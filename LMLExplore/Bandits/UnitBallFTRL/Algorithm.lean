/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.UnitBallFTRL.Basic
public import LMLExplore.MeasureTheory.MeasurableSpace.Constructions
public import LMLExplore.MeasureTheory.Measure.Weighted
public import LMLExplore.SequentialLearning.Algorithm
public import LMLExplore.SequentialLearning.Environments.Deterministic

/-!
# FTRL with bandit feedback on the unit ball as an algorithm

[LS, Algorithm 17] plays adversarial linear bandits on the closed unit ball of a
finite-dimensional real inner product space `E` with an orthonormal basis `b` indexed by `ι`. At
round `t` it computes the play `a t` of follow the regularized leader on the closed ball of radius
`r` with potential `unitBallPotential` and learning rate `η`, for the past loss estimates; then it
draws an outcome `o` with probability `unitBallProb (a t) o`, plays `unitBallAction b (a t) o` and
estimates the loss by `unitBallEstimate` [LS, (28.12)].

The estimate of round `t` depends on the outcome, not only on the vector played: when `a t / ‖a t‖`
is one of the exploration directions `± b i`, the vector does not tell whether the round explored.
The history of a run records only the actions and the feedbacks, so the action of the algorithm
is the pair `(unitBallAction b (a t) o, o) ∈ E × Option (ι × Bool)`: the vector played and the
outcome that produced it. The play `a t` is then a function of the history, computed in closed
form by `unitBallFTRLPlay` from the cumulative estimate `unitBallFTRLHistSum`.

An adaptive adversary chooses at round `t` a loss vector `ℓ t (h, o) ∈ E`, a measurable function
of the history `h` of the first `t` rounds and of the observation `o` of round `t`, and the learner
observes the loss `⟪v, ℓ t (h, o)⟫` of the vector `v` it plays. This is the hypothesis
`Y t =ᵐ[P] fun ω ↦ ⟪(A t ω).1, ℓ t (history O A Y t ω, O t ω)⟫` on a run, which holds against the
environment `Environment.detFeedback obs (fun t x ↦ ⟪x.2.1, ℓ t x.1⟫) _` whatever the observation
kernels `obs`. Applying the round-by-round analysis of `LMLExplore.Bandits.UnitBallFTRL.Basic` with
the σ-algebras `h.filtrationObs t` gives [LS, Theorem 28.11] for every run of the algorithm.

## Main definitions

* `unitBallFeedbackEstimate b a x o`: the loss estimate [LS, (28.12)] for the play `a`, the
  observed loss `x` and the outcome `o`, as a vector of `E`.
* `unitBallFTRLHistSum b η r n h`: the cumulative loss estimate computed from the history `h` of
  the first `n` rounds.
* `unitBallLaw b a`: the law of the action for the play `a`.
* `unitBallFTRL b η r hη hr`: the algorithm [LS, Algorithm 17].

## Main statements

* `innerSL_unitBallFeedbackEstimate`: when the observed loss is the loss of the vector played, the
  estimate represents `unitBallEstimate`.
* `unitBallFTRLHistSum_history`: along a run, the cumulative estimate is the sum of the estimates
  of the past rounds.
* `UnitBallFTRL.ae_fst_action_eq`, `UnitBallFTRL.condExp_indicator_outcome`: the run lemma: the
  vector played is the action of the outcome for the play, and the outcome of round `n` has
  conditional law `unitBallProb` of the play given the history and the observation of round `n`.
* `UnitBallFTRL.ae_isFTRLPlay`: the plays are FTRL plays for the estimated losses.
* `UnitBallFTRL.integral_regret_le`: against an adaptive adversary with losses of norm at most
  `1`, the expected regret against every `u` of the unit ball is at most
  `(1 - r) n - log (1 - r) / η + η d n / 2`.
* `UnitBallFTRL.integral_regret_le_two_mul_sqrt`: [LS, Theorem 28.11], with `r = 1 - 2 η d` and
  `η = √(log n / (3 d n))`, the expected regret is at most `2 √(3 n d log n)`;
  `UnitBallFTRL.integral_regret_detFeedback_le_two_mul_sqrt` states it for every run against the
  environment of an adaptive adversary.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 28.4.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Metric Real LMLExplore.OnlineLearning
open scoped InnerProductSpace

namespace LMLExplore.Bandits

variable {ι 𝓞 E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Estimate

variable (b : OrthonormalBasis ι ℝ E) (a : E) (x : ℝ)

/-- The loss estimate [LS, (28.12)] of [LS, Algorithm 17] for the play `a`, the observed loss `x`
and the outcome `o`, as a vector of `E`: `0` if the algorithm does not explore, and
`d / (1 - ‖a‖) * x • A` for the action `A = unitBallAction b a o` if it explores, where `d` is
the cardinality of `ι`. When `x` is the loss `y A` of the action, its functional `⟪·, ·⟫` is
`unitBallEstimate b a y o` (`innerSL_unitBallFeedbackEstimate`). -/
noncomputable def unitBallFeedbackEstimate : Option (ι × Bool) → E
  | none => 0
  | some p => (Fintype.card ι / (1 - ‖a‖) * x) • unitBallAction b a (some p)

@[simp]
lemma unitBallFeedbackEstimate_none : unitBallFeedbackEstimate b a x none = 0 := (rfl)

@[simp]
lemma unitBallFeedbackEstimate_some (p : ι × Bool) :
    unitBallFeedbackEstimate b a x (some p) =
      (Fintype.card ι / (1 - ‖a‖) * x) • unitBallAction b a (some p) := (rfl)

/-- When the observed loss is the loss `y A` of the action `A = unitBallAction b a o`, the vector
estimate represents the loss estimate `unitBallEstimate b a y o`. -/
@[simp]
lemma innerSL_unitBallFeedbackEstimate (y : E →L[ℝ] ℝ) (o : Option (ι × Bool)) :
    innerSL ℝ (unitBallFeedbackEstimate b a (y (unitBallAction b a o)) o) =
      unitBallEstimate b a y o := by
  rcases o with _ | ⟨i, _ | _⟩ <;> simp

end Estimate

section Measurability

variable [MeasurableSpace E] [BorelSpace E]

/-- The FTRL play on the ball is a measurable function of the cumulative loss. -/
@[fun_prop]
lemma measurable_unitBallFTRLPlay (η r : ℝ) : Measurable (unitBallFTRLPlay (E := E) η r) := by
  rw [funext (unitBallFTRLPlay_def η r)]
  fun_prop

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] (b : OrthonormalBasis ι ℝ E)

/-- The vector loss estimate is a measurable function of the play, the observed loss and the
outcome. -/
lemma measurable_unitBallFeedbackEstimate :
    Measurable fun z : (E × ℝ) × Option (ι × Bool) ↦
      unitBallFeedbackEstimate b z.1.1 z.1.2 z.2 := by
  refine measurable_from_prod_countable_left fun o ↦ ?_
  rcases o with _ | p
  · exact measurable_const
  · simp only [unitBallFeedbackEstimate_some]
    exact (by fun_prop : Measurable fun z : E × ℝ ↦ Fintype.card ι / (1 - ‖z.1‖) * z.2).smul
      ((measurable_unitBallAction b).comp (measurable_fst.prodMk measurable_const))

end Measurability

section HistSum

variable (b : OrthonormalBasis ι ℝ E) (η r : ℝ)

/-- The cumulative loss estimate of [LS, Algorithm 17] computed from the history `h` of the first
`n` rounds: the sum over the rounds `s < n` of the estimates
`unitBallFeedbackEstimate b (a s) (x s) (o s)` for the outcome `o s` and the observed loss `x s`
of round `s` of `h`, where `a s = unitBallFTRLPlay η r (S s)` is the play of round `s`, computed
from the cumulative estimate `S s` of the rounds before `s`. -/
noncomputable def unitBallFTRLHistSum : (n : ℕ) → Hist 𝓞 (E × Option (ι × Bool)) ℝ n → E
  | 0, _ => 0
  | n + 1, h => unitBallFTRLHistSum n (Fin.init h) +
      unitBallFeedbackEstimate b (unitBallFTRLPlay η r (unitBallFTRLHistSum n (Fin.init h)))
        (h (Fin.last n)).feedback (h (Fin.last n)).action.2

@[simp]
lemma unitBallFTRLHistSum_zero (h : Hist 𝓞 (E × Option (ι × Bool)) ℝ 0) :
    unitBallFTRLHistSum b η r 0 h = 0 := by
  rw [unitBallFTRLHistSum]

lemma unitBallFTRLHistSum_succ (n : ℕ) (h : Hist 𝓞 (E × Option (ι × Bool)) ℝ (n + 1)) :
    unitBallFTRLHistSum b η r (n + 1) h = unitBallFTRLHistSum b η r n (Fin.init h) +
      unitBallFeedbackEstimate b (unitBallFTRLPlay η r (unitBallFTRLHistSum b η r n (Fin.init h)))
        (h (Fin.last n)).feedback (h (Fin.last n)).action.2 := by
  rw [unitBallFTRLHistSum]

/-- Along a sequence of observations `O`, actions `A` and feedbacks `Y`, the cumulative estimate
of the history of the first `n` rounds is the sum over the rounds `t < n` of the estimates for the
play of round `t`, the feedback `Y t` and the outcome `(A t).2`. -/
lemma unitBallFTRLHistSum_history {Ω : Type*} (O : ℕ → Ω → 𝓞)
    (A : ℕ → Ω → E × Option (ι × Bool)) (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    unitBallFTRLHistSum b η r n (history O A Y n ω) = ∑ t ∈ range n,
      unitBallFeedbackEstimate b
        (unitBallFTRLPlay η r (unitBallFTRLHistSum b η r t (history O A Y t ω))) (Y t ω)
        (A t ω).2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [unitBallFTRLHistSum_succ, init_history, sum_range_succ, ← ih]
    simp [history_apply]

variable [MeasurableSpace 𝓞] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

@[fun_prop]
lemma measurable_unitBallFTRLHistSum (n : ℕ) :
    Measurable (unitBallFTRLHistSum (𝓞 := 𝓞) b η r n) := by
  induction n with
  | zero =>
    rw [funext (unitBallFTRLHistSum_zero b η r)]
    exact measurable_const
  | succ n ih =>
    have hS := ih.comp (measurable_finInit (β := fun _ ↦ _))
    have hlast : Measurable fun h : Hist 𝓞 (E × Option (ι × Bool)) ℝ (n + 1) ↦ h (Fin.last n) :=
      measurable_pi_apply _
    rw [funext (unitBallFTRLHistSum_succ b η r n)]
    exact hS.add ((measurable_unitBallFeedbackEstimate b).comp
      ((((measurable_unitBallFTRLPlay η r).comp hS).prodMk
        (Round.measurable_feedback.comp hlast)).prodMk
        (measurable_snd.comp (Round.measurable_action.comp hlast))))

end HistSum

section Law

variable (b : OrthonormalBasis ι ℝ E) [MeasurableSpace E] [MeasurableSpace ι] {a : E}

/-- The law of the action of [LS, Algorithm 17] for the play `a`: the outcome `o` is drawn with
probability `unitBallProb a o`, and the action is the pair `(unitBallAction b a o, o)` of the
vector played and the outcome. -/
noncomputable def unitBallLaw (a : E) : Measure (E × Option (ι × Bool)) :=
  ∑ o, ENNReal.ofReal (unitBallProb a o) • Measure.dirac (unitBallAction b a o, o)

lemma unitBallLaw_def (a : E) :
    unitBallLaw b a =
      ∑ o, ENNReal.ofReal (unitBallProb a o) • Measure.dirac (unitBallAction b a o, o) := (rfl)

/-- The law of the action is a measurable function of the play. -/
lemma measurable_unitBallLaw [BorelSpace E] [MeasurableSingletonClass ι] :
    Measurable (unitBallLaw (E := E) b) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp only [unitBallLaw_def, _root_.sum_apply, _root_.smul_apply, Measure.dirac_apply' _ hs,
    smul_eq_mul]
  refine Finset.measurable_sum _ fun o _ ↦
    (ENNReal.measurable_ofReal.comp (measurable_unitBallProb o)).mul ?_
  exact (measurable_one.indicator hs).comp
    (((measurable_unitBallAction b).comp (measurable_id.prodMk measurable_const)).prodMk
      measurable_const)

/-- For a play in the closed unit ball, the law of the action is a probability measure. -/
lemma isProbabilityMeasure_unitBallLaw [Nonempty ι] (ha : ‖a‖ ≤ 1) :
    IsProbabilityMeasure (unitBallLaw b a) := by
  constructor
  simp only [unitBallLaw_def, _root_.sum_apply, _root_.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun o _ ↦ unitBallProb_nonneg ha o, sum_unitBallProb,
    ENNReal.ofReal_one]

/-- For a play in the closed unit ball, the integral against the law of the action is the
average `∑ o, unitBallProb a o • f (unitBallAction b a o, o)` over the outcomes. -/
lemma integral_unitBallLaw {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    (ha : ‖a‖ ≤ 1) {f : E × Option (ι × Bool) → F} (hf : StronglyMeasurable f) :
    ∫ z, f z ∂(unitBallLaw b a) = ∑ o, unitBallProb a o • f (unitBallAction b a o, o) :=
  integral_sum_smul_dirac (unitBallProb_nonneg ha) hf

variable [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSingletonClass ι]

/-- Under the law of the action, the vector played is almost surely the action of the outcome. -/
lemma ae_unitBallLaw_fst_eq (a : E) : ∀ᵐ z ∂(unitBallLaw b a), z.1 = unitBallAction b a z.2 := by
  have hS : MeasurableSet {z : E × Option (ι × Bool) | z.1 = unitBallAction b a z.2} :=
    measurableSet_eq_fun measurable_fst ((measurable_unitBallAction b).comp
      (measurable_const.prodMk measurable_snd))
  have hS' : MeasurableSet {z : E × Option (ι × Bool) | ¬z.1 = unitBallAction b a z.2} :=
    hS.compl
  rw [ae_iff, unitBallLaw_def, _root_.sum_apply]
  refine Finset.sum_eq_zero fun o _ ↦ ?_
  rw [_root_.smul_apply, Measure.dirac_apply' _ hS']
  simp

end Law

section Algorithm

variable [MeasurableSpace 𝓞] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι] (b : OrthonormalBasis ι ℝ E)
  (η r : ℝ)

/-- **FTRL with bandit feedback on the unit ball** [LS, Algorithm 17], with learning rate `η ≥ 0`
and radius `r ∈ [0, 1]`. At round `n`, with history `h`, it computes the FTRL play
`a = unitBallFTRLPlay η r (unitBallFTRLHistSum b η r n h)` on the closed ball of radius `r` for
the cumulative loss estimate of `h`, and draws its action from `unitBallLaw b a`: the outcome `o`
with probability `unitBallProb a o`, together with the vector `unitBallAction b a o` it plays. It
ignores the observations. -/
noncomputable def unitBallFTRL (hη : 0 ≤ η) (hr : r ∈ Set.Icc 0 1) :
    Algorithm 𝓞 (E × Option (ι × Bool)) ℝ where
  policy n :=
    { toFun x := unitBallLaw b (unitBallFTRLPlay η r (unitBallFTRLHistSum b η r n x.1))
      measurable' := (measurable_unitBallLaw b).comp (((measurable_unitBallFTRLPlay η r).comp
        (measurable_unitBallFTRLHistSum b η r n)).comp measurable_fst) }
  isMarkovKernel_policy _ :=
    ⟨fun _ ↦ isProbabilityMeasure_unitBallLaw b ((norm_unitBallFTRLPlay_le hη hr.1 _).trans hr.2)⟩

/-- The policy of `unitBallFTRL` at round `n` draws its action from the law `unitBallLaw b a`
for the FTRL play `a` of the cumulative estimate of the history. -/
@[simp]
lemma unitBallFTRL_policy_apply (hη : 0 ≤ η) (hr : r ∈ Set.Icc 0 1) (n : ℕ)
    (x : Hist 𝓞 (E × Option (ι × Bool)) ℝ n × 𝓞) :
    (unitBallFTRL b η r hη hr).policy n x =
      unitBallLaw b (unitBallFTRLPlay η r (unitBallFTRLHistSum b η r n x.1)) := (rfl)

end Algorithm

namespace UnitBallFTRL

variable [MeasurableSpace 𝓞] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Nonempty ι] {b : OrthonormalBasis ι ℝ E}
  {η r : ℝ} {hη : 0 ≤ η} {hr : r ∈ Set.Icc 0 1} {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → E × Option (ι × Bool)} {Y : ℕ → Ω → ℝ}
  {env : Environment 𝓞 (E × Option (ι × Bool)) ℝ}

/-- **The vector played is the action of the outcome.** Along a run of `unitBallFTRL` against any
environment, the vector `(A n).1` played at round `n` is almost surely
`unitBallAction b a (A n).2`, for the play `a` of round `n` computed from the history. -/
theorem ae_fst_action_eq (h : IsAlgEnvSeq O A Y (unitBallFTRL b η r hη hr) env P) (n : ℕ) :
    ∀ᵐ ω ∂P, (A n ω).1 = unitBallAction b
      (unitBallFTRLPlay η r (unitBallFTRLHistSum b η r n (history O A Y n ω))) (A n ω).2 := by
  have hS : MeasurableSet {q : (Hist 𝓞 (E × Option (ι × Bool)) ℝ n × 𝓞) × (E × Option (ι × Bool)) |
      q.2.1 = unitBallAction b (unitBallFTRLPlay η r (unitBallFTRLHistSum b η r n q.1.1)) q.2.2} :=
    measurableSet_eq_fun measurable_snd.fst ((measurable_unitBallAction b).comp
      ((((measurable_unitBallFTRLPlay η r).comp (measurable_unitBallFTRLHistSum b η r n)).comp
        measurable_fst.fst).prodMk measurable_snd.snd))
  have h_ae := Measure.ae_compProd_of_ae_ae (μ := P.map fun ω ↦ (history O A Y n ω, O n ω))
    (κ := (unitBallFTRL b η r hη hr).policy n) hS (.of_forall fun x ↦ ae_unitBallLaw_fst_eq b _)
  rw [← (h.hasCondDistrib_action n).map_eq] at h_ae
  exact ae_of_ae_map (h.hasCondDistrib_action n).aemeasurable h_ae

/-- **The run lemma of `unitBallFTRL`.** Along a run against any environment, the conditional
probability of the outcome `o` at round `n`, given the history and the observation of round `n`,
is `unitBallProb a o` for the play `a` of round `n` computed from the history. -/
theorem condExp_indicator_outcome [IsFiniteMeasure P]
    (h : IsAlgEnvSeq O A Y (unitBallFTRL b η r hη hr) env P) (n : ℕ) (o : Option (ι × Bool)) :
    P⟦(fun ω ↦ (A n ω).2) ⁻¹' {o} | h.filtrationObs n⟧ =ᵐ[P] fun ω ↦
      unitBallProb (unitBallFTRLPlay η r (unitBallFTRLHistSum b η r n (history O A Y n ω))) o := by
  set f : (Hist 𝓞 (E × Option (ι × Bool)) ℝ n × 𝓞) × (E × Option (ι × Bool)) → ℝ :=
    fun z ↦ ({o} : Set (Option (ι × Bool))).indicator (fun _ ↦ 1) z.2.2
  have hf : StronglyMeasurable f :=
    ((measurable_const.indicator (measurableSet_singleton o)).comp
      measurable_snd.snd).stronglyMeasurable
  have hind : ((fun ω ↦ (A n ω).2) ⁻¹' {o}).indicator (fun _ ↦ (1 : ℝ)) =
      fun ω ↦ f ((history O A Y n ω, O n ω), A n ω) := by
    funext ω
    exact Set.indicator_comp_right (g := fun _ ↦ (1 : ℝ)) (fun ω ↦ (A n ω).2)
  have hint : Integrable (fun ω ↦ f ((history O A Y n ω, O n ω), A n ω)) P :=
    hind ▸ (integrable_const 1).indicator
      ((h.measurable_action n).snd (measurableSet_singleton o))
  rw [hind]
  filter_upwards [h.condExp_comp_action n hf hint] with ω hω
  rw [hω, unitBallFTRL_policy_apply, integral_unitBallLaw b
    ((norm_unitBallFTRLPlay_le hη hr.1 _).trans hr.2)
    (f := fun z ↦ f ((history O A Y n ω, O n ω), z))
    (hf.comp_measurable (measurable_const.prodMk measurable_id)),
    Finset.sum_eq_single o (fun o' _ ho' ↦ by simp [f, ho']) (by simp)]
  simp [f]

variable {ℓ : (t : ℕ) → Hist 𝓞 (E × Option (ι × Bool)) ℝ t × 𝓞 → E} {n : ℕ}

/-- **The plays are FTRL plays.** Along a run of `unitBallFTRL` with `r < 1` whose feedbacks of
the rounds `t < n` are the losses `⟪(A t).1, ℓ t (h, o)⟫` of the vectors played, almost surely,
for every `t ≤ n`, the play of round `t` is a play of FTRL on the closed ball of radius `r` with
potential `unitBallPotential` and learning rate `η` for the estimated losses
`unitBallEstimate b (a s) ⟪ℓ s (h, o), ·⟫ (A s).2` of the rounds `s < t`. -/
theorem ae_isFTRLPlay (h : IsAlgEnvSeq O A Y (unitBallFTRL b η r hη hr) env P)
    (hr1 : r < 1)
    (hY : ∀ t < n, Y t =ᵐ[P] fun ω ↦ ⟪(A t ω).1, ℓ t (history O A Y t ω, O t ω)⟫_ℝ) :
    ∀ᵐ ω ∂P, ∀ t ≤ n, IsFTRLPlay (closedBall 0 r) unitBallPotential η
      (fun s ↦ unitBallEstimate b
        (unitBallFTRLPlay η r (unitBallFTRLHistSum b η r s (history O A Y s ω)))
        (innerSL ℝ (ℓ s (history O A Y s ω, O s ω))) (A s ω).2) t
      (unitBallFTRLPlay η r (unitBallFTRLHistSum b η r t (history O A Y t ω))) := by
  have hY' : ∀ᵐ ω ∂P, ∀ t < n, Y t ω = ⟪(A t ω).1, ℓ t (history O A Y t ω, O t ω)⟫_ℝ :=
    ae_all_iff.2 fun t ↦ if ht : t < n then (hY t ht).mono fun _ hω _ ↦ hω
      else ae_of_all _ fun _ h ↦ absurd h ht
  filter_upwards [hY', ae_all_iff.2 (ae_fst_action_eq h)] with ω hYω hAω t ht
  refine isFTRLPlay_unitBallFTRLPlay hη hr.1 hr1 ?_
  rw [unitBallFTRLHistSum_history, map_sum]
  refine sum_congr rfl fun s hs ↦ ?_
  rw [hYω s ((mem_range.1 hs).trans_le ht), hAω s, real_inner_comm, ← innerSL_apply_apply ℝ,
    innerSL_unitBallFeedbackEstimate]

/-- Along a run of `unitBallFTRL`, the regret `∑ t < n, (⟪(A t).1, ℓ t⟫ - ⟪u, ℓ t⟫)` is almost
surely the regret of the actions `unitBallAction b (a t) (A t).2` for the losses `⟪ℓ t, ·⟫`. -/
private lemma integral_regret_eq (h : IsAlgEnvSeq O A Y (unitBallFTRL b η r hη hr) env P) (u : E) :
    ∫ ω, ∑ t ∈ range n, (⟪(A t ω).1, ℓ t (history O A Y t ω, O t ω)⟫_ℝ -
      ⟪u, ℓ t (history O A Y t ω, O t ω)⟫_ℝ) ∂P =
    ∫ ω, ∑ t ∈ range n, innerSL ℝ (ℓ t (history O A Y t ω, O t ω)) (unitBallAction b
      (unitBallFTRLPlay η r (unitBallFTRLHistSum b η r t (history O A Y t ω))) (A t ω).2 - u)
      ∂P := by
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 (ae_fst_action_eq h)] with ω hAω
  refine sum_congr rfl fun t _ ↦ ?_
  rw [← hAω t, innerSL_apply_apply, inner_sub_right, real_inner_comm, real_inner_comm u]

variable [IsProbabilityMeasure P]

/-- **Regret of FTRL with bandit feedback on the unit ball against an adaptive adversary.** Let
`η > 0` and `r < 1`. Let an adaptive adversary choose at round `t < n` the loss vector
`ℓ t (h, o)` of norm at most `1`, a measurable function of the history `h` and the observation `o`
of round `t`, and let the feedback `Y t` of a run of `unitBallFTRL` be the loss
`⟪(A t).1, ℓ t (h, o)⟫` of the vector played. Then against every `u` of the closed unit ball, the
expected regret after `n` rounds is at most `(1 - r) n - log (1 - r) / η + η d n / 2`, where `d`
is the cardinality of `ι`, the dimension of `E`. -/
theorem integral_regret_le (h : IsAlgEnvSeq O A Y (unitBallFTRL b η r hη hr) env P)
    (hη0 : 0 < η) (hr1 : r < 1) (hℓ : ∀ t < n, Measurable (ℓ t))
    (hℓ1 : ∀ t < n, ∀ x, ‖ℓ t x‖ ≤ 1)
    (hY : ∀ t < n, Y t =ᵐ[P] fun ω ↦ ⟪(A t ω).1, ℓ t (history O A Y t ω, O t ω)⟫_ℝ) {u : E}
    (hu : ‖u‖ ≤ 1) :
    ∫ ω, ∑ t ∈ range n, (⟪(A t ω).1, ℓ t (history O A Y t ω, O t ω)⟫_ℝ -
      ⟪u, ℓ t (history O A Y t ω, O t ω)⟫_ℝ) ∂P ≤
      (1 - r) * n - log (1 - r) / η + η * Fintype.card ι * n / 2 := by
  have hpast (t : ℕ) : Measurable[h.filtrationObs t] fun ω ↦ (history O A Y t ω, O t ω) :=
    (h.measurable_history_filtrationObs t).prodMk (h.adapted_obs_filtrationObs t)
  rw [integral_regret_eq h u]
  exact ftrl_integral_regret_le_of_unitBallEstimate b hr1 hη0 (m := h.filtrationObs)
    (fun t _ ↦ h.filtrationObs.le t)
    (fun t _ o ↦ (h.measurable_action t).snd (measurableSet_singleton o))
    (fun t _ o ↦ condExp_indicator_outcome h t o)
    (fun t _ ↦ ((measurable_unitBallFTRLPlay η r).comp
      ((measurable_unitBallFTRLHistSum b η r t).comp
        (h.measurable_history_filtrationObs t))).aestronglyMeasurable)
    (fun t ht ↦ (innerSL ℝ).continuous.comp_aestronglyMeasurable
      ((hℓ t ht).comp (hpast t)).aestronglyMeasurable)
    (fun t ht ↦ ae_of_all _ fun ω ↦ by rw [innerSL_apply_norm]; exact hℓ1 t ht _)
    (ae_isFTRLPlay h hr1 hY) hu

/-- **Regret of FTRL with bandit feedback on the unit ball against an adaptive adversary**
[LS, Theorem 28.11]. Under the hypotheses of `UnitBallFTRL.integral_regret_le` on the adversary,
with `n ≥ 2` rounds, the learning rate `η = √(log n / (3 d n))` and the radius `r = 1 - 2 η d`,
where `d` is the cardinality of `ι`, the expected regret against every `u` of the closed unit ball
is at most `2 √(3 n d log n)`. The algorithm requires `r ≥ 0`, that is `4 d log n ≤ 3 n`; for
smaller horizons the bound exceeds the trivial bound `2 n`. -/
theorem integral_regret_le_two_mul_sqrt (h : IsAlgEnvSeq O A Y (unitBallFTRL b η r hη hr) env P)
    (hn : 2 ≤ n) (hηn : η = √(log n / (3 * Fintype.card ι * n)))
    (hrn : r = 1 - 2 * η * Fintype.card ι) (hℓ : ∀ t < n, Measurable (ℓ t))
    (hℓ1 : ∀ t < n, ∀ x, ‖ℓ t x‖ ≤ 1)
    (hY : ∀ t < n, Y t =ᵐ[P] fun ω ↦ ⟪(A t ω).1, ℓ t (history O A Y t ω, O t ω)⟫_ℝ) {u : E}
    (hu : ‖u‖ ≤ 1) :
    ∫ ω, ∑ t ∈ range n, (⟪(A t ω).1, ℓ t (history O A Y t ω, O t ω)⟫_ℝ -
      ⟪u, ℓ t (history O A Y t ω, O t ω)⟫_ℝ) ∂P ≤
      2 * √(3 * n * Fintype.card ι * log n) := by
  have hpast (t : ℕ) : Measurable[h.filtrationObs t] fun ω ↦ (history O A Y t ω, O t ω) :=
    (h.measurable_history_filtrationObs t).prodMk (h.adapted_obs_filtrationObs t)
  have hr1 : r < 1 := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have : 0 < η := by
      rw [hηn]
      exact sqrt_pos.2 (div_pos (log_pos (by linarith)) (by positivity))
    rw [hrn]
    have : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
    nlinarith
  rw [integral_regret_eq h u]
  exact ftrl_integral_regret_le_two_mul_sqrt_of_unitBallEstimate b hn hηn hrn
    (m := h.filtrationObs) (fun t _ ↦ h.filtrationObs.le t)
    (fun t _ o ↦ (h.measurable_action t).snd (measurableSet_singleton o))
    (fun t _ o ↦ condExp_indicator_outcome h t o)
    (fun t _ ↦ ((measurable_unitBallFTRLPlay η r).comp
      ((measurable_unitBallFTRLHistSum b η r t).comp
        (h.measurable_history_filtrationObs t))).aestronglyMeasurable)
    (fun t ht ↦ (innerSL ℝ).continuous.comp_aestronglyMeasurable
      ((hℓ t ht).comp (hpast t)).aestronglyMeasurable)
    (fun t ht ↦ ae_of_all _ fun ω ↦ by rw [innerSL_apply_norm]; exact hℓ1 t ht _)
    (ae_isFTRLPlay h hr1 hY) hu

/-- **Regret of FTRL with bandit feedback on the unit ball, for every run against an adaptive
adversary** [LS, Theorem 28.11]. Let an adaptive adversary choose at round `t` the loss vector
`ℓ t (h, o)`, a measurable function of the history `h` and of the observation `o` of round `t`,
drawn from arbitrary observation kernels `obs`, with `‖ℓ t (h, o)‖ ≤ 1`, and let its environment
`Environment.detFeedback obs (fun t x ↦ ⟪x.2.1, ℓ t x.1⟫) _` return the loss of the vector
played. With the rates of `UnitBallFTRL.integral_regret_le_two_mul_sqrt`, every run of
`unitBallFTRL` against it has expected regret at most `2 √(3 n d log n)` against every `u` of
the closed unit ball. -/
theorem integral_regret_detFeedback_le_two_mul_sqrt
    {obs : (t : ℕ) → Kernel (Hist 𝓞 (E × Option (ι × Bool)) ℝ t) 𝓞} [∀ t, IsMarkovKernel (obs t)]
    {hf : ∀ t, Measurable fun x : (Hist 𝓞 (E × Option (ι × Bool)) ℝ t × 𝓞) ×
      (E × Option (ι × Bool)) ↦ ⟪x.2.1, ℓ t x.1⟫_ℝ}
    (h : IsAlgEnvSeq O A Y (unitBallFTRL b η r hη hr)
      (Environment.detFeedback obs (fun t x ↦ ⟪x.2.1, ℓ t x.1⟫_ℝ) hf) P)
    (hn : 2 ≤ n) (hηn : η = √(log n / (3 * Fintype.card ι * n)))
    (hrn : r = 1 - 2 * η * Fintype.card ι) (hℓ : ∀ t < n, Measurable (ℓ t))
    (hℓ1 : ∀ t < n, ∀ x, ‖ℓ t x‖ ≤ 1) {u : E} (hu : ‖u‖ ≤ 1) :
    ∫ ω, ∑ t ∈ range n, (⟪(A t ω).1, ℓ t (history O A Y t ω, O t ω)⟫_ℝ -
      ⟪u, ℓ t (history O A Y t ω, O t ω)⟫_ℝ) ∂P ≤
      2 * √(3 * n * Fintype.card ι * log n) :=
  integral_regret_le_two_mul_sqrt h hn hηn hrn hℓ hℓ1
    (fun t _ ↦ h.feedback_detFeedback_ae_eq t) hu

end UnitBallFTRL

end LMLExplore.Bandits
