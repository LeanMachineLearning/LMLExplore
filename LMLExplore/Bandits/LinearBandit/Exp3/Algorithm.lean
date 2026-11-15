/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.LinearBandit.Exp3.Basic
public import LMLExplore.Bandits.WeightAlgorithm
public import LMLExplore.SequentialLearning.Algorithm
public import LMLExplore.SequentialLearning.Environments.Deterministic

/-!
# Exp3 for adversarial linear bandits as an algorithm

Exp3 for linear bandits [LS, Algorithm 15], with features `φ : α → E` of a finite type of arms in
a finite-dimensional real inner product space, an exploration distribution `π`, a learning rate
`η` and an exploration rate `γ ∈ [0, 1]`, is the weight-based algorithm whose weights at round
`n` are `linearExp3Weights π η γ (S n)`: the exponential weights of `-η` times the cumulative loss
estimate `S n`, mixed with `π`. The cumulative estimate is computed from the history: the arms
played and their observed losses.

An adaptive adversary for linear bandits chooses at round `t` a loss vector `y t (h, o) ∈ E`, a
measurable function of the history `h` of the first `t` rounds and of the observation `o` of
round `t`, and the learner observes the loss `⟪φ (A t), y t (h, o)⟫` of the arm it plays. This is
the hypothesis `Y t =ᵐ[P] fun ω ↦ ⟪φ (A t ω), y t (history O A Y t ω, O t ω)⟫` on a run, which
holds against the environment `Environment.detFeedback obs (fun n x ↦ ⟪φ x.2, y n x.1⟫) hf`
whatever the observation kernels `obs`, by `IsAlgEnvSeq.feedback_detFeedback_ae_eq`. Loss vectors
fixed in advance by an oblivious adversary are the case of functions `y t` that do not depend on
`(h, o)`.

Along a run, given the history and the observation of round `n`, the arm of round `n` has law the
weights computed from the past arms and feedbacks (`LinearExp3.condExp_indicator_action`). With
the analysis of `LMLExplore.Bandits.LinearBandit.Exp3.Basic`, which is stated round by round for
σ-algebras `m t`, applied to `m t = h.filtrationObs t`, this gives [LS, Theorem 27.1] for every run
of the algorithm against an adaptive adversary.

## Main definitions

* `LMLExplore.Bandits.linearExp3HistSum φ π η γ n h`: the cumulative loss estimate of Exp3 for
  linear bandits computed from the history `h` of the first `n` rounds.
* `LMLExplore.Bandits.linearExp3 φ π η γ hπ hγ`: Exp3 for linear bandits [LS, Algorithm 15].

## Main statements

* `linearExp3HistSum_history`: along a sequence of observations, actions and feedbacks, the
  cumulative estimate of the history is `linearExp3Sum` of the actions and the feedbacks.
* `linearExp3_policy_apply`: the policy of round `n` draws the arm from the weights.
* `LinearExp3.condExp_indicator_action`: the run lemma, the conditional probability of playing an
  arm `c` at round `n` given the history and the observation of round `n` is its weight;
  `LinearExp3.condExp_indicator_action_of_feedback_ae_eq`: the same weight, computed from the
  losses of the arms played when the feedbacks are these losses.
* `LinearExp3.integral_regret_le`: [LS, Theorem 27.1] for arbitrary rates against an adaptive
  adversary: the expected regret against every arm is at most `log k / η + η d n + 2 γ n`.
* `LinearExp3.integral_regret_le_two_mul_sqrt`: with tuned rates, the expected regret is at most
  `2 √((2 g + d) n log k)`.
* `LinearExp3.integral_regret_le_two_mul_sqrt_three`: with an exploration distribution of G-value
  `d`, which the Kiefer–Wolfowitz theorem provides when the features span `E`, the expected regret
  is at most `2 √(3 d n log k)`; `LinearExp3.integral_regret_detFeedback_le_two_mul_sqrt_three`
  states it for every run against the environment of an adaptive adversary.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 27.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning ContinuousLinearMap InnerProductSpace Module
  LMLExplore.OnlineLearning
open scoped InnerProductSpace

namespace LMLExplore.Bandits

variable {α 𝓞 E : Type*} [Fintype α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section HistSum

variable (φ : α → E) (π : α → ℝ) (η γ : ℝ)

/-- The cumulative loss estimate of Exp3 for linear bandits computed from the history `h` of the
first `n` rounds: the sum over the rounds `s < n` of the estimates
`linearExp3Estimate φ (P s) (A s) (ℓ s)` for the arm `A s` and the observed loss `ℓ s` of round
`s` of `h`, where `P s` are the weights of round `s`, computed from the cumulative estimate of the
rounds before `s`. -/
noncomputable def linearExp3HistSum : (n : ℕ) → Hist 𝓞 α ℝ n → α → ℝ
  | 0, _ => 0
  | n + 1, h => linearExp3HistSum n (Fin.init h) +
      linearExp3Estimate φ (linearExp3Weights π η γ (linearExp3HistSum n (Fin.init h)))
        (h (Fin.last n)).action (h (Fin.last n)).feedback

@[simp]
lemma linearExp3HistSum_zero (h : Hist 𝓞 α ℝ 0) : linearExp3HistSum φ π η γ 0 h = 0 := by
  rw [linearExp3HistSum]

lemma linearExp3HistSum_succ (n : ℕ) (h : Hist 𝓞 α ℝ (n + 1)) :
    linearExp3HistSum φ π η γ (n + 1) h = linearExp3HistSum φ π η γ n (Fin.init h) +
      linearExp3Estimate φ (linearExp3Weights π η γ (linearExp3HistSum φ π η γ n (Fin.init h)))
        (h (Fin.last n)).action (h (Fin.last n)).feedback := by
  rw [linearExp3HistSum]

/-- Along a sequence of observations `O`, actions `A` and feedbacks `Y`, the cumulative estimate
of the history of the first `n` rounds is the cumulative estimate `linearExp3Sum` of the actions
and the feedbacks of these rounds. -/
lemma linearExp3HistSum_history {Ω : Type*} (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    linearExp3HistSum φ π η γ n (history O A Y n ω) =
      linearExp3Sum φ π η γ (A · ω) (Y · ω) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [linearExp3HistSum_succ, init_history, ih, linearExp3Sum_succ]
    simp [history_apply]

variable [FiniteDimensional ℝ E] [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace 𝓞]

@[fun_prop]
lemma measurable_linearExp3HistSum (n : ℕ) :
    Measurable (linearExp3HistSum (𝓞 := 𝓞) φ π η γ n) := by
  induction n with
  | zero =>
    rw [funext (linearExp3HistSum_zero φ π η γ)]
    exact measurable_const
  | succ n ih =>
    have hS := ih.comp (measurable_finInit (β := fun _ ↦ _))
    have hlast : Measurable fun h : Hist 𝓞 α ℝ (n + 1) ↦ h (Fin.last n) := measurable_pi_apply _
    rw [funext (linearExp3HistSum_succ φ π η γ n)]
    exact hS.add (measurable_linearExp3Estimate φ ((measurable_linearExp3Weights π η γ).comp hS)
      (Round.measurable_action.comp hlast) (Round.measurable_feedback.comp hlast))

end HistSum

section Algorithm

variable [FiniteDimensional ℝ E] [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace 𝓞] (φ : α → E) (π : α → ℝ) (η γ : ℝ)

/-- **Exp3 for adversarial linear bandits** [LS, Algorithm 15] with features `φ`, exploration
distribution `π`, learning rate `η` and exploration rate `γ ∈ [0, 1]`: the weight-based algorithm
that draws the arm of round `n` from the weights `linearExp3Weights π η γ (S n)`, where `S n` is
the cumulative loss estimate computed from the history of the first `n` rounds. It ignores the
observations. -/
noncomputable def linearExp3 (hπ : π ∈ simplex α) (hγ : γ ∈ Set.Icc 0 1) : Algorithm 𝓞 α ℝ :=
  weightAlgorithm (fun n x ↦ linearExp3Weights π η γ (linearExp3HistSum φ π η γ n x.1))
    (fun n a ↦ (measurable_pi_apply a).comp (((measurable_linearExp3Weights π η γ).comp
      (measurable_linearExp3HistSum φ π η γ n)).comp measurable_fst))
    (fun _ _ ↦ linearExp3Weights_mem_simplex hπ hγ.1 hγ.2 _)

lemma linearExp3_def (hπ : π ∈ simplex α) (hγ : γ ∈ Set.Icc 0 1) :
    linearExp3 (𝓞 := 𝓞) φ π η γ hπ hγ =
      weightAlgorithm (fun n x ↦ linearExp3Weights π η γ (linearExp3HistSum φ π η γ n x.1))
        (fun n a ↦ (measurable_pi_apply a).comp (((measurable_linearExp3Weights π η γ).comp
          (measurable_linearExp3HistSum φ π η γ n)).comp measurable_fst))
        (fun _ _ ↦ linearExp3Weights_mem_simplex hπ hγ.1 hγ.2 _) := (rfl)

/-- The policy of Exp3 for linear bandits at round `n` draws the arm from the weights
`linearExp3Weights π η γ (S n)` of the cumulative estimate `S n` of the history. -/
@[simp]
lemma linearExp3_policy_apply (hπ : π ∈ simplex α) (hγ : γ ∈ Set.Icc 0 1) (n : ℕ)
    (x : Hist 𝓞 α ℝ n × 𝓞) :
    (linearExp3 φ π η γ hπ hγ).policy n x =
      weightedMeasure (linearExp3Weights π η γ (linearExp3HistSum φ π η γ n x.1)) := by
  rw [linearExp3_def, weightAlgorithm_policy, weightKernel_apply]

end Algorithm

namespace LinearExp3

variable [FiniteDimensional ℝ E] [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace 𝓞] {φ : α → E} {π : α → ℝ} {g η γ : ℝ} {hπ : π ∈ simplex α}
  {hγ : γ ∈ Set.Icc 0 1} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}
  {env : Environment 𝓞 α ℝ}

/-- **The run lemma of Exp3 for linear bandits.** Along a run against any environment, the
conditional probability of playing the arm `c` at round `n`, given the history and the
observation of round `n`, is the weight of `c` computed from the arms and the feedbacks of the
rounds before `n`. -/
theorem condExp_indicator_action [IsFiniteMeasure P]
    (h : IsAlgEnvSeq O A Y (linearExp3 φ π η γ hπ hγ) env P)
    (n : ℕ) (c : α) :
    P⟦A n ⁻¹' {c} | h.filtrationObs n⟧ =ᵐ[P] fun ω ↦
      linearExp3Weights π η γ (linearExp3Sum φ π η γ (A · ω) (Y · ω) n) c := by
  have := nonempty_of_mem_simplex hπ
  set f : (Hist 𝓞 α ℝ n × 𝓞) × α → ℝ := fun z ↦ ({c} : Set α).indicator (fun _ ↦ 1) z.2
  have hf : StronglyMeasurable f :=
    ((measurable_const.indicator (measurableSet_singleton c)).comp
      measurable_snd).stronglyMeasurable
  have hind : (A n ⁻¹' {c}).indicator (fun _ ↦ (1 : ℝ)) =
      fun ω ↦ f ((history O A Y n ω, O n ω), A n ω) := by
    funext ω
    simp only [f]
    exact Set.indicator_comp_right (g := fun _ ↦ (1 : ℝ)) (A n)
  have hint : Integrable (fun ω ↦ f ((history O A Y n ω, O n ω), A n ω)) P :=
    hind ▸ (integrable_const 1).indicator (h.measurable_action n (measurableSet_singleton c))
  -- view the run as a run of a weight-based algorithm
  have halg := linearExp3_def (𝓞 := 𝓞) φ π η γ hπ hγ
  generalize linearExp3 (𝓞 := 𝓞) φ π η γ hπ hγ = alg at h halg
  subst halg
  rw [hind]
  filter_upwards [WeightAlgorithm.condExp_comp_action h n hf hint] with ω hω
  rw [hω, linearExp3HistSum_history, Finset.sum_eq_single c (fun b _ hb ↦ by simp [f, hb])
    (by simp)]
  simp [f]

variable {y : (n : ℕ) → Hist 𝓞 α ℝ n × 𝓞 → E} {n : ℕ}

/-- Along a run of Exp3 for linear bandits whose feedbacks before round `t` are the losses
`⟪φ (A s), y s (h, o)⟫` of the arms played, for the history `h` and the observation `o` of round
`s`, the conditional probability of playing the arm `c` at round `t`, given the history and the
observation of round `t`, is the weight of `c` computed from these losses. -/
theorem condExp_indicator_action_of_feedback_ae_eq [IsFiniteMeasure P]
    (h : IsAlgEnvSeq O A Y (linearExp3 φ π η γ hπ hγ) env P) {t : ℕ}
    (hY : ∀ s < t, Y s =ᵐ[P] fun ω ↦ ⟪φ (A s ω), y s (history O A Y s ω, O s ω)⟫_ℝ) (c : α) :
    P⟦A t ⁻¹' {c} | h.filtrationObs t⟧ =ᵐ[P] fun ω ↦ linearExp3Weights π η γ
      (linearExp3Sum φ π η γ (A · ω) (fun s ↦ ⟪φ (A s ω), y s (history O A Y s ω, O s ω)⟫_ℝ)
        t) c := by
  have hY' : ∀ᵐ ω ∂P, ∀ s < t, Y s ω = ⟪φ (A s ω), y s (history O A Y s ω, O s ω)⟫_ℝ :=
    ae_all_iff.2 fun s ↦ if hs : s < t then (hY s hs).mono fun _ hω _ ↦ hω
      else ae_of_all _ fun _ h ↦ absurd h hs
  filter_upwards [condExp_indicator_action h t c, hY'] with ω hω hYω
  rw [hω, linearExp3Sum_congr φ π η γ _ hYω]

variable [MeasurableSpace E] [BorelSpace E]

/-- Along a run of Exp3 for linear bandits whose feedbacks before round `n` are the losses
`⟪φ (A t), y t (h, o)⟫` of the arms played, for measurable loss vectors `y t` with
`|⟪φ c, y t (h, o)⟫| ≤ 1`, the round-wise hypotheses of `linearExp3_integral_regret_le` hold at
the σ-algebras `h.filtrationObs t` of the history and the observation of round `t`: these
σ-algebras are sub-σ-algebras, the arms are measurable, the arm of round `t` has conditional law
the weights of Exp3 for linear bandits, and the loss vectors are measurable and bounded. -/
private lemma regret_hypotheses [IsFiniteMeasure P]
    (h : IsAlgEnvSeq O A Y (linearExp3 φ π η γ hπ hγ) env P)
    (hy : ∀ t < n, Measurable (y t)) (hy1 : ∀ t < n, ∀ x c, |⟪φ c, y t x⟫_ℝ| ≤ 1)
    (hY : ∀ t < n, Y t =ᵐ[P] fun ω ↦ ⟪φ (A t ω), y t (history O A Y t ω, O t ω)⟫_ℝ) :
    (∀ t < n, h.filtrationObs t ≤ mΩ) ∧ (∀ t < n, ∀ c, MeasurableSet (A t ⁻¹' {c})) ∧
    (∀ t < n, ∀ c, P⟦A t ⁻¹' {c} | h.filtrationObs t⟧ =ᵐ[P] fun ω ↦ linearExp3Weights π η γ
      (linearExp3Sum φ π η γ (A · ω) (fun s ↦ ⟪φ (A s ω), y s (history O A Y s ω, O s ω)⟫_ℝ)
        t) c) ∧
    (∀ t < n, AEStronglyMeasurable[h.filtrationObs t]
      (fun ω ↦ y t (history O A Y t ω, O t ω)) P) ∧
    (∀ t < n, ∀ᵐ ω ∂P, ∀ c, |⟪φ c, y t (history O A Y t ω, O t ω)⟫_ℝ| ≤ 1) :=
  ⟨fun t _ ↦ h.filtrationObs.le t,
    fun t _ c ↦ h.measurable_action t (measurableSet_singleton c),
    fun _ ht ↦ condExp_indicator_action_of_feedback_ae_eq h fun s hs ↦ hY s (hs.trans ht),
    fun t ht ↦ by
      rw [h.filtrationObs_eq_comap]
      exact ((hy t ht).comp (measurable_iff_comap_le.2 le_rfl)).aestronglyMeasurable,
    fun t ht ↦ ae_of_all _ fun _ c ↦ hy1 t ht _ c⟩

include hγ in
/-- **Regret of Exp3 for adversarial linear bandits against an adaptive adversary**
[LS, Theorem 27.1], for arbitrary rates. Let `π` be an exploration distribution with invertible
design operator `V(π) = ∑ b, π b • φ b ⊗ φ b` and `⟪φ b, V(π)⁻¹ φ b⟫ ≤ g` for every arm `b`, and
let `η > 0` and `0 < γ ≤ 1` with `η g ≤ γ`. Let an adaptive adversary choose at round `t` the loss
vector `y t (h, o)`, a measurable function of the history `h` and the observation `o` of round `t`
with `|⟪φ c, y t (h, o)⟫| ≤ 1` for every arm `c`, and let the feedback `Y t` of a run of Exp3
for linear bandits be the loss `⟪φ (A t), y t (h, o)⟫` of the arm played. Then against every arm
`b`, on a space of dimension `d` and with `k` arms, the expected regret after `n` rounds is at most
`log k / η + η d n + 2 γ n`. -/
theorem integral_regret_le [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y (linearExp3 φ π η γ hπ hγ) env P)
    (hπu : IsUnit (∑ b, π b • rankOne ℝ (φ b) (φ b)))
    (hg : ∀ b, ⟪φ b, Ring.inverse (∑ b, π b • rankOne ℝ (φ b) (φ b)) (φ b)⟫_ℝ ≤ g)
    (hη : 0 < η) (hγ0 : 0 < γ) (hηγ : η * g ≤ γ) (hy : ∀ t < n, Measurable (y t))
    (hy1 : ∀ t < n, ∀ x c, |⟪φ c, y t x⟫_ℝ| ≤ 1)
    (hY : ∀ t < n, Y t =ᵐ[P] fun ω ↦ ⟪φ (A t ω), y t (history O A Y t ω, O t ω)⟫_ℝ) (b : α) :
    ∫ ω, ∑ t ∈ range n, (⟪φ (A t ω), y t (history O A Y t ω, O t ω)⟫_ℝ -
      ⟪φ b, y t (history O A Y t ω, O t ω)⟫_ℝ) ∂P ≤
      Real.log (Fintype.card α) / η + η * finrank ℝ E * n + 2 * γ * n :=
  have ⟨hm, hA, hAW, hy', hy1'⟩ := regret_hypotheses h hy hy1 hY
  linearExp3_integral_regret_le hπ hπu hg hη hγ0 hγ.2 hηγ hm hA hAW hy' hy1' b

include hγ in
/-- **Regret of Exp3 for adversarial linear bandits with tuned rates against an adaptive
adversary** [LS, Theorem 27.1]. Under the hypotheses of `LinearExp3.integral_regret_le` on a
nontrivial space of dimension `d`, with `k ≥ 2` arms, `n ≥ 1` rounds, the exploration rate
`γ = η g` and the learning rate `η = √(log k / ((2 g + d) n))`, the expected regret against every
arm is at most `2 √((2 g + d) n log k)`. -/
theorem integral_regret_le_two_mul_sqrt [Nontrivial E] [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y (linearExp3 φ π η γ hπ hγ) env P)
    (hπu : IsUnit (∑ b, π b • rankOne ℝ (φ b) (φ b)))
    (hg : ∀ b, ⟪φ b, Ring.inverse (∑ b, π b • rankOne ℝ (φ b) (φ b)) (φ b)⟫_ℝ ≤ g)
    (hk : 1 < Fintype.card α) (hn : 0 < n)
    (hη : η = √(Real.log (Fintype.card α) / ((2 * g + finrank ℝ E) * n))) (hγg : γ = η * g)
    (hy : ∀ t < n, Measurable (y t)) (hy1 : ∀ t < n, ∀ x c, |⟪φ c, y t x⟫_ℝ| ≤ 1)
    (hY : ∀ t < n, Y t =ᵐ[P] fun ω ↦ ⟪φ (A t ω), y t (history O A Y t ω, O t ω)⟫_ℝ) (b : α) :
    ∫ ω, ∑ t ∈ range n, (⟪φ (A t ω), y t (history O A Y t ω, O t ω)⟫_ℝ -
      ⟪φ b, y t (history O A Y t ω, O t ω)⟫_ℝ) ∂P ≤
      2 * √((2 * g + finrank ℝ E) * n * Real.log (Fintype.card α)) :=
  have ⟨hm, hA, hAW, hy', hy1'⟩ := regret_hypotheses h hy hy1 hY
  linearExp3_integral_regret_le_two_mul_sqrt hπ hπu hg hk hn hη hγg hγ.2 hm hA hAW hy' hy1' b

include hγ in
/-- **Regret of Exp3 for adversarial linear bandits with the Kiefer–Wolfowitz exploration against
an adaptive adversary** [LS, Theorem 27.1]. If the exploration distribution `π` has
`⟪φ b, V(π)⁻¹ φ b⟫ ≤ d` for every arm, on a nontrivial space of dimension `d` (such a
distribution exists when the features span `E`, by
`exists_mem_simplex_inner_ringInverse_le_finrank`), then under the hypotheses of
`LinearExp3.integral_regret_le` with `k ≥ 2` arms, `n ≥ 1` rounds, `γ = η d` and
`η = √(log k / (3 d n))`, the expected regret against every arm is at most `2 √(3 d n log k)`. -/
theorem integral_regret_le_two_mul_sqrt_three [Nontrivial E] [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y (linearExp3 φ π η γ hπ hγ) env P)
    (hπu : IsUnit (∑ b, π b • rankOne ℝ (φ b) (φ b)))
    (hg : ∀ b, ⟪φ b, Ring.inverse (∑ b, π b • rankOne ℝ (φ b) (φ b)) (φ b)⟫_ℝ ≤ finrank ℝ E)
    (hk : 1 < Fintype.card α) (hn : 0 < n)
    (hη : η = √(Real.log (Fintype.card α) / (3 * finrank ℝ E * n)))
    (hγd : γ = η * finrank ℝ E) (hy : ∀ t < n, Measurable (y t))
    (hy1 : ∀ t < n, ∀ x c, |⟪φ c, y t x⟫_ℝ| ≤ 1)
    (hY : ∀ t < n, Y t =ᵐ[P] fun ω ↦ ⟪φ (A t ω), y t (history O A Y t ω, O t ω)⟫_ℝ) (b : α) :
    ∫ ω, ∑ t ∈ range n, (⟪φ (A t ω), y t (history O A Y t ω, O t ω)⟫_ℝ -
      ⟪φ b, y t (history O A Y t ω, O t ω)⟫_ℝ) ∂P ≤
      2 * √(3 * finrank ℝ E * n * Real.log (Fintype.card α)) := by
  have h3 : (3 : ℝ) * finrank ℝ E = 2 * finrank ℝ E + finrank ℝ E := by ring
  rw [h3] at hη ⊢
  exact integral_regret_le_two_mul_sqrt h hπu hg hk hn hη hγd hy hy1 hY b

include hγ in
/-- **Regret of Exp3 for adversarial linear bandits with the Kiefer–Wolfowitz exploration, for
every run against an adaptive adversary** [LS, Theorem 27.1]. Let an adaptive adversary choose at
round `t` the loss vector `y t (h, o)`, a measurable function of the history `h` and of the
observation `o` of round `t`, drawn from arbitrary observation kernels `obs`, with
`|⟪φ c, y t (h, o)⟫| ≤ 1` for every arm `c`, and let its environment
`Environment.detFeedback obs (fun t x ↦ ⟪φ x.2, y t x.1⟫) _` return the loss of the arm played.
Under the hypotheses of `LinearExp3.integral_regret_le_two_mul_sqrt_three` on the exploration and
the rates, every run of Exp3 for linear bandits against it has expected regret at most
`2 √(3 d n log k)` against every arm. -/
theorem integral_regret_detFeedback_le_two_mul_sqrt_three [Nontrivial E] [IsProbabilityMeasure P]
    {obs : (n : ℕ) → Kernel (Hist 𝓞 α ℝ n) 𝓞} [∀ n, IsMarkovKernel (obs n)]
    {hf : ∀ n, Measurable fun x : (Hist 𝓞 α ℝ n × 𝓞) × α ↦ ⟪φ x.2, y n x.1⟫_ℝ}
    (h : IsAlgEnvSeq O A Y (linearExp3 φ π η γ hπ hγ)
      (Environment.detFeedback obs (fun n x ↦ ⟪φ x.2, y n x.1⟫_ℝ) hf) P)
    (hπu : IsUnit (∑ b, π b • rankOne ℝ (φ b) (φ b)))
    (hg : ∀ b, ⟪φ b, Ring.inverse (∑ b, π b • rankOne ℝ (φ b) (φ b)) (φ b)⟫_ℝ ≤ finrank ℝ E)
    (hk : 1 < Fintype.card α) (hn : 0 < n)
    (hη : η = √(Real.log (Fintype.card α) / (3 * finrank ℝ E * n)))
    (hγd : γ = η * finrank ℝ E) (hy : ∀ t < n, Measurable (y t))
    (hy1 : ∀ t < n, ∀ x c, |⟪φ c, y t x⟫_ℝ| ≤ 1) (b : α) :
    ∫ ω, ∑ t ∈ range n, (⟪φ (A t ω), y t (history O A Y t ω, O t ω)⟫_ℝ -
      ⟪φ b, y t (history O A Y t ω, O t ω)⟫_ℝ) ∂P ≤
      2 * √(3 * finrank ℝ E * n * Real.log (Fintype.card α)) :=
  integral_regret_le_two_mul_sqrt_three h hπu hg hk hn hη hγd hy hy1
    (fun t _ ↦ h.feedback_detFeedback_ae_eq t) b

end LinearExp3

end LMLExplore.Bandits
