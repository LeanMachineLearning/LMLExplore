/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.InnerProductSpace.Dual
public import LMLExplore.Bandits.StochasticMirrorDescent
public import LMLExplore.MeasureTheory.Function.ConditionalExpectation.FiniteValued
public import LMLExplore.OnlineLearning.UnitBallPotential
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Adversarial linear bandits on the unit ball

In an adversarial linear bandit on the closed unit ball of a finite-dimensional real inner
product space `E`, the learner plays at round `t` an action `A t` of norm at most `1` and observes
only the loss `y t (A t)`, where the loss `y t ∈ E →L[ℝ] ℝ`, of norm at most `1`, is chosen by an
adaptive adversary. [LS, Algorithm 17] runs follow the regularized leader with the potential
`unitBallPotential a = -log (1 - ‖a‖) - ‖a‖` on the closed ball of radius `r < 1`, on estimates
of the losses, and turns each play `a t` into a random action with mean `a t`:

* with probability `‖a t‖` it plays `a t / ‖a t‖`, on the unit sphere;
* with probability `1 - ‖a t‖` it explores: it plays `U`, drawn uniformly from the `2 d` vectors
  `b i` and `-b i` of an orthonormal basis `b` of `E` (with `d = dim E`), and estimates the loss
  by `d / (1 - ‖a t‖) * y t (U) * ⟪U, ·⟫` [LS, (28.12)]; it estimates the loss by `0` when it does
  not explore. The pseudocode of [LS, Algorithm 17] omits the signs, which its text and the
  unbiasedness of the action require.

We encode the randomness of a round by an outcome in `Option (ι × Bool)`: `none` when the
algorithm does not explore, `some (i, s)` when it explores in direction `b i` (if `s`) or `-b i`
(otherwise). `unitBallProb (a t) o` is the probability of the outcome `o`, `unitBallAction` the
action and `unitBallEstimate` the loss estimate it produces. The estimate is unbiased, the mean of
the action is the play, and the variance term `(1 - ‖a‖) * ‖unitBallEstimate b a y o‖ ^ 2` of the
full-information bound `ftrl_regret_le_of_unitBallPotential` has expectation `d * ‖y‖ ^ 2`,
independently of the play: the factor `1 - ‖a‖` cancels the importance weight. Combined with the
comparison of the regret against `u` and against `r • u`, this gives the regret bound of
[LS, Theorem 28.11].

As in `LMLExplore.Bandits.StochasticMirrorDescent`, the interaction is described round by round
relative to σ-algebras `m t`, the information available before the action of round `t` is drawn:
the play and the loss are `m t`-measurable, and the outcome of round `t` has conditional law
`unitBallProb (a t)` given `m t`. The plays are, almost surely, FTRL plays for the estimated
losses.

## Main definitions

* `unitBallProb a`: the law of the outcome of a round with play `a`.
* `unitBallAction b a o`: the action played for the outcome `o`.
* `unitBallEstimate b a y o`: the loss estimate [LS, (28.12)] for the outcome `o` and the loss
  `y`.

## Main statements

* `sum_unitBallProb_smul_unitBallAction`, `sum_unitBallProb_smul_unitBallEstimate`: the mean of
  the action is the play and the mean of the estimate is the loss.
* `sum_unitBallProb_mul_one_sub_norm_mul_norm_unitBallEstimate_sq`: the mean of
  `(1 - ‖a‖) * ‖unitBallEstimate b a y o‖ ^ 2` is `d * ‖y‖ ^ 2`.
* `isUnbiasedRound_unitBall`: a round of the algorithm is unbiased (`IsUnbiasedRound`).
* `integral_one_sub_norm_mul_norm_unitBallEstimate_sq`: the expected variance term of a round.
* `ftrl_integral_regret_le_of_unitBallEstimate`: the expected regret against every `u` of the unit
  ball is at most `(1 - r) n - log (1 - r) / η + η d n / 2`.
* `ftrl_integral_regret_le_two_mul_sqrt_of_unitBallEstimate`: [LS, Theorem 28.11], with
  `r = 1 - 2 η d` and `η = √(log n / (3 d n))`, the expected regret is at most `2 √(3 n d log n)`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 28.4.
-/

public section

open MeasureTheory Finset Metric Real LMLExplore.OnlineLearning
open scoped ProbabilityTheory

namespace LMLExplore.Bandits

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] {a : E} {o : Option (ι × Bool)}

/-- The law of the outcome of a round of [LS, Algorithm 17] with play `a`: the algorithm does not
explore with probability `‖a‖` and explores in each of the `2 d` directions `b i`, `-b i` with
probability `(1 - ‖a‖) / (2 d)`, where `d` is the cardinality of `ι`. -/
noncomputable def unitBallProb (a : E) : Option (ι × Bool) → ℝ
  | none => ‖a‖
  | some _ => (1 - ‖a‖) / (2 * Fintype.card ι)

variable (a) in
@[simp]
lemma unitBallProb_none : unitBallProb (ι := ι) a none = ‖a‖ := (rfl)

variable (a) in
@[simp]
lemma unitBallProb_some (p : ι × Bool) :
    unitBallProb a (some p) = (1 - ‖a‖) / (2 * Fintype.card ι) := (rfl)

/-- The probabilities of the outcomes are nonnegative for a play in the closed unit ball. -/
lemma unitBallProb_nonneg (ha : ‖a‖ ≤ 1) (o : Option (ι × Bool)) : 0 ≤ unitBallProb a o := by
  rcases o with _ | p
  · simp
  · simp only [unitBallProb_some]
    exact div_nonneg (sub_nonneg.2 ha) (by positivity)

/-- The probabilities of the outcomes sum to `1`. -/
lemma sum_unitBallProb [Nonempty ι] (a : E) : ∑ o, unitBallProb (ι := ι) a o = 1 := by
  have hd : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [Fintype.sum_option, unitBallProb_none, unitBallProb_some, sum_const, card_univ,
    Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  ring

variable [InnerProductSpace ℝ E] {b : OrthonormalBasis ι ℝ E} {y : E →L[ℝ] ℝ}

variable (b) in
/-- The action of [LS, Algorithm 17] for the play `a` and the outcome `o`: `a / ‖a‖` if the
algorithm does not explore (`o = none`), and `b i` or `-b i` if it explores in direction
`o = some (i, s)`. -/
noncomputable def unitBallAction (a : E) : Option (ι × Bool) → E
  | none => ‖a‖⁻¹ • a
  | some (i, s) => if s then b i else -b i

variable (b a) in
@[simp]
lemma unitBallAction_none : unitBallAction b a none = ‖a‖⁻¹ • a := (rfl)

variable (b a) in
@[simp]
lemma unitBallAction_some (i : ι) (s : Bool) :
    unitBallAction b a (some (i, s)) = if s then b i else -b i := (rfl)

/-- The actions lie in the closed unit ball. -/
lemma norm_unitBallAction_le : ‖unitBallAction b a o‖ ≤ 1 := by
  rcases o with _ | ⟨i, _ | _⟩
  · rw [unitBallAction_none, norm_smul, norm_inv, norm_norm]
    exact inv_mul_le_one_of_le₀ le_rfl (norm_nonneg a)
  all_goals simp

/-- **The mean of the action is the play**: `∑ o, unitBallProb a o • unitBallAction b a o = a`. -/
theorem sum_unitBallProb_smul_unitBallAction (b : OrthonormalBasis ι ℝ E) (a : E) :
    ∑ o, unitBallProb a o • unitBallAction b a o = a := by
  -- the exploration directions `b i` and `-b i` cancel
  have h_expl : ∑ p : ι × Bool, unitBallProb a (some p) • unitBallAction b a (some p) = 0 := by
    simp [Fintype.sum_prod_type]
  rw [Fintype.sum_option, h_expl, add_zero, unitBallProb_none, unitBallAction_none, smul_smul]
  rcases eq_or_ne ‖a‖ 0 with h | h
  · simp [norm_eq_zero.1 h]
  · rw [mul_inv_cancel₀ h, one_smul]

/-- The loss estimate [LS, (28.12)] of [LS, Algorithm 17] for the play `a`, the loss `y` and the
outcome `o`: `0` if the algorithm does not explore, and
`d / (1 - ‖a‖) * y A * ⟪A, ·⟫` for the action `A = unitBallAction b a o` if it explores, where
`d` is the cardinality of `ι`. It only uses the observed loss `y A` of the action. -/
noncomputable def unitBallEstimate (b : OrthonormalBasis ι ℝ E) (a : E) (y : E →L[ℝ] ℝ) :
    Option (ι × Bool) → E →L[ℝ] ℝ
  | none => 0
  | some p => (Fintype.card ι / (1 - ‖a‖) * y (unitBallAction b a (some p))) •
      innerSL ℝ (unitBallAction b a (some p))

variable (b a y) in
@[simp]
lemma unitBallEstimate_none : unitBallEstimate b a y none = 0 := (rfl)

variable (b a y) in
/-- When the algorithm explores in direction `b i` or `-b i`, the loss estimate is
`d / (1 - ‖a‖) * y (b i) * ⟪b i, ·⟫`, whatever the sign. -/
@[simp]
lemma unitBallEstimate_some (i : ι) (s : Bool) :
    unitBallEstimate b a y (some (i, s)) =
      (Fintype.card ι / (1 - ‖a‖) * y (b i)) • innerSL ℝ (b i) := by
  cases s <;> simp [unitBallEstimate]

/-- **The loss estimate is unbiased**: for a play in the open unit ball,
`∑ o, unitBallProb a o • unitBallEstimate b a y o = y`. -/
theorem sum_unitBallProb_smul_unitBallEstimate (b : OrthonormalBasis ι ℝ E) (ha : ‖a‖ < 1)
    (y : E →L[ℝ] ℝ) : ∑ o, unitBallProb a o • unitBallEstimate b a y o = y := by
  have h1 : 1 - ‖a‖ ≠ 0 := (sub_pos.2 ha).ne'
  conv_rhs => rw [← b.sum_apply_smul_innerSL y]
  simp only [Fintype.sum_option, unitBallEstimate_none, smul_zero, zero_add,
    Fintype.sum_prod_type, Fintype.sum_bool, unitBallProb_some, unitBallEstimate_some, smul_smul,
    ← add_smul]
  refine sum_congr rfl fun i _ ↦ ?_
  have : Nonempty ι := ⟨i⟩
  have hd : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  congr 1
  field_simp
  ring

/-- **The variance term of the estimate**: for a play in the open unit ball, the mean of
`(1 - ‖a‖) * ‖unitBallEstimate b a y o‖ ^ 2` is `d * ‖y‖ ^ 2`, where `d` is the cardinality of
`ι`. -/
theorem sum_unitBallProb_mul_one_sub_norm_mul_norm_unitBallEstimate_sq
    (b : OrthonormalBasis ι ℝ E) (ha : ‖a‖ < 1) (y : E →L[ℝ] ℝ) :
    ∑ o, unitBallProb a o * ((1 - ‖a‖) * ‖unitBallEstimate b a y o‖ ^ 2) =
      Fintype.card ι * ‖y‖ ^ 2 := by
  have h1 : 1 - ‖a‖ ≠ 0 := (sub_pos.2 ha).ne'
  rw [b.norm_dual y, mul_sum]
  simp only [Fintype.sum_option, unitBallEstimate_none, Fintype.sum_prod_type, Fintype.sum_bool,
    unitBallProb_none, unitBallProb_some, unitBallEstimate_some, norm_zero, norm_smul,
    innerSL_apply_norm, b.norm_eq_one, mul_one, norm_mul, norm_div, RCLike.norm_natCast,
    norm_eq_abs, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add]
  refine sum_congr rfl fun i _ ↦ ?_
  have : Nonempty ι := ⟨i⟩
  have hd : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [abs_of_pos (sub_pos.2 ha), mul_pow, sq_abs]
  field_simp
  ring

/-- For a play in the open unit ball, the norm of the loss estimate is at most
`d / (1 - ‖a‖) * ‖y‖`. -/
lemma norm_unitBallEstimate_le (ha : ‖a‖ < 1) :
    ‖unitBallEstimate b a y o‖ ≤ Fintype.card ι / (1 - ‖a‖) * ‖y‖ := by
  have h1 : 0 < 1 - ‖a‖ := sub_pos.2 ha
  rcases o with _ | ⟨i, s⟩
  · simp only [unitBallEstimate_none, norm_zero]
    positivity
  · rw [unitBallEstimate_some, norm_smul, innerSL_apply_norm, b.norm_eq_one, mul_one, norm_mul,
      Real.norm_of_nonneg (by positivity)]
    gcongr
    simpa [b.norm_eq_one] using y.le_opNorm (b i)

section Measurability

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω} {a : Ω → E}
  {y : Ω → E →L[ℝ] ℝ}

/-- The action of a round is measurable with respect to the σ-algebra of its play, for each
outcome. -/
lemma aestronglyMeasurable_unitBallAction (b : OrthonormalBasis ι ℝ E)
    (ha : AEStronglyMeasurable[m] a μ) (o : Option (ι × Bool)) :
    AEStronglyMeasurable[m] (fun ω ↦ unitBallAction b (a ω) o) μ := by
  rcases o with _ | p
  · simp only [unitBallAction_none]
    exact (continuous_norm.comp_aestronglyMeasurable ha).fun_inv₀.fun_smul ha
  · exact aestronglyMeasurable_const

/-- The loss estimate of a round is measurable with respect to a σ-algebra for which the play and
the loss are measurable, for each outcome. -/
lemma aestronglyMeasurable_unitBallEstimate (b : OrthonormalBasis ι ℝ E)
    (ha : AEStronglyMeasurable[m] a μ) (hy : AEStronglyMeasurable[m] y μ)
    (o : Option (ι × Bool)) :
    AEStronglyMeasurable[m] (fun ω ↦ unitBallEstimate b (a ω) (y ω) o) μ := by
  rcases o with _ | ⟨i, s⟩
  · exact aestronglyMeasurable_const
  · simp only [unitBallEstimate_some, div_eq_mul_inv]
    exact ((aestronglyMeasurable_const.fun_mul (aestronglyMeasurable_const.fun_sub
      (continuous_norm.comp_aestronglyMeasurable ha)).fun_inv₀).fun_mul
      ((ContinuousLinearMap.apply ℝ ℝ (b i)).continuous.comp_aestronglyMeasurable hy)).fun_smul
      aestronglyMeasurable_const

end Measurability

section Round

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω} [IsFiniteMeasure P]
  {a : Ω → E} {y : Ω → E →L[ℝ] ℝ} {X : Ω → Option (ι × Bool)} {r : ℝ}

/-- **A round of [LS, Algorithm 17] is unbiased.** Let the play `a` and the loss `y` be
`m`-measurable, with `‖a‖ ≤ r < 1` almost surely and `y` integrable, and let the outcome `X` of
the round have conditional law `unitBallProb a` given `m`. Then the action
`unitBallAction b a X` has conditional mean `a` and the estimate `unitBallEstimate b a y X` has
conditional mean `y` given `m`, so that [LS, Theorem 28.10] applies to the round. -/
theorem isUnbiasedRound_unitBall (b : OrthonormalBasis ι ℝ E) (hm : m ≤ mΩ)
    (hX : ∀ o, MeasurableSet (X ⁻¹' {o}))
    (hXa : ∀ o, P⟦X ⁻¹' {o} | m⟧ =ᵐ[P] fun ω ↦ unitBallProb (a ω) o)
    (ha : AEStronglyMeasurable[m] a P) (hy : AEStronglyMeasurable[m] y P) (hyi : Integrable y P)
    (hr : r < 1) (har : ∀ᵐ ω ∂P, ‖a ω‖ ≤ r) :
    IsUnbiasedRound m P y (fun ω ↦ unitBallAction b (a ω) (X ω)) a
      (fun ω ↦ unitBallEstimate b (a ω) (y ω) (X ω)) := by
  have hA (o : Option (ι × Bool)) := aestronglyMeasurable_unitBallAction b ha o
  have hY (o : Option (ι × Bool)) := aestronglyMeasurable_unitBallEstimate b ha hy o
  have hc : 0 ≤ Fintype.card ι / (1 - r) := div_nonneg (Nat.cast_nonneg _) (sub_pos.2 hr).le
  -- the estimates are bounded by `d / (1 - r) * ‖y‖`
  have hY_le (o : Option (ι × Bool)) : ∀ᵐ ω ∂P,
      ‖unitBallEstimate b (a ω) (y ω) o‖ ≤ Fintype.card ι / (1 - r) * ‖y ω‖ := by
    filter_upwards [har] with ω hω
    refine (norm_unitBallEstimate_le (hω.trans_lt hr)).trans ?_
    gcongr
  have hA_int (o : Option (ι × Bool)) : Integrable (fun ω ↦ unitBallAction b (a ω) o) P :=
    .of_bound ((hA o).mono hm) 1 (ae_of_all _ fun _ ↦ norm_unitBallAction_le)
  have hY_int (o : Option (ι × Bool)) :
      Integrable (fun ω ↦ unitBallEstimate b (a ω) (y ω) o) P :=
    (hyi.norm.const_mul _).mono' ((hY o).mono hm) (hY_le o)
  have := b.toBasis.finiteDimensional_of_finite
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  refine
    { le := hm
      integrable_action := integrable_apply_of_measurableSet_preimage (X := X)
        (g := fun ω o ↦ unitBallAction b (a ω) o) hX hA_int
      condExp_action := ?_
      integrable_apply_action := integrable_apply_of_measurableSet_preimage (X := X)
        (g := fun ω o ↦ y ω (unitBallAction b (a ω) o)) hX fun o ↦ ?_
      integrable_estimate := integrable_apply_of_measurableSet_preimage (X := X)
        (g := fun ω o ↦ unitBallEstimate b (a ω) (y ω) o) hX hY_int
      condExp_estimate := ?_
      integrable_estimate_apply_play := integrable_apply_of_measurableSet_preimage (X := X)
        (g := fun ω o ↦ unitBallEstimate b (a ω) (y ω) o (a ω)) hX fun o ↦ ?_ }
  · -- the mean of the action is the play
    refine (condExp_apply_ae_eq_sum_smul (g := fun ω o ↦ unitBallAction b (a ω) o)
      (q := fun o ω ↦ unitBallProb (a ω) o) hX hXa hA hA_int).trans ?_
    exact ae_of_all _ fun ω ↦ sum_unitBallProb_smul_unitBallAction b (a ω)
  · -- the loss of the action is bounded by `‖y‖`
    refine hyi.norm.mono' (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hyi.1.prodMk ((hA o).mono hm))) (ae_of_all _ fun ω ↦ ?_)
    exact (y ω).le_opNorm_of_le norm_unitBallAction_le |>.trans_eq (mul_one _)
  · -- the mean of the estimate is the loss
    refine (condExp_apply_ae_eq_sum_smul (g := fun ω o ↦ unitBallEstimate b (a ω) (y ω) o)
      (q := fun o ω ↦ unitBallProb (a ω) o) hX hXa hY hY_int).trans ?_
    filter_upwards [har] with ω hω
    exact sum_unitBallProb_smul_unitBallEstimate b (hω.trans_lt hr) (y ω)
  · -- the estimated loss of the play is bounded by `d / (1 - r) * ‖y‖`
    refine (hyi.norm.const_mul (Fintype.card ι / (1 - r))).mono'
      (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        ((hY_int o).1.prodMk (ha.mono hm))) ?_
    filter_upwards [har, hY_le o] with ω hω hYω
    calc ‖unitBallEstimate b (a ω) (y ω) o (a ω)‖
        ≤ ‖unitBallEstimate b (a ω) (y ω) o‖ * 1 :=
          (ContinuousLinearMap.le_opNorm_of_le _ (hω.trans hr.le))
      _ ≤ Fintype.card ι / (1 - r) * ‖y ω‖ := by rw [mul_one]; exact hYω

omit [IsFiniteMeasure P] in
/-- The variance term of a round is measurable with respect to a σ-algebra for which the play and
the loss are measurable, for each outcome. -/
private lemma aestronglyMeasurable_one_sub_norm_mul_norm_unitBallEstimate_sq
    (ha : AEStronglyMeasurable[m] a P) (hy : AEStronglyMeasurable[m] y P) (o : Option (ι × Bool)) :
    AEStronglyMeasurable[m]
      (fun ω ↦ (1 - ‖a ω‖) * ‖unitBallEstimate b (a ω) (y ω) o‖ ^ 2) P :=
  (aestronglyMeasurable_const.fun_sub (continuous_norm.comp_aestronglyMeasurable ha)).fun_mul
    ((continuous_norm.comp_aestronglyMeasurable
      (aestronglyMeasurable_unitBallEstimate b ha hy o)).fun_pow 2)

omit [IsFiniteMeasure P] in
/-- For each outcome, the variance term of a round is integrable: it is at most
`d ^ 2 / (1 - r) * ‖y‖ ^ 2`. -/
private lemma integrable_one_sub_norm_mul_norm_unitBallEstimate_sq_of_outcome
    (b : OrthonormalBasis ι ℝ E) (hm : m ≤ mΩ) (ha : AEStronglyMeasurable[m] a P)
    (hy : AEStronglyMeasurable[m] y P) (hy2 : Integrable (fun ω ↦ ‖y ω‖ ^ 2) P) (hr : r < 1)
    (har : ∀ᵐ ω ∂P, ‖a ω‖ ≤ r) (o : Option (ι × Bool)) :
    Integrable (fun ω ↦ (1 - ‖a ω‖) * ‖unitBallEstimate b (a ω) (y ω) o‖ ^ 2) P := by
  refine (hy2.const_mul (Fintype.card ι ^ 2 / (1 - r))).mono'
    ((aestronglyMeasurable_one_sub_norm_mul_norm_unitBallEstimate_sq ha hy o).mono hm) ?_
  filter_upwards [har] with ω hω
  have h1 : 0 < 1 - ‖a ω‖ := sub_pos.2 (hω.trans_lt hr)
  have h_le := norm_unitBallEstimate_le (b := b) (y := y ω) (o := o) (hω.trans_lt hr)
  rw [Real.norm_of_nonneg (by positivity)]
  calc (1 - ‖a ω‖) * ‖unitBallEstimate b (a ω) (y ω) o‖ ^ 2
      ≤ (1 - ‖a ω‖) * (Fintype.card ι / (1 - ‖a ω‖) * ‖y ω‖) ^ 2 := by gcongr
    _ = Fintype.card ι ^ 2 / (1 - ‖a ω‖) * ‖y ω‖ ^ 2 := by field_simp
    _ ≤ Fintype.card ι ^ 2 / (1 - r) * ‖y ω‖ ^ 2 := by gcongr

omit [IsFiniteMeasure P] in
/-- The variance term `(1 - ‖a‖) * ‖unitBallEstimate b a y X‖ ^ 2` of a round is integrable when
`‖y‖ ^ 2` is. -/
lemma integrable_one_sub_norm_mul_norm_unitBallEstimate_sq (b : OrthonormalBasis ι ℝ E)
    (hm : m ≤ mΩ) (hX : ∀ o, MeasurableSet (X ⁻¹' {o})) (ha : AEStronglyMeasurable[m] a P)
    (hy : AEStronglyMeasurable[m] y P) (hy2 : Integrable (fun ω ↦ ‖y ω‖ ^ 2) P) (hr : r < 1)
    (har : ∀ᵐ ω ∂P, ‖a ω‖ ≤ r) :
    Integrable (fun ω ↦ (1 - ‖a ω‖) * ‖unitBallEstimate b (a ω) (y ω) (X ω)‖ ^ 2) P :=
  integrable_apply_of_measurableSet_preimage (X := X)
    (g := fun ω o ↦ (1 - ‖a ω‖) * ‖unitBallEstimate b (a ω) (y ω) o‖ ^ 2) hX
    (integrable_one_sub_norm_mul_norm_unitBallEstimate_sq_of_outcome b hm ha hy hy2 hr har)

/-- **The expected variance term of a round of [LS, Algorithm 17].** Under the hypotheses of
`isUnbiasedRound_unitBall`, with `‖y‖ ^ 2` integrable, the expectation of
`(1 - ‖a‖) * ‖unitBallEstimate b a y X‖ ^ 2` is `d * E[‖y‖ ^ 2]`, where `d` is the cardinality of
`ι`: the factor `1 - ‖a‖` cancels the importance weight of the estimate. -/
theorem integral_one_sub_norm_mul_norm_unitBallEstimate_sq (b : OrthonormalBasis ι ℝ E)
    (hm : m ≤ mΩ) (hX : ∀ o, MeasurableSet (X ⁻¹' {o}))
    (hXa : ∀ o, P⟦X ⁻¹' {o} | m⟧ =ᵐ[P] fun ω ↦ unitBallProb (a ω) o)
    (ha : AEStronglyMeasurable[m] a P) (hy : AEStronglyMeasurable[m] y P)
    (hy2 : Integrable (fun ω ↦ ‖y ω‖ ^ 2) P) (hr : r < 1) (har : ∀ᵐ ω ∂P, ‖a ω‖ ≤ r) :
    ∫ ω, (1 - ‖a ω‖) * ‖unitBallEstimate b (a ω) (y ω) (X ω)‖ ^ 2 ∂P =
      Fintype.card ι * ∫ ω, ‖y ω‖ ^ 2 ∂P := by
  have hg (o : Option (ι × Bool)) := aestronglyMeasurable_one_sub_norm_mul_norm_unitBallEstimate_sq
    (b := b) ha hy o
  rw [integral_apply_eq_integral_sum_smul (g := fun ω o ↦
      (1 - ‖a ω‖) * ‖unitBallEstimate b (a ω) (y ω) o‖ ^ 2)
    (q := fun o ω ↦ unitBallProb (a ω) o) hm hX hXa hg
    (integrable_one_sub_norm_mul_norm_unitBallEstimate_sq_of_outcome b hm ha hy hy2 hr har),
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [har] with ω hω
  exact sum_unitBallProb_mul_one_sub_norm_mul_norm_unitBallEstimate_sq b (hω.trans_lt hr) (y ω)

end Round

section Regret

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {m : ℕ → MeasurableSpace Ω} {a : ℕ → Ω → E} {y : ℕ → Ω → E →L[ℝ] ℝ}
  {X : ℕ → Ω → Option (ι × Bool)} {n : ℕ} {r η : ℝ} {u : E}

/-- Moving the comparator from `u` to `r • u`, for `r ≤ 1` and `‖u‖ ≤ 1`, costs at most
`1 - r` per round against losses of norm at most `1`. -/
private lemma integral_sum_apply_smul_sub_le (hr1 : r ≤ 1) (hu : ‖u‖ ≤ 1)
    (hyi : ∀ t < n, Integrable (y t) P) (hy1 : ∀ t < n, ∀ᵐ ω ∂P, ‖y t ω‖ ≤ 1) :
    ∫ ω, ∑ t ∈ range n, y t ω (r • u - u) ∂P ≤ (1 - r) * n := by
  have h_norm : ‖r • u - u‖ ≤ 1 - r := by
    have h_eq : r • u - u = (r - 1) • u := by rw [sub_smul, one_smul]
    rw [h_eq, norm_smul, Real.norm_of_nonpos (by linarith)]
    nlinarith [norm_nonneg u]
  rw [integral_finsetSum _ fun t ht ↦ (hyi t (mem_range.1 ht)).apply_continuousLinearMap _]
  calc ∑ t ∈ range n, ∫ ω, y t ω (r • u - u) ∂P ≤ ∑ _t ∈ range n, (1 - r) := by
        refine sum_le_sum fun t ht ↦ ?_
        calc ∫ ω, y t ω (r • u - u) ∂P ≤ ∫ _, (1 - r) ∂P := by
              refine integral_mono_ae ((hyi t (mem_range.1 ht)).apply_continuousLinearMap _)
                (integrable_const _) ?_
              filter_upwards [hy1 t (mem_range.1 ht)] with ω hω
              calc y t ω (r • u - u) ≤ ‖y t ω‖ * ‖r • u - u‖ :=
                    (le_abs_self _).trans ((y t ω).le_opNorm (r • u - u))
                _ ≤ 1 * (1 - r) := mul_le_mul hω h_norm (norm_nonneg _) zero_le_one
                _ = 1 - r := one_mul _
          _ = 1 - r := by simp
    _ = (1 - r) * n := by rw [sum_const, card_range, nsmul_eq_mul, mul_comm]

/-- **Regret of FTRL with bandit feedback on the unit ball.** Let `r < 1` and `η > 0`. For
each round `t < n`, let the play `a t` and the loss `y t`, of norm at most `1`, be
`m t`-measurable, and let the outcome `X t` have conditional law `unitBallProb (a t)` given
`m t`. Let the plays be, almost surely, FTRL plays on the closed ball of radius `r` with potential
`unitBallPotential` and learning rate `η` for the estimated losses `unitBallEstimate b a y X`.
Then the actions `unitBallAction b (a t) (X t)` satisfy, for every `u` of the closed unit ball,
`E[∑ t < n, y t (A t - u)] ≤ (1 - r) n - log (1 - r) / η + η d n / 2`,
where `d` is the cardinality of `ι`. The last term is half the corresponding term of [LS], which
bounds the stability terms of FTRL through the Hessian of the potential on a segment rather than
at the plays. -/
theorem ftrl_integral_regret_le_of_unitBallEstimate (b : OrthonormalBasis ι ℝ E) (hr : r < 1)
    (hη : 0 < η) (hm : ∀ t < n, m t ≤ mΩ)
    (hX : ∀ t < n, ∀ o, MeasurableSet (X t ⁻¹' {o}))
    (hXa : ∀ t < n, ∀ o, P⟦X t ⁻¹' {o} | m t⟧ =ᵐ[P] fun ω ↦ unitBallProb (a t ω) o)
    (ha : ∀ t < n, AEStronglyMeasurable[m t] (a t) P)
    (hy : ∀ t < n, AEStronglyMeasurable[m t] (y t) P) (hy1 : ∀ t < n, ∀ᵐ ω ∂P, ‖y t ω‖ ≤ 1)
    (hftrl : ∀ᵐ ω ∂P, ∀ t ≤ n, IsFTRLPlay (closedBall 0 r) unitBallPotential η
      (fun s ↦ unitBallEstimate b (a s ω) (y s ω) (X s ω)) t (a t ω))
    (hu : ‖u‖ ≤ 1) :
    ∫ ω, ∑ t ∈ range n, y t ω (unitBallAction b (a t ω) (X t ω) - u) ∂P ≤
      (1 - r) * n - log (1 - r) / η + η * Fintype.card ι * n / 2 := by
  have := b.toBasis.finiteDimensional_of_finite
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  set A : ℕ → Ω → E := fun t ω ↦ unitBallAction b (a t ω) (X t ω) with hA_def
  set Y : ℕ → Ω → E →L[ℝ] ℝ := fun t ω ↦ unitBallEstimate b (a t ω) (y t ω) (X t ω) with hY_def
  have har (t : ℕ) (ht : t ≤ n) : ∀ᵐ ω ∂P, ‖a t ω‖ ≤ r := by
    filter_upwards [hftrl] with ω hω
    exact mem_closedBall_zero_iff.1 (hω t ht).mem
  have hyi (t : ℕ) (ht : t < n) : Integrable (y t) P :=
    .of_bound ((hy t ht).mono (hm t ht)) 1 (hy1 t ht)
  have hy2 (t : ℕ) (ht : t < n) : Integrable (fun ω ↦ ‖y t ω‖ ^ 2) P := by
    refine .of_bound (((hy t ht).mono (hm t ht)).norm.pow 2) 1 ?_
    filter_upwards [hy1 t ht] with ω hω
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_one₀ (norm_nonneg _) hω
  have hround (t : ℕ) (ht : t < n) : IsUnbiasedRound (m t) P (y t) (A t) (a t) (Y t) :=
    isUnbiasedRound_unitBall b (hm t ht) (hX t ht) (hXa t ht) (ha t ht) (hy t ht) (hyi t ht) hr
      (har t ht.le)
  -- the variance term of each round has expectation at most `d`
  have h_var (t : ℕ) (ht : t < n) :
      ∫ ω, (1 - ‖a t ω‖) * ‖Y t ω‖ ^ 2 ∂P ≤ (Fintype.card ι : ℝ) := by
    rw [hY_def, integral_one_sub_norm_mul_norm_unitBallEstimate_sq b (hm t ht) (hX t ht) (hXa t ht)
      (ha t ht) (hy t ht) (hy2 t ht) hr (har t ht.le)]
    refine mul_le_of_le_one_right (Nat.cast_nonneg _) ?_
    calc ∫ ω, ‖y t ω‖ ^ 2 ∂P ≤ ∫ _, (1 : ℝ) ∂P := by
          refine integral_mono_ae (hy2 t ht) (integrable_const 1) ?_
          filter_upwards [hy1 t ht] with ω hω
          exact pow_le_one₀ (norm_nonneg _) hω
      _ = 1 := by simp
  have h_var_int (t : ℕ) (ht : t < n) : Integrable (fun ω ↦ (1 - ‖a t ω‖) * ‖Y t ω‖ ^ 2) P :=
    integrable_one_sub_norm_mul_norm_unitBallEstimate_sq b (hm t ht) (hX t ht) (ha t ht) (hy t ht)
      (hy2 t ht) hr (har t ht.le)
  -- the regret against `r • u`, through the full-information bound
  -- the closed ball of radius `r` contains the plays, so `r` is nonnegative
  obtain ⟨ω₀, hω₀⟩ := hftrl.exists
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (mem_closedBall_zero_iff.1 (hω₀ 0 (Nat.zero_le n)).mem)
  have hru : r • u ∈ closedBall (0 : E) r := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hr0]
    exact mul_le_of_le_one_right hr0 hu
  have h_ru : ∫ ω, ∑ t ∈ range n, y t ω (A t ω - r • u) ∂P ≤
      -log (1 - r) / η + η / 2 * Fintype.card ι * n := by
    refine (integral_sum_apply_sub_le_of_ae_le hround
      (B := fun ω ↦ -log (1 - r) / η + η / 2 * ∑ t ∈ range n, (1 - ‖a t ω‖) * ‖Y t ω‖ ^ 2)
      ((integrable_const _).add ((integrable_finsetSum _ fun t ht ↦
        h_var_int t (mem_range.1 ht)).const_mul _)) ?_).trans ?_
    · filter_upwards [hftrl] with ω hω
      exact ftrl_regret_le_of_unitBallPotential (convex_closedBall 0 r) subset_rfl hr hη
        (fun t ↦ Y t ω) (fun t ↦ a t ω) hω hru
    · rw [integral_add (integrable_const _) ((integrable_finsetSum _ fun t ht ↦
        h_var_int t (mem_range.1 ht)).const_mul _), integral_const_mul,
        integral_finsetSum _ fun t ht ↦ h_var_int t (mem_range.1 ht)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      have h_sum : ∑ t ∈ range n, ∫ ω, (1 - ‖a t ω‖) * ‖Y t ω‖ ^ 2 ∂P ≤
          ∑ _t ∈ range n, (Fintype.card ι : ℝ) :=
        sum_le_sum fun t ht ↦ h_var t (mem_range.1 ht)
      rw [sum_const, card_range, nsmul_eq_mul] at h_sum
      have : η / 2 * ∑ t ∈ range n, ∫ ω, (1 - ‖a t ω‖) * ‖Y t ω‖ ^ 2 ∂P ≤
          η / 2 * (n * Fintype.card ι) := mul_le_mul_of_nonneg_left h_sum (by positivity)
      linarith
  -- the comparison of `u` with `r • u` costs at most `1 - r` per round
  have h_shift_int : Integrable (fun ω ↦ ∑ t ∈ range n, y t ω (r • u - u)) P :=
    integrable_finsetSum _ fun t ht ↦ (hyi t (mem_range.1 ht)).apply_continuousLinearMap _
  have h_shift := integral_sum_apply_smul_sub_le hr.le hu hyi hy1
  -- combine
  have h_split : ∫ ω, ∑ t ∈ range n, y t ω (A t ω - u) ∂P =
      ∫ ω, ∑ t ∈ range n, y t ω (A t ω - r • u) ∂P +
        ∫ ω, ∑ t ∈ range n, y t ω (r • u - u) ∂P := by
    rw [← integral_add (integrable_finsetSum _ fun t ht ↦
      (hround t (mem_range.1 ht)).integrable_apply_action_sub (r • u)) h_shift_int]
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    simp only [← sum_add_distrib, ← map_add, sub_add_sub_cancel]
  rw [h_split]
  calc _ ≤ -log (1 - r) / η + η / 2 * Fintype.card ι * n + (1 - r) * n := add_le_add h_ru h_shift
    _ = (1 - r) * n - log (1 - r) / η + η * Fintype.card ι * n / 2 := by ring

/-- **Regret of FTRL with bandit feedback on the unit ball** [LS, Theorem 28.11]. Let `n ≥ 2`,
let `d ≥ 1` be the cardinality of `ι`, and tune the learning rate to `η = √(log n / (3 d n))` and
the radius to `r = 1 - 2 η d`. Under the hypotheses of
`ftrl_integral_regret_le_of_unitBallEstimate`, the expected regret against every `u` of the closed
unit ball is at most `2 √(3 n d log n)`. The FTRL plays lie in the closed ball of radius `r`, so
the hypotheses force `1 - 2 η d ≥ 0`; when `1 - 2 η d < 0` the ball is empty and the algorithm is
not defined, and the bound `2 √(3 n d log n)` is then at least `3 n`, more than the trivial bound
`2 n`. -/
theorem ftrl_integral_regret_le_two_mul_sqrt_of_unitBallEstimate [Nonempty ι]
    (b : OrthonormalBasis ι ℝ E) (hn : 2 ≤ n) (hη : η = √(log n / (3 * Fintype.card ι * n)))
    (hr : r = 1 - 2 * η * Fintype.card ι)
    (hm : ∀ t < n, m t ≤ mΩ) (hX : ∀ t < n, ∀ o, MeasurableSet (X t ⁻¹' {o}))
    (hXa : ∀ t < n, ∀ o, P⟦X t ⁻¹' {o} | m t⟧ =ᵐ[P] fun ω ↦ unitBallProb (a t ω) o)
    (ha : ∀ t < n, AEStronglyMeasurable[m t] (a t) P)
    (hy : ∀ t < n, AEStronglyMeasurable[m t] (y t) P) (hy1 : ∀ t < n, ∀ᵐ ω ∂P, ‖y t ω‖ ≤ 1)
    (hftrl : ∀ᵐ ω ∂P, ∀ t ≤ n, IsFTRLPlay (closedBall 0 r) unitBallPotential η
      (fun s ↦ unitBallEstimate b (a s ω) (y s ω) (X s ω)) t (a t ω))
    (hu : ‖u‖ ≤ 1) :
    ∫ ω, ∑ t ∈ range n, y t ω (unitBallAction b (a t ω) (X t ω) - u) ∂P ≤
      2 * √(3 * n * Fintype.card ι * log n) := by
  set d : ℝ := (Fintype.card ι : ℝ) with hd_def
  have hd : 1 ≤ d := Nat.one_le_cast.2 Fintype.card_pos
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : log 2 ≤ log n := log_le_log two_pos hn2
  have hL0 : 0 < log n := (log_pos one_lt_two).trans_le hL
  have hη0 : 0 < η := by rw [hη]; positivity
  -- the learning rate satisfies `log n = 3 d n η ^ 2`
  have hη_sq : log n = 3 * d * n * η ^ 2 := by
    rw [hη, sq_sqrt (by positivity)]
    field_simp
  have h1r : 1 - r = 2 * η * d := by rw [hr]; ring
  -- the exploration rate `1 - r = 2 η d` is at least `1 / n`
  have h_ge : 1 ≤ 2 * η * d * n := by
    have h_sq : 1 ≤ (2 * η * d * n) ^ 2 := by
      have : (2 * η * d * n) ^ 2 = 4 / 3 * (d * n) * log n := by rw [hη_sq]; ring
      rw [this]
      have := one_sub_inv_le_log_of_pos two_pos
      have : (2 : ℝ) ≤ d * n := by nlinarith
      nlinarith
    nlinarith [show 0 < 2 * η * d * n by positivity]
  have h_log : -log (1 - r) ≤ log n := by
    rw [h1r]
    have := log_nonneg h_ge
    rw [log_mul (by positivity) (by positivity)] at this
    linarith
  have h2ηd : 0 < 2 * η * d := by positivity
  refine (ftrl_integral_regret_le_of_unitBallEstimate b (by linarith) hη0 hm hX hXa ha hy hy1
    hftrl hu).trans ?_
  -- the bound is at most `6 d n η = 2 √(3 n d log n)`
  have h_sqrt : √(3 * n * d * log n) = 3 * d * n * η := by
    rw [hη_sq, show 3 * n * d * (3 * d * n * η ^ 2) = (3 * d * n * η) ^ 2 by ring,
      sqrt_sq (by positivity)]
  rw [h_sqrt, h1r]
  have h_div : -(log (2 * η * d) / η) ≤ 3 * d * n * η := by
    rw [← neg_div, div_le_iff₀ hη0]
    rw [h1r] at h_log
    nlinarith
  have hηdn : 0 < η * d * n := by positivity
  rw [← hd_def]
  linarith

end Regret

end LMLExplore.Bandits
