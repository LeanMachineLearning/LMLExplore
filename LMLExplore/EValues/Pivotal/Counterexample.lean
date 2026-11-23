/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Pivotal.Basic
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.MeasureTheory.Integral.Bochner.Set
import LMLExplore.MeasureTheory.Measure.TotalVariation.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.ConditionalProbability
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex

/-!
# Pivotal exact e-variables: what fails without boundedness or uniformity

The characterization of `LMLExplore.EValues.Pivotal.Basic` needs both of its hypotheses: the
e-variable is bounded, and its e-power is uniformly positive over the alternative. This file
gives the two examples of [EVR26, Note 26] that show it, both on `[0, 1]` with a simple null, for
which every random variable is pivotal.

* Without boundedness, the "only if" direction of [ZRW24, Conjecture 6.8] fails ([EVR26,
  Note 26, Theorem 2 (1)]): for the Lebesgue measure `P` on `[0, 1]`, disjoint intervals `A_n`
  of length `δ_n = 2 ^ (-n - 1) e ^ (-2 n)` and the alternatives
  `Q_n = (1 - 1 / n) P + (1 / n) P(· | A_n)`, the unbounded e-variable
  `X = 1 / 2 + ∑_{n ≥ 1} e ^ (2 n) 1_{A_n}` is exact with `E_{Q_n} log X ≥ 2 - log 2` for every
  `n ≥ 1`, although `Q_n → P` in total variation. No bounded exact e-variable has uniformly
  positive e-power against the `Q_n`.
* With pointwise instead of uniform positivity, the separation is not necessary, even for bounded
  e-variables ([EVR26, Note 26, Pointwise positivity, first example]): for `P` uniform on
  `[0, 1 / 2]`, `R` uniform on `(1 / 2, 1]` and `Q_n = (1 - 1 / n) P + (1 / n) R`, the exact
  e-variable equal to `1` on `[0, 1 / 2]` and to `2` on `(1 / 2, 1]` has e-power `(log 2) / n > 0`
  against every `Q_n`, although `Q_n → P` in total variation.

## Main statements

* `ProbabilityTheory.exists_isExactEVar_le_eintegral_log_and_tendsto_tvDist`: the first example.
* `ProbabilityTheory.exists_isExactEVar_eintegral_log_eq_and_tendsto_tvDist`: the second example.

## Implementation notes

This file ports and adapts `EValuesResearch/Results/PivotalEVariables.lean` of the paper project
`RemyDegenne/evalues_research`, which names the laws and e-variables of the examples; here they
are private and the statements are existential.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 26 and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026.
* [ZRW24] Z. Zhang, A. Ramdas and R. Wang, *On the existence of powerful p-values and e-values for
  composite hypotheses*, arXiv:2305.16539, Conjecture 6.8.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology unitInterval

namespace ProbabilityTheory

/-! ### Without boundedness, the separation is not necessary -/

/-- The mass `δ_n = 2 ^ (-n - 1) e ^ (-2 n)` of the set `A_n`. -/
private noncomputable def bumpMass (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (n + 1))⁻¹ * Real.exp (-(2 * n))

/-- The interval `A_n = [2 ^ (-n), 2 ^ (-n) + δ_n)` of `[0, 1]`, of Lebesgue measure `δ_n` for
`n ≥ 1`. The sets `A_n`, `n ≥ 1`, are disjoint, as `A_n ⊆ [2 ^ (-n), 2 ^ (-n + 1))`. -/
private def bumpSet (n : ℕ) : Set I :=
  {x | ((2 : ℝ) ^ n)⁻¹ ≤ (x : ℝ) ∧ (x : ℝ) < ((2 : ℝ) ^ n)⁻¹ + bumpMass n}

/-- The e-variable `X = 1 / 2 + ∑_{n ≥ 1} e ^ (2 n) 1_{A_n}`. -/
private noncomputable def bumpEVar (x : I) : ℝ≥0∞ :=
  2⁻¹ + ∑' n : ℕ, (bumpSet (n + 1)).indicator (fun _ ↦ ENNReal.ofReal (Real.exp (2 * (n + 1)))) x

/-- The alternative `Q_n = (1 - 1 / n) P + (1 / n) P(· | A_n)`, with `P` the Lebesgue measure on
`[0, 1]`. -/
private noncomputable def bumpAlt (n : ℕ) : Measure I :=
  (1 - (n : ℝ≥0)⁻¹) • volume + (n : ℝ≥0)⁻¹ • volume[|bumpSet n]

private lemma bumpMass_pos (n : ℕ) : 0 < bumpMass n := by
  unfold bumpMass
  positivity

private lemma bumpMass_le (n : ℕ) : bumpMass n ≤ ((2 : ℝ) ^ (n + 1))⁻¹ := by
  unfold bumpMass
  calc ((2 : ℝ) ^ (n + 1))⁻¹ * Real.exp (-(2 * n))
  _ ≤ ((2 : ℝ) ^ (n + 1))⁻¹ * 1 := by
    gcongr
    exact Real.exp_le_one_iff.2 (by simp only [Left.neg_nonpos_iff]; positivity)
  _ = ((2 : ℝ) ^ (n + 1))⁻¹ := mul_one _

private lemma measurableSet_bumpSet (n : ℕ) : MeasurableSet (bumpSet n) :=
  (measurableSet_le measurable_const measurable_subtypeVal).inter
    (measurableSet_lt measurable_subtypeVal measurable_const)

/-- The interval `A_n` has Lebesgue measure `δ_n` for `n ≥ 1`. -/
private lemma volume_bumpSet {n : ℕ} (hn : 1 ≤ n) :
    volume (bumpSet n) = ENNReal.ofReal (bumpMass n) := by
  have h2 : (2 : ℝ) ≤ 2 ^ n := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  have h2' : (2 : ℝ) ≤ 2 ^ (n + 1) := h2.trans (pow_le_pow_right₀ (by norm_num) n.le_succ)
  have ha : ((2 : ℝ) ^ n)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
  have ha' : ((2 : ℝ) ^ (n + 1))⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2'
  have ha0 : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
  have hδ := bumpMass_le n
  have hδ0 := bumpMass_pos n
  have hset : bumpSet n = Ico (⟨((2 : ℝ) ^ n)⁻¹, ha0, by linarith⟩ : I)
      ⟨((2 : ℝ) ^ n)⁻¹ + bumpMass n, by linarith, by linarith⟩ := by
    ext x
    simp [bumpSet, ← Subtype.coe_le_coe, ← Subtype.coe_lt_coe]
  rw [hset, unitInterval.volume_Ico]
  congr 1
  ring

private lemma volume_bumpSet_ne_zero {n : ℕ} (hn : 1 ≤ n) : volume (bumpSet n) ≠ 0 := by
  rw [volume_bumpSet hn]
  exact (ENNReal.ofReal_pos.2 (bumpMass_pos n)).ne'

private lemma measurable_bumpEVar : Measurable bumpEVar :=
  measurable_const.add
    (Measurable.tsum fun _ ↦ measurable_const.indicator (measurableSet_bumpSet _))

/-- The unbounded e-variable is exact: `E_P X = 1 / 2 + ∑_{n ≥ 1} 2 ^ (-n - 1) = 1`. -/
private lemma isExactEVar_bumpEVar : IsExactEVar bumpEVar {(volume : Measure I)} := by
  refine .of_lintegral_eq_one measurable_bumpEVar fun P hP ↦ ?_
  rw [mem_singleton_iff.1 hP]
  -- each term contributes `e ^ (2 (n + 1)) δ_{n + 1} = 2 ^ (-(n + 2))`
  have hterm (n : ℕ) : ∫⁻ x, (bumpSet (n + 1)).indicator
      (fun _ ↦ ENNReal.ofReal (Real.exp (2 * (n + 1)))) x ∂volume = 2⁻¹ ^ (n + 2) := by
    rw [lintegral_indicator_const (measurableSet_bumpSet _), volume_bumpSet (by omega),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    simp [bumpMass, mul_left_comm (Real.exp _), ← Real.exp_add, ENNReal.ofReal_inv_of_pos,
      ENNReal.ofReal_pow, ENNReal.inv_pow]
  unfold bumpEVar
  rw [lintegral_add_left measurable_const, lintegral_tsum fun _ ↦
    (measurable_const.indicator (measurableSet_bumpSet _)).aemeasurable]
  simp_rw [hterm, pow_add, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  simp [pow_two, ← mul_assoc, ENNReal.mul_inv_cancel, ENNReal.inv_two_add_inv_two]

private lemma isProbabilityMeasure_bumpAlt (n : ℕ) : IsProbabilityMeasure (bumpAlt n) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [bumpAlt, CharP.cast_eq_zero, inv_zero, tsub_zero, one_smul, zero_smul, add_zero]
    infer_instance
  have := cond_isProbabilityMeasure (volume_bumpSet_ne_zero hn)
  rw [bumpAlt, ← Measure.coe_nnreal_smul, ← Measure.coe_nnreal_smul]
  exact TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul
    (by norm_cast; exact tsub_add_cancel_of_le (Nat.cast_inv_le_one n)) _ _

/-- The alternative `Q_n` gives mass at least `1 / n` to `A_n`. -/
private lemma inv_le_measureReal_bumpAlt_bumpSet {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ)⁻¹ ≤ (bumpAlt n).real (bumpSet n) := by
  have := isProbabilityMeasure_bumpAlt n
  have h : (((n : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) ≤ bumpAlt n (bumpSet n) := by
    rw [bumpAlt, add_apply, Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply,
      cond_apply_self (volume_bumpSet_ne_zero hn) (measure_ne_top _ _), mul_one]
    exact le_add_self
  have h' := ENNReal.toReal_mono (measure_ne_top _ _) h
  rwa [ENNReal.coe_toReal, NNReal.coe_inv, NNReal.coe_natCast, ← measureReal_def] at h'

/-- `log X ≥ - log 2 + (2 n + log 2) 1_{A_n}`: `X ≥ 1 / 2` everywhere and `X ≥ e ^ (2 n)` on
`A_n`. -/
private lemma le_log_bumpEVar {n : ℕ} (hn : 1 ≤ n) (x : I) :
    ((-Real.log 2 + (bumpSet n).indicator (fun _ ↦ 2 * n + Real.log 2) x : ℝ) : EReal) ≤
      ENNReal.log (bumpEVar x) := by
  by_cases hx : x ∈ bumpSet n
  · rw [indicator_of_mem hx, show -Real.log 2 + (2 * n + Real.log 2) = 2 * (n : ℝ) by ring,
      ← ENNReal.log_ofReal_exp]
    refine ENNReal.log_monotone ?_
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    calc ENNReal.ofReal (Real.exp (2 * ((m + 1 : ℕ) : ℝ)))
    _ = (bumpSet (m + 1)).indicator (fun _ ↦ ENNReal.ofReal (Real.exp (2 * (m + 1)))) x := by
      simp only [indicator_of_mem hx, Nat.cast_add_one]
    _ ≤ ∑' k : ℕ, (bumpSet (k + 1)).indicator
        (fun _ ↦ ENNReal.ofReal (Real.exp (2 * (k + 1)))) x :=
      le_tsum (fun k : ℕ ↦ (bumpSet (k + 1)).indicator
        (fun _ ↦ ENNReal.ofReal (Real.exp (2 * (k + 1)))) x) m
    _ ≤ bumpEVar x := le_add_self
  · rw [indicator_of_notMem hx, add_zero, ← Real.log_inv, ← ENNReal.log_ofReal_of_pos (by norm_num)]
    refine ENNReal.log_monotone ?_
    calc ENNReal.ofReal 2⁻¹ = 2⁻¹ := by
          rw [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ bumpEVar x := le_self_add

/-- The unbounded e-variable has uniformly positive e-power:
`E_{Q_n} log X ≥ (1 - 1 / n) log (1 / 2) + (1 / n) log (e ^ (2 n)) ≥ 2 - log 2` for `n ≥ 1`. -/
private lemma le_eintegral_log_bumpEVar {n : ℕ} (hn : 1 ≤ n) :
    ((2 - Real.log 2 : ℝ) : EReal) ≤ ∫ᵉ x, ENNReal.log (bumpEVar x) ∂(bumpAlt n) := by
  have := isProbabilityMeasure_bumpAlt n
  have hint : Integrable (fun x ↦ -Real.log 2 +
      (bumpSet n).indicator (fun _ ↦ 2 * (n : ℝ) + Real.log 2) x) (bumpAlt n) :=
    (integrable_const _).add ((integrable_const _).indicator (measurableSet_bumpSet n))
  refine le_trans ?_ ((eintegral_eq_integral hint).symm.trans_le
    (eintegral_mono (le_log_bumpEVar hn)))
  rw [EReal.coe_le_coe_iff, integral_const_add_indicator_const _ _ (measurableSet_bumpSet n),
    smul_eq_mul]
  have hQA := inv_le_measureReal_bumpAlt_bumpSet hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 : (n : ℝ)⁻¹ * (2 * n + Real.log 2) = 2 + Real.log 2 / n := by
    field_simp
  have h2 : 0 ≤ Real.log 2 / n := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hQA (by positivity : (0 : ℝ) ≤ 2 * n + Real.log 2)]

private lemma tendsto_tvDist_bumpAlt :
    Tendsto (fun n ↦ tvDist (bumpAlt n) (volume : Measure I)) atTop (𝓝 0) :=
  tendsto_tvDist_one_sub_smul_add_smul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
    (.of_forall Nat.cast_inv_le_one)
    ((eventually_ge_atTop 1).mono fun _ hn ↦ cond_isProbabilityMeasure (volume_bumpSet_ne_zero hn))

private lemma bumpAlt_absolutelyContinuous (n : ℕ) : bumpAlt n ≪ volume :=
  (Measure.AbsolutelyContinuous.rfl.smul_left _).add_left
    (cond_absolutelyContinuous.smul_left _)

/-- **Without boundedness, the "only if" direction of Conjecture 6.8 fails** ([EVR26, Note 26,
Theorem 2 (1)]): for the Lebesgue measure on `[0, 1]`, there are probability measures `Q_n`
tending to it in total variation, so that the separation condition fails, and an exact
e-variable `X`, pivotal since the null is simple, with `E_{Q_n} log X ≥ 2 - log 2 > 0` for every
`n ≥ 1`. Every bounded exact e-variable `Y` with `E_{Q_n} log Y ≥ c` for every `n ≥ 1` has
`c ≤ 0`, so `X` is necessarily unbounded. -/
theorem exists_isExactEVar_le_eintegral_log_and_tendsto_tvDist :
    ∃ (X : I → ℝ≥0∞) (Q : ℕ → Measure I), IsExactEVar X {(volume : Measure I)} ∧
      IsPivotal X {(volume : Measure I)} ∧ (∀ n, IsProbabilityMeasure (Q n)) ∧
      (∀ n, 1 ≤ n → ((2 - Real.log 2 : ℝ) : EReal) ≤ ∫ᵉ x, ENNReal.log (X x) ∂(Q n)) ∧
      Tendsto (fun n ↦ tvDist (Q n) volume) atTop (𝓝 0) ∧
      ∀ (Y : I → ℝ≥0∞) (M c : ℝ), IsExactEVar Y {(volume : Measure I)} →
        (∀ᵐ x ∂(volume : Measure I), |(Y x).toReal - 1| ≤ M) →
        (∀ n, 1 ≤ n → (c : EReal) ≤ ∫ᵉ x, ENNReal.log (Y x) ∂(Q n)) → c ≤ 0 := by
  refine ⟨bumpEVar, bumpAlt, isExactEVar_bumpEVar, isPivotal_singleton _ _,
    isProbabilityMeasure_bumpAlt, fun n hn ↦ le_eintegral_log_bumpEVar hn,
    tendsto_tvDist_bumpAlt, fun Y M c hY hYM hc ↦ ?_⟩
  -- `c ≤ M ‖Q_n - P‖` for every `n ≥ 1`, and the right-hand side tends to `0`
  set 𝒬 : Set (Measure I) := {Q | ∃ m, 1 ≤ m ∧ bumpAlt m = Q}
  have hbound : ∀ n, 1 ≤ n → c ≤ M * tvDist (bumpAlt n) volume := by
    intro n hn
    have h := le_mul_tvDist_of_isExactEVar_of_le_eintegral_log (S := {(volume : Measure I)})
      (𝒬 := 𝒬) (fun P hP ↦ by rw [mem_singleton_iff.1 hP]; infer_instance)
      (by rintro _ ⟨m, -, rfl⟩; have := isProbabilityMeasure_bumpAlt m; infer_instance) hY
      (by
        rintro _ (hP | ⟨m, -, rfl⟩)
        · rw [mem_singleton_iff.1 hP]; exact hYM
        · exact (bumpAlt_absolutelyContinuous m).ae_le hYM)
      (by
        rintro _ ⟨m, -, rfl⟩
        filter_upwards [(bumpAlt_absolutelyContinuous m).ae_le
          (hY.ae_lt_top (mem_singleton _))] with x hx
        exact hx.ne)
      (by rintro _ ⟨m, hm, rfl⟩; exact hc m hm) (μ₁ := 0) (μ₂ := volume) (ν := bumpAlt n)
      (Submodule.zero_mem _) (Submodule.subset_span rfl) (subset_convexHull _ _ ⟨n, hn, rfl⟩)
    rwa [zero_add] at h
  have hlim : Tendsto (fun n ↦ M * tvDist (bumpAlt n) (volume : Measure I)) atTop (𝓝 0) := by
    simpa using tendsto_tvDist_bumpAlt.const_mul M
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨1, hbound⟩)

/-! ### Pointwise positivity -/

/-- The set `[0, 1 / 2]` of `[0, 1]`. -/
private noncomputable def lowHalf : Set I := Iic ⟨2⁻¹, by norm_num, by norm_num⟩

/-- The null `P`, uniform on `[0, 1 / 2]`. -/
private noncomputable def halfLow : Measure I := volume[|lowHalf]

/-- The alternative `Q_n = (1 - 1 / n) P + (1 / n) R`, with `R` uniform on `(1 / 2, 1]`. -/
private noncomputable def halfAlt (n : ℕ) : Measure I :=
  (1 - (n : ℝ≥0)⁻¹) • halfLow + (n : ℝ≥0)⁻¹ • volume[|lowHalfᶜ]

/-- The e-variable `X`, equal to `1` on `[0, 1 / 2]` and to `2` on `(1 / 2, 1]`. -/
private noncomputable def halfEVar (x : I) : ℝ≥0∞ :=
  1 + lowHalfᶜ.indicator 1 x

private lemma measurableSet_lowHalf : MeasurableSet lowHalf :=
  measurableSet_Iic

private lemma volume_lowHalf : volume lowHalf = ENNReal.ofReal 2⁻¹ :=
  unitInterval.volume_Iic _

private lemma volume_lowHalf_ne_zero : volume lowHalf ≠ 0 := by
  rw [volume_lowHalf]
  exact (ENNReal.ofReal_pos.2 (by norm_num)).ne'

private lemma volume_compl_lowHalf_ne_zero : volume lowHalfᶜ ≠ 0 := by
  rw [prob_compl_eq_one_sub measurableSet_lowHalf, volume_lowHalf]
  exact (tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 (by norm_num))).ne'

private instance isProbabilityMeasure_halfLow : IsProbabilityMeasure halfLow :=
  cond_isProbabilityMeasure volume_lowHalf_ne_zero

private instance isProbabilityMeasure_cond_compl_lowHalf :
    IsProbabilityMeasure ((volume : Measure I)[|lowHalfᶜ]) :=
  cond_isProbabilityMeasure volume_compl_lowHalf_ne_zero

private instance isProbabilityMeasure_halfAlt (n : ℕ) : IsProbabilityMeasure (halfAlt n) := by
  rw [halfAlt, ← Measure.coe_nnreal_smul, ← Measure.coe_nnreal_smul]
  exact TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul
    (by norm_cast; exact tsub_add_cancel_of_le (Nat.cast_inv_le_one n)) _ _

private lemma halfLow_compl : halfLow lowHalfᶜ = 0 := by
  rw [halfLow, cond_apply measurableSet_lowHalf, inter_compl_self, measure_empty, mul_zero]

/-- The alternative `Q_n` gives mass `1 / n` to `(1 / 2, 1]`. -/
private lemma measureReal_halfAlt_compl (n : ℕ) : (halfAlt n).real lowHalfᶜ = (n : ℝ)⁻¹ := by
  simp [measureReal_def, halfAlt, halfLow_compl,
    cond_apply_self volume_compl_lowHalf_ne_zero (measure_ne_top _ _)]

private lemma measurable_halfEVar : Measurable halfEVar :=
  (measurable_one.indicator measurableSet_lowHalf.compl).const_add 1

/-- `log X` is `log 2` on `(1 / 2, 1]` and `0` on `[0, 1 / 2]`. -/
private lemma log_halfEVar (x : I) :
    ENNReal.log (halfEVar x) = ((lowHalfᶜ.indicator (fun _ ↦ Real.log 2) x : ℝ) : EReal) := by
  by_cases hx : x ∈ lowHalfᶜ
  · rw [halfEVar, indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, one_add_one_eq_two,
      ← ENNReal.ofReal_ofNat 2, ENNReal.log_ofReal_of_pos (by norm_num)]
  · rw [halfEVar, indicator_of_notMem hx, indicator_of_notMem hx, add_zero, ENNReal.log_one,
      EReal.coe_zero]

/-- **With pointwise positivity, the separation is not necessary** ([EVR26, Note 26, Pointwise
positivity, first example]): for the uniform law `P` on `[0, 1 / 2]`, there are probability
measures `Q_n` tending to `P` in total variation, so that the separation condition fails, and an
exact e-variable `X ≤ 2`, pivotal since the null is simple, with `E_{Q_n} log X = (log 2) / n`,
positive for every `n ≥ 1`. -/
theorem exists_isExactEVar_eintegral_log_eq_and_tendsto_tvDist :
    ∃ (P : Measure I) (X : I → ℝ≥0∞) (Q : ℕ → Measure I), IsProbabilityMeasure P ∧
      IsExactEVar X {P} ∧ IsPivotal X {P} ∧ (∀ x, X x ≤ 2) ∧ (∀ n, IsProbabilityMeasure (Q n)) ∧
      (∀ n, ∫ᵉ x, ENNReal.log (X x) ∂(Q n) = ((Real.log 2 / n : ℝ) : EReal)) ∧
      Tendsto (fun n ↦ tvDist (Q n) P) atTop (𝓝 0) := by
  refine ⟨halfLow, halfEVar, halfAlt, inferInstance, ?_, isPivotal_singleton _ _, fun x ↦ ?_,
    fun n ↦ inferInstance, fun n ↦ ?_, ?_⟩
  · refine .of_lintegral_eq_one measurable_halfEVar fun P hP ↦ ?_
    unfold halfEVar
    rw [mem_singleton_iff.1 hP, lintegral_add_left measurable_const, lintegral_const,
      measure_univ, mul_one, lintegral_indicator_one measurableSet_lowHalf.compl, halfLow_compl,
      add_zero]
  · by_cases hx : x ∈ lowHalfᶜ <;> simp [halfEVar, hx, one_add_one_eq_two]
  · rw [eintegral_congr log_halfEVar,
      eintegral_eq_integral ((integrable_const _).indicator measurableSet_lowHalf.compl),
      integral_indicator_const _ measurableSet_lowHalf.compl, smul_eq_mul,
      measureReal_halfAlt_compl, inv_mul_eq_div]
  · exact tendsto_tvDist_one_sub_smul_add_smul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
      (.of_forall Nat.cast_inv_le_one) (.of_forall fun _ ↦ inferInstance)

end ProbabilityTheory
