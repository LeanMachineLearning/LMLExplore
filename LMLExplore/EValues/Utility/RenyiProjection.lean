/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Utility.Power
public import LMLExplore.MeasureTheory.Measure.AbsolutelyContinuousSet
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import LMLExplore.EValues.EVariable
import LMLExplore.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Statlib.EValues.NumeraireExistence

/-!
# The limit of the reverse Rényi projections

For `γ > 1`, let `Y γ` be a numeraire for the power utility `x ↦ x ^ (1 - γ) / (1 - γ)` among the
e-variables of a null `S`, under an alternative `Q`, and let `X` be the numeraire for the
logarithmic utility. The reverse Rényi projection of order `γ⁻¹` [LRR25, Theorem 6.1] is the
member of the effective null with density `Y γ ^ (-γ) / c γ` with respect to `Q`, where
`c γ = ∫⁻ Y γ ^ (1 - γ) ∂Q`
(`ProbabilityTheory.IsNumeraireFor.withDensity_rpow_neg_mem_effectiveSet`), and the reverse
information projection has density `X⁻¹` (`ProbabilityTheory.IsNumeraire.ripr_eq`). As `γ ↓ 1`,
the power utility shifted by the constant `(γ - 1)⁻¹` tends to the logarithm, and the optimal
objects follow when `Q` is absolutely continuous with respect to the null
[EVR26, Note 27, Theorem 1]:

* the ratio `Y γ / X` is close to `1` in the sense that `∫⁻ χ (Y γ / X) ∂Q` is at most
  `2 ∫⁻ |X ^ (1 - γ) - 1| ∂Q`, for the truncated Neyman χ² generator `χ`
  (`truncNeymanChi`), and the right-hand side tends to `0`;
* hence `Y γ / X → 1` and `Y γ → X` in `Q`-measure, and `c γ → Q univ`;
* the densities `Y γ ^ (-γ) / c γ` of the reverse Rényi projections converge in `Q`-measure to
  `X⁻¹ / Q univ`, the density of the reverse information projection when `Q` is a probability
  measure.

This answers in the affirmative, for convergence in probability of the densities, the conjecture
of Lardy, Grünwald and Harremoës that the reverse Rényi projections converge to the reverse
information projection [LGH24, §V].

## Main definitions

* `ProbabilityTheory.truncNeymanChi`: the function `χ`, equal to `(z - 1) ^ 2 / z` for `z ≥ 1 / 3`
  and to `z + 1` below.

## Main statements

* `ProbabilityTheory.tendsto_lintegral_abs_rpow_sub_one`: for an almost everywhere finite `X`
  with `∫⁻ X⁻¹ < ∞`, `∫⁻ |X ^ (1 - γ) - 1| → 0` as `γ ↓ 1`.
* `ProbabilityTheory.IsNumeraireFor.lintegral_truncNeymanChi_div_le`: the bound
  `∫⁻ χ (Y γ / X) ∂Q ≤ 2 ∫⁻ |X ^ (1 - γ) - 1| ∂Q`.
* `ProbabilityTheory.IsNumeraire.tendstoInMeasure_div_of_powerUtility`,
  `ProbabilityTheory.IsNumeraire.tendstoInMeasure_of_powerUtility`: `Y γ / X → 1` and `Y γ → X` in
  `Q`-measure.
* `ProbabilityTheory.tendsto_lintegral_rpow_one_sub_of_powerUtility`: `c γ → Q univ`.
* `ProbabilityTheory.IsNumeraire.tendstoInMeasure_rpow_neg_of_powerUtility`: the densities of the
  reverse Rényi projections converge in `Q`-measure to `X⁻¹ / Q univ`.

## Implementation notes

The bound comes from three inequalities, with `Z = Y γ / X`: `∫⁻ Z ∂Q ≤ Q univ` (the numeraire
property of `X`, applied to `Y γ`), and `∫⁻ Y γ ^ (-γ) * X ∂Q ≤ c γ < ∞` (the first-order condition
of `Y γ`, applied to `X`). They are combined through the pointwise inequality
`χ (y / x) + 1 + y ^ (1 - γ) ≤ y / x + y ^ (-γ) x + 2 |x ^ (1 - γ) - 1|` on `[0, ∞]` with `y ≠ 0`.
The convergence of the densities is then pointwise along almost everywhere convergent
subsequences. The proofs are adapted from the Lean file `Results/RenyiChoquet.lean` of
`EValuesResearch` [EVR26], where the three inequalities are hypotheses; here they are derived from
the numeraire properties.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 27, and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026.
* [LGH24] T. Lardy, P. Grünwald, P. Harremoës, *Reverse information projections and optimal
  e-statistics*, IEEE Trans. Inform. Theory 70 (2024), arXiv:2306.16646.
* [LRR25] M. Larsson, A. Ramdas, J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The truncated Neyman χ² generator -/

/-- The truncated generator of Neyman's χ² divergence: `(z - 1) ^ 2 / z` for `z ≥ 1 / 3`, and
`z + 1` for `z < 1 / 3`. On `[0, ∞)` it is nonnegative, vanishes only at `1`
(`truncNeymanChi_eq_zero_iff`) and is bounded below away from `1` (`le_truncNeymanChi`): its
expectation controls the distance in probability of a nonnegative variable to `1`. -/
noncomputable def truncNeymanChi (z : ℝ) : ℝ :=
  if z < 3⁻¹ then z + 1 else (z - 1) ^ 2 / z

/-- The function `χ` is measurable. -/
@[fun_prop]
lemma measurable_truncNeymanChi : Measurable truncNeymanChi :=
  Measurable.ite (p := fun z : ℝ ↦ z < 3⁻¹) measurableSet_Iio (by fun_prop) (by fun_prop)

/-- The function `χ` is nonnegative on `[0, ∞)`. -/
lemma truncNeymanChi_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ truncNeymanChi z := by
  unfold truncNeymanChi
  split_ifs
  · linarith
  · positivity

/-- Away from `1`, the function `χ` is bounded below: if `z ≥ 0` and `|z - 1| ≥ e > 0`, then
`χ z ≥ e ^ 2 / (1 + e)`. -/
lemma le_truncNeymanChi {z e : ℝ} (hz : 0 ≤ z) (he : 0 < e) (hze : e ≤ |z - 1|) :
    e ^ 2 / (1 + e) ≤ truncNeymanChi z := by
  unfold truncNeymanChi
  split_ifs with h
  · rw [abs_of_nonpos (by linarith)] at hze
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · replace h := not_lt.mp h
    have hz' : 0 < z := lt_of_lt_of_le (by norm_num) h
    rw [div_le_div_iff₀ (by positivity) hz']
    rcases le_total z 1 with h1 | h1
    · rw [abs_of_nonpos (by linarith)] at hze
      have : e ^ 2 ≤ (z - 1) ^ 2 := by nlinarith
      nlinarith
    · rw [abs_of_nonneg (by linarith)] at hze
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ z - 1) he.le)
        (sub_nonneg.2 hze)]

@[simp]
lemma truncNeymanChi_one : truncNeymanChi 1 = 0 := by
  norm_num [truncNeymanChi]

/-- On `[0, ∞)`, the function `χ` vanishes exactly at `1`. -/
lemma truncNeymanChi_eq_zero_iff {z : ℝ} (hz : 0 ≤ z) : truncNeymanChi z = 0 ↔ z = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ truncNeymanChi_one⟩
  by_contra hz1
  have he : 0 < |z - 1| := abs_pos.2 (sub_ne_zero.2 hz1)
  have := le_truncNeymanChi hz he le_rfl
  rw [h] at this
  exact absurd this (not_le.2 (by positivity))

/-- On `(0, ∞)`, `χ z = (z - 1) + min (1 / z - 1) 2`. -/
private lemma truncNeymanChi_eq_of_pos {z : ℝ} (hz : 0 < z) :
    truncNeymanChi z = z - 1 + min (1 / z - 1) 2 := by
  unfold truncNeymanChi
  split_ifs with h
  · have : 3 < 1 / z := by rw [lt_div_iff₀ hz]; linarith [inv_mul_cancel₀ (three_ne_zero (α := ℝ))]
    rw [min_eq_right (by linarith)]
    ring
  · replace h := not_lt.mp h
    have : 1 / z ≤ 3 := by
      rw [div_le_iff₀ hz]
      linarith [inv_mul_cancel₀ (three_ne_zero (α := ℝ))]
    rw [min_eq_left (by linarith)]
    field_simp
    ring

/-- For `z > 0` and `γ ≥ 1`, `1 / z - 1 ≤ z ^ (-γ) * (1 - z)`. -/
private lemma one_div_sub_one_le_rpow_neg_mul {z γ : ℝ} (hz : 0 < z) (hγ : 1 ≤ γ) :
    1 / z - 1 ≤ z ^ (-γ) * (1 - z) := by
  have h1 : 1 / z - 1 = z ^ (-1 : ℝ) * (1 - z) := by
    rw [Real.rpow_neg_one]
    field_simp
  rw [h1]
  rcases le_total z 1 with h | h
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hz h (by linarith)) (by linarith)
  · exact mul_le_mul_of_nonpos_right
      (Real.rpow_le_rpow_of_exponent_le h (by linarith)) (by linarith)

/-- The pointwise inequality behind the bound, for real `x, y > 0` and `γ ≥ 1`:
`χ (y / x) + 1 + y ^ (1 - γ) ≤ y / x + y ^ (-γ) x + 2 |x ^ (1 - γ) - 1|`. -/
private lemma truncNeymanChi_add_le_real {x y γ : ℝ} (hx : 0 < x) (hy : 0 < y) (hγ : 1 ≤ γ) :
    truncNeymanChi (y / x) + 1 + y ^ (1 - γ)
      ≤ y / x + y ^ (-γ) * x + 2 * |x ^ (1 - γ) - 1| := by
  set z := y / x with hz_def
  have hz : 0 < z := div_pos hy hx
  set v := x ^ (1 - γ) with hv_def
  have hv : 0 < v := Real.rpow_pos_of_pos hx _
  set t := z ^ (-γ) with ht_def
  have hyz : y = z * x := by rw [hz_def]; field_simp
  have h1 : y ^ (1 - γ) = v * (z * t) := by
    rw [hyz, Real.mul_rpow hz.le hx.le, ht_def, hv_def, sub_eq_add_neg, Real.rpow_add hz,
      Real.rpow_one]
    ring
  have h2 : y ^ (-γ) * x = v * t := by
    rw [hyz, Real.mul_rpow hz.le hx.le, ht_def, hv_def, mul_assoc, ← Real.rpow_add_one hx.ne']
    ring_nf
  rw [h1, h2, truncNeymanChi_eq_of_pos hz]
  set m := min (1 / z - 1) 2
  have hm1 : m ≤ t * (1 - z) := (min_le_left _ _).trans (one_div_sub_one_le_rpow_neg_mul hz hγ)
  have hm2 : -1 ≤ m := le_min (by have := one_div_pos.2 hz; linarith) (by norm_num)
  have hm3 : m ≤ 2 := min_le_right _ _
  have hvm : v * m ≤ v * (t * (1 - z)) := mul_le_mul_of_nonneg_left hm1 hv.le
  have hrest : (1 - v) * m ≤ 2 * |v - 1| := by
    rcases le_total v 1 with h | h
    · rw [abs_of_nonpos (by linarith)]
      nlinarith
    · rw [abs_of_nonneg (by linarith)]
      nlinarith
  nlinarith

/-- The pointwise inequality behind the bound in `ℝ≥0∞`, for `y ≠ 0` and `γ > 1`:
`χ (y / x) + 1 + y ^ (1 - γ) ≤ y / x + y ^ (-γ) x + 2 |x ^ (1 - γ) - 1|`. -/
private lemma truncNeymanChi_add_le {x y : ℝ≥0∞} (hy : y ≠ 0) {γ : ℝ} (hγ : 1 < γ) :
    ENNReal.ofReal (truncNeymanChi (y / x).toReal) + 1 + y ^ (1 - γ)
      ≤ y / x + y ^ (-γ) * x + 2 * ENNReal.ofReal |x.toReal ^ (1 - γ) - 1| := by
  have hγ0 : 1 - γ < 0 := by linarith
  have hγ1 : -γ < 0 := by linarith
  by_cases hx0 : x = 0
  · simp [hx0, ENNReal.div_zero hy]
  by_cases hxt : x = ∞
  · subst hxt
    by_cases hyt : y = ∞
    · subst hyt
      simp only [ENNReal.div_top, ENNReal.toReal_zero, ENNReal.toReal_top,
        ENNReal.top_rpow_of_neg hγ0, ENNReal.top_rpow_of_neg hγ1, zero_mul,
        Real.zero_rpow hγ0.ne]
      norm_num [truncNeymanChi]
    · have : y ^ (-γ) ≠ 0 := by simp [ENNReal.rpow_eq_zero_iff, hy, hyt]
      simp [ENNReal.mul_top this]
  by_cases hyt : y = ∞
  · subst hyt
    simp [ENNReal.top_div_of_ne_top hxt]
  have hx' : 0 < x.toReal := ENNReal.toReal_pos hx0 hxt
  have hy' : 0 < y.toReal := ENNReal.toReal_pos hy hyt
  have key := truncNeymanChi_add_le_real hx' hy' hγ.le
  have hX : x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hxt).symm
  have hY : y = ENNReal.ofReal y.toReal := (ENNReal.ofReal_toReal hyt).symm
  have hdiv : y / x = ENNReal.ofReal (y.toReal / x.toReal) := by
    rw [ENNReal.ofReal_div_of_pos hx', ← hX, ← hY]
  have hdiv' : (y / x).toReal = y.toReal / x.toReal := ENNReal.toReal_div _ _
  have hp1 : y ^ (1 - γ) = ENNReal.ofReal (y.toReal ^ (1 - γ)) := by
    rw [← ENNReal.ofReal_rpow_of_pos hy', ← hY]
  have hp2 : y ^ (-γ) * x = ENNReal.ofReal (y.toReal ^ (-γ) * x.toReal) := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hy'.le _), ← ENNReal.ofReal_rpow_of_pos hy', ← hX,
      ← hY]
  rw [hdiv', hp1, hp2, hdiv]
  have hc := truncNeymanChi_nonneg (div_pos hy' hx').le
  have h1 : 0 ≤ y.toReal ^ (-γ) * x.toReal := mul_nonneg (Real.rpow_nonneg hy'.le _) hx'.le
  calc ENNReal.ofReal (truncNeymanChi (y.toReal / x.toReal)) + 1
        + ENNReal.ofReal (y.toReal ^ (1 - γ))
  _ = ENNReal.ofReal (truncNeymanChi (y.toReal / x.toReal) + 1 + y.toReal ^ (1 - γ)) := by
    rw [ENNReal.ofReal_add (add_nonneg hc zero_le_one) (Real.rpow_nonneg hy'.le _),
      ENNReal.ofReal_add hc zero_le_one, ENNReal.ofReal_one]
  _ ≤ ENNReal.ofReal (y.toReal / x.toReal + y.toReal ^ (-γ) * x.toReal
        + 2 * |x.toReal ^ (1 - γ) - 1|) := ENNReal.ofReal_le_ofReal key
  _ = _ := by
    rw [ENNReal.ofReal_add (add_nonneg (by positivity) h1) (by positivity),
      ENNReal.ofReal_add (by positivity) h1,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

/-! ### The moment `∫⁻ |X ^ (1 - γ) - 1|` -/

/-- For `x > 0` and `γ ∈ [1, 2]`, `x ^ (1 - γ) ≤ 1 + x⁻¹`. -/
private lemma rpow_one_sub_le_one_add_inv {x γ : ℝ} (hx : 0 < x) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 2) :
    x ^ (1 - γ) ≤ 1 + x⁻¹ := by
  rcases le_total 1 x with h | h
  · have := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith : 1 - γ ≤ 0)
    have : 0 ≤ x⁻¹ := by positivity
    linarith
  · have h' : x ^ (1 - γ) ≤ x ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hx h (by linarith)
    rw [Real.rpow_neg_one] at h'
    linarith

/-- If `X` is almost everywhere finite and `∫⁻ X⁻¹ ∂Q < ∞`, then `∫⁻ |X ^ (1 - γ) - 1| ∂Q → 0`
as `γ ↓ 1`, by dominated convergence with the bound `X⁻¹ + 2` for `γ ≤ 2`. -/
theorem tendsto_lintegral_abs_rpow_sub_one {Q : Measure Ω} [IsFiniteMeasure Q] {X : Ω → ℝ≥0∞}
    (hX : AEMeasurable X Q) (hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞) (hX_inv : ∫⁻ ω, (X ω)⁻¹ ∂Q ≠ ∞) :
    Tendsto (fun γ : ℝ ↦ ∫⁻ ω, ENNReal.ofReal |(X ω).toReal ^ (1 - γ) - 1| ∂Q) (𝓝[>] 1)
      (𝓝 0) := by
  have hX0 : ∀ᵐ ω ∂Q, X ω ≠ 0 := by
    filter_upwards [ae_lt_top' hX.inv hX_inv] with ω hω h0
    simp [h0] at hω
  rw [← lintegral_zero (μ := Q)]
  refine tendsto_lintegral_filter_of_dominated_convergence' (l := 𝓝[>] (1 : ℝ))
    (F := fun γ ω ↦ ENNReal.ofReal |(X ω).toReal ^ (1 - γ) - 1|) (fun ω ↦ (X ω)⁻¹ + 2)
    (Eventually.of_forall fun γ ↦ by fun_prop) ?_ ?_ ?_
  · have h2 : ∀ᶠ γ in 𝓝[>] (1 : ℝ), γ < 2 :=
      nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num))
    filter_upwards [h2, self_mem_nhdsWithin] with γ hγ2 hγ1
    filter_upwards [hX0, hX_top] with ω h0 htop
    have ha : 0 < (X ω).toReal := ENNReal.toReal_pos h0 htop
    have hu := rpow_one_sub_le_one_add_inv ha (le_of_lt hγ1) hγ2.le
    have hu0 : 0 ≤ (X ω).toReal ^ (1 - γ) := Real.rpow_nonneg ha.le _
    calc ENNReal.ofReal |(X ω).toReal ^ (1 - γ) - 1|
    _ ≤ ENNReal.ofReal ((X ω).toReal⁻¹ + 2) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [abs_le]
      constructor <;> linarith
    _ = (X ω)⁻¹ + 2 := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_inv_of_pos ha,
        ENNReal.ofReal_toReal htop, ENNReal.ofReal_ofNat]
  · rw [lintegral_add_right' _ aemeasurable_const]
    simp [hX_inv, ENNReal.mul_eq_top]
  · filter_upwards [hX0, hX_top] with ω h0 htop
    have ha : 0 < (X ω).toReal := ENNReal.toReal_pos h0 htop
    have h1 : Tendsto (fun γ : ℝ ↦ (X ω).toReal ^ (1 - γ)) (𝓝 1)
        (𝓝 ((X ω).toReal ^ (1 - 1 : ℝ))) :=
      (Real.continuousAt_const_rpow ha.ne').tendsto.comp
        ((continuous_const.sub continuous_id).tendsto 1)
    rw [sub_self, Real.rpow_zero] at h1
    have h2 := ENNReal.tendsto_ofReal ((h1.sub_const 1).abs)
    rw [sub_self, abs_zero, ENNReal.ofReal_zero] at h2
    exact h2.mono_left nhdsWithin_le_nhds

/-- The pointwise bound behind `c γ → Q univ`: for `x ∈ (0, ∞)`, `K ≠ 0` and `γ ≥ 1`,
`K ^ (1 - γ) ≤ y ^ (1 - γ) + K ^ (1 - γ) |x ^ (1 - γ) - 1| + K ^ (1 - γ) 1{K ≤ y / x}`. -/
private lemma rpow_le_rpow_add_mul_add_mul_indicator {x y K : ℝ≥0∞} (hx0 : x ≠ 0)
    (hxt : x ≠ ∞) (hK0 : K ≠ 0) {γ : ℝ} (hγ : 1 ≤ γ) :
    K ^ (1 - γ) ≤ y ^ (1 - γ) + K ^ (1 - γ) * ENNReal.ofReal |x.toReal ^ (1 - γ) - 1|
      + K ^ (1 - γ) * {z : ℝ≥0∞ | K ≤ z}.indicator 1 (y / x) := by
  by_cases h : K ≤ y / x
  · rw [Set.indicator_of_mem (by exact h), Pi.one_apply, mul_one]
    exact le_add_self
  rw [Set.indicator_of_notMem (by exact h), mul_zero, add_zero]
  have hyK : y ≤ K * x := calc
    y = y / x * x := (ENNReal.div_mul_cancel hx0 hxt).symm
    _ ≤ K * x := mul_le_mul_left (not_le.mp h).le x
  have hpow : (K * x) ^ (1 - γ) ≤ y ^ (1 - γ) := by
    rw [show 1 - γ = -(γ - 1) by ring, ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hyK (by linarith))
  rw [ENNReal.mul_rpow_of_ne_zero hK0 hx0] at hpow
  have hx' : 0 < x.toReal := ENNReal.toReal_pos hx0 hxt
  have h1 : 1 ≤ x ^ (1 - γ) + ENNReal.ofReal |x.toReal ^ (1 - γ) - 1| := by
    rw [← ENNReal.ofReal_toReal hxt, ENNReal.ofReal_rpow_of_pos hx', ENNReal.toReal_ofReal hx'.le,
      ← ENNReal.ofReal_add (Real.rpow_nonneg hx'.le _) (abs_nonneg _), ← ENNReal.ofReal_one]
    have h2 := neg_abs_le (x.toReal ^ (1 - γ) - 1)
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc K ^ (1 - γ)
  _ = K ^ (1 - γ) * 1 := (mul_one _).symm
  _ ≤ K ^ (1 - γ) * (x ^ (1 - γ) + ENNReal.ofReal |x.toReal ^ (1 - γ) - 1|) := by gcongr
  _ = K ^ (1 - γ) * x ^ (1 - γ) + K ^ (1 - γ) * ENNReal.ofReal |x.toReal ^ (1 - γ) - 1| :=
    mul_add _ _ _
  _ ≤ _ := by gcongr

/-- The lower bound behind `c γ → Q univ`: if `X` is almost everywhere positive and finite and
`∫⁻ Y / X ∂Q ≤ Q univ`, then for `K ∈ (0, ∞)` and `γ ≥ 1`, Markov's inequality gives
`K ^ (1 - γ) * Q univ - K ^ (1 - γ) * (∫⁻ |X ^ (1 - γ) - 1| ∂Q + Q univ / K)` as a lower bound
for `∫⁻ Y ^ (1 - γ) ∂Q`. -/
private lemma rpow_mul_sub_le_lintegral_rpow {Q : Measure Ω} {X Y : Ω → ℝ≥0∞}
    (hX : Measurable X) (hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞) (hX0 : ∀ᵐ ω ∂Q, X ω ≠ 0)
    (hY : Measurable Y) (h_num : ∫⁻ ω, Y ω / X ω ∂Q ≤ Q univ) {K : ℝ≥0∞} (hK0 : K ≠ 0)
    (hKt : K ≠ ∞) {γ : ℝ} (hγ : 1 ≤ γ) :
    K ^ (1 - γ) * Q univ - K ^ (1 - γ) * (∫⁻ ω, ENNReal.ofReal |(X ω).toReal ^ (1 - γ) - 1| ∂Q
      + Q univ / K) ≤ ∫⁻ ω, Y ω ^ (1 - γ) ∂Q := by
  have hKγ : K ^ (1 - γ) ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero hK0 hKt
  have hmarkov : Q {ω | K ≤ Y ω / X ω} ≤ Q univ / K :=
    (meas_ge_le_lintegral_div (by fun_prop) hK0 hKt).trans (by gcongr)
  rw [tsub_le_iff_right]
  calc K ^ (1 - γ) * Q univ
  _ = ∫⁻ _, K ^ (1 - γ) ∂Q := by rw [lintegral_const]
  _ ≤ ∫⁻ ω, (Y ω ^ (1 - γ) + K ^ (1 - γ) * ENNReal.ofReal |(X ω).toReal ^ (1 - γ) - 1|
        + K ^ (1 - γ) * {ω | K ≤ Y ω / X ω}.indicator 1 ω) ∂Q :=
    lintegral_mono_ae (by
      filter_upwards [hX0, hX_top] with ω h0 ht
      exact rpow_le_rpow_add_mul_add_mul_indicator h0 ht hK0 hγ)
  _ = ∫⁻ ω, Y ω ^ (1 - γ) ∂Q
        + K ^ (1 - γ) * ∫⁻ ω, ENNReal.ofReal |(X ω).toReal ^ (1 - γ) - 1| ∂Q
        + K ^ (1 - γ) * ∫⁻ ω, {ω | K ≤ Y ω / X ω}.indicator 1 ω ∂Q := by
    rw [lintegral_add_left' (by fun_prop), lintegral_add_left' (by fun_prop),
      lintegral_const_mul' _ _ hKγ, lintegral_const_mul' _ _ hKγ]
  _ ≤ ∫⁻ ω, Y ω ^ (1 - γ) ∂Q
        + K ^ (1 - γ) * (∫⁻ ω, ENNReal.ofReal |(X ω).toReal ^ (1 - γ) - 1| ∂Q + Q univ / K) := by
    rw [add_assoc, ← mul_add]
    gcongr
    exact (lintegral_indicator_one_le _).trans hmarkov

/-! ### The optimal e-variables of the power utilities and the numeraire -/

variable {Q : Measure Ω} {S : Set (Measure Ω)} {X : Ω → ℝ≥0∞}

/-- **The χ bound** [EVR26, Note 27, Theorem 1]: for a numeraire `Y` for the power utility of
risk aversion `γ > 1` and the numeraire `X` for the logarithmic utility, among the e-variables of
a null of masses at most `1` under a finite measure `Q`,
`∫⁻ χ (Y / X) ∂Q ≤ 2 ∫⁻ |X ^ (1 - γ) - 1| ∂Q`. -/
theorem IsNumeraireFor.lintegral_truncNeymanChi_div_le [IsFiniteMeasure Q] {γ : ℝ} {hγ : 1 < γ}
    {Y : Ω → ℝ≥0∞} (hS : ∀ P ∈ S, P univ ≤ 1)
    (hY : IsNumeraireFor (powerUtility γ hγ) Y {Z | IsEVar Z S} Q) (hX : IsNumeraire X S Q) :
    ∫⁻ ω, ENNReal.ofReal (truncNeymanChi (Y ω / X ω).toReal) ∂Q
      ≤ 2 * ∫⁻ ω, ENNReal.ofReal |(X ω).toReal ^ (1 - γ) - 1| ∂Q := by
  have hXm := hX.measurable
  have hYm : Measurable Y := hY.mem.measurable
  -- the numeraire property of `X` applied to `Y`, and the first-order condition of `Y` at `X`
  have h_num : ∫⁻ ω, Y ω / X ω ∂Q ≤ Q univ := hX.lintegral_div_le_measure_univ hY.mem
  have h_foc : ∫⁻ ω, Y ω ^ (-γ) * X ω ∂Q ≤ ∫⁻ ω, Y ω ^ (1 - γ) ∂Q :=
    hY.lintegral_rpow_neg_mul_le hS hX.isEVar
  have h_fin : ∫⁻ ω, Y ω ^ (1 - γ) ∂Q ≠ ∞ :=
    ((hY.lintegral_rpow_le_measure_univ hS).trans_lt (measure_lt_top Q univ)).ne
  have hpt : ∀ᵐ ω ∂Q, ENNReal.ofReal (truncNeymanChi (Y ω / X ω).toReal) + 1 + Y ω ^ (1 - γ)
      ≤ Y ω / X ω + Y ω ^ (-γ) * X ω + 2 * ENNReal.ofReal |(X ω).toReal ^ (1 - γ) - 1| := by
    filter_upwards [hY.ae_ne_zero_powerUtility hS] with ω hω using truncNeymanChi_add_le hω hγ
  set A := ∫⁻ ω, ENNReal.ofReal (truncNeymanChi (Y ω / X ω).toReal) ∂Q
  set B := ∫⁻ ω, ENNReal.ofReal |(X ω).toReal ^ (1 - γ) - 1| ∂Q
  set c := ∫⁻ ω, Y ω ^ (1 - γ) ∂Q
  -- integrate the pointwise inequality and cancel `Q univ + c`
  have key : A + (Q univ + c) ≤ 2 * B + (Q univ + c) := calc
    A + (Q univ + c)
    _ = A + ∫⁻ _, 1 ∂Q + c := by rw [lintegral_one, add_assoc]
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (truncNeymanChi (Y ω / X ω).toReal) + 1) ∂Q + c :=
      add_le_add_left (le_lintegral_add _ _) _
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (truncNeymanChi (Y ω / X ω).toReal) + 1 + Y ω ^ (1 - γ)) ∂Q :=
      le_lintegral_add _ _
    _ ≤ ∫⁻ ω, (Y ω / X ω + Y ω ^ (-γ) * X ω
          + 2 * ENNReal.ofReal |(X ω).toReal ^ (1 - γ) - 1|) ∂Q := lintegral_mono_ae hpt
    _ = ∫⁻ ω, Y ω / X ω ∂Q + ∫⁻ ω, Y ω ^ (-γ) * X ω ∂Q + 2 * B := by
      rw [lintegral_add_left' (by fun_prop), lintegral_add_left' (by fun_prop),
        lintegral_const_mul' _ _ (by simp)]
    _ ≤ Q univ + c + 2 * B := add_le_add_left (add_le_add h_num h_foc) _
    _ = 2 * B + (Q univ + c) := add_comm _ _
  exact ENNReal.le_of_add_le_add_right (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, h_fin⟩) key

variable {Y : ℝ → Ω → ℝ≥0∞}

/-- **The optimal e-variables of the power utilities converge to the numeraire, in ratio**
[EVR26, Note 27, Theorem 1 (1)]: if `Q` is a finite measure absolutely continuous with respect
to a null of masses at most `1`, `X` is the numeraire and `Y γ` is a numeraire for the power
utility of risk aversion `γ` for every `γ > 1`, then `Y γ / X → 1` in `Q`-measure as `γ ↓ 1`. -/
theorem IsNumeraire.tendstoInMeasure_div_of_powerUtility [IsFiniteMeasure Q]
    (hS : ∀ P ∈ S, P univ ≤ 1) (hQS : Q.AbsolutelyContinuousSet S) (hX : IsNumeraire X S Q)
    (hY : ∀ γ (hγ : 1 < γ), IsNumeraireFor (powerUtility γ hγ) (Y γ) {Z | IsEVar Z S} Q) :
    TendstoInMeasure Q (fun γ ω ↦ (Y γ ω / X ω).toReal) (𝓝[>] 1) (fun _ ↦ 1) := by
  have hX_inv : ∫⁻ ω, (X ω)⁻¹ ∂Q ≠ ∞ :=
    ((hX.lintegral_inv_le_measure_fsupport hS).trans_lt (measure_lt_top _ _)).ne
  refine tendstoInMeasure_of_ne_top fun ε hε hεt ↦ ?_
  set e := ε.toReal
  have he : 0 < e := ENNReal.toReal_pos hε.ne' hεt
  set δ : ℝ≥0∞ := ENNReal.ofReal (e ^ 2 / (1 + e))
  have hδ : δ ≠ 0 := by
    simp only [δ, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  -- a deviation of `Y γ / X` from `1` by at least `ε` makes `χ (Y γ / X)` at least `δ`
  have hsub : ∀ γ, {ω | ε ≤ edist ((Y γ ω / X ω).toReal) 1}
      ⊆ {ω | δ ≤ ENNReal.ofReal (truncNeymanChi (Y γ ω / X ω).toReal)} := by
    intro γ ω hω
    simp only [mem_ofPred_eq, edist_dist, Real.dist_eq] at hω ⊢
    rw [← ENNReal.ofReal_toReal hεt, ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)] at hω
    exact ENNReal.ofReal_le_ofReal (le_truncNeymanChi ENNReal.toReal_nonneg he hω)
  have hupper : Tendsto
      (fun γ : ℝ ↦ 2 * (∫⁻ ω, ENNReal.ofReal |(X ω).toReal ^ (1 - γ) - 1| ∂Q) / δ) (𝓝[>] 1)
      (𝓝 0) := by
    have := ENNReal.Tendsto.div_const (ENNReal.Tendsto.const_mul
      (tendsto_lintegral_abs_rpow_sub_one hX.measurable.aemeasurable (hQS.ae_ne_top hX.isEVar)
        hX_inv) (Or.inr (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ∞))) (Or.inr hδ)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with γ hγ
  have hYm : Measurable (Y γ) := (hY γ hγ).mem.measurable
  have hXm := hX.measurable
  calc Q {ω | ε ≤ edist ((Y γ ω / X ω).toReal) 1}
  _ ≤ Q {ω | δ ≤ ENNReal.ofReal (truncNeymanChi (Y γ ω / X ω).toReal)} := measure_mono (hsub γ)
  _ ≤ (∫⁻ ω, ENNReal.ofReal (truncNeymanChi (Y γ ω / X ω).toReal) ∂Q) / δ :=
    meas_ge_le_lintegral_div (by fun_prop) hδ ENNReal.ofReal_ne_top
  _ ≤ 2 * (∫⁻ ω, ENNReal.ofReal |(X ω).toReal ^ (1 - γ) - 1| ∂Q) / δ := by
    gcongr
    exact (hY γ hγ).lintegral_truncNeymanChi_div_le hS hX

/-- **The optimal e-variables of the power utilities converge to the numeraire**
[EVR26, Note 27, Theorem 1 (1)]: if `Q` is a finite measure absolutely continuous with respect
to a null of masses at most `1`, `X` is the numeraire and `Y γ` is a numeraire for the power
utility of risk aversion `γ` for every `γ > 1`, then `Y γ → X` in `Q`-measure as `γ ↓ 1`. -/
theorem IsNumeraire.tendstoInMeasure_of_powerUtility [IsFiniteMeasure Q]
    (hS : ∀ P ∈ S, P univ ≤ 1) (hQS : Q.AbsolutelyContinuousSet S) (hX : IsNumeraire X S Q)
    (hY : ∀ γ (hγ : 1 < γ), IsNumeraireFor (powerUtility γ hγ) (Y γ) {Z | IsEVar Z S} Q) :
    TendstoInMeasure Q (fun γ ω ↦ (Y γ ω).toReal) (𝓝[>] 1) (fun ω ↦ (X ω).toReal) := by
  refine tendstoInMeasure_of_forall_seq_exists_subseq_tendsto_ae ?_ fun u hu ↦ ?_
  · filter_upwards [self_mem_nhdsWithin] with γ hγ
    exact (hY γ hγ).mem.measurable.ennreal_toReal.aestronglyMeasurable
  -- along a subsequence, `Y γ / X → 1` almost everywhere, and `Y γ = (Y γ / X) * X`
  obtain ⟨ns, hns, h_ae⟩ :=
    ((hX.tendstoInMeasure_div_of_powerUtility hS hQS hY).comp hu).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  have hu' : ∀ᶠ n in atTop, 1 < u (ns n) :=
    (hu.comp hns.tendsto_atTop).eventually self_mem_nhdsWithin
  have hY_top : ∀ᵐ ω ∂Q, ∀ n, 1 < u n → Y (u n) ω ≠ ∞ := ae_all_iff.2 fun n ↦ by
    by_cases h : 1 < u n
    · filter_upwards [hQS.ae_ne_top (hY _ h).mem] with ω hω _ using hω
    · exact Eventually.of_forall fun _ h' ↦ absurd h' h
  filter_upwards [h_ae, hY_top, hQS.ae_ne_top hX.isEVar, hX.ae_ne_zero hS]
    with ω hω hYt hXt hX0
  have h_eq : ∀ᶠ n in atTop,
      (Y (u (ns n)) ω / X ω).toReal * (X ω).toReal = (Y (u (ns n)) ω).toReal := by
    filter_upwards [hu'] with n hn
    rw [← ENNReal.toReal_mul, ENNReal.div_mul_cancel hX0 hXt]
  simpa using (hω.mul_const (X ω).toReal).congr' h_eq

/-- **The normalizing constants of the reverse Rényi projections converge**
[EVR26, Note 27, Theorem 1 (1)]: if `Q` is a finite measure absolutely continuous with respect
to a null of masses at most `1` and `Y γ` is a numeraire for the power utility of risk aversion
`γ` for every `γ > 1`, then `∫⁻ Y γ ^ (1 - γ) ∂Q → Q univ` as `γ ↓ 1`. -/
theorem tendsto_lintegral_rpow_one_sub_of_powerUtility [IsFiniteMeasure Q]
    (hS : ∀ P ∈ S, P univ ≤ 1) (hQS : Q.AbsolutelyContinuousSet S)
    (hY : ∀ γ (hγ : 1 < γ), IsNumeraireFor (powerUtility γ hγ) (Y γ) {Z | IsEVar Z S} Q) :
    Tendsto (fun γ ↦ ∫⁻ ω, Y γ ω ^ (1 - γ) ∂Q) (𝓝[>] 1) (𝓝 (Q univ)) := by
  -- compare with Statlib's numeraire `X` for the logarithmic utility
  set X := numeraire Q S
  have hX : IsNumeraire X S Q := isNumeraire_numeraire Q hS
  have hXm := hX.measurable
  have hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞ := hQS.ae_ne_top hX.isEVar
  have hX0 : ∀ᵐ ω ∂Q, X ω ≠ 0 := hX.ae_ne_zero hS
  set M := Q univ
  have hM : M ≠ ∞ := measure_ne_top Q univ
  set ε : ℝ → ℝ≥0∞ := fun γ ↦ ∫⁻ ω, ENNReal.ofReal |(X ω).toReal ^ (1 - γ) - 1| ∂Q
  have hε : Tendsto ε (𝓝[>] 1) (𝓝 0) := tendsto_lintegral_abs_rpow_sub_one hXm.aemeasurable hX_top
    ((hX.lintegral_inv_le_measure_fsupport hS).trans_lt (measure_lt_top _ _)).ne
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  swap
  · filter_upwards [self_mem_nhdsWithin] with γ hγ
    exact ((hY γ hγ).lintegral_rpow_le_measure_univ hS).trans_lt hb
  -- the lower bound: `c γ ≥ K ^ (1 - γ) (M - ε γ - M / K)` for every `K ≥ 1`, by Markov
  obtain ⟨K, hK1, hKa⟩ : ∃ K : ℕ, 1 ≤ K ∧ a < M - M / K := by
    have h : Tendsto (fun K : ℕ ↦ M - M / K) atTop (𝓝 (M - M / ∞)) :=
      ENNReal.Tendsto.sub tendsto_const_nhds
        (ENNReal.Tendsto.const_div ENNReal.tendsto_nat_nhds_top (Or.inr hM)) (Or.inl hM)
    rw [ENNReal.div_top, tsub_zero] at h
    obtain ⟨K, hK⟩ := ((h.eventually (lt_mem_nhds ha)).and (eventually_ge_atTop 1)).exists
    exact ⟨K, hK.2, hK.1⟩
  have hK0 : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hK1)
  have hKt : (K : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top K
  have hlow : ∀ᶠ γ in 𝓝[>] 1, (K : ℝ≥0∞) ^ (1 - γ) * M
      - (K : ℝ≥0∞) ^ (1 - γ) * (ε γ + M / K) ≤ ∫⁻ ω, Y γ ω ^ (1 - γ) ∂Q := by
    filter_upwards [self_mem_nhdsWithin] with γ hγ
    exact rpow_mul_sub_le_lintegral_rpow hXm hX_top hX0 (hY γ hγ).mem.measurable
      (hX.lintegral_div_le_measure_univ (hY γ hγ).mem) hK0 hKt hγ.le
  -- the lower bound tends to `M - M / K > a`
  have hKpow : Tendsto (fun γ : ℝ ↦ (K : ℝ≥0∞) ^ (1 - γ)) (𝓝[>] 1) (𝓝 1) := by
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK1
    have h1 : Tendsto (fun γ : ℝ ↦ (K : ℝ) ^ (1 - γ)) (𝓝 1) (𝓝 ((K : ℝ) ^ (1 - 1 : ℝ))) :=
      (Real.continuousAt_const_rpow hK'.ne').tendsto.comp
        ((continuous_const.sub continuous_id).tendsto 1)
    rw [sub_self, Real.rpow_zero] at h1
    have h2 := (ENNReal.tendsto_ofReal h1).mono_left (nhdsWithin_le_nhds (s := Ioi 1))
    rw [ENNReal.ofReal_one] at h2
    refine h2.congr fun γ ↦ ?_
    rw [← ENNReal.ofReal_rpow_of_pos hK', ENNReal.ofReal_natCast]
  have hlim : Tendsto (fun γ ↦ (K : ℝ≥0∞) ^ (1 - γ) * M - (K : ℝ≥0∞) ^ (1 - γ) * (ε γ + M / K))
      (𝓝[>] 1) (𝓝 (M - M / K)) := by
    have h1 := ENNReal.Tendsto.mul_const hKpow (Or.inr hM)
    have h2 := ENNReal.Tendsto.mul hKpow (Or.inl one_ne_zero)
      (hε.add (tendsto_const_nhds (x := M / K))) (Or.inr ENNReal.one_ne_top)
    simpa using ENNReal.Tendsto.sub h1 h2 (Or.inl (by simpa using hM))
  filter_upwards [hlim.eventually (lt_mem_nhds hKa), hlow] with γ h1 h2
  exact h1.trans_le h2

/-- **The reverse Rényi projections converge to the reverse information projection**
[EVR26, Note 27, Theorem 1 (2)]: if `Q` is a finite measure absolutely continuous with respect
to a null of masses at most `1`, `X` is the numeraire and `Y γ` is a numeraire for the power
utility of risk aversion `γ` for every `γ > 1`, then the density
`Y γ ^ (-γ) / ∫⁻ Y γ ^ (1 - γ) ∂Q` of the reverse Rényi projection of order `γ⁻¹` with respect to
`Q` (`IsNumeraireFor.withDensity_rpow_neg_mem_effectiveSet`) converges in `Q`-measure to
`X⁻¹ / Q univ` as `γ ↓ 1`. For a probability measure `Q`, the limit `X⁻¹` is the density of the
reverse information projection `ripr Q S` (`IsNumeraire.ripr_eq`). -/
theorem IsNumeraire.tendstoInMeasure_rpow_neg_of_powerUtility [IsFiniteMeasure Q]
    (hS : ∀ P ∈ S, P univ ≤ 1) (hQS : Q.AbsolutelyContinuousSet S) (hX : IsNumeraire X S Q)
    (hY : ∀ γ (hγ : 1 < γ), IsNumeraireFor (powerUtility γ hγ) (Y γ) {Z | IsEVar Z S} Q) :
    TendstoInMeasure Q (fun γ ω ↦ ((∫⁻ ω', Y γ ω' ^ (1 - γ) ∂Q)⁻¹ * Y γ ω ^ (-γ)).toReal)
      (𝓝[>] 1) (fun ω ↦ ((Q univ)⁻¹ * (X ω)⁻¹).toReal) := by
  rcases eq_zero_or_neZero Q with rfl | hQ
  · exact fun ε _ ↦ by simp
  have hc := tendsto_lintegral_rpow_one_sub_of_powerUtility hS hQS hY
  refine tendstoInMeasure_of_forall_seq_exists_subseq_tendsto_ae ?_ fun u hu ↦ ?_
  · filter_upwards [self_mem_nhdsWithin] with γ hγ
    exact ((((hY γ hγ).mem.measurable.pow_const _).const_mul _).ennreal_toReal).aestronglyMeasurable
  -- along a subsequence, `Y γ → X` almost everywhere, and the powers and constants follow
  obtain ⟨ns, hns, h_ae⟩ :=
    ((hX.tendstoInMeasure_of_powerUtility hS hQS hY).comp hu).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  have hu1 : Tendsto (fun n ↦ u (ns n)) atTop (𝓝[>] 1) := hu.comp hns.tendsto_atTop
  have hc_inv : Tendsto (fun n ↦ ((∫⁻ ω', Y (u (ns n)) ω' ^ (1 - u (ns n)) ∂Q)⁻¹).toReal) atTop
      (𝓝 ((Q univ)⁻¹.toReal)) :=
    (ENNReal.tendsto_toReal (ENNReal.inv_ne_top.2 (NeZero.ne (Q univ)))).comp
      (tendsto_inv_iff.2 (hc.comp hu1))
  have hγ_lim : Tendsto (fun n ↦ -u (ns n)) atTop (𝓝 (-1)) :=
    (tendsto_nhdsWithin_iff.1 hu1).1.neg
  filter_upwards [h_ae, hQS.ae_ne_top hX.isEVar, hX.ae_ne_zero hS] with ω hω hXt hX0
  have hx : (X ω).toReal ≠ 0 := (ENNReal.toReal_pos hX0 hXt).ne'
  have h_pow := hω.rpow hγ_lim (.inl hx)
  rw [Real.rpow_neg_one] at h_pow
  convert hc_inv.mul h_pow using 1
  · ext n
    simp [ENNReal.toReal_mul, ENNReal.toReal_rpow]
  · simp [ENNReal.toReal_mul, ENNReal.toReal_inv]

end ProbabilityTheory
