/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Prod
import LMLExplore.Probability.Independence.Integration

/-!
# The inverse moment of a sum of independent variables with values in `[0, 1]`

For an independent family of random variables `Y i` such that, for `i ∈ s`, `Y i` has values
in `[0, 1]` and expectation at least `q ∈ (0, 1]`, the expectation of `(1 + ∑ i ∈ s, Y i)⁻¹` is
at most `(1 - (1 - q) ^ (#s + 1)) / ((#s + 1) * q)`, the expectation of `(1 + B)⁻¹` for a
binomial variable `B` with `#s` trials of success probability `q`; in particular it is at most
`((#s + 1) * q)⁻¹`. This is the bound behind the null-proportion estimates of adaptive multiple
testing procedures [MD26], used for e-values in
`LMLExplore.EValues.MultipleTesting.AdaptiveEBH`.

The bound comes from the representation `(1 + x)⁻¹ = ∫₀¹ u ^ x du` for `x ≥ 0`: independence
factorizes `E[u ^ ∑ i ∈ s, Y i]`, and `u ^ y ≤ (1 - y) + y * u` for `y ∈ [0, 1]`.

## Main statements

* `ProbabilityTheory.lintegral_inv_one_add_sum_le`: the inverse moment bound.
* `setLIntegral_Ioc_zero_one_rpow`, `setLIntegral_Ioc_zero_one_one_sub_add_mul_pow`: the
  integrals `∫₀¹ u ^ x du` and `∫₀¹ ((1 - q) + q * u) ^ n du`.
* `ENNReal.ofReal_rpow_toReal_le_one_sub_add_mul`: Bernoulli's inequality
  `u ^ y ≤ (1 - y) + y * u` for `y ∈ [0, 1]`, in `ℝ≥0∞`.
* `ENNReal.one_sub_add_mul_le_one_sub_add_mul`: `a ↦ (1 - a) + a * c` is antitone on `[0, 1]`
  for `c ≤ 1`.

## References

* [MD26] I. Meah and S. Döhler, *Improved null proportion estimators for multiple discrete tests
  with plug-in FDR control*, Comput. Statist. Data Anal. 224 (2026), arXiv:2307.13557.
-/

public section

open MeasureTheory Set Finset
open scoped ENNReal

/-- `∫₀¹ u ^ x du = (x + 1)⁻¹` for `x > -1`, as a lower integral. -/
theorem setLIntegral_Ioc_zero_one_rpow {x : ℝ} (hx : -1 < x) :
    ∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal (u ^ x) = ENNReal.ofReal (x + 1)⁻¹ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (intervalIntegral.intervalIntegrable_rpow' hx).1
    ((ae_restrict_mem measurableSet_Ioc).mono fun u hu ↦ Real.rpow_nonneg hu.1.le x),
    ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hx), Real.one_rpow,
    Real.zero_rpow (by linarith), sub_zero, one_div]

namespace ENNReal

/-- **Bernoulli's inequality** in `ℝ≥0∞`: `u ^ y ≤ (1 - y) + y * u` for `0 ≤ u` and
`y ∈ [0, 1]`. -/
theorem ofReal_rpow_toReal_le_one_sub_add_mul {u : ℝ} (hu : 0 ≤ u) {y : ℝ≥0∞} (hy : y ≤ 1) :
    ENNReal.ofReal (u ^ y.toReal) ≤ (1 - y) + y * ENNReal.ofReal u := by
  have hy_top : y ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hy
  have hy1 : y.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hy)
  have h := rpow_one_add_le_one_add_mul_self (s := u - 1) (by linarith)
    ENNReal.toReal_nonneg hy1
  rw [add_sub_cancel] at h
  calc ENNReal.ofReal (u ^ y.toReal) ≤ ENNReal.ofReal ((1 - y.toReal) + y.toReal * u) :=
        ENNReal.ofReal_le_ofReal (h.trans_eq (by ring))
    _ = (1 - y) + y * ENNReal.ofReal u := by
        rw [ENNReal.ofReal_add (by linarith) (by positivity),
          ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
          ENNReal.ofReal_one, ENNReal.ofReal_toReal hy_top]

/-- The affine function `a ↦ (1 - a) + a * c` is antitone on `[0, 1]` for `c ≤ 1`. -/
theorem one_sub_add_mul_le_one_sub_add_mul {q a c : ℝ≥0∞} (hqa : q ≤ a) (ha : a ≤ 1)
    (hc : c ≤ 1) : (1 - a) + a * c ≤ (1 - q) + q * c := by
  obtain ⟨d, rfl⟩ := exists_add_of_le hqa
  have hd : d ≤ 1 - q := ENNReal.le_sub_of_add_le_left
    (ne_top_of_le_ne_top ENNReal.one_ne_top (le_self_add.trans ha)) ha
  calc 1 - (q + d) + (q + d) * c = (1 - q - d) + q * c + d * c := by
        rw [← tsub_tsub, add_mul, add_assoc]
    _ ≤ (1 - q - d) + q * c + d := by gcongr; exact mul_le_of_le_one_right' hc
    _ = (1 - q) + q * c := by rw [add_right_comm, tsub_add_cancel_of_le hd]

end ENNReal

/-- `∫₀¹ ((1 - q) + q * u) ^ n du = (1 - (1 - q) ^ (n + 1)) / ((n + 1) * q)` for `q ∈ (0, 1]`. -/
theorem setLIntegral_Ioc_zero_one_one_sub_add_mul_pow {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq1 : q ≤ 1)
    (n : ℕ) :
    ∫⁻ u in Ioc (0 : ℝ) 1, ((1 - q) + q * ENNReal.ofReal u) ^ n =
      (1 - (1 - q) ^ (n + 1)) / ((n + 1) * q) := by
  have hq_top : q ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hq1
  set r := q.toReal with hr_def
  have hq : q = ENNReal.ofReal r := (ENNReal.ofReal_toReal hq_top).symm
  have hr0 : 0 < r := ENNReal.toReal_pos hq0 hq_top
  have hr1 : r ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hq1)
  have h_eq : ∀ u ∈ Ioc (0 : ℝ) 1,
      ((1 - q) + q * ENNReal.ofReal u) ^ n = ENNReal.ofReal ((r * u + (1 - r)) ^ n) := by
    intro u hu
    have hru : 0 ≤ r * u := mul_nonneg hr0.le hu.1.le
    rw [ENNReal.ofReal_pow (by linarith), ENNReal.ofReal_add hru (by linarith),
      ENNReal.ofReal_mul hr0.le, ENNReal.ofReal_sub _ hr0.le, ← hq]
    simp [add_comm]
  rw [setLIntegral_congr_fun measurableSet_Ioc h_eq, ← ofReal_integral_eq_lintegral_ofReal
    ((by fun_prop : Continuous fun u : ℝ ↦ (r * u + (1 - r)) ^ n).intervalIntegrable 0 1).1
    ((ae_restrict_mem measurableSet_Ioc).mono fun u hu ↦ by
      dsimp only [Pi.zero_apply]; exact pow_nonneg (by nlinarith [hu.1]) n),
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_mul_add (fun x ↦ x ^ n) hr0.ne', integral_pow]
  simp only [mul_zero, zero_add, mul_one, add_sub_cancel, one_pow, smul_eq_mul]
  -- Both sides are finite: compare them in `ℝ`.
  have h1 : (1 - q) ^ (n + 1) ≤ 1 := pow_le_one₀ zero_le tsub_le_self
  rw [← ENNReal.ofReal_toReal (a := (1 - (1 - q) ^ (n + 1)) / ((n + 1) * q))
    (ENNReal.div_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top) (mul_ne_zero (by simp) hq0))]
  simp [ENNReal.toReal_sub_of_le h1, ENNReal.toReal_sub_of_le hq1, ENNReal.toReal_add, ← hr_def]
  field_simp

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The inverse moment of a sum of independent variables with values in `[0, 1]`** [MD26]. Let
`Y : ι → Ω → ℝ≥0∞` be an independent family, and let `Y i`, for `i ∈ s`, be measurable and almost
surely at most `1`, with expectations at least `q ∈ (0, 1]`. Then
`E[(1 + ∑ i ∈ s, Y i)⁻¹] ≤ (1 - (1 - q) ^ (#s + 1)) / ((#s + 1) * q)`, the value of the left side
for independent Bernoulli variables of parameter `q`. -/
theorem lintegral_inv_one_add_sum_le [IsProbabilityMeasure P] {Y : ι → Ω → ℝ≥0∞}
    (hY : iIndepFun Y P) (s : Finset ι) (hY_meas : ∀ i ∈ s, Measurable (Y i))
    (hY_le : ∀ i ∈ s, ∀ᵐ ω ∂P, Y i ω ≤ 1) {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq1 : q ≤ 1)
    (hq : ∀ i ∈ s, q ≤ ∫⁻ ω, Y i ω ∂P) :
    ∫⁻ ω, (1 + ∑ i ∈ s, Y i ω)⁻¹ ∂P ≤ (1 - (1 - q) ^ (#s + 1)) / ((#s + 1) * q) := by
  -- `(1 + x)⁻¹ = ∫₀¹ u ^ x du`, and `u ^ ∑ i ∈ s, Y i` is the product of the `u ^ Y i`.
  have h_rep : ∀ᵐ ω ∂P, (1 + ∑ i ∈ s, Y i ω)⁻¹ =
      ∫⁻ u in Ioc (0 : ℝ) 1, ∏ i ∈ s, ENNReal.ofReal (u ^ (Y i ω).toReal) := by
    filter_upwards [(Filter.eventually_all_finset s).2 hY_le] with ω hω
    have h_top : ∀ i ∈ s, Y i ω ≠ ∞ := fun i hi ↦ ne_top_of_le_ne_top ENNReal.one_ne_top (hω i hi)
    have h_sum : 1 + ∑ i ∈ s, Y i ω = ENNReal.ofReal (∑ i ∈ s, (Y i ω).toReal + 1) := by
      rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_one, add_comm,
        ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ ENNReal.toReal_nonneg]
      exact congrArg (· + 1) (sum_congr rfl fun i hi ↦ (ENNReal.ofReal_toReal (h_top i hi)).symm)
    rw [h_sum, ← ENNReal.ofReal_inv_of_pos (by positivity), ← setLIntegral_Ioc_zero_one_rpow
      (by linarith [show 0 ≤ ∑ i ∈ s, (Y i ω).toReal by positivity])]
    refine setLIntegral_congr_fun measurableSet_Ioc fun u hu ↦ ?_
    rw [Real.rpow_sum_of_pos hu.1, ENNReal.ofReal_prod_of_nonneg fun i _ ↦
      Real.rpow_nonneg hu.1.le _]
  rw [lintegral_congr_ae h_rep, lintegral_lintegral_swap (Measurable.aemeasurable (by
    refine Finset.measurable_prod _ fun i hi ↦ ?_
    exact (measurable_snd.pow ((hY_meas i hi).ennreal_toReal.comp measurable_fst)).ennreal_ofReal)),
    ← setLIntegral_Ioc_zero_one_one_sub_add_mul_pow hq0 hq1]
  refine setLIntegral_mono' measurableSet_Ioc fun u hu ↦ ?_
  -- By independence, `E[u ^ ∑ i ∈ s, Y i] = ∏ i ∈ s, E[u ^ Y i] ≤ ((1 - q) + q * u) ^ #s`.
  have h_meas : Measurable fun y : ℝ≥0∞ ↦ ENNReal.ofReal (u ^ y.toReal) :=
    (measurable_const.pow ENNReal.measurable_toReal).ennreal_ofReal
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun'
    (X := fun i ω ↦ ENNReal.ofReal (u ^ (Y i ω).toReal)) s (hY.comp _ fun _ ↦ h_meas)
    fun i hi ↦ h_meas.comp (hY_meas i hi), ← prod_const]
  refine prod_le_prod fun i hi ↦ ?_
  have h_int : ∫⁻ ω, Y i ω ∂P ≤ 1 := (lintegral_mono_ae (hY_le i hi)).trans_eq (by simp)
  calc ∫⁻ ω, ENNReal.ofReal (u ^ (Y i ω).toReal) ∂P
      ≤ ∫⁻ ω, (1 - Y i ω) + Y i ω * ENNReal.ofReal u ∂P :=
        lintegral_mono_ae ((hY_le i hi).mono fun ω h ↦
          ENNReal.ofReal_rpow_toReal_le_one_sub_add_mul hu.1.le h)
    _ = (1 - ∫⁻ ω, Y i ω ∂P) + (∫⁻ ω, Y i ω ∂P) * ENNReal.ofReal u := by
        rw [lintegral_add_right _ ((hY_meas i hi).mul_const _),
          lintegral_mul_const _ (hY_meas i hi), lintegral_sub (hY_meas i hi)
            (ne_top_of_le_ne_top ENNReal.one_ne_top h_int) (hY_le i hi), lintegral_const,
          measure_univ, mul_one]
    _ ≤ (1 - q) + q * ENNReal.ofReal u :=
        ENNReal.one_sub_add_mul_le_one_sub_add_mul (hq i hi) h_int (ENNReal.ofReal_le_one.2 hu.2)

end ProbabilityTheory
