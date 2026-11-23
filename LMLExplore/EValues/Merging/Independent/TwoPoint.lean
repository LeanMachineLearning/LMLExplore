/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Merging.Independent
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import LMLExplore.MeasureTheory.Constructions.Pi
import LMLExplore.Order.Filter.Basic
import LMLExplore.Probability.Distributions.Bernoulli
import TauCeti.MeasureTheory.Integral.Pi

/-!
# Merging functions for independent e-values: two-point laws and admissibility

A function `g` of one e-value with `∫⁻ g ∂μ ≤ 1` for every law `μ` on `ℝ≥0∞` supported on at most
two points and with mean at most `1` (a Bernoulli law `Ber(x, y, p)`) is dominated, at finite
arguments, by a weighted mean `w₀ + w * e` with `w₀ + w = 1`, and so has `∫⁻ g ∂μ ≤ 1` for every
law `μ` with mean at most `1`: for one e-value, the laws on two points determine the e-merging
functions.

The same holds for merging functions of independent e-values [VW24, Proposition 1]: a measurable
`F : (ι → ℝ≥0∞) → ℝ≥0∞` is a merging function for independent e-values as soon as it merges
independent e-values each taking at most two values, that is,
`∫⁻ F ∂(Measure.pi fun i ↦ Ber(x i, y i, p i)) ≤ 1` whenever every `Ber(x i, y i, p i)` has mean
at most `1`.

Two consequences follow from laws on two points [VW21, Section 4]:

* every merging function for independent e-values is at most `∏ i, max 1 (e i)` at every point
  `e`, so the product weakly dominates it: the product is at least the merging function on
  `[1, ∞]ᴷ` [VW21, Proposition 4.2];
* a precise merging function for independent e-values, one with integral `1` against every
  product of laws with mean `1`, is admissible [VW21, Proposition 4.1]: a product of laws with
  mean `1` charges every point with finite coordinates. The product of the e-values, the
  U-statistics `U n`, which average the products of `n` of the e-values, and their mixtures
  are precise, hence admissible.

As for e-merging functions, admissibility is admissibility among the e-variables of the merging
null of the product laws, whose quasi-sure filter is the principal filter of the points with
finite coordinates: values at infinite arguments are not compared.

## Main definitions

* `ProbabilityTheory.IsAdmissibleIEMerging F`: `F` is an admissible e-variable for the merging
  null of the product laws.
* `ProbabilityTheory.uStatistic n e`: the U-statistic of order `n` of the e-values `e`, the
  elementary symmetric polynomial of degree `n` divided by the number of its terms.

## Main statements

* `ProbabilityTheory.exists_le_add_mul_of_forall_lintegral_bernoulliMeasure_le_one`: a function of
  one e-value with integral at most `1` against the laws on two points with mean at most `1` is
  dominated, at finite arguments, by a weighted mean.
* `ProbabilityTheory.lintegral_le_one_of_forall_lintegral_bernoulliMeasure_le_one`: such a
  function has integral at most `1` against every law with mean at most `1`.
* `ProbabilityTheory.isIEMerging_iff_forall_lintegral_pi_bernoulliMeasure_le_one`: the merging
  functions for independent e-values are the measurable functions that merge independent
  e-values taking at most two values [VW24, Proposition 1].
* `ProbabilityTheory.IsIEMerging.le_prod_max_one`, `ProbabilityTheory.IsIEMerging.le_prod`: a
  merging function for independent e-values is at most `∏ i, max 1 (e i)`, and at most the product
  on `[1, ∞]ᴷ` [VW21, Proposition 4.2].
* `ProbabilityTheory.isAdmissibleIEMerging_iff_isAdmissible`,
  `ProbabilityTheory.IsAdmissibleIEMerging.eq_of_le`: admissibility reads at finite arguments.
* `ProbabilityTheory.IsPreciseIEMerging.isAdmissibleIEMerging`: precise merging functions for
  independent e-values are admissible [VW21, Proposition 4.1].
* `ProbabilityTheory.isAdmissibleIEMerging_uStatistic`,
  `ProbabilityTheory.isAdmissibleIEMerging_prod`,
  `ProbabilityTheory.isAdmissibleIEMerging_sum_mul_uStatistic`: the U-statistics, the product, and
  the mixtures of the U-statistics, are admissible merging functions for independent e-values
  [VW21, Section 4].

## Implementation notes

For one e-value, the laws on two points with mean `1`, together with the point masses at `x ≤ 1`,
bound the slopes of `g` on both sides of `1`, and the supremum of the slopes on the right is the
weight `w`. For several e-values, integrating `F` against the laws of all coordinates but one
leaves a function of one e-value, to which this applies, by induction on the set of coordinates
whose law is arbitrary (`MeasureTheory.Measure.lintegral_pi_update_measure`). This replaces the
decomposition of a law with finite mean into a mixture of laws on two points with the same mean
used in [VW24].

## References

* [VW21] V. Vovk and R. Wang, *E-values: calibration, combination and applications*, Ann. Statist.
  49 (2021), arXiv:1912.06116v4: Section 4 (Propositions 4.1 and 4.2, the product and the
  U-statistics).
* [VW24] V. Vovk and R. Wang, *Merging sequential e-values via martingales*, Electron. J.
  Statist. 18 (2024), arXiv:2007.06382v3: Section 2 (Proposition 1, two-point laws).
-/

public section

open MeasureTheory unitInterval
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-! ### One e-value -/

section OneEValue

variable {g : ℝ≥0∞ → ℝ≥0∞}

/-- **A law on two points with mean `1`.** If `g` has integral at most `1` against the laws on two
points with mean at most `1`, then for `0 ≤ a < 1 < b` the law on `{a, b}` with mean `1` gives
`(b - 1) * g a + (1 - a) * g b ≤ b - a`, in real numbers, with `g a` and `g b` finite. -/
private lemma toReal_le_of_forall_lintegral_bernoulliMeasure_le_one
    (hg : ∀ (x y : ℝ≥0∞) (p : I), ∫⁻ z, z ∂Ber(x, y, p) ≤ 1 → ∫⁻ z, g z ∂Ber(x, y, p) ≤ 1)
    {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb1 : 1 < b) :
    g (ENNReal.ofReal a) ≠ ∞ ∧ g (ENNReal.ofReal b) ≠ ∞ ∧
      (b - 1) * (g (ENNReal.ofReal a)).toReal + (1 - a) * (g (ENNReal.ofReal b)).toReal ≤
        b - a := by
  have hba : 0 < b - a := by linarith
  -- The Bernoulli law with weight `w = (b - 1) / (b - a)` on `a` has mean `1`.
  set w : I := ⟨(b - 1) / (b - a), div_nonneg (by linarith) hba.le,
    (div_le_one hba).2 (by linarith)⟩
  have hw0 : 0 < (w : ℝ) := div_pos (by linarith) hba
  have hw : (1 : ℝ) - w = (1 - a) / (b - a) := by
    simp only [w]
    field_simp
    ring
  have hw1 : 0 < (1 : ℝ) - w := by
    rw [hw]
    exact div_pos (by linarith) hba
  have h_mean : ∫⁻ x, x ∂Ber(ENNReal.ofReal a, ENNReal.ofReal b, w) ≤ 1 := by
    rw [lintegral_id_bernoulliMeasure_ofReal ha0 (by linarith), hw]
    exact ENNReal.ofReal_le_one.2 (le_of_eq (by simp only [w]; field_simp; ring))
  have h := hg _ _ _ h_mean
  rw [lintegral_bernoulliMeasure] at h
  -- Both weights are positive, so both values are finite.
  have hfin {c : ℝ} (hc : 0 < c) {t : ℝ≥0∞} (ht : ENNReal.ofReal c * t ≤ 1) : t ≠ ∞ := by
    rintro rfl
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne'] at ht
    exact ENNReal.top_ne_one (le_antisymm ht le_top)
  have ha_top := hfin hw0 (le_self_add.trans h)
  have hb_top := hfin hw1 (le_add_self.trans h)
  refine ⟨ha_top, hb_top, ?_⟩
  have h_real := ENNReal.toReal_mono ENNReal.one_ne_top h
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hw0.le, ENNReal.toReal_ofReal hw1.le, hw,
    ENNReal.toReal_one] at h_real
  calc (b - 1) * (g (ENNReal.ofReal a)).toReal + (1 - a) * (g (ENNReal.ofReal b)).toReal
      = (b - a) * ((b - 1) / (b - a) * (g (ENNReal.ofReal a)).toReal +
        (1 - a) / (b - a) * (g (ENNReal.ofReal b)).toReal) := by
        field_simp
    _ ≤ (b - a) * 1 := mul_le_mul_of_nonneg_left h_real hba.le
    _ = b - a := mul_one _

/-- **Domination by a weighted mean from two-point laws.** A function `g` of one e-value with
`∫⁻ g ∂μ ≤ 1` for every law `μ` on at most two points with mean at most `1` is dominated, at
finite arguments, by a weighted mean `w₀ + w * e` with `w₀ + w = 1`. This is the case of one
e-value of `ProbabilityTheory.IsEMerging.exists_le_add_sum_mul`, from laws on two points only. -/
theorem exists_le_add_mul_of_forall_lintegral_bernoulliMeasure_le_one
    (hg : ∀ (x y : ℝ≥0∞) (p : I), ∫⁻ z, z ∂Ber(x, y, p) ≤ 1 → ∫⁻ z, g z ∂Ber(x, y, p) ≤ 1) :
    ∃ w₀ w : ℝ≥0, w₀ + w = 1 ∧ ∀ e : ℝ≥0, g e ≤ w₀ + w * e := by
  have hstep := @toReal_le_of_forall_lintegral_bernoulliMeasure_le_one g hg
  -- Point masses at `x ≤ 1` give `g x ≤ 1`.
  have h_small (x : ℝ) (hx1 : x ≤ 1) : g (ENNReal.ofReal x) ≤ 1 := by
    simpa [lintegral_bernoulliMeasure] using
      hg (ENNReal.ofReal x) 0 1 (by simpa [lintegral_bernoulliMeasure] using hx1)
  have hg_top (x : ℝ) (hx0 : 0 ≤ x) : g (ENNReal.ofReal x) ≠ ∞ := by
    rcases le_or_gt x 1 with hx1 | hx1
    · exact ne_top_of_le_ne_top ENNReal.one_ne_top (h_small x hx1)
    · exact (hstep le_rfl zero_lt_one hx1).2.1
  -- The real counterpart `G` of `g`.
  set G : ℝ → ℝ := fun x ↦ (g (ENNReal.ofReal x)).toReal
  have hG1 (x : ℝ) (hx1 : x ≤ 1) : G x ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h_small x hx1)
  have hG0 (x : ℝ) : 0 ≤ G x := ENNReal.toReal_nonneg
  -- The slopes `(G b - 1) / (b - 1)`, `b > 1`, are below the slopes `(1 - G a) / (1 - a)`,
  -- `a < 1`.
  set A : Set ℝ := (fun b ↦ (G b - 1) / (b - 1)) '' Set.Ioi 1
  have hA_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) : ∀ y ∈ A, y ≤ (1 - G a) / (1 - a) := by
    rintro _ ⟨b, hb, rfl⟩
    have hb : 1 < b := hb
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [(hstep ha0 ha1 hb).2.2]
  have hA_ne : A.Nonempty := ⟨_, Set.mem_image_of_mem _ (show (2 : ℝ) ∈ Set.Ioi 1 by norm_num)⟩
  have hA_bdd : BddAbove A := ⟨_, hA_le 0 le_rfl zero_lt_one⟩
  -- The weight `w` is the supremum of the slopes on the right of `1`, or `0`.
  set w := max (sSup A) 0
  have hw0 : 0 ≤ w := le_max_right _ _
  have hw1 : w ≤ 1 := max_le ((csSup_le hA_ne (hA_le 0 le_rfl zero_lt_one)).trans
    (by simpa using hG0 0)) zero_le_one
  have hG_lin (x : ℝ) (hx0 : 0 ≤ x) : G x ≤ (1 - w) + w * x := by
    rcases lt_trichotomy x 1 with hx | rfl | hx
    · have h : w ≤ (1 - G x) / (1 - x) := max_le (csSup_le hA_ne (hA_le x hx0 hx))
        (div_nonneg (by linarith [hG1 x hx.le]) (by linarith))
      rw [le_div_iff₀ (by linarith)] at h
      linarith
    · simpa using hG1 1 le_rfl
    · have h := (le_csSup hA_bdd (Set.mem_image_of_mem _ (show x ∈ Set.Ioi 1 from hx))).trans
        (le_max_left _ 0)
      rw [div_le_iff₀ (by linarith)] at h
      linarith
  refine ⟨Real.toNNReal (1 - w), Real.toNNReal w, ?_, fun e ↦ ?_⟩
  · rw [← Real.toNNReal_add (by linarith) hw0, sub_add_cancel, Real.toNNReal_one]
  · rw [ENNReal.ofNNReal_toNNReal, ENNReal.ofNNReal_toNNReal, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul hw0, ← ENNReal.ofReal_add (by linarith) (by positivity)]
    exact (ENNReal.ofReal_toReal (hg_top _ e.2)).symm.trans_le
      (ENNReal.ofReal_le_ofReal (hG_lin e e.2))

/-- **Two-point laws suffice for one e-value.** A function `g` of one e-value with `∫⁻ g ∂ν ≤ 1`
for every law `ν` on at most two points with mean at most `1` has `∫⁻ g ∂μ ≤ 1` for every
probability measure `μ` on `ℝ≥0∞` with mean at most `1`. -/
theorem lintegral_le_one_of_forall_lintegral_bernoulliMeasure_le_one
    (hg : ∀ (x y : ℝ≥0∞) (p : I), ∫⁻ z, z ∂Ber(x, y, p) ≤ 1 → ∫⁻ z, g z ∂Ber(x, y, p) ≤ 1)
    {μ : Measure ℝ≥0∞} [IsProbabilityMeasure μ] (hμ : ∫⁻ z, z ∂μ ≤ 1) :
    ∫⁻ z, g z ∂μ ≤ 1 := by
  obtain ⟨w₀, w, hw, hle⟩ := exists_le_add_mul_of_forall_lintegral_bernoulliMeasure_le_one hg
  -- The mean is finite, so `μ` is carried by the finite points.
  have hfin : ∀ᵐ z ∂μ, z ≠ ∞ :=
    (ae_lt_top measurable_id (ne_top_of_le_ne_top ENNReal.one_ne_top hμ)).mono fun _ ↦ ne_of_lt
  calc ∫⁻ z, g z ∂μ ≤ ∫⁻ z, (w₀ + w * z) ∂μ := lintegral_mono_ae <| hfin.mono fun z hz ↦ by
        simpa [ENNReal.coe_toNNReal hz] using hle z.toNNReal
    _ = w₀ + w * ∫⁻ z, z ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ measurable_id']
    _ ≤ w₀ + w * 1 := by gcongr
    _ = 1 := by rw [mul_one, ← ENNReal.coe_add, hw, ENNReal.coe_one]

end OneEValue

/-! ### Independent e-values taking two values -/

section TwoPoint

variable {ι : Type*} [Fintype ι] {F : (ι → ℝ≥0∞) → ℝ≥0∞}

/-- Induction on the set `s` of coordinates whose law is arbitrary: the integral of `F` against a
product of laws with mean at most `1` is at most `1` when the laws outside `s` are on two points.
Integrating `F` against the other laws leaves a function of the coordinate `i` with integral at
most `1` against the laws on two points, by induction, hence against every law. -/
private lemma lintegral_pi_le_one_of_forall_lintegral_pi_bernoulliMeasure_le_one
    (hF : Measurable F)
    (h : ∀ (x y : ι → ℝ≥0∞) (p : ι → I), (∀ i, ∫⁻ z, z ∂Ber(x i, y i, p i) ≤ 1) →
      ∫⁻ e, F e ∂Measure.pi (fun i ↦ Ber(x i, y i, p i)) ≤ 1)
    (s : Finset ι) (μ : ι → Measure ℝ≥0∞) (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hmean : ∀ i, ∫⁻ z, z ∂μ i ≤ 1) (hber : ∀ i ∉ s, ∃ x y p, μ i = Ber(x, y, p)) :
    ∫⁻ e, F e ∂Measure.pi μ ≤ 1 := by
  classical
  induction s using Finset.induction_on generalizing μ with
  | empty =>
    choose x y p hxyp using fun i ↦ hber i (Finset.notMem_empty i)
    obtain rfl : μ = fun i ↦ Ber(x i, y i, p i) := funext hxyp
    exact h x y p hmean
  | insert i s hi ih =>
    -- Replacing the law of the coordinate `i` by a probability measure `ν`.
    have hupd (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν] (j : ι) :
        IsProbabilityMeasure (Function.update μ i ν j) := by
      rcases eq_or_ne j i with rfl | hj
      · rwa [Function.update_self]
      · rw [Function.update_of_ne hj]
        exact hμ j
    have heq (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν] :
        ∫⁻ e, F e ∂Measure.pi (Function.update μ i ν) =
          ∫⁻ z, ∫⁻ e, F (Function.update e i z) ∂Measure.pi μ ∂ν :=
      Measure.lintegral_pi_update_measure μ i ν hF
    rw [← Function.update_eq_self i μ, heq]
    refine lintegral_le_one_of_forall_lintegral_bernoulliMeasure_le_one (fun x y p hp ↦ ?_)
      (hmean i)
    rw [← heq]
    refine ih _ (hupd _) (fun j ↦ ?_) fun j hj ↦ ?_ <;> rcases eq_or_ne j i with rfl | hji
    · simpa using hp
    · simpa [Function.update_of_ne hji] using hmean j
    · exact ⟨x, y, p, Function.update_self ..⟩
    · rw [Function.update_of_ne hji]
      exact hber j (by simp [hji, hj])

/-- **Two-point laws characterize merging functions for independent e-values** [VW24,
Proposition 1]: a function of e-values is a merging function for independent e-values exactly
when it is measurable and merges independent e-values each taking at most two values, that is,
its integral against `Measure.pi fun i ↦ Ber(x i, y i, p i)` is at most `1` whenever every
`Ber(x i, y i, p i)` has mean at most `1`. -/
theorem isIEMerging_iff_forall_lintegral_pi_bernoulliMeasure_le_one :
    IsIEMerging F ↔ Measurable F ∧
      ∀ (x y : ι → ℝ≥0∞) (p : ι → I), (∀ i, ∫⁻ z, z ∂Ber(x i, y i, p i) ≤ 1) →
        ∫⁻ e, F e ∂Measure.pi (fun i ↦ Ber(x i, y i, p i)) ≤ 1 := by
  refine ⟨fun hF ↦ ⟨hF.measurable, fun x y p ↦ hF.lintegral_le_one _⟩, fun ⟨hF, h⟩ ↦
    ⟨hF, fun μ hμ hmean ↦ ?_⟩⟩
  exact lintegral_pi_le_one_of_forall_lintegral_pi_bernoulliMeasure_le_one hF h Finset.univ μ hμ
    hmean fun i hi ↦ absurd (Finset.mem_univ i) hi

/-- **The product weakly dominates every merging function for independent e-values**: such a
function is at most `∏ i, max 1 (e i)` at every point `e`. -/
theorem IsIEMerging.le_prod_max_one (hF : IsIEMerging F) (e : ι → ℝ≥0∞) :
    F e ≤ ∏ i, max 1 (e i) := by
  classical
  have hm0 (i : ι) : max 1 (e i) ≠ 0 := (zero_lt_one.trans_le (le_max_left _ _)).ne'
  by_cases htop : ∃ i, e i = ∞
  · obtain ⟨i, hi⟩ := htop
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hi, max_eq_right le_top,
      ENNReal.top_mul (Finset.prod_ne_zero_iff.2 fun j _ ↦ hm0 j)]
    exact le_top
  simp only [not_exists] at htop
  have hmtop (i : ι) : max 1 (e i) ≠ ∞ := max_ne_top ENNReal.one_ne_top (htop i)
  have hm1 (i : ι) : 1 ≤ (max 1 (e i)).toReal := by
    simpa using ENNReal.toReal_mono (hmtop i) (le_max_left 1 (e i))
  -- Under the product of the laws `Ber(e i, 0, p i)` with `p i = (max 1 (e i))⁻¹`, which have
  -- mean at most `1`, the point `e` has mass at least `∏ i, (max 1 (e i))⁻¹`.
  set p : ι → I := fun i ↦ ⟨((max 1 (e i)).toReal)⁻¹, by positivity, inv_le_one_of_one_le₀ (hm1 i)⟩
  have hp (i : ι) : ENNReal.ofReal (p i) = (max 1 (e i))⁻¹ := by
    rw [← ENNReal.ofReal_toReal (hmtop i), ← ENNReal.ofReal_inv_of_pos (by linarith [hm1 i])]
  set μ : ι → Measure ℝ≥0∞ := fun i ↦ Ber(e i, 0, p i)
  have hmean (i : ι) : ∫⁻ z, z ∂μ i ≤ 1 := by
    rw [lintegral_bernoulliMeasure, hp, mul_zero, add_zero]
    calc (max 1 (e i))⁻¹ * e i ≤ (max 1 (e i))⁻¹ * max 1 (e i) := by
          gcongr
          exact le_max_right _ _
      _ = 1 := ENNReal.inv_mul_cancel (hm0 i) (hmtop i)
  have hmass (i : ι) : (max 1 (e i))⁻¹ ≤ μ i {e i} := by
    rw [← lintegral_indicator_one (measurableSet_singleton _), lintegral_bernoulliMeasure, hp]
    simp
  have hint : F e * ∏ i, (max 1 (e i))⁻¹ ≤ 1 :=
    calc F e * ∏ i, (max 1 (e i))⁻¹ ≤ F e * Measure.pi μ {e} := by
          rw [Measure.pi_singleton]
          gcongr with i
          exact hmass i
      _ = ∫⁻ x in {e}, F x ∂Measure.pi μ := (lintegral_singleton' hF.measurable e).symm
      _ ≤ ∫⁻ x, F x ∂Measure.pi μ := setLIntegral_le_lintegral _ _
      _ ≤ 1 := hF.lintegral_le_one μ hmean
  have hc : (∏ i, (max 1 (e i))⁻¹) * ∏ i, max 1 (e i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ ↦ ENNReal.inv_mul_cancel (hm0 i) (hmtop i)
  calc F e = F e * ((∏ i, (max 1 (e i))⁻¹) * ∏ i, max 1 (e i)) := by rw [hc, mul_one]
    _ = (F e * ∏ i, (max 1 (e i))⁻¹) * ∏ i, max 1 (e i) := (mul_assoc _ _ _).symm
    _ ≤ 1 * ∏ i, max 1 (e i) := by gcongr
    _ = ∏ i, max 1 (e i) := one_mul _

/-- **The product weakly dominates every merging function for independent e-values** [VW21,
Proposition 4.2]: at a point whose coordinates are at least `1`, such a function is at most the
product of the coordinates. -/
theorem IsIEMerging.le_prod (hF : IsIEMerging F) {e : ι → ℝ≥0∞} (he : ∀ i, 1 ≤ e i) :
    F e ≤ ∏ i, e i :=
  (hF.le_prod_max_one e).trans_eq (Finset.prod_congr rfl fun i _ ↦ max_eq_right (he i))

end TwoPoint

/-! ### Admissible merging functions for independent e-values -/

section Admissible

variable {ι : Type*} [Fintype ι] {F G : (ι → ℝ≥0∞) → ℝ≥0∞}

/-- Every point with finite coordinates is charged by a product of probability measures with
mean `1`: a product of laws on two points. -/
private lemma exists_pi_measure_singleton_ne_zero (e : ι → ℝ≥0) :
    ∃ μ : ι → Measure ℝ≥0∞, (∀ i, IsProbabilityMeasure (μ i)) ∧ (∀ i, ∫⁻ z, z ∂μ i = 1) ∧
      Measure.pi μ {fun i ↦ (e i : ℝ≥0∞)} ≠ 0 := by
  choose μ hμ hmean hμe using fun i ↦ exists_lintegral_id_eq_one (ENNReal.coe_ne_top (r := e i))
  refine ⟨μ, hμ, hmean, ?_⟩
  rw [Measure.pi_singleton]
  exact Finset.prod_ne_zero_iff.2 fun i _ ↦ hμe i

/-- **The quasi-sure filter of the merging null of the product laws** is the principal filter of
the points with finite coordinates: a product of laws with mean `1` charges each of them. -/
theorem quasiSure_mergingNull_productLaws_eq_principal :
    quasiSure (mergingNull (productLaws : Set (Measure (ι → ℝ≥0∞)))) =
      Filter.principal (Set.range fun (e : ι → ℝ≥0) i ↦ (e i : ℝ≥0∞)) := by
  refine quasiSure_mergingNull_eq_principal fun e ↦ ?_
  obtain ⟨μ, hμ, hmean, hne⟩ := exists_pi_measure_singleton_ne_zero e
  exact ⟨_, (pi_mem_mergingNull_productLaws_iff μ).2 fun i ↦ (hmean i).le, hne⟩

/-- An **admissible merging function for independent e-values** [VW21, Section 4]: an admissible
e-variable for the merging null of the product laws, whose e-variables are the merging functions
for independent e-values (`isIEMerging_iff_isEVar_mergingNull`). Its quasi-sure filter is the
principal filter of the points with finite coordinates
(`quasiSure_mergingNull_productLaws_eq_principal`), so `F` is admissible when every merging
function for independent e-values dominating it at finite arguments equals it there
(`isAdmissibleIEMerging_iff_isAdmissible`, `IsAdmissibleIEMerging.eq_of_le`). -/
abbrev IsAdmissibleIEMerging (F : (ι → ℝ≥0∞) → ℝ≥0∞) : Prop :=
  IsAdmissibleEVar F (mergingNull productLaws)

/-- An admissible merging function for independent e-values is a merging function for independent
e-values. -/
theorem IsAdmissibleIEMerging.isIEMerging (hF : IsAdmissibleIEMerging F) : IsIEMerging F :=
  isIEMerging_iff_isEVar_mergingNull.2 hF.mem

/-- An admissible merging function for independent e-values is admissible (`Filter.IsAdmissible`)
among the merging functions for independent e-values for the order at finite arguments, the
eventual order along the principal filter of the finite vectors, and conversely. -/
theorem isAdmissibleIEMerging_iff_isAdmissible :
    IsAdmissibleIEMerging F ↔
      (Filter.principal (Set.range fun (e : ι → ℝ≥0) i ↦ (e i : ℝ≥0∞))).IsAdmissible
        {G | IsIEMerging G} F := by
  simp only [IsAdmissibleIEMerging, IsAdmissibleEVar,
    quasiSure_mergingNull_productLaws_eq_principal, ← isIEMerging_iff_isEVar_mergingNull]

/-- A merging function for independent e-values that dominates an admissible one at finite
arguments is equal to it there. -/
theorem IsAdmissibleIEMerging.eq_of_le (hF : IsAdmissibleIEMerging F) (hG : IsIEMerging G)
    (hFG : ∀ e : ι → ℝ≥0, F (fun i ↦ e i) ≤ G (fun i ↦ e i)) (e : ι → ℝ≥0) :
    G (fun i ↦ e i) = F (fun i ↦ e i) :=
  (Filter.eventuallyLE_principal_range_iff.1
    ((isAdmissibleIEMerging_iff_isAdmissible.1 hF).eventuallyLE hG
      (Filter.eventuallyLE_principal_range_iff.2 hFG)) e).antisymm (hFG e)

/-- **Precise merging functions for independent e-values are admissible** [VW21,
Proposition 4.1]. -/
theorem IsPreciseIEMerging.isAdmissibleIEMerging (hF : IsPreciseIEMerging F) :
    IsAdmissibleIEMerging F := by
  -- If `G ≥ F` at finite arguments, then `G - F` has integral `0` against every product of laws
  -- with mean `1`, and such a product charges any given point with finite coordinates.
  refine isAdmissibleIEMerging_iff_isAdmissible.2 ⟨hF.toIsIEMerging, fun G hG hle ↦
    Filter.eventuallyLE_principal_range_iff.2 fun e ↦ ?_⟩
  have hG : IsIEMerging G := hG
  replace hle := Filter.eventuallyLE_principal_range_iff.1 hle
  obtain ⟨μ, hμ, hmean, hne⟩ := exists_pi_measure_singleton_ne_zero e
  have hfin : ∀ᵐ x ∂Measure.pi μ, ∀ i, x i ≠ ∞ := ae_all_iff.2 fun i ↦
    (isEVar_eval_mergingNull productLaws i).ae_ne_top
      ((pi_mem_mergingNull_productLaws_iff μ).2 fun i ↦ (hmean i).le)
  have hF1 := hF.lintegral_eq_one μ hmean
  have hint : ∫⁻ x, (G x - F x) ∂Measure.pi μ = 0 := by
    rw [lintegral_sub hF.measurable (hF1 ▸ ENNReal.one_ne_top) (ae_le_of_forall_nnreal_le hfin hle),
      hF1]
    exact tsub_eq_zero_of_le (hG.lintegral_le_one μ fun i ↦ (hmean i).le)
  have h0 : (G (fun i ↦ e i) - F (fun i ↦ e i)) * Measure.pi μ {fun i ↦ (e i : ℝ≥0∞)} = 0 :=
    le_antisymm (((lintegral_singleton' (hG.measurable.sub hF.measurable) _).symm.trans_le
      (setLIntegral_le_lintegral _ _)).trans hint.le) zero_le
  exact tsub_eq_zero_iff_le.1 ((mul_eq_zero.1 h0).resolve_right hne)

end Admissible

/-! ### Mixtures and U-statistics -/

section Mixture

variable {ι κ : Type*} [Fintype ι] [Countable κ] {w : κ → ℝ≥0∞}
  {F : κ → (ι → ℝ≥0∞) → ℝ≥0∞}

/-- A countable mixture `∑' j, w j * F j e`, with total weight at most `1`, of merging functions
for independent e-values is one. -/
theorem isIEMerging_tsum_mul (hw : ∑' j, w j ≤ 1) (hF : ∀ j, IsIEMerging (F j)) :
    IsIEMerging fun e ↦ ∑' j, w j * F j e := by
  refine ⟨Measurable.tsum fun j ↦ (hF j).measurable.const_mul _, fun μ _ hμ ↦ ?_⟩
  rw [lintegral_tsum fun j ↦ ((hF j).measurable.const_mul _).aemeasurable]
  simp_rw [lintegral_const_mul _ (hF _).measurable]
  calc ∑' j, w j * ∫⁻ e, F j e ∂Measure.pi μ ≤ ∑' j, w j * 1 :=
        tsum_le_tsum fun j ↦ by gcongr; exact (hF j).lintegral_le_one μ hμ
    _ ≤ 1 := by simpa using hw

/-- A countable mixture `∑' j, w j * F j e`, with total weight `1`, of precise merging functions
for independent e-values is one. -/
theorem isPreciseIEMerging_tsum_mul (hw : ∑' j, w j = 1) (hF : ∀ j, IsPreciseIEMerging (F j)) :
    IsPreciseIEMerging fun e ↦ ∑' j, w j * F j e := by
  refine ⟨isIEMerging_tsum_mul hw.le fun j ↦ (hF j).toIsIEMerging, fun μ _ hμ ↦ ?_⟩
  rw [lintegral_tsum fun j ↦ ((hF j).measurable.const_mul _).aemeasurable]
  simp_rw [lintegral_const_mul _ (hF _).measurable, (hF _).lintegral_eq_one μ hμ, mul_one, hw]

end Mixture

section UStatistic

variable {ι : Type*} [Fintype ι]

/-- The **U-statistic of order `n`** of the e-values `e` [VW21, Section 4]: the average, over the
subsets `s` of `n` coordinates, of the products `∏ i ∈ s, e i`, that is, the elementary symmetric
polynomial `MvPolynomial.esymm` of degree `n` evaluated at `e`, divided by the number of its
terms. It is `1` for `n = 0` (`uStatistic_zero`), the arithmetic mean for `n = 1`
(`uStatistic_one`) and the product of the e-values for `n = card ι` (`uStatistic_card`). -/
noncomputable def uStatistic (n : ℕ) (e : ι → ℝ≥0∞) : ℝ≥0∞ :=
  ((Fintype.card ι).choose n : ℝ≥0∞)⁻¹ * MvPolynomial.eval e (MvPolynomial.esymm ι ℝ≥0∞ n)

theorem uStatistic_apply (n : ℕ) (e : ι → ℝ≥0∞) :
    uStatistic n e =
      ((Fintype.card ι).choose n : ℝ≥0∞)⁻¹ * ∑ s ∈ Finset.univ.powersetCard n, ∏ i ∈ s, e i := by
  simp [uStatistic, MvPolynomial.esymm]

@[simp]
theorem uStatistic_zero (e : ι → ℝ≥0∞) : uStatistic 0 e = 1 := by
  simp [uStatistic_apply]

theorem uStatistic_one (e : ι → ℝ≥0∞) : uStatistic 1 e = (∑ i, e i) / Fintype.card ι := by
  simp only [uStatistic_apply, Nat.choose_one_right, Finset.powersetCard_one, Finset.sum_map,
    Function.Embedding.coeFn_mk, Finset.prod_singleton]
  rw [ENNReal.div_eq_inv_mul]

@[simp]
theorem uStatistic_card (e : ι → ℝ≥0∞) : uStatistic (Fintype.card ι) e = ∏ i, e i := by
  rw [uStatistic_apply, Nat.choose_self, ← Finset.card_univ, Finset.powersetCard_self]
  simp

@[fun_prop]
theorem measurable_uStatistic (n : ℕ) : Measurable (uStatistic (ι := ι) n) := by
  simp_rw [funext (uStatistic_apply n)]
  fun_prop

/-- The integral of a U-statistic against a product of probability measures is the average, over
the subsets `s` of `n` coordinates, of the products of the means of the coordinates in `s`. -/
theorem lintegral_uStatistic_pi (n : ℕ) (μ : ι → Measure ℝ≥0∞)
    [∀ i, IsProbabilityMeasure (μ i)] :
    ∫⁻ e, uStatistic n e ∂Measure.pi μ = ((Fintype.card ι).choose n : ℝ≥0∞)⁻¹ *
      ∑ s ∈ Finset.univ.powersetCard n, ∏ i ∈ s, ∫⁻ z, z ∂μ i := by
  classical
  simp_rw [uStatistic_apply]
  rw [lintegral_const_mul _ (by fun_prop), lintegral_finsetSum _ fun s _ ↦ by fun_prop]
  congr 1
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  -- The product over `s` is the product over all coordinates of `if i ∈ s then e i else 1`.
  have h := TauCeti.lintegral_fintype_prod_eq_prod μ (f := fun i x ↦ if i ∈ s then x else 1)
    fun i ↦ by fun_prop
  simp only [Finset.prod_ite_mem, Finset.univ_inter] at h
  rw [h]
  calc ∏ i, ∫⁻ y, (if i ∈ s then y else 1) ∂μ i = ∏ i, if i ∈ s then ∫⁻ z, z ∂μ i else 1 :=
        Finset.prod_congr rfl fun i _ ↦ by split_ifs <;> simp
    _ = ∏ i ∈ s, ∫⁻ z, z ∂μ i := by rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- **The U-statistics are merging functions for independent e-values** [VW21, Section 4]. -/
theorem isIEMerging_uStatistic (n : ℕ) : IsIEMerging (uStatistic (ι := ι) n) := by
  refine ⟨measurable_uStatistic n, fun μ _ hμ ↦ ?_⟩
  rw [lintegral_uStatistic_pi]
  calc ((Fintype.card ι).choose n : ℝ≥0∞)⁻¹ *
        ∑ s ∈ Finset.univ.powersetCard n, ∏ i ∈ s, ∫⁻ z, z ∂μ i ≤
      ((Fintype.card ι).choose n : ℝ≥0∞)⁻¹ * ∑ s ∈ Finset.univ.powersetCard n, 1 := by
        gcongr with s
        exact Finset.prod_le_one fun i _ ↦ hμ i
    _ ≤ 1 := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_one]
        exact ENNReal.inv_mul_le_one _

/-- **The U-statistics of order at most the number of e-values are precise merging functions for
independent e-values**. Above that order, the U-statistic is `0`. -/
theorem isPreciseIEMerging_uStatistic {n : ℕ} (hn : n ≤ Fintype.card ι) :
    IsPreciseIEMerging (uStatistic (ι := ι) n) := by
  refine ⟨isIEMerging_uStatistic n, fun μ _ hμ ↦ ?_⟩
  rw [lintegral_uStatistic_pi]
  simp only [hμ, Finset.prod_const_one, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, nsmul_one]
  exact ENNReal.inv_mul_cancel (by simpa using Nat.choose_pos hn |>.ne')
    (ENNReal.natCast_ne_top _)

/-- **The U-statistics of order at most the number of e-values are admissible merging functions
for independent e-values** [VW21, Section 4]. -/
theorem isAdmissibleIEMerging_uStatistic {n : ℕ} (hn : n ≤ Fintype.card ι) :
    IsAdmissibleIEMerging (uStatistic (ι := ι) n) :=
  (isPreciseIEMerging_uStatistic hn).isAdmissibleIEMerging

/-- **The product is a precise merging function for independent e-values**: its integral against
a product of laws with mean `1` is `1`. It is the U-statistic of order `card ι`. -/
theorem isPreciseIEMerging_prod : IsPreciseIEMerging fun e : ι → ℝ≥0∞ ↦ ∏ i, e i := by
  simpa only [← funext uStatistic_card] using isPreciseIEMerging_uStatistic (ι := ι) le_rfl

/-- **The product is an admissible merging function for independent e-values** [VW21,
Section 4]. -/
theorem isAdmissibleIEMerging_prod : IsAdmissibleIEMerging fun e : ι → ℝ≥0∞ ↦ ∏ i, e i :=
  isPreciseIEMerging_prod.isAdmissibleIEMerging

/-- **The mixtures of the U-statistics are admissible merging functions for independent
e-values** [VW21, Section 4]: for weights `w n`, `n ≤ card ι`, summing to `1`, the mixture
`∑ n, w n * uStatistic n e` is admissible. It includes the product, the arithmetic mean and the
constant `1`. -/
theorem isAdmissibleIEMerging_sum_mul_uStatistic {w : Fin (Fintype.card ι + 1) → ℝ≥0∞}
    (hw : ∑ n, w n = 1) :
    IsAdmissibleIEMerging fun e : ι → ℝ≥0∞ ↦ ∑ n, w n * uStatistic n e := by
  have h := isPreciseIEMerging_tsum_mul
    (F := fun (n : Fin (Fintype.card ι + 1)) ↦ uStatistic (ι := ι) n)
    (by rwa [tsum_fintype]) fun n ↦ isPreciseIEMerging_uStatistic (Nat.lt_succ_iff.1 n.2)
  simp only [tsum_fintype] at h
  exact h.isAdmissibleIEMerging

end UStatistic

end ProbabilityTheory
