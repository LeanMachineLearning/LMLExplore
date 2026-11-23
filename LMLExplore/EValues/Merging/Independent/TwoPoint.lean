/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Merging.Independent
public import Mathlib.Probability.Distributions.Bernoulli
import LMLExplore.Probability.Distributions.Bernoulli
import LMLExplore.Probability.ProductMeasure

/-!
# Merging functions for independent e-values: two-point laws

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

As a consequence of laws on two points, every merging function for independent e-values is at
most `∏ i, max 1 (e i)` at every point `e`, so the product weakly dominates it: the product is at
least the merging function on `[1, ∞]ᴷ` [VW21, Proposition 4.2]. The admissibility of the precise
merging functions [VW21, Proposition 4.1] is in `LMLExplore.EValues.Merging.Independent`.

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

## Implementation notes

For one e-value, the laws on two points with mean `1`, together with the point masses at `x ≤ 1`,
bound the slopes of `g` on both sides of `1`, and the supremum of the slopes on the right is the
weight `w`. For several e-values, integrating `F` against the laws of all coordinates but one
leaves a function of one e-value, to which this applies, by induction on the set of coordinates
whose law is arbitrary (`MeasureTheory.Measure.lintegral_infinitePi_update`, through
`MeasureTheory.Measure.infinitePi_eq_pi`). This replaces the
decomposition of a law with finite mean into a mixture of laws on two points with the same mean
used in [VW24].

## References

* [VW21] V. Vovk and R. Wang, *E-values: calibration, combination and applications*, Ann. Statist.
  49 (2021), arXiv:1912.06116v4: Section 4 (Proposition 4.2).
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
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at h_real
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal, hw0.le, hw1.le, ENNReal.toReal_one]
    at h_real
  rw [hw] at h_real
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
    replace hb := Set.mem_Ioi.1 hb
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
    · have h := (le_csSup hA_bdd (Set.mem_image_of_mem _ (Set.mem_Ioi.2 hx))).trans
        (le_max_left _ 0)
      rw [div_le_iff₀ (by linarith)] at h
      linarith
  refine ⟨Real.toNNReal (1 - w), Real.toNNReal w, ?_, fun e ↦ ?_⟩
  · rw [← Real.toNNReal_add (by linarith) hw0, sub_add_cancel, Real.toNNReal_one]
  · calc g e = ENNReal.ofReal (G e) := by
          simp only [G, ENNReal.ofReal_coe_nnreal]
          exact (ENNReal.ofReal_toReal (by simpa using hg_top _ e.property)).symm
      _ ≤ ENNReal.ofReal ((1 - w) + w * e) := ENNReal.ofReal_le_ofReal (hG_lin e e.property)
      _ = _ := by
        rw [ENNReal.ofReal_add (by linarith) (by positivity), ENNReal.ofReal_mul hw0,
          ENNReal.ofReal_coe_nnreal, ENNReal.ofNNReal_toNNReal, ENNReal.ofNNReal_toNNReal]

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
    have hupd (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν] :
        ∀ j, IsProbabilityMeasure (Function.update μ i ν j) :=
      (Function.forall_update_iff μ fun _ m ↦ IsProbabilityMeasure m).2 ⟨‹_›, fun j _ ↦ hμ j⟩
    have heq (ν : Measure ℝ≥0∞) [IsProbabilityMeasure ν] :
        ∫⁻ e, F e ∂Measure.pi (Function.update μ i ν) =
          ∫⁻ z, ∫⁻ e, F (Function.update e i z) ∂Measure.pi μ ∂ν := by
      have := hμ
      have := hupd ν
      rw [← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
      exact Measure.lintegral_infinitePi_update μ i ν hF
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

end ProbabilityTheory
