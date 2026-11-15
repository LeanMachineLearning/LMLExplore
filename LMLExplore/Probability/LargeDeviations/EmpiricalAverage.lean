/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.InformationTheory.KullbackLeibler.Cond
public import LMLExplore.InformationTheory.KullbackLeibler.Pi
public import Mathlib.Probability.Moments.Variance
public import Statlib.Divergence.KullbackLeibler.Basic
public import Statlib.ForMathlib.MeasureTheory.Integral.Pi

/-!
# Empirical averages of bounded functions under product laws

For finitely many bounded measurable functions `f i` on `𝓧` and `m` observations `x : Fin m → 𝓧`,
this file bounds the probability, under an i.i.d. law `P ^ m`, that the empirical averages
`(∑ j, f i (x j)) / m` lie within `ε` of given values `a i`, from both sides.

* From above, by a Sanov-type bound with blocks of length one: if every law whose integrals of
  the `f i` are within `ε` of the `a i` is at relative entropy at least `c` from `P`, the
  probability is at most `exp (- m c)`. This is Csiszár's argument for Sanov's upper bound on a
  convex set [Csi84]: condition `P ^ m` on the event, whose relative entropy to `P ^ m` is at most
  `log (1 / P ^ m (A))` (`InformationTheory.klDiv_cond_le`), and bound it from below by the
  superadditivity of the relative entropy over the coordinates
  (`InformationTheory.sum_klDiv_map_eval_le`) and its convexity, at the average of the marginals
  of the conditioned law, which is in the neighbourhood.
* From below, when the `a i` are the means of the `f i` under `P`, by the weak law of large
  numbers from Chebyshev's inequality.

## Main statements

* `ProbabilityTheory.ofReal_exp_mul_measure_pi_le_one`: the Sanov-type bound.
* `ProbabilityTheory.measure_pi_lt_abs_avg_sub_le`: the weak law of large numbers for a bounded
  function, `P ^ m (|avg - mean| > ε) ≤ C ^ 2 / (m ε ^ 2)`.
* `ProbabilityTheory.one_sub_div_le_measureReal_pi_forall_abs_avg_sub_le`: the weak law of large
  numbers for finitely many bounded functions at once.

## References

* [Csi84] I. Csiszár, *Sanov property, generalized I-projection and a conditional limit theorem*,
  Ann. Probab. 12 (1984), 768–793.
-/

public section

open MeasureTheory InformationTheory Filter
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- The tuples whose empirical averages of the measurable functions `f i` are within `ε` of the
`a i` form a measurable set. -/
lemma measurableSet_setOf_forall_abs_avg_sub_le {k : ℕ} {f : Fin k → 𝓧 → ℝ}
    (hf : ∀ i, Measurable (f i)) (a : Fin k → ℝ) (ε : ℝ) (m : ℕ) :
    MeasurableSet {x : Fin m → 𝓧 | ∀ i, |(∑ j, f i (x j)) / m - a i| ≤ ε} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ measurableSet_le (continuous_abs.measurable.comp
    (((Finset.measurable_sum _ fun j _ ↦ (hf i).comp (measurable_pi_apply j)).div_const _).sub_const
      _)) measurable_const

/-- The average of the marginals of a probability measure on `Fin m → 𝓧`, for `m ≠ 0`, is a
probability measure. -/
lemma isProbabilityMeasure_sum_smul_map_eval {m : ℕ} (hm : m ≠ 0) (μ : Measure (Fin m → 𝓧))
    [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (∑ j : Fin m, (((m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) • μ.map fun x ↦ x j) :=
  ⟨by simp [ENNReal.coe_inv (Nat.cast_ne_zero.2 hm : (m : ℝ≥0) ≠ 0),
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hm) (ENNReal.natCast_ne_top m)]⟩

/-- The integral against the average of the marginals of `μ` is the integral of the empirical
average against `μ`. -/
lemma integral_sum_smul_map_eval {m : ℕ} (μ : Measure (Fin m → 𝓧))
    [IsProbabilityMeasure μ] {g : 𝓧 → ℝ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C) :
    ∫ x, g x ∂(∑ j : Fin m, (((m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) • μ.map fun x ↦ x j) =
      ∫ x, (∑ j, g (x j)) / m ∂μ := by
  have hint (ν : Measure 𝓧) [IsFiniteMeasure ν] : Integrable g ν :=
    Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun x ↦ hgC x)
  rw [integral_finsetSum_measure fun j _ ↦ (hint _).smul_measure ENNReal.coe_ne_top]
  have hj (j : Fin m) : ∫ x, g x ∂(μ.map fun x ↦ x j) = ∫ x, g (x j) ∂μ :=
    integral_map (measurable_pi_apply j).aemeasurable hg.aestronglyMeasurable
  simp_rw [integral_smul_measure, hj]
  have hs : ∫ x, ∑ j, g (x j) ∂μ = ∑ j, ∫ x, g (x j) ∂μ :=
    integral_finsetSum _ fun j _ ↦ Integrable.of_bound
      (hg.comp (measurable_pi_apply j)).aestronglyMeasurable C (Eventually.of_forall fun x ↦ hgC _)
  rw [integral_div, hs]
  simp [div_eq_inv_mul, Finset.mul_sum]

/-- If the empirical average of a bounded measurable function `g` is almost surely within `ε` of
`a` under `μ`, then so is the integral of `g` against the average of the marginals of `μ`. -/
lemma abs_integral_sum_smul_map_eval_sub_le {m : ℕ} (μ : Measure (Fin m → 𝓧))
    [IsProbabilityMeasure μ] {g : 𝓧 → ℝ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C)
    {a ε : ℝ} (hμ : ∀ᵐ x ∂μ, |(∑ j, g (x j)) / m - a| ≤ ε) :
    |∫ x, g x ∂(∑ j : Fin m, (((m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) • μ.map fun x ↦ x j) - a| ≤ ε := by
  rw [integral_sum_smul_map_eval μ hg hgC]
  have hint : Integrable (fun x : Fin m → 𝓧 ↦ (∑ j, g (x j)) / m) μ :=
    ((integrable_finsetSum _ fun j _ ↦ Integrable.of_bound
      (hg.comp (measurable_pi_apply j)).aestronglyMeasurable C
      (Eventually.of_forall fun x ↦ hgC _))).div_const _
  have heq : ∫ x, (∑ j, g (x j)) / m ∂μ - a = ∫ x, ((∑ j, g (x j)) / m - a) ∂μ := by
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [heq, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ε) ?_).trans (by simp)
  simpa only [Real.norm_eq_abs] using hμ

/-- **Sanov-type bound** [Csi84]. If every law `R` whose integrals of the bounded functions `f i`
are within `ε` of `a i` is at relative entropy at least `c ≥ 0` from `P`, then the probability
under `P ^ m` that the empirical averages of the `f i` are within `ε` of the `a i` is at most
`exp (- m c)`. -/
lemma ofReal_exp_mul_measure_pi_le_one {k : ℕ} {f : Fin k → 𝓧 → ℝ} (hf : ∀ i, Measurable (f i))
    {C : Fin k → ℝ} (hfC : ∀ i x, |f i x| ≤ C i) {a : Fin k → ℝ} {ε c : ℝ} (hc : 0 ≤ c)
    {P : Measure 𝓧} [IsProbabilityMeasure P]
    (hU : ∀ R : Measure 𝓧, IsProbabilityMeasure R → (∀ i, |∫ x, f i x ∂R - a i| ≤ ε) →
      ENNReal.ofReal c ≤ klDiv R P) {m : ℕ} (hm : m ≠ 0) :
    ENNReal.ofReal (Real.exp (m * c)) *
      (Measure.pi fun _ : Fin m ↦ P) {x | ∀ i, |(∑ j, f i (x j)) / m - a i| ≤ ε} ≤ 1 := by
  set A := {x : Fin m → 𝓧 | ∀ i, |(∑ j, f i (x j)) / m - a i| ≤ ε}
  set Pm := Measure.pi fun _ : Fin m ↦ P
  have hA : MeasurableSet A := measurableSet_setOf_forall_abs_avg_sub_le hf a ε m
  rcases eq_or_ne (Pm A) 0 with h0 | h0
  · simp [h0]
  -- the law `μ` of `m` observations conditioned on the event, and the average `R` of its marginals
  set μ := Pm[|A]
  have : IsProbabilityMeasure μ := cond_isProbabilityMeasure h0
  have hm0 : (m : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hm
  set w : Fin m → ℝ≥0 := fun _ ↦ (m : ℝ≥0)⁻¹
  have hw : ∑ j, w j = 1 := by
    simp [w, Finset.card_univ, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm : (m : ℝ≥0) ≠ 0)]
  set R := ∑ j, (w j : ℝ≥0∞) • μ.map fun x ↦ x j
  have hR : IsProbabilityMeasure R := isProbabilityMeasure_sum_smul_map_eval hm μ
  have hRU (i : Fin k) : |∫ x, f i x ∂R - a i| ≤ ε := by
    refine abs_integral_sum_smul_map_eval_sub_le μ (hf i) (hfC i) ?_
    filter_upwards [ae_cond_mem hA] with x hx
    exact hx i
  -- `R` is in the neighbourhood, so by convexity and superadditivity over the coordinates the
  -- relative entropy from `μ` to `P ^ m` is at least `m c`
  have h1 : (m : ℝ≥0∞) * ENNReal.ofReal c ≤ klDiv μ Pm := by
    calc (m : ℝ≥0∞) * ENNReal.ofReal c
    _ ≤ m * klDiv R P := by gcongr; exact hU R hR hRU
    _ ≤ m * ∑ j, (w j : ℝ≥0∞) * klDiv (μ.map fun x ↦ x j) P := by
      gcongr
      exact klDiv_sum_smul_left_le hw
    _ = ∑ j, klDiv (μ.map fun x ↦ x j) P := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← mul_assoc, ENNReal.coe_inv (Nat.cast_ne_zero.2 hm : (m : ℝ≥0) ≠ 0),
        ENNReal.coe_natCast, ENNReal.mul_inv_cancel hm0 (ENNReal.natCast_ne_top m), one_mul]
    _ ≤ klDiv μ Pm := sum_klDiv_map_eval_le (fun _ ↦ P) μ
  -- the relative entropy from `μ` to `P ^ m` is at most `log (1 / P ^ m (A))`: take logarithms
  rw [← ENNReal.le_inv_iff_mul_le, ← ENNReal.log_le_log_iff,
    ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  calc ((m * c : ℝ) : EReal)
  _ = ((ENNReal.ofReal (m * c) : ℝ≥0∞) : EReal) := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left (by positivity)]
  _ = (((m : ℝ≥0∞) * ENNReal.ofReal c : ℝ≥0∞) : EReal) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  _ ≤ (klDiv μ Pm : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.2 h1
  _ ≤ ENNReal.log (Pm A)⁻¹ := klDiv_cond_le h0

/-- **Weak law of large numbers**, by Chebyshev's inequality: the probability that the empirical
average of a function bounded by `C` deviates by more than `ε` from its mean is at most
`C ^ 2 / (m ε ^ 2)`. -/
lemma measure_pi_lt_abs_avg_sub_le {g : 𝓧 → ℝ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C)
    (Q : Measure 𝓧) [IsProbabilityMeasure Q] {ε : ℝ} (hε : 0 < ε) {m : ℕ} (hm : m ≠ 0) :
    (Measure.pi fun _ : Fin m ↦ Q) {x | ε < |(∑ j, g (x j)) / m - ∫ y, g y ∂Q|} ≤
      ENNReal.ofReal (C ^ 2 / (m * ε ^ 2)) := by
  set Qm := Measure.pi fun _ : Fin m ↦ Q
  set X : (Fin m → 𝓧) → ℝ := fun x ↦ ∑ j, g (x j) with hX_def
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
  have hgL (j : Fin m) : MemLp (fun x : Fin m → 𝓧 ↦ g (x j)) 2 Qm :=
    MemLp.of_bound (hg.comp (measurable_pi_apply j)).aestronglyMeasurable C
      (Eventually.of_forall fun x ↦ hgC _)
  have hXL : MemLp X 2 Qm := memLp_finsetSum _ fun j _ ↦ hgL j
  have hEX : ∫ x, X x ∂Qm = m * ∫ y, g y ∂Q := by
    have hj (j : Fin m) : ∫ x, g (x j) ∂Qm = ∫ y, g y ∂Q := by
      rw [← integral_map (measurable_pi_apply j).aemeasurable hg.aestronglyMeasurable]
      congr 1
      exact (measurePreserving_eval (fun _ : Fin m ↦ Q) j).map_eq
    rw [integral_finsetSum _ fun j _ ↦ (hgL j).integrable one_le_two]
    simp [hj]
  have hVar : Var[X; Qm] ≤ m * C ^ 2 := by
    have h := variance_sum_pi (μ := fun _ : Fin m ↦ Q) (X := fun _ ↦ g)
      fun _ ↦ MemLp.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hgC)
    have hX : X = ∑ j : Fin m, fun x : Fin m → 𝓧 ↦ g (x j) := by
      ext x
      simp [X]
    rw [hX, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    gcongr
    have hb := variance_le_sq_of_bounded (μ := Q) (a := -C) (b := C)
      (Eventually.of_forall fun x ↦ abs_le.1 (hgC x)) hg.aemeasurable
    convert hb using 1
    ring
  calc Qm {x | ε < |(∑ j, g (x j)) / m - ∫ y, g y ∂Q|}
  _ ≤ Qm {x | m * ε ≤ |X x - ∫ x, X x ∂Qm|} := by
    refine measure_mono fun x hx ↦ ?_
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have h : (∑ j, g (x j)) / m - ∫ y, g y ∂Q = (X x - ∫ x, X x ∂Qm) / m := by
      rw [hEX, hX_def]
      field_simp
    rw [h, abs_div, abs_of_pos hm', lt_div_iff₀ hm'] at hx
    linarith
  _ ≤ ENNReal.ofReal (Var[X; Qm] / (m * ε) ^ 2) :=
    meas_ge_le_variance_div_sq hXL (by positivity)
  _ ≤ ENNReal.ofReal (C ^ 2 / (m * ε ^ 2)) := by
    refine ENNReal.ofReal_le_ofReal ?_
    calc Var[X; Qm] / (m * ε) ^ 2
    _ ≤ m * C ^ 2 / (m * ε) ^ 2 := by gcongr
    _ = C ^ 2 / (m * ε ^ 2) := by field_simp

/-- **Weak law of large numbers** for finitely many functions `f i` bounded by `C i`: with
probability at least `1 - (∑ i, C i ^ 2 / ε ^ 2) / m` under `Q ^ m`, the empirical averages of all
the `f i` are within `ε` of their means. -/
lemma one_sub_div_le_measureReal_pi_forall_abs_avg_sub_le {k : ℕ} {f : Fin k → 𝓧 → ℝ}
    (hf : ∀ i, Measurable (f i)) {C : Fin k → ℝ} (hfC : ∀ i x, |f i x| ≤ C i)
    (Q : Measure 𝓧) [IsProbabilityMeasure Q] {ε : ℝ} (hε : 0 < ε) {m : ℕ} (hm : m ≠ 0) :
    1 - (∑ i, C i ^ 2 / ε ^ 2) / m ≤
      (Measure.pi fun _ : Fin m ↦ Q).real
        {x | ∀ i, |(∑ j, f i (x j)) / m - ∫ y, f i y ∂Q| ≤ ε} := by
  set A := {x : Fin m → 𝓧 | ∀ i, |(∑ j, f i (x j)) / m - ∫ y, f i y ∂Q| ≤ ε}
  have hcompl : Aᶜ = ⋃ i, {x : Fin m → 𝓧 | ε < |(∑ j, f i (x j)) / m - ∫ y, f i y ∂Q|} := by
    ext x
    simp [A]
  have hle : (Measure.pi fun _ : Fin m ↦ Q) Aᶜ ≤
      ENNReal.ofReal ((∑ i, C i ^ 2 / ε ^ 2) / m) := by
    rw [hcompl]
    refine (measure_iUnion_fintype_le _ _).trans ?_
    calc ∑ i, (Measure.pi fun _ : Fin m ↦ Q)
          {x : Fin m → 𝓧 | ε < |(∑ j, f i (x j)) / m - ∫ y, f i y ∂Q|}
    _ ≤ ∑ i, ENNReal.ofReal (C i ^ 2 / (m * ε ^ 2)) :=
      Finset.sum_le_sum fun i _ ↦ measure_pi_lt_abs_avg_sub_le (hf i) (hfC i) Q hε hm
    _ = ENNReal.ofReal ((∑ i, C i ^ 2 / ε ^ 2) / m) := by
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by positivity]
      congr 1
      simp only [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      field_simp
  have h := ENNReal.toReal_le_of_le_ofReal (by positivity) hle
  rw [← measureReal_def, probReal_compl_eq_one_sub
    (measurableSet_setOf_forall_abs_avg_sub_le hf _ ε m)] at h
  linarith

end ProbabilityTheory
