/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Probability.UniformOn
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
import LMLExplore.Analysis.Normed.Group.AddCircle
import LMLExplore.MeasureTheory.Integral.BoundedMeasurable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Order.Group.Lattice
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# The uniform laws on the finite cosets of the circle

For `N > 0` and a point `x₀` of the circle `UnitAddCircle = ℝ / ℤ`, the coset
`x₀ + (1 / N) ℤ` is the finite set of the points `x₀ + j / N`, `j < N`, and the uniform law on it
is the average of the `N` Dirac masses at these points. Its integrals are the Riemann sums of the
circle: they depend only on the coset, they tend to the integral against Lebesgue measure
uniformly in `x₀` for a continuous function, and the map from a function to its coset averages
is a contraction of `L¹`.

## Main statements

* `UnitAddCircle.finite_coset`: the coset `x₀ + (1 / N) ℤ` is finite.
* `UnitAddCircle.uniformOn_coset`: for `N ≠ 0`, the uniform law on the coset is the average of
  the Dirac masses at the points `x₀ + j / N`, `j < N`.
* `UnitAddCircle.integral_uniformOn_coset`: the integral against it is the average of the values
  at these points.
* `UnitAddCircle.uniformOn_coset_add_intCast_div`: it depends only on the coset.
* `UnitAddCircle.exists_forall_abs_integral_uniformOn_coset_sub_le`: for a bounded continuous
  function, the coset averages tend to the integral against Lebesgue measure, uniformly in `x₀`.
* `UnitAddCircle.integral_abs_integral_uniformOn_coset_le`: the coset averages are a contraction
  of `L¹`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BoundedContinuousFunction

namespace UnitAddCircle

/-- The coset `x₀ + (1 / N) ℤ` of the circle is finite. -/
lemma finite_coset (x₀ : UnitAddCircle) (N : ℕ) :
    {x | x - x₀ ∈ AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)}.Finite := by
  have h : IsOfFinAddOrder (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle) := by
    rcases eq_or_ne N 0 with rfl | hN
    · simp
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, Nat.pos_of_ne_zero hN, ?_⟩
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN)]
    exact AddCircle.coe_period 1
  have := h.finite_zmultiples
  exact (Set.toFinite _).preimage (sub_left_injective.injOn)

/-- For `N ≠ 0`, the uniform law on the coset `x₀ + (1 / N) ℤ` of the circle is the average of
the Dirac masses at the points `x₀ + j / N`, `j < N`: these points are distinct and form the
coset. -/
theorem uniformOn_coset (x₀ : UnitAddCircle) {N : ℕ} (hN : N ≠ 0) :
    uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} =
      (N : ℝ≥0∞)⁻¹ • ∑ j ∈ Finset.range N,
        Measure.dirac (x₀ + (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)) := by
  classical
  set f : ℕ → UnitAddCircle := fun j ↦ x₀ + (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle) with hf
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
  -- the points `x₀ + j / N`, `j < N`, are distinct
  have hinj : Set.InjOn f (Finset.range N) := by
    intro j hj k hk h
    have hmem (i : ℕ) (hi : i ∈ (Finset.range N : Set ℕ)) :
        (i : ℝ) / N ∈ Set.Ico (0 : ℝ) (0 + 1) :=
      ⟨by positivity, by rw [zero_add, div_lt_one hN']; exact_mod_cast Finset.mem_range.1 hi⟩
    have h' := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem j hj) (hmem k hk)).1 (add_left_cancel h)
    exact_mod_cast (div_left_inj₀ hN'.ne').1 h'
  -- and they form the coset
  have hset : {x | x - x₀ ∈ AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} =
      ↑((Finset.range N).image f) := by
    ext x
    simp only [Set.mem_ofPred_eq, AddSubgroup.mem_zmultiples_iff, Finset.coe_image,
      Finset.coe_range, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨k, hk⟩
      have hr := Int.emod_nonneg k (Int.natCast_ne_zero.2 hN)
      have hrN := Int.emod_lt_of_pos k (Int.natCast_pos.2 (Nat.pos_of_ne_zero hN))
      refine ⟨(k % N).toNat, by omega, ?_⟩
      rw [hf, ← eq_sub_iff_add_eq', ← hk, ← AddCircle.coe_zsmul, zsmul_eq_mul]
      have hj : (((k % N).toNat : ℕ) : ℝ) = k - N * ((k / N : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hr, Int.emod_def]
        push_cast
        ring
      have hk' : (k : ℝ) * (N : ℝ)⁻¹ = (((k % N).toNat : ℕ) : ℝ) / N + ((k / N : ℤ) : ℝ) := by
        rw [hj]
        field_simp
        ring
      rw [hk', AddCircle.coe_add, ((AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨k / N, by simp⟩ :
        (((k / N : ℤ) : ℝ) : UnitAddCircle) = 0), add_zero]
    · rintro ⟨j, -, rfl⟩
      refine ⟨j, ?_⟩
      rw [hf, add_sub_cancel_left, ← AddCircle.coe_zsmul, zsmul_eq_mul, div_eq_mul_inv,
        Int.cast_natCast]
  rw [hset]
  ext t ht
  rw [uniformOn, cond_apply (Finset.measurableSet _), Measure.count_apply_finset,
    Finset.card_image_of_injOn hinj, Finset.card_range, smul_apply, smul_eq_mul,
    _root_.sum_apply]
  congr 1
  have hT : ↑((Finset.range N).image f) ∩ t = (↑(((Finset.range N).image f).filter (· ∈ t)) :
      Set UnitAddCircle) := by
    ext
    simp
  rw [hT, Measure.count_apply_finset, Finset.card_filter, Nat.cast_sum, Finset.sum_image hinj]
  simp [hf, Measure.dirac_apply' _ ht, Set.indicator_apply]

/-- For `N ≠ 0`, the integral against the uniform law on the coset `x₀ + (1 / N) ℤ` of the circle
is the average of the values at the points `x₀ + j / N`, `j < N`. -/
theorem integral_uniformOn_coset (f : UnitAddCircle → ℝ) (x₀ : UnitAddCircle) {N : ℕ}
    (hN : N ≠ 0) :
    ∫ x, f x ∂uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} =
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, f (x₀ + (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)) := by
  rw [uniformOn_coset x₀ hN, integral_smul_measure, integral_finsetSum_measure
    fun j _ ↦ integrable_dirac eNorm_lt_top]
  simp [integral_dirac, ENNReal.toReal_inv, smul_eq_mul]

/-- The uniform law on a coset of the circle depends only on the coset: shifting the base point
by a multiple of `1 / N` does not change it. -/
theorem uniformOn_coset_add_intCast_div (x₀ : UnitAddCircle) (N : ℕ) (m : ℤ) :
    uniformOn {x | x - (x₀ + (((m : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)) ∈
      AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} =
    uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} := by
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  have hc : (((m : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle) ∈
      AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle) :=
    ⟨m, by beta_reduce; rw [← AddCircle.coe_zsmul, zsmul_eq_mul, div_eq_mul_inv]⟩
  rw [sub_add_eq_sub_sub, sub_eq_add_neg (x - x₀)]
  exact AddSubgroup.add_mem_cancel_right _ (neg_mem hc)

/-- **Uniform Riemann sums on the cosets of the circle.** For a bounded continuous function `h`
on the circle and `η > 0`, for every large `N` the average of `h` on every coset `x₀ + (1 / N) ℤ`
is within `η` of its integral against Lebesgue measure. -/
theorem exists_forall_abs_integral_uniformOn_coset_sub_le (h : UnitAddCircle →ᵇ ℝ) {η : ℝ}
    (hη : 0 < η) : ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → 0 < N → ∀ x₀,
      |∫ x, h x ∂uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples
        (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} - ∫ x, h x| ≤ η := by
  obtain ⟨δ, hδ, hδh⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous h.continuous) η hη
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / δ)
  refine ⟨N₀, fun N hN hN0 x₀ ↦ ?_⟩
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN0
  have hNδ : 1 / (2 * (N : ℝ)) < δ := by
    have h1 : 1 / δ < N := hN₀.trans_le (by exact_mod_cast hN)
    rw [div_lt_iff₀ hδ] at h1
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hint (c : UnitAddCircle) : Integrable (fun y ↦ h (y + c)) (volume : Measure UnitAddCircle) :=
    .of_bound (h.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable ‖h‖
      (.of_forall fun y ↦ h.norm_coe_le_norm _)
  -- the average over the base points of the coset averages is the integral
  have hTint : Integrable (fun y ↦ ∫ x, h x ∂uniformOn {x | x - y ∈ AddSubgroup.zmultiples
      (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)}) (volume : Measure UnitAddCircle) := by
    simp_rw [integral_uniformOn_coset _ _ hN0.ne']
    exact (integrable_finsetSum _ fun j _ ↦ hint _).const_mul _
  have hmean : ∫ y, (∫ x, h x ∂uniformOn {x | x - y ∈ AddSubgroup.zmultiples
      (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)}) = ∫ x, h x := by
    simp_rw [integral_uniformOn_coset _ _ hN0.ne']
    rw [integral_const_mul, integral_finsetSum _ fun j _ ↦ hint _]
    simp_rw [integral_add_right_eq_self (fun x ↦ h x)]
    simp [hN'.ne']
  -- two coset averages are within `η`
  have hpt (y : UnitAddCircle) :
      ‖∫ x, h x ∂uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} -
        ∫ x, h x ∂uniformOn {x | x - y ∈ AddSubgroup.zmultiples
          (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)}‖ ≤ η := by
    obtain ⟨m, hm⟩ := UnitAddCircle.exists_norm_add_intCast_div_sub_le y x₀ hN0
    rw [← uniformOn_coset_add_intCast_div y N m, integral_uniformOn_coset _ _ hN0.ne',
      integral_uniformOn_coset _ _ hN0.ne', ← mul_sub, ← Finset.sum_sub_distrib, Real.norm_eq_abs,
      abs_mul, abs_inv, Nat.abs_cast]
    calc (N : ℝ)⁻¹ * |∑ j ∈ Finset.range N,
          (h (x₀ + (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)) -
            h (y + (((m : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle) +
              (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)))|
    _ ≤ (N : ℝ)⁻¹ * ∑ _j ∈ Finset.range N, η := by
      gcongr
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      have hd : dist (x₀ + (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle))
          (y + (((m : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle) +
            (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)) < δ := by
        rw [dist_add_right, dist_comm, dist_eq_norm]
        exact hm.trans_lt hNδ
      have := hδh hd
      rw [Real.dist_eq] at this
      exact this.le
    _ = η := by
      simp [hN'.ne']
  rw [← hmean]
  calc |∫ x, h x ∂uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples
        (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} - ∫ y, (∫ x, h x ∂uniformOn {x | x - y ∈
          AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)})|
  _ = ‖∫ y, (∫ x, h x ∂uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples
        (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} - ∫ x, h x ∂uniformOn {x | x - y ∈
          AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)})‖ := by
    rw [integral_sub (integrable_const _) hTint, integral_const, probReal_univ, one_smul,
      Real.norm_eq_abs]
  _ ≤ η * (volume : Measure UnitAddCircle).real Set.univ :=
    norm_integral_le_of_norm_le_const (.of_forall hpt)
  _ = η := by rw [probReal_univ, mul_one]

/-- For `N ≠ 0`, the average of a bounded measurable function on the coset `x₀ + (1 / N) ℤ` of the
circle is an integrable function of the base point `x₀`. -/
theorem integrable_integral_uniformOn_coset {f : UnitAddCircle → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) {N : ℕ} (hN : N ≠ 0) :
    Integrable (fun x₀ ↦ ∫ x, f x ∂uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples
      (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)}) (volume : Measure UnitAddCircle) := by
  simp_rw [integral_uniformOn_coset _ _ hN]
  exact (integrable_finsetSum _ fun j _ ↦
    LMLExplore.integrable_of_abs_le (hf.comp (measurable_add_const _)) (fun y ↦ hC _) _).const_mul _

/-- **The coset averages are a contraction of `L¹`**: for `N ≠ 0` and a bounded measurable `f`,
the integral over the base points `x₀` of the absolute value of the average of `f` on the coset
`x₀ + (1 / N) ℤ` of the circle is at most the integral of `|f|`. -/
theorem integral_abs_integral_uniformOn_coset_le {f : UnitAddCircle → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) {N : ℕ} (hN : N ≠ 0) :
    ∫ x₀, |∫ x, f x ∂uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples
      (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)}| ≤ ∫ x, ‖f x‖ := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
  have hint (c : UnitAddCircle) :
      Integrable (fun y ↦ |f (y + c)|) (volume : Measure UnitAddCircle) :=
    LMLExplore.integrable_of_abs_le (hf.comp (measurable_add_const _)).abs
      (fun y ↦ by rw [abs_abs]; exact hC _) _
  calc ∫ x₀, |∫ x, f x ∂uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples
        (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)}|
  _ ≤ ∫ x₀, (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
      |f (x₀ + (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle))| := by
    refine integral_mono (integrable_integral_uniformOn_coset hf hC hN).abs
      ((integrable_finsetSum _ fun j _ ↦ hint _).const_mul _) fun x₀ ↦ ?_
    rw [integral_uniformOn_coset _ _ hN, abs_mul, abs_inv, Nat.abs_cast]
    gcongr
    exact Finset.abs_sum_le_sum_abs _ _
  _ = ∫ x, ‖f x‖ := by
    rw [integral_const_mul, integral_finsetSum _ fun j _ ↦ hint _]
    simp_rw [integral_add_right_eq_self (fun x ↦ |f x|)]
    simp [hN'.ne', Real.norm_eq_abs]

end UnitAddCircle
