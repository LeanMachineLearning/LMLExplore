/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.ConstraintNull.Basic
public import LMLExplore.EValues.EVariable

/-!
# The laws invariant under an involution, and their e-variables

For a measurable map `T` of a space `𝓧`, `ProbabilityTheory.invariantLaws T` is the set of the
probability measures `ν` on `𝓧` with `ν.map T = ν`. When `T` is an involution, such as the swap
`(x, y) ↦ (y, x)` of a pair of observations or the reflection `z ↦ -z`, this is the null of
invariance testing [SR23, §5.2]: two-sample testing, since a product law `μ₁.prod μ₂` is invariant
under the swap exactly when `μ₁ = μ₂` (`ProbabilityTheory.prod_mem_invariantLaws_swap_iff`), and
testing for symmetry about the origin.

Under an invariant law, `X` and `X ∘ T` have the same integral, so `X` has the integral of the
symmetrization `(X + X ∘ T) / 2`. Hence the e-variables for the invariant laws of an involution
are the measurable `X` with `X z + X (T z) ≤ 2` at every point, and the exact e-variables those
with `X z + X (T z) = 2` (`ProbabilityTheory.isEVar_invariantLaws_iff`,
`ProbabilityTheory.isExactEVar_invariantLaws_iff`); the converse directions test the invariant
laws `(δ z + δ (T z)) / 2`.

The exact e-variables include the bets on antisymmetric payoffs: for a measurable `v` with
`v (T z) = -v z` and `v ≥ -1`, the factor `1 + v` is an exact e-variable
(`ProbabilityTheory.isExactEVar_invariantLaws_ofReal_one_add`). The payoffs of [SR23] are
`v z = c * (g z - g (T z))` for a function `g` with values in `[-1/2, 1/2]` and a bet
`c ∈ [-1, 1]`.

The invariant laws are also a constraint null. A finite measure is invariant under `T` exactly
when every constraint `g - g ∘ T`, for a bounded measurable `g`, has integral zero
(`ProbabilityTheory.map_eq_iff_forall_integral_eq_zero`), so that the invariant laws are the
constraint null of these constraints `ProbabilityTheory.invarianceConstraints T`, a set closed
under negation (`ProbabilityTheory.invariantLaws_eq_constraintNull`). This holds for every
measurable `T`.

## Main definitions

* `ProbabilityTheory.invariantLaws T`: the probability measures invariant under `T`.
* `ProbabilityTheory.invarianceConstraints T`: the constraints `g - g ∘ T` of the bounded
  measurable functions `g`.

## Main statements

* `ProbabilityTheory.isEVar_invariantLaws_iff`, `ProbabilityTheory.isExactEVar_invariantLaws_iff`:
  for a measurable involution, the e-variables and the exact e-variables by the symmetrization.
* `ProbabilityTheory.isExactEVar_invariantLaws_ofReal_one_add`: bets on antisymmetric payoffs are
  exact e-variables.
* `ProbabilityTheory.map_eq_iff_forall_integral_eq_zero`,
  `ProbabilityTheory.invariantLaws_eq_constraintNull`: invariance through the constraints of
  invariance; the invariant laws are their constraint null.
* `ProbabilityTheory.prod_mem_invariantLaws_swap_iff`: the product laws invariant under the swap
  are those of two copies of one law.

## Implementation notes

The laws invariant under an involution `T ≠ id` are the invariant laws of the action of the group
`{id, T}` of order two, whose e-variables are described for every finite group by
`ProbabilityTheory.isEVar_invariantMeasures_iff_sum_le`. The statements here are proved directly:
`T` is a map rather than a group action, and the group it generates has order one when `T = id`.

## References

* [SR23] S. Shekhar and A. Ramdas, *Nonparametric two-sample testing by betting*, IEEE Trans. Inf.
  Theory 70 (2024), arXiv:2112.09162: §2 and §5.2.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 𝓨 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨] {T : 𝓧 → 𝓧} {ν : Measure 𝓧}
  {X : 𝓧 → ℝ≥0∞} {f : 𝓧 → ℝ}

/-! ### The invariant laws -/

/-- The **laws invariant under a map** `T`: the probability measures `ν` with `ν.map T = ν`. -/
def invariantLaws (T : 𝓧 → 𝓧) : Set (Measure 𝓧) :=
  {ν | IsProbabilityMeasure ν ∧ ν.map T = ν}

/-- Membership in the laws invariant under `T`. -/
theorem mem_invariantLaws_iff : ν ∈ invariantLaws T ↔ IsProbabilityMeasure ν ∧ ν.map T = ν :=
  Iff.rfl

/-- The laws invariant under `T` are probability measures. -/
theorem isProbabilityMeasure_of_mem_invariantLaws (hν : ν ∈ invariantLaws T) :
    IsProbabilityMeasure ν :=
  hν.1

/-- A law invariant under `T` is its own image under `T`. -/
theorem map_eq_of_mem_invariantLaws (hν : ν ∈ invariantLaws T) : ν.map T = ν :=
  hν.2

/-- Under a law invariant under a measurable `T`, the integral of `X + X ∘ T` is twice that of
`X`. -/
theorem lintegral_add_comp_of_mem_invariantLaws (hT : Measurable T) (hX : Measurable X)
    (hν : ν ∈ invariantLaws T) : ∫⁻ z, (X z + X (T z)) ∂ν = 2 * ∫⁻ z, X z ∂ν := by
  rw [lintegral_add_left hX, ← lintegral_map hX hT, map_eq_of_mem_invariantLaws hν, two_mul]

/-! ### E-variables for the invariant laws -/

/-- A measurable `X` with `X z + X (T z) ≤ 2` at every point is an e-variable for the laws
invariant under a measurable `T`. -/
theorem isEVar_invariantLaws_of_add_le (hT : Measurable T) (hX : Measurable X)
    (h : ∀ z, X z + X (T z) ≤ 2) : IsEVar X (invariantLaws T) := by
  refine ⟨hX, fun ν hν ↦ ?_⟩
  have := isProbabilityMeasure_of_mem_invariantLaws hν
  have h2 : 2 * ∫⁻ z, X z ∂ν ≤ 2 * 1 := by
    rw [← lintegral_add_comp_of_mem_invariantLaws hT hX hν, mul_one]
    calc ∫⁻ z, (X z + X (T z)) ∂ν ≤ ∫⁻ _, 2 ∂ν := lintegral_mono h
      _ = 2 := by simp
  exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 h2

/-- A measurable `X` with `X z + X (T z) = 2` at every point is an exact e-variable for the laws
invariant under a measurable `T`. -/
theorem isExactEVar_invariantLaws_of_add_eq (hT : Measurable T) (hX : Measurable X)
    (h : ∀ z, X z + X (T z) = 2) : IsExactEVar X (invariantLaws T) := by
  refine .of_lintegral_eq_one hX fun ν hν ↦ ?_
  have := isProbabilityMeasure_of_mem_invariantLaws hν
  have h2 : 2 * ∫⁻ z, X z ∂ν = 2 * 1 := by
    rw [← lintegral_add_comp_of_mem_invariantLaws hT hX hν, mul_one]
    simp [h]
  exact (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).1 h2

/-- For a measurable involution `T`, the uniform law on `{z, T z}` is invariant under `T`. -/
private lemma smul_dirac_add_dirac_mem_invariantLaws (hT : Measurable T)
    (hTT : Function.Involutive T) (z : 𝓧) :
    (2⁻¹ : ℝ≥0∞) • (Measure.dirac z + Measure.dirac (T z)) ∈ invariantLaws T := by
  refine ⟨⟨?_⟩, ?_⟩
  · simp [ENNReal.inv_two_add_inv_two]
  · rw [Measure.map_smul _ hT.aemeasurable, Measure.map_add _ _ hT, Measure.map_dirac' hT,
      Measure.map_dirac' hT, hTT z, add_comm]

/-- The integral of a measurable `X` under the uniform law on `{z, T z}`. -/
private lemma lintegral_smul_dirac_add_dirac (hX : Measurable X) (z : 𝓧) :
    ∫⁻ x, X x ∂((2⁻¹ : ℝ≥0∞) • (Measure.dirac z + Measure.dirac (T z))) =
      (X z + X (T z)) / 2 := by
  rw [lintegral_smul_measure, lintegral_add_measure, lintegral_dirac' _ hX, lintegral_dirac' _ hX,
    smul_eq_mul, ENNReal.div_eq_inv_mul]

/-- **The e-variables for the laws invariant under an involution**: for a measurable involution
`T`, a function is an e-variable for the laws invariant under `T` exactly when it is measurable
and `X z + X (T z) ≤ 2` at every point. -/
theorem isEVar_invariantLaws_iff (hT : Measurable T) (hTT : Function.Involutive T) :
    IsEVar X (invariantLaws T) ↔ Measurable X ∧ ∀ z, X z + X (T z) ≤ 2 := by
  refine ⟨fun hX ↦ ⟨hX.measurable, fun z ↦ ?_⟩, fun h ↦ isEVar_invariantLaws_of_add_le hT h.1 h.2⟩
  have h := hX.lintegral_le_one (smul_dirac_add_dirac_mem_invariantLaws hT hTT z)
  rwa [lintegral_smul_dirac_add_dirac hX.measurable,
    ENNReal.div_le_iff two_ne_zero ENNReal.ofNat_ne_top, one_mul] at h

/-- **The exact e-variables for the laws invariant under an involution**: for a measurable
involution `T`, a function is an exact e-variable for the laws invariant under `T` exactly when it
is measurable and `X z + X (T z) = 2` at every point. -/
theorem isExactEVar_invariantLaws_iff (hT : Measurable T) (hTT : Function.Involutive T) :
    IsExactEVar X (invariantLaws T) ↔ Measurable X ∧ ∀ z, X z + X (T z) = 2 := by
  refine ⟨fun hX ↦ ⟨hX.measurable, fun z ↦ ?_⟩,
    fun h ↦ isExactEVar_invariantLaws_of_add_eq hT h.1 h.2⟩
  have h := hX.lintegral_eq_one (smul_dirac_add_dirac_mem_invariantLaws hT hTT z)
  rwa [lintegral_smul_dirac_add_dirac hX.measurable,
    ENNReal.div_eq_one_iff two_ne_zero ENNReal.ofNat_ne_top] at h

/-- **Bets on antisymmetric payoffs are exact e-variables** [SR23, §2 and §5.2]. For a measurable
`T` and a measurable payoff `v` with `v (T z) = -v z` and `v ≥ -1`, the factor `1 + v` is an
exact e-variable for the laws invariant under `T`. With `v z = c * (g z - g (T z))` for an
involution `T`, a function `g` with values in `[-1/2, 1/2]` and `c ∈ [-1, 1]`, this is one round
of the tests of [SR23]. -/
theorem isExactEVar_invariantLaws_ofReal_one_add (hT : Measurable T) {v : 𝓧 → ℝ}
    (hv : Measurable v) (hv_anti : ∀ z, v (T z) = -v z) (hv_ge : ∀ z, -1 ≤ v z) :
    IsExactEVar (fun z ↦ ENNReal.ofReal (1 + v z)) (invariantLaws T) := by
  refine isExactEVar_invariantLaws_of_add_eq hT (by fun_prop) fun z ↦ ?_
  have h₁ : 0 ≤ 1 + v z := by linarith [hv_ge z]
  have h₂ : 0 ≤ 1 + v (T z) := by linarith [hv_ge (T z)]
  rw [← ENNReal.ofReal_add h₁ h₂, hv_anti, show 1 + v z + (1 + -v z) = 2 by ring]
  simp

/-! ### The invariant laws as a constraint null -/

/-- The **constraints of invariance under** `T`: the functions `g - g ∘ T` for the bounded
measurable `g : 𝓧 → ℝ`. -/
def invarianceConstraints (T : 𝓧 → 𝓧) : Set (𝓧 → ℝ) :=
  {f | ∃ g : 𝓧 → ℝ, Measurable g ∧ (∃ C, ∀ z, |g z| ≤ C) ∧ f = fun z ↦ g z - g (T z)}

/-- Membership in the constraints of invariance under `T`. -/
theorem mem_invarianceConstraints_iff : f ∈ invarianceConstraints T ↔
    ∃ g : 𝓧 → ℝ, Measurable g ∧ (∃ C, ∀ z, |g z| ≤ C) ∧ f = fun z ↦ g z - g (T z) :=
  Iff.rfl

/-- The constraints of invariance under a measurable `T` are measurable. -/
theorem measurable_of_mem_invarianceConstraints (hT : Measurable T)
    (hf : f ∈ invarianceConstraints T) : Measurable f := by
  obtain ⟨g, hg, -, rfl⟩ := hf
  exact hg.sub (hg.comp hT)

/-- The constraints of invariance under a measurable `T` are bounded. -/
theorem exists_abs_le_of_mem_invarianceConstraints (hf : f ∈ invarianceConstraints T) :
    ∃ C, ∀ z, |f z| ≤ C := by
  obtain ⟨g, -, ⟨C, hC⟩, rfl⟩ := hf
  exact ⟨C + C, fun z ↦ (abs_sub _ _).trans (add_le_add (hC z) (hC (T z)))⟩

/-- The constraints of invariance are closed under negation. -/
theorem neg_mem_invarianceConstraints (hf : f ∈ invarianceConstraints T) :
    -f ∈ invarianceConstraints T := by
  obtain ⟨g, hg, ⟨C, hC⟩, rfl⟩ := hf
  exact ⟨-g, hg.neg, ⟨C, fun z ↦ by simpa using hC z⟩, by ext z; simp; ring⟩

/-- Under a finite measure, the constraints of invariance under a measurable `T` are
integrable. -/
theorem integrable_of_mem_invarianceConstraints [IsFiniteMeasure ν] (hT : Measurable T)
    (hf : f ∈ invarianceConstraints T) : Integrable f ν := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_mem_invarianceConstraints hf
  exact .of_bound (measurable_of_mem_invarianceConstraints hT hf).aestronglyMeasurable C
    (ae_of_all _ hC)

/-- For a measurable set `t`, `1_t - 1_t ∘ T` is a constraint of invariance under `T`. -/
private lemma indicator_sub_indicator_comp_mem_invarianceConstraints {t : Set 𝓧}
    (ht : MeasurableSet t) :
    (fun z ↦ (t.indicator 1 z - t.indicator 1 (T z) : ℝ)) ∈ invarianceConstraints T :=
  ⟨t.indicator 1, measurable_one.indicator ht,
    ⟨1, fun z ↦ by by_cases hz : z ∈ t <;> simp [hz]⟩, rfl⟩

/-- Under a finite measure, the integral of the constraint `1_t - 1_t ∘ T` is
`ν t - ν (T ⁻¹' t)`. -/
private lemma integral_indicator_sub_indicator_comp [IsFiniteMeasure ν] (hT : Measurable T)
    {t : Set 𝓧} (ht : MeasurableSet t) :
    ∫ z, (t.indicator 1 z - t.indicator 1 (T z) : ℝ) ∂ν = ν.real t - ν.real (T ⁻¹' t) := by
  calc ∫ z, (t.indicator 1 z - t.indicator 1 (T z) : ℝ) ∂ν
      = ∫ z, (t.indicator (1 : 𝓧 → ℝ) z - (T ⁻¹' t).indicator 1 z) ∂ν := by
        refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
        by_cases hz : T z ∈ t <;> simp [hz]
    _ = ν.real t - ν.real (T ⁻¹' t) := by
        rw [integral_sub (f := t.indicator 1) (g := (T ⁻¹' t).indicator 1)
          ((integrable_const 1).indicator ht) ((integrable_const 1).indicator (hT ht)),
          integral_indicator_one ht, integral_indicator_one (hT ht)]

/-- **Invariance through the constraints.** A finite measure `ν` is invariant under a measurable
`T` exactly when every constraint `g - g ∘ T` of invariance, for a bounded measurable `g`, has
integral zero under `ν`. -/
theorem map_eq_iff_forall_integral_eq_zero [IsFiniteMeasure ν] (hT : Measurable T) :
    ν.map T = ν ↔ ∀ f ∈ invarianceConstraints T, ∫ z, f z ∂ν = 0 := by
  refine ⟨fun hν f hf ↦ ?_, fun h ↦ Measure.ext fun t ht ↦ ?_⟩
  · obtain ⟨g, hg, ⟨C, hC⟩, rfl⟩ := hf
    have hgi : Integrable g ν := .of_bound hg.aestronglyMeasurable C (ae_of_all _ hC)
    have hgTi : Integrable (fun z ↦ g (T z)) ν :=
      .of_bound (hg.comp hT).aestronglyMeasurable C (ae_of_all _ fun z ↦ hC (T z))
    rw [integral_sub hgi hgTi, ← integral_map hT.aemeasurable hg.aestronglyMeasurable, hν,
      sub_self]
  · have h₀ := h _ (indicator_sub_indicator_comp_mem_invarianceConstraints ht)
    rw [integral_indicator_sub_indicator_comp hT ht, sub_eq_zero] at h₀
    rw [Measure.map_apply hT ht]
    exact ((measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).1 h₀).symm

/-- **The invariant laws are a constraint null.** For a measurable `T`, the laws invariant under
`T` are the probability measures under which every constraint `g - g ∘ T` of invariance, for a
bounded measurable `g`, is integrable with a nonpositive integral; since the constraints are
closed under negation, their integrals are zero. -/
theorem invariantLaws_eq_constraintNull (hT : Measurable T) :
    invariantLaws T = constraintNull (invarianceConstraints T) := by
  ext ν
  refine ⟨fun hν ↦ ?_, fun hν ↦ ?_⟩
  · have := isProbabilityMeasure_of_mem_invariantLaws hν
    refine mem_constraintNull_iff.2 ⟨this, fun f hf ↦
      ⟨integrable_of_mem_invarianceConstraints hT hf, ((map_eq_iff_forall_integral_eq_zero hT).1
        (map_eq_of_mem_invariantLaws hν) f hf).le⟩⟩
  · obtain ⟨hprob, h⟩ := mem_constraintNull_iff.1 hν
    refine ⟨hprob, (map_eq_iff_forall_integral_eq_zero hT).2 fun f hf ↦ ?_⟩
    have h₂ := (h _ (neg_mem_invarianceConstraints hf)).2
    simp only [Pi.neg_apply, integral_neg, neg_nonpos] at h₂
    exact le_antisymm (h f hf).2 h₂

/-! ### Two-sample testing -/

/-- **The two-sample null** [SR23, (2)]. A product `μ₁.prod μ₂` of probability measures is
invariant under the swap `(x, y) ↦ (y, x)` exactly when `μ₁ = μ₂`. -/
theorem prod_mem_invariantLaws_swap_iff {μ₁ μ₂ : Measure 𝓨} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] : μ₁.prod μ₂ ∈ invariantLaws Prod.swap ↔ μ₁ = μ₂ := by
  rw [mem_invariantLaws_iff, Measure.prod_swap]
  refine ⟨fun ⟨_, h⟩ ↦ ?_, fun h ↦ ⟨inferInstance, h ▸ rfl⟩⟩
  simpa using (congrArg (Measure.map Prod.fst) h).symm

end ProbabilityTheory
