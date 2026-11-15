/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Symmetric.Range

/-!
# Moore–Penrose inverses: range projections, and symmetric and positive operators

Tau Ceti's `LinearMap.moorePenroseInverse A`, written `A⁺`, is the Moore–Penrose inverse of a
linear map between finite-dimensional inner product spaces. This file adds the facts that let it
replace the inverse in weighted norms `‖v‖²_{V⁺} = ⟪v, V⁺ v⟫` when the operator `V` may be
singular, as for the Gram operator of unregularized least squares or of a design:

* for every Moore–Penrose pair `(A, B)`, the composition `A B` is the orthogonal projection onto
  the range of `A`;
* the Moore–Penrose inverse of an invertible operator is its inverse;
* if an operator acts on a subspace as an invertible operator of that subspace, its Moore–Penrose
  inverse acts there as the inverse of that restriction;
* the Moore–Penrose inverse of a symmetric operator `V` is symmetric, has the same range as `V`,
  and inverts `V` on that range; that of a positive operator is positive.

## Main statements

* `LinearMap.IsMoorePenroseInverse.comp_eq_starProjection_range`: if `B` is a Moore–Penrose
  inverse of `A`, then `A B` is the orthogonal projection onto the range of `A`.
* `ContinuousLinearMap.moorePenroseInverse_eq_ringInverse`: `V⁺ = V⁻¹` for an invertible
  operator `V`.
* `ContinuousLinearMap.moorePenroseInverse_apply_coe_of_apply_coe_eq`: if a symmetric operator
  `T` on `E` acts on a subspace `K` as an invertible operator `T_K` on `K`, then `T⁺ c = T_K⁻¹ c`
  for `c ∈ K`, and `ContinuousLinearMap.inner_moorePenroseInverse_of_apply_coe_eq`:
  `⟪a, T⁺ c⟫ = ⟪a, T_K⁻¹ c⟫` for `a c ∈ K`; `ContinuousLinearMap.le_range_of_apply_coe_eq`: then
  `K` lies in the range of `T`.
* `LinearMap.IsSymmetric.moorePenroseInverse`, `LinearMap.IsPositive.moorePenroseInverse`: the
  Moore–Penrose inverse of a symmetric (positive) operator is symmetric (positive).
* `LinearMap.IsSymmetric.range_moorePenroseInverse`: `V⁺` and a symmetric `V` have the same
  range, and `LinearMap.IsSymmetric.moorePenroseInverse_apply_apply_of_mem_range`:
  `V⁺ (V v) = v` for `v` in that range.
* `LinearMap.IsPositive.re_inner_moorePenroseInverse_apply_pos`: for a positive `V`,
  `0 < re ⟪v, V⁺ v⟫` for every nonzero `v` in the range of `V`.

## References

* A. Ben-Israel, T. N. E. Greville, *Generalized Inverses: Theory and Applications*, 2nd ed.,
  CMS Books in Mathematics, Springer (2003), Chapter 1.
-/

public section

open Module InnerProductSpace
open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace IsMoorePenroseInverse

variable {A : E →ₗ[𝕜] F} {B : F →ₗ[𝕜] E}

/-- A Moore–Penrose inverse `B` of `A` inverts `A` on its range: `A (B y) = y` for `y` in the
range of `A`. -/
theorem apply_apply_of_mem_range (h : IsMoorePenroseInverse A B) {y : F} (hy : y ∈ range A) :
    A (B y) = y := by
  obtain ⟨x, rfl⟩ := hy
  exact h.apply_apply_apply x

/-- If `B` is a Moore–Penrose inverse of `A`, then `A B` and `A` have the same range. -/
theorem range_comp (h : IsMoorePenroseInverse A B) : range (A ∘ₗ B) = range A :=
  le_antisymm (range_comp_le_range B A) fun y hy ↦ ⟨y, h.apply_apply_of_mem_range hy⟩

/-- If `B` is a Moore–Penrose inverse of `A`, then `A B` is a symmetric projection. -/
theorem isSymmetricProjection_comp (h : IsMoorePenroseInverse A B) :
    (A ∘ₗ B).IsSymmetricProjection where
  isIdempotentElem := LinearMap.ext fun y ↦ h.apply_apply_apply (B y)
  isSymmetric := h.isSymmetric_comp

/-- If `B` is a Moore–Penrose inverse of `A`, then `A B` is the orthogonal projection onto the
range of `A`. Applied to the pair `(B, A)`, `B A` is the orthogonal projection onto the range
of `B`. -/
theorem comp_eq_starProjection_range (h : IsMoorePenroseInverse A B)
    [(range A).HasOrthogonalProjection] :
    A ∘ₗ B = ((range A).starProjection : F →ₗ[𝕜] F) :=
  (h.isSymmetricProjection_comp.ext_iff (Submodule.isSymmetricProjection_starProjection _)).2
    (by rw [h.range_comp, Submodule.range_starProjection])

end IsMoorePenroseInverse

variable [FiniteDimensional 𝕜 E]

/-- `A A⁺` is the orthogonal projection onto the range of `A`. -/
theorem comp_moorePenroseInverse [FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] F) :
    A ∘ₗ A.moorePenroseInverse = ((range A).starProjection : F →ₗ[𝕜] F) :=
  A.isMoorePenroseInverse_moorePenroseInverse.comp_eq_starProjection_range

variable {V : E →ₗ[𝕜] E}

/-- The Moore–Penrose inverse of a symmetric operator is symmetric. -/
theorem IsSymmetric.moorePenroseInverse (hV : V.IsSymmetric) :
    V.moorePenroseInverse.IsSymmetric := by
  rw [isSymmetric_iff_isSelfAdjoint, isSelfAdjoint_iff', ← moorePenroseInverse_adjoint,
    hV.adjoint_eq]

/-- The Moore–Penrose inverse of a symmetric operator `V` inverts `V` on its range:
`V⁺ (V v) = v` for `v` in the range of `V`. -/
theorem IsSymmetric.moorePenroseInverse_apply_apply_of_mem_range (hV : V.IsSymmetric)
    {v : E} (hv : v ∈ range V) : V.moorePenroseInverse (V v) = v := by
  have hVv : (range V).orthogonalProjectionOnto (V v) = hV.rangeEquiv ⟨v, hv⟩ :=
    Subtype.ext (by simp [Submodule.starProjection_eq_self_iff.2 (mem_range_self V v)])
  rw [hV.moorePenroseInverse_eq_rangeEquiv_symm_comp]
  simp [hVv]

/-- The Moore–Penrose inverse of a symmetric operator has the same range as the operator. -/
theorem IsSymmetric.range_moorePenroseInverse (hV : V.IsSymmetric) :
    range V.moorePenroseInverse = range V := by
  refine le_antisymm ?_ fun v hv ↦
    ⟨V v, hV.moorePenroseInverse_apply_apply_of_mem_range hv⟩
  rintro _ ⟨y, rfl⟩
  rw [hV.moorePenroseInverse_eq_rangeEquiv_symm_comp]
  exact Submodule.coe_mem _

/-- The Moore–Penrose inverse of a positive operator is positive. -/
theorem IsPositive.moorePenroseInverse (hV : V.IsPositive) :
    V.moorePenroseInverse.IsPositive := by
  have hsymm := hV.isSymmetric.moorePenroseInverse
  refine (isPositive_iff _).2 ⟨hsymm, fun y ↦ ?_⟩
  -- `⟪V⁺ y, y⟫ = ⟪V⁺ (V (V⁺ y)), y⟫ = ⟪V (V⁺ y), V⁺ y⟫`
  rw [← V.isMoorePenroseInverse_moorePenroseInverse.apply_apply_apply' y, hsymm]
  exact hV.inner_nonneg_left _

/-- For a positive operator `V`, the weighted norm `‖v‖²_{V⁺} = re ⟪v, V⁺ v⟫` is positive on
the nonzero vectors of the range of `V`. -/
theorem IsPositive.re_inner_moorePenroseInverse_apply_pos (hV : V.IsPositive) {v : E}
    (hv : v ∈ range V) (hv0 : v ≠ 0) : 0 < RCLike.re ⟪v, V.moorePenroseInverse v⟫_𝕜 := by
  rw [← hV.isSymmetric.moorePenroseInverse]
  exact hV.moorePenroseInverse.re_inner_pos_of_mem_range
    (hV.isSymmetric.range_moorePenroseInverse ▸ hv) hv0

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section Restrict

variable {K : Submodule 𝕜 E} {T : E →L[𝕜] E} {T_K : K →L[𝕜] K}

/-- If an operator `T` on `E` acts on a subspace `K` as an invertible operator `T_K` on `K`, then
`T` maps `T_K⁻¹ v` to `v` for `v ∈ K`. -/
theorem apply_coe_ringInverse_of_apply_coe_eq (hT : ∀ v : K, T v = T_K v) (hu : IsUnit T_K)
    (v : K) : T ↑(Ring.inverse T_K v) = v := by
  rw [hT, apply_ringInverse_apply hu]

/-- If an operator `T` on `E` acts on a subspace `K` as an invertible operator `T_K` on `K`, then
`K` lies in the range of `T`. -/
theorem le_range_of_apply_coe_eq (hT : ∀ v : K, T v = T_K v) (hu : IsUnit T_K) :
    K ≤ LinearMap.range (T : E →ₗ[𝕜] E) := fun v hv ↦
  ⟨_, apply_coe_ringInverse_of_apply_coe_eq hT hu ⟨v, hv⟩⟩

end Restrict

variable [FiniteDimensional 𝕜 E]

/-- The Moore–Penrose inverse of an invertible operator is its inverse: `V⁺ = V⁻¹`. -/
theorem moorePenroseInverse_eq_ringInverse {V : E →L[𝕜] E} (hV : IsUnit V) :
    (V : E →ₗ[𝕜] E).moorePenroseInverse = (Ring.inverse V : E →L[𝕜] E) :=
  ((LinearMap.isMoorePenroseInverse_iff_eq_moorePenroseInverse _).1
    (.of_comp_eq_id (LinearMap.ext (ringInverse_apply_apply hV))
      (LinearMap.ext (apply_ringInverse_apply hV)))).symm

/-- If a symmetric operator `T` on a finite-dimensional space `E` acts on a subspace `K` as an
invertible operator `T_K` on `K`, then the Moore–Penrose inverse of `T` acts on `K` as the inverse
of `T_K`: `T⁺ c = T_K⁻¹ c` for `c ∈ K`. -/
theorem moorePenroseInverse_apply_coe_of_apply_coe_eq {K : Submodule 𝕜 E} {T : E →L[𝕜] E}
    {T_K : K →L[𝕜] K} (hsym : (T : E →ₗ[𝕜] E).IsSymmetric) (hT : ∀ v : K, T v = T_K v)
    (hu : IsUnit T_K) (c : K) :
    (T : E →ₗ[𝕜] E).moorePenroseInverse c = Ring.inverse T_K c := by
  have h := hsym.moorePenroseInverse_apply_apply_of_mem_range
    (le_range_of_apply_coe_eq hT hu (Ring.inverse T_K c).2)
  rwa [coe_coe, apply_coe_ringInverse_of_apply_coe_eq hT hu] at h

/-- If a symmetric operator `T` on a finite-dimensional space `E` acts on a subspace `K` as an
invertible operator `T_K` on `K`, then `⟪a, T⁺ c⟫ = ⟪a, T_K⁻¹ c⟫` for `a c ∈ K`, the inner products
on the right being those of `K`. -/
theorem inner_moorePenroseInverse_of_apply_coe_eq {K : Submodule 𝕜 E} {T : E →L[𝕜] E}
    {T_K : K →L[𝕜] K} (hsym : (T : E →ₗ[𝕜] E).IsSymmetric) (hT : ∀ v : K, T v = T_K v)
    (hu : IsUnit T_K) (a c : K) :
    ⟪(a : E), (T : E →ₗ[𝕜] E).moorePenroseInverse c⟫_𝕜 = ⟪a, Ring.inverse T_K c⟫_𝕜 := by
  rw [moorePenroseInverse_apply_coe_of_apply_coe_eq hsym hT hu, Submodule.coe_inner]

end ContinuousLinearMap
