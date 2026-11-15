/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finitely many points detect the combinations vanishing on a set

Let `a i : 𝓧 → K`, for `i` in a finite type, be functions on a type `𝓧` with values in a field
`K`, and let `Y` be a set in `𝓧`. The vectors `(a i x)_i`, for `x ∈ Y`, span a finite-dimensional
subspace of `ι → K`, so finitely many of them already span it: a combination `∑ i, ρ i * a i`
vanishing at finitely many well chosen points of `Y` vanishes on `Y`.

In a linearly ordered field, two combinations, one at most the other on `Y`, whose sums over these
finitely many points are in the opposite order, are then equal on `Y`.

## Main statements

* `exists_finset_forall_sum_mul_eq_zero`: finitely many points of `Y` detect the combinations of
  the functions `a i` that vanish on `Y`.
* `forall_sum_mul_eq_of_forall_le_of_sum_le`: two combinations, one at most the other on `Y`, with
  sums over the detecting points in the opposite order, are equal on `Y`.
-/

public section

variable {𝓧 ι K : Type*} [Fintype ι] {a : ι → 𝓧 → K} {Y : Set 𝓧}

/-- Finitely many points of `Y` detect the combinations of the functions `a i` that vanish on
`Y`. -/
theorem exists_finset_forall_sum_mul_eq_zero [Field K] (a : ι → 𝓧 → K) (Y : Set 𝓧) :
    ∃ F : Finset 𝓧, ↑F ⊆ Y ∧ ∀ ρ : ι → K, (∀ x ∈ F, ∑ i, ρ i * a i x = 0) →
      ∀ x ∈ Y, ∑ i, ρ i * a i x = 0 := by
  classical
  set v : 𝓧 → ι → K := fun x i ↦ a i x
  obtain ⟨t, htY, -, hspan, -⟩ := Submodule.exists_finset_span_eq_linearIndepOn K (v '' Y)
  obtain ⟨F, hFY, rfl⟩ := Finset.subset_set_image_iff.1 htY
  refine ⟨F, hFY, fun ρ hρ x hx ↦ ?_⟩
  let ℓ : (ι → K) →ₗ[K] K := Fintype.linearCombination K ρ
  have hℓ : ∀ y, ℓ (v y) = ∑ i, ρ i * a i y := fun y ↦ by
    simp [ℓ, Fintype.linearCombination_apply, v, mul_comm]
  have hb : ↑(F.image v) ⊆ (LinearMap.ker ℓ : Set (ι → K)) := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
    simp [LinearMap.mem_ker, hℓ, hρ y hy]
  have h1 : v x ∈ Submodule.span K (↑(F.image v) : Set (ι → K)) :=
    hspan ▸ Submodule.subset_span ⟨x, hx, rfl⟩
  simpa [LinearMap.mem_ker, hℓ] using Submodule.span_le.2 hb h1

/-- If finitely many points `F ⊆ Y` detect the combinations of the functions `a i` that vanish on
`Y`, then two combinations, one at most the other on `Y`, whose sums over `F` are in the opposite
order, are equal on `Y`. -/
theorem forall_sum_mul_eq_of_forall_le_of_sum_le [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {F : Finset 𝓧} (hFY : ↑F ⊆ Y)
    (hF : ∀ ρ : ι → K, (∀ x ∈ F, ∑ i, ρ i * a i x = 0) → ∀ x ∈ Y, ∑ i, ρ i * a i x = 0)
    {ρ ρ' : ι → K} (hle : ∀ x ∈ Y, ∑ i, ρ i * a i x ≤ ∑ i, ρ' i * a i x)
    (hsum : ∑ x ∈ F, ∑ i, ρ' i * a i x ≤ ∑ x ∈ F, ∑ i, ρ i * a i x) :
    ∀ x ∈ Y, ∑ i, ρ i * a i x = ∑ i, ρ' i * a i x := by
  -- the nonnegative differences on `F` have a nonpositive sum, so they vanish on `F`
  have h0 : ∑ x ∈ F, (∑ i, ρ' i * a i x - ∑ i, ρ i * a i x) = 0 := by
    refine le_antisymm ?_ (Finset.sum_nonneg fun x hx ↦ sub_nonneg.2 (hle x (hFY hx)))
    rw [Finset.sum_sub_distrib]
    exact sub_nonpos.2 hsum
  have hF0 : ∀ x ∈ F, ∑ i, (ρ' i - ρ i) * a i x = 0 := fun x hx ↦ by
    simpa only [sub_mul, Finset.sum_sub_distrib] using (Finset.sum_eq_zero_iff_of_nonneg
      (fun y hy ↦ sub_nonneg.2 (hle y (hFY hy)))).1 h0 x hx
  intro x hx
  have := hF _ hF0 x hx
  simp only [sub_mul, Finset.sum_sub_distrib, sub_eq_zero] at this
  exact this.symm
