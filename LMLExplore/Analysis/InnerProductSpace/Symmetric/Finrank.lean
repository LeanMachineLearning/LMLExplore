/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.Matrix.Hermitian

/-!
# The dimension of the space of symmetric operators

The symmetric operators on a real inner product space of dimension `d` form a subspace of
dimension `d (d + 1) / 2`: in an orthonormal basis they are the symmetric matrices. Bounding the
size of a linearly independent family of symmetric operators by this dimension bounds the
support of optimal designs, whose design operators are convex combinations of the symmetric
rank-one operators `a ⊗ a`.

## Main statements

* `LinearIndependent.fintype_card_le_of_isSymmetric`: a linearly independent family of symmetric
  operators on a real inner product space of dimension `d` has at most `d (d + 1) / 2` members.
-/

public section

open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A linearly independent family of symmetric operators on a real inner product space of
dimension `d` has at most `d (d + 1) / 2` members, the dimension of the space of symmetric
`d × d` matrices (`TauCeti.finrank_symmetricMatrix`), which are their matrices in an orthonormal
basis. -/
theorem LinearIndependent.fintype_card_le_of_isSymmetric {ι : Type*} [Fintype ι]
    {f : ι → E →ₗ[ℝ] E} (hf : LinearIndependent ℝ f) (hsym : ∀ i, (f i).IsSymmetric) :
    Fintype.card ι ≤ finrank ℝ E * (finrank ℝ E + 1) / 2 := by
  set b := stdOrthonormalBasis ℝ E
  let M := LinearMap.toMatrix b.toBasis b.toBasis
  -- the matrices of the `f i` are linearly independent symmetric matrices
  let g : ι → selfAdjoint.submodule ℝ (Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ) :=
    fun i ↦ ⟨M (f i), ((LinearMap.isHermitian_toMatrix_iff b).2 (hsym i)).isSelfAdjoint⟩
  have hg : LinearIndependent ℝ g :=
    LinearIndependent.of_comp (Submodule.subtype _) (hf.map' M.toLinearMap M.ker)
  simpa [TauCeti.finrank_symmetricMatrix] using hg.fintype_card_le_finrank
