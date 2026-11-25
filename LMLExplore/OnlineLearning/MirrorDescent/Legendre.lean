/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Legendre.Basic
public import LMLExplore.OnlineLearning.MirrorDescent.Basic

/-!
# Mirror descent with a Legendre potential

For a Legendre potential `F` with domain `D`, mirror descent steps on a closed, convex, bounded set
`K ⊆ D` that meets the interior of `D` exist, and they lie in the interior of `D`, where `F` is
differentiable. This complements `LMLExplore.OnlineLearning.exists_isMirrorDescentStep`, which
needs `F` continuous on a compact `K`, and
`LMLExplore.OnlineLearning.exists_isMirrorDescentStep_of_strongConvexOn`, which needs `F`
strongly convex.

## Main statements

* `LMLExplore.IsLegendre.exists_isMirrorDescentStep_mem_interior`: in finite dimension, for a
  Legendre potential, every point, derivative, learning rate and loss have a mirror descent step on
  `K`, and every such step lies in the interior of the domain.
-/

public section

open Set

namespace LMLExplore.IsLegendre

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : E → ℝ} {D K : Set E}

/-- **Mirror descent steps for a Legendre potential.** In finite dimension, let `F` be Legendre
with domain `D`, and let `K ⊆ D` be closed, convex, bounded and meet the interior of `D`. Then
every point `a` and linear map `F'` have a mirror descent step on `K` from `a` with derivative
`F'`, for every learning rate `η` and loss `y`, and every such step lies in the interior of `D`. -/
theorem exists_isMirrorDescentStep_mem_interior (hF : IsLegendre F D) (hK : IsClosed K)
    (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K) (hKD : K ⊆ D)
    (hK_int : (K ∩ interior D).Nonempty) (η : ℝ) (y : E →L[ℝ] ℝ) (a : E) (F' : E →L[ℝ] ℝ) :
    ∃ x, OnlineLearning.IsMirrorDescentStep K F η y a F' x ∧ x ∈ interior D := by
  have hKD' : K ∩ D = K := inter_eq_left.2 hKD
  obtain ⟨x₀, hx₀⟩ := hK_int
  -- the step is a Bregman projection for the Legendre function `D_F(·, a)` with a shifted slope
  obtain ⟨z, ⟨hz, hzmin⟩, -⟩ :=
    (hF.bregDiv a (F' - η • y)).existsUnique_isMinOn_inter_of_isBounded hK hKc hx₀
      (hKb.subset fun x hx ↦ hx.1.1)
  have h_int := hF.mem_interior_of_isMinOn_bregDiv hKc ⟨x₀, hx₀⟩ hz hzmin
  rw [hKD'] at hz hzmin
  exact ⟨z, (OnlineLearning.isMirrorDescentStep_iff_isMinOn_bregDiv rfl a a z).2 ⟨hz, hzmin⟩,
    h_int⟩

end LMLExplore.IsLegendre
