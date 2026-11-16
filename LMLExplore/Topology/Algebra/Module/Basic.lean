/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Topological closures of submodules

## Main statements

* `Submodule.sup_topologicalClosure_eq_top`: if `p ⊔ q` is the whole module, so is
  `p ⊔ closure q`.
-/

public section

namespace Submodule

variable {R M : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousConstSMul R M] [ContinuousAdd M] {p q : Submodule R M}

/-- If `p ⊔ q` is the whole module, so is `p ⊔ closure q`. -/
theorem sup_topologicalClosure_eq_top (h : p ⊔ q = ⊤) : p ⊔ q.topologicalClosure = ⊤ :=
  eq_top_mono (sup_le_sup_left q.le_topologicalClosure p) h

end Submodule
