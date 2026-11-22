/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Finiteness of `Mᵈᵐᵃ`, and the action of `DomMulAct.mk m` on functions

The type synonym `Mᵈᵐᵃ` of a finite type `M` is finite, with the same cardinality, and a sum over
`Mᵈᵐᵃ` is the sum over `M` through `DomMulAct.mk`. The action of `DomMulAct.mk m` on functions
`α → β` is precomposition by `(m • ·)`.

## Main statements

* `DomMulAct.mk_smul_apply`, `DomMulAct.mk_smul`: `(DomMulAct.mk m • f) a = f (m • a)`.
* `DomMulAct.instFintype`: `Mᵈᵐᵃ` is finite when `M` is.
* `Fintype.card_domMulAct`: `Fintype.card Mᵈᵐᵃ = Fintype.card M`.
* `Fintype.sum_domMulAct`: `∑ c : Mᵈᵐᵃ, f c = ∑ m : M, f (DomMulAct.mk m)`.
-/

@[expose] public section

variable {M : Type*}

namespace DomMulAct

section SMul

variable {α β : Type*} [SMul M α]

/-- The action of `DomMulAct.mk m` on a function is precomposition by `(m • ·)`. -/
@[to_additive (attr := simp) /-- The action of `DomAddAct.mk m` on a function is precomposition
by `(m +ᵥ ·)`. -/]
theorem mk_smul_apply (m : M) (f : α → β) (a : α) : (mk m • f) a = f (m • a) := by
  rw [smul_apply, Equiv.symm_apply_apply]

/-- The action of `DomMulAct.mk m` on a function is precomposition by `(m • ·)`. -/
@[to_additive /-- The action of `DomAddAct.mk m` on a function is precomposition by
`(m +ᵥ ·)`. -/]
theorem mk_smul (m : M) (f : α → β) : mk m • f = fun a ↦ f (m • a) :=
  funext (mk_smul_apply m f)

end SMul

/-- `Mᵈᵐᵃ` is finite when `M` is. -/
@[to_additive /-- `Mᵈᵃᵃ` is finite when `M` is. -/]
instance instFintype [Fintype M] : Fintype Mᵈᵐᵃ := .ofEquiv M mk

end DomMulAct

namespace Fintype

variable [Fintype M]

/-- `Mᵈᵐᵃ` has as many elements as `M`. -/
@[to_additive (attr := simp) /-- `Mᵈᵃᵃ` has as many elements as `M`. -/]
theorem card_domMulAct : card Mᵈᵐᵃ = card M :=
  card_congr DomMulAct.mk.symm

/-- A sum over `Mᵈᵐᵃ` is the sum over `M` through `DomMulAct.mk`. -/
theorem sum_domMulAct {β : Type*} [AddCommMonoid β] (f : Mᵈᵐᵃ → β) :
    ∑ c, f c = ∑ m : M, f (DomMulAct.mk m) :=
  (sum_equiv DomMulAct.mk _ _ fun _ ↦ rfl).symm

end Fintype
