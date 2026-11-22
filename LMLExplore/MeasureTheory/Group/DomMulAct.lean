/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.DomAct.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Measurability of the action of `Mᵈᵐᵃ` on functions

If `M` acts on `ι`, then `Mᵈᵐᵃ` acts on `ι → α` by precomposition,
`(DomMulAct.mk m • f) i = f (m • i)`. Every such precomposition is measurable for the product
σ-algebra.

## Main statements

* `DomMulAct.instMeasurableConstSMulPi`: the action of `Mᵈᵐᵃ` on `ι → α` is measurable.
-/

@[expose] public section

namespace DomMulAct

variable {M ι α : Type*} [MeasurableSpace α]

/-- Precomposition by the action of an element of `M` on the indices is measurable. -/
@[to_additive /-- Precomposition by the action of an element of `M` on the indices is
measurable. -/]
instance instMeasurableConstSMulPi [SMul M ι] : MeasurableConstSMul Mᵈᵐᵃ (ι → α) :=
  ⟨fun c ↦ .of_eval fun i ↦ measurable_pi_apply (mk.symm c • i)⟩

end DomMulAct
