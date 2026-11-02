/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# The pointwise order on `ℓ^p`

When every `E i` is partially ordered, `lp E p` carries the pointwise order: `f ≤ g` if and only
if `f i ≤ g i` for every `i`. It is compatible with addition and with scalar multiplication by
nonnegative scalars. On `ℓ^∞(α, ℝ)` and its subspaces this is the order for which operators on
bounded functions, such as the action of a Markov kernel or the Bellman operators of dynamic
programming, are monotone.

## Main definitions

* `lp.instPartialOrder`: the pointwise partial order on `lp E p`.

## Main statements

* `lp.coeFn_le_coeFn`, `lp.le_def`: the order on `lp E p` is the pointwise order.
* `lp.instIsOrderedAddMonoid`, `lp.instPosSMulMono`: the order is compatible with addition and
  with multiplication by nonnegative scalars.
-/

public section

namespace lp

variable {α : Type*} {E : α → Type*} [∀ i, NormedAddCommGroup (E i)] {p : ENNReal}

section PartialOrder

variable [∀ i, PartialOrder (E i)]

/-- The pointwise partial order on `lp E p`. -/
instance instPartialOrder : PartialOrder (lp E p) :=
  PartialOrder.lift (fun f ↦ ⇑f) fun _ _ ↦ lp.ext

@[simp, norm_cast]
theorem coeFn_le_coeFn {f g : lp E p} : ⇑f ≤ ⇑g ↔ f ≤ g :=
  Iff.rfl

theorem le_def {f g : lp E p} : f ≤ g ↔ ∀ i, f i ≤ g i :=
  Iff.rfl

@[simp, norm_cast]
theorem coeFn_lt_coeFn {f g : lp E p} : ⇑f < ⇑g ↔ f < g :=
  Iff.rfl

instance instIsOrderedAddMonoid [∀ i, IsOrderedAddMonoid (E i)] : IsOrderedAddMonoid (lp E p) where
  add_le_add_left _ _ h c i := by simpa using add_le_add_left (h i) (c i)

instance instPosSMulMono {𝕜 : Type*} [NormedRing 𝕜] [Preorder 𝕜] [∀ i, Module 𝕜 (E i)]
    [∀ i, IsBoundedSMul 𝕜 (E i)] [∀ i, PosSMulMono 𝕜 (E i)] : PosSMulMono 𝕜 (lp E p) where
  smul_le_smul_of_nonneg_left _ hc _ _ h i := by
    simpa using smul_le_smul_of_nonneg_left (h i) hc

end PartialOrder

end lp
