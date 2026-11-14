/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# The pointwise order on `ℓ^p`

When every `E i` is partially ordered, `lp E p` carries the pointwise order: `f ≤ g` if and only
if `f i ≤ g i` for every `i`. It is compatible with addition and with scalar multiplication by
nonnegative scalars, and for `1 ≤ p` it is closed for the topology of `lp E p`, when it is so on
every `E i`. On `ℓ^∞(α, ℝ)` and its subspaces this is the order for which operators on
bounded functions, such as the action of a Markov kernel or the Bellman operators of dynamic
programming, are monotone. Its closedness lets limits of iterates of such operators keep the
inequalities that the iterates satisfy: the comparison results of abstract dynamic programming
need it.

## Main definitions

* `lp.instPartialOrder`: the pointwise partial order on `lp E p`.

## Main statements

* `lp.coeFn_le_coeFn`, `lp.le_def`: the order on `lp E p` is the pointwise order.
* `lp.instIsOrderedAddMonoid`, `lp.instPosSMulMono`: the order is compatible with addition and
  with multiplication by nonnegative scalars.
* `lp.instOrderClosedTopology`: for `1 ≤ p`, the order on `lp E p` is closed. It is inherited by
  the subspaces of `lp E p`, such as the bounded measurable functions.
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

/-- The pointwise order on `lp E p` is compatible with addition. -/
instance instIsOrderedAddMonoid [∀ i, IsOrderedAddMonoid (E i)] : IsOrderedAddMonoid (lp E p) where
  add_le_add_left _ _ h c i := by simpa using add_le_add_left (h i) (c i)

/-- Multiplication by a nonnegative scalar is monotone for the pointwise order on `lp E p`, when it
is so on every `E i`. -/
instance instPosSMulMono {𝕜 : Type*} [NormedRing 𝕜] [Preorder 𝕜] [∀ i, Module 𝕜 (E i)]
    [∀ i, IsBoundedSMul 𝕜 (E i)] [∀ i, PosSMulMono 𝕜 (E i)] : PosSMulMono 𝕜 (lp E p) where
  smul_le_smul_of_nonneg_left _ hc _ _ h i := by
    simpa using smul_le_smul_of_nonneg_left (h i) hc

/-- For `1 ≤ p`, the pointwise order on `lp E p` is closed when it is so on every `E i`, since the
coercion of `lp E p` to the functions `∀ i, E i` is continuous. -/
instance instOrderClosedTopology [Fact (1 ≤ p)] [∀ i, OrderClosedTopology (E i)] :
    OrderClosedTopology (lp E p) where
  isClosed_le' := by
    have hc : Continuous fun f : lp E p ↦ ⇑f := uniformContinuous_coe.continuous
    simpa only [Function.comp_apply, coeFn_le_coeFn] using
      isClosed_le (hc.comp continuous_fst) (hc.comp continuous_snd)

end PartialOrder

end lp
