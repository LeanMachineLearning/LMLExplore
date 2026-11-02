/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Order.Basic

/-!
# Maximal values of functions

Two criteria for a function `f` into a preorder to be maximal at `a`: when the only elements of
the domain are `a` and `b` and `f b ≤ f a`, or when `f b < f a` for every `b ≠ a`.

## Main statements

* `apply_le_of_forall_eq_or_eq`: if the only elements are `a` and `b` and `f b ≤ f a`, then
  `f c ≤ f a` for every `c`.
* `apply_le_of_forall_ne_lt`: if `f b < f a` for every `b ≠ a`, then `f c ≤ f a` for every `c`.
-/

public section

variable {ι β : Type*} [Preorder β] {a b : ι} {f : ι → β}

/-- On a type whose only elements are `a` and `b`, a function `f` with `f b ≤ f a` is maximal at
`a`. -/
theorem apply_le_of_forall_eq_or_eq (h : ∀ c, c = a ∨ c = b) (hf : f b ≤ f a) (c : ι) :
    f c ≤ f a := by
  rcases h c with rfl | rfl
  exacts [le_rfl, hf]

/-- A function `f` with `f b < f a` for every `b ≠ a` is maximal at `a`. -/
theorem apply_le_of_forall_ne_lt (hf : ∀ b ≠ a, f b < f a) (c : ι) : f c ≤ f a := by
  rcases eq_or_ne c a with rfl | hc
  exacts [le_rfl, (hf c hc).le]
