/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Products over a type with two elements

When the only elements of a finite type are `a ≠ b`, a product over the type is `f a * f b`, and a
sum is `f a + f b`. This is `Finset.prod_eq_mul` with its side conditions discharged.

## Main statements

* `Fintype.prod_eq_mul_of_forall_eq_or_eq`, `Fintype.sum_eq_add_of_forall_eq_or_eq`: a product
  (sum) over a type whose only elements are `a ≠ b` is `f a * f b` (`f a + f b`).
-/

public section

variable {ι M : Type*} [Fintype ι] [CommMonoid M] {a b : ι}

/-- A product over a type whose only elements are `a ≠ b` is `f a * f b`. -/
@[to_additive /-- A sum over a type whose only elements are `a ≠ b` is `f a + f b`. -/]
theorem Fintype.prod_eq_mul_of_forall_eq_or_eq (hab : a ≠ b) (h : ∀ c, c = a ∨ c = b)
    (f : ι → M) : ∏ c, f c = f a * f b :=
  Finset.prod_eq_mul a b hab (fun c _ hc ↦ absurd (h c) (not_or.2 hc))
    (fun ha ↦ absurd (Finset.mem_univ a) ha) fun hb ↦ absurd (Finset.mem_univ b) hb
