/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Averaging over sign patterns

Lower bounds for linear bandits [LS, Theorems 24.1 and 24.2] compare, for each coordinate `i` of
a sign pattern `ε : ι → Bool`, the pattern `ε` with the pattern obtained by flipping its `i`-th
sign. If a quantity `g ε i` satisfies `c ≤ g ε i + g ε' i` for each such pair, then, since
flipping the `i`-th sign is an involution of the sign patterns, the average of `∑ i, g ε i` over
the `2^d` patterns is at least `d c / 2`, so some pattern attains it.

## Main statements

* `Fintype.exists_card_mul_div_two_le_sum`: if `c ≤ g ε i + g ε' i` whenever `ε'` is `ε` with
  the `i`-th sign flipped, then `d c / 2 ≤ ∑ i, g ε i` for some sign pattern `ε`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Theorems 24.1 and 24.2.
-/

public section

open Finset

namespace Fintype

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]

/-- **Averaging over the sign patterns.** If `c ≤ g ε i + g ε' i` whenever `ε'` is `ε` with the
`i`-th sign flipped, then some sign pattern `ε` has `d c / 2 ≤ ∑ i, g ε i`, with `d` the
cardinality of `ι`. -/
theorem exists_card_mul_div_two_le_sum (g : (ι → Bool) → ι → 𝕜) {c : 𝕜}
    (hg : ∀ ε i, c ≤ g ε i + g (Function.update ε i (!ε i)) i) :
    ∃ ε, Fintype.card ι * c / 2 ≤ ∑ i, g ε i := by
  have hinv (i : ι) : Function.Involutive fun ε : ι → Bool ↦ Function.update ε i (!ε i) :=
    fun ε ↦ by
      simp only [Function.update_self, Bool.not_not, Function.update_idem, Function.update_eq_self]
  have hflip (i : ι) : ∑ ε, g (Function.update ε i (!ε i)) i = ∑ ε, g ε i :=
    Fintype.sum_bijective _ (hinv i).bijective _ _ fun _ ↦ rfl
  have hi (i : ι) : (Fintype.card (ι → Bool) : 𝕜) * c / 2 ≤ ∑ ε, g ε i := by
    have := sum_le_sum fun ε (_ : ε ∈ univ) ↦ hg ε i
    rw [sum_add_distrib, hflip, sum_const, card_univ, nsmul_eq_mul] at this
    linarith
  have hsum : ∑ _ : ι → Bool, (Fintype.card ι : 𝕜) * c / 2 ≤ ∑ ε, ∑ i, g ε i := by
    rw [sum_comm]
    calc ∑ _ : ι → Bool, (Fintype.card ι : 𝕜) * c / 2
        = ∑ _ : ι, (Fintype.card (ι → Bool) : 𝕜) * c / 2 := by
          simp only [sum_const, card_univ, nsmul_eq_mul]
          ring
      _ ≤ ∑ i, ∑ ε, g ε i := sum_le_sum fun i _ ↦ hi i
  obtain ⟨ε, -, hε⟩ := exists_le_of_sum_le univ_nonempty hsum
  exact ⟨ε, hε⟩

end Fintype
