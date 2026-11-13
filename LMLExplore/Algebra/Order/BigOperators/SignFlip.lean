/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
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
sign. If a quantity `g ε i` satisfies `h ε i ≤ g ε i + g ε' i` for each such pair, then, since
flipping the `i`-th sign is an involution of the sign patterns, the average of `∑ i, g ε i` over
the `2^d` patterns is at least half the least of the sums `∑ i, h ε i`, so some pattern attains
it. With a constant `h ε i = c`, the bound is `d c / 2`.

## Main statements

* `Fintype.exists_div_two_le_sum`: if `h ε i ≤ g ε i + g ε' i` whenever `ε'` is `ε` with the
  `i`-th sign flipped, and `c ≤ ∑ i, h ε i` for every `ε`, then `c / 2 ≤ ∑ i, g ε i` for some
  sign pattern `ε`.
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

/-- **Averaging over the sign patterns.** If `h ε i ≤ g ε i + g ε' i` whenever `ε'` is `ε` with
the `i`-th sign flipped, and `c ≤ ∑ i, h ε i` for every sign pattern `ε`, then some sign pattern
`ε` has `c / 2 ≤ ∑ i, g ε i`. -/
theorem exists_div_two_le_sum (g h : (ι → Bool) → ι → 𝕜) {c : 𝕜}
    (hg : ∀ ε i, h ε i ≤ g ε i + g (Function.update ε i (!ε i)) i) (hh : ∀ ε, c ≤ ∑ i, h ε i) :
    ∃ ε, c / 2 ≤ ∑ i, g ε i := by
  have hinv (i : ι) : Function.Involutive fun ε : ι → Bool ↦ Function.update ε i (!ε i) :=
    fun ε ↦ by
      simp only [Function.update_self, Bool.not_not, Function.update_idem, Function.update_eq_self]
  -- flipping the `i`-th sign permutes the sign patterns
  have hflip : ∑ ε, ∑ i, g (Function.update ε i (!ε i)) i = ∑ ε, ∑ i, g ε i := by
    rw [sum_comm, sum_comm (f := fun ε i ↦ g ε i)]
    exact sum_congr rfl fun i _ ↦ Fintype.sum_bijective _ (hinv i).bijective _ _ fun _ ↦ rfl
  have hsum : ∑ _ : ι → Bool, c / 2 ≤ ∑ ε, ∑ i, g ε i := by
    have h1 := sum_le_sum fun ε (_ : ε ∈ univ) ↦ (hh ε).trans (sum_le_sum fun i (_ : i ∈ univ) ↦
      hg ε i)
    simp_rw [sum_add_distrib] at h1
    rw [hflip, sum_const, card_univ, nsmul_eq_mul] at h1
    rw [sum_const, card_univ, nsmul_eq_mul]
    linarith
  obtain ⟨ε, -, hε⟩ := exists_le_of_sum_le univ_nonempty hsum
  exact ⟨ε, hε⟩

/-- **Averaging over the sign patterns.** If `c ≤ g ε i + g ε' i` whenever `ε'` is `ε` with the
`i`-th sign flipped, then some sign pattern `ε` has `d c / 2 ≤ ∑ i, g ε i`, with `d` the
cardinality of `ι`. -/
theorem exists_card_mul_div_two_le_sum (g : (ι → Bool) → ι → 𝕜) {c : 𝕜}
    (hg : ∀ ε i, c ≤ g ε i + g (Function.update ε i (!ε i)) i) :
    ∃ ε, Fintype.card ι * c / 2 ≤ ∑ i, g ε i :=
  exists_div_two_le_sum g (fun _ _ ↦ c) hg fun _ ↦ by
    rw [sum_const, card_univ, nsmul_eq_mul]

end Fintype
