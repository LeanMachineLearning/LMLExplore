/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Basic

/-!
# The probability simplex

The probability simplex `simplex α` of a finite type `α` is the set of vectors `w : α → ℝ` with
nonnegative entries summing to `1`: the probability distributions on `α`, as allocations of samples
to arms, mixed strategies, or weights of an online learner.

It is stated directly on `α → ℝ`, with the topology and the order of that space: Mathlib's set
`stdSimplex` is deprecated, and its replacement `Convexity.StdSimplex` is a type of finitely
supported distributions, not a subset of `α → ℝ`.

## Main definitions

* `LMLExplore.simplex α`: the vectors `w : α → ℝ` with nonnegative entries summing to `1`.

## Main statements

* `LMLExplore.mem_simplex_iff`: membership in the simplex.
* `LMLExplore.simplex_subset_nonneg`: the simplex consists of nonnegative vectors.
* `LMLExplore.simplex_nonempty`: the simplex of a nonempty type is nonempty.
* `LMLExplore.convex_simplex`: the simplex is convex.
-/

public section

namespace LMLExplore

variable {α : Type*} [Fintype α]

variable (α) in
/-- The probability simplex of `α`: vectors `w : α → ℝ` with nonnegative entries summing to `1`. -/
def simplex : Set (α → ℝ) := {w | (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1}

@[simp]
lemma mem_simplex_iff {w : α → ℝ} : w ∈ simplex α ↔ (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1 := Iff.rfl

lemma simplex_subset_nonneg : simplex α ⊆ Set.Ici 0 := fun _ hw ↦ hw.1

variable (α) in
lemma simplex_nonempty [Nonempty α] : (simplex α).Nonempty := by
  classical
  obtain ⟨a⟩ := ‹Nonempty α›
  exact ⟨Pi.single a 1, fun b ↦ by by_cases h : b = a <;> simp [h], by simp⟩

variable (α) in
lemma convex_simplex : Convex ℝ (simplex α) := by
  intro w hw v hv a b ha hb hab
  refine ⟨fun x ↦ ?_, ?_⟩
  · simpa using add_nonneg (mul_nonneg ha (hw.1 x)) (mul_nonneg hb (hv.1 x))
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw.2, hv.2, hab]

end LMLExplore
