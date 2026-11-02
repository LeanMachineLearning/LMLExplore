/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

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
* `LMLExplore.add_eq_one_of_mem_simplex`: on a type with two elements `a` and `b`, the entries of
  a vector of the simplex satisfy `w a + w b = 1`.
* `LMLExplore.simplex_subset_nonneg`: the simplex consists of nonnegative vectors.
* `LMLExplore.simplex_nonempty`: the simplex of a nonempty type is nonempty.
* `LMLExplore.convex_simplex`: the simplex is convex.
* `LMLExplore.smul_sub_single_mem_simplex`: removing a mass `s < 1` from an entry of a vector of
  the simplex and rescaling by `(1 - s)⁻¹` stays in the simplex.
* `LMLExplore.isCompact_simplex`: the simplex is compact.
-/

public section

namespace LMLExplore

variable {α : Type*} [Fintype α]

variable (α) in
/-- The probability simplex of `α`: vectors `w : α → ℝ` with nonnegative entries summing to `1`. -/
def simplex : Set (α → ℝ) := {w | (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1}

@[simp]
lemma mem_simplex_iff {w : α → ℝ} : w ∈ simplex α ↔ (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1 := Iff.rfl

/-- On a type whose only elements are `a ≠ b`, the entries of a vector `w` of the simplex satisfy
`w a + w b = 1`. -/
lemma add_eq_one_of_mem_simplex {w : α → ℝ} {a b : α} (hab : a ≠ b) (h : ∀ c, c = a ∨ c = b)
    (hw : w ∈ simplex α) : w a + w b = 1 :=
  Fintype.sum_eq_add (f := w) a b hab (fun c hc ↦ absurd (h c) (not_or.2 hc)) ▸ hw.2

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

variable (α) in
lemma isClosed_simplex : IsClosed (simplex α) := by
  have h : simplex α = (⋂ a, {w | 0 ≤ w a}) ∩ {w | ∑ a, w a = 1} := by ext; simp
  rw [h]
  exact (isClosed_iInter fun a ↦ isClosed_le continuous_const (continuous_apply a)).inter
    (isClosed_eq (by fun_prop) continuous_const)

/-- The entries of a vector of the simplex lie in `[0, 1]`. -/
lemma simplex_subset_Icc : simplex α ⊆ Set.Icc 0 1 := by
  refine fun w hw ↦ ⟨hw.1, fun a ↦ ?_⟩
  simpa [hw.2] using Finset.single_le_sum (fun b _ ↦ hw.1 b) (Finset.mem_univ a)

/-- Removing a mass `s < 1` from an entry `w b ≥ s` of a vector `w` of the simplex and rescaling
by `(1 - s)⁻¹` gives a vector of the simplex. -/
lemma smul_sub_single_mem_simplex [DecidableEq α] {w : α → ℝ} (hw : w ∈ simplex α) {b : α}
    {s : ℝ} (hsb : s ≤ w b) (hs1 : s < 1) : (1 - s)⁻¹ • (w - Pi.single b s) ∈ simplex α := by
  refine ⟨fun c ↦ mul_nonneg (inv_nonneg.2 (sub_nonneg.2 hs1.le)) ?_, ?_⟩
  · by_cases hcb : c = b
    · subst hcb
      simpa using hsb
    · simpa [hcb] using hw.1 c
  · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_pi_single', Finset.mem_univ, ite_true, hw.2]
    field_simp [(sub_pos.2 hs1).ne']

variable (α) in
lemma isCompact_simplex : IsCompact (simplex α) :=
  isCompact_Icc.of_isClosed_subset (isClosed_simplex α) simplex_subset_Icc

end LMLExplore
