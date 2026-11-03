/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.ENNReal.BigOperators
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
* `LMLExplore.single_mem_simplex`, `LMLExplore.simplex_nonempty`: the vertices `Pi.single a 1`
  belong to the simplex, which is nonempty when `α` is.
* `LMLExplore.convex_simplex`: the simplex is convex.
* `LMLExplore.smul_sub_single_mem_simplex`: removing a mass `s < 1` from an entry of a vector of
  the simplex and rescaling by `(1 - s)⁻¹` stays in the simplex.
* `LMLExplore.isCompact_simplex`: the simplex is compact.
* `LMLExplore.exists_mul_le_inv_sum_inv`, `LMLExplore.eq_inv_div_sum_inv_of_le_mul`: for positive
  weights `c`, every vector `w` of the simplex has an entry with
  `w a c a ≤ (∑ b, (c b)⁻¹)⁻¹`, and the vector proportional to `c⁻¹`
  (`LMLExplore.inv_div_sum_inv_mem_simplex`) is the only one with `w a c a` at least this value
  for all `a`: it is the unique maximizer of `w ↦ min_a w a c a` on the simplex.
* `LMLExplore.iSup_simplex_sum_ofReal_mul`: the largest value of `w ↦ ∑ a, w a e a` on the simplex
  is the largest entry of `e`, in `ℝ≥0∞`.
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

/-- The vertex `Pi.single a 1` of the simplex, the allocation of all the mass to `a`. -/
lemma single_mem_simplex [DecidableEq α] (a : α) : (Pi.single a 1 : α → ℝ) ∈ simplex α :=
  ⟨fun b ↦ by by_cases h : b = a <;> simp [h], by simp⟩

variable (α) in
lemma simplex_nonempty [Nonempty α] : (simplex α).Nonempty := by
  classical
  obtain ⟨a⟩ := ‹Nonempty α›
  exact ⟨Pi.single a 1, single_mem_simplex a⟩

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

/-! ### Linear functions and the smallest weighted entry on the simplex -/

/-- The largest value of `w ↦ ∑ a, w a e a` on the simplex, in `ℝ≥0∞`, is the largest entry of
`e`, attained at the vertex `Pi.single a 1` of an arm `a` with the largest entry. -/
lemma iSup_simplex_sum_ofReal_mul (e : α → ℝ) :
    ⨆ w ∈ simplex α, ∑ a, ENNReal.ofReal (w a * e a) = ⨆ a, ENNReal.ofReal (e a) := by
  classical
  refine le_antisymm (iSup₂_le fun w hw ↦ ?_) (iSup_le fun a ↦ ?_)
  · calc ∑ a, ENNReal.ofReal (w a * e a)
    _ ≤ ∑ a, ENNReal.ofReal (w a) * ⨆ b, ENNReal.ofReal (e b) := by
      refine Finset.sum_le_sum fun a _ ↦ ?_
      rw [ENNReal.ofReal_mul (hw.1 a)]
      exact mul_le_mul_right (le_iSup (fun b ↦ ENNReal.ofReal (e b)) a) _
    _ = ⨆ b, ENNReal.ofReal (e b) := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun a _ ↦ hw.1 a, hw.2,
        ENNReal.ofReal_one, one_mul]
  · refine le_iSup₂_of_le (Pi.single a 1) (single_mem_simplex a) (le_of_eq ?_)
    rw [Finset.sum_eq_single a (fun b _ hb ↦ by simp [hb]) (by simp)]
    simp

variable {w c : α → ℝ}

/-- A type whose simplex has an element is nonempty. -/
lemma nonempty_of_mem_simplex (hw : w ∈ simplex α) : Nonempty α := by
  by_contra h
  rw [not_nonempty_iff] at h
  simpa using hw.2

/-- For positive weights `c` on a nonempty type, the vector proportional to the inverses `c⁻¹`
belongs to the simplex. -/
lemma inv_div_sum_inv_mem_simplex [Nonempty α] (hc : ∀ a, 0 < c a) :
    (fun a ↦ (c a)⁻¹ / ∑ b, (c b)⁻¹) ∈ simplex α := by
  have hs : 0 < ∑ b, (c b)⁻¹ := Finset.sum_pos (fun b _ ↦ inv_pos.2 (hc b)) Finset.univ_nonempty
  exact ⟨fun a ↦ div_nonneg (inv_pos.2 (hc a)).le hs.le, by rw [← Finset.sum_div, div_self hs.ne']⟩

/-- For positive weights `c`, every vector `w` of the simplex has an entry with
`w a c a ≤ (∑ b, (c b)⁻¹)⁻¹`: the smallest weighted entry `min_a w a c a` is at most
`(∑ b, (c b)⁻¹)⁻¹`. -/
lemma exists_mul_le_inv_sum_inv (hw : w ∈ simplex α) (hc : ∀ a, 0 < c a) :
    ∃ a, w a * c a ≤ (∑ b, (c b)⁻¹)⁻¹ := by
  have := nonempty_of_mem_simplex hw
  have hs : 0 < ∑ b, (c b)⁻¹ := Finset.sum_pos (fun b _ ↦ inv_pos.2 (hc b)) Finset.univ_nonempty
  -- Since `∑ a, w a = 1 = ∑ a, (c a)⁻¹ / s`, some entry has `w a ≤ (c a)⁻¹ / s`.
  obtain ⟨a, -, ha⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty
    (f := w) (g := fun a ↦ (c a)⁻¹ / ∑ b, (c b)⁻¹)
    (by rw [hw.2, (inv_div_sum_inv_mem_simplex hc).2])
  refine ⟨a, (mul_le_mul_of_nonneg_right ha (hc a).le).trans_eq ?_⟩
  field_simp [(hc a).ne']

/-- For positive weights `c`, the only vector `w` of the simplex with
`(∑ b, (c b)⁻¹)⁻¹ ≤ w a c a` for every `a` is the vector proportional to `c⁻¹`. -/
lemma eq_inv_div_sum_inv_of_le_mul (hw : w ∈ simplex α) (hc : ∀ a, 0 < c a)
    (h : ∀ a, (∑ b, (c b)⁻¹)⁻¹ ≤ w a * c a) : w = fun a ↦ (c a)⁻¹ / ∑ b, (c b)⁻¹ := by
  have := nonempty_of_mem_simplex hw
  have hs : 0 < ∑ b, (c b)⁻¹ := Finset.sum_pos (fun b _ ↦ inv_pos.2 (hc b)) Finset.univ_nonempty
  -- Each entry is at least `(c a)⁻¹ / s`, and both vectors sum to `1`.
  have hle (a : α) : (c a)⁻¹ / ∑ b, (c b)⁻¹ ≤ w a := by
    rw [div_eq_inv_mul, ← le_div_iff₀ (inv_pos.2 (hc a)), div_inv_eq_mul]
    exact h a
  have h_eq := (Finset.sum_eq_sum_iff_of_le fun a _ ↦ hle a).1
    (by rw [(inv_div_sum_inv_mem_simplex hc).2, hw.2])
  exact funext fun a ↦ (h_eq a (Finset.mem_univ a)).symm

end LMLExplore
