/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg

/-!
# The indices with the largest values

For `x : α → ℝ` on a nonempty finite type `α`, `topArms x k` is a set of `k` indices with the
largest values of `x`, chosen one at a time with LML's `argmax`: `topArms x (k + 1)` adds to
`topArms x k` an index outside it with the largest value. In bandit algorithms such as LUCB, it
is the set of the `k` arms with the largest empirical means.

## Main definitions

* `topArms x k`: `k` indices with the largest values of `x`.

## Main statements

* `argmax_notMem_and_le`: the index with the largest value outside a set `S` is outside `S` and
  its value is at least the value of every index outside `S`.
* `card_topArms`: `topArms x k` has `k` elements for `k` at most the number of indices.
* `le_of_mem_topArms_of_notMem_topArms`: the values of `x` on `topArms x k` are at least its
  values outside `topArms x k`.
* `measurable_topArms`: `topArms x k` is a measurable function of `x`.
-/

public section

open MeasureTheory Finset

namespace LMLExplore

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- If some index `b` is outside `S`, the index with the largest value of `x` outside `S` is
outside `S` and its value is at least that of `b`. -/
lemma argmax_notMem_and_le {S : Finset α} {x : α → ℝ} {b : α} (hb : b ∉ S) :
    (argmax fun a ↦ if a ∈ S then (⊥ : EReal) else x a) ∉ S ∧
      x b ≤ x (argmax fun a ↦ if a ∈ S then (⊥ : EReal) else x a) := by
  have h := isMaxOn_univ_iff.1 (isMaxOn_argmax fun a ↦ if a ∈ S then (⊥ : EReal) else x a) b
  by_cases hc : (argmax fun a ↦ if a ∈ S then (⊥ : EReal) else x a) ∈ S
  · simp [hb, hc] at h
  · simp only [hb, hc, ↓reduceIte, EReal.coe_le_coe_iff] at h
    exact ⟨hc, h⟩

/-- `k` indices with the largest values of `x`, chosen one at a time: `topArms x (k + 1)` adds to
`topArms x k` an index outside it with the largest value. -/
noncomputable def topArms (x : α → ℝ) : ℕ → Finset α
  | 0 => ∅
  | k + 1 => insert (argmax fun a ↦ if a ∈ topArms x k then (⊥ : EReal) else x a) (topArms x k)

@[simp]
lemma topArms_zero (x : α → ℝ) : topArms x 0 = ∅ := (rfl)

lemma topArms_succ (x : α → ℝ) (k : ℕ) :
    topArms x (k + 1) =
      insert (argmax fun a ↦ if a ∈ topArms x k then (⊥ : EReal) else x a) (topArms x k) := (rfl)

/-- There are `k` indices in `topArms x k` for `k` at most the number of indices. -/
lemma card_topArms (x : α → ℝ) {k : ℕ} (hk : k ≤ Fintype.card α) : #(topArms x k) = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (by omega)
    obtain ⟨b, hb⟩ : ∃ b, b ∉ topArms x k := by
      by_contra! h
      rw [eq_univ_of_forall h, card_univ] at ih
      omega
    rw [topArms_succ, card_insert_of_notMem (argmax_notMem_and_le hb).1, ih]

/-- The values of `x` on `topArms x k` are at least its values outside `topArms x k`. -/
lemma le_of_mem_topArms_of_notMem_topArms (x : α → ℝ) {k : ℕ} {a b : α}
    (ha : a ∈ topArms x k) (hb : b ∉ topArms x k) : x b ≤ x a := by
  induction k with
  | zero => simp at ha
  | succ k ih =>
    rw [topArms_succ, mem_insert, not_or] at hb
    rw [topArms_succ, mem_insert] at ha
    rcases ha with rfl | ha
    · exact (argmax_notMem_and_le hb.2).2
    · exact ih ha hb.2

variable [MeasurableSpace α] [MeasurableSingletonClass α]

lemma measurable_topArms (k : ℕ) : Measurable fun x : α → ℝ ↦ topArms x k := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hc : Measurable fun x : α → ℝ ↦
        argmax fun a ↦ if a ∈ topArms x k then (⊥ : EReal) else x a := by
      refine (measurable_argmax (ι := α) (α := EReal)).comp (Measurable.of_eval fun a ↦ ?_)
      exact Measurable.ite ((measurableSet_mem_finset a).preimage ih) measurable_const
        (measurable_coe_real_ereal.comp (measurable_pi_apply a))
    simp_rw [topArms_succ, insert_eq]
    exact ((measurable_of_countable fun a : α ↦ ({a} : Finset α)).comp hc).union_finset ih

end LMLExplore
