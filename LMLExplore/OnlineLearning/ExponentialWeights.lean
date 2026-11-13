/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Simplex
public import LMLExplore.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Exponential weights

The softmax of a vector `v : α → ℝ` over a finite set `α`, also called its exponential weights, is
the probability vector `softmax v = a ↦ exp (v a) / ∑ b, exp (v b)`. Exponential weights with
learning rate `η > 0` and losses `y 0, y 1, …` play at round `t` the vector
`p t = softmax (-(η • ∑ s < t, y s))`, which puts more mass on the coordinates with small
cumulative loss. For rewards `r t = 1 - y t` (more generally `r t = c t - y t` with constants
`c t`), the softmax of `η` times the cumulative rewards is the same vector, since adding a constant
to every coordinate of `v` does not change `softmax v`.

For nonnegative losses, the regret of exponential weights against every coordinate `a` satisfies
the local-norm bound
`∑ t < n, (⟨p t, y t⟩ - y t a) ≤ log k / η + η / 2 * ∑ t < n, ⟨p t, (y t) ^ 2⟩`,
with `k` the cardinality of `α` and `⟨p, y⟩ = ∑ b, p b * y b`. The second-order terms are
averages under the played weights, rather than squared sup norms of the losses: this is what
makes the bound useful for the unbounded but nonnegative importance-weighted loss estimates of
Exp3 [LS, Section 11.3]. This bound and its form for nonincreasing learning rates
(`softmax_regret_le`, `softmax_regret_le_of_antitone`) are proved in
`LMLExplore.OnlineLearning.Simplex`, through follow the regularized leader with the negative
entropy.

## Main definitions

* `LMLExplore.OnlineLearning.softmax v`: the softmax (exponential weights) of `v`.

## Main statements

* `softmax_mem_simplex`, `softmax_pos`: on a nonempty finite type, the softmax is a probability
  vector with positive entries.
* `softmax_add_const`: adding a constant to every coordinate does not change the softmax.
* `measurable_softmax`: `v ↦ softmax v` is measurable.
* `sum_mul_exp_neg_sub_one_add_le`: for nonnegative weights `p`, a nonnegative loss `y` and
  `η ≥ 0`, `∑ b, p b * (exp (-(η * y b)) - 1 + η * y b) ≤ η ^ 2 / 2 * ∑ b, p b * y b ^ 2`.
* `sum_mul_exp_neg_sub_one_add_le_of_neg_one_le`: for nonnegative weights `p` and a loss `y` with
  `η * y b ≥ -1`, `∑ b, p b * (exp (-(η * y b)) - 1 + η * y b) ≤ η ^ 2 * ∑ b, p b * y b ^ 2`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Finset Real

namespace LMLExplore.OnlineLearning

variable {α : Type*} [Fintype α]

/-- The **softmax** of `v : α → ℝ`, also called its exponential weights: the probability vector
`a ↦ exp (v a) / ∑ b, exp (v b)`. -/
noncomputable def softmax (v : α → ℝ) : α → ℝ := fun a ↦ exp (v a) / ∑ b, exp (v b)

lemma softmax_apply (v : α → ℝ) (a : α) :
    softmax v a = exp (v a) / ∑ b, exp (v b) := (rfl)

lemma softmax_pos [Nonempty α] (v : α → ℝ) (a : α) : 0 < softmax v a :=
  div_pos (exp_pos _) (Finset.sum_pos (fun b _ ↦ exp_pos (v b)) univ_nonempty)

lemma softmax_nonneg (v : α → ℝ) (a : α) : 0 ≤ softmax v a :=
  div_nonneg (exp_pos _).le (Finset.sum_nonneg fun b _ ↦ (exp_pos (v b)).le)

@[simp]
lemma sum_softmax [Nonempty α] (v : α → ℝ) : ∑ a, softmax v a = 1 := by
  simp_rw [softmax_apply, ← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun b _ ↦ exp_pos (v b)) univ_nonempty).ne'

lemma softmax_mem_simplex [Nonempty α] (v : α → ℝ) : softmax v ∈ simplex α :=
  mem_simplex_iff.2 ⟨softmax_nonneg v, sum_softmax v⟩

/-- Adding a constant `c` to every coordinate of `v` does not change its softmax. -/
@[simp]
lemma softmax_add_const (v : α → ℝ) (c : ℝ) :
    softmax (fun a ↦ v a + c) = softmax v := by
  funext a
  simp_rw [softmax_apply, exp_add, ← Finset.sum_mul]
  exact mul_div_mul_right _ _ (exp_pos c).ne'

/-- The softmax of the zero vector is uniform. -/
@[simp]
lemma softmax_zero : softmax (0 : α → ℝ) = fun _ ↦ (Fintype.card α : ℝ)⁻¹ := by
  funext a
  simp [softmax_apply]

@[fun_prop]
lemma measurable_softmax : Measurable (softmax (α := α)) := by
  refine Measurable.of_eval fun a ↦ ?_
  simp_rw [softmax_apply]
  exact (Real.measurable_exp.comp (measurable_pi_apply a)).div
    (Finset.measurable_sum _ fun b _ ↦ Real.measurable_exp.comp (measurable_pi_apply b))

/-- **Second-order bound under exponential weights.** For nonnegative weights `p`, a nonnegative
loss `y` and a learning rate `η ≥ 0`,
`∑ b, p b * (exp (-(η * y b)) - 1 + η * y b) ≤ η ^ 2 / 2 * ∑ b, p b * y b ^ 2`, from
`exp (-x) ≤ 1 - x + x ^ 2 / 2` for `x ≥ 0`. This bounds the stability terms of exponential weights
by local norms [Ora, Section 7.5]. -/
theorem sum_mul_exp_neg_sub_one_add_le {p y : α → ℝ} (hp : ∀ b, 0 ≤ p b) (hy : ∀ b, 0 ≤ y b)
    {η : ℝ} (hη : 0 ≤ η) :
    ∑ b, p b * (exp (-(η * y b)) - 1 + η * y b) ≤ η ^ 2 / 2 * ∑ b, p b * y b ^ 2 := by
  rw [mul_sum]
  refine sum_le_sum fun b _ ↦ ?_
  have h := exp_neg_le_one_sub_add_sq_div_two (mul_nonneg hη (hy b))
  calc p b * (exp (-(η * y b)) - 1 + η * y b)
  _ ≤ p b * (η ^ 2 / 2 * y b ^ 2) := mul_le_mul_of_nonneg_left (by linarith) (hp b)
  _ = η ^ 2 / 2 * (p b * y b ^ 2) := by ring

/-- **Second-order bound under exponential weights, for losses bounded below.** For nonnegative
weights `p`, a learning rate `η` and a loss `y` with `η * y b ≥ -1` for every `b`,
`∑ b, p b * (exp (-(η * y b)) - 1 + η * y b) ≤ η ^ 2 * ∑ b, p b * y b ^ 2`, from
`exp (-x) ≤ 1 - x + x ^ 2` for `x ≥ -1` [LS, proof of Theorem 27.1]. -/
theorem sum_mul_exp_neg_sub_one_add_le_of_neg_one_le {p y : α → ℝ} (hp : ∀ b, 0 ≤ p b) {η : ℝ}
    (hy : ∀ b, -1 ≤ η * y b) :
    ∑ b, p b * (exp (-(η * y b)) - 1 + η * y b) ≤ η ^ 2 * ∑ b, p b * y b ^ 2 := by
  rw [mul_sum]
  refine sum_le_sum fun b _ ↦ ?_
  have h := exp_neg_le_one_sub_add_sq (hy b)
  calc p b * (exp (-(η * y b)) - 1 + η * y b)
  _ ≤ p b * (η ^ 2 * y b ^ 2) := mul_le_mul_of_nonneg_left (by nlinarith) (hp b)
  _ = η ^ 2 * (p b * y b ^ 2) := by ring

end LMLExplore.OnlineLearning
