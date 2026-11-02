/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Convex.Simplex
public import LMLExplore.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Exponential weights

The exponential weights of a vector `v : α → ℝ` over a finite set `α` are the probability vector
`expWeights v = a ↦ exp (v a) / ∑ b, exp (v b)` (the softmax of `v`). Exponential weights with
learning rate `η > 0` and losses `y 0, y 1, …` play at round `t` the vector
`p t = expWeights (-(η • ∑ s < t, y s))`, which puts more mass on the coordinates with small
cumulative loss. With rewards instead of losses, the weights of `η` times the cumulative rewards
are the same: adding a constant to every coordinate of `v` does not change `expWeights v`.

For nonnegative losses, the regret of exponential weights against every coordinate `a` satisfies
the local-norm bound
`∑ t < n, (⟨p t, y t⟩ - y t a) ≤ log k / η + η / 2 * ∑ t < n, ⟨p t, (y t) ^ 2⟩`,
with `k` the cardinality of `α` and `⟨p, y⟩ = ∑ b, p b * y b`. The second-order terms are
averages under the played weights, rather than squared sup norms of the losses: this is what
makes the bound useful for the unbounded but nonnegative importance-weighted loss estimates of
Exp3 [LS, Section 11.3].

## Main definitions

* `LMLExplore.OnlineLearning.expWeights v`: the exponential weights of `v`.

## Main statements

* `expWeights_mem_simplex`, `expWeights_pos`: on a nonempty finite type, the exponential weights
  form a probability vector with positive entries.
* `expWeights_add_const`: adding a constant to every coordinate does not change the exponential
  weights.
* `measurable_expWeights`: `v ↦ expWeights v` is measurable.
* `log_sum_exp_sub_mul_le`: the one-step bound on the log-partition function
  `log ∑ b, exp (v b)` under a nonnegative loss `y` and learning rate `η ≥ 0`.
* `expWeights_regret_le`: the local-norm regret bound of exponential weights for nonnegative
  losses.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open Finset Real

namespace LMLExplore.OnlineLearning

variable {α : Type*} [Fintype α]

/-- The **exponential weights** of `v : α → ℝ`: the probability vector
`a ↦ exp (v a) / ∑ b, exp (v b)`, also called the softmax of `v`. -/
noncomputable def expWeights (v : α → ℝ) : α → ℝ := fun a ↦ exp (v a) / ∑ b, exp (v b)

lemma expWeights_apply (v : α → ℝ) (a : α) :
    expWeights v a = exp (v a) / ∑ b, exp (v b) := (rfl)

lemma expWeights_pos [Nonempty α] (v : α → ℝ) (a : α) : 0 < expWeights v a :=
  div_pos (exp_pos _) (Finset.sum_pos (fun b _ ↦ exp_pos (v b)) univ_nonempty)

lemma expWeights_nonneg (v : α → ℝ) (a : α) : 0 ≤ expWeights v a :=
  div_nonneg (exp_pos _).le (Finset.sum_nonneg fun b _ ↦ (exp_pos (v b)).le)

@[simp]
lemma sum_expWeights [Nonempty α] (v : α → ℝ) : ∑ a, expWeights v a = 1 := by
  simp_rw [expWeights_apply, ← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun b _ ↦ exp_pos (v b)) univ_nonempty).ne'

lemma expWeights_mem_simplex [Nonempty α] (v : α → ℝ) : expWeights v ∈ simplex α :=
  mem_simplex_iff.2 ⟨expWeights_nonneg v, sum_expWeights v⟩

/-- Adding a constant `c` to every coordinate of `v` does not change its exponential weights. -/
@[simp]
lemma expWeights_add_const (v : α → ℝ) (c : ℝ) :
    expWeights (fun a ↦ v a + c) = expWeights v := by
  funext a
  simp_rw [expWeights_apply, exp_add, ← Finset.sum_mul]
  exact mul_div_mul_right _ _ (exp_pos c).ne'

/-- The exponential weights of the zero vector are uniform. -/
@[simp]
lemma expWeights_zero : expWeights (0 : α → ℝ) = fun _ ↦ (Fintype.card α : ℝ)⁻¹ := by
  funext a
  simp [expWeights_apply]

@[fun_prop]
lemma measurable_expWeights : Measurable (expWeights (α := α)) := by
  refine Measurable.of_eval fun a ↦ ?_
  simp_rw [expWeights_apply]
  exact (Real.measurable_exp.comp (measurable_pi_apply a)).div
    (Finset.measurable_sum _ fun b _ ↦ Real.measurable_exp.comp (measurable_pi_apply b))

/-- **One step of exponential weights.** For a nonnegative loss `y` and a learning rate `η ≥ 0`,
the log-partition function `log ∑ b, exp (v b)` decreases by at least
`η ⟨p, y⟩ - η ^ 2 / 2 ⟨p, y ^ 2⟩` when the loss `η y` is subtracted from `v`, where
`p = expWeights v`. -/
theorem log_sum_exp_sub_mul_le [Nonempty α] (v : α → ℝ) {y : α → ℝ} (hy : ∀ b, 0 ≤ y b)
    {η : ℝ} (hη : 0 ≤ η) :
    log (∑ b, exp (v b - η * y b)) ≤ log (∑ b, exp (v b)) - η * ∑ b, expWeights v b * y b +
      η ^ 2 / 2 * ∑ b, expWeights v b * y b ^ 2 := by
  set p := expWeights v with hp
  have hZ : 0 < ∑ b, exp (v b) := Finset.sum_pos (fun b _ ↦ exp_pos (v b)) univ_nonempty
  -- the new partition function is `Z * ∑ b, p b * exp (-(η * y b))`, with `Z` the old one
  have hsplit : ∑ b, exp (v b - η * y b) = (∑ b, exp (v b)) * ∑ b, p b * exp (-(η * y b)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [hp, expWeights_apply, sub_eq_add_neg, exp_add]
    field_simp
  have hS : 0 < ∑ b, p b * exp (-(η * y b)) :=
    Finset.sum_pos (fun b _ ↦ mul_pos (expWeights_pos v b) (exp_pos _)) univ_nonempty
  have hle : ∑ b, p b * exp (-(η * y b)) ≤
      1 - η * ∑ b, p b * y b + η ^ 2 / 2 * ∑ b, p b * y b ^ 2 := by
    calc ∑ b, p b * exp (-(η * y b))
    _ ≤ ∑ b, p b * (1 - η * y b + (η * y b) ^ 2 / 2) :=
        Finset.sum_le_sum fun b _ ↦ mul_le_mul_of_nonneg_left
          (exp_neg_le_one_sub_add_sq_div_two (mul_nonneg hη (hy b))) (expWeights_nonneg v b)
    _ = 1 - η * ∑ b, p b * y b + η ^ 2 / 2 * ∑ b, p b * y b ^ 2 := by
        simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
        simp only [mul_one, hp, sum_expWeights]
        congr 1
        · congr 1
          exact Finset.sum_congr rfl fun b _ ↦ by ring
        · exact Finset.sum_congr rfl fun b _ ↦ by ring
  rw [hsplit, log_mul hZ.ne' hS.ne']
  linarith [log_le_sub_one_of_pos hS]

/-- **Regret of exponential weights** with local norms. For losses `y t` that are nonnegative at
the rounds `t < n` and a learning rate `η > 0`, the weights `p t = expWeights (-(η • ∑ s < t, y s))`
satisfy, against every coordinate `a`,
`∑ t < n, (⟨p t, y t⟩ - y t a) ≤ log k / η + η / 2 * ∑ t < n, ⟨p t, (y t) ^ 2⟩`,
with `k` the cardinality of `α`. -/
theorem expWeights_regret_le [Nonempty α] {η : ℝ} (hη : 0 < η) {y : ℕ → α → ℝ} {n : ℕ}
    (hy : ∀ t < n, ∀ b, 0 ≤ y t b) (a : α) :
    ∑ t ∈ range n, (∑ b, expWeights (-(η • ∑ s ∈ range t, y s)) b * y t b - y t a) ≤
      log (Fintype.card α) / η +
        η / 2 * ∑ t ∈ range n, ∑ b, expWeights (-(η • ∑ s ∈ range t, y s)) b * y t b ^ 2 := by
  -- the potential `Φ t = log ∑ b, exp (-η L t b)` of the cumulative losses `L t`
  set L : ℕ → α → ℝ := fun t ↦ ∑ s ∈ range t, y s with hL
  set Φ : ℕ → ℝ := fun t ↦ log (∑ b, exp ((-(η • L t)) b)) with hΦ
  have hstep : ∀ t < n, Φ (t + 1) - Φ t ≤ -(η * ∑ b, expWeights (-(η • L t)) b * y t b) +
      η ^ 2 / 2 * ∑ b, expWeights (-(η • L t)) b * y t b ^ 2 := by
    intro t ht
    have h := log_sum_exp_sub_mul_le (-(η • L t)) (hy t ht) hη.le
    have hL1 : (fun b ↦ (-(η • L (t + 1))) b) = fun b ↦ (-(η • L t)) b - η * y t b := by
      funext b
      simp only [hL, sum_range_succ, smul_add, Pi.neg_apply, Pi.add_apply, Pi.smul_apply,
        Finset.sum_apply, smul_eq_mul]
      ring
    simp only [hΦ, hL1]
    linarith
  have h0 : Φ 0 = log (Fintype.card α) := by simp [hΦ, hL]
  have hn : -(η * L n a) ≤ Φ n := by
    rw [hΦ, ← log_exp (-(η * L n a))]
    exact log_le_log (exp_pos _) (Finset.single_le_sum (f := fun b ↦ exp ((-(η • L n)) b))
      (fun b _ ↦ (exp_pos _).le) (mem_univ a))
  have htel : Φ n - Φ 0 ≤ ∑ t ∈ range n, (-(η * ∑ b, expWeights (-(η • L t)) b * y t b) +
      η ^ 2 / 2 * ∑ b, expWeights (-(η • L t)) b * y t b ^ 2) := by
    rw [← Finset.sum_range_sub Φ n]
    exact Finset.sum_le_sum fun t ht ↦ hstep t (mem_range.1 ht)
  have hLa : L n a = ∑ t ∈ range n, y t a := by simp [hL]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at htel
  rw [Finset.sum_sub_distrib, ← hLa, div_add' _ _ _ hη.ne', le_div_iff₀ hη]
  nlinarith

end LMLExplore.OnlineLearning
