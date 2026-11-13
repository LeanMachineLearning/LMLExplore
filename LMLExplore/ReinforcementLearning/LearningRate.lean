/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Tactic.Module
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Learning-rate weights

Stochastic approximation algorithms such as Q-learning update an estimate by the recursion
`x t = (1 - η t) • x (t - 1) + η t • y t`, which moves the estimate towards a new target `y t` with
the learning rate `η t`. Unrolled, the `t`-th iterate is an explicit combination of the initial
value and of the targets,

`x t = (∏_{j=1}^t (1 - η j)) • x 0 + ∑_{i=1}^t η^i_t • y i`,

with the weights `η^i_t = η i ∏_{j=i+1}^t (1 - η j)`.

The weights `η^i_t = learningRateWeight η t i` add up to `1 - ∏_{j=1}^t (1 - η j)`. Analyses of
Q-learning bound the error of the iterates through these weights, and the first part of this file
develops them for any learning rate, in a module over a commutative ring.

Optimistic Q-learning with horizon `H` [JABJ18] uses the learning rate
`α t = qLearningRate H t = (H + 1) / (H + t)`. Since `α 1 = 1`, the initial value gets weight
`α^0_t = 0` for `t ≥ 1` and the weights `α^i_t` add up to `1`. For `H ≥ 1` and `1 ≤ i ≤ t`, they
satisfy [JABJ18, Lemma 4.1]:
* `1 / √t ≤ ∑_{i=1}^t α^i_t / √i ≤ 2 / √t`;
* `α^i_t ≤ (H + 1) / (H + t) ≤ 2 H / t`, hence `∑_{i=1}^t (α^i_t) ^ 2 ≤ 2 H / t`;
* `∑_{t ≥ i} α^i_t = 1 + 1 / H`.
The first bound only needs `H ≥ 0`, and the partial sums `∑_{t=i}^T α^i_t` are at most
`1 + 1 / H` for all `H > 0`.

## Main definitions

* `LMLExplore.learningRateWeight η t i`: the weight `η i ∏_{j=i+1}^t (1 - η j)` of the `i`-th
  target in the `t`-th iterate.
* `LMLExplore.qLearningRate H t`: the learning rate `(H + 1) / (H + t)` of optimistic Q-learning.

## Main statements

* `LMLExplore.eq_prod_smul_add_sum_learningRateWeight_smul`: the unrolled recursion.
* `LMLExplore.sum_learningRateWeight`: `∑_{i=1}^t η^i_t = 1 - ∏_{j=1}^t (1 - η j)`.
* `LMLExplore.sum_learningRateWeight_qLearningRate`: `∑_{i=1}^t α^i_t = 1` for `t ≥ 1`.
* `LMLExplore.one_div_sqrt_le_sum_learningRateWeight_qLearningRate_div_sqrt`,
  `LMLExplore.sum_learningRateWeight_qLearningRate_div_sqrt_le`:
  `1 / √t ≤ ∑_{i=1}^t α^i_t / √i ≤ 2 / √t`.
* `LMLExplore.learningRateWeight_qLearningRate_le_two_mul_div`: `α^i_t ≤ 2 H / t`.
* `LMLExplore.sum_learningRateWeight_qLearningRate_sq_le`: `∑_{i=1}^t (α^i_t) ^ 2 ≤ 2 H / t`.
* `LMLExplore.hasSum_learningRateWeight_qLearningRate`: `∑_{t ≥ i} α^i_t = 1 + 1 / H`.

## References

* [JABJ18] C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, *Is Q-learning provably efficient?*,
  NeurIPS 2018, arXiv:1807.03765.
-/

public section

open Finset Filter Topology

namespace LMLExplore

section Weight

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The weight `η i * ∏_{j=i+1}^t (1 - η j)` of the `i`-th target `y i` in the `t`-th iterate of
the recursion `x t = (1 - η t) • x (t - 1) + η t • y t`, for `1 ≤ i ≤ t`. -/
def learningRateWeight (η : ℕ → R) (t i : ℕ) : R := η i * ∏ j ∈ Ioc i t, (1 - η j)

theorem learningRateWeight_def (η : ℕ → R) (t i : ℕ) :
    learningRateWeight η t i = η i * ∏ j ∈ Ioc i t, (1 - η j) := (rfl)

/-- The last target `y t` of the `t`-th iterate has weight `η t`. -/
@[simp]
theorem learningRateWeight_self (η : ℕ → R) (t : ℕ) : learningRateWeight η t t = η t := by
  simp [learningRateWeight_def]

/-- Each step of the recursion multiplies the weights of the previous targets by `1 - η (t + 1)`. -/
theorem learningRateWeight_succ (η : ℕ → R) {t i : ℕ} (hi : i ≤ t) :
    learningRateWeight η (t + 1) i = (1 - η (t + 1)) * learningRateWeight η t i := by
  rw [learningRateWeight_def, learningRateWeight_def, prod_Ioc_succ_top hi]
  ring

/-- The combinations `∑_{i=1}^t η^i_t • y i` of the targets satisfy the recursion
`x (t + 1) = (1 - η (t + 1)) • x t + η (t + 1) • y (t + 1)`. -/
theorem sum_learningRateWeight_smul_succ (η : ℕ → R) (y : ℕ → M) (t : ℕ) :
    ∑ i ∈ Icc 1 (t + 1), learningRateWeight η (t + 1) i • y i =
      (1 - η (t + 1)) • ∑ i ∈ Icc 1 t, learningRateWeight η t i • y i +
        η (t + 1) • y (t + 1) := by
  rw [sum_Icc_succ_top (by omega), learningRateWeight_self, smul_sum]
  congr 1
  refine sum_congr rfl fun i hi ↦ ?_
  rw [learningRateWeight_succ η (mem_Icc.1 hi).2, mul_smul]

/-- **The unrolled recursion.** If `x (t + 1) = (1 - η (t + 1)) • x t + η (t + 1) • y (t + 1)` for
every `t`, then `x t = (∏_{j=1}^t (1 - η j)) • x 0 + ∑_{i=1}^t η^i_t • y i`. -/
theorem eq_prod_smul_add_sum_learningRateWeight_smul {η : ℕ → R} {x y : ℕ → M}
    (hx : ∀ t, x (t + 1) = (1 - η (t + 1)) • x t + η (t + 1) • y (t + 1)) (t : ℕ) :
    x t = (∏ j ∈ Icc 1 t, (1 - η j)) • x 0 + ∑ i ∈ Icc 1 t, learningRateWeight η t i • y i := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hx, ih, sum_learningRateWeight_smul_succ, prod_Icc_succ_top (by omega)]
    module

/-- The weights of the targets add up to `1 - ∏_{j=1}^t (1 - η j)`, the complement of the weight of
the initial value. This is `Finset.prod_one_sub_ordered'` on `Icc 1 t`, with
`{j ∈ Icc 1 t | i < j}` rewritten to `Ioc i t`. -/
theorem sum_learningRateWeight (η : ℕ → R) (t : ℕ) :
    ∑ i ∈ Icc 1 t, learningRateWeight η t i = 1 - ∏ j ∈ Icc 1 t, (1 - η j) := by
  rw [prod_one_sub_ordered', sub_sub_cancel]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [learningRateWeight_def]
  congr 2
  ext j
  simp only [mem_filter, mem_Icc, mem_Ioc]
  have := (mem_Icc.1 hi).1
  omega

/-- The weights are nonnegative when the learning rates lie in `[0, 1]`. -/
theorem learningRateWeight_nonneg {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
    {η : ℕ → R} {t i : ℕ} (hi : 0 ≤ η i) (hη : ∀ j ∈ Ioc i t, η j ≤ 1) :
    0 ≤ learningRateWeight η t i :=
  mul_nonneg hi (prod_nonneg fun j hj ↦ sub_nonneg.2 (hη j hj))

end Weight

section QLearning

variable {H : ℝ}

/-- The learning rate `α t = (H + 1) / (H + t)` of optimistic Q-learning with horizon `H`
[JABJ18]. It is meaningful for `t ≥ 1`. -/
noncomputable def qLearningRate (H : ℝ) (t : ℕ) : ℝ := (H + 1) / (H + t)

theorem qLearningRate_def (H : ℝ) (t : ℕ) : qLearningRate H t = (H + 1) / (H + t) := (rfl)

/-- The first step has learning rate `1`. -/
@[simp]
theorem qLearningRate_one (hH : H + 1 ≠ 0) : qLearningRate H 1 = 1 := by
  simp [qLearningRate_def, hH]

/-- `1 - α t = (t - 1) / (H + t)`. -/
theorem one_sub_qLearningRate {t : ℕ} (hH : H + t ≠ 0) :
    1 - qLearningRate H t = (t - 1) / (H + t) := by
  rw [qLearningRate_def]
  field_simp
  ring

theorem qLearningRate_nonneg (hH : 0 ≤ H) (t : ℕ) : 0 ≤ qLearningRate H t := by
  rw [qLearningRate_def]
  positivity

/-- `α t ≤ 1` for `t ≥ 1`. -/
theorem qLearningRate_le_one (hH : 0 ≤ H) {t : ℕ} (ht : 1 ≤ t) : qLearningRate H t ≤ 1 := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  exact div_le_one_of_le₀ (by linarith) (by linarith)

/-- `(H + 1) / (H + t) ≤ 2 H / t` for `H ≥ 1` and `t ≥ 1`. -/
theorem qLearningRate_le_two_mul_div (hH : 1 ≤ H) {t : ℕ} (ht : 1 ≤ t) :
    qLearningRate H t ≤ 2 * H / t := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  rw [qLearningRate_def, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- With the learning rate `(H + 1) / (H + t)`, the initial value has weight `0` in the iterates
`t ≥ 1`, since the first step replaces it by the first target. -/
theorem prod_one_sub_qLearningRate_eq_zero (hH : H + 1 ≠ 0) {t : ℕ} (ht : 1 ≤ t) :
    ∏ j ∈ Icc 1 t, (1 - qLearningRate H j) = 0 :=
  prod_eq_zero (mem_Icc.2 ⟨le_rfl, ht⟩) (by simp [qLearningRate_one hH])

/-- With the learning rate `(H + 1) / (H + t)`, the weights of the targets add up to `1`
[JABJ18, Lemma 4.1]. -/
theorem sum_learningRateWeight_qLearningRate (hH : H + 1 ≠ 0) {t : ℕ} (ht : 1 ≤ t) :
    ∑ i ∈ Icc 1 t, learningRateWeight (qLearningRate H) t i = 1 := by
  rw [sum_learningRateWeight, prod_one_sub_qLearningRate_eq_zero hH ht, sub_zero]

/-- The products `∏_{j=i+1}^t (1 - α j)` of the learning rate `(H + 1) / (H + t)` are
nonnegative, since `α j ≤ 1` for `j ≥ 1`. -/
theorem prod_Ioc_one_sub_qLearningRate_nonneg (hH : 0 ≤ H) (i t : ℕ) :
    0 ≤ ∏ j ∈ Ioc i t, (1 - qLearningRate H j) :=
  prod_nonneg fun j hj ↦ sub_nonneg.2 (qLearningRate_le_one hH (by have := (mem_Ioc.1 hj).1; omega))

/-- The weights of the learning rate `(H + 1) / (H + t)` are nonnegative. -/
theorem learningRateWeight_qLearningRate_nonneg (hH : 0 ≤ H) (t i : ℕ) :
    0 ≤ learningRateWeight (qLearningRate H) t i :=
  learningRateWeight_nonneg (qLearningRate_nonneg hH i) fun j hj ↦
    qLearningRate_le_one hH (by have := (mem_Ioc.1 hj).1; omega)

/-- The weight of every target of the `t`-th iterate is at most the learning rate
`(H + 1) / (H + t)` of the last one. -/
theorem learningRateWeight_qLearningRate_le (hH : 0 ≤ H) {t i : ℕ} (hit : i ≤ t) :
    learningRateWeight (qLearningRate H) t i ≤ qLearningRate H t := by
  induction t, hit using Nat.le_induction with
  | base => simp
  | succ t hit ih =>
    rw [learningRateWeight_succ _ hit]
    calc (1 - qLearningRate H (t + 1)) * learningRateWeight (qLearningRate H) t i
        ≤ (1 - qLearningRate H (t + 1)) * qLearningRate H t :=
          mul_le_mul_of_nonneg_left ih (sub_nonneg.2 (qLearningRate_le_one hH (by omega)))
      _ ≤ qLearningRate H (t + 1) := by
          rcases (add_nonneg hH (Nat.cast_nonneg t : (0 : ℝ) ≤ t)).eq_or_lt with h0 | h0
          · rw [qLearningRate_def H t, ← h0, div_zero, mul_zero]
            exact qLearningRate_nonneg hH _
          rw [one_sub_qLearningRate (by positivity), qLearningRate_def, qLearningRate_def]
          push_cast
          rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos (by positivity) h0) (by positivity)]
          have : 0 ≤ (H + 1) * (H + (t + 1)) * H := by positivity
          nlinarith

/-- The weight of every target of the `t`-th iterate is at most `2 H / t` [JABJ18, Lemma 4.1]. -/
theorem learningRateWeight_qLearningRate_le_two_mul_div (hH : 1 ≤ H) {t i : ℕ} (hit : i ≤ t)
    (ht : 1 ≤ t) : learningRateWeight (qLearningRate H) t i ≤ 2 * H / t :=
  (learningRateWeight_qLearningRate_le (by linarith) hit).trans (qLearningRate_le_two_mul_div hH ht)

/-- The squared weights of the targets of the `t`-th iterate add up to at most `2 H / t`
[JABJ18, Lemma 4.1]. -/
theorem sum_learningRateWeight_qLearningRate_sq_le (hH : 1 ≤ H) {t : ℕ} (ht : 1 ≤ t) :
    ∑ i ∈ Icc 1 t, learningRateWeight (qLearningRate H) t i ^ 2 ≤ 2 * H / t := by
  calc ∑ i ∈ Icc 1 t, learningRateWeight (qLearningRate H) t i ^ 2
      ≤ ∑ i ∈ Icc 1 t, learningRateWeight (qLearningRate H) t i * (2 * H / t) := by
        refine sum_le_sum fun i hi ↦ ?_
        rw [sq]
        exact mul_le_mul_of_nonneg_left
          (learningRateWeight_qLearningRate_le_two_mul_div hH (mem_Icc.1 hi).2 ht)
          (learningRateWeight_qLearningRate_nonneg (by linarith) t i)
    _ = 2 * H / t := by
        rw [← sum_mul, sum_learningRateWeight_qLearningRate (by linarith) ht, one_mul]

/-- `1 / √t ≤ ∑_{i=1}^t α^i_t / √i` [JABJ18, Lemma 4.1]. -/
theorem one_div_sqrt_le_sum_learningRateWeight_qLearningRate_div_sqrt (hH : 0 ≤ H) {t : ℕ}
    (ht : 1 ≤ t) :
    1 / √t ≤ ∑ i ∈ Icc 1 t, learningRateWeight (qLearningRate H) t i / √i := by
  calc 1 / √t = ∑ i ∈ Icc 1 t, learningRateWeight (qLearningRate H) t i / √t := by
        rw [← sum_div, sum_learningRateWeight_qLearningRate (by linarith) ht]
    _ ≤ ∑ i ∈ Icc 1 t, learningRateWeight (qLearningRate H) t i / √i := by
        refine sum_le_sum fun i hi ↦ ?_
        have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (mem_Icc.1 hi).1
        exact div_le_div_of_nonneg_left (learningRateWeight_qLearningRate_nonneg hH t i)
          (Real.sqrt_pos.2 (by linarith))
          (Real.sqrt_le_sqrt (by exact_mod_cast (mem_Icc.1 hi).2))

/-- The algebraic identity behind the induction step of
`sum_learningRateWeight_qLearningRate_div_sqrt_le`, with `a = √t` and `b = √(t + 1)`. -/
private lemma div_mul_two_div_add_div_mul_inv_eq {H t a b : ℝ} (hb : 0 < b)
    (hHt : 0 < H + (t + 1)) (ha2 : a ^ 2 = t) :
    t / (H + (t + 1)) * (2 * a⁻¹) + (H + 1) / (H + (t + 1)) * b⁻¹ =
      (2 * (a * b) + (H + 1)) / ((H + (t + 1)) * b) := by
  subst ha2
  field_simp

/-- `∑_{i=1}^t α^i_t / √i ≤ 2 / √t` [JABJ18, Lemma 4.1]. -/
theorem sum_learningRateWeight_qLearningRate_div_sqrt_le (hH : 0 ≤ H) {t : ℕ} (ht : 1 ≤ t) :
    ∑ i ∈ Icc 1 t, learningRateWeight (qLearningRate H) t i / √i ≤ 2 / √t := by
  induction t, ht using Nat.le_induction with
  | base =>
    have hH1 : H + 1 ≠ 0 := by linarith
    simp [hH1]
  | succ t ht ih =>
    have h := sum_learningRateWeight_smul_succ (qLearningRate H) (fun i ↦ (√(i : ℝ))⁻¹) t
    simp only [smul_eq_mul] at h
    simp only [div_eq_mul_inv] at ih ⊢
    rw [h, one_sub_qLearningRate (by positivity), qLearningRate_def]
    push_cast
    simp only [add_sub_cancel_right]
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have ha2 : √(t : ℝ) ^ 2 = t := Real.sq_sqrt (by linarith)
    have hb2 : √((t : ℝ) + 1) ^ 2 = t + 1 := Real.sq_sqrt (by linarith)
    have ha : 0 < √(t : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hb : 0 < √((t : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
    -- `2 √t √(t + 1) ≤ 2 t + 1`, by the inequality of arithmetic and geometric means
    have key : 2 * (√(t : ℝ) * √((t : ℝ) + 1)) + (H + 1) ≤ 2 * (H + (t + 1)) := by
      nlinarith [sq_nonneg (√(t : ℝ) - √((t : ℝ) + 1))]
    calc (t : ℝ) / (H + (t + 1)) *
          ∑ i ∈ Icc 1 t, learningRateWeight (qLearningRate H) t i * (√(i : ℝ))⁻¹ +
            (H + 1) / (H + (t + 1)) * (√((t : ℝ) + 1))⁻¹
        ≤ t / (H + (t + 1)) * (2 * (√(t : ℝ))⁻¹) +
            (H + 1) / (H + (t + 1)) * (√((t : ℝ) + 1))⁻¹ := by
          gcongr
      _ = (2 * (√(t : ℝ) * √((t : ℝ) + 1)) + (H + 1)) / ((H + (t + 1)) * √((t : ℝ) + 1)) :=
          div_mul_two_div_add_div_mul_inv_eq hb (by positivity) ha2
      _ ≤ 2 * (H + (t + 1)) / ((H + (t + 1)) * √((t : ℝ) + 1)) := by gcongr
      _ = 2 * (√((t : ℝ) + 1))⁻¹ := by
        field_simp

/-- The partial sums of the weights of the `i`-th target over the iterates `t = i, …, i + N - 1`
in closed form: `(1 + 1 / H) * (1 - (H + i + N) / (H + i) * ∏_{j=i+1}^{i+N} (1 - α j))`. -/
theorem sum_range_learningRateWeight_qLearningRate (hH : 0 < H) (i N : ℕ) :
    ∑ n ∈ range N, learningRateWeight (qLearningRate H) (i + n) i =
      (1 + 1 / H) * (1 - (H + i + N) / (H + i) *
        ∏ j ∈ Ioc i (i + N), (1 - qLearningRate H j)) := by
  induction N with
  | zero => simp [(by positivity : H + i ≠ 0)]
  | succ N ih =>
    rw [sum_range_succ, ih, learningRateWeight_def, ← add_assoc, prod_Ioc_succ_top (by omega),
      one_sub_qLearningRate (by positivity), qLearningRate_def]
    push_cast
    field_simp
    ring

/-- The remainder `(H + i + N) / (H + i) * ∏_{j=i+1}^{i+N} (1 - α j)` in the closed form of the
partial sums `sum_range_learningRateWeight_qLearningRate` is nonnegative. -/
private lemma div_mul_prod_Ioc_one_sub_qLearningRate_nonneg (hH : 0 ≤ H) (i N : ℕ) :
    0 ≤ (H + i + N) / (H + i) * ∏ j ∈ Ioc i (i + N), (1 - qLearningRate H j) :=
  mul_nonneg (by positivity) (prod_Ioc_one_sub_qLearningRate_nonneg hH i (i + N))

/-- The partial sums of the weights of the `i`-th target over the iterates `t ≥ i` are at most
`1 + 1 / H`. -/
theorem sum_range_learningRateWeight_qLearningRate_le (hH : 0 < H) (i N : ℕ) :
    ∑ n ∈ range N, learningRateWeight (qLearningRate H) (i + n) i ≤ 1 + 1 / H := by
  rw [sum_range_learningRateWeight_qLearningRate hH]
  have := div_mul_prod_Ioc_one_sub_qLearningRate_nonneg hH.le i N
  have : 0 ≤ 1 + 1 / H := by positivity
  nlinarith

/-- For `H ≥ 1`, `(H + i + N) * ∏_{j=i+1}^{i+N} (1 - α j) * (i + N) ≤ (H + i) * i`: the remainder
of the partial sums vanishes. -/
private lemma mul_prod_one_sub_qLearningRate_le (hH : 1 ≤ H) (i N : ℕ) :
    (H + i + N) * (∏ j ∈ Ioc i (i + N), (1 - qLearningRate H j)) * (i + N) ≤ (H + i) * i := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprod := prod_Ioc_one_sub_qLearningRate_nonneg (by linarith : 0 ≤ H) i (i + N)
    rw [← add_assoc, prod_Ioc_succ_top (by omega), one_sub_qLearningRate (by positivity)]
    push_cast
    calc (H + i + (N + 1)) * ((∏ j ∈ Ioc i (i + N), (1 - qLearningRate H j)) *
          ((i + N + 1 - 1) / (H + (i + N + 1)))) * (i + (N + 1))
        = (∏ j ∈ Ioc i (i + N), (1 - qLearningRate H j)) * (i + N) * (i + N + 1) := by
          field_simp
          ring
      _ ≤ (∏ j ∈ Ioc i (i + N), (1 - qLearningRate H j)) * (i + N) * (H + i + N) := by
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (H + i) * i := by linarith

/-- **The total weight of a target.** For `H ≥ 1`, the weights of the `i`-th target over all the
iterates `t ≥ i` add up to `1 + 1 / H` [JABJ18, Lemma 4.1]. -/
theorem hasSum_learningRateWeight_qLearningRate (hH : 1 ≤ H) (i : ℕ) :
    HasSum (fun n ↦ learningRateWeight (qLearningRate H) (i + n) i) (1 + 1 / H) := by
  have hH0 : 0 < H := by linarith
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun n ↦ learningRateWeight_qLearningRate_nonneg hH0.le _ _)]
  simp_rw [sum_range_learningRateWeight_qLearningRate hH0]
  -- the remainder is squeezed between `0` and `i / (i + N)`
  have hr0 := div_mul_prod_Ioc_one_sub_qLearningRate_nonneg hH0.le i
  have hr : ∀ N : ℕ, 1 ≤ N →
      (H + i + N) / (H + i) * ∏ j ∈ Ioc i (i + N), (1 - qLearningRate H j) ≤ i / (i + N) :=
    fun N hN ↦ by
      have hN' : (0 : ℝ) < i + N := by
        have : (1 : ℝ) ≤ N := by exact_mod_cast hN
        linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
      rw [le_div_iff₀ hN']
      calc (H + i + N) / (H + i) * (∏ j ∈ Ioc i (i + N), (1 - qLearningRate H j)) * (i + N)
          = (H + i + N) * (∏ j ∈ Ioc i (i + N), (1 - qLearningRate H j)) * (i + N) / (H + i) := by
            ring
        _ ≤ (H + i) * i / (H + i) :=
            div_le_div_of_nonneg_right (mul_prod_one_sub_qLearningRate_le hH i N) (by positivity)
        _ = i := by field_simp
  have hlim : Tendsto (fun N : ℕ ↦ (i : ℝ) / (i + N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  have hr_lim := tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall hr0) (eventually_atTop.2 ⟨1, hr⟩)
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hr_lim).const_mul (1 + 1 / H)
  rwa [sub_zero, mul_one] at h

end QLearning

end LMLExplore
