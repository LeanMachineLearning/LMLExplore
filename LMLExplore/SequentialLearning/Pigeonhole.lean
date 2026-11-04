/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.SequentialLearning.FiniteActions
public import LMLExplore.Analysis.Real.Sqrt
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import LMLExplore.NumberTheory.Harmonic.Bounds

/-!
# Pigeonhole sums of inverse counts

Let `x_0, x_1, …` be a sequence in a finite type `α` with `m` elements, and let
`N_k(x) = #{i < k | x_i = x}` be the number of visits of `x` before step `k` (LML's `pullCount`).
Regret analyses of optimistic algorithms bound the regret by a sum over the steps of confidence
widths of the form `(N_k(x_k) + 1)^{-1/2}`, `max(1, N_k(x_k))^{-1/2}`, or their squares. Since
the step `k` that visits `x` sees the counts `0, 1, …, N_K(x) - 1`, each exactly once
(`Learning.sum_comp_pullCount`), these sums reduce to one-dimensional sums over the counts of each
element, which are then combined over the `m` elements. This file proves:

* `LMLExplore.sum_sqrt_pullCount_le`: `∑_x √(N_K(x)) ≤ √(m K)`, by Cauchy–Schwarz.
* `LMLExplore.sum_inv_sqrt_pullCount_add_one_le`: `∑_{k < K} (N_k(x_k) + 1)^{-1/2} ≤ 2 √(m K)`.
* `LMLExplore.sum_inv_pullCount_add_one_le`:
  `∑_{k < K} (N_k(x_k) + 1)⁻¹ ≤ m (1 + log (1 + K / m))`, by Jensen's inequality for the logarithm.
* `LMLExplore.sum_inv_sqrt_max_one_pullCount_le`:
  `∑_{k < K} max(1, N_k(x_k))^{-1/2} ≤ 2 √(m K) + m`.
* `LMLExplore.sum_inv_max_one_pullCount_le`: `∑_{k < K} max(1, N_k(x_k))⁻¹ ≤ m (2 + log K)`.

The sequence is `k ↦ A k ω` for `A : ℕ → Ω → α`, the form in which LML states `pullCount`; a fixed
sequence is the case of a one-point `Ω`. These sums appear in the regret analysis of UCBVI
[AJKS, Chapter 7].

## References

* [AJKS] A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, version of 31 January 2022.
-/

public section

open Finset Learning Real

namespace LMLExplore

variable {α Ω : Type*} [DecidableEq α] [Fintype α] {A : ℕ → Ω → α}

/-- `∑_x √(N_K(x)) ≤ √(m K)`: by Cauchy–Schwarz, the square roots of the counts of the elements of
`α` before step `K` add up to at most `√(Fintype.card α * K)`. -/
theorem sum_sqrt_pullCount_le (ω : Ω) (K : ℕ) :
    ∑ a, √(pullCount A a K ω : ℝ) ≤ √(Fintype.card α * K) := by
  have h := Real.sum_sqrt_mul_sqrt_le univ (f := fun _ : α ↦ (1 : ℝ))
    (g := fun a ↦ (pullCount A a K ω : ℝ)) (fun _ ↦ zero_le_one) (fun _ ↦ Nat.cast_nonneg _)
  simp only [sqrt_one, one_mul, sum_const, card_univ, nsmul_eq_mul, mul_one,
    sum_natCast_pullCount] at h
  rwa [sqrt_mul (Nat.cast_nonneg _)]

/-- **Pigeonhole sum of inverse square roots**: `∑_{k < K} (N_k(x_k) + 1)^{-1/2} ≤ 2 √(m K)`,
where `N_k(x)` counts the visits of `x` before step `k` and `m = Fintype.card α`. -/
theorem sum_inv_sqrt_pullCount_add_one_le (ω : Ω) (K : ℕ) :
    ∑ k ∈ range K, (√((pullCount A (A k ω) k ω : ℝ) + 1))⁻¹ ≤ 2 * √(Fintype.card α * K) := by
  refine (sum_comp_pullCount (fun j : ℕ ↦ (√((j : ℝ) + 1))⁻¹) K ω).trans_le ?_
  calc ∑ a, ∑ j ∈ range (pullCount A a K ω), (√((j : ℝ) + 1))⁻¹
      ≤ ∑ a, 2 * √(pullCount A a K ω : ℝ) :=
        sum_le_sum fun a _ ↦ sum_range_inv_sqrt_add_one_le _
    _ ≤ 2 * √(Fintype.card α * K) := by
        rw [← mul_sum]
        gcongr
        exact sum_sqrt_pullCount_le ω K

/-- **Pigeonhole sum of inverse counts**: `∑_{k < K} (N_k(x_k) + 1)⁻¹ ≤ m (1 + log (1 + K / m))`,
where `N_k(x)` counts the visits of `x` before step `k` and `m = Fintype.card α`. -/
theorem sum_inv_pullCount_add_one_le (ω : Ω) (K : ℕ) :
    ∑ k ∈ range K, ((pullCount A (A k ω) k ω : ℝ) + 1)⁻¹ ≤
      Fintype.card α * (1 + log (1 + K / Fintype.card α)) := by
  have : Nonempty α := ⟨A 0 ω⟩
  have hm : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  refine (sum_comp_pullCount (fun j : ℕ ↦ ((j : ℝ) + 1)⁻¹) K ω).trans_le ?_
  -- each element contributes at most `1 + log (1 + N_K(x))`
  have h_arm (n : ℕ) : ∑ j ∈ range n, ((j : ℝ) + 1)⁻¹ ≤ 1 + log (1 + n) := by
    refine (sum_range_inv_add_one_le n).trans ?_
    gcongr 1 + ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact log_le_log (by positivity) (by linarith)
  -- Jensen's inequality for the concave logarithm, with uniform weights `1 / m`
  have h_jensen := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := univ)
    (w := fun _ : α ↦ (Fintype.card α : ℝ)⁻¹) (p := fun a ↦ 1 + (pullCount A a K ω : ℝ))
    (fun _ _ ↦ by positivity) (by simp [hm.ne']) (fun _ _ ↦ Set.mem_Ioi.2 (by positivity))
  simp only [smul_eq_mul, ← mul_sum, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
    mul_one, sum_natCast_pullCount] at h_jensen
  have h_mean : (Fintype.card α : ℝ)⁻¹ * (Fintype.card α + K) = 1 + K / Fintype.card α := by
    field_simp
  rw [h_mean, inv_mul_le_iff₀ hm] at h_jensen
  calc ∑ a, ∑ j ∈ range (pullCount A a K ω), ((j : ℝ) + 1)⁻¹
      ≤ ∑ a, (1 + log (1 + (pullCount A a K ω : ℝ))) := sum_le_sum fun a _ ↦ h_arm _
    _ = Fintype.card α + ∑ a, log (1 + (pullCount A a K ω : ℝ)) := by simp [sum_add_distrib]
    _ ≤ Fintype.card α * (1 + log (1 + K / Fintype.card α)) := by linarith

/-- **Pigeonhole sum of clipped inverse square roots**:
`∑_{k < K} max(1, N_k(x_k))^{-1/2} ≤ 2 √(m K) + m`, where `N_k(x)` counts the visits of `x`
before step `k` and `m = Fintype.card α`. -/
theorem sum_inv_sqrt_max_one_pullCount_le (ω : Ω) (K : ℕ) :
    ∑ k ∈ range K, (√(max 1 (pullCount A (A k ω) k ω : ℝ)))⁻¹ ≤
      2 * √(Fintype.card α * K) + Fintype.card α := by
  refine (sum_comp_pullCount (fun j : ℕ ↦ (√(max 1 (j : ℝ)))⁻¹) K ω).trans_le ?_
  calc ∑ a, ∑ j ∈ range (pullCount A a K ω), (√(max 1 (j : ℝ)))⁻¹
      ≤ ∑ a, (2 * √(pullCount A a K ω : ℝ) + 1) :=
        sum_le_sum fun a _ ↦ sum_range_inv_sqrt_max_one_le _
    _ = 2 * ∑ a, √(pullCount A a K ω : ℝ) + Fintype.card α := by
        rw [sum_add_distrib, mul_sum, sum_const, card_univ, nsmul_eq_mul, mul_one]
    _ ≤ 2 * √(Fintype.card α * K) + Fintype.card α := by
        gcongr
        exact sum_sqrt_pullCount_le ω K

/-- **Pigeonhole sum of clipped inverse counts**: `∑_{k < K} max(1, N_k(x_k))⁻¹ ≤ m (2 + log K)`,
where `N_k(x)` counts the visits of `x` before step `k` and `m = Fintype.card α`. -/
theorem sum_inv_max_one_pullCount_le (ω : Ω) (K : ℕ) :
    ∑ k ∈ range K, (max 1 (pullCount A (A k ω) k ω : ℝ))⁻¹ ≤
      Fintype.card α * (2 + log K) := by
  refine (sum_comp_pullCount (fun j : ℕ ↦ (max 1 (j : ℝ))⁻¹) K ω).trans_le ?_
  -- each element, visited `n ≤ K` times, contributes at most `2 + log n ≤ 2 + log K`
  have h_arm (n : ℕ) (hn : n ≤ K) : ∑ j ∈ range n, (max 1 (j : ℝ))⁻¹ ≤ 2 + log K := by
    refine (sum_range_inv_max_one_le n).trans ?_
    gcongr 2 + ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simpa using log_natCast_nonneg K
    · exact log_le_log (by positivity) (by exact_mod_cast hn)
  calc ∑ a, ∑ j ∈ range (pullCount A a K ω), (max 1 (j : ℝ))⁻¹
      ≤ ∑ _a : α, (2 + log K) := sum_le_sum fun a _ ↦ h_arm _ (pullCount_le a K ω)
    _ = Fintype.card α * (2 + log K) := by rw [sum_const, card_univ, nsmul_eq_mul]

end LMLExplore
