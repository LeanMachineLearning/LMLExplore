/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import LMLExplore.SequentialLearning.FiniteActions
public import LeanMachineLearning.Online.Bandit.Regret

/-!
# Bounds on the gaps and the expected regret

Facts about LML's `gap` and `regret` of a bandit `ν : Kernel α ℝ` that hold for any sequence of
actions `A : ℕ → Ω → α`.

The first part gives lower bounds on the gaps and on the expected regret in terms of the expected
numbers of pulls.

The second part turns gap-dependent regret bounds into gap-free ones. The analysis of an algorithm
for stochastic bandits with finitely many arms typically bounds the expected number of pulls of
each suboptimal arm `a` by `C / Δ_a ^ 2 + B`, where `Δ_a = gap ν a`. The resulting regret bound
`∑ a, (C / Δ_a + B Δ_a)` blows up when some gap is small. This is turned into the gap-free bound
`2 √(C k n) + B ∑ a, Δ_a` at horizon `n`, with `k` the number of arms, by splitting the arms
according to whether their gap is below a threshold `δ`, as in the proof of [LS, Theorem 7.2].

## Main statements

* `LMLExplore.Bandits.sub_le_gap`: the gap of an arm is at least its difference of mean with any
  other arm.
* `LMLExplore.Bandits.mul_sub_integral_pullCount_le_integral_regret`: if every arm other than `a₁`
  has gap at least `Δ`, the expected regret is at least `Δ (n - E[T_{a₁}(n)])`.
* `LMLExplore.Bandits.mul_integral_pullCount_le_integral_regret`: if the arm `a₁` has gap at least
  `Δ`, the expected regret is at least `Δ E[T_{a₁}(n)]`.
* `integral_regret_le_mul_add_div_add_of_forall_integral_pullCount_le`: the bound
  `δ n + k C / δ + B ∑ a, Δ_a` for every threshold `δ > 0`.
* `integral_regret_le_two_mul_sqrt_add_of_forall_integral_pullCount_le`: the bound
  `2 √(C k n) + B ∑ a, Δ_a`, for the optimal threshold `δ = √(C k / n)`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Bandits

namespace LMLExplore.Bandits

section LowerBound

variable {α : Type*} [MeasurableSpace α]

/-- The gap of an arm is at least its difference of mean with any other arm. -/
theorem sub_le_gap [Finite α] (ν : Kernel α ℝ) (a j : α) :
    (ν j)[id] - (ν a)[id] ≤ gap ν a := by
  rw [gap]
  exact sub_le_sub_right (le_ciSup (f := fun i ↦ (ν i)[id]) (Set.finite_range _).bddAbove j) _

variable [StandardBorelSpace α] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {A : ℕ → Ω → α} {ν : Kernel α ℝ}

/-- If every arm other than `a₁` has gap at least `Δ`, the expected regret is at least
`Δ (n - E[T_{a₁}(n)])`. -/
theorem mul_sub_integral_pullCount_le_integral_regret [Finite α] [DecidableEq α]
    (hA : ∀ t, Measurable (A t)) {a₁ : α} {Δ : ℝ} (hΔ : ∀ a ≠ a₁, Δ ≤ gap ν a) (n : ℕ) :
    Δ * (n - ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P) ≤ ∫ ω, regret ν A n ω ∂P := by
  have := Fintype.ofFinite α
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount hA]
  have hnn (a : α) : 0 ≤ ∫ ω, (pullCount A a n ω : ℝ) ∂P :=
    integral_nonneg fun _ ↦ Nat.cast_nonneg _
  calc Δ * (n - ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P)
      = ∑ a ∈ univ.erase a₁, Δ * ∫ ω, (pullCount A a n ω : ℝ) ∂P := by
        rw [← mul_sum, ← sum_integral_pullCount (P := P) hA n, ← add_sum_erase _ _ (mem_univ a₁)]
        ring
    _ ≤ ∑ a ∈ univ.erase a₁, gap ν a * ∫ ω, (pullCount A a n ω : ℝ) ∂P :=
        sum_le_sum fun a ha ↦ mul_le_mul_of_nonneg_right (hΔ a (ne_of_mem_erase ha)) (hnn a)
    _ ≤ ∑ a, gap ν a * ∫ ω, (pullCount A a n ω : ℝ) ∂P :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
          fun a _ _ ↦ mul_nonneg gap_nonneg (hnn a)

/-- If the arm `a₁` has gap at least `Δ`, the expected regret is at least `Δ E[T_{a₁}(n)]`. -/
theorem mul_integral_pullCount_le_integral_regret [Finite α] [DecidableEq α]
    (hA : ∀ t, Measurable (A t)) {a₁ : α} {Δ : ℝ} (hΔ : Δ ≤ gap ν a₁) (n : ℕ) :
    Δ * ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P ≤ ∫ ω, regret ν A n ω ∂P := by
  have := Fintype.ofFinite α
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount hA]
  have hnn (a : α) : 0 ≤ ∫ ω, (pullCount A a n ω : ℝ) ∂P :=
    integral_nonneg fun _ ↦ Nat.cast_nonneg _
  calc Δ * ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P
      ≤ gap ν a₁ * ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P := mul_le_mul_of_nonneg_right hΔ (hnn a₁)
    _ ≤ ∑ a, gap ν a * ∫ ω, (pullCount A a n ω : ℝ) ∂P :=
        single_le_sum (f := fun a ↦ gap ν a * ∫ ω, (pullCount A a n ω : ℝ) ∂P)
          (fun a _ ↦ mul_nonneg gap_nonneg (hnn a)) (mem_univ a₁)

end LowerBound

section GapFree

variable {α Ω : Type*} [DecidableEq α] [Fintype α] [MeasurableSpace α] [StandardBorelSpace α]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ν : Kernel α ℝ} {A : ℕ → Ω → α} {n : ℕ} {B C : ℝ}

/-- If every arm `a` with positive gap `Δ_a` is pulled at most `C / Δ_a ^ 2 + B` times in
expectation during the first `n` rounds, then for every threshold `δ > 0` the expected regret at
horizon `n` is at most `δ n + k C / δ + B ∑ a, Δ_a`, where `k` is the number of arms. -/
theorem integral_regret_le_mul_add_div_add_of_forall_integral_pullCount_le
    (hA : ∀ t, Measurable (A t)) (hC : 0 ≤ C) (hB : 0 ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (h_le : ∀ a, 0 < gap ν a → P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤ C / gap ν a ^ 2 + B) :
    P[regret ν A n] ≤ δ * n + Fintype.card α * C / δ + B * ∑ a, gap ν a := by
  -- Each arm contributes at most `δ` per pull if its gap is at most `δ`, and at most
  -- `C / Δ_a + B Δ_a ≤ C / δ + B Δ_a` otherwise.
  have h_arm a : gap ν a * P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤
      δ * P[fun ω ↦ (pullCount A a n ω : ℝ)] + C / δ + B * gap ν a := by
    have h_nonneg : 0 ≤ P[fun ω ↦ (pullCount A a n ω : ℝ)] := integral_nonneg fun _ ↦ by simp
    have h_gap : 0 ≤ gap ν a := gap_nonneg
    rcases le_or_gt (gap ν a) δ with h_gap_le | h_lt
    · have : 0 ≤ C / δ + B * gap ν a := by positivity
      nlinarith
    · have h_gap_pos : 0 < gap ν a := hδ.trans h_lt
      calc gap ν a * P[fun ω ↦ (pullCount A a n ω : ℝ)]
      _ ≤ gap ν a * (C / gap ν a ^ 2 + B) := by gcongr; exact h_le a h_gap_pos
      _ = C / gap ν a + B * gap ν a := by field_simp
      _ ≤ C / δ + B * gap ν a := by gcongr
      _ ≤ δ * P[fun ω ↦ (pullCount A a n ω : ℝ)] + C / δ + B * gap ν a := by
        have : 0 ≤ δ * P[fun ω ↦ (pullCount A a n ω : ℝ)] := by positivity
        linarith
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount hA]
  refine (sum_le_sum fun a _ ↦ h_arm a).trans_eq ?_
  simp only [sum_add_distrib, ← mul_sum, sum_integral_pullCount hA n, sum_const, card_univ,
    nsmul_eq_mul]
  ring

/-- **Gap-free regret bound** [LS, Theorem 7.2]. If every arm `a` with positive gap `Δ_a` is
pulled at most `C / Δ_a ^ 2 + B` times in expectation during the first `n` rounds, then the
expected regret at horizon `n` is at most `2 √(C k n) + B ∑ a, Δ_a`, where `k` is the number of
arms. -/
theorem integral_regret_le_two_mul_sqrt_add_of_forall_integral_pullCount_le
    (hA : ∀ t, Measurable (A t)) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (h_le : ∀ a, 0 < gap ν a → P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤ C / gap ν a ^ 2 + B) :
    P[regret ν A n] ≤ 2 * √(C * Fintype.card α * n) + B * ∑ a, gap ν a := by
  have h_bound {δ : ℝ} (hδ : 0 < δ) :=
    integral_regret_le_mul_add_div_add_of_forall_integral_pullCount_le hA hC hB hδ h_le
  have h_gap_sum : 0 ≤ B * ∑ a, gap ν a := mul_nonneg hB (sum_nonneg fun _ _ ↦ gap_nonneg)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [regret_eq_sum_gap, h_gap_sum]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases (mul_nonneg hC (Nat.cast_nonneg (Fintype.card α))).eq_or_lt' with hCk | hCk
  · -- If `C k = 0`, the bound `δ n + B ∑ a, Δ_a` holds for every `δ > 0`.
    rw [hCk, zero_mul, Real.sqrt_zero, mul_zero, zero_add]
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    refine (h_bound (div_pos hε hn')).trans_eq ?_
    rw [mul_comm (Fintype.card α : ℝ), hCk]
    field_simp
    ring
  · -- Otherwise, the threshold `δ = s / n` with `s = √(C k n)` gives `δ n = k C / δ = s`.
    set s := √(C * Fintype.card α * n) with hs_def
    have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos hCk hn')
    have hs_sq : s ^ 2 = C * Fintype.card α * n := Real.sq_sqrt (mul_pos hCk hn').le
    refine (h_bound (div_pos hs hn')).trans_eq ?_
    field_simp
    linear_combination -hs_sq

end GapFree

end LMLExplore.Bandits
