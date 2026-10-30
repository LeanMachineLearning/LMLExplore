/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.SequentialLearning.FiniteActions
public import LeanMachineLearning.Online.Bandit.Regret

/-!
# Lower bounds on the gaps and the expected regret

Facts about LML's `gap` and `regret` of a bandit `ν : Kernel α ℝ` that hold for any sequence of
actions `A : ℕ → Ω → α`.

## Main statements

* `LMLExplore.Bandits.sub_le_gap`: the gap of an arm is at least its difference of mean with any
  other arm.
* `LMLExplore.Bandits.mul_sub_integral_pullCount_le_integral_regret`: if every arm other than `a₁`
  has gap at least `Δ`, the expected regret is at least `Δ (n - E[T_{a₁}(n)])`.
* `LMLExplore.Bandits.mul_integral_pullCount_le_integral_regret`: if the arm `a₁` has gap at least
  `Δ`, the expected regret is at least `Δ E[T_{a₁}(n)]`.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Bandits

namespace LMLExplore.Bandits

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

end LMLExplore.Bandits
