/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.FiniteActions

/-!
# Counting the pulls of each arm

Facts about LML's `pullCount` that hold for any sequence of actions `A : ℕ → Ω → α`.

## Main statements

* `pullCount_eq_zero_iff`, `pullCount_eq_one_iff`: characterisations of an arm pulled zero times
  and exactly once before a given round.
* `exists_pullCount_eq_zero_of_lt_card`: before round `Fintype.card α`, some arm has not been
  pulled yet.
* `pullCount_card_eq_one_of_forall_pullCount_action_eq_zero`: if each of the first
  `Fintype.card α` rounds plays an arm not pulled before, then every arm is pulled exactly once
  during those rounds.
* `integral_pullCount_eq_sum`: `E[T_a(n)] = ∑_{t < n} P(A t = a)`.
* `lintegral_pullCount_eq_ofReal_integral`: the expected number of pulls is the same whether
  computed as a lower Lebesgue integral in `ℝ≥0∞` or as a Bochner integral in `ℝ`.
* `sum_integral_pullCount`: the expected numbers of pulls of the arms before `n` add up to `n`.
* `exists_ne_integral_pullCount_le`: for every arm `a₁`, some other arm is pulled at most
  `n / (Fintype.card α - 1)` times in expectation before `n`.
-/

public section

open Finset Learning MeasureTheory
open scoped ENNReal

namespace LMLExplore

variable {α Ω : Type*} [DecidableEq α] {A : ℕ → Ω → α} {a : α} {n : ℕ} {ω : Ω}

/-- An arm has not been pulled before round `n` if and only if no round `s < n` played it. -/
lemma pullCount_eq_zero_iff : pullCount A a n ω = 0 ↔ ∀ s < n, A s ω ≠ a := by
  simp [pullCount, filter_eq_empty_iff]

/-- An arm has been pulled exactly once before round `n` if and only if exactly one round `s < n`
played it. -/
lemma pullCount_eq_one_iff :
    pullCount A a n ω = 1 ↔ ∃ s < n, A s ω = a ∧ ∀ t < n, A t ω = a → t = s := by
  simp [pullCount, card_eq_one, eq_singleton_iff_unique_mem, and_assoc]

variable [Fintype α]

/-- Before round `Fintype.card α`, some arm has not been pulled yet. -/
lemma exists_pullCount_eq_zero_of_lt_card (hn : n < Fintype.card α) :
    ∃ b, pullCount A b n ω = 0 := by
  by_contra! h0
  have : Fintype.card α ≤ n := calc
    Fintype.card α = ∑ _ : α, 1 := by simp
    _ ≤ ∑ a, pullCount A a n ω := sum_le_sum fun a _ ↦ Nat.one_le_iff_ne_zero.mpr (h0 a)
    _ = n := sum_pullCount
  omega

/-- If every round before `Fintype.card α` plays an arm that has not been pulled before, then every
arm is pulled exactly once during the first `Fintype.card α` rounds. -/
lemma pullCount_card_eq_one_of_forall_pullCount_action_eq_zero
    (hA : ∀ n < Fintype.card α, pullCount A (A n ω) n ω = 0) (a : α) :
    pullCount A a (Fintype.card α) ω = 1 := by
  -- The arms played during the first `Fintype.card α` rounds are pairwise distinct.
  have h_inj : Set.InjOn (A · ω) (range (Fintype.card α)) := by
    intro s hs t ht hst
    by_contra hne
    wlog hlt : s < t generalizing s t
    · exact this ht hs hst.symm (Ne.symm hne) (by omega)
    exact pullCount_eq_zero_iff.mp (hA t (by simpa using ht)) s hlt hst
  -- Hence every arm is played during those rounds, at a single round.
  have h_univ : (range (Fintype.card α)).image (A · ω) = univ :=
    eq_univ_of_card _ (by rw [card_image_of_injOn h_inj, card_range])
  obtain ⟨s, hs, rfl⟩ := mem_image.mp (h_univ ▸ mem_univ a)
  exact pullCount_eq_one_iff.mpr
    ⟨s, by simpa using hs, rfl, fun t ht hts ↦ h_inj (by simpa using ht) hs hts⟩

end LMLExplore

namespace LMLExplore

section Integral

variable {α Ω : Type*} [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {A : ℕ → Ω → α}

/-- The expected number of pulls of `a` before `n` is `∑_{t < n} P(A t = a)`. -/
theorem integral_pullCount_eq_sum [IsFiniteMeasure P] (hA : ∀ t, Measurable (A t)) (a : α)
    (n : ℕ) : ∫ ω, (pullCount A a n ω : ℝ) ∂P = ∑ t ∈ range n, P.real (A t ⁻¹' {a}) := by
  have hs (t : ℕ) : MeasurableSet (A t ⁻¹' {a}) := hA t (measurableSet_singleton a)
  have h (ω : Ω) : (pullCount A a n ω : ℝ) =
      ∑ t ∈ range n, (A t ⁻¹' {a}).indicator (fun _ ↦ (1 : ℝ)) ω := by
    rw [pullCount_eq_sum]
    push_cast
    refine sum_congr rfl fun t _ ↦ ?_
    by_cases hω : A t ω = a <;> simp [hω]
  simp_rw [h]
  rw [integral_finsetSum _ fun t _ ↦ (integrable_const (1 : ℝ)).indicator (hs t)]
  exact sum_congr rfl fun t _ ↦ by rw [integral_indicator_const _ (hs t), smul_eq_mul, mul_one]

/-- The expected number of pulls of `a` before `n` is the same whether computed as a lower Lebesgue
integral in `ℝ≥0∞` or as a Bochner integral in `ℝ`. -/
theorem lintegral_pullCount_eq_ofReal_integral [IsFiniteMeasure P] (hA : ∀ t, Measurable (A t))
    (a : α) (n : ℕ) :
    ∫⁻ ω, (pullCount A a n ω : ℝ≥0∞) ∂P = ENNReal.ofReal (∫ ω, (pullCount A a n ω : ℝ) ∂P) := by
  have hint : Integrable (fun ω ↦ (pullCount A a n ω : ℝ)) P :=
    .of_bound (by fun_prop) n (ae_of_all _ fun ω ↦ by simpa using pullCount_le a n ω)
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ Nat.cast_nonneg _)]
  simp

variable [Fintype α] [IsProbabilityMeasure P]

/-- The expected numbers of pulls of the arms before `n` add up to `n`. -/
theorem sum_integral_pullCount (hA : ∀ t, Measurable (A t)) (n : ℕ) :
    ∑ a, ∫ ω, (pullCount A a n ω : ℝ) ∂P = n := by
  rw [← integral_finsetSum _ fun a _ ↦ integrable_pullCount hA a n]
  simp [← Nat.cast_sum, sum_pullCount]

/-- For every arm `a₁`, some other arm is pulled at most `n / (Fintype.card α - 1)` times in
expectation before `n`. -/
theorem exists_ne_integral_pullCount_le [Nontrivial α] (hA : ∀ t, Measurable (A t)) (a₁ : α)
    (n : ℕ) : ∃ i ≠ a₁, ∫ ω, (pullCount A i n ω : ℝ) ∂P ≤ n / (Fintype.card α - 1) := by
  have hk : 1 < Fintype.card α := Fintype.one_lt_card
  have hne : (univ.erase a₁).Nonempty := by
    rw [← card_pos, card_erase_of_mem (mem_univ _), card_univ]
    omega
  obtain ⟨i, hi, hTi⟩ : ∃ i ∈ univ.erase a₁,
      ∫ ω, (pullCount A i n ω : ℝ) ∂P ≤ n / (Fintype.card α - 1) := by
    refine exists_le_of_sum_le hne ?_
    have hconst : ∑ _a ∈ univ.erase a₁, (n : ℝ) / (Fintype.card α - 1) = n := by
      rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul,
        Nat.cast_pred (by omega)]
      have : (Fintype.card α : ℝ) - 1 ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast hk.ne'
      field_simp
    rw [hconst, ← sum_integral_pullCount (P := P) hA n]
    exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
      fun a _ _ ↦ integral_nonneg fun _ ↦ Nat.cast_nonneg _
  exact ⟨i, ne_of_mem_erase hi, hTi⟩

end Integral

end LMLExplore
