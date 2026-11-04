/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.Regret
public import LMLExplore.NumberTheory.Harmonic.Basic

/-!
# The complexity `H₂` of best arm identification

The fixed-budget guarantees of [ABM10] for best arm identification are stated in terms of the
gaps `Δ_b` of the arms of a bandit `ν` through the complexity `H₂ = max_i i Δ_(i)⁻²`, where
`Δ_(1) ≤ ⋯ ≤ Δ_(K)` are the gaps sorted increasingly, and through the constant
`log‾ K = 1 / 2 + ∑_{i = 2}^K 1 / i`.

## Main definitions

In the namespace `LMLExplore.Identification`:

* `complexityTwo ν`: the complexity `H₂` of best arm identification, written without sorting the
  gaps: the largest `r_b / Δ_b²` over the arms `b`, with `r_b` the number of arms whose gap is at
  most `Δ_b`.
* `logBar K`: the constant `log‾ K = 1 / 2 + ∑_{i = 2}^K 1 / i`.

## Main statements

* `le_complexityTwo`, `complexityTwo_le`: `H₂` is the least upper bound of the `r_b / Δ_b²`.
* `complexityTwo_nonneg`, `complexityTwo_pos`: `H₂ ≥ 0`, and `H₂ > 0` when some gap is positive.
* `sub_card_div_complexityTwo_le_gap_sq`: an arm of a set `B` of arms with the largest gaps among
  the arms other than the unique best arm has `Δ_b² ≥ (K + 1 - #B) / H₂`.
* `logBar_eq_sum`, `one_half_le_logBar`: `log‾ K` as a sum, and `log‾ K ≥ 1 / 2`.

## References

* [ABM10] J.-Y. Audibert, S. Bubeck and R. Munos, *Best arm identification in multi-armed
  bandits*, COLT 2010.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning

namespace LMLExplore.Identification

/-! ### The constant `log‾ K` -/

/-- The constant `log‾ K = 1 / 2 + ∑_{i = 2}^K 1 / i` of [ABM10], written with the harmonic number
`H_K = ∑_{i = 1}^K 1 / i` as `H_K - 1 / 2`. -/
noncomputable def logBar (K : ℕ) : ℝ := harmonic K - 1 / 2

lemma logBar_def (K : ℕ) : logBar K = harmonic K - 1 / 2 := (rfl)

lemma logBar_eq_sum {K : ℕ} (hK : K ≠ 0) :
    logBar K = ∑ j ∈ range (K - 1), ((K - j : ℝ))⁻¹ + 1 / 2 := by
  rw [sum_range_inv_sub_eq_harmonic_sub_one hK, logBar]
  ring

lemma one_half_le_logBar {K : ℕ} (hK : K ≠ 0) : 1 / 2 ≤ logBar K := by
  rw [logBar_eq_sum hK, le_add_iff_nonneg_left]
  refine sum_nonneg fun j hj ↦ inv_nonneg.2 (sub_nonneg.2 ?_)
  exact_mod_cast (mem_range.1 hj).le.trans (Nat.sub_le K 1)

/-! ### The complexity `H₂` -/

variable {α : Type*} [MeasurableSpace α] [Fintype α] {ν : Kernel α ℝ}

/-- The complexity `H₂` of best arm identification [ABM10]: the largest `r_b / Δ_b²` over the
arms `b`, where `Δ_b` is the gap of `b` and `r_b` is the number of arms whose gap is at most `Δ_b`.
The term of an arm of gap zero is `0`. When the best arm is unique and `Δ_(1) ≤ ⋯ ≤ Δ_(K)` are the
gaps sorted increasingly, with the gap `0` of the best arm replaced by the smallest gap of the
other arms, this is `max_i i Δ_(i)⁻²`: within a block of equal gaps, `i Δ_(i)⁻²` is largest at
the last index of the block, which is `r_b` for the arms `b` of the block. -/
noncomputable def complexityTwo (ν : Kernel α ℝ) : ℝ :=
  ⨆ b, (#{c | Bandits.gap ν c ≤ Bandits.gap ν b} : ℝ) / Bandits.gap ν b ^ 2

lemma complexityTwo_def (ν : Kernel α ℝ) :
    complexityTwo ν = ⨆ b, (#{c | Bandits.gap ν c ≤ Bandits.gap ν b} : ℝ) / Bandits.gap ν b ^ 2 :=
  (rfl)

lemma le_complexityTwo (ν : Kernel α ℝ) (b : α) :
    (#{c | Bandits.gap ν c ≤ Bandits.gap ν b} : ℝ) / Bandits.gap ν b ^ 2 ≤ complexityTwo ν :=
  le_ciSup (Set.finite_range fun b ↦
    (#{c | Bandits.gap ν c ≤ Bandits.gap ν b} : ℝ) / Bandits.gap ν b ^ 2).bddAbove b

lemma complexityTwo_le [Nonempty α] {x : ℝ}
    (h : ∀ b, (#{c | Bandits.gap ν c ≤ Bandits.gap ν b} : ℝ) / Bandits.gap ν b ^ 2 ≤ x) :
    complexityTwo ν ≤ x :=
  ciSup_le h

lemma complexityTwo_nonneg (ν : Kernel α ℝ) : 0 ≤ complexityTwo ν :=
  Real.iSup_nonneg fun _ ↦ by positivity

/-- `H₂` is positive as soon as some arm has a positive gap. -/
lemma complexityTwo_pos {b : α} (hb : 0 < Bandits.gap ν b) : 0 < complexityTwo ν :=
  (div_pos (by exact_mod_cast card_pos.2 ⟨b, by simp⟩) (pow_pos hb 2)).trans_le
    (le_complexityTwo ν b)

/-- If `B` is a set of arms other than the unique best arm `a'` whose gaps are at least those of
the other arms `c ≠ a'`, and `b ∈ B`, then `Δ_b² ≥ (K + 1 - #B) / H₂`: the `K + 1 - #B` arms
outside `B`, together with `b`, have gaps at most `Δ_b`. -/
lemma sub_card_div_complexityTwo_le_gap_sq [DecidableEq α] {a' : α}
    (ha' : ∀ b ≠ a', (ν b)[id] < (ν a')[id]) {B : Finset α} (hB : B ⊆ univ.erase a')
    (h_top : ∀ b ∈ B, ∀ c ∈ univ.erase a' \ B, Bandits.gap ν c ≤ Bandits.gap ν b)
    {b : α} (hb : b ∈ B) :
    ((Fintype.card α : ℝ) + 1 - #B) / complexityTwo ν ≤ Bandits.gap ν b ^ 2 := by
  have : Nonempty α := ⟨a'⟩
  have hΔ : 0 < Bandits.gap ν b := Bandits.gap_pos_of_forall_lt ha' (mem_erase.1 (hB hb)).1
  -- The arms outside `B`, and `b`, have gaps at most that of `b`.
  have h_rank : #(B.erase b)ᶜ ≤ #{c | Bandits.gap ν c ≤ Bandits.gap ν b} := by
    refine card_le_card fun c hc ↦ ?_
    rw [mem_compl, mem_erase, not_and_or, not_not] at hc
    rw [mem_filter_univ]
    rcases hc with rfl | hc
    · exact le_rfl
    rcases eq_or_ne c a' with rfl | hca
    · rw [← Bandits.bestArm_eq_of_forall_lt ha', Bandits.gap_bestArm]
      exact Bandits.gap_nonneg
    · exact h_top b hb c (mem_sdiff.2 ⟨mem_erase.2 ⟨hca, mem_univ c⟩, hc⟩)
  rw [card_compl, card_erase_of_mem hb] at h_rank
  have h_rank' : (Fintype.card α : ℝ) + 1 - #B ≤ #{c | Bandits.gap ν c ≤ Bandits.gap ν b} := by
    have hBK : #B ≤ Fintype.card α := card_le_univ B
    have hB1 : 1 ≤ #B := card_pos.2 ⟨b, hb⟩
    calc (Fintype.card α : ℝ) + 1 - #B = (Fintype.card α - (#B - 1) : ℕ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub hB1]
          ring
      _ ≤ _ := by exact_mod_cast h_rank
  have hH := le_complexityTwo ν b
  rw [div_le_iff₀ (pow_pos hΔ 2)] at hH
  rw [div_le_iff₀ (complexityTwo_pos hΔ)]
  nlinarith

end LMLExplore.Identification
