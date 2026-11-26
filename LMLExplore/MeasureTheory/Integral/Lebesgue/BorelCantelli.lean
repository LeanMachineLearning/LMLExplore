/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# A Borel–Cantelli lemma with a time of finite mean

By the Borel–Cantelli lemma (`MeasureTheory.ae_eventually_notMem`), if `∑' k, μ (s k)` is
finite, almost every point lies in only finitely many of the sets `s k`. If the weighted series
`∑' k, (k + 1) * μ (s k)` is finite, the time after which a point lies in none of them has a
finite mean: one plus the last index `k` with `x ∈ s k` is at most
`∑' k, (k + 1) * 𝟙{x ∈ s k}`, whose integral is the weighted series. For the sets where a random
walk is below a line, this is the integrability of its last exit time from the region below the
line.

## Main statements

* `MeasureTheory.exists_lintegral_le_tsum_forall_ge_notMem`: there is `N` with
  `∫⁻ x, N x ∂μ ≤ ∑' k, (k + 1) * μ (s k)` such that almost every `x` lies in no `s k` with
  `k ≥ N x`.

## Implementation notes

The construction of the time is adapted from the helper `exists_forall_ge_mul_le_sum` of
`EValuesResearch/Results/ConvexPieces.lean` (commit `83205cb`) in the paper project
`RemyDegenne/evalues_research`, stated here for arbitrary sets.
-/

public section

open Filter Set
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- **A Borel–Cantelli lemma with a time of finite mean.** If `∑' k, (k + 1) * μ (s k)` is finite,
there is a time `N x`, with `∫⁻ x, N x ∂μ ≤ ∑' k, (k + 1) * μ (s k)`, such that almost every `x`
lies in no `s k` with `k ≥ N x`. The sets need not be measurable. -/
theorem exists_lintegral_le_tsum_forall_ge_notMem (μ : Measure α) {s : ℕ → Set α}
    (hs : ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * μ (s k) ≠ ∞) :
    ∃ N : α → ℕ, ∫⁻ x, (N x : ℝ≥0∞) ∂μ ≤ ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * μ (s k) ∧
      ∀ᵐ x ∂μ, ∀ k ≥ N x, x ∉ s k := by
  classical
  -- measurable hulls of the sets, with the same measures
  set t : ℕ → Set α := fun k ↦ toMeasurable μ (s k)
  have ht (k : ℕ) : MeasurableSet (t k) := measurableSet_toMeasurable μ (s k)
  have hμt (k : ℕ) : μ (t k) = μ (s k) := measure_toMeasurable (s k)
  -- one plus the last index `k` with `x ∈ t k`, and `0` if there is none or no last one
  set N : α → ℕ := fun x ↦ sSup ((· + 1) '' {k | x ∈ t k})
  have hN (x : α) : (N x : ℝ≥0∞) ≤ ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * (t k).indicator 1 x := by
    by_cases hbdd : BddAbove ((· + 1) '' {k | x ∈ t k})
    · rcases Set.eq_empty_or_nonempty {k | x ∈ t k} with h0 | hne
      · simp [N, h0]
      obtain ⟨k, hk, hkN⟩ := Nat.sSup_mem (hne.image _) hbdd
      calc (N x : ℝ≥0∞) = ((k : ℝ≥0∞) + 1) * (t k).indicator 1 x := by
            simp [N, ← hkN, indicator_of_mem (show x ∈ t k from hk)]
        _ ≤ _ := le_tsum (fun k : ℕ ↦ ((k : ℝ≥0∞) + 1) * (t k).indicator 1 x) k
    · simp [N, Nat.sSup_of_not_bddAbove hbdd]
  refine ⟨N, ?_, ?_⟩
  · calc ∫⁻ x, (N x : ℝ≥0∞) ∂μ ≤ ∫⁻ x, ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * (t k).indicator 1 x ∂μ :=
          lintegral_mono hN
      _ = ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * μ (s k) := by
          rw [lintegral_tsum fun k ↦ ((measurable_one.indicator (ht k)).const_mul _).aemeasurable]
          refine tsum_congr fun k ↦ ?_
          rw [lintegral_const_mul _ (measurable_one.indicator (ht k)),
            lintegral_indicator_one (ht k), hμt]
  · -- by the Borel–Cantelli lemma, almost every point lies in finitely many `t k`
    have hsum : ∑' k, μ (t k) ≠ ∞ := by
      refine ne_top_of_le_ne_top hs (tsum_le_tsum fun k ↦ ?_)
      rw [hμt]
      exact le_mul_of_one_le_left' le_add_self
    filter_upwards [ae_eventually_notMem hsum] with x hx k hk hks
    obtain ⟨K, hK⟩ := eventually_atTop.1 hx
    have hbdd : BddAbove ((· + 1) '' {k | x ∈ t k}) := by
      refine ⟨K, ?_⟩
      rintro _ ⟨j, hj, rfl⟩
      by_contra hlt
      exact hK j (by simp only [not_le] at hlt; omega) hj
    have : k + 1 ≤ N x := le_csSup hbdd ⟨k, subset_toMeasurable μ (s k) hks, rfl⟩
    omega

end MeasureTheory
