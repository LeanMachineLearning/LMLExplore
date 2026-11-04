/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Averages of points close to a convex set

The average of points of a convex set `C` lies in `C`, so the average of points `ε`-close to `C`
is `ε`-close to `C`. We prove a version that allows finitely many initial points to be far from
`C`, provided they are bounded: this is the step of the analysis of C-tracking where the targets,
which are eventually close to the convex set of the optimal allocations, are averaged
[DK19, proof of Lemma 6].

## Main statements

* `Convex.exists_mem_norm_sum_sub_smul_le`: if `v s` is `ε`-close to the convex set `C` for
  `t₀ ≤ s < T`, and `‖v s‖ ≤ A` for `s < t₀`, then some `c ∈ C` satisfies
  `‖∑_{s < T} v s - T • c‖ ≤ (A + B) t₀ + ε (T - t₀)`, where `B` bounds the norms on `C`.

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, Lemma 6.
-/

public section

open Finset Metric

namespace Convex

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}

/-- **Averages of points close to a convex set are close to it.** Let `v s` be `ε`-close to the
convex set `C` for `t₀ ≤ s < T`, let `‖v s‖ ≤ A` for `s < t₀` and let `‖c‖ ≤ B` for `c ∈ C`. Then
some `c ∈ C` satisfies `‖∑_{s < T} v s - T • c‖ ≤ (A + B) t₀ + ε (T - t₀)`: the average of the
first `T` points is at distance at most `((A + B) t₀ + ε (T - t₀)) / T` from `C`. -/
theorem exists_mem_norm_sum_sub_smul_le (hC : Convex ℝ C) (hC_ne : C.Nonempty) {v : ℕ → E}
    {t₀ T : ℕ} {A B ε : ℝ} (hT : t₀ ≤ T) (hA : ∀ s < t₀, ‖v s‖ ≤ A) (hB : ∀ c ∈ C, ‖c‖ ≤ B)
    (hε : ∀ s, t₀ ≤ s → s < T → v s ∈ thickening ε C) :
    ∃ c ∈ C, ‖∑ s ∈ range T, v s - (T : ℝ) • c‖ ≤ (A + B) * t₀ + ε * (T - t₀) := by
  obtain ⟨c₀, hc₀⟩ := hC_ne
  obtain rfl | hT0 := eq_or_ne T 0
  · obtain rfl := Nat.le_zero.1 hT
    exact ⟨c₀, hc₀, by simp⟩
  have hT' : (0 : ℝ) < T := Nat.cast_pos.2 (Nat.pos_of_ne_zero hT0)
  -- Points `c s` of `C`, `ε`-close to `v s` for `t₀ ≤ s < T`.
  have h_near (s : ℕ) : ∃ c ∈ C, t₀ ≤ s → s < T → dist (v s) c < ε := by
    by_cases hs : t₀ ≤ s ∧ s < T
    · obtain ⟨c, hc, hd⟩ := mem_thickening_iff.1 (hε s hs.1 hs.2)
      exact ⟨c, hc, fun _ _ ↦ hd⟩
    · exact ⟨c₀, hc₀, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hs⟩
  choose c hcC hc using h_near
  -- Their average is in `C`, and `∑ v s - T • (T⁻¹ ∑ c s) = ∑ (v s - c s)`.
  refine ⟨∑ s ∈ range T, (T : ℝ)⁻¹ • c s, hC.sum_mem (fun _ _ ↦ by positivity)
    (by rw [sum_const, card_range, nsmul_eq_mul, mul_inv_cancel₀ hT'.ne']) fun s _ ↦ hcC s, ?_⟩
  rw [smul_sum]
  simp only [smul_inv_smul₀ hT'.ne']
  rw [← sum_sub_distrib, ← sum_range_add_sum_Ico _ hT]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans ?_)
    ((norm_sum_le _ _).trans ?_))
  · calc ∑ s ∈ range t₀, ‖v s - c s‖
    _ ≤ ∑ s ∈ range t₀, (A + B) := sum_le_sum fun s hs ↦
      (norm_sub_le _ _).trans (add_le_add (hA s (mem_range.1 hs)) (hB _ (hcC s)))
    _ = (A + B) * t₀ := by rw [sum_const, card_range, nsmul_eq_mul, mul_comm]
  · calc ∑ s ∈ Ico t₀ T, ‖v s - c s‖
    _ ≤ ∑ s ∈ Ico t₀ T, ε := sum_le_sum fun s hs ↦ by
      rw [← dist_eq_norm]
      exact (hc s (Finset.mem_Ico.1 hs).1 (Finset.mem_Ico.1 hs).2).le
    _ = ε * (T - t₀) := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hT, mul_comm]

end Convex
