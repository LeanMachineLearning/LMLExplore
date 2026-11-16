/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Power-bounded elements of a seminormed ring

An element `a` of a seminormed ring is *power bounded* when the norms `‖a ^ n‖` of its powers are
bounded. For a continuous linear operator `T : E →L[𝕜] E` these are operator norms, and power
boundedness is the hypothesis of Yosida's mean ergodic theorem
(`LMLExplore.IsPowerBounded.exists_tendsto_birkhoffAverage_iff`).

This is the norm-bounded notion. Tau Ceti's `TauCeti.Huber.IsPowerBounded` is the notion for
topological rings, where the set of powers must be absorbed by every neighbourhood of zero.

## Main definitions

* `LMLExplore.IsPowerBounded`: the norms of the powers of `a` are bounded.

## Main statements

* `LMLExplore.isPowerBounded_iff`: `a` is power bounded iff some constant bounds `‖a ^ n‖`.
* `LMLExplore.IsPowerBounded.of_norm_le_one`: an element of norm at most `1` is power bounded.
* `LMLExplore.IsPowerBounded.isUnit_one_sub_smul`: in a normed algebra with summable geometric
  series (for instance a Banach algebra), `1 - γ • a` is invertible for power-bounded `a` and
  `‖γ‖ < 1`.
-/

public section

namespace LMLExplore

variable {R : Type*} [SeminormedRing R] {a : R}

/-- An element of a seminormed ring is *power bounded* when the norms of its powers are
bounded. -/
def IsPowerBounded (a : R) : Prop :=
  BddAbove (Set.range fun n : ℕ ↦ ‖a ^ n‖)

/-- `a` is power bounded iff some constant bounds the norms of all its powers. -/
lemma isPowerBounded_iff : IsPowerBounded a ↔ ∃ C, ∀ n, ‖a ^ n‖ ≤ C := by
  simp [IsPowerBounded, bddAbove_def]

namespace IsPowerBounded

/-- An element of norm at most `1` is power bounded. -/
lemma of_norm_le_one (h : ‖a‖ ≤ 1) : IsPowerBounded a := by
  refine isPowerBounded_iff.2 ⟨max ‖(1 : R)‖ 1, fun n ↦ ?_⟩
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact (norm_pow_le' a hn).trans ((pow_le_one₀ (norm_nonneg a) h).trans (le_max_right _ _))

/-- `⨆ k, ‖a ^ k‖` bounds the norm of every power of a power-bounded `a`. -/
lemma norm_pow_le (ha : IsPowerBounded a) (n : ℕ) : ‖a ^ n‖ ≤ ⨆ k, ‖a ^ k‖ :=
  le_ciSup ha n

/-- The bound `⨆ k, ‖a ^ k‖` of a power-bounded `a` is nonnegative. -/
lemma iSup_norm_pow_nonneg (ha : IsPowerBounded a) : 0 ≤ ⨆ k, ‖a ^ k‖ :=
  (norm_nonneg _).trans (ha.norm_pow_le 0)

end IsPowerBounded

/-- In a normed algebra with summable geometric series (for instance a Banach algebra), `1 - γ • a`
is invertible for a power-bounded `a` and `‖γ‖ < 1`. For a power-bounded operator `T`, this is the
invertibility of the resolvent `1 - γ T` at every discount factor `γ ∈ [0, 1)`. -/
theorem IsPowerBounded.isUnit_one_sub_smul {𝕜 R : Type*} [NormedField 𝕜] [NormedRing R]
    [NormedAlgebra 𝕜 R] [HasSummableGeomSeries R] {a : R} (ha : IsPowerBounded a) {γ : 𝕜}
    (hγ : ‖γ‖ < 1) : IsUnit (1 - γ • a) := by
  -- Some power `(γ • a) ^ N` has norm `< 1`, and
  -- `1 - (γ • a) ^ N = (1 - γ • a) ∑ i < N, (γ • a) ^ i` is a product of commuting factors.
  obtain ⟨N, hN⟩ := (((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg γ) hγ).mul_const
    (⨆ k, ‖a ^ k‖)).eventually (gt_mem_nhds (by simp : (0 : ℝ) * (⨆ k, ‖a ^ k‖) < 1))).exists
  have hx : ‖(γ • a) ^ N‖ < 1 := by
    rw [smul_pow]
    refine (norm_smul_le _ _).trans_lt (lt_of_le_of_lt ?_ hN)
    rw [norm_pow]
    exact mul_le_mul_of_nonneg_left (ha.norm_pow_le N) (by positivity)
  have hunit := isUnit_one_sub_of_norm_lt_one hx
  rw [← mul_neg_geom_sum] at hunit
  exact ((Commute.sum_right _ _ _ fun i _ ↦
    (Commute.one_left _).sub_left (Commute.self_pow _ i)).isUnit_mul_iff.1 hunit).1

end LMLExplore
