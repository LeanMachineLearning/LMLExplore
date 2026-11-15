/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic

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

end LMLExplore
