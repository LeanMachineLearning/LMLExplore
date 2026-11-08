/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.UnitInterval

/-!
# The coercion from the unit interval to `ℝ≥0`, and uniform grids on intervals

A uniform grid of `K + 1` points `c - Δ + 2 Δ k / K`, `k ≤ K`, on an interval `[c - Δ, c + Δ]` of
a linearly ordered field is a `2 Δ / K`-net of this interval. As `Set.projIcc a b` is a
contraction (`Set.abs_projIcc_sub_projIcc`), the grid clipped to `[a, b]` is still a `2 Δ / K`-net
of the points of `[a, b]` within `Δ` of `c`, now with all its points in `[a, b]`.

## Main statements

* `unitInterval.toNNReal_eq_zero`: `toNNReal p = 0 ↔ p = 0`.
* `exists_abs_sub_grid_le`: a uniform grid of `K + 1` points on `[c - Δ, c + Δ]` is a
  `2 Δ / K`-net of this interval.
* `exists_abs_sub_projIcc_grid_le`: the same grid, clipped to `[a, b]`, is a `2 Δ / K`-net of the
  points of `[a, b]` within `Δ` of `c`.
-/

public section

namespace unitInterval

/-- The coercion `unitInterval.toNNReal` vanishes exactly at `0`. -/
@[simp]
lemma toNNReal_eq_zero {p : I} : toNNReal p = 0 ↔ p = 0 := by
  rw [← NNReal.coe_eq_zero, coe_toNNReal, Set.Icc.coe_eq_zero]

end unitInterval

section Grid

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [FloorSemiring 𝕜]
  {x c Δ : 𝕜} {K : ℕ}

/-- A uniform grid of `K + 1` points on `[c - Δ, c + Δ]` is a `2 Δ / K`-net of this interval. -/
theorem exists_abs_sub_grid_le (hx : |x - c| ≤ Δ) (hK : 0 < K) :
    ∃ k : Fin (K + 1), |x - (c - Δ + 2 * Δ * (k : ℕ) / K)| ≤ 2 * Δ / K := by
  have hK' : (0 : 𝕜) < K := by exact_mod_cast hK
  rcases ((abs_nonneg _).trans hx).eq_or_lt with rfl | hΔ
  · exact ⟨0, by simpa using hx⟩
  obtain ⟨hx₁, hx₂⟩ := abs_le.1 hx
  -- the position of `x` in the grid, in `[0, K]`
  set t := (x - c + Δ) * K / (2 * Δ)
  have ht₀ : 0 ≤ t := div_nonneg (mul_nonneg (by linarith) hK'.le) (by positivity)
  have htK : t ≤ K := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨⟨⌊t⌋₊, Nat.lt_succ_of_le ((Nat.floor_le_floor htK).trans (Nat.floor_natCast K).le)⟩, ?_⟩
  have h_eq : x - (c - Δ + 2 * Δ * (⌊t⌋₊ : 𝕜) / K) = 2 * Δ / K * (t - ⌊t⌋₊) := by
    simp only [t]
    field_simp
    ring
  rw [h_eq, abs_mul, abs_of_pos (by positivity)]
  have h₁ := Nat.floor_le ht₀
  have h₂ := Nat.lt_floor_add_one t
  calc 2 * Δ / K * |t - ⌊t⌋₊| ≤ 2 * Δ / K * 1 := by
        gcongr
        rw [abs_le]
        constructor <;> linarith
    _ = 2 * Δ / K := mul_one _

/-- A uniform grid of `K + 1` points on `[c - Δ, c + Δ]`, clipped to `[a, b]`, is a `2 Δ / K`-net
of the points of `[a, b]` within `Δ` of `c`. -/
theorem exists_abs_sub_projIcc_grid_le {a b : 𝕜} (hab : a ≤ b) (hx : x ∈ Set.Icc a b)
    (hxc : |x - c| ≤ Δ) (hK : 0 < K) :
    ∃ k : Fin (K + 1), |x - Set.projIcc a b hab (c - Δ + 2 * Δ * (k : ℕ) / K)| ≤ 2 * Δ / K := by
  obtain ⟨k, hk⟩ := exists_abs_sub_grid_le hxc hK
  refine ⟨k, ?_⟩
  -- clipping to `[a, b]` does not increase the distance to `x ∈ [a, b]`
  have h_clip := Set.abs_projIcc_sub_projIcc hab (c := x) (d := c - Δ + 2 * Δ * (k : ℕ) / K)
  rw [Set.projIcc_of_mem hab hx] at h_clip
  exact h_clip.trans hk

end Grid
