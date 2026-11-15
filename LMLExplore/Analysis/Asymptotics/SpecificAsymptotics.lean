/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Comparison of Cesàro averages of eventually ordered sequences

Averages `(1/n) ∑ i < n, y i` ignore finitely many terms (`Filter.Tendsto.cesaro`), so an
eventual inequality `z i ≤ y i` between two real sequences passes to their averages up to a
sequence tending to `0`. This gives lower and upper bounds on the averages of `y` from the limits
of the averages of `z`.

## Main statements

* `LMLExplore.exists_tendsto_zero_add_average_le`: if `z i ≤ y i` eventually, the average of `y`
  is at least the average of `z` plus a sequence tending to `0`.
* `LMLExplore.eventually_lt_average_of_eventually_le`,
  `LMLExplore.eventually_average_lt_of_eventually_le`: if `z i ≤ y i` (respectively `y i ≤ z i`)
  eventually and the averages of `z` tend to `V > c` (respectively `U < c`), the averages of `y`
  are eventually larger (respectively smaller) than `c`.
* `LMLExplore.tendsto_average_atTop_of_eventually_le`: if `z i ≤ y i` eventually and the averages
  of `z` tend to `+∞`, so do the averages of `y`.
-/

public section

open Filter Topology

namespace LMLExplore

/-- Averages ignore finitely many terms: if `z i ≤ y i` eventually, the average of `y` is at least
the average of `z` plus a sequence tending to `0`. -/
theorem exists_tendsto_zero_add_average_le {y z : ℕ → ℝ} (h : ∀ᶠ i in atTop, z i ≤ y i) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ n : ℕ,
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, z i + r n ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, y i := by
  refine ⟨fun n ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, min (y i - z i) 0,
    Tendsto.cesaro (tendsto_const_nhds.congr' ?_), fun n ↦ ?_⟩
  · filter_upwards [h] with i hi
    exact (min_eq_right (sub_nonneg.2 hi)).symm
  · rw [← mul_add, ← Finset.sum_add_distrib]
    gcongr with i
    linarith [min_le_left (y i - z i) 0]

/-- If `z i ≤ y i` eventually and the averages of `z` tend to `V > c`, the averages of `y` are
eventually larger than `c`. -/
theorem eventually_lt_average_of_eventually_le {y z : ℕ → ℝ} (h : ∀ᶠ i in atTop, z i ≤ y i)
    {V c : ℝ} (hz : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, z i) atTop (𝓝 V))
    (hc : c < V) : ∀ᶠ n : ℕ in atTop, c < (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, y i := by
  obtain ⟨r, hr, hle⟩ := exists_tendsto_zero_add_average_le h
  have hlim := hz.add hr
  rw [add_zero] at hlim
  filter_upwards [hlim.eventually (lt_mem_nhds hc)] with n hn
  exact hn.trans_le (hle n)

/-- If `y i ≤ z i` eventually and the averages of `z` tend to `U < c`, the averages of `y` are
eventually smaller than `c`. -/
theorem eventually_average_lt_of_eventually_le {y z : ℕ → ℝ} (h : ∀ᶠ i in atTop, y i ≤ z i)
    {U c : ℝ} (hz : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, z i) atTop (𝓝 U))
    (hc : U < c) : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, y i < c := by
  obtain ⟨r, hr, hle⟩ := exists_tendsto_zero_add_average_le h
  have hlim := hz.sub hr
  rw [sub_zero] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds hc)] with n hn
  linarith [hle n]

/-- If `z i ≤ y i` eventually and the averages of `z` tend to `+∞`, so do the averages of `y`. -/
theorem tendsto_average_atTop_of_eventually_le {y z : ℕ → ℝ} (h : ∀ᶠ i in atTop, z i ≤ y i)
    (hz : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, z i) atTop atTop) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, y i) atTop atTop := by
  obtain ⟨r, hr, hle⟩ := exists_tendsto_zero_add_average_le h
  exact tendsto_atTop_mono hle (hz.atTop_add hr)

end LMLExplore
