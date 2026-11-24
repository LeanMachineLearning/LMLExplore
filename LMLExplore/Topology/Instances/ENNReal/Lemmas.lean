/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Order.SuccPred.Int

/-!
# Suprema of `f x / x` over a dense set, ratios to small thresholds, and telescoping series

For `f : ℝ≥0∞ → ℝ≥0∞` monotone on an open interval `Ioo a b`, the supremum of `f x / x` over
`x ∈ Ioo a b` is already the supremum over the points of any dense set: the value at `x` is
approached by the values at points `c > x` of the dense set, since `f c ≥ f x` and `f x / c`
tends to `f x / x` as `c` decreases to `x`. With a countable dense set, this turns the supremum
over an interval, an uncountable family, into a countable one, which is what makes it measurable
when `f` depends measurably on a parameter; post-hoc valid families of tests, indexed by their
levels, are the main instance.

For a family of masses `a i ≤ 1` and values `f i`, the infimum of the ratios `f i / a i` is
zero exactly when, as the threshold `δ` decreases to `0`, the infimum of `f i / δ` over the indices
with `a i > δ` has `liminf` zero. This is the step between the two forms of the admissibility
criterion of Ramdas and Wang for e-variables, one dividing by the mass `a i` itself and the other
by a threshold below it.

The increments `c (j + 1) - c j` of a nondecreasing `c : ℤ → ℝ≥0∞` sum to at most the supremum
of `c`: the finite sums over the windows `[a, a + n)` telescope. Bounds on a probability by a sum
over a geometric grid `ρ ^ j`, `j : ℤ`, of increments of a nondecreasing ratio are the main
instance.

## Main statements

* `ENNReal.biSup_Ioo_div_eq_biSup_inter_of_dense`: for `f` monotone on `Ioo a b` and a dense set
  `D`, `⨆ x ∈ Ioo a b, f x / x = ⨆ x ∈ Ioo a b ∩ D, f x / x`.
* `ENNReal.liminf_iInf_div_eq_zero_iff`: for `a i ≤ 1`,
  `liminf (fun δ ↦ ⨅ i ∈ s, ⨅ (_ : δ < a i), f i / δ) (𝓝[>] 0) = 0` exactly when
  `⨅ i ∈ s, ⨅ (_ : a i ≠ 0), f i / a i = 0`.
* `ENNReal.tsum_sub_le_iSup`: for `c : ℤ → ℝ≥0∞` nondecreasing,
  `∑' j, (c (j + 1) - c j) ≤ ⨆ j, c j`.
-/

public section

open Filter Set Topology
open scoped ENNReal

namespace ENNReal

/-- For `f` monotone on an open interval `Ioo a b`, the supremum of `f x / x` over the interval is
the supremum over the points of the interval in any dense set `D`, for instance the rational
points. -/
theorem biSup_Ioo_div_eq_biSup_inter_of_dense {f : ℝ≥0∞ → ℝ≥0∞} {a b : ℝ≥0∞} {D : Set ℝ≥0∞}
    (hD : Dense D) (hf : MonotoneOn f (Ioo a b)) :
    ⨆ x ∈ Ioo a b, f x / x = ⨆ x ∈ Ioo a b ∩ D, f x / x := by
  refine le_antisymm (iSup₂_le fun x hx ↦ le_of_forall_lt fun r hr ↦ ?_)
    (biSup_mono fun _ hx ↦ hx.1)
  -- `c ↦ f x / c` is continuous at `x`, so it stays above `r` on a neighbourhood of `x`
  have h_tendsto : Tendsto (fun c ↦ f x / c) (𝓝 x) (𝓝 (f x / x)) :=
    ENNReal.Tendsto.const_div tendsto_id (Or.inl (ne_top_of_lt hx.2))
  obtain ⟨l, u, hxlu, hlu⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨a, hx.1⟩ ⟨b, hx.2⟩).1
    ((h_tendsto.eventually (lt_mem_nhds hr)).and (Iio_mem_nhds hx.2))
  -- a point `c` of `D` slightly to the right of `x` does the job
  obtain ⟨c, hcD, hc⟩ := hD.exists_between hxlu.2
  have hc_mem : c ∈ Ioo a b := ⟨hx.1.trans hc.1, (hlu ⟨hxlu.1.trans hc.1, hc.2⟩).2⟩
  calc r < f x / c := (hlu ⟨hxlu.1.trans hc.1, hc.2⟩).1
    _ ≤ f c / c := by
      gcongr
      exact hf hx hc_mem hc.1.le
    _ ≤ ⨆ x ∈ Ioo a b ∩ D, f x / x := le_iSup₂_of_le c ⟨hc_mem, hcD⟩ le_rfl

/-- For masses `a i ≤ 1`, the infimum of the ratios `f i / a i` over the indices of `s` with
`a i ≠ 0` is zero exactly when the infimum of `f i / δ` over the indices with `δ < a i` has
`liminf` zero as `δ` decreases to `0`. Both sides fail when no `a i` is positive, since an
infimum over no index is `∞`. Without a bound on the masses, the ratios can tend to zero along
masses `a i → ∞` while the values `f i` stay away from zero; then the `liminf` is `∞`. -/
theorem liminf_iInf_div_eq_zero_iff {ι : Type*} {s : Set ι} {a f : ι → ℝ≥0∞}
    (ha : ∀ i ∈ s, a i ≤ 1) :
    liminf (fun δ ↦ ⨅ i ∈ s, ⨅ (_ : δ < a i), f i / δ) (𝓝[>] 0) = 0 ↔
      ⨅ i ∈ s, ⨅ (_ : a i ≠ 0), f i / a i = 0 := by
  constructor
  · -- dividing by a threshold below the mass gives a larger ratio
    refine fun h ↦ nonpos_iff_eq_zero.1 ((le_liminf_of_le (h := eventually_nhdsWithin_of_forall
      fun (δ : ℝ≥0∞) (hδ : δ ∈ Ioi 0) ↦ le_iInf₂ fun i hi ↦ le_iInf fun hδi ↦ ?_)).trans h.le)
    exact iInf₂_le_of_le i hi (iInf_le_of_le (hδ.out.trans hδi).ne'
      (ENNReal.div_le_div_left hδi.le _))
  intro h
  -- otherwise the infimum over the indices above a small threshold stays above some `c * δ`
  by_contra h_ne
  obtain ⟨c, hc0, hc⟩ := exists_between (pos_iff_ne_zero.2 h_ne)
  obtain ⟨u, hu0, hu⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' zero_lt_one).1
    (eventually_lt_of_lt_liminf hc)
  rw [mem_Ioi] at hu0
  set v := min u 1 with hv
  have hv0 : v ≠ 0 := (lt_min hu0 zero_lt_one).ne'
  have hv1 : v ≠ ∞ := ne_top_of_le_ne_top one_ne_top (min_le_right _ _)
  -- so every ratio is at least `c * v / 2`, by the threshold `v * a i / 2`
  refine (ENNReal.div_pos (mul_ne_zero hc0.ne' hv0) (ofNat_ne_top (n := 2))).ne'
    (nonpos_iff_eq_zero.1 ((le_iInf₂ fun i hi ↦ le_iInf fun hai ↦ ?_).trans h.le))
  have hai1 : a i ≠ ∞ := ne_top_of_le_ne_top one_ne_top (ha i hi)
  set δ := v * a i / 2 with hδ
  have hδ0 : δ ≠ 0 := (ENNReal.div_pos (mul_ne_zero hv0 hai) (ofNat_ne_top (n := 2))).ne'
  have hδ1 : δ ≠ ∞ := ENNReal.div_ne_top (mul_ne_top hv1 hai1) two_ne_zero
  have hδu : δ < u := calc
    δ ≤ v * 1 / 2 := by rw [hδ]; gcongr; exact ha i hi
    _ < v := by rw [mul_one]; exact ENNReal.half_lt_self hv0 hv1
    _ ≤ u := min_le_left _ _
  have hδa : δ < a i := calc
    δ ≤ 1 * a i / 2 := by rw [hδ]; gcongr; exact min_le_right _ _
    _ < a i := by rw [one_mul]; exact ENNReal.half_lt_self hai hai1
  have hcδ : c ≤ f i / δ :=
    (hu ⟨pos_iff_ne_zero.2 hδ0, hδu⟩).le.trans (iInf₂_le_of_le i hi (iInf_le _ hδa))
  rw [ENNReal.le_div_iff_mul_le (.inl hai) (.inl hai1)]
  calc c * v / 2 * a i = c * δ := by simp only [hδ, div_eq_mul_inv]; ring
    _ ≤ f i := (ENNReal.le_div_iff_mul_le (.inl hδ0) (.inl hδ1)).1 hcδ

/-- **A telescoping series over the integers**: the increments of a nondecreasing
`c : ℤ → ℝ≥0∞` sum to at most the supremum of `c`. -/
theorem tsum_sub_le_iSup {c : ℤ → ℝ≥0∞} (hc : Monotone c) :
    ∑' j, (c (j + 1) - c j) ≤ ⨆ j, c j := by
  -- The finite sums over the windows `[a, a + n)` telescope.
  have hsum (a : ℤ) (n : ℕ) : ∑ j ∈ Finset.Ico a (a + n), (c (j + 1) - c j) = c (a + n) - c a := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc,
        ← Finset.insert_Ico_right_eq_Ico_add_one (show a ≤ a + n by omega),
        Finset.sum_insert (by simp), ih,
        tsub_add_tsub_cancel (hc (by omega)) (hc (by omega))]
  rw [tsum_eq_iSup_sum]
  refine iSup_le fun t ↦ ?_
  -- Every finite set of integers lies in a window `[-n, n)`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, t ⊆ Finset.Ico (-(n : ℤ)) (-(n : ℤ) + (2 * n : ℕ)) := by
    obtain ⟨N, hN⟩ := t.bddAbove
    obtain ⟨M, hM⟩ := t.bddBelow
    refine ⟨N.toNat + (-M).toNat + 1, fun j hj ↦ ?_⟩
    have h1 := hN hj
    have h2 := hM hj
    simp only [Finset.mem_Ico]
    push_cast
    constructor <;> omega
  calc ∑ j ∈ t, (c (j + 1) - c j)
      ≤ ∑ j ∈ Finset.Ico (-(n : ℤ)) (-(n : ℤ) + (2 * n : ℕ)), (c (j + 1) - c j) :=
        Finset.sum_le_sum_of_subset hn
    _ = c (-(n : ℤ) + (2 * n : ℕ)) - c (-(n : ℤ)) := hsum _ _
    _ ≤ ⨆ j, c j := tsub_le_self.trans (le_iSup c _)

end ENNReal
