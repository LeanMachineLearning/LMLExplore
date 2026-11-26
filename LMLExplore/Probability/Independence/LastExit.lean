/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
import LMLExplore.MeasureTheory.Integral.Lebesgue.BorelCantelli
import LMLExplore.Probability.Moments.SubGaussian.Bounded
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The last time a random walk with bounded increments is below a line

Let `X 0, X 1, …` be independent real random variables with values in `[l, u]` and means at least
`m`, and let `c < m`. By Hoeffding's inequality
(`LMLExplore.measureReal_le_abs_sum_sub_integral_le`), the walk `∑ i < k, X i` is below `c k` at
time `k` with probability at most `2 r ^ k`, for `r = exp (-2 (m - c)² / (u - l)²) < 1` when
`u > l`, so that the series `∑' k, (k + 1) * P (∑ i < k, X i < c k)` converges. By the
Borel–Cantelli lemma with a time of finite mean
(`MeasureTheory.exists_lintegral_le_tsum_forall_ge_notMem`), finitely many such walks are then
all above `c k` from a time of finite mean on: the last time one of them is below the line has a
finite mean. This is the integrable convergence of [ARR26], which bounds the expected time a
growing process takes to reach a level
(`ProbabilityTheory.limsup_lintegral_hittingAfter_div_log_le`).

## Main statements

* `ProbabilityTheory.tsum_mul_measure_sum_lt_mul_ne_top`: `∑' k, (k + 1) * P (∑ i < k, X i < c k)`
  is finite.
* `ProbabilityTheory.exists_lintegral_ne_top_forall_ge_mul_le_sum`: finitely many such walks are
  above `c k` from a time of finite mean on.

## Implementation notes

The statements are adapted from the helper `exists_forall_ge_mul_le_sum` of
`EValuesResearch/Results/ConvexPieces.lean` (commit `83205cb`) in the paper project
`RemyDegenne/evalues_research`, rewritten with the two-sided Hoeffding inequality of LMLExplore
and stated for independent increments that need not be identically distributed.

## References

* [ARR26] S. Agrawal, A. Ram and A. Ramdas, *On stopping times of power-one sequential tests:
  tight lower and upper bounds*, arXiv:2504.19952v2, Theorem 4.1.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **A random walk with bounded increments is rarely below a line of smaller slope.** Let `X i`
be independent real random variables with values in `[l, u]` and means at least `m`, and let
`c < m`. Then `∑' k, (k + 1) * μ {ω | ∑ i < k, X i ω < c k}` is finite: by Hoeffding's
inequality, the terms decay geometrically. -/
theorem tsum_mul_measure_sum_lt_mul_ne_top {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ)
    (hXm : ∀ i, AEMeasurable (X i) μ) {l u : ℝ} (hX : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc l u)
    {m c : ℝ} (hm : ∀ i, m ≤ μ[X i]) (hc : c < m) :
    ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * μ {ω | ∑ i ∈ Finset.range k, X i ω < c * k} ≠ ∞ := by
  set δ := m - c
  have hδ : 0 < δ := sub_pos.2 hc
  -- an interval of positive length containing the values
  set u' := max u (l + 1)
  have hu' : 1 ≤ u' - l := by linarith [le_max_right u (l + 1)]
  have hX' (i : ℕ) : ∀ᵐ ω ∂μ, X i ω ∈ Icc l u' :=
    (hX i).mono fun ω hω ↦ Icc_subset_Icc_right (le_max_left u (l + 1)) hω
  set r := Real.exp (-(2 * δ ^ 2 / (u' - l) ^ 2))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (neg_neg_of_pos (by positivity))
  -- Hoeffding's inequality: the walk is below `c k` with probability at most `2 r ^ k`
  have hp (k : ℕ) : μ {ω | ∑ i ∈ Finset.range k, X i ω < c * k} ≤ ENNReal.ofReal (2 * r ^ k) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have hH := LMLExplore.measureReal_le_abs_sum_sub_integral_le h_indep (s := Finset.range k)
      (fun i _ ↦ hXm i) (l := fun _ ↦ l) (u := fun _ ↦ u') (fun i _ ↦ hX' i)
      (t := δ * k) (by positivity)
    have hsub : {ω | ∑ i ∈ Finset.range k, X i ω < c * k} ⊆
        {ω | δ * k ≤ |∑ i ∈ Finset.range k, (X i ω - μ[X i])|} := by
      intro ω (hω : _ < _)
      have hmean : (k : ℝ) * m ≤ ∑ i ∈ Finset.range k, μ[X i] := by
        simpa using Finset.card_nsmul_le_sum (Finset.range k) _ m fun i _ ↦ hm i
      refine le_trans ?_ (neg_le_abs (∑ i ∈ Finset.range k, (X i ω - μ[X i])))
      rw [Finset.sum_sub_distrib]
      simp only [δ]
      linarith
    have hexp : 2 * Real.exp (-(2 * (δ * k) ^ 2 / ∑ i ∈ Finset.range k, (u' - l) ^ 2)) =
        2 * r ^ k := by
      rw [← Real.exp_natCast_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 2
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      field_simp
    calc μ {ω | ∑ i ∈ Finset.range k, X i ω < c * k}
        ≤ μ {ω | δ * k ≤ |∑ i ∈ Finset.range k, (X i ω - μ[X i])|} := measure_mono hsub
      _ = ENNReal.ofReal (μ.real {ω | δ * k ≤ |∑ i ∈ Finset.range k, (X i ω - μ[X i])|}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (2 * r ^ k) := ENNReal.ofReal_le_ofReal (hH.trans hexp.le)
  -- the series `∑ (k + 1) 2 r ^ k` converges
  have hsumm : Summable fun k : ℕ ↦ ((k : ℝ) + 1) * (2 * r ^ k) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0] : ‖r‖ < 1)
    simp only [pow_one] at h1
    have := (h1.add (summable_geometric_of_lt_one hr0 hr1)).mul_left 2
    convert this using 1
    ext k
    ring
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_of_le_of_eq
    (tsum_le_tsum fun k ↦ ?_) (ENNReal.ofReal_tsum_of_nonneg (fun k ↦ by positivity)
      hsumm).symm)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one,
    ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  gcongr
  exact hp k

/-- **Finitely many random walks with bounded increments are above a line of smaller slope from a
time of finite mean on.** Let `X j i`, for `j` in a finite type, be real random variables with
values in `[l, u]` and means at least `m`, independent in `i` for every `j`, and let `c < m`.
There is a time `N` of finite mean such that, almost surely, `c k ≤ ∑ i < k, X j i` for every
`k ≥ N` and every `j`. -/
theorem exists_lintegral_ne_top_forall_ge_mul_le_sum {κ : Type*} [Finite κ]
    {X : κ → ℕ → Ω → ℝ} (h_indep : ∀ j, iIndepFun (X j) μ)
    (hXm : ∀ j i, AEMeasurable (X j i) μ) {l u : ℝ} (hX : ∀ j i, ∀ᵐ ω ∂μ, X j i ω ∈ Icc l u)
    {m c : ℝ} (hm : ∀ j i, m ≤ μ[X j i]) (hc : c < m) :
    ∃ N : Ω → ℕ, ∫⁻ ω, (N ω : ℝ≥0∞) ∂μ ≠ ∞ ∧
      ∀ᵐ ω ∂μ, ∀ k ≥ N ω, ∀ j, c * k ≤ ∑ i ∈ Finset.range k, X j i ω := by
  have := Fintype.ofFinite κ
  -- the times at which some walk is below the line
  set s : ℕ → Set Ω := fun k ↦ ⋃ j, {ω | ∑ i ∈ Finset.range k, X j i ω < c * k}
  have hs : ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * μ (s k) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑ j, ∑' k : ℕ, ((k : ℝ≥0∞) + 1) *
      μ {ω | ∑ i ∈ Finset.range k, X j i ω < c * k}) (ENNReal.sum_ne_top.2 fun j _ ↦
        tsum_mul_measure_sum_lt_mul_ne_top (h_indep j) (hXm j) (hX j) (hm j) hc) ?_
    rw [← Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
    refine tsum_le_tsum fun k ↦ ?_
    rw [← Finset.mul_sum]
    gcongr
    exact measure_iUnion_fintype_le μ _
  obtain ⟨N, hN, hNs⟩ := exists_lintegral_le_tsum_forall_ge_notMem μ hs
  refine ⟨N, ne_top_of_le_ne_top hs hN, hNs.mono fun ω hω k hk j ↦ ?_⟩
  by_contra hlt
  exact hω k hk (mem_iUnion.2 ⟨j, lt_of_not_ge hlt⟩)

end ProbabilityTheory
