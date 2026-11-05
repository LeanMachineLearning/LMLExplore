/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MeasureTheory.Measure.TotalVariation.Basic

import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Cauchy sequences of probability measures in total variation

A sequence of probability measures `ν n` that is Cauchy for the total variation distance, in the
quantitative form `tvDist (ν m) (ν n) ≤ ε n` for `n ≤ m` with `ε n → 0`, converges: there is a
probability measure `π` with `tvDist (ν n) π ≤ ε n` for every `n`.

This is how limits of Markov chains are built when the laws of the chain contract in total
variation, such as the invariant measure of a kernel whose Dobrushin coefficient is less than
one.

## Main statements

* `MeasureTheory.exists_isProbabilityMeasure_forall_tvDist_le`: a Cauchy sequence of probability
  measures for the total variation distance has a limit, at the rate of the Cauchy bound.

## Implementation notes

The limit is the setwise limit `π s = lim (ν n) s`, defined through `Measure.ofMeasurable`. The
masses `(ν n) s` are Cauchy uniformly in `s`, and this uniformity makes the setwise limit
countably additive: the tail `⋃ i ≥ N, s i` of a disjoint union is small for `π` because it is
small for a single `ν n` close to `π`. This avoids building the Banach space of signed measures
with the total variation norm.
-/

public section

open Set Filter Function Topology

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- A setwise limit of measures that is uniform in the set is countably additive: if the masses
`F n s` of measurable sets converge to `L s` with `|F n s - L s| ≤ e n` and `e n → 0`, the partial
sums of `L` along a disjoint sequence of measurable sets converge to `L` of their union. -/
private lemma tendsto_sum_of_abs_measureReal_sub_le {ν : ℕ → Measure 𝓧}
    [∀ n, IsFiniteMeasure (ν n)] {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) {L : Set 𝓧 → ℝ}
    (hL : ∀ s, MeasurableSet s → Tendsto (fun n ↦ (ν n).real s) atTop (𝓝 (L s)))
    (hνL : ∀ n s, MeasurableSet s → |(ν n).real s - L s| ≤ e n) {f : ℕ → Set 𝓧}
    (hf : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :
    Tendsto (fun N ↦ ∑ i ∈ Finset.range N, L (f i)) atTop (𝓝 (L (⋃ i, f i))) := by
  have hmeas (N : ℕ) : MeasurableSet (⋃ i ∈ Finset.range N, f i) :=
    Finset.measurableSet_biUnion _ fun i _ ↦ hf i
  -- the partial sums are the values of `L` on the finite unions, by finite additivity in the limit
  have hU (N : ℕ) : ∑ i ∈ Finset.range N, L (f i) = L (⋃ i ∈ Finset.range N, f i) := by
    refine tendsto_nhds_unique (tendsto_finsetSum _ fun i _ ↦ hL _ (hf i)) ?_
    refine (hL _ (hmeas N)).congr fun n ↦ ?_
    exact measureReal_biUnion_finset (fun i _ j _ hij ↦ hd hij) fun i _ ↦ hf i
  simp_rw [hU]
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  -- choose `n` with `e n < ε / 3`, then `N₀` such that the finite unions are `ε / 3`-close to
  -- the union for `ν n`
  obtain ⟨n, hn⟩ := (he.eventually (gt_mem_nhds (by positivity : 0 < ε / 3))).exists
  have hlim : Tendsto (fun N ↦ (ν n).real (⋃ i ∈ Finset.range N, f i)) atTop
      (𝓝 ((ν n).real (⋃ i, f i))) := by
    -- countable additivity of `ν n`, through its partial sums
    have hsum : Tendsto (fun N ↦ ∑ i ∈ Finset.range N, ν n (f i)) atTop (𝓝 (ν n (⋃ i, f i))) :=
      measure_iUnion hd hf ▸ ENNReal.tendsto_nat_tsum _
    refine ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hsum).congr fun N ↦ ?_
    rw [Function.comp_apply, measureReal_biUnion_finset (fun i _ j _ hij ↦ hd hij) fun i _ ↦ hf i,
      ENNReal.toReal_sum fun i _ ↦ measure_ne_top _ _]
    rfl
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hlim (ε / 3) (by positivity)
  refine ⟨N₀, fun N hN ↦ ?_⟩
  have h1 := hνL n _ (hmeas N)
  have h2 := hνL n _ (MeasurableSet.iUnion hf)
  have h3 := hN₀ N hN
  rw [Real.dist_eq] at h3 ⊢
  have h4 := abs_sub_le (L (⋃ i ∈ Finset.range N, f i))
    ((ν n).real (⋃ i ∈ Finset.range N, f i)) (L (⋃ i, f i))
  have h5 := abs_sub_le ((ν n).real (⋃ i ∈ Finset.range N, f i)) ((ν n).real (⋃ i, f i))
    (L (⋃ i, f i))
  rw [abs_sub_comm] at h1
  linarith

/-- **Cauchy sequences of probability measures in total variation converge**: if
`tvDist (ν m) (ν n) ≤ ε n` for all `n ≤ m`, with `ε n → 0`, there is a probability measure `π`
with `tvDist (ν n) π ≤ ε n` for every `n`. -/
theorem exists_isProbabilityMeasure_forall_tvDist_le {ν : ℕ → Measure 𝓧}
    [∀ n, IsProbabilityMeasure (ν n)] {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (h : ∀ n m, n ≤ m → tvDist (ν m) (ν n) ≤ ε n) :
    ∃ π : Measure 𝓧, IsProbabilityMeasure π ∧ ∀ n, tvDist (ν n) π ≤ ε n := by
  have he : Tendsto (fun n ↦ ε n / 2) atTop (𝓝 0) := by simpa using hε.div_const 2
  have hνν {n m : ℕ} (hnm : n ≤ m) {s : Set 𝓧} (hs : MeasurableSet s) :
      |(ν m).real s - (ν n).real s| ≤ ε n / 2 :=
    (abs_measureReal_sub_measureReal_le_tvDist_div_two (by simp) hs).trans
      (by linarith [h n m hnm])
  -- the masses of each measurable set converge, to a limit `L s` within `ε n / 2` of `ν n s`
  have hcauchy {s : Set 𝓧} (hs : MeasurableSet s) : CauchySeq fun n ↦ (ν n).real s := by
    refine cauchySeq_of_le_tendsto_0 (fun N ↦ ε N) (fun n k N hn hk ↦ ?_) hε
    have h1 := hνν hn hs
    have h2 := hνν hk hs
    rw [Real.dist_eq]
    calc |(ν n).real s - (ν k).real s|
        ≤ |(ν n).real s - (ν N).real s| + |(ν N).real s - (ν k).real s| := abs_sub_le _ _ _
      _ ≤ ε N := by rw [abs_sub_comm ((ν N).real s)]; linarith
  set L := fun s ↦ limUnder atTop fun n ↦ (ν n).real s
  have hL (s : Set 𝓧) (hs : MeasurableSet s) :
      Tendsto (fun n ↦ (ν n).real s) atTop (𝓝 (L s)) :=
    (hcauchy hs).tendsto_limUnder
  have hνL (N : ℕ) (s : Set 𝓧) (hs : MeasurableSet s) : |(ν N).real s - L s| ≤ ε N / 2 := by
    refine le_of_tendsto (((hL s hs).const_sub _).abs)
      (eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩)
    rw [abs_sub_comm]
    exact hνν hn hs
  have hL0 {s : Set 𝓧} (hs : MeasurableSet s) : 0 ≤ L s :=
    ge_of_tendsto' (hL s hs) fun _ ↦ measureReal_nonneg
  -- the limit is countably additive, hence defines a measure
  have hLempty : L ∅ = 0 := tendsto_nhds_unique (hL ∅ MeasurableSet.empty) (by
    simp only [measureReal_empty]
    exact tendsto_const_nhds)
  let π : Measure 𝓧 := Measure.ofMeasurable (fun s _ ↦ ENNReal.ofReal (L s))
    (by rw [hLempty, ENNReal.ofReal_zero])
    (fun f hf hd ↦ by
      have hs := (hasSum_iff_tendsto_nat_of_nonneg (fun i ↦ hL0 (hf i)) _).2
        (tendsto_sum_of_abs_measureReal_sub_le he hL hνL hf hd)
      rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun i ↦ hL0 (hf i)) hs.summable])
  have hπs {s : Set 𝓧} (hs : MeasurableSet s) : π s = ENNReal.ofReal (L s) :=
    Measure.ofMeasurable_apply s hs
  have hπ1 : L univ = 1 := tendsto_nhds_unique (hL univ MeasurableSet.univ) (by
    simp only [probReal_univ]
    exact tendsto_const_nhds)
  have : IsProbabilityMeasure π :=
    ⟨by rw [hπs MeasurableSet.univ, hπ1, ENNReal.ofReal_one]⟩
  -- the setwise bound `|ν n s - π s| ≤ ε n / 2` gives the bound in total variation
  refine ⟨π, this, fun n ↦ ?_⟩
  have := tvDist_le_two_mul_of_forall_measureReal_le_add (μ := ν n) (ν := π)
    (c := ε n / 2) (by simp)
    fun s hs ↦ by
      rw [measureReal_def π s, hπs hs, ENNReal.toReal_ofReal (hL0 hs)]
      linarith [(abs_le.1 (hνL n s hs)).2]
  linarith

end MeasureTheory
