/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Martingale.Centering
public import Mathlib.Probability.Process.Stopping

/-!
# The Doob decomposition at stopping times

Mathlib's `MeasureTheory.predictablePart f ℱ μ` is the predictable part of the Doob decomposition
of a process `f` indexed by `ℕ`: `predictablePart f ℱ μ n = ∑ k < n, μ[f (k + 1) - f k | ℱ k]`.
Between two bounded stopping times `σ ≤ τ`, the increments of an integrable process and those of
its predictable part have the same set integrals over every set measurable for the σ-algebra at
`σ`: the martingale part of the decomposition has no drift. No adaptedness is needed.

This identity is the expectation form of optional stopping for every integrable process, and
the source of exact identities such as the exact Ville identity, in which the predictable part
measures the decrease of a supermartingale up to a hitting time.

## Main statements

* `MeasureTheory.setIntegral_stoppedValue_sub_eq_predictablePart`: for bounded stopping times
  `σ ≤ τ` and `s` measurable at `σ`,
  `∫ ω in s, f τ - f σ ∂μ = ∫ ω in s, predictablePart f τ - predictablePart f σ ∂μ`.
* `MeasureTheory.Supermartingale.condExp_sub_nonpos`: the conditional expectation of an increment
  of a supermartingale is almost surely nonpositive.
* `MeasureTheory.Supermartingale.antitone_predictablePart`: the predictable part of a
  supermartingale is almost surely antitone.
-/

public section

open Finset Set

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {f : ℕ → Ω → E} {ℱ : Filtration ℕ mΩ}
  {σ τ : Ω → WithTop ℕ}

/-- **The Doob decomposition between stopping times.** For an integrable process `f`, bounded
stopping times `σ ≤ τ` and a set `s` measurable for the σ-algebra at `σ`, the increments of `f` and
of its predictable part from `σ` to `τ` have the same integral over `s`. -/
theorem setIntegral_stoppedValue_sub_eq_predictablePart [SigmaFiniteFiltration μ ℱ]
    (hf : ∀ n, Integrable (f n) μ) (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) {N : ℕ} (hτN : ∀ ω, τ ω ≤ N) {s : Set Ω}
    (hs : MeasurableSet[hσ.measurableSpace] s) :
    ∫ ω in s, stoppedValue f τ ω - stoppedValue f σ ω ∂μ =
      ∫ ω in s, stoppedValue (predictablePart f ℱ μ) τ ω -
        stoppedValue (predictablePart f ℱ μ) σ ω ∂μ := by
  -- The set `{σ ≤ k < τ}`, and its intersection with `s`, are `ℱ k`-measurable.
  have hgt (k : ℕ) : MeasurableSet[ℱ k] {ω | k < τ ω} := by simpa using hτ.measurableSet_gt k
  have hmeas' (k : ℕ) : MeasurableSet[ℱ k] {ω | σ ω ≤ k ∧ k < τ ω} := by
    rw [ofPred_and]
    exact (by simpa using hσ.measurableSet_le k : MeasurableSet[ℱ k] {ω | σ ω ≤ k}).inter (hgt k)
  have hmeas (k : ℕ) : MeasurableSet[ℱ k] (s ∩ {ω | σ ω ≤ k ∧ k < τ ω}) := by
    rw [ofPred_and, ← Set.inter_assoc]
    exact (by simpa using hs.2 k : MeasurableSet[ℱ k] (s ∩ {ω | σ ω ≤ k})).inter (hgt k)
  -- Both increments are sums over `k ≤ N` of the increments from `k` to `k + 1` on `{σ ≤ k < τ}`.
  have hsum (g : ℕ → Ω → E) (ω : Ω) : stoppedValue g τ ω - stoppedValue g σ ω =
      ∑ k ∈ range (N + 1), {ω | σ ω ≤ k ∧ k < τ ω}.indicator (g (k + 1) - g k) ω := by
    simpa [Finset.sum_apply] using congrFun (stoppedValue_sub_eq_sum' (u := g) hστ hτN) ω
  have hint (k : ℕ) : Integrable (f (k + 1) - f k) μ := (hf (k + 1)).sub (hf k)
  have hA (k : ℕ) : predictablePart f ℱ μ (k + 1) - predictablePart f ℱ μ k =
      μ[f (k + 1) - f k | ℱ k] := by
    rw [predictablePart_add_one, add_sub_cancel_left]
  simp_rw [hsum, hA]
  rw [integral_finsetSum _ fun k _ ↦ ((hint k).indicator (ℱ.le k _ (hmeas' k))).integrableOn,
    integral_finsetSum _ fun k _ ↦
      (integrable_condExp.indicator (ℱ.le k _ (hmeas' k))).integrableOn]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [setIntegral_indicator (ℱ.le k _ (hmeas' k)), setIntegral_indicator (ℱ.le k _ (hmeas' k)),
    setIntegral_condExp (ℱ.le k) (hint k) (hmeas k)]

/-- The conditional expectation of an increment of a supermartingale is almost surely
nonpositive: the supermartingale counterpart of Mathlib's
`MeasureTheory.Submartingale.condExp_sub_nonneg`. -/
theorem Supermartingale.condExp_sub_nonpos {ι : Type*} [Preorder ι] [PartialOrder E]
    [IsOrderedAddMonoid E] {g : ι → Ω → E} {𝒢 : Filtration ι mΩ} (hg : Supermartingale g 𝒢 μ)
    {i j : ι} (hij : i ≤ j) : μ[g j - g i | 𝒢 i] ≤ᵐ[μ] 0 := by
  have h := hg.neg.condExp_sub_nonneg hij
  simp only [Pi.neg_apply, neg_sub_neg] at h
  filter_upwards [h, condExp_neg (g i - g j) (𝒢 i)] with ω hω hneg
  rw [← neg_sub, hneg, Pi.neg_apply, Pi.zero_apply, neg_nonpos]
  exact hω

/-- The predictable part of a supermartingale is almost surely antitone: the supermartingale
counterpart of Mathlib's `MeasureTheory.Submartingale.monotone_predictablePart`. -/
theorem Supermartingale.antitone_predictablePart [PartialOrder E] [IsOrderedAddMonoid E]
    (hf : Supermartingale f ℱ μ) : ∀ᵐ ω ∂μ, Antitone (predictablePart f ℱ μ · ω) := by
  filter_upwards [ae_all_iff.2 fun n : ℕ ↦ hf.condExp_sub_nonpos n.le_succ] with ω hω
  refine antitone_nat_of_succ_le fun n ↦ ?_
  rw [predictablePart_add_one, Pi.add_apply, add_le_iff_nonpos_right]
  exact hω n

end MeasureTheory
