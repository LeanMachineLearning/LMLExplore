/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LMLExplore.Probability.Process.Filtration
import Mathlib.Probability.Independence.Integration
import TauCeti.MeasureTheory.Integral.Lebesgue.Encard

/-!
# Wald's bound on the expected first passage time of a random walk

Let `X 0, X 1, …` be independent real random variables whose means are at least `a > 0` and
which are bounded above by `C`. The partial sums `∑ j < k, X j` first reach a level `b` after
`N b` steps, the hitting time `hittingAfter` of `[b, ∞)`, which is `⊤` if they never do.
**Wald's argument** bounds its expectation: `𝔼[N b] ≤ (b + C) / a`.

The step `j` is taken on the event `{j < N b}`, which is determined by `X 0, …, X (j - 1)` and
hence independent of `X j`. So the expectation of the partial sum stopped at `min (N b) n` is
`∑ j < n, P(j < N b) 𝔼[X j] ≥ a 𝔼[min (N b) n]` (Wald's identity [Gut09]). That stopped sum is at
most `b + C`, since one step earlier the partial sum was below `b`. Letting `n → ∞` gives the
bound. The increments need not be identically distributed, nor bounded below.

## Main statements

* `ProbabilityTheory.iIndepFun.lintegral_hittingAfter_sum_le`: `𝔼[N b] ≤ (b + C) / a`.

## Implementation notes

The argument is adapted from `EValuesResearch/Results/NumeraireAux.lean` (commit `dd4072f`) in
the paper project `RemyDegenne/evalues_research`, where it is written for the blocks of an i.i.d.
sequence, rewritten on Mathlib's `hittingAfter` and the strict past `Filtration.naturalLT` of
LMLExplore.

## References

* [Gut09] A. Gut, *Stopped Random Walks: Limit Theorems and Applications*, 2nd edition, Springer,
  2009.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- **Wald's bound on the expected first passage time.** Let `X j` be independent real random
variables with means at least `a > 0`, almost surely bounded above by `C`. The first time `N b`
at which the partial sums `∑ j < k, X j` reach `b` (`⊤` if they never do) has expectation at most
`(b + C) / a`. -/
theorem iIndepFun.lintegral_hittingAfter_sum_le (hX : iIndepFun X μ)
    (hXm : ∀ j, Measurable (X j)) {a C : ℝ} (ha : 0 < a) (haX : ∀ j, a ≤ ∫ ω, X j ω ∂μ)
    (hXC : ∀ j, ∀ᵐ ω ∂μ, X j ω ≤ C) (b : ℝ) :
    ∫⁻ ω, ENat.toENNReal
        (hittingAfter (fun k ω ↦ ∑ j ∈ Finset.range k, X j ω) (Set.Ici b) 0 ω) ∂μ ≤
      ENNReal.ofReal ((b + C) / a) := by
  have := hX.isProbabilityMeasure
  set S : ℕ → Ω → ℝ := fun k ω ↦ ∑ j ∈ Finset.range k, X j ω
  set N : Ω → ℕ∞ := hittingAfter S (Set.Ici b) 0
  -- the event that the step `j` is taken, a function of the steps before `j`
  set A : ℕ → Set Ω := fun j ↦ {ω | ∀ k ≤ j, S k ω < b}
  have hNA (j : ℕ) : {ω | (j : ℕ∞) < N ω} = A j := by
    ext ω
    rw [Set.mem_ofPred_eq, lt_iff_not_ge]
    -- `hittingAfter` takes values in `WithTop ℕ`, and `N ω ≤ j` compares them in `ℕ∞`, its
    -- definitional synonym; restating the inequality in `WithTop ℕ` lets `hittingAfter_le_iff`
    -- apply (no `rw` with a cast lemma can, since the goal mixes the two types)
    change ¬ hittingAfter S (Set.Ici b) 0 ω ≤ WithTop.some j ↔ _
    rw [hittingAfter_le_iff]
    simp [A]
  have hAm (j : ℕ) : MeasurableSet[Filtration.naturalLT X hXm j] (A j) := by
    have hS (k : ℕ) (hk : k ≤ j) : Measurable[Filtration.naturalLT X hXm j] (S k) :=
      Finset.measurable_sum (m := Filtration.naturalLT X hXm j) _ fun i hi ↦
        Filtration.measurable_naturalLT hXm ((Finset.mem_range.1 hi).trans_le hk)
    have hA : A j = ⋂ k ∈ Finset.range (j + 1), {ω | S k ω < b} := by
      ext ω
      simp [A]
    rw [hA]
    exact Finset.measurableSet_biInter _ fun k hk ↦
      measurableSet_lt (hS k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))) measurable_const
  have hAm' (j : ℕ) : MeasurableSet (A j) := Filtration.le _ j _ (hAm j)
  refine (lintegral_enat_eq_tsum μ (f := N) fun j ↦ (hNA j).symm ▸ hAm' j).trans_le ?_
  simp_rw [hNA]
  -- if `b ≤ 0`, no step is taken
  rcases le_or_gt b 0 with hb | hb
  · have hA0 (j : ℕ) : A j = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω hω ↦ (hω 0 (Nat.zero_le j)).not_ge (by simpa [S] using hb)
    simp [hA0]
  have hint (j : ℕ) : Integrable (X j) μ := .of_integral_ne_zero (ha.trans_le (haX j)).ne'
  have hC : a ≤ C :=
    (haX 0).trans (integral_mono_ae (hint 0) (integrable_const C) (hXC 0) |>.trans_eq (by simp))
  -- the partial sum stopped at `min N n` overshoots `b` by at most `C`
  have hstop (ω : Ω) (hω : ∀ j, X j ω ≤ C) (n : ℕ) :
      ∑ j ∈ Finset.range n, (A j).indicator (X j) ω ≤ b + C := by
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty]; linarith
    | succ n ih =>
      by_cases hn : ω ∈ A n
      · have h : ∑ j ∈ Finset.range (n + 1), (A j).indicator (X j) ω = S n ω + X n ω := by
          rw [← Finset.sum_range_succ]
          exact Finset.sum_congr rfl fun j hj ↦ Set.indicator_of_mem
            (fun k hk ↦ hn k (hk.trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))) _
        rw [h]
        linarith [hn n le_rfl, hω n]
      · rw [Finset.sum_range_succ, Set.indicator_of_notMem hn, add_zero]
        exact ih
  -- Wald's identity for the stopped partial sum
  have hsum (n : ℕ) : (∑ j ∈ Finset.range n, μ.real (A j)) * a ≤ b + C := by
    have hi (j : ℕ) : Integrable ((A j).indicator (X j)) μ := (hint j).indicator (hAm' j)
    calc (∑ j ∈ Finset.range n, μ.real (A j)) * a
    _ ≤ ∑ j ∈ Finset.range n, μ.real (A j) * ∫ ω, X j ω ∂μ := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (haX j) measureReal_nonneg
    _ = ∫ ω, ∑ j ∈ Finset.range n, (A j).indicator (X j) ω ∂μ := by
      rw [integral_finsetSum _ fun j _ ↦ hi j]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [integral_indicator (hAm' j)]
      exact ((Filtration.indep_naturalLT hXm hX j).symm.setIntegral_eq_mul (f := id)
        (Filtration.le _ j) (hXm j).aemeasurable (hAm j) aestronglyMeasurable_id).symm
    _ ≤ ∫ _, b + C ∂μ := by
      refine integral_mono_ae (integrable_finsetSum _ fun j _ ↦ hi j) (integrable_const _) ?_
      filter_upwards [ae_all_iff.2 hXC] with ω hω using hstop ω hω n
    _ = b + C := by simp
  refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  calc ∑ j ∈ Finset.range n, μ (A j)
  _ = ENNReal.ofReal (∑ j ∈ Finset.range n, μ.real (A j)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ measureReal_nonneg]
    exact Finset.sum_congr rfl fun j _ ↦ (ofReal_measureReal).symm
  _ ≤ ENNReal.ofReal ((b + C) / a) :=
    ENNReal.ofReal_le_ofReal ((le_div_iff₀ ha).2 (hsum n))

end ProbabilityTheory
