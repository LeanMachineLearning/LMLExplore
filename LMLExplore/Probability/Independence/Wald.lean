/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Process.Filtration
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LMLExplore.Probability.Process.HittingTime
import LMLExplore.Probability.Process.Stopping
import Mathlib.Probability.Independence.Integration
import TauCeti.MeasureTheory.Integral.Lebesgue.Encard

/-!
# Wald's identity and Wald's bound on the expected first passage time of a random walk

Let `X 0, X 1, …` be independent random variables and `τ` a stopping time of the filtration
`Filtration.naturalLT` of the past variables. **Wald's identity** in `ℝ≥0∞` states that for a
measurable `g ≥ 0` with `𝔼[g (X j)] = m` for every `j`, `𝔼[∑ j < τ, g (X j)] = m 𝔼[τ]`, with no
integrability hypothesis and `τ` possibly infinite.

Let `X 0, X 1, …` be independent real random variables whose means are at least `a > 0` and
which are bounded above by `C`. The partial sums `∑ j < k, X j` first reach a level `b` after
`N b` steps, the hitting time `hittingAfter` of `[b, ∞)`, which is `⊤` if they never do.
**Wald's argument** bounds its expectation: `𝔼[N b] ≤ (b + C) / a`.

The step `j` is taken on the event `{j < N b}`, which is determined by `X 0, …, X (j - 1)` and
hence independent of `X j`. So the expectation of the partial sum stopped at `min (N b) n` is
`∑ j < n, P(j < N b) 𝔼[X j] ≥ a 𝔼[min (N b) n]` (Wald's identity [Gut09]). That stopped sum is at
most `b + C`, since one step earlier the partial sum was below `b`. Letting `n → ∞` gives the
bound. The increments need not be identically distributed, nor bounded below.

Increments that are not bounded above can be truncated: the walk of the increments `min (X j) c`
lies below the walk, so it reaches `b` no earlier, and the bound applies to it with the means of
the truncated increments.

## Main statements

* `ProbabilityTheory.iIndepFun.lintegral_tsum_indicator_lt_eq_mul`: Wald's identity in `ℝ≥0∞` at a
  stopping time of the filtration `Filtration.naturalLT` of the past variables.
* `ProbabilityTheory.iIndepFun.lintegral_hittingAfter_sum_le`: `𝔼[N b] ≤ (b + C) / a`.
* `ProbabilityTheory.iIndepFun.lintegral_hittingAfter_sum_le_of_le_integral_min`:
  `𝔼[N b] ≤ (b + c) / a` when the increments truncated at `c` have means at least `a > 0`.

## Implementation notes

Wald's bound is adapted from `EValuesResearch/Results/NumeraireAux.lean` (commit `dd4072f`) in
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

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

section Wald

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {X : ℕ → Ω → 𝓧}

/-- **Wald's identity in `ℝ≥0∞`.** Let `X j` be independent random variables and `τ` a stopping
time of the filtration `Filtration.naturalLT` of the past variables, so that the event
`{j < τ}` is determined by `X 0, …, X (j - 1)`. For a measurable `g ≥ 0` with
`𝔼[g (X j)] = m` for every `j`, the sum `∑ j < τ, g (X j)` has mean `m 𝔼[τ]`. No integrability
is needed, and `τ` may be infinite. -/
theorem iIndepFun.lintegral_tsum_indicator_lt_eq_mul (hX : iIndepFun X μ)
    (hXm : ∀ j, Measurable (X j)) {τ : Ω → ℕ∞}
    (hτ : IsStoppingTime (Filtration.naturalLT X hXm) τ) {g : 𝓧 → ℝ≥0∞} (hg : Measurable g)
    {m : ℝ≥0∞} (hm : ∀ j, ∫⁻ ω, g (X j ω) ∂μ = m) :
    ∫⁻ ω, ∑' j : ℕ, {ω | (j : ℕ∞) < τ ω}.indicator (fun ω ↦ g (X j ω)) ω ∂μ =
      m * ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ := by
  have hA (j : ℕ) : MeasurableSet[Filtration.naturalLT X hXm j] {ω | (j : ℕ∞) < τ ω} :=
    hτ.measurableSet_natCast_lt j
  have hA' (j : ℕ) : MeasurableSet {ω | (j : ℕ∞) < τ ω} := Filtration.le _ j _ (hA j)
  rw [lintegral_tsum (f := fun (j : ℕ) ω ↦ {ω | (j : ℕ∞) < τ ω}.indicator (fun ω ↦ g (X j ω)) ω)
      fun j ↦ ((hg.comp (hXm j)).indicator (hA' j)).aemeasurable,
    lintegral_enat_eq_tsum μ hA', ← ENNReal.tsum_mul_left]
  refine tsum_congr fun j ↦ ?_
  have h : ∀ ω, {ω | (j : ℕ∞) < τ ω}.indicator (fun ω ↦ g (X j ω)) ω =
      {ω | (j : ℕ∞) < τ ω}.indicator 1 ω * g (X j ω) := fun ω ↦ by
    by_cases hω : ω ∈ {ω | (j : ℕ∞) < τ ω} <;> simp [hω]
  simp_rw [h]
  -- the event `{j < τ}` is determined by the past, independent of `X j`
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (f := {ω | (j : ℕ∞) < τ ω}.indicator 1) (g := fun ω ↦ g (X j ω)) (Filtration.le _ j)
    (hXm j).comap_le (Filtration.indep_naturalLT hXm hX j).symm
    (measurable_const.indicator (hA j)) (hg.comp (comap_measurable (X j))),
    lintegral_indicator_one (hA' j), hm j, mul_comm]

end Wald

variable {X : ℕ → Ω → ℝ}

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

/-- **Wald's upper bound on the expected first passage time, by truncation.** Let `X j` be
independent real random variables whose truncations `min (X j) c` at a level `c` have means at
least `a > 0`. The first time `N b` at which the partial sums `∑ j < k, X j` reach `b` has
expectation at most `(b + c) / a`. The increments need not be bounded above or identically
distributed. -/
theorem iIndepFun.lintegral_hittingAfter_sum_le_of_le_integral_min (hX : iIndepFun X μ)
    (hXm : ∀ j, Measurable (X j)) {a c : ℝ} (ha : 0 < a)
    (haX : ∀ j, a ≤ ∫ ω, min (X j ω) c ∂μ) (b : ℝ) :
    ∫⁻ ω, ENat.toENNReal
        (hittingAfter (fun k ω ↦ ∑ j ∈ Finset.range k, X j ω) (Set.Ici b) 0 ω) ∂μ ≤
      ENNReal.ofReal ((b + c) / a) := by
  refine (lintegral_mono fun ω ↦ ?_).trans
    (iIndepFun.lintegral_hittingAfter_sum_le (X := fun j ω ↦ min (X j ω) c)
      (hX.comp (fun _ x ↦ min x c) fun _ ↦ measurable_id.min measurable_const)
      (fun j ↦ (hXm j).min measurable_const) ha haX
      (fun _ ↦ ae_of_all _ fun _ ↦ min_le_right _ _) b)
  refine ENat.toENNReal_le.2 (hittingAfter_apply_le_of_forall_mem fun k _ hk ↦ ?_)
  exact le_trans hk (Finset.sum_le_sum fun j _ ↦ min_le_left _ _)

end ProbabilityTheory
