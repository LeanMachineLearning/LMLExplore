/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Null.Basic
public import LMLExplore.Probability.ProductMeasure.Blocks
public import LMLExplore.Probability.ProductMeasure.Restart

/-!
# Bets on the first observations of an i.i.d. sequence

The observations are the coordinates of `ℕ → 𝓧`, and the null is the i.i.d. null `iidNull S₁` of a
set `S₁` of laws on `𝓧`. A bet on the first `n` observations is an e-variable `f` for `iidNull S₁`
that is a function of the first `n` coordinates, `DependsOn f (Set.Iio n)`: its expectation is at
most `1` under the i.i.d. law of every member of the null. The wealth of a gambler who bets on
blocks of observations [RR26, Definitions 2.3–2.5] is built from such bets by a few operations,
which this file shows produce bets again:

* **skipping** the first `n` observations: `g ∘ (shift 𝓧)^[n]`, a bet read on the observations
  after the first `n`, whose law under an i.i.d. law is that of `g`;
* **concatenation** with a shifted continuation: `f ω * g ((shift 𝓧)^[n] ω)`, a bet `f` on the
  first `n` observations followed by a bet `g` on the next ones, whose expectations multiply since
  the two are independent under an i.i.d. law;
* **mixtures** `∑ i, w i * f i`, countable or finite, with weights of sum at most `1`
  (`ProbabilityTheory.isEVar_tsum_mul`, `ProbabilityTheory.isEVar_finsetSum_mul`, for any null);
* **parsing into blocks**: the product `seqBlockProd m V k` of a bet `V` on `m` observations over
  the first `k` consecutive blocks of `m` observations;
* **restart at a stopping time**: a round of duration `σ`, a stopping time, and payoff `V`, known
  at time `σ`, restarted on the fresh observations each time it ends; the product
  `restartPayoff σ V j` of the payoffs of the first `j` rounds, on the event that they end within
  the first `N` observations.

Each operation also keeps track of the observations the bet has seen:
`MeasureTheory.dependsOn_comp_shift_iterate`, `MeasureTheory.dependsOn_mul_comp_shift_iterate`,
`MeasureTheory.dependsOn_seqBlockProd` and
`ProbabilityTheory.DependsOnBefore.dependsOn_indicator_le`. A function of the first `n`
observations is exactly a function measurable for the time `n` of the filtration
`Filtration.piLT` of the observations (`Filtration.measurable_piLT_of_dependsOn`,
`Measurable.dependsOn_of_piLT`), so a sequence of bets, the `n`-th on the first `n` observations,
is adapted to that filtration.

## Main statements

* `ProbabilityTheory.IsEVar.comp_shift_iterate`: a bet read after the first `n` observations is a
  bet.
* `ProbabilityTheory.IsEVar.mul_comp_shift_iterate`: the concatenation of a bet on the first `n`
  observations with a bet on the next ones is a bet.
* `ProbabilityTheory.isEVar_seqBlockProd`: the product over blocks of a bet on `m` observations,
  for the null `sampleNull S₁ m` of `m`-samples, is a bet for the i.i.d. null.
* `ProbabilityTheory.isEVar_indicator_restartPayoff`: the payoff of the first `j` restarted rounds,
  on the event that they end within the first `N` observations, is a bet.

## References

* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1,
  Definitions 2.3–2.5.
-/

public section

open MeasureTheory
open TauCeti.Probability (shift measurable_shift_iterate)
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)} {f g : (ℕ → 𝓧) → ℝ≥0∞}

/-- **Skipping observations.** An e-variable for the i.i.d. null, read on the observations after
the first `n`, is an e-variable for the i.i.d. null, which is invariant under the shift
(`ProbabilityTheory.mapNull_shift_iterate_iidNull`). -/
theorem IsEVar.comp_shift_iterate (hg : IsEVar g (iidNull S₁)) (n : ℕ) :
    IsEVar (fun ω ↦ g ((shift 𝓧)^[n] ω)) (iidNull S₁) :=
  (isEVar_mapNull_iff (measurable_shift_iterate n) hg.measurable).1
    (by rwa [mapNull_shift_iterate_iidNull])

/-- **Concatenation of bets.** For an e-variable `f` for the i.i.d. null that is a function of the
first `n` observations and an e-variable `g` for the i.i.d. null, the bet `f` on the first `n`
observations followed by the bet `g` on the next ones, `ω ↦ f ω * g ((shift 𝓧)^[n] ω)`, is an
e-variable for the i.i.d. null. If `g` is a function of the first `m` observations, the
concatenation is a function of the first `n + m` (`MeasureTheory.dependsOn_mul_comp_shift_iterate`).
-/
theorem IsEVar.mul_comp_shift_iterate {n : ℕ} (hf : IsEVar f (iidNull S₁))
    (hfn : DependsOn f (Set.Iio n)) (hg : IsEVar g (iidNull S₁)) :
    IsEVar (fun ω ↦ f ω * g ((shift 𝓧)^[n] ω)) (iidNull S₁) :=
  isEVar_iidNull_iff.2 ⟨hf.measurable.mul (hg.measurable.comp (measurable_shift_iterate n)),
    fun P hP _ ↦ by
      rw [lintegral_mul_comp_shift_iterate P hf.measurable hfn hg.measurable]
      exact mul_le_one' (hf.lintegral_le_one (infinitePi_mem_iidNull hP))
        (hg.lintegral_le_one (infinitePi_mem_iidNull hP))⟩

/-- **Parsing into blocks.** For an e-variable `V` of `m` observations for the null
`sampleNull S₁ m` of `m`-samples, its product `seqBlockProd m V k` over the first `k` consecutive
blocks of `m` observations is an e-variable for the i.i.d. null, a function of the first `k * m`
observations (`MeasureTheory.dependsOn_seqBlockProd`). -/
theorem isEVar_seqBlockProd {m : ℕ} {V : (Fin m → 𝓧) → ℝ≥0∞}
    (hV : IsEVar V (sampleNull S₁ m)) (k : ℕ) :
    IsEVar (seqBlockProd m V k) (iidNull S₁) :=
  isEVar_iidNull_iff.2 ⟨measurable_seqBlockProd hV.measurable k, fun P hP _ ↦ by
    rw [lintegral_seqBlockProd_const P hV.measurable]
    exact pow_le_one₀ (by positivity) (hV.lintegral_le_one (pi_mem_sampleNull hP))⟩

/-- The payoff of `j + 1` rounds within `N` observations: that of the first `j` rounds, within
`N` observations, times that of the next round within the observations left. -/
private lemma indicator_restartTime_succ_le {σ : (ℕ → 𝓧) → ℕ} (j N : ℕ) (ω : ℕ → 𝓧) :
    {ω | restartTime σ (j + 1) ω ≤ N}.indicator (restartPayoff σ f (j + 1)) ω =
      {ω | restartTime σ j ω ≤ N}.indicator (fun ω ↦ restartPayoff σ f j ω *
        {x | σ x ≤ N - restartTime σ j ω}.indicator f ((shift 𝓧)^[restartTime σ j ω] ω)) ω := by
  simp only [Set.indicator, Set.mem_ofPred_eq, restartTime_succ, restartPayoff_succ]
  by_cases h1 : restartTime σ j ω ≤ N
  · by_cases h2 : σ ((shift 𝓧)^[restartTime σ j ω] ω) ≤ N - restartTime σ j ω
    · simp [h1, h2, show restartTime σ j ω + σ ((shift 𝓧)^[restartTime σ j ω] ω) ≤ N by omega]
    · simp [h1, h2, show ¬ restartTime σ j ω + σ ((shift 𝓧)^[restartTime σ j ω] ω) ≤ N by omega]
  · simp [h1, show ¬ restartTime σ j ω + σ ((shift 𝓧)^[restartTime σ j ω] ω) ≤ N by omega]

/-- **Restart at a stopping time.** Let a round have a duration `σ`, a stopping time counted in
observations, and a payoff `V` known at time `σ`, such that the payoff on each event `{σ ≤ n}` is
an e-variable for the i.i.d. null. Restart the round on the fresh observations each time it ends.
Then the product `restartPayoff σ V j` of the payoffs of the first `j` rounds, on the event that
they end within the first `N` observations, is an e-variable for the i.i.d. null. It is a function
of the first `N` observations (`ProbabilityTheory.DependsOnBefore.dependsOn_indicator_le`, with
`ProbabilityTheory.dependsOnBefore_restartTime` and
`ProbabilityTheory.dependsOnBefore_restartPayoff`). -/
theorem isEVar_indicator_restartPayoff {σ : (ℕ → 𝓧) → ℕ} {V : (ℕ → 𝓧) → ℝ≥0∞}
    (hσ : DependsOnBefore σ σ) (hV : DependsOnBefore σ V) (hσm : Measurable σ)
    (hVσ : ∀ n : ℕ, IsEVar ({ω | σ ω ≤ n}.indicator V) (iidNull S₁)) (j N : ℕ) :
    IsEVar ({ω | restartTime σ j ω ≤ N}.indicator (restartPayoff σ V j)) (iidNull S₁) := by
  -- the payoff is the supremum of its restrictions to the events `{σ ≤ n}`
  have hVm : Measurable V := by
    convert Measurable.iSup fun n : ℕ ↦ (hVσ n).measurable with ω
    refine le_antisymm (le_iSup_of_le (σ ω) ?_) (iSup_le fun n ↦ Set.indicator_le_self _ _ ω)
    rw [Set.indicator_of_mem (s := {ω' | σ ω' ≤ σ ω}) (le_refl (σ ω))]
  refine isEVar_iidNull_iff.2 ⟨(measurable_restartPayoff hσm hVm j).indicator
    (measurable_restartTime hσm j measurableSet_Iic), fun P hP _ ↦ ?_⟩
  set μ := Measure.infinitePi (fun _ : ℕ ↦ P)
  induction j generalizing N with
  | zero =>
    calc ∫⁻ ω, {ω | restartTime σ 0 ω ≤ N}.indicator (restartPayoff σ V 0) ω ∂μ
    _ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun ω ↦
      (Set.indicator_le_self _ _ ω).trans_eq (restartPayoff_zero σ V ω)
    _ = 1 := by simp
  | succ j ih =>
    have hT := dependsOnBefore_restartTime hσ j
    have hTm := measurable_restartTime hσm j
    have hf := dependsOnBefore_restartPayoff hσ hV j
    have hfm := measurable_restartPayoff hσm hVm j
    calc ∫⁻ ω, {ω | restartTime σ (j + 1) ω ≤ N}.indicator (restartPayoff σ V (j + 1)) ω ∂μ
    _ = ∑ t ∈ Finset.range (N + 1),
          (∫⁻ ω, {ω | restartTime σ j ω = t}.indicator (restartPayoff σ V j) ω ∂μ) *
            ∫⁻ ω, {ω | σ ω ≤ N - t}.indicator V ω ∂μ := by
      simp_rw [indicator_restartTime_succ_le]
      exact hT.lintegral_indicator_mul_comp_shift_iterate hTm hf hfm
        (g := fun t ↦ {ω | σ ω ≤ N - t}.indicator V) (fun t ↦ (hVσ (N - t)).measurable) P N
    _ ≤ ∑ t ∈ Finset.range (N + 1),
          ∫⁻ ω, {ω | restartTime σ j ω = t}.indicator (restartPayoff σ V j) ω ∂μ :=
      Finset.sum_le_sum fun t _ ↦ mul_le_of_le_one_right'
        ((hVσ (N - t)).lintegral_le_one (infinitePi_mem_iidNull hP))
    _ = ∫⁻ ω, {ω | restartTime σ j ω ≤ N}.indicator (fun ω ↦ restartPayoff σ V j ω * 1) ω ∂μ := by
      rw [hT.lintegral_indicator_mul_comp_shift_iterate hTm hf hfm (g := fun _ _ ↦ 1)
        (fun _ ↦ measurable_const) P N]
      simp [μ]
    _ ≤ 1 := by simpa using ih N

end ProbabilityTheory
