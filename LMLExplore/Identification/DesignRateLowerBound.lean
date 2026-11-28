/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Design.Basic
public import LMLExplore.Identification.SampleComplexity
public import LMLExplore.Identification.Task.CorrectnessOnStop
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
import LMLExplore.EValues.BipolarRate.Design.Algorithm
import LMLExplore.EValues.TestBet
import LMLExplore.Probability.HasLaw

/-!
# The lower bound with the rate of the designs, for algorithms `δ`-correct when they stop

Let `A` be an identification algorithm `δ`-correct when it stops on an identification task
(`IdentTask.IsDeltaCorrectOnStop`), with `δ ≤ 1 / 2`: on every admissible model, it stops with an
answer that is not correct with probability at most `δ`, and nothing is asked when it does not
stop. Let `θ` be an admissible model with the single correct answer `i` and an alternative, at
which `A` stops almost surely. Then `kl(δ, 1 - δ) ≤ D* E_θ[τ]`, where `D*` is the rate of the
designs of the laws of the arms at `θ` against those at the alternatives to `i`: the expected
stopping time is at least `kl(δ, 1 - δ) / D*` [EVR26, Note 41, Corollary 2; Note 55].

At `θ`, the algorithm stops and answers `i` with probability at least `1 - δ`, since it stops
almost surely and errs with probability at most `δ`; at every alternative to `i`, with
probability at most `δ`, since it errs when it answers `i`. Given the history at the stopping
time, the probability that the algorithm stops and answers `i` is therefore a test of level `δ`
for the alternatives to `i`, of power at least `1 - δ` at `θ`. The bet on it
(`ProbabilityTheory.testBet`) is an e-variable at the stopping time whose expected logarithm at
`θ` is at least `kl(1 - δ, δ) = kl(δ, 1 - δ)`, and the Wald inequality with a design
(`Learning.IsAlgEnvSeq.eintegral_log_le_designRate_mul_lintegral`) bounds that expected logarithm
by `D* E_θ[τ]`. Only almost sure stopping at `θ` is used, not at the alternatives: the bound
holds for the algorithm that learns the design [EVR26, Note 49], which is `δ`-correct when it
stops but need not be `δ`-correct.

## Main statements

* `IdentTask.IsDeltaCorrectOnStop.klBer_le_designRate_mul_expectedStoppingTime`: the lower bound
  `kl(δ, 1 - δ) ≤ D* E_θ[τ]` for an algorithm `δ`-correct when it stops.

## Implementation notes

The statement and its proof are adapted from `EValuesResearch/Results/DesignLearningWald.lean`
(commit `cb8238f`) in the paper project `RemyDegenne/evalues_research`, rewritten on the API of
LMLExplore. They follow the proof of
`IdentTask.IsDeltaCorrect.klBer_le_designRate_mul_expectedStoppingTime` for `δ`-correct
algorithms, with the case `δ ≤ 0` deduced from small positive levels.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 55 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory ProbabilityTheory Learning

open scoped ENNReal

namespace LMLExplore.Identification.IdentTask

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} [MeasurableSingletonClass α]
  {m𝓨 : MeasurableSpace 𝓨} {mℐ : MeasurableSpace ℐ} [MeasurableSingletonClass ℐ]
  {task : IdentTask α Θ ℐ 𝓨} {A : IdentAlg Unit α 𝓨 ℐ} {δ : ℝ} {θ : Θ} {i : ℐ}

/-- `IsDeltaCorrectOnStop.klBer_le_designRate_mul_expectedStoppingTime` for `0 < δ`. -/
private lemma IsDeltaCorrectOnStop.klBer_le_designRate_mul_expectedStoppingTime_of_pos
    (hA : task.IsDeltaCorrectOnStop A δ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hθ : θ ∈ task.M)
    (hi : task.correct θ = {i}) (h_alt : (task.alt i).Nonempty)
    (hstop : StopsAS A (Environment.bandit (task.ν θ))) :
    (klBer δ (1 - δ) : EReal) ≤
      designRate (fun a ↦ task.ν θ a) ((fun θ' a ↦ task.ν θ' a) '' task.alt i) *
        (expectedStoppingTime A (Environment.bandit (task.ν θ)) : EReal) := by
  classical
  have hseq := IT.isAlgEnvSeq_trajMeasure A.alg (Environment.bandit (task.ν θ))
  -- the probability `φ h` that `A` stops and answers `i` given the stopped history `h` is a test
  -- of level `δ` against the alternatives to `i`, of power at least `1 - δ` at `θ`
  set φ : (Σ n : ℕ, Hist Unit α 𝓨 n) → ℝ≥0∞ := A.stopSet.indicator fun h ↦ A.output h {i}
  have hφm : Measurable φ :=
    (A.output.measurable_coe (measurableSet_singleton i)).indicator A.measurableSet_stopSet
  have hφ1 (h : Σ n : ℕ, Hist Unit α 𝓨 n) : φ h ≤ 1 :=
    Set.indicator_apply_le' (fun _ ↦ prob_le_one) fun _ ↦ zero_le_one
  have hφθ : ENNReal.ofReal (1 - δ) ≤
      ∫⁻ h, φ h ∂stoppedHistMeasure A.alg (Environment.bandit (task.ν θ)) A.stopSet := by
    rw [lintegral_indicator_output_eq_histOutputMeasure]
    exact ENNReal.ofReal_le_of_le_toReal
      (hA.one_sub_le_measureReal_histOutputMeasure hθ hi hstop)
  -- the bet on that test is an e-variable at the stopping time against the alternatives
  set G := testBet δ (1 - δ) φ
  have hGm : Measurable G := hφm.testBet
  have hGalt : ∀ (ν : Kernel α 𝓨) [IsMarkovKernel ν], ν ∈ task.ν '' task.alt i →
      ∫⁻ h in A.stopSet, G h ∂stoppedHistMeasure A.alg (Environment.bandit ν) A.stopSet ≤ 1 := by
    rintro _ _ ⟨θ', hθ', rfl⟩
    refine (setLIntegral_le_lintegral _ _).trans (lintegral_testBet_le_one hφm hφ1
      ⟨hδ0, by linarith⟩ (by linarith) (by linarith) prob_le_one ?_)
    rw [lintegral_indicator_output_eq_histOutputMeasure]
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hδ0.le).2
      (hA.measureReal_histOutputMeasure_le hθ')
  have hτ : ∀ᵐ ω ∂trajMeasure A.alg (Environment.bandit (task.ν θ)),
      hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) A.stopSet 0 ω ≠ ⊤ :=
    (stopsAS_iff_ae_stoppingTime_ne_top hseq).1 hstop
  have hlog : AEMeasurable (fun h ↦ ENNReal.log (G h))
      (stoppedHistMeasure A.alg (Environment.bandit (task.ν θ)) A.stopSet) :=
    (ENNReal.measurable_log.comp hGm).aemeasurable
  -- `kl(δ, 1 - δ) = kl(1 - δ, δ) ≤ 𝔼_θ[log G] ≤ D* 𝔼_θ[τ]`
  calc (klBer δ (1 - δ) : EReal) = klBer (1 - δ) δ := by
        rw [← klBer_one_sub_one_sub, sub_sub_cancel]
  _ ≤ ∫ᵉ h, ENNReal.log (G h)
      ∂stoppedHistMeasure A.alg (Environment.bandit (task.ν θ)) A.stopSet :=
    klBer_le_eintegral_log_testBet hφm hφ1 hδ0 (by linarith) (by linarith) hφθ
  _ = ∫ᵉ ω, ENNReal.log (G (stoppedValue (sigmaHistory IT.obs IT.action IT.feedback)
        (hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) A.stopSet 0) ω))
          ∂trajMeasure A.alg (Environment.bandit (task.ν θ)) :=
    ((hseq.hasLaw_stoppedValue_sigmaHistory A.measurableSet_stopSet).eintegral_comp hlog).symm
  _ ≤ _ := hseq.eintegral_log_le_designRate_mul_lintegral (Λ := task.ν '' task.alt i)
      (by rintro _ ⟨θ', -, rfl⟩; infer_instance) (h_alt.image _) A.measurableSet_stopSet hGm
      hGalt hτ
  _ = _ := by rw [Set.image_image, expectedStoppingTime_def, IdentAlg.stoppingTime_def]

/-- **Lower bound on the sample complexity with the rate of the designs, for algorithms
`δ`-correct when they stop** [EVR26, Note 41, Corollary 2; Note 55]. Let `A` be `δ`-correct when
it stops with `δ ≤ 1 / 2`, let `i` be the only correct answer of the admissible model `θ`, and
suppose that `i` has an alternative and that `A` stops almost surely on `θ`. Then
`kl(δ, 1 - δ) ≤ D* E_θ[τ]`, where `D*` is the rate of the designs of the laws of the arms at `θ`
against those at the alternatives to `i`: `E_θ[τ] ≥ kl(δ, 1 - δ) / D*`.

This is the Wald inequality with a design
(`Learning.IsAlgEnvSeq.eintegral_log_le_designRate_mul_lintegral`) for the bet on the event that
`A` stops and answers `i`, randomized by the output rule. The product is in `EReal`. Almost sure
stopping is assumed at `θ` only: at the alternatives, `A` may not stop. -/
theorem IsDeltaCorrectOnStop.klBer_le_designRate_mul_expectedStoppingTime
    (hA : task.IsDeltaCorrectOnStop A δ) (hδ : δ ≤ 1 / 2) (hθ : θ ∈ task.M)
    (hi : task.correct θ = {i}) (h_alt : (task.alt i).Nonempty)
    (hstop : StopsAS A (Environment.bandit (task.ν θ))) :
    (klBer δ (1 - δ) : EReal) ≤
      designRate (fun a ↦ task.ν θ a) ((fun θ' a ↦ task.ν θ' a) '' task.alt i) *
        (expectedStoppingTime A (Environment.bandit (task.ν θ)) : EReal) := by
  rcases lt_or_ge 0 δ with hδ0 | hδ0
  · exact hA.klBer_le_designRate_mul_expectedStoppingTime_of_pos hδ0 hδ hθ hi h_alt hstop
  -- for `δ ≤ 0`, `A` is `δ`-correct when it stops for every level `ε > 0`, and `kl(ε, 1 - ε)` is
  -- unbounded as `ε → 0`, so that the right-hand side is `⊤`
  rw [klBer_one_sub_right_eq_top fun h ↦ hδ0.not_gt h.1]
  refine ((EReal.eq_top_iff_forall_lt _).2 fun y ↦ ?_).ge
  obtain ⟨ε, hy, hε⟩ := ((tendsto_klBer_one_sub_right_nhdsGT_zero.eventually
    (eventually_gt_nhds (ENNReal.ofReal_lt_top (r := y)))).and
    (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2))).exists
  calc (y : EReal) ≤ (ENNReal.ofReal y : EReal) := by
        rw [EReal.coe_ennreal_ofReal]
        exact EReal.coe_le_coe_iff.2 (le_max_left _ _)
  _ < (klBer ε (1 - ε) : EReal) := EReal.coe_ennreal_lt_coe_ennreal_iff.2 hy
  _ ≤ _ := hA.mono (hδ0.trans hε.1.le) |>.klBer_le_designRate_mul_expectedStoppingTime_of_pos hε.1
    hε.2 hθ hi h_alt hstop

end LMLExplore.Identification.IdentTask
