/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Design.Basic
public import LMLExplore.Identification.Task.TransportationCost

/-!
# The rate of the designs of an identification task

At a model `θ` of an identification task, the instances against which an answer `i` must be
defended are the laws of the arms at the alternatives to `i`. The rate of the designs
`ProbabilityTheory.designRate` of the laws of the arms at `θ` against those instances is the
constant `D*` of the Wald inequality with a design, which bounds the expected logarithm of an
e-variable at a stopping time of an algorithm that samples the arms adaptively [EVR26, Note 41].
This file compares it with the characteristic time `T*(θ)` of Garivier and Kaufmann:
`D* ≤ D(θ, ¬i) ≤ 1 / T*(θ)`, so that a lower bound on the sample complexity with the constant
`1 / D*` is at least the bound `T*(θ) kl(δ, 1 - δ)` [EVR26, Note 41, Corollary 2; GK16].

## Main statements

* `LMLExplore.Identification.IdentTask.designRate_le_answerValue`: the rate of the designs against
  the alternatives to `i` is at most the value `D(θ, ¬i)` of the pure exploration game.
* `LMLExplore.Identification.IdentTask.designRate_le_inv_charTime`: for a correct answer `i` of
  `θ`, the rate of the designs against the alternatives to `i` is at most `1 / T*(θ)`.

## References

* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 41,
  `results/41-several-arms-bipolar-rate.md`, Section 3.
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace LMLExplore.Identification.IdentTask

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (task : IdentTask α Θ ℐ 𝓨) {θ : Θ} {i : ℐ}

/-- **The rate of the designs is at most the value of the game.** At the model `θ`, the rate of
the designs against the laws of the arms at the alternatives to the answer `i` is at most the
value `D(θ, ¬i) = sup_w inf_{λ ∈ ¬i} ∑ a, w a KL(ν_a(θ), ν_a(λ))` of the pure exploration game.
-/
theorem designRate_le_answerValue (θ : Θ) (i : ℐ) :
    designRate (fun a ↦ task.ν θ a) ((fun θ' a ↦ task.ν θ' a) '' task.alt i) ≤
      (task.answerValue θ i : EReal) := by
  refine (designRate_le_iSup_iInf_sum_mul_klDiv ?_).trans_eq ?_
  · rintro _ ⟨θ', -, rfl⟩ a
    infer_instance
  · simp_rw [iInf_image, answerValue_def, altCost_def, cost_def]

/-- **The rate of the designs is at most the inverse of the characteristic time.** For a correct
answer `i` of the model `θ`, the rate of the designs against the laws of the arms at the
alternatives to `i` is at most `1 / T*(θ)`. -/
theorem designRate_le_inv_charTime (hi : i ∈ task.correct θ) :
    designRate (fun a ↦ task.ν θ a) ((fun θ' a ↦ task.ν θ' a) '' task.alt i) ≤
      ((task.charTime θ)⁻¹ : ℝ≥0∞) := by
  rw [charTime_def, inv_inv]
  exact (task.designRate_le_answerValue θ i).trans
    (EReal.coe_ennreal_le_coe_ennreal_iff.2 (task.answerValue_le_gameValue hi))

end LMLExplore.Identification.IdentTask
