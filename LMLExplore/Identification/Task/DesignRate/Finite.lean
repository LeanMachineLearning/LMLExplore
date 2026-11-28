/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Design.Basic
public import LMLExplore.Identification.Task.TransportationCost
import LMLExplore.EValues.BipolarRate.Design.Finite

/-!
# The rate of the designs of an identification task on a finite alphabet

At a model `θ` of an identification task, the rate `D*` of the designs of the laws of the arms at
`θ` against the laws of the arms at the alternatives to an answer `i` is at most the value
`D(θ, ¬i)` of the pure exploration game, and at most the inverse `1 / T*(θ)` of the
characteristic time of [GK16] when `i` is correct
(`LMLExplore.Identification.IdentTask.designRate_le_answerValue`,
`LMLExplore.Identification.IdentTask.designRate_le_inv_charTime`). When the observations take
finitely many values, these bounds are equalities, the second when `i` is the single correct
answer [EVR26, Note 41, Proposition 5]: the rate of the designs is then the entropy constant
(`ProbabilityTheory.designRate_eq_iSup_iInf_sum_mul_klDiv_of_finite`), which is `D(θ, ¬i)`. So on
a finite alphabet the lower bound `kl(δ, 1 - δ) ≤ D* E_θ[τ]` of
`LMLExplore.Identification.IdentTask.IsDeltaCorrect.klBer_le_designRate_mul_expectedStoppingTime`
is the bound `T*(θ) kl(δ, 1 - δ) ≤ E_θ[τ]` of [GK16, Theorem 1].

## Main statements

* `LMLExplore.Identification.IdentTask.designRate_eq_answerValue_of_finite`: on a finite
  alphabet, the rate of the designs against the alternatives to `i` is `D(θ, ¬i)`.
* `LMLExplore.Identification.IdentTask.designRate_eq_inv_charTime_of_finite`: on a finite
  alphabet, for a model `θ` with the single correct answer `i`, the rate of the designs against
  the alternatives to `i` is `1 / T*(θ)`.

## Implementation notes

The statements are adapted from `EValuesResearch/Results/DesignConstants.lean` (commit `cb8238f`)
in the paper project `RemyDegenne/evalues_research`, rewritten on the API of LMLExplore.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 55 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 41, *The lower bound at the bipolar rate, with several arms*.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LMLExplore.Identification.IdentTask

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (task : IdentTask α Θ ℐ 𝓨) {θ : Θ} {i : ℐ}

/-- **The rate of the designs is the value of the game on a finite alphabet.** If the
observations take finitely many values, then at the model `θ` the rate of the designs against the
laws of the arms at the alternatives to the answer `i` is the value
`D(θ, ¬i) = sup_w inf_{λ ∈ ¬i} ∑ a, w a KL(ν_a(θ), ν_a(λ))` of the pure exploration game
[EVR26, Note 41, Proposition 5]. -/
theorem designRate_eq_answerValue_of_finite [Finite 𝓨] (θ : Θ) (i : ℐ) :
    designRate (fun a ↦ task.ν θ a) ((fun θ' a ↦ task.ν θ' a) '' task.alt i) =
      (task.answerValue θ i : EReal) := by
  rw [designRate_eq_iSup_iInf_sum_mul_klDiv_of_finite _ (by
    rintro _ ⟨θ', -, rfl⟩ a
    infer_instance)]
  simp_rw [iInf_image, answerValue_def, altCost_def, cost_def]

/-- **`D* = 1 / T*` on a finite alphabet.** If the observations take finitely many values, then
for a model `θ` with the single correct answer `i`, the rate of the designs against the laws of
the arms at the alternatives to `i` is the inverse `1 / T*(θ)` of the characteristic time
[EVR26, Note 41, Proposition 5; GK16]. -/
theorem designRate_eq_inv_charTime_of_finite [Finite 𝓨] (hi : task.correct θ = {i}) :
    designRate (fun a ↦ task.ν θ a) ((fun θ' a ↦ task.ν θ' a) '' task.alt i) =
      ((task.charTime θ)⁻¹ : ℝ≥0∞) := by
  rw [task.designRate_eq_answerValue_of_finite θ i, task.charTime_eq_inv_answerValue hi, inv_inv]

end LMLExplore.Identification.IdentTask
