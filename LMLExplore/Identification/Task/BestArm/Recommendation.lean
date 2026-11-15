/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.Task.BestArm.Basic

/-!
# The recommendation of a best arm is locally constant

In best arm identification with means continuous in the model, the models with a unique best arm
`a` form an open set (`isOpen_answerSet_baiTask_of_continuous`). So a recommendation that answers
a best arm of every admissible model is constant near every admissible model, and targets that are
optimal allocations at every admissible model `θ'` for the answer `rec θ'` are, near an admissible
model `θ`, optimal allocations for the answer `rec θ`. These are the local-constancy and
target hypotheses of the sample complexity theorems of Track-and-Stop
(`Identification/TrackAndStop.lean`) on best arm identification.

## Main statements

* `eventually_eq_of_forall_mem_correct_baiTask_restrict`: on best arm identification restricted to
  a neighbourhood of `θ`, a recommendation of a best arm of every admissible model is, near `θ`,
  the unique best arm of `θ`.
* `eventually_eq_of_forall_mem_correct_baiTask`: a recommendation of a best arm of every
  admissible model is locally constant at every admissible model.
* `eventually_mem_optAlloc_baiTask`: targets that are optimal allocations at every admissible model
  are, near an admissible model `θ`, optimal allocations for the answer `rec θ`.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace LMLExplore.Identification

variable {α Θ ι 𝓨 : Type*} [Finite ι] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  [TopologicalSpace Θ] (ν : Θ → Kernel α 𝓨) [∀ θ, IsMarkovKernel (ν θ)] {mean : Θ → ι → ℝ}
  {S : Set Θ} {θ : Θ} {a : ι} {rec : Θ → ι}

/-- **The recommendation of a best arm is locally constant** at the models with a unique best arm.
For means continuous in the model, a recommendation `rec` that answers a best arm of every
admissible model of best arm identification restricted to a neighbourhood `S` of `θ` is the unique
best arm `a` of `θ` at every model near `θ`. The empirical best arm `μ ↦ rec μ` on vectors of means
is such a recommendation, with `S` the vectors of means of the arm families. -/
theorem eventually_eq_of_forall_mem_correct_baiTask_restrict
    (hmean : ∀ b, Continuous fun θ ↦ mean θ b) (hS : S ∈ 𝓝 θ)
    (hrec : ∀ θ' ∈ ((baiTask ν mean).restrict S).M,
      rec θ' ∈ ((baiTask ν mean).restrict S).correct θ')
    (ha : ∀ b ≠ a, mean θ b < mean θ a) :
    ∀ᶠ θ' in 𝓝 θ, rec θ' = a := by
  filter_upwards [(isOpen_answerSet_baiTask_of_continuous ν mean hmean a).mem_nhds
    ((mem_answerSet_baiTask_iff ν mean).2 ha), hS] with θ' hθ' hθ'S
  rw [IdentTask.mem_answerSet_iff] at hθ'
  have h := hrec θ' (by rw [IdentTask.M_restrict]; exact ⟨hθ'.1, hθ'S⟩)
  rw [IdentTask.correct_restrict] at h
  exact subsingleton_correct_baiTask ν mean θ' h hθ'.2

/-- **The recommendation of a best arm is locally constant** at every admissible model. For means
continuous in the model, a recommendation `rec` that answers a best arm of every admissible model
of best arm identification is equal to `rec θ` near every admissible model `θ`. -/
theorem eventually_eq_of_forall_mem_correct_baiTask (hmean : ∀ b, Continuous fun θ ↦ mean θ b)
    (hrec : ∀ θ' ∈ (baiTask ν mean).M, rec θ' ∈ (baiTask ν mean).correct θ')
    (hθ : θ ∈ (baiTask ν mean).M) :
    ∀ᶠ θ' in 𝓝 θ, rec θ' = rec θ :=
  eventually_eq_of_forall_mem_correct_baiTask_restrict ν hmean univ_mem
    (fun θ' hθ' ↦ by
      rw [IdentTask.M_restrict] at hθ'
      rw [IdentTask.correct_restrict]
      exact hrec θ' hθ'.1)
    (by simpa using hrec θ hθ)

/-- **Optimal targets near an admissible model.** For means continuous in the model and a
recommendation `rec` of a best arm of every admissible model of best arm identification, targets
`w θ' ∈ w*(θ', ¬rec θ')` that are optimal allocations at every admissible model `θ'` are, near an
admissible model `θ`, optimal allocations `w θ' ∈ w*(θ', ¬rec θ)` for the answer `rec θ`. -/
theorem eventually_mem_optAlloc_baiTask [Fintype α] (hmean : ∀ b, Continuous fun θ ↦ mean θ b)
    (hrec : ∀ θ' ∈ (baiTask ν mean).M, rec θ' ∈ (baiTask ν mean).correct θ')
    {w : Θ → α → ℝ} (hw : ∀ θ' ∈ (baiTask ν mean).M, w θ' ∈ (baiTask ν mean).optAlloc θ' (rec θ'))
    (hθ : θ ∈ (baiTask ν mean).M) :
    ∀ᶠ θ' in 𝓝 θ, w θ' ∈ (baiTask ν mean).optAlloc θ' (rec θ) := by
  filter_upwards [eventually_eq_of_forall_mem_correct_baiTask ν hmean hrec hθ,
    (isOpen_answerSet_baiTask_of_continuous ν mean hmean (rec θ)).mem_nhds
      ((mem_answerSet_baiTask_iff ν mean).2 (by simpa using hrec θ hθ))] with θ' h_eq hθ'
  rw [IdentTask.mem_answerSet_iff] at hθ'
  exact h_eq ▸ hw θ' hθ'.1

end LMLExplore.Identification
