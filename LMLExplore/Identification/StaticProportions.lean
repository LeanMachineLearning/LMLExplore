/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.TransportationCost

/-!
# The static-proportions difficulty of fixed-budget identification

A fixed-budget algorithm with *static proportions* samples the arms with fixed proportions
`w ∈ Δ_K` and recommends an answer computed from the empirical means at the end of the budget.
For arms in exponential families and a regular task, its probability of error `p_{θ,T}` at the
model `θ` satisfies
`log (1 / p_{θ,T}) / T → inf_{λ ∈ Alt(θ)} ∑ a, w a KL(ν_a(λ), ν_a(θ))`, where `Alt(θ)` is the
set of admissible models without a common correct answer with `θ` (`IdentTask.alternatives`)
[D23, Theorem 1; GJ04]. In the exponent the alternative `λ` comes first in the divergence,
unlike in the transportation costs of fixed-confidence identification (`IdentTask.altCost`): the
error is a large deviation of the empirical means of `θ` towards `λ`. The best proportions give the
*static-proportions difficulty*
`H^{sp}(θ) = (sup_{w ∈ Δ_K} inf_{λ ∈ Alt(θ)} ∑ a, w a KL(ν_a(λ), ν_a(θ)))⁻¹`, the baseline
against which [D23] compares the fixed-budget algorithm families.

## Main definitions

* `LMLExplore.Identification.IdentTask.staticDifficulty task θ`: the static-proportions
  difficulty `H^{sp}(θ)`.

## Main statements

* `LMLExplore.Identification.IdentTask.inv_staticDifficulty`:
  `H^{sp}(θ)⁻¹ = sup_{w ∈ Δ_K} inf_{λ ∈ Alt(θ)} cost(w, λ, θ)`.
* `LMLExplore.Identification.IdentTask.staticDifficulty_restrict_le`: restricting the admissible
  models can only decrease the static-proportions difficulty.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
* [GJ04] P. Glynn and S. Juneja, *A large deviations perspective on ordinal optimization*,
  Winter Simulation Conference 2004.
* Adapted from the formalization of [D23] in the project `RemyDegenne/Degenne2023Existence`
  (same author).
-/

public section

open scoped ENNReal

namespace LMLExplore.Identification.IdentTask

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (task : IdentTask α Θ ℐ 𝓨)

/-- The static-proportions difficulty
`H^{sp}(θ) = (sup_{w ∈ Δ_K} inf_{λ ∈ Alt(θ)} ∑ a, w a KL(ν_a(λ), ν_a(θ)))⁻¹` of the model `θ`,
with the alternative `λ` first in the divergence. For arms in exponential families and under the
regularity assumption of [D23, Theorem 1], it is the best asymptotic rate `T / log (1 / p_{θ,T})`
of the static proportions algorithms at `θ`. -/
noncomputable def staticDifficulty (θ : Θ) : ℝ≥0∞ :=
  (⨆ w ∈ simplex α, ⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ)⁻¹

lemma staticDifficulty_def (θ : Θ) :
    task.staticDifficulty θ = (⨆ w ∈ simplex α, ⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ)⁻¹ :=
  (rfl)

/-- The inverse of the static-proportions difficulty is the value
`sup_{w ∈ Δ_K} inf_{λ ∈ Alt(θ)} cost(w, λ, θ)` of the static game. -/
lemma inv_staticDifficulty (θ : Θ) :
    (task.staticDifficulty θ)⁻¹ =
      ⨆ w ∈ simplex α, ⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ := by
  rw [staticDifficulty_def, inv_inv]

/-- Restricting the admissible models removes alternatives, so it can only decrease the
static-proportions difficulty. -/
lemma staticDifficulty_restrict_le (S : Set Θ) (θ : Θ) :
    (task.restrict S).staticDifficulty θ ≤ task.staticDifficulty θ := by
  rw [staticDifficulty_def, staticDifficulty_def, alternatives_restrict, cost_restrict,
    ENNReal.inv_le_inv]
  exact iSup₂_mono fun w _ ↦ biInf_mono Set.inter_subset_left

end LMLExplore.Identification.IdentTask
