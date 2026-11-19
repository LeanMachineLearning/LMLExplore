/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Matrix.Operator
public import LMLExplore.MarkovDecisionProcess.Value
public import LMLExplore.Probability.Kernel.Matrix

/-!
# The transition matrix of a stationary policy

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP with a finite state space and `π` a stationary policy. The states
of a run of `π` form a Markov chain, whose transition matrix `P_π` is the real matrix of the state
kernel `M.stateKernel π`. This file gives its basic API: its entries, its action on functions and
that of its powers by integration against the state kernel, and its row-stochasticity. It then
writes the discounted value as the resolvent `v^π_γ = (1 - γ P_π)⁻¹ r_π` of `P_π` applied to the
mean reward `r_π = M.policyReward π`.

## Main definitions

* `Learning.MDP.stateMatrix M π`: the transition matrix `P_π` of the states under `π`.

## Main statements

* `Learning.MDP.stateMatrix_mulVec_apply`, `Learning.MDP.stateMatrix_pow_mulVec_apply`: `P_π`
  and its powers act on functions by integration against the state kernel and its powers.
* `Learning.MDP.stateMatrix_mem_rowStochastic`: `P_π` is row-stochastic.
* `Learning.MDP.value_eq_inv_mulVec`: the discounted value is `v^π_γ = (1 - γ P_π)⁻¹ r_π`.
-/

public section

open MeasureTheory ProbabilityTheory Matrix LMLExplore Learning
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} (M : MDP 𝓢 𝓐 ℝ)
  (π : Kernel 𝓢 𝓐)

/-- The transition matrix `P_π` of the states of a run of the stationary policy `π`: the real
transition matrix of the state kernel `M.stateKernel π`, with entries
`P_π s s' = (M.stateKernel π s).real {s'}` (`Learning.MDP.stateMatrix_apply`). -/
noncomputable def stateMatrix : Matrix 𝓢 𝓢 ℝ :=
  (M.stateKernel π).toMatrix.map ((↑) : ℝ≥0 → ℝ)

lemma stateMatrix_def : M.stateMatrix π = (M.stateKernel π).toMatrix.map ((↑) : ℝ≥0 → ℝ) :=
  (rfl)

@[simp]
lemma stateMatrix_apply (s s' : 𝓢) : M.stateMatrix π s s' = (M.stateKernel π s).real {s'} := by
  rw [stateMatrix_def, Kernel.toMatrix_map_coe_apply]

variable [IsMarkovKernel π]

variable [Fintype 𝓢] [MeasurableSingletonClass 𝓢]

/-- `P_π` acts on functions by integration against the state kernel. -/
lemma stateMatrix_mulVec_apply (f : 𝓢 → ℝ) (s : 𝓢) :
    (M.stateMatrix π *ᵥ f) s = ∫ s', f s' ∂(M.stateKernel π s) := by
  rw [stateMatrix_def, Kernel.toMatrix_map_coe_mulVec]

variable [DecidableEq 𝓢]

/-- `P_π ^ n` acts on functions by integration against the `n`-th power of the state kernel. -/
lemma stateMatrix_pow_mulVec_apply (n : ℕ) (f : 𝓢 → ℝ) (s : 𝓢) :
    (M.stateMatrix π ^ n *ᵥ f) s = ∫ s', f s' ∂((M.stateKernel π ^ n) s) := by
  rw [stateMatrix_def, ← Kernel.toMatrix_map_coe_pow, Kernel.toMatrix_map_coe_mulVec]

/-- The transition matrix of a stationary policy is row-stochastic. -/
lemma stateMatrix_mem_rowStochastic : M.stateMatrix π ∈ rowStochastic ℝ 𝓢 := by
  rw [stateMatrix_def]
  exact Kernel.toMatrix_map_coe_mem_rowStochastic _

/-- The discounted value is the resolvent of the transition matrix applied to the reward:
`v^π_γ = (1 - γ P_π)⁻¹ r_π` for `γ < 1`. -/
theorem value_eq_inv_mulVec {γ : ℝ≥0} (hγ : γ < 1) :
    M.value γ π = (1 - (γ : ℝ) • M.stateMatrix π)⁻¹ *ᵥ M.policyReward π := by
  ext s
  have hsum := hasSum_pow_smul_pow (M.stateMatrix_mem_rowStochastic π) (γ := γ)
    (by rwa [NNReal.abs_eq, NNReal.coe_lt_one])
  have hv := Pi.hasSum.1 (hsum.map (mulVec.addMonoidHomLeft (M.policyReward π))
    (continuous_id.matrix_mulVec continuous_const)) s
  simp only [Function.comp_def, mulVec.addMonoidHomLeft_apply, smul_mulVec, Pi.smul_apply,
    smul_eq_mul, stateMatrix_pow_mulVec_apply] at hv
  rw [value_def, hv.tsum_eq]

end Learning.MDP
