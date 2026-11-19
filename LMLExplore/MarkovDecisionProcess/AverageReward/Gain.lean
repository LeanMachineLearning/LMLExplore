/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Matrix.LimitingMatrix
public import LMLExplore.MarkovDecisionProcess.Value
public import LMLExplore.Probability.Kernel.Matrix
public import LMLExplore.Topology.Instances.NNReal.Lemmas

/-!
# The gain and the bias of a stationary policy

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP with a finite state space and `π` a stationary policy. The states
of a run of `π` form a Markov chain with transition matrix `P_π` (`Learning.MDP.stateMatrix`, the
real matrix of `M.stateKernel π`), and the policy earns the mean reward `r_π = M.policyReward π`
in each state. This Markov reward process `(P_π, r_π)` has
* the *gain* `g^π = P*_π r_π`, with `P*_π` the limiting matrix of `P_π`: the long-run average
  expected reward `lim_N N⁻¹ ∑ n < N, P_π ^ n r_π`;
* the *bias* `h^π = D_π r_π`, with `D_π` the deviation matrix of `P_π`: the Cesàro limit of the
  total expected reward in excess of the gain, `∑ k < n, (P_π ^ k r_π - g^π)`.

They are the objects in which the average-reward criterion is stated: the gain measures the
long-run reward of a policy, and the bias refines the comparison of policies with equal gain. They
are also the first two coefficients of the Laurent expansion of the discounted value `v^π_γ`
in powers of `(1 - γ) / γ`, which links the discounted and the average-reward criteria as
`γ ↑ 1`.

The action space `𝓐` is arbitrary, and no bound on the rewards is needed: the state space being
finite, every function of the states is integrable against every finite measure.

## Main definitions

* `Learning.MDP.stateMatrix M π`: the transition matrix `P_π` of the states under `π`.
* `Learning.MDP.gain M π`: the gain `g^π = P*_π r_π`.
* `Learning.MDP.bias M π`: the bias `h^π = D_π r_π`.

## Main statements

* `Learning.MDP.tendsto_cesaro_gain`: the gain is the Cesàro limit of the expected rewards
  `∫ r_π ∂(P_π ^ n s)` [P, Proposition 8.2.1].
* `Learning.MDP.gain_eq_of_mem_communicatingClass`: the gain is constant on each closed
  communicating class of the state chain, and `Learning.MDP.gain_eq_of_forall_reaches`: it is
  constant when every state reaches every other state [P, Proposition 8.2.1].
* `Learning.MDP.tendsto_cesaro_sum_sub_gain`, `Learning.MDP.tendsto_cesaro_sum_of_gain_eq_zero`:
  the bias is the Cesàro limit of the total expected reward in excess of the gain, hence of the
  total expected reward when the gain is zero [P, Proposition 8.2.2].
* `Learning.MDP.value_eq_inv_mulVec`: the discounted value is `v^π_γ = (1 - γ P_π)⁻¹ r_π`.
* `Learning.MDP.value_eq_laurent`: the Laurent expansion of the discounted value
  [P, Theorem 8.2.3].
* `Learning.MDP.tendsto_value_sub_inv_one_sub_mul_gain`,
  `Learning.MDP.tendsto_one_sub_mul_value`: `v^π_γ = (1 - γ)⁻¹ g^π + h^π + o(1)` and
  `g^π = lim_{γ ↑ 1} (1 - γ) v^π_γ` [P, Corollaries 8.2.4–8.2.5].
* `Learning.MDP.integral_gain`, `Learning.MDP.gain_add_bias`,
  `Learning.MDP.limitingMatrix_mulVec_bias`: the evaluation equations `P_π g = g`,
  `g + h = r_π + P_π h` and `P*_π h = 0`, which characterize `(g^π, h^π)`
  (`Learning.MDP.eq_gain_and_eq_bias_iff`); without the third equation, the solutions are the
  pairs `(g^π, h^π + P*_π h)` (`Learning.MDP.eq_gain_and_eq_bias_add_iff`) [P, Theorem 8.2.6].

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §8.2
-/

public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix Topology LMLExplore Learning
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} (M : MDP 𝓢 𝓐 ℝ)
  (π : Kernel 𝓢 𝓐)

/-! ### The transition matrix, the gain and the bias of a stationary policy -/

/-- The transition matrix `P_π` of the states of a run of the stationary policy `π`: the real
transition matrix of the state kernel `M.stateKernel π`, with entries
`P_π s s' = (M.stateKernel π s).real {s'}` (`Learning.MDP.stateMatrix_apply`). -/
noncomputable def stateMatrix : Matrix 𝓢 𝓢 ℝ :=
  (M.stateKernel π).toMatrix.map ((↑) : ℝ≥0 → ℝ)

lemma stateMatrix_def : M.stateMatrix π = (M.stateKernel π).toMatrix.map ((↑) : ℝ≥0 → ℝ) :=
  (rfl)

section Defs

variable [Fintype 𝓢] [DecidableEq 𝓢]

/-- The *gain* `g^π = P*_π r_π` of the stationary policy `π`, with `P*_π` the limiting matrix of
its transition matrix: the long-run average expected reward of `π` from each state
(`Learning.MDP.tendsto_cesaro_gain`). -/
noncomputable def gain : 𝓢 → ℝ :=
  (M.stateMatrix π).limitingMatrix *ᵥ M.policyReward π

lemma gain_def : M.gain π = (M.stateMatrix π).limitingMatrix *ᵥ M.policyReward π :=
  (rfl)

/-- The *bias* `h^π = D_π r_π` of the stationary policy `π`, with `D_π` the deviation matrix of
its transition matrix: the Cesàro limit of the total expected reward of `π` in excess of its gain
(`Learning.MDP.tendsto_cesaro_sum_sub_gain`). -/
noncomputable def bias : 𝓢 → ℝ :=
  (M.stateMatrix π).deviationMatrix *ᵥ M.policyReward π

lemma bias_def : M.bias π = (M.stateMatrix π).deviationMatrix *ᵥ M.policyReward π :=
  (rfl)

end Defs

@[simp]
lemma stateMatrix_apply (s s' : 𝓢) : M.stateMatrix π s s' = (M.stateKernel π s).real {s'} := by
  rw [stateMatrix_def, Kernel.toMatrix_map_coe_apply]

/-- The value at `s` of `A *ᵥ r_π` is continuous in the matrix `A`. -/
private lemma continuous_mulVec_policyReward_apply [Fintype 𝓢] (s : 𝓢) :
    Continuous fun A : Matrix 𝓢 𝓢 ℝ ↦ (A *ᵥ M.policyReward π) s :=
  (continuous_apply s).comp (continuous_id.matrix_mulVec continuous_const)

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

/-- `(1 - P_π) g = 0` is the harmonicity `∫ g ∂(P_π s) = g s` of `g`. -/
private lemma one_sub_stateMatrix_mulVec_eq_zero_iff {g : 𝓢 → ℝ} :
    (1 - M.stateMatrix π) *ᵥ g = 0 ↔ ∀ s, ∫ s', g s' ∂(M.stateKernel π s) = g s := by
  simp only [sub_mulVec, one_mulVec, funext_iff, stateMatrix_mulVec_apply, sub_eq_zero]
  exact forall_congr' fun _ ↦ eq_comm

/-- `g + (1 - P_π) h = r` is the pointwise equation `g s + h s = r s + ∫ h ∂(P_π s)`. -/
private lemma add_one_sub_stateMatrix_mulVec_eq_iff {g h r : 𝓢 → ℝ} :
    g + (1 - M.stateMatrix π) *ᵥ h = r ↔
      ∀ s, g s + h s = r s + ∫ s', h s' ∂(M.stateKernel π s) := by
  simp only [sub_mulVec, one_mulVec, funext_iff, Pi.add_apply, Pi.sub_apply,
    stateMatrix_mulVec_apply]
  exact forall_congr' fun _ ↦ ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩

/-! ### The gain as an average reward, and the evaluation equations -/

/-- **The gain is the long-run average expected reward** [P, Proposition 8.2.1]:
`g^π s = lim_N N⁻¹ ∑ n < N, ∫ r_π ∂(P_π ^ n s)`. -/
theorem tendsto_cesaro_gain (s : 𝓢) :
    Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ *
      ∑ n ∈ range N, ∫ s', M.policyReward π s' ∂((M.stateKernel π ^ n) s)) atTop
      (𝓝 (M.gain π s)) := by
  rw [gain_def]
  refine (((M.continuous_mulVec_policyReward_apply π s).tendsto _).comp
    (tendsto_cesaro_limitingMatrix (M.stateMatrix_mem_rowStochastic π))).congr fun N ↦ ?_
  simp only [Function.comp_apply, smul_mulVec, sum_mulVec, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul, stateMatrix_pow_mulVec_apply]

/-- The gain is the limit of the Cesàro means of the expected rewards. -/
theorem gain_eq_limUnder (s : 𝓢) :
    M.gain π s = limUnder atTop fun N : ℕ ↦ (N : ℝ)⁻¹ *
      ∑ n ∈ range N, ∫ s', M.policyReward π s' ∂((M.stateKernel π ^ n) s) :=
  (M.tendsto_cesaro_gain π s).limUnder_eq.symm

/-- The gain is harmonic for the transition matrix: `P_π g^π = g^π`. -/
theorem stateMatrix_mulVec_gain : M.stateMatrix π *ᵥ M.gain π = M.gain π := by
  rw [gain_def, mulVec_mulVec, mul_limitingMatrix (M.stateMatrix_mem_rowStochastic π)]

/-- **The first evaluation equation** [P, Theorem 8.2.6]: the gain is harmonic,
`∫ g^π ∂(P_π s) = g^π s`. -/
theorem integral_gain (s : 𝓢) : ∫ s', M.gain π s' ∂(M.stateKernel π s) = M.gain π s := by
  rw [← stateMatrix_mulVec_apply, stateMatrix_mulVec_gain]

/-- **The second evaluation equation** [P, Theorem 8.2.6]:
`g^π s + h^π s = r_π s + ∫ h^π ∂(P_π s)`. -/
theorem gain_add_bias (s : 𝓢) :
    M.gain π s + M.bias π s = M.policyReward π s + ∫ s', M.bias π s' ∂(M.stateKernel π s) :=
  (M.add_one_sub_stateMatrix_mulVec_eq_iff π).1
    ((eq_limitingMatrix_mulVec_and_eq_deviationMatrix_mulVec_iff
      (M.stateMatrix_mem_rowStochastic π)).1 ⟨gain_def .., bias_def ..⟩).2.1 s

/-- **The normalization of the bias** [P, Theorem 8.2.6]: `P*_π h^π = 0`. -/
theorem limitingMatrix_mulVec_bias : (M.stateMatrix π).limitingMatrix *ᵥ M.bias π = 0 :=
  ((eq_limitingMatrix_mulVec_and_eq_deviationMatrix_mulVec_iff
    (M.stateMatrix_mem_rowStochastic π)).1 ⟨gain_def .., bias_def ..⟩).2.2

/-- **The evaluation equations** [P, Theorem 8.2.6]: `(g^π, h^π)` is the unique pair `(g, h)`
with `P_π g = g`, `g + h = r_π + P_π h` and `P*_π h = 0`. -/
theorem eq_gain_and_eq_bias_iff {g h : 𝓢 → ℝ} :
    g = M.gain π ∧ h = M.bias π ↔
      (∀ s, ∫ s', g s' ∂(M.stateKernel π s) = g s) ∧
      (∀ s, g s + h s = M.policyReward π s + ∫ s', h s' ∂(M.stateKernel π s)) ∧
      (M.stateMatrix π).limitingMatrix *ᵥ h = 0 := by
  rw [← M.one_sub_stateMatrix_mulVec_eq_zero_iff π, ← M.add_one_sub_stateMatrix_mulVec_eq_iff π,
    gain_def, bias_def]
  exact eq_limitingMatrix_mulVec_and_eq_deviationMatrix_mulVec_iff
    (M.stateMatrix_mem_rowStochastic π)

/-- **All solutions of the first two evaluation equations** [P, Theorem 8.2.6]: the pairs `(g, h)`
with `P_π g = g` and `g + h = r_π + P_π h` are those with `g = g^π` and `h = h^π + P*_π h`. So
they determine the gain, and the bias up to the function `P*_π h`, which is harmonic. -/
theorem eq_gain_and_eq_bias_add_iff {g h : 𝓢 → ℝ} :
    g = M.gain π ∧ h = M.bias π + (M.stateMatrix π).limitingMatrix *ᵥ h ↔
      (∀ s, ∫ s', g s' ∂(M.stateKernel π s) = g s) ∧
      (∀ s, g s + h s = M.policyReward π s + ∫ s', h s' ∂(M.stateKernel π s)) := by
  rw [← M.one_sub_stateMatrix_mulVec_eq_zero_iff π, ← M.add_one_sub_stateMatrix_mulVec_eq_iff π,
    gain_def, bias_def]
  exact eq_limitingMatrix_mulVec_and_eq_deviationMatrix_mulVec_add_iff
    (M.stateMatrix_mem_rowStochastic π)

/-- **The gain is constant on closed classes** [P, Proposition 8.2.1]: it takes the same value at
all the states of a closed communicating class of the state chain of `π`. -/
theorem gain_eq_of_mem_communicatingClass {s s' : 𝓢}
    (hs : (M.stateKernel π).IsClosedSet ((M.stateKernel π).communicatingClass s))
    (hs' : s' ∈ (M.stateKernel π).communicatingClass s) : M.gain π s' = M.gain π s := by
  refine Kernel.eq_of_toMatrix_map_coe_mulVec_eq_of_mem_communicatingClass ?_ hs hs'
  rw [← stateMatrix_def, stateMatrix_mulVec_gain]

/-- When every state reaches every other state under `π`, the gain of `π` is constant. -/
theorem gain_eq_of_forall_reaches (h : ∀ s s', (M.stateKernel π).Reaches s s') (s s' : 𝓢) :
    M.gain π s' = M.gain π s := by
  refine Kernel.eq_of_toMatrix_map_coe_mulVec_eq_of_forall_reaches ?_ h s s'
  rw [← stateMatrix_def, stateMatrix_mulVec_gain]

/-- **The bias is the Cesàro limit of the excess total reward** [P, Proposition 8.2.2]:
`h^π s = lim_N N⁻¹ ∑ n < N, ∑ k < n, (∫ r_π ∂(P_π ^ k s) - g^π s)`. -/
theorem tendsto_cesaro_sum_sub_gain (s : 𝓢) :
    Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ * ∑ n ∈ range N, ∑ k ∈ range n,
      (∫ s', M.policyReward π s' ∂((M.stateKernel π ^ k) s) - M.gain π s)) atTop
      (𝓝 (M.bias π s)) := by
  refine (((M.continuous_mulVec_policyReward_apply π s).tendsto _).comp
    (tendsto_cesaro_sum_pow_sub_limitingMatrix
    (M.stateMatrix_mem_rowStochastic π))).congr fun N ↦ ?_
  simp only [Function.comp_apply, smul_mulVec, sum_mulVec, sub_mulVec, Pi.smul_apply,
    Finset.sum_apply, Pi.sub_apply, smul_eq_mul, stateMatrix_pow_mulVec_apply, gain_def]

/-- **The bias is the Cesàro limit of the total reward when the gain is zero**
[P, Proposition 8.2.2]: `h^π s = lim_N N⁻¹ ∑ n < N, ∑ k < n, ∫ r_π ∂(P_π ^ k s)`. -/
theorem tendsto_cesaro_sum_of_gain_eq_zero (hg : M.gain π = 0) (s : 𝓢) :
    Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ * ∑ n ∈ range N, ∑ k ∈ range n,
      ∫ s', M.policyReward π s' ∂((M.stateKernel π ^ k) s)) atTop (𝓝 (M.bias π s)) := by
  simpa [hg] using M.tendsto_cesaro_sum_sub_gain π s

/-! ### The Laurent expansion of the discounted value -/

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

/-- **Laurent expansion of the discounted value** [P, Theorem 8.2.3]. For `0 < γ < 1` and
`u = (1 - γ) / γ` with `u ‖D_π‖ < 1`, where `‖D_π‖` is the operator norm of the action of the
deviation matrix on `𝓢 → ℝ` for the sup norm,
`v^π_γ = (1 + u) (u⁻¹ g^π + ∑ₙ (-u) ^ n D_π ^ (n + 1) r_π)`. The term `n = 0` of the series is
the bias `h^π = D_π r_π`. -/
theorem value_eq_laurent {γ : ℝ≥0} {u : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (hu : u = (1 - γ) / γ)
    (hD : u * ‖toContinuousLinAlgEquiv' ℝ (M.stateMatrix π).deviationMatrix‖ < 1) :
    M.value γ π = (1 + u) • (u⁻¹ • M.gain π + ∑' n : ℕ,
      (-u) ^ n • ((M.stateMatrix π).deviationMatrix ^ (n + 1) *ᵥ M.policyReward π)) := by
  have hP := M.stateMatrix_mem_rowStochastic π
  have hu₀ : 0 < u := hu ▸ div_pos (sub_pos.2 (NNReal.coe_lt_one.2 hγ₁)) (NNReal.coe_pos.2 hγ₀)
  have hS := summable_neg_pow_smul_pow_succ (A := (M.stateMatrix π).deviationMatrix)
    (by rwa [abs_of_pos hu₀])
  have hv : HasSum (fun n : ℕ ↦ ((-u) ^ n • (M.stateMatrix π).deviationMatrix ^ (n + 1)) *ᵥ
      M.policyReward π) ((∑' n : ℕ, (-u) ^ n • (M.stateMatrix π).deviationMatrix ^ (n + 1)) *ᵥ
      M.policyReward π) :=
    hS.hasSum.map (mulVec.addMonoidHomLeft (M.policyReward π))
      (continuous_id.matrix_mulVec continuous_const)
  simp only [smul_mulVec] at hv
  rw [value_eq_inv_mulVec M π hγ₁, inv_one_sub_smul_eq_laurent hP (NNReal.coe_pos.2 hγ₀)
    (NNReal.coe_lt_one.2 hγ₁) hu hD, smul_mulVec, add_mulVec, smul_mulVec, ← gain_def,
    hv.tsum_eq]

/-- **The gain is the limit of the normalized discounted values** [P, Corollary 8.2.5]:
`(1 - γ) v^π_γ s → g^π s` as `γ ↑ 1`. -/
theorem tendsto_one_sub_mul_value (s : 𝓢) :
    Tendsto (fun γ : ℝ≥0 ↦ (1 - (γ : ℝ)) * M.value γ π s) (𝓝[<] 1) (𝓝 (M.gain π s)) := by
  refine ((((M.continuous_mulVec_policyReward_apply π s).tendsto _).comp
    (tendsto_one_sub_smul_inv_one_sub_smul_limitingMatrix (M.stateMatrix_mem_rowStochastic π))).comp
    (NNReal.tendsto_coe_nhdsLT 1)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with γ hγ
  simp [M.value_eq_inv_mulVec π (Set.mem_Iio.1 hγ), smul_mulVec]

/-- **Laurent expansion to first order** [P, Corollary 8.2.4]:
`v^π_γ = (1 - γ)⁻¹ g^π + h^π + o(1)` as `γ ↑ 1`. -/
theorem tendsto_value_sub_inv_one_sub_mul_gain (s : 𝓢) :
    Tendsto (fun γ : ℝ≥0 ↦ M.value γ π s - (1 - (γ : ℝ))⁻¹ * M.gain π s) (𝓝[<] 1)
      (𝓝 (M.bias π s)) := by
  refine ((((M.continuous_mulVec_policyReward_apply π s).tendsto _).comp
    (tendsto_inv_smul_one_sub_smul_inv_one_sub_smul_sub_deviationMatrix
      (M.stateMatrix_mem_rowStochastic π))).comp (NNReal.tendsto_coe_nhdsLT 1)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with γ hγ
  have hγ' : 1 - (γ : ℝ) ≠ 0 := sub_ne_zero.2 (NNReal.coe_lt_one.2 (Set.mem_Iio.1 hγ)).ne'
  simp only [Function.comp_apply, smul_mulVec, sub_mulVec, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, M.value_eq_inv_mulVec π (Set.mem_Iio.1 hγ), gain_def]
  field_simp

end Learning.MDP
