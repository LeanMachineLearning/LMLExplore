/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Episodic.Value
public import LMLExplore.Probability.Kernel.HorizonSum
import LMLExplore.Analysis.Convex.Integral
import LMLExplore.MeasureTheory.Integral.BoundedMeasurable

/-!
# Values of episodic MDPs as finite-horizon sums, and the levels of [LWCGC24, Lemma 9]

For a Markov policy `π : ℕ → Kernel 𝓢 𝓐` of an episodic MDP `M`, the state kernel
`M.stateKernel π h = M.trans h ∘ₖ (Kernel.id ×ₖ π h)` of the step `h` draws an action from `π h s`
and then the next state from `M.trans h`, and the policy reward `M.policyReward π h s` is the
average of the mean rewards `r_h (s, a)` over the actions of `π h s`. For bounded rewards, the
value of `π` is the finite-horizon sum of its rewards along its state kernels
(`value_eq_horizonSum`):
`V^π_h = horizonSum (M.stateKernel π) H (M.policyReward π) h`.

The levels `M.valueLevel H π l` of [LWCGC24, (62)] are the levels
`ProbabilityTheory.Kernel.horizonSumLevel` of this finite-horizon sum: `V 0 = V^π` and
`V (l + 1) h = ∑_{j ≥ h} P_π^{h:j} √Var_{P_π j}(V l (j + 1))`. For rewards in `[0, C]`, the level
`l` lies in `[0, C H √H ^ l]` [LWCGC24, Lemma 12]. Comparing two episodic MDPs `M` and `M'` with
the same mean rewards, whose state kernels deviate by the Bernstein-type bound
`√(2 Var_{P_π j}(V l (j + 1)) L / N) + C H √H ^ l L / (3 N)` on the levels `l ≤ m`, with
`H ≤ 4 ^ m` and `18 L H ≤ N`, the values of `π` satisfy
`|V'^π_h - V^π_h| ≤ 4 C H √(2 L H / N)` [LWCGC24, Lemma 9]. This is the deterministic part of the
analysis of model-based planning with a generative model in finite horizon [LWCGC24, §7.3].

## Main definitions

* `Learning.MDP.Episodic.EpisodicMDP.stateKernel M π h`: the state kernel of `π` at the step `h`.
* `Learning.MDP.Episodic.EpisodicMDP.policyReward M π h`: the reward of `π` at the step `h`.
* `Learning.MDP.Episodic.EpisodicMDP.valueLevel M H π`: the levels of [LWCGC24, (62)].

## Main statements

* `Learning.MDP.Episodic.EpisodicMDP.value_eq_horizonSum`: for bounded rewards, the value of `π`
  is the finite-horizon sum of its rewards along its state kernels.
* `Learning.MDP.Episodic.EpisodicMDP.valueLevel_mem_Icc`: for rewards in `[0, C]`, the level `l`
  lies in `[0, C H √H ^ l]`.
* `Learning.MDP.Episodic.EpisodicMDP.valueLevel_congr`: the levels from the step `h₀` on only
  depend on the transitions, the mean rewards and the policy from `h₀` on.
* `Learning.MDP.Episodic.EpisodicMDP.abs_value_sub_value_le_of_abs_integral_stateKernel_sub_le`:
  the deterministic part of model-based planning in finite horizon [LWCGC24, Lemma 9].

## References

* [G. Li, Y. Wei, Y. Chi, Y. Gu and Y. Chen, *Breaking the sample size barrier in model-based
  reinforcement learning with a generative model*, Operations Research, 2024][LWCGC24], §7
  (arXiv:2005.12900)
-/

public section

open MeasureTheory ProbabilityTheory LMLExplore

namespace Learning.MDP.Episodic.EpisodicMDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}

/-! ### The state kernels and the rewards of a Markov policy -/

section StateKernel

variable (M : EpisodicMDP 𝓢 𝓐) (π : ℕ → Kernel 𝓢 𝓐)

/-- The state kernel of the Markov policy `π` at the step `h`: from the state `s`, draw an action
`a` from `π h s`, then the next state from `M.trans h (s, a)`. -/
noncomputable def stateKernel (h : ℕ) : Kernel 𝓢 𝓢 :=
  M.trans h ∘ₖ (Kernel.id ×ₖ π h)

lemma stateKernel_def (h : ℕ) : M.stateKernel π h = M.trans h ∘ₖ (Kernel.id ×ₖ π h) :=
  (rfl)

instance (h : ℕ) : IsSFiniteKernel (M.stateKernel π h) := by
  rw [stateKernel_def]
  infer_instance

instance [∀ h, IsMarkovKernel (π h)] (h : ℕ) : IsMarkovKernel (M.stateKernel π h) := by
  rw [stateKernel_def]
  infer_instance

/-- The reward `∫ a, r_h (s, a) ∂(π h s)` of the Markov policy `π` at the step `h` and the
state `s`. -/
noncomputable def policyReward (h : ℕ) (s : 𝓢) : ℝ :=
  ∫ a, M.meanReward h s a ∂(π h s)

lemma policyReward_def (h : ℕ) (s : 𝓢) :
    M.policyReward π h s = ∫ a, M.meanReward h s a ∂(π h s) :=
  (rfl)

variable {M π}

/-- Integrating against the state kernel of `π` at the step `h` from `s` averages over the
actions `a` of `π h s` the integral against `M.trans h (s, a)`. -/
lemma integral_stateKernel [∀ h, IsSFiniteKernel (π h)] {h : ℕ} {s : 𝓢} {v : 𝓢 → ℝ}
    (hv : Integrable v (M.stateKernel π h s)) :
    ∫ s', v s' ∂(M.stateKernel π h s) = ∫ a, ∫ s', v s' ∂(M.trans h (s, a)) ∂(π h s) := by
  rw [stateKernel_def] at hv ⊢
  have h' := hv.integral_comp.aestronglyMeasurable
  rw [Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod] at h'
  rw [Kernel.integral_comp hv, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    integral_map measurable_prodMk_left.aemeasurable h']

/-- The state kernel of the deterministic Markov policy playing `d h s` draws the next state from
`M.trans h (s, d h s)`. -/
@[simp]
lemma stateKernel_deterministic_apply {d : ℕ → 𝓢 → 𝓐} (hd : ∀ h, Measurable (d h)) (h : ℕ)
    (s : 𝓢) :
    M.stateKernel (fun h ↦ Kernel.deterministic (d h) (hd h)) h s = M.trans h (s, d h s) := by
  ext t ht
  rw [stateKernel_def, Kernel.comp_apply' _ _ _ ht, Kernel.prod_apply, Kernel.id_apply,
    Kernel.deterministic_apply, Measure.dirac_prod_dirac,
    lintegral_dirac' _ ((M.trans h).measurable_coe ht)]

/-- The reward of `π` at every step is a measurable function of the state. -/
lemma measurable_policyReward [∀ h, IsSFiniteKernel (π h)] (h : ℕ) :
    Measurable (M.policyReward π h) :=
  ((M.measurable_meanReward h).stronglyMeasurable.integral_kernel_prod_right'
    (κ := π h)).measurable

/-- For rewards in `[a, b]`, the reward of `π` lies in `[a, b]`. -/
lemma policyReward_mem_Icc [∀ h, IsMarkovKernel (π h)] {a b : ℝ}
    (hM : M.RewardsIn (Set.Icc a b)) (h : ℕ) (s : 𝓢) : M.policyReward π h s ∈ Set.Icc a b :=
  integral_mem_Icc_of_ae_mem_Icc
    ((M.measurable_meanReward h).comp measurable_prodMk_left).aemeasurable
    (.of_forall fun a' ↦ meanReward_mem_Icc hM h s a')

/-- The reward of the deterministic Markov policy playing `d h s` is the mean reward of this
action. -/
@[simp]
lemma policyReward_deterministic {d : ℕ → 𝓢 → 𝓐} (hd : ∀ h, Measurable (d h)) (h : ℕ)
    (s : 𝓢) :
    M.policyReward (fun h ↦ Kernel.deterministic (d h) (hd h)) h s = M.meanReward h s (d h s) :=
  Kernel.integral_deterministic' (hd h)
    ((M.measurable_meanReward h).comp measurable_prodMk_left).stronglyMeasurable

end StateKernel

/-! ### Values as finite-horizon sums -/

variable {M M' : EpisodicMDP 𝓢 𝓐} {H : ℕ} {π π' : ℕ → Kernel 𝓢 𝓐}

/-- **The value of a Markov policy is the finite-horizon sum of its rewards along its state
kernels**: for bounded rewards, `V^π_h = horizonSum (M.stateKernel π) H (M.policyReward π) h`. -/
theorem value_eq_horizonSum [∀ h, IsMarkovKernel (π h)] {a b : ℝ}
    (hM : M.RewardsIn (Set.Icc a b)) (h : ℕ) :
    M.value H π h = Kernel.horizonSum (M.stateKernel π) H (M.policyReward π) h := by
  funext s
  by_cases hh : h < H
  · have hV := value_eq_horizonSum hM (h + 1)
    have hVm := measurable_value (M := M) (H := H) (π := π) (h + 1)
    have hVI := value_mem_Icc (H := H) (π := π) hM (h + 1)
    rw [Kernel.horizonSum_of_lt hh, ← hV, integral_stateKernel (integrable_value hM (h + 1)),
      value_of_lt hh, policyReward_def]
    simp_rw [qValue_def]
    exact integral_add (.of_mem_Icc a b
      ((M.measurable_meanReward h).comp measurable_prodMk_left).aemeasurable
      (.of_forall fun a' ↦ meanReward_mem_Icc hM h s a'))
      (.of_mem_Icc _ _ (((hVm.stronglyMeasurable.integral_kernel
        (κ := M.trans h)).measurable).comp measurable_prodMk_left).aemeasurable
        (.of_forall fun a' ↦ integral_mem_Icc_of_ae_mem_Icc hVm.aemeasurable (.of_forall hVI)))
  · rw [value_of_le (not_lt.1 hh), Kernel.horizonSum_of_le (not_lt.1 hh)]
termination_by H - h

/-! ### The levels of [LWCGC24, Lemma 9] -/

variable (M H π) in
/-- The levels of [LWCGC24, (62)] for a Markov policy `π`, with state kernels `P_π`: the levels
`ProbabilityTheory.Kernel.horizonSumLevel` of the finite-horizon sum of the rewards of `π` along
its state kernels. The level `0` is the value `V^π` for bounded rewards (`valueLevel_zero`), and
`V (l + 1) h = ∑_{j ≥ h} P_π^{h:j} √Var_{P_π j}(V l (j + 1))`. -/
noncomputable def valueLevel (l h : ℕ) : 𝓢 → ℝ :=
  Kernel.horizonSumLevel (M.stateKernel π) H (M.policyReward π) l h

variable (M H π) in
lemma valueLevel_def (l h : ℕ) :
    M.valueLevel H π l h = Kernel.horizonSumLevel (M.stateKernel π) H (M.policyReward π) l h :=
  (rfl)

/-- For bounded rewards, the level `0` is the value of `π`. -/
lemma valueLevel_zero [∀ h, IsMarkovKernel (π h)] {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) :
    M.valueLevel H π 0 = M.value H π := by
  funext h s
  rw [valueLevel, Kernel.horizonSumLevel_zero, value_eq_horizonSum hM]

/-- The levels are measurable. -/
lemma measurable_valueLevel [∀ h, IsSFiniteKernel (π h)] (l h : ℕ) :
    Measurable (M.valueLevel H π l h) :=
  Kernel.measurable_horizonSumLevel measurable_policyReward l h

/-- For rewards in `[0, C]`, the level `l` lies in `[0, C H √H ^ l]` [LWCGC24, Lemma 12]. -/
lemma valueLevel_mem_Icc [∀ h, IsMarkovKernel (π h)] {C : ℝ} (hM : M.RewardsIn (Set.Icc 0 C))
    (l h : ℕ) (s : 𝓢) : M.valueLevel H π l h s ∈ Set.Icc 0 (C * H * √H ^ l) :=
  Kernel.horizonSumLevel_mem_Icc measurable_policyReward (policyReward_mem_Icc hM) l h s

/-- The levels from the step `h₀` on only depend on the transition kernels, the mean rewards and
the policy from the step `h₀` on. -/
theorem valueLevel_congr {h₀ : ℕ} (htrans : ∀ h, h₀ ≤ h → M.trans h = M'.trans h)
    (hr : ∀ h, h₀ ≤ h → M.meanReward h = M'.meanReward h) (hπ : ∀ h, h₀ ≤ h → π h = π' h)
    (l : ℕ) {h : ℕ} (hh : h₀ ≤ h) : M.valueLevel H π l h = M'.valueLevel H π' l h := by
  funext s
  rw [valueLevel, valueLevel, Kernel.horizonSumLevel_congr (κ' := M'.stateKernel π')
    (g := M'.policyReward π') (fun j hj ↦ ?_) (fun j hj ↦ ?_) l hh]
  · rw [stateKernel_def, stateKernel_def, htrans j hj, hπ j hj]
  · funext s'
    rw [policyReward_def, policyReward_def, hr j hj, hπ j hj]

/-- **The deterministic part of model-based planning in finite horizon** [LWCGC24, Lemma 9].
Let `M` and `M'` be episodic MDPs with the same rewards, in `[0, C]`, and `π` a Markov
policy, with state kernels `P_π` in `M` and `P'_π` in `M'`. Let `V = M.valueLevel H π` be the
levels `V 0 = V^π` and `V (l + 1) h = ∑_{j ≥ h} P_π^{h:j} √Var_{P_π j}(V l (j + 1))` of
[LWCGC24, (62)], bounded by `C H √H ^ l`, and `H ≤ 4 ^ m`. Let `L ≥ 0`, `N > 0` and
`18 L H ≤ N`. If `P'_π` deviates from `P_π` on the levels `l ≤ m` by the bound
`√(2 Var_{P_π j}(V l (j + 1)) L / N) + C H √H ^ l L / (3 N)` of Bernstein's inequality at the
level `L`, at every step `j < H`, then the value of `π` in `M'` satisfies
`|V'^π_h - V^π_h| ≤ 4 C H √(2 L H / N)`.

This is `ProbabilityTheory.Kernel.abs_horizonSum_sub_horizonSum_le_of_abs_sub_le` with
`ε = 2 L / N`, for the finite-horizon sum forms of the two values. -/
theorem abs_value_sub_value_le_of_abs_integral_stateKernel_sub_le
    (hM' : M'.reward = M.reward) {C : ℝ} (hM : M.RewardsIn (Set.Icc 0 C))
    (π : ℕ → Kernel 𝓢 𝓐) [∀ h, IsMarkovKernel (π h)] {m : ℕ} (hm : H ≤ 4 ^ m) {N L : ℝ}
    (hN : 0 < N) (hL : 0 ≤ L) (hNL : 18 * L * H ≤ N)
    (hdev : ∀ l ≤ m, ∀ j < H, ∀ s,
      |∫ s', M.valueLevel H π l (j + 1) s' ∂(M'.stateKernel π j s) -
          ∫ s', M.valueLevel H π l (j + 1) s' ∂(M.stateKernel π j s)| ≤
        √(2 * Var[M.valueLevel H π l (j + 1); M.stateKernel π j s] * L / N) +
          C * H * √H ^ l * L / (3 * N))
    (h : ℕ) (s : 𝓢) :
    |M'.value H π h s - M.value H π h s| ≤ 4 * C * H * √(2 * L * H / N) := by
  simp only [valueLevel_def] at hdev
  have hM'R : M'.RewardsIn (Set.Icc 0 C) := by
    have h₀ := hM
    rw [rewardsIn_def] at h₀ ⊢
    rwa [hM']
  have hr : M'.policyReward π = M.policyReward π := by
    funext j s'
    simp only [policyReward_def, meanReward_def, hM']
  rw [value_eq_horizonSum hM'R, value_eq_horizonSum hM, hr]
  have hε : 9 * (2 * L / N) * H ≤ 1 := by
    rw [show 9 * (2 * L / N) * H = 18 * L * H / N by ring, div_le_one hN]
    exact hNL
  refine (Kernel.abs_horizonSum_sub_horizonSum_le_of_abs_sub_le measurable_policyReward
    (policyReward_mem_Icc hM) hm (div_nonneg (by linarith) hN.le) hε
    (fun l hl j hj y ↦ (hdev l hl j hj y).trans ?_) h s).trans_eq (by ring_nf)
  have hb : 0 ≤ C * H * √H ^ l :=
    (valueLevel_mem_Icc (H := H) (π := π) hM l 0 y).1.trans
      (valueLevel_mem_Icc (H := H) (π := π) hM l 0 y).2
  refine add_le_add (le_of_eq (by ring_nf)) ?_
  calc C * H * √H ^ l * L / (3 * N) = 2 * L / N * (C * H * √H ^ l) / 6 := by
        field_simp
        ring
    _ ≤ 2 * L / N * (C * H * √H ^ l) :=
        div_le_self (mul_nonneg (div_nonneg (by linarith) hN.le) hb) (by norm_num)

end Learning.MDP.Episodic.EpisodicMDP
