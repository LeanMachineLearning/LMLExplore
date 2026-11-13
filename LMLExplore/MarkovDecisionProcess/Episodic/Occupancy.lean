/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Episodic.Value
public import LMLExplore.Probability.Kernel.Composition.IntegralCompProd

/-!
# Occupancy measures of Markov policies in an episodic MDP

For an episodic MDP `M : EpisodicMDP 𝓢 𝓐`, a Markov policy `π : ℕ → Kernel 𝓢 𝓐` and an initial
law `μ` of the state at the step `0`, the state marginals `μ_h` and the occupancy measures
`d^π_h` are defined by the forward recursion
* `μ_0 = μ` and `μ_{h+1} = P_h ∘ₘ d^π_h`;
* `d^π_h = μ_h ⊗ₘ π_h`.

The state marginals are those of the sequence of transition kernels `M.trans`,
`Learning.MDP.stateMarginal M.trans π μ`, the definition shared with stationary MDPs.

Along every run of `π` in the time-augmented MDP `M.augmented` started at the step `0`, `μ_h` is
the law of the state of round `h` and `d^π_h` is the law of the state-action pair of round `h`
(`hasLaw_obs_fst_markov`, `hasLaw_obs_fst_action_markov`). The occupancy measures satisfy the flow
equation: the state marginal of `d^π_{h+1}` is `P_h ∘ₘ d^π_h` (`occupancy_add_one_fst`).

Every expectation of a sum of functions of the state-action pairs of an episode is a sum of
integrals against the occupancy measures (`integral_sum_eq_sum_integral_occupancy`). In particular,
the value of `π` is `∫ V^π_0 dμ = ∑_{h < H} ∫ r_h d d^π_h`
(`integral_value_eq_sum_integral_occupancy`). This follows from the telescoping identity
`integral_eq_sum_integral_occupancy_add`, valid for every bounded measurable sequence of functions
`V_h` of the state: `∫ V_0 dμ` is the sum over the steps `h < H` of the integrals of
`V_h (s) - ∫ V_{h+1} dP_h (s, a)` against `d^π_h`, plus `∫ V_H dμ_H`. These identities are the
episodic counterparts of those of the discounted occupancy measure `Learning.MDP.occupancy`.

## Main definitions

* `Learning.MDP.Episodic.EpisodicMDP.occupancy M π μ h`: the occupancy measure `d^π_h`, the law of
  the state-action pair at the step `h`.

## Main statements

* `Learning.MDP.Episodic.EpisodicMDP.stateMarginal_trans_add_one`: the recursion
  `μ_{h+1} = P_h ∘ₘ d^π_h` of the state marginals.
* `Learning.MDP.Episodic.EpisodicMDP.occupancy_fst`,
  `Learning.MDP.Episodic.EpisodicMDP.occupancy_add_one_fst`: the state marginal of `d^π_h` is
  `μ_h`, and the flow equation `(d^π_{h+1}).fst = P_h ∘ₘ d^π_h`.
* `Learning.MDP.Episodic.EpisodicMDP.integral_occupancy`: the integral against `d^π_h` is the
  integral against `μ_h` of the integral against `π_h`.
* `Learning.MDP.Episodic.EpisodicMDP.integral_sub_integral_stateMarginal`:
  `∫ (V s - ∫ Q (s, a) dπ_h(a | s)) dμ_h = ∫ (V - Q) dd^π_h`.
* `Learning.MDP.Episodic.EpisodicMDP.integral_eq_sum_integral_occupancy_add`: the telescoping
  identity for a bounded measurable sequence of functions of the state.
* `Learning.MDP.Episodic.EpisodicMDP.integral_qValue_occupancy`: before the horizon, the integral
  of `Q^π_h` against `d^π_h` is the integral of `V^π_h` against `μ_h`.
* `Learning.MDP.Episodic.EpisodicMDP.integral_value_eq_sum_integral_occupancy`: the value of `π`
  is the sum of the integrals of the mean rewards against the occupancy measures.
* `Learning.MDP.Episodic.EpisodicMDP.hasLaw_obs_fst_markov`,
  `Learning.MDP.Episodic.EpisodicMDP.hasLaw_obs_fst_action_markov`: along a run of `π` in the
  augmented MDP started at the step `0`, the state of round `h` has law `μ_h` and the state-action
  pair of round `h` has law `d^π_h`.
* `Learning.MDP.Episodic.EpisodicMDP.integral_sum_eq_sum_integral_occupancy`: along such a run,
  `E [∑_{h < N} f_h (S_h, A_h)] = ∑_{h < N} ∫ f_h d d^π_h`.

## References

* [AJKS] A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022, §1.2.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset LMLExplore

namespace Learning.MDP.Episodic.EpisodicMDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}

/-! ### State marginals and occupancy measures -/

section Defs

variable (M : EpisodicMDP 𝓢 𝓐) (π : ℕ → Kernel 𝓢 𝓐) (μ : Measure 𝓢)

/-- The occupancy measure `d^π_h = μ_h ⊗ₘ π_h` of the Markov policy `π` at the step `h`, from the
initial law `μ` at the step `0`: the law of the state-action pair at the step `h`. -/
noncomputable def occupancy (h : ℕ) : Measure (𝓢 × 𝓐) :=
  stateMarginal M.trans π μ h ⊗ₘ π h

lemma occupancy_def (h : ℕ) : M.occupancy π μ h = stateMarginal M.trans π μ h ⊗ₘ π h :=
  (rfl)

/-- The law `μ_{h+1}` of the state at the step `h + 1` is `P_h ∘ₘ d^π_h`. -/
lemma stateMarginal_trans_add_one (h : ℕ) :
    stateMarginal M.trans π μ (h + 1) = M.trans h ∘ₘ M.occupancy π μ h := by
  rw [stateMarginal_add_one, occupancy_def]

@[simp]
lemma occupancy_zero : M.occupancy π μ 0 = μ ⊗ₘ π 0 := by
  rw [occupancy_def, stateMarginal_zero]

instance (h : ℕ) : SFinite (M.occupancy π μ h) := by
  rw [occupancy_def]
  infer_instance

instance [IsProbabilityMeasure μ] [∀ h, IsMarkovKernel (π h)] (h : ℕ) :
    IsProbabilityMeasure (M.occupancy π μ h) := by
  rw [occupancy_def]
  infer_instance

variable [SFinite μ] [∀ h, IsMarkovKernel (π h)]

/-- The state marginal of the occupancy measure at the step `h` is the law `μ_h` of the state. -/
@[simp]
lemma occupancy_fst (h : ℕ) : (M.occupancy π μ h).fst = stateMarginal M.trans π μ h :=
  Measure.fst_compProd _ _

/-- **The flow equation** of the occupancy measures: the state marginal of `d^π_{h+1}` is
`P_h ∘ₘ d^π_h`. -/
theorem occupancy_add_one_fst (h : ℕ) :
    (M.occupancy π μ (h + 1)).fst = M.trans h ∘ₘ M.occupancy π μ h := by
  rw [occupancy_fst, stateMarginal_trans_add_one]

end Defs

/-! ### Integrals against the occupancy measures -/

section Integral

variable {M : EpisodicMDP 𝓢 𝓐} {π : ℕ → Kernel 𝓢 𝓐} {μ : Measure 𝓢}

/-- The integral of a function of the state against the occupancy measure at the step `h` is its
integral against the law `μ_h` of the state. -/
lemma integral_occupancy_fst [SFinite μ] [∀ h, IsMarkovKernel (π h)] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {h : ℕ}
    {f : 𝓢 → E} (hf : AEStronglyMeasurable f (stateMarginal M.trans π μ h)) :
    ∫ p, f p.1 ∂(M.occupancy π μ h) = ∫ s, f s ∂(stateMarginal M.trans π μ h) := by
  rw [← occupancy_fst M π μ h] at hf ⊢
  exact (integral_map measurable_fst.aemeasurable hf).symm

/-- The integral of a function `f` against the law `μ_{h+1}` of the state at the step `h + 1` is
the integral against the occupancy measure at the step `h` of the integral of `f` against the
transition kernel `P_h`. -/
lemma integral_stateMarginal_add_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℕ} {f : 𝓢 → E} (hf : Integrable f (stateMarginal M.trans π μ (h + 1))) :
    ∫ s, f s ∂(stateMarginal M.trans π μ (h + 1)) =
      ∫ p, ∫ s, f s ∂(M.trans h p) ∂(M.occupancy π μ h) := by
  rw [stateMarginal_trans_add_one, Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [Kernel.integral_comp hf, Kernel.const_apply]

/-- The integral of a function `f` of the state-action pair against the occupancy measure `d^π_h`
is the integral against the law `μ_h` of the state of the integral of `f` against the policy
`π_h`. -/
lemma integral_occupancy [SFinite μ] [∀ h, IsMarkovKernel (π h)] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {h : ℕ} {f : 𝓢 × 𝓐 → E}
    (hf : Integrable f (M.occupancy π μ h)) :
    ∫ p, f p ∂(M.occupancy π μ h) = ∫ s, ∫ a, f (s, a) ∂(π h s) ∂(stateMarginal M.trans π μ h) := by
  rw [occupancy_def] at hf ⊢
  exact Measure.integral_compProd hf

/-- The integral against the law `μ_h` of the state of `V s - ∫ Q (s, a) dπ_h(a | s)` is the
integral of `V s - Q (s, a)` against the occupancy measure `d^π_h`. -/
lemma integral_sub_integral_stateMarginal [SFinite μ] [∀ h, IsMarkovKernel (π h)] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {h : ℕ} {V : 𝓢 → E}
    {Q : 𝓢 → 𝓐 → E} (hV : Integrable V (stateMarginal M.trans π μ h))
    (hQ : Integrable (fun p : 𝓢 × 𝓐 ↦ Q p.1 p.2) (M.occupancy π μ h)) :
    ∫ s, (V s - ∫ a, Q s a ∂(π h s)) ∂(stateMarginal M.trans π μ h) =
      ∫ p, (V p.1 - Q p.1 p.2) ∂(M.occupancy π μ h) := by
  rw [occupancy_def] at hQ ⊢
  exact Measure.integral_sub_integral_eq_integral_compProd hV hQ

variable [IsProbabilityMeasure μ] [∀ h, IsMarkovKernel (π h)]

/-- **Telescoping identity.** For a bounded measurable sequence of functions `V_h` of the state,
`∫ V_0 dμ` is the sum over the steps `h < H` of the integrals of `V_h (s) - ∫ V_{h+1} dP_h (s, a)`
against the occupancy measures `d^π_h`, plus the integral of `V_H` against the law `μ_H` of the
state at the step `H`. -/
theorem integral_eq_sum_integral_occupancy_add {V : ℕ → 𝓢 → ℝ} (hV : ∀ h, Measurable (V h))
    {B : ℝ} (hVB : ∀ h s, |V h s| ≤ B) (H : ℕ) :
    ∫ s, V 0 s ∂μ =
      ∑ h ∈ range H, ∫ p, (V h p.1 - ∫ s', V (h + 1) s' ∂(M.trans h p)) ∂(M.occupancy π μ h) +
        ∫ s, V H s ∂(stateMarginal M.trans π μ H) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [ih, sum_range_succ, add_assoc,
      integral_sub (integrable_of_abs_le (f := fun p : 𝓢 × 𝓐 ↦ V H p.1)
          ((hV H).comp measurable_fst) (fun p ↦ hVB H p.1) _)
        (integrable_integral_kernel_of_abs_le (hV (H + 1)) (hVB (H + 1)) _ _),
      integral_occupancy_fst (hV H).aestronglyMeasurable,
      ← integral_stateMarginal_add_one (integrable_of_abs_le (hV (H + 1)) (hVB (H + 1)) _)]
    ring

/-- Before the horizon, the integral of the action value `Q^π_h` against the occupancy measure
`d^π_h` is the integral of the value `V^π_h` against the law `μ_h` of the state. -/
theorem integral_qValue_occupancy {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) {H h : ℕ}
    (hh : h < H) :
    ∫ p, M.qValue H π h p.1 p.2 ∂(M.occupancy π μ h) =
      ∫ s, M.value H π h s ∂(stateMarginal M.trans π μ h) := by
  rw [integral_occupancy (.of_mem_Icc _ _ (measurable_qValue h).aemeasurable
    (.of_forall fun p ↦ qValue_mem_Icc hM hh p.1 p.2))]
  exact integral_congr_ae (.of_forall fun s ↦ (value_of_lt hh s).symm)

/-- **The value as an occupancy integral.** For rewards in `[-C, C]`, the value of the Markov
policy `π` from the initial law `μ` is the sum over the steps `h < H` of the integrals of the
mean rewards `r_h` against the occupancy measures `d^π_h`. -/
theorem integral_value_eq_sum_integral_occupancy {C : ℝ} (hM : M.RewardsIn (Set.Icc (-C) C))
    (H : ℕ) :
    ∫ s, M.value H π 0 s ∂μ =
      ∑ h ∈ range H, ∫ p, M.meanReward h p.1 p.2 ∂(M.occupancy π μ h) := by
  rw [integral_eq_sum_integral_occupancy_add (M := M) (π := π) measurable_value
    (abs_value_le_mul_abs hM) H]
  simp only [value_self, integral_zero, add_zero]
  refine sum_congr rfl fun h hh ↦ ?_
  have hh : h < H := mem_range.1 hh
  have hr : Integrable (fun p : 𝓢 × 𝓐 ↦ M.meanReward h p.1 p.2) (M.occupancy π μ h) :=
    integrable_meanReward hM h
  have hQ : Integrable (fun p : 𝓢 × 𝓐 ↦ M.qValue H π h p.1 p.2) (M.occupancy π μ h) :=
    .of_mem_Icc _ _ (measurable_qValue h).aemeasurable
      (.of_forall fun p ↦ qValue_mem_Icc hM hh p.1 p.2)
  have hQr : Integrable (fun p : 𝓢 × 𝓐 ↦ M.qValue H π h p.1 p.2 - M.meanReward h p.1 p.2)
      (M.occupancy π μ h) :=
    hQ.sub hr
  -- `∫ V^π_{h+1} dP_h (s, a) = Q^π_h (s, a) - r_h (s, a)`
  have h_eq : (fun p : 𝓢 × 𝓐 ↦ M.value H π h p.1 - ∫ s', M.value H π (h + 1) s' ∂(M.trans h p)) =
      fun p ↦ M.value H π h p.1 - (M.qValue H π h p.1 p.2 - M.meanReward h p.1 p.2) := by
    ext p
    rw [qValue_def]
    ring
  have hV : Integrable (fun p : 𝓢 × 𝓐 ↦ M.value H π h p.1) (M.occupancy π μ h) :=
    integrable_of_abs_le ((measurable_value h).comp measurable_fst)
      (fun p ↦ abs_value_le_mul_abs hM h p.1) _
  rw [h_eq, integral_sub hV hQr, integral_sub hQ hr,
    integral_qValue_occupancy hM hh,
    integral_occupancy_fst (measurable_value h).aestronglyMeasurable]
  ring

end Integral

/-! ### Laws along the runs -/

section Runs

variable [Nonempty 𝓢] {M : EpisodicMDP 𝓢 𝓐} {π : ℕ → Kernel 𝓢 𝓐} [∀ h, IsMarkovKernel (π h)]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓢 × ℕ} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {μ : Measure (𝓢 × ℕ)}
  [IsProbabilityMeasure μ]

/-- Along a run of the Markov policy `π` in the augmented MDP from an initial law `μ`
concentrated on the step `0`, the state of round `h` has law `μ_h`, the state marginal of `π`
from the law `μ.map Prod.fst` of the initial state. -/
theorem hasLaw_obs_fst_markov (hμ : ∀ᵐ p ∂μ, p.2 = 0)
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ augMarkovPolicy π) (M.augmented.env μ) P)
    (n : ℕ) :
    HasLaw (fun ω ↦ (O n ω).1) (stateMarginal M.trans π (μ.map Prod.fst) n) P := by
  induction n with
  | zero =>
    rw [stateMarginal_zero]
    exact (hasLaw_map measurable_fst.aemeasurable).fun_comp (MDP.hasLaw_obs_zero h)
  | succ n ih =>
    have h_pair := ih.prodMk_of_hasCondDistrib (hasCondDistrib_action_obs_fst_markov hμ h n)
    have h_next := (hasCondDistrib_obs_fst_add_one hμ h n).hasLaw_comp
    rwa [h_pair.map_eq, zero_add, ← occupancy_def, ← stateMarginal_trans_add_one] at h_next

/-- Along a run of the Markov policy `π` in the augmented MDP from an initial law `μ`
concentrated on the step `0`, the state-action pair of round `h` has law `d^π_h`, the occupancy
measure of `π` from the law `μ.map Prod.fst` of the initial state. -/
theorem hasLaw_obs_fst_action_markov (hμ : ∀ᵐ p ∂μ, p.2 = 0)
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ augMarkovPolicy π) (M.augmented.env μ) P)
    (n : ℕ) :
    HasLaw (fun ω ↦ ((O n ω).1, A n ω)) (M.occupancy π (μ.map Prod.fst) n) P := by
  have h_act := hasCondDistrib_action_obs_fst_markov hμ h n
  rw [zero_add] at h_act
  exact (hasLaw_obs_fst_markov hμ h n).prodMk_of_hasCondDistrib h_act

/-- Along a run of the Markov policy `π` in the augmented MDP from an initial law `μ`
concentrated on the step `0`, the expectation of the sum over the first `N` rounds of functions
`f_h` of the state-action pairs is the sum of the integrals of the `f_h` against the occupancy
measures: `E [∑_{h < N} f_h (S_h, A_h)] = ∑_{h < N} ∫ f_h d d^π_h`. -/
theorem integral_sum_eq_sum_integral_occupancy {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hμ : ∀ᵐ p ∂μ, p.2 = 0)
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ augMarkovPolicy π) (M.augmented.env μ) P)
    {N : ℕ} {f : ℕ → 𝓢 × 𝓐 → E}
    (hf : ∀ n < N, Integrable (f n) (M.occupancy π (μ.map Prod.fst) n)) :
    ∫ ω, ∑ n ∈ range N, f n ((O n ω).1, A n ω) ∂P =
      ∑ n ∈ range N, ∫ p, f n p ∂(M.occupancy π (μ.map Prod.fst) n) := by
  rw [integral_finsetSum _ fun n hn ↦
    (hasLaw_obs_fst_action_markov hμ h n).integrable_fun_comp (hf n (mem_range.1 hn))]
  exact sum_congr rfl fun n hn ↦ (hasLaw_obs_fst_action_markov hμ h n).integral_comp
    (hf n (mem_range.1 hn)).aestronglyMeasurable

end Runs

end Learning.MDP.Episodic.EpisodicMDP
