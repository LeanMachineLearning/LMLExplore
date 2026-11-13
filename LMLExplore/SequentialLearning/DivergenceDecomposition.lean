/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.SequentialLearning.Algorithm
public import LMLExplore.SequentialLearning.FiniteActions
public import LMLExplore.SequentialLearning.StoppedHistory
public import LMLExplore.SequentialLearning.Wald
public import LeanMachineLearning.SequentialLearning.DivergenceDecomposition

import LMLExplore.InformationTheory.KullbackLeibler.ChainRule

/-!
# The divergence decomposition, reindexed by the actions, and the chain rule at a stopping time

LML's `IsAlgEnvSeq.klDiv_map_history_bandit` writes the relative entropy between the laws of the
histories of the first `M` rounds of one algorithm run against two stationary environments with
reward kernels `κ` and `κ'` as a sum over the rounds: `∑ t < M, E[KL(κ (A t) ‖ κ' (A t))]`. For a
finite set of actions, this file regroups the sum by the action played, which gives the
*divergence decomposition* of bandit lower bounds [LS, Lemma 15.1]:
`KL = ∑ a, E[N_a(M)] KL(κ a ‖ κ' a)`, where `N_a(M) = pullCount A a M` is the number of rounds
before `M` at which `a` was played. The regrouping is `LMLExplore.sum_lintegral_pullCount_mul`,
one of the Wald identities of `LMLExplore/SequentialLearning/Wald.lean`.

At a stopping time `τ`, the hitting time of a stopping rule `S`, the chain rule bounds the
relative entropy between the laws of the histories stopped by `S` under any two
algorithm-environment pairs `(alg, env)` and `(alg', env')` by the series over the rounds `t` of
the divergences of the step of round `t`, on the event that `S` has not stopped after the first `t`
rounds under `(alg, env)`. For countably generated spaces and a `τ` that is almost surely finite
under `(alg, env)`, this series is
`E[∑ t < τ, KL(stepKernel alg env t (H t) ‖ stepKernel alg' env' t (H t))]`. For one algorithm
against two stationary environments and an almost surely finite `τ`, it gives
`KL ≤ ∑ a, E[N_a(τ)] KL(κ a ‖ κ' a)`. This is the change of measure behind the lower bounds of
bandit identification.

## Main statements

* `Learning.IsAlgEnvSeq.klDiv_map_history_eq_sum_pullCount`: the divergence decomposition.
* `Learning.IsAlgEnvSeq.klDiv_map_history_eq_lintegral_pullCount_mul`: if the reward kernels
  agree outside the action `i`, then `KL = E[N_i(M)] KL(κ i ‖ κ' i)`.
* `Learning.IsAlgEnvSeq.klDiv_map_history_le_ofReal_integral_pullCount_mul`: if moreover
  `KL(κ i ‖ κ' i) ≤ c`, then `KL ≤ E[N_i(M)] c`.
* `Learning.klDiv_stoppedHistMeasure_le_tsum`: the chain rule at a stopping time for any two
  algorithm-environment pairs, as a series over the rounds of the divergences of the steps, with
  the law of the history restricted to the histories after which `S` has not stopped.
* `Learning.klDiv_stoppedHistMeasure_le_lintegral`: its integral form
  `KL ≤ E[∑ t < τ, KL(stepKernel alg env t (H t) ‖ stepKernel alg' env' t (H t))]`, for countably
  generated spaces and an almost surely finite hitting time `τ`.
* `Learning.IsAlgEnvSeq.klDiv_restrict_compProd_stepKernel_bandit`: for one algorithm against two
  stationary environments, the divergence of the step of round `t` on an event of the history of
  the first `t` rounds is the expected divergence between the reward kernels at the played action
  on that event.
* `Learning.klDiv_stoppedHistMeasure_le`: the divergence decomposition at a stopping time,
  `KL(stoppedHistMeasure alg (Environment.bandit κ) S ‖
    stoppedHistMeasure alg (Environment.bandit κ') S) ≤ ∑ a, E_κ[N_a(τ)] KL(κ a ‖ κ' a)` when the
  hitting time `τ` of `S` is almost surely finite under `κ`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 15.1.
* E. Kaufmann, O. Cappé and A. Garivier, *On the complexity of best-arm identification in
  multi-armed bandit models*, JMLR 17 (2016), proof of Lemma 1, for the decomposition at a
  stopping time.
* A. Garivier, P. Ménard and G. Stoltz, *Explore first, exploit next: the true shape of regret in
  bandit problems*, Mathematics of Operations Research 44(2) (2019), Section 2, for the chain rule
  at a stopping time.
* The proofs of the fixed-horizon statements are adapted from the formalization in the LMLPapers
  project
  (`LMLPapers/LeanMachineLearning/SequentialLearning/DivergenceDecomposition.lean`).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal

namespace Learning

section ChainRule

/-! ### The chain rule at a stopping time

Let `τ` be the hitting time of a stopping rule `S`. The algorithm `alg'.piecewise` and the
environment `env'.piecewise` below follow `(alg', env')` until `τ` and `(alg, env)` afterwards.
Their stopped history has the same law as under `(alg', env')` (`stoppedHistMeasure_congr`), and
the divergence between their trajectory and the trajectory under `(alg, env)` only collects the
rounds before `τ` (`klDiv_compProd_piecewise`). The data processing inequality for the stopped
history, a function of the trajectory, concludes. -/

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {alg alg' : Algorithm 𝓞 𝓐 𝓨} {env env' : Environment 𝓞 𝓐 𝓨}
  {S : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)}

/-- **Chain rule at a stopping time.** For two algorithms `alg`, `alg'` run against two
environments `env`, `env'` and a measurable stopping rule `S`, the divergence between the laws of
the histories stopped by `S` is at most the series over the rounds `t` of the divergences of the
step at round `t`, where the law of the history of the first `t` rounds under `(alg, env)` is
restricted to the histories after which `S` has not stopped. -/
theorem klDiv_stoppedHistMeasure_le_tsum (hS : MeasurableSet S) :
    klDiv (stoppedHistMeasure alg env S) (stoppedHistMeasure alg' env' S) ≤
      ∑' t, klDiv
        (((trajMeasure alg env).map (history IT.obs IT.action IT.feedback t)).restrict
          (notStoppedSet S t) ⊗ₘ stepKernel alg env t)
        (((trajMeasure alg env).map (history IT.obs IT.action IT.feedback t)).restrict
          (notStoppedSet S t) ⊗ₘ stepKernel alg' env' t) := by
  have hs : ∀ n, MeasurableSet (notStoppedSet S n) := measurableSet_notStoppedSet hS
  -- The stopped history under the pair that switches to `(alg, env)` at the stopping time has
  -- the same law as under `(alg', env')`.
  have h_swap : stoppedHistMeasure alg' env' S =
      stoppedHistMeasure (alg'.piecewise _ hs alg) (env'.piecewise _ hs env) S :=
    stoppedHistMeasure_congr hS fun _ _ hx ↦ (stepKernel_piecewise_of_mem alg' alg hx).symm
  have h := IT.isAlgEnvSeq_trajMeasure alg env
  have h' := IT.isAlgEnvSeq_trajMeasure (alg'.piecewise _ hs alg) (env'.piecewise _ hs env)
  have h_chain := h.klDiv_map_trajectory_stepKernel h'
  rw [h.map_trajectory, h'.map_trajectory] at h_chain
  calc klDiv (stoppedHistMeasure alg env S) (stoppedHistMeasure alg' env' S)
      ≤ klDiv (trajMeasure alg env)
          (trajMeasure (alg'.piecewise _ hs alg) (env'.piecewise _ hs env)) := by
        rw [h_swap, stoppedHistMeasure, stoppedHistMeasure]
        exact klDiv_map_le _ _ (measurable_stoppedValue_sigmaHistory IT.measurable_obs
          IT.measurable_action IT.measurable_feedback (measurable_hittingAfter_sigmaHistory
            IT.measurable_obs IT.measurable_action IT.measurable_feedback hS))
    _ = _ := by
        classical
        rw [h_chain]
        exact tsum_congr fun t ↦ by rw [stepKernel_piecewise, klDiv_compProd_piecewise]

/-- **Chain rule at a stopping time**, integral form. For two algorithms `alg`, `alg'` run against
two environments `env`, `env'` with countably generated spaces of observations, actions and
feedback, and a measurable stopping rule `S` whose hitting time `τ` is almost surely finite under
`(alg, env)`, the divergence between the laws of the histories stopped by `S` is at most
`E[∑ t < τ, KL(stepKernel alg env t (H t) ‖ stepKernel alg' env' t (H t))]`, where `H t` is the
history of the first `t` rounds under `(alg, env)`. -/
theorem klDiv_stoppedHistMeasure_le_lintegral [MeasurableSpace.CountablyGenerated 𝓞]
    [MeasurableSpace.CountablyGenerated 𝓐] [MeasurableSpace.CountablyGenerated 𝓨]
    (hS : MeasurableSet S)
    (hτ : ∀ᵐ ω ∂(trajMeasure alg env),
      hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0 ω ≠ ⊤) :
    klDiv (stoppedHistMeasure alg env S) (stoppedHistMeasure alg' env' S) ≤
      ∫⁻ ω, ∑ t ∈ range (ENat.toNat
          (hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0 ω)),
        klDiv (stepKernel alg env t (history IT.obs IT.action IT.feedback t ω))
          (stepKernel alg' env' t (history IT.obs IT.action IT.feedback t ω))
        ∂(trajMeasure alg env) := by
  have hH (t : ℕ) : Measurable (history (IT.obs (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨)) IT.action
      IT.feedback t) :=
    measurable_history IT.measurable_obs IT.measurable_action IT.measurable_feedback t
  have hf (t : ℕ) : Measurable fun ω ↦
      klDiv (stepKernel alg env t (history IT.obs IT.action IT.feedback t ω))
        (stepKernel alg' env' t (history IT.obs IT.action IT.feedback t ω)) :=
    (measurable_klDiv_kernel _ _).comp (hH t)
  refine (klDiv_stoppedHistMeasure_le_tsum hS).trans_eq ((tsum_congr fun t ↦ ?_).trans
    (tsum_setLIntegral_notStoppedSet IT.measurable_obs IT.measurable_action IT.measurable_feedback
      hS hτ hf))
  rw [klDiv_compProd_right_eq_lintegral,
    setLIntegral_map (measurableSet_notStoppedSet hS t) (measurable_klDiv_kernel _ _) (hH t)]

end ChainRule

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  [Fintype 𝓐] [DecidableEq 𝓐] [MeasurableSingletonClass 𝓐] [MeasurableSpace.CountablyGenerated 𝓨]
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {O' : ℕ → Ω' → Unit} {A' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}
  {alg : Algorithm Unit 𝓐 𝓨} {κ κ' : Kernel 𝓐 𝓨} [IsMarkovKernel κ] [IsMarkovKernel κ']

/-- **Divergence decomposition** [LS, Lemma 15.1]: the relative entropy between the laws of the
histories of the first `M` rounds of an algorithm run against two stationary environments with
reward kernels `κ` and `κ'` is `∑ a, E[N_a(M)] KL(κ a ‖ κ' a)`, where `N_a(M) = pullCount A a M`
is the number of rounds before `M` at which `a` was played. -/
lemma IsAlgEnvSeq.klDiv_map_history_eq_sum_pullCount
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit κ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (Environment.bandit κ') P') (M : ℕ) :
    klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M)) =
      ∑ a, (∫⁻ ω, (pullCount A a M ω : ℝ≥0∞) ∂P) * klDiv (κ a) (κ' a) := by
  have hsum : ∑ t ∈ range M, ∫⁻ ω, klDiv (κ (A t ω)) (κ' (A t ω)) ∂P =
      ∫⁻ ω, ∑ t ∈ range M, klDiv (κ (A t ω)) (κ' (A t ω)) ∂P :=
    (lintegral_finsetSum _ fun t _ ↦
      (measurable_klDiv_kernel κ κ').comp (h.measurable_action t)).symm
  rw [h.klDiv_map_history_bandit h' M, hsum]
  exact (LMLExplore.sum_lintegral_pullCount_mul (g := fun _ ↦ M) h.measurable_action
    measurable_const fun a ↦ klDiv (κ a) (κ' a)).symm

omit [Fintype 𝓐] in
/-- **Divergence decomposition** for reward kernels `κ` and `κ'` that agree outside the action
`i`: the relative entropy between the laws of the histories of the first `M` rounds is
`E[N_i(M)] KL(κ i ‖ κ' i)`. -/
lemma IsAlgEnvSeq.klDiv_map_history_eq_lintegral_pullCount_mul [Finite 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit κ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (Environment.bandit κ') P') {i : 𝓐} (hκ : ∀ a ≠ i, κ a = κ' a)
    (M : ℕ) :
    klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M)) =
      (∫⁻ ω, (pullCount A i M ω : ℝ≥0∞) ∂P) * klDiv (κ i) (κ' i) := by
  have := Fintype.ofFinite 𝓐
  rw [h.klDiv_map_history_eq_sum_pullCount h' M,
    sum_eq_single i (fun a _ ha ↦ by rw [hκ a ha, klDiv_self, mul_zero])
      (fun hi ↦ absurd (mem_univ i) hi)]

omit [Fintype 𝓐] in
/-- If the reward kernels `κ` and `κ'` agree outside the action `i` and
`KL(κ i ‖ κ' i) ≤ c`, then the relative entropy between the laws of the histories of the first `M`
rounds is at most `E[N_i(M)] c`. -/
lemma IsAlgEnvSeq.klDiv_map_history_le_ofReal_integral_pullCount_mul [Finite 𝓐]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit κ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (Environment.bandit κ') P') {i : 𝓐} (hκ : ∀ a ≠ i, κ a = κ' a)
    {c : ℝ} (hc : klDiv (κ i) (κ' i) ≤ ENNReal.ofReal c) (M : ℕ) :
    klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M)) ≤
      ENNReal.ofReal ((∫ ω, (pullCount A i M ω : ℝ) ∂P) * c) := by
  rw [h.klDiv_map_history_eq_lintegral_pullCount_mul h' hκ M,
    LMLExplore.lintegral_pullCount_eq_ofReal_integral h.measurable_action,
    ENNReal.ofReal_mul (integral_nonneg fun _ ↦ Nat.cast_nonneg _)]
  gcongr

section StoppingTime

/-! ### The divergence decomposition at a stopping time for one algorithm and two bandits -/

omit [Fintype 𝓐] [DecidableEq 𝓐] [MeasurableSingletonClass 𝓐] in
/-- The divergence of round `t` of an algorithm run against two stationary environments with
reward kernels `κ` and `κ'`, with the law of the history of the first `t` rounds restricted to a
measurable set `s`, is the expected divergence between the reward kernels at the played action on
the event that this history belongs to `s`. -/
lemma IsAlgEnvSeq.klDiv_restrict_compProd_stepKernel_bandit
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit κ) P) {t : ℕ} {s : Set (Hist Unit 𝓐 𝓨 t)}
    (hs : MeasurableSet s) :
    klDiv ((P.map (history O A Y t)).restrict s ⊗ₘ stepKernel alg (Environment.bandit κ) t)
        ((P.map (history O A Y t)).restrict s ⊗ₘ stepKernel alg (Environment.bandit κ') t) =
      ∫⁻ ω in history O A Y t ⁻¹' s, klDiv (κ (A t ω)) (κ' (A t ω)) ∂P := by
  have hX : Measurable fun ω ↦ ((history O A Y t ω, O t ω), A t ω) :=
    ((h.measurable_history t).prodMk (h.measurable_obs t)).prodMk (h.measurable_action t)
  -- The restriction to `s` of the law of the history, followed by the observation and the action
  -- of round `t`, is the restricted joint law of the history, the observation and the action.
  have h_joint : (P.map (history O A Y t)).restrict s ⊗ₘ Kernel.const _ (Measure.dirac ()) ⊗ₘ
        alg.policy t =
      (P.map fun ω ↦ ((history O A Y t ω, O t ω), A t ω)).restrict ((s ×ˢ .univ) ×ˢ .univ) := by
    rw [Measure.compProd_restrict_left _ _ hs, Measure.compProd_restrict_left _ _ (hs.prod .univ),
      ← obs_bandit (ν := κ) t, ← (h.hasCondDistrib_obs t).map_eq,
      ← (h.hasCondDistrib_action t).map_eq]
  -- Reassociated, the two steps only differ in their feedback kernels.
  have h_assoc : klDiv
        ((P.map (history O A Y t)).restrict s ⊗ₘ stepKernel alg (Environment.bandit κ) t)
        ((P.map (history O A Y t)).restrict s ⊗ₘ stepKernel alg (Environment.bandit κ') t) =
      klDiv ((P.map fun ω ↦ ((history O A Y t ω, O t ω), A t ω)).restrict
          ((s ×ˢ .univ) ×ˢ .univ) ⊗ₘ κ.prodMkLeft _)
        ((P.map fun ω ↦ ((history O A Y t ω, O t ω), A t ω)).restrict
          ((s ×ˢ .univ) ×ˢ .univ) ⊗ₘ κ'.prodMkLeft _) := by
    rw [stepKernel_bandit, stepKernel_bandit, klDiv_compProd_assoc, klDiv_compProd_assoc, h_joint]
  rw [h_assoc, klDiv_compProd_right_eq_lintegral,
    setLIntegral_map ((hs.prod .univ).prod .univ) (measurable_klDiv_kernel _ _) hX]
  have h_pre : (fun ω ↦ ((history O A Y t ω, O t ω), A t ω)) ⁻¹' ((s ×ˢ .univ) ×ˢ .univ) =
      history O A Y t ⁻¹' s := by
    ext; simp
  simp only [h_pre, Kernel.prodMkLeft_apply]

variable {S : Set (Σ n : ℕ, Hist Unit 𝓐 𝓨 n)}

/-- **Divergence decomposition at a stopping time.** Let `τ` be the hitting time of a measurable
stopping rule `S` by an algorithm run against a stationary environment with reward kernel `κ`, and
suppose that `τ` is almost surely finite. Then the relative entropy between the laws of the history
stopped by `S` under the reward kernels `κ` and `κ'` is at most
`∑ a, E_κ[N_a(τ)] KL(κ a ‖ κ' a)`, where `N_a(τ)` is the number of pulls of `a` before `τ`. -/
theorem klDiv_stoppedHistMeasure_le (hS : MeasurableSet S)
    (hτ : ∀ᵐ ω ∂(trajMeasure alg (Environment.bandit κ)),
      hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0 ω ≠ ⊤) :
    klDiv (stoppedHistMeasure alg (Environment.bandit κ) S)
        (stoppedHistMeasure alg (Environment.bandit κ') S) ≤
      ∑ a, (∫⁻ ω, (pullCount IT.action a
          (ENat.toNat (hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0 ω)) ω :
            ℝ≥0∞) ∂(trajMeasure alg (Environment.bandit κ))) * klDiv (κ a) (κ' a) := by
  have h := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit κ)
  have hτm := measurable_hittingAfter_sigmaHistory (𝓞 := Unit) (𝓐 := 𝓐) (𝓨 := 𝓨)
    IT.measurable_obs IT.measurable_action IT.measurable_feedback hS
  have hf (t : ℕ) : Measurable fun ω : ℕ → Round Unit 𝓐 𝓨 ↦
      klDiv (κ (IT.action t ω)) (κ' (IT.action t ω)) :=
    (measurable_klDiv_kernel κ κ').comp (IT.measurable_action t)
  refine (klDiv_stoppedHistMeasure_le_tsum hS).trans_eq
    (((tsum_congr fun t ↦ h.klDiv_restrict_compProd_stepKernel_bandit (κ' := κ')
      (measurableSet_notStoppedSet hS t)).trans
        (tsum_setLIntegral_notStoppedSet IT.measurable_obs IT.measurable_action
          IT.measurable_feedback hS hτ hf)).trans ?_)
  exact (LMLExplore.sum_lintegral_pullCount_mul IT.measurable_action
    (Measurable.of_discrete.comp hτm) fun a ↦ klDiv (κ a) (κ' a)).symm

end StoppingTime

end Learning
