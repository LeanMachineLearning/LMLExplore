/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.SequentialLearning.EmpiricalLaw

import LMLExplore.SequentialLearning.Algorithm

/-!
# Counts and empirical transition kernels of Markov decision processes

A learner interacting with a tabular MDP estimates its transition kernel from the transitions it
has observed: the empirical kernel `P̂(s, a)` is the empirical law of the next states observed
after the visits of the state-action pair `(s, a)`, and the uniform law on the state space when
`(s, a)` has not been visited (`LMLExplore.empiricalLaw`). For a finite nonempty state space it is
a Markov kernel, and it is measurable with respect to the information available to the learner.

**Runs of a stationary MDP.** Along a run with states `O n` and actions `A n` (in `M.env μ`), the
visits of `p = (s, a)` before round `t` are counted by LML's `pullCount` of the state-action process
`n ↦ (O n, A n)`, and the transitions `p → s'` by the `pullCount` of `((s, a), s')` for the
process `n ↦ ((O n, A n), O (n + 1))`. The empirical kernel at round `t` is `MDP.empTrans O A t ω`:
it gives `s'` the proportion `N_t(s, a, s') / N_t(s, a)` (`MDP.measureReal_empTrans_singleton`)
and it only depends on the rounds before `t` and on the state of round `t`, so that it is
measurable with respect to the past `h.filtrationObs t` of round `t`
(`MDP.measurable_empTrans_filtrationObs`): the algorithm can use it at round `t`. The empirical
mean reward of `(s, a)` is LML's `empMean` of the rewards at the visits of `(s, a)`, `0` when the
count is zero; it is the mean of the empirical law of these rewards
(`LMLExplore.empMean_eq_integral_empiricalLaw`).

**Episodes as rounds.** When every round of the interaction is an episode of horizon `H`, played
with a deterministic `H`-step policy `π : Fin H → S → A` along the state sequence
`τ : Fin (H + 1) → S`, the step `h` of the episode visits the pair `MDP.Episodic.stepPair π τ h =
(τ h, π h (τ h))` and observes the next state `τ (h + 1)`. For processes `π i` of policies and
`τ i` of state sequences, the episodic counts before episode `k` are the `pullCount`s
`N^k_h(s, a) = #{i < k | (S^i_h, A^i_h) = (s, a)}` of the processes
`i ↦ stepPair (π i) (τ i) h`, and their sums over the steps are the pooled counts
`N^k(s, a) = ∑_h N^k_h(s, a)` (`LMLExplore.card_filter_range_product_eq_sum_pullCount`). The
empirical kernel of the step `h` is `MDP.Episodic.stepEmpTrans π τ h k ω` and, for stationary
transitions, the empirical kernel pooled over the steps is `MDP.Episodic.pooledEmpTrans π τ k ω`.
Along a run whose actions are the policies and whose feedbacks are the state sequences, both are
measurable with respect to the past of episode `k`.

The episodic and pooled counts follow the empirical models of the formalization of [EV26] in
Essakine2026Tight (`github.com/RemyDegenne/Essakine2026Tight`, files
`Essakine2026Tight/ForLMLExplore/ReinforcementLearning/Episodic/Empirical.lean` and
`Essakine2026Tight/ForLMLExplore/ReinforcementLearning/Episodic/EmpiricalCounts.lean`, by Rémy
Degenne, Apache 2.0), restated through LML's `pullCount` and empirical laws.

## Main definitions

* `Learning.MDP.empTrans O A t ω`: the empirical transition kernel of a run before round `t`.
* `Learning.MDP.Episodic.stepPair π τ h`: the state-action pair of the step `h` of an episode.
* `Learning.MDP.Episodic.stepEmpTrans π τ h k ω`: the empirical transition kernel of the step `h`
  before episode `k`.
* `Learning.MDP.Episodic.pooledEmpTrans π τ k ω`: the empirical transition kernel pooled over the
  steps, before episode `k`.

## Main statements

* `Learning.MDP.measureReal_empTrans_singleton`,
  `Learning.MDP.Episodic.measureReal_stepEmpTrans_singleton`,
  `Learning.MDP.Episodic.measureReal_pooledEmpTrans_singleton`: the empirical kernels as ratios of
  transition counts to visit counts.
* `Learning.MDP.measurable_empTrans_filtrationObs`,
  `Learning.MDP.Episodic.measurable_stepEmpTrans_filtrationObs`,
  `Learning.MDP.Episodic.measurable_pooledEmpTrans_filtrationObs`: the empirical kernels are
  measurable in the history.

## References

* [EV26] A. Essakine and C. Vernade, *Tight sample complexity bounds for entropic best policy
  identification*, COLT 2026, arXiv:2605.13717.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning LMLExplore

namespace Learning.MDP

variable {𝓢 𝓐 𝓨 Ω : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {mΩ : MeasurableSpace Ω}

/-! ### Runs of a stationary MDP -/

section Run

variable [Countable 𝓢] [Countable 𝓐] [MeasurableSingletonClass 𝓢] [MeasurableSingletonClass 𝓐]
  [DecidableEq 𝓢] [DecidableEq 𝓐] {O : ℕ → Ω → 𝓢} {A : ℕ → Ω → 𝓐} {t : ℕ} {ω : Ω} {p : 𝓢 × 𝓐}

/-- The empirical transition kernel before round `t` of a run with states `O` and actions `A`: it
maps a state-action pair `p` to the empirical law of the next states `O (n + 1)` observed at the
rounds `n < t` with `(O n, A n) = p`, and to the uniform law if there is no such round. -/
noncomputable def empTrans (O : ℕ → Ω → 𝓢) (A : ℕ → Ω → 𝓐) (t : ℕ) (ω : Ω) :
    Kernel (𝓢 × 𝓐) 𝓢 :=
  empiricalLawKernel (range t) (fun n ↦ (O n ω, A n ω)) (fun n ↦ O (n + 1) ω)

lemma empTrans_apply (O : ℕ → Ω → 𝓢) (A : ℕ → Ω → 𝓐) (t : ℕ) (ω : Ω) (p : 𝓢 × 𝓐) :
    empTrans O A t ω p = empiricalLaw (range t) (fun n ↦ (O n ω, A n ω)) (fun n ↦ O (n + 1) ω) p :=
  empiricalLawKernel_apply _ _ _ p

instance [Finite 𝓢] [Nonempty 𝓢] : IsMarkovKernel (empTrans O A t ω) :=
  isMarkovKernel_empiricalLawKernel

/-- The empirical kernel of an unvisited state-action pair is the uniform law. -/
lemma empTrans_of_pullCount_eq_zero (h : pullCount (fun n ω ↦ (O n ω, A n ω)) p t ω = 0) :
    empTrans O A t ω p = uniformOn Set.univ :=
  (empTrans_apply O A t ω p).trans (empiricalLaw_of_card_eq_zero h)

/-- **Empirical transition probabilities.** The empirical kernel of a visited pair `(s, a)` gives
the state `s'` the proportion `N_t(s, a, s') / N_t(s, a)` of the visits of `(s, a)` before round `t`
that were followed by `s'`. -/
lemma measureReal_empTrans_singleton (h : pullCount (fun n ω ↦ (O n ω, A n ω)) p t ω ≠ 0)
    (s' : 𝓢) :
    (empTrans O A t ω p).real {s'} =
      (pullCount (fun n ω ↦ ((O n ω, A n ω), O (n + 1) ω)) (p, s') t ω : ℝ) /
        pullCount (fun n ω ↦ (O n ω, A n ω)) p t ω := by
  rw [empTrans_apply, measureReal_empiricalLaw_singleton h]
  simp only [pullCount, Prod.mk.injEq]

/-- **Measurability in the history.** Along a run of an algorithm, the empirical kernel before
round `t` is measurable with respect to the past `h.filtrationObs t` of round `t`: the history of
the rounds before `t` and the state of round `t`. -/
lemma measurable_empTrans_filtrationObs {alg : Algorithm 𝓢 𝓐 𝓨} {env : Environment 𝓢 𝓐 𝓨}
    {P : Measure Ω} {Y : ℕ → Ω → 𝓨} (h : IsAlgEnvSeq O A Y alg env P) (t : ℕ) (p : 𝓢 × 𝓐) :
    Measurable[h.filtrationObs t] fun ω ↦ empTrans O A t ω p := by
  simp_rw [empTrans_apply]
  refine measurable_empiricalLaw (fun n hn ↦ ?_) (fun n hn ↦ ?_) p
  · have hnt : n < t := mem_range.1 hn
    exact (h.adapted_obs_filtrationObs.measurable_le hnt.le).prodMk
      (h.measurable_action_filtrationObs_of_lt hnt)
  · exact h.adapted_obs_filtrationObs.measurable_le (mem_range.1 hn)

end Run

/-! ### Episodes as rounds -/

namespace Episodic

variable {H : ℕ}

/-- The state-action pair `(s_h, π_h(s_h))` visited at the step `h` of an episode played with the
deterministic `H`-step policy `π` along the state sequence `τ = (s_0, …, s_H)`. -/
def stepPair (π : Fin H → 𝓢 → 𝓐) (τ : Fin (H + 1) → 𝓢) (h : Fin H) : 𝓢 × 𝓐 :=
  (τ h.castSucc, π h (τ h.castSucc))

lemma stepPair_def (π : Fin H → 𝓢 → 𝓐) (τ : Fin (H + 1) → 𝓢) (h : Fin H) :
    stepPair π τ h = (τ h.castSucc, π h (τ h.castSucc)) :=
  (rfl)

@[simp]
lemma fst_stepPair (π : Fin H → 𝓢 → 𝓐) (τ : Fin (H + 1) → 𝓢) (h : Fin H) :
    (stepPair π τ h).1 = τ h.castSucc :=
  (rfl)

@[simp]
lemma snd_stepPair (π : Fin H → 𝓢 → 𝓐) (τ : Fin (H + 1) → 𝓢) (h : Fin H) :
    (stepPair π τ h).2 = π h (τ h.castSucc) :=
  (rfl)

variable [Countable 𝓢] [MeasurableSingletonClass 𝓢]

/-- The state-action pair of a step is a measurable function of the policy and of the state
sequence. -/
lemma measurable_stepPair (h : Fin H) :
    Measurable fun q : (Fin H → 𝓢 → 𝓐) × (Fin (H + 1) → 𝓢) ↦ stepPair q.1 q.2 h := by
  have h_eval : Measurable fun q : (Fin H → 𝓢 → 𝓐) × 𝓢 ↦ q.1 h q.2 :=
    measurable_from_prod_countable_left fun s ↦
      (measurable_pi_apply s).comp (measurable_pi_apply h)
  have h_state : Measurable fun q : (Fin H → 𝓢 → 𝓐) × (Fin (H + 1) → 𝓢) ↦ q.2 h.castSucc :=
    (measurable_pi_apply _).comp measurable_snd
  exact h_state.prodMk (h_eval.comp (measurable_fst.prodMk h_state))

variable [Countable 𝓐] [MeasurableSingletonClass 𝓐] [DecidableEq 𝓢] [DecidableEq 𝓐]
  {π : ℕ → Ω → Fin H → 𝓢 → 𝓐} {τ : ℕ → Ω → Fin (H + 1) → 𝓢} {k : ℕ} {ω : Ω} {p : 𝓢 × 𝓐}

/-- The empirical transition kernel of the step `h` before episode `k`, for the policies `π i` and
the state sequences `τ i` of the episodes `i`: it maps a state-action pair `p` to the empirical law
of the states `τ i (h + 1)` of the episodes `i < k` that visit `p` at the step `h`, and to the
uniform law if there is no such episode. -/
noncomputable def stepEmpTrans (π : ℕ → Ω → Fin H → 𝓢 → 𝓐) (τ : ℕ → Ω → Fin (H + 1) → 𝓢)
    (h : Fin H) (k : ℕ) (ω : Ω) : Kernel (𝓢 × 𝓐) 𝓢 :=
  empiricalLawKernel (range k) (fun i ↦ stepPair (π i ω) (τ i ω) h) (fun i ↦ τ i ω h.succ)

lemma stepEmpTrans_apply (π : ℕ → Ω → Fin H → 𝓢 → 𝓐) (τ : ℕ → Ω → Fin (H + 1) → 𝓢)
    (h : Fin H) (k : ℕ) (ω : Ω) (p : 𝓢 × 𝓐) :
    stepEmpTrans π τ h k ω p =
      empiricalLaw (range k) (fun i ↦ stepPair (π i ω) (τ i ω) h) (fun i ↦ τ i ω h.succ) p :=
  empiricalLawKernel_apply _ _ _ p

instance [Finite 𝓢] [Nonempty 𝓢] (h : Fin H) : IsMarkovKernel (stepEmpTrans π τ h k ω) :=
  isMarkovKernel_empiricalLawKernel

/-- The empirical kernel of the step `h` at a pair that no episode visits at the step `h` is the
uniform law. -/
lemma stepEmpTrans_of_pullCount_eq_zero {h : Fin H}
    (hN : pullCount (fun i ω ↦ stepPair (π i ω) (τ i ω) h) p k ω = 0) :
    stepEmpTrans π τ h k ω p = uniformOn Set.univ :=
  (stepEmpTrans_apply π τ h k ω p).trans (empiricalLaw_of_card_eq_zero hN)

/-- The empirical kernel of the step `h` gives the state `s'` the proportion
`N^k_h(s, a, s') / N^k_h(s, a)` of the episodes visiting `(s, a)` at the step `h` before episode `k`
that move to `s'`. -/
lemma measureReal_stepEmpTrans_singleton {h : Fin H}
    (hN : pullCount (fun i ω ↦ stepPair (π i ω) (τ i ω) h) p k ω ≠ 0) (s' : 𝓢) :
    (stepEmpTrans π τ h k ω p).real {s'} =
      (pullCount (fun i ω ↦ (stepPair (π i ω) (τ i ω) h, τ i ω h.succ)) (p, s') k ω : ℝ) /
        pullCount (fun i ω ↦ stepPair (π i ω) (τ i ω) h) p k ω := by
  rw [stepEmpTrans_apply, measureReal_empiricalLaw_singleton hN]
  simp only [pullCount, Prod.mk.injEq]

/-- The empirical transition kernel pooled over the steps before episode `k`, for an MDP with
stationary transitions: it maps a state-action pair `p` to the empirical law of the next states
observed at all the visits of `p`, at every step `h` of every episode `i < k`, and to the uniform
law if there is no such visit. -/
noncomputable def pooledEmpTrans (π : ℕ → Ω → Fin H → 𝓢 → 𝓐) (τ : ℕ → Ω → Fin (H + 1) → 𝓢)
    (k : ℕ) (ω : Ω) : Kernel (𝓢 × 𝓐) 𝓢 :=
  empiricalLawKernel (range k ×ˢ univ) (fun q : ℕ × Fin H ↦ stepPair (π q.1 ω) (τ q.1 ω) q.2)
    (fun q ↦ τ q.1 ω q.2.succ)

lemma pooledEmpTrans_apply (π : ℕ → Ω → Fin H → 𝓢 → 𝓐) (τ : ℕ → Ω → Fin (H + 1) → 𝓢)
    (k : ℕ) (ω : Ω) (p : 𝓢 × 𝓐) :
    pooledEmpTrans π τ k ω p =
      empiricalLaw (range k ×ˢ univ) (fun q : ℕ × Fin H ↦ stepPair (π q.1 ω) (τ q.1 ω) q.2)
        (fun q ↦ τ q.1 ω q.2.succ) p :=
  empiricalLawKernel_apply _ _ _ p

instance [Finite 𝓢] [Nonempty 𝓢] : IsMarkovKernel (pooledEmpTrans π τ k ω) :=
  isMarkovKernel_empiricalLawKernel

/-- The pooled empirical kernel at a pair that no step of an episode visits is the uniform
law. -/
lemma pooledEmpTrans_of_sum_pullCount_eq_zero
    (hN : ∑ h, pullCount (fun i ω ↦ stepPair (π i ω) (τ i ω) h) p k ω = 0) :
    pooledEmpTrans π τ k ω p = uniformOn Set.univ :=
  (pooledEmpTrans_apply π τ k ω p).trans <| empiricalLaw_of_card_eq_zero <|
    (card_filter_range_product_eq_sum_pullCount
      (fun i ω h ↦ stepPair (π i ω) (τ i ω) h) p k ω).trans hN

/-- The pooled empirical kernel gives the state `s'` the proportion
`∑_h N^k_h(s, a, s') / ∑_h N^k_h(s, a)` of the visits of `(s, a)`, at all the steps of the episodes
before `k`, that are followed by `s'`. -/
lemma measureReal_pooledEmpTrans_singleton
    (hN : ∑ h, pullCount (fun i ω ↦ stepPair (π i ω) (τ i ω) h) p k ω ≠ 0) (s' : 𝓢) :
    (pooledEmpTrans π τ k ω p).real {s'} =
      (∑ h, pullCount (fun i ω ↦ (stepPair (π i ω) (τ i ω) h, τ i ω h.succ)) (p, s') k ω : ℝ) /
        ∑ h, pullCount (fun i ω ↦ stepPair (π i ω) (τ i ω) h) p k ω := by
  have hcard := card_filter_range_product_eq_sum_pullCount
    (fun i ω h ↦ stepPair (π i ω) (τ i ω) h) p k ω
  have hcard' : #{q ∈ range k ×ˢ univ |
      stepPair (π q.1 ω) (τ q.1 ω) q.2 = p ∧ τ q.1 ω q.2.succ = s'} =
      ∑ h, pullCount (fun i ω ↦ (stepPair (π i ω) (τ i ω) h, τ i ω h.succ)) (p, s') k ω := by
    rw [← card_filter_range_product_eq_sum_pullCount
      (fun i ω h ↦ (stepPair (π i ω) (τ i ω) h, τ i ω h.succ)) (p, s') k ω]
    simp_rw [Prod.mk.injEq]
  rw [pooledEmpTrans_apply, measureReal_empiricalLaw_singleton (hcard.trans_ne hN), hcard, hcard',
    Nat.cast_sum]

section Measurability

variable {𝓞 : Type*} {m𝓞 : MeasurableSpace 𝓞}
  {alg : Algorithm 𝓞 (Fin H → 𝓢 → 𝓐) (Fin (H + 1) → 𝓢)}
  {env : Environment 𝓞 (Fin H → 𝓢 → 𝓐) (Fin (H + 1) → 𝓢)} {P : Measure Ω} {O : ℕ → Ω → 𝓞}

omit [Countable 𝓐] [MeasurableSingletonClass 𝓐] [DecidableEq 𝓢] [DecidableEq 𝓐] in
/-- Along a run whose actions are the policies and whose feedbacks are the state sequences of the
episodes, the state-action pair of the step `h` of an episode `i < k` is measurable with respect
to the past `hr.filtrationObs k` of episode `k`. In particular, so are the episodic counts
`pullCount (fun i ω ↦ stepPair (π i ω) (τ i ω) h) p k` before episode `k`. -/
lemma measurable_stepPair_filtrationObs_of_lt (hr : IsAlgEnvSeq O π τ alg env P)
    {i k : ℕ} (hik : i < k) (h : Fin H) :
    Measurable[hr.filtrationObs k] fun ω ↦ stepPair (π i ω) (τ i ω) h :=
  (measurable_stepPair h).comp ((hr.measurable_action_filtrationObs_of_lt hik).prodMk
    (hr.measurable_feedback_filtrationObs_of_lt hik))

/-- **Measurability in the history.** Along a run whose actions are the policies and whose
feedbacks are the state sequences of the episodes, the empirical kernel of the step `h` before
episode `k` is measurable with respect to the past `hr.filtrationObs k` of episode `k`. -/
lemma measurable_stepEmpTrans_filtrationObs (hr : IsAlgEnvSeq O π τ alg env P) (h : Fin H)
    (k : ℕ) (p : 𝓢 × 𝓐) :
    Measurable[hr.filtrationObs k] fun ω ↦ stepEmpTrans π τ h k ω p := by
  simp_rw [stepEmpTrans_apply]
  exact measurable_empiricalLaw
    (fun i hi ↦ measurable_stepPair_filtrationObs_of_lt hr (mem_range.1 hi) h)
    (fun i hi ↦ (measurable_pi_apply _).comp
      (hr.measurable_feedback_filtrationObs_of_lt (mem_range.1 hi))) p

/-- **Measurability in the history.** Along a run whose actions are the policies and whose
feedbacks are the state sequences of the episodes, the pooled empirical kernel before episode `k`
is measurable with respect to the past `hr.filtrationObs k` of episode `k`. -/
lemma measurable_pooledEmpTrans_filtrationObs (hr : IsAlgEnvSeq O π τ alg env P) (k : ℕ)
    (p : 𝓢 × 𝓐) :
    Measurable[hr.filtrationObs k] fun ω ↦ pooledEmpTrans π τ k ω p := by
  simp_rw [pooledEmpTrans_apply]
  exact measurable_empiricalLaw
    (fun q hq ↦ measurable_stepPair_filtrationObs_of_lt hr
      (mem_range.1 (mem_product.1 hq).1) q.2)
    (fun q hq ↦ (measurable_pi_apply q.2.succ).comp
      (hr.measurable_feedback_filtrationObs_of_lt (mem_range.1 (mem_product.1 hq).1))) p

end Measurability

end Episodic

end Learning.MDP
