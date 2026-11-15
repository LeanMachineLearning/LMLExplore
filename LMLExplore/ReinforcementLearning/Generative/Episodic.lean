/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Episodic.Optimal
public import LMLExplore.Probability.Kernel.Empirical
import LMLExplore.Analysis.SpecialFunctions.Log.Basic
import LMLExplore.MeasureTheory.MeasurableSpace.Constructions
import LMLExplore.SequentialLearning.SumRewards

/-!
# The generative model of an episodic MDP and the empirical episodic MDP

A generative model of an episodic MDP `M` with horizon `H` draws, for every step `h < H` and
every state-action pair `p`, independent next states with law `M.trans h p`. It is LML's stream
model `Bandits.streamMeasure (M.generativeKernel H)` on arrays `ω : ℕ → Fin H × (𝓢 × 𝓐) → 𝓢`,
with the keys `(h, p)`: the entry `ω i (h, p)` is the `i`-th sample from `M.trans h p`, and `N`
samples per step and pair use the entries `i < N`. The sample sequences of distinct keys are
mutually independent (`LMLExplore.iIndepFun_arm_streamMeasure`).

The empirical episodic MDP `M.empirical H N ω` has, at every step `h < H`, the empirical kernel
of the samples of the step `h` as transition kernel, and the rewards of `M`.

Model-based planning computes the optimal values `V̂*_h` and the greedy optimal policy `π̂*_h` of
the empirical MDP by backward induction from the horizon, so that these only depend on the
samples of the steps `h, …, H - 1` (`optValue_congr`, `value_optPolicy_congr`). Every function of
the empirical MDP that only depends on its transitions after the step `h` is therefore
independent of the samples of the step `h`, and Bernstein's inequality applies to the one-step
prediction errors `∫ V dP_h p - ∫ V dP̂_h p` of such functions `V`: for instance `V̂*_{h+1}`, or
the value `V^{π̂*}_{h+1}` in `M` of the greedy optimal policy of the empirical MDP. This is the
decoupling behind the analysis of model-based planning in finite-horizon MDPs [LWCGC24, §7.3],
whose Bernstein condition (66) concerns value sequences of the optimal policy of `M` and of the
greedy optimal policy of the empirical MDP: with probability at least `1 - δ`, for finitely many
such families `V_j`, every step `h < H` and every pair `p`,

`|∫ V_j dP_h p - ∫ V_j dP̂_h p| < √(2 Var_{P_h p}(V_j) L / N) + (u - l) L / (3 N)`,

with `L = log (2 J H S A / δ)` for `J` families with values in `[l, u]`.

## Main definitions

* `Learning.MDP.Episodic.EpisodicMDP.generativeKernel M H`: the kernel of the generative model,
  on the keys `Fin H × (𝓢 × 𝓐)`.
* `Learning.MDP.Episodic.EpisodicMDP.empirical M H N ω`: the empirical episodic MDP of the first
  `N` samples per step and pair of `ω`.

## Main statements

* `Learning.MDP.Episodic.EpisodicMDP.measurable_comp_empirical`: for finite state and action
  spaces, every function of the empirical MDP is a measurable function of the samples.
* `Learning.MDP.Episodic.EpisodicMDP.indepFun_comp_empirical`: every function of the empirical
  MDP that only depends on its transitions after the step `k` is independent of the samples of
  the step `k`.
* `measureReal_sqrt_variance_add_le_abs_integral_sub_integral_empirical_trans_le` (in
  `Learning.MDP.Episodic.EpisodicMDP`): Bernstein's inequality at a step `k` for these functions.
* `le_streamMeasure_forall_abs_integral_sub_integral_empirical_trans_lt` (in
  `Learning.MDP.Episodic.EpisodicMDP`): its uniform form over finitely many families, the steps
  and the pairs.

## References

* [G. Li, Y. Wei, Y. Chi, Y. Gu and Y. Chen, *Breaking the sample size barrier in model-based
  reinforcement learning with a generative model*, Operations Research, 2024][LWCGC24], §4.1 and
  §7.3 (arXiv:2005.12900)
-/

public section

open MeasureTheory ProbabilityTheory LMLExplore Learning Bandits
open Real (log exp)

namespace Learning.MDP.Episodic.EpisodicMDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}

/-! ### The generative model -/

/-- The kernel of the generative model of `M` up to the horizon `H`: it maps a key `(h, p)` of a
step `h < H` and a state-action pair `p` to the law `M.trans h p` of the next state. -/
noncomputable def generativeKernel (M : EpisodicMDP 𝓢 𝓐) (H : ℕ) :
    Kernel (Fin H × (𝓢 × 𝓐)) 𝓢 :=
  ⟨fun k ↦ M.trans k.1 k.2, measurable_from_prod_countable_right fun h ↦ (M.trans h).measurable⟩

@[simp]
lemma generativeKernel_apply (M : EpisodicMDP 𝓢 𝓐) (H : ℕ) (h : Fin H) (p : 𝓢 × 𝓐) :
    M.generativeKernel H (h, p) = M.trans h p :=
  (rfl)

instance (M : EpisodicMDP 𝓢 𝓐) (H : ℕ) : IsMarkovKernel (M.generativeKernel H) :=
  ⟨fun k ↦ by rw [← Prod.mk.eta (p := k), generativeKernel_apply]; infer_instance⟩

/-! ### The empirical episodic MDP -/

section Countable

variable [Countable 𝓢] [Countable 𝓐] [MeasurableSingletonClass 𝓢] [MeasurableSingletonClass 𝓐]

/-- The empirical episodic MDP of an array `ω : ℕ → Fin H × (𝓢 × 𝓐) → 𝓢` of samples of next
states, for `N ≠ 0`: at a step `h < H`, its transition kernel maps a pair `p` to the empirical law
of the first `N` samples `ω i (h, p)`, `i < N`; its rewards, and its transitions from the horizon
on, are those of `M`. Under the generative model `Bandits.streamMeasure (M.generativeKernel H)`,
it is the model of `M` estimated from `N` samples per step and state-action pair. -/
noncomputable def empirical (M : EpisodicMDP 𝓢 𝓐) (H N : ℕ) [NeZero N]
    (ω : ℕ → Fin H × (𝓢 × 𝓐) → 𝓢) : EpisodicMDP 𝓢 𝓐 where
  trans h := if hh : h < H then
      (empiricalKernel N ω).comap (Prod.mk ⟨h, hh⟩) measurable_prodMk_left
    else M.trans h
  isMarkovKernel_trans h := by split_ifs <;> infer_instance
  reward := M.reward

variable (M : EpisodicMDP 𝓢 𝓐) {H N : ℕ} [NeZero N] (ω : ℕ → Fin H × (𝓢 × 𝓐) → 𝓢)

/-- Before the horizon, the transitions of the empirical MDP are the empirical laws of the
samples of the step. -/
lemma empirical_trans_apply_of_lt {h : ℕ} (hh : h < H) (p : 𝓢 × 𝓐) :
    (M.empirical H N ω).trans h p = empiricalKernel N ω (⟨h, hh⟩, p) := by
  simp [empirical, hh]

@[simp]
lemma empirical_trans_apply (h : Fin H) (p : 𝓢 × 𝓐) :
    (M.empirical H N ω).trans h p = empiricalKernel N ω (h, p) :=
  M.empirical_trans_apply_of_lt ω h.isLt p

/-- From the horizon on, the transitions of the empirical MDP are those of `M`. -/
lemma empirical_trans_of_le {h : ℕ} (hh : H ≤ h) : (M.empirical H N ω).trans h = M.trans h := by
  simp [empirical, not_lt.2 hh]

@[simp]
lemma empirical_reward : (M.empirical H N ω).reward = M.reward :=
  (rfl)

@[simp]
lemma meanReward_empirical : (M.empirical H N ω).meanReward = M.meanReward := by
  funext h s a
  rw [meanReward_def, meanReward_def, empirical_reward]

@[simp]
lemma rewardsIn_empirical {I : Set ℝ} : (M.empirical H N ω).RewardsIn I ↔ M.RewardsIn I := by
  rw [rewardsIn_def, rewardsIn_def, empirical_reward]

/-- The empirical MDP of the first `N` samples per step and pair only depends on these
samples. -/
lemma empirical_congr {ω ω' : ℕ → Fin H × (𝓢 × 𝓐) → 𝓢} (h : ∀ i < N, ω i = ω' i) :
    M.empirical H N ω = M.empirical H N ω' := by
  ext1
  · funext h'
    by_cases hh : h' < H
    · ext1 p
      rw [empirical_trans_apply_of_lt M ω hh, empirical_trans_apply_of_lt M ω' hh,
        empiricalKernel_congr h]
    · rw [empirical_trans_of_le M ω (not_lt.1 hh), empirical_trans_of_le M ω' (not_lt.1 hh)]
  · rw [empirical_reward, empirical_reward]

/-- For finite state and action spaces, every function of the empirical MDP is a measurable
function of the array of samples: the empirical MDP only depends on the finitely many samples
`ω i k`, `i < N`, which take finitely many values. -/
lemma measurable_comp_empirical [Finite 𝓢] [Finite 𝓐] (H N : ℕ) [NeZero N] {β : Type*}
    [MeasurableSpace β] (F : EpisodicMDP 𝓢 𝓐 → β) :
    Measurable fun ω ↦ F (M.empirical H N ω) :=
  DependsOn.measurable_of_countable (Set.finite_Iio N) fun _ _ h ↦ by
    rw [M.empirical_congr fun i hi ↦ h i hi]

end Countable

/-! ### Decoupling across steps -/

section Finite

variable [Finite 𝓢] [Finite 𝓐] [MeasurableSingletonClass 𝓢] [MeasurableSingletonClass 𝓐]

/-- **Decoupling across steps.** Under the generative model of `M`, every function `F` of the
empirical episodic MDP that only depends on its rewards and on its transitions after the step
`k` is independent of the samples `(ω i (k, p))_i` of every pair `p` at the step `k`. -/
theorem indepFun_comp_empirical (M : EpisodicMDP 𝓢 𝓐) (H N : ℕ) [NeZero N] {β : Type*}
    [MeasurableSpace β] (F : EpisodicMDP 𝓢 𝓐 → β) (k : Fin H)
    (hF : ∀ M₁ M₂ : EpisodicMDP 𝓢 𝓐, M₁.reward = M₂.reward →
      (∀ h, (k : ℕ) < h → M₁.trans h = M₂.trans h) → F M₁ = F M₂) (p : 𝓢 × 𝓐) :
    IndepFun (fun ω ↦ F (M.empirical H N ω)) (fun ω i ↦ ω i (k, p))
      (streamMeasure (M.generativeKernel H)) := by
  have : Countable 𝓢 := Finite.to_countable
  have : Countable 𝓐 := Finite.to_countable
  -- the function only depends on the samples of the keys of the steps after `k`
  refine indepFun_streamMeasure_of_forall_eq _ (T := {q | k < q.1})
    (M.measurable_comp_empirical H N F) (fun ω ω' hωω' ↦ hF _ _ rfl fun h hkh ↦ ?_)
    (lt_irrefl k)
  by_cases hh : h < H
  · ext1 q
    rw [empirical_trans_apply_of_lt M ω hh, empirical_trans_apply_of_lt M ω' hh]
    exact empiricalKernel_apply_congr fun i _ ↦ hωω' i _ hkh
  · rw [empirical_trans_of_le M ω (not_lt.1 hh), empirical_trans_of_le M ω' (not_lt.1 hh)]

/-- **Bernstein's inequality at a step of the empirical episodic MDP.** Under the generative
model of `M`, let `G M'` be a function on the states computed from an episodic MDP `M'`, that only
depends on its rewards and on its transitions after the step `k`, with values in `[l, u]`,
`l < u`, at the empirical MDPs. For `N ≠ 0`, every pair `p` and every `x`, the one-step
prediction error `|∫ V dP_k p - ∫ V dP̂_k p|` of `V = G (M.empirical H N ω)` is at least
`√(2 Var_{P_k p}(V) x / N) + (u - l) x / (3 N)` with probability at most `2 exp (-x)`. -/
theorem measureReal_sqrt_variance_add_le_abs_integral_sub_integral_empirical_trans_le
    (M : EpisodicMDP 𝓢 𝓐) (H N : ℕ) [NeZero N] (G : EpisodicMDP 𝓢 𝓐 → 𝓢 → ℝ) (k : Fin H)
    (hG : ∀ M₁ M₂ : EpisodicMDP 𝓢 𝓐, M₁.reward = M₂.reward →
      (∀ h, (k : ℕ) < h → M₁.trans h = M₂.trans h) → G M₁ = G M₂)
    {l u : ℝ} (hlu : l < u) (hGb : ∀ ω s, G (M.empirical H N ω) s ∈ Set.Icc l u) (p : 𝓢 × 𝓐)
    (x : ℝ) :
    (streamMeasure (M.generativeKernel H)).real {ω |
      √(2 * Var[G (M.empirical H N ω); M.trans k p] * x / N) + (u - l) * x / (3 * N) ≤
        |∫ s, G (M.empirical H N ω) s ∂(M.trans k p) -
          ∫ s, G (M.empirical H N ω) s ∂((M.empirical H N ω).trans k p)|} ≤
      2 * exp (-x) := by
  have : Countable 𝓢 := Finite.to_countable
  have : Countable 𝓐 := Finite.to_countable
  simpa only [generativeKernel_apply, empirical_trans_apply] using
    measureReal_sqrt_variance_add_le_abs_integral_sub_integral_empiricalKernel_le_of_indepFun
      (M.generativeKernel H) (M.measurable_comp_empirical H N G)
      (indepFun_comp_empirical M H N G k hG p) hlu hGb N x

end Finite

/-- **Uniform Bernstein bound at the steps of the empirical episodic MDP.** Under the generative
model of an episodic MDP `M` with horizon `H`, `S` states and `A` actions, let `G j h M'`, for `j`
in a finite type `ι` of cardinality `J` and every step `h`, be functions on the states computed
from an episodic MDP `M'`, such that `G j h M'` only depends on the rewards of `M'` and on its
transitions after the step `h`, with values in `[l, u]`, `l < u`, at the empirical MDPs. For
`N ≠ 0` and `δ > 0`, with probability at least `1 - δ`, for every `j`, every step `h < H` and
every pair `p`, the function `V = G j h (M.empirical H N ω)` satisfies
`|∫ V dP_h p - ∫ V dP̂_h p| < √(2 Var_{P_h p}(V) L / N) + (u - l) L / (3 N)` with
`L = log (2 J H S A / δ)`. -/
theorem le_streamMeasure_forall_abs_integral_sub_integral_empirical_trans_lt [Fintype 𝓢]
    [Fintype 𝓐] [MeasurableSingletonClass 𝓢] [MeasurableSingletonClass 𝓐] {ι : Type*} [Fintype ι]
    (M : EpisodicMDP 𝓢 𝓐) (H N : ℕ) [NeZero N] (G : ι → ℕ → EpisodicMDP 𝓢 𝓐 → 𝓢 → ℝ)
    (hG : ∀ j, ∀ h < H, ∀ M₁ M₂ : EpisodicMDP 𝓢 𝓐, M₁.reward = M₂.reward →
      (∀ h', h < h' → M₁.trans h' = M₂.trans h') → G j h M₁ = G j h M₂)
    {l u : ℝ} (hlu : l < u)
    (hGb : ∀ j, ∀ h < H, ∀ ω s, G j h (M.empirical H N ω) s ∈ Set.Icc l u)
    {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ (streamMeasure (M.generativeKernel H)).real {ω | ∀ j, ∀ h < H, ∀ p,
      |∫ s, G j h (M.empirical H N ω) s ∂(M.trans h p) -
          ∫ s, G j h (M.empirical H N ω) s ∂((M.empirical H N ω).trans h p)| <
        √(2 * Var[G j h (M.empirical H N ω); M.trans h p] *
            log (2 * Fintype.card ι * H * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) / N) +
          (u - l) * log (2 * Fintype.card ι * H * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) /
            (3 * N)} := by
  set L := log (2 * Fintype.card ι * H * Fintype.card 𝓢 * Fintype.card 𝓐 / δ)
  -- the bad event of a family, a step and a pair has probability at most `δ / (J H S A)`
  set bad : ι × Fin H × (𝓢 × 𝓐) → Set (ℕ → Fin H × (𝓢 × 𝓐) → 𝓢) := fun i ↦ {ω |
    √(2 * Var[G i.1 i.2.1 (M.empirical H N ω); M.trans i.2.1 i.2.2] * L / N) +
        (u - l) * L / (3 * N) ≤
      |∫ s, G i.1 i.2.1 (M.empirical H N ω) s ∂(M.trans i.2.1 i.2.2) -
        ∫ s, G i.1 i.2.1 (M.empirical H N ω) s ∂((M.empirical H N ω).trans i.2.1 i.2.2)|}
  have h_bad (i : ι × Fin H × (𝓢 × 𝓐)) :
      (streamMeasure (M.generativeKernel H)).real (bad i) ≤
        δ / Fintype.card (ι × Fin H × (𝓢 × 𝓐)) := by
    refine (measureReal_sqrt_variance_add_le_abs_integral_sub_integral_empirical_trans_le M H N
      (G i.1 i.2.1) i.2.1 (hG i.1 i.2.1 i.2.1.isLt) hlu (hGb i.1 i.2.1 i.2.1.isLt) i.2.2
      L).trans ?_
    refine Real.mul_exp_neg_log_div_le two_pos
      (by exact_mod_cast Fintype.card_pos_iff.2 ⟨i⟩) hδ (le_of_eq ?_)
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    ring
  -- a union bound over the families, the steps and the pairs
  refine (one_sub_le_measureReal_compl_iUnion hδ.le h_bad).trans
    (measureReal_mono (fun ω hω j h hh p ↦ ?_) (measure_ne_top _ _))
  have h : ω ∉ bad (j, ⟨h, hh⟩, p) := fun h ↦ hω (Set.mem_iUnion.2 ⟨_, h⟩)
  simpa only [bad, Set.mem_ofPred_eq, not_le] using h

end Learning.MDP.Episodic.EpisodicMDP
