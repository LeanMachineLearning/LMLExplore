/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
public import LMLExplore.MarkovDecisionProcess.Optimality
public import LMLExplore.SequentialLearning.DivergenceDecomposition

/-!
# A lower bound for planning with a generative model

Azar, Munos and Kappen [AMK13] prove that estimating the optimal action values of a discounted MDP
to accuracy `ε` with probability `1 - δ` from a generative model needs of the order of
`N log (N / δ) / ((1 - γ)³ ε²)` samples, where `N` is the number of state-action pairs of their
hard MDPs. This file proves this lower bound for every algorithm that queries the generative model
adaptively, with `N` the number `K A` of hard pairs: with one action set for all the states, the
hard MDPs have `S = K (1 + 2 A)` states.

The hard MDPs have `K` start states `start x`, each with `A` actions, and `2 K A` states whose
actions all behave alike: the action `a` leads from `start x` to the self-loop state
`loop (x, a)`, which has reward `1`, stays put with probability `θ (x, a)` and otherwise moves to
the absorbing state `sink (x, a)` with reward `0`. The optimal action value at `(start x, a)` is
`γ / (1 - γ θ (x, a))`, so that it is very sensitive to `θ (x, a)` when `θ (x, a)` is close to `1`.

[AMK13] compares two MDPs with a common self-loop probability, `p` or `p + α`, at all the pairs.
The samples at the different pairs then carry information about one another, and the
independence claim of its proof fails. We use the product family instead: the self-loop
probability at each pair is chosen independently in `{p, p + α}`. An algorithm querying the
generative model is a run of an algorithm against the stationary environment
`Environment.bandit M.P` whose actions are the state-action pairs and whose feedback is the next
state. The change of measure, `Learning.IsAlgEnvSeq.klDiv_map_history_eq_sum_pullCount` with the
data processing inequality `LMLExplore.klBer_measureReal_le_klDiv`, shows that an estimate
which separates `p` from `p + α` at the pair `(x, a)` with probability `1 - δ` needs
`log (1 / (2.4 δ)) / d(p, p + α)` expected queries of the state `loop (x, a)`. With
`p = (4γ - 1) / (3γ)` and `α = 2 (1 - γ p)² ε / γ²`, the separation is more than `2 ε` and
`d(p, p + α) ≤ 2400 (1 - γ)³ ε²`. Summing over the `K A` pairs gives the bound.

## Main definitions

* `LMLExplore.ReinforcementLearning.SelfLoopState 𝓚 𝓐`: the states of the hard MDPs.
* `LMLExplore.ReinforcementLearning.selfLoopMDP θ`: the hard MDP with self-loop probabilities `θ`.

## Main statements

* `LMLExplore.ReinforcementLearning.card_selfLoopState`: there are `S = K (1 + 2 A)` states.
* `LMLExplore.ReinforcementLearning.optQValue_selfLoopMDP_start`: the optimal action values
  `Q* (start x, a) = γ / (1 - γ θ (x, a))`.
* `LMLExplore.ReinforcementLearning.klDiv_map_history_eq_sum_lintegral_pullCount_mul_klBer`: the
  divergence decomposition for two self-loop MDPs that differ at one pair.
* `LMLExplore.ReinforcementLearning.ofReal_log_le_sum_lintegral_pullCount_mul_klBer`: the change
  of measure at one pair.
* `LMLExplore.ReinforcementLearning.ofReal_log_le_sum_lintegral_pullCount_mul_klBer_of_two_mul_lt`:
  the two-point lower bound at one pair, for estimates of optimal action values more than `2 ε`
  apart.
* `LMLExplore.ReinforcementLearning.card_mul_card_mul_log_le_of_forall_abs_sub_optQValue_le`:
  the lower bound with explicit constants, `K A log (1 / (2.4 δ)) ≤ 2400 (1 - γ)³ ε² T`.
* `LMLExplore.ReinforcementLearning.exists_const_le_of_forall_abs_sub_optQValue_le`: the lower
  bound [AMK13, Theorem 3], corrected: `T ≥ K A log (K A / (C δ)) / (C (1 - γ)³ ε²)` for
  `γ ≥ 2 / 5`, `ε ≤ ε₀` and `δ < δ₀ / (K A)`.

## References

* [M. G. Azar, R. Munos and H. J. Kappen, *Minimax PAC bounds on the sample complexity of
  reinforcement learning with a generative model*, Machine Learning 91 (2013)][AMK13],
  Theorem 3; Theorem 2 in the conference version, *On the sample complexity of reinforcement
  learning with a generative model*, ICML 2012, arXiv:1206.6461
* [E. Kaufmann, O. Cappé and A. Garivier, *On the complexity of best-arm identification in
  multi-armed bandit models*, JMLR 17 (2016)][KCG16], Lemma 1, for the change of measure
-/

public section

universe u v

open MeasureTheory ProbabilityTheory InformationTheory Learning
open scoped ENNReal NNReal unitInterval

namespace LMLExplore.ReinforcementLearning

/-- The states of the self-loop MDPs with start states in `𝓚` and actions in `𝓐`: the start
states, and for each pair `z` of a start state and an action, a self-loop state and a sink. -/
inductive SelfLoopState (𝓚 𝓐 : Type*) where
  /-- A start state `x`. -/
  | start (x : 𝓚)
  /-- The rewarding self-loop state reached by the action `a` from the start state `x`. -/
  | loop (z : 𝓚 × 𝓐)
  /-- The absorbing state left by the self-loop state `loop z`. -/
  | sink (z : 𝓚 × 𝓐)
  deriving DecidableEq, Fintype

namespace SelfLoopState

variable {𝓚 𝓐 : Type*}

instance [Nonempty 𝓚] : Nonempty (SelfLoopState 𝓚 𝓐) := ⟨.start (Classical.arbitrary 𝓚)⟩

/-- The discrete σ-algebra on the states of the self-loop MDPs. -/
instance : MeasurableSpace (SelfLoopState 𝓚 𝓐) := ⊤

instance : DiscreteMeasurableSpace (SelfLoopState 𝓚 𝓐) := ⟨fun _ ↦ trivial⟩

/-- The states of the self-loop MDPs are the disjoint union of the start states and of two copies
of the pairs. -/
private def equivSum : SelfLoopState 𝓚 𝓐 ≃ 𝓚 ⊕ (𝓚 × 𝓐) ⊕ (𝓚 × 𝓐) where
  toFun
    | start x => .inl x
    | loop z => .inr (.inl z)
    | sink z => .inr (.inr z)
  invFun
    | .inl x => start x
    | .inr (.inl z) => loop z
    | .inr (.inr z) => sink z
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with x | z | z <;> rfl

end SelfLoopState

open SelfLoopState

/-- The self-loop MDPs with `K` start states and `A` actions have `S = K (1 + 2 A)` states. -/
theorem card_selfLoopState {𝓚 𝓐 : Type*} [Fintype 𝓚] [Fintype 𝓐] :
    Fintype.card (SelfLoopState 𝓚 𝓐) = Fintype.card 𝓚 * (1 + 2 * Fintype.card 𝓐) := by
  rw [Fintype.card_congr equivSum, Fintype.card_sum, Fintype.card_sum, Fintype.card_prod]
  ring

variable {𝓚 𝓐 : Type*}

/-- The reward of the self-loop MDPs: `1` in the self-loop states, `0` elsewhere. -/
def selfLoopReward : SelfLoopState 𝓚 𝓐 × 𝓐 → ℝ
  | (loop _, _) => 1
  | (start _, _) => 0
  | (sink _, _) => 0

@[simp]
lemma selfLoopReward_start (x : 𝓚) (a : 𝓐) : selfLoopReward (start x, a) = 0 := (rfl)

@[simp]
lemma selfLoopReward_loop (z : 𝓚 × 𝓐) (a : 𝓐) : selfLoopReward (loop z, a) = 1 := (rfl)

@[simp]
lemma selfLoopReward_sink (z : 𝓚 × 𝓐) (a : 𝓐) : selfLoopReward (sink z, a) = 0 := (rfl)

variable [Fintype 𝓚] [Fintype 𝓐] [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐]

/-- The transition kernel of the self-loop MDP with self-loop probabilities `θ`: every action leads
from `start x` to `loop (x, a)`, from `loop z` to itself with probability `θ z` and to `sink z`
otherwise, and from `sink z` to itself. -/
noncomputable def selfLoopKernel (θ : 𝓚 × 𝓐 → I) :
    Kernel (SelfLoopState 𝓚 𝓐 × 𝓐) (SelfLoopState 𝓚 𝓐) :=
  Kernel.ofFunOfCountable fun p ↦ match p with
    | (start x, a) => Measure.dirac (loop (x, a))
    | (loop z, _) => Ber(loop z, sink z, θ z)
    | (sink z, _) => Measure.dirac (sink z)

variable (θ : 𝓚 × 𝓐 → I)

@[simp]
lemma selfLoopKernel_start (x : 𝓚) (a : 𝓐) :
    selfLoopKernel θ (start x, a) = Measure.dirac (loop (x, a)) :=
  (rfl)

@[simp]
lemma selfLoopKernel_loop (z : 𝓚 × 𝓐) (a : 𝓐) :
    selfLoopKernel θ (loop z, a) = Ber(loop z, sink z, θ z) :=
  (rfl)

@[simp]
lemma selfLoopKernel_sink (z : 𝓚 × 𝓐) (a : 𝓐) :
    selfLoopKernel θ (sink z, a) = Measure.dirac (sink z) :=
  (rfl)

instance : IsMarkovKernel (selfLoopKernel θ) :=
  ⟨fun p ↦ by
    rcases p with ⟨x | z | z, a⟩ <;>
      simp only [selfLoopKernel_start, selfLoopKernel_loop, selfLoopKernel_sink] <;>
      infer_instance⟩

/-- The self-loop MDP with self-loop probabilities `θ`: the transition kernel `selfLoopKernel θ`
and the deterministic reward `selfLoopReward`. -/
noncomputable def selfLoopMDP : MDP (SelfLoopState 𝓚 𝓐) 𝓐 ℝ :=
  MDP.ofDet (selfLoopKernel θ) selfLoopReward (measurable_of_countable _)

@[simp]
lemma selfLoopMDP_P : (selfLoopMDP θ).P = selfLoopKernel θ := by
  simp [selfLoopMDP]

@[simp]
lemma selfLoopMDP_R :
    (selfLoopMDP θ).R = Kernel.deterministic selfLoopReward (measurable_of_countable _) := by
  simp [selfLoopMDP]

/-- The rewards of the self-loop MDPs are bounded by `1`. -/
lemma ae_abs_selfLoopMDP_R_le (p : SelfLoopState 𝓚 𝓐 × 𝓐) :
    ∀ᵐ r ∂((selfLoopMDP θ).R p), |r| ≤ 1 :=
  MDP.ae_abs_ofDet_R_le _ _ (fun p ↦ by rcases p with ⟨x | z | z, a⟩ <;> simp) p

/-! ### The optimal values -/

section OptValue

variable {γ : ℝ≥0}

/-- The optimal value of the self-loop MDP, in closed form. -/
private noncomputable def selfLoopValue (γ : ℝ≥0) : SelfLoopState 𝓚 𝓐 → ℝ
  | start x => ⨆ a, γ / (1 - γ * θ (x, a))
  | loop z => 1 / (1 - γ * θ z)
  | sink _ => 0

variable [Nonempty 𝓚] [Nonempty 𝓐]

private lemma optValue_selfLoopMDP (hγ : γ < 1) :
    (selfLoopMDP θ).optValue γ = selfLoopValue θ γ := by
  have hγ' : (γ : ℝ) < 1 := by exact_mod_cast hγ
  have h0 (q : I) : 0 < 1 - (γ : ℝ) * q :=
    sub_pos.2 ((mul_le_of_le_one_right γ.coe_nonneg (unitInterval.le_one q)).trans_lt hγ')
  have hB (q : I) : (γ : ℝ) / (1 - γ * q) ≤ 1 / (1 - γ) := by
    rw [div_le_div_iff₀ (h0 q) (by linarith)]
    nlinarith [mul_le_of_le_one_right γ.coe_nonneg (unitInterval.le_one q), γ.coe_nonneg]
  refine (MDP.eq_optValue_of_bellman_eq hγ (ae_abs_selfLoopMDP_R_le θ) (measurable_of_countable _)
    (B := 1 / (1 - γ)) (fun s ↦ ?_) ?_).symm
  · rcases s with x | z | z
    · simp only [selfLoopValue]
      have hnn : 0 ≤ ⨆ a, (γ : ℝ) / (1 - γ * θ (x, a)) :=
        le_ciSup_of_le (Finite.bddAbove_range _) (Classical.arbitrary 𝓐)
          (div_nonneg γ.coe_nonneg (h0 _).le)
      rw [abs_of_nonneg hnn]
      exact ciSup_le fun a ↦ hB _
    · simp only [selfLoopValue]
      rw [abs_of_nonneg (div_nonneg zero_le_one (h0 _).le)]
      gcongr
      exact mul_le_of_le_one_right γ.coe_nonneg (unitInterval.le_one _)
    · simpa [selfLoopValue] using hγ.le
  · funext s
    rcases s with x | z | z
    · simp [MDP.bellman_def, MDP.lookahead_def, selfLoopValue, div_eq_mul_inv]
    · simp only [MDP.bellman_def, MDP.lookahead_def, selfLoopMDP_P, selfLoopKernel_loop,
        selfLoopMDP_R, MDP.meanReward_deterministic, selfLoopReward_loop,
        integral_bernoulliMeasure, selfLoopValue, smul_eq_mul, mul_zero, add_zero, ciSup_const]
      field_simp [(h0 (θ z)).ne']
      ring
    · simp [MDP.bellman_def, MDP.lookahead_def, selfLoopValue]

/-- The optimal value of a start state of the self-loop MDP is `⨆ a, γ / (1 - γ θ (x, a))`. -/
theorem optValue_selfLoopMDP_start (hγ : γ < 1) (x : 𝓚) :
    (selfLoopMDP θ).optValue γ (start x) = ⨆ a, (γ : ℝ) / (1 - γ * (θ (x, a) : ℝ)) := by
  rw [optValue_selfLoopMDP θ hγ, selfLoopValue]

/-- The optimal value of the self-loop state `loop z` is `1 / (1 - γ θ z)`. -/
theorem optValue_selfLoopMDP_loop (hγ : γ < 1) (z : 𝓚 × 𝓐) :
    (selfLoopMDP θ).optValue γ (loop z) = 1 / (1 - γ * (θ z : ℝ)) := by
  rw [optValue_selfLoopMDP θ hγ, selfLoopValue]

/-- The optimal value of a sink is `0`. -/
theorem optValue_selfLoopMDP_sink (hγ : γ < 1) (z : 𝓚 × 𝓐) :
    (selfLoopMDP θ).optValue γ (sink z) = 0 := by
  rw [optValue_selfLoopMDP θ hγ, selfLoopValue]

/-- The optimal action value of the pair `(start x, a)` is `γ / (1 - γ θ (x, a))`. -/
theorem optQValue_selfLoopMDP_start (hγ : γ < 1) (x : 𝓚) (a : 𝓐) :
    (selfLoopMDP θ).optQValue γ (start x, a) = (γ : ℝ) / (1 - γ * (θ (x, a) : ℝ)) := by
  simp [MDP.optQValue_def, optValue_selfLoopMDP_loop θ hγ, div_eq_mul_inv]

/-- The optimal action value of every action in the self-loop state `loop z` is
`1 / (1 - γ θ z)`. -/
theorem optQValue_selfLoopMDP_loop (hγ : γ < 1) (z : 𝓚 × 𝓐) (a : 𝓐) :
    (selfLoopMDP θ).optQValue γ (loop z, a) = 1 / (1 - γ * (θ z : ℝ)) := by
  simp only [MDP.optQValue_def, selfLoopMDP_R, MDP.meanReward_deterministic, selfLoopReward_loop,
    selfLoopMDP_P, selfLoopKernel_loop, integral_bernoulliMeasure, optValue_selfLoopMDP_loop θ hγ,
    optValue_selfLoopMDP_sink θ hγ, smul_eq_mul, mul_zero, add_zero]
  have hγ' : (γ : ℝ) < 1 := by exact_mod_cast hγ
  field_simp [(sub_pos.2 ((mul_le_of_le_one_right γ.coe_nonneg
    (unitInterval.le_one (θ z))).trans_lt hγ')).ne']
  ring

/-- The optimal action value of every action in a sink is `0`. -/
theorem optQValue_selfLoopMDP_sink (hγ : γ < 1) (z : 𝓚 × 𝓐) (a : 𝓐) :
    (selfLoopMDP θ).optQValue γ (sink z, a) = 0 := by
  simp [MDP.optQValue_def, optValue_selfLoopMDP_sink θ hγ]

end OptValue

/-! ### The change of measure at one pair -/

section ChangeOfMeasure

variable {θ} {θ' : 𝓚 × 𝓐 → I} {j : 𝓚 × 𝓐}

/-- Two self-loop MDPs whose self-loop probabilities agree outside `j` have the same transitions
outside the self-loop state `loop j`. -/
lemma selfLoopKernel_eq_of_ne (hθ : ∀ z ≠ j, θ z = θ' z) {s : SelfLoopState 𝓚 𝓐}
    (hs : s ≠ loop j) (a : 𝓐) : selfLoopKernel θ (s, a) = selfLoopKernel θ' (s, a) := by
  rcases s with x | z | z
  · simp
  · rw [selfLoopKernel_loop, selfLoopKernel_loop, hθ z fun h ↦ hs (h ▸ rfl)]
  · simp

variable [DecidableEq 𝓚] [DecidableEq 𝓐]
  {alg : Algorithm Unit (SelfLoopState 𝓚 𝓐 × 𝓐) (SelfLoopState 𝓚 𝓐)}

/-- **Divergence decomposition** for the generative models of two self-loop MDPs whose self-loop
probabilities agree outside `j`: the relative entropy between the laws of the histories of the
first `T` queries of an algorithm is the expected number of queries of the self-loop state
`loop j`, with any action, times `d(θ j, θ' j)`. -/
theorem klDiv_map_history_eq_sum_lintegral_pullCount_mul_klBer (hθ : ∀ z ≠ j, θ z = θ' z) (T : ℕ) :
    klDiv ((trajMeasure alg (Environment.bandit (selfLoopMDP θ).P)).map
        (history IT.obs IT.action IT.feedback T))
      ((trajMeasure alg (Environment.bandit (selfLoopMDP θ').P)).map
        (history IT.obs IT.action IT.feedback T)) =
      (∑ b, ∫⁻ ω, (pullCount IT.action (loop j, b) T ω : ℝ≥0∞)
        ∂(trajMeasure alg (Environment.bandit (selfLoopMDP θ).P))) * klBer (θ j) (θ' j) := by
  rw [(IT.isAlgEnvSeq_trajMeasure _ _).klDiv_map_history_eq_sum_pullCount
    (IT.isAlgEnvSeq_trajMeasure _ _) T, Fintype.sum_prod_type,
    Finset.sum_eq_single (loop j) (fun s _ hs ↦ Finset.sum_eq_zero fun a _ ↦ by
      rw [show (selfLoopMDP θ).P (s, a) = (selfLoopMDP θ').P (s, a) by
        simpa using selfLoopKernel_eq_of_ne hθ hs a, klDiv_self, mul_zero])
      (fun h ↦ absurd (Finset.mem_univ _) h), Finset.sum_mul]
  simp [klDiv_bernoulliMeasure (show (loop j : SelfLoopState 𝓚 𝓐) ≠ sink j by simp)]

/-- **Change of measure at one pair.** Let the self-loop probabilities `θ` and `θ'` agree
outside `j`, and let `E` be a set of histories of `T` queries that has probability at least
`1 - δ` under the generative model of `θ` and at most `δ` under that of `θ'`. Then the expected
number of queries of the self-loop state `loop j` under `θ` is at least
`log (1 / (2.4 δ)) / d(θ j, θ' j)`. -/
theorem ofReal_log_le_sum_lintegral_pullCount_mul_klBer (hθ : ∀ z ≠ j, θ z = θ' z) {T : ℕ}
    {E : Set (Hist Unit (SelfLoopState 𝓚 𝓐 × 𝓐) (SelfLoopState 𝓚 𝓐) T)} {δ : ℝ}
    (hE : 1 - δ ≤ (trajMeasure alg (Environment.bandit (selfLoopMDP θ).P)).real
      (history IT.obs IT.action IT.feedback T ⁻¹' E))
    (hE' : (trajMeasure alg (Environment.bandit (selfLoopMDP θ').P)).real
      (history IT.obs IT.action IT.feedback T ⁻¹' E) ≤ δ) :
    ENNReal.ofReal (Real.log (1 / (2.4 * δ))) ≤
      (∑ b, ∫⁻ ω, (pullCount IT.action (loop j, b) T ω : ℝ≥0∞)
        ∂(trajMeasure alg (Environment.bandit (selfLoopMDP θ).P))) * klBer (θ j) (θ' j) := by
  rw [← klDiv_map_history_eq_sum_lintegral_pullCount_mul_klBer hθ T, ← one_mul (ENNReal.ofReal _)]
  refine mul_ofReal_log_le_of_mul_klBer_le le_rfl fun hδ ↦ ?_
  have hm := (IT.isAlgEnvSeq_trajMeasure alg
    (Environment.bandit (selfLoopMDP θ).P)).measurable_history T
  have hm' := (IT.isAlgEnvSeq_trajMeasure alg
    (Environment.bandit (selfLoopMDP θ').P)).measurable_history T
  have hE_meas : MeasurableSet E := .of_discrete
  -- The data processing inequality for the indicator of `E`.
  refine (one_mul _).trans_le (le_trans ?_ (klBer_measureReal_le_klDiv hE_meas))
  rw [map_measureReal_apply hm hE_meas, map_measureReal_apply hm' hE_meas]
  calc klBer δ (1 - δ) = klBer (1 - δ) δ := by rw [← klBer_one_sub_one_sub, sub_sub_cancel]
    _ ≤ _ := klBer_le_klBer hE' (by linarith) hE

/-- **Two-point lower bound at one pair.** Let the self-loop probabilities `θ` and `θ'` agree
outside `j = (x, a)`, with optimal action values at `(start x, a)` more than `2 ε` apart. If an
estimate computed from the history of `T` queries is within `ε` of the optimal action value at
`(start x, a)` with probability at least `1 - δ` under both generative models, then the expected
number of queries of the self-loop state `loop j` under `θ` is at least
`log (1 / (2.4 δ)) / d(θ j, θ' j)`. -/
theorem ofReal_log_le_sum_lintegral_pullCount_mul_klBer_of_two_mul_lt [Nonempty 𝓚]
    (hθ : ∀ z ≠ j, θ z = θ' z) {γ : ℝ≥0} {ε : ℝ}
    (hgap : 2 * ε < |(selfLoopMDP θ').optQValue γ (start j.1, j.2) -
      (selfLoopMDP θ).optQValue γ (start j.1, j.2)|) {T : ℕ}
    (est : Hist Unit (SelfLoopState 𝓚 𝓐 × 𝓐) (SelfLoopState 𝓚 𝓐) T → ℝ) {δ : ℝ}
    (h : 1 - δ ≤ (trajMeasure alg (Environment.bandit (selfLoopMDP θ).P)).real
      {ω | |est (history IT.obs IT.action IT.feedback T ω) -
        (selfLoopMDP θ).optQValue γ (start j.1, j.2)| ≤ ε})
    (h' : 1 - δ ≤ (trajMeasure alg (Environment.bandit (selfLoopMDP θ').P)).real
      {ω | |est (history IT.obs IT.action IT.feedback T ω) -
        (selfLoopMDP θ').optQValue γ (start j.1, j.2)| ≤ ε}) :
    ENNReal.ofReal (Real.log (1 / (2.4 * δ))) ≤
      (∑ b, ∫⁻ ω, (pullCount IT.action (loop j, b) T ω : ℝ≥0∞)
        ∂(trajMeasure alg (Environment.bandit (selfLoopMDP θ).P))) * klBer (θ j) (θ' j) := by
  set Q := (selfLoopMDP θ).optQValue γ (start j.1, j.2)
  set Q' := (selfLoopMDP θ').optQValue γ (start j.1, j.2)
  refine ofReal_log_le_sum_lintegral_pullCount_mul_klBer hθ (E := {hh | |est hh - Q| ≤ ε}) h ?_
  -- The estimate cannot be within `ε` of both `Q` and `Q'`.
  have hsub : history IT.obs IT.action IT.feedback T ⁻¹' {hh | |est hh - Q| ≤ ε} ⊆
      {ω | |est (history IT.obs IT.action IT.feedback T ω) - Q'| ≤ ε}ᶜ := fun ω hE hE' ↦ by
    have h1 : |est (history IT.obs IT.action IT.feedback T ω) - Q| ≤ ε := hE
    have h2 : |est (history IT.obs IT.action IT.feedback T ω) - Q'| ≤ ε := hE'
    have := abs_sub_le Q' (est (history IT.obs IT.action IT.feedback T ω)) Q
    rw [abs_sub_comm] at h2
    linarith
  have hm := (IT.isAlgEnvSeq_trajMeasure alg
    (Environment.bandit (selfLoopMDP θ').P)).measurable_history T
  calc _ ≤ _ := measureReal_mono hsub
    _ = 1 - (trajMeasure alg (Environment.bandit (selfLoopMDP θ').P)).real
        {ω | |est (history IT.obs IT.action IT.feedback T ω) - Q'| ≤ ε} :=
        probReal_compl_eq_one_sub (hm (.of_discrete (s := {hh | |est hh - Q'| ≤ ε})))
    _ ≤ δ := by linarith

end ChangeOfMeasure

/-! ### The parameters of the lower bound -/

section Parameters

variable {g ε p q : ℝ} (hg : 2 / 5 ≤ g) (hg1 : g < 1) (hε : 0 < ε) (hε1 : ε ≤ 1 / 32)
  (hp : p = (4 * g - 1) / (3 * g)) (hq : q = p + 32 * (1 - g) ^ 2 * ε / (9 * g ^ 2))

include hg hp in
private lemma half_le_selfLoopProb : 1 / 2 ≤ p := by
  rw [hp, le_div_iff₀ (by linarith)]
  linarith

include hg hg1 hε hε1 hp hq in
private lemma le_one_sub_selfLoopProb : (1 - g) / (6 * g) ≤ 1 - q := by
  have hg0 : 0 < g := by linarith
  have h : 1 - q = (1 - g) / (3 * g) - 32 * (1 - g) ^ 2 * ε / (9 * g ^ 2) := by
    rw [hq, hp]; field_simp; ring
  have h1 : 192 * (1 - g) * ε ≤ 9 * g := by nlinarith
  have h2 : 32 * (1 - g) ^ 2 * ε / (9 * g ^ 2) ≤ (1 - g) / (6 * g) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h1 (by nlinarith : (0 : ℝ) ≤ (1 - g) * g)]
  rw [h]
  have : (1 - g) / (3 * g) = 2 * ((1 - g) / (6 * g)) := by field_simp; ring
  linarith

include hg hg1 hε hε1 hp hq in
private lemma sq_sub_div_le : (q - p) ^ 2 / (q * (1 - q)) ≤ 2400 * (1 - g) ^ 3 * ε ^ 2 := by
  have hg0 : 0 < g := by linarith
  have h1g : 0 < 1 - g := by linarith
  have hp2 := half_le_selfLoopProb hg hp
  have h1q := le_one_sub_selfLoopProb hg hg1 hε hε1 hp hq
  have hqp : q - p = 32 * (1 - g) ^ 2 * ε / (9 * g ^ 2) := by rw [hq]; ring
  have hpq : p ≤ q := by
    have : 0 ≤ q - p := by rw [hqp]; positivity
    linarith
  calc (q - p) ^ 2 / (q * (1 - q)) ≤ (q - p) ^ 2 / (1 / 2 * ((1 - g) / (6 * g))) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          (mul_le_mul (by linarith) h1q (by positivity) (by linarith))
    _ = 12288 * (1 - g) ^ 3 * ε ^ 2 / (81 * g ^ 3) := by
        rw [hqp]; field_simp; ring
    _ ≤ 2400 * (1 - g) ^ 3 * ε ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have hg3 : (2 / 5) ^ 3 ≤ g ^ 3 := pow_le_pow_left₀ (by norm_num) hg 3
        have : 0 ≤ (1 - g) ^ 3 * ε ^ 2 := by positivity
        nlinarith

include hg hg1 hε hε1 hp hq in
private lemma two_mul_lt_div_sub_div : 2 * ε < g / (1 - g * q) - g / (1 - g * p) := by
  have hg0 : 0 < g := by linarith
  have h1g : 0 < 1 - g := by linarith
  have h1q := le_one_sub_selfLoopProb hg hg1 hε hε1 hp hq
  have h1p : 1 - g * p = 4 * (1 - g) / 3 := by rw [hp]; field_simp; ring
  have hqp : q - p = 32 * (1 - g) ^ 2 * ε / (9 * g ^ 2) := by rw [hq]; ring
  have hα : 0 < q - p := by rw [hqp]; positivity
  have hq1 : 0 < 1 - g * q := by
    have : 0 < (1 - g) / (6 * g) := by positivity
    nlinarith
  have hp1 : 0 < 1 - g * p := by rw [h1p]; linarith
  have hlt : 1 - g * q < 1 - g * p := by nlinarith
  calc 2 * ε = g ^ 2 * (q - p) / ((1 - g * p) * (1 - g * p)) := by
        rw [hqp, h1p]; field_simp; ring
    _ < g ^ 2 * (q - p) / ((1 - g * p) * (1 - g * q)) := by
        gcongr
    _ = g / (1 - g * q) - g / (1 - g * p) := by
        field_simp; ring

end Parameters

/-! ### The lower bound -/

section LowerBound

variable {T : ℕ}

/-- The expected numbers of queries of the self-loop states, with any action, add up to at most
the number `T` of queries. -/
private lemma sum_sum_lintegral_pullCount_loop_le [DecidableEq 𝓚] [DecidableEq 𝓐]
    (P : Measure (ℕ → Round Unit (SelfLoopState 𝓚 𝓐 × 𝓐) (SelfLoopState 𝓚 𝓐)))
    [IsProbabilityMeasure P] :
    ∑ z : 𝓚 × 𝓐, ∑ b, ∫⁻ ω, (pullCount IT.action (loop z, b) T ω : ℝ≥0∞) ∂P ≤ T := by
  have hinj : Function.Injective (loop : 𝓚 × 𝓐 → SelfLoopState 𝓚 𝓐) := fun _ _ h ↦ loop.inj h
  calc ∑ z : 𝓚 × 𝓐, ∑ b, ∫⁻ ω, (pullCount IT.action (loop z, b) T ω : ℝ≥0∞) ∂P
      = ∑ s ∈ Finset.univ.map ⟨loop, hinj⟩, ∑ b,
          ∫⁻ ω, (pullCount IT.action (s, b) T ω : ℝ≥0∞) ∂P := by simp [Finset.sum_map]
    _ ≤ ∑ s, ∑ b, ∫⁻ ω, (pullCount IT.action (s, b) T ω : ℝ≥0∞) ∂P :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ k, (∫⁻ ω, (pullCount IT.action k T ω : ℝ≥0∞) ∂P) * 1 := by
        rw [← Fintype.sum_prod_type']; simp
    _ = T := by
        rw [sum_lintegral_pullCount_mul IT.measurable_action measurable_const]
        simp

variable [Nonempty 𝓚] [Nonempty 𝓐]
  {alg : Algorithm Unit (SelfLoopState 𝓚 𝓐 × 𝓐) (SelfLoopState 𝓚 𝓐)} {γ : ℝ≥0} {ε δ : ℝ}

/-- The bound at one pair `z` for the self-loop MDP with self-loop probability `p` at every pair,
compared with the MDP whose self-loop probability at `z` is `p + α`. -/
private lemma ofReal_log_le_sum_lintegral_pullCount_loop_mul [DecidableEq 𝓚] [DecidableEq 𝓐]
    (hγ : 2 / 5 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 32)
    (est : Hist Unit (SelfLoopState 𝓚 𝓐 × 𝓐) (SelfLoopState 𝓚 𝓐) T → SelfLoopState 𝓚 𝓐 × 𝓐 → ℝ)
    (h : ∀ θ : 𝓚 × 𝓐 → I, (∀ z, (θ z : ℝ) = (4 * γ - 1) / (3 * γ) ∨
        (θ z : ℝ) = (4 * γ - 1) / (3 * γ) + 32 * (1 - γ) ^ 2 * ε / (9 * γ ^ 2)) →
      1 - δ ≤ (trajMeasure alg (Environment.bandit (selfLoopMDP θ).P)).real
        {ω | ∀ x a, |est (history IT.obs IT.action IT.feedback T ω) (start x, a) -
          (selfLoopMDP θ).optQValue γ (start x, a)| ≤ ε})
    {θ₀ : 𝓚 × 𝓐 → I} (hθ₀ : ∀ z, (θ₀ z : ℝ) = (4 * γ - 1) / (3 * γ)) (z : 𝓚 × 𝓐) :
    ENNReal.ofReal (Real.log (1 / (2.4 * δ))) ≤
      (∑ b, ∫⁻ ω, (pullCount IT.action (loop z, b) T ω : ℝ≥0∞)
        ∂(trajMeasure alg (Environment.bandit (selfLoopMDP θ₀).P))) *
        ENNReal.ofReal (2400 * (1 - γ) ^ 3 * ε ^ 2) := by
  classical
  set p : ℝ := (4 * γ - 1) / (3 * γ) with hp
  set q : ℝ := p + 32 * (1 - γ) ^ 2 * ε / (9 * γ ^ 2) with hq
  have hγ' : (2 / 5 : ℝ) ≤ γ := by exact_mod_cast hγ
  have hγ1' : (γ : ℝ) < 1 := by exact_mod_cast hγ1
  have hp2 := half_le_selfLoopProb hγ' hp
  have h1q := le_one_sub_selfLoopProb hγ' hγ1' hε hε1 hp hq
  have hpq : p ≤ q := by
    have : 0 ≤ 32 * (1 - (γ : ℝ)) ^ 2 * ε / (9 * γ ^ 2) := by
      have : (0 : ℝ) ≤ 1 - γ := by linarith
      positivity
    linarith
  have hq1 : q < 1 := by
    have : 0 < (1 - (γ : ℝ)) / (6 * γ) := by
      have : (0 : ℝ) < 1 - γ := by linarith
      have : (0 : ℝ) < γ := by linarith
      positivity
    linarith
  let θ₁ := Function.update θ₀ z ⟨q, by linarith, hq1.le⟩
  have hQ₀ : (selfLoopMDP θ₀).optQValue γ (start z.1, z.2) = γ / (1 - γ * p) := by
    rw [optQValue_selfLoopMDP_start θ₀ hγ1, hθ₀]
  have hQ₁ : (selfLoopMDP θ₁).optQValue γ (start z.1, z.2) = γ / (1 - γ * q) := by
    rw [optQValue_selfLoopMDP_start θ₁ hγ1]
    simp [θ₁]
  have hθ₁ (y : 𝓚 × 𝓐) : (θ₁ y : ℝ) = p ∨ (θ₁ y : ℝ) = q := by
    by_cases hy : y = z
    · subst hy; exact Or.inr (by simp [θ₁])
    · exact Or.inl (by simp [θ₁, hy, hθ₀])
  have hgap : 2 * ε < |(selfLoopMDP θ₁).optQValue γ (start z.1, z.2) -
      (selfLoopMDP θ₀).optQValue γ (start z.1, z.2)| := by
    rw [hQ₀, hQ₁]
    exact (two_mul_lt_div_sub_div hγ' hγ1' hε hε1 hp hq).trans_le (le_abs_self _)
  -- The two-point bound at `z`, with `d(p, p + α) ≤ 2400 (1 - γ)³ ε²`.
  refine (ofReal_log_le_sum_lintegral_pullCount_mul_klBer_of_two_mul_lt (alg := alg)
    (θ := θ₀) (θ' := θ₁) (j := z) (fun y hy ↦ by simp [θ₁, hy]) hgap
    (fun hh ↦ est hh (start z.1, z.2))
    ((h θ₀ fun y ↦ Or.inl (hθ₀ y)).trans (measureReal_mono fun ω hω ↦ hω z.1 z.2))
    ((h θ₁ hθ₁).trans (measureReal_mono fun ω hω ↦ hω z.1 z.2))).trans ?_
  gcongr
  rw [show (θ₀ z : ℝ) = p from hθ₀ z, show (θ₁ z : ℝ) = q by simp [θ₁]]
  refine (klBer_le_ofReal_sq_sub_div ⟨by linarith, by linarith⟩ ⟨by linarith, hq1⟩).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [← neg_sub, neg_sq]
  exact sq_sub_div_le hγ' hγ1' hε hε1 hp hq

/-- **Lower bound for planning with a generative model** [AMK13, Theorem 3], corrected, with
explicit constants. Let `2 / 5 ≤ γ < 1`, `0 < ε ≤ 1 / 32`, `p = (4γ - 1) / (3γ)` and
`α = 32 (1 - γ)² ε / (9 γ²) = 2 (1 - γ p)² ε / γ²`. Suppose that an algorithm querying the
generative model `T` times returns an estimate of the optimal action values that is `ε`-accurate at
all the pairs `(start x, a)` with probability at least `1 - δ`, for every self-loop MDP whose
self-loop probabilities lie in `{p, p + α}`. Then
`K A log (1 / (2.4 δ)) ≤ 2400 (1 - γ)³ ε² T`, where `K` and `A` are the numbers of start states
and of actions. -/
theorem card_mul_card_mul_log_le_of_forall_abs_sub_optQValue_le (hγ : 2 / 5 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 32)
    (est : Hist Unit (SelfLoopState 𝓚 𝓐 × 𝓐) (SelfLoopState 𝓚 𝓐) T → SelfLoopState 𝓚 𝓐 × 𝓐 → ℝ)
    (h : ∀ θ : 𝓚 × 𝓐 → I, (∀ z, (θ z : ℝ) = (4 * γ - 1) / (3 * γ) ∨
        (θ z : ℝ) = (4 * γ - 1) / (3 * γ) + 32 * (1 - γ) ^ 2 * ε / (9 * γ ^ 2)) →
      1 - δ ≤ (trajMeasure alg (Environment.bandit (selfLoopMDP θ).P)).real
        {ω | ∀ x a, |est (history IT.obs IT.action IT.feedback T ω) (start x, a) -
          (selfLoopMDP θ).optQValue γ (start x, a)| ≤ ε}) :
    Fintype.card 𝓚 * Fintype.card 𝓐 * Real.log (1 / (2.4 * δ)) ≤
      2400 * (1 - γ) ^ 3 * ε ^ 2 * T := by
  classical
  have hγ' : (2 / 5 : ℝ) ≤ γ := by exact_mod_cast hγ
  have hγ1' : (γ : ℝ) < 1 := by exact_mod_cast hγ1
  have hp0 := half_le_selfLoopProb hγ' rfl
  have hp1 : (4 * γ - 1) / (3 * γ) ≤ (1 : ℝ) := by
    rw [div_le_one (by linarith)]
    linarith
  -- The self-loop MDP with self-loop probability `p` at every pair.
  let θ₀ : 𝓚 × 𝓐 → I := fun _ ↦ ⟨(4 * γ - 1) / (3 * γ), by linarith, hp1⟩
  set κ : ℝ := 2400 * (1 - γ) ^ 3 * ε ^ 2
  set L : ℝ := Real.log (1 / (2.4 * δ))
  -- Sum the bounds at the pairs: the expected numbers of queries add up to at most `T`.
  have hsum : (Fintype.card 𝓚 * Fintype.card 𝓐 : ℝ≥0∞) * ENNReal.ofReal L ≤
      T * ENNReal.ofReal κ := by
    calc (Fintype.card 𝓚 * Fintype.card 𝓐 : ℝ≥0∞) * ENNReal.ofReal L
        = ∑ _z : 𝓚 × 𝓐, ENNReal.ofReal L := by
          simp [Finset.card_univ, Fintype.card_prod]
      _ ≤ ∑ z : 𝓚 × 𝓐, (∑ b, ∫⁻ ω, (pullCount IT.action (loop z, b) T ω : ℝ≥0∞)
            ∂(trajMeasure alg (Environment.bandit (selfLoopMDP θ₀).P))) * ENNReal.ofReal κ :=
          Finset.sum_le_sum fun z _ ↦
            ofReal_log_le_sum_lintegral_pullCount_loop_mul hγ hγ1 hε hε1 est h (fun _ ↦ rfl) z
      _ ≤ T * ENNReal.ofReal κ := by
          rw [← Finset.sum_mul]
          gcongr
          exact sum_sum_lintegral_pullCount_loop_le _
  have hκ0 : 0 ≤ κ := by
    have : (0 : ℝ) ≤ 1 - γ := by linarith
    positivity
  rcases le_or_gt L 0 with hL | hL
  · have : (0 : ℝ) ≤ κ * T := by positivity
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card 𝓚))
      (Nat.cast_nonneg (α := ℝ) (Fintype.card 𝓐))]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hsum
  linarith

end LowerBound

/-- **Lower bound for planning with a generative model** [AMK13, Theorem 3], corrected: there are
constants `C, ε₀, δ₀ > 0` such that, for `2 / 5 ≤ γ < 1`, `0 < ε ≤ ε₀` and `0 < δ < δ₀ / (K A)`,
every algorithm that queries the generative model `T` times and returns an `ε`-accurate estimate
of the optimal action values with probability at least `1 - δ` on every self-loop MDP with `K`
start states, `A` actions and self-loop probabilities in `{p, p + α}` makes
`T ≥ K A log (K A / (C δ)) / (C (1 - γ)³ ε²)` queries. Here `p = (4γ - 1) / (3γ)` and
`α = 32 (1 - γ)² ε / (9 γ²)` are the parameters of [AMK13]. The constants are `C = 4800`,
`ε₀ = 1 / 32` and `δ₀ = 5 / 24`. -/
theorem exists_const_le_of_forall_abs_sub_optQValue_le :
    ∃ C > 0, ∃ ε₀ > 0, ∃ δ₀ > 0, ∀ (𝓚 : Type u) (𝓐 : Type v) [Fintype 𝓚] [Nonempty 𝓚]
      [Fintype 𝓐] [Nonempty 𝓐] [MeasurableSpace 𝓐] [MeasurableSingletonClass 𝓐] (γ : ℝ≥0),
      2 / 5 ≤ γ → γ < 1 → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ δ : ℝ, 0 < δ →
      δ < δ₀ / (Fintype.card 𝓚 * Fintype.card 𝓐) →
      ∀ (alg : Algorithm Unit (SelfLoopState 𝓚 𝓐 × 𝓐) (SelfLoopState 𝓚 𝓐)) (T : ℕ)
        (est : Hist Unit (SelfLoopState 𝓚 𝓐 × 𝓐) (SelfLoopState 𝓚 𝓐) T →
          SelfLoopState 𝓚 𝓐 × 𝓐 → ℝ),
      (∀ θ : 𝓚 × 𝓐 → I, (∀ z, (θ z : ℝ) = (4 * γ - 1) / (3 * γ) ∨
          (θ z : ℝ) = (4 * γ - 1) / (3 * γ) + 32 * (1 - γ) ^ 2 * ε / (9 * γ ^ 2)) →
        1 - δ ≤ (trajMeasure alg (Environment.bandit (selfLoopMDP θ).P)).real
          {ω | ∀ p, |est (history IT.obs IT.action IT.feedback T ω) p -
            (selfLoopMDP θ).optQValue γ p| ≤ ε}) →
      Fintype.card 𝓚 * Fintype.card 𝓐 *
          Real.log (Fintype.card 𝓚 * Fintype.card 𝓐 / (C * δ)) / (C * (1 - γ) ^ 3 * ε ^ 2) ≤
        T := by
  refine ⟨4800, by norm_num, 1 / 32, by norm_num, 5 / 24, by norm_num,
    fun 𝓚 𝓐 _ _ _ _ _ _ γ hγ hγ1 ε hε hε1 δ hδ hδ₀ alg T est h ↦ ?_⟩
  have hb := card_mul_card_mul_log_le_of_forall_abs_sub_optQValue_le hγ hγ1 hε hε1 est
    fun θ hθ ↦ (h θ hθ).trans (measureReal_mono fun ω hω x a ↦ hω (start x, a))
  set n : ℝ := Fintype.card 𝓚 * Fintype.card 𝓐 with hn
  have hn1 : 1 ≤ n := by
    rw [hn]
    have h1 : (1 : ℝ) ≤ Fintype.card 𝓚 := by exact_mod_cast Fintype.card_pos
    have h2 : (1 : ℝ) ≤ Fintype.card 𝓐 := by exact_mod_cast Fintype.card_pos
    nlinarith
  have hγ1' : (γ : ℝ) < 1 := by exact_mod_cast hγ1
  have hpos : 0 < 4800 * (1 - (γ : ℝ)) ^ 3 * ε ^ 2 := by
    have : (0 : ℝ) < 1 - γ := by linarith
    positivity
  -- With `u = 1 / (2.4 δ)`, the condition on `δ` gives `n ≤ u`, hence `n / (4800 δ) ≤ u²`.
  have hu : n ≤ 1 / (2.4 * δ) := by
    rw [lt_div_iff₀ (by positivity)] at hδ₀
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hlog : Real.log (n / (4800 * δ)) ≤ 2 * Real.log (1 / (2.4 * δ)) := by
    rw [show 2 * Real.log (1 / (2.4 * δ)) = Real.log ((1 / (2.4 * δ)) ^ 2) by
      rw [Real.log_pow]; norm_num]
    refine Real.log_le_log (by positivity) ?_
    calc n / (4800 * δ) ≤ n * (1 / (2.4 * δ)) := by
          rw [div_le_iff₀ (by positivity)]
          field_simp
          nlinarith
      _ ≤ (1 / (2.4 * δ)) ^ 2 := by rw [sq]; gcongr
  rw [div_le_iff₀ hpos]
  nlinarith

end LMLExplore.ReinforcementLearning
