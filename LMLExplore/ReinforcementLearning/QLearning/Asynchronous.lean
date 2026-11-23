/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.ValueIteration.ActionValue
public import LMLExplore.MeasureTheory.MeasurableSpace.Constructions
public import LMLExplore.Probability.StochasticApproximation.Asynchronous

/-!
# Asynchronous Q-learning and its almost-sure convergence

Asynchronous Q-learning estimates the optimal action value `Q*` of an MDP from a single run in
its environment, played by any algorithm. Along the states `O t`, actions `A t` and observed
rewards `Y t` of the run, it updates at round `t` the action value of the visited pair only:
`Q (t + 1) (O t, A t) = (1 - α t) * Q t (O t, A t) + α t * (Y t + γ * ⨆ a, Q t (O (t + 1), a))`,
with a learning rate `α t` known at the time of the action of round `t`. Tabular TD(0), which
estimates the value of the policy that plays the run, is the case of one action.

Tsitsiklis [Tsi94, Theorem 4 (a)] proves that with learning rates in `[0, 1]` whose sums diverge
at every pair and whose sums of squares are bounded, `Q t → Q*` almost surely. The recursion is an
asynchronous stochastic approximation, `Q (t + 1) p = Q t p + α t p * (F (Q t) p - Q t p + w t p)`,
of the fixed point of the optimality operator on action values
`F Q = r + γ P (s' ↦ ⨆ a', Q (s', a'))`, which is a `γ`-contraction for the sup norm with fixed
point `Q*`. The noise `w t` is the deviation of the target `Y t + γ * ⨆ a, Q t (O (t + 1), a)`
from its conditional mean `F (Q t) (O t, A t)`, at the visited pair; it contains both the reward
noise and the transition noise. The source minimizes costs; we maximize rewards.

## Main definitions

* `LMLExplore.ReinforcementLearning.qLearning γ Q₀ O A Y α`: the iterates of asynchronous
  Q-learning along the states `O`, actions `A` and rewards `Y` of a run, with discount `γ`,
  initial action value `Q₀` and learning rates `α`.

## Main statements

* `LMLExplore.ReinforcementLearning.qLearning_succ_apply_self`,
  `LMLExplore.ReinforcementLearning.qLearning_succ_apply_of_ne`: the update of the visited pair,
  and the other pairs are not updated.
* `LMLExplore.ReinforcementLearning.abs_qLearning_target_le`: the target of a round is bounded by
  `B` when the reward is bounded by `C`, the action values by `B`, and `C + γ B ≤ B`.
* `LMLExplore.ReinforcementLearning.abs_qLearning_le`: the iterates stay in `[-B, B]` when the
  rewards are bounded by `C` and `C + γ B ≤ B`;
  `LMLExplore.ReinforcementLearning.ae_abs_qLearning_le`: along a run in an MDP with rewards
  bounded by `C`, they are almost surely bounded by `max ‖Q₀‖ (|C| / (1 - γ))`.
* `LMLExplore.ReinforcementLearning.adapted_qLearning`: the iterates are known at the action of
  each round.
* `LMLExplore.ReinforcementLearning.condExp_feedback_add_mul_iSup_qLearning`: the target of
  round `t` has conditional mean `F (Q t) (O t, A t)` given the history up to the action of
  round `t`.
* `LMLExplore.ReinforcementLearning.ae_tendsto_qLearning_optQValue`: **almost-sure convergence of
  Q-learning** [Tsi94, Theorem 4 (a)].

## References

* [Tsi94] J. N. Tsitsiklis, *Asynchronous stochastic approximation and Q-learning*, Machine
  Learning 16 (1994), 185–202.
* [WD92] C. J. C. H. Watkins and P. Dayan, *Q-learning*, Machine Learning 8 (1992), 279–292.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology Finset Learning
open scoped NNReal ENNReal

namespace LMLExplore.ReinforcementLearning

variable {𝓢 𝓐 Ω : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {mΩ : MeasurableSpace Ω} [DecidableEq 𝓢] [DecidableEq 𝓐] {γ : ℝ≥0} {Q₀ : 𝓢 × 𝓐 → ℝ}
  {O : ℕ → Ω → 𝓢} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {α : ℕ → Ω → 𝓢 × 𝓐 → ℝ}

/-! ### The recursion -/

variable (γ Q₀ O A Y α) in
/-- **Asynchronous Q-learning** [WD92] along the states `O`, actions `A` and rewards `Y` of a run,
with discount `γ`, initial action value `Q₀` and learning rates `α`: at round `t`, only the
action value of the visited pair `(O t, A t)` is updated, to
`(1 - α t) * Q t (O t, A t) + α t * (Y t + γ * ⨆ a, Q t (O (t + 1), a))`, where `α t` is the
learning rate `α t ω (O t ω, A t ω)` of that pair. -/
noncomputable def qLearning : ℕ → Ω → 𝓢 × 𝓐 → ℝ
  | 0 => fun _ ↦ Q₀
  | t + 1 => fun ω ↦ Function.update (qLearning t ω) (O t ω, A t ω)
      ((1 - α t ω (O t ω, A t ω)) * qLearning t ω (O t ω, A t ω) +
        α t ω (O t ω, A t ω) * (Y t ω + γ * ⨆ a, qLearning t ω (O (t + 1) ω, a)))

@[simp]
lemma qLearning_zero (ω : Ω) : qLearning γ Q₀ O A Y α 0 ω = Q₀ :=
  (rfl)

lemma qLearning_succ (t : ℕ) (ω : Ω) :
    qLearning γ Q₀ O A Y α (t + 1) ω = Function.update (qLearning γ Q₀ O A Y α t ω)
      (O t ω, A t ω) ((1 - α t ω (O t ω, A t ω)) * qLearning γ Q₀ O A Y α t ω (O t ω, A t ω) +
        α t ω (O t ω, A t ω) *
          (Y t ω + γ * ⨆ a, qLearning γ Q₀ O A Y α t ω (O (t + 1) ω, a))) :=
  (rfl)

/-- Q-learning updates the action value of the visited pair towards the target
`Y t + γ * ⨆ a, Q t (O (t + 1), a)`. -/
lemma qLearning_succ_apply_self (t : ℕ) (ω : Ω) :
    qLearning γ Q₀ O A Y α (t + 1) ω (O t ω, A t ω) =
      (1 - α t ω (O t ω, A t ω)) * qLearning γ Q₀ O A Y α t ω (O t ω, A t ω) +
        α t ω (O t ω, A t ω) *
          (Y t ω + γ * ⨆ a, qLearning γ Q₀ O A Y α t ω (O (t + 1) ω, a)) := by
  rw [qLearning_succ, Function.update_self]

/-- Q-learning does not update the action values of the pairs that are not visited. -/
lemma qLearning_succ_apply_of_ne {t : ℕ} {ω : Ω} {p : 𝓢 × 𝓐} (hp : p ≠ (O t ω, A t ω)) :
    qLearning γ Q₀ O A Y α (t + 1) ω p = qLearning γ Q₀ O A Y α t ω p := by
  rw [qLearning_succ, Function.update_of_ne hp]

/-- With a reward bounded by `C` and action values bounded by `B`, where `C + γ * B ≤ B`, the
target `Y t + γ * ⨆ a, Q t (O (t + 1), a)` of round `t` is bounded by `B`. -/
lemma abs_qLearning_target_le [Nonempty 𝓐] {ω : Ω} {B C : ℝ} {t : ℕ} (hY : |Y t ω| ≤ C)
    (hQ : ∀ p, |qLearning γ Q₀ O A Y α t ω p| ≤ B) (hB : C + γ * B ≤ B) :
    |Y t ω + γ * ⨆ a, qLearning γ Q₀ O A Y α t ω (O (t + 1) ω, a)| ≤ B := by
  refine (abs_add_le _ _).trans (le_trans ?_ hB)
  rw [abs_mul, NNReal.abs_eq]
  exact add_le_add hY (mul_le_mul_of_nonneg_left (abs_ciSup_le fun a ↦ hQ _) γ.property)

/-- With learning rates in `[0, 1]` at the visited pairs, rewards bounded by `C` and an initial
action value bounded by `B`, where `C + γ * B ≤ B`, the iterates of Q-learning stay bounded by
`B`: each update is a convex combination of the current action value and a target bounded by
`C + γ * B`. With `γ < 1`, any `B ≥ max ‖Q₀‖ (C / (1 - γ))` will do. -/
theorem abs_qLearning_le [Nonempty 𝓐] {ω : Ω} {B C : ℝ}
    (hα : ∀ t, α t ω (O t ω, A t ω) ∈ Set.Icc (0 : ℝ) 1) (hY : ∀ t, |Y t ω| ≤ C)
    (hQ₀ : ∀ p, |Q₀ p| ≤ B) (hB : C + γ * B ≤ B) (t : ℕ) (p : 𝓢 × 𝓐) :
    |qLearning γ Q₀ O A Y α t ω p| ≤ B := by
  induction t generalizing p with
  | zero => exact hQ₀ p
  | succ t ih =>
    by_cases hp : p = (O t ω, A t ω)
    · subst hp
      rw [qLearning_succ_apply_self]
      have htarget := abs_qLearning_target_le (hY t) ih hB
      obtain ⟨h0, h1⟩ := hα t
      calc _ ≤ |1 - α t ω (O t ω, A t ω)| * |qLearning γ Q₀ O A Y α t ω (O t ω, A t ω)| +
            |α t ω (O t ω, A t ω)| *
              |Y t ω + γ * ⨆ a, qLearning γ Q₀ O A Y α t ω (O (t + 1) ω, a)| := by
            rw [← abs_mul, ← abs_mul]
            exact abs_add_le _ _
        _ ≤ (1 - α t ω (O t ω, A t ω)) * B + α t ω (O t ω, A t ω) * B := by
            rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonneg h0]
            exact add_le_add (mul_le_mul_of_nonneg_left (ih _) (sub_nonneg.2 h1))
              (mul_le_mul_of_nonneg_left htarget h0)
        _ = B := by ring
    · rw [qLearning_succ_apply_of_ne hp]
      exact ih p

/-- Along a run of any algorithm in any environment, the iterates of Q-learning with learning
rates known at the action of each round are known at the action of each round: `Q t` is
measurable for the history before round `t`, the state and the action of round `t`. -/
theorem adapted_qLearning [Countable 𝓢] [MeasurableSingletonClass 𝓢] [Countable 𝓐]
    [MeasurableSingletonClass 𝓐] {P : Measure Ω} {env : Environment 𝓢 𝓐 ℝ}
    {alg : Algorithm 𝓢 𝓐 ℝ} (h : IsAlgEnvSeq O A Y alg env P)
    (hα : Adapted h.filtrationAction α) :
    Adapted h.filtrationAction (qLearning γ Q₀ O A Y α) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    set ℱ := h.filtrationAction
    have hle : ℱ t ≤ ℱ (t + 1) := ℱ.mono t.le_succ
    have hQ : Measurable[ℱ (t + 1)] (qLearning γ Q₀ O A Y α t) := ih.mono hle le_rfl
    have hpair : Measurable[ℱ (t + 1)] fun ω ↦ (O t ω, A t ω) :=
      ((h.adapted_obs_filtrationAction t).prodMk (h.adapted_action_filtrationAction t)).mono hle
        le_rfl
    have hQpair : Measurable[ℱ (t + 1)] fun ω ↦ qLearning γ Q₀ O A Y α t ω (O t ω, A t ω) :=
      @Measurable.eval_index _ _ _ (ℱ (t + 1)) _ _ _ _ _ _ hQ hpair
    have hαpair : Measurable[ℱ (t + 1)] fun ω ↦ α t ω (O t ω, A t ω) :=
      @Measurable.eval_index _ _ _ (ℱ (t + 1)) _ _ _ _ _ _ ((hα t).mono hle le_rfl) hpair
    have hmax := hQ.iSup_apply_prodMk (h.adapted_obs_filtrationAction (t + 1))
    have hY : Measurable[ℱ (t + 1)] (Y t) :=
      h.measurable_feedback_filtrationAction_of_lt t.lt_succ_self
    refine @Measurable.of_eval _ _ _ (ℱ (t + 1)) _ _ fun p ↦ ?_
    simp_rw [qLearning_succ, Function.update_apply]
    refine Measurable.ite (hpair (measurableSet_singleton p) |>.congr ?_) ?_
      ((measurable_pi_apply p).comp hQ)
    · ext ω
      simp [eq_comm]
    · exact ((measurable_const.sub hαpair).mul hQpair).add
        (hαpair.mul (hY.add (measurable_const.mul hmax)))

/-- A bound `B ≥ |C| / (1 - γ)`, here `B = max b (|C| / (1 - γ))`, satisfies
`|C| + γ * B ≤ B`: it bounds the targets of Q-learning when it bounds the action values. -/
private lemma abs_add_mul_max_le {b C : ℝ} (hγ : γ < 1) :
    |C| + γ * max b (|C| / (1 - γ)) ≤ max b (|C| / (1 - γ)) := by
  have : |C| ≤ (1 - γ) * max b (|C| / (1 - γ)) :=
    (div_le_iff₀' (sub_pos.2 (by exact_mod_cast hγ))).1 (le_max_right _ _)
  linarith

/-! ### Q-learning along a run in an MDP -/

section Run

variable [Nonempty 𝓢] {P : Measure Ω} {M : MDP 𝓢 𝓐 ℝ} {μ : Measure 𝓢} {alg : Algorithm 𝓢 𝓐 ℝ}
  {C : ℝ}

/-- Along a run in the environment of an MDP with rewards bounded by `C`, with `γ < 1` and
learning rates in `[0, 1]`, the iterates of Q-learning are almost surely bounded by
`max ‖Q₀‖ (|C| / (1 - γ))`. -/
theorem ae_abs_qLearning_le [Fintype 𝓢] [Fintype 𝓐] [Nonempty 𝓐] [SFinite P]
    (h : IsAlgEnvSeq O A Y alg (M.env μ) P)
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hα : ∀ t ω p, α t ω p ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, ∀ t p, |qLearning γ Q₀ O A Y α t ω p| ≤ max ‖Q₀‖ (|C| / (1 - γ)) := by
  have hB := abs_add_mul_max_le (b := ‖Q₀‖) (C := C) hγ
  have hQ₀ (p : 𝓢 × 𝓐) : |Q₀ p| ≤ max ‖Q₀‖ (|C| / (1 - γ)) := by
    have := norm_le_pi_norm Q₀ p
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  filter_upwards [ae_all_iff.2 (MDP.ae_abs_feedback_le h hR)] with ω hω t p
  exact abs_qLearning_le (fun t ↦ hα _ _ _) (fun t ↦ (hω t).trans (le_abs_self C)) hQ₀ hB t p

/-- The target `Y t + γ * ⨆ a, Q t (O (t + 1), a)` of round `t` is known after round `t`. -/
private lemma measurable_qLearning_target [Countable 𝓢] [MeasurableSingletonClass 𝓢]
    [Countable 𝓐] [MeasurableSingletonClass 𝓐] (h : IsAlgEnvSeq O A Y alg (M.env μ) P)
    (hαm : Adapted h.filtrationAction α) (t : ℕ) :
    Measurable[h.filtrationAction (t + 1)]
      fun ω ↦ Y t ω + γ * ⨆ a, qLearning γ Q₀ O A Y α t ω (O (t + 1) ω, a) :=
  (h.measurable_feedback_filtrationAction_of_lt t.lt_succ_self).add
    (measurable_const.mul (((adapted_qLearning h hαm t).mono (h.filtrationAction.mono t.le_succ)
      le_rfl).iSup_apply_prodMk (h.adapted_obs_filtrationAction (t + 1))))

/-- The target of round `t` is almost surely bounded by `max ‖Q₀‖ (|C| / (1 - γ))`, the bound
of the iterates. -/
private lemma ae_abs_qLearning_target_le [Fintype 𝓢] [Fintype 𝓐] [Nonempty 𝓐] [SFinite P]
    (h : IsAlgEnvSeq O A Y alg (M.env μ) P) (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hα : ∀ t ω p, α t ω p ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, ∀ t, |Y t ω + γ * ⨆ a, qLearning γ Q₀ O A Y α t ω (O (t + 1) ω, a)| ≤
      max ‖Q₀‖ (|C| / (1 - γ)) := by
  have hB := abs_add_mul_max_le (b := ‖Q₀‖) (C := C) hγ
  filter_upwards [ae_all_iff.2 (MDP.ae_abs_feedback_le h hR), ae_abs_qLearning_le h hγ hR hα]
    with ω hY hQ t
  exact abs_qLearning_target_le ((hY t).trans (le_abs_self C)) (hQ t) hB

/-- **The target of Q-learning is unbiased for the optimality operator.** Along a run in the
environment of an MDP with bounded rewards, given the history before round `t`, the state and the
action of round `t`, the target `Y t + γ * ⨆ a, Q t (O (t + 1), a)` has conditional expectation
`(r + γ P (s' ↦ ⨆ a', Q t (s', a'))) (O t, A t)`, the optimality operator on action values
applied to `Q t`, at the visited pair. -/
theorem condExp_feedback_add_mul_iSup_qLearning [Finite 𝓢] [MeasurableSingletonClass 𝓢] [Finite 𝓐]
    [Nonempty 𝓐] [MeasurableSingletonClass 𝓐] [IsFiniteMeasure P]
    (h : IsAlgEnvSeq O A Y alg (M.env μ) P) (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hαm : Adapted h.filtrationAction α)
    (hα : ∀ t ω p, α t ω p ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    P[fun ω ↦ Y t ω + γ * ⨆ a, qLearning γ Q₀ O A Y α t ω (O (t + 1) ω, a) |
        h.filtrationAction t] =ᵐ[P]
      fun ω ↦ M.lookahead γ (fun s ↦ ⨆ a, qLearning γ Q₀ O A Y α t ω (s, a)) (O t ω, A t ω) := by
  have := Fintype.ofFinite 𝓢
  have := Fintype.ofFinite 𝓐
  have hQ := adapted_qLearning (γ := γ) (Q₀ := Q₀) h hαm t
  refine MDP.condExp_feedback_add_mul_obs_add_one h hR t
    (@Measurable.of_eval _ _ _ (h.filtrationAction t) _ _ fun s ↦
      Measurable.iSup fun a ↦ (measurable_pi_apply (s, a)).comp hQ) ?_
  -- the largest next action value is bounded by the bound of the iterates
  refine .of_bound (((hQ.mono (h.filtrationAction.le _) le_rfl).iSup_apply_prodMk
    (h.measurable_obs (t + 1))).aestronglyMeasurable) (max ‖Q₀‖ (|C| / (1 - γ)))
    ((ae_abs_qLearning_le (Q₀ := Q₀) h hγ hR hα).mono fun ω hω ↦ ?_)
  simpa [Real.norm_eq_abs] using abs_ciSup_le fun a ↦ hω t (O (t + 1) ω, a)

/-! ### Almost-sure convergence -/

/-- **Almost-sure convergence of Q-learning** [Tsi94, Theorem 4 (a)]. Let `M` be an MDP with
finite state and action spaces and rewards bounded by `C`, let `γ < 1`, and consider a run of any
algorithm in the environment `M.env μ`. Let the learning rates `α t p` be known at the action of
round `t`, lie in `[0, 1]`, vanish off the visited pair `(O t, A t)`, and satisfy
`∑ t, α t p = ∞` and `∑ t, α t p ^ 2 ≤ K` almost surely, for every pair `p` and a deterministic
`K`. Then, from any initial action value, the iterates of Q-learning converge almost surely to the
optimal action value `Q* = M.optQValue γ`. -/
theorem ae_tendsto_qLearning_optQValue [Finite 𝓢] [MeasurableSingletonClass 𝓢] [Finite 𝓐]
    [Nonempty 𝓐] [MeasurableSingletonClass 𝓐] [IsFiniteMeasure P] {K : ℝ}
    (h : IsAlgEnvSeq O A Y alg (M.env μ) P)
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (Q₀ : 𝓢 × 𝓐 → ℝ)
    (hαm : Adapted h.filtrationAction α) (hα : ∀ t ω p, α t ω p ∈ Set.Icc (0 : ℝ) 1)
    (hα_zero : ∀ t ω p, p ≠ (O t ω, A t ω) → α t ω p = 0)
    (hα_sum : ∀ᵐ ω ∂P, ∀ p, Tendsto (fun T ↦ ∑ t ∈ range T, α t ω p) atTop atTop)
    (hα_sq : ∀ᵐ ω ∂P, ∀ p T, ∑ t ∈ range T, α t ω p ^ 2 ≤ K) :
    ∀ᵐ ω ∂P, Tendsto (fun t ↦ qLearning γ Q₀ O A Y α t ω) atTop (𝓝 (M.optQValue γ)) := by
  have := Fintype.ofFinite 𝓢
  have := Fintype.ofFinite 𝓐
  set Q := qLearning γ Q₀ O A Y α with hQ
  set ℱ := h.filtrationAction
  set B := max ‖Q₀‖ (|C| / (1 - γ))
  -- the optimality operator on action values, a `γ`-Lipschitz map with fixed point `Q*`
  set F : (𝓢 × 𝓐 → ℝ) → 𝓢 × 𝓐 → ℝ := fun y ↦ M.lookahead γ fun s ↦ ⨆ a, y (s, a)
  have hF : LipschitzWith γ F := MDP.lipschitzWith_lookahead_iSup hR
  have hQm : Adapted ℱ Q := adapted_qLearning h hαm
  -- the target `Z t` and its conditional mean `G t`, the operator at the visited pair
  set Z : ℕ → Ω → ℝ := fun t ω ↦ Y t ω + γ * ⨆ a, Q t ω (O (t + 1) ω, a)
  set G : ℕ → Ω → ℝ := fun t ω ↦ F (Q t ω) (O t ω, A t ω)
  have hpair (t : ℕ) : Measurable[ℱ t] fun ω ↦ (O t ω, A t ω) :=
    (h.adapted_obs_filtrationAction t).prodMk (h.adapted_action_filtrationAction t)
  have hGm (t : ℕ) : Measurable[ℱ t] (G t) :=
    @Measurable.eval_index _ _ _ (ℱ t) _ _ _ _ _ _ (hF.continuous.measurable.comp (hQm t)) (hpair t)
  have hGB : ∀ᵐ ω ∂P, ∀ t, |G t ω| ≤ B := (ae_abs_qLearning_le h hγ hR hα).mono fun ω hω t ↦
    (MDP.abs_lookahead_le hR (fun s ↦ abs_ciSup_le fun a ↦ hω t (s, a)) _).trans <|
      (add_le_add_left (le_abs_self C) _).trans (abs_add_mul_max_le hγ)
  have hZ_int (t : ℕ) : Integrable (Z t) P :=
    .of_bound (((measurable_qLearning_target h hαm t).mono (ℱ.le _) le_rfl).aestronglyMeasurable)
      B ((ae_abs_qLearning_target_le h hγ hR hα).mono fun ω hω ↦ (Real.norm_eq_abs _).trans_le
        (hω t))
  have hG_int (t : ℕ) : Integrable (G t) P :=
    .of_bound ((hGm t).mono (ℱ.le _) le_rfl).aestronglyMeasurable B
      (hGB.mono fun ω hω ↦ (Real.norm_eq_abs _).trans_le (hω t))
  -- the noise: the deviation of the target from its conditional mean, at the visited pair
  set w : ℕ → Ω → 𝓢 × 𝓐 → ℝ := fun t ω p ↦ {ω | (O t ω, A t ω) = p}.indicator (Z t - G t) ω
  have hset (t : ℕ) (p : 𝓢 × 𝓐) : MeasurableSet[ℱ t] {ω | (O t ω, A t ω) = p} :=
    hpair t (measurableSet_singleton p)
  refine ae_tendsto_of_norm_sub_div_le_mul (ℱ := ℱ) (w := w) (F := F) (v := 1) (β := γ)
    (A := ‖2 * B‖₊ ^ 2) (B := 0) (C := K) (fun t ω p ↦ ?_) hQm hαm hα hα_sum hα_sq
    (fun t ↦ ?_) (fun t p ↦ ?_) (fun t p ↦ ?_) (fun t p ↦ ?_) (fun _ ↦ one_pos)
    (by exact_mod_cast hγ) (fun y ↦ ?_)
  · -- the recursion
    by_cases hp : p = (O t ω, A t ω)
    · subst hp
      have hw : w t ω (O t ω, A t ω) = Z t ω - G t ω := Set.indicator_of_mem (by simp) _
      rw [hw, hQ, qLearning_succ_apply_self]
      ring
    · rw [hQ, qLearning_succ_apply_of_ne hp, hα_zero t ω p hp, zero_mul, add_zero]
  · -- the noise is measurable at the next round
    exact @Measurable.of_eval _ _ _ (ℱ (t + 1)) _ _ fun p ↦
      ((measurable_qLearning_target h hαm t).sub ((hGm t).mono (ℱ.mono t.le_succ) le_rfl)).indicator
        (ℱ.mono t.le_succ _ (hset t p))
  · -- the noise is integrable
    exact ((hZ_int t).sub (hG_int t)).indicator (ℱ.le t _ (hset t p))
  · -- the noise has conditional mean zero
    filter_upwards [condExp_indicator ((hZ_int t).sub (hG_int t)) (hset t p),
      condExp_sub (hZ_int t) (hG_int t) (ℱ t),
      condExp_feedback_add_mul_iSup_qLearning h hγ hR hαm hα t,
      ae_of_all P (congrFun (condExp_of_stronglyMeasurable (ℱ.le t) (hGm t).stronglyMeasurable
        (hG_int t)))] with ω h1 h2 h3 h4
    refine h1.trans (Set.indicator_apply_eq_zero.2 fun _ ↦ ?_)
    rw [h2, Pi.sub_apply, h3, h4, sub_self]
  · -- the noise is bounded by `2 * B`, hence so is its conditional second moment
    have hle : (fun ω ↦ ‖w t ω p‖ₑ ^ 2) ≤ᵐ[P] fun _ ↦ ((‖2 * B‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
      filter_upwards [ae_abs_qLearning_target_le h hγ hR hα, hGB] with ω hZ hG
      simp only [ENNReal.coe_pow, ← eNorm_eq_nnNorm]
      gcongr
      refine eNorm_le_iff_norm_le.2 ((norm_indicator_le_norm_self (Z t - G t) ω).trans ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Pi.sub_apply, two_mul]
      exact ((abs_sub _ _).trans (add_le_add (hZ t) (hG t))).trans (le_abs_self _)
    filter_upwards [condLExp_mono (mΩ := ℱ t) hle] with ω hω
    rw [condLExp_const (ℱ.le t)] at hω
    simpa using hω
  · -- the operator is a `γ`-contraction towards its fixed point `Q*`
    have hfix : F (M.optQValue γ) = M.optQValue γ := MDP.lookahead_iSup_optQValue hγ hR
    simp only [div_one]
    rw [← dist_eq_norm, ← dist_eq_norm]
    conv_lhs => rw [← hfix]
    exact hF.dist_le_mul y _

end Run

end LMLExplore.ReinforcementLearning
