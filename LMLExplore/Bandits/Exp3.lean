/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.AdversarialRegret
public import LMLExplore.Bandits.ImportanceWeighted
public import LMLExplore.OnlineLearning.ExponentialWeights

/-!
# Exp3

Exp3 [ACFS02], [LS, Algorithm 9] is the weight-based algorithm for adversarial bandits with
finitely many arms `α` that plays at round `t` the exponential weights `P t = softmax (η • Ŝ t)`
of its cumulative reward estimates `Ŝ t = ∑ s < t, X̂ s`, where `X̂ s` is the loss-based
importance-weighted estimate of the rewards of round `s`, computed from the arm `A s` drawn from
`P s` and its observed reward `X s`: `X̂ s a = 1 - 𝟙{A s = a} (1 - X s) / P s a`. The
learning rate `η > 0` is a parameter. Exp3 ignores the observations of the environment.

For rewards in `[0, 1]`, its adversarial regret against the reward table `x` satisfies
`R_n(x) ≤ log k / η + η n k / 2`, with `k` the number of arms, and the learning rate
`η = √(2 log k / (n k))` gives `R_n(x) ≤ √(2 n k log k)` [LS, Theorem 11.2]. The proof writes the
reward estimates as `X̂ s = 1 - Ŷ s` with the importance-weighted estimates `Ŷ s` of the losses
`1 - x s`, so that `P t` are the exponential weights of `-η` times the cumulative loss estimates,
and applies the local-norm bound of exponential weights to the nonnegative losses `Ŷ s`. The
estimates are conditionally unbiased, and the second-order term `∑ b, P t b * Ŷ t b ^ 2` has
expectation `∑ b, (1 - x t b) ^ 2 ≤ k`.

## Main definitions

* `LMLExplore.Bandits.exp3Sum η n h`: the cumulative reward estimates `Ŝ n` of Exp3, computed
  from the history `h` of the first `n` rounds.
* `LMLExplore.Bandits.exp3Weights η n h`: the weights `P n = softmax (η • Ŝ n)` of Exp3 at
  round `n`.
* `LMLExplore.Bandits.exp3 η`: the Exp3 algorithm with learning rate `η`.

## Main statements

* `exp3Weights_history_eq`: along every sequence of actions and feedbacks, the weights of Exp3
  are the exponential weights of `-η` times the cumulative importance-weighted loss estimates.
* `Exp3.sum_lossIwEstimator_sub_le`: the pathwise bound on the estimated regret of Exp3.
* `Exp3.sum_sub_integral_eq_integral_sum_lossIwEstimator_sub`: the regret of Exp3 against an
  arm is the expectation of its estimated regret.
* `Exp3.integrable_sq_div_exp3Weights`, `Exp3.integral_sq_div_exp3Weights`: the second-order
  term `(1 - Y t) ^ 2 / P t (A t)` of round `t` has expectation `∑ b, (1 - x t b) ^ 2`.
* `Exp3.advRegret_le`: for a run of Exp3 whose feedback is the reward `x t (A t)` of its action,
  with rewards in `[0, 1]`, `R_n(x) ≤ log k / η + η n k / 2`.
* `exp3_advRegret_le`: the same bound for runs against LML's `Environment.evalSeq x _`.
* `Exp3.advRegret_le_sqrt`: [LS, Theorem 11.2]. With `η = √(2 log k / (n k))`,
  `R_n(x) ≤ √(2 n k log k)`.
* `exp3_advRegret_le_sqrt`: the same bound for runs against LML's `Environment.evalSeq x _`.

## References

* [ACFS02] P. Auer, N. Cesa-Bianchi, Y. Freund and R. E. Schapire, *The nonstochastic multiarmed
  bandit problem*, SIAM J. Comput. 32(1), 2002.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real LMLExplore.OnlineLearning

namespace LMLExplore.Bandits

variable {α 𝓞 : Type*} [Fintype α] [DecidableEq α] {η : ℝ}

section Weights

/-- The cumulative reward estimates of Exp3 with learning rate `η`, computed from the history `h`
of the first `n` rounds: `∑ s < n, X̂ s` with `X̂ s = lossIwEstimator (P s) (A s) (X s)` the
loss-based importance-weighted estimate of round `s`, for the action `A s` and the reward `X s`
of round `s` of `h` and the weights `P s = softmax (η • ∑ r < s, X̂ r)` of round `s`. -/
noncomputable def exp3Sum (η : ℝ) : (n : ℕ) → Hist 𝓞 α ℝ n → α → ℝ
  | 0, _ => 0
  | n + 1, h => exp3Sum η n (Fin.init h) +
      lossIwEstimator (softmax (η • exp3Sum η n (Fin.init h))) (h (Fin.last n)).action
        (h (Fin.last n)).feedback

/-- The weights of Exp3 with learning rate `η` after the history `h` of the first `n` rounds: the
softmax of `η` times the cumulative reward estimates `exp3Sum η n h`. -/
noncomputable def exp3Weights (η : ℝ) (n : ℕ) (h : Hist 𝓞 α ℝ n) : α → ℝ :=
  softmax (η • exp3Sum η n h)

lemma exp3Weights_def (η : ℝ) (n : ℕ) (h : Hist 𝓞 α ℝ n) :
    exp3Weights η n h = softmax (η • exp3Sum η n h) := (rfl)

@[simp]
lemma exp3Sum_zero (h : Hist 𝓞 α ℝ 0) : exp3Sum η 0 h = 0 := by
  rw [exp3Sum]

lemma exp3Sum_succ (n : ℕ) (h : Hist 𝓞 α ℝ (n + 1)) :
    exp3Sum η (n + 1) h = exp3Sum η n (Fin.init h) +
      lossIwEstimator (exp3Weights η n (Fin.init h)) (h (Fin.last n)).action
        (h (Fin.last n)).feedback := by
  rw [exp3Sum, exp3Weights_def]

/-- The first weights of Exp3 are uniform. -/
@[simp]
lemma exp3Weights_zero (h : Hist 𝓞 α ℝ 0) :
    exp3Weights η 0 h = fun _ ↦ (Fintype.card α : ℝ)⁻¹ := by
  simp [exp3Weights_def]

lemma exp3Weights_pos [Nonempty α] (n : ℕ) (h : Hist 𝓞 α ℝ n) (a : α) :
    0 < exp3Weights η n h a :=
  softmax_pos _ a

lemma exp3Weights_mem_simplex [Nonempty α] (n : ℕ) (h : Hist 𝓞 α ℝ n) :
    exp3Weights η n h ∈ simplex α :=
  softmax_mem_simplex _

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞]

@[fun_prop]
lemma measurable_exp3Sum (η : ℝ) (n : ℕ) : Measurable (exp3Sum (𝓞 := 𝓞) (α := α) η n) := by
  induction n with
  | zero =>
    rw [funext exp3Sum_zero]
    exact measurable_const
  | succ n ih =>
    have hinit : Measurable fun h : Hist 𝓞 α ℝ (n + 1) ↦ Fin.init h :=
      Measurable.of_eval fun i ↦ measurable_pi_apply _
    have hS := ih.comp hinit
    have hlast : Measurable fun h : Hist 𝓞 α ℝ (n + 1) ↦ h (Fin.last n) := measurable_pi_apply _
    rw [funext (exp3Sum_succ n)]
    simp_rw [exp3Weights_def]
    exact hS.add (measurable_lossIwEstimator.comp
      ((measurable_softmax.comp (hS.const_smul η)).prodMk
        ((Round.measurable_action.comp hlast).prodMk (Round.measurable_feedback.comp hlast))))

@[fun_prop]
lemma measurable_exp3Weights (η : ℝ) (n : ℕ) :
    Measurable (exp3Weights (𝓞 := 𝓞) (α := α) η n) :=
  measurable_softmax.comp ((measurable_exp3Sum η n).const_smul η)

end Weights

section Algorithm

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] [Nonempty α]

/-- **Exp3** with learning rate `η` [LS, Algorithm 9]: the weight-based algorithm that draws its
action of round `n` from the weights `exp3Weights η n h`, the exponential weights of `η` times
the cumulative loss-based importance-weighted reward estimates computed from the history `h`.
It ignores the observations. -/
noncomputable def exp3 (η : ℝ) : Algorithm 𝓞 α ℝ :=
  weightAlgorithm (fun n x ↦ exp3Weights η n x.1)
    (fun n a ↦ (measurable_pi_apply a).comp ((measurable_exp3Weights η n).comp measurable_fst))
    (fun n x ↦ exp3Weights_mem_simplex n x.1)

lemma exp3_def (η : ℝ) :
    exp3 (𝓞 := 𝓞) (α := α) η = weightAlgorithm (fun n x ↦ exp3Weights η n x.1)
      (fun n a ↦ (measurable_pi_apply a).comp ((measurable_exp3Weights η n).comp measurable_fst))
      (fun n x ↦ exp3Weights_mem_simplex n x.1) := (rfl)

/-- The policy of Exp3 at round `n` draws its action from the weights `exp3Weights η n h` of the
history `h`. -/
@[simp]
lemma exp3_policy_apply (n : ℕ) (x : Hist 𝓞 α ℝ n × 𝓞) :
    (exp3 η).policy n x = weightedMeasure (exp3Weights η n x.1) := by
  rw [exp3_def, weightAlgorithm_policy, weightKernel_apply]

end Algorithm

section History

variable {Ω : Type*} (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ)

/-- Along a sequence of observations `O`, actions `A` and feedbacks `Y`, the cumulative reward
estimates of Exp3 after `n` rounds are the sums of the loss-based importance-weighted estimates of
the rounds `t < n`. -/
lemma exp3Sum_history (n : ℕ) (ω : Ω) :
    exp3Sum η n (history O A Y n ω) = ∑ t ∈ range n,
      lossIwEstimator (exp3Weights η t (history O A Y t ω)) (A t ω) (Y t ω) := by
  induction n with
  | zero => simp
  | succ n ih => simp [exp3Sum_succ, Finset.sum_range_succ, ih, history_apply]

/-- **Exp3 as exponential weights on losses.** Along a sequence of observations `O`, actions `A`
and feedbacks `Y`, the weights of Exp3 at round `n` are the exponential weights of `-η` times the
cumulative importance-weighted estimates of the losses `1 - Y t`, since the loss-based reward
estimates are one minus these loss estimates. -/
lemma exp3Weights_history_eq (n : ℕ) (ω : Ω) :
    exp3Weights η n (history O A Y n ω) = softmax (-(η • ∑ t ∈ range n,
      iwEstimator (exp3Weights η t (history O A Y t ω)) (A t ω) (1 - Y t ω))) := by
  rw [exp3Weights_def, exp3Sum_history, ← softmax_add_const _ (-(η * n))]
  congr 1
  funext a
  simp only [lossIwEstimator_def, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one,
    Pi.smul_apply, Pi.sub_apply, Pi.natCast_apply, Finset.sum_apply, smul_eq_mul, Pi.neg_apply]
  ring

end History

namespace Exp3

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] [Nonempty α]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {env : Environment 𝓞 α ℝ}
  {x : ℕ → α → ℝ} {n : ℕ}

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] in
/-- **Pathwise bound on the estimated regret of Exp3.** Along every sequence of actions `A` and
feedbacks `Y ≤ 1` of the rounds `t < n`, with `P t` the weights of Exp3 at round `t` and `X̂ t` its
loss-based importance-weighted reward estimates, for every arm `a` and `η > 0`,
`∑ t < n, (X̂ t a - Y t) ≤ log k / η + η / 2 * ∑ t < n, (1 - Y t) ^ 2 / P t (A t)`. -/
theorem sum_lossIwEstimator_sub_le (hη : 0 < η) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → ℝ) (ω : Ω) (hY : ∀ t < n, Y t ω ≤ 1) (a : α) :
    ∑ t ∈ range n,
        (lossIwEstimator (exp3Weights η t (history O A Y t ω)) (A t ω) (Y t ω) a - Y t ω) ≤
      log (Fintype.card α) / η + η / 2 *
        ∑ t ∈ range n, (1 - Y t ω) ^ 2 / exp3Weights η t (history O A Y t ω) (A t ω) := by
  -- the exponential-weights bound for the nonnegative loss estimates
  set p : ℕ → α → ℝ := fun t ↦ exp3Weights η t (history O A Y t ω) with hp
  set y : ℕ → α → ℝ := fun t ↦ iwEstimator (p t) (A t ω) (1 - Y t ω) with hy
  have hy0 : ∀ t < n, ∀ b, 0 ≤ y t b := fun t ht b ↦
    iwEstimator_nonneg (exp3Weights_pos _ _ _).le (sub_nonneg.2 (hY t ht))
  have key := softmax_regret_le hη hy0 a
  have hpw : ∀ t, softmax (-(η • ∑ s ∈ range t, y s)) = p t := fun t ↦
    (exp3Weights_history_eq O A Y t ω).symm
  simp only [hpw] at key
  -- the regret and second-order terms of the losses `y t` in terms of `Y t`
  have h1 : ∀ t, ∑ b, p t b * y t b - y t a =
      lossIwEstimator (p t) (A t ω) (Y t ω) a - Y t ω := fun t ↦ by
    rw [hy, sum_mul_iwEstimator (exp3Weights_pos _ _ _).ne', lossIwEstimator_apply]
    ring
  have h2 : ∀ t, ∑ b, p t b * y t b ^ 2 = (1 - Y t ω) ^ 2 / p t (A t ω) := fun t ↦
    sum_mul_iwEstimator_sq
  simp only [h1, h2] at key
  exact key

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] [Nonempty α]
  [IsProbabilityMeasure P] in
private lemma sq_div_exp3Weights_ae_eq {t : ℕ} (hY : Y t =ᵐ[P] x t ∘ A t) :
    (fun ω ↦ (1 - Y t ω) ^ 2 / exp3Weights η t (history O A Y t ω) (A t ω)) =ᵐ[P]
      fun ω ↦ (1 - x t (A t ω)) ^ 2 / exp3Weights η t (history O A Y t ω) (A t ω) := by
  filter_upwards [hY] with ω hω
  rw [hω, Function.comp_apply]

/-- Along a run of Exp3 whose feedback is the reward `x t (A t)` of its action, the second-order
term `(1 - Y t) ^ 2 / P t (A t)` of round `t` is integrable. -/
lemma integrable_sq_div_exp3Weights {t : ℕ} (hY : Y t =ᵐ[P] x t ∘ A t)
    (h : IsAlgEnvSeq O A Y (exp3 η) env P) :
    Integrable (fun ω ↦ (1 - Y t ω) ^ 2 / exp3Weights η t (history O A Y t ω) (A t ω)) P :=
  (WeightAlgorithm.integrable_div_weights h t fun b ↦ (1 - x t b) ^ 2).congr
    (sq_div_exp3Weights_ae_eq hY).symm

/-- Along a run of Exp3 whose feedback is the reward `x t (A t)` of its action, the second-order
term `(1 - Y t) ^ 2 / P t (A t)` of round `t` has expectation `∑ b, (1 - x t b) ^ 2`. -/
lemma integral_sq_div_exp3Weights {t : ℕ} (hY : Y t =ᵐ[P] x t ∘ A t)
    (h : IsAlgEnvSeq O A Y (exp3 η) env P) :
    P[fun ω ↦ (1 - Y t ω) ^ 2 / exp3Weights η t (history O A Y t ω) (A t ω)] =
      ∑ b, (1 - x t b) ^ 2 := by
  rw [integral_congr_ae (sq_div_exp3Weights_ae_eq hY)]
  exact WeightAlgorithm.integral_div_weights h t (c := fun b ↦ (1 - x t b) ^ 2)
    (ae_of_all _ fun _ b hb ↦ absurd hb (exp3Weights_pos _ _ b).ne')

/-- **The estimated regret of Exp3 is unbiased.** Along a run of Exp3 whose feedback at the rounds
`t < n` is the reward `x t (A t)` of its action, the regret against every arm `a` is the
expectation of `∑ t < n, (X̂ t a - Y t)`, with `X̂ t` the loss-based importance-weighted reward
estimates of Exp3. -/
theorem sum_sub_integral_eq_integral_sum_lossIwEstimator_sub
    (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t) (h : IsAlgEnvSeq O A Y (exp3 η) env P) (a : α) :
    ∑ t ∈ range n, x t a - P[fun ω ↦ ∑ t ∈ range n, x t (A t ω)] =
      P[fun ω ↦ ∑ t ∈ range n,
        (lossIwEstimator (exp3Weights η t (history O A Y t ω)) (A t ω) (Y t ω) a - Y t ω)] := by
  have hYint := fun t (ht : t ∈ range n) ↦
    h.integrable_feedback_of_ae_eq (hY t (mem_range.1 ht))
  have hXint : ∀ t ∈ range n, Integrable (fun ω ↦
      lossIwEstimator (exp3Weights η t (history O A Y t ω)) (A t ω) (Y t ω) a) P := fun t ht ↦
    WeightAlgorithm.integrable_lossIwEstimator h (hY t (mem_range.1 ht)) a
  rw [integral_finsetSum (f := fun t ω ↦
      lossIwEstimator (exp3Weights η t (history O A Y t ω)) (A t ω) (Y t ω) a - Y t ω) _
      fun t ht ↦ (hXint t ht).sub (hYint t ht),
    integral_finsetSum (f := fun t ω ↦ x t (A t ω)) _ fun t ht ↦
      (hYint t ht).congr (hY t (mem_range.1 ht)), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  have hXt : P[fun ω ↦ lossIwEstimator (exp3Weights η t (history O A Y t ω)) (A t ω) (Y t ω) a] =
      x t a := WeightAlgorithm.integral_lossIwEstimator h (hY t (mem_range.1 ht))
        (ae_of_all _ fun _ ↦ exp3Weights_pos _ _ _)
  rw [integral_sub (hXint t ht) (hYint t ht), hXt, integral_congr_ae (hY t (mem_range.1 ht)),
    Function.comp_def]

/-- **Regret of Exp3.** Along a run of Exp3 with learning rate `η > 0` whose feedback at every
round `t < n` is the reward `x t (A t) ∈ [0, 1]` of its action, the adversarial regret after `n`
rounds is at most `log k / η + η n k / 2`, with `k` the number of arms. -/
theorem advRegret_le (hη : 0 < η) (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t)
    (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1) (h : IsAlgEnvSeq O A Y (exp3 η) env P) :
    advRegret x A P n ≤ log (Fintype.card α) / η + η * n * Fintype.card α / 2 := by
  set V : ℕ → Ω → ℝ := fun t ω ↦
    (1 - Y t ω) ^ 2 / exp3Weights η t (history O A Y t ω) (A t ω) with hV
  have hVint : ∀ t ∈ range n, Integrable (V t) P := fun t ht ↦
    integrable_sq_div_exp3Weights (hY t (mem_range.1 ht)) h
  have hYle : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ≤ 1 := by
    refine ae_all_iff.2 fun t ↦ ?_
    by_cases ht : t < n
    · filter_upwards [hY t ht] with ω hω _
      rw [hω]
      exact (hx t ht _).2
    · exact ae_of_all _ fun _ ht' ↦ absurd ht' ht
  -- `∑ t < n, E[V t] ≤ n k`, as `(1 - x t b) ^ 2 ≤ 1`
  have hle : ∑ t ∈ range n, P[V t] ≤ (n * Fintype.card α : ℝ) := by
    calc ∑ t ∈ range n, P[V t]
    _ = ∑ t ∈ range n, ∑ b, (1 - x t b) ^ 2 := Finset.sum_congr rfl fun t ht ↦
        integral_sq_div_exp3Weights (hY t (mem_range.1 ht)) h
    _ ≤ ∑ t ∈ range n, ∑ _b : α, (1 : ℝ) := Finset.sum_le_sum fun t ht ↦
        Finset.sum_le_sum fun b _ ↦ by
          obtain ⟨h0, h1⟩ := hx t (mem_range.1 ht) b
          nlinarith
    _ = n * Fintype.card α := by simp
  refine advRegret_le_iff.2 fun a ↦ ?_
  rw [sum_sub_integral_eq_integral_sum_lossIwEstimator_sub hY h a]
  calc P[fun ω ↦ ∑ t ∈ range n,
        (lossIwEstimator (exp3Weights η t (history O A Y t ω)) (A t ω) (Y t ω) a - Y t ω)]
  _ ≤ P[fun ω ↦ log (Fintype.card α) / η + η / 2 * ∑ t ∈ range n, V t ω] := by
      refine integral_mono_ae (integrable_finsetSum _ fun t ht ↦
        (WeightAlgorithm.integrable_lossIwEstimator h (hY t (mem_range.1 ht)) a).sub
          (h.integrable_feedback_of_ae_eq (hY t (mem_range.1 ht))))
        ((integrable_const _).add ((integrable_finsetSum _ hVint).const_mul _)) ?_
      filter_upwards [hYle] with ω hω
      exact sum_lossIwEstimator_sub_le hη O A Y ω hω a
  _ = log (Fintype.card α) / η + η / 2 * ∑ t ∈ range n, P[V t] := by
      rw [integral_add (integrable_const _) ((integrable_finsetSum _ hVint).const_mul _),
        integral_const_mul, integral_finsetSum _ hVint, integral_const, probReal_univ,
        one_smul]
  _ ≤ log (Fintype.card α) / η + η * n * Fintype.card α / 2 := by
      have := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ η / 2)
      linarith

/-- **Regret of Exp3** [LS, Theorem 11.2]: along a run of Exp3 with learning rate
`η = √(2 log k / (n k))` whose feedback at every round `t < n` is the reward `x t (A t) ∈ [0, 1]`
of its action, the adversarial regret after `n` rounds is at most `√(2 n k log k)`, with `k` the
number of arms. -/
theorem advRegret_le_sqrt (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t)
    (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3 √(2 * log (Fintype.card α) / (n * Fintype.card α))) env P) :
    advRegret x A P n ≤ √(2 * n * Fintype.card α * log (Fintype.card α)) := by
  set k : ℝ := (Fintype.card α : ℝ) with hk
  have hk1 : (1 : ℝ) ≤ k := by
    rw [hk, Nat.one_le_cast]
    exact Fintype.card_pos
  -- with one arm or no round, the regret is zero
  rcases hk1.eq_or_lt with hk1 | hk1
  · have hcard : Fintype.card α ≤ 1 := by
      rw [hk] at hk1
      exact_mod_cast hk1.ge
    have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.1 hcard
    rw [advRegret_of_subsingleton]
    positivity
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [advRegret_def]
  have hL : 0 < log k := log_pos hk1
  have hm : 0 < n * k := mul_pos (by exact_mod_cast hn) (by linarith)
  set η := √(2 * log k / (n * k)) with hη
  have hη0 : 0 < η := sqrt_pos.2 (by positivity)
  -- with `η ^ 2 = 2 log k / (n k)`, both terms of the bound are `η n k / 2`
  have hηsq : η ^ 2 = 2 * log k / (n * k) := sq_sqrt (by positivity)
  refine (advRegret_le hη0 hY hx h).trans (le_of_eq ?_)
  have hsq : √(2 * n * k * log k) = η * (n * k) := by
    rw [← sqrt_sq (by positivity : 0 ≤ η * (n * k)), mul_pow, hηsq]
    congr 1
    field_simp
  -- `log k / η = η n k / 2`, from `η ^ 2 = 2 log k / (n k)`
  have hlog : log k / η = η * (n * k) / 2 := by
    rw [div_eq_iff hη0.ne']
    rw [eq_div_iff hm.ne'] at hηsq
    linear_combination -hηsq / 2
  rw [hsq, hlog]
  ring

end Exp3

section OnlineEvalEnv

variable [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {x : ℕ → α → ℝ}
  {hxm : ∀ t, Measurable (x t)} {n : ℕ}

/-- **Regret of Exp3** against an oblivious adversary: along a run of Exp3 with learning rate
`η > 0` against LML's evaluation environment `Environment.evalSeq x _` with rewards in `[0, 1]` at
the rounds `t < n`, the adversarial regret after `n` rounds is at most `log k / η + η n k / 2`. -/
theorem exp3_advRegret_le (hη : 0 < η) (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3 η) (Environment.evalSeq x hxm) P) :
    advRegret x A P n ≤ log (Fintype.card α) / η + η * n * Fintype.card α / 2 :=
  Exp3.advRegret_le hη (fun t _ ↦ h.feedback_ae_eq_evalSeq t) hx h

/-- **Regret of Exp3** [LS, Theorem 11.2]: along a run of Exp3 with learning rate
`η = √(2 log k / (n k))` against LML's evaluation environment `Environment.evalSeq x _` with rewards
in `[0, 1]` at the rounds `t < n`, the adversarial regret after `n` rounds is at most
`√(2 n k log k)`, with `k` the number of arms. -/
theorem exp3_advRegret_le_sqrt (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y
      (exp3 √(2 * log (Fintype.card α) / (n * Fintype.card α))) (Environment.evalSeq x hxm) P) :
    advRegret x A P n ≤ √(2 * n * Fintype.card α * log (Fintype.card α)) :=
  Exp3.advRegret_le_sqrt (fun t _ ↦ h.feedback_ae_eq_evalSeq t) hx h

end OnlineEvalEnv

end LMLExplore.Bandits
