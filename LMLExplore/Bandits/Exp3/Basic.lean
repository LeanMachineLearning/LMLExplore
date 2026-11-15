/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Real.Sqrt
public import LMLExplore.Bandits.Adversarial.Regret
public import LMLExplore.Bandits.Exp4.IX
public import LMLExplore.MeasureTheory.Integral.Bochner.Basic

/-!
# Exp3

Exp3 [ACFS02], [LS, Algorithm 9] is the weight-based algorithm for adversarial bandits with
finitely many arms `α` that plays at round `t` the exponential weights `P t = softmax (-(η • L̂ t))`
of its cumulative loss estimates `L̂ t = ∑ s < t, Ŷ s`, where `Ŷ s` is the importance-weighted
estimate of the losses `1 - X s` of round `s`, computed from the arm `A s` drawn from `P s` and its
observed reward `X s`: `Ŷ s a = 𝟙{A s = a} (1 - X s) / P s a`. The learning rate `η > 0` is a
parameter. Exp3 ignores the observations of the environment. It is defined as the instance of
Exp4-IX (`LMLExplore.Bandits.exp4IX`) with the experts `α`, expert `b` advising the Dirac mass at
`b` at every observation (`singleAdvice`), the constant learning rate `η` and no implicit
exploration: its weights on the arms are its weights on the experts, and the estimated loss of
expert `b` is `Ŷ s b`.
[LS, Algorithm 9] writes the weights as `softmax (η • Ŝ t)` with the loss-based reward estimates
`Ŝ t = ∑ s < t, (1 - Ŷ s)`, which differ from `-L̂ t` by the constant `t`.

For rewards in `[0, 1]`, its adversarial regret against the reward table `x` satisfies
`R_n(x) ≤ log k / η + η n k / 2`, with `k` the number of arms, and the learning rate
`η = √(2 log k / (n k))` gives `R_n(x) ≤ √(2 n k log k)` [LS, Theorem 11.2]. The proof applies the
pathwise local-norm bound of Exp4-IX to the nonnegative losses `Ŷ s`. The loss-based reward
estimates `X̂ s = 1 - Ŷ s` are conditionally unbiased, and the second-order term
`∑ b, P t b * Ŷ t b ^ 2` has expectation `∑ b, (1 - x t b) ^ 2 ≤ k`.

## Main definitions

* `LMLExplore.Bandits.singleAdvice`: the advice of the experts `α` that each recommend one arm,
  expert `b` advising the Dirac mass at `b` at every observation.
* `LMLExplore.Bandits.exp3 η`: the Exp3 algorithm with learning rate `η`, the instance of Exp4-IX
  with one expert per arm, the constant learning rate `η` and `γ = 0`.

## Main statements

* `exp4IXWeights_single`: with the experts that each recommend one arm, the weights of Exp4-IX on
  the arms are its weights on the experts.
* `exp4IXSum_single_history`: with the experts that each recommend one arm, the cumulative
  estimated loss of expert `b` is the sum of the implicit-exploration estimates of the losses of
  arm `b`.
* `Exp3.sum_lossIwEstimator_sub_le`: the pathwise bound on the estimated regret of Exp3.
* `Exp3.sum_sub_integral_eq_integral_sum_lossIwEstimator_sub`: the regret of Exp3 against an
  arm is the expectation of its estimated regret.
* `Exp3.integrable_sq_div_exp4IXWeights`, `Exp3.integral_sq_div_exp4IXWeights`: the second-order
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

variable {α 𝓞 : Type*} [Fintype α] [DecidableEq α]

section Single

/-- The advice of the experts `α` that each recommend one arm: at every observation, expert `b`
advises the Dirac mass at `b`. Exp3 and Exp3-IX are the instances of Exp4-IX with this advice. -/
noncomputable def singleAdvice : 𝓞 → α → simplex α :=
  fun _ b ↦ ⟨Pi.single b 1, single_mem_simplex b⟩

@[simp]
lemma coe_singleAdvice (o : 𝓞) (b : α) : (singleAdvice o b : α → ℝ) = Pi.single b 1 := (rfl)

@[fun_prop]
lemma measurable_singleAdvice [MeasurableSpace 𝓞] :
    Measurable (singleAdvice : 𝓞 → α → simplex α) :=
  measurable_const

variable {η γ : ℕ → ℝ}

/-- With the experts `α` that each recommend one arm (expert `b` advises the Dirac mass at `b`),
the weights of Exp4-IX on the arms are its weights on the experts, at every observation. -/
@[simp]
lemma exp4IXWeights_single (n : ℕ) (h : Hist 𝓞 α ℝ n) (o : 𝓞) :
    exp4IXWeights singleAdvice η γ n h o = exp4IXExpertWeights singleAdvice η γ n h := by
  rw [exp4IXWeights_def]
  exact (pi_eq_sum_univ' _).symm

/-- With the experts `α` that each recommend one arm, every arm has positive weight in Exp4-IX. -/
lemma exp4IXWeights_single_pos [Nonempty α] (n : ℕ) (h : Hist 𝓞 α ℝ n) (o : 𝓞) (a : α) :
    0 < exp4IXWeights singleAdvice η γ n h o a := by
  rw [exp4IXWeights_single]
  exact exp4IXExpertWeights_pos n h a

/-- With the experts `α` that each recommend one arm, along a sequence of observations `O`, actions
`A` and feedbacks `Y`, the cumulative estimated loss of expert `b` in Exp4-IX after `n` rounds is
the sum over the rounds `t < n` of the implicit-exploration estimates `Ŷ t b` of the losses
`1 - Y t` at the arm `b`. -/
lemma exp4IXSum_single_history {Ω : Type*} (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (b : α) :
    exp4IXSum singleAdvice η γ n (history O A Y n ω) b =
      ∑ t ∈ range n, iwEstimator (fun a ↦
        exp4IXWeights singleAdvice η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω) (1 - Y t ω)
          b := by
  simp [exp4IXSum_history, Finset.sum_apply, single_dotProduct]

end Single

variable {η : ℝ}

section Algorithm

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] [Nonempty α]

/-- **Exp3** with learning rate `η` [LS, Algorithm 9]: Exp4-IX with the experts `α`, expert `b`
advising the Dirac mass at `b` at every observation, the constant learning rate `η` and no
implicit exploration. It draws its action of round `n` from the exponential weights of `-η` times
the cumulative importance-weighted loss estimates computed from the history, and ignores the
observations. -/
noncomputable def exp3 (η : ℝ) : Algorithm 𝓞 α ℝ :=
  exp4IX singleAdvice measurable_singleAdvice (fun _ ↦ η) 0

lemma exp3_def (η : ℝ) :
    exp3 (𝓞 := 𝓞) (α := α) η = exp4IX singleAdvice measurable_singleAdvice (fun _ ↦ η) 0 :=
  (rfl)

end Algorithm

namespace Exp3

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] [Nonempty α]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {env : Environment 𝓞 α ℝ}
  {x : ℕ → α → ℝ} {n : ℕ}

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] in
/-- **Pathwise bound on the estimated regret of Exp3.** Along every sequence of observations `O`,
actions `A` and feedbacks `Y ≤ 1` of the rounds `t < n`, with `P t` the weights of Exp3 at round
`t` and `X̂ t` its loss-based importance-weighted reward estimates, for every arm `a` and `η > 0`,
`∑ t < n, (X̂ t a - Y t) ≤ log k / η + η / 2 * ∑ t < n, (1 - Y t) ^ 2 / P t (A t)`. This is the
local-norm bound of Exp4-IX for the constant learning rate `η` and `γ = 0`. -/
theorem sum_lossIwEstimator_sub_le (hη : 0 < η) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → ℝ) (ω : Ω) (hY : ∀ t < n, Y t ω ≤ 1) (a : α) :
    ∑ t ∈ range n, (lossIwEstimator (exp4IXWeights singleAdvice
        (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) a - Y t ω) ≤
      log (Fintype.card α) / η + η / 2 * ∑ t ∈ range n, (1 - Y t ω) ^ 2 /
        exp4IXWeights singleAdvice (fun _ ↦ η) 0 t
          (history O A Y t ω) (O t ω) (A t ω) := by
  have key := Exp4IX.sum_sum_mul_sub_dotProduct_le
    (adv := singleAdvice) (η := fun _ ↦ η) (γ := 0) O A Y ω
    (fun _ ↦ hη) antitone_const (fun _ ↦ le_rfl) hY a
  -- the regret and second-order terms of the loss estimates in terms of `Y t`
  have h1 : ∀ (p : α → ℝ) (b : α) (y : ℝ), p b ≠ 0 →
      ∑ c, p c * iwEstimator p b (1 - y) c - iwEstimator p b (1 - y) a =
        lossIwEstimator p b y a - y := fun p b y hb ↦ by
    rw [sum_mul_iwEstimator hb, lossIwEstimator_apply]
    ring
  -- with `γ = 0`, the estimates are the importance-weighted estimates for the weights on the arms
  simp only [Pi.zero_apply, add_zero, coe_singleAdvice, single_dotProduct, one_mul,
    sum_mul_iwEstimator_sq, ← Finset.mul_sum] at key
  rwa [Finset.sum_congr rfl fun t _ ↦ h1 _ _ _ (exp4IXWeights_single_pos _ _ _ _).ne'] at key

/-- Along a run of Exp3 whose feedback is the reward `x t (A t)` of its action, the second-order
term `(1 - Y t) ^ 2 / P t (A t)` of round `t` is integrable. -/
lemma integrable_sq_div_exp4IXWeights {t : ℕ} (hY : Y t =ᵐ[P] x t ∘ A t)
    (h : IsAlgEnvSeq O A Y (exp3 η) env P) :
    Integrable (fun ω ↦ (1 - Y t ω) ^ 2 /
      exp4IXWeights singleAdvice (fun _ ↦ η) 0 t
        (history O A Y t ω) (O t ω) (A t ω)) P :=
  have hw := Exp4IX.isAlgEnvSeq_weightAlgorithm h
  (WeightAlgorithm.integrable_div_weights hw t fun b ↦ (1 - x t b) ^ 2).congr
    (comp_feedback_ae_eq hY fun z b y ↦ (1 - y) ^ 2 /
      exp4IXWeights singleAdvice (fun _ ↦ η) 0 t z.1 z.2
        b).symm

/-- Along a run of Exp3 whose feedback is the reward `x t (A t)` of its action, the second-order
term `(1 - Y t) ^ 2 / P t (A t)` of round `t` has expectation `∑ b, (1 - x t b) ^ 2`. -/
lemma integral_sq_div_exp4IXWeights {t : ℕ} (hY : Y t =ᵐ[P] x t ∘ A t)
    (h : IsAlgEnvSeq O A Y (exp3 η) env P) :
    P[fun ω ↦ (1 - Y t ω) ^ 2 /
      exp4IXWeights singleAdvice (fun _ ↦ η) 0 t
        (history O A Y t ω) (O t ω) (A t ω)] = ∑ b, (1 - x t b) ^ 2 := by
  have hw := Exp4IX.isAlgEnvSeq_weightAlgorithm h
  rw [integral_congr_ae (comp_feedback_ae_eq hY fun z b y ↦ (1 - y) ^ 2 /
    exp4IXWeights singleAdvice (fun _ ↦ η) 0 t z.1 z.2 b)]
  exact WeightAlgorithm.integral_div_weights hw t (c := fun b ↦ (1 - x t b) ^ 2)
    (ae_of_all _ fun _ b hb ↦ absurd hb (exp4IXWeights_single_pos _ _ _ b).ne')

/-- **The estimated regret of Exp3 is unbiased.** Along a run of Exp3 whose feedback at the rounds
`t < n` is the reward `x t (A t)` of its action, the regret against every arm `a` is the
expectation of `∑ t < n, (X̂ t a - Y t)`, with `X̂ t` the loss-based importance-weighted reward
estimates of Exp3. -/
theorem sum_sub_integral_eq_integral_sum_lossIwEstimator_sub
    (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t) (h : IsAlgEnvSeq O A Y (exp3 η) env P) (a : α) :
    ∑ t ∈ range n, x t a - P[fun ω ↦ ∑ t ∈ range n, x t (A t ω)] =
      P[fun ω ↦ ∑ t ∈ range n, (lossIwEstimator
        (exp4IXWeights singleAdvice (fun _ ↦ η) 0 t
          (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) a - Y t ω)] := by
  have hw := Exp4IX.isAlgEnvSeq_weightAlgorithm h
  set X : ℕ → Ω → ℝ := fun t ω ↦ lossIwEstimator
    (exp4IXWeights singleAdvice (fun _ ↦ η) 0 t
      (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) a with hX
  have hYint := fun t (ht : t ∈ range n) ↦
    h.integrable_feedback_of_ae_eq (hY t (mem_range.1 ht))
  have hXint : ∀ t ∈ range n, Integrable (X t) P := fun t ht ↦
    WeightAlgorithm.integrable_lossIwEstimator hw (hY t (mem_range.1 ht)) a
  rw [integral_finsetSum (f := fun t ω ↦ X t ω - Y t ω) _
      fun t ht ↦ (hXint t ht).sub (hYint t ht),
    integral_finsetSum (f := fun t ω ↦ x t (A t ω)) _ fun t ht ↦
      (hYint t ht).congr (hY t (mem_range.1 ht)), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  have hXt : P[X t] = x t a := WeightAlgorithm.integral_lossIwEstimator hw (hY t (mem_range.1 ht))
    (ae_of_all _ fun _ ↦ exp4IXWeights_single_pos _ _ _ _)
  rw [integral_sub (hXint t ht) (hYint t ht), hXt, integral_congr_ae (hY t (mem_range.1 ht)),
    Function.comp_def]

/-- **Regret of Exp3.** Along a run of Exp3 with learning rate `η > 0` whose feedback at every
round `t < n` is the reward `x t (A t) ∈ [0, 1]` of its action, the adversarial regret after `n`
rounds is at most `log k / η + η n k / 2`, with `k` the number of arms. -/
theorem advRegret_le (hη : 0 < η) (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t)
    (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1) (h : IsAlgEnvSeq O A Y (exp3 η) env P) :
    advRegret x A P n ≤ log (Fintype.card α) / η + η * n * Fintype.card α / 2 := by
  have hw := Exp4IX.isAlgEnvSeq_weightAlgorithm h
  set V : ℕ → Ω → ℝ := fun t ω ↦ (1 - Y t ω) ^ 2 /
    exp4IXWeights singleAdvice (fun _ ↦ η) 0 t
      (history O A Y t ω) (O t ω) (A t ω)
  have hVint : ∀ t ∈ range n, Integrable (V t) P := fun t ht ↦
    integrable_sq_div_exp4IXWeights (hY t (mem_range.1 ht)) h
  have hYle : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ≤ 1 := ae_feedback_le_one hY fun t ht a ↦ (hx t ht a).2
  have hle : ∑ t ∈ range n, P[V t] ≤ (n * Fintype.card α : ℝ) :=
    WeightAlgorithm.sum_integral_one_sub_sq_div_weights_le hw (ae_feedback_mem_Icc hY hx)
  refine advRegret_le_iff.2 fun a ↦ ?_
  rw [sum_sub_integral_eq_integral_sum_lossIwEstimator_sub hY h a]
  refine (integral_sum_le_add_mul_of_ae_le (B := log (Fintype.card α) / η) (c := η / 2)
    (by positivity) (fun t ht ↦
      (WeightAlgorithm.integrable_lossIwEstimator hw (hY t (mem_range.1 ht)) a).sub
        (h.integrable_feedback_of_ae_eq (hY t (mem_range.1 ht)))) hVint hle ?_).trans_eq (by ring)
  filter_upwards [hYle] with ω hω
  exact sum_lossIwEstimator_sub_le hη O A Y ω hω a

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
  refine (advRegret_le hη0 hY hx h).trans (le_of_eq ?_)
  rw [mul_assoc η, mul_assoc 2 (n : ℝ)]
  exact div_sqrt_add_sqrt_mul_div_two _ hm.le

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
