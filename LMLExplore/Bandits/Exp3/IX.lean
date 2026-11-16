/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.Exp3.Basic

/-!
# Exp3-IX

Exp3-IX [Neu15], [LS, Algorithm 10] is the weight-based algorithm for adversarial bandits with
finitely many arms `α` that plays at round `t` the exponential weights
`P t = softmax (-(η t • L̂ t))` of its cumulative loss estimates `L̂ t = ∑ s < t, Ŷ s`, where the
estimates of the losses of round `s` are biased by an implicit-exploration parameter `γ s ≥ 0`
[LS, (12.4)]: `Ŷ s a = 𝟙{A s = a} (1 - X s) / (P s a + γ s)`, for the arm `A s` drawn from `P s`
and its observed reward `X s`. This is the importance-weighted estimate of the loss `1 - X s`
for the weights `P s + γ s`. The learning rates `η t` and the implicit-exploration parameters
`γ t` are sequences fixed in advance; [LS] uses constant sequences, tuned for the horizon. With
a constant learning rate and `γ = 0` it is Exp3. Both are defined as instances of Exp4-IX
(`LMLExplore.Bandits.exp4IX`), with the experts `α` that each recommend one arm.

Exp3-IX has high-probability regret bounds against every environment whose feedback is in
`[0, 1]`: an adaptive adversary, which includes oblivious reward tables and stochastic bandits.
Write `m t a = env.means O A Y a t` for the conditional mean of the reward of arm `a` at round
`t` given the past, `L t a = ∑ s < t, (1 - m s a)` for the cumulative losses of these means and
`R̂_n = max_a ∑ t < n, (m t a - Y t)` for the random regret. For nonincreasing sequences `η t > 0`
and `γ t ≥ 0` with `γ (n - 1) > 0`, the analysis of [LS, §12.2] bounds the regret against every
arm `a` by `log k / η (n - 1) + ∑ t < n, (γ t + η t / 2) ∑ b, Ŷ t b + (L̂ n a - L n a)`, with `k`
the number of arms: this combines the local-norm bound of exponential weights with the bias
identity `(1 - X t) - ⟨P t, Ŷ t⟩ = γ t ∑ b, Ŷ t b` [LS, Lemma 12.4]. The deviations
`L̂ n a - L n a` and the weighted deviations `∑ t < n, w t ∑ b, (Ŷ t b - (1 - m t b))`, for
weights `w t ∈ [0, 1]`, are at most `c = log ((k + 1) / δ) / (2 γ (n - 1))` with probability at
least `1 - δ` [LS, Lemma 12.3], by the concentration of implicit-exploration estimates around the
conditional means [LS, Lemma 12.2; Neu15, Lemma 1], which holds against adaptive adversaries. The
weights `w t = (γ t + η t / 2) / (γ 0 + η 0 / 2)` then bound the random regret by
`log k / η (n - 1) + k ∑ t < n, (γ t + η t / 2) + (γ 0 + η 0 / 2 + 1) c` with probability at
least `1 - δ`. For constant rates `η` and `γ = η / 2` this is
`(log k + log ((k + 1) / δ)) / η + η n k + log ((k + 1) / δ)`; with
`η = √(2 log (k + 1) / (n k))`, the random regret is at most
`√(8 n k log (k + 1)) + √(n k / (2 log (k + 1))) log (1 / δ) + log ((k + 1) / δ)`
with probability at least `1 - δ`, and the confidence-dependent learning rate
`η = √((log k + log ((k + 1) / δ)) / (n k))` improves this to
`2 √((2 log (k + 1) + log (1 / δ)) n k) + log ((k + 1) / δ)` [LS, Theorem 12.1]. [LS] states
these bounds for an oblivious reward table `x`, where `m t a = x t a` and the random regret is
`max_a ∑ t < n, (x t a - x t (A t))`; they are the corollaries for LML's `Environment.evalSeq x _`.

## Main definitions

* `LMLExplore.Bandits.exp3IX η γ`: the Exp3-IX algorithm with learning rates `η t` and
  implicit-exploration parameters `γ t`, the instance of Exp4-IX with one expert per arm. Its
  cumulative loss estimates `L̂ n` are the cumulative estimated losses `exp4IXSum` of the experts,
  and its weights `P n` are the weights `exp4IXWeights` of Exp4-IX on the arms.

## Main statements

* `exp3IX_eq_exp3`: Exp3-IX with a constant learning rate and `γ = 0` is Exp3.
* `Exp3IX.sum_sub_sum_mul_eq_sum_mul_sum`: [LS, Lemma 12.4], the bias of the loss estimates.
* `Exp3IX.sum_sub_exp4IXSum_le`: the pathwise bound on the estimated regret of Exp3-IX.
* `Exp3IX.measure_le_sum_mul_sum_mul_iwEstimator_sub_le`: the concentration of the deviations
  of the loss estimates from the losses of the conditional means, weighted by `v a ∈ [0, 1]` on
  the arms and `w t ∈ [0, 1]` on the rounds.
* `Exp3IX.measure_le_exp4IXSum_sub_le`, `Exp3IX.measure_le_sum_exp4IXSum_sub_le`: the
  deviations of the loss estimates of one arm and of their sum over the arms [LS, (12.9), (12.8)].
* `Exp3IX.measure_le_sum_mul_sum_iwEstimator_sub_le`: the deviations of the sums of the estimates
  of the rounds, weighted by `w t ∈ [0, 1]`.
* `Exp3IX.measure_exists_le_exp4IXSum_sub_union_le`: [LS, Lemma 12.3], with weighted rounds.
* `Exp3IX.measure_le_randomRegret_le`: the high-probability bound on the random regret of
  Exp3-IX for nonincreasing sequences `η` and `γ`.
* `Exp3IX.measure_div_add_mul_add_le_randomRegret_le`: the same bound for constant rates `η` and
  `γ = η / 2`, in the form `L / η + η n k + log ((k + 1) / δ)` from which both bounds of
  [LS, Theorem 12.1] follow.
* `Exp3IX.measure_sqrt_add_le_randomRegret_le`,
  `Exp3IX.measure_two_mul_sqrt_add_le_randomRegret_le`: the two bounds of [LS, Theorem 12.1],
  against an adaptive adversary.
* `exp3IX_measure_exists_sqrt_le_sum_sub_le`, `exp3IX_measure_exists_two_mul_sqrt_le_sum_sub_le`:
  the same bounds for runs against LML's `Environment.evalSeq x _`, for the regret
  `∑ t < n, (x t a - x t (A t))` against the arms.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
* [Neu15] G. Neu, *Explore no more: improved high-probability regret bounds for non-stochastic
  bandits*, NeurIPS 2015.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real LMLExplore.OnlineLearning

namespace LMLExplore.Bandits

variable {α 𝓞 : Type*} [Fintype α] [DecidableEq α]

section Algorithm

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] [Nonempty α]

/-- **Exp3-IX** with learning rates `η` and implicit-exploration parameters `γ`
[LS, Algorithm 10]: Exp4-IX with the experts `α`, expert `b` advising the Dirac mass at `b` at
every observation. It draws its action of round `n` from the exponential weights of `-η n` times
the cumulative implicit-exploration loss estimates computed from the history, and ignores the
observations. [LS] uses constant sequences `η` and `γ`. -/
noncomputable def exp3IX (η γ : ℕ → ℝ) : Algorithm 𝓞 α ℝ :=
  exp4IX singleAdvice measurable_singleAdvice η γ

lemma exp3IX_def (η γ : ℕ → ℝ) :
    exp3IX (𝓞 := 𝓞) (α := α) η γ = exp4IX singleAdvice measurable_singleAdvice η γ := (rfl)

/-- Exp3-IX with a constant learning rate `η` and `γ = 0` is Exp3. -/
lemma exp3IX_eq_exp3 (η : ℝ) : exp3IX (𝓞 := 𝓞) (α := α) (fun _ ↦ η) 0 = exp3 η := by
  rw [exp3IX_def, exp3_def]

end Algorithm

namespace Exp3IX

/-! ### Pathwise bounds -/

section Pathwise

variable [Nonempty α] {Ω : Type*} (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ) (ω : Ω)
  {η γ : ℕ → ℝ} {n : ℕ}

/-- **Bias of the loss estimates of Exp3-IX** [LS, Lemma 12.4]. Along every sequence of
observations `O`, actions `A` and feedbacks `Y`, with `P t` the weights of Exp3-IX at round `t`
and `Ŷ t` its implicit-exploration loss estimates, for `γ t ≥ 0` at the rounds `t < n`,
`∑ t < n, ((1 - Y t) - ⟨P t, Ŷ t⟩) = ∑ t < n, γ t * ∑ b, Ŷ t b`. For a constant `γ`, the
right-hand side is `γ * ∑ b, L̂ n b`, with `L̂ n` the cumulative loss estimates. -/
theorem sum_sub_sum_mul_eq_sum_mul_sum (hγ : ∀ t < n, 0 ≤ γ t) :
    ∑ t ∈ range n, ((1 - Y t ω) - ∑ b,
      exp4IXWeights singleAdvice η γ t (history O A Y t ω) (O t ω) b *
      iwEstimator (fun a ↦ exp4IXWeights singleAdvice η γ t (history O A Y t ω) (O t ω) a + γ t)
        (A t ω) (1 - Y t ω) b) =
      ∑ t ∈ range n, γ t * ∑ b, iwEstimator
        (fun a ↦ exp4IXWeights singleAdvice η γ t (history O A Y t ω) (O t ω) a + γ t)
          (A t ω) (1 - Y t ω) b :=
  Finset.sum_congr rfl fun t ht ↦ sub_sum_mul_iwEstimator_add
    (add_pos_of_pos_of_nonneg (exp4IXWeights_single_pos _ _ _ _) (hγ t (mem_range.1 ht))).ne'

/-- **Pathwise bound on the estimated regret of Exp3-IX** [LS, (12.3) and Lemma 12.4]. Along every
sequence of observations `O`, actions `A` and feedbacks `Y t ∈ [0, 1]` of the rounds `t < n`, with
`Ŷ t` the implicit-exploration loss estimates of Exp3-IX and `L̂ n` their cumulative sums, for
every arm `a`, nonincreasing learning rates `η t > 0` and `γ t ≥ 0`,
`∑ t < n, (1 - Y t) - L̂ n a ≤ log k / η (n - 1) + ∑ t < n, (γ t + η t / 2) * ∑ b, Ŷ t b`, with
`k` the number of arms. This is the pathwise bound of Exp4-IX for one expert per arm. -/
theorem sum_sub_exp4IXSum_le (hη : ∀ t, 0 < η t) (hη_anti : Antitone η) (hγ : ∀ t, 0 ≤ γ t)
    (hY : ∀ t < n, Y t ω ∈ Set.Icc 0 1) (a : α) :
    ∑ t ∈ range n, (1 - Y t ω) - exp4IXSum singleAdvice η γ n (history O A Y n ω) a ≤
      log (Fintype.card α) / η (n - 1) + ∑ t ∈ range n, (γ t + η t / 2) * ∑ b, iwEstimator
        (fun a ↦ exp4IXWeights singleAdvice η γ t (history O A Y t ω) (O t ω) a + γ t)
          (A t ω) (1 - Y t ω) b := by
  have key := Exp4IX.sum_one_sub_sub_dotProduct_le (adv := singleAdvice) O A Y ω hη hη_anti hγ hY
    (fun t _ ↦ (add_pos_of_pos_of_nonneg (exp4IXWeights_single_pos _ _ _ _) (hγ t)).ne') a
  simp only [coe_singleAdvice, single_dotProduct, one_mul] at key
  rwa [exp4IXSum_single_history, ← Finset.sum_sub_distrib]

end Pathwise

/-! ### Concentration of the loss estimates -/

section Concentration

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] [Nonempty α]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {env : Environment 𝓞 α ℝ} {η γ : ℕ → ℝ}
  {n : ℕ} {δ : ℝ}

/-- **Concentration of the loss estimates of Exp3-IX** [LS, proof of Lemma 12.3]. Along a run of
Exp3-IX against any environment whose feedback at every round `t < n` is almost surely in
`[0, 1]`, for `0 ≤ c ≤ γ t` at the rounds `t < n`, weights `v a ∈ [0, 1]` on the arms, weights
`w t ∈ [0, 1]` on the rounds `t < n` and `δ > 0`, the probability that
`log (1 / δ) ≤ 2 c ∑ t < n, w t * ∑ a, v a * (Ŷ t a - (1 - m_t(a)))` is at most `δ`, with `Ŷ t`
the implicit-exploration loss estimates and `m_t(a) = env.means O A Y a t` the conditional means
of the rewards. This is the instance of
`WeightAlgorithm.measure_log_one_div_le_sum_sum_mul_iwEstimator_add_sub_le` with the coefficients
`2 c w t v a`. -/
theorem measure_le_sum_mul_sum_mul_iwEstimator_sub_le {v : α → ℝ} (hv : ∀ a, v a ∈ Set.Icc 0 1)
    {w : ℕ → ℝ} (hw : ∀ t < n, w t ∈ Set.Icc 0 1) {c : ℝ} (hc : 0 ≤ c) (hcγ : ∀ t < n, c ≤ γ t)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) (h : IsAlgEnvSeq O A Y (exp3IX η γ) env P)
    (hδ : 0 < δ) :
    P {ω | log (1 / δ) ≤ 2 * c * ∑ t ∈ range n, w t * ∑ a, v a *
      (iwEstimator (fun b ↦ exp4IXWeights singleAdvice η γ t (history O A Y t ω) (O t ω) b + γ t)
        (A t ω) (1 - Y t ω) a - (1 - env.means O A Y a t ω))} ≤ ENNReal.ofReal δ := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (WeightAlgorithm.measure_log_one_div_le_sum_sum_mul_iwEstimator_add_sub_le
      (Exp4IX.isAlgEnvSeq_weightAlgorithm h) hY (γ := γ)
      (c := fun t a _ ↦ 2 * c * w t * v a) (fun _ _ _ ↦ measurable_const)
      (fun t ht a _ ↦ mul_nonneg (mul_nonneg (by positivity) (hw t ht).1) (hv a).1)
      (fun t ht a _ ↦ (mul_le_of_le_one_right (mul_nonneg (by positivity) (hw t ht).1)
        (hv a).2).trans ((mul_le_of_le_one_right (by positivity) (hw t ht).2).trans (by
          linarith [hcγ t ht])))
      (fun t _ a _ ha ↦ absurd ha (exp4IXWeights_single_pos t _ _ a).ne') hδ)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine hω.trans_eq ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ by ring

/-- **Concentration of the loss estimates of one arm** [LS, (12.9)]. Along a run of Exp3-IX with
nonincreasing `γ` and `γ (n - 1) > 0` against any environment whose feedback at every round
`t < n` is almost surely in `[0, 1]`, for every arm `a` and `δ > 0`, the probability that
`log (1 / δ) / (2 γ (n - 1)) ≤ L̂ n a - L n a` is at most `δ`, with `L̂ n` the cumulative loss
estimates and `L n a = ∑ t < n, (1 - m_t(a))`, `m_t(a) = env.means O A Y a t`. -/
theorem measure_le_exp4IXSum_sub_le (hγ_anti : Antitone γ) (hγn : 0 < γ (n - 1))
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) (h : IsAlgEnvSeq O A Y (exp3IX η γ) env P)
    (hδ : 0 < δ) (a : α) :
    P {ω | log (1 / δ) / (2 * γ (n - 1)) ≤
      exp4IXSum singleAdvice η γ n (history O A Y n ω) a -
        ∑ t ∈ range n, (1 - env.means O A Y a t ω)} ≤ ENNReal.ofReal δ := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_le_sum_mul_sum_mul_iwEstimator_sub_le (v := Pi.single a 1) (w := fun _ ↦ 1)
      (fun b ↦ ?_) (fun _ _ ↦ ⟨zero_le_one, le_rfl⟩) hγn.le
      (fun t ht ↦ hγ_anti (Nat.le_sub_one_of_lt ht)) hY h hδ)
  · simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [← div_le_iff₀' (by positivity)]
    refine hω.trans_eq ?_
    rw [exp4IXSum_single_history, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [one_mul, Finset.sum_eq_single a (fun b _ hb ↦ by simp [hb]) (by simp), Pi.single_eq_same,
      one_mul]
  · rw [Pi.single_apply]
    split_ifs <;> simp

/-- **Concentration of the weighted sums of the loss estimates**. Along a run of Exp3-IX with
nonincreasing `γ` and `γ (n - 1) > 0` against any environment whose feedback at every round
`t < n` is almost surely in `[0, 1]`, for weights `w t ∈ [0, 1]` on the rounds `t < n` and
`δ > 0`, the probability that
`log (1 / δ) / (2 γ (n - 1)) ≤ ∑ t < n, w t * ∑ a, (Ŷ t a - (1 - m_t(a)))` is at most `δ`, with
`Ŷ t` the implicit-exploration loss estimates and `m_t(a) = env.means O A Y a t`. This is the
case `v = 1`, `c = γ (n - 1)` of `measure_le_sum_mul_sum_mul_iwEstimator_sub_le`. -/
theorem measure_le_sum_mul_sum_iwEstimator_sub_le (hγ_anti : Antitone γ) (hγn : 0 < γ (n - 1))
    {w : ℕ → ℝ} (hw : ∀ t < n, w t ∈ Set.Icc 0 1) (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3IX η γ) env P) (hδ : 0 < δ) :
    P {ω | log (1 / δ) / (2 * γ (n - 1)) ≤ ∑ t ∈ range n, w t * ∑ a,
      (iwEstimator (fun b ↦ exp4IXWeights singleAdvice η γ t (history O A Y t ω) (O t ω) b + γ t)
        (A t ω) (1 - Y t ω) a - (1 - env.means O A Y a t ω))} ≤ ENNReal.ofReal δ := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_le_sum_mul_sum_mul_iwEstimator_sub_le (v := fun _ ↦ 1)
      (fun _ ↦ ⟨zero_le_one, le_rfl⟩) hw hγn.le (fun t ht ↦ hγ_anti (Nat.le_sub_one_of_lt ht))
      hY h hδ)
  simp only [Set.mem_ofPred_eq, one_mul] at hω ⊢
  rwa [div_le_iff₀' (by positivity)] at hω

/-- **Concentration of the sum of the loss estimates** [LS, (12.8)]. Along a run of Exp3-IX with
nonincreasing `γ` and `γ (n - 1) > 0` against any environment whose feedback at every round
`t < n` is almost surely in `[0, 1]`, for `δ > 0`, the probability that
`log (1 / δ) / (2 γ (n - 1)) ≤ ∑ a, (L̂ n a - L n a)` is at most `δ`, with `L̂ n` the cumulative
loss estimates and `L n a = ∑ t < n, (1 - m_t(a))`, `m_t(a) = env.means O A Y a t`. -/
theorem measure_le_sum_exp4IXSum_sub_le (hγ_anti : Antitone γ) (hγn : 0 < γ (n - 1))
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) (h : IsAlgEnvSeq O A Y (exp3IX η γ) env P)
    (hδ : 0 < δ) :
    P {ω | log (1 / δ) / (2 * γ (n - 1)) ≤
      ∑ a, (exp4IXSum singleAdvice η γ n (history O A Y n ω) a -
        ∑ t ∈ range n, (1 - env.means O A Y a t ω))} ≤ ENNReal.ofReal δ := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_le_sum_mul_sum_iwEstimator_sub_le (w := fun _ ↦ 1) hγ_anti hγn
      (fun _ _ ↦ ⟨zero_le_one, le_rfl⟩) hY h hδ)
  simp only [Set.mem_ofPred_eq, one_mul] at hω ⊢
  simp only [exp4IXSum_single_history, ← Finset.sum_sub_distrib] at hω
  rwa [Finset.sum_comm] at hω

/-- **Concentration of the loss estimates of Exp3-IX** [LS, Lemma 12.3]. Along a run of Exp3-IX
with nonincreasing `γ` and `γ (n - 1) > 0` against any environment whose feedback at every round
`t < n` is almost surely in `[0, 1]`, for weights `w t ∈ [0, 1]` on the rounds `t < n` and
`δ > 0`, with probability at least `1 - δ`, both `L̂ n a - L n a < c` for every arm `a` and
`∑ t < n, w t * ∑ a, (Ŷ t a - (1 - m_t(a))) < c`, where `c = log ((k + 1) / δ) / (2 γ (n - 1))`,
`Ŷ t` are the implicit-exploration loss estimates, `L̂ n` their cumulative sums,
`L n a = ∑ t < n, (1 - m_t(a))` for the conditional means `m_t(a) = env.means O A Y a t` of the
rewards, and `k` is the number of arms. With `w = 1` and a constant `γ`, the second sum is
`∑ a, (L̂ n a - L n a)`, as in [LS]. -/
theorem measure_exists_le_exp4IXSum_sub_union_le (hγ_anti : Antitone γ) (hγn : 0 < γ (n - 1))
    {w : ℕ → ℝ} (hw : ∀ t < n, w t ∈ Set.Icc 0 1) (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3IX η γ) env P) (hδ : 0 < δ) :
    P ({ω | ∃ a, log ((Fintype.card α + 1) / δ) / (2 * γ (n - 1)) ≤
        exp4IXSum singleAdvice η γ n (history O A Y n ω) a -
          ∑ t ∈ range n, (1 - env.means O A Y a t ω)} ∪
      {ω | log ((Fintype.card α + 1) / δ) / (2 * γ (n - 1)) ≤ ∑ t ∈ range n, w t * ∑ a,
        (iwEstimator (fun b ↦ exp4IXWeights singleAdvice η γ t (history O A Y t ω) (O t ω) b +
          γ t) (A t ω) (1 - Y t ω) a - (1 - env.means O A Y a t ω))}) ≤
      ENNReal.ofReal δ := by
  -- a union bound over `k + 1` events of probability at most `δ / (k + 1)`
  have hk : (0 : ℝ) < Fintype.card α + 1 := by positivity
  have hδ' : 0 < δ / (Fintype.card α + 1) := div_pos hδ hk
  have hlog : log (1 / (δ / (Fintype.card α + 1))) = log ((Fintype.card α + 1) / δ) := by
    rw [one_div_div]
  refine (measure_union_le _ _).trans ?_
  calc
    _ ≤ ∑ _a : α, ENNReal.ofReal (δ / (Fintype.card α + 1)) +
        ENNReal.ofReal (δ / (Fintype.card α + 1)) := by
      gcongr
      · rw [Set.ofPred_exists]
        refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
        simpa [hlog] using measure_le_exp4IXSum_sub_le hγ_anti hγn hY h hδ' a
      · simpa [hlog] using measure_le_sum_mul_sum_iwEstimator_sub_le hγ_anti hγn hw hY h hδ'
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ hδ'.le, ← ENNReal.ofReal_add
        (Finset.sum_nonneg fun _ _ ↦ hδ'.le) hδ'.le]
      congr 1
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

end Concentration

/-! ### High-probability regret bounds -/

section Regret

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] [Nonempty α]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {env : Environment 𝓞 α ℝ} {n : ℕ} {δ : ℝ}

/-- **High-probability regret bound of Exp3-IX** [LS, proof of Theorem 12.1]. Along a run of
Exp3-IX with nonincreasing learning rates `η t > 0` and nonincreasing implicit-exploration
parameters `γ t ≥ 0` with `γ (n - 1) > 0`, against any environment whose feedback at every round
`t < n` is almost surely in `[0, 1]`, for `δ > 0`, the probability that the random regret
`R̂_n = max_a ∑ t < n, (m_t(a) - Y t)` is at least
`log k / η (n - 1) + k ∑ t < n, (γ t + η t / 2) + (γ 0 + η 0 / 2 + 1) c` is at most `δ`, where
`c = log ((k + 1) / δ) / (2 γ (n - 1))`, `m_t(a) = env.means O A Y a t` is the conditional mean of
the reward of arm `a` at round `t` and `k` is the number of arms. For constant rates `η` and `γ`,
the bound is `log k / η + (γ + η / 2) (n k + c) + c`. -/
theorem measure_le_randomRegret_le {η γ : ℕ → ℝ} (hη : ∀ t, 0 < η t) (hη_anti : Antitone η)
    (hγ : ∀ t, 0 ≤ γ t) (hγ_anti : Antitone γ) (hγn : 0 < γ (n - 1))
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) (h : IsAlgEnvSeq O A Y (exp3IX η γ) env P)
    (hδ : 0 < δ) :
    P {ω | log (Fintype.card α) / η (n - 1) + Fintype.card α * ∑ t ∈ range n, (γ t + η t / 2) +
        (γ 0 + η 0 / 2 + 1) * (log ((Fintype.card α + 1) / δ) / (2 * γ (n - 1))) ≤
          randomRegret env O A Y n ω} ≤ ENNReal.ofReal δ := by
  set c := log ((Fintype.card α + 1) / δ) / (2 * γ (n - 1)) with hc_def
  -- the weights `w t = b t / b 0` of the rounds, for the coefficients `b t = γ t + η t / 2` of the
  -- pathwise bound
  have hb : ∀ t, 0 ≤ γ t + η t / 2 := fun t ↦ by linarith [hγ t, hη t]
  have hb0 : 0 < γ 0 + η 0 / 2 := by linarith [hγ 0, hη 0]
  have hw : ∀ t < n, (γ t + η t / 2) / (γ 0 + η 0 / 2) ∈ Set.Icc 0 1 := fun t _ ↦
    ⟨div_nonneg (hb t) hb0.le, (div_le_one hb0).2 (by
      linarith [hγ_anti (Nat.zero_le t), hη_anti (Nat.zero_le t)])⟩
  refine le_trans (measure_mono_ae ?_)
    (measure_exists_le_exp4IXSum_sub_union_le hγ_anti hγn hw hY h hδ)
  filter_upwards [hY, WeightAlgorithm.ae_forall_means_nonneg_of_weights_pos
    (Exp4IX.isAlgEnvSeq_weightAlgorithm h) hY] with ω h01 hm0 hR
  by_contra hE
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_le] at hE hR
  obtain ⟨hEa, hEs⟩ := hE
  -- the random regret is the regret against some arm `a`
  obtain ⟨a, ha⟩ := exists_eq_ciSup_of_finite
    (f := fun a ↦ ∑ t ∈ range n, (env.means O A Y a t ω - Y t ω))
  rw [randomRegret_def, ← ha] at hR
  -- the estimated regret, the deviation of arm `a` and the weighted sums of the estimates
  rw [← hc_def] at hEa hEs
  set L := exp4IXSum singleAdvice η γ n (history O A Y n ω)
  set Yh : ℕ → α → ℝ := fun t ↦ iwEstimator
    (fun b ↦ exp4IXWeights singleAdvice η γ t (history O A Y t ω) (O t ω) b + γ t) (A t ω)
      (1 - Y t ω) with hYh
  have hpath : ∑ t ∈ range n, (1 - Y t ω) - L a ≤
      log (Fintype.card α) / η (n - 1) + ∑ t ∈ range n, (γ t + η t / 2) * ∑ b, Yh t b :=
    sum_sub_exp4IXSum_le O A Y ω hη hη_anti hγ h01 a
  have hEs' : ∑ t ∈ range n, (γ t + η t / 2) / (γ 0 + η 0 / 2) *
      ∑ b, (Yh t b - (1 - env.means O A Y b t ω)) < c := hEs
  have hsplit : ∑ t ∈ range n, (env.means O A Y a t ω - Y t ω) =
      (∑ t ∈ range n, (1 - Y t ω) - L a) +
        (L a - ∑ t ∈ range n, (1 - env.means O A Y a t ω)) := by
    rw [sub_add_sub_cancel, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ ↦ by ring
  -- the conditional means are nonnegative, since every arm has positive weight, so the losses of
  -- the means of a round sum to at most `k`
  have hk : ∀ t ∈ range n, (γ t + η t / 2) * ∑ b, (1 - env.means O A Y b t ω) ≤
      (γ t + η t / 2) * Fintype.card α := fun t ht ↦ by
    refine mul_le_mul_of_nonneg_left ?_ (hb t)
    calc ∑ b, (1 - env.means O A Y b t ω) ≤ ∑ _b : α, (1 : ℝ) :=
          Finset.sum_le_sum fun b _ ↦
            sub_le_self _ (hm0 t (mem_range.1 ht) b (exp4IXWeights_single_pos _ _ _ b))
      _ = Fintype.card α := by simp
  -- the weighted sum of the estimates is the weighted sum of the losses of the means plus
  -- `b 0` times the weighted deviation
  have hid : ∑ t ∈ range n, (γ t + η t / 2) * ∑ b, Yh t b =
      ∑ t ∈ range n, (γ t + η t / 2) * ∑ b, (1 - env.means O A Y b t ω) +
        (γ 0 + η 0 / 2) * ∑ t ∈ range n, (γ t + η t / 2) / (γ 0 + η 0 / 2) *
          ∑ b, (Yh t b - (1 - env.means O A Y b t ω)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [← mul_assoc, mul_div_cancel₀ _ hb0.ne', ← mul_add, ← Finset.sum_add_distrib]
    simp only [add_sub_cancel]
  have hS : ∑ t ∈ range n, (γ t + η t / 2) * ∑ b, Yh t b ≤
      Fintype.card α * ∑ t ∈ range n, (γ t + η t / 2) + (γ 0 + η 0 / 2) * c := by
    rw [hid]
    have h1 := Finset.sum_le_sum hk
    have h2 := mul_le_mul_of_nonneg_left hEs'.le hb0.le
    rw [← Finset.sum_mul] at h1
    linarith
  have hc : (γ 0 + η 0 / 2 + 1) * c = (γ 0 + η 0 / 2) * c + c := by ring
  linarith [hEa a]

end Regret

/-! ### High-probability regret bounds for constant rates -/

section ConstantRates

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] [Nonempty α]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {env : Environment 𝓞 α ℝ} {η : ℝ} {n : ℕ}
  {δ : ℝ}

/-- **High-probability regret bound of Exp3-IX with `γ = η / 2`** [LS, proof of Theorem 12.1].
Along a run of Exp3-IX with learning rate `η ≥ 0` and implicit-exploration parameter `γ = η / 2`
against any environment whose feedback at every round `t < n` is almost surely in `[0, 1]`, for
`δ > 0` and `L ≥ log k + log ((k + 1) / δ)` such that `η > 0` whenever `n` and `L` are positive,
the probability that the random regret `R̂_n = max_a ∑ t < n, (m_t(a) - Y t)` is at least
`L / η + η n k + log ((k + 1) / δ)` is at most `δ`, with `m_t(a) = env.means O A Y a t` and `k`
the number of arms. -/
theorem measure_div_add_mul_add_le_randomRegret_le {L : ℝ} (hη : 0 ≤ η)
    (hηL : 0 < n → 0 < L → 0 < η)
    (hL : log (Fintype.card α) + log ((Fintype.card α + 1) / δ) ≤ L)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3IX (fun _ ↦ η) (fun _ ↦ η / 2)) env P) (hδ : 0 < δ) :
    P {ω | L / η + η * (n * Fintype.card α) + log ((Fintype.card α + 1) / δ) ≤
      randomRegret env O A Y n ω} ≤ ENNReal.ofReal δ := by
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.2 hδ1)
  have hk0 : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hlogδ : 0 < log ((Fintype.card α + 1) / δ) := log_pos ((one_lt_div hδ).2 (by linarith))
  have hlogk : 0 ≤ log (Fintype.card α) := log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hL0 : 0 < L := by linarith
  -- with no round, the regret is zero
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (measure_mono_null (fun ω hω ↦ ?_) measure_empty).trans_le zero_le
    simp only [Set.mem_ofPred_eq, randomRegret_def, CharP.cast_eq_zero, zero_mul, mul_zero,
      add_zero, range_zero, sum_empty, ciSup_const] at hω
    linarith [div_nonneg hL0.le hη]
  have hη0 := hηL hn hL0
  refine (measure_mono fun ω hω ↦ ?_).trans
    (measure_le_randomRegret_le (fun _ ↦ hη0) antitone_const (fun _ ↦ (half_pos hη0).le)
      antitone_const (half_pos hη0) hY h hδ)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine le_trans ?_ hω
  -- the bound of `measure_le_randomRegret_le` for the constant rates `η` and `γ = η / 2`
  have e1 : log (Fintype.card α) / η + Fintype.card α * ∑ t ∈ range n, (η / 2 + η / 2) +
      (η / 2 + η / 2 + 1) * (log ((Fintype.card α + 1) / δ) / (2 * (η / 2))) =
      (log (Fintype.card α) + log ((Fintype.card α + 1) / δ)) / η + η * (n * Fintype.card α) +
        log ((Fintype.card α + 1) / δ) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
    ring
  rw [e1]
  gcongr

/-- **High-probability regret bound of Exp3-IX** [LS, Theorem 12.1, (12.5)], against an adaptive
adversary. Along a run of Exp3-IX with learning rate `η = √(2 log (k + 1) / (n k))` and
implicit-exploration parameter `γ = η / 2` against any environment whose feedback at every round
`t < n` is almost surely in `[0, 1]`, for every `δ > 0`, the probability that the random regret
`R̂_n = max_a ∑ t < n, (m_t(a) - Y t)` is at least
`√(8 n k log (k + 1)) + √(n k / (2 log (k + 1))) log (1 / δ) + log ((k + 1) / δ)` is at most `δ`,
with `m_t(a) = env.means O A Y a t` and `k` the number of arms. The learning rate does not depend
on `δ`. -/
theorem measure_sqrt_add_le_randomRegret_le (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3IX (fun _ ↦ √(2 * log (Fintype.card α + 1) / (n * Fintype.card α)))
      (fun _ ↦ √(2 * log (Fintype.card α + 1) / (n * Fintype.card α)) / 2)) env P) (hδ : 0 < δ) :
    P {ω | √(8 * n * Fintype.card α * log (Fintype.card α + 1)) +
        √(n * Fintype.card α / (2 * log (Fintype.card α + 1))) * log (1 / δ) +
          log ((Fintype.card α + 1) / δ) ≤ randomRegret env O A Y n ω} ≤
      ENNReal.ofReal δ := by
  set k : ℝ := (Fintype.card α : ℝ) with hk
  have hk0 : 0 < k := by rw [hk]; exact_mod_cast Fintype.card_pos
  have hL : 0 < log (k + 1) := log_pos (by linarith)
  set m : ℝ := n * k with hm
  have hm0 : 0 ≤ m := mul_nonneg n.cast_nonneg hk0.le
  set η := √(2 * log (k + 1) / m) with hη
  -- `L = 2 log (k + 1) + log (1 / δ)` in `measure_div_add_mul_add_le_randomRegret_le`
  have hlog : log ((k + 1) / δ) = log (k + 1) + log (1 / δ) := by
    rw [div_eq_mul_one_div, log_mul (by linarith) (by positivity)]
  have hLle : log k + log ((k + 1) / δ) ≤ 2 * log (k + 1) + log (1 / δ) := by
    rw [hlog]
    linarith [log_le_log hk0 (by linarith : k ≤ k + 1)]
  refine (measure_mono fun ω hω ↦ ?_).trans
    (measure_div_add_mul_add_le_randomRegret_le (sqrt_nonneg _)
      (fun hn _ ↦ sqrt_pos.2 (div_pos (by positivity) (mul_pos (Nat.cast_pos.2 hn) hk0))) hLle
      hY h hδ)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine le_trans (le_of_eq ?_) hω
  have e2 : √(8 * n * k * log (k + 1)) = 2 * log (k + 1) / η + η * m := by
    have := div_sqrt_add_sqrt_mul_div_two (log (k + 1)) hm0
    rw [show (8 : ℝ) * n * k * log (k + 1) = 2 ^ 2 * (2 * m * log (k + 1)) by rw [hm]; ring,
      sqrt_mul (by positivity), sqrt_sq zero_le_two, ← this, hη]
    ring
  have e3 : √(n * k / (2 * log (k + 1))) = 1 / η := by
    rw [hη, one_div, ← sqrt_inv, inv_div, hm]
  rw [e2, e3, ← hm]
  ring

/-- **High-probability regret bound of Exp3-IX for a fixed confidence level**
[LS, Theorem 12.1, (12.6)], against an adaptive adversary. Along a run of Exp3-IX with learning
rate `η = √((log k + log ((k + 1) / δ)) / (n k))` and implicit-exploration parameter `γ = η / 2`
against any environment whose feedback at every round `t < n` is almost surely in `[0, 1]`, for
`δ > 0`, the probability that the random regret `R̂_n = max_a ∑ t < n, (m_t(a) - Y t)` is at least
`2 √((2 log (k + 1) + log (1 / δ)) n k) + log ((k + 1) / δ)` is at most `δ`, with
`m_t(a) = env.means O A Y a t` and `k` the number of arms. -/
theorem measure_two_mul_sqrt_add_le_randomRegret_le
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3IX
      (fun _ ↦ √((log (Fintype.card α) + log ((Fintype.card α + 1) / δ)) / (n * Fintype.card α)))
      (fun _ ↦
        √((log (Fintype.card α) + log ((Fintype.card α + 1) / δ)) / (n * Fintype.card α)) / 2))
      env P) (hδ : 0 < δ) :
    P {ω | 2 * √((2 * log (Fintype.card α + 1) + log (1 / δ)) * n * Fintype.card α) +
          log ((Fintype.card α + 1) / δ) ≤ randomRegret env O A Y n ω} ≤
      ENNReal.ofReal δ := by
  set k : ℝ := (Fintype.card α : ℝ) with hk
  have hk0 : 0 < k := by rw [hk]; exact_mod_cast Fintype.card_pos
  set m : ℝ := n * k with hm
  have hm0 : 0 ≤ m := mul_nonneg n.cast_nonneg hk0.le
  set M := log k + log ((k + 1) / δ) with hM
  set η := √(M / m) with hη
  refine (measure_mono fun ω hω ↦ ?_).trans
    (measure_div_add_mul_add_le_randomRegret_le (L := M) (sqrt_nonneg _)
      (fun hn hM0 ↦ sqrt_pos.2 (div_pos hM0 (mul_pos (Nat.cast_pos.2 hn) hk0))) le_rfl
      hY h hδ)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine le_trans ?_ hω
  -- the bound `M / η + η m + log ((k + 1) / δ)` is `2 √(M m) + log ((k + 1) / δ)`
  have hbal : M / η + η * m = 2 * √(M * m) := by
    have := div_sqrt_add_sqrt_mul_div_two (M / 2) hm0
    rw [show 2 * (M / 2) / m = M / m by ring, show 2 * m * (M / 2) = M * m by ring, ← hη] at this
    rw [← this]
    ring
  -- `M ≤ 2 log (k + 1) + log (1 / δ)`
  have hMle : M ≤ 2 * log (k + 1) + log (1 / δ) := by
    have h1 : log k ≤ log (k + 1) := log_le_log hk0 (by linarith)
    have h2 : log ((k + 1) / δ) = log (k + 1) + log (1 / δ) := by
      rw [div_eq_mul_one_div, log_mul (by linarith) (by positivity)]
    rw [hM, h2]
    linarith
  have hsqrt : √(M * m) ≤ √((2 * log (k + 1) + log (1 / δ)) * n * k) := by
    rw [mul_assoc _ (n : ℝ) k, ← hm]
    exact sqrt_le_sqrt (mul_le_mul_of_nonneg_right hMle hm0)
  rw [← hm, hbal]
  linarith

end ConstantRates

end Exp3IX

section EvalSeq

variable [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {x : ℕ → α → ℝ}
  {hxm : ∀ t, Measurable (x t)} {n : ℕ} {δ : ℝ}

/-- **High-probability regret bound of Exp3-IX** [LS, Theorem 12.1, (12.5)] against an oblivious
adversary: along a run of Exp3-IX with `η = √(2 log (k + 1) / (n k))` and `γ = η / 2` against
LML's evaluation environment `Environment.evalSeq x _` with rewards in `[0, 1]` at the rounds
`t < n`, for every `δ > 0`, the probability that the random regret against some arm is at least
`√(8 n k log (k + 1)) + √(n k / (2 log (k + 1))) log (1 / δ) + log ((k + 1) / δ)` is at most `δ`,
with `k` the number of arms. -/
theorem exp3IX_measure_exists_sqrt_le_sum_sub_le (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3IX (fun _ ↦ √(2 * log (Fintype.card α + 1) / (n * Fintype.card α)))
      (fun _ ↦ √(2 * log (Fintype.card α + 1) / (n * Fintype.card α)) / 2))
      (Environment.evalSeq x hxm) P) (hδ : 0 < δ) :
    P {ω | ∃ a, √(8 * n * Fintype.card α * log (Fintype.card α + 1)) +
        √(n * Fintype.card α / (2 * log (Fintype.card α + 1))) * log (1 / δ) +
          log ((Fintype.card α + 1) / δ) ≤ ∑ t ∈ range n, (x t a - x t (A t ω))} ≤
      ENNReal.ofReal δ :=
  (h.measure_exists_le_sum_sub_le_measure_le_randomRegret n _).trans
    (Exp3IX.measure_sqrt_add_le_randomRegret_le
      (ae_feedback_mem_Icc (fun t _ ↦ h.feedback_ae_eq_evalSeq t) hx) h hδ)

/-- **High-probability regret bound of Exp3-IX for a fixed confidence level**
[LS, Theorem 12.1, (12.6)] against an oblivious adversary: along a run of Exp3-IX with
`η = √((log k + log ((k + 1) / δ)) / (n k))` and `γ = η / 2` against LML's evaluation environment
`Environment.evalSeq x _` with rewards in `[0, 1]` at the rounds `t < n`, for `δ > 0`, the
probability that the random regret against some arm is at least
`2 √((2 log (k + 1) + log (1 / δ)) n k) + log ((k + 1) / δ)` is at most `δ`, with `k` the number
of arms. -/
theorem exp3IX_measure_exists_two_mul_sqrt_le_sum_sub_le (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3IX
      (fun _ ↦ √((log (Fintype.card α) + log ((Fintype.card α + 1) / δ)) / (n * Fintype.card α)))
      (fun _ ↦
        √((log (Fintype.card α) + log ((Fintype.card α + 1) / δ)) / (n * Fintype.card α)) / 2))
      (Environment.evalSeq x hxm) P) (hδ : 0 < δ) :
    P {ω | ∃ a, 2 * √((2 * log (Fintype.card α + 1) + log (1 / δ)) * n * Fintype.card α) +
          log ((Fintype.card α + 1) / δ) ≤ ∑ t ∈ range n, (x t a - x t (A t ω))} ≤
      ENNReal.ofReal δ :=
  (h.measure_exists_le_sum_sub_le_measure_le_randomRegret n _).trans
    (Exp3IX.measure_two_mul_sqrt_add_le_randomRegret_le
      (ae_feedback_mem_Icc (fun t _ ↦ h.feedback_ae_eq_evalSeq t) hx) h hδ)

end EvalSeq

end LMLExplore.Bandits
