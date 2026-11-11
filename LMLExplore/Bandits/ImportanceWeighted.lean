/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.WeightAlgorithm
public import LMLExplore.Probability.CondVar
public import LMLExplore.Probability.Martingale.ImplicitExploration
public import LMLExplore.SequentialLearning.Means

/-!
# Importance-weighted estimators

An adversarial bandit algorithm observes at round `t` only the reward `X_t = x_t (A_t)` of the
arm `A_t` it plays, drawn from a probability vector `P_t`. It estimates the reward of every arm
`a` by importance weighting [LS, Section 11.2]: the **importance-weighted estimator**
`X̂_t a = 𝟙{A_t = a} X_t / P_t a` [LS, (11.3)] and the **loss-based importance-weighted estimator**
`X̂_t a = 1 - 𝟙{A_t = a} (1 - X_t) / P_t a` [LS, (11.6)]. Both are conditionally unbiased given
the past when `P_t a > 0` [LS, (11.4)], with conditional variances
`x_t a ^ 2 (1 - P_t a) / P_t a` [LS, (11.5)] and `(1 - x_t a) ^ 2 (1 - P_t a) / P_t a`. The
loss-based estimator is at most `1` for rewards at most `1`, which the analysis of Exp3 uses.

Both estimators are defined as functions of a probability vector `p`, the drawn arm `b` and the
observed reward `y`, so that an algorithm can compute them from its history. For a run of a
weight-based algorithm (`LMLExplore.Bandits.weightAlgorithm`), the past of round `n` is the pair
of the history and the observation of round `n`, `p` is the weight vector `w n (past)` and the
conditional statements are given the σ-algebra `h.filtrationObs n` of the past.

The conditional statements hold against any environment. The estimates of the feedback of an arm
`a` have conditional mean `env.means O A Y a n`, LML's mean of the feedback of `a` at round `n`
given the past, and conditional variance `E_a[Y ^ 2] / P_t a - (env.means O A Y a n) ^ 2` with
`E_a[Y ^ 2]` the conditional second moment of that feedback. More generally, the estimates of any
random variable `Z` whose conditional mean given the past and the action is `m (past) (A n)` have
conditional mean `m (past) a`. For a reward table fixed in advance, as in LML's
`Environment.evalSeq g _` with `x = g n` (`IsAlgEnvSeq.feedback_ae_eq_evalSeq`) and
`Environment.ofSeq o g _` with expert advice `o` (`IsAlgEnvSeq.feedback_ofSeq_ae_eq`), the
feedback `Y n` is almost surely the reward `x (A n)` of the action, the conditional means are
`x a` and the variances are those of [LS, (11.5)].

## Main definitions

* `LMLExplore.Bandits.iwEstimator p b y`: the vector `a ↦ 𝟙{b = a} y / p a`.
* `LMLExplore.Bandits.lossIwEstimator p b y`: the vector `a ↦ 1 - 𝟙{b = a} (1 - y) / p a`.

## Main statements

* `sum_mul_iwEstimator_apply`, `sum_mul_lossIwEstimator_apply`: averaged over the drawn arm
  `b ∼ p`, the estimates of the reward `x a` are equal to `x a` when `p a ≠ 0`.
* `sum_mul_iwEstimator_apply_sub_sq`, `sum_mul_lossIwEstimator_apply_sub_sq`: the corresponding
  variances.
* `sum_mul_sum_mul_iwEstimator_apply_sub_sq`: the `p`-average of a weighted sum over the arms of
  the squared deviations of the importance-weighted estimates, as in the local norms of
  Tsallis-INF.
* `dotProduct_iwEstimator`, `dotProduct_lossIwEstimator`: the averages of the estimates against
  a vector `e` summing to `1`, such as the advice of an expert in Exp4, are `e b y / p b` and
  `1 - e b (1 - y) / p b`.
* `sum_iwEstimator`: the importance-weighted estimates of all the arms sum to `y / p b`.
* `sum_mul_iwEstimator_sq`: the `p`-average of the squared importance-weighted estimates is
  `y ^ 2 / p b`, the second moment that the analysis of Exp3 controls.
* `iwEstimator_nonneg`, `iwEstimator_le_one_div`, `lossIwEstimator_le_one`: the
  importance-weighted estimates of a nonnegative reward are nonnegative, those of a reward at most
  `1` are at most `1 / p a`, and the loss-based estimates are at most `1` for rewards at most `1`.
* `norm_iwEstimator_le_single_div`, `mul_iwEstimator_le_two_mul_div`: the bounds on the
  importance-weighted estimates of a reward in `[0, 1]` used by the concentration of
  implicit-exploration estimates.
* `iwEstimator_mul_iwEstimator_of_ne`: the importance-weighted estimates of two different arms
  multiply to `0`.
* `iwEstimator_apply_eq_ite_mul`: the importance-weighted estimate is `𝟙{b = a} / p a` times the
  observed value.
* `iwEstimator_div_one_add_div`, `sub_sum_mul_iwEstimator_add`, `sum_mul_iwEstimator_add_sq_le`:
  the importance-weighted estimator for the weights `p + γ`, the implicit-exploration estimator of
  Exp3-IX [LS, (12.4)], is the estimator for the weights `p` discounted by `1 + γ / p a`; its bias
  is `γ` times the sum of the estimates [LS, Lemma 12.4]; and for losses in `[0, 1]` the
  `p`-average of its squares is at most this sum.
* `comp_feedback_ae_eq`: when the feedback `Y n` is almost surely `x (A n)`, it can be replaced
  by `x (A n)` in any function of the past, the action and the feedback of round `n`.
* `Learning.IsAlgEnvSeq.integrable_feedback_of_ae_eq`,
  `Learning.IsAlgEnvSeq.condExp_feedback_ae_eq_of_ae_eq`: such a feedback is integrable when there
  are finitely many actions, and its conditional expectation given the past and the action of
  round `n` is `x (A n)`.
* `ae_forall_feedback_eq`, `ae_feedback_le_one`, `ae_feedback_mem_Icc`: when the feedbacks of the
  rounds `t < n` are almost surely rewards, they are almost surely these rewards at all these
  rounds simultaneously, and almost surely at most `1`, respectively in `[0, 1]`, when the rewards
  are.
* `WeightAlgorithm.condExp_iwEstimator_eq_ite_of_condExp_eq`: along a run of a weight-based
  algorithm, the importance-weighted estimate at an arm of a random variable whose conditional mean
  given the past and the action is known has this conditional mean at the arm given the past if
  the arm has positive weight, and `0` otherwise.
* `WeightAlgorithm.condExp_iwEstimator_of_condExp_eq`,
  `WeightAlgorithm.condExp_lossIwEstimator_of_condExp_eq`: conditional unbiasedness along a run of a
  weight-based algorithm [LS, (11.4)], for the estimates of a random variable whose conditional mean
  given the past and the action is known.
* `WeightAlgorithm.condExp_iwEstimator`, `WeightAlgorithm.condExp_lossIwEstimator`: in any
  environment, the estimates of the feedback of an arm `a` have conditional mean
  `env.means O A Y a n` given the past.
* `WeightAlgorithm.integral_iwEstimator`, `WeightAlgorithm.integral_lossIwEstimator`: when the
  feedback is almost surely the reward `x (A n)` of the action, the estimates of `x a` are unbiased.
* `WeightAlgorithm.condVar_iwEstimator_of_condExp_eq`: the conditional variance of the
  importance-weighted estimates of a random variable whose conditional mean and second moment
  given the past and the action are known [LS, (11.5)].
* `WeightAlgorithm.condVar_iwEstimator`, `WeightAlgorithm.condVar_lossIwEstimator`: in any
  environment, the conditional variances of the estimates of the feedback [LS, (11.5)].
* `WeightAlgorithm.sum_integral_one_sub_sq_div_weights_le`: in any environment with feedback in
  `[0, 1]`, the expected second-order terms `(1 - Y t) ^ 2 / w t (past) (A t)` of Exp3 and Exp4
  sum to at most `n k` over `n` rounds with `k` arms.
* `WeightAlgorithm.ae_means_nonneg_of_weights_pos`: in any environment with nonnegative feedback,
  the means of the arms of positive weight are almost surely nonnegative.
* `WeightAlgorithm.condExp_iwEstimator_one_sub`: in any environment, the estimate of the loss
  `1 - Y n` of an arm has conditional mean `1 - env.means O A Y a n` given the past if the arm has
  positive weight, and `0` otherwise.
* `WeightAlgorithm.integrable_iwEstimator_one_sub`, `WeightAlgorithm.integral_iwEstimator_one_sub`:
  in any environment with feedback in `[0, 1]`, the estimate of the loss `1 - Y n` of an arm is
  integrable, and its expectation is `E[1 - env.means O A Y a n]` if the arm has almost surely
  positive weight.
* `WeightAlgorithm.measure_log_one_div_le_sum_sum_mul_iwEstimator_add_sub_le`: the concentration of
  the implicit-exploration estimates of the losses in any environment [Neu15, Lemma 1;
  LS, Lemma 12.2].
* `WeightAlgorithm.measure_add_le_sum_mul_sum_iwEstimator_le`: the weighted sums of the
  implicit-exploration estimates of all the arms are at most `k` times the weights, up to
  `log (1 / δ)`, with `k` the number of arms.
* `WeightAlgorithm.ae_means_eq_of_weights_pos`: when the feedback is almost surely the reward
  `x (A n)` of the action, the means of the arms of positive weight are almost surely their
  rewards.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
* [Neu15] G. Neu, *Explore no more: improved high-probability regret bounds for non-stochastic
  bandits*, NeurIPS 2015.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset

namespace LMLExplore.Bandits

variable {α : Type*} [DecidableEq α] {p x : α → ℝ} {a b : α} {y γ : ℝ}

section Estimator

/-- The **importance-weighted estimator** [LS, (11.3)]: when the arm `b` is drawn from the
probability vector `p` and its reward `y` is observed, the estimate of the reward of arm `a` is
`𝟙{b = a} y / p a` (which is `0` when `p a = 0`, by the convention `y / 0 = 0`). -/
noncomputable def iwEstimator (p : α → ℝ) (b : α) (y : ℝ) : α → ℝ := Pi.single b (y / p b)

lemma iwEstimator_def (p : α → ℝ) (b : α) (y : ℝ) :
    iwEstimator p b y = Pi.single b (y / p b) := (rfl)

lemma iwEstimator_apply : iwEstimator p b y a = if a = b then y / p a else 0 := by
  rw [iwEstimator_def, Pi.single_apply]
  split_ifs with h <;> simp [h]

/-- The importance-weighted estimate is linear in the observed reward: it is `y` times
`𝟙{b = a} / p a`. -/
lemma iwEstimator_apply_eq_ite_mul :
    iwEstimator p b y a = (if b = a then (p a)⁻¹ else 0) * y := by
  rw [iwEstimator_apply]
  rcases eq_or_ne b a with rfl | h
  · simp [div_eq_inv_mul]
  · simp [h, Ne.symm h]

@[simp]
lemma iwEstimator_apply_self : iwEstimator p b y b = y / p b := by simp [iwEstimator_def]

@[simp]
lemma iwEstimator_apply_of_ne (h : a ≠ b) : iwEstimator p b y a = 0 := by
  simp [iwEstimator_def, h]

/-- The importance-weighted estimate of a nonnegative reward is nonnegative. -/
lemma iwEstimator_nonneg (hp : 0 ≤ p b) (hy : 0 ≤ y) : 0 ≤ iwEstimator p b y a := by
  rw [iwEstimator_apply]
  split_ifs with h
  · subst h
    exact div_nonneg hy hp
  · exact le_rfl

/-- The importance-weighted estimate of a reward at most `1` is at most `1 / p a`. -/
lemma iwEstimator_le_one_div (ha : 0 ≤ p a) (hy : y ≤ 1) : iwEstimator p b y a ≤ 1 / p a := by
  rw [iwEstimator_apply]
  split_ifs
  · exact div_le_div_of_nonneg_right hy ha
  · positivity

/-- The norm of the importance-weighted estimate of a reward in `[0, 1]` is at most
`Pi.single a 1 b / p b`: at most `1 / p a` if the arm `a` is drawn, and `0` otherwise. -/
lemma norm_iwEstimator_le_single_div (hp : 0 ≤ p b) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖iwEstimator p b y a‖ ≤ (Pi.single a 1 : α → ℝ) b / p b := by
  rw [iwEstimator_apply]
  split_ifs with hab
  · subst hab
    rw [Pi.single_eq_same, Real.norm_of_nonneg (div_nonneg hy0 hp)]
    exact div_le_div_of_nonneg_right hy1 hp
  · rw [Pi.single_eq_of_ne (Ne.symm hab), zero_div, norm_zero]

/-- For nonnegative weights `p` and a reward `y ∈ [0, 1]`, a coefficient `0 ≤ c ≤ 2 γ` that
vanishes if `p a = 0` times the importance-weighted estimate of `y` at `a` is at most
`2 (γ / p a)`, the bound required by the concentration of implicit-exploration estimates
[LS, Lemma 12.2]. -/
lemma mul_iwEstimator_le_two_mul_div {c : ℝ} (hp : ∀ b, 0 ≤ p b) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hc0 : 0 ≤ c) (hcγ : c ≤ 2 * γ) (hcp : p a = 0 → c = 0) :
    c * iwEstimator p b y a ≤ 2 * (γ / p a) := by
  rcases (hp a).eq_or_lt with hpa | hpa
  · simp [hcp hpa.symm, ← hpa]
  calc c * iwEstimator p b y a ≤ 2 * γ * (1 / p a) :=
        mul_le_mul hcγ (iwEstimator_le_one_div hpa.le hy1) (iwEstimator_nonneg (hp b) hy0)
          (hc0.trans hcγ)
    _ = 2 * (γ / p a) := by ring

/-- The importance-weighted estimates of two different arms multiply to `0`: at most one of them,
that of the drawn arm, is nonzero. -/
lemma iwEstimator_mul_iwEstimator_of_ne {a a' : α} (h : a ≠ a') :
    iwEstimator p b y a * iwEstimator p b y a' = 0 := by
  rcases eq_or_ne a b with rfl | ha
  · simp [iwEstimator_apply_of_ne h.symm]
  · simp [iwEstimator_apply_of_ne ha]

/-- The importance-weighted estimate for the weights `p` with the discount `1 / (1 + γ / p a)` of
[LS, Lemma 12.2] is the implicit-exploration estimate for the weights `p + γ`. -/
lemma iwEstimator_div_one_add_div (ha : 0 < p a) :
    iwEstimator p b y a / (1 + γ / p a) = iwEstimator (fun c ↦ p c + γ) b y a := by
  rw [iwEstimator_apply, iwEstimator_apply]
  split_ifs
  · field_simp
  · simp

/-- The **loss-based importance-weighted estimator** [LS, (11.6)]: when the arm `b` is drawn from
the probability vector `p` and its reward `y` is observed, the estimate of the reward of arm `a` is
`1 - 𝟙{b = a} (1 - y) / p a`, that is, one minus the importance-weighted estimate of the loss
`1 - y`. -/
noncomputable def lossIwEstimator (p : α → ℝ) (b : α) (y : ℝ) : α → ℝ :=
  1 - iwEstimator p b (1 - y)

lemma lossIwEstimator_def (p : α → ℝ) (b : α) (y : ℝ) :
    lossIwEstimator p b y = 1 - iwEstimator p b (1 - y) := (rfl)

@[simp]
lemma lossIwEstimator_apply : lossIwEstimator p b y a = 1 - iwEstimator p b (1 - y) a := by
  simp [lossIwEstimator_def]

/-- The loss-based estimate is at most `1` for a reward at most `1`. -/
lemma lossIwEstimator_le_one (hp : 0 ≤ p b) (hy : y ≤ 1) : lossIwEstimator p b y a ≤ 1 := by
  rw [lossIwEstimator_apply, sub_le_self_iff, iwEstimator_apply]
  split_ifs with h
  · subst h
    exact div_nonneg (sub_nonneg.2 hy) hp
  · exact le_rfl

variable [MeasurableSpace α] [MeasurableSingletonClass α]

@[fun_prop]
lemma measurable_iwEstimator :
    Measurable fun z : (α → ℝ) × α × ℝ ↦ iwEstimator z.1 z.2.1 z.2.2 := by
  refine measurable_pi_iff.2 fun a ↦ ?_
  simp_rw [iwEstimator_apply, eq_comm (a := a)]
  exact Measurable.ite ((measurableSet_singleton a).preimage (measurable_fst.comp measurable_snd))
    ((measurable_snd.comp measurable_snd).div ((measurable_pi_apply a).comp measurable_fst))
    measurable_const

@[fun_prop]
lemma measurable_lossIwEstimator :
    Measurable fun z : (α → ℝ) × α × ℝ ↦ lossIwEstimator z.1 z.2.1 z.2.2 := by
  simp_rw [lossIwEstimator_def]
  exact measurable_const.sub (measurable_iwEstimator.comp (measurable_fst.prodMk
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_const.sub (measurable_snd.comp measurable_snd)))))

end Estimator

section Sum

variable [Fintype α]

/-- The `p`-average of the importance-weighted estimates is the observed reward. -/
lemma sum_mul_iwEstimator (hb : p b ≠ 0) : ∑ a, p a * iwEstimator p b y a = y := by
  simp [iwEstimator_def, Pi.single_apply, mul_div_cancel₀ _ hb]

/-- The `e`-weighted sum of the importance-weighted estimates is `e b * y / p b`. -/
@[simp]
lemma dotProduct_iwEstimator (e : α → ℝ) : e ⬝ᵥ iwEstimator p b y = e b * y / p b := by
  rw [iwEstimator_def, dotProduct_single, mul_div_assoc]

/-- For weights `e` summing to `1`, such as the advice of an expert, the `e`-average of the
loss-based estimates is `1 - e b * (1 - y) / p b`. -/
lemma dotProduct_lossIwEstimator {e : α → ℝ} (he : ∑ a, e a = 1) :
    e ⬝ᵥ lossIwEstimator p b y = 1 - e b * (1 - y) / p b := by
  rw [lossIwEstimator_def, dotProduct_sub, dotProduct_iwEstimator, dotProduct_one, he]

/-- The sum of the importance-weighted estimates over the arms is `y / p b`. -/
lemma sum_iwEstimator : ∑ a, iwEstimator p b y a = y / p b := by
  simpa only [one_dotProduct, Pi.one_apply, one_mul] using dotProduct_iwEstimator (p := p) (b := b)
    (y := y) 1

/-- The `p`-average of the squared importance-weighted estimates is `y ^ 2 / p b`. -/
lemma sum_mul_iwEstimator_sq : ∑ a, p a * iwEstimator p b y a ^ 2 = y ^ 2 / p b := by
  rw [Finset.sum_eq_single b (fun a _ ha ↦ by simp [ha]) (by simp), iwEstimator_apply_self]
  rcases eq_or_ne (p b) 0 with hb | hb
  · simp [hb]
  · field_simp

/-- **Bias of the implicit-exploration estimator** [LS, proof of Lemma 12.4]: the observed loss `y`
exceeds the `p`-average of its importance-weighted estimates for the weights `p + γ` by `γ` times
their sum. -/
lemma sub_sum_mul_iwEstimator_add (hb : p b + γ ≠ 0) :
    y - ∑ a, p a * iwEstimator (fun c ↦ p c + γ) b y a =
      γ * ∑ a, iwEstimator (fun c ↦ p c + γ) b y a := by
  have hp : ∑ a, p a * iwEstimator (fun c ↦ p c + γ) b y a = p b * y / (p b + γ) := by
    simpa only [dotProduct] using dotProduct_iwEstimator (p := fun c ↦ p c + γ) (b := b) (y := y) p
  rw [hp, sum_iwEstimator]
  field_simp
  ring

/-- For a loss `y ∈ [0, 1]` and `γ ≥ 0`, the `p`-average of the squared importance-weighted
estimates for the weights `p + γ` is at most their sum. -/
lemma sum_mul_iwEstimator_add_sq_le (hp : 0 ≤ p b) (hγ : 0 ≤ γ) (hb : 0 < p b + γ)
    (hy : y ∈ Set.Icc 0 1) :
    ∑ a, p a * iwEstimator (fun c ↦ p c + γ) b y a ^ 2 ≤
      ∑ a, iwEstimator (fun c ↦ p c + γ) b y a := by
  rw [Finset.sum_eq_single b (fun a _ ha ↦ by simp [ha]) (by simp), iwEstimator_apply_self,
    sum_iwEstimator, div_pow, mul_div_assoc', div_le_div_iff₀ (pow_pos hb 2) hb]
  have : p b * y ^ 2 ≤ y * (p b + γ) := by
    nlinarith [mul_nonneg (mul_nonneg hp hy.1) (sub_nonneg.2 hy.2), mul_nonneg hy.1 hγ]
  nlinarith [mul_le_mul_of_nonneg_right this hb.le]

/-- The `p`-average of the loss-based importance-weighted estimates is the observed reward. -/
lemma sum_mul_lossIwEstimator (hp : ∑ a, p a = 1) (hb : p b ≠ 0) :
    ∑ a, p a * lossIwEstimator p b y a = y := by
  simp [mul_sub, sum_sub_distrib, hp, sum_mul_iwEstimator hb]

/-- Averaged over the drawn arm `b ∼ p`, the importance-weighted estimate of the reward of an arm
`a` with `p a ≠ 0` is unbiased. -/
lemma sum_mul_iwEstimator_apply (ha : p a ≠ 0) : ∑ b, p b * iwEstimator p b (x b) a = x a := by
  rw [Finset.sum_eq_single a (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp)]
  simp [mul_div_cancel₀ _ ha]

/-- Averaged over the drawn arm `b ∼ p`, the loss-based importance-weighted estimate of the reward
of an arm `a` with `p a ≠ 0` is unbiased. -/
lemma sum_mul_lossIwEstimator_apply (hp : ∑ b, p b = 1) (ha : p a ≠ 0) :
    ∑ b, p b * lossIwEstimator p b (x b) a = x a := by
  simp only [lossIwEstimator_apply, mul_sub, mul_one, sum_sub_distrib, hp]
  rw [sum_mul_iwEstimator_apply (x := fun b ↦ 1 - x b) ha]
  ring

/-- Averaged over the drawn arm `b ∼ p`, the absolute value of the importance-weighted estimate of
the reward of an arm `a` is at most `|x a|`. -/
lemma sum_mul_abs_iwEstimator_apply_le (ha : 0 ≤ p a) :
    ∑ b, p b * |iwEstimator p b (x b) a| ≤ |x a| := by
  rw [Finset.sum_eq_single a (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp), iwEstimator_apply_self,
    abs_div, abs_of_nonneg ha]
  rcases ha.eq_or_lt with ha | ha
  · simp [← ha]
  · rw [mul_div_cancel₀ _ ha.ne']

/-- The variance of the importance-weighted estimate of the reward of an arm `a` with `p a ≠ 0`,
over the drawn arm `b ∼ p`, is `x a ^ 2 * (1 - p a) / p a`. -/
lemma sum_mul_iwEstimator_apply_sub_sq (hp : ∑ b, p b = 1) (ha : p a ≠ 0) :
    ∑ b, p b * (iwEstimator p b (x b) a - x a) ^ 2 = x a ^ 2 * (1 - p a) / p a := by
  rw [← Finset.add_sum_erase _ _ (mem_univ a)] at hp ⊢
  have hrest : ∑ b ∈ univ.erase a, p b * (iwEstimator p b (x b) a - x a) ^ 2 =
      (1 - p a) * x a ^ 2 := by
    rw [← eq_sub_of_add_eq' hp, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    simp [Ne.symm (Finset.ne_of_mem_erase hb)]
  rw [hrest, iwEstimator_apply_self]
  field_simp
  ring

/-- The `p`-average, over the drawn arm `b ∼ p`, of the `f`-weighted sum
`∑ a, f a * (iwEstimator p b (x b) a - x a) ^ 2` of the squared deviations of the
importance-weighted estimates is `∑ a, f a * (x a ^ 2 * (1 - p a) / p a)`, for coefficients `f`
that vanish on the arms of weight zero. -/
lemma sum_mul_sum_mul_iwEstimator_apply_sub_sq (hp : ∑ b, p b = 1) {f : α → ℝ}
    (hf : ∀ a, p a = 0 → f a = 0) :
    ∑ b, p b * ∑ a, f a * (iwEstimator p b (x b) a - x a) ^ 2 =
      ∑ a, f a * (x a ^ 2 * (1 - p a) / p a) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases ha : p a = 0
  · simp [hf a ha]
  rw [← sum_mul_iwEstimator_apply_sub_sq hp ha, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ ↦ by ring

/-- The variance of the loss-based importance-weighted estimate of the reward of an arm `a` with
`p a ≠ 0`, over the drawn arm `b ∼ p`, is `(1 - x a) ^ 2 * (1 - p a) / p a`. -/
lemma sum_mul_lossIwEstimator_apply_sub_sq (hp : ∑ b, p b = 1) (ha : p a ≠ 0) :
    ∑ b, p b * (lossIwEstimator p b (x b) a - x a) ^ 2 = (1 - x a) ^ 2 * (1 - p a) / p a := by
  rw [← sum_mul_iwEstimator_apply_sub_sq (x := fun b ↦ 1 - x b) hp ha]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [lossIwEstimator_apply]
  ring

end Sum

section Feedback

variable {𝓞 Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {O : ℕ → Ω → 𝓞}
  {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {n : ℕ}

omit [DecidableEq α] in
/-- If the feedback `Y n` of round `n` is almost surely the reward `x (A n)` of the action, then a
function `g (past, A n, Y n)` of the past (history and observation), the action and the feedback
of round `n` is almost surely `g (past, A n, x (A n))`. -/
lemma comp_feedback_ae_eq (hY : Y n =ᵐ[P] x ∘ A n) (g : Hist 𝓞 α ℝ n × 𝓞 → α → ℝ → E) :
    (fun ω ↦ g (history O A Y n ω, O n ω) (A n ω) (Y n ω)) =ᵐ[P]
      fun ω ↦ g (history O A Y n ω, O n ω) (A n ω) (x (A n ω)) := by
  filter_upwards [hY] with ω hω
  rw [hω, Function.comp_apply]

omit [DecidableEq α] in
/-- Along a run of an algorithm with finitely many actions whose feedback at round `n` is almost
surely the reward `x (A n)` of its action, the feedback of round `n` is integrable. -/
lemma _root_.Learning.IsAlgEnvSeq.integrable_feedback_of_ae_eq [MeasurableSpace α]
    [MeasurableSingletonClass α] [Finite α] [MeasurableSpace 𝓞] [IsFiniteMeasure P]
    {alg : Algorithm 𝓞 α ℝ} {env : Environment 𝓞 α ℝ} (h : IsAlgEnvSeq O A Y alg env P)
    (hY : Y n =ᵐ[P] x ∘ A n) :
    Integrable (Y n) P := by
  have := Fintype.ofFinite α
  exact (Integrable.of_bound ((measurable_of_finite x).comp
    (h.measurable_action n)).aestronglyMeasurable (∑ a, |x a|) (ae_of_all _ fun ω ↦
      Finset.single_le_sum (f := fun a ↦ |x a|) (fun a _ ↦ abs_nonneg _)
        (Finset.mem_univ (A n ω)))).congr hY.symm

omit [DecidableEq α] in
/-- If the feedback `Y t` of every round `t < n` is almost surely the reward `x t (A t)` of the
action, then almost surely the feedbacks of all the rounds `t < n` are these rewards. -/
lemma ae_forall_feedback_eq {x : ℕ → α → ℝ} (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t) :
    ∀ᵐ ω ∂P, ∀ t < n, Y t ω = x t (A t ω) := by
  refine ae_all_iff.2 fun t ↦ ?_
  by_cases ht : t < n
  · filter_upwards [hY t ht] with ω hω _ using hω
  · exact ae_of_all _ fun _ ht' ↦ absurd ht' ht

omit [DecidableEq α] in
/-- If the feedback `Y t` of every round `t < n` is almost surely the reward `x t (A t)` of the
action and the rewards are at most `1`, then almost surely the feedbacks of the rounds `t < n` are
at most `1`. -/
lemma ae_feedback_le_one {x : ℕ → α → ℝ} (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t)
    (hx : ∀ t < n, ∀ a, x t a ≤ 1) : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ≤ 1 := by
  filter_upwards [ae_forall_feedback_eq hY] with ω hω t ht
  rw [hω t ht]
  exact hx t ht _

omit [DecidableEq α] in
/-- If the feedback `Y t` of every round `t < n` is almost surely the reward `x t (A t)` of the
action and the rewards are in `[0, 1]`, then almost surely the feedbacks of the rounds `t < n` are
in `[0, 1]`. -/
lemma ae_feedback_mem_Icc {x : ℕ → α → ℝ} (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t)
    (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1) : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1 := by
  filter_upwards [ae_forall_feedback_eq hY] with ω hω t ht
  rw [hω t ht]
  exact hx t ht _

omit [DecidableEq α] in
/-- Along a run of an algorithm with finitely many actions whose feedback at round `n` is almost
surely the reward `x (A n)` of its action, the conditional expectation of the feedback given the
past and the action of round `n` is `x (A n)`. -/
lemma _root_.Learning.IsAlgEnvSeq.condExp_feedback_ae_eq_of_ae_eq [MeasurableSpace α]
    [MeasurableSingletonClass α] [Finite α] [MeasurableSpace 𝓞] [IsFiniteMeasure P]
    {alg : Algorithm 𝓞 α ℝ} {env : Environment 𝓞 α ℝ} (h : IsAlgEnvSeq O A Y alg env P)
    (hY : Y n =ᵐ[P] x ∘ A n) :
    P[Y n | h.filtrationAction n] =ᵐ[P] fun ω ↦ x (A n ω) := by
  refine (condExp_congr_ae hY).trans (Filter.EventuallyEq.of_eq ?_)
  have := Fintype.ofFinite α
  exact condExp_of_stronglyMeasurable (h.filtrationAction.le n)
    ((measurable_of_finite x).comp (h.adapted_action_filtrationAction n)).stronglyMeasurable
    ((h.integrable_feedback_of_ae_eq hY).congr hY)

end Feedback

namespace WeightAlgorithm

variable [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {𝓞 : Type*} [MeasurableSpace 𝓞]
  {w : (n : ℕ) → Hist 𝓞 α ℝ n × 𝓞 → α → ℝ} {hw : ∀ n a, Measurable fun x ↦ w n x a}
  {hp : ∀ n x, w n x ∈ simplex α} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsFiniteMeasure P] {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}
  {env : Environment 𝓞 α ℝ} {n : ℕ}

variable {x : α → ℝ} {a : α}

/-- Along a run of a weight-based algorithm whose feedback at round `n` is the reward `x (A n)` of
the action, the importance-weighted estimate of the reward of an arm `a` is integrable. -/
lemma integrable_iwEstimator (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : Y n =ᵐ[P] x ∘ A n) (a : α) :
    Integrable (fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a) P :=
  (integrable_comp_weights h n (g := fun p b ↦ iwEstimator p b (x b) a) (by fun_prop)
    fun p hp ↦ sum_mul_abs_iwEstimator_apply_le ((mem_simplex_iff.1 hp).1 a)).congr
    (comp_feedback_ae_eq hY fun z b y ↦ iwEstimator (w n z) b y a).symm

/-- Along a run of a weight-based algorithm whose feedback at round `n` is the reward `x (A n)` of
the action, the loss-based importance-weighted estimate of the reward of an arm `a` is
integrable. -/
lemma integrable_lossIwEstimator (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : Y n =ᵐ[P] x ∘ A n) (a : α) :
    Integrable (fun ω ↦ lossIwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a) P := by
  refine (integrable_comp_weights h n (g := fun p b ↦ lossIwEstimator p b (x b) a)
    (by fun_prop) (C := 1 + |1 - x a|) fun p hp ↦ ?_).congr
    (comp_feedback_ae_eq hY fun z b y ↦ lossIwEstimator (w n z) b y a).symm
  rw [mem_simplex_iff] at hp
  calc ∑ b, p b * |lossIwEstimator p b (x b) a|
      ≤ ∑ b, p b * (1 + |iwEstimator p b (1 - x b) a|) := by
        refine Finset.sum_le_sum fun b _ ↦ mul_le_mul_of_nonneg_left ?_ (hp.1 b)
        rw [lossIwEstimator_apply]
        exact (abs_sub _ _).trans (by simp)
    _ ≤ 1 + |1 - x a| := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, hp.2, add_le_add_iff_left]
        exact sum_mul_abs_iwEstimator_apply_le (x := fun b ↦ 1 - x b) (hp.1 a)

/-- Along a run of a weight-based algorithm whose feedback at round `n` is almost surely in
`[0, 1]`, in any environment, the importance-weighted estimate of the loss `1 - Y n` at an arm `a`
is integrable. -/
lemma integrable_iwEstimator_one_sub (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : ∀ᵐ ω ∂P, Y n ω ∈ Set.Icc 0 1) (a : α) :
    Integrable
      (fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (1 - Y n ω) a) P := by
  have hwm : Measurable fun ω ↦ w n (history O A Y n ω, O n ω) :=
    (measurable_pi_iff.2 (hw n)).comp ((h.measurable_history n).prodMk (h.measurable_obs n))
  have hm : Measurable
      fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (1 - Y n ω) a :=
    (measurable_pi_apply a).comp (measurable_iwEstimator.comp (hwm.prodMk
      ((h.measurable_action n).prodMk (measurable_const.sub (h.measurable_feedback n)))))
  refine (integrable_div_weights h n (Pi.single a 1)).mono' hm.aestronglyMeasurable ?_
  filter_upwards [hY] with ω hω
  exact norm_iwEstimator_le_single_div ((mem_simplex_iff.1 (hp n _)).1 _) (sub_nonneg.2 hω.2)
    (by linarith [hω.1])

variable [Nonempty α]

omit [DecidableEq α] [Fintype α] [MeasurableSingletonClass α] [IsFiniteMeasure P] [Nonempty α] in
/-- The integral of a function of the feedback against the feedback kernel of round `n` at the
past and an action `b` is measurable in the past. -/
private lemma measurable_integral_feedback {g : ℝ → ℝ} (hg : StronglyMeasurable g) (b : α) :
    Measurable fun x : Hist 𝓞 α ℝ n × 𝓞 ↦ ∫ y, g y ∂env.feedback n (x, b) :=
  (hg.integral_kernel (κ := env.feedback n)).measurable.comp measurable_prodMk_right

/-- **Conditional mean of the importance-weighted estimator** [LS, (11.4)]: along a run of a
weight-based algorithm, let `Z` be an integrable random variable whose conditional expectation
given the past and the action of round `n` is `m (past) (A n)`, such as the feedback of round `n`
with `m` its conditional means. Then the importance-weighted estimate of `Z` at an arm `a` has
conditional expectation given the past `m (past) a` if `a` has positive weight, and `0` if `a` has
weight zero, provided it is integrable. -/
theorem condExp_iwEstimator_eq_ite_of_condExp_eq
    (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P) {Z : Ω → ℝ} (hZ : Integrable Z P)
    {m : Hist 𝓞 α ℝ n × 𝓞 → α → ℝ} (hm : ∀ b, Measurable fun x ↦ m x b)
    (hZm : P[Z | h.filtrationAction n] =ᵐ[P] fun ω ↦ m (history O A Y n ω, O n ω) (A n ω))
    (hint : Integrable
      (fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Z ω) a) P) :
    P[fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Z ω) a
      | h.filtrationObs n] =ᵐ[P] fun ω ↦
        if w n (history O A Y n ω, O n ω) a = 0 then 0 else m (history O A Y n ω, O n ω) a := by
  simp_rw [iwEstimator_apply_eq_ite_mul] at hint ⊢
  filter_upwards [condExp_comp_action_mul h n (f := fun x b ↦ if b = a then (w n x a)⁻¹ else 0)
    (fun b ↦ by split_ifs; exacts [(hw n a).inv, measurable_const]) hm hZ hZm hint] with ω hω
  rw [hω, Finset.sum_eq_single a (fun b _ hb ↦ by simp [hb]) (by simp)]
  simp only [↓reduceIte]
  split_ifs with ha
  · rw [ha, zero_mul]
  · rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]

/-- **Conditional unbiasedness of the importance-weighted estimator** [LS, (11.4)]: along a run of
a weight-based algorithm, let `Z` be an integrable random variable whose conditional expectation
given the past and the action of round `n` is `m (past) (A n)`, such as the feedback of round `n`
with `m` its conditional means. Then the importance-weighted estimate of `Z` at an arm `a` that has
almost surely positive weight has conditional expectation `m (past) a` given the past, provided it
is integrable. -/
theorem condExp_iwEstimator_of_condExp_eq
    (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P) {Z : Ω → ℝ} (hZ : Integrable Z P)
    {m : Hist 𝓞 α ℝ n × 𝓞 → α → ℝ} (hm : ∀ b, Measurable fun x ↦ m x b)
    (hZm : P[Z | h.filtrationAction n] =ᵐ[P] fun ω ↦ m (history O A Y n ω, O n ω) (A n ω))
    (hint : Integrable (fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Z ω) a) P)
    (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a) :
    P[fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Z ω) a
      | h.filtrationObs n] =ᵐ[P] fun ω ↦ m (history O A Y n ω, O n ω) a := by
  filter_upwards [condExp_iwEstimator_eq_ite_of_condExp_eq h hZ hm hZm hint, ha] with ω hω hωa
  rw [hω]
  simp [hωa.ne']

/-- **Conditional unbiasedness of the loss-based importance-weighted estimator** [LS, Section 11.2]:
along a run of a weight-based algorithm, let `Z` be an integrable random variable whose conditional
expectation given the past and the action of round `n` is `m (past) (A n)`. Then the loss-based
importance-weighted estimate of `Z` at an arm `a` that has almost surely positive weight has
conditional expectation `m (past) a` given the past, provided it is integrable. -/
theorem condExp_lossIwEstimator_of_condExp_eq
    (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P) {Z : Ω → ℝ} (hZ : Integrable Z P)
    {m : Hist 𝓞 α ℝ n × 𝓞 → α → ℝ} (hm : ∀ b, Measurable fun x ↦ m x b)
    (hZm : P[Z | h.filtrationAction n] =ᵐ[P] fun ω ↦ m (history O A Y n ω, O n ω) (A n ω))
    (hint : Integrable
      (fun ω ↦ lossIwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Z ω) a) P)
    (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a) :
    P[fun ω ↦ lossIwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Z ω) a
      | h.filtrationObs n] =ᵐ[P] fun ω ↦ m (history O A Y n ω, O n ω) a := by
  -- the loss-based estimate of `Z` is `1` minus the importance-weighted estimate of `1 - Z`
  have hint' : Integrable
      (fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (1 - Z ω) a) P :=
    ((integrable_const 1).sub hint).congr (ae_of_all _ fun ω ↦ by simp)
  have hZm' : P[fun ω ↦ 1 - Z ω | h.filtrationAction n] =ᵐ[P]
      fun ω ↦ 1 - m (history O A Y n ω, O n ω) (A n ω) := by
    filter_upwards [condExp_const_sub (h.filtrationAction.le n) hZ 1, hZm] with ω h1 h2
    rw [h1, h2]
  filter_upwards [condExp_const_sub (h.filtrationObs.le n) hint' 1,
    condExp_iwEstimator_of_condExp_eq h (Z := fun ω ↦ 1 - Z ω) ((integrable_const 1).sub hZ)
      (m := fun x b ↦ 1 - m x b) (fun b ↦ measurable_const.sub (hm b)) hZm' hint' ha] with ω h1 h2
  simp only [lossIwEstimator_apply]
  rw [h1, h2]
  ring

/-- **Conditional unbiasedness of the importance-weighted estimator** [LS, (11.4)] in any
environment: along a run of a weight-based algorithm with integrable feedback at round `n`, the
importance-weighted estimate of the feedback at an arm `a` that has almost surely positive weight
has conditional expectation `env.means O A Y a n` given the past, the mean of the feedback of `a`
at round `n` given the past, provided it is integrable. -/
theorem condExp_iwEstimator (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : Integrable (Y n) P)
    (hint : Integrable (fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a) P)
    (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a) :
    P[fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a
      | h.filtrationObs n] =ᵐ[P] fun ω ↦ env.means O A Y a n ω := by
  filter_upwards [condExp_iwEstimator_of_condExp_eq h hY
    (m := fun x b ↦ ∫ y, y ∂env.feedback n (x, b))
    (measurable_integral_feedback stronglyMeasurable_id)
    (h.condExp_feedback_comp n stronglyMeasurable_id hY) hint ha] with ω hω
  rw [hω, Environment.means_eq_integral]

/-- **Conditional unbiasedness of the loss-based importance-weighted estimator** [LS, Section 11.2]
in any environment: along a run of a weight-based algorithm with integrable feedback at round `n`,
the loss-based importance-weighted estimate of the feedback at an arm `a` that has almost surely
positive weight has conditional expectation `env.means O A Y a n` given the past, provided it is
integrable. -/
theorem condExp_lossIwEstimator (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : Integrable (Y n) P)
    (hint : Integrable
      (fun ω ↦ lossIwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a) P)
    (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a) :
    P[fun ω ↦ lossIwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a
      | h.filtrationObs n] =ᵐ[P] fun ω ↦ env.means O A Y a n ω := by
  filter_upwards [condExp_lossIwEstimator_of_condExp_eq h hY
    (m := fun x b ↦ ∫ y, y ∂env.feedback n (x, b))
    (measurable_integral_feedback stronglyMeasurable_id)
    (h.condExp_feedback_comp n stronglyMeasurable_id hY) hint ha] with ω hω
  rw [hω, Environment.means_eq_integral]

/-- Along a run of a weight-based algorithm whose feedback at round `n` is the reward `x (A n)` of
the action, the importance-weighted estimate of the reward of an arm `a` that has almost surely
positive weight has expectation `x a`. -/
theorem integral_iwEstimator [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : Y n =ᵐ[P] x ∘ A n) (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a) :
    P[fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a] = x a := by
  have hYint := h.integrable_feedback_of_ae_eq hY
  rw [← integral_condExp (h.filtrationObs.le n), integral_congr_ae
    (condExp_iwEstimator_of_condExp_eq h hYint (m := fun _ b ↦ x b) (fun _ ↦ measurable_const)
      (h.condExp_feedback_ae_eq_of_ae_eq hY) (integrable_iwEstimator h hY a) ha)]
  simp

/-- Along a run of a weight-based algorithm whose feedback at round `n` is the reward `x (A n)` of
the action, the loss-based importance-weighted estimate of the reward of an arm `a` that has almost
surely positive weight has expectation `x a`. -/
theorem integral_lossIwEstimator [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : Y n =ᵐ[P] x ∘ A n) (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a) :
    P[fun ω ↦ lossIwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a] = x a := by
  have hYint := h.integrable_feedback_of_ae_eq hY
  rw [← integral_condExp (h.filtrationObs.le n), integral_congr_ae
    (condExp_lossIwEstimator_of_condExp_eq h hYint (m := fun _ b ↦ x b) (fun _ ↦ measurable_const)
      (h.condExp_feedback_ae_eq_of_ae_eq hY) (integrable_lossIwEstimator h hY a) ha)]
  simp

/-- **Conditional variance of the importance-weighted estimator** [LS, (11.5)]: along a run of a
weight-based algorithm, let `Z` be a square-integrable random variable whose conditional
expectation and conditional second moment given the past and the action of round `n` are
`m (past) (A n)` and `s (past) (A n)`. Then the importance-weighted estimate of `Z` at an arm `a`
with almost surely positive weight `P_a` has conditional variance
`s (past) a / P_a - m (past) a ^ 2` given the past, provided it is square-integrable. -/
theorem condVar_iwEstimator_of_condExp_eq
    (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P) {Z : Ω → ℝ} (hZ : MemLp Z 2 P)
    {m s : Hist 𝓞 α ℝ n × 𝓞 → α → ℝ} (hm : ∀ b, Measurable fun x ↦ m x b)
    (hs : ∀ b, Measurable fun x ↦ s x b)
    (hZm : P[Z | h.filtrationAction n] =ᵐ[P] fun ω ↦ m (history O A Y n ω, O n ω) (A n ω))
    (hZs : P[fun ω ↦ Z ω ^ 2 | h.filtrationAction n] =ᵐ[P]
      fun ω ↦ s (history O A Y n ω, O n ω) (A n ω))
    (hint : MemLp (fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Z ω) a) 2 P)
    (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a) :
    Var[fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Z ω) a;
      P | h.filtrationObs n] =ᵐ[P] fun ω ↦ s (history O A Y n ω, O n ω) a /
        w n (history O A Y n ω, O n ω) a - m (history O A Y n ω, O n ω) a ^ 2 := by
  -- the square of the estimate is `𝟙{A n = a} / P_a ^ 2` times `Z ^ 2`
  have hsq : ∀ (p : α → ℝ) b y, iwEstimator p b y a ^ 2 = (if b = a then (p a)⁻¹ ^ 2 else 0) *
      y ^ 2 := fun p b y ↦ by
    rw [iwEstimator_apply_eq_ite_mul]
    split_ifs <;> ring
  have h2 : P[(fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Z ω) a) ^ 2
      | h.filtrationObs n] =ᵐ[P]
        fun ω ↦ s (history O A Y n ω, O n ω) a / w n (history O A Y n ω, O n ω) a := by
    have hint2 := hint.integrable_sq
    simp only [Pi.pow_def, hsq] at hint2 ⊢
    filter_upwards [condExp_comp_action_mul h n
      (f := fun x b ↦ if b = a then (w n x a)⁻¹ ^ 2 else 0)
      (fun b ↦ by split_ifs; exacts [(hw n a).inv.pow_const 2, measurable_const]) hs
      hZ.integrable_sq hZs hint2, ha] with ω hω hωa
    rw [hω, Finset.sum_eq_single a (fun b _ hb ↦ by simp [hb]) (by simp)]
    simp only [ite_true]
    field_simp
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp (h.filtrationObs.le n) hint, h2,
    condExp_iwEstimator_of_condExp_eq h (hZ.integrable one_le_two) hm hZm
      (hint.integrable one_le_two) ha] with ω h1 h2 h3
  rw [h1, Pi.sub_apply, h2, Pi.pow_apply, h3]

/-- **Conditional variance of the importance-weighted estimator** [LS, (11.5)] in any environment:
along a run of a weight-based algorithm with square-integrable feedback at round `n`, the
importance-weighted estimate of the feedback at an arm `a` with almost surely positive weight `P_a`
has conditional variance `E_a[Y ^ 2] / P_a - (env.means O A Y a n) ^ 2` given the past, with
`E_a[Y ^ 2]` the second moment of the feedback of `a` at round `n` given the past, provided it is
square-integrable. Against LML's `Environment.evalSeq g _`, whose feedback of `a` at round `n` is
`x a = g n a`, this is `x a ^ 2 * (1 - P_a) / P_a`. -/
theorem condVar_iwEstimator (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : MemLp (Y n) 2 P)
    (hint : MemLp (fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a) 2 P)
    (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a) :
    Var[fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a;
      P | h.filtrationObs n] =ᵐ[P] fun ω ↦
        (∫ y, y ^ 2 ∂env.feedbackKernel O A Y n ω a) / w n (history O A Y n ω, O n ω) a -
          env.means O A Y a n ω ^ 2 := by
  have hsq : StronglyMeasurable fun y : ℝ ↦ y ^ 2 := (continuous_pow 2).stronglyMeasurable
  filter_upwards [condVar_iwEstimator_of_condExp_eq h hY
    (m := fun x b ↦ ∫ y, y ∂env.feedback n (x, b))
    (s := fun x b ↦ ∫ y, y ^ 2 ∂env.feedback n (x, b))
    (measurable_integral_feedback stronglyMeasurable_id)
    (measurable_integral_feedback hsq)
    (h.condExp_feedback_comp n stronglyMeasurable_id (hY.integrable one_le_two))
    (h.condExp_feedback_comp n hsq hY.integrable_sq) hint ha] with ω hω
  rw [hω, Environment.means_eq_integral, Environment.feedbackKernel_apply]

/-- **Conditional variance of the loss-based importance-weighted estimator** [LS, Section 11.2] in
any environment: along a run of a weight-based algorithm with square-integrable feedback at round
`n`, the loss-based importance-weighted estimate of the feedback at an arm `a` with almost surely
positive weight `P_a` has conditional variance
`E_a[(1 - Y) ^ 2] / P_a - (1 - env.means O A Y a n) ^ 2` given the past, with `E_a[(1 - Y) ^ 2]`
the conditional second moment of the loss `1 - Y` of `a` at round `n`, provided it is
square-integrable. Against LML's `Environment.evalSeq g _`, whose feedback of `a` at round `n` is
`x a = g n a`, this is `(1 - x a) ^ 2 * (1 - P_a) / P_a`. -/
theorem condVar_lossIwEstimator (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : MemLp (Y n) 2 P)
    (hint : MemLp
      (fun ω ↦ lossIwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a) 2 P)
    (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a) :
    Var[fun ω ↦ lossIwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a;
      P | h.filtrationObs n] =ᵐ[P] fun ω ↦
        (∫ y, (1 - y) ^ 2 ∂env.feedbackKernel O A Y n ω a) / w n (history O A Y n ω, O n ω) a -
          (1 - env.means O A Y a n ω) ^ 2 := by
  -- the loss-based estimate of `Y` is `1` minus the importance-weighted estimate of `1 - Y`
  have hloss : (fun ω ↦ lossIwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a) =
      fun ω ↦ 1 - iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (1 - Y n ω) a := by
    simp
  have hiw : (fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (1 - Y n ω) a) =
      fun ω ↦ 1 - lossIwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a := by
    simp
  have hint' : MemLp
      (fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (1 - Y n ω) a) 2 P := by
    rw [hiw]
    exact (memLp_const 1).sub hint
  have hg : StronglyMeasurable fun y : ℝ ↦ 1 - y :=
    (continuous_const.sub continuous_id).stronglyMeasurable
  have hg2 : StronglyMeasurable fun y : ℝ ↦ (1 - y) ^ 2 :=
    ((continuous_const.sub continuous_id).pow 2).stronglyMeasurable
  have hY1 : Integrable (fun ω ↦ 1 - Y n ω) P := (integrable_const 1).sub (hY.integrable one_le_two)
  -- the conditional mean of the importance-weighted estimate of `1 - Y` is `1 - env.means`
  have hmean : P[fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (1 - Y n ω) a
      | h.filtrationObs n] =ᵐ[P] fun ω ↦ 1 - env.means O A Y a n ω := by
    rw [hiw]
    filter_upwards [condExp_const_sub (h.filtrationObs.le n) (hint.integrable one_le_two) 1,
      condExp_lossIwEstimator h (hY.integrable one_le_two) (hint.integrable one_le_two) ha]
      with ω h1 h2
    rw [h1, h2]
  rw [hloss]
  filter_upwards [condVar_const_sub (h.filtrationObs.le n) (hint'.integrable one_le_two) 1,
    condVar_iwEstimator_of_condExp_eq h (Z := fun ω ↦ 1 - Y n ω) ((memLp_const 1).sub hY)
      (m := fun x b ↦ ∫ y, 1 - y ∂env.feedback n (x, b))
      (s := fun x b ↦ ∫ y, (1 - y) ^ 2 ∂env.feedback n (x, b))
      (measurable_integral_feedback hg) (measurable_integral_feedback hg2)
      (h.condExp_feedback_comp n hg hY1)
      (h.condExp_feedback_comp n hg2 ((memLp_const 1).sub hY).integrable_sq) hint' ha,
    condExp_iwEstimator_of_condExp_eq h (Z := fun ω ↦ 1 - Y n ω) hY1
      (m := fun x b ↦ ∫ y, 1 - y ∂env.feedback n (x, b)) (measurable_integral_feedback hg)
      (h.condExp_feedback_comp n hg hY1) (hint'.integrable one_le_two) ha, hmean]
    with ω h1 h2 h3 h4
  rw [h1, h2, ← h3, h4, Environment.feedbackKernel_apply]

omit [DecidableEq α] in
/-- Along a run of a weight-based algorithm whose feedback at every round `t < n` is almost surely
in `[0, 1]`, in any environment, the second-order terms `(1 - Y t) ^ 2 / w t (past) (A t)` of the
analysis of Exp3 and Exp4 have expectations summing to at most `n k` over the rounds `t < n`, with
`k` the number of arms. -/
lemma sum_integral_one_sub_sq_div_weights_le [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) :
    ∑ t ∈ range n, P[fun ω ↦ (1 - Y t ω) ^ 2 / w t (history O A Y t ω, O t ω) (A t ω)] ≤
      (n * Fintype.card α : ℝ) := by
  calc ∑ t ∈ range n, P[fun ω ↦ (1 - Y t ω) ^ 2 / w t (history O A Y t ω, O t ω) (A t ω)]
  _ ≤ ∑ t ∈ range n, ∑ _b : α, (1 : ℝ) := Finset.sum_le_sum fun t ht ↦ by
      -- each term is at most `1 / w t (past) (A t)`, whose expectation is at most `k`
      refine (integral_mono_of_nonneg (ae_of_all _ fun ω ↦ div_nonneg (sq_nonneg _)
        ((mem_simplex_iff.1 (hp t _)).1 _)) (integrable_div_weights h t fun _ ↦ 1) ?_).trans
        (integral_div_weights_le h t fun _ ↦ zero_le_one)
      filter_upwards [hY] with ω hω
      obtain ⟨h0, h1⟩ := hω t (mem_range.1 ht)
      exact div_le_div_of_nonneg_right (by nlinarith) ((mem_simplex_iff.1 (hp t _)).1 _)
  _ = n * Fintype.card α := by simp

omit [DecidableEq α] in
/-- Along a run of a weight-based algorithm whose feedback at round `n` is integrable and almost
surely nonnegative, in any environment, almost surely the mean `env.means O A Y a n` of the
feedback of every arm `a` of positive weight is nonnegative. -/
lemma ae_means_nonneg_of_weights_pos (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hYint : Integrable (Y n) P) (hY : 0 ≤ᵐ[P] Y n) :
    ∀ᵐ ω ∂P, ∀ a, 0 < w n (history O A Y n ω, O n ω) a → 0 ≤ env.means O A Y a n ω := by
  classical
  refine ae_all_iff.2 fun a ↦ ?_
  have hind : Measurable fun ω ↦ if A n ω = a then (1 : ℝ) else 0 :=
    (measurable_of_finite fun b : α ↦ if b = a then (1 : ℝ) else 0).comp (h.measurable_action n)
  have hint : Integrable (fun ω ↦ (if A n ω = a then (1 : ℝ) else 0) * Y n ω) P :=
    hYint.mono (hind.aestronglyMeasurable.mul hYint.aestronglyMeasurable)
      (ae_of_all _ fun ω ↦ by split_ifs <;> simp)
  have hnn : 0 ≤ᵐ[P] fun ω ↦ (if A n ω = a then (1 : ℝ) else 0) * Y n ω := hY.mono fun ω hω ↦
    mul_nonneg (by split_ifs <;> norm_num) hω
  -- the conditional expectation of `𝟙{A n = a} Y n` given the past is `w a * env.means a`
  filter_upwards [condExp_comp_action_mul h n (f := fun _ b ↦ if b = a then 1 else 0)
      (m := fun x b ↦ ∫ y, y ∂env.feedback n (x, b)) (fun _ ↦ measurable_const)
      (measurable_integral_feedback stronglyMeasurable_id) hYint
      (h.condExp_feedback_comp n stronglyMeasurable_id hYint) hint,
    condExp_nonneg (m := h.filtrationObs n) hnn] with ω h1 h2 hwa
  rw [h1] at h2
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h2
  rw [Environment.means_eq_integral]
  exact nonneg_of_mul_nonneg_right h2 hwa

omit [DecidableEq α] in
/-- Along a run of a weight-based algorithm whose feedback at every round `t < n` is almost surely
in `[0, 1]`, in any environment, almost surely the means `env.means O A Y a t` of the feedbacks
of the arms `a` of positive weight at the rounds `t < n` are nonnegative. -/
lemma ae_forall_means_nonneg_of_weights_pos
    (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) :
    ∀ᵐ ω ∂P, ∀ t < n, ∀ a, 0 < w t (history O A Y t ω, O t ω) a →
      0 ≤ env.means O A Y a t ω := by
  refine ae_all_iff.2 fun t ↦ ?_
  by_cases ht : t < n
  · filter_upwards [ae_means_nonneg_of_weights_pos h
      (Integrable.of_mem_Icc 0 1 (h.measurable_feedback t).aemeasurable
        (hY.mono fun ω hω ↦ hω t ht))
      (hY.mono fun ω hω ↦ (hω t ht).1)] with ω hω _ using hω
  · exact ae_of_all _ fun _ ht' ↦ absurd ht' ht

/-- Along a run of a weight-based algorithm whose feedback at round `n` is integrable, in any
environment, the conditional expectation given the past of the importance-weighted estimate of the
loss `1 - Y n` at an arm `a` is `1 - env.means O A Y a n` if `a` has positive weight, and `0`
otherwise. -/
theorem condExp_iwEstimator_one_sub (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hYint : Integrable (Y n) P)
    (hint : Integrable
      (fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (1 - Y n ω) a) P) :
    P[fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (1 - Y n ω) a
      | h.filtrationObs n] =ᵐ[P] fun ω ↦
        if w n (history O A Y n ω, O n ω) a = 0 then 0 else 1 - env.means O A Y a n ω := by
  have hZm : P[fun ω ↦ 1 - Y n ω | h.filtrationAction n] =ᵐ[P]
      fun ω ↦ 1 - ∫ y, y ∂env.feedback n ((history O A Y n ω, O n ω), A n ω) := by
    filter_upwards [condExp_const_sub (h.filtrationAction.le n) hYint 1,
      h.condExp_feedback_comp n stronglyMeasurable_id hYint] with ω h1 h2
    rw [h1]
    exact congrArg (fun z ↦ 1 - z) h2
  filter_upwards [condExp_iwEstimator_eq_ite_of_condExp_eq h (Z := fun ω ↦ 1 - Y n ω)
    ((integrable_const 1).sub hYint) (m := fun x b ↦ 1 - ∫ y, y ∂env.feedback n (x, b))
    (fun b ↦ measurable_const.sub (measurable_integral_feedback stronglyMeasurable_id b)) hZm
    hint] with ω hω
  rw [hω, Environment.means_eq_integral]

/-- **Unbiasedness of the estimated losses in expectation**, in any environment. Along a run of a
weight-based algorithm whose feedback at round `n` is almost surely in `[0, 1]`, the
importance-weighted estimate of the loss `1 - Y n` at an arm `a` that has almost surely positive
weight has the expectation `E[1 - m_n(a)]` of the loss of `a`, with `m_n(a) = env.means O A Y a n`
the mean feedback of `a` at round `n` given the past. -/
theorem integral_iwEstimator_one_sub (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : ∀ᵐ ω ∂P, Y n ω ∈ Set.Icc 0 1) (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a) :
    P[fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (1 - Y n ω) a] =
      P[fun ω ↦ 1 - env.means O A Y a n ω] := by
  rw [← integral_condExp (h.filtrationObs.le n)]
  refine integral_congr_ae ?_
  filter_upwards [condExp_iwEstimator_one_sub h
    (Integrable.of_mem_Icc 0 1 (h.measurable_feedback n).aemeasurable hY)
    (integrable_iwEstimator_one_sub h hY a), ha] with ω hω hωa
  simp [hω, hωa.ne']

/-- **Concentration of implicit-exploration estimates** [Neu15, Lemma 1; LS, Lemma 12.2], in any
environment. Along a run of a weight-based algorithm with weights `P t = w t (past)` whose
feedback at every round `t < n` is almost surely in `[0, 1]`, let
`Ŷ t a = 𝟙{A t = a} (1 - Y t) / (P t a + γ t)` be the implicit-exploration estimates of the losses
`1 - Y t`, with `μ t a = env.means O A Y a t` the conditional means of the rewards. For
coefficients `c t a` that are
measurable for the past of round `t`, satisfy `0 ≤ c t a ≤ 2 γ t` and vanish on the arms of
weight zero, at the rounds `t < n`, and for `δ > 0`, the probability that
`log (1 / δ) ≤ ∑ t < n, ∑ a, c t a * (Ŷ t a - (1 - μ t a))` is at most `δ`.

The coefficients must vanish on the arms of weight zero: such an arm is almost surely not played,
so the hypothesis on the feedback says nothing about its mean `μ t a`, which may exceed `1`. -/
theorem measure_log_one_div_le_sum_sum_mul_iwEstimator_add_sub_le [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) {γ : ℕ → ℝ} {c : ℕ → α → Ω → ℝ}
    (hc : ∀ t < n, ∀ a, Measurable[h.filtrationObs t] (c t a))
    (hc0 : ∀ t < n, ∀ a ω, 0 ≤ c t a ω) (hcγ : ∀ t < n, ∀ a ω, c t a ω ≤ 2 * γ t)
    (hcw : ∀ t < n, ∀ a ω, w t (history O A Y t ω, O t ω) a = 0 → c t a ω = 0) {δ : ℝ}
    (hδ : 0 < δ) :
    P {ω | Real.log (1 / δ) ≤ ∑ t ∈ range n, ∑ a, c t a ω *
      (iwEstimator (fun b ↦ w t (history O A Y t ω, O t ω) b + γ t) (A t ω) (1 - Y t ω) a -
        (1 - env.means O A Y a t ω))} ≤ ENNReal.ofReal δ := by
  -- We apply `measure_log_one_div_le_sum_sum_mul_div_one_add_sub_le` for the filtration
  -- `h.filtrationObs` to the estimates `X t a` for the weights `P t`, whose conditional means are
  -- `y t a`, with the coefficients `c' t a` and `l t a = γ t / P t a`. All four are set to `0` from
  -- round `n` on, so that only the rounds `t < n` count. Its sum
  -- `∑ t < n, ∑ a, c t a * (X t a / (1 + l t a) - y t a)` is the sum of the statement: the
  -- estimate `X t a / (1 + γ t / P t a)` is the estimate for the weights `P t + γ t`
  -- (`iwEstimator_div_one_add_div`), and `c t a` vanishes where `P t a = 0`.
  set p : ℕ → Ω → α → ℝ := fun t ω ↦ w t (history O A Y t ω, O t ω) with hp_def
  set X : ℕ → α → Ω → ℝ := fun t a ω ↦
    if t < n then iwEstimator (p t ω) (A t ω) (1 - Y t ω) a else 0 with hX
  set y : ℕ → α → Ω → ℝ := fun t a ω ↦
    if t < n then (if p t ω a = 0 then 0 else 1 - env.means O A Y a t ω) else 0 with hy
  set c' : ℕ → α → Ω → ℝ := fun t a ω ↦ if t < n then c t a ω else 0 with hc'
  set l : ℕ → α → Ω → ℝ := fun t a ω ↦ if t < n then γ t / p t ω a else 0 with hl
  have hp0 : ∀ t ω b, 0 ≤ p t ω b := fun t ω ↦ (mem_simplex_iff.1 (hp t _)).1
  have hpm : ∀ t a, Measurable[h.filtrationObs t] fun ω ↦ p t ω a :=
    measurable_weights_filtrationObs h
  have hpv : ∀ t, Measurable[h.filtration t] (p t) := fun t ↦ by
    refine Measurable.mono ?_ (h.filtrationObs_le_filtration t) le_rfl
    rw [h.filtrationObs_eq_comap]
    exact (measurable_pi_iff.2 (hw t)).comp (measurable_iff_comap_le.2 le_rfl)
  have hYint : ∀ t < n, Integrable (Y t) P := fun t ht ↦
    Integrable.of_mem_Icc 0 1 (h.measurable_feedback t).aemeasurable (hY.mono fun ω hω ↦ hω t ht)
  have hXm : ∀ t a, Measurable[h.filtrationObs (t + 1)] (X t a) := fun t a ↦ by
    refine Measurable.mono ?_ (h.filtration_le_filtrationObs_succ t) le_rfl
    simp only [hX]
    split_ifs
    · exact Measurable.comp (mα := h.filtration t) (measurable_pi_apply a)
        (Measurable.comp (mα := h.filtration t) measurable_iwEstimator
          ((hpv t).prodMk ((h.adapted_action t).prodMk
            (measurable_const.sub (h.adapted_feedback t)))))
    · exact measurable_const
  have hXint : ∀ t a, Integrable (X t a) P := fun t a ↦ by
    by_cases ht : t < n
    · refine Integrable.mono' (integrable_div_weights h t (Pi.single a 1))
        ((hXm t a).mono (h.filtrationObs.le (t + 1)) le_rfl).aestronglyMeasurable ?_
      filter_upwards [hY] with ω hω
      simp only [hX, ht, ite_true]
      exact norm_iwEstimator_le_single_div (hp0 t ω _) (sub_nonneg.2 (hω t ht).2)
        (sub_le_self _ (hω t ht).1)
    · simp [hX, ht]
  have hX0 : ∀ t a, 0 ≤ᵐ[P] X t a := fun t a ↦ by
    filter_upwards [hY] with ω hω
    simp only [hX, Pi.zero_apply]
    split_ifs with ht
    · exact iwEstimator_nonneg (hp0 t ω _) (sub_nonneg.2 (hω t ht).2)
    · exact le_rfl
  have hXy : ∀ t a, P[X t a | h.filtrationObs t] ≤ᵐ[P] y t a := fun t a ↦ by
    by_cases ht : t < n
    · have hXt : X t a = fun ω ↦ iwEstimator (w t (history O A Y t ω, O t ω)) (A t ω)
          (1 - Y t ω) a := by
        funext ω
        simp [hX, ht, hp_def]
      rw [hXt]
      refine (condExp_iwEstimator_one_sub h (hYint t ht) (hXt ▸ hXint t a)).le.trans ?_
      exact ae_of_all _ fun ω ↦ by simp [hy, ht, hp_def]
    · have : X t a = 0 := by
        funext ω
        simp [hX, ht]
      rw [this, condExp_zero]
      exact ae_of_all _ fun ω ↦ by simp [hy, ht]
  have hym : ∀ t a, Measurable[h.filtrationObs t] (y t a) := fun t a ↦ by
    simp only [hy]
    split_ifs
    · exact Measurable.ite (measurableSet_eq_fun (hpm t a) measurable_const) measurable_const
        (measurable_const.sub (h.measurable_means_filtrationObs a))
    · exact measurable_const
  have hc'm : ∀ t a, Measurable[h.filtrationObs t] (c' t a) := fun t a ↦ by
    simp only [hc']
    split_ifs with ht
    · exact hc t ht a
    · exact measurable_const
  have hlm : ∀ t a, Measurable[h.filtrationObs (t + 1)] (l t a) := fun t a ↦ by
    simp only [hl]
    split_ifs
    · exact measurable_const.div
        ((hpm t a).mono (h.filtrationObs.mono (Nat.le_succ t)) le_rfl)
    · exact measurable_const
  have hwl : ∀ t a, ∀ᵐ ω ∂P, c' t a ω * X t a ω ≤ 2 * l t a ω := fun t a ↦ by
    filter_upwards [hY] with ω hω
    simp only [hc', hX, hl]
    split_ifs with ht
    · exact mul_iwEstimator_le_two_mul_div (hp0 t ω) (sub_nonneg.2 (hω t ht).2)
        (sub_le_self _ (hω t ht).1) (hc0 t ht a ω) (hcγ t ht a ω) (hcw t ht a ω)
    · simp
  have hmul : ∀ t i j, i ≠ j → ∀ᵐ ω ∂P, c' t i ω * X t i ω * (c' t j ω * X t j ω) = 0 :=
    fun t i j hij ↦ ae_of_all _ fun ω ↦ by
      simp only [hX]
      split_ifs
      · rw [mul_mul_mul_comm, iwEstimator_mul_iwEstimator_of_ne hij, mul_zero]
      · simp
  have key := measure_log_one_div_le_sum_sum_mul_div_one_add_sub_le (ℱ := h.filtrationObs)
    hXm hXint hX0 hXy hc'm hlm hym
    (fun t a ↦ ae_of_all _ fun ω ↦ by
      simp only [hc']
      split_ifs with ht
      exacts [hc0 t ht a ω, le_rfl]) hwl hmul hδ n
  -- the sum of the concentration inequality is the sum of the statement
  refine le_trans (measure_mono fun ω hω ↦ ?_) key
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine hω.trans_eq (Finset.sum_congr rfl fun t ht ↦ Finset.sum_congr rfl fun a _ ↦ ?_)
  have ht' := mem_range.1 ht
  rcases (hp0 t ω a).eq_or_lt with hpa | hpa
  · simp [hc', hcw t ht' a ω hpa.symm]
  · simp only [hc', hX, hy, hl, ht', ite_true, hpa.ne', ite_false]
    rw [iwEstimator_div_one_add_div hpa]

/-- **Concentration of the sums of the implicit-exploration estimates** [Neu15, Lemma 1], in any
environment. Along a run of a weight-based algorithm with weights `P t = w t (past)` whose
feedback at every round `t < n` is almost surely in `[0, 1]`, with
`Ŷ t a = 𝟙{A t = a} (1 - Y t) / (P t a + γ t)` the implicit-exploration estimates of the losses
`1 - Y t`, for coefficients `0 ≤ b t ≤ 2 γ t` at the rounds `t < n` and `δ > 0`, the probability
that `k ∑ t < n, b t + log (1 / δ) ≤ ∑ t < n, b t * ∑ a, Ŷ t a` is at most `δ`, with `k` the
number of arms. -/
theorem measure_add_le_sum_mul_sum_iwEstimator_le [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) {γ b : ℕ → ℝ} (hb : ∀ t < n, 0 ≤ b t)
    (hbγ : ∀ t < n, b t ≤ 2 * γ t) {δ : ℝ} (hδ : 0 < δ) :
    P {ω | Fintype.card α * ∑ t ∈ range n, b t + Real.log (1 / δ) ≤ ∑ t ∈ range n, b t *
        ∑ a, iwEstimator (fun a ↦ w t (history O A Y t ω, O t ω) a + γ t) (A t ω) (1 - Y t ω) a} ≤
      ENNReal.ofReal δ := by
  set p : ℕ → Ω → α → ℝ := fun t ω ↦ w t (history O A Y t ω, O t ω) with hp_def
  set Yh : ℕ → Ω → α → ℝ := fun t ω ↦
    iwEstimator (fun a ↦ p t ω a + γ t) (A t ω) (1 - Y t ω) with hYh
  -- the coefficients `b t` on the arms of positive weight
  have key := measure_log_one_div_le_sum_sum_mul_iwEstimator_add_sub_le h hY
    (c := fun t a ω ↦ if p t ω a = 0 then 0 else b t)
    (fun t _ a ↦ Measurable.ite
      (measurableSet_eq_fun (measurable_weights_filtrationObs h t a) measurable_const)
      measurable_const measurable_const)
    (fun t ht a ω ↦ by split_ifs; exacts [le_rfl, hb t ht])
    (fun t ht a ω ↦ by split_ifs; exacts [(hb t ht).trans (hbγ t ht), hbγ t ht])
    (fun t _ a ω ha ↦ by simp [hp_def, ha]) hδ
  refine le_trans (measure_mono_ae ?_) key
  filter_upwards [ae_forall_means_nonneg_of_weights_pos h hY,
    ae_all_iff.2 fun t ↦ ae_weights_action_pos h t] with ω hm hA hω
  -- the means are at most `1` on the arms of positive weight
  have h1 : ∑ t ∈ range n, ∑ a, (if p t ω a = 0 then 0 else b t) *
      (1 - env.means O A Y a t ω) ≤ Fintype.card α * ∑ t ∈ range n, b t := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht ↦ ?_
    refine le_trans (Finset.sum_le_sum fun a _ ↦ ?_) (le_of_eq (by simp) :
      ∑ _a : α, b t ≤ Fintype.card α * b t)
    split_ifs with ha
    · simpa using hb t (mem_range.1 ht)
    · have hma := hm t (mem_range.1 ht) a
        (lt_of_le_of_ne ((mem_simplex_iff.1 (hp t _)).1 a) (Ne.symm ha))
      nlinarith [hb t (mem_range.1 ht)]
  -- the estimates vanish outside the drawn arm, which has positive weight
  have h2 : ∑ t ∈ range n, ∑ a, (if p t ω a = 0 then 0 else b t) * Yh t ω a =
      ∑ t ∈ range n, b t * ∑ a, Yh t ω a := by
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rcases eq_or_ne a (A t ω) with rfl | ha
    · simp [hp_def, (hA t).ne']
    · simp [hYh, iwEstimator_apply_of_ne ha]
  have h3 : ∑ t ∈ range n, ∑ a, (if p t ω a = 0 then 0 else b t) *
      (Yh t ω a - (1 - env.means O A Y a t ω)) =
      ∑ t ∈ range n, ∑ a, (if p t ω a = 0 then 0 else b t) * Yh t ω a -
        ∑ t ∈ range n, ∑ a, (if p t ω a = 0 then 0 else b t) * (1 - env.means O A Y a t ω) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  simp only [hYh, hp_def] at h1 h2 h3 ⊢
  linarith

omit [DecidableEq α] in
/-- Along a run of a weight-based algorithm whose feedback at round `n` is almost surely the reward
`x (A n)` of the action, almost surely the mean `env.means O A Y a n` of the feedback of every arm
`a` of positive weight is `x a`. -/
lemma ae_means_eq_of_weights_pos (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : Y n =ᵐ[P] x ∘ A n) :
    ∀ᵐ ω ∂P, ∀ a, 0 < w n (history O A Y n ω, O n ω) a → env.means O A Y a n ω = x a := by
  classical
  have hYint := h.integrable_feedback_of_ae_eq hY
  refine ae_all_iff.2 fun a ↦ ?_
  -- both `env.means O A Y a n` and `x a` are the conditional mean of the estimate of `Y n` at `a`
  filter_upwards [condExp_iwEstimator_eq_ite_of_condExp_eq h hYint
      (m := fun z b ↦ ∫ y, y ∂env.feedback n (z, b))
      (measurable_integral_feedback stronglyMeasurable_id)
      (h.condExp_feedback_comp n stronglyMeasurable_id hYint) (integrable_iwEstimator h hY a),
    condExp_iwEstimator_eq_ite_of_condExp_eq h hYint (m := fun _ b ↦ x b) (fun _ ↦ measurable_const)
      (h.condExp_feedback_ae_eq_of_ae_eq hY) (integrable_iwEstimator h hY a)] with ω h1 h2 ha
  rw [h1] at h2
  simp only [ha.ne', ↓reduceIte] at h2
  rw [Environment.means_eq_integral]
  exact h2

end WeightAlgorithm

end LMLExplore.Bandits
