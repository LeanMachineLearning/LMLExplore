/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.Exp3.Basic
public import LMLExplore.Probability.Martingale.ImplicitExploration

/-!
# Exp3-IX

Exp3-IX [Neu15], [LS, Algorithm 10] is the weight-based algorithm for adversarial bandits with
finitely many arms `α` that plays at round `t` the exponential weights
`P t = softmax (-(η • L̂ t))` of its cumulative loss estimates `L̂ t = ∑ s < t, Ŷ s`, where the
estimates of the losses of round `s` are biased by an implicit-exploration parameter `γ ≥ 0`
[LS, (12.4)]: `Ŷ s a = 𝟙{A s = a} (1 - X s) / (P s a + γ)`, for the arm `A s` drawn from `P s`
and its observed reward `X s`. This is the importance-weighted estimate of the loss `1 - X s`
for the weights `P s + γ`. With `γ = 0` it is Exp3.

Exp3-IX has high-probability regret bounds. For rewards `x t a ∈ [0, 1]`, write
`L t a = ∑ s < t, (1 - x s a)` for the cumulative losses and
`R̂_n = max_a ∑ t < n, (x t a - x t (A t))` for the random regret. The analysis of [LS, §12.2]
bounds the random regret against every arm `a` by
`log k / η + (γ + η / 2) ∑ b, L̂ n b + (L̂ n a - L n a)`, with `k` the number of arms: this
combines the local-norm bound of exponential weights with the bias identity
`∑ t < n, (1 - X t) - ∑ t < n, ⟨P t, Ŷ t⟩ = γ ∑ b, L̂ n b` [LS, Lemma 12.4]. The deviations
`L̂ n a - L n a` and their sum over the arms are at most `log ((k + 1) / δ) / (2 γ)` with
probability at least `1 - δ` [LS, Lemma 12.3], by the concentration of implicit-exploration
estimates [LS, Lemma 12.2]. With `γ = η / 2` and `η = √(2 log (k + 1) / (n k))`, the random regret
is then at most `√(8 n k log (k + 1)) + √(n k / (2 log (k + 1))) log (1 / δ) + log ((k + 1) / δ)`
with probability at least `1 - δ`, and the confidence-dependent learning rate
`η = √((log k + log ((k + 1) / δ)) / (n k))` improves this to
`2 √((2 log (k + 1) + log (1 / δ)) n k) + log ((k + 1) / δ)` [LS, Theorem 12.1].

## Main definitions

* `LMLExplore.Bandits.exp3IXSum η γ n h`: the cumulative loss estimates `L̂ n` of Exp3-IX,
  computed from the history `h` of the first `n` rounds.
* `LMLExplore.Bandits.exp3IXWeights η γ n h`: the weights `P n = softmax (-(η • L̂ n))` of
  Exp3-IX at round `n`.
* `LMLExplore.Bandits.exp3IX η γ`: the Exp3-IX algorithm with learning rate `η` and
  implicit-exploration parameter `γ`.

## Main statements

* `exp3IX_eq_exp3`: Exp3-IX with `γ = 0` is Exp3.
* `Exp3IX.sum_sub_sum_mul_eq_mul_sum`: [LS, Lemma 12.4], the bias of the loss estimates.
* `Exp3IX.sum_sub_exp3IXSum_le`: the pathwise bound on the estimated regret of Exp3-IX.
* `Exp3IX.mul_sum_mul_exp3IXSum_sub_eq`: the weighted deviations of the loss estimates from the
  losses, written as the sum to which the concentration of [LS, Lemma 12.2] applies.
* `Exp3IX.measure_le_sum_mul_exp3IXSum_sub_le`: the concentration of a weighted sum of the
  deviations `L̂ n a - L n a` of the loss estimates from the losses.
* `Exp3IX.measure_le_exp3IXSum_sub_le`, `Exp3IX.measure_le_sum_exp3IXSum_sub_le`: the
  deviations of the loss estimates of one arm and of their sum over the arms [LS, (12.9), (12.8)].
* `Exp3IX.measure_exists_le_exp3IXSum_sub_union_le`: [LS, Lemma 12.3].
* `Exp3IX.measure_exists_le_sum_sub_le`: the high-probability bound on the random regret of
  Exp3-IX for every `η, γ > 0`.
* `Exp3IX.measure_exists_div_add_mul_add_le_sum_sub_le`: the same bound for `γ = η / 2`, in the
  form `L / η + η n k + log ((k + 1) / δ)` from which both bounds of [LS, Theorem 12.1] follow.
* `Exp3IX.measure_exists_sqrt_le_sum_sub_le`, `Exp3IX.measure_exists_two_mul_sqrt_le_sum_sub_le`:
  the two bounds of [LS, Theorem 12.1].
* `exp3IX_measure_exists_sqrt_le_sum_sub_le`, `exp3IX_measure_exists_two_mul_sqrt_le_sum_sub_le`:
  the same bounds for runs against LML's `Environment.evalSeq x _`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
* [Neu15] G. Neu, *Explore no more: improved high-probability regret bounds for non-stochastic
  bandits*, NeurIPS 2015.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real LMLExplore.OnlineLearning

namespace LMLExplore.Bandits

variable {α 𝓞 : Type*} [Fintype α] [DecidableEq α] {η γ : ℝ}

section Weights

/-- The cumulative loss estimates of Exp3-IX with learning rate `η` and implicit-exploration
parameter `γ`, computed from the history `h` of the first `n` rounds: `∑ s < n, Ŷ s` with
`Ŷ s = iwEstimator (P s + γ) (A s) (1 - X s)` the implicit-exploration estimate of the losses of
round `s`, for the action `A s` and the reward `X s` of round `s` of `h` and the weights
`P s = softmax (-(η • ∑ r < s, Ŷ r))` of round `s`. -/
noncomputable def exp3IXSum (η γ : ℝ) : (n : ℕ) → Hist 𝓞 α ℝ n → α → ℝ
  | 0, _ => 0
  | n + 1, h => exp3IXSum η γ n (Fin.init h) +
      iwEstimator (fun a ↦ softmax (-(η • exp3IXSum η γ n (Fin.init h))) a + γ)
        (h (Fin.last n)).action (1 - (h (Fin.last n)).feedback)

/-- The weights of Exp3-IX with learning rate `η` and implicit-exploration parameter `γ` after the
history `h` of the first `n` rounds: the softmax of `-η` times the cumulative loss estimates
`exp3IXSum η γ n h`. -/
noncomputable def exp3IXWeights (η γ : ℝ) (n : ℕ) (h : Hist 𝓞 α ℝ n) : α → ℝ :=
  softmax (-(η • exp3IXSum η γ n h))

lemma exp3IXWeights_def (η γ : ℝ) (n : ℕ) (h : Hist 𝓞 α ℝ n) :
    exp3IXWeights η γ n h = softmax (-(η • exp3IXSum η γ n h)) := (rfl)

@[simp]
lemma exp3IXSum_zero (h : Hist 𝓞 α ℝ 0) : exp3IXSum η γ 0 h = 0 := by
  rw [exp3IXSum]

lemma exp3IXSum_succ (n : ℕ) (h : Hist 𝓞 α ℝ (n + 1)) :
    exp3IXSum η γ (n + 1) h = exp3IXSum η γ n (Fin.init h) +
      iwEstimator (fun a ↦ exp3IXWeights η γ n (Fin.init h) a + γ) (h (Fin.last n)).action
        (1 - (h (Fin.last n)).feedback) := by
  rw [exp3IXSum, exp3IXWeights_def]

/-- The first weights of Exp3-IX are uniform. -/
@[simp]
lemma exp3IXWeights_zero (h : Hist 𝓞 α ℝ 0) :
    exp3IXWeights η γ 0 h = fun _ ↦ (Fintype.card α : ℝ)⁻¹ := by
  simp [exp3IXWeights_def]

lemma exp3IXWeights_pos [Nonempty α] (n : ℕ) (h : Hist 𝓞 α ℝ n) (a : α) :
    0 < exp3IXWeights η γ n h a :=
  softmax_pos _ a

lemma exp3IXWeights_mem_simplex [Nonempty α] (n : ℕ) (h : Hist 𝓞 α ℝ n) :
    exp3IXWeights η γ n h ∈ simplex α :=
  softmax_mem_simplex _

omit [Fintype α] [DecidableEq α] in
/-- `-(η • (n - S))` is `η • S` shifted by the constant `-(η * n)`. -/
private lemma neg_smul_natCast_sub (S : α → ℝ) (n : ℕ) :
    -(η • fun a ↦ (n : ℝ) - S a) = fun a ↦ (η • S) a + -(η * n) := by
  funext a
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- With `γ = 0`, the cumulative loss estimates of Exp3-IX are `n` minus the cumulative reward
estimates of Exp3. -/
lemma exp3IXSum_eq_sub_exp3Sum (n : ℕ) (h : Hist 𝓞 α ℝ n) :
    exp3IXSum η 0 n h = fun a ↦ n - exp3Sum η n h a := by
  induction n with
  | zero => funext a; simp
  | succ n ih =>
    have hw : exp3IXWeights η 0 n (Fin.init h) = exp3Weights η n (Fin.init h) := by
      rw [exp3IXWeights_def, ih, neg_smul_natCast_sub, softmax_add_const, exp3Weights_def]
    rw [exp3IXSum_succ, ih, exp3Sum_succ]
    simp only [add_zero, hw]
    funext a
    simp only [Pi.add_apply, lossIwEstimator_apply, Nat.cast_succ]
    ring

/-- With `γ = 0`, the weights of Exp3-IX are the weights of Exp3. -/
lemma exp3IXWeights_eq_exp3Weights (n : ℕ) (h : Hist 𝓞 α ℝ n) :
    exp3IXWeights η 0 n h = exp3Weights η n h := by
  rw [exp3IXWeights_def, exp3IXSum_eq_sub_exp3Sum, neg_smul_natCast_sub, softmax_add_const,
    exp3Weights_def]

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞]

@[fun_prop]
lemma measurable_exp3IXSum (η γ : ℝ) (n : ℕ) :
    Measurable (exp3IXSum (𝓞 := 𝓞) (α := α) η γ n) := by
  induction n with
  | zero =>
    rw [funext exp3IXSum_zero]
    exact measurable_const
  | succ n ih =>
    have hS := ih.comp (measurable_finInit (β := fun _ ↦ _))
    have hlast : Measurable fun h : Hist 𝓞 α ℝ (n + 1) ↦ h (Fin.last n) := measurable_pi_apply _
    have hP : Measurable fun h : Hist 𝓞 α ℝ (n + 1) ↦
        fun a ↦ exp3IXWeights η γ n (Fin.init h) a + γ := by
      simp_rw [exp3IXWeights_def]
      exact measurable_pi_iff.2 fun a ↦ ((measurable_pi_apply a).comp
        (measurable_softmax.comp (hS.const_smul η).neg)).add_const γ
    rw [funext (exp3IXSum_succ n)]
    exact hS.add (measurable_iwEstimator.comp (hP.prodMk
      ((Round.measurable_action.comp hlast).prodMk
        (measurable_const.sub (Round.measurable_feedback.comp hlast)))))

@[fun_prop]
lemma measurable_exp3IXWeights (η γ : ℝ) (n : ℕ) :
    Measurable (exp3IXWeights (𝓞 := 𝓞) (α := α) η γ n) :=
  measurable_softmax.comp ((measurable_exp3IXSum η γ n).const_smul η).neg

end Weights

section Algorithm

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] [Nonempty α]

/-- **Exp3-IX** with learning rate `η` and implicit-exploration parameter `γ` [LS, Algorithm 10]:
the weight-based algorithm that draws its action of round `n` from the weights
`exp3IXWeights η γ n h`, the exponential weights of `-η` times the cumulative
implicit-exploration loss estimates computed from the history `h`. It ignores the observations. -/
noncomputable def exp3IX (η γ : ℝ) : Algorithm 𝓞 α ℝ :=
  weightAlgorithm (fun n x ↦ exp3IXWeights η γ n x.1)
    (fun n a ↦ (measurable_pi_apply a).comp ((measurable_exp3IXWeights η γ n).comp measurable_fst))
    (fun n x ↦ exp3IXWeights_mem_simplex n x.1)

lemma exp3IX_def (η γ : ℝ) :
    exp3IX (𝓞 := 𝓞) (α := α) η γ = weightAlgorithm (fun n x ↦ exp3IXWeights η γ n x.1)
      (fun n a ↦ (measurable_pi_apply a).comp
        ((measurable_exp3IXWeights η γ n).comp measurable_fst))
      (fun n x ↦ exp3IXWeights_mem_simplex n x.1) := (rfl)

/-- The policy of Exp3-IX at round `n` draws its action from the weights `exp3IXWeights η γ n h`
of the history `h`. -/
@[simp]
lemma exp3IX_policy_apply (n : ℕ) (x : Hist 𝓞 α ℝ n × 𝓞) :
    (exp3IX η γ).policy n x = weightedMeasure (exp3IXWeights η γ n x.1) := by
  rw [exp3IX_def, weightAlgorithm_policy, weightKernel_apply]

/-- Exp3-IX without implicit exploration (`γ = 0`) is Exp3. -/
lemma exp3IX_eq_exp3 (η : ℝ) : exp3IX (𝓞 := 𝓞) (α := α) η 0 = exp3 η := by
  simp only [exp3IX_def, exp3_def, exp3IXWeights_eq_exp3Weights]

end Algorithm

section History

variable {Ω : Type*} (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ)

/-- Along a sequence of observations `O`, actions `A` and feedbacks `Y`, the cumulative loss
estimates of Exp3-IX after `n` rounds are the sums of the implicit-exploration estimates of the
losses of the rounds `t < n`. -/
lemma exp3IXSum_history (n : ℕ) (ω : Ω) :
    exp3IXSum η γ n (history O A Y n ω) = ∑ t ∈ range n,
      iwEstimator (fun a ↦ exp3IXWeights η γ t (history O A Y t ω) a + γ) (A t ω)
        (1 - Y t ω) := by
  induction n with
  | zero => simp
  | succ n ih => simp [exp3IXSum_succ, Finset.sum_range_succ, ih, history_apply]

/-- Along a sequence of observations `O`, actions `A` and feedbacks `Y`, the weights of Exp3-IX
at round `n` are the exponential weights of `-η` times the cumulative implicit-exploration
estimates of the losses `1 - Y t`. -/
lemma exp3IXWeights_history_eq (n : ℕ) (ω : Ω) :
    exp3IXWeights η γ n (history O A Y n ω) = softmax (-(η • ∑ t ∈ range n,
      iwEstimator (fun a ↦ exp3IXWeights η γ t (history O A Y t ω) a + γ) (A t ω)
        (1 - Y t ω))) := by
  rw [exp3IXWeights_def, exp3IXSum_history]

end History

namespace Exp3IX

/-! ### Pathwise bounds -/

section Pathwise

variable [Nonempty α] {Ω : Type*} (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ) (ω : Ω)
  {n : ℕ}

/-- **Bias of the loss estimates of Exp3-IX** [LS, Lemma 12.4]. Along every sequence of actions `A`
and feedbacks `Y`, with `P t` the weights of Exp3-IX at round `t`, `Ŷ t` its implicit-exploration
loss estimates and `L̂ n` their cumulative sums, for `γ ≥ 0`,
`∑ t < n, ((1 - Y t) - ⟨P t, Ŷ t⟩) = γ * ∑ b, L̂ n b`. -/
theorem sum_sub_sum_mul_eq_mul_sum (hγ : 0 ≤ γ) :
    ∑ t ∈ range n, ((1 - Y t ω) - ∑ b, exp3IXWeights η γ t (history O A Y t ω) b *
        iwEstimator (fun a ↦ exp3IXWeights η γ t (history O A Y t ω) a + γ) (A t ω) (1 - Y t ω) b) =
      γ * ∑ b, exp3IXSum η γ n (history O A Y n ω) b := by
  simp_rw [exp3IXSum_history, Finset.sum_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ ↦
    sub_sum_mul_iwEstimator_add (add_pos_of_pos_of_nonneg (exp3IXWeights_pos _ _ _) hγ).ne'

/-- **Pathwise bound on the estimated regret of Exp3-IX** [LS, (12.3) and Lemma 12.4]. Along every
sequence of actions `A` and feedbacks `Y t ∈ [0, 1]` of the rounds `t < n`, with `L̂ n` the
cumulative loss estimates of Exp3-IX, for every arm `a`, `η > 0` and `γ ≥ 0`,
`∑ t < n, (1 - Y t) - L̂ n a ≤ log k / η + (γ + η / 2) * ∑ b, L̂ n b`, with `k` the number of
arms. -/
theorem sum_sub_exp3IXSum_le (hη : 0 < η) (hγ : 0 ≤ γ) (hY : ∀ t < n, Y t ω ∈ Set.Icc 0 1)
    (a : α) :
    ∑ t ∈ range n, (1 - Y t ω) - exp3IXSum η γ n (history O A Y n ω) a ≤
      log (Fintype.card α) / η + (γ + η / 2) * ∑ b, exp3IXSum η γ n (history O A Y n ω) b := by
  set p : ℕ → α → ℝ := fun t ↦ exp3IXWeights η γ t (history O A Y t ω) with hp
  set y : ℕ → α → ℝ := fun t ↦ iwEstimator (fun c ↦ p t c + γ) (A t ω) (1 - Y t ω) with hy
  have hpγ : ∀ t c, 0 < p t c + γ := fun t c ↦
    add_pos_of_pos_of_nonneg (exp3IXWeights_pos _ _ _) hγ
  have hz : ∀ t < n, 1 - Y t ω ∈ Set.Icc 0 1 := fun t ht ↦
    ⟨sub_nonneg.2 (hY t ht).2, sub_le_self _ (hY t ht).1⟩
  -- the local-norm bound of exponential weights for the nonnegative loss estimates `y t`
  have hy0 : ∀ t < n, ∀ c, 0 ≤ y t c := fun t ht c ↦
    iwEstimator_nonneg (hpγ t _).le (hz t ht).1
  have key := softmax_regret_le hη hy0 a
  have hpw : ∀ t, softmax (-(η • ∑ s ∈ range t, y s)) = p t := fun t ↦
    (exp3IXWeights_history_eq O A Y t ω).symm
  simp only [hpw] at key
  -- the second-order terms are at most the estimates
  have h2 : ∑ t ∈ range n, ∑ c, p t c * y t c ^ 2 ≤ ∑ t ∈ range n, ∑ c, y t c :=
    Finset.sum_le_sum fun t ht ↦ sum_mul_iwEstimator_add_sq_le
      (exp3IXWeights_pos _ _ _).le hγ (hpγ t _) (hz t (mem_range.1 ht))
  -- the bias identity and the cumulative estimates
  have hbias := sum_sub_sum_mul_eq_mul_sum (η := η) O A Y ω (n := n) hγ
  have hsum : ∑ t ∈ range n, ∑ c, y t c = ∑ c, exp3IXSum η γ n (history O A Y n ω) c := by
    simp_rw [hy, hp, exp3IXSum_history, Finset.sum_apply]
    exact Finset.sum_comm
  have hLa : exp3IXSum η γ n (history O A Y n ω) a = ∑ t ∈ range n, y t a := by
    rw [exp3IXSum_history, Finset.sum_apply]
  rw [Finset.sum_sub_distrib] at key hbias
  rw [← hsum] at hbias ⊢
  have h2' := mul_le_mul_of_nonneg_left h2 (half_pos hη).le
  rw [hLa]
  linarith

/-- Along every sequence of actions `A` and feedbacks `Y`, with `P t` the weights of Exp3-IX at
round `t` and `L̂ n` its cumulative loss estimates, the weighted deviations
`c ∑ a, v a * (L̂ n a - L n a)` from the cumulative losses `L n a = ∑ t < n, (1 - x t a)` are the
sums over the rounds `t < n` and the arms of `c v a` times the deviations of the importance-weighted
estimates for the weights `P t`, discounted by `1 + γ / P t a` as in [LS, Lemma 12.2], from the
losses `1 - x t a`. -/
lemma mul_sum_mul_exp3IXSum_sub_eq (c : ℝ) (v : α → ℝ) (x : ℕ → α → ℝ) :
    c * ∑ a, v a * (exp3IXSum η γ n (history O A Y n ω) a - ∑ t ∈ range n, (1 - x t a)) =
      ∑ t ∈ range n, ∑ a, c * v a *
        (iwEstimator (exp3IXWeights η γ t (history O A Y t ω)) (A t ω) (1 - Y t ω) a /
          (1 + γ / exp3IXWeights η γ t (history O A Y t ω) a) - (1 - x t a)) := by
  rw [exp3IXSum_history, Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_apply, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [iwEstimator_div_one_add_div (exp3IXWeights_pos _ _ a)]
  ring

end Pathwise

/-! ### Concentration of the loss estimates -/

section Concentration

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] [Nonempty α]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {env : Environment 𝓞 α ℝ}
  {x : ℕ → α → ℝ} {n : ℕ} {δ : ℝ}

/-- **Concentration of the loss estimates of Exp3-IX** [LS, proof of Lemma 12.3]. Along a run of
Exp3-IX with `γ ≥ 0` whose feedback at every round `t < n` is the reward `x t (A t) ∈ [0, 1]` of
its action, for weights `v a ∈ [0, 1]` on the arms and `δ > 0`, the probability that
`log (1 / δ) ≤ 2 γ ∑ a, v a * (L̂ n a - L n a)` is at most `δ`, with `L̂ n` the cumulative loss
estimates and `L n a = ∑ t < n, (1 - x t a)` the cumulative losses. -/
theorem measure_le_sum_mul_exp3IXSum_sub_le {v : α → ℝ} (hv : ∀ a, v a ∈ Set.Icc 0 1)
    (hγ : 0 ≤ γ) (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t) (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3IX η γ) env P) (hδ : 0 < δ) :
    P {ω | log (1 / δ) ≤ 2 * γ * ∑ a, v a *
      (exp3IXSum η γ n (history O A Y n ω) a - ∑ t ∈ range n, (1 - x t a))} ≤
      ENNReal.ofReal δ := by
  -- the variables of the concentration inequality of implicit-exploration estimates
  set p : ℕ → Ω → α → ℝ := fun t ω ↦ exp3IXWeights η γ t (history O A Y t ω) with hp
  set X : ℕ → α → Ω → ℝ := fun t a ω ↦
    if t < n then iwEstimator (p t ω) (A t ω) (1 - Y t ω) a else 0 with hX
  set y : ℕ → α → Ω → ℝ := fun t a _ ↦ if t < n then 1 - x t a else 0 with hy
  set w : ℕ → α → Ω → ℝ := fun _ a _ ↦ 2 * γ * v a with hw
  set l : ℕ → α → Ω → ℝ := fun t a ω ↦ γ / p t ω a with hl
  have hY01 := ae_feedback_mem_Icc hY hx
  have hW : ∀ t, Measurable[h.filtration t] fun ω ↦ exp3IXWeights η γ t (history O A Y t ω) :=
    fun t ↦ Measurable.comp (mα := h.filtration t) (g := exp3IXWeights η γ t)
      (f := history O A Y t) (measurable_exp3IXWeights η γ t) (h.adapted_history t)
  have hpm : ∀ t a, Measurable[h.filtration t] fun ω ↦ p t ω a := fun t a ↦
    Measurable.comp (mα := h.filtration t) (g := fun q : α → ℝ ↦ q a)
      (f := fun ω ↦ exp3IXWeights η γ t (history O A Y t ω)) (measurable_pi_apply a) (hW t)
  have hpm' : ∀ t a, Measurable[h.filtrationObs (t + 1)] fun ω ↦ p t ω a := fun t a ↦
    (hpm t a).mono (h.filtration_le_filtrationObs_succ t) le_rfl
  -- the estimate of round `t < n` as a function of the weights and the action
  have hcongr : ∀ t < n, ∀ a, X t a =ᵐ[P] fun ω ↦
      iwEstimator (exp3IXWeights η γ t (history O A Y t ω)) (A t ω) (1 - x t (A t ω)) a :=
    fun t ht a ↦ by
      filter_upwards [comp_feedback_ae_eq (O := O) (hY t ht)
        fun z b y ↦ iwEstimator (exp3IXWeights η γ t z.1) b (1 - y) a] with ω hω
      simpa [hX, ht] using hω
  have hint : ∀ t a, Integrable (fun ω ↦ iwEstimator (exp3IXWeights η γ t (history O A Y t ω))
      (A t ω) (1 - x t (A t ω)) a) P := fun t a ↦
    WeightAlgorithm.integrable_comp_weights h t (g := fun p b ↦ iwEstimator p b (1 - x t b) a)
      (by fun_prop) (C := |1 - x t a|) fun p hp ↦
        sum_mul_abs_iwEstimator_apply_le (x := fun b ↦ 1 - x t b) ((mem_simplex_iff.1 hp).1 a)
  have hXm : ∀ t a, Measurable[h.filtrationObs (t + 1)] (X t a) := fun t a ↦ by
    refine Measurable.mono ?_ (h.filtration_le_filtrationObs_succ t) le_rfl
    simp only [hX]
    split_ifs
    · exact Measurable.comp (mα := h.filtration t) (measurable_pi_apply a)
        (Measurable.comp (mα := h.filtration t) measurable_iwEstimator
          ((hW t).prodMk ((h.adapted_action t).prodMk
            (measurable_const.sub (h.adapted_feedback t)))))
    · exact measurable_const
  have hXint : ∀ t a, Integrable (X t a) P := fun t a ↦ by
    by_cases ht : t < n
    · exact (hint t a).congr (hcongr t ht a).symm
    · simp [hX, ht]
  have hX0 : ∀ t a, 0 ≤ᵐ[P] X t a := fun t a ↦ by
    filter_upwards [hY01] with ω hω
    simp only [hX, Pi.zero_apply]
    split_ifs with ht
    · exact iwEstimator_nonneg (exp3IXWeights_pos _ _ _).le (sub_nonneg.2 (hω t ht).2)
    · exact le_rfl
  have hXy : ∀ t a, P[X t a | h.filtrationObs t] ≤ᵐ[P] y t a := fun t a ↦ by
    by_cases ht : t < n
    · refine ((condExp_congr_ae (hcongr t ht a)).trans ?_).le
      filter_upwards [WeightAlgorithm.condExp_comp_weights h t
        (g := fun p b ↦ iwEstimator p b (1 - x t b) a) (by fun_prop) (hint t a)] with ω hω
      refine hω.trans ?_
      simpa [hy, ht] using sum_mul_iwEstimator_apply (x := fun b ↦ 1 - x t b)
        (exp3IXWeights_pos (η := η) (γ := γ) t (history O A Y t ω) a).ne'
    · have : X t a = 0 := by
        funext ω
        simp [hX, ht]
      rw [this, condExp_zero]
      exact ae_of_all _ fun ω ↦ by simp [hy, ht]
  have hwl : ∀ t a, ∀ᵐ ω ∂P, w t a ω * X t a ω ≤ 2 * l t a ω := fun t a ↦ by
    filter_upwards [hY01] with ω hω
    have hpa := exp3IXWeights_pos (η := η) (γ := γ) t (history O A Y t ω) a
    have hl0 : 0 ≤ 2 * l t a ω := by positivity
    simp only [hw, hX, hl]
    split_ifs with ht
    · have hX1 : iwEstimator (p t ω) (A t ω) (1 - Y t ω) a ≤ 1 / p t ω a :=
        iwEstimator_le_one_div hpa.le (sub_le_self _ (hω t ht).1)
      have hX0 : 0 ≤ iwEstimator (p t ω) (A t ω) (1 - Y t ω) a :=
        iwEstimator_nonneg (exp3IXWeights_pos _ _ _).le (sub_nonneg.2 (hω t ht).2)
      have hvX : v a * iwEstimator (p t ω) (A t ω) (1 - Y t ω) a ≤ 1 / p t ω a :=
        (mul_le_of_le_one_left hX0 (hv a).2).trans hX1
      calc 2 * γ * v a * iwEstimator (p t ω) (A t ω) (1 - Y t ω) a
          = 2 * γ * (v a * iwEstimator (p t ω) (A t ω) (1 - Y t ω) a) := by ring
        _ ≤ 2 * γ * (1 / p t ω a) := mul_le_mul_of_nonneg_left hvX (by positivity)
        _ = 2 * (γ / p t ω a) := by ring
    · simpa using hl0
  have hmul : ∀ t i j, i ≠ j → ∀ᵐ ω ∂P, w t i ω * X t i ω * (w t j ω * X t j ω) = 0 :=
    fun t i j hij ↦ ae_of_all _ fun ω ↦ by
      simp only [hX]
      split_ifs
      · rw [mul_mul_mul_comm, iwEstimator_mul_iwEstimator_of_ne hij, mul_zero]
      · simp
  have key := measure_log_one_div_le_sum_sum_mul_div_one_add_sub_le (ℱ := h.filtrationObs)
    hXm hXint hX0 hXy (fun _ _ ↦ measurable_const) (fun t a ↦ measurable_const.div (hpm' t a))
    (fun _ _ ↦ measurable_const) (fun _ _ ↦ ae_of_all _ fun _ ↦
      mul_nonneg (by positivity) (hv _).1) hwl hmul hδ n
  -- the sum of the concentration inequality is `2 γ ∑ a, v a * (L̂ n a - L n a)`
  refine le_trans (measure_mono fun ω hω ↦ ?_) key
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [mul_sum_mul_exp3IXSum_sub_eq O A Y ω] at hω
  refine hω.trans_eq (Finset.sum_congr rfl fun t ht ↦ Finset.sum_congr rfl fun a _ ↦ ?_)
  simp only [hX, hy, hp, mem_range.1 ht, ite_true, Pi.div_apply]

/-- **Concentration of the loss estimates of one arm** [LS, (12.9)]. Along a run of Exp3-IX with
`γ > 0` whose feedback at every round `t < n` is the reward `x t (A t) ∈ [0, 1]` of its action, for
every arm `a` and `δ > 0`, the probability that `log (1 / δ) / (2 γ) ≤ L̂ n a - L n a` is at most
`δ`, with `L̂ n` the cumulative loss estimates and `L n a = ∑ t < n, (1 - x t a)`. -/
theorem measure_le_exp3IXSum_sub_le (hγ : 0 < γ) (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t)
    (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1) (h : IsAlgEnvSeq O A Y (exp3IX η γ) env P)
    (hδ : 0 < δ) (a : α) :
    P {ω | log (1 / δ) / (2 * γ) ≤
      exp3IXSum η γ n (history O A Y n ω) a - ∑ t ∈ range n, (1 - x t a)} ≤
      ENNReal.ofReal δ := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_le_sum_mul_exp3IXSum_sub_le (v := Pi.single a 1) (fun b ↦ ?_) hγ.le hY hx h hδ)
  · simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [Finset.sum_eq_single a (fun b _ hb ↦ by simp [hb]) (by simp), Pi.single_eq_same, one_mul,
      ← div_le_iff₀' (by positivity)]
    exact hω
  · rw [Pi.single_apply]
    split_ifs <;> simp

/-- **Concentration of the sum of the loss estimates** [LS, (12.8)]. Along a run of Exp3-IX with
`γ > 0` whose feedback at every round `t < n` is the reward `x t (A t) ∈ [0, 1]` of its action, for
`δ > 0`, the probability that `log (1 / δ) / (2 γ) ≤ ∑ a, (L̂ n a - L n a)` is at most `δ`, with
`L̂ n` the cumulative loss estimates and `L n a = ∑ t < n, (1 - x t a)`. -/
theorem measure_le_sum_exp3IXSum_sub_le (hγ : 0 < γ) (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t)
    (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1) (h : IsAlgEnvSeq O A Y (exp3IX η γ) env P)
    (hδ : 0 < δ) :
    P {ω | log (1 / δ) / (2 * γ) ≤
      ∑ a, (exp3IXSum η γ n (history O A Y n ω) a - ∑ t ∈ range n, (1 - x t a))} ≤
      ENNReal.ofReal δ := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_le_sum_mul_exp3IXSum_sub_le (v := fun _ ↦ 1) (fun _ ↦ ⟨zero_le_one, le_rfl⟩) hγ.le
      hY hx h hδ)
  simp only [Set.mem_ofPred_eq, one_mul] at hω ⊢
  rwa [← div_le_iff₀' (by positivity)]

/-- **Concentration of the loss estimates of Exp3-IX** [LS, Lemma 12.3]. Along a run of Exp3-IX
with `γ > 0` whose feedback at every round `t < n` is the reward `x t (A t) ∈ [0, 1]` of its
action, for `δ > 0`, with probability at least `1 - δ`, both
`L̂ n a - L n a < log ((k + 1) / δ) / (2 γ)` for every arm `a` and
`∑ a, (L̂ n a - L n a) < log ((k + 1) / δ) / (2 γ)`, with `L̂ n` the cumulative loss estimates,
`L n a = ∑ t < n, (1 - x t a)` and `k` the number of arms. -/
theorem measure_exists_le_exp3IXSum_sub_union_le (hγ : 0 < γ)
    (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t) (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3IX η γ) env P) (hδ : 0 < δ) :
    P ({ω | ∃ a, log ((Fintype.card α + 1) / δ) / (2 * γ) ≤
        exp3IXSum η γ n (history O A Y n ω) a - ∑ t ∈ range n, (1 - x t a)} ∪
      {ω | log ((Fintype.card α + 1) / δ) / (2 * γ) ≤
        ∑ a, (exp3IXSum η γ n (history O A Y n ω) a - ∑ t ∈ range n, (1 - x t a))}) ≤
      ENNReal.ofReal δ := by
  -- a union bound over `k + 1` events of probability at most `δ / (k + 1)`
  have hk : (0 : ℝ) < Fintype.card α + 1 := by positivity
  have hδ' : 0 < δ / (Fintype.card α + 1) := div_pos hδ hk
  have hlog : log (1 / (δ / (Fintype.card α + 1))) = log ((Fintype.card α + 1) / δ) := by
    rw [one_div_div]
  calc _ ≤ P {ω | ∃ a, log ((Fintype.card α + 1) / δ) / (2 * γ) ≤
        exp3IXSum η γ n (history O A Y n ω) a - ∑ t ∈ range n, (1 - x t a)} +
      P {ω | log ((Fintype.card α + 1) / δ) / (2 * γ) ≤
        ∑ a, (exp3IXSum η γ n (history O A Y n ω) a - ∑ t ∈ range n, (1 - x t a))} :=
        measure_union_le _ _
    _ ≤ ∑ _a : α, ENNReal.ofReal (δ / (Fintype.card α + 1)) +
        ENNReal.ofReal (δ / (Fintype.card α + 1)) := by
      gcongr
      · rw [Set.ofPred_exists]
        refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
        simpa [hlog] using measure_le_exp3IXSum_sub_le hγ hY hx h hδ' a
      · simpa [hlog] using measure_le_sum_exp3IXSum_sub_le hγ hY hx h hδ'
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
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {env : Environment 𝓞 α ℝ}
  {x : ℕ → α → ℝ} {n : ℕ} {δ : ℝ}

/-- **High-probability regret bound of Exp3-IX** [LS, proof of Theorem 12.1]. Along a run of
Exp3-IX with `η, γ > 0` whose feedback at every round `t < n` is the reward `x t (A t) ∈ [0, 1]` of
its action, for `δ > 0`, the probability that the random regret `∑ t < n, (x t a - x t (A t))`
against some arm `a` is at least `log k / η + (γ + η / 2) (n k + c) + c` is at most `δ`, where
`c = log ((k + 1) / δ) / (2 γ)` and `k` is the number of arms. -/
theorem measure_exists_le_sum_sub_le (hη : 0 < η) (hγ : 0 < γ)
    (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t) (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3IX η γ) env P) (hδ : 0 < δ) :
    P {ω | ∃ a, log (Fintype.card α) / η + (γ + η / 2) *
        (n * Fintype.card α + log ((Fintype.card α + 1) / δ) / (2 * γ)) +
          log ((Fintype.card α + 1) / δ) / (2 * γ) ≤ ∑ t ∈ range n, (x t a - x t (A t ω))} ≤
      ENNReal.ofReal δ := by
  set c := log ((Fintype.card α + 1) / δ) / (2 * γ)
  refine le_trans (measure_mono_ae ?_) (measure_exists_le_exp3IXSum_sub_union_le hγ hY hx h hδ)
  filter_upwards [ae_forall_feedback_eq hY, ae_feedback_mem_Icc hY hx] with ω hYω h01 ⟨a, ha⟩
  by_contra hE
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_le] at hE ha
  obtain ⟨hEa, hEs⟩ := hE
  -- the estimated regret, the deviation of arm `a` and the sum of the estimates
  have hpath := sum_sub_exp3IXSum_le O A Y ω hη hγ.le h01 a
  have hR : ∑ t ∈ range n, (x t a - x t (A t ω)) =
      (∑ t ∈ range n, (1 - Y t ω) - exp3IXSum η γ n (history O A Y n ω) a) +
        (exp3IXSum η γ n (history O A Y n ω) a - ∑ t ∈ range n, (1 - x t a)) := by
    rw [sub_add_sub_cancel, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    rw [hYω t (mem_range.1 ht)]
    ring
  have hL : ∑ b, ∑ t ∈ range n, (1 - x t b) ≤ n * Fintype.card α := by
    calc ∑ b, ∑ t ∈ range n, (1 - x t b) ≤ ∑ _b : α, ∑ _t ∈ range n, (1 : ℝ) :=
          Finset.sum_le_sum fun b _ ↦ Finset.sum_le_sum fun t ht ↦
            sub_le_self _ (hx t (mem_range.1 ht) b).1
      _ = n * Fintype.card α := by simp [mul_comm]
  have hS : ∑ b, exp3IXSum η γ n (history O A Y n ω) b ≤ n * Fintype.card α + c := by
    have := hEs.le
    rw [Finset.sum_sub_distrib] at this
    linarith
  have hS' := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ γ + η / 2)
  linarith [hEa a]

/-- **High-probability regret bound of Exp3-IX with `γ = η / 2`** [LS, proof of Theorem 12.1].
Along a run of Exp3-IX with learning rate `η ≥ 0` and implicit-exploration parameter `γ = η / 2`
whose feedback at every round `t < n` is the reward `x t (A t) ∈ [0, 1]` of its action, for
`δ > 0` and `L ≥ log k + log ((k + 1) / δ)` such that `η > 0` whenever `n` and `L` are positive,
the probability that the random regret `∑ t < n, (x t a - x t (A t))` against some arm `a` is at
least `L / η + η n k + log ((k + 1) / δ)` is at most `δ`, with `k` the number of arms. -/
theorem measure_exists_div_add_mul_add_le_sum_sub_le {L : ℝ} (hη : 0 ≤ η)
    (hηL : 0 < n → 0 < L → 0 < η)
    (hL : log (Fintype.card α) + log ((Fintype.card α + 1) / δ) ≤ L)
    (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t) (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3IX η (η / 2)) env P) (hδ : 0 < δ) :
    P {ω | ∃ a, L / η + η * (n * Fintype.card α) + log ((Fintype.card α + 1) / δ) ≤
      ∑ t ∈ range n, (x t a - x t (A t ω))} ≤ ENNReal.ofReal δ := by
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.2 hδ1)
  have hk0 : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hlogδ : 0 < log ((Fintype.card α + 1) / δ) := log_pos ((one_lt_div hδ).2 (by linarith))
  have hlogk : 0 ≤ log (Fintype.card α) := log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hL0 : 0 < L := by linarith
  -- with no round, the regret is zero
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (measure_mono_null (fun ω hω ↦ ?_) measure_empty).trans_le zero_le
    obtain ⟨a, ha⟩ := hω
    simp only [CharP.cast_eq_zero, zero_mul, mul_zero, add_zero, range_zero, sum_empty] at ha
    linarith [div_nonneg hL0.le hη]
  have hη0 := hηL hn hL0
  refine (measure_mono fun ω hω ↦ ?_).trans
    (measure_exists_le_sum_sub_le hη0 (half_pos hη0) hY hx h hδ)
  obtain ⟨a, ha⟩ := hω
  refine ⟨a, le_trans ?_ ha⟩
  -- the bound of `measure_exists_le_sum_sub_le` for `γ = η / 2`
  have e1 : log (Fintype.card α) / η + (η / 2 + η / 2) * (n * Fintype.card α +
      log ((Fintype.card α + 1) / δ) / (2 * (η / 2))) +
        log ((Fintype.card α + 1) / δ) / (2 * (η / 2)) =
      (log (Fintype.card α) + log ((Fintype.card α + 1) / δ)) / η + η * (n * Fintype.card α) +
        log ((Fintype.card α + 1) / δ) := by
    field_simp
    ring
  rw [e1]
  gcongr

/-- **High-probability regret bound of Exp3-IX** [LS, Theorem 12.1, (12.5)]. Along a run of
Exp3-IX with learning rate `η = √(2 log (k + 1) / (n k))` and implicit-exploration parameter
`γ = η / 2` whose feedback at every round `t < n` is the reward `x t (A t) ∈ [0, 1]` of its action,
for every `δ > 0`, the probability that the random regret `∑ t < n, (x t a - x t (A t))` against
some arm `a` is at least
`√(8 n k log (k + 1)) + √(n k / (2 log (k + 1))) log (1 / δ) + log ((k + 1) / δ)` is at most `δ`,
with `k` the number of arms. The learning rate does not depend on `δ`. -/
theorem measure_exists_sqrt_le_sum_sub_le (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t)
    (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3IX √(2 * log (Fintype.card α + 1) / (n * Fintype.card α))
      (√(2 * log (Fintype.card α + 1) / (n * Fintype.card α)) / 2)) env P) (hδ : 0 < δ) :
    P {ω | ∃ a, √(8 * n * Fintype.card α * log (Fintype.card α + 1)) +
        √(n * Fintype.card α / (2 * log (Fintype.card α + 1))) * log (1 / δ) +
          log ((Fintype.card α + 1) / δ) ≤ ∑ t ∈ range n, (x t a - x t (A t ω))} ≤
      ENNReal.ofReal δ := by
  set k : ℝ := (Fintype.card α : ℝ) with hk
  have hk0 : 0 < k := by rw [hk]; exact_mod_cast Fintype.card_pos
  have hL : 0 < log (k + 1) := log_pos (by linarith)
  set m : ℝ := n * k with hm
  have hm0 : 0 ≤ m := mul_nonneg n.cast_nonneg hk0.le
  set η := √(2 * log (k + 1) / m) with hη
  -- `L = 2 log (k + 1) + log (1 / δ)` in `measure_exists_div_add_mul_add_le_sum_sub_le`
  have hlog : log ((k + 1) / δ) = log (k + 1) + log (1 / δ) := by
    rw [div_eq_mul_one_div, log_mul (by linarith) (by positivity)]
  have hLle : log k + log ((k + 1) / δ) ≤ 2 * log (k + 1) + log (1 / δ) := by
    rw [hlog]
    linarith [log_le_log hk0 (by linarith : k ≤ k + 1)]
  refine (measure_mono fun ω hω ↦ ?_).trans
    (measure_exists_div_add_mul_add_le_sum_sub_le (sqrt_nonneg _)
      (fun hn _ ↦ sqrt_pos.2 (div_pos (by positivity) (mul_pos (Nat.cast_pos.2 hn) hk0))) hLle
      hY hx h hδ)
  obtain ⟨a, ha⟩ := hω
  refine ⟨a, le_trans (le_of_eq ?_) ha⟩
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
[LS, Theorem 12.1, (12.6)]. Along a run of Exp3-IX with learning rate
`η = √((log k + log ((k + 1) / δ)) / (n k))` and implicit-exploration parameter `γ = η / 2` whose
feedback at every round `t < n` is the reward `x t (A t) ∈ [0, 1]` of its action, for `δ > 0`, the
probability that the random regret `∑ t < n, (x t a - x t (A t))` against some arm `a` is at least
`2 √((2 log (k + 1) + log (1 / δ)) n k) + log ((k + 1) / δ)` is at most `δ`, with `k` the number
of arms. -/
theorem measure_exists_two_mul_sqrt_le_sum_sub_le (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t)
    (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3IX
      √((log (Fintype.card α) + log ((Fintype.card α + 1) / δ)) / (n * Fintype.card α))
      (√((log (Fintype.card α) + log ((Fintype.card α + 1) / δ)) / (n * Fintype.card α)) / 2))
      env P) (hδ : 0 < δ) :
    P {ω | ∃ a, 2 * √((2 * log (Fintype.card α + 1) + log (1 / δ)) * n * Fintype.card α) +
          log ((Fintype.card α + 1) / δ) ≤ ∑ t ∈ range n, (x t a - x t (A t ω))} ≤
      ENNReal.ofReal δ := by
  set k : ℝ := (Fintype.card α : ℝ) with hk
  have hk0 : 0 < k := by rw [hk]; exact_mod_cast Fintype.card_pos
  set m : ℝ := n * k with hm
  have hm0 : 0 ≤ m := mul_nonneg n.cast_nonneg hk0.le
  set M := log k + log ((k + 1) / δ) with hM
  set η := √(M / m) with hη
  refine (measure_mono fun ω hω ↦ ?_).trans
    (measure_exists_div_add_mul_add_le_sum_sub_le (L := M) (sqrt_nonneg _)
      (fun hn hM0 ↦ sqrt_pos.2 (div_pos hM0 (mul_pos (Nat.cast_pos.2 hn) hk0))) le_rfl
      hY hx h hδ)
  obtain ⟨a, ha⟩ := hω
  refine ⟨a, le_trans ?_ ha⟩
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

end Regret

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
    (h : IsAlgEnvSeq O A Y (exp3IX √(2 * log (Fintype.card α + 1) / (n * Fintype.card α))
      (√(2 * log (Fintype.card α + 1) / (n * Fintype.card α)) / 2))
      (Environment.evalSeq x hxm) P) (hδ : 0 < δ) :
    P {ω | ∃ a, √(8 * n * Fintype.card α * log (Fintype.card α + 1)) +
        √(n * Fintype.card α / (2 * log (Fintype.card α + 1))) * log (1 / δ) +
          log ((Fintype.card α + 1) / δ) ≤ ∑ t ∈ range n, (x t a - x t (A t ω))} ≤
      ENNReal.ofReal δ :=
  Exp3IX.measure_exists_sqrt_le_sum_sub_le (fun t _ ↦ h.feedback_ae_eq_evalSeq t) hx h hδ

/-- **High-probability regret bound of Exp3-IX for a fixed confidence level**
[LS, Theorem 12.1, (12.6)] against an oblivious adversary: along a run of Exp3-IX with
`η = √((log k + log ((k + 1) / δ)) / (n k))` and `γ = η / 2` against LML's evaluation environment
`Environment.evalSeq x _` with rewards in `[0, 1]` at the rounds `t < n`, for `δ > 0`, the
probability that the random regret against some arm is at least
`2 √((2 log (k + 1) + log (1 / δ)) n k) + log ((k + 1) / δ)` is at most `δ`, with `k` the number
of arms. -/
theorem exp3IX_measure_exists_two_mul_sqrt_le_sum_sub_le (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3IX
      √((log (Fintype.card α) + log ((Fintype.card α + 1) / δ)) / (n * Fintype.card α))
      (√((log (Fintype.card α) + log ((Fintype.card α + 1) / δ)) / (n * Fintype.card α)) / 2))
      (Environment.evalSeq x hxm) P) (hδ : 0 < δ) :
    P {ω | ∃ a, 2 * √((2 * log (Fintype.card α + 1) + log (1 / δ)) * n * Fintype.card α) +
          log ((Fintype.card α + 1) / δ) ≤ ∑ t ∈ range n, (x t a - x t (A t ω))} ≤
      ENNReal.ofReal δ :=
  Exp3IX.measure_exists_two_mul_sqrt_le_sum_sub_le (fun t _ ↦ h.feedback_ae_eq_evalSeq t) hx h hδ

end EvalSeq

end LMLExplore.Bandits
