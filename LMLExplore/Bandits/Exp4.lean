/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.Exp3

/-!
# Exp4

In a bandit with expert advice [LS, Chapter 18], each expert `m` of a finite set `β` recommends at
round `t` a distribution `E t m ∈ simplex α` over the arms, and the learner sees this advice before
acting. Exp4 [ACFS02], [LS, Algorithm 11] runs exponential weights over the experts: it keeps
weights `Q t = softmax (η • Ŝᴱ t)` on the experts, plays an arm drawn from the mixture
`P t = ∑ m, Q t m • E t m` of their advice, estimates the rewards of the arms by the loss-based
importance-weighted estimates `X̂ t` of `P t`, and credits each expert `m` with the estimate
`X̂ᴱ t m = E t m ⬝ᵥ X̂ t` of its expected reward, so that `Ŝᴱ t = ∑ s < t, X̂ᴱ s`. In matrix form,
`P t = Q t E t` and `X̂ᴱ t = E t X̂ t`. The learning rate `η > 0` is a parameter; this is the
algorithm of [LS] with `γ = 0`.

The observation of round `t` is the advice `E t : β → simplex α`. For rewards in `[0, 1]` and a
fixed advice sequence `E`, the regret against the best expert satisfies
`R_n ≤ log M / η + η n k / 2`, with `k` the number of arms and `M` the number of experts, and the
learning rate `η = √(2 log M / (n k))` gives `R_n ≤ √(2 n k log M)` [LS, Theorem 18.1].

With the experts `α` that each recommend one arm, Exp4 is Exp3: its weights on the experts are the
weights of Exp3, and so is the mixture of their advice.

## Main definitions

* `LMLExplore.Bandits.exp4Sum η n h`: the cumulative reward estimates `Ŝᴱ n` of the experts,
  computed from the history `h` of the first `n` rounds.
* `LMLExplore.Bandits.exp4ExpertWeights η n h`: the weights `Q n = softmax (η • Ŝᴱ n)` of Exp4 on
  the experts at round `n`.
* `LMLExplore.Bandits.exp4Weights η n h e`: the weights `P n = ∑ m, Q n m • e m` of Exp4 on the
  arms at round `n`, for the advice `e` of round `n`.
* `LMLExplore.Bandits.exp4 η`: the Exp4 algorithm with learning rate `η`.

## Main statements

* `exp4Weights_mem_simplex`: the weights of Exp4 on the arms are a probability vector.
* `exp4ExpertWeights_history_eq`: along every sequence of observations, actions and feedbacks,
  the weights of Exp4 on the experts are the exponential weights of `-η` times the cumulative
  estimated losses `E t m ⬝ᵥ Ŷ t` of the experts, with `Ŷ t` the importance-weighted estimates of
  the losses `1 - Y t`.
* `exp4ExpertWeights_eq_exp3Weights`, `exp4Weights_eq_exp3Weights`: with the advice of the
  experts `α` that each recommend one arm, the weights of Exp4 on the experts and on the arms are
  those of Exp3.
* `exp4_eq_of_subsingleton`: with a single expert, Exp4 does not depend on its learning rate.
* `Exp4.sum_sub_sum_le`: [LS, Lemma 18.2], the pathwise bound
  `∑ t < n, (X̂ᴱ t m - ⟨Q t, X̂ᴱ t⟩) ≤ log M / η + η / 2 * ∑ t < n, ⟨Q t, (1 - X̂ᴱ t) ^ 2⟩`.
* `Exp4.sum_exp4ExpertWeights_mul_dotProduct_lossIwEstimator`: the `Q t`-average of the
  estimated rewards `X̂ᴱ t` of the experts is the observed reward `Y t`.
* `Exp4.sum_mul_one_sub_sq_le`: the second-order term satisfies
  `⟨Q t, (1 - X̂ᴱ t) ^ 2⟩ ≤ (1 - Y t) ^ 2 / P t (A t)`.
* `Exp4.sum_dotProduct_lossIwEstimator_sub_le`: the resulting pathwise bound on the estimated
  regret against an expert.
* `Exp4.integral_dotProduct_lossIwEstimator`: the estimated reward `X̂ᴱ t m` of expert `m` is
  unbiased [LS, (18.10)].
* `Exp4.expertRegret_le`: for a run of Exp4 whose observations are the advice `E t` and whose
  feedback is the reward `x t (A t) ∈ [0, 1]` of its action, `R_n ≤ log M / η + η n k / 2`.
* `Exp4.expertRegret_nonpos_of_subsingleton`: with a single expert, the regret is nonpositive.
* `Exp4.expertRegret_le_sqrt`: [LS, Theorem 18.1]. With `η = √(2 log M / (n k))`,
  `R_n ≤ √(2 n k log M)`.
* `exp4_expertRegret_le`, `exp4_expertRegret_le_sqrt`: the same bounds for runs against
  `Environment.ofSeq E x _`.

## References

* [ACFS02] P. Auer, N. Cesa-Bianchi, Y. Freund and R. E. Schapire, *The nonstochastic multiarmed
  bandit problem*, SIAM J. Comput. 32(1), 2002.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real LMLExplore.OnlineLearning

namespace LMLExplore.Bandits

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] {η : ℝ}

section Weights

/-- The cumulative reward estimates of the experts in Exp4 with learning rate `η`, computed from
the history `h` of the first `n` rounds: `∑ s < n, X̂ᴱ s` with `X̂ᴱ s m = E s m ⬝ᵥ X̂ s`, for the
advice `E s` observed at round `s`, the loss-based importance-weighted estimates
`X̂ s = lossIwEstimator (P s) (A s) (X s)` of the rewards of the arms, computed from the action
`A s` and the reward `X s` of round `s` of `h`, and the weights
`P s = ∑ m, softmax (η • ∑ r < s, X̂ᴱ r) m • E s m` on the arms at round `s`. -/
noncomputable def exp4Sum (η : ℝ) : (n : ℕ) → Hist (β → simplex α) α ℝ n → β → ℝ
  | 0, _ => 0
  | n + 1, h => exp4Sum η n (Fin.init h) + fun m ↦ ((h (Fin.last n)).obs m : α → ℝ) ⬝ᵥ
      lossIwEstimator (∑ m', softmax (η • exp4Sum η n (Fin.init h)) m' •
        ((h (Fin.last n)).obs m' : α → ℝ)) (h (Fin.last n)).action (h (Fin.last n)).feedback

/-- The weights of Exp4 with learning rate `η` on the experts after the history `h` of the first
`n` rounds: the softmax of `η` times the cumulative reward estimates `exp4Sum η n h` of the
experts. -/
noncomputable def exp4ExpertWeights (η : ℝ) (n : ℕ) (h : Hist (β → simplex α) α ℝ n) : β → ℝ :=
  softmax (η • exp4Sum η n h)

/-- The weights of Exp4 with learning rate `η` on the arms after the history `h` of the first `n`
rounds, for the advice `e` of round `n`: the mixture `∑ m, Q m • e m` of the advice of the experts
with the weights `Q = exp4ExpertWeights η n h`. -/
noncomputable def exp4Weights (η : ℝ) (n : ℕ) (h : Hist (β → simplex α) α ℝ n)
    (e : β → simplex α) : α → ℝ :=
  ∑ m, exp4ExpertWeights η n h m • (e m : α → ℝ)

lemma exp4ExpertWeights_def (η : ℝ) (n : ℕ) (h : Hist (β → simplex α) α ℝ n) :
    exp4ExpertWeights η n h = softmax (η • exp4Sum η n h) := (rfl)

lemma exp4Weights_def (η : ℝ) (n : ℕ) (h : Hist (β → simplex α) α ℝ n) (e : β → simplex α) :
    exp4Weights η n h e = ∑ m, exp4ExpertWeights η n h m • (e m : α → ℝ) := (rfl)

lemma exp4Weights_apply (n : ℕ) (h : Hist (β → simplex α) α ℝ n) (e : β → simplex α) (a : α) :
    exp4Weights η n h e a = ∑ m, exp4ExpertWeights η n h m * (e m : α → ℝ) a := by
  simp [exp4Weights_def]

@[simp]
lemma exp4Sum_zero (h : Hist (β → simplex α) α ℝ 0) : exp4Sum η 0 h = 0 := by
  rw [exp4Sum]

lemma exp4Sum_succ (n : ℕ) (h : Hist (β → simplex α) α ℝ (n + 1)) :
    exp4Sum η (n + 1) h = exp4Sum η n (Fin.init h) + fun m ↦ ((h (Fin.last n)).obs m : α → ℝ) ⬝ᵥ
      lossIwEstimator (exp4Weights η n (Fin.init h) (h (Fin.last n)).obs)
        (h (Fin.last n)).action (h (Fin.last n)).feedback := by
  rw [exp4Sum, exp4Weights_def, exp4ExpertWeights_def]

/-- The first weights of Exp4 on the experts are uniform. -/
@[simp]
lemma exp4ExpertWeights_zero (h : Hist (β → simplex α) α ℝ 0) :
    exp4ExpertWeights η 0 h = fun _ ↦ (Fintype.card β : ℝ)⁻¹ := by
  simp [exp4ExpertWeights_def]

lemma exp4ExpertWeights_pos [Nonempty β] (n : ℕ) (h : Hist (β → simplex α) α ℝ n) (m : β) :
    0 < exp4ExpertWeights η n h m :=
  softmax_pos _ m

lemma exp4ExpertWeights_mem_simplex [Nonempty β] (n : ℕ) (h : Hist (β → simplex α) α ℝ n) :
    exp4ExpertWeights η n h ∈ simplex β :=
  softmax_mem_simplex _

lemma exp4Weights_mem_simplex [Nonempty β] (n : ℕ) (h : Hist (β → simplex α) α ℝ n)
    (e : β → simplex α) :
    exp4Weights η n h e ∈ simplex α :=
  (convex_simplex α).sum_mem (fun m _ ↦ (exp4ExpertWeights_pos n h m).le)
    (mem_simplex_iff.1 (exp4ExpertWeights_mem_simplex n h)).2 fun m _ ↦ (e m).2

/-- The weights `exp4Weights η n h e` of Exp4 on the arms dominate the contribution `Q m • e m` of
every expert `m`, with `Q = exp4ExpertWeights η n h`. As `Q m > 0`, the advice of every expert
vanishes on the arms of weight zero. -/
lemma exp4ExpertWeights_mul_le_exp4Weights (n : ℕ) (h : Hist (β → simplex α) α ℝ n)
    (e : β → simplex α) (m : β) (a : α) :
    exp4ExpertWeights η n h m * (e m : α → ℝ) a ≤ exp4Weights η n h e a := by
  rw [exp4Weights_apply]
  exact Finset.single_le_sum (f := fun m' ↦ exp4ExpertWeights η n h m' * (e m' : α → ℝ) a)
    (fun m' _ ↦ mul_nonneg (softmax_nonneg _ m') ((mem_simplex_iff.1 (e m').2).1 a))
    (mem_univ m)

variable [MeasurableSpace α] [MeasurableSingletonClass α]

@[fun_prop]
lemma measurable_exp4Sum (η : ℝ) (n : ℕ) :
    Measurable (exp4Sum (α := α) (β := β) η n) := by
  induction n with
  | zero =>
    rw [funext exp4Sum_zero]
    exact measurable_const
  | succ n ih =>
    have hinit : Measurable fun h : Hist (β → simplex α) α ℝ (n + 1) ↦ Fin.init h :=
      Measurable.of_eval fun i ↦ measurable_pi_apply _
    have hS := ih.comp hinit
    have hlast : Measurable fun h : Hist (β → simplex α) α ℝ (n + 1) ↦ h (Fin.last n) :=
      measurable_pi_apply _
    have hobs := Round.measurable_obs.comp hlast
    -- the weights on the arms and the loss-based estimates of round `n`
    have hP : Measurable fun h : Hist (β → simplex α) α ℝ (n + 1) ↦
        exp4Weights η n (Fin.init h) (h (Fin.last n)).obs := by
      simp_rw [exp4Weights_def, exp4ExpertWeights_def]
      have := measurable_softmax.comp (hS.const_smul η)
      fun_prop
    have hX := measurable_lossIwEstimator.comp (hP.prodMk
      ((Round.measurable_action.comp hlast).prodMk (Round.measurable_feedback.comp hlast)))
    rw [funext (exp4Sum_succ n)]
    refine hS.add (measurable_pi_iff.2 fun m ↦ ?_)
    have hadv : Measurable fun h : Hist (β → simplex α) α ℝ (n + 1) ↦
        ((h (Fin.last n)).obs m : α → ℝ) :=
      measurable_subtype_coe.comp ((measurable_pi_apply m).comp hobs)
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun a _ ↦
      ((measurable_pi_apply a).comp hadv).mul ((measurable_pi_apply a).comp hX)

@[fun_prop]
lemma measurable_exp4ExpertWeights (η : ℝ) (n : ℕ) :
    Measurable (exp4ExpertWeights (α := α) (β := β) η n) :=
  measurable_softmax.comp ((measurable_exp4Sum η n).const_smul η)

/-- The weights of Exp4 on the arms are a measurable function of the history and the advice. -/
@[fun_prop]
lemma measurable_exp4Weights (η : ℝ) (n : ℕ) :
    Measurable fun x : Hist (β → simplex α) α ℝ n × (β → simplex α) ↦
      exp4Weights η n x.1 x.2 :=
  by unfold exp4Weights; fun_prop

end Weights

section Algorithm

variable [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty β]

/-- **Exp4** with learning rate `η` [LS, Algorithm 11] (with `γ = 0`): the weight-based algorithm
that observes at round `n` the advice `e : β → simplex α` of the experts and draws its action from
the weights `exp4Weights η n h e`, the mixture of the advice with the exponential weights of `η`
times the cumulative reward estimates of the experts computed from the history `h`. -/
noncomputable def exp4 (η : ℝ) : Algorithm (β → simplex α) α ℝ :=
  weightAlgorithm (fun n x ↦ exp4Weights η n x.1 x.2)
    (fun n a ↦ (measurable_pi_apply a).comp (measurable_exp4Weights η n))
    (fun n x ↦ exp4Weights_mem_simplex n x.1 x.2)

lemma exp4_def (η : ℝ) :
    exp4 (α := α) (β := β) η = weightAlgorithm (fun n x ↦ exp4Weights η n x.1 x.2)
      (fun n a ↦ (measurable_pi_apply a).comp (measurable_exp4Weights η n))
      (fun n x ↦ exp4Weights_mem_simplex n x.1 x.2) := (rfl)

/-- The policy of Exp4 at round `n` draws its action from the weights `exp4Weights η n h e` of the
history `h` and the advice `e` of round `n`. -/
@[simp]
lemma exp4_policy_apply (n : ℕ) (x : Hist (β → simplex α) α ℝ n × (β → simplex α)) :
    (exp4 η).policy n x = weightedMeasure (exp4Weights η n x.1 x.2) := by
  rw [exp4_def, weightAlgorithm_policy, weightKernel_apply]

/-- With a single expert, Exp4 does not depend on its learning rate: it follows the advice. -/
lemma exp4_eq_of_subsingleton [Subsingleton β] (η η' : ℝ) :
    exp4 (α := α) (β := β) η = exp4 η' := by
  have hQ : ∀ η₀ n (h : Hist (β → simplex α) α ℝ n), exp4ExpertWeights η₀ n h = 1 := by
    intro η₀ n h
    funext m
    have := sum_softmax (η₀ • exp4Sum η₀ n h)
    rwa [Fintype.sum_subsingleton _ m] at this
  simp_rw [exp4_def, exp4Weights_def, hQ]

end Algorithm

section History

variable {Ω : Type*} (O : ℕ → Ω → β → simplex α) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ)

/-- Along a sequence of observations `O`, actions `A` and feedbacks `Y`, the cumulative reward
estimates of the experts in Exp4 after `n` rounds are the sums of the estimates
`O t m ⬝ᵥ X̂ t` of the rounds `t < n`, with `X̂ t` the loss-based importance-weighted estimates of
the rewards of the arms. -/
lemma exp4Sum_history (n : ℕ) (ω : Ω) :
    exp4Sum η n (history O A Y n ω) = ∑ t ∈ range n, fun m ↦ (O t ω m : α → ℝ) ⬝ᵥ
      lossIwEstimator (exp4Weights η t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) := by
  induction n with
  | zero => simp
  | succ n ih => simp [exp4Sum_succ, Finset.sum_range_succ, ih, history_apply]

/-- **Exp4 as exponential weights on losses.** Along a sequence of observations `O`, actions `A`
and feedbacks `Y`, the weights of Exp4 on the experts at round `n` are the exponential weights of
`-η` times the cumulative estimated losses `O t m ⬝ᵥ Ŷ t` of the experts, with `Ŷ t` the
importance-weighted estimates of the losses `1 - Y t`, since the advice of each expert sums to
`1`. -/
lemma exp4ExpertWeights_history_eq (n : ℕ) (ω : Ω) :
    exp4ExpertWeights η n (history O A Y n ω) = softmax (-(η • ∑ t ∈ range n, fun m ↦
      (O t ω m : α → ℝ) ⬝ᵥ iwEstimator (exp4Weights η t (history O A Y t ω) (O t ω)) (A t ω)
        (1 - Y t ω))) := by
  rw [exp4ExpertWeights_def, exp4Sum_history, ← softmax_add_const _ (-(η * n))]
  congr 1
  funext m
  have hsum : ∀ t, (O t ω m : α → ℝ) ⬝ᵥ 1 = 1 := fun t ↦ by
    simpa [dotProduct] using (mem_simplex_iff.1 (O t ω m).2).2
  simp only [lossIwEstimator_def, dotProduct_sub, hsum, Pi.smul_apply, Finset.sum_apply,
    Pi.neg_apply, smul_eq_mul, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
  ring

end History

section Exp3

omit [Fintype β] in
/-- **Exp3 is Exp4 with one expert per arm.** Along a history whose observations are the advice of
the experts `α` that each recommend one arm, the weights of Exp4 on the experts are the weights of
Exp3. -/
lemma exp4ExpertWeights_eq_exp3Weights (n : ℕ) (h : Hist (α → simplex α) α ℝ n)
    (hh : ∀ i, (h i).obs = fun a ↦ ⟨Pi.single a 1, single_mem_simplex a⟩) :
    exp4ExpertWeights η n h = exp3Weights η n h := by
  rw [exp4ExpertWeights_def, exp3Weights_def]
  congr 2
  induction n with
  | zero => simp
  | succ n ih =>
    rw [exp4Sum_succ, exp3Sum_succ, ih (Fin.init h) fun i ↦ hh _, hh, exp4Weights_def,
      exp4ExpertWeights_def, ih (Fin.init h) fun i ↦ hh _, ← exp3Weights_def]
    congr 1
    funext m
    simp only [← pi_eq_sum_univ']
    simp [dotProduct, Pi.single_apply]

omit [Fintype β] in
/-- **Exp3 is Exp4 with one expert per arm.** Along a history whose observations are the advice of
the experts `α` that each recommend one arm, and for that advice at the current round, the weights
of Exp4 on the arms are the weights of Exp3. -/
lemma exp4Weights_eq_exp3Weights (n : ℕ) (h : Hist (α → simplex α) α ℝ n)
    (hh : ∀ i, (h i).obs = fun a ↦ ⟨Pi.single a 1, single_mem_simplex a⟩) :
    exp4Weights η n h (fun a ↦ ⟨Pi.single a 1, single_mem_simplex a⟩) = exp3Weights η n h := by
  rw [exp4Weights_def, ← exp4ExpertWeights_eq_exp3Weights n h hh]
  exact (pi_eq_sum_univ' _).symm

end Exp3

namespace Exp4

section Pathwise

variable {Ω : Type*} {n : ℕ}

omit [Fintype β] in
/-- The estimate `e m ⬝ᵥ X̂` of the reward of an expert `m` whose advice `e m` sums to `1`, from the
loss-based importance-weighted estimates `X̂` of the rewards of the arms. -/
private lemma dotProduct_lossIwEstimator_advice (e : β → simplex α) (m : β) (p : α → ℝ) (b : α)
    (y : ℝ) :
    (e m : α → ℝ) ⬝ᵥ lossIwEstimator p b y = 1 - (e m : α → ℝ) b * (1 - y) / p b :=
  dotProduct_lossIwEstimator (mem_simplex_iff.1 (e m).2).2

variable [Nonempty β]

/-- The `Q`-average of the estimated rewards `e m ⬝ᵥ X̂` of the experts, with
`Q = exp4ExpertWeights η n h` the weights of Exp4 on the experts and `X̂` the loss-based
importance-weighted estimates of the weights `P = exp4Weights η n h e` on the arms, is the observed
reward `y` of an arm `b` with `P b ≠ 0`, since it is the `P`-average of `X̂`. -/
lemma sum_exp4ExpertWeights_mul_dotProduct_lossIwEstimator (n : ℕ)
    (h : Hist (β → simplex α) α ℝ n) (e : β → simplex α) {b : α} (y : ℝ)
    (hb : exp4Weights η n h e b ≠ 0) :
    ∑ m, exp4ExpertWeights η n h m * (e m : α → ℝ) ⬝ᵥ lossIwEstimator (exp4Weights η n h e) b y =
      y := by
  simp_rw [← smul_eq_mul, ← smul_dotProduct, ← sum_dotProduct, ← exp4Weights_def]
  exact sum_mul_lossIwEstimator (mem_simplex_iff.1 (exp4Weights_mem_simplex _ _ _)).2 hb

/-- **Pathwise regret of the experts' weights in Exp4** [LS, Lemma 18.2]. Along every sequence of
observations `O`, actions `A` and feedbacks `Y ≤ 1` of the rounds `t < n`, with `Q t` the weights
of Exp4 on the experts at round `t` and `X̂ᴱ t m = O t m ⬝ᵥ X̂ t` the estimated reward of expert
`m`, for every expert `m` and `η > 0`,
`∑ t < n, (X̂ᴱ t m - ∑ m', Q t m' * X̂ᴱ t m') ≤
  log M / η + η / 2 * ∑ t < n, ∑ m', Q t m' * (1 - X̂ᴱ t m') ^ 2`,
with `M` the number of experts. -/
theorem sum_sub_sum_le (hη : 0 < η) (O : ℕ → Ω → β → simplex α) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → ℝ) (ω : Ω) (hY : ∀ t < n, Y t ω ≤ 1) (m : β) :
    ∑ t ∈ range n, ((O t ω m : α → ℝ) ⬝ᵥ
        lossIwEstimator (exp4Weights η t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) -
      ∑ m', exp4ExpertWeights η t (history O A Y t ω) m' * (O t ω m' : α → ℝ) ⬝ᵥ
        lossIwEstimator (exp4Weights η t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω)) ≤
      log (Fintype.card β) / η + η / 2 * ∑ t ∈ range n,
        ∑ m', exp4ExpertWeights η t (history O A Y t ω) m' * (1 - (O t ω m' : α → ℝ) ⬝ᵥ
          lossIwEstimator (exp4Weights η t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω)) ^ 2 := by
  -- the exponential-weights bound for the nonnegative estimated losses `y t` of the experts
  set y : ℕ → β → ℝ := fun t m' ↦ (O t ω m' : α → ℝ) ⬝ᵥ
    iwEstimator (exp4Weights η t (history O A Y t ω) (O t ω)) (A t ω) (1 - Y t ω) with hy
  have hy0 : ∀ t < n, ∀ m', 0 ≤ y t m' := fun t ht m' ↦ Finset.sum_nonneg fun a _ ↦
    mul_nonneg ((mem_simplex_iff.1 (O t ω m').2).1 a) (iwEstimator_nonneg
      ((mem_simplex_iff.1 (exp4Weights_mem_simplex _ _ _)).1 _) (sub_nonneg.2 (hY t ht)))
  have key := softmax_regret_le hη hy0 m
  have hqw : ∀ t, softmax (-(η • ∑ s ∈ range t, y s)) =
      exp4ExpertWeights η t (history O A Y t ω) := fun t ↦
    (exp4ExpertWeights_history_eq O A Y t ω).symm
  simp only [hqw] at key
  -- the estimated rewards are one minus the estimated losses
  have hX : ∀ t m', (O t ω m' : α → ℝ) ⬝ᵥ
      lossIwEstimator (exp4Weights η t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) =
        1 - y t m' := fun t m' ↦ by
    simp only [dotProduct_lossIwEstimator_advice, hy, dotProduct_iwEstimator]
  have h1 : ∀ t, (1 - y t m) - ∑ m', exp4ExpertWeights η t (history O A Y t ω) m' *
      (1 - y t m') = ∑ m', exp4ExpertWeights η t (history O A Y t ω) m' * y t m' - y t m :=
    fun t ↦ by
      simp only [mul_sub, mul_one, sum_sub_distrib,
        (mem_simplex_iff.1 (exp4ExpertWeights_mem_simplex t _)).2]
      ring
  simp only [hX, h1, sub_sub_cancel]
  exact key

omit [Nonempty β] in
/-- **The second-order term of Exp4.** Along every sequence of observations `O`, actions `A` and
feedbacks `Y`, with `Q t` and `P t` the weights of Exp4 on the experts and on the arms at round `t`
and `X̂ᴱ t m = O t m ⬝ᵥ X̂ t` the estimated reward of expert `m`,
`∑ m', Q t m' * (1 - X̂ᴱ t m') ^ 2 ≤ (1 - Y t) ^ 2 / P t (A t)`. -/
lemma sum_mul_one_sub_sq_le (O : ℕ → Ω → β → simplex α) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ)
    (ω : Ω) (t : ℕ) :
    ∑ m', exp4ExpertWeights η t (history O A Y t ω) m' * (1 - (O t ω m' : α → ℝ) ⬝ᵥ
        lossIwEstimator (exp4Weights η t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω)) ^ 2 ≤
      (1 - Y t ω) ^ 2 / exp4Weights η t (history O A Y t ω) (O t ω) (A t ω) := by
  set P := exp4Weights η t (history O A Y t ω) (O t ω) (A t ω) with hP
  set q := exp4ExpertWeights η t (history O A Y t ω) with hq
  set e : β → ℝ := fun m' ↦ (O t ω m' : α → ℝ) (A t ω) with he
  simp only [dotProduct_lossIwEstimator_advice, sub_sub_cancel]
  -- `∑ m', q m' * e m' ^ 2 ≤ ∑ m', q m' * e m' = P`, as the advice lies in `[0, 1]`
  have hle : ∑ m', q m' * e m' ^ 2 ≤ P := by
    rw [hP, exp4Weights_apply]
    refine Finset.sum_le_sum fun m' _ ↦ mul_le_mul_of_nonneg_left ?_ (softmax_nonneg _ m')
    have h0 : 0 ≤ e m' := (mem_simplex_iff.1 (O t ω m').2).1 _
    have h1 : e m' ≤ 1 := by simpa using (simplex_subset_Icc (O t ω m').2).2 (A t ω)
    nlinarith
  calc ∑ m', q m' * ((O t ω m' : α → ℝ) (A t ω) * (1 - Y t ω) / P) ^ 2
  _ = (∑ m', q m' * e m' ^ 2) * ((1 - Y t ω) / P) ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun m' _ ↦ by rw [he, mul_div_assoc]; ring
  _ ≤ P * ((1 - Y t ω) / P) ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  _ = (1 - Y t ω) ^ 2 / P := by
      rcases eq_or_ne P 0 with h0 | h0
      · simp [h0]
      · field_simp

/-- **Pathwise bound on the estimated regret of Exp4.** Along every sequence of observations `O`,
actions `A` and feedbacks `Y ≤ 1` of the rounds `t < n` whose actions have positive weight
`P t (A t)`, with `X̂ᴱ t m = O t m ⬝ᵥ X̂ t` the estimated reward of expert `m`, for every expert `m`
and `η > 0`,
`∑ t < n, (X̂ᴱ t m - Y t) ≤ log M / η + η / 2 * ∑ t < n, (1 - Y t) ^ 2 / P t (A t)`. -/
theorem sum_dotProduct_lossIwEstimator_sub_le (hη : 0 < η) (O : ℕ → Ω → β → simplex α)
    (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ) (ω : Ω) (hY : ∀ t < n, Y t ω ≤ 1)
    (hpos : ∀ t < n, exp4Weights η t (history O A Y t ω) (O t ω) (A t ω) ≠ 0) (m : β) :
    ∑ t ∈ range n, ((O t ω m : α → ℝ) ⬝ᵥ
        lossIwEstimator (exp4Weights η t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) - Y t ω) ≤
      log (Fintype.card β) / η + η / 2 * ∑ t ∈ range n,
        (1 - Y t ω) ^ 2 / exp4Weights η t (history O A Y t ω) (O t ω) (A t ω) := by
  calc ∑ t ∈ range n, ((O t ω m : α → ℝ) ⬝ᵥ
        lossIwEstimator (exp4Weights η t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) - Y t ω)
  _ = ∑ t ∈ range n, ((O t ω m : α → ℝ) ⬝ᵥ
        lossIwEstimator (exp4Weights η t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) -
      ∑ m', exp4ExpertWeights η t (history O A Y t ω) m' * (O t ω m' : α → ℝ) ⬝ᵥ
        lossIwEstimator (exp4Weights η t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω)) :=
      Finset.sum_congr rfl fun t ht ↦ by
        rw [sum_exp4ExpertWeights_mul_dotProduct_lossIwEstimator _ _ _ _ (hpos t (mem_range.1 ht))]
  _ ≤ _ := sum_sub_sum_le hη O A Y ω hY m
  _ ≤ _ := by
      gcongr with t ht
      exact sum_mul_one_sub_sq_le O A Y ω t

end Pathwise

section Run

variable [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α] [Nonempty β]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → β → simplex α} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}
  {env : Environment (β → simplex α) α ℝ} {E : ℕ → β → simplex α} {x : ℕ → α → ℝ} {n t : ℕ}

omit [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α] [Nonempty β]
  [IsProbabilityMeasure P] in
/-- When the observation and the feedback of round `t` are almost surely the advice `E t` and the
reward `x t (A t)`, the estimated loss `O t m (A t) (1 - Y t) / P t (A t)` of expert `m` is almost
surely the inverse-weighted value of `b ↦ E t m b * (1 - x t b)` at the action. -/
private lemma advice_mul_div_ae_eq (hO : O t =ᵐ[P] fun _ ↦ E t) (hY : Y t =ᵐ[P] x t ∘ A t)
    (m : β) :
    (fun ω ↦ (O t ω m : α → ℝ) (A t ω) * (1 - Y t ω) /
        exp4Weights η t (history O A Y t ω) (O t ω) (A t ω)) =ᵐ[P]
      fun ω ↦ (E t m : α → ℝ) (A t ω) * (1 - x t (A t ω)) /
        exp4Weights η t (history O A Y t ω) (O t ω) (A t ω) := by
  filter_upwards [hO, hY] with ω hωO hωY
  rw [hωO, hωY, Function.comp_apply]

omit [Nonempty α] in
/-- Along a run of Exp4 whose observation of round `t` is the advice `E t` and whose feedback is
the reward `x t (A t)` of its action, the estimated reward `X̂ᴱ t m = O t m ⬝ᵥ X̂ t` of expert `m`
is integrable. -/
lemma integrable_dotProduct_lossIwEstimator (hO : O t =ᵐ[P] fun _ ↦ E t)
    (hY : Y t =ᵐ[P] x t ∘ A t) (h : IsAlgEnvSeq O A Y (exp4 η) env P) (m : β) :
    Integrable (fun ω ↦ (O t ω m : α → ℝ) ⬝ᵥ
      lossIwEstimator (exp4Weights η t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω)) P := by
  simp only [dotProduct_lossIwEstimator_advice]
  exact (integrable_const 1).sub ((WeightAlgorithm.integrable_div_weights h t
    (fun b ↦ (E t m : α → ℝ) b * (1 - x t b))).congr (advice_mul_div_ae_eq hO hY m).symm)

/-- **The estimated rewards of the experts are unbiased** [LS, (18.10)]. Along a run of Exp4 whose
observation of round `t` is the advice `E t` and whose feedback is the reward `x t (A t)` of its
action, the estimated reward `X̂ᴱ t m = O t m ⬝ᵥ X̂ t` of expert `m` has expectation
`E t m ⬝ᵥ x t`, the expected reward of following its advice. -/
theorem integral_dotProduct_lossIwEstimator (hO : O t =ᵐ[P] fun _ ↦ E t)
    (hY : Y t =ᵐ[P] x t ∘ A t) (h : IsAlgEnvSeq O A Y (exp4 η) env P) (m : β) :
    P[fun ω ↦ (O t ω m : α → ℝ) ⬝ᵥ
      lossIwEstimator (exp4Weights η t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω)] =
      (E t m : α → ℝ) ⬝ᵥ x t := by
  simp only [dotProduct_lossIwEstimator_advice]
  -- the advice of `m` vanishes on the arms of weight zero, as `m` has positive weight
  have hc : ∀ᵐ ω ∂P, ∀ b, exp4Weights η t (history O A Y t ω) (O t ω) b = 0 →
      (E t m : α → ℝ) b * (1 - x t b) = 0 := by
    filter_upwards [hO] with ω hω b hb
    have hle := exp4ExpertWeights_mul_le_exp4Weights (η := η) t (history O A Y t ω) (O t ω) m b
    rw [hb, hω] at hle
    have h0 := (mem_simplex_iff.1 (E t m).2).1 b
    have : (E t m : α → ℝ) b = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right hle (exp4ExpertWeights_pos t _ m)) h0
    rw [this, zero_mul]
  rw [integral_sub (integrable_const 1) ((WeightAlgorithm.integrable_div_weights h t
      (fun b ↦ (E t m : α → ℝ) b * (1 - x t b))).congr (advice_mul_div_ae_eq hO hY m).symm),
    integral_congr_ae (advice_mul_div_ae_eq hO hY m),
    WeightAlgorithm.integral_div_weights h t (c := fun b ↦ (E t m : α → ℝ) b * (1 - x t b)) hc]
  simp only [integral_const, probReal_univ, one_smul, mul_sub, mul_one, sum_sub_distrib,
    (mem_simplex_iff.1 (E t m).2).2, dotProduct]
  ring

/-- **Regret of Exp4.** Along a run of Exp4 with learning rate `η > 0` whose observation of every
round `t < n` is the advice `E t` and whose feedback is the reward `x t (A t) ∈ [0, 1]` of its
action, the regret against the best expert after `n` rounds is at most `log M / η + η n k / 2`,
with `k` the number of arms and `M` the number of experts. -/
theorem expertRegret_le (hη : 0 < η) (hO : ∀ t < n, O t =ᵐ[P] fun _ ↦ E t)
    (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t) (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp4 η) env P) :
    expertRegret (fun t m ↦ (E t m : α → ℝ)) x A P n ≤
      log (Fintype.card β) / η + η * n * Fintype.card α / 2 := by
  set X : ℕ → β → Ω → ℝ := fun t m ω ↦ (O t ω m : α → ℝ) ⬝ᵥ
    lossIwEstimator (exp4Weights η t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) with hXdef
  set V : ℕ → Ω → ℝ := fun t ω ↦
    (1 - Y t ω) ^ 2 / exp4Weights η t (history O A Y t ω) (O t ω) (A t ω) with hV
  have hVint : ∀ t ∈ range n, Integrable (V t) P := fun t ht ↦
    (WeightAlgorithm.integrable_div_weights h t fun b ↦ (1 - x t b) ^ 2).congr
      (comp_feedback_ae_eq (hY t (mem_range.1 ht))
        fun z b y ↦ (1 - y) ^ 2 / exp4Weights η t z.1 z.2 b).symm
  have hYint := fun t (ht : t ∈ range n) ↦
    h.integrable_feedback_of_ae_eq (hY t (mem_range.1 ht))
  have hXint : ∀ m, ∀ t ∈ range n, Integrable (X t m) P := fun m t ht ↦
    integrable_dotProduct_lossIwEstimator (hO t (mem_range.1 ht)) (hY t (mem_range.1 ht)) h m
  -- almost surely, the feedbacks are at most `1` and the actions have positive weight
  have hgood : ∀ᵐ ω ∂P, (∀ t < n, Y t ω ≤ 1) ∧
      ∀ t, exp4Weights η t (history O A Y t ω) (O t ω) (A t ω) ≠ 0 := by
    refine (ae_all_iff.2 fun t ↦ ?_).and
      (ae_all_iff.2 fun t ↦ (WeightAlgorithm.ae_pos_weights_action h t).mono fun _ h ↦ h.ne')
    by_cases ht : t < n
    · filter_upwards [hY t ht] with ω hω _
      rw [hω]
      exact (hx t ht _).2
    · exact ae_of_all _ fun _ ht' ↦ absurd ht' ht
  -- `∑ t < n, E[V t] ≤ n k`, as `(1 - x t b) ^ 2 ≤ 1`
  have hle : ∑ t ∈ range n, P[V t] ≤ (n * Fintype.card α : ℝ) := by
    calc ∑ t ∈ range n, P[V t]
    _ ≤ ∑ t ∈ range n, ∑ b, (1 - x t b) ^ 2 := Finset.sum_le_sum fun t ht ↦ by
        rw [hV, integral_congr_ae (comp_feedback_ae_eq (hY t (mem_range.1 ht))
          fun z b y ↦ (1 - y) ^ 2 / exp4Weights η t z.1 z.2 b)]
        exact WeightAlgorithm.integral_div_weights_le h t (c := fun b ↦ (1 - x t b) ^ 2)
          fun b ↦ sq_nonneg _
    _ ≤ ∑ t ∈ range n, ∑ _b : α, (1 : ℝ) := Finset.sum_le_sum fun t ht ↦
        Finset.sum_le_sum fun b _ ↦ by
          obtain ⟨h0, h1⟩ := hx t (mem_range.1 ht) b
          nlinarith
    _ = n * Fintype.card α := by simp
  refine expertRegret_le_iff.2 fun m ↦ ?_
  -- the regret against `m` is the expectation of its estimated regret
  have hreg : ∑ t ∈ range n, ∑ a, (E t m : α → ℝ) a * x t a -
      P[fun ω ↦ ∑ t ∈ range n, x t (A t ω)] = P[fun ω ↦ ∑ t ∈ range n, (X t m ω - Y t ω)] := by
    rw [integral_finsetSum (f := fun t ω ↦ X t m ω - Y t ω) _
        fun t ht ↦ (hXint m t ht).sub (hYint t ht),
      integral_finsetSum (f := fun t ω ↦ x t (A t ω)) _
        fun t ht ↦ (hYint t ht).congr (hY t (mem_range.1 ht)),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    rw [integral_sub (hXint m t ht) (hYint t ht), hXdef,
      integral_dotProduct_lossIwEstimator (hO t (mem_range.1 ht)) (hY t (mem_range.1 ht)) h m,
      integral_congr_ae (hY t (mem_range.1 ht)), Function.comp_def, dotProduct]
  rw [hreg]
  calc P[fun ω ↦ ∑ t ∈ range n, (X t m ω - Y t ω)]
  _ ≤ P[fun ω ↦ log (Fintype.card β) / η + η / 2 * ∑ t ∈ range n, V t ω] := by
      refine integral_mono_ae (integrable_finsetSum _ fun t ht ↦ (hXint m t ht).sub (hYint t ht))
        ((integrable_const _).add ((integrable_finsetSum _ hVint).const_mul _)) ?_
      filter_upwards [hgood] with ω hω
      exact sum_dotProduct_lossIwEstimator_sub_le hη O A Y ω hω.1 (fun t _ ↦ hω.2 t) m
  _ = log (Fintype.card β) / η + η / 2 * ∑ t ∈ range n, P[V t] := by
      rw [integral_add (integrable_const _) ((integrable_finsetSum _ hVint).const_mul _),
        integral_const_mul, integral_finsetSum _ hVint, integral_const, probReal_univ,
        one_smul]
  _ ≤ log (Fintype.card β) / η + η * n * Fintype.card α / 2 := by
      have := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ η / 2)
      linarith

/-- **Regret of Exp4 with a single expert.** Along a run of Exp4 with any learning rate whose
observation of every round `t < n` is the advice `E t` of the single expert and whose feedback is
the reward `x t (A t) ∈ [0, 1]` of its action, the regret against that expert is nonpositive: Exp4
follows the advice for every learning rate, so the regret is at most `η' n k / 2` for all
`η' > 0`. -/
theorem expertRegret_nonpos_of_subsingleton [Subsingleton β]
    (hO : ∀ t < n, O t =ᵐ[P] fun _ ↦ E t) (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t)
    (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1) (h : IsAlgEnvSeq O A Y (exp4 η) env P) :
    expertRegret (fun t m ↦ (E t m : α → ℝ)) x A P n ≤ 0 := by
  set k : ℝ := (Fintype.card α : ℝ) with hk
  have hM : (Fintype.card β : ℝ) = 1 := by
    exact_mod_cast le_antisymm (Fintype.card_le_one_iff_subsingleton.2 ‹_›) Fintype.card_pos
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hc : 0 ≤ (n : ℝ) * k := by positivity
  have hη' : 0 < ε / (n * k + 1) := by positivity
  have hle := expertRegret_le hη' hO hY hx (exp4_eq_of_subsingleton (α := α) (β := β) _ _ ▸ h)
  rw [hM, log_one, zero_div, zero_add, ← hk] at hle
  refine hle.trans ?_
  have h1 : ε / (n * k + 1) * (n * k) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : ε / (n * k + 1) * n * k / 2 = ε / (n * k + 1) * (n * k) / 2 := by ring
  rw [h2, zero_add]
  linarith [(by positivity : 0 ≤ ε / (n * k + 1) * (n * k))]

/-- **Regret of Exp4** [LS, Theorem 18.1]: along a run of Exp4 with learning rate
`η = √(2 log M / (n k))` whose observation of every round `t < n` is the advice `E t` and whose
feedback is the reward `x t (A t) ∈ [0, 1]` of its action, the regret against the best expert after
`n` rounds is at most `√(2 n k log M)`, with `k` the number of arms and `M` the number of
experts. -/
theorem expertRegret_le_sqrt (hO : ∀ t < n, O t =ᵐ[P] fun _ ↦ E t)
    (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t) (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp4 √(2 * log (Fintype.card β) / (n * Fintype.card α))) env P) :
    expertRegret (fun t m ↦ (E t m : α → ℝ)) x A P n ≤
      √(2 * n * Fintype.card α * log (Fintype.card β)) := by
  set k : ℝ := (Fintype.card α : ℝ) with hk
  set M : ℝ := (Fintype.card β : ℝ) with hM
  have hk0 : 0 < k := by
    rw [hk, Nat.cast_pos]
    exact Fintype.card_pos
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM, Nat.one_le_cast]
    exact Fintype.card_pos
  -- with one expert, the regret is nonpositive
  rcases hM1.eq_or_lt with hM1 | hM1
  · have hcard : Fintype.card β ≤ 1 := by
      rw [hM] at hM1
      exact_mod_cast hM1.ge
    have : Subsingleton β := Fintype.card_le_one_iff_subsingleton.1 hcard
    rw [← hM1, log_one, mul_zero, sqrt_zero]
    exact expertRegret_nonpos_of_subsingleton hO hY hx h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [expertRegret_def]
  have hL : 0 < log M := log_pos hM1
  have hm : 0 < n * k := mul_pos (by exact_mod_cast hn) hk0
  set η := √(2 * log M / (n * k)) with hη
  have hη0 : 0 < η := sqrt_pos.2 (by positivity)
  -- with `η ^ 2 = 2 log M / (n k)`, both terms of the bound are `η n k / 2`
  have hηsq : η ^ 2 = 2 * log M / (n * k) := sq_sqrt (by positivity)
  refine (expertRegret_le hη0 hO hY hx h).trans (le_of_eq ?_)
  have hsq : √(2 * n * k * log M) = η * (n * k) := by
    rw [← sqrt_sq (by positivity : 0 ≤ η * (n * k)), mul_pow, hηsq]
    congr 1
    field_simp
  -- `log M / η = η n k / 2`, from `η ^ 2 = 2 log M / (n k)`
  have hlog : log M / η = η * (n * k) / 2 := by
    rw [div_eq_iff hη0.ne']
    rw [eq_div_iff hm.ne'] at hηsq
    linear_combination -hηsq / 2
  rw [hsq, hlog]
  ring

end Run

end Exp4

section OfSeq

variable [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α] [Nonempty β]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → β → simplex α} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {E : ℕ → β → simplex α}
  {x : ℕ → α → ℝ} {hxm : ∀ t, Measurable (x t)} {n : ℕ}

/-- **Regret of Exp4** against oblivious experts and rewards: along a run of Exp4 with learning
rate `η > 0` against `Environment.ofSeq E x _`, which announces the advice `E t` and pays the
reward `x t a ∈ [0, 1]` of the action `a` at the rounds `t < n`, the regret against the best expert
after `n` rounds is at most `log M / η + η n k / 2`. -/
theorem exp4_expertRegret_le (hη : 0 < η) (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp4 η) (Environment.ofSeq E x hxm) P) :
    expertRegret (fun t m ↦ (E t m : α → ℝ)) x A P n ≤
      log (Fintype.card β) / η + η * n * Fintype.card α / 2 :=
  Exp4.expertRegret_le hη (fun t _ ↦ h.obs_ofSeq_ae_eq t) (fun t _ ↦ h.feedback_ofSeq_ae_eq t) hx h

/-- **Regret of Exp4** [LS, Theorem 18.1]: along a run of Exp4 with learning rate
`η = √(2 log M / (n k))` against `Environment.ofSeq E x _`, which announces the advice `E t` and
pays the reward `x t a ∈ [0, 1]` of the action `a` at the rounds `t < n`, the regret against the
best expert after `n` rounds is at most `√(2 n k log M)`, with `k` the number of arms and `M` the
number of experts. -/
theorem exp4_expertRegret_le_sqrt (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp4 √(2 * log (Fintype.card β) / (n * Fintype.card α)))
      (Environment.ofSeq E x hxm) P) :
    expertRegret (fun t m ↦ (E t m : α → ℝ)) x A P n ≤
      √(2 * n * Fintype.card α * log (Fintype.card β)) :=
  Exp4.expertRegret_le_sqrt (fun t _ ↦ h.obs_ofSeq_ae_eq t) (fun t _ ↦ h.feedback_ofSeq_ae_eq t)
    hx h

end OfSeq

end LMLExplore.Bandits
