/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.ImportanceWeighted
public import LMLExplore.OnlineLearning.ExponentialWeights

/-!
# Exp4-IX

In a bandit with expert advice, each expert `m` of a finite set `β` recommends at round `t` a
distribution over the arms `α`, and the learner sees this advice before acting. Exp4-IX
[Neu15, Section 3.2] computes the advice `E t = adv (O t)` from the observation `O t` of round `t`
through a fixed advice map `adv : 𝓞 → β → simplex α`, and plays at round `t`:

* the weights `Q t = softmax (-(η t • L̂ᴱ t))` on the experts, the exponential weights of the
  cumulative estimated losses `L̂ᴱ t = ∑ s < t, E s Ŷ s` of the experts, where
  `(E s Ŷ s) m = E s m ⬝ᵥ Ŷ s` is the estimated loss of following expert `m` at round `s`;
* an arm drawn from the mixture `P t = ∑ m, Q t m • E t m` of the advice;
* the implicit-exploration estimates `Ŷ t a = 𝟙{A t = a} (1 - Y t) / (P t a + γ t)` of the losses
  `1 - Y t` [LS, (12.4); Neu15, (3)], from the action `A t` and the observed reward `Y t`.

The learning rates `η t > 0` and the implicit-exploration parameters `γ t ≥ 0` are sequences fixed
in advance, used at round `t`; a constant sequence is a rate tuned for the horizon.

Exp4-IX is the single algorithm of the three importance-weighted algorithms of [LS], which use
constant rates, and which are defined as its instances: `exp4` [LS, Algorithm 11]
(`Bandits/Exp4/Basic.lean`) is the case `γ = 0` with the advice observed directly (`adv = id`),
and `exp3IX` [LS, Algorithm 10] (`Bandits/Exp3/IX.lean`) and `exp3` [LS, Algorithm 9]
(`Bandits/Exp3/Basic.lean`) are the cases with the experts `α`, expert `b` advising the Dirac mass
at `b` at every observation, with any constant `γ` and with `γ = 0`. Along every run,
the weights `Q t` are the exponential weights of the nonnegative estimated losses of the experts,
so the local-norm bound of exponential weights with nonincreasing learning rates holds pathwise:
against every expert `m`, with `M` the number of experts,
`∑ t < n, (⟨Q t, E t Ŷ t⟩ - E t m ⬝ᵥ Ŷ t) ≤
  log M / η (n - 1) + ∑ t < n, η t / 2 * ⟨Q t, (E t Ŷ t) ^ 2⟩`,
which is [LS, Lemma 18.2] for a constant rate, and follows [Ora, Section 7.5; BCB12, proof of
Theorem 3.1] for nonincreasing rates. Adding the bias `γ t ∑ a, Ŷ t a` of the
implicit-exploration estimates [LS, Lemma 12.4] bounds the estimated regret against expert `m` by
`log M / η (n - 1) + ∑ t < n, (γ t + η t / 2) * ∑ a, Ŷ t a` for rewards in `[0, 1]`.

## Main definitions

* `LMLExplore.Bandits.exp4IXSum adv η γ n h`: the cumulative estimated losses `L̂ᴱ n` of the
  experts, computed from the history `h` of the first `n` rounds.
* `LMLExplore.Bandits.exp4IXExpertWeights adv η γ n h`: the weights
  `Q n = softmax (-(η n • L̂ᴱ n))` of Exp4-IX on the experts at round `n`.
* `LMLExplore.Bandits.exp4IXWeights adv η γ n h o`: the weights `P n = ∑ m, Q n m • adv o m` of
  Exp4-IX on the arms at round `n`, for the observation `o` of round `n`.
* `LMLExplore.Bandits.exp4IX adv hadv η γ`: the Exp4-IX algorithm.
* `LMLExplore.Bandits.singleAdvice`: the advice of the experts `α` that each recommend one arm,
  expert `b` advising the Dirac mass at `b` at every observation, which gives Exp3 and Exp3-IX.

## Main statements

* `exp4IXWeights_mem_simplex`: the weights of Exp4-IX on the arms are a probability vector.
* `exp4IXExpertWeights_history_eq`: along every sequence of observations, actions and feedbacks,
  the weights of Exp4-IX on the experts are the exponential weights of `-η n` times the cumulative
  estimated losses of the experts.
* `exp4IX_eq_of_subsingleton`: with a single expert, Exp4-IX does not depend on its parameters.
* `Exp4IX.isAlgEnvSeq_weightAlgorithm`: a run of Exp4-IX is a run of the weight-based algorithm
  with its weights on the arms.
* `Exp4IX.sum_exp4IXExpertWeights_mul_dotProduct_lossIwEstimator`: the `Q t`-average of the
  estimated rewards `X̂ᴱ t` of the experts is the observed reward `Y t`.
* `Exp4IX.sum_mul_one_sub_sq_le`: the second-order term of the estimated rewards satisfies
  `⟨Q t, (1 - X̂ᴱ t) ^ 2⟩ ≤ (1 - Y t) ^ 2 / P t (A t)`.
* `Exp4IX.sum_sum_mul_sub_le`: the local-norm bound of the weights of Exp4-IX on the experts,
  [LS, Lemma 18.2] for a constant rate, with nonincreasing learning rates as in
  [Ora, Section 7.5; BCB12, proof of Theorem 3.1].
* `Exp4IX.sum_sum_mul_sub_dotProduct_le`: the same bound with the second-order term
  `⟨P t, (Ŷ t) ^ 2⟩` on the arms.
* `Exp4IX.sum_one_sub_sub_dotProduct_le`: the pathwise bound on the estimated regret against an
  expert, for rewards in `[0, 1]`.

## References

* [BCB12] S. Bubeck and N. Cesa-Bianchi, *Regret analysis of stochastic and nonstochastic
  multi-armed bandit problems*, Foundations and Trends in Machine Learning 5(1), 2012.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
* [Neu15] G. Neu, *Explore no more: improved high-probability regret bounds for non-stochastic
  bandits*, NeurIPS 2015.
* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real LMLExplore.OnlineLearning

namespace LMLExplore.Bandits

variable {α β 𝓞 : Type*} [Fintype α] [DecidableEq α] [Fintype β] {adv : 𝓞 → β → simplex α}
  {η γ : ℕ → ℝ}

section SingleAdvice

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

end SingleAdvice

section Weights

/-- The cumulative estimated losses of the experts in Exp4-IX with advice map `adv`, learning rates
`η` and implicit-exploration parameters `γ`, computed from the history `h` of the first `n` rounds:
`∑ s < n, E s Ŷ s` with `(E s Ŷ s) m = E s m ⬝ᵥ Ŷ s`, for the advice `E s = adv (O s)` of the
observation `O s` of round `s`, the implicit-exploration estimates
`Ŷ s = iwEstimator (P s + γ s) (A s) (1 - X s)` of the losses of round `s`, computed from the
action `A s` and the reward `X s` of round `s` of `h`, and the weights
`P s = ∑ m, softmax (-(η s • ∑ r < s, E r Ŷ r)) m • E s m` on the arms at round `s`. -/
noncomputable def exp4IXSum (adv : 𝓞 → β → simplex α) (η γ : ℕ → ℝ) :
    (n : ℕ) → Hist 𝓞 α ℝ n → β → ℝ
  | 0, _ => 0
  | n + 1, h => exp4IXSum adv η γ n (Fin.init h) + fun m ↦
      (adv (h (Fin.last n)).obs m : α → ℝ) ⬝ᵥ iwEstimator
        (fun a ↦ (∑ m', softmax (-(η n • exp4IXSum adv η γ n (Fin.init h))) m' •
          (adv (h (Fin.last n)).obs m' : α → ℝ)) a + γ n)
        (h (Fin.last n)).action (1 - (h (Fin.last n)).feedback)

/-- The weights of Exp4-IX on the experts after the history `h` of the first `n` rounds: the
softmax of `-η n` times the cumulative estimated losses `exp4IXSum adv η γ n h` of the experts. -/
noncomputable def exp4IXExpertWeights (adv : 𝓞 → β → simplex α) (η γ : ℕ → ℝ) (n : ℕ)
    (h : Hist 𝓞 α ℝ n) : β → ℝ :=
  softmax (-(η n • exp4IXSum adv η γ n h))

/-- The weights of Exp4-IX on the arms after the history `h` of the first `n` rounds, for the
observation `o` of round `n`: the mixture `∑ m, Q m • adv o m` of the advice of the experts with
the weights `Q = exp4IXExpertWeights adv η γ n h`. -/
noncomputable def exp4IXWeights (adv : 𝓞 → β → simplex α) (η γ : ℕ → ℝ) (n : ℕ)
    (h : Hist 𝓞 α ℝ n) (o : 𝓞) : α → ℝ :=
  ∑ m, exp4IXExpertWeights adv η γ n h m • (adv o m : α → ℝ)

lemma exp4IXExpertWeights_def (adv : 𝓞 → β → simplex α) (η γ : ℕ → ℝ) (n : ℕ)
    (h : Hist 𝓞 α ℝ n) :
    exp4IXExpertWeights adv η γ n h = softmax (-(η n • exp4IXSum adv η γ n h)) := (rfl)

lemma exp4IXWeights_def (adv : 𝓞 → β → simplex α) (η γ : ℕ → ℝ) (n : ℕ) (h : Hist 𝓞 α ℝ n)
    (o : 𝓞) :
    exp4IXWeights adv η γ n h o = ∑ m, exp4IXExpertWeights adv η γ n h m • (adv o m : α → ℝ) :=
  (rfl)

lemma exp4IXWeights_apply (n : ℕ) (h : Hist 𝓞 α ℝ n) (o : 𝓞) (a : α) :
    exp4IXWeights adv η γ n h o a = ∑ m, exp4IXExpertWeights adv η γ n h m * (adv o m : α → ℝ) a :=
  by simp [exp4IXWeights_def]

@[simp]
lemma exp4IXSum_zero (h : Hist 𝓞 α ℝ 0) : exp4IXSum adv η γ 0 h = 0 := by
  rw [exp4IXSum]

lemma exp4IXSum_succ (n : ℕ) (h : Hist 𝓞 α ℝ (n + 1)) :
    exp4IXSum adv η γ (n + 1) h = exp4IXSum adv η γ n (Fin.init h) + fun m ↦
      (adv (h (Fin.last n)).obs m : α → ℝ) ⬝ᵥ iwEstimator
        (fun a ↦ exp4IXWeights adv η γ n (Fin.init h) (h (Fin.last n)).obs a + γ n)
        (h (Fin.last n)).action (1 - (h (Fin.last n)).feedback) := by
  rw [exp4IXSum, exp4IXWeights_def, exp4IXExpertWeights_def]

/-- The first weights of Exp4-IX on the experts are uniform. -/
@[simp]
lemma exp4IXExpertWeights_zero (h : Hist 𝓞 α ℝ 0) :
    exp4IXExpertWeights adv η γ 0 h = fun _ ↦ (Fintype.card β : ℝ)⁻¹ := by
  simp [exp4IXExpertWeights_def]

lemma exp4IXExpertWeights_pos [Nonempty β] (n : ℕ) (h : Hist 𝓞 α ℝ n) (m : β) :
    0 < exp4IXExpertWeights adv η γ n h m :=
  softmax_pos _ m

lemma exp4IXExpertWeights_mem_simplex [Nonempty β] (n : ℕ) (h : Hist 𝓞 α ℝ n) :
    exp4IXExpertWeights adv η γ n h ∈ simplex β :=
  softmax_mem_simplex _

lemma exp4IXWeights_nonneg (n : ℕ) (h : Hist 𝓞 α ℝ n) (o : 𝓞) (a : α) :
    0 ≤ exp4IXWeights adv η γ n h o a := by
  rw [exp4IXWeights_apply]
  exact Finset.sum_nonneg fun m _ ↦
    mul_nonneg (softmax_nonneg _ m) ((mem_simplex_iff.1 (adv o m).2).1 a)

lemma exp4IXWeights_mem_simplex [Nonempty β] (n : ℕ) (h : Hist 𝓞 α ℝ n) (o : 𝓞) :
    exp4IXWeights adv η γ n h o ∈ simplex α :=
  (convex_simplex α).sum_mem (fun m _ ↦ (exp4IXExpertWeights_pos n h m).le)
    (mem_simplex_iff.1 (exp4IXExpertWeights_mem_simplex n h)).2 fun m _ ↦ (adv o m).2

/-- The weights `exp4IXWeights adv η γ n h o` of Exp4-IX on the arms dominate the contribution
`Q m • adv o m` of every expert `m`, with `Q = exp4IXExpertWeights adv η γ n h`. As `Q m > 0`, the
advice of every expert vanishes on the arms of weight zero. -/
lemma exp4IXExpertWeights_mul_le_exp4IXWeights (n : ℕ) (h : Hist 𝓞 α ℝ n) (o : 𝓞) (m : β)
    (a : α) :
    exp4IXExpertWeights adv η γ n h m * (adv o m : α → ℝ) a ≤ exp4IXWeights adv η γ n h o a := by
  rw [exp4IXWeights_apply]
  exact Finset.single_le_sum
    (f := fun m' ↦ exp4IXExpertWeights adv η γ n h m' * (adv o m' : α → ℝ) a)
    (fun m' _ ↦ mul_nonneg (softmax_nonneg _ m') ((mem_simplex_iff.1 (adv o m').2).1 a))
    (mem_univ m)

/-- The advice of every expert vanishes on the arms of weight zero in Exp4-IX, as every expert has
positive weight. -/
lemma adv_apply_eq_zero_of_exp4IXWeights_eq_zero [Nonempty β] {n : ℕ} {h : Hist 𝓞 α ℝ n} {o : 𝓞}
    {a : α} (ha : exp4IXWeights adv η γ n h o a = 0) (m : β) : (adv o m : α → ℝ) a = 0 := by
  have hle := exp4IXExpertWeights_mul_le_exp4IXWeights (adv := adv) (η := η) (γ := γ) n h o m a
  rw [ha] at hle
  exact le_antisymm (nonpos_of_mul_nonpos_right hle (exp4IXExpertWeights_pos n h m))
    ((mem_simplex_iff.1 (adv o m).2).1 a)

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞]

@[fun_prop]
lemma measurable_exp4IXSum (hadv : Measurable adv) (η γ : ℕ → ℝ) (n : ℕ) :
    Measurable (exp4IXSum adv η γ n) := by
  induction n with
  | zero =>
    rw [funext exp4IXSum_zero]
    exact measurable_const
  | succ n ih =>
    have hS := ih.comp (measurable_finInit (β := fun _ ↦ _))
    have hlast : Measurable fun h : Hist 𝓞 α ℝ (n + 1) ↦ h (Fin.last n) :=
      measurable_pi_apply _
    have hE := hadv.comp (Round.measurable_obs.comp hlast)
    have hadvm : ∀ m, Measurable fun h : Hist 𝓞 α ℝ (n + 1) ↦
        (adv (h (Fin.last n)).obs m : α → ℝ) := fun m ↦
      measurable_subtype_coe.comp ((measurable_pi_apply m).comp hE)
    -- the weights on the arms, shifted by `γ n`, and the estimates of round `n`
    have hP : Measurable fun h : Hist 𝓞 α ℝ (n + 1) ↦
        fun a ↦ exp4IXWeights adv η γ n (Fin.init h) (h (Fin.last n)).obs a + γ n := by
      simp_rw [exp4IXWeights_apply, exp4IXExpertWeights_def]
      have hQ := measurable_softmax.comp (hS.const_smul (η n)).neg
      refine measurable_pi_iff.2 fun a ↦ (Finset.measurable_sum _ fun m _ ↦ ?_).add_const _
      exact ((measurable_pi_apply m).comp hQ).mul ((measurable_pi_apply a).comp (hadvm m))
    have hY := measurable_iwEstimator.comp (hP.prodMk ((Round.measurable_action.comp hlast).prodMk
      ((measurable_const (a := (1 : ℝ))).sub (Round.measurable_feedback.comp hlast))))
    rw [funext (exp4IXSum_succ n)]
    refine hS.add (measurable_pi_iff.2 fun m ↦ ?_)
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun a _ ↦
      ((measurable_pi_apply a).comp (hadvm m)).mul ((measurable_pi_apply a).comp hY)

@[fun_prop]
lemma measurable_exp4IXExpertWeights (hadv : Measurable adv) (η γ : ℕ → ℝ) (n : ℕ) :
    Measurable (exp4IXExpertWeights adv η γ n) :=
  measurable_softmax.comp ((measurable_exp4IXSum hadv η γ n).const_smul (η n)).neg

/-- The weights of Exp4-IX on the arms are a measurable function of the history and the
observation. -/
@[fun_prop]
lemma measurable_exp4IXWeights (hadv : Measurable adv) (η γ : ℕ → ℝ) (n : ℕ) :
    Measurable fun x : Hist 𝓞 α ℝ n × 𝓞 ↦ exp4IXWeights adv η γ n x.1 x.2 := by
  refine measurable_pi_iff.2 fun a ↦ ?_
  simp_rw [exp4IXWeights_apply]
  refine Finset.measurable_sum _ fun m _ ↦ ?_
  exact ((measurable_pi_apply m).comp ((measurable_exp4IXExpertWeights hadv η γ n).comp
    measurable_fst)).mul ((measurable_pi_apply a).comp (measurable_subtype_coe.comp
      ((measurable_pi_apply m).comp (hadv.comp measurable_snd))))

end Weights

section Algorithm

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] [Nonempty β]

/-- **Exp4-IX** with the measurable advice map `adv`, learning rates `η` and implicit-exploration
parameters `γ` [Neu15, Section 3.2]: the weight-based algorithm that observes `o` at round `n` and
draws its action from the weights `exp4IXWeights adv η γ n h o`, the mixture of the advice
`adv o` with the exponential weights of `-η n` times the cumulative estimated losses of the
experts computed from the history `h`. -/
noncomputable def exp4IX (adv : 𝓞 → β → simplex α) (hadv : Measurable adv) (η γ : ℕ → ℝ) :
    Algorithm 𝓞 α ℝ :=
  weightAlgorithm (fun n x ↦ exp4IXWeights adv η γ n x.1 x.2)
    (fun n a ↦ (measurable_pi_apply a).comp (measurable_exp4IXWeights hadv η γ n))
    (fun n x ↦ exp4IXWeights_mem_simplex n x.1 x.2)

lemma exp4IX_def (adv : 𝓞 → β → simplex α) (hadv : Measurable adv) (η γ : ℕ → ℝ) :
    exp4IX adv hadv η γ = weightAlgorithm (fun n x ↦ exp4IXWeights adv η γ n x.1 x.2)
      (fun n a ↦ (measurable_pi_apply a).comp (measurable_exp4IXWeights hadv η γ n))
      (fun n x ↦ exp4IXWeights_mem_simplex n x.1 x.2) := (rfl)

/-- The policy of Exp4-IX at round `n` draws its action from the weights
`exp4IXWeights adv η γ n h o` of the history `h` and the observation `o` of round `n`. -/
@[simp]
lemma exp4IX_policy_apply {hadv : Measurable adv} (n : ℕ) (x : Hist 𝓞 α ℝ n × 𝓞) :
    (exp4IX adv hadv η γ).policy n x = weightedMeasure (exp4IXWeights adv η γ n x.1 x.2) := by
  rw [exp4IX_def, weightAlgorithm_policy, weightKernel_apply]

/-- With a single expert, Exp4-IX does not depend on its learning rates and implicit-exploration
parameters: it follows the advice. -/
lemma exp4IX_eq_of_subsingleton [Subsingleton β] (hadv : Measurable adv) (η γ η' γ' : ℕ → ℝ) :
    exp4IX adv hadv η γ = exp4IX adv hadv η' γ' := by
  have hQ : ∀ (η₀ γ₀ : ℕ → ℝ) n (h : Hist 𝓞 α ℝ n), exp4IXExpertWeights adv η₀ γ₀ n h = 1 := by
    intro η₀ γ₀ n h
    funext m
    have := sum_softmax (-(η₀ n • exp4IXSum adv η₀ γ₀ n h))
    rwa [Fintype.sum_subsingleton _ m] at this
  simp_rw [exp4IX_def, exp4IXWeights_def, hQ]

end Algorithm

section History

variable {Ω : Type*} (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ)

/-- Along a sequence of observations `O`, actions `A` and feedbacks `Y`, the cumulative estimated
losses of the experts in Exp4-IX after `n` rounds are the sums of the estimated losses
`adv (O t) m ⬝ᵥ Ŷ t` of the rounds `t < n`, with `Ŷ t` the implicit-exploration estimates of the
losses `1 - Y t`. -/
lemma exp4IXSum_history (n : ℕ) (ω : Ω) :
    exp4IXSum adv η γ n (history O A Y n ω) = ∑ t ∈ range n, fun m ↦ (adv (O t ω) m : α → ℝ) ⬝ᵥ
      iwEstimator (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
        (1 - Y t ω) := by
  induction n with
  | zero => simp
  | succ n ih => simp [exp4IXSum_succ, Finset.sum_range_succ, ih, history_apply]

/-- **Exp4-IX as exponential weights.** Along a sequence of observations `O`, actions `A` and
feedbacks `Y`, the weights of Exp4-IX on the experts at round `n` are the exponential weights of
`-η n` times the cumulative estimated losses `adv (O t) m ⬝ᵥ Ŷ t` of the experts, with `Ŷ t` the
implicit-exploration estimates of the losses `1 - Y t`. -/
lemma exp4IXExpertWeights_history_eq (n : ℕ) (ω : Ω) :
    exp4IXExpertWeights adv η γ n (history O A Y n ω) = softmax (-(η n • ∑ t ∈ range n, fun m ↦
      (adv (O t ω) m : α → ℝ) ⬝ᵥ iwEstimator
        (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
          (1 - Y t ω))) := by
  rw [exp4IXExpertWeights_def, exp4IXSum_history]

end History

omit [Fintype β] in
/-- The estimate `e m ⬝ᵥ X̂` of the reward of an expert `m` whose advice `e m` sums to `1`, from the
loss-based importance-weighted estimates `X̂` of the rewards of the arms. -/
lemma dotProduct_lossIwEstimator_advice (e : β → simplex α) (m : β) (p : α → ℝ) (b : α)
    (y : ℝ) :
    (e m : α → ℝ) ⬝ᵥ lossIwEstimator p b y = 1 - (e m : α → ℝ) b * (1 - y) / p b :=
  dotProduct_lossIwEstimator (mem_simplex_iff.1 (e m).2).2

namespace Exp4IX

/-- A run of Exp4-IX is a run of the weight-based algorithm with the weights of Exp4-IX. -/
lemma isAlgEnvSeq_weightAlgorithm [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace 𝓞] [Nonempty β] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {env : Environment 𝓞 α ℝ}
    {hadv : Measurable adv} (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P) :
    IsAlgEnvSeq O A Y (weightAlgorithm (fun n x ↦ exp4IXWeights adv η γ n x.1 x.2)
      (fun n a ↦ (measurable_pi_apply a).comp (measurable_exp4IXWeights hadv η γ n))
      (fun n x ↦ exp4IXWeights_mem_simplex n x.1 x.2)) env P :=
  exp4IX_def adv hadv η γ ▸ h

section Pathwise

variable {Ω : Type*} (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ) (ω : Ω) {n : ℕ}

/-- The `Q`-average of the estimated losses `adv o m ⬝ᵥ v` of the experts, for the weights
`Q = exp4IXExpertWeights adv η γ n h` on the experts, is the `P`-average of the estimates `v` of
the losses of the arms, for the weights `P = exp4IXWeights adv η γ n h o` on the arms. -/
lemma sum_exp4IXExpertWeights_mul_dotProduct (n : ℕ) (h : Hist 𝓞 α ℝ n) (o : 𝓞) (v : α → ℝ) :
    ∑ m, exp4IXExpertWeights adv η γ n h m * (adv o m : α → ℝ) ⬝ᵥ v =
      ∑ a, exp4IXWeights adv η γ n h o a * v a := by
  simp_rw [← smul_eq_mul, ← smul_dotProduct, ← sum_dotProduct, ← exp4IXWeights_def, dotProduct,
    smul_eq_mul]

/-- The `Q`-average of the squared estimated losses `adv o m ⬝ᵥ v` of the experts, for the weights
`Q = exp4IXExpertWeights adv η γ n h` on the experts, is at most the `P`-average of the squared
estimates `v` of the losses of the arms, for the weights `P = exp4IXWeights adv η γ n h o`. -/
lemma sum_exp4IXExpertWeights_mul_dotProduct_sq_le (n : ℕ) (h : Hist 𝓞 α ℝ n) (o : 𝓞)
    (v : α → ℝ) :
    ∑ m, exp4IXExpertWeights adv η γ n h m * ((adv o m : α → ℝ) ⬝ᵥ v) ^ 2 ≤
      ∑ a, exp4IXWeights adv η γ n h o a * v a ^ 2 := by
  calc ∑ m, exp4IXExpertWeights adv η γ n h m * ((adv o m : α → ℝ) ⬝ᵥ v) ^ 2
  _ ≤ ∑ m, exp4IXExpertWeights adv η γ n h m * (adv o m : α → ℝ) ⬝ᵥ (v ^ 2) :=
      Finset.sum_le_sum fun m _ ↦ mul_le_mul_of_nonneg_left
        (sq_dotProduct_le_dotProduct_sq_of_mem_simplex (adv o m).2 v) (softmax_nonneg _ m)
  _ = ∑ a, exp4IXWeights adv η γ n h o a * v a ^ 2 := by
      simp only [sum_exp4IXExpertWeights_mul_dotProduct, Pi.pow_apply]

/-- The `Q`-average of the estimated rewards `adv o m ⬝ᵥ X̂` of the experts, with `Q` the weights
of Exp4-IX on the experts and `X̂` the loss-based importance-weighted estimates of the weights `P`
of Exp4-IX on the arms for the observation `o`, is the observed reward `y` of an arm `b` with
`P b ≠ 0`, since it is the `P`-average of `X̂`. -/
lemma sum_exp4IXExpertWeights_mul_dotProduct_lossIwEstimator [Nonempty β] (n : ℕ)
    (h : Hist 𝓞 α ℝ n) (o : 𝓞) {b : α} (y : ℝ) (hb : exp4IXWeights adv η γ n h o b ≠ 0) :
    ∑ m, exp4IXExpertWeights adv η γ n h m *
      (adv o m : α → ℝ) ⬝ᵥ lossIwEstimator (exp4IXWeights adv η γ n h o) b y = y := by
  rw [sum_exp4IXExpertWeights_mul_dotProduct]
  exact sum_mul_lossIwEstimator (mem_simplex_iff.1 (exp4IXWeights_mem_simplex _ _ _)).2 hb

/-- **The second-order term of the estimated rewards in Exp4-IX.** Along every sequence of
observations `O`, actions `A` and feedbacks `Y`, with `Q t` and `P t` the weights of Exp4-IX on
the experts and on the arms at round `t` and `X̂ᴱ t m = adv (O t) m ⬝ᵥ X̂ t` the estimated reward of
expert `m`, for the loss-based importance-weighted estimates `X̂ t` of the weights `P t`,
`∑ m', Q t m' * (1 - X̂ᴱ t m') ^ 2 ≤ (1 - Y t) ^ 2 / P t (A t)`. -/
lemma sum_mul_one_sub_sq_le (t : ℕ) :
    ∑ m', exp4IXExpertWeights adv η γ t (history O A Y t ω) m' *
        (1 - (adv (O t ω) m' : α → ℝ) ⬝ᵥ lossIwEstimator
          (exp4IXWeights adv η γ t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω)) ^ 2 ≤
      (1 - Y t ω) ^ 2 / exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) (A t ω) := by
  -- `1 - X̂ᴱ t m'` is the estimated loss of expert `m'` for the estimates of the losses `1 - Y t`
  calc ∑ m', exp4IXExpertWeights adv η γ t (history O A Y t ω) m' *
        (1 - (adv (O t ω) m' : α → ℝ) ⬝ᵥ lossIwEstimator
          (exp4IXWeights adv η γ t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω)) ^ 2
  _ = ∑ m', exp4IXExpertWeights adv η γ t (history O A Y t ω) m' *
        ((adv (O t ω) m' : α → ℝ) ⬝ᵥ iwEstimator
          (exp4IXWeights adv η γ t (history O A Y t ω) (O t ω)) (A t ω) (1 - Y t ω)) ^ 2 := by
      simp only [dotProduct_lossIwEstimator_advice, sub_sub_cancel, dotProduct_iwEstimator]
  _ ≤ ∑ a, exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a * iwEstimator
          (exp4IXWeights adv η γ t (history O A Y t ω) (O t ω)) (A t ω) (1 - Y t ω) a ^ 2 :=
      sum_exp4IXExpertWeights_mul_dotProduct_sq_le _ _ _ _
  _ = _ := sum_mul_iwEstimator_sq

/-- **Pathwise regret of the weights of Exp4-IX on the experts** [LS, Lemma 18.2] for a constant
rate; [Ora, Section 7.5; BCB12, proof of Theorem 3.1] for nonincreasing rates. Along every
sequence of observations `O`, actions `A` and feedbacks `Y ≤ 1` of the rounds `t < n`, with `Q t`
the weights of Exp4-IX on the experts at round `t` and `L t m = adv (O t) m ⬝ᵥ Ŷ t` the estimated
loss of expert `m`, for nonincreasing learning rates `η t > 0`, `γ ≥ 0` and every expert `m`,
`∑ t < n, (∑ m', Q t m' * L t m' - L t m) ≤
  log M / η (n - 1) + ∑ t < n, η t / 2 * ∑ m', Q t m' * L t m' ^ 2`,
with `M` the number of experts. -/
theorem sum_sum_mul_sub_le (hη : ∀ t, 0 < η t) (hη_anti : Antitone η) (hγ : ∀ t, 0 ≤ γ t)
    (hY : ∀ t < n, Y t ω ≤ 1) (m : β) :
    ∑ t ∈ range n, (∑ m', exp4IXExpertWeights adv η γ t (history O A Y t ω) m' *
        (adv (O t ω) m' : α → ℝ) ⬝ᵥ iwEstimator
          (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
            (1 - Y t ω) -
      (adv (O t ω) m : α → ℝ) ⬝ᵥ iwEstimator
          (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
            (1 - Y t ω)) ≤
      log (Fintype.card β) / η (n - 1) + ∑ t ∈ range n, η t / 2 *
        ∑ m', exp4IXExpertWeights adv η γ t (history O A Y t ω) m' *
          ((adv (O t ω) m' : α → ℝ) ⬝ᵥ iwEstimator
            (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
              (1 - Y t ω)) ^ 2 := by
  classical
  -- the estimated losses of the experts are nonnegative
  set y : ℕ → β → ℝ := fun t m' ↦ (adv (O t ω) m' : α → ℝ) ⬝ᵥ iwEstimator
    (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω) (1 - Y t ω)
    with hy
  have hy0 : ∀ t < n, ∀ m', 0 ≤ y t m' := fun t ht m' ↦ Finset.sum_nonneg fun a _ ↦
    mul_nonneg ((mem_simplex_iff.1 (adv (O t ω) m').2).1 a) (iwEstimator_nonneg
      (add_nonneg (exp4IXWeights_nonneg _ _ _ _) (hγ t)) (sub_nonneg.2 (hY t ht)))
  have := nonempty_of_mem_simplex (adv (O 0 ω) m).2
  -- the weights on the experts are the exponential weights of these losses
  have hqw : ∀ t, softmax (-(η t • ∑ s ∈ range t, y s)) =
      exp4IXExpertWeights adv η γ t (history O A Y t ω) := fun t ↦
    (exp4IXExpertWeights_history_eq O A Y t ω).symm
  have key := softmax_regret_le_of_antitone hη hη_anti hy0 (single_mem_simplex m)
  simpa only [hqw, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', mem_univ,
    ite_true] using key

/-- **Pathwise local-norm bound of Exp4-IX on the arms.** Along every sequence of observations `O`,
actions `A` and feedbacks `Y ≤ 1` of the rounds `t < n`, with `P t` the weights of Exp4-IX on the
arms at round `t` and `Ŷ t` its implicit-exploration estimates of the losses `1 - Y t`, for
nonincreasing learning rates `η t > 0`, `γ ≥ 0` and every expert `m`,
`∑ t < n, (⟨P t, Ŷ t⟩ - adv (O t) m ⬝ᵥ Ŷ t) ≤
  log M / η (n - 1) + ∑ t < n, η t / 2 * ⟨P t, Ŷ t ^ 2⟩`,
with `M` the number of experts and `⟨p, v⟩ = ∑ a, p a * v a`. -/
theorem sum_sum_mul_sub_dotProduct_le (hη : ∀ t, 0 < η t) (hη_anti : Antitone η)
    (hγ : ∀ t, 0 ≤ γ t) (hY : ∀ t < n, Y t ω ≤ 1) (m : β) :
    ∑ t ∈ range n, (∑ a, exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a *
        iwEstimator (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
          (1 - Y t ω) a -
      (adv (O t ω) m : α → ℝ) ⬝ᵥ iwEstimator
          (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
            (1 - Y t ω)) ≤
      log (Fintype.card β) / η (n - 1) + ∑ t ∈ range n, η t / 2 *
        ∑ a, exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a *
          iwEstimator (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t)
            (A t ω) (1 - Y t ω) a ^ 2 := by
  have key := sum_sum_mul_sub_le (adv := adv) O A Y ω hη hη_anti hγ hY m
  simp only [sum_exp4IXExpertWeights_mul_dotProduct] at key
  refine key.trans (add_le_add le_rfl (Finset.sum_le_sum fun t _ ↦
    mul_le_mul_of_nonneg_left ?_ (half_pos (hη t)).le))
  exact sum_exp4IXExpertWeights_mul_dotProduct_sq_le _ _ _ _

/-- **Pathwise bound on the estimated regret of Exp4-IX** [LS, Lemmas 12.4 and 18.2;
Neu15, proof of Theorem 2; Ora, Section 7.5]. Along every sequence of observations `O`,
actions `A` and feedbacks `Y t ∈ [0, 1]` of the rounds `t < n` with `P t (A t) + γ t ≠ 0`, with
`P t` the weights of Exp4-IX on the arms at round `t` and `Ŷ t` its implicit-exploration
estimates of the losses `1 - Y t`, for nonincreasing learning rates `η t > 0`,
`γ ≥ 0` and every expert `m`,
`∑ t < n, ((1 - Y t) - adv (O t) m ⬝ᵥ Ŷ t) ≤
  log M / η (n - 1) + ∑ t < n, (γ t + η t / 2) * ∑ a, Ŷ t a`,
with `M` the number of experts. -/
theorem sum_one_sub_sub_dotProduct_le (hη : ∀ t, 0 < η t) (hη_anti : Antitone η)
    (hγ : ∀ t, 0 ≤ γ t) (hY : ∀ t < n, Y t ω ∈ Set.Icc 0 1)
    (hpos : ∀ t < n,
      exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) (A t ω) + γ t ≠ 0) (m : β) :
    ∑ t ∈ range n, ((1 - Y t ω) - (adv (O t ω) m : α → ℝ) ⬝ᵥ iwEstimator
          (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
            (1 - Y t ω)) ≤
      log (Fintype.card β) / η (n - 1) + ∑ t ∈ range n, (γ t + η t / 2) *
        ∑ a, iwEstimator (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t)
          (A t ω) (1 - Y t ω) a := by
  set P : ℕ → α → ℝ := fun t ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) with hP
  set y : ℕ → α → ℝ := fun t ↦ iwEstimator (fun a ↦ P t a + γ t) (A t ω) (1 - Y t ω) with hy
  have hz : ∀ t < n, 1 - Y t ω ∈ Set.Icc 0 1 := fun t ht ↦
    ⟨sub_nonneg.2 (hY t ht).2, sub_le_self _ (hY t ht).1⟩
  have key := sum_sum_mul_sub_dotProduct_le (adv := adv) O A Y ω hη hη_anti hγ
    (fun t ht ↦ (hY t ht).2) m
  -- the bias of the estimates: `1 - Y t = ⟨P t, Ŷ t⟩ + γ t * ∑ a, Ŷ t a`
  have hbias : ∀ t ∈ range n, 1 - Y t ω = ∑ a, P t a * y t a + γ t * ∑ a, y t a := fun t ht ↦ by
    rw [← sub_sum_mul_iwEstimator_add (hpos t (mem_range.1 ht))]
    ring
  -- the second-order terms are at most the sums of the estimates
  have h2 : ∀ t ∈ range n, ∑ a, P t a * y t a ^ 2 ≤ ∑ a, y t a := fun t ht ↦
    sum_mul_iwEstimator_add_sq_le (exp4IXWeights_nonneg _ _ _ _) (hγ t)
      ((add_nonneg (exp4IXWeights_nonneg _ _ _ _) (hγ t)).lt_of_ne'
        (hpos t (mem_range.1 ht))) (hz t (mem_range.1 ht))
  calc ∑ t ∈ range n, ((1 - Y t ω) - (adv (O t ω) m : α → ℝ) ⬝ᵥ y t)
  _ = ∑ t ∈ range n, (∑ a, P t a * y t a - (adv (O t ω) m : α → ℝ) ⬝ᵥ y t) +
      ∑ t ∈ range n, γ t * ∑ a, y t a := by
      rw [← sum_add_distrib]
      exact Finset.sum_congr rfl fun t ht ↦ by rw [hbias t ht]; ring
  _ ≤ log (Fintype.card β) / η (n - 1) + ∑ t ∈ range n, η t / 2 * ∑ a, P t a * y t a ^ 2 +
      ∑ t ∈ range n, γ t * ∑ a, y t a := add_le_add key le_rfl
  _ ≤ log (Fintype.card β) / η (n - 1) + ∑ t ∈ range n, η t / 2 * ∑ a, y t a +
      ∑ t ∈ range n, γ t * ∑ a, y t a :=
      add_le_add (add_le_add le_rfl (Finset.sum_le_sum fun t ht ↦
        mul_le_mul_of_nonneg_left (h2 t ht) (half_pos (hη t)).le)) le_rfl
  _ = _ := by
      rw [add_assoc, ← sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun t _ ↦ by ring

end Pathwise

end Exp4IX

end LMLExplore.Bandits
