/-
Copyright (c) 2026 Adrien Prévost. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Prévost
-/
module

public import LMLExplore.Bandits.Adversarial.Regret
public import LMLExplore.Bandits.ImportanceWeighted
public import LMLExplore.Bandits.WeightAlgorithm
public import LMLExplore.OnlineLearning.Tsallis

/-!
# Mirror descent with the ½-Tsallis potential for adversarial bandits

Online mirror descent on the probability simplex of a finite set of arms `α`, with the ½-Tsallis
potential `ψ p = -2 ∑ a, √(p a)` and a constant learning rate `η > 0`, run on the
importance-weighted estimates of the losses, is the bandit algorithm of [Ora, Section 9.1.2]. It
starts from the uniform weights `P 0`, draws the arm `A t` of round `t` from the weights `P t`,
observes its reward `Y t`, and plays at round `t + 1` the mirror descent step
`P (t + 1) = argmin_{p ∈ simplex α} (η ⟨G t, p⟩ + D_ψ(p, P t))` for the estimates
`G t a = 𝟙{A t = a} (1 - Y t) / P t a` of the losses `1 - Y t`, with `D_ψ` the Bregman divergence
of `ψ`. This is mirror descent with the potential `-∑ a, √(p a)` and the learning rate `η / 2`,
whose steps are `OnlineLearning.tsallisMDStep (2 / η)`. With a constant learning rate, mirror
descent coincides with follow the regularized leader: the weights of round `t` are the Tsallis
weights `tsallisWeights (2 / η) (∑ s < t, G s)`, those of Tsallis-INF
(`LMLExplore.Bandits.tsallisINF`) with the constant coefficient `2 / η` in place of `4 √(t + 1)`.

Against any environment with feedback in `[0, 1]`, an adaptive adversary included, the
pseudo-regret after `n` rounds is at most `2 (√k - 1) / η + η √k n`, with `k` the number of arms
[Ora, Theorem 9.2]. The proof applies the local-norm bound of mirror descent with the ½-Tsallis
potential (`OnlineLearning.tsallisMirrorDescent_regret_le`) to the nonnegative estimates `G t`.
Given the past, the expected local norm `∑ a, P t a √(P t a) G t a ^ 2` of round `t` is at most
`∑ a, √(P t a) ≤ √k`, and the estimates are conditionally unbiased. For `η = √(2 / n)` the bound
is `2 √(2 k n)`.

## Main definitions

* `LMLExplore.Bandits.tsallisMDWeights η n h`: the weights `P n` of round `n`, computed from the
  history `h` of the first `n` rounds.
* `LMLExplore.Bandits.tsallisMD η hη`: the algorithm, for `η ≠ 0`.

## Main statements

* `isMirrorDescentStep_tsallisMDWeights`: the weights of round `n + 1` are the mirror descent step
  from the weights of round `n` for the importance-weighted estimate of the loss of round `n`.
* `tsallisMDWeights_history_eq`: along every sequence of actions and feedbacks, the weights of
  round `n` are the Tsallis weights with coefficient `2 / η` of the cumulative importance-weighted
  estimates of the losses of the rounds `t < n`.
* `TsallisMD.pseudoRegret_le`: the pseudo-regret against an adaptive adversary is at most
  `2 (√k - 1) / η + η √k n` [Ora, Theorem 9.2].
* `TsallisMD.pseudoRegret_le_two_mul_sqrt`: for `η = √(2 / n)`, it is at most `2 √(2 k n)`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real

namespace LMLExplore.Bandits

variable {α 𝓞 : Type*} [Fintype α] [DecidableEq α] {η : ℝ}

section Weights

/-- The weights of mirror descent with the ½-Tsallis potential `-2 ∑ a, √(p a)` and the learning
rate `η`, after the history `h` of the first `n` rounds: uniform at round `0`, and at round
`n + 1` the mirror descent step `OnlineLearning.tsallisMDStep (2 / η)` from the weights `P n` of
round `n`, for the importance-weighted estimate `iwEstimator (P n) (A n) (1 - X n)` of the losses
`1 - X n`, computed from the action `A n` and the reward `X n` of round `n` of `h`. -/
noncomputable def tsallisMDWeights (η : ℝ) : (n : ℕ) → Hist 𝓞 α ℝ n → α → ℝ
  | 0, _ => fun _ ↦ (Fintype.card α : ℝ)⁻¹
  | n + 1, h => OnlineLearning.tsallisMDStep (2 / η) (tsallisMDWeights η n (Fin.init h))
      (iwEstimator (tsallisMDWeights η n (Fin.init h)) (h (Fin.last n)).action
        (1 - (h (Fin.last n)).feedback))

@[simp]
lemma tsallisMDWeights_zero (h : Hist 𝓞 α ℝ 0) :
    tsallisMDWeights η 0 h = fun _ ↦ (Fintype.card α : ℝ)⁻¹ := by
  rw [tsallisMDWeights]

lemma tsallisMDWeights_succ (n : ℕ) (h : Hist 𝓞 α ℝ (n + 1)) :
    tsallisMDWeights η (n + 1) h =
      OnlineLearning.tsallisMDStep (2 / η) (tsallisMDWeights η n (Fin.init h))
        (iwEstimator (tsallisMDWeights η n (Fin.init h)) (h (Fin.last n)).action
          (1 - (h (Fin.last n)).feedback)) := by
  rw [tsallisMDWeights]

variable [Nonempty α]

lemma tsallisMDWeights_pos (hη : η ≠ 0) (n : ℕ) (h : Hist 𝓞 α ℝ n) (a : α) :
    0 < tsallisMDWeights η n h a := by
  rcases n with _ | n
  · rw [tsallisMDWeights_zero]
    exact inv_pos.2 (by exact_mod_cast Fintype.card_pos)
  · rw [tsallisMDWeights_succ]
    exact OnlineLearning.tsallisMDStep_pos (by positivity) _ _ a

lemma tsallisMDWeights_mem_simplex (hη : η ≠ 0) (n : ℕ) (h : Hist 𝓞 α ℝ n) :
    tsallisMDWeights η n h ∈ simplex α := by
  rcases n with _ | n
  · rw [tsallisMDWeights_zero]
    exact uniform_mem_simplex α
  · rw [tsallisMDWeights_succ]
    exact OnlineLearning.tsallisMDStep_mem_simplex (by positivity) _ _

/-- **The weights are mirror descent steps** [Ora, Section 9.1.2]. For `η > 0`, the weights of
round `n + 1` are the mirror descent step on the simplex from the weights `P n` of round `n`,
with the ½-Tsallis potential `-∑ a, √(p a)`, the learning rate `η / 2` and the loss
`G n = iwEstimator (P n) (A n) (1 - X n)`, the importance-weighted estimate of the losses of round
`n`. -/
theorem isMirrorDescentStep_tsallisMDWeights (hη : 0 < η) (n : ℕ) (h : Hist 𝓞 α ℝ (n + 1)) :
    OnlineLearning.IsMirrorDescentStep (simplex α) (fun q ↦ -∑ a, √(q a)) (η / 2)
      (∑ a, iwEstimator (tsallisMDWeights η n (Fin.init h)) (h (Fin.last n)).action
          (1 - (h (Fin.last n)).feedback) a • ContinuousLinearMap.proj a)
      (tsallisMDWeights η n (Fin.init h)) (tsallisDeriv (tsallisMDWeights η n (Fin.init h)))
      (tsallisMDWeights η (n + 1) h) := by
  have h_rate : η / 2 = (2 / η)⁻¹ := by rw [inv_div]
  rw [h_rate, OnlineLearning.isMirrorDescentStep_iff_eq_tsallisMDStep (by positivity),
    tsallisMDWeights_succ]

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞]

@[fun_prop]
lemma measurable_tsallisMDWeights (hη : η ≠ 0) (n : ℕ) :
    Measurable (tsallisMDWeights (𝓞 := 𝓞) (α := α) η n) := by
  induction n with
  | zero =>
    rw [funext tsallisMDWeights_zero]
    exact measurable_const
  | succ n ih =>
    have hW := ih.comp (measurable_finInit (β := fun _ ↦ _))
    have hS := OnlineLearning.measurable_tsallisMDStep (α := α) (c := 2 / η) (by positivity)
    have hlast : Measurable fun h : Hist 𝓞 α ℝ (n + 1) ↦ h (Fin.last n) := measurable_pi_apply _
    rw [funext (tsallisMDWeights_succ n)]
    exact hS.comp (hW.prodMk (measurable_iwEstimator.comp (hW.prodMk
      ((Round.measurable_action.comp hlast).prodMk
        (measurable_const.sub (Round.measurable_feedback.comp hlast))))))

end Weights

section Algorithm

variable [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞]

/-- **Mirror descent with the ½-Tsallis potential** for adversarial bandits [Ora, Section 9.1.2]:
the weight-based algorithm that draws its action of round `n` from the weights
`tsallisMDWeights η n h` of the history `h`, the iterates of mirror descent with the potential
`-2 ∑ a, √(p a)` and the learning rate `η` on the importance-weighted loss estimates, from the
uniform weights. It ignores the observations. -/
noncomputable def tsallisMD (η : ℝ) (hη : η ≠ 0) : Algorithm 𝓞 α ℝ :=
  weightAlgorithm (fun n x ↦ tsallisMDWeights η n x.1)
    (fun n a ↦ (measurable_pi_apply a).comp ((measurable_tsallisMDWeights hη n).comp
      measurable_fst))
    (fun n x ↦ tsallisMDWeights_mem_simplex hη n x.1)

lemma tsallisMD_def (hη : η ≠ 0) :
    tsallisMD (𝓞 := 𝓞) (α := α) η hη = weightAlgorithm (fun n x ↦ tsallisMDWeights η n x.1)
      (fun n a ↦ (measurable_pi_apply a).comp ((measurable_tsallisMDWeights hη n).comp
        measurable_fst))
      (fun n x ↦ tsallisMDWeights_mem_simplex hη n x.1) := (rfl)

/-- The policy of `tsallisMD η hη` at round `n` draws its action from the weights
`tsallisMDWeights η n h` of the history `h`. -/
@[simp]
lemma tsallisMD_policy_apply (hη : η ≠ 0) (n : ℕ) (x : Hist 𝓞 α ℝ n × 𝓞) :
    (tsallisMD (𝓞 := 𝓞) (α := α) η hη).policy n x =
      weightedMeasure (tsallisMDWeights η n x.1) := by
  rw [tsallisMD_def, weightAlgorithm_policy, weightKernel_apply]

/-- A run of `tsallisMD η hη` is a run of the weight-based algorithm with the weights
`tsallisMDWeights η`, so the run lemmas of weight-based algorithms (`WeightAlgorithm`) apply to
it. -/
lemma isAlgEnvSeq_tsallisMD_iff (hη : η ≠ 0) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}
    {env : Environment 𝓞 α ℝ} :
    IsAlgEnvSeq O A Y (tsallisMD η hη) env P ↔
      IsAlgEnvSeq O A Y (weightAlgorithm (fun n x ↦ tsallisMDWeights η n x.1)
        (fun n a ↦ (measurable_pi_apply a).comp ((measurable_tsallisMDWeights hη n).comp
          measurable_fst))
        (fun n x ↦ tsallisMDWeights_mem_simplex hη n x.1)) env P := by
  rw [tsallisMD_def]

end Algorithm

section History

variable {Ω : Type*} (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ)

/-- Along a sequence of observations `O`, actions `A` and feedbacks `Y`, the weights of round
`n + 1` are the mirror descent step `OnlineLearning.tsallisMDStep (2 / η)` from the weights `P n`
of round `n` for the importance-weighted estimate of the loss `1 - Y n` of round `n`. -/
lemma tsallisMDWeights_history_succ (n : ℕ) (ω : Ω) :
    tsallisMDWeights η (n + 1) (history O A Y (n + 1) ω) =
      OnlineLearning.tsallisMDStep (2 / η) (tsallisMDWeights η n (history O A Y n ω))
        (iwEstimator (tsallisMDWeights η n (history O A Y n ω)) (A n ω) (1 - Y n ω)) := by
  simp [tsallisMDWeights_succ, history_apply]

/-- **Mirror descent with a constant learning rate is follow the regularized leader.** For `η > 0`,
along a sequence of observations `O`, actions `A` and feedbacks `Y`, the weights of round `n` are
the Tsallis weights with coefficient `2 / η` of the cumulative importance-weighted estimates of the
losses `1 - Y t` of the rounds `t < n`. -/
lemma tsallisMDWeights_history_eq [Nonempty α] (hη : 0 < η) (n : ℕ) (ω : Ω) :
    tsallisMDWeights η n (history O A Y n ω) = tsallisWeights (2 / η) (∑ t ∈ range n,
      iwEstimator (tsallisMDWeights η t (history O A Y t ω)) (A t ω) (1 - Y t ω)) :=
  OnlineLearning.eq_tsallisWeights_of_eq_tsallisMDStep (c := 2 / η) (n := n)
    (p := fun t ↦ tsallisMDWeights η t (history O A Y t ω))
    (ℓ := fun t ↦ iwEstimator (tsallisMDWeights η t (history O A Y t ω)) (A t ω) (1 - Y t ω))
    (by positivity) (tsallisMDWeights_zero _)
    (fun t _ ↦ tsallisMDWeights_history_succ O A Y t ω) n le_rfl

end History

namespace TsallisMD

variable {Ω : Type*} [Nonempty α] {n t : ℕ}

section Path

/-- **Pathwise regret on the estimated losses** [Ora, Theorem 9.2]. For `η > 0`, along every
sequence of observations `O`, actions `A` and feedbacks `Y` with `Y t ω ≤ 1` for `t < n`, with
`P t` the weights of `tsallisMD η _` and `G t = iwEstimator (P t) (A t) (1 - Y t)` the
importance-weighted estimates of the losses `1 - Y t`, the estimated regret against every arm `a`
satisfies
`∑ t < n, ((1 - Y t) - G t a) ≤ 2 (√k - 1) / η + η ∑ t < n, ∑ b, P t b √(P t b) G t b ^ 2`,
with `k` the number of arms. -/
theorem sum_one_sub_sub_iwEstimator_le (hη : 0 < η) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → ℝ) (ω : Ω) (hY : ∀ t < n, Y t ω ≤ 1) (a : α) :
    ∑ t ∈ range n, ((1 - Y t ω) -
        iwEstimator (tsallisMDWeights η t (history O A Y t ω)) (A t ω) (1 - Y t ω) a) ≤
      2 * (√(Fintype.card α) - 1) / η + η * ∑ t ∈ range n,
        ∑ b, tsallisMDWeights η t (history O A Y t ω) b *
          √(tsallisMDWeights η t (history O A Y t ω) b) *
          iwEstimator (tsallisMDWeights η t (history O A Y t ω)) (A t ω) (1 - Y t ω) b ^ 2 := by
  have h := OnlineLearning.tsallisMirrorDescent_regret_le (c := 2 / η) (by positivity)
    (ℓ := fun t ↦ iwEstimator (tsallisMDWeights η t (history O A Y t ω)) (A t ω) (1 - Y t ω))
    (p := fun t ↦ tsallisMDWeights η t (history O A Y t ω)) (n := n)
    (fun t ht b ↦ iwEstimator_nonneg (tsallisMDWeights_pos hη.ne' _ _ _).le
      (sub_nonneg.2 (hY t ht)))
    (tsallisMDWeights_zero _) (fun t _ ↦ tsallisMDWeights_history_succ O A Y t ω)
    (single_mem_simplex a)
  have hu : ∑ b, √((Pi.single a 1 : α → ℝ) b) = 1 := by
    simp [Pi.single_apply, apply_ite]
  refine (le_of_eq ?_).trans (h.trans_eq ?_)
  · -- the loss of the weights is the observed loss
    refine sum_congr rfl fun t _ ↦ ?_
    rw [sum_mul_iwEstimator (tsallisMDWeights_pos hη.ne' _ _ _).ne']
    simp [Pi.single_apply]
  · rw [hu, mul_sum]
    congr 1
    · field_simp
    · exact sum_congr rfl fun t _ ↦ by field_simp

end Path

section Expectation

omit [Nonempty α] in
/-- For weights `p ≥ 0` and a loss `y ∈ [0, 1]`, the local norm
`∑ b, p b √(p b) G b ^ 2` of the importance-weighted estimate `G = iwEstimator p a y` is at most
`√(p a) / p a`. -/
private lemma sum_mul_sqrt_mul_iwEstimator_sq_le {p : α → ℝ} (hp : ∀ b, 0 ≤ p b) {y : ℝ}
    (hy : y ∈ Set.Icc 0 1) (a : α) :
    ∑ b, p b * √(p b) * iwEstimator p a y b ^ 2 ≤ √(p a) / p a := by
  rw [sum_eq_single a (fun b _ hb ↦ by rw [iwEstimator_apply_of_ne hb]; ring) (by simp),
    iwEstimator_apply_self]
  rcases (hp a).eq_or_lt with ha | ha
  · simp [← ha]
  have hy2 : y ^ 2 ≤ 1 := pow_le_one₀ hy.1 hy.2
  calc p a * √(p a) * (y / p a) ^ 2 = √(p a) / p a * y ^ 2 := by field_simp
  _ ≤ √(p a) / p a * 1 := by gcongr
  _ = √(p a) / p a := mul_one _

omit [DecidableEq α] [Nonempty α] in
/-- For weights `p ≥ 0`, `∑ b, p b * (√(p b) / p b) = ∑ b, √(p b)`. -/
private lemma sum_mul_sqrt_div {p : α → ℝ} (hp : ∀ b, 0 ≤ p b) :
    ∑ b, p b * (√(p b) / p b) = ∑ b, √(p b) := by
  refine sum_congr rfl fun b _ ↦ ?_
  rcases (hp b).eq_or_lt with hb | hb
  · simp [← hb]
  · exact mul_div_cancel₀ _ hb.ne'

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝓞}
  {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {env : Environment 𝓞 α ℝ}

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace 𝓞] in
/-- The ratio `√(p b) / p b` is measurable in `(p, b)`. -/
private lemma measurable_sqrt_div [Countable α] :
    Measurable fun z : (α → ℝ) × α ↦ √(z.1 z.2) / z.1 z.2 := by
  have h : Measurable fun z : (α → ℝ) × α ↦ z.1 z.2 :=
    measurable_from_prod_countable_left fun b ↦ measurable_pi_apply b
  fun_prop

/-- Along a run of `tsallisMD η _`, the ratio `√(P t (A t)) / P t (A t)` of the weight of the
played arm is integrable, as its average over the drawn arm is `∑ b, √(P t b) ≤ √k`. -/
private lemma integrable_sqrt_div_weights (hη : 0 < η)
    (h : IsAlgEnvSeq O A Y (tsallisMD η hη.ne') env P) :
    Integrable (fun ω ↦ √(tsallisMDWeights η t (history O A Y t ω) (A t ω)) /
      tsallisMDWeights η t (history O A Y t ω) (A t ω)) P :=
  WeightAlgorithm.integrable_comp_weights ((isAlgEnvSeq_tsallisMD_iff hη.ne').1 h) t
    (g := fun p b ↦ √(p b) / p b) measurable_sqrt_div (C := √(Fintype.card α)) fun p hp ↦ by
      simp_rw [abs_of_nonneg (div_nonneg (sqrt_nonneg _) ((mem_simplex_iff.1 hp).1 _))]
      rw [sum_mul_sqrt_div (mem_simplex_iff.1 hp).1]
      exact sum_sqrt_le_sqrt_card hp

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞]
  [IsProbabilityMeasure P] in
/-- Along every sequence of observations `O`, actions `A` and feedbacks `Y` whose feedback at round
`t` is almost surely in `[0, 1]`, with `P t` the weights of `tsallisMD η _` and `G t` the
importance-weighted estimates of the losses `1 - Y t`, the local norm
`∑ b, P t b √(P t b) G t b ^ 2` is almost surely nonnegative and at most
`√(P t (A t)) / P t (A t)`. -/
private lemma ae_sum_mul_sqrt_mul_iwEstimator_sq_mem_Icc (hη : 0 < η)
    (hY : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1) :
    ∀ᵐ ω ∂P, ∑ b, tsallisMDWeights η t (history O A Y t ω) b *
      √(tsallisMDWeights η t (history O A Y t ω) b) *
      iwEstimator (tsallisMDWeights η t (history O A Y t ω)) (A t ω) (1 - Y t ω) b ^ 2 ∈
      Set.Icc 0 (√(tsallisMDWeights η t (history O A Y t ω) (A t ω)) /
        tsallisMDWeights η t (history O A Y t ω) (A t ω)) := by
  have hW_nn (ω : Ω) (b : α) : 0 ≤ tsallisMDWeights η t (history O A Y t ω) b :=
    (tsallisMDWeights_pos hη.ne' _ _ _).le
  filter_upwards [hY] with ω hω
  exact ⟨sum_nonneg fun b _ ↦ mul_nonneg (mul_nonneg (hW_nn ω b) (sqrt_nonneg _)) (sq_nonneg _),
    sum_mul_sqrt_mul_iwEstimator_sq_le (hW_nn ω) ⟨sub_nonneg.2 hω.2, by linarith [hω.1]⟩ _⟩

/-- Along a run of `tsallisMD η _` whose feedback at round `t` is almost surely in `[0, 1]`, with
`P t` the weights and `G t` the importance-weighted estimates of the losses `1 - Y t`, the local
norm `∑ b, P t b √(P t b) G t b ^ 2` of round `t` is integrable. -/
theorem integrable_sum_mul_sqrt_mul_iwEstimator_sq (hη : 0 < η)
    (h : IsAlgEnvSeq O A Y (tsallisMD η hη.ne') env P) (hY : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1) :
    Integrable (fun ω ↦ ∑ b, tsallisMDWeights η t (history O A Y t ω) b *
      √(tsallisMDWeights η t (history O A Y t ω) b) *
      iwEstimator (tsallisMDWeights η t (history O A Y t ω)) (A t ω) (1 - Y t ω) b ^ 2) P := by
  have h' := (isAlgEnvSeq_tsallisMD_iff hη.ne').1 h
  have hW : Measurable fun ω ↦ tsallisMDWeights η t (history O A Y t ω) :=
    WeightAlgorithm.measurable_weights_run h' t
  have hiw : Measurable fun ω ↦
      iwEstimator (tsallisMDWeights η t (history O A Y t ω)) (A t ω) (1 - Y t ω) :=
    WeightAlgorithm.measurable_iwEstimator_run h' (measurable_const.sub (h.measurable_feedback t))
  refine (integrable_sqrt_div_weights (t := t) hη h).mono' (by fun_prop) ?_
  filter_upwards [ae_sum_mul_sqrt_mul_iwEstimator_sq_mem_Icc (O := O) (A := A) hη hY] with ω hω
  rw [Real.norm_of_nonneg hω.1]
  exact hω.2

/-- **The expected local norm of a round.** Along a run of `tsallisMD η _` whose feedback at round
`t` is almost surely in `[0, 1]`, with `P t` the weights and `G t` the importance-weighted
estimates of the losses `1 - Y t`, the local norm `∑ b, P t b √(P t b) G t b ^ 2` of round `t` has
expectation at most `√k`, with `k` the number of arms. -/
theorem integral_sum_mul_sqrt_mul_iwEstimator_sq_le (hη : 0 < η)
    (h : IsAlgEnvSeq O A Y (tsallisMD η hη.ne') env P) (hY : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1) :
    P[fun ω ↦ ∑ b, tsallisMDWeights η t (history O A Y t ω) b *
      √(tsallisMDWeights η t (history O A Y t ω) b) *
      iwEstimator (tsallisMDWeights η t (history O A Y t ω)) (A t ω) (1 - Y t ω) b ^ 2] ≤
      √(Fintype.card α) := by
  have hW_nn (ω : Ω) (b : α) : 0 ≤ tsallisMDWeights η t (history O A Y t ω) b :=
    (tsallisMDWeights_pos hη.ne' _ _ _).le
  -- the local norm is dominated by `√(P t (A t)) / P t (A t)`
  refine (integral_mono_ae (integrable_sum_mul_sqrt_mul_iwEstimator_sq hη h hY)
    (integrable_sqrt_div_weights (t := t) hη h)
    ((ae_sum_mul_sqrt_mul_iwEstimator_sq_mem_Icc (O := O) (A := A) hη hY).mono
      fun _ hω ↦ hω.2)).trans ?_
  -- whose expectation is that of `∑ b, √(P t b) ≤ √k`
  rw [WeightAlgorithm.integral_comp_weights ((isAlgEnvSeq_tsallisMD_iff hη.ne').1 h) t
    (g := fun p b ↦ √(p b) / p b) measurable_sqrt_div (integrable_sqrt_div_weights (t := t) hη h)]
  refine (integral_mono_of_nonneg (ae_of_all _ fun ω ↦ ?_)
    (integrable_const (√(Fintype.card α))) (ae_of_all _ fun ω ↦ ?_)).trans (by simp)
  · exact sum_nonneg fun b _ ↦ mul_nonneg (hW_nn ω b) (div_nonneg (sqrt_nonneg _) (hW_nn ω b))
  · rw [sum_mul_sqrt_div (hW_nn ω)]
    exact sum_sqrt_le_sqrt_card (tsallisMDWeights_mem_simplex hη.ne' _ _)

/-- **Pseudo-regret of mirror descent with the ½-Tsallis potential against an adaptive
adversary** [Ora, Theorem 9.2]. For `η > 0`, along a run of `tsallisMD η _` against any
environment whose feedbacks of the rounds `t < n` are almost surely in `[0, 1]`, the pseudo-regret
after `n` rounds is at most `2 (√k - 1) / η + η √k n`, with `k` the number of arms. -/
theorem pseudoRegret_le (hη : 0 < η) (h : IsAlgEnvSeq O A Y (tsallisMD η hη.ne') env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) :
    pseudoRegret env O A Y P n ≤ 2 * (√(Fintype.card α) - 1) / η + η * √(Fintype.card α) * n := by
  refine pseudoRegret_le_iff.2 fun a ↦ ?_
  have h' := (isAlgEnvSeq_tsallisMD_iff hη.ne').1 h
  have hYt (t : ℕ) (ht : t < n) : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1 :=
    hY.mono fun _ hω ↦ hω t ht
  have hV (t : ℕ) (ht : t ∈ range n) :=
    integrable_sum_mul_sqrt_mul_iwEstimator_sq hη h (hYt t (mem_range.1 ht))
  -- the expected regret against `a` is the expected estimated regret
  rw [WeightAlgorithm.integral_sum_means_sub_eq_integral_sum_one_sub_sub_iwEstimator h' hYt
    fun t _ ↦ ae_of_all _ fun ω ↦ tsallisMDWeights_pos hη.ne' _ _ a]
  have hint (t : ℕ) (ht : t ∈ range n) :=
    ((integrable_const 1).sub (Integrable.of_mem_Icc 0 1 (h.measurable_feedback t).aemeasurable
      (hYt t (mem_range.1 ht)))).sub
      (WeightAlgorithm.integrable_iwEstimator_one_sub h' (hYt t (mem_range.1 ht)) a)
  calc P[fun ω ↦ ∑ t ∈ range n, ((1 - Y t ω) -
        iwEstimator (tsallisMDWeights η t (history O A Y t ω)) (A t ω) (1 - Y t ω) a)]
  -- take expectations in the pathwise bound
  _ ≤ P[fun ω ↦ 2 * (√(Fintype.card α) - 1) / η + η * ∑ t ∈ range n,
        ∑ b, tsallisMDWeights η t (history O A Y t ω) b *
          √(tsallisMDWeights η t (history O A Y t ω) b) *
          iwEstimator (tsallisMDWeights η t (history O A Y t ω)) (A t ω) (1 - Y t ω) b ^ 2] := by
      refine integral_mono_ae (integrable_finsetSum _ hint)
        ((integrable_const _).add ((integrable_finsetSum _ fun t ht ↦ (hV t ht)).const_mul _))
        ?_
      filter_upwards [hY] with ω hω using
        sum_one_sub_sub_iwEstimator_le hη O A Y ω (fun t ht ↦ (hω t ht).2) a
  _ = 2 * (√(Fintype.card α) - 1) / η + η * ∑ t ∈ range n,
        P[fun ω ↦ ∑ b, tsallisMDWeights η t (history O A Y t ω) b *
          √(tsallisMDWeights η t (history O A Y t ω) b) *
          iwEstimator (tsallisMDWeights η t (history O A Y t ω)) (A t ω) (1 - Y t ω) b ^ 2] := by
      rw [integral_add (integrable_const _)
          ((integrable_finsetSum _ fun t ht ↦ (hV t ht)).const_mul _),
        integral_const_mul, integral_finsetSum _ fun t ht ↦ (hV t ht), integral_const,
        probReal_univ, one_smul]
  -- the expected local norms are at most `√k`
  _ ≤ 2 * (√(Fintype.card α) - 1) / η + η * ∑ t ∈ range n, √(Fintype.card α) := by
      gcongr with t ht
      exact integral_sum_mul_sqrt_mul_iwEstimator_sq_le hη h (hYt t (mem_range.1 ht))
  _ = 2 * (√(Fintype.card α) - 1) / η + η * √(Fintype.card α) * n := by
      rw [sum_const, card_range, nsmul_eq_mul]
      ring

/-- **Pseudo-regret of mirror descent with the ½-Tsallis potential and the tuned learning rate**
[Ora, Theorem 9.2]. Along a run of `tsallisMD η _` with `η = √(2 / n)` against any environment
whose feedbacks of the rounds `t < n` are almost surely in `[0, 1]`, the pseudo-regret after `n`
rounds is at most `2 √(2 k n)`, with `k` the number of arms. -/
theorem pseudoRegret_le_two_mul_sqrt (hη : 0 < η) (hηn : η = √(2 / n))
    (h : IsAlgEnvSeq O A Y (tsallisMD η hη.ne') env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) :
    pseudoRegret env O A Y P n ≤ 2 * √(2 * Fintype.card α * n) := by
  have hn : (0 : ℝ) < n := by
    rcases (n.cast_nonneg : (0 : ℝ) ≤ n).eq_or_lt with hn | hn
    · rw [hηn, ← hn, div_zero, sqrt_zero] at hη
      exact absurd hη (lt_irrefl 0)
    · exact hn
  refine (pseudoRegret_le hη h hY).trans ?_
  have hsk := sqrt_nonneg (Fintype.card α : ℝ)
  -- `2 (√k - 1) / η + η √k n ≤ 2 √k / η + η √k n = 2 √(2 k n)` for `η = √(2 / n)`
  have h_eq : 2 * √(Fintype.card α) / η + η * √(Fintype.card α) * n =
      2 * √(2 * Fintype.card α * n) := by
    have h2n : √(2 / n) * √n = √2 := by
      rw [← sqrt_mul (by positivity), div_mul_cancel₀ _ hn.ne']
    have hsn : √n ^ 2 = n := sq_sqrt hn.le
    rw [hηn, sqrt_mul (by positivity), sqrt_mul (by positivity)]
    have : 0 < √(2 / n) := by positivity
    field_simp
    nlinarith [h2n, hsn, sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [← h_eq]
  gcongr
  linarith

end Expectation

end TsallisMD

end LMLExplore.Bandits
