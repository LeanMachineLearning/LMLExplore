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
# Exp4

In a bandit with expert advice [LS, Chapter 18], each expert `m` of a finite set `β` recommends at
round `t` a distribution `E t m ∈ simplex α` over the arms, and the learner sees this advice before
acting. Exp4 [ACFS02], [LS, Algorithm 11] runs exponential weights over the experts: it keeps
weights `Q t` on the experts, plays an arm drawn from the mixture `P t = ∑ m, Q t m • E t m` of
their advice, estimates the rewards of the arms by the loss-based importance-weighted estimates
`X̂ t` of `P t`, and credits each expert `m` with the estimate `X̂ᴱ t m = E t m ⬝ᵥ X̂ t` of its
expected reward, so that `Q t = softmax (η • ∑ s < t, X̂ᴱ s)`. In matrix form, `P t = Q t E t` and
`X̂ᴱ t = E t X̂ t`. The learning rate `η > 0` is a parameter; this is the algorithm of [LS] with
`γ = 0`.

Exp4 is defined as the instance of Exp4-IX (`LMLExplore.Bandits.exp4IX`) that observes the advice
directly (`adv = id`), with the constant learning rate `η` and no implicit exploration: the
estimated reward `X̂ᴱ s m` of expert `m` is one minus its estimated loss in Exp4-IX, so both
algorithms put the same weights on the experts.

The observation of round `t` is the advice `E t : β → simplex α`. For rewards in `[0, 1]` and a
fixed advice sequence `E`, the regret against the best expert satisfies
`R_n ≤ log M / η + η n k / 2`, with `k` the number of arms and `M` the number of experts, and the
learning rate `η = √(2 log M / (n k))` gives `R_n ≤ √(2 n k log M)` [LS, Theorem 18.1].

## Main definitions

* `LMLExplore.Bandits.exp4 η`: the Exp4 algorithm with learning rate `η`, the instance of Exp4-IX
  with the advice observed directly, the constant learning rate `η` and `γ = 0`.

## Main statements

* `exp4_eq_of_subsingleton`: with a single expert, Exp4 does not depend on its learning rate.
* `Exp4.sum_sub_sum_le`: [LS, Lemma 18.2], the pathwise bound
  `∑ t < n, (X̂ᴱ t m - ⟨Q t, X̂ᴱ t⟩) ≤ log M / η + η / 2 * ∑ t < n, ⟨Q t, (1 - X̂ᴱ t) ^ 2⟩`.
* `Exp4IX.sum_exp4IXExpertWeights_mul_dotProduct_lossIwEstimator`: for every instance of
  Exp4-IX, the `Q t`-average of the estimated rewards `X̂ᴱ t` of the experts is the observed reward
  `Y t`.
* `Exp4IX.sum_mul_one_sub_sq_le`: for every instance of Exp4-IX, the second-order term satisfies
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

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]

omit [Fintype β] in
/-- The estimate `e m ⬝ᵥ X̂` of the reward of an expert `m` whose advice `e m` sums to `1`, from the
loss-based importance-weighted estimates `X̂` of the rewards of the arms. -/
private lemma dotProduct_lossIwEstimator_advice (e : β → simplex α) (m : β) (p : α → ℝ) (b : α)
    (y : ℝ) :
    (e m : α → ℝ) ⬝ᵥ lossIwEstimator p b y = 1 - (e m : α → ℝ) b * (1 - y) / p b :=
  dotProduct_lossIwEstimator (mem_simplex_iff.1 (e m).2).2

namespace Exp4IX

section LossIwEstimator

variable {𝓞 Ω : Type*} {adv : 𝓞 → β → simplex α} {η γ : ℕ → ℝ}

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
lemma sum_mul_one_sub_sq_le (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) :
    ∑ m', exp4IXExpertWeights adv η γ t (history O A Y t ω) m' *
        (1 - (adv (O t ω) m' : α → ℝ) ⬝ᵥ lossIwEstimator
          (exp4IXWeights adv η γ t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω)) ^ 2 ≤
      (1 - Y t ω) ^ 2 / exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) (A t ω) := by
  set P := exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) (A t ω) with hP
  set q := exp4IXExpertWeights adv η γ t (history O A Y t ω) with hq
  set e : β → ℝ := fun m' ↦ (adv (O t ω) m' : α → ℝ) (A t ω) with he
  simp only [dotProduct_lossIwEstimator_advice, sub_sub_cancel]
  -- `∑ m', q m' * e m' ^ 2 ≤ ∑ m', q m' * e m' = P`, as the advice lies in `[0, 1]`
  have hle : ∑ m', q m' * e m' ^ 2 ≤ P := by
    rw [hP, exp4IXWeights_apply]
    refine Finset.sum_le_sum fun m' _ ↦ mul_le_mul_of_nonneg_left ?_
      (by rw [hq, exp4IXExpertWeights_def]; exact softmax_nonneg _ m')
    have h0 : 0 ≤ e m' := (mem_simplex_iff.1 (adv (O t ω) m').2).1 _
    have h1 : e m' ≤ 1 := by simpa using (simplex_subset_Icc (adv (O t ω) m').2).2 (A t ω)
    nlinarith
  calc ∑ m', q m' * ((adv (O t ω) m' : α → ℝ) (A t ω) * (1 - Y t ω) / P) ^ 2
  _ = (∑ m', q m' * e m' ^ 2) * ((1 - Y t ω) / P) ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun m' _ ↦ by rw [he, mul_div_assoc]; ring
  _ ≤ P * ((1 - Y t ω) / P) ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  _ = (1 - Y t ω) ^ 2 / P := by
      rcases eq_or_ne P 0 with h0 | h0
      · simp [h0]
      · field_simp

end LossIwEstimator

end Exp4IX

variable {η : ℝ}

section Algorithm

variable [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty β]

/-- **Exp4** with learning rate `η` [LS, Algorithm 11] (with `γ = 0`): Exp4-IX that observes at
round `n` the advice `e : β → simplex α` of the experts (`adv = id`), with the constant learning
rate `η` and no implicit exploration. It draws its action from the mixture of the advice with the
exponential weights of `η` times the cumulative reward estimates of the experts. -/
noncomputable def exp4 (η : ℝ) : Algorithm (β → simplex α) α ℝ :=
  exp4IX id measurable_id (fun _ ↦ η) 0

lemma exp4_def (η : ℝ) :
    exp4 (α := α) (β := β) η = exp4IX id measurable_id (fun _ ↦ η) 0 := (rfl)

/-- With a single expert, Exp4 does not depend on its learning rate: it follows the advice. -/
lemma exp4_eq_of_subsingleton [Subsingleton β] (η η' : ℝ) :
    exp4 (α := α) (β := β) η = exp4 η' :=
  exp4IX_eq_of_subsingleton _ _ _ _ _

end Algorithm

namespace Exp4

section Pathwise

variable {Ω : Type*} {n : ℕ} [Nonempty β]

/-- **Pathwise regret of the experts' weights in Exp4** [LS, Lemma 18.2]. Along every sequence of
observations `O`, actions `A` and feedbacks `Y ≤ 1` of the rounds `t < n`, with `Q t` the weights
of Exp4 on the experts at round `t` and `X̂ᴱ t m = O t m ⬝ᵥ X̂ t` the estimated reward of expert
`m`, for every expert `m` and `η > 0`,
`∑ t < n, (X̂ᴱ t m - ∑ m', Q t m' * X̂ᴱ t m') ≤
  log M / η + η / 2 * ∑ t < n, ∑ m', Q t m' * (1 - X̂ᴱ t m') ^ 2`,
with `M` the number of experts. This is the local-norm bound of Exp4-IX for the constant learning
rate `η` and `γ = 0`, since the estimated rewards are one minus the estimated losses. -/
theorem sum_sub_sum_le (hη : 0 < η) (O : ℕ → Ω → β → simplex α) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → ℝ) (ω : Ω) (hY : ∀ t < n, Y t ω ≤ 1) (m : β) :
    ∑ t ∈ range n, ((O t ω m : α → ℝ) ⬝ᵥ lossIwEstimator
        (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) -
      ∑ m', exp4IXExpertWeights id (fun _ ↦ η) 0 t (history O A Y t ω) m' *
        (O t ω m' : α → ℝ) ⬝ᵥ lossIwEstimator
          (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω)) ≤
      log (Fintype.card β) / η + η / 2 * ∑ t ∈ range n,
        ∑ m', exp4IXExpertWeights id (fun _ ↦ η) 0 t (history O A Y t ω) m' *
          (1 - (O t ω m' : α → ℝ) ⬝ᵥ lossIwEstimator
            (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω))
              (A t ω) (Y t ω)) ^ 2 := by
  have key := Exp4IX.sum_sum_mul_sub_le (adv := id) (η := fun _ ↦ η) (γ := 0) O A Y ω
    (fun _ ↦ hη) antitone_const (fun _ ↦ le_rfl) hY m
  -- with `γ = 0`, the estimates are the importance-weighted estimates for the weights on the arms
  simp only [Pi.zero_apply, add_zero, id] at key
  -- the estimated rewards are one minus the estimated losses
  have hX : ∀ t m', (O t ω m' : α → ℝ) ⬝ᵥ lossIwEstimator
      (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) =
        1 - (O t ω m' : α → ℝ) ⬝ᵥ iwEstimator
          (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (1 - Y t ω) :=
    fun t m' ↦ by simp only [dotProduct_lossIwEstimator_advice, dotProduct_iwEstimator]
  have h1 : ∀ t (y : β → ℝ), (1 - y m) - ∑ m', exp4IXExpertWeights id (fun _ ↦ η) 0 t
      (history O A Y t ω) m' * (1 - y m') =
        ∑ m', exp4IXExpertWeights id (fun _ ↦ η) 0 t (history O A Y t ω) m' * y m' - y m :=
    fun t y ↦ by
      simp only [mul_sub, mul_one, sum_sub_distrib,
        (mem_simplex_iff.1 (exp4IXExpertWeights_mem_simplex t _)).2]
      ring
  simp only [hX, sub_sub_cancel]
  rw [Finset.mul_sum]
  exact le_of_eq_of_le (Finset.sum_congr rfl fun t _ ↦ h1 t fun m' ↦ (O t ω m' : α → ℝ) ⬝ᵥ
    iwEstimator (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω)
      (1 - Y t ω)) key

/-- **Pathwise bound on the estimated regret of Exp4.** Along every sequence of observations `O`,
actions `A` and feedbacks `Y ≤ 1` of the rounds `t < n` whose actions have positive weight
`P t (A t)`, with `X̂ᴱ t m = O t m ⬝ᵥ X̂ t` the estimated reward of expert `m`, for every expert `m`
and `η > 0`,
`∑ t < n, (X̂ᴱ t m - Y t) ≤ log M / η + η / 2 * ∑ t < n, (1 - Y t) ^ 2 / P t (A t)`. -/
theorem sum_dotProduct_lossIwEstimator_sub_le (hη : 0 < η) (O : ℕ → Ω → β → simplex α)
    (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ) (ω : Ω) (hY : ∀ t < n, Y t ω ≤ 1)
    (hpos : ∀ t < n, exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω) (A t ω) ≠ 0)
    (m : β) :
    ∑ t ∈ range n, ((O t ω m : α → ℝ) ⬝ᵥ
        lossIwEstimator
          (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) - Y t ω) ≤
      log (Fintype.card β) / η + η / 2 * ∑ t ∈ range n,
        (1 - Y t ω) ^ 2 / exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω) (A t ω) := by
  calc ∑ t ∈ range n, ((O t ω m : α → ℝ) ⬝ᵥ
        lossIwEstimator
          (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) - Y t ω)
  _ = ∑ t ∈ range n, ((O t ω m : α → ℝ) ⬝ᵥ
        lossIwEstimator
          (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) -
      ∑ m', exp4IXExpertWeights id (fun _ ↦ η) 0 t (history O A Y t ω) m' * (O t ω m' : α → ℝ) ⬝ᵥ
        lossIwEstimator
          (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω)) :=
      Finset.sum_congr rfl fun t ht ↦ by
        have key := Exp4IX.sum_exp4IXExpertWeights_mul_dotProduct_lossIwEstimator (adv := id)
          (η := fun _ ↦ η) (γ := 0) t (history O A Y t ω) (O t ω) (Y t ω) (hpos t (mem_range.1 ht))
        simp only [id_eq] at key
        rw [key]
  _ ≤ _ := sum_sub_sum_le hη O A Y ω hY m
  _ ≤ _ := by
      gcongr with t ht
      exact Exp4IX.sum_mul_one_sub_sq_le (adv := id) O A Y ω t

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
        exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω) (A t ω)) =ᵐ[P]
      fun ω ↦ (E t m : α → ℝ) (A t ω) * (1 - x t (A t ω)) /
        exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω) (A t ω) := by
  filter_upwards [hO, hY] with ω hωO hωY
  rw [hωO, hωY, Function.comp_apply]

omit [Nonempty α] in
/-- Along a run of Exp4 whose observation of round `t` is the advice `E t` and whose feedback is
the reward `x t (A t)` of its action, the estimated reward `X̂ᴱ t m = O t m ⬝ᵥ X̂ t` of expert `m`
is integrable. -/
lemma integrable_dotProduct_lossIwEstimator (hO : O t =ᵐ[P] fun _ ↦ E t)
    (hY : Y t =ᵐ[P] x t ∘ A t) (h : IsAlgEnvSeq O A Y (exp4 η) env P) (m : β) :
    Integrable (fun ω ↦ (O t ω m : α → ℝ) ⬝ᵥ
      lossIwEstimator
        (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω)) P := by
  have hw := Exp4IX.isAlgEnvSeq_weightAlgorithm h
  simp only [dotProduct_lossIwEstimator_advice]
  exact (integrable_const 1).sub ((WeightAlgorithm.integrable_div_weights hw t
    (fun b ↦ (E t m : α → ℝ) b * (1 - x t b))).congr (advice_mul_div_ae_eq hO hY m).symm)

/-- **The estimated rewards of the experts are unbiased** [LS, (18.10)]. Along a run of Exp4 whose
observation of round `t` is the advice `E t` and whose feedback is the reward `x t (A t)` of its
action, the estimated reward `X̂ᴱ t m = O t m ⬝ᵥ X̂ t` of expert `m` has expectation
`E t m ⬝ᵥ x t`, the expected reward of following its advice. -/
theorem integral_dotProduct_lossIwEstimator (hO : O t =ᵐ[P] fun _ ↦ E t)
    (hY : Y t =ᵐ[P] x t ∘ A t) (h : IsAlgEnvSeq O A Y (exp4 η) env P) (m : β) :
    P[fun ω ↦ (O t ω m : α → ℝ) ⬝ᵥ
      lossIwEstimator
        (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω)] =
      (E t m : α → ℝ) ⬝ᵥ x t := by
  have hw := Exp4IX.isAlgEnvSeq_weightAlgorithm h
  simp only [dotProduct_lossIwEstimator_advice]
  -- the advice of `m` vanishes on the arms of weight zero, as `m` has positive weight
  have hc : ∀ᵐ ω ∂P, ∀ b, exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω) b = 0 →
      (E t m : α → ℝ) b * (1 - x t b) = 0 := by
    filter_upwards [hO] with ω hω b hb
    have := adv_apply_eq_zero_of_exp4IXWeights_eq_zero hb m
    rw [id, hω] at this
    rw [this, zero_mul]
  rw [integral_sub (integrable_const 1) ((WeightAlgorithm.integrable_div_weights hw t
      (fun b ↦ (E t m : α → ℝ) b * (1 - x t b))).congr (advice_mul_div_ae_eq hO hY m).symm),
    integral_congr_ae (advice_mul_div_ae_eq hO hY m),
    WeightAlgorithm.integral_div_weights hw t (c := fun b ↦ (E t m : α → ℝ) b * (1 - x t b)) hc]
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
  have hw := Exp4IX.isAlgEnvSeq_weightAlgorithm h
  set X : ℕ → β → Ω → ℝ := fun t m ω ↦ (O t ω m : α → ℝ) ⬝ᵥ
    lossIwEstimator
      (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) with hXdef
  set V : ℕ → Ω → ℝ := fun t ω ↦
    (1 - Y t ω) ^ 2 / exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω) (A t ω)
  have hVint : ∀ t ∈ range n, Integrable (V t) P := fun t ht ↦
    (WeightAlgorithm.integrable_div_weights hw t fun b ↦ (1 - x t b) ^ 2).congr
      (comp_feedback_ae_eq (hY t (mem_range.1 ht))
        fun z b y ↦ (1 - y) ^ 2 / exp4IXWeights id (fun _ ↦ η) 0 t z.1 z.2 b).symm
  have hYint := fun t (ht : t ∈ range n) ↦
    h.integrable_feedback_of_ae_eq (hY t (mem_range.1 ht))
  have hXint : ∀ m, ∀ t ∈ range n, Integrable (X t m) P := fun m t ht ↦
    integrable_dotProduct_lossIwEstimator (hO t (mem_range.1 ht)) (hY t (mem_range.1 ht)) h m
  -- almost surely, the feedbacks are at most `1` and the actions have positive weight
  have hgood : ∀ᵐ ω ∂P, (∀ t < n, Y t ω ≤ 1) ∧
      ∀ t, exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω) (A t ω) ≠ 0 :=
    (ae_feedback_le_one hY fun t ht a ↦ (hx t ht a).2).and
      (ae_all_iff.2 fun t ↦ (WeightAlgorithm.ae_weights_action_pos hw t).mono fun _ h ↦ h.ne')
  have hle : ∑ t ∈ range n, P[V t] ≤ (n * Fintype.card α : ℝ) :=
    WeightAlgorithm.sum_integral_one_sub_sq_div_weights_le hw (ae_feedback_mem_Icc hY hx)
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
  refine (integral_sum_le_add_mul_of_ae_le (B := log (Fintype.card β) / η) (c := η / 2)
    (by positivity) (fun t ht ↦ (hXint m t ht).sub (hYint t ht)) hVint hle ?_).trans_eq (by ring)
  filter_upwards [hgood] with ω hω
  exact sum_dotProduct_lossIwEstimator_sub_le hη O A Y ω hω.1 (fun t _ ↦ hω.2 t) m

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
  refine (expertRegret_le hη0 hO hY hx h).trans (le_of_eq ?_)
  rw [mul_assoc η, mul_assoc 2 (n : ℝ)]
  exact div_sqrt_add_sqrt_mul_div_two _ hm.le

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
