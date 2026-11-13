/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Real.Sqrt
public import LMLExplore.Bandits.Adversarial.Regret
public import LMLExplore.Bandits.Exp4.IX

/-!
# Pseudo-regret of Exp4-IX against an adaptive adversary

Exp4-IX (`LMLExplore.Bandits.exp4IX`) plays against any environment `env : Environment 𝓞 α ℝ`,
whose feedback law at round `t` may depend on the history and on the observation of round `t`: an
adaptive adversary. With `m_t(a) = env.means O A Y a t` the mean reward of arm `a` at round `t`
given the past and `E t = adv (O t)` the advice of round `t`, the expert pseudo-regret is
`max_m E[∑_{t < n} (⟨E t m, m_t⟩ - Y t)]` (`LMLExplore.Bandits.expertPseudoRegret`). This file
bounds it for rewards in `[0, 1]`, nonincreasing learning rates `η t > 0` and implicit-exploration
parameters `γ t ≥ 0`, with `k` arms and `M` experts:
`max_m E[∑_{t < n} (⟨E t m, m_t⟩ - Y t)] ≤ log M / η (n - 1) + k ∑_{t < n} (γ t + η t / 2)`.

The proof takes expectations in the pathwise bound `Exp4IX.sum_one_sub_sub_dotProduct_le`. Given
the past, the importance-weighted estimate `E t m ⬝ᵥ Ŷ t` of the loss of expert `m`, computed with
the weights `P t` of Exp4-IX on the arms, has conditional mean `⟨E t m, 1 - m_t⟩` [LS, (18.10)]:
the advice of `m` vanishes on the arms of weight zero, since every expert has positive weight. The
implicit exploration `γ t` only lowers the estimates, and the expected sum of the estimates of
round `t` is at most `k`. For `γ = 0` the bound is `log M / η (n - 1) + k / 2 ∑_{t < n} η t`, and
Exp3 (with the experts that each recommend one arm, `M = k`) inherits it for the pseudo-regret.

The learning rates `η = √(2 log M / (n k))` tuned for the horizon `n` give
`√(2 n k log M)` [LS, Theorem 18.1], and with `M = k` the bound `√(2 n k log k)` of Exp3
[LS, Theorem 11.2]. The anytime rates `η t = √(log M / (k (t + 1)))` give `2 √(n k log M)`, the
bound `2 √(n k log k)` of Exp3 with anytime rates [BCB12, Theorem 3.1].

## Main statements

* `Exp4IX.condExp_dotProduct_iwEstimator`: conditional unbiasedness of the importance-weighted
  estimates of the losses of the experts against any environment [LS, (18.10)].
* `Exp4IX.integral_dotProduct_iwEstimator_le`, `Exp4IX.integral_sum_iwEstimator_le`: the expected
  implicit-exploration estimate of the loss of an expert is at most its expected loss, and the
  expected sum of the estimates of the arms is at most `k`.
* `Exp4IX.integral_sum_sub_le_integral_sum_sub_dotProduct`: the expected regret against an expert
  is at most the expected estimated regret, which the pathwise bound controls.
* `Exp4IX.expertPseudoRegret_le`: the expert pseudo-regret of Exp4-IX against an adaptive
  adversary.
* `Exp4IX.expertPseudoRegret_nonpos_of_subsingleton`: with a single expert, the expert
  pseudo-regret is nonpositive.
* `Exp4IX.expertPseudoRegret_le_sqrt`, `Exp4IX.expertPseudoRegret_le_two_mul_sqrt`: the bounds
  `√(2 n k log M)` for the rate tuned for the horizon [LS, Theorem 18.1] and `2 √(n k log M)` for
  the anytime rates.
* `Exp3.pseudoRegret_le`, `Exp3.pseudoRegret_le_sqrt`: the pseudo-regret of Exp3 with a constant
  learning rate against an adaptive adversary, and [LS, Theorem 11.2].
* `Exp3.pseudoRegret_le_two_mul_sqrt`: the pseudo-regret of Exp3 with anytime learning rates
  [BCB12, Theorem 3.1].

## References

* [BCB12] S. Bubeck and N. Cesa-Bianchi, *Regret analysis of stochastic and nonstochastic
  multi-armed bandit problems*, Foundations and Trends in Machine Learning 5(1), 2012.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real

namespace LMLExplore.Bandits

variable {α β 𝓞 Ω : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [Fintype β] [Nonempty β] [MeasurableSpace 𝓞]
  {adv : 𝓞 → β → simplex α} {hadv : Measurable adv} {η γ : ℕ → ℝ}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {env : Environment 𝓞 α ℝ} {n t : ℕ}

namespace Exp4IX

section Round

omit [Nonempty α] [IsProbabilityMeasure P] in
/-- A run of Exp4-IX is a run of the weight-based algorithm with the weights of Exp4-IX. -/
private lemma isAlgEnvSeq_weightAlgorithm (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P) :
    IsAlgEnvSeq O A Y (weightAlgorithm (fun n x ↦ exp4IXWeights adv η γ n x.1 x.2)
      (fun n a ↦ (measurable_pi_apply a).comp (measurable_exp4IXWeights hadv η γ n))
      (fun n x ↦ exp4IXWeights_mem_simplex n x.1 x.2)) env P :=
  exp4IX_def adv hadv η γ ▸ h

omit [Nonempty α] in
/-- Along a run of Exp4-IX, a random variable bounded by the inverse weight `1 / P t (A t)` of the
action of round `t` is integrable. -/
private lemma integrable_of_abs_le_inv_weights
    (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P) {X : Ω → ℝ}
    (hX : AEStronglyMeasurable X P)
    (hle : ∀ᵐ ω ∂P, |X ω| ≤ 1 / exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) (A t ω)) :
    Integrable X P := by
  have : IsFiniteMeasure P := inferInstance
  exact (WeightAlgorithm.integrable_div_weights (isAlgEnvSeq_weightAlgorithm h) t
    fun _ ↦ 1).mono' hX
    (by simpa only [Real.norm_eq_abs] using hle)

omit [Nonempty α] [IsProbabilityMeasure P] in
/-- Along a run of Exp4-IX, the weight of the action of round `t` is a measurable function of the
run. -/
private lemma measurable_exp4IXWeights_action
    (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P) :
    Measurable fun ω ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) (A t ω) :=
  (measurable_from_prod_countable_left
    (f := fun z : (Hist 𝓞 α ℝ t × 𝓞) × α ↦ exp4IXWeights adv η γ t z.1.1 z.1.2 z.2)
    fun b ↦ (measurable_pi_apply b).comp (measurable_exp4IXWeights hadv η γ t)).comp
    (((h.measurable_history t).prodMk (h.measurable_obs t)).prodMk (h.measurable_action t))

omit [Nonempty α] [IsProbabilityMeasure P] in
/-- Along a run of Exp4-IX, the advice of an expert at the action of round `t` is a measurable
function of the run. -/
private lemma measurable_adv_action (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (m : β) : Measurable fun ω ↦ (adv (O t ω) m : α → ℝ) (A t ω) :=
  (measurable_from_prod_countable_left (f := fun z : 𝓞 × α ↦ (adv z.1 m : α → ℝ) z.2)
    fun b ↦ (measurable_pi_apply b).comp (measurable_subtype_coe.comp
      ((measurable_pi_apply m).comp hadv))).comp
    ((h.measurable_obs t).prodMk (h.measurable_action t))

omit [Nonempty α] in
/-- Along a run of Exp4-IX with feedback in `[0, 1]` at round `t`, almost surely, the weight
`P t (A t)` of the action of round `t` is positive and, for every `e ∈ [0, 1]` and `g ≥ 0`, the
estimate `e * (1 - Y t) / (P t (A t) + g)` of a loss lies in `[0, 1 / P t (A t)]`. -/
private lemma ae_mul_one_sub_div_mem_Icc (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (hY : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1) :
    ∀ᵐ ω ∂P, 0 < exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) (A t ω) ∧
      ∀ e ∈ Set.Icc (0 : ℝ) 1, ∀ g : ℝ, 0 ≤ g →
        e * (1 - Y t ω) / (exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) (A t ω) + g) ∈
          Set.Icc 0 (1 / exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) (A t ω)) := by
  have : IsFiniteMeasure P := inferInstance
  filter_upwards [hY, WeightAlgorithm.ae_weights_action_pos (isAlgEnvSeq_weightAlgorithm h) t]
    with ω hω hw
  refine ⟨hw, fun e he g hg ↦ ⟨div_nonneg (mul_nonneg he.1 (sub_nonneg.2 hω.2)) (by linarith),
    div_le_div₀ zero_le_one ?_ hw (by linarith)⟩⟩
  exact (mul_le_mul he.2 (sub_le_self _ hω.1) (sub_nonneg.2 hω.2) zero_le_one).trans_eq (one_mul 1)

omit [Nonempty α] in
/-- Along a run of Exp4-IX with feedback in `[0, 1]` at round `t`, the estimated loss
`adv (O t) m (A t) * (1 - Y t) / (P t (A t) + g)` of an expert `m`, for the weights `P t + g` with
`g ≥ 0`, is integrable. -/
private lemma integrable_adv_action_mul_div (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (hY : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1) (m : β) {g : ℝ} (hg : 0 ≤ g) :
    Integrable (fun ω ↦ (adv (O t ω) m : α → ℝ) (A t ω) * (1 - Y t ω) /
      (exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) (A t ω) + g)) P := by
  refine integrable_of_abs_le_inv_weights (t := t) h (((measurable_adv_action h m).mul
    (measurable_const.sub (h.measurable_feedback t))).div
      ((measurable_exp4IXWeights_action h).add_const _)).aestronglyMeasurable ?_
  filter_upwards [ae_mul_one_sub_div_mem_Icc h hY] with ω ⟨_, hω⟩
  have := hω ((adv (O t ω) m : α → ℝ) (A t ω)) ⟨(simplex_subset_Icc (adv (O t ω) m).2).1 _,
    (simplex_subset_Icc (adv (O t ω) m).2).2 _⟩ g hg
  rw [abs_of_nonneg this.1]
  exact this.2

/-- **Conditional unbiasedness of the estimated losses of the experts** [LS, (18.10)] against any
environment: along a run of Exp4-IX whose feedback at round `t` is almost surely in `[0, 1]`, the
importance-weighted estimate `adv (O t) m ⬝ᵥ Ŷ t` of the loss of expert `m`, with the estimates
`Ŷ t = iwEstimator (P t) (A t) (1 - Y t)` for the weights `P t` of Exp4-IX on the arms, has
conditional expectation `∑ a, adv (O t) m a * (1 - m_t(a))` given the history and the observation
of round `t`, with `m_t(a) = env.means O A Y a t` the mean reward of arm `a` at round `t`. -/
theorem condExp_dotProduct_iwEstimator (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (hY : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1) (m : β) :
    P[fun ω ↦ (adv (O t ω) m : α → ℝ) ⬝ᵥ
        iwEstimator (exp4IXWeights adv η γ t (history O A Y t ω) (O t ω)) (A t ω) (1 - Y t ω)
      | h.filtrationObs t] =ᵐ[P]
      fun ω ↦ ∑ a, (adv (O t ω) m : α → ℝ) a * (1 - env.means O A Y a t ω) := by
  have hYint : Integrable (Y t) P :=
    Integrable.of_mem_Icc 0 1 (h.measurable_feedback t).aemeasurable hY
  have hint : Integrable (fun ω ↦ (adv (O t ω) m : α → ℝ) (A t ω) /
      exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) (A t ω) * (1 - Y t ω)) P :=
    (integrable_adv_action_mul_div h hY m le_rfl).congr
      (ae_of_all _ fun ω ↦ by simp only [add_zero]; ring)
  -- view the run as a run of a weight-based algorithm
  have halg := exp4IX_def adv hadv η γ
  generalize exp4IX adv hadv η γ = alg at h halg
  subst halg
  have hf : ∀ b, Measurable fun x : Hist 𝓞 α ℝ t × 𝓞 ↦
      (adv x.2 m : α → ℝ) b / exp4IXWeights adv η γ t x.1 x.2 b := fun b ↦
    ((measurable_pi_apply b).comp (measurable_subtype_coe.comp
      ((measurable_pi_apply m).comp (hadv.comp measurable_snd)))).div
      ((measurable_pi_apply b).comp (measurable_exp4IXWeights hadv η γ t))
  have hmean : ∀ b, Measurable fun x : Hist 𝓞 α ℝ t × 𝓞 ↦ 1 - ∫ y, y ∂env.feedback t (x, b) :=
    fun b ↦ measurable_const.sub
      ((stronglyMeasurable_id.integral_kernel (κ := env.feedback t)).measurable.comp
        measurable_prodMk_right)
  -- given the past and the action, the loss `1 - Y t` has mean `1 - m_t(A t)`
  have hZm : P[fun ω ↦ 1 - Y t ω | h.filtrationAction t] =ᵐ[P]
      fun ω ↦ 1 - ∫ y, y ∂env.feedback t ((history O A Y t ω, O t ω), A t ω) := by
    filter_upwards [condExp_const_sub (h.filtrationAction.le t) hYint 1,
      h.condExp_feedback t hYint] with ω h1 h2
    rw [h1, h2, Environment.means_eq_integral]
  have hfun : (fun ω ↦ (adv (O t ω) m : α → ℝ) ⬝ᵥ
      iwEstimator (exp4IXWeights adv η γ t (history O A Y t ω) (O t ω)) (A t ω) (1 - Y t ω)) =
      fun ω ↦ (adv (O t ω) m : α → ℝ) (A t ω) /
        exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) (A t ω) * (1 - Y t ω) := by
    funext ω
    rw [dotProduct_iwEstimator, div_mul_eq_mul_div]
  rw [hfun]
  filter_upwards [WeightAlgorithm.condExp_comp_action_mul h t hf hmean
    (Z := fun ω ↦ 1 - Y t ω) ((integrable_const 1).sub hYint) hZm hint] with ω hω
  rw [hω]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Environment.means_eq_integral]
  rcases eq_or_ne (exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) b) 0 with hb | hb
  · simp [hb, adv_apply_eq_zero_of_exp4IXWeights_eq_zero hb m]
  · field_simp

/-- Along a run of Exp4-IX whose feedback at round `t` is almost surely in `[0, 1]`, the expected
loss `∑ a, adv (O t) m a * (1 - m_t(a))` of an expert `m` at round `t` is integrable, with
`m_t(a) = env.means O A Y a t` the mean reward of arm `a` at round `t`. -/
lemma integrable_sum_mul_one_sub_means (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (hY : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1) (m : β) :
    Integrable (fun ω ↦ ∑ a, (adv (O t ω) m : α → ℝ) a * (1 - env.means O A Y a t ω)) P :=
  integrable_condExp.congr (condExp_dotProduct_iwEstimator h hY m)

/-- Along a run of Exp4-IX whose feedback at round `t` is almost surely in `[0, 1]`, the expected
reward `∑ a, adv (O t) m a * m_t(a)` of an expert `m` at round `t` is integrable, with
`m_t(a) = env.means O A Y a t` the mean reward of arm `a` at round `t`. -/
lemma integrable_sum_mul_means (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (hY : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1) (m : β) :
    Integrable (fun ω ↦ ∑ a, (adv (O t ω) m : α → ℝ) a * env.means O A Y a t ω) P := by
  refine ((integrable_const 1).sub (integrable_sum_mul_one_sub_means h hY m)).congr
    (ae_of_all _ fun ω ↦ ?_)
  simp only [Pi.sub_apply, mul_sub, mul_one, sum_sub_distrib,
    (mem_simplex_iff.1 (adv (O t ω) m).2).2, sub_sub_cancel]

omit [Nonempty α] in
/-- Along a run of Exp4-IX whose feedback at round `t` is almost surely in `[0, 1]`, the
implicit-exploration estimate `adv (O t) m ⬝ᵥ Ŷ t` of the loss of an expert `m` is integrable. -/
lemma integrable_dotProduct_iwEstimator (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (hγ : 0 ≤ γ t) (hY : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1) (m : β) :
    Integrable (fun ω ↦ (adv (O t ω) m : α → ℝ) ⬝ᵥ iwEstimator
      (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
        (1 - Y t ω)) P := by
  simpa only [dotProduct_iwEstimator] using integrable_adv_action_mul_div h hY m hγ

omit [Nonempty α] in
/-- Along a run of Exp4-IX whose feedback at round `t` is almost surely in `[0, 1]`, the sum
`∑ a, Ŷ t a` of the implicit-exploration estimates of the losses of the arms is integrable. -/
lemma integrable_sum_iwEstimator (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (hγ : 0 ≤ γ t) (hY : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1) :
    Integrable (fun ω ↦ ∑ a, iwEstimator
      (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
        (1 - Y t ω) a) P := by
  simp only [sum_iwEstimator]
  refine integrable_of_abs_le_inv_weights (t := t) h ((measurable_const.sub
    (h.measurable_feedback t)).div
      ((measurable_exp4IXWeights_action h).add_const _)).aestronglyMeasurable ?_
  filter_upwards [ae_mul_one_sub_div_mem_Icc h hY] with ω ⟨_, hω⟩
  have := hω 1 ⟨zero_le_one, le_rfl⟩ (γ t) hγ
  rw [one_mul] at this
  rw [abs_of_nonneg this.1]
  exact this.2

/-- **The estimated loss of an expert is at most its loss in expectation** [LS, (18.10) and
Lemma 12.4]: along a run of Exp4-IX whose feedback at round `t` is almost surely in `[0, 1]`, with
`γ t ≥ 0`, the implicit-exploration estimate `adv (O t) m ⬝ᵥ Ŷ t` of the loss of an expert `m` has
expectation at most the expected loss `E[∑ a, adv (O t) m a * (1 - m_t(a))]` of `m`, with
`m_t(a) = env.means O A Y a t` the mean reward of arm `a` at round `t`. -/
theorem integral_dotProduct_iwEstimator_le (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (hγ : 0 ≤ γ t) (hY : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1) (m : β) :
    P[fun ω ↦ (adv (O t ω) m : α → ℝ) ⬝ᵥ iwEstimator
        (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
          (1 - Y t ω)] ≤
      P[fun ω ↦ ∑ a, (adv (O t ω) m : α → ℝ) a * (1 - env.means O A Y a t ω)] := by
  -- the estimates with the weights `P t + γ t` are at most those with the weights `P t`
  calc P[fun ω ↦ (adv (O t ω) m : α → ℝ) ⬝ᵥ iwEstimator
        (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
          (1 - Y t ω)]
  _ ≤ P[fun ω ↦ (adv (O t ω) m : α → ℝ) (A t ω) * (1 - Y t ω) /
        (exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) (A t ω) + 0)] := by
      simp only [dotProduct_iwEstimator]
      refine integral_mono_ae (integrable_adv_action_mul_div h hY m hγ)
        (integrable_adv_action_mul_div (g := 0) h hY m le_rfl) ?_
      filter_upwards [ae_mul_one_sub_div_mem_Icc h hY, hY] with ω ⟨hw, _⟩ hYω
      rw [add_zero]
      exact div_le_div_of_nonneg_left (mul_nonneg ((mem_simplex_iff.1 (adv (O t ω) m).2).1 _)
        (sub_nonneg.2 hYω.2)) hw (le_add_of_nonneg_right hγ)
  _ = P[fun ω ↦ ∑ a, (adv (O t ω) m : α → ℝ) a * (1 - env.means O A Y a t ω)] := by
      rw [← integral_congr_ae (condExp_dotProduct_iwEstimator h hY m),
        integral_condExp (h.filtrationObs.le t)]
      simp only [add_zero, dotProduct_iwEstimator]

/-- Along a run of Exp4-IX whose feedback at round `t` is almost surely in `[0, 1]`, with
`γ t ≥ 0`, the sum `∑ a, Ŷ t a` of the implicit-exploration estimates of the losses of the arms has
expectation at most the number `k` of arms. -/
theorem integral_sum_iwEstimator_le (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (hγ : 0 ≤ γ t) (hY : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1) :
    P[fun ω ↦ ∑ a, iwEstimator
        (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
          (1 - Y t ω) a] ≤ (Fintype.card α : ℝ) := by
  have h' := isAlgEnvSeq_weightAlgorithm h
  -- each sum is at most the inverse weight of the action, of expectation at most `k`
  refine (integral_mono_ae (integrable_sum_iwEstimator h hγ hY)
    (WeightAlgorithm.integrable_div_weights h' t fun _ ↦ 1) ?_).trans
    ((WeightAlgorithm.integral_div_weights_le h' t fun _ ↦ zero_le_one).trans_eq (by simp))
  filter_upwards [ae_mul_one_sub_div_mem_Icc h hY] with ω ⟨_, hω⟩
  have := hω 1 ⟨zero_le_one, le_rfl⟩ (γ t) hγ
  rw [one_mul] at this
  simpa only [sum_iwEstimator] using this.2

end Round

omit [IsProbabilityMeasure P] in
/-- If the feedbacks of the rounds `t < n` are almost surely in `[0, 1]`, so is the feedback of
each round `t ∈ range n`. -/
private lemma ae_mem_Icc_of_mem_range (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1)
    (ht : t ∈ range n) : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1 :=
  hY.mono fun _ hω ↦ hω t (mem_range.1 ht)

omit [Nonempty α] in
/-- Along a run of Exp4-IX whose feedbacks of the rounds `t < n` are almost surely in `[0, 1]`, the
loss `1 - Y t` of each round `t ∈ range n` is integrable. -/
private lemma integrable_one_sub_of_mem_range (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) (ht : t ∈ range n) :
    Integrable (fun ω ↦ 1 - Y t ω) P :=
  (integrable_const 1).sub (Integrable.of_mem_Icc 0 1 (h.measurable_feedback t).aemeasurable
    (ae_mem_Icc_of_mem_range hY ht))

/-- **The expected regret against an expert is at most the expected estimated regret**
[LS, (18.10) and Lemma 12.4]: along a run of Exp4-IX against any environment whose feedbacks of
the rounds `t < n` are almost surely in `[0, 1]`, with `γ t ≥ 0`, the expected regret
`E[∑_{t < n} (⟨adv (O t) m, m_t⟩ - Y t)]` against an expert `m` is at most the expected estimated
regret `E[∑_{t < n} ((1 - Y t) - adv (O t) m ⬝ᵥ Ŷ t)]`, with `m_t(a) = env.means O A Y a t` the
mean reward of arm `a` at round `t` and `Ŷ t` the implicit-exploration estimates of the losses. -/
theorem integral_sum_sub_le_integral_sum_sub_dotProduct
    (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P) (hγ : ∀ t < n, 0 ≤ γ t)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) (m : β) :
    P[fun ω ↦ ∑ t ∈ range n, (∑ a, (adv (O t ω) m : α → ℝ) a * env.means O A Y a t ω -
        Y t ω)] ≤ P[fun ω ↦ ∑ t ∈ range n, ((1 - Y t ω) - (adv (O t ω) m : α → ℝ) ⬝ᵥ iwEstimator
        (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
          (1 - Y t ω))] := by
  have hYt : ∀ t ∈ range n, ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1 := fun _ ↦ ae_mem_Icc_of_mem_range hY
  have hYint : ∀ t ∈ range n, Integrable (fun ω ↦ 1 - Y t ω) P := fun _ ↦
    integrable_one_sub_of_mem_range h hY
  have hLint := fun t (ht : t ∈ range n) ↦
    integrable_dotProduct_iwEstimator h (hγ t (mem_range.1 ht)) (hYt t ht) m
  calc P[fun ω ↦ ∑ t ∈ range n, (∑ a, (adv (O t ω) m : α → ℝ) a * env.means O A Y a t ω -
        Y t ω)]
  -- the expected reward of `m` minus the reward is the loss minus the expected loss of `m`
  _ = ∑ t ∈ range n, (P[fun ω ↦ 1 - Y t ω] -
        P[fun ω ↦ ∑ a, (adv (O t ω) m : α → ℝ) a * (1 - env.means O A Y a t ω)]) := by
      rw [integral_finsetSum (f := fun t ω ↦
          ∑ a, (adv (O t ω) m : α → ℝ) a * env.means O A Y a t ω - Y t ω) _
        fun t ht ↦ ((integrable_sum_mul_means h (hYt t ht) m).sub
          (Integrable.of_mem_Icc 0 1 (h.measurable_feedback t).aemeasurable (hYt t ht)))]
      refine Finset.sum_congr rfl fun t ht ↦ ?_
      rw [← integral_sub (hYint t ht) (integrable_sum_mul_one_sub_means h (hYt t ht) m)]
      refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
      simp only [mul_sub, mul_one, sum_sub_distrib, (mem_simplex_iff.1 (adv (O t ω) m).2).2]
      ring
  _ ≤ ∑ t ∈ range n, (P[fun ω ↦ 1 - Y t ω] - P[fun ω ↦ (adv (O t ω) m : α → ℝ) ⬝ᵥ iwEstimator
        (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
          (1 - Y t ω)]) := Finset.sum_le_sum fun t ht ↦
      sub_le_sub_left
        (integral_dotProduct_iwEstimator_le h (hγ t (mem_range.1 ht)) (hYt t ht) m) _
  _ = P[fun ω ↦ ∑ t ∈ range n, ((1 - Y t ω) - (adv (O t ω) m : α → ℝ) ⬝ᵥ iwEstimator
        (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
          (1 - Y t ω))] := by
      rw [integral_finsetSum (f := fun t ω ↦ (1 - Y t ω) - (adv (O t ω) m : α → ℝ) ⬝ᵥ
          iwEstimator (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t)
            (A t ω) (1 - Y t ω)) _ fun t ht ↦ (hYint t ht).sub (hLint t ht)]
      exact Finset.sum_congr rfl fun t ht ↦ (integral_sub (hYint t ht) (hLint t ht)).symm

/-- **Pseudo-regret of Exp4-IX against an adaptive adversary**, the bound of [LS, proof of
Theorem 18.1] for a constant rate, `γ = 0` and an oblivious adversary, and of [BCB12, proof of
Theorem 3.1] for Exp3 with nonincreasing rates. Along a run of Exp4-IX against any environment
whose feedbacks of the rounds `t < n` are almost surely in `[0, 1]`, for nonincreasing learning
rates `η t > 0` and implicit-exploration parameters `γ t ≥ 0`, the expert pseudo-regret after `n`
rounds is at most `log M / η (n - 1) + k ∑_{t < n} (γ t + η t / 2)`, with `k` the number of arms
and `M` the number of experts. For `γ = 0` this is `log M / η (n - 1) + k / 2 ∑_{t < n} η t`. -/
theorem expertPseudoRegret_le (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (hη : ∀ t, 0 < η t) (hη_anti : Antitone η) (hγ : ∀ t, 0 ≤ γ t)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) :
    expertPseudoRegret env (fun o m ↦ (adv o m : α → ℝ)) O A Y P n ≤
      log (Fintype.card β) / η (n - 1) + Fintype.card α * ∑ t ∈ range n, (γ t + η t / 2) := by
  refine expertPseudoRegret_le_iff.2 fun m ↦ ?_
  have hYt : ∀ t ∈ range n, ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1 := fun _ ↦ ae_mem_Icc_of_mem_range hY
  have hYint : ∀ t ∈ range n, Integrable (fun ω ↦ 1 - Y t ω) P := fun _ ↦
    integrable_one_sub_of_mem_range h hY
  have hLint := fun t (ht : t ∈ range n) ↦
    integrable_dotProduct_iwEstimator h (hγ t) (hYt t ht) m
  have hSint := fun t (ht : t ∈ range n) ↦ integrable_sum_iwEstimator h (hγ t) (hYt t ht)
  -- almost surely, the pathwise bound on the estimated regret against `m` holds
  have hpath : ∀ᵐ ω ∂P, ∑ t ∈ range n, ((1 - Y t ω) - (adv (O t ω) m : α → ℝ) ⬝ᵥ iwEstimator
        (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
          (1 - Y t ω)) ≤
      log (Fintype.card β) / η (n - 1) + ∑ t ∈ range n, (γ t + η t / 2) * ∑ a, iwEstimator
        (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
          (1 - Y t ω) a := by
    filter_upwards [hY, ae_all_iff.2 fun t ↦
      WeightAlgorithm.ae_weights_action_pos (isAlgEnvSeq_weightAlgorithm h) t] with ω hω hpos
    exact sum_one_sub_sub_dotProduct_le O A Y ω hη hη_anti hγ hω
      (fun t _ ↦ (add_pos_of_pos_of_nonneg (hpos t) (hγ t)).ne') m
  refine (integral_sum_sub_le_integral_sum_sub_dotProduct h (fun t _ ↦ hγ t) hY m).trans ?_
  -- take expectations in the pathwise bound
  calc P[fun ω ↦ ∑ t ∈ range n, ((1 - Y t ω) - (adv (O t ω) m : α → ℝ) ⬝ᵥ iwEstimator
        (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
          (1 - Y t ω))]
  _ ≤ P[fun ω ↦ (log (Fintype.card β) / η (n - 1) + ∑ t ∈ range n, (γ t + η t / 2) *
        ∑ a, iwEstimator (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t)
          (A t ω) (1 - Y t ω) a : ℝ)] := by
      refine integral_mono_ae (integrable_finsetSum _ fun t ht ↦ (hYint t ht).sub (hLint t ht))
        ((integrable_const _).add (integrable_finsetSum _ fun t ht ↦ (hSint t ht).const_mul _)) ?_
      filter_upwards [hpath] with ω hω using hω
  _ = log (Fintype.card β) / η (n - 1) + ∑ t ∈ range n, (γ t + η t / 2) *
        P[fun ω ↦ ∑ a, iwEstimator
          (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω)
            (1 - Y t ω) a] := by
      rw [integral_add (integrable_const _)
          (integrable_finsetSum _ fun t ht ↦ (hSint t ht).const_mul _),
        integral_finsetSum _ fun t ht ↦ (hSint t ht).const_mul _, integral_const, probReal_univ,
        one_smul]
      simp only [integral_const_mul]
  -- the expected sums of the estimates are at most `k`
  _ ≤ log (Fintype.card β) / η (n - 1) +
        ∑ t ∈ range n, (γ t + η t / 2) * (Fintype.card α : ℝ) := by
      gcongr with t ht
      · exact add_nonneg (hγ t) (half_pos (hη t)).le
      · exact integral_sum_iwEstimator_le h (hγ t) (hYt t ht)
  _ = log (Fintype.card β) / η (n - 1) +
        (Fintype.card α : ℝ) * ∑ t ∈ range n, (γ t + η t / 2) := by
      rw [Finset.mul_sum]
      exact congrArg _ (Finset.sum_congr rfl fun t _ ↦ mul_comm _ _)

/-- **Pseudo-regret of Exp4-IX with a single expert.** Along a run of Exp4-IX with a single expert,
with any learning rates and implicit-exploration parameters, against any environment whose
feedbacks of the rounds `t < n` are almost surely in `[0, 1]`, the expert pseudo-regret is
nonpositive: Exp4-IX follows the advice, whatever its parameters. -/
theorem expertPseudoRegret_nonpos_of_subsingleton [Subsingleton β]
    (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) :
    expertPseudoRegret env (fun o m ↦ (adv o m : α → ℝ)) O A Y P n ≤ 0 := by
  have hM : (Fintype.card β : ℝ) = 1 := by
    exact_mod_cast le_antisymm (Fintype.card_le_one_iff_subsingleton.2 ‹_›) Fintype.card_pos
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set k : ℝ := (Fintype.card α : ℝ) with hk
  have hε' : 0 < ε / (n * k + 1) := by positivity
  rw [exp4IX_eq_of_subsingleton hadv η γ (fun _ ↦ ε / (n * k + 1)) 0] at h
  refine (expertPseudoRegret_le h (fun _ ↦ hε') antitone_const (fun _ ↦ le_rfl) hY).trans ?_
  rw [hM, log_one, zero_div, zero_add, zero_add]
  simp only [Pi.zero_apply, zero_add, sum_const, card_range, nsmul_eq_mul]
  -- `k n ε / (2 (n k + 1)) ≤ ε`
  have h1 : ε / (n * k + 1) * (n * k) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [(by positivity : 0 ≤ (n : ℝ) * k)]
  nlinarith [(by positivity : 0 ≤ ε / (n * k + 1) * (n * k))]

/-- A bound `B ≥ 0` on the expert pseudo-regret of Exp4-IX, against an environment whose feedbacks
of the rounds `t < n` are almost surely in `[0, 1]`, holds as soon as it holds with at least two
experts and at least one round. -/
private lemma expertPseudoRegret_le_of_one_lt_card {B : ℝ}
    (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) (hB : 0 ≤ B)
    (hlt : 1 < (Fintype.card β : ℝ) → 0 < n →
      expertPseudoRegret env (fun o m ↦ (adv o m : α → ℝ)) O A Y P n ≤ B) :
    expertPseudoRegret env (fun o m ↦ (adv o m : α → ℝ)) O A Y P n ≤ B := by
  -- with one expert, the expert pseudo-regret is nonpositive
  rcases (Nat.one_le_cast.2 Fintype.card_pos : (1 : ℝ) ≤ Fintype.card β).eq_or_lt with hM1 | hM1
  · have : Subsingleton β := Fintype.card_le_one_iff_subsingleton.1 (by exact_mod_cast hM1.ge)
    exact (expertPseudoRegret_nonpos_of_subsingleton h hY).trans hB
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [expertPseudoRegret_def] using hB
  exact hlt hM1 hn

/-- **Pseudo-regret of Exp4** [LS, Theorem 18.1] against an adaptive adversary: along a run of
Exp4-IX with `γ = 0` (Exp4) and the learning rate `η = √(2 log M / (n k))` tuned for the horizon
`n`, against any environment whose feedbacks of the rounds `t < n` are almost surely in `[0, 1]`,
the expert pseudo-regret after `n` rounds is at most `√(2 n k log M)`, with `k` the number of arms
and `M` the number of experts. -/
theorem expertPseudoRegret_le_sqrt
    (h : IsAlgEnvSeq O A Y (exp4IX adv hadv
      (fun _ ↦ √(2 * log (Fintype.card β) / (n * Fintype.card α))) 0) env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) :
    expertPseudoRegret env (fun o m ↦ (adv o m : α → ℝ)) O A Y P n ≤
      √(2 * n * Fintype.card α * log (Fintype.card β)) := by
  refine expertPseudoRegret_le_of_one_lt_card h hY (sqrt_nonneg _) fun hM1 hn ↦ ?_
  set k : ℝ := (Fintype.card α : ℝ)
  set M : ℝ := (Fintype.card β : ℝ)
  have hk0 : 0 < k := Nat.cast_pos.2 Fintype.card_pos
  have hnk : 0 < n * k := mul_pos (by exact_mod_cast hn) hk0
  have hη : 0 < √(2 * log M / (n * k)) := sqrt_pos.2 (by have := log_pos hM1; positivity)
  refine (expertPseudoRegret_le h (fun _ ↦ hη) antitone_const (fun _ ↦ le_rfl) hY).trans
    (le_of_eq ?_)
  simp only [Pi.zero_apply, zero_add, sum_const, card_range, nsmul_eq_mul]
  rw [mul_assoc 2 (n : ℝ), ← div_sqrt_add_sqrt_mul_div_two (log M) hnk.le]
  ring

/-- **Pseudo-regret of Exp4 with anytime learning rates** against an adaptive adversary: along a run
of Exp4-IX with `γ = 0` (Exp4) and the learning rates `η t = √(log M / (k (t + 1)))`, against any
environment whose feedbacks of the rounds `t < n` are almost surely in `[0, 1]`, the expert
pseudo-regret after `n` rounds is at most `2 √(n k log M)`, with `k` the number of arms and `M` the
number of experts. -/
theorem expertPseudoRegret_le_two_mul_sqrt
    (h : IsAlgEnvSeq O A Y (exp4IX adv hadv
      (fun t ↦ √(log (Fintype.card β) / (Fintype.card α * (t + 1)))) 0) env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) :
    expertPseudoRegret env (fun o m ↦ (adv o m : α → ℝ)) O A Y P n ≤
      2 * √(n * Fintype.card α * log (Fintype.card β)) := by
  refine expertPseudoRegret_le_of_one_lt_card h hY (by positivity) fun hM1 hn ↦ ?_
  set k : ℝ := (Fintype.card α : ℝ)
  set M : ℝ := (Fintype.card β : ℝ)
  have hk0 : 0 < k := Nat.cast_pos.2 Fintype.card_pos
  set L := log M with hL
  have hL0 : 0 < L := log_pos hM1
  -- the rates are `η t = √(L / k) / √(t + 1)`, positive and nonincreasing
  have hηt : ∀ t : ℕ, √(L / (k * (t + 1))) = √(L / k) * (√((t : ℝ) + 1))⁻¹ := fun t ↦ by
    rw [← div_div, sqrt_div (div_nonneg hL0.le hk0.le), div_eq_mul_inv]
  have hη : ∀ t : ℕ, 0 < √(L / (k * (t + 1))) := fun t ↦ sqrt_pos.2 (by positivity)
  have hanti : Antitone fun t : ℕ ↦ √(L / (k * (t + 1))) := fun s t hst ↦
    sqrt_le_sqrt (div_le_div_of_nonneg_left hL0.le (by positivity)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hst 1) hk0.le))
  refine (expertPseudoRegret_le h hη hanti (fun _ ↦ le_rfl) hY).trans ?_
  simp only [Pi.zero_apply, zero_add]
  -- the first term: `L / η (n - 1) = √L √(k n)`
  have hn1 : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hn]
  have h1 : L / √(L / (k * ((n - 1 : ℕ) + 1))) = √L * √(k * n) := by
    rw [hn1, sqrt_div hL0.le, div_div_eq_mul_div, mul_div_right_comm, div_sqrt]
  -- the second term: `k ∑ t < n, η t / 2 ≤ √(L k) √n`
  have h2 : k * ∑ t ∈ range n, √(L / (k * (t + 1))) / 2 ≤ √(L * k) * √n := by
    simp_rw [hηt, ← Finset.sum_div, ← Finset.mul_sum]
    calc k * ((√(L / k) * ∑ t ∈ range n, (√((t : ℝ) + 1))⁻¹) / 2)
    _ ≤ k * ((√(L / k) * (2 * √n)) / 2) := by
        gcongr
        exact sum_range_inv_sqrt_add_one_le n
    _ = k * √(L / k) * √n := by ring
    _ = √(L * k) * √n := by rw [mul_sqrt_div_eq_sqrt_mul L hk0.le]
  rw [h1]
  calc √L * √(k * n) + k * ∑ t ∈ range n, √(L / (k * (t + 1))) / 2
  _ ≤ √L * √(k * n) + √(L * k) * √n := by gcongr
  _ = 2 * √(n * k * L) := by
      rw [← sqrt_mul hL0.le, ← sqrt_mul (by positivity)]
      ring_nf

end Exp4IX

namespace Exp3

/-- **Pseudo-regret of Exp3** against an adaptive adversary: along a run of Exp3 with learning rate
`η > 0` against any environment whose feedbacks of the rounds `t < n` are almost surely in
`[0, 1]`, the pseudo-regret after `n` rounds is at most `log k / η + η n k / 2`, with `k` the
number of arms. -/
theorem pseudoRegret_le {η₀ : ℝ} (h : IsAlgEnvSeq O A Y (exp3 η₀) env P) (hη : 0 < η₀)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) :
    pseudoRegret env O A Y P n ≤ log (Fintype.card α) / η₀ + η₀ * n * Fintype.card α / 2 := by
  rw [exp3_eq_exp4IX] at h
  refine (Exp4IX.expertPseudoRegret_le h (fun _ ↦ hη) antitone_const (fun _ ↦ le_rfl) hY).trans_eq'
    ?_ |>.trans_eq ?_
  · simp
  · simp only [Pi.zero_apply, zero_add, sum_const, card_range, nsmul_eq_mul]
    ring

/-- **Pseudo-regret of Exp3** [LS, Theorem 11.2] against an adaptive adversary: along a run of
Exp3 with the learning rate `η = √(2 log k / (n k))` tuned for the horizon `n`, against any
environment whose feedbacks of the rounds `t < n` are almost surely in `[0, 1]`, the pseudo-regret
after `n` rounds is at most `√(2 n k log k)`, with `k` the number of arms. -/
theorem pseudoRegret_le_sqrt
    (h : IsAlgEnvSeq O A Y (exp3 √(2 * log (Fintype.card α) / (n * Fintype.card α))) env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) :
    pseudoRegret env O A Y P n ≤ √(2 * n * Fintype.card α * log (Fintype.card α)) := by
  rw [exp3_eq_exp4IX] at h
  simpa using Exp4IX.expertPseudoRegret_le_sqrt h hY

/-- **Pseudo-regret of Exp3 with anytime learning rates** [BCB12, Theorem 3.1] against an adaptive
adversary: along a run of Exp4-IX with the experts `α`, expert `b` advising the Dirac mass at `b`,
`γ = 0` (Exp3) and the learning rates `η t = √(log k / (k (t + 1)))`, against any environment whose
feedbacks of the rounds `t < n` are almost surely in `[0, 1]`, the pseudo-regret after `n` rounds
is at most `2 √(n k log k)`, with `k` the number of arms. -/
theorem pseudoRegret_le_two_mul_sqrt
    (h : IsAlgEnvSeq O A Y (exp4IX (fun _ b ↦ ⟨Pi.single b 1, single_mem_simplex b⟩)
      measurable_const (fun t ↦ √(log (Fintype.card α) / (Fintype.card α * (t + 1)))) 0) env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) :
    pseudoRegret env O A Y P n ≤ 2 * √(n * Fintype.card α * log (Fintype.card α)) := by
  simpa using Exp4IX.expertPseudoRegret_le_two_mul_sqrt h hY

end Exp3

end LMLExplore.Bandits
