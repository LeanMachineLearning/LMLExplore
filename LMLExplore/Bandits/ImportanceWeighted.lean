/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.WeightAlgorithm

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
conditional statements are given the σ-algebra `h.filtrationObs n` of the past. They assume that
the feedback `Y n` of round `n` is almost surely the reward `x (A n)` of the action, as for runs
against LML's `onlineEvalEnv g _` with `x = g n` (`feedback_onlineEvalEnv_ae_eq_eval_action`) and
against `Environment.ofSeq o g _` with expert advice `o` (`IsAlgEnvSeq.feedback_ofSeq_ae_eq`).

## Main definitions

* `LMLExplore.Bandits.iwEstimator p b y`: the vector `a ↦ 𝟙{b = a} y / p a`.
* `LMLExplore.Bandits.lossIwEstimator p b y`: the vector `a ↦ 1 - 𝟙{b = a} (1 - y) / p a`.

## Main statements

* `sum_mul_iwEstimator_apply`, `sum_mul_lossIwEstimator_apply`: averaged over the drawn arm
  `b ∼ p`, the estimates of the reward `x a` are equal to `x a` when `p a ≠ 0`.
* `sum_mul_iwEstimator_apply_sub_sq`, `sum_mul_lossIwEstimator_apply_sub_sq`: the corresponding
  variances.
* `lossIwEstimator_le_one`: the loss-based estimates are at most `1` for rewards at most `1`.
* `comp_feedback_ae_eq`: when the feedback `Y n` is almost surely `x (A n)`, it can be replaced
  by `x (A n)` in any function of the past, the action and the feedback of round `n`.
* `WeightAlgorithm.condExp_iwEstimator`, `WeightAlgorithm.condExp_lossIwEstimator`: conditional
  unbiasedness along a run of a weight-based algorithm [LS, (11.4)].
* `WeightAlgorithm.integral_iwEstimator`, `WeightAlgorithm.integral_lossIwEstimator`: the
  estimates are unbiased.
* `WeightAlgorithm.condVar_iwEstimator`, `WeightAlgorithm.condVar_lossIwEstimator`: the
  conditional variances [LS, (11.5)].

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset

namespace LMLExplore.Bandits

variable {α : Type*} [DecidableEq α] {p x : α → ℝ} {a b : α} {y : ℝ}

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

@[simp]
lemma iwEstimator_apply_self : iwEstimator p b y b = y / p b := by simp [iwEstimator_def]

@[simp]
lemma iwEstimator_apply_of_ne (h : a ≠ b) : iwEstimator p b y a = 0 := by
  simp [iwEstimator_def, h]

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

variable [Nonempty α]

/-- **Conditional unbiasedness of the importance-weighted estimator** [LS, (11.4)]: along a run of
a weight-based algorithm whose feedback at round `n` is the reward `x (A n)` of the action, the
importance-weighted estimate of the reward of an arm `a` that has almost surely positive weight
has conditional expectation `x a` given the past. -/
theorem condExp_iwEstimator (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : Y n =ᵐ[P] x ∘ A n) (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a) :
    P[fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a
      | h.filtrationObs n] =ᵐ[P] fun _ ↦ x a := by
  have hcongr := comp_feedback_ae_eq (O := O) hY fun z b y ↦ iwEstimator (w n z) b y a
  refine (condExp_congr_ae hcongr).trans ?_
  filter_upwards [condExp_comp_weights h n (g := fun p b ↦ iwEstimator p b (x b) a)
    (by fun_prop) ((integrable_iwEstimator h hY a).congr hcongr), ha] with ω hω hωa
  rw [hω]
  exact sum_mul_iwEstimator_apply hωa.ne'

/-- **Conditional unbiasedness of the loss-based importance-weighted estimator** [LS, Section 11.2]:
along a run of a weight-based algorithm whose feedback at round `n` is the reward `x (A n)` of the
action, the loss-based importance-weighted estimate of the reward of an arm `a` that has almost
surely positive weight has conditional expectation `x a` given the past. -/
theorem condExp_lossIwEstimator (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : Y n =ᵐ[P] x ∘ A n) (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a) :
    P[fun ω ↦ lossIwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a
      | h.filtrationObs n] =ᵐ[P] fun _ ↦ x a := by
  have hcongr := comp_feedback_ae_eq (O := O) hY fun z b y ↦ lossIwEstimator (w n z) b y a
  refine (condExp_congr_ae hcongr).trans ?_
  filter_upwards [condExp_comp_weights h n (g := fun p b ↦ lossIwEstimator p b (x b) a)
    (by fun_prop) ((integrable_lossIwEstimator h hY a).congr hcongr), ha] with ω hω hωa
  rw [hω]
  exact sum_mul_lossIwEstimator_apply (mem_simplex_iff.1 (hp n _)).2 hωa.ne'

/-- Along a run of a weight-based algorithm whose feedback at round `n` is the reward `x (A n)` of
the action, the importance-weighted estimate of the reward of an arm `a` that has almost surely
positive weight has expectation `x a`. -/
theorem integral_iwEstimator [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : Y n =ᵐ[P] x ∘ A n) (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a) :
    P[fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a] = x a := by
  rw [← integral_condExp (h.filtrationObs.le n), integral_congr_ae (condExp_iwEstimator h hY ha)]
  simp

/-- Along a run of a weight-based algorithm whose feedback at round `n` is the reward `x (A n)` of
the action, the loss-based importance-weighted estimate of the reward of an arm `a` that has almost
surely positive weight has expectation `x a`. -/
theorem integral_lossIwEstimator [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : Y n =ᵐ[P] x ∘ A n) (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a) :
    P[fun ω ↦ lossIwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a] = x a := by
  rw [← integral_condExp (h.filtrationObs.le n),
    integral_congr_ae (condExp_lossIwEstimator h hY ha)]
  simp

omit [Nonempty α] in
/-- For `q` almost surely nonzero with `q⁻¹` integrable, `c * (1 - q) / q` is integrable. -/
private lemma integrable_mul_one_sub_div {q : Ω → ℝ} (hq : ∀ᵐ ω ∂P, q ω ≠ 0)
    (hint : Integrable (fun ω ↦ (q ω)⁻¹) P) (c : ℝ) :
    Integrable (fun ω ↦ c * (1 - q ω) / q ω) P := by
  refine ((hint.sub (integrable_const 1)).const_mul c).congr ?_
  filter_upwards [hq] with ω hω
  simp only [Pi.sub_apply]
  field_simp

/-- **Conditional variance of the importance-weighted estimator** [LS, (11.5)]: along a run of a
weight-based algorithm whose feedback at round `n` is the reward `x (A n)` of the action, the
importance-weighted estimate of the reward of an arm `a` with almost surely positive weight `P_a`
has conditional variance `x a ^ 2 * (1 - P_a) / P_a` given the past, when `1 / P_a` is
integrable. -/
theorem condVar_iwEstimator (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : Y n =ᵐ[P] x ∘ A n) (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a)
    (hint : Integrable (fun ω ↦ (w n (history O A Y n ω, O n ω) a)⁻¹) P) :
    Var[fun ω ↦ iwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a;
      P | h.filtrationObs n] =ᵐ[P] fun ω ↦
        x a ^ 2 * (1 - w n (history O A Y n ω, O n ω) a) / w n (history O A Y n ω, O n ω) a := by
  have hsum : ∀ᵐ ω ∂P, ∑ b, w n (history O A Y n ω, O n ω) b *
      (iwEstimator (w n (history O A Y n ω, O n ω)) b (x b) a - x a) ^ 2 =
        x a ^ 2 * (1 - w n (history O A Y n ω, O n ω) a) / w n (history O A Y n ω, O n ω) a := by
    filter_upwards [ha] with ω hωa
    exact sum_mul_iwEstimator_apply_sub_sq (mem_simplex_iff.1 (hp n _)).2 hωa.ne'
  refine (condVar_comp_weights h n (g := fun p b ↦ iwEstimator p b (x b) a) (by fun_prop)
    (comp_feedback_ae_eq hY fun z b y ↦ iwEstimator (w n z) b y a)
    (condExp_iwEstimator h hY ha) ?_).trans hsum
  exact (integrable_mul_one_sub_div (ha.mono fun _ h ↦ h.ne') hint (x a ^ 2)).congr
    (hsum.mono fun _ h ↦ h.symm)

/-- **Conditional variance of the loss-based importance-weighted estimator** [LS, Section 11.2]:
along a run of a weight-based algorithm whose feedback at round `n` is the reward `x (A n)` of the
action, the loss-based importance-weighted estimate of the reward of an arm `a` with almost surely
positive weight `P_a` has conditional variance `(1 - x a) ^ 2 * (1 - P_a) / P_a` given the past,
when `1 / P_a` is integrable. -/
theorem condVar_lossIwEstimator (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (hY : Y n =ᵐ[P] x ∘ A n) (ha : ∀ᵐ ω ∂P, 0 < w n (history O A Y n ω, O n ω) a)
    (hint : Integrable (fun ω ↦ (w n (history O A Y n ω, O n ω) a)⁻¹) P) :
    Var[fun ω ↦ lossIwEstimator (w n (history O A Y n ω, O n ω)) (A n ω) (Y n ω) a;
      P | h.filtrationObs n] =ᵐ[P] fun ω ↦ (1 - x a) ^ 2 *
        (1 - w n (history O A Y n ω, O n ω) a) / w n (history O A Y n ω, O n ω) a := by
  have hsum : ∀ᵐ ω ∂P, ∑ b, w n (history O A Y n ω, O n ω) b *
      (lossIwEstimator (w n (history O A Y n ω, O n ω)) b (x b) a - x a) ^ 2 = (1 - x a) ^ 2 *
        (1 - w n (history O A Y n ω, O n ω) a) / w n (history O A Y n ω, O n ω) a := by
    filter_upwards [ha] with ω hωa
    exact sum_mul_lossIwEstimator_apply_sub_sq (mem_simplex_iff.1 (hp n _)).2 hωa.ne'
  refine (condVar_comp_weights h n (g := fun p b ↦ lossIwEstimator p b (x b) a) (by fun_prop)
    (comp_feedback_ae_eq hY fun z b y ↦ lossIwEstimator (w n z) b y a)
    (condExp_lossIwEstimator h hY ha) ?_).trans hsum
  exact (integrable_mul_one_sub_div (ha.mono fun _ h ↦ h.ne') hint ((1 - x a) ^ 2)).congr
    (hsum.mono fun _ h ↦ h.symm)

end WeightAlgorithm

end LMLExplore.Bandits
