/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Real.Sqrt
public import LMLExplore.Bandits.Adversarial.Regret
public import LMLExplore.Bandits.TsallisINF.Basic
public import LMLExplore.OnlineLearning.Tsallis

/-!
# Pseudo-regret of Tsallis-INF against an adaptive adversary

Tsallis-INF (`LMLExplore.Bandits.tsallisINF`) plays against any environment
`env : Environment 𝓞 α ℝ`, whose feedback law at round `t` may depend on the history and on the
observation of round `t`: an adaptive adversary. With `m_t(a) = env.means O A Y a t` the mean
reward of arm `a` at round `t` given the past, its pseudo-regret is
`max_a E[∑_{t < n} (m_t(a) - Y t)]` (`LMLExplore.Bandits.pseudoRegret`). This file proves that for
rewards in `[0, 1]` it is at most `12 √((k - 1) n)`, with `k` the number of arms: the order
`√(k n)` of [ZS21, Theorem 1], here with an explicit constant [Ora, Section 9.3].

The proof follows the regularized leader on the importance-weighted loss estimates
`Ŷ t a = 𝟙{A t = a} (1 - Y t) / P t a`, shifted by the observed loss `1 - Y t` of the played arm.
The shift does not change the weights `P t` of Tsallis-INF
(`tsallisINFWeights_history_eq_add_const`) nor the regret against an arm, and the shifted
estimates are at least `-1`. The local-norm bound of FTRL with the ½-Tsallis potential
(`OnlineLearning.tsallisWeights_regret_le_of_monotone`) then gives the pathwise bound
`∑ t < n, ((1 - Y t) - Ŷ t a)
  ≤ 4 √n (√k - 1) + ∑ t < n, 4 / √(t + 1) * ∑ b, P t b √(P t b) (Ŷ t b - (1 - Y t)) ^ 2`.
Given the past, the shifted estimate of an arm `b` is `(1 - Y t) (𝟙{A t = b} / P t b - 1)`, so the
expected local norm of round `t` is at most `∑ b, √(P t b) (1 - P t b) ≤ √(k - 1)`, by the
Cauchy–Schwarz inequality. The shift is what replaces `k` by `k - 1`. The estimates are
conditionally unbiased, so the expected regret against `a` is the expected estimated regret, and
`∑ t < n, 1 / √(t + 1) ≤ 2 √n`.

## Main statements

* `TsallisINF.sum_one_sub_sub_iwEstimator_le`: the pathwise regret bound on the estimated losses,
  along every sequence of actions and feedbacks in `[0, 1]`.
* `TsallisINF.sum_one_sub_sub_iwEstimator_le_sum_sqrt`: the finer pathwise bound
  `∑ t < n, 4 / √(t + 1) * (∑ b ≠ a', √(P t b) + ∑ b, P t b √(P t b) (Ŷ t b - (1 - Y t)) ^ 2)`,
  for every arm `a'`, which keeps the penalty of each round at its weights.
* `TsallisINF.integral_sum_means_sub_eq_integral_sum_one_sub_sub_iwEstimator`: the expected
  regret against an arm is the expected estimated regret.
* `TsallisINF.integral_sum_mul_sqrt_mul_sq_le_integral_sum_sqrt_mul_one_sub`,
  `TsallisINF.integral_sum_mul_sqrt_mul_sq_le`: the expected local norm of each round is at most
  `E[∑ b, √(P t b) (1 - P t b)]`, hence at most `√(k - 1)`.
* `TsallisINF.pseudoRegret_le`: the pseudo-regret of Tsallis-INF against an adaptive adversary is
  at most `4 √n (√k - 1) + 4 √(k - 1) ∑ t < n, 1 / √(t + 1)`.
* `TsallisINF.pseudoRegret_le_sqrt`: the pseudo-regret is at most `12 √((k - 1) n)`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
* [ZS21] J. Zimmert and Y. Seldin, *Tsallis-INF: an optimal algorithm for stochastic and
  adversarial bandits*, JMLR 22 (2021).
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real

namespace LMLExplore.Bandits

variable {α 𝓞 Ω : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [MeasurableSpace 𝓞]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {env : Environment 𝓞 α ℝ} {n t : ℕ}

namespace TsallisINF

section Path

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] in
/-- Along a run, the weights of Tsallis-INF at round `t` are the Tsallis weights with coefficient
`4 √(t + 1)` of the cumulative importance-weighted estimates shifted by the observed losses,
`Ŷ s b - (1 - Y s)`: the shift does not change the weights. -/
private lemma tsallisINFWeights_history_eq_shift (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) :
    tsallisINFWeights t (history O A Y t ω) = tsallisWeights (4 * √((t : ℝ) + 1))
      (∑ s ∈ range t, fun b ↦
        iwEstimator (tsallisINFWeights s (history O A Y s ω)) (A s ω) (1 - Y s ω) b -
          (1 - Y s ω)) := by
  rw [tsallisINFWeights_history_eq_add_const O A Y (fun s ↦ -(1 - Y s ω)) t ω]
  congr 1
  funext b
  simp only [Finset.sum_apply, sub_eq_add_neg]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] in
/-- For a feedback in `[0, 1]`, the shifted estimates are at least `-1`, hence at least
`-(4 √(t + 1)) / 4`. -/
private lemma neg_le_iwEstimator_sub (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ)
    {ω : Ω} {t : ℕ} (hY : Y t ω ∈ Set.Icc 0 1) (b : α) :
    -(4 * √((t : ℝ) + 1) / 4) ≤
      iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b -
        (1 - Y t ω) := by
  have h0 : 0 ≤ iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b :=
    iwEstimator_nonneg (tsallisINFWeights_pos _ _ _).le (sub_nonneg.2 hY.2)
  have h1 : 1 ≤ √((t : ℝ) + 1) := one_le_sqrt.2 (by linarith [(t.cast_nonneg : (0 : ℝ) ≤ t)])
  linarith [hY.1]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] in
/-- The regret of round `t` of the weights on the shifted estimates against the vertex of `a` is
the estimated regret `(1 - Y t) - Ŷ t a` against `a`: the weights average the shifted estimates
to `0`. -/
private lemma sum_mul_sub_sum_single_mul (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ)
    (ω : Ω) (t : ℕ) (a : α) :
    ∑ b, tsallisINFWeights t (history O A Y t ω) b *
        (iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b -
          (1 - Y t ω)) -
      ∑ b, (Pi.single a 1 : α → ℝ) b *
        (iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b -
          (1 - Y t ω)) =
      (1 - Y t ω) - iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) a
    := by
  set W := tsallisINFWeights t (history O A Y t ω)
  have hpos : W (A t ω) ≠ 0 := (tsallisINFWeights_pos _ _ _).ne'
  have hW1 : ∑ b, W b = 1 := (mem_simplex_iff.1 (tsallisINFWeights_mem_simplex _ _)).2
  have hsum : ∑ b, W b * (iwEstimator W (A t ω) (1 - Y t ω) b - (1 - Y t ω)) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, sum_mul_iwEstimator hpos, hW1, one_mul,
      sub_self]
  rw [hsum]
  simp [Pi.single_apply]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] in
/-- **Pathwise regret of Tsallis-INF on the estimated losses** [ZS21], [Ora, Section 9.3]. Along
every sequence of observations `O`, actions `A` and feedbacks `Y` with `Y t ω ∈ [0, 1]` for
`t < n`, with `P t` the weights of Tsallis-INF and `Ŷ t = iwEstimator (P t) (A t) (1 - Y t)` the
importance-weighted estimates of the losses `1 - Y t`, the estimated regret against every arm `a`
satisfies
`∑ t < n, ((1 - Y t) - Ŷ t a)
  ≤ 4 √n (√k - 1) + ∑ t < n, 4 / √(t + 1) * ∑ b, P t b √(P t b) (Ŷ t b - (1 - Y t)) ^ 2`,
with `k` the number of arms. -/
theorem sum_one_sub_sub_iwEstimator_le (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ)
    (ω : Ω) (hY : ∀ t < n, Y t ω ∈ Set.Icc 0 1) (a : α) :
    ∑ t ∈ range n, ((1 - Y t ω) -
        iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) a) ≤
      4 * √n * (√(Fintype.card α) - 1) + ∑ t ∈ range n, 4 / √((t : ℝ) + 1) *
        ∑ b, tsallisINFWeights t (history O A Y t ω) b *
          √(tsallisINFWeights t (history O A Y t ω) b) *
          (iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b -
            (1 - Y t ω)) ^ 2 := by
  rcases n with _ | m
  · simp
  have hc (t : ℕ) : 0 < 4 * √((t : ℝ) + 1) := by positivity
  have hc_mono : Monotone fun t : ℕ ↦ 4 * √((t : ℝ) + 1) := fun s t hst ↦ by
    have : (s : ℝ) ≤ t := by exact_mod_cast hst
    dsimp only
    gcongr
  have h := OnlineLearning.tsallisWeights_regret_le_of_monotone hc hc_mono
    (fun t ht b ↦ neg_le_iwEstimator_sub O A Y (hY t ht) b) (single_mem_simplex a)
  simp_rw [← tsallisINFWeights_history_eq_shift O A Y ω] at h
  refine (le_of_eq ?_).trans (h.trans_eq ?_)
  · exact sum_congr rfl fun t _ ↦ (sum_mul_sub_sum_single_mul O A Y ω t a).symm
  · -- the penalty term and the coefficients `16 / (4 √(t + 1))`
    have hu : ∑ b, √((Pi.single a 1 : α → ℝ) b) = 1 := by
      simp [Pi.single_apply, apply_ite]
    rw [hu, Nat.add_sub_cancel, Nat.cast_add_one]
    congr 1
    refine sum_congr rfl fun t _ ↦ ?_
    have : 0 < √((t : ℝ) + 1) := by positivity
    field_simp
    ring

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] in
/-- **Pathwise regret of Tsallis-INF on the estimated losses, in terms of the weights of the
other arms** [ZS21], [Ora, Section 9.3]. Along every sequence of observations `O`, actions `A`
and feedbacks `Y` with `Y t ω ∈ [0, 1]` for `t < n`, with `P t` the weights of Tsallis-INF and
`Ŷ t = iwEstimator (P t) (A t) (1 - Y t)` the importance-weighted estimates of the losses
`1 - Y t`, the estimated regret against every arm `a` satisfies, for every arm `a'`,
`∑ t < n, ((1 - Y t) - Ŷ t a)
  ≤ ∑ t < n, 4 / √(t + 1) * (∑ b ≠ a', √(P t b) + ∑ b, P t b √(P t b) (Ŷ t b - (1 - Y t)) ^ 2)`.
The arm `a'` need not be `a`: the penalty of each round is at most its weights `∑ b ≠ a', √(P t b)`
away from any vertex. -/
theorem sum_one_sub_sub_iwEstimator_le_sum_sqrt (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → ℝ) (ω : Ω) (hY : ∀ t < n, Y t ω ∈ Set.Icc 0 1) (a a' : α) :
    ∑ t ∈ range n, ((1 - Y t ω) -
        iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) a) ≤
      ∑ t ∈ range n, 4 / √((t : ℝ) + 1) *
        (∑ b ∈ univ.erase a', √(tsallisINFWeights t (history O A Y t ω) b) +
          ∑ b, tsallisINFWeights t (history O A Y t ω) b *
            √(tsallisINFWeights t (history O A Y t ω) b) *
            (iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b -
              (1 - Y t ω)) ^ 2) := by
  rcases n with _ | m
  · simp
  set W : ℕ → α → ℝ := fun t ↦ tsallisINFWeights t (history O A Y t ω) with hW
  have hc (t : ℕ) : 0 < 4 * √((t : ℝ) + 1) := by positivity
  have h := OnlineLearning.tsallisWeights_regret_succ_le_sum_sub_mul hc
    (fun t ht b ↦ neg_le_iwEstimator_sub O A Y (hY t (Nat.lt_succ_of_le ht)) b)
    (single_mem_simplex a)
  simp_rw [← tsallisINFWeights_history_eq_shift O A Y ω] at h
  have hW0 : tsallisWeights (4 * √(((0 : ℕ) : ℝ) + 1)) (0 : α → ℝ) = W 0 := by
    simp [hW, tsallisINFWeights_history_eq_shift O A Y ω 0]
  have hu : ∑ b, √((Pi.single a 1 : α → ℝ) b) = 1 := by
    simp [Pi.single_apply, apply_ite]
  rw [hW0, hu] at h
  refine (le_of_eq ?_).trans (h.trans ?_)
  · exact sum_congr rfl fun t _ ↦ (sum_mul_sub_sum_single_mul O A Y ω t a).symm
  -- the stability terms have the coefficients `16 / (4 √(t + 1)) = 4 / √(t + 1)`
  have h_stab : ∀ t ∈ range (m + 1), 16 / (4 * √((t : ℝ) + 1)) = 4 / √((t : ℝ) + 1) :=
    fun t _ ↦ by
      have : 0 < √((t : ℝ) + 1) := by positivity
      field_simp
      ring
  simp only [mul_add, sum_add_distrib]
  refine add_le_add ?_ (sum_le_sum fun t ht ↦ by rw [h_stab t ht])
  -- the penalty of round `t` is at most `4 / √(t + 1) * ∑ b ≠ a', √(P t b)`
  have hS (t : ℕ) : ∑ b, √(W t b) - 1 ≤ ∑ b ∈ univ.erase a', √(W t b) :=
    sum_sqrt_sub_one_le_sum_erase (tsallisINFWeights_mem_simplex _ _) a'
  have hS0 (t : ℕ) : 0 ≤ ∑ b ∈ univ.erase a', √(W t b) := sum_nonneg fun _ _ ↦ sqrt_nonneg _
  rw [sum_range_succ']
  refine (add_comm _ _).trans_le (add_le_add (sum_le_sum fun t _ ↦ ?_) ?_)
  · -- `4 (√(t + 2) - √(t + 1)) ≤ 4 / √(t + 2)`
    have h1 : 0 < √((t : ℝ) + 1 + 1) := by positivity
    have h2 : √((t : ℝ) + 1) ≤ √((t : ℝ) + 1 + 1) := sqrt_le_sqrt (by linarith)
    have h3 : √((t : ℝ) + 1 + 1) * √((t : ℝ) + 1 + 1) = (t : ℝ) + 1 + 1 :=
      mul_self_sqrt (by positivity)
    have h4 : √((t : ℝ) + 1) * √((t : ℝ) + 1) = (t : ℝ) + 1 := mul_self_sqrt (by positivity)
    have h_coef : 4 * √((t : ℝ) + 1 + 1) - 4 * √((t : ℝ) + 1) ≤ 4 / √((t : ℝ) + 1 + 1) := by
      rw [le_div_iff₀ h1]
      nlinarith [sqrt_nonneg ((t : ℝ) + 1)]
    push_cast
    calc (4 * √((t : ℝ) + 1 + 1) - 4 * √((t : ℝ) + 1)) * (∑ b, √(W (t + 1) b) - 1)
        ≤ (4 * √((t : ℝ) + 1 + 1) - 4 * √((t : ℝ) + 1)) *
          ∑ b ∈ univ.erase a', √(W (t + 1) b) :=
          mul_le_mul_of_nonneg_left (hS (t + 1)) (by linarith)
      _ ≤ 4 / √((t : ℝ) + 1 + 1) * ∑ b ∈ univ.erase a', √(W (t + 1) b) :=
          mul_le_mul_of_nonneg_right h_coef (hS0 (t + 1))
  · have h0 : 4 * √(((0 : ℕ) : ℝ) + 1) = 4 / √(((0 : ℕ) : ℝ) + 1) := by simp
    rw [h0]
    exact mul_le_mul_of_nonneg_left (hS 0) (by positivity)

end Path

section Expectation

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] in
/-- The local norm `∑ b, p b √(p b) (𝟙{a = b} / p b - 1) ^ 2` of the shifted estimate of a unit
loss when the arm `a` is drawn from the weights `p`. -/
private noncomputable def localNorm (p : α → ℝ) (a : α) : ℝ :=
  ∑ b, p b * √(p b) * (iwEstimator p a 1 b - 1) ^ 2

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] in
/-- The `p`-average of the local norms `localNorm p a` over the drawn arm `a` is
`∑ b, √(p b) (1 - p b)`. -/
private lemma sum_mul_localNorm {p : α → ℝ} (hp : p ∈ simplex α) :
    ∑ a, p a * localNorm p a = ∑ b, √(p b) * (1 - p b) := by
  have hp' := mem_simplex_iff.1 hp
  have h := sum_mul_sum_mul_iwEstimator_apply_sub_sq (x := fun _ ↦ 1) hp'.2
    (f := fun b ↦ p b * √(p b)) fun b hb ↦ by simp [hb]
  simp only [one_pow, one_mul] at h
  simp only [localNorm]
  rw [h]
  refine sum_congr rfl fun b _ ↦ ?_
  rcases (hp'.1 b).eq_or_lt with hb | hb
  · simp [← hb]
  have hs : 0 < √(p b) := sqrt_pos.2 hb
  field_simp

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] in
/-- For a loss `y ∈ [0, 1]`, the local norm of the shifted importance-weighted estimate of `y` is
at most `localNorm p a`. -/
private lemma sum_mul_sqrt_mul_sq_le_localNorm {p : α → ℝ} (hp : ∀ b, 0 ≤ p b) {y : ℝ}
    (hy : y ∈ Set.Icc 0 1) (a : α) :
    ∑ b, p b * √(p b) * (iwEstimator p a y b - y) ^ 2 ≤ localNorm p a := by
  refine sum_le_sum fun b _ ↦ mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hp b) (sqrt_nonneg _))
  have h_eq : iwEstimator p a y b - y = y * (iwEstimator p a 1 b - 1) := by
    simp only [iwEstimator_apply]
    split_ifs <;> ring
  rw [h_eq, mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hy.1 hy.2)

omit [Nonempty α] [MeasurableSpace 𝓞] in
/-- The local norm `localNorm p a` is measurable in `(p, a)`. -/
private lemma measurable_localNorm : Measurable fun z : (α → ℝ) × α ↦ localNorm z.1 z.2 := by
  simp only [localNorm]
  refine Finset.measurable_sum _ fun b _ ↦ ?_
  have hiw : Measurable fun z : (α → ℝ) × α ↦ iwEstimator z.1 z.2 1 :=
    measurable_iwEstimator.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  fun_prop

/-- Along a run of Tsallis-INF, the local norm `localNorm (P t) (A t)` of round `t` is
integrable. -/
private lemma integrable_localNorm (h : IsAlgEnvSeq O A Y tsallisINF env P) (t : ℕ) :
    Integrable (fun ω ↦ localNorm (tsallisINFWeights t (history O A Y t ω)) (A t ω)) P := by
  refine WeightAlgorithm.integrable_comp_weights (isAlgEnvSeq_tsallisINF_iff.1 h) t
    measurable_localNorm
    (C := √((Fintype.card α : ℝ) - 1)) fun p hp ↦ ?_
  have hnn (a : α) : 0 ≤ localNorm p a :=
    sum_nonneg fun b _ ↦ mul_nonneg (mul_nonneg ((mem_simplex_iff.1 hp).1 b) (sqrt_nonneg _))
      (sq_nonneg _)
  simp_rw [abs_of_nonneg (hnn _)]
  rw [sum_mul_localNorm hp]
  exact sum_sqrt_mul_one_sub_le_sqrt hp

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞]
  [IsProbabilityMeasure P] in
/-- Along every sequence of actions and feedbacks, the local norm of round `t` of the shifted
estimates is nonnegative, and at most `localNorm (P t) (A t)` if `Y t ∈ [0, 1]`. -/
private lemma sum_mul_sqrt_mul_sq_run_mem_Icc (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (ω : Ω)
    (hω : Y t ω ∈ Set.Icc 0 1) :
    ∑ b, tsallisINFWeights t (history O A Y t ω) b *
      √(tsallisINFWeights t (history O A Y t ω) b) *
      (iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b -
        (1 - Y t ω)) ^ 2 ∈
      Set.Icc 0 (localNorm (tsallisINFWeights t (history O A Y t ω)) (A t ω)) :=
  ⟨sum_nonneg fun b _ ↦ mul_nonneg (mul_nonneg (tsallisINFWeights_pos _ _ _).le
      (sqrt_nonneg _)) (sq_nonneg _),
    sum_mul_sqrt_mul_sq_le_localNorm (fun b ↦ (tsallisINFWeights_pos _ _ b).le)
      ⟨sub_nonneg.2 hω.2, by linarith [hω.1]⟩ _⟩

/-- Along a run of Tsallis-INF whose feedback at round `t` is almost surely in `[0, 1]`, with `P t`
the weights and `Ŷ t` the importance-weighted estimates of the losses `1 - Y t`, the local norm
`∑ b, P t b √(P t b) (Ŷ t b - (1 - Y t)) ^ 2` of the estimates shifted by the observed loss is
integrable. -/
theorem integrable_sum_mul_sqrt_mul_sq (h : IsAlgEnvSeq O A Y tsallisINF env P)
    (hY : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1) :
    Integrable (fun ω ↦ ∑ b, tsallisINFWeights t (history O A Y t ω) b *
      √(tsallisINFWeights t (history O A Y t ω) b) *
      (iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b -
        (1 - Y t ω)) ^ 2) P := by
  have hm : Measurable fun ω ↦ ∑ b, tsallisINFWeights t (history O A Y t ω) b *
      √(tsallisINFWeights t (history O A Y t ω) b) *
      (iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b -
        (1 - Y t ω)) ^ 2 := by
    have hW : Measurable fun ω ↦ tsallisINFWeights t (history O A Y t ω) :=
      WeightAlgorithm.measurable_weights_run (isAlgEnvSeq_tsallisINF_iff.1 h) t
    have hiw : Measurable fun ω ↦
        iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) :=
      WeightAlgorithm.measurable_iwEstimator_run (isAlgEnvSeq_tsallisINF_iff.1 h)
        (measurable_const.sub (h.measurable_feedback t))
    have hYt := h.measurable_feedback t
    fun_prop
  refine (integrable_localNorm h t).mono' hm.aestronglyMeasurable ?_
  filter_upwards [hY] with ω hω
  have h_mem := sum_mul_sqrt_mul_sq_run_mem_Icc O A ω hω
  rw [Real.norm_of_nonneg h_mem.1]
  exact h_mem.2

/-- **The expected local norm of a round of Tsallis-INF.** Along a run of Tsallis-INF whose
feedback at round `t` is almost surely in `[0, 1]`, with `P t` the weights and `Ŷ t` the
importance-weighted estimates of the losses `1 - Y t`, the local norm
`∑ b, P t b √(P t b) (Ŷ t b - (1 - Y t)) ^ 2` of the estimates shifted by the observed loss has
expectation at most `E[∑ b, √(P t b) (1 - P t b)]`. -/
theorem integral_sum_mul_sqrt_mul_sq_le_integral_sum_sqrt_mul_one_sub
    (h : IsAlgEnvSeq O A Y tsallisINF env P) (hY : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1) :
    P[fun ω ↦ ∑ b, tsallisINFWeights t (history O A Y t ω) b *
      √(tsallisINFWeights t (history O A Y t ω) b) *
      (iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b -
        (1 - Y t ω)) ^ 2] ≤
      P[fun ω ↦ ∑ b, √(tsallisINFWeights t (history O A Y t ω) b) *
        (1 - tsallisINFWeights t (history O A Y t ω) b)] := by
  -- the local norm is dominated by its value `localNorm (P t) (A t)` for a unit loss
  have h1 := integral_mono_of_nonneg (μ := P)
    (g := fun ω ↦ localNorm (tsallisINFWeights t (history O A Y t ω)) (A t ω))
    (by filter_upwards [hY] with ω hω using (sum_mul_sqrt_mul_sq_run_mem_Icc O A ω hω).1)
    (integrable_localNorm h t)
    (by filter_upwards [hY] with ω hω using (sum_mul_sqrt_mul_sq_run_mem_Icc O A ω hω).2)
  -- whose expectation is that of `∑ b, √(P t b) (1 - P t b) ≤ √(k - 1)`
  rw [WeightAlgorithm.integral_comp_weights (isAlgEnvSeq_tsallisINF_iff.1 h) t measurable_localNorm
    (integrable_localNorm h t)] at h1
  simpa only [sum_mul_localNorm (tsallisINFWeights_mem_simplex _ _)] using h1

/-- **The expected local norm of a round of Tsallis-INF.** Along a run of Tsallis-INF whose
feedback at round `t` is almost surely in `[0, 1]`, with `P t` the weights and `Ŷ t` the
importance-weighted estimates of the losses `1 - Y t`, the local norm
`∑ b, P t b √(P t b) (Ŷ t b - (1 - Y t)) ^ 2` of the estimates shifted by the observed loss has
expectation at most `√(k - 1)`, with `k` the number of arms. -/
theorem integral_sum_mul_sqrt_mul_sq_le (h : IsAlgEnvSeq O A Y tsallisINF env P)
    (hY : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1) :
    P[fun ω ↦ ∑ b, tsallisINFWeights t (history O A Y t ω) b *
      √(tsallisINFWeights t (history O A Y t ω) b) *
      (iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b -
        (1 - Y t ω)) ^ 2] ≤ √((Fintype.card α : ℝ) - 1) := by
  refine (integral_sum_mul_sqrt_mul_sq_le_integral_sum_sqrt_mul_one_sub h hY).trans ?_
  refine (integral_mono_of_nonneg (ae_of_all _ fun ω ↦ ?_)
    (integrable_const (√((Fintype.card α : ℝ) - 1)))
    (ae_of_all _ fun ω ↦ sum_sqrt_mul_one_sub_le_sqrt (tsallisINFWeights_mem_simplex _ _))).trans
    (by simp)
  exact sum_nonneg fun b _ ↦ mul_nonneg (sqrt_nonneg _)
    (sub_nonneg.2 ((simplex_subset_Icc (tsallisINFWeights_mem_simplex _ _)).2 b))

/-- **The expected regret of Tsallis-INF is its expected estimated regret.** Along a run of
Tsallis-INF against any environment whose feedbacks of the rounds `t < n` are almost surely in
`[0, 1]`, with `m t a = env.means O A Y a t` the conditional means of the rewards and `Ŷ t` the
importance-weighted estimates of the losses `1 - Y t`, the expected regret against every arm `a`
is `E[∑ t < n, (m t a - Y t)] = E[∑ t < n, ((1 - Y t) - Ŷ t a)]`, by the conditional
unbiasedness of the estimates. -/
theorem integral_sum_means_sub_eq_integral_sum_one_sub_sub_iwEstimator
    (h : IsAlgEnvSeq O A Y tsallisINF env P) (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1)
    (a : α) :
    P[fun ω ↦ ∑ t ∈ range n, (env.means O A Y a t ω - Y t ω)] =
      P[fun ω ↦ ∑ t ∈ range n, ((1 - Y t ω) -
        iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) a)] := by
  have hYt (t : ℕ) (ht : t ∈ range n) : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1 :=
    hY.mono fun _ hω ↦ hω t (mem_range.1 ht)
  have hYint (t : ℕ) (ht : t ∈ range n) : Integrable (fun ω ↦ 1 - Y t ω) P :=
    (integrable_const 1).sub
      (Integrable.of_mem_Icc 0 1 (h.measurable_feedback t).aemeasurable (hYt t ht))
  have hLint (t : ℕ) (ht : t ∈ range n) :=
    WeightAlgorithm.integrable_iwEstimator_one_sub (isAlgEnvSeq_tsallisINF_iff.1 h) (hYt t ht) a
  have hMint (t : ℕ) (ht : t ∈ range n) : Integrable (fun ω ↦ 1 - env.means O A Y a t ω) P :=
    WeightAlgorithm.integrable_one_sub_means (isAlgEnvSeq_tsallisINF_iff.1 h) (hYt t ht)
      (ae_of_all _ fun ω ↦ tsallisINFWeights_pos _ _ a)
  calc P[fun ω ↦ ∑ t ∈ range n, (env.means O A Y a t ω - Y t ω)]
  _ = ∑ t ∈ range n, (P[fun ω ↦ 1 - Y t ω] - P[fun ω ↦ 1 - env.means O A Y a t ω]) := by
      rw [integral_finsetSum _ fun t ht ↦ ((hYint t ht).sub (hMint t ht)).congr
        (ae_of_all _ fun ω ↦ by simp only [Pi.sub_apply]; ring)]
      refine sum_congr rfl fun t ht ↦ ?_
      rw [← integral_sub (hYint t ht) (hMint t ht)]
      exact integral_congr_ae (ae_of_all _ fun ω ↦ by simp only; ring)
  _ = ∑ t ∈ range n, (P[fun ω ↦ 1 - Y t ω] - P[fun ω ↦
        iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) a]) :=
      sum_congr rfl fun t ht ↦ by
        rw [WeightAlgorithm.integral_iwEstimator_one_sub (isAlgEnvSeq_tsallisINF_iff.1 h)
          (hYt t ht) (ae_of_all _ fun ω ↦ tsallisINFWeights_pos _ _ a)]
  _ = P[fun ω ↦ ∑ t ∈ range n, ((1 - Y t ω) -
        iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) a)] := by
      rw [integral_finsetSum (f := fun t ω ↦ (1 - Y t ω) -
        iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) a) _
        fun t ht ↦ (hYint t ht).sub (hLint t ht)]
      exact sum_congr rfl fun t ht ↦ (integral_sub (hYint t ht) (hLint t ht)).symm

/-- **Pseudo-regret of Tsallis-INF against an adaptive adversary** [ZS21], [Ora, Section 9.3].
Along a run of Tsallis-INF against any environment whose feedbacks of the rounds `t < n` are
almost surely in `[0, 1]`, the pseudo-regret after `n` rounds is at most
`4 √n (√k - 1) + 4 √(k - 1) ∑ t < n, 1 / √(t + 1)`, with `k` the number of arms. -/
theorem pseudoRegret_le (h : IsAlgEnvSeq O A Y tsallisINF env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) :
    pseudoRegret env O A Y P n ≤ 4 * √n * (√(Fintype.card α) - 1) +
      4 * √((Fintype.card α : ℝ) - 1) * ∑ t ∈ range n, (√((t : ℝ) + 1))⁻¹ := by
  refine pseudoRegret_le_iff.2 fun a ↦ ?_
  have hYt (t : ℕ) (ht : t ∈ range n) : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1 :=
    hY.mono fun _ hω ↦ hω t (mem_range.1 ht)
  have hYint (t : ℕ) (ht : t ∈ range n) : Integrable (fun ω ↦ 1 - Y t ω) P :=
    (integrable_const 1).sub
      (Integrable.of_mem_Icc 0 1 (h.measurable_feedback t).aemeasurable (hYt t ht))
  have hLint (t : ℕ) (ht : t ∈ range n) :=
    WeightAlgorithm.integrable_iwEstimator_one_sub (isAlgEnvSeq_tsallisINF_iff.1 h) (hYt t ht) a
  have hVint (t : ℕ) (ht : t ∈ range n) := integrable_sum_mul_sqrt_mul_sq (t := t) h (hYt t ht)
  rw [integral_sum_means_sub_eq_integral_sum_one_sub_sub_iwEstimator h hY a]
  calc P[fun ω ↦ ∑ t ∈ range n, ((1 - Y t ω) -
        iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) a)]
  -- take expectations in the pathwise bound
  _ ≤ P[fun ω ↦ 4 * √n * (√(Fintype.card α) - 1) + ∑ t ∈ range n, 4 / √((t : ℝ) + 1) *
        ∑ b, tsallisINFWeights t (history O A Y t ω) b *
          √(tsallisINFWeights t (history O A Y t ω) b) *
          (iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b -
            (1 - Y t ω)) ^ 2] := by
      refine integral_mono_ae (integrable_finsetSum _ fun t ht ↦ (hYint t ht).sub (hLint t ht))
        ((integrable_const _).add (integrable_finsetSum _ fun t ht ↦ (hVint t ht).const_mul _)) ?_
      filter_upwards [hY] with ω hω using sum_one_sub_sub_iwEstimator_le O A Y ω hω a
  _ = 4 * √n * (√(Fintype.card α) - 1) + ∑ t ∈ range n, 4 / √((t : ℝ) + 1) *
        P[fun ω ↦ ∑ b, tsallisINFWeights t (history O A Y t ω) b *
          √(tsallisINFWeights t (history O A Y t ω) b) *
          (iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b -
            (1 - Y t ω)) ^ 2] := by
      rw [integral_add (integrable_const _)
          (integrable_finsetSum _ fun t ht ↦ (hVint t ht).const_mul _),
        integral_finsetSum _ fun t ht ↦ (hVint t ht).const_mul _, integral_const, probReal_univ,
        one_smul]
      simp only [integral_const_mul]
  -- the expected local norms are at most `√(k - 1)`
  _ ≤ 4 * √n * (√(Fintype.card α) - 1) +
        ∑ t ∈ range n, 4 / √((t : ℝ) + 1) * √((Fintype.card α : ℝ) - 1) := by
      gcongr with t ht
      exact integral_sum_mul_sqrt_mul_sq_le h (hYt t ht)
  _ = 4 * √n * (√(Fintype.card α) - 1) +
        4 * √((Fintype.card α : ℝ) - 1) * ∑ t ∈ range n, (√((t : ℝ) + 1))⁻¹ := by
      rw [mul_sum]
      congr 1
      exact sum_congr rfl fun t _ ↦ by ring

/-- **Pseudo-regret of Tsallis-INF against an adaptive adversary**, of the order `√(k n)` of
[ZS21, Theorem 1]: along a run of Tsallis-INF against any environment whose feedbacks of the
rounds `t < n` are almost surely in `[0, 1]`, the pseudo-regret after `n` rounds is at most
`12 √((k - 1) n)`, with `k` the number of arms. The learning rates of Tsallis-INF do not depend
on the horizon, so the bound holds for every `n`. -/
theorem pseudoRegret_le_sqrt (h : IsAlgEnvSeq O A Y tsallisINF env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) :
    pseudoRegret env O A Y P n ≤ 12 * √(((Fintype.card α : ℝ) - 1) * n) := by
  have hk : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hk1 : 0 ≤ (Fintype.card α : ℝ) - 1 := by linarith
  -- `√k - 1 ≤ √(k - 1)`
  have h_sqrt : √(Fintype.card α) - 1 ≤ √((Fintype.card α : ℝ) - 1) := by
    have h : √(Fintype.card α) ≤ √((Fintype.card α : ℝ) - 1) + 1 :=
      (sqrt_le_left (by positivity)).2
        (by nlinarith [sq_sqrt hk1, sqrt_nonneg ((Fintype.card α : ℝ) - 1)])
    linarith
  refine (pseudoRegret_le h hY).trans ?_
  calc 4 * √n * (√(Fintype.card α) - 1) +
        4 * √((Fintype.card α : ℝ) - 1) * ∑ t ∈ range n, (√((t : ℝ) + 1))⁻¹
  _ ≤ 4 * √n * √((Fintype.card α : ℝ) - 1) +
        4 * √((Fintype.card α : ℝ) - 1) * (2 * √n) := by
      gcongr
      exact sum_range_inv_sqrt_add_one_le n
  _ = 12 * √(((Fintype.card α : ℝ) - 1) * n) := by
      rw [sqrt_mul hk1]
      ring

end Expectation

end TsallisINF

end LMLExplore.Bandits
