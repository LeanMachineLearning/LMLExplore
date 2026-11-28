/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.SequentialLearning.LikelihoodRatio
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.StrongLaw
import LMLExplore.Probability.Moments.SubGaussian.Basic
import LMLExplore.Probability.StrongLaw

/-!
# A weak law of large numbers along bandit runs, uniform in the algorithm

Run any algorithm against a stochastic bandit `ν` with finitely many arms, and let `z a y` be a
function of the arm and of the observation, integrable under every arm law `ν a`, with means
`m a = ∫ z a dν a`. The centred sums `∑_{t < n} (z(A_t, Y_t) - m(A_t))` are a martingale, and
they are `o(T)` up to the horizon `T` with probability tending to `1`, at a rate that depends on
`ν` and `z` only: for every `ε > 0`, the probability that `∑_{t < n} (z(A_t, Y_t) - m(A_t))`
exceeds `ε T` for some `n ≤ T` tends to `0` as `T → ∞`, uniformly over the algorithms. No moment
beyond the first is assumed.

The proof truncates `z` at a level `M`, with Mathlib's truncation `z_M = truncation (z a) M`, which
is `z` on `(-M, M]` and `0` elsewhere. The truncated part has sub-Gaussian increments, and a
time-uniform Hoeffding inequality (from the likelihood ratio supermartingales of
`SequentialLearning/LikelihoodRatio.lean` and Ville's inequality) bounds its deviations by
`exp (-ε² T / (8 M²))`. The remainder has expectation at most `2 T ∑_a E_{ν a}|z - z_M|` along
every run, and Markov's inequality bounds it by `4 / ε ∑_a E_{ν a}|z - z_M|`, which tends to `0`
as `M → ∞` (`ProbabilityTheory.tendsto_integral_abs_sub_truncation`).

For `z` the log-likelihood ratio of `ν` against another bandit, `m a` is the relative entropy of the
arm `a`, and this is the concentration of the log-likelihood ratio of the history on which the
lower bound of identification with several correct answers rests [DK19, Lemma 19]; Degenne and
Koolen assume sub-Gaussian arms and apply the Hoeffding–Azuma inequality directly.

## Main statements

* `Learning.IsAlgEnvSeq.lintegral_comp_action_feedback_bandit`: the expectation of a function of
  the action and the observation of a round is that of its integral against the arm law.
* `Learning.IsAlgEnvSeq.measure_exists_le_lt_sum_le_of_hasSubgaussianMGF`: Hoeffding's inequality
  up to a horizon, for sub-Gaussian functions of the observations.
* `Learning.IsAlgEnvSeq.measure_exists_le_mul_lt_sum_sub_integral_le`: the bound
  `exp (-ε² T / (8 M²)) + 4 / ε ∑_a E_{ν a}|z - z_M|` on the probability of a deviation `ε T` of
  the centred sums before the horizon `T`, for every level of truncation `M`.
* `LMLExplore.eventually_measure_exists_le_mul_lt_sum_sub_integral_le`: the weak law, uniformly over
  the algorithms and the runs.

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, supplementary material, Appendix C.4, Lemma 19.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real Filter

open scoped ENNReal NNReal Topology

namespace Learning

open LMLExplore

variable {α 𝓨 Ω : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm Unit α 𝓨}
  {ν : Kernel α 𝓨} [IsMarkovKernel ν] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨}

/-- Along a run against the stochastic bandit `ν`, the expectation of a function `f ≥ 0` of the
action and the observation of round `t` is the expectation of its integral against the law of the
observations of the action. -/
lemma IsAlgEnvSeq.lintegral_comp_action_feedback_bandit
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) {f : α × 𝓨 → ℝ≥0∞} (hf : Measurable f)
    (t : ℕ) :
    ∫⁻ ω, f (A t ω, Y t ω) ∂P = ∫⁻ ω, ∫⁻ y, f (A t ω, y) ∂ν (A t ω) ∂P := by
  rw [(h.hasCondDistrib_feedback_bandit t).lintegral_comp hf.aemeasurable,
    Measure.lintegral_compProd hf, lintegral_map (hf.lintegral_kernel_prod_right' (κ := ν))
      (h.measurable_action t)]

/-- **Hoeffding's inequality up to a horizon along a bandit run.** Along a run of any algorithm
against the stochastic bandit `ν`, let `g a y` be a function of the arm and the observation that is
`c`-sub-Gaussian under every arm law `ν a`. For `x > 0` and a horizon `T ≥ 1`, the probability that
`∑_{t < n} g(A_t, Y_t)` exceeds `x` for some `n ≤ T` is at most `exp (-x² / (2 c T))`. -/
theorem IsAlgEnvSeq.measure_exists_le_lt_sum_le_of_hasSubgaussianMGF
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) {g : α → 𝓨 → ℝ}
    (hg : Measurable (Function.uncurry g)) {c : ℝ≥0} (hc : 0 < c)
    (hgc : ∀ a, HasSubgaussianMGF (g a) c (ν a)) {x : ℝ} (hx : 0 < x) {T : ℕ} (hT : 0 < T) :
    P {ω | ∃ n ≤ T, x < ∑ t ∈ range n, g (A t ω) (Y t ω)} ≤
      ENNReal.ofReal (exp (-(x ^ 2 / (2 * c * T)))) := by
  have hc' : (0 : ℝ) < c := hc
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  -- the exponential supermartingale `exp (s ∑ g - n c s² / 2)` with `s = x / (c T)`
  set s : ℝ := x / (c * T) with hs
  set z : α → 𝓨 → ℝ := fun a y ↦ s * g a y - c * s ^ 2 / 2 with hz
  have hzm : Measurable (Function.uncurry z) :=
    (hg.const_mul s).sub_const _
  have hle (a : α) : ∫⁻ y, ENNReal.ofReal (exp (z a y)) ∂ν a ≤ 1 :=
    (ofReal_integral_eq_lintegral_ofReal ((hgc a).integrable_exp_mul_sub s)
      (ae_of_all _ fun _ ↦ (exp_pos _).le)).symm.trans_le
        (ENNReal.ofReal_le_one.2 ((hgc a).integral_exp_mul_sub_le_one s))
  have hsup := supermartingale_exp_sum_of_lintegral_exp_le_one h hzm hle
  set κ : ℝ := x ^ 2 / (2 * c * T) with hκ
  -- on the event, the supermartingale exceeds `exp κ` at the round `n`
  have h_sub : {ω | ∃ n ≤ T, x < ∑ t ∈ range n, g (A t ω) (Y t ω)} ⊆
      {ω | ∃ n, exp κ ≤ exp (∑ k ∈ range n, z (A k ω) (Y k ω))} := by
    rintro ω ⟨n, hnT, hn⟩
    refine ⟨n, exp_le_exp.2 ?_⟩
    have hsum : ∑ k ∈ range n, z (A k ω) (Y k ω) =
        s * ∑ k ∈ range n, g (A k ω) (Y k ω) - n * (c * s ^ 2 / 2) := by
      simp only [hz, sum_sub_distrib, mul_sum, sum_const, card_range, nsmul_eq_mul]
    have hn' : (n : ℝ) ≤ T := by exact_mod_cast hnT
    have hs0 : 0 < s := div_pos hx (mul_pos hc' hT')
    have hκ_eq : κ = s * x - T * (c * s ^ 2 / 2) := by
      rw [hκ, hs]
      field_simp
      ring
    rw [hsum, hκ_eq]
    nlinarith [mul_lt_mul_of_pos_left hn hs0, mul_le_mul_of_nonneg_right hn'
      (by positivity : 0 ≤ c * s ^ 2 / 2)]
  calc P {ω | ∃ n ≤ T, x < ∑ t ∈ range n, g (A t ω) (Y t ω)}
  _ ≤ P {ω | ∃ n, exp κ ≤ exp (∑ k ∈ range n, z (A k ω) (Y k ω))} := measure_mono h_sub
  _ ≤ ENNReal.ofReal ((P[fun ω ↦ exp (∑ k ∈ range 0, z (A k ω) (Y k ω))]) / exp κ) :=
      hsup.measure_exists_le_le (fun n ↦ ae_of_all _ fun _ ↦ (exp_pos _).le) (exp_pos κ)
  _ = ENNReal.ofReal (exp (-κ)) := by simp [exp_neg]

variable [Fintype α] [MeasurableSingletonClass α]

omit [MeasurableSingletonClass α] in
/-- Along a run against the stochastic bandit `ν`, for a function `d ≥ 0` of the arm and the
observation, integrable under every arm law, `E[d(A_t, Y_t) + E_{ν(A_t)}[d]] ≤ 2 ∑_a E_{ν a}[d]`. -/
private lemma IsAlgEnvSeq.lintegral_ofReal_add_ofReal_integral_le
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) {d : α → 𝓨 → ℝ}
    (hdm : Measurable (Function.uncurry d)) (hd0 : ∀ a y, 0 ≤ d a y)
    (hdint : ∀ a, Integrable (d a) (ν a)) (t : ℕ) :
    ∫⁻ ω, (ENNReal.ofReal (d (A t ω) (Y t ω)) +
        ENNReal.ofReal (∫ y, d (A t ω) y ∂ν (A t ω))) ∂P ≤
      2 * ENNReal.ofReal (∑ a, ∫ y, d a y ∂ν a) := by
  have hr0 (a : α) : 0 ≤ ∫ y, d a y ∂ν a := integral_nonneg (hd0 a)
  -- `E[d(A_t, Y_t)] = E[E_{ν(A_t)}[d]]`
  have hdA : ∫⁻ ω, ENNReal.ofReal (d (A t ω) (Y t ω)) ∂P =
      ∫⁻ ω, ENNReal.ofReal (∫ y, d (A t ω) y ∂ν (A t ω)) ∂P := by
    rw [h.lintegral_comp_action_feedback_bandit
      (f := fun p ↦ ENNReal.ofReal (d p.1 p.2)) (ENNReal.measurable_ofReal.comp hdm) t]
    refine lintegral_congr fun ω ↦ ?_
    exact (ofReal_integral_eq_lintegral_ofReal (hdint _) (ae_of_all _ (hd0 _))).symm
  -- `E_{ν(A_t)}[d] ≤ ∑_a E_{ν a}[d]`
  have hrA : ∫⁻ ω, ENNReal.ofReal (∫ y, d (A t ω) y ∂ν (A t ω)) ∂P ≤
      ENNReal.ofReal (∑ a, ∫ y, d a y ∂ν a) := by
    refine (lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal
      (single_le_sum (fun a _ ↦ hr0 a) (mem_univ (A t ω)))).trans ?_
    simp
  have hdAm : Measurable fun ω ↦ ENNReal.ofReal (d (A t ω) (Y t ω)) :=
    ENNReal.measurable_ofReal.comp (hdm.comp
      ((h.measurable_action t).prodMk (h.measurable_feedback t)))
  rw [lintegral_add_left hdAm, hdA, two_mul]
  exact add_le_add hrA hrA

/-- The remainder of the truncation at the level `M` up to the horizon `T`,
`∑_{t < T} (|z - z_M|(A_t, Y_t) + E_{ν(A_t)}|z - z_M|)`, exceeds `ε T / 2` with probability at
most `4 / ε ∑_a E_{ν a}|z - z_M|`, by Markov's inequality. -/
private lemma IsAlgEnvSeq.measure_lt_sum_abs_sub_truncation_le
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) {z : α → 𝓨 → ℝ}
    (hz : Measurable (Function.uncurry z)) (hint : ∀ a, Integrable (z a) (ν a)) {ε M : ℝ}
    (hε : 0 < ε) {T : ℕ} (hT : 0 < T) :
    P {ω | ε * T / 2 < ∑ t ∈ range T, (|z (A t ω) (Y t ω) - truncation (z (A t ω)) M (Y t ω)| +
        ∫ y, |z (A t ω) y - truncation (z (A t ω)) M y| ∂ν (A t ω))} ≤
      ENNReal.ofReal (4 / ε * ∑ a, ∫ y, |z a y - truncation (z a) M y| ∂ν a) := by
  set d : α → 𝓨 → ℝ := fun a y ↦ |z a y - truncation (z a) M y| with hd
  set r : α → ℝ := fun a ↦ ∫ y, d a y ∂ν a with hr
  have hdm : Measurable (Function.uncurry d) :=
    continuous_abs.measurable.comp (hz.sub ((measurable_id.indicator measurableSet_Ioc).comp hz))
  have hd0 (a : α) (y : 𝓨) : 0 ≤ d a y := abs_nonneg _
  have hr0 (a : α) : 0 ≤ r a := integral_nonneg (hd0 a)
  have hdint (a : α) : Integrable (d a) (ν a) := by
    refine ((hint a).sub ?_).abs
    exact (hint a).aestronglyMeasurable.integrable_truncation
  have hrm : Measurable r := measurable_of_countable r
  set ρ := ∑ a, r a with hρ
  have hρ0 : 0 ≤ ρ := sum_nonneg fun a _ ↦ hr0 a
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hx : 0 < ε * T / 2 := by positivity
  -- the remainder as an `ℝ≥0∞`-valued sum
  set B : Ω → ℝ≥0∞ := fun ω ↦ ∑ t ∈ range T,
    (ENNReal.ofReal (d (A t ω) (Y t ω)) + ENNReal.ofReal (r (A t ω))) with hB
  have hterm (t : ℕ) : Measurable fun ω ↦
      ENNReal.ofReal (d (A t ω) (Y t ω)) + ENNReal.ofReal (r (A t ω)) :=
    (ENNReal.measurable_ofReal.comp (hdm.comp ((h.measurable_action t).prodMk
      (h.measurable_feedback t)))).add
      (ENNReal.measurable_ofReal.comp (hrm.comp (h.measurable_action t)))
  have hBm : Measurable B := Finset.measurable_sum _ fun t _ ↦ hterm t
  have h_sub : {ω | ε * T / 2 < ∑ t ∈ range T, (d (A t ω) (Y t ω) + r (A t ω))} ⊆
      {ω | ENNReal.ofReal (ε * T / 2) ≤ B ω} := by
    intro ω hω
    have hBω : B ω = ENNReal.ofReal (∑ t ∈ range T, (d (A t ω) (Y t ω) + r (A t ω))) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun t _ ↦ add_nonneg (hd0 _ _) (hr0 _)]
      exact sum_congr rfl fun t _ ↦ (ENNReal.ofReal_add (hd0 _ _) (hr0 _)).symm
    rw [Set.mem_ofPred_eq, hBω]
    exact ENNReal.ofReal_le_ofReal hω.le
  -- along the run, `E[d(A_t, Y_t)] = E[r(A_t)] ≤ ρ`
  have h_exp (t : ℕ) := h.lintegral_ofReal_add_ofReal_integral_le hdm hd0 hdint t
  calc P {ω | ε * T / 2 < ∑ t ∈ range T, (d (A t ω) (Y t ω) + r (A t ω))}
  _ ≤ P {ω | ENNReal.ofReal (ε * T / 2) ≤ B ω} := measure_mono h_sub
  _ ≤ (∫⁻ ω, B ω ∂P) / ENNReal.ofReal (ε * T / 2) :=
      meas_ge_le_lintegral_div hBm.aemeasurable (ENNReal.ofReal_pos.2 hx).ne' ENNReal.ofReal_ne_top
  _ ≤ (T * (2 * ENNReal.ofReal ρ)) / ENNReal.ofReal (ε * T / 2) := by
      gcongr
      simp only [hB]
      rw [lintegral_finsetSum _ fun t _ ↦ hterm t]
      exact (sum_le_sum fun t _ ↦ h_exp t).trans (by simp [hρ, hr])
  _ = ENNReal.ofReal (4 / ε * ρ) := by
      rw [show (T : ℝ≥0∞) * (2 * ENNReal.ofReal ρ) = ENNReal.ofReal (T * (2 * ρ)) by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul zero_le_two,
          ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat],
        ← ENNReal.ofReal_div_of_pos hx]
      congr 1
      field_simp
      ring

/-- **Deviations of the centred sums before a horizon.** Along a run of any algorithm against the
stochastic bandit `ν` with finitely many arms, let `z a y` be integrable under every arm law
`ν a`. For `ε > 0`, every level of truncation `M > 0` and every horizon `T`, the probability that
`∑_{t < n} (z(A_t, Y_t) - E_{ν(A_t)}[z])` exceeds `ε T` for some `n ≤ T` is at most
`exp (-ε² T / (8 M²)) + 4 / ε ∑_a E_{ν a}|z - z_M|`, where `z_M = truncation (z a) M` is the
truncation of `z` at the level `M`, equal to `z` on `(-M, M]` and to `0` elsewhere. The bound
does not depend on the algorithm. -/
theorem IsAlgEnvSeq.measure_exists_le_mul_lt_sum_sub_integral_le
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) {z : α → 𝓨 → ℝ}
    (hz : Measurable (Function.uncurry z)) (hint : ∀ a, Integrable (z a) (ν a)) {ε M : ℝ}
    (hε : 0 < ε) (hM : 0 < M) (T : ℕ) :
    P {ω | ∃ n ≤ T, ε * T < ∑ t ∈ range n, (z (A t ω) (Y t ω) - ∫ y, z (A t ω) y ∂ν (A t ω))} ≤
      ENNReal.ofReal (exp (-(ε ^ 2 * T / (8 * M ^ 2)))) +
        ENNReal.ofReal (4 / ε * ∑ a, ∫ y, |z a y - truncation (z a) M y| ∂ν a) := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · -- before the horizon `0` the sums are empty
    have : {ω | ∃ n ≤ 0, ε * (0 : ℕ) < ∑ t ∈ range n,
        (z (A t ω) (Y t ω) - ∫ y, z (A t ω) y ∂ν (A t ω))} = ∅ := by
      ext ω
      simp
    rw [this, measure_empty]
    exact bot_le
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  -- the truncation `z_M` and its centred version `g`, which is `M²`-sub-Gaussian
  set g : α → 𝓨 → ℝ := fun a y ↦ truncation (z a) M y - ∫ y', truncation (z a) M y' ∂ν a with hg
  have hzcm : Measurable fun p : α × 𝓨 ↦ truncation (z p.1) M p.2 :=
    (measurable_id.indicator measurableSet_Ioc).comp hz
  have hgm : Measurable (Function.uncurry g) :=
    hzcm.sub ((measurable_of_countable fun a ↦ ∫ y', truncation (z a) M y' ∂ν a).comp
      measurable_fst)
  have hzcint (a : α) : Integrable (truncation (z a) M) (ν a) :=
    (hint a).aestronglyMeasurable.integrable_truncation
  set c : ℝ≥0 := (‖M - -M‖₊ / 2) ^ 2 with hc
  have hcM : (c : ℝ) = M ^ 2 := by
    rw [hc, NNReal.coe_pow, NNReal.coe_div, coe_nnNorm, Real.norm_eq_abs, sub_neg_eq_add,
      abs_of_pos (by linarith)]
    norm_num
  have hc0 : 0 < c := by
    rw [← NNReal.coe_pos, hcM]
    positivity
  have hgc (a : α) : HasSubgaussianMGF (g a) c (ν a) :=
    hasSubgaussianMGF_of_mem_Icc (hint a).aestronglyMeasurable.truncation.aemeasurable
      (ae_of_all _ fun y ↦ abs_le.1 ((abs_truncation_le_bound _ _ y).trans_eq (abs_of_pos hM)))
  -- the deviation splits between the truncated part and the remainder
  have h_dec (ω : Ω) (n : ℕ) (hn : n ≤ T) :
      ∑ t ∈ range n, (z (A t ω) (Y t ω) - ∫ y, z (A t ω) y ∂ν (A t ω)) ≤
        ∑ t ∈ range n, g (A t ω) (Y t ω) + ∑ t ∈ range T,
          (|z (A t ω) (Y t ω) - truncation (z (A t ω)) M (Y t ω)| +
            ∫ y, |z (A t ω) y - truncation (z (A t ω)) M y| ∂ν (A t ω)) := by
    have h_term (a : α) (y : 𝓨) : z a y - ∫ y', z a y' ∂ν a ≤ g a y +
        (|z a y - truncation (z a) M y| + ∫ y', |z a y' - truncation (z a) M y'| ∂ν a) := by
      have h_mean : |∫ y', z a y' ∂ν a - ∫ y', truncation (z a) M y' ∂ν a| ≤
          ∫ y', |z a y' - truncation (z a) M y'| ∂ν a := by
        rw [← integral_sub (hint a) (hzcint a)]
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := ν a) fun y ↦ z a y - truncation (z a) M y
      have hga : g a y = truncation (z a) M y - ∫ y', truncation (z a) M y' ∂ν a := rfl
      linarith [le_abs_self (z a y - truncation (z a) M y), neg_abs_le
        (∫ y', z a y' ∂ν a - ∫ y', truncation (z a) M y' ∂ν a)]
    calc _ ≤ ∑ t ∈ range n, (g (A t ω) (Y t ω) +
          (|z (A t ω) (Y t ω) - truncation (z (A t ω)) M (Y t ω)| +
            ∫ y, |z (A t ω) y - truncation (z (A t ω)) M y| ∂ν (A t ω))) :=
        sum_le_sum fun t _ ↦ h_term _ _
    _ ≤ _ := by
        rw [sum_add_distrib]
        gcongr
  have h_sub : {ω | ∃ n ≤ T, ε * T < ∑ t ∈ range n,
      (z (A t ω) (Y t ω) - ∫ y, z (A t ω) y ∂ν (A t ω))} ⊆
      {ω | ∃ n ≤ T, ε * T / 2 < ∑ t ∈ range n, g (A t ω) (Y t ω)} ∪
        {ω | ε * T / 2 < ∑ t ∈ range T, (|z (A t ω) (Y t ω) - truncation (z (A t ω)) M (Y t ω)| +
          ∫ y, |z (A t ω) y - truncation (z (A t ω)) M y| ∂ν (A t ω))} := by
    rintro ω ⟨n, hnT, hn⟩
    by_contra hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_lt] at hω
    linarith [h_dec ω n hnT, hω.1 n hnT]
  calc _ ≤ P ({ω | ∃ n ≤ T, ε * T / 2 < ∑ t ∈ range n, g (A t ω) (Y t ω)} ∪
        {ω | ε * T / 2 < ∑ t ∈ range T, (|z (A t ω) (Y t ω) - truncation (z (A t ω)) M (Y t ω)| +
          ∫ y, |z (A t ω) y - truncation (z (A t ω)) M y| ∂ν (A t ω))}) := measure_mono h_sub
  _ ≤ _ := measure_union_le _ _
  _ ≤ _ := by
      gcongr
      · refine (h.measure_exists_le_lt_sum_le_of_hasSubgaussianMGF hgm hc0 hgc
          (by positivity) hT).trans (ENNReal.ofReal_le_ofReal (exp_le_exp.2 (le_of_eq ?_)))
        rw [hcM]
        field_simp
        ring
      · exact h.measure_lt_sum_abs_sub_truncation_le hz hint hε hT

end Learning

namespace LMLExplore

variable {α 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} [Finite α]
  [MeasurableSingletonClass α] {ν : Kernel α 𝓨} [IsMarkovKernel ν]

/-- **A weak law of large numbers along bandit runs, uniform in the algorithm.** Let `z a y` be
integrable under every arm law `ν a` of a stochastic bandit with finitely many arms. For every
`ε > 0` and `η > 0`, for every large enough horizon `T`, along every run of every algorithm against
`ν`, the probability that `∑_{t < n} (z(A_t, Y_t) - E_{ν(A_t)}[z])` exceeds `ε T` for some
`n ≤ T` is at most `η`. -/
theorem eventually_measure_exists_le_mul_lt_sum_sub_integral_le {z : α → 𝓨 → ℝ}
    (hz : Measurable (Function.uncurry z)) (hint : ∀ a, Integrable (z a) (ν a)) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      [IsProbabilityMeasure P] {alg : Algorithm Unit α 𝓨} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
      {Y : ℕ → Ω → 𝓨}, IsAlgEnvSeq O A Y alg (Environment.bandit ν) P →
        P {ω | ∃ n ≤ T, ε * T < ∑ t ∈ range n,
          (z (A t ω) (Y t ω) - ∫ y, z (A t ω) y ∂ν (A t ω))} ≤ ENNReal.ofReal η := by
  have := Fintype.ofFinite α
  -- choose a level of truncation with a small remainder, then a large horizon
  have h_lim : Tendsto (fun M ↦ 4 / ε * ∑ a, ∫ y, |z a y - truncation (z a) M y| ∂ν a) atTop
      (𝓝 (4 / ε * ∑ _a : α, (0 : ℝ))) :=
    (tendsto_finsetSum _ fun a _ ↦ tendsto_integral_abs_sub_truncation (hint a)).const_mul _
  rw [sum_const_zero, mul_zero] at h_lim
  obtain ⟨M, hMη, hM⟩ := ((h_lim.eventually (gt_mem_nhds (half_pos hη))).and
    (eventually_gt_atTop (0 : ℝ))).exists
  have h_exp : Tendsto (fun T : ℕ ↦ exp (-(ε ^ 2 * T / (8 * M ^ 2)))) atTop (𝓝 0) := by
    have h_lin : Tendsto (fun T : ℕ ↦ ε ^ 2 / (8 * M ^ 2) * T) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop
    exact tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (h_lin.congr fun T ↦ by ring))
  filter_upwards [h_exp.eventually (gt_mem_nhds (half_pos hη))] with T hT Ω _ P _ alg O A Y h
  refine (h.measure_exists_le_mul_lt_sum_sub_integral_le hz hint hε hM T).trans ?_
  rw [← ENNReal.ofReal_add (exp_pos _).le (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end LMLExplore
