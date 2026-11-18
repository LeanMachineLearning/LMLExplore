/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.LinearBandit.Basic
public import LMLExplore.Identification.Task.GaussianLinear
public import LMLExplore.Identification.TrackAndStop
public import LMLExplore.SequentialLearning.FiniteActions

/-!
# The GLRT of linear models with the self-normalized threshold

In a linear model, the models of an identification task are the vectors `θ` of a
finite-dimensional real inner product space `E`, and the arm `a` of `θ` has observations of mean
`⟪φ a, θ⟫` for features `φ : α → E`. After `n` rounds with history `h`, let `x s = φ (A s)` be the
features of the arms played at the rounds `s < n`, `V_n = λ 1 + ∑_{s < n} x s ⊗ x s` the design
operator of ridge regression with parameter `λ > 0` and `θ̂_n` the ridge estimate of `θ` from the
observations of `h` (`ridgeEstimate'`).

For Gaussian observations with known variance `σ²`, the arm `a` of `θ` having the law
`𝒩(⟪φ a, θ⟫, σ²)`, the plug-in statistic of the ridge estimate against a model `λ'`, the statistic
of the GLRT of `Identification/TrackAndStop.lean`, is the sum of the squared differences of the
predictions of the two models at the features of the rounds,
`∑_a N_a KL(ν_a(θ̂_n), ν_a(λ')) = ∑_{s < n} ⟪x s, θ̂_n - λ'⟫² / (2 σ²)`
(`IdentTask.plugInCost_gaussianReal_inner`), and is therefore at most
`‖θ̂_n - λ'‖²_{V_n} / (2 σ²)` (`IdentTask.plugInCost_le_inner_designOp`).

At the true model `θ`, the confidence ellipsoids of ridge regression [AYPS11, Theorem 2;
LS, Theorem 20.5] bound this self-normalized quantity uniformly in time: if the noise is
conditionally σ²-sub-Gaussian, with probability at least `1 - δ`, for every `n`,
`‖θ̂_n - θ‖_{V_n} < √λ ‖θ‖ + √(2 σ² log (1 / δ) + σ² log (det V_n / λ ^ d))`, with `d` the
dimension of `E`. When every admissible model has norm at most `S`, the GLRT with the
*self-normalized threshold* (`selfNormalizedThreshold`)
`β_n(h) = (√λ S + √(2 σ² log (1 / δ) + σ² log (det V_n / λ ^ d)))² / (2 σ²)`,
which reads the history through the design operator, or with any larger threshold, therefore
stops with an incorrect answer with probability at most `δ`, for every task and every sampling
rule. The game-based algorithms of linear identification [DMSV20] stop with thresholds of this
kind. For features of norm at most `L`, `log (det V_n / λ ^ d) ≤ d log (1 + n L² / (λ d))`
[LS, (20.9)], which gives a threshold depending on the round only
(`selfNormalizedThreshold_le_of_norm_le`).

The bound on the norm of the models is the price of the regularization: the bias of the ridge
estimate towards `0` is at most `√λ ‖θ‖` in the norm of `V_n`.

## Main definitions

* `LMLExplore.Identification.ridgeEstimate' φ λ n h`: the ridge estimate of the parameter of a
  linear model with features `φ` from the history `h` of the first `n` rounds.
* `LMLExplore.Identification.selfNormalizedThreshold φ σ2 λ S δ n h`: the self-normalized
  threshold `β_n(h)`.

## Main statements

* `selfNormalizedThreshold_le_of_norm_le`: for features of norm at most `L`, the self-normalized
  threshold is at most
  `(√λ S + √(2 σ² log (1 / δ) + σ² d log (1 + n L² / (λ d))))² / (2 σ²)`.
* `IdentTask.isSubgaussianLinearEnv_bandit_of_gaussianReal`: Gaussian linear observations are a
  linear environment with σ²-sub-Gaussian noise.
* `IdentTask.plugInCost_gaussianReal_inner`: for Gaussian observations with variance `σ²`, the
  plug-in statistic of any estimator `θ̂` is `∑_{s < n} ⟪x s, θ̂ - λ'⟫² / (2 σ²)`.
* `IdentTask.plugInCost_le_inner_designOp`: it is at most `‖θ̂ - λ'‖²_{V_n} / (2 σ²)`.
* `measure_exists_selfNormalizedThreshold_lt_le`: along a run of any sampling rule in a linear
  environment with σ²-sub-Gaussian noise and parameter of norm at most `S`, the probability that
  `‖θ̂_n - θ‖²_{V_n} / (2 σ²)` exceeds the self-normalized threshold at some round is at most `δ`.
* `IdentTask.measure_exists_selfNormalizedThreshold_lt_plugInCost_le`: the same for the plug-in
  statistic of the ridge estimate, for Gaussian observations.
* `IdentTask.measureReal_histOutputMeasure_glrt_selfNormalizedThreshold_le`: for every task with
  Gaussian linear observations and every sampling rule, the GLRT with the plug-in statistic of the
  ridge estimate and any thresholds above the self-normalized threshold stops with an answer that
  is not correct for an admissible model of norm at most `S` with probability at most `δ`.
* `IdentTask.isDeltaPAC_glrt_selfNormalizedThreshold`: when every admissible model has norm at
  most `S`, this GLRT is `δ`-PAC as soon as it stops almost surely on every admissible model.

## References

* [AYPS11] Y. Abbasi-Yadkori, D. Pál and Cs. Szepesvári, *Improved algorithms for linear
  stochastic bandits*, NeurIPS 2011, Theorem 2.
* [DMSV20] R. Degenne, P. Ménard, X. Shang and M. Valko, *Gamification of pure exploration for
  linear bandits*, ICML 2020.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Theorem 20.5 and (20.9).
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real Module LMLExplore.Bandits
open scoped ENNReal NNReal InnerProductSpace

namespace LMLExplore.Identification

variable {α E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {φ : α → E} {σ2 : ℝ≥0}
  {lam S δ : ℝ}

/-! ### The ridge estimate and the self-normalized threshold of a history -/

section Defs

variable {Ω : Type*} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}

/-- The *ridge estimate* `θ̂_n = V_n⁻¹ ∑_{s < n} Y s • φ (A s)` of the parameter of a linear model
with features `φ`, from the history `h` of the first `n` rounds, with the design operator
`V_n = λ 1 + ∑_{s < n} φ (A s) ⊗ φ (A s)` of ridge regression with parameter `λ`. -/
noncomputable def ridgeEstimate' (φ : α → E) (lam : ℝ) (n : ℕ) (h : Hist Unit α ℝ n) : E :=
  ridgeEstimate lam (histFeature (fun _ ↦ φ) h) (histReward h) n

lemma ridgeEstimate'_def (n : ℕ) (h : Hist Unit α ℝ n) :
    ridgeEstimate' φ lam n h = ridgeEstimate lam (histFeature (fun _ ↦ φ) h) (histReward h) n :=
  (rfl)

/-- The ridge estimate of the history of a sequence of rounds is the ridge estimate of the
features of the arms played and of the observations. -/
@[simp]
lemma ridgeEstimate'_history (n : ℕ) (ω : Ω) :
    ridgeEstimate' φ lam n (history O A Y n ω) =
      ridgeEstimate lam (fun s ↦ φ (A s ω)) (fun s ↦ Y s ω) n :=
  ridgeEstimate_congr (fun _ hs ↦ histFeature_history hs ω) fun _ hs ↦ histReward_history hs ω

/-- In finite dimension, the ridge estimate depends measurably on the history. -/
lemma measurable_ridgeEstimate' [MeasurableSpace α] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (hφ : Measurable φ) (lam : ℝ) (n : ℕ) :
    Measurable (ridgeEstimate' φ lam n) :=
  (measurable_histFeature (φ := fun (_ : Unit) ↦ φ) (hφ.comp measurable_snd) n).ridgeEstimate
    (measurable_histReward n) lam n

variable (φ σ2 lam S δ) in
/-- The *self-normalized threshold* of the GLRT of a linear model with features `φ`, after `n`
rounds with history `h`:
`β_n(h) = (√λ S + √(2 σ² log (1 / δ) + σ² log (det V_n / λ ^ d)))² / (2 σ²)`, with
`V_n = λ 1 + ∑_{s < n} φ (A s) ⊗ φ (A s)` the design operator of ridge regression with parameter
`λ` and `d` the dimension of `E`. For σ²-sub-Gaussian noise and a parameter of norm at most `S`,
`‖θ̂_n - θ‖²_{V_n} / (2 σ²)` exceeds it at some round with probability at most `δ`
(`measure_exists_selfNormalizedThreshold_lt_le`). -/
noncomputable def selfNormalizedThreshold (n : ℕ) (h : Hist Unit α ℝ n) : ℝ≥0∞ :=
  ENNReal.ofReal ((√lam * S + √(2 * σ2 * log (1 / δ) + σ2 *
    log (LinearMap.det (designOp (lam • 1) (histFeature (fun _ ↦ φ) h) n : E →ₗ[ℝ] E) /
      lam ^ finrank ℝ E))) ^ 2 / (2 * σ2))

lemma selfNormalizedThreshold_def (n : ℕ) (h : Hist Unit α ℝ n) :
    selfNormalizedThreshold φ σ2 lam S δ n h =
      ENNReal.ofReal ((√lam * S + √(2 * σ2 * log (1 / δ) + σ2 *
        log (LinearMap.det (designOp (lam • 1) (histFeature (fun _ ↦ φ) h) n : E →ₗ[ℝ] E) /
          lam ^ finrank ℝ E))) ^ 2 / (2 * σ2)) :=
  (rfl)

/-- In finite dimension, the self-normalized threshold depends measurably on the history. -/
lemma measurable_selfNormalizedThreshold [MeasurableSpace α] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (hφ : Measurable φ) (n : ℕ) :
    Measurable (selfNormalizedThreshold φ σ2 lam S δ n) := by
  have hdet : Measurable fun h : Hist Unit α ℝ n ↦
      LinearMap.det (designOp (lam • 1) (histFeature (fun _ ↦ φ) h) n : E →ₗ[ℝ] E) :=
    ContinuousLinearMap.continuous_det.measurable.comp
      ((measurable_histFeature (φ := fun (_ : Unit) ↦ φ) (hφ.comp measurable_snd) n).designOp _ n)
  simp_rw [funext (selfNormalizedThreshold_def (φ := φ) (σ2 := σ2) (lam := lam) (S := S)
    (δ := δ) n)]
  exact ENNReal.measurable_ofReal.comp ((((hdet.div_const _).log.const_mul _).const_add
    _).sqrt.const_add _ |>.pow_const 2 |>.div_const _)

/-- The self-normalized threshold of the history of a sequence of rounds reads the design
operator of the features of the arms played. -/
lemma selfNormalizedThreshold_history (n : ℕ) (ω : Ω) :
    selfNormalizedThreshold φ σ2 lam S δ n (history O A Y n ω) =
      ENNReal.ofReal ((√lam * S + √(2 * σ2 * log (1 / δ) + σ2 *
        log (LinearMap.det (designOp (lam • 1) (fun s ↦ φ (A s ω)) n : E →ₗ[ℝ] E) /
          lam ^ finrank ℝ E))) ^ 2 / (2 * σ2)) := by
  rw [selfNormalizedThreshold_def, designOp_congr fun _ hs ↦ histFeature_history hs ω]

/-- **The self-normalized threshold for bounded features** [LS, (20.9)]. If the features have
norm at most `L`, the self-normalized threshold after `n` rounds is at most
`(√λ S + √(2 σ² log (1 / δ) + σ² d log (1 + n L² / (λ d))))² / (2 σ²)`, which depends on the
round only. -/
lemma selfNormalizedThreshold_le_of_norm_le [FiniteDimensional ℝ E] (hlam : 0 < lam)
    (hS : 0 ≤ S) {L : ℝ} (hL : ∀ a, ‖φ a‖ ≤ L) (n : ℕ) (h : Hist Unit α ℝ n) :
    selfNormalizedThreshold φ σ2 lam S δ n h ≤
      ENNReal.ofReal ((√lam * S + √(2 * σ2 * log (1 / δ) +
        σ2 * finrank ℝ E * log (1 + n * L ^ 2 / (lam * finrank ℝ E)))) ^ 2 / (2 * σ2)) := by
  have hL' : ∀ s < n, ‖histFeature (fun _ ↦ φ) h s‖ ≤ L := fun s hs ↦ by
    simpa [histFeature_def, hs] using hL _
  rw [selfNormalizedThreshold_def]
  refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (pow_le_pow_left₀
    (add_nonneg (mul_nonneg (sqrt_nonneg _) hS) (sqrt_nonneg _)) ?_ 2) (by positivity))
  gcongr _ + √(_ + ?_)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (log_det_designOp_div_pow_le hlam _ hL') σ2.2

end Defs

/-! ### The plug-in statistic of Gaussian linear models -/

namespace IdentTask

variable {mα : MeasurableSpace α} {ℐ : Type*} {task : IdentTask α E ℐ ℝ}

/-- A linear model with Gaussian observations of variance `σ2`, the arm `a` of `θ` having the law
`𝒩(⟪φ a, θ⟫, σ2)`, is a linear environment with features `φ`, parameter `θ` and σ²-sub-Gaussian
noise. -/
lemma isSubgaussianLinearEnv_bandit_of_gaussianReal
    (hν : ∀ θ a, task.ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ σ2) (θ : E) :
    IsSubgaussianLinearEnv (fun _ ↦ φ) θ σ2 (Environment.bandit (task.ν θ)) :=
  isSubgaussianLinearEnv_iff.2 fun n h o a ↦ by
    rw [feedback_bandit, Kernel.prodMkLeft_apply, hν, real_inner_comm]
    exact hasSubgaussianMGF_sub_of_hasLaw_gaussianReal HasLaw.id

variable [Fintype α] [DecidableEq α]

/-- For a linear model with Gaussian observations of variance `σ2 ≠ 0`, the arm `a` of `θ` having
the law `𝒩(⟪φ a, θ⟫, σ2)`, the plug-in statistic of an estimator `est`, for the history `h` of the
first `n` rounds against the model `θ'`, is `∑_{s < n} ⟪x s, θ̂ - θ'⟫² / (2 σ2)`, with the features
`x s` of the arms played and the estimate `θ̂ = est n h`. -/
theorem plugInCost_gaussianReal_inner (hσ : σ2 ≠ 0)
    (hν : ∀ θ a, task.ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ σ2)
    (est : (n : ℕ) → Hist Unit α ℝ n → E) (n : ℕ) (h : Hist Unit α ℝ n) (θ' : E) :
    task.plugInCost est n h θ' = ENNReal.ofReal
      ((∑ s ∈ range n, ⟪histFeature (fun _ ↦ φ) h s, est n h - θ'⟫_ℝ ^ 2) / (2 * σ2)) := by
  have hsum : ∑ a, (pullCount' n h a : ℝ) * ⟪φ a, est n h - θ'⟫_ℝ ^ 2 =
      ∑ s ∈ range n, ⟪histFeature (fun _ ↦ φ) h s, est n h - θ'⟫_ℝ ^ 2 := by
    rw [sum_pullCount'_mul, ← Fin.sum_univ_eq_sum_range]
    simp [histFeature_def]
  rw [plugInCost_def, cost_gaussianReal_inner (v := fun _ ↦ σ2) (fun _ ↦ hσ) hν
    (fun _ ↦ Nat.cast_nonneg _), inner_sum_smul_rankOne_apply_self, ← hsum, sum_div, sum_div]
  congr 1
  exact sum_congr rfl fun a _ ↦ by ring

/-- For a linear model with Gaussian observations of variance `σ2 ≠ 0`, the plug-in statistic of
an estimator `est`, for the history `h` of the first `n` rounds against the model `θ'`, is at most
`‖θ̂ - θ'‖²_{V_n} / (2 σ2)` for the estimate `θ̂ = est n h` and the design operator `V_n` of ridge
regression with any parameter `λ ≥ 0`. -/
theorem plugInCost_le_inner_designOp (hσ : σ2 ≠ 0)
    (hν : ∀ θ a, task.ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ σ2)
    (est : (n : ℕ) → Hist Unit α ℝ n → E) (hlam : 0 ≤ lam) (n : ℕ) (h : Hist Unit α ℝ n)
    (θ' : E) :
    task.plugInCost est n h θ' ≤ ENNReal.ofReal (⟪est n h - θ',
      designOp (lam • 1) (histFeature (fun _ ↦ φ) h) n (est n h - θ')⟫_ℝ / (2 * σ2)) := by
  rw [plugInCost_gaussianReal_inner hσ hν, inner_designOp_smul_one_apply_self]
  gcongr
  exact le_add_of_nonneg_left (by positivity)

end IdentTask

/-! ### Deviations of the self-normalized statistic -/

variable [MeasurableSpace α] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
  {Y : ℕ → Ω → ℝ} {θ : E}

/-- **Deviations of the self-normalized statistic**, along a run of any sampling rule. In a linear
environment with features `φ`, parameter `θ` of norm at most `S` and σ²-sub-Gaussian noise,
`σ2 ≠ 0`, for `λ > 0` and `δ > 0`, the probability that at some round `n`,
`‖θ̂_n - θ‖²_{V_n} / (2 σ2)` exceeds the self-normalized threshold is at most `δ`, where `θ̂_n` is
the ridge estimate and `V_n` the design operator of ridge regression after `n` rounds. -/
theorem measure_exists_selfNormalizedThreshold_lt_le
    {env : Environment Unit α ℝ} (hseq : IsAlgEnvSeq O A Y alg env P)
    (henv : IsSubgaussianLinearEnv (fun _ ↦ φ) θ σ2 env) (hφ : Measurable φ) (hσ : σ2 ≠ 0)
    (hlam : 0 < lam) (hδ : 0 < δ) (hθ : ‖θ‖ ≤ S) :
    P {ω | ∃ n, selfNormalizedThreshold φ σ2 lam S δ n (history O A Y n ω) <
      ENNReal.ofReal (⟪ridgeEstimate' φ lam n (history O A Y n ω) - θ,
        designOp (lam • 1) (fun s ↦ φ (A s ω)) n
          (ridgeEstimate' φ lam n (history O A Y n ω) - θ)⟫_ℝ / (2 * σ2))} ≤
      ENNReal.ofReal δ := by
  refine (measure_mono fun ω hω ↦ ?_).trans
    (hseq.measure_exists_sqrt_inner_ridgeEstimate_sub_ge_le henv (hφ.comp measurable_snd) hσ hlam
      hδ)
  obtain ⟨n, hn⟩ := hω
  refine ⟨n, ?_⟩
  rw [selfNormalizedThreshold_history, ridgeEstimate'_history,
    ENNReal.ofReal_lt_ofReal_iff'] at hn
  have hσ' : (0 : ℝ) < 2 * σ2 := by positivity
  have hr : 0 ≤ √lam * S + √(2 * σ2 * log (1 / δ) + σ2 *
      log (LinearMap.det (designOp (lam • 1) (fun s ↦ φ (A s ω)) n : E →ₗ[ℝ] E) /
        lam ^ finrank ℝ E)) :=
    add_nonneg (mul_nonneg (sqrt_nonneg _) ((norm_nonneg θ).trans hθ)) (sqrt_nonneg _)
  refine le_trans ?_ ((lt_sqrt hr).2 ((div_lt_div_iff_of_pos_right hσ').1 hn.1)).le
  gcongr

variable [MeasurableSingletonClass α]

namespace IdentTask

variable [Fintype α] [DecidableEq α] {ℐ : Type*} {task : IdentTask α E ℐ ℝ}

/-- **Deviations of the plug-in statistic of the ridge estimate**, along a run of any sampling
rule. For a linear model with Gaussian observations of variance `σ2 ≠ 0` and a model `θ` of norm
at most `S`, for `λ > 0` and `δ > 0`, the probability that at some round, the plug-in statistic of
the ridge estimate against `θ` exceeds the self-normalized threshold is at most `δ`. -/
theorem measure_exists_selfNormalizedThreshold_lt_plugInCost_le (hσ : σ2 ≠ 0)
    (hν : ∀ θ a, task.ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ σ2)
    (hseq : IsAlgEnvSeq O A Y alg (Environment.bandit (task.ν θ)) P) (hlam : 0 < lam)
    (hδ : 0 < δ) (hθ : ‖θ‖ ≤ S) :
    P {ω | ∃ n, selfNormalizedThreshold φ σ2 lam S δ n (history O A Y n ω) <
      task.plugInCost (ridgeEstimate' φ lam) n (history O A Y n ω) θ} ≤ ENNReal.ofReal δ := by
  refine (measure_mono fun ω ↦ Exists.imp fun n hn ↦ hn.trans_le ?_).trans
    (measure_exists_selfNormalizedThreshold_lt_le hseq
      (isSubgaussianLinearEnv_bandit_of_gaussianReal hν θ) (measurable_of_countable φ) hσ hlam hδ
      hθ)
  refine (plugInCost_le_inner_designOp hσ hν _ hlam.le n _ θ).trans_eq ?_
  rw [designOp_congr fun _ hs ↦ histFeature_history hs ω]

/-! ### The GLRT with the self-normalized threshold -/

variable {mℐ : MeasurableSpace ℐ} {β : (n : ℕ) → Hist Unit α ℝ n → ℝ≥0∞}
  {rec : (n : ℕ) → Hist Unit α ℝ n → ℐ} {hrec : ∀ n, Measurable (rec n)}
  {hstop : ∀ n, MeasurableSet
    {h | β n h < task.glr (task.plugInCost (ridgeEstimate' φ lam)) n h (rec n h)}}

/-- **Error probability of the GLRT of a Gaussian linear model**, for every task and every
sampling rule. For a linear model with Gaussian observations of variance `σ2 ≠ 0`, an admissible
model `θ` of norm at most `S`, `λ > 0` and `δ > 0`, the GLRT with the plug-in statistic of the
ridge estimate and thresholds at least the self-normalized threshold stops with an answer that is
not correct for `θ` with probability at most `δ`. -/
theorem measureReal_histOutputMeasure_glrt_selfNormalizedThreshold_le (hσ : σ2 ≠ 0)
    (hν : ∀ θ a, task.ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ σ2) (hlam : 0 < lam) (hδ : 0 < δ)
    (hβ : ∀ n h, selfNormalizedThreshold φ σ2 lam S δ n h ≤ β n h) (hθ : θ ∈ task.M)
    (hθS : ‖θ‖ ≤ S) (hc : MeasurableSet (task.correct θ)) :
    (histOutputMeasure (task.glrt (task.plugInCost (ridgeEstimate' φ lam)) alg β rec hrec hstop)
        (Environment.bandit (task.ν θ))).real
        {p | p.1 ∈ (task.glrt (task.plugInCost (ridgeEstimate' φ lam)) alg β rec hrec
          hstop).stopSet ∧ p.2 ∉ task.correct θ} ≤ δ :=
  (task.measureReal_histOutputMeasure_glrt_le _ alg β rec hrec hstop
    (IT.isAlgEnvSeq_trajMeasure alg _) hθ hc).trans
    (ENNReal.toReal_le_of_le_ofReal hδ.le ((measure_mono fun _ ↦
      Exists.imp fun n hn ↦ (hβ n _).trans_lt hn).trans
      (measure_exists_selfNormalizedThreshold_lt_plugInCost_le hσ hν
        (IT.isAlgEnvSeq_trajMeasure alg _) hlam hδ hθS)))

/-- **The GLRT of a Gaussian linear model is `δ`-PAC**, for every task and every sampling rule.
For a linear model with Gaussian observations of variance `σ2 ≠ 0` whose admissible models have
norm at most `S`, `λ > 0` and `δ > 0`, the GLRT with the plug-in statistic of the ridge estimate
and thresholds at least the self-normalized threshold is `δ`-PAC on the task, provided it stops
almost surely on every admissible model. -/
theorem isDeltaPAC_glrt_selfNormalizedThreshold (hσ : σ2 ≠ 0)
    (hν : ∀ θ a, task.ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ σ2) (hlam : 0 < lam) (hδ : 0 < δ)
    (hβ : ∀ n h, selfNormalizedThreshold φ σ2 lam S δ n h ≤ β n h)
    (hM : ∀ θ ∈ task.M, ‖θ‖ ≤ S) (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (h_stops : ∀ θ ∈ task.M, StopsAS
      (task.glrt (task.plugInCost (ridgeEstimate' φ lam)) alg β rec hrec hstop)
      (Environment.bandit (task.ν θ))) :
    task.IsDeltaPAC
      (task.glrt (task.plugInCost (ridgeEstimate' φ lam)) alg β rec hrec hstop) δ :=
  task.isDeltaPAC_glrt _ alg β rec hrec hstop hc
    (fun θ hθ ↦ ENNReal.toReal_le_of_le_ofReal hδ.le ((measure_mono fun _ ↦
      Exists.imp fun n hn ↦ (hβ n _).trans_lt hn).trans
      (measure_exists_selfNormalizedThreshold_lt_plugInCost_le hσ hν
        (IT.isAlgEnvSeq_trajMeasure alg _) hlam hδ (hM θ hθ)))) h_stops

end IdentTask

end LMLExplore.Identification
