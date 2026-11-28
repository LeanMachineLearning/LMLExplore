/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.WithDensity
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import LMLExplore.SequentialLearning.StoppedHistory
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
public import Mathlib.Probability.Kernel.Composition.WithDensity
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The likelihood ratio of the history between two stochastic bandits

Run one algorithm against two stochastic bandits `ν` and `ν₀` on the same arms, with `ν a ≪ ν₀ a`
for every arm `a`. The law of the history of the first `n` rounds against `ν` is the law of that
history against `ν₀` with density the likelihood ratio of the observations,
`L_n(h) = ∏_{t < n} (dν(a_t) / dν₀(a_t))(y_t)` for the history `h = (a_t, y_t)_{t < n}`. The
policy of the algorithm, which is common to both runs, does not appear in the density: only the
observations change law.

This is the change of measure on which the high-probability lower bounds of identification rest
[DK19, Proposition 18]: for an event `E` of the history, `P_ν(E) = E_{ν₀}[L_n 𝟙_E]`, so that
`P_ν(E) ≤ e^γ P_{ν₀}(E) + P_ν(L_n > e^γ)`. LML proves the analogous statement for two algorithms
in a common environment (`Learning.IsAlgEnvSeq.hasLaw_history_withDensity`), whose proof this file
follows.

The density is built from the Radon–Nikodym derivatives of the arms, taken finite
(`ENNReal.toNNReal`), so that its logarithm is the sum of the log-likelihood ratios `llr` of the
observations wherever it is positive.

## Main definitions

* `LMLExplore.armLikelihoodRatio ν ν₀ (a, y)`: the likelihood ratio `(dν(a) / dν₀(a))(y)` of one
  observation, taken finite.
* `LMLExplore.histLikelihoodRatio ν ν₀ n h`: the likelihood ratio
  `∏_{t < n} (dν(a_t) / dν₀(a_t))(y_t)` of the observations of the `n`-round history `h`.

## Main statements

* `LMLExplore.histLikelihoodRatio_succ`: the recursion `L_{n+1}(h) = L_n(h|_n) · ρ(a_n, y_n)`.
* `LMLExplore.measurable_histLikelihoodRatio`: its measurability, for countably many arms.
* `LMLExplore.measurable_sigma_sum_round`, `LMLExplore.measurable_sum_mul_llr`: the measurability
  of a sum of a function of the rounds of a history, and of the weighted log-likelihood ratio of an
  observation.
* `Learning.stepKernel_bandit_eq_withDensity`: the step kernel of a run against `ν` is the step
  kernel against `ν₀` with the density of the likelihood ratio of the observation of the round.
* `Learning.IsAlgEnvSeq.hasLaw_history_withDensity_bandit`: the law of the history against `ν` is
  the law of the history against `ν₀` with density `histLikelihoodRatio ν ν₀ n`.
* `Learning.setLIntegral_stoppedHistMeasure_bandit_eq`: the likelihood ratio identity at a stopping
  time, `E_ν[f(H_τ); τ < ∞] = E_{ν₀}[L_τ f(H_τ); τ < ∞]`.
* `Learning.setLIntegral_stoppedHistMeasure_bandit_le`: the change of measure towards a mixture of
  bandits `κ k` with weights `w k` [DK19, Lemma 19]:
  `E_ν[φ; τ < ∞] ≤ e^γ ∑_k w_k E_{κ k}[φ; τ < ∞] + E_ν[φ; τ < ∞, γ < Λ_τ]`, where `Λ_τ` is the
  weighted log-likelihood ratio of the stopped history. It rests on Jensen's inequality
  `e^{-∑_k w_k log L_k} ≤ ∑_k w_k / L_k`.

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, supplementary material, Appendix C.2, Proposition 18, and Appendix C.4,
  Lemma 19.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset

open scoped ENNReal

namespace LMLExplore

variable {α 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}

/-- The likelihood ratio `(dν(a) / dν₀(a))(y)` of one observation `y` of the arm `a`, taken
finite. -/
noncomputable def armLikelihoodRatio (ν ν₀ : Kernel α 𝓨) (p : α × 𝓨) : ℝ≥0∞ :=
  ((ν p.1).rnDeriv (ν₀ p.1) p.2).toNNReal

/-- The defining formula of `armLikelihoodRatio`. -/
lemma armLikelihoodRatio_def (ν ν₀ : Kernel α 𝓨) (p : α × 𝓨) :
    armLikelihoodRatio ν ν₀ p = ((ν p.1).rnDeriv (ν₀ p.1) p.2).toNNReal := (rfl)

/-- The likelihood ratio of one observation is finite. -/
lemma armLikelihoodRatio_ne_top (ν ν₀ : Kernel α 𝓨) (p : α × 𝓨) :
    armLikelihoodRatio ν ν₀ p ≠ ∞ :=
  ENNReal.coe_ne_top

/-- The real value of the likelihood ratio of one observation is the real value of the
Radon–Nikodym derivative, whose logarithm is the log-likelihood ratio `llr`. -/
lemma toReal_armLikelihoodRatio (ν ν₀ : Kernel α 𝓨) (p : α × 𝓨) :
    (armLikelihoodRatio ν ν₀ p).toReal = ((ν p.1).rnDeriv (ν₀ p.1) p.2).toReal := by
  rw [armLikelihoodRatio_def, ENNReal.coe_toReal, ENNReal.coe_toNNReal_eq_toReal]

/-- The likelihood ratio of one observation is measurable, for countably many arms. -/
@[fun_prop]
lemma measurable_armLikelihoodRatio [Countable α] [MeasurableSingletonClass α]
    (ν ν₀ : Kernel α 𝓨) : Measurable (armLikelihoodRatio ν ν₀) :=
  measurable_from_prod_countable_right fun a ↦ by
    simpa only [armLikelihoodRatio_def] using
      (Measure.measurable_rnDeriv (ν a) (ν₀ a)).ennreal_toNNReal.coe_nnreal_ennreal

/-- Against `ν₀ a`, the likelihood ratio of the observations of the arm `a` is a density of `ν a`,
when `ν a ≪ ν₀ a`. -/
lemma withDensity_armLikelihoodRatio (ν ν₀ : Kernel α 𝓨) [IsFiniteKernel ν] [IsFiniteKernel ν₀]
    {a : α}
    (hac : ν a ≪ ν₀ a) :
    (ν₀ a).withDensity (fun y ↦ armLikelihoodRatio ν ν₀ (a, y)) = ν a := by
  rw [← Measure.withDensity_rnDeriv_eq _ _ hac]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_ne_top (ν a) (ν₀ a)] with y hy
  rw [armLikelihoodRatio_def, ENNReal.coe_toNNReal hy]

/-- The likelihood ratio `∏_{t < n} (dν(a_t) / dν₀(a_t))(y_t)` of the observations of the
`n`-round history `h = (a_t, y_t)_{t < n}` between the stochastic bandits `ν` and `ν₀`. When
`ν a ≪ ν₀ a` for every arm, it is the density of the law of the history against `ν` with respect
to its law against `ν₀`, for every algorithm (`IsAlgEnvSeq.hasLaw_history_withDensity_bandit`). -/
noncomputable def histLikelihoodRatio (ν ν₀ : Kernel α 𝓨) (n : ℕ) (h : Hist Unit α 𝓨 n) : ℝ≥0∞ :=
  ∏ i, armLikelihoodRatio ν ν₀ ((h i).action, (h i).feedback)

/-- The defining formula of `histLikelihoodRatio`. -/
lemma histLikelihoodRatio_def (ν ν₀ : Kernel α 𝓨) (n : ℕ) (h : Hist Unit α 𝓨 n) :
    histLikelihoodRatio ν ν₀ n h = ∏ i, armLikelihoodRatio ν ν₀ ((h i).action, (h i).feedback) :=
  (rfl)

/-- The likelihood ratio of the empty history is `1`. -/
@[simp]
lemma histLikelihoodRatio_zero (ν ν₀ : Kernel α 𝓨) (h : Hist Unit α 𝓨 0) :
    histLikelihoodRatio ν ν₀ 0 h = 1 := by
  simp [histLikelihoodRatio_def]

/-- The likelihood ratio of an `(n + 1)`-round history is that of its first `n` rounds times the
likelihood ratio of its last observation. -/
lemma histLikelihoodRatio_succ (ν ν₀ : Kernel α 𝓨) (n : ℕ) (h : Hist Unit α 𝓨 (n + 1)) :
    histLikelihoodRatio ν ν₀ (n + 1) h = histLikelihoodRatio ν ν₀ n (fun i ↦ h i.castSucc) *
      armLikelihoodRatio ν ν₀ ((h (Fin.last n)).action, (h (Fin.last n)).feedback) := by
  simp only [histLikelihoodRatio_def, Fin.prod_univ_castSucc]

/-- The likelihood ratio of the history is finite. -/
lemma histLikelihoodRatio_ne_top (ν ν₀ : Kernel α 𝓨) (n : ℕ) (h : Hist Unit α 𝓨 n) :
    histLikelihoodRatio ν ν₀ n h ≠ ∞ :=
  ENNReal.prod_ne_top fun _ _ ↦ armLikelihoodRatio_ne_top ν ν₀ _

/-- The likelihood ratio of the history is measurable, for countably many arms. -/
@[fun_prop]
lemma measurable_histLikelihoodRatio [Countable α] [MeasurableSingletonClass α]
    (ν ν₀ : Kernel α 𝓨) (n : ℕ) : Measurable (histLikelihoodRatio ν ν₀ n) := by
  rw [show histLikelihoodRatio ν ν₀ n = fun h ↦ ∏ i,
    armLikelihoodRatio ν ν₀ ((h i).action, (h i).feedback) from
      funext (histLikelihoodRatio_def ν ν₀ n)]
  refine Finset.measurable_prod _ fun i _ ↦ (measurable_armLikelihoodRatio ν ν₀).comp ?_
  exact ((Round.measurable_action).comp (measurable_pi_apply i)).prodMk
    ((Round.measurable_feedback).comp (measurable_pi_apply i))

/-- The sum `∑_t g(a_t, y_t)` of a measurable function of the actions and the observations of the
rounds of a history of variable length is measurable. -/
lemma measurable_sigma_sum_round {𝓞 M : Type*} {m𝓞 : MeasurableSpace 𝓞} [AddCommMonoid M]
    [MeasurableSpace M] [MeasurableAdd₂ M] {g : α → 𝓨 → M}
    (hg : Measurable (Function.uncurry g)) :
    Measurable fun x : Σ n : ℕ, Hist 𝓞 α 𝓨 n ↦ ∑ t, g (x.2 t).action (x.2 t).feedback :=
  measurable_sigma fun n ↦ by
    simpa only [Function.comp_def] using Finset.measurable_sum
      (f := fun t (h : Hist 𝓞 α 𝓨 n) ↦ g (h t).action (h t).feedback) Finset.univ
      fun t _ ↦ hg.comp (((Round.measurable_action (𝓞 := 𝓞)).comp
        (measurable_pi_apply t)).prodMk ((Round.measurable_feedback (𝓞 := 𝓞)).comp
          (measurable_pi_apply t)))

/-- The weighted log-likelihood ratio `∑_{k ∈ s} w_k log (dν(a) / dκ_k(a))(y)` of an observation
`y` of the arm `a` is measurable, for countably many arms. -/
lemma measurable_sum_mul_llr [Countable α] [MeasurableSingletonClass α] {ι : Type*}
    (ν : Kernel α 𝓨) (κ : ι → Kernel α 𝓨) (s : Finset ι) (w : ι → ℝ) :
    Measurable fun p : α × 𝓨 ↦ ∑ k ∈ s, w k * llr (ν p.1) (κ k p.1) p.2 :=
  measurable_from_prod_countable_right fun a ↦
    Finset.measurable_sum _ fun k _ ↦ (measurable_llr (ν a) (κ k a)).const_mul (w k)

end LMLExplore

namespace Learning

open LMLExplore

variable {α 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  [Countable α] [MeasurableSingletonClass α] {ν ν₀ : Kernel α 𝓨} [IsMarkovKernel ν]
  [IsMarkovKernel ν₀] {alg : Algorithm Unit α 𝓨}

/-- Against `ν₀`, the step kernel of a run against `ν` has the density of the likelihood ratio of
the observation of the round, when `ν a ≪ ν₀ a` for every arm. -/
lemma stepKernel_bandit_eq_withDensity (hac : ∀ a, ν a ≪ ν₀ a) (n : ℕ) :
    stepKernel alg (Environment.bandit ν) n = (stepKernel alg (Environment.bandit ν₀) n).withDensity
      (fun _ r ↦ armLikelihoodRatio ν ν₀ (r.action, r.feedback)) := by
  have hρ : Measurable (Function.uncurry fun (p : (Hist Unit α 𝓨 n × Unit) × α) (y : 𝓨) ↦
      armLikelihoodRatio ν ν₀ (p.2, y)) :=
    (measurable_armLikelihoodRatio ν ν₀).comp (measurable_fst.snd.prodMk measurable_snd)
  -- the feedback kernel against `ν` has density the likelihood ratio against `ν₀`
  have h_fb : ν.prodMkLeft (Hist Unit α 𝓨 n × Unit) = (ν₀.prodMkLeft _).withDensity
      (fun p y ↦ armLikelihoodRatio ν ν₀ (p.2, y)) := by
    ext p : 1
    rw [Kernel.withDensity_apply _ hρ, Kernel.prodMkLeft_apply, Kernel.prodMkLeft_apply]
    exact (withDensity_armLikelihoodRatio ν ν₀ (hac p.2)).symm
  have : IsMarkovKernel ((ν₀.prodMkLeft (Hist Unit α 𝓨 n × Unit)).withDensity
      (fun p y ↦ armLikelihoodRatio ν ν₀ (p.2, y))) := by
    rw [← h_fb]
    infer_instance
  -- the policy is common to both runs
  have h_inner : alg.policy n ⊗ₖ ν.prodMkLeft (Hist Unit α 𝓨 n × Unit) =
      (alg.policy n ⊗ₖ ν₀.prodMkLeft _).withDensity
        (fun p ay ↦ armLikelihoodRatio ν ν₀ (ay.1, ay.2)) := by
    rw [h_fb, Kernel.compProd_withDensity hρ]
  have : IsMarkovKernel ((alg.policy n ⊗ₖ ν₀.prodMkLeft (Hist Unit α 𝓨 n × Unit)).withDensity
      (fun p ay ↦ armLikelihoodRatio ν ν₀ (ay.1, ay.2))) := by
    rw [← h_inner]
    infer_instance
  -- `stepKernel alg (Environment.bandit ν₀) n` unfolds to the same composition with `ν₀`
  rw [stepKernel_bandit (ν := ν), h_inner]
  exact Kernel.compProd_withDensity
    ((measurable_armLikelihoodRatio ν ν₀).comp (measurable_snd.fst.prodMk measurable_snd.snd))

variable {Ω Ω₀ : Type*} {mΩ : MeasurableSpace Ω} {mΩ₀ : MeasurableSpace Ω₀}
  {P : Measure Ω} [IsProbabilityMeasure P] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨}
  {O₀ : ℕ → Ω₀ → Unit} {A₀ : ℕ → Ω₀ → α} {Y₀ : ℕ → Ω₀ → 𝓨}

/-- **Change of measure between two stochastic bandits.** Run the algorithm `alg` against the
stochastic bandits `ν` and `ν₀`, with `ν a ≪ ν₀ a` for every arm `a`. The law of the history of the
first `n` rounds against `ν` is the law of that history against `ν₀` with density the likelihood
ratio `∏_{t < n} (dν(a_t) / dν₀(a_t))(y_t)` of its observations. -/
lemma IsAlgEnvSeq.hasLaw_history_withDensity_bandit
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (h₀ : IsAlgEnvSeq O₀ A₀ Y₀ alg (Environment.bandit ν₀) P₀) (hac : ∀ a, ν a ≪ ν₀ a)
    (n : ℕ) : HasLaw (history O A Y n)
      ((P₀.map (history O₀ A₀ Y₀ n)).withDensity (histLikelihoodRatio ν ν₀ n)) P where
  aemeasurable := (h.measurable_history n).aemeasurable
  map_eq := by
    induction n with
    | zero =>
      rw [(hasLaw_history_zero O A Y).map_eq, (hasLaw_history_zero O₀ A₀ Y₀).map_eq,
        show histLikelihoodRatio ν ν₀ 0 = 1 from funext (histLikelihoodRatio_zero ν ν₀),
        withDensity_one]
    | succ n ih =>
      have hs := stepKernel_bandit_eq_withDensity (alg := alg) hac n
      have : IsMarkovKernel ((stepKernel alg (Environment.bandit ν₀) n).withDensity
          (fun _ r ↦ armLikelihoodRatio ν ν₀ (r.action, r.feedback))) := by
        rw [← hs]
        infer_instance
      simp_rw [history_succ]
      rw [← Measure.map_map (by fun_prop) (h.measurable_history n |>.prodMk (h.measurable_step n)),
        ← Measure.map_map (by fun_prop) (h₀.measurable_history n |>.prodMk
          (h₀.measurable_step n)),
        (h.hasCondDistrib_step n).map_eq, (h₀.hasCondDistrib_step n).map_eq, ih, hs,
        Measure.withDensity_compProd_withDensity (measurable_histLikelihoodRatio ν ν₀ n)
          (by fun_prop),
        map_equiv_withDensity (by fun_prop)]
      congr 1
      funext x
      simp [histLikelihoodRatio_succ]

omit [IsProbabilityMeasure P] [IsProbabilityMeasure P₀] in
/-- **The likelihood ratio identity at a stopping time.** Run the algorithm `alg` against the
stochastic bandits `ν` and `ν₀`, with `ν a ≪ ν₀ a` for every arm `a`, until the stopping rule `S`
stops. On the stopping rule, the law of the stopped history against `ν` is its law against `ν₀`
with density the likelihood ratio `∏_{t < τ} (dν(a_t) / dν₀(a_t))(y_t)` of the observations of the
stopped history: `E_ν[f(H_τ); τ < ∞] = E_{ν₀}[L_τ f(H_τ); τ < ∞]`. -/
theorem setLIntegral_stoppedHistMeasure_bandit_eq (hac : ∀ a, ν a ≪ ν₀ a)
    {S : Set (Σ n : ℕ, Hist Unit α 𝓨 n)} (hS : MeasurableSet S)
    {f : (Σ n : ℕ, Hist Unit α 𝓨 n) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in S, f x ∂stoppedHistMeasure alg (Environment.bandit ν) S =
      ∫⁻ x in S, histLikelihoodRatio ν ν₀ x.1 x.2 * f x
        ∂stoppedHistMeasure alg (Environment.bandit ν₀) S := by
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν)
  have hseq₀ := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν₀)
  have hLf : Measurable fun x : Σ n : ℕ, Hist Unit α 𝓨 n ↦ histLikelihoodRatio ν ν₀ x.1 x.2 * f x :=
    (measurable_sigma (f := fun x : Σ n : ℕ, Hist Unit α 𝓨 n ↦ histLikelihoodRatio ν ν₀ x.1 x.2)
      fun n ↦ measurable_histLikelihoodRatio ν ν₀ n).mul hf
  rw [hseq.setLIntegral_stoppedHistMeasure_eq_tsum hS hf,
    hseq₀.setLIntegral_stoppedHistMeasure_eq_tsum hS hLf]
  refine tsum_congr fun n ↦ ?_
  rw [(hseq.hasLaw_history_withDensity_bandit hseq₀ hac n).map_eq,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (g := fun x ↦ f ⟨n, x⟩)
      (measurable_histLikelihoodRatio ν ν₀ n) (hf.comp (measurable_sigmaMk n))
      ((measurableSet_notStoppedBeforeSet hS n).inter (measurable_sigmaMk n hS))]
  simp only [Pi.mul_apply]

end Learning

namespace LMLExplore

variable {α 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} {ν : Kernel α 𝓨}

/-- If the weighted sum of the log-likelihood ratios of the observations of a history against the
bandits `κ k` is at most `γ`, the mixture of the inverse likelihood ratios is at least `e^{-γ}`:
`1 ≤ e^γ ∑_k w_k / L_k(h)`. This is Jensen's inequality for the exponential, `e^{-∑ w_k log L_k} ≤
∑ w_k / L_k`, or the trivial bound when some `L_k(h)` of positive weight vanishes. -/
private lemma one_le_ofReal_exp_mul_sum_inv_histLikelihoodRatio {ι : Type*} {s : Finset ι}
    {w : ι → ℝ} (hw0 : ∀ k ∈ s, 0 ≤ w k) (hw1 : ∑ k ∈ s, w k = 1) (κ : ι → Kernel α 𝓨) {n : ℕ}
    {h : Hist Unit α 𝓨 n} {γ : ℝ}
    (hγ : ∑ t, ∑ k ∈ s, w k * llr (ν (h t).action) (κ k (h t).action) (h t).feedback ≤ γ) :
    1 ≤ ENNReal.ofReal (Real.exp γ) *
      ∑ k ∈ s, ENNReal.ofReal (w k) * (histLikelihoodRatio ν (κ k) n h)⁻¹ := by
  by_cases h0 : ∃ k ∈ s, 0 < w k ∧ histLikelihoodRatio ν (κ k) n h = 0
  · -- a likelihood ratio of positive weight vanishes: the mixture is infinite
    obtain ⟨k, hk, hwk, hL⟩ := h0
    have h_top : ∑ k ∈ s, ENNReal.ofReal (w k) * (histLikelihoodRatio ν (κ k) n h)⁻¹ = ∞ :=
      ENNReal.sum_eq_top.2 ⟨k, hk, by rw [hL, ENNReal.inv_zero,
        ENNReal.mul_top (ENNReal.ofReal_pos.2 hwk).ne']⟩
    rw [h_top, ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos γ)).ne']
    exact le_top
  simp only [not_exists, not_and] at h0
  set ℓ : ι → ℝ := fun k ↦ (histLikelihoodRatio ν (κ k) n h).toReal with hℓ
  have hℓpos (k : ι) (hk : k ∈ s) (hwk : 0 < w k) : 0 < ℓ k :=
    ENNReal.toReal_pos (h0 k hk hwk) (histLikelihoodRatio_ne_top _ _ n h)
  -- the logarithm of a positive likelihood ratio is the sum of the log-likelihood ratios
  have hlog (k : ι) (hk : k ∈ s) (hwk : 0 < w k) :
      Real.log (ℓ k) = ∑ t, llr (ν (h t).action) (κ k (h t).action) (h t).feedback := by
    have hne : ∏ t, (armLikelihoodRatio ν (κ k) ((h t).action, (h t).feedback)).toReal ≠ 0 := by
      rw [← ENNReal.toReal_prod, ← histLikelihoodRatio_def]
      exact (hℓpos k hk hwk).ne'
    simp only [hℓ]
    rw [histLikelihoodRatio_def, ENNReal.toReal_prod,
      Real.log_prod fun t _ ↦ Finset.prod_ne_zero_iff.1 hne t (Finset.mem_univ t)]
    simp only [toReal_armLikelihoodRatio, llr_def]
  have hwlog : ∑ k ∈ s, w k * Real.log (ℓ k) =
      ∑ t, ∑ k ∈ s, w k * llr (ν (h t).action) (κ k (h t).action) (h t).feedback := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rcases (hw0 k hk).eq_or_lt with hwk | hwk
    · simp [← hwk]
    · rw [hlog k hk hwk, Finset.mul_sum]
  -- Jensen's inequality for the exponential
  have hJ : Real.exp (-γ) ≤ ∑ k ∈ s, w k * (ℓ k)⁻¹ := by
    calc Real.exp (-γ) ≤ Real.exp (∑ k ∈ s, w k • (-Real.log (ℓ k))) := by
          refine Real.exp_le_exp.2 ?_
          simp only [smul_eq_mul, mul_neg, Finset.sum_neg_distrib, hwlog, neg_le_neg_iff, hγ]
    _ ≤ ∑ k ∈ s, w k • Real.exp (-Real.log (ℓ k)) :=
          convexOn_exp.map_sum_le hw0 hw1 fun _ _ ↦ Set.mem_univ _
    _ = ∑ k ∈ s, w k * (ℓ k)⁻¹ := by
          refine Finset.sum_congr rfl fun k hk ↦ ?_
          rcases (hw0 k hk).eq_or_lt with hwk | hwk
          · simp [← hwk]
          · rw [smul_eq_mul, Real.exp_neg, Real.exp_log (hℓpos k hk hwk)]
  have hsum : ∑ k ∈ s, ENNReal.ofReal (w k) * (histLikelihoodRatio ν (κ k) n h)⁻¹ =
      ENNReal.ofReal (∑ k ∈ s, w k * (ℓ k)⁻¹) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun k hk ↦ mul_nonneg (hw0 k hk)
      (inv_nonneg.2 ENNReal.toReal_nonneg)]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rcases (hw0 k hk).eq_or_lt with hwk | hwk
    · simp [← hwk]
    · rw [ENNReal.ofReal_mul (hw0 k hk), ENNReal.ofReal_inv_of_pos (hℓpos k hk hwk)]
      simp only [hℓ, ENNReal.ofReal_toReal (histLikelihoodRatio_ne_top _ _ n h)]
  rw [hsum, ← ENNReal.ofReal_mul (Real.exp_pos γ).le, ENNReal.one_le_ofReal]
  calc (1 : ℝ) = Real.exp γ * Real.exp (-γ) := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  _ ≤ _ := mul_le_mul_of_nonneg_left hJ (Real.exp_pos γ).le

end LMLExplore

namespace Learning

open LMLExplore

variable {α 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  [Countable α] [MeasurableSingletonClass α] {ν : Kernel α 𝓨} [IsMarkovKernel ν]
  {alg : Algorithm Unit α 𝓨}

/-- **Change of measure towards a mixture of bandits** [DK19, Lemma 19]. Run the algorithm `alg`
until the stopping rule `S` stops, against the stochastic bandit `ν` and against the bandits
`κ k`, `k ∈ s`, with `ν a ≪ κ k a` for every arm, and let `w` be weights on `s`. For every
measurable `φ ≥ 0` of the stopped history and every `γ`,
`E_ν[φ; τ < ∞] ≤ e^γ ∑_k w_k E_{κ k}[φ; τ < ∞] + E_ν[φ; τ < ∞, γ < Λ_τ]`, where
`Λ_τ = ∑_{t < τ} ∑_k w_k log (dν(a_t) / dκ_k(a_t))(y_t)` is the weighted log-likelihood ratio of
the stopped history. If `φ` is the indicator of an event of probability at most `δ` under every
`κ k`, the event has probability at most `e^γ δ + P_ν(γ < Λ_τ)` under `ν`. -/
theorem setLIntegral_stoppedHistMeasure_bandit_le {ι : Type*} {s : Finset ι} {w : ι → ℝ}
    (hw0 : ∀ k ∈ s, 0 ≤ w k) (hw1 : ∑ k ∈ s, w k = 1) (κ : ι → Kernel α 𝓨)
    [∀ k, IsMarkovKernel (κ k)] (hac : ∀ k ∈ s, ∀ a, ν a ≪ κ k a)
    {S : Set (Σ n : ℕ, Hist Unit α 𝓨 n)} (hS : MeasurableSet S)
    {φ : (Σ n : ℕ, Hist Unit α 𝓨 n) → ℝ≥0∞} (hφ : Measurable φ) (γ : ℝ) :
    ∫⁻ x in S, φ x ∂stoppedHistMeasure alg (Environment.bandit ν) S ≤
      ENNReal.ofReal (Real.exp γ) * ∑ k ∈ s, ENNReal.ofReal (w k) *
          ∫⁻ x in S, φ x ∂stoppedHistMeasure alg (Environment.bandit (κ k)) S +
        ∫⁻ x in S ∩ {x | γ < ∑ t, ∑ k ∈ s,
          w k * llr (ν (x.2 t).action) (κ k (x.2 t).action) (x.2 t).feedback},
          φ x ∂stoppedHistMeasure alg (Environment.bandit ν) S := by
  set Λ : (Σ n : ℕ, Hist Unit α 𝓨 n) → ℝ := fun x ↦ ∑ t, ∑ k ∈ s,
    w k * llr (ν (x.2 t).action) (κ k (x.2 t).action) (x.2 t).feedback with hΛ
  set G := {x : Σ n : ℕ, Hist Unit α 𝓨 n | γ < Λ x} with hG
  have hΛm : Measurable Λ := measurable_sigma_sum_round
    (g := fun a y ↦ ∑ k ∈ s, w k * llr (ν a) (κ k a) y) (measurable_sum_mul_llr ν κ s w)
  have hGm : MeasurableSet G := measurableSet_lt measurable_const hΛm
  have hL (k : ι) : Measurable fun x : Σ n : ℕ, Hist Unit α 𝓨 n ↦
      (histLikelihoodRatio ν (κ k) x.1 x.2)⁻¹ * φ x :=
    (measurable_sigma (f := fun x : Σ n : ℕ, Hist Unit α 𝓨 n ↦
      (histLikelihoodRatio ν (κ k) x.1 x.2)⁻¹) fun n ↦
        (measurable_histLikelihoodRatio ν (κ k) n).inv).mul hφ
  -- off `G`, `φ ≤ e^γ ∑_k w_k φ / L_k`
  have h_pt (x : Σ n : ℕ, Hist Unit α 𝓨 n) : φ x ≤ ENNReal.ofReal (Real.exp γ) *
      ∑ k ∈ s, ENNReal.ofReal (w k) * ((histLikelihoodRatio ν (κ k) x.1 x.2)⁻¹ * φ x) +
        G.indicator φ x := by
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx]
      exact le_add_self
    · rw [Set.indicator_of_notMem hx, add_zero]
      simp_rw [← mul_assoc, ← Finset.sum_mul, ← mul_assoc]
      exact le_mul_of_one_le_left' (one_le_ofReal_exp_mul_sum_inv_histLikelihoodRatio hw0 hw1 κ
        (not_lt.1 hx))
  -- under `ν`, `φ / L_k` integrates to at most the integral of `φ` under `κ k`
  have h_k (k : ι) (hk : k ∈ s) :
      ∫⁻ x in S, (histLikelihoodRatio ν (κ k) x.1 x.2)⁻¹ * φ x
          ∂stoppedHistMeasure alg (Environment.bandit ν) S ≤
        ∫⁻ x in S, φ x ∂stoppedHistMeasure alg (Environment.bandit (κ k)) S := by
    rw [setLIntegral_stoppedHistMeasure_bandit_eq (hac k hk) hS (hL k)]
    refine setLIntegral_mono hφ fun x _ ↦ ?_
    rw [← mul_assoc]
    exact mul_le_of_le_one_left' (ENNReal.mul_inv_le_one _)
  calc ∫⁻ x in S, φ x ∂stoppedHistMeasure alg (Environment.bandit ν) S
  _ ≤ ∫⁻ x in S, (ENNReal.ofReal (Real.exp γ) *
        ∑ k ∈ s, ENNReal.ofReal (w k) * ((histLikelihoodRatio ν (κ k) x.1 x.2)⁻¹ * φ x) +
          G.indicator φ x) ∂stoppedHistMeasure alg (Environment.bandit ν) S :=
      lintegral_mono h_pt
  _ = ENNReal.ofReal (Real.exp γ) * ∑ k ∈ s, ENNReal.ofReal (w k) *
        ∫⁻ x in S, (histLikelihoodRatio ν (κ k) x.1 x.2)⁻¹ * φ x
          ∂stoppedHistMeasure alg (Environment.bandit ν) S +
        ∫⁻ x in S ∩ G, φ x ∂stoppedHistMeasure alg (Environment.bandit ν) S := by
      have hm_sum : Measurable fun x ↦ ∑ k ∈ s, ENNReal.ofReal (w k) *
          ((histLikelihoodRatio ν (κ k) x.1 x.2)⁻¹ * φ x) :=
        Finset.measurable_sum _ fun k _ ↦ (hL k).const_mul _
      rw [lintegral_add_right _ (hφ.indicator hGm), lintegral_const_mul _ hm_sum,
        lintegral_finsetSum _ fun k _ ↦ (hL k).const_mul _, lintegral_indicator hGm,
        Measure.restrict_restrict hGm, Set.inter_comm]
      simp_rw [lintegral_const_mul _ (hL _)]
  _ ≤ _ := add_le_add_left (mul_le_mul_right
      (Finset.sum_le_sum fun k hk ↦ mul_le_mul_right (h_k k hk) _) _) _

end Learning
