/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.Bandit.Regret
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import LMLExplore.Probability.Distributions.Gaussian.Real
public import LMLExplore.Probability.Martingale.ConfidenceEllipsoid

/-!
# Stochastic linear bandits

In a stochastic linear bandit [LS, §19.2], the learner observes at round `t` a context
`O t ∈ 𝓞`, plays an action `A t ∈ 𝓐` and receives a reward whose mean is linear in a feature
of the context and the action: with a feature map `φ : 𝓞 → 𝓐 → E` into a real inner product
space and an unknown parameter `θ : E`, the reward is `⟪θ, φ (O t) (A t)⟫ + η t` for a noise
`η t` that is conditionally σ²-sub-Gaussian given the past, the context and the action. This
covers finitely many arms (`φ` one-hot), a fixed action set (`𝓞` a single point) and decision
sets `φ (O t) '' univ` that change from round to round.

The predicate `IsSubgaussianLinearEnv φ θ σ2 env` states this of an LML environment `env`: at
every round, whatever the history, the context `o` and the action `a`, the feedback law minus
`⟪θ, φ o a⟫` is σ²-sub-Gaussian. Along every run of an algorithm in such an environment, the
noise `Y t - ⟪θ, φ (O t) (A t)⟫` is then conditionally σ²-sub-Gaussian given the σ-algebra of
the history, the context and the action of round `t`, so the confidence ellipsoids of ridge
regression [LS, Theorem 20.5] hold for the features `φ (O t) (A t)` and the rewards `Y t` of
the run. These are the confidence sets of the optimistic algorithm OFUL.

The random regret after `n` rounds is
`R̂_n = ∑_{t < n} (sup_a ⟪θ, φ (O t) a⟫ - ⟪θ, φ (O t) (A t)⟫)`, and the expected regret of a run
under `P` is `P[linearRegret φ θ O A n]`, as LML writes `P[regret ν A n]` for stochastic
bandits. The supremum is the real `iSup`, which is meaningful when the expected rewards of the
actions are bounded above at every context, for example for finitely many actions or bounded
features.

## Main definitions

* `LMLExplore.Bandits.IsSubgaussianLinearEnv φ θ σ2 env`: `env` is a linear bandit environment
  with features `φ`, parameter `θ` and σ²-sub-Gaussian noise.
* `LMLExplore.Bandits.histFeature φ h`, `LMLExplore.Bandits.histReward h`: the features and the
  rewards of the rounds of a history, as sequences.
* `LMLExplore.Bandits.linearRegret φ θ O A n`: the random regret `R̂_n` of the actions `A` in
  the contexts `O`.
* `LMLExplore.Bandits.gaussianLinearKernel φ θ σ2 hφ`: the kernel `(o, a) ↦ 𝒩(⟪θ, φ o a⟫, σ2)`.
* `LMLExplore.Bandits.gaussianLinearEnv μ φ θ σ2 hφ`: the Gaussian linear environment, with
  i.i.d. contexts of law `μ` and Gaussian rewards of variance `σ2`.

## Main statements

* `Learning.IsAlgEnvSeq.hasCondSubgaussianMGF_feedback_sub_inner`: along a run in a linear
  environment, the noise of round `t` is conditionally σ²-sub-Gaussian given
  `h.filtrationAction t`.
* `Learning.IsAlgEnvSeq.le_measureReal_forall_sqrt_inner_ridgeEstimate_sub_lt`: the confidence
  ellipsoids of ridge regression along a run [LS, Theorem 20.5], and
  `Learning.IsAlgEnvSeq.le_measureReal_forall_sqrt_inner_ridgeEstimate_sub_lt_of_norm_le` their
  form for bounded features [LS, Theorem 20.5 and (20.9)];
  `Learning.IsAlgEnvSeq.measure_exists_sqrt_inner_ridgeEstimate_sub_ge_le_of_norm_le` the bound
  on the probability that the latter fail.
* `nonneg_of_gap`, `bddAbove_range_inner_of_gap`, `iSup_inner_sub_inner_le_of_gap`: if the gaps
  between the expected rewards of the actions and that of an action `b` are at most `G`, then
  `0 ≤ G`, the expected rewards are bounded above and `sup_a ⟪θ, f a⟫ - ⟪θ, f b⟫ ≤ G`.
* `linearRegret_nonneg`, `linearRegret_le_mul`: the random regret is nonnegative, and at most
  `n G` after `n` rounds when the gaps between the expected rewards of the actions are at most `G`.
* `isSubgaussianLinearEnv_gaussianLinearEnv`: the Gaussian linear environment is linear with
  σ²-sub-Gaussian noise.
* `isSubgaussianLinearEnv_bandit`, `linearRegret_single_eq_regret`: a stochastic bandit with
  finitely many σ²-sub-Gaussian arms is a linear bandit with the one-hot features
  `a ↦ EuclideanSpace.single a 1` and the vector of means as parameter, and its linear regret is
  LML's `regret`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 19.2 and Theorem 20.5.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Module Learning Bandits
open scoped ENNReal NNReal InnerProductSpace

namespace LMLExplore.Bandits

variable {𝓞 𝓐 E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {mΩ : MeasurableSpace Ω}
  {φ : 𝓞 → 𝓐 → E} {θ : E} {σ2 : ℝ≥0}

section Environment

variable [MeasurableSpace 𝓞] [MeasurableSpace 𝓐] {env : Environment 𝓞 𝓐 ℝ}

/-- A **linear bandit environment** with features `φ : 𝓞 → 𝓐 → E`, parameter `θ : E` and
σ²-sub-Gaussian noise [LS, §19.2]: at every round `n`, whatever the history `h`, the context `o`
and the action `a`, the feedback law `env.feedback n ((h, o), a)` is σ²-sub-Gaussian around the
expected reward `⟪θ, φ o a⟫`. -/
def IsSubgaussianLinearEnv (φ : 𝓞 → 𝓐 → E) (θ : E) (σ2 : ℝ≥0) (env : Environment 𝓞 𝓐 ℝ) :
    Prop :=
  ∀ (n : ℕ) (h : Hist 𝓞 𝓐 ℝ n) (o : 𝓞) (a : 𝓐),
    HasSubgaussianMGF (fun y ↦ y - ⟪θ, φ o a⟫_ℝ) σ2 (env.feedback n ((h, o), a))

lemma isSubgaussianLinearEnv_iff :
    IsSubgaussianLinearEnv φ θ σ2 env ↔ ∀ (n : ℕ) (h : Hist 𝓞 𝓐 ℝ n) (o : 𝓞) (a : 𝓐),
      HasSubgaussianMGF (fun y ↦ y - ⟪θ, φ o a⟫_ℝ) σ2 (env.feedback n ((h, o), a)) :=
  Iff.rfl

/-- In a linear bandit environment, the feedback law of every round is σ²-sub-Gaussian around the
expected reward of the context and the action. -/
lemma IsSubgaussianLinearEnv.hasSubgaussianMGF (henv : IsSubgaussianLinearEnv φ θ σ2 env)
    (n : ℕ) (h : Hist 𝓞 𝓐 ℝ n) (o : 𝓞) (a : 𝓐) :
    HasSubgaussianMGF (fun y ↦ y - ⟪θ, φ o a⟫_ℝ) σ2 (env.feedback n ((h, o), a)) :=
  isSubgaussianLinearEnv_iff.1 henv n h o a

end Environment

section History

omit [InnerProductSpace ℝ E] in
/-- The features `φ o a` of the rounds `s < n` of a history `h` of length `n`, as a sequence
extended by `0` from round `n` on. -/
noncomputable def histFeature (φ : 𝓞 → 𝓐 → E) {n : ℕ} (h : Hist 𝓞 𝓐 ℝ n) (s : ℕ) : E :=
  if hs : s < n then φ (h ⟨s, hs⟩).obs (h ⟨s, hs⟩).action else 0

omit [InnerProductSpace ℝ E] in
lemma histFeature_def {n : ℕ} (h : Hist 𝓞 𝓐 ℝ n) (s : ℕ) :
    histFeature φ h s = if hs : s < n then φ (h ⟨s, hs⟩).obs (h ⟨s, hs⟩).action else 0 :=
  (rfl)

/-- The rewards of the rounds `s < n` of a history `h` of length `n`, as a sequence extended by
`0` from round `n` on. -/
noncomputable def histReward {n : ℕ} (h : Hist 𝓞 𝓐 ℝ n) (s : ℕ) : ℝ :=
  if hs : s < n then (h ⟨s, hs⟩).feedback else 0

lemma histReward_def {n : ℕ} (h : Hist 𝓞 𝓐 ℝ n) (s : ℕ) :
    histReward h s = if hs : s < n then (h ⟨s, hs⟩).feedback else 0 :=
  (rfl)

omit [InnerProductSpace ℝ E] in
@[simp]
lemma histFeature_history {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {n s : ℕ}
    (hs : s < n) (ω : Ω) :
    histFeature φ (history O A Y n ω) s = φ (O s ω) (A s ω) := by
  simp [histFeature_def, hs, history_apply]

@[simp]
lemma histReward_history {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {n s : ℕ}
    (hs : s < n) (ω : Ω) :
    histReward (history O A Y n ω) s = Y s ω := by
  simp [histReward_def, hs, history_apply]

end History

section Run

variable [MeasurableSpace 𝓞] [MeasurableSpace 𝓐] {env : Environment 𝓞 𝓐 ℝ} {P : Measure Ω}
  {alg : Algorithm 𝓞 𝓐 ℝ} {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ}

/-- **The noise of a run is conditionally sub-Gaussian.** Along a run of an algorithm in a linear
bandit environment with σ²-sub-Gaussian noise, the noise `Y n - ⟪θ, φ (O n) (A n)⟫` of round `n`
is conditionally σ²-sub-Gaussian given the σ-algebra `h.filtrationAction n` of the history, the
context and the action of round `n`. -/
theorem _root_.Learning.IsAlgEnvSeq.hasCondSubgaussianMGF_feedback_sub_inner
    [StandardBorelSpace Ω] [IsFiniteMeasure P]
    (h : IsAlgEnvSeq O A Y alg env P) (henv : IsSubgaussianLinearEnv φ θ σ2 env)
    (hφ : Measurable fun p : 𝓞 × 𝓐 ↦ ⟪θ, φ p.1 p.2⟫_ℝ) (n : ℕ) :
    HasCondSubgaussianMGF (h.filtrationAction n) (h.filtrationAction.le n)
      (fun ω ↦ Y n ω - ⟪θ, φ (O n ω) (A n ω)⟫_ℝ) σ2 P := by
  convert (h.hasCondDistrib_feedback n).hasCondSubgaussianMGF_sub
    (((h.measurable_history n).prodMk (h.measurable_obs n)).prodMk (h.measurable_action n))
    (hφ.comp (measurable_fst.snd.prodMk measurable_snd))
    (ae_of_all _ fun p ↦ henv.hasSubgaussianMGF n p.1.1 p.1.2 p.2) using 1
  exacts [h.filtrationAction_eq_comap n, rfl]

/-- The features and the noises of a run in a linear bandit environment satisfy the
measurability and the noise assumptions of the confidence ellipsoids of ridge regression, for the
filtration `h.filtrationAction`. -/
private lemma measurable_features_noise [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (θ : E) (h : IsAlgEnvSeq O A Y alg env P)
    (hφ' : Measurable (Function.uncurry φ)) (t : ℕ) :
    Measurable[h.filtrationAction t] (fun ω ↦ φ (O t ω) (A t ω)) ∧
      Measurable[h.filtrationAction (t + 1)] (fun ω ↦ Y t ω - ⟪θ, φ (O t ω) (A t ω)⟫_ℝ) := by
  have hx (t : ℕ) : Measurable[h.filtrationAction t] (fun ω ↦ φ (O t ω) (A t ω)) :=
    hφ'.comp ((h.adapted_obs_filtrationAction t).prodMk (h.adapted_action_filtrationAction t))
  refine ⟨hx t, (h.measurable_feedback_filtrationAction_of_lt t.lt_succ_self).sub ?_⟩
  exact ((hx t).mono (h.filtrationAction.mono t.le_succ) le_rfl).const_inner

variable [StandardBorelSpace Ω] [IsProbabilityMeasure P] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {lam δ : ℝ}

/-- **Confidence ellipsoids along a run** [LS, Theorem 20.5]. Along a run of any algorithm in a
linear bandit environment with σ²-sub-Gaussian noise, `σ² ≠ 0`, let `V_t = designOp (λ • 1) x t` and
`θ̂_t = ridgeEstimate λ x Y t` be the design operator and the ridge estimate of the features
`x s = φ (O s) (A s)` and the rewards `Y s` of the rounds `s < t`. For `λ > 0` and `δ > 0`, with
probability at least `1 - δ`, for all `t`,
`‖θ̂_t - θ‖_{V_t} < √λ ‖θ‖ + √(2σ² log (1 / δ) + σ² log (det V_t / λ ^ d))`. -/
theorem _root_.Learning.IsAlgEnvSeq.le_measureReal_forall_sqrt_inner_ridgeEstimate_sub_lt
    (h : IsAlgEnvSeq O A Y alg env P) (henv : IsSubgaussianLinearEnv φ θ σ2 env)
    (hφ : Measurable (Function.uncurry φ)) (hσ : σ2 ≠ 0) (hlam : 0 < lam) (hδ : 0 < δ) :
    1 - δ ≤ P.real {ω | ∀ t,
      √⟪ridgeEstimate lam (fun s ↦ φ (O s ω) (A s ω)) (fun s ↦ Y s ω) t - θ,
        designOp (lam • 1) (fun s ↦ φ (O s ω) (A s ω)) t
          (ridgeEstimate lam (fun s ↦ φ (O s ω) (A s ω)) (fun s ↦ Y s ω) t - θ)⟫_ℝ <
      √lam * ‖θ‖ + √(2 * σ2 * log (1 / δ) +
        σ2 * log (LinearMap.det (designOp (lam • 1) (fun s ↦ φ (O s ω) (A s ω)) t : E →ₗ[ℝ] E) /
          lam ^ finrank ℝ E))} :=
  LMLExplore.le_measureReal_forall_sqrt_inner_ridgeEstimate_sub_lt
    (fun t ↦ (measurable_features_noise θ h hφ t).1)
    (fun t ↦ (measurable_features_noise θ h hφ t).2)
    (h.hasCondSubgaussianMGF_feedback_sub_inner henv (by fun_prop)) hσ θ
    (fun _ _ ↦ (add_sub_cancel _ _).symm) hlam hδ

/-- **Confidence ellipsoids along a run, for bounded features** [LS, Theorem 20.5 and (20.9)].
Under the assumptions of
`Learning.IsAlgEnvSeq.le_measureReal_forall_sqrt_inner_ridgeEstimate_sub_lt`, if moreover
`‖φ o a‖ ≤ L` for all contexts `o` and actions `a`, then with probability at least `1 - δ`, for
all `t`,
`‖θ̂_t - θ‖_{V_t} < √λ ‖θ‖ + √(2σ² log (1 / δ) + σ² d log (1 + t L² / (λ d)))`. -/
theorem _root_.Learning.IsAlgEnvSeq.le_measureReal_forall_sqrt_inner_ridgeEstimate_sub_lt_of_norm_le
    (h : IsAlgEnvSeq O A Y alg env P) (henv : IsSubgaussianLinearEnv φ θ σ2 env)
    (hφ : Measurable (Function.uncurry φ)) (hσ : σ2 ≠ 0) {L : ℝ} (hL : ∀ o a, ‖φ o a‖ ≤ L)
    (hlam : 0 < lam) (hδ : 0 < δ) :
    1 - δ ≤ P.real {ω | ∀ t,
      √⟪ridgeEstimate lam (fun s ↦ φ (O s ω) (A s ω)) (fun s ↦ Y s ω) t - θ,
        designOp (lam • 1) (fun s ↦ φ (O s ω) (A s ω)) t
          (ridgeEstimate lam (fun s ↦ φ (O s ω) (A s ω)) (fun s ↦ Y s ω) t - θ)⟫_ℝ <
      √lam * ‖θ‖ + √(2 * σ2 * log (1 / δ) +
        σ2 * finrank ℝ E * log (1 + t * L ^ 2 / (lam * finrank ℝ E)))} :=
  LMLExplore.le_measureReal_forall_sqrt_inner_ridgeEstimate_sub_lt_of_norm_le
    (fun t ↦ (measurable_features_noise θ h hφ t).1)
    (fun t ↦ (measurable_features_noise θ h hφ t).2)
    (h.hasCondSubgaussianMGF_feedback_sub_inner henv (by fun_prop)) hσ θ
    (fun _ _ ↦ (add_sub_cancel _ _).symm) (fun _ _ ↦ hL _ _) hlam hδ

/-- **Confidence ellipsoids along a run, for bounded features** [LS, Theorem 20.5 and (20.9)],
failure-probability form: under the assumptions of
`Learning.IsAlgEnvSeq.le_measureReal_forall_sqrt_inner_ridgeEstimate_sub_lt_of_norm_le`, the
probability that for some `t`,
`√λ ‖θ‖ + √(2σ² log (1 / δ) + σ² d log (1 + t L² / (λ d))) ≤ ‖θ̂_t - θ‖_{V_t}` is at most `δ`. -/
theorem _root_.Learning.IsAlgEnvSeq.measure_exists_sqrt_inner_ridgeEstimate_sub_ge_le_of_norm_le
    (h : IsAlgEnvSeq O A Y alg env P) (henv : IsSubgaussianLinearEnv φ θ σ2 env)
    (hφ : Measurable (Function.uncurry φ)) (hσ : σ2 ≠ 0) {L : ℝ} (hL : ∀ o a, ‖φ o a‖ ≤ L)
    (hlam : 0 < lam) (hδ : 0 < δ) :
    P {ω | ∃ t : ℕ, √lam * ‖θ‖ + √(2 * σ2 * log (1 / δ) +
        σ2 * finrank ℝ E * log (1 + t * L ^ 2 / (lam * finrank ℝ E))) ≤
      √⟪ridgeEstimate lam (fun s ↦ φ (O s ω) (A s ω)) (fun s ↦ Y s ω) t - θ,
        designOp (lam • 1) (fun s ↦ φ (O s ω) (A s ω)) t
          (ridgeEstimate lam (fun s ↦ φ (O s ω) (A s ω)) (fun s ↦ Y s ω) t - θ)⟫_ℝ} ≤
      ENNReal.ofReal δ :=
  LMLExplore.measure_exists_sqrt_inner_ridgeEstimate_sub_ge_le_of_norm_le
    (fun t ↦ (measurable_features_noise θ h hφ t).1)
    (fun t ↦ (measurable_features_noise θ h hφ t).2)
    (h.hasCondSubgaussianMGF_feedback_sub_inner henv (by fun_prop)) hσ θ
    (fun _ _ ↦ (add_sub_cancel _ _).symm) (fun _ _ ↦ hL _ _) hlam hδ

end Run

section Regret

variable {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {n : ℕ} {ω : Ω}

/-- The **random regret** of a linear bandit [LS, §19.2] after `n` rounds, for the features `φ`,
the parameter `θ`, the contexts `O` and the actions `A`:
`∑_{t < n} (sup_a ⟪θ, φ (O t) a⟫ - ⟪θ, φ (O t) (A t)⟫)`, the total shortfall of the expected
rewards of the actions played against the best action of each context. The supremum is the real
`iSup`, meaningful when the expected rewards at every context are bounded above. -/
noncomputable def linearRegret (φ : 𝓞 → 𝓐 → E) (θ : E) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → 𝓐)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ range n, ((⨆ a, ⟪θ, φ (O t ω) a⟫_ℝ) - ⟪θ, φ (O t ω) (A t ω)⟫_ℝ)

lemma linearRegret_def :
    linearRegret φ θ O A n ω =
      ∑ t ∈ range n, ((⨆ a, ⟪θ, φ (O t ω) a⟫_ℝ) - ⟪θ, φ (O t ω) (A t ω)⟫_ℝ) :=
  (rfl)

@[simp]
lemma linearRegret_zero : linearRegret φ θ O A 0 ω = 0 := by
  simp [linearRegret_def]

lemma linearRegret_add_one :
    linearRegret φ θ O A (n + 1) ω =
      linearRegret φ θ O A n ω + ((⨆ a, ⟪θ, φ (O n ω) a⟫_ℝ) - ⟪θ, φ (O n ω) (A n ω)⟫_ℝ) := by
  rw [linearRegret_def, linearRegret_def, sum_range_succ]

/-- The random regret is nonnegative when the expected rewards at every context are bounded
above, for example for finitely many actions. -/
lemma linearRegret_nonneg (hbdd : ∀ o, BddAbove (Set.range fun a ↦ ⟪θ, φ o a⟫_ℝ)) :
    0 ≤ linearRegret φ θ O A n ω :=
  sum_nonneg fun t _ ↦ sub_nonneg.2 (le_ciSup (hbdd (O t ω)) (A t ω))

/-- If the gaps `⟪θ, f a⟫ - ⟪θ, f b⟫` between the expected rewards of the actions and that of an
action `b` are at most `G`, then the expected rewards are bounded above. -/
lemma bddAbove_range_inner_of_gap {f : 𝓐 → E} {b : 𝓐} {G : ℝ}
    (hgap : ∀ a, ⟪θ, f a⟫_ℝ - ⟪θ, f b⟫_ℝ ≤ G) :
    BddAbove (Set.range fun a ↦ ⟪θ, f a⟫_ℝ) :=
  ⟨G + ⟪θ, f b⟫_ℝ, by rintro _ ⟨a, rfl⟩; linarith [hgap a]⟩

/-- If the gaps `⟪θ, f a⟫ - ⟪θ, f b⟫` between the expected rewards of the actions and that of an
action `b` are at most `G`, then `G` is nonnegative. -/
lemma nonneg_of_gap {f : 𝓐 → E} {b : 𝓐} {G : ℝ} (hgap : ∀ a, ⟪θ, f a⟫_ℝ - ⟪θ, f b⟫_ℝ ≤ G) :
    0 ≤ G := by
  simpa using hgap b

/-- If the gaps `⟪θ, f a⟫ - ⟪θ, f b⟫` between the expected rewards of the actions and that of an
action `b` are at most `G`, then so is the gap `sup_a ⟪θ, f a⟫ - ⟪θ, f b⟫`. -/
lemma iSup_inner_sub_inner_le_of_gap {f : 𝓐 → E} {b : 𝓐} {G : ℝ}
    (hgap : ∀ a, ⟪θ, f a⟫_ℝ - ⟪θ, f b⟫_ℝ ≤ G) :
    (⨆ a, ⟪θ, f a⟫_ℝ) - ⟪θ, f b⟫_ℝ ≤ G :=
  have : Nonempty 𝓐 := ⟨b⟩
  sub_le_iff_le_add.2 (ciSup_le fun a ↦ sub_le_iff_le_add.1 (hgap a))

/-- If the gaps between the expected rewards of two actions are at most `G` at every context, then
the random regret after `n` rounds is at most `n G`. -/
lemma linearRegret_le_mul {G : ℝ} (hgap : ∀ o a b, ⟪θ, φ o a⟫_ℝ - ⟪θ, φ o b⟫_ℝ ≤ G) :
    linearRegret φ θ O A n ω ≤ n * G := by
  simpa [linearRegret_def] using
    sum_le_sum fun t (_ : t ∈ range n) ↦ iSup_inner_sub_inner_le_of_gap (hgap (O t ω) · (A t ω))

end Regret

section Gaussian

variable [MeasurableSpace 𝓞] [MeasurableSpace 𝓐]

/-- The Markov kernel `(o, a) ↦ 𝒩(⟪θ, φ o a⟫, σ2)` of Gaussian rewards with mean linear in the
features `φ o a`. -/
noncomputable def gaussianLinearKernel (φ : 𝓞 → 𝓐 → E) (θ : E) (σ2 : ℝ≥0)
    (hφ : Measurable fun p : 𝓞 × 𝓐 ↦ ⟪θ, φ p.1 p.2⟫_ℝ) : Kernel (𝓞 × 𝓐) ℝ where
  toFun p := gaussianReal ⟪θ, φ p.1 p.2⟫_ℝ σ2
  measurable' := measurable_gaussianReal.comp (hφ.prodMk measurable_const)

variable {hφ : Measurable fun p : 𝓞 × 𝓐 ↦ ⟪θ, φ p.1 p.2⟫_ℝ}

@[simp]
lemma gaussianLinearKernel_apply (p : 𝓞 × 𝓐) :
    gaussianLinearKernel φ θ σ2 hφ p = gaussianReal ⟪θ, φ p.1 p.2⟫_ℝ σ2 :=
  (rfl)

instance : IsMarkovKernel (gaussianLinearKernel φ θ σ2 hφ) :=
  ⟨fun p ↦ by rw [gaussianLinearKernel_apply]; infer_instance⟩

variable {μ : Measure 𝓞} [IsProbabilityMeasure μ]

/-- The **Gaussian linear environment**: the contexts are i.i.d. with law `μ`, and the reward of
the action `a` in the context `o` has law `𝒩(⟪θ, φ o a⟫, σ2)`, whatever the past. -/
noncomputable def gaussianLinearEnv (μ : Measure 𝓞) [IsProbabilityMeasure μ] (φ : 𝓞 → 𝓐 → E)
    (θ : E) (σ2 : ℝ≥0) (hφ : Measurable fun p : 𝓞 × 𝓐 ↦ ⟪θ, φ p.1 p.2⟫_ℝ) :
    Environment 𝓞 𝓐 ℝ :=
  Environment.stationary μ (gaussianLinearKernel φ θ σ2 hφ)

lemma gaussianLinearEnv_def :
    gaussianLinearEnv μ φ θ σ2 hφ = Environment.stationary μ (gaussianLinearKernel φ θ σ2 hφ) :=
  (rfl)

instance : (gaussianLinearEnv μ φ θ σ2 hφ).IsStationary :=
  inferInstanceAs (Environment.stationary μ (gaussianLinearKernel φ θ σ2 hφ)).IsStationary

instance : (gaussianLinearEnv μ φ θ σ2 hφ).IsOblivious :=
  inferInstanceAs (Environment.stationary μ (gaussianLinearKernel φ θ σ2 hφ)).IsOblivious

@[simp]
lemma obs_gaussianLinearEnv (n : ℕ) :
    (gaussianLinearEnv μ φ θ σ2 hφ).obs n = Kernel.const _ μ := by
  rw [gaussianLinearEnv_def, obs_stationary]

@[simp]
lemma feedback_gaussianLinearEnv_apply (n : ℕ) (h : Hist 𝓞 𝓐 ℝ n) (o : 𝓞) (a : 𝓐) :
    (gaussianLinearEnv μ φ θ σ2 hφ).feedback n ((h, o), a) = gaussianReal ⟪θ, φ o a⟫_ℝ σ2 := by
  rw [gaussianLinearEnv_def, feedback_stationary, Kernel.comap_apply, gaussianLinearKernel_apply]

/-- The Gaussian linear environment is a linear bandit environment with σ²-sub-Gaussian noise. -/
theorem isSubgaussianLinearEnv_gaussianLinearEnv :
    IsSubgaussianLinearEnv φ θ σ2 (gaussianLinearEnv μ φ θ σ2 hφ) := fun n h o a ↦ by
  rw [feedback_gaussianLinearEnv_apply]
  exact hasSubgaussianMGF_sub_of_hasLaw_gaussianReal HasLaw.id

end Gaussian

section OneHot

variable {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α] {ν : Kernel α ℝ}

/-- **Finitely many arms as a linear bandit.** A stochastic bandit `ν` with finitely many
σ²-sub-Gaussian arms is a linear bandit with the one-hot features `a ↦ EuclideanSpace.single a 1`
and the vector of the means of the arms as parameter. -/
theorem isSubgaussianLinearEnv_bandit [IsMarkovKernel ν]
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) :
    IsSubgaussianLinearEnv (fun (_ : Unit) a ↦ EuclideanSpace.single a (1 : ℝ))
      (WithLp.toLp 2 fun a ↦ (ν a)[id]) σ2 (Environment.bandit ν) := fun n h o a ↦ by
  simpa [feedback_bandit, EuclideanSpace.inner_single_right] using hν a

/-- With the one-hot features and the vector of the means as parameter, the random regret of a
linear bandit is LML's `regret` of the stochastic bandit `ν`. -/
theorem linearRegret_single_eq_regret (O : ℕ → Ω → Unit) (A : ℕ → Ω → α) (n : ℕ) (ω : Ω) :
    linearRegret (fun (_ : Unit) a ↦ EuclideanSpace.single a (1 : ℝ))
      (WithLp.toLp 2 fun a ↦ (ν a)[id]) O A n ω = regret ν A n ω := by
  simp [linearRegret_def, regret_eq_sum_gap, gap, EuclideanSpace.inner_single_right]

end OneHot

end LMLExplore.Bandits
