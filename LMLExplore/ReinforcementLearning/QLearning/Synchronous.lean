/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.Online.Bandit.ArrayProbSpace
public import LMLExplore.MarkovDecisionProcess.Optimality
public import LMLExplore.Probability.Process.Filtration
public import LMLExplore.ReinforcementLearning.LearningRate
public import Mathlib.Probability.Moments.Variance
import LMLExplore.MeasureTheory.MeasurableSpace.Constructions
import TauCeti.Probability.Independence.CondExp

/-!
# Synchronous Q-learning on the generative model

Synchronous Q-learning estimates the optimal action value `Q*` of an MDP from a generative model,
which draws at every iteration one fresh next state for every state-action pair. The samples form
an array `ω : ℕ → 𝓢 × 𝓐 → 𝓢`, whose entry `ω t p` is the next state drawn from `P p` at iteration
`t + 1`; under the generative model the array has law `Bandits.streamMeasure P`. With known rewards
`r`, a discount `γ` and learning rates `η`, iteration `t + 1` updates every pair `p` towards the
empirical Bellman target of the `t`-th sample:
`Q (t + 1) p = (1 - η (t + 1)) * Q t p + η (t + 1) * (r p + γ * ⨆ a, Q t (ω t p, a))`.
Synchronous TD learning, which estimates the value of a Markov reward process, is the case of one
action.

This file develops the elementary facts on which the sample complexity analysis of [LCCWC24]
rests. Write `V t s = ⨆ a, Q t (s, a)` for the value estimates, `Δ t = Q t - Q*` for the errors,
`P V` for the one-step prediction `p ↦ ∫ V dP p`, `P^π Δ` for `p ↦ ∫ s', Δ (s', π s') dP p` and
`P_{t+1} V` for the empirical prediction `p ↦ V (ω t p)`.
* The iterate `Q t` only depends on the first `t` samples; for finite state and action spaces, it
  takes finitely many values and is measurable for the strict past of the sample sequence.
* **Ranges** [LCCWC24, Lemma 4]: for learning rates in `[0, 1]`, rewards in `[0, C]` and
  `0 ≤ Q₀ ≤ C / (1 - γ)`, the iterates stay in `[0, C / (1 - γ)]`, and `|Q t - Q*| ≤ C / (1 - γ)`;
  the source has `C = 1`.
* **The error recursion** [LCCWC24, (32)–(35)]:
  `Δ (t + 1) = (1 - η (t + 1)) Δ t + η (t + 1) γ (P (V t - V*) + (P_{t+1} - P) V t)`, where
  `P^{π*} Δ t ≤ P (V t - V*) ≤ P^{π t} Δ t` for policies `π t` greedy for `Q t` and `π*` greedy for
  `Q*`. Unrolled with the learning-rate weights `η^i_t`, these give upper and lower bounds on
  `Δ t` by `(∏_{j ≤ t} (1 - η j)) Δ 0` plus a weighted sum of the previous errors and of the
  sampling noises `(P_i - P) V (i - 1)`. With one action both bounds are the same equality, the
  error recursion of TD learning [LCCWC24, (110)].
* **The sampling noise** is a martingale difference sequence: under the generative model, given the
  first `t` samples, the conditional mean of `V t (ω t p)` is `P V t p` and its conditional variance
  is the variance of `V t` under `P p`.

## Main definitions

* `LMLExplore.ReinforcementLearning.syncQLearning r γ η Q₀ t ω`: the `t`-th iterate of synchronous
  Q-learning with rewards `r`, discount `γ`, learning rates `η` and initial value `Q₀`, on the
  samples `ω`.

## Main statements

* `LMLExplore.ReinforcementLearning.syncQLearning_succ_of_unique`: with one action, the iteration
  is the synchronous TD learning update.
* `LMLExplore.ReinforcementLearning.measurable_syncQLearning`: the iterate `Q t` is measurable for
  the σ-algebra of the first `t` samples.
* `LMLExplore.ReinforcementLearning.syncQLearning_mem_Icc`,
  `LMLExplore.ReinforcementLearning.abs_syncQLearning_sub_optQValue_le`: the ranges of the
  iterates and of their errors [LCCWC24, Lemma 4].
* `LMLExplore.ReinforcementLearning.syncQLearning_succ_sub_optQValue`: the error recursion
  [LCCWC24, (32)]; `LMLExplore.ReinforcementLearning.syncQLearning_succ_sub_optQValue_le`,
  `LMLExplore.ReinforcementLearning.le_syncQLearning_succ_sub_optQValue`: its upper and lower
  bounds through greedy policies [LCCWC24, (33)–(34)].
* `LMLExplore.ReinforcementLearning.syncQLearning_sub_optQValue_le`,
  `LMLExplore.ReinforcementLearning.le_syncQLearning_sub_optQValue`: the unrolled bounds
  [LCCWC24, (35)]; `LMLExplore.ReinforcementLearning.syncQLearning_sub_optQValue_eq_of_unique`:
  the unrolled equality with one action.
* `LMLExplore.ReinforcementLearning.condExp_comp_syncQLearning`: given the first `t` samples, the
  sample `ω t p` keeps its law `P p` and the iterate `Q t` is frozen;
  `LMLExplore.ReinforcementLearning.condExp_iSup_syncQLearning`,
  `LMLExplore.ReinforcementLearning.condExp_sq_sub_integral_iSup_syncQLearning`: the conditional
  mean and variance of the empirical prediction `V t (ω t p)`.

## References

* [LCCWC24] G. Li, C. Cai, Y. Chen, Y. Wei and Y. Chi, *Is Q-learning minimax optimal? A tight
  sample complexity analysis*, Operations Research (2024), arXiv:2102.06548.
* [WD92] C. J. C. H. Watkins and P. Dayan, *Q-learning*, Machine Learning 8 (1992), 279–292.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP Bandits
open scoped NNReal

namespace LMLExplore.ReinforcementLearning

variable {𝓢 𝓐 : Type*} {r : 𝓢 × 𝓐 → ℝ} {γ : ℝ≥0} {η : ℕ → ℝ} {Q₀ : 𝓢 × 𝓐 → ℝ}

/-! ### The recursion -/

variable (r γ η Q₀) in
/-- **Synchronous Q-learning** [WD92], [LCCWC24, Algorithm 1] with rewards `r`, discount `γ`,
learning rates `η` and initial action value `Q₀`, on the array of samples `ω : ℕ → 𝓢 × 𝓐 → 𝓢`:
iteration `t + 1` updates the action value of every pair `p` to
`(1 - η (t + 1)) * Q t p + η (t + 1) * (r p + γ * ⨆ a, Q t (ω t p, a))`, with the next state
`ω t p` sampled from `p`. -/
noncomputable def syncQLearning : ℕ → (ℕ → 𝓢 × 𝓐 → 𝓢) → 𝓢 × 𝓐 → ℝ
  | 0 => fun _ ↦ Q₀
  | t + 1 => fun ω p ↦ (1 - η (t + 1)) * syncQLearning t ω p +
      η (t + 1) * (r p + γ * ⨆ a, syncQLearning t ω (ω t p, a))

@[simp]
lemma syncQLearning_zero (ω : ℕ → 𝓢 × 𝓐 → 𝓢) : syncQLearning r γ η Q₀ 0 ω = Q₀ :=
  (rfl)

lemma syncQLearning_succ (t : ℕ) (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) :
    syncQLearning r γ η Q₀ (t + 1) ω p = (1 - η (t + 1)) * syncQLearning r γ η Q₀ t ω p +
      η (t + 1) * (r p + γ * ⨆ a, syncQLearning r γ η Q₀ t ω (ω t p, a)) :=
  (rfl)

/-- **Synchronous TD learning** [LCCWC24, (7)]: with one action, synchronous Q-learning updates the
value of every state `s` towards `r s + γ V t (ω t s)`. -/
lemma syncQLearning_succ_of_unique [Unique 𝓐] (t : ℕ) (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) :
    syncQLearning r γ η Q₀ (t + 1) ω p = (1 - η (t + 1)) * syncQLearning r γ η Q₀ t ω p +
      η (t + 1) * (r p + γ * syncQLearning r γ η Q₀ t ω (ω t p, default)) := by
  rw [syncQLearning_succ, ciSup_unique]

/-- The `t`-th iterate only depends on the first `t` samples. -/
lemma syncQLearning_congr {t : ℕ} {ω ω' : ℕ → 𝓢 × 𝓐 → 𝓢} (h : ∀ i < t, ω i = ω' i) :
    syncQLearning r γ η Q₀ t ω = syncQLearning r γ η Q₀ t ω' := by
  induction t with
  | zero => simp
  | succ t ih =>
    ext p
    rw [syncQLearning_succ, syncQLearning_succ, ih fun i hi ↦ h i (by omega), h t t.lt_succ_self]

/-- For finite state and action spaces, the `t`-th iterate takes finitely many values: it is a
function of the first `t` samples, which take finitely many values. -/
theorem finite_range_syncQLearning [Finite 𝓢] [Finite 𝓐] (t : ℕ) :
    (Set.range (syncQLearning r γ η Q₀ t)).Finite := by
  induction t with
  | zero =>
    exact (Set.finite_singleton Q₀).subset
      (Set.range_subset_iff.2 fun ω ↦ Set.mem_singleton_iff.2 (syncQLearning_zero ω))
  | succ t ih =>
    refine ((ih.prod (Set.finite_univ (α := 𝓢 × 𝓐 → 𝓢))).image fun z p ↦
      (1 - η (t + 1)) * z.1 p + η (t + 1) * (r p + γ * ⨆ a, z.1 (z.2 p, a))).subset ?_
    rintro _ ⟨ω, rfl⟩
    exact ⟨(syncQLearning r γ η Q₀ t ω, ω t), ⟨⟨ω, rfl⟩, Set.mem_univ _⟩,
      funext fun p ↦ (syncQLearning_succ t ω p).symm⟩

section Measurable

variable {m𝓢 : MeasurableSpace 𝓢} [Countable 𝓢] [MeasurableSingletonClass 𝓢] [Countable 𝓐]

/-- The `t`-th iterate is measurable for the σ-algebra of the first `t` samples, the strict past
`Filtration.naturalLT` of the sample sequence at time `t`. -/
theorem measurable_syncQLearning (t : ℕ) :
    Measurable[Filtration.naturalLT (fun i (ω : ℕ → 𝓢 × 𝓐 → 𝓢) ↦ ω i) measurable_pi_apply t]
      (syncQLearning r γ η Q₀ t) := by
  set ℱ := Filtration.naturalLT (fun i (ω : ℕ → 𝓢 × 𝓐 → 𝓢) ↦ ω i) measurable_pi_apply
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hQ : Measurable[ℱ (t + 1)] (syncQLearning r γ η Q₀ t) :=
      ih.mono (ℱ.mono t.le_succ) le_rfl
    have hω : Measurable[ℱ (t + 1)] fun ω : ℕ → 𝓢 × 𝓐 → 𝓢 ↦ ω t :=
      Filtration.measurable_naturalLT measurable_pi_apply t.lt_succ_self
    -- with `ℱ (t + 1)` as ambient σ-algebra, `measurable_pi_iff` checks each coordinate `p`
    let : MeasurableSpace (ℕ → 𝓢 × 𝓐 → 𝓢) := ℱ (t + 1)
    refine measurable_pi_iff.2 fun p ↦ ?_
    simp_rw [syncQLearning_succ]
    exact (measurable_const.mul ((measurable_pi_apply p).comp hQ)).add
      (measurable_const.mul (measurable_const.add (measurable_const.mul
        (Measurable.iSup_apply_prodMk hQ ((measurable_pi_apply p).comp hω)))))

end Measurable

/-! ### Ranges of the iterates -/

/-- A supremum of values in `[a, b]` over a nonempty index type lies in `[a, b]`. -/
private lemma ciSup_mem_Icc {α ι : Type*} [ConditionallyCompleteLattice α] [Nonempty ι]
    {f : ι → α} {a b : α} (h : ∀ i, f i ∈ Set.Icc a b) : (⨆ i, f i) ∈ Set.Icc a b :=
  ⟨(h (Classical.arbitrary ι)).1.trans (le_ciSup ⟨b, Set.forall_mem_range.2 fun i ↦ (h i).2⟩ _),
    ciSup_le fun i ↦ (h i).2⟩

/-- **Ranges of the iterates** [LCCWC24, Lemma 4]. With learning rates in `[0, 1]`, rewards in
`[0, C]` and an initial value in `[0, B]`, where `C + γ * B ≤ B`, the iterates of synchronous
Q-learning stay in `[0, B]`: each update is a convex combination of the current value and of a
target in `[0, C + γ * B]`. With `γ < 1`, `B = C / (1 - γ)` will do. -/
theorem syncQLearning_mem_Icc [Nonempty 𝓐] {B C : ℝ} (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hr : ∀ p, r p ∈ Set.Icc 0 C) (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 B) (hB : C + γ * B ≤ B) (t : ℕ)
    (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) : syncQLearning r γ η Q₀ t ω p ∈ Set.Icc 0 B := by
  induction t generalizing p with
  | zero => exact hQ₀ p
  | succ t ih =>
    obtain ⟨h0, h1⟩ := hη t
    -- the value estimate at the sampled state lies in `[0, B]`
    have hV : (⨆ a, syncQLearning r γ η Q₀ t ω (ω t p, a)) ∈ Set.Icc 0 B :=
      ciSup_mem_Icc fun a ↦ ih _
    have hγV : 0 ≤ (γ : ℝ) * ⨆ a, syncQLearning r γ η Q₀ t ω (ω t p, a) := mul_nonneg γ.2 hV.1
    have hγB : (γ : ℝ) * ⨆ a, syncQLearning r γ η Q₀ t ω (ω t p, a) ≤ γ * B :=
      mul_le_mul_of_nonneg_left hV.2 γ.2
    rw [syncQLearning_succ]
    refine ⟨add_nonneg (mul_nonneg (sub_nonneg.2 h1) (ih p).1)
      (mul_nonneg h0 (add_nonneg (hr p).1 hγV)), ?_⟩
    nlinarith [(ih p).2, (hr p).2, mul_le_mul_of_nonneg_left (ih p).2 (sub_nonneg.2 h1),
      mul_le_mul_of_nonneg_left (add_le_add (hr p).2 hγB) h0]

/-- **Ranges of the value estimates** [LCCWC24, Lemma 4]. Under the assumptions of
`syncQLearning_mem_Icc`, the value estimates `V t s = ⨆ a, Q t (s, a)` stay in `[0, B]`. -/
theorem iSup_syncQLearning_mem_Icc [Nonempty 𝓐] {B C : ℝ}
    (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1) (hr : ∀ p, r p ∈ Set.Icc 0 C)
    (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 B) (hB : C + γ * B ≤ B) (t : ℕ) (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (s : 𝓢) :
    (⨆ a, syncQLearning r γ η Q₀ t ω (s, a)) ∈ Set.Icc 0 B :=
  ciSup_mem_Icc fun a ↦ syncQLearning_mem_Icc hη hr hQ₀ hB t ω (s, a)

/-! ### The error recursion -/

section MDP

variable {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Nonempty 𝓢] {M : MDP 𝓢 𝓐 ℝ}
  {C : ℝ}

/-- **The errors of the iterates are bounded** [LCCWC24, Lemma 4]. For an MDP with rewards in
`[0, C]`, `γ < 1`, learning rates in `[0, 1]` and an initial value in `[0, C / (1 - γ)]`, the
iterates of synchronous Q-learning with the mean rewards stay within `C / (1 - γ)` of the optimal
action value: both lie in `[0, C / (1 - γ)]`. -/
theorem abs_syncQLearning_sub_optQValue_le [Countable 𝓐] [Nonempty 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ))) (t : ℕ) (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) :
    |syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p| ≤ C / (1 - γ) := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  have hRabs : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C := fun p ↦ (hR p).mono fun x hx ↦
    abs_le.2 ⟨by linarith [hx.1, hx.2], hx.2⟩
  have hr (q : 𝓢 × 𝓐) : meanReward M.R q ∈ Set.Icc 0 C :=
    ⟨by rw [meanReward_def]; exact integral_nonneg_of_ae ((hR q).mono fun x hx ↦ hx.1),
      (le_abs_self _).trans (abs_meanReward_le hRabs q)⟩
  have hB : C + γ * (C / (1 - γ)) ≤ C / (1 - γ) := by
    refine le_of_eq ?_
    field_simp
    ring
  have hQ := syncQLearning_mem_Icc hη hr hQ₀ hB t ω p
  have hQs := optQValue_nonneg hγ hRabs (fun q ↦ (hr q).1) p
  have hQs' := (le_abs_self _).trans (abs_optQValue_le hγ hRabs p)
  exact abs_sub_le_iff.2 ⟨by linarith [hQ.2], by linarith [hQ.1]⟩

/-- **The error recursion** [LCCWC24, (32)]. Writing `V t s = ⨆ a, Q t (s, a)` and `V*` for the
optimal value, the error `Δ t = Q t - Q*` of synchronous Q-learning with the mean rewards satisfies
`Δ (t + 1) p = (1 - η (t + 1)) Δ t p + η (t + 1) γ (V t (ω t p) - ∫ V* dP p)`. -/
theorem syncQLearning_succ_sub_optQValue (t : ℕ) (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) :
    syncQLearning (meanReward M.R) γ η Q₀ (t + 1) ω p - M.optQValue γ p =
      (1 - η (t + 1)) * (syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p) +
        η (t + 1) * γ * ((⨆ a, syncQLearning (meanReward M.R) γ η Q₀ t ω (ω t p, a)) -
          ∫ s', M.optValue γ s' ∂(M.P p)) := by
  rw [syncQLearning_succ, optQValue_def]
  ring

variable [Finite 𝓢] [MeasurableSingletonClass 𝓢] [Finite 𝓐]

/-- **Upper bound on the error recursion** [LCCWC24, (33a), (34)]. If the policy `π` is greedy for
the `t`-th iterate, `Q t (s, π s) = V t s`, then, with `Δ t = Q t - Q*`,
`Δ (t + 1) p ≤ (1 - η (t + 1)) Δ t p + η (t + 1) γ (P^π Δ t p + (V t (ω t p) - P V t p))`. -/
theorem syncQLearning_succ_sub_optQValue_le [Nonempty 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {t : ℕ} (hη : 0 ≤ η (t + 1)) {ω : ℕ → 𝓢 × 𝓐 → 𝓢} {π : 𝓢 → 𝓐}
    (hπ : ∀ s, syncQLearning (meanReward M.R) γ η Q₀ t ω (s, π s) =
      ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ t ω (s, a)) (p : 𝓢 × 𝓐) :
    syncQLearning (meanReward M.R) γ η Q₀ (t + 1) ω p - M.optQValue γ p ≤
      (1 - η (t + 1)) * (syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p) +
        η (t + 1) * γ *
          ((∫ s', (syncQLearning (meanReward M.R) γ η Q₀ t ω (s', π s') -
              M.optQValue γ (s', π s')) ∂(M.P p)) +
            ((⨆ a, syncQLearning (meanReward M.R) γ η Q₀ t ω (ω t p, a)) -
              ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ t ω (s', a) ∂(M.P p))) := by
  rw [syncQLearning_succ_sub_optQValue]
  gcongr
  -- `P (V t - V*) ≤ P^π Δ t`, since `V t = Q t (·, π ·)` and `Q* (·, π ·) ≤ V*`
  have h : ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ t ω (s', a) ∂(M.P p) -
      ∫ s', M.optValue γ s' ∂(M.P p) ≤
      ∫ s', (syncQLearning (meanReward M.R) γ η Q₀ t ω (s', π s') -
        M.optQValue γ (s', π s')) ∂(M.P p) := by
    rw [← integral_sub (.of_finite) (.of_finite)]
    exact integral_mono (.of_finite) (.of_finite) fun s ↦ by
      rw [← hπ s]
      exact sub_le_sub_left (optQValue_le_optValue hγ hR s (π s)) _
  linarith

/-- **Lower bound on the error recursion** [LCCWC24, (33b), (34)]. If the policy `π` is greedy for
the optimal action value, `Q* (s, π s) = V* s`, then, with `Δ t = Q t - Q*`,
`(1 - η (t + 1)) Δ t p + η (t + 1) γ (P^π Δ t p + (V t (ω t p) - P V t p)) ≤ Δ (t + 1) p`. -/
theorem le_syncQLearning_succ_sub_optQValue {t : ℕ} (hη : 0 ≤ η (t + 1))
    (ω : ℕ → 𝓢 × 𝓐 → 𝓢) {π : 𝓢 → 𝓐} (hπ : ∀ s, M.optQValue γ (s, π s) = M.optValue γ s)
    (p : 𝓢 × 𝓐) :
    (1 - η (t + 1)) * (syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p) +
        η (t + 1) * γ *
          ((∫ s', (syncQLearning (meanReward M.R) γ η Q₀ t ω (s', π s') -
              M.optQValue γ (s', π s')) ∂(M.P p)) +
            ((⨆ a, syncQLearning (meanReward M.R) γ η Q₀ t ω (ω t p, a)) -
              ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ t ω (s', a) ∂(M.P p))) ≤
      syncQLearning (meanReward M.R) γ η Q₀ (t + 1) ω p - M.optQValue γ p := by
  rw [syncQLearning_succ_sub_optQValue]
  gcongr
  -- `P^π Δ t ≤ P (V t - V*)`, since `Q t (·, π ·) ≤ V t` and `Q* (·, π ·) = V*`
  have h : ∫ s', (syncQLearning (meanReward M.R) γ η Q₀ t ω (s', π s') -
        M.optQValue γ (s', π s')) ∂(M.P p) ≤
      ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ t ω (s', a) ∂(M.P p) -
        ∫ s', M.optValue γ s' ∂(M.P p) := by
    rw [← integral_sub (.of_finite) (.of_finite)]
    exact integral_mono (.of_finite) (.of_finite) fun s ↦ by
      rw [hπ s]
      exact sub_le_sub_right (le_ciSup (Set.finite_range fun a ↦
        syncQLearning (meanReward M.R) γ η Q₀ t ω (s, a)).bddAbove (π s)) _
  linarith

/-- **The unrolled upper bound** [LCCWC24, (35)]. For learning rates in `[0, 1]` and policies
`π i` greedy for the iterates `Q i`, the error `Δ t = Q t - Q*` at `p` is at most
`(∏_{j=1}^t (1 - η j)) Δ 0 p` plus
`∑_{i=1}^t η^i_t γ (P^{π (i - 1)} Δ (i - 1) p + (P_i - P) V (i - 1) p)`,
with the learning-rate weights `η^i_t = learningRateWeight η t i`. -/
theorem syncQLearning_sub_optQValue_le [Nonempty 𝓐] (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1) {ω : ℕ → 𝓢 × 𝓐 → 𝓢} {π : ℕ → 𝓢 → 𝓐}
    (hπ : ∀ i s, syncQLearning (meanReward M.R) γ η Q₀ i ω (s, π i s) =
      ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (s, a)) (t : ℕ) (p : 𝓢 × 𝓐) :
    syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p ≤
      (∏ j ∈ Icc 1 t, (1 - η j)) * (Q₀ p - M.optQValue γ p) +
        ∑ i ∈ Icc 1 t, learningRateWeight η t i * (γ *
          ((∫ s', (syncQLearning (meanReward M.R) γ η Q₀ (i - 1) ω (s', π (i - 1) s') -
              M.optQValue γ (s', π (i - 1) s')) ∂(M.P p)) +
            ((⨆ a, syncQLearning (meanReward M.R) γ η Q₀ (i - 1) ω (ω (i - 1) p, a)) -
              ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ (i - 1) ω (s', a) ∂(M.P p)))) := by
  refine le_prod_mul_add_sum_learningRateWeight_mul (x := fun t ↦
    syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p) (fun t ↦ (hη t).2)
    (fun t ↦ ?_) t
  simpa only [Nat.add_sub_cancel, mul_assoc] using
    syncQLearning_succ_sub_optQValue_le hγ hR (hη t).1 (hπ t) p

/-- **The unrolled lower bound** [LCCWC24, (35)]. For learning rates in `[0, 1]` and a policy `π`
greedy for the optimal action value, the error `Δ t = Q t - Q*` is at least
`(∏_{j=1}^t (1 - η j)) Δ 0 p + ∑_{i=1}^t η^i_t γ (P^π Δ (i - 1) p + (P_i - P) V (i - 1) p)`. -/
theorem le_syncQLearning_sub_optQValue (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (ω : ℕ → 𝓢 × 𝓐 → 𝓢) {π : 𝓢 → 𝓐} (hπ : ∀ s, M.optQValue γ (s, π s) = M.optValue γ s)
    (t : ℕ) (p : 𝓢 × 𝓐) :
    (∏ j ∈ Icc 1 t, (1 - η j)) * (Q₀ p - M.optQValue γ p) +
        ∑ i ∈ Icc 1 t, learningRateWeight η t i * (γ *
          ((∫ s', (syncQLearning (meanReward M.R) γ η Q₀ (i - 1) ω (s', π s') -
              M.optQValue γ (s', π s')) ∂(M.P p)) +
            ((⨆ a, syncQLearning (meanReward M.R) γ η Q₀ (i - 1) ω (ω (i - 1) p, a)) -
              ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ (i - 1) ω (s', a) ∂(M.P p)))) ≤
      syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p := by
  refine prod_mul_add_sum_learningRateWeight_mul_le (x := fun t ↦
    syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p) (fun t ↦ (hη t).2)
    (fun t ↦ ?_) t
  simpa only [Nat.add_sub_cancel, mul_assoc] using
    le_syncQLearning_succ_sub_optQValue (hη t).1 ω hπ p

/-- **The error of synchronous TD learning** [LCCWC24, (110)], unrolled. With one action, the error
`Δ t = Q t - Q*` is exactly
`(∏_{j=1}^t (1 - η j)) Δ 0 p + ∑_{i=1}^t η^i_t γ (P Δ (i - 1) p + (P_i - P) V (i - 1) p)`,
where `V i s = Q i (s, default)`, for any learning rates. -/
theorem syncQLearning_sub_optQValue_eq_of_unique [Unique 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (t : ℕ) (p : 𝓢 × 𝓐) :
    syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p =
      (∏ j ∈ Icc 1 t, (1 - η j)) * (Q₀ p - M.optQValue γ p) +
        ∑ i ∈ Icc 1 t, learningRateWeight η t i * (γ *
          ((∫ s', (syncQLearning (meanReward M.R) γ η Q₀ (i - 1) ω (s', default) -
              M.optQValue γ (s', default)) ∂(M.P p)) +
            (syncQLearning (meanReward M.R) γ η Q₀ (i - 1) ω (ω (i - 1) p, default) -
              ∫ s', syncQLearning (meanReward M.R) γ η Q₀ (i - 1) ω (s', default) ∂(M.P p)))) := by
  have hv (s : 𝓢) : M.optQValue γ (s, default) = M.optValue γ s := by
    rw [← iSup_optQValue hγ hR s, ciSup_unique]
  refine eq_prod_smul_add_sum_learningRateWeight_smul (R := ℝ) (M := ℝ) (x := fun t ↦
    syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p) (fun t ↦ ?_) t
  rw [smul_eq_mul, smul_eq_mul, Nat.add_sub_cancel, syncQLearning_succ_sub_optQValue,
    ciSup_unique]
  simp only [hv]
  rw [integral_sub (.of_finite) (.of_finite)]
  ring

end MDP

/-! ### The sampling noise under the generative model -/

section Noise

variable {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Finite 𝓢]
  [MeasurableSingletonClass 𝓢] [Finite 𝓐] {P : Kernel (𝓢 × 𝓐) 𝓢} [IsMarkovKernel P]

/-- **Freezing the iterate.** Under the generative model `Bandits.streamMeasure P`, given the first
`t` samples, the sample `ω t p` keeps its law `P p` while the iterate `Q t` is known: for every
measurable `f`, the conditional mean of `f (Q t, ω t p)` is `∫ s', f (Q t, s') dP p`. -/
theorem condExp_comp_syncQLearning {f : (𝓢 × 𝓐 → ℝ) × 𝓢 → ℝ} (hf : Measurable f) (t : ℕ)
    (p : 𝓢 × 𝓐) :
    (streamMeasure P)[fun ω ↦ f (syncQLearning r γ η Q₀ t ω, ω t p) |
        Filtration.naturalLT (fun i (ω : ℕ → 𝓢 × 𝓐 → 𝓢) ↦ ω i) measurable_pi_apply t] =ᵐ[
      streamMeasure P] fun ω ↦ ∫ s', f (syncQLearning r γ η Q₀ t ω, s') ∂(P p) := by
  set ℱ := Filtration.naturalLT (fun i (ω : ℕ → 𝓢 × 𝓐 → 𝓢) ↦ ω i) measurable_pi_apply
  have hQ := measurable_syncQLearning (r := r) (γ := γ) (η := η) (Q₀ := Q₀) (m𝓢 := m𝓢) t
  have hY : Measurable fun ω : ℕ → 𝓢 × 𝓐 → 𝓢 ↦ ω t p :=
    (measurable_pi_apply p).comp (measurable_pi_apply t)
  -- the sample `ω t p` is independent of the first `t` samples
  have hindep : Indep (MeasurableSpace.comap (fun ω : ℕ → 𝓢 × 𝓐 → 𝓢 ↦ ω t p) inferInstance)
      (ℱ t) (streamMeasure P) :=
    indep_of_indep_of_le_left (Filtration.indep_naturalLT measurable_pi_apply
      (iIndepFun_eval_streamMeasure' P) t)
      ((measurable_pi_apply p).comp (comap_measurable fun ω : ℕ → 𝓢 × 𝓐 → 𝓢 ↦ ω t)).comap_le
  -- the composite takes finitely many values, hence is integrable
  have hfin : (Set.range fun ω ↦ f (syncQLearning r γ η Q₀ t ω, ω t p)).Finite :=
    (((finite_range_syncQLearning t).prod (Set.finite_univ (α := 𝓢))).image f).subset
      (Set.range_subset_iff.2 fun ω ↦ ⟨_, ⟨⟨ω, rfl⟩, Set.mem_univ _⟩, rfl⟩)
  obtain ⟨B, hB⟩ := (hfin.image fun x ↦ ‖x‖).bddAbove
  have hm : Measurable fun ω ↦ f (syncQLearning r γ η Q₀ t ω, ω t p) :=
    hf.comp ((hQ.mono (ℱ.le t) le_rfl).prodMk hY)
  have hint : Integrable (fun ω ↦ f (syncQLearning r γ η Q₀ t ω, ω t p)) (streamMeasure P) :=
    .of_bound hm.aestronglyMeasurable B
      (ae_of_all _ fun ω ↦ hB ⟨_, ⟨ω, rfl⟩, rfl⟩)
  have h := TauCeti.Probability.condExp_comp_prodMk_ae_eq_integral_of_indep (ℱ.le t) hQ hY
    hindep hf.stronglyMeasurable hint
  rwa [(hasLaw_eval_eval_streamMeasure P t p).map_eq] at h

/-- **The sampling noise is a martingale difference.** Under the generative model, given the first
`t` samples, the empirical prediction `V t (ω t p)` of the value estimate
`V t s = ⨆ a, Q t (s, a)` has conditional mean `P V t p = ∫ V t dP p`. -/
theorem condExp_iSup_syncQLearning (t : ℕ) (p : 𝓢 × 𝓐) :
    (streamMeasure P)[fun ω ↦ ⨆ a, syncQLearning r γ η Q₀ t ω (ω t p, a) |
        Filtration.naturalLT (fun i (ω : ℕ → 𝓢 × 𝓐 → 𝓢) ↦ ω i) measurable_pi_apply t] =ᵐ[
      streamMeasure P] fun ω ↦ ∫ s', ⨆ a, syncQLearning r γ η Q₀ t ω (s', a) ∂(P p) :=
  condExp_comp_syncQLearning (f := fun z ↦ ⨆ a, z.1 (z.2, a))
    (Measurable.iSup_apply_prodMk measurable_fst measurable_snd) t p

/-- **The conditional variance of the sampling noise.** Under the generative model, given the first
`t` samples, the empirical prediction `V t (ω t p)` of the value estimate
`V t s = ⨆ a, Q t (s, a)` has conditional variance the variance of `V t` under `P p`. -/
theorem condExp_sq_sub_integral_iSup_syncQLearning (t : ℕ) (p : 𝓢 × 𝓐) :
    (streamMeasure P)[fun ω ↦ ((⨆ a, syncQLearning r γ η Q₀ t ω (ω t p, a)) -
          ∫ s', ⨆ a, syncQLearning r γ η Q₀ t ω (s', a) ∂(P p)) ^ 2 |
        Filtration.naturalLT (fun i (ω : ℕ → 𝓢 × 𝓐 → 𝓢) ↦ ω i) measurable_pi_apply t] =ᵐ[
      streamMeasure P] fun ω ↦ Var[fun s' ↦ ⨆ a, syncQLearning r γ η Q₀ t ω (s', a); P p] := by
  have hV : Measurable fun z : (𝓢 × 𝓐 → ℝ) × 𝓢 ↦ ⨆ a, z.1 (z.2, a) :=
    Measurable.iSup_apply_prodMk measurable_fst measurable_snd
  have hmean : Measurable fun q : 𝓢 × 𝓐 → ℝ ↦ ∫ s', ⨆ a, q (s', a) ∂(P p) :=
    (hV.stronglyMeasurable.integral_prod_right' (ν := P p)).measurable
  refine (condExp_comp_syncQLearning
    (f := fun z ↦ ((⨆ a, z.1 (z.2, a)) - ∫ s', ⨆ a, z.1 (s', a) ∂(P p)) ^ 2)
    ((hV.sub (hmean.comp measurable_fst)).pow_const 2) t p).trans (ae_of_all _ fun ω ↦ ?_)
  exact (variance_eq_integral (Measurable.of_discrete.aemeasurable)).symm

end Noise

end LMLExplore.ReinforcementLearning
