/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Comparison
public import LMLExplore.MarkovDecisionProcess.Episodic.Basic
import Mathlib.Analysis.Convex.Integral

/-!
# Values of Markov policies in an episodic MDP

A Markov policy of an episodic MDP `M : EpisodicMDP 𝓢 𝓐` is a sequence `π : ℕ → Kernel 𝓢 𝓐` of
Markov kernels: at the step `h`, it draws its action from `π h s`, where `s` is the current
state. For a horizon `H`, its state values `V^π_h` and action values `Q^π_h` are defined by
backward induction from `V^π_H = 0`:
* `Q^π_h (s, a) = r_h (s, a) + ∫ V^π_{h+1} dP_h (s, a)`;
* `V^π_h s = ∫ Q^π_h (s, a) dπ_h(a | s)` for `h < H`, and `V^π_h = 0` for `h ≥ H`.

These are the values of the remaining `H - h` steps of an episode started at the step `h`. The
policy `π` is run in the time-augmented MDP `M.augmented` as the stationary policy
`augMarkovPolicy π`, which plays `π h s` at the augmented state `(s, h)`. From an initial law
concentrated on the step `h`, the expected sum of the rewards of the first `H - h` rounds of every
run of this policy is the integral of `V^π_h` (`runReturn_augmented_markov`,
`integral_sum_feedback_eq_integral_value`). This identification is what the regret and sample
complexity bounds of episodic learning consume: they compare these values for the policies chosen
by a learner.

The definition `augMarkovPolicy` is adapted from `augPolicy` in the formalization entropy-mdp
(`github.com/RemyDegenne/entropy-mdp`, file
`Essakine2026Tight/LeanMachineLearning/ReinforcementLearning/MDP/Episodic.lean`, by Rémy Degenne,
Apache 2.0), from deterministic to stochastic Markov policies.

## Main definitions

* `Learning.MDP.Episodic.augMarkovPolicy π`: the stationary policy of the augmented MDP playing the
  Markov policy `π`.
* `Learning.MDP.Episodic.EpisodicMDP.value M H π h s`: the value `V^π_h s` of `π` at the step `h`
  and the state `s`, with the horizon `H`.
* `Learning.MDP.Episodic.EpisodicMDP.qValue M H π h s a`: the action value `Q^π_h (s, a)`.

## Main statements

* `Learning.MDP.Episodic.EpisodicMDP.value_of_lt`, `Learning.MDP.Episodic.EpisodicMDP.value_of_le`:
  the backward recursion `V^π_h s = ∫ Q^π_h (s, a) dπ_h(a | s)` for `h < H`, and `V^π_h = 0`
  for `H ≤ h`.
* `Learning.MDP.Episodic.EpisodicMDP.measurable_value`,
  `Learning.MDP.Episodic.EpisodicMDP.measurable_qValue`: the values are measurable.
* `Learning.MDP.Episodic.EpisodicMDP.value_mem_Icc`: for rewards in `[a, b]`, the value at the
  step `h` lies in `[(H - h) a, (H - h) b]`; in particular `0 ≤ V^π_h ≤ H - h` for rewards in
  `[0, 1]` (`value_nonneg`, `value_le`); for rewards in `[-C, C]`, `|V^π_h| ≤ H |C|` at every
  step (`abs_value_le_mul_abs`) and `|Q^π_h| ≤ H |C|` before the horizon
  (`abs_qValue_le_mul_abs`).
* `Learning.MDP.Episodic.EpisodicMDP.measurable_meanReward_add_integral`,
  `Learning.MDP.Episodic.EpisodicMDP.meanReward_add_integral_mem_Icc`: the measurability and the
  bounds of the backup `r_h (s, a) + ∫ V dP_h (s, a)` of a function `V` of the next state, shared
  by the values of policies and the optimal values.
* `Learning.MDP.Episodic.EpisodicMDP.value_deterministic_of_lt`: the value of a deterministic
  Markov policy is its action value at the action it plays.
* `Learning.MDP.Episodic.EpisodicMDP.hasCondDistrib_action_obs_fst_markov`: along a run of
  `augMarkovPolicy π` started at the step `h₀`, the action of round `n` has conditional law
  `π (h₀ + n)` given the state of round `n`.
* `Learning.MDP.Episodic.EpisodicMDP.runReturn_augmented_markov`: the undiscounted `(H - h)`-step
  return `M.augmented.runReturn 1 (H - h) 0` in the augmented MDP of `augMarkovPolicy π`, from an
  initial law `μ` concentrated on the step `h`, is `∫ V^π_h dμ`;
  `runReturn_augmented_markov_dirac` is the case of a Dirac mass at `(s, h)`.
* `Learning.MDP.Episodic.EpisodicMDP.integral_sum_feedback_eq_integral_value`: the same identity
  along every run, for the expected sum of the realized rewards.

## References

* [AJKS] A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022, §1.2.
* [P] M. L. Puterman, *Markov Decision Processes: Discrete Stochastic Dynamic Programming*,
  Wiley, 1994, §4.2.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset LMLExplore

namespace Learning.MDP.Episodic

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}

/-! ### Markov policies in the augmented MDP -/

/-- The stationary policy of the time-augmented state space `𝓢 × ℕ` playing the Markov policy
`π : ℕ → Kernel 𝓢 𝓐`: at the augmented state `(s, h)`, it draws its action from `π h s`. -/
noncomputable def augMarkovPolicy (π : ℕ → Kernel 𝓢 𝓐) : Kernel (𝓢 × ℕ) 𝓐 :=
  ⟨fun q ↦ π q.2 q.1, measurable_from_prod_countable_left fun h ↦ (π h).measurable⟩

@[simp]
lemma augMarkovPolicy_apply (π : ℕ → Kernel 𝓢 𝓐) (s : 𝓢) (h : ℕ) :
    augMarkovPolicy π (s, h) = π h s :=
  (rfl)

instance (π : ℕ → Kernel 𝓢 𝓐) [∀ h, IsMarkovKernel (π h)] :
    IsMarkovKernel (augMarkovPolicy π) :=
  ⟨fun q ↦ by rw [← Prod.mk.eta (p := q), augMarkovPolicy_apply]; infer_instance⟩

namespace EpisodicMDP

/-! ### Values and action values -/

variable (M : EpisodicMDP 𝓢 𝓐) (H : ℕ) (π : ℕ → Kernel 𝓢 𝓐)

/-- The value `V^π_h s` of the Markov policy `π` at the step `h` and the state `s`, with the
horizon `H`: the expected sum of the mean rewards of the `H - h` remaining steps. It is defined by
backward induction: `V^π_h s = ∫ (r_h (s, a) + ∫ V^π_{h+1} dP_h (s, a)) dπ_h(a | s)` for `h < H`,
and `V^π_h = 0` for `h ≥ H`. See `value_of_lt` and `value_of_le`. -/
noncomputable def value (h : ℕ) (s : 𝓢) : ℝ :=
  if h < H then
    ∫ a, (M.meanReward h s a + ∫ s', value (h + 1) s' ∂(M.trans h (s, a))) ∂(π h s)
  else 0
termination_by H - h

/-- The action value `Q^π_h (s, a) = r_h (s, a) + ∫ V^π_{h+1} dP_h (s, a)` of the Markov policy
`π` at the step `h`, with the horizon `H`. For `h < H`, it is the expected sum of the mean rewards
of the `H - h` remaining steps when the action `a` is played at the state `s` and `π` is followed
afterwards. -/
noncomputable def qValue (h : ℕ) (s : 𝓢) (a : 𝓐) : ℝ :=
  M.meanReward h s a + ∫ s', M.value H π (h + 1) s' ∂(M.trans h (s, a))

lemma qValue_def (h : ℕ) (s : 𝓢) (a : 𝓐) :
    M.qValue H π h s a = M.meanReward h s a + ∫ s', M.value H π (h + 1) s' ∂(M.trans h (s, a)) :=
  (rfl)

variable {M H π}

/-- Before the horizon, the value is the average of the action value over the actions of the
policy: `V^π_h s = ∫ Q^π_h (s, a) dπ_h(a | s)`. -/
theorem value_of_lt {h : ℕ} (hh : h < H) (s : 𝓢) :
    M.value H π h s = ∫ a, M.qValue H π h s a ∂(π h s) := by
  rw [value]
  simp only [hh, ↓reduceIte, qValue_def]

/-- From the horizon on, the value is zero. -/
theorem value_of_le {h : ℕ} (hh : H ≤ h) (s : 𝓢) : M.value H π h s = 0 := by
  rw [value]
  simp [not_lt.2 hh]

@[simp]
lemma value_self (s : 𝓢) : M.value H π H s = 0 :=
  value_of_le le_rfl s

/-- For a measurable function `V` of the next state, the backup
`(s, a) ↦ r_h (s, a) + ∫ V dP_h (s, a)` at the step `h` is measurable. -/
theorem measurable_meanReward_add_integral {V : 𝓢 → ℝ} (hV : Measurable V) (h : ℕ) :
    Measurable fun p : 𝓢 × 𝓐 ↦ M.meanReward h p.1 p.2 + ∫ s', V s' ∂(M.trans h p) :=
  (M.measurable_meanReward h).add
    (hV.stronglyMeasurable.integral_kernel (κ := M.trans h)).measurable

section Measurable

variable [∀ h, IsSFiniteKernel (π h)]

/-- The value at every step is a measurable function of the state. -/
theorem measurable_value (h : ℕ) : Measurable (M.value H π h) := by
  by_cases hh : h < H
  · have hQ : Measurable fun p : 𝓢 × 𝓐 ↦ M.qValue H π h p.1 p.2 :=
      measurable_meanReward_add_integral (M := M) (measurable_value (h + 1)) h
    rw [funext (value_of_lt hh)]
    exact (hQ.stronglyMeasurable.integral_kernel_prod_right' (κ := π h)).measurable
  · rw [funext (value_of_le (not_lt.1 hh))]
    exact measurable_const
termination_by H - h

/-- The action value at every step is a measurable function of the state-action pair. -/
theorem measurable_qValue (h : ℕ) : Measurable fun p : 𝓢 × 𝓐 ↦ M.qValue H π h p.1 p.2 :=
  measurable_meanReward_add_integral (M := M) (measurable_value (h + 1)) h

/-- The values of `π` at all steps, read at the step of the augmented state, form a measurable
function on the augmented states. -/
private lemma measurable_value_augmented : Measurable fun q : 𝓢 × ℕ ↦ M.value H π q.2 q.1 :=
  measurable_from_prod_countable_left fun h ↦ measurable_value h

variable (M H π) in
/-- The action value is the one-step lookahead, in the augmented MDP and without discount, of the
values read at the step of the augmented state. -/
theorem lookahead_augmented_value (s : 𝓢) (h : ℕ) (a' : 𝓐) :
    M.augmented.lookahead 1 (fun q ↦ M.value H π q.2 q.1) ((s, h), a') = M.qValue H π h s a' := by
  simp only [MDP.lookahead_def, meanReward_augmented, augmented_P_apply, NNReal.coe_one, one_mul,
    qValue_def, integral_map measurable_prodMk_right.aemeasurable
      measurable_value_augmented.aestronglyMeasurable]

end Measurable

/-- Before the horizon, the value of the deterministic Markov policy playing `d h s` at the step
`h` and the state `s` is its action value at that action: `V^d_h s = Q^d_h (s, d_h s)`. -/
theorem value_deterministic_of_lt {d : ℕ → 𝓢 → 𝓐} (hd : ∀ h, Measurable (d h)) {h : ℕ}
    (hh : h < H) (s : 𝓢) :
    M.value H (fun h ↦ Kernel.deterministic (d h) (hd h)) h s =
      M.qValue H (fun h ↦ Kernel.deterministic (d h) (hd h)) h s (d h s) := by
  rw [value_of_lt hh, Kernel.integral_deterministic' (hd h)
    (Measurable.stronglyMeasurable (f := M.qValue H _ h s)
      ((measurable_qValue h).comp measurable_prodMk_left))]

/-! ### Bounds -/

variable [∀ h, IsMarkovKernel (π h)] {a b C : ℝ}

/-- For rewards in `[a, b]`, if a measurable function `V` of the next state lies in
`[(H - (h + 1)) a, (H - (h + 1)) b]`, then the backup `r_h (s, a) + ∫ V dP_h (s, a)` at a step
`h < H` lies in `[(H - h) a, (H - h) b]`. -/
theorem meanReward_add_integral_mem_Icc (hM : M.RewardsIn (Set.Icc a b)) {h : ℕ} (hh : h < H)
    {V : 𝓢 → ℝ} (hVm : Measurable V)
    (hV : ∀ s', V s' ∈ Set.Icc ((H - (h + 1) : ℕ) * a) ((H - (h + 1) : ℕ) * b))
    (s : 𝓢) (a' : 𝓐) :
    M.meanReward h s a' + ∫ s', V s' ∂(M.trans h (s, a')) ∈
      Set.Icc ((H - h : ℕ) * a) ((H - h : ℕ) * b) := by
  have hr := meanReward_mem_Icc hM h s a'
  have hPV := Convex.integral_mem (μ := M.trans h (s, a')) (convex_Icc _ _) isClosed_Icc
    (.of_forall hV) (.of_mem_Icc _ _ hVm.aemeasurable (.of_forall hV))
  rw [show H - h = H - (h + 1) + 1 by omega, Nat.cast_add_one]
  constructor <;> linarith [hr.1, hr.2, hPV.1, hPV.2]

/-- For rewards in `[a, b]`, the value of `π` at the step `h` lies in `[(H - h) a, (H - h) b]`. -/
theorem value_mem_Icc (hM : M.RewardsIn (Set.Icc a b)) (h : ℕ) (s : 𝓢) :
    M.value H π h s ∈ Set.Icc ((H - h : ℕ) * a) ((H - h : ℕ) * b) := by
  by_cases hh : h < H
  · -- the action values lie in the same interval, and so does their average
    have hQ : ∀ a', M.qValue H π h s a' ∈ Set.Icc ((H - h : ℕ) * a) ((H - h : ℕ) * b) :=
      meanReward_add_integral_mem_Icc hM hh (measurable_value (h + 1))
        (fun s' ↦ value_mem_Icc hM (h + 1) s') s
    rw [value_of_lt hh]
    exact Convex.integral_mem (convex_Icc _ _) isClosed_Icc (.of_forall hQ)
      (.of_mem_Icc _ _ ((measurable_qValue h).comp measurable_prodMk_left).aemeasurable
        (.of_forall hQ))
  · rw [value_of_le (not_lt.1 hh), Nat.sub_eq_zero_of_le (not_lt.1 hh)]
    simp
termination_by H - h

/-- For rewards in `[a, b]`, the action value of `π` at a step `h < H` lies in
`[(H - h) a, (H - h) b]`. -/
theorem qValue_mem_Icc (hM : M.RewardsIn (Set.Icc a b)) {h : ℕ} (hh : h < H) (s : 𝓢)
    (a' : 𝓐) : M.qValue H π h s a' ∈ Set.Icc ((H - h : ℕ) * a) ((H - h : ℕ) * b) :=
  meanReward_add_integral_mem_Icc hM hh (measurable_value (h + 1)) (value_mem_Icc hM (h + 1)) s a'

/-- For bounded rewards, the value of `π` at every step is integrable with respect to every finite
measure on the states. -/
theorem integrable_value (hM : M.RewardsIn (Set.Icc a b)) (h : ℕ) {μ : Measure 𝓢}
    [IsFiniteMeasure μ] : Integrable (M.value H π h) μ :=
  .of_mem_Icc _ _ (measurable_value h).aemeasurable (.of_forall (value_mem_Icc hM h))

/-- For nonnegative rewards in `[0, b]`, the value of `π` is nonnegative. -/
theorem value_nonneg (hM : M.RewardsIn (Set.Icc 0 b)) (h : ℕ) (s : 𝓢) : 0 ≤ M.value H π h s := by
  simpa using (value_mem_Icc (H := H) (π := π) hM h s).1

/-- For rewards in `[a, 1]`, the value of `π` at the step `h` is at most the number `H - h` of
steps to go. -/
theorem value_le (hM : M.RewardsIn (Set.Icc a 1)) (h : ℕ) (s : 𝓢) :
    M.value H π h s ≤ (H - h : ℕ) := by
  simpa using (value_mem_Icc (H := H) (π := π) hM h s).2

/-- For rewards in `[-C, C]`, the value of `π` at the step `h` is at most `(H - h) C` in absolute
value. -/
theorem abs_value_le (hM : M.RewardsIn (Set.Icc (-C) C)) (h : ℕ) (s : 𝓢) :
    |M.value H π h s| ≤ (H - h : ℕ) * C := by
  have hV := value_mem_Icc (H := H) (π := π) hM h s
  rw [mul_neg] at hV
  exact abs_le.2 hV

/-- For rewards in `[-C, C]`, the value of `π` is at most `H |C|` in absolute value, uniformly
over the steps. -/
theorem abs_value_le_mul_abs (hM : M.RewardsIn (Set.Icc (-C) C)) (h : ℕ) (s : 𝓢) :
    |M.value H π h s| ≤ H * |C| :=
  calc |M.value H π h s| ≤ (H - h : ℕ) * C := abs_value_le hM h s
    _ ≤ (H - h : ℕ) * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) (Nat.cast_nonneg _)
    _ ≤ H * |C| := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) (abs_nonneg C)

/-- For rewards in `[-C, C]`, the action value of `π` before the horizon is at most `H |C|` in
absolute value, uniformly over the steps. -/
theorem abs_qValue_le_mul_abs (hM : M.RewardsIn (Set.Icc (-C) C)) {h : ℕ} (hh : h < H) (s : 𝓢)
    (a : 𝓐) : |M.qValue H π h s a| ≤ H * |C| := by
  have hQ := qValue_mem_Icc (π := π) hM hh s a
  rw [mul_neg] at hQ
  calc |M.qValue H π h s a| ≤ (H - h : ℕ) * C := abs_le.2 hQ
    _ ≤ (H - h : ℕ) * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) (Nat.cast_nonneg _)
    _ ≤ H * |C| := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) (abs_nonneg C)

/-! ### The values are the returns of the augmented MDP -/

section Runs

variable [Nonempty 𝓢] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → 𝓢 × ℕ} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ}
  {μ : Measure (𝓢 × ℕ)} [IsProbabilityMeasure μ] {h₀ : ℕ}

/-- Along a run of the Markov policy `π` in the augmented MDP started at the step `h₀`, the
action of round `n` has conditional law `π (h₀ + n)` given the state of round `n`. -/
theorem hasCondDistrib_action_obs_fst_markov (hμ : ∀ᵐ p ∂μ, p.2 = h₀)
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ augMarkovPolicy π) (M.augmented.env μ) P)
    (n : ℕ) :
    HasCondDistrib (A n) (fun ω ↦ (O n ω).1) (π (h₀ + n)) P := by
  -- the augmented state of round `n` is almost surely the state of round `n` at the step `h₀ + n`
  have h_ae : O n =ᵐ[P] (fun s : 𝓢 ↦ (s, h₀ + n)) ∘ fun ω ↦ (O n ω).1 := by
    filter_upwards [ae_obs_snd_eq hμ h n] with ω hω
    simp [← hω]
  have h_cond := ((h.hasCondDistrib_action_markov n).congr h_ae.symm
    .rfl).of_measurableEmbedding_comp_right (measurableEmbedding_prod_mk_right (h₀ + n))
  convert h_cond using 1
  ext s : 1
  rw [Kernel.comap_apply, augMarkovPolicy_apply]

/-- Along a run of `augMarkovPolicy π` started at the step `h₀`, at a round `n` before the
horizon, the expected value of the state is the expected mean reward of the round plus the
expected value of the next state. -/
private lemma integral_value_obs (hM : M.RewardsIn (Set.Icc (-C) C)) (hμ : ∀ᵐ p ∂μ, p.2 = h₀)
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ augMarkovPolicy π) (M.augmented.env μ) P)
    {n : ℕ} (hn : h₀ + n < H) :
    ∫ ω, M.value H π (O n ω).2 (O n ω).1 ∂P =
      ∫ ω, MDP.meanReward M.augmented.R (O n ω, A n ω) ∂P +
        ∫ ω, M.value H π (O (n + 1) ω).2 (O (n + 1) ω).1 ∂P := by
  have hW := measurable_value_augmented (M := M) (H := H) (π := π)
  have hWB (q : 𝓢 × ℕ) := abs_value_le_mul_abs (H := H) (π := π) hM q.2 q.1
  have hR := hM.ae_abs_augmented_R_le
  have hlaw := MDP.hasLaw_obs_markov h n
  -- the state of round `n` is almost surely at the step `h₀ + n`
  have h_step : ∀ᵐ q ∂(stateMarginal (fun _ ↦ M.augmented.P) (fun _ ↦ augMarkovPolicy π) μ n),
      q.2 = h₀ + n := by
    rw [← hlaw.map_eq]
    exact (ae_map_iff (h.measurable_obs n).aemeasurable
      (measurable_snd (measurableSet_singleton _))).2 (ae_obs_snd_eq hμ h n)
  calc ∫ ω, M.value H π (O n ω).2 (O n ω).1 ∂P
      = ∫ q, M.value H π q.2 q.1
          ∂(stateMarginal (fun _ ↦ M.augmented.P) (fun _ ↦ augMarkovPolicy π) μ n) :=
        hlaw.integral_comp hW.aestronglyMeasurable
    _ = ∫ q, ∫ a', M.augmented.lookahead 1 (fun q ↦ M.value H π q.2 q.1) (q, a')
          ∂(augMarkovPolicy π q)
          ∂(stateMarginal (fun _ ↦ M.augmented.P) (fun _ ↦ augMarkovPolicy π) μ n) := by
        refine integral_congr_ae (h_step.mono fun q hq ↦ ?_)
        obtain ⟨s, k⟩ := q
        simp only at hq
        simp_rw [lookahead_augmented_value, augMarkovPolicy_apply]
        exact value_of_lt (hq ▸ hn) s
    _ = ∫ p, M.augmented.lookahead 1 (fun q ↦ M.value H π q.2 q.1) p
          ∂(stateMarginal (fun _ ↦ M.augmented.P) (fun _ ↦ augMarkovPolicy π) μ n ⊗ₘ
            augMarkovPolicy π) :=
        (Measure.integral_compProd (integrable_of_abs_le (MDP.measurable_lookahead hW)
          (MDP.abs_lookahead_le hR hWB) _)).symm
    _ = ∫ ω, M.augmented.lookahead 1 (fun q ↦ M.value H π q.2 q.1) (O n ω, A n ω) ∂P :=
        ((MDP.hasLaw_obs_action_markov h n).integral_comp
          (MDP.measurable_lookahead hW).aestronglyMeasurable).symm
    _ = _ := by
        rw [MDP.integral_lookahead h hR hW hWB n, NNReal.coe_one, one_mul]

/-- Along a run of `augMarkovPolicy π` started at the step `h₀`, the expected value of the
initial state is the expected sum of the mean rewards of the first `k` rounds plus the expected
value of the state of round `k`, for every `k ≤ H - h₀`. -/
private lemma integral_value_obs_zero (hM : M.RewardsIn (Set.Icc (-C) C))
    (hμ : ∀ᵐ p ∂μ, p.2 = h₀)
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ augMarkovPolicy π) (M.augmented.env μ) P)
    {k : ℕ} (hk : k ≤ H - h₀) :
    ∫ ω, M.value H π (O 0 ω).2 (O 0 ω).1 ∂P =
      ∑ n ∈ range k, ∫ ω, MDP.meanReward M.augmented.R (O n ω, A n ω) ∂P +
        ∫ ω, M.value H π (O k ω).2 (O k ω).1 ∂P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih (by omega), integral_value_obs hM hμ h (by omega), sum_range_succ, add_assoc]

/-- **The values are the returns of the augmented MDP.** For rewards in `[-C, C]` and an initial
law `μ` concentrated on the step `h`, the undiscounted `(H - h)`-step return, in the augmented MDP
and without terminal reward, of the stationary policy `augMarkovPolicy π` is the integral of the
value `V^π_h` against `μ`. -/
theorem runReturn_augmented_markov (hM : M.RewardsIn (Set.Icc (-C) C)) {h : ℕ}
    (hμ : ∀ᵐ p ∂μ, p.2 = h) :
    M.augmented.runReturn 1 (H - h) 0 (Algorithm.markov fun _ ↦ augMarkovPolicy π) μ =
      ∫ p, M.value H π h p.1 ∂μ := by
  have hrun := IT.isAlgEnvSeq_trajMeasure (Algorithm.markov fun _ ↦ augMarkovPolicy π)
    (M.augmented.env μ)
  have hW := measurable_value_augmented (M := M) (H := H) (π := π)
  rw [MDP.runReturn_eq_sum hrun hM.ae_abs_augmented_R_le (u := 0) measurable_zero (B := 0)
    (by simp)]
  simp only [NNReal.coe_one, one_pow, one_mul, Pi.zero_apply, integral_zero, mul_zero, add_zero]
  -- the value of the initial state is `V^π_h` since the initial step is `h`
  have h_init : ∫ p, M.value H π h p.1 ∂μ =
      ∫ ω, M.value H π (IT.obs 0 ω).2 (IT.obs 0 ω).1
        ∂(trajMeasure (Algorithm.markov fun _ ↦ augMarkovPolicy π) (M.augmented.env μ)) :=
    (integral_congr_ae (hμ.mono fun p hp ↦ by rw [hp])).trans
      ((MDP.hasLaw_obs_zero hrun).integral_comp hW.aestronglyMeasurable).symm
  -- the value of the state of round `H - h` is zero since its step is at least `H`
  have h_last : ∫ ω, M.value H π (IT.obs (H - h) ω).2 (IT.obs (H - h) ω).1
      ∂(trajMeasure (Algorithm.markov fun _ ↦ augMarkovPolicy π) (M.augmented.env μ)) = 0 :=
    integral_eq_zero_of_ae ((ae_obs_snd_eq hμ hrun (H - h)).mono fun ω hω ↦
      value_of_le (by omega) _)
  rw [h_init, integral_value_obs_zero hM hμ hrun le_rfl, h_last, add_zero]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [integral_map (hrun.measurable_obs_action n).aemeasurable
    (MDP.measurable_meanReward _).aestronglyMeasurable]

/-- For rewards in `[-C, C]`, the undiscounted `(H - h)`-step return, in the augmented MDP and
without terminal reward, of the stationary policy `augMarkovPolicy π` started at the state `s` and
the step `h` is the value `V^π_h s`. -/
theorem runReturn_augmented_markov_dirac (hM : M.RewardsIn (Set.Icc (-C) C)) (h : ℕ) (s : 𝓢) :
    M.augmented.runReturn 1 (H - h) 0 (Algorithm.markov fun _ ↦ augMarkovPolicy π)
      (Measure.dirac (s, h)) = M.value H π h s := by
  rw [runReturn_augmented_markov hM
      ((ae_dirac_iff (p := fun q : 𝓢 × ℕ ↦ q.2 = h)
        (measurable_snd (measurableSet_singleton h))).2 rfl),
    integral_dirac' (fun p : 𝓢 × ℕ ↦ M.value H π h p.1) _
      ((measurable_value h).comp measurable_fst).stronglyMeasurable]

/-- Along every run of `augMarkovPolicy π` in the augmented MDP from an initial law `μ`
concentrated on the step `h₀`, with rewards in `[-C, C]`, the expected sum of the realized
rewards of the first `H - h₀` rounds is the integral of the value `V^π_{h₀}` against `μ`. -/
theorem integral_sum_feedback_eq_integral_value (hM : M.RewardsIn (Set.Icc (-C) C))
    (hμ : ∀ᵐ p ∂μ, p.2 = h₀)
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ augMarkovPolicy π) (M.augmented.env μ) P) :
    ∫ ω, ∑ n ∈ range (H - h₀), Y n ω ∂P = ∫ p, M.value H π h₀ p.1 ∂μ := by
  rw [← runReturn_augmented_markov hM hμ,
    MDP.runReturn_eq_integral_feedback h hM.ae_abs_augmented_R_le (u := 0) measurable_zero
      (B := 0) (by simp)]
  simp

end Runs

end EpisodicMDP

end Learning.MDP.Episodic
