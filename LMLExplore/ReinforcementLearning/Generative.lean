/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Simulation
public import LMLExplore.Probability.Kernel.Empirical

/-!
# Planning with a generative model: the empirical MDP and crude bounds

A generative model of an MDP `M` with countable state and action spaces draws, for every
state-action pair `p`, independent next states with law `M.P p`. It is LML's stream model
`Bandits.streamMeasure M.P` on arrays `ω : ℕ → 𝓢 × 𝓐 → 𝓢`: the entry `ω i p` is the `i`-th sample
from `M.P p`, and `N` samples per pair use the entries `i < N`. The sample sequences of distinct
pairs are mutually independent (`LMLExplore.iIndepFun_arm_streamMeasure`), so that the samples of
disjoint sets of pairs are independent (`ProbabilityTheory.iIndepFun.indepFun_set`).

The empirical MDP `M.empirical N ω` has the empirical kernel of these samples as transition kernel
and the rewards of `M`. For finite state and action spaces with `S` states and `A` actions, its
transitions are uniformly close to those of `M` in total variation: for `δ > 0`, with probability
at least `1 - δ`, every pair `p` satisfies `tvDist (M.P p) (M̂.P p) < η` with
`η = √(2 (log (S A / δ) + S log 2) / N)`. Through the simulation lemma, for rewards bounded by `C`
and `γ < 1`, this gives the crude bounds of [AJKS, Proposition 2.1]: with probability at least
`1 - δ`,
* the action values of every stationary policy in `M` and in `M̂` are within `γ C η / (1 - γ) ^ 2`;
* the optimal action values of `M` and `M̂` are within `γ C η / (1 - γ) ^ 2`;
* every optimal stationary policy `π̂` of `M̂` satisfies `|Q^π̂ - Q*| ≤ 2 γ C η / (1 - γ) ^ 2` in
  `M`.

The optimal action values only depend on the transitions through the one-step predictions
`∫ v* dP̂ (s, a)` of the optimal value `v*` of `M` (the componentwise bounds of
`MarkovDecisionProcess/Simulation.lean`). Since `v*` is a fixed function with values in
`[-C / (1 - γ), C / (1 - γ)]`, Hoeffding's inequality and a union bound over the pairs give a
radius without the term `S log 2`: for `δ > 0`, with probability at least `1 - δ`, every pair `p`
satisfies `|∫ v* dP p - ∫ v* dP̂ p| ≤ C Δ / (1 - γ)` with `Δ = √(2 log (2 S A / δ) / N)`. This
gives the crude value bounds of [AJKS, Proposition 2.4]: with probability at least `1 - δ`,
* the optimal action values of `M` and `M̂` are within `γ C Δ / (1 - γ) ^ 2`;
* the action values in `M̂` of every optimal stationary policy `π*` of `M` are within
  `γ C Δ / (1 - γ) ^ 2` of the optimal action values of `M`.

## Main definitions

* `Learning.MDP.empirical M N ω`: the empirical MDP of the first `N` samples per pair of `ω`.

## Main statements

* `Learning.MDP.le_streamMeasure_forall_tvDist_empirical_lt`: with probability at least `1 - δ`,
  the transition kernels of `M` and `M.empirical N ω` are within `η` in total variation.
* `Learning.MDP.le_streamMeasure_forall_abs_qValue_sub_qValue_empirical_le`,
  `Learning.MDP.le_streamMeasure_forall_abs_optQValue_sub_optQValue_empirical_le`,
  `Learning.MDP.le_streamMeasure_forall_abs_qValue_sub_optQValue_le_of_value_empirical_eq_optValue`:
  the crude bounds [AJKS, Proposition 2.1].
* `Learning.MDP.le_streamMeasure_forall_abs_integral_optValue_sub_integral_optValue_empirical_le`:
  with probability at least `1 - δ`, the one-step predictions of the optimal value by `M` and by
  `M.empirical N ω` are within `C Δ / (1 - γ)`.
* `Learning.MDP.le_streamMeasure_forall_abs_optQValue_sub_optQValue_empirical_le'`,
  `Learning.MDP.le_streamMeasure_forall_abs_optQValue_sub_qValue_empirical_le_of_value_eq_optValue`:
  the crude value bounds [AJKS, Proposition 2.4].

## References

* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], Propositions 2.1 and 2.4
-/

public section

open MeasureTheory ProbabilityTheory LMLExplore Learning Bandits
open Real (log)
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 𝓡 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓡 : MeasurableSpace 𝓡} [MeasurableSingletonClass 𝓢] [MeasurableSingletonClass 𝓐]

section Countable

variable [Countable 𝓢] [Countable 𝓐]

/-- The empirical MDP of an array `ω : ℕ → 𝓢 × 𝓐 → 𝓢` of samples of next states, for `N ≠ 0`: its
transition kernel maps a pair `p` to the empirical law of the first `N` samples `ω i p`, `i < N`,
and its rewards are those of `M`. Under the generative model `Bandits.streamMeasure M.P` it is the
model of `M` estimated from `N` samples per state-action pair. -/
noncomputable def empirical (M : MDP 𝓢 𝓐 𝓡) (N : ℕ) [NeZero N] (ω : ℕ → 𝓢 × 𝓐 → 𝓢) :
    MDP 𝓢 𝓐 𝓡 where
  P := empiricalKernel N ω
  R := M.R

@[simp]
lemma empirical_P (M : MDP 𝓢 𝓐 𝓡) (N : ℕ) [NeZero N] (ω : ℕ → 𝓢 × 𝓐 → 𝓢) :
    (M.empirical N ω).P = empiricalKernel N ω :=
  (rfl)

@[simp]
lemma empirical_R (M : MDP 𝓢 𝓐 𝓡) (N : ℕ) [NeZero N] (ω : ℕ → 𝓢 × 𝓐 → 𝓢) :
    (M.empirical N ω).R = M.R :=
  (rfl)

end Countable

variable [Fintype 𝓢] [Fintype 𝓐]

/-- **The transitions of the empirical MDP are uniformly accurate.** Under the generative model of
an MDP `M` with `S` states and `A` actions, for `N ≠ 0` and `δ > 0`, with probability at least
`1 - δ`, every state-action pair `p` satisfies `tvDist (M.P p) ((M.empirical N ω).P p) < η` with
`η = √(2 (log (S A / δ) + S log 2) / N)`. -/
theorem le_streamMeasure_forall_tvDist_empirical_lt (M : MDP 𝓢 𝓐 𝓡) (N : ℕ) [NeZero N] {δ : ℝ}
    (hδ : 0 < δ) :
    1 - δ ≤ (streamMeasure M.P).real {ω | ∀ p, tvDist (M.P p) ((M.empirical N ω).P p) <
      √(2 * (log (Fintype.card 𝓢 * Fintype.card 𝓐 / δ) + Fintype.card 𝓢 * log 2) / N)} := by
  simpa [Fintype.card_prod] using le_streamMeasure_forall_tvDist_empiricalKernel_lt M.P N hδ

/-- **Uniform value accuracy of the empirical MDP** [AJKS, Proposition 2.1]. Under the generative
model of an MDP `M` with `S` states, `A` actions and rewards bounded by `C`, for `γ < 1`, `N ≠ 0`
and `δ > 0`, with probability at least `1 - δ`, the action values of every stationary policy `π` in
`M` and in `M.empirical N ω` differ by at most `γ C η / (1 - γ) ^ 2`, with
`η = √(2 (log (S A / δ) + S log 2) / N)`. -/
theorem le_streamMeasure_forall_abs_qValue_sub_qValue_empirical_le {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0}
    (hγ : γ < 1) {C : ℝ} (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (N : ℕ) [NeZero N] {δ : ℝ}
    (hδ : 0 < δ) :
    1 - δ ≤ (streamMeasure M.P).real {ω | ∀ (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] (p : 𝓢 × 𝓐),
      |M.qValue γ π p - (M.empirical N ω).qValue γ π p| ≤ γ * C *
        √(2 * (log (Fintype.card 𝓢 * Fintype.card 𝓐 / δ) + Fintype.card 𝓢 * log 2) / N) /
          (1 - γ) ^ 2} := by
  refine (le_streamMeasure_forall_tvDist_empirical_lt M N hδ).trans
    (measureReal_mono (fun ω hω π _ p ↦ ?_) (measure_ne_top _ _))
  exact abs_qValue_sub_qValue_le_of_tvDist_le (M' := M.empirical N ω) (by simp) hγ hR
    (by simpa using hR) (fun q ↦ (hω q).le) p

variable [Nonempty 𝓢] [Nonempty 𝓐]

/-- **Accuracy of the optimal action values of the empirical MDP** [AJKS, Proposition 2.1]. Under
the generative model of an MDP `M` with `S` states, `A` actions and rewards bounded by `C`, for
`γ < 1`, `N ≠ 0` and `δ > 0`, with probability at least `1 - δ`, the optimal action values of `M`
and of `M.empirical N ω` differ by at most `γ C η / (1 - γ) ^ 2`, with
`η = √(2 (log (S A / δ) + S log 2) / N)`. -/
theorem le_streamMeasure_forall_abs_optQValue_sub_optQValue_empirical_le {M : MDP 𝓢 𝓐 ℝ}
    {γ : ℝ≥0} (hγ : γ < 1) {C : ℝ} (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (N : ℕ) [NeZero N] {δ : ℝ}
    (hδ : 0 < δ) :
    1 - δ ≤ (streamMeasure M.P).real {ω | ∀ p,
      |M.optQValue γ p - (M.empirical N ω).optQValue γ p| ≤ γ * C *
        √(2 * (log (Fintype.card 𝓢 * Fintype.card 𝓐 / δ) + Fintype.card 𝓢 * log 2) / N) /
          (1 - γ) ^ 2} := by
  refine (le_streamMeasure_forall_tvDist_empirical_lt M N hδ).trans
    (measureReal_mono (fun ω hω p ↦ ?_) (measure_ne_top _ _))
  exact abs_optQValue_sub_optQValue_le_of_tvDist_le (M' := M.empirical N ω) (by simp) hγ hR
    (by simpa using hR) (fun q ↦ (hω q).le) p

/-- **Near-optimal planning in the empirical MDP** [AJKS, Proposition 2.1]. Under the generative
model of an MDP `M` with `S` states, `A` actions and rewards bounded by `C`, for `γ < 1`, `N ≠ 0`
and `δ > 0`, with probability at least `1 - δ`, every optimal stationary policy `π̂` of
`M.empirical N ω` has action values in `M` within `2 γ C η / (1 - γ) ^ 2` of the optimal action
values of `M`, with `η = √(2 (log (S A / δ) + S log 2) / N)`. -/
theorem le_streamMeasure_forall_abs_qValue_sub_optQValue_le_of_value_empirical_eq_optValue
    {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} (hγ : γ < 1) {C : ℝ} (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (N : ℕ)
    [NeZero N] {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ (streamMeasure M.P).real {ω | ∀ (π : Kernel 𝓢 𝓐) [IsMarkovKernel π],
      (M.empirical N ω).value γ π = (M.empirical N ω).optValue γ → ∀ p,
        |M.qValue γ π p - M.optQValue γ p| ≤ 2 * γ * C *
          √(2 * (log (Fintype.card 𝓢 * Fintype.card 𝓐 / δ) + Fintype.card 𝓢 * log 2) / N) /
            (1 - γ) ^ 2} := by
  refine (le_streamMeasure_forall_tvDist_empirical_lt M N hδ).trans
    (measureReal_mono (fun ω hω π _ hπ p ↦ ?_) (measure_ne_top _ _))
  -- `Q^π̂ - Q* = (Q^π̂ - Q̂^π̂) + (Q̂* - Q*)`, since `Q̂^π̂ = Q̂*`
  have h₁ := abs_qValue_sub_qValue_le_of_tvDist_le (M' := M.empirical N ω) (π := π) (by simp) hγ
    hR (by simpa using hR) (fun q ↦ (hω q).le) p
  have h₂ := abs_optQValue_sub_optQValue_le_of_tvDist_le (M' := M.empirical N ω) (by simp) hγ hR
    (by simpa using hR) (fun q ↦ (hω q).le) p
  rw [← qValue_eq_optQValue hπ, abs_sub_comm] at h₂
  exact (abs_sub_le _ _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

/-- **Accuracy of the one-step predictions of the optimal value.** Under the generative model of
an MDP `M` with `S` states, `A` actions and rewards bounded by `C`, for `γ < 1`, `N ≠ 0` and
`δ > 0`, with probability at least `1 - δ`, the one-step predictions of the optimal value `v*` of
`M` by `M` and by `M.empirical N ω` satisfy, for every state-action pair `p`,
`|∫ v* dP p - ∫ v* dP̂ p| ≤ C Δ / (1 - γ)`, with `Δ = √(2 log (2 S A / δ) / N)`. It is Hoeffding's
inequality for the fixed function `v*`, with values in `[-C / (1 - γ), C / (1 - γ)]`, and a union
bound over the pairs. -/
theorem le_streamMeasure_forall_abs_integral_optValue_sub_integral_optValue_empirical_le
    {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} (hγ : γ < 1) {C : ℝ} (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (N : ℕ)
    [NeZero N] {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ (streamMeasure M.P).real {ω | ∀ p,
      |∫ s, M.optValue γ s ∂(M.P p) - ∫ s, M.optValue γ s ∂((M.empirical N ω).P p)| ≤
        C / (1 - γ) * √(2 * log (2 * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) / N)} := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  -- the radius of Hoeffding's inequality for the range `[-C / (1 - γ), C / (1 - γ)]`
  have h_r : (C / (1 - γ) - -(C / (1 - γ))) *
      √(log (2 * Fintype.card (𝓢 × 𝓐) / δ) / (2 * N)) =
        C / (1 - γ) * √(2 * log (2 * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) / N) := by
    rw [Fintype.card_prod, Nat.cast_mul, ← mul_assoc, sub_neg_eq_add, ← two_mul,
      mul_comm 2 (C / (1 - γ)), mul_assoc]
    congr 1
    rw [show 2 * log (2 * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) / N =
        2 ^ 2 * (log (2 * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) / (2 * N)) by field_simp,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  refine (le_streamMeasure_forall_abs_integral_sub_integral_empiricalKernel_le M.P
    (measurable_optValue hγ hR) (fun _ ↦ ae_of_all _ fun s ↦ abs_le.1 (abs_optValue_le hγ hR s))
    N hδ).trans (measureReal_mono (fun ω hω p ↦ ?_) (measure_ne_top _ _))
  rw [empirical_P]
  exact (hω p).trans_eq h_r

/-- **Crude value bounds**, for the optimal action values [AJKS, Proposition 2.4]. Under the
generative model of an MDP `M` with `S` states, `A` actions and rewards bounded by `C`, for
`γ < 1`, `N ≠ 0` and `δ > 0`, with probability at least `1 - δ`, the optimal action values of `M`
and of `M.empirical N ω` differ by at most `γ C Δ / (1 - γ) ^ 2`, with
`Δ = √(2 log (2 S A / δ) / N)`. Unlike
`Learning.MDP.le_streamMeasure_forall_abs_optQValue_sub_optQValue_empirical_le`, the radius does
not grow with `√S`. -/
theorem le_streamMeasure_forall_abs_optQValue_sub_optQValue_empirical_le' {M : MDP 𝓢 𝓐 ℝ}
    {γ : ℝ≥0} (hγ : γ < 1) {C : ℝ} (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (N : ℕ) [NeZero N] {δ : ℝ}
    (hδ : 0 < δ) :
    1 - δ ≤ (streamMeasure M.P).real {ω | ∀ p,
      |M.optQValue γ p - (M.empirical N ω).optQValue γ p| ≤ γ * C *
        √(2 * log (2 * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) / N) / (1 - γ) ^ 2} := by
  refine (le_streamMeasure_forall_abs_integral_optValue_sub_integral_optValue_empirical_le hγ hR
    N hδ).trans (measureReal_mono (fun ω hω p ↦ ?_) (measure_ne_top _ _))
  exact (abs_optQValue_sub_optQValue_le (M' := M.empirical N ω) (by simp) hγ hR
    (by simpa using hR) hω p).trans_eq (by rw [sq, ← div_div]; ring)

/-- **Crude value bounds**, for the optimal policies of `M` [AJKS, Proposition 2.4]. Under the
generative model of an MDP `M` with `S` states, `A` actions and rewards bounded by `C`, for
`γ < 1`, `N ≠ 0` and `δ > 0`, with probability at least `1 - δ`, every optimal stationary policy
`π*` of `M` has action values in `M.empirical N ω` within `γ C Δ / (1 - γ) ^ 2` of the optimal
action values of `M`, with `Δ = √(2 log (2 S A / δ) / N)`. -/
theorem le_streamMeasure_forall_abs_optQValue_sub_qValue_empirical_le_of_value_eq_optValue
    {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} (hγ : γ < 1) {C : ℝ} (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (N : ℕ)
    [NeZero N] {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ (streamMeasure M.P).real {ω | ∀ (π : Kernel 𝓢 𝓐) [IsMarkovKernel π],
      M.value γ π = M.optValue γ → ∀ p,
        |M.optQValue γ p - (M.empirical N ω).qValue γ π p| ≤ γ * C *
          √(2 * log (2 * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) / N) / (1 - γ) ^ 2} := by
  refine (le_streamMeasure_forall_abs_integral_optValue_sub_integral_optValue_empirical_le hγ hR
    N hδ).trans (measureReal_mono (fun ω hω π _ hπ p ↦ ?_) (measure_ne_top _ _))
  -- `Q* = Q^π*`, and the simulation bound for `π*` only involves `v^π* = v*`
  rw [← qValue_eq_optQValue hπ]
  exact (abs_qValue_sub_qValue_le (M' := M.empirical N ω) (by simp) hγ hR (by simpa using hR)
    (fun q ↦ hπ ▸ hω q) p).trans_eq (by rw [sq, ← div_div]; ring)

end Learning.MDP
