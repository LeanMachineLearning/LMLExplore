/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.TieBreaking
public import LMLExplore.ReinforcementLearning.Generative.LeaveOneOut
import LMLExplore.MeasureTheory.MeasurableSpace.Constructions
import LMLExplore.MeasureTheory.Measure.Prod

/-!
# Planning with a generative model: the perturbed plug-in policy

Let `P` be the transition kernel of an MDP with `S` states and `A` actions, with deterministic
rewards `r` in `[0, C]`, and `γ < 1`. Under the generative model `Bandits.streamMeasure P`, the
array `ω` holds `N` samples of next states per state-action pair. Li, Wei, Chi, Gu and Chen
[LWCGC24, Algorithm 1] perturb the rewards by a random vector `ζ` of independent rewards, uniform
on `[0, ξ]` and independent of the samples, and plan in the empirical MDP with transition kernel
`empiricalKernel N ω` and rewards `r + ζ`. The *perturbed plug-in policy*
`LMLExplore.ReinforcementLearning.perturbedPlugIn r N γ ω ζ` is the greedy optimal policy of this
MDP. The probability is taken over the joint law
`(streamMeasure P).prod (Measure.pi fun _ ↦ volume[|Icc 0 ξ])` of the samples and the
perturbation.

The perturbation serves the analysis:
* given the samples, it separates the optimal action values of distinct actions of the perturbed
  empirical MDP with high probability (tie-breaking, [LWCGC24, Lemma 6], in
  `MarkovDecisionProcess/TieBreaking.lean`);
* given the perturbation, the leave-one-out argument [LWCGC24, Lemma 5]
  (`ReinforcementLearning/Generative/LeaveOneOut.lean`) bounds the suboptimality of the plug-in
  policy of the perturbed model on the separation event, through the policy evaluation bound
  [LWCGC24, Lemma 1] over the full range of sample sizes;
* it changes the values of every policy by at most `ξ / (1 - γ)`.

This gives [LWCGC24, Theorem 1]: for rewards in `[0, 1]`, `0 < ε ≤ 1 / (1 - γ)`, a perturbation
level `ξ` between `(1 - γ) ε / (2 (S A) ^ 5)` and `(1 - γ) ε / 2`, `δ > 0` and
`N ≥ 5184 log (3 S A / ((1 - γ) ^ 2 ε δ)) / ((1 - γ) ^ 3 ε ^ 2)`, with probability at least
`1 - δ`, the perturbed plug-in policy `π̂` satisfies `v^π̂ ≥ v* - ε` and `Q^π̂ ≥ Q* - γ ε`. The
total number `S A N` of samples is of order `S A log (S A / ((1 - γ) ε δ)) / ((1 - γ) ^ 3 ε ^ 2)`
over the full range of accuracies `ε ≤ 1 / (1 - γ)`, where the analysis of the plug-in policy of
[AKY20] (`ReinforcementLearning/Generative/PlugIn.lean`) needs `ε ≤ (1 - γ)^(-1/2)`. This matches
the lower bound of [AMK13] up to the logarithmic factor.

[LWCGC24] takes `ξ` of order `(1 - γ) ε / (S A) ^ 5` and states the level
`log (S A / ((1 - γ) ε δ))`. The level here is the one the proof gives, through the size
`K ≈ S ^ 6 A ^ 7 / ((1 - γ) ^ 4 ε δ)` of the grid of rewards of [LWCGC24, Lemma 4] and the
factor `log (e / (1 - γ))` of [LWCGC24, Lemma 1]: `log (3 S A / ((1 - γ) ^ 2 ε δ))`. For `ε ≤ 1`, it
is at most twice `log (3 S A / ((1 - γ) ε δ))`.

## Main definitions

* `LMLExplore.ReinforcementLearning.perturbedPlugIn r N γ ω ζ`: the perturbed plug-in policy.

## Main statements

* `LMLExplore.ReinforcementLearning.measurable_perturbedPlugIn`: the perturbed plug-in policy is
  a measurable function of the samples and the perturbation.
* `LMLExplore.ReinforcementLearning.optQValue_perturbedPlugIn`: the perturbed plug-in policy is
  optimal in the perturbed empirical MDP.
* `le_streamMeasure_prod_forall_optValue_sub_sqrt_le_value_perturbedPlugIn`:
  the suboptimality of the perturbed plug-in policy, for every perturbation level `ξ > 0` and
  rewards in `[0, C]`, with the explicit level of [LWCGC24, Lemma 5].
* `le_streamMeasure_prod_forall_optValue_sub_le_value_perturbedPlugIn`,
  `le_streamMeasure_prod_forall_optQValue_sub_le_qValue_perturbedPlugIn`:
  **the perturbed plug-in policy is `ε`-optimal over the full range of accuracies**
  [LWCGC24, Theorem 1], for values and action values.

## References

* [G. Li, Y. Wei, Y. Chi, Y. Gu and Y. Chen, *Breaking the sample size barrier in model-based
  reinforcement learning with a generative model*, Operations Research, 2024][LWCGC24],
  Algorithm 1 and Theorem 1, and its proof in §6.3 (arXiv:2005.12900)
* [A. Agarwal, S. Kakade and L. F. Yang, *Model-based reinforcement learning with a generative
  model is minimax optimal*, COLT 2020][AKY20]
* [M. G. Azar, R. Munos and H. J. Kappen, *Minimax PAC bounds on the sample complexity of
  reinforcement learning with a generative model*, Machine Learning 91 (2013)][AMK13]
-/

public section

open MeasureTheory ProbabilityTheory Set LMLExplore Learning Learning.MDP Bandits
open Real (log exp)
open scoped NNReal ENNReal

namespace LMLExplore.ReinforcementLearning

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓢] [MeasurableSingletonClass 𝓐] [Fintype 𝓢] [Fintype 𝓐]
  [Nonempty 𝓢] [Nonempty 𝓐]

/-- The **perturbed plug-in policy** of [LWCGC24, Algorithm 1]: the greedy optimal policy, for the
discount factor `γ`, of the MDP whose transition kernel is the empirical kernel of the first `N`
samples `ω i p`, `i < N`, of every state-action pair `p`, and whose deterministic rewards are the
rewards `r` perturbed by `ζ`. -/
noncomputable def perturbedPlugIn (r : 𝓢 × 𝓐 → ℝ) (N : ℕ) [NeZero N] (γ : ℝ≥0)
    (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (ζ : 𝓢 × 𝓐 → ℝ) : 𝓢 → 𝓐 :=
  (ofDet (empiricalKernel N ω) (r + ζ) (measurable_of_finite _)).greedy γ
    ((ofDet (empiricalKernel N ω) (r + ζ) (measurable_of_finite _)).optValue γ)

lemma perturbedPlugIn_def (r : 𝓢 × 𝓐 → ℝ) (N : ℕ) [NeZero N] (γ : ℝ≥0)
    (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (ζ : 𝓢 × 𝓐 → ℝ) :
    perturbedPlugIn r N γ ω ζ =
      (ofDet (empiricalKernel N ω) (r + ζ) (measurable_of_finite _)).greedy γ
        ((ofDet (empiricalKernel N ω) (r + ζ) (measurable_of_finite _)).optValue γ) :=
  (rfl)

omit [Fintype 𝓢] [Fintype 𝓐] in
/-- The optimal action values of the perturbed empirical MDP are jointly measurable in the
samples and the perturbation. -/
private lemma measurable_optQValue_ofDet_empiricalKernel [Finite 𝓢] [Finite 𝓐]
    (r : 𝓢 × 𝓐 → ℝ) (N : ℕ) [NeZero N] {γ : ℝ≥0} (hγ : γ < 1) (q : 𝓢 × 𝓐) :
    Measurable fun x : (ℕ → 𝓢 × 𝓐 → 𝓢) × (𝓢 × 𝓐 → ℝ) ↦
      (ofDet (empiricalKernel N x.1) (r + x.2) (measurable_of_finite _)).optQValue γ q :=
  measurable_from_prod_of_dependsOn (Set.finite_Iio N)
    (fun ζ ω ω' h ↦ by
      simp only [empiricalKernel_congr fun i hi ↦ h i hi])
    fun ω ↦ ((continuous_optQValue_ofDet (empiricalKernel N ω) hγ q).comp
      (continuous_const.add continuous_id : Continuous fun ζ : 𝓢 × 𝓐 → ℝ ↦ r + ζ)).measurable

/-- The perturbed plug-in policy is jointly measurable in the samples and the perturbation. -/
theorem measurable_perturbedPlugIn (r : 𝓢 × 𝓐 → ℝ) (N : ℕ) [NeZero N] {γ : ℝ≥0}
    (hγ : γ < 1) :
    Measurable fun x : (ℕ → 𝓢 × 𝓐 → 𝓢) × (𝓢 × 𝓐 → ℝ) ↦ perturbedPlugIn r N γ x.1 x.2 := by
  refine measurable_pi_iff.2 fun s ↦ ?_
  simp_rw [perturbedPlugIn_def, greedy_def, ← optQValue_eq_lookahead]
  exact measurable_argmax.comp (measurable_pi_iff.2 fun a ↦
    measurable_optQValue_ofDet_empiricalKernel r N hγ (s, a))

/-- For `γ < 1`, the perturbed plug-in policy attains the optimal value of the perturbed empirical
MDP: its action at every state `s` has optimal action value `v̂* s`. -/
theorem optQValue_perturbedPlugIn (r : 𝓢 × 𝓐 → ℝ) (N : ℕ) [NeZero N] {γ : ℝ≥0} (hγ : γ < 1)
    (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (ζ : 𝓢 × 𝓐 → ℝ) (s : 𝓢) :
    (ofDet (empiricalKernel N ω) (r + ζ) (measurable_of_finite _)).optQValue γ
        (s, perturbedPlugIn r N γ ω ζ s) =
      (ofDet (empiricalKernel N ω) (r + ζ) (measurable_of_finite _)).optValue γ s := by
  have hR := ae_abs_ofDet_R_le (empiricalKernel N ω) (measurable_of_finite (r + ζ))
    fun p ↦ Finset.single_le_sum (f := fun q ↦ |(r + ζ) q|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_univ p)
  rw [perturbedPlugIn_def, optQValue_eq_lookahead, lookahead_greedy, bellman_optValue hγ hR]

omit [Fintype 𝓢] [Fintype 𝓐] in
/-- Perturbing deterministic rewards by `ζ` with values in `[0, ξ]` does not lower the optimal
value and changes the value of every stationary policy by at most `ξ / (1 - γ)`: a suboptimality
bound `b` at `s` in the perturbed MDP gives the bound `b + ξ / (1 - γ)` in the unperturbed one. -/
private lemma optValue_sub_le_value_of_perturbation [Finite 𝓢] [Finite 𝓐]
    (P : Kernel (𝓢 × 𝓐) 𝓢) [IsMarkovKernel P] {r ζ : 𝓢 × 𝓐 → ℝ} {C ξ : ℝ}
    (hr : ∀ p, |r p| ≤ C) (hζ : ∀ p, ζ p ∈ Icc 0 ξ) {γ : ℝ≥0} (hγ : γ < 1) (π : Kernel 𝓢 𝓐)
    [IsMarkovKernel π] {b : ℝ} {s : 𝓢}
    (h : (ofDet P (r + ζ) (measurable_of_finite _)).optValue γ s -
      (ofDet P (r + ζ) (measurable_of_finite _)).value γ π s ≤ b) :
    (ofDet P r (measurable_of_finite r)).optValue γ s - (b + ξ / (1 - γ)) ≤
      (ofDet P r (measurable_of_finite r)).value γ π s := by
  have hR := ae_abs_ofDet_R_le P (measurable_of_finite r) hr
  have hR' := ae_abs_ofDet_R_le P (measurable_of_finite (r + ζ)) (C := C + ξ) fun p ↦
    (abs_add_le (r p) (ζ p)).trans
      (add_le_add (hr p) (abs_le.2 ⟨by linarith [(hζ p).1, (hζ p).2], (hζ p).2⟩))
  have hv₁ := optValue_le_optValue_of_meanReward_le hγ hR hR' (by simp)
    (fun q ↦ by simp [(hζ q).1]) s
  have hv₂ := abs_value_sub_value_le (π := π) hγ hR' hR (δ := ξ) (ε := 0)
    (fun q ↦ by simp [abs_of_nonneg (hζ q).1, (hζ q).2]) (fun q ↦ by simp) s
  rw [mul_zero, zero_div, add_zero] at hv₂
  linarith [(abs_le.1 hv₂).2]

/-- **Suboptimality of the perturbed plug-in policy**, with an explicit level [LWCGC24, proof of
Theorem 1]. Let `P` be a transition kernel on `S` states and `A` actions, `r` deterministic
rewards in `[0, C]`, `γ < 1`, `ξ > 0`, `δ > 0`, `K` with
`32 (1 + γ) (C + ξ) S A ^ 2 ≤ (1 - γ) ^ 3 ξ δ K`, and
`L = log (16 S A (K + 1) log (e / (1 - γ)) / δ)`. If `18 L ≤ (1 - γ) N`, then with probability at
least `1 - δ` under the joint law of the samples of the generative model and of a perturbation `ζ`
of independent rewards uniform on `[0, ξ]`, the perturbed plug-in policy `π̂` satisfies

`v^π̂ ≥ v* - 6 (C + ξ) √(2 L / (N (1 - γ) ^ 3)) - ξ / (1 - γ)`

at every state, for the values of the MDP `ofDet P r` with the unperturbed rewards. -/
theorem le_streamMeasure_prod_forall_optValue_sub_sqrt_le_value_perturbedPlugIn
    (P : Kernel (𝓢 × 𝓐) 𝓢) [IsMarkovKernel P] {r : 𝓢 × 𝓐 → ℝ} {C : ℝ}
    (hr : ∀ p, r p ∈ Icc 0 C) {γ : ℝ≥0} (hγ : γ < 1) {ξ : ℝ} (hξ : 0 < ξ) {δ : ℝ} (hδ : 0 < δ)
    {K : ℕ} (hK : 32 * (1 + γ) * (C + ξ) * (Fintype.card 𝓢 * Fintype.card 𝓐 ^ 2) ≤
      (1 - γ) ^ 3 * ξ * δ * K) (N : ℕ) [NeZero N]
    (hN : 18 * log (16 * Fintype.card 𝓢 * Fintype.card 𝓐 * (K + 1) * log (exp 1 / (1 - γ)) / δ) ≤
      (1 - γ) * N) :
    1 - δ ≤ ((streamMeasure P).prod (Measure.pi fun _ : 𝓢 × 𝓐 ↦ volume[|Icc 0 ξ])).real {x |
      ∀ s, (ofDet P r (measurable_of_finite r)).optValue γ s -
          (6 * (C + ξ) * √(2 * log (16 * Fintype.card 𝓢 * Fintype.card 𝓐 * (K + 1) *
            log (exp 1 / (1 - γ)) / δ) / (N * (1 - γ) ^ 3)) + ξ / (1 - γ)) ≤
        (ofDet P r (measurable_of_finite r)).value γ
          (Kernel.deterministic (perturbedPlugIn r N γ x.1 x.2) (measurable_of_finite _)) s} := by
  -- The event `D` that the perturbed empirical MDP separates its optimal action values has
  -- probability at least `1 - δ / 2` given the samples, by tie-breaking [LWCGC24, Lemma 6]. Given
  -- the perturbation, the leave-one-out bound [LWCGC24, Lemma 5] holds on `D` with probability
  -- at least `1 - δ / 2`, in the perturbed model. The perturbation changes values by at most
  -- `ξ / (1 - γ)`, which transfers the bound to the unperturbed model.
  set μ := streamMeasure P
  have hIcc : volume (Icc 0 ξ) = ENNReal.ofReal ξ := by simp
  have : IsProbabilityMeasure (volume[|Icc 0 ξ]) :=
    cond_isProbabilityMeasure_of_finite (by simp [hIcc, hξ]) (by simp [hIcc])
  set ν := Measure.pi fun _ : 𝓢 × 𝓐 ↦ volume[|Icc 0 ξ]
  set S : ℝ := (Fintype.card 𝓢 : ℝ)
  set A : ℝ := (Fintype.card 𝓐 : ℝ)
  set lg := log (exp 1 / (1 - γ))
  set L := log (16 * S * A * (K + 1) * lg / δ)
  set B := 6 * (C + ξ) * √(2 * L / (N * (1 - γ) ^ 3)) + ξ / (1 - γ)
  set M := ofDet P r (measurable_of_finite r)
  set η := ξ * (δ / 2) * (1 - γ) / (2 * (S * A ^ 2))
  have hC : 0 ≤ C := (hr (Classical.arbitrary _)).1.trans (hr _).2
  have hu : 0 < 1 - (γ : ℝ) := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  have hS : 0 < S := Nat.cast_pos.2 Fintype.card_pos
  have hA : 0 < A := Nat.cast_pos.2 Fintype.card_pos
  -- the events `D` and `G`, and their measurability
  set Q := fun (x : (ℕ → 𝓢 × 𝓐 → 𝓢) × (𝓢 × 𝓐 → ℝ)) (q : 𝓢 × 𝓐) ↦
    (ofDet (empiricalKernel N x.1) (r + x.2) (measurable_of_finite _)).optQValue γ q with hQ_def
  set D := {x | ∀ s a₁ a₂, a₁ ≠ a₂ → η < |Q x (s, a₁) - Q x (s, a₂)|} with hD_def
  set G := {x : (ℕ → 𝓢 × 𝓐 → 𝓢) × (𝓢 × 𝓐 → ℝ) | ∀ s, M.optValue γ s - B ≤
    M.value γ (Kernel.deterministic (perturbedPlugIn r N γ x.1 x.2) (measurable_of_finite _)) s}
    with hG_def
  have hD : MeasurableSet D :=
    measurableSet_setOfPred.2 (Measurable.forall fun s ↦ Measurable.forall fun a₁ ↦
      Measurable.forall fun a₂ ↦ measurable_const.imp (measurableSet_setOfPred.1
        (measurableSet_lt measurable_const
          (continuous_abs.measurable.comp ((measurable_optQValue_ofDet_empiricalKernel r N hγ _).sub
            (measurable_optQValue_ofDet_empiricalKernel r N hγ _))))))
  have hG : MeasurableSet G :=
    measurable_perturbedPlugIn r N hγ (Set.to_countable {d : 𝓢 → 𝓐 | ∀ s, M.optValue γ s - B ≤
      M.value γ (Kernel.deterministic d (measurable_of_finite _)) s}).measurableSet
  -- tie-breaking, given the samples
  have h₁ : ENNReal.ofReal (1 - δ / 2) ≤ μ.prod ν D := by
    have h := Measure.le_prod_apply_of_ae_le (μ := μ) (ν := ν) hD (c := ENNReal.ofReal (1 - δ / 2))
      (ae_of_all _ fun ω ↦ ENNReal.ofReal_le_of_le_toReal ?_)
    · rwa [measure_univ, mul_one] at h
    exact (le_measureReal_pi_cond_Icc_forall_lt_abs_optQValue_ofDet_sub (empiricalKernel N ω) r
      hγ hξ (half_pos hδ).le).trans (measureReal_mono fun ζ hζ ↦ hζ)
  set H := {x | x ∈ D → x ∈ G} with hH_def
  have hH : MeasurableSet H := measurableSet_setOfPred.2 (hD.mem.imp hG.mem)
  have hK₀ : 0 < K := by
    rcases Nat.eq_zero_or_pos K with hK₀ | hK₀
    · rw [hK₀, Nat.cast_zero, mul_zero] at hK
      have : 0 < 32 * (1 + (γ : ℝ)) * (C + ξ) * (S * A ^ 2) := by positivity
      linarith
    · exact hK₀
  have hη : 0 < η := by positivity
  have hKη : 8 * ((1 + γ) * (C + ξ) / (1 - γ)) ≤ (1 - γ) * η * K := by
    have h : (1 - γ) * η * K = (1 - γ) ^ 3 * ξ * δ * K / ((1 - γ) * (4 * (S * A ^ 2))) := by
      simp only [η]
      field_simp
      ring
    rw [h, le_div_iff₀ (by positivity)]
    calc 8 * ((1 + γ) * (C + ξ) / (1 - γ)) * ((1 - γ) * (4 * (S * A ^ 2)))
        = 32 * (1 + γ) * (C + ξ) * (S * A ^ 2) := by field_simp; ring
      _ ≤ (1 - γ) ^ 3 * ξ * δ * K := hK
  have h8 : 8 * S * A * (K + 1) * lg / (δ / 2) = 16 * S * A * (K + 1) * lg / δ := by
    field_simp
    ring
  -- the leave-one-out bound, given the perturbation
  have hae : ∀ᵐ ζ ∂ν, ∀ p, ζ p ∈ Icc 0 ξ := Filter.eventually_all.2 fun _ ↦
    Measure.tendsto_eval_ae_ae.eventually (ae_cond_mem measurableSet_Icc)
  have h₂ : ENNReal.ofReal (1 - δ / 2) ≤ μ.prod ν H := by
    have h := Measure.le_prod_apply_of_ae_le_symm (μ := μ) (ν := ν) hH
      (c := ENNReal.ofReal (1 - δ / 2)) (hae.mono fun ζ hζ ↦ ENNReal.ofReal_le_of_le_toReal ?_)
    · rwa [measure_univ, mul_one] at h
    have hR' : ∀ p, ∀ᵐ x ∂((ofDet P (r + ζ) (measurable_of_finite _)).R p), x ∈ Icc 0 (C + ξ) :=
      fun p ↦ by
        simp only [ofDet_R, Kernel.deterministic_apply, ae_dirac_eq, Filter.eventually_pure,
          Pi.add_apply]
        exact ⟨add_nonneg (hr p).1 (hζ p).1, add_le_add (hr p).2 (hζ p).2⟩
    have hLOO := le_streamMeasure_forall_optValue_sub_value_le_of_separated
      (M := ofDet P (r + ζ) (measurable_of_finite _)) hγ hR' hη hK₀ hKη N (half_pos hδ)
      (by rwa [h8])
    simp only [ofDet_P, ofDet_empirical, ← perturbedPlugIn_def] at hLOO
    rw [h8] at hLOO
    refine hLOO.trans (measureReal_mono (fun ω hω hDω s ↦ ?_) (measure_ne_top _ _))
    -- the perturbed empirical MDP is separated at its greedy optimal policy
    have hRₑ := ae_abs_ofDet_R_le (empiricalKernel N ω) (measurable_of_finite (r + ζ))
      (C := C + ξ) fun p ↦ abs_le.2 ⟨by simp only [Pi.add_apply]; linarith [(hr p).1, (hζ p).1],
        add_le_add (hr p).2 (hζ p).2⟩
    have hsep : ∀ s a, a ≠ perturbedPlugIn r N γ ω ζ s →
        (ofDet (empiricalKernel N ω) (r + ζ) (measurable_of_finite _)).optQValue γ (s, a) + η ≤
          (ofDet (empiricalKernel N ω) (r + ζ) (measurable_of_finite _)).optQValue γ
            (s, perturbedPlugIn r N γ ω ζ s) := fun s a ha ↦ by
      have := optQValue_add_lt_optValue_of_forall_lt_abs_optQValue_sub hγ hRₑ
        (fun a₁ a₂ h ↦ hDω s a₁ a₂ h) (optQValue_perturbedPlugIn r N hγ ω ζ s) ha
      rw [optQValue_perturbedPlugIn r N hγ ω ζ s]
      exact this.le
    -- the perturbation changes the values by at most `ξ / (1 - γ)`
    exact optValue_sub_le_value_of_perturbation P (fun p ↦ abs_le.2 ⟨by linarith [(hr p).1],
      (hr p).2⟩) hζ hγ _ (hω hsep s)
  -- the two events
  have hD' : 1 - δ / 2 ≤ (μ.prod ν).real D :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h₁
  have hH' : 1 - δ / 2 ≤ (μ.prod ν).real H :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h₂
  have h := measureReal_union_add_inter (μ := μ.prod ν) (s := D) hH
  have h₃ : (μ.prod ν).real (D ∪ H) ≤ 1 := measureReal_le_one
  exact le_trans (by linarith) (measureReal_mono (s₁ := D ∩ H) (fun x ⟨hx, hxH⟩ ↦ hxH hx)
    (measure_ne_top _ _))

/-- The sample-size arithmetic of [LWCGC24, Theorem 1]: under its hypotheses, some size `K` of the
grid of rewards satisfies the hypotheses of
`le_streamMeasure_prod_forall_optValue_sub_sqrt_le_value_perturbedPlugIn` for rewards in `[0, 1]`,
and the bound of this theorem is at most `ε`. -/
private lemma exists_grid_size_perturbedPlugIn {γ : ℝ≥0} (hγ : γ < 1) {ε : ℝ} (hε : 0 < ε)
    (hεγ : ε ≤ 1 / (1 - γ)) {ξ : ℝ} (hξ' : 0 < ξ)
    (hξ₀ : (1 - γ) * ε ≤ 2 * (Fintype.card 𝓢 * Fintype.card 𝓐) ^ 5 * ξ)
    (hξ : ξ ≤ (1 - γ) * ε / 2) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (N : ℕ) [NeZero N]
    (hN : 5184 * log (3 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) ^ 2 * ε * δ)) /
      ((1 - γ) ^ 3 * ε ^ 2) ≤ N) :
    ∃ K : ℕ, 32 * (1 + γ) * (1 + ξ) * (Fintype.card 𝓢 * Fintype.card 𝓐 ^ 2) ≤
        (1 - γ) ^ 3 * ξ * δ * K ∧
      18 * log (16 * Fintype.card 𝓢 * Fintype.card 𝓐 * (K + 1) * log (exp 1 / (1 - γ)) / δ) ≤
        (1 - γ) * N ∧
      6 * (1 + ξ) * √(2 * log (16 * Fintype.card 𝓢 * Fintype.card 𝓐 * (K + 1) *
        log (exp 1 / (1 - γ)) / δ) / (N * (1 - γ) ^ 3)) + ξ / (1 - γ) ≤ ε := by
  -- With `a = S A` and `w = 1 / ((1 - γ) ((1 - γ) ε) δ) ≥ 1`, the grid size `K = ⌈192 a ^ 7 w ^ 3⌉`
  -- satisfies the hypothesis on `K`, and the level `L` of the explicit statement is at most
  -- `8 ℓ`, where `ℓ = log (3 a w)` is the level of `hN`. The hypothesis `hN` then controls both
  -- `18 L ≤ (1 - γ) N` and the bound.
  set S : ℝ := (Fintype.card 𝓢 : ℝ)
  set A : ℝ := (Fintype.card 𝓐 : ℝ)
  set t : ℝ := 1 - γ with ht_def
  have ht : 0 < t := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  have ht1 : t ≤ 1 := sub_le_self _ γ.coe_nonneg
  have hu1 : t * ε ≤ 1 := by rwa [le_div_iff₀ ht, mul_comm] at hεγ
  have hS : 1 ≤ S := Nat.one_le_cast.2 Fintype.card_pos
  have hA : 1 ≤ A := Nat.one_le_cast.2 Fintype.card_pos
  set a := S * A with ha_def
  have ha : 1 ≤ a := one_le_mul_of_one_le_of_one_le hS hA
  have hξ1 : ξ ≤ 1 / 2 := hξ.trans (by linarith)
  -- `w = 1 / ((1 - γ) ((1 - γ) ε) δ)` bounds `1 / (1 - γ)` and `1 / δ`
  set w := 1 / (t * (t * ε) * δ) with hw_def
  have hw₀ : 0 < t * (t * ε) * δ := by positivity
  have hw1 : 1 ≤ w := by
    rw [hw_def, le_div_iff₀ hw₀, one_mul]
    calc t * (t * ε) * δ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  have htw : 1 / t ≤ w := by
    rw [hw_def]
    gcongr
    calc t * (t * ε) * δ ≤ t * 1 * 1 := by gcongr
      _ = t := by ring
  have hδw : 1 / δ ≤ w := by
    rw [hw_def]
    gcongr
    calc t * (t * ε) * δ ≤ 1 * 1 * δ := by gcongr
      _ = δ := by ring
  -- the size `K` of the grid of rewards
  set K := ⌈192 * a ^ 7 * w ^ 3⌉₊
  have hK : 32 * (1 + γ) * (1 + ξ) * (S * A ^ 2) ≤ t ^ 3 * ξ * δ * K := by
    have hKw : 192 * a ^ 7 * w ^ 3 ≤ K := Nat.le_ceil _
    have h₁ : t ^ 3 * ξ * δ * (192 * a ^ 7 * w ^ 3) = 192 * a ^ 7 * ξ / ((t * ε) ^ 3 * δ ^ 2) := by
      rw [hw_def]
      field_simp
    have h₂ : 96 * a ^ 2 ≤ 192 * a ^ 7 * ξ / ((t * ε) ^ 3 * δ ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have h₃ : (t * ε) ^ 3 * δ ^ 2 ≤ t * ε := by
        calc (t * ε) ^ 3 * δ ^ 2 = (t * ε) * ((t * ε) ^ 2 * δ ^ 2) := by ring
          _ ≤ (t * ε) * (1 * 1) := by
            gcongr
            · exact pow_le_one₀ (by positivity) hu1
            · exact pow_le_one₀ hδ.le hδ1.le
          _ = t * ε := by ring
      calc 96 * a ^ 2 * ((t * ε) ^ 3 * δ ^ 2) ≤ 96 * a ^ 2 * (t * ε) := by gcongr
        _ ≤ 96 * a ^ 2 * (2 * a ^ 5 * ξ) := by gcongr
        _ = 192 * a ^ 7 * ξ := by ring
    have h₄ : 32 * (1 + γ) * (1 + ξ) * (S * A ^ 2) ≤ 96 * a ^ 2 := by
      have hγ2 : (1 + γ : ℝ) ≤ 2 := by linarith [NNReal.coe_lt_one.2 hγ]
      calc 32 * (1 + γ) * (1 + ξ) * (S * A ^ 2) ≤ 32 * 2 * (3 / 2) * (S * A ^ 2) := by
            gcongr
            linarith
        _ = 96 * (S * A ^ 2) := by ring
        _ ≤ 96 * a ^ 2 := by
            rw [ha_def]
            gcongr
            nlinarith
    calc 32 * (1 + γ) * (1 + ξ) * (S * A ^ 2) ≤ 192 * a ^ 7 * ξ / ((t * ε) ^ 3 * δ ^ 2) :=
          h₄.trans h₂
      _ = t ^ 3 * ξ * δ * (192 * a ^ 7 * w ^ 3) := h₁.symm
      _ ≤ t ^ 3 * ξ * δ * K := by gcongr
  -- the level `L` of the explicit bound is at most `8 ℓ`, with `ℓ` the level of `hN`
  set ℓ := log (3 * S * A / (t ^ 2 * ε * δ)) with hℓ_def
  have hℓ : ℓ = log (3 * (a * w)) := by
    rw [hℓ_def]
    congr 1
    rw [hw_def, ha_def]
    field_simp
  have hℓ₀ : 0 ≤ ℓ := by
    rw [hℓ]
    exact Real.log_nonneg (by nlinarith)
  set L := log (16 * S * A * (K + 1) * log (exp 1 / t) / δ)
  have hlg : log (exp 1 / t) ≤ w := by
    rw [Real.log_div (Real.exp_pos 1).ne' ht.ne', Real.log_exp]
    have := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
    rw [Real.log_inv] at this
    rw [one_div] at htw
    linarith
  have hlg₀ : 0 < log (exp 1 / t) := Real.log_pos (by
    rw [lt_div_iff₀ ht, one_mul]
    linarith [Real.add_one_le_exp (1 : ℝ)])
  have hLℓ : L ≤ 8 * ℓ := by
    have hK1 : (K : ℝ) + 1 ≤ 194 * a ^ 7 * w ^ 3 := by
      have h₁ := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 192 * a ^ 7 * w ^ 3)
      have h₂ : 1 ≤ a ^ 7 * w ^ 3 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ ha)
        (one_le_pow₀ hw1)
      linarith
    rw [hℓ, show (8 : ℝ) * log (3 * (a * w)) = log ((3 * (a * w)) ^ 8) by
      rw [Real.log_pow]; norm_num]
    refine Real.log_le_log (by positivity) ?_
    calc 16 * S * A * (K + 1) * log (exp 1 / t) / δ
        = 16 * a * (K + 1) * log (exp 1 / t) * (1 / δ) := by rw [ha_def]; ring
      _ ≤ 16 * a * (194 * a ^ 7 * w ^ 3) * w * w := by gcongr
      _ = 3104 * a ^ 8 * w ^ 5 := by ring
      _ ≤ 6561 * a ^ 8 * w ^ 8 := by
          have h₅ : w ^ 5 ≤ w ^ 8 := pow_le_pow_right₀ hw1 (by norm_num)
          have h₈ : 0 ≤ a ^ 8 := by positivity
          have h₅' : 0 ≤ w ^ 5 := by positivity
          nlinarith
      _ = (3 * (a * w)) ^ 8 := by ring
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNℓ : 5184 * ℓ ≤ t ^ 3 * ε ^ 2 * N := by
    rwa [div_le_iff₀ (by positivity), mul_comm (N : ℝ)] at hN
  have hN' : 18 * L ≤ t * N := by
    have : t ^ 3 * ε ^ 2 * N ≤ t * N := by
      calc t ^ 3 * ε ^ 2 * N = (t * ε) ^ 2 * (t * N) := by ring
        _ ≤ 1 * (t * N) := by gcongr; exact pow_le_one₀ (by positivity) hu1
        _ = t * N := one_mul _
    linarith
  refine ⟨K, hK, hN', ?_⟩
  -- the bound of the explicit statement is at most `ε`
  have hsq : √(2 * L / (N * t ^ 3)) ≤ ε / 18 := by
    rw [show ε / 18 = √((ε / 18) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hξt : ξ / t ≤ ε / 2 := by
    rw [div_le_iff₀ ht]
    linarith
  have : 6 * (1 + ξ) * √(2 * L / (N * t ^ 3)) ≤ 9 * (ε / 18) := by
    gcongr
    linarith
  linarith

/-- **The perturbed plug-in policy is `ε`-optimal over the full range of accuracies**, for values
[LWCGC24, Theorem 1]. Let `P` be a transition kernel on `S` states and `A` actions, `r`
deterministic rewards in `[0, 1]`, `γ < 1`, `0 < ε ≤ 1 / (1 - γ)`, `ξ` with
`(1 - γ) ε / (2 (S A) ^ 5) ≤ ξ ≤ (1 - γ) ε / 2` and `δ > 0`. If
`N ≥ 5184 log (3 S A / ((1 - γ) ^ 2 ε δ)) / ((1 - γ) ^ 3 ε ^ 2)`, then with probability at least
`1 - δ` under the joint law of the samples of the generative model and of a perturbation of
independent rewards uniform on `[0, ξ]`, the perturbed plug-in policy `π̂` satisfies
`v^π̂ ≥ v* - ε` at every state.

[LWCGC24] states the level `log (S A / ((1 - γ) ε δ))`; the level here is the one its proof gives,
and it is at most twice `log (3 S A / ((1 - γ) ε δ))` for `ε ≤ 1`. -/
theorem le_streamMeasure_prod_forall_optValue_sub_le_value_perturbedPlugIn
    (P : Kernel (𝓢 × 𝓐) 𝓢) [IsMarkovKernel P] {r : 𝓢 × 𝓐 → ℝ} (hr : ∀ p, r p ∈ Icc 0 1)
    {γ : ℝ≥0} (hγ : γ < 1) {ε : ℝ} (hε : 0 < ε) (hεγ : ε ≤ 1 / (1 - γ)) {ξ : ℝ}
    (hξ₀ : (1 - γ) * ε ≤ 2 * (Fintype.card 𝓢 * Fintype.card 𝓐) ^ 5 * ξ)
    (hξ : ξ ≤ (1 - γ) * ε / 2) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) [NeZero N]
    (hN : 5184 * log (3 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) ^ 2 * ε * δ)) /
      ((1 - γ) ^ 3 * ε ^ 2) ≤ N) :
    1 - δ ≤ ((streamMeasure P).prod (Measure.pi fun _ : 𝓢 × 𝓐 ↦ volume[|Icc 0 ξ])).real {x |
      ∀ s, (ofDet P r (measurable_of_finite r)).optValue γ s - ε ≤
        (ofDet P r (measurable_of_finite r)).value γ
          (Kernel.deterministic (perturbedPlugIn r N γ x.1 x.2) (measurable_of_finite _)) s} := by
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact (sub_nonpos.2 hδ1).trans measureReal_nonneg
  have hξ' : 0 < ξ := by
    have h : 0 < 2 * ((Fintype.card 𝓢 : ℝ) * Fintype.card 𝓐) ^ 5 * ξ :=
      (mul_pos (sub_pos.2 (NNReal.coe_lt_one.2 hγ)) hε).trans_le hξ₀
    exact pos_of_mul_pos_right h (by positivity)
  obtain ⟨K, hK, hN', hB⟩ :=
    exists_grid_size_perturbedPlugIn hγ hε hεγ hξ' hξ₀ hξ hδ hδ1 N hN
  exact (le_streamMeasure_prod_forall_optValue_sub_sqrt_le_value_perturbedPlugIn P (C := 1) hr hγ
    hξ' hδ hK N hN').trans (measureReal_mono (fun x hx s ↦ (hx s).trans' (sub_le_sub_left hB _))
      (measure_ne_top _ _))

/-- **The perturbed plug-in policy is `ε`-optimal over the full range of accuracies**, for action
values [LWCGC24, Theorem 1]. Under the hypotheses of
`le_streamMeasure_prod_forall_optValue_sub_le_value_perturbedPlugIn`,
with probability at least `1 - δ`, the perturbed plug-in policy `π̂` satisfies
`Q^π̂ ≥ Q* - γ ε` at every state-action pair. -/
theorem le_streamMeasure_prod_forall_optQValue_sub_le_qValue_perturbedPlugIn
    (P : Kernel (𝓢 × 𝓐) 𝓢) [IsMarkovKernel P] {r : 𝓢 × 𝓐 → ℝ} (hr : ∀ p, r p ∈ Icc 0 1)
    {γ : ℝ≥0} (hγ : γ < 1) {ε : ℝ} (hε : 0 < ε) (hεγ : ε ≤ 1 / (1 - γ)) {ξ : ℝ}
    (hξ₀ : (1 - γ) * ε ≤ 2 * (Fintype.card 𝓢 * Fintype.card 𝓐) ^ 5 * ξ)
    (hξ : ξ ≤ (1 - γ) * ε / 2) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) [NeZero N]
    (hN : 5184 * log (3 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) ^ 2 * ε * δ)) /
      ((1 - γ) ^ 3 * ε ^ 2) ≤ N) :
    1 - δ ≤ ((streamMeasure P).prod (Measure.pi fun _ : 𝓢 × 𝓐 ↦ volume[|Icc 0 ξ])).real {x |
      ∀ p, (ofDet P r (measurable_of_finite r)).optQValue γ p - γ * ε ≤
        (ofDet P r (measurable_of_finite r)).qValue γ
          (Kernel.deterministic (perturbedPlugIn r N γ x.1 x.2) (measurable_of_finite _)) p} := by
  have hR := ae_abs_ofDet_R_le P (measurable_of_finite r) (C := 1) fun p ↦
    abs_le.2 ⟨by linarith [(hr p).1], (hr p).2⟩
  refine (le_streamMeasure_prod_forall_optValue_sub_le_value_perturbedPlugIn P hr hγ hε hεγ hξ₀
    hξ hδ N hN).trans (measureReal_mono (fun x hx p ↦ ?_) (measure_ne_top _ _))
  have h := optQValue_sub_qValue_le_of_optValue_sub_value_le hγ hR
    (fun s ↦ sub_le_comm.1 (hx s)) p
  linarith

end LMLExplore.ReinforcementLearning

end
