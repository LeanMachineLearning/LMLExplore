/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.ReinforcementLearning.TemporalDifference.Synchronous

/-!
# The lower bound on the error of synchronous Q-learning

The unrolling of the error recursion of synchronous TD learning with its propagators
(`LMLExplore.ReinforcementLearning.TemporalDifference.Synchronous`) bounds the errors of
synchronous Q-learning from below [LCCWC24, Lemma 2]: for a policy `π` greedy for the optimal
action value, `Q* (s, π s) = V* s`, the error `Δ t = Q t - Q*` is a supersolution of the TD
recursion with the state-action kernel `P^π` of `π`,
`Δ (t + 1) ≥ (I - η (t + 1) (I - γ P^π)) Δ t + η (t + 1) γ (P_{t+1} - P) V t`
[LCCWC24, (33b), (34)], where `V t s = ⨆ a, Q t (s, a)`. Since the steps are monotone, `Δ t` is at
least its unrolled form `Φ 0 t Δ 0 + ξ t`, with the propagators `Φ k t` of `P^π` and the noise
term `ξ t = ∑_{k < t} η (k + 1) γ Φ (k + 1) t (P_{k+1} - P) V k`
(`LMLExplore.ReinforcementLearning.tdNoise`), and the noise term is controlled as for TD learning,
along the fixed kernel `P^π`: by Freedman's inequality and a union bound over the pairs, with high
probability, `Q* - Q t ≤ ρ 0 t C / (1 - γ) + 3 √(W ℓ) + 2 b ℓ`, with
`ρ k t = ∏_{i = k + 1}^t (1 - η i (1 - γ))`, the quadratic variation bound `W`
(`LMLExplore.ReinforcementLearning.tdNoiseVarBound`) along `P^π`, a bound `b` on the increments
and a logarithmic factor `ℓ`. A union bound gives this bound at all the iterations of a finite
set. The upper bound involves the kernels of the policies greedy for the iterates, which change
with the iteration, and is not covered by this unrolling.

## Main statements

* `LMLExplore.ReinforcementLearning.tdPropagator_add_tdNoise_le_syncQLearning_sub_optQValue`: the
  unrolled lower bound on the error of Q-learning [LCCWC24, (33b)–(35)].
* `LMLExplore.ReinforcementLearning.measure_exists_lt_optQValue_sub_syncQLearning_le`,
  `LMLExplore.ReinforcementLearning.measure_exists_mem_exists_lt_optQValue_sub_syncQLearning_le`:
  the high-probability lower bound on the error of Q-learning at the `t`-th iterate and at all
  the iterations of a finite set, the core of [LCCWC24, Lemma 2].

## References

* [LCCWC24] G. Li, C. Cai, Y. Chen, Y. Wei and Y. Chi, *Is Q-learning minimax optimal? A tight
  sample complexity analysis*, Operations Research (2024), arXiv:2102.06548.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP Bandits
open scoped NNReal

namespace LMLExplore.ReinforcementLearning

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Finite 𝓢]
  [Nonempty 𝓢] [MeasurableSingletonClass 𝓢] [Finite 𝓐] [MeasurableSingletonClass 𝓐]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {η : ℕ → ℝ} {Q₀ : 𝓢 × 𝓐 → ℝ} {C : ℝ}

/-- **The lower bound on the error of synchronous Q-learning** [LCCWC24, (33b), (34)], unrolled
with the propagators. For learning rates in `[0, 1]` and a policy `π` greedy for the optimal action
value, `Q* (s, π s) = V* s`, the error `Δ t = Q t - Q*` satisfies `Φ 0 t Δ 0 + ξ t ≤ Δ t`, where
`Φ k t` is the propagator of the mean dynamics with the state-action kernel `P^π` of `π` and
`ξ t = ∑_{k < t} η (k + 1) γ Φ (k + 1) t (P_{k+1} - P) V k` is the noise term
`LMLExplore.ReinforcementLearning.tdNoise` with this kernel. -/
theorem tdPropagator_add_tdNoise_le_syncQLearning_sub_optQValue
    (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1) (ω : ℕ → 𝓢 × 𝓐 → 𝓢) {π : 𝓢 → 𝓐}
    (hπ : ∀ s, M.optQValue γ (s, π s) = M.optValue γ s) (t : ℕ) (p : 𝓢 × 𝓐) :
    Kernel.tdPropagator (M.saKernel (Kernel.deterministic π (measurable_of_finite π))) γ η 0 t
          (fun q ↦ Q₀ q - M.optQValue γ q) p +
        tdNoise M γ η Q₀ (M.saKernel (Kernel.deterministic π (measurable_of_finite π))) t ω p ≤
      syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p := by
  have h := Kernel.tdPropagator_add_sum_le
    (κ := M.saKernel (Kernel.deterministic π (measurable_of_finite π))) (γ := γ) hη
    (x := fun t q ↦ syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q)
    (e := fun t ↦ (η (t + 1) * γ) • fun q ↦
      (⨆ a, syncQLearning (meanReward M.R) γ η Q₀ t ω (ω t q, a)) -
        ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ t ω (s', a) ∂(M.P q))
    (fun t q ↦ by
      -- one step of the lower bound [LCCWC24, (33b), (34)]
      have h := le_syncQLearning_succ_sub_optQValue (Q₀ := Q₀) (hη t).1 ω hπ q
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Kernel.tdStep_apply, integral_saKernel_deterministic _ .of_finite]
      linarith) t p
  simp only [Pi.add_apply, syncQLearning_zero] at h
  rw [tdNoise_eq_sum_apply]
  exact h

/-- If the error of the `t`-th iterate of synchronous Q-learning is below
`-(ρ 0 t C / (1 - γ) + a)`, with `ρ 0 t = ∏_{i = 1}^t (1 - η i (1 - γ))`, then the noise `ξ t p`
with the state-action kernel of a policy greedy for `Q*` is below `-a`: the contracted initial
error is at least `-ρ 0 t C / (1 - γ)`. -/
private lemma lt_neg_tdNoise_of_lt_optQValue_sub_syncQLearning (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ))) {π : 𝓢 → 𝓐}
    (hπ : ∀ s, M.optQValue γ (s, π s) = M.optValue γ s) {a : ℝ} {t : ℕ} {ω : ℕ → 𝓢 × 𝓐 → 𝓢}
    {p : 𝓢 × 𝓐}
    (h : (∏ i ∈ Ioc 0 t, (1 - η i * (1 - γ))) * (C / (1 - γ)) + a <
      M.optQValue γ p - syncQLearning (meanReward M.R) γ η Q₀ t ω p) :
    a < -1 * tdNoise M γ η Q₀ (M.saKernel (Kernel.deterministic π (measurable_of_finite π)))
      t ω p := by
  have : Nonempty 𝓐 := ⟨π (Classical.arbitrary 𝓢)⟩
  have h₀ := Kernel.abs_tdPropagator_le
    (κ := M.saKernel (Kernel.deterministic π (measurable_of_finite π))) (γ := γ)
    (k := 0) (t := t) (fun i hi ↦ mem_Icc_of_mem_Ioc hη hi) (f := fun q ↦ Q₀ q - M.optQValue γ q)
    (fun q ↦ by simpa using abs_syncQLearning_sub_optQValue_le (η := η) hγ hR hη hQ₀ 0 ω q) p
  have h₁ := tdPropagator_add_tdNoise_le_syncQLearning_sub_optQValue (Q₀ := Q₀) hη ω hπ t p
  linarith [neg_abs_le (Kernel.tdPropagator
    (M.saKernel (Kernel.deterministic π (measurable_of_finite π))) γ η 0 t
      (fun q ↦ Q₀ q - M.optQValue γ q) p)]

/-- **The high-probability lower bound on the error of synchronous Q-learning**, the core of
[LCCWC24, Lemma 2]. With rewards in `[0, C]`, `γ < 1`, learning rates in `[0, 1]`
and `0 ≤ Q₀ ≤ C / (1 - γ)`, let `π` be a policy greedy for the optimal action value,
`Q* (s, π s) = V* s`, and let `b > 0` with `η (k + 1) γ ρ (k + 1) t C / (1 - γ) ≤ b` for every
`k < t`, where `ρ k t = ∏_{i = k + 1}^t (1 - η i (1 - γ))`. Then with probability at least
`1 - S A δ`, with `S` and `A` the numbers of states and actions, for every pair `p`, the `t`-th
iterate satisfies `Q* p - Q t p ≤ ρ 0 t C / (1 - γ) + 3 √(W p ℓ) + 2 b ℓ`, with the quadratic
variation bound `W p = LMLExplore.ReinforcementLearning.tdNoiseVarBound M γ η Q₀ P^π t ω p` for
the state-action kernel `P^π` of `π`, `ℓ = max 1 (log (K / δ))` and `K = ⌈log₄ t⌉ + 1`. The
source expands the lower bound `H` times along `P^π` [LCCWC24, (88)]; here it is unrolled with the
propagators of `P^π`, as for TD learning [LCCWC24, Appendix C], and `W` is bounded in terms of the
late errors by `LMLExplore.ReinforcementLearning.tdNoiseVarBound_le`. -/
theorem measure_exists_lt_optQValue_sub_syncQLearning_le [Fintype 𝓢] [Fintype 𝓐]
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C)
    (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1) (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ)))
    {π : 𝓢 → 𝓐} (hπ : ∀ s, M.optQValue γ (s, π s) = M.optValue γ s) {δ b : ℝ} (hδ : 0 < δ)
    (hb : 0 < b) (t : ℕ)
    (hvb : ∀ k < t,
      η (k + 1) * γ * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) * (C / (1 - γ)) ≤ b) :
    streamMeasure M.P {ω | ∃ p, (∏ i ∈ Ioc 0 t, (1 - η i * (1 - γ))) * (C / (1 - γ)) +
        (3 * √(tdNoiseVarBound M γ η Q₀
            (M.saKernel (Kernel.deterministic π (measurable_of_finite π))) t ω p *
          max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) +
        2 * b * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) <
      M.optQValue γ p - syncQLearning (meanReward M.R) γ η Q₀ t ω p} ≤
      ENNReal.ofReal (Fintype.card 𝓢 * Fintype.card 𝓐 * δ) := by
  have : Nonempty 𝓐 := ⟨π (Classical.arbitrary 𝓢)⟩
  -- the noise exceeds its bound from below at some pair
  set E : 𝓢 × 𝓐 → Set (ℕ → 𝓢 × 𝓐 → 𝓢) := fun p ↦ {ω |
    3 * √(tdNoiseVarBound M γ η Q₀
        (M.saKernel (Kernel.deterministic π (measurable_of_finite π))) t ω p *
      max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) +
      2 * b * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ)) <
    -1 * tdNoise M γ η Q₀ (M.saKernel (Kernel.deterministic π (measurable_of_finite π)))
      t ω p}
  calc streamMeasure M.P _ ≤ streamMeasure M.P (⋃ p, E p) :=
        measure_mono fun ω hω ↦ by
          obtain ⟨p, hp⟩ := hω
          exact Set.mem_iUnion.2
            ⟨p, lt_neg_tdNoise_of_lt_optQValue_sub_syncQLearning hγ hR hη hQ₀ hπ hp⟩
    _ ≤ ∑ p, streamMeasure M.P (E p) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : 𝓢 × 𝓐, ENNReal.ofReal δ := sum_le_sum fun p _ ↦
        measure_three_mul_sqrt_add_lt_mul_tdNoise_le hγ hR hη hQ₀ hδ hb (by simp) t hvb p
    _ = ENNReal.ofReal (Fintype.card 𝓢 * Fintype.card 𝓐 * δ) := by
        rw [sum_const, card_univ, Fintype.card_prod, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), Nat.cast_mul]

/-- **The high-probability lower bound on the error of synchronous Q-learning at several
iterations**, the core of [LCCWC24, Lemma 2]. Under the assumptions of
`measure_exists_lt_optQValue_sub_syncQLearning_le`, let `I` be a finite set of iterations and let
`b > 0` bound the weights `η (k + 1) γ ρ (k + 1) t C / (1 - γ)` for every `t ∈ I` and `k < t`.
Then with probability at least `1 - S A #I δ`, for every iteration `t ∈ I` and every pair `p`, the
`t`-th iterate satisfies `Q* p - Q t p ≤ ρ 0 t C / (1 - γ) + 3 √(W t p ℓ t) + 2 b ℓ t`, with
`ℓ t = max 1 (log ((⌈log₄ t⌉ + 1) / δ))`. -/
theorem measure_exists_mem_exists_lt_optQValue_sub_syncQLearning_le [Fintype 𝓢] [Fintype 𝓐]
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C)
    (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1) (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ)))
    {π : 𝓢 → 𝓐} (hπ : ∀ s, M.optQValue γ (s, π s) = M.optValue γ s) {δ b : ℝ} (hδ : 0 < δ)
    (hb : 0 < b) (I : Finset ℕ)
    (hvb : ∀ t ∈ I, ∀ k < t,
      η (k + 1) * γ * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) * (C / (1 - γ)) ≤ b) :
    streamMeasure M.P {ω | ∃ t ∈ I, ∃ p,
      (∏ i ∈ Ioc 0 t, (1 - η i * (1 - γ))) * (C / (1 - γ)) +
        (3 * √(tdNoiseVarBound M γ η Q₀
            (M.saKernel (Kernel.deterministic π (measurable_of_finite π))) t ω p *
          max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) +
        2 * b * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) <
      M.optQValue γ p - syncQLearning (meanReward M.R) γ η Q₀ t ω p} ≤
      ENNReal.ofReal (Fintype.card 𝓢 * Fintype.card 𝓐 * #I * δ) := by
  refine (measure_mono fun ω hω ↦ ?_).trans ((measure_biUnion_finset_le I _).trans
    ((sum_le_sum fun t ht ↦ measure_exists_lt_optQValue_sub_syncQLearning_le hγ hR hη hQ₀ hπ hδ
      hb t (hvb t ht)).trans_eq ?_))
  · obtain ⟨t, ht, hω⟩ := hω
    exact Set.mem_biUnion ht hω
  · rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

end LMLExplore.ReinforcementLearning
