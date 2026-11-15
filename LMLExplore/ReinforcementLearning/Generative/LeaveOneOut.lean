/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.ReinforcementLearning.Generative.Decoupling
public import LMLExplore.ReinforcementLearning.Generative.PolicyEvaluation
import LMLExplore.Analysis.SpecialFunctions.Log.Basic

/-!
# Planning with a generative model: leave-one-out evaluation of the separated plug-in policy

Let `M` be an MDP with `S` states, `A` actions and rewards in `[0, C]`, `γ < 1`, and
`M̂ = M.empirical N ω` the empirical MDP of `N` samples per state-action pair under the generative
model `Bandits.streamMeasure M.P`. The plug-in policy `π̂` is the greedy optimal policy of `M̂`. It
depends on all the samples, so that the evaluation bound of
`ReinforcementLearning/Generative/PolicyEvaluation.lean` [LWCGC24, Lemma 1], which needs a policy
fixed independently of the data, does not apply to it directly.

Li, Wei, Chi, Gu and Chen [LWCGC24, Lemma 5] remove this dependence when the optimal action values
of `M̂` are *separated* by `η > 0`: at every state `s`, every action `a ≠ π̂ s` has
`Q̂* (s, a) + η ≤ Q̂* (s, π̂ s)` (the event `B_η` of [LWCGC24, (41)]). Their leave-one-out argument
runs through the state-action absorbing modifications `M̂.saAbsorbing p c`
(`MarkovDecisionProcess/Absorbing/StateAction.lean`):
* the modification at `p` is computed from the samples of the pairs other than `p`, so that every
  function of it, such as its greedy optimal policy, is independent of the samples of `p`
  (`Learning.MDP.indepFun_comp_saAbsorbing_empirical` in
  `ReinforcementLearning/Generative/Decoupling.lean`), and Bernstein's inequality applies at `p`
  to every function of the modification;
* under the separation, a uniform grid of rewards `c`, fixed in advance, contains one whose
  modification at `p` has the greedy optimal policy `π̂` [LWCGC24, Lemma 4].

A union bound over the pairs `p`, the points of the grid and the levels of [LWCGC24, Lemma 2],
`ProbabilityTheory.Kernel.abs_integral_resolvent_sub_integral_resolvent_le_of_abs_sub_le`, then
gives the Bernstein-type deviations of the empirical state kernel of `π̂` that Lemma 2 needs, in
the form of `Learning.MDP.abs_value_sub_value_le_of_abs_integral_stateKernel_sub_le`.
With `K + 1` grid points, `8 (1 + γ) C / (1 - γ) ≤ (1 - γ) η K`, `δ > 0` and
`L = log (4 S A (K + 1) log (e / (1 - γ)) / δ)`, as soon as `18 L ≤ (1 - γ) N`, with probability
at least `1 - δ`, if `M̂` is separated by `η`, then

`|v̂^π̂ - v^π̂| ≤ 3 C √(2 L / (N (1 - γ) ^ 3))`.

Combined with [LWCGC24, Lemma 1] for the greedy optimal policy of `M`, which does not depend on the
samples, and with the optimality of `π̂` in `M̂`, this bounds the suboptimality of the plug-in
policy: with probability at least `1 - δ`, if `M̂` is separated by `η`, then
`v* - v^π̂ ≤ 6 C √(2 L' / (N (1 - γ) ^ 3))`, with `L' = log (8 S A (K + 1) log (e / (1 - γ)) / δ)`
the level of the first bound at `δ / 2`.

[LWCGC24, Lemma 5] assumes that the separation holds with probability at least `1 - δ` and
concludes with probability at least `1 - 3 δ`. The statements here hold on the separation event,
whatever its probability, so that they combine with any tie-breaking argument.

The grid size only enters through `log (K + 1)`: for `η` polynomially small in `S`, `A`,
`1 - γ` and `δ`, as produced by the random perturbation of the rewards of [LWCGC24, Lemma 6]
(`MarkovDecisionProcess/TieBreaking.lean`), the bound is of order `√(L / (N (1 - γ) ^ 3))` with a
logarithmic `L`, over the full range of sample sizes `N ≳ L / (1 - γ)`.

## Main statements

* `Learning.MDP.le_streamMeasure_forall_abs_value_empirical_sub_value_le_of_separated`: the
  evaluation of the separated plug-in policy [LWCGC24, Lemma 5, first claim].
* `Learning.MDP.le_streamMeasure_forall_optValue_sub_value_le_of_separated`: the suboptimality of
  the separated plug-in policy [LWCGC24, Lemma 5, second claim].

## References

* [G. Li, Y. Wei, Y. Chi, Y. Gu and Y. Chen, *Breaking the sample size barrier in model-based
  reinforcement learning with a generative model*, Operations Research, 2024][LWCGC24], §6.3.2,
  Lemma 5 and its proof in Appendix B.4 (arXiv:2005.12900)
-/

public section

open MeasureTheory ProbabilityTheory LMLExplore Learning Bandits
open Real (log exp)
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 𝓡 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓡 : MeasurableSpace 𝓡} [MeasurableSingletonClass 𝓢] [MeasurableSingletonClass 𝓐]

section Generative

variable [Fintype 𝓢] [Fintype 𝓐] [Nonempty 𝓢] [Nonempty 𝓐]

/-- **Evaluation of the separated plug-in policy** [LWCGC24, Lemma 5, first claim]. Under the
generative model of an MDP `M` with `S` states, `A` actions and rewards in `[0, C]`, let `γ < 1`,
`η > 0`, `K > 0` with `8 (1 + γ) C / (1 - γ) ≤ (1 - γ) η K`, `δ > 0` and
`L = log (4 S A (K + 1) log (e / (1 - γ)) / δ)`. If `18 L ≤ (1 - γ) N`, then with probability at
least `1 - δ`, whenever the optimal action values of the empirical MDP `M̂ = M.empirical N ω` are
separated by `η` at its greedy optimal policy `π̂` (`Q̂* (s, a) + η ≤ Q̂* (s, π̂ s)` for every
`a ≠ π̂ s`), the value of `π̂` in `M̂` satisfies `|v̂^π̂ - v^π̂| ≤ 3 C √(2 L / (N (1 - γ) ^ 3))` at
every state.

For rewards in `[0, 1]`, [LWCGC24] uses the grid of spacing `(1 - γ) η / 4` on
`[-1 / (1 - γ), 1 / (1 - γ)]`, with `K ≤ 8 / ((1 - γ) ^ 2 η)`, assumes
`N ≥ 16 e ^ 2 β₁ / (1 - γ)` for the corresponding `β₁ = 2 L`, and proves the bound with the
constant `6` in place of `3`; the constant `3` comes from the constant `1` of
`ProbabilityTheory.Kernel.integral_sqrt_variance_integral_resolvent_le`. -/
theorem le_streamMeasure_forall_abs_value_empirical_sub_value_le_of_separated {M : MDP 𝓢 𝓐 ℝ}
    {γ : ℝ≥0} (hγ : γ < 1) {C : ℝ} (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) {η : ℝ}
    (hη : 0 < η) {K : ℕ} (hK : 0 < K) (hKη : 8 * ((1 + γ) * C / (1 - γ)) ≤ (1 - γ) * η * K)
    (N : ℕ) [NeZero N] {δ : ℝ} (hδ : 0 < δ)
    (hN : 18 * log (4 * Fintype.card 𝓢 * Fintype.card 𝓐 * (K + 1) * log (exp 1 / (1 - γ)) / δ) ≤
      (1 - γ) * N) :
    1 - δ ≤ (streamMeasure M.P).real {ω |
      (∀ s a, a ≠ (M.empirical N ω).greedy γ ((M.empirical N ω).optValue γ) s →
        (M.empirical N ω).optQValue γ (s, a) + η ≤
          (M.empirical N ω).optQValue γ
            (s, (M.empirical N ω).greedy γ ((M.empirical N ω).optValue γ) s)) →
      ∀ s, |(M.empirical N ω).value γ (Kernel.deterministic
            ((M.empirical N ω).greedy γ ((M.empirical N ω).optValue γ))
            (measurable_of_finite _)) s -
          M.value γ (Kernel.deterministic
            ((M.empirical N ω).greedy γ ((M.empirical N ω).optValue γ))
            (measurable_of_finite _)) s| ≤
        3 * C * √(2 * log (4 * Fintype.card 𝓢 * Fintype.card 𝓐 * (K + 1) *
          log (exp 1 / (1 - γ)) / δ) / (N * (1 - γ) ^ 3))} := by
  -- For every pair `p`, point `k` of the grid and level `l ≤ m = ⌈log (1 - γ)⁻¹⌉₊`, Bernstein's
  -- inequality at `p` holds for the `l`-th level `V d l` of [LWCGC24, Lemma 2] of the greedy
  -- optimal policy `d` of the `p`-absorbing modification with the `k`-th reward of the grid, which
  -- is independent of the samples of `p`. Under the separation, at `p = (s, π̂ s)` one of these
  -- policies is `π̂` [LWCGC24, Lemma 4], so that the deviations of the empirical state kernel of
  -- `π̂` needed by [LWCGC24, Lemma 2] hold at every state.
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact (sub_nonpos.2 hδ1).trans measureReal_nonneg
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hu : 0 < 1 - (γ : ℝ) := sub_pos.2 hγ
  have hRabs (p : 𝓢 × 𝓐) : ∀ᵐ x ∂(M.R p), |x| ≤ C :=
    (hR p).mono fun x hx ↦ (abs_of_nonneg hx.1).trans_le hx.2
  have hRe (ω : ℕ → 𝓢 × 𝓐 → 𝓢) : ∀ p, ∀ᵐ x ∂((M.empirical N ω).R p), |x| ≤ C := by
    simpa using hRabs
  have hC : 0 ≤ C := (abs_nonneg _).trans (abs_meanReward_le hRabs (Classical.arbitrary _))
  -- for `C = 0` all the values vanish, and for `γ = 0` both values are the reward
  rcases hC.eq_or_lt with rfl | hC₀
  · refine le_trans ?_ (measureReal_mono (s₁ := Set.univ) (fun ω _ _ s ↦ ?_) (measure_ne_top _ _))
    · rw [probReal_univ]
      linarith
    · have h₁ := abs_value_le (π := Kernel.deterministic
        ((M.empirical N ω).greedy γ ((M.empirical N ω).optValue γ)) (measurable_of_finite _))
        hγ (hRe ω) s
      have h₂ := abs_value_le (π := Kernel.deterministic
        ((M.empirical N ω).greedy γ ((M.empirical N ω).optValue γ)) (measurable_of_finite _))
        hγ hRabs s
      rw [zero_div] at h₁ h₂
      rw [mul_zero, zero_mul]
      exact (abs_sub _ _).trans (by linarith)
  rcases eq_or_ne γ 0 with rfl | hγ₀
  · refine le_trans ?_ (measureReal_mono (s₁ := Set.univ) (fun ω _ _ s ↦ ?_) (measure_ne_top _ _))
    · rw [probReal_univ]
      linarith
    · rw [value_empirical_zero, sub_self, abs_zero]
      positivity
  have hγ₀' : 0 < γ := pos_iff_ne_zero.2 hγ₀
  -- the confidence level `L` and the number `m` of levels
  set S : ℝ := (Fintype.card 𝓢 : ℝ)
  set A : ℝ := (Fintype.card 𝓐 : ℝ)
  set lg : ℝ := log (exp 1 / (1 - γ))
  set L := log (4 * S * A * (K + 1) * lg / δ)
  set m := ⌈log (1 - (γ : ℝ))⁻¹⌉₊
  have hm' : (m : ℝ) + 1 ≤ 2 * lg := Real.natCeil_log_inv_one_sub_add_one_le γ.coe_nonneg hγ
  have hS : 1 ≤ S := Nat.one_le_cast.2 Fintype.card_pos
  have hA : 1 ≤ A := Nat.one_le_cast.2 Fintype.card_pos
  have hK₁ : (1 : ℝ) ≤ K + 1 := by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have hlg1 : 1 ≤ 2 * lg := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hL : 0 ≤ L := Real.log_nonneg (by
    rw [le_div_iff₀ hδ, one_mul]
    have h₁ : 1 ≤ S * A * (K + 1) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hS hA) hK₁
    nlinarith)
  -- the levels `V d l` of a deterministic policy `d` and their bounds `b l`
  set V : (𝓢 → 𝓐) → ℕ → 𝓢 → ℝ := fun d ↦
    M.valueLevel γ (Kernel.deterministic d (measurable_of_finite d)) with hV_def
  set b : ℕ → ℝ := fun l ↦ C / ((1 - γ) * (γ * √(1 - γ)) ^ l)
  have hbpos (l : ℕ) : 0 < b l :=
    div_pos hC₀ (mul_pos hu (pow_pos (mul_pos (NNReal.coe_pos.2 hγ₀') (Real.sqrt_pos.2 hu)) _))
  have hVb (d : 𝓢 → 𝓐) : ∀ l y, V d l y ∈ Set.Icc 0 (b l) := valueLevel_mem_Icc hγ₀' hγ hR _
  -- the grid of rewards on `[-B, B]`, with `B` bounding `Q̂* (s, a) - γ v̂* s`
  set B := (1 + γ) * C / (1 - γ)
  -- the levels of the greedy optimal policies of the absorbing modifications on the grid
  set W : (𝓢 × 𝓐) × Fin (K + 1) × Fin (m + 1) → MDP 𝓢 𝓐 ℝ → 𝓢 → ℝ := fun i M' ↦
    V ((M'.saAbsorbing i.1 (-B + 2 * B * (i.2.1 : ℕ) / K)).greedy γ
      ((M'.saAbsorbing i.1 (-B + 2 * B * (i.2.1 : ℕ) / K)).optValue γ)) i.2.2 with hW_def
  -- the bad events: Bernstein's inequality fails for one of them
  set bad : (𝓢 × 𝓐) × Fin (K + 1) × Fin (m + 1) → Set (ℕ → 𝓢 × 𝓐 → 𝓢) := fun i ↦ {ω |
    √(2 * Var[W i (M.empirical N ω); M.P i.1] * L / N) + (b i.2.2 - 0) * L / (3 * N) ≤
      |∫ s', W i (M.empirical N ω) s' ∂(M.P i.1) -
        ∫ s', W i (M.empirical N ω) s' ∂((M.empirical N ω).P i.1)|} with hbad_def
  have h_bad (i : (𝓢 × 𝓐) × Fin (K + 1) × Fin (m + 1)) :
      (streamMeasure M.P).real (bad i) ≤
        δ / Fintype.card ((𝓢 × 𝓐) × Fin (K + 1) × Fin (m + 1)) := by
    refine (measureReal_sqrt_variance_add_le_abs_integral_sub_integral_empirical_saAbsorbing_le M N
      (fun M'' ↦ V (M''.greedy γ (M''.optValue γ)) i.2.2) (hbpos i.2.2) i.1 _
      (fun ω s' ↦ hVb _ _ _) L).trans ?_
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    refine Real.mul_exp_neg_log_div_le two_pos (by positivity) hδ ?_
    calc 2 * (S * A * ((K + 1) * ((m : ℝ) + 1))) = 2 * S * A * (K + 1) * ((m : ℝ) + 1) := by ring
      _ ≤ 2 * S * A * (K + 1) * (2 * lg) := by gcongr
      _ = 4 * S * A * (K + 1) * lg := by ring
  -- outside the bad events, the deterministic part applies to `π̂`
  refine (one_sub_le_measureReal_compl_iUnion hδ.le h_bad).trans
    (measureReal_mono fun ω hω ↦ ?_)
  simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hω
  intro hsep x
  set g := (M.empirical N ω).greedy γ ((M.empirical N ω).optValue γ)
  refine abs_value_sub_value_le_of_abs_integral_stateKernel_sub_le (empirical_R M N ω) hγ₀' hγ hR
    _ (Nat.le_ceil _) hN₀ hL hN (fun l hl y ↦ ?_) x
  -- `g` is the greedy optimal policy of a modification at `(y, g y)` on the grid
  obtain ⟨k, hk⟩ := exists_greedy_optValue_saAbsorbing_eq (p := (y, g y)) hγ (hRe ω) hη hsep
    (abs_optQValue_sub_mul_optValue_le hγ (hRe ω) _) hK hKη
  have h := hω ((y, g y), k, ⟨l, Nat.lt_succ_of_le hl⟩)
  simp only [hbad_def, hW_def, Set.mem_ofPred_eq, not_le, sub_zero] at h
  rw [hk] at h
  rw [stateKernel_deterministic_apply, stateKernel_deterministic_apply, abs_sub_comm]
  exact h.le

/-- **Suboptimality of the separated plug-in policy** [LWCGC24, Lemma 5, second claim]. Under the
generative model of an MDP `M` with `S` states, `A` actions and rewards in `[0, C]`, let `γ < 1`,
`η > 0`, `K > 0` with `8 (1 + γ) C / (1 - γ) ≤ (1 - γ) η K`, `δ > 0` and
`L = log (8 S A (K + 1) log (e / (1 - γ)) / δ)`. If `18 L ≤ (1 - γ) N`, then with probability at
least `1 - δ`, whenever the optimal action values of the empirical MDP `M̂ = M.empirical N ω` are
separated by `η` at its greedy optimal policy `π̂` (`Q̂* (s, a) + η ≤ Q̂* (s, π̂ s)` for every
`a ≠ π̂ s`), the value of `π̂` in `M` satisfies `v* - v^π̂ ≤ 6 C √(2 L / (N (1 - γ) ^ 3))` at every
state.

[LWCGC24] proves the bound with the constant `12` in place of `6`, for rewards in `[0, 1]` and
under its condition on `N`. -/
theorem le_streamMeasure_forall_optValue_sub_value_le_of_separated {M : MDP 𝓢 𝓐 ℝ}
    {γ : ℝ≥0} (hγ : γ < 1) {C : ℝ} (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) {η : ℝ}
    (hη : 0 < η) {K : ℕ} (hK : 0 < K) (hKη : 8 * ((1 + γ) * C / (1 - γ)) ≤ (1 - γ) * η * K)
    (N : ℕ) [NeZero N] {δ : ℝ} (hδ : 0 < δ)
    (hN : 18 * log (8 * Fintype.card 𝓢 * Fintype.card 𝓐 * (K + 1) * log (exp 1 / (1 - γ)) / δ) ≤
      (1 - γ) * N) :
    1 - δ ≤ (streamMeasure M.P).real {ω |
      (∀ s a, a ≠ (M.empirical N ω).greedy γ ((M.empirical N ω).optValue γ) s →
        (M.empirical N ω).optQValue γ (s, a) + η ≤
          (M.empirical N ω).optQValue γ
            (s, (M.empirical N ω).greedy γ ((M.empirical N ω).optValue γ) s)) →
      ∀ s, M.optValue γ s - M.value γ (Kernel.deterministic
            ((M.empirical N ω).greedy γ ((M.empirical N ω).optValue γ))
            (measurable_of_finite _)) s ≤
        6 * C * √(2 * log (8 * Fintype.card 𝓢 * Fintype.card 𝓐 * (K + 1) *
          log (exp 1 / (1 - γ)) / δ) / (N * (1 - γ) ^ 3))} := by
  -- `v* - v^π̂ = (v^π* - v̂^π*) + (v̂^π* - v̂^π̂) + (v̂^π̂ - v^π̂)` for the greedy optimal policy
  -- `π*` of `M`: the first term is bounded by [LWCGC24, Lemma 1], since `π*` does not depend on
  -- the samples, the second one is nonpositive by optimality of `π̂` in `M̂`, and the third one is
  -- bounded by the first claim. Each bound holds with probability at least `1 - δ / 2`.
  set μ := streamMeasure M.P
  have hRabs (p : 𝓢 × 𝓐) : ∀ᵐ x ∂(M.R p), |x| ≤ C :=
    (hR p).mono fun x hx ↦ (abs_of_nonneg hx.1).trans_le hx.2
  have hRe (ω : ℕ → 𝓢 × 𝓐 → 𝓢) : ∀ p, ∀ᵐ x ∂((M.empirical N ω).R p), |x| ≤ C := by
    simpa using hRabs
  set S : ℝ := (Fintype.card 𝓢 : ℝ)
  set A : ℝ := (Fintype.card 𝓐 : ℝ)
  set lg : ℝ := log (exp 1 / (1 - γ)) with hlg_def
  set L := log (8 * S * A * (K + 1) * lg / δ)
  have hS : 1 ≤ S := Nat.one_le_cast.2 Fintype.card_pos
  have hA : 1 ≤ A := Nat.one_le_cast.2 Fintype.card_pos
  have hK₁ : (1 : ℝ) ≤ K + 1 := by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have hlg₀ : 0 < lg := by
    rw [hlg_def]
    refine Real.log_pos ((one_lt_div (sub_pos.2 (NNReal.coe_lt_one.2 hγ))).2 ?_)
    linarith [Real.add_one_le_exp (1 : ℝ), γ.coe_nonneg]
  have h8 : 4 * S * A * (K + 1) * lg / (δ / 2) = 8 * S * A * (K + 1) * lg / δ := by
    field_simp
    ring
  -- the level of [LWCGC24, Lemma 1] at `δ / 2` is at most `L`
  have hL₀ : log (4 * S * lg / (δ / 2)) ≤ L := by
    refine Real.log_le_log (by positivity) ?_
    rw [show 4 * S * lg / (δ / 2) = 8 * S * lg / δ by field_simp; ring]
    refine div_le_div_of_nonneg_right ?_ hδ.le
    have h₁ : 1 ≤ A * (K + 1) := one_le_mul_of_one_le_of_one_le hA hK₁
    calc 8 * S * lg = 8 * S * lg * 1 := (mul_one _).symm
      _ ≤ 8 * S * lg * (A * (K + 1)) := by gcongr
      _ = 8 * S * A * (K + 1) * lg := by ring
  -- the two events, each of probability at least `1 - δ / 2`
  set g : MDP 𝓢 𝓐 ℝ → 𝓢 → 𝓐 := fun M' ↦ M'.greedy γ (M'.optValue γ)
  have hg := measurable_greedy (M := M) (γ := γ) (measurable_optValue hγ hRabs)
  set E₁ := {ω | (∀ s a, a ≠ g (M.empirical N ω) s →
      (M.empirical N ω).optQValue γ (s, a) + η ≤ (M.empirical N ω).optQValue γ
        (s, g (M.empirical N ω) s)) →
    ∀ s, |(M.empirical N ω).value γ (Kernel.deterministic (g (M.empirical N ω))
        (measurable_of_finite _)) s -
      M.value γ (Kernel.deterministic (g (M.empirical N ω)) (measurable_of_finite _)) s| ≤
      3 * C * √(2 * L / (N * (1 - γ) ^ 3))}
  set E₂ := {ω | ∀ s, |(M.empirical N ω).value γ (Kernel.deterministic (g M) hg) s -
      M.value γ (Kernel.deterministic (g M) hg) s| ≤
      3 * C * √(2 * log (4 * S * lg / (δ / 2)) / (N * (1 - γ) ^ 3))}
  have h₁ : 1 - δ / 2 ≤ μ.real E₁ := by
    have h := le_streamMeasure_forall_abs_value_empirical_sub_value_le_of_separated hγ hR hη hK
      hKη N (half_pos hδ) (by rwa [h8])
    rwa [h8] at h
  have h₂ : 1 - δ / 2 ≤ μ.real E₂ :=
    le_streamMeasure_forall_abs_value_empirical_sub_value_le hγ hR _ N (half_pos hδ)
      ((mul_le_mul_of_nonneg_left hL₀ (by norm_num)).trans hN)
  have hE₂ : MeasurableSet E₂ :=
    measurableSet_setOfPred.2 (measurable_comp_empirical M N fun M' ↦ ∀ s,
      |M'.value γ (Kernel.deterministic (g M) hg) s - M.value γ (Kernel.deterministic (g M) hg) s| ≤
        3 * C * √(2 * log (4 * S * lg / (δ / 2)) / (N * (1 - γ) ^ 3)))
  have h_inter : 1 - δ ≤ μ.real (E₁ ∩ E₂) := by
    have h := one_sub_sub_le_measureReal_inter hE₂ h₁ h₂
    rwa [sub_sub, add_halves] at h
  refine h_inter.trans (measureReal_mono (fun ω ⟨hω₁, hω₂⟩ hsep s ↦ ?_) (measure_ne_top _ _))
  have hv₁ := abs_le.1 (hω₁ hsep s)
  have hv₂ := abs_le.1 (hω₂ s)
  -- `π*` is optimal in `M`, and `π̂` is optimal in `M̂`
  have hopt : M.value γ (Kernel.deterministic (g M) hg) = M.optValue γ :=
    value_greedy_optValue hγ hRabs hg
  have hle : (M.empirical N ω).value γ (Kernel.deterministic (g M) hg) s ≤
      (M.empirical N ω).value γ (Kernel.deterministic (g (M.empirical N ω))
        (measurable_of_finite _)) s := by
    exact (value_le_optValue hγ (hRe ω) s).trans_eq
      (congrFun (value_greedy_optValue hγ (hRe ω) (measurable_of_finite _)) s).symm
  have hC : 0 ≤ C := (abs_nonneg _).trans (abs_meanReward_le hRabs (s, Classical.arbitrary 𝓐))
  have hsq : 3 * C * √(2 * log (4 * S * lg / (δ / 2)) / (N * (1 - γ) ^ 3)) ≤
      3 * C * √(2 * L / (N * (1 - γ) ^ 3)) := by
    have : 0 ≤ (N : ℝ) * (1 - γ) ^ 3 := by
      have := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
      positivity
    gcongr
  rw [← hopt]
  linarith

end Generative

end Learning.MDP
