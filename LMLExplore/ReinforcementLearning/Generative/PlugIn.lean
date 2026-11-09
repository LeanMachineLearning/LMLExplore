/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.ReinforcementLearning.Generative.Decoupling

/-!
# Planning with a generative model: the plug-in policy is minimax optimal

Let `M` be an MDP with `S` states, `A` actions and rewards bounded by `C`, `1 / 2 ≤ γ < 1`, and
`M̂ = M.empirical N ω` the empirical MDP of `N` samples per state-action pair under the generative
model `Bandits.streamMeasure M.P`. Agarwal, Kakade and Yang [AKY20, Theorem 1] prove that planning
in `M̂` is minimax optimal: for `0 < ε ≤ (1 - γ)^(-1/2)` and
`N ≥ c γ log (c S A / ((1 - γ) δ)) / ((1 - γ) ^ 3 ε ^ 2)`, with probability at least `1 - δ`, every
policy `π` that is `ε₀`-optimal in `M̂` is `(C ε + 9 ε₀ / (1 - γ))`-optimal in `M`, both for its
action values and for its values. We prove this with the absolute constant `c = 10000`.

The total number `S A N` of samples is then of order
`S A log (S A / ((1 - γ) δ)) / ((1 - γ) ^ 3 ε ^ 2)`, which matches the lower bound of [AMK13] up
to logarithmic factors.

The proof has a deterministic part and a probabilistic part.
* The **deterministic part**, `Learning.MDP.optQValue_sub_qValue_le_of_le_sqrt_variance` and
  `Learning.MDP.optValue_sub_value_le_of_le_sqrt_variance` in
  `MarkovDecisionProcess/Simulation.lean`, is [AKY20, Lemmas 2 and 10]: if the optimal value `v̂*`
  of `M̂` and the value `v̂^π*` in `M̂` of an optimal policy `π*` of `M` satisfy the Bernstein-type
  bounds `|∫ v dP p - ∫ v dP̂ p| ≤ a √(Var_{P p}(v)) + b`, then the near-optimal policies of `M̂`
  are near-optimal in `M`. The variances are taken under the true transitions `P`, and the
  total-variance lemma in `M` controls them.
* The **probabilistic part** is [AKY20, Lemma 9], both claims
  (`ReinforcementLearning/Generative/Decoupling.lean`): with probability at least `1 - δ / 2`
  each, these Bernstein-type bounds hold with `a = √(2 L / N)` and
  `L = log (24 S A / ((1 - γ) ^ 2 δ))`.
  The policy `π*` is the greedy policy of the optimal value of `M`, which does not depend on the
  samples.

[AKY20] states the hypothesis on `π` as `‖Q̂^π - Q̂*‖ ≤ ε₀`, but its proof of Lemma 10 uses
`‖v̂^π - v̂*‖ ≤ ε₀`, which this hypothesis does not imply: for `γ = 0`, every policy has
`Q̂^π = Q̂* = r`. We state the hypothesis that the proof uses, `|v̂^π - v̂*| ≤ ε₀`; it implies
`|Q̂^π - Q̂*| ≤ γ ε₀`. For `ε₀ = 0`, it holds for every optimal policy of `M̂`, such as its greedy
policy.

## Main statements

* `Learning.MDP.le_streamMeasure_forall_optQValue_sub_le_qValue`: the action values of the
  near-optimal policies of the empirical MDP [AKY20, Theorem 1].
* `Learning.MDP.le_streamMeasure_forall_optValue_sub_le_value`: the values of the near-optimal
  policies of the empirical MDP [AKY20, Theorem 1].

## References

* [A. Agarwal, S. Kakade and L. F. Yang, *Model-based reinforcement learning with a generative
  model is minimax optimal*, COLT 2020][AKY20], Theorem 1 and §4
* [M. G. Azar, R. Munos and H. J. Kappen, *Minimax PAC bounds on the sample complexity of
  reinforcement learning with a generative model*, Machine Learning 91, 2013][AMK13]
-/

public section

open MeasureTheory ProbabilityTheory LMLExplore Learning Bandits
open Real (log)
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  [MeasurableSingletonClass 𝓢] [MeasurableSingletonClass 𝓐]

/-- The numerical step of [AKY20, Theorem 1]: if `10000 γ L ≤ 2 (1 - γ) ^ 3 ε ^ 2 N`, the error of
`Learning.MDP.optValue_sub_value_le_of_le_sqrt_variance` with `a = √(2 L / N)` and
`b = 4 γ C a + 5 C L / ((1 - γ) N)` is at most `C ε + 9 ε₀ / (1 - γ)`, and `γ a / (1 - γ) < 1`. -/
private lemma plugIn_bound_le {γ C ε ε₀ L N : ℝ} (hγ₀ : 1 / 2 ≤ γ) (hγ : γ < 1) (hC : 0 ≤ C)
    (hε : 0 < ε) (hθε : (1 - γ) * ε ^ 2 ≤ 1) (hε₀ : 0 ≤ ε₀) (hL : 0 ≤ L) (hN : 0 < N)
    (hLN : 10000 * γ * L ≤ 2 * (1 - γ) ^ 3 * ε ^ 2 * N) :
    γ * √(2 * L / N) / (1 - γ) < 1 ∧
    (2 * γ * (√(2 * L / N) * C * √(2 / (1 - γ) ^ 3) +
        (4 * γ * C * √(2 * L / N) + 5 * C * L / ((1 - γ) * N)) / (1 - γ)) +
        γ * (2 + √(2 * L / N)) * ε₀ / (1 - γ)) / (1 - γ * √(2 * L / N) / (1 - γ)) + ε₀ ≤
      C * ε + 9 * ε₀ / (1 - γ) := by
  set θ := 1 - γ with hθ
  have hθ₀ : 0 < θ := by linarith
  have hθ₁ : θ ≤ 1 / 2 := by linarith
  have hγ₀' : 0 < γ := by linarith
  set q := L / N with hq_def
  have hq₀ : 0 ≤ q := div_nonneg hL hN.le
  have hq : 10000 * γ * q ≤ 2 * θ ^ 3 * ε ^ 2 := by
    rw [hq_def, ← mul_div_assoc, div_le_iff₀ hN]
    exact hLN
  set a := √(2 * L / N) with ha_def
  have ha₀ : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 2 * q := by rw [ha_def, Real.sq_sqrt (by positivity), mul_div_assoc]
  -- `θ ε ≤ 1` and `θ ε ^ 2 ≤ ε`
  have hθε₁ : θ * ε ≤ 1 := by
    refine (pow_le_pow_iff_left₀ (by positivity) zero_le_one two_ne_zero).1 ?_
    calc (θ * ε) ^ 2 = θ * (θ * ε ^ 2) := by ring
      _ ≤ 1 * 1 := mul_le_mul (by linarith) hθε (by positivity) zero_le_one
      _ = 1 ^ 2 := by norm_num
  have hθε₂ : θ * ε ^ 2 ≤ ε := by
    calc θ * ε ^ 2 = ε * (θ * ε) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hθε₁ hε.le
      _ = ε := mul_one ε
  have hθε₃ : θ * ε ^ 2 ≤ ε ^ 2 := mul_le_of_le_one_left (sq_nonneg _) (by linarith)
  -- `2 γ ^ 2 q ≤ 4 θ ^ 3 ε ^ 2 / 10000` and `q ≤ θ ^ 3 ε ^ 2 / 2500`
  have hγq : 2 * γ ^ 2 * q ≤ 4 * θ ^ 3 * ε ^ 2 / 10000 := by
    have h := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 2 * γ)
    have h' : γ * (θ ^ 3 * ε ^ 2) ≤ θ ^ 3 * ε ^ 2 :=
      mul_le_of_le_one_left (by positivity) hγ.le
    linarith
  have hq' : q ≤ θ ^ 3 * ε ^ 2 / 2500 := by
    have h : 5000 * q ≤ 10000 * γ * q := mul_le_mul_of_nonneg_right (by linarith) hq₀
    linarith
  -- `α = γ a / θ ≤ ε / 20` and `α ≤ 1 / 20`
  set α := γ * a / θ with hα_def
  have hα₀ : 0 ≤ α := by positivity
  have hα2 : α ^ 2 = 2 * γ ^ 2 * q / θ ^ 2 := by
    rw [hα_def, div_pow, mul_pow, ha2]
    ring
  have hα2' : α ^ 2 ≤ 4 * θ * ε ^ 2 / 10000 := by
    rw [hα2, div_le_iff₀ (by positivity)]
    calc 2 * γ ^ 2 * q ≤ 4 * θ ^ 3 * ε ^ 2 / 10000 := hγq
      _ = 4 * θ * ε ^ 2 / 10000 * θ ^ 2 := by ring
  have hαε : α ≤ ε / 20 := by
    refine (pow_le_pow_iff_left₀ hα₀ (by positivity) two_ne_zero).1 (hα2'.trans ?_)
    rw [show (ε / 20) ^ 2 = ε ^ 2 / 400 by ring]
    linarith [sq_nonneg ε]
  have hα1 : α ≤ 1 / 20 := by
    refine (pow_le_pow_iff_left₀ hα₀ (by positivity) two_ne_zero).1 (hα2'.trans ?_)
    norm_num
    linarith
  -- `t = γ a √(2 / θ ^ 3) ≤ ε / 10`
  set t := γ * a * √(2 / θ ^ 3) with ht_def
  have ht₀ : 0 ≤ t := by positivity
  have ht : t ≤ ε / 10 := by
    refine (pow_le_pow_iff_left₀ ht₀ (by positivity) two_ne_zero).1 ?_
    have ht2 : t ^ 2 = 2 * (2 * γ ^ 2 * q) / θ ^ 3 := by
      rw [ht_def, mul_pow, mul_pow, ha2, Real.sq_sqrt (by positivity)]
      ring
    rw [ht2, div_le_iff₀ (by positivity), div_pow]
    linarith
  -- `z = q / θ ^ 2 ≤ ε / 2500`
  set z := q / θ ^ 2 with hz_def
  have hz : z ≤ ε / 2500 := by
    rw [hz_def, div_le_iff₀ (by positivity)]
    have h : θ ^ 2 * (θ * ε ^ 2) ≤ θ ^ 2 * ε := mul_le_mul_of_nonneg_left hθε₂ (by positivity)
    linarith
  -- the error is `(2 C t + 8 C γ α + 10 C γ z + 2 γ ε₀ / θ + α ε₀) / (1 - α) + ε₀`
  have hE : 2 * γ * (a * C * √(2 / θ ^ 3) + (4 * γ * C * a + 5 * C * L / (θ * N)) / θ) +
      γ * (2 + a) * ε₀ / θ = 2 * C * t + 8 * C * γ * α + 10 * C * γ * z + 2 * γ * (ε₀ / θ) +
        α * ε₀ := by
    simp only [ht_def, hα_def, hz_def, hq_def]
    field_simp
    ring
  have hw : ε₀ ≤ ε₀ / θ := le_div_self hε₀ hθ₀ (by linarith)
  refine ⟨hα1.trans_lt (by norm_num), ?_⟩
  rw [hE, show 9 * ε₀ / θ = 9 * (ε₀ / θ) by ring]
  have hD : 0 < 1 - α := by linarith
  have h₁ : C * t ≤ C * (ε / 10) := mul_le_mul_of_nonneg_left ht hC
  have hz₀ : 0 ≤ z := by positivity
  have h₂ : C * γ * α ≤ C * (ε / 20) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left hα₀ hγ.le).trans hαε) hC
  have h₃ : C * γ * z ≤ C * (ε / 2500) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left hz₀ hγ.le).trans hz) hC
  have h₄ : α * (C * ε) ≤ 1 / 20 * (C * ε) := mul_le_mul_of_nonneg_right hα1 (by positivity)
  have h₅ : α * (ε₀ / θ) ≤ 1 / 20 * (ε₀ / θ) := mul_le_mul_of_nonneg_right hα1 (by positivity)
  have h₆ : α * ε₀ ≤ α * (ε₀ / θ) := mul_le_mul_of_nonneg_left hw hα₀
  have h₇ : γ * (ε₀ / θ) ≤ ε₀ / θ := mul_le_of_le_one_left (by positivity) hγ.le
  have hCε : 0 ≤ C * ε := by positivity
  have hw₀ : 0 ≤ ε₀ / θ := by positivity
  have h_main : 2 * C * t + 8 * C * γ * α + 10 * C * γ * z + 2 * γ * (ε₀ / θ) + α * ε₀ ≤
      (1 - α) * (C * ε + 8 * (ε₀ / θ)) := by
    linarith
  calc (2 * C * t + 8 * C * γ * α + 10 * C * γ * z + 2 * γ * (ε₀ / θ) + α * ε₀) / (1 - α) + ε₀
      ≤ (C * ε + 8 * (ε₀ / θ)) + ε₀ / θ := by
        gcongr
        rw [div_le_iff₀ hD]
        linarith
    _ = C * ε + 9 * (ε₀ / θ) := by ring

/-- The two Bernstein-type bounds of [AKY20, Lemma 9] at the level `δ / 2`, for the optimal value
`v̂*` of `M̂` and for the value `v̂^π*` in `M̂` of the greedy optimal policy `π*` of `M`, give
both claims of [AKY20, Theorem 1] through the deterministic
`Learning.MDP.optQValue_sub_qValue_le_of_le_sqrt_variance` and
`Learning.MDP.optValue_sub_value_le_of_le_sqrt_variance`. -/
private theorem le_streamMeasure_forall_optQValue_sub_le_qValue_and_optValue_sub_le_value
    [Fintype 𝓢] [Fintype 𝓐] [Nonempty 𝓢] [Nonempty 𝓐] {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0}
    (hγ₀ : 1 / 2 ≤ γ) (hγ : γ < 1) {C : ℝ} (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {ε : ℝ}
    (hε : 0 < ε) (hεγ : ε ≤ 1 / √(1 - γ)) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) [NeZero N]
    (hN : 10000 * γ * log (10000 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) * δ)) /
      ((1 - γ) ^ 3 * ε ^ 2) ≤ N) :
    1 - δ ≤ (streamMeasure M.P).real {ω | ∀ (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] (ε₀ : ℝ),
      (∀ s, |(M.empirical N ω).value γ π s - (M.empirical N ω).optValue γ s| ≤ ε₀) →
      (∀ p, M.optQValue γ p - C * ε - 9 * ε₀ / (1 - γ) ≤ M.qValue γ π p) ∧
      ∀ s, M.optValue γ s - C * ε - 9 * ε₀ / (1 - γ) ≤ M.value γ π s} := by
  set μ := streamMeasure M.P
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact (sub_nonpos.2 hδ1).trans measureReal_nonneg
  have hγ₀' : (1 / 2 : ℝ) ≤ γ := by exact_mod_cast hγ₀
  have hγ₁ : (γ : ℝ) < 1 := NNReal.coe_lt_one.2 hγ
  have hθ : 0 < 1 - (γ : ℝ) := sub_pos.2 hγ₁
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hS : (1 : ℝ) ≤ Fintype.card 𝓢 := Nat.one_le_cast.2 Fintype.card_pos
  have hA : (1 : ℝ) ≤ Fintype.card 𝓐 := Nat.one_le_cast.2 Fintype.card_pos
  have hSA : (1 : ℝ) ≤ Fintype.card 𝓢 * Fintype.card 𝓐 := one_le_mul_of_one_le_of_one_le hS hA
  have hC : 0 ≤ C := (abs_nonneg _).trans (abs_meanReward_le hR (Classical.arbitrary _))
  have hR' (ω : ℕ → 𝓢 × 𝓐 → 𝓢) : ∀ p, ∀ᵐ x ∂((M.empirical N ω).R p), |x| ≤ C := by
    simpa using hR
  -- `(1 - γ) ε ^ 2 ≤ 1`
  have hθε : (1 - γ) * ε ^ 2 ≤ 1 := by
    have h : ε * √(1 - γ) ≤ 1 := by
      rwa [le_div_iff₀ (Real.sqrt_pos.2 hθ)] at hεγ
    have h' := pow_le_pow_left₀ (by positivity) h 2
    rwa [mul_pow, Real.sq_sqrt hθ.le, one_pow, mul_comm] at h'
  -- the level `L` of the Bernstein bounds at `δ / 2` is at most twice the level of `hN`
  set L := log (12 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) ^ 2 * (δ / 2)))
  set ℓ := log (10000 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) * δ))
  have hθ₂ : (1 - (γ : ℝ)) ^ 2 * (δ / 2) ≤ 1 := by
    have : (1 - (γ : ℝ)) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hL₀ : 0 ≤ L := Real.log_nonneg ((one_le_div (by positivity)).2 (by nlinarith))
  have hLℓ : L ≤ 2 * ℓ := by
    have h := Real.log_pow (10000 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) * δ)) 2
    push_cast at h
    rw [← h]
    refine Real.log_le_log (by positivity) ?_
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have key : 12 * δ ≤ 50000000 * (Fintype.card 𝓢 * Fintype.card 𝓐) := by nlinarith
    have h' := mul_le_mul_of_nonneg_left key
      (by positivity : (0 : ℝ) ≤ Fintype.card 𝓢 * Fintype.card 𝓐 * (1 - γ) ^ 2 * δ)
    nlinarith
  have hLN : 10000 * γ * L ≤ 2 * (1 - γ) ^ 3 * ε ^ 2 * N := by
    have h := (div_le_iff₀ (by positivity)).1 hN
    have h' := mul_le_mul_of_nonneg_left hLℓ (by positivity : (0 : ℝ) ≤ 10000 * γ)
    nlinarith
  -- the greedy optimal policy `π*` of `M`, which does not depend on the samples
  have hg := measurable_greedy (M := M) (γ := γ) (measurable_optValue hγ hR)
  have hπ' := value_greedy_optValue hγ hR hg
  -- the Bernstein-type bounds of [AKY20, Lemma 9] at the level `δ / 2`
  have h₁ :=
    le_streamMeasure_forall_abs_integral_optValue_empirical_sub_integral_optValue_empirical_le
      hγ hR N (half_pos hδ)
  have h₂ := le_streamMeasure_forall_abs_integral_value_empirical_sub_integral_value_empirical_le
    hγ hR (Kernel.deterministic _ hg) N (half_pos hδ)
  set E₁ : Set (ℕ → 𝓢 × 𝓐 → 𝓢) := {ω | ∀ p,
    |∫ s, (M.empirical N ω).optValue γ s ∂(M.P p) -
        ∫ s, (M.empirical N ω).optValue γ s ∂((M.empirical N ω).P p)| ≤
      √(2 * L / N) * √Var[(M.empirical N ω).optValue γ; M.P p] + 4 * γ * C * √(2 * L / N) +
        5 * C * L / ((1 - γ) * N)}
  have h_meas : MeasurableSet E₁ :=
    measurableSet_setOfPred.2 (measurable_comp_empirical M N fun M' ↦ ∀ p,
      |∫ s, M'.optValue γ s ∂(M.P p) - ∫ s, M'.optValue γ s ∂(M'.P p)| ≤
        √(2 * L / N) * √Var[M'.optValue γ; M.P p] + 4 * γ * C * √(2 * L / N) +
          5 * C * L / ((1 - γ) * N))
  set E₂ : Set (ℕ → 𝓢 × 𝓐 → 𝓢) := {ω | ∀ p,
    |∫ s, (M.empirical N ω).value γ (Kernel.deterministic _ hg) s ∂(M.P p) -
        ∫ s, (M.empirical N ω).value γ (Kernel.deterministic _ hg) s ∂((M.empirical N ω).P p)| ≤
      √(2 * L / N) * √Var[(M.empirical N ω).value γ (Kernel.deterministic _ hg); M.P p] +
        4 * γ * C * √(2 * L / N) + 5 * C * L / ((1 - γ) * N)}
  have h_inter := measureReal_union_add_inter (μ := μ) (s := E₂) h_meas
  have h_le : μ.real (E₂ ∪ E₁) ≤ 1 := measureReal_le_one
  refine le_trans (by linarith) (measureReal_mono (s₁ := E₂ ∩ E₁)
    (fun ω ⟨hω₂, hω₁⟩ π _ ε₀ hπ ↦ ?_) (measure_ne_top _ _))
  have hε₀ : 0 ≤ ε₀ := (abs_nonneg _).trans (hπ (Classical.arbitrary _))
  obtain ⟨hα, hbound⟩ := plugIn_bound_le hγ₀' hγ₁ hC hε hθε hε₀ hL₀ hN₀ hLN
  have hr : meanReward (M.empirical N ω).R = meanReward M.R := by rw [empirical_R]
  have hε' (p : 𝓢 × 𝓐) := (hω₂ p).trans_eq (add_assoc _ _ _)
  have hε (p : 𝓢 × 𝓐) := (hω₁ p).trans_eq (add_assoc _ _ _)
  have hγε₀ : (γ : ℝ) * ε₀ ≤ ε₀ := mul_le_of_le_one_left hε₀ hγ₁.le
  refine ⟨fun p ↦ ?_, fun s ↦ ?_⟩
  · have h := optQValue_sub_qValue_le_of_le_sqrt_variance hγ hR (hR' ω) hr (Real.sqrt_nonneg _)
      hα hπ' hε' hε hπ p
    linarith
  · have h := optValue_sub_value_le_of_le_sqrt_variance hγ hR (hR' ω) hr (Real.sqrt_nonneg _)
      hα hπ' hε' hε hπ s
    linarith

variable [Fintype 𝓢] [Fintype 𝓐] [Nonempty 𝓢] [Nonempty 𝓐]

/-- **The plug-in policy is minimax optimal**, for action values [AKY20, Theorem 1]. Under the
generative model of an MDP `M` with `S` states, `A` actions and rewards bounded by `C`, for
`1 / 2 ≤ γ < 1`, `0 < ε ≤ (1 - γ)^(-1/2)`, `δ > 0` and
`N ≥ 10000 γ log (10000 S A / ((1 - γ) δ)) / ((1 - γ) ^ 3 ε ^ 2)`, with probability at least
`1 - δ`, every stationary policy `π` whose value in the empirical MDP `M̂ = M.empirical N ω` is
within `ε₀` of the optimal value of `M̂` has action values `Q^π ≥ Q* - C ε - 9 ε₀ / (1 - γ)` in `M`.

[AKY20] states the hypothesis on `π` as `‖Q̂^π - Q̂*‖ ≤ ε₀`; its proof uses `‖v̂^π - v̂*‖ ≤ ε₀`,
which is the hypothesis stated here. -/
theorem le_streamMeasure_forall_optQValue_sub_le_qValue {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0}
    (hγ₀ : 1 / 2 ≤ γ) (hγ : γ < 1) {C : ℝ} (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {ε : ℝ}
    (hε : 0 < ε) (hεγ : ε ≤ 1 / √(1 - γ)) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) [NeZero N]
    (hN : 10000 * γ * log (10000 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) * δ)) /
      ((1 - γ) ^ 3 * ε ^ 2) ≤ N) :
    1 - δ ≤ (streamMeasure M.P).real {ω | ∀ (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] (ε₀ : ℝ),
      (∀ s, |(M.empirical N ω).value γ π s - (M.empirical N ω).optValue γ s| ≤ ε₀) →
      ∀ p, M.optQValue γ p - C * ε - 9 * ε₀ / (1 - γ) ≤ M.qValue γ π p} :=
  (le_streamMeasure_forall_optQValue_sub_le_qValue_and_optValue_sub_le_value hγ₀ hγ hR hε hεγ
    hδ N hN).trans (measureReal_mono (fun _ h π _ ε₀ hπ ↦ (h π ε₀ hπ).1) (measure_ne_top _ _))

/-- **The plug-in policy is minimax optimal**, for values [AKY20, Theorem 1]. Under the
generative model of an MDP `M` with `S` states, `A` actions and rewards bounded by `C`, for
`1 / 2 ≤ γ < 1`, `0 < ε ≤ (1 - γ)^(-1/2)`, `δ > 0` and
`N ≥ 10000 γ log (10000 S A / ((1 - γ) δ)) / ((1 - γ) ^ 3 ε ^ 2)`, with probability at least
`1 - δ`, every stationary policy `π` whose value in the empirical MDP `M̂ = M.empirical N ω` is
within `ε₀` of the optimal value of `M̂` has values `v^π ≥ v* - C ε - 9 ε₀ / (1 - γ)` in `M`. -/
theorem le_streamMeasure_forall_optValue_sub_le_value {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0}
    (hγ₀ : 1 / 2 ≤ γ) (hγ : γ < 1) {C : ℝ} (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {ε : ℝ}
    (hε : 0 < ε) (hεγ : ε ≤ 1 / √(1 - γ)) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) [NeZero N]
    (hN : 10000 * γ * log (10000 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) * δ)) /
      ((1 - γ) ^ 3 * ε ^ 2) ≤ N) :
    1 - δ ≤ (streamMeasure M.P).real {ω | ∀ (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] (ε₀ : ℝ),
      (∀ s, |(M.empirical N ω).value γ π s - (M.empirical N ω).optValue γ s| ≤ ε₀) →
      ∀ s, M.optValue γ s - C * ε - 9 * ε₀ / (1 - γ) ≤ M.value γ π s} :=
  (le_streamMeasure_forall_optQValue_sub_le_qValue_and_optValue_sub_le_value hγ₀ hγ hR hε hεγ
    hδ N hN).trans (measureReal_mono (fun _ h π _ ε₀ hπ ↦ (h π ε₀ hπ).2) (measure_ne_top _ _))

end Learning.MDP
