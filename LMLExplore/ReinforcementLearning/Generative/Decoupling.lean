/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Absorbing.Basic
public import LMLExplore.ReinforcementLearning.Generative.Basic
import LMLExplore.Probability.Moments.Variance
import LMLExplore.SequentialLearning.SumRewards
import LMLExplore.Topology.UnitInterval

/-!
# Planning with a generative model: decoupling through absorbing modifications

Let `M` be an MDP with `S` states, `A` actions and rewards bounded by `C`, `γ < 1`, and
`M̂ = M.empirical N ω` the empirical MDP of `N` samples per state-action pair under the generative
model `Bandits.streamMeasure M.P`. The analysis of the plug-in policy of [AKY20] needs Bernstein
bounds on the one-step prediction errors `∫ v̂ dP (s, a) - ∫ v̂ dP̂ (s, a)` of the values `v̂` of
`M̂`: its optimal value, or the value of a fixed policy. Such a value is computed from all the
samples, including those of `(s, a)`, so that Bernstein's inequality does not apply directly.

Agarwal, Kakade and Yang decouple the two through the `s`-absorbing modifications of `M̂`
(`MarkovDecisionProcess/Absorbing/Basic.lean`), in which every action leads back to `s` with reward
`(1 - γ) u`:
* the modification is computed from the samples of the pairs at the other states, so that every
  function of it is independent of the samples of `(s, a)`
  (`Learning.MDP.indepFun_comp_absorbing_empirical`), and Bernstein's inequality applies to its
  values for each fixed `u` [AKY20, Lemma 6];
* its values are within `|v̂ s - u|` of `v̂` [AKY20, Lemmas 7 and 8], so that a finite net of values
  `u` around `v s` approximates `v̂`, and a union bound over the net transfers the Bernstein bound
  to `v̂` [AKY20, Proposition 1].

The net at `s` has `⌈(1 - γ)⁻²⌉ + 1` evenly spaced points on the interval of radius
`γ C √(2 log (4 S A / δ) / N) / (1 - γ) ^ 2` around the value `v s` of `M`, which contains `v̂ s`
by the crude value bounds of `ReinforcementLearning/Generative/Basic.lean`, clipped to the range
`[-C / (1 - γ), C / (1 - γ)]` of the values. This gives [AKY20, Lemma 9]: for `δ > 0`, with
probability at least `1 - δ`, every pair `p` satisfies

`|∫ v̂ dP p - ∫ v̂ dP̂ p| ≤ √(2 L / N) √(Var_{P p}(v̂)) + 4 γ C √(2 L / N) + 5 C L / ((1 - γ) N)`,

with `L = log (12 S A / ((1 - γ) ^ 2 δ))`, both for the optimal value `v̂ = v̂*` of `M̂` and for the
value `v̂ = v̂^π` in `M̂` of a fixed stationary policy `π`. The variance is that of `v̂` under the
true transitions `P p`, as needed for the total-variance argument of [AKY20, Lemma 10].

The approximation step bounds the prediction error of `v̂ - v̂_{s,u}` by twice the sup norm of this
difference, where [AKY20] uses its sup norm; this only changes the absolute constants.

## Main statements

* `Learning.MDP.indepFun_comp_absorbing_empirical`: every function of the `s`-absorbing
  modification of the empirical MDP is independent of the samples of `(s, a)`.
* `Learning.MDP.measureReal_sqrt_variance_add_le_abs_integral_sub_integral_empirical_absorbing_le`:
  Bernstein's inequality for the values of the absorbing modifications of the empirical MDP
  [AKY20, Lemma 6].
* `le_streamMeasure_forall_abs_integral_optValue_empirical_sub_integral_optValue_empirical_le` and
  `le_streamMeasure_forall_abs_integral_value_empirical_sub_integral_value_empirical_le` (in
  `Learning.MDP`): the Bernstein-type bounds for the optimal value of the empirical MDP and for
  the value of a fixed policy in it [AKY20, Lemma 9].

## References

* [A. Agarwal, S. Kakade and L. F. Yang, *Model-based reinforcement learning with a generative
  model is minimax optimal*, COLT 2020][AKY20], §4.2
-/

public section

open MeasureTheory ProbabilityTheory LMLExplore Learning Bandits
open Real (log exp)
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 𝓡 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓡 : MeasurableSpace 𝓡} [MeasurableSingletonClass 𝓢] [MeasurableSingletonClass 𝓐]

section Decoupling

variable [Finite 𝓢] [Finite 𝓐]

/-- **Decoupling** [AKY20, §4.2]. Under the generative model of `M`, every function of the
`s`-absorbing modification of the empirical MDP is independent of the samples of the pair
`(s, a)`: the modification is computed from the samples of the pairs at the other states. -/
theorem indepFun_comp_absorbing_empirical (M : MDP 𝓢 𝓐 𝓡) (N : ℕ) [NeZero N] {β : Type*}
    [MeasurableSpace β] (F : MDP 𝓢 𝓐 𝓡 → β) (s : 𝓢) (c : 𝓡) (a : 𝓐) :
    IndepFun (fun ω ↦ F ((M.empirical N ω).absorbing s c)) (fun ω i ↦ ω i (s, a))
      (streamMeasure M.P) := by
  classical
  -- the sample sequences of the pairs at the other states are independent of those of `(s, a)`
  have h := (iIndepFun_arm_streamMeasure M.P).indepFun_set {p | p.1 ≠ s} {(s, a)}
    (Set.disjoint_singleton_right.2 fun h ↦ h rfl) fun p ↦ by fun_prop
  -- the array with the samples of the pairs at the other states, and `s` at the pairs at `s`
  let ext : ({p : 𝓢 × 𝓐 | p.1 ≠ s} → ℕ → 𝓢) → ℕ → 𝓢 × 𝓐 → 𝓢 :=
    fun x i p ↦ if hp : p.1 ≠ s then x ⟨p, hp⟩ i else s
  have h_ext : Measurable ext := by
    refine Measurable.of_eval fun i ↦ Measurable.of_eval fun p ↦ ?_
    by_cases hp : p.1 ≠ s
    · have h₁ : (fun x ↦ ext x i p) = fun x ↦ x ⟨p, hp⟩ i := funext fun x ↦ by simp [ext, hp]
      rw [h₁]
      fun_prop
    · simp [ext, not_not.1 hp]
  have h_eq : (fun ω ↦ F ((M.empirical N ω).absorbing s c)) =
      (fun x ↦ F ((M.empirical N (ext x)).absorbing s c)) ∘ fun ω p i ↦ ω i p := by
    ext ω
    simp only [Function.comp_apply]
    congr 1
    refine absorbing_congr c (fun p hp ↦ ?_) fun p _ ↦ by simp
    simp only [empirical_P]
    exact empiricalKernel_apply_congr fun i _ ↦ by simp [ext, hp]
  rw [h_eq]
  exact h.comp ((measurable_comp_empirical M N fun M' ↦ F (M'.absorbing s c)).comp h_ext)
    (measurable_pi_apply ⟨(s, a), Set.mem_singleton _⟩)

/-- **Bernstein's inequality for the absorbing modifications of the empirical MDP** [AKY20,
Lemma 6]. Under the generative model of `M`, let `G M'` be a function on the states computed from
an MDP `M'` (for instance its optimal value), with values in `[l, u]`, `l < u`, at the
`s`-absorbing modifications of the empirical MDPs with reward `c`. For `N ≠ 0`, every action `a`
and every `x`, the one-step prediction error `|∫ v dP (s, a) - ∫ v dP̂ (s, a)|` of
`v = G ((M.empirical N ω).absorbing s c)` is at least
`√(2 Var_{P (s, a)}(v) x / N) + (u - l) x / (3 N)` with probability at most `2 exp (-x)`. -/
theorem measureReal_sqrt_variance_add_le_abs_integral_sub_integral_empirical_absorbing_le
    (M : MDP 𝓢 𝓐 𝓡) (N : ℕ) [NeZero N] (G : MDP 𝓢 𝓐 𝓡 → 𝓢 → ℝ) {l u : ℝ} (hlu : l < u) (s : 𝓢)
    (c : 𝓡) (hG : ∀ ω s', G ((M.empirical N ω).absorbing s c) s' ∈ Set.Icc l u) (a : 𝓐)
    (x : ℝ) :
    (streamMeasure M.P).real {ω |
      √(2 * Var[G ((M.empirical N ω).absorbing s c); M.P (s, a)] * x / N) +
        (u - l) * x / (3 * N) ≤
      |∫ s', G ((M.empirical N ω).absorbing s c) s' ∂(M.P (s, a)) -
        ∫ s', G ((M.empirical N ω).absorbing s c) s' ∂((M.empirical N ω).P (s, a))|} ≤
      2 * exp (-x) := by
  simpa only [empirical_P] using
    measureReal_sqrt_variance_add_le_abs_integral_sub_integral_empiricalKernel_le_of_indepFun M.P
      (measurable_comp_empirical M N fun M' ↦ G (M'.absorbing s c))
      (indepFun_comp_absorbing_empirical M N G s c a) hlu hG N x

end Decoupling

/-- The confidence count of [AKY20, Lemma 9]: for `θ ^ 2 (K + 1) ≤ 3`, the probability
`2 exp (-L)` of each bad event of the Bernstein inequality at the level
`L = log (12 S A / (θ ^ 2 δ))` is at most `δ / 2` divided by the number `S A (K + 1)` of pairs and
points of the net. -/
private lemma two_mul_exp_neg_log_le {S A K θ δ : ℝ} (hS : 0 < S) (hA : 0 < A) (hK : 0 ≤ K)
    (hθ : 0 < θ) (hδ : 0 < δ) (hθK : θ ^ 2 * (K + 1) ≤ 3) :
    2 * Real.exp (-log (12 * S * A / (θ ^ 2 * δ))) ≤ δ / 2 / (S * (A * (K + 1))) := by
  rw [Real.exp_neg, Real.exp_log (by positivity), inv_div, div_div, le_div_iff₀ (by positivity)]
  calc 2 * (θ ^ 2 * δ / (12 * S * A)) * (2 * (S * (A * (K + 1)))) = θ ^ 2 * (K + 1) * δ / 3 := by
        field_simp
        ring
    _ ≤ 3 * δ / 3 := by gcongr
    _ = δ := by ring

/-- The numerical step of [AKY20, Lemma 9]: with `r = √(2 L / N)` and `Λ ≤ r`, the error terms
`(2 + r) 2 γ C Λ + 2 C L / (3 (1 - γ) N)` of the approximation by the net and of Bernstein's
inequality are at most `4 γ C r + 5 C L / ((1 - γ) N)`. -/
private lemma net_bound_le {γ C L N r Λ σ : ℝ} (hγ₀ : 0 ≤ γ) (hγ : γ < 1) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hN : 0 < N) (hr : 0 ≤ r) (hΛ : Λ ≤ r) (hr2 : r ^ 2 = 2 * L / N) :
    r * σ + (2 + r) * (2 * γ * C * Λ) + (C / (1 - γ) - -(C / (1 - γ))) * L / (3 * N) ≤
      r * σ + 4 * γ * C * r + 5 * C * L / ((1 - γ) * N) := by
  have hθ : 0 < 1 - γ := sub_pos.2 hγ
  -- with `D = C L / ((1 - γ) N)`, the error terms are `4 γ C r + 4 γ (1 - γ) D + 2 D / 3`
  set D := C * L / ((1 - γ) * N)
  have hD₀ : 0 ≤ D := by positivity
  have hγD : γ * (1 - γ) * D ≤ D := mul_le_of_le_one_left hD₀ (by nlinarith)
  calc r * σ + (2 + r) * (2 * γ * C * Λ) + (C / (1 - γ) - -(C / (1 - γ))) * L / (3 * N)
      ≤ r * σ + (2 + r) * (2 * γ * C * r) + (C / (1 - γ) - -(C / (1 - γ))) * L / (3 * N) := by
        gcongr
    _ = r * σ + 4 * γ * C * r + 4 * γ * (1 - γ) * D + 2 / 3 * D := by
        rw [show (2 + r) * (2 * γ * C * r) = 4 * γ * C * r + 2 * γ * C * r ^ 2 by ring, hr2]
        simp only [D]
        field_simp
        ring
    _ ≤ r * σ + 4 * γ * C * r + 5 * C * L / ((1 - γ) * N) := by
        rw [show 5 * C * L / ((1 - γ) * N) = 5 * D by simp only [D]; ring]
        linarith

section Generative

variable [Fintype 𝓢] [Fintype 𝓐]

/-- The common proof of [AKY20, Lemma 9] for the optimal values and for the values of a fixed
policy: `G M'` is the optimal value or the value of a fixed policy in `M'`, bounded by
`C / (1 - γ)` and within `|G M' s - u|` of its value in the `s`-absorbing modification with reward
`(1 - γ) u`, and `hcrude` is the crude bound on `G M - G (M.empirical N ω)`. -/
private theorem le_streamMeasure_forall_abs_integral_sub_le_of_absorbing {M : MDP 𝓢 𝓐 ℝ}
    {γ : ℝ≥0} (hγ : γ < 1) {C : ℝ} (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (N : ℕ) [NeZero N]
    {δ : ℝ} (hδ : 0 < δ) (G : MDP 𝓢 𝓐 ℝ → 𝓢 → ℝ)
    (hGb : ∀ M' : MDP 𝓢 𝓐 ℝ, (∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C) → ∀ s, |G M' s| ≤ C / (1 - γ))
    (hGabs : ∀ M' : MDP 𝓢 𝓐 ℝ, (∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C) → ∀ s u s',
      |G M' s' - G (M'.absorbing s ((1 - γ) * u)) s'| ≤ |G M' s - u|)
    (hcrude : 1 - δ / 2 ≤ (streamMeasure M.P).real {ω | ∀ s, |G M s - G (M.empirical N ω) s| ≤
      γ * C * √(2 * log (4 * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) / N) / (1 - γ) ^ 2}) :
    1 - δ ≤ (streamMeasure M.P).real {ω | ∀ p,
      |∫ s, G (M.empirical N ω) s ∂(M.P p) - ∫ s, G (M.empirical N ω) s ∂((M.empirical N ω).P p)| ≤
        √(2 * log (12 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) ^ 2 * δ)) / N) *
            √Var[G (M.empirical N ω); M.P p] +
          4 * γ * C * √(2 * log (12 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) ^ 2 * δ)) / N) +
          5 * C * log (12 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) ^ 2 * δ)) /
            ((1 - γ) * N)} := by
  set μ := streamMeasure M.P
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact (sub_nonpos.2 hδ1).trans measureReal_nonneg
  rcases isEmpty_or_nonempty (𝓢 × 𝓐) with h𝓢𝓐 | ⟨⟨s₀, a₀⟩⟩
  · refine le_trans ?_ (measureReal_mono (s₁ := Set.univ) (fun ω _ p ↦ (IsEmpty.false p).elim)
      (measure_ne_top _ _))
    rw [probReal_univ]
    linarith
  have : Nonempty 𝓢 := ⟨s₀⟩
  have : Nonempty 𝓐 := ⟨a₀⟩
  have hγ₀ : (0 : ℝ) ≤ γ := γ.coe_nonneg
  have hγ₁ : (γ : ℝ) < 1 := NNReal.coe_lt_one.2 hγ
  set θ : ℝ := 1 - γ with hθ
  have hθ₀ : 0 < θ := sub_pos.2 hγ₁
  have hθ₁ : θ ≤ 1 := by linarith
  have hθ₂ : θ ^ 2 ≤ 1 := pow_le_one₀ hθ₀.le hθ₁
  set S : ℝ := (Fintype.card 𝓢 : ℝ)
  set A : ℝ := (Fintype.card 𝓐 : ℝ)
  set L := log (12 * S * A / (θ ^ 2 * δ))
  set Λ := √(2 * log (4 * S * A / δ) / N)
  set r := √(2 * L / N)
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hS : 1 ≤ S := Nat.one_le_cast.2 Fintype.card_pos
  have hA : 1 ≤ A := Nat.one_le_cast.2 Fintype.card_pos
  have hSA : 1 ≤ S * A := one_le_mul_of_one_le_of_one_le hS hA
  have hR' (ω : ℕ → 𝓢 × 𝓐 → 𝓢) : ∀ p, ∀ᵐ x ∂((M.empirical N ω).R p), |x| ≤ C := by
    simpa using hR
  have hC : 0 ≤ C := (abs_nonneg _).trans (abs_meanReward_le hR (s₀, a₀))
  -- the radius `Λ` of the crude bounds is at most `r`
  have hL₀ : 0 ≤ log (4 * S * A / δ) := Real.log_nonneg ((one_le_div hδ).2 (by nlinarith))
  have hL : log (4 * S * A / δ) ≤ L := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ hδ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hθ₂ (by positivity : (0 : ℝ) ≤ 4 * S * A * δ)]
  have hL' : 0 ≤ L := hL₀.trans hL
  have hr2 : r ^ 2 = 2 * L / N := Real.sq_sqrt (by positivity)
  have hΛ : Λ ≤ r := Real.sqrt_le_sqrt (by gcongr)
  -- for `C = 0`, all the values vanish
  rcases hC.eq_or_lt with rfl | hC₀
  · have hG₀ (ω : ℕ → 𝓢 × 𝓐 → 𝓢) : G (M.empirical N ω) = 0 :=
      funext fun s ↦ abs_nonpos_iff.1 ((hGb _ (hR' ω) s).trans_eq (zero_div _))
    refine le_trans ?_ (measureReal_mono (s₁ := Set.univ) (fun ω _ p ↦ by simp [hG₀])
      (measure_ne_top _ _))
    rw [probReal_univ]
    linarith
  set B := C / θ
  have hB : 0 < B := div_pos hC₀ hθ₀
  -- the size `K + 1` of the net, with `θ ^ 2 K ≥ 1` and `θ ^ 2 (K + 1) ≤ 3`
  set K : ℕ := ⌈(θ ^ 2)⁻¹⌉₊
  have hK : 0 < K := Nat.ceil_pos.2 (by positivity)
  have hK₁ : 1 ≤ θ ^ 2 * K := (inv_le_iff_one_le_mul₀' (by positivity)).1 (Nat.le_ceil _)
  have hK₂ : θ ^ 2 * (K + 1) ≤ 3 := by
    have h : (K : ℝ) < (θ ^ 2)⁻¹ + 1 := Nat.ceil_lt_add_one (inv_nonneg.2 (sq_nonneg θ))
    calc θ ^ 2 * (K + 1) ≤ θ ^ 2 * ((θ ^ 2)⁻¹ + 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg θ)
      _ = 1 + 2 * θ ^ 2 := by field_simp
      _ ≤ 3 := by linarith
  -- the net at the state `s`: a grid on the interval of radius `Δ` around `G M s`, clipped to
  -- `[-B, B]`
  set Δ := γ * C * Λ / θ ^ 2
  have hBB : -B ≤ B := neg_le_self hB.le
  set net : 𝓢 → Fin (K + 1) → ℝ :=
    fun s k ↦ Set.projIcc (-B) B hBB (G M s - Δ + 2 * Δ * (k : ℕ) / K)
  have hnet (s : 𝓢) (k : Fin (K + 1)) : |θ * net s k| ≤ C := by
    have h : |net s k| ≤ B := abs_le.2 (Set.projIcc (-B) B hBB _).2
    rw [abs_mul, abs_of_pos hθ₀]
    calc θ * |net s k| ≤ θ * B := by gcongr
      _ = C := mul_div_cancel₀ C hθ₀.ne'
  -- the values of the absorbing modifications at the points of the net
  set W : (ℕ → 𝓢 × 𝓐 → 𝓢) → 𝓢 → Fin (K + 1) → 𝓢 → ℝ :=
    fun ω s k ↦ G ((M.empirical N ω).absorbing s (θ * net s k))
  have hWb (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (s : 𝓢) (k : Fin (K + 1)) (s' : 𝓢) :
      W ω s k s' ∈ Set.Icc (-B) B :=
    abs_le.1 (hGb _ (fun p ↦ (ae_abs_absorbing_R_le (hR' ω) p).mono fun _ hx ↦
      hx.trans (max_le le_rfl (hnet s k))) s')
  -- the bad events of the Bernstein inequality, for every pair and every point of the net
  set bad : 𝓢 × 𝓐 × Fin (K + 1) → Set (ℕ → 𝓢 × 𝓐 → 𝓢) := fun i ↦ {ω |
    √(2 * Var[W ω i.1 i.2.2; M.P (i.1, i.2.1)] * L / N) + (B - -B) * L / (3 * N) ≤
      |∫ s', W ω i.1 i.2.2 s' ∂(M.P (i.1, i.2.1)) -
        ∫ s', W ω i.1 i.2.2 s' ∂((M.empirical N ω).P (i.1, i.2.1))|}
  have h_bad (i : 𝓢 × 𝓐 × Fin (K + 1)) :
      μ.real (bad i) ≤ δ / 2 / Fintype.card (𝓢 × 𝓐 × Fin (K + 1)) := by
    refine (measureReal_sqrt_variance_add_le_abs_integral_sub_integral_empirical_absorbing_le M N G
      (neg_lt_self hB) i.1 _ (fun ω ↦ hWb ω i.1 i.2.2) i.2.1 L).trans ?_
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact two_mul_exp_neg_log_le (by positivity) (by positivity) (Nat.cast_nonneg K) hθ₀ hδ hK₂
  have h_good : 1 - δ / 2 ≤ μ.real (⋃ i, bad i)ᶜ :=
    one_sub_le_measureReal_compl_iUnion (by positivity) h_bad
  -- the crude event is measurable, and both events hold with probability at least `1 - δ`
  have h_meas : MeasurableSet {ω | ∀ s, |G M s - G (M.empirical N ω) s| ≤ Δ} :=
    measurableSet_setOfPred.2 (measurable_comp_empirical M N fun M' ↦ ∀ s, |G M s - G M' s| ≤ Δ)
  have h_inter :
      1 - δ ≤ μ.real ((⋃ i, bad i)ᶜ ∩ {ω | ∀ s, |G M s - G (M.empirical N ω) s| ≤ Δ}) := by
    have h := measureReal_union_add_inter (μ := μ) (s := (⋃ i, bad i)ᶜ) h_meas
    have h₁ : μ.real ((⋃ i, bad i)ᶜ ∪ {ω | ∀ s, |G M s - G (M.empirical N ω) s| ≤ Δ}) ≤ 1 :=
      measureReal_le_one
    linarith
  refine h_inter.trans (measureReal_mono (fun ω ⟨hω₁, hω₂⟩ ↦ ?_) (measure_ne_top _ _))
  rintro ⟨s, a⟩
  -- a point of the net within `2 Δ / K ≤ 2 γ C Λ` of `G (M.empirical N ω) s ∈ [-B, B]`
  obtain ⟨k, hk⟩ := exists_abs_sub_projIcc_grid_le hBB (abs_le.1 (hGb _ (hR' ω) s))
    ((abs_sub_comm _ _).trans_le (hω₂ s)) hK
  have hd : |G (M.empirical N ω) s - net s k| ≤ 2 * γ * C * Λ := by
    refine hk.trans ?_
    rw [div_le_iff₀ (by positivity)]
    calc 2 * Δ = 2 * Δ * 1 := (mul_one _).symm
      _ ≤ 2 * Δ * (θ ^ 2 * K) := by gcongr
      _ = 2 * γ * C * Λ * K := by
          simp only [Δ]
          field_simp
  -- the Bernstein bound at the point `k` of the net, transferred to `G (M.empirical N ω)`
  have hW : |∫ s', W ω s k s' ∂(M.P (s, a)) - ∫ s', W ω s k s' ∂((M.empirical N ω).P (s, a))| ≤
      r * √Var[W ω s k; M.P (s, a)] + (B - -B) * L / (3 * N) := by
    have h : ω ∉ bad (s, a, k) := fun h ↦ hω₁ (Set.mem_iUnion.2 ⟨_, h⟩)
    simp only [bad, Set.mem_ofPred_eq, not_le] at h
    refine h.le.trans_eq ?_
    rw [show 2 * Var[W ω s k; M.P (s, a)] * L / N = 2 * L / N * Var[W ω s k; M.P (s, a)] by ring,
      Real.sqrt_mul (div_nonneg (mul_nonneg zero_le_two hL') hN.le)]
  have h := abs_integral_sub_integral_le_of_abs_sub_le .of_discrete .of_discrete .of_finite
    .of_finite (Real.sqrt_nonneg _) (fun s' ↦ (hGabs _ (hR' ω) s (net s k) s').trans hd) hW
  exact h.trans (net_bound_le hγ₀ hγ₁ hC hL' hN (Real.sqrt_nonneg _) hΛ hr2)

/-- **Bernstein-type bound for the value of a fixed policy in the empirical MDP** [AKY20, Lemma 9,
second claim]. Under the generative model of an MDP `M` with `S` states, `A` actions and rewards
bounded by `C`, for `γ < 1`, a stationary policy `π`, `N ≠ 0` and `δ > 0`, with probability at
least `1 - δ`, the value `v̂ = (M.empirical N ω).value γ π` of `π` in the empirical MDP satisfies
`|∫ v̂ dP p - ∫ v̂ dP̂ p| ≤ √(2 L / N) √(Var_{P p}(v̂)) + E` for every state-action pair `p`, with
`E = 4 γ C √(2 L / N) + 5 C L / ((1 - γ) N)` and `L = log (12 S A / ((1 - γ) ^ 2 δ))`. -/
theorem le_streamMeasure_forall_abs_integral_value_empirical_sub_integral_value_empirical_le
    {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} (hγ : γ < 1) {C : ℝ} (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] (N : ℕ) [NeZero N] {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ (streamMeasure M.P).real {ω | ∀ p,
      |∫ s, (M.empirical N ω).value γ π s ∂(M.P p) -
          ∫ s, (M.empirical N ω).value γ π s ∂((M.empirical N ω).P p)| ≤
        √(2 * log (12 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) ^ 2 * δ)) / N) *
            √Var[(M.empirical N ω).value γ π; M.P p] +
          4 * γ * C * √(2 * log (12 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) ^ 2 * δ)) / N) +
          5 * C * log (12 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) ^ 2 * δ)) /
            ((1 - γ) * N)} := by
  refine le_streamMeasure_forall_abs_integral_sub_le_of_absorbing hγ hR N hδ
    (fun M' ↦ M'.value γ π) (fun M' hR' s ↦ abs_value_le hγ hR' s)
    (fun M' hR' s u s' ↦ abs_value_sub_value_absorbing_le (s := s) hγ hR' u s') ?_
  -- the crude bound, from Hoeffding's inequality for the fixed function `v^π`
  have hvB := abs_value_le (π := π) hγ hR
  refine (le_streamMeasure_forall_abs_integral_sub_integral_empiricalKernel_le M.P
    (measurable_value hγ hR) (fun _ ↦ ae_of_all _ fun s ↦ abs_le.1 (hvB s)) N
    (half_pos hδ)).trans (measureReal_mono (fun ω hω s ↦ ?_) (measure_ne_top _ _))
  refine (abs_value_sub_value_le (M' := M.empirical N ω) hγ hR (by simpa using hR) (δ := 0)
    (fun q ↦ by simp) (fun q ↦ by rw [empirical_P]; exact hω q) s).trans_eq ?_
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hγ' : (1 - γ : ℝ) ≠ 0 := (sub_pos.2 (NNReal.coe_lt_one.2 hγ)).ne'
  rw [Fintype.card_prod, Nat.cast_mul,
    show 2 * ((Fintype.card 𝓢 : ℝ) * Fintype.card 𝓐) / (δ / 2) =
      4 * Fintype.card 𝓢 * Fintype.card 𝓐 / δ by field_simp; ring,
    show 2 * log (4 * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) / N =
      2 ^ 2 * (log (4 * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) / (2 * N)) by field_simp,
    Real.sqrt_mul (by positivity), Real.sqrt_sq zero_le_two]
  field_simp
  ring

/-- **Bernstein-type bound for the optimal value of the empirical MDP** [AKY20, Lemma 9, first
claim]. Under the generative model of an MDP `M` with `S` states, `A` actions and rewards bounded
by `C`, for `γ < 1`, `N ≠ 0` and `δ > 0`, with probability at least `1 - δ`, the optimal value
`v̂* = (M.empirical N ω).optValue γ` of the empirical MDP satisfies
`|∫ v̂* dP p - ∫ v̂* dP̂ p| ≤ √(2 L / N) √(Var_{P p}(v̂*)) + E` for every state-action pair `p`,
with `E = 4 γ C √(2 L / N) + 5 C L / ((1 - γ) N)` and `L = log (12 S A / ((1 - γ) ^ 2 δ))`. -/
theorem le_streamMeasure_forall_abs_integral_optValue_empirical_sub_integral_optValue_empirical_le
    [Nonempty 𝓢] [Nonempty 𝓐] {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} (hγ : γ < 1) {C : ℝ}
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (N : ℕ) [NeZero N] {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ (streamMeasure M.P).real {ω | ∀ p,
      |∫ s, (M.empirical N ω).optValue γ s ∂(M.P p) -
          ∫ s, (M.empirical N ω).optValue γ s ∂((M.empirical N ω).P p)| ≤
        √(2 * log (12 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) ^ 2 * δ)) / N) *
            √Var[(M.empirical N ω).optValue γ; M.P p] +
          4 * γ * C * √(2 * log (12 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) ^ 2 * δ)) / N) +
          5 * C * log (12 * Fintype.card 𝓢 * Fintype.card 𝓐 / ((1 - γ) ^ 2 * δ)) /
            ((1 - γ) * N)} := by
  refine le_streamMeasure_forall_abs_integral_sub_le_of_absorbing hγ hR N hδ
    (fun M' ↦ M'.optValue γ) (fun M' hR' s ↦ abs_optValue_le hγ hR' s)
    (fun M' hR' s u s' ↦ abs_optValue_sub_optValue_absorbing_le (s := s) hγ hR' u s') ?_
  -- the crude bound, from Hoeffding's inequality for the fixed function `v*`
  refine (le_streamMeasure_forall_abs_integral_optValue_sub_integral_optValue_empirical_le hγ hR
    N (half_pos hδ)).trans (measureReal_mono (fun ω hω s ↦ ?_) (measure_ne_top _ _))
  refine (abs_optValue_sub_optValue_le (M' := M.empirical N ω) hγ hR (by simpa using hR) (δ := 0)
    (fun q ↦ by simp) hω s).trans_eq ?_
  have hγ' : (1 - γ : ℝ) ≠ 0 := (sub_pos.2 (NNReal.coe_lt_one.2 hγ)).ne'
  rw [show 2 * (Fintype.card 𝓢 : ℝ) * Fintype.card 𝓐 / (δ / 2) =
    4 * Fintype.card 𝓢 * Fintype.card 𝓐 / δ by field_simp; ring]
  field_simp
  ring

end Generative

end Learning.MDP
