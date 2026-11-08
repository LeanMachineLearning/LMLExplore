/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.ReturnVariance
public import LMLExplore.ReinforcementLearning.Generative.Basic

/-!
# Planning with a generative model: value estimation with variance-aware accuracy

Let `M` be an MDP with `S` states, `A` actions and rewards bounded by `C`, and `γ < 1`. Under the
generative model `Bandits.streamMeasure M.P`, the empirical MDP `M̂ = M.empirical N ω` of `N`
samples per state-action pair estimates the optimal action values of `M` with accuracy
[AJKS, Theorem 2.6 (first claim)], [AMK13]: for `δ > 0`, with probability at least `1 - δ`,

`|Q* - Q̂*| ≤ 2 γ C √(L / ((1 - γ) ^ 3 N)) + 17 γ C L / ((1 - γ) ^ 3 N)`, with
`L = log (3 S A / δ)`.

For `N ≥ L / (1 - γ) ^ 3`, the second term is at most `17 / 2` times the first, and the bound is of
order `γ C √(L / ((1 - γ) ^ 3 N))`: up to constants, a factor `√(1 - γ)` better than the crude bound
`γ C √(2 log (2 S A / δ) / N) / (1 - γ) ^ 2` of
`Learning.MDP.le_streamMeasure_forall_abs_optQValue_sub_optQValue_empirical_le'`. This is the
minimax rate of [AMK13].

The bound has a deterministic part and a probabilistic part.
* The **deterministic part** holds for any two MDPs `M` and `M'` with the same mean rewards. If
  the one-step predictions of the optimal value `v*` of `M` satisfy the Bernstein-type bound
  `|∫ v* dP q - ∫ v* dP' q| ≤ a √(Var_{P' q}(v*)) + b` at every pair `q`, then the componentwise
  bounds of `MarkovDecisionProcess/Simulation.lean` express `Q* - Q'*` through the resolvents
  `R_γ(P'^π_SA)` of an optimal policy `π` of `M` and of an optimal policy of `M'`, applied to these
  one-step errors. The standard deviation of `v*` is within `‖v* - v'^π‖` of the standard
  deviation of the value `v'^π` of `π` in `M'`, and the total-variance lemma
  (`Learning.MDP.integral_sqrt_variance_value_resolvent_le`) in `M'` bounds the resolvent of the
  latter by `C √(2 / (1 - γ) ^ 3)`.
* The **probabilistic part** is the empirical Bernstein inequality for the fixed function `v*`
  under the empirical kernel, with a union bound over the pairs
  (`LMLExplore.le_streamMeasure_forall_abs_integral_sub_integral_empiricalKernel_lt_sqrt_add`).
  It gives the Bernstein-type bound with `a = √(2 L / N)` and `b = 6 C L / ((1 - γ) N)`, with the
  variance of `v*` under the empirical kernel, which is the one the deterministic part needs.

[AJKS] instead uses Bernstein's inequality with the variance under `P` and compares it with the
variance under `P̂` through Hoeffding's inequality for `v*` and `v* ^ 2`; the empirical Bernstein
inequality does this comparison at once.

## Main statements

* `Learning.MDP.abs_optQValue_sub_optQValue_le_of_le_sqrt_variance`: the deterministic part, for
  two MDPs with the same mean rewards.
* `Learning.MDP.le_streamMeasure_forall_abs_optQValue_sub_optQValue_empirical_le_sqrt_add`: value
  estimation with a generative model [AJKS, Theorem 2.6 (first claim)].

## References

* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], Theorem 2.6 and §2.4
* [M. G. Azar, R. Munos and H. J. Kappen, *Minimax PAC bounds on the sample complexity of
  reinforcement learning with a generative model*, Machine Learning 91, 2013][AMK13]
* [J.-Y. Audibert, R. Munos and Cs. Szepesvári, *Exploration–exploitation tradeoff using variance
  estimates in multi-armed bandits*, Theoretical Computer Science 410 (2009)][AMS09], Theorem 1
-/

public section

open MeasureTheory ProbabilityTheory LMLExplore Learning Bandits
open Real (log)
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}

section Deterministic

variable [Nonempty 𝓢] [Nonempty 𝓐] [Finite 𝓐] {M M' : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {C a b : ℝ}

/-- For two MDPs with the same mean rewards and a one-step error of the optimal value `v*` of `M`
bounded by `a √(Var_{P' q}(v*)) + b`, the resolvent of the state-action kernel in `M'` of a
stationary policy `π` whose value in `M'` is within `D` of `v*` maps the right-hand side of the
componentwise bounds to at most `γ (a C √(2 / (1 - γ) ^ 3) + (a D + b) / (1 - γ))`. -/
private lemma abs_integral_resolvent_le_of_le_sqrt_variance (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C)
    (hr : meanReward M'.R = meanReward M.R) (ha : 0 ≤ a)
    (hε : ∀ q, |∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)| ≤
      a * √(Var[M.optValue γ; M'.P q]) + b)
    (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] {D : ℝ}
    (hD : ∀ s, |M.optValue γ s - M'.value γ π s| ≤ D) (p : 𝓢 × 𝓐) :
    |∫ q, (meanReward M.R q - meanReward M'.R q +
        γ * (∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)))
        ∂(Kernel.resolvent γ (M'.saKernel π) p)| ≤
      γ * (a * C * √(2 / (1 - γ) ^ 3) + (a * D + b) / (1 - γ)) := by
  have := Kernel.isFiniteKernel_resolvent (κ := M'.saKernel π) hγ
  have hγ' : 0 < 1 - (γ : ℝ) := sub_pos.2 hγ
  have hB : 0 ≤ C / (1 - γ) := (abs_nonneg _).trans (abs_value_le (π := π) hγ hR' p.1)
  have hv := measurable_optValue hγ hR
  have hvB := abs_optValue_le hγ hR
  have hv' := measurable_value (π := π) hγ hR'
  have hvB' := abs_value_le (π := π) hγ hR'
  set ρ := Kernel.resolvent γ (M'.saKernel π) p
  -- the one-step error `g = (P - P') v*` and the standard deviation `σ` of `v^π_M'` under `P'`
  set g : 𝓢 × 𝓐 → ℝ := fun q ↦ ∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)
  set σ : 𝓢 × 𝓐 → ℝ := fun q ↦ √(Var[M'.value γ π; M'.P q])
  have hg : Measurable g := (hv.stronglyMeasurable.integral_kernel (κ := M.P)).measurable.fun_sub
    (hv.stronglyMeasurable.integral_kernel (κ := M'.P)).measurable
  have hgB (q : 𝓢 × 𝓐) : |g q| ≤ C / (1 - γ) + C / (1 - γ) := (abs_sub _ _).trans
    (add_le_add (abs_integral_le_of_abs_le hvB) (abs_integral_le_of_abs_le hvB))
  have hσ : Measurable σ := (hv'.variance_kernel (η := M'.P)).sqrt
  have hσB (q : 𝓢 × 𝓐) : |σ q| ≤ C / (1 - γ) := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_left hB]
    exact variance_le_sq_of_abs_le hv'.aemeasurable (.of_forall hvB')
  -- pointwise, `|g| ≤ a (σ + D) + b`: the standard deviations of `v*` and `v^π_M'` are within `D`
  have h_pt (q : 𝓢 × 𝓐) : |g q| ≤ a * σ q + (a * D + b) := by
    have hmem {f : 𝓢 → ℝ} (hf : Measurable f) (hfB : ∀ s, |f s| ≤ C / (1 - γ)) :
        MemLp f 2 (M'.P q) :=
      MemLp.of_bound hf.aestronglyMeasurable _
        (.of_forall fun s ↦ (Real.norm_eq_abs _).trans_le (hfB s))
    have h_sd := sqrt_variance_le_sqrt_variance_add_of_abs_sub_le (hmem hv hvB) (hmem hv' hvB')
      (.of_forall hD)
    calc |g q| ≤ a * √(Var[M.optValue γ; M'.P q]) + b := hε q
      _ ≤ a * (σ q + D) + b := by gcongr
      _ = a * σ q + (a * D + b) := by ring
  have h_int : ∫ q, σ q ∂ρ ≤ C * √(2 / (1 - γ) ^ 3) :=
    integral_sqrt_variance_value_resolvent_le hγ hR' p
  simp only [hr, sub_self, zero_add]
  rw [integral_const_mul, abs_mul, NNReal.abs_eq]
  gcongr
  calc |∫ q, g q ∂ρ| ≤ ∫ q, |g q| ∂ρ := abs_integral_le_integral_abs
    _ ≤ ∫ q, (a * σ q + (a * D + b)) ∂ρ :=
        integral_mono (integrable_of_abs_le hg hgB ρ).abs
          ((integrable_of_abs_le hσ hσB ρ).const_mul a |>.add (integrable_const _)) h_pt
    _ = a * ∫ q, σ q ∂ρ + (a * D + b) / (1 - γ) := by
        rw [integral_add ((integrable_of_abs_le hσ hσB ρ).const_mul a) (integrable_const _),
          integral_const_mul, integral_const, smul_eq_mul, Kernel.measureReal_resolvent_univ hγ,
          inv_mul_eq_div]
    _ ≤ a * (C * √(2 / (1 - γ) ^ 3)) + (a * D + b) / (1 - γ) := by gcongr
    _ = a * C * √(2 / (1 - γ) ^ 3) + (a * D + b) / (1 - γ) := by ring

/-- **Variance-aware accuracy of the optimal action values** [AJKS, §2.4]: for two MDPs `M` and
`M'` with finitely many actions, the same mean rewards, rewards bounded by `C` and `γ < 1`, if the
one-step predictions of the optimal value `v*` of `M` satisfy, for some `a ≥ 0` and `b`, the
Bernstein-type bound `|∫ v* dP q - ∫ v* dP' q| ≤ a √(Var_{P' q}(v*)) + b` at every pair `q`, then
the optimal action values satisfy
`|Q*_M - Q*_M'| ≤ γ (a C √(2 / (1 - γ) ^ 3) + (a D + b) / (1 - γ))`, with
`D = γ (a C / (1 - γ) + b) / (1 - γ)`. For a small `a`, the leading term `γ a C √(2 / (1 - γ) ^ 3)`
is smaller by the factor `√(1 - γ)` than the bound `γ a C / (1 - γ) ^ 2` obtained from the
uniform bound `√(Var_{P' q}(v*)) ≤ C / (1 - γ)`. -/
theorem abs_optQValue_sub_optQValue_le_of_le_sqrt_variance (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C)
    (hr : meanReward M'.R = meanReward M.R) (ha : 0 ≤ a)
    (hε : ∀ q, |∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)| ≤
      a * √(Var[M.optValue γ; M'.P q]) + b) (p : 𝓢 × 𝓐) :
    |M.optQValue γ p - M'.optQValue γ p| ≤ γ * (a * C * √(2 / (1 - γ) ^ 3) +
      (a * (γ * (a * (C / (1 - γ)) + b) / (1 - γ)) + b) / (1 - γ)) := by
  have := Fintype.ofFinite 𝓐
  have hv := measurable_optValue hγ hR
  have hvB := abs_optValue_le hγ hR
  have hB : 0 ≤ C / (1 - γ) := (abs_nonneg _).trans (hvB (Classical.arbitrary 𝓢))
  have hδ (q : 𝓢 × 𝓐) : |meanReward M.R q - meanReward M'.R q| ≤ 0 := by simp [hr]
  -- the uniform bound on the one-step error, from `√(Var_{P' q}(v*)) ≤ C / (1 - γ)`
  have hε' (q : 𝓢 × 𝓐) : |∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)| ≤
      a * (C / (1 - γ)) + b := by
    refine (hε q).trans ?_
    gcongr
    rw [Real.sqrt_le_left hB]
    exact variance_le_sq_of_abs_le hv.aemeasurable (.of_forall hvB)
  -- the greedy policies for the optimal values are optimal stationary policies
  have hg := measurable_greedy (M := M) (γ := γ) hv
  have hg' := measurable_greedy (M := M') (γ := γ) (measurable_optValue hγ hR')
  have hπ := value_greedy_optValue hγ hR hg
  have hπ' := value_greedy_optValue hγ hR' hg'
  -- their values in `M'` are within `D` of `v*`, by the simulation bounds
  have hD (s : 𝓢) : |M.optValue γ s - M'.value γ (Kernel.deterministic _ hg) s| ≤
      γ * (a * (C / (1 - γ)) + b) / (1 - γ) := by
    have h := abs_value_sub_value_le (π := Kernel.deterministic _ hg) hγ hR hR' hδ
      (fun q ↦ by rw [hπ]; exact hε' q) s
    rwa [hπ, zero_div, zero_add] at h
  have hD' (s : 𝓢) : |M.optValue γ s - M'.value γ (Kernel.deterministic _ hg') s| ≤
      γ * (a * (C / (1 - γ)) + b) / (1 - γ) := by
    have h := abs_optValue_sub_optValue_le hγ hR hR' hδ hε' s
    rwa [← hπ', zero_div, zero_add] at h
  have h₁ := abs_integral_resolvent_le_of_le_sqrt_variance hγ hR hR' hr ha hε _ hD p
  have h₂ := abs_integral_resolvent_le_of_le_sqrt_variance hγ hR hR' hr ha hε _ hD' p
  exact abs_le.2 ⟨(neg_le_of_abs_le h₂).trans (le_optQValue_sub_optQValue hγ hR hR' hπ' p),
    (optQValue_sub_optQValue_le hγ hR hR' hπ p).trans (le_of_abs_le h₁)⟩

end Deterministic

/-- The numerical step of value estimation: for `L ≤ N`, the bound of
`Learning.MDP.abs_optQValue_sub_optQValue_le_of_le_sqrt_variance` with
`a = √(2 L / N)` and `b = 3 (2 C / (1 - γ)) L / N` is at most
`2 γ C √(L / ((1 - γ) ^ 3 N)) + 17 γ C L / ((1 - γ) ^ 3 N)`. -/
private lemma value_estimation_bound_le {γ C L N : ℝ} (hγ₀ : 0 ≤ γ) (hγ : γ < 1) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hN : 0 < N) (hLN : L ≤ N) :
    γ * (√(2 * L / N) * C * √(2 / (1 - γ) ^ 3) + (√(2 * L / N) * (γ * (√(2 * L / N) *
      (C / (1 - γ)) + 3 * (C / (1 - γ) - -(C / (1 - γ))) * L / N) / (1 - γ)) +
        3 * (C / (1 - γ) - -(C / (1 - γ))) * L / N) / (1 - γ)) ≤
      2 * γ * C * √(L / ((1 - γ) ^ 3 * N)) + 17 * γ * C * L / ((1 - γ) ^ 3 * N) := by
  set u := 1 - γ with hu_def
  have hu : 0 < u := sub_pos.2 hγ
  have hu1 : u ≤ 1 := by linarith
  set a := √(2 * L / N) with ha_def
  have ha2 : a * a = 2 * (L / N) := by
    rw [ha_def, Real.mul_self_sqrt (by positivity), mul_div_assoc]
  have hx1 : L / N ≤ 1 := (div_le_one hN).2 hLN
  have ha : a ≤ 3 / 2 := by
    rw [ha_def, Real.sqrt_le_left (by norm_num), mul_div_assoc]
    linarith
  have ha₀ : 0 ≤ a := Real.sqrt_nonneg _
  -- the leading term
  have e₁ : a * C * √(2 / u ^ 3) = 2 * C * √(L / (u ^ 3 * N)) := by
    have h : a * √(2 / u ^ 3) = 2 * √(L / (u ^ 3 * N)) := by
      rw [ha_def, ← Real.sqrt_mul (by positivity),
        show (2 : ℝ) * √(L / (u ^ 3 * N)) = √(2 ^ 2 * (L / (u ^ 3 * N))) by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq zero_le_two]]
      congr 1
      field_simp
    linear_combination C * h
  -- the second-order term, with `a ^ 2 = 2 L / N` and `a ≤ 3 / 2`
  have e₂ : (a * (γ * (a * (C / u) + 3 * (C / u - -(C / u)) * L / N) / u) +
      3 * (C / u - -(C / u)) * L / N) / u =
        C * (L / N) * (γ * (2 + 6 * a) + 6 * u) / u ^ 3 := by
    rw [show a * (γ * (a * (C / u) + 3 * (C / u - -(C / u)) * L / N) / u) =
      γ * ((a * a) * (C / u) + 6 * a * (C / u) * (L / N)) / u by ring, ha2]
    field_simp
    ring
  have h₂ : γ * (2 + 6 * a) + 6 * u ≤ 17 := by
    have : γ * (2 + 6 * a) ≤ 2 + 6 * a := mul_le_of_le_one_left (by positivity) (by linarith)
    linarith
  rw [e₁, e₂]
  calc γ * (2 * C * √(L / (u ^ 3 * N)) + C * (L / N) * (γ * (2 + 6 * a) + 6 * u) / u ^ 3)
      ≤ γ * (2 * C * √(L / (u ^ 3 * N)) + C * (L / N) * 17 / u ^ 3) := by gcongr
    _ = 2 * γ * C * √(L / (u ^ 3 * N)) + 17 * γ * C * L / (u ^ 3 * N) := by
        field_simp

section Generative

variable [MeasurableSingletonClass 𝓢] [MeasurableSingletonClass 𝓐] [Fintype 𝓢] [Fintype 𝓐]
  [Nonempty 𝓢] [Nonempty 𝓐]

/-- **Value estimation with a generative model** [AJKS, Theorem 2.6 (first claim)], [AMK13].
Under the generative model of an MDP `M` with `S` states, `A` actions and rewards bounded by `C`,
for `γ < 1`, `N ≠ 0` and `δ > 0`, with probability at least `1 - δ`, the optimal action values of
`M` and of `M.empirical N ω` differ by at most
`2 γ C √(L / ((1 - γ) ^ 3 N)) + 17 γ C L / ((1 - γ) ^ 3 N)`, with `L = log (3 S A / δ)`. -/
theorem le_streamMeasure_forall_abs_optQValue_sub_optQValue_empirical_le_sqrt_add
    {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} (hγ : γ < 1) {C : ℝ} (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (N : ℕ)
    [NeZero N] {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ (streamMeasure M.P).real {ω | ∀ p,
      |M.optQValue γ p - (M.empirical N ω).optQValue γ p| ≤
        2 * γ * C * √(log (3 * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) / ((1 - γ) ^ 3 * N)) +
          17 * γ * C * log (3 * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) / ((1 - γ) ^ 3 * N)} := by
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact (sub_nonpos.2 hδ1).trans measureReal_nonneg
  set L := log (3 * Fintype.card 𝓢 * Fintype.card 𝓐 / δ)
  have hγ' : 0 < 1 - (γ : ℝ) := sub_pos.2 hγ
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hL : 0 ≤ L := by
    have hS : (1 : ℝ) ≤ Fintype.card 𝓢 := by exact_mod_cast Fintype.card_pos
    have hA : (1 : ℝ) ≤ Fintype.card 𝓐 := by exact_mod_cast Fintype.card_pos
    refine Real.log_nonneg ((one_le_div hδ).2 ?_)
    nlinarith
  have hvB := abs_optValue_le hγ hR
  have hC : 0 ≤ C := (abs_nonneg _).trans (abs_meanReward_le hR (Classical.arbitrary _))
  have hR' (ω : ℕ → 𝓢 × 𝓐 → 𝓢) : ∀ p, ∀ᵐ x ∂((M.empirical N ω).R p), |x| ≤ C := by
    simpa using hR
  -- the crude bound `|Q* - Q̂*| ≤ 2 γ C / (1 - γ) ^ 2` suffices when `C = 0` or `N < L`
  have h_crude (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) (hCN : C = 0 ∨ (N : ℝ) < L) :
      |M.optQValue γ p - (M.empirical N ω).optQValue γ p| ≤
        2 * γ * C * √(L / ((1 - γ) ^ 3 * N)) + 17 * γ * C * L / ((1 - γ) ^ 3 * N) := by
    have h := abs_optQValue_sub_optQValue_le (M' := M.empirical N ω) hγ hR (hR' ω) (δ := 0)
      (fun q ↦ by simp) (fun q ↦ (abs_sub _ _).trans (add_le_add
        (abs_integral_le_of_abs_le (μ := M.P q) hvB)
        (abs_integral_le_of_abs_le (μ := (M.empirical N ω).P q) hvB))) p
    rw [zero_div, zero_add] at h
    refine h.trans ?_
    rcases hCN with hC₀ | hNL
    · simp [hC₀]
    refine le_add_of_nonneg_of_le (by positivity) ?_
    have h₁ : 2 * (1 - γ) * N ≤ 17 * L := by nlinarith [γ.coe_nonneg]
    calc (γ : ℝ) * (C / (1 - γ) + C / (1 - γ)) / (1 - γ) =
          γ * C * (2 * (1 - γ) * N) / ((1 - γ) ^ 3 * N) := by
          field_simp
          ring
      _ ≤ γ * C * (17 * L) / ((1 - γ) ^ 3 * N) := by gcongr
      _ = 17 * γ * C * L / ((1 - γ) ^ 3 * N) := by ring
  rcases hC.eq_or_lt with hC₀ | hC₀
  · have h_univ : {ω : ℕ → 𝓢 × 𝓐 → 𝓢 | ∀ p,
        |M.optQValue γ p - (M.empirical N ω).optQValue γ p| ≤
          2 * γ * C * √(L / ((1 - γ) ^ 3 * N)) + 17 * γ * C * L / ((1 - γ) ^ 3 * N)} =
        Set.univ :=
      Set.eq_univ_of_forall fun ω p ↦ h_crude ω p (.inl hC₀.symm)
    rw [h_univ, probReal_univ]
    linarith
  -- the empirical Bernstein inequality for `v*`, with values in `[-C / (1 - γ), C / (1 - γ)]`
  have h_ev := le_streamMeasure_forall_abs_integral_sub_integral_empiricalKernel_lt_sqrt_add M.P
    (measurable_optValue hγ hR) (l := -(C / (1 - γ))) (u := C / (1 - γ))
    (neg_lt_self (div_pos hC₀ hγ')) (fun _ ↦ ae_of_all _ fun s ↦ abs_le.1 (hvB s)) N hδ
  rw [Fintype.card_prod, Nat.cast_mul, ← mul_assoc] at h_ev
  refine h_ev.trans (measureReal_mono (fun ω hω p ↦ ?_) (measure_ne_top _ _))
  rcases lt_or_ge (N : ℝ) L with hNL | hLN
  · exact h_crude ω p (.inr hNL)
  have hε (q : 𝓢 × 𝓐) :
      |∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂((M.empirical N ω).P q)| ≤
        √(2 * L / N) * √(Var[M.optValue γ; (M.empirical N ω).P q]) +
          3 * (C / (1 - γ) - -(C / (1 - γ))) * L / N := by
    rw [empirical_P]
    refine (hω q).le.trans_eq ?_
    rw [show 2 * Var[M.optValue γ; empiricalKernel N ω q] * L / N =
      2 * L / N * Var[M.optValue γ; empiricalKernel N ω q] by ring,
      Real.sqrt_mul (by positivity)]
  exact (abs_optQValue_sub_optQValue_le_of_le_sqrt_variance hγ hR (hR' ω) (by simp)
    (Real.sqrt_nonneg _) hε p).trans (value_estimation_bound_le γ.coe_nonneg hγ hC hL hN hLN)

end Generative

end Learning.MDP
