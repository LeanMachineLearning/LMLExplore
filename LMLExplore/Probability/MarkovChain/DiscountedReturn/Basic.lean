/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.Integral.DominatedConvergence
public import LMLExplore.Probability.Kernel.Resolvent
public import LMLExplore.Probability.MarkovChain.DiscountedReturn.Defs
public import LMLExplore.Probability.Moments.Variance
public import TauCeti.Probability.MarkovChain.MarkovProperty
public import TauCeti.Probability.Moments.Mixture
import LMLExplore.Analysis.Convex.Integral
import LMLExplore.Probability.MarkovChain.MarkovProperty

/-!
# The discounted return of a Markov chain: its mean and its variance

Let `κ` be a Markov kernel on a measurable space `α`, `f : α → ℝ` a bounded measurable reward and
`γ < 1` a discount factor. Along a path `ω : ℕ → α`, the discounted return is
`G ω = ∑' t, γ ^ t * f (ω t)` (`LMLExplore.discountedReturn`, whose path-level API lives in
`LMLExplore.Probability.MarkovChain.DiscountedReturn.Defs`). Under the law
`ℙₓ = κ.markovChainKernel x` of the chain started at `x`, its mean `V x = ∫ G dℙₓ` is the
resolvent `R_γ(κ) f = ∑ t, γ ^ t κ ^ t f` evaluated at `x`, and its variance
satisfies the *total-variance identity* [Sob82], [AMK13]
`Var_x(G) = ∑' t, γ ^ (2 (t + 1)) (κ ^ t σ²)(x)`, where `σ² y = Var[V; κ y]` is the variance of
`V` after one step from `y`, that is `κ (V ^ 2) - (κ V) ^ 2`.

The identity comes from the first-step decomposition `G ω = f (ω 0) + γ G (θ ω)`, where `θ` shifts
the path. Under `ℙₓ` the first state is `x`, and the shifted path is the chain started from the
law `κ x` (the Markov property at time one,
`MeasureTheory.Measure.markovChainLaw_map_shift_iterate`), whose law is the mixture of the `ℙ_y`
over `y ∼ κ x`. The law of total variance for mixtures
(`TauCeti.Probability.variance_comp`) then gives the *variance Bellman equation*
`Var_x(G) = γ ^ 2 (Var[V; κ x] + ∫ Var_y(G) dκ x)`, whose unique bounded solution is the
resolvent `R_{γ²}(κ) (γ ^ 2 σ²)`.

The same decomposition writes `σ² = U - γ ^ 2 κ U` for the bounded function
`U y = Var[G; κ.markovChainKernel ∘ₘ κ y]`, so that the resolvent `R_γ(κ) σ²` with discount `γ`
(rather than `γ ^ 2`) is at most `(1 + γ) (C / (1 - γ)) ^ 2` for `|f| ≤ C`. With Jensen's
inequality for the square root, this gives the *total-variance lemma* [AJKS, Lemma 2.12]
`R_γ(κ) √σ² ≤ C √((1 + γ) / (1 - γ) ^ 3)`, of order `(1 - γ) ^ (-3/2)` where the pointwise bound
`√σ² ≤ C / (1 - γ)` alone gives `(1 - γ) ^ (-2)`.

## Main statements

* `ProbabilityTheory.Kernel.integral_discountedReturn_markovChainKernel`: the mean of the
  discounted return from `x` is `∫ f dR_γ(κ)(x)`;
  `MeasureTheory.Measure.integral_discountedReturn_markovChainLaw`: from an initial law `μ`, it is
  `∫ f d(R_γ(κ) ∘ₘ μ)`.
* `ProbabilityTheory.Kernel.abs_integral_discountedReturn_markovChainKernel_le`,
  `ProbabilityTheory.Kernel.variance_discountedReturn_markovChainKernel_le` and
  `ProbabilityTheory.Kernel.variance_integral_discountedReturn_markovChainKernel_le`: the bounds
  `C / (1 - γ)` on the mean, `γ ^ 2 (C / (1 - γ)) ^ 2` on the variance of the return and
  `(C / (1 - γ)) ^ 2` on the one-step variance of its mean.
* `ProbabilityTheory.Kernel.variance_discountedReturn_markovChainKernel_eq_mul_variance_comp`:
  `Var_x(G) = γ ^ 2 Var[G; κ.markovChainKernel ∘ₘ κ x]`.
* `ProbabilityTheory.Kernel.variance_discountedReturn_markovChainKernel_eq_add`: the variance
  Bellman equation `Var_x(G) = γ ^ 2 (Var[V; κ x] + ∫ Var_y(G) dκ x)`.
* `ProbabilityTheory.Kernel.variance_discountedReturn_markovChainKernel_eq_integral_resolvent`:
  `Var_x(G) = γ ^ 2 ∫ Var[V; κ y] dR_{γ²}(κ)(x)`.
* `ProbabilityTheory.Kernel.variance_discountedReturn_markovChainKernel`: the total-variance
  identity `Var_x(G) = ∑' t, γ ^ (2 (t + 1)) ∫ Var[V; κ y] d(κ ^ t)(x)`.
* `ProbabilityTheory.Kernel.integral_variance_integral_discountedReturn_resolvent_le` and
  `ProbabilityTheory.Kernel.integral_sqrt_variance_integral_discountedReturn_resolvent_le`: the
  resolvent with discount `γ` of the one-step variances is at most `(1 + γ) (C / (1 - γ)) ^ 2`,
  and that of the one-step standard deviations `√(Var[V; κ y])` is at most
  `C √((1 + γ) / (1 - γ) ^ 3)` (the *total-variance lemma*).

## References

* [M. J. Sobel, *The variance of discounted Markov decision processes*, 1982][Sob82]
* [M. G. Azar, R. Munos and H. J. Kappen, *Minimax PAC bounds on the sample complexity of
  reinforcement learning with a generative model*, 2013][AMK13]
* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], Lemma 2.11 (the state-action form of the variance Bellman equation)
  and Lemma 2.12 (the total-variance lemma)
-/

public section

open MeasureTheory Set Filter Topology TauCeti.Probability
open scoped ENNReal NNReal

namespace ProbabilityTheory.Kernel

open LMLExplore

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} [IsMarkovKernel κ] {γ : ℝ≥0}
  {f : α → ℝ} {C : ℝ}

/-! ### The mean of the discounted return -/

/-- **The mean of the discounted return is the resolvent**: for `γ < 1` and a bounded measurable
reward `f`, the expected discounted return of the chain started at `x` is
`∫ f dR_γ(κ)(x) = ∑' t, γ ^ t ∫ f d(κ ^ t)(x)`. -/
theorem integral_discountedReturn_markovChainKernel (hγ : γ < 1) (hf : Measurable f)
    (hfC : ∀ x, |f x| ≤ C) (x : α) :
    ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel x) = ∫ y, f y ∂(resolvent γ κ x) := by
  have := isFiniteKernel_resolvent (κ := κ) hγ
  have h_tsum := integral_tsum_smul_of_norm_le (μ := κ.markovChainKernel x)
    (summable_geometric_of_lt_one γ.coe_nonneg hγ) (C := C) (X := fun t ω ↦ f (ω t))
    (fun t ↦ (hf.comp (measurable_pi_apply t)).aestronglyMeasurable)
    (fun t ↦ .of_forall fun ω ↦ (Real.norm_eq_abs _).trans_le (hfC _))
  simp only [smul_eq_mul] at h_tsum
  simp_rw [discountedReturn_def, h_tsum,
    integral_resolvent (integrable_of_abs_le hf hfC (resolvent γ κ x)), smul_eq_mul]
  refine tsum_congr fun t ↦ ?_
  rw [← κ.markovChainKernel_map_eval t, map_apply _ (measurable_pi_apply t),
    integral_map (measurable_pi_apply t).aemeasurable hf.aestronglyMeasurable]

/-- The expected discounted return of the chain is a measurable function of the starting state. -/
theorem measurable_integral_discountedReturn_markovChainKernel (hγ : γ < 1) (hf : Measurable f)
    (hfC : ∀ x, |f x| ≤ C) :
    Measurable fun x ↦ ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel x) :=
  ((measurable_discountedReturn hγ hf hfC).stronglyMeasurable.integral_kernel).measurable

/-- For `γ < 1` and a reward bounded by `C`, the expected discounted return of the chain is bounded
by `C / (1 - γ)`. -/
theorem abs_integral_discountedReturn_markovChainKernel_le (hγ : γ < 1) (hfC : ∀ x, |f x| ≤ C)
    (x : α) :
    |∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel x)| ≤ C / (1 - γ) :=
  abs_integral_le_of_abs_le (abs_discountedReturn_le hγ hfC)

/-! ### The variance of the discounted return -/

/-- **First-step decomposition of the variance of the discounted return**: for `γ < 1` and a
bounded measurable reward `f`, the variance of the discounted return `G` of the chain started at `x`
is `γ ^ 2` times the variance of `G` under the chain started from the law `κ x`, the mixture
`κ.markovChainKernel ∘ₘ κ x` of the laws `ℙ_y`. -/
theorem variance_discountedReturn_markovChainKernel_eq_mul_variance_comp (hγ : γ < 1)
    (hf : Measurable f) (hfC : ∀ x, |f x| ≤ C) (x : α) :
    Var[discountedReturn γ f; κ.markovChainKernel x] =
      (γ : ℝ) ^ 2 * Var[discountedReturn γ f; κ.markovChainKernel ∘ₘ κ x] := by
  have hG := measurable_discountedReturn hγ hf hfC
  -- Started at `x`, the chain has `x` as its first state.
  have h_eval : (κ.markovChainKernel x).map (fun ω ↦ ω 0) = Measure.dirac x := by
    rw [← map_apply _ (measurable_pi_apply 0), markovChainKernel_map_eval, pow_zero, one_def,
      id_apply]
  have h_zero : ∀ᵐ ω ∂(κ.markovChainKernel x), f (ω 0) = f x := by
    have hs : MeasurableSet {y | f y = f x} := measurableSet_eq_fun hf measurable_const
    refine (ae_map_iff (f := fun ω : ℕ → α ↦ ω 0) (measurable_pi_apply 0).aemeasurable hs).1 ?_
    rw [h_eval, ae_dirac_iff hs]
  -- The shifted path is the chain started from `κ x`, a mixture of the laws `ℙ_y`.
  have h_shift : (κ.markovChainKernel x).map (shift α) = κ.markovChainKernel ∘ₘ κ x := by
    rw [← Function.iterate_one (shift α), ← map_apply _ (measurable_shift.iterate 1),
      markovChainKernel_map_shift_iterate, pow_one, comp_apply]
  calc Var[discountedReturn γ f; κ.markovChainKernel x]
      = Var[fun ω ↦ f x + γ * discountedReturn γ f (shift α ω); κ.markovChainKernel x] := by
        refine variance_congr ?_
        filter_upwards [h_zero] with ω hω
        rw [discountedReturn_eq_add_mul_shift hγ hfC, hω]
    _ = (γ : ℝ) ^ 2 * Var[discountedReturn γ f; κ.markovChainKernel ∘ₘ κ x] := by
        rw [variance_const_add (X := fun ω ↦ (γ : ℝ) * discountedReturn γ f (shift α ω))
          ((hG.comp measurable_shift).const_mul _).aestronglyMeasurable,
          variance_const_mul, ← h_shift,
          variance_map hG.aemeasurable measurable_shift.aemeasurable, Function.comp_def]

/-- For `γ < 1` and a bounded measurable reward `f` with `|f| ≤ C`, the variance of the discounted
return of the chain started at `x` is at most `γ ^ 2 (C / (1 - γ)) ^ 2`: the first reward `f x` is
deterministic, and the rest of the return is `γ` times a return bounded by `C / (1 - γ)`. -/
theorem variance_discountedReturn_markovChainKernel_le (hγ : γ < 1) (hf : Measurable f)
    (hfC : ∀ x, |f x| ≤ C) (x : α) :
    Var[discountedReturn γ f; κ.markovChainKernel x] ≤ (γ : ℝ) ^ 2 * (C / (1 - γ)) ^ 2 := by
  rw [variance_discountedReturn_markovChainKernel_eq_mul_variance_comp hγ hf hfC]
  gcongr
  exact variance_le_sq_of_abs_le (measurable_discountedReturn hγ hf hfC).aemeasurable
    (.of_forall (abs_discountedReturn_le hγ hfC))

/-- For `γ < 1` and a bounded measurable reward `f` with `|f| ≤ C`, the one-step variance
`Var[V; κ x]` of the expected discounted return `V y = ∫ G dℙ_y` is at most `(C / (1 - γ)) ^ 2`. -/
theorem variance_integral_discountedReturn_markovChainKernel_le (hγ : γ < 1) (hf : Measurable f)
    (hfC : ∀ x, |f x| ≤ C) (x : α) :
    Var[fun y ↦ ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel y); κ x] ≤ (C / (1 - γ)) ^ 2 :=
  variance_le_sq_of_abs_le
    (measurable_integral_discountedReturn_markovChainKernel hγ hf hfC).aemeasurable
    (.of_forall (abs_integral_discountedReturn_markovChainKernel_le hγ hfC))

/-- The law of total variance for the chain started from `κ x`: the variance of the discounted
return `G` under the mixture `κ.markovChainKernel ∘ₘ κ x` is `Var[V; κ x] + ∫ Var_y(G) dκ x`,
where `V y = ∫ G dℙ_y` is the expected discounted return. -/
private lemma variance_discountedReturn_comp_eq_add (hγ : γ < 1) (hf : Measurable f)
    (hfC : ∀ x, |f x| ≤ C) (x : α) :
    Var[discountedReturn γ f; κ.markovChainKernel ∘ₘ κ x] =
      Var[fun y ↦ ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel y); κ x] +
        ∫ y, Var[discountedReturn γ f; κ.markovChainKernel y] ∂(κ x) := by
  rw [variance_comp _ (MemLp.of_bound (measurable_discountedReturn hγ hf hfC).aestronglyMeasurable
    _ (.of_forall fun ω ↦ (Real.norm_eq_abs _).trans_le (abs_discountedReturn_le hγ hfC ω))),
    add_comm]

/-- **The variance Bellman equation**: for `γ < 1` and a bounded measurable reward `f`, the
variance `W x = Var_x(G)` of the discounted return `G` of the chain started at `x` satisfies
`W x = γ ^ 2 (Var[V; κ x] + ∫ W dκ x)`, where `V y = ∫ G dℙ_y` is the expected discounted return. -/
theorem variance_discountedReturn_markovChainKernel_eq_add (hγ : γ < 1) (hf : Measurable f)
    (hfC : ∀ x, |f x| ≤ C) (x : α) :
    Var[discountedReturn γ f; κ.markovChainKernel x] =
      (γ : ℝ) ^ 2 * (Var[fun y ↦ ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel y); κ x] +
        ∫ y, Var[discountedReturn γ f; κ.markovChainKernel y] ∂(κ x)) := by
  rw [variance_discountedReturn_markovChainKernel_eq_mul_variance_comp hγ hf hfC,
    variance_discountedReturn_comp_eq_add hγ hf hfC]

/-- **The total-variance identity, resolvent form**: for `γ < 1` and a bounded measurable reward
`f`, the variance of the discounted return `G` of the chain started at `x` is
`γ ^ 2 ∫ Var[V; κ y] dR_{γ²}(κ)(x)`, where `V y = ∫ G dℙ_y` is the expected discounted return. -/
theorem variance_discountedReturn_markovChainKernel_eq_integral_resolvent (hγ : γ < 1)
    (hf : Measurable f) (hfC : ∀ x, |f x| ≤ C) (x : α) :
    Var[discountedReturn γ f; κ.markovChainKernel x] =
      (γ : ℝ) ^ 2 * ∫ y, Var[fun z ↦ ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel z); κ y]
        ∂(resolvent (γ ^ 2) κ x) := by
  have hγ2 : γ ^ 2 < 1 := pow_lt_one₀ γ.zero_le_coe hγ two_ne_zero
  have hG := measurable_discountedReturn hγ hf hfC
  have hV := measurable_integral_discountedReturn_markovChainKernel (κ := κ) hγ hf hfC
  have h := eq_integral_resolvent_of_eq_add hγ2
    (f := fun y ↦ (γ : ℝ) ^ 2 *
      Var[fun z ↦ ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel z); κ y])
    (B := (γ : ℝ) ^ 2 * (C / (1 - γ)) ^ 2) (B' := (γ : ℝ) ^ 2 * (C / (1 - γ)) ^ 2)
    ((hV.variance_kernel (η := κ)).const_mul _)
    (fun y ↦ by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      gcongr
      exact (abs_of_nonneg (variance_nonneg _ _)).trans_le
        (variance_integral_discountedReturn_markovChainKernel_le hγ hf hfC y))
    (hG.variance_kernel (η := κ.markovChainKernel))
    (fun y ↦ (abs_of_nonneg (variance_nonneg _ _)).trans_le
      (variance_discountedReturn_markovChainKernel_le hγ hf hfC y))
    (fun y ↦ by
      rw [variance_discountedReturn_markovChainKernel_eq_add hγ hf hfC, NNReal.coe_pow]
      ring)
  rw [congrFun h x, integral_const_mul]

/-- **The total-variance identity** [Sob82]: for `γ < 1` and a bounded measurable reward `f`, the
variance of the discounted return `G` of the chain started at `x` is
`∑' t, γ ^ (2 (t + 1)) (κ ^ t σ²)(x)`, where `σ² y = Var[V; κ y]` is the one-step variance of the
expected discounted return `V y = ∫ G dℙ_y`. -/
theorem variance_discountedReturn_markovChainKernel (hγ : γ < 1) (hf : Measurable f)
    (hfC : ∀ x, |f x| ≤ C) (x : α) :
    Var[discountedReturn γ f; κ.markovChainKernel x] =
      ∑' t, (γ : ℝ) ^ (2 * (t + 1)) *
        ∫ y, Var[fun z ↦ ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel z); κ y]
          ∂((κ ^ t) x) := by
  have hγ2 : γ ^ 2 < 1 := pow_lt_one₀ γ.zero_le_coe hγ two_ne_zero
  have := isFiniteKernel_resolvent (κ := κ) hγ2
  have hV := measurable_integral_discountedReturn_markovChainKernel (κ := κ) hγ hf hfC
  rw [variance_discountedReturn_markovChainKernel_eq_integral_resolvent hγ hf hfC,
    integral_resolvent (integrable_of_abs_le (hV.variance_kernel (η := κ))
      (fun y ↦ (abs_of_nonneg (variance_nonneg _ _)).trans_le
        (variance_integral_discountedReturn_markovChainKernel_le hγ hf hfC y)) _),
    ← tsum_mul_left]
  refine tsum_congr fun t ↦ ?_
  rw [smul_eq_mul]
  push_cast
  ring

/-! ### The total-variance lemma -/

/-- The one-step variance `σ² y = Var[V; κ y]` of the expected discounted return is `U - γ ^ 2 κ U`,
where `U y = Var[G; κ.markovChainKernel ∘ₘ κ y]` is the variance of the return from the law
`κ y`. -/
private lemma variance_integral_discountedReturn_eq_sub (hγ : γ < 1) (hf : Measurable f)
    (hfC : ∀ x, |f x| ≤ C) (y : α) :
    Var[fun z ↦ ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel z); κ y] =
      Var[discountedReturn γ f; κ.markovChainKernel ∘ₘ κ y] -
        (γ : ℝ) ^ 2 * ∫ z, Var[discountedReturn γ f; κ.markovChainKernel ∘ₘ κ z] ∂(κ y) := by
  rw [variance_discountedReturn_comp_eq_add hγ hf hfC, ← integral_const_mul]
  simp_rw [variance_discountedReturn_markovChainKernel_eq_mul_variance_comp hγ hf hfC]
  ring

/-- For `γ < 1` and a bounded measurable reward `f` with `|f| ≤ C`, the resolvent `R_γ(κ)` of the
one-step variances `σ² y = Var[V; κ y]` of the expected discounted return `V y = ∫ G dℙ_y` is at
most `(1 + γ) (C / (1 - γ)) ^ 2`. The total-variance identity bounds their resolvent `R_{γ²}(κ)` by
`(C / (1 - γ)) ^ 2`; this is the corresponding bound for the resolvent with discount `γ`. -/
theorem integral_variance_integral_discountedReturn_resolvent_le (hγ : γ < 1) (hf : Measurable f)
    (hfC : ∀ x, |f x| ≤ C) (x : α) :
    ∫ y, Var[fun z ↦ ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel z); κ y]
        ∂(resolvent γ κ x) ≤ (1 + γ) * (C / (1 - γ)) ^ 2 := by
  have := isFiniteKernel_resolvent (κ := κ) hγ
  have hγ' : 0 < 1 - (γ : ℝ) := sub_pos.2 hγ
  have hG := measurable_discountedReturn hγ hf hfC
  -- `U y` is the variance of the return from the law `κ y`, and `P U` its mean after one step.
  let U y := Var[discountedReturn γ f; κ.markovChainKernel ∘ₘ κ y]
  let PU y := ∫ z, U z ∂(κ y)
  have hU : Measurable U := by
    have h := hG.variance_kernel (η := κ.markovChainKernel ∘ₖ κ)
    simp only [Kernel.comp_apply] at h
    exact h
  have hUB (y : α) : |U y| ≤ (C / (1 - γ)) ^ 2 := by
    rw [abs_of_nonneg (variance_nonneg _ _)]
    exact variance_le_sq_of_abs_le hG.aemeasurable (.of_forall (abs_discountedReturn_le hγ hfC))
  have hPU : Measurable PU := (hU.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  have hPUB (y : α) : |PU y| ≤ (C / (1 - γ)) ^ 2 := abs_integral_le_of_abs_le hUB
  -- `U` solves `U = (U - γ P U) + γ P U`, so it is the resolvent of `U - γ P U`.
  have hRU : ∫ y, (U y - γ * PU y) ∂(resolvent γ κ x) = U x := by
    refine (congrFun (eq_integral_resolvent_of_eq_add hγ (f := fun y ↦ U y - γ * PU y)
      (B := (C / (1 - γ)) ^ 2 + γ * (C / (1 - γ)) ^ 2) (hU.sub (hPU.const_mul _))
      (fun y ↦ (abs_sub _ _).trans (add_le_add (hUB y) ?_)) hU hUB
      fun y ↦ (sub_add_cancel _ _).symm) x).symm
    rw [abs_mul, NNReal.abs_eq]
    exact mul_le_mul_of_nonneg_left (hPUB y) γ.coe_nonneg
  -- Hence `R_γ σ² = R_γ (U - γ P U) + γ (1 - γ) R_γ P U = U + γ (1 - γ) R_γ P U`.
  have hσ (y : α) : Var[fun z ↦ ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel z); κ y] =
      (U y - γ * PU y) + γ * (1 - γ) * PU y := by
    rw [variance_integral_discountedReturn_eq_sub hγ hf hfC]
    ring
  have hint (g : α → ℝ) (hg : Measurable g) (hgB : ∀ y, |g y| ≤ (C / (1 - γ)) ^ 2) :
      Integrable g (resolvent γ κ x) := integrable_of_abs_le hg hgB _
  simp_rw [hσ]
  rw [integral_add (f := fun y ↦ U y - γ * PU y)
    ((hint U hU hUB).sub ((hint PU hPU hPUB).const_mul _)) ((hint PU hPU hPUB).const_mul _),
    integral_const_mul, hRU]
  calc U x + γ * (1 - γ) * ∫ y, PU y ∂(resolvent γ κ x)
      ≤ (C / (1 - γ)) ^ 2 + γ * (1 - γ) * ((C / (1 - γ)) ^ 2 / (1 - γ)) := by
        gcongr
        · exact (le_abs_self _).trans (hUB x)
        · exact (le_abs_self _).trans (abs_integral_resolvent_le hγ hPUB x)
    _ = (1 + γ) * (C / (1 - γ)) ^ 2 := by
        field_simp

/-- **The total-variance lemma** [AJKS, Lemma 2.12]: for `γ < 1` and a bounded measurable reward
`f` with `|f| ≤ C`, the resolvent `R_γ(κ)` of the one-step standard deviations `√(Var[V; κ y])` of
the expected discounted return `V y = ∫ G dℙ_y` is at most `C √((1 + γ) / (1 - γ) ^ 3)`, of order
`(1 - γ) ^ (-3/2)` instead of the `(1 - γ) ^ (-2)` that the bound `√(Var[V; κ y]) ≤ C / (1 - γ)`
alone would give. -/
theorem integral_sqrt_variance_integral_discountedReturn_resolvent_le (hγ : γ < 1)
    (hf : Measurable f) (hfC : ∀ x, |f x| ≤ C) (x : α) :
    ∫ y, √(Var[fun z ↦ ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel z); κ y])
        ∂(resolvent γ κ x) ≤ C * √((1 + γ) / (1 - γ) ^ 3) := by
  have := isFiniteKernel_resolvent (κ := κ) hγ
  have hγ' : 0 < 1 - (γ : ℝ) := sub_pos.2 hγ
  have hC : 0 ≤ C := (abs_nonneg _).trans (hfC x)
  have hσ := (measurable_integral_discountedReturn_markovChainKernel (κ := κ) hγ hf
    hfC).variance_kernel (η := κ)
  -- Jensen's inequality for the square root, for the resolvent of mass `(1 - γ)⁻¹`.
  refine (integral_sqrt_le_sqrt_measureReal_mul_integral (.of_forall fun y ↦ variance_nonneg _ _)
    (integrable_of_abs_le (B := (C / (1 - γ)) ^ 2) hσ (fun y ↦ ?_) (resolvent γ κ x))).trans ?_
  · rw [abs_of_nonneg (variance_nonneg _ _)]
    exact variance_integral_discountedReturn_markovChainKernel_le hγ hf hfC y
  rw [measureReal_resolvent_univ hγ, show C * √((1 + γ) / (1 - γ) ^ 3) =
      √((1 - (γ : ℝ))⁻¹ * ((1 + γ) * (C / (1 - γ)) ^ 2)) by
    rw [show (1 - (γ : ℝ))⁻¹ * ((1 + γ) * (C / (1 - γ)) ^ 2) =
      C ^ 2 * ((1 + γ) / (1 - γ) ^ 3) by field_simp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC]]
  gcongr
  exact integral_variance_integral_discountedReturn_resolvent_le hγ hf hfC x

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

open LMLExplore ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} [IsMarkovKernel κ] {γ : ℝ≥0}
  {f : α → ℝ} {C : ℝ}

/-- **The mean of the discounted return from an initial law**: for `γ < 1`, a bounded measurable
reward `f` and a finite initial measure `μ`, the expected discounted return of the chain with
initial law `μ` is `∫ f d(R_γ(κ) ∘ₘ μ)`. -/
theorem integral_discountedReturn_markovChainLaw (hγ : γ < 1) (hf : Measurable f)
    (hfC : ∀ x, |f x| ≤ C) (μ : Measure α) [IsFiniteMeasure μ] :
    ∫ ω, discountedReturn γ f ω ∂(markovChainLaw μ κ) =
      ∫ y, f y ∂(Kernel.resolvent γ κ ∘ₘ μ) := by
  have := Kernel.isFiniteKernel_resolvent (κ := κ) hγ
  rw [markovChainLaw_eq_comp, Measure.integral_bind κ.markovChainKernel.aemeasurable
      (integrable_of_abs_le (measurable_discountedReturn hγ hf hfC)
        (abs_discountedReturn_le hγ hfC) _),
    Measure.integral_bind (Kernel.resolvent γ κ).aemeasurable (integrable_of_abs_le hf hfC _)]
  simp_rw [Kernel.integral_discountedReturn_markovChainKernel hγ hf hfC]

end MeasureTheory.Measure
