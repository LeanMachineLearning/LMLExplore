/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MeasureTheory.Integral.DominatedConvergence
public import LMLExplore.Probability.Kernel.Resolvent
public import LMLExplore.Probability.Moments.Variance
public import TauCeti.Probability.MarkovChain.MarkovProperty
public import TauCeti.Probability.Moments.Mixture

/-!
# The discounted return of a Markov chain: its mean and its variance

Let `κ` be a Markov kernel on a measurable space `α`, `f : α → ℝ` a bounded measurable reward and
`γ < 1` a discount factor. Along a path `ω : ℕ → α`, the discounted return is
`G ω = ∑' t, γ ^ t * f (ω t)`. Under the law `ℙₓ = κ.markovChainKernel x` of the chain started at
`x`, its mean `V x = ∫ G dℙₓ` is the resolvent `R_γ(κ) f = ∑ t, γ ^ t κ ^ t f` evaluated at `x`,
and its variance satisfies the *total-variance identity* [Sob82], [AMK13]
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

## Main definitions

* `LMLExplore.discountedReturn γ f ω`: the discounted return `∑' t, γ ^ t * f (ω t)` along a path.

## Main statements

* `LMLExplore.abs_discountedReturn_le`: `|G ω| ≤ C / (1 - γ)` for `|f| ≤ C`.
* `LMLExplore.discountedReturn_eq_add_mul_shift`: the first-step decomposition
  `G ω = f (ω 0) + γ G (θ ω)`.
* `ProbabilityTheory.Kernel.integral_discountedReturn_markovChainKernel`: the mean of the
  discounted return from `x` is `∫ f dR_γ(κ)(x)`;
  `MeasureTheory.Measure.integral_discountedReturn_markovChainLaw`: from an initial law `μ`, it is
  `∫ f d(R_γ(κ) ∘ₘ μ)`.
* `ProbabilityTheory.Kernel.variance_discountedReturn_markovChainKernel_eq_add`: the variance
  Bellman equation `Var_x(G) = γ ^ 2 (Var[V; κ x] + ∫ Var_y(G) dκ x)`.
* `ProbabilityTheory.Kernel.variance_discountedReturn_markovChainKernel_eq_integral_resolvent`:
  `Var_x(G) = γ ^ 2 ∫ Var[V; κ y] dR_{γ²}(κ)(x)`.
* `ProbabilityTheory.Kernel.variance_discountedReturn_markovChainKernel`: the total-variance
  identity `Var_x(G) = ∑' t, γ ^ (2 (t + 1)) ∫ Var[V; κ y] d(κ ^ t)(x)`.

## References

* [M. J. Sobel, *The variance of discounted Markov decision processes*, 1982][Sob82]
* [M. G. Azar, R. Munos and H. J. Kappen, *Minimax PAC bounds on the sample complexity of
  reinforcement learning with a generative model*, 2013][AMK13]
* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], Lemma 2.11 (the state-action form of the variance Bellman equation)
-/

public section

open MeasureTheory Set Filter Topology TauCeti.Probability
open scoped ENNReal NNReal

namespace LMLExplore

variable {α : Type*} {mα : MeasurableSpace α} {γ : ℝ≥0} {f : α → ℝ} {C : ℝ}

/-- The *discounted return* `∑' t, γ ^ t * f (ω t)` of a reward function `f : α → ℝ` along a path
`ω : ℕ → α`, with discount factor `γ`. -/
noncomputable def discountedReturn (γ : ℝ≥0) (f : α → ℝ) (ω : ℕ → α) : ℝ :=
  ∑' t, (γ : ℝ) ^ t * f (ω t)

lemma discountedReturn_def (γ : ℝ≥0) (f : α → ℝ) (ω : ℕ → α) :
    discountedReturn γ f ω = ∑' t, (γ : ℝ) ^ t * f (ω t) :=
  (rfl)

/-- For a reward bounded by `C`, the terms of the discounted return are dominated by the geometric
sequence `γ ^ t * C`. -/
private lemma norm_pow_mul_apply_le (hfC : ∀ x, |f x| ≤ C) (ω : ℕ → α) (t : ℕ) :
    ‖(γ : ℝ) ^ t * f (ω t)‖ ≤ (γ : ℝ) ^ t * C := by
  rw [norm_mul, norm_pow, NNReal.norm_eq, Real.norm_eq_abs]
  gcongr
  exact hfC _

/-- For `γ < 1` and a bounded reward, the series defining the discounted return is summable. -/
lemma summable_discountedReturn (hγ : γ < 1) (hfC : ∀ x, |f x| ≤ C) (ω : ℕ → α) :
    Summable fun t ↦ (γ : ℝ) ^ t * f (ω t) :=
  .of_norm_bounded ((summable_geometric_of_lt_one γ.coe_nonneg hγ).mul_right C)
    (norm_pow_mul_apply_le hfC ω)

/-- For `γ < 1` and a reward bounded by `C`, the discounted return is bounded by `C / (1 - γ)`. -/
theorem abs_discountedReturn_le (hγ : γ < 1) (hfC : ∀ x, |f x| ≤ C) (ω : ℕ → α) :
    |discountedReturn γ f ω| ≤ C / (1 - γ) := by
  have h_geom := (hasSum_geometric_of_lt_one γ.coe_nonneg hγ).mul_right C
  rw [← Real.norm_eq_abs, div_eq_inv_mul, discountedReturn_def]
  exact (summable_discountedReturn hγ hfC ω).hasSum.norm_le_of_bounded h_geom
    (norm_pow_mul_apply_le hfC ω)

/-- For `γ < 1` and a bounded measurable reward, the discounted return is a measurable function of
the path. -/
theorem measurable_discountedReturn (hγ : γ < 1) (hf : Measurable f) (hfC : ∀ x, |f x| ≤ C) :
    Measurable (discountedReturn γ f) := by
  refine measurable_of_tendsto_metrizable
    (f := fun n ω ↦ ∑ t ∈ Finset.range n, (γ : ℝ) ^ t * f (ω t)) (fun n ↦ ?_)
    (tendsto_pi_nhds.2 fun ω ↦ (summable_discountedReturn hγ hfC ω).hasSum.tendsto_sum_nat)
  exact Finset.measurable_sum _ fun t _ ↦ (hf.comp (measurable_pi_apply t)).const_mul _

/-- **First-step decomposition of the discounted return**: the return along `ω` is the first
reward plus `γ` times the return along the shifted path `θ ω = (ω (t + 1))ₜ`. -/
theorem discountedReturn_eq_add_mul_shift (hγ : γ < 1) (hfC : ∀ x, |f x| ≤ C) (ω : ℕ → α) :
    discountedReturn γ f ω = f (ω 0) + γ * discountedReturn γ f (shift α ω) := by
  rw [discountedReturn_def, (summable_discountedReturn hγ hfC ω).tsum_eq_zero_add,
    discountedReturn_def, ← tsum_mul_left]
  simp [shift_apply, pow_succ, mul_assoc, mul_left_comm]

end LMLExplore

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

/-! ### The variance of the discounted return -/

/-- **The variance Bellman equation**: for `γ < 1` and a bounded measurable reward `f`, the
variance `W x = Var_x(G)` of the discounted return `G` of the chain started at `x` satisfies
`W x = γ ^ 2 (Var[V; κ x] + ∫ W dκ x)`, where `V y = ∫ G dℙ_y` is the expected discounted return. -/
theorem variance_discountedReturn_markovChainKernel_eq_add (hγ : γ < 1) (hf : Measurable f)
    (hfC : ∀ x, |f x| ≤ C) (x : α) :
    Var[discountedReturn γ f; κ.markovChainKernel x] =
      (γ : ℝ) ^ 2 * (Var[fun y ↦ ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel y); κ x] +
        ∫ y, Var[discountedReturn γ f; κ.markovChainKernel y] ∂(κ x)) := by
  have hG := measurable_discountedReturn hγ hf hfC
  -- Started at `x`, the chain has `x` as its first state.
  have h_eval : (κ.markovChainKernel x).map (fun ω ↦ ω 0) = Measure.dirac x := by
    rw [← map_apply _ (measurable_pi_apply 0), markovChainKernel_map_eval, pow_zero]
    -- The unit of the monoid of kernels `Kernel α α` is `Kernel.id`.
    exact id_apply x
  have h_zero : ∀ᵐ ω ∂(κ.markovChainKernel x), f (ω 0) = f x := by
    have hs : MeasurableSet {y | f y = f x} := measurableSet_eq_fun hf measurable_const
    refine (ae_map_iff (f := fun ω : ℕ → α ↦ ω 0) (measurable_pi_apply 0).aemeasurable hs).1 ?_
    rw [h_eval, ae_dirac_iff hs]
  -- The shifted path is the chain started from `κ x`, a mixture of the laws `ℙ_y`.
  have h_shift : (κ.markovChainKernel x).map (shift α) = κ.markovChainKernel ∘ₘ κ x := by
    rw [markovChainKernel_apply, ← Function.iterate_one (shift α),
      Measure.markovChainLaw_map_shift_iterate, pow_one, Measure.dirac_bind κ.measurable,
      Measure.markovChainLaw_eq_comp]
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
    _ = _ := by
        rw [variance_comp _ (MemLp.of_bound hG.aestronglyMeasurable _
          (.of_forall fun ω ↦ (Real.norm_eq_abs _).trans_le (abs_discountedReturn_le hγ hfC ω))),
          add_comm]

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
  have hGB := abs_discountedReturn_le hγ hfC
  have hV := measurable_integral_discountedReturn_markovChainKernel (κ := κ) hγ hf hfC
  have hVB (y : α) : |∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel y)| ≤ C / (1 - γ) :=
    abs_integral_le_of_abs_le hGB
  -- Both variances are bounded by `(C / (1 - γ)) ^ 2`, the square of the bound on returns.
  have hσB (y : α) :
      |Var[fun z ↦ ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel z); κ y]| ≤
        (C / (1 - γ)) ^ 2 := by
    rw [abs_of_nonneg (variance_nonneg _ _)]
    exact variance_le_sq_of_abs_le hV.aemeasurable (.of_forall hVB)
  have hWB (y : α) : |Var[discountedReturn γ f; κ.markovChainKernel y]| ≤ (C / (1 - γ)) ^ 2 := by
    rw [abs_of_nonneg (variance_nonneg _ _)]
    exact variance_le_sq_of_abs_le hG.aemeasurable (.of_forall hGB)
  have h := eq_integral_resolvent_of_eq_add hγ2
    (f := fun y ↦ (γ : ℝ) ^ 2 *
      Var[fun z ↦ ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel z); κ y])
    (B := (γ : ℝ) ^ 2 * (C / (1 - γ)) ^ 2) (B' := (C / (1 - γ)) ^ 2)
    ((hV.variance_kernel (η := κ)).const_mul _)
    (fun y ↦ by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      gcongr
      exact hσB y)
    (hG.variance_kernel (η := κ.markovChainKernel)) hWB
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
  have hVB (y : α) : |∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel y)| ≤ C / (1 - γ) :=
    abs_integral_le_of_abs_le (abs_discountedReturn_le hγ hfC)
  have hσB (y : α) :
      |Var[fun z ↦ ∫ ω, discountedReturn γ f ω ∂(κ.markovChainKernel z); κ y]| ≤
        (C / (1 - γ)) ^ 2 := by
    rw [abs_of_nonneg (variance_nonneg _ _)]
    exact variance_le_sq_of_abs_le hV.aemeasurable (.of_forall hVB)
  rw [variance_discountedReturn_markovChainKernel_eq_integral_resolvent hγ hf hfC,
    integral_resolvent (integrable_of_abs_le (hV.variance_kernel (η := κ)) hσB _),
    ← tsum_mul_left]
  refine tsum_congr fun t ↦ ?_
  rw [smul_eq_mul, NNReal.coe_pow, ← pow_mul, ← mul_assoc, ← _root_.pow_add, mul_add, mul_one,
    add_comm]

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
