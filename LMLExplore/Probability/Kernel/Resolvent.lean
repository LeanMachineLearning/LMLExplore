/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.Integral.BoundedMeasurable
public import LMLExplore.Probability.Kernel.Composition.Comp
public import LMLExplore.Probability.Kernel.Operator
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Moments.Variance
import LMLExplore.Analysis.Convex.Integral
import Mathlib.Analysis.Complex.ExponentialBounds
import LMLExplore.Probability.Moments.Variance

/-!
# The resolvent of a kernel

For a kernel `κ : Kernel α α` and a discount factor `γ : ℝ≥0`, the resolvent of `κ` is the kernel
`R_γ(κ) = ∑ n, γ ^ n κ ^ n`: the measure `resolvent γ κ x` gives to a set `s` the expected
discounted number of visits to `s` of the Markov chain with kernel `κ` started at `x`,
`∑' n, γ ^ n * (κ ^ n) x s`. Acting on functions, it maps `f` to
`x ↦ ∫ y, f y ∂(resolvent γ κ x) = ∑' n, γ ^ n * ∫ y, f y ∂((κ ^ n) x)`, the expected discounted sum
of the values of `f` along the chain. The resolvent of an s-finite kernel is s-finite, and for a
Markov kernel and `γ < 1`, it is a finite kernel of mass `(1 - γ)⁻¹`.

For every kernel and every `γ`, the resolvent satisfies, as measures,
`resolvent γ κ x = δ_x + γ • (resolvent γ κ ∘ₖ κ) x = δ_x + γ • (κ ∘ₖ resolvent γ κ) x`, which
are the operator identities `R_γ = 1 + γ κ R_γ = 1 + γ R_γ κ`. Whenever the resolvent is a finite
kernel, as it is for a Markov kernel and `γ < 1`, its action on bounded measurable functions
(`Kernel.integralCLM`) is therefore the inverse of `1 - γ κ` in the Banach algebra of continuous
linear maps of `boundedMeasurable α`. Consequently:
* for a Markov kernel, `γ < 1` and a bounded measurable `f`, the function `u = R_γ f` is the
  unique bounded measurable solution of the equation `u = f + γ κ u`;
* for a measure `μ`, the measure `ν = μ.bind R_γ` (written `resolvent γ κ ∘ₘ μ`) satisfies the
  flow equation `ν = μ + γ • ν.bind κ` for every kernel and every `γ`; for a Markov kernel and
  `γ < 1`, it is the unique finite measure satisfying it.

Uniqueness also compares resolvents: for every bounded measurable `y`, `R_γ f - y` is the resolvent
`R_γ (f + γ κ y - y)` of the residual of `y` in the equation `u = f + γ κ u` (the
performance-difference identity). For a second Markov kernel `κ'` and a second bounded measurable
`f'`, applying it to `κ'`, `f'` and `y = R_γ(κ) f` gives the simulation identity with two rewards
`R_γ(κ) f - R_γ(κ') f' = R_γ(κ') ((f - f') + γ (κ - κ') R_γ(κ) f)`. Since the
resolvent is a positive operator, the performance-difference identity also compares `R_γ f` with
sub- and supersolutions of `u = f + γ κ u`.

The comparison with supersolutions bounds the resolvent of the one-step variances
`Var[V; κ y] = κ (V ^ 2) (y) - (κ V) (y) ^ 2` of a nonnegative resolvent `V = R_γ f ≤ B`: the
function `2 B V - V ^ 2` is a supersolution for `γ ^ 2 Var_κ(V)`, so that
`γ ^ 2 R_γ Var_κ(V) ≤ B ^ 2`, and Jensen's inequality for the square root gives
`R_γ √Var_κ(V) ≤ B / (γ √(1 - γ))` [LWCGC24, Lemma 11]. Bounds of this kind control the error
`γ R_γ(κ') (κ' - κ) V` of the simulation identity when the deviation `(κ' - κ) V` is bounded by
a multiple of the standard deviation `√Var_κ(V)`, as Bernstein's inequality bounds it for an
empirical kernel `κ'`. Iterating this control along the functions `V 0 = R_γ f` and
`V (l + 1) = R_γ √Var_κ(V l)`, each bounded through Lemma 11 by the previous one, compares
`R_γ(κ') f` with `R_γ(κ) f` up to `3 C √(ε / (1 - γ) ^ 3)` for `0 ≤ f ≤ C`: for `0 < γ < 1` and
`9 ε ≤ 1 - γ`, as soon as `κ'` deviates from `κ` by `√(ε Var_κ(V l))` plus a lower-order term on
the levels `l ≤ m`, for some `m ≥ log (1 - γ)⁻¹` [LWCGC24, Lemma 2].

In a Markov decision process, the value of a stationary policy is the resolvent of the state
kernel of the policy applied to its reward, and the discounted occupancy measure of a stationary
policy is, up to the factor `1 - γ`, the image of the initial state-action law by the resolvent of
the state-action kernel. The two characterizations above are the evaluation equation and the flow
equation of these objects.

## Main definitions

* `ProbabilityTheory.Kernel.resolvent γ κ`: the resolvent kernel `∑ n, γ ^ n κ ^ n`.

## Main statements

* `ProbabilityTheory.Kernel.lintegral_resolvent`, `ProbabilityTheory.Kernel.integral_resolvent`:
  the integral against `resolvent γ κ x` is the discounted series of the integrals against the
  powers of `κ`.
* `ProbabilityTheory.Kernel.resolvent_apply_univ`: for a Markov kernel, the mass of the resolvent
  is `(1 - γ)⁻¹`; `ProbabilityTheory.Kernel.isFiniteKernel_resolvent`: it is a finite kernel for
  `γ < 1`. The resolvent of an s-finite kernel is s-finite (an instance).
* `ProbabilityTheory.Kernel.dirac_add_resolvent_comp_apply`,
  `ProbabilityTheory.Kernel.dirac_add_comp_resolvent_apply`: the resolvent identities
  `R_γ = 1 + γ κ R_γ = 1 + γ R_γ κ`.
* `ProbabilityTheory.Kernel.one_sub_smul_integralCLM_mul_integralCLM_resolvent`,
  `ProbabilityTheory.Kernel.integralCLM_resolvent_mul_one_sub_smul_integralCLM`: the resolvent
  identities as operators, `(1 - γ κ) R_γ = R_γ (1 - γ κ) = 1`, when the resolvent is finite.
* `ProbabilityTheory.Kernel.isUnit_one_sub_smul_integralCLM`,
  `ProbabilityTheory.Kernel.ringInverse_one_sub_smul_integralCLM`: `1 - γ κ` is invertible, with
  inverse `R_γ = (1 - γ κ)⁻¹`; `ProbabilityTheory.Kernel.eq_integralCLM_resolvent_iff`: `R_γ f` is
  the only bounded measurable solution of `u = f + γ κ u`.
* `ProbabilityTheory.Kernel.integral_resolvent_eq_add`,
  `ProbabilityTheory.Kernel.eq_integral_resolvent_of_eq_add`: for a Markov kernel and `γ < 1`,
  `R_γ f` is the unique bounded measurable solution of `u = f + γ κ u`.
* `ProbabilityTheory.Kernel.abs_integral_resolvent_le`,
  `ProbabilityTheory.Kernel.abs_mul_integral_resolvent_le`,
  `ProbabilityTheory.Kernel.abs_integral_resolvent_add_mul_le`,
  `ProbabilityTheory.Kernel.le_integral_resolvent`: for a Markov kernel and `γ < 1`,
  `|R_γ f| ≤ sup |f| / (1 - γ)`, `|γ R_γ f| ≤ γ sup |f| / (1 - γ)`,
  `|R_γ (f + γ g)| ≤ sup |f| / (1 - γ) + γ sup |g| / (1 - γ)`, and `f ≤ R_γ f` for `f ≥ 0`.
* `ProbabilityTheory.Kernel.integral_resolvent_sub_eq_integral_resolvent`: the
  performance-difference identity `R_γ f - y = R_γ (f + γ κ y - y)`.
* `ProbabilityTheory.Kernel.integral_resolvent_le_of_add_le`,
  `ProbabilityTheory.Kernel.le_integral_resolvent_of_le_add`: comparison with sub- and
  supersolutions, `f + γ κ u ≤ u → R_γ f ≤ u` and `u ≤ f + γ κ u → u ≤ R_γ f`.
* `ProbabilityTheory.Kernel.integral_resolvent_sub_integral_resolvent`: the simulation identity
  with two rewards `R_γ(κ) f - R_γ(κ') f' = R_γ(κ') ((f - f') + γ (κ - κ') R_γ(κ) f)`.
* `ProbabilityTheory.Kernel.abs_integral_resolvent_sub_integral_resolvent_le`:
  the simulation bound `|R_γ(κ') f - R_γ(κ) f| ≤ γ R_γ(κ') e` when `|(κ' - κ) R_γ(κ) f| ≤ e`.
* `ProbabilityTheory.Kernel.mul_integral_variance_integral_resolvent_le`,
  `ProbabilityTheory.Kernel.integral_sqrt_variance_integral_resolvent_le`: for a nonnegative
  bounded measurable `f` with `V = R_γ f ≤ B`, `γ ^ 2 R_γ Var_κ(V) ≤ 2 B V - V ^ 2` and
  `R_γ √Var_κ(V) ≤ B / (γ √(1 - γ))` [LWCGC24, Lemma 11].
* `ProbabilityTheory.Kernel.measurable_of_eq_integral_resolvent_sqrt_variance`,
  `ProbabilityTheory.Kernel.mem_Icc_of_eq_integral_resolvent_sqrt_variance`: the iterated
  resolvents `V (l + 1) = R_γ √Var_κ(V l)` of the one-step standard deviations of `V 0 = R_γ f` are
  measurable, with `0 ≤ V l ≤ C / ((1 - γ) (γ √(1 - γ)) ^ l)` for `0 ≤ f ≤ C`.
* `ProbabilityTheory.Kernel.abs_integral_resolvent_sub_integral_resolvent_le_of_abs_sub_le`: the
  comparison of the resolvents of two kernels with Bernstein-type deviations on these functions
  [LWCGC24, Lemma 2].
* `MeasureTheory.Measure.resolvent_comp_eq_add`: for every kernel and every `γ`,
  `resolvent γ κ ∘ₘ μ` solves the flow equation `ν = μ + γ • (κ ∘ₘ ν)`;
  `MeasureTheory.Measure.eq_resolvent_comp_of_eq_add`: for a Markov kernel and `γ < 1`, it is the
  unique finite solution. `MeasureTheory.Measure.eq_sum_range_add_of_eq_add` unfolds the flow
  equation `n` times, for every kernel.

## References

* D. Revuz, *Markov chains*, North-Holland, 2nd edition, 1984, Chapter 2
* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §6.1
* [A. Agarwal, S. M. Kakade, J. D. Lee and G. Mahajan, *On the theory of policy gradient methods:
  optimality, approximation, and distribution shift*, 2021][AKLM21], Lemma 3.2
* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], Lemma 2.2
* [G. Li, Y. Wei, Y. Chi, Y. Gu and Y. Chen, *Breaking the sample size barrier in model-based
  reinforcement learning with a generative model*, Operations Research, 2024][LWCGC24], Lemmas 2
  and 11 (arXiv:2005.12900)
-/

public section

open MeasureTheory Set Filter Topology LMLExplore
open scoped ENNReal NNReal lp

namespace ProbabilityTheory.Kernel

variable {α E : Type*} {mα : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {γ : ℝ≥0} {κ : Kernel α α}

/-! ### Definition -/

/-- The resolvent `R_γ(κ) = ∑ n, γ ^ n κ ^ n` of a kernel `κ : Kernel α α`: the measure
`resolvent γ κ x` gives to a measurable set `s` the mass `∑' n, γ ^ n * (κ ^ n) x s`, the expected
discounted number of visits to `s` of the Markov chain with kernel `κ` started at `x`. -/
noncomputable def resolvent (γ : ℝ≥0) (κ : Kernel α α) : Kernel α α where
  toFun x := Measure.sum fun n ↦ ((γ : ℝ≥0∞) ^ n) • (κ ^ n) x
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs ↦ by
    simp_rw [Measure.sum_apply _ hs, smul_apply, smul_eq_mul]
    exact Measurable.tsum fun n ↦ ((κ ^ n).measurable_coe hs).const_mul _

lemma resolvent_apply (γ : ℝ≥0) (κ : Kernel α α) (x : α) :
    resolvent γ κ x = Measure.sum fun n ↦ ((γ : ℝ≥0∞) ^ n) • (κ ^ n) x :=
  (rfl)

lemma resolvent_apply' (γ : ℝ≥0) (κ : Kernel α α) (x : α) {s : Set α} (hs : MeasurableSet s) :
    resolvent γ κ x s = ∑' n, (γ : ℝ≥0∞) ^ n * (κ ^ n) x s := by
  simp [resolvent_apply, Measure.sum_apply _ hs]

/-- The resolvent of an s-finite kernel is an s-finite kernel. -/
instance [IsSFiniteKernel κ] : IsSFiniteKernel (resolvent γ κ) := by
  have h : resolvent γ κ =
      Kernel.sum fun n ↦ withDensity (κ ^ n) fun _ _ ↦ ((γ ^ n : ℝ≥0) : ℝ≥0∞) := by
    ext x : 1
    rw [resolvent_apply, Kernel.sum_apply]
    congr with n : 1
    rw [Kernel.withDensity_apply _ (by fun_prop), withDensity_const, ENNReal.coe_pow]
  rw [h]
  infer_instance

/-- The lower Lebesgue integral against the resolvent is the discounted series of the integrals
against the powers of the kernel. -/
lemma lintegral_resolvent (γ : ℝ≥0) (κ : Kernel α α) (x : α) (f : α → ℝ≥0∞) :
    ∫⁻ y, f y ∂(resolvent γ κ x) = ∑' n, (γ : ℝ≥0∞) ^ n * ∫⁻ y, f y ∂((κ ^ n) x) := by
  simp [resolvent_apply, lintegral_sum_measure, lintegral_smul_measure]

/-- The integral of a function `f` integrable against the resolvent is the discounted series
`∑' n, γ ^ n • ∫ f d(κ ^ n x)`. -/
theorem integral_resolvent {f : α → E} {x : α} (hf : Integrable f (resolvent γ κ x)) :
    ∫ y, f y ∂(resolvent γ κ x) = ∑' n, ((γ : ℝ) ^ n) • ∫ y, f y ∂((κ ^ n) x) := by
  rw [resolvent_apply] at hf ⊢
  simp [integral_sum_measure hf, integral_smul_measure]

/-- The integral of a measurable function against the resolvent is a measurable function of the
starting point. -/
theorem measurable_integral_resolvent {f : α → ℝ} (hf : Measurable f) :
    Measurable fun x ↦ ∫ y, f y ∂(resolvent γ κ x) :=
  (hf.stronglyMeasurable.integral_kernel (κ := resolvent γ κ)).measurable

/-- For `γ = 0`, the resolvent is the identity kernel. -/
@[simp]
lemma resolvent_zero (κ : Kernel α α) : resolvent 0 κ = Kernel.id := by
  ext x s hs
  rw [resolvent_apply' _ _ _ hs, tsum_eq_single 0 fun n hn ↦ by simp [hn]]
  simp [one_def]

/-- The measure `resolvent γ κ x` dominates the Dirac mass at `x`. -/
lemma dirac_le_resolvent (γ : ℝ≥0) (κ : Kernel α α) (x : α) :
    Measure.dirac x ≤ resolvent γ κ x := by
  refine Measure.le_iff.2 fun s hs ↦ ?_
  rw [resolvent_apply' _ _ _ hs]
  refine le_trans ?_ (le_tsum _ 0)
  simp [one_def, Kernel.id_apply]

/-! ### The resolvent identities -/

/-- The resolvent identity `R_γ = 1 + γ κ R_γ`, as measures: the resolvent from `x` is the Dirac
mass at `x` plus `γ` times the resolvent from the next state. -/
theorem dirac_add_resolvent_comp_apply (γ : ℝ≥0) (κ : Kernel α α) (x : α) :
    Measure.dirac x + (γ : ℝ≥0∞) • (resolvent γ κ ∘ₖ κ) x = resolvent γ κ x := by
  ext s hs
  have h (n : ℕ) : Measurable fun y ↦ (γ : ℝ≥0∞) ^ n * (κ ^ n) y s :=
    ((κ ^ n).measurable_coe hs).const_mul _
  rw [add_apply, smul_apply, smul_eq_mul, comp_apply' _ _ _ hs,
    resolvent_apply' _ _ _ hs, tsum_eq_zero_add' CompleteLattice.summable]
  simp_rw [resolvent_apply' _ _ _ hs]
  rw [lintegral_tsum fun n ↦ (h n).aemeasurable, ← ENNReal.tsum_mul_left]
  congr 1
  · simp [one_def, Kernel.id_apply]
  · refine tsum_congr fun n ↦ ?_
    rw [lintegral_const_mul _ ((κ ^ n).measurable_coe hs), pow_succ, pow_succ, mul_eq_comp,
      comp_apply' _ _ _ hs]
    ring

/-- The resolvent identity `R_γ = 1 + γ R_γ κ`, as measures: the resolvent from `x` is the Dirac
mass at `x` plus `γ` times the image of the resolvent from `x` by one step of `κ`. -/
theorem dirac_add_comp_resolvent_apply (γ : ℝ≥0) (κ : Kernel α α) (x : α) :
    Measure.dirac x + (γ : ℝ≥0∞) • (κ ∘ₖ resolvent γ κ) x = resolvent γ κ x := by
  ext s hs
  rw [add_apply, smul_apply, smul_eq_mul, comp_apply' _ _ _ hs,
    lintegral_resolvent, resolvent_apply' _ _ _ hs, ← ENNReal.tsum_mul_left]
  conv_rhs => rw [tsum_eq_zero_add' CompleteLattice.summable]
  congr 1
  · simp [one_def, Kernel.id_apply]
  · refine tsum_congr fun n ↦ ?_
    rw [pow_succ_apply_eq_lintegral _ _ _ hs, pow_succ]
    ring

/-! ### The resolvent as the inverse of `1 - γ κ` -/

section Operator

variable [IsFiniteKernel κ] [IsFiniteKernel (resolvent γ κ)]

omit [IsFiniteKernel κ] in
/-- A measure identity `δ_x + γ • η x = resolvent γ κ x` as an identity of operators on bounded
measurable functions, `R_γ = 1 + γ η`. -/
private lemma integralCLM_resolvent_eq_add (η : Kernel α α) [IsFiniteKernel η]
    (h : ∀ x, Measure.dirac x + (γ : ℝ≥0∞) • η x = resolvent γ κ x) (f : boundedMeasurable α) :
    (resolvent γ κ).integralCLM f = f + (γ : ℝ) • η.integralCLM f := by
  ext x
  simp only [boundedMeasurable.coeFn_add, boundedMeasurable.coeFn_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, integralCLM_apply]
  rw [← h x, integral_add_measure (boundedMeasurable.integrable f _)
    ((boundedMeasurable.integrable f _).smul_measure ENNReal.coe_ne_top),
    integral_dirac' _ _ (boundedMeasurable.measurable f).stronglyMeasurable, integral_smul_measure]
  simp

/-- The resolvent identity `R_γ = 1 + γ κ R_γ` as operators on bounded measurable functions:
`(1 - γ κ) R_γ = 1`. -/
theorem one_sub_smul_integralCLM_mul_integralCLM_resolvent :
    (1 - (γ : ℝ) • κ.integralCLM) * (resolvent γ κ).integralCLM = 1 := by
  ext1 f
  have h := integralCLM_resolvent_eq_add _ (dirac_add_resolvent_comp_apply γ κ) f
  rw [integralCLM_comp, ContinuousLinearMap.comp_apply] at h
  rw [mul_apply_eq_comp, sub_apply, one_apply_eq_self, smul_apply]
  exact sub_eq_iff_eq_add.2 h

/-- The resolvent identity `R_γ = 1 + γ R_γ κ` as operators on bounded measurable functions:
`R_γ (1 - γ κ) = 1`. -/
theorem integralCLM_resolvent_mul_one_sub_smul_integralCLM :
    (resolvent γ κ).integralCLM * (1 - (γ : ℝ) • κ.integralCLM) = 1 := by
  ext1 f
  have h := integralCLM_resolvent_eq_add _ (dirac_add_comp_resolvent_apply γ κ) f
  rw [integralCLM_comp, ContinuousLinearMap.comp_apply] at h
  rw [mul_apply_eq_comp, sub_apply, one_apply_eq_self, smul_apply,
    ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul]
  exact sub_eq_iff_eq_add.2 h

/-- When the resolvent of `κ` is a finite kernel (for instance for a Markov kernel and `γ < 1`,
`isFiniteKernel_resolvent`), the operator `1 - γ κ` on bounded measurable functions is
invertible. -/
theorem isUnit_one_sub_smul_integralCLM : IsUnit (1 - (γ : ℝ) • κ.integralCLM) :=
  isUnit_iff_exists.2 ⟨_, one_sub_smul_integralCLM_mul_integralCLM_resolvent,
    integralCLM_resolvent_mul_one_sub_smul_integralCLM⟩

/-- **The resolvent is the inverse of `1 - γ κ`**: when the resolvent of `κ` is a finite kernel
(for instance for a Markov kernel and `γ < 1`, `isFiniteKernel_resolvent`), its action on bounded
measurable functions is the inverse of `1 - γ κ`, `R_γ = (1 - γ κ)⁻¹`. -/
theorem ringInverse_one_sub_smul_integralCLM :
    Ring.inverse (1 - (γ : ℝ) • κ.integralCLM) = (resolvent γ κ).integralCLM := by
  simpa using Ring.inverse_unit (M₀ := boundedMeasurable α →L[ℝ] boundedMeasurable α)
    ⟨_, _, one_sub_smul_integralCLM_mul_integralCLM_resolvent,
      integralCLM_resolvent_mul_one_sub_smul_integralCLM⟩

/-- **The resolvent equation**: when the resolvent of `κ` is a finite kernel, a bounded measurable
`u` is `R_γ f` if and only if it solves `u = f + γ κ u`. -/
theorem eq_integralCLM_resolvent_iff {f u : boundedMeasurable α} :
    u = (resolvent γ κ).integralCLM f ↔ u = f + (γ : ℝ) • κ.integralCLM u := by
  have h : u - (γ : ℝ) • κ.integralCLM u = (1 - (γ : ℝ) • κ.integralCLM) u := by
    simp
  rw [← sub_eq_iff_eq_add, h]
  constructor
  · rintro rfl
    rw [← mul_apply_eq_comp, one_sub_smul_integralCLM_mul_integralCLM_resolvent,
      one_apply_eq_self]
  · intro h
    rw [← h, ← mul_apply_eq_comp, integralCLM_resolvent_mul_one_sub_smul_integralCLM,
      one_apply_eq_self]

end Operator

/-! ### Mass and finiteness -/

section Markov

variable [IsMarkovKernel κ]

variable (γ κ) in
/-- The resolvent of a Markov kernel has mass `(1 - γ)⁻¹`. -/
@[simp]
lemma resolvent_apply_univ (x : α) : resolvent γ κ x univ = (1 - (γ : ℝ≥0∞))⁻¹ := by
  simp [resolvent_apply' _ _ _ MeasurableSet.univ, ENNReal.tsum_geometric]

/-- For `γ < 1`, the resolvent of a Markov kernel is a finite kernel. -/
lemma isFiniteKernel_resolvent (hγ : γ < 1) : IsFiniteKernel (resolvent γ κ) := by
  refine ⟨⟨(1 - (γ : ℝ≥0∞))⁻¹, ?_, fun x ↦ (resolvent_apply_univ γ κ x).le⟩⟩
  rw [ENNReal.inv_lt_top, tsub_pos_iff_lt]
  exact_mod_cast hγ

/-- For `γ < 1`, the resolvent of a Markov kernel has real mass `(1 - γ)⁻¹`. -/
lemma measureReal_resolvent_univ (hγ : γ < 1) (x : α) :
    (resolvent γ κ x).real univ = (1 - (γ : ℝ))⁻¹ := by
  simp [measureReal_def, ENNReal.toReal_inv, ENNReal.toReal_sub_of_le, hγ.le]

/-! ### The resolvent acting on bounded functions -/

/-- For `γ < 1`, a function bounded by `B` has an integral against the resolvent of a Markov
kernel bounded by `B / (1 - γ)`: `|R_γ f| ≤ sup |f| / (1 - γ)`. -/
theorem abs_integral_resolvent_le (hγ : γ < 1) {f : α → ℝ} {B : ℝ} (hfB : ∀ y, |f y| ≤ B)
    (x : α) : |∫ y, f y ∂(resolvent γ κ x)| ≤ B / (1 - γ) := by
  have := isFiniteKernel_resolvent (κ := κ) hγ
  rw [← Real.norm_eq_abs, div_eq_mul_inv, ← measureReal_resolvent_univ (κ := κ) hγ x]
  exact norm_integral_le_of_norm_le_const <| .of_forall fun y ↦
    (Real.norm_eq_abs _).trans_le (hfB y)

/-- For `γ < 1`, a function bounded by `B` has a discounted integral against the resolvent of a
Markov kernel bounded by `γ B / (1 - γ)`: `|γ R_γ f| ≤ γ sup |f| / (1 - γ)`. -/
theorem abs_mul_integral_resolvent_le (hγ : γ < 1) {f : α → ℝ} {B : ℝ} (hfB : ∀ y, |f y| ≤ B)
    (x : α) : |γ * ∫ y, f y ∂(resolvent γ κ x)| ≤ γ * B / (1 - γ) := by
  rw [abs_mul, NNReal.abs_eq, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (abs_integral_resolvent_le hγ hfB x) γ.coe_nonneg

/-- For `γ < 1`, if `f` is bounded by `B` and `g` by `B'`, the integral of `f + γ g` against the
resolvent of a Markov kernel is bounded by `B / (1 - γ) + γ B' / (1 - γ)`:
`|R_γ (f + γ g)| ≤ sup |f| / (1 - γ) + γ sup |g| / (1 - γ)`. -/
theorem abs_integral_resolvent_add_mul_le (hγ : γ < 1) {f g : α → ℝ} {B B' : ℝ}
    (hfB : ∀ y, |f y| ≤ B) (hgB : ∀ y, |g y| ≤ B') (x : α) :
    |∫ y, (f y + γ * g y) ∂(resolvent γ κ x)| ≤ B / (1 - γ) + γ * B' / (1 - γ) := by
  rw [← add_div]
  refine abs_integral_resolvent_le hγ (fun y ↦ (abs_add_le _ _).trans (add_le_add (hfB y) ?_)) x
  rw [abs_mul, NNReal.abs_eq]
  exact mul_le_mul_of_nonneg_left (hgB y) γ.coe_nonneg

/-- The resolvent equation `R_γ f = f + γ κ R_γ f`: for `γ < 1` and a bounded measurable `f`, the
function `u = R_γ f` solves `u = f + γ κ u`. -/
theorem integral_resolvent_eq_add (hγ : γ < 1) {f : α → ℝ} {B : ℝ} (hf : Measurable f)
    (hfB : ∀ y, |f y| ≤ B) (x : α) :
    ∫ y, f y ∂(resolvent γ κ x) =
      f x + γ * ∫ y, (∫ z, f z ∂(resolvent γ κ y)) ∂(κ x) := by
  have := isFiniteKernel_resolvent (κ := κ) hγ
  have hint : Integrable f (resolvent γ κ x) := integrable_of_abs_le hf hfB _
  rw [← dirac_add_resolvent_comp_apply] at hint
  conv_lhs => rw [← dirac_add_resolvent_comp_apply]
  rw [integral_add_measure (hint.mono_measure (Measure.le_add_right le_rfl))
    (hint.mono_measure (Measure.le_add_left le_rfl)), integral_dirac' _ _ hf.stronglyMeasurable,
    integral_smul_measure, integral_comp (integrable_of_abs_le hf hfB _)]
  simp

/-- **Uniqueness of the solution of the resolvent equation**: for `γ < 1`, if a bounded measurable
`u` solves `u = f + γ κ u` for a bounded measurable `f`, then `u = R_γ f`. -/
theorem eq_integral_resolvent_of_eq_add (hγ : γ < 1) {f u : α → ℝ} {B B' : ℝ} (hf : Measurable f)
    (hfB : ∀ y, |f y| ≤ B) (hu : Measurable u) (huB : ∀ y, |u y| ≤ B')
    (h : ∀ x, u x = f x + γ * ∫ y, u y ∂(κ x)) :
    u = fun x ↦ ∫ y, f y ∂(resolvent γ κ x) := by
  have := isFiniteKernel_resolvent (κ := κ) hγ
  set F := boundedMeasurable.mk f hf ⟨B, forall_mem_range.2 hfB⟩
  set U := boundedMeasurable.mk u hu ⟨B', forall_mem_range.2 huB⟩
  have hF : ⇑(F : ℓ^∞(α, ℝ)) = f := boundedMeasurable.coeFn_mk ..
  have hU : ⇑(U : ℓ^∞(α, ℝ)) = u := boundedMeasurable.coeFn_mk ..
  have hUF : U = (resolvent γ κ).integralCLM F := eq_integralCLM_resolvent_iff.2 <| by
    ext x
    simp only [boundedMeasurable.coeFn_add, boundedMeasurable.coeFn_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, integralCLM_apply, hF, hU]
    exact h x
  ext x
  rw [← hU, hUF, integralCLM_apply, hF]

/-- The resolvent of a Markov kernel dominates the identity on nonnegative functions: for `γ < 1`
and a nonnegative bounded measurable `f`, `f ≤ R_γ f`. -/
theorem le_integral_resolvent (hγ : γ < 1) {f : α → ℝ} {B : ℝ} (hf : Measurable f)
    (hfB : ∀ y, |f y| ≤ B) (hf₀ : 0 ≤ f) (x : α) : f x ≤ ∫ y, f y ∂(resolvent γ κ x) := by
  have := isFiniteKernel_resolvent (κ := κ) hγ
  rw [← integral_dirac' f x hf.stronglyMeasurable]
  exact integral_mono_measure (dirac_le_resolvent γ κ x) (.of_forall hf₀)
    (integrable_of_abs_le hf hfB _)

/-! ### Resolvent identities for differences -/

/-- **The performance-difference identity** `R_γ f - y = R_γ (f + γ κ y - y)`: for `γ < 1` and
bounded measurable `f` and `y`, the function `R_γ f` differs from `y` by the resolvent of the
residual of `y` in the equation `u = f + γ κ u`. -/
theorem integral_resolvent_sub_eq_integral_resolvent (hγ : γ < 1) {f y : α → ℝ} {B B' : ℝ}
    (hf : Measurable f) (hfB : ∀ z, |f z| ≤ B) (hy : Measurable y) (hyB : ∀ z, |y z| ≤ B')
    (x : α) :
    ∫ z, f z ∂(resolvent γ κ x) - y x =
      ∫ z, (f z + γ * ∫ w, y w ∂(κ z) - y z) ∂(resolvent γ κ x) := by
  have hR := measurable_integral_resolvent (γ := γ) (κ := κ) hf
  have hRB := abs_integral_resolvent_le (κ := κ) hγ hfB
  have hκy : Measurable fun z ↦ ∫ w, y w ∂(κ z) :=
    (hy.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  have hgB (z : α) : |f z + γ * ∫ w, y w ∂(κ z) - y z| ≤ B + γ * B' + B' := by
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (hfB z) ?_))
      (hyB z))
    rw [abs_mul, NNReal.abs_eq]
    exact mul_le_mul_of_nonneg_left (abs_integral_le_of_abs_le hyB) γ.coe_nonneg
  -- `u = R_γ f - y` solves `u = (f + γ κ y - y) + γ κ u`, hence is the resolvent of that residual.
  refine congrFun (eq_integral_resolvent_of_eq_add hγ ((hf.add (hκy.const_mul _)).sub hy) hgB
    (u := fun x ↦ ∫ z, f z ∂(resolvent γ κ x) - y x) (hR.sub hy)
    (fun z ↦ (abs_sub _ _).trans (add_le_add (hRB z) (hyB z))) fun x ↦ ?_) x
  rw [integral_sub (integrable_of_abs_le hR hRB _) (integrable_of_abs_le hy hyB _),
    integral_resolvent_eq_add hγ hf hfB x, Pi.sub_apply, Pi.add_apply]
  ring

/-- **Comparison with supersolutions of the resolvent equation**: for `γ < 1` and bounded
measurable `f`, a bounded measurable `u` with `f + γ κ u ≤ u` dominates `R_γ f`. -/
theorem integral_resolvent_le_of_add_le (hγ : γ < 1) {f u : α → ℝ} {B B' : ℝ}
    (hf : Measurable f) (hfB : ∀ z, |f z| ≤ B) (hu : Measurable u) (huB : ∀ z, |u z| ≤ B')
    (h : ∀ z, f z + γ * ∫ w, u w ∂(κ z) ≤ u z) (x : α) :
    ∫ z, f z ∂(resolvent γ κ x) ≤ u x := by
  rw [← sub_nonpos, integral_resolvent_sub_eq_integral_resolvent hγ hf hfB hu huB]
  exact integral_nonpos fun z ↦ sub_nonpos.2 (h z)

/-- **Comparison with subsolutions of the resolvent equation**: for `γ < 1` and bounded measurable
`f`, a bounded measurable `u` with `u ≤ f + γ κ u` is dominated by `R_γ f`. -/
theorem le_integral_resolvent_of_le_add (hγ : γ < 1) {f u : α → ℝ} {B B' : ℝ}
    (hf : Measurable f) (hfB : ∀ z, |f z| ≤ B) (hu : Measurable u) (huB : ∀ z, |u z| ≤ B')
    (h : ∀ z, u z ≤ f z + γ * ∫ w, u w ∂(κ z)) (x : α) :
    u x ≤ ∫ z, f z ∂(resolvent γ κ x) := by
  rw [← sub_nonneg, integral_resolvent_sub_eq_integral_resolvent hγ hf hfB hu huB]
  exact integral_nonneg fun z ↦ sub_nonneg.2 (h z)

/-- **The simulation identity with two rewards**
`R_γ(κ) f - R_γ(κ') f' = R_γ(κ') ((f - f') + γ (κ - κ') R_γ(κ) f)`: for Markov kernels `κ` and
`κ'`, `γ < 1` and bounded measurable `f` and `f'`, the discounted sums of `f` along the chain with
kernel `κ` and of `f'` along the chain with kernel `κ'` differ by the resolvent of `κ'` applied to
the difference of the rewards plus the discounted one-step difference of the kernels, acting on the
discounted sum of `f` along the chain with kernel `κ`. -/
theorem integral_resolvent_sub_integral_resolvent (κ' : Kernel α α) [IsMarkovKernel κ']
    (hγ : γ < 1) {f f' : α → ℝ} {B B' : ℝ} (hf : Measurable f) (hfB : ∀ z, |f z| ≤ B)
    (hf' : Measurable f') (hfB' : ∀ z, |f' z| ≤ B') (x : α) :
    ∫ z, f z ∂(resolvent γ κ x) - ∫ z, f' z ∂(resolvent γ κ' x) =
      ∫ z, (f z - f' z + γ * (∫ w, (∫ y, f y ∂(resolvent γ κ w)) ∂(κ z) -
        ∫ w, (∫ y, f y ∂(resolvent γ κ w)) ∂(κ' z))) ∂(resolvent γ κ' x) := by
  have hR := measurable_integral_resolvent (γ := γ) (κ := κ) hf
  have hRB := abs_integral_resolvent_le (κ := κ) hγ hfB
  -- the performance-difference identity for `κ'`, `f'` and `y = R_γ(κ) f`
  rw [← neg_sub, integral_resolvent_sub_eq_integral_resolvent hγ hf' hfB' hR hRB,
    ← integral_neg]
  congr with z
  rw [integral_resolvent_eq_add (κ := κ) hγ hf hfB z]
  ring
/-- **The simulation bound**: for Markov kernels `κ` and `κ'`, `γ < 1` and a bounded measurable
`f`, if the one-step deviation `|κ' V - κ V|` of `V = R_γ(κ) f` is bounded by a function `e`
integrable against `R_γ(κ') x`, then `|R_γ(κ') f - R_γ(κ) f| ≤ γ R_γ(κ') e` at `x`. -/
theorem abs_integral_resolvent_sub_integral_resolvent_le
    (κ' : Kernel α α) [IsMarkovKernel κ'] (hγ : γ < 1) {f e : α → ℝ} {B : ℝ} (hf : Measurable f)
    (hfB : ∀ z, |f z| ≤ B) {x : α} (he : Integrable e (resolvent γ κ' x))
    (h : ∀ z, |∫ w, (∫ y, f y ∂(resolvent γ κ w)) ∂(κ' z) -
      ∫ w, (∫ y, f y ∂(resolvent γ κ w)) ∂(κ z)| ≤ e z) :
    |∫ z, f z ∂(resolvent γ κ' x) - ∫ z, f z ∂(resolvent γ κ x)| ≤
      γ * ∫ z, e z ∂(resolvent γ κ' x) := by
  rw [abs_sub_comm, integral_resolvent_sub_integral_resolvent κ' hγ hf hfB hf hfB x,
    ← integral_const_mul]
  simp_rw [sub_self, zero_add]
  refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
    (.of_forall fun _ ↦ abs_nonneg _) (he.const_mul _) (.of_forall fun z ↦ ?_))
  dsimp only
  rw [abs_mul, NNReal.abs_eq, abs_sub_comm]
  exact mul_le_mul_of_nonneg_left (h z) γ.coe_nonneg

/-! ### The resolvent of the one-step variances -/

/-- **The resolvent of the one-step variances of a nonnegative resolvent**: for `γ < 1` and a
nonnegative bounded measurable `f` whose resolvent `V = R_γ f` is bounded by `B`, the resolvent of
the one-step variances `Var[V; κ y]` satisfies `γ ^ 2 R_γ Var_κ(V) ≤ 2 B V - V ^ 2`, hence
`γ ^ 2 R_γ Var_κ(V) ≤ B ^ 2`. -/
theorem mul_integral_variance_integral_resolvent_le (hγ : γ < 1) {f : α → ℝ} {B C : ℝ}
    (hf : Measurable f) (hfC : ∀ y, |f y| ≤ C) (hf₀ : ∀ y, 0 ≤ f y)
    (hVB : ∀ y, ∫ z, f z ∂(resolvent γ κ y) ≤ B) (x : α) :
    (γ : ℝ) ^ 2 * ∫ y, Var[fun z ↦ ∫ w, f w ∂(resolvent γ κ z); κ y] ∂(resolvent γ κ x) ≤
      2 * B * ∫ z, f z ∂(resolvent γ κ x) - (∫ z, f z ∂(resolvent γ κ x)) ^ 2 := by
  have := isFiniteKernel_resolvent (κ := κ) hγ
  set V := fun z ↦ ∫ w, f w ∂(resolvent γ κ z) with hV_def
  have hV : Measurable V := measurable_integral_resolvent hf
  have hVC := abs_integral_resolvent_le (κ := κ) hγ hfC
  have hV₀ (z : α) : 0 ≤ V z := integral_nonneg hf₀
  have hσ : Measurable fun y ↦ Var[V; κ y] := hV.variance_kernel
  have hσB (y : α) : |(γ : ℝ) ^ 2 * Var[V; κ y]| ≤ (γ : ℝ) ^ 2 * (C / (1 - γ)) ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (variance_nonneg _ _))]
    gcongr
    exact variance_le_sq_of_abs_le hV.aemeasurable (.of_forall hVC)
  have huB (z : α) : |2 * B * V z - V z ^ 2| ≤ B ^ 2 := by
    have := hVB z
    rw [abs_le]
    constructor <;> nlinarith [hV₀ z]
  rw [← integral_const_mul]
  refine integral_resolvent_le_of_add_le hγ (hσ.const_mul _) hσB
    (u := fun z ↦ 2 * B * V z - V z ^ 2) ((hV.const_mul _).sub (hV.pow_const 2)) huB
    (fun z ↦ ?_) x
  -- With `a = κ V` and `b = κ V ^ 2` at `z`, this is the inequality
  -- `γ ^ 2 (b - a ^ 2) + γ (2 B a - b) ≤ 2 B V z - V z ^ 2` for `V z = f z + γ a ≤ B`.
  have hint := integrable_of_abs_le hV hVC (κ z)
  have hint₂ : Integrable (fun w ↦ V w ^ 2) (κ z) :=
    integrable_of_abs_le (hV.pow_const 2) (B := (C / (1 - γ)) ^ 2)
      (fun w ↦ by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hVC w) 2) _
  have hb : 0 ≤ ∫ w, V w ^ 2 ∂(κ z) := integral_nonneg fun w ↦ sq_nonneg _
  have hVz : V z = f z + γ * ∫ w, V w ∂(κ z) := integral_resolvent_eq_add hγ hf hfC z
  have hγ₀ : (0 : ℝ) ≤ γ := γ.coe_nonneg
  have hγ₁ : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ.le
  have hVzB : f z + γ * ∫ w, V w ∂(κ z) ≤ B := hVz ▸ hVB z
  rw [variance_eq_sub (MemLp.of_bound hV.aestronglyMeasurable _
      (.of_forall fun w ↦ (Real.norm_eq_abs _).trans_le (hVC w))),
    integral_sub (hint.const_mul (2 * B)) hint₂, integral_const_mul, hVz]
  simp only [Pi.pow_apply]
  nlinarith [mul_nonneg (hf₀ z) (sub_nonneg.2 hVzB), mul_nonneg (mul_nonneg hγ₀
    (sub_nonneg.2 hγ₁)) hb, sq_nonneg (f z)]

/-- **The resolvent of the one-step standard deviations of a nonnegative resolvent**
[LWCGC24, Lemma 11]: for `0 < γ < 1` and a nonnegative bounded measurable `f` whose resolvent
`V = R_γ f` is bounded by `B`, the resolvent of the one-step standard deviations `√(Var[V; κ y])` is
at most `B / (γ √(1 - γ))`, improving the constant `4` of [LWCGC24, Lemma 11] to `1`. The bound
is stated in terms of the size `B` of `V`, rather than of a bound on `f` as in the total-variance
lemma. -/
theorem integral_sqrt_variance_integral_resolvent_le (hγ₀ : 0 < γ) (hγ : γ < 1) {f : α → ℝ}
    {B C : ℝ} (hf : Measurable f) (hfC : ∀ y, |f y| ≤ C) (hf₀ : ∀ y, 0 ≤ f y)
    (hVB : ∀ y, ∫ z, f z ∂(resolvent γ κ y) ≤ B) (x : α) :
    ∫ y, √(Var[fun z ↦ ∫ w, f w ∂(resolvent γ κ z); κ y]) ∂(resolvent γ κ x) ≤
      B / (γ * √(1 - γ)) := by
  have := isFiniteKernel_resolvent (κ := κ) hγ
  have hV := measurable_integral_resolvent (γ := γ) (κ := κ) hf
  have hVC := abs_integral_resolvent_le (κ := κ) hγ hfC
  have hγ₀' : (0 : ℝ) < γ := hγ₀
  have hγ' : 0 < 1 - (γ : ℝ) := sub_pos.2 hγ
  have hB : 0 ≤ B := (integral_nonneg hf₀).trans (hVB x)
  -- `γ ^ 2 R_γ Var_κ(V) ≤ 2 B V - V ^ 2 ≤ B ^ 2`.
  have hI : ∫ y, Var[fun z ↦ ∫ w, f w ∂(resolvent γ κ z); κ y] ∂(resolvent γ κ x) ≤
      (B / γ) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity), mul_comm]
    have := mul_integral_variance_integral_resolvent_le hγ hf hfC hf₀ hVB x
    nlinarith [sq_nonneg (B - ∫ z, f z ∂(resolvent γ κ x))]
  -- Jensen's inequality for the square root, for the resolvent of mass `(1 - γ)⁻¹`.
  refine (integral_sqrt_le_sqrt_measureReal_mul_integral (.of_forall fun y ↦ variance_nonneg _ _)
    (integrable_of_abs_le (B := (C / (1 - γ)) ^ 2) hV.variance_kernel (fun y ↦ ?_)
      (resolvent γ κ x))).trans ?_
  · rw [abs_of_nonneg (variance_nonneg _ _)]
    exact variance_le_sq_of_abs_le hV.aemeasurable (.of_forall hVC)
  rw [measureReal_resolvent_univ hγ, show B / (γ * √(1 - γ)) = √((1 - (γ : ℝ))⁻¹ * (B / γ) ^ 2) by
    rw [Real.sqrt_mul (inv_nonneg.2 hγ'.le), Real.sqrt_sq (div_nonneg hB hγ₀'.le), Real.sqrt_inv]
    ring]
  gcongr

/-! ### The resolvent of a kernel with Bernstein-type deviations -/

omit [IsMarkovKernel κ] in
/-- The iterated resolvents of the one-step standard deviations are measurable: if
`V 0 = R_γ f` for a measurable `f` and `V (l + 1) = R_γ √Var_κ(V l)` for every `l`, then every
`V l` is measurable. -/
theorem measurable_of_eq_integral_resolvent_sqrt_variance [IsSFiniteKernel κ] {f : α → ℝ}
    (hf : Measurable f) {V : ℕ → α → ℝ} (hV₀ : ∀ x, V 0 x = ∫ y, f y ∂(resolvent γ κ x))
    (hV : ∀ l x, V (l + 1) x = ∫ y, √Var[V l; κ y] ∂(resolvent γ κ x)) (l : ℕ) :
    Measurable (V l) := by
  induction l with
  | zero => rw [funext hV₀]; exact measurable_integral_resolvent hf
  | succ l ih => rw [funext (hV l)]; exact measurable_integral_resolvent ih.variance_kernel.sqrt

/-- **A priori bounds on the iterated resolvents of the one-step standard deviations**
[LWCGC24, (73)]: for `0 < γ < 1` and a measurable `f` with `0 ≤ f ≤ C`, if `V 0 = R_γ f` and
`V (l + 1) = R_γ √Var_κ(V l)` for every `l`, then `0 ≤ V l ≤ C / ((1 - γ) (γ √(1 - γ)) ^ l)`.
The bound of `V 0` is `C / (1 - γ)`, and each step multiplies it by `1 / (γ √(1 - γ))`
(`ProbabilityTheory.Kernel.integral_sqrt_variance_integral_resolvent_le`). -/
theorem mem_Icc_of_eq_integral_resolvent_sqrt_variance (hγ₀ : 0 < γ) (hγ : γ < 1) {f : α → ℝ}
    {C : ℝ} (hf : Measurable f) (hf₀ : ∀ x, 0 ≤ f x) (hfC : ∀ x, f x ≤ C) {V : ℕ → α → ℝ}
    (hV₀ : ∀ x, V 0 x = ∫ y, f y ∂(resolvent γ κ x))
    (hV : ∀ l x, V (l + 1) x = ∫ y, √Var[V l; κ y] ∂(resolvent γ κ x)) (l : ℕ) (x : α) :
    V l x ∈ Icc 0 (C / ((1 - γ) * (γ * √(1 - γ)) ^ l)) := by
  have hVm := measurable_of_eq_integral_resolvent_sqrt_variance hf hV₀ hV
  -- `V l` is the resolvent of a nonnegative bounded measurable function `g`
  suffices h : ∃ g : α → ℝ, Measurable g ∧ (∀ y, 0 ≤ g y) ∧ (∃ B, ∀ y, |g y| ≤ B) ∧
      (∀ x, V l x = ∫ y, g y ∂(resolvent γ κ x)) ∧
      ∀ x, V l x ∈ Icc 0 (C / ((1 - γ) * (γ * √(1 - γ)) ^ l)) from h.choose_spec.2.2.2.2 x
  induction l with
  | zero =>
    refine ⟨f, hf, hf₀, ⟨C, fun y ↦ abs_le.2 ⟨by linarith [hf₀ y, hfC y], hfC y⟩⟩, hV₀,
      fun x ↦ ⟨?_, ?_⟩⟩
    · rw [hV₀]
      exact integral_nonneg hf₀
    · rw [hV₀, pow_zero, mul_one]
      exact (le_abs_self _).trans (abs_integral_resolvent_le hγ
        (fun y ↦ abs_le.2 ⟨by linarith [hf₀ y, hfC y], hfC y⟩) x)
  | succ l ih =>
    obtain ⟨g, hg, hg₀, ⟨B, hgB⟩, hVg, hVl⟩ := ih
    have hb : 0 ≤ C / ((1 - γ) * (γ * √(1 - γ)) ^ l) := (hVl x).1.trans (hVl x).2
    have hσ (y : α) : √Var[V l; κ y] ≤ C / ((1 - γ) * (γ * √(1 - γ)) ^ l) :=
      sqrt_variance_le_of_abs_le (hVm l).aemeasurable hb
        (.of_forall fun z ↦ abs_le.2 ⟨by linarith [(hVl z).1], (hVl z).2⟩)
    refine ⟨fun y ↦ √Var[V l; κ y], (hVm l).variance_kernel.sqrt, fun y ↦ Real.sqrt_nonneg _,
      ⟨_, fun y ↦ (abs_of_nonneg (Real.sqrt_nonneg _)).trans_le (hσ y)⟩, hV l,
      fun x ↦ ⟨?_, ?_⟩⟩
    · rw [hV]
      exact integral_nonneg fun y ↦ Real.sqrt_nonneg _
    · -- Lemma 11 for `V l = R_γ g ≤ C / ((1 - γ) (γ √(1 - γ)) ^ l)`
      have h := integral_sqrt_variance_integral_resolvent_le (κ := κ) hγ₀ hγ hg hgB hg₀
        (fun y ↦ (hVg y).symm.trans_le (hVl y).2) x
      rw [← funext hVg] at h
      rw [hV, pow_succ, ← mul_assoc, ← div_div]
      exact h

/-- The scalar recursion behind [LWCGC24, Lemma 2, (76)–(78)]: for `0 < γ < 1`, `9 ε ≤ 1 - γ`,
`log (1 - γ)⁻¹ ≤ m` and `b l = C / ((1 - γ) (γ √(1 - γ)) ^ l)`, if the errors `d l` and the
next-level terms `e l` satisfy `d l ≤ γ √ε e l + γ ε b l / (1 - γ)` for `l ≤ m`,
`e l ≤ b (l + 1) + d (l + 1)` and `e m ≤ b m / (1 - γ)`, then `d 0 ≤ 3 C √(ε / (1 - γ) ^ 3)`. -/
private lemma le_three_mul_sqrt_of_le_mul_add (hγ₀ : 0 < γ) (hγ : γ < 1) {C ε : ℝ} (hC : 0 ≤ C)
    {m : ℕ} (hm : Real.log (1 - γ)⁻¹ ≤ m) (hε₀ : 0 ≤ ε) (hε : 9 * ε ≤ 1 - γ) {d e : ℕ → ℝ}
    (hd : ∀ l ≤ m, d l ≤
      γ * √ε * e l + γ * ε * (C / ((1 - γ) * (γ * √(1 - γ)) ^ l)) / (1 - γ))
    (he : ∀ l, e l ≤ C / ((1 - γ) * (γ * √(1 - γ)) ^ (l + 1)) + d (l + 1))
    (hem : e m ≤ C / ((1 - γ) * (γ * √(1 - γ)) ^ m) / (1 - γ)) :
    d 0 ≤ 3 * C * √(ε / (1 - γ) ^ 3) := by
  have hγ₁ : (γ : ℝ) < 1 := hγ
  have hu : 0 < 1 - (γ : ℝ) := sub_pos.2 hγ₁
  set b : ℕ → ℝ := fun l ↦ C / ((1 - γ) * (γ * √(1 - γ)) ^ l) with hb_def
  -- rescaling: with `a = γ √ε` and `q = √(ε / (1 - γ))`, `a ^ l b l = (C / (1 - γ)) q ^ l`
  set a : ℝ := γ * √ε with ha_def
  set q : ℝ := √(ε / (1 - γ)) with hq_def
  set B : ℝ := C / (1 - γ) with hB_def
  have ha₀ : 0 ≤ a := by positivity
  have hq₀ : 0 ≤ q := Real.sqrt_nonneg _
  have hB₀ : 0 ≤ B := by positivity
  have hq : q = √ε / √(1 - γ) := Real.sqrt_div' _ hu.le
  have hsqrt : 0 < √(1 - (γ : ℝ)) := Real.sqrt_pos.2 hu
  have hab (l : ℕ) : a ^ l * b l = B * q ^ l := by
    rw [hB_def, hq, ha_def]
    simp only [hb_def]
    rw [mul_pow, mul_pow, div_pow]
    field_simp
  have hq2 : γ * ε / (1 - γ) ≤ q ^ 2 := by
    rw [hq_def, Real.sq_sqrt (div_nonneg hε₀ hu.le), mul_div_assoc]
    exact mul_le_of_le_one_left (by positivity) hγ₁.le
  have haq : a / (1 - γ) ≤ q / √(1 - γ) := by
    rw [hq, div_div, Real.mul_self_sqrt hu.le, ha_def]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (Real.sqrt_nonneg _) hγ₁.le) hu.le
  have hq13 : q ≤ 1 / 3 := by
    rw [hq_def, show (1 / 3 : ℝ) = √(1 / 9) by
      rw [show (1 / 9 : ℝ) = (1 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by rw [div_le_iff₀ hu]; linarith)
  set θ : ℝ := q * (1 + q) / (1 - q) with hθ_def
  have hq1 : 0 < 1 - q := by linarith
  have hθ : q + θ * q + q ^ 2 = θ := by
    rw [hθ_def]
    field_simp
    ring
  have hθq : q ^ 2 ≤ θ := by
    rw [hθ_def, le_div_iff₀ hq1]
    nlinarith
  -- backward induction over the levels: `a ^ l d l ≤ B (θ q ^ l + q ^ m q / √(1 - γ))`
  have hind (k : ℕ) (hk : k ≤ m) :
      a ^ (m - k) * d (m - k) ≤ B * (θ * q ^ (m - k) + q ^ m * (q / √(1 - γ))) := by
    induction k with
    | zero =>
      rw [Nat.sub_zero]
      have h₁ := hd m le_rfl
      calc a ^ m * d m ≤ a ^ m * (a * (b m / (1 - γ)) + γ * ε * b m / (1 - γ)) := by
            gcongr
            exact h₁.trans (by gcongr)
        _ = (a ^ m * b m) * (a / (1 - γ) + γ * ε / (1 - γ)) := by ring
        _ ≤ (B * q ^ m) * (q / √(1 - γ) + θ) := by
            rw [hab]
            gcongr
            exact hq2.trans hθq
        _ = B * (θ * q ^ m + q ^ m * (q / √(1 - γ))) := by ring
    | succ k ih =>
      have hl : m - k = m - (k + 1) + 1 := by omega
      have h₁ := hd (m - (k + 1)) (Nat.sub_le _ _)
      have h₂ := he (m - (k + 1))
      have h₃ := ih (by omega)
      rw [hl] at h₃
      set l := m - (k + 1)
      calc a ^ l * d l ≤ a ^ l * (a * (b (l + 1) + d (l + 1)) + γ * ε * b l / (1 - γ)) := by
            gcongr
            exact h₁.trans (by gcongr)
        _ = a ^ (l + 1) * b (l + 1) + a ^ (l + 1) * d (l + 1) +
            (a ^ l * b l) * (γ * ε / (1 - γ)) := by ring
        _ ≤ B * q ^ (l + 1) + B * (θ * q ^ (l + 1) + q ^ m * (q / √(1 - γ))) +
            (B * q ^ l) * q ^ 2 := by
            rw [hab, hab]
            gcongr
        _ = B * (q ^ l * (q + θ * q + q ^ 2) + q ^ m * (q / √(1 - γ))) := by ring
        _ = B * (θ * q ^ l + q ^ m * (q / √(1 - γ))) := by rw [hθ]; ring
  -- after `m ≥ log (1 - γ)⁻¹` levels, `q ^ m ≤ exp (-m) ≤ 1 - γ`
  have hqm : q ^ m ≤ 1 - γ := by
    have hqe : q ≤ Real.exp (-1) :=
      hq13.trans (le_of_lt (by
        rw [Real.exp_neg, one_div]
        exact inv_strictAnti₀ (Real.exp_pos 1) Real.exp_one_lt_three))
    calc q ^ m ≤ Real.exp (-1) ^ m := pow_le_pow_left₀ hq₀ hqe m
      _ = Real.exp (-m) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (Real.log (1 - γ)) := Real.exp_le_exp.2 (by rw [Real.log_inv] at hm; linarith)
      _ = 1 - γ := Real.exp_log hu
  have h₀ := hind m le_rfl
  rw [Nat.sub_self, pow_zero, one_mul, pow_zero, mul_one] at h₀
  have hfin : q ^ m * (q / √(1 - γ)) ≤ q := by
    rw [mul_div_assoc', div_le_iff₀ hsqrt]
    calc q ^ m * q ≤ (1 - γ) * q := by gcongr
      _ = q * (√(1 - γ) * √(1 - γ)) := by rw [Real.mul_self_sqrt hu.le]; ring
      _ ≤ q * √(1 - γ) := by
          gcongr
          rw [mul_le_iff_le_one_left hsqrt, Real.sqrt_le_one]
          linarith [γ.coe_nonneg]
  have hθ2 : θ ≤ 2 * q := by
    rw [hθ_def, div_le_iff₀ hq1]
    nlinarith
  have hBq : B * q = C * √(ε / (1 - γ) ^ 3) := by
    rw [hB_def, hq_def, show ε / (1 - (γ : ℝ)) ^ 3 = ε / (1 - γ) / (1 - γ) ^ 2 by
      rw [div_div]; ring, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hu.le]
    ring
  calc d 0 ≤ B * (θ + q ^ m * (q / √(1 - γ))) := h₀
    _ ≤ B * (2 * q + q) := by gcongr
    _ = 3 * (B * q) := by ring
    _ = 3 * C * √(ε / (1 - γ) ^ 3) := by rw [hBq]; ring

/-- **The resolvent of a kernel with Bernstein-type deviations** [LWCGC24, Lemma 2]. Let `κ` and
`κ'` be Markov kernels, `0 < γ < 1`, and `f` a measurable function with `0 ≤ f ≤ C`. Let
`V 0 = R_γ(κ) f` and `V (l + 1) = R_γ(κ) √Var_κ(V l)` be the iterated resolvents of the one-step
standard deviations, so that `0 ≤ V l ≤ b l := C / ((1 - γ) (γ √(1 - γ)) ^ l)`
(`ProbabilityTheory.Kernel.mem_Icc_of_eq_integral_resolvent_sqrt_variance`). Suppose that `κ'`
deviates from `κ` on the first levels by a Bernstein-type bound
`|κ' V l - κ V l| ≤ √(ε Var_κ(V l)) + ε b l` for every `l ≤ m`, with `log (1 - γ)⁻¹ ≤ m` and
`9 ε ≤ 1 - γ`. Then the resolvents of `f` satisfy
`|R_γ(κ') f - R_γ(κ) f| ≤ 3 C √(ε / (1 - γ) ^ 3)`.

With `ε = β / N`, [LWCGC24] assumes the deviation bound with the sup norm of `V l`,
which is at most `b l`, in place of `b l`, and concludes
`|R_γ(κ') f - R_γ(κ) f| ≤ 6 C √(ε / (1 - γ) ^ 3)` under the stronger condition
`16 e ^ 2 ε < 1 - γ`; the bound `γ R_γ √Var_κ(V) ≤ sup V / √(1 - γ)` of Lemma 11 with constant
`1` instead of `4` gives the constant `3`. -/
theorem abs_integral_resolvent_sub_integral_resolvent_le_of_abs_sub_le (κ' : Kernel α α)
    [IsMarkovKernel κ'] (hγ₀ : 0 < γ) (hγ : γ < 1) {f : α → ℝ} {C ε : ℝ} (hf : Measurable f)
    (hf₀ : ∀ x, 0 ≤ f x) (hfC : ∀ x, f x ≤ C) {V : ℕ → α → ℝ}
    (hV₀ : ∀ x, V 0 x = ∫ y, f y ∂(resolvent γ κ x))
    (hV : ∀ l x, V (l + 1) x = ∫ y, √Var[V l; κ y] ∂(resolvent γ κ x)) {m : ℕ}
    (hm : Real.log (1 - γ)⁻¹ ≤ m) (hε₀ : 0 ≤ ε) (hε : 9 * ε ≤ 1 - γ)
    (h : ∀ l ≤ m, ∀ x, |∫ y, V l y ∂(κ' x) - ∫ y, V l y ∂(κ x)| ≤
      √(ε * Var[V l; κ x]) + ε * (C / ((1 - γ) * (γ * √(1 - γ)) ^ l))) (x : α) :
    |∫ y, f y ∂(resolvent γ κ' x) - ∫ y, f y ∂(resolvent γ κ x)| ≤
      3 * C * √(ε / (1 - γ) ^ 3) := by
  -- The error `D l = |R_γ(κ') (r l) - V l|` at level `l`, where `V l = R_γ(κ) (r l)`, is bounded
  -- by the simulation bound by `γ √ε` times `R_γ(κ') √Var_κ(V l)`, which is `V (l + 1)` up to
  -- the error at level `l + 1` [LWCGC24, (74)–(76)]. The scalar recursion
  -- `le_three_mul_sqrt_of_le_mul_add` unrolls these bounds over the levels `l ≤ m`.
  have := isFiniteKernel_resolvent (κ := κ') hγ
  have hC : 0 ≤ C := (hf₀ x).trans (hfC x)
  set b : ℕ → ℝ := fun l ↦ C / ((1 - γ) * (γ * √(1 - γ)) ^ l) with hb_def
  have hVm := measurable_of_eq_integral_resolvent_sqrt_variance hf hV₀ hV
  have hVb : ∀ l y, V l y ∈ Icc 0 (b l) :=
    mem_Icc_of_eq_integral_resolvent_sqrt_variance hγ₀ hγ hf hf₀ hfC hV₀ hV
  have hb₀ (l : ℕ) : 0 ≤ b l := (hVb l x).1.trans (hVb l x).2
  have hσ (l : ℕ) (y : α) : √Var[V l; κ y] ≤ b l :=
    sqrt_variance_le_of_abs_le (hVm l).aemeasurable (hb₀ l)
      (.of_forall fun z ↦ abs_le.2 ⟨by linarith [(hVb l z).1, hb₀ l], (hVb l z).2⟩)
  -- the rewards `r l` of the levels: `V l = R_γ(κ) (r l)`
  set r : ℕ → α → ℝ := fun l ↦ Nat.casesOn l f fun k y ↦ √Var[V k; κ y] with hr_def
  have hr₀ : r 0 = f := rfl
  have hr (l : ℕ) : r (l + 1) = fun y ↦ √Var[V l; κ y] := rfl
  have hr_meas (l : ℕ) : Measurable (r l) := by
    cases l
    exacts [hf, (hVm _).variance_kernel.sqrt]
  have hrB (l : ℕ) : ∃ B, ∀ y, |r l y| ≤ B := by
    cases l with
    | zero => rw [hr₀]; exact ⟨C, fun y ↦ abs_le.2 ⟨by linarith [hf₀ y, hfC y], hfC y⟩⟩
    | succ k =>
      rw [hr]
      exact ⟨b k, fun y ↦ (abs_of_nonneg (Real.sqrt_nonneg _)).trans_le (hσ k y)⟩
  have hVr (l : ℕ) (x : α) : V l x = ∫ y, r l y ∂(resolvent γ κ x) := by
    cases l
    exacts [hV₀ x, hV _ x]
  -- the error `D l = |R_γ(κ') (r l) - V l|` at level `l`
  set D : ℕ → ℝ := fun l ↦ |∫ y, r l y ∂(resolvent γ κ' x) - V l x| with hD_def
  have hstep (l : ℕ) (hl : l ≤ m) :
      D l ≤ γ * √ε * ∫ y, r (l + 1) y ∂(resolvent γ κ' x) + γ * ε * b l / (1 - γ) := by
    obtain ⟨B, hB⟩ := hrB l
    obtain ⟨B', hB'⟩ := hrB (l + 1)
    have hi : Integrable (fun z ↦ √ε * r (l + 1) z) (resolvent γ κ' x) :=
      (integrable_of_abs_le (hr_meas (l + 1)) hB' _).const_mul _
    have hdev (z : α) : |∫ w, (∫ y, r l y ∂(resolvent γ κ w)) ∂(κ' z) -
        ∫ w, (∫ y, r l y ∂(resolvent γ κ w)) ∂(κ z)| ≤ √ε * r (l + 1) z + ε * b l := by
      simp_rw [← hVr l]
      rw [hr, ← Real.sqrt_mul hε₀]
      exact h l hl z
    simp only [hD_def]
    rw [hVr l x]
    refine (abs_integral_resolvent_sub_integral_resolvent_le κ' hγ
      (hr_meas l) hB (hi.add (integrable_const (ε * b l))) hdev).trans_eq ?_
    rw [Pi.add_def, integral_add hi (integrable_const _), integral_const_mul, integral_const,
      smul_eq_mul, measureReal_resolvent_univ hγ]
    field_simp
  -- the next level: `R_γ(κ') (r (l + 1)) ≤ V (l + 1) + D (l + 1) ≤ b (l + 1) + D (l + 1)`
  have hnext (l : ℕ) : ∫ y, r (l + 1) y ∂(resolvent γ κ' x) ≤ b (l + 1) + D (l + 1) := by
    have h₁ := le_abs_self (∫ y, r (l + 1) y ∂(resolvent γ κ' x) - V (l + 1) x)
    linarith [(hVb (l + 1) x).2]
  -- the last level: `R_γ(κ') (r (m + 1)) ≤ b m / (1 - γ)`
  have hlast : ∫ y, r (m + 1) y ∂(resolvent γ κ' x) ≤ b m / (1 - γ) :=
    (le_abs_self _).trans (abs_integral_resolvent_le hγ
      (fun y ↦ (abs_of_nonneg (Real.sqrt_nonneg _)).trans_le (hσ m y)) x)
  have hD₀ : D 0 = |∫ y, f y ∂(resolvent γ κ' x) - ∫ y, f y ∂(resolvent γ κ x)| := by
    simp only [hD_def, hr₀, hV₀]
  rw [← hD₀]
  exact le_three_mul_sqrt_of_le_mul_add hγ₀ hγ hC hm hε₀ hε hstep hnext hlast

end Markov

end ProbabilityTheory.Kernel

/-! ### The flow equation -/

namespace MeasureTheory.Measure

open ProbabilityTheory Kernel

variable {α : Type*} {mα : MeasurableSpace α} {γ : ℝ≥0} {κ : Kernel α α} {μ ν : Measure α}

/-- The image of a measure by the resolvent is the discounted sum of its images by the powers of
the kernel. -/
theorem resolvent_comp (γ : ℝ≥0) (κ : Kernel α α) (μ : Measure α) :
    resolvent γ κ ∘ₘ μ = Measure.sum fun n ↦ ((γ : ℝ≥0∞) ^ n) • ((κ ^ n : Kernel α α) ∘ₘ μ) := by
  ext s hs
  rw [bind_apply hs (resolvent γ κ).aemeasurable, Measure.sum_apply _ hs]
  simp_rw [resolvent_apply' _ _ _ hs, smul_apply, smul_eq_mul, bind_apply hs (κ ^ _).aemeasurable]
  rw [lintegral_tsum fun n ↦ (((κ ^ n).measurable_coe hs).const_mul _).aemeasurable]
  simp_rw [lintegral_const_mul _ ((κ ^ _).measurable_coe hs)]

/-- **The flow equation**: the image `ν = resolvent γ κ ∘ₘ μ` of a measure `μ` by the resolvent
satisfies `ν = μ + γ • (κ ∘ₘ ν)`. -/
theorem resolvent_comp_eq_add (γ : ℝ≥0) (κ : Kernel α α) (μ : Measure α) :
    resolvent γ κ ∘ₘ μ = μ + (γ : ℝ≥0∞) • (κ ∘ₘ (resolvent γ κ ∘ₘ μ)) := by
  ext s hs
  rw [comp_assoc, add_apply, smul_apply, smul_eq_mul, bind_apply hs (resolvent γ κ).aemeasurable,
    bind_apply hs (κ ∘ₖ resolvent γ κ).aemeasurable]
  simp_rw [← dirac_add_comp_resolvent_apply γ κ, add_apply, smul_apply, smul_eq_mul]
  rw [lintegral_add_right _ (((κ ∘ₖ resolvent γ κ).measurable_coe hs).const_mul _),
    lintegral_const_mul _ ((κ ∘ₖ resolvent γ κ).measurable_coe hs)]
  simp_rw [dirac_apply' _ hs]
  rw [lintegral_indicator_one hs]

/-- Unfolding the flow equation `n` times: if `ν = μ + c • (κ ∘ₘ ν)`, then
`ν = ∑ k < n, c ^ k • (κ ^ k ∘ₘ μ) + c ^ n • (κ ^ n ∘ₘ ν)`. -/
theorem eq_sum_range_add_of_eq_add {c : ℝ≥0∞} (h : ν = μ + c • (κ ∘ₘ ν)) (n : ℕ) :
    ν = (∑ k ∈ Finset.range n, c ^ k • ((κ ^ k : Kernel α α) ∘ₘ μ)) +
      c ^ n • ((κ ^ n : Kernel α α) ∘ₘ ν) := by
  induction n with
  | zero => simp [one_def, id_comp]
  | succ n ih =>
    conv_lhs => rw [ih, h]
    simp [comp_add, comp_smul, comp_assoc, ← mul_eq_comp, ← pow_succ, smul_smul,
      Finset.sum_range_succ, add_assoc]

/-- **Uniqueness of the solution of the flow equation**: for a Markov kernel `κ` and `γ < 1`, a
finite measure `ν` with `ν = μ + γ • (κ ∘ₘ ν)` is the image `resolvent γ κ ∘ₘ μ` of `μ` by the
resolvent. -/
theorem eq_resolvent_comp_of_eq_add [IsMarkovKernel κ] (hγ : γ < 1) [IsFiniteMeasure ν]
    (h : ν = μ + (γ : ℝ≥0∞) • (κ ∘ₘ ν)) : ν = resolvent γ κ ∘ₘ μ := by
  ext s hs
  rw [resolvent_comp, Measure.sum_apply _ hs]
  simp_rw [smul_apply, smul_eq_mul]
  -- The remainder `γ ^ n * (κ ^ n ∘ₘ ν) s` is at most `γ ^ n * ν univ`, which tends to `0`.
  have hrem : Tendsto (fun n ↦ (γ : ℝ≥0∞) ^ n * ((κ ^ n : Kernel α α) ∘ₘ ν) s) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n ↦ (γ : ℝ≥0∞) ^ n * ν univ) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.coe_lt_one_iff.2 hγ))
        (Or.inr (measure_ne_top ν univ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ bot_le)
      fun n ↦ ?_
    gcongr (γ : ℝ≥0∞) ^ n * ?_
    exact (measure_mono (subset_univ s)).trans_eq (comp_apply_univ (κ := κ ^ n))
  refine tendsto_nhds_unique (f := fun _ : ℕ ↦ ν s) (l := atTop) tendsto_const_nhds ?_
  convert (ENNReal.tendsto_nat_tsum fun k ↦
    (γ : ℝ≥0∞) ^ k * ((κ ^ k : Kernel α α) ∘ₘ μ) s).add hrem using 1
  · ext n
    conv_lhs => rw [eq_sum_range_add_of_eq_add h n]
    simp
  · rw [add_zero]

end MeasureTheory.Measure
