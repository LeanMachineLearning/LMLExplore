/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MeasureTheory.Integral.BoundedMeasurable
public import LMLExplore.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableIntegral

import TauCeti.MeasureTheory.Integral.Bind

/-!
# Kernels as operators on bounded measurable functions

A finite kernel `κ : Kernel α β` acts on bounded measurable functions by
`(κ f)(x) = ∫ y, f y ∂κ x`. This file bundles that action as a continuous linear map
`κ.integralCLM : boundedMeasurable β →L[ℝ] boundedMeasurable α` and proves its basic properties:
it is positive (monotone), the action of a composite kernel is the composite of the actions, and
a Markov kernel preserves constants and does not increase the sup norm.

These are the properties through which transition kernels enter the analysis of Markov chains and
of Markov decision processes: the Bellman operators are built from the action of the transition
kernel, and their monotonicity and contraction properties come from those proved here.

Kernels act on functions contravariantly: `η ∘ₖ κ` acts as the action of `κ` after that of `η`
(`integralCLM_comp`).

## Main definitions

* `ProbabilityTheory.Kernel.integralCLM κ`: the action `f ↦ (x ↦ ∫ y, f y ∂κ x)` of a finite
  kernel on bounded measurable functions.

## Main statements

* `ProbabilityTheory.Kernel.monotone_integralCLM`, `ProbabilityTheory.Kernel.integralCLM_nonneg`:
  the action of a kernel is positive.
* `ProbabilityTheory.Kernel.integralCLM_comp`, `ProbabilityTheory.Kernel.integralCLM_id`: the
  action is contravariant for the composition of kernels.
* `ProbabilityTheory.Kernel.integralCLM_pow_zero`, `ProbabilityTheory.Kernel.integralCLM_pow_succ`:
  the powers of a kernel act by the iterates of its action.
* `ProbabilityTheory.Kernel.integralCLM_one`: a Markov kernel preserves constants.
* `ProbabilityTheory.Kernel.Invariant.integral_integralCLM`: integrating `κ u` against an invariant
  measure of `κ` gives the integral of `u`.
* `ProbabilityTheory.Kernel.norm_integralCLM_apply_le`,
  `ProbabilityTheory.Kernel.opNorm_integralCLM_le`: a Markov kernel does not increase the sup
  norm.

## References

* D. Revuz, *Markov chains*, North-Holland, 2nd edition, 1984, Chapter 1
-/

public section

open MeasureTheory Set LMLExplore
open scoped ENNReal NNReal lp

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {κ : Kernel α β}

private lemma abs_integral_le_mul_norm [IsFiniteKernel κ] {C : ℝ≥0} {x : α} (hC : κ x univ ≤ C)
    (f : boundedMeasurable β) : |∫ y, (f : ℓ^∞(β, ℝ)) y ∂κ x| ≤ C * ‖f‖ := by
  refine (boundedMeasurable.abs_integral_le f).trans ?_
  rw [mul_comm]
  gcongr
  exact ENNReal.toReal_le_coe_of_le_coe hC

private lemma abs_integral_le_bound_mul (κ : Kernel α β) [IsFiniteKernel κ]
    (f : boundedMeasurable β) (x : α) :
    |∫ y, (f : ℓ^∞(β, ℝ)) y ∂κ x| ≤ κ.bound.toReal * ‖f‖ := by
  have hC : κ x univ ≤ κ.bound.toNNReal := by
    rw [ENNReal.coe_toNNReal κ.bound_ne_top]
    exact κ.measure_le_bound x univ
  rw [← ENNReal.coe_toNNReal_eq_toReal]
  exact abs_integral_le_mul_norm hC f

private lemma bddAbove_abs_integral (κ : Kernel α β) [IsFiniteKernel κ]
    (f : boundedMeasurable β) : BddAbove (range fun x ↦ |∫ y, (f : ℓ^∞(β, ℝ)) y ∂κ x|) := by
  refine ⟨κ.bound.toReal * ‖f‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact abs_integral_le_bound_mul κ f x

/-- The action `f ↦ (x ↦ ∫ y, f y ∂κ x)` of a finite kernel `κ : Kernel α β` on bounded measurable
functions, as a continuous linear map from `boundedMeasurable β` to `boundedMeasurable α`. -/
noncomputable def integralCLM (κ : Kernel α β) [IsFiniteKernel κ] :
    boundedMeasurable β →L[ℝ] boundedMeasurable α :=
  LinearMap.mkContinuous
    { toFun f := boundedMeasurable.mk (fun x ↦ ∫ y, (f : ℓ^∞(β, ℝ)) y ∂κ x)
        ((boundedMeasurable.measurable f).stronglyMeasurable.integral_kernel (κ := κ)).measurable
        (bddAbove_abs_integral κ f)
      map_add' f g := by
        ext x
        simp only [boundedMeasurable.coeFn_mk, boundedMeasurable.coeFn_add, Pi.add_apply]
        exact integral_add (boundedMeasurable.integrable f (κ x))
          (boundedMeasurable.integrable g (κ x))
      map_smul' c f := by
        ext x
        simp [integral_const_mul] }
    κ.bound.toReal fun f ↦ by
      refine boundedMeasurable.norm_le_of_forall_le (by positivity) fun x ↦ ?_
      rw [LinearMap.coe_mk, AddHom.coe_mk, boundedMeasurable.coeFn_mk]
      exact abs_integral_le_bound_mul κ f x

section IntegralCLM

variable [IsFiniteKernel κ]

@[simp]
theorem integralCLM_apply (f : boundedMeasurable β) (x : α) :
    (κ.integralCLM f : ℓ^∞(α, ℝ)) x = ∫ y, (f : ℓ^∞(β, ℝ)) y ∂κ x :=
  congrFun (boundedMeasurable.coeFn_mk _ _ _) x

/-- The action of a kernel is monotone. -/
theorem monotone_integralCLM : Monotone κ.integralCLM := fun f g hfg ↦
  boundedMeasurable.le_def.2 fun x ↦ by
    simp only [integralCLM_apply]
    exact integral_mono (boundedMeasurable.integrable f (κ x))
      (boundedMeasurable.integrable g (κ x)) fun y ↦ boundedMeasurable.le_def.1 hfg y

/-- The action of a kernel is positive. -/
theorem integralCLM_nonneg {f : boundedMeasurable β} (hf : 0 ≤ f) : 0 ≤ κ.integralCLM f := by
  rw [← κ.integralCLM.map_zero]
  exact monotone_integralCLM hf

/-- If every measure `κ x` has total mass at most `C`, the action of `κ` multiplies the sup norm
by at most `C`. -/
theorem norm_integralCLM_apply_le_of_forall_measure_univ_le {C : ℝ≥0}
    (hC : ∀ x, κ x univ ≤ C) (f : boundedMeasurable β) : ‖κ.integralCLM f‖ ≤ C * ‖f‖ := by
  refine boundedMeasurable.norm_le_of_forall_le (by positivity) fun x ↦ ?_
  rw [integralCLM_apply]
  exact abs_integral_le_mul_norm (hC x) f

/-- The action of `η ∘ₖ κ` is the action of `η` followed by that of `κ`. -/
theorem integralCLM_comp (η : Kernel β γ) [IsFiniteKernel η] :
    (η ∘ₖ κ).integralCLM = κ.integralCLM.comp η.integralCLM := by
  ext f x
  simp only [integralCLM_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]
  exact integral_comp (boundedMeasurable.integrable f ((η ∘ₖ κ) x))

/-- The identity kernel acts as the identity. -/
@[simp]
theorem integralCLM_id : (Kernel.id : Kernel α α).integralCLM = ContinuousLinearMap.id ℝ _ := by
  ext f x
  rw [integralCLM_apply, id_apply,
    integral_dirac' _ _ (boundedMeasurable.measurable f).stronglyMeasurable,
    ContinuousLinearMap.id_apply]

end IntegralCLM

section Invariant

variable {κ : Kernel α α} [IsFiniteKernel κ]

/-- Integrating `κ u` against an invariant measure `π` of `κ` gives the integral of `u`. -/
theorem Invariant.integral_integralCLM {π : Measure α} [IsFiniteMeasure π] (hπ : κ.Invariant π)
    (u : boundedMeasurable α) :
    ∫ x, (κ.integralCLM u : ℓ^∞(α, ℝ)) x ∂π = ∫ x, (u : ℓ^∞(α, ℝ)) x ∂π := by
  conv_rhs => rw [← hπ.def]
  rw [Measure.integral_bind κ.aemeasurable (boundedMeasurable.integrable u _)]
  simp only [integralCLM_apply]

end Invariant

section Markov

variable [IsMarkovKernel κ]

/-- A Markov kernel maps the constant function `1` to itself. -/
@[simp]
theorem integralCLM_one : κ.integralCLM 1 = 1 := by
  ext x
  simp only [integralCLM_apply, boundedMeasurable.coeFn_one, Pi.one_apply,
    integral_const, probReal_univ, smul_eq_mul, mul_one]

/-- A Markov kernel preserves constant functions. -/
@[simp]
theorem integralCLM_algebraMap (c : ℝ) :
    κ.integralCLM (algebraMap ℝ (boundedMeasurable β) c) =
      algebraMap ℝ (boundedMeasurable α) c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, κ.integralCLM.map_smul,
    integralCLM_one]

/-- A Markov kernel does not increase the sup norm: `sup |κ f| ≤ sup |f|`. -/
theorem norm_integralCLM_apply_le (f : boundedMeasurable β) : ‖κ.integralCLM f‖ ≤ ‖f‖ := by
  have h := norm_integralCLM_apply_le_of_forall_measure_univ_le (C := 1)
    (fun x ↦ (measure_univ (μ := κ x)).le) f
  rwa [NNReal.coe_one, one_mul] at h

/-- The action of a Markov kernel has operator norm at most `1`. -/
theorem opNorm_integralCLM_le : ‖κ.integralCLM‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    rw [one_mul]
    exact norm_integralCLM_apply_le f

end Markov

section Powers

variable {κ : Kernel α α} [IsMarkovKernel κ]

/-- The `0`-step kernel acts as the identity. -/
theorem integralCLM_pow_zero (f : boundedMeasurable α) : (κ ^ 0).integralCLM f = f := by
  simp only [pow_zero, one_eq_id, integralCLM_id, ContinuousLinearMap.id_apply]

/-- The `(n + 1)`-step kernel acts as the `n`-step kernel followed by `κ`. -/
theorem integralCLM_pow_succ (n : ℕ) (f : boundedMeasurable α) :
    (κ ^ (n + 1)).integralCLM f = κ.integralCLM ((κ ^ n).integralCLM f) := by
  simp only [pow_succ, mul_eq_comp, integralCLM_comp, ContinuousLinearMap.comp_apply]

end Powers

end ProbabilityTheory.Kernel
