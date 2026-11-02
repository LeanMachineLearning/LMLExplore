/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Normed.Lp.Measurable
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableIntegral

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
* `ProbabilityTheory.Kernel.integralCLM_one`: a Markov kernel preserves constants.
* `ProbabilityTheory.Kernel.norm_integralCLM_apply_le`,
  `ProbabilityTheory.Kernel.opNorm_integralCLM_le`: a Markov kernel does not increase the sup
  norm.

## References

* [D. Revuz, *Markov chains*, 1984][Rev84], Chapter 1
-/

public section

open MeasureTheory Set LMLExplore
open scoped ENNReal NNReal lp

namespace LMLExplore.boundedMeasurable

variable {β : Type*} [MeasurableSpace β]

/-- A bounded measurable function is integrable for every finite measure. -/
lemma integrable (f : boundedMeasurable β) (μ : Measure β) [IsFiniteMeasure μ] :
    Integrable (⇑(f : ℓ^∞(β, ℝ))) μ :=
  .of_bound (measurable f).aestronglyMeasurable ‖f‖ <| .of_forall fun y ↦
    (Real.norm_eq_abs _).trans_le (abs_apply_le_norm f y)

/-- The integral of a bounded measurable function `f` against a finite measure `μ` is at most
`‖f‖ * μ univ` in absolute value. -/
lemma abs_integral_le (f : boundedMeasurable β) {μ : Measure β} [IsFiniteMeasure μ] :
    |∫ y, (f : ℓ^∞(β, ℝ)) y ∂μ| ≤ ‖f‖ * μ.real univ := by
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const <| .of_forall fun y ↦
    (Real.norm_eq_abs _).trans_le (abs_apply_le_norm f y)

end LMLExplore.boundedMeasurable

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {κ : Kernel α β}

private lemma abs_integral_le_bound_mul (κ : Kernel α β) [IsFiniteKernel κ]
    (f : boundedMeasurable β) (x : α) :
    |∫ y, (f : ℓ^∞(β, ℝ)) y ∂κ x| ≤ κ.bound.toReal * ‖f‖ := by
  refine (boundedMeasurable.abs_integral_le f).trans ?_
  rw [mul_comm]
  gcongr
  exact ENNReal.toReal_mono κ.bound_ne_top (κ.measure_le_bound x univ)

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
theorem monotone_integralCLM : Monotone κ.integralCLM := fun f g hfg x ↦ by
  simp only [integralCLM_apply]
  exact integral_mono (boundedMeasurable.integrable f (κ x)) (boundedMeasurable.integrable g (κ x))
    fun y ↦ hfg y

/-- The action of a kernel is positive. -/
theorem integralCLM_nonneg {f : boundedMeasurable β} (hf : 0 ≤ f) : 0 ≤ κ.integralCLM f :=
  κ.integralCLM.map_zero ▸ monotone_integralCLM hf

/-- If every measure `κ x` has total mass at most `C`, the action of `κ` multiplies the sup norm
by at most `C`. -/
theorem norm_integralCLM_apply_le_of_forall_measure_univ_le {C : ℝ≥0}
    (hC : ∀ x, κ x univ ≤ C) (f : boundedMeasurable β) : ‖κ.integralCLM f‖ ≤ C * ‖f‖ := by
  refine boundedMeasurable.norm_le_of_forall_le (by positivity) fun x ↦ ?_
  rw [integralCLM_apply, mul_comm]
  refine (boundedMeasurable.abs_integral_le f).trans ?_
  gcongr
  rw [measureReal_def, ← ENNReal.coe_toReal, ENNReal.toReal_le_toReal (measure_ne_top _ _)
    ENNReal.coe_ne_top]
  exact hC x

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
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦
    (one_mul ‖f‖).symm ▸ norm_integralCLM_apply_le f

end Markov

end ProbabilityTheory.Kernel
