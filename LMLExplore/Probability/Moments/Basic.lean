/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.Basic

/-!
# Measurability of generating functions and Chernoff bounds

Small general facts about moment-generating functions and tail probabilities of real random
variables, shared by the concentration inequalities of the library. Tau Ceti provides the product
formula for the moment-generating function of a sum of independent random variables over a
`Finset` (`ProbabilityTheory.iIndepFun.mgf_sum_of_aemeasurable`) and the union bound over both
tails (`TauCeti.measureReal_le_abs_le_add`).

## Main statements

* `ProbabilityTheory.measurable_mgf`, `ProbabilityTheory.measurable_cgf`: for an s-finite measure,
  the moment-generating and cumulant generating functions are measurable functions of their
  argument.
* `ProbabilityTheory.measureReal_ge_le_exp_of_mgf_le`: Chernoff's bound
  `P(ε ≤ Y) ≤ exp (-t ε + K)` when `exp (t Y)` is integrable, `mgf Y μ t ≤ exp K` and `t ≥ 0`.
-/

public section

open MeasureTheory Real

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The moment-generating function of an almost-everywhere measurable random variable under an
s-finite measure is a measurable function of its argument. -/
@[fun_prop]
theorem measurable_mgf [SFinite μ] {X : Ω → ℝ} (hX : AEMeasurable X μ) : Measurable (mgf X μ) := by
  have h_eq : mgf X μ = mgf (hX.mk X) μ := funext fun _ ↦ mgf_congr hX.ae_eq_mk
  rw [h_eq]
  have h : Measurable fun p : ℝ × Ω ↦ exp (p.1 * hX.mk X p.2) :=
    measurable_exp.comp (measurable_fst.mul (hX.measurable_mk.comp measurable_snd))
  exact (h.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

/-- The cumulant generating function of an almost-everywhere measurable random variable under an
s-finite measure is a measurable function of its argument. -/
@[fun_prop]
theorem measurable_cgf [SFinite μ] {X : Ω → ℝ} (hX : AEMeasurable X μ) : Measurable (cgf X μ) := by
  unfold cgf
  exact (measurable_mgf hX).log

/-- **Chernoff's bound**: if `exp (t Y)` is integrable and the moment-generating function of `Y`
at `t ≥ 0` is at most `exp K`, then `P(ε ≤ Y) ≤ exp (-t ε + K)`. -/
theorem measureReal_ge_le_exp_of_mgf_le [IsFiniteMeasure μ] {Y : Ω → ℝ} {t ε K : ℝ}
    (ht : 0 ≤ t) (h_int : Integrable (fun ω ↦ exp (t * Y ω)) μ) (hK : mgf Y μ t ≤ exp K) :
    μ.real {ω | ε ≤ Y ω} ≤ exp (-t * ε + K) := by
  refine (measure_ge_le_exp_mul_mgf ε ht h_int).trans ?_
  rw [exp_add]
  gcongr

end ProbabilityTheory
