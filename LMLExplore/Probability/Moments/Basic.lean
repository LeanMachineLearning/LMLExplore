/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.Basic

/-!
# Moment-generating functions of sums and Chernoff bounds

Small general facts about moment-generating functions and tail probabilities of real random
variables, shared by the concentration inequalities of the library.

## Main statements

* `ProbabilityTheory.iIndepFun.mgf_sum_eq_prod_of_mem`: the moment-generating function of a sum
  of independent random variables over a `Finset` is the product of their moment-generating
  functions, assuming measurability only on the `Finset`.
* `ProbabilityTheory.measurable_mgf`, `ProbabilityTheory.measurable_cgf`: for an s-finite measure,
  the moment-generating and cumulant generating functions are measurable functions of their
  argument.
* `ProbabilityTheory.measureReal_ge_le_exp_of_mgf_le`: Chernoff's bound
  `P(ε ≤ Y) ≤ exp (-t ε + K)` when `exp (t Y)` is integrable, `mgf Y μ t ≤ exp K` and `t ≥ 0`.
* `MeasureTheory.measureReal_abs_ge_le_add`: the union bound over both tails,
  `P(ε ≤ |f|) ≤ P(ε ≤ f) + P(ε ≤ -f)`.
-/

public section

open MeasureTheory Real

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The union bound over both tails: `P(ε ≤ |f|) ≤ P(ε ≤ f) + P(ε ≤ -f)`. -/
theorem measureReal_abs_ge_le_add (f : Ω → ℝ) (ε : ℝ) :
    μ.real {ω | ε ≤ |f ω|} ≤ μ.real {ω | ε ≤ f ω} + μ.real {ω | ε ≤ -f ω} := by
  have : {ω | ε ≤ |f ω|} = {ω | ε ≤ f ω} ∪ {ω | ε ≤ -f ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs', le_neg, or_comm]
  rw [this]
  exact measureReal_union_le _ _

end MeasureTheory

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The moment-generating function of `∑ i ∈ s, X i` for independent `X i` is the product of
the moment-generating functions of the `X i`, `i ∈ s`. Unlike `iIndepFun.mgf_sum₀`, only the
`X i` with `i ∈ s` need to be almost-everywhere measurable. -/
theorem iIndepFun.mgf_sum_eq_prod_of_mem {X : ι → Ω → ℝ} {s : Finset ι} {t : ℝ}
    (h_indep : iIndepFun X μ) (hX : ∀ i ∈ s, AEMeasurable (X i) μ) :
    mgf (fun ω ↦ ∑ i ∈ s, X i ω) μ t = ∏ i ∈ s, mgf (X i) μ t := by
  rw [← Finset.prod_coe_sort s (fun i ↦ mgf (X i) μ t),
    ← (h_indep.precomp Subtype.val_injective).mgf_sum₀ (fun i : s ↦ hX i i.2) Finset.univ]
  congr with ω
  rw [Finset.sum_apply, Finset.sum_coe_sort s fun i ↦ X i ω]

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
