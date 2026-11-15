/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Distributions.Exponential
public import TauCeti.Probability.Distributions.Hypoexponential.Basic
public import LMLExplore.Probability.Kernel.SegmentUniform
public import TauCeti.Probability.Distributions.Uniform.Basic
import LMLExplore.Probability.Distributions.Gamma
import LMLExplore.Probability.Distributions.Uniform
import TauCeti.MeasureTheory.Measure.Mixture.Basic
import TauCeti.Probability.Distributions.Beta.Uniform
import TauCeti.Probability.Distributions.Gamma.Beta
import TauCeti.Probability.Distributions.Gamma.Measurability
import TauCeti.Probability.Distributions.Hypoexponential.PDF

/-!
# Exponential laws and the sum of two independent exponential variables

Facts about Mathlib's exponential laws `expMeasure l`: they are finite measures, and those with
positive rates are equivalent. The sum of two independent exponential variables of rates `l₁` and
`l₂` has Tau Ceti's hypoexponential law, which is `Gamma(2, l)` when `l₁ = l₂ = l` and has the
density `l₁ l₂ (exp (- l₁ x) - exp (- l₂ x)) / (l₂ - l₁)` on `(0, ∞)` when `l₁ ≠ l₂`. In the
second case it is the mixture of the laws `Gamma(2, 1 / m)` over the mean `m` uniform between
`1 / l₁` and `1 / l₂`. In the first case, given the sum `s`, the first variable is uniform on
`[0, s]`: `Exp(l) ⊗ Exp(l)` is `ProbabilityTheory.Kernel.segmentUniform ∘ₘ Gamma(2, l)`.

## Main statements

* `ProbabilityTheory.isFiniteMeasure_expMeasure`: exponential laws are finite measures.
* `ProbabilityTheory.expMeasure_absolutelyContinuous`,
  `ProbabilityTheory.prod_expMeasure_absolutelyContinuous`: exponential laws, and their products,
  with positive rates are equivalent.
* `ProbabilityTheory.map_add_prod_expMeasure_self`: `Exp(l) + Exp(l)` has the law `Gamma(2, l)`.
* `ProbabilityTheory.segmentUniform_comp_gammaMeasure`: given the sum `s`, two independent
  `Exp(l)` variables are uniform on the segment of the pairs with sum `s`.
* `ProbabilityTheory.map_add_prod_expMeasure_eq_hypoexponentialMeasure`: `Exp(l₁) + Exp(l₂)` has
  the hypoexponential law of rates `l₁, l₂`.
* `ProbabilityTheory.map_add_prod_expMeasure_eq_withDensity`: its density for `l₁ ≠ l₂`.
* `ProbabilityTheory.map_add_prod_expMeasure_eq_bind`: for `l₁ ≠ l₂`, it is the mixture of the
  laws `Gamma(2, 1 / m)` over `m` uniform between `1 / l₁` and `1 / l₂`.
-/

public section

open MeasureTheory Set Real TauCeti.Probability

namespace ProbabilityTheory

variable {l l₁ l₂ : ℝ}

/-- Exponential laws are finite measures: probability measures for a positive rate, and the zero
measure otherwise. -/
instance isFiniteMeasure_expMeasure (l : ℝ) : IsFiniteMeasure (expMeasure l) := by
  rcases le_or_gt l 0 with hl | hl
  · rw [expMeasure_of_nonpos hl]
    infer_instance
  · have := isProbabilityMeasure_expMeasure hl
    infer_instance

/-- Exponential laws with positive rates are equivalent. -/
theorem expMeasure_absolutelyContinuous (l : ℝ) {l' : ℝ} (hl' : 0 < l') :
    expMeasure l ≪ expMeasure l' := by
  rw [expMeasure_eq_withDensity_restrict_Ioi l, expMeasure_eq_withDensity_restrict_Ioi l']
  refine (withDensity_absolutelyContinuous _ _).trans (withDensity_absolutelyContinuous'
    (measurable_exponentialPDFReal l').ennreal_ofReal.aemeasurable ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (ENNReal.ofReal_pos.mpr (exponentialPDFReal_pos hl' hx)).ne'

/-- Products of exponential laws with positive rates are equivalent. -/
theorem prod_expMeasure_absolutelyContinuous (l₁ l₂ : ℝ) {l₁' l₂' : ℝ} (h₁ : 0 < l₁')
    (h₂ : 0 < l₂') :
    (expMeasure l₁).prod (expMeasure l₂) ≪ (expMeasure l₁').prod (expMeasure l₂') :=
  (expMeasure_absolutelyContinuous l₁ h₁).prod (expMeasure_absolutelyContinuous l₂ h₂)

/-- The sum of two independent `Exp(l)` variables has the law `Gamma(2, l)`. -/
theorem map_add_prod_expMeasure_self (hl : 0 < l) :
    ((expMeasure l).prod (expMeasure l)).map (fun x ↦ x.1 + x.2) = gammaMeasure 2 l := by
  have : IsProbabilityMeasure (betaMeasure 1 1) := by rw [betaMeasure_one_one]; infer_instance
  have h := congrArg (Measure.map Prod.snd) (map_div_add_prod_gammaMeasure one_pos one_pos hl)
  rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod, measure_univ,
    one_smul, one_add_one_eq_two] at h
  exact h

/-- **The conditional law given the sum under the null**: two independent `Exp(l)` variables are
`(u * s, (1 - u) * s)` for a sum `s` of law `Gamma(2, l)` and an independent uniform `u`. -/
theorem segmentUniform_comp_gammaMeasure (hl : 0 < l) :
    Kernel.segmentUniform ∘ₘ gammaMeasure 2 l = (expMeasure l).prod (expMeasure l) := by
  have h := map_div_add_prod_gammaMeasure one_pos one_pos hl
  rw [betaMeasure_one_one, one_add_one_eq_two] at h
  rw [Kernel.segmentUniform_comp, ← h, Measure.map_map (by fun_prop) (by fun_prop)]
  conv_rhs => rw [← Measure.map_id (μ := (expMeasure l).prod (expMeasure l))]
  refine Measure.map_congr ?_
  filter_upwards [ae_mem_prod_Ioi_gammaMeasure (a := 1) (r := l) (b := 1) (s := l)] with z hz
  have hz0 : z.1 + z.2 ≠ 0 := (add_pos hz.1 hz.2).ne'
  refine Prod.ext ?_ ?_
  · simp [field]
  · simp [field]

/-- **The sum of two independent exponential variables is hypoexponential**: for positive rates
`l₁, l₂`, the law of the sum under `Exp(l₁) ⊗ Exp(l₂)` is `hypoexponentialMeasure ![l₁, l₂]`. -/
theorem map_add_prod_expMeasure_eq_hypoexponentialMeasure (h₁ : 0 < l₁) (h₂ : 0 < l₂) :
    ((expMeasure l₁).prod (expMeasure l₂)).map (fun x ↦ x.1 + x.2) =
      hypoexponentialMeasure ![l₁, l₂] := by
  have hr : ∀ i, 0 < ![l₁, l₂] i := by simp [Fin.forall_fin_two, h₁, h₂]
  have hpi : (fun i ↦ expMeasure (![l₁, l₂] i)) = ![expMeasure l₁, expMeasure l₂] := by
    ext i : 1
    fin_cases i <;> rfl
  rw [hypoexponentialMeasure_eq_map hr, hpi,
    ← (measurePreserving_finTwoArrow_vec (expMeasure l₁) (expMeasure l₂)).map_eq,
    Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  congr 1
  ext x
  simp [Fin.sum_univ_two, MeasurableEquiv.finTwoArrow]

/-- **The density of the sum of two exponential variables** with distinct positive rates
`l₁, l₂` is `l₁ l₂ (exp (- l₁ x) - exp (- l₂ x)) / (l₂ - l₁)` on `(0, ∞)`. -/
theorem map_add_prod_expMeasure_eq_withDensity (h₁ : 0 < l₁) (h₂ : 0 < l₂) (h : l₁ ≠ l₂) :
    ((expMeasure l₁).prod (expMeasure l₂)).map (fun x ↦ x.1 + x.2) =
      (volume.restrict (Ioi 0)).withDensity fun x ↦
        ENNReal.ofReal (l₁ * l₂ * (exp (-(l₁ * x)) - exp (-(l₂ * x))) / (l₂ - l₁)) := by
  have hr : ∀ i, 0 < ![l₁, l₂] i := by simp [Fin.forall_fin_two, h₁, h₂]
  have hinj : Function.Injective ![l₁, l₂] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  rw [map_add_prod_expMeasure_eq_hypoexponentialMeasure h₁ h₂,
    ← Measure.restrict_eq_self_of_ae_mem (s := Ioi 0)
      (μ := hypoexponentialMeasure ![l₁, l₂]) (ae_pos_hypoexponentialMeasure _),
    hypoexponentialMeasure_eq_withDensity, restrict_withDensity measurableSet_Ioi]
  refine withDensity_congr_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
    (ae_of_all _ fun x (hx : 0 < x) ↦ ?_))
  rw [hypoexponentialPDF_eq_ofReal, hypoexponentialPDFReal_of_injective hr hinj hx]
  have h01 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have h10 : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  have h12 : l₂ - l₁ ≠ 0 := sub_ne_zero.mpr h.symm
  have h21 : l₁ - l₂ ≠ 0 := sub_ne_zero.mpr h
  simp only [Fin.sum_univ_two, h01, h10, Finset.prod_singleton, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  congr 1
  field_simp
  ring

/-- The density of the mixture of the laws `Gamma(2, 1 / m)` over the mean `m` uniform between
`1 / l₁` and `1 / l₂`, at `x > 0`. -/
private lemma lintegral_gammaPDF_uniformMeasure (h₁ : 0 < l₁) (h₂ : 0 < l₂) (h : l₁ ≠ l₂)
    {x : ℝ} (hx : 0 < x) :
    ∫⁻ m, gammaPDF 2 m⁻¹ x ∂uniformMeasure (min l₁⁻¹ l₂⁻¹) (max l₁⁻¹ l₂⁻¹) =
      ENNReal.ofReal (l₁ * l₂ * (exp (-(l₁ * x)) - exp (-(l₂ * x))) / (l₂ - l₁)) := by
  have hpos : ∀ m ∈ uIcc l₁⁻¹ l₂⁻¹, 0 < m := fun m hm ↦
    (lt_inf_iff.mpr ⟨inv_pos.mpr h₁, inv_pos.mpr h₂⟩).trans_le hm.1
  have hderiv : ∀ m ∈ uIcc l₁⁻¹ l₂⁻¹, HasDerivAt (fun m ↦ exp (-(m⁻¹ * x)))
      (exp (-(m⁻¹ * x)) * ((m ^ 2)⁻¹ * x)) m :=
    fun m hm ↦ (((hasDerivAt_inv (hpos m hm).ne').mul_const x).neg.exp).congr_deriv
      (by simp only [Pi.neg_apply]; ring)
  have hcont : ContinuousOn (fun m ↦ exp (-(m⁻¹ * x)) * ((m ^ 2)⁻¹ * x)) (uIcc l₁⁻¹ l₂⁻¹) := by
    refine ContinuousOn.mul (by fun_prop (disch := exact fun m hm ↦ (hpos m hm).ne')) ?_
    fun_prop (disch := exact fun m hm ↦ pow_ne_zero 2 (hpos m hm).ne')
  have hpdf : ∀ᵐ m ∂uniformMeasure (min l₁⁻¹ l₂⁻¹) (max l₁⁻¹ l₂⁻¹), gammaPDF 2 m⁻¹ x =
      ENNReal.ofReal (exp (-(m⁻¹ * x)) * ((m ^ 2)⁻¹ * x)) := by
    filter_upwards [ae_mem_Ioc_uniformMeasure] with m hm
    rw [gammaPDF_two hx.le]
    congr 1
    ring
  rw [lintegral_congr_ae hpdf, lintegral_ofReal_uniformMeasure_min_max_of_hasDerivAt
    (inv_injective.ne h) hderiv hcont fun m hm ↦ ?_]
  · have h12 : l₂ - l₁ ≠ 0 := sub_ne_zero.mpr h.symm
    have h21 : l₁ - l₂ ≠ 0 := sub_ne_zero.mpr h
    simp only [inv_inv]
    congr 1
    field_simp
    ring
  · have := hpos m (uIoc_subset_uIcc hm)
    positivity

/-- **The sum of two exponential variables is a mixture of gamma laws**: for distinct positive
rates, the law of the sum is the mixture of the laws `Gamma(2, 1 / m)` over the mean `m` uniform
between `1 / l₁` and `1 / l₂`. -/
theorem map_add_prod_expMeasure_eq_bind (h₁ : 0 < l₁) (h₂ : 0 < l₂) (h : l₁ ≠ l₂) :
    ((expMeasure l₁).prod (expMeasure l₂)).map (fun x ↦ x.1 + x.2) =
      (uniformMeasure (min l₁⁻¹ l₂⁻¹) (max l₁⁻¹ l₂⁻¹)).bind fun m ↦ gammaMeasure 2 m⁻¹ := by
  simp_rw [gammaMeasure_eq_withDensity_restrict_Ioi]
  have hf : Measurable (Function.uncurry fun m x ↦ gammaPDF 2 m⁻¹ x) :=
    measurable_uncurry_gammaPDF.comp (f := fun p : ℝ × ℝ ↦ (((2 : ℝ), p.1⁻¹), p.2)) (by fun_prop)
  rw [map_add_prod_expMeasure_eq_withDensity h₁ h₂ h, Measure.bind_withDensity _ _ hf]
  refine withDensity_congr_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
    (ae_of_all _ fun x (hx : 0 < x) ↦ ?_))
  exact (lintegral_gammaPDF_uniformMeasure h₁ h₂ h hx).symm

end ProbabilityTheory
