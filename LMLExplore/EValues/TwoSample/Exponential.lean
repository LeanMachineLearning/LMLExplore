/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Numeraire.Conditional
public import Mathlib.Probability.Distributions.Exponential
public import TauCeti.Probability.Distributions.Uniform.Basic
import TauCeti.MeasureTheory.Measure.Mixture.Basic
import TauCeti.Probability.Distributions.Beta.Uniform
import TauCeti.Probability.Distributions.Gamma.Beta
import TauCeti.Probability.Distributions.Gamma.Measurability
import TauCeti.Probability.Distributions.Gamma.PDF
import TauCeti.Probability.Distributions.Hypoexponential.PDF

/-!
# The numeraire of two exponential observations against a common rate

Two independent observations `X₁, X₂` have the laws `Exp(l₁)` and `Exp(l₂)`, and the null
hypothesis is that they have a common, unknown rate: it is the set of the products
`Exp(l) ⊗ Exp(l)`, `l > 0`. This is the two-sample test with a common nuisance parameter
of [HGLLA24] for the exponential family.

Under every member of the null, the sum `s = X₁ + X₂` has the law `Gamma(2, l)` and, given `s`,
the first observation is uniform on `[0, s]` and the second one is `s - X₁`: the conditional law
given the sum is `ProbabilityTheory.Kernel.segmentUniform s` for every member. For the alternative
`Q = Exp(l₁) ⊗ Exp(l₂)`, let `Qᶜ = Kernel.segmentUniform ∘ₘ Q.map (x.1 + x.2)` be the law under
which the sum has its law under `Q` and, given the sum `s`, the first observation is uniform on
`[0, s]`. Then:

* the likelihood ratio of `Q` to `Qᶜ`, the conditional e-variable of [HGLLA24], is the numeraire
  of the null under `Q`, and `Qᶜ` is the reverse information projection of `Q` on the null;
* for `l₁ ≠ l₂`, `Qᶜ` is the mixture of the members `Exp(1 / m) ⊗ Exp(1 / m)` of the null whose
  mean `m` is uniform between `1 / l₁` and `1 / l₂`;
* no finite combination of members of the null is equal to it, against the conjecture of
  [HGLLA24, §5.2].

## Main definitions

* `ProbabilityTheory.Kernel.segmentUniform`: the law of `(u * s, (1 - u) * s)` for `u` uniform
  on `[0, 1]`.

## Main statements

* `ProbabilityTheory.isNumeraire_rnDeriv_segmentUniform_comp`: the likelihood ratio of `Q` to
  `Qᶜ` is the numeraire.
* `ProbabilityTheory.ripr_prod_expMeasure`: `Qᶜ` is the reverse information projection.
* `ProbabilityTheory.segmentUniform_comp_map_add_prod_expMeasure`: `Qᶜ` is the mixture of the
  members of the null whose mean is uniform between the two means.
* `ProbabilityTheory.sum_smul_prod_expMeasure_ne_ripr`: no finite combination of members of the
  null is the reverse information projection.

## Implementation notes

That the law of the sum and the conditional law given the sum are as described under the null is
the beta–gamma algebra of Tau Ceti (`TauCeti.Probability.map_div_add_prod_gammaMeasure`). The law
of the sum under `Q` is Tau Ceti's hypoexponential law, with density
`l₁ l₂ (exp (- l₁ x) - exp (- l₂ x)) / (l₂ - l₁)` on `(0, ∞)`, which is also the density of the
mixture of the laws `Gamma(2, 1 / m)` over the uniform mean `m`. The numeraire is then identified
through the effective null: the likelihood ratio is an e-variable by
`ProbabilityTheory.isEVar_rnDeriv_comp_map`, and `Qᶜ` is a mixture of members of the null, so
that `ProbabilityTheory.isNumeraire_of_ae_eq_rnDeriv` and
`ProbabilityTheory.ripr_eq_of_isEVar_rnDeriv` apply. For the last statement, a finite combination
of the laws `Gamma(2, l)` has a density `∑ c l * l ^ 2 * x * exp (- l x)`, which decays either too
slowly or too fast at infinity compared to `exp (- min l₁ l₂ * x)`.

## References

* [HGLLA24] Y. Hao, P. Grünwald, T. Lardy, L. Long and R. Adams, *E-values for k-sample tests
  with exponential families*, arXiv:2303.00471, §5.2.
* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4, Theorem 4.1.
-/

public section

open MeasureTheory Set Filter Real TauCeti.Probability

open scoped ENNReal Topology

namespace ProbabilityTheory

/-! ### The uniform law on a segment -/

/-- **The uniform law on a segment**: for `s : ℝ`, the law of `(u * s, (1 - u) * s)` for `u`
uniform on `[0, 1]`. For `s ≥ 0`, its first coordinate is uniform on `[0, s]` and the two
coordinates add up to `s`. -/
noncomputable def Kernel.segmentUniform : Kernel ℝ (ℝ × ℝ) :=
  (Kernel.id ×ₖ Kernel.const ℝ (uniformMeasure 0 1)).map fun p ↦ (p.2 * p.1, (1 - p.2) * p.1)

/-- The uniform law on a segment is a Markov kernel. -/
instance Kernel.isMarkovKernel_segmentUniform : IsMarkovKernel Kernel.segmentUniform := by
  unfold Kernel.segmentUniform
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The uniform law on the segment of the pairs with sum `s`. -/
theorem Kernel.segmentUniform_apply (s : ℝ) :
    Kernel.segmentUniform s = (uniformMeasure 0 1).map fun u ↦ (u * s, (1 - u) * s) := by
  rw [Kernel.segmentUniform, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The mixture of the uniform laws on the segments against a law `ν` of the sum is the image of
`uniformMeasure 0 1 ⊗ ν` under `(u, s) ↦ (u * s, (1 - u) * s)`. -/
theorem Kernel.segmentUniform_comp (ν : Measure ℝ) [SFinite ν] :
    Kernel.segmentUniform ∘ₘ ν =
      ((uniformMeasure 0 1).prod ν).map fun p ↦ (p.1 * p.2, (1 - p.1) * p.2) := by
  rw [Kernel.segmentUniform, ← Measure.map_comp _ _ (by fun_prop), ← Measure.compProd_eq_comp_prod,
    Measure.compProd_const, ← Measure.prod_swap, Measure.map_map (by fun_prop) measurable_swap]
  rfl

/-- Under the uniform law on the segment of the pairs with sum `s`, the coordinates add up to
`s`. -/
theorem Kernel.ae_add_segmentUniform (s : ℝ) : ∀ᵐ x ∂Kernel.segmentUniform s, x.1 + x.2 = s := by
  rw [Kernel.segmentUniform_apply,
    ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) measurable_const)]
  exact ae_of_all _ fun u ↦ by ring

/-! ### The null of two exponential observations with a common rate -/

section Null

variable {l l₁ l₂ : ℝ}

/-- Exponential laws are s-finite. -/
private instance sFinite_expMeasure (l : ℝ) : SFinite (expMeasure l) :=
  inferInstanceAs (SFinite (gammaMeasure 1 l))

/-- Exponential laws with positive rates are equivalent. -/
private lemma expMeasure_absolutelyContinuous (l : ℝ) {l' : ℝ} (hl' : 0 < l') :
    expMeasure l ≪ expMeasure l' := by
  rw [expMeasure_eq_withDensity_restrict_Ioi l, expMeasure_eq_withDensity_restrict_Ioi l']
  refine (withDensity_absolutelyContinuous _ _).trans (withDensity_absolutelyContinuous'
    (measurable_exponentialPDFReal l').ennreal_ofReal.aemeasurable ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (ENNReal.ofReal_pos.mpr (exponentialPDFReal_pos hl' hx)).ne'

/-- Products of exponential laws with positive rates are equivalent. -/
private lemma prod_expMeasure_absolutelyContinuous (l₁ l₂ : ℝ) {l₁' l₂' : ℝ} (h₁ : 0 < l₁')
    (h₂ : 0 < l₂') :
    (expMeasure l₁).prod (expMeasure l₂) ≪ (expMeasure l₁').prod (expMeasure l₂') :=
  (expMeasure_absolutelyContinuous l₁ h₁).prod (expMeasure_absolutelyContinuous l₂ h₂)

/-- The sum of two independent `Exp(l)` variables has the law `Gamma(2, l)`. -/
private lemma map_add_prod_expMeasure_self (hl : 0 < l) :
    ((expMeasure l).prod (expMeasure l)).map (fun x ↦ x.1 + x.2) = gammaMeasure 2 l := by
  have : IsProbabilityMeasure (betaMeasure 1 1) := by rw [betaMeasure_one_one]; infer_instance
  have h := congrArg (Measure.map Prod.snd) (map_div_add_prod_gammaMeasure one_pos one_pos hl)
  rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod, measure_univ,
    one_smul, one_add_one_eq_two] at h
  exact h

/-- **The conditional law given the sum under the null**: two independent `Exp(l)` variables are
`(u * s, (1 - u) * s)` for a sum `s` of law `Gamma(2, l)` and an independent uniform `u`. -/
private lemma segmentUniform_comp_gammaMeasure (hl : 0 < l) :
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

/-- Every member of the null is its own `Qᶜ`. -/
private lemma segmentUniform_comp_map_add_prod_expMeasure_self (hl : 0 < l) :
    Kernel.segmentUniform ∘ₘ ((expMeasure l).prod (expMeasure l)).map (fun x ↦ x.1 + x.2) =
      (expMeasure l).prod (expMeasure l) := by
  rw [map_add_prod_expMeasure_self hl, segmentUniform_comp_gammaMeasure hl]

/-- `Exp(l₁) ⊗ Exp(l₂)` and its `Qᶜ` are equivalent: both are equivalent to `Exp(1) ⊗ Exp(1)`,
which is its own `Qᶜ`. -/
private lemma absolutelyContinuous_segmentUniform_comp (h₁ : 0 < l₁) (h₂ : 0 < l₂) :
    (expMeasure l₁).prod (expMeasure l₂) ≪
        Kernel.segmentUniform ∘ₘ ((expMeasure l₁).prod (expMeasure l₂)).map (fun x ↦ x.1 + x.2) ∧
      Kernel.segmentUniform ∘ₘ ((expMeasure l₁).prod (expMeasure l₂)).map (fun x ↦ x.1 + x.2) ≪
        (expMeasure l₁).prod (expMeasure l₂) := by
  have h1 := segmentUniform_comp_map_add_prod_expMeasure_self (l := 1) one_pos
  refine ⟨(prod_expMeasure_absolutelyContinuous l₁ l₂ one_pos one_pos).trans ?_, ?_⟩
  · rw [← h1]
    exact ((prod_expMeasure_absolutelyContinuous 1 1 h₁ h₂).map (by fun_prop)).comp_right _
  · refine (((prod_expMeasure_absolutelyContinuous l₁ l₂ one_pos one_pos).map
      (by fun_prop)).comp_right _).trans ?_
    rw [h1]
    exact prod_expMeasure_absolutelyContinuous 1 1 h₁ h₂

/-- The members of the null are probability measures. -/
private lemma isProbabilityMeasure_of_mem_null {P : Measure (ℝ × ℝ)}
    (hP : P ∈ Set.range fun l : Ioi (0 : ℝ) ↦ (expMeasure l).prod (expMeasure l)) :
    IsProbabilityMeasure P := by
  obtain ⟨⟨l, hl⟩, rfl⟩ := hP
  have := isProbabilityMeasure_expMeasure hl
  infer_instance

/-- Every member of the null has the conditional law `Kernel.segmentUniform` given the sum. -/
private lemma segmentUniform_comp_map_add_of_mem {P : Measure (ℝ × ℝ)}
    (hP : P ∈ Set.range fun l : Ioi (0 : ℝ) ↦ (expMeasure l).prod (expMeasure l)) :
    Kernel.segmentUniform ∘ₘ P.map (fun x ↦ x.1 + x.2) = P := by
  obtain ⟨⟨l, hl⟩, rfl⟩ := hP
  exact segmentUniform_comp_map_add_prod_expMeasure_self hl

/-- Under every member of the null, the law of the sum is absolutely continuous with respect to
its law under `Exp(l₁) ⊗ Exp(l₂)`. -/
private lemma map_add_absolutelyContinuous_of_mem (h₁ : 0 < l₁) (h₂ : 0 < l₂)
    {P : Measure (ℝ × ℝ)}
    (hP : P ∈ Set.range fun l : Ioi (0 : ℝ) ↦ (expMeasure l).prod (expMeasure l)) :
    P.map (fun x ↦ x.1 + x.2) ≪
      ((expMeasure l₁).prod (expMeasure l₂)).map (fun x ↦ x.1 + x.2) := by
  obtain ⟨⟨l, hl⟩, rfl⟩ := hP
  exact (prod_expMeasure_absolutelyContinuous l l h₁ h₂).map (by fun_prop)

/-! ### The law of the sum and the mixture -/

/-- The density on `(0, ∞)` of the sum of two independent exponential variables with distinct
rates `l₁, l₂`. -/
private noncomputable def sumDensity (l₁ l₂ x : ℝ) : ℝ :=
  l₁ * l₂ * (exp (-(l₁ * x)) - exp (-(l₂ * x))) / (l₂ - l₁)

/-- The density of the sum is nonnegative on `[0, ∞)`. -/
private lemma sumDensity_nonneg (h₁ : 0 < l₁) (h₂ : 0 < l₂) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ sumDensity l₁ l₂ x := by
  unfold sumDensity
  rcases le_total l₁ l₂ with h | h
  · exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr (exp_le_exp.mpr
      (by nlinarith)))) (sub_nonneg.mpr h)
  · exact div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (sub_nonpos.mpr (exp_le_exp.mpr (by nlinarith)))) (sub_nonpos.mpr h)

/-- **The law of the sum of two exponential variables** with distinct rates `l₁, l₂` has density
`l₁ l₂ (exp (- l₁ x) - exp (- l₂ x)) / (l₂ - l₁)` on `(0, ∞)`. -/
private lemma map_add_prod_expMeasure (h₁ : 0 < l₁) (h₂ : 0 < l₂) (h : l₁ ≠ l₂) :
    ((expMeasure l₁).prod (expMeasure l₂)).map (fun x ↦ x.1 + x.2) =
      (volume.restrict (Ioi 0)).withDensity fun x ↦ ENNReal.ofReal (sumDensity l₁ l₂ x) := by
  have := isProbabilityMeasure_expMeasure h₁
  have := isProbabilityMeasure_expMeasure h₂
  have hr : ∀ i, 0 < ![l₁, l₂] i := by simp [Fin.forall_fin_two, h₁, h₂]
  have hinj : Function.Injective ![l₁, l₂] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hpi : (fun i ↦ expMeasure (![l₁, l₂] i)) = ![expMeasure l₁, expMeasure l₂] := by
    ext i : 1
    fin_cases i <;> rfl
  have hmap : ((expMeasure l₁).prod (expMeasure l₂)).map (fun x ↦ x.1 + x.2) =
      hypoexponentialMeasure ![l₁, l₂] := by
    rw [hypoexponentialMeasure_eq_map hr, hpi,
      ← (measurePreserving_finTwoArrow_vec (expMeasure l₁) (expMeasure l₂)).map_eq,
      Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
    congr 1
    ext x
    simp [Fin.sum_univ_two, MeasurableEquiv.finTwoArrow]
  rw [hmap, ← Measure.restrict_eq_self_of_ae_mem (s := Ioi 0)
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
    Matrix.cons_val_one, sumDensity]
  congr 1
  field_simp
  ring

/-- The density of `Gamma(2, r)` on `[0, ∞)`. -/
private lemma gammaPDF_two {r x : ℝ} (hx : 0 ≤ x) :
    gammaPDF 2 r x = ENNReal.ofReal (r ^ 2 * x * exp (-(r * x))) := by
  rw [gammaPDF_of_nonneg hx, Real.Gamma_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.rpow_two, div_one]

/-- The uniform law on `(a, b]` lives on `(a, b]`. -/
private lemma ae_mem_Ioc_uniformMeasure (a b : ℝ) : ∀ᵐ m ∂uniformMeasure a b, m ∈ Ioc a b := by
  rw [uniformMeasure_eq_smul]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioc) _

/-- The density of the mixture of the laws `Gamma(2, 1 / m)` over the uniform mean `m`. -/
private lemma lintegral_gammaPDF_uniformMeasure (h₁ : 0 < l₁) (h₂ : 0 < l₂) (h : l₁ ≠ l₂)
    {x : ℝ} (hx : 0 < x) :
    ∫⁻ m, gammaPDF 2 m⁻¹ x ∂uniformMeasure (min l₁⁻¹ l₂⁻¹) (max l₁⁻¹ l₂⁻¹) =
      ENNReal.ofReal (sumDensity l₁ l₂ x) := by
  set α := min l₁⁻¹ l₂⁻¹
  set β := max l₁⁻¹ l₂⁻¹
  have hα : 0 < α := lt_min (inv_pos.mpr h₁) (inv_pos.mpr h₂)
  have hαβ : α < β := min_lt_max.mpr (inv_injective.ne h)
  have hpos : ∀ m ∈ uIcc α β, 0 < m := fun m hm ↦ hα.trans_le (by
    rw [uIcc_of_le hαβ.le] at hm; exact hm.1)
  have hderiv : ∀ m ∈ uIcc α β, HasDerivAt (fun m ↦ exp (-(m⁻¹ * x)))
      (exp (-(m⁻¹ * x)) * ((m ^ 2)⁻¹ * x)) m :=
    fun m hm ↦ (((hasDerivAt_inv (hpos m hm).ne').mul_const x).neg.exp).congr_deriv
      (by simp only [Pi.neg_apply]; ring)
  have hcont : ContinuousOn (fun m ↦ exp (-(m⁻¹ * x)) * ((m ^ 2)⁻¹ * x)) (uIcc α β) := by
    refine ContinuousOn.mul (by fun_prop (disch := exact fun m hm ↦ (hpos m hm).ne')) ?_
    fun_prop (disch := exact fun m hm ↦ pow_ne_zero 2 (hpos m hm).ne')
  have hpdf : ∀ m ∈ Ioc α β, gammaPDF 2 m⁻¹ x =
      ENNReal.ofReal (exp (-(m⁻¹ * x)) * ((m ^ 2)⁻¹ * x)) := by
    intro m hm
    rw [gammaPDF_two hx.le]
    congr 1
    ring
  rw [uniformMeasure_eq_smul, lintegral_smul_measure, setLIntegral_congr_fun measurableSet_Ioc hpdf,
    ← ofReal_integral_eq_lintegral_ofReal, ← intervalIntegral.integral_of_le hαβ.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable,
    smul_eq_mul, ← ENNReal.ofReal_inv_of_pos (sub_pos.mpr hαβ),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (sub_pos.mpr hαβ).le)]
  · congr 1
    have h12 : l₂ - l₁ ≠ 0 := sub_ne_zero.mpr h.symm
    rcases h.lt_or_gt with h' | h'
    · have hinv : l₂⁻¹ ≤ l₁⁻¹ := (inv_strictAnti₀ h₁ h').le
      simp only [α, β, min_eq_right hinv, max_eq_left hinv, inv_inv, sumDensity]
      field_simp
    · have hinv : l₁⁻¹ ≤ l₂⁻¹ := (inv_strictAnti₀ h₂ h').le
      simp only [α, β, min_eq_left hinv, max_eq_right hinv, inv_inv, sumDensity]
      field_simp
      ring
  · rw [uIcc_of_le hαβ.le] at hcont
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · refine ae_restrict_of_forall_mem measurableSet_Ioc fun m hm ↦ ?_
    have := hpos m (by rw [uIcc_of_le hαβ.le]; exact Ioc_subset_Icc_self hm)
    positivity

/-- **The sum of two exponential variables is a mixture of gamma laws**: for distinct rates, the
law of the sum is the mixture of the laws `Gamma(2, 1 / m)` over the mean `m` uniform between
`1 / l₁` and `1 / l₂`. -/
private lemma map_add_prod_expMeasure_eq_bind (h₁ : 0 < l₁) (h₂ : 0 < l₂) (h : l₁ ≠ l₂) :
    ((expMeasure l₁).prod (expMeasure l₂)).map (fun x ↦ x.1 + x.2) =
      (uniformMeasure (min l₁⁻¹ l₂⁻¹) (max l₁⁻¹ l₂⁻¹)).bind fun m ↦ gammaMeasure 2 m⁻¹ := by
  have := isProbabilityMeasure_uniformMeasure
    (min_lt_max.mpr (inv_injective.ne h) : min l₁⁻¹ l₂⁻¹ < max l₁⁻¹ l₂⁻¹)
  simp_rw [gammaMeasure_eq_withDensity_restrict_Ioi]
  have hf : Measurable (Function.uncurry fun m x ↦ gammaPDF 2 m⁻¹ x) :=
    measurable_uncurry_gammaPDF.comp (f := fun p : ℝ × ℝ ↦ (((2 : ℝ), p.1⁻¹), p.2)) (by fun_prop)
  rw [map_add_prod_expMeasure h₁ h₂ h, Measure.bind_withDensity _ _ hf]
  refine withDensity_congr_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
    (ae_of_all _ fun x (hx : 0 < x) ↦ ?_))
  exact (lintegral_gammaPDF_uniformMeasure h₁ h₂ h hx).symm

/-- The laws `Gamma(2, 1 / m)`, as a kernel. -/
private noncomputable def gammaTwoInvKernel : Kernel ℝ ℝ where
  toFun m := gammaMeasure 2 m⁻¹
  measurable' := measurable_gammaMeasure.comp (f := fun m : ℝ ↦ ((2 : ℝ), m⁻¹)) (by fun_prop)

/-- `Qᶜ` is in the effective null. -/
private lemma segmentUniform_comp_mem_effectiveSet (h₁ : 0 < l₁) (h₂ : 0 < l₂) :
    Kernel.segmentUniform ∘ₘ ((expMeasure l₁).prod (expMeasure l₂)).map (fun x ↦ x.1 + x.2) ∈
      effectiveSet (Set.range fun l : Ioi (0 : ℝ) ↦ (expMeasure l).prod (expMeasure l)) := by
  have hS : ∀ P ∈ Set.range fun l : Ioi (0 : ℝ) ↦ (expMeasure l).prod (expMeasure l),
      P univ ≤ 1 := fun P hP ↦ (isProbabilityMeasure_of_mem_null hP).measure_univ.le
  rcases eq_or_ne l₁ l₂ with rfl | h
  · rw [segmentUniform_comp_map_add_prod_expMeasure_self h₁]
    exact subset_effectiveSet hS ⟨⟨l₁, h₁⟩, rfl⟩
  have hα : 0 < min l₁⁻¹ l₂⁻¹ := lt_min (inv_pos.mpr h₁) (inv_pos.mpr h₂)
  have := isProbabilityMeasure_uniformMeasure
    (min_lt_max.mpr (inv_injective.ne h) : min l₁⁻¹ l₂⁻¹ < max l₁⁻¹ l₂⁻¹)
  rw [map_add_prod_expMeasure_eq_bind h₁ h₂ h]
  change Kernel.segmentUniform ∘ₘ (gammaTwoInvKernel ∘ₘ _) ∈ _
  rw [Measure.comp_assoc]
  refine comp_mem_effectiveSet prob_le_one ?_
  filter_upwards [ae_mem_Ioc_uniformMeasure (min l₁⁻¹ l₂⁻¹) (max l₁⁻¹ l₂⁻¹)] with m hm
  have hm0 : 0 < m⁻¹ := inv_pos.mpr (hα.trans hm.1)
  rw [Kernel.comp_apply]
  change Kernel.segmentUniform ∘ₘ gammaMeasure 2 m⁻¹ ∈ _
  rw [segmentUniform_comp_gammaMeasure hm0]
  exact subset_effectiveSet hS ⟨⟨m⁻¹, hm0⟩, rfl⟩

/-- The likelihood ratio of `Exp(l₁) ⊗ Exp(l₂)` to its `Qᶜ` is an e-variable for the null. -/
private lemma isEVar_rnDeriv_segmentUniform_comp (h₁ : 0 < l₁) (h₂ : 0 < l₂) :
    IsEVar (((expMeasure l₁).prod (expMeasure l₂)).rnDeriv
        (Kernel.segmentUniform ∘ₘ ((expMeasure l₁).prod (expMeasure l₂)).map fun x ↦ x.1 + x.2))
      (Set.range fun l : Ioi (0 : ℝ) ↦ (expMeasure l).prod (expMeasure l)) := by
  have := isProbabilityMeasure_expMeasure h₁
  have := isProbabilityMeasure_expMeasure h₂
  exact isEVar_rnDeriv_comp_map (by fun_prop) (ae_of_all _ Kernel.ae_add_segmentUniform)
    (absolutelyContinuous_segmentUniform_comp h₁ h₂).1
    (fun P hP ↦ have := isProbabilityMeasure_of_mem_null hP; inferInstance)
    (fun _ ↦ segmentUniform_comp_map_add_of_mem)
    (fun _ ↦ map_add_absolutelyContinuous_of_mem h₁ h₂)

end Null

/-! ### The numeraire and the reverse information projection -/

section Main

variable {l₁ l₂ : ℝ}

/-- **The numeraire of two exponential observations against a common rate.** For positive rates
`l₁, l₂`, the likelihood ratio of `Exp(l₁) ⊗ Exp(l₂)` to the law under which the sum of the two
observations has its law under `Exp(l₁) ⊗ Exp(l₂)` and, given the sum `s`, the first observation
is uniform on `[0, s]`, is the numeraire of the null of the products `Exp(l) ⊗ Exp(l)`, `l > 0`:
it is an e-variable, and no e-variable has a larger expected logarithm under
`Exp(l₁) ⊗ Exp(l₂)` (`ProbabilityTheory.IsNumeraire.eintegral_log_le`). -/
theorem isNumeraire_rnDeriv_segmentUniform_comp (h₁ : 0 < l₁) (h₂ : 0 < l₂) :
    IsNumeraire (((expMeasure l₁).prod (expMeasure l₂)).rnDeriv
        (Kernel.segmentUniform ∘ₘ ((expMeasure l₁).prod (expMeasure l₂)).map fun x ↦ x.1 + x.2))
      (Set.range fun l : Ioi (0 : ℝ) ↦ (expMeasure l).prod (expMeasure l))
      ((expMeasure l₁).prod (expMeasure l₂)) := by
  have := isProbabilityMeasure_expMeasure h₁
  have := isProbabilityMeasure_expMeasure h₂
  exact isNumeraire_of_ae_eq_rnDeriv (isEVar_rnDeriv_segmentUniform_comp h₁ h₂)
    (segmentUniform_comp_mem_effectiveSet h₁ h₂) (absolutelyContinuous_segmentUniform_comp h₁ h₂).1
    .rfl

/-- **The reverse information projection of two exponential observations** on the null of the
products `Exp(l) ⊗ Exp(l)`, `l > 0`, is the law under which the sum of the two observations has
its law under `Exp(l₁) ⊗ Exp(l₂)` and, given the sum `s`, the first observation is uniform on
`[0, s]`. -/
theorem ripr_prod_expMeasure (h₁ : 0 < l₁) (h₂ : 0 < l₂) :
    ripr ((expMeasure l₁).prod (expMeasure l₂))
        (Set.range fun l : Ioi (0 : ℝ) ↦ (expMeasure l).prod (expMeasure l)) =
      Kernel.segmentUniform ∘ₘ ((expMeasure l₁).prod (expMeasure l₂)).map fun x ↦ x.1 + x.2 := by
  have := isProbabilityMeasure_expMeasure h₁
  have := isProbabilityMeasure_expMeasure h₂
  exact ripr_eq_of_isEVar_rnDeriv
    (fun P hP ↦ have := isProbabilityMeasure_of_mem_null hP; inferInstance)
    (segmentUniform_comp_mem_effectiveSet h₁ h₂) (absolutelyContinuous_segmentUniform_comp h₁ h₂).1
    (absolutelyContinuous_segmentUniform_comp h₁ h₂).2 (isEVar_rnDeriv_segmentUniform_comp h₁ h₂)

/-- **The reverse information projection is a continuous mixture of members of the null.** For
distinct positive rates `l₁, l₂`, the law under which the sum of the two observations has its
law under `Exp(l₁) ⊗ Exp(l₂)` and, given the sum `s`, the first observation is uniform on
`[0, s]`, is the mixture of the members `Exp(1 / m) ⊗ Exp(1 / m)` of the null whose mean `m` is
uniform between `1 / l₁` and `1 / l₂`. -/
theorem segmentUniform_comp_map_add_prod_expMeasure (h₁ : 0 < l₁) (h₂ : 0 < l₂) (h : l₁ ≠ l₂) :
    Kernel.segmentUniform ∘ₘ ((expMeasure l₁).prod (expMeasure l₂)).map (fun x ↦ x.1 + x.2) =
      (uniformMeasure (min l₁⁻¹ l₂⁻¹) (max l₁⁻¹ l₂⁻¹)).bind
        fun m ↦ (expMeasure m⁻¹).prod (expMeasure m⁻¹) := by
  have hα : 0 < min l₁⁻¹ l₂⁻¹ := lt_min (inv_pos.mpr h₁) (inv_pos.mpr h₂)
  rw [map_add_prod_expMeasure_eq_bind h₁ h₂ h, Measure.bind_bind (f := fun m ↦ gammaMeasure 2 m⁻¹)
    gammaTwoInvKernel.measurable.aemeasurable Kernel.segmentUniform.aemeasurable]
  refine Measure.bind_congr_right ?_
  filter_upwards [ae_mem_Ioc_uniformMeasure (min l₁⁻¹ l₂⁻¹) (max l₁⁻¹ l₂⁻¹)] with m hm
  exact segmentUniform_comp_gammaMeasure (inv_pos.mpr (hα.trans hm.1))

/-- A nonnegative finite combination of the functions `x ↦ l ^ 2 * x * exp (- l x)`, `l > 0`, is
not `C (exp (- a x) - exp (- b x))` on `(0, ∞)` for `a < b` and `C > 0`: at infinity, the terms
with `l ≤ a` decay too slowly and the other ones too fast. -/
private lemma not_forall_sum_eq_mul_sub {a b C : ℝ} (hab : a < b) (hC : 0 < C) (s : Finset ℝ)
    (c : ℝ → ℝ) (hc : ∀ l ∈ s, 0 ≤ c l) (hs : ∀ l ∈ s, 0 < l) :
    ¬ ∀ x > 0, ∑ l ∈ s, c l * (l ^ 2 * x * exp (-(l * x))) =
      C * (exp (-(a * x)) - exp (-(b * x))) := by
  intro h
  have hterm : ∀ x > 0, ∀ l ∈ s, 0 ≤ c l * (l ^ 2 * x * exp (-(l * x))) := fun x hx l hl ↦ by
    have := hc l hl
    positivity
  -- the coefficients of the rates `l ≤ a` vanish
  have h0 : ∀ l ∈ s, l ≤ a → c l = 0 := by
    intro l hl hla
    by_contra hcl
    have hcl' : 0 < c l * l ^ 2 := mul_pos ((hc l hl).lt_of_ne' hcl) (pow_pos (hs l hl) 2)
    set x := 2 * C / (c l * l ^ 2) with hx_def
    have hx : 0 < x := by positivity
    have h1 := Finset.single_le_sum (hterm x hx) hl
    rw [h x hx] at h1
    have h2 : C * exp (-(a * x)) ≤ C * exp (-(l * x)) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith)) hC.le
    have h3 : 0 < C * exp (-(b * x)) := mul_pos hC (exp_pos _)
    have h4 : 0 < C * exp (-(l * x)) := mul_pos hC (exp_pos _)
    have h5 : c l * (l ^ 2 * x * exp (-(l * x))) = 2 * (C * exp (-(l * x))) := by
      have := (hs l hl).ne'
      rw [hx_def]
      field_simp
    linarith
  -- multiply by `exp (a x)` and let `x` tend to infinity
  have hlim : Tendsto (fun x ↦ ∑ l ∈ s, c l * l ^ 2 * (x * exp (-((l - a) * x)))) atTop
      (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ _l ∈ s, 0 by simp]
    refine tendsto_finsetSum _ fun l hl ↦ ?_
    by_cases hla : l ≤ a
    · simp [h0 l hl hla]
    have hε : 0 < l - a := sub_pos.mpr (not_le.mp hla)
    have := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (Tendsto.const_mul_atTop hε tendsto_id)).const_mul (c l * l ^ 2 / (l - a))
    rw [mul_zero] at this
    refine this.congr fun x ↦ ?_
    simp only [Function.comp_apply, id, pow_one]
    field_simp
  have hlim' : Tendsto (fun x ↦ C * (1 - exp (-((b - a) * x)))) atTop (𝓝 C) := by
    have : Tendsto (fun x ↦ exp (-((b - a) * x))) atTop (𝓝 0) :=
      tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop (sub_pos.mpr hab) tendsto_id)
    simpa using (this.const_sub 1).const_mul C
  refine hC.ne (tendsto_nhds_unique (hlim.congr' ?_) hlim')
  filter_upwards [eventually_gt_atTop 0] with x hx
  have key : ∀ l, exp (-((l - a) * x)) = exp (-(l * x)) * exp (a * x) := fun l ↦ by
    rw [← exp_add]
    ring_nf
  have ha : exp (-(a * x)) * exp (a * x) = 1 := by
    rw [← exp_add]
    simp
  calc ∑ l ∈ s, c l * l ^ 2 * (x * exp (-((l - a) * x)))
  _ = (∑ l ∈ s, c l * (l ^ 2 * x * exp (-(l * x)))) * exp (a * x) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [key]
    ring
  _ = C * (1 - exp (-((b - a) * x))) := by
    rw [h x hx, key b]
    linear_combination C * ha

/-- **No finite combination of members of the null is the reverse information projection.** For
distinct positive rates `l₁, l₂`, no finite combination of the laws `Exp(l) ⊗ Exp(l)` is the
reverse information projection of `Exp(l₁) ⊗ Exp(l₂)` on the null of the products
`Exp(l) ⊗ Exp(l)`, `l > 0`. In particular it is not a mixture of two members of the null, against
the conjecture of [HGLLA24, §5.2]. -/
theorem sum_smul_prod_expMeasure_ne_ripr (h₁ : 0 < l₁) (h₂ : 0 < l₂) (h : l₁ ≠ l₂)
    (s : Finset ℝ) (w : ℝ → ℝ≥0∞) :
    ∑ l ∈ s, w l • (expMeasure l).prod (expMeasure l) ≠
      ripr ((expMeasure l₁).prod (expMeasure l₂))
        (Set.range fun l : Ioi (0 : ℝ) ↦ (expMeasure l).prod (expMeasure l)) := by
  have := isProbabilityMeasure_expMeasure h₁
  have := isProbabilityMeasure_expMeasure h₂
  rw [ripr_prod_expMeasure h₁ h₂]
  intro heq
  set s' := s.filter (0 < ·) with hs'
  have hs'pos : ∀ l ∈ s', 0 < l := fun l hl ↦ (Finset.mem_filter.mp hl).2
  -- the laws of the sum agree
  have hsum : ∀ A, MeasurableSet A → ∑ l ∈ s', w l * gammaMeasure 2 l A =
      ((expMeasure l₁).prod (expMeasure l₂)).map (fun x ↦ x.1 + x.2) A := by
    intro A hA
    have h1 := congrArg (fun μ : Measure (ℝ × ℝ) ↦ μ ((fun x ↦ x.1 + x.2) ⁻¹' A)) heq
    simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul] at h1
    rw [← Measure.map_apply (by fun_prop) hA,
      map_comp_eq_of_ae_eq (by fun_prop) (ae_of_all _ Kernel.ae_add_segmentUniform)] at h1
    rw [← h1, hs', Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    split_ifs with hl
    · rw [← map_add_prod_expMeasure_self hl, Measure.map_apply (by fun_prop) hA]
    · simp [expMeasure_of_nonpos (not_lt.mp hl)]
  -- so the weights are finite
  have hw : ∀ l ∈ s', w l ≠ ∞ := by
    have hmass := hsum univ MeasurableSet.univ
    rw [measure_univ, Finset.sum_congr rfl fun l hl ↦ by
      have := isProbabilityMeasure_gammaMeasure two_pos (hs'pos l hl)
      rw [measure_univ, mul_one]] at hmass
    exact fun l hl ↦ ne_top_of_le_ne_top ENNReal.one_ne_top
      (hmass ▸ Finset.single_le_sum (fun _ _ ↦ zero_le) hl)
  -- and the densities of the laws of the sum agree on `(0, ∞)`
  have hae : (fun x ↦ ∑ l ∈ s', w l * gammaPDF 2 l x) =ᵐ[volume.restrict (Ioi 0)]
      fun x ↦ ENNReal.ofReal (sumDensity l₁ l₂ x) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      (Finset.measurable_fun_sum _ fun l _ ↦ (measurable_gammaPDF 2 l).const_mul _)
      (by unfold sumDensity; fun_prop) fun A hA _ ↦ ?_
    rw [lintegral_finsetSum _ fun l _ ↦ (measurable_gammaPDF 2 l).const_mul _,
      ← withDensity_apply _ hA, ← map_add_prod_expMeasure h₁ h₂ h, ← hsum A hA]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [lintegral_const_mul _ (measurable_gammaPDF 2 l), ← withDensity_apply _ hA,
      ← gammaMeasure_eq_withDensity_restrict_Ioi]
  have hreal : ∀ x ∈ Ioi (0 : ℝ),
      ∑ l ∈ s', (w l).toReal * (l ^ 2 * x * exp (-(l * x))) = sumDensity l₁ l₂ x := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_Ioi (by fun_prop)
      (by unfold sumDensity; fun_prop)
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with x hx (hx0 : 0 < x)
    rw [← ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun l hl ↦
      have := hs'pos l hl; by positivity) (sumDensity_nonneg h₁ h₂ hx0.le), ← hx,
      ENNReal.ofReal_sum_of_nonneg fun l hl ↦ have := hs'pos l hl; by positivity]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hw l hl),
      gammaPDF_two hx0.le]
  rcases h.lt_or_gt with h12 | h12
  · refine not_forall_sum_eq_mul_sub h12 (div_pos (mul_pos h₁ h₂) (sub_pos.mpr h12)) s'
      (fun l ↦ (w l).toReal) (fun _ _ ↦ ENNReal.toReal_nonneg) hs'pos fun x hx ↦ ?_
    rw [hreal x hx, sumDensity]
    ring
  · refine not_forall_sum_eq_mul_sub h12 (div_pos (mul_pos h₁ h₂) (sub_pos.mpr h12)) s'
      (fun l ↦ (w l).toReal) (fun _ _ ↦ ENNReal.toReal_nonneg) hs'pos fun x hx ↦ ?_
    have h21 : l₂ - l₁ ≠ 0 := sub_ne_zero.mpr h.symm
    have h12' : l₁ - l₂ ≠ 0 := sub_ne_zero.mpr h
    rw [hreal x hx, sumDensity]
    field_simp
    ring

end Main

end ProbabilityTheory
