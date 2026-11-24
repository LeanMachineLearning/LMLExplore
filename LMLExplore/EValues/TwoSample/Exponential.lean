/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.CondEVariable.Statistic
public import LMLExplore.EValues.Numeraire
public import LMLExplore.Probability.Distributions.Exponential
public import LMLExplore.Probability.Kernel.SegmentUniform
public import TauCeti.Probability.Distributions.Uniform.Basic
import LMLExplore.Probability.Distributions.Gamma
import TauCeti.Probability.Distributions.Gamma.Basic
import TauCeti.Probability.Distributions.Gamma.Measurability

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
  mean `m` is uniform between `1 / l₁` and `1 / l₂`.

These identifications and the mixture are [EVR26, Note 28]. That no finite combination of members
of the null is equal to `Qᶜ`, against the conjecture of [HGLLA24, §5.2], is in
`LMLExplore.EValues.Examples.TwoSample.Exponential`.

## Main statements

* `ProbabilityTheory.isNumeraire_rnDeriv_segmentUniform_comp`: the likelihood ratio of `Q` to
  `Qᶜ` is the numeraire.
* `ProbabilityTheory.ripr_prod_expMeasure`: `Qᶜ` is the reverse information projection.
* `ProbabilityTheory.segmentUniform_comp_map_add_prod_expMeasure`: `Qᶜ` is the mixture of the
  members of the null whose mean is uniform between the two means.

## Implementation notes

That the law of the sum and the conditional law given the sum are as described under the null is
the beta–gamma algebra of Tau Ceti (`TauCeti.Probability.map_div_add_prod_gammaMeasure`), through
`ProbabilityTheory.map_add_prod_expMeasure_self` and
`ProbabilityTheory.segmentUniform_comp_gammaMeasure`. The law of the sum under `Q` is
Tau Ceti's hypoexponential law (`ProbabilityTheory.map_add_prod_expMeasure_eq_withDensity`), with
density `l₁ l₂ (exp (- l₁ x) - exp (- l₂ x)) / (l₂ - l₁)` on `(0, ∞)`, which is also the
density of the mixture of the laws `Gamma(2, 1 / m)` over the uniform mean `m`
(`ProbabilityTheory.map_add_prod_expMeasure_eq_bind`). The numeraire is then identified
through the effective null: `Qᶜ` is a mixture of members of the null and is equivalent to `Q`,
so that the conditional numeraire theorem `ProbabilityTheory.isNumeraire_rnDeriv_comp_map` and
its corollary `ProbabilityTheory.ripr_eq_comp_map` apply.

## References

* [HGLLA24] Y. Hao, P. Grünwald, T. Lardy, L. Long and R. Adams, *E-values for k-sample tests
  with exponential families*, arXiv:2303.00471, §5.2.
* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4, Theorem 4.1.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, paper project
  `RemyDegenne/evalues_research` (2026), Note 28.
-/

public section

open MeasureTheory Set Filter Real TauCeti.Probability

open scoped ENNReal Topology

namespace ProbabilityTheory

/-! ### The null of two exponential observations with a common rate -/

section Null

variable {l l₁ l₂ : ℝ}

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

/-- The laws `Gamma(2, 1 / m)`, as a kernel. -/
private noncomputable def gammaTwoInvKernel : Kernel ℝ ℝ where
  toFun m := gammaMeasure 2 m⁻¹
  measurable' := measurable_gammaMeasure.comp (f := fun m : ℝ ↦ ((2 : ℝ), m⁻¹)) (by fun_prop)

/-- The kernel `gammaTwoInvKernel` maps `m` to `Gamma(2, 1 / m)`. -/
private lemma gammaTwoInvKernel_apply (m : ℝ) : gammaTwoInvKernel m = gammaMeasure 2 m⁻¹ := rfl

/-- The mixture of the laws `Gamma(2, 1 / m)` over a law of `m`, as a composition with
`gammaTwoInvKernel`. -/
private lemma bind_gammaMeasure_eq_comp (μ : Measure ℝ) :
    (μ.bind fun m ↦ gammaMeasure 2 m⁻¹) = gammaTwoInvKernel ∘ₘ μ := by
  simp_rw [← gammaTwoInvKernel_apply]

/-- `Qᶜ` is in the effective null. -/
private lemma segmentUniform_comp_mem_effectiveSet (h₁ : 0 < l₁) (h₂ : 0 < l₂) :
    Kernel.segmentUniform ∘ₘ ((expMeasure l₁).prod (expMeasure l₂)).map (fun x ↦ x.1 + x.2) ∈
      effectiveSet (Set.range fun l : Ioi (0 : ℝ) ↦ (expMeasure l).prod (expMeasure l)) := by
  rcases eq_or_ne l₁ l₂ with rfl | h
  · rw [segmentUniform_comp_map_add_prod_expMeasure_self h₁]
    exact subset_effectiveSet ⟨⟨l₁, h₁⟩, rfl⟩
  have hα : 0 < min l₁⁻¹ l₂⁻¹ := lt_min (inv_pos.mpr h₁) (inv_pos.mpr h₂)
  have := isProbabilityMeasure_uniformMeasure
    (min_lt_max.mpr (inv_injective.ne h) : min l₁⁻¹ l₂⁻¹ < max l₁⁻¹ l₂⁻¹)
  rw [map_add_prod_expMeasure_eq_bind h₁ h₂ h, bind_gammaMeasure_eq_comp, Measure.comp_assoc]
  refine comp_mem_effectiveSet prob_le_one ?_
  filter_upwards [ae_mem_Ioc_uniformMeasure] with m hm
  have hm0 : 0 < m⁻¹ := inv_pos.mpr (hα.trans hm.1)
  rw [Kernel.comp_apply, gammaTwoInvKernel_apply, segmentUniform_comp_gammaMeasure hm0]
  exact subset_effectiveSet ⟨⟨m⁻¹, hm0⟩, rfl⟩

end Null

/-! ### The numeraire and the reverse information projection -/

section Main

variable {l₁ l₂ : ℝ}

/-- **The numeraire of two exponential observations against a common rate.** For positive rates
`l₁, l₂`, the likelihood ratio of `Exp(l₁) ⊗ Exp(l₂)` to the law under which the sum of the two
observations has its law under `Exp(l₁) ⊗ Exp(l₂)` and, given the sum `s`, the first observation
is uniform on `[0, s]`, is the numeraire of the null of the products `Exp(l) ⊗ Exp(l)`, `l > 0`:
it is an e-variable, and no e-variable has a larger expected logarithm under
`Exp(l₁) ⊗ Exp(l₂)` (`ProbabilityTheory.IsNumeraire.eintegral_log_le`) [EVR26, Note 28]. -/
theorem isNumeraire_rnDeriv_segmentUniform_comp (h₁ : 0 < l₁) (h₂ : 0 < l₂) :
    IsNumeraire (((expMeasure l₁).prod (expMeasure l₂)).rnDeriv
        (Kernel.segmentUniform ∘ₘ ((expMeasure l₁).prod (expMeasure l₂)).map fun x ↦ x.1 + x.2))
      (Set.range fun l : Ioi (0 : ℝ) ↦ (expMeasure l).prod (expMeasure l))
      ((expMeasure l₁).prod (expMeasure l₂)) := by
  have := isProbabilityMeasure_expMeasure h₁
  have := isProbabilityMeasure_expMeasure h₂
  exact isNumeraire_rnDeriv_comp_map (by fun_prop) (ae_of_all _ Kernel.ae_add_segmentUniform)
    (absolutelyContinuous_segmentUniform_comp h₁ h₂).1
    (fun P hP ↦ (isProbabilityMeasure_of_mem_null hP).measure_univ.le)
    (fun _ ↦ segmentUniform_comp_map_add_of_mem) (fun _ ↦ map_add_absolutelyContinuous_of_mem h₁ h₂)
    (segmentUniform_comp_mem_effectiveSet h₁ h₂)

/-- **The reverse information projection of two exponential observations** on the null of the
products `Exp(l) ⊗ Exp(l)`, `l > 0`, is the law under which the sum of the two observations has
its law under `Exp(l₁) ⊗ Exp(l₂)` and, given the sum `s`, the first observation is uniform on
`[0, s]` [EVR26, Note 28]. -/
theorem ripr_prod_expMeasure (h₁ : 0 < l₁) (h₂ : 0 < l₂) :
    ripr ((expMeasure l₁).prod (expMeasure l₂))
        (Set.range fun l : Ioi (0 : ℝ) ↦ (expMeasure l).prod (expMeasure l)) =
      Kernel.segmentUniform ∘ₘ ((expMeasure l₁).prod (expMeasure l₂)).map fun x ↦ x.1 + x.2 := by
  have := isProbabilityMeasure_expMeasure h₁
  have := isProbabilityMeasure_expMeasure h₂
  exact ripr_eq_comp_map (by fun_prop) (ae_of_all _ Kernel.ae_add_segmentUniform)
    (absolutelyContinuous_segmentUniform_comp h₁ h₂).1
    (absolutelyContinuous_segmentUniform_comp h₁ h₂).2
    (fun P hP ↦ (isProbabilityMeasure_of_mem_null hP).measure_univ.le)
    (fun _ ↦ segmentUniform_comp_map_add_of_mem) (fun _ ↦ map_add_absolutelyContinuous_of_mem h₁ h₂)
    (segmentUniform_comp_mem_effectiveSet h₁ h₂)

/-- **The reverse information projection is a continuous mixture of members of the null.** For
distinct positive rates `l₁, l₂`, the law under which the sum of the two observations has its
law under `Exp(l₁) ⊗ Exp(l₂)` and, given the sum `s`, the first observation is uniform on
`[0, s]`, is the mixture of the members `Exp(1 / m) ⊗ Exp(1 / m)` of the null whose mean `m` is
uniform between `1 / l₁` and `1 / l₂` [EVR26, Note 28]. -/
theorem segmentUniform_comp_map_add_prod_expMeasure (h₁ : 0 < l₁) (h₂ : 0 < l₂) (h : l₁ ≠ l₂) :
    Kernel.segmentUniform ∘ₘ ((expMeasure l₁).prod (expMeasure l₂)).map (fun x ↦ x.1 + x.2) =
      (uniformMeasure (min l₁⁻¹ l₂⁻¹) (max l₁⁻¹ l₂⁻¹)).bind
        fun m ↦ (expMeasure m⁻¹).prod (expMeasure m⁻¹) := by
  have hα : 0 < min l₁⁻¹ l₂⁻¹ := lt_min (inv_pos.mpr h₁) (inv_pos.mpr h₂)
  rw [map_add_prod_expMeasure_eq_bind h₁ h₂ h, Measure.bind_bind (f := fun m ↦ gammaMeasure 2 m⁻¹)
    gammaTwoInvKernel.measurable.aemeasurable Kernel.segmentUniform.aemeasurable]
  refine Measure.bind_congr_right ?_
  filter_upwards [ae_mem_Ioc_uniformMeasure] with m hm
  exact segmentUniform_comp_gammaMeasure (inv_pos.mpr (hα.trans hm.1))

end Main

end ProbabilityTheory
