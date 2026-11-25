/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic
public import Statlib.EValues.EVariable
public import LMLExplore.EValues.Merging
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import LMLExplore.Order.Filter.Basic
import LMLExplore.Probability.Distributions.Bernoulli
import TauCeti.MeasureTheory.Integral.Pi

/-!
# Merging functions for independent e-values

A merging function for independent e-values indexed by a finite type `ι` is a measurable
`F : (ι → ℝ≥0∞) → ℝ≥0∞` with `∫⁻ e, F e ∂Measure.pi μ ≤ 1` for all probability measures `μ i` on
`ℝ≥0∞` with expectation at most `1`. The law of e-variables that are independent under a
probability measure is such a product, so `F` turns e-variables that are independent under every
member of the null into an e-variable, and this characterizes merging functions for independent
e-values (`ProbabilityTheory.isIEMerging_iff_forall_isEVar`). Equivalently, they are the
e-variables of the merging null of the product laws `ProbabilityTheory.productLaws`, the joint laws
of independent e-values (`ProbabilityTheory.isIEMerging_iff_isEVar_mergingNull`); so every
e-merging function, and the product of the e-values, is one. No monotonicity is assumed. Such a
function is precise when its integral is `1` against every product of laws with expectation `1`.
As for e-merging functions, the values at infinite arguments are irrelevant
(`ProbabilityTheory.IsIEMerging.of_le`), so domination is a statement about finite arguments.

A precise merging function for independent e-values is admissible [VW21, Proposition 4.1]: a
product of laws with expectation `1` charges every point with finite coordinates. As for
e-merging functions, admissibility is admissibility among the e-variables of the merging null of
the product laws, whose quasi-sure filter is the principal filter of the points with finite
coordinates. The product of the e-values, the U-statistics `uStatistic n` of order
`n ≤ card ι`, which average the products of `n` of the e-values, and their mixtures are precise,
hence admissible [VW21, Section 4].

Vovk and Wang ask whether every increasing merging function for independent e-values is
dominated by a generalized martingale merging function, and whether every precise one is such a
function [VW24, Section 7]; the negative answers are in
`LMLExplore.EValues.Examples.Merging.Independent`.

## Main definitions

* `ProbabilityTheory.productLaws`: the products of probability measures on `ι → α`.
* `ProbabilityTheory.IsIEMerging F`: `F` is a merging function for independent e-values.
* `ProbabilityTheory.IsPreciseIEMerging F`: `F` is a precise merging function for independent
  e-values.
* `ProbabilityTheory.IsAdmissibleIEMerging F`: `F` is an admissible e-variable for the merging
  null of the product laws.
* `ProbabilityTheory.uStatistic n e`: the U-statistic of order `n` of the e-values `e`, the
  elementary symmetric polynomial of degree `n` divided by the number of its terms.

## Main statements

* `ProbabilityTheory.map_mem_productLaws_iff`: the joint law of random variables is a product law
  exactly when they are independent.
* `ProbabilityTheory.isIEMerging_iff_isEVar_mergingNull`: the merging functions for independent
  e-values are the e-variables of the merging null of the product laws.
* `ProbabilityTheory.IsEMerging.isIEMerging`, `ProbabilityTheory.isIEMerging_prod`: e-merging
  functions and the product are merging functions for independent e-values.
* `ProbabilityTheory.isPreciseIEMerging_prod`: the product is precise.
* `ProbabilityTheory.IsIEMerging.isEVar_comp`: a merging function for independent e-values of
  e-variables that are independent under every member of the null is an e-variable, and
  `ProbabilityTheory.isIEMerging_iff_forall_isEVar` characterizes these functions by this property.
* `ProbabilityTheory.IsIEMerging.of_le`: a measurable function dominated on finite arguments by a
  merging function for independent e-values is one.
* `ProbabilityTheory.quasiSure_mergingNull_productLaws_eq_principal`: the quasi-sure filter of the
  merging null of the product laws is the principal filter of the points with finite coordinates.
* `ProbabilityTheory.isAdmissibleIEMerging_iff_isAdmissible`,
  `ProbabilityTheory.IsAdmissibleIEMerging.eq_of_le`: admissibility reads at finite arguments.
* `ProbabilityTheory.IsPreciseIEMerging.isAdmissibleIEMerging`: precise merging functions for
  independent e-values are admissible [VW21, Proposition 4.1].
* `ProbabilityTheory.isIEMerging_tsum_mul`, `ProbabilityTheory.isPreciseIEMerging_tsum_mul`:
  countable mixtures of (precise) merging functions for independent e-values are (precise) merging
  functions for independent e-values; `ProbabilityTheory.isIEMerging_lintegral` and
  `ProbabilityTheory.isPreciseIEMerging_lintegral` give the same for jointly measurable mixtures
  against a measure.
* `ProbabilityTheory.isIEMerging_uStatistic`, `ProbabilityTheory.isPreciseIEMerging_uStatistic`:
  the U-statistics are merging functions for independent e-values, precise up to order `card ι`.
* `ProbabilityTheory.isAdmissibleIEMerging_uStatistic`,
  `ProbabilityTheory.isAdmissibleIEMerging_prod`,
  `ProbabilityTheory.isAdmissibleIEMerging_sum_mul_uStatistic`: the U-statistics of order at most
  `card ι`, the product, and the mixtures of these U-statistics, are admissible merging functions
  for independent e-values [VW21, Section 4].

## References

* [VW21] V. Vovk and R. Wang, *E-values: calibration, combination and applications*, Ann. Statist.
  49 (2021), arXiv:1912.06116v4: Section 4 (the product of independent e-values, the
  U-statistics, Proposition 4.1 on admissibility).
* [VW24] V. Vovk and R. Wang, *Merging sequential e-values via martingales*, Electron. J.
  Statist. 18 (2024), arXiv:2007.06382v3: Section 2 (merging functions for independent e-values),
  Section 7 (precise merging functions).
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

universe u

/-! ### The product laws -/

section ProductLaws

variable {ι α Ω : Type*} [Fintype ι] {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
  {μ : Measure (ι → α)}

/-- The **product laws** on `ι → α`: the products `Measure.pi ν` of probability measures `ν i` on
`α`, the joint laws of independent random variables (`ProbabilityTheory.map_mem_productLaws_iff`).
Their merging null is the null of the joint laws of independent e-values. -/
def productLaws : Set (Measure (ι → α)) :=
  {μ | ∃ ν : ι → Measure α, (∀ i, IsProbabilityMeasure (ν i)) ∧ Measure.pi ν = μ}

@[simp]
theorem mem_productLaws :
    μ ∈ productLaws ↔ ∃ ν : ι → Measure α, (∀ i, IsProbabilityMeasure (ν i)) ∧ Measure.pi ν = μ :=
  Iff.rfl

/-- A product of probability measures is a product law. It has priority over the unfolding
`ProbabilityTheory.mem_productLaws`, after which `simp` could not close the goal. -/
@[simp high]
theorem pi_mem_productLaws (ν : ι → Measure α) [∀ i, IsProbabilityMeasure (ν i)] :
    Measure.pi ν ∈ productLaws :=
  ⟨ν, inferInstance, rfl⟩

/-- **The joint law of independent random variables is a product law**: for a probability measure
`P`, the joint law of almost everywhere measurable `X i` is a product of laws exactly when the
`X i` are independent. -/
theorem map_mem_productLaws_iff {P : Measure Ω} [IsProbabilityMeasure P] {X : ι → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) P) :
    P.map (fun ω i ↦ X i ω) ∈ productLaws ↔ iIndepFun X P := by
  refine ⟨fun ⟨ν, hν, h⟩ ↦ (iIndepFun_iff_map_fun_eq_pi_map hX).2 ?_, fun h ↦ ?_⟩
  · -- the factors of the product are the laws of the `X i`
    have hm : AEMeasurable (fun ω i ↦ X i ω) P := AEMeasurable.of_eval hX
    have hmarg (i : ι) : P.map (X i) = ν i := by
      rw [← (measurePreserving_eval ν i).map_eq, h, AEMeasurable.map_map_of_aemeasurable
        (measurable_pi_apply i).aemeasurable hm]
      rfl
    simp_rw [hmarg, h]
  · rw [h.map_fun_eq_pi_map hX]
    exact pi_mem_productLaws _

end ProductLaws

/-! ### Merging functions for independent e-values -/

section Definition

variable {ι : Type*} [Fintype ι] {F G : (ι → ℝ≥0∞) → ℝ≥0∞}

/-- A **merging function for independent e-values** indexed by `ι` [VW24, Section 2]: a
measurable `F : (ι → ℝ≥0∞) → ℝ≥0∞` with `∫⁻ e, F e ∂Measure.pi μ ≤ 1` for all probability
measures `μ i` on `ℝ≥0∞` with expectation at most `1`. It is not required to be monotone. -/
structure IsIEMerging (F : (ι → ℝ≥0∞) → ℝ≥0∞) : Prop where
  measurable : Measurable F
  lintegral_le_one : ∀ (μ : ι → Measure ℝ≥0∞) [∀ i, IsProbabilityMeasure (μ i)],
    (∀ i, ∫⁻ x, x ∂μ i ≤ 1) → ∫⁻ e, F e ∂Measure.pi μ ≤ 1

/-- A **precise merging function for independent e-values** [VW24, Section 7]: a merging function
for independent e-values whose integral against `Measure.pi μ` is `1` for all probability measures
`μ i` on `ℝ≥0∞` with expectation `1`. -/
structure IsPreciseIEMerging (F : (ι → ℝ≥0∞) → ℝ≥0∞) : Prop extends IsIEMerging F where
  lintegral_eq_one : ∀ (μ : ι → Measure ℝ≥0∞) [∀ i, IsProbabilityMeasure (μ i)],
    (∀ i, ∫⁻ x, x ∂μ i = 1) → ∫⁻ e, F e ∂Measure.pi μ = 1

/-- The members of the merging null of the product laws are the products of laws on `ℝ≥0∞` with
expectation at most `1`. -/
theorem pi_mem_mergingNull_productLaws_iff (μ : ι → Measure ℝ≥0∞)
    [∀ i, IsProbabilityMeasure (μ i)] :
    Measure.pi μ ∈ mergingNull productLaws ↔ ∀ i, ∫⁻ x, x ∂μ i ≤ 1 := by
  simp only [mem_mergingNull, pi_mem_productLaws, true_and,
    fun i ↦ (measurePreserving_eval μ i).lintegral_comp measurable_id']
  exact ⟨And.right, fun h ↦ ⟨inferInstance, h⟩⟩

/-- **Merging functions for independent e-values are the e-variables of the merging null of the
product laws**: they are the bets on the space of values against the joint laws of independent
e-values. -/
theorem isIEMerging_iff_isEVar_mergingNull :
    IsIEMerging F ↔ IsEVar F (mergingNull productLaws) := by
  refine ⟨fun hF ↦ ⟨hF.measurable, fun P hP ↦ ?_⟩, fun hF ↦ ⟨hF.measurable, fun μ _ hμ ↦
    hF.lintegral_le_one ((pi_mem_mergingNull_productLaws_iff μ).2 hμ)⟩⟩
  obtain ⟨⟨μ, hμ, rfl⟩, -⟩ := mem_mergingNull.1 hP
  exact hF.lintegral_le_one μ ((pi_mem_mergingNull_productLaws_iff μ).1 hP)

/-- An e-merging function is a merging function for independent e-values. -/
theorem IsEMerging.isIEMerging (hF : IsEMerging F) : IsIEMerging F :=
  isIEMerging_iff_isEVar_mergingNull.2 (hF.isEVar_mergingNull _)

/-- **The product merges independent e-values** [VW21, Section 4]: the product of the e-values is a
merging function for independent e-values. -/
theorem isIEMerging_prod : IsIEMerging fun e : ι → ℝ≥0∞ ↦ ∏ i, e i := by
  refine ⟨by fun_prop, fun μ _ hμ ↦ ?_⟩
  rw [TauCeti.lintegral_fintype_prod_eq_prod μ (f := fun _ x ↦ x) fun _ ↦ measurable_id]
  exact Finset.prod_le_one fun i _ ↦ hμ i

/-- **The product is a precise merging function for independent e-values**: its integral against
a product of laws with mean `1` is `1`. -/
theorem isPreciseIEMerging_prod : IsPreciseIEMerging fun e : ι → ℝ≥0∞ ↦ ∏ i, e i := by
  refine ⟨isIEMerging_prod, fun μ _ hμ ↦ ?_⟩
  rw [TauCeti.lintegral_fintype_prod_eq_prod μ (f := fun _ x ↦ x) fun _ ↦ measurable_id]
  exact Finset.prod_eq_one fun i _ ↦ hμ i

/-- A measurable function dominated on finite arguments by a merging function for independent
e-values is one: the values at infinite arguments are irrelevant, since the coordinates are
almost surely finite under a product of laws with finite expectations. -/
theorem IsIEMerging.of_le (hG : IsIEMerging G) (hF : Measurable F)
    (hle : ∀ e : ι → ℝ≥0, F (fun i ↦ e i) ≤ G (fun i ↦ e i)) : IsIEMerging F :=
  isIEMerging_iff_isEVar_mergingNull.2
    ((isIEMerging_iff_isEVar_mergingNull.1 hG).mono_mergingNull hF hle)

/-- A merging function for independent e-values, applied to e-variables that are independent under
every member of the null, is an e-variable. -/
theorem IsIEMerging.isEVar_comp {Ω : Type*} {mΩ : MeasurableSpace Ω} {S : Set (Measure Ω)}
    (hF : IsIEMerging F) (hS : ∀ P ∈ S, IsProbabilityMeasure P) {E : ι → Ω → ℝ≥0∞}
    (hE : ∀ i, IsEVar (E i) S) (hindep : ∀ P ∈ S, iIndepFun E P) :
    IsEVar (fun ω ↦ F fun i ↦ E i ω) S :=
  (isIEMerging_iff_isEVar_mergingNull.1 hF).comp_isEVar hS hE fun P hP ↦
    have := hS P hP
    (map_mem_productLaws_iff fun i ↦ (hE i).measurable.aemeasurable).2 (hindep P hP)

/-- A function of e-values is a merging function for independent e-values exactly when it turns
e-variables that are independent under every member of the null into an e-variable, for every
null hypothesis of probability measures on every measurable space in the universe of `ι`. The
forward direction holds on measurable spaces in any universe
(`ProbabilityTheory.IsIEMerging.isEVar_comp`). -/
theorem isIEMerging_iff_forall_isEVar {ι : Type u} [Fintype ι] {F : (ι → ℝ≥0∞) → ℝ≥0∞} :
    IsIEMerging F ↔ ∀ (Ω : Type u) [MeasurableSpace Ω] (S : Set (Measure Ω)),
      (∀ P ∈ S, IsProbabilityMeasure P) → ∀ E : ι → Ω → ℝ≥0∞, (∀ i, IsEVar (E i) S) →
        (∀ P ∈ S, iIndepFun E P) → IsEVar (fun ω ↦ F fun i ↦ E i ω) S := by
  refine ⟨fun hF Ω _ S hS E hE hindep ↦ hF.isEVar_comp hS hE hindep, fun h ↦ ?_⟩
  -- Apply the hypothesis to the coordinates, under the merging null of the product laws.
  refine isIEMerging_iff_isEVar_mergingNull.2 <| h (ι → ℝ≥0∞) (mergingNull productLaws)
    (fun _ ↦ isProbabilityMeasure_of_mem_mergingNull) (fun i e ↦ e i)
    (isEVar_eval_mergingNull productLaws) fun P hP ↦ ?_
  obtain ⟨⟨μ, hμ, rfl⟩, -⟩ := mem_mergingNull.1 hP
  exact iIndepFun_pi (X := fun _ x ↦ x) fun _ ↦ aemeasurable_id'

end Definition

/-! ### Admissible merging functions for independent e-values -/

section Admissible

variable {ι : Type*} [Fintype ι] {F G : (ι → ℝ≥0∞) → ℝ≥0∞}

/-- **The quasi-sure filter of the merging null of the product laws** is the principal filter of
the points with finite coordinates: a product of laws with mean `1` charges each of them
(`exists_pi_lintegral_id_eq_one`). -/
theorem quasiSure_mergingNull_productLaws_eq_principal :
    quasiSure (mergingNull (productLaws : Set (Measure (ι → ℝ≥0∞)))) =
      Filter.principal (Set.range fun (e : ι → ℝ≥0) i ↦ (e i : ℝ≥0∞)) := by
  refine quasiSure_mergingNull_eq_principal fun e ↦ ?_
  obtain ⟨μ, hμ, hmean, hne⟩ := exists_pi_lintegral_id_eq_one e
  exact ⟨_, (pi_mem_mergingNull_productLaws_iff μ).2 fun i ↦ (hmean i).le, hne⟩

/-- An **admissible merging function for independent e-values** [VW21, Section 4]: an admissible
e-variable for the merging null of the product laws, whose e-variables are the merging functions
for independent e-values (`isIEMerging_iff_isEVar_mergingNull`). Its quasi-sure filter is the
principal filter of the points with finite coordinates
(`quasiSure_mergingNull_productLaws_eq_principal`), so `F` is admissible when every merging
function for independent e-values dominating it at finite arguments equals it there
(`isAdmissibleIEMerging_iff_isAdmissible`, `IsAdmissibleIEMerging.eq_of_le`). -/
abbrev IsAdmissibleIEMerging (F : (ι → ℝ≥0∞) → ℝ≥0∞) : Prop :=
  IsAdmissibleEVar F (mergingNull productLaws)

/-- An admissible merging function for independent e-values is a merging function for independent
e-values. -/
theorem IsAdmissibleIEMerging.isIEMerging (hF : IsAdmissibleIEMerging F) : IsIEMerging F :=
  isIEMerging_iff_isEVar_mergingNull.2 hF.mem

/-- An admissible merging function for independent e-values is admissible (`Filter.IsAdmissible`)
among the merging functions for independent e-values for the order at finite arguments, the
eventual order along the principal filter of the finite vectors, and conversely. -/
theorem isAdmissibleIEMerging_iff_isAdmissible :
    IsAdmissibleIEMerging F ↔
      (Filter.principal (Set.range fun (e : ι → ℝ≥0) i ↦ (e i : ℝ≥0∞))).IsAdmissible
        {G | IsIEMerging G} F := by
  simp only [IsAdmissibleIEMerging, IsAdmissibleEVar,
    quasiSure_mergingNull_productLaws_eq_principal, ← isIEMerging_iff_isEVar_mergingNull]

/-- A merging function for independent e-values that dominates an admissible one at finite
arguments is equal to it there. -/
theorem IsAdmissibleIEMerging.eq_of_le (hF : IsAdmissibleIEMerging F) (hG : IsIEMerging G)
    (hFG : ∀ e : ι → ℝ≥0, F (fun i ↦ e i) ≤ G (fun i ↦ e i)) (e : ι → ℝ≥0) :
    G (fun i ↦ e i) = F (fun i ↦ e i) :=
  (Filter.eventuallyLE_principal_range_iff.1
    ((isAdmissibleIEMerging_iff_isAdmissible.1 hF).eventuallyLE hG
      (Filter.eventuallyLE_principal_range_iff.2 hFG)) e).antisymm (hFG e)

/-- **Precise merging functions for independent e-values are admissible** [VW21,
Proposition 4.1]. -/
theorem IsPreciseIEMerging.isAdmissibleIEMerging (hF : IsPreciseIEMerging F) :
    IsAdmissibleIEMerging F := by
  -- If `G ≥ F` at finite arguments, then `G = F` almost surely under every product of laws with
  -- mean `1`, since `F` is exact there, and such a product charges any given finite point.
  refine isAdmissibleIEMerging_iff_isAdmissible.2 ⟨hF.toIsIEMerging, fun G hG hle ↦
    Filter.eventuallyLE_principal_range_iff.2 fun e ↦ ?_⟩
  have hG : IsIEMerging G := by simpa using hG
  replace hle := Filter.eventuallyLE_principal_range_iff.1 hle
  obtain ⟨μ, hμ, hmean, hne⟩ := exists_pi_lintegral_id_eq_one e
  have hμS := (pi_mem_mergingNull_productLaws_iff μ).2 fun i ↦ (hmean i).le
  have hfin : ∀ᵐ x ∂Measure.pi μ, ∀ i, x i ≠ ∞ := ae_all_iff.2 fun i ↦
    (isEVar_eval_mergingNull productLaws i).ae_ne_top hμS
  have h0 := (isIEMerging_iff_isEVar_mergingNull.1 hG).measure_lt_eq_zero_of_ae_le hμS
    (ae_le_of_forall_nnreal_le hfin hle) (hF.lintegral_eq_one μ hmean)
  exact not_lt.1 fun hlt ↦ hne (measure_mono_null (Set.singleton_subset_iff.2 hlt) h0)

/-- **The product is an admissible merging function for independent e-values** [VW21,
Section 4]. -/
theorem isAdmissibleIEMerging_prod : IsAdmissibleIEMerging fun e : ι → ℝ≥0∞ ↦ ∏ i, e i :=
  isPreciseIEMerging_prod.isAdmissibleIEMerging

end Admissible

/-! ### Mixtures and U-statistics -/

section Mixture

variable {ι κ : Type*} [Fintype ι] [Countable κ] {w : κ → ℝ≥0∞}
  {F : κ → (ι → ℝ≥0∞) → ℝ≥0∞}

/-- A countable mixture `∑' j, w j * F j e`, with total weight at most `1`, of merging functions
for independent e-values is one: an instance of `isEVar_tsum_mul` for the merging null of the
product laws. -/
theorem isIEMerging_tsum_mul (hw : ∑' j, w j ≤ 1) (hF : ∀ j, IsIEMerging (F j)) :
    IsIEMerging fun e ↦ ∑' j, w j * F j e :=
  isIEMerging_iff_isEVar_mergingNull.2
    (isEVar_tsum_mul (fun j ↦ isIEMerging_iff_isEVar_mergingNull.1 (hF j)) hw)

/-- A countable mixture `∑' j, w j * F j e`, with total weight `1`, of precise merging functions
for independent e-values is one. -/
theorem isPreciseIEMerging_tsum_mul (hw : ∑' j, w j = 1) (hF : ∀ j, IsPreciseIEMerging (F j)) :
    IsPreciseIEMerging fun e ↦ ∑' j, w j * F j e := by
  refine ⟨isIEMerging_tsum_mul hw.le fun j ↦ (hF j).toIsIEMerging, fun μ _ hμ ↦ ?_⟩
  rw [lintegral_tsum fun j ↦ ((hF j).measurable.const_mul _).aemeasurable]
  simp_rw [lintegral_const_mul _ (hF _).measurable, (hF _).lintegral_eq_one μ hμ, mul_one, hw]

/-- A mixture `∫⁻ a, G a e ∂ρ`, against a measure `ρ` of mass at most `1`, of a jointly measurable
family of merging functions for independent e-values is one. -/
theorem isIEMerging_lintegral {A : Type*} {mA : MeasurableSpace A} {ρ : Measure A}
    (hρ : ρ Set.univ ≤ 1) {G : A → (ι → ℝ≥0∞) → ℝ≥0∞} (hGm : Measurable (Function.uncurry G))
    (hG : ∀ a, IsIEMerging (G a)) :
    IsIEMerging fun e ↦ ∫⁻ a, G a e ∂ρ := by
  -- a measure of mass at most `1` is finite, hence s-finite, so the integrals can be swapped
  have : IsFiniteMeasure ρ := ⟨hρ.trans_lt ENNReal.one_lt_top⟩
  refine ⟨hGm.lintegral_prod_left', fun μ _ hμ ↦ ?_⟩
  rw [lintegral_lintegral_swap (f := fun e a ↦ G a e) (hGm.comp measurable_swap).aemeasurable]
  calc ∫⁻ a, ∫⁻ e, G a e ∂Measure.pi μ ∂ρ ≤ ∫⁻ _, 1 ∂ρ :=
        lintegral_mono fun a ↦ (hG a).lintegral_le_one μ hμ
    _ ≤ 1 := by simpa using hρ

/-- A mixture `∫⁻ a, G a e ∂ρ`, against a probability measure `ρ`, of a jointly measurable family
of precise merging functions for independent e-values is one. -/
theorem isPreciseIEMerging_lintegral {A : Type*} {mA : MeasurableSpace A} {ρ : Measure A}
    [IsProbabilityMeasure ρ] {G : A → (ι → ℝ≥0∞) → ℝ≥0∞}
    (hGm : Measurable (Function.uncurry G)) (hG : ∀ a, IsPreciseIEMerging (G a)) :
    IsPreciseIEMerging fun e ↦ ∫⁻ a, G a e ∂ρ := by
  refine ⟨isIEMerging_lintegral (by simp) hGm fun a ↦ (hG a).toIsIEMerging, fun μ _ hμ ↦ ?_⟩
  rw [lintegral_lintegral_swap (f := fun e a ↦ G a e) (hGm.comp measurable_swap).aemeasurable]
  simp_rw [(hG _).lintegral_eq_one μ hμ]
  simp

end Mixture

section UStatistic

variable {ι : Type*} [Fintype ι]

/-- The **U-statistic of order `n`** of the e-values `e` [VW21, Section 4]: the average, over the
subsets `s` of `n` coordinates, of the products `∏ i ∈ s, e i`, that is, the elementary symmetric
polynomial `MvPolynomial.esymm` of degree `n` evaluated at `e`, divided by the number of its
terms. It is `1` for `n = 0` (`uStatistic_zero`), the arithmetic mean for `n = 1`
(`uStatistic_one`), the product of the e-values for `n = card ι` (`uStatistic_card`) and `0` for
`n > card ι` (`uStatistic_eq_zero_of_card_lt`). -/
noncomputable def uStatistic (n : ℕ) (e : ι → ℝ≥0∞) : ℝ≥0∞ :=
  ((Fintype.card ι).choose n : ℝ≥0∞)⁻¹ * MvPolynomial.eval e (MvPolynomial.esymm ι ℝ≥0∞ n)

theorem uStatistic_apply (n : ℕ) (e : ι → ℝ≥0∞) :
    uStatistic n e =
      ((Fintype.card ι).choose n : ℝ≥0∞)⁻¹ * ∑ s ∈ Finset.univ.powersetCard n, ∏ i ∈ s, e i := by
  simp [uStatistic, MvPolynomial.esymm]

@[simp]
theorem uStatistic_zero (e : ι → ℝ≥0∞) : uStatistic 0 e = 1 := by
  simp [uStatistic_apply]

theorem uStatistic_one (e : ι → ℝ≥0∞) : uStatistic 1 e = (∑ i, e i) / Fintype.card ι := by
  simp only [uStatistic_apply, Nat.choose_one_right, Finset.powersetCard_one, Finset.sum_map,
    Function.Embedding.coeFn_mk, Finset.prod_singleton]
  rw [ENNReal.div_eq_inv_mul]

@[simp]
theorem uStatistic_card (e : ι → ℝ≥0∞) : uStatistic (Fintype.card ι) e = ∏ i, e i := by
  rw [uStatistic_apply, Nat.choose_self, ← Finset.card_univ, Finset.powersetCard_self]
  simp

/-- Above the number of e-values, there are no subsets of `n` coordinates, and the U-statistic of
order `n` is `0`. -/
@[simp]
theorem uStatistic_eq_zero_of_card_lt {n : ℕ} (h : Fintype.card ι < n) (e : ι → ℝ≥0∞) :
    uStatistic n e = 0 := by
  rw [uStatistic_apply, Finset.powersetCard_eq_empty.2 (by rwa [Finset.card_univ])]
  simp

@[fun_prop]
theorem measurable_uStatistic (n : ℕ) : Measurable (uStatistic (ι := ι) n) := by
  simp_rw [funext (uStatistic_apply n)]
  fun_prop

/-- The integral of a U-statistic against a product of probability measures is the average, over
the subsets `s` of `n` coordinates, of the products of the means of the coordinates in `s`. -/
theorem lintegral_uStatistic_pi (n : ℕ) (μ : ι → Measure ℝ≥0∞)
    [∀ i, IsProbabilityMeasure (μ i)] :
    ∫⁻ e, uStatistic n e ∂Measure.pi μ = ((Fintype.card ι).choose n : ℝ≥0∞)⁻¹ *
      ∑ s ∈ Finset.univ.powersetCard n, ∏ i ∈ s, ∫⁻ z, z ∂μ i := by
  classical
  simp_rw [uStatistic_apply]
  rw [lintegral_const_mul _ (by fun_prop), lintegral_finsetSum _ fun s _ ↦ by fun_prop]
  congr 1
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  -- The product over `s` is the product over all coordinates of `if i ∈ s then e i else 1`.
  have h := TauCeti.lintegral_fintype_prod_eq_prod μ (f := fun i x ↦ if i ∈ s then x else 1)
    fun i ↦ by fun_prop
  simp only [Finset.prod_ite_mem, Finset.univ_inter] at h
  rw [h]
  calc ∏ i, ∫⁻ y, (if i ∈ s then y else 1) ∂μ i = ∏ i, if i ∈ s then ∫⁻ z, z ∂μ i else 1 :=
        Finset.prod_congr rfl fun i _ ↦ by split_ifs <;> simp
    _ = ∏ i ∈ s, ∫⁻ z, z ∂μ i := by rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- **The U-statistics are merging functions for independent e-values** [VW21, Section 4]. -/
theorem isIEMerging_uStatistic (n : ℕ) : IsIEMerging (uStatistic (ι := ι) n) := by
  refine ⟨measurable_uStatistic n, fun μ _ hμ ↦ ?_⟩
  rw [lintegral_uStatistic_pi]
  calc ((Fintype.card ι).choose n : ℝ≥0∞)⁻¹ *
        ∑ s ∈ Finset.univ.powersetCard n, ∏ i ∈ s, ∫⁻ z, z ∂μ i ≤
      ((Fintype.card ι).choose n : ℝ≥0∞)⁻¹ * ∑ s ∈ Finset.univ.powersetCard n, 1 := by
        gcongr with s
        exact Finset.prod_le_one fun i _ ↦ hμ i
    _ ≤ 1 := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_one]
        exact ENNReal.inv_mul_le_one _

/-- **The U-statistics of order at most the number of e-values are precise merging functions for
independent e-values**. Above that order, the U-statistic is `0`
(`uStatistic_eq_zero_of_card_lt`). -/
theorem isPreciseIEMerging_uStatistic {n : ℕ} (hn : n ≤ Fintype.card ι) :
    IsPreciseIEMerging (uStatistic (ι := ι) n) := by
  refine ⟨isIEMerging_uStatistic n, fun μ _ hμ ↦ ?_⟩
  rw [lintegral_uStatistic_pi]
  simp only [hμ, Finset.prod_const_one, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, nsmul_one]
  exact ENNReal.inv_mul_cancel (by simpa using Nat.choose_pos hn |>.ne')
    (ENNReal.natCast_ne_top _)

/-- **The U-statistics of order at most the number of e-values are admissible merging functions
for independent e-values** [VW21, Section 4]. -/
theorem isAdmissibleIEMerging_uStatistic {n : ℕ} (hn : n ≤ Fintype.card ι) :
    IsAdmissibleIEMerging (uStatistic (ι := ι) n) :=
  (isPreciseIEMerging_uStatistic hn).isAdmissibleIEMerging

/-- **The mixtures of the U-statistics are admissible merging functions for independent
e-values** [VW21, Section 4]: for weights `w n`, `n ≤ card ι`, summing to `1`, the mixture
`∑ n, w n * uStatistic n e` is admissible. It includes the product, the arithmetic mean and the
constant `1`. -/
theorem isAdmissibleIEMerging_sum_mul_uStatistic {w : Fin (Fintype.card ι + 1) → ℝ≥0∞}
    (hw : ∑ n, w n = 1) :
    IsAdmissibleIEMerging fun e : ι → ℝ≥0∞ ↦ ∑ n, w n * uStatistic n e := by
  have h := isPreciseIEMerging_tsum_mul
    (F := fun (n : Fin (Fintype.card ι + 1)) ↦ uStatistic (ι := ι) n)
    (by rwa [tsum_fintype]) fun n ↦ isPreciseIEMerging_uStatistic (Nat.lt_succ_iff.1 n.isLt)
  simp only [tsum_fintype] at h
  exact h.isAdmissibleIEMerging

end UStatistic

end ProbabilityTheory
