/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import LMLExplore.MeasureTheory.Measure.AbsolutelyContinuousSet
public import LMLExplore.Probability.Independence.Integration
public import LMLExplore.Probability.QuasiSure
public import Statlib.EValues.EVariable

/-!
# Exact e-variables, Markov's inequality and products of independent e-variables

An e-variable for a null hypothesis `S : Set (Measure Ω)` (Statlib's `ProbabilityTheory.IsEVar`)
is a measurable `E : Ω → ℝ≥0∞` with `∫⁻ E ∂P ≤ 1` for every `P ∈ S`
(`ProbabilityTheory.IsEVar.lintegral_le_one`). This file develops the first properties of
e-variables that hypothesis testing uses:

* the exact e-variables, with `∫⁻ E ∂P = 1` for every `P ∈ S`;
* the e-variable equal to `∞` on a set null for every member of `S`, and the measures under which
  every e-variable for `S` is almost surely finite, which are those absolutely continuous with
  respect to `S`;
* Markov's inequality, which makes `{α⁻¹ ≤ E}` the rejection region of a level-`α` test;
* products of e-variables from a family that is independent under every member of the null.

Following Statlib, the null is an arbitrary set of measures, with no dominating measure, and
e-variables are `ℝ≥0∞`-valued.

## Main definitions

* `ProbabilityTheory.IsExactEVar E S`: `E` is an e-variable for `S` with `∫⁻ E ∂P = 1` for every
  `P ∈ S`.

## Main statements

* `ProbabilityTheory.isEVar_iff_lintegral_le_one`, `ProbabilityTheory.isExactEVar_iff`: the
  e-variables and the exact e-variables in terms of `∫⁻`.
* `ProbabilityTheory.IsEVar.congr_quasiSure`, `ProbabilityTheory.IsEVar.mono_ae`: the set
  of e-variables is closed under quasi-sure equality and solid in the quasi-sure order
  (`ProbabilityTheory.quasiSure`), among measurable functions.
* `ProbabilityTheory.IsExactEVar.integral_toReal_sub_one_eq_zero`: under a probability measure of
  the null, the gain `E - 1` of an exact e-variable has expectation `0`.
* `ProbabilityTheory.isExactEVar_rnDeriv`: a likelihood ratio `Q.rnDeriv P` of a probability
  measure `Q ≪ P` is an exact e-variable for `{P}`.
* `ProbabilityTheory.isEVar_div_singleton`: on a countable space, the likelihood ratio
  `x ↦ Q {x} / P {x}` against a probability measure `P` that charges every point is an
  e-variable for `{P}`.
* `ProbabilityTheory.IsEVar.ofReal_one_sub_mul_add_ofReal`: for `ε ∈ [0, 1]`, the mixture
  `(1 - ε) E + ε` of an e-variable with the constant `1` is an e-variable.
* `ProbabilityTheory.isEVar_tsum_mul`, `ProbabilityTheory.isEVar_finsetSum_mul`: a countable or
  finite mixture `∑ i, w i * E i` of e-variables, with weights of sum at most `1`, is an
  e-variable.
* `ProbabilityTheory.isEVar_piecewise_top`: the function equal to `∞` on a measurable set null
  for every member of `S`, and to `0` elsewhere, is an e-variable for `S`.
* `ProbabilityTheory.absolutelyContinuousSet_iff_forall_isEVar_ae_ne_top`: a measure `Q` is
  absolutely continuous with respect to `S` (`MeasureTheory.Measure.AbsolutelyContinuousSet`)
  exactly when every e-variable for `S` is `Q`-almost surely finite [LRR25, Theorem 2.6].
* `ProbabilityTheory.IsEVar.measure_inv_le_le`: **Markov's inequality** for e-variables,
  `P {ω | α⁻¹ ≤ E ω} ≤ α`.
* `ProbabilityTheory.isEVar_finsetProd`, `ProbabilityTheory.isExactEVar_finsetProd`: a finite
  product of (exact) e-variables, from a family that is independent under every member of the
  null, is an (exact) e-variable. Statlib's `ProbabilityTheory.IsEVar.prod` treats the two
  coordinates of a product space, where independence holds by construction.

## References

* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4, Theorem 2.6.
* A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6: Definition 1.2, Fact 1.3 and Proposition 2.1.
* V. Vovk and R. Wang, *E-values: calibration, combination and applications*, Ann. Statist. 49
  (2021).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓨 : MeasurableSpace 𝓨}
  {S T : Set (Measure Ω)} {E F : Ω → ℝ≥0∞} {P : Measure Ω}

/-- `E` is an e-variable exactly when it is measurable and has expectation at most one under every
member of the null. -/
theorem isEVar_iff_lintegral_le_one :
    IsEVar E S ↔ Measurable E ∧ ∀ P ∈ S, ∫⁻ ω, E ω ∂P ≤ 1 :=
  ⟨fun hE ↦ ⟨hE.measurable, fun _ hP ↦ hE.lintegral_le_one hP⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-! ### Exact e-variables -/

/-- An e-variable `E` for `S` is **exact** when `∫⁻ E ∂P = 1` for every `P ∈ S`. -/
structure IsExactEVar (E : Ω → ℝ≥0∞) (S : Set (Measure Ω)) : Prop extends IsEVar E S where
  lintegral_eq_one ⦃P : Measure Ω⦄ (hP : P ∈ S) : ∫⁻ ω, E ω ∂P = 1

/-- `E` is an exact e-variable exactly when it is measurable and has expectation one under every
member of the null. -/
theorem isExactEVar_iff :
    IsExactEVar E S ↔ Measurable E ∧ ∀ P ∈ S, ∫⁻ ω, E ω ∂P = 1 :=
  ⟨fun hE ↦ ⟨hE.measurable, fun _ hP ↦ hE.lintegral_eq_one hP⟩,
    fun h ↦ ⟨⟨h.1, fun P hP ↦ (h.2 P hP).le⟩, h.2⟩⟩

theorem IsExactEVar.of_lintegral_eq_one (hE : Measurable E) (h : ∀ P ∈ S, ∫⁻ ω, E ω ∂P = 1) :
    IsExactEVar E S :=
  isExactEVar_iff.2 ⟨hE, h⟩

/-- The constant `1` is an exact e-variable for every null of probability measures. -/
theorem isExactEVar_one (hS : ∀ P ∈ S, IsProbabilityMeasure P) : IsExactEVar 1 S :=
  .of_lintegral_eq_one measurable_one fun P hP ↦ by have := hS P hP; simp

theorem IsExactEVar.anti_set (hST : S ⊆ T) (hE : IsExactEVar E T) : IsExactEVar E S where
  toIsEVar := hE.toIsEVar.anti_set hST
  lintegral_eq_one _ hP := hE.lintegral_eq_one (hST hP)

/-- A measurable function quasi-surely equal to an e-variable is an e-variable: Statlib's
`IsEVar.congr` with the quasi-sure filter. -/
theorem IsEVar.congr_quasiSure (hE : IsEVar E S) (hF : Measurable F) (hEF : E =ᶠ[quasiSure S] F) :
    IsEVar F S :=
  hE.congr hF (eventuallyEq_quasiSure_iff.1 hEF)

/-- The set of e-variables is solid in the quasi-sure order: a measurable function quasi-surely
below an e-variable is an e-variable. Measurability cannot be dropped, as every e-variable is
measurable. -/
theorem IsEVar.mono_ae (hF : IsEVar F S) (hE : Measurable E) (hEF : E ≤ᶠ[quasiSure S] F) :
    IsEVar E S :=
  ⟨hE, fun _ hP ↦ (lintegral_mono_ae (ae_of_eventually_quasiSure hEF hP)).trans
    (hF.lintegral_le_one hP)⟩

/-- A measurable function quasi-surely equal to an exact e-variable is an exact e-variable. -/
theorem IsExactEVar.congr (hE : IsExactEVar E S) (hF : Measurable F)
    (hEF : E =ᶠ[quasiSure S] F) : IsExactEVar F S where
  toIsEVar := hE.toIsEVar.congr_quasiSure hF hEF
  lintegral_eq_one P hP := by
    rw [← lintegral_congr_ae (ae_of_eventually_quasiSure hEF hP), hE.lintegral_eq_one hP]

/-- The composition of an exact e-variable with a measurable map is an exact e-variable for the
null of the measures whose image is in the original null. -/
theorem IsExactEVar.comp {Y : 𝓨 → ℝ≥0∞} {φ : Ω → 𝓨} (hφ : Measurable φ)
    (h : IsExactEVar Y {P.map φ | P ∈ S}) : IsExactEVar (Y ∘ φ) S where
  toIsEVar := h.toIsEVar.comp hφ
  lintegral_eq_one P hP := by
    have h_eq := h.lintegral_eq_one ⟨P, hP, rfl⟩
    rwa [lintegral_map h.measurable hφ] at h_eq

/-- Under a probability measure of the null, the gain `E - 1` of an exact e-variable has
expectation `0`. -/
theorem IsExactEVar.integral_toReal_sub_one_eq_zero (hE : IsExactEVar E S) (hP : P ∈ S)
    [IsProbabilityMeasure P] : ∫ ω, ((E ω).toReal - 1) ∂P = 0 := by
  have hfin : ∫⁻ ω, E ω ∂P ≠ ∞ := by rw [hE.lintegral_eq_one hP]; exact ENNReal.one_ne_top
  rw [integral_sub (integrable_toReal_of_lintegral_ne_top hE.measurable.aemeasurable hfin)
    (integrable_const 1), integral_toReal hE.measurable.aemeasurable (ae_lt_top hE.measurable hfin),
    hE.lintegral_eq_one hP]
  simp

/-- A likelihood ratio `Q.rnDeriv P` of a probability measure `Q ≪ P` is an exact e-variable for
the simple null `{P}`. -/
theorem isExactEVar_rnDeriv {Q : Measure Ω} [IsProbabilityMeasure Q]
    [Q.HaveLebesgueDecomposition P] (hQP : Q ≪ P) :
    IsExactEVar (Q.rnDeriv P) {P} :=
  .of_lintegral_eq_one (Measure.measurable_rnDeriv Q P) fun _ hP ↦ by
    rw [Set.mem_singleton_iff.1 hP, Measure.lintegral_rnDeriv hQP, measure_univ]

/-- On a countable space, the likelihood ratio `x ↦ Q {x} / P {x}` of a probability measure `Q`
against a probability measure `P` that charges every point is an e-variable for `{P}`: its
expectation under `P` is `1`. -/
theorem isEVar_div_singleton [MeasurableSingletonClass Ω] [Countable Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] [IsProbabilityMeasure P] (hP : ∀ ω, P {ω} ≠ 0) :
    IsEVar (fun ω ↦ Q {ω} / P {ω}) {P} := by
  refine ⟨Measurable.of_discrete, fun _ h ↦ ?_⟩
  rw [Set.mem_singleton_iff.1 h, lintegral_countable',
    tsum_congr fun ω ↦ ENNReal.div_mul_cancel (hP ω) (measure_ne_top _ _)]
  simpa using (lintegral_countable' (μ := Q) 1).symm.le

/-! ### Mixing with a constant -/

/-- **Mixing with a constant.** For a null of measures of mass at most one and `ε ∈ [0, 1]`, the
mixture `(1 - ε) E + ε` of an e-variable `E` with the constant `1` is an e-variable. -/
theorem IsEVar.ofReal_one_sub_mul_add_ofReal (hS : ∀ P ∈ S, P univ ≤ 1) (hE : IsEVar E S) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    IsEVar (fun x ↦ ENNReal.ofReal (1 - ε) * E x + ENNReal.ofReal ε) S := by
  have h : IsEVar (ENNReal.ofReal (1 - ε) • E + ENNReal.ofReal ε • 1) S :=
    convex_isEVar S hE (isEVar_one hS) (zero_le : 0 ≤ ENNReal.ofReal (1 - ε))
      (zero_le : 0 ≤ ENNReal.ofReal ε)
      (by rw [← ENNReal.ofReal_add (by linarith) hε0, sub_add_cancel, ENNReal.ofReal_one])
  convert h using 1
  ext x
  simp

/-! ### E-variables and null sets -/

/-- For a measurable set `s` that is null for every member of `S`, the function equal to `∞` on
`s` and to `0` elsewhere is an e-variable for `S`. -/
theorem isEVar_piecewise_top {s : Set Ω} [DecidablePred (· ∈ s)] (hs : MeasurableSet s)
    (hS : ∀ P ∈ S, P s = 0) : IsEVar (s.piecewise (fun _ ↦ ∞) 0) S :=
  isEVar_zero.congr (measurable_const.piecewise hs measurable_const) fun P hP ↦ by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hS P hP)] with ω hω
    simp [hω]

/-- An e-variable for `S` is almost surely finite under a measure absolutely continuous with
respect to `S` [LRR25, Theorem 2.6]. -/
theorem _root_.MeasureTheory.Measure.AbsolutelyContinuousSet.ae_ne_top {Q : Measure Ω}
    (hQS : Q.AbsolutelyContinuousSet S) (hE : IsEVar E S) : ∀ᵐ ω ∂Q, E ω ≠ ∞ :=
  hQS.ae_of_forall_ae ((measurableSet_singleton ∞).compl.preimage hE.measurable)
    fun _ hP ↦ hE.ae_ne_top hP

/-- A measure is absolutely continuous with respect to `S` exactly when every e-variable for `S`
is almost surely finite under it [LRR25, Theorem 2.6]. -/
theorem absolutelyContinuousSet_iff_forall_isEVar_ae_ne_top {Q : Measure Ω} :
    Q.AbsolutelyContinuousSet S ↔ ∀ E, IsEVar E S → ∀ᵐ ω ∂Q, E ω ≠ ∞ := by
  classical
  refine ⟨fun hQS _ hE ↦ hQS.ae_ne_top hE,
    fun h ↦ Measure.absolutelyContinuousSet_iff.mpr fun s hs hS ↦ ?_⟩
  refine measure_mono_null (fun ω hω ↦ ?_) (ae_iff.mp (h _ (isEVar_piecewise_top hs hS)))
  simp [hω]

/-! ### Markov's inequality -/

/-- **Markov's inequality** for e-variables: for every probability measure `P` of the null and
every level
`α`, the e-variable reaches `α⁻¹` with probability at most `α`. -/
theorem IsEVar.measure_inv_le_le (hE : IsEVar E S) (hP : P ∈ S) (α : ℝ≥0∞) :
    P {ω | α⁻¹ ≤ E ω} ≤ α := by
  rcases eq_or_ne α 0 with rfl | hα₀
  · -- at level `0`, the event is `{E = ∞}`, which is null since `E` is almost surely finite
    refine (measure_eq_zero_iff_ae_notMem.2 ?_).le
    filter_upwards [hE.ae_lt_top hP] with ω hω
    simpa using hω.ne
  rcases eq_or_ne α ∞ with rfl | hα_top
  · exact le_top
  calc P {ω | α⁻¹ ≤ E ω}
  _ ≤ (∫⁻ ω, E ω ∂P) / α⁻¹ :=
    meas_ge_le_lintegral_div hE.measurable.aemeasurable (by simpa) (by simpa)
  _ ≤ 1 / α⁻¹ := by
    gcongr
    exact hE.lintegral_le_one hP
  _ = α := by simp

/-- **Countable mixtures of e-variables.** For a countable family of e-variables `E i` and weights
`w i` with `∑' i, w i ≤ 1`, the mixture `∑' i, w i * E i` is an e-variable. -/
theorem isEVar_tsum_mul {ι : Type*} [Countable ι] {E : ι → Ω → ℝ≥0∞} (hE : ∀ i, IsEVar (E i) S)
    {w : ι → ℝ≥0∞} (hw : ∑' i, w i ≤ 1) :
    IsEVar (fun ω ↦ ∑' i, w i * E i ω) S := by
  refine ⟨Measurable.tsum fun i ↦ (hE i).measurable.const_mul (w i), fun P hP ↦ ?_⟩
  rw [lintegral_tsum fun i ↦ ((hE i).measurable.const_mul (w i)).aemeasurable]
  calc ∑' i, ∫⁻ ω, w i * E i ω ∂P
  _ = ∑' i, w i * ∫⁻ ω, E i ω ∂P := by simp_rw [lintegral_const_mul _ (hE _).measurable]
  _ ≤ ∑' i, w i * 1 := by
    gcongr with i
    exact (hE i).lintegral_le_one hP
  _ ≤ 1 := by simpa using hw

/-- **Finite mixtures of e-variables.** For e-variables `E i`, `i ∈ s`, and weights `w i` with
`∑ i ∈ s, w i ≤ 1`, the mixture `∑ i ∈ s, w i * E i` is an e-variable. -/
theorem isEVar_finsetSum_mul {ι : Type*} {E : ι → Ω → ℝ≥0∞} (s : Finset ι)
    (hE : ∀ i ∈ s, IsEVar (E i) S) {w : ι → ℝ≥0∞} (hw : ∑ i ∈ s, w i ≤ 1) :
    IsEVar (fun ω ↦ ∑ i ∈ s, w i * E i ω) S := by
  convert isEVar_tsum_mul (fun i : s ↦ hE i i.2) (w := fun i ↦ w i)
    (by rwa [Finset.tsum_subtype s w]) using 2 with ω
  exact (Finset.tsum_subtype s fun i ↦ w i * E i ω).symm

/-! ### Products of independent e-variables -/

/-- A finite product `∏ i ∈ s, E i` of e-variables is an e-variable when the whole family `E` is
independent under every member of the null, which makes the null a set of probability
measures. -/
theorem isEVar_finsetProd {ι : Type*} {E : ι → Ω → ℝ≥0∞} (s : Finset ι)
    (hE : ∀ i ∈ s, IsEVar (E i) S) (hind : ∀ P ∈ S, iIndepFun E P) :
    IsEVar (fun ω ↦ ∏ i ∈ s, E i ω) S := by
  refine ⟨Finset.measurable_fun_prod s fun i hi ↦ (hE i hi).measurable, fun P hP ↦ ?_⟩
  have := (hind P hP).isProbabilityMeasure
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun' s (hind P hP)
    fun i hi ↦ (hE i hi).measurable]
  exact Finset.prod_le_one fun i hi ↦ (hE i hi).lintegral_le_one hP

/-- A finite product `∏ i ∈ s, E i` of exact e-variables is an exact e-variable when the whole
family `E` is independent under every member of the null, which makes the null a set of
probability measures. -/
theorem isExactEVar_finsetProd {ι : Type*} {E : ι → Ω → ℝ≥0∞} (s : Finset ι)
    (hE : ∀ i ∈ s, IsExactEVar (E i) S) (hind : ∀ P ∈ S, iIndepFun E P) :
    IsExactEVar (fun ω ↦ ∏ i ∈ s, E i ω) S := by
  refine .of_lintegral_eq_one (Finset.measurable_fun_prod s fun i hi ↦ (hE i hi).measurable)
    fun P hP ↦ ?_
  have := (hind P hP).isProbabilityMeasure
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun' s (hind P hP)
    fun i hi ↦ (hE i hi).measurable]
  exact Finset.prod_eq_one fun i hi ↦ (hE i hi).lintegral_eq_one hP

end ProbabilityTheory
