/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Statlib.EValues.EVariable
import LMLExplore.Algebra.BigOperators.Perm
import LMLExplore.Analysis.Convex.LagrangeDuality
import LMLExplore.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Algebra.BigOperators.Field

/-!
# E-merging functions

An e-merging function of finitely many e-values, indexed by a finite type `ι`, is a measurable
`F : (ι → ℝ≥0∞) → ℝ≥0∞` that turns e-variables into an e-variable, whatever their dependence.
It is defined here through laws: `∫⁻ e, F e ∂μ ≤ 1` for every probability measure `μ` on
`ι → ℝ≥0∞` whose coordinates have expectation at most `1`. This is equivalent to the definition
through random variables, `F ∘ E` being an e-variable for every null hypothesis on every measurable
space in the universe of `ι` and all e-variables `E i`
(`ProbabilityTheory.isEMerging_iff_forall_isEVar`), since the law of `E` under each member of the
null is such a `μ`; the forward direction holds on measurable spaces in any universe
(`ProbabilityTheory.IsEMerging.isEVar_comp`). No monotonicity is assumed, as in [Cle26].

The weighted means `e ↦ w₀ + ∑ i, w i * e i`, with nonnegative weights summing to `1`, are
e-merging, and every e-merging function is dominated by one of them on finite arguments
[Wan25, Theorem 1; Cle26; RW, Theorem 8.4]. Values at infinite arguments are irrelevant, since
e-variables are almost surely finite (`ProbabilityTheory.IsEMerging.of_le`), so domination and
admissibility are statements about finite arguments `e : ι → ℝ≥0`. The admissible e-merging
functions are therefore exactly the weighted means. For symmetric e-merging functions, the weights
of the coordinates can be taken equal, which gives the domination by `λ + (1 - λ) M` with `M` the
arithmetic mean, the characterization of the admissible ones, and the essential domination of
every symmetric e-merging function by `M` [VW21, Proposition 3.1, Theorem 3.2; RW,
Proposition 8.3].

## Main definitions

* `ProbabilityTheory.IsEMerging F`: `F` is an e-merging function.
* `ProbabilityTheory.IsAdmissibleEMerging F`: `F` is an e-merging function that every e-merging
  function dominating it on finite arguments equals there.

## Main statements

* `ProbabilityTheory.IsEMerging.isEVar_comp`: an e-merging function of e-variables is an
  e-variable, for every null of probability measures;
  `ProbabilityTheory.isEMerging_iff_forall_isEVar` characterizes e-merging functions by this
  property.
* `ProbabilityTheory.isEMerging_add_sum_mul`: the weighted means are e-merging.
* `ProbabilityTheory.IsEMerging.exists_le_add_sum_mul`: every e-merging function is dominated by a
  weighted mean on finite arguments [Wan25, Theorem 1; Cle26], and
  `ProbabilityTheory.isEMerging_iff_exists_le_add_sum_mul`: this characterizes e-merging functions
  among measurable functions.
* `ProbabilityTheory.isAdmissibleEMerging_iff`: the admissible e-merging functions are the weighted
  means on finite arguments [Wan25, Theorem 1; RW, Theorem 8.4], and
  `ProbabilityTheory.IsEMerging.exists_isAdmissibleEMerging_le`: every e-merging function is
  dominated by an admissible one.
* `ProbabilityTheory.IsEMerging.exists_le_add_mul_sum_div_card`: a symmetric e-merging function is
  dominated by `λ + (1 - λ) M` for some `λ ∈ [0, 1]` [VW21, Theorem 3.2], and
  `ProbabilityTheory.isAdmissibleEMerging_iff_of_symmetric`: the symmetric admissible ones are
  exactly these functions.
* `ProbabilityTheory.IsEMerging.le_sum_div_card_of_symmetric`: the arithmetic mean essentially
  dominates every symmetric e-merging function: `F e ≤ M e` wherever `1 < F e` [VW21,
  Proposition 3.1; RW, Proposition 8.3].

## Implementation notes

The weights dominating an e-merging function `F` are Lagrange multipliers of the program of
maximizing `∫⁻ F ∂μ` over the probability measures `μ` under the constraints
`∫⁻ e, e i ∂μ ≤ 1`, whose value is at most `1` by definition. The objective and the constraints are
affine under mixtures of measures, so the convex-like form of Lagrange duality
(`LMLExplore.exists_forall_le_add_sum_mul_of_convexLike`) applies on the set of probability
measures, with the Dirac mass at `0` as Slater point; evaluating the Lagrangian at Dirac masses
gives the weighted mean. This is the supporting hyperplane argument of [Cle26] for the concave
envelope of `F`, stated on measures.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6: Definition 8.1, Propositions 8.3 and A.3,
  Theorem 8.4.
* [VW21] V. Vovk and R. Wang, *E-values: calibration, combination and applications*, Ann. Statist.
  49 (2021), arXiv:1912.06116v4: Proposition 3.1, Theorem 3.2, Proposition E.5.
* [Wan25] R. Wang, *The only admissible way of merging arbitrary e-values*, Biometrika (2025),
  arXiv:2409.19888v2: Theorem 1.
* [Cle26] E. Clerico, *A simple geometric proof for the characterisation of e-merging functions*,
  arXiv:2512.09708v3.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

universe u

variable {ι : Type*} [Fintype ι] {F G : (ι → ℝ≥0∞) → ℝ≥0∞}

/-- An **e-merging function** of e-values indexed by `ι` [RW, Definition 8.1, Proposition A.3;
Cle26]: a measurable `F : (ι → ℝ≥0∞) → ℝ≥0∞` with `∫⁻ e, F e ∂μ ≤ 1` for every probability
measure `μ` on `ι → ℝ≥0∞` whose coordinates have expectation at most `1`. It is not required to be
monotone. -/
structure IsEMerging (F : (ι → ℝ≥0∞) → ℝ≥0∞) : Prop where
  measurable : Measurable F
  lintegral_le_one : ∀ (μ : Measure (ι → ℝ≥0∞)) [IsProbabilityMeasure μ],
    (∀ i, ∫⁻ e, e i ∂μ ≤ 1) → ∫⁻ e, F e ∂μ ≤ 1

omit [Fintype ι] in
/-- An e-merging function of e-variables is an e-variable, for every null hypothesis of
probability measures, with no assumption on the dependence of the e-variables. -/
theorem IsEMerging.isEVar_comp {Ω : Type*} {mΩ : MeasurableSpace Ω} {S : Set (Measure Ω)}
    (hF : IsEMerging F) (hS : ∀ P ∈ S, IsProbabilityMeasure P) {E : ι → Ω → ℝ≥0∞}
    (hE : ∀ i, IsEVar (E i) S) : IsEVar (fun ω ↦ F fun i ↦ E i ω) S := by
  have hm : Measurable fun ω i ↦ E i ω := measurable_pi_iff.2 fun i ↦ (hE i).measurable
  refine IsEVar.of_lintegral_le_one hS (hF.measurable.comp hm) fun P hP ↦ ?_
  have := hS P hP
  rw [← lintegral_map hF.measurable hm]
  refine hF.lintegral_le_one _ fun i ↦ ?_
  rw [lintegral_map (measurable_pi_apply i) hm]
  simpa using (hE i).lintegral_le_measure_univ P hP

/-- A function of e-values is e-merging exactly when it turns e-variables into an e-variable, for
every null hypothesis of probability measures on every measurable space in the universe of `ι`.
The forward direction holds on measurable spaces in any universe
(`ProbabilityTheory.IsEMerging.isEVar_comp`). -/
theorem isEMerging_iff_forall_isEVar {ι : Type u} {F : (ι → ℝ≥0∞) → ℝ≥0∞} :
    IsEMerging F ↔ ∀ (Ω : Type u) [MeasurableSpace Ω] (S : Set (Measure Ω)),
      (∀ P ∈ S, IsProbabilityMeasure P) → ∀ E : ι → Ω → ℝ≥0∞, (∀ i, IsEVar (E i) S) →
        IsEVar (fun ω ↦ F fun i ↦ E i ω) S := by
  refine ⟨fun hF Ω _ S hS E hE ↦ hF.isEVar_comp hS hE, fun h ↦ ?_⟩
  set S : Set (Measure (ι → ℝ≥0∞)) :=
    {μ | IsProbabilityMeasure μ ∧ ∀ i, ∫⁻ e, e i ∂μ ≤ 1}
  have hS : ∀ μ ∈ S, IsProbabilityMeasure μ := fun μ hμ ↦ hμ.1
  have hF := h (ι → ℝ≥0∞) S hS (fun i e ↦ e i)
    fun i ↦ IsEVar.of_lintegral_le_one hS (measurable_pi_apply i) fun μ hμ ↦ hμ.2 i
  refine ⟨hF.measurable, fun μ _ hle ↦ ?_⟩
  simpa using hF.lintegral_le_measure_univ μ ⟨‹_›, hle⟩

omit [Fintype ι] in
/-- An e-merging function of finitely many e-values is finite at finite arguments. -/
theorem IsEMerging.lt_top [Finite ι] (hF : IsEMerging F) (e : ι → ℝ≥0) :
    F (fun i ↦ e i) < ∞ := by
  have := Fintype.ofFinite ι
  -- Mix the Dirac masses at `0` and at `e`, with weight `p = (1 + ∑ i, e i)⁻¹` at `e`.
  set s : ℝ≥0∞ := 1 + ∑ i, (e i : ℝ≥0∞)
  have hs : s ≠ ∞ := by simp [s]
  have hs0 : s ≠ 0 := by simp [s]
  set p := s⁻¹
  have hp0 : p ≠ 0 := ENNReal.inv_ne_zero.2 hs
  have hp1 : p ≤ 1 := ENNReal.inv_le_one.2 le_self_add
  set μ : Measure (ι → ℝ≥0∞) :=
    (1 - p) • Measure.dirac (0 : ι → ℝ≥0∞) + p • Measure.dirac (fun i ↦ (e i : ℝ≥0∞)) with hμ_def
  have hμ : IsProbabilityMeasure μ := ⟨by simp [μ, tsub_add_cancel_of_le hp1]⟩
  have hle := hF.lintegral_le_one μ fun i ↦ by
    simp only [hμ_def, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
      smul_eq_mul]
    calc (1 - p) * (0 : ι → ℝ≥0∞) i + p * e i ≤ p * s := by
          rw [Pi.zero_apply, mul_zero, zero_add]
          gcongr
          exact le_add_left (Finset.single_le_sum (f := fun i ↦ (e i : ℝ≥0∞))
            (fun _ _ ↦ zero_le) (Finset.mem_univ i))
      _ = 1 := ENNReal.inv_mul_cancel hs0 hs
  simp only [hμ_def, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul] at hle
  refine lt_top_iff_ne_top.2 fun htop ↦ ?_
  rw [htop, ENNReal.mul_top hp0, add_top] at hle
  exact ENNReal.top_ne_one (le_antisymm hle le_top)

omit [Fintype ι] in
/-- A function dominated on finite arguments by `G` is dominated by `G` almost everywhere, under
every measure on `ι → ℝ≥0∞` whose coordinates are almost everywhere finite. -/
theorem ae_le_of_forall_nnreal_le {ν : Measure (ι → ℝ≥0∞)} (hfin : ∀ᵐ e ∂ν, ∀ i, e i ≠ ∞)
    (hle : ∀ e : ι → ℝ≥0, F (fun i ↦ e i) ≤ G (fun i ↦ e i)) : F ≤ᵐ[ν] G := by
  filter_upwards [hfin] with e he
  have : e = fun i ↦ ((e i).toNNReal : ℝ≥0∞) := funext fun i ↦ (ENNReal.coe_toNNReal (he i)).symm
  rw [this]
  exact hle _

omit [Fintype ι] in
/-- A measurable function dominated on finite arguments by an e-merging function is e-merging:
the values of an e-merging function at infinite arguments are irrelevant, since the
coordinates of `μ` are `μ`-almost surely finite. -/
theorem IsEMerging.of_le [Countable ι] (hG : IsEMerging G) (hF : Measurable F)
    (hle : ∀ e : ι → ℝ≥0, F (fun i ↦ e i) ≤ G (fun i ↦ e i)) : IsEMerging F := by
  refine ⟨hF, fun μ _ he ↦ (lintegral_mono_ae (ae_le_of_forall_nnreal_le ?_ hle)).trans
    (hG.lintegral_le_one μ he)⟩
  exact ae_all_iff.2 fun i ↦
    (ae_lt_top (measurable_pi_apply i) ((he i).trans_lt ENNReal.one_lt_top).ne).mono
      fun _ h ↦ h.ne

/-- The **weighted means** `e ↦ w₀ + ∑ i, w i * e i`, with nonnegative weights of total mass at
most `1`, are e-merging. -/
theorem isEMerging_add_sum_mul {w₀ : ℝ≥0} {w : ι → ℝ≥0} (hw : w₀ + ∑ i, w i ≤ 1) :
    IsEMerging fun e : ι → ℝ≥0∞ ↦ (w₀ : ℝ≥0∞) + ∑ i, (w i : ℝ≥0∞) * e i := by
  refine ⟨by fun_prop, fun μ _ he ↦ ?_⟩
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_finsetSum _ fun i _ ↦ (measurable_pi_apply i).const_mul _]
  rw [Finset.sum_congr rfl fun i _ ↦
    lintegral_const_mul _ (measurable_pi_apply i : Measurable fun e : ι → ℝ≥0∞ ↦ e i)]
  calc (w₀ : ℝ≥0∞) + ∑ i, (w i : ℝ≥0∞) * ∫⁻ e, e i ∂μ ≤ w₀ + ∑ i, (w i : ℝ≥0∞) * 1 := by
        gcongr with i
        exact he i
    _ ≤ 1 := by simp only [mul_one]; exact_mod_cast hw

/-- The weighted mean of finite arguments has the same value computed in `ℝ≥0` and in `ℝ≥0∞`. -/
private lemma coe_add_sum_mul (w₀ : ℝ≥0) (w e : ι → ℝ≥0) :
    ((w₀ + ∑ i, w i * e i : ℝ≥0) : ℝ≥0∞) = w₀ + ∑ i, (w i : ℝ≥0∞) * e i := by
  rw [ENNReal.coe_add, ENNReal.ofNNReal_finsetSum]
  simp only [ENNReal.coe_mul]

omit [Fintype ι] in
/-- The objective `μ ↦ -∫⁻ F ∂μ` and the constraints `μ ↦ ∫⁻ e, e i ∂μ - 1` are jointly
convex-like on the probability measures against which `F` and the coordinates have finite
integrals: mixtures of measures mix the integrals. -/
private lemma jointlyConvexLikeOn_lintegral (F : (ι → ℝ≥0∞) → ℝ≥0∞) :
    LMLExplore.JointlyConvexLikeOn
      {μ : Measure (ι → ℝ≥0∞) | IsProbabilityMeasure μ ∧ ∫⁻ e, F e ∂μ ≠ ∞ ∧
        ∀ i, ∫⁻ e, e i ∂μ ≠ ∞}
      (fun μ ↦ -(∫⁻ e, F e ∂μ).toReal) (fun i μ ↦ (∫⁻ e, e i ∂μ).toReal - 1) := by
  refine LMLExplore.jointlyConvexLikeOn_iff.2 ?_
  rintro μ ⟨hμ, hμF, hμe⟩ ν ⟨hν, hνF, hνe⟩ a b ha hb hab
  have hprob : IsProbabilityMeasure (ENNReal.ofReal a • μ + ENNReal.ofReal b • ν) :=
    ⟨by simp [← ENNReal.ofReal_add ha hb, hab]⟩
  refine ⟨_, ⟨hprob, lintegral_ofReal_smul_add_smul_ne_top hμF hνF,
    fun i ↦ lintegral_ofReal_smul_add_smul_ne_top (hμe i) (hνe i)⟩,
    by rw [toReal_lintegral_ofReal_smul_add_smul ha hb hμF hνF]; linarith, fun i ↦ ?_⟩
  rw [toReal_lintegral_ofReal_smul_add_smul ha hb (hμe i) (hνe i)]
  linear_combination hab

/-- **Every e-merging function is dominated by a weighted mean** [Wan25, Theorem 1; Cle26; RW,
Theorem 8.4]: for some nonnegative weights `w₀` and `w i` summing to `1`,
`F e ≤ w₀ + ∑ i, w i * e i` at every finite argument `e`. No monotonicity of `F` is assumed. -/
theorem IsEMerging.exists_le_add_sum_mul (hF : IsEMerging F) :
    ∃ (w₀ : ℝ≥0) (w : ι → ℝ≥0), w₀ + ∑ i, w i = 1 ∧
      ∀ e : ι → ℝ≥0, F (fun i ↦ e i) ≤ w₀ + ∑ i, (w i : ℝ≥0∞) * e i := by
  -- The program: maximize `∫⁻ F ∂μ` over the probability measures `μ` on which `F` and the
  -- coordinates have finite integrals, under the constraints `∫⁻ e, e i ∂μ ≤ 1`.
  set C : Set (Measure (ι → ℝ≥0∞)) :=
    {μ | IsProbabilityMeasure μ ∧ ∫⁻ e, F e ∂μ ≠ ∞ ∧ ∀ i, ∫⁻ e, e i ∂μ ≠ ∞}
  have hdirac (e : ι → ℝ≥0) : Measure.dirac (fun i ↦ (e i : ℝ≥0∞)) ∈ C :=
    ⟨inferInstance, by rw [lintegral_dirac]; exact (hF.lt_top e).ne,
      fun i ↦ by rw [lintegral_dirac]; exact ENNReal.coe_ne_top⟩
  have hslater : ∃ μ ∈ C, ∀ i, (fun i μ ↦ (∫⁻ e, e i ∂μ).toReal - 1) i μ < 0 :=
    ⟨_, hdirac 0, fun i ↦ by simp [lintegral_dirac]⟩
  have hvalue : ∀ μ ∈ C, (∀ i, (∫⁻ e, e i ∂μ).toReal - 1 ≤ 0) →
      -1 ≤ -(∫⁻ e, F e ∂μ).toReal := by
    rintro μ ⟨hμ, -, hμe⟩ hle
    have h1 : ∫⁻ e, F e ∂μ ≤ 1 := hF.lintegral_le_one μ fun i ↦
      (ENNReal.toReal_le_toReal (hμe i) ENNReal.one_ne_top).1 (by simpa using hle i)
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h1
  obtain ⟨π, hπ⟩ := LMLExplore.exists_forall_le_add_sum_mul_of_convexLike
    (jointlyConvexLikeOn_lintegral F) hslater hvalue
  -- The Lagrangian at the Dirac mass at `e` bounds `F e`.
  have hbound (e : ι → ℝ≥0) :
      (F fun i ↦ e i).toReal ≤ 1 - ∑ i, (π i : ℝ) + ∑ i, (π i : ℝ) * e i := by
    have := hπ _ (hdirac e)
    simp only [lintegral_dirac, ENNReal.coe_toReal, mul_sub, mul_one,
      Finset.sum_sub_distrib] at this
    linarith
  have hsum : ∑ i, π i ≤ 1 := by
    have := (hbound 0).trans' ENNReal.toReal_nonneg
    simp only [Pi.zero_apply, NNReal.coe_zero, mul_zero, Finset.sum_const_zero, add_zero,
      sub_nonneg] at this
    exact_mod_cast this
  refine ⟨1 - ∑ i, π i, π, tsub_add_cancel_of_le hsum, fun e ↦ ?_⟩
  rw [← coe_add_sum_mul, ← ENNReal.ofReal_toReal (hF.lt_top e).ne,
    ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ((hbound e).trans_eq ?_)
  rw [NNReal.coe_add, NNReal.coe_sub hsum, NNReal.coe_one, NNReal.coe_sum, NNReal.coe_sum]
  simp only [NNReal.coe_mul]

/-- **E-merging functions are the functions dominated by weighted means**: a measurable function
is e-merging exactly when it is dominated, at finite arguments, by `e ↦ w₀ + ∑ i, w i * e i` for
some nonnegative weights summing to `1`. -/
theorem isEMerging_iff_exists_le_add_sum_mul :
    IsEMerging F ↔ Measurable F ∧ ∃ (w₀ : ℝ≥0) (w : ι → ℝ≥0), w₀ + ∑ i, w i = 1 ∧
      ∀ e : ι → ℝ≥0, F (fun i ↦ e i) ≤ w₀ + ∑ i, (w i : ℝ≥0∞) * e i := by
  refine ⟨fun hF ↦ ⟨hF.measurable, hF.exists_le_add_sum_mul⟩, ?_⟩
  rintro ⟨hF, w₀, w, hw, hle⟩
  exact (isEMerging_add_sum_mul hw.le).of_le hF hle

omit [Fintype ι] in
/-- If a weighted mean is at most another one at every finite argument, then each weight of the
first is at most the corresponding weight of the second. -/
private lemma le_and_forall_le_of_add_sum_mul_le [Fintype ι] {w₀ v₀ : ℝ≥0} {w v : ι → ℝ≥0}
    (h : ∀ e : ι → ℝ≥0, w₀ + ∑ i, w i * e i ≤ v₀ + ∑ i, v i * e i) :
    w₀ ≤ v₀ ∧ ∀ i, w i ≤ v i := by
  classical
  refine ⟨by simpa using h 0, fun i ↦ le_of_not_gt fun hlt ↦ ?_⟩
  -- At the argument `t` on coordinate `i` and `0` elsewhere, for `t` large, the first mean
  -- exceeds the second.
  have hd : (0 : ℝ) < w i - v i := sub_pos.2 (by exact_mod_cast hlt)
  set t : ℝ := (v₀ + 1) / (w i - v i)
  have ht := h fun j ↦ if j = i then t.toNNReal else 0
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at ht
  have ht' : (w₀ : ℝ) + w i * t ≤ v₀ + v i * t := by
    simpa [Real.coe_toNNReal _ (by positivity : 0 ≤ t)] using NNReal.coe_le_coe.2 ht
  have h2 : (w i : ℝ) * t - v i * t = v₀ + 1 := by
    rw [← sub_mul, mul_div_cancel₀ _ hd.ne']
  linarith [NNReal.coe_nonneg w₀]

/-- An **admissible** e-merging function [VW21, §3]: an e-merging function `F`
such that every e-merging function dominating `F` at finite arguments equals `F` there. Values
at infinite arguments are not compared, since they do not affect the e-merging property
(`ProbabilityTheory.IsEMerging.of_le`). -/
structure IsAdmissibleEMerging (F : (ι → ℝ≥0∞) → ℝ≥0∞) : Prop extends IsEMerging F where
  eq_of_le : ∀ G : (ι → ℝ≥0∞) → ℝ≥0∞, IsEMerging G →
    (∀ e : ι → ℝ≥0, F (fun i ↦ e i) ≤ G (fun i ↦ e i)) →
      ∀ e : ι → ℝ≥0, G (fun i ↦ e i) = F (fun i ↦ e i)

/-- **The admissible e-merging functions are the weighted means** [Wan25, Theorem 1; RW,
Theorem 8.4]: a function is an admissible e-merging function exactly when it is measurable and
equal, at finite arguments, to `e ↦ w₀ + ∑ i, w i * e i` for some nonnegative weights summing
to `1`. -/
theorem isAdmissibleEMerging_iff :
    IsAdmissibleEMerging F ↔ Measurable F ∧ ∃ (w₀ : ℝ≥0) (w : ι → ℝ≥0), w₀ + ∑ i, w i = 1 ∧
      ∀ e : ι → ℝ≥0, F (fun i ↦ e i) = w₀ + ∑ i, (w i : ℝ≥0∞) * e i := by
  classical
  constructor
  · intro hF
    obtain ⟨w₀, w, hw, hle⟩ := hF.exists_le_add_sum_mul
    exact ⟨hF.measurable, w₀, w, hw,
      fun e ↦ (hF.eq_of_le _ (isEMerging_add_sum_mul hw.le) hle e).symm⟩
  · rintro ⟨hF, w₀, w, hw, heq⟩
    have hFm : IsEMerging F := (isEMerging_add_sum_mul hw.le).of_le hF fun e ↦ (heq e).le
    refine ⟨hFm, fun G hG hle e ↦ le_antisymm ?_ (hle e)⟩
    -- `G` is dominated by a weighted mean `v`, which dominates the weighted mean `w`; the two
    -- weight vectors are then equal.
    obtain ⟨v₀, v, hv, hGv⟩ := hG.exists_le_add_sum_mul
    have hwv (e : ι → ℝ≥0) : w₀ + ∑ i, w i * e i ≤ v₀ + ∑ i, v i * e i := by
      have := ((heq e).symm.trans_le (hle e)).trans (hGv e)
      rwa [← coe_add_sum_mul, ← coe_add_sum_mul, ENNReal.coe_le_coe] at this
    obtain ⟨hw₀, hwi⟩ := le_and_forall_le_of_add_sum_mul_le hwv
    have hsum : ∑ i, w i ≤ ∑ i, v i := Finset.sum_le_sum fun i _ ↦ hwi i
    obtain ⟨rfl, hsum_eq⟩ := (add_eq_add_iff_eq_and_eq hw₀ hsum).1 (hw.trans hv.symm)
    have hvw : v = w := funext fun i ↦ ((Finset.sum_eq_sum_iff_of_le fun i _ ↦ hwi i).1
      hsum_eq i (Finset.mem_univ i)).symm
    subst hvw
    exact (hGv e).trans_eq (heq e).symm

omit [Fintype ι] in
/-- **Every e-merging function is dominated by an admissible one** [VW21, Proposition E.5], at
finite arguments: by a weighted mean. -/
theorem IsEMerging.exists_isAdmissibleEMerging_le [Finite ι] (hF : IsEMerging F) :
    ∃ G, IsAdmissibleEMerging G ∧ ∀ e : ι → ℝ≥0, F (fun i ↦ e i) ≤ G (fun i ↦ e i) := by
  have := Fintype.ofFinite ι
  obtain ⟨w₀, w, hw, hle⟩ := hF.exists_le_add_sum_mul
  exact ⟨fun e ↦ (w₀ : ℝ≥0∞) + ∑ i, (w i : ℝ≥0∞) * e i, isAdmissibleEMerging_iff.2
    ⟨by fun_prop, w₀, w, hw, fun e ↦ rfl⟩, hle⟩

/-! ### Symmetric e-merging functions -/

/-- `λ + (1 - λ) M`, for the arithmetic mean `M`, is the weighted mean with the weight
`(1 - λ) / K` on each of the `K` coordinates. -/
private lemma mul_sum_div_card_eq_sum_mul (lam : ℝ≥0) (e : ι → ℝ≥0) :
    (1 - lam) * ((∑ i, e i) / Fintype.card ι) = ∑ i, (1 - lam) / Fintype.card ι * e i := by
  rw [← Finset.mul_sum, div_mul_eq_mul_div, mul_div_assoc]

/-- The arithmetic mean of finite arguments has the same value computed in `ℝ≥0` and in
`ℝ≥0∞`. -/
private lemma coe_sum_div_card (e : ι → ℝ≥0) :
    (((∑ i, e i) / Fintype.card ι : ℝ≥0) : ℝ≥0∞) = (∑ i, (e i : ℝ≥0∞)) / Fintype.card ι := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · rw [ENNReal.coe_div (by simp [Fintype.card_ne_zero]), ENNReal.ofNNReal_finsetSum,
      ENNReal.coe_natCast]

/-- `λ + (1 - λ) M`, for the arithmetic mean `M` of finite arguments, has the same value computed
in `ℝ≥0` and in `ℝ≥0∞`. -/
private lemma coe_add_mul_sum_div_card (lam : ℝ≥0) (e : ι → ℝ≥0) :
    ((lam + (1 - lam) * ((∑ i, e i) / Fintype.card ι) : ℝ≥0) : ℝ≥0∞) =
      lam + (1 - lam) * ((∑ i, (e i : ℝ≥0∞)) / Fintype.card ι) := by
  rw [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_sub, ENNReal.coe_one, coe_sum_div_card]

/-- **Symmetrizing a dominating weighted mean**: if `F` is symmetric at finite arguments and
dominated there by the weighted mean with weights `w₀` and `w i`, then it is also dominated by the
weighted mean with weights `w₀` and the averages `(∑ σ, w (σ j)) / N` over the `N` permutations
`σ`. -/
private lemma le_add_sum_div_card_mul_of_symmetric [DecidableEq ι] {w₀ : ℝ≥0} {w : ι → ℝ≥0}
    (hsymm : ∀ (σ : Equiv.Perm ι) (e : ι → ℝ≥0), F (fun i ↦ e (σ i)) = F (fun i ↦ e i))
    (hle : ∀ e : ι → ℝ≥0, F (fun i ↦ e i) ≤ w₀ + ∑ i, (w i : ℝ≥0∞) * e i) (e : ι → ℝ≥0) :
    F (fun i ↦ e i) ≤
      ↑(w₀ + ∑ j, (∑ σ : Equiv.Perm ι, w (σ j)) / Fintype.card (Equiv.Perm ι) * e j) := by
  set N : ℝ≥0 := (Fintype.card (Equiv.Perm ι) : ℝ≥0)
  have hN : N ≠ 0 := by simp [N, Fintype.card_ne_zero]
  -- `F e = F (e ∘ σ⁻¹)` is dominated by the weighted mean with the weights `w ∘ σ`.
  have hσ (σ : Equiv.Perm ι) : F (fun i ↦ e i) ≤ ↑(w₀ + ∑ j, w (σ j) * e j) := by
    refine ((hsymm σ⁻¹ e).symm.trans_le (hle _)).trans_eq ?_
    rw [coe_add_sum_mul, ← Equiv.sum_comp σ fun j ↦ (w j : ℝ≥0∞) * e (σ⁻¹ j)]
    simp
  -- Average these bounds over the permutations `σ`.
  have hsum : (N : ℝ≥0∞) * F (fun i ↦ e i) ≤
      ↑(∑ σ : Equiv.Perm ι, (w₀ + ∑ j, w (σ j) * e j)) := by
    have := Finset.card_nsmul_le_sum Finset.univ _ _ fun σ _ ↦ hσ σ
    rwa [Finset.card_univ, nsmul_eq_mul, ← ENNReal.coe_natCast,
      ← ENNReal.ofNNReal_finsetSum] at this
  have hcalc : (∑ σ : Equiv.Perm ι, (w₀ + ∑ j, w (σ j) * e j)) / N =
      w₀ + ∑ j, (∑ σ : Equiv.Perm ι, w (σ j)) / N * e j := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_div,
      mul_div_cancel_left₀ _ hN, Finset.sum_comm, Finset.sum_div]
    simp only [← Finset.sum_mul, mul_div_right_comm]
  rw [← hcalc, ENNReal.coe_div hN, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hN))
    (Or.inl ENNReal.coe_ne_top), mul_comm]
  exact hsum

/-- **A symmetric e-merging function is dominated by a mixture of `1` and the arithmetic mean**
[VW21, Theorem 3.2]: for some `λ ∈ [0, 1]`, `F e ≤ λ + (1 - λ) * (∑ i, e i) / K` at every finite
argument `e`, with `K` the number of e-values. Symmetry is needed only at finite arguments. -/
theorem IsEMerging.exists_le_add_mul_sum_div_card (hF : IsEMerging F)
    (hsymm : ∀ (σ : Equiv.Perm ι) (e : ι → ℝ≥0), F (fun i ↦ e (σ i)) = F (fun i ↦ e i)) :
    ∃ lam ≤ (1 : ℝ≥0), ∀ e : ι → ℝ≥0,
      F (fun i ↦ e i) ≤ lam + (1 - lam) * ((∑ i, (e i : ℝ≥0∞)) / Fintype.card ι) := by
  classical
  obtain ⟨w₀, w, hw, hle⟩ := hF.exists_le_add_sum_mul
  refine ⟨w₀, hw ▸ le_self_add, fun e ↦ ?_⟩
  rw [← coe_add_mul_sum_div_card, mul_sum_div_card_eq_sum_mul]
  refine (le_add_sum_div_card_mul_of_symmetric hsymm hle e).trans_eq ?_
  -- The averaged weights are all equal to `(1 - w₀) / K`.
  simp_rw [Equiv.Perm.sum_apply_div_card]
  rw [← hw, add_tsub_cancel_left]

/-- **The admissible symmetric e-merging functions** [VW21, Theorem 3.2]: a function of at least
one e-value, symmetric at finite arguments, is an admissible e-merging function exactly when it is
measurable and equal, at finite arguments, to `λ + (1 - λ) * (∑ i, e i) / K` for some
`λ ∈ [0, 1]`. -/
theorem isAdmissibleEMerging_iff_of_symmetric [Nonempty ι]
    (hsymm : ∀ (σ : Equiv.Perm ι) (e : ι → ℝ≥0), F (fun i ↦ e (σ i)) = F (fun i ↦ e i)) :
    IsAdmissibleEMerging F ↔ Measurable F ∧ ∃ lam ≤ (1 : ℝ≥0), ∀ e : ι → ℝ≥0,
      F (fun i ↦ e i) = lam + (1 - lam) * ((∑ i, (e i : ℝ≥0∞)) / Fintype.card ι) := by
  have hcard : (Fintype.card ι : ℝ≥0) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hweights (lam : ℝ≥0) (hlam : lam ≤ 1) :
      lam + ∑ _i : ι, (1 - lam) / Fintype.card ι = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hcard,
      add_tsub_cancel_of_le hlam]
  -- `λ + (1 - λ) M` is the weighted mean with the weight `(1 - λ) / K` on each coordinate.
  have hGe (lam : ℝ≥0) (e : ι → ℝ≥0) :
      (lam : ℝ≥0∞) + ∑ i, (((1 - lam) / Fintype.card ι : ℝ≥0) : ℝ≥0∞) * e i =
        lam + (1 - lam) * ((∑ i, (e i : ℝ≥0∞)) / Fintype.card ι) := by
    rw [← coe_add_mul_sum_div_card, mul_sum_div_card_eq_sum_mul, coe_add_sum_mul]
  constructor
  · intro hF
    obtain ⟨lam, hlam, hle⟩ := hF.toIsEMerging.exists_le_add_mul_sum_div_card hsymm
    refine ⟨hF.measurable, lam, hlam, fun e ↦ ?_⟩
    have hG := isEMerging_add_sum_mul (hweights lam hlam).le
    rw [← hGe]
    exact (hF.eq_of_le _ hG (fun e ↦ (hle e).trans_eq (hGe lam e).symm) e).symm
  · rintro ⟨hF, lam, hlam, heq⟩
    exact isAdmissibleEMerging_iff.2 ⟨hF, lam, fun _ ↦ (1 - lam) / Fintype.card ι,
      hweights lam hlam, fun e ↦ (heq e).trans (hGe lam e).symm⟩

/-- **The arithmetic mean essentially dominates every symmetric e-merging function** [VW21,
Proposition 3.1; RW, Proposition 8.3]: wherever an e-merging function symmetric at finite
arguments exceeds `1`, it is at most the arithmetic mean `(∑ i, e i) / K`. -/
theorem IsEMerging.le_sum_div_card_of_symmetric (hF : IsEMerging F)
    (hsymm : ∀ (σ : Equiv.Perm ι) (e : ι → ℝ≥0), F (fun i ↦ e (σ i)) = F (fun i ↦ e i))
    {e : ι → ℝ≥0} (he : 1 < F (fun i ↦ e i)) :
    F (fun i ↦ e i) ≤ (∑ i, (e i : ℝ≥0∞)) / Fintype.card ι := by
  obtain ⟨lam, hlam, hle⟩ := hF.exists_le_add_mul_sum_div_card hsymm
  have hle' := (hle e).trans_eq (coe_add_mul_sum_div_card lam e).symm
  rw [← coe_sum_div_card]
  set m := (∑ i, e i) / (Fintype.card ι : ℝ≥0)
  refine hle'.trans (ENNReal.coe_le_coe.2 ?_)
  -- If `m ≤ 1`, the bound `λ + (1 - λ) m` is at most `1`, which `F e` exceeds.
  have hm : 1 ≤ m := by
    refine le_of_not_gt fun hm ↦ ?_
    have : lam + (1 - lam) * m ≤ 1 := by
      calc lam + (1 - lam) * m ≤ lam + (1 - lam) * 1 := by gcongr
        _ = 1 := by rw [mul_one, add_tsub_cancel_of_le hlam]
    exact (he.trans_le hle').not_ge (by exact_mod_cast this)
  calc lam + (1 - lam) * m ≤ lam * m + (1 - lam) * m := by
        gcongr
        exact le_mul_of_one_le_right' hm
    _ = m := by rw [← add_mul, add_tsub_cancel_of_le hlam, one_mul]

end ProbabilityTheory
