/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Admissible
public import LMLExplore.EValues.Numeraire
public import Mathlib.Probability.Distributions.Poisson.Basic
import LMLExplore.Probability.Distributions.Poisson

/-!
# Numeraires and admissible e-variables

Statlib's numeraire of a null `S` against an alternative `Q` is the e-variable that maximizes the
expected logarithm under `Q`; an admissible e-variable is one that no e-variable improves in a way
that the null can see. This file compares the two notions.

* **Which e-variables are numeraires.** This is in `LMLExplore.EValues.Numeraire`
  (`ProbabilityTheory.exists_isNumeraire_iff` and the results around it): for a null of measures of
  mass at most one, an e-variable `E` is a numeraire against some probability measure exactly when
  it is exact under a member `μ` of the effective null, `∫⁻ E ∂μ = 1`, or infinite at some point.
* **Numeraires against dominating alternatives are admissible.** A numeraire against `Q` is at
  least, `Q`-almost surely, every e-variable that dominates it quasi-surely, so it is admissible
  as soon as every member of the null is absolutely continuous with respect to `Q`. Without this
  domination it need not be: on `Bool`, the indicator of `true` is a numeraire of the two Dirac
  masses against the Dirac mass at `true`, and is not admissible.
* **Finite nulls.** For a finite null of finite measures, an e-variable is admissible exactly when
  it is strongly admissible [RW, Proposition 2.16], and every e-variable is at most an admissible
  one; both are in `LMLExplore.EValues.Admissible`
  (`ProbabilityTheory.isAdmissibleEVar_iff_isStronglyAdmissibleEVar_of_finite`,
  `ProbabilityTheory.IsEVar.exists_isAdmissibleEVar_le`). Then every admissible e-variable is a
  numeraire against some alternative, every numeraire is almost surely equal to an admissible
  numeraire, and the numeraires against the alternatives that dominate the null are the admissible
  e-variables that are almost surely positive under the null.
* **The Poisson family.** For the null of the Poisson laws, `2 · 𝟙{k odd}` is an admissible
  e-variable, and it is a numeraire against no nonzero finite measure. So for an infinite null an
  admissible e-variable need not be a numeraire against any alternative.

Following Statlib, e-variables are `ℝ≥0∞`-valued, the bound of an e-variable is `1` whatever the
mass of the member, and exact means `∫⁻ E ∂P = 1`.

## Main statements

* `ProbabilityTheory.IsNumeraire.ae_le_of_eventuallyLE`,
  `ProbabilityTheory.IsNumeraire.isAdmissibleEVar`: a numeraire against an alternative that
  dominates the null is admissible [EVR26, Note 42, Theorem 8].
* `ProbabilityTheory.exists_isNumeraire_not_isAdmissibleEVar`: the domination is needed in
  `ProbabilityTheory.IsNumeraire.isAdmissibleEVar`, even for a finite null [EVR26, Note 42,
  Theorem 9 (3)].
* `ProbabilityTheory.IsAdmissibleEVar.exists_isNumeraire_withDensity`: admissible e-variables of a
  finite null are numeraires [EVR26, Note 42, Theorem 9 (2)], through
  `ProbabilityTheory.isNumeraire_withDensity_of_mem_convexHull`.
* `ProbabilityTheory.IsNumeraire.exists_isAdmissibleEVar_ae_eq`: numeraires of a finite null are
  almost surely equal to admissible ones [EVR26, Note 42, Theorem 9 (3)].
* `ProbabilityTheory.exists_isNumeraire_absolutelyContinuous_iff`: the numeraires against
  dominating alternatives [EVR26, Note 42, Theorem 9 (4)].
* `ProbabilityTheory.isAdmissibleEVar_indicator_odd_poissonMeasure`,
  `ProbabilityTheory.not_isNumeraire_indicator_odd_poissonMeasure`: the Poisson family
  [EVR26, Note 42, Theorem 10].

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes and Lean
  library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026, Note 42, whose file
  `Results/NumeraireAdmissible.lean` this file adapts.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, Proposition 2.16.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S : Set (Measure Ω)} {E F : Ω → ℝ≥0∞}
  {Q μ : Measure Ω}

/-! ### A numeraire against an alternative that dominates the null is admissible -/

/-- **A numeraire is maximal almost surely under its alternative** [EVR26, Note 42, Theorem 8].
Let `E` be a numeraire of `S` against `Q`, with `Q {0 < E < ∞} < ∞` (for instance `Q` finite). An
e-variable `F` for `S` that is quasi-surely at least `E` is at most `E`, `Q`-almost surely. -/
theorem IsNumeraire.ae_le_of_eventuallyLE (hE : IsNumeraire E S Q) (hQ : Q E.fsupport ≠ ∞)
    (hF : IsEVar F S) (hEF : E ≤ᶠ[quasiSure S] F) : F ≤ᵐ[Q] E := by
  have hE_meas := hE.measurable
  have h_fs : MeasurableSet E.fsupport := hE_meas.measurable_fsupport
  -- the maximum `G` of `E` and `F` is an e-variable, and `G / E` is at least `1` on the finite
  -- support of `E`; since `∫⁻ G / E ∂Q ≤ Q E.fsupport`, `G / E` is `Q`-almost surely the
  -- indicator of the finite support of `E`
  have hG : IsEVar (fun ω ↦ max (E ω) (F ω)) S :=
    hF.congr_quasiSure (hE_meas.max hF.measurable) (hEF.mono fun ω hω ↦ (max_eq_right hω).symm)
  have h_le : E.fsupport.indicator 1 ≤ fun ω ↦ max (E ω) (F ω) / E ω := by
    intro ω
    by_cases hω : ω ∈ E.fsupport
    · rw [indicator_of_mem hω, Pi.one_apply, ENNReal.le_div_iff_mul_le (.inl hω.2) (.inl hω.1),
        one_mul]
      exact le_max_left _ _
    · simp [indicator_of_notMem hω]
  have h_eq : E.fsupport.indicator 1 =ᵐ[Q] fun ω ↦ max (E ω) (F ω) / E ω := by
    refine ae_eq_of_ae_le_of_lintegral_le (.of_forall h_le) (by rwa [lintegral_indicator_one h_fs])
      (hG.measurable.div hE_meas).aemeasurable ?_
    rw [lintegral_indicator_one h_fs]
    exact hE.lintegral_div_le_measure_fsupport hG
  filter_upwards [h_eq] with ω hω
  by_cases h_top : E ω = ∞
  · simp [h_top]
  by_cases h0 : E ω = 0
  · -- off the finite support, `G / E = 0` forces `G = 0`
    have hω' : ω ∉ E.fsupport := fun h ↦ h.2 h0
    rw [indicator_of_notMem hω', eq_comm, h0, ENNReal.div_eq_zero_iff] at hω
    exact (le_max_right _ _).trans (le_of_eq (hω.resolve_right ENNReal.zero_ne_top)) |>.trans
      zero_le
  · -- on the finite support, `G / E = 1` forces `G = E`
    rw [indicator_of_mem (⟨h_top, h0⟩ : ω ∈ E.fsupport), Pi.one_apply, eq_comm,
      ENNReal.div_eq_one_iff h0 h_top] at hω
    exact (le_max_right _ _).trans hω.le

/-- **A numeraire against an alternative that dominates the null is admissible** [EVR26, Note 42,
Theorem 8]. If `E` is a numeraire of `S` against `Q`, with `Q {0 < E < ∞} < ∞` (for instance `Q`
finite), and every member of `S` is absolutely continuous with respect to `Q`, then `E` is an
admissible e-variable for `S`. -/
theorem IsNumeraire.isAdmissibleEVar (hE : IsNumeraire E S Q) (hQ : Q E.fsupport ≠ ∞)
    (hSQ : ∀ P ∈ S, P ≪ Q) : IsAdmissibleEVar E S where
  mem := hE.isEVar
  eventuallyLE _ hF hEF := eventuallyLE_quasiSure_iff.2 fun P hP ↦
    (hSQ P hP).ae_le (hE.ae_le_of_eventuallyLE hQ hF hEF)

/-- **A numeraire need not be admissible** [EVR26, Note 42, Theorem 9 (3), the example]. For the
null of the two Dirac masses on `Bool`, the indicator of `true` is a numeraire against the Dirac
mass at `true`, and it is not admissible: the constant `1` is larger at `false`. So the domination
of the null by the alternative cannot be dropped in `IsNumeraire.isAdmissibleEVar` (Theorem 8 of
the note). -/
theorem exists_isNumeraire_not_isAdmissibleEVar :
    ∃ (S : Set (Measure Bool)) (E : Bool → ℝ≥0∞) (Q : Measure Bool), S.Finite ∧
      (∀ P ∈ S, IsProbabilityMeasure P) ∧ IsProbabilityMeasure Q ∧ IsNumeraire E S Q ∧
      ¬ IsAdmissibleEVar E S := by
  set S : Set (Measure Bool) := {Measure.dirac true, Measure.dirac false}
  set E : Bool → ℝ≥0∞ := ({true} : Set Bool).indicator 1
  have hS : ∀ P ∈ S, P univ ≤ 1 := by rintro P (rfl | rfl) <;> simp
  have h_le : E ≤ 1 := indicator_le_self' fun _ _ ↦ zero_le
  have hE : IsEVar E S := (isEVar_one hS).mono (measurable_one.indicator (by simp)) h_le
  refine ⟨S, E, Measure.dirac true, toFinite _, by rintro P (rfl | rfl) <;> infer_instance,
    inferInstance, ?_, fun h ↦ ?_⟩
  · exact (isNumeraire_one hS (by simp [S])).congr hE ((ae_dirac_iff .of_discrete).2 (by simp [E]))
  · -- the constant `1` dominates `E`, so it is equal to `E` almost surely under `δ false`
    have h1 := ae_of_eventually_quasiSure
      (h.eventuallyLE (isEVar_one hS) (.of_forall h_le)) (P := Measure.dirac false) (by simp [S])
    simpa [E] using (ae_dirac_iff .of_discrete).1 h1

/-! ### Finite nulls -/

/-- **For a finite null, every admissible e-variable is a numeraire against some alternative**
[EVR26, Note 42, Theorem 9 (2)]. If `E` is an admissible e-variable for a finite null `S` of
finite measures, not all zero, then some member `P` of `S` has `∫⁻ E ∂P = 1`, and `E` is a
numeraire of `S` against the probability measure `P.withDensity E`. -/
theorem IsAdmissibleEVar.exists_isNumeraire_withDensity (hS : S.Finite)
    (hSfin : ∀ P ∈ S, IsFiniteMeasure P) (hne : ∃ P ∈ S, P ≠ 0) (hE : IsAdmissibleEVar E S) :
    ∃ P ∈ S, ∫⁻ ω, E ω ∂P = 1 ∧ IsNumeraire E S (P.withDensity E) := by
  obtain ⟨P₀, hP₀, hP₀0⟩ := hne
  obtain ⟨P, hP, -, hPE⟩ :=
    ((isAdmissibleEVar_iff_isStronglyAdmissibleEVar_of_finite hS hSfin).1 hE).exists_lintegral_eq
      univ .univ ⟨P₀, hP₀, by simpa using hP₀0⟩
  exact ⟨P, hP, hPE, isNumeraire_withDensity_of_mem_convexHull hE.mem
    (subset_convexHull _ _ ⟨hP, hPE⟩)⟩

/-- **Every numeraire of a finite null is almost surely equal to an admissible numeraire**
[EVR26, Note 42, Theorem 9 (3)]. If `E` is a numeraire of a finite null `S` of finite measures
against `Q`, with `Q {0 < E < ∞} < ∞` (for instance `Q` finite), then there is an admissible
e-variable `E' ≥ E` that is equal to `E` `Q`-almost surely and is again a numeraire of `S` against
`Q`. -/
theorem IsNumeraire.exists_isAdmissibleEVar_ae_eq (hS : S.Finite)
    (hSfin : ∀ P ∈ S, IsFiniteMeasure P) (hE : IsNumeraire E S Q) (hQ : Q E.fsupport ≠ ∞) :
    ∃ E' : Ω → ℝ≥0∞, IsAdmissibleEVar E' S ∧ E ≤ E' ∧ E' =ᵐ[Q] E ∧ IsNumeraire E' S Q := by
  obtain ⟨E', hE', hEE'⟩ := hE.isEVar.exists_isAdmissibleEVar_le hS hSfin
  have h_eq : E' =ᵐ[Q] E :=
    (hE.ae_le_of_eventuallyLE hQ hE'.mem (.of_forall hEE')).antisymm (.of_forall hEE')
  exact ⟨E', hE', hEE', h_eq, hE.congr hE'.mem h_eq⟩

/-- A finite null of finite measures has a positive constant e-variable: the inverse of the sum
of the masses of its members. -/
private lemma exists_isEVar_const_ne_zero (hS : S.Finite) (hSfin : ∀ P ∈ S, IsFiniteMeasure P) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ IsEVar (fun _ ↦ c) S := by
  refine ⟨(∑ P ∈ hS.toFinset, P univ)⁻¹, ENNReal.inv_ne_zero.2 (ENNReal.sum_ne_top.2
    fun P hP ↦ have := hSfin P (hS.mem_toFinset.1 hP); measure_ne_top P univ),
    measurable_const, fun P hP ↦ ?_⟩
  rw [lintegral_const]
  exact (mul_le_mul_right (Finset.single_le_sum (fun P _ ↦ zero_le)
    (hS.mem_toFinset.2 hP)) _).trans (ENNReal.inv_mul_le_one _)

/-- **The numeraires against the alternatives that dominate a finite null** [EVR26, Note 42,
Theorem 9 (4)]. For a finite null `S` of finite measures, `E` is a numeraire of `S` against some
finite measure with respect to which every member of `S` is absolutely continuous if and only if
`E` is an admissible e-variable that is positive almost surely under every member of `S`. -/
theorem exists_isNumeraire_absolutelyContinuous_iff (hS : S.Finite)
    (hSfin : ∀ P ∈ S, IsFiniteMeasure P) :
    (∃ Q : Measure Ω, IsFiniteMeasure Q ∧ (∀ P ∈ S, P ≪ Q) ∧ IsNumeraire E S Q) ↔
      IsAdmissibleEVar E S ∧ ∀ P ∈ S, ∀ᵐ ω ∂P, E ω ≠ 0 := by
  refine ⟨fun ⟨Q, hQ, hSQ, hE⟩ ↦ ⟨hE.isAdmissibleEVar (measure_ne_top _ _) hSQ, fun P hP ↦ ?_⟩,
    fun ⟨hE, hE0⟩ ↦ ?_⟩
  · obtain ⟨c, hc, hcS⟩ := exists_isEVar_const_ne_zero hS hSfin
    exact (hSQ P hP).ae_le (hE.ae_ne_zero_of_isEVar_const (measure_ne_top _ _) hc hcS)
  -- the alternative is the tilt by `E` of the sum of the members under which `E` is exact
  have h_fin : {P' : Measure Ω | P' ∈ S ∧ ∫⁻ ω, E ω ∂P' = 1}.Finite := hS.subset fun P hP ↦ hP.1
  have : Finite {P' : Measure Ω // P' ∈ S ∧ ∫⁻ ω, E ω ∂P' = 1} := h_fin.to_subtype
  have := Fintype.ofFinite {P' : Measure Ω // P' ∈ S ∧ ∫⁻ ω, E ω ∂P' = 1}
  set ν := Measure.sum fun P' : {P' : Measure Ω // P' ∈ S ∧ ∫⁻ ω, E ω ∂P' = 1} ↦
    (P' : Measure Ω) with hν
  have hSν := (isAdmissibleEVar_iff_forall_absolutelyContinuous_sum hS hSfin hE.mem).1 hE
  have h_int (F : Ω → ℝ≥0∞) : ∫⁻ ω, F ω ∂ν =
      ∑ P' : {P' : Measure Ω // P' ∈ S ∧ ∫⁻ ω, E ω ∂P' = 1}, ∫⁻ ω, F ω ∂(P' : Measure Ω) := by
    rw [hν, lintegral_sum_measure, tsum_fintype]
  have hEν : ∫⁻ ω, E ω ∂ν ≠ ∞ := by
    rw [h_int]
    exact ENNReal.sum_ne_top.2 fun P' _ ↦ by simp [P'.2.2]
  refine ⟨ν.withDensity E, isFiniteMeasure_withDensity hEν, fun P hP ↦ (hSν P hP).trans ?_,
    isNumeraire_withDensity hE.mem hEν fun F hF ↦ ?_⟩
  · refine withDensity_absolutelyContinuous' hE.mem.measurable.aemeasurable ?_
    rw [Measure.ae_sum_iff]
    exact fun P' ↦ hE0 P' P'.2.1
  · rw [h_int, h_int]
    refine Finset.sum_le_sum fun P' _ ↦ ?_
    rw [P'.2.2]
    exact hF.lintegral_le_one P'.2.1

/-! ### An admissible e-variable for the Poisson family that is a numeraire against no
alternative -/

/-- `exp (-2 x) ≤ 1` for `x ≥ 0`. -/
private lemma exp_neg_two_mul_le_one {x : ℝ} (hx : 0 ≤ x) : Real.exp (-(2 * x)) ≤ 1 :=
  Real.exp_le_one_iff.2 (by linarith)

/-- `exp (-2 x) ≤ 2` in `ℝ≥0∞`, for `x ≥ 0`. -/
private lemma ofReal_exp_neg_two_mul_le_two {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal (Real.exp (-(2 * x))) ≤ 2 :=
  (ENNReal.ofReal_le_one.2 (exp_neg_two_mul_le_one hx)).trans one_le_two

/-- `exp (-2 x) = exp (-x) * exp (-x)` in `ℝ≥0∞`. -/
private lemma ofReal_exp_neg_two_mul (x : ℝ) :
    ENNReal.ofReal (Real.exp (-(2 * x))) =
      ENNReal.ofReal (Real.exp (-x)) * ENNReal.ofReal (Real.exp (-x)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  ring_nf

/-- `exp (-n) * (1 / k!) ≤ Po(n) {k}` for an integer `n ≥ 1`: the product form of
`LMLExplore.ofReal_exp_neg_div_factorial_le_poissonMeasure_singleton`. -/
private lemma ofReal_exp_neg_mul_le_poissonMeasure_singleton {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    ENNReal.ofReal (Real.exp (-(n : ℝ))) * ENNReal.ofReal ((k.factorial : ℝ))⁻¹ ≤
      poissonMeasure (n : ℝ≥0) {k} := by
  have h := LMLExplore.ofReal_exp_neg_div_factorial_le_poissonMeasure_singleton
    (r := (n : ℝ≥0)) (by exact_mod_cast hn) k
  rwa [NNReal.coe_natCast, div_eq_mul_inv, ENNReal.ofReal_mul (Real.exp_pos _).le] at h

/-- `(1 - exp (-2 x)) + exp (-2 x) = 1` in `ℝ≥0∞`, for `x ≥ 0`. -/
private lemma ofReal_one_sub_exp_add_ofReal_exp {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal (1 - Real.exp (-(2 * x))) + ENNReal.ofReal (Real.exp (-(2 * x))) = 1 := by
  rw [← ENNReal.ofReal_add (sub_nonneg.2 (exp_neg_two_mul_le_one hx)) (Real.exp_pos _).le]
  simp

/-- The function `2 · 𝟙{k odd}` is `2` at an odd `k`. -/
private lemma indicator_odd_eq_two {k : ℕ} (hk : Odd k) :
    {k : ℕ | Odd k}.indicator (fun _ ↦ (2 : ℝ≥0∞)) k = 2 :=
  indicator_of_mem hk _

/-- Under the Poisson law of parameter `r`, the expectation of `2 · 𝟙{k odd}` is
`1 - exp (-2 r)`. -/
private lemma lintegral_indicator_odd_poissonMeasure (r : ℝ≥0) :
    ∫⁻ k, {k : ℕ | Odd k}.indicator (fun _ ↦ (2 : ℝ≥0∞)) k ∂poissonMeasure r =
      ENNReal.ofReal (1 - Real.exp (-(2 * r))) := by
  rw [lintegral_indicator_const .of_discrete, LMLExplore.poissonMeasure_setOf_odd,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two]
  congr 1
  ring

/-- The function `2 · 𝟙{k odd}` is an e-variable for the null of the Poisson laws. -/
private lemma isEVar_indicator_odd_poissonMeasure :
    IsEVar ({k : ℕ | Odd k}.indicator fun _ ↦ 2) (range poissonMeasure) where
  measurable := .of_discrete
  lintegral_le_one := by
    rintro _ ⟨r, rfl⟩
    rw [lintegral_indicator_odd_poissonMeasure]
    exact ENNReal.ofReal_le_one.2 (by linarith [Real.exp_pos (-(2 * (r : ℝ)))])

/-- Under the Poisson law of parameter `r`, an e-variable `F ≥ 2 · 𝟙{k odd}` for the null of the
Poisson laws exceeds `2 · 𝟙{k odd}` by at most `exp (-2 r)` in mean. -/
private lemma lintegral_sub_indicator_odd_le {F : ℕ → ℝ≥0∞}
    (hF : IsEVar F (range poissonMeasure)) (hEF : {k : ℕ | Odd k}.indicator (fun _ ↦ 2) ≤ F)
    (r : ℝ≥0) :
    ∫⁻ k, F k - {k : ℕ | Odd k}.indicator (fun _ ↦ 2) k ∂poissonMeasure r ≤
      ENNReal.ofReal (Real.exp (-(2 * r))) := by
  have hFr := hF.lintegral_le_one (μ := poissonMeasure r) ⟨r, rfl⟩
  have h_add : ∫⁻ k, F k ∂poissonMeasure r =
      ∫⁻ k, {k : ℕ | Odd k}.indicator (fun _ ↦ (2 : ℝ≥0∞)) k ∂poissonMeasure r +
        ∫⁻ k, F k - {k : ℕ | Odd k}.indicator (fun _ ↦ 2) k ∂poissonMeasure r := by
    rw [← lintegral_add_left (by exact .of_discrete)]
    exact lintegral_congr fun k ↦ (add_tsub_cancel_of_le (hEF k)).symm
  rw [h_add, lintegral_indicator_odd_poissonMeasure,
    ← ofReal_one_sub_exp_add_ofReal_exp r.coe_nonneg] at hFr
  exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).1 hFr

/-- **An admissible e-variable for the Poisson family** [EVR26, Note 42, Theorem 10]. The
function `2 · 𝟙{k odd}` is an admissible e-variable for the null of the Poisson laws on `ℕ`. -/
theorem isAdmissibleEVar_indicator_odd_poissonMeasure :
    IsAdmissibleEVar ({k : ℕ | Odd k}.indicator fun _ ↦ 2) (range poissonMeasure) := by
  set E : ℕ → ℝ≥0∞ := {k : ℕ | Odd k}.indicator fun _ ↦ 2 with hE_def
  refine isAdmissibleEVar_iff_forall_le.2 ⟨isEVar_indicator_odd_poissonMeasure, fun F hF hEF ↦ ?_⟩
  -- an e-variable `F ≥ E` is equal to `E` at every point `k`: under the Poisson law of parameter
  -- `n ≥ 1`, the excess of `F` has mean at most `exp (-2 n)`, and `k` has mass at least
  -- `exp (-n) / k!`
  suffices h : F = E by rw [h]
  funext k
  refine le_antisymm ?_ (hEF k)
  set c : ℝ≥0∞ := ENNReal.ofReal ((k.factorial : ℝ))⁻¹
  have h_bound (n : ℕ) (hn : 1 ≤ n) :
      (F k - E k) * c ≤ ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
    have h_single : (F k - E k) * poissonMeasure (n : ℝ≥0) {k} ≤
        ∫⁻ j, F j - E j ∂poissonMeasure (n : ℝ≥0) := by
      rw [lintegral_countable']
      exact le_tsum (fun a ↦ (F a - E a) * poissonMeasure (n : ℝ≥0) {a}) k
    -- `(F k - E k) * exp (-n) * c ≤ exp (-2 n) = exp (-n) * exp (-n)`; cancel `exp (-n)`
    have h_main : ENNReal.ofReal (Real.exp (-(n : ℝ))) * ((F k - E k) * c) ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ))) * ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
      calc ENNReal.ofReal (Real.exp (-(n : ℝ))) * ((F k - E k) * c)
      _ = (F k - E k) * (ENNReal.ofReal (Real.exp (-(n : ℝ))) * c) := mul_left_comm _ _ _
      _ ≤ (F k - E k) * poissonMeasure (n : ℝ≥0) {k} := by
        gcongr
        exact ofReal_exp_neg_mul_le_poissonMeasure_singleton hn k
      _ ≤ ENNReal.ofReal (Real.exp (-(2 * ((n : ℝ≥0) : ℝ)))) :=
        h_single.trans (lintegral_sub_indicator_odd_le hF hEF n)
      _ = _ := by rw [NNReal.coe_natCast, ofReal_exp_neg_two_mul]
    exact (ENNReal.mul_le_mul_iff_right (by simpa using Real.exp_pos _) ENNReal.ofReal_ne_top).1
      h_main
  have h_lim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (Real.exp (-(n : ℝ)))) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop)
    rwa [ENNReal.ofReal_zero] at h
  have h_zero : (F k - E k) * c = 0 :=
    le_zero_iff.1 (ge_of_tendsto h_lim ((eventually_ge_atTop 1).mono h_bound))
  rcases mul_eq_zero.1 h_zero with h | h
  · exact tsub_eq_zero_iff_le.1 h
  · exact absurd (ENNReal.ofReal_eq_zero.1 h) (not_le.2 (by positivity))

/-- A finite measure on `ℕ` that charges a point `k₀` charges some odd `k₁ > k₀` less than
`k₀`. -/
private lemma exists_odd_gt_measure_singleton_lt (Q : Measure ℕ) [IsFiniteMeasure Q] {k₀ : ℕ}
    (hk₀ : Q {k₀} ≠ 0) : ∃ k₁, Odd k₁ ∧ k₀ < k₁ ∧ Q {k₁} < Q {k₀} := by
  have h_sum : ∑' k, Q {k} ≠ ∞ := by
    have h := lintegral_countable' (μ := Q) (fun _ ↦ (1 : ℝ≥0∞))
    simp only [one_mul, lintegral_const] at h
    rw [← h]
    exact measure_ne_top Q _
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((ENNReal.tendsto_atTop_zero_of_tsum_ne_top h_sum).eventually
    (gt_mem_nhds (pos_iff_ne_zero.2 hk₀)))
  exact ⟨2 * (N + k₀) + 1, ⟨N + k₀, rfl⟩, by omega, hN _ (by omega)⟩

/-- The function `2 · 𝟙{k odd}` with `a` added at `k₀` and subtracted at `k₁`. -/
private noncomputable def oddShift (k₀ k₁ : ℕ) (a : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if k = k₀ then 2 + a else if k = k₁ then 2 - a else {k : ℕ | Odd k}.indicator (fun _ ↦ 2) k

/-- Moving `a ≤ 2` from an odd `k₁` to an odd `k₀ ≠ k₁` in `2 · 𝟙{k odd}` changes the integral
under `μ` by `a μ {k₀} - a μ {k₁}`. -/
private lemma lintegral_oddShift_add {k₀ k₁ : ℕ} (hk₀ : Odd k₀) (hk₁ : Odd k₁) (hk₀₁ : k₀ ≠ k₁)
    {a : ℝ≥0∞} (ha : a ≤ 2) (μ : Measure ℕ) :
    ∫⁻ k, oddShift k₀ k₁ a k ∂μ + a * μ {k₁} =
      ∫⁻ k, {k : ℕ | Odd k}.indicator (fun _ ↦ 2) k ∂μ + a * μ {k₀} := by
  have h_id (k : ℕ) : oddShift k₀ k₁ a k + ({k₁} : Set ℕ).indicator (fun _ ↦ a) k =
      {k : ℕ | Odd k}.indicator (fun _ ↦ 2) k + ({k₀} : Set ℕ).indicator (fun _ ↦ a) k := by
    by_cases h0 : k = k₀
    · simp [oddShift, h0, hk₀₁, indicator_odd_eq_two hk₀]
    · by_cases h1 : k = k₁
      · simp [oddShift, h1, hk₀₁.symm, indicator_odd_eq_two hk₁, tsub_add_cancel_of_le ha]
      · simp [oddShift, h0, h1]
  rw [← lintegral_indicator_const (measurableSet_singleton k₁) a,
    ← lintegral_indicator_const (measurableSet_singleton k₀) a,
    ← lintegral_add_left (by exact .of_discrete), ← lintegral_add_left (by exact .of_discrete)]
  exact lintegral_congr h_id

/-- For odd `k₀ < k₁`, moving `exp (-2 k₁)` from `k₁` to `k₀` in `2 · 𝟙{k odd}` gives an
e-variable for the null of the Poisson laws. -/
private lemma isEVar_oddShift {k₀ k₁ : ℕ} (hk₀ : Odd k₀) (hk₁ : Odd k₁) (hk₀₁ : k₀ < k₁) :
    IsEVar (oddShift k₀ k₁ (ENNReal.ofReal (Real.exp (-(2 * (k₁ : ℝ))))))
      (range poissonMeasure) := by
  set a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(2 * (k₁ : ℝ)))) with ha_def
  refine ⟨.of_discrete, ?_⟩
  rintro _ ⟨r, rfl⟩
  have h := lintegral_oddShift_add hk₀ hk₁ hk₀₁.ne (ofReal_exp_neg_two_mul_le_two k₁.cast_nonneg)
    (poissonMeasure r)
  rw [lintegral_indicator_odd_poissonMeasure] at h
  rcases le_or_gt (k₁ : ℝ) r with hr₁ | hr₁
  · -- for `r ≥ k₁`, the Poisson law charges `k₁` more than `k₀`
    have hp : poissonMeasure r {k₀} ≤ poissonMeasure r {k₁} :=
      LMLExplore.poissonMeasure_singleton_le_of_le hk₀₁.le hr₁
    have h' : ∫⁻ k, oddShift k₀ k₁ a k ∂poissonMeasure r + a * poissonMeasure r {k₁} ≤
        ENNReal.ofReal (1 - Real.exp (-(2 * r))) + a * poissonMeasure r {k₁} := by
      rw [h]
      gcongr
    exact ((ENNReal.add_le_add_iff_right
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))).1 h').trans
      (ENNReal.ofReal_le_one.2 (by linarith [Real.exp_pos (-(2 * (r : ℝ)))]))
  · -- for `r < k₁`, the slack `exp (-2 r)` of `2 · 𝟙{k odd}` is more than `a`
    calc ∫⁻ k, oddShift k₀ k₁ a k ∂poissonMeasure r
    _ ≤ ∫⁻ k, oddShift k₀ k₁ a k ∂poissonMeasure r + a * poissonMeasure r {k₁} := le_self_add
    _ = ENNReal.ofReal (1 - Real.exp (-(2 * r))) + a * poissonMeasure r {k₀} := h
    _ ≤ ENNReal.ofReal (1 - Real.exp (-(2 * r))) + ENNReal.ofReal (Real.exp (-(2 * r))) := by
      gcongr
      calc a * poissonMeasure r {k₀}
      _ ≤ a * 1 := by gcongr; exact prob_le_one
      _ = a := mul_one a
      _ ≤ ENNReal.ofReal (Real.exp (-(2 * r))) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))
    _ = 1 := ofReal_one_sub_exp_add_ofReal_exp r.coe_nonneg

/-- **An admissible e-variable that is a numeraire against no alternative** [EVR26, Note 42,
Theorem 10]. The function `2 · 𝟙{k odd}`, admissible for the null of the Poisson laws
(`isAdmissibleEVar_indicator_odd_poissonMeasure`), is a numeraire of that null against no nonzero
finite measure `Q`. -/
theorem not_isNumeraire_indicator_odd_poissonMeasure (Q : Measure ℕ) [IsFiniteMeasure Q]
    (hQ : Q ≠ 0) :
    ¬ IsNumeraire ({k : ℕ | Odd k}.indicator fun _ ↦ 2) (range poissonMeasure) Q := by
  set E : ℕ → ℝ≥0∞ := {k : ℕ | Odd k}.indicator fun _ ↦ 2 with hE_def
  intro hE
  have hS : ∀ P ∈ range poissonMeasure, P univ ≤ 1 := by rintro _ ⟨r, rfl⟩; simp
  -- `Q` is carried by the odd numbers and charges an odd `k₀`, and an odd `k₁ > k₀` less; moving
  -- a small amount `a` of the value of `E` from `k₁` to `k₀` gives an e-variable `F` whose ratio
  -- to `E` has `Q`-expectation above `Q univ`
  have h_odd : ∀ k, Q {k} ≠ 0 → Odd k := fun k hk ↦ by
    by_contra h
    exact (ae_iff_of_countable.1 (hE.ae_ne_zero hS) k hk) (indicator_of_notMem h _)
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, Q {k₀} ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h_false : ∀ᵐ k ∂Q, False := ae_iff_of_countable.2 fun k hk ↦ hk (hcon k)
    exact hQ (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 h_false))
  obtain ⟨k₁, hk₁_odd, hk₀₁, hQk₁⟩ := exists_odd_gt_measure_singleton_lt Q hk₀
  have hF := isEVar_oddShift (h_odd k₀ hk₀) hk₁_odd hk₀₁
  set a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(2 * (k₁ : ℝ)))) with ha_def
  set F : ℕ → ℝ≥0∞ := oddShift k₀ k₁ a with hF_def
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  -- the ratio of `F` to `E` has too large an integral under `Q`
  have h_num := hE.lintegral_div_le_measure_fsupport hF
  have hE_top : ∀ᵐ k ∂Q, E k ≠ ∞ := .of_forall fun k ↦
    ne_top_of_le_ne_top ENNReal.ofNat_ne_top (indicator_le_self' (fun _ _ ↦ zero_le) k)
  rw [measure_fsupport_eq_measure_univ hE_top (hE.ae_ne_zero hS)] at h_num
  have h_two : ∀ᵐ k ∂Q, E k = 2 :=
    ae_iff_of_countable.2 fun k hk ↦ indicator_odd_eq_two (h_odd k hk)
  have h_div : ∫⁻ k, F k / E k ∂Q = (∫⁻ k, F k ∂Q) / 2 := by
    rw [lintegral_congr_ae (h_two.mono fun k hk ↦ by rw [hk])]
    simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const _ hF.measurable]
  have h := lintegral_oddShift_add (h_odd k₀ hk₀) hk₁_odd hk₀₁.ne
    (ofReal_exp_neg_two_mul_le_two k₁.cast_nonneg) Q
  rw [lintegral_congr_ae h_two, lintegral_const] at h
  have hFQ : ∫⁻ k, F k ∂Q ≤ 2 * Q univ := by
    rwa [h_div, ENNReal.div_le_iff_le_mul (.inl two_ne_zero) (.inl ENNReal.ofNat_ne_top),
      mul_comm] at h_num
  have h_le : 2 * Q univ + a * Q {k₀} ≤ 2 * Q univ + a * Q {k₁} := by
    rw [← h]
    gcongr
  have h_le' := (ENNReal.add_le_add_iff_left
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (measure_ne_top _ _))).1 h_le
  exact absurd ((ENNReal.mul_le_mul_iff_right ha0 ENNReal.ofReal_ne_top).1 h_le') (not_le.2 hQk₁)

end ProbabilityTheory
