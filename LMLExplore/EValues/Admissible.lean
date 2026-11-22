/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EVariable
public import LMLExplore.Order.Filter.CompleteClass
public import Statlib.EValues.Product
public import LMLExplore.MeasureTheory.Measure.Prod
import LMLExplore.Topology.Instances.ENNReal.Lemmas

/-!
# Admissible e-variables

An e-variable for a null `S` is admissible when no e-variable is larger in a way that the null can
see: every e-variable that dominates it quasi-surely is quasi-surely equal to it. This is the
admissibility of `Filter.IsAdmissible` for the quasi-sure filter of the null, among the
e-variables, so that the complete class lemmas of `LMLExplore.Order.Filter.CompleteClass` apply
to it.

The criterion of Ramdas and Wang characterizes admissibility for every null: an e-variable `E` is
admissible exactly when, on every measurable set `A` charged by the null, the deficits
`1 - ∫⁻ E ∂P` are arbitrarily small compared with `P A`, since the infimum of these ratios is the
largest amount that can be added to `E` on `A`. The sufficient condition of strong admissibility,
the necessary condition `⨆ ∫⁻ E ∂P = 1` and the case of a simple null are derived from it. This
file also proves that for a simple null the admissible e-variables are the likelihood ratios, that
for a finite null of finite measures the admissible e-variables are the strongly admissible ones
and every e-variable is at most an admissible one, and that products of strongly admissible
e-variables are strongly admissible for the product null.

Following Statlib, the null is an arbitrary set of measures and e-variables are `ℝ≥0∞`-valued;
exact means `∫⁻ E ∂P = 1`.

## Main definitions

* `ProbabilityTheory.IsAdmissibleEVar E S`: `E` is an admissible e-variable for `S`, that is
  `Filter.IsAdmissible (quasiSure S) {X | IsEVar X S} E`.
* `ProbabilityTheory.IsStronglyAdmissibleEVar E S`: `E` is an e-variable for `S` such that every
  measurable set charged by a member of `S` is charged by a member under which `E` is exact.

## Main statements

* `ProbabilityTheory.isAdmissibleEVar_iff_forall_le`: admissibility can be tested on the
  e-variables that dominate `E` everywhere.
* `ProbabilityTheory.IsAdmissibleEVar.congr`: a measurable function quasi-surely equal to an
  admissible e-variable is an admissible e-variable.
* `ProbabilityTheory.IsEVar.isEVar_add_indicator_iff`: `E + t 𝟙_A` is an e-variable exactly when
  `t ≤ ⨅ {(1 - ∫⁻ E ∂P) / P A | P ∈ S, P A ≠ 0}` [EVR26, Note 46].
* `ProbabilityTheory.isAdmissibleEVar_iff_iInf_div_eq_zero`: **the admissibility criterion**, for
  any null: `E` is admissible exactly when that infimum is zero for every measurable set charged by
  the null [RW, Theorem 2.14; EVR26, Note 46, Theorem 1].
* `ProbabilityTheory.isAdmissibleEVar_iff_liminf_eq_zero`: the criterion in the form of
  [RW, Theorem 2.14], `liminf_{δ ↓ 0} ⨅ {(1 - ∫⁻ E ∂P) / δ | P ∈ S, δ < P A} = 0`, for a null of
  masses at most one.
* `ProbabilityTheory.IsAdmissibleEVar.iSup_lintegral_eq_one`: the necessary condition
  `⨆ {∫⁻ E ∂P | P ∈ S, P A ≠ 0} = 1` [RW, Proposition 2.13].
* `ProbabilityTheory.IsEVar.measure_lt_eq_zero_of_ae_le`: an e-variable that dominates `E`
  almost surely under a member of the null under which `E` is exact is equal to `E` almost surely
  under that member.
* `ProbabilityTheory.IsStronglyAdmissibleEVar.isAdmissibleEVar`: a strongly admissible e-variable
  is admissible [RW, Corollary 2.15 (a)].
* `ProbabilityTheory.IsEVar.isStronglyAdmissibleEVar_of_forall_exists_absolutelyContinuous`: an
  e-variable exact under a member of the null that dominates each member is strongly admissible
  [RW, Corollary 2.15 (b)].
* `ProbabilityTheory.IsExactEVar.isAdmissibleEVar`: so is an exact e-variable.
* `ProbabilityTheory.isAdmissibleEVar_singleton_iff`: for a simple null `{P}` with `P` finite and
  nonzero, admissible and exact coincide.
* `ProbabilityTheory.isExactEVar_singleton_iff_exists_rnDeriv`: the exact e-variables for `{P}`
  are the likelihood ratios `Q.rnDeriv P` of the probability measures `Q ≪ P`.
* `ProbabilityTheory.isAdmissibleEVar_iff_isStronglyAdmissibleEVar_of_finite`,
  `ProbabilityTheory.isAdmissibleEVar_iff_forall_absolutelyContinuous_sum`: for a finite null of
  finite measures, an e-variable is admissible exactly when it is strongly admissible, that is when
  every member is absolutely continuous with respect to the sum of the members under which it is
  exact [RW, Proposition 2.16; EVR26, Note 42, Theorem 9 (1)].
* `ProbabilityTheory.IsEVar.exists_isAdmissibleEVar_le`: for such a null, every e-variable is at
  most an admissible e-variable [EVR26, Note 42, Theorem 9 (3)].
* `ProbabilityTheory.IsStronglyAdmissibleEVar.prod`: the product of two strongly admissible
  e-variables is strongly admissible for the null of the product measures.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6: Definition 2.11, Propositions 2.12 and 2.13,
  Theorem 2.14, Corollary 2.15, Propositions 2.16 and 2.17.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes and Lean
  library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026: Note 42, whose file
  `Results/NumeraireAdmissible.lean` the section on finite nulls adapts, and Note 46, Theorem 1
  (`results/46-admissibility-criterion.md`), the form of the criterion with a ratio.
* [LRR26] M. Larsson, A. Ramdas and J. Ruf, *Testing hypotheses generated by constraints*, Math.
  Oper. Res. (2026), arXiv:2504.02974v5: Lemma 6.2.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {S : Set (Measure Ω)} {T : Set (Measure Ω')} {E F : Ω → ℝ≥0∞} {P : Measure Ω}

/-! ### Admissible e-variables -/

/-- An e-variable `E` for `S` is **admissible** when every e-variable for `S` that is quasi-surely
at least `E` is quasi-surely at most `E` [RW, Definition 2.11]: `E` is admissible among the
e-variables for the quasi-sure order of the null (`Filter.IsAdmissible`), to which the minimal
complete class lemma [LRR26, Lemma 6.2] applies. It is enough to test the e-variables that
dominate `E` everywhere: `isAdmissibleEVar_iff_forall_le`. -/
abbrev IsAdmissibleEVar (E : Ω → ℝ≥0∞) (S : Set (Measure Ω)) : Prop :=
  (quasiSure S).IsAdmissible {X | IsEVar X S} E

/-- An e-variable is admissible exactly when every e-variable that is at least it everywhere is
quasi-surely equal to it: the definition of [RW, Definition 2.11]. -/
theorem isAdmissibleEVar_iff_forall_le :
    IsAdmissibleEVar E S ↔ IsEVar E S ∧ ∀ F, IsEVar F S → E ≤ F → F =ᶠ[quasiSure S] E := by
  refine ⟨fun h ↦ ⟨h.mem, fun F hF hEF ↦ h.eventuallyEq hF (.of_forall hEF)⟩,
    fun ⟨hE, h⟩ ↦ ⟨hE, fun F hF hEF ↦ ?_⟩⟩
  -- the maximum of `E` and `F` is an e-variable, quasi-surely equal to `F`, that dominates `E`
  have h_max : IsEVar (fun ω ↦ max (E ω) (F ω)) S :=
    hF.congr_quasiSure (hE.measurable.max hF.measurable)
      (hEF.mono fun ω hω ↦ (max_eq_right hω).symm)
  filter_upwards [h _ h_max (fun ω ↦ le_max_left _ _)] with ω hω
  exact (le_max_right _ _).trans hω.le

/-- A measurable function quasi-surely equal to an admissible e-variable is an admissible
e-variable: `Filter.IsAdmissible.congr`, with `IsEVar.congr_quasiSure` for the membership. -/
theorem IsAdmissibleEVar.congr (hE : IsAdmissibleEVar E S) (hF : Measurable F)
    (hEF : E =ᶠ[quasiSure S] F) : IsAdmissibleEVar F S :=
  Filter.IsAdmissible.congr hE (hE.mem.congr_quasiSure hF hEF) hEF

/-! ### The criterion of Ramdas and Wang -/

/-- **The largest amount that can be added on a set.** Adding `t` on a measurable set `A` to an
e-variable `E` gives an e-variable exactly when `t` is at most the deficit `1 - ∫⁻ E ∂P` divided
by `P A`, for every member `P` of the null that charges `A` [EVR26, Note 46]. -/
theorem IsEVar.isEVar_add_indicator_iff (hE : IsEVar E S) {A : Set Ω} (hA : MeasurableSet A)
    {t : ℝ≥0∞} :
    IsEVar (fun ω ↦ E ω + A.indicator (fun _ ↦ t) ω) S ↔
      t ≤ ⨅ P ∈ S, ⨅ (_ : P A ≠ 0), (1 - ∫⁻ ω, E ω ∂P) / P A := by
  have h_int (P : Measure Ω) :
      ∫⁻ ω, E ω + A.indicator (fun _ ↦ t) ω ∂P = ∫⁻ ω, E ω ∂P + t * P A := by
    rw [lintegral_add_left hE.measurable, lintegral_indicator_const hA]
  have h_iff (P : Measure Ω) (hP : P ∈ S) (hPA : P A ≠ 0) :
      t ≤ (1 - ∫⁻ ω, E ω ∂P) / P A ↔ ∫⁻ ω, E ω ∂P + t * P A ≤ 1 := by
    have h1 := hE.lintegral_le_one hP
    rw [ENNReal.le_div_iff_mul_le (.inl hPA) (.inr (ENNReal.sub_ne_top ENNReal.one_ne_top)),
      ENNReal.le_sub_iff_add_le_left (ne_top_of_le_ne_top ENNReal.one_ne_top h1) h1]
  simp only [le_iInf_iff]
  refine ⟨fun h P hP hPA ↦ (h_iff P hP hPA).2 (h_int P ▸ h.lintegral_le_one hP),
    fun h ↦ ⟨hE.measurable.add (measurable_const.indicator hA), fun P hP ↦ ?_⟩⟩
  rw [h_int]
  by_cases hPA : P A = 0
  · rw [hPA, mul_zero, add_zero]
    exact hE.lintegral_le_one hP
  · exact (h_iff P hP hPA).1 (h P hP hPA)

/-- **The admissibility criterion** [RW, Theorem 2.14, in the form of EVR26, Note 46,
Theorem 1]. An e-variable `E` for any null `S` is admissible exactly when, for every measurable set
`A` charged by some member of the null, the deficits `1 - ∫⁻ E ∂P` of the members `P` that charge
`A` are arbitrarily small compared with `P A`. The infimum is the largest amount that can be added
to `E` on `A` (`ProbabilityTheory.IsEVar.isEVar_add_indicator_iff`). No domination, finiteness or
mass hypothesis is needed. -/
theorem isAdmissibleEVar_iff_iInf_div_eq_zero :
    IsAdmissibleEVar E S ↔ IsEVar E S ∧ ∀ A, MeasurableSet A → (∃ P ∈ S, P A ≠ 0) →
      ⨅ P ∈ S, ⨅ (_ : P A ≠ 0), (1 - ∫⁻ ω, E ω ∂P) / P A = 0 := by
  refine ⟨fun hE ↦ ⟨hE.mem, fun A hA ⟨P, hP, hPA⟩ ↦ ?_⟩, fun ⟨hE, h⟩ ↦ ?_⟩
  · -- adding the infimum on `A` gives a larger e-variable, which is quasi-surely `E`
    by_contra ht
    have hF := (hE.mem.isEVar_add_indicator_iff hA).2 le_rfl
    refine hPA (measure_eq_zero_iff_ae_notMem.2 ?_)
    filter_upwards [ae_of_eventually_quasiSure
        (hE.eventuallyLE hF (.of_forall fun ω ↦ le_self_add)) hP,
      hE.mem.ae_lt_top hP] with ω hω hω_top hωA
    rw [indicator_of_mem hωA] at hω
    exact ht (le_zero_iff.1 ((ENNReal.add_le_add_iff_left hω_top.ne).1 (by simpa using hω)))
  refine isAdmissibleEVar_iff_forall_le.2 ⟨hE, fun F hF hEF ↦
    eventuallyEq_quasiSure_iff.2 fun P hP ↦ ?_⟩
  -- on each set where `F` exceeds `E` by `n⁻¹`, `E` can be raised by `n⁻¹`: that set is polar
  have h_null (n : ℕ) : P {ω | E ω + (n : ℝ≥0∞)⁻¹ ≤ F ω} = 0 := by
    have hB : MeasurableSet {ω | E ω + (n : ℝ≥0∞)⁻¹ ≤ F ω} :=
      measurableSet_le (hE.measurable.add_const _) hF.measurable
    by_contra hPB
    have hG : IsEVar (fun ω ↦ E ω + {ω | E ω + (n : ℝ≥0∞)⁻¹ ≤ F ω}.indicator
        (fun _ ↦ (n : ℝ≥0∞)⁻¹) ω) S := by
      refine hF.mono (hE.measurable.add (measurable_const.indicator hB)) fun ω ↦ ?_
      by_cases hω : ω ∈ {ω | E ω + (n : ℝ≥0∞)⁻¹ ≤ F ω}
      · simpa [indicator_of_mem hω] using hω
      · simpa [indicator_of_notMem hω] using hEF ω
    have h_le := (hE.isEVar_add_indicator_iff hB).1 hG
    rw [h _ hB ⟨P, hP, hPB⟩] at h_le
    exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n) (le_zero_iff.1 h_le)
  -- and `{E < F}` is their union
  have h_lt : P {ω | E ω < F ω} = 0 := by
    refine measure_mono_null (fun ω (hω : E ω < F ω) ↦ ?_) (measure_iUnion_null h_null)
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (tsub_pos_of_lt hω).ne'
    exact mem_iUnion.2 ⟨n, (add_le_add le_rfl hn.le).trans (add_tsub_cancel_of_le hω.le).le⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h_lt] with ω hω
  exact le_antisymm (not_lt.1 hω) (hEF ω)

/-- **The admissibility criterion of Ramdas and Wang** [RW, Theorem 2.14]. For a null of measures
of mass at most one, an e-variable `E` is admissible exactly when, for every measurable set `A`
charged by some member of the null,
`liminf_{δ ↓ 0} ⨅ {(1 - ∫⁻ E ∂P) / δ | P ∈ S, δ < P A} = 0`. Over a set `A` charged by no member
the infimum is over no measure; [RW] then takes it to be `0`, while here such sets are excluded.
Without a bound on the masses, the criterion fails: for the null `{∞ • δ₀}` the e-variable `0`
is admissible, while for `A = univ` the infimum is `1 / δ`. -/
theorem isAdmissibleEVar_iff_liminf_eq_zero (hS : ∀ P ∈ S, P univ ≤ 1) :
    IsAdmissibleEVar E S ↔ IsEVar E S ∧ ∀ A, MeasurableSet A → (∃ P ∈ S, P A ≠ 0) →
      liminf (fun δ ↦ ⨅ P ∈ S, ⨅ (_ : δ < P A), (1 - ∫⁻ ω, E ω ∂P) / δ) (𝓝[>] 0) = 0 := by
  refine isAdmissibleEVar_iff_iInf_div_eq_zero.trans (and_congr_right fun _ ↦
    forall_congr' fun A ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ ?_)
  exact (ENNReal.liminf_iInf_div_eq_zero_iff (a := fun P ↦ P A)
    fun P hP ↦ (measure_mono (subset_univ A)).trans (hS P hP)).symm

/-- **The necessary condition of Ramdas and Wang** [RW, Proposition 2.13]. For a null of measures
of mass at most one, an admissible e-variable has expectation arbitrarily close to `1` under the
members that charge any given measurable set charged by the null. The bound on the masses is
needed: for the null `{∞ • δ₀}` the e-variable `0` is admissible. -/
theorem IsAdmissibleEVar.iSup_lintegral_eq_one (hS : ∀ P ∈ S, P univ ≤ 1)
    (hE : IsAdmissibleEVar E S) {A : Set Ω} (hA : MeasurableSet A) (hSA : ∃ P ∈ S, P A ≠ 0) :
    ⨆ P ∈ S, ⨆ (_ : P A ≠ 0), ∫⁻ ω, E ω ∂P = 1 := by
  refine le_antisymm (iSup₂_le fun P hP ↦ iSup_le fun _ ↦ hE.mem.lintegral_le_one hP) ?_
  -- the gap to `1` is at most every ratio of the criterion, since the masses are at most one
  have h_gap : 1 - ⨆ P ∈ S, ⨆ (_ : P A ≠ 0), ∫⁻ ω, E ω ∂P ≤
      ⨅ P ∈ S, ⨅ (_ : P A ≠ 0), (1 - ∫⁻ ω, E ω ∂P) / P A := by
    refine le_iInf₂ fun P hP ↦ le_iInf fun hPA ↦ ?_
    calc 1 - ⨆ P ∈ S, ⨆ (_ : P A ≠ 0), ∫⁻ ω, E ω ∂P
    _ ≤ 1 - ∫⁻ ω, E ω ∂P := tsub_le_tsub_left (le_iSup₂_of_le P hP (by rw [iSup_pos hPA])) 1
    _ ≤ (1 - ∫⁻ ω, E ω ∂P) / P A :=
      (ENNReal.le_div_iff_mul_le (.inl hPA) (.inr (ENNReal.sub_ne_top ENNReal.one_ne_top))).2
        (mul_le_of_le_one_right' ((measure_mono (subset_univ A)).trans (hS P hP)))
  rw [(isAdmissibleEVar_iff_iInf_div_eq_zero.1 hE).2 A hA hSA, nonpos_iff_eq_zero,
    tsub_eq_zero_iff_le] at h_gap
  exact h_gap

/-! ### Strongly admissible e-variables -/

/-- An e-variable `E` for `S` is **strongly admissible** when every measurable set charged by some
member of `S` is charged by a member `P` of `S` with `∫⁻ E ∂P = 1`: the sufficient condition for
admissibility of [RW, Corollary 2.15 (a)]. -/
structure IsStronglyAdmissibleEVar (E : Ω → ℝ≥0∞) (S : Set (Measure Ω)) : Prop
    extends IsEVar E S where
  exists_lintegral_eq : ∀ A, MeasurableSet A → (∃ P ∈ S, P A ≠ 0) →
    ∃ P ∈ S, P A ≠ 0 ∧ ∫⁻ ω, E ω ∂P = 1

/-- A measurable function quasi-surely equal to a strongly admissible e-variable is a strongly
admissible e-variable. -/
theorem IsStronglyAdmissibleEVar.congr (hE : IsStronglyAdmissibleEVar E S) (hF : Measurable F)
    (hEF : E =ᶠ[quasiSure S] F) : IsStronglyAdmissibleEVar F S where
  toIsEVar := hE.toIsEVar.congr_quasiSure hF hEF
  exists_lintegral_eq A hA hSA := by
    obtain ⟨P, hP, hPA, hPE⟩ := hE.exists_lintegral_eq A hA hSA
    exact ⟨P, hP, hPA, by rw [← lintegral_congr_ae (ae_of_eventually_quasiSure hEF hP), hPE]⟩

/-- If an e-variable `F` dominates `E` almost surely under a member `P` of the null under which `E`
is exact, `∫⁻ E ∂P = 1`, then `F` is equal to `E` almost surely under `P`: the event `E < F` is
`P`-null. -/
theorem IsEVar.measure_lt_eq_zero_of_ae_le (hF : IsEVar F S) (hP : P ∈ S) (hEF : E ≤ᵐ[P] F)
    (hE : ∫⁻ ω, E ω ∂P = 1) : P {ω | E ω < F ω} = 0 := by
  have h_eq : E =ᵐ[P] F := ae_eq_of_ae_le_of_lintegral_le hEF (by simp [hE])
    hF.measurable.aemeasurable (by rw [hE]; exact hF.lintegral_le_one hP)
  exact measure_mono_null (fun ω hω ↦ (hω : E ω < F ω).ne) h_eq

/-- A strongly admissible e-variable is admissible [RW, Corollary 2.15 (a)], a case of the
criterion `isAdmissibleEVar_iff_iInf_div_eq_zero`. -/
theorem IsStronglyAdmissibleEVar.isAdmissibleEVar (hE : IsStronglyAdmissibleEVar E S) :
    IsAdmissibleEVar E S := by
  refine isAdmissibleEVar_iff_iInf_div_eq_zero.2 ⟨hE.toIsEVar, fun A hA hSA ↦ ?_⟩
  obtain ⟨P, hP, hPA, hPE⟩ := hE.exists_lintegral_eq A hA hSA
  exact le_zero_iff.1 (iInf₂_le_of_le P hP (iInf_le_of_le hPA (by simp [hPE])))

/-- An e-variable that is exact under a member of the null dominating each member is strongly
admissible [RW, Corollary 2.15 (b)]. -/
theorem IsEVar.isStronglyAdmissibleEVar_of_forall_exists_absolutelyContinuous
    (hE : IsEVar E S) (h : ∀ P ∈ S, ∃ P' ∈ S, P ≪ P' ∧ ∫⁻ ω, E ω ∂P' = 1) :
    IsStronglyAdmissibleEVar E S where
  toIsEVar := hE
  exists_lintegral_eq _ _ := fun ⟨P, hP, hPA⟩ ↦
    let ⟨P', hP', hPP', hP'E⟩ := h P hP
    ⟨P', hP', fun h0 ↦ hPA (hPP' h0), hP'E⟩

/-- An exact e-variable is strongly admissible [RW, Corollary 2.15 (c)]. -/
theorem IsExactEVar.isStronglyAdmissibleEVar (hE : IsExactEVar E S) :
    IsStronglyAdmissibleEVar E S :=
  hE.toIsEVar.isStronglyAdmissibleEVar_of_forall_exists_absolutelyContinuous fun P hP ↦
    ⟨P, hP, .rfl, hE.lintegral_eq_one hP⟩

/-- An exact e-variable is admissible. -/
theorem IsExactEVar.isAdmissibleEVar (hE : IsExactEVar E S) : IsAdmissibleEVar E S :=
  hE.isStronglyAdmissibleEVar.isAdmissibleEVar

/-! ### Simple nulls -/

/-- An admissible e-variable for a simple null `{P}`, with `P` finite and nonzero, is exact
[RW, Proposition 2.12]: the case `A = univ` of the criterion
`isAdmissibleEVar_iff_iInf_div_eq_zero`. -/
theorem IsAdmissibleEVar.isExactEVar_singleton [IsFiniteMeasure P] [NeZero P]
    (hE : IsAdmissibleEVar E {P}) : IsExactEVar E {P} where
  toIsEVar := hE.mem
  lintegral_eq_one := by
    simp only [mem_singleton_iff, forall_eq]
    have hP0 : P univ ≠ 0 := by simp [NeZero.ne P]
    have h := (isAdmissibleEVar_iff_iInf_div_eq_zero.1 hE).2 univ .univ ⟨P, rfl, hP0⟩
    rw [iInf_singleton, iInf_pos hP0, ENNReal.div_eq_zero_iff, tsub_eq_zero_iff_le] at h
    exact le_antisymm (hE.mem.lintegral_le_one rfl) (h.resolve_right (measure_ne_top P univ))

/-- For a simple null `{P}` with `P` finite and nonzero, the admissible e-variables are the exact
ones [RW, Proposition 2.12]. -/
theorem isAdmissibleEVar_singleton_iff [IsFiniteMeasure P] [NeZero P] :
    IsAdmissibleEVar E {P} ↔ IsExactEVar E {P} :=
  ⟨fun h ↦ h.isExactEVar_singleton, fun h ↦ h.isAdmissibleEVar⟩

/-- The exact e-variables for a simple null `{P}`, with `P` finite, are the likelihood ratios
`Q.rnDeriv P` of the probability measures `Q ≪ P`, up to `P`-almost sure equality
[RW, Proposition 2.12]. -/
theorem isExactEVar_singleton_iff_exists_rnDeriv [IsFiniteMeasure P] :
    IsExactEVar E {P} ↔
      Measurable E ∧ ∃ Q : Measure Ω, Q ≪ P ∧ Q univ = 1 ∧ E =ᵐ[P] Q.rnDeriv P := by
  refine ⟨fun hE ↦ ⟨hE.measurable, P.withDensity E, withDensity_absolutelyContinuous P E, ?_,
    (Measure.rnDeriv_withDensity P hE.measurable).symm⟩, fun ⟨hE, Q, hQP, hQ, hEQ⟩ ↦ ?_⟩
  · rw [withDensity_apply _ .univ, Measure.restrict_univ]
    exact hE.lintegral_eq_one rfl
  · have : IsProbabilityMeasure Q := ⟨hQ⟩
    refine (isExactEVar_rnDeriv hQP).congr hE ?_
    rw [quasiSure_singleton]
    exact hEQ.symm

/-! ### Finite nulls -/

/-- **Raising an e-variable on a set that no exact member charges.** Let `E` be an e-variable
for a finite null `S` of finite measures, and `A` a measurable set charged by a member of `S` and
by no member under which `E` is exact. Then for some `ε ≠ 0`, `E + ε 𝟙_A` is an e-variable, and
it is exact under a member of `S` that charges `A`. -/
private lemma exists_isEVar_add_indicator (hS : S.Finite) (hSfin : ∀ P ∈ S, IsFiniteMeasure P)
    (hE : IsEVar E S) {A : Set Ω} (hA : MeasurableSet A) (hA₀ : ∃ P ∈ S, P A ≠ 0)
    (hAE : ∀ P ∈ S, P A ≠ 0 → ∫⁻ ω, E ω ∂P ≠ 1) :
    ∃ ε : ℝ≥0∞, ε ≠ 0 ∧ IsEVar (fun ω ↦ E ω + A.indicator (fun _ ↦ ε) ω) S ∧
      ∃ P ∈ S, P A ≠ 0 ∧ ∫⁻ ω, E ω + A.indicator (fun _ ↦ ε) ω ∂P = 1 := by
  -- the largest constant: the smallest ratio of the slack to the mass of `A`
  obtain ⟨P₁, ⟨hP₁, hP₁A⟩, hmin⟩ := exists_min_image {P | P ∈ S ∧ P A ≠ 0}
    (fun P ↦ (1 - ∫⁻ ω, E ω ∂P) / P A) (hS.subset fun P hP ↦ hP.1) (hA₀.imp fun P hP ↦ hP)
  have := hSfin P₁ hP₁
  refine ⟨(1 - ∫⁻ ω, E ω ∂P₁) / P₁ A, ?_, (hE.isEVar_add_indicator_iff hA).2
    (le_iInf₂ fun P hP ↦ le_iInf fun hPA ↦ hmin P ⟨hP, hPA⟩), P₁, hP₁, hP₁A, ?_⟩
  · refine (ENNReal.div_pos (tsub_pos_of_lt ?_).ne' (measure_ne_top P₁ A)).ne'
    exact lt_of_le_of_ne (hE.lintegral_le_one hP₁) (hAE P₁ hP₁ hP₁A)
  · rw [lintegral_add_left hE.measurable, lintegral_indicator_const hA,
      ENNReal.div_mul_cancel hP₁A (measure_ne_top P₁ A),
      add_tsub_cancel_of_le (hE.lintegral_le_one hP₁)]

/-- **Admissible e-variables for a finite null** [RW, Proposition 2.16; EVR26, Note 42,
Theorem 9 (1)]. For a finite null of finite measures, an e-variable is admissible if and only if
it is strongly admissible: every measurable set charged by a member of the null is charged by a
member under which the e-variable is exact. -/
theorem isAdmissibleEVar_iff_isStronglyAdmissibleEVar_of_finite (hS : S.Finite)
    (hSfin : ∀ P ∈ S, IsFiniteMeasure P) :
    IsAdmissibleEVar E S ↔ IsStronglyAdmissibleEVar E S := by
  refine ⟨fun hE ↦ ⟨hE.mem, fun A hA hA₀ ↦ ?_⟩, fun hE ↦ hE.isAdmissibleEVar⟩
  by_contra hcon
  push Not at hcon
  -- otherwise `E + ε 𝟙_A` is a larger e-variable, on a set that a member charges
  obtain ⟨ε, hε, hF, -⟩ := exists_isEVar_add_indicator hS hSfin hE.mem hA hA₀ hcon
  obtain ⟨P, hP, hPA⟩ := hA₀
  refine hPA (measure_eq_zero_iff_ae_notMem.2 ?_)
  filter_upwards [ae_of_eventually_quasiSure
      (hE.eventuallyLE hF (.of_forall fun ω ↦ le_self_add)) hP,
    hE.mem.ae_lt_top hP] with ω hω hω_top hωA
  rw [indicator_of_mem hωA] at hω
  exact hε (le_zero_iff.1 ((ENNReal.add_le_add_iff_left hω_top.ne).1 (by simpa using hω)))

/-- Every member of the null is absolutely continuous with respect to the sum of the members
under which `E` is exact if and only if every measurable set charged by a member of the null is
charged by a member under which `E` is exact. -/
private lemma forall_absolutelyContinuous_sum_iff :
    (∀ P ∈ S, P ≪ Measure.sum
      fun P' : {P' : Measure Ω // P' ∈ S ∧ ∫⁻ ω, E ω ∂P' = 1} ↦ (P' : Measure Ω)) ↔
      ∀ A, MeasurableSet A → (∃ P ∈ S, P A ≠ 0) → ∃ P ∈ S, P A ≠ 0 ∧ ∫⁻ ω, E ω ∂P = 1 := by
  refine ⟨fun h A hA ⟨P, hP, hPA⟩ ↦ ?_, fun h P hP ↦ .mk fun A hA hA0 ↦ ?_⟩
  · have h0 : Measure.sum (fun P' : {P' : Measure Ω // P' ∈ S ∧ ∫⁻ ω, E ω ∂P' = 1} ↦
        (P' : Measure Ω)) A ≠ 0 := fun h0 ↦ hPA (h P hP h0)
    rw [Ne, Measure.sum_apply_eq_zero' hA, not_forall] at h0
    obtain ⟨P', hP'⟩ := h0
    exact ⟨P', P'.2.1, hP', P'.2.2⟩
  · by_contra hPA
    obtain ⟨P', hP', hP'A, hP'E⟩ := h A hA ⟨P, hP, hPA⟩
    exact hP'A (le_antisymm ((Measure.le_sum _ (⟨P', hP', hP'E⟩ :
      {P' : Measure Ω // P' ∈ S ∧ ∫⁻ ω, E ω ∂P' = 1}) A).trans hA0.le) zero_le)

/-- **Admissible e-variables for a finite null** [RW, Proposition 2.16; EVR26, Note 42,
Theorem 9 (1)]. For a finite null `S` of finite measures, an e-variable `E` is admissible if and
only if every member of `S` is absolutely continuous with respect to the sum of the members `P` of
`S` under which `E` is exact, `∫⁻ E ∂P = 1`. -/
theorem isAdmissibleEVar_iff_forall_absolutelyContinuous_sum (hS : S.Finite)
    (hSfin : ∀ P ∈ S, IsFiniteMeasure P) (hE : IsEVar E S) :
    IsAdmissibleEVar E S ↔ ∀ P ∈ S, P ≪ Measure.sum
      fun P' : {P' : Measure Ω // P' ∈ S ∧ ∫⁻ ω, E ω ∂P' = 1} ↦ (P' : Measure Ω) := by
  rw [isAdmissibleEVar_iff_isStronglyAdmissibleEVar_of_finite hS hSfin,
    forall_absolutelyContinuous_sum_iff]
  exact ⟨fun h ↦ h.exists_lintegral_eq, fun h ↦ ⟨hE, h⟩⟩

/-- **Every e-variable for a finite null is dominated by an admissible e-variable.** For a
finite null of finite measures, every e-variable is at most an admissible e-variable. -/
theorem IsEVar.exists_isAdmissibleEVar_le (hS : S.Finite) (hSfin : ∀ P ∈ S, IsFiniteMeasure P)
    (hE : IsEVar E S) : ∃ E' : Ω → ℝ≥0∞, IsAdmissibleEVar E' S ∧ E ≤ E' := by
  -- raise the e-variable on sets that no exact member charges until it is strongly admissible, by
  -- induction on the number of members under which it is not exact
  suffices h : ∀ n : ℕ, ∀ E : Ω → ℝ≥0∞, IsEVar E S →
      {P | P ∈ S ∧ ∫⁻ ω, E ω ∂P ≠ 1}.ncard ≤ n →
      ∃ E' : Ω → ℝ≥0∞, IsAdmissibleEVar E' S ∧ E ≤ E' from h _ E hE le_rfl
  have h_fin (E : Ω → ℝ≥0∞) : {P | P ∈ S ∧ ∫⁻ ω, E ω ∂P ≠ 1}.Finite :=
    hS.subset fun P hP ↦ hP.1
  intro n
  induction n with
  | zero =>
    intro E hE hn
    have h_empty := (ncard_eq_zero (h_fin E)).1 (Nat.le_zero.1 hn)
    refine ⟨E, IsExactEVar.isAdmissibleEVar ⟨hE, fun P hP ↦ ?_⟩, le_rfl⟩
    by_contra hPE
    exact notMem_empty P (h_empty ▸ (⟨hP, hPE⟩ : P ∈ {P | P ∈ S ∧ ∫⁻ ω, E ω ∂P ≠ 1}))
  | succ n ih =>
    intro E hE hn
    by_cases hadm : IsStronglyAdmissibleEVar E S
    · exact ⟨E, hadm.isAdmissibleEVar, le_rfl⟩
    obtain ⟨A, hA, hA₀, hAE⟩ : ∃ A, MeasurableSet A ∧ (∃ P ∈ S, P A ≠ 0) ∧
        ∀ P ∈ S, P A ≠ 0 → ∫⁻ ω, E ω ∂P ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hadm ⟨hE, fun A hA hA₀ ↦ hcon A hA hA₀⟩
    obtain ⟨ε, -, hF, P₁, hP₁, hP₁A, hP₁F⟩ := exists_isEVar_add_indicator hS hSfin hE hA hA₀ hAE
    -- the new e-variable is exact under one more member
    have h_ssub : {P | P ∈ S ∧ ∫⁻ ω, E ω + A.indicator (fun _ ↦ ε) ω ∂P ≠ 1} ⊂
        {P | P ∈ S ∧ ∫⁻ ω, E ω ∂P ≠ 1} := by
      refine ⟨fun P ⟨hP, hPF⟩ ↦ ⟨hP, fun hPE ↦ hPF ?_⟩,
        fun h_sub ↦ (h_sub ⟨hP₁, hAE P₁ hP₁ hP₁A⟩).2 hP₁F⟩
      have hPA : P A = 0 := by_contra fun hPA ↦ hAE P hP hPA hPE
      rw [lintegral_add_left hE.measurable, lintegral_indicator_const hA, hPA, mul_zero, add_zero,
        hPE]
    have h_lt := ncard_lt_ncard h_ssub (h_fin E)
    obtain ⟨E', hE', hFE'⟩ := ih _ hF (by omega)
    exact ⟨E', hE', fun ω ↦ le_self_add.trans (hFE' ω)⟩

/-! ### Products -/

/-- The product of two strongly admissible e-variables, for nulls of finite measures, is strongly
admissible for the null of the product measures [RW, Proposition 2.17]. -/
theorem IsStronglyAdmissibleEVar.prod {F : Ω' → ℝ≥0∞} (hE : IsStronglyAdmissibleEVar E S)
    (hF : IsStronglyAdmissibleEVar F T) (hS : ∀ P ∈ S, IsFiniteMeasure P)
    (hT : ∀ P ∈ T, IsFiniteMeasure P) :
    IsStronglyAdmissibleEVar (fun p : Ω × Ω' ↦ E p.1 * F p.2) (image2 Measure.prod S T) where
  toIsEVar := hE.toIsEVar.prod hF.toIsEVar
  exists_lintegral_eq A hA := by
    rintro ⟨_, ⟨P, hP, P', hP', rfl⟩, hPA⟩
    have := hS P hP
    have := hT P' hP'
    -- replace the first factor by a member of `S` under which `E` is exact
    have hB := measurable_measure_prodMk_left (ν := P') hA
    obtain ⟨P₁, hP₁, hP₁B, hP₁E⟩ := hE.exists_lintegral_eq _ (measurableSet_support hB)
      ⟨P, hP, (Measure.prod_apply_ne_zero_iff hA).1 hPA⟩
    have := hS P₁ hP₁
    have hP₁A : (P₁.prod P') A ≠ 0 := (Measure.prod_apply_ne_zero_iff hA).2 hP₁B
    -- then the second factor by a member of `T` under which `F` is exact
    have hC := measurable_measure_prodMk_right (μ := P₁) hA
    obtain ⟨P₂, hP₂, hP₂C, hP₂F⟩ := hF.exists_lintegral_eq _ (measurableSet_support hC)
      ⟨P', hP', (Measure.prod_apply_ne_zero_iff_symm hA).1 hP₁A⟩
    have := hT P₂ hP₂
    refine ⟨P₁.prod P₂, ⟨P₁, hP₁, P₂, hP₂, rfl⟩, ?_, ?_⟩
    · exact (Measure.prod_apply_ne_zero_iff_symm hA).2 hP₂C
    · rw [lintegral_prod_mul hE.measurable.aemeasurable hF.measurable.aemeasurable, hP₁E, hP₂F,
        mul_one]

end ProbabilityTheory
