/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.Basic
public import LMLExplore.EValues.MultipleTesting.ClosedEBH
public import LMLExplore.EValues.PostHoc
public import Mathlib.Probability.Independence.Integration

/-!
# Closed testing with e-values

Hypotheses are indexed by a finite type `ι`, with nulls `H : ι → Set (Measure Ω)`, and every set
`S` of hypotheses carries a statistic `e S`, an e-variable for the intersection of the nulls of
`S`, or more generally an e-collection (`ProbabilityTheory.IsECollection`). The **e-closed test**
rejects `H i` at level `α` when `e S` reaches `α⁻¹` for every set `S ∋ i`, that is, when the
**adjusted e-value** `adjustedEValue e i = ⨅ S ∋ i, e S` reaches `α⁻¹` [HL25, (1); VW21, §5]. It
is the closed testing procedure of the rejection events `{α⁻¹ ≤ e S}`, and its rejection set is
the largest member of the e-closure of `e` for the family-wise loss. Its key property is that the
adjusted e-values of the true nulls `N` are at most `e N` [HL25, Lemma 2.1].

Adjusted e-values are **family-wise valid** (`ProbabilityTheory.IsFamilyWiseValid`) [VW21, §5]:
under every probability measure `P`, the largest of the adjusted e-values of the true nulls of `P`
has expectation at most one. Family-wise validity gives strong control of the family-wise error
rate [HL25, Proposition 2.2], also at levels chosen after seeing the data [HL25, Theorem 2.3].
Conversely, every family-wise valid family of statistics is the family of adjusted e-values of
an e-collection, `S ↦ ⨆ i ∈ S, E i`: adjusted e-values are all the family-wise valid
families.

For e-processes for the intersection hypotheses in a common filtration, the adjusted e-values
at any stopping time are family-wise valid [HL25, Theorem 2.4], and those at all times control
the family-wise error rate uniformly in time, by Ville's inequality for the e-process of the true
nulls [HL25, Theorem 2.5].

The two algorithms of [VW21, §5] compute the adjusted e-values of the arithmetic means and of the
products of e-values. For statistics that grow when a member of a set is exchanged for one with a
larger value, as the means do, the infimum over the sets containing `i` may be restricted to `i`
together with any set of hypotheses with the smallest values (VW21, Algorithm 1). For products, the
adjusted e-value of `i` is `E i * ∏ j ≠ i, min (E j) 1`, and the products are family-wise valid
when the e-variables of the true nulls are independent, as is the output `(∏ j, min (E j) 1) * E i`
of [VW21, Algorithm 2] [VW21, Theorem 5.1].

Finally, the discovery e-values `discoveryEValue e R j = ⨅ {e S | #(R \ S) ≤ j}` of [VW23, §6]
bound the number of true discoveries in every rejection set `R` simultaneously: with probability
at least `1 - α`, every set `R` with `α⁻¹ ≤ discoveryEValue e R j` contains more than `j` false
nulls. The adjusted e-value of `i` is the discovery e-value of `{i}` at `0`.

## Main definitions

* `ProbabilityTheory.adjustedEValue e i`: the adjusted e-value `⨅ S ∋ i, e S`.
* `ProbabilityTheory.IsFamilyWiseValid E H`: the statistics `E i` are family-wise valid.
* `ProbabilityTheory.discoveryEValue e R j`: the (regularized) discovery e-value of `R` at `j`.

## Main statements

* `ProbabilityTheory.iSup_adjustedEValue_le`: the adjusted e-values of a set `S` are at most
  `e S` [HL25, Lemma 2.1].
* `ProbabilityTheory.mem_eClosure_fwerLoss_iff_forall_le_adjustedEValue`: the members of the
  e-closure for the family-wise loss are the sets of hypotheses rejected by the e-closed test.
* `ProbabilityTheory.isFamilyWiseValid_adjustedEValue`: adjusted e-values are family-wise valid
  [VW21, §5].
* `ProbabilityTheory.isFamilyWiseValid_iff_exists_isECollection`: family-wise valid families are
  exactly the adjusted e-values of e-collections.
* `ProbabilityTheory.isFamilyWiseValid_iff_exists_le`: family-wise validity in the form of
  [VW21, §5], witnessed by one e-variable for each probability measure.
* `ProbabilityTheory.IsFamilyWiseValid.measure_exists_inv_le_le`: strong control of the
  family-wise error rate [HL25, Proposition 2.2].
* `ProbabilityTheory.IsFamilyWiseValid.lintegral_indicator_inv_le_one`,
  `ProbabilityTheory.IsFamilyWiseValid.isPostHocValid`: control at data-dependent levels
  [HL25, Theorem 2.3].
* `ProbabilityTheory.isFamilyWiseValid_adjustedEValue_stoppedValueLimsup`: e-closed tests of
  e-processes at stopping times [HL25, Theorem 2.4].
* `ProbabilityTheory.measure_exists_inv_le_adjustedEValue_le`: uniform control in time
  [HL25, Theorem 2.5].
* `ProbabilityTheory.adjustedEValue_eq_iInf_of_exchange`,
  `ProbabilityTheory.adjustedEValue_meanECollection`: the reduction of [VW21, Algorithm 1].
* `ProbabilityTheory.adjustedEValue_prod`, `ProbabilityTheory.isFamilyWiseValid_prod_min_mul`:
  the adjusted products and [VW21, Algorithm 2, Theorem 5.1].
* `ProbabilityTheory.discoveryEValue_antitone`, `ProbabilityTheory.discoveryEValue_mono`,
  `ProbabilityTheory.discoveryEValue_add_card_sdiff_le`: [VW23, Proposition 6.3].
* `ProbabilityTheory.measure_exists_inv_le_discoveryEValue_le`,
  `ProbabilityTheory.IsECollection.measure_exists_inv_le_discoveryEValue_le`: the true-discovery
  bounds of [VW23, §6].

## References

* [HL25] N. Hartog and L. Lei, *Family-wise error rate control with e-values*,
  arXiv:2501.09015v4.
* [VW21] V. Vovk and R. Wang, *E-values: calibration, combination and applications*, Ann. Statist.
  49 (2021), arXiv:1912.06116v4.
* [VW23] V. Vovk and R. Wang, *Confidence and discoveries with e-values*, Statist. Sci. 38 (2023),
  arXiv:1912.13292v5.
* [XSF+26] Z. Xu, A. Solari, L. Fischer, R. de Heide, A. Ramdas and J. Goeman, *Bringing closure
  to false discovery rate control: a general principle for multiple testing*,
  arXiv:2509.02517v3.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Adjusted e-values -/

section Adjusted

variable {e e' : Finset ι → Ω → ℝ≥0∞} {i : ι} {S : Finset ι} {ω : Ω} {c : ℝ≥0∞}

/-- The **adjusted e-value** of the hypothesis `i` [HL25, (1); VW21, §5]: the smallest statistic
`e S` of a set `S` of hypotheses containing `i`. The e-closed test rejects `i` at level `α` when
the adjusted e-value of `i` reaches `α⁻¹`. -/
noncomputable def adjustedEValue (e : Finset ι → Ω → ℝ≥0∞) (i : ι) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (S : Finset ι) (_ : i ∈ S), e S ω

theorem adjustedEValue_def (e : Finset ι → Ω → ℝ≥0∞) (i : ι) (ω : Ω) :
    adjustedEValue e i ω = ⨅ (S : Finset ι) (_ : i ∈ S), e S ω := (rfl)

theorem adjustedEValue_le (h : i ∈ S) : adjustedEValue e i ω ≤ e S ω :=
  iInf₂_le S h

theorem le_adjustedEValue_iff : c ≤ adjustedEValue e i ω ↔ ∀ S, i ∈ S → c ≤ e S ω :=
  le_iInf₂_iff

/-- The adjusted e-values grow with the statistics. -/
theorem adjustedEValue_mono (h : ∀ S, i ∈ S → e S ω ≤ e' S ω) :
    adjustedEValue e i ω ≤ adjustedEValue e' i ω :=
  le_adjustedEValue_iff.2 fun S hS ↦ (adjustedEValue_le hS).trans (h S hS)

/-- **The adjusted e-values of a set are at most its statistic** [HL25, Lemma 2.1]: for the set
`N` of true nulls, the largest adjusted e-value of a true null is at most `e N`. -/
theorem iSup_adjustedEValue_le (e : Finset ι → Ω → ℝ≥0∞) (S : Finset ι) (ω : Ω) :
    ⨆ i ∈ S, adjustedEValue e i ω ≤ e S ω :=
  iSup₂_le fun _ ↦ adjustedEValue_le

/-- The adjusted e-value of measurable statistics is measurable. Only the statistics of the sets
containing `i` matter. -/
theorem measurable_adjustedEValue [Countable ι] (he : ∀ S, i ∈ S → Measurable (e S)) :
    Measurable (adjustedEValue e i) :=
  Measurable.iInf fun S ↦ Measurable.iInf fun hS ↦ he S hS

/-- The adjusted e-values of the largest values `S ↦ ⨆ j ∈ S, E j` are the values `E i`. -/
@[simp]
theorem adjustedEValue_iSup (E : ι → Ω → ℝ≥0∞) :
    adjustedEValue (fun S ω ↦ ⨆ j ∈ S, E j ω) = E := by
  ext i ω
  refine le_antisymm ?_ (le_adjustedEValue_iff.2 fun _ hS ↦ le_biSup (fun j ↦ E j ω) hS)
  simpa using adjustedEValue_le (e := fun S ω ↦ ⨆ j ∈ S, E j ω) (mem_singleton_self i) (ω := ω)

/-- The e-closed test is closed testing: `i` belongs to the closed testing rejection set of the
events `{c ≤ e S}` exactly when its adjusted e-value is at least `c`. -/
theorem mem_closedTesting_iff_le_adjustedEValue [Fintype ι] :
    i ∈ closedTesting (fun S ↦ {ω | c ≤ e S ω}) ω ↔ c ≤ adjustedEValue e i ω := by
  simp [le_adjustedEValue_iff]

/-- **The e-closed test is an e-closure.** For a level `α ∉ {0, ∞}`, the members of the e-closure
of `e` for the family-wise loss are the sets of hypotheses whose adjusted e-values reach `α⁻¹`. -/
theorem mem_eClosure_fwerLoss_iff_forall_le_adjustedEValue [Finite ι] [DecidableEq ι]
    {α : ℝ≥0∞} {R : Finset ι} (hα₀ : α ≠ 0) (hα : α ≠ ∞) :
    R ∈ eClosure fwerLoss α e ω ↔ ∀ i ∈ R, α⁻¹ ≤ adjustedEValue e i ω := by
  have := Fintype.ofFinite ι
  simp only [mem_eClosure_fwerLoss_iff hα₀ hα, Finset.subset_iff,
    mem_closedTesting_iff_le_adjustedEValue]

end Adjusted

/-! ### Family-wise validity -/

section FamilyWise

variable [Fintype ι] {H : ι → Set (Measure Ω)} {E F : ι → Ω → ℝ≥0∞}
  {e : Finset ι → Ω → ℝ≥0∞} {P : Measure Ω}

/-- The statistic of a true null is at most the largest statistic of a true null. -/
theorem le_iSup_trueNulls (E : ι → Ω → ℝ≥0∞) {i : ι} (hi : i ∈ trueNulls H P) (ω : Ω) :
    E i ω ≤ ⨆ j ∈ trueNulls H P, E j ω :=
  le_biSup (fun j ↦ E j ω) hi

/-- If the statistic of some true null is at least `c`, so is the largest statistic of a true
null. -/
theorem le_iSup_trueNulls_of_exists {c : ℝ≥0∞} {ω : Ω} (h : ∃ i ∈ trueNulls H P, c ≤ E i ω) :
    c ≤ ⨆ i ∈ trueNulls H P, E i ω :=
  let ⟨_, hi, hiω⟩ := h
  hiω.trans (le_iSup_trueNulls E hi ω)

/-- Statistics `E i` are **family-wise valid** for the hypotheses `H` [VW21, §5] when they are
measurable and, under every probability measure `P`, the largest statistic of a true null of `P`
has expectation at most one. Then each `E i` is an e-variable for the probability measures of
`H i`, and the e-values of all
the true nulls are valid jointly: one may reject every `H i` whose `E i` is large. -/
structure IsFamilyWiseValid (E : ι → Ω → ℝ≥0∞) (H : ι → Set (Measure Ω)) : Prop where
  /-- Each statistic is measurable. -/
  measurable (i : ι) : Measurable (E i)
  /-- The largest statistic of a true null has expectation at most one. -/
  lintegral_iSup_le_one (P : Measure Ω) [IsProbabilityMeasure P] :
    ∫⁻ ω, ⨆ i ∈ trueNulls H P, E i ω ∂P ≤ 1

namespace IsFamilyWiseValid

/-- The largest statistic of a true null of `P` is an e-variable for `P`. -/
theorem isEVar_iSup (hE : IsFamilyWiseValid E H) (P : Measure Ω) [IsProbabilityMeasure P] :
    IsEVar (fun ω ↦ ⨆ i ∈ trueNulls H P, E i ω) {P} :=
  ⟨Measurable.biSup _ (Set.toFinite _).countable fun i _ ↦ hE.measurable i,
    fun _ hQ ↦ (Set.mem_singleton_iff.1 hQ) ▸ hE.lintegral_iSup_le_one P⟩

/-- Each statistic of a family-wise valid family is an e-variable for the probability measures of
its hypothesis. -/
theorem isEVar (hE : IsFamilyWiseValid E H) (i : ι) :
    IsEVar (E i) {P | P ∈ H i ∧ IsProbabilityMeasure P} := by
  refine ⟨hE.measurable i, fun P ⟨hP, _⟩ ↦ ?_⟩
  exact (lintegral_mono (le_iSup_trueNulls E (mem_trueNulls.2 hP))).trans
    (hE.lintegral_iSup_le_one P)

/-- Measurable statistics below a family-wise valid family are family-wise valid. -/
theorem of_le (hE : IsFamilyWiseValid E H) (hF : ∀ i, Measurable (F i))
    (hFE : ∀ i ω, F i ω ≤ E i ω) : IsFamilyWiseValid F H where
  measurable := hF
  lintegral_iSup_le_one P _ :=
    (lintegral_mono fun ω ↦ iSup₂_mono fun i _ ↦ hFE i ω).trans (hE.lintegral_iSup_le_one P)

/-- **Strong control of the family-wise error rate** [HL25, Proposition 2.2]: under every
probability measure `P`, the probability that some true null of `P` has a statistic at least
`α⁻¹` is at most `α`. -/
theorem measure_exists_inv_le_le (hE : IsFamilyWiseValid E H) (P : Measure Ω)
    [IsProbabilityMeasure P] (α : ℝ≥0∞) :
    P {ω | ∃ i ∈ trueNulls H P, α⁻¹ ≤ E i ω} ≤ α := by
  exact (measure_mono fun _ ↦ le_iSup_trueNulls_of_exists).trans
    ((hE.isEVar_iSup P).measure_inv_le_le (Set.mem_singleton P) α)

/-- **Control at a data-dependent level** [HL25, Theorem 2.3]: for every level `ℓ ω` chosen after
seeing the data, measurable or not, the indicator that some true null has a statistic at least
`(ℓ ω)⁻¹`, divided by `ℓ ω`, has expectation at most one. -/
theorem lintegral_indicator_inv_le_one (hE : IsFamilyWiseValid E H) (P : Measure Ω)
    [IsProbabilityMeasure P] (ℓ : Ω → ℝ≥0∞) :
    ∫⁻ ω, {ω | ∃ i ∈ trueNulls H P, (ℓ ω)⁻¹ ≤ E i ω}.indicator (fun ω ↦ (ℓ ω)⁻¹) ω ∂P ≤ 1 := by
  refine (lintegral_mono fun ω ↦ ?_).trans (hE.lintegral_iSup_le_one P)
  by_cases hω : ∃ i ∈ trueNulls H P, (ℓ ω)⁻¹ ≤ E i ω
  · rw [Set.indicator_of_mem (by exact hω)]
    exact le_iSup_trueNulls_of_exists hω
  · rw [Set.indicator_of_notMem (by exact hω)]
    exact zero_le

/-- **Post-hoc control of the family-wise error rate** [HL25, Theorem 2.3]: under every
probability measure `P`, the tests that reject when some true null of `P` has a statistic at
least `α⁻¹` are post-hoc valid for `P`. -/
theorem isPostHocValid (hE : IsFamilyWiseValid E H) (P : Measure Ω) [IsProbabilityMeasure P] :
    IsPostHocValid (fun α ↦ {ω | ∃ i ∈ trueNulls H P, α⁻¹ ≤ E i ω}.indicator 1) {P} := by
  refine (hE.isEVar_iSup P).isPostHocValid_indicator.mono fun _ _ ↦ ae_of_all _ fun ω α _ ↦ ?_
  exact Set.indicator_le_indicator_of_subset (fun _ ↦ le_iSup_trueNulls_of_exists)
    (fun _ ↦ zero_le) ω

end IsFamilyWiseValid

/-- Family-wise validity in the form of [VW21, §5]: measurable statistics are family-wise valid
exactly when there is an e-variable `E' P` for each probability measure `P`, a conditional
e-variable in the language of [VW21], above the statistic of every hypothesis that `P` belongs
to. -/
theorem isFamilyWiseValid_iff_exists_le (hE : ∀ i, Measurable (E i)) :
    IsFamilyWiseValid E H ↔
      ∃ E' : Measure Ω → Ω → ℝ≥0∞, (∀ (P : Measure Ω) [IsProbabilityMeasure P], IsEVar (E' P) {P}) ∧
        ∀ i, ∀ P ∈ H i, E i ≤ E' P := by
  refine ⟨fun h ↦ ⟨fun P ω ↦ ⨆ i ∈ trueNulls H P, E i ω, fun P _ ↦ h.isEVar_iSup P,
    fun _ _ hP ↦ le_iSup_trueNulls E (mem_trueNulls.2 hP)⟩,
    fun ⟨E', hE', hle⟩ ↦ ⟨hE, fun P _ ↦ ?_⟩⟩
  refine (lintegral_mono fun ω ↦ iSup₂_le fun i hi ↦ hle i P (mem_trueNulls.1 hi) ω).trans ?_
  exact (hE' P).lintegral_le_one (Set.mem_singleton P)

/-- **Adjusted e-values are family-wise valid** [VW21, §5; HL25, Lemma 2.1]: if `e N` has
expectation at most one under every probability measure whose set `N` of true nulls is nonempty,
as for an e-collection, the adjusted e-values are family-wise valid. Only the statistics of
nonempty sets are used. -/
theorem isFamilyWiseValid_adjustedEValue (he : ∀ S : Finset ι, S.Nonempty → Measurable (e S))
    (hle : ∀ (P : Measure Ω) [IsProbabilityMeasure P], (trueNulls H P).Nonempty →
      ∫⁻ ω, e (trueNulls H P) ω ∂P ≤ 1) :
    IsFamilyWiseValid (adjustedEValue e) H where
  measurable _ := measurable_adjustedEValue fun S hS ↦ he S ⟨_, hS⟩
  lintegral_iSup_le_one P _ := by
    rcases (trueNulls H P).eq_empty_or_nonempty with hN | hN
    · simp [hN]
    exact (lintegral_mono fun ω ↦ iSup_adjustedEValue_le e _ ω).trans (hle P hN)

/-- The adjusted e-values of an e-collection are family-wise valid [VW21, §5]. -/
theorem IsECollection.isFamilyWiseValid_adjustedEValue (he : IsECollection e H) :
    IsFamilyWiseValid (adjustedEValue e) H :=
  ProbabilityTheory.isFamilyWiseValid_adjustedEValue (fun S _ ↦ he.measurable S)
    fun P _ _ ↦ he.lintegral_le_one P

/-- **Adjusted e-values are all the family-wise valid families**: statistics are family-wise
valid exactly when they are the adjusted e-values of some e-collection, which can be taken to be
`S ↦ ⨆ i ∈ S, E i`. -/
theorem isFamilyWiseValid_iff_exists_isECollection :
    IsFamilyWiseValid E H ↔ ∃ e, IsECollection e H ∧ E = adjustedEValue e := by
  refine ⟨fun hE ↦ ⟨fun S ω ↦ ⨆ i ∈ S, E i ω, ⟨fun S ↦ ?_, ?_, hE.lintegral_iSup_le_one⟩,
    (adjustedEValue_iSup E).symm⟩, fun ⟨e, he, hEe⟩ ↦ hEe ▸ he.isFamilyWiseValid_adjustedEValue⟩
  · exact Measurable.biSup _ (Set.toFinite _).countable fun i _ ↦ hE.measurable i
  · ext ω
    simp

/-! ### E-closed tests of e-processes -/

section Sequential

variable {ℱ : Filtration ℕ mΩ} {e : Finset ι → ℕ → Ω → ℝ≥0∞}

/-- An e-process for the intersection of the nulls of the true nulls of `P` is an e-process for
`P`. -/
private lemma isEProcess_singleton_trueNulls
    (he : ∀ S : Finset ι, S.Nonempty → IsEProcess (e S) ℱ (⋂ i ∈ S, H i)) (P : Measure Ω)
    (hN : (trueNulls H P).Nonempty) : IsEProcess (e (trueNulls H P)) ℱ {P} :=
  (he _ hN).anti_set (Set.singleton_subset_iff.2
    (Set.mem_iInter₂.2 fun _ hi ↦ mem_trueNulls.1 hi))

/-- **E-closed tests at stopping times** [HL25, Theorem 2.4]: for e-processes `e S` for the
intersections of the nulls of the nonempty sets `S`, in a common filtration, the adjusted
e-values of their values at a stopping time `τ` are family-wise valid, with the `limsup` of the
processes where `τ` is infinite. In particular they control the family-wise error rate at levels
chosen after seeing the data. -/
theorem isFamilyWiseValid_adjustedEValue_stoppedValueLimsup
    (he : ∀ S : Finset ι, S.Nonempty → IsEProcess (e S) ℱ (⋂ i ∈ S, H i))
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) :
    IsFamilyWiseValid (adjustedEValue fun S ↦ stoppedValueLimsup (e S) τ) H :=
  isFamilyWiseValid_adjustedEValue
    (fun S hS ↦ measurable_stoppedValueLimsup (he S hS).measurable hτ.measurable')
    fun P _ hN ↦ ((isEProcess_singleton_trueNulls he P hN).isEVar_stoppedValueLimsup
      (fun _ hQ ↦ (Set.mem_singleton_iff.1 hQ) ▸ ‹_›) hτ).lintegral_le_one (Set.mem_singleton P)

/-- **Uniform control in time of the family-wise error rate** [HL25, Theorem 2.5]: for
e-processes `e S` for the intersections of the nulls of the nonempty sets `S`, in a common
filtration, the probability that the adjusted e-value of some true null ever reaches `α⁻¹` is at
most `α`, under every probability measure. -/
theorem measure_exists_inv_le_adjustedEValue_le
    (he : ∀ S : Finset ι, S.Nonempty → IsEProcess (e S) ℱ (⋂ i ∈ S, H i)) (P : Measure Ω)
    [IsProbabilityMeasure P] (α : ℝ≥0∞) :
    P {ω | ∃ n, ∃ i ∈ trueNulls H P, α⁻¹ ≤ adjustedEValue (fun S ↦ e S n) i ω} ≤ α := by
  rcases (trueNulls H P).eq_empty_or_nonempty with hN | hN
  · simp [hN]
  -- The adjusted e-values of the true nulls are below the e-process of the true nulls.
  refine (measure_mono fun ω hω ↦ ?_).trans
    ((isEProcess_singleton_trueNulls he P hN).measure_exists_inv_le_le (Set.mem_singleton P) α)
  obtain ⟨n, i, hi, hiω⟩ := hω
  exact ⟨n, hiω.trans (adjustedEValue_le hi)⟩

end Sequential

end FamilyWise

/-! ### The adjustments of arithmetic means and products -/

section Exchange

variable [DecidableEq ι] {β : Type*} [LinearOrder β] {x : ι → β} {k : ι} {ω : Ω}
  {e : Finset ι → Ω → ℝ≥0∞}

/-- **Adjusted e-values of exchangeable statistics** [VW21, §5, Algorithm 1]: for statistics that
grow when an element of a set is exchanged for one with a larger value `x`, as symmetric
statistics nondecreasing in the e-values do, the infimum defining the adjusted e-value of `k` may
be restricted to the sets `insert k T` where `T` is made of hypotheses other than `k` with the
smallest values, whatever the order among ties. The proof exchanges the members of a set one at a
time (`Finset.induction_on_exchange`), as in the proof of
`ProbabilityTheory.mem_eClosure_of_forall_le` [XSF+26, Lemma 52]. -/
theorem adjustedEValue_eq_iInf_of_exchange [Finite ι]
    (he : ∀ S i j, i ∉ S → j ∉ S → x i ≤ x j → e (insert i S) ω ≤ e (insert j S) ω) :
    adjustedEValue e k ω =
      ⨅ (T : Finset ι) (_ : k ∉ T) (_ : ∀ i ∈ T, ∀ j ∉ T, j ≠ k → x i ≤ x j),
        e (insert k T) ω := by
  have := Fintype.ofFinite ι
  refine le_antisymm (le_iInf₂ fun T _ ↦ le_iInf fun _ ↦ adjustedEValue_le (mem_insert_self k T))
    (le_adjustedEValue_iff.2 fun S hS ↦ ?_)
  -- Compare `S = insert k (S.erase k)` with a set of the same size of smallest values.
  obtain ⟨T, hTk, hT, hTx⟩ := exists_subset_card_eq_forall_le (fun i ↦ OrderDual.toDual (x i))
    (card_le_card (erase_subset_erase k (subset_univ S)))
  have hkT : k ∉ T := fun h ↦ notMem_erase k univ (hTk h)
  replace hTx : ∀ i ∈ T, ∀ j ∉ T, j ≠ k → x i ≤ x j := fun i hi j hj hjk ↦
    hTx i hi j (mem_sdiff.2 ⟨mem_erase.2 ⟨hjk, mem_univ j⟩, hj⟩)
  calc ⨅ (T : Finset ι) (_ : k ∉ T) (_ : ∀ i ∈ T, ∀ j ∉ T, j ≠ k → x i ≤ x j), e (insert k T) ω
      ≤ e (insert k T) ω := iInf₂_le_of_le T hkT (iInf_le _ hTx)
    _ ≤ e (insert k (S.erase k)) ω := by
        refine induction_on_exchange (p := fun A ↦ k ∉ A → e (insert k T) ω ≤ e (insert k A) ω)
          (fun _ ↦ le_rfl) (fun A i j _ hi hiT hjT hjA ih hkA ↦ ?_) _ hT.symm (notMem_erase k S)
        have hik : i ≠ k := fun h ↦ hkA (h ▸ hi)
        have hjk : j ≠ k := fun h ↦ hkT (h ▸ hjT)
        calc e (insert k T) ω ≤ e (insert k (insert j (A.erase i))) ω :=
              ih (by simp [hjk.symm, hkA])
          _ = e (insert j (insert k (A.erase i))) ω := by rw [insert_comm]
          _ ≤ e (insert i (insert k (A.erase i))) ω :=
              he _ _ _ (by simp [hjk, hjA]) (by simp [hik]) (hTx j hjT i hiT hik)
          _ = e (insert k A) ω := by rw [insert_comm, insert_erase hi]
    _ = e S ω := by rw [insert_erase hS]

omit [DecidableEq ι] in
/-- **The adjusted arithmetic means** [VW21, §5, Algorithm 1]: the adjusted e-value of `k` for the
mean e-collection is the smallest mean of `E k` and the e-values of a set `T` of hypotheses other
than `k` with the smallest e-values. -/
theorem adjustedEValue_meanECollection [Finite ι] (E : ι → Ω → ℝ≥0∞) (k : ι) (ω : Ω) :
    adjustedEValue (meanECollection E) k ω =
      ⨅ (T : Finset ι) (_ : k ∉ T) (_ : ∀ i ∈ T, ∀ j ∉ T, j ≠ k → E i ω ≤ E j ω),
        (E k ω + ∑ i ∈ T, E i ω) / (#T + 1) := by
  classical
  rw [adjustedEValue_eq_iInf_of_exchange (x := fun i ↦ E i ω)
    fun S i j hi hj hij ↦ meanECollection_insert_le_insert hi hj hij]
  refine iInf_congr fun T ↦ iInf_congr fun hkT ↦ iInf_congr fun _ ↦ ?_
  rw [meanECollection_def, sum_insert hkT, card_insert_of_notMem hkT, Nat.cast_add_one]

end Exchange

section Product

variable [Fintype ι] {H : ι → Set (Measure Ω)} {E : ι → Ω → ℝ≥0∞}

/-- **The adjusted products** [VW21, §5]: the adjusted e-value of `k` for the products
`S ↦ ∏ i ∈ S, E i` is `E k` times the product of the e-values below one of the other
hypotheses. -/
theorem adjustedEValue_prod [DecidableEq ι] (E : ι → Ω → ℝ≥0∞) (k : ι) (ω : Ω) :
    adjustedEValue (fun S ω ↦ ∏ i ∈ S, E i ω) k ω = E k ω * ∏ j ∈ univ.erase k, min (E j ω) 1 := by
  refine le_antisymm ?_ (le_adjustedEValue_iff.2 fun S hS ↦ ?_)
  · -- The infimum is attained at `k` together with the other hypotheses with e-values below one.
    have hk : k ∉ (univ.erase k).filter (fun j ↦ E j ω < 1) := by simp
    refine (adjustedEValue_le (S := insert k ((univ.erase k).filter fun j ↦ E j ω < 1))
      (mem_insert_self k _)).trans_eq ?_
    rw [prod_insert hk, prod_filter]
    congr 1
    refine prod_congr rfl fun j _ ↦ ?_
    split_ifs with h
    · exact (min_eq_left h.le).symm
    · exact (min_eq_right (not_lt.1 h)).symm
  · rw [← mul_prod_erase S _ hS]
    refine mul_le_mul' le_rfl ?_
    calc ∏ j ∈ univ.erase k, min (E j ω) 1 ≤ ∏ j ∈ S.erase k, min (E j ω) 1 :=
          prod_le_prod_of_subset_of_le_one (erase_subset_erase k (subset_univ S))
            fun _ _ _ ↦ min_le_right _ _
      _ ≤ ∏ j ∈ S.erase k, E j ω := prod_le_prod fun _ _ ↦ min_le_left _ _

/-- **Adjusted products are family-wise valid** [VW21, §5, Theorem 5.1]: if each `E i` is an
e-variable for `H i` and, under every probability measure, the e-variables of the true nulls are
independent, the adjusted e-values `E k * ∏ j ≠ k, min (E j) 1` are family-wise valid. -/
theorem isFamilyWiseValid_adjustedEValue_prod (hE : ∀ i, IsEVar (E i) (H i))
    (hind : ∀ (P : Measure Ω) [IsProbabilityMeasure P],
      iIndepFun (fun i : trueNulls H P ↦ E i) P) :
    IsFamilyWiseValid (adjustedEValue fun S ω ↦ ∏ i ∈ S, E i ω) H := by
  refine isFamilyWiseValid_adjustedEValue (fun S _ ↦ measurable_prod S fun i _ ↦ (hE i).measurable)
    fun P _ _ ↦ ?_
  -- The expectation of the product of independent e-variables is the product of expectations.
  calc ∫⁻ ω, ∏ i ∈ trueNulls H P, E i ω ∂P = ∫⁻ ω, ∏ i : trueNulls H P, E i ω ∂P :=
        lintegral_congr fun ω ↦ (prod_coe_sort (trueNulls H P) fun i ↦ E i ω).symm
    _ = ∏ i : trueNulls H P, ∫⁻ ω, E i ω ∂P :=
        lintegral_prod_eq_prod_lintegral_of_indepFun _ _ (hind P) fun i ↦ (hE i).measurable
    _ ≤ 1 := prod_le_one fun i _ ↦ (hE i).lintegral_le_one (mem_trueNulls.1 i.property)

/-- **The output of [VW21, Algorithm 2] is family-wise valid** [VW21, Theorem 5.1]: under the
hypotheses of `isFamilyWiseValid_adjustedEValue_prod`, the e-values `E k` multiplied by the
product `∏ j, min (E j) 1` of all the e-values below one are family-wise valid. They are at most
the adjusted products. -/
theorem isFamilyWiseValid_prod_min_mul (hE : ∀ i, IsEVar (E i) (H i))
    (hind : ∀ (P : Measure Ω) [IsProbabilityMeasure P],
      iIndepFun (fun i : trueNulls H P ↦ E i) P) :
    IsFamilyWiseValid (fun k ω ↦ (∏ j, min (E j ω) 1) * E k ω) H := by
  classical
  refine (isFamilyWiseValid_adjustedEValue_prod hE hind).of_le (fun k ↦
    (measurable_prod (univ : Finset ι) fun j _ ↦ (hE j).measurable.min measurable_const).mul
      (hE k).measurable) fun k ω ↦ ?_
  rw [adjustedEValue_prod, mul_comm]
  exact mul_le_mul' le_rfl
    (prod_le_prod_of_subset_of_le_one (erase_subset k univ) fun _ _ _ ↦ min_le_right _ _)

end Product

/-! ### Discovery e-values -/

section Discovery

variable [DecidableEq ι] {e : Finset ι → Ω → ℝ≥0∞} {R R' S : Finset ι} {j j' : ℕ} {ω : Ω}

/-- The **discovery e-value** of the rejection set `R` at `j` [VW23, §6]: the smallest
statistic `e S` of a set `S` of hypotheses that leaves at most `j` members of `R` outside it.
For an e-collection, with probability at least `1 - α`, every `R` with
`α⁻¹ ≤ discoveryEValue e R j` has more than `j` true discoveries: the set `N` of true nulls has
`j < #(R \ N)` (`IsECollection.measure_exists_inv_le_discoveryEValue_le`). This is the
regularized discovery e-vector `min_{j' ≤ j} D^R(j')` of [VW23]. -/
noncomputable def discoveryEValue (e : Finset ι → Ω → ℝ≥0∞) (R : Finset ι) (j : ℕ) (ω : Ω) :
    ℝ≥0∞ :=
  ⨅ (S : Finset ι) (_ : #(R \ S) ≤ j), e S ω

theorem discoveryEValue_def (e : Finset ι → Ω → ℝ≥0∞) (R : Finset ι) (j : ℕ) (ω : Ω) :
    discoveryEValue e R j ω = ⨅ (S : Finset ι) (_ : #(R \ S) ≤ j), e S ω := (rfl)

theorem discoveryEValue_le (h : #(R \ S) ≤ j) : discoveryEValue e R j ω ≤ e S ω :=
  iInf₂_le S h

theorem le_discoveryEValue_iff {c : ℝ≥0∞} :
    c ≤ discoveryEValue e R j ω ↔ ∀ S, #(R \ S) ≤ j → c ≤ e S ω :=
  le_iInf₂_iff

/-- The discovery e-value of measurable statistics is measurable. Only the statistics of the sets
leaving at most `j` members of `R` outside them matter. -/
theorem measurable_discoveryEValue [Countable ι] (he : ∀ S, #(R \ S) ≤ j → Measurable (e S)) :
    Measurable (discoveryEValue e R j) :=
  Measurable.iInf fun S ↦ Measurable.iInf fun hS ↦ he S hS

/-- The regularized discovery e-value is the smallest of the discovery e-values
`D^R(j') = ⨅ {e S | #(R \ S) = j'}` of [VW23, §6] at the numbers `j' ≤ j`. -/
theorem discoveryEValue_eq_iInf (e : Finset ι → Ω → ℝ≥0∞) (R : Finset ι) (j : ℕ) (ω : Ω) :
    discoveryEValue e R j ω = ⨅ (j' : ℕ) (_ : j' ≤ j) (S : Finset ι) (_ : #(R \ S) = j'), e S ω :=
  le_antisymm (le_iInf₂ fun _ hj' ↦ le_iInf₂ fun _ hS ↦ discoveryEValue_le (hS.trans_le hj'))
    (le_discoveryEValue_iff.2 fun S hS ↦ iInf₂_le_of_le _ hS
      (iInf₂_le (f := fun S' (_ : #(R \ S') = #(R \ S)) ↦ e S' ω) S rfl))

/-- The adjusted e-value of `i` is the discovery e-value of `{i}` at `0`. -/
theorem adjustedEValue_eq_discoveryEValue (e : Finset ι → Ω → ℝ≥0∞) (i : ι) (ω : Ω) :
    adjustedEValue e i ω = discoveryEValue e {i} 0 ω := by
  simp [adjustedEValue_def, discoveryEValue_def, sdiff_eq_empty_iff_subset]

/-- The discovery e-values decrease in `j` [VW23, Proposition 6.3 (1)]. -/
theorem discoveryEValue_antitone (e : Finset ι → Ω → ℝ≥0∞) (R : Finset ι) (ω : Ω) :
    Antitone fun j ↦ discoveryEValue e R j ω :=
  fun _ _ hjj' ↦ le_discoveryEValue_iff.2 fun _ hS ↦ discoveryEValue_le (hS.trans hjj')

/-- The discovery e-values grow with the rejection set [VW23, Proposition 6.3 (2)]. -/
theorem discoveryEValue_mono (h : R ⊆ R') : discoveryEValue e R j ω ≤ discoveryEValue e R' j ω :=
  le_discoveryEValue_iff.2 fun _ hS ↦
    discoveryEValue_le ((card_le_card (sdiff_subset_sdiff h subset_rfl)).trans hS)

/-- Adding members to a rejection set adds at most as many to the bound [VW23,
Proposition 6.3 (3)]. -/
theorem discoveryEValue_add_card_sdiff_le (e : Finset ι → Ω → ℝ≥0∞) (R R' : Finset ι) (j : ℕ)
    (ω : Ω) : discoveryEValue e R' (j + #(R' \ R)) ω ≤ discoveryEValue e R j ω := by
  refine le_discoveryEValue_iff.2 fun S hS ↦ discoveryEValue_le ?_
  calc #(R' \ S) ≤ #(R \ S ∪ R' \ R) := card_le_card fun i hi ↦ by
        simp only [mem_union, mem_sdiff] at hi ⊢
        tauto
    _ ≤ #(R \ S) + #(R' \ R) := card_union_le _ _
    _ ≤ j + #(R' \ R) := by omega

variable [Fintype ι] {H : ι → Set (Measure Ω)} {P : Measure Ω}

/-- The discovery e-values of the pairs `(R, j)` with at most `j` true discoveries in `R` are at
most the statistic of the true nulls; if it has expectation at most one, as for an e-collection,
their supremum is an e-value [VW23, §6]. Only the statistic of the true nulls is used. -/
theorem lintegral_iSup_discoveryEValue_le_one (P : Measure Ω)
    (hle : ∫⁻ ω, e (trueNulls H P) ω ∂P ≤ 1) :
    ∫⁻ ω, ⨆ (R : Finset ι) (j : ℕ) (_ : #(R \ trueNulls H P) ≤ j), discoveryEValue e R j ω ∂P ≤ 1 :=
  (lintegral_mono fun _ ↦ iSup_le fun _ ↦ iSup₂_le fun _ ↦ discoveryEValue_le).trans hle

/-- **True-discovery bounds** [VW23, §6]: under a measure `P` for which the statistic of the true
nulls is measurable with expectation at most one, as for an e-collection, outside an event of
measure at most `α`, every rejection set `R` with discovery e-value at `j` at least `α⁻¹` contains
more than `j` hypotheses that are not true nulls of `P`, simultaneously over all `R` and `j`. Only
the statistic of the true nulls is used. -/
theorem measure_exists_inv_le_discoveryEValue_le (P : Measure Ω)
    (hm : Measurable (e (trueNulls H P))) (hle : ∫⁻ ω, e (trueNulls H P) ω ∂P ≤ 1) (α : ℝ≥0∞) :
    P {ω | ∃ R j, #(R \ trueNulls H P) ≤ j ∧ α⁻¹ ≤ discoveryEValue e R j ω} ≤ α := by
  have hN : IsEVar (e (trueNulls H P)) {P} := ⟨hm, fun _ hQ ↦ (Set.mem_singleton_iff.1 hQ) ▸ hle⟩
  refine (measure_mono fun ω hω ↦ ?_).trans (hN.measure_inv_le_le (Set.mem_singleton P) α)
  obtain ⟨R, j, hRj, hRω⟩ := hω
  exact hRω.trans (discoveryEValue_le hRj)

/-- The true-discovery bounds of an e-collection [VW23, §6], in expectation. -/
theorem IsECollection.lintegral_iSup_discoveryEValue_le_one (he : IsECollection e H)
    (P : Measure Ω) [IsProbabilityMeasure P] :
    ∫⁻ ω, ⨆ (R : Finset ι) (j : ℕ) (_ : #(R \ trueNulls H P) ≤ j), discoveryEValue e R j ω ∂P ≤ 1 :=
  ProbabilityTheory.lintegral_iSup_discoveryEValue_le_one P (he.lintegral_le_one P)

/-- **True-discovery bounds of an e-collection** [VW23, §6]: under every probability measure `P`,
with probability at least `1 - α`, every rejection set `R` with discovery e-value at `j` at least
`α⁻¹` contains more than `j` hypotheses that are not true nulls of `P`, simultaneously over all
`R` and `j`. -/
theorem IsECollection.measure_exists_inv_le_discoveryEValue_le (he : IsECollection e H)
    (P : Measure Ω) [IsProbabilityMeasure P] (α : ℝ≥0∞) :
    P {ω | ∃ R j, #(R \ trueNulls H P) ≤ j ∧ α⁻¹ ≤ discoveryEValue e R j ω} ≤ α :=
  ProbabilityTheory.measure_exists_inv_le_discoveryEValue_le P (he.measurable _)
    (he.lintegral_le_one P) α

end Discovery

end ProbabilityTheory
