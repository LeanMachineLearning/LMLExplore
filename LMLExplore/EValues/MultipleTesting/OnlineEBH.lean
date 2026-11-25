/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.MultipleTesting.ClosedEBH
public import LMLExplore.EValues.MultipleTesting.DynamicEClosure

/-!
# Online e-BH, e-LOND and stopped e-BH

This file derives the online and stopped e-BH procedures from the dynamic e-closure principle
(`ProbabilityTheory.controlsSupLoss_dynamicEClosure`,
`ProbabilityTheory.controlsStoppedLoss_dynamicEClosure`). Hypotheses are indexed by a type `ι`, with
nulls `H : ι → Set (Measure Ω)`, and `I t : Finset ι` is the nondecreasing set of the hypotheses
that have arrived at time `t`.

**Fixed evidence.** An e-collection `e : Finset ι → Ω → ℝ≥0∞`, with `e S` an e-variable for the
intersection null of `S`, gives the dynamic collection `ProbabilityTheory.arrivedECollection e I`,
whose evidence for `S` at time `t` is `e (S ∩ I t)`. When `e` is increasing along arrivals
(`e (S ∩ I t) ≤ e S`) it is a coherent and time-monotone dynamic intersection e-process
collection for every filtration to which it is adapted, and its dynamic e-closure at time `t` is
the family of the sets `R ⊆ I t` with `f S R ≤ α * e S` for every nonempty `S ⊆ I t`. This gives
the **online SupFDR e-closure principle** [XFR26, Theorem 1; dH26, Remark 3.8]: these families
are nested and control the supremum loss
(`ProbabilityTheory.controlsSupLoss_dynamicEClosure_arrivedECollection`). No adaptedness is needed
for the supremum loss, since it does not involve a filtration.

**Online e-BH and e-LOND.** For e-variables `E i` for the hypotheses and weights `γ i` with
`∑' i, γ i ≤ 1`, the weighted e-collection `S ↦ ∑ i ∈ S, γ i * E i` is increasing. A set `R` is
self-consistent for the weights (`ProbabilityTheory.IsWeightedSelfConsistent`) when
`1 ≤ α * γ i * #R * E i` for every `i ∈ R`; such a set belongs to the dynamic e-closure, so the
self-consistent sets control the supremum over time of the false discovery proportion under
arbitrary dependence [FXR26, Proposition 2.1]. The online e-BH procedure rejects at time `t` the
largest self-consistent subset of `I t` (`ProbabilityTheory.weightedEBH`); it never retracts a
rejection, it is e-BH for the weights `1 / K` on `K` hypotheses, and it controls the SupFDR
[FXR26, Theorem 2.2]. The e-LOND procedure (`ProbabilityTheory.eLOND`) tests the `t`-th hypothesis
at the level `α * γ t * (#R + 1)` given its earlier rejections `R`; its rejection sets are
self-consistent, so online e-BH contains them and e-LOND controls the SupFDR [FXR26, §2.2,
Proposition 2.3; XR24, Theorem 1].

**Stopped e-BH.** With all hypotheses present from the start and e-processes `M i` for the
hypotheses in a common filtration, the means `S ↦ ∑ i ∈ S, M i t / #S` form a dynamic intersection
e-process collection. Its dynamic e-closure is the closed e-BH family at each time, so the closed
e-BH sets and the e-BH set of the values of the e-processes at a stopping time control the false
discovery rate [WDR25, Theorem 2.4, and its remark on closed e-BH].

## Main definitions

* `ProbabilityTheory.arrivedECollection e I`: the dynamic collection of a fixed e-collection.
* `ProbabilityTheory.weightedECollection γ E`: the weighted e-collection `S ↦ ∑ i ∈ S, γ i * E i`.
* `ProbabilityTheory.IsWeightedSelfConsistent γ e α R`: weighted self-consistency.
* `ProbabilityTheory.weightedEBH γ e α J`: the weighted e-BH procedure on the finite set `J`; online
  e-BH at time `t` is `weightedEBH γ e α (I t)`.
* `ProbabilityTheory.eLOND γ e α t`: the rejection set of e-LOND at time `t`.

## Main statements

* `ProbabilityTheory.controlsSupLoss_dynamicEClosure_arrivedECollection`,
  `ProbabilityTheory.monotone_dynamicEClosure_arrivedECollection`: the online SupFDR e-closure
  principle [XFR26, Theorem 1].
* `ProbabilityTheory.controlsSupLoss_isWeightedSelfConsistent`: SupFDR control by the weighted
  self-consistent sets [FXR26, Proposition 2.1].
* `ProbabilityTheory.isGreatest_weightedEBH`, `ProbabilityTheory.weightedEBH_mono`,
  `ProbabilityTheory.eBH_eq_weightedEBH`: online e-BH is the largest self-consistent set, is
  nested in time, and generalizes e-BH [FXR26, §2].
* `ProbabilityTheory.controlsSupLoss_weightedEBH`,
  `ProbabilityTheory.lintegral_iSup_fdp_weightedEBH_le`: online e-BH controls the SupFDR
  [FXR26, Theorem 2.2].
* `ProbabilityTheory.eLOND_subset_weightedEBH`, `ProbabilityTheory.controlsSupLoss_eLOND`,
  `ProbabilityTheory.lintegral_iSup_fdp_eLOND_le`: online e-BH uniformly improves e-LOND, which
  controls the SupFDR [FXR26, §2.2, Proposition 2.3; XR24, Theorem 1].
* `ProbabilityTheory.controlsStoppedLoss_isMeanConsistent`,
  `ProbabilityTheory.controlsStoppedLoss_eBH`,
  `ProbabilityTheory.lintegral_fdp_eBH_stoppedValue_le`: stopped closed e-BH and stopped e-BH
  control the false discovery rate at stopping times [WDR25, Theorem 2.4].

## References

* [dH26] R. de Heide, *Dynamic e-closure for online hypotheses with any-time-valid evidence:
  closure principles and projective mergers*, arXiv:2608.09927v1.
* [FXR26] L. Fischer, Z. Xu and A. Ramdas, *An online generalization of the (e-)Benjamini–Hochberg
  procedure*, arXiv:2407.20683v5.
* [WDR25] H. Wang, S. Dandapanthula and A. Ramdas, *Anytime-valid FDR control with the stopped
  e-BH procedure*, arXiv:2502.08539.
* [XFR26] Z. Xu, L. Fischer and A. Ramdas, *Improving online FDR procedures via online analogs of
  e-closure and compound e-values*, arXiv:2603.24792v3.
* [XR24] Z. Xu and A. Ramdas, *Online multiple testing with e-values*, AISTATS 2024,
  arXiv:2311.06412.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {H : ι → Set (Measure Ω)}
  {I : ℕ → Finset ι} {t : ℕ}

/-! ### Fixed evidence and the online e-closure principle -/

section Arrived

variable [DecidableEq ι] {e : Finset ι → Ω → ℝ≥0∞} {f : Finset ι → Finset ι → ℝ≥0∞} {α : ℝ≥0∞}
  {S R : Finset ι} {ω : Ω}

/-- The **dynamic collection of a fixed e-collection** `e`: at time `t`, the evidence of a set `S`
of hypotheses is the value `e (S ∩ I t)` of the collection at the hypotheses of `S` that have
arrived. The evidence of `S` no longer changes once all of `S` has arrived. -/
def arrivedECollection (e : Finset ι → Ω → ℝ≥0∞) (I : ℕ → Finset ι) (S : Finset ι) (t : ℕ) :
    Ω → ℝ≥0∞ :=
  e (S ∩ I t)

theorem arrivedECollection_def (e : Finset ι → Ω → ℝ≥0∞) (I : ℕ → Finset ι) (S : Finset ι)
    (t : ℕ) : arrivedECollection e I S t = e (S ∩ I t) := (rfl)

/-- The evidence of a set that has fully arrived is its value under the e-collection. -/
theorem arrivedECollection_of_subset (h : S ⊆ I t) : arrivedECollection e I S t = e S := by
  rw [arrivedECollection_def, inter_eq_left.2 h]

/-- For an e-collection increasing along arrivals, the evidence of a set is nondecreasing in time.
-/
theorem monotone_arrivedECollection (hI : Monotone I) (hinc : ∀ S t, e (S ∩ I t) ≤ e S)
    (S : Finset ι) : Monotone (arrivedECollection e I S) := by
  intro t u htu
  have h : S ∩ I u ∩ I t = S ∩ I t := by rw [inter_assoc, inter_eq_right.2 (hI htu)]
  calc arrivedECollection e I S t = e (S ∩ I u ∩ I t) := by rw [arrivedECollection_def, h]
    _ ≤ arrivedECollection e I S u := hinc _ t

/-- The dynamic collection of a fixed e-collection is coherent, with equality. -/
theorem isFutureCoherent_arrivedECollection : IsFutureCoherent (arrivedECollection e I) I where
  le S t _ := by simp only [arrivedECollection_def, inter_assoc, inter_self, le_refl]

/-- **Fixed evidence is a dynamic intersection e-process collection**: for an e-collection
increasing along arrivals, whose value at a nonempty set is an e-variable for the intersection null
of the set, and whose value at every set is measurable at every time at which the set has arrived,
the evidence of the arrived hypotheses of a nonempty set is an e-process for its intersection null.
-/
theorem isDynamicECollection_arrivedECollection
    (he : ∀ S, S.Nonempty → IsEVar (e S) {P | IsProbabilityMeasure P ∧ ∀ i ∈ S, P ∈ H i})
    (hmeas : ∀ t, ∀ S ⊆ I t, Measurable[ℱ t] (e S)) (hinc : ∀ S t, e (S ∩ I t) ≤ e S) :
    IsDynamicECollection (arrivedECollection e I) H ℱ where
  isEProcess S hS := by
    refine .of_lintegral_le_one (fun t ↦ ?_) fun τ _ _ _ P hP ↦ ?_
    · rw [arrivedECollection_def]
      exact hmeas t _ inter_subset_right
    · refine (lintegral_mono fun ω ↦ ?_).trans ((he S hS).lintegral_le_one hP)
      simp only [stoppedValue, arrivedECollection_def]
      exact hinc S _ ω

/-- **The dynamic e-closure of fixed evidence** at time `t`: the sets `R` of arrived hypotheses
with `f S R ≤ α * e S ω` for every nonempty set `S` of arrived hypotheses [XFR26, §2.1]. -/
theorem mem_dynamicEClosure_arrivedECollection :
    R ∈ dynamicEClosure f α (arrivedECollection e I) I t ω ↔
      R ⊆ I t ∧ ∀ S ⊆ I t, S.Nonempty → f S R ≤ α * e S ω := by
  refine mem_dynamicEClosure.trans (and_congr_right fun _ ↦ forall₂_congr fun S hS ↦ ?_)
  rw [arrivedECollection_of_subset hS]

/-- **The online SupFDR e-closure principle** [XFR26, Theorem 1; dH26, Remark 3.8]: for an
e-collection increasing along arrivals, whose value at a set is an e-variable for the
intersection null of the set, the dynamic e-closure of its fixed evidence controls the supremum
loss, for every loss vanishing when there are no true nulls. With `fdp`, it controls the SupFDR.
The e-collection need not be adapted to any filtration. -/
theorem controlsSupLoss_dynamicEClosure_arrivedECollection (hI : Monotone I)
    (hf₀ : ∀ R, f ∅ R = 0)
    (he : ∀ S, IsEVar (e S) {P | IsProbabilityMeasure P ∧ ∀ i ∈ S, P ∈ H i})
    (hinc : ∀ S t, e (S ∩ I t) ≤ e S) :
    ControlsSupLoss f α (dynamicEClosure f α (arrivedECollection e I) I) H I :=
  -- The supremum loss involves no filtration: use the constant filtration `⊤`.
  controlsSupLoss_dynamicEClosure (ℱ := ⊤) hI hf₀
    (isDynamicECollection_arrivedECollection (fun S _ ↦ he S) (fun _ S _ ↦ (he S).measurable)
      hinc)
    isFutureCoherent_arrivedECollection fun S _ ↦ monotone_arrivedECollection hI hinc S

/-- **The online e-closure families are nested** [XFR26, §2.1]: for an e-collection increasing
along arrivals and a loss that vanishes when there are no true nulls and depends only on the
rejected true nulls, every member of the dynamic e-closure at time `t` stays a member later. -/
theorem monotone_dynamicEClosure_arrivedECollection (hI : Monotone I) (hf₀ : ∀ R, f ∅ R = 0)
    (hf : ∀ S R, f S R = f (S ∩ R) R) (hinc : ∀ S t, e (S ∩ I t) ≤ e S) :
    Monotone fun t ↦ dynamicEClosure f α (arrivedECollection e I) I t :=
  monotone_dynamicEClosure hI hf₀ hf isFutureCoherent_arrivedECollection fun S _ ↦
    monotone_arrivedECollection hI hinc S

end Arrived

/-! ### Weighted e-collections and weighted self-consistency -/

section Weighted

variable {γ γ' : ι → ℝ≥0∞} {E : ι → Ω → ℝ≥0∞} {e e' : ι → ℝ≥0∞} {α α' : ℝ≥0∞}
  {R R' S S' : Finset ι}

/-- The **weighted e-collection** of statistics `E i` with weights `γ i`: the statistic of a set `S`
of hypotheses is `∑ i ∈ S, γ i * E i`, the e-collection behind [FXR26, Proposition 2.1]. -/
noncomputable def weightedECollection (γ : ι → ℝ≥0∞) (E : ι → Ω → ℝ≥0∞) (S : Finset ι) :
    Ω → ℝ≥0∞ :=
  fun ω ↦ ∑ i ∈ S, γ i * E i ω

theorem weightedECollection_def (γ : ι → ℝ≥0∞) (E : ι → Ω → ℝ≥0∞) (S : Finset ι) :
    weightedECollection γ E S = fun ω ↦ ∑ i ∈ S, γ i * E i ω := (rfl)

@[simp]
theorem weightedECollection_empty (γ : ι → ℝ≥0∞) (E : ι → Ω → ℝ≥0∞) :
    weightedECollection γ E ∅ = 0 := by
  ext ω
  simp [weightedECollection_def]

/-- The weighted e-collection is monotone in the set of hypotheses. -/
theorem weightedECollection_mono (h : S ⊆ S') :
    weightedECollection γ E S ≤ weightedECollection γ E S' :=
  fun _ ↦ sum_le_sum_of_subset h

/-- For weights of sum at most `1`, the weighted sum of e-variables `E i` for the hypotheses
`i ∈ S` is an e-variable for the intersection of their nulls. -/
theorem isEVar_weightedECollection (hγ : ∑' i, γ i ≤ 1) (hE : ∀ i ∈ S, IsEVar (E i) (H i)) :
    IsEVar (weightedECollection γ E S) (⋂ i ∈ S, H i) := by
  rw [weightedECollection_def]
  exact isEVar_finsetSum_mul S (fun i hi ↦ (hE i hi).anti_set (Set.biInter_subset_of_mem hi))
    ((sum_le_tsum S).trans hγ)

/-- A rejection set `R` is **self-consistent** at level `α` for the e-values `e` and the weights
`γ` [FXR26, §2.1] when `1 ≤ α * γ i * #R * e i` for every `i ∈ R`. For a level and weights in
`(0, ∞)`, this says that every rejected e-value is at least `(α * γ i * #R)⁻¹`. -/
def IsWeightedSelfConsistent (γ e : ι → ℝ≥0∞) (α : ℝ≥0∞) (R : Finset ι) : Prop :=
  ∀ i ∈ R, 1 ≤ α * γ i * #R * e i

theorem isWeightedSelfConsistent_iff :
    IsWeightedSelfConsistent γ e α R ↔ ∀ i ∈ R, 1 ≤ α * γ i * #R * e i :=
  Iff.rfl

@[simp]
theorem isWeightedSelfConsistent_empty : IsWeightedSelfConsistent γ e α ∅ := by
  simp [isWeightedSelfConsistent_iff]

/-- Weighted self-consistency is preserved by raising the level, the weights and the e-values. -/
theorem IsWeightedSelfConsistent.mono (h : IsWeightedSelfConsistent γ e α R) (hα : α ≤ α')
    (hγ : γ ≤ γ') (he : e ≤ e') : IsWeightedSelfConsistent γ' e' α' R :=
  fun i hi ↦ (h i hi).trans (by gcongr; exacts [hγ i, he i])

/-- The union of two weighted self-consistent sets is weighted self-consistent. -/
theorem IsWeightedSelfConsistent.union [DecidableEq ι] (h : IsWeightedSelfConsistent γ e α R)
    (h' : IsWeightedSelfConsistent γ e α R') : IsWeightedSelfConsistent γ e α (R ∪ R') := by
  intro i hi
  rcases mem_union.1 hi with hi | hi
  · exact (h i hi).trans (by gcongr; exact subset_union_left)
  · exact (h' i hi).trans (by gcongr; exact subset_union_right)

/-- **The false discovery proportion of a weighted self-consistent set**: for every set `N` of
hypotheses, `fdp N R ≤ α * ∑ i ∈ N, γ i * e i`. Each rejected hypothesis of `N` contributes
`1 / #R ≤ α * γ i * e i`. -/
theorem IsWeightedSelfConsistent.fdp_le [DecidableEq ι] (h : IsWeightedSelfConsistent γ e α R)
    (N : Finset ι) : fdp N R ≤ α * ∑ i ∈ N, γ i * e i := by
  rcases R.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
  · simp
  have hR0 : (#R : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (card_ne_zero_of_mem hj)
  -- Each rejected hypothesis contributes `1 / #R`, at most `α * γ i * e i` by self-consistency.
  have hi (i : ι) (hi : i ∈ R) : (#R : ℝ≥0∞)⁻¹ ≤ α * (γ i * e i) :=
    calc (#R : ℝ≥0∞)⁻¹ ≤ (#R : ℝ≥0∞)⁻¹ * (α * γ i * #R * e i) := le_mul_of_one_le_right' (h i hi)
      _ = (#R : ℝ≥0∞)⁻¹ * #R * (α * (γ i * e i)) := by ring
      _ = α * (γ i * e i) := by
          rw [ENNReal.inv_mul_cancel hR0 (ENNReal.natCast_ne_top _), one_mul]
  calc fdp N R = ∑ _ ∈ R ∩ N, (#R : ℝ≥0∞)⁻¹ := fdp_eq_sum_inv_card N R
    _ ≤ ∑ i ∈ R ∩ N, α * (γ i * e i) := sum_le_sum fun i hi' ↦ hi i (mem_inter.1 hi').1
    _ ≤ ∑ i ∈ N, α * (γ i * e i) := sum_le_sum_of_subset inter_subset_right
    _ = α * ∑ i ∈ N, γ i * e i := (mul_sum ..).symm

/-- **Self-consistency is weighted self-consistency for the weights `1 / K`**, with `K` the number
of hypotheses. -/
theorem isSelfConsistent_iff_isWeightedSelfConsistent [Fintype ι] :
    IsSelfConsistent e α R ↔
      IsWeightedSelfConsistent (fun _ ↦ (Fintype.card ι : ℝ≥0∞)⁻¹) e α R := by
  rw [isSelfConsistent_iff, isWeightedSelfConsistent_iff]
  refine forall₂_congr fun i _ ↦ ?_
  have : Nonempty ι := ⟨i⟩
  have hK : (Fintype.card ι : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h : α * (Fintype.card ι : ℝ≥0∞)⁻¹ * #R * e i = (α * #R * e i) / Fintype.card ι := by
    rw [ENNReal.div_eq_inv_mul]
    ring
  rw [h, ENNReal.le_div_iff_mul_le (Or.inl hK) (Or.inl (ENNReal.natCast_ne_top _)), one_mul]

/-- **Weighted self-consistent sets belong to the online e-closure** of the weighted e-collection
for the false discovery proportion. -/
theorem IsWeightedSelfConsistent.mem_dynamicEClosure [DecidableEq ι] {ω : Ω} (hRI : R ⊆ I t)
    (h : IsWeightedSelfConsistent γ (E · ω) α R) :
    R ∈ dynamicEClosure fdp α (arrivedECollection (weightedECollection γ E) I) I t ω :=
  mem_dynamicEClosure_arrivedECollection.2 ⟨hRI, fun _ _ _ ↦ by
    rw [weightedECollection_def]
    exact h.fdp_le _⟩

/-- **Weighted self-consistent sets control the SupFDR** [FXR26, Proposition 2.1]: for weights of
sum at most `1` and e-variables `E i` for the hypotheses, with no assumption on their dependence,
the family of the weighted self-consistent sets of arrived hypotheses controls the supremum over
time of the false discovery proportion at level `α`. When every hypothesis eventually arrives,
this bounds the expected supremum of the false discovery proportion over all finite
self-consistent sets. -/
theorem controlsSupLoss_isWeightedSelfConsistent [DecidableEq ι] (hI : Monotone I)
    (hγ : ∑' i, γ i ≤ 1) (hE : ∀ i, IsEVar (E i) (H i)) :
    ControlsSupLoss fdp α (fun t ω ↦ {R | R ⊆ I t ∧ IsWeightedSelfConsistent γ (E · ω) α R}) H I :=
  (controlsSupLoss_dynamicEClosure_arrivedECollection hI fdp_empty_left
    (fun _ ↦ (isEVar_weightedECollection hγ fun i _ ↦ hE i).anti_set fun _ hP ↦
      Set.mem_iInter₂.2 hP.2)
    fun _ _ ↦ weightedECollection_mono inter_subset_left).mono
    fun _ _ _ hR ↦ hR.2.mem_dynamicEClosure hR.1

end Weighted

/-! ### Online e-BH -/

section WeightedEBH

variable {γ γ' : ι → ℝ≥0∞} {E : ι → Ω → ℝ≥0∞} {e e' : ι → ℝ≥0∞} {α α' : ℝ≥0∞}
  {R J J' : Finset ι} {i : ι}

/-- **The weighted e-BH procedure** on a finite set `J` of hypotheses, at level `α`, for the
e-values `e` and the weights `γ` [FXR26, §2]: with `k*` the largest `k ≤ #J` such that at least `k`
hypotheses `j ∈ J` satisfy `1 ≤ α * γ j * k * e j`, it rejects the hypotheses `i ∈ J` with
`1 ≤ α * γ i * k* * e i`. With `J = I t` the hypotheses arrived at time `t`, this is the rejection
set of the **online e-BH procedure** at time `t`. It rejects `k*` hypotheses
(`ProbabilityTheory.card_weightedEBH`) and is the largest weighted self-consistent subset of `J`
(`ProbabilityTheory.isGreatest_weightedEBH`). -/
noncomputable def weightedEBH (γ e : ι → ℝ≥0∞) (α : ℝ≥0∞) (J : Finset ι) : Finset ι :=
  {i ∈ J | 1 ≤ α * γ i *
    (Nat.findGreatest (fun k ↦ k ≤ #{j ∈ J | 1 ≤ α * γ j * k * e j}) #J : ℕ) * e i}

theorem weightedEBH_def (γ e : ι → ℝ≥0∞) (α : ℝ≥0∞) (J : Finset ι) :
    weightedEBH γ e α J = {i ∈ J | 1 ≤ α * γ i *
      (Nat.findGreatest (fun k ↦ k ≤ #{j ∈ J | 1 ≤ α * γ j * k * e j}) #J : ℕ) * e i} :=
  (rfl)

/-- Weighted e-BH on `J` rejects only hypotheses of `J`. -/
theorem weightedEBH_subset : weightedEBH γ e α J ⊆ J := by
  rw [weightedEBH_def]
  exact filter_subset _ _

/-- The number `k*` of rejections of weighted e-BH on `J` bounds every weighted self-consistent
subset `R` of `J`: at least `#R` hypotheses `j ∈ J` satisfy `1 ≤ α * γ j * #R * e j`. -/
private lemma card_le_findGreatest (hRJ : R ⊆ J) (h : IsWeightedSelfConsistent γ e α R) :
    #R ≤ Nat.findGreatest (fun k ↦ k ≤ #{j ∈ J | 1 ≤ α * γ j * k * e j}) #J :=
  Nat.le_findGreatest (card_le_card hRJ) (card_le_card fun j hj ↦ mem_filter.2 ⟨hRJ hj, h j hj⟩)

/-- At least `k*` hypotheses `j ∈ J` satisfy `1 ≤ α * γ j * k* * e j`. -/
private lemma findGreatest_le_card_filter :
    Nat.findGreatest (fun k ↦ k ≤ #{j ∈ J | 1 ≤ α * γ j * k * e j}) #J ≤
      #{j ∈ J | 1 ≤ α * γ j *
        (Nat.findGreatest (fun k ↦ k ≤ #{j ∈ J | 1 ≤ α * γ j * k * e j}) #J : ℕ) * e j} :=
  Nat.findGreatest_spec (P := fun k ↦ k ≤ #{j ∈ J | 1 ≤ α * γ j * k * e j})
    (Nat.zero_le _) (Nat.zero_le _)

/-- A weighted self-consistent subset of `J` is contained in the weighted e-BH set of `J`. -/
theorem IsWeightedSelfConsistent.subset_weightedEBH (hRJ : R ⊆ J)
    (h : IsWeightedSelfConsistent γ e α R) : R ⊆ weightedEBH γ e α J := by
  intro i hi
  rw [weightedEBH_def, mem_filter]
  exact ⟨hRJ hi, (h i hi).trans (by gcongr; exact card_le_findGreatest hRJ h)⟩

/-- The weighted e-BH set is weighted self-consistent. -/
theorem isWeightedSelfConsistent_weightedEBH :
    IsWeightedSelfConsistent γ e α (weightedEBH γ e α J) := by
  intro i hi
  rw [weightedEBH_def, mem_filter] at hi
  refine hi.2.trans ?_
  gcongr
  exact findGreatest_le_card_filter

/-- **Weighted e-BH is the largest weighted self-consistent subset** of `J` [FXR26, §2.1]. -/
theorem isGreatest_weightedEBH :
    IsGreatest {R | R ⊆ J ∧ IsWeightedSelfConsistent γ e α R} (weightedEBH γ e α J) :=
  ⟨⟨weightedEBH_subset, isWeightedSelfConsistent_weightedEBH⟩, fun _ h ↦ h.2.subset_weightedEBH h.1⟩

/-- **The number of rejections of weighted e-BH** on `J` is `k*`, the largest `k ≤ #J` such that
at least `k` hypotheses `j ∈ J` satisfy `1 ≤ α * γ j * k * e j`. -/
theorem card_weightedEBH : #(weightedEBH γ e α J) =
    Nat.findGreatest (fun k ↦ k ≤ #{j ∈ J | 1 ≤ α * γ j * k * e j}) #J := by
  refine le_antisymm (card_le_findGreatest weightedEBH_subset
    isWeightedSelfConsistent_weightedEBH) ?_
  rw [weightedEBH_def]
  exact findGreatest_le_card_filter

/-- **The threshold form of weighted e-BH**: it rejects `i` exactly when `i ∈ J` and
`1 ≤ α * γ i * #(weightedEBH γ e α J) * e i`. -/
theorem mem_weightedEBH_iff_one_le_mul_card :
    i ∈ weightedEBH γ e α J ↔ i ∈ J ∧ 1 ≤ α * γ i * #(weightedEBH γ e α J) * e i := by
  conv_lhs => rw [weightedEBH_def]
  rw [mem_filter, card_weightedEBH]

/-- **Online e-BH never retracts a rejection** [FXR26, §2]: weighted e-BH is monotone in the set of
hypotheses, the level, the weights and the e-values. For a nondecreasing family `I t` of arrived
hypotheses, the online e-BH rejection sets are nested. -/
theorem weightedEBH_mono (hJ : J ⊆ J') (hα : α ≤ α') (hγ : γ ≤ γ') (he : e ≤ e') :
    weightedEBH γ e α J ⊆ weightedEBH γ' e' α' J' :=
  (isWeightedSelfConsistent_weightedEBH.mono hα hγ he).subset_weightedEBH
    (weightedEBH_subset.trans hJ)

/-- **Online e-BH generalizes e-BH** [FXR26, §2]: e-BH on `K` hypotheses is weighted e-BH on all of
them with the weights `1 / K`. -/
theorem eBH_eq_weightedEBH [Fintype ι] :
    eBH e α = weightedEBH (fun _ ↦ (Fintype.card ι : ℝ≥0∞)⁻¹) e α univ := by
  refine isGreatest_eBH.unique ?_
  simpa only [subset_univ, true_and, ← isSelfConsistent_iff_isWeightedSelfConsistent] using
    isGreatest_weightedEBH (γ := fun _ ↦ (Fintype.card ι : ℝ≥0∞)⁻¹) (e := e) (α := α) (J := univ)

/-- **Online e-BH controls the SupFDR** [FXR26, Theorem 2.2]: for weights of sum at most `1` and
e-variables `E i` for the hypotheses, with no assumption on their dependence, the online e-BH
procedure, rejecting `weightedEBH γ (E · ω) α (I t)` at time `t`, controls the supremum over time
of the false discovery proportion at level `α`. -/
theorem controlsSupLoss_weightedEBH [DecidableEq ι] (hI : Monotone I) (hγ : ∑' i, γ i ≤ 1)
    (hE : ∀ i, IsEVar (E i) (H i)) :
    ControlsSupLoss fdp α (fun t ω ↦ {weightedEBH γ (E · ω) α (I t)}) H I :=
  (controlsSupLoss_isWeightedSelfConsistent hI hγ hE).mono fun _ _ R hR ↦ by
    rw [Set.mem_singleton_iff.1 hR]
    exact ⟨weightedEBH_subset, isWeightedSelfConsistent_weightedEBH⟩

/-- **The SupFDR of online e-BH** [FXR26, Theorem 2.2]: under every probability measure, the
expected supremum over time of the false discovery proportion of online e-BH is at most `α`. -/
theorem lintegral_iSup_fdp_weightedEBH_le [DecidableEq ι] (hI : Monotone I) (hγ : ∑' i, γ i ≤ 1)
    (hE : ∀ i, IsEVar (E i) (H i)) (P : Measure Ω) [IsProbabilityMeasure P] :
    ∫⁻ ω, ⨆ t, fdp (activeTrueNulls H I P t) (weightedEBH γ (E · ω) α (I t)) ∂P ≤ α := by
  simpa using (controlsSupLoss_weightedEBH hI hγ hE).lintegral_iSup_le P

end WeightedEBH

/-! ### e-LOND -/

section ELOND

variable {γ e : ℕ → ℝ≥0∞} {α : ℝ≥0∞} {i : ℕ}

/-- **The e-LOND procedure** [XR24, §2; FXR26, §2.2] at level `α`, for the e-values
`e` and the weights `γ`: the hypothesis `t` arrives at time `t + 1`, and is rejected when
`1 ≤ α * γ t * (#R + 1) * e t`, with `R` the rejection set at time `t`; that is, when its e-value is
at least `1 / α t` for the level `α t = α * γ t * (#R + 1)`. -/
noncomputable def eLOND (γ e : ℕ → ℝ≥0∞) (α : ℝ≥0∞) : ℕ → Finset ℕ
  | 0 => ∅
  | t + 1 => if 1 ≤ α * γ t * ((#(eLOND γ e α t) : ℝ≥0∞) + 1) * e t then
      insert t (eLOND γ e α t) else eLOND γ e α t

@[simp]
theorem eLOND_zero : eLOND γ e α 0 = ∅ :=
  eLOND.eq_1 γ e α

theorem eLOND_succ (t : ℕ) : eLOND γ e α (t + 1) =
    if 1 ≤ α * γ t * ((#(eLOND γ e α t) : ℝ≥0∞) + 1) * e t then insert t (eLOND γ e α t)
    else eLOND γ e α t :=
  eLOND.eq_2 γ e α t

/-- At time `t`, e-LOND rejects only hypotheses that have arrived. -/
theorem eLOND_subset_range (t : ℕ) : eLOND γ e α t ⊆ range t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [eLOND_succ, range_add_one]
    split_ifs
    · exact insert_subset_insert t ih
    · exact ih.trans (subset_insert t _)

/-- **e-LOND never retracts a rejection.** -/
theorem monotone_eLOND : Monotone (eLOND γ e α) := by
  refine monotone_nat_of_le_succ fun t ↦ ?_
  rw [eLOND_succ]
  split_ifs
  exacts [subset_insert t _, le_rfl]

/-- **The rejection sets of e-LOND** [XR24, §2]: e-LOND rejects at time `t` the arrived
hypotheses `i < t` with `1 ≤ α * γ i * (#R + 1) * e i`, with `R` its rejection set at time `i`. -/
theorem mem_eLOND_iff :
    i ∈ eLOND γ e α t ↔ i < t ∧ 1 ≤ α * γ i * ((#(eLOND γ e α i) : ℝ≥0∞) + 1) * e i := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [eLOND_succ]
    split_ifs with h
    · rw [mem_insert, ih]
      refine ⟨?_, fun ⟨hi, hc⟩ ↦ ?_⟩
      · rintro (rfl | ⟨hi, hc⟩)
        exacts [⟨Nat.lt_succ_self i, h⟩, ⟨hi.trans (Nat.lt_succ_self t), hc⟩]
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        exacts [Or.inr ⟨hi, hc⟩, Or.inl rfl]
    · rw [ih]
      refine ⟨fun ⟨hi, hc⟩ ↦ ⟨hi.trans (Nat.lt_succ_self t), hc⟩, fun ⟨hi, hc⟩ ↦ ⟨?_, hc⟩⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      exacts [hi, absurd hc h]

/-- **The rejection sets of e-LOND are weighted self-consistent**: a hypothesis rejected at time
`i + 1` was tested at a level that counts the `#R + 1 ≤ #(eLOND γ e α t)` rejections of the time
`i + 1`. -/
theorem isWeightedSelfConsistent_eLOND (t : ℕ) :
    IsWeightedSelfConsistent γ e α (eLOND γ e α t) := by
  intro i hi
  obtain ⟨hit, hc⟩ := mem_eLOND_iff.1 hi
  refine hc.trans ?_
  -- The rejection of `i` at time `i + 1` adds `i` to the rejection set of time `i`.
  have hsucc : eLOND γ e α (i + 1) = insert i (eLOND γ e α i) := by rw [eLOND_succ, ite_eq_left hc]
  have hnot : i ∉ eLOND γ e α i := fun h ↦ (notMem_range_self (n := i)) (eLOND_subset_range i h)
  have hcard : #(eLOND γ e α i) + 1 ≤ #(eLOND γ e α t) := by
    rw [← card_insert_of_notMem hnot, ← hsucc]
    exact card_le_card (monotone_eLOND hit)
  gcongr
  exact_mod_cast hcard

/-- **Online e-BH uniformly improves e-LOND** [FXR26, §2.2]: at every time, the rejection set of
e-LOND is contained in that of online e-BH for the same weights. -/
theorem eLOND_subset_weightedEBH (t : ℕ) : eLOND γ e α t ⊆ weightedEBH γ e α (range t) :=
  (isWeightedSelfConsistent_eLOND t).subset_weightedEBH (eLOND_subset_range t)

/-- **e-LOND controls the SupFDR** [FXR26, Proposition 2.3; XR24, Theorem 1]: for weights of sum
at most `1` and e-variables `E i` for the hypotheses, with no assumption on their dependence, the
e-LOND procedure controls the supremum over time of the false discovery proportion at level `α`.
-/
theorem controlsSupLoss_eLOND {H : ℕ → Set (Measure Ω)} {E : ℕ → Ω → ℝ≥0∞} (hγ : ∑' i, γ i ≤ 1)
    (hE : ∀ i, IsEVar (E i) (H i)) :
    ControlsSupLoss fdp α (fun t ω ↦ {eLOND γ (E · ω) α t}) H range :=
  (controlsSupLoss_isWeightedSelfConsistent range_mono hγ hE).mono fun t _ R hR ↦ by
    rw [Set.mem_singleton_iff.1 hR]
    exact ⟨eLOND_subset_range t, isWeightedSelfConsistent_eLOND t⟩

/-- **The SupFDR of e-LOND** [FXR26, Proposition 2.3]: under every probability measure, the
expected supremum over time of the false discovery proportion of e-LOND is at most `α`. -/
theorem lintegral_iSup_fdp_eLOND_le {H : ℕ → Set (Measure Ω)} {E : ℕ → Ω → ℝ≥0∞}
    (hγ : ∑' i, γ i ≤ 1) (hE : ∀ i, IsEVar (E i) (H i)) (P : Measure Ω) [IsProbabilityMeasure P] :
    ∫⁻ ω, ⨆ t, fdp (activeTrueNulls H range P t) (eLOND γ (E · ω) α t) ∂P ≤ α := by
  simpa using (controlsSupLoss_eLOND hγ hE).lintegral_iSup_le P

end ELOND

/-! ### Stopped e-BH -/

section Stopped

variable {M : ι → ℕ → Ω → ℝ≥0∞} {α : ℝ≥0∞}

/-- The mean of e-processes `M i` for the hypotheses `i ∈ S`, in a common filtration, is an
e-process for the intersection of their nulls. -/
theorem isEProcess_meanECollection {S : Finset ι} (hM : ∀ i ∈ S, IsEProcess (M i) ℱ (H i)) :
    IsEProcess (fun t ↦ meanECollection (M · t) S) ℱ (⋂ i ∈ S, H i) := by
  refine ⟨fun t ↦ ?_, fun τ hτ N hτN ↦ ?_⟩
  · have h : meanECollection (M · t) S = fun ω ↦ (∑ i ∈ S, M i t ω) / #S :=
      funext (meanECollection_def _ S)
    rw [h]
    exact (Finset.measurable_sum S fun i hi ↦ (hM i hi).adapted t).div_const _
  · have h : stoppedValue (fun t ↦ meanECollection (M · t) S) τ =
        meanECollection (fun i ↦ stoppedValue (M i) τ) S := by
      ext ω
      simp only [stoppedValue, meanECollection_def]
    rw [h]
    exact isEVar_meanECollection fun i hi ↦ (hM i hi).isEVar_stoppedValue_of_le hτ hτN

/-- The means of e-processes for the hypotheses, in a common filtration, form a dynamic
intersection e-process collection. -/
theorem isDynamicECollection_meanECollection (hM : ∀ i, IsEProcess (M i) ℱ (H i)) :
    IsDynamicECollection (fun S t ↦ meanECollection (M · t) S) H ℱ where
  isEProcess _ _ := (isEProcess_meanECollection fun i _ ↦ hM i).anti_set fun _ hP ↦
    Set.mem_iInter₂.2 hP.2

variable [Fintype ι] [DecidableEq ι]

/-- **Stopped closed e-BH** [WDR25, Theorem 2.4 and the remark after Lemma 2.1]: for e-processes
`M i` for the hypotheses in a common filtration, with no assumption on their dependence, the
closed e-BH families of their values (the mean-consistent sets) control the false discovery rate,
simultaneously over the family, at every stopping time that is almost surely finite. -/
theorem controlsStoppedLoss_isMeanConsistent (hM : ∀ i, IsEProcess (M i) ℱ (H i)) :
    ControlsStoppedLoss fdp α (fun t ω ↦ {R | IsMeanConsistent (M · t ω) α R}) H
      (fun _ ↦ univ) ℱ :=
  (controlsStoppedLoss_dynamicEClosure monotone_const fdp_empty_left
    (isDynamicECollection_meanECollection hM) ⟨fun _ _ _ ↦ by simp⟩).mono fun _ _ _ hR ↦ by
      rw [dynamicEClosure_const_univ fdp_empty_left]
      exact mem_eClosure_meanECollection_iff.2 hR

/-- **Stopped e-BH** [WDR25, Theorem 2.4]: for e-processes `M i` for the hypotheses in a common
filtration, with no assumption on their dependence, e-BH applied to their values controls the
false discovery rate at every stopping time that is almost surely finite. -/
theorem controlsStoppedLoss_eBH (hM : ∀ i, IsEProcess (M i) ℱ (H i)) :
    ControlsStoppedLoss fdp α (fun t ω ↦ {eBH (M · t ω) α}) H (fun _ ↦ univ) ℱ :=
  (controlsStoppedLoss_isMeanConsistent hM).mono fun _ _ R hR ↦ by
    rw [Set.mem_singleton_iff.1 hR]
    exact isMeanConsistent_eBH

/-- **The false discovery rate of stopped e-BH** [WDR25, Theorem 2.4]: under every probability
measure and at every stopping time `τ` that is almost surely finite, e-BH applied to the values
`stoppedValue (M i) τ` of the e-processes has false discovery rate at most `α`. -/
theorem lintegral_fdp_eBH_stoppedValue_le (hM : ∀ i, IsEProcess (M i) ℱ (H i)) (P : Measure Ω)
    [IsProbabilityMeasure P] {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ)
    (hτ_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∫⁻ ω, fdp (trueNulls H P) (eBH (fun i ↦ stoppedValue (M i) τ ω) α) ∂P ≤ α := by
  simpa [stoppedValue] using (controlsStoppedLoss_eBH (α := α) hM).lintegral_le P hτ hτ_top

end Stopped

end ProbabilityTheory
