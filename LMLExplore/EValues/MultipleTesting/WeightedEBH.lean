/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.MultipleTesting.EClosure

/-!
# Weighted self-consistency and the weighted e-BH procedure

Hypotheses are indexed by a type `ι`, with realized e-values `e : ι → ℝ≥0∞` and weights
`γ : ι → ℝ≥0∞`. A set `R` of hypotheses is self-consistent at level `α` for the weights
(`ProbabilityTheory.IsWeightedSelfConsistent`) when `1 ≤ α * γ i * #R * e i` for every `i ∈ R`
[FXR26, §2.1]. The weighted e-BH procedure on a finite set `J` of hypotheses
(`ProbabilityTheory.weightedEBH`) rejects the largest weighted self-consistent subset of `J`; with
`J` the hypotheses arrived at time `t`, it is the online e-BH procedure of [FXR26, §2]. The e-BH
procedure of `LMLExplore.EValues.MultipleTesting.EBH` is the case of the weights `1 / K` on all
`K` hypotheses, and its API is derived from the one of this file.

## Main definitions

* `ProbabilityTheory.IsWeightedSelfConsistent γ e α R`: weighted self-consistency.
* `ProbabilityTheory.weightedECollection γ E`: the weighted e-collection `S ↦ ∑ i ∈ S, γ i * E i`,
  which bounds, up to the factor `α`, the false discovery proportion of a weighted self-consistent
  set.
* `ProbabilityTheory.weightedEBH γ e α J`: the weighted e-BH procedure on the finite set `J`.

## Main statements

* `ProbabilityTheory.IsWeightedSelfConsistent.fdp_le`: the false discovery proportion of a
  weighted self-consistent set.
* `ProbabilityTheory.isEVar_weightedECollection`: for weights of sum at most `1`, the weighted
  e-collection of e-variables is an e-variable for the intersection null.
* `ProbabilityTheory.isGreatest_weightedEBH`, `ProbabilityTheory.mem_weightedEBH_iff_exists`:
  weighted e-BH is the largest weighted self-consistent subset of `J` and the union of all of them
  [FXR26, §2.1].
* `ProbabilityTheory.card_weightedEBH`, `ProbabilityTheory.mem_weightedEBH_iff_one_le_mul_card`:
  the number of rejections of weighted e-BH, and its threshold form.
* `ProbabilityTheory.weightedEBH_mono`: weighted e-BH is monotone in the set of hypotheses, the
  level, the weights and the e-values, so online e-BH never retracts a rejection [FXR26, §2].

## References

* [FXR26] L. Fischer, Z. Xu and A. Ramdas, *An online generalization of the (e-)Benjamini–Hochberg
  procedure*, arXiv:2407.20683v5.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {ι : Type*}

/-! ### Weighted self-consistency -/

section WeightedSelfConsistent

variable {γ γ' : ι → ℝ≥0∞} {e e' : ι → ℝ≥0∞} {α α' : ℝ≥0∞} {R R' : Finset ι}

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
hypotheses, `fdp N R ≤ α * ∑ i ∈ N, γ i * e i`. -/
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

end WeightedSelfConsistent

/-! ### Weighted e-collections -/

section WeightedECollection

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {H : ι → Set (Measure Ω)} {γ : ι → ℝ≥0∞}
  {E : ι → Ω → ℝ≥0∞} {S S' : Finset ι}

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

end WeightedECollection

/-! ### The weighted e-BH procedure -/

section WeightedEBH

variable {γ γ' : ι → ℝ≥0∞} {e e' : ι → ℝ≥0∞} {α α' : ℝ≥0∞} {R J J' : Finset ι} {i : ι}

/-- **The weighted e-BH procedure** on a finite set `J` of hypotheses, at level `α`, for the
e-values `e` and the weights `γ` [FXR26, §2]: with `k*` the largest `k ≤ #J` such that at least `k`
hypotheses `j ∈ J` satisfy `1 ≤ α * γ j * k * e j`, it rejects the hypotheses `i ∈ J` with
`1 ≤ α * γ i * k* * e i`. With `J` the hypotheses arrived at time `t`, this is the rejection
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

/-- On no hypotheses, weighted e-BH rejects nothing. -/
@[simp]
theorem weightedEBH_empty (γ e : ι → ℝ≥0∞) (α : ℝ≥0∞) : weightedEBH γ e α ∅ = ∅ :=
  subset_empty.1 weightedEBH_subset

/-- At level `0`, weighted e-BH rejects nothing. -/
@[simp]
theorem weightedEBH_zero (γ e : ι → ℝ≥0∞) (J : Finset ι) : weightedEBH γ e 0 J = ∅ := by
  simp [weightedEBH_def]

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

/-- **Weighted e-BH is the union of all weighted self-consistent subsets** of `J`: it rejects `i`
exactly when some weighted self-consistent subset of `J` contains `i`. -/
theorem mem_weightedEBH_iff_exists :
    i ∈ weightedEBH γ e α J ↔ ∃ R ⊆ J, IsWeightedSelfConsistent γ e α R ∧ i ∈ R :=
  ⟨fun hi ↦ ⟨_, weightedEBH_subset, isWeightedSelfConsistent_weightedEBH, hi⟩,
    fun ⟨_, hRJ, h, hi⟩ ↦ h.subset_weightedEBH hRJ hi⟩

/-- **Weighted e-BH makes a rejection exactly when some nonempty subset of `J` is weighted
self-consistent.** -/
theorem weightedEBH_nonempty_iff :
    (weightedEBH γ e α J).Nonempty ↔ ∃ R ⊆ J, R.Nonempty ∧ IsWeightedSelfConsistent γ e α R :=
  ⟨fun h ↦ ⟨_, weightedEBH_subset, h, isWeightedSelfConsistent_weightedEBH⟩,
    fun ⟨_, hRJ, hR, h⟩ ↦ hR.mono (h.subset_weightedEBH hRJ)⟩

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
hypotheses, the level, the weights and the e-values. For a nondecreasing family of sets of arrived
hypotheses, the online e-BH rejection sets are nested. -/
theorem weightedEBH_mono (hJ : J ⊆ J') (hα : α ≤ α') (hγ : γ ≤ γ') (he : e ≤ e') :
    weightedEBH γ e α J ⊆ weightedEBH γ' e' α' J' :=
  (isWeightedSelfConsistent_weightedEBH.mono hα hγ he).subset_weightedEBH
    (weightedEBH_subset.trans hJ)

end WeightedEBH

end ProbabilityTheory
