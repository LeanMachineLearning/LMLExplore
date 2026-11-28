/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.AddContent
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import TauCeti.MeasureTheory.SetAlgebra

/-!
# The Yosida–Hewitt decomposition of a finitely additive measure

A finitely additive measure on `α` is an additive content on its measurable sets,
`m : AddContent ℝ≥0∞ {s : Set α | MeasurableSet s}`. Its countably additive part `m_c` is the
supremum of the measures that are below `m` on the measurable sets. It is itself below `m` on the
measurable sets, so it is the largest such measure: every measure below `m` is below the outer
measure induced by `m`, for which the measurable sets are Carathéodory measurable by the finite
additivity of `m`, and that outer measure is at most `m` on the measurable sets.

An additive content dominated by a finite measure is countably additive, since it is continuous at
`∅`. When `m` has finite mass, this gives the decomposition of Yosida and Hewitt [YH52]:

* the remainder `p = m - m_c` is purely finitely additive: the only measure below it on the
  measurable sets is `0`;
* `m = m_c + p` is the only decomposition of `m`, on the measurable sets, into a measure and a set
  function below which the only measure is `0`;
* `p` is singular to every finite measure `R`: for every `ε > 0`, some measurable set `E` has
  `R E + p Eᶜ < ε`. The set function `A ↦ ⨅ B ⊆ A, R B + p (A \ B)`, over the measurable `B`, is
  finitely additive and below `R`, hence a measure, and it is below `p`, hence `0`.

## Main definitions

* `MeasureTheory.countablyAdditivePart ν`: the supremum of the measures below a set function `ν`
  on the measurable sets.

## Main statements

* `MeasureTheory.addContent_iUnion_eq_tsum_of_le_measure`: an additive content on a ring of
  null-measurable sets that is dominated by a finite measure is countably additive.
* `MeasureTheory.countablyAdditivePart_apply_le`, `MeasureTheory.isGreatest_countablyAdditivePart`:
  the countably additive part of an additive content is the largest measure below it.
* `MeasureTheory.countablyAdditivePart_mono`, `MeasureTheory.countablyAdditivePart_coe`: the
  countably additive part is monotone, and a measure is its own countably additive part.
* `MeasureTheory.AddContent.apply_ne_top_of_univ_ne_top`: an additive content of finite mass is
  finite on the measurable sets.
* `MeasureTheory.countablyAdditivePart_fun_sub_countablyAdditivePart_self_eq_zero`: the remainder
  `m - m_c` is purely finitely additive.
* `MeasureTheory.eq_countablyAdditivePart`, `MeasureTheory.apply_eq_sub_countablyAdditivePart`: the
  uniqueness of the decomposition.
* `MeasureTheory.exists_measurableSet_add_sub_countablyAdditivePart_lt`: the remainder is
  singular to every finite measure.

## Implementation notes

Purely finitely additive set functions have no definition of their own: `ν` is one when
`countablyAdditivePart ν = 0` (`MeasureTheory.countablyAdditivePart_eq_zero_iff`). The countably
additive part is defined for every set function, so that purely finitely additive set functions
need no separate definition, and its properties are stated for additive contents on the measurable
sets. The countable additivity of
a dominated content is Mathlib's `MeasureTheory.addContent_iUnion_eq_sum_of_tendsto_zero`, the form
in `ℝ≥0∞` of Mathlib's `MeasureTheory.VectorMeasure.of_additive_of_le_measure`.

The statements and proofs are adapted from
`EValuesResearch/ForLMLExplore/MeasureTheory/Measure/FinitelyAdditive.lean` (commit `83205cb`) in
the paper project `RemyDegenne/evalues_research`, rewritten on Mathlib's `AddContent`; the
uniqueness of the decomposition is proved here.

## References

* [YH52] K. Yosida and E. Hewitt, *Finitely additive measures*, Trans. Amer. Math. Soc. 72
  (1952), 46–66.
-/

public section

open Set Filter Function
open scoped ENNReal Topology

namespace MeasureTheory

variable {α : Type*} [mα : MeasurableSpace α]

/-! ### Additive contents dominated by a finite measure -/

/-- **An additive content dominated by a finite measure is countably additive.** Let `m` be an
additive content on a ring `C` of `μ`-null-measurable sets with `m s ≤ μ s` for every `s ∈ C`, for
a finite measure `μ`. Then `m (⋃ i, f i) = ∑' i, m (f i)` for pairwise disjoint `f i ∈ C` whose
union is in `C`. -/
theorem addContent_iUnion_eq_tsum_of_le_measure {C : Set (Set α)} (hC : IsSetRing C)
    {m : AddContent ℝ≥0∞ C} (μ : Measure α) [IsFiniteMeasure μ]
    (hCμ : ∀ s ∈ C, NullMeasurableSet s μ) (hmμ : ∀ s ∈ C, m s ≤ μ s) {f : ℕ → Set α}
    (hf : ∀ i, f i ∈ C) (hfU : ⋃ i, f i ∈ C) (hd : Pairwise (Disjoint on f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  -- the content is continuous at `∅`, being dominated by `μ`
  refine addContent_iUnion_eq_sum_of_tendsto_zero hC m
    (fun s hs ↦ ne_top_of_le_ne_top (measure_ne_top μ s) (hmμ s hs))
    (fun s hs hanti hempty ↦ ?_) hf hfU hd
  have hμs : Tendsto (fun n ↦ μ (s n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (fun n ↦ hCμ _ (hs n))
      hanti ⟨0, measure_ne_top μ _⟩
    rwa [hempty, measure_empty] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hμs (fun _ ↦ zero_le)
    fun n ↦ hmμ _ (hs n)

/-! ### The countably additive part of a set function -/

/-- The **countably additive part** of a set function `ν`: the supremum of the measures that are
below `ν` on the measurable sets. For an additive content on the measurable sets, it is the
largest such measure (`MeasureTheory.isGreatest_countablyAdditivePart`). -/
noncomputable def countablyAdditivePart (ν : Set α → ℝ≥0∞) : Measure α :=
  sSup {μ : Measure α | ∀ s, MeasurableSet s → μ s ≤ ν s}

variable {ν : Set α → ℝ≥0∞} {μ : Measure α}

/-- The definition of the countably additive part, as the supremum of the measures below `ν` on
the measurable sets. -/
theorem countablyAdditivePart_def (ν : Set α → ℝ≥0∞) :
    countablyAdditivePart ν = sSup {μ : Measure α | ∀ s, MeasurableSet s → μ s ≤ ν s} :=
  (rfl)

/-- Every measure below `ν` on the measurable sets is below the countably additive part of `ν`. -/
theorem le_countablyAdditivePart (h : ∀ s, MeasurableSet s → μ s ≤ ν s) :
    μ ≤ countablyAdditivePart ν :=
  le_sSup h

/-- The countably additive part of `ν` is `0` exactly when `0` is the only measure below `ν` on
the measurable sets: `ν` is then purely finitely additive, in the sense of Yosida and Hewitt
[YH52]. -/
theorem countablyAdditivePart_eq_zero_iff :
    countablyAdditivePart ν = 0 ↔
      ∀ μ : Measure α, (∀ s, MeasurableSet s → μ s ≤ ν s) → μ = 0 := by
  rw [countablyAdditivePart_def]
  exact sSup_eq_bot

/-- The countably additive part is monotone: if `ν ≤ ν'` on the measurable sets, then
`countablyAdditivePart ν ≤ countablyAdditivePart ν'`. -/
theorem countablyAdditivePart_mono {ν' : Set α → ℝ≥0∞}
    (h : ∀ s, MeasurableSet s → ν s ≤ ν' s) :
    countablyAdditivePart ν ≤ countablyAdditivePart ν' :=
  sSup_le_sSup fun _ hμ s hs ↦ (hμ s hs).trans (h s hs)

/-- A measure is its own countably additive part. -/
@[simp]
theorem countablyAdditivePart_coe (μ : Measure α) : countablyAdditivePart μ = μ :=
  le_antisymm (sSup_le fun _ h ↦ Measure.le_iff.2 h) (le_countablyAdditivePart fun _ _ ↦ le_rfl)

/-- **The countably additive part of an additive content is below it** on the measurable sets. -/
theorem countablyAdditivePart_apply_le (m : AddContent ℝ≥0∞ {s : Set α | MeasurableSet s})
    {s : Set α} (hs : MeasurableSet s) :
    countablyAdditivePart m s ≤ m s := by
  -- every measure below `m` is below the outer measure induced by `m`, for which the measurable
  -- sets are Carathéodory measurable by the finite additivity of `m`, and that outer measure is at
  -- most `m` on the measurable sets
  have hC := (isSetRing_measurableSet (α := α)).isSetSemiring
  set ρ := inducedOuterMeasure (fun t (_ : t ∈ {t : Set α | MeasurableSet t}) ↦ m t)
    hC.empty_mem addContent_empty with hρ
  have hcar : mα ≤ ρ.caratheodory := fun t ht ↦
    AddContent.isCaratheodory_inducedOuterMeasure hC m t
      (by rwa [MeasurableSpace.generateFrom_measurableSet])
  have hle : countablyAdditivePart m ≤ ρ.toMeasure hcar :=
    sSup_le fun μ hμ ↦ Measure.le_iff.2 fun t ht ↦ by
      rw [toMeasure_apply _ _ ht]
      exact le_inducedOuterMeasure.2 hμ t
  calc countablyAdditivePart m s ≤ ρ.toMeasure hcar s := Measure.le_iff'.1 hle s
    _ = ρ s := toMeasure_apply _ _ hs
    _ ≤ m s := (OuterMeasure.ofFunction_le s).trans (extend_eq _ hs).le

/-- The countably additive part of an additive content `m` on the measurable sets is the largest
measure below `m` on the measurable sets. -/
theorem isGreatest_countablyAdditivePart (m : AddContent ℝ≥0∞ {s : Set α | MeasurableSet s}) :
    IsGreatest {μ : Measure α | ∀ s, MeasurableSet s → μ s ≤ m s} (countablyAdditivePart m) :=
  ⟨fun _ hs ↦ countablyAdditivePart_apply_le m hs, fun _ hμ ↦ le_countablyAdditivePart hμ⟩

/-- The countably additive part of an additive content of finite mass is a finite measure. -/
theorem isFiniteMeasure_countablyAdditivePart
    {m : AddContent ℝ≥0∞ {s : Set α | MeasurableSet s}} (hm : m univ ≠ ∞) :
    IsFiniteMeasure (countablyAdditivePart m) :=
  ⟨(countablyAdditivePart_apply_le m .univ).trans_lt hm.lt_top⟩

/-! ### The Yosida–Hewitt decomposition -/

variable {m : AddContent ℝ≥0∞ {s : Set α | MeasurableSet s}}

/-- An additive content of finite mass on the measurable sets is finite on the measurable sets. -/
theorem AddContent.apply_ne_top_of_univ_ne_top (hm : m univ ≠ ∞) {s : Set α}
    (hs : MeasurableSet s) : m s ≠ ∞ :=
  ne_top_of_le_ne_top hm
    (addContent_mono isSetRing_measurableSet.isSetSemiring hs .univ (subset_univ s))

/-- For an additive content of finite mass, the remainder `m - m_c` after its countably additive
part is additive on the measurable sets. -/
private lemma sub_countablyAdditivePart_union (hm : m univ ≠ ∞) {s t : Set α}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    m (s ∪ t) - countablyAdditivePart m (s ∪ t) =
      (m s - countablyAdditivePart m s) + (m t - countablyAdditivePart m t) := by
  have := isFiniteMeasure_countablyAdditivePart hm
  rw [addContent_union isSetRing_measurableSet hs ht hst, measure_union hst ht,
    (ENNReal.cancel_of_ne (measure_ne_top _ s)).tsub_add_tsub_comm
      (ENNReal.cancel_of_ne (measure_ne_top _ t)) (countablyAdditivePart_apply_le m hs)
      (countablyAdditivePart_apply_le m ht)]

/-- **The remainder after the countably additive part is purely finitely additive** [YH52]. For
an additive content `m` of finite mass on the measurable sets, the only measure below
`m - countablyAdditivePart m` on the measurable sets is `0`. -/
theorem countablyAdditivePart_fun_sub_countablyAdditivePart_self_eq_zero (hm : m univ ≠ ∞) :
    countablyAdditivePart (fun s ↦ m s - countablyAdditivePart m s) = 0 := by
  have := isFiniteMeasure_countablyAdditivePart hm
  refine countablyAdditivePart_eq_zero_iff.2 fun μ hμ ↦ ?_
  -- the sum of `μ` with the countably additive part is again below `m`
  have hle : countablyAdditivePart m + μ ≤ countablyAdditivePart m :=
    le_countablyAdditivePart fun s hs ↦ by
      rw [add_apply]
      calc countablyAdditivePart m s + μ s
          ≤ countablyAdditivePart m s + (m s - countablyAdditivePart m s) := by
            gcongr; exact hμ s hs
        _ = m s := add_tsub_cancel_of_le (countablyAdditivePart_apply_le m hs)
  have h := Measure.le_iff'.1 hle univ
  rw [add_apply] at h
  exact Measure.measure_univ_eq_zero.1 (le_antisymm
    (ENNReal.le_of_add_le_add_left (measure_ne_top _ _) (h.trans (add_zero _).symm.le)) bot_le)

/-- **The Yosida–Hewitt decomposition is unique** [YH52]: if an additive content `m` of finite
mass is, on the measurable sets, the sum of a measure `μ` and of a set function `q` whose countably
additive part is `0`, then `μ` is the countably additive part of `m`. -/
theorem eq_countablyAdditivePart (hm : m univ ≠ ∞) {q : Set α → ℝ≥0∞}
    (hq : countablyAdditivePart q = 0) (h : ∀ s, MeasurableSet s → m s = μ s + q s) :
    μ = countablyAdditivePart m := by
  have hμm : μ ≤ countablyAdditivePart m :=
    le_countablyAdditivePart fun s hs ↦ (h s hs).symm ▸ le_self_add
  have : IsFiniteMeasure μ := ⟨(le_self_add.trans_eq (h univ .univ).symm).trans_lt hm.lt_top⟩
  -- the measure `countablyAdditivePart m - μ` is below `q`, hence `0`
  have h0 : countablyAdditivePart m - μ = 0 :=
    countablyAdditivePart_eq_zero_iff.1 hq _ fun s hs ↦ by
      rw [Measure.sub_apply hs hμm]
      calc countablyAdditivePart m s - μ s ≤ m s - μ s := by
            gcongr; exact countablyAdditivePart_apply_le m hs
        _ = q s := by rw [h s hs, ENNReal.add_sub_cancel_left (measure_ne_top μ s)]
  rw [← Measure.sub_add_cancel_of_le hμm, h0, zero_add]

/-- **The Yosida–Hewitt decomposition is unique**, its purely finitely additive part: if an
additive content `m` of finite mass is, on the measurable sets, the sum of a measure `μ` and of a
set function `q` whose countably additive part is `0`, then `q` is `m - countablyAdditivePart m`
on the measurable sets. -/
theorem apply_eq_sub_countablyAdditivePart (hm : m univ ≠ ∞) {q : Set α → ℝ≥0∞}
    (hq : countablyAdditivePart q = 0) (h : ∀ s, MeasurableSet s → m s = μ s + q s) {s : Set α}
    (hs : MeasurableSet s) :
    q s = m s - countablyAdditivePart m s := by
  have hμs : μ s ≠ ∞ := ne_top_of_le_ne_top (AddContent.apply_ne_top_of_univ_ne_top hm hs)
    ((h s hs).symm ▸ le_self_add)
  rw [← eq_countablyAdditivePart hm hq h, h s hs, ENNReal.add_sub_cancel_left hμs]

/-- The inf-convolution `A ↦ ⨅ B ⊆ A, R B + p (A \ B)`, over the measurable `B`, of a measure `R`
and of a set function `p` additive on the measurable sets is additive on the measurable sets. -/
private lemma iInf_add_sdiff_union (R : Measure α) {p : Set α → ℝ≥0∞}
    (hpadd : ∀ s t, MeasurableSet s → MeasurableSet t → Disjoint s t → p (s ∪ t) = p s + p t)
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    ⨅ b : {b : Set α // MeasurableSet b ∧ b ⊆ s ∪ t}, R b + p ((s ∪ t) \ b) =
      (⨅ b : {b : Set α // MeasurableSet b ∧ b ⊆ s}, R b + p (s \ b)) +
        ⨅ b : {b : Set α // MeasurableSet b ∧ b ⊆ t}, R b + p (t \ b) := by
  refine le_antisymm ?_ ?_
  · -- the union of a set below `s` and a set below `t`
    rw [ENNReal.iInf_add]
    refine le_iInf fun b ↦ ?_
    rw [ENNReal.add_iInf]
    refine le_iInf fun c ↦ ?_
    have hbc : Disjoint (b : Set α) c := hst.mono b.property.2 c.property.2
    have hset : (s ∪ t) \ (b ∪ c) = (s \ b) ∪ (t \ c) := by
      ext x
      have hsc : x ∈ s → x ∉ (c : Set α) := fun hx hxc ↦
        hst.notMem_of_mem_left hx (c.property.2 hxc)
      have htb : x ∈ t → x ∉ (b : Set α) := fun hx hxb ↦
        hst.notMem_of_mem_left (b.property.2 hxb) hx
      simp only [Set.mem_sdiff, mem_union]
      tauto
    refine (iInf_le _ ⟨b ∪ c, b.property.1.union c.property.1,
      union_subset_union b.property.2 c.property.2⟩).trans (le_of_eq ?_)
    rw [measure_union hbc c.property.1, hset,
      hpadd _ _ (hs.diff b.property.1) (ht.diff c.property.1)
        (hst.mono sdiff_subset sdiff_subset)]
    ring
  · -- the traces on `s` and on `t` of a set below `s ∪ t`
    refine le_iInf fun b ↦ ?_
    have h1 := iInf_le (fun c : {c : Set α // MeasurableSet c ∧ c ⊆ s} ↦ R c + p (s \ c))
      ⟨(b : Set α) ∩ s, b.property.1.inter hs, inter_subset_right⟩
    have h2 := iInf_le (fun c : {c : Set α // MeasurableSet c ∧ c ⊆ t} ↦ R c + p (t \ c))
      ⟨(b : Set α) ∩ t, b.property.1.inter ht, inter_subset_right⟩
    have hRb : R b = R ((b : Set α) ∩ s) + R ((b : Set α) ∩ t) := by
      conv_lhs => rw [← inter_eq_left.2 b.property.2, inter_union_distrib_left]
      exact measure_union (hst.mono inter_subset_right inter_subset_right)
        (b.property.1.inter ht)
    have hset : (s ∪ t) \ b = (s \ ((b : Set α) ∩ s)) ∪ (t \ ((b : Set α) ∩ t)) := by
      rw [sdiff_inter_self_eq_sdiff, sdiff_inter_self_eq_sdiff, union_sdiff_distrib]
    refine (add_le_add h1 h2).trans (le_of_eq ?_)
    rw [hset, hpadd _ _ (hs.diff (b.property.1.inter hs)) (ht.diff (b.property.1.inter ht))
      (hst.mono sdiff_subset sdiff_subset), hRb]
    ring

/-- **The purely finitely additive part is singular to every finite measure** [YH52]. For an
additive content `m` of finite mass on the measurable sets, a finite measure `R` and `ε > 0`, some
measurable set `E` has `R E + (m Eᶜ - countablyAdditivePart m Eᶜ) < ε`: the remainder
`m - countablyAdditivePart m` lives on sets of arbitrarily small `R`-measure. -/
theorem exists_measurableSet_add_sub_countablyAdditivePart_lt (hm : m univ ≠ ∞) (R : Measure α)
    [IsFiniteMeasure R] {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ E, MeasurableSet E ∧ R E + (m Eᶜ - countablyAdditivePart m Eᶜ) < ε := by
  -- the purely finitely additive part
  set p : Set α → ℝ≥0∞ := fun s ↦ m s - countablyAdditivePart m s with hp
  have hp0 : p ∅ = 0 := by simp [hp]
  -- the set function `A ↦ ⨅ B ⊆ A, R B + p (A \ B)`, below `R` and `p`
  set ρ : Set α → ℝ≥0∞ := fun s ↦
    ⨅ b : {b : Set α // MeasurableSet b ∧ b ⊆ s}, R b + p (s \ b) with hρ
  have hρR (s : Set α) (hs : MeasurableSet s) : ρ s ≤ R s :=
    (iInf_le _ ⟨s, hs, subset_rfl⟩).trans (by simp [hp0])
  have hρp (s : Set α) : ρ s ≤ p s :=
    (iInf_le _ ⟨∅, .empty, empty_subset s⟩).trans (by simp)
  have hρ0 : ρ ∅ = 0 := le_antisymm ((hρp ∅).trans hp0.le) bot_le
  -- it is an additive content dominated by `R`, hence a measure, below `p`, hence zero
  set ρc : AddContent ℝ≥0∞ {s : Set α | MeasurableSet s} :=
    isSetRing_measurableSet.addContent_of_union ρ hρ0 fun hs ht hst ↦
      iInf_add_sdiff_union R (fun _ _ ↦ sub_countablyAdditivePart_union hm) hs ht hst
  set ρm : Measure α := Measure.ofMeasurable (fun s _ ↦ ρ s) hρ0 fun f hf hd ↦
    addContent_iUnion_eq_tsum_of_le_measure (m := ρc) isSetRing_measurableSet R
      (fun _ h ↦ h.nullMeasurableSet) hρR hf (MeasurableSet.iUnion hf) hd
  have hρm0 : ρm = 0 :=
    countablyAdditivePart_eq_zero_iff.1
      (countablyAdditivePart_fun_sub_countablyAdditivePart_self_eq_zero hm) ρm
      fun s hs ↦ (Measure.ofMeasurable_apply s hs).trans_le (hρp s)
  have hlt : ρ univ < ε := by
    have h : ρm univ = ρ univ := Measure.ofMeasurable_apply univ .univ
    rwa [← h, hρm0, FunLike.coe_zero, Pi.zero_apply]
  obtain ⟨b, hb⟩ := iInf_lt_iff.1 hlt
  refine ⟨b, b.property.1, ?_⟩
  rwa [← compl_eq_univ_sdiff] at hb

end MeasureTheory
