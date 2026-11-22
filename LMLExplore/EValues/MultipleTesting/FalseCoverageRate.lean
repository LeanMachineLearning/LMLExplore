/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EVariable
public import LMLExplore.EValues.MultipleTesting.EClosure
public import LMLExplore.MeasureTheory.Integral.Lebesgue.Add

/-!
# E-confidence sets and the false coverage rate of the e-BY procedure

For a type `Θ` of parameters and a family of nulls `S : Θ → Set (Measure Ω)`, with `P ∈ S θ`
meaning that `θ` is a true parameter of `P`, a random set `C ω ⊆ Θ` is a confidence set at level
`α` when it misses each true parameter with probability at most `α` (`ProbabilityTheory.IsConfSet`).
For statistics `E θ`, the e-confidence set at level `α` is `{θ | E θ ω < α⁻¹}`
(`ProbabilityTheory.eConfSet`), and it is an e-confidence set (`ProbabilityTheory.IsEConfSet`)
when each `E θ` is an e-variable for `S θ` [RW, Definition 13.1]. By Markov's inequality an
e-confidence set is a confidence set; conversely, at every level `α ≠ ∞`, every confidence set is
the e-confidence set of the e-variables `α⁻¹ * 𝟙{θ ∉ C}`. A family of e-confidence sets indexed by
the level is level-free (`ProbabilityTheory.IsLevelFreeEConfSet`) when the same e-variables serve
at every level, `C α = eConfSet E α`; it is then antitone in the level.

For finitely many parameters `i : ι`, `K = Fintype.card ι`, each with its own type `Θ i` and its
own nulls `S i`, a scientist selects after seeing the data, by any rule, a set `R` of parameters
and reports a confidence set for each of them. The false coverage proportion
(`ProbabilityTheory.fcp`) is the proportion of the reported sets that miss the true parameters `θ`,
and its expectation is the false coverage rate. The e-BY procedure at level `δ`
(`ProbabilityTheory.eBY`) of [XWR24] reports for `i ∈ R` the confidence set of level
`δ * #R / K` [RW, Definition 13.6]. For level-free e-confidence sets it controls the false
coverage rate at `δ`, under arbitrary dependence and for every selection rule, and even post hoc:
the expected largest ratio of the false coverage proportion to `δ`, over all selections and all
levels, is at most one [RW, Theorem 13.7]. Under every measure `P`, the bound is
`(∑ i, ∫⁻ E i (θ i) ∂P) / K` for any statistics, so that it suffices that the expectations of the
statistics at the true parameters sum to at most `K`, as for compound e-values.
This is the analogue for selected confidence sets of the false discovery rate control of e-BH.

## Main definitions

* `ProbabilityTheory.IsConfSet C S α`: `C` is a confidence set at level `α` for the nulls `S`.
* `ProbabilityTheory.eConfSet E α ω`: the e-confidence set `{θ | E θ ω < α⁻¹}`.
* `ProbabilityTheory.IsEConfSet C S α`, `ProbabilityTheory.IsLevelFreeEConfSet C S`: `C` is an
  e-confidence set at level `α`, and a level-free family of e-confidence sets.
* `ProbabilityTheory.fcp C θ R`: the false coverage proportion of the sets `C i`, `i ∈ R`, at the
  true parameters `θ`.
* `ProbabilityTheory.eBY C δ R ω`: the confidence sets that the e-BY procedure reports at level `δ`
  for the selection `R`.

## Main statements

* `ProbabilityTheory.IsEConfSet.isConfSet`, `ProbabilityTheory.isEConfSet_iff_isConfSet`: an
  e-confidence set is a confidence set, and at a level `α ≠ ∞` every confidence set is an
  e-confidence set [RW, §13.1].
* `ProbabilityTheory.fcp_eBY_eConfSet_div_le`: pointwise, the false coverage proportion of e-BY
  divided by its level is at most the mean of the e-values at the true parameters.
* `ProbabilityTheory.lintegral_iSup_fcp_eBY_eConfSet_div_le`: the post-hoc bound
  `(∑ i, ∫⁻ E i (θ i) ∂P) / K` for any statistics.
* `ProbabilityTheory.lintegral_iSup_fcp_eBY_div_le_one`,
  `ProbabilityTheory.lintegral_fcp_eBY_le`: **false coverage rate control by e-BY** for level-free
  e-confidence sets, post hoc and at a fixed level [RW, Theorem 13.7].

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, Chapter 13.
* [XWR24] Z. Xu, R. Wang and A. Ramdas, *Post-selection inference for e-value based confidence
  intervals*, Electron. J. Statist. 18(1) (2024), 2292–2338.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Confidence sets and e-confidence sets -/

section ConfSet

variable {Θ : Type*} {S T : Θ → Set (Measure Ω)} {C D : Ω → Set Θ} {E : Θ → Ω → ℝ≥0∞}
  {α β : ℝ≥0∞} {θ : Θ} {ω : Ω}

/-- `C : Ω → Set Θ` is a **confidence set** at level `α` for the parameters of the nulls
`S : Θ → Set (Measure Ω)`: the event `{ω | θ ∈ C ω}` is measurable for every `θ`, and for every
parameter `θ` and every `P ∈ S θ` the probability that `C` misses `θ` is at most `α`
[RW, Definition 13.1]. -/
structure IsConfSet (C : Ω → Set Θ) (S : Θ → Set (Measure Ω)) (α : ℝ≥0∞) : Prop where
  measurableSet_mem : ∀ θ, MeasurableSet {ω | θ ∈ C ω}
  measure_notMem_le : ∀ θ, ∀ P ∈ S θ, P {ω | θ ∉ C ω} ≤ α

/-- A confidence set for the nulls `T` is one for all smaller nulls `S θ ⊆ T θ`. -/
theorem IsConfSet.anti_set (hST : ∀ θ, S θ ⊆ T θ) (hC : IsConfSet C T α) : IsConfSet C S α :=
  ⟨hC.measurableSet_mem, fun θ P hP ↦ hC.measure_notMem_le θ P (hST θ hP)⟩

/-- A confidence set at level `α` is one at every level `β ≥ α`. -/
theorem IsConfSet.mono_level (hC : IsConfSet C S α) (hαβ : α ≤ β) : IsConfSet C S β :=
  ⟨hC.measurableSet_mem, fun θ P hP ↦ (hC.measure_notMem_le θ P hP).trans hαβ⟩

/-- The **e-confidence set** at level `α` of statistics `E θ` indexed by the parameters: the
parameters `θ` whose e-value `E θ ω` is below `α⁻¹`, that is, the parameters that the e-test at
level `α` does not reject [RW, Definition 13.1]. It is the empty set at level `∞`, and at level
`0` the set of parameters with a finite e-value. -/
def eConfSet (E : Θ → Ω → ℝ≥0∞) (α : ℝ≥0∞) (ω : Ω) : Set Θ :=
  {θ | E θ ω < α⁻¹}

@[simp]
theorem mem_eConfSet : θ ∈ eConfSet E α ω ↔ E θ ω < α⁻¹ := Iff.rfl

theorem notMem_eConfSet : θ ∉ eConfSet E α ω ↔ α⁻¹ ≤ E θ ω := by
  rw [mem_eConfSet, not_lt]

@[simp]
theorem eConfSet_top : eConfSet E ∞ ω = ∅ := by
  ext θ
  simp

/-- The e-confidence sets shrink as the level grows. -/
theorem eConfSet_anti (E : Θ → Ω → ℝ≥0∞) (ω : Ω) : Antitone fun α ↦ eConfSet E α ω :=
  fun _ _ hαβ _ hθ ↦ (mem_eConfSet.1 hθ).trans_le (ENNReal.inv_le_inv.2 hαβ)

theorem measurableSet_mem_eConfSet (hE : Measurable (E θ)) (α : ℝ≥0∞) :
    MeasurableSet {ω | θ ∈ eConfSet E α ω} :=
  measurableSet_lt hE measurable_const

/-- `C` is an **e-confidence set** at level `α` for the nulls `S` when it is the e-confidence set
`eConfSet E α` of a family of e-variables `E θ` for the nulls `S θ` [RW, Definition 13.1]. -/
def IsEConfSet (C : Ω → Set Θ) (S : Θ → Set (Measure Ω)) (α : ℝ≥0∞) : Prop :=
  ∃ E : Θ → Ω → ℝ≥0∞, (∀ θ, IsEVar (E θ) (S θ)) ∧ C = eConfSet E α

theorem isEConfSet_iff :
    IsEConfSet C S α ↔ ∃ E : Θ → Ω → ℝ≥0∞, (∀ θ, IsEVar (E θ) (S θ)) ∧ C = eConfSet E α :=
  Iff.rfl

theorem isEConfSet_eConfSet (hE : ∀ θ, IsEVar (E θ) (S θ)) (α : ℝ≥0∞) :
    IsEConfSet (eConfSet E α) S α :=
  ⟨E, hE, rfl⟩

/-- **E-confidence sets are confidence sets**, by Markov's inequality for e-variables
[RW, §13.1]. -/
theorem IsEConfSet.isConfSet (hC : IsEConfSet C S α) : IsConfSet C S α := by
  obtain ⟨E, hE, rfl⟩ := hC
  refine ⟨fun θ ↦ measurableSet_mem_eConfSet (hE θ).measurable α, fun θ P hP ↦ ?_⟩
  simpa only [notMem_eConfSet] using (hE θ).measure_inv_le_le hP α

/-- **Confidence sets are e-confidence sets** [RW, §13.1]: at a level `α ≠ ∞`, a confidence set
`C` is the e-confidence set of the e-variables `α⁻¹ * 𝟙{θ ∉ C}`, so that the two notions agree.
At level `∞` every random set with measurable events `{θ ∈ C}` is a confidence set, while the
only e-confidence set is empty. -/
theorem isEConfSet_iff_isConfSet (hα : α ≠ ∞) : IsEConfSet C S α ↔ IsConfSet C S α := by
  refine ⟨IsEConfSet.isConfSet, fun hC ↦ ?_⟩
  have hs (θ : Θ) : MeasurableSet {ω | θ ∉ C ω} := (hC.measurableSet_mem θ).compl
  refine ⟨fun θ ↦ {ω | θ ∉ C ω}.indicator fun _ ↦ α⁻¹, fun θ ↦ ⟨?_, fun P hP ↦ ?_⟩, ?_⟩
  · exact measurable_const.indicator (hs θ)
  · dsimp only
    rw [lintegral_indicator_const (hs θ)]
    calc α⁻¹ * P {ω | θ ∉ C ω} ≤ α⁻¹ * α := by gcongr; exact hC.measure_notMem_le θ P hP
      _ ≤ 1 := ENNReal.inv_mul_le_one α
  · ext ω θ
    by_cases hθ : θ ∈ C ω
    · simpa [hθ] using hα
    · simp [hθ]

/-- A family `C : ℝ≥0∞ → Ω → Set Θ` of e-confidence sets indexed by the level is **level-free**
for the nulls `S` when it is `eConfSet E` for a single family of e-variables `E θ` for the nulls
`S θ`, which does not depend on the level [RW, Definition 13.1]. -/
def IsLevelFreeEConfSet (C : ℝ≥0∞ → Ω → Set Θ) (S : Θ → Set (Measure Ω)) : Prop :=
  ∃ E : Θ → Ω → ℝ≥0∞, (∀ θ, IsEVar (E θ) (S θ)) ∧ C = eConfSet E

theorem isLevelFreeEConfSet_iff {C : ℝ≥0∞ → Ω → Set Θ} :
    IsLevelFreeEConfSet C S ↔ ∃ E : Θ → Ω → ℝ≥0∞, (∀ θ, IsEVar (E θ) (S θ)) ∧ C = eConfSet E :=
  Iff.rfl

theorem isLevelFreeEConfSet_eConfSet (hE : ∀ θ, IsEVar (E θ) (S θ)) :
    IsLevelFreeEConfSet (eConfSet E) S :=
  ⟨E, hE, rfl⟩

/-- The members of a level-free family of e-confidence sets are e-confidence sets. -/
theorem IsLevelFreeEConfSet.isEConfSet {C : ℝ≥0∞ → Ω → Set Θ} (hC : IsLevelFreeEConfSet C S)
    (α : ℝ≥0∞) : IsEConfSet (C α) S α := by
  obtain ⟨E, hE, rfl⟩ := hC
  exact isEConfSet_eConfSet hE α

/-- A level-free family of e-confidence sets shrinks as the level grows. -/
theorem IsLevelFreeEConfSet.antitone {C : ℝ≥0∞ → Ω → Set Θ} (hC : IsLevelFreeEConfSet C S)
    (ω : Ω) : Antitone fun α ↦ C α ω := by
  obtain ⟨E, -, rfl⟩ := hC
  exact eConfSet_anti E ω

end ConfSet

/-! ### The false coverage proportion and the e-BY procedure -/

section EBY

variable {ι : Type*} [Fintype ι] {Θ : ι → Type*}

/-- **The e-BY procedure** at level `δ` [XWR24; RW, Definition 13.6]: for the selected set `R` of
parameters, it reports for each parameter the set of the family `C i` at the level
`δ * #R / K`, with `K` the number of parameters. Only the sets of the selected parameters enter
the false coverage proportion. -/
noncomputable def eBY (C : ∀ i, ℝ≥0∞ → Ω → Set (Θ i)) (δ : ℝ≥0∞) (R : Finset ι) (ω : Ω) :
    ∀ i, Set (Θ i) :=
  fun i ↦ C i (δ * #R / Fintype.card ι) ω

@[simp]
theorem eBY_apply (C : ∀ i, ℝ≥0∞ → Ω → Set (Θ i)) (δ : ℝ≥0∞) (R : Finset ι) (ω : Ω) (i : ι) :
    eBY C δ R ω i = C i (δ * #R / Fintype.card ι) ω := (rfl)

variable [DecidableEq ι]

/-- The **false coverage proportion** [RW, §13.2] of the sets `C i ⊆ Θ i` reported for the
selected parameters `i ∈ R`, when the true parameters are `θ i`: the proportion of the selected
`i` with `θ i ∉ C i`, and `0` for the empty selection. It is the false discovery proportion of `R`
when the true nulls are the parameters whose sets miss them. -/
noncomputable def fcp (C : ∀ i, Set (Θ i)) (θ : ∀ i, Θ i) (R : Finset ι) : ℝ≥0∞ :=
  fdp (Set.toFinite {i | θ i ∉ C i}).toFinset R

theorem fcp_def (C : ∀ i, Set (Θ i)) (θ : ∀ i, Θ i) (R : Finset ι) :
    fcp C θ R = fdp (Set.toFinite {i | θ i ∉ C i}).toFinset R := (rfl)

@[simp]
theorem fcp_empty (C : ∀ i, Set (Θ i)) (θ : ∀ i, Θ i) : fcp C θ ∅ = 0 :=
  fdp_empty_right _

/-- The false coverage proportion is at most one. -/
theorem fcp_le_one (C : ∀ i, Set (Θ i)) (θ : ∀ i, Θ i) (R : Finset ι) : fcp C θ R ≤ 1 :=
  fdp_le_one _ _

/-- **The false coverage proportion of e-BY, pointwise.** For statistics `E i` and true
parameters `θ`, the false coverage proportion of the e-confidence sets reported by e-BY at level
`δ` for the selection `R`, divided by `δ`, is at most `∑ i ∈ R, E i (θ i) ω / K`. A missed
parameter `i ∈ R` has `K / (δ * #R) ≤ E i (θ i) ω`, so its contribution `1 / #R` to the
proportion is at most `δ * E i (θ i) ω / K`. The bound holds at every level, `0` and `∞`
included. -/
theorem fcp_eBY_eConfSet_div_le (E : ∀ i, Θ i → Ω → ℝ≥0∞) (θ : ∀ i, Θ i) (δ : ℝ≥0∞)
    (R : Finset ι) (ω : Ω) :
    fcp (eBY (fun i ↦ eConfSet (E i)) δ R ω) θ R / δ ≤
      ∑ i ∈ R, E i (θ i) ω / Fintype.card ι := by
  rcases R.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
  · simp
  set N := (Set.toFinite {i | θ i ∉ eBY (fun i ↦ eConfSet (E i)) δ R ω i}).toFinset
  have hK : (Fintype.card ι : ℝ≥0∞) ≠ 0 :=
    haveI : Nonempty ι := ⟨j⟩
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hR : (#R : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (card_ne_zero_of_mem hj)
  -- Each missed parameter contributes `1 / (#R * δ)`, at most its e-value over `K`.
  have hi : ∀ i ∈ N, (#R : ℝ≥0∞)⁻¹ / δ ≤ E i (θ i) ω / Fintype.card ι := by
    intro i hi
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, eBY_apply, notMem_eConfSet,
      ENNReal.inv_div (Or.inl (ENNReal.natCast_ne_top _)) (Or.inl hK)] at hi
    rw [ENNReal.le_div_iff_mul_le (Or.inl hK) (Or.inl (ENNReal.natCast_ne_top _))]
    refine le_of_eq_of_le ?_ hi
    rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inr hR)]
    ring
  calc fcp (eBY (fun i ↦ eConfSet (E i)) δ R ω) θ R / δ
      = ∑ _ ∈ R ∩ N, (#R : ℝ≥0∞)⁻¹ / δ := by
        rw [fcp_def, fdp_def, max_eq_left (Nat.one_le_cast.2 (card_pos.2 ⟨j, hj⟩)), sum_const,
          nsmul_eq_mul, div_eq_mul_inv (b := δ), div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
    _ ≤ ∑ i ∈ R ∩ N, E i (θ i) ω / Fintype.card ι :=
        sum_le_sum fun i hi' ↦ hi i (mem_inter.1 hi').2
    _ ≤ ∑ i ∈ R, E i (θ i) ω / Fintype.card ι := sum_le_sum_of_subset inter_subset_left

/-- **Post-hoc false coverage rate of e-BY for any statistics.** For statistics `E i` and true
parameters `θ` such that each `E i (θ i)` is almost everywhere measurable for a measure `P`, the
expected largest ratio of the false coverage proportion of the e-confidence sets reported by e-BY
to its level, over all selections and all levels, is at most `(∑ i, ∫⁻ E i (θ i) ∂P) / K`. -/
theorem lintegral_iSup_fcp_eBY_eConfSet_div_le {E : ∀ i, Θ i → Ω → ℝ≥0∞} {θ : ∀ i, Θ i}
    {P : Measure Ω} (hE : ∀ i, AEMeasurable (E i (θ i)) P) :
    ∫⁻ ω, ⨆ (R : Finset ι) (δ : ℝ≥0∞), fcp (eBY (fun i ↦ eConfSet (E i)) δ R ω) θ R / δ ∂P ≤
      (∑ i, ∫⁻ ω, E i (θ i) ω ∂P) / Fintype.card ι :=
  (lintegral_mono fun ω ↦ iSup₂_le fun R δ ↦ (fcp_eBY_eConfSet_div_le E θ δ R ω).trans
    (sum_le_sum_of_subset (subset_univ R))).trans_eq (lintegral_finsetSum_div (fun i _ ↦ hE i) _)

variable {C : ∀ i, ℝ≥0∞ → Ω → Set (Θ i)} {S : ∀ i, Θ i → Set (Measure Ω)} {θ : ∀ i, Θ i}
  {P : Measure Ω}

/-- **Post-hoc false coverage rate control by e-BY** [XWR24; RW, Theorem 13.7]: for level-free
families of e-confidence sets `C i` for the nulls `S i`, and a measure `P` of which every `θ i`
is a true parameter, the expected largest ratio of the false coverage proportion of e-BY to its
level, over all selections `R` and all levels `δ`, is at most one. This holds under arbitrary
dependence between the e-variables, and it covers every selection rule and every level chosen
after seeing the data. -/
theorem lintegral_iSup_fcp_eBY_div_le_one (hC : ∀ i, IsLevelFreeEConfSet (C i) (S i))
    (hP : ∀ i, P ∈ S i (θ i)) :
    ∫⁻ ω, ⨆ (R : Finset ι) (δ : ℝ≥0∞), fcp (eBY C δ R ω) θ R / δ ∂P ≤ 1 := by
  choose E hE hCE using hC
  obtain rfl : C = fun i ↦ eConfSet (E i) := funext hCE
  -- the mean of the `K` expectations, each at most one, is at most one
  exact (lintegral_iSup_fcp_eBY_eConfSet_div_le fun i ↦ (hE i (θ i)).measurable.aemeasurable).trans
    (ENNReal.div_le_of_le_mul ((sum_le_sum fun i _ ↦ (hE i (θ i)).lintegral_le_one (hP i)).trans_eq
      (by simp)))

/-- **False coverage rate control by e-BY** [XWR24; RW, Theorem 13.7]: for level-free families of
e-confidence sets `C i` for the nulls `S i`, a measure `P` of which every `θ i` is a true
parameter, any selection rule `R : Ω → Finset ι` and any level `δ`, the false coverage rate of
the e-confidence sets reported by e-BY is at most `δ`. This holds under arbitrary dependence
between the e-variables, with no condition on the selection rule. -/
theorem lintegral_fcp_eBY_le (hC : ∀ i, IsLevelFreeEConfSet (C i) (S i)) (hP : ∀ i, P ∈ S i (θ i))
    (R : Ω → Finset ι) (δ : ℝ≥0∞) :
    ∫⁻ ω, fcp (eBY C δ (R ω) ω) θ (R ω) ∂P ≤ δ := by
  rcases eq_or_ne δ ∞ with rfl | hδ
  · exact le_top
  choose E hE hCE using hC
  obtain rfl : C = fun i ↦ eConfSet (E i) := funext hCE
  -- Almost surely every e-value is finite, so the pointwise bound can be multiplied by `δ`.
  have hfin : ∀ᵐ ω ∂P, ∀ i, E i (θ i) ω < ∞ := ae_all_iff.2 fun i ↦ (hE i (θ i)).ae_lt_top (hP i)
  have hle : ∀ᵐ ω ∂P, fcp (eBY (fun i ↦ eConfSet (E i)) δ (R ω) ω) θ (R ω) ≤
      δ * ∑ i, E i (θ i) ω / Fintype.card ι := by
    filter_upwards [hfin] with ω hω
    set x := fcp (eBY (fun i ↦ eConfSet (E i)) δ (R ω) ω) θ (R ω)
    have hx : x / δ ≤ ∑ i, E i (θ i) ω / Fintype.card ι :=
      (fcp_eBY_eConfSet_div_le E θ δ (R ω) ω).trans (sum_le_sum_of_subset (subset_univ _))
    rcases eq_or_ne δ 0 with rfl | hδ₀
    · -- at level `0` a missed parameter has an infinite e-value, so nothing is missed
      have hsum : ∑ i, E i (θ i) ω / Fintype.card ι ≠ ∞ :=
        ENNReal.sum_ne_top.2 fun i _ ↦ ENNReal.div_ne_top (hω i).ne (by
          have : Nonempty ι := ⟨i⟩
          exact Nat.cast_ne_zero.2 Fintype.card_ne_zero)
      by_contra hx₀
      exact hsum (eq_top_mono hx (ENNReal.div_zero (fun h ↦ hx₀ (by simp [h]))))
    · calc x = δ * (x / δ) := (ENNReal.mul_div_cancel hδ₀ hδ).symm
        _ ≤ δ * ∑ i, E i (θ i) ω / Fintype.card ι := by gcongr
  have hE' : ∀ i, AEMeasurable (E i (θ i)) P := fun i ↦ (hE i (θ i)).measurable.aemeasurable
  calc ∫⁻ ω, fcp (eBY (fun i ↦ eConfSet (E i)) δ (R ω) ω) θ (R ω) ∂P
      ≤ ∫⁻ ω, δ * ∑ i, E i (θ i) ω / Fintype.card ι ∂P := lintegral_mono_ae hle
    _ = δ * ((∑ i, ∫⁻ ω, E i (θ i) ω ∂P) / Fintype.card ι) := by
        rw [lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum _ fun i _ ↦ (hE' i).div_const _),
          lintegral_finsetSum_div fun i _ ↦ hE' i]
    _ ≤ δ * 1 := by
        gcongr
        exact ENNReal.div_le_of_le_mul
          ((sum_le_sum fun i _ ↦ (hE i (θ i)).lintegral_le_one (hP i)).trans_eq (by simp))
    _ = δ := mul_one δ

end EBY

end ProbabilityTheory
