/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.PVariable

/-!
# Confidence sets and e-confidence sets

For a type `Θ` of parameters and a family of nulls `S : Θ → Set (Measure Ω)`, with `P ∈ S θ`
meaning that `θ` is a true parameter of `P`, a random set `C ω ⊆ Θ` is a confidence set at level
`α` when it misses each true parameter with probability at most `α` (`ProbabilityTheory.IsConfSet`).
For statistics `E θ`, the e-confidence set at level `α` is `{θ | E θ ω < α⁻¹}`
(`ProbabilityTheory.eConfSet`), and it is an e-confidence set (`ProbabilityTheory.IsEConfSet`)
when each `E θ` is an e-variable for `S θ` [RW, Definition 13.1]. By Markov's inequality an
e-confidence set is a confidence set; conversely, at every level `α ≠ ∞`, every confidence set is
the e-confidence set of the e-variables `𝟙{θ ∉ C} / α`. A family of e-confidence sets indexed by
the level is level-free (`ProbabilityTheory.IsLevelFreeEConfSet`) when the same e-variables serve
at every level, `C α = eConfSet E α`; it is then antitone in the level.

These are the fixed-time counterparts of the confidence sequences of
`LMLExplore.EValues.ConfidenceSequence`.

## Main definitions

* `ProbabilityTheory.IsConfSet C S α`: `C` is a confidence set at level `α` for the nulls `S`.
* `ProbabilityTheory.eConfSet E α ω`: the e-confidence set `{θ | E θ ω < α⁻¹}`.
* `ProbabilityTheory.IsEConfSet C S α`, `ProbabilityTheory.IsLevelFreeEConfSet C S`: `C` is an
  e-confidence set at level `α`, and a level-free family of e-confidence sets.

## Main statements

* `ProbabilityTheory.IsEConfSet.isConfSet`, `ProbabilityTheory.isEConfSet_iff_isConfSet`: an
  e-confidence set is a confidence set, and at a level `α ≠ ∞` every confidence set is an
  e-confidence set [RW, §13.1].

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, Chapter 13.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

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
`C` is the e-confidence set of the e-variables `𝟙{θ ∉ C} / α`, so that the two notions agree.
At level `∞` every random set with measurable events `{θ ∈ C}` is a confidence set, while the
only e-confidence set is empty. -/
theorem isEConfSet_iff_isConfSet (hα : α ≠ ∞) : IsEConfSet C S α ↔ IsConfSet C S α := by
  refine ⟨IsEConfSet.isConfSet, fun hC ↦ ⟨fun θ ω ↦ {ω | θ ∉ C ω}.indicator 1 ω / α,
    fun θ ↦ (isTest_indicator_iff.2 ⟨(hC.measurableSet_mem θ).compl,
      hC.measure_notMem_le θ⟩).isEVar_div, ?_⟩⟩
  -- `𝟙{θ ∉ C} / α` is `0 < α⁻¹` on `C` and `1 / α = α⁻¹` off it, since `α ≠ ∞`
  ext ω θ
  by_cases h : θ ∈ C ω <;> simp [h, hα]

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

end ProbabilityTheory
