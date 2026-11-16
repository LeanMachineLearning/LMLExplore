/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.TestSupermartingale
import LMLExplore.MeasureTheory.MeasurableSpace.Constructions
import LMLExplore.MeasureTheory.Measure.Weighted

/-!
# Doob martingales on a finite space

On a finite space `Ω` with weights `w : Ω → ℝ≥0∞`, the conditional expectation of a function `Z`
given the value of a map `f : Ω → β` is its `w`-weighted average over the fiber of `f`. For maps
`info t` that refine as `t` increases, these fiber averages are the Doob martingale of `Z` for
the filtration of the information `info t`, so they form a test martingale for the weighted sum
of Dirac masses as soon as the weighted sum of `Z` is at most `1`. This gives test martingales
with any prescribed terminal value of expectation at most `1` on a finite space, as in the
lower bound for e-BH on running maxima
(`LMLExplore.EValues.MultipleTesting.RunningMaxima.LowerBound`).

## Main definitions

* `ProbabilityTheory.fiberAvg w f Z y`: the `w`-weighted average of `Z` over the fiber
  `f ⁻¹' {y}`, `0` on a fiber of weight `0`.
* `ProbabilityTheory.fiberFiltration info hinfo`: the filtration of a countable space whose
  σ-algebra at time `t` is `MeasurableSpace.comap (info t) ⊤`, for maps `info t` that refine as
  `t` increases.

## Main statements

* `ProbabilityTheory.sum_mul_fiberAvg`: on a union of fibers, the weighted sums of `Z` and of its
  fiber averages agree.
* `ProbabilityTheory.measurableSet_fiberFiltration_iff`: the measurable sets at time `t` are the
  unions of fibers of `info t`.
* `ProbabilityTheory.isTestMartingale_fiberAvg`: the fiber averages of `Z` form a test martingale
  for the filtration of the information.

## Implementation notes

The construction is adapted from the Doob-martingale step of the Lean proof in
`EValuesResearch/Results/RunningMaximaAux.lean` (commit `ffba78a`) of the paper project
`RemyDegenne/evalues_research`.
-/

public section

open MeasureTheory MeasurableSpace LMLExplore
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω β : Type*}

section FiberAvg

variable [Fintype Ω] [DecidableEq β]

/-- The `w`-weighted average of `Z` over the fiber `f ⁻¹' {y}` of a finite space; it is `0` on
a fiber of weight `0`. -/
noncomputable def fiberAvg (w : Ω → ℝ≥0∞) (f : Ω → β) (Z : Ω → ℝ≥0∞) (y : β) : ℝ≥0∞ :=
  (∑ ω, if f ω = y then w ω * Z ω else 0) / ∑ ω, if f ω = y then w ω else 0

/-- The fiber average is the weighted sum of `Z` over the fiber divided by its weight. -/
lemma fiberAvg_def (w : Ω → ℝ≥0∞) (f : Ω → β) (Z : Ω → ℝ≥0∞) (y : β) :
    fiberAvg w f Z y =
      (∑ ω, if f ω = y then w ω * Z ω else 0) / ∑ ω, if f ω = y then w ω else 0 := by
  rw [fiberAvg]

/-- The fiber average over a fiber of weight `0` is `0`. -/
lemma fiberAvg_eq_zero_of_sum_eq_zero {w : Ω → ℝ≥0∞} {f : Ω → β} (Z : Ω → ℝ≥0∞) {y : β}
    (h : ∑ ω, (if f ω = y then w ω else 0) = 0) : fiberAvg w f Z y = 0 := by
  rw [fiberAvg_def, ENNReal.div_eq_zero_iff]
  refine Or.inl (Finset.sum_eq_zero fun ω _ ↦ ?_)
  have hω := (Finset.sum_eq_zero_iff.1 h) ω (Finset.mem_univ ω)
  split_ifs at hω ⊢ with hf
  · simp [hω]
  · rfl

/-- On a union of fibers of `f`, the weighted sums of `Z` and of its fiber averages agree. -/
theorem sum_mul_fiberAvg {w : Ω → ℝ≥0∞} (hw : ∀ ω, w ω ≠ ⊤) (f : Ω → β) (Z : Ω → ℝ≥0∞)
    (s : Set Ω) [DecidablePred (· ∈ s)] (hs : ∀ ω ω', f ω = f ω' → (ω ∈ s ↔ ω' ∈ s)) :
    ∑ ω, (if ω ∈ s then w ω * fiberAvg w f Z (f ω) else 0) =
      ∑ ω, if ω ∈ s then w ω * Z ω else 0 := by
  set W : β → ℝ≥0∞ := fun y ↦ ∑ ω, if f ω = y then w ω else 0 with hW_def
  have hW (ω : Ω) : w ω ≤ W (f ω) := by
    have := Finset.single_le_sum (s := Finset.univ)
      (f := fun ω' ↦ (if f ω' = f ω then w ω' else 0 : ℝ≥0∞)) (fun _ _ ↦ zero_le)
      (Finset.mem_univ ω)
    simpa using this
  have hWtop (y : β) : W y ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun ω _ ↦ by split_ifs <;> simp [hw]
  calc ∑ ω, (if ω ∈ s then w ω * fiberAvg w f Z (f ω) else 0)
      = ∑ ω, ∑ ω', if ω ∈ s ∧ f ω' = f ω then w ω * (w ω' * Z ω') * (W (f ω'))⁻¹ else 0 := by
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        by_cases h : ω ∈ s
        · simp only [h, ite_true, true_and, fiberAvg, div_eq_mul_inv, Finset.sum_mul,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun ω' _ ↦ ?_
          by_cases h' : f ω' = f ω
          · simp [h', W, mul_assoc]
          · simp [h']
        · simp [h]
    _ = ∑ ω', ∑ ω, if ω ∈ s ∧ f ω' = f ω then w ω * (w ω' * Z ω') * (W (f ω'))⁻¹ else 0 :=
        Finset.sum_comm
    _ = ∑ ω', if ω' ∈ s then w ω' * Z ω' * (W (f ω') * (W (f ω'))⁻¹) else 0 := by
        refine Finset.sum_congr rfl fun ω' _ ↦ ?_
        by_cases h : ω' ∈ s
        · simp only [h, ite_true]
          rw [hW_def]
          simp only [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun ω _ ↦ ?_
          by_cases h' : f ω' = f ω
          · simp [(hs ω ω' h'.symm).2 h, h', mul_left_comm, mul_assoc]
          · simp [h', Ne.symm h']
        · simp only [h, ite_false]
          refine Finset.sum_eq_zero fun ω _ ↦ ?_
          by_cases h' : f ω' = f ω
          · simp [show ω ∉ s from fun hω ↦ h ((hs ω ω' h'.symm).1 hω)]
          · simp [h']
    _ = ∑ ω', if ω' ∈ s then w ω' * Z ω' else 0 := by
        refine Finset.sum_congr rfl fun ω' _ ↦ ?_
        split_ifs
        · rcases eq_or_ne (W (f ω')) 0 with h0 | h0
          · have : w ω' = 0 := le_antisymm ((hW ω').trans h0.le) zero_le
            simp [this]
          · rw [ENNReal.mul_inv_cancel h0 (hWtop _), mul_one]
        · rfl

end FiberAvg

variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The filtration of the information `info t`, for maps `info t` of a countable space that refine
as `t` increases: at time `t`, the σ-algebra `MeasurableSpace.comap (info t) ⊤`. -/
def fiberFiltration [Countable Ω] (info : ℕ → Ω → β)
    (hinfo : ∀ t ω ω', info (t + 1) ω = info (t + 1) ω' → info t ω = info t ω') :
    Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq t := MeasurableSpace.comap (info t) ⊤
  mono' := monotone_nat_of_le_succ fun t _ hs ↦ measurableSet_comap_top_iff.2 fun ω ω' h ↦
    measurableSet_comap_top_iff.1 hs ω ω' (hinfo t ω ω' h)
  le' _ s _ := s.to_countable.measurableSet

/-- The measurable sets of the filtration of the information at time `t` are the unions of fibers
of `info t`. -/
lemma measurableSet_fiberFiltration_iff [Countable Ω] {info : ℕ → Ω → β}
    {hinfo : ∀ t ω ω', info (t + 1) ω = info (t + 1) ω' → info t ω = info t ω'} {t : ℕ}
    {s : Set Ω} :
    MeasurableSet[fiberFiltration info hinfo t] s ↔
      ∀ ω ω', info t ω = info t ω' → (ω ∈ s ↔ ω' ∈ s) :=
  measurableSet_comap_top_iff

/-- **Doob martingales on a finite space.** The fiber averages of `Z` given refining
maps `info t` form a test martingale for the weighted sum of Dirac masses, as soon as the
weighted sum of `Z` is at most `1`. -/
theorem isTestMartingale_fiberAvg [Fintype Ω] [DecidableEq β] {w : Ω → ℝ≥0∞}
    (hw : ∀ ω, w ω ≠ ⊤) (info : ℕ → Ω → β)
    (hinfo : ∀ t ω ω', info (t + 1) ω = info (t + 1) ω' → info t ω = info t ω')
    (Z : Ω → ℝ≥0∞) (hZ : ∑ ω, w ω * Z ω ≤ 1) :
    IsTestMartingale (fun t ω ↦ fiberAvg w (info t) Z (info t ω)) (fiberFiltration info hinfo)
      {∑ ω, w ω • Measure.dirac ω} := by
  classical
  have key (t : ℕ) (s : Set Ω) (hs : ∀ ω ω', info t ω = info t ω' → (ω ∈ s ↔ ω' ∈ s)) :
      ∫⁻ ω in s, fiberAvg w (info t) Z (info t ω) ∂(∑ ω, w ω • Measure.dirac ω) =
        ∫⁻ ω in s, Z ω ∂(∑ ω, w ω • Measure.dirac ω) := by
    rw [setLIntegral_sum_smul_dirac, setLIntegral_sum_smul_dirac]
    exact sum_mul_fiberAvg hw (info t) Z s hs
  refine ⟨fun t U _ ↦ measurableSet_fiberFiltration_iff.2 fun ω ω' h ↦ by simp [h], ?_, ?_⟩
  · rintro P rfl
    rw [← setLIntegral_univ, key 0 Set.univ (by simp), setLIntegral_sum_smul_dirac]
    simpa using hZ
  · rintro P rfl t s hs
    have hs' := measurableSet_fiberFiltration_iff.1 hs
    rw [key t s hs', key (t + 1) s fun ω ω' h ↦ hs' ω ω' (hinfo t ω ω' h)]

end ProbabilityTheory
