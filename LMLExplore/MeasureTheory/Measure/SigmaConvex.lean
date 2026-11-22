/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Measure.Sum

/-!
# σ-convex sets of measures

A set of measures is σ-convex if it contains the countable mixtures `∑ n, w n • Qs n` of its
members, for weights `w n` of sum `1`. It is then convex. σ-convexity is the closure property
under which the description gain of Lardy, Grünwald and Harremoës over a set of measures does not
change when the set is replaced by its closure in total variation; the effective null of a null
hypothesis is σ-convex.

## Main definitions

* `MeasureTheory.IsSigmaConvex 𝒞`: `𝒞` contains the countable mixtures of its members.

## Main statements

* `MeasureTheory.isSigmaConvex_iff`, `MeasureTheory.IsSigmaConvex.sum_smul_mem`: the definition,
  and the mixtures it contains.
* `MeasureTheory.IsSigmaConvex.convex`: a σ-convex set is convex.

## References

* [LGH24] T. Lardy, P. Grünwald, P. Harremoës, *Reverse information projections and optimal
  e-statistics*, IEEE Trans. Inform. Theory 70 (2024), arXiv:2306.16646.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A set of measures is σ-convex if it contains the countable mixtures `∑ n, w n • Qs n` of its
members, for weights `w n` of sum `1`. -/
def IsSigmaConvex (𝒞 : Set (Measure Ω)) : Prop :=
  ∀ ⦃w : ℕ → ℝ≥0∞⦄ ⦃Qs : ℕ → Measure Ω⦄, ∑' n, w n = 1 → (∀ n, Qs n ∈ 𝒞) →
    Measure.sum (fun n ↦ w n • Qs n) ∈ 𝒞

/-- The definition of σ-convexity, for introduction. -/
theorem isSigmaConvex_iff {𝒞 : Set (Measure Ω)} :
    IsSigmaConvex 𝒞 ↔ ∀ ⦃w : ℕ → ℝ≥0∞⦄ ⦃Qs : ℕ → Measure Ω⦄, ∑' n, w n = 1 → (∀ n, Qs n ∈ 𝒞) →
      Measure.sum (fun n ↦ w n • Qs n) ∈ 𝒞 :=
  Iff.rfl

/-- A σ-convex set contains the countable mixtures of its members. -/
theorem IsSigmaConvex.sum_smul_mem {𝒞 : Set (Measure Ω)} (h𝒞 : IsSigmaConvex 𝒞)
    {w : ℕ → ℝ≥0∞} {Qs : ℕ → Measure Ω} (hw : ∑' n, w n = 1) (hQs : ∀ n, Qs n ∈ 𝒞) :
    Measure.sum (fun n ↦ w n • Qs n) ∈ 𝒞 :=
  h𝒞 hw hQs

/-- A σ-convex set contains the mixtures of two of its members: it is convex. -/
theorem IsSigmaConvex.convex {𝒞 : Set (Measure Ω)} (h𝒞 : IsSigmaConvex 𝒞) :
    Convex ℝ≥0∞ 𝒞 := by
  intro ν₁ h₁ ν₂ h₂ a b _ _ hab
  have hsum (f : ℕ → ℝ≥0∞) :
      ∑' n, (if n = 0 then a else if n = 1 then b else 0) * f n = a * f 0 + b * f 1 := by
    rw [tsum_eq_sum (s := {0, 1}) fun n hn ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      simp [hn.1, hn.2]]
    simp
  have h := h𝒞.sum_smul_mem (w := fun n ↦ if n = 0 then a else if n = 1 then b else 0)
    (Qs := fun n ↦ if n = 0 then ν₁ else ν₂) (by simpa [hab] using hsum 1)
    (fun n ↦ by split_ifs <;> assumption)
  convert h using 1
  ext t ht
  rw [Measure.sum_apply _ ht]
  simp only [smul_apply, smul_eq_mul]
  rw [hsum (fun n ↦ (if n = 0 then ν₁ else ν₂) t)]
  simp

end MeasureTheory
