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
* `MeasureTheory.sigmaConvexHull 𝒞`: the set of countable mixtures of members of `𝒞`.

## Main statements

* `MeasureTheory.isSigmaConvex_iff`, `MeasureTheory.IsSigmaConvex.sum_smul_mem`: the definition,
  and the mixtures it contains.
* `MeasureTheory.IsSigmaConvex.convex`: a σ-convex set is convex.
* `MeasureTheory.isSigmaConvex_sigmaConvexHull`,
  `MeasureTheory.IsSigmaConvex.sigmaConvexHull_subset`: the countable mixtures of members of `𝒞`
  form the smallest σ-convex set that contains `𝒞`.

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

/-! ### The σ-convex hull -/

/-- The **σ-convex hull** of a set `𝒞` of measures: the countable mixtures `∑ n, w n • Qs n` of
members `Qs n` of `𝒞`, for weights `w n` of sum `1`. It is the smallest σ-convex set that contains
`𝒞` (`MeasureTheory.isSigmaConvex_sigmaConvexHull`,
`MeasureTheory.IsSigmaConvex.sigmaConvexHull_subset`). -/
def sigmaConvexHull (𝒞 : Set (Measure Ω)) : Set (Measure Ω) :=
  {ν | ∃ w : ℕ → ℝ≥0∞, ∃ Qs : ℕ → Measure Ω, ∑' n, w n = 1 ∧ (∀ n, Qs n ∈ 𝒞) ∧
    ν = Measure.sum fun n ↦ w n • Qs n}

theorem mem_sigmaConvexHull_iff {𝒞 : Set (Measure Ω)} {ν : Measure Ω} :
    ν ∈ sigmaConvexHull 𝒞 ↔ ∃ w : ℕ → ℝ≥0∞, ∃ Qs : ℕ → Measure Ω, ∑' n, w n = 1 ∧
      (∀ n, Qs n ∈ 𝒞) ∧ ν = Measure.sum fun n ↦ w n • Qs n :=
  Iff.rfl

/-- A set of measures is contained in its σ-convex hull. -/
theorem subset_sigmaConvexHull {𝒞 : Set (Measure Ω)} : 𝒞 ⊆ sigmaConvexHull 𝒞 := by
  intro ν hν
  refine ⟨fun n ↦ if n = 0 then 1 else 0, fun _ ↦ ν, by simp, fun _ ↦ hν, ?_⟩
  ext t ht
  rw [Measure.sum_apply _ ht, tsum_eq_single 0 fun n hn ↦ by simp [hn]]
  simp

/-- The σ-convex hull is σ-convex: a countable mixture of countable mixtures is a countable
mixture, indexed by the pairs of indices. -/
theorem isSigmaConvex_sigmaConvexHull {𝒞 : Set (Measure Ω)} :
    IsSigmaConvex (sigmaConvexHull 𝒞) := by
  intro v νs hv hνs
  choose w Qs hw hQs hνs_eq using hνs
  set e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  refine ⟨fun k ↦ v (e k).1 * w (e k).1 (e k).2, fun k ↦ Qs (e k).1 (e k).2, ?_,
    fun k ↦ hQs _ _, ?_⟩
  · rw [e.tsum_eq (fun p ↦ v p.1 * w p.1 p.2), tsum_prod (f := fun i j ↦ v i * w i j)]
    simp [ENNReal.tsum_mul_left, hw, hv]
  ext t ht
  simp only [Measure.sum_apply _ ht, hνs_eq, smul_apply, smul_eq_mul]
  rw [e.tsum_eq (fun p ↦ v p.1 * w p.1 p.2 * Qs p.1 p.2 t),
    tsum_prod (f := fun i j ↦ v i * w i j * Qs i j t)]
  simp [mul_assoc, ENNReal.tsum_mul_left]

/-- The σ-convex hull of `𝒞` is contained in every σ-convex set that contains `𝒞`. -/
theorem IsSigmaConvex.sigmaConvexHull_subset {𝒞 𝒟 : Set (Measure Ω)} (h𝒟 : IsSigmaConvex 𝒟)
    (h : 𝒞 ⊆ 𝒟) : sigmaConvexHull 𝒞 ⊆ 𝒟 := by
  rintro _ ⟨w, Qs, hw, hQs, rfl⟩
  exact h𝒟.sum_smul_mem hw fun n ↦ h (hQs n)

end MeasureTheory
