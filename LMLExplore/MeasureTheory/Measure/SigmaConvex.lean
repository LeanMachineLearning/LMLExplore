/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

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
* `MeasureTheory.convexHull_subset_sigmaConvexHull`: the finite mixtures are countable mixtures.
* `MeasureTheory.isProbabilityMeasure_of_mem_sigmaConvexHull`: the countable mixtures of
  probability measures are probability measures.
* `MeasureTheory.add_add_smul_mem_convexHull`: a mixture of three members with real weights of
  sum one is in the convex hull.

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

/-- The finite mixtures of members of `𝒞`, its convex hull, are countable mixtures. -/
theorem convexHull_subset_sigmaConvexHull {𝒞 : Set (Measure Ω)} :
    convexHull ℝ≥0∞ 𝒞 ⊆ sigmaConvexHull 𝒞 :=
  convexHull_min subset_sigmaConvexHull isSigmaConvex_sigmaConvexHull.convex

/-- The countable mixtures of probability measures are probability measures. -/
theorem isProbabilityMeasure_of_mem_sigmaConvexHull {𝒞 : Set (Measure Ω)}
    (h𝒞 : ∀ P ∈ 𝒞, IsProbabilityMeasure P) {ν : Measure Ω} (hν : ν ∈ sigmaConvexHull 𝒞) :
    IsProbabilityMeasure ν := by
  obtain ⟨w, Qs, hw, hQs, rfl⟩ := mem_sigmaConvexHull_iff.1 hν
  constructor
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp [fun i ↦ (h𝒞 _ (hQs i)).measure_univ, hw]

/-- A mixture of three members of a set of measures, with real weights of sum one, is in its
convex hull. -/
theorem add_add_smul_mem_convexHull {𝒞 : Set (Measure Ω)} {P₁ P₂ P₃ : Measure Ω} (h₁ : P₁ ∈ 𝒞)
    (h₂ : P₂ ∈ 𝒞) (h₃ : P₃ ∈ 𝒞) {w₁ w₂ w₃ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    (hw : w₁ + w₂ + w₃ = 1) :
    ENNReal.ofReal w₁ • P₁ + ENNReal.ofReal w₂ • P₂ + ENNReal.ofReal w₃ • P₃ ∈
      convexHull ℝ≥0∞ 𝒞 := by
  have h𝒞 := convex_convexHull ℝ≥0∞ 𝒞
  rcases (add_nonneg hw₁ hw₂).eq_or_lt with h0 | h0
  · obtain rfl : w₁ = 0 := by linarith
    obtain rfl : w₂ = 0 := by linarith
    obtain rfl : w₃ = 1 := by linarith
    simpa using subset_convexHull ℝ≥0∞ 𝒞 h₃
  -- the mixture of the first two, with weights `w₁ / (w₁ + w₂)` and `w₂ / (w₁ + w₂)`
  have h12 : ENNReal.ofReal (w₁ / (w₁ + w₂)) • P₁ + ENNReal.ofReal (w₂ / (w₁ + w₂)) • P₂ ∈
      convexHull ℝ≥0∞ 𝒞 := by
    refine h𝒞 (subset_convexHull ℝ≥0∞ 𝒞 h₁) (subset_convexHull ℝ≥0∞ 𝒞 h₂) zero_le zero_le ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_div, div_self h0.ne',
      ENNReal.ofReal_one]
  have h := h𝒞 h12 (subset_convexHull ℝ≥0∞ 𝒞 h₃) (zero_le (a := ENNReal.ofReal (w₁ + w₂)))
    (zero_le (a := ENNReal.ofReal w₃)) (by rw [← ENNReal.ofReal_add h0.le hw₃, hw,
      ENNReal.ofReal_one])
  rwa [smul_add, smul_smul, smul_smul, ← ENNReal.ofReal_mul h0.le, ← ENNReal.ofReal_mul h0.le,
    mul_div_cancel₀ _ h0.ne', mul_div_cancel₀ _ h0.ne'] at h

end MeasureTheory
