/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EffectiveSet.Basic
public import LMLExplore.EValues.Null.Bipolar
import LMLExplore.Analysis.Convex.ENNReal
import LMLExplore.MeasureTheory.Measure.Typeclasses.Probability
import LMLExplore.MeasureTheory.Measure.WithDensity

/-!
# The effective null of a dominated null

When every member of a null `S` is absolutely continuous with respect to a σ-finite measure `μ`,
so is every member of its effective null (`absolutelyContinuous_of_mem_effectiveSet`), and the
effective null can be read off the densities. Larsson, Ramdas and Ruf [LRR25, Lemma 4.5] identify
it as the smallest set of measures that contains `S` and is convex, solid and closed under
convergence in `μ`-probability of the densities. Here: a σ-finite measure `ν` is in
`effectiveSet S` exactly when `ν ≪ μ` and its density `dν/dμ` is in the closed solid convex hull
of the densities `dP/dμ` of the members of `S`, the smallest set of functions that contains them
and is convex, solid and closed in `L⁰₊(μ)` (`MeasureTheory.closedSolidConvexHull`).

The proof pairs measures with densities: a measurable `X` is an e-variable for `S` exactly when
the measure with density `X` is in the polar of the densities of `S`, so that the densities of the
effective null are the bipolar of the densities of `S`, and the bipolar theorem of Brannath and
Schachermayer (`mem_closedSolidConvexHull_iff_isEVar`) describes the bipolar.

For finitely many finite measures the closed solid convex hull of the densities is the set of
functions below a convex combination of them (`MeasureTheory.closedSolidConvexHull_range`). The
effective null of a finite null is therefore the set of measures setwise below a convex
combination of its members, and its probability measures form the convex hull of the null when the
members are probability measures [LRR25, Corollary 4.6].

## Main statements

* `ProbabilityTheory.isEVar_image_withDensity_iff`: a measurable `X` is an e-variable for the
  measures `μ.withDensity p`, `p ∈ D`, exactly when `μ.withDensity X` is in `polarNull D`.
* `ProbabilityTheory.withDensity_mem_effectiveSet_iff`: for a σ-finite `μ` and a nonempty set `D`
  of measurable densities, a measurable, `μ`-almost everywhere finite `q` is the density of a
  member of the effective null of the measures with densities in `D` exactly when `q` is in the
  closed solid convex hull of `D`. The direction from the hull to the effective null,
  `ProbabilityTheory.withDensity_mem_effectiveSet_of_mem_closedSolidConvexHull`, holds for every
  `μ`.
* `ProbabilityTheory.mem_effectiveSet_iff_rnDeriv_mem_closedSolidConvexHull`: **the effective null
  of a dominated null** [LRR25, Lemma 4.5], in terms of Radon–Nikodym derivatives.
* `ProbabilityTheory.mem_effectiveSet_range_iff`: the effective null of finitely many finite
  measures `P i` consists of the measures setwise below some convex combination `∑ i, w i • P i`
  [LRR25, Corollary 4.6].
* `ProbabilityTheory.effectiveSet_range_inter_eq_convexHull`: for finitely many probability
  measures, the probability measures of the effective null are the convex hull of the null
  [LRR25, Corollary 4.6].

## References

* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4, Lemma 4.5 and Corollary 4.6.
* [BS99] W. Brannath and W. Schachermayer, *A bipolar theorem for `L⁰₊(Ω, F, P)`*, Séminaire de
  Probabilités XXXIII, Lecture Notes in Math. 1709 (1999), Theorem 1.3.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {S : Set (Measure Ω)}
  {D : Set (Ω → ℝ≥0∞)} {q : Ω → ℝ≥0∞}

/-- **E-variables of a null given by densities.** For measurable densities `D` with respect to
`μ`, a measurable `X` is an e-variable for the measures `μ.withDensity p`, `p ∈ D`, exactly when
the measure `μ.withDensity X` is in the polar of `D`: both say that `∫⁻ X * p ∂μ ≤ 1` for every
`p ∈ D`. -/
theorem isEVar_image_withDensity_iff (hD : ∀ p ∈ D, Measurable p) {X : Ω → ℝ≥0∞}
    (hX : Measurable X) :
    IsEVar X ((fun p ↦ μ.withDensity p) '' D) ↔ μ.withDensity X ∈ polarNull D := by
  simp only [isEVar_iff_lintegral_le_one, forall_mem_image, mem_polarNull_iff, hX, true_and]
  refine forall₂_congr fun p hp ↦ ?_
  rw [lintegral_withDensity_comm (hD p hp).aemeasurable hX.aemeasurable]

/-- The measures whose densities are in the closed solid convex hull of a set `D` of measurable
densities are in the effective null of the measures `μ.withDensity p`, `p ∈ D`. This holds for
every measure `μ`, with no finiteness. -/
theorem withDensity_mem_effectiveSet_of_mem_closedSolidConvexHull (hD : ∀ p ∈ D, Measurable p)
    (hq : q ∈ closedSolidConvexHull μ D) :
    μ.withDensity q ∈ effectiveSet ((fun p ↦ μ.withDensity p) '' D) := by
  intro X hX
  -- the measure with density an e-variable `X` is in the polar of `D`, so `q` integrates to at
  -- most `1` against it
  have hq_evar := IsEVar.of_mem_closedSolidConvexHull hD hq
  have h_le := hq_evar.lintegral_le_one
    ⟨(isEVar_image_withDensity_iff hD hX.measurable).1 hX, withDensity_absolutelyContinuous μ X⟩
  rwa [lintegral_withDensity_comm hX.measurable.aemeasurable hq_evar.measurable.aemeasurable]

/-- **The densities of the effective null.** For a σ-finite measure `μ` and a nonempty set `D` of
measurable densities, a measurable, `μ`-almost everywhere finite `q` is the density of a member of
the effective null of the measures `μ.withDensity p`, `p ∈ D`, exactly when `q` is in the closed
solid convex hull of `D`: the densities of the effective null are the bipolar of `D`. -/
theorem withDensity_mem_effectiveSet_iff [SigmaFinite μ] (hne : D.Nonempty)
    (hD : ∀ p ∈ D, Measurable p) (hq : Measurable q) (hq_top : ∀ᵐ ω ∂μ, q ω ≠ ∞) :
    μ.withDensity q ∈ effectiveSet ((fun p ↦ μ.withDensity p) '' D) ↔
      q ∈ closedSolidConvexHull μ D := by
  refine ⟨fun h ↦ mem_closedSolidConvexHull_of_isEVar hne hD hq_top ⟨hq, ?_⟩,
    withDensity_mem_effectiveSet_of_mem_closedSolidConvexHull hD⟩
  -- a finite member `ν ≪ μ` of the polar of `D` is the measure with density `dν/dμ`, an
  -- e-variable for the measures with densities in `D`
  rintro ν ⟨hν, hν_fin, hνμ⟩
  have hg := Measure.measurable_rnDeriv ν μ
  rw [← Measure.withDensity_rnDeriv_eq ν μ hνμ] at hν ⊢
  rw [lintegral_withDensity_comm hq.aemeasurable hg.aemeasurable]
  exact h _ ((isEVar_image_withDensity_iff hD hg).2 hν)

/-- **The effective null of a dominated null** [LRR25, Lemma 4.5]. Let `S` be a nonempty null of
s-finite measures absolutely continuous with respect to a σ-finite measure `μ`. A σ-finite measure
`ν` is in the effective null of `S` exactly when `ν ≪ μ` and its density `dν/dμ` is in the closed
solid convex hull of the densities `dP/dμ`, `P ∈ S`, the smallest set of functions that contains
them and is convex, solid and closed under almost everywhere convergence (closed in `L⁰₊(μ)`). -/
theorem mem_effectiveSet_iff_rnDeriv_mem_closedSolidConvexHull [SigmaFinite μ] [SigmaFinite ν]
    (hne : S.Nonempty) (hS : ∀ P ∈ S, P ≪ μ) (hS_fin : ∀ P ∈ S, SFinite P) :
    ν ∈ effectiveSet S ↔
      ν ≪ μ ∧ ν.rnDeriv μ ∈ closedSolidConvexHull μ ((fun P ↦ P.rnDeriv μ) '' S) := by
  have hS_eq : (fun p ↦ μ.withDensity p) '' ((fun P ↦ P.rnDeriv μ) '' S) = S := by
    rw [image_image]
    refine (image_congr fun P hP ↦ ?_).trans (image_id S)
    have := hS_fin P hP
    exact Measure.withDensity_rnDeriv_eq P μ (hS P hP)
  have hD : ∀ p ∈ (fun P ↦ P.rnDeriv μ) '' S, Measurable p :=
    forall_mem_image.2 fun P _ ↦ Measure.measurable_rnDeriv P μ
  have h_iff := withDensity_mem_effectiveSet_iff (hne.image _) hD
    (Measure.measurable_rnDeriv ν μ) (Measure.rnDeriv_ne_top ν μ)
  rw [hS_eq] at h_iff
  refine ⟨fun h ↦ ?_, fun ⟨hνμ, h⟩ ↦ ?_⟩
  · have hνμ := absolutelyContinuous_of_mem_effectiveSet h hS
    rw [Measure.withDensity_rnDeriv_eq ν μ hνμ] at h_iff
    exact ⟨hνμ, h_iff.1 h⟩
  · rw [← Measure.withDensity_rnDeriv_eq ν μ hνμ]
    exact h_iff.2 h

/-- **The effective null of a finite null** [LRR25, Corollary 4.6]. For finitely many finite
measures `P i`, a measure is in the effective null of `{P i}` exactly when it is setwise below a
convex combination `∑ i, w i • P i` of them. -/
theorem mem_effectiveSet_range_iff {ι : Type*} [Fintype ι] [Nonempty ι] {P : ι → Measure Ω}
    [∀ i, IsFiniteMeasure (P i)] :
    ν ∈ effectiveSet (range P) ↔ ∃ w : ι → ℝ≥0∞, ∑ i, w i = 1 ∧ ν ≤ ∑ i, w i • P i := by
  refine ⟨fun hν ↦ ?_, fun ⟨w, hw, hν⟩ ↦ mem_effectiveSet_of_le
    (Convex.sum_ennreal_smul_mem convex_effectiveSet hw fun i _ ↦ subset_effectiveSet ⟨i, rfl⟩) hν⟩
  -- the reference measure is the sum of the members
  set μ := Measure.sum P
  have hPμ (i : ι) : P i ≤ μ := Measure.le_sum P i
  have hνμ : ν ≪ μ := absolutelyContinuous_of_mem_effectiveSet hν
    (forall_mem_range.2 fun i ↦ Measure.absolutelyContinuous_of_le (hPμ i))
  -- `ν` has mass at most that of `μ`, since `P i univ ≤ μ univ` for every `i`
  have : IsFiniteMeasure ν := ⟨by
    refine lt_of_le_of_lt ?_ (measure_lt_top μ univ)
    simpa using lintegral_le_of_mem_effectiveSet hν (φ := fun _ ↦ 1) measurable_const
      (forall_mem_range.2 fun i ↦ by simpa using Measure.le_iff'.1 (hPμ i) univ)⟩
  -- the density of `ν` is below a convex combination of the densities `p i` of the `P i`
  set p : ι → Ω → ℝ≥0∞ := fun i ↦ (P i).rnDeriv μ
  have hq := ((mem_effectiveSet_iff_rnDeriv_mem_closedSolidConvexHull (range_nonempty P)
    (forall_mem_range.2 fun i ↦ Measure.absolutelyContinuous_of_le (hPμ i))
    (forall_mem_range.2 fun i ↦ inferInstance)).1 hν).2
  have h_range : (fun P ↦ P.rnDeriv μ) '' range P = range p := (range_comp _ _).symm
  rw [h_range, closedSolidConvexHull_range (fun i ↦ Measure.measurable_rnDeriv (P i) μ)
    (fun i ↦ Measure.rnDeriv_ne_top (P i) μ)] at hq
  obtain ⟨-, w, hw, hqw⟩ := hq
  refine ⟨w, hw, ?_⟩
  -- integrate the bound on the densities against `μ`
  have hp (i : ι) : Measurable (w i • p i) := (Measure.measurable_rnDeriv _ _).const_smul _
  calc ν = μ.withDensity (ν.rnDeriv μ) := (Measure.withDensity_rnDeriv_eq ν μ hνμ).symm
  _ ≤ μ.withDensity (∑ i, w i • p i) := withDensity_mono hqw
  _ = ∑ i, μ.withDensity (w i • p i) := by
    rw [← Measure.sum_fintype, ← withDensity_tsum hp, tsum_fintype]
  _ = ∑ i, w i • P i := Finset.sum_congr rfl fun i _ ↦ by
    rw [withDensity_smul _ (Measure.measurable_rnDeriv _ _),
      Measure.withDensity_rnDeriv_eq _ _ (Measure.absolutelyContinuous_of_le (hPμ i))]

/-- **The probability measures of the effective null of a finite null** [LRR25, Corollary 4.6].
For finitely many probability measures `P i`, the probability measures of the effective null of
`{P i}` are the convex hull of `{P i}`. -/
theorem effectiveSet_range_inter_eq_convexHull {ι : Type*} [Finite ι] {P : ι → Measure Ω}
    [∀ i, IsProbabilityMeasure (P i)] :
    effectiveSet (range P) ∩ {ν | IsProbabilityMeasure ν} = convexHull ℝ≥0∞ (range P) := by
  have := Fintype.ofFinite ι
  refine subset_antisymm ?_ (convexHull_min (fun _ ⟨i, hi⟩ ↦ hi ▸
    ⟨subset_effectiveSet ⟨i, rfl⟩, inferInstanceAs (IsProbabilityMeasure (P i))⟩)
    (convex_effectiveSet.inter convex_setOfPred_isProbabilityMeasure))
  rintro ν ⟨hν, hν_prob⟩
  have : IsProbabilityMeasure ν := hν_prob
  -- the null is not empty, since the empty null has no probability measure in its effective null
  have : Nonempty ι := by
    by_contra h
    have h_le := lintegral_le_of_mem_effectiveSet hν measurable_const (φ := fun _ ↦ 1) (c := 0)
      (by simp [not_nonempty_iff.1 h])
    simp at h_le
  obtain ⟨w, hw, hνw⟩ := mem_effectiveSet_range_iff.1 hν
  have h_eq : ν = ∑ i, w i • P i := Measure.eq_of_le_of_measure_univ_eq hνw (by simp [hw])
  rw [h_eq]
  exact Convex.sum_ennreal_smul_mem (convex_convexHull ℝ≥0∞ (range P)) hw fun i _ ↦
    subset_convexHull ℝ≥0∞ _ ⟨i, rfl⟩

end ProbabilityTheory
