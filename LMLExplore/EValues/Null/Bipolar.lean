/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Null.Polar
public import LMLExplore.MeasureTheory.Function.SolidConvexHull
public import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-!
# The bipolar theorem on the side of functions

A set `𝓔` of bets generates the null `polarNull 𝓔` of the measures under which every bet has
expectation at most one. Which functions are e-variables for that null? Every bet is one, and so
is every convex combination of bets, every measurable function below one, and every limit of
such functions. The bipolar theorem of Brannath and Schachermayer [BS99, Theorem 1.3] says that
nothing else is, provided the null is restricted to the measures absolutely continuous with
respect to a reference measure `μ`: for an s-finite `μ` and a nonempty set `𝓔` of measurable
bets, the `μ`-almost everywhere finite e-variables of the σ-finite members of `polarNull 𝓔`
absolutely continuous with respect to `μ` are exactly the `μ`-almost everywhere finite members of
the closed solid convex hull of `𝓔` in `L⁰₊(μ)`.

The theorem is the description of `{X | IsEVar X S}` from bets that a complete class theorem asks
for, under domination. It is also the step from e-variables back to measures behind the
description of the effective null of a dominated null by densities [LRR25, Lemma 4.5].

## Main statements

* `ProbabilityTheory.closedSolidConvexHull_subset_setOf_isEVar`: for a null of measures
  absolutely continuous with respect to `μ`, the e-variables form a convex, solid and closed set,
  so they contain the closed solid convex hull of every set of e-variables.
* `ProbabilityTheory.mem_closedSolidConvexHull_of_isEVar`: for an s-finite `μ` and a nonempty set
  `𝓔` of measurable bets, a `μ`-almost everywhere finite e-variable for the finite members of
  `polarNull 𝓔` absolutely continuous with respect to `μ` is in the closed solid convex hull of
  `𝓔`.
* `ProbabilityTheory.mem_closedSolidConvexHull_iff_isEVar`: **the bipolar theorem** [BS99,
  Theorem 1.3]: a `μ`-almost everywhere finite function is in the closed solid convex hull of `𝓔`
  exactly when it is an e-variable for the σ-finite members of `polarNull 𝓔` absolutely
  continuous with respect to `μ`.
* `ProbabilityTheory.exists_mem_closedSolidConvexHull_not_isEVar_polarNull`: the restriction to
  absolutely continuous members cannot be dropped. For `𝓔 = {1}` and a point of `μ`-measure zero,
  a function equal to `2` at that point and `0` elsewhere is in the hull, but it is not an
  e-variable for the Dirac mass at the point, which is in `polarNull {1}`.

The hull is closed under almost everywhere limits that are almost everywhere finite
(`MeasureTheory.IsAESeqClosed`), which for a finite measure is closedness in `μ`-probability in
`L⁰₊(μ)`. The easy direction holds for every null of measures absolutely continuous with respect
to `μ`, with no finiteness and no σ-finiteness. The proof of the other separates a function outside
the hull with `MeasureTheory.exists_lintegral_mul_le_one_lt`, applied to the finite measure
`μ.toFinite` with the null sets of `μ`, and reads the separating weight `g` as the density of a
member `μ.toFinite.withDensity g` of the polar.

## References

* [BS99] W. Brannath and W. Schachermayer, *A bipolar theorem for `L⁰₊(Ω, F, P)`*, Séminaire de
  Probabilités XXXIII, Lecture Notes in Math. 1709 (1999), Theorem 1.3.
* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4, Lemma 4.5.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {S : Set (Measure Ω)}
  {𝓔 : Set (Ω → ℝ≥0∞)} {X : Ω → ℝ≥0∞}

/-- For a null of measures absolutely continuous with respect to `μ`, the set of e-variables is
solid for `μ`. -/
lemma isAESolid_setOf_isEVar (hS : ∀ ν ∈ S, ν ≪ μ) : IsAESolid μ {X | IsEVar X S} :=
  isAESolid_iff.2 fun _ _ (hf : IsEVar _ S) hg hgf ↦
    hf.mono_ae hg (eventuallyLE_quasiSure_iff.2 fun _ hν ↦ (hS _ hν).ae_le hgf)

/-- For a null of measures absolutely continuous with respect to `μ`, the set of e-variables is
closed under `μ`-almost everywhere limits, by Fatou's lemma. -/
lemma isAESeqClosed_setOf_isEVar (hS : ∀ ν ∈ S, ν ≪ μ) : IsAESeqClosed μ {X | IsEVar X S} :=
  isAESeqClosed_iff.2 fun _ _ hf hg _ hfg ↦ (isEVar_liminf hf).congr hg fun _ hν ↦
    Eventually.mono ((hS _ hν).ae_le hfg) fun _ hω ↦ hω.liminf_eq

/-- For a null of measures absolutely continuous with respect to `μ`, the closed solid convex hull
of a set of e-variables consists of e-variables. -/
theorem closedSolidConvexHull_subset_setOf_isEVar (hS : ∀ ν ∈ S, ν ≪ μ)
    (h𝓔 : ∀ E ∈ 𝓔, IsEVar E S) : closedSolidConvexHull μ 𝓔 ⊆ {X | IsEVar X S} :=
  closedSolidConvexHull_subset h𝓔 (convex_isEVar S) (isAESolid_setOf_isEVar hS)
    (isAESeqClosed_setOf_isEVar hS)

/-- Every member of the closed solid convex hull of a set `𝓔` of measurable bets is an e-variable
for the members of `polarNull 𝓔` absolutely continuous with respect to `μ`. -/
theorem IsEVar.of_mem_closedSolidConvexHull (h𝓔 : ∀ E ∈ 𝓔, Measurable E)
    (hX : X ∈ closedSolidConvexHull μ 𝓔) : IsEVar X (polarNull 𝓔 ∩ {ν | ν ≪ μ}) :=
  closedSolidConvexHull_subset_setOf_isEVar (S := polarNull 𝓔 ∩ {ν | ν ≪ μ})
    (fun _ hν ↦ hν.2) (fun E hE ↦ ⟨h𝓔 E hE, fun _ hν ↦ mem_polarNull_iff.1 hν.1 E hE⟩) hX

/-- **The bipolar theorem, the hard direction** [BS99, Theorem 1.3]. For an s-finite `μ` and a
nonempty set `𝓔` of measurable bets, a `μ`-almost everywhere finite e-variable for the finite
members of `polarNull 𝓔` absolutely continuous with respect to `μ` is in the closed solid convex
hull of `𝓔`. -/
theorem mem_closedSolidConvexHull_of_isEVar [SFinite μ] (hne : 𝓔.Nonempty)
    (h𝓔 : ∀ E ∈ 𝓔, Measurable E) (hX_top : ∀ᵐ ω ∂μ, X ω ≠ ∞)
    (hX : IsEVar X (polarNull 𝓔 ∩ {ν | IsFiniteMeasure ν ∧ ν ≪ μ})) :
    X ∈ closedSolidConvexHull μ 𝓔 := by
  rw [closedSolidConvexHull_congr_ae ae_toFinite.symm]
  by_contra hXD
  obtain ⟨g, hg, hg_top, hD, hXg⟩ := exists_lintegral_mul_le_one_lt convex_closedSolidConvexHull
    isAESolid_closedSolidConvexHull isAESeqClosed_closedSolidConvexHull
    (hne.mono subset_closedSolidConvexHull) hX.measurable (by rwa [ae_toFinite]) hXD
  -- the separating weight is the density of a member of the polar
  set ν := μ.toFinite.withDensity fun ω ↦ g ω
  have hgm : Measurable fun ω ↦ (g ω : ℝ≥0∞) := hg.coe_nnreal_ennreal
  have hν_eq (f : Ω → ℝ≥0∞) (hf : Measurable f) :
      ∫⁻ ω, f ω ∂ν = ∫⁻ ω, f ω * g ω ∂μ.toFinite := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hgm hf]
    simp_rw [Pi.mul_apply, mul_comm]
  have hν : ν ∈ polarNull 𝓔 ∩ {ν | IsFiniteMeasure ν ∧ ν ≪ μ} := by
    refine ⟨mem_polarNull_iff.2 fun E hE ↦ ?_, ⟨?_⟩, (withDensity_absolutelyContinuous _ _).trans
      (toFinite_absolutelyContinuous μ)⟩
    · rw [hν_eq E (h𝓔 E hE)]
      exact hD E (subset_closedSolidConvexHull hE) (h𝓔 E hE)
    · rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact hg_top.lt_top
  exact (hXg.trans_eq (hν_eq X hX.measurable).symm).not_ge (hX.lintegral_le_one hν)

/-- **The bipolar theorem** [BS99, Theorem 1.3]. For an s-finite measure `μ` and a nonempty set
`𝓔` of measurable bets, a `μ`-almost everywhere finite function is in the closed solid convex hull
of `𝓔` exactly when it is an e-variable for the σ-finite members of `polarNull 𝓔` absolutely
continuous with respect to `μ`. -/
theorem mem_closedSolidConvexHull_iff_isEVar [SFinite μ] (hne : 𝓔.Nonempty)
    (h𝓔 : ∀ E ∈ 𝓔, Measurable E) (hX_top : ∀ᵐ ω ∂μ, X ω ≠ ∞) :
    X ∈ closedSolidConvexHull μ 𝓔 ↔
      IsEVar X (polarNull 𝓔 ∩ {ν | SigmaFinite ν ∧ ν ≪ μ}) :=
  ⟨fun hX ↦ (IsEVar.of_mem_closedSolidConvexHull h𝓔 hX).anti_set
      (inter_subset_inter_right _ fun _ hν ↦ hν.2),
    fun hX ↦ mem_closedSolidConvexHull_of_isEVar hne h𝓔 hX_top <| hX.anti_set <| by
      rintro ν ⟨hν, _, hνμ⟩
      exact ⟨hν, inferInstance, hνμ⟩⟩

/-- The bipolar theorem needs the restriction to the members of the polar absolutely continuous
with respect to `μ`. For `𝓔 = {1}` and a point `x` of `μ`-measure zero, the function equal to `2`
at `x` and `0` elsewhere is in the closed solid convex hull of `𝓔`, but it is not an e-variable for
`polarNull {1}`, which contains the Dirac mass at `x`. -/
theorem exists_mem_closedSolidConvexHull_not_isEVar_polarNull [MeasurableSingletonClass Ω]
    {x : Ω} (hx : μ {x} = 0) :
    ∃ X ∈ closedSolidConvexHull μ {1}, ¬ IsEVar X (polarNull {1}) := by
  refine ⟨Set.indicator {x} 2, isAESolid_closedSolidConvexHull.mem
    (subset_closedSolidConvexHull rfl) (measurable_const.indicator (measurableSet_singleton x)) ?_,
    fun h ↦ ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hx] with ω hω
    simp [hω]
  · have h1 : Measure.dirac x ∈ polarNull {1} := by simp [mem_polarNull_iff]
    have h2 := h.lintegral_le_one h1
    simp at h2

end ProbabilityTheory
