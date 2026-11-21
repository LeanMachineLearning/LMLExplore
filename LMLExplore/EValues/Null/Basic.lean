/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.PVariable
public import LMLExplore.Probability.ProductMeasure

/-!
# Operations on nulls

A null hypothesis is a set `S : Set (Measure Ω)` of measures, with no dominating measure and no
convexity. This file names the operations that build new nulls from old ones, so that inclusions
between nulls, such as `iidNull S₁ ⊆ indepNull S₁`, can be stated and used:

* `ProbabilityTheory.mapNull φ S`, the image of a null by a map: the laws of `φ` under the members
  of `S`;
* `ProbabilityTheory.sampleNull S₁ n`, the null of `n` independent observations with one law in
  `S₁`, on `Fin n → 𝓧`;
* `ProbabilityTheory.iidNull S₁`, the null of an i.i.d. sequence with law in `S₁`, on `ℕ → 𝓧`;
* `ProbabilityTheory.indepNull S₁`, the null of a sequence of independent observations, each with
  a law in `S₁` that may depend on the index.

The product of two nulls is Statlib's `Set.image2 Measure.prod S T`, the form of
`ProbabilityTheory.IsEVar.prod` and `ProbabilityTheory.maxEPower_prod_eq_add`. Its membership,
monotonicity and singleton lemmas are Mathlib's `Set.mem_image2`, `Set.image2_subset` and
`Set.image2_singleton`, and this file adds the masses of its members.

For each operation the file gives the membership lemma, monotonicity, the singleton and empty
cases, and the masses of the members: probability measures when those of the argument are, mass
at most one when those of the argument have mass at most one. The members of `iidNull S₁` and of
`indepNull S₁` have mass at most one for every `S₁`, since Mathlib's `Measure.infinitePi` is `0`
unless every factor is a probability measure.

## Main statements

* `ProbabilityTheory.isEVar_mapNull_iff`, `ProbabilityTheory.isPVar_mapNull_iff`: for measurable
  `φ` and `X`, `X` is an e-variable (a p-variable) for the image of `S` by `φ` exactly when
  `X ∘ φ` is one for `S`.
* `ProbabilityTheory.iidNull_subset_indepNull`: an i.i.d. sequence is an independent sequence.
* `ProbabilityTheory.mapNull_initSeg_iidNull`: for a null of probability measures, the first `n`
  terms of the sequences of `iidNull S₁` have the laws of `sampleNull S₁ n`.

## References

* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4, Definition 3.1.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, Definition 1.2.

The definitions follow the prototypes of `notes/book/Suggested.lean` (commit `88fb487`) in the
paper project `RemyDegenne/evalues_research` (Apache 2.0).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω Ω' Ω'' 𝓧 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace Ω'] [MeasurableSpace Ω'']
  {m𝓧 : MeasurableSpace 𝓧}

/-! ### The image of a null by a map -/

section MapNull

variable {φ : Ω → Ω'} {S T : Set (Measure Ω)} {P : Measure Ω} {μ : Measure Ω'}

/-- The image of a null by a map: the laws `P.map φ` of `φ` under the members `P` of `S`. The
σ-algebra of the target is an instance argument: `φ` and `S` do not determine it. -/
noncomputable def mapNull (φ : Ω → Ω') (S : Set (Measure Ω)) : Set (Measure Ω') :=
  Measure.map φ '' S

/-- The null `mapNull φ S` as the set `{P.map φ | P ∈ S}`, the spelling of Statlib's
`IsEVar.comp` and `maxUtility_map_le`. -/
theorem mapNull_def (φ : Ω → Ω') (S : Set (Measure Ω)) : mapNull φ S = {P.map φ | P ∈ S} :=
  (rfl)

@[simp]
theorem mem_mapNull : μ ∈ mapNull φ S ↔ ∃ P ∈ S, P.map φ = μ :=
  Iff.rfl

theorem map_mem_mapNull (hP : P ∈ S) : P.map φ ∈ mapNull φ S :=
  mem_image_of_mem _ hP

@[gcongr]
theorem mapNull_mono (hST : S ⊆ T) : mapNull φ S ⊆ mapNull φ T :=
  image_mono hST

@[simp]
theorem mapNull_empty : mapNull φ (∅ : Set (Measure Ω)) = ∅ :=
  image_empty _

@[simp]
theorem mapNull_singleton : mapNull φ {P} = {P.map φ} :=
  image_singleton

theorem mapNull_union : mapNull φ (S ∪ T) = mapNull φ S ∪ mapNull φ T :=
  image_union _ _ _

@[simp]
theorem mapNull_id : mapNull id S = S := by
  simp [mapNull]

/-- The image of the image of a null is the image by the composition. -/
theorem mapNull_mapNull {ψ : Ω' → Ω''} (hψ : Measurable ψ) (hφ : Measurable φ) :
    mapNull ψ (mapNull φ S) = mapNull (ψ ∘ φ) S := by
  simp only [mapNull, image_image, Measure.map_map hψ hφ]

/-- The image by any map of a null of probability measures is a null of probability measures:
Mathlib's `Measure.map` along a map that is not almost everywhere measurable is a Dirac mass. -/
theorem isProbabilityMeasure_of_mem_mapNull (hS : ∀ P ∈ S, IsProbabilityMeasure P) :
    ∀ μ ∈ mapNull φ S, IsProbabilityMeasure μ := by
  rintro _ ⟨P, hP, rfl⟩
  have := hS P hP
  infer_instance

/-- The image by any map of a null of measures of mass at most one has members of mass at most
one. -/
theorem measure_univ_le_one_of_mem_mapNull (hS : ∀ P ∈ S, P univ ≤ 1) :
    ∀ μ ∈ mapNull φ S, μ univ ≤ 1 := by
  rintro _ ⟨P, hP, rfl⟩
  by_cases hφ : AEMeasurable φ P
  · rw [Measure.map_apply_of_aemeasurable hφ MeasurableSet.univ, preimage_univ]
    exact hS P hP
  · rcases eq_or_ne P 0 with rfl | hP0
    · simp
    · simp [Measure.map_of_not_aemeasurable_of_ne_zero hφ hP0]

/-- A measurable `X` is an e-variable for the image of `S` by a measurable map `φ` exactly when
`X ∘ φ` is an e-variable for `S`. Statlib's `IsEVar.comp` is the forward direction. -/
theorem isEVar_mapNull_iff (hφ : Measurable φ) {X : Ω' → ℝ≥0∞} (hX : Measurable X) :
    IsEVar X (mapNull φ S) ↔ IsEVar (X ∘ φ) S := by
  refine ⟨IsEVar.comp hφ, fun h ↦ ⟨hX, ?_⟩⟩
  rintro _ ⟨P, hP, rfl⟩
  rw [lintegral_map hX hφ]
  exact h.lintegral_le_one hP

/-- A measurable `p` is a p-variable for the image of `S` by a measurable map `φ` exactly when
`p ∘ φ` is a p-variable for `S`. `IsPVar.comp` is the forward direction. -/
theorem isPVar_mapNull_iff (hφ : Measurable φ) {p : Ω' → ℝ≥0∞} (hp : Measurable p) :
    IsPVar p (mapNull φ S) ↔ IsPVar (p ∘ φ) S := by
  refine ⟨IsPVar.comp hφ, fun h ↦ ⟨hp, ?_⟩⟩
  rintro _ ⟨P, hP, rfl⟩ α
  rw [Measure.map_apply hφ (measurableSet_le hp measurable_const)]
  exact h.measure_le_le P hP α

end MapNull

/-! ### The product of two nulls -/

section Prod

variable {S : Set (Measure Ω)} {T : Set (Measure Ω')}

/-- The product of two nulls of probability measures is a null of probability measures. -/
theorem isProbabilityMeasure_of_mem_image2_prod (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hT : ∀ Q ∈ T, IsProbabilityMeasure Q) :
    ∀ μ ∈ image2 Measure.prod S T, IsProbabilityMeasure μ := by
  rintro _ ⟨P, hP, Q, hQ, rfl⟩
  have := hS P hP
  have := hT Q hQ
  infer_instance

/-- The product of two nulls of measures of mass at most one has members of mass at most one. -/
theorem measure_univ_le_one_of_mem_image2_prod (hS : ∀ P ∈ S, P univ ≤ 1)
    (hT : ∀ Q ∈ T, Q univ ≤ 1) : ∀ μ ∈ image2 Measure.prod S T, μ univ ≤ 1 := by
  rintro _ ⟨P, hP, Q, hQ, rfl⟩
  have : IsFiniteMeasure Q := ⟨(hT Q hQ).trans_lt ENNReal.one_lt_top⟩
  rw [← univ_prod_univ, Measure.prod_prod]
  exact mul_le_one' (hS P hP) (hT Q hQ)

end Prod

/-! ### Samples, i.i.d. sequences and independent sequences -/

section Sample

variable {S₁ T₁ : Set (Measure 𝓧)} {P : Measure 𝓧} {n : ℕ}

/-- The null of `n` independent observations with one law in `S₁`: the product laws
`Measure.pi fun _ : Fin n ↦ P` for `P ∈ S₁`. -/
noncomputable def sampleNull (S₁ : Set (Measure 𝓧)) (n : ℕ) : Set (Measure (Fin n → 𝓧)) :=
  (fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁

/-- The null `sampleNull S₁ n` as the image of `S₁` under `P ↦ Measure.pi fun _ : Fin n ↦ P`. -/
theorem sampleNull_def (S₁ : Set (Measure 𝓧)) (n : ℕ) :
    sampleNull S₁ n = (fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁ :=
  (rfl)

@[simp]
theorem mem_sampleNull {μ : Measure (Fin n → 𝓧)} :
    μ ∈ sampleNull S₁ n ↔ ∃ P ∈ S₁, (Measure.pi fun _ : Fin n ↦ P) = μ :=
  Iff.rfl

theorem pi_mem_sampleNull (hP : P ∈ S₁) : (Measure.pi fun _ : Fin n ↦ P) ∈ sampleNull S₁ n :=
  mem_image_of_mem _ hP

/-- A property holds for every member of `sampleNull S₁ n` exactly when it holds for the product
law `Measure.pi fun _ : Fin n ↦ P` of every `P ∈ S₁`. -/
theorem forall_mem_sampleNull {p : Measure (Fin n → 𝓧) → Prop} :
    (∀ μ ∈ sampleNull S₁ n, p μ) ↔ ∀ P ∈ S₁, p (Measure.pi fun _ : Fin n ↦ P) :=
  forall_mem_image

@[gcongr]
theorem sampleNull_mono (hST : S₁ ⊆ T₁) (n : ℕ) : sampleNull S₁ n ⊆ sampleNull T₁ n :=
  image_mono hST

@[simp]
theorem sampleNull_empty (n : ℕ) : sampleNull (∅ : Set (Measure 𝓧)) n = ∅ :=
  image_empty _

@[simp]
theorem sampleNull_singleton (P : Measure 𝓧) (n : ℕ) :
    sampleNull {P} n = {Measure.pi fun _ : Fin n ↦ P} :=
  image_singleton

@[simp]
theorem sampleNull_insert (P : Measure 𝓧) (S₁ : Set (Measure 𝓧)) (n : ℕ) :
    sampleNull (insert P S₁) n = insert (Measure.pi fun _ : Fin n ↦ P) (sampleNull S₁ n) :=
  image_insert_eq

/-- The samples of a null of probability measures have probability laws. -/
theorem isProbabilityMeasure_of_mem_sampleNull (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (n : ℕ) :
    ∀ μ ∈ sampleNull S₁ n, IsProbabilityMeasure μ := by
  rintro _ ⟨P, hP, rfl⟩
  have := hS₁ P hP
  infer_instance

/-- The samples of a null of measures of mass at most one have laws of mass at most one. -/
theorem measure_univ_le_one_of_mem_sampleNull (hS₁ : ∀ P ∈ S₁, P univ ≤ 1) (n : ℕ) :
    ∀ μ ∈ sampleNull S₁ n, μ univ ≤ 1 := by
  rintro _ ⟨P, hP, rfl⟩
  have : IsFiniteMeasure P := ⟨(hS₁ P hP).trans_lt ENNReal.one_lt_top⟩
  rw [Measure.pi_univ]
  exact Finset.prod_le_one fun _ _ ↦ hS₁ P hP

/-- The null of an i.i.d. sequence with law in `S₁`: the laws
`Measure.infinitePi fun _ : ℕ ↦ P` for `P ∈ S₁`. -/
noncomputable def iidNull (S₁ : Set (Measure 𝓧)) : Set (Measure (ℕ → 𝓧)) :=
  (fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁

/-- The null `iidNull S₁` as the image of `S₁` under `P ↦ Measure.infinitePi fun _ : ℕ ↦ P`. -/
theorem iidNull_def (S₁ : Set (Measure 𝓧)) :
    iidNull S₁ = (fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁ :=
  (rfl)

@[simp]
theorem mem_iidNull {μ : Measure (ℕ → 𝓧)} :
    μ ∈ iidNull S₁ ↔ ∃ P ∈ S₁, (Measure.infinitePi fun _ : ℕ ↦ P) = μ :=
  Iff.rfl

theorem infinitePi_mem_iidNull (hP : P ∈ S₁) : (Measure.infinitePi fun _ : ℕ ↦ P) ∈ iidNull S₁ :=
  mem_image_of_mem _ hP

/-- A property holds for every member of `iidNull S₁` exactly when it holds for the law
`Measure.infinitePi fun _ : ℕ ↦ P` of every `P ∈ S₁`. -/
theorem forall_mem_iidNull {p : Measure (ℕ → 𝓧) → Prop} :
    (∀ μ ∈ iidNull S₁, p μ) ↔ ∀ P ∈ S₁, p (Measure.infinitePi fun _ : ℕ ↦ P) :=
  forall_mem_image

@[gcongr]
theorem iidNull_mono (hST : S₁ ⊆ T₁) : iidNull S₁ ⊆ iidNull T₁ :=
  image_mono hST

@[simp]
theorem iidNull_empty : iidNull (∅ : Set (Measure 𝓧)) = ∅ :=
  image_empty _

@[simp]
theorem iidNull_singleton (P : Measure 𝓧) :
    iidNull {P} = {Measure.infinitePi fun _ : ℕ ↦ P} :=
  image_singleton

@[simp]
theorem iidNull_insert (P : Measure 𝓧) (S₁ : Set (Measure 𝓧)) :
    iidNull (insert P S₁) = insert (Measure.infinitePi fun _ : ℕ ↦ P) (iidNull S₁) :=
  image_insert_eq

/-- The members of the i.i.d. null of a null of probability measures are probability measures. -/
theorem isProbabilityMeasure_of_mem_iidNull (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) :
    ∀ μ ∈ iidNull S₁, IsProbabilityMeasure μ := by
  rintro _ ⟨P, hP, rfl⟩
  have := hS₁ P hP
  infer_instance

/-- The null of a sequence of independent observations, each with a law in `S₁`: the laws
`Measure.infinitePi P` for `P : ℕ → Measure 𝓧` with `P i ∈ S₁` for every `i`. -/
noncomputable def indepNull (S₁ : Set (Measure 𝓧)) : Set (Measure (ℕ → 𝓧)) :=
  Measure.infinitePi '' {P : ℕ → Measure 𝓧 | ∀ i, P i ∈ S₁}

/-- The null `indepNull S₁` as the image under `Measure.infinitePi` of the sequences of members
of `S₁`. -/
theorem indepNull_def (S₁ : Set (Measure 𝓧)) :
    indepNull S₁ = Measure.infinitePi '' {P : ℕ → Measure 𝓧 | ∀ i, P i ∈ S₁} :=
  (rfl)

@[simp]
theorem mem_indepNull {μ : Measure (ℕ → 𝓧)} :
    μ ∈ indepNull S₁ ↔ ∃ P : ℕ → Measure 𝓧, (∀ i, P i ∈ S₁) ∧ Measure.infinitePi P = μ :=
  Iff.rfl

theorem infinitePi_mem_indepNull {P : ℕ → Measure 𝓧} (hP : ∀ i, P i ∈ S₁) :
    Measure.infinitePi P ∈ indepNull S₁ :=
  mem_image_of_mem _ hP

/-- A property holds for every member of `indepNull S₁` exactly when it holds for the law
`Measure.infinitePi P` of every sequence `P` of members of `S₁`. -/
theorem forall_mem_indepNull {p : Measure (ℕ → 𝓧) → Prop} :
    (∀ μ ∈ indepNull S₁, p μ) ↔
      ∀ P : ℕ → Measure 𝓧, (∀ i, P i ∈ S₁) → p (Measure.infinitePi P) :=
  forall_mem_image

@[gcongr]
theorem indepNull_mono (hST : S₁ ⊆ T₁) : indepNull S₁ ⊆ indepNull T₁ :=
  image_mono fun _ hP i ↦ hST (hP i)

@[simp]
theorem indepNull_empty : indepNull (∅ : Set (Measure 𝓧)) = ∅ := by
  simp [indepNull]

@[simp]
theorem indepNull_singleton (P : Measure 𝓧) :
    indepNull {P} = {Measure.infinitePi fun _ : ℕ ↦ P} := by
  ext μ
  simp only [mem_indepNull, mem_singleton_iff]
  refine ⟨?_, fun h ↦ ⟨fun _ ↦ P, fun _ ↦ rfl, h.symm⟩⟩
  rintro ⟨Q, hQ, rfl⟩
  rw [show Q = fun _ ↦ P from funext hQ]

/-- The members of the independent null of a null of probability measures are probability
measures. -/
theorem isProbabilityMeasure_of_mem_indepNull (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) :
    ∀ μ ∈ indepNull S₁, IsProbabilityMeasure μ := by
  rintro _ ⟨P, hP, rfl⟩
  have := fun i ↦ hS₁ (P i) (hP i)
  infer_instance

/-- Every member of the independent null of any null has mass at most one: the infinite product
is a probability measure when every factor is one, and `0` otherwise. -/
theorem measure_univ_le_one_of_mem_indepNull (S₁ : Set (Measure 𝓧)) :
    ∀ μ ∈ indepNull S₁, μ univ ≤ 1 := by
  rintro _ ⟨P, -, rfl⟩
  by_cases h : ∀ i, IsProbabilityMeasure (P i)
  · exact prob_le_one
  · obtain ⟨i, hi⟩ := not_forall.1 h
    simp [Measure.infinitePi_eq_zero_of_not_isProbabilityMeasure hi]

/-- An i.i.d. sequence with law in `S₁` is an independent sequence with laws in `S₁`. -/
theorem iidNull_subset_indepNull (S₁ : Set (Measure 𝓧)) : iidNull S₁ ⊆ indepNull S₁ := by
  rintro _ ⟨P, hP, rfl⟩
  exact infinitePi_mem_indepNull fun _ ↦ hP

/-- Every member of the i.i.d. null of any null has mass at most one. -/
theorem measure_univ_le_one_of_mem_iidNull (S₁ : Set (Measure 𝓧)) :
    ∀ μ ∈ iidNull S₁, μ univ ≤ 1 :=
  fun μ hμ ↦ measure_univ_le_one_of_mem_indepNull S₁ μ (iidNull_subset_indepNull S₁ hμ)

/-- For a null of probability measures, the first `n` terms `initSeg n` of the sequences of
`iidNull S₁` have the laws of `sampleNull S₁ n`. Without the probability measures this fails: the
i.i.d. law of a measure of mass `2` is `0`, while its product law on `Fin n → 𝓧` has mass
`2 ^ n`. -/
theorem mapNull_initSeg_iidNull (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (n : ℕ) :
    mapNull (initSeg n) (iidNull S₁) = sampleNull S₁ n := by
  rw [iidNull, mapNull, image_image]
  refine image_congr fun P hP ↦ ?_
  have := hS₁ P hP
  exact (measurePreserving_initSeg P n).map_eq

end Sample

end ProbabilityTheory
