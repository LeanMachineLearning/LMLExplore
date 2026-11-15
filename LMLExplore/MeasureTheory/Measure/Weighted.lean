/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Simplex
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Weighted measures on a finite type

`weightedMeasure p = ∑ i, p i • δ_i` is the measure on a finite type `ι` with (real) weights `p`
(negative weights are replaced by `0`). The map `p ↦ weightedMeasure p` is measurable, which
allows building kernels that sample from a computed distribution, such as the policies of
weight-based bandit algorithms.

The definition of `weightedMeasure` and its basic API (masses of sets and atoms, finiteness,
probability, absolute continuity, lower integrals and measurability) are adapted from the
LMLPapers project. `isProbabilityMeasure_sum_smul_dirac` and `sum_smul_dirac_compl_eq_zero` are
adapted from the Lean proof in `EValuesResearch/Results/SubGaussianCompleteClass.lean` and
`EValuesResearch/Results/SubGaussianCompleteClassAux.lean` (commit `dd4072f`) of the paper project
`RemyDegenne/evalues_research`.

## Main definitions

* `LMLExplore.weightedMeasure p = ∑ i, ENNReal.ofReal (p i) • δ_i`.

## Main statements

* `weightedMeasure_def`: `weightedMeasure p` as a sum of weighted Dirac measures;
* `weightedMeasure_apply`, `weightedMeasure_singleton`, `measureReal_weightedMeasure_singleton`:
  the masses of sets and of atoms;
* `measureReal_weightedMeasure_singleton_of_mem_simplex`: for `p ∈ simplex ι`, the atom `{i}`
  has probability `p i`;
* `isFiniteMeasure_weightedMeasure`: a weighted measure is finite (an instance);
* `isProbabilityMeasure_weightedMeasure`: it is a probability measure for a probability vector
  `p ∈ simplex ι`;
* `weightedMeasure_absolutelyContinuous`: `weightedMeasure q ≪ weightedMeasure p` when the support
  of `q` is contained in that of `p`;
* `lintegral_weightedMeasure_eq_sum`, `integral_weightedMeasure_eq_sum`: integrals against
  `weightedMeasure p` are weighted sums;
* `measurable_weightedMeasure`: `p ↦ weightedMeasure p` is measurable;
* `integral_sum_smul_dirac`: the integral against a finite sum `∑ k, w k • δ_{x k}` of weighted
  Dirac measures at points of any measurable space is the weighted sum `∑ k, w k • f (x k)`;
* `lintegral_sum_smul_dirac`: the same for lower integrals of any function, measurable or not,
  in a space with measurable singletons;
* `isProbabilityMeasure_sum_smul_dirac`: such a sum is a probability measure when the weights are
  nonnegative and sum to `1`;
* `sum_smul_dirac_compl_eq_zero`: such a sum gives no mass outside a finite set containing the
  points `x k`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace LMLExplore

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] {p q : ι → ℝ}

/-- The measure on `ι` with weights `p`: `∑ i, p i • δ_i` (negative weights count as `0`). -/
noncomputable def weightedMeasure (p : ι → ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac i

/-- `weightedMeasure p` is the sum of the Dirac masses `δ_i` weighted by `ENNReal.ofReal (p i)`. -/
lemma weightedMeasure_def (p : ι → ℝ) :
    weightedMeasure p = ∑ i, ENNReal.ofReal (p i) • Measure.dirac i :=
  (rfl)

/-- The mass of a measurable set under `weightedMeasure p`. -/
lemma weightedMeasure_apply (p : ι → ℝ) {s : Set ι} (hs : MeasurableSet s) :
    weightedMeasure p s = ∑ i, ENNReal.ofReal (p i) * s.indicator 1 i := by
  simp [weightedMeasure_def, Measure.dirac_apply' _ hs]

/-- The total mass of `weightedMeasure p`. -/
lemma weightedMeasure_univ (p : ι → ℝ) :
    weightedMeasure p Set.univ = ∑ i, ENNReal.ofReal (p i) := by
  simp [weightedMeasure_apply _ MeasurableSet.univ]

/-- The mass of an atom under `weightedMeasure p`. -/
@[simp]
lemma weightedMeasure_singleton [MeasurableSingletonClass ι] (p : ι → ℝ) (i : ι) :
    weightedMeasure p {i} = ENNReal.ofReal (p i) := by
  classical
  rw [weightedMeasure_apply p (measurableSet_singleton i)]
  simp [Set.indicator_apply]

/-- The real mass of an atom under `weightedMeasure p`, for nonnegative weights. -/
lemma measureReal_weightedMeasure_singleton [MeasurableSingletonClass ι] (hp : ∀ i, 0 ≤ p i)
    (i : ι) :
    (weightedMeasure p).real {i} = p i := by
  rw [measureReal_def, weightedMeasure_singleton, ENNReal.toReal_ofReal (hp i)]

/-- The probability of an atom under `weightedMeasure p`, for a probability vector
`p ∈ simplex ι`. -/
lemma measureReal_weightedMeasure_singleton_of_mem_simplex [MeasurableSingletonClass ι]
    (hp : p ∈ simplex ι) (i : ι) :
    (weightedMeasure p).real {i} = p i :=
  measureReal_weightedMeasure_singleton (mem_simplex_iff.1 hp).1 i

/-- A weighted measure is finite. -/
instance isFiniteMeasure_weightedMeasure (p : ι → ℝ) : IsFiniteMeasure (weightedMeasure p) :=
  ⟨by simp [weightedMeasure_univ, ENNReal.sum_lt_top]⟩

/-- The weighted measure of a probability vector is a probability measure. -/
lemma isProbabilityMeasure_weightedMeasure (hp : p ∈ simplex ι) :
    IsProbabilityMeasure (weightedMeasure p) := by
  rw [mem_simplex_iff] at hp
  constructor
  rw [weightedMeasure_univ, ← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hp.1 i), hp.2,
    ENNReal.ofReal_one]

/-- `weightedMeasure q ≪ weightedMeasure p` when the support of `q` is contained in that of
`p`. -/
lemma weightedMeasure_absolutelyContinuous [MeasurableSingletonClass ι]
    (hq : ∀ i, 0 < q i → 0 < p i) :
    weightedMeasure q ≪ weightedMeasure p := by
  intro s hs
  rw [weightedMeasure_apply q (s.toFinite.measurableSet)]
  rw [weightedMeasure_apply p (s.toFinite.measurableSet)] at hs
  rw [Finset.sum_eq_zero_iff] at hs ⊢
  intro i _
  have hi := hs i (Finset.mem_univ i)
  by_cases his : i ∈ s
  · simp only [Set.indicator_of_mem his, Pi.one_apply, mul_one, ENNReal.ofReal_eq_zero] at hi ⊢
    by_contra h
    exact absurd hi (not_le.2 (hq i (not_le.1 h)))
  · simp [Set.indicator_of_notMem his]

/-- The lower Lebesgue integral against `weightedMeasure p` is the weighted sum
`∑ x, ENNReal.ofReal (p x) * f x` (negative weights count as `0`). -/
lemma lintegral_weightedMeasure_eq_sum [MeasurableSingletonClass ι] (p : ι → ℝ) (f : ι → ℝ≥0∞) :
    ∫⁻ x, f x ∂(weightedMeasure p) = ∑ x, ENNReal.ofReal (p x) * f x := by
  simp [lintegral_fintype, mul_comm]

/-- For nonnegative weights, the integral of a function with values in a Banach space against
`weightedMeasure p` is the weighted sum `∑ x, p x • f x`. -/
lemma integral_weightedMeasure_eq_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSingletonClass ι] (hp : ∀ i, 0 ≤ p i) (f : ι → E) :
    ∫ x, f x ∂(weightedMeasure p) = ∑ x, p x • f x := by
  rw [integral_fintype Integrable.of_finite]
  simp [measureReal_weightedMeasure_singleton hp]

/-- The map `p ↦ weightedMeasure p` is measurable. -/
lemma measurable_weightedMeasure : Measurable (weightedMeasure (ι := ι)) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp_rw [weightedMeasure_apply _ hs]
  exact Finset.measurable_sum _ fun i _ ↦
    (ENNReal.measurable_ofReal.comp (measurable_pi_apply i)).mul measurable_const

/-- For nonnegative weights `w k` and points `x k` of a measurable space, the integral of a
strongly measurable function with values in a Banach space against `∑ k, w k • δ_{x k}` is the
weighted sum `∑ k, w k • f (x k)`. -/
lemma integral_sum_smul_dirac {α 𝓧 E : Type*} [Fintype α] [MeasurableSpace 𝓧]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : 𝓧 → E} {x : α → 𝓧}
    {w : α → ℝ} (hw : ∀ k, 0 ≤ w k) (hf : StronglyMeasurable f) :
    ∫ y, f y ∂(∑ k, ENNReal.ofReal (w k) • Measure.dirac (x k)) = ∑ k, w k • f (x k) := by
  have hint : ∀ k ∈ Finset.univ,
      Integrable f (ENNReal.ofReal (w k) • Measure.dirac (x k)) := fun k _ ↦
    (integrable_dirac' hf (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [integral_finsetSum_measure hint]
  simp_rw [integral_smul_measure, integral_dirac' _ _ hf, ENNReal.toReal_ofReal (hw _)]

/-- In a space with measurable singletons, the lower integral of any function against
`∑ k, w k • δ_{x k}` is the weighted sum `∑ k, w k * f (x k)`. -/
lemma lintegral_sum_smul_dirac {α 𝓧 : Type*} [Fintype α] [MeasurableSpace 𝓧]
    [MeasurableSingletonClass 𝓧] (w : α → ℝ) (x : α → 𝓧) (f : 𝓧 → ℝ≥0∞) :
    ∫⁻ y, f y ∂(∑ k, ENNReal.ofReal (w k) • Measure.dirac (x k)) =
      ∑ k, ENNReal.ofReal (w k) * f (x k) := by
  rw [lintegral_finsetSum_measure]
  simp [lintegral_smul_measure, lintegral_dirac]

/-- A finite sum `∑ k, w k • δ_{x k}` of weighted Dirac measures with nonnegative weights summing
to `1` is a probability measure. -/
lemma isProbabilityMeasure_sum_smul_dirac {α 𝓧 : Type*} [Fintype α] [MeasurableSpace 𝓧]
    {w : α → ℝ} (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) (x : α → 𝓧) :
    IsProbabilityMeasure (∑ k, ENNReal.ofReal (w k) • Measure.dirac (x k)) := by
  constructor
  simp [← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ hw k, hw1]

/-- A finite sum `∑ k, w k • δ_{x k}` of weighted Dirac measures at points of a finite set `s`
gives no mass to the complement of `s`. -/
lemma sum_smul_dirac_compl_eq_zero {α 𝓧 : Type*} [Fintype α] [MeasurableSpace 𝓧]
    [MeasurableSingletonClass 𝓧] {w : α → ℝ} {x : α → 𝓧} {s : Finset 𝓧} (hs : ∀ k, x k ∈ s) :
    (∑ k, ENNReal.ofReal (w k) • Measure.dirac (x k)) (↑s)ᶜ = 0 := by
  simp [Measure.dirac_apply' _ s.measurableSet.compl, hs]

end LMLExplore
