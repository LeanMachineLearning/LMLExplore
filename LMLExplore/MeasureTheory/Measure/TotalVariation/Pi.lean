/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
import Statlib.ForMathlib.MeasureTheory.Measure.Decomposition.RNDerivProd

/-!
# Total variation distance between product measures

The total variation distance between two finite products of probability measures is at most the
sum of the distances between the factors:

```text
etvDist (Measure.pi μ) (Measure.pi ν) ≤ ∑ i, etvDist (μ i) (ν i).
```

In particular `n` independent observations of `μ` and of `ν` are at distance at most
`n * etvDist μ ν`, so that the `n`-fold products of a sequence of laws that converges to `ν` in
total variation converge to the `n`-fold product of `ν`.

## Main statements

* `MeasureTheory.etvDist_pi_le_sum`: the total variation distance between products of
  probability measures is at most the sum of the distances between the factors.

## Implementation notes

The proof goes through a common minorant of two finite measures: on a Hahn decomposition `s` of
`(μ, ν)`, the measure `ρ = μ.restrict s + ν.restrict sᶜ` is below `μ` and `ν`, with
`μ univ + ν univ = 2 * ρ univ + etvDist μ ν`. For probability measures the product of
the minorants is below both products and has mass `∏ i, ρ i univ`, so the distance between the
products is at most `2 * (1 - ∏ i, ρ i univ) ≤ ∑ i, 2 * (1 - ρ i univ)`.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}

/-- The product of finite measures is monotone in each factor. -/
private lemma pi_mono {μ ν : ∀ i, Measure (X i)} [∀ i, IsFiniteMeasure (ν i)]
    (h : ∀ i, μ i ≤ ν i) :
    Measure.pi μ ≤ Measure.pi ν := by
  have (i : ι) : IsFiniteMeasure (μ i) := isFiniteMeasure_of_le (ν i) (h i)
  rw [Measure.pi_eq_withDensity_prod_rnDeriv fun i ↦ Measure.absolutelyContinuous_of_le (h i)]
  calc (Measure.pi ν).withDensity (fun x ↦ ∏ i, (μ i).rnDeriv (ν i) (x i))
  _ ≤ (Measure.pi ν).withDensity 1 := by
    refine withDensity_mono ?_
    filter_upwards [Measure.ae_le_pi fun i ↦ Measure.rnDeriv_le_one_of_le (h i)] with x hx
    exact Finset.prod_le_one fun i _ ↦ hx i
  _ = Measure.pi ν := withDensity_one

/-- A common minorant of two finite measures: on a Hahn decomposition `s`, the measure
`μ.restrict s + ν.restrict sᶜ` is below `μ` and `ν`, and its mass is the mean of the masses of `μ`
and `ν` minus half their total variation distance. -/
private lemma exists_le_le_add_etvDist {α : Type*} {mα : MeasurableSpace α} (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∃ ρ : Measure α, ρ ≤ μ ∧ ρ ≤ ν ∧ μ univ + ν univ = 2 * ρ univ + etvDist μ ν := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  refine ⟨μ.restrict s + ν.restrict sᶜ, ?_, ?_, ?_⟩
  · calc μ.restrict s + ν.restrict sᶜ ≤ μ.restrict s + μ.restrict sᶜ :=
          add_le_add le_rfl hs.ge_on_compl
    _ = μ := Measure.restrict_add_restrict_compl hs.measurableSet
  · calc μ.restrict s + ν.restrict sᶜ ≤ ν.restrict s + ν.restrict sᶜ :=
          add_le_add hs.le_on le_rfl
    _ = ν := Measure.restrict_add_restrict_compl hs.measurableSet
  · obtain ⟨a, ha⟩ := le_iff_exists_add.1 (by simpa using hs.le_on univ : μ s ≤ ν s)
    obtain ⟨b, hb⟩ := le_iff_exists_add.1 (by simpa using hs.ge_on_compl univ : ν sᶜ ≤ μ sᶜ)
    rw [hs.etvDist_eq, add_apply, Measure.restrict_apply_univ, Measure.restrict_apply_univ,
      ← measure_add_measure_compl hs.measurableSet (μ := μ),
      ← measure_add_measure_compl hs.measurableSet (μ := ν), ha, hb,
      ENNReal.add_sub_cancel_left (measure_ne_top μ s),
      ENNReal.add_sub_cancel_left (measure_ne_top ν sᶜ)]
    ring

/-- For numbers in `[0, 1]`, one minus their product is at most the sum of the numbers `1 - m i`:
the union bound for independent events of probabilities `1 - m i`. -/
private lemma one_sub_prod_le_sum_one_sub {κ : Type*} (s : Finset κ) {m : κ → ℝ≥0∞}
    (hm : ∀ i ∈ s, m i ≤ 1) :
    1 - ∏ i ∈ s, m i ≤ ∑ i ∈ s, (1 - m i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    have hmj : m j ≤ 1 := hm j (Finset.mem_insert_self j s)
    have hms : ∀ i ∈ s, m i ≤ 1 := fun i hi ↦ hm i (Finset.mem_insert_of_mem hi)
    have hprod : ∏ i ∈ s, m i ≤ 1 := Finset.prod_le_one hms
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    calc 1 - m j * ∏ i ∈ s, m i ≤ (1 - m j) + (1 - ∏ i ∈ s, m i) := by
          refine tsub_le_iff_right.2 ?_
          calc (1 : ℝ≥0∞) = (1 - m j) + m j * ((1 - ∏ i ∈ s, m i) + ∏ i ∈ s, m i) := by
                rw [tsub_add_cancel_of_le hprod, mul_one, tsub_add_cancel_of_le hmj]
          _ = (1 - m j) + (m j * (1 - ∏ i ∈ s, m i) + m j * ∏ i ∈ s, m i) := by rw [mul_add]
          _ ≤ (1 - m j) + ((1 - ∏ i ∈ s, m i) + m j * ∏ i ∈ s, m i) := by
                gcongr; exact mul_le_of_le_one_left' hmj
          _ = (1 - m j) + (1 - ∏ i ∈ s, m i) + m j * ∏ i ∈ s, m i := (add_assoc _ _ _).symm
    _ ≤ (1 - m j) + ∑ i ∈ s, (1 - m i) := by gcongr; exact ih hms

/-- **Total variation distance between product measures.** The total variation distance between
two finite products of probability measures is at most the sum of the distances between the
factors. -/
theorem etvDist_pi_le_sum (μ ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] :
    etvDist (Measure.pi μ) (Measure.pi ν) ≤ ∑ i, etvDist (μ i) (ν i) := by
  choose ρ hρμ hρν hρ using fun i ↦ exists_le_le_add_etvDist (μ i) (ν i)
  have (i : ι) : IsFiniteMeasure (ρ i) := isFiniteMeasure_of_le (μ i) (hρμ i)
  have hm (i : ι) : ρ i univ ≤ 1 := (hρμ i univ).trans prob_le_one
  calc etvDist (Measure.pi μ) (Measure.pi ν)
  _ ≤ etvDist (Measure.pi μ) (Measure.pi ρ) + etvDist (Measure.pi ρ) (Measure.pi ν) :=
    etvDist_triangle _ _ _
  _ = 2 * (1 - ∏ i, ρ i univ) := by
    rw [etvDist_of_ge (pi_mono hρμ), etvDist_of_le (pi_mono hρν)]
    simp [Measure.pi_univ, two_mul]
  _ ≤ 2 * ∑ i, (1 - ρ i univ) := by
    gcongr; exact one_sub_prod_le_sum_one_sub _ fun i _ ↦ hm i
  _ = ∑ i, 2 * (1 - ρ i univ) := Finset.mul_sum _ _ _
  _ ≤ ∑ i, etvDist (μ i) (ν i) := by
    gcongr with i
    rw [ENNReal.mul_sub fun _ _ ↦ ENNReal.ofNat_ne_top, mul_one, tsub_le_iff_left]
    simpa [one_add_one_eq_two] using (hρ i).le

end MeasureTheory
