/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

import LMLExplore.Basic.ENNReal.BigOperators
import LMLExplore.MeasureTheory.Constructions.Pi
import LMLExplore.MeasureTheory.Measure.TotalVariation.Basic

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
* `MeasureTheory.etvDist_pi_const_le_card_mul`: the distance between the `ι`-fold products of two
  probability measures is at most `Fintype.card ι` times the distance between them.

## Implementation notes

The proof goes through a common minorant of two finite measures
(`MeasureTheory.exists_le_le_add_etvDist`): on a Hahn decomposition `s` of `(μ, ν)`, the measure
`ρ = μ.restrict s + ν.restrict sᶜ` is below `μ` and `ν`, with
`μ univ + ν univ = 2 * ρ univ + etvDist μ ν`. For probability measures the product of
the minorants is below both products (`MeasureTheory.Measure.pi_mono`) and has mass
`∏ i, ρ i univ`, so the distance between the products is at most
`2 * (1 - ∏ i, ρ i univ) ≤ ∑ i, 2 * (1 - ρ i univ)` (`ENNReal.one_sub_prod_le_sum_one_sub`).

The argument, common minorants and the bound `1 - ∏ i, m i ≤ ∑ i, (1 - m i)`, is adapted from
the Lean proof of [EVR26, Note 22] in `EValuesResearch/Results/PowerlessNulls.lean`
(commit `dd4072f`) of the paper project `RemyDegenne/evalues_research`.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 22, and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}

/-- **Total variation distance between product measures.** The total variation distance between
two finite products of probability measures is at most the sum of the distances between the
factors. -/
theorem etvDist_pi_le_sum (μ ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] :
    etvDist (Measure.pi μ) (Measure.pi ν) ≤ ∑ i, etvDist (μ i) (ν i) := by
  choose ρ hρμ hρν hρ using fun i ↦ exists_le_le_add_etvDist (μ i) (ν i)
  have (i : ι) : IsFiniteMeasure (ρ i) := isFiniteMeasure_of_le (μ i) (hρμ i)
  calc etvDist (Measure.pi μ) (Measure.pi ν)
  _ ≤ etvDist (Measure.pi μ) (Measure.pi ρ) + etvDist (Measure.pi ρ) (Measure.pi ν) :=
    etvDist_triangle _ _ _
  _ = 2 * (1 - ∏ i, ρ i univ) := by
    rw [etvDist_of_ge (Measure.pi_mono hρμ), etvDist_of_le (Measure.pi_mono hρν)]
    simp [Measure.pi_univ, two_mul]
  _ ≤ 2 * ∑ i, (1 - ρ i univ) := by
    gcongr; exact ENNReal.one_sub_prod_le_sum_one_sub _ _
  _ = ∑ i, 2 * (1 - ρ i univ) := Finset.mul_sum _ _ _
  _ ≤ ∑ i, etvDist (μ i) (ν i) := by
    gcongr with i
    rw [ENNReal.mul_sub fun _ _ ↦ ENNReal.ofNat_ne_top, mul_one, tsub_le_iff_left]
    simpa [one_add_one_eq_two] using (hρ i).le

/-- **Total variation distance between i.i.d. products.** The distance between the `ι`-fold
products of two probability measures `μ` and `ν` is at most `Fintype.card ι * etvDist μ ν`. -/
theorem etvDist_pi_const_le_card_mul {Y : Type*} {mY : MeasurableSpace Y} (μ ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    etvDist (Measure.pi fun _ : ι ↦ μ) (Measure.pi fun _ : ι ↦ ν) ≤
      Fintype.card ι * etvDist μ ν :=
  (etvDist_pi_le_sum _ _).trans_eq (by simp)

end MeasureTheory
