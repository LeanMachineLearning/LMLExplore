/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Distributions.Geometric
import TauCeti.Probability.Distributions.Geometric.Basic

/-!
# Geometric laws with a positive success probability

Mathlib's `geometricMeasure 0` is the point mass at `0`, as is `geometricMeasure 1`
(Tau Ceti's `TauCeti.Probability.geometricMeasure_zero` and
`TauCeti.Probability.geometricMeasure_one`), so every geometric law is one with a positive success
probability, for which Mathlib's `geometricMeasure_singleton` gives the masses of the points.

## Main statements

* `ProbabilityTheory.exists_ne_zero_geometricMeasure_eq`: every geometric law is one with a
  positive success probability.
* `ProbabilityTheory.geometricMeasure_singleton_zero_pos`: every geometric law charges `0`.
* `ProbabilityTheory.prod_geometricMeasure_singleton`: the mass of a point under a product of two
  geometric laws with positive success probabilities.
-/

public section

open MeasureTheory Set

namespace ProbabilityTheory

/-- Every geometric law is one with a positive success probability. -/
theorem exists_ne_zero_geometricMeasure_eq (p : unitInterval) :
    ∃ q : unitInterval, q ≠ 0 ∧ geometricMeasure q = geometricMeasure p := by
  by_cases hp : p = 0
  · exact ⟨1, one_ne_zero, by rw [hp, TauCeti.Probability.geometricMeasure_one,
      TauCeti.Probability.geometricMeasure_zero]⟩
  · exact ⟨p, hp, rfl⟩

/-- The point `0` has positive mass under every geometric law. -/
theorem geometricMeasure_singleton_zero_pos (p : unitInterval) : 0 < geometricMeasure p {0} := by
  obtain ⟨q, hq, hqp⟩ := exists_ne_zero_geometricMeasure_eq p
  rw [← hqp, geometricMeasure_singleton hq]
  simpa using unitInterval.pos_iff_ne_zero.mpr hq

/-- The mass of a point under a product of geometric laws with positive success
probabilities. -/
theorem prod_geometricMeasure_singleton {p₁ p₂ : unitInterval} (h₁ : p₁ ≠ 0) (h₂ : p₂ ≠ 0)
    (x : ℕ × ℕ) :
    (geometricMeasure p₁).prod (geometricMeasure p₂) {x} =
      ENNReal.ofReal ((1 - p₁) ^ x.1 * p₁ * ((1 - p₂) ^ x.2 * p₂)) := by
  rw [← singleton_prod_singleton, Measure.prod_prod, geometricMeasure_singleton h₁,
    geometricMeasure_singleton h₂, ← ENNReal.ofReal_mul (geometricMeasure_nonneg _ _)]

end ProbabilityTheory
