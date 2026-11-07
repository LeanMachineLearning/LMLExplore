/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import TauCeti.Probability.Distributions.Poisson.Basic

/-!
# Poisson laws: exponential moments

The count under the Poisson law `Po(r)` on `ℕ` has the moment generating function
`η ↦ exp (r (exp η - 1))`, finite for every `η`, hence the cumulant generating function
`η ↦ r (exp η - 1)`. Tilting `Po(r)` by `n ↦ η n` multiplies its rate by `exp η`: that is
Tau Ceti's `TauCeti.Probability.poissonMeasure_tilted_mul`.

## Main statements

* `LMLExplore.mgf_natCast_poissonMeasure`, `LMLExplore.cgf_natCast_poissonMeasure`: the moment and
  cumulant generating functions of the count under `Po(r)`.
* `LMLExplore.integrableExpSet_natCast_poissonMeasure`: every exponential moment of the count under
  `Po(r)` is finite.
-/

public section

open MeasureTheory ProbabilityTheory Real Set

open scoped NNReal

namespace LMLExplore

/-- The moment generating function of the count under `Po(r)` is `η ↦ exp (r (exp η - 1))`. -/
@[simp]
lemma mgf_natCast_poissonMeasure (r : ℝ≥0) (η : ℝ) :
    mgf (Nat.cast : ℕ → ℝ) (poissonMeasure r) η = exp (r * (exp η - 1)) :=
  (TauCeti.Probability.pgf_exp id _ η).symm.trans (TauCeti.Probability.pgf_poissonMeasure r _)

/-- The cumulant generating function of the count under `Po(r)` is `η ↦ r (exp η - 1)`. -/
@[simp]
theorem cgf_natCast_poissonMeasure (r : ℝ≥0) (η : ℝ) :
    cgf (Nat.cast : ℕ → ℝ) (poissonMeasure r) η = r * (exp η - 1) := by
  rw [cgf, mgf_natCast_poissonMeasure, log_exp]

/-- Every exponential moment of the count under `Po(r)` is finite. -/
@[simp]
theorem integrableExpSet_natCast_poissonMeasure (r : ℝ≥0) :
    integrableExpSet (Nat.cast : ℕ → ℝ) (poissonMeasure r) = univ :=
  eq_univ_of_forall fun η ↦ by
    rw [integrableExpSet, mem_ofPred_eq, ← mgf_pos_iff, mgf_natCast_poissonMeasure]
    exact exp_pos _

end LMLExplore
