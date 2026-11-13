/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Moments.IntegrableExpMul
public import TauCeti.Probability.Distributions.Poisson.Basic

/-!
# Poisson laws: exponential moments

The count under the Poisson law `Po(r)` on `ℕ` has the moment generating function
`η ↦ exp (r (exp η - 1))`, finite for every `η`, hence the cumulant generating function
`η ↦ r (exp η - 1)`. Tau Ceti states these facts for the identity under the real-valued law
`Po(ℝ, r) = (poissonMeasure r).map Nat.cast` (`TauCeti.Probability.mgf_id_map_cast_poissonMeasure`,
`TauCeti.Probability.cgf_id_map_cast_poissonMeasure` and
`TauCeti.Probability.integrableExpSet_id_map_cast_poissonMeasure`); this file transfers them to the
count through `ProbabilityTheory.mgf_id_map`, `LMLExplore.cgf_id_map` and
`LMLExplore.integrableExpSet_id_map`. Tilting `Po(r)` by `n ↦ η n` multiplies its rate by `exp η`:
that is Tau Ceti's `TauCeti.Probability.poissonMeasure_tilted_mul`.

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
  congrFun ((mgf_id_map .of_discrete).symm.trans
    (TauCeti.Probability.mgf_id_map_cast_poissonMeasure r)) η

/-- The cumulant generating function of the count under `Po(r)` is `η ↦ r (exp η - 1)`. -/
@[simp]
theorem cgf_natCast_poissonMeasure (r : ℝ≥0) (η : ℝ) :
    cgf (Nat.cast : ℕ → ℝ) (poissonMeasure r) η = r * (exp η - 1) :=
  congrFun ((cgf_id_map .of_discrete).symm.trans
    (TauCeti.Probability.cgf_id_map_cast_poissonMeasure r)) η

/-- Every exponential moment of the count under `Po(r)` is finite. -/
@[simp]
theorem integrableExpSet_natCast_poissonMeasure (r : ℝ≥0) :
    integrableExpSet (Nat.cast : ℕ → ℝ) (poissonMeasure r) = univ :=
  (integrableExpSet_id_map .of_discrete).symm.trans
    (TauCeti.Probability.integrableExpSet_id_map_cast_poissonMeasure r)

end LMLExplore
