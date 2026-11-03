/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted
public import TauCeti.Probability.Distributions.Poisson.Basic

/-!
# Poisson laws: exponential moments and tilting

The count under the Poisson law `Po(r)` on `ℕ` has the moment generating function
`η ↦ exp (r (exp η - 1))`, finite for every `η`, hence the cumulant generating function
`η ↦ r (exp η - 1)`. Tilting `Po(r)` by `n ↦ η n` multiplies its rate by `exp η`.

## Main statements

* `LMLExplore.mgf_natCast_poissonMeasure`, `LMLExplore.cgf_natCast_poissonMeasure`: the moment and
  cumulant generating functions of the count under `Po(r)`.
* `LMLExplore.integrableExpSet_natCast_poissonMeasure`: every exponential moment of the count under
  `Po(r)` is finite.
* `LMLExplore.tilted_mul_natCast_poissonMeasure`: `Po(r)` tilted by `n ↦ η n` is `Po(r exp η)`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set

open scoped NNReal ENNReal Nat

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

/-- Tilting a Poisson law by `n ↦ η n` multiplies its rate by `exp η`. -/
@[simp]
theorem tilted_mul_natCast_poissonMeasure (r : ℝ≥0) (η : ℝ) :
    (poissonMeasure r).tilted (fun n ↦ η * n) = poissonMeasure (r * exp η).toNNReal := by
  have hr : ((r * exp η).toNNReal : ℝ) = r * exp η := coe_toNNReal _ (by positivity)
  refine Measure.ext_of_singleton fun n ↦ ?_
  have h_mgf : ∫ k : ℕ, exp (η * k) ∂(poissonMeasure r) = exp (r * (exp η - 1)) := by
    simpa only [mgf] using mgf_natCast_poissonMeasure r η
  rw [tilted_apply, lintegral_singleton, h_mgf, poissonMeasure_singleton, poissonMeasure_singleton,
    hr, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  -- `exp (η n) / exp (r (exp η - 1)) * (exp (-r) r ^ n / n!) = exp (-(r exp η)) (r exp η) ^ n / n!`
  rw [mul_pow, ← exp_nat_mul, mul_comm (n : ℝ) η]
  have h : exp (-(r * exp η)) = exp (-r) / exp (r * (exp η - 1)) := by
    rw [← exp_sub]
    ring_nf
  rw [h]
  field_simp

end LMLExplore
