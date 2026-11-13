/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Beta
public import TauCeti.Probability.Distributions.Beta.Basic

/-!
# Beta laws: integer moments

The mixed integer moments `∫ u ^ k (1 - u) ^ m d Beta(a, b) = B(a + k, b + m) / B(a, b)` of the
beta laws, the natural-power case of Tau Ceti's
`TauCeti.Probability.integral_rpow_mul_one_sub_rpow_betaMeasure`. They are the likelihoods of
Bernoulli samples mixed over a beta prior on the mean, such as the Krichevsky–Trofimov mixture.

## Main statements

* `LMLExplore.integral_pow_mul_one_sub_pow_betaMeasure`: the moments
  `∫ u ^ k (1 - u) ^ m d Beta(a, b) = B(a + k, b + m) / B(a, b)` of the beta laws, and
  `LMLExplore.integral_pow_mul_one_sub_pow_betaMeasure_pos`: they are positive.

This file is adapted from `InformationTheory/KrichevskyTrofimov.lean` of the formalization in
RemyDegenne/Garivier2016Optimal (commit 53ac67e4, directory `ForLMLExplore/`).
-/

public section

open MeasureTheory ProbabilityTheory Real

namespace LMLExplore

/-- The moments of the beta laws: for `a, b > 0` and `k, m : ℕ`,
`∫ u ^ k (1 - u) ^ m d Beta(a, b) = B(a + k, b + m) / B(a, b)`. -/
lemma integral_pow_mul_one_sub_pow_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k m : ℕ) :
    ∫ u, u ^ k * (1 - u) ^ m ∂betaMeasure a b = beta (a + k) (b + m) / beta a b := by
  have h := TauCeti.Probability.integral_rpow_mul_one_sub_rpow_betaMeasure (q := k) (s := m)
    ha hb (by positivity) (by positivity)
  simpa only [Real.rpow_natCast] using h

/-- The moments `∫ u ^ k (1 - u) ^ m d Beta(a, b)` of the beta laws are positive, for `a, b > 0`. -/
lemma integral_pow_mul_one_sub_pow_betaMeasure_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k m : ℕ) : 0 < ∫ u, u ^ k * (1 - u) ^ m ∂betaMeasure a b := by
  rw [integral_pow_mul_one_sub_pow_betaMeasure ha hb]
  exact div_pos (beta_pos (by positivity) (by positivity)) (beta_pos ha hb)

end LMLExplore
