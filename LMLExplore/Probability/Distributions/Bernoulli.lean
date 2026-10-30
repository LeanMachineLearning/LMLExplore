/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Boundedness and sub-Gaussianity of real Bernoulli laws

The real two-point law `Ber(x, y, p)` is supported on the interval between `x` and `y`, hence, by
Hoeffding's lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`), it is
`(|x - y| / 2) ^ 2`-sub-Gaussian around its mean `p x + (1 - p) y`. For `Ber((1 : ℝ), 0, p)` these
are the two noise assumptions (rewards in `[0, 1]` and `1 / 4`-sub-Gaussian rewards) under which
stochastic bandit algorithms are analysed.

## Main statements

* `LMLExplore.ae_mem_uIcc_bernoulliMeasure`: `Ber(x, y, p)`-almost every point lies in
  `Set.uIcc x y`.
* `LMLExplore.hasSubgaussianMGF_bernoulliMeasure`: `Ber(x, y, p)` is
  `(|x - y| / 2) ^ 2`-sub-Gaussian around `p x + (1 - p) y`.
-/

public section

open MeasureTheory ProbabilityTheory

open scoped NNReal ProbabilityTheory unitInterval

namespace LMLExplore

/-- Almost every point of the real Bernoulli law `Ber(x, y, p)` lies between `x` and `y`. -/
lemma ae_mem_uIcc_bernoulliMeasure (x y : ℝ) (p : I) :
    ∀ᵐ z ∂Ber(x, y, p), z ∈ Set.uIcc x y := by
  rw [ae_iff]
  exact bernoulliMeasure_apply_of_notMem_of_notMem p measurableSet_uIcc.compl (by simp) (by simp)

/-- The real Bernoulli law `Ber(x, y, p)` is `(|x - y| / 2) ^ 2`-sub-Gaussian around its mean
`p x + (1 - p) y`. -/
lemma hasSubgaussianMGF_bernoulliMeasure (x y : ℝ) (p : I) :
    HasSubgaussianMGF (fun z ↦ z - (p * x + (1 - p) * y)) ((‖x - y‖₊ / 2) ^ 2) Ber(x, y, p) := by
  have h := hasSubgaussianMGF_of_mem_Icc aemeasurable_id (ae_mem_uIcc_bernoulliMeasure x y p)
  have hc : ‖x ⊔ y - x ⊓ y‖₊ = ‖x - y‖₊ := by
    ext
    simp [max_sub_min_eq_abs']
  simpa only [id_eq, integral_bernoulliMeasure, smul_eq_mul, hc] using h

end LMLExplore
