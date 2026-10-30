/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import TauCeti.Probability.Distributions.Bernoulli.Basic

/-!
# Boundedness and sub-Gaussianity of the real Bernoulli law

The real-valued Bernoulli law `Ber((1 : ℝ), 0, p)` is supported on `[0, 1]`, hence, by Hoeffding's
lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`), it is `1 / 4`-sub-Gaussian around its
mean `p`. These are the two noise assumptions (bounded rewards and sub-Gaussian rewards) under which
stochastic bandit algorithms are analysed.

## Main statements

* `LMLExplore.ae_mem_Icc_bernoulliMeasure`: `Ber((1 : ℝ), 0, p)`-almost every point lies in
  `[0, 1]`.
* `LMLExplore.hasSubgaussianMGF_bernoulliMeasure`: `Ber((1 : ℝ), 0, p)` is `1 / 4`-sub-Gaussian
  around `p`.
-/

public section

open MeasureTheory ProbabilityTheory

open scoped NNReal ProbabilityTheory unitInterval

namespace LMLExplore

/-- Almost every point of the real Bernoulli law `Ber((1 : ℝ), 0, p)` lies in `[0, 1]`. -/
lemma ae_mem_Icc_bernoulliMeasure (p : I) : ∀ᵐ x ∂Ber((1 : ℝ), 0, p), x ∈ Set.Icc 0 1 := by
  rw [ae_iff]
  exact bernoulliMeasure_apply_of_notMem_of_notMem p measurableSet_Icc.compl (by simp) (by simp)

/-- The real Bernoulli law `Ber((1 : ℝ), 0, p)` is `1 / 4`-sub-Gaussian around its mean `p`. -/
lemma hasSubgaussianMGF_bernoulliMeasure (p : I) :
    HasSubgaussianMGF (fun x ↦ x - p) (1 / 4) Ber((1 : ℝ), 0, p) := by
  have h := hasSubgaussianMGF_of_mem_Icc aemeasurable_id (ae_mem_Icc_bernoulliMeasure p)
  have hc : (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 = 1 / 4 := by
    ext
    norm_num
  simpa only [id_eq, TauCeti.Probability.integral_id_bernoulliMeasure, hc] using h

end LMLExplore
