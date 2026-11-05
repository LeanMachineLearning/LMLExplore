/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.SubGaussian

/-!
# Sub-Gaussianity of variables with values in `[0, 1]`

By Hoeffding's lemma `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`, a random variable with
values in `[a, b]` is `((b - a) / 2) ^ 2`-sub-Gaussian around its mean. We record the case
`[0, 1]`, with the constant `1 / 4`, which is the form used by the bandit algorithms for rewards
in `[0, 1]`.

## Main statements

* `LMLExplore.hasSubgaussianMGF_of_mem_Icc_zero_one`: a random variable with values in `[0, 1]`
  is `1 / 4`-sub-Gaussian around its mean.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LMLExplore

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ}

/-- **Hoeffding's lemma on `[0, 1]`**: a random variable with values in `[0, 1]` is
`1 / 4`-sub-Gaussian around its mean. -/
lemma hasSubgaussianMGF_of_mem_Icc_zero_one (hm : AEMeasurable X μ)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) :
    HasSubgaussianMGF (fun ω ↦ X ω - μ[X]) (1 / 4) μ := by
  have hσ : (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 = 1 / 4 := by
    ext
    norm_num
  exact hσ ▸ hasSubgaussianMGF_of_mem_Icc hm hb

end LMLExplore
