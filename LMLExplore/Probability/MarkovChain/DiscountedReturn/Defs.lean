/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import TauCeti.Probability.Process.PathLaw.Basic

/-!
# The discounted return along a path

For a reward function `f : α → ℝ` and a discount factor `γ`, the discounted return along a path
`ω : ℕ → α` is `G ω = ∑' t, γ ^ t * f (ω t)`. This file collects its path-level properties, which
use no probability: for `γ < 1` and a bounded reward the series is summable and bounded, it is a
measurable function of the path, and it satisfies the first-step decomposition
`G ω = f (ω 0) + γ G (θ ω)`, where `θ` shifts the path.

## Main definitions

* `LMLExplore.discountedReturn γ f ω`: the discounted return `∑' t, γ ^ t * f (ω t)` along a path.

## Main statements

* `LMLExplore.abs_discountedReturn_le`: `|G ω| ≤ C / (1 - γ)` for `|f| ≤ C`.
* `LMLExplore.measurable_discountedReturn`: the discounted return is measurable in the path.
* `LMLExplore.discountedReturn_eq_add_mul_shift`: the first-step decomposition
  `G ω = f (ω 0) + γ G (θ ω)`.
-/

public section

open TauCeti.Probability
open scoped NNReal

namespace LMLExplore

variable {α : Type*} {mα : MeasurableSpace α} {γ : ℝ≥0} {f : α → ℝ} {C : ℝ}

/-- The *discounted return* `∑' t, γ ^ t * f (ω t)` of a reward function `f : α → ℝ` along a path
`ω : ℕ → α`, with discount factor `γ`. -/
noncomputable def discountedReturn (γ : ℝ≥0) (f : α → ℝ) (ω : ℕ → α) : ℝ :=
  ∑' t, (γ : ℝ) ^ t * f (ω t)

lemma discountedReturn_def (γ : ℝ≥0) (f : α → ℝ) (ω : ℕ → α) :
    discountedReturn γ f ω = ∑' t, (γ : ℝ) ^ t * f (ω t) :=
  (rfl)

/-- For a reward bounded by `C`, the terms of the discounted return are dominated by the geometric
sequence `γ ^ t * C`. -/
private lemma norm_pow_mul_apply_le (hfC : ∀ x, |f x| ≤ C) (ω : ℕ → α) (t : ℕ) :
    ‖(γ : ℝ) ^ t * f (ω t)‖ ≤ (γ : ℝ) ^ t * C := by
  rw [norm_mul, norm_pow, NNReal.norm_eq, Real.norm_eq_abs]
  gcongr
  exact hfC _

/-- For `γ < 1` and a bounded reward, the series defining the discounted return is summable. -/
lemma summable_discountedReturn (hγ : γ < 1) (hfC : ∀ x, |f x| ≤ C) (ω : ℕ → α) :
    Summable fun t ↦ (γ : ℝ) ^ t * f (ω t) :=
  .of_norm_bounded ((summable_geometric_of_lt_one γ.coe_nonneg hγ).mul_right C)
    (norm_pow_mul_apply_le hfC ω)

/-- For `γ < 1` and a reward bounded by `C`, the discounted return is bounded by `C / (1 - γ)`. -/
theorem abs_discountedReturn_le (hγ : γ < 1) (hfC : ∀ x, |f x| ≤ C) (ω : ℕ → α) :
    |discountedReturn γ f ω| ≤ C / (1 - γ) := by
  have h_geom := (hasSum_geometric_of_lt_one γ.coe_nonneg hγ).mul_right C
  rw [← Real.norm_eq_abs, div_eq_inv_mul, discountedReturn_def]
  exact (summable_discountedReturn hγ hfC ω).hasSum.norm_le_of_bounded h_geom
    (norm_pow_mul_apply_le hfC ω)

/-- For `γ < 1` and a bounded measurable reward, the discounted return is a measurable function of
the path. -/
theorem measurable_discountedReturn (hγ : γ < 1) (hf : Measurable f) (hfC : ∀ x, |f x| ≤ C) :
    Measurable (discountedReturn γ f) := by
  refine measurable_of_tendsto_metrizable
    (f := fun n ω ↦ ∑ t ∈ Finset.range n, (γ : ℝ) ^ t * f (ω t)) (fun n ↦ ?_)
    (tendsto_pi_nhds.2 fun ω ↦ (summable_discountedReturn hγ hfC ω).hasSum.tendsto_sum_nat)
  exact Finset.measurable_sum _ fun t _ ↦ (hf.comp (measurable_pi_apply t)).const_mul _

/-- **First-step decomposition of the discounted return**: the return along `ω` is the first
reward plus `γ` times the return along the shifted path `θ ω = (ω (t + 1))ₜ`. -/
theorem discountedReturn_eq_add_mul_shift (hγ : γ < 1) (hfC : ∀ x, |f x| ≤ C) (ω : ℕ → α) :
    discountedReturn γ f ω = f (ω 0) + γ * discountedReturn γ f (shift α ω) := by
  rw [discountedReturn_def, (summable_discountedReturn hγ hfC ω).tsum_eq_zero_add,
    discountedReturn_def, ← tsum_mul_left]
  simp [shift_apply, pow_succ, mul_assoc, mul_left_comm]

end LMLExplore
