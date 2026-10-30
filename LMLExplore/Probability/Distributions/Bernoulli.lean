/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Distributions.Bernoulli
public import LMLExplore.Topology.UnitInterval

/-!
# Bernoulli laws: symmetry, absolute continuity, boundedness and sub-Gaussianity

Exchanging the two points of a Bernoulli law `Ber(x, y, p)` replaces `p` by `1 - p`, and for
`x ≠ y`, `Ber(x, y, p) ≪ Ber(x, y, q)` exactly when `p` puts no mass on a point that `q` ignores.

The real two-point law `Ber(x, y, p)` is supported on the interval between `x` and `y`, hence, by
Hoeffding's lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`), it is
`(|x - y| / 2) ^ 2`-sub-Gaussian around its mean `p x + (1 - p) y`. For `Ber((1 : ℝ), 0, p)` these
are the two noise assumptions (rewards in `[0, 1]` and `1 / 4`-sub-Gaussian rewards) under which
stochastic bandit algorithms are analysed.

## Main statements

* `ProbabilityTheory.bernoulliMeasure_symm`: `Ber(x, y, 1 - p) = Ber(y, x, p)`.
* `ProbabilityTheory.bernoulliMeasure_absolutelyContinuous_iff`: for `x ≠ y`,
  `Ber(x, y, p) ≪ Ber(x, y, q)` if and only if `q = 0 → p = 0` and `q = 1 → p = 1`.
* `LMLExplore.ae_mem_uIcc_bernoulliMeasure`: `Ber(x, y, p)`-almost every point lies in
  `Set.uIcc x y`.
* `LMLExplore.hasSubgaussianMGF_bernoulliMeasure`: `Ber(x, y, p)` is
  `(|x - y| / 2) ^ 2`-sub-Gaussian around `p x + (1 - p) y`.
-/

public section

open MeasureTheory ProbabilityTheory

open scoped NNReal ProbabilityTheory unitInterval

namespace ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] {x y : X} {p q : I}

/-- Exchanging the two points of a Bernoulli law replaces its parameter `p` by `1 - p`. -/
theorem bernoulliMeasure_symm (x y : X) (p : I) : Ber(x, y, σ p) = Ber(y, x, p) := by
  rw [bernoulliMeasure_def, bernoulliMeasure_def, unitInterval.symm_symm, add_comm]

/-- A Bernoulli law is absolutely continuous with respect to the Bernoulli law on the same two
points with parameter `q` whenever it puts no mass on a point that the second law ignores. -/
theorem bernoulliMeasure_absolutelyContinuous (h0 : q = 0 → p = 0) (h1 : q = 1 → p = 1) :
    Ber(x, y, p) ≪ Ber(x, y, q) := by
  classical
  refine Measure.AbsolutelyContinuous.mk fun s hs hνs ↦ ?_
  rw [bernoulliMeasure_apply q hs] at hνs
  rw [bernoulliMeasure_apply p hs]
  split_ifs at hνs ⊢ with hx hy hy
  · simp at hνs
  · rw [ENNReal.coe_eq_zero, unitInterval.toNNReal_eq_zero] at hνs ⊢
    exact h0 hνs
  · rw [ENNReal.coe_eq_zero, unitInterval.toNNReal_eq_zero, unitInterval.symm_eq_zero] at hνs ⊢
    exact h1 hνs
  · rfl

/-- Absolute continuity between two Bernoulli laws on two distinct points: `Ber(x, y, p)` is
absolutely continuous with respect to `Ber(x, y, q)` if and only if `p` vanishes when `q` does
and `p = 1` when `q = 1`. -/
theorem bernoulliMeasure_absolutelyContinuous_iff [MeasurableSingletonClass X] (hxy : x ≠ y) :
    Ber(x, y, p) ≪ Ber(x, y, q) ↔ (q = 0 → p = 0) ∧ (q = 1 → p = 1) := by
  refine ⟨fun h ↦ ⟨fun hq ↦ ?_, fun hq ↦ ?_⟩,
    fun h ↦ bernoulliMeasure_absolutelyContinuous h.1 h.2⟩
  · simpa [hxy.symm] using h (s := {x}) (by simp [hq, hxy.symm])
  · simpa [hxy, unitInterval.symm_eq_zero] using h (s := {y}) (by simp [hq, hxy])

end ProbabilityTheory

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
