/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate

/-!
# When one observation attains the smallest relative entropy

For a probability measure `Q₁` and a null `S₁` on a measurable space, the maximal expected
logarithm `maxLogGrowth Q₁ S₁ n` of an `n`-sample e-variable is at least `n` times that of one
observation, by superadditivity, and at most `n` times the smallest relative entropy from `Q₁` to
the null. If one observation already attains the smallest relative entropy, that is, if
`⨅ P ∈ S₁, klDiv Q₁ P ≤ maxLogGrowth Q₁ S₁ 1`, the three quantities agree: `n` observations are
worth exactly `n` times one, and the bipolar rate is the smallest relative entropy. No
semicontinuity, convexity or compactness of the null is assumed.

For a weakly compact convex null the hypothesis holds [RR26, Proposition 4.5].

## Main statements

* `ProbabilityTheory.mul_maxLogGrowth_one_le`: `n * maxLogGrowth Q₁ S₁ 1 ≤ maxLogGrowth Q₁ S₁ n`.
* `ProbabilityTheory.maxLogGrowth_one_le_bipolarRate`: the growth of one observation is at most
  the bipolar rate.
* `ProbabilityTheory.bipolarRate_eq_iInf_klDiv_of_iInf_klDiv_le_maxLogGrowth_one`: if one
  observation attains the smallest relative entropy, the bipolar rate is the smallest relative
  entropy.
* `ProbabilityTheory.maxLogGrowth_eq_mul_of_iInf_klDiv_le_maxLogGrowth_one`: and then
  `maxLogGrowth Q₁ S₁ n = n * maxLogGrowth Q₁ S₁ 1`.

## References

* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1.
-/

public section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {Q₁ : Measure 𝓧} {S₁ : Set (Measure 𝓧)} {n : ℕ}

/-- The maximal expected logarithm of an `n`-sample e-variable is at least `n` times that of one
observation: superadditivity, iterated. -/
theorem mul_maxLogGrowth_one_le (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsFiniteMeasure P) (n : ℕ) :
    n * maxLogGrowth Q₁ S₁ 1 ≤ maxLogGrowth Q₁ S₁ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_mul]
    exact maxLogGrowth_nonneg Q₁ S₁ 0
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, EReal.right_distrib_of_nonneg (Nat.cast_nonneg' n) zero_le_one,
      one_mul]
    exact (add_le_add_left ih _).trans (maxLogGrowth_add_le Q₁ hS₁ n 1)

/-- The maximal expected logarithm of a one-observation e-variable is at most the bipolar
rate. -/
theorem maxLogGrowth_one_le_bipolarRate (Q₁ : Measure 𝓧) (S₁ : Set (Measure 𝓧)) :
    maxLogGrowth Q₁ S₁ 1 ≤ bipolarRate Q₁ S₁ := by
  simpa using maxLogGrowth_div_le_bipolarRate Q₁ S₁ one_ne_zero

/-- If one observation attains the smallest relative entropy from `Q₁` to the null, the bipolar
rate is the maximal expected logarithm of a one-observation e-variable. -/
theorem bipolarRate_eq_maxLogGrowth_one_of_iInf_klDiv_le (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (h : ((⨅ P ∈ S₁, klDiv Q₁ P : ℝ≥0∞) : EReal) ≤ maxLogGrowth Q₁ S₁ 1) :
    bipolarRate Q₁ S₁ = maxLogGrowth Q₁ S₁ 1 :=
  le_antisymm ((bipolarRate_le_iInf_klDiv Q₁ hS₁).trans h) (maxLogGrowth_one_le_bipolarRate Q₁ S₁)

/-- If one observation attains the smallest relative entropy from `Q₁` to the null, the bipolar
rate is the smallest relative entropy. -/
theorem bipolarRate_eq_iInf_klDiv_of_iInf_klDiv_le_maxLogGrowth_one (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (h : ((⨅ P ∈ S₁, klDiv Q₁ P : ℝ≥0∞) : EReal) ≤ maxLogGrowth Q₁ S₁ 1) :
    bipolarRate Q₁ S₁ = ((⨅ P ∈ S₁, klDiv Q₁ P : ℝ≥0∞) : EReal) :=
  le_antisymm (bipolarRate_le_iInf_klDiv Q₁ hS₁) (h.trans (maxLogGrowth_one_le_bipolarRate Q₁ S₁))

/-- If one observation attains the smallest relative entropy from `Q₁` to the null, then `n`
observations are worth `n` times one: the maximal expected logarithm of an `n`-sample e-variable
is `n` times that of a one-observation e-variable. The common value may be infinite. -/
theorem maxLogGrowth_eq_mul_of_iInf_klDiv_le_maxLogGrowth_one (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (h : ((⨅ P ∈ S₁, klDiv Q₁ P : ℝ≥0∞) : EReal) ≤ maxLogGrowth Q₁ S₁ 1) (hn : n ≠ 0) :
    maxLogGrowth Q₁ S₁ n = n * maxLogGrowth Q₁ S₁ 1 := by
  refine le_antisymm ?_ (mul_maxLogGrowth_one_le Q₁ (fun P hP ↦ ?_) n)
  · rw [← bipolarRate_eq_maxLogGrowth_one_of_iInf_klDiv_le Q₁ hS₁ h]
    exact maxLogGrowth_le_mul_bipolarRate Q₁ S₁ hn
  · have := hS₁ P hP
    infer_instance

end ProbabilityTheory
