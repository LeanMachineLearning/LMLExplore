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
`⨅ P ∈ S₁, klDiv Q₁ P ≤ maxLogGrowth Q₁ S₁ 1`, the three quantities agree: for every `n ≠ 0`,
`n` observations are worth exactly `n` times one, and the bipolar rate is the smallest relative
entropy [EVR26, Note 11, Theorem 9]. No semicontinuity, convexity or compactness of the null is
assumed. Both conclusions already follow from the weaker hypothesis
`bipolarRate Q₁ S₁ ≤ maxLogGrowth Q₁ S₁ 1`, the first for a null of finite measures.

For a weakly compact convex null the hypothesis holds [RR26, Proposition 4.5].

## Main statements

* `ProbabilityTheory.mul_maxLogGrowth_one_le`: `n * maxLogGrowth Q₁ S₁ 1 ≤ maxLogGrowth Q₁ S₁ n`.
* `ProbabilityTheory.maxLogGrowth_one_le_bipolarRate`: the growth of one observation is at most
  the bipolar rate.
* `ProbabilityTheory.bipolarRate_eq_maxLogGrowth_one_of_le`: if the bipolar rate is at most the
  growth of one observation, the two are equal.
* `ProbabilityTheory.maxLogGrowth_eq_mul_of_bipolarRate_le`: if the bipolar rate is at most the
  growth of one observation, then `maxLogGrowth Q₁ S₁ n = n * maxLogGrowth Q₁ S₁ 1` for `n ≠ 0`.
* `ProbabilityTheory.bipolarRate_eq_iInf_klDiv_of_iInf_klDiv_le_maxLogGrowth_one`: if one
  observation attains the smallest relative entropy, the bipolar rate is the smallest relative
  entropy [EVR26, Note 11, Theorem 9].
* `ProbabilityTheory.maxLogGrowth_eq_mul_of_iInf_klDiv_le_maxLogGrowth_one`: and then
  `maxLogGrowth Q₁ S₁ n = n * maxLogGrowth Q₁ S₁ 1` for `n ≠ 0` [EVR26, Note 11, Theorem 9].

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 11, and its
  Lean library `EValuesResearch`, github.com/RemyDegenne/evalues_research, 2026.
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
  cases n with
  | zero => simpa using maxLogGrowth_nonneg Q₁ S₁ 0
  | succ q =>
    simpa [EReal.nsmul_eq_mul] using
      EReal.nsmul_le_of_superadditive (maxLogGrowth_add_le Q₁ hS₁) 1 q

/-- The maximal expected logarithm of a one-observation e-variable is at most the bipolar
rate. -/
theorem maxLogGrowth_one_le_bipolarRate (Q₁ : Measure 𝓧) (S₁ : Set (Measure 𝓧)) :
    maxLogGrowth Q₁ S₁ 1 ≤ bipolarRate Q₁ S₁ := by
  simpa using maxLogGrowth_div_le_bipolarRate Q₁ S₁ one_ne_zero

/-- If the bipolar rate is at most the maximal expected logarithm of a one-observation
e-variable, the two are equal. -/
theorem bipolarRate_eq_maxLogGrowth_one_of_le (h : bipolarRate Q₁ S₁ ≤ maxLogGrowth Q₁ S₁ 1) :
    bipolarRate Q₁ S₁ = maxLogGrowth Q₁ S₁ 1 :=
  le_antisymm h (maxLogGrowth_one_le_bipolarRate Q₁ S₁)

/-- If the bipolar rate is at most the maximal expected logarithm of a one-observation
e-variable, then for `n ≠ 0`, `n` observations are worth `n` times one. -/
theorem maxLogGrowth_eq_mul_of_bipolarRate_le (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsFiniteMeasure P) (h : bipolarRate Q₁ S₁ ≤ maxLogGrowth Q₁ S₁ 1)
    (hn : n ≠ 0) : maxLogGrowth Q₁ S₁ n = n * maxLogGrowth Q₁ S₁ 1 :=
  le_antisymm ((maxLogGrowth_le_mul_bipolarRate Q₁ S₁ hn).trans (by gcongr))
    (mul_maxLogGrowth_one_le Q₁ hS₁ n)

/-- If one observation attains the smallest relative entropy from `Q₁` to the null, the bipolar
rate is the maximal expected logarithm of a one-observation e-variable
[EVR26, Note 11, Theorem 9]. -/
theorem bipolarRate_eq_maxLogGrowth_one_of_iInf_klDiv_le (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (h : ((⨅ P ∈ S₁, klDiv Q₁ P : ℝ≥0∞) : EReal) ≤ maxLogGrowth Q₁ S₁ 1) :
    bipolarRate Q₁ S₁ = maxLogGrowth Q₁ S₁ 1 :=
  bipolarRate_eq_maxLogGrowth_one_of_le ((bipolarRate_le_iInf_klDiv Q₁ hS₁).trans h)

/-- If one observation attains the smallest relative entropy from `Q₁` to the null, the bipolar
rate is the smallest relative entropy [EVR26, Note 11, Theorem 9]. -/
theorem bipolarRate_eq_iInf_klDiv_of_iInf_klDiv_le_maxLogGrowth_one (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (h : ((⨅ P ∈ S₁, klDiv Q₁ P : ℝ≥0∞) : EReal) ≤ maxLogGrowth Q₁ S₁ 1) :
    bipolarRate Q₁ S₁ = ((⨅ P ∈ S₁, klDiv Q₁ P : ℝ≥0∞) : EReal) :=
  le_antisymm (bipolarRate_le_iInf_klDiv Q₁ hS₁) (h.trans (maxLogGrowth_one_le_bipolarRate Q₁ S₁))

/-- If one observation attains the smallest relative entropy from `Q₁` to the null, then for
`n ≠ 0`, `n` observations are worth `n` times one: the maximal expected logarithm of an `n`-sample
e-variable is `n` times that of a one-observation e-variable. The common value may be infinite
[EVR26, Note 11, Theorem 9]. -/
theorem maxLogGrowth_eq_mul_of_iInf_klDiv_le_maxLogGrowth_one (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (h : ((⨅ P ∈ S₁, klDiv Q₁ P : ℝ≥0∞) : EReal) ≤ maxLogGrowth Q₁ S₁ 1) (hn : n ≠ 0) :
    maxLogGrowth Q₁ S₁ n = n * maxLogGrowth Q₁ S₁ 1 :=
  maxLogGrowth_eq_mul_of_bipolarRate_le Q₁ (fun P hP ↦ have := hS₁ P hP; inferInstance)
    ((bipolarRate_le_iInf_klDiv Q₁ hS₁).trans h) hn

end ProbabilityTheory
