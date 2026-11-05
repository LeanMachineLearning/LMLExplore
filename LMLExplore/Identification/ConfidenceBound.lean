/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.SumRewards

/-!
# Confidence bounds from an exploration rate

Many fixed-confidence identification algorithms, such as LUCB [KTAS12] and successive elimination
[EMM02], compare confidence bounds of the form `μ̂_a ∓ β(N_a, n)` after `n` rounds, where `N_a`
and `μ̂_a` are the number of pulls and the empirical mean of the arm `a`, and `β` is an
exploration rate.

## Main definitions

In the namespace `LMLExplore.Identification`:

* `lowerBound β`, `upperBound β`: the confidence bounds `μ̂_a ∓ β(N_a, n)` with exploration
  rate `β`, as functions of the history.

## Main statements

* `measurable_lowerBound`, `measurable_upperBound`: the confidence bounds are measurable functions
  of the history.

## References

* [EMM02] E. Even-Dar, S. Mannor and Y. Mansour, *PAC bounds for multi-armed bandit and Markov
  decision processes*, COLT 2002, Section 3.
* [KTAS12] S. Kalyanakrishnan, A. Tewari, P. Auer and P. Stone, *PAC subset selection in
  stochastic multi-armed bandits*, ICML 2012, Section 3.1.
-/

public section

open MeasureTheory Learning

namespace LMLExplore.Identification

variable {α : Type*} [DecidableEq α]

/-- The lower confidence bound `μ̂_a - β(N_a, n)` with exploration rate `β`, after `n` rounds with
history `h`, where `N_a` and `μ̂_a` are the number of pulls and the empirical mean of the
arm `a`. -/
noncomputable def lowerBound (β : ℕ → ℕ → ℝ) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) : ℝ :=
  empMean' n h a - β (pullCount' n h a) n

lemma lowerBound_def (β : ℕ → ℕ → ℝ) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) :
    lowerBound β n h a = empMean' n h a - β (pullCount' n h a) n := (rfl)

/-- The upper confidence bound `μ̂_a + β(N_a, n)` with exploration rate `β`, after `n` rounds with
history `h`, where `N_a` and `μ̂_a` are the number of pulls and the empirical mean of the
arm `a`. -/
noncomputable def upperBound (β : ℕ → ℕ → ℝ) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) : ℝ :=
  empMean' n h a + β (pullCount' n h a) n

lemma upperBound_def (β : ℕ → ℕ → ℝ) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) :
    upperBound β n h a = empMean' n h a + β (pullCount' n h a) n := (rfl)

variable [MeasurableSpace α] [MeasurableSingletonClass α]

lemma measurable_lowerBound (β : ℕ → ℕ → ℝ) (n : ℕ) (a : α) :
    Measurable fun h : Hist Unit α ℝ n ↦ lowerBound β n h a :=
  (measurable_empMean' n a).sub
    ((measurable_of_countable fun u ↦ β u n).comp (measurable_pullCount' n a))

lemma measurable_upperBound (β : ℕ → ℕ → ℝ) (n : ℕ) (a : α) :
    Measurable fun h : Hist Unit α ℝ n ↦ upperBound β n h a :=
  (measurable_empMean' n a).add
    ((measurable_of_countable fun u ↦ β u n).comp (measurable_pullCount' n a))

end LMLExplore.Identification
