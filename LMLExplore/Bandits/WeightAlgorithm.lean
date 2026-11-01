/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MeasureTheory.Measure.Weighted
public import LMLExplore.Probability.HasCondDistrib
public import LeanMachineLearning.SequentialLearning.Algorithm

/-!
# Weight-based policies

A weight-based policy on a finite set of arms `α` computes, at every round `n`, a probability
vector `w n (h, o) : α → ℝ` from the history `h` of the first `n` rounds and the current
observation `o`, and draws its action from it: its policy kernel is
`(h, o) ↦ ∑ a, w n (h, o) a • δ_a`. Exponential weights, Exp3, Exp3-IX and Exp4 are weight-based
policies [LS, Algorithms 9, 10 and 11].

## Main definitions

* `LMLExplore.Bandits.weightKernel w hw`: the kernel `x ↦ weightedMeasure (w x)` drawing an arm
  from the weights `w x`.
* `LMLExplore.Bandits.weightAlgorithm w hw hp`: the algorithm whose policy at round `n` is
  `weightKernel (w n)`, for measurable weights in the probability simplex `simplex α`.

## Main statements

In the namespace `LMLExplore.Bandits.WeightAlgorithm`, for a run of `weightAlgorithm w …`:
* `measure_preimage_inter_action_eq`: the run lemma in integral form, for a measurable set `s` of
  pasts and an arm `a`, `P(past ∈ s, A n = a) = ∫_{past ∈ s} w n (past) a dP`;
* `measure_action_eq`: `P(A n = a) = E[w n (past) a]`.

The conditional law of the action of round `n` given the past is
`(weightAlgorithm w …).policy n = weightKernel (w n) _`, by LML's
`IsAlgEnvSeq.hasCondDistrib_action` and `weightAlgorithm_policy`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Learning
open scoped ENNReal

namespace LMLExplore.Bandits

variable {α 𝓞 𝓨 : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSpace 𝓞] [MeasurableSpace 𝓨]

/-- The kernel that draws an arm from the weights `w x`: `x ↦ ∑ a, w x a • δ_a`. -/
noncomputable def weightKernel {X : Type*} [MeasurableSpace X] (w : X → α → ℝ)
    (hw : ∀ a, Measurable fun x ↦ w x a) : Kernel X α where
  toFun x := weightedMeasure (w x)
  measurable' := measurable_weightedMeasure.comp (Measurable.of_eval hw)

@[simp]
lemma weightKernel_apply {X : Type*} [MeasurableSpace X] (w : X → α → ℝ)
    (hw : ∀ a, Measurable fun x ↦ w x a) (x : X) :
    weightKernel w hw x = weightedMeasure (w x) := (rfl)

/-- The kernel of probability vectors `w x ∈ simplex α` is a Markov kernel. -/
lemma isMarkovKernel_weightKernel {X : Type*} [MeasurableSpace X] {w : X → α → ℝ}
    (hw : ∀ a, Measurable fun x ↦ w x a) (hp : ∀ x, w x ∈ simplex α) :
    IsMarkovKernel (weightKernel w hw) :=
  ⟨fun x ↦ isProbabilityMeasure_weightedMeasure (hp x)⟩

/-- The weight-based algorithm: at round `n`, with history `h` and observation `o`, it draws its
action from the probability vector `w n (h, o) ∈ simplex α`. -/
noncomputable def weightAlgorithm (w : (n : ℕ) → Hist 𝓞 α 𝓨 n × 𝓞 → α → ℝ)
    (hw : ∀ n a, Measurable fun x ↦ w n x a) (hp : ∀ n x, w n x ∈ simplex α) :
    Algorithm 𝓞 α 𝓨 where
  policy n := weightKernel (w n) (hw n)
  isMarkovKernel_policy n := isMarkovKernel_weightKernel (hw n) (hp n)

variable {w : (n : ℕ) → Hist 𝓞 α 𝓨 n × 𝓞 → α → ℝ} {hw : ∀ n a, Measurable fun x ↦ w n x a}
  {hp : ∀ n x, w n x ∈ simplex α}

@[simp]
lemma weightAlgorithm_policy (n : ℕ) :
    (weightAlgorithm w hw hp).policy n = weightKernel (w n) (hw n) := (rfl)

namespace WeightAlgorithm

variable [MeasurableSingletonClass α] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsFiniteMeasure P] {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨}
  {env : Environment 𝓞 α 𝓨}

/-- Along a run of a weight-based algorithm, for a measurable set `s` of pasts (history and
observation) of round `n` and an arm `a`, `P(past ∈ s, A n = a) = ∫_{past ∈ s} w n (past) a dP`:
the conditional probability of playing `a` given the past is its weight. -/
lemma measure_preimage_inter_action_eq (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (n : ℕ) {s : Set (Hist 𝓞 α 𝓨 n × 𝓞)} (hs : MeasurableSet s) (a : α) :
    P ((fun ω ↦ (history O A Y n ω, O n ω)) ⁻¹' s ∩ A n ⁻¹' {a}) =
      ∫⁻ ω in (fun ω ↦ (history O A Y n ω, O n ω)) ⁻¹' s,
        ENNReal.ofReal (w n (history O A Y n ω, O n ω) a) ∂P := by
  rw [(h.hasCondDistrib_action n).measure_preimage_inter_eq_setLIntegral hs
    (measurableSet_singleton a)]
  simp

/-- Along a run of a weight-based algorithm, the probability of playing `a` at round `n` is the
expectation of its weight: `P(A n = a) = E[w n (past) a]`. -/
lemma measure_action_eq (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P) (n : ℕ)
    (a : α) :
    P (A n ⁻¹' {a}) = ∫⁻ ω, ENNReal.ofReal (w n (history O A Y n ω, O n ω) a) ∂P := by
  simpa using measure_preimage_inter_action_eq h n MeasurableSet.univ a

end WeightAlgorithm

end LMLExplore.Bandits
