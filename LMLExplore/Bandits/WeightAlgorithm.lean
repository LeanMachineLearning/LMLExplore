/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MeasureTheory.Measure.Weighted
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
* `LMLExplore.Bandits.weightAlgorithm w hw hw0 hw1`: the algorithm whose policy at round `n` is
  `weightKernel (w n)`, for measurable, nonnegative weights summing to `1`.

## Main statements

In the namespace `LMLExplore.Bandits.WeightAlgorithm`, for a run of `weightAlgorithm w …`:
* `hasCondDistrib_action`: the run lemma, the conditional law of the action of round `n` given the
  history and the observation is `weightedMeasure (w n (h, o))`;
* `measure_preimage_inter_action_eq`: in integral form, for a measurable set `s` of pasts and an
  arm `a`, `P(past ∈ s, A n = a) = ∫_{past ∈ s} w n (past) a dP`;
* `measure_action_eq`: `P(A n = a) = E[w n (past) a]`.
-/

@[expose] public section

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
    weightKernel w hw x = weightedMeasure (w x) := rfl

/-- The kernel of probability vectors is a Markov kernel. -/
lemma isMarkovKernel_weightKernel {X : Type*} [MeasurableSpace X] {w : X → α → ℝ}
    (hw : ∀ a, Measurable fun x ↦ w x a) (hw0 : ∀ x a, 0 ≤ w x a)
    (hw1 : ∀ x, ∑ a, w x a = 1) :
    IsMarkovKernel (weightKernel w hw) :=
  ⟨fun x ↦ isProbabilityMeasure_weightedMeasure (hw0 x) (hw1 x)⟩

/-- The weight-based algorithm: at round `n`, with history `h` and observation `o`, it draws its
action from the probability vector `w n (h, o)`. -/
noncomputable def weightAlgorithm (w : (n : ℕ) → Hist 𝓞 α 𝓨 n × 𝓞 → α → ℝ)
    (hw : ∀ n a, Measurable fun x ↦ w n x a) (hw0 : ∀ n x a, 0 ≤ w n x a)
    (hw1 : ∀ n x, ∑ a, w n x a = 1) : Algorithm 𝓞 α 𝓨 where
  policy n := weightKernel (w n) (hw n)
  isMarkovKernel_policy n := isMarkovKernel_weightKernel (hw n) (hw0 n) (hw1 n)

variable {w : (n : ℕ) → Hist 𝓞 α 𝓨 n × 𝓞 → α → ℝ} {hw : ∀ n a, Measurable fun x ↦ w n x a}
  {hw0 : ∀ n x a, 0 ≤ w n x a} {hw1 : ∀ n x, ∑ a, w n x a = 1}

@[simp]
lemma weightAlgorithm_policy (n : ℕ) :
    (weightAlgorithm w hw hw0 hw1).policy n = weightKernel (w n) (hw n) := rfl

namespace WeightAlgorithm

variable [MeasurableSingletonClass α] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsFiniteMeasure P] {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨}
  {env : Environment 𝓞 α 𝓨}

omit [MeasurableSingletonClass α] in
/-- The run lemma: along a run of a weight-based algorithm, the conditional law of the action of
round `n` given the history and the observation is the weighted measure of the weights. -/
lemma hasCondDistrib_action (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hw0 hw1) env P)
    (n : ℕ) :
    HasCondDistrib (A n) (fun ω ↦ (history O A Y n ω, O n ω)) (weightKernel (w n) (hw n)) P :=
  h.hasCondDistrib_action n

/-- Along a run of a weight-based algorithm, for a measurable set `s` of pasts (history and
observation) of round `n` and an arm `a`, `P(past ∈ s, A n = a) = ∫_{past ∈ s} w n (past) a dP`:
the conditional probability of playing `a` given the past is its weight. -/
lemma measure_preimage_inter_action_eq (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hw0 hw1) env P)
    (n : ℕ) {s : Set (Hist 𝓞 α 𝓨 n × 𝓞)} (hs : MeasurableSet s) (a : α) :
    P ((fun ω ↦ (history O A Y n ω, O n ω)) ⁻¹' s ∩ A n ⁻¹' {a}) =
      ∫⁻ ω in (fun ω ↦ (history O A Y n ω, O n ω)) ⁻¹' s,
        ENNReal.ofReal (w n (history O A Y n ω, O n ω) a) ∂P := by
  have := isMarkovKernel_weightKernel (hw n) (hw0 n) (hw1 n)
  set X := fun ω ↦ (history O A Y n ω, O n ω) with hX_def
  have hX : Measurable X := (h.measurable_history n).prodMk (h.measurable_obs n)
  have hXA : Measurable fun ω ↦ (X ω, A n ω) := hX.prodMk (h.measurable_action n)
  calc P (X ⁻¹' s ∩ A n ⁻¹' {a})
      = P.map (fun ω ↦ (X ω, A n ω)) (s ×ˢ {a}) := by
        rw [Measure.map_apply hXA (hs.prod (measurableSet_singleton a))]
        rfl
    _ = (P.map X ⊗ₘ weightKernel (w n) (hw n)) (s ×ˢ {a}) := by
        rw [(hasCondDistrib_action h n).map_eq]
    _ = ∫⁻ x in s, weightKernel (w n) (hw n) x {a} ∂(P.map X) :=
        Measure.compProd_apply_prod hs (measurableSet_singleton a)
    _ = ∫⁻ x in s, ENNReal.ofReal (w n x a) ∂(P.map X) := by simp
    _ = ∫⁻ ω in X ⁻¹' s, ENNReal.ofReal (w n (X ω) a) ∂P :=
        setLIntegral_map hs (ENNReal.measurable_ofReal.comp (hw n a)) hX

/-- Along a run of a weight-based algorithm, the probability of playing `a` at round `n` is the
expectation of its weight: `P(A n = a) = E[w n (past) a]`. -/
lemma measure_action_eq (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hw0 hw1) env P) (n : ℕ)
    (a : α) :
    P (A n ⁻¹' {a}) = ∫⁻ ω, ENNReal.ofReal (w n (history O A Y n ω, O n ω) a) ∂P := by
  simpa using measure_preimage_inter_action_eq h n MeasurableSet.univ a

end WeightAlgorithm

end LMLExplore.Bandits
