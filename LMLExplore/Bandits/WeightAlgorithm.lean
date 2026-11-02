/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MeasureTheory.Measure.Weighted
public import LMLExplore.SequentialLearning.Algorithm

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
* `measure_action_eq`: `P(A n = a) = E[w n (past) a]`;
* `integrable_comp_action_iff`: a function `f (past, A n)` of the past and the action is integrable
  iff the weighted sum `∑ a, w n (past) a * ‖f (past, a)‖` is;
* `condExp_comp_action`: the conditional expectation of `f (past, A n)` given the past is the
  weighted sum `∑ a, w n (past) a • f (past, a)`.

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

variable {E : Type*} [NormedAddCommGroup E]

/-- Along a run of a weight-based algorithm, a function `f (past, A n)` of the past (history and
observation) of round `n` and of the action of round `n` is integrable iff the weighted sum
`∑ a, w n (past) a * ‖f (past, a)‖` is integrable. -/
lemma integrable_comp_action_iff (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (n : ℕ) {f : (Hist 𝓞 α 𝓨 n × 𝓞) × α → E} (hf : StronglyMeasurable f) :
    Integrable (fun ω ↦ f ((history O A Y n ω, O n ω), A n ω)) P ↔
      Integrable (fun ω ↦ ∑ a, w n (history O A Y n ω, O n ω) a *
        ‖f ((history O A Y n ω, O n ω), a)‖) P := by
  have hX : Measurable fun ω ↦ (history O A Y n ω, O n ω) :=
    (h.measurable_history n).prodMk (h.measurable_obs n)
  have hg : Measurable fun x ↦ ∑ a, w n x a * ‖f (x, a)‖ :=
    Finset.measurable_sum _ fun a _ ↦ (hw n a).mul
      (hf.norm.measurable.comp (measurable_id.prodMk measurable_const))
  refine (integrable_map_measure hf.aestronglyMeasurable
    (hX.prodMk (h.measurable_action n)).aemeasurable).symm.trans ?_
  rw [(h.hasCondDistrib_action n).map_eq, Measure.integrable_compProd_iff hf.aestronglyMeasurable]
  simp only [weightAlgorithm_policy, weightKernel_apply, Integrable.of_finite,
    Filter.eventually_true, true_and]
  refine Iff.trans ?_ (integrable_map_measure (f := fun ω ↦ (history O A Y n ω, O n ω))
    (g := fun x ↦ ∑ a, w n x a * ‖f (x, a)‖) hg.aestronglyMeasurable hX.aemeasurable)
  refine integrable_congr (ae_of_all _ fun x ↦ ?_)
  simp [integral_weightedMeasure_eq_sum (mem_simplex_iff.1 (hp n x)).1]

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- Along a run of a weight-based algorithm, the conditional expectation of an integrable function
`f (past, A n)` of the past and of the action of round `n` given the past is the weighted sum
`∑ a, w n (past) a • f (past, a)`. -/
lemma condExp_comp_action [Nonempty α] (h : IsAlgEnvSeq O A Y (weightAlgorithm w hw hp) env P)
    (n : ℕ) {f : (Hist 𝓞 α 𝓨 n × 𝓞) × α → E} (hf : StronglyMeasurable f)
    (hint : Integrable (fun ω ↦ f ((history O A Y n ω, O n ω), A n ω)) P) :
    P[fun ω ↦ f ((history O A Y n ω, O n ω), A n ω) | h.filtrationObs n] =ᵐ[P]
      fun ω ↦ ∑ a, w n (history O A Y n ω, O n ω) a • f ((history O A Y n ω, O n ω), a) := by
  filter_upwards [h.condExp_comp_action n hf hint] with ω hω
  rw [hω, weightAlgorithm_policy, weightKernel_apply,
    integral_weightedMeasure_eq_sum (mem_simplex_iff.1 (hp n _)).1]

end WeightAlgorithm

end LMLExplore.Bandits
