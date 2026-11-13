/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.SumRewards
public import TauCeti.Probability.Process.EmpiricalMeasure

import LMLExplore.Probability.Kernel.Basic

/-!
# Empirical laws of the outcomes observed at the visits of a key

A learner that visits keys `x i` (arms, state-action pairs, …) at the indices `i` of a finite set
`u` and observes an outcome `y i` at each visit estimates the law of the outcome of a key `a` by
the empirical law of the outcomes observed at the visits of `a`:
`empiricalLaw u x y a = N⁻¹ ∑_{i ∈ u, x i = a} δ_{y i}`, with `N = #{i ∈ u | x i = a}` the number
of visits of `a`. It is Tau Ceti's empirical measure of the family of these outcomes, a
probability measure for every outcome type (`isProbabilityMeasure_empiricalLaw_of_card_ne_zero`).
When `a` is not visited, it is the uniform law `uniformOn Set.univ`, so that for a finite nonempty
outcome type it is a probability measure at every key (`isProbabilityMeasure_empiricalLaw`), and
the kernel `empiricalLawKernel u x y` of the empirical laws of all keys is a Markov kernel.

For a sequential process, the visits before time `t` are the indices `u = range t`, and the number
of visits of `a` is LML's `pullCount`. The empirical mean of the rewards of an arm, LML's `empMean`,
is the mean of the empirical law of its rewards (`empMean_eq_integral_empiricalLaw`). The
empirical law depends measurably on the keys and outcomes of the indices of `u`
(`measurable_empiricalLaw`), so that the empirical laws of an adapted process before time `t + 1`
form an adapted process (`adapted_empiricalLaw`).

The empirical transition kernels of Markov decision processes are the case of the state-action
pairs as keys and of the next states as outcomes
(`LMLExplore/ReinforcementLearning/EmpiricalTransitions.lean`).

The empirical laws and the pooled counts follow the empirical models of the formalization of
[EV26] in Essakine2026Tight (`github.com/RemyDegenne/Essakine2026Tight`, files
`Essakine2026Tight/ForLMLExplore/ReinforcementLearning/Episodic/Empirical.lean` and
`Essakine2026Tight/ForLMLExplore/ReinforcementLearning/Episodic/EmpiricalCounts.lean`, by Rémy
Degenne, Apache 2.0), restated through LML's `pullCount`, with the uniform law at unvisited keys.

## Main definitions

* `LMLExplore.empiricalLaw u x y a`: the empirical law of the outcomes at the visits of `a`.
* `LMLExplore.empiricalLawKernel u x y`: the kernel of the empirical laws, for a countable key
  type.

## Main statements

* `LMLExplore.empiricalLaw_apply`, `LMLExplore.measureReal_empiricalLaw_singleton`: a visited
  key gives an outcome set the proportion of its visits with an outcome in the set.
* `LMLExplore.integral_empiricalLaw`, `LMLExplore.lintegral_empiricalLaw`: integrating against
  the empirical law of a visited key averages over its visits.
* `LMLExplore.measurable_empiricalLaw`, `LMLExplore.adapted_empiricalLaw`: measurability in the
  observations.

## References

* [EV26] A. Essakine and C. Vernade, *Tight sample complexity bounds for entropic best policy
  identification*, COLT 2026, arXiv:2605.13717.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning
open scoped ENNReal

namespace LMLExplore

variable {ι α β : Type*} [MeasurableSpace β] [DecidableEq α]
  {u : Finset ι} {x : ι → α} {y : ι → β} {a : α}

/-- The empirical law of the outcomes `y i` observed at the indices `i ∈ u` of key `x i = a`:
Tau Ceti's empirical measure `N⁻¹ ∑_{i ∈ u, x i = a} δ_{y i}` of the family of these outcomes,
with `N = #{i ∈ u | x i = a}`, and the uniform law `uniformOn Set.univ` if no index of `u` has
key `a`. -/
noncomputable def empiricalLaw (u : Finset ι) (x : ι → α) (y : ι → β) (a : α) : Measure β :=
  if #{i ∈ u | x i = a} = 0 then uniformOn Set.univ
  else (TauCeti.Probability.empiricalFiniteMeasure fun i : u.filter (x · = a) ↦ y i : Measure β)

/-- The empirical law of an unvisited key is the uniform law. -/
lemma empiricalLaw_of_card_eq_zero (h : #{i ∈ u | x i = a} = 0) :
    empiricalLaw u x y a = uniformOn Set.univ :=
  ite_eq_left h

/-- The empirical law of a visited key is Tau Ceti's empirical measure of the outcomes at its
visits. -/
lemma empiricalLaw_of_card_ne_zero (h : #{i ∈ u | x i = a} ≠ 0) :
    empiricalLaw u x y a =
      (TauCeti.Probability.empiricalFiniteMeasure fun i : u.filter (x · = a) ↦ y i :
        Measure β) :=
  ite_eq_right h

/-- The empirical law of a visited key is the normalized sum `N⁻¹ ∑_{i ∈ u, x i = a} δ_{y i}` of
the Dirac masses at the outcomes of its `N` visits. -/
lemma empiricalLaw_eq_smul_sum (h : #{i ∈ u | x i = a} ≠ 0) :
    empiricalLaw u x y a =
      (#{i ∈ u | x i = a} : ℝ≥0∞)⁻¹ • ∑ i ∈ u with x i = a, Measure.dirac (y i) := by
  rw [empiricalLaw_of_card_ne_zero h, TauCeti.Probability.empiricalFiniteMeasure_toMeasure,
    ← smul_sum, Fintype.card_coe]
  exact congrArg _ (sum_coe_sort _ fun i ↦ Measure.dirac (y i))

/-- The empirical law of a key only depends on the keys and outcomes of the indices of `u`. -/
lemma empiricalLaw_congr {x' : ι → α} {y' : ι → β} (hx : ∀ i ∈ u, x i = x' i)
    (hy : ∀ i ∈ u, y i = y' i) (a : α) :
    empiricalLaw u x y a = empiricalLaw u x' y' a := by
  have hfilter : ({i ∈ u | x i = a} : Finset ι) = {i ∈ u | x' i = a} :=
    filter_congr fun i hi ↦ by rw [hx i hi]
  by_cases h : #{i ∈ u | x i = a} = 0
  · rw [empiricalLaw_of_card_eq_zero h, empiricalLaw_of_card_eq_zero (hfilter ▸ h)]
  · rw [empiricalLaw_eq_smul_sum h, empiricalLaw_eq_smul_sum (hfilter ▸ h), hfilter]
    refine congrArg _ (sum_congr rfl fun i hi ↦ ?_)
    rw [hy i (mem_filter.1 hi).1]

/-- The empirical law of a visited key is a probability measure. -/
lemma isProbabilityMeasure_empiricalLaw_of_card_ne_zero (h : #{i ∈ u | x i = a} ≠ 0) :
    IsProbabilityMeasure (empiricalLaw u x y a) := by
  rw [empiricalLaw_of_card_ne_zero h]
  have : Nonempty (u.filter (x · = a)) := (card_pos.1 (Nat.pos_of_ne_zero h)).to_subtype
  infer_instance

/-- For a finite nonempty outcome type, the empirical law of every key is a probability
measure. -/
instance isProbabilityMeasure_empiricalLaw [Finite β] [Nonempty β] :
    IsProbabilityMeasure (empiricalLaw u x y a) := by
  by_cases h : #{i ∈ u | x i = a} = 0
  · rw [empiricalLaw_of_card_eq_zero h]
    infer_instance
  · exact isProbabilityMeasure_empiricalLaw_of_card_ne_zero h

open Classical in
/-- A visited key gives a measurable set `s` the proportion `#{i ∈ u | x i = a ∧ y i ∈ s} / N` of
its `N` visits with an outcome in `s`. -/
lemma empiricalLaw_apply (h : #{i ∈ u | x i = a} ≠ 0) {s : Set β} (hs : MeasurableSet s) :
    empiricalLaw u x y a s = #{i ∈ u | x i = a ∧ y i ∈ s} / #{i ∈ u | x i = a} := by
  rw [empiricalLaw_eq_smul_sum h, ENNReal.div_eq_inv_mul, ← filter_filter]
  simp [Measure.dirac_apply' _ hs, Set.indicator_apply, sum_boole]

/-- A visited key gives an outcome `b` the proportion `#{i ∈ u | x i = a ∧ y i = b} / N` of its
`N` visits with outcome `b`. -/
lemma measureReal_empiricalLaw_singleton [MeasurableSingletonClass β] [DecidableEq β]
    (h : #{i ∈ u | x i = a} ≠ 0) (b : β) :
    (empiricalLaw u x y a).real {b} = (#{i ∈ u | x i = a ∧ y i = b} : ℝ) / #{i ∈ u | x i = a} := by
  rw [measureReal_def, empiricalLaw_apply h (measurableSet_singleton b), ENNReal.toReal_div]
  simp

/-- Integrating a strongly measurable function against the empirical law of a visited key
averages it over the outcomes of the visits. -/
lemma integral_empiricalLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (h : #{i ∈ u | x i = a} ≠ 0) {f : β → E} (hf : StronglyMeasurable f) :
    ∫ z, f z ∂(empiricalLaw u x y a) =
      (#{i ∈ u | x i = a} : ℝ)⁻¹ • ∑ i ∈ u with x i = a, f (y i) := by
  rw [empiricalLaw_of_card_ne_zero h, TauCeti.Probability.integral_empiricalFiniteMeasure hf,
    Fintype.card_coe]
  exact congrArg _ (sum_coe_sort _ fun i ↦ f (y i))

/-- The Lebesgue integral of a measurable function against the empirical law of a visited key is
its average over the outcomes of the visits. -/
lemma lintegral_empiricalLaw (h : #{i ∈ u | x i = a} ≠ 0) {f : β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(empiricalLaw u x y a) =
      (#{i ∈ u | x i = a} : ℝ≥0∞)⁻¹ * ∑ i ∈ u with x i = a, f (y i) := by
  rw [empiricalLaw_of_card_ne_zero h, TauCeti.Probability.lintegral_empiricalFiniteMeasure hf,
    Fintype.card_coe]
  exact congrArg _ (sum_coe_sort _ fun i ↦ f (y i))

section Measurability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The empirical law of a key is a measurable function of the observations, provided that the
keys and outcomes of the indices of `u` are measurable. -/
lemma measurable_empiricalLaw {X : ι → Ω → α} {Y : ι → Ω → β} (hX : ∀ i ∈ u, Measurable (X i))
    (hY : ∀ i ∈ u, Measurable (Y i)) (a : α) :
    Measurable fun ω ↦ empiricalLaw u (X · ω) (Y · ω) a := by
  have hset (i : ι) (hi : i ∈ u) : MeasurableSet {ω | X i ω = a} :=
    (hX i hi) (measurableSet_singleton a)
  -- the number of visits of `a` is a measurable function of the observations
  have hN : Measurable fun ω ↦ #{i ∈ u | X i ω = a} := by
    simp_rw [card_filter]
    exact Finset.measurable_sum _ fun i hi ↦
      Measurable.ite (hset i hi) measurable_const measurable_const
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  have heq : (fun ω ↦ empiricalLaw u (X · ω) (Y · ω) a s) = fun ω ↦
      if #{i ∈ u | X i ω = a} = 0 then uniformOn Set.univ s
      else (#{i ∈ u | X i ω = a} : ℝ≥0∞)⁻¹ *
        ∑ i ∈ u, if X i ω = a then s.indicator 1 (Y i ω) else 0 := by
    ext ω
    split_ifs with h
    · rw [empiricalLaw_of_card_eq_zero h]
    · rw [empiricalLaw_eq_smul_sum h, ← sum_filter]
      simp [Measure.dirac_apply' _ hs]
  rw [heq]
  refine Measurable.ite ((measurableSet_singleton 0).preimage hN) measurable_const ?_
  refine ((measurable_from_nat (f := fun n : ℕ ↦ (n : ℝ≥0∞)⁻¹)).comp hN).mul ?_
  exact Finset.measurable_sum _ fun i hi ↦ Measurable.ite (hset i hi)
    ((measurable_one.indicator hs).comp (hY i hi)) measurable_const

/-- If the keys `A` and the outcomes `Y` of a process are adapted to a filtration, then so are the
empirical laws of the outcomes at the visits of `a` before time `t + 1`. -/
lemma adapted_empiricalLaw {𝓕 : Filtration ℕ mΩ} {A : ℕ → Ω → α} {Y : ℕ → Ω → β}
    (hA : Adapted 𝓕 A) (hY : Adapted 𝓕 Y) (a : α) :
    Adapted 𝓕 fun t ω ↦ empiricalLaw (range (t + 1)) (A · ω) (Y · ω) a := fun _ ↦
  measurable_empiricalLaw (fun _ hi ↦ hA.measurable_le (Nat.lt_succ_iff.1 (mem_range.1 hi)))
    (fun _ hi ↦ hY.measurable_le (Nat.lt_succ_iff.1 (mem_range.1 hi))) a

end Measurability

/-- The empirical mean of the rewards of a pulled arm, LML's `empMean`, is the mean of the
empirical law of its rewards. -/
lemma empMean_eq_integral_empiricalLaw {Ω : Type*} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {t : ℕ}
    {ω : Ω} (h : pullCount A a t ω ≠ 0) :
    empMean A R a t ω = ∫ z, z ∂(empiricalLaw (range t) (A · ω) (R · ω) a) := by
  rw [integral_empiricalLaw (f := fun z : ℝ ↦ z) h stronglyMeasurable_id, empMean, sumRewards,
    ← sum_filter, smul_eq_mul, div_eq_inv_mul, pullCount]

/-- The visits of a key `a` before time `k` by a finite family `j ↦ x · · j` of processes, with one
visit per process at every time, are the sum over the family of the visits of `a` by each
process. -/
lemma card_filter_range_product_eq_sum_pullCount {Ω κ : Type*} [Fintype κ]
    (x : ℕ → Ω → κ → α) (a : α) (k : ℕ) (ω : Ω) :
    #{q ∈ range k ×ˢ univ | x q.1 ω q.2 = a} = ∑ j, pullCount (fun i ω ↦ x i ω j) a k ω := by
  rw [card_filter, sum_product_right]
  simp_rw [pullCount_eq_sum]

section Kernel

variable [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- The kernel mapping each key `a` to the empirical law `empiricalLaw u x y a` of the outcomes
observed at its visits. It is a Markov kernel when the outcome type is finite and nonempty. -/
noncomputable def empiricalLawKernel (u : Finset ι) (x : ι → α) (y : ι → β) : Kernel α β :=
  Kernel.ofFunOfCountable (empiricalLaw u x y)

@[simp]
lemma empiricalLawKernel_apply (u : Finset ι) (x : ι → α) (y : ι → β) (a : α) :
    empiricalLawKernel u x y a = empiricalLaw u x y a :=
  Kernel.ofFunOfCountable_apply _ _

instance isMarkovKernel_empiricalLawKernel [Finite β] [Nonempty β] :
    IsMarkovKernel (empiricalLawKernel u x y) :=
  Kernel.isMarkovKernel_ofFunOfCountable _

end Kernel

end LMLExplore
