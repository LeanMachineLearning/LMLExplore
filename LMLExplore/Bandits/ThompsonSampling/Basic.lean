/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.SumRewards
public import LMLExplore.Bandits.PerturbedLeader
public import LMLExplore.Probability.Distributions.ExponentialFamily.Posterior
public import LMLExplore.SequentialLearning.FiniteActions

/-!
# Thompson sampling for exponential families

Let every arm `a` have a natural exponential family `ρ a` (a measure on `ℝ` with the statistic
`id`, log-partition function `ψ_a = cgf id (ρ a)` and natural parameters `Θ_a`, the interior of
`integrableExpSet id (ρ a)`) and a prior `π a` on its natural parameter, a measure on `ℝ` that
may be infinite. Thompson sampling [KKM13, Section 2] samples at every round, independently for
every arm `a` pulled `s ≥ 1` times with sum of rewards `S`, a natural parameter `θ_a` from the
posterior `(ρ a).expFamilyPosterior id (π a) s S`, the probability measure proportional to
`exp (θ S - s ψ_a(θ)) π_a(dθ)` on `Θ_a`, and takes its mean `ψ_a'(θ_a)` as the perturbation of
`a`. The perturbation of an arm that has not been pulled, or whose posterior normalizing constant
is `0` or infinite (an improper posterior), is `⊤`. It then plays the arm of largest perturbation.

This is a follow-the-perturbed-leader policy (`perturbedLeaderAlgorithm`) whose perturbation
laws, in `EReal`, depend on the history only through the number of pulls and the sum of rewards
of each arm, so [LS, Theorem 36.2] applies to it in the reward-stack form of
`PerturbedLeader.lintegral_pullCount_le`. With the Jeffreys prior `(ρ a).jeffreysPrior id` it is
the algorithm of [KKM13]; for the Gaussian family of variance `σ² ≠ 0` the Jeffreys prior is a
constant multiple of Lebesgue measure, and Thompson sampling is Gaussian Thompson sampling
`gaussianTS σ2` (`gaussianTS_eq_expFamilyTS`).

## Main definitions

* `LMLExplore.Bandits.expFamilyTSStackLaw ρ π s S`: the law of the perturbation of an arm of
  family `ρ` and prior `π` that has been pulled `s` times with sum of rewards `S`: `δ_⊤` if
  `s = 0` or the posterior is `0`, and otherwise the image of the posterior by the mean map
  `ψ'`.
* `LMLExplore.Bandits.expFamilyTSLaw ρ π n h a`: the law of the perturbation of arm `a` after the
  history `h` of length `n`.
* `LMLExplore.Bandits.expFamilyTS ρ π`: Thompson sampling for the families `ρ` with priors `π`, the
  algorithm `perturbedLeaderAlgorithm` with perturbation laws `expFamilyTSLaw ρ π`.

## Main statements

* `expFamilyTSStackLaw_of_ne_zero`: the law of the perturbation of a pulled arm with a proper
  posterior is the image of the posterior by the mean map.
* `measurable_expFamilyTSStackLaw`, `measurable_expFamilyTSLaw`: measurability of the
  perturbation laws in the sum of rewards and in the history.
* `expFamilyTSLaw_history`: along a sequence of rounds, the perturbation law in terms of LML's
  `pullCount` and `sumRewards`.
* `ExpFamilyTS.lintegral_pullCount_le`: [LS, Theorem 36.2] for Thompson sampling against a
  stochastic bandit, in the reward-stack model.

## References

* [KKM13] N. Korda, E. Kaufmann and R. Munos, *Thompson sampling for 1-dimensional exponential
  family bandits*, NeurIPS 2013.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 36.
-/

public section

open MeasureTheory ProbabilityTheory Learning Bandits

open scoped ENNReal

namespace LMLExplore.Bandits

section Law

variable {α : Type*} [DecidableEq α] {ρ π : Measure ℝ} {s : ℕ} {S : ℝ}

open scoped Classical in
/-- The law of the perturbation of an arm in Thompson sampling for the natural exponential family
of `ρ` with prior `π` on the natural parameter, as a function of the number of pulls `s` of the
arm and of its sum of rewards `S`: the Dirac mass at `⊤` if `s = 0` or if the posterior
`ρ.expFamilyPosterior id π s S` is `0`, and otherwise the image of the posterior by the mean map
`θ ↦ ψ'(θ)`, with `ψ = cgf id ρ`. This is the perturbation law of the reward-stack model, in which
the sum of rewards after `s` pulls is the sum of the first `s` rewards of the stack. -/
noncomputable def expFamilyTSStackLaw (ρ π : Measure ℝ) (s : ℕ) (S : ℝ) : Measure EReal :=
  if s = 0 ∨ ρ.expFamilyPosterior id π s S = 0 then Measure.dirac ⊤
  else (ρ.expFamilyPosterior id π s S).map fun θ ↦ ((deriv (cgf id ρ) θ : ℝ) : EReal)

open scoped Classical in
/-- The defining equation of `expFamilyTSStackLaw`. -/
lemma expFamilyTSStackLaw_def (ρ π : Measure ℝ) (s : ℕ) (S : ℝ) :
    expFamilyTSStackLaw ρ π s S =
      if s = 0 ∨ ρ.expFamilyPosterior id π s S = 0 then Measure.dirac ⊤
      else (ρ.expFamilyPosterior id π s S).map fun θ ↦ ((deriv (cgf id ρ) θ : ℝ) : EReal) :=
  (rfl)

/-- The perturbation of an arm that has not been pulled is `⊤`. -/
@[simp]
lemma expFamilyTSStackLaw_zero (ρ π : Measure ℝ) (S : ℝ) :
    expFamilyTSStackLaw ρ π 0 S = Measure.dirac ⊤ := by
  simp [expFamilyTSStackLaw_def]

/-- The perturbation of an arm whose posterior is `0` (its normalizing constant is `0` or
infinite) is `⊤`. -/
lemma expFamilyTSStackLaw_of_expFamilyPosterior_eq_zero (h : ρ.expFamilyPosterior id π s S = 0) :
    expFamilyTSStackLaw ρ π s S = Measure.dirac ⊤ := by
  simp [expFamilyTSStackLaw_def, h]

/-- The perturbation of an arm that has been pulled `s ≠ 0` times with sum of rewards `S`, and
whose posterior is not `0`, is the mean `ψ'(θ)` of a natural parameter `θ` drawn from the
posterior. -/
lemma expFamilyTSStackLaw_of_ne_zero (hs : s ≠ 0) (h : ρ.expFamilyPosterior id π s S ≠ 0) :
    expFamilyTSStackLaw ρ π s S =
      (ρ.expFamilyPosterior id π s S).map fun θ ↦ ((deriv (cgf id ρ) θ : ℝ) : EReal) := by
  simp [expFamilyTSStackLaw_def, hs, h]

instance : IsProbabilityMeasure (expFamilyTSStackLaw ρ π s S) := by
  by_cases h : s = 0 ∨ ρ.expFamilyPosterior id π s S = 0
  · rcases h with h | h
    · rw [h, expFamilyTSStackLaw_zero]
      infer_instance
    · rw [expFamilyTSStackLaw_of_expFamilyPosterior_eq_zero h]
      infer_instance
  · push Not at h
    have := Measure.isProbabilityMeasure_expFamilyPosterior_of_ne_zero h.2
    rw [expFamilyTSStackLaw_of_ne_zero h.1 h.2]
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

/-- For an s-finite family `ρ` and an s-finite prior `π`, the perturbation law of an arm pulled `s`
times is a measurable function of its sum of rewards. -/
@[fun_prop]
lemma measurable_expFamilyTSStackLaw (ρ π : Measure ℝ) [SFinite ρ] [SFinite π] (s : ℕ) :
    Measurable fun S ↦ expFamilyTSStackLaw ρ π s S := by
  classical
  have hpost := Measure.measurable_expFamilyPosterior (ρ := ρ) aemeasurable_id π s
  have hset : MeasurableSet {S | s = 0 ∨ ρ.expFamilyPosterior id π s S = 0} := by
    simp_rw [← Measure.measure_univ_eq_zero]
    exact (MeasurableSet.const _).union
      ((Measure.measurable_coe MeasurableSet.univ).comp hpost (measurableSet_singleton 0))
  simp_rw [expFamilyTSStackLaw_def]
  exact Measurable.ite hset measurable_const
    ((Measure.measurable_map _ (by fun_prop)).comp hpost)

/-- The law of the perturbation of arm `a` in Thompson sampling for the families `ρ` with priors
`π`, at Lean round `n` for the history `h` of the first `n` rounds: the perturbation law
`expFamilyTSStackLaw (ρ a) (π a)` at the number of pulls and the sum of rewards of `a`. -/
noncomputable def expFamilyTSLaw (ρ π : α → Measure ℝ) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) :
    Measure EReal :=
  expFamilyTSStackLaw (ρ a) (π a) (pullCount' n h a) (sumRewards' n h a)

/-- The defining equation of `expFamilyTSLaw`. -/
lemma expFamilyTSLaw_def (ρ π : α → Measure ℝ) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) :
    expFamilyTSLaw ρ π n h a =
      expFamilyTSStackLaw (ρ a) (π a) (pullCount' n h a) (sumRewards' n h a) :=
  (rfl)

instance {ρ π : α → Measure ℝ} {n : ℕ} {h : Hist Unit α ℝ n} {a : α} :
    IsProbabilityMeasure (expFamilyTSLaw ρ π n h a) := by
  rw [expFamilyTSLaw_def]
  infer_instance

/-- For s-finite families and priors, the perturbation law of an arm at round `n` is a measurable
function of the history: it depends on it through the number of pulls and the sum of rewards of
the arm. -/
@[fun_prop]
lemma measurable_expFamilyTSLaw [MeasurableSpace α] [MeasurableSingletonClass α]
    (ρ π : α → Measure ℝ) [∀ a, SFinite (ρ a)] [∀ a, SFinite (π a)] (n : ℕ) (a : α) :
    Measurable fun h : Hist Unit α ℝ n ↦ expFamilyTSLaw ρ π n h a :=
  (measurable_from_prod_countable_right
    (f := fun q : ℕ × ℝ ↦ expFamilyTSStackLaw (ρ a) (π a) q.1 q.2)
    (measurable_expFamilyTSStackLaw (ρ a) (π a))).comp
    ((measurable_pullCount' n a).prodMk (measurable_sumRewards' n a))

/-- Along a sequence of rounds `(O, A, R)`, the perturbation law of an arm at round `n` is the
perturbation law `expFamilyTSStackLaw` at its number of pulls `pullCount A a n ω` and its sum of
rewards `sumRewards A R a n ω` before round `n`. -/
lemma expFamilyTSLaw_history {Ω : Type*} (O : ℕ → Ω → Unit) (A : ℕ → Ω → α) (R : ℕ → Ω → ℝ)
    (ρ π : α → Measure ℝ) (n : ℕ) (ω : Ω) (a : α) :
    expFamilyTSLaw ρ π n (history O A R n ω) a =
      expFamilyTSStackLaw (ρ a) (π a) (pullCount A a n ω) (sumRewards A R a n ω) := by
  rw [expFamilyTSLaw_def, ← pullCount_eq_pullCount', ← sumRewards_eq_sumRewards']

end Law

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- **Thompson sampling for exponential families** [KKM13, Section 2]: for natural exponential
families `ρ a` and priors `π a` on their natural parameters, the follow-the-perturbed-leader
algorithm whose perturbation of an arm `a` pulled `s ≥ 1` times with sum of rewards `S` is the mean
`ψ_a'(θ_a)` of a natural parameter `θ_a` drawn from the posterior
`(ρ a).expFamilyPosterior id (π a) s S`, and `⊤` for unpulled arms and improper posteriors. -/
noncomputable def expFamilyTS (ρ π : α → Measure ℝ) [∀ a, SFinite (ρ a)] [∀ a, SFinite (π a)] :
    Algorithm Unit α ℝ :=
  perturbedLeaderAlgorithm (fun n x a ↦ expFamilyTSLaw ρ π n x.1 a)
    (fun n a ↦ (measurable_expFamilyTSLaw ρ π n a).comp measurable_fst) fun _ _ _ ↦ inferInstance

/-- Thompson sampling for exponential families is the follow-the-perturbed-leader algorithm with
perturbation laws `expFamilyTSLaw ρ π`. -/
lemma expFamilyTS_def (ρ π : α → Measure ℝ) [∀ a, SFinite (ρ a)] [∀ a, SFinite (π a)] :
    expFamilyTS ρ π =
      perturbedLeaderAlgorithm (fun n x a ↦ expFamilyTSLaw ρ π n x.1 a)
        (fun n a ↦ (measurable_expFamilyTSLaw ρ π n a).comp measurable_fst)
        fun _ _ _ ↦ inferInstance :=
  (rfl)

namespace ExpFamilyTS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {O : ℕ → Ω → Unit}
  {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {ρ π : α → Measure ℝ} [∀ a, SFinite (ρ a)]
  [∀ a, SFinite (π a)]

/-- **[LS, Theorem 36.2] for Thompson sampling for exponential families.** In a run of Thompson
sampling against the stochastic bandit `Environment.bandit ν`, for arms `i ≠ j`, a level `c` and
every horizon `n`,
`E[T_i(n)] ≤ 1 + E[∑_{s < n} (G_{j s}⁻¹ - 1)] + ∑_{s < n} P(G_{i s} > 1 / n)`, where `G_{a s}` is
the probability that the perturbation of arm `a` after its first `s` rewards in the reward-stack
model `streamMeasure ν` exceeds `c`. -/
theorem lintegral_pullCount_le [IsProbabilityMeasure P] {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (h : IsAlgEnvSeq O A R (expFamilyTS ρ π) (Environment.bandit ν) P) {i j : α} (hij : i ≠ j)
    (c : EReal) (n : ℕ) :
    ∫⁻ ω, (pullCount A i n ω : ℝ≥0∞) ∂P ≤
      1 + ∑ s ∈ Finset.range n, ∫⁻ x,
          (expFamilyTSStackLaw (ρ j) (π j) s (∑ k ∈ Finset.range s, x k j) (Set.Ioi c))⁻¹ - 1
            ∂(streamMeasure ν) +
        ∑ s ∈ Finset.range n, streamMeasure ν {x | (n : ℝ≥0∞)⁻¹ <
          expFamilyTSStackLaw (ρ i) (π i) s (∑ k ∈ Finset.range s, x k i) (Set.Ioi c)} :=
  -- the perturbation law of an arm is a function of its number of pulls and its sum of rewards
  PerturbedLeader.lintegral_pullCount_le h (fun a ↦ expFamilyTSStackLaw (ρ a) (π a))
    (fun a ↦ measurable_expFamilyTSStackLaw (ρ a) (π a))
    (fun t x a ↦ expFamilyTSLaw_def ρ π t x.1 a) hij c n

end ExpFamilyTS

end LMLExplore.Bandits
