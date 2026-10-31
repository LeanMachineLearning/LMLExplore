/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.DivergenceDecomposition
public import LeanMachineLearning.SequentialLearning.FiniteActions

/-!
# The divergence decomposition, reindexed by the actions

LML's `IsAlgEnvSeq.klDiv_map_history` writes the relative entropy between the laws of the
histories of the first `M` rounds of one algorithm run against two stationary environments with
reward kernels `κ` and `κ'` as a sum over the rounds: `∑ t < M, E[KL(κ (A t) ‖ κ' (A t))]`. For a
finite set of actions, this file regroups the sum by the action played, which gives the
*divergence decomposition* of bandit lower bounds [LS, Lemma 15.1]:
`KL = ∑ a, E[N_a(M)] KL(κ a ‖ κ' a)`, where `N_a(M) = pullCount A a M` is the number of rounds
before `M` at which `a` was played.

## Main statements

* `LMLExplore.sum_lintegral_pullCount_mul`: for a measurable random time `g`,
  `∑ a, E[N_a(g)] f a = E[∑ s < g, f (A s)]`.
* `LMLExplore.lintegral_toENNReal_eq_sum_lintegral_pullCount`: Wald's identity
  `E[τ] = ∑ a, E[N_a(τ)]` for an almost surely finite measurable random time `τ`.
* `Learning.IsAlgEnvSeq.klDiv_map_history_eq_sum_pullCount`: the divergence decomposition.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 15.1.
* The proofs are adapted from the formalization in the LMLPapers project
  (`LMLPapers/LeanMachineLearning/SequentialLearning/DivergenceDecomposition.lean`).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal

namespace LMLExplore

variable {𝓐 Ω : Type*} {m𝓐 : MeasurableSpace 𝓐} {mΩ : MeasurableSpace Ω} [DecidableEq 𝓐]
  [Fintype 𝓐] {P : Measure Ω} {A : ℕ → Ω → 𝓐}

/-- For a finite action set and a measurable random time `g`, the expected number of rounds
before `g` at which each action is played, weighted by `f`, is the expected sum of `f` over the
actions played before `g`: `∑ a, E[N_a(g)] f a = E[∑ s < g, f (A s)]`. -/
lemma sum_lintegral_pullCount_mul [MeasurableSingletonClass 𝓐] (hA : ∀ n, Measurable (A n))
    {g : Ω → ℕ} (hg : Measurable g) (f : 𝓐 → ℝ≥0∞) :
    ∑ a, (∫⁻ ω, (Learning.pullCount A a (g ω) ω : ℝ≥0∞) ∂P) * f a =
      ∫⁻ ω, ∑ s ∈ range (g ω), f (A s ω) ∂P := by
  have hmeas (a : 𝓐) : Measurable fun ω ↦ (Learning.pullCount A a (g ω) ω : ℝ≥0∞) :=
    (measurable_of_countable _).comp
      (Learning.measurable_uncurry_pullCount_comp hA measurable_const hg)
  calc ∑ a, (∫⁻ ω, (Learning.pullCount A a (g ω) ω : ℝ≥0∞) ∂P) * f a
      = ∫⁻ ω, ∑ a, (Learning.pullCount A a (g ω) ω : ℝ≥0∞) * f a ∂P := by
        rw [lintegral_finsetSum _ fun a _ ↦ (hmeas a).mul_const _]
        exact sum_congr rfl fun a _ ↦ (lintegral_mul_const _ (hmeas a)).symm
    _ = ∫⁻ ω, ∑ s ∈ range (g ω), f (A s ω) ∂P :=
        lintegral_congr fun ω ↦ Learning.sum_pullCount_mul ω f (g ω)

/-- **Wald's identity for the number of rounds.** For an almost surely finite measurable random
time `τ` and finitely many actions, `E[τ] = ∑ a, E[N_a(τ)]`, where `N_a(τ)` is the number of
rounds before `τ` at which the action `a` is played. -/
lemma lintegral_toENNReal_eq_sum_lintegral_pullCount [MeasurableSingletonClass 𝓐]
    (hA : ∀ n, Measurable (A n)) {τ : Ω → ℕ∞} (hτ : Measurable τ) (h_fin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂P = ∑ a, ∫⁻ ω, (Learning.pullCount A a (τ ω).toNat ω : ℝ≥0∞) ∂P := by
  have h := sum_lintegral_pullCount_mul (P := P) hA (g := fun ω ↦ (τ ω).toNat)
    (Measurable.of_discrete.comp hτ) fun _ ↦ 1
  simp only [mul_one, sum_const, card_range, nsmul_eq_mul] at h
  rw [h]
  refine lintegral_congr_ae ?_
  filter_upwards [h_fin] with ω hω
  rw [← ENat.toENNReal_coe, ENat.natCast_toNat hω]

end LMLExplore

namespace Learning

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  [Fintype 𝓐] [DecidableEq 𝓐] [MeasurableSingletonClass 𝓐] [MeasurableSpace.CountablyGenerated 𝓨]
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {O' : ℕ → Ω' → Unit} {A' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}
  {alg : Algorithm Unit 𝓐 𝓨} {κ κ' : Kernel 𝓐 𝓨} [IsMarkovKernel κ] [IsMarkovKernel κ']

/-- **Divergence decomposition** [LS, Lemma 15.1]: the relative entropy between the laws of the
histories of the first `M` rounds of an algorithm run against two stationary environments with
reward kernels `κ` and `κ'` is `∑ a, E[N_a(M)] KL(κ a ‖ κ' a)`, where `N_a(M) = pullCount A a M`
is the number of rounds before `M` at which `a` was played. -/
lemma IsAlgEnvSeq.klDiv_map_history_eq_sum_pullCount
    (h : IsAlgEnvSeq O A Y alg (stationaryEnv κ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (stationaryEnv κ') P') (M : ℕ) :
    klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M)) =
      ∑ a, (∫⁻ ω, (pullCount A a M ω : ℝ≥0∞) ∂P) * klDiv (κ a) (κ' a) := by
  have hsum : ∑ t ∈ range M, ∫⁻ ω, klDiv (κ (A t ω)) (κ' (A t ω)) ∂P =
      ∫⁻ ω, ∑ t ∈ range M, klDiv (κ (A t ω)) (κ' (A t ω)) ∂P :=
    (lintegral_finsetSum _ fun t _ ↦
      (measurable_klDiv_kernel κ κ').comp (h.measurable_action t)).symm
  rw [h.klDiv_map_history h' M, hsum]
  exact (LMLExplore.sum_lintegral_pullCount_mul (g := fun _ ↦ M) h.measurable_action
    measurable_const fun a ↦ klDiv (κ a) (κ' a)).symm

end Learning
