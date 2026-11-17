/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.SequentialLearning.Algorithm
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

import LMLExplore.InformationTheory.KullbackLeibler.Pinsker
import LMLExplore.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Pinsker's inequality for the actions of sequential algorithms

For two sequences of rounds `(O, A, Y)` under `P` and `(O', A', Y')` under `P'` (for instance two
runs of an algorithm against two environments), let `KL` be the relative entropy between the laws
of the histories of the first `M` rounds. For a round `t < M` and nonnegative measurable losses
`f` and `g` on the actions with `0 ≤ c ≤ f a + g a` for every action `a`, Pinsker's inequality
`tvDist ≤ √(2 KL)` (`LMLExplore.tvDist_div_two_le_sqrt_toReal_klDiv_div_two`) bounds from below
the expected loss `f` of the action of round `t` under `P` plus the expected loss `g` of the
action of round `t` under `P'`:
`E_P[f (A t)] + E_{P'}[g (A' t)] ≥ c (1 - √(KL / 2))`.

For the losses `f = 1_s` and `g = 1_{sᶜ}` of a measurable set `s` of actions, this is the
counterpart of the Bretagnolle–Huber bound `exp(-KL) / 2` of
`LMLExplore.SequentialLearning.BretagnolleHuber`, sharper when `KL` is small. Losses that are not
indicators, such as squared distances to a target, are what lower bounds whose regret is a
quadratic function of the action need: there the sum `f + g` is bounded below even where neither
loss is.

## Main statements

* `LMLExplore.mul_one_sub_sqrt_klDiv_map_history_le`: the inequality for one round.
* `LMLExplore.mul_one_sub_sqrt_klDiv_map_history_le_sum`: the inequality summed over the rounds
  `t < M`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Section 14.2 and Chapter 15.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset Real Learning
open scoped ENNReal

namespace LMLExplore

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {O' : ℕ → Ω' → 𝓞} {A' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨} {M : ℕ} {f g : 𝓐 → ℝ} {c : ℝ}

/-- **Pinsker's inequality for the action of a round.** If the laws of the histories of the first
`M` rounds of two sequences of rounds are at finite relative entropy `KL`, then for a round
`t < M` and nonnegative measurable losses `f` and `g` on the actions with `0 ≤ c ≤ f a + g a` for
every action `a`, `c (1 - √(KL / 2)) ≤ E_P[f (A t)] + E_{P'}[g (A' t)]`. -/
lemma mul_one_sub_sqrt_klDiv_map_history_le (hH : Measurable (history O A Y M))
    (hH' : Measurable (history O' A' Y' M)) {t : ℕ} (ht : t < M) (hf : Measurable f)
    (hg : Measurable g) (hfi : Integrable (fun ω ↦ f (A t ω)) P)
    (hgi : Integrable (fun ω ↦ g (A' t ω)) P') (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hc0 : 0 ≤ c) (hc : ∀ a, c ≤ f a + g a)
    (h : klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M)) ≠ ∞) :
    c * (1 - √((klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M))).toReal / 2)) ≤
      ∫ ω, f (A t ω) ∂P + ∫ ω, g (A' t ω) ∂P' := by
  set μ := P.map (history O A Y M)
  set ν := P'.map (history O' A' Y' M)
  -- the losses of the action of round `t`, as functions of the history
  have hact : Measurable fun h : Hist 𝓞 𝓐 𝓨 M ↦ (h ⟨t, ht⟩).action :=
    Round.measurable_action.comp (measurable_pi_apply _)
  have hF : ∫ h, f (h ⟨t, ht⟩).action ∂μ = ∫ ω, f (A t ω) ∂P :=
    integral_map hH.aemeasurable (hf.comp hact).aestronglyMeasurable
  have hG : ∫ h, g (h ⟨t, ht⟩).action ∂ν = ∫ ω, g (A' t ω) ∂P' :=
    integral_map hH'.aemeasurable (hg.comp hact).aestronglyMeasurable
  have hFi : Integrable (fun h : Hist 𝓞 𝓐 𝓨 M ↦ f (h ⟨t, ht⟩).action) μ :=
    (integrable_map_measure (hf.comp hact).aestronglyMeasurable hH.aemeasurable).2 hfi
  have hGi : Integrable (fun h : Hist 𝓞 𝓐 𝓨 M ↦ g (h ⟨t, ht⟩).action) ν :=
    (integrable_map_measure (hg.comp hact).aestronglyMeasurable hH'.aemeasurable).2 hgi
  have htv := mul_sub_tvDist_div_two_le_integral_add_integral
    (f := fun h : Hist 𝓞 𝓐 𝓨 M ↦ f (h ⟨t, ht⟩).action)
    (g := fun h : Hist 𝓞 𝓐 𝓨 M ↦ g (h ⟨t, ht⟩).action) (by simp) (hf.comp hact) (hg.comp hact)
    hFi hGi (fun h ↦ hf0 _) (fun h ↦ hg0 _) (c := c) fun h ↦ hc _
  rw [hF, hG, probReal_univ] at htv
  -- Pinsker's inequality `tvDist μ ν ≤ √(2 KL)`
  have hpinsker := tvDist_div_two_le_sqrt_toReal_klDiv_div_two h
  exact htv.trans' (mul_le_mul_of_nonneg_left (by linarith) hc0)

/-- **Pinsker's inequality for the actions**, summed over the rounds: if the laws of the histories
of the first `M` rounds of two sequences of rounds are at finite relative entropy `KL`, then for
nonnegative measurable losses `f` and `g` on the actions with `0 ≤ c ≤ f a + g a` for every action
`a`, `M c (1 - √(KL / 2)) ≤ ∑_{t < M} (E_P[f (A t)] + E_{P'}[g (A' t)])`. -/
lemma mul_one_sub_sqrt_klDiv_map_history_le_sum (hH : Measurable (history O A Y M))
    (hH' : Measurable (history O' A' Y' M)) (hf : Measurable f) (hg : Measurable g)
    (hfi : ∀ t, Integrable (fun ω ↦ f (A t ω)) P) (hgi : ∀ t, Integrable (fun ω ↦ g (A' t ω)) P')
    (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) (hc0 : 0 ≤ c) (hc : ∀ a, c ≤ f a + g a)
    (h : klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M)) ≠ ∞) :
    M * (c * (1 - √((klDiv (P.map (history O A Y M)) (P'.map (history O' A' Y' M))).toReal / 2)))
      ≤ ∑ t ∈ range M, ∫ ω, f (A t ω) ∂P + ∑ t ∈ range M, ∫ ω, g (A' t ω) ∂P' := by
  rw [← sum_add_distrib]
  refine le_of_eq_of_le (by simp) (sum_le_sum fun t ht ↦
    mul_one_sub_sqrt_klDiv_map_history_le hH hH' (mem_range.1 ht) hf hg (hfi t) (hgi t) hf0 hg0
      hc0 hc h)

end LMLExplore
