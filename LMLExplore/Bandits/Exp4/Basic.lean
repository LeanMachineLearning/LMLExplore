/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.Exp4.IX

/-!
# Exp4

In a bandit with expert advice [LS, Chapter 18], each expert `m` of a finite set `β` recommends at
round `t` a distribution `E t m ∈ simplex α` over the arms, and the learner sees this advice before
acting. Exp4 [ACFS02], [LS, Algorithm 11] runs exponential weights over the experts: it keeps
weights `Q t` on the experts, plays an arm drawn from the mixture `P t = ∑ m, Q t m • E t m` of
their advice, estimates the rewards of the arms by the loss-based importance-weighted estimates
`X̂ t` of `P t`, and credits each expert `m` with the estimate `X̂ᴱ t m = E t m ⬝ᵥ X̂ t` of its
expected reward, so that `Q t = softmax (η • ∑ s < t, X̂ᴱ s)`. In matrix form, `P t = Q t E t` and
`X̂ᴱ t = E t X̂ t`. The learning rate `η > 0` is a parameter; this is the algorithm of [LS] with
`γ = 0`.

Exp4 is defined as the instance of Exp4-IX (`LMLExplore.Bandits.exp4IX`) that observes the advice
directly (`adv = id`), with the constant learning rate `η` and no implicit exploration: the
estimated reward `X̂ᴱ s m` of expert `m` is one minus its estimated loss in Exp4-IX, so both
algorithms put the same weights on the experts.

The observation of round `t` is the advice `E t : β → simplex α`. For rewards in `[0, 1]` and a
fixed advice sequence `E`, the regret against the best expert satisfies
`R_n ≤ log M / η + η n k / 2`, with `k` the number of arms and `M` the number of experts, and the
learning rate `η = √(2 log M / (n k))` gives `R_n ≤ √(2 n k log M)` [LS, Theorem 18.1]. These
bounds hold for the expert pseudo-regret against any environment
(`LMLExplore/Bandits/Exp4/PseudoRegret.lean`), which against advice and rewards fixed in advance is
the regret against the best expert (`LMLExplore/Bandits/Exp4/Oblivious.lean`). This file defines
Exp4 and states the pathwise bounds of [LS, Lemma 18.2] in its notation.

## Main definitions

* `LMLExplore.Bandits.exp4 η`: the Exp4 algorithm with learning rate `η`, the instance of Exp4-IX
  with the advice observed directly, the constant learning rate `η` and `γ = 0`.

## Main statements

* `exp4_eq_of_subsingleton`: with a single expert, Exp4 does not depend on its learning rate.
* `Exp4.sum_sub_sum_le`: [LS, Lemma 18.2], the pathwise bound
  `∑ t < n, (X̂ᴱ t m - ⟨Q t, X̂ᴱ t⟩) ≤ log M / η + η / 2 * ∑ t < n, ⟨Q t, (1 - X̂ᴱ t) ^ 2⟩`.
* `Exp4.sum_dotProduct_lossIwEstimator_sub_le`: the resulting pathwise bound on the estimated
  regret against an expert.

## References

* [ACFS02] P. Auer, N. Cesa-Bianchi, Y. Freund and R. E. Schapire, *The nonstochastic multiarmed
  bandit problem*, SIAM J. Comput. 32(1), 2002.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real LMLExplore.OnlineLearning

namespace LMLExplore.Bandits

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]

variable {η : ℝ}

section Algorithm

variable [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty β]

/-- **Exp4** with learning rate `η` [LS, Algorithm 11] (with `γ = 0`): Exp4-IX that observes at
round `n` the advice `e : β → simplex α` of the experts (`adv = id`), with the constant learning
rate `η` and no implicit exploration. It draws its action from the mixture of the advice with the
exponential weights of `η` times the cumulative reward estimates of the experts. -/
noncomputable def exp4 (η : ℝ) : Algorithm (β → simplex α) α ℝ :=
  exp4IX id measurable_id (fun _ ↦ η) 0

lemma exp4_def (η : ℝ) :
    exp4 (α := α) (β := β) η = exp4IX id measurable_id (fun _ ↦ η) 0 := (rfl)

/-- With a single expert, Exp4 does not depend on its learning rate: it follows the advice. -/
lemma exp4_eq_of_subsingleton [Subsingleton β] (η η' : ℝ) :
    exp4 (α := α) (β := β) η = exp4 η' :=
  exp4IX_eq_of_subsingleton _ _ _ _ _

end Algorithm

namespace Exp4

section Pathwise

variable {Ω : Type*} {n : ℕ} [Nonempty β]

/-- **Pathwise regret of the experts' weights in Exp4** [LS, Lemma 18.2]. Along every sequence of
observations `O`, actions `A` and feedbacks `Y ≤ 1` of the rounds `t < n`, with `Q t` the weights
of Exp4 on the experts at round `t` and `X̂ᴱ t m = O t m ⬝ᵥ X̂ t` the estimated reward of expert
`m`, for every expert `m` and `η > 0`,
`∑ t < n, (X̂ᴱ t m - ∑ m', Q t m' * X̂ᴱ t m') ≤
  log M / η + η / 2 * ∑ t < n, ∑ m', Q t m' * (1 - X̂ᴱ t m') ^ 2`,
with `M` the number of experts. This is the local-norm bound of Exp4-IX for the constant learning
rate `η` and `γ = 0`, since the estimated rewards are one minus the estimated losses. -/
theorem sum_sub_sum_le (hη : 0 < η) (O : ℕ → Ω → β → simplex α) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → ℝ) (ω : Ω) (hY : ∀ t < n, Y t ω ≤ 1) (m : β) :
    ∑ t ∈ range n, ((O t ω m : α → ℝ) ⬝ᵥ lossIwEstimator
        (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) -
      ∑ m', exp4IXExpertWeights id (fun _ ↦ η) 0 t (history O A Y t ω) m' *
        (O t ω m' : α → ℝ) ⬝ᵥ lossIwEstimator
          (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω)) ≤
      log (Fintype.card β) / η + η / 2 * ∑ t ∈ range n,
        ∑ m', exp4IXExpertWeights id (fun _ ↦ η) 0 t (history O A Y t ω) m' *
          (1 - (O t ω m' : α → ℝ) ⬝ᵥ lossIwEstimator
            (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω))
              (A t ω) (Y t ω)) ^ 2 := by
  have key := Exp4IX.sum_sum_mul_sub_le (adv := id) (η := fun _ ↦ η) (γ := 0) O A Y ω
    (fun _ ↦ hη) antitone_const (fun _ ↦ le_rfl) hY m
  -- with `γ = 0`, the estimates are the importance-weighted estimates for the weights on the arms
  simp only [Pi.zero_apply, add_zero, id] at key
  -- the estimated rewards are one minus the estimated losses
  have hX : ∀ t m', (O t ω m' : α → ℝ) ⬝ᵥ lossIwEstimator
      (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) =
        1 - (O t ω m' : α → ℝ) ⬝ᵥ iwEstimator
          (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (1 - Y t ω) :=
    fun t m' ↦ by simp only [dotProduct_lossIwEstimator_advice, dotProduct_iwEstimator]
  have h1 : ∀ t (y : β → ℝ), (1 - y m) - ∑ m', exp4IXExpertWeights id (fun _ ↦ η) 0 t
      (history O A Y t ω) m' * (1 - y m') =
        ∑ m', exp4IXExpertWeights id (fun _ ↦ η) 0 t (history O A Y t ω) m' * y m' - y m :=
    fun t y ↦ by
      simp only [mul_sub, mul_one, sum_sub_distrib,
        (mem_simplex_iff.1 (exp4IXExpertWeights_mem_simplex t _)).2]
      ring
  simp only [hX, sub_sub_cancel]
  rw [Finset.mul_sum]
  exact le_of_eq_of_le (Finset.sum_congr rfl fun t _ ↦ h1 t fun m' ↦ (O t ω m' : α → ℝ) ⬝ᵥ
    iwEstimator (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω)
      (1 - Y t ω)) key

/-- **Pathwise bound on the estimated regret of Exp4.** Along every sequence of observations `O`,
actions `A` and feedbacks `Y ≤ 1` of the rounds `t < n` whose actions have positive weight
`P t (A t)`, with `X̂ᴱ t m = O t m ⬝ᵥ X̂ t` the estimated reward of expert `m`, for every expert `m`
and `η > 0`,
`∑ t < n, (X̂ᴱ t m - Y t) ≤ log M / η + η / 2 * ∑ t < n, (1 - Y t) ^ 2 / P t (A t)`. -/
theorem sum_dotProduct_lossIwEstimator_sub_le (hη : 0 < η) (O : ℕ → Ω → β → simplex α)
    (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ) (ω : Ω) (hY : ∀ t < n, Y t ω ≤ 1)
    (hpos : ∀ t < n, exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω) (A t ω) ≠ 0)
    (m : β) :
    ∑ t ∈ range n, ((O t ω m : α → ℝ) ⬝ᵥ
        lossIwEstimator
          (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) - Y t ω) ≤
      log (Fintype.card β) / η + η / 2 * ∑ t ∈ range n,
        (1 - Y t ω) ^ 2 / exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω) (A t ω) := by
  calc ∑ t ∈ range n, ((O t ω m : α → ℝ) ⬝ᵥ
        lossIwEstimator
          (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) - Y t ω)
  _ = ∑ t ∈ range n, ((O t ω m : α → ℝ) ⬝ᵥ
        lossIwEstimator
          (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) -
      ∑ m', exp4IXExpertWeights id (fun _ ↦ η) 0 t (history O A Y t ω) m' * (O t ω m' : α → ℝ) ⬝ᵥ
        lossIwEstimator
          (exp4IXWeights id (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω)) :=
      Finset.sum_congr rfl fun t ht ↦ by
        have key := Exp4IX.sum_exp4IXExpertWeights_mul_dotProduct_lossIwEstimator (adv := id)
          (η := fun _ ↦ η) (γ := 0) t (history O A Y t ω) (O t ω) (Y t ω) (hpos t (mem_range.1 ht))
        simp only [id_eq] at key
        rw [key]
  _ ≤ _ := sum_sub_sum_le hη O A Y ω hY m
  _ ≤ _ := by
      gcongr with t ht
      exact Exp4IX.sum_mul_one_sub_sq_le (adv := id) O A Y ω t

end Pathwise

end Exp4

end LMLExplore.Bandits
