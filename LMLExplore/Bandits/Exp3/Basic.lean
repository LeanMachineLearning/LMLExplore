/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.Exp4.IX

/-!
# Exp3

Exp3 [ACFS02], [LS, Algorithm 9] is the weight-based algorithm for adversarial bandits with
finitely many arms `α` that plays at round `t` the exponential weights `P t = softmax (-(η • L̂ t))`
of its cumulative loss estimates `L̂ t = ∑ s < t, Ŷ s`, where `Ŷ s` is the importance-weighted
estimate of the losses `1 - X s` of round `s`, computed from the arm `A s` drawn from `P s` and its
observed reward `X s`: `Ŷ s a = 𝟙{A s = a} (1 - X s) / P s a`. The learning rate `η > 0` is a
parameter. Exp3 ignores the observations of the environment. It is defined as the instance of
Exp4-IX (`LMLExplore.Bandits.exp4IX`) with the experts `α`, expert `b` advising the Dirac mass at
`b` at every observation (`singleAdvice`), the constant learning rate `η` and no implicit
exploration: its weights on the arms are its weights on the experts, and the estimated loss of
expert `b` is `Ŷ s b`.
[LS, Algorithm 9] writes the weights as `softmax (η • Ŝ t)` with the loss-based reward estimates
`Ŝ t = ∑ s < t, (1 - Ŷ s)`, which differ from `-L̂ t` by the constant `t`.

For rewards in `[0, 1]`, its adversarial regret against the reward table `x` satisfies
`R_n(x) ≤ log k / η + η n k / 2`, with `k` the number of arms, and the learning rate
`η = √(2 log k / (n k))` gives `R_n(x) ≤ √(2 n k log k)` [LS, Theorem 11.2]. These bounds hold
for the pseudo-regret against any environment (`LMLExplore/Bandits/Exp4/PseudoRegret.lean`), which
against a reward table fixed in advance is the adversarial regret
(`LMLExplore/Bandits/Exp4/Oblivious.lean`). This file defines Exp3 and states its pathwise bound on
the estimated regret, the local-norm bound of Exp4-IX for a constant learning rate applied to the
nonnegative losses `Ŷ s`.

## Main definitions

* `LMLExplore.Bandits.exp3 η`: the Exp3 algorithm with learning rate `η`, the instance of Exp4-IX
  with one expert per arm, the constant learning rate `η` and `γ = 0`.

## Main statements

* `exp4IXWeights_single`: with the experts that each recommend one arm, the weights of Exp4-IX on
  the arms are its weights on the experts.
* `exp4IXSum_single_history`: with the experts that each recommend one arm, the cumulative
  estimated loss of expert `b` is the sum of the implicit-exploration estimates of the losses of
  arm `b`.
* `Exp3.sum_lossIwEstimator_sub_le`: the pathwise bound on the estimated regret of Exp3.

## References

* [ACFS02] P. Auer, N. Cesa-Bianchi, Y. Freund and R. E. Schapire, *The nonstochastic multiarmed
  bandit problem*, SIAM J. Comput. 32(1), 2002.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real LMLExplore.OnlineLearning

namespace LMLExplore.Bandits

variable {α 𝓞 : Type*} [Fintype α] [DecidableEq α]

section Single

variable {η γ : ℕ → ℝ}

/-- With the experts `α` that each recommend one arm (expert `b` advises the Dirac mass at `b`),
the weights of Exp4-IX on the arms are its weights on the experts, at every observation. -/
@[simp]
lemma exp4IXWeights_single (n : ℕ) (h : Hist 𝓞 α ℝ n) (o : 𝓞) :
    exp4IXWeights singleAdvice η γ n h o = exp4IXExpertWeights singleAdvice η γ n h := by
  simp only [exp4IXWeights_def, coe_singleAdvice]
  exact (pi_eq_sum_univ' _).symm

/-- With the experts `α` that each recommend one arm, every arm has positive weight in Exp4-IX. -/
lemma exp4IXWeights_single_pos [Nonempty α] (n : ℕ) (h : Hist 𝓞 α ℝ n) (o : 𝓞) (a : α) :
    0 < exp4IXWeights singleAdvice η γ n h o a := by
  rw [exp4IXWeights_single]
  exact exp4IXExpertWeights_pos n h a

/-- With the experts `α` that each recommend one arm, along a sequence of observations `O`, actions
`A` and feedbacks `Y`, the cumulative estimated loss of expert `b` in Exp4-IX after `n` rounds is
the sum over the rounds `t < n` of the implicit-exploration estimates `Ŷ t b` of the losses
`1 - Y t` at the arm `b`. -/
lemma exp4IXSum_single_history {Ω : Type*} (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (b : α) :
    exp4IXSum singleAdvice η γ n (history O A Y n ω) b =
      ∑ t ∈ range n, iwEstimator (fun a ↦
        exp4IXWeights singleAdvice η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω) (1 - Y t ω)
          b := by
  simp [exp4IXSum_history, Finset.sum_apply, single_dotProduct]

end Single

variable {η : ℝ}

section Algorithm

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] [Nonempty α]

/-- **Exp3** with learning rate `η` [LS, Algorithm 9]: Exp4-IX with the experts `α`, expert `b`
advising the Dirac mass at `b` at every observation, the constant learning rate `η` and no
implicit exploration. It draws its action of round `n` from the exponential weights of `-η` times
the cumulative importance-weighted loss estimates computed from the history, and ignores the
observations. -/
noncomputable def exp3 (η : ℝ) : Algorithm 𝓞 α ℝ :=
  exp4IX singleAdvice measurable_singleAdvice (fun _ ↦ η) 0

lemma exp3_def (η : ℝ) :
    exp3 (𝓞 := 𝓞) (α := α) η = exp4IX singleAdvice measurable_singleAdvice (fun _ ↦ η) 0 :=
  (rfl)

end Algorithm

namespace Exp3

variable [Nonempty α] {Ω : Type*} {n : ℕ}

/-- **Pathwise bound on the estimated regret of Exp3.** Along every sequence of observations `O`,
actions `A` and feedbacks `Y ≤ 1` of the rounds `t < n`, with `P t` the weights of Exp3 at round
`t` and `X̂ t` its loss-based importance-weighted reward estimates, for every arm `a` and `η > 0`,
`∑ t < n, (X̂ t a - Y t) ≤ log k / η + η / 2 * ∑ t < n, (1 - Y t) ^ 2 / P t (A t)`. This is the
local-norm bound of Exp4-IX for the constant learning rate `η` and `γ = 0`. -/
theorem sum_lossIwEstimator_sub_le (hη : 0 < η) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → ℝ) (ω : Ω) (hY : ∀ t < n, Y t ω ≤ 1) (a : α) :
    ∑ t ∈ range n, (lossIwEstimator (exp4IXWeights singleAdvice
        (fun _ ↦ η) 0 t (history O A Y t ω) (O t ω)) (A t ω) (Y t ω) a - Y t ω) ≤
      log (Fintype.card α) / η + η / 2 * ∑ t ∈ range n, (1 - Y t ω) ^ 2 /
        exp4IXWeights singleAdvice (fun _ ↦ η) 0 t
          (history O A Y t ω) (O t ω) (A t ω) := by
  have key := Exp4IX.sum_sum_mul_sub_dotProduct_le
    (adv := singleAdvice) (η := fun _ ↦ η) (γ := 0) O A Y ω
    (fun _ ↦ hη) antitone_const (fun _ ↦ le_rfl) hY a
  -- the regret and second-order terms of the loss estimates in terms of `Y t`
  have h1 : ∀ (p : α → ℝ) (b : α) (y : ℝ), p b ≠ 0 →
      ∑ c, p c * iwEstimator p b (1 - y) c - iwEstimator p b (1 - y) a =
        lossIwEstimator p b y a - y := fun p b y hb ↦ by
    rw [sum_mul_iwEstimator hb, lossIwEstimator_apply]
    ring
  -- with `γ = 0`, the estimates are the importance-weighted estimates for the weights on the arms
  simp only [Pi.zero_apply, add_zero, coe_singleAdvice, single_dotProduct, one_mul,
    sum_mul_iwEstimator_sq, ← Finset.mul_sum] at key
  rwa [Finset.sum_congr rfl fun t _ ↦ h1 _ _ _ (exp4IXWeights_single_pos _ _ _ _).ne'] at key

end Exp3

end LMLExplore.Bandits
