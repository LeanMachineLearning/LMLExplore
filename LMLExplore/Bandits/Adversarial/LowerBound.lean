/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.Adversarial.Regret
public import LMLExplore.Bandits.MinimaxLowerBound

/-!
# The minimax lower bound for adversarial bandits

A stochastic bandit `Environment.bandit ν` is a mixture of oblivious adversaries, so the expected
adversarial regret over the reward tables `x ∼ streamMeasure ν` dominates the expected stochastic
regret (`LMLExplore.Bandits.integral_regret_le_integral_advRegret`). With Bernoulli arms the
tables take values in `{0, 1}`, and the minimax lower bound for Bernoulli bandits
(`LMLExplore.Bandits.exists_sqrt_le_integral_regret_bernoulliBandit`) gives, for every
algorithm, a table `x ∈ {0, 1}^{ℕ × α}` with `R_n(x) ≥ √(3 (k - 1) n / 32) / 16`. This is the
randomization argument of the adversarial lower bound of [ACFS02], adapting [LS, Theorem 15.2]
(which has the constant `1 / 27`) to Bernoulli arms, with the constant `1 / 16`; the factor
`3 / 32` is the variance proxy `σ²` that bounds the relative entropy between Bernoulli arms with
means in `[1 / 4, 3 / 4]`. Up to the factor `√(log k)`, it matches the upper bound
`√(2 n k log k)` of Exp3 [LS, Theorem 11.2].

## Main statements

* `LMLExplore.Bandits.exists_sqrt_le_advRegret`: the minimax lower bound for adversarial bandits.

## References

* [ACFS02] P. Auer, N. Cesa-Bianchi, Y. Freund and R. E. Schapire, *The nonstochastic
  multiarmed bandit problem*, SIAM J. Comput. 32(1), 2002.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Bandits
open scoped unitInterval

namespace LMLExplore.Bandits

variable {α : Type*} [MeasurableSpace α] (alg : Algorithm Unit α ℝ)

/-- **Minimax lower bound for adversarial bandits** [ACFS02]: for `k ≥ 2` arms and
`3 (k - 1) ≤ 8 n`, every algorithm has, against some
oblivious adversary with a reward table `x` with values in `{0, 1}`, an adversarial regret
`R_n(x)` at least `√(3 (k - 1) n / 32) / 16`. By
`Learning.IsAlgEnvSeq.advRegret_eq_advRegret_trajMeasure`, the bound holds for every run of the
algorithm against `Environment.evalSeq x _`. -/
theorem exists_sqrt_le_advRegret [Fintype α] [MeasurableSingletonClass α] (n : ℕ)
    (hk : 2 ≤ Fintype.card α)
    (hn : 3 * (Fintype.card α - 1 : ℝ) ≤ 8 * n) :
    ∃ x : ℕ → α → ℝ, (∀ t a, x t a ∈ ({0, 1} : Set ℝ)) ∧
      √(3 / 32 * (Fintype.card α - 1) * n) / 16 ≤
        advRegret x IT.action (trajMeasure alg (Environment.evalSeq x fun _ ↦ .of_discrete)) n := by
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨p, -, hR⟩ := exists_sqrt_le_integral_regret_bernoulliBandit alg n hk hn
  have hν := integrable_id_bernoulliBandit p
  have hle := hR.trans (integral_regret_le_integral_advRegret alg
    (IT.isAlgEnvSeq_trajMeasure alg _) hν n)
  obtain ⟨x, hx, hxR⟩ := exists_notMem_null_integral_le
    (integrable_advRegret_evalSeq alg hν n)
    (N := {x | ¬ ∀ t a, x t a ∈ ({0, 1} : Set ℝ)})
    (ae_iff.1 (ae_mem_streamMeasure_bernoulliBandit p))
  exact ⟨x, not_not.1 hx, hle.trans hxR⟩

end LMLExplore.Bandits
