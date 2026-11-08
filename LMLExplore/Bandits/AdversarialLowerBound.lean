/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.AdversarialRegret
public import LMLExplore.Bandits.MinimaxLowerBound
public import LMLExplore.Bandits.TableModel

/-!
# The minimax lower bound for adversarial bandits

A stochastic bandit `Environment.bandit ν` is a mixture of oblivious adversaries: the law of a run
against it is the mixture, over the reward tables `x ∼ streamMeasure ν` whose rows are independent
with law `⨂ a, ν a`, of the laws of the runs against `Environment.evalSeq x _`
(`LMLExplore.Bandits.trajMeasure_bandit_eq_bind`). Averaging the adversarial regret
`R_n(x) = max_a ∑_{t < n} x t a - E[∑_{t < n} x t (A t)]` over these tables, the expected
reward of the learner averages to its expected reward against the stochastic bandit, while the
average of the reward `max_a ∑_{t < n} x t a` of the best arm in hindsight is at least the reward
`n max_a μ_a` of the best arm in expectation. So the expected adversarial regret over i.i.d.
tables dominates the expected stochastic regret.

With Bernoulli arms the tables take values in `{0, 1}`, and the minimax lower bound for Bernoulli
bandits (`LMLExplore.Bandits.exists_sqrt_le_integral_regret_bernoulliBandit`) gives, for every
algorithm, a table `x ∈ {0, 1}^{ℕ × α}` with `R_n(x) ≥ √(3 (k - 1) n / 32) / 16`. This is the
randomization argument of the adversarial lower bound of [ACFS02], with the constants of
[LS, Theorem 15.2]. Up to the factor `√(log k)`, it matches the upper bound `√(2 n k log k)` of
Exp3 [LS, Theorem 11.2].

## Main statements

* `LMLExplore.Bandits.integral_regret_le_integral_advRegret`: the expected stochastic regret
  against `Environment.bandit ν` is at most the expected adversarial regret over the tables
  `x ∼ streamMeasure ν`.
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

variable {α : Type*} [MeasurableSpace α] {ν : Kernel α ℝ} [IsMarkovKernel ν]

/-- The total reward of each arm over the first `n` rows of a table `x ∼ streamMeasure ν` is
integrable when the arms are. -/
private lemma integrable_sum_eval_streamMeasure (hν : ∀ a, Integrable id (ν a)) (n : ℕ) (a : α) :
    Integrable (fun x : ℕ → α → ℝ ↦ ∑ t ∈ range n, x t a) (streamMeasure ν) :=
  integrable_finsetSum _ fun t _ ↦ integrable_eval_streamMeasure ν t a (hν a)

/-- The total reward `max_a ∑_{t < n} x t a` of the best arm in hindsight is integrable over the
tables `x ∼ streamMeasure ν` when the arms are. -/
private lemma integrable_iSup_sum_streamMeasure [Finite α] [Nonempty α]
    (hν : ∀ a, Integrable id (ν a)) (n : ℕ) :
    Integrable (fun x : ℕ → α → ℝ ↦ ⨆ a, ∑ t ∈ range n, x t a) (streamMeasure ν) := by
  have := Fintype.ofFinite α
  refine (integrable_finsetSum univ fun a _ ↦
    (integrable_sum_eval_streamMeasure hν n a).norm).mono' ?_ (ae_of_all _ fun x ↦ ?_)
  · exact (Measurable.iSup fun a ↦ Finset.measurable_sum _ fun t _ ↦
      (measurable_pi_apply a).comp (measurable_pi_apply t)).aestronglyMeasurable
  · obtain ⟨a₀, ha₀⟩ := exists_eq_ciSup_of_finite (f := fun a ↦ ∑ t ∈ range n, x t a)
    rw [← ha₀]
    exact single_le_sum (f := fun a ↦ ‖∑ t ∈ range n, x t a‖) (fun _ _ ↦ norm_nonneg _)
      (mem_univ a₀)

/-- In expectation over the tables `x ∼ streamMeasure ν`, the total reward of the best arm in
hindsight is at least `n` times the best mean. -/
private lemma mul_iSup_le_integral_iSup_sum [Finite α] (hν : ∀ a, Integrable id (ν a)) (n : ℕ)
    (a : α) :
    n * (ν a)[id] ≤ ∫ x, ⨆ a, ∑ t ∈ range n, x t a ∂(streamMeasure ν) := by
  have : Nonempty α := ⟨a⟩
  calc n * (ν a)[id] = ∫ x, ∑ t ∈ range n, x t a ∂(streamMeasure ν) := by
        rw [integral_finsetSum _ fun t _ ↦ integrable_eval_streamMeasure ν t a (hν a)]
        simp [integral_eval_streamMeasure]
    _ ≤ ∫ x, ⨆ a, ∑ t ∈ range n, x t a ∂(streamMeasure ν) :=
        integral_mono (integrable_sum_eval_streamMeasure hν n a)
          (integrable_iSup_sum_streamMeasure hν n)
          fun x ↦ le_ciSup (Finite.bddAbove_range fun a ↦ ∑ t ∈ range n, x t a) a

variable (alg : Algorithm Unit α ℝ)

/-- The total feedback of the first `n` rounds, a function of the sequence of rounds. -/
private lemma measurable_sum_feedback (n : ℕ) :
    Measurable fun τ : ℕ → Round Unit α ℝ ↦ ∑ t ∈ range n, IT.feedback t τ :=
  Finset.measurable_sum _ fun t _ ↦ IT.measurable_feedback t

private lemma integrable_sum_feedback_bandit [Finite α] (hν : ∀ a, Integrable id (ν a)) (n : ℕ) :
    Integrable (fun τ : ℕ → Round Unit α ℝ ↦ ∑ t ∈ range n, IT.feedback t τ)
      (trajMeasure alg (Environment.bandit ν)) :=
  integrable_finsetSum _ fun t _ ↦
    (IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν)).integrable_feedback_bandit hν t

/-- The adversarial regret of the run against `Environment.evalSeq x _` is an integrable function
of the table `x ∼ streamMeasure ν` when the arms are integrable. -/
lemma integrable_advRegret_evalSeq [Finite α] [Nonempty α] [MeasurableSingletonClass α]
    (hν : ∀ a, Integrable id (ν a)) (n : ℕ) :
    Integrable (fun x : ℕ → α → ℝ ↦
      advRegret x IT.action (trajMeasure alg (Environment.evalSeq x fun _ ↦ .of_discrete)) n)
      (streamMeasure ν) := by
  simp_rw [(IT.isAlgEnvSeq_trajMeasure alg _).advRegret_eq_sub_integral_sum_feedback]
  exact (integrable_iSup_sum_streamMeasure hν n).sub
    (integrable_integral_trajMeasure_evalSeq alg ν (measurable_sum_feedback n).stronglyMeasurable
      (integrable_sum_feedback_bandit alg hν n))

/-- **The adversarial regret dominates the stochastic regret.** The expected regret of a run of an
algorithm against the stochastic bandit `Environment.bandit ν` with integrable arms is at most the
expectation, over the tables `x ∼ streamMeasure ν` whose rows are independent with law
`⨂ a, ν a`, of the adversarial regret `R_n(x)` of the algorithm against
`Environment.evalSeq x _`. -/
theorem integral_regret_le_integral_advRegret [Finite α] [Nonempty α] [MeasurableSingletonClass α]
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
    {Y : ℕ → Ω → ℝ} (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P)
    (hν : ∀ a, Integrable id (ν a)) (n : ℕ) :
    P[regret ν A n] ≤ ∫ x, advRegret x IT.action
      (trajMeasure alg (Environment.evalSeq x fun _ ↦ .of_discrete)) n ∂(streamMeasure ν) := by
  have h' := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν)
  have hY (t : ℕ) := h'.integrable_feedback_bandit hν t
  -- the expected regret is `max_a (n μ_a - L)`, with `L` the expected total reward of the learner
  rw [h.integral_regret_eq_integral_trajMeasure, ← h'.pseudoRegret_bandit hν n, pseudoRegret_def]
  simp_rw [means_bandit, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  -- the expected adversarial regret is `E[max_a ∑_{t < n} x t a] - L`
  simp_rw [(IT.isAlgEnvSeq_trajMeasure alg _).advRegret_eq_sub_integral_sum_feedback]
  rw [integral_sub (integrable_iSup_sum_streamMeasure hν n)
      (integrable_integral_trajMeasure_evalSeq alg ν (measurable_sum_feedback n).stronglyMeasurable
        (integrable_sum_feedback_bandit alg hν n)),
    ← integral_trajMeasure_bandit alg ν (measurable_sum_feedback n).stronglyMeasurable
      (integrable_sum_feedback_bandit alg hν n)]
  refine ciSup_le fun a ↦ ?_
  rw [integral_sub (integrable_const _) (integrable_finsetSum _ fun t _ ↦ hY t), integral_const,
    probReal_univ, one_smul, integral_finsetSum _ fun t _ ↦ hY t]
  exact sub_le_sub_right (mul_iSup_le_integral_iSup_sum hν n a) _

/-- The tables of a Bernoulli bandit take values in `{0, 1}` almost surely. -/
private lemma ae_mem_streamMeasure_bernoulliBandit [Countable α] [MeasurableSingletonClass α]
    (p : α → I) :
    ∀ᵐ x ∂(streamMeasure (bernoulliBandit p)), ∀ t a, x t a ∈ ({0, 1} : Set ℝ) := by
  rw [ae_all_iff]
  intro t
  rw [ae_all_iff]
  intro a
  have h01 : ∀ᵐ y ∂(bernoulliBandit p a), y ∈ ({0, 1} : Set ℝ) := by
    rw [bernoulliBandit_apply, ae_iff]
    exact bernoulliMeasure_apply_of_notMem_of_notMem (p a)
      (MeasurableSet.compl (by measurability)) (by simp) (by simp)
  rw [← (hasLaw_eval_eval_streamMeasure (bernoulliBandit p) t a).map_eq] at h01
  exact ae_of_ae_map ((measurable_pi_apply a).comp (measurable_pi_apply t)).aemeasurable h01

/-- **Minimax lower bound for adversarial bandits** [ACFS02]: for `k ≥ 2` arms and
`3 (k - 1) ≤ 8 n`, every algorithm has, against some
oblivious adversary with a reward table `x` with values in `{0, 1}`, an adversarial regret
`R_n(x)` at least `√(3 (k - 1) n / 32) / 16`. By
`Learning.IsAlgEnvSeq.advRegret_eq_advRegret_trajMeasure`, the bound holds for every run of the
algorithm against `Environment.evalSeq x _`. -/
theorem exists_sqrt_le_advRegret [Fintype α] [Nonempty α] [MeasurableSingletonClass α] (n : ℕ)
    (hk : 2 ≤ Fintype.card α)
    (hn : 3 * (Fintype.card α - 1 : ℝ) ≤ 8 * n) :
    ∃ x : ℕ → α → ℝ, (∀ t a, x t a ∈ ({0, 1} : Set ℝ)) ∧
      √(3 / 32 * (Fintype.card α - 1) * n) / 16 ≤
        advRegret x IT.action (trajMeasure alg (Environment.evalSeq x fun _ ↦ .of_discrete)) n := by
  obtain ⟨p, -, hR⟩ := exists_sqrt_le_integral_regret_bernoulliBandit alg n hk hn
  have hν : ∀ a, Integrable id (bernoulliBandit p a) := fun a ↦
    Integrable.of_bound (C := 1) aestronglyMeasurable_id <| by
      filter_upwards [ae_mem_Icc_bernoulliBandit p a] with y hy
      rw [id, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hy.1], hy.2⟩
  have hle := hR.trans (integral_regret_le_integral_advRegret alg
    (IT.isAlgEnvSeq_trajMeasure alg _) hν n)
  obtain ⟨x, hx, hxR⟩ := exists_notMem_null_integral_le
    (integrable_advRegret_evalSeq alg hν n)
    (N := {x | ¬ ∀ t a, x t a ∈ ({0, 1} : Set ℝ)})
    (ae_iff.1 (ae_mem_streamMeasure_bernoulliBandit p))
  exact ⟨x, not_not.1 hx, hle.trans hxR⟩

end LMLExplore.Bandits
