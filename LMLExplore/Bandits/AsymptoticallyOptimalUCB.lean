/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.SumRewards
public import LMLExplore.Bandits.IndexAlgorithm

/-!
# Asymptotically optimal UCB

The asymptotically optimal UCB algorithm [LS, Algorithm 6] for σ²-sub-Gaussian rewards is the
index policy whose index at book round `t`, for an arm `a` pulled `T_a > 0` times with empirical
mean `μ̂_a`, is `μ̂_a + √(2 σ² log f(t) / T_a)` with `f(t) = 1 + t log² t`. An arm that has not
been pulled yet has index `⊤`, so that the policy pulls every arm once before comparing finite
indices. Unlike LML's `ucbAlgorithm`, it is stated for any finite type of arms, does not
depend on an enumeration of the arms, and its exploration level `log f(t)` is the one for which
[LS, Theorem 8.1] gives the asymptotically optimal constant `2 σ² / Δ_a`.

Book round `t` is Lean round `n = t - 1`, at which the history has length `n`: the index of
Lean round `n` uses `log f(n + 1)`.

## Main definitions

* `LMLExplore.Bandits.ucbFIndex σ2 n h a`: the index of arm `a` after the history `h` of length
  `n`.
* `LMLExplore.Bandits.ucbF σ2`: the asymptotically optimal UCB algorithm, the index policy
  `indexAlgorithm` with index `ucbFIndex σ2`.

## Main statements

* `ucbFIndex_eq_top_iff`: the index is `⊤` exactly on the arms not pulled yet.
* `UCBF.pullCount_card_eq_one`: `ucbF σ2` pulls every arm exactly once during the first
  `Fintype.card α` rounds.
* `ucbFIndex_history`: along a sequence of rounds, the index in terms of LML's `pullCount` and
  `empMean`.
* `UCBF.integral_pullCount_le_sum_add_sum`: the decomposition of the expected number of pulls of
  an arm `a` in the proof of [LS, Theorem 8.1]: for every arm `b` and threshold `c`,
  `E[T_a(n)]` is at most the sum over the rounds `t < n` of the probabilities that the index of
  `b` is at most `c`, plus the sum over `t < n` of the probabilities that `a` is played at round
  `t` with an index above `c` for the exploration level `log f(n)` of the horizon.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 8.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Learning

open scoped NNReal

namespace LMLExplore.Bandits

section Index

variable {α : Type*} [DecidableEq α] {σ2 : ℝ≥0} {n : ℕ} {h : Hist Unit α ℝ n} {a : α}

/-- The index of the asymptotically optimal UCB algorithm [LS, Algorithm 6] at Lean round `n`
(book round `n + 1`), for the history `h` of the first `n` rounds: `⊤` if the arm `a` has not been
pulled, and otherwise `μ̂_a + √(2 σ² log f(n + 1) / T_a)` with `f(t) = 1 + t log² t`, where `T_a`
is the number of pulls of `a` and `μ̂_a` its empirical mean. -/
noncomputable def ucbFIndex (σ2 : ℝ≥0) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) : EReal :=
  if pullCount' n h a = 0 then ⊤ else
    ((empMean' n h a +
      √(2 * σ2 * log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount' n h a) : ℝ) : EReal)

/-- The defining equation of `ucbFIndex`. -/
lemma ucbFIndex_def (σ2 : ℝ≥0) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) :
    ucbFIndex σ2 n h a = if pullCount' n h a = 0 then ⊤ else
      ((empMean' n h a +
        √(2 * σ2 * log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount' n h a) : ℝ) : EReal) :=
  (rfl)

/-- An arm that has not been pulled has index `⊤`. -/
@[simp]
lemma ucbFIndex_of_pullCount'_eq_zero (h0 : pullCount' n h a = 0) : ucbFIndex σ2 n h a = ⊤ := by
  simp [ucbFIndex_def, h0]

/-- The index of an arm that has been pulled is `μ̂_a + √(2 σ² log f(n + 1) / T_a)`. -/
lemma ucbFIndex_of_pullCount'_ne_zero (h0 : pullCount' n h a ≠ 0) :
    ucbFIndex σ2 n h a =
      ((empMean' n h a +
        √(2 * σ2 * log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount' n h a) : ℝ) : EReal) := by
  simp [ucbFIndex_def, h0]

/-- The index of an arm is `⊤` if and only if the arm has not been pulled yet. -/
lemma ucbFIndex_eq_top_iff : ucbFIndex σ2 n h a = ⊤ ↔ pullCount' n h a = 0 := by
  by_cases h0 : pullCount' n h a = 0
  · simp [h0]
  · simp [ucbFIndex_of_pullCount'_ne_zero h0, h0]

@[fun_prop]
lemma measurable_ucbFIndex [MeasurableSpace α] [MeasurableSingletonClass α]
    (σ2 : ℝ≥0) (n : ℕ) : Measurable (ucbFIndex (α := α) σ2 n) := by
  refine Measurable.of_eval fun a ↦ ?_
  simp_rw [ucbFIndex_def]
  refine Measurable.ite ?_ measurable_const (by fun_prop)
  exact (measurableSet_singleton 0).preimage (measurable_pullCount' n a)

/-- Along a sequence of rounds `(O, A, R)`, the index of an arm at round `n` is `⊤` if the arm has
not been pulled before `n`, and otherwise `μ̂_a + √(2 σ² log f(n + 1) / T_a)` for the number of
pulls `T_a = pullCount A a n ω` and the empirical mean `μ̂_a = empMean A R a n ω`. -/
lemma ucbFIndex_history {Ω : Type*} (O : ℕ → Ω → Unit) (A : ℕ → Ω → α) (R : ℕ → Ω → ℝ)
    (σ2 : ℝ≥0) (n : ℕ) (ω : Ω) (a : α) :
    ucbFIndex σ2 n (history O A R n ω) a = if pullCount A a n ω = 0 then ⊤ else
      ((empMean A R a n ω +
        √(2 * σ2 * log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount A a n ω) : ℝ) : EReal) := by
  rw [ucbFIndex_def, ← pullCount_eq_pullCount', ← empMean_eq_empMean']

end Index

section Algorithm

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- The asymptotically optimal UCB algorithm [LS, Algorithm 6] for σ²-sub-Gaussian rewards: the
index policy with index `ucbFIndex σ2`, which plays at round `n` an arm of maximal index, ties
being broken by LML's `argmax`. -/
noncomputable def ucbF (σ2 : ℝ≥0) : Algorithm Unit α ℝ :=
  indexAlgorithm (fun n x ↦ ucbFIndex σ2 n x.1)
    fun n ↦ (measurable_ucbFIndex σ2 n).comp measurable_fst

/-- The asymptotically optimal UCB algorithm is the index policy with index `ucbFIndex σ2`. -/
lemma ucbF_def (σ2 : ℝ≥0) :
    ucbF (α := α) σ2 =
      indexAlgorithm (fun n x ↦ ucbFIndex σ2 n x.1)
        fun n ↦ (measurable_ucbFIndex σ2 n).comp measurable_fst :=
  (rfl)

namespace UCBF

variable {σ2 : ℝ≥0} {Ω : Type*} {mΩ : MeasurableSpace Ω} {env : Environment Unit α ℝ}
  {P : Measure Ω} [IsFiniteMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- The asymptotically optimal UCB algorithm pulls every arm exactly once during the first
`Fintype.card α` rounds. -/
lemma pullCount_card_eq_one (h : IsAlgEnvSeq O A R (ucbF σ2) env P) :
    ∀ᵐ ω ∂P, ∀ a, pullCount A a (Fintype.card α) ω = 1 := by
  rw [ucbF_def] at h
  exact IndexAlgorithm.pullCount_card_eq_one h fun _ _ _ ↦ ucbFIndex_eq_top_iff

/-- The decomposition of the expected number of pulls of an arm `a` by the asymptotically optimal
UCB algorithm, in the proof of [LS, Theorem 8.1]. For every arm `b` (typically an optimal arm) and
every threshold `c` (typically `μ* - ε`), `E[T_a(n)]` is at most the sum over the rounds `t < n`
of the probabilities that `b` has been pulled with index `μ̂_b + √(2 σ² log f(t + 1) / T_b)` at
most `c`, plus the sum over `t < n` of the probabilities that `a` is played at round `t` while
either it has not been pulled yet or `c < μ̂_a + √(2 σ² log f(n) / T_a)`. The exploration level
`log f(t + 1)` of round `t` is bounded by that of the horizon `n` in the second sum, so that the
event only depends on `T_a` and `μ̂_a`. -/
theorem integral_pullCount_le_sum_add_sum (h : IsAlgEnvSeq O A R (ucbF σ2) env P) (a b : α)
    (c : ℝ) (n : ℕ) :
    ∫ ω, (pullCount A a n ω : ℝ) ∂P ≤
      ∑ t ∈ range n, P.real {ω | pullCount A b t ω ≠ 0 ∧
        empMean A R b t ω + √(2 * σ2 * log (1 + (t + 1) * log (t + 1) ^ 2) / pullCount A b t ω)
          ≤ c} +
      ∑ t ∈ range n, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨
        c < empMean A R a t ω + √(2 * σ2 * log (1 + n * log n ^ 2) / pullCount A a t ω))} := by
  rw [ucbF_def] at h
  refine (IndexAlgorithm.integral_pullCount_le_sum_add_sum h a b c n).trans
    (add_le_add (sum_le_sum fun t _ ↦ le_of_eq ?_) (sum_le_sum fun t ht ↦ measureReal_mono ?_))
  · congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, ucbFIndex_history]
    split_ifs with h0
    · simp [h0]
    · rw [EReal.coe_le_coe_iff]
      exact (and_iff_right h0).symm
  · -- The exploration level `log f(t + 1)` of round `t < n` is at most `log f(n)`.
    have hlog : log (1 + (t + 1) * log (t + 1) ^ 2) ≤ log (1 + n * log n ^ 2) := by
      have htn : (t : ℝ) + 1 ≤ n := by exact_mod_cast mem_range.mp ht
      have hlog0 : 0 ≤ log ((t : ℝ) + 1) := log_nonneg (by linarith [t.cast_nonneg (α := ℝ)])
      have hlogle : log ((t : ℝ) + 1) ≤ log n := log_le_log (by positivity) htn
      gcongr
    intro ω hω
    simp only [Set.mem_ofPred_eq, ucbFIndex_history] at hω ⊢
    refine ⟨hω.1, ?_⟩
    split_ifs at hω with h0
    · exact Or.inl h0
    · refine Or.inr ((EReal.coe_lt_coe_iff.mp hω.2).trans_le ?_)
      gcongr

end UCBF

end Algorithm

end LMLExplore.Bandits
