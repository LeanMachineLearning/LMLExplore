/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.Bandit.Regret
public import LMLExplore.Bandits.Concentration
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
* `UCBF.integral_pullCount_le`: the bound
  `1 + 5 σ² / ε² + 2 σ² (log f(n) + √(π log f(n)) + 1) / (Δ_a - ε)²` on the expected number of
  pulls of an arm `a` with gap `Δ_a`, for every `ε ∈ (0, Δ_a)`.
* `ucbF_regret_le`: [LS, Theorem 8.1], the finite-time bound on the expected regret.

## Implementation notes

The proof of [LS, Theorem 8.1] bounds the two sums of `UCBF.integral_pullCount_le_sum_add_sum`,
for an optimal arm `b` and the threshold `μ* - ε`. The first sum, the underestimation of `b`, is
at most `5 σ² / ε²` by `sum_measureReal_pullCount_ne_zero_and_empMean_add_sqrt_le_le`. The second
sum, the overestimation of `a` by more than `Δ_a - ε`, is bounded by [LS, Lemma 8.2] in LML's
i.i.d. reward stream model, by
`sum_measureReal_action_eq_and_pullCount_eq_zero_or_lt_empMean_add_sqrt_le`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 8.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Learning Bandits

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

section Regret

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {ν : Kernel α ℝ} [IsMarkovKernel ν] {σ2 : ℝ≥0}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- **[LS, Theorem 8.1], number of pulls.** For σ²-sub-Gaussian rewards with `σ² ≠ 0`, the
asymptotically optimal UCB algorithm pulls an arm `a` with gap `Δ_a` at most
`1 + 5 σ² / ε² + 2 σ² (log f(n) + √(π log f(n)) + 1) / (Δ_a - ε)²` times in expectation during the
first `n` rounds, for every `ε ∈ (0, Δ_a)`, where `f(n) = 1 + n log² n`. -/
theorem UCBF.integral_pullCount_le (h : IsAlgEnvSeq O A R (ucbF σ2) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0) (a : α)
    {ε : ℝ} (hε : 0 < ε) (hεa : ε < gap ν a) (n : ℕ) :
    P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤
      1 + 5 * σ2 / ε ^ 2 + 2 * σ2 * (log (1 + n * log n ^ 2) +
        √(π * log (1 + n * log n ^ 2)) + 1) / (gap ν a - ε) ^ 2 := by
  set μs := (ν (bestArm ν))[id] with hμs
  set L := log (1 + n * log n ^ 2) with hL
  have hL0 : 0 ≤ L := log_nonneg (by linarith [(by positivity : (0 : ℝ) ≤ n * log n ^ 2)])
  have hgap : gap ν a = μs - (ν a)[id] := gap_eq_bestArm_sub
  have h_thr : μs - ε = (ν a)[id] + (gap ν a - ε) := by
    rw [hgap]
    ring
  calc P[fun ω ↦ (pullCount A a n ω : ℝ)]
  _ ≤ ∑ t ∈ range n, P.real {ω | pullCount A (bestArm ν) t ω ≠ 0 ∧
        empMean A R (bestArm ν) t ω + √(2 * σ2 * log (1 + (t + 1) * log (t + 1) ^ 2) /
          pullCount A (bestArm ν) t ω) ≤ μs - ε} +
      ∑ t ∈ range n, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨
        μs - ε < empMean A R a t ω + √(2 * σ2 * L / pullCount A a t ω))} :=
    UCBF.integral_pullCount_le_sum_add_sum h a (bestArm ν) (μs - ε) n
  _ ≤ 5 * σ2 / ε ^ 2 + (1 + 2 * σ2 / (gap ν a - ε) ^ 2 * (L + √(π * L) + 1)) :=
    add_le_add (sum_measureReal_pullCount_ne_zero_and_empMean_add_sqrt_le_le h (bestArm ν)
      (hν _) hσ2 hε n) (h_thr ▸
        sum_measureReal_action_eq_and_pullCount_eq_zero_or_lt_empMean_add_sqrt_le h a (hν a)
          (sub_pos.mpr hεa) hL0 n)
  _ = 1 + 5 * σ2 / ε ^ 2 + 2 * σ2 * (L + √(π * L) + 1) / (gap ν a - ε) ^ 2 := by ring

/-- **[LS, Theorem 8.1]** For σ²-sub-Gaussian rewards with `σ² ≠ 0`, the expected regret of the
asymptotically optimal UCB algorithm at horizon `n` is at most the sum over the arms `a` with
positive gap `Δ_a` of
`inf_{ε ∈ (0, Δ_a)} Δ_a (1 + 5 σ² / ε² + 2 σ² (log f(n) + √(π log f(n)) + 1) / (Δ_a - ε)²)`,
where `f(n) = 1 + n log² n`. -/
theorem ucbF_regret_le [StandardBorelSpace α]
    (h : IsAlgEnvSeq O A R (ucbF σ2) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0) (n : ℕ) :
    P[regret ν A n] ≤ ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a), ⨅ ε : Set.Ioo 0 (gap ν a),
      gap ν a * (1 + 5 * σ2 / (ε : ℝ) ^ 2 + 2 * σ2 * (log (1 + n * log n ^ 2) +
        √(π * log (1 + n * log n ^ 2)) + 1) / (gap ν a - ε) ^ 2) := by
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount h.measurable_action,
    ← sum_filter_of_ne fun a _ ha ↦ gap_nonneg.lt_of_ne' (left_ne_zero_of_mul ha)]
  refine sum_le_sum fun a ha ↦ ?_
  have : Nonempty (Set.Ioo 0 (gap ν a)) := (Set.nonempty_Ioo.mpr (mem_filter.mp ha).2).to_subtype
  exact le_ciInf fun ε ↦ mul_le_mul_of_nonneg_left
    (UCBF.integral_pullCount_le h hν hσ2 a ε.2.1 ε.2.2 n) gap_nonneg

end Regret

end LMLExplore.Bandits
