/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.Bandit.Regret
public import LeanMachineLearning.SequentialLearning.SumRewards
public import LMLExplore.Analysis.SpecialFunctions.Log.Basic
public import LMLExplore.Bandits.Concentration
public import LMLExplore.Bandits.IndexAlgorithm
public import LMLExplore.Bandits.Regret
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli

/-!
# KL-UCB

The KL-UCB algorithm [LS, Algorithm 8] for rewards in `[0, 1]` is the index policy whose index at
book round `t`, for an arm `a` pulled `T_a > 0` times with empirical mean `μ̂_a`, is the upper
confidence level `U(μ̂_a, log f(t) / T_a)` of the binary relative entropy, the largest
`q ∈ [μ̂_a, 1]` with `d(μ̂_a, q) ≤ log f(t) / T_a`, where `f(t) = 1 + t log² t`. An arm that has
not been pulled yet has index `⊤`, so that the policy pulls every arm once before comparing finite
indices. It is stated for any finite type of arms and does not depend on an enumeration of the
arms.

Book round `t` is Lean round `n = t - 1`, at which the history has length `n`: the index of
Lean round `n` uses `log f(n + 1)`.

## Main definitions

* `LMLExplore.Bandits.klucbIndex n h a`: the index of arm `a` after the history `h` of length `n`.
* `LMLExplore.Bandits.klucb`: the KL-UCB algorithm, the index policy `indexAlgorithm` with index
  `klucbIndex`.

## Main statements

* `klucbIndex_eq_top_iff`: the index is `⊤` exactly on the arms not pulled yet.
* `klucbIndex_history`: along a sequence of rounds, the index in terms of LML's `pullCount` and
  `empMean`.
* `KLUCB.pullCount_card_eq_one`: `klucb` pulls every arm exactly once during the first
  `Fintype.card α` rounds.
* `KLUCB.integral_pullCount_le_sum_add_sum`: the decomposition of the expected number of pulls of
  an arm `a` in the proof of [LS, Theorem 10.6]: for every arm `b` and threshold `c`, `E[T_a(n)]`
  is at most the sum over the rounds `t < n` of the probabilities that the index of `b` is at
  most `c`, plus the sum over `t < n` of the probabilities that `a` is played at round `t` while
  either it has not been pulled yet (`T_a = 0`), or its empirical mean `μ̂_a` is at least `c`, or
  `c ≤ 1` and `d(μ̂_a, c) ≤ log f(n) / T_a` for the exploration level `log f(n)` of the horizon.
* `KLUCB.integral_pullCount_le`: for rewards in `[0, 1]`, the bound
  `log f(n) / d(μ_a + ε₁, μ* - ε₂) + 1 / (2 ε₁²) + 2 / ε₂²` on the expected number of pulls of an
  arm `a` with gap `Δ_a`, for all `ε₁, ε₂ > 0` with `ε₁ + ε₂ < Δ_a`.
* `klucb_regret_le`: [LS, Theorem 10.6], the finite-time bound on the expected regret.
* `KLUCB.integral_pullCount_eventually_le`: for rewards in `[0, 1]`, an arm `a` with positive gap
  and every `c > 1 / d(μ_a, μ*)`, eventually `E[T_a(n)] ≤ c log n`, that is,
  `limsup_n E[T_a(n)] / log n ≤ 1 / d(μ_a, μ*)`.
* `klucb_regret_eventually_le`: the asymptotic part of [LS, Theorem 10.6]: for every
  `c > ∑_{a : Δ_a > 0} Δ_a / d(μ_a, μ*)`, eventually `E[R_n] ≤ c log n`, that is,
  `limsup_n E[R_n] / log n ≤ ∑_{a : Δ_a > 0} Δ_a / d(μ_a, μ*)`.

* `klucb_regret_eventually_le_of_integral_bestArm_eq_one`: when the largest mean is `1`, the
  expected regret is `o(log n)`.

In the asymptotic statements, `1 / d(μ_a, μ*)` and `Δ_a / d(μ_a, μ*)` are computed from the real
number `(klBer μ_a μ*).toReal`, which is `0` when `d(μ_a, μ*) = ∞`, so that both quantities are
then `0`. For an arm with positive gap, `d(μ_a, μ*) = ∞` happens exactly when `μ* = 1`: such an
arm is pulled `o(log n)` times in expectation.

## Implementation notes

The proof of [LS, Theorem 10.6] bounds the two sums of `KLUCB.integral_pullCount_le_sum_add_sum`,
for an optimal arm `b` and the threshold `μ* - ε₂`. The first sum, the underestimation of `b`, is
at most `3 / (4 ε₂²)` by `sum_measureReal_pullCount_ne_zero_and_klUpper_le_le` ([LS, Lemma 10.7]).
The second sum, the overestimation of `a`, is at most `1 + log f(n) / d(μ_a + ε₁, μ* - ε₂) +
1 / (2 ε₁²)` by `sum_measureReal_action_eq_and_pullCount_eq_zero_or_le_empMean_or_klBer_le_le`
([LS, Lemma 10.8]), where the `1` accounts for the first pull of `a`. Since `ε₂ < Δ_a ≤ 1`,
`1 + 3 / (4 ε₂²) ≤ 2 / ε₂²`.

For the asymptotic bound, `ε₁ = ε₂ = ε` is chosen small enough that
`1 / d(μ_a + ε, μ* - ε) < c`. This uses the lower semicontinuity of `d`
(`lowerSemicontinuous_klBer`), which also covers the case `d(μ_a, μ*) = ∞`. The bound of
`KLUCB.integral_pullCount_le` divided by `log n` then tends to `1 / d(μ_a + ε, μ* - ε)`, since
`log f(n) / log n → 1` (`Real.tendsto_log_one_add_mul_log_sq_div_log_atTop`). The book leaves
this limit to its Exercise 10.2.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 10.
* A. Garivier and O. Cappé, *The KL-UCB algorithm for bounded stochastic bandits and beyond*,
  COLT 2011.
-/

public section

open MeasureTheory ProbabilityTheory Finset Filter Topology Real Learning Bandits

open scoped ENNReal

namespace LMLExplore.Bandits

section Index

variable {α : Type*} [DecidableEq α] {n : ℕ} {h : Hist Unit α ℝ n} {a : α}

/-- The index of the KL-UCB algorithm [LS, Algorithm 8] at Lean round `n` (book round `n + 1`),
for the history `h` of the first `n` rounds: `⊤` if the arm `a` has not been pulled, and otherwise
the upper confidence level `U(μ̂_a, log f(n + 1) / T_a)` with `f(t) = 1 + t log² t`, where `T_a` is
the number of pulls of `a` and `μ̂_a` its empirical mean. -/
noncomputable def klucbIndex (n : ℕ) (h : Hist Unit α ℝ n) (a : α) : EReal :=
  if pullCount' n h a = 0 then ⊤ else
    ((klUpper (empMean' n h a)
      (ENNReal.ofReal (log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount' n h a)) : ℝ) : EReal)

/-- The defining equation of `klucbIndex`. -/
lemma klucbIndex_def (n : ℕ) (h : Hist Unit α ℝ n) (a : α) :
    klucbIndex n h a = if pullCount' n h a = 0 then ⊤ else
      ((klUpper (empMean' n h a)
        (ENNReal.ofReal (log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount' n h a)) : ℝ) : EReal) :=
  (rfl)

/-- An arm that has not been pulled has index `⊤`. -/
@[simp]
lemma klucbIndex_of_pullCount'_eq_zero (h0 : pullCount' n h a = 0) : klucbIndex n h a = ⊤ := by
  simp [klucbIndex_def, h0]

/-- The index of an arm that has been pulled is `U(μ̂_a, log f(n + 1) / T_a)`. -/
lemma klucbIndex_of_pullCount'_ne_zero (h0 : pullCount' n h a ≠ 0) :
    klucbIndex n h a =
      ((klUpper (empMean' n h a)
        (ENNReal.ofReal (log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount' n h a)) : ℝ) :
          EReal) := by
  simp [klucbIndex_def, h0]

/-- The index of an arm is `⊤` if and only if the arm has not been pulled yet. -/
lemma klucbIndex_eq_top_iff : klucbIndex n h a = ⊤ ↔ pullCount' n h a = 0 := by
  by_cases h0 : pullCount' n h a = 0
  · simp [h0]
  · simp [klucbIndex_of_pullCount'_ne_zero h0, h0]

@[fun_prop]
lemma measurable_klucbIndex [MeasurableSpace α] [MeasurableSingletonClass α] (n : ℕ) :
    Measurable (klucbIndex (α := α) n) := by
  refine Measurable.of_eval fun a ↦ ?_
  simp_rw [klucbIndex_def]
  refine Measurable.ite ?_ measurable_const (by fun_prop)
  exact (measurableSet_singleton 0).preimage (measurable_pullCount' n a)

/-- Along a sequence of rounds `(O, A, R)`, the index of an arm at round `n` is `⊤` if the arm has
not been pulled before `n`, and otherwise `U(μ̂_a, log f(n + 1) / T_a)` for the number of pulls
`T_a = pullCount A a n ω` and the empirical mean `μ̂_a = empMean A R a n ω`. -/
lemma klucbIndex_history {Ω : Type*} (O : ℕ → Ω → Unit) (A : ℕ → Ω → α) (R : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (a : α) :
    klucbIndex n (history O A R n ω) a = if pullCount A a n ω = 0 then ⊤ else
      ((klUpper (empMean A R a n ω)
        (ENNReal.ofReal (log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount A a n ω)) : ℝ) :
          EReal) := by
  rw [klucbIndex_def, ← pullCount_eq_pullCount', ← empMean_eq_empMean']

end Index

section Algorithm

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- The KL-UCB algorithm [LS, Algorithm 8] for rewards in `[0, 1]`: the index policy with index
`klucbIndex`, which plays at round `n` an arm of maximal index, ties being broken by LML's
`argmax`. -/
noncomputable def klucb : Algorithm Unit α ℝ :=
  indexAlgorithm (fun n x ↦ klucbIndex n x.1) fun n ↦ (measurable_klucbIndex n).comp measurable_fst

/-- The KL-UCB algorithm is the index policy with index `klucbIndex`. -/
lemma klucb_def :
    klucb (α := α) =
      indexAlgorithm (fun n x ↦ klucbIndex n x.1)
        fun n ↦ (measurable_klucbIndex n).comp measurable_fst :=
  (rfl)

namespace KLUCB

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {env : Environment Unit α ℝ}
  {P : Measure Ω} [IsFiniteMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- The KL-UCB algorithm pulls every arm exactly once during the first `Fintype.card α`
rounds. -/
lemma pullCount_card_eq_one (h : IsAlgEnvSeq O A R klucb env P) :
    ∀ᵐ ω ∂P, ∀ a, pullCount A a (Fintype.card α) ω = 1 := by
  rw [klucb_def] at h
  exact IndexAlgorithm.pullCount_card_eq_one h fun _ _ _ ↦ klucbIndex_eq_top_iff

/-- The decomposition of the expected number of pulls of an arm `a` by the KL-UCB algorithm, in
the proof of [LS, Theorem 10.6]. For every arm `b` (typically an optimal arm) and every threshold
`c` (typically `μ* - ε`), `E[T_a(n)]` is at most the sum over the rounds `t < n` of the
probabilities that `b` has been pulled with index `U(μ̂_b, log f(t + 1) / T_b)` at most `c`, plus
the sum over `t < n` of the probabilities that `a` is played at round `t` while either it has not
been pulled yet, or `c ≤ μ̂_a`, or `c ≤ 1` and `d(μ̂_a, c) ≤ log f(n) / T_a`. The exploration level
`log f(t + 1)` of round `t` is bounded by that of the horizon `n` in the second sum, so that the
event only depends on `T_a` and `μ̂_a`. -/
theorem integral_pullCount_le_sum_add_sum (h : IsAlgEnvSeq O A R klucb env P) (a b : α)
    (c : ℝ) (n : ℕ) :
    ∫ ω, (pullCount A a n ω : ℝ) ∂P ≤
      ∑ t ∈ range n, P.real {ω | pullCount A b t ω ≠ 0 ∧
        klUpper (empMean A R b t ω)
          (ENNReal.ofReal (log (1 + (t + 1) * log (t + 1) ^ 2) / pullCount A b t ω)) ≤ c} +
      ∑ t ∈ range n, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨ c ≤ empMean A R a t ω ∨
        c ≤ 1 ∧ klBer (empMean A R a t ω) c ≤
          ENNReal.ofReal (log (1 + n * log n ^ 2) / pullCount A a t ω))} := by
  rw [klucb_def] at h
  refine (IndexAlgorithm.integral_pullCount_le_sum_add_sum h a b c n).trans
    (add_le_add (sum_le_sum fun t _ ↦ le_of_eq ?_) (sum_le_sum fun t ht ↦ measureReal_mono ?_))
  · simp only [klucbIndex_history, apply_ite (· ≤ (c : EReal)), top_le_iff, EReal.coe_ne_top,
      ite_false_left, EReal.coe_le_coe_iff, ne_eq]
  · -- The exploration level `log f(t + 1)` of round `t < n` is at most `log f(n)`.
    have htn : t + 1 ≤ n := mem_range.mp ht
    have hlog : log (1 + (t + 1) * log (t + 1) ^ 2) ≤ log (1 + n * log n ^ 2) :=
      monotoneOn_log_one_add_mul_log_sq (by simp) (Nat.one_le_cast.2 (by omega))
        (by exact_mod_cast htn)
    intro ω hω
    simp only [Set.mem_ofPred_eq, klucbIndex_history] at hω ⊢
    refine ⟨hω.1, ?_⟩
    split_ifs at hω with h0
    · exact Or.inl h0
    · refine Or.inr (le_or_klBer_le_of_le_klUpper ((EReal.coe_lt_coe_iff.mp hω.2).le.trans ?_))
      exact monotone_klUpper _ (ENNReal.ofReal_le_ofReal (by gcongr))

end KLUCB

end Algorithm

section Regret

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {ν : Kernel α ℝ} [IsMarkovKernel ν]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- **[LS, Theorem 10.6], number of pulls.** For rewards in `[0, 1]`, the KL-UCB algorithm pulls
an arm `a` with gap `Δ_a` at most
`log f(n) / d(μ_a + ε₁, μ* - ε₂) + 1 / (2 ε₁²) + 2 / ε₂²` times in expectation during the first
`n` rounds, for all `ε₁, ε₂ > 0` with `ε₁ + ε₂ < Δ_a`, where `μ_a` is the mean of `a`, `μ*` the
largest mean and `f(n) = 1 + n log² n`. -/
theorem KLUCB.integral_pullCount_le (h : IsAlgEnvSeq O A R klucb (stationaryEnv ν) P)
    (hν : ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1) (a : α) {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (hε : ε₁ + ε₂ < gap ν a) (n : ℕ) :
    P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤
      log (1 + n * log n ^ 2) / klBerReal ((ν a)[id] + ε₁) ((ν (bestArm ν))[id] - ε₂) +
        1 / (2 * ε₁ ^ 2) + 2 / ε₂ ^ 2 := by
  set μs := (ν (bestArm ν))[id] with hμs
  set L := log (1 + n * log n ^ 2) with hL
  have hL0 : 0 ≤ L := log_nonneg (by linarith [(by positivity : (0 : ℝ) ≤ n * log n ^ 2)])
  have hgap : gap ν a = μs - (ν a)[id] := gap_eq_bestArm_sub
  -- the means lie in `[0, 1]`, so that `ε₂ < Δ_a ≤ 1`
  have hμ (b : α) : (ν b)[id] ∈ Set.Icc 0 1 := integral_id_mem_Icc_of_ae_mem_Icc (hν b)
  have hμs1 : μs ≤ 1 := (hμ (bestArm ν)).2
  have hε₂1 : ε₂ < 1 := by linarith [(hμ a).1]
  calc P[fun ω ↦ (pullCount A a n ω : ℝ)]
  _ ≤ ∑ t ∈ range n, P.real {ω | pullCount A (bestArm ν) t ω ≠ 0 ∧
        klUpper (empMean A R (bestArm ν) t ω)
          (ENNReal.ofReal (log (1 + (t + 1) * log (t + 1) ^ 2) / pullCount A (bestArm ν) t ω)) ≤
            μs - ε₂} +
      ∑ t ∈ range n, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨
        μs - ε₂ ≤ empMean A R a t ω ∨ μs - ε₂ ≤ 1 ∧
          klBer (empMean A R a t ω) (μs - ε₂) ≤ ENNReal.ofReal (L / pullCount A a t ω))} :=
    KLUCB.integral_pullCount_le_sum_add_sum h a (bestArm ν) (μs - ε₂) n
  _ ≤ 3 / (4 * ε₂ ^ 2) + (1 + L / klBerReal ((ν a)[id] + ε₁) (μs - ε₂) + 1 / (2 * ε₁ ^ 2)) :=
    add_le_add (sum_measureReal_pullCount_ne_zero_and_klUpper_le_le h (bestArm ν) (hν _) hε₂ n)
      (sum_measureReal_action_eq_and_pullCount_eq_zero_or_le_empMean_or_klBer_le_le h a (hν a)
        hε₁ (by linarith) (by linarith) hL0 n)
  _ ≤ L / klBerReal ((ν a)[id] + ε₁) (μs - ε₂) + 1 / (2 * ε₁ ^ 2) + 2 / ε₂ ^ 2 := by
    -- `1 + 3 / (4 ε₂²) ≤ 2 / ε₂²` since `ε₂ < 1`
    have h1 : 1 ≤ 5 / (4 * ε₂ ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h2 : 3 / (4 * ε₂ ^ 2) + 5 / (4 * ε₂ ^ 2) = 2 / ε₂ ^ 2 := by
      field_simp
      ring
    linarith

/-- **[LS, Theorem 10.6]** For rewards in `[0, 1]`, the expected regret of the KL-UCB algorithm at
horizon `n` is at most the sum over the arms `a` with positive gap `Δ_a` of
`inf_{ε₁, ε₂ > 0, ε₁ + ε₂ < Δ_a} Δ_a (log f(n) / d(μ_a + ε₁, μ* - ε₂) + 1 / (2 ε₁²) + 2 / ε₂²)`,
where `μ_a` is the mean of `a`, `μ*` the largest mean and `f(n) = 1 + n log² n`. -/
theorem klucb_regret_le [StandardBorelSpace α]
    (h : IsAlgEnvSeq O A R klucb (stationaryEnv ν) P) (hν : ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    (n : ℕ) :
    P[regret ν A n] ≤ ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
      ⨅ ε₁ : Set.Ioo 0 (gap ν a), ⨅ ε₂ : Set.Ioo 0 (gap ν a - ε₁),
        gap ν a * (log (1 + n * log n ^ 2) /
          klBerReal ((ν a)[id] + ε₁) ((ν (bestArm ν))[id] - ε₂) +
            1 / (2 * (ε₁ : ℝ) ^ 2) + 2 / (ε₂ : ℝ) ^ 2) := by
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount h.measurable_action,
    ← sum_filter_of_ne fun a _ ha ↦ gap_nonneg.lt_of_ne' (left_ne_zero_of_mul ha)]
  refine sum_le_sum fun a ha ↦ ?_
  have : Nonempty (Set.Ioo 0 (gap ν a)) := (Set.nonempty_Ioo.mpr (mem_filter.mp ha).2).to_subtype
  refine le_ciInf fun ε₁ ↦ ?_
  have : Nonempty (Set.Ioo 0 (gap ν a - ε₁)) :=
    (Set.nonempty_Ioo.mpr (sub_pos.mpr ε₁.2.2)).to_subtype
  exact le_ciInf fun ε₂ ↦ mul_le_mul_of_nonneg_left
    (KLUCB.integral_pullCount_le h hν a ε₁.2.1 ε₂.2.1 (by linarith [ε₂.2.2]) n) gap_nonneg

/-- **Asymptotic number of pulls of KL-UCB.** For rewards in `[0, 1]`, an arm `a` with positive gap
and every `c > 1 / d(μ_a, μ*)`, where `μ_a` is the mean of `a` and `μ*` the largest mean, the
expected number of pulls of `a` by the KL-UCB algorithm during the first `n` rounds is eventually
at most `c log n`; that is, `limsup_n E[T_a(n)] / log n ≤ 1 / d(μ_a, μ*)`. Here `1 / d(μ_a, μ*)` is
`(klBer μ_a μ*).toReal⁻¹`, which is `0` when `d(μ_a, μ*) = ∞`. -/
theorem KLUCB.integral_pullCount_eventually_le (h : IsAlgEnvSeq O A R klucb (stationaryEnv ν) P)
    (hν : ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1) (a : α) (ha : 0 < gap ν a) {c : ℝ}
    (hc : (klBer (ν a)[id] (ν (bestArm ν))[id]).toReal⁻¹ < c) :
    ∀ᶠ n : ℕ in atTop, P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤ c * log n := by
  set μa := (ν a)[id]
  set μs := (ν (bestArm ν))[id]
  have hgap : gap ν a = μs - μa := gap_eq_bestArm_sub
  -- the means lie in `[0, 1]`
  have hμ (b : α) : (ν b)[id] ∈ Set.Icc 0 1 := integral_id_mem_Icc_of_ae_mem_Icc (hν b)
  have hc0 : 0 < c := (inv_nonneg.mpr ENNReal.toReal_nonneg).trans_lt hc
  -- `c⁻¹ < d(μ_a, μ*)`, also when `d(μ_a, μ*) = ∞`
  have hlt : ENNReal.ofReal c⁻¹ < klBer μa μs := by
    by_cases htop : klBer μa μs = ∞
    · simp [htop]
    have hpos : 0 < (klBer μa μs).toReal := ENNReal.toReal_pos
      (fun h0 ↦ by linarith [(klBer_eq_zero_iff (hμ a) (hμ _)).mp h0]) htop
    exact (ENNReal.ofReal_lt_iff_lt_toReal (inv_nonneg.mpr hc0.le) htop).mpr
      (inv_lt_of_inv_lt₀ hpos hc)
  -- Choose `ε ∈ (0, Δ_a / 2)` with `c⁻¹ < d(μ_a + ε, μ* - ε)`, by lower semicontinuity of `d`.
  have h_tendsto : Tendsto (fun ε : ℝ ↦ (μa + ε, μs - ε)) (𝓝[>] 0) (𝓝 (μa, μs)) := by
    have : Continuous fun ε : ℝ ↦ (μa + ε, μs - ε) := by fun_prop
    simpa using (this.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hεd, hε, hεa⟩ := (h_tendsto.eventually (lowerSemicontinuous_klBer (μa, μs) _ hlt)).and
    (Ioo_mem_nhdsGT (half_pos ha)) |>.exists
  simp only [Function.uncurry_apply_pair] at hεd
  set D := klBerReal (μa + ε) (μs - ε)
  have hp : μa + ε ∈ Set.Icc 0 1 := ⟨by linarith [(hμ a).1], by linarith [(hμ (bestArm ν)).2]⟩
  have hq : μs - ε ∈ Set.Ioo 0 1 := ⟨by linarith [(hμ a).1], by linarith [(hμ (bestArm ν)).2]⟩
  rw [klBer_eq_ofReal_klBerReal hp (Set.Ioo_subset_Icc_self hq) (klBer_ne_top hq), gt_iff_lt,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (inv_nonneg.mpr hc0.le)] at hεd
  have hDc : D⁻¹ < c := inv_lt_of_inv_lt₀ hc0 hεd
  -- The bound of `KLUCB.integral_pullCount_le` divided by `log n` tends to `D⁻¹`.
  set K := 1 / (2 * ε ^ 2) + 2 / ε ^ 2
  set L : ℕ → ℝ := fun n ↦ log (1 + n * log n ^ 2)
  have hL : Tendsto (fun n : ℕ ↦ L n / log n) atTop (𝓝 1) :=
    tendsto_log_one_add_mul_log_sq_div_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_log : Tendsto (fun n : ℕ ↦ log n) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_bound : Tendsto (fun n : ℕ ↦ (L n / D + K) / log n) atTop (𝓝 D⁻¹) := by
    have := (hL.mul_const D⁻¹).add ((tendsto_inv_atTop_zero.comp h_log).const_mul K)
    simp only [one_mul, mul_zero, add_zero] at this
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply]
    ring
  filter_upwards [eventually_lt_mul_log_of_tendsto_div_log h_bound hDc] with n hn
  refine (KLUCB.integral_pullCount_le h hν a hε hε (by linarith) n).trans ?_
  simp only [K, L] at hn
  linarith

/-- **[LS, Theorem 10.6], asymptotic part.** For rewards in `[0, 1]` and every
`c > ∑_{a : Δ_a > 0} Δ_a / d(μ_a, μ*)`, where `μ_a` is the mean of `a` and `μ*` the largest mean,
the expected regret of the KL-UCB algorithm at horizon `n` is eventually at most `c log n`; that
is, `limsup_n E[R_n] / log n ≤ ∑_{a : Δ_a > 0} Δ_a / d(μ_a, μ*)`. Here `Δ_a / d(μ_a, μ*)` is
`Δ_a / (klBer μ_a μ*).toReal`, which is `0` when `d(μ_a, μ*) = ∞`. -/
theorem klucb_regret_eventually_le [StandardBorelSpace α]
    (h : IsAlgEnvSeq O A R klucb (stationaryEnv ν) P) (hν : ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    {c : ℝ} (hc : ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
      gap ν a / (klBer (ν a)[id] (ν (bestArm ν))[id]).toReal < c) :
    ∀ᶠ n : ℕ in atTop, P[regret ν A n] ≤ c * log n :=
  integral_regret_eventually_le_of_forall_integral_pullCount_eventually_le
    h.measurable_action (.of_forall fun n ↦ log_natCast_nonneg n)
    (fun a ↦ (klBer (ν a)[id] (ν (bestArm ν))[id]).toReal⁻¹)
    (fun a ha _ hc ↦ KLUCB.integral_pullCount_eventually_le h hν a ha hc)
    (by simpa only [div_eq_mul_inv] using hc)

/-- For rewards in `[0, 1]` whose largest mean is `1`, the expected regret of the KL-UCB algorithm
is `o(log n)`: for every `c > 0`, eventually `E[R_n] ≤ c log n`. Indeed `d(μ_a, 1) = ∞` for every
arm `a` with positive gap, so that the constant of `klucb_regret_eventually_le` vanishes. -/
theorem klucb_regret_eventually_le_of_integral_bestArm_eq_one [StandardBorelSpace α]
    (h : IsAlgEnvSeq O A R klucb (stationaryEnv ν) P) (hν : ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    (h1 : (ν (bestArm ν))[id] = 1) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, P[regret ν A n] ≤ c * log n := by
  refine klucb_regret_eventually_le h hν (lt_of_eq_of_lt (sum_eq_zero fun a ha ↦ ?_) hc)
  have hμ : (ν a)[id] ∈ Set.Icc 0 1 := integral_id_mem_Icc_of_ae_mem_Icc (hν a)
  have hlt : (ν a)[id] < 1 := by
    have := (mem_filter.mp ha).2
    rw [gap_eq_bestArm_sub, h1] at this
    linarith
  rw [h1, (klBer_eq_top_iff hμ (by simp)).mpr (Or.inr ⟨rfl, hlt.ne⟩), ENNReal.toReal_top,
    div_zero]

end Regret

end LMLExplore.Bandits
