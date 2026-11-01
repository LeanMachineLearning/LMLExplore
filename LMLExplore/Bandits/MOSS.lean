/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import LeanMachineLearning.SequentialLearning.SumRewards
public import LMLExplore.Bandits.IndexAlgorithm

/-!
# The MOSS algorithm

The MOSS algorithm ("minimax optimal strategy in the stochastic case") [LS, Algorithm 7] for
σ²-sub-Gaussian rewards and a known horizon `N` (the argument `horizon`, the number of rounds
`0, …, N - 1` of the run) is the index policy whose index, for an arm `a` pulled `T_a > 0` times
with empirical mean `μ̂_a`, is `μ̂_a + √(4 σ² / T_a * log⁺ (N / (k T_a)))`, where `k` is the number
of arms and `log⁺ x = max 0 (log x)`. An arm that has not been pulled yet has index `⊤`, so that
the policy pulls every arm once before comparing finite indices.

Unlike the index of asymptotically optimal UCB, whose exploration level `log f(t)` grows with the
round, the exploration level of MOSS depends on the number of pulls of the arm, the horizon and
the number of arms, and vanishes once an arm has been pulled more than `N / k` times. This is what
removes the logarithmic factor from the minimax bound `E[R_N] ≤ 39 √(σ² k N) + ∑_a Δ_a` of
[LS, Theorem 9.1].

## Main definitions

* `LMLExplore.Bandits.mossIndex σ2 horizon n h a`: the index of arm `a` after the history `h` of
  length `n`, for the horizon `horizon`.
* `LMLExplore.Bandits.moss σ2 horizon`: the MOSS algorithm, the index policy `indexAlgorithm` with
  index `mossIndex σ2 horizon`.

## Main statements

* `mossIndex_eq_top_iff`: the index is `⊤` exactly on the arms not pulled yet.
* `mossIndex_history`: along a sequence of rounds, the index in terms of LML's `pullCount` and
  `empMean`.
* `MOSS.pullCount_card_eq_one`: `moss σ2 horizon` pulls every arm exactly once during the first
  `Fintype.card α` rounds.
* `MOSS.pullCount_eq_card_filter_of_forall_lt_index`: the pathwise step of the proof of
  [LS, Theorem 9.1]. Along a run, for arms `a`, `b` and a threshold `c`, if the index of `b` stays
  above `c` during the first `n` rounds, then every pull of `a` before round `n` is a round at
  which `a` either has not been pulled yet or has an index
  `μ̂_a + √(4 σ² / T_a * log⁺ (N / (k T_a)))` above `c`.

## Implementation notes

The proof of [LS, Theorem 9.1] takes an optimal arm `b` and the random amount
`Δ = (μ* - min_s (μ̂_{b,s} + √(4 σ² / s * log⁺ (N / (k s)))))⁺` by which the index of `b` falls
below its mean. For an arm `a` with gap `Δ_a > 2 Δ`, the index of `b` stays above
`c = μ_a + Δ_a / 2`, and `MOSS.pullCount_eq_card_filter_of_forall_lt_index` bounds the number of
pulls of `a` by the number of rounds at which `a` is played with an index above `c`. That event
depends only on `T_a` and `μ̂_a`, so `SequentialLearning/SumRewards.lean` moves it to the i.i.d.
reward stream of `a`, where [LS, Lemma 8.2] applies; the tail of `Δ` is bounded by the peeling
bound of [LS, Lemma 9.3] (`Probability/Martingale/SubGaussian.lean`).

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 9.
* J.-Y. Audibert and S. Bubeck, *Minimax policies for adversarial and stochastic bandits*,
  COLT 2009.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Learning

open scoped NNReal

namespace LMLExplore.Bandits

section Index

variable {α : Type*} [Fintype α] [DecidableEq α] {σ2 : ℝ≥0} {horizon n : ℕ}
  {h : Hist Unit α ℝ n} {a : α}

/-- The index of the MOSS algorithm [LS, Algorithm 7] for the horizon `horizon`, for the history
`h` of the first `n` rounds: `⊤` if the arm `a` has not been pulled, and otherwise
`μ̂_a + √(4 σ² / T_a * log⁺ (horizon / (k T_a)))`, where `T_a` is the number of pulls of `a`,
`μ̂_a` its empirical mean and `k = Fintype.card α` the number of arms. -/
noncomputable def mossIndex (σ2 : ℝ≥0) (horizon n : ℕ) (h : Hist Unit α ℝ n) (a : α) : EReal :=
  if pullCount' n h a = 0 then ⊤ else
    ((empMean' n h a + √(4 * σ2 / pullCount' n h a *
      log⁺ (horizon / (Fintype.card α * pullCount' n h a))) : ℝ) : EReal)

/-- The defining equation of `mossIndex`. -/
lemma mossIndex_def (σ2 : ℝ≥0) (horizon n : ℕ) (h : Hist Unit α ℝ n) (a : α) :
    mossIndex σ2 horizon n h a = if pullCount' n h a = 0 then ⊤ else
      ((empMean' n h a + √(4 * σ2 / pullCount' n h a *
        log⁺ (horizon / (Fintype.card α * pullCount' n h a))) : ℝ) : EReal) :=
  (rfl)

/-- An arm that has not been pulled has index `⊤`. -/
@[simp]
lemma mossIndex_of_pullCount'_eq_zero (h0 : pullCount' n h a = 0) :
    mossIndex σ2 horizon n h a = ⊤ := by
  simp [mossIndex_def, h0]

/-- The index of an arm that has been pulled is `μ̂_a + √(4 σ² / T_a * log⁺ (horizon / (k T_a)))`.
-/
lemma mossIndex_of_pullCount'_ne_zero (h0 : pullCount' n h a ≠ 0) :
    mossIndex σ2 horizon n h a =
      ((empMean' n h a + √(4 * σ2 / pullCount' n h a *
        log⁺ (horizon / (Fintype.card α * pullCount' n h a))) : ℝ) : EReal) := by
  simp [mossIndex_def, h0]

/-- The index of an arm is `⊤` if and only if the arm has not been pulled yet. -/
lemma mossIndex_eq_top_iff : mossIndex σ2 horizon n h a = ⊤ ↔ pullCount' n h a = 0 := by
  by_cases h0 : pullCount' n h a = 0
  · simp [h0]
  · simp [mossIndex_of_pullCount'_ne_zero h0, h0]

@[fun_prop]
lemma measurable_mossIndex [MeasurableSpace α] [MeasurableSingletonClass α]
    (σ2 : ℝ≥0) (horizon n : ℕ) : Measurable (mossIndex (α := α) σ2 horizon n) := by
  refine Measurable.of_eval fun a ↦ ?_
  simp_rw [mossIndex_def]
  refine Measurable.ite ?_ measurable_const (by fun_prop)
  exact (measurableSet_singleton 0).preimage (measurable_pullCount' n a)

/-- Along a sequence of rounds `(O, A, R)`, the index of an arm at round `n` is `⊤` if the arm has
not been pulled before `n`, and otherwise `μ̂_a + √(4 σ² / T_a * log⁺ (horizon / (k T_a)))` for
the number of pulls `T_a = pullCount A a n ω` and the empirical mean
`μ̂_a = empMean A R a n ω`. -/
lemma mossIndex_history {Ω : Type*} (O : ℕ → Ω → Unit) (A : ℕ → Ω → α) (R : ℕ → Ω → ℝ)
    (σ2 : ℝ≥0) (horizon n : ℕ) (ω : Ω) (a : α) :
    mossIndex σ2 horizon n (history O A R n ω) a = if pullCount A a n ω = 0 then ⊤ else
      ((empMean A R a n ω + √(4 * σ2 / pullCount A a n ω *
        log⁺ (horizon / (Fintype.card α * pullCount A a n ω))) : ℝ) : EReal) := by
  rw [mossIndex_def, ← pullCount_eq_pullCount', ← empMean_eq_empMean']

/-- The index of an arm exceeds a real threshold `c` if and only if the arm has not been pulled
yet or `c < μ̂_a + √(4 σ² / T_a * log⁺ (horizon / (k T_a)))`. -/
lemma coe_lt_mossIndex_iff {c : ℝ} :
    (c : EReal) < mossIndex σ2 horizon n h a ↔ pullCount' n h a = 0 ∨
      c < empMean' n h a + √(4 * σ2 / pullCount' n h a *
        log⁺ (horizon / (Fintype.card α * pullCount' n h a))) := by
  by_cases h0 : pullCount' n h a = 0
  · simp [h0]
  · rw [mossIndex_of_pullCount'_ne_zero h0, EReal.coe_lt_coe_iff]
    simp [h0]

end Index

section Algorithm

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- The MOSS algorithm [LS, Algorithm 7] for σ²-sub-Gaussian rewards and the horizon `horizon`:
the index policy with index `mossIndex σ2 horizon`, which plays at round `n` an arm of maximal
index, ties being broken by LML's `argmax`. -/
noncomputable def moss (σ2 : ℝ≥0) (horizon : ℕ) : Algorithm Unit α ℝ :=
  indexAlgorithm (fun n x ↦ mossIndex σ2 horizon n x.1)
    fun n ↦ (measurable_mossIndex σ2 horizon n).comp measurable_fst

/-- The MOSS algorithm is the index policy with index `mossIndex σ2 horizon`. -/
lemma moss_def (σ2 : ℝ≥0) (horizon : ℕ) :
    moss (α := α) σ2 horizon =
      indexAlgorithm (fun n x ↦ mossIndex σ2 horizon n x.1)
        fun n ↦ (measurable_mossIndex σ2 horizon n).comp measurable_fst :=
  (rfl)

namespace MOSS

variable {σ2 : ℝ≥0} {horizon : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {env : Environment Unit α ℝ} {P : Measure Ω} [IsFiniteMeasure P] {O : ℕ → Ω → Unit}
  {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- The MOSS algorithm pulls every arm exactly once during the first `Fintype.card α` rounds. -/
lemma pullCount_card_eq_one (h : IsAlgEnvSeq O A R (moss σ2 horizon) env P) :
    ∀ᵐ ω ∂P, ∀ a, pullCount A a (Fintype.card α) ω = 1 := by
  rw [moss_def] at h
  exact IndexAlgorithm.pullCount_card_eq_one h fun _ _ _ ↦ mossIndex_eq_top_iff

/-- The pathwise step of the proof of [LS, Theorem 9.1]. Along a run of the MOSS algorithm, for
arms `a`, `b` (typically an optimal arm) and a threshold `c`, if at every round `t < n` at which
`b` has been pulled its index `μ̂_b + √(4 σ² / T_b * log⁺ (horizon / (k T_b)))` exceeds `c`, then
the number of pulls of `a` before round `n` is the number of rounds `t < n` at which `a` is played
while either it has not been pulled yet or `c < μ̂_a + √(4 σ² / T_a * log⁺ (horizon / (k T_a)))`.
The latter event only depends on `T_a` and `μ̂_a`. -/
theorem pullCount_eq_card_filter_of_forall_lt_index
    (h : IsAlgEnvSeq O A R (moss σ2 horizon) env P) (a b : α) (c : ℝ) :
    ∀ᵐ ω ∂P, ∀ n, (∀ t < n, pullCount A b t ω ≠ 0 →
        c < empMean A R b t ω + √(4 * σ2 / pullCount A b t ω *
          log⁺ (horizon / (Fintype.card α * pullCount A b t ω)))) →
      pullCount A a n ω = #{t ∈ range n | A t ω = a ∧ (pullCount A a t ω = 0 ∨
        c < empMean A R a t ω + √(4 * σ2 / pullCount A a t ω *
          log⁺ (horizon / (Fintype.card α * pullCount A a t ω))))} := by
  rw [moss_def] at h
  filter_upwards [IndexAlgorithm.pullCount_eq_card_filter_of_forall_lt_index h a b c]
    with ω hω n hb
  simp_rw [coe_lt_mossIndex_iff, ← pullCount_eq_pullCount', ← empMean_eq_empMean'] at hω
  exact hω n fun t ht ↦ or_iff_not_imp_left.mpr (hb t ht)

end MOSS

end Algorithm

end LMLExplore.Bandits
