/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import LeanMachineLearning.Online.Bandit.Regret
public import LeanMachineLearning.SequentialLearning.SumRewards
public import LMLExplore.Bandits.Concentration
public import LMLExplore.Bandits.IndexAlgorithm
public import LMLExplore.MeasureTheory.Integral.Bochner.Set
public import LMLExplore.MeasureTheory.Integral.Layercake
public import LMLExplore.Probability.Martingale.SubGaussian

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
* `MOSS.mul_sum_measureReal_streamMeasure_le`, `MOSS.mul_sum_measureReal_action_eq_le`: for an arm
  with mean `μ_a` and `Δ > 8 √(σ² k / N)`, `Δ` times the expected number of rounds at which the
  arm is played with an index above `μ_a + Δ / 2` is at most `Δ + 15 √(σ² N / k)`, in the reward
  stream model and in a run of any algorithm.
* `MOSS.measure_exists_empMean_add_sqrt_add_lt_le`: in a run of any algorithm, the index of an arm
  falls below its mean minus `x > 0` at some round before the horizon with probability at most
  `12 σ² k / (N x²)`.
* `MOSS.regret_le_of_forall_sub_le_index`: the pathwise regret decomposition of the proof of
  [LS, Theorem 9.1].
* `moss_regret_le`: **[LS, Theorem 9.1]** for σ²-sub-Gaussian rewards, the expected regret of MOSS
  at the horizon `N` is at most `39 √(σ² k N) + ∑_a Δ_a`.

## Implementation notes

The proof of [LS, Theorem 9.1] takes an optimal arm `b` and the random amount `D ≥ 0` by which the
index of `b` falls below its mean `μ*` before the horizon. By the peeling bound of [LS, Lemma 9.3]
(`Probability/Martingale/SubGaussian.lean`, with the constant `12` instead of the book's `15`),
`P(x < D) ≤ 12 σ² k / (N x²)`, so `E[D] ≤ 2 √(12 σ² k / N)` by the layer cake formula
(`MeasureTheory.lintegral_ofReal_le_two_mul_sqrt_of_measure_lt_le`). The arms with gap
`Δ_a ≤ 2 D + θ`, for `θ = 8 √(σ² k / N)`, contribute at most `N (2 D + θ)` to the regret. For an
arm with a larger gap, the index of `b` stays above `μ_a + Δ_a / 2`, and
`MOSS.pullCount_eq_card_filter_of_forall_lt_index` bounds the number of pulls of `a` by the number
of rounds at which `a` is played with an index above `μ_a + Δ_a / 2`. That event depends only on
`T_a` and `μ̂_a`, so `SequentialLearning/SumRewards.lean` moves it to the i.i.d. reward stream of
`a`, where [LS, Lemma 8.2] applies to the sample sizes `s ≥ σ² / Δ_a²` (the book's `1 / Δ_a²` for
`σ² = 1`). Altogether `E[R_N] ≤ (8 √3 + 8 + 15) √(σ² k N) + ∑_a Δ_a`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 9.
* J.-Y. Audibert and S. Bubeck, *Minimax policies for adversarial and stochastic bandits*,
  COLT 2009.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Learning Bandits

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

section Regret

/-- The numerical inequality of the proof of [LS, Theorem 9.1]: for `u ≥ 8`,
`9 + 32 log u + 16 √(π log u) ≤ 15 u`. Its value at `u = 8` is about `14.6 * 8`. -/
private lemma nine_add_mul_log_add_mul_sqrt_le {u : ℝ} (hu : 8 ≤ u) :
    9 + 32 * log u + 16 * √(π * log u) ≤ 15 * u := by
  have hl2 := log_two_lt_d9
  have hpi := pi_lt_d2
  have h8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]
    norm_num
  -- write `u = 8 z` with `z ≥ 1`, and use `log z ≤ z - 1`
  set z := u / 8 with hz_def
  have hz : 1 ≤ z := by rw [hz_def, le_div_iff₀ (by norm_num)]; linarith
  have hu_eq : u = 8 * z := by rw [hz_def]; ring
  have hlogu : log u = log 8 + log z := by
    rw [hu_eq, log_mul (by norm_num) (by linarith)]
  have hlogz : log z ≤ z - 1 := log_le_sub_one_of_pos (by linarith)
  have hlog0 : 0 ≤ log u := log_nonneg (by linarith)
  have hlog_le : log u ≤ 1.08 + z := by linarith
  have h_sqrt : √(π * log u) ≤ 2.6 * z := by
    rw [sqrt_le_left (by linarith)]
    have : π * log u ≤ 3.15 * (1.08 + z) :=
      mul_le_mul hpi.le hlog_le hlog0 (by norm_num)
    nlinarith
  linarith

/-- The numerical step of the bound on the overestimation of the MOSS index: for
`Δ > 8 √(σ² k / N)` and `L = log⁺ (N Δ² / (k σ²))`,
`σ² / Δ * (9 + 16 L + 8 √(2 π L)) ≤ 15 √(σ² N / k)`. With `u = Δ / √(σ² k / N) > 8`, this is
`nine_add_mul_log_add_mul_sqrt_le`. -/
private lemma div_mul_nine_add_le (σ2 : ℝ≥0) {k N Δ : ℝ} (hk : 0 < k) (hN : 0 < N)
    (hΔ : 8 * √(σ2 * k / N) < Δ) :
    σ2 / Δ * (9 + 16 * log⁺ (N * Δ ^ 2 / (k * σ2)) +
      8 * √(π * (2 * log⁺ (N * Δ ^ 2 / (k * σ2))))) ≤ 15 * √(σ2 * N / k) := by
  set L := log⁺ (N * Δ ^ 2 / (k * σ2)) with hL_def
  rcases eq_or_ne (σ2 : ℝ) 0 with h0 | h0
  · simp [h0]
  have hσ : (0 : ℝ) < σ2 := lt_of_le_of_ne σ2.2 (Ne.symm h0)
  set r := √(σ2 * k / N) with hr_def
  have hr : 0 < r := sqrt_pos.mpr (by positivity)
  have hr2 : r ^ 2 = σ2 * k / N := sq_sqrt (by positivity)
  set u := Δ / r with hu_def
  have hΔu : Δ = u * r := by rw [hu_def]; field_simp
  have hu : 8 ≤ u := by rw [hu_def, le_div_iff₀ hr]; linarith
  have hL : L = 2 * log u := by
    have : N * Δ ^ 2 / (k * σ2) = u ^ 2 := by
      rw [hΔu, mul_pow, hr2]
      field_simp
    rw [hL_def, this, posLog_eq_log (by rw [abs_of_nonneg (by positivity)]; nlinarith), log_pow]
    push_cast
    ring
  have h_sqrt : √(π * (2 * L)) = 2 * √(π * log u) := by
    rw [hL, show π * (2 * (2 * log u)) = 2 ^ 2 * (π * log u) by ring, sqrt_mul (by positivity),
      sqrt_sq (by norm_num)]
  have h_rhs : √(σ2 * N / k) = σ2 / r := by
    rw [sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    field_simp
    rw [hr2]
    field_simp
  rw [h_sqrt, hL, h_rhs, hΔu]
  have := nine_add_mul_log_add_mul_sqrt_le hu
  calc σ2 / (u * r) * (9 + 16 * (2 * log u) + 8 * (2 * √(π * log u)))
  _ = σ2 / (u * r) * (9 + 32 * log u + 16 * √(π * log u)) := by ring
  _ ≤ σ2 / (u * r) * (15 * u) := by gcongr
  _ = 15 * (σ2 / r) := by field_simp

variable {α : Type*} [Fintype α] [MeasurableSpace α] {ν : Kernel α ℝ} [IsMarkovKernel ν]
  {σ2 : ℝ≥0} {a : α}

/-- **Overestimation of the MOSS index in the stream model.** If arm `a` is σ²-sub-Gaussian with
mean `μ_a`, `N` is a horizon, `k` the number of arms and `Δ > 8 √(σ² k / N)`, then `Δ` times the
expected number of sample sizes `s < N` at which the MOSS index
`μ̂_s + √(4 σ² / s * log⁺ (N / (k s)))` of the first `s` rewards of `a` in the i.i.d. reward stream
model exceeds `μ_a + Δ / 2` is at most `Δ + 15 √(σ² N / k)`. The event of `s = 0` is the sure
event, matching the infinite index of an unpulled arm. -/
theorem MOSS.mul_sum_measureReal_streamMeasure_le
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (horizon : ℕ) {Δ : ℝ}
    (hΔ : 8 * √(σ2 * Fintype.card α / horizon) < Δ) :
    Δ * ∑ s ∈ range horizon, (streamMeasure ν).real {ω | s = 0 ∨
        (ν a)[id] + Δ / 2 < (∑ i ∈ range s, ω i a) / s +
          √(4 * σ2 / s * log⁺ (horizon / (Fintype.card α * s)))} ≤
      Δ + 15 * √(σ2 * horizon / Fintype.card α) := by
  have hΔ0 : 0 < Δ := (by positivity : (0 : ℝ) ≤ 8 * √(σ2 * Fintype.card α / horizon)).trans_lt hΔ
  rcases Nat.eq_zero_or_pos horizon with rfl | hN
  · simp only [range_zero, sum_empty, mul_zero]
    positivity
  have hk : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨a⟩)
  have hN' : (0 : ℝ) < horizon := Nat.cast_pos.mpr hN
  set k : ℝ := (Fintype.card α : ℝ) with hk_def
  set N : ℝ := (horizon : ℝ) with hN_def
  set μ := (ν a)[id]
  -- the exploration level of the sample sizes `s ≥ σ² / Δ²`
  set L := log⁺ (N * Δ ^ 2 / (k * σ2)) with hL_def
  have hL0 : 0 ≤ L := posLog_nonneg
  -- the sample sizes `1 ≤ s < σ² / Δ²` are at most `σ² / Δ²` in number, and for the other ones
  -- the event is contained in the event of [LS, Lemma 8.2] with the level `2 L`
  have h_split : ∀ s ∈ range horizon, (streamMeasure ν).real {ω | s = 0 ∨
        μ + Δ / 2 < (∑ i ∈ range s, ω i a) / s + √(4 * σ2 / s * log⁺ (N / (k * s)))} ≤
      (if 1 ≤ s ∧ (s : ℝ) * Δ ^ 2 < σ2 then 1 else 0) + (streamMeasure ν).real
        {ω | s * (μ + Δ / 2) ≤ ∑ i ∈ range s, ω i a + √(2 * σ2 * (2 * L) * s)} := by
    intro s _
    split_ifs with hs
    · exact measureReal_le_one.trans (le_add_of_nonneg_right measureReal_nonneg)
    rw [zero_add]
    refine measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · simp
    replace hω := hω.resolve_left hs0.ne'
    have hs' : (0 : ℝ) < s := Nat.cast_pos.mpr hs0
    have hσΔ : (σ2 : ℝ) ≤ s * Δ ^ 2 := not_lt.mp fun h ↦ hs ⟨hs0, h⟩
    -- `s * √(4 σ² / s * log⁺ (N / (k s))) = √(4 σ² log⁺ (N / (k s)) s) ≤ √(2 σ² (2 L) s)`
    have h_level : 4 * σ2 * log⁺ (N / (k * s)) * s ≤ 2 * σ2 * (2 * L) * s := by
      rcases eq_or_ne (σ2 : ℝ) 0 with h0 | h0
      · simp [h0]
      have hσ : (0 : ℝ) < σ2 := lt_of_le_of_ne σ2.2 (Ne.symm h0)
      have h_le : N / (k * s) ≤ N * Δ ^ 2 / (k * σ2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_left hσΔ (by positivity : (0 : ℝ) ≤ N * k)
        nlinarith
      have h_log := posLog_le_posLog (by linarith [show 0 ≤ N / (k * s) by positivity]) h_le
      rw [← hL_def] at h_log
      nlinarith [mul_le_mul_of_nonneg_left h_log (by positivity : (0 : ℝ) ≤ 4 * σ2 * s)]
    have h_sqrt : s * √(4 * σ2 / s * log⁺ (N / (k * s))) ≤ √(2 * σ2 * (2 * L) * s) := by
      rw [div_mul_eq_mul_div, mul_sqrt_div_eq_sqrt_mul _ hs'.le]
      exact sqrt_le_sqrt h_level
    rw [div_add' _ _ _ hs'.ne', lt_div_iff₀ hs'] at hω
    nlinarith
  -- the number of sample sizes `1 ≤ s < σ² / Δ²`
  have h_card : ∑ s ∈ range horizon, (if 1 ≤ s ∧ (s : ℝ) * Δ ^ 2 < σ2 then (1 : ℝ) else 0) ≤
      σ2 / Δ ^ 2 := by
    rw [sum_boole]
    have h_sub : (range horizon).filter (fun s : ℕ ↦ 1 ≤ s ∧ (s : ℝ) * Δ ^ 2 < σ2) ⊆
        Icc 1 ⌊(σ2 : ℝ) / Δ ^ 2⌋₊ := by
      intro s hs
      simp only [mem_filter] at hs
      refine mem_Icc.mpr ⟨hs.2.1, Nat.le_floor ?_⟩
      rw [le_div_iff₀ (by positivity)]
      exact hs.2.2.le
    calc (#((range horizon).filter (fun s : ℕ ↦ 1 ≤ s ∧ (s : ℝ) * Δ ^ 2 < σ2)) : ℝ)
    _ ≤ #(Icc 1 ⌊(σ2 : ℝ) / Δ ^ 2⌋₊) := by exact_mod_cast card_le_card h_sub
    _ = ⌊(σ2 : ℝ) / Δ ^ 2⌋₊ := by simp
    _ ≤ σ2 / Δ ^ 2 := Nat.floor_le (by positivity)
  have h82 := sum_measureReal_streamMeasure_mul_le_sum_add_sqrt_le hν (half_pos hΔ0)
    (by positivity : 0 ≤ 2 * L) horizon
  have h_num := div_mul_nine_add_le σ2 hk hN' hΔ
  calc Δ * ∑ s ∈ range horizon, (streamMeasure ν).real {ω | s = 0 ∨
        μ + Δ / 2 < (∑ i ∈ range s, ω i a) / s + √(4 * σ2 / s * log⁺ (N / (k * s)))}
  _ ≤ Δ * (σ2 / Δ ^ 2 + (1 + 2 * σ2 / (Δ / 2) ^ 2 * (2 * L + √(π * (2 * L)) + 1))) := by
    gcongr
    refine (sum_le_sum h_split).trans ?_
    rw [sum_add_distrib]
    exact add_le_add h_card h82
  _ = Δ + σ2 / Δ * (9 + 16 * L + 8 * √(π * (2 * L))) := by
    field_simp
    ring
  _ ≤ Δ + 15 * √(σ2 * N / k) := by linarith

variable [DecidableEq α] [MeasurableSingletonClass α] {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ} {O : ℕ → Ω → Unit}
  {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- **Overestimation of the MOSS index in a run.** In a run of any algorithm against the
stochastic bandit `stationaryEnv ν`, if arm `a` is σ²-sub-Gaussian with mean `μ_a`, `N` is a
horizon, `k` the number of arms and `Δ > 8 √(σ² k / N)`, then `Δ` times the expected number of
rounds `t < N` at which `a` is played while either it has not been pulled yet or its MOSS index
`μ̂_a + √(4 σ² / T_a * log⁺ (N / (k T_a)))` exceeds `μ_a + Δ / 2` is at most
`Δ + 15 √(σ² N / k)`. This bounds the contribution of an arm with gap `Δ` in the proof of
[LS, Theorem 9.1]. -/
theorem MOSS.mul_sum_measureReal_action_eq_le
    (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P) (a : α)
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (horizon : ℕ) {Δ : ℝ}
    (hΔ : 8 * √(σ2 * Fintype.card α / horizon) < Δ) :
    Δ * ∑ t ∈ range horizon, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨
        (ν a)[id] + Δ / 2 < empMean A R a t ω + √(4 * σ2 / pullCount A a t ω *
          log⁺ (horizon / (Fintype.card α * pullCount A a t ω))))} ≤
      Δ + 15 * √(σ2 * horizon / Fintype.card α) := by
  have hΔ0 : 0 < Δ := (by positivity : (0 : ℝ) ≤ 8 * √(σ2 * Fintype.card α / horizon)).trans_lt hΔ
  set p : ℕ → ℝ → Prop := fun s x ↦ s = 0 ∨ (ν a)[id] + Δ / 2 < x / s +
    √(4 * σ2 / s * log⁺ (horizon / (Fintype.card α * s))) with hp_def
  have hp : Measurable fun q : ℕ × ℝ ↦ p q.1 q.2 :=
    (measurableSet_setOfPred.mp ((measurableSet_singleton 0).preimage measurable_fst)).or
      (measurableSet_setOfPred.mp (measurableSet_lt measurable_const (by fun_prop)))
  -- the events are transferred to the reward stream
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hΔ0.le)
    (MOSS.mul_sum_measureReal_streamMeasure_le hν horizon hΔ)
  exact sum_measureReal_action_eq_and_pullCount_sumRewards_le h a horizon hp

/-- **Underestimation of the MOSS index of an arm in a run.** In a run of any algorithm against
the stochastic bandit `stationaryEnv ν`, if arm `b` is σ²-sub-Gaussian with mean `μ_b`, `N` is a
horizon and `k` the number of arms, then for `x > 0` the probability that at some round `t < N`
the arm `b` has been pulled and its MOSS index `μ̂_b + √(4 σ² / T_b * log⁺ (N / (k T_b)))` is
below `μ_b - x` is at most `12 σ² k / (N x²)`. This is the peeling bound of [LS, Lemma 9.3],
transferred from the reward stream to the run. -/
theorem MOSS.measure_exists_empMean_add_sqrt_add_lt_le
    (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P) (b : α)
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν b)[id]) σ2 (ν b)) (horizon : ℕ) {x : ℝ} (hx : 0 < x) :
    P {ω | ∃ t < horizon, pullCount A b t ω ≠ 0 ∧ empMean A R b t ω +
        √(4 * σ2 / pullCount A b t ω * log⁺ (horizon / (Fintype.card α * pullCount A b t ω))) +
          x < (ν b)[id]} ≤
      ENNReal.ofReal (12 * σ2 * Fintype.card α / (horizon * x ^ 2)) := by
  rcases Nat.eq_zero_or_pos horizon with rfl | hN
  · simp
  have hk : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨b⟩)
  have hN' : (0 : ℝ) < horizon := Nat.cast_pos.mpr hN
  set μ := (ν b)[id]
  calc P {ω | ∃ t < horizon, pullCount A b t ω ≠ 0 ∧ empMean A R b t ω +
        √(4 * σ2 / pullCount A b t ω * log⁺ (horizon / (Fintype.card α * pullCount A b t ω))) +
          x < μ}
  _ ≤ streamMeasure ν {ω | ∃ s < horizon, s ≠ 0 ∧ (∑ i ∈ range s, ω i b) / s +
        √(4 * σ2 / s * log⁺ (horizon / (Fintype.card α * s))) + x < μ} :=
    measure_exists_lt_pullCount_sumRewards_le h b horizon fun s y ↦ s ≠ 0 ∧ y / s +
      √(4 * σ2 / s * log⁺ (horizon / (Fintype.card α * s))) + x < μ
  _ ≤ streamMeasure ν {ω | ∃ s : ℕ, 0 < s ∧ (∑ i ∈ range s, (ω i b - μ)) / s +
        √(4 * σ2 / s * log⁺ (1 / (s * (Fintype.card α / horizon)))) + x ≤ 0} := by
    refine measure_mono fun ω ⟨s, _, hs0, hs⟩ ↦ ⟨s, Nat.pos_of_ne_zero hs0, ?_⟩
    have hs' : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs0
    have h_mean : (∑ i ∈ range s, (ω i b - μ)) / s = (∑ i ∈ range s, ω i b) / s - μ := by
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      field_simp
    have h_level : 1 / (s * (Fintype.card α / horizon : ℝ)) = horizon / (Fintype.card α * s) := by
      field_simp
    rw [h_mean, h_level]
    linarith
  _ ≤ ENNReal.ofReal (12 * σ2 * (Fintype.card α / horizon) / x ^ 2) :=
    measure_exists_sum_div_add_sqrt_add_le_zero_le_of_iIndepFun
      (iIndepFun_streamMeasure_sub_mean ν b) (hasSubgaussianMGF_streamMeasure_sub_mean hν)
      (by positivity) hx
  _ = ENNReal.ofReal (12 * σ2 * Fintype.card α / (horizon * x ^ 2)) := by
    congr 1
    field_simp

/-- **Expected drop of the MOSS index of an arm.** In a run of any algorithm against the stochastic
bandit `stationaryEnv ν`, if arm `b` is σ²-sub-Gaussian with mean `μ_b`, there is a nonnegative
integrable random variable `D` with `E[D] ≤ 2 √(12 σ² k / n)` such that the MOSS index of `b` for
the horizon `n` is at least `μ_b - D` at every round `t < n` at which `b` has been pulled. -/
private lemma MOSS.exists_integral_le_and_sub_le_index
    (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P) (b : α)
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν b)[id]) σ2 (ν b)) (n : ℕ) :
    ∃ D : Ω → ℝ, (∀ ω, 0 ≤ D ω) ∧ Integrable D P ∧
      P[D] ≤ 2 * √(12 * σ2 * Fintype.card α / n) ∧
      ∀ ω, ∀ t < n, pullCount A b t ω ≠ 0 → (ν b)[id] - D ω ≤ empMean A R b t ω +
        √(4 * σ2 / pullCount A b t ω * log⁺ (n / (Fintype.card α * pullCount A b t ω))) := by
  have hA := h.measurable_action
  have hR := h.measurable_feedback
  set k : ℝ := (Fintype.card α : ℝ)
  set w : ℕ → ℝ := fun s ↦ √(4 * σ2 / s * log⁺ (n / (k * s)))
  -- `D` is the largest amount by which the index of `b` falls below `μ_b` before round `n`
  set F : ℕ → Ω → ℝ≥0 := fun t ω ↦ if pullCount A b t ω = 0 then 0 else
    ((ν b)[id] - (empMean A R b t ω + w (pullCount A b t ω))).toNNReal with hF_def
  set D : Ω → ℝ≥0 := (range n).sup F
  have hD_apply (ω : Ω) : D ω = (range n).sup fun t ↦ F t ω := Finset.sup_apply _ _ _
  have hD_meas : Measurable D :=
    Finset.sup_induction (p := Measurable) measurable_const (fun _ hf _ hg ↦ hf.sup hg)
      fun t _ ↦ Measurable.ite ((measurableSet_singleton 0).preimage
        (measurable_pullCount hA b t)) measurable_const (by fun_prop)
  -- [LS, Lemma 9.3] bounds the tail of `D`, hence its expectation
  have hD_tail (x : ℝ) (hx : 0 < x) :
      P {ω | x < D ω} ≤ ENNReal.ofReal (12 * σ2 * k / n / x ^ 2) := by
    refine le_trans (measure_mono fun ω (hω : x < D ω) ↦ ?_)
      ((MOSS.measure_exists_empMean_add_sqrt_add_lt_le h b hν n hx).trans_eq (by rw [div_div]))
    rw [← toNNReal_lt_iff_lt_coe hx.le, hD_apply, Finset.lt_sup_iff] at hω
    obtain ⟨t, ht, hlt⟩ := hω
    by_cases h0 : pullCount A b t ω = 0
    · simp [hF_def, h0] at hlt
    simp only [hF_def, h0, ↓reduceIte, toNNReal_lt_toNNReal_iff'] at hlt
    exact ⟨t, mem_range.mp ht, h0, by linarith [hlt.1]⟩
  have hD_lint := lintegral_ofReal_le_two_mul_sqrt_of_measure_lt_le
    hD_meas.coe_nnreal_real.aemeasurable (by positivity) hD_tail
  refine ⟨fun ω ↦ D ω, fun ω ↦ (D ω).coe_nonneg,
    ⟨hD_meas.coe_nnreal_real.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω ↦ (D ω).coe_nonneg)).mpr
        (hD_lint.trans_lt ENNReal.ofReal_lt_top)⟩, ?_, fun ω t ht h0 ↦ ?_⟩
  · beta_reduce
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω ↦ (D ω).coe_nonneg)
      hD_meas.coe_nnreal_real.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hD_lint
  · -- the index of `b` at round `t` is at least `μ_b - D`
    have h_le := Finset.le_sup (f := fun t ↦ F t ω) (mem_range.mpr ht)
    simp only [hF_def, h0, ↓reduceIte] at h_le
    have := (Real.le_coe_toNNReal _).trans (NNReal.coe_le_coe.mpr (h_le.trans_eq (hD_apply ω).symm))
    linarith

omit [IsMarkovKernel ν] in
/-- **Pathwise regret decomposition of [LS, Theorem 9.1].** Along a run of the MOSS algorithm for
the horizon `n`, let `d ≥ 0` be such that, at every round `t < n` at which an optimal arm has been
pulled, its index is at least `μ* - d`. Then for every `θ ≥ 0` the regret at the horizon is at most
`n (2 d + θ)` plus the sum over the arms `a` with gap `Δ_a > θ` of `Δ_a` times the number of rounds
`t < n` at which `a` is played while it has not been pulled yet or its index
`μ̂_a + √(4 σ² / T_a * log⁺ (n / (k T_a)))` exceeds `μ_a + Δ_a / 2`. -/
theorem MOSS.regret_le_of_forall_sub_le_index [Nonempty α] {env : Environment Unit α ℝ} {n : ℕ}
    (h : IsAlgEnvSeq O A R (moss σ2 n) env P) :
    ∀ᵐ ω ∂P, ∀ d θ : ℝ, 0 ≤ d → 0 ≤ θ → (∀ t < n, pullCount A (bestArm ν) t ω ≠ 0 →
        (ν (bestArm ν))[id] - d ≤ empMean A R (bestArm ν) t ω +
          √(4 * σ2 / pullCount A (bestArm ν) t ω *
            log⁺ (n / (Fintype.card α * pullCount A (bestArm ν) t ω)))) →
      regret ν A n ω ≤ n * (2 * d + θ) + ∑ a ∈ univ.filter (fun a ↦ θ < gap ν a),
        gap ν a * #{t ∈ range n | A t ω = a ∧ (pullCount A a t ω = 0 ∨
          (ν a)[id] + gap ν a / 2 < empMean A R a t ω + √(4 * σ2 / pullCount A a t ω *
            log⁺ (n / (Fintype.card α * pullCount A a t ω))))} := by
  have h_ae := ae_all_iff.mpr fun a ↦
    MOSS.pullCount_eq_card_filter_of_forall_lt_index h a (bestArm ν) ((ν a)[id] + gap ν a / 2)
  filter_upwards [h_ae] with ω hω d θ hd hθ hb
  have hn : ∑ a, (pullCount A a n ω : ℝ) = n := by
    exact_mod_cast sum_pullCount (A := A) (t := n) (ω := ω)
  rw [regret_eq_sum_pullCount_mul_gap, sum_filter,
    show (n : ℝ) * (2 * d + θ) = ∑ a, (pullCount A a n ω : ℝ) * (2 * d + θ) by rw [← sum_mul, hn],
    ← sum_add_distrib]
  refine sum_le_sum fun a _ ↦ ?_
  have hT : (0 : ℝ) ≤ pullCount A a n ω := Nat.cast_nonneg _
  by_cases hlt : 2 * d + θ < gap ν a
  · -- the index of the optimal arm stays above `μ_a + Δ_a / 2`, so `a` is pulled only at the
    -- counted rounds
    have hgap : gap ν a = (ν (bestArm ν))[id] - (ν a)[id] := gap_eq_bestArm_sub
    simp only [show θ < gap ν a by linarith, ↓reduceIte]
    rw [← hω a n fun t ht h0 ↦ by linarith [hb t ht h0]]
    nlinarith
  · have := mul_le_mul_of_nonneg_left (not_lt.mp hlt) hT
    split_ifs
    · nlinarith [mul_nonneg (gap_nonneg (ν := ν) (a := a)) hT]
    · linarith

/-- The final numerical step of the proof of [LS, Theorem 9.1]: the contribution
`N (2 (2 √(12 σ² k / N)) + 8 √(σ² k / N))` of the optimal arm and the contribution
`k (15 √(σ² N / k))` of the arms with large gaps add up to at most `39 √(σ² k N)`, since
`4 √12 + 8 + 15 ≤ 39`. -/
private lemma mul_add_mul_sqrt_le_mul_sqrt (σ2 : ℝ≥0) {k N : ℝ} (hk : 0 < k)
    (hN : 0 < N) :
    N * (2 * (2 * √(12 * σ2 * k / N)) + 8 * √(σ2 * k / N)) + k * (15 * √(σ2 * N / k)) ≤
      39 * √(σ2 * k * N) := by
  -- the square roots in terms of `q = √(σ² k N)`
  set q := √(σ2 * k * N) with hq_def
  have hq1 : √(σ2 * k / N) = q / N := by
    rw [hq_def, show σ2 * k / N = σ2 * k * N / N ^ 2 by field_simp, sqrt_div' _ (by positivity),
      sqrt_sq hN.le]
  have hq2 : √(12 * σ2 * k / N) = √12 * (q / N) := by
    rw [show 12 * σ2 * k / N = 12 * (σ2 * k / N) by ring, sqrt_mul (by norm_num), hq1]
  have hq3 : √(σ2 * N / k) = q / k := by
    rw [hq_def, show σ2 * N / k = σ2 * k * N / k ^ 2 by field_simp, sqrt_div' _ (by positivity),
      sqrt_sq hk.le]
  have h12 : √12 ≤ 4 := by
    rw [sqrt_le_left (by norm_num)]
    norm_num
  calc N * (2 * (2 * √(12 * σ2 * k / N)) + 8 * √(σ2 * k / N)) + k * (15 * √(σ2 * N / k))
  _ = (4 * √12 + 8) * q + 15 * q := by
    rw [hq1, hq2, hq3]
    field_simp
    ring
  _ ≤ 39 * q := by nlinarith [sqrt_nonneg (σ2 * k * N)]

/-- **[LS, Theorem 9.1]** For σ²-sub-Gaussian rewards, the expected regret of the MOSS algorithm
for the horizon `n` is at most `39 √(σ² k n) + ∑_a Δ_a` at that horizon, where `k` is the number of
arms. -/
theorem moss_regret_le [Nonempty α] (n : ℕ)
    (h : IsAlgEnvSeq O A R (moss σ2 n) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) :
    P[regret ν A n] ≤ 39 * √(σ2 * Fintype.card α * n) + ∑ a, gap ν a := by
  have h_gap_sum : 0 ≤ ∑ a, gap ν a := sum_nonneg fun _ _ ↦ gap_nonneg
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [regret_eq_sum_gap] using h_gap_sum
  have hA := h.measurable_action
  have hR := h.measurable_feedback
  have hk : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hN : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set k : ℝ := (Fintype.card α : ℝ)
  set N : ℝ := (n : ℝ)
  set w : ℕ → ℝ := fun s ↦ √(4 * σ2 / s * log⁺ (n / (k * s)))
  set θ := 8 * √(σ2 * k / N) with hθ_def
  have hθ0 : 0 ≤ θ := by positivity
  -- `D` bounds the drop of the index of an optimal arm below `μ*`
  obtain ⟨D, hD0, hD_int, hD_exp, hD⟩ :=
    MOSS.exists_integral_le_and_sub_le_index h (bestArm ν) (hν _) n
  -- `κ a` counts the rounds at which `a` is played with an index above `μ_a + Δ_a / 2`
  set E : α → ℕ → Set Ω := fun a t ↦ {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨
    (ν a)[id] + gap ν a / 2 < empMean A R a t ω + w (pullCount A a t ω))}
  have hE_meas (a : α) (t : ℕ) : MeasurableSet (E a t) :=
    measurableSet_setOfPred.mpr
      ((measurableSet_setOfPred.mp ((measurableSet_singleton a).preimage (hA t))).and
        ((measurableSet_setOfPred.mp
          ((measurableSet_singleton 0).preimage (measurable_pullCount hA a t))).or
        (measurableSet_setOfPred.mp (measurableSet_lt measurable_const
          ((measurable_empMean hA hR a t).add
            ((measurable_from_nat (f := w)).comp (measurable_pullCount hA a t)))))))
  set κ : α → Ω → ℝ := fun a ω ↦ ∑ t ∈ range n, (E a t).indicator 1 ω with hκ_def
  have hκ_card (a : α) (ω : Ω) : κ a ω = #{t ∈ range n | ω ∈ E a t} := by
    simp [hκ_def, Set.indicator_apply]
  have hκ_int (a : α) : Integrable (κ a) P :=
    integrable_finsetSum _ fun t _ ↦ (integrable_const (1 : ℝ)).indicator (hE_meas a t)
  -- an arm with gap `Δ_a > θ` contributes at most `Δ_a + 15 √(σ² n / k)`
  have h_arm (a : α) (hθa : θ < gap ν a) : gap ν a * P[κ a] ≤ gap ν a + 15 * √(σ2 * N / k) := by
    rw [hκ_def, integral_finsetSum_indicator_one (fun t _ ↦ hE_meas a t)
      fun _ _ ↦ measure_ne_top _ _]
    exact MOSS.mul_sum_measureReal_action_eq_le h a (hν a) n hθa
  -- the regret is integrated along the pathwise decomposition with `d = D`
  have h_path : ∀ᵐ ω ∂P, regret ν A n ω ≤
      N * (2 * D ω + θ) + ∑ a ∈ univ.filter (fun a ↦ θ < gap ν a), gap ν a * κ a ω := by
    filter_upwards [MOSS.regret_le_of_forall_sub_le_index (ν := ν) h] with ω hω
    simp_rw [hκ_card]
    exact hω (D ω) θ (hD0 ω) hθ0 (hD ω)
  have hgκ : ∀ a ∈ univ.filter (fun a ↦ θ < gap ν a), Integrable (fun ω ↦ gap ν a * κ a ω) P :=
    fun a _ ↦ (hκ_int a).const_mul _
  have hD2 : Integrable (fun ω ↦ 2 * D ω) P := hD_int.const_mul 2
  have hDN : Integrable (fun ω ↦ N * (2 * D ω + θ)) P := (hD2.add (integrable_const θ)).const_mul N
  have hgκ_sum := integrable_finsetSum _ hgκ
  calc P[regret ν A n]
  _ ≤ ∫ ω, N * (2 * D ω + θ) + ∑ a ∈ univ.filter (fun a ↦ θ < gap ν a), gap ν a * κ a ω ∂P :=
    integral_mono_of_nonneg (f := regret ν A n) (ae_of_all _ fun _ ↦ regret_nonneg)
      (hDN.add hgκ_sum) h_path
  _ = N * (2 * P[D] + θ) + ∑ a ∈ univ.filter (fun a ↦ θ < gap ν a), gap ν a * P[κ a] := by
    rw [integral_add hDN hgκ_sum, integral_const_mul, integral_add hD2 (integrable_const θ),
      integral_const_mul, integral_finsetSum _ hgκ]
    simp [integral_const_mul]
  _ ≤ N * (2 * (2 * √(12 * σ2 * k / N)) + θ) +
      ∑ a ∈ univ.filter (fun a ↦ θ < gap ν a), (gap ν a + 15 * √(σ2 * N / k)) := by
    gcongr with a ha
    exact h_arm a (mem_filter.mp ha).2
  _ ≤ N * (2 * (2 * √(12 * σ2 * k / N)) + θ) + ∑ a, (gap ν a + 15 * √(σ2 * N / k)) := by
    gcongr
    · exact fun a _ _ ↦ by positivity [gap_nonneg (ν := ν) (a := a)]
    · exact subset_univ _
  _ ≤ 39 * √(σ2 * Fintype.card α * n) + ∑ a, gap ν a := by
    rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, hθ_def]
    linarith [mul_add_mul_sqrt_le_mul_sqrt σ2 hk hN]

end Regret

end LMLExplore.Bandits
