/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Log.TruncLog
public import LMLExplore.EValues.BipolarRate.Basic
public import LMLExplore.Probability.ProductMeasure.Restart
import LMLExplore.EValues.BipolarRate.EProcess
import LMLExplore.EValues.Null.PrefixBet
import LMLExplore.Probability.Process.StoppedValue
import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner
import TauCeti.Probability.Process.PathLaw.Shift

/-!
# The Wald inequality at the bipolar rate for a round

Let `S₁` be a set of probability measures on `𝓧` (the null) and `Q₁` a probability measure on `𝓧`
(the alternative), and write `d = bipolarRate Q₁ S₁`. The observations are the coordinates of
`ℕ → 𝓧`, with the i.i.d. laws `Measure.infinitePi fun _ ↦ P`. A round is a duration
`σ : (ℕ → 𝓧) → ℕ`, the number of observations that it uses, and a payoff `V : (ℕ → 𝓧) → ℝ≥0∞`,
both determined by the observations of the round (`ProbabilityTheory.DependsOnBefore`). If
`1 ≤ σ ≤ K`, `V ≥ δ > 0` and the payoff has expectation at most `1` on each event `{σ ≤ n}` under
the i.i.d. law of every member of the null, then under the i.i.d. law of `Q₁` the expected
logarithm of the payoff, truncated above at `c` (`ENNReal.truncLog`), is at most
`d * 𝔼[σ]` [EVR26, Note 01]. This is the step of the proof of the Wald inequality
`ProbabilityTheory.IsEProcess.eintegral_log_stoppedValue_le_mul_bipolarRate` that uses the
bipolar rate.

## Main statements

* `ProbabilityTheory.integral_truncLog_le_bipolarRate_mul`: the Wald inequality for a round,
  `𝔼_Q[truncLog c V] ≤ d * 𝔼_Q[σ]`.

## Implementation notes

The proof restarts the round on the fresh observations each time it ends
(`ProbabilityTheory.restartTime`, `ProbabilityTheory.restartPayoff`), and bets on the number of
completed rounds with a geometric mixture. Within the first `N` observations, the mixture over the
rounds completed so far of the products of their payoffs is an e-variable for the i.i.d. null and
a function of the first `N` observations (`ProbabilityTheory.isEVar_indicator_restartPayoff`).
Its expected logarithm under `Q` is at most `maxLogGrowth Q₁ S₁ N ≤ N * d`. A Wald argument shows
that the rounds that start within the first `N` observations use at least `N + 1` observations,
hence that `(N + 1) / 𝔼_Q[σ]` of them start in expectation; letting `N → ∞` bounds the expected
truncated logarithm of the payoff by `d * 𝔼_Q[σ]`. The proof does not use the law of large
numbers, and it uses the strong Markov property only at the restart times, where it holds for an
i.i.d. sequence by independence
(`ProbabilityTheory.DependsOnBefore.integral_indicator_comp_shift_iterate`).

The proofs are adapted from `EValuesResearch/Results/BipolarRate.lean` and
`EValuesResearch/Results/BipolarRateAux.lean` (commit `dd4072f`) in the paper project
`RemyDegenne/evalues_research`, which formalizes [EVR26, Note 01]. They are specialized here to
bounded rounds.

## References

* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 01,
  `results/01-bipolar-rate.md`.
-/

public section

open MeasureTheory Filter
open TauCeti.Probability (shift shift_iterate_apply measurable_shift_iterate)
open ENNReal (truncLog)
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}

/-! ### Mixtures of restarted rounds

The restart times `restartTime σ j` and the payoffs `restartPayoff σ V j` of the first `j` rounds
are those of `LMLExplore.Probability.ProductMeasure.Restart`. The proof bets on the number of
rounds completed within the first `N` observations with a geometric mixture. -/

section Restart

variable {σ : (ℕ → 𝓧) → ℕ} {V : (ℕ → 𝓧) → ℝ≥0∞}

variable (σ V) in
/-- The geometric mixture, with weights `(1 - r) r ^ j`, of the products of the payoffs of the
first `j` rounds on the event that they use at most `N` observations. -/
private noncomputable def restartMixture (r : ℝ) (N : ℕ) (ω : ℕ → 𝓧) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal ((1 - r) * r ^ j) *
    {ω | restartTime σ j ω ≤ N}.indicator (restartPayoff σ V j) ω

/-- The mixture of the rounds completed within the first `N` observations is a function of the
first `N` observations. -/
private lemma dependsOn_restartMixture (hσ : DependsOnBefore σ σ) (hV : DependsOnBefore σ V)
    (r : ℝ) (N : ℕ) : DependsOn (restartMixture σ V r N) (Set.Iio N) := fun ω ω' h ↦
  Finset.sum_congr rfl fun j _ ↦ by
    rw [(dependsOnBefore_restartTime hσ j).dependsOn_indicator_le
      (dependsOnBefore_restartPayoff hσ hV j) N h]

/-- The mixture of restarted rounds is an e-variable for the i.i.d. null if the payoff of a round
on each event `{σ ≤ n}` is. -/
private lemma isEVar_restartMixture (hσ : DependsOnBefore σ σ) (hV : DependsOnBefore σ V)
    (hσm : Measurable σ) (hVσ : ∀ n : ℕ, IsEVar ({ω | σ ω ≤ n}.indicator V) (iidNull S₁))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (N : ℕ) :
    IsEVar (restartMixture σ V r N) (iidNull S₁) := by
  refine isEVar_finsetSum_mul _ (fun j _ ↦ isEVar_indicator_restartPayoff hσ hV hσm hVσ j N) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ mul_nonneg (by linarith) (pow_nonneg hr0 j),
    ← Finset.mul_sum, mul_neg_geom_sum]
  exact ENNReal.ofReal_le_one.2 (by have := pow_nonneg hr0 (N + 1); linarith)

variable (σ) in
/-- The number of rounds completed within the first `N` observations. -/
private def numRounds (N : ℕ) (ω : ℕ → 𝓧) : ℕ :=
  Nat.findGreatest (fun j ↦ restartTime σ j ω ≤ N) N

/-- At most `N` rounds are completed within `N` observations. -/
private lemma numRounds_le (N : ℕ) (ω : ℕ → 𝓧) : numRounds σ N ω ≤ N := Nat.findGreatest_le N

/-- The completed rounds use at most `N` observations. -/
private lemma restartTime_numRounds_le (N : ℕ) (ω : ℕ → 𝓧) :
    restartTime σ (numRounds σ N ω) ω ≤ N :=
  Nat.findGreatest_spec (P := fun j ↦ restartTime σ j ω ≤ N) (Nat.zero_le N)
    ((restartTime_zero σ ω).trans_le (Nat.zero_le N))

/-- For `i ≤ N`, the first `i` rounds use at most `N` observations if and only if they are among
the completed rounds. -/
private lemma restartTime_le_iff_le_numRounds {N i : ℕ} (hi : i ≤ N) (ω : ℕ → 𝓧) :
    restartTime σ i ω ≤ N ↔ i ≤ numRounds σ N ω :=
  ⟨fun h ↦ Nat.le_findGreatest hi h,
    fun h ↦ (monotone_restartTime σ ω h).trans (restartTime_numRounds_le N ω)⟩

/-- Among the first `N + 1` rounds, those that end within the first `N` observations are the
completed ones. -/
private lemma sum_range_indicator_restartTime_le (g : ℕ → (ℕ → 𝓧) → ℝ) (N : ℕ) (ω : ℕ → 𝓧) :
    ∑ i ∈ Finset.range (N + 1), {ω | restartTime σ i ω ≤ N}.indicator (g i) ω =
      ∑ i ∈ Finset.range (numRounds σ N ω + 1), g i ω := by
  have hJN : numRounds σ N ω ≤ N := numRounds_le N ω
  rw [← Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_succ hJN))
    (f := fun i ↦ {ω | restartTime σ i ω ≤ N}.indicator (g i) ω)]
  · refine Finset.sum_congr rfl fun i hi ↦ Set.indicator_of_mem ?_ _
    have hi' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    exact (restartTime_le_iff_le_numRounds (hi'.trans hJN) ω).2 hi'
  · intro i hi hiJ
    refine Set.indicator_of_notMem (fun h ↦ hiJ (Finset.mem_range.2 (Nat.lt_succ_of_le ?_))) _
    exact (restartTime_le_iff_le_numRounds (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) ω).1 h

/-- If every round uses at least one observation, the round after the completed ones ends after
the first `N` observations. -/
private lemma lt_restartTime_numRounds_succ (hσ1 : ∀ ω, 1 ≤ σ ω) (N : ℕ) (ω : ℕ → 𝓧) :
    N < restartTime σ (numRounds σ N ω + 1) ω := by
  by_cases hJ : numRounds σ N ω + 1 ≤ N
  · exact not_le.1 (Nat.findGreatest_is_greatest (P := fun j ↦ restartTime σ j ω ≤ N)
      (Nat.lt_succ_self _) hJ)
  · have hJN : numRounds σ N ω = N := le_antisymm (numRounds_le N ω) (by omega)
    rw [hJN]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (le_restartTime hσ1 (N + 1) ω)

/-- **Wald's argument, pointwise.** The durations of the rounds that start within the first `N`
observations add up to more than `N`. -/
private lemma add_one_le_sum_indicator (hσ1 : ∀ ω, 1 ≤ σ ω) (N : ℕ) (ω : ℕ → 𝓧) :
    (N + 1 : ℝ) ≤ ∑ i ∈ Finset.range (N + 1), {ω | restartTime σ i ω ≤ N}.indicator
      (fun ω ↦ (σ ((shift 𝓧)^[restartTime σ i ω] ω) : ℝ)) ω := by
  set J := numRounds σ N ω
  have hJ : N + 1 ≤ restartTime σ (J + 1) ω := lt_restartTime_numRounds_succ hσ1 N ω
  calc (N + 1 : ℝ) ≤ (restartTime σ (J + 1) ω : ℝ) := by exact_mod_cast hJ
  _ = ∑ i ∈ Finset.range (J + 1), (σ ((shift 𝓧)^[restartTime σ i ω] ω) : ℝ) := by
    rw [restartTime_eq_sum, Nat.cast_sum]
  _ = _ := (sum_range_indicator_restartTime_le
    (fun i ω ↦ (σ ((shift 𝓧)^[restartTime σ i ω] ω) : ℝ)) N ω).symm

end Restart

/-! ### The Wald inequality for a round -/

section Wald

variable {σ : (ℕ → 𝓧) → ℕ} {V : (ℕ → 𝓧) → ℝ≥0∞}

/-- A measurable bounded duration is integrable, as a real function, under a finite measure. -/
private lemma integrable_natCast_of_le {μ : Measure (ℕ → 𝓧)} [IsFiniteMeasure μ]
    {τ : (ℕ → 𝓧) → ℕ} (hτm : Measurable τ) {K : ℕ} (hτK : ∀ ω, τ ω ≤ K) :
    Integrable (fun ω ↦ (τ ω : ℝ)) μ :=
  Integrable.of_bound (measurable_from_top.comp hτm).aestronglyMeasurable K
    (ae_of_all _ fun ω ↦ by simpa using hτK ω)

/-- The logarithm of the mixture of restarted rounds is at least the logarithm of the weight of
the completed rounds plus their truncated log-payoffs, hence at least the sum of the truncated
log-payoffs of the rounds that start within the first `N` observations, up to `c` for the last
one and to the logarithm of the weights. -/
private lemma log_restartMixture_ge {δ : ℝ} (hδ : 0 < δ) (hVδ : ∀ ω, ENNReal.ofReal δ ≤ V ω)
    (c : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) (ω : ℕ → 𝓧) :
    ((Real.log (1 - r) + N * Real.log r - c + ∑ i ∈ Finset.range (N + 1),
        {ω | restartTime σ i ω ≤ N}.indicator
          (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω : ℝ) : EReal) ≤
      ENNReal.log (restartMixture σ V r N ω) := by
  set J := numRounds σ N ω
  set Y : ℕ → ℝ := fun i ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))
  have hV0 (ω : ℕ → 𝓧) : V ω ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hδ) (hVδ ω)).ne'
  have hJN : J ≤ N := numRounds_le N ω
  have hr' : 0 < 1 - r := by linarith
  -- the mixture is at least its term of index `J`
  have h1 : ENNReal.ofReal ((1 - r) * r ^ J * Real.exp (∑ i ∈ Finset.range J, Y i)) ≤
      restartMixture σ V r N ω := by
    calc ENNReal.ofReal ((1 - r) * r ^ J * Real.exp (∑ i ∈ Finset.range J, Y i))
    _ = ENNReal.ofReal ((1 - r) * r ^ J) *
          ∏ i ∈ Finset.range J, ENNReal.ofReal (Real.exp (Y i)) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hr'.le (pow_nonneg hr0.le J)), Real.exp_sum,
        ENNReal.ofReal_prod_of_nonneg fun i _ ↦ (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal ((1 - r) * r ^ J) * restartPayoff σ V J ω := by
      rw [restartPayoff_eq_prod]
      gcongr with i hi
      exact ENNReal.ofReal_exp_truncLog_le (hV0 _)
    _ = ENNReal.ofReal ((1 - r) * r ^ J) *
          {ω | restartTime σ J ω ≤ N}.indicator (restartPayoff σ V J) ω := by
      rw [Set.indicator_of_mem (restartTime_numRounds_le N ω)]
    _ ≤ restartMixture σ V r N ω :=
      Finset.single_le_sum (f := fun j ↦ ENNReal.ofReal ((1 - r) * r ^ j) *
        {ω | restartTime σ j ω ≤ N}.indicator (restartPayoff σ V j) ω)
        (fun _ _ ↦ bot_le) (Finset.mem_range.2 (Nat.lt_succ_of_le hJN))
  -- the logarithm of this term
  have hpos : 0 < (1 - r) * r ^ J * Real.exp (∑ i ∈ Finset.range J, Y i) := by
    have := pow_pos hr0 J
    have := Real.exp_pos (∑ i ∈ Finset.range J, Y i)
    positivity
  have h2 : Real.log ((1 - r) * r ^ J * Real.exp (∑ i ∈ Finset.range J, Y i)) =
      Real.log (1 - r) + J * Real.log r + ∑ i ∈ Finset.range J, Y i := by
    rw [Real.log_mul (mul_pos hr' (pow_pos hr0 J)).ne' (Real.exp_pos _).ne',
      Real.log_mul hr'.ne' (pow_pos hr0 J).ne', Real.log_pow, Real.log_exp]
  -- the sum over the rounds that start within the first `N` observations
  have h3 : ∑ i ∈ Finset.range (N + 1), {ω | restartTime σ i ω ≤ N}.indicator
      (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω =
        ∑ i ∈ Finset.range (J + 1), Y i :=
    sum_range_indicator_restartTime_le
      (fun i ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) N ω
  have h4 : Y J ≤ c := ENNReal.truncLog_le (hV0 _)
  have h5 : (N : ℝ) * Real.log r ≤ J * Real.log r :=
    mul_le_mul_of_nonpos_right (by exact_mod_cast hJN) (Real.log_nonpos hr0.le hr1.le)
  calc ((Real.log (1 - r) + N * Real.log r - c + ∑ i ∈ Finset.range (N + 1),
        {ω | restartTime σ i ω ≤ N}.indicator
          (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω : ℝ) : EReal)
  _ ≤ ((Real.log ((1 - r) * r ^ J * Real.exp (∑ i ∈ Finset.range J, Y i)) : ℝ) : EReal) := by
    rw [h2, h3, Finset.sum_range_succ]
    exact EReal.coe_le_coe_iff.2 (by linarith)
  _ = ENNReal.log (ENNReal.ofReal ((1 - r) * r ^ J * Real.exp (∑ i ∈ Finset.range J, Y i))) :=
    (ENNReal.log_ofReal_of_pos hpos).symm
  _ ≤ ENNReal.log (restartMixture σ V r N ω) := ENNReal.log_le_log h1

/-- The limit argument of the Wald inequality: if for every `r ∈ (0, 1)` and `N ≥ 1` some
`s ≥ (N + 1) / m` satisfies `log (1 - r) + N log r - c + A s ≤ N d`, then `A ≤ d m`. -/
private lemma le_mul_of_forall_restart {A c d m : ℝ} (hm : 0 < m) (hd : 0 ≤ d)
    (h : ∀ r : ℝ, 0 < r → r < 1 → ∀ N : ℕ, 1 ≤ N → ∃ s : ℝ,
      (N + 1 : ℝ) ≤ m * s ∧ Real.log (1 - r) + N * Real.log r - c + A * s ≤ N * d) :
    A ≤ d * m := by
  by_contra hlt
  rw [not_le] at hlt
  have hA : 0 < A := lt_of_le_of_lt (mul_nonneg hd hm.le) hlt
  set ε := A / m - d with hε
  have hε0 : 0 < ε := by
    rw [hε, sub_pos, lt_div_iff₀ hm]
    linarith
  set r := Real.exp (-(ε / 2)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hlogr : Real.log r = -(ε / 2) := Real.log_exp _
  obtain ⟨N, hN⟩ := exists_nat_gt ((c - Real.log (1 - r)) * 2 / ε)
  obtain ⟨s, hs1, hs2⟩ := h r hr0 hr1 (N + 1) (by omega)
  have hAs : A * (((N + 1 : ℕ) : ℝ) + 1) / m ≤ A * s := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hm).2 (by linarith [mul_comm m s])) hA.le
  have key : A * (((N + 1 : ℕ) : ℝ) + 1) / m = (((N + 1 : ℕ) : ℝ) + 1) * (d + ε) := by
    rw [hε]
    field_simp
    ring
  rw [key] at hAs
  rw [hlogr] at hs2
  have hN' : (c - Real.log (1 - r)) * 2 < N * ε := (div_lt_iff₀ hε0).1 hN
  push_cast at hs2 hAs
  nlinarith

/-- **Wald's argument.** Under an i.i.d. law, the rounds that start within the first `N`
observations number at least `(N + 1) / 𝔼[σ]` in expectation. -/
private lemma add_one_le_integral_mul_sum_measureReal (hσ : DependsOnBefore σ σ)
    (hσm : Measurable σ) (hσ1 : ∀ ω, 1 ≤ σ ω) {K : ℕ} (hσK : ∀ ω, σ ω ≤ K) (P : Measure 𝓧)
    [IsProbabilityMeasure P] (N : ℕ) :
    (N + 1 : ℝ) ≤ (∫ ω, (σ ω : ℝ) ∂Measure.infinitePi (fun _ : ℕ ↦ P)) *
      ∑ i ∈ Finset.range (N + 1),
        (Measure.infinitePi (fun _ : ℕ ↦ P)).real {ω | restartTime σ i ω ≤ N} := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ P)
  set m := ∫ ω, (σ ω : ℝ) ∂μ
  have hσm' : Measurable fun ω ↦ (σ ω : ℝ) := measurable_from_top.comp hσm
  have hT (i : ℕ) : Measurable (restartTime σ i) := measurable_restartTime hσm i
  have hgi (i : ℕ) : Integrable (fun ω ↦ {ω | restartTime σ i ω ≤ N}.indicator
      (fun ω ↦ (σ ((shift 𝓧)^[restartTime σ i ω] ω) : ℝ)) ω) μ :=
    (integrable_natCast_of_le (measurable_apply_of_countable
      (fun t ↦ hσm.comp (measurable_shift_iterate t)) (hT i)) fun _ ↦ hσK _).indicator
      (hT i measurableSet_Iic)
  calc (N + 1 : ℝ) = ∫ _, (N + 1 : ℝ) ∂μ := by simp
  _ ≤ ∫ ω, ∑ i ∈ Finset.range (N + 1), {ω | restartTime σ i ω ≤ N}.indicator
        (fun ω ↦ (σ ((shift 𝓧)^[restartTime σ i ω] ω) : ℝ)) ω ∂μ :=
    integral_mono (integrable_const _) (integrable_finsetSum _ fun i _ ↦ hgi i)
      fun ω ↦ add_one_le_sum_indicator hσ1 N ω
  _ = ∑ i ∈ Finset.range (N + 1), μ.real {ω | restartTime σ i ω ≤ N} * m := by
    rw [integral_finsetSum _ fun i _ ↦ hgi i]
    exact Finset.sum_congr rfl fun i _ ↦
      (dependsOnBefore_restartTime hσ i).integral_indicator_comp_shift_iterate (hT i) P hσm'
        (integrable_natCast_of_le hσm hσK) N
  _ = m * ∑ i ∈ Finset.range (N + 1), μ.real {ω | restartTime σ i ω ≤ N} := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- The logarithmic bound of the Wald inequality for a round: the expected logarithm of the
mixture of the rounds completed within the first `N` observations is at most `N d`, and at least
the logarithm of the weights plus the expected truncated log-payoffs of the rounds that start
within the first `N` observations. -/
private lemma add_integral_truncLog_mul_sum_measureReal_le (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hσ : DependsOnBefore σ σ) (hV : DependsOnBefore σ V) (hσm : Measurable σ)
    (hVm : Measurable V)
    (h_null : ∀ P ∈ S₁, ∀ n : ℕ,
      ∫⁻ ω, {ω | σ ω ≤ n}.indicator V ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hVδ : ∀ ω, ENNReal.ofReal δ ≤ V ω) {c : ℝ}
    (hd : bipolarRate Q₁ S₁ ≠ ⊤) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {N : ℕ} (hN : 1 ≤ N) :
    Real.log (1 - r) + N * Real.log r - c +
        (∫ ω, truncLog c (V ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)) *
          ∑ i ∈ Finset.range (N + 1),
            (Measure.infinitePi (fun _ : ℕ ↦ Q₁)).real {ω | restartTime σ i ω ≤ N} ≤
      N * (bipolarRate Q₁ S₁).toReal := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  set A := ∫ ω, truncLog c (V ω) ∂μ
  have hYm : Measurable fun ω ↦ truncLog c (V ω) := (ENNReal.measurable_truncLog c).comp hVm
  have hT (i : ℕ) : Measurable (restartTime σ i) := measurable_restartTime hσm i
  -- the truncated log-payoffs are bounded, hence integrable
  have hfi (i : ℕ) : Integrable (fun ω ↦ {ω | restartTime σ i ω ≤ N}.indicator
      (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω) μ :=
    (ENNReal.integrable_truncLog_comp hδ (measurable_apply_of_countable
      (fun t ↦ hVm.comp (measurable_shift_iterate t)) (hT i)) (fun _ ↦ hVδ _)).indicator
      (hT i measurableSet_Iic)
  have hmix : IsEVar (restartMixture σ V r N) (iidNull S₁) :=
    isEVar_restartMixture hσ hV hσm (fun n ↦ isEVar_iidNull_iff.2
      ⟨hVm.indicator (hσm measurableSet_Iic), fun P hP _ ↦ h_null P hP n⟩) hr0.le hr1.le N
  set B := Real.log (1 - r) + N * Real.log r - c
  have hsum : Integrable (fun ω ↦ ∑ i ∈ Finset.range (N + 1),
      {ω | restartTime σ i ω ≤ N}.indicator
        (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω) μ :=
    integrable_finsetSum _ fun i _ ↦ hfi i
  have hint : Integrable (fun ω ↦ B + ∑ i ∈ Finset.range (N + 1),
      {ω | restartTime σ i ω ≤ N}.indicator
        (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω) μ :=
    (integrable_const B).add hsum
  have hval : ∫ ω, B + ∑ i ∈ Finset.range (N + 1), {ω | restartTime σ i ω ≤ N}.indicator
        (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω ∂μ =
      B + A * ∑ i ∈ Finset.range (N + 1), μ.real {ω | restartTime σ i ω ≤ N} := by
    rw [integral_add (integrable_const B) hsum, integral_finsetSum _ fun i _ ↦ hfi i,
      Finset.mul_sum]
    simp only [integral_const, probReal_univ, one_smul]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦
      ((dependsOnBefore_restartTime hσ i).integral_indicator_comp_shift_iterate (hT i) Q₁ hYm
        (ENNReal.integrable_truncLog_comp hδ hVm hVδ) N).trans (mul_comm _ _)
  have hle : ((B + A * ∑ i ∈ Finset.range (N + 1), μ.real {ω | restartTime σ i ω ≤ N} : ℝ) :
      EReal) ≤ (N : EReal) * bipolarRate Q₁ S₁ := by
    rw [← hval, ← eintegral_eq_integral hint]
    calc ∫ᵉ ω, ((B + ∑ i ∈ Finset.range (N + 1), {ω | restartTime σ i ω ≤ N}.indicator
          (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω : ℝ) : EReal) ∂μ
    _ ≤ ∫ᵉ ω, ENNReal.log (restartMixture σ V r N ω) ∂μ :=
      eintegral_mono fun ω ↦ log_restartMixture_ge hδ hVδ c hr0 hr1 N ω
    _ ≤ maxLogGrowth Q₁ S₁ N :=
      IsEVar.eintegral_log_le_maxLogGrowth Q₁ hS₁ hmix
        (Filtration.measurable_piLT_of_dependsOn hmix.measurable
          (dependsOn_restartMixture hσ hV r N))
    _ ≤ N * bipolarRate Q₁ S₁ := maxLogGrowth_le_mul_bipolarRate Q₁ S₁ (by omega)
  rw [← coe_toReal_bipolarRate (fun P hP ↦ (hS₁ P hP).measure_univ.le) hd, ← EReal.coe_natCast,
    ← EReal.coe_mul, EReal.coe_le_coe_iff] at hle
  exact hle

/-- **The Wald inequality for a round.** Let `σ ≥ 1` be the bounded duration and `V ≥ δ > 0` the
payoff of a round, both determined by the observations of the round. If the payoff has
expectation at most `1` on each event `{σ ≤ n}` under the i.i.d. laws of the members of `S₁`,
then under the i.i.d. law of `Q₁` the expected logarithm of the payoff, truncated above at `c`, is
at most the bipolar rate times the expected duration. -/
lemma integral_truncLog_le_bipolarRate_mul (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hσ : DependsOnBefore σ σ)
    (hV : DependsOnBefore σ V) (hσm : Measurable σ) (hVm : Measurable V) (hσ1 : ∀ ω, 1 ≤ σ ω)
    {K : ℕ} (hσK : ∀ ω, σ ω ≤ K)
    (h_null : ∀ P ∈ S₁, ∀ n : ℕ,
      ∫⁻ ω, {ω | σ ω ≤ n}.indicator V ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hVδ : ∀ ω, ENNReal.ofReal δ ≤ V ω) {c : ℝ}
    (hd : bipolarRate Q₁ S₁ ≠ ⊤) :
    ∫ ω, truncLog c (V ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤
      (bipolarRate Q₁ S₁).toReal * ∫ ω, (σ ω : ℝ) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  set m := ∫ ω, (σ ω : ℝ) ∂μ
  have hd0 := bipolarRate_nonneg Q₁ (fun P hP ↦ (hS₁ P hP).measure_univ.le)
  have hm1 : 1 ≤ m := by
    calc (1 : ℝ) = ∫ _, (1 : ℝ) ∂μ := by simp
    _ ≤ m := integral_mono (integrable_const _) (integrable_natCast_of_le hσm hσK)
      fun ω ↦ by exact_mod_cast hσ1 ω
  refine le_mul_of_forall_restart (c := c) (by linarith) (EReal.toReal_nonneg hd0)
    fun r hr0 hr1 N hN ↦ ⟨_, add_one_le_integral_mul_sum_measureReal hσ hσm hσ1 hσK Q₁ N,
      add_integral_truncLog_mul_sum_measureReal_le Q₁ hS₁ hσ hV hσm hVm h_null hδ hVδ hd hr0
        hr1 hN⟩

end Wald

end ProbabilityTheory
