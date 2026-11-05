/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.ConfidenceBound
public import LMLExplore.Identification.Task.MeanVector
public import LMLExplore.MeasureTheory.Order.MeasurableArg
public import LMLExplore.Probability.Moments.SubGaussian.Bounded
public import LMLExplore.SequentialLearning.SubGaussianDeviation

/-!
# The stopping rule of LUCB

LUCB [KTAS12] is a fixed-confidence algorithm for top-`m` identification with tolerance `ε`
(`epsTopMTask`): it must output `m` arms whose means are all at least the `m`-th largest mean
minus `ε`. After `n` rounds, let `High` be the `m` arms with the largest empirical means and
`Low` the other arms, and let each arm `a` have a lower confidence bound `L_a` and an upper
confidence bound `U_a`. LUCB stops as soon as every arm has been pulled and
`max_{b ∈ Low} U_b < min_{a ∈ High} L_a + ε`, and then outputs `High`. The sampling rule is
arbitrary: LUCB1 samples the arm of `High` with the smallest lower bound and the arm of `Low`
with the largest upper bound, but the correctness of the stopping rule holds for every sampling
rule.

If LUCB stops with a wrong answer, then some arm `b ∈ High` is not `(ε, m)`-optimal, so that for a
set `t` of `m` arms with the largest means, `b ∉ t` and some arm `i ∈ t ∩ Low` has
`μ_b + ε < μ_i`. As `U_i < L_b + ε`, either `U_i < μ_i` or `μ_b < L_b`: an arm of `t` is
underestimated by its upper bound or an arm outside `t` is overestimated by its lower bound. Each
arm is concerned by one of the two events only. For the bounds `μ̂_a ∓ β(N_a, n)` of [KTAS12], with
pull counts `N_a` and empirical means `μ̂_a`, each event has probability at most
`∑_n ∑_{u = 1}^n exp (-u β(u, n)² / (2 σ²))` for σ²-sub-Gaussian arms, uniformly over the
sampling rules. If this sum is at most `δ / K`, LUCB stops with a wrong answer with probability
at most `δ`: this is [KTAS12, Theorem 1], stated there for Bernoulli rewards (its proof only uses
Hoeffding's inequality, valid for all rewards in `[0, 1]`, which are `1/4`-sub-Gaussian), with the
condition `∑_t ∑_{u = 1}^t exp (-2 u β(u, t)²) ≤ δ / K`.

## Main definitions

In the namespace `LMLExplore.Identification`:

* `LUCB.StopRule lcb ucb ε m n h`: the stopping rule of LUCB with confidence bounds `lcb` and
  `ucb`, after `n` rounds with history `h`.
* `lucb alg lcb ucb hlcb hucb ε m`: LUCB with sampling rule `alg` and confidence bounds `lcb` and
  `ucb`, as an identification algorithm.

## Main statements

* `topArms_mem_correct_epsTopMTask`: for `ε ≥ 0`, the `m` arms with the largest values of `μ`
  (`topArms μ m`) are a correct answer of top-`m` identification with tolerance `ε`.
* `LUCB.exists_ucb_lt_or_lt_lcb_of_stopRule`: if LUCB stops with a wrong answer, an arm of a set
  `t` of `m` arms with the largest means has an upper bound below its mean or an arm outside `t`
  has a lower bound above its mean.
* `measureReal_histOutputMeasure_lucb_le`: for every sampling rule and all confidence bounds, the
  probability that LUCB stops with a wrong answer is at most the probability of these deviations.
* `measureReal_histOutputMeasure_lucb_le_card_mul`: the same bound, `K S`, when every arm violates
  each of its confidence bounds at some round with probability at most `S`.
* `measureReal_histOutputMeasure_lucbOfRate_le_of_hasSubgaussianMGF`: [KTAS12, Theorem 1] for
  σ²-sub-Gaussian arms, and `measureReal_histOutputMeasure_lucbOfRate_le_of_mem_Icc`, its form for
  rewards in `[0, 1]`.
* `measureReal_stoppingTime_ne_top_and_notMem_le_of_isRun_lucbOfRate`: the same bound along
  every run.
* `isDeltaPAC_lucbOfRate`: LUCB is `δ`-PAC on top-`m` identification with tolerance `ε` for
  σ²-sub-Gaussian arms if it stops almost surely.

## Implementation notes

The rounds are numbered from `0`, so the exploration rate `β u n` is used after `n` rounds, at the
round `t = n + 1` of [KTAS12], where the number of pulls `u` is at most `t - 1 = n`. Our condition
`∑_n ∑_{u = 1}^n exp (-u β(u, n)² / (2 σ²)) ≤ δ / K` is therefore implied by the condition of
[KTAS12] for the rate `β(u, t - 1)`. LUCB starts by sampling each arm once; here this is part of
the stopping rule, which only stops once every arm has been pulled. The `m` arms with the largest
empirical means are chosen one at a time by `topArms`, ties being broken by LML's `argmax`.

## References

* [KTAS12] S. Kalyanakrishnan, A. Tewari, P. Auer and P. Stone, *PAC subset selection in
  stochastic multi-armed bandits*, ICML 2012, Section 3.1 and Theorem 1.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α : Type*}

variable [Fintype α] [DecidableEq α] [Nonempty α]

/-- For `ε ≥ 0` and `m` at most the number of arms, the `m` arms with the largest values of `μ`
are a correct answer of top-`m` identification with tolerance `ε` for the means `μ`. -/
lemma topArms_mem_correct_epsTopMTask [MeasurableSpace α] {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}
    (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)] {ε : ℝ} {m : ℕ} (hε : 0 ≤ ε)
    (hm : m ≤ Fintype.card α) (μ : α → ℝ) : topArms μ m ∈ (epsTopMTask ν m ε).correct μ :=
  mem_correct_epsTopMTask_of_forall_le ν hε (card_topArms μ hm)
    fun _ ha _ hc ↦ le_of_mem_topArms_of_notMem_topArms μ ha hc

namespace LUCB

/-! ### The stopping rule -/

variable (lcb ucb : (n : ℕ) → Hist Unit α ℝ n → α → ℝ) (ε : ℝ) (m : ℕ)

/-- The stopping rule of LUCB [KTAS12, Section 3.1] with lower and upper confidence bounds `lcb`
and `ucb`, tolerance `ε` and `m` arms to select, after `n` rounds with history `h`: every arm has
been pulled, and the upper bound of every arm outside the `m` arms with the largest empirical means
is less than the lower bound of every arm among them plus `ε`. -/
def StopRule (n : ℕ) (h : Hist Unit α ℝ n) : Prop :=
  (∀ a, pullCount' n h a ≠ 0) ∧
    ∀ a ∈ topArms (empMean' n h) m, ∀ b ∉ topArms (empMean' n h) m, ucb n h b < lcb n h a + ε

lemma stopRule_iff {n : ℕ} {h : Hist Unit α ℝ n} :
    StopRule lcb ucb ε m n h ↔ (∀ a, pullCount' n h a ≠ 0) ∧
      ∀ a ∈ topArms (empMean' n h) m, ∀ b ∉ topArms (empMean' n h) m,
        ucb n h b < lcb n h a + ε := (Iff.rfl)

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The `m` arms with the largest empirical means after `n` rounds are a measurable function of
the history. -/
lemma measurable_topArms_empMean' (n m : ℕ) :
    Measurable fun h : Hist Unit α ℝ n ↦ topArms (empMean' n h) m :=
  (measurable_topArms m).comp (Measurable.of_eval fun a ↦ measurable_empMean' n a)

variable {lcb ucb} in
lemma measurableSet_stopRule (hlcb : ∀ n a, Measurable fun h ↦ lcb n h a)
    (hucb : ∀ n a, Measurable fun h ↦ ucb n h a) (n : ℕ) :
    MeasurableSet {h | StopRule lcb ucb ε m n h} := by
  have hS := measurable_topArms_empMean' (α := α) n m
  refine measurableSet_setOfPred.2 ((Measurable.forall fun a ↦ ?_).and
    (Measurable.forall fun a ↦ ((measurable_finset_mem a).comp hS).imp
      (Measurable.forall fun b ↦ ((measurable_finset_mem b).comp hS).not.imp ?_)))
  · exact (measurableSet_setOfPred.1 ((measurableSet_singleton 0).preimage
      (measurable_pullCount' n a))).not
  · exact measurableSet_setOfPred.1 (measurableSet_lt (hucb n b) ((hlcb n a).add_const ε))

end LUCB

/-! ### LUCB -/

section Algorithm

variable [MeasurableSpace α] [MeasurableSingletonClass α] (alg : Algorithm Unit α ℝ)
  (lcb ucb : (n : ℕ) → Hist Unit α ℝ n → α → ℝ) (hlcb : ∀ n a, Measurable fun h ↦ lcb n h a)
  (hucb : ∀ n a, Measurable fun h ↦ ucb n h a) (ε : ℝ) (m : ℕ)

/-- **LUCB** [KTAS12, Section 3] with sampling rule `alg`, lower and upper confidence bounds `lcb`
and `ucb`, tolerance `ε` and `m` arms to select: it stops after `n` rounds with history `h` if
`LUCB.StopRule lcb ucb ε m n h` holds, and then outputs the `m` arms with the largest empirical
means. -/
noncomputable def lucb : IdentAlg Unit α ℝ (Finset α) :=
  ofStop alg (LUCB.StopRule lcb ucb ε m) (LUCB.measurableSet_stopRule ε m hlcb hucb)
    fun n ↦ Kernel.deterministic (fun h ↦ topArms (empMean' n h) m)
      (LUCB.measurable_topArms_empMean' n m)

lemma lucb_def : lucb alg lcb ucb hlcb hucb ε m =
    ofStop alg (LUCB.StopRule lcb ucb ε m) (LUCB.measurableSet_stopRule ε m hlcb hucb)
      (fun n ↦ Kernel.deterministic (fun h ↦ topArms (empMean' n h) m)
        (LUCB.measurable_topArms_empMean' n m)) := (rfl)

@[simp]
lemma alg_lucb : (lucb alg lcb ucb hlcb hucb ε m).alg = alg := by
  rw [lucb_def, alg_ofStop]

@[simp]
lemma mem_stopSet_lucb {h : Σ n, Hist Unit α ℝ n} :
    h ∈ (lucb alg lcb ucb hlcb hucb ε m).stopSet ↔ LUCB.StopRule lcb ucb ε m h.1 h.2 := by
  rw [lucb_def, mem_stopSet_ofStop]

@[simp]
lemma output_lucb (h : Σ n, Hist Unit α ℝ n) :
    (lucb alg lcb ucb hlcb hucb ε m).output h =
      Measure.dirac (topArms (empMean' h.1 h.2) m) := by
  rw [lucb_def, output_ofStop, Kernel.sigma_apply, Kernel.deterministic_apply]

/-- LUCB has stopped after `n` rounds if its stopping rule holds after `n` rounds. -/
lemma stoppingTime_lucb_le {Ω : Type*} {O : ℕ → Ω → Unit} {X : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}
    {ω : Ω} {n : ℕ} (hn : LUCB.StopRule lcb ucb ε m n (history O X Y n ω)) :
    (lucb alg lcb ucb hlcb hucb ε m).stoppingTime O X Y ω ≤ n :=
  IdentAlg.stoppingTime_le_of_mem_stopSet ((mem_stopSet_lucb alg lcb ucb hlcb hucb ε m).2 hn)

end Algorithm

/-! ### Correctness of the stopping rule -/

variable [MeasurableSpace α] {ν : (α → ℝ) → Kernel α ℝ} [∀ μ, IsMarkovKernel (ν μ)]
  {lcb ucb : (n : ℕ) → Hist Unit α ℝ n → α → ℝ} {ε : ℝ} {m : ℕ} {μ : α → ℝ} {t : Finset α}

/-- **A wrong answer of LUCB violates a confidence bound** [KTAS12, proof of Theorem 1]. Let
`ε ≥ 0`, `m ≤ K`, and let `t` be a set of `m` arms with the largest means `μ`. If the stopping rule
of LUCB holds after `n` rounds with history `h` and its answer is not a correct answer of top-`m`
identification with tolerance `ε`, then some arm `a` has been pulled and either `a ∈ t` and its
upper bound is less than `μ a`, or `a ∉ t` and its lower bound is more than `μ a`. -/
lemma LUCB.exists_ucb_lt_or_lt_lcb_of_stopRule (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α)
    (ht : #t = m) (ht' : ∀ a ∈ t, ∀ c ∉ t, μ c ≤ μ a) {n : ℕ} {h : Hist Unit α ℝ n}
    (hstop : StopRule lcb ucb ε m n h)
    (hbad : topArms (empMean' n h) m ∉ (epsTopMTask ν m ε).correct μ) :
    ∃ a, pullCount' n h a ≠ 0 ∧ (a ∈ t ∧ ucb n h a < μ a ∨ a ∉ t ∧ μ a < lcb n h a) := by
  obtain ⟨hpull, hsep⟩ := hstop
  -- An arm `b` of the answer outside `t`, and an arm `i ∈ t` outside the answer, with
  -- `μ b + ε < μ i`.
  obtain ⟨b, hbS, hbt, i, hit, hiS, hlt⟩ :=
    exists_add_lt_of_notMem_correct_epsTopMTask ν hε (card_topArms _ hm) hbad ht ht'
  -- The stopping rule gives `ucb i < lcb b + ε`.
  have hib := hsep b hbS i hiS
  by_cases hi : ucb n h i < μ i
  · exact ⟨i, hpull i, Or.inl ⟨hit, hi⟩⟩
  · exact ⟨b, hpull b, Or.inr ⟨hbt, by linarith⟩⟩

variable [MeasurableSingletonClass α] {alg : Algorithm Unit α ℝ}
  {hlcb : ∀ n a, Measurable fun h ↦ lcb n h a} {hucb : ∀ n a, Measurable fun h ↦ ucb n h a}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}

/-- **Error probability of LUCB**, for every sampling rule and all confidence bounds. Let `ε ≥ 0`,
`m ≤ K`, and let `t` be a set of `m` arms with the largest means `μ`. The probability that LUCB
stops with an answer that is not a correct answer of top-`m` identification with tolerance `ε`
for `μ` is at most the probability that at some round, some pulled arm `a ∈ t` has an upper bound
less than `μ a` or some pulled arm `a ∉ t` has a lower bound more than `μ a`, along any
algorithm-environment sequence of the sampling rule. -/
theorem measureReal_histOutputMeasure_lucb_le {env : Environment Unit α ℝ}
    (hseq : IsAlgEnvSeq O X Y alg env P) (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α) (ht : #t = m)
    (ht' : ∀ a ∈ t, ∀ c ∉ t, μ c ≤ μ a) :
    (histOutputMeasure (lucb alg lcb ucb hlcb hucb ε m) env).real
        {p | p.1 ∈ (lucb alg lcb ucb hlcb hucb ε m).stopSet ∧
          p.2 ∉ (epsTopMTask ν m ε).correct μ} ≤
      P.real {ω | ∃ n a, pullCount X a n ω ≠ 0 ∧
        (a ∈ t ∧ ucb n (history O X Y n ω) a < μ a ∨
          a ∉ t ∧ μ a < lcb n (history O X Y n ω) a)} := by
  rw [lucb_def]
  refine (measureReal_histOutputMeasure_ofStop_deterministic_le hseq
    (Set.to_countable ((epsTopMTask ν m ε).correct μ)).measurableSet).trans
    (measureReal_mono fun ω ⟨n, hn_stop, hn_wrong⟩ ↦ ?_)
  obtain ⟨a, ha, h⟩ := LUCB.exists_ucb_lt_or_lt_lcb_of_stopRule hε hm ht ht' hn_stop hn_wrong
  exact ⟨n, a, by rwa [pullCount_eq_pullCount' (O := O) (R' := Y)], h⟩

/-- **Error probability of LUCB from per-arm deviation bounds**, for every sampling rule and all
confidence bounds. Let `ε ≥ 0` and `m ≤ K`. If, along an algorithm-environment sequence of the
sampling rule, for every arm `a`, the probability that at some round `a` has been pulled and its
upper bound is less than `μ a` is at most `S`, and the same holds for its lower bound exceeding
`μ a`, then LUCB stops with an answer that is not a correct answer of top-`m` identification with
tolerance `ε` for `μ` with probability at most `K S`. -/
theorem measureReal_histOutputMeasure_lucb_le_card_mul {env : Environment Unit α ℝ}
    (hseq : IsAlgEnvSeq O X Y alg env P) (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α) {S : ℝ}
    (h_ucb : ∀ a, P.real {ω | ∃ n, pullCount X a n ω ≠ 0 ∧
      ucb n (history O X Y n ω) a < μ a} ≤ S)
    (h_lcb : ∀ a, P.real {ω | ∃ n, pullCount X a n ω ≠ 0 ∧
      μ a < lcb n (history O X Y n ω) a} ≤ S) :
    (histOutputMeasure (lucb alg lcb ucb hlcb hucb ε m) env).real
        {p | p.1 ∈ (lucb alg lcb ucb hlcb hucb ε m).stopSet ∧
          p.2 ∉ (epsTopMTask ν m ε).correct μ} ≤ Fintype.card α * S := by
  -- A set `t` of `m` arms with the largest means.
  obtain ⟨t, -, ht, ht'⟩ := exists_subset_card_eq_forall_le μ (s := univ) (j := m)
    (by rwa [card_univ])
  have ht'' : ∀ a ∈ t, ∀ c ∉ t, μ c ≤ μ a := fun a ha c hc ↦ ht' a ha c (by simp [hc])
  -- The deviation event of the arm `a`: underestimation if `a ∈ t`, overestimation otherwise.
  set E : α → Set Ω := fun a ↦ {ω | ∃ n, pullCount X a n ω ≠ 0 ∧
    (a ∈ t ∧ ucb n (history O X Y n ω) a < μ a ∨ a ∉ t ∧ μ a < lcb n (history O X Y n ω) a)}
  have hE (a : α) : P.real (E a) ≤ S := by
    by_cases ha : a ∈ t
    · refine le_trans (measureReal_mono fun ω hω ↦ ?_) (h_ucb a)
      obtain ⟨n, hn, h⟩ := hω
      exact ⟨n, hn, (h.resolve_right fun h ↦ h.1 ha).2⟩
    · refine le_trans (measureReal_mono fun ω hω ↦ ?_) (h_lcb a)
      obtain ⟨n, hn, h⟩ := hω
      exact ⟨n, hn, (h.resolve_left fun h ↦ ha h.1).2⟩
  refine (measureReal_histOutputMeasure_lucb_le hseq hε hm ht ht'').trans ?_
  calc P.real {ω | ∃ n a, pullCount X a n ω ≠ 0 ∧
        (a ∈ t ∧ ucb n (history O X Y n ω) a < μ a ∨
          a ∉ t ∧ μ a < lcb n (history O X Y n ω) a)}
  _ ≤ P.real (⋃ a ∈ (univ : Finset α), E a) := measureReal_mono
      (fun ω ⟨n, a, hn, h⟩ ↦ Set.mem_biUnion (Finset.mem_univ a) ⟨n, hn, h⟩) (measure_ne_top _ _)
  _ ≤ ∑ a, P.real (E a) := measureReal_biUnion_finset_le _ _
  _ ≤ ∑ _a : α, S := sum_le_sum fun a _ ↦ hE a
  _ = Fintype.card α * S := by rw [sum_const, card_univ, nsmul_eq_mul]

/-! ### LUCB for sub-Gaussian arms -/

section Rate

variable (alg) in
/-- **LUCB with exploration rate `β`** [KTAS12, Section 3.1], with sampling rule `alg`,
tolerance `ε` and `m` arms to select: LUCB with the confidence bounds `μ̂_a ∓ β(N_a, n)` after `n`
rounds, where `N_a` and `μ̂_a` are the number of pulls and the empirical mean of the arm `a`. -/
noncomputable def lucbOfRate (β : ℕ → ℕ → ℝ) (ε : ℝ) (m : ℕ) : IdentAlg Unit α ℝ (Finset α) :=
  lucb alg (lowerBound β) (upperBound β) (measurable_lowerBound β)
    (measurable_upperBound β) ε m

variable (alg) in
lemma lucbOfRate_def (β : ℕ → ℕ → ℝ) (ε : ℝ) (m : ℕ) :
    lucbOfRate alg β ε m = lucb alg (lowerBound β) (upperBound β)
      (measurable_lowerBound β) (measurable_upperBound β) ε m := (rfl)

end Rate

variable {ν₀ : Kernel α ℝ} [IsMarkovKernel ν₀] {σ2 : ℝ≥0} {β : ℕ → ℕ → ℝ} {δ : ℝ}

/-- **Error probability of LUCB for sub-Gaussian arms** [KTAS12, Theorem 1], for every sampling
rule. Let the arms of `ν₀` be σ²-sub-Gaussian with means `μ`, let `ε ≥ 0` and `m ≤ K`, and let the
exploration rate `β ≥ 0` satisfy `∑_n ∑_{u = 1}^n exp (-u β(u, n)² / (2 σ²)) ≤ δ / K`. Then the
probability that LUCB with the confidence bounds `μ̂_a ∓ β(N_a, n)` stops with an answer that is not
a correct answer of top-`m` identification with tolerance `ε` for `μ` is at most `δ`. -/
theorem measureReal_histOutputMeasure_lucbOfRate_le_of_hasSubgaussianMGF
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν₀ a)[id]) σ2 (ν₀ a)) (hβ : ∀ u n, 0 ≤ β u n)
    (hsum : Summable fun n ↦ ∑ u ∈ Icc 1 n, exp (-(u * β u n ^ 2 / (2 * σ2))))
    (hδ : ∑' n, ∑ u ∈ Icc 1 n, exp (-(u * β u n ^ 2 / (2 * σ2))) ≤ δ / Fintype.card α)
    (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α) :
    (histOutputMeasure (lucbOfRate alg β ε m) (Environment.bandit ν₀)).real
        {p | p.1 ∈ (lucbOfRate alg β ε m).stopSet ∧
          p.2 ∉ (epsTopMTask ν m ε).correct fun a ↦ (ν₀ a)[id]} ≤ δ := by
  rw [lucbOfRate_def]
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν₀)
  have hP : IsProbabilityMeasure (trajMeasure alg (Environment.bandit ν₀)) :=
    inferInstanceAs (IsProbabilityMeasure (trajMeasure alg (Environment.bandit ν₀)))
  refine (measureReal_histOutputMeasure_lucb_le_card_mul hseq hε hm
    (S := ∑' n, ∑ u ∈ Icc 1 n, exp (-(u * β u n ^ 2 / (2 * σ2)))) (fun a ↦ ?_)
    (fun a ↦ ?_)).trans ?_
  · refine le_trans (measureReal_mono fun ω hω ↦ ?_)
      (measureReal_exists_empMean_add_lt_le_tsum hseq a (hν a) hβ hsum)
    obtain ⟨n, hn, h⟩ := hω
    rw [upperBound_def, ← empMean_eq_empMean', ← pullCount_eq_pullCount'] at h
    exact ⟨n, hn, h⟩
  · refine le_trans (measureReal_mono fun ω hω ↦ ?_)
      (measureReal_exists_lt_empMean_sub_le_tsum hseq a (hν a) hβ hsum)
    obtain ⟨n, hn, h⟩ := hω
    rw [lowerBound_def, ← empMean_eq_empMean', ← pullCount_eq_pullCount'] at h
    exact ⟨n, hn, h⟩
  · have hK : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
    rwa [← le_div_iff₀' hK]

/-- **Error probability of LUCB for rewards in `[0, 1]`** [KTAS12, Theorem 1], for every sampling
rule. Let the rewards of the arms of `ν₀` be in `[0, 1]`, with means `μ`, let `ε ≥ 0` and `m ≤ K`,
and let the exploration rate `β ≥ 0` satisfy `∑_n ∑_{u = 1}^n exp (-2 u β(u, n)²) ≤ δ / K`. Then
the probability that LUCB with the confidence bounds `μ̂_a ∓ β(N_a, n)` stops with an answer that
is not a correct answer of top-`m` identification with tolerance `ε` for `μ` is at most `δ`. -/
theorem measureReal_histOutputMeasure_lucbOfRate_le_of_mem_Icc
    (hν : ∀ a, ∀ᵐ x ∂(ν₀ a), x ∈ Set.Icc (0 : ℝ) 1) (hβ : ∀ u n, 0 ≤ β u n)
    (hsum : Summable fun n ↦ ∑ u ∈ Icc 1 n, exp (-(2 * u * β u n ^ 2)))
    (hδ : ∑' n, ∑ u ∈ Icc 1 n, exp (-(2 * u * β u n ^ 2)) ≤ δ / Fintype.card α)
    (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α) :
    (histOutputMeasure (lucbOfRate alg β ε m) (Environment.bandit ν₀)).real
        {p | p.1 ∈ (lucbOfRate alg β ε m).stopSet ∧
          p.2 ∉ (epsTopMTask ν m ε).correct fun a ↦ (ν₀ a)[id]} ≤ δ := by
  have h_sub (a : α) : HasSubgaussianMGF (fun x ↦ x - (ν₀ a)[id]) (1 / 4) (ν₀ a) :=
    hasSubgaussianMGF_of_mem_Icc_zero_one aemeasurable_id (hν a)
  -- For `σ² = 1 / 4`, the terms `exp (-u β(u, n)² / (2 σ²))` are `exp (-2 u β(u, n)²)`.
  have h_eq : (fun n ↦ ∑ u ∈ Icc 1 n, exp (-(u * β u n ^ 2 / (2 * ((1 / 4 : ℝ≥0) : ℝ))))) =
      fun n ↦ ∑ u ∈ Icc 1 n, exp (-(2 * u * β u n ^ 2)) := by
    ext n
    refine sum_congr rfl fun u _ ↦ ?_
    norm_num
    ring_nf
  exact measureReal_histOutputMeasure_lucbOfRate_le_of_hasSubgaussianMGF h_sub hβ (h_eq ▸ hsum)
    (by simpa only [h_eq] using hδ) hε hm

/-- **Error probability of LUCB along a run**, for σ²-sub-Gaussian arms and every sampling rule
[KTAS12, Theorem 1]. Under the assumptions of
`measureReal_histOutputMeasure_lucbOfRate_le_of_hasSubgaussianMGF`, along every run of LUCB, the
probability that it stops with an answer that is not a correct answer of top-`m` identification
with tolerance `ε` for the means `μ` is at most `δ`. -/
theorem measureReal_stoppingTime_ne_top_and_notMem_le_of_isRun_lucbOfRate {out : Ω → Finset α}
    (hrun : (lucbOfRate alg β ε m).IsRun (Environment.bandit ν₀) O X Y out P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν₀ a)[id]) σ2 (ν₀ a)) (hβ : ∀ u n, 0 ≤ β u n)
    (hsum : Summable fun n ↦ ∑ u ∈ Icc 1 n, exp (-(u * β u n ^ 2 / (2 * σ2))))
    (hδ : ∑' n, ∑ u ∈ Icc 1 n, exp (-(u * β u n ^ 2 / (2 * σ2))) ≤ δ / Fintype.card α)
    (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α) :
    P.real {ω | (lucbOfRate alg β ε m).stoppingTime O X Y ω ≠ ⊤ ∧
        out ω ∉ (epsTopMTask ν m ε).correct fun a ↦ (ν₀ a)[id]} ≤ δ := by
  rw [hrun.measureReal_stoppingTime_ne_top_and_notMem_eq (Set.to_countable _).measurableSet]
  exact measureReal_histOutputMeasure_lucbOfRate_le_of_hasSubgaussianMGF hν hβ hsum hδ hε hm

/-- **LUCB is `δ`-PAC** for top-`m` identification with tolerance `ε` [KTAS12, Theorem 1], for
every sampling rule. Let the arms of every model `μ` be σ²-sub-Gaussian with means `μ`, let `ε ≥ 0`
and `m ≤ K`, and let the exploration rate `β ≥ 0` satisfy
`∑_n ∑_{u = 1}^n exp (-u β(u, n)² / (2 σ²)) ≤ δ / K`. If LUCB with the confidence bounds
`μ̂_a ∓ β(N_a, n)` stops almost surely on every model, then it is `δ`-PAC. -/
theorem isDeltaPAC_lucbOfRate (hmean : ∀ (μ : α → ℝ) a, (ν μ a)[id] = μ a)
    (hν : ∀ (μ : α → ℝ) a, HasSubgaussianMGF (fun x ↦ x - (ν μ a)[id]) σ2 (ν μ a))
    (hβ : ∀ u n, 0 ≤ β u n)
    (hsum : Summable fun n ↦ ∑ u ∈ Icc 1 n, exp (-(u * β u n ^ 2 / (2 * σ2))))
    (hδ : ∑' n, ∑ u ∈ Icc 1 n, exp (-(u * β u n ^ 2 / (2 * σ2))) ≤ δ / Fintype.card α)
    (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α)
    (h_stops : ∀ μ : α → ℝ, StopsAS (lucbOfRate alg β ε m) (Environment.bandit (ν μ))) :
    (epsTopMTask ν m ε).IsDeltaPAC (lucbOfRate alg β ε m) δ := by
  refine IdentTask.isDeltaPAC_of_measureReal_mem_stopSet_and_notMem_le
    (fun μ _ ↦ (Set.to_countable _).measurableSet) (fun μ _ ↦ ?_)
    fun μ _ ↦ by simpa only [ν_epsTopMTask] using h_stops μ
  simp only [ν_epsTopMTask]
  have h := measureReal_histOutputMeasure_lucbOfRate_le_of_hasSubgaussianMGF (alg := alg)
    (ν := ν) (hν μ) hβ hsum hδ hε hm
  rwa [funext (hmean μ)] at h

end LMLExplore.Identification
