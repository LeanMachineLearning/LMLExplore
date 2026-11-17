/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.Online.Bandit.Concentration
public import LMLExplore.Data.Finset.Card
public import LMLExplore.Data.Finset.RoundRobin
public import LMLExplore.Identification.Complexity
public import LMLExplore.Identification.PhasedElimination
public import LMLExplore.Identification.Task.RealLaws
public import LMLExplore.Probability.Moments.SubGaussian.Bounded

/-!
# Successive rejects

Successive rejects [ABM10] is the fixed-budget algorithm for best arm identification that proceeds
in `K - 1` phases, `K` being the number of arms. Given numbers of pulls
`0 = n 0 ≤ n 1 ≤ ⋯ ≤ n (K - 1)`, phase `k + 1` pulls each of the `K - k` arms that survive the first
`k` phases until it has been pulled `n (k + 1)` times, then eliminates the surviving arm with the
smallest empirical mean. The arm that survives the `K - 1` phases is recommended.

It is a phased-elimination algorithm (`LMLExplore.Identification.phasedEliminationFixedBudget`),
with the arms as answers, all of them initially active, and `K` phases numbered from `0`. Phase
`r < K - 1` is the elimination phase `r + 1` of [ABM10]: it pulls the active arms in a round robin,
`n (r + 1) - n r` times each, and its elimination map removes the active arm with the smallest sum
of rewards. The last phase `K - 1` pulls the arm that survives until the budget `T` is spent, and
eliminates nothing; the algorithm outputs the arm that survives. The phases are capped at the
budget, so that successive rejects always stops after `T` rounds.

If the best arm `a'` is eliminated at the end of phase `k + 1`, then, since only `k` arms were
eliminated before, some arm `b` of any given set `B k` of `k + 1` other arms still survives, and the
empirical mean of `a'` after `n (k + 1)` pulls is at most that of `b`. The survival bound of phased
elimination (`LMLExplore.Identification.measure_outputMeasure_phasedEliminationFixedBudget_le`), a
union bound and the sub-Gaussian concentration of the rewards give the bound
`P(error) ≤ ∑_{k < K - 1} ∑_{b ∈ B k} exp(-n (k + 1) Δ_b² / (4 σ2))` for `σ2`-sub-Gaussian arms with
gaps `Δ`. With the numbers of pulls `n k = ⌈(T - K) / (log‾ K (K + 1 - k))⌉` of [ABM10], which
fit in a budget `T ≥ K`, and with `B k` a set of `k + 1` arms with the largest gaps, every term is
at most `exp(-(T - K) / (4 σ2 log‾ K H₂))`, with the complexity `H₂ = max_i i Δ_(i)⁻²` and the
constant `log‾ K` of `LMLExplore.Identification.Complexity`. This is
[ABM10, Theorem 2]: `P(error) ≤ K (K - 1) / 2 · exp(-(T - K) / (log‾ K H₂))` for rewards in
`[0, 1]`.

## Main definitions

In the namespace `LMLExplore.Identification.SuccessiveRejects`:

* `phaseEnd K n k`: the round at which the elimination phase `k` ends, for `K` arms and numbers of
  pulls `n`.
* `cappedPhaseEnd K n T r`: the round at which phase `r` of the phased-elimination algorithm
  starts, for the budget `T`.
* `pulls n T`, `elim`: the pull schedule and the elimination maps of successive rejects.
* `pullSchedule K T`: the numbers of pulls of [ABM10].

In the namespace `LMLExplore.Identification`:

* `successiveRejects n T`: successive rejects with numbers of pulls `n` and budget `T`, as a
  fixed-budget phased-elimination algorithm.

## Main statements

In the namespace `LMLExplore.Identification`:

* `isFixedBudget_successiveRejects`: successive rejects with budget `T` stops after `T` rounds.
* `SuccessiveRejects.pullCount_phaseEnd_succ`: along a run, at the end of phase `k + 1`, every arm
  that survives `k` phases has been pulled `n (k + 1)` times.
* `SuccessiveRejects.empMean_le_of_mem_activeSet_of_notMem_activeSet_succ`: along a run, the arm
  eliminated at the end of a phase has the smallest empirical mean among the arms of that phase.
* `SuccessiveRejects.measureReal_output_ne_le_sum`: the error bound for any numbers of pulls and
  any sets `B k`.
* `SuccessiveRejects.exp_neg_pullSchedule_mul_gap_sq_div_le`: with the numbers of pulls of
  [ABM10], each term of that bound is at most `exp(-(T - K) / (4 σ2 log‾ K H₂))`.
* `SuccessiveRejects.measureReal_output_ne_le`: [ABM10, Theorem 2] for `σ2`-sub-Gaussian arms, and
  `SuccessiveRejects.measureReal_output_ne_le_of_mem_Icc`, its form for rewards in `[0, 1]`.
* `SuccessiveRejects.measureReal_outputMeasure_compl_correct_le`,
  `SuccessiveRejects.measureReal_outputMeasure_compl_correct_le_of_unitIntervalLaws`: the same
  bounds on the probability of error of best arm identification (`baiTask lawBandit lawMean`), on
  every bandit with `σ2`-sub-Gaussian arms, respectively with laws on `[0, 1]`.

## Implementation notes

All the surviving arms have the same number of pulls at the end of a phase, so the arm with the
smallest empirical mean is the arm with the smallest sum of rewards: the eliminations compare the
sums of rewards `Learning.sumRewards'` of the history at the end of the phase. Ties are broken by
LML's `argmin`, where [ABM10] breaks them at random. The active arms are pulled in the round robin
`Finset.roundRobinOn`. The length of each phase depends on its index only, not on the active set,
so that the phases start at the same rounds `cappedPhaseEnd K n T r` along every history.

## References

* [ABM10] J.-Y. Audibert, S. Bubeck and R. Munos, *Best arm identification in multi-armed
  bandits*, COLT 2010, Section 4, Theorem 2.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real
open scoped ENNReal NNReal

namespace LMLExplore.Identification.SuccessiveRejects

/-! ### Phases -/

/-- The round at which the elimination phase `k` of successive rejects with `K` arms and numbers of
pulls `n` ends: phase `k + 1` pulls each of its `K - k` arms `n (k + 1) - n k` times. -/
def phaseEnd (K : ℕ) (n : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => phaseEnd K n k + (K - k) * (n (k + 1) - n k)

@[simp]
lemma phaseEnd_zero (K : ℕ) (n : ℕ → ℕ) : phaseEnd K n 0 = 0 := (rfl)

lemma phaseEnd_succ (K : ℕ) (n : ℕ → ℕ) (k : ℕ) :
    phaseEnd K n (k + 1) = phaseEnd K n k + (K - k) * (n (k + 1) - n k) := (rfl)

lemma monotone_phaseEnd (K : ℕ) (n : ℕ → ℕ) : Monotone (phaseEnd K n) :=
  monotone_nat_of_le_succ fun k ↦ by rw [phaseEnd_succ]; exact Nat.le_add_right _ _

/-- The round at which phase `r` (numbered from `0`) of successive rejects with `K` arms, numbers of
pulls `n` and budget `T` starts: for `r < K`, the end `phaseEnd K n r` of the first `r` elimination
phases, capped at the budget, and the budget `T` from phase `K` on. The last phase `K - 1` thus
lasts until the budget is spent. -/
def cappedPhaseEnd (K : ℕ) (n : ℕ → ℕ) (T r : ℕ) : ℕ :=
  if r < K then min (phaseEnd K n r) T else T

lemma cappedPhaseEnd_def (K : ℕ) (n : ℕ → ℕ) (T r : ℕ) :
    cappedPhaseEnd K n T r = if r < K then min (phaseEnd K n r) T else T := (rfl)

lemma cappedPhaseEnd_zero {K : ℕ} (hK : 0 < K) (n : ℕ → ℕ) (T : ℕ) :
    cappedPhaseEnd K n T 0 = 0 := by
  simp [cappedPhaseEnd, hK]

lemma cappedPhaseEnd_of_le {K : ℕ} (n : ℕ → ℕ) (T : ℕ) {r : ℕ} (hr : K ≤ r) :
    cappedPhaseEnd K n T r = T := by
  simp [cappedPhaseEnd, not_lt.2 hr]

lemma monotone_cappedPhaseEnd (K : ℕ) (n : ℕ → ℕ) (T : ℕ) : Monotone (cappedPhaseEnd K n T) := by
  refine monotone_nat_of_le_succ fun r ↦ ?_
  simp only [cappedPhaseEnd]
  split_ifs with h₁ h₂ h₂
  · exact min_le_min_right T (monotone_phaseEnd K n (Nat.le_succ r))
  · exact min_le_right _ _
  · omega
  · exact le_rfl

/-- The lengths of the first `R` phases add up to the round `cappedPhaseEnd K n T R` at which
phase `R` starts. -/
lemma sum_range_cappedPhaseEnd_sub {K : ℕ} (hK : 0 < K) (n : ℕ → ℕ) (T R : ℕ) :
    ∑ r ∈ range R, (cappedPhaseEnd K n T (r + 1) - cappedPhaseEnd K n T r) =
      cappedPhaseEnd K n T R := by
  rw [sum_range_tsub (monotone_cappedPhaseEnd K n T), cappedPhaseEnd_zero hK, tsub_zero]

/-- If the elimination phases end within the budget, each phase `r < K` starts at the end
`phaseEnd K n r` of the first `r` elimination phases. -/
lemma cappedPhaseEnd_eq_phaseEnd {K : ℕ} {n : ℕ → ℕ} {T : ℕ} (hT : phaseEnd K n (K - 1) ≤ T)
    {r : ℕ} (hr : r < K) : cappedPhaseEnd K n T r = phaseEnd K n r := by
  rw [cappedPhaseEnd, ite_eq_left hr, min_eq_left ((monotone_phaseEnd K n (by omega)).trans hT)]

/-! ### Eliminations -/

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]


/-- The arm eliminated from the set `S` by the values `x`: an arm of `S` with the smallest value
(an arbitrary arm if `S` is empty). -/
noncomputable def eliminated (S : Finset α) (x : α → ℝ) : α :=
  argmin fun a ↦ if a ∈ S then (x a : EReal) else ⊤

lemma eliminated_def (S : Finset α) (x : α → ℝ) :
    eliminated S x = argmin fun a ↦ if a ∈ S then (x a : EReal) else ⊤ := (rfl)

/-- The arm `eliminated S x` minimizes the values `x`, extended by `⊤` outside `S`. -/
lemma ite_eliminated_le (S : Finset α) (x : α → ℝ) (b : α) :
    (if eliminated S x ∈ S then (x (eliminated S x) : EReal) else ⊤) ≤
      if b ∈ S then (x b : EReal) else ⊤ :=
  isMinOn_univ_iff.1 (isMinOn_argmin fun a ↦ if a ∈ S then (x a : EReal) else ⊤) b

lemma eliminated_mem {S : Finset α} (hS : S.Nonempty) (x : α → ℝ) : eliminated S x ∈ S := by
  obtain ⟨b, hb⟩ := hS
  by_contra h
  simpa [h, hb] using ite_eliminated_le S x b

lemma le_of_eliminated_mem {S : Finset α} {x : α → ℝ} (h : eliminated S x ∈ S) {b : α}
    (hb : b ∈ S) : x (eliminated S x) ≤ x b := by
  simpa [h, hb] using ite_eliminated_le S x b

/-- An arm of `S` removed by the elimination of `eliminated S x` has a value at most that of every
arm of `S`. -/
lemma le_of_mem_of_notMem_erase_eliminated {S : Finset α} {x : α → ℝ} {a b : α} (ha : a ∈ S)
    (ha' : a ∉ S.erase (eliminated S x)) (hb : b ∈ S) : x a ≤ x b := by
  rw [mem_erase, not_and_or, not_not] at ha'
  obtain rfl := ha'.resolve_right (not_not.2 ha)
  exact le_of_eliminated_mem ha hb

/-- The arm eliminated from `S` only depends on the values of the arms of `S`. -/
lemma eliminated_congr {S : Finset α} {x y : α → ℝ} (h : ∀ a ∈ S, x a = y a) :
    eliminated S x = eliminated S y := by
  rw [eliminated_def, eliminated_def]
  congr 1
  funext a
  split_ifs with ha
  · rw [h a ha]
  · rfl

/-- The arm eliminated from `S` by the values `x` is a measurable function of `(S, x)`. -/
lemma measurable_eliminated [MeasurableSpace α] :
    Measurable fun p : Finset α × (α → ℝ) ↦ eliminated p.1 p.2 := by
  simp_rw [eliminated_def]
  refine (measurable_argmin (ι := α) (α := EReal)).comp (Measurable.of_eval fun a ↦ ?_)
  refine Measurable.ite ((measurableSet_mem_finset a).preimage measurable_fst) ?_ measurable_const
  exact measurable_coe_real_ereal.comp ((measurable_pi_apply a).comp measurable_snd)

/-! ### The pull schedule and the elimination maps -/

omit [DecidableEq α] in
/-- The pull schedule of successive rejects with numbers of pulls `n` and budget `T`: phase `r`
pulls the arms of its active set `S` in a round robin, from round `cappedPhaseEnd K n T r` to round
`cappedPhaseEnd K n T (r + 1)`. -/
noncomputable def pulls (n : ℕ → ℕ) (T r : ℕ) (S : Finset α) : List α :=
  S.roundRobinList
    (cappedPhaseEnd (Fintype.card α) n T (r + 1) - cappedPhaseEnd (Fintype.card α) n T r)

omit [DecidableEq α] in
lemma pulls_def (n : ℕ → ℕ) (T r : ℕ) (S : Finset α) :
    pulls n T r S = S.roundRobinList
      (cappedPhaseEnd (Fintype.card α) n T (r + 1) - cappedPhaseEnd (Fintype.card α) n T r) :=
  (rfl)

omit [DecidableEq α] in
@[simp]
lemma length_pulls (n : ℕ → ℕ) (T r : ℕ) (S : Finset α) :
    (pulls n T r S).length =
      cappedPhaseEnd (Fintype.card α) n T (r + 1) - cappedPhaseEnd (Fintype.card α) n T r := by
  simp [pulls]

/-- Phase `r` pulls the arm `a` as many times as the round robin over its active set visits `a`
during the phase. -/
lemma count_pulls (n : ℕ → ℕ) (T r : ℕ) (S : Finset α) (a : α) :
    (pulls n T r S).count a = #{j ∈ range (cappedPhaseEnd (Fintype.card α) n T (r + 1) -
      cappedPhaseEnd (Fintype.card α) n T r) | roundRobinOn S j = a} := by
  rw [pulls, count_roundRobinList]

/-- If the elimination phases end within the budget, phase `r < K - 1`, with an active set `S` of
`K - r` arms, pulls each arm of `S` `n (r + 1) - n r` times. -/
lemma count_pulls_of_mem {n : ℕ → ℕ} {T : ℕ}
    (hT : phaseEnd (Fintype.card α) n (Fintype.card α - 1) ≤ T) {r : ℕ}
    (hr : r + 1 < Fintype.card α) {S : Finset α} (hS : #S = Fintype.card α - r) {a : α}
    (ha : a ∈ S) : (pulls n T r S).count a = n (r + 1) - n r := by
  rw [count_pulls, cappedPhaseEnd_eq_phaseEnd hT hr, cappedPhaseEnd_eq_phaseEnd hT (by omega),
    phaseEnd_succ, Nat.add_sub_cancel_left, ← hS, card_filter_roundRobinOn_eq, ite_eq_left ha]

/-- The elimination maps of successive rejects: at the end of each phase `r < K - 1`, the active
arm with the smallest sum of rewards in the history `h` is removed from the active set `S`. The
last phase `K - 1`, and the phases after it, remove no arm. -/
noncomputable def elim (r : ℕ) (S : Finset α) (h : Σ m, Hist Unit α ℝ m) : Finset α :=
  if r + 1 < Fintype.card α then S.erase (eliminated S (sumRewards' h.1 h.2)) else S

lemma elim_def (r : ℕ) (S : Finset α) (h : Σ m, Hist Unit α ℝ m) :
    elim r S h =
      if r + 1 < Fintype.card α then S.erase (eliminated S (sumRewards' h.1 h.2)) else S := (rfl)

lemma measurable_elim [MeasurableSpace α] [MeasurableSingletonClass α] (r : ℕ) (S : Finset α) :
    Measurable (elim (α := α) r S) := by
  refine measurable_sigma fun m ↦ ?_
  by_cases hr : r + 1 < Fintype.card α
  · simp only [Function.comp_def, elim, hr, ite_true]
    exact (measurable_of_countable fun a : α ↦ S.erase a).comp (measurable_eliminated.comp
      (measurable_const.prodMk (Measurable.of_eval fun a ↦ measurable_sumRewards' m a)))
  · simp only [Function.comp_def, elim, hr, ite_false]
    exact measurable_const

/-! ### The phases along a history -/

open PhasedElimination

variable {n : ℕ → ℕ} {T : ℕ} {H : ℕ → Σ m, Hist Unit α ℝ m}

/-- Phase `r` of successive rejects starts at round `cappedPhaseEnd K n T r`, along every
history. -/
@[simp]
lemma phaseStart_eq_cappedPhaseEnd (r : ℕ) :
    phaseStart univ (pulls n T) elim H r = cappedPhaseEnd (Fintype.card α) n T r := by
  rw [phaseStart_eq_sum]
  simp only [length_pulls]
  exact sum_range_cappedPhaseEnd_sub Fintype.card_pos n T r

/-- Each phase `r < K - 1` removes from the active set the active arm with the smallest sum of
rewards in the history at the end of the phase. -/
lemma activeSet_succ_of_lt {r : ℕ} (hr : r + 1 < Fintype.card α) :
    activeSet univ (pulls n T) elim H (r + 1) = (activeSet univ (pulls n T) elim H r).erase
      (eliminated (activeSet univ (pulls n T) elim H r)
        (sumRewards' _ (H (phaseStart univ (pulls n T) elim H (r + 1))).2)) := by
  rw [activeSet_succ, elim, ite_eq_left hr, inter_erase, inter_self]

/-- Each phase `r < K - 1` eliminates one arm, so that `K - r` arms are active in phase `r < K`. -/
lemma card_activeSet {r : ℕ} (hr : r < Fintype.card α) :
    #(activeSet univ (pulls n T) elim H r) = Fintype.card α - r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have ih := ih (by omega)
    have hne : (activeSet univ (pulls n T) elim H r).Nonempty := card_pos.1 (by omega)
    rw [activeSet_succ_of_lt hr, card_erase_of_mem (eliminated_mem hne _), ih]
    omega

/-- The phases from phase `K - 1` on eliminate no arm. -/
lemma activeSet_succ_of_le {r : ℕ} (hr : Fintype.card α ≤ r + 1) :
    activeSet univ (pulls n T) elim H (r + 1) = activeSet univ (pulls n T) elim H r := by
  rw [activeSet_succ, elim, ite_eq_right (not_lt.2 hr), inter_self]

/-- After the `K` phases, a single arm is active. -/
lemma card_activeSet_card : #(activeSet univ (pulls n T) elim H (Fintype.card α)) = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card α = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
  rw [hk, activeSet_succ_of_le hk.le, card_activeSet (by omega)]
  omega

/-- An arm active in phase `r` but not in phase `r + 1` is eliminated by an elimination phase:
`r < K - 1`. -/
lemma lt_card_of_mem_activeSet_of_notMem_activeSet_succ {r : ℕ} {a : α}
    (ha : a ∈ activeSet univ (pulls n T) elim H r)
    (ha' : a ∉ activeSet univ (pulls n T) elim H (r + 1)) : r + 1 < Fintype.card α := by
  by_contra hr
  rw [activeSet_succ_of_le (not_lt.1 hr)] at ha'
  exact ha' ha

/-- An arm active in phase `r` but not in phase `r + 1` has the smallest sum of rewards among the
arms active in phase `r`, in the history at the end of phase `r`. -/
lemma sumRewards'_le_of_mem_activeSet_of_notMem_activeSet_succ {r : ℕ} {a b : α}
    (ha : a ∈ activeSet univ (pulls n T) elim H r)
    (ha' : a ∉ activeSet univ (pulls n T) elim H (r + 1))
    (hb : b ∈ activeSet univ (pulls n T) elim H r) :
    sumRewards' _ (H (phaseStart univ (pulls n T) elim H (r + 1))).2 a ≤
      sumRewards' _ (H (phaseStart univ (pulls n T) elim H (r + 1))).2 b := by
  have hr := lt_card_of_mem_activeSet_of_notMem_activeSet_succ ha ha'
  rw [activeSet_succ_of_lt hr] at ha'
  exact le_of_mem_of_notMem_erase_eliminated ha ha' hb

/-! ### Runs -/

variable {Ω : Type*} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {ω : Ω}

/-- If the actions follow successive rejects and the elimination phases end within the budget,
then during phase `r < K - 1`, the elimination phase `r + 1` of [ABM10], every arm active in it is
pulled `n (r + 1) - n r` times. -/
lemma pullCount_phaseEnd_succ_eq_add (hT : phaseEnd (Fintype.card α) n (Fintype.card α - 1) ≤ T)
    (hω : ∀ t, A t ω = armAt univ (pulls n T) elim H t) {r : ℕ} (hr : r + 1 < Fintype.card α)
    {a : α} (ha : a ∈ activeSet univ (pulls n T) elim H r) :
    pullCount A a (phaseEnd (Fintype.card α) n (r + 1)) ω =
      pullCount A a (phaseEnd (Fintype.card α) n r) ω + (n (r + 1) - n r) := by
  have h := pullCount_phaseStart_succ hω a r
  rwa [phaseStart_eq_cappedPhaseEnd, phaseStart_eq_cappedPhaseEnd,
    cappedPhaseEnd_eq_phaseEnd hT hr, cappedPhaseEnd_eq_phaseEnd hT (by omega),
    count_pulls_of_mem hT hr (card_activeSet (by omega)) ha] at h

/-- If the actions follow successive rejects with nondecreasing numbers of pulls `n` with
`n 0 = 0`, and the elimination phases end within the budget, then at the end of phase `r < K - 1`,
the elimination phase `r + 1` of [ABM10], every arm active in it has been pulled `n (r + 1)`
times. -/
lemma pullCount_phaseEnd_succ (hn0 : n 0 = 0) (hn : MonotoneOn n (Set.Iic (Fintype.card α - 1)))
    (hT : phaseEnd (Fintype.card α) n (Fintype.card α - 1) ≤ T)
    (hω : ∀ t, A t ω = armAt univ (pulls n T) elim H t) {r : ℕ} (hr : r + 1 < Fintype.card α)
    {a : α} (ha : a ∈ activeSet univ (pulls n T) elim H r) :
    pullCount A a (phaseEnd (Fintype.card α) n (r + 1)) ω = n (r + 1) := by
  have hmono := hn (a := r) (b := r + 1) (by simp; omega) (by simp; omega) (Nat.le_succ r)
  rw [pullCount_phaseEnd_succ_eq_add hT hω hr ha]
  induction r generalizing a with
  | zero => simp [hn0]
  | succ r ih =>
    rw [pullCount_phaseEnd_succ_eq_add hT hω (by omega) (activeSet_succ_subset r ha),
      ih (by omega) (activeSet_succ_subset r ha)]
    · omega
    · exact hn (by simp; omega) (by simp; omega) (Nat.le_succ r)

/-- If the elimination phases end within the budget, an arm active in phase `r` but not in phase
`r + 1` has, at the end of phase `r`, a sum of rewards at most that of every arm active in phase
`r`. -/
lemma sumRewards_le_of_mem_activeSet_of_notMem_activeSet_succ
    (hT : phaseEnd (Fintype.card α) n (Fintype.card α - 1) ≤ T) {r : ℕ} {a b : α}
    (ha : a ∈ activeSet univ (pulls n T) elim (fun m ↦ sigmaHistory O A R m ω) r)
    (ha' : a ∉ activeSet univ (pulls n T) elim (fun m ↦ sigmaHistory O A R m ω) (r + 1))
    (hb : b ∈ activeSet univ (pulls n T) elim (fun m ↦ sigmaHistory O A R m ω) r) :
    sumRewards A R a (phaseEnd (Fintype.card α) n (r + 1)) ω ≤
      sumRewards A R b (phaseEnd (Fintype.card α) n (r + 1)) ω := by
  have h := sumRewards'_le_of_mem_activeSet_of_notMem_activeSet_succ ha ha' hb
  rw [phaseStart_eq_cappedPhaseEnd,
    cappedPhaseEnd_eq_phaseEnd hT (lt_card_of_mem_activeSet_of_notMem_activeSet_succ ha ha')]
    at h
  simp only [sigmaHistory_apply] at h
  rwa [sumRewards_eq_sumRewards' (O := O), sumRewards_eq_sumRewards' (O := O)]

/-- If the actions follow successive rejects with nondecreasing numbers of pulls `n` with
`n 0 = 0`, and the elimination phases end within the budget, the arm eliminated at the end of a
phase has the smallest empirical mean among the arms active in that phase. -/
lemma empMean_le_of_mem_activeSet_of_notMem_activeSet_succ (hn0 : n 0 = 0)
    (hn : MonotoneOn n (Set.Iic (Fintype.card α - 1)))
    (hT : phaseEnd (Fintype.card α) n (Fintype.card α - 1) ≤ T)
    (hω : ∀ t, A t ω = armAt univ (pulls n T) elim (fun m ↦ sigmaHistory O A R m ω) t)
    {r : ℕ} {a b : α}
    (ha : a ∈ activeSet univ (pulls n T) elim (fun m ↦ sigmaHistory O A R m ω) r)
    (ha' : a ∉ activeSet univ (pulls n T) elim (fun m ↦ sigmaHistory O A R m ω) (r + 1))
    (hb : b ∈ activeSet univ (pulls n T) elim (fun m ↦ sigmaHistory O A R m ω) r) :
    empMean A R a (phaseEnd (Fintype.card α) n (r + 1)) ω ≤
      empMean A R b (phaseEnd (Fintype.card α) n (r + 1)) ω := by
  have hr := lt_card_of_mem_activeSet_of_notMem_activeSet_succ ha ha'
  rw [empMean, empMean, pullCount_phaseEnd_succ hn0 hn hT hω hr ha,
    pullCount_phaseEnd_succ hn0 hn hT hω hr hb]
  exact div_le_div_of_nonneg_right
    (sumRewards_le_of_mem_activeSet_of_notMem_activeSet_succ hT ha ha' hb) (Nat.cast_nonneg _)

/-- If the actions follow successive rejects with nondecreasing numbers of pulls `n` with
`n 0 = 0`, the elimination phases end within the budget, and the arm `a'` is active in phase `r`
but not in phase `r + 1`, then for any set `B` of at least `r + 1` arms other than `a'`, at the
end of the elimination phase `r + 1` of [ABM10], the arm `a'` and some arm `b ∈ B` have both been
pulled `n (r + 1)` times and the sum of the rewards of `a'` is at most that of `b`. -/
lemma exists_sumRewards_le_of_mem_activeSet_of_notMem_activeSet_succ (hn0 : n 0 = 0)
    (hn : MonotoneOn n (Set.Iic (Fintype.card α - 1)))
    (hT : phaseEnd (Fintype.card α) n (Fintype.card α - 1) ≤ T)
    (hω : ∀ t, A t ω = armAt univ (pulls n T) elim (fun m ↦ sigmaHistory O A R m ω) t)
    {r : ℕ} {a' : α}
    (ha : a' ∈ activeSet univ (pulls n T) elim (fun m ↦ sigmaHistory O A R m ω) r)
    (ha' : a' ∉ activeSet univ (pulls n T) elim (fun m ↦ sigmaHistory O A R m ω) (r + 1))
    {B : Finset α} (hB : B ⊆ univ.erase a') (hBcard : r + 1 ≤ #B) :
    ∃ b ∈ B, pullCount A a' (phaseEnd (Fintype.card α) n (r + 1)) ω = n (r + 1) ∧
      pullCount A b (phaseEnd (Fintype.card α) n (r + 1)) ω = n (r + 1) ∧
      sumRewards A R a' (phaseEnd (Fintype.card α) n (r + 1)) ω ≤
        sumRewards A R b (phaseEnd (Fintype.card α) n (r + 1)) ω := by
  set S := activeSet univ (pulls n T) elim (fun m ↦ sigmaHistory O A R m ω) r
  have hr := lt_card_of_mem_activeSet_of_notMem_activeSet_succ ha ha'
  -- Only `r` arms were eliminated before phase `r`, so some arm of `B` is active in it.
  have hcard : #(univ.erase a') < #B + #(S.erase a') := by
    rw [card_erase_of_mem (mem_univ _), card_univ, card_erase_of_mem ha,
      card_activeSet (by omega)]
    omega
  obtain ⟨b, hb⟩ := inter_nonempty_of_card_lt_card_add_card hB
    (erase_subset_erase _ (subset_univ _)) hcard
  rw [mem_inter, mem_erase] at hb
  exact ⟨b, hb.1, pullCount_phaseEnd_succ hn0 hn hT hω hr ha,
    pullCount_phaseEnd_succ hn0 hn hT hω hr hb.2.2,
    sumRewards_le_of_mem_activeSet_of_notMem_activeSet_succ hT ha ha' hb.2.2⟩

end LMLExplore.Identification.SuccessiveRejects

namespace LMLExplore.Identification

open SuccessiveRejects PhasedElimination

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- **Successive rejects** [ABM10] with numbers of pulls `n` and budget `T`, the fixed-budget
identification algorithm for best arm identification, as a phased-elimination algorithm. With `K`
arms, it proceeds in `K - 1` elimination phases: phase `k + 1` pulls each of the `K - k` arms that
survive the first `k` phases, in a round robin, until it has been pulled `n (k + 1)` times, then
eliminates the surviving arm with the smallest sum of rewards, which is the surviving arm with the
smallest empirical mean (`SuccessiveRejects.empMean_le_of_mem_activeSet_of_notMem_activeSet_succ`).
A last phase pulls the arm that survives the `K - 1` phases until the budget `T` is spent, and the
algorithm recommends it. The numbers of pulls are meant to be nondecreasing with `n 0 = 0`, and the
elimination phases to end within the budget: `phaseEnd K n (K - 1) ≤ T`; otherwise the phases are
cut at round `T`. -/
noncomputable def successiveRejects (n : ℕ → ℕ) (T : ℕ) : IdentAlg Unit α ℝ α :=
  phasedEliminationFixedBudget univ (pulls n T) elim measurable_elim (roundRobinOn · 0)
    (Fintype.card α)

variable {n : ℕ → ℕ} {T : ℕ}

lemma successiveRejects_def :
    successiveRejects (α := α) n T = phasedEliminationFixedBudget univ (pulls n T) elim
      measurable_elim (roundRobinOn · 0) (Fintype.card α) := (rfl)

@[simp]
lemma alg_successiveRejects :
    (successiveRejects (α := α) n T).alg = samplingRule univ (pulls n T) elim measurable_elim :=
  alg_phasedEliminationFixedBudget

/-- Successive rejects with budget `T` stops after `T` rounds. -/
lemma isFixedBudget_successiveRejects : IsFixedBudget (successiveRejects (α := α) n T) T := by
  have h := isFixedBudget_phasedEliminationFixedBudget (S₀ := univ) (pulls := pulls n T)
    (elim := elim) (helim := measurable_elim) (out := (roundRobinOn · 0)) (R := Fintype.card α)
    (L := fun r ↦ cappedPhaseEnd (Fintype.card α) n T (r + 1) -
      cappedPhaseEnd (Fintype.card α) n T r) fun _ r _ ↦ length_pulls n T r _
  rwa [sum_range_cappedPhaseEnd_sub Fintype.card_pos, cappedPhaseEnd_of_le _ _ le_rfl] at h

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {out : Ω → α} {ν : Kernel α ℝ}
  [IsMarkovKernel ν]

/-- **Error of successive rejects**, for any numbers of pulls [ABM10, proof of Theorem 2]. Let the
arms be `σ2`-sub-Gaussian with a unique best arm `a'`, let the numbers of pulls `n` be
nondecreasing with `n 0 = 0` and the phases end within the budget, and for each phase `k + 1` let
`B k` be any set of at least `k + 1` arms other than `a'`. Then the probability that successive
rejects does not recommend `a'` is at most
`∑_{k < K - 1} ∑_{b ∈ B k} exp(-n (k + 1) Δ_b² / (4 σ2))`, where `Δ_b` is the gap of `b`. -/
theorem SuccessiveRejects.measureReal_output_ne_le_sum (hn0 : n 0 = 0)
    (hn : MonotoneOn n (Set.Iic (Fintype.card α - 1)))
    (hT : phaseEnd (Fintype.card α) n (Fintype.card α - 1) ≤ T) {σ2 : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {a' : α}
    (ha' : ∀ b ≠ a', (ν b)[id] < (ν a')[id]) {B : ℕ → Finset α} (hB : ∀ k, B k ⊆ univ.erase a')
    (hBcard : ∀ k < Fintype.card α - 1, k + 1 ≤ #(B k))
    (h : (successiveRejects n T).IsRun (Environment.bandit ν) O A R out P) :
    P.real {ω | out ω ≠ a'} ≤ ∑ k ∈ range (Fintype.card α - 1), ∑ b ∈ B k,
      Real.exp (-(n (k + 1) : ℝ) * Bandits.gap ν b ^ 2 / (4 * σ2)) := by
  set K := Fintype.card α
  have hK : 0 < K := Fintype.card_pos
  have h_alg : IsAlgEnvSeq O A R (samplingRule univ (pulls n T) elim measurable_elim)
      (Environment.bandit ν) P := by
    simpa using h.isAlgEnvSeq
  -- The events that `a'` is eliminated at the end of phase `r`.
  set F : ℕ → Set Ω := fun r ↦ {ω |
    a' ∈ activeSet univ (pulls n T) elim (fun m ↦ sigmaHistory O A R m ω) r ∧
    a' ∉ activeSet univ (pulls n T) elim (fun m ↦ sigmaHistory O A R m ω) (r + 1)}
  set E : ℕ → α → Set Ω := fun k b ↦ {ω |
    pullCount A a' (phaseEnd K n (k + 1)) ω = n (k + 1) ∧
    pullCount A b (phaseEnd K n (k + 1)) ω = n (k + 1) ∧
    sumRewards A R a' (phaseEnd K n (k + 1)) ω ≤ sumRewards A R b (phaseEnd K n (k + 1)) ω}
  -- The survival bound of phased elimination, with a single arm active after the `K` phases.
  have h_surv := measure_outputMeasure_phasedEliminationFixedBudget_le h_alg
    (out := (roundRobinOn · 0)) (R := K) (fun S hS ↦ roundRobinOn_mem hS 0) (mem_univ a')
    (ae_of_all _ fun ω ↦ card_activeSet_card.le)
  rw [← successiveRejects_def] at h_surv
  -- The last phase eliminates no arm.
  have h_last : F (K - 1) = ∅ := by
    ext ω
    simp only [F, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
    intro ha
    rwa [activeSet_succ_of_le (by omega)]
  have h_out : P.real {ω | out ω ≠ a'} =
      ((successiveRejects n T).outputMeasure (Environment.bandit ν)).real {a'}ᶜ :=
    h.hasLaw_output.measureReal_eq (measurableSet_singleton a').compl
  calc P.real {ω | out ω ≠ a'}
  _ = ((successiveRejects n T).outputMeasure (Environment.bandit ν)).real {a'}ᶜ := h_out
  _ ≤ (∑ r ∈ range K, P (F r)).toReal :=
    ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun r _ ↦ measure_ne_top P _) h_surv
  _ = ∑ r ∈ range K, P.real (F r) := ENNReal.toReal_sum fun r _ ↦ measure_ne_top P _
  _ ≤ ∑ k ∈ range (K - 1), ∑ b ∈ B k, P.real (E k b) := by
    conv_lhs => rw [← Nat.sub_add_cancel hK, sum_range_succ, h_last, measureReal_empty, add_zero]
    refine sum_le_sum fun k hk ↦ (ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono_ae ?_)).trans (measureReal_biUnion_finset_le _ _)
    filter_upwards [action_ae_all_eq_armAt h_alg] with ω hω hF
    obtain ⟨b, hb, hE⟩ := exists_sumRewards_le_of_mem_activeSet_of_notMem_activeSet_succ hn0 hn
      hT hω hF.1 hF.2 (hB k) (hBcard k (mem_range.1 hk))
    exact Set.mem_biUnion hb hE
  _ ≤ ∑ k ∈ range (K - 1), ∑ b ∈ B k,
      Real.exp (-(n (k + 1) : ℝ) * Bandits.gap ν b ^ 2 / (4 * σ2)) := by
    refine sum_le_sum fun k _ ↦ sum_le_sum fun b _ ↦ ?_
    refine (Bandits.probReal_sumRewards_le_sumRewards_le h_alg a' b _ _ _).trans ?_
    rw [← Bandits.bestArm_eq_of_forall_lt ha']
    exact Bandits.probReal_sum_le_sum_streamMeasure hν b _

/-! ### The schedule of [ABM10] -/

namespace SuccessiveRejects

/-- The phase ends in terms of the numbers of pulls, by summation by parts: after `k ≤ K - 1`
phases, `∑_{j < k} n (j + 1) + (K - k) n k` rounds have been played. -/
lemma phaseEnd_eq_sum {K : ℕ} {n : ℕ → ℕ} (hn0 : n 0 = 0) (hn : MonotoneOn n (Set.Iic (K - 1)))
    {k : ℕ} (hk : k ≤ K - 1) :
    phaseEnd K n k = ∑ j ∈ range k, n (j + 1) + (K - k) * n k := by
  induction k with
  | zero => simp [hn0]
  | succ k ih =>
    rw [phaseEnd_succ, ih (by omega), sum_range_succ]
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
      (hn (a := k) (b := k + 1) (by simp; omega) (by simp; omega) (Nat.le_succ k))
    obtain ⟨e, he⟩ : ∃ e, K - k = e + 1 := ⟨K - k - 1, by omega⟩
    rw [hd, he, show K - (k + 1) = e by omega, Nat.add_sub_cancel_left]
    ring

/-- The numbers of pulls of successive rejects with `K` arms and budget `T` [ABM10]:
`n k = ⌈(T - K) / (log‾ K (K + 1 - k))⌉` after `k ≥ 1` phases, and `n 0 = 0`. -/
noncomputable def pullSchedule (K T k : ℕ) : ℕ :=
  if k = 0 then 0 else ⌈((T : ℝ) - K) / (logBar K * (K + 1 - k))⌉₊

@[simp]
lemma pullSchedule_zero (K T : ℕ) : pullSchedule K T 0 = 0 := by simp [pullSchedule]

lemma pullSchedule_of_ne_zero (K T : ℕ) {k : ℕ} (hk : k ≠ 0) :
    pullSchedule K T k = ⌈((T : ℝ) - K) / (logBar K * (K + 1 - k))⌉₊ := by
  simp [pullSchedule, hk]

lemma le_pullSchedule (K T : ℕ) {k : ℕ} (hk : k ≠ 0) :
    ((T : ℝ) - K) / (logBar K * (K + 1 - k)) ≤ pullSchedule K T k := by
  rw [pullSchedule_of_ne_zero K T hk]
  exact Nat.le_ceil _

lemma pullSchedule_le {K T k : ℕ} (hKT : K ≤ T) (hk : k ≠ 0) (hkK : k ≤ K) :
    (pullSchedule K T k : ℝ) ≤ ((T : ℝ) - K) / logBar K * ((K : ℝ) + 1 - k)⁻¹ + 1 := by
  rw [pullSchedule_of_ne_zero K T hk, div_mul_eq_div_div, ← div_eq_mul_inv]
  refine (Nat.ceil_lt_add_one (div_nonneg (div_nonneg (by simp [hKT]) ?_) ?_)).le
  · linarith [one_half_le_logBar (K := K) (by omega)]
  · have : (k : ℝ) ≤ K := by exact_mod_cast hkK
    linarith

lemma monotoneOn_pullSchedule {K T : ℕ} (hKT : K ≤ T) :
    MonotoneOn (pullSchedule K T) (Set.Iic (K - 1)) := by
  intro j hj k hk hjk
  rcases eq_or_ne j 0 with rfl | hj0
  · simp
  rw [Set.mem_Iic] at hj hk
  rw [pullSchedule_of_ne_zero K T hj0, pullSchedule_of_ne_zero K T (by omega)]
  have hL := one_half_le_logBar (K := K) (by omega)
  have hk' : (k : ℝ) + 1 ≤ K := by exact_mod_cast (by omega : k + 1 ≤ K)
  have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
  exact Nat.ceil_mono (div_le_div_of_nonneg_left (by simp [hKT]) (by nlinarith) (by nlinarith))

/-- With the numbers of pulls of [ABM10], the `K - 1` phases end within the budget `T ≥ K`. -/
lemma phaseEnd_pullSchedule_le {K T : ℕ} (hKT : K ≤ T) :
    phaseEnd K (pullSchedule K T) (K - 1) ≤ T := by
  rcases Nat.lt_or_ge K 2 with hK | hK
  · simp [show K - 1 = 0 by omega]
  have hL := one_half_le_logBar (K := K) (by omega)
  set x : ℝ := ((T : ℝ) - K) / logBar K
  rw [phaseEnd_eq_sum (pullSchedule_zero _ _) (monotoneOn_pullSchedule hKT) le_rfl,
    show K - (K - 1) = 1 by omega, one_mul]
  have h_sum : (∑ j ∈ range (K - 1), pullSchedule K T (j + 1) : ℝ) ≤
      ∑ j ∈ range (K - 1), (x * ((K - j : ℝ))⁻¹ + 1) := by
    refine sum_le_sum fun j hj ↦ (pullSchedule_le hKT (by omega) (by grind)).trans_eq ?_
    rw [show ((K : ℝ) + 1 - ((j + 1 : ℕ) : ℝ)) = K - j by push_cast; ring]
  have h_last : (pullSchedule K T (K - 1) : ℝ) ≤ x * 2⁻¹ + 1 := by
    refine (pullSchedule_le hKT (by omega) (by omega)).trans_eq ?_
    rw [Nat.cast_sub (by omega), show ((K : ℝ) + 1 - (K - (1 : ℕ))) = 2 by push_cast; ring]
  rw [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul, mul_one] at h_sum
  have hx : x * logBar K = T - K := div_mul_cancel₀ _ (by linarith)
  have : (∑ j ∈ range (K - 1), pullSchedule K T (j + 1) + pullSchedule K T (K - 1) : ℕ) ≤
      (T : ℝ) := by
    push_cast
    calc _ ≤ x * ∑ j ∈ range (K - 1), ((K - j : ℝ))⁻¹ + (K - 1 : ℕ) + (x * 2⁻¹ + 1) :=
          add_le_add h_sum h_last
      _ = x * logBar K + K := by rw [logBar_eq_sum (by omega), Nat.cast_sub (by omega)]; ring
      _ = T := by rw [hx]; ring
  exact_mod_cast this

omit [Nonempty α] [MeasurableSingletonClass α] [IsMarkovKernel ν] in
/-- With the numbers of pulls of [ABM10], if `B` is a set of `k + 1` arms other than the unique best
arm `a'` whose gaps are at least those of the other arms `c ≠ a'`, the term of `b ∈ B` in the
error bound `measureReal_output_ne_le_sum` of phase `k + 1` is at most
`exp(-(T - K) / (4 σ2 log‾ K H₂))`: `n (k + 1) ≥ (T - K) / (log‾ K (K - k))` and
`Δ_b² ≥ (K - k) / H₂`. -/
lemma exp_neg_pullSchedule_mul_gap_sq_div_le (T : ℕ) (σ2 : ℝ≥0) {a' : α}
    (ha' : ∀ b ≠ a', (ν b)[id] < (ν a')[id]) {B : Finset α} (hB : B ⊆ univ.erase a')
    (h_top : ∀ b ∈ B, ∀ c ∈ univ.erase a' \ B, Bandits.gap ν c ≤ Bandits.gap ν b) {k : ℕ}
    (hk : k + 1 < Fintype.card α) (hBk : #B = k + 1) {b : α} (hb : b ∈ B) :
    Real.exp (-(pullSchedule (Fintype.card α) T (k + 1) : ℝ) * Bandits.gap ν b ^ 2 / (4 * σ2)) ≤
      Real.exp (-((T : ℝ) - Fintype.card α) /
        (4 * σ2 * logBar (Fintype.card α) * complexityTwo ν)) := by
  set K := Fintype.card α
  set x : ℝ := (T : ℝ) - K
  have hKk : (0 : ℝ) < K - k := by
    have : (k : ℝ) + 1 < K := by exact_mod_cast hk
    linarith
  have h_gap : (K - k : ℝ) / complexityTwo ν ≤ Bandits.gap ν b ^ 2 := by
    have := sub_card_div_complexityTwo_le_gap_sq ha' hB h_top hb
    rwa [hBk, Nat.cast_add, Nat.cast_one, add_sub_add_right_eq_sub] at this
  have h_pulls : x / (logBar K * (K - k)) ≤ pullSchedule K T (k + 1) := by
    refine (le_of_eq ?_).trans (le_pullSchedule K T (Nat.succ_ne_zero k))
    rw [show ((K : ℝ) + 1 - ((k + 1 : ℕ) : ℝ)) = K - k by push_cast; ring]
  have h_main : x / (logBar K * complexityTwo ν) ≤
      pullSchedule K T (k + 1) * Bandits.gap ν b ^ 2 := by
    calc x / (logBar K * complexityTwo ν)
        = x / (logBar K * (K - k)) * ((K - k : ℝ) / complexityTwo ν) := by
          field_simp
      _ ≤ _ := mul_le_mul h_pulls h_gap (div_nonneg hKk.le (complexityTwo_nonneg ν))
          (Nat.cast_nonneg _)
  refine Real.exp_le_exp.2 ?_
  rw [show -x / (4 * σ2 * logBar K * complexityTwo ν) =
    -(x / (logBar K * complexityTwo ν)) / (4 * σ2) by ring, neg_mul]
  exact div_le_div_of_nonneg_right (neg_le_neg h_main) (by positivity)

end SuccessiveRejects

/-- **Successive rejects** [ABM10, Theorem 2]. For `σ2`-sub-Gaussian arms with a unique best arm
`a'` and a budget `T ≥ K`, successive rejects with the numbers of pulls
`n k = ⌈(T - K) / (log‾ K (K + 1 - k))⌉` fails to recommend `a'` with probability at most
`K (K - 1) / 2 · exp(-(T - K) / (4 σ2 log‾ K H₂))`. For rewards in `[0, 1]`, `σ2 = 1 / 4` and this
is the bound `K (K - 1) / 2 · exp(-(T - K) / (log‾ K H₂))` of [ABM10]. -/
theorem SuccessiveRejects.measureReal_output_ne_le (hKT : Fintype.card α ≤ T) {σ2 : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {a' : α}
    (ha' : ∀ b ≠ a', (ν b)[id] < (ν a')[id])
    (h : (successiveRejects (pullSchedule (Fintype.card α) T) T).IsRun (Environment.bandit ν)
      O A R out P) :
    P.real {ω | out ω ≠ a'} ≤ Fintype.card α * (Fintype.card α - 1) / 2 *
      Real.exp (-((T : ℝ) - Fintype.card α) /
        (4 * σ2 * logBar (Fintype.card α) * complexityTwo ν)) := by
  set K := Fintype.card α
  have hK : 0 < K := Fintype.card_pos
  -- For each phase `k + 1`, a set `B k` of `k + 1` arms other than `a'` with the largest gaps.
  choose B hB_sub hB_card hB_top using fun k ↦ Finset.exists_subset_card_eq_forall_le
    (Bandits.gap ν) (s := univ.erase a') (j := min (k + 1) (K - 1))
    (by rw [card_erase_of_mem (mem_univ _), card_univ]; exact min_le_right _ _)
  have hB_card' (k : ℕ) (hk : k ∈ range (K - 1)) : #(B k) = k + 1 := by
    rw [hB_card, min_eq_left (by have := mem_range.1 hk; omega)]
  refine (measureReal_output_ne_le_sum (pullSchedule_zero _ _) (monotoneOn_pullSchedule hKT)
    (phaseEnd_pullSchedule_le hKT) hν ha' hB_sub
    (fun k hk ↦ (hB_card' k (mem_range.2 hk)).ge) h).trans ?_
  set y := Real.exp (-((T : ℝ) - K) / (4 * σ2 * logBar K * complexityTwo ν))
  calc ∑ k ∈ range (K - 1), ∑ b ∈ B k,
        Real.exp (-(pullSchedule K T (k + 1) : ℝ) * Bandits.gap ν b ^ 2 / (4 * σ2))
  _ ≤ ∑ k ∈ range (K - 1), ∑ _b ∈ B k, y :=
    sum_le_sum fun k hk ↦ sum_le_sum fun b hb ↦ exp_neg_pullSchedule_mul_gap_sq_div_le T σ2 ha'
      (hB_sub k) (hB_top k) (by have := mem_range.1 hk; omega) (hB_card' k hk) hb
  _ = (∑ k ∈ range (K - 1), ((k : ℝ) + 1)) * y := by
    simp_rw [sum_const, sum_mul]
    exact sum_congr rfl fun k hk ↦ by rw [hB_card' k hk, nsmul_eq_mul]; push_cast; ring
  _ = K * (K - 1) / 2 * y := by
    congr 1
    -- Gauss' formula `(∑ i < K, i) * 2 = K (K - 1)`, shifted to `∑ i < K - 1, (i + 1)`.
    have h := sum_range_id_mul_two K
    rw [← Nat.sub_add_cancel hK, sum_range_succ', Nat.add_sub_cancel, add_zero,
      Nat.sub_add_cancel hK] at h
    rw [eq_div_iff two_ne_zero, ← Nat.cast_pred hK]
    exact_mod_cast h

/-- **Successive rejects for rewards in `[0, 1]`** [ABM10, Theorem 2]: with a unique best arm `a'`
and a budget `T ≥ K`, successive rejects with the numbers of pulls
`n k = ⌈(T - K) / (log‾ K (K + 1 - k))⌉` fails to recommend `a'` with probability at most
`K (K - 1) / 2 · exp(-(T - K) / (log‾ K H₂))`. -/
theorem SuccessiveRejects.measureReal_output_ne_le_of_mem_Icc (hKT : Fintype.card α ≤ T)
    (hν : ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc (0 : ℝ) 1) {a' : α}
    (ha' : ∀ b ≠ a', (ν b)[id] < (ν a')[id])
    (h : (successiveRejects (pullSchedule (Fintype.card α) T) T).IsRun (Environment.bandit ν)
      O A R out P) :
    P.real {ω | out ω ≠ a'} ≤ Fintype.card α * (Fintype.card α - 1) / 2 *
      Real.exp (-((T : ℝ) - Fintype.card α) /
        (logBar (Fintype.card α) * complexityTwo ν)) := by
  have h_sub (a : α) : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) (1 / 4) (ν a) :=
    hasSubgaussianMGF_of_mem_Icc_zero_one aemeasurable_id (hν a)
  refine (measureReal_output_ne_le hKT h_sub ha' h).trans_eq ?_
  norm_num

/-- **Successive rejects on the bandits with σ²-sub-Gaussian arms** [ABM10, Theorem 2]. For a
budget `T ≥ K`, on every bandit `θ` whose arms are `σ2`-sub-Gaussian and which has a unique best
arm, the probability that successive rejects with the numbers of pulls
`n k = ⌈(T - K) / (log‾ K (K + 1 - k))⌉` does not output the best arm is at most
`K (K - 1) / 2 · exp(-(T - K) / (4 σ2 log‾ K H₂))`. -/
theorem SuccessiveRejects.measureReal_outputMeasure_compl_correct_le (hKT : Fintype.card α ≤ T)
    {σ2 : ℝ≥0} {θ : α → ProbabilityMeasure ℝ}
    (hθ : θ ∈ ((baiTask (lawBandit (α := α)) lawMean).restrict
      (Set.univ.pi fun _ ↦ subgaussianLaws σ2)).M) :
    ((successiveRejects (pullSchedule (Fintype.card α) T) T).outputMeasure
        (Environment.bandit (lawBandit θ))).real ((baiTask lawBandit lawMean).correct θ)ᶜ ≤
      Fintype.card α * (Fintype.card α - 1) / 2 * Real.exp (-((T : ℝ) - Fintype.card α) /
        (4 * σ2 * logBar (Fintype.card α) * complexityTwo (lawBandit θ))) := by
  rw [IdentTask.M_restrict, M_baiTask] at hθ
  obtain ⟨⟨a, ha⟩, hθ⟩ := hθ
  have hν (b : α) : HasSubgaussianMGF (fun x ↦ x - (lawBandit θ b)[id]) σ2 (lawBandit θ b) := by
    simpa only [lawMean_eq_integral_lawBandit] using mem_pi_subgaussianLaws_iff.1 hθ b
  have hrun := isRun_runMeasure (successiveRejects (α := α) (pullSchedule (Fintype.card α) T) T)
    (Environment.bandit (lawBandit θ))
  rw [(correct_baiTask_eq_singleton_iff _ _).2 ha, Set.compl_def,
    ← hrun.hasLaw_output.measureReal_eq MeasurableSet.of_discrete]
  simp only [lawMean_eq_integral_lawBandit] at ha
  simpa only [Set.mem_singleton_iff] using measureReal_output_ne_le hKT hν ha hrun

/-- **Successive rejects on the bandits with laws on `[0, 1]`** [ABM10, Theorem 2]. For a budget
`T ≥ K`, on every bandit `θ` whose arms have laws on `[0, 1]` and which has a unique best arm, the
probability that successive rejects with the numbers of pulls
`n k = ⌈(T - K) / (log‾ K (K + 1 - k))⌉` does not output the best arm is at most
`K (K - 1) / 2 · exp(-(T - K) / (log‾ K H₂))`. -/
theorem SuccessiveRejects.measureReal_outputMeasure_compl_correct_le_of_unitIntervalLaws
    (hKT : Fintype.card α ≤ T) {θ : α → ProbabilityMeasure ℝ}
    (hθ : θ ∈ ((baiTask (lawBandit (α := α)) lawMean).restrict
      (Set.univ.pi fun _ ↦ unitIntervalLaws)).M) :
    ((successiveRejects (pullSchedule (Fintype.card α) T) T).outputMeasure
        (Environment.bandit (lawBandit θ))).real ((baiTask lawBandit lawMean).correct θ)ᶜ ≤
      Fintype.card α * (Fintype.card α - 1) / 2 * Real.exp (-((T : ℝ) - Fintype.card α) /
        (logBar (Fintype.card α) * complexityTwo (lawBandit θ))) := by
  rw [IdentTask.M_restrict] at hθ
  refine (measureReal_outputMeasure_compl_correct_le hKT (σ2 := 1 / 4) ?_).trans_eq
    (by norm_num)
  rw [IdentTask.M_restrict]
  exact ⟨hθ.1, Set.pi_mono (fun _ _ ↦ unitIntervalLaws_subset_subgaussianLaws) hθ.2⟩

end LMLExplore.Identification
