/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Data.Finset.RoundRobin
public import LMLExplore.Identification.ConfidenceBound
public import LMLExplore.Identification.PhasedElimination
public import LMLExplore.Identification.Task.RealLaws
public import LMLExplore.SequentialLearning.SubGaussianDeviation

/-!
# Successive elimination

Successive elimination [EMM02, EMM06] is a fixed-confidence algorithm for best arm identification.
It keeps a set of *active* arms, initially all the arms, and proceeds in phases: each phase pulls
every active arm once, and at its end eliminates every active arm `a` whose upper confidence bound
is less than the lower confidence bound of some active arm. It stops when at most one arm is
active, and outputs it. It is the phased-elimination algorithm (`phasedElimination`) with initial
active set `univ`, the pull schedule `SuccessiveElimination.pulls` and the elimination maps
`SuccessiveElimination.elim`.

At the end of phase `r`, every active arm has been pulled `r + 1` times. If the confidence
intervals of all the arms contain their means at all rounds, a best arm `a⋆` is never eliminated,
so successive elimination outputs `a⋆` whenever it stops. If moreover the widths of the intervals
after `u` pulls are at most `w u`, an arm `b` with gap `Δ_b = μ_{a⋆} - μ_b > 2 w u` is not active
after `u ≠ 0` phases. Hence an arm `b ≠ a⋆` is active in at most `T_b` phases, for any `T_b ≠ 0`
with `2 w (T_b) < Δ_b`, and the algorithm stops after at most `T_{a⋆}` phases, for any
`T_{a⋆} ≠ 0` with `2 w (T_{a⋆}) < Δ_b` for every `b ≠ a⋆`: it stops after at most `∑_a T_a`
rounds.

For σ²-sub-Gaussian arms and the confidence intervals `μ̂_a ∓ β(N_a)` with
`β(u) = √(2 σ² (log (2 u (u + 1)) + log (K / δ)) / u)`, the intervals of all the arms contain
their means at all rounds with probability at least `1 - δ` ([LS, Lemma 33.8] and a union bound
over the `K` arms). Hence successive elimination is `δ`-correct for best arm identification, and
it stops after at most `∑_a T_a` rounds with probability at least `1 - δ`, where `w = 2 β`
[EMM02, Theorem 3; EMM06, Theorem 8]. Solving `4 β(u) < Δ_a` shows that `T_a` can be taken equal
to `N(Δ_a) = max ⌈64 σ² Δ_a⁻² (log (K / δ) + 2 log (256 σ² Δ_a⁻²))⌉₊ 1`, of order
`σ² Δ_a⁻² log (K / (δ Δ_a))` for `σ² = 1`, with the smallest gap in place of the gap `0` of the
best arm.

## Main definitions

In the namespace `LMLExplore.Identification`:

* `SuccessiveElimination.pulls`: the pull schedule of successive elimination, each phase pulls
  every active arm once.
* `SuccessiveElimination.elim lcb ucb`: the elimination maps of successive elimination for the
  lower and upper confidence bounds `lcb` and `ucb`, which keep the active arms whose upper
  confidence bound is at least the lower confidence bound of every active arm.
* `successiveElimination lcb ucb hlcb hucb`: successive elimination as an identification
  algorithm, built with the phased-elimination constructor.
* `successiveEliminationOfRate β`: successive elimination with the confidence bounds
  `μ̂_a ∓ β(N_a)`.
* `SuccessiveElimination.pullBound σ2 y Δ`: the number of pulls
  `max ⌈64 σ² Δ⁻² (y + 2 log (256 σ² Δ⁻²))⌉₊ 1` after which `4 subgaussianRate σ2 y < Δ`.

## Main statements

* `SuccessiveElimination.pullCount_phaseStart_of_mem`: an arm active in phase `r` has been pulled
  `r` times at its start.
* `SuccessiveElimination.mem_activeSet_of_forall_le`,
  `SuccessiveElimination.activeSet_eq_singleton`: along a run in which the confidence intervals
  contain the means, a best arm `a` stays active; if their widths are at most `w`, only `a` is
  active after `u ≠ 0` phases when `2 w u` is less than every gap.
* `measureReal_histOutputMeasure_successiveElimination_le`: for all confidence bounds, the
  probability that successive elimination stops with an arm other than a best arm `a⋆` is at most
  the probability that the confidence interval of some pulled arm misses its mean at some round.
* `stoppingTime_successiveElimination_le`: along a run in which the confidence intervals contain
  the means and have widths at most `w`, successive elimination stops after at most `∑_a T_a`
  rounds.
* `measureReal_sum_lt_stoppingTime_successiveEliminationOfRate_le`: for σ²-sub-Gaussian arms,
  successive elimination with the rate `β = subgaussianRate σ2 (log (K / δ))` stops after more than
  `∑_a T_a` rounds with probability at most `δ`, for `w = 2 β` [EMM02, Theorem 3].
* `measureReal_pullBound_add_sum_lt_stoppingTime_successiveEliminationOfRate_le`: the same bound
  in closed form: if `μ_a - μ_b ≥ Δ > 0` for every arm `b ≠ a`, successive elimination stops
  after more than `N(Δ) + ∑_{b ≠ a} N(μ_a - μ_b)` rounds with probability at most `δ`, for
  `N = pullBound σ2 (log (K / δ))` [EMM02, Theorem 3].
* `measureReal_histOutputMeasure_successiveEliminationOfRate_notMem_or_le`: for σ²-sub-Gaussian
  arms with a unique best arm `a⋆`, successive elimination with that rate does not stop, or stops
  with an arm other than `a⋆`, with probability at most `δ`.
* `isDeltaCorrect_successiveEliminationOfRate`: successive elimination with that rate is
  `δ`-correct for best arm identification on every bandit with σ²-sub-Gaussian arms, the
  restriction of `baiTask lawBandit lawMean` to the σ²-sub-Gaussian laws [EMM02, Theorem 3].

## Implementation notes

The confidence bounds `lcb n h` and `ucb n h` after `n` rounds with history `h` are evaluated at
the end of each phase, when every active arm has been pulled. The output of the final active set
`S` is `roundRobinOn S 0`, an element of `S` when `S` is nonempty. The confidence bounds
`μ̂_a ∓ β(N_a)` of `successiveEliminationOfRate` are the bounds `lowerBound` and `upperBound`,
also used by LUCB, for a rate that does not depend on the round. The rate
`subgaussianRate σ2 (log (K / δ))` and the probability that the confidence intervals of all the
arms contain their means at all rounds
(`measureReal_exists_exists_subgaussianRate_lt_abs_empMean_sub_le`) are in
`SequentialLearning/SubGaussianDeviation.lean`.

## References

* [EMM02] E. Even-Dar, S. Mannor and Y. Mansour, *PAC bounds for multi-armed bandit and Markov
  decision processes*, COLT 2002, Theorem 3.
* [EMM06] E. Even-Dar, S. Mannor and Y. Mansour, *Action elimination and stopping conditions for
  the multi-armed bandit and reinforcement learning problems*, JMLR 7 (2006), Theorem 8.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 33.8.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real Filter Topology

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α : Type*}

namespace SuccessiveElimination

/-! ### The pull schedule and the elimination maps -/

/-- The pull schedule of successive elimination: every phase pulls each arm of its active set `S`
once, in the order of `S.toList`. -/
noncomputable def pulls : ℕ → Finset α → List α := fun _ S ↦ S.toList

lemma pulls_apply (r : ℕ) (S : Finset α) : pulls r S = S.toList := (rfl)

@[simp]
lemma length_pulls (r : ℕ) (S : Finset α) : (pulls r S).length = #S := by
  rw [pulls_apply, length_toList]

/-- Every phase of successive elimination pulls each active arm once, and no other arm. -/
@[simp]
lemma count_pulls [DecidableEq α] (r : ℕ) (S : Finset α) (a : α) :
    (pulls r S).count a = if a ∈ S then 1 else 0 := by
  rw [pulls_apply, ← Multiset.coe_count, coe_toList, Multiset.count_eq_of_nodup S.nodup]
  simp

variable (lcb ucb : (n : ℕ) → Hist Unit α ℝ n → α → ℝ)

open Classical in
/-- The elimination maps of successive elimination, for the lower and upper confidence bounds `lcb`
and `ucb`: given the active set `S` and the history `h` at the end of a phase, keep the arms `a` of
`S` whose upper confidence bound is at least the lower confidence bound of every arm of `S`. -/
noncomputable def elim : ℕ → Finset α → (Σ m, Hist Unit α ℝ m) → Finset α :=
  fun _ S h ↦ {a ∈ S | ∀ b ∈ S, lcb h.1 h.2 b ≤ ucb h.1 h.2 a}

variable {lcb ucb} {r : ℕ} {S : Finset α} {h : Σ m, Hist Unit α ℝ m} {a : α}

@[simp]
lemma mem_elim_iff :
    a ∈ elim lcb ucb r S h ↔ a ∈ S ∧ ∀ b ∈ S, lcb h.1 h.2 b ≤ ucb h.1 h.2 a := by
  rw [elim, mem_filter]

lemma elim_subset : elim lcb ucb r S h ⊆ S := fun _ ha ↦ (mem_elim_iff.1 ha).1

/-- The elimination maps of successive elimination are measurable. -/
lemma measurable_elim [Countable α] [MeasurableSpace α]
    (hlcb : ∀ n a, Measurable fun h ↦ lcb n h a) (hucb : ∀ n a, Measurable fun h ↦ ucb n h a)
    (r : ℕ) (S : Finset α) : Measurable (elim lcb ucb r S) := by
  refine measurable_finset_iff.2 fun a ↦ measurable_sigma fun m ↦ ?_
  simp only [Function.comp_def, mem_elim_iff]
  exact measurable_const.and (Measurable.forall fun b ↦ measurable_const.imp
    (measurableSet_setOfPred.1 (measurableSet_le (hlcb m b) (hucb m a))))

/-! ### The phases of successive elimination -/

open PhasedElimination

variable [Fintype α] [DecidableEq α] {H : ℕ → Σ m, Hist Unit α ℝ m}

/-- At the end of phase `r`, successive elimination keeps the arms active in phase `r` whose upper
confidence bound is at least the lower confidence bound of every arm active in phase `r`. -/
lemma mem_activeSet_succ_iff :
    a ∈ activeSet univ pulls (elim lcb ucb) H (r + 1) ↔
      a ∈ activeSet univ pulls (elim lcb ucb) H r ∧
        ∀ b ∈ activeSet univ pulls (elim lcb ucb) H r,
          lcb (H (phaseStart univ pulls (elim lcb ucb) H (r + 1))).1
              (H (phaseStart univ pulls (elim lcb ucb) H (r + 1))).2 b ≤
            ucb (H (phaseStart univ pulls (elim lcb ucb) H (r + 1))).1
              (H (phaseStart univ pulls (elim lcb ucb) H (r + 1))).2 a := by
  rw [activeSet_succ, inter_eq_right.2 elim_subset, mem_elim_iff]

/-- Phase `r` of successive elimination starts after `∑_{j < r} #S_j` rounds. -/
lemma phaseStart_eq_sum_card (r : ℕ) :
    phaseStart univ pulls (elim lcb ucb) H r =
      ∑ j ∈ range r, #(activeSet univ pulls (elim lcb ucb) H j) := by
  simp only [phaseStart_eq_sum, length_pulls]

variable [Nonempty α] {Ω : Type*} {O : ℕ → Ω → Unit} {X : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {ω : Ω}

/-- If the arms are played by successive elimination, an arm active in phase `r` has been pulled
once in each of the previous phases. -/
lemma pullCount_phaseStart_of_mem (hX : ∀ t, X t ω = armAt univ pulls (elim lcb ucb) H t)
    (ha : a ∈ activeSet univ pulls (elim lcb ucb) H r) :
    pullCount X a (phaseStart univ pulls (elim lcb ucb) H r) ω = r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have ha' := activeSet_succ_subset r ha
    rw [pullCount_phaseStart_succ hX, ih ha', count_pulls, ite_eq_left ha']

/-- If the arms are played by successive elimination, an arm active in phase `r` has been pulled
`r + 1` times at its end. -/
lemma pullCount_phaseStart_succ_of_mem (hX : ∀ t, X t ω = armAt univ pulls (elim lcb ucb) H t)
    (ha : a ∈ activeSet univ pulls (elim lcb ucb) H r) :
    pullCount X a (phaseStart univ pulls (elim lcb ucb) H (r + 1)) ω = r + 1 := by
  rw [pullCount_phaseStart_succ hX, pullCount_phaseStart_of_mem hX ha, count_pulls, ite_eq_left ha]

/-- **A best arm is not eliminated while the confidence intervals hold.** Let `a` be a best arm
for the means `μ`. If the arms are played by successive elimination and at every round the
confidence interval `[lcb, ucb]` of every pulled arm `b` contains `μ_b`, then `a` is active in
every phase. -/
lemma mem_activeSet_of_forall_le
    (hX : ∀ t, X t ω = armAt univ pulls (elim lcb ucb) (fun m ↦ sigmaHistory O X Y m ω) t)
    {μ : α → ℝ} (ha : ∀ b, μ b ≤ μ a)
    (hmem : ∀ n b, pullCount X b n ω ≠ 0 →
      lcb n (history O X Y n ω) b ≤ μ b ∧ μ b ≤ ucb n (history O X Y n ω) b) (r : ℕ) :
    a ∈ activeSet univ pulls (elim lcb ucb) (fun m ↦ sigmaHistory O X Y m ω) r := by
  induction r with
  | zero => rw [activeSet_zero]; exact mem_univ a
  | succ r ih =>
    refine mem_activeSet_succ_iff.2 ⟨ih, fun b hb ↦ ?_⟩
    set t := phaseStart univ pulls (elim lcb ucb) (fun m ↦ sigmaHistory O X Y m ω) (r + 1)
    rw [sigmaHistory_apply t ω]
    have hb0 : pullCount X b t ω ≠ 0 := by
      rw [pullCount_phaseStart_succ_of_mem hX hb]; exact r.succ_ne_zero
    have ha0 : pullCount X a t ω ≠ 0 := by
      rw [pullCount_phaseStart_succ_of_mem hX ih]; exact r.succ_ne_zero
    linarith [(hmem t b hb0).1, (hmem t a ha0).2, ha b]

/-- **Elimination of the suboptimal arms.** Let `a` be a best arm for the means `μ`, and let
`w : ℕ → ℝ` bound the widths of the confidence intervals, in the sense that at every round the
confidence interval `[lcb, ucb]` of every pulled arm `b` contains `μ_b` and has its endpoints within
`w (N_b)` of `μ_b`. If the arms are played by successive elimination, every arm `b` with
`2 w u < μ_a - μ_b` is not active after `u ≠ 0` phases. -/
lemma notMem_activeSet_of_two_mul_lt
    (hX : ∀ t, X t ω = armAt univ pulls (elim lcb ucb) (fun m ↦ sigmaHistory O X Y m ω) t)
    {μ : α → ℝ} {w : ℕ → ℝ} (ha : ∀ b, μ b ≤ μ a)
    (hmem : ∀ n b, pullCount X b n ω ≠ 0 →
      lcb n (history O X Y n ω) b ≤ μ b ∧ μ b ≤ ucb n (history O X Y n ω) b)
    (hw : ∀ n b, pullCount X b n ω ≠ 0 → μ b - w (pullCount X b n ω) ≤ lcb n (history O X Y n ω) b ∧
      ucb n (history O X Y n ω) b ≤ μ b + w (pullCount X b n ω))
    {u : ℕ} (hu0 : u ≠ 0) {b : α} (hu : 2 * w u < μ a - μ b) :
    b ∉ activeSet univ pulls (elim lcb ucb) (fun m ↦ sigmaHistory O X Y m ω) u := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hu0
  intro hb
  have hb' := activeSet_succ_subset r hb
  have ha' := mem_activeSet_of_forall_le hX ha hmem r
  have h_le := (mem_activeSet_succ_iff.1 hb).2 a ha'
  set t := phaseStart univ pulls (elim lcb ucb) (fun m ↦ sigmaHistory O X Y m ω) (r + 1)
  rw [sigmaHistory_apply t ω] at h_le
  have hat := pullCount_phaseStart_succ_of_mem hX ha'
  have hbt := pullCount_phaseStart_succ_of_mem hX hb'
  have h_a := (hw t a (by rw [hat]; exact r.succ_ne_zero)).1
  have h_b := (hw t b (by rw [hbt]; exact r.succ_ne_zero)).2
  rw [hat] at h_a
  rw [hbt] at h_b
  linarith

/-- **Only the best arm is left.** Under the hypotheses of `notMem_activeSet_of_two_mul_lt`, if
`2 w u < μ_a - μ_b` for every arm `b ≠ a`, then `a` is the only active arm after `u ≠ 0`
phases. -/
lemma activeSet_eq_singleton
    (hX : ∀ t, X t ω = armAt univ pulls (elim lcb ucb) (fun m ↦ sigmaHistory O X Y m ω) t)
    {μ : α → ℝ} {w : ℕ → ℝ} (ha : ∀ b, μ b ≤ μ a)
    (hmem : ∀ n b, pullCount X b n ω ≠ 0 →
      lcb n (history O X Y n ω) b ≤ μ b ∧ μ b ≤ ucb n (history O X Y n ω) b)
    (hw : ∀ n b, pullCount X b n ω ≠ 0 → μ b - w (pullCount X b n ω) ≤ lcb n (history O X Y n ω) b ∧
      ucb n (history O X Y n ω) b ≤ μ b + w (pullCount X b n ω))
    {u : ℕ} (hu0 : u ≠ 0) (hu : ∀ b ≠ a, 2 * w u < μ a - μ b) :
    activeSet univ pulls (elim lcb ucb) (fun m ↦ sigmaHistory O X Y m ω) u = {a} := by
  refine eq_singleton_iff_unique_mem.2 ⟨mem_activeSet_of_forall_le hX ha hmem u, fun b hb ↦ ?_⟩
  by_contra hba
  exact notMem_activeSet_of_two_mul_lt hX ha hmem hw hu0 (hu b hba) hb

end SuccessiveElimination

/-! ### Successive elimination -/

section Algorithm

open SuccessiveElimination PhasedElimination

variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  (lcb ucb : (n : ℕ) → Hist Unit α ℝ n → α → ℝ) (hlcb : ∀ n a, Measurable fun h ↦ lcb n h a)
  (hucb : ∀ n a, Measurable fun h ↦ ucb n h a)

/-- **Successive elimination** [EMM02, Section 3] with lower and upper confidence bounds `lcb`
and `ucb`: the phased-elimination algorithm with initial active set `univ`, whose phases pull each
active arm once (`SuccessiveElimination.pulls`) and then eliminate the active arms whose upper
confidence bound is less than the lower confidence bound of some active arm
(`SuccessiveElimination.elim`). It stops when at most one arm is active, and then outputs it. -/
noncomputable def successiveElimination : IdentAlg Unit α ℝ α :=
  phasedElimination univ pulls (elim lcb ucb) (measurable_elim hlcb hucb) (roundRobinOn · 0)

lemma successiveElimination_def : successiveElimination lcb ucb hlcb hucb =
    phasedElimination univ pulls (elim lcb ucb) (measurable_elim hlcb hucb)
      (roundRobinOn · 0) := (rfl)

@[simp]
lemma alg_successiveElimination : (successiveElimination lcb ucb hlcb hucb).alg =
    samplingRule univ pulls (elim lcb ucb) (measurable_elim hlcb hucb) := by
  rw [successiveElimination_def, alg_phasedElimination]

variable [MeasurableSingletonClass α] {lcb ucb hlcb hucb} {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {O : ℕ → Ω → Unit} {X : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {ω : Ω}

/-- **Error probability of successive elimination**, for all confidence bounds. Let `a` be a best
arm for the means `μ`. Along any algorithm-environment sequence of the sampling rule, the
probability that successive elimination stops with an arm other than `a` is at most the
probability that at some round `n`, the confidence interval `[lcb, ucb]` of some pulled arm `b`
does not contain `μ_b`. -/
theorem measureReal_histOutputMeasure_successiveElimination_le [IsProbabilityMeasure P]
    {env : Environment Unit α ℝ}
    (hseq : IsAlgEnvSeq O X Y (successiveElimination lcb ucb hlcb hucb).alg env P)
    {μ : α → ℝ} {a : α} (ha : ∀ b, μ b ≤ μ a) :
    (histOutputMeasure (successiveElimination lcb ucb hlcb hucb) env).real
        {p | p.1 ∈ (successiveElimination lcb ucb hlcb hucb).stopSet ∧ p.2 ∉ ({a} : Set α)} ≤
      P.real {ω | ∃ n b, pullCount X b n ω ≠ 0 ∧
        (ucb n (history O X Y n ω) b < μ b ∨ μ b < lcb n (history O X Y n ω) b)} := by
  rw [alg_successiveElimination] at hseq
  rw [successiveElimination_def, phasedElimination_def]
  refine (measureReal_histOutputMeasure_ofStop_deterministic_le hseq
    (measurableSet_singleton a)).trans
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_))
  filter_upwards [action_ae_all_eq_armAt hseq] with ω hX ⟨n, hn_stop, hn_wrong⟩
  -- Otherwise, `a` is active in every phase, and it is the output.
  by_contra h_con
  simp only [not_exists, not_and, not_or, not_lt] at h_con
  exact hn_wrong (out_activeSet_finalPhase_truncHist_eq (out := fun S ↦ roundRobinOn S 0)
    (fun _ hS ↦ roundRobinOn_mem hS 0) hn_stop
    (mem_activeSet_of_forall_le hX ha fun m b hb ↦ (h_con m b hb).symm))

omit [MeasurableSingletonClass α] in
/-- **Sample complexity of successive elimination along a run.** Let `a` be a best arm for the
means `μ`, and let `w : ℕ → ℝ` and `T : α → ℕ` with `T b ≠ 0` satisfy `2 w (T a) < μ_a - μ_b` and
`2 w (T b) < μ_a - μ_b` for every arm `b ≠ a`. Consider a sequence of actions played by
successive elimination in which at every round, the confidence interval `[lcb, ucb]` of every
pulled arm `b` contains `μ_b` and has its endpoints within `w (N_b)` of `μ_b`. Then successive
elimination stops after at most `∑_b T_b` rounds. -/
theorem stoppingTime_successiveElimination_le {μ : α → ℝ} {a : α} {w : ℕ → ℝ} {T : α → ℕ}
    (ha : ∀ b, μ b ≤ μ a) (hT0 : ∀ b, T b ≠ 0)
    (hT : ∀ b ≠ a, 2 * w (T a) < μ a - μ b ∧ 2 * w (T b) < μ a - μ b)
    (hX : ∀ t, X t ω = armAt univ pulls (elim lcb ucb) (fun m ↦ sigmaHistory O X Y m ω) t)
    (hmem : ∀ n b, pullCount X b n ω ≠ 0 →
      lcb n (history O X Y n ω) b ≤ μ b ∧ μ b ≤ ucb n (history O X Y n ω) b)
    (hw : ∀ n b, pullCount X b n ω ≠ 0 → μ b - w (pullCount X b n ω) ≤ lcb n (history O X Y n ω) b ∧
      ucb n (history O X Y n ω) b ≤ μ b + w (pullCount X b n ω)) :
    (successiveElimination lcb ucb hlcb hucb).stoppingTime O X Y ω ≤ ((∑ b, T b : ℕ) : ℕ∞) := by
  set H := fun m ↦ sigmaHistory O X Y m ω
  -- After `T a` phases only `a` is active, and an arm `b ≠ a` is active in fewer than `T b`
  -- phases.
  have h_single : activeSet univ pulls (elim lcb ucb) H (T a) = {a} :=
    activeSet_eq_singleton hX ha hmem hw (hT0 a) fun b hb ↦ (hT b hb).1
  have h_lt (b : α) (j : ℕ) (hj : j < T a) (hb : b ∈ activeSet univ pulls (elim lcb ucb) H j) :
      j < T b := by
    by_cases hba : b = a
    · exact hba ▸ hj
    by_contra h_le
    exact notMem_activeSet_of_two_mul_lt hX ha hmem hw (hT0 b) (hT b hba).2
      (antitone_activeSet (not_lt.1 h_le) hb)
  rw [successiveElimination_def]
  refine (stoppingTime_phasedElimination_le (r := T a) (by rw [h_single, card_singleton])).trans
    (WithTop.coe_le_coe.2 ?_)
  -- The start of phase `T a` is the number of pairs `(j, b)` with `j < T a` and `b ∈ S_j`.
  rw [phaseStart_eq_sum_card]
  calc ∑ j ∈ range (T a), #(activeSet univ pulls (elim lcb ucb) H j)
      = ∑ j ∈ range (T a), ∑ b, if b ∈ activeSet univ pulls (elim lcb ucb) H j then 1 else 0 := by
        simp
    _ = ∑ b, ∑ j ∈ range (T a), if b ∈ activeSet univ pulls (elim lcb ucb) H j then 1 else 0 :=
      sum_comm
    _ ≤ ∑ b, T b := sum_le_sum fun b _ ↦ by
      rw [sum_boole, Nat.cast_id]
      exact (card_le_card fun j hj ↦ mem_range.2 (h_lt b j (mem_range.1 (mem_filter.1 hj).1)
        (mem_filter.1 hj).2)).trans_eq (card_range _)

end Algorithm

/-! ### Successive elimination for sub-Gaussian arms -/

section Rate

open SuccessiveElimination PhasedElimination

variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Successive elimination with exploration rate `β`** [EMM02, Section 3]: successive elimination
with the confidence bounds `μ̂_a ∓ β(N_a)` after `n` rounds, where `N_a` and `μ̂_a` are the number
of pulls and the empirical mean of the arm `a`. -/
noncomputable def successiveEliminationOfRate (β : ℕ → ℝ) : IdentAlg Unit α ℝ α :=
  successiveElimination (lowerBound fun u _ ↦ β u) (upperBound fun u _ ↦ β u)
    (measurable_lowerBound _) (measurable_upperBound _)

lemma successiveEliminationOfRate_def (β : ℕ → ℝ) :
    successiveEliminationOfRate (α := α) β =
      successiveElimination (lowerBound fun u _ ↦ β u) (upperBound fun u _ ↦ β u)
        (measurable_lowerBound _) (measurable_upperBound _) := (rfl)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {O : ℕ → Ω → Unit} {X : ℕ → Ω → α}
  {Y : ℕ → Ω → ℝ} {β : ℕ → ℝ} {μ : α → ℝ} {ω : Ω}

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- If the empirical means are within `β(N_b)` of the means `μ_b`, the confidence intervals
`μ̂_b ∓ β(N_b)` contain the means and have their endpoints within `2 β(N_b)` of them. -/
lemma SuccessiveElimination.mem_and_le_of_abs_empMean_sub_le
    (hgood : ∀ n b, pullCount X b n ω ≠ 0 →
      |empMean X Y b n ω - μ b| ≤ β (pullCount X b n ω)) {n : ℕ} {b : α}
    (hb : pullCount X b n ω ≠ 0) :
    (lowerBound (fun u _ ↦ β u) n (history O X Y n ω) b ≤ μ b ∧
      μ b ≤ upperBound (fun u _ ↦ β u) n (history O X Y n ω) b) ∧
    (μ b - 2 * β (pullCount X b n ω) ≤ lowerBound (fun u _ ↦ β u) n (history O X Y n ω) b ∧
      upperBound (fun u _ ↦ β u) n (history O X Y n ω) b ≤
        μ b + 2 * β (pullCount X b n ω)) := by
  simp only [lowerBound_def, upperBound_def, ← empMean_eq_empMean',
    ← pullCount_eq_pullCount']
  have h := abs_le.1 (hgood n b hb)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [h.1, h.2]

/-- **Sample complexity of successive elimination with exploration rate `β` along a run.** Let `a`
be a best arm for the means `μ`, and let `T : α → ℕ` with `T b ≠ 0` satisfy `4 β(T a) < μ_a - μ_b`
and `4 β(T b) < μ_a - μ_b` for every arm `b ≠ a`. Consider a sequence of actions played by
successive elimination with exploration rate `β`, in which at every round, the empirical mean of
every pulled arm `b` is within `β(N_b)` of `μ_b`. Then successive elimination stops after at most
`∑_b T_b` rounds. -/
theorem stoppingTime_successiveEliminationOfRate_le {a : α} {T : α → ℕ}
    (ha : ∀ b, μ b ≤ μ a) (hT0 : ∀ b, T b ≠ 0)
    (hT : ∀ b ≠ a, 4 * β (T a) < μ a - μ b ∧ 4 * β (T b) < μ a - μ b)
    (hX : ∀ t, X t ω = armAt univ pulls (elim (lowerBound fun u _ ↦ β u)
      (upperBound fun u _ ↦ β u)) (fun m ↦ sigmaHistory O X Y m ω) t)
    (hgood : ∀ n b, pullCount X b n ω ≠ 0 →
      |empMean X Y b n ω - μ b| ≤ β (pullCount X b n ω)) :
    (successiveEliminationOfRate β).stoppingTime O X Y ω ≤ ((∑ b, T b : ℕ) : ℕ∞) :=
  stoppingTime_successiveElimination_le (w := fun u ↦ 2 * β u) ha hT0
    (fun b hb ↦ ⟨by linarith [(hT b hb).1], by linarith [(hT b hb).2]⟩) hX
    (fun _ _ hb ↦ (mem_and_le_of_abs_empMean_sub_le hgood hb).1)
    (fun _ _ hb ↦ (mem_and_le_of_abs_empMean_sub_le hgood hb).2)

variable [IsProbabilityMeasure P] {ν₀ : Kernel α ℝ} [IsMarkovKernel ν₀] {σ2 : ℝ≥0} {δ : ℝ}

/-- **Sample complexity of successive elimination for sub-Gaussian arms** [EMM02, Theorem 3;
EMM06, Theorem 8]. Let the arms of `ν₀` be σ²-sub-Gaussian with `σ² ≠ 0`, let `0 < δ ≤ K` and
`β = subgaussianRate σ2 (log (K / δ))`. Let `a` be an arm and `T : α → ℕ` with `T b ≠ 0` satisfy
`4 β(T a) < μ_a - μ_b` and `4 β(T b) < μ_a - μ_b` for every arm `b ≠ a` (so that `a` is the best
arm). Along every algorithm-environment sequence of the sampling rule, successive elimination with
exploration rate `β` stops after more than `∑_b T_b` rounds with probability at most `δ`. -/
theorem measureReal_sum_lt_stoppingTime_successiveEliminationOfRate_le
    (hseq : IsAlgEnvSeq O X Y
      (successiveEliminationOfRate (subgaussianRate σ2 (log (Fintype.card α / δ)))).alg
      (Environment.bandit ν₀) P)
    (hσ2 : σ2 ≠ 0) (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν₀ a)[id]) σ2 (ν₀ a))
    (hδ : 0 < δ) (hδK : δ ≤ Fintype.card α) {a : α} {T : α → ℕ} (hT0 : ∀ b, T b ≠ 0)
    (hT : ∀ b ≠ a,
      4 * subgaussianRate σ2 (log (Fintype.card α / δ)) (T a) < (ν₀ a)[id] - (ν₀ b)[id] ∧
        4 * subgaussianRate σ2 (log (Fintype.card α / δ)) (T b) < (ν₀ a)[id] - (ν₀ b)[id]) :
    P.real {ω | ((∑ b, T b : ℕ) : WithTop ℕ) < (successiveEliminationOfRate
      (subgaussianRate σ2 (log (Fintype.card α / δ)))).stoppingTime O X Y ω} ≤ δ := by
  -- The arm `a` is a best arm, as `0 ≤ 4 β(T a) < μ_a - μ_b` for every arm `b ≠ a`.
  have ha (b : α) : (ν₀ b)[id] ≤ (ν₀ a)[id] := by
    rcases eq_or_ne b a with rfl | hba
    · exact le_rfl
    · linarith [(hT b hba).1, subgaussianRate_nonneg σ2 (log (Fintype.card α / δ)) (T a)]
  refine le_trans ?_
    (measureReal_exists_exists_subgaussianRate_lt_abs_empMean_sub_le hseq hσ2 hν hδ hδK)
  rw [successiveEliminationOfRate_def, alg_successiveElimination] at hseq
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [action_ae_all_eq_armAt hseq] with ω hX hω
  -- On the event where all the confidence intervals hold, the algorithm stops in time.
  by_contra h_good
  simp only [not_exists, not_and, not_lt] at h_good
  exact (stoppingTime_successiveEliminationOfRate_le ha hT0 hT hX h_good).not_gt hω

/-- The number of pulls `max ⌈64 σ² Δ⁻² (y + 2 log (256 σ² Δ⁻²))⌉₊ 1`, of order
`σ² Δ⁻² (y + log (σ² / Δ²))`, after which the exploration rate `β = subgaussianRate σ2 y`
satisfies `4 β < Δ` (`SuccessiveElimination.four_mul_subgaussianRate_lt`). With `y = log (K / δ)`
and `Δ` the gap of an arm, successive elimination pulls that arm at most this number of times on
the event where all the confidence intervals hold. -/
noncomputable def SuccessiveElimination.pullBound (σ2 : ℝ≥0) (y Δ : ℝ) : ℕ :=
  max ⌈64 * σ2 / Δ ^ 2 * (y + 2 * log (256 * σ2 / Δ ^ 2))⌉₊ 1

lemma SuccessiveElimination.pullBound_def (σ2 : ℝ≥0) (y Δ : ℝ) :
    SuccessiveElimination.pullBound σ2 y Δ =
      max ⌈64 * σ2 / Δ ^ 2 * (y + 2 * log (256 * σ2 / Δ ^ 2))⌉₊ 1 := (rfl)

lemma SuccessiveElimination.one_le_pullBound (σ2 : ℝ≥0) (y Δ : ℝ) :
    1 ≤ SuccessiveElimination.pullBound σ2 y Δ :=
  le_max_right _ _

/-- After `u ≥ pullBound σ2 y Δ` pulls, four times the exploration rate `subgaussianRate σ2 y` is
less than `Δ > 0`. -/
lemma SuccessiveElimination.four_mul_subgaussianRate_lt {σ2 : ℝ≥0} {y Δ : ℝ} (hΔ : 0 < Δ) {u : ℕ}
    (hu : SuccessiveElimination.pullBound σ2 y Δ ≤ u) :
    4 * subgaussianRate σ2 y u < Δ := by
  have hu' : 64 * (σ2 : ℝ) / Δ ^ 2 * (y + 2 * log (256 * σ2 / Δ ^ 2)) ≤ u :=
    (Nat.le_ceil _).trans (Nat.cast_le.2 ((le_max_left _ _).trans hu))
  have h := subgaussianRate_lt (σ2 := σ2) (y := y) (u := u) (div_pos hΔ four_pos) (by
    rw [show 4 * (σ2 : ℝ) / (Δ / 4) ^ 2 = 64 * σ2 / Δ ^ 2 by field_simp; ring,
      show 16 * (σ2 : ℝ) / (Δ / 4) ^ 2 = 256 * σ2 / Δ ^ 2 by field_simp; ring]
    exact hu')
  linarith

/-- **Sample complexity of successive elimination for sub-Gaussian arms, in closed form**
[EMM02, Theorem 3; EMM06, Theorem 8]. Let the arms of `ν₀` be σ²-sub-Gaussian with `σ² ≠ 0`, let
`0 < δ ≤ K`, and let `a` be an arm and `Δ > 0` with `μ_a - μ_b ≥ Δ` for every arm `b ≠ a`, so that
`a` is the unique best arm and `Δ` is at most the smallest gap. Along every algorithm-environment
sequence of the sampling rule, successive elimination with exploration rate
`β = subgaussianRate σ2 (log (K / δ))` stops after more than `N(Δ) + ∑_{b ≠ a} N(μ_a - μ_b)`
rounds with probability at most `δ`, where `N = pullBound σ2 (log (K / δ))` and
`N(d) = max ⌈64 σ² d⁻² (log (K / δ) + 2 log (256 σ² d⁻²))⌉₊ 1`. With `Δ` the smallest gap, this is
the bound `∑_b c σ² Δ_b⁻² log (K / (δ Δ_b))` of [EMM02] in a scale-invariant form, the gap of the
best arm being the smallest gap: for `σ² = 1` and `d ≤ 16`,
`N(d) ≤ 256 d⁻² log (16 K / (δ d)) + 1`. -/
theorem measureReal_pullBound_add_sum_lt_stoppingTime_successiveEliminationOfRate_le
    (hseq : IsAlgEnvSeq O X Y
      (successiveEliminationOfRate (subgaussianRate σ2 (log (Fintype.card α / δ)))).alg
      (Environment.bandit ν₀) P)
    (hσ2 : σ2 ≠ 0) (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν₀ a)[id]) σ2 (ν₀ a))
    (hδ : 0 < δ) (hδK : δ ≤ Fintype.card α) {a : α} {Δ : ℝ} (hΔ : 0 < Δ)
    (ha : ∀ b ≠ a, Δ ≤ (ν₀ a)[id] - (ν₀ b)[id]) :
    P.real {ω | ((SuccessiveElimination.pullBound σ2 (log (Fintype.card α / δ)) Δ +
      ∑ b ∈ univ.erase a, SuccessiveElimination.pullBound σ2 (log (Fintype.card α / δ))
        ((ν₀ a)[id] - (ν₀ b)[id]) : ℕ) : WithTop ℕ) < (successiveEliminationOfRate
      (subgaussianRate σ2 (log (Fintype.card α / δ)))).stoppingTime O X Y ω} ≤ δ := by
  set y := log (Fintype.card α / δ)
  -- The number of pulls of each arm: `N(Δ)` for `a` and `N(μ_a - μ_b)` for `b ≠ a`.
  set T : α → ℕ := fun b ↦ if b = a then SuccessiveElimination.pullBound σ2 y Δ
    else SuccessiveElimination.pullBound σ2 y ((ν₀ a)[id] - (ν₀ b)[id]) with hT_def
  have h_sum : SuccessiveElimination.pullBound σ2 y Δ +
      ∑ b ∈ univ.erase a, SuccessiveElimination.pullBound σ2 y ((ν₀ a)[id] - (ν₀ b)[id]) =
      ∑ b, T b := by
    rw [← add_sum_erase univ T (mem_univ a)]
    congr 1
    · simp [hT_def]
    · exact sum_congr rfl fun b hb ↦ by simp [hT_def, (mem_erase.1 hb).1]
  rw [h_sum]
  refine measureReal_sum_lt_stoppingTime_successiveEliminationOfRate_le hseq hσ2 hν hδ hδK (a := a)
    (fun b ↦ by
      simp only [hT_def]
      split_ifs <;> exact Nat.one_le_iff_ne_zero.1 (SuccessiveElimination.one_le_pullBound _ _ _))
    fun b hb ↦ ⟨?_, ?_⟩
  -- Four times the rate after `N(Δ)` pulls is less than `Δ`, and after `N(μ_a - μ_b)` pulls it is
  -- less than the gap of `b`.
  · simp only [hT_def, ↓reduceIte]
    exact (SuccessiveElimination.four_mul_subgaussianRate_lt hΔ le_rfl).trans_le (ha b hb)
  · simp only [hT_def, hb, ↓reduceIte]
    exact SuccessiveElimination.four_mul_subgaussianRate_lt (hΔ.trans_le (ha b hb)) le_rfl

omit [IsProbabilityMeasure P] in
/-- **Error probability of successive elimination for sub-Gaussian arms** [EMM02, Theorem 3;
EMM06, Theorem 8]. Let the arms of `ν₀` be σ²-sub-Gaussian with `σ² ≠ 0`, let `a` be its unique
best arm and let `0 < δ ≤ K`. Successive elimination with exploration rate
`subgaussianRate σ2 (log (K / δ))` does not stop, or stops with an arm other than `a`, with
probability at most `δ`. -/
theorem measureReal_histOutputMeasure_successiveEliminationOfRate_notMem_or_le (hσ2 : σ2 ≠ 0)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν₀ a)[id]) σ2 (ν₀ a)) (hδ : 0 < δ)
    (hδK : δ ≤ Fintype.card α) {a : α} (ha : ∀ b ≠ a, (ν₀ b)[id] < (ν₀ a)[id]) :
    (histOutputMeasure (successiveEliminationOfRate
        (subgaussianRate σ2 (log (Fintype.card α / δ)))) (Environment.bandit ν₀)).real
      {p | p.1 ∉ (successiveEliminationOfRate
        (subgaussianRate σ2 (log (Fintype.card α / δ)))).stopSet ∨ p.2 ∉ ({a} : Set α)} ≤ δ := by
  set β := subgaussianRate σ2 (log (Fintype.card α / δ))
  have ha' (b : α) : (ν₀ b)[id] ≤ (ν₀ a)[id] := by
    rcases eq_or_ne b a with rfl | hba
    exacts [le_rfl, (ha b hba).le]
  -- A number of pulls `u ≠ 0` such that `4 β(u) < μ_a - μ_b` for every arm `b ≠ a`.
  obtain ⟨T₀, hT₀⟩ : ∃ T₀, ∀ u ≥ T₀, ∀ b, b ≠ a → 4 * β u < (ν₀ a)[id] - (ν₀ b)[id] := by
    refine eventually_atTop.1 (eventually_all.2 fun b ↦ ?_)
    by_cases hba : b = a
    · exact .of_forall fun _ h ↦ absurd hba h
    · have hpos : 0 < ((ν₀ a)[id] - (ν₀ b)[id]) / 4 := by linarith [ha b hba]
      have h_lim : Tendsto β atTop (𝓝 0) := tendsto_subgaussianRate_atTop σ2 _
      filter_upwards [(tendsto_order.1 h_lim).2 _ hpos] with u hu _
      linarith
  have hu := hT₀ (max T₀ 1) (le_max_left _ _)
  have hu0 : max T₀ 1 ≠ 0 := (Nat.lt_of_lt_of_le one_pos (le_max_right T₀ 1)).ne'
  -- The bound in the canonical model of the sampling rule.
  set alg := samplingRule (univ : Finset α) pulls
    (elim (lowerBound fun u _ ↦ β u) (upperBound fun u _ ↦ β u))
    (measurable_elim (measurable_lowerBound _) (measurable_upperBound _))
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν₀)
  have hP : IsProbabilityMeasure (trajMeasure alg (Environment.bandit ν₀)) :=
    inferInstanceAs (IsProbabilityMeasure (trajMeasure _ _))
  refine le_trans ?_
    (measureReal_exists_exists_subgaussianRate_lt_abs_empMean_sub_le hseq hσ2 hν hδ hδK)
  rw [successiveEliminationOfRate_def, successiveElimination_def, phasedElimination_def]
  refine (measureReal_histOutputMeasure_ofStop_deterministic_notMem_or_le hseq
    (measurableSet_singleton a)).trans
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_))
  filter_upwards [action_ae_all_eq_armAt hseq] with ω hX hω
  -- On the event where all the confidence intervals hold, `a` is active in every phase and the
  -- only active arm after `max T₀ 1` phases, so the algorithm stops with the answer `a`.
  by_contra h_good
  simp only [not_exists, not_and, not_lt] at h_good
  have hmem := fun n b (hb : pullCount IT.action b n ω ≠ 0) ↦
    (mem_and_le_of_abs_empMean_sub_le (O := IT.obs) h_good hb).1
  have h_act := mem_activeSet_of_forall_le hX ha' hmem
  rcases hω with h_never | ⟨n, h_stop, h_wrong⟩
  · have h_single := activeSet_eq_singleton hX ha' hmem
      (fun _ _ hb ↦ (mem_and_le_of_abs_empMean_sub_le (O := IT.obs) h_good hb).2) hu0
      (w := fun u ↦ 2 * β u) fun b hb ↦ by linarith [hu b hb]
    have h_card : ∃ r, #(activeSet univ pulls
        (elim (lowerBound fun u _ ↦ β u) (upperBound fun u _ ↦ β u))
        (fun m ↦ sigmaHistory IT.obs IT.action IT.feedback m ω) r) ≤ 1 :=
      ⟨_, by rw [h_single, card_singleton]⟩
    exact h_never _ ((stopRule_congr fun m hm ↦ truncHist_mk_history_of_le hm ω).2
      (stopRule_phaseStart_finalPhase h_card))
  · exact h_wrong (out_activeSet_finalPhase_truncHist_eq (out := fun S ↦ roundRobinOn S 0)
      (fun _ hS ↦ roundRobinOn_mem hS 0) h_stop h_act)

/-- **Successive elimination is `δ`-correct** for best arm identification with σ²-sub-Gaussian
arms [EMM02, Theorem 3; EMM06, Theorem 8]. For `σ² ≠ 0` and `0 < δ ≤ K`, on every bandit whose
arms are σ²-sub-Gaussian and which has a unique best arm, successive elimination with exploration
rate `subgaussianRate σ2 (log (K / δ))` stops and outputs the best arm with probability at least
`1 - δ`. -/
theorem isDeltaCorrect_successiveEliminationOfRate (hσ2 : σ2 ≠ 0) (hδ : 0 < δ)
    (hδK : δ ≤ Fintype.card α) :
    ((baiTask (lawBandit (α := α)) lawMean).restrict
      (Set.univ.pi fun _ ↦ subgaussianLaws σ2)).IsDeltaCorrect (successiveEliminationOfRate
        (subgaussianRate σ2 (log (Fintype.card α / δ)))) δ := by
  refine IdentTask.isDeltaCorrect_iff.2 fun θ hθ ↦ ?_
  rw [IdentTask.M_restrict, M_baiTask] at hθ
  obtain ⟨⟨a, ha⟩, hθ⟩ := hθ
  simp only [IdentTask.ν_restrict, ν_baiTask, IdentTask.correct_restrict,
    (correct_baiTask_eq_singleton_iff _ _).2 ha]
  simp only [lawMean_eq_integral_lawBandit] at ha
  exact measureReal_histOutputMeasure_successiveEliminationOfRate_notMem_or_le hσ2
    (fun b ↦ by simpa only [lawMean_eq_integral_lawBandit] using mem_pi_subgaussianLaws_iff.1 hθ b)
    hδ hδK ha

end Rate

end LMLExplore.Identification
