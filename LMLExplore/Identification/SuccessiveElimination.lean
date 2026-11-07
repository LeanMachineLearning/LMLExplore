/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.IndexAlgorithm
public import LMLExplore.Identification.ConfidenceBound
public import LMLExplore.Identification.Task.RealLaws
public import LMLExplore.SequentialLearning.SubGaussianDeviation

/-!
# Successive elimination

Successive elimination [EMM02, EMM06] is a fixed-confidence algorithm for best arm identification.
It keeps a set of *active* arms, initially all the arms, samples the active arms in turn, and
eliminates an arm `a` as soon as some arm `b` has a lower confidence bound larger than the upper
confidence bound of `a`. It stops when at most one arm is active, and outputs it.

If the confidence intervals of all the arms contain their means at all rounds, a best arm `a⋆` is
never eliminated, so successive elimination outputs `a⋆` whenever it stops. Moreover, an arm `a`
with gap `Δ_a = μ_{a⋆} - μ_a > 0` is sampled while it is active, and the active arms are sampled
in turn, so `a⋆` has been pulled at least as often as `a` when `a` is sampled. If the widths of the
intervals after `u` pulls are at most `w u`, the arm `a` is then not eliminated by `a⋆` only if
`Δ_a ≤ w (N_a) + w (N_{a⋆})`: the arm `a` is pulled at most `T_a` times, for any `T_a` beyond which
`w u + w v < Δ_a` for all `T_a ≤ u ≤ v`. The arm `a⋆` is pulled at most `T_{a⋆}` times, for the
same condition with the smallest gap. The algorithm stops after at most `∑_a T_a` rounds.

For σ²-sub-Gaussian arms and the confidence intervals `μ̂_a ∓ β(N_a)` with
`β(u) = √(2 σ² (log (2 u (u + 1)) + log (K / δ)) / u)`, the intervals of all the arms contain
their means at all rounds with probability at least `1 - δ` ([LS, Lemma 33.8] and a union bound
over the `K` arms). Hence successive elimination is `δ`-correct for best arm identification, and
it stops after at most `∑_a T_a` rounds with probability at least `1 - δ`, where `w = 2 β`
[EMM02, Theorem 3; EMM06, Theorem 8]. Solving `4 β(u) < Δ_a` for all `u ≥ T_a` shows that `T_a`
can be taken equal to `N(Δ_a) = max ⌈64 σ² Δ_a⁻² (log (K / δ) + 2 log (256 σ² Δ_a⁻²))⌉₊ 1`, of
order `σ² Δ_a⁻² log (K / (δ Δ_a))` for `σ² = 1`, with the smallest gap in place of the gap `0` of
the best arm.

## Main definitions

In the namespace `LMLExplore.Identification`:

* `SuccessiveElimination.IsEliminated lcb ucb n h a`: the arm `a` has been eliminated after `n`
  rounds with history `h`, for the lower and upper confidence bounds `lcb` and `ucb`.
* `SuccessiveElimination.index lcb ucb n h`: the sampling index, `-N_a` for an active arm `a` and
  `⊥` for an eliminated arm, so that the sampled arm is a least pulled active arm.
* `SuccessiveElimination.StopRule lcb ucb n h`: at most one arm is active.
* `successiveElimination lcb ucb hlcb hucb`: successive elimination as an identification
  algorithm.
* `successiveEliminationOfRate β`: successive elimination with the confidence bounds
  `μ̂_a ∓ β(N_a)`.
* `SuccessiveElimination.pullBound σ2 y Δ`: the number of pulls
  `max ⌈64 σ² Δ⁻² (y + 2 log (256 σ² Δ⁻²))⌉₊ 1` after which `4 subgaussianRate σ2 y < Δ`.

## Main statements

* `measureReal_histOutputMeasure_successiveElimination_le`: for all confidence bounds, the
  probability that successive elimination stops with an arm other than a best arm `a⋆` is at most
  the probability that the confidence interval of some pulled arm misses its mean at some round.
* `exists_stoppingTime_successiveElimination_eq`: along a run in which the confidence intervals
  contain the means and have widths at most `w`, successive elimination stops after at most
  `∑_a T_a` rounds and outputs the best arm.
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

[EMM02] samples the active arms in phases and eliminates arms at the end of each phase. Here the
sampled arm is the active arm of largest index, that is a least pulled active arm, ties being
broken by LML's `argmax`, and eliminations are checked after every round. The active arms are
therefore sampled in turn, as in a phase, and the analysis is the same. An arm is only eliminated
by an arm when both have been pulled, so that unpulled arms are active, and an eliminated arm stays
eliminated. The confidence bounds `μ̂_a ∓ β(N_a)` of `successiveEliminationOfRate` are the bounds
`lowerBound` and `upperBound`, also used by LUCB, for a rate that does not depend on the round.
The rate `subgaussianRate σ2 (log (K / δ))` and the probability that the confidence intervals of
all the arms contain their means at all rounds
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

/-! ### Elimination, sampling index and stopping rule -/

section Rule

variable [DecidableEq α] (lcb ucb : (n : ℕ) → Hist Unit α ℝ n → α → ℝ)

/-- The arm `b` *eliminates* the arm `a` after `n` rounds with history `h`, for the lower and upper
confidence bounds `lcb` and `ucb`: both arms have been pulled and the upper confidence bound of `a`
is less than the lower confidence bound of `b`. -/
def Eliminates (n : ℕ) (h : Hist Unit α ℝ n) (b a : α) : Prop :=
  pullCount' n h a ≠ 0 ∧ pullCount' n h b ≠ 0 ∧ ucb n h a < lcb n h b

lemma eliminates_iff {n : ℕ} {h : Hist Unit α ℝ n} {b a : α} :
    Eliminates lcb ucb n h b a ↔
      pullCount' n h a ≠ 0 ∧ pullCount' n h b ≠ 0 ∧ ucb n h a < lcb n h b := Iff.rfl

/-- The arm `a` is *eliminated* after `n` rounds with history `h`: some arm eliminated it after
some number `m ≤ n` of rounds, for the prefix of length `m` of `h`. -/
def IsEliminated (n : ℕ) (h : Hist Unit α ℝ n) (a : α) : Prop :=
  ∃ m : Fin (n + 1), ∃ b,
    Eliminates lcb ucb m (fun i ↦ h (Fin.castLE (Nat.lt_succ_iff.1 m.isLt) i)) b a

lemma isEliminated_iff {n : ℕ} {h : Hist Unit α ℝ n} {a : α} :
    IsEliminated lcb ucb n h a ↔ ∃ m : Fin (n + 1), ∃ b,
      Eliminates lcb ucb m (fun i ↦ h (Fin.castLE (Nat.lt_succ_iff.1 m.isLt) i)) b a := Iff.rfl

variable {lcb ucb} in
/-- An arm eliminated by some arm after `n` rounds is eliminated after `n` rounds. -/
lemma IsEliminated.of_eliminates {n : ℕ} {h : Hist Unit α ℝ n} {a b : α}
    (hba : Eliminates lcb ucb n h b a) : IsEliminated lcb ucb n h a :=
  ⟨Fin.last n, b, hba⟩

/-- After `n` rounds of a sequence of actions and feedbacks, the arm `a` is eliminated iff some arm
eliminated it after some number `m ≤ n` of rounds. -/
lemma isEliminated_history_iff {Ω : Type*} {O : ℕ → Ω → Unit} {X : ℕ → Ω → α}
    {Y : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω} {a : α} :
    IsEliminated lcb ucb n (history O X Y n ω) a ↔
      ∃ m ≤ n, ∃ b, Eliminates lcb ucb m (history O X Y m ω) b a :=
  -- The prefix of length `m` of the history of the first `n` rounds is the history of the first
  -- `m` rounds (`history_eq_comp_history`).
  ⟨fun ⟨m, b, hm⟩ ↦ ⟨m, Nat.lt_succ_iff.1 m.isLt, b, hm⟩,
    fun ⟨m, hm, b, hb⟩ ↦ ⟨⟨m, Nat.lt_succ_of_le hm⟩, b, hb⟩⟩

open Classical in
/-- The sampling index of successive elimination after `n` rounds with history `h`: `-N_a` for an
arm `a` that is not eliminated, where `N_a` is its number of pulls, and `⊥` for an eliminated arm.
An arm of largest index is a least pulled arm among those that are not eliminated. -/
noncomputable def index (n : ℕ) (h : Hist Unit α ℝ n) (a : α) : EReal :=
  if IsEliminated lcb ucb n h a then ⊥ else -(pullCount' n h a : EReal)

variable {lcb ucb} {n : ℕ} {h : Hist Unit α ℝ n} {a : α}

lemma index_of_isEliminated (ha : IsEliminated lcb ucb n h a) : index lcb ucb n h a = ⊥ := by
  simp [index, ha]

lemma index_of_not_isEliminated (ha : ¬ IsEliminated lcb ucb n h a) :
    index lcb ucb n h a = -(pullCount' n h a : EReal) := by
  simp [index, ha]

/-- The index of an arm is not `⊥` iff the arm is not eliminated. -/
lemma bot_lt_index_iff : ⊥ < index lcb ucb n h a ↔ ¬ IsEliminated lcb ucb n h a := by
  by_cases ha : IsEliminated lcb ucb n h a
  · simp [index_of_isEliminated ha, ha]
  · simp only [index_of_not_isEliminated ha, ha, not_false_eq_true, iff_true]
    exact bot_lt_iff_ne_bot.2 (by rw [Ne, EReal.neg_eq_bot_iff]; exact EReal.natCast_ne_top _)

variable (lcb ucb) in
/-- The stopping rule of successive elimination after `n` rounds with history `h`: at most one arm
is not eliminated. -/
def StopRule (n : ℕ) (h : Hist Unit α ℝ n) : Prop :=
  ∀ a b, ¬ IsEliminated lcb ucb n h a → ¬ IsEliminated lcb ucb n h b → a = b

lemma stopRule_iff : StopRule lcb ucb n h ↔
    ∀ a b, ¬ IsEliminated lcb ucb n h a → ¬ IsEliminated lcb ucb n h b → a = b := Iff.rfl

section Argmax

variable [Fintype α] [Nonempty α]

/-- The arm of largest index has the largest index. -/
lemma index_le_index_argmax (b : α) :
    index lcb ucb n h b ≤ index lcb ucb n h (argmax (index lcb ucb n h)) :=
  isMaxOn_argmax (index lcb ucb n h) (Set.mem_univ b)

/-- If some arm is not eliminated, the arm of largest index is not eliminated. -/
lemma not_isEliminated_argmax_index {b : α} (hb : ¬ IsEliminated lcb ucb n h b) :
    ¬ IsEliminated lcb ucb n h (argmax (index lcb ucb n h)) :=
  bot_lt_index_iff.1 ((bot_lt_index_iff.2 hb).trans_le (index_le_index_argmax b))

/-- The arm of largest index has been pulled at most as often as any arm that is not
eliminated. -/
lemma pullCount'_argmax_index_le {b : α} (hb : ¬ IsEliminated lcb ucb n h b) :
    pullCount' n h (argmax (index lcb ucb n h)) ≤ pullCount' n h b := by
  have h_le := index_le_index_argmax (lcb := lcb) (ucb := ucb) (h := h) b
  rw [index_of_not_isEliminated hb, index_of_not_isEliminated (not_isEliminated_argmax_index hb),
    EReal.neg_le_neg_iff] at h_le
  exact_mod_cast h_le

/-- If the stopping rule holds and the arm of largest index is not `a`, then `a` is
eliminated. -/
lemma isEliminated_of_stopRule (hstop : StopRule lcb ucb n h)
    (ha : argmax (index lcb ucb n h) ≠ a) : IsEliminated lcb ucb n h a := by
  by_contra hna
  exact ha (hstop _ a (not_isEliminated_argmax_index hna) hna)

/-- **One round of successive elimination.** Let `a` be a best arm for the means `μ`, let
`w : ℕ → ℝ` bound the widths of the confidence intervals, in the sense that
`μ_b - w (N_b) ≤ lcb n h b` and `ucb n h b ≤ μ_b + w (N_b)` for every pulled arm `b`, and let `T`
satisfy `w u + w v < μ_a - μ_b` for every arm `b ≠ a` and all `min (T a) (T b) ≤ u ≤ v`. If `a`
is not eliminated and the stopping rule does not hold after `n` rounds with history `h`, then the
arm `c` of largest index has been pulled fewer than `T c` times. -/
lemma pullCount'_argmax_index_lt {μ : α → ℝ} {w : ℕ → ℝ} {T : α → ℕ}
    (hT : ∀ b ≠ a, ∀ u v, min (T a) (T b) ≤ u → u ≤ v → w u + w v < μ a - μ b)
    (hT0 : ∀ b, T b ≠ 0)
    (hw : ∀ b, pullCount' n h b ≠ 0 →
      μ b - w (pullCount' n h b) ≤ lcb n h b ∧ ucb n h b ≤ μ b + w (pullCount' n h b))
    (ha : ¬ IsEliminated lcb ucb n h a) (hstop : ¬ StopRule lcb ucb n h) :
    pullCount' n h (argmax (index lcb ucb n h)) < T (argmax (index lcb ucb n h)) := by
  set c := argmax (index lcb ucb n h)
  have hc : ¬ IsEliminated lcb ucb n h c := not_isEliminated_argmax_index ha
  -- An arm `d` that is not eliminated by `e` while both are pulled has
  -- `μ_e - μ_d ≤ w (N_e) + w (N_d)`.
  have h_gap (d e : α) (hd : ¬ IsEliminated lcb ucb n h d) (hd0 : pullCount' n h d ≠ 0)
      (he0 : pullCount' n h e ≠ 0) :
      μ e - μ d ≤ w (pullCount' n h e) + w (pullCount' n h d) := by
    have h_not : ¬ ucb n h d < lcb n h e := fun hlt ↦ hd (.of_eliminates ⟨hd0, he0, hlt⟩)
    linarith [(hw e he0).1, (hw d hd0).2, not_lt.1 h_not]
  rcases Nat.eq_zero_or_pos (pullCount' n h c) with h0 | hpos
  · rw [h0]
    exact Nat.pos_of_ne_zero (hT0 c)
  by_contra hTc
  rw [not_lt] at hTc
  by_cases hca : c = a
  · -- Another arm `b` is not eliminated, and it has been pulled at least as often as `a`.
    obtain ⟨b, hb, hba⟩ : ∃ b, ¬ IsEliminated lcb ucb n h b ∧ b ≠ a := by
      simp only [stopRule_iff, not_forall] at hstop
      obtain ⟨d, e, hd, he, hde⟩ := hstop
      by_cases hda : d = a
      · exact ⟨e, he, fun hea ↦ hde (hda.trans hea.symm)⟩
      · exact ⟨d, hd, hda⟩
    have hcb : pullCount' n h c ≤ pullCount' n h b := pullCount'_argmax_index_le hb
    rw [hca] at hTc hcb hpos
    linarith [h_gap b a hb (by omega) hpos.ne', hT b hba _ _ ((min_le_left _ _).trans hTc) hcb]
  · -- The arm `a` has been pulled at least as often as `c`.
    have hca' : pullCount' n h c ≤ pullCount' n h a := pullCount'_argmax_index_le ha
    linarith [h_gap c a hc hpos.ne' (by omega), hT c hca _ _ ((min_le_right _ _).trans hTc) hca']

end Argmax

end Rule

/-! ### Measurability -/

section Measurability

variable [DecidableEq α] [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {lcb ucb : (n : ℕ) → Hist Unit α ℝ n → α → ℝ} (hlcb : ∀ n a, Measurable fun h ↦ lcb n h a)
  (hucb : ∀ n a, Measurable fun h ↦ ucb n h a)
include hlcb hucb

omit [Countable α] in
lemma measurable_eliminates (n : ℕ) (b a : α) :
    Measurable fun h : Hist Unit α ℝ n ↦ Eliminates lcb ucb n h b a := by
  have h0 (c : α) : Measurable fun h : Hist Unit α ℝ n ↦ pullCount' n h c ≠ 0 :=
    (measurableSet_setOfPred.1
      ((measurableSet_singleton 0).preimage (measurable_pullCount' n c))).not
  exact (h0 a).and ((h0 b).and (measurableSet_setOfPred.1 (measurableSet_lt (hucb n a) (hlcb n b))))

lemma measurable_isEliminated (n : ℕ) (a : α) :
    Measurable fun h : Hist Unit α ℝ n ↦ IsEliminated lcb ucb n h a :=
  Measurable.exists fun m ↦ Measurable.exists fun b ↦ (measurable_eliminates hlcb hucb m b a).comp
    (Measurable.of_eval fun _ ↦ measurable_pi_apply _)

lemma measurable_index (n : ℕ) : Measurable (index lcb ucb n) := by
  refine Measurable.of_eval fun a ↦ ?_
  simp only [index]
  exact Measurable.ite (measurableSet_setOfPred.2 (measurable_isEliminated hlcb hucb n a))
    measurable_const
    ((measurable_of_countable fun k : ℕ ↦ -(k : EReal)).comp (measurable_pullCount' n a))

lemma measurableSet_stopRule (n : ℕ) : MeasurableSet {h | StopRule lcb ucb n h} :=
  measurableSet_setOfPred.2 <| Measurable.forall fun a ↦ Measurable.forall fun b ↦
    (measurable_isEliminated hlcb hucb n a).not.imp
      ((measurable_isEliminated hlcb hucb n b).not.imp measurable_const)

end Measurability

end SuccessiveElimination

/-! ### Successive elimination -/

section Algorithm

variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  (lcb ucb : (n : ℕ) → Hist Unit α ℝ n → α → ℝ) (hlcb : ∀ n a, Measurable fun h ↦ lcb n h a)
  (hucb : ∀ n a, Measurable fun h ↦ ucb n h a)

/-- **Successive elimination** [EMM02, Section 3] with lower and upper confidence bounds `lcb`
and `ucb`. After `n` rounds with history `h`, it samples the arm of largest index
`SuccessiveElimination.index lcb ucb n h`, a least pulled arm among those that are not eliminated.
It stops when at most one arm is not eliminated (`SuccessiveElimination.StopRule`), and then
outputs the arm of largest index. -/
noncomputable def successiveElimination : IdentAlg Unit α ℝ α :=
  ofStop (Bandits.indexAlgorithm (fun n x ↦ SuccessiveElimination.index lcb ucb n x.1)
      fun n ↦ (SuccessiveElimination.measurable_index hlcb hucb n).comp measurable_fst)
    (SuccessiveElimination.StopRule lcb ucb)
    (SuccessiveElimination.measurableSet_stopRule hlcb hucb)
    fun n ↦ Kernel.deterministic (fun h ↦ argmax (SuccessiveElimination.index lcb ucb n h))
      (measurable_argmax.comp (SuccessiveElimination.measurable_index hlcb hucb n))

lemma successiveElimination_def : successiveElimination lcb ucb hlcb hucb =
    ofStop (Bandits.indexAlgorithm (fun n x ↦ SuccessiveElimination.index lcb ucb n x.1)
        fun n ↦ (SuccessiveElimination.measurable_index hlcb hucb n).comp measurable_fst)
      (SuccessiveElimination.StopRule lcb ucb)
      (SuccessiveElimination.measurableSet_stopRule hlcb hucb)
      fun n ↦ Kernel.deterministic (fun h ↦ argmax (SuccessiveElimination.index lcb ucb n h))
        (measurable_argmax.comp (SuccessiveElimination.measurable_index hlcb hucb n)) := (rfl)

@[simp]
lemma alg_successiveElimination : (successiveElimination lcb ucb hlcb hucb).alg =
    Bandits.indexAlgorithm (fun n x ↦ SuccessiveElimination.index lcb ucb n x.1)
      fun n ↦ (SuccessiveElimination.measurable_index hlcb hucb n).comp measurable_fst := by
  rw [successiveElimination_def, alg_ofStop]

@[simp]
lemma mem_stopSet_successiveElimination {h : Σ n, Hist Unit α ℝ n} :
    h ∈ (successiveElimination lcb ucb hlcb hucb).stopSet ↔
      SuccessiveElimination.StopRule lcb ucb h.1 h.2 := by
  rw [successiveElimination_def, mem_stopSet_ofStop]

@[simp]
lemma output_successiveElimination (h : Σ n, Hist Unit α ℝ n) :
    (successiveElimination lcb ucb hlcb hucb).output h =
      Measure.dirac (argmax (SuccessiveElimination.index lcb ucb h.1 h.2)) := by
  rw [successiveElimination_def, output_ofStop, Kernel.sigma_apply, Kernel.deterministic_apply]

variable {lcb ucb hlcb hucb} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}

/-- **The run lemma of successive elimination**: along every algorithm-environment sequence of its
sampling rule, almost surely, the arm played at every round `n` is the arm of largest index for
the history of the first `n` rounds. -/
lemma ae_action_eq_argmax_index [IsFiniteMeasure P] {env : Environment Unit α ℝ}
    (hseq : IsAlgEnvSeq O X Y (successiveElimination lcb ucb hlcb hucb).alg env P) :
    ∀ᵐ ω ∂P, ∀ n, X n ω = argmax (SuccessiveElimination.index lcb ucb n (history O X Y n ω)) := by
  rw [alg_successiveElimination] at hseq
  exact Bandits.IndexAlgorithm.action_ae_all_eq hseq

/-- **Not stopping, or stopping with a wrong output.** Along any algorithm-environment sequence of
the sampling rule, the probability that successive elimination does not stop or stops with an
output outside `s` is at most the probability that the stopping rule never holds or that at some
round `n`, the stopping rule holds and the arm of largest index is not in `s`. -/
lemma measureReal_histOutputMeasure_successiveElimination_notMem_or_le
    [IsProbabilityMeasure P] {env : Environment Unit α ℝ}
    (hseq : IsAlgEnvSeq O X Y (successiveElimination lcb ucb hlcb hucb).alg env P) {s : Set α}
    (hs : MeasurableSet s) :
    (histOutputMeasure (successiveElimination lcb ucb hlcb hucb) env).real
        {p | p.1 ∉ (successiveElimination lcb ucb hlcb hucb).stopSet ∨ p.2 ∉ s} ≤
      P.real {ω | (∀ n, ¬ SuccessiveElimination.StopRule lcb ucb n (history O X Y n ω)) ∨
        ∃ n, SuccessiveElimination.StopRule lcb ucb n (history O X Y n ω) ∧
          argmax (SuccessiveElimination.index lcb ucb n (history O X Y n ω)) ∉ s} := by
  rw [alg_successiveElimination] at hseq
  rw [successiveElimination_def]
  exact measureReal_histOutputMeasure_ofStop_deterministic_notMem_or_le hseq hs

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **A best arm is not eliminated while the confidence intervals hold.** Let `a` be a best arm
for the means `μ`. If at every round the confidence interval `[lcb, ucb]` of every pulled arm `b`
contains `μ_b`, then `a` is never eliminated. -/
lemma SuccessiveElimination.not_isEliminated_history {ω : Ω} {μ : α → ℝ} {a : α}
    (ha : ∀ b, μ b ≤ μ a)
    (hmem : ∀ n b, pullCount X b n ω ≠ 0 →
      lcb n (history O X Y n ω) b ≤ μ b ∧ μ b ≤ ucb n (history O X Y n ω) b) (n : ℕ) :
    ¬ IsEliminated lcb ucb n (history O X Y n ω) a := by
  rw [isEliminated_history_iff]
  rintro ⟨m, -, b, hpa, hpb, hlt⟩
  rw [← pullCount_eq_pullCount'] at hpa hpb
  linarith [(hmem m a hpa).2, (hmem m b hpb).1, ha b]

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
  rw [successiveElimination_def]
  refine (measureReal_histOutputMeasure_ofStop_deterministic_le hseq
    (measurableSet_singleton a)).trans (measureReal_mono fun ω ⟨n, hn_stop, hn_wrong⟩ ↦ ?_)
  -- Otherwise, `a` is not eliminated, and it is the output.
  by_contra h_con
  simp only [Set.mem_ofPred_eq, not_exists, not_and, not_or, not_lt] at h_con
  exact SuccessiveElimination.not_isEliminated_history ha (fun m b hb ↦ (h_con m b hb).symm) n
    (SuccessiveElimination.isEliminated_of_stopRule hn_stop hn_wrong)

/-- **Sample complexity of successive elimination along a run.** Let `a` be a best arm for the
means `μ`, and let `w : ℕ → ℝ` and `T : α → ℕ` with `T b ≠ 0` satisfy `w u + w v < μ_a - μ_b` for
every arm `b ≠ a` and all `min (T a) (T b) ≤ u ≤ v`. Consider a sequence of actions in
which the arm played at every round is the arm of largest index, and in which at every round, the
confidence interval `[lcb, ucb]` of every pulled arm `b` contains `μ_b` and has its endpoints within
`w (N_b)` of `μ_b`. Then successive elimination stops after at most `∑_b T_b` rounds and outputs
`a`. -/
theorem exists_stoppingTime_successiveElimination_eq {ω : Ω} {μ : α → ℝ} {a : α} {w : ℕ → ℝ}
    {T : α → ℕ} (ha : ∀ b, μ b ≤ μ a)
    (hT : ∀ b ≠ a, ∀ u v, min (T a) (T b) ≤ u → u ≤ v → w u + w v < μ a - μ b)
    (hT0 : ∀ b, T b ≠ 0)
    (hX : ∀ n, X n ω = argmax (SuccessiveElimination.index lcb ucb n (history O X Y n ω)))
    (hmem : ∀ n b, pullCount X b n ω ≠ 0 →
      lcb n (history O X Y n ω) b ≤ μ b ∧ μ b ≤ ucb n (history O X Y n ω) b)
    (hw : ∀ n b, pullCount X b n ω ≠ 0 → μ b - w (pullCount X b n ω) ≤ lcb n (history O X Y n ω) b ∧
      ucb n (history O X Y n ω) b ≤ μ b + w (pullCount X b n ω)) :
    ∃ n ≤ ∑ b, T b, (successiveElimination lcb ucb hlcb hucb).stoppingTime O X Y ω = n ∧
      argmax (SuccessiveElimination.index lcb ucb n (history O X Y n ω)) = a := by
  have ha_act := SuccessiveElimination.not_isEliminated_history ha hmem
  -- Before the stopping rule holds, the arm played at round `n` has been pulled fewer than
  -- `T` times.
  have h_step (n : ℕ) (hn : ¬ SuccessiveElimination.StopRule lcb ucb n (history O X Y n ω)) :
      pullCount X (X n ω) n ω < T (X n ω) := by
    rw [hX n, pullCount_eq_pullCount' (O := O) (R' := Y)]
    refine SuccessiveElimination.pullCount'_argmax_index_lt hT hT0 (fun b hb ↦ ?_)
      (ha_act n) hn
    rw [← pullCount_eq_pullCount'] at hb ⊢
    exact hw n b hb
  -- As long as the stopping rule does not hold, every arm `b` has been pulled at most `T b` times.
  have h_le (n : ℕ)
      (hn : ∀ t < n, ¬ SuccessiveElimination.StopRule lcb ucb t (history O X Y t ω)) (b : α) :
      pullCount X b n ω ≤ T b := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pullCount_add_one]
      split_ifs with hXb
      · have h := h_step n (hn n (lt_add_one n))
        rw [hXb] at h
        omega
      · simpa using ih fun t ht ↦ hn t (ht.trans (lt_add_one n))
  -- Hence the stopping rule holds after at most `∑ b, T b` rounds.
  obtain ⟨n, hn, h_stop⟩ : ∃ n ≤ ∑ b, T b,
      SuccessiveElimination.StopRule lcb ucb n (history O X Y n ω) := by
    by_contra h_con
    simp only [not_exists, not_and] at h_con
    have h_sum : ∑ b, pullCount X b (∑ b, T b + 1) ω ≤ ∑ b, T b :=
      sum_le_sum fun b _ ↦ h_le _ (fun t ht ↦ h_con t (Nat.lt_succ_iff.1 ht)) b
    rw [sum_pullCount] at h_sum
    omega
  have hτ : (successiveElimination lcb ucb hlcb hucb).stoppingTime O X Y ω ≤ n :=
    IdentAlg.stoppingTime_le_of_mem_stopSet
      ((mem_stopSet_successiveElimination lcb ucb hlcb hucb).2 h_stop)
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hτ)
  rw [← hk] at hτ
  have hkn : k ≤ n := WithTop.coe_le_coe.1 hτ
  have hk_stop := (IdentAlg.stoppingTime_eq_coe_iff.1 hk.symm).1
  rw [mem_stopSet_successiveElimination] at hk_stop
  refine ⟨k, hkn.trans hn, hk.symm, ?_⟩
  by_contra hne
  exact ha_act k (SuccessiveElimination.isEliminated_of_stopRule hk_stop hne)

end Algorithm

/-! ### Successive elimination for sub-Gaussian arms -/

section Rate

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
be a best arm for the means `μ`, and let `T : α → ℕ` with `T b ≠ 0` satisfy
`2 β(u) + 2 β(v) < μ_a - μ_b` for every arm `b ≠ a` and all `min (T a) (T b) ≤ u ≤ v`. Consider
a sequence of actions in which the arm played at every round is the arm of largest index, and in
which at every round, the empirical mean of every pulled arm `b` is within `β(N_b)` of `μ_b`.
Then successive elimination stops after at most `∑_b T_b` rounds and outputs `a`. -/
theorem exists_stoppingTime_successiveEliminationOfRate_eq {a : α} {T : α → ℕ}
    (ha : ∀ b, μ b ≤ μ a)
    (hT : ∀ b ≠ a, ∀ u v, min (T a) (T b) ≤ u → u ≤ v → 2 * β u + 2 * β v < μ a - μ b)
    (hT0 : ∀ b, T b ≠ 0)
    (hX : ∀ n, X n ω = argmax (SuccessiveElimination.index (lowerBound fun u _ ↦ β u)
      (upperBound fun u _ ↦ β u) n (history O X Y n ω)))
    (hgood : ∀ n b, pullCount X b n ω ≠ 0 →
      |empMean X Y b n ω - μ b| ≤ β (pullCount X b n ω)) :
    ∃ n ≤ ∑ b, T b, (successiveEliminationOfRate β).stoppingTime O X Y ω = n ∧
      argmax (SuccessiveElimination.index (lowerBound fun u _ ↦ β u)
        (upperBound fun u _ ↦ β u) n (history O X Y n ω)) = a :=
  exists_stoppingTime_successiveElimination_eq (w := fun u ↦ 2 * β u) ha hT hT0 hX
    (fun _ _ hb ↦ (SuccessiveElimination.mem_and_le_of_abs_empMean_sub_le hgood hb).1)
    (fun _ _ hb ↦ (SuccessiveElimination.mem_and_le_of_abs_empMean_sub_le hgood hb).2)

variable [IsProbabilityMeasure P] {ν₀ : Kernel α ℝ} [IsMarkovKernel ν₀] {σ2 : ℝ≥0} {δ : ℝ}

/-- **Sample complexity of successive elimination for sub-Gaussian arms** [EMM02, Theorem 3;
EMM06, Theorem 8]. Let the arms of `ν₀` be σ²-sub-Gaussian with `σ² ≠ 0`, let `0 < δ ≤ K` and
`β = subgaussianRate σ2 (log (K / δ))`. Let `a` be an arm and `T : α → ℕ` with `T b ≠ 0` satisfy
`2 β(u) + 2 β(v) < μ_a - μ_b` for every arm `b ≠ a` and all `min (T a) (T b) ≤ u ≤ v` (so that
`a` is the best arm). Along every algorithm-environment sequence of the sampling rule, successive
elimination with exploration rate `β` stops after more than `∑_b T_b` rounds with probability at
most `δ`. -/
theorem measureReal_sum_lt_stoppingTime_successiveEliminationOfRate_le
    (hseq : IsAlgEnvSeq O X Y
      (successiveEliminationOfRate (subgaussianRate σ2 (log (Fintype.card α / δ)))).alg
      (Environment.bandit ν₀) P)
    (hσ2 : σ2 ≠ 0) (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν₀ a)[id]) σ2 (ν₀ a))
    (hδ : 0 < δ) (hδK : δ ≤ Fintype.card α) {a : α} {T : α → ℕ}
    (hT : ∀ b ≠ a, ∀ u v, min (T a) (T b) ≤ u → u ≤ v →
      2 * subgaussianRate σ2 (log (Fintype.card α / δ)) u +
        2 * subgaussianRate σ2 (log (Fintype.card α / δ)) v < (ν₀ a)[id] - (ν₀ b)[id])
    (hT0 : ∀ b, T b ≠ 0) :
    P.real {ω | ((∑ b, T b : ℕ) : WithTop ℕ) < (successiveEliminationOfRate
      (subgaussianRate σ2 (log (Fintype.card α / δ)))).stoppingTime O X Y ω} ≤ δ := by
  -- The arm `a` is a best arm, as `0 ≤ 4 β(T a) < μ_a - μ_b` for every arm `b ≠ a`.
  have ha (b : α) : (ν₀ b)[id] ≤ (ν₀ a)[id] := by
    rcases eq_or_ne b a with rfl | hba
    · exact le_rfl
    · have h := hT b hba (T a) (T a) (min_le_left _ _) le_rfl
      linarith [subgaussianRate_nonneg σ2 (log (Fintype.card α / δ)) (T a)]
  refine le_trans ?_
    (measureReal_exists_exists_subgaussianRate_lt_abs_empMean_sub_le hseq hσ2 hν hδ hδK)
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [ae_action_eq_argmax_index hseq] with ω hX hω
  -- On the event where all the confidence intervals hold, the algorithm stops in time.
  by_contra h_good
  simp only [not_exists, not_and, not_lt] at h_good
  obtain ⟨n, hn, hτ, -⟩ :=
    exists_stoppingTime_successiveEliminationOfRate_eq ha hT hT0 hX h_good
  rw [hτ] at hω
  have h_lt : ∑ b, T b < n := WithTop.coe_lt_coe.1 hω
  omega

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
    (fun b hb u v hu huv ↦ ?_) fun b ↦ by
      simp only [hT_def]
      split_ifs <;> exact Nat.one_le_iff_ne_zero.1 (SuccessiveElimination.one_le_pullBound _ _ _)
  -- After `min (T a) (T b)` pulls, four times the rate is less than the gap of `b`.
  have h_lt {w : ℕ} (hw : min (T a) (T b) ≤ w) :
      4 * subgaussianRate σ2 y w < (ν₀ a)[id] - (ν₀ b)[id] := by
    rcases min_le_iff.1 hw with hw | hw
    · simp only [hT_def, ↓reduceIte] at hw
      exact (SuccessiveElimination.four_mul_subgaussianRate_lt hΔ hw).trans_le (ha b hb)
    · simp only [hT_def, hb, ↓reduceIte] at hw
      exact SuccessiveElimination.four_mul_subgaussianRate_lt (hΔ.trans_le (ha b hb)) hw
  linarith [h_lt hu, h_lt (hu.trans huv)]

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
  -- A number of pulls `T₀` beyond which `4 β(u) < μ_a - μ_b` for every arm `b ≠ a`.
  obtain ⟨T₀, hT₀⟩ : ∃ T₀, ∀ u ≥ T₀, ∀ b, b ≠ a → 4 * β u < (ν₀ a)[id] - (ν₀ b)[id] := by
    refine eventually_atTop.1 (eventually_all.2 fun b ↦ ?_)
    by_cases hba : b = a
    · exact .of_forall fun _ h ↦ absurd hba h
    · have hpos : 0 < ((ν₀ a)[id] - (ν₀ b)[id]) / 4 := by linarith [ha b hba]
      have h_lim : Tendsto β atTop (𝓝 0) := tendsto_subgaussianRate_atTop σ2 _
      filter_upwards [(tendsto_order.1 h_lim).2 _ hpos] with u hu _
      linarith
  have hT : ∀ b ≠ a, ∀ u v, min (max T₀ 1) (max T₀ 1) ≤ u → u ≤ v →
      2 * β u + 2 * β v < (ν₀ a)[id] - (ν₀ b)[id] :=
    fun b hb u v hu huv ↦ by
      rw [min_self] at hu
      have h1 := hT₀ u (le_of_max_le_left hu) b hb
      have h2 := hT₀ v ((le_of_max_le_left hu).trans huv) b hb
      linarith
  -- The bound in the canonical model of the sampling rule.
  have hseq := IT.isAlgEnvSeq_trajMeasure (successiveEliminationOfRate β).alg
    (Environment.bandit ν₀)
  have hP : IsProbabilityMeasure
      (trajMeasure (successiveEliminationOfRate β).alg (Environment.bandit ν₀)) :=
    inferInstanceAs (IsProbabilityMeasure (trajMeasure _ _))
  refine (measureReal_histOutputMeasure_successiveElimination_notMem_or_le hseq
    (measurableSet_singleton a)).trans (le_trans ?_
    (measureReal_exists_exists_subgaussianRate_lt_abs_empMean_sub_le hseq hσ2 hν hδ hδK))
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [ae_action_eq_argmax_index hseq] with ω hX hω
  -- On the event where all the confidence intervals hold, the algorithm stops with the answer `a`.
  by_contra h_good
  simp only [not_exists, not_and, not_lt] at h_good
  rcases hω with h_never | ⟨n, h_stop, h_wrong⟩
  · obtain ⟨n, -, hτ, -⟩ := exists_stoppingTime_successiveEliminationOfRate_eq
      (T := fun _ ↦ max T₀ 1) ha' hT
      (fun _ ↦ (Nat.lt_of_lt_of_le one_pos (le_max_right T₀ 1)).ne') hX h_good
    exact h_never n ((mem_stopSet_successiveElimination _ _ _ _).1
      (IdentAlg.stoppingTime_eq_coe_iff.1 hτ).1)
  · exact SuccessiveElimination.not_isEliminated_history ha'
      (fun _ _ hb ↦ (SuccessiveElimination.mem_and_le_of_abs_empMean_sub_le h_good hb).1) n
      (SuccessiveElimination.isEliminated_of_stopRule h_stop h_wrong)

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
