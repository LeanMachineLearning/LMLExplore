/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.FixedBudget
public import LMLExplore.SequentialLearning.StoppedHistory
public import Mathlib.Data.List.GetD

/-!
# Phased elimination

A *phased-elimination* algorithm keeps a set of *active* answers and proceeds in phases. Phase `r`
starts with an active set `S_r`, plays a list `pulls r S_r` of arms in the order of the list, then
replaces the active set by `S_{r+1} = S_r ∩ elim r S_r h`, where `h` is the history at the end of
the phase. The data are a type `ℐ` of answers, an initial active set `S₀ : Finset ℐ`, the *pull
schedule* `pulls : ℕ → Finset ℐ → List α` (the number of pulls of the arm `a` in phase `r` is
`(pulls r S).count a`) and measurable *elimination maps*
`elim : ℕ → Finset ℐ → (Σ m, Hist 𝓞 α 𝓨 m) → Finset ℐ`. The fixed-confidence version stops as
soon as at most one answer is active; the fixed-budget version stops after a given number `R` of
phases. Both then output `out S` for the final active set `S`, where `out : Finset ℐ → ℐ` is
meant to choose an element of `S` when `S` is nonempty.

Successive elimination [EMM02, EMM06] (each phase pulls every active arm once), median elimination
[EMM02] (each phase pulls every active arm the same number of times and keeps the better half),
successive rejects [ABM10] and sequential halving [KKS13] are of this form, with `ℐ = α`; so is
the elimination of answers with optimal designs of linear identification [FJJR19].

The phases are computed from the histories of the first `m` rounds, given by a function
`H : ℕ → Σ m, Hist 𝓞 α 𝓨 m`: the history of the first `m` rounds of a trajectory, or the
prefixes `truncHist m ⟨t, h⟩` of a history `h` of `t` rounds. The phase state after `r` phases,
the start of phase `r` and the active set during phase `r` (`phaseState`, `phaseStart`,
`activeSet`) only use the histories `H m` with `m` at most the start of phase `r`
(`phaseState_congr`), so that computing them from the prefixes of a history of `t` rounds or along
the whole trajectory gives the same result for the phases that start by round `t`.

## Main definitions

In the namespace `LMLExplore.Identification.PhasedElimination`:

* `phaseState S₀ pulls elim H r`, `phaseStart S₀ pulls elim H r`, `activeSet S₀ pulls elim H r`:
  the pair (start of phase `r`, active set of phase `r`), and its two components.
* `phaseOf S₀ pulls elim H t`: the phase containing the round `t`.
* `armAt S₀ pulls elim H t`: the arm played at round `t`.
* `finalPhase S₀ pulls elim H`: the first phase with at most one active answer.
* `samplingRule S₀ pulls elim helim`: the sampling rule of phased elimination, the deterministic
  algorithm that plays `armAt` at every round.

In the namespace `LMLExplore.Identification`:

* `phasedElimination S₀ pulls elim helim out`: the fixed-confidence version, which stops at the
  start of the first phase with at most one active answer `S` and outputs `out S`.
* `phasedEliminationFixedBudget S₀ pulls elim helim out R`: the fixed-budget version, which stops
  after `R` phases and outputs `out S_R`.

## Main statements

* `PhasedElimination.armAt_phaseStart_add`: round `j` of phase `r` plays the `j`-th arm of the
  list `pulls r S_r`.
* `PhasedElimination.action_ae_eq_armAt`, `PhasedElimination.pullCount_phaseStart_succ`: along
  every run of the sampling rule, the arm played at round `t` is `armAt` for the history of the
  run, and phase `r` pulls the arm `a` exactly `(pulls r S_r).count a` times.
* `stoppingTime_phasedElimination_eq`, `stoppingTime_phasedElimination_eq_top`: the stopping time
  of the fixed-confidence version is the start of the first phase with at most one active answer,
  the total number `∑ j < r, (pulls j S_j).length` of pulls of the phases before it
  (`PhasedElimination.phaseStart_eq_sum`), and it is infinite if there is no such phase.
* `measure_histOutputMeasure_phasedElimination_le`: the survival bound. If `out` chooses an element
  of every nonempty set and `i ∈ S₀`, the probability that the fixed-confidence version stops
  with an output other than `i` is at most `∑_r P(1 < #S_r, i ∈ S_r, i ∉ S_{r+1})`, the sum over
  the phases of the probability that `i` is eliminated at the end of the phase.
* `stoppingTime_phasedEliminationFixedBudget`, `isFixedBudget_phasedEliminationFixedBudget`: the
  fixed-budget version stops at the start of phase `R`, and it is a fixed-budget algorithm when
  the length of each phase depends on its index only.
* `measure_outputMeasure_phasedEliminationFixedBudget_le`: the survival bound of the fixed-budget
  version: if at most one answer is active after `R` phases, the probability of an output other
  than `i ∈ S₀` is at most `∑_{r < R} P(i ∈ S_r, i ∉ S_{r+1})`.

## References

* [EMM02] E. Even-Dar, S. Mannor and Y. Mansour, *PAC bounds for multi-armed bandit and Markov
  decision processes*, COLT 2002.
* [EMM06] E. Even-Dar, S. Mannor and Y. Mansour, *Action elimination and stopping conditions for
  the multi-armed bandit and reinforcement learning problems*, JMLR 7 (2006).
* [ABM10] J.-Y. Audibert, S. Bubeck and R. Munos, *Best arm identification in multi-armed
  bandits*, COLT 2010.
* [KKS13] Z. Karnin, T. Koren and O. Somekh, *Almost optimal exploration in multi-armed bandits*,
  ICML 2013.
* [FJJR19] T. Fiez, L. Jain, K. Jamieson and L. Ratliff, *Sequential experimental design for
  transductive linear bandits*, NeurIPS 2019.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset
open scoped ENNReal

namespace LMLExplore.Identification

namespace PhasedElimination

variable {𝓞 α 𝓨 ℐ : Type*} [DecidableEq ℐ] (S₀ : Finset ℐ) (pulls : ℕ → Finset ℐ → List α)
  (elim : ℕ → Finset ℐ → (Σ m, Hist 𝓞 α 𝓨 m) → Finset ℐ)

/-! ### The phases -/

/-- The state of phased elimination after `r` phases, computed from the histories `H m` of the
first `m` rounds: the round at which phase `r` starts and the active set during phase `r`. Phase
`r` plays the arms of the list `pulls r S_r`, and the history at its end decides the next active
set `S_r ∩ elim r S_r h`. -/
def phaseState (H : ℕ → Σ m, Hist 𝓞 α 𝓨 m) : ℕ → ℕ × Finset ℐ
  | 0 => (0, S₀)
  | r + 1 => ((phaseState H r).1 + (pulls r (phaseState H r).2).length,
      (phaseState H r).2 ∩
        elim r (phaseState H r).2 (H ((phaseState H r).1 + (pulls r (phaseState H r).2).length)))

/-- The round at which phase `r` starts. -/
def phaseStart (H : ℕ → Σ m, Hist 𝓞 α 𝓨 m) (r : ℕ) : ℕ := (phaseState S₀ pulls elim H r).1

/-- The active set during phase `r`. -/
def activeSet (H : ℕ → Σ m, Hist 𝓞 α 𝓨 m) (r : ℕ) : Finset ℐ :=
  (phaseState S₀ pulls elim H r).2

variable {S₀ pulls elim} {H H' : ℕ → Σ m, Hist 𝓞 α 𝓨 m}

lemma phaseState_eq (r : ℕ) :
    phaseState S₀ pulls elim H r = (phaseStart S₀ pulls elim H r, activeSet S₀ pulls elim H r) :=
  (rfl)

@[simp]
lemma phaseStart_zero : phaseStart S₀ pulls elim H 0 = 0 := (rfl)

@[simp]
lemma activeSet_zero : activeSet S₀ pulls elim H 0 = S₀ := (rfl)

lemma phaseStart_succ (r : ℕ) :
    phaseStart S₀ pulls elim H (r + 1) =
      phaseStart S₀ pulls elim H r + (pulls r (activeSet S₀ pulls elim H r)).length := (rfl)

lemma activeSet_succ (r : ℕ) :
    activeSet S₀ pulls elim H (r + 1) = activeSet S₀ pulls elim H r ∩
      elim r (activeSet S₀ pulls elim H r) (H (phaseStart S₀ pulls elim H (r + 1))) := (rfl)

lemma phaseState_succ (r : ℕ) :
    phaseState S₀ pulls elim H (r + 1) =
      ((phaseState S₀ pulls elim H r).1 + (pulls r (phaseState S₀ pulls elim H r).2).length,
        (phaseState S₀ pulls elim H r).2 ∩ elim r (phaseState S₀ pulls elim H r).2
          (H ((phaseState S₀ pulls elim H r).1 +
            (pulls r (phaseState S₀ pulls elim H r).2).length))) := (rfl)

lemma activeSet_succ_subset (r : ℕ) :
    activeSet S₀ pulls elim H (r + 1) ⊆ activeSet S₀ pulls elim H r := by
  rw [activeSet_succ]
  exact inter_subset_left

lemma antitone_activeSet : Antitone (activeSet S₀ pulls elim H) :=
  antitone_nat_of_succ_le activeSet_succ_subset

lemma activeSet_subset (r : ℕ) : activeSet S₀ pulls elim H r ⊆ S₀ :=
  antitone_activeSet (Nat.zero_le r)

lemma monotone_phaseStart : Monotone (phaseStart S₀ pulls elim H) :=
  monotone_nat_of_le_succ fun r ↦ by rw [phaseStart_succ]; exact Nat.le_add_right _ _

/-- Phase `r` starts after the pulls of the previous phases. -/
lemma phaseStart_eq_sum (r : ℕ) :
    phaseStart S₀ pulls elim H r =
      ∑ j ∈ range r, (pulls j (activeSet S₀ pulls elim H j)).length := by
  induction r with
  | zero => simp
  | succ r ih => rw [phaseStart_succ, ih, sum_range_succ]

/-! ### Dependence on the histories -/

/-- The state after `r` phases only depends on the histories of the first `m` rounds for `m` at
most the start of phase `r`. -/
lemma phaseState_congr {N : ℕ} (hH : ∀ m ≤ N, H m = H' m) {r : ℕ}
    (hr : phaseStart S₀ pulls elim H r ≤ N) :
    phaseState S₀ pulls elim H r = phaseState S₀ pulls elim H' r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have h_le : phaseStart S₀ pulls elim H r ≤ N :=
      (monotone_phaseStart (Nat.le_succ r)).trans hr
    rw [phaseState_succ, phaseState_succ, ← ih h_le]
    rw [phaseStart_succ] at hr
    simp only [phaseStart, activeSet] at hr
    rw [hH _ hr]

lemma phaseStart_congr {N : ℕ} (hH : ∀ m ≤ N, H m = H' m) {r : ℕ}
    (hr : phaseStart S₀ pulls elim H r ≤ N) :
    phaseStart S₀ pulls elim H r = phaseStart S₀ pulls elim H' r := by
  rw [phaseStart, phaseStart, phaseState_congr hH hr]

lemma activeSet_congr {N : ℕ} (hH : ∀ m ≤ N, H m = H' m) {r : ℕ}
    (hr : phaseStart S₀ pulls elim H r ≤ N) :
    activeSet S₀ pulls elim H r = activeSet S₀ pulls elim H' r := by
  rw [activeSet, activeSet, phaseState_congr hH hr]

/-- The start of phase `r + 1` only depends on the state after `r` phases. -/
lemma phaseStart_succ_congr {N : ℕ} (hH : ∀ m ≤ N, H m = H' m) {r : ℕ}
    (hr : phaseStart S₀ pulls elim H r ≤ N) :
    phaseStart S₀ pulls elim H (r + 1) = phaseStart S₀ pulls elim H' (r + 1) := by
  rw [phaseStart_succ, phaseStart_succ, phaseStart_congr hH hr, activeSet_congr hH hr]

/-- Whether phase `r` starts after round `t` only depends on the histories of the first `m ≤ t`
rounds. -/
lemma lt_phaseStart_congr {t : ℕ} (hH : ∀ m ≤ t, H m = H' m) {r : ℕ} :
    t < phaseStart S₀ pulls elim H r ↔ t < phaseStart S₀ pulls elim H' r := by
  have hH' : ∀ m ≤ t, H' m = H m := fun m hm ↦ (hH m hm).symm
  constructor
  · intro h
    by_contra h'
    exact h.not_ge ((phaseStart_congr hH' (not_lt.1 h')).symm ▸ not_lt.1 h')
  · intro h
    by_contra h'
    exact h.not_ge ((phaseStart_congr hH (not_lt.1 h')) ▸ not_lt.1 h')

lemma phaseStart_eq_congr {t : ℕ} (hH : ∀ m ≤ t, H m = H' m) {r : ℕ} :
    phaseStart S₀ pulls elim H r = t ↔ phaseStart S₀ pulls elim H' r = t := by
  by_cases h : phaseStart S₀ pulls elim H r ≤ t
  · rw [phaseStart_congr hH h]
  · have h' : t < phaseStart S₀ pulls elim H' r := (lt_phaseStart_congr hH).1 (not_le.1 h)
    exact ⟨fun h'' ↦ absurd h''.le h, fun h'' ↦ absurd h''.le h'.not_ge⟩

/-! ### The phase of a round and the arm it plays -/

variable (S₀ pulls elim) in
open scoped Classical in
/-- The phase containing the round `t`: the first phase `r` whose next phase starts after `t`
(`0` if every phase starts by round `t`, so that the rounds from `t` on are in no phase). -/
noncomputable def phaseOf (H : ℕ → Σ m, Hist 𝓞 α 𝓨 m) (t : ℕ) : ℕ :=
  Nat.find (p := fun r ↦ t < phaseStart S₀ pulls elim H (r + 1) ∨
    ∀ j, phaseStart S₀ pulls elim H (j + 1) ≤ t) <| by
    by_cases h : ∃ r, t < phaseStart S₀ pulls elim H (r + 1)
    · exact h.imp fun _ ↦ Or.inl
    · exact ⟨0, Or.inr fun j ↦ not_lt.1 fun hj ↦ h ⟨j, hj⟩⟩

variable (S₀ pulls elim) in
/-- The phase containing the round `t` starts by round `t`. -/
lemma phaseStart_phaseOf_le (H : ℕ → Σ m, Hist 𝓞 α 𝓨 m) (t : ℕ) :
    phaseStart S₀ pulls elim H (phaseOf S₀ pulls elim H t) ≤ t := by
  classical
  rw [phaseOf]
  set r := Nat.find (p := fun r ↦ t < phaseStart S₀ pulls elim H (r + 1) ∨
    ∀ j, phaseStart S₀ pulls elim H (j + 1) ≤ t) _ with hr
  rcases Nat.eq_zero_or_eq_succ_pred r with h0 | hs
  · rw [h0]; exact Nat.zero_le t
  · have h_min := Nat.find_min (p := fun r ↦ t < phaseStart S₀ pulls elim H (r + 1) ∨
      ∀ j, phaseStart S₀ pulls elim H (j + 1) ≤ t) _ (m := r - 1) (by omega)
    rw [hs]
    push Not at h_min
    exact h_min.1

/-- The phase containing a round `t` with `S_r ≤ t < S_{r+1}`, for the starts `S_r` of the phases,
is `r`. -/
lemma phaseOf_eq {t r : ℕ} (h₁ : phaseStart S₀ pulls elim H r ≤ t)
    (h₂ : t < phaseStart S₀ pulls elim H (r + 1)) : phaseOf S₀ pulls elim H t = r := by
  classical
  rw [phaseOf, Nat.find_eq_iff]
  refine ⟨Or.inl h₂, fun j hj ↦ ?_⟩
  push Not
  exact ⟨(monotone_phaseStart (Nat.succ_le_of_lt hj)).trans h₁, r, h₂⟩

/-- The phase containing the round `t` only depends on the histories of the first `m ≤ t`
rounds. -/
lemma phaseOf_congr {t : ℕ} (hH : ∀ m ≤ t, H m = H' m) :
    phaseOf S₀ pulls elim H t = phaseOf S₀ pulls elim H' t := by
  classical
  simp only [phaseOf, lt_phaseStart_congr hH, ← not_lt]

section Arm

variable (S₀ pulls elim) in
/-- The arm played at round `t` by phased elimination: in phase `r`, which starts at round `S_r`,
the round `t` plays the arm of index `t - S_r` of the list `pulls r S_r`. The rounds that are in no
phase, which only exist when all the phases from some point on are empty, play an arbitrary arm. -/
noncomputable def armAt [Nonempty α] (H : ℕ → Σ m, Hist 𝓞 α 𝓨 m) (t : ℕ) : α :=
  (pulls (phaseOf S₀ pulls elim H t) (activeSet S₀ pulls elim H (phaseOf S₀ pulls elim H t))).getD
    (t - phaseStart S₀ pulls elim H (phaseOf S₀ pulls elim H t)) (Classical.arbitrary α)

variable [Nonempty α]

/-- Round `j` of phase `r` plays the arm of index `j` of the list `pulls r S_r`. -/
lemma armAt_phaseStart_add {r j : ℕ} (hj : j < (pulls r (activeSet S₀ pulls elim H r)).length) :
    armAt S₀ pulls elim H (phaseStart S₀ pulls elim H r + j) =
      (pulls r (activeSet S₀ pulls elim H r))[j] := by
  have h_phase : phaseOf S₀ pulls elim H (phaseStart S₀ pulls elim H r + j) = r :=
    phaseOf_eq (Nat.le_add_right _ _) (by rw [phaseStart_succ]; omega)
  rw [armAt, h_phase, Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hj]

/-- The arm played at round `t` only depends on the histories of the first `m ≤ t` rounds. -/
lemma armAt_congr {t : ℕ} (hH : ∀ m ≤ t, H m = H' m) :
    armAt S₀ pulls elim H t = armAt S₀ pulls elim H' t := by
  have h_le := phaseStart_phaseOf_le S₀ pulls elim H t
  rw [armAt, armAt, ← phaseOf_congr hH, activeSet_congr hH h_le, phaseStart_congr hH h_le]

end Arm

/-! ### The final phase -/

variable (S₀ pulls elim) in
open scoped Classical in
/-- The first phase with at most one active answer (`0` if there is none). -/
noncomputable def finalPhase (H : ℕ → Σ m, Hist 𝓞 α 𝓨 m) : ℕ :=
  Nat.find (p := fun r ↦ #(activeSet S₀ pulls elim H r) ≤ 1 ∨
    ∀ j, 1 < #(activeSet S₀ pulls elim H j)) <| by
    by_cases h : ∃ r, #(activeSet S₀ pulls elim H r) ≤ 1
    · exact h.imp fun _ ↦ Or.inl
    · exact ⟨0, Or.inr fun j ↦ not_le.1 fun hj ↦ h ⟨j, hj⟩⟩

lemma finalPhase_eq_iff (h : ∃ r, #(activeSet S₀ pulls elim H r) ≤ 1) {r : ℕ} :
    finalPhase S₀ pulls elim H = r ↔
      #(activeSet S₀ pulls elim H r) ≤ 1 ∧ ∀ j < r, 1 < #(activeSet S₀ pulls elim H j) := by
  classical
  obtain ⟨r₀, hr₀⟩ := h
  rw [finalPhase, Nat.find_eq_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁.resolve_right fun h ↦ (h r₀).not_ge hr₀, fun j hj ↦ not_le.1 fun h ↦ ?_⟩
    exact h₂ j hj (Or.inl h)
  · rintro ⟨h₁, h₂⟩
    exact ⟨Or.inl h₁, fun j hj h ↦
      h.elim (fun h' ↦ (h₂ j hj).not_ge h') fun h' ↦ (h' r).not_ge h₁⟩

lemma card_activeSet_finalPhase_le (h : ∃ r, #(activeSet S₀ pulls elim H r) ≤ 1) :
    #(activeSet S₀ pulls elim H (finalPhase S₀ pulls elim H)) ≤ 1 :=
  ((finalPhase_eq_iff h).1 rfl).1

lemma one_lt_card_activeSet_of_lt_finalPhase (h : ∃ r, #(activeSet S₀ pulls elim H r) ≤ 1)
    {j : ℕ} (hj : j < finalPhase S₀ pulls elim H) : 1 < #(activeSet S₀ pulls elim H j) :=
  ((finalPhase_eq_iff h).1 rfl).2 j hj

lemma finalPhase_le {r : ℕ} (hr : #(activeSet S₀ pulls elim H r) ≤ 1) :
    finalPhase S₀ pulls elim H ≤ r := by
  by_contra h
  exact (one_lt_card_activeSet_of_lt_finalPhase ⟨r, hr⟩ (not_le.1 h)).not_ge hr

/-- The first phase with at most one active answer only depends on the histories of the first
`m ≤ N` rounds, if some phase starting by round `N` has at most one active answer. -/
lemma finalPhase_congr {N : ℕ} (hH : ∀ m ≤ N, H m = H' m) {r : ℕ}
    (hr : phaseStart S₀ pulls elim H r ≤ N) (hcard : #(activeSet S₀ pulls elim H r) ≤ 1) :
    finalPhase S₀ pulls elim H = finalPhase S₀ pulls elim H' := by
  have h_le : ∀ j ≤ r, phaseStart S₀ pulls elim H j ≤ N := fun j hj ↦
    (monotone_phaseStart hj).trans hr
  have hcard' : #(activeSet S₀ pulls elim H' r) ≤ 1 := activeSet_congr hH hr ▸ hcard
  have h_fin := finalPhase_le hcard
  refine ((finalPhase_eq_iff ⟨r, hcard'⟩).2 ⟨?_, fun j hj ↦ ?_⟩).symm
  · rw [← activeSet_congr hH (h_le _ h_fin)]
    exact card_activeSet_finalPhase_le ⟨r, hcard⟩
  · rw [← activeSet_congr hH (h_le _ (hj.le.trans h_fin))]
    exact one_lt_card_activeSet_of_lt_finalPhase ⟨r, hcard⟩ hj

/-- **Elimination of an answer.** An answer `i ∈ S₀` that is not active in phase `k` is eliminated
at the end of some phase `r < k`. -/
lemma exists_lt_mem_activeSet_notMem_activeSet_succ {i : ℐ} (hi : i ∈ S₀) {k : ℕ}
    (hk : i ∉ activeSet S₀ pulls elim H k) :
    ∃ r < k, i ∈ activeSet S₀ pulls elim H r ∧ i ∉ activeSet S₀ pulls elim H (r + 1) := by
  induction k with
  | zero => exact absurd hi hk
  | succ k ih =>
    by_cases hk' : i ∈ activeSet S₀ pulls elim H k
    · exact ⟨k, Nat.lt_succ_self k, hk', hk⟩
    · obtain ⟨r, hr, h⟩ := ih hk'
      exact ⟨r, hr.trans (Nat.lt_succ_self k), h⟩

/-! ### Stopping rules -/

variable (S₀ pulls elim) in
/-- The stopping rule of the fixed-confidence version of phased elimination at round `t`: a phase
with at most one active answer starts at round `t`. -/
def StopRule (H : ℕ → Σ m, Hist 𝓞 α 𝓨 m) (t : ℕ) : Prop :=
  ∃ r, phaseStart S₀ pulls elim H r = t ∧ #(activeSet S₀ pulls elim H r) ≤ 1

lemma stopRule_iff {t : ℕ} :
    StopRule S₀ pulls elim H t ↔
      ∃ r, phaseStart S₀ pulls elim H r = t ∧ #(activeSet S₀ pulls elim H r) ≤ 1 := (Iff.rfl)

/-- The stopping rule at round `t` only depends on the histories of the first `m ≤ t` rounds. -/
lemma stopRule_congr {t : ℕ} (hH : ∀ m ≤ t, H m = H' m) :
    StopRule S₀ pulls elim H t ↔ StopRule S₀ pulls elim H' t := by
  have h (H H' : ℕ → Σ m, Hist 𝓞 α 𝓨 m) (hH : ∀ m ≤ t, H m = H' m)
      (h : StopRule S₀ pulls elim H t) : StopRule S₀ pulls elim H' t := by
    obtain ⟨r, hr, hcard⟩ := h
    exact ⟨r, (phaseStart_eq_congr hH).1 hr, activeSet_congr hH hr.le ▸ hcard⟩
  exact ⟨h H H' hH, h H' H fun m hm ↦ (hH m hm).symm⟩

/-- The first round at which the stopping rule holds is the start of the first phase with at most
one active answer. -/
lemma phaseStart_finalPhase_le_of_stopRule {t : ℕ} (hstop : StopRule S₀ pulls elim H t) :
    phaseStart S₀ pulls elim H (finalPhase S₀ pulls elim H) ≤ t := by
  obtain ⟨r, rfl, hr⟩ := hstop
  exact monotone_phaseStart (finalPhase_le hr)

lemma stopRule_phaseStart_finalPhase (h : ∃ r, #(activeSet S₀ pulls elim H r) ≤ 1) :
    StopRule S₀ pulls elim H (phaseStart S₀ pulls elim H (finalPhase S₀ pulls elim H)) :=
  ⟨_, rfl, card_activeSet_finalPhase_le h⟩

/-! ### Measurability -/

section Measurability

variable [MeasurableSpace 𝓞] [MeasurableSpace α] [MeasurableSpace 𝓨] [Countable ℐ] {β : Type*}
  [MeasurableSpace β] {H : β → ℕ → Σ m, Hist 𝓞 α 𝓨 m}

/-- The state after `r` phases is measurable in the histories, if the elimination maps are. -/
lemma measurable_phaseState (helim : ∀ r S, Measurable (elim r S)) (hH : ∀ m, Measurable (H · m))
    (r : ℕ) : Measurable fun x ↦ phaseState S₀ pulls elim (H x) r := by
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
    simp_rw [phaseState_succ]
    refine (measurable_from_prod_countable_right (f := fun p : (ℕ × Finset ℐ) × β ↦
      (p.1.1 + (pulls r p.1.2).length,
        p.1.2 ∩ elim r p.1.2 (H p.2 (p.1.1 + (pulls r p.1.2).length)))) fun s ↦ ?_).comp
      (ih.prodMk measurable_id)
    dsimp only
    exact measurable_const.prodMk
      (measurable_const.inter_finset ((helim r s.2).comp (hH (s.1 + (pulls r s.2).length))))

lemma measurable_phaseStart (helim : ∀ r S, Measurable (elim r S)) (hH : ∀ m, Measurable (H · m))
    (r : ℕ) : Measurable fun x ↦ phaseStart S₀ pulls elim (H x) r :=
  measurable_fst.comp (measurable_phaseState helim hH r)

lemma measurable_activeSet (helim : ∀ r S, Measurable (elim r S))
    (hH : ∀ m, Measurable (H · m)) (r : ℕ) : Measurable fun x ↦ activeSet S₀ pulls elim (H x) r :=
  measurable_snd.comp (measurable_phaseState helim hH r)

/-- The state after a measurable number of phases is measurable. -/
lemma measurable_phaseState_comp (helim : ∀ r S, Measurable (elim r S))
    (hH : ∀ m, Measurable (H · m)) {k : β → ℕ} (hk : Measurable k) :
    Measurable fun x ↦ phaseState S₀ pulls elim (H x) (k x) :=
  (measurable_from_prod_countable_right (f := fun p : ℕ × β ↦ phaseState S₀ pulls elim (H p.2) p.1)
    fun r ↦ measurable_phaseState helim hH r).comp (hk.prodMk measurable_id)

/-- The active set after a measurable number of phases is measurable. -/
lemma measurable_activeSet_comp (helim : ∀ r S, Measurable (elim r S))
    (hH : ∀ m, Measurable (H · m)) {k : β → ℕ} (hk : Measurable k) :
    Measurable fun x ↦ activeSet S₀ pulls elim (H x) (k x) :=
  measurable_snd.comp (measurable_phaseState_comp helim hH hk)

lemma measurable_phaseOf (helim : ∀ r S, Measurable (elim r S)) (hH : ∀ m, Measurable (H · m))
    (t : ℕ) : Measurable fun x ↦ phaseOf S₀ pulls elim (H x) t := by
  classical
  refine measurable_find _ fun r ↦ ?_
  simp only [Set.ofPred_or, Set.ofPred_forall]
  exact (measurableSet_lt measurable_const (measurable_phaseStart helim hH (r + 1))).union
    (.iInter fun j ↦ measurableSet_le (measurable_phaseStart helim hH (j + 1)) measurable_const)

lemma measurable_armAt [Nonempty α] (helim : ∀ r S, Measurable (elim r S))
    (hH : ∀ m, Measurable (H · m)) (t : ℕ) : Measurable fun x ↦ armAt S₀ pulls elim (H x) t := by
  have hk := measurable_phaseOf (S₀ := S₀) (pulls := pulls) helim hH t
  have h_eq : (fun x ↦ armAt S₀ pulls elim (H x) t) = (fun p : ℕ × (ℕ × Finset ℐ) ↦
      (pulls p.1 p.2.2).getD (t - p.2.1) (Classical.arbitrary α)) ∘
        fun x ↦ (phaseOf S₀ pulls elim (H x) t,
          phaseState S₀ pulls elim (H x) (phaseOf S₀ pulls elim (H x) t)) := by
    ext x
    rw [armAt, Function.comp_apply, phaseState_eq]
  rw [h_eq]
  exact (measurable_of_countable _).comp (hk.prodMk (measurable_phaseState_comp helim hH hk))

lemma measurable_finalPhase (helim : ∀ r S, Measurable (elim r S))
    (hH : ∀ m, Measurable (H · m)) : Measurable fun x ↦ finalPhase S₀ pulls elim (H x) := by
  classical
  have h_card (j : ℕ) : Measurable fun x ↦ #(activeSet S₀ pulls elim (H x) j) :=
    (measurable_of_countable card).comp (measurable_activeSet helim hH j)
  refine measurable_find _ fun r ↦ ?_
  simp only [Set.ofPred_or, Set.ofPred_forall]
  exact (measurableSet_le (h_card r) measurable_const).union
    (.iInter fun j ↦ measurableSet_lt measurable_const (h_card j))

lemma measurableSet_stopRule (helim : ∀ r S, Measurable (elim r S))
    (hH : ∀ m, Measurable (H · m)) (t : ℕ) :
    MeasurableSet {x | StopRule S₀ pulls elim (H x) t} := by
  simp only [stopRule_iff, Set.ofPred_exists]
  refine .iUnion fun r ↦ ?_
  have h_eq : {x | phaseStart S₀ pulls elim (H x) r = t ∧ #(activeSet S₀ pulls elim (H x) r) ≤ 1} =
      (fun x ↦ phaseState S₀ pulls elim (H x) r) ⁻¹' {p | p.1 = t ∧ #p.2 ≤ 1} := by
    ext x
    simp [phaseState_eq]
  rw [h_eq]
  exact (Set.to_countable _).measurableSet.preimage (measurable_phaseState helim hH r)

variable [MeasurableSpace ℐ] (out : Finset ℐ → ℐ)

variable (S₀ pulls) in
/-- The output rule of the fixed-confidence version is measurable. -/
lemma measurable_out_activeSet_finalPhase (helim : ∀ r S, Measurable (elim r S)) (t : ℕ) :
    Measurable fun h : Hist 𝓞 α 𝓨 t ↦ out (activeSet S₀ pulls elim (fun m ↦ truncHist m ⟨t, h⟩)
      (finalPhase S₀ pulls elim (fun m ↦ truncHist m ⟨t, h⟩))) :=
  (measurable_of_countable out).comp (measurable_activeSet_comp helim (measurable_truncHist_mk t)
    (measurable_finalPhase helim (measurable_truncHist_mk t)))

variable (S₀ pulls) in
/-- The output rule of the fixed-budget version is measurable. -/
lemma measurable_out_activeSet (helim : ∀ r S, Measurable (elim r S)) (R t : ℕ) :
    Measurable fun h : Hist 𝓞 α 𝓨 t ↦
      out (activeSet S₀ pulls elim (fun m ↦ truncHist m ⟨t, h⟩) R) :=
  (measurable_of_countable out).comp (measurable_activeSet helim (measurable_truncHist_mk t) R)

end Measurability

/-! ### The sampling rule -/

variable [MeasurableSpace 𝓞] [MeasurableSpace α] [MeasurableSpace 𝓨] [Countable ℐ] [Nonempty α]

variable (S₀ pulls elim) in
/-- The sampling rule of phased elimination: the deterministic algorithm that plays `armAt` for
the prefixes of the history. -/
noncomputable def samplingRule (helim : ∀ r S, Measurable (elim r S)) : Algorithm 𝓞 α 𝓨 :=
  Algorithm.deterministic (fun t p ↦ armAt S₀ pulls elim (fun m ↦ truncHist m ⟨t, p.1⟩) t)
    fun t ↦ measurable_armAt helim
      (fun m ↦ (measurable_truncHist_mk t m).comp measurable_fst) t

variable {helim : ∀ r S, Measurable (elim r S)}

lemma samplingRule_def :
    samplingRule S₀ pulls elim helim =
      Algorithm.deterministic (fun t p ↦ armAt S₀ pulls elim (fun m ↦ truncHist m ⟨t, p.1⟩) t)
        (fun t ↦ measurable_armAt helim
          (fun m ↦ (measurable_truncHist_mk t m).comp measurable_fst) t) := (rfl)

variable [MeasurableEq α] {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [SFinite P] {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨}
  {env : Environment 𝓞 α 𝓨}

/-- Along every run of the sampling rule of phased elimination, the arm played at round `t` is
`armAt` for the histories of the run. -/
lemma action_ae_eq_armAt (hseq : IsAlgEnvSeq O X Y (samplingRule S₀ pulls elim helim) env P) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = armAt S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) t := by
  filter_upwards [hseq.action_ae_all_eq_deterministic] with ω hω t
  rw [hω t]
  exact armAt_congr fun m hm ↦ truncHist_mk_history_of_le hm ω

omit [MeasurableSpace 𝓞] [MeasurableSpace α] [MeasurableSpace 𝓨] [Countable ℐ] [MeasurableEq α] in
/-- **Pull counts of a phase.** If the arms are played by phased elimination, phase `r` pulls the
arm `a` exactly `(pulls r S_r).count a` times. -/
lemma pullCount_phaseStart_succ [DecidableEq α] {H : ℕ → Σ m, Hist 𝓞 α 𝓨 m} {ω : Ω}
    (hω : ∀ t, X t ω = armAt S₀ pulls elim H t) (a : α) (r : ℕ) :
    pullCount X a (phaseStart S₀ pulls elim H (r + 1)) ω =
      pullCount X a (phaseStart S₀ pulls elim H r) ω +
        (pulls r (activeSet S₀ pulls elim H r)).count a := by
  -- The number of indices of a list `l` at which `a` appears is `l.count a`.
  have h_count (l : List α) (d : α) :
      (∑ j ∈ range l.length, if l.getD j d = a then 1 else 0) = l.count a := by
    induction l with
    | nil => simp
    | cons x l ih =>
      rw [List.length_cons, sum_range_succ', List.count_cons]
      simp only [List.getD_cons_succ, List.getD_cons_zero, ih, beq_iff_eq]
  rw [phaseStart_succ, pullCount_eq_sum, pullCount_eq_sum, sum_range_add, Nat.add_left_cancel_iff,
    ← h_count _ (Classical.arbitrary α)]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [hω, armAt_phaseStart_add (mem_range.1 hj), List.getD_eq_getElem _ _ (mem_range.1 hj)]

end PhasedElimination

open PhasedElimination

variable {𝓞 α 𝓨 ℐ : Type*} [MeasurableSpace 𝓞] [MeasurableSpace α] [MeasurableSpace 𝓨]
  [Nonempty α] [DecidableEq ℐ] [Countable ℐ] [MeasurableSpace ℐ] {S₀ : Finset ℐ}
  {pulls : ℕ → Finset ℐ → List α} {elim : ℕ → Finset ℐ → (Σ m, Hist 𝓞 α 𝓨 m) → Finset ℐ}
  {helim : ∀ r S, Measurable (elim r S)} {out : Finset ℐ → ℐ}

/-! ### The fixed-confidence version -/

variable (S₀ pulls elim helim out) in
/-- **Phased elimination**, fixed-confidence version, with initial active set `S₀`, pull schedule
`pulls`, elimination maps `elim` and output rule `out`: it plays the phases of
`PhasedElimination.samplingRule`, stops at the start of the first phase whose active set `S` has
at most one element, and outputs `out S`. -/
noncomputable def phasedElimination : IdentAlg 𝓞 α 𝓨 ℐ :=
  ofStop (samplingRule S₀ pulls elim helim)
    (fun t h ↦ StopRule S₀ pulls elim (fun m ↦ truncHist m ⟨t, h⟩) t)
    (fun t ↦ measurableSet_stopRule helim (measurable_truncHist_mk t) t)
    fun t ↦ Kernel.deterministic _ (measurable_out_activeSet_finalPhase S₀ pulls out helim t)

lemma phasedElimination_def :
    phasedElimination S₀ pulls elim helim out = ofStop (samplingRule S₀ pulls elim helim)
      (fun t h ↦ StopRule S₀ pulls elim (fun m ↦ truncHist m ⟨t, h⟩) t)
      (fun t ↦ measurableSet_stopRule helim (measurable_truncHist_mk t) t)
      (fun t ↦ Kernel.deterministic _
        (measurable_out_activeSet_finalPhase S₀ pulls out helim t)) := (rfl)

@[simp]
lemma alg_phasedElimination :
    (phasedElimination S₀ pulls elim helim out).alg = samplingRule S₀ pulls elim helim := by
  rw [phasedElimination_def, alg_ofStop]

@[simp]
lemma mem_stopSet_phasedElimination {h : Σ t, Hist 𝓞 α 𝓨 t} :
    h ∈ (phasedElimination S₀ pulls elim helim out).stopSet ↔
      StopRule S₀ pulls elim (fun m ↦ truncHist m h) h.1 := by
  rw [phasedElimination_def, mem_stopSet_ofStop]

@[simp]
lemma output_phasedElimination (h : Σ t, Hist 𝓞 α 𝓨 t) :
    (phasedElimination S₀ pulls elim helim out).output h =
      Measure.dirac (out (activeSet S₀ pulls elim (fun m ↦ truncHist m h)
        (finalPhase S₀ pulls elim (fun m ↦ truncHist m h)))) := by
  rw [phasedElimination_def, output_ofStop, Kernel.sigma_apply, Kernel.deterministic_apply]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨}
  {ω : Ω}

/-- Along a trajectory, the stopping rule of phased elimination holds at round `t` iff it holds
for the histories of the trajectory. -/
lemma mem_stopSet_phasedElimination_history {t : ℕ} :
    (⟨t, history O X Y t ω⟩ : Σ t, Hist 𝓞 α 𝓨 t) ∈
        (phasedElimination S₀ pulls elim helim out).stopSet ↔
      StopRule S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) t := by
  rw [mem_stopSet_phasedElimination]
  exact stopRule_congr fun m hm ↦ truncHist_mk_history_of_le hm ω

/-- **The stopping time of phased elimination** is the start of the first phase with at most one
active answer. -/
lemma stoppingTime_phasedElimination_eq
    (h : ∃ r, #(activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) r) ≤ 1) :
    (phasedElimination S₀ pulls elim helim out).stoppingTime O X Y ω =
      phaseStart S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω)
        (finalPhase S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω)) := by
  rw [IdentAlg.stoppingTime_eq_coe_iff, mem_stopSet_phasedElimination_history]
  refine ⟨stopRule_phaseStart_finalPhase h, fun j hj hstop ↦ ?_⟩
  rw [mem_stopSet_phasedElimination_history] at hstop
  exact hj.not_ge (phaseStart_finalPhase_le_of_stopRule hstop)

/-- Phased elimination does not stop if more than one answer stays active in every phase. -/
lemma stoppingTime_phasedElimination_eq_top
    (h : ∀ r, 1 < #(activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) r)) :
    (phasedElimination S₀ pulls elim helim out).stoppingTime O X Y ω = ⊤ := by
  rw [IdentAlg.stoppingTime_eq_top_iff]
  rintro t hstop
  obtain ⟨r, -, hr⟩ := mem_stopSet_phasedElimination_history.1 hstop
  exact (h r).not_ge hr

/-- Phased elimination stops by the start of every phase with at most one active answer. -/
lemma stoppingTime_phasedElimination_le {r : ℕ}
    (hr : #(activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) r) ≤ 1) :
    (phasedElimination S₀ pulls elim helim out).stoppingTime O X Y ω ≤
      phaseStart S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) r := by
  rw [stoppingTime_phasedElimination_eq ⟨r, hr⟩]
  exact WithTop.coe_le_coe.2 (monotone_phaseStart (finalPhase_le hr))

section Survival

variable [MeasurableSingletonClass ℐ] {P : Measure Ω} [IsProbabilityMeasure P]
  {env : Environment 𝓞 α 𝓨}

/-- **Survival bound of phased elimination.** Let `out` choose an element of every nonempty set,
and let `i ∈ S₀`. Along any algorithm-environment sequence of the sampling rule, the probability
that phased elimination stops with an output other than `i` is at most the sum over the phases `r`
of the probability that more than one answer is active in phase `r`, `i` among them, and that `i`
is eliminated at its end. -/
theorem measure_histOutputMeasure_phasedElimination_le
    (hseq : IsAlgEnvSeq O X Y (samplingRule S₀ pulls elim helim) env P)
    (hout : ∀ S : Finset ℐ, S.Nonempty → out S ∈ S) {i : ℐ} (hi : i ∈ S₀) :
    histOutputMeasure (phasedElimination S₀ pulls elim helim out) env
        {p | p.1 ∈ (phasedElimination S₀ pulls elim helim out).stopSet ∧ p.2 ≠ i} ≤
      ∑' r, P {ω | 1 < #(activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) r) ∧
        i ∈ activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) r ∧
        i ∉ activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) (r + 1)} := by
  have h_real := measureReal_histOutputMeasure_ofStop_deterministic_le
    (stop := fun t h ↦ StopRule S₀ pulls elim (fun m ↦ truncHist m ⟨t, h⟩) t)
    (hstop := fun t ↦ measurableSet_stopRule helim (measurable_truncHist_mk t) t)
    (hrec := measurable_out_activeSet_finalPhase S₀ pulls out helim) hseq
    (measurableSet_singleton i)
  rw [← phasedElimination_def] at h_real
  simp only [Set.mem_singleton_iff] at h_real
  rw [← ofReal_measureReal]
  refine (ENNReal.ofReal_le_ofReal h_real).trans ?_
  rw [ofReal_measureReal]
  refine (measure_mono (t := ⋃ r, {ω | 1 < #(activeSet S₀ pulls elim
      (fun m ↦ sigmaHistory O X Y m ω) r) ∧
    i ∈ activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) r ∧
    i ∉ activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) (r + 1)})
      fun ω hω ↦ ?_).trans (measure_iUnion_le _)
  obtain ⟨t, hstop, hne⟩ := hω
  -- At a round `t` at which it stops, the output is `out` of the final active set of the run.
  have hH (m : ℕ) (hm : m ≤ t) : truncHist m ⟨t, history O X Y t ω⟩ = sigmaHistory O X Y m ω :=
    truncHist_mk_history_of_le hm ω
  obtain ⟨r, hr, hcard⟩ := hstop
  rw [activeSet_congr hH ((monotone_phaseStart (finalPhase_le hcard)).trans hr.le),
    finalPhase_congr hH hr.le hcard] at hne
  have hcard' := activeSet_congr hH hr.le ▸ hcard
  obtain ⟨r', hr', h_elim⟩ := exists_lt_mem_activeSet_notMem_activeSet_succ hi fun hi' ↦
    hne (card_le_one.1 (card_activeSet_finalPhase_le ⟨r, hcard'⟩) _ (hout _ ⟨i, hi'⟩) _ hi')
  exact Set.mem_iUnion.2 ⟨r', one_lt_card_activeSet_of_lt_finalPhase ⟨r, hcard'⟩ hr', h_elim⟩

end Survival

/-! ### The fixed-budget version -/

variable (S₀ pulls elim helim out) in
/-- **Phased elimination**, fixed-budget version, with initial active set `S₀`, pull schedule
`pulls`, elimination maps `elim`, output rule `out` and `R` phases: it plays the phases of
`PhasedElimination.samplingRule`, stops at the start of phase `R` and outputs `out S_R`. -/
noncomputable def phasedEliminationFixedBudget (R : ℕ) : IdentAlg 𝓞 α 𝓨 ℐ :=
  ofStop (samplingRule S₀ pulls elim helim)
    (fun t h ↦ phaseStart S₀ pulls elim (fun m ↦ truncHist m ⟨t, h⟩) R = t)
    (fun t ↦ measurableSet_eq_fun (measurable_phaseStart helim (measurable_truncHist_mk t) R)
      measurable_const)
    fun t ↦ Kernel.deterministic _ (measurable_out_activeSet S₀ pulls out helim R t)

variable {R : ℕ}

lemma phasedEliminationFixedBudget_def :
    phasedEliminationFixedBudget S₀ pulls elim helim out R =
      ofStop (samplingRule S₀ pulls elim helim)
        (fun t h ↦ phaseStart S₀ pulls elim (fun m ↦ truncHist m ⟨t, h⟩) R = t)
        (fun t ↦ measurableSet_eq_fun (measurable_phaseStart helim (measurable_truncHist_mk t) R)
          measurable_const)
        (fun t ↦ Kernel.deterministic _ (measurable_out_activeSet S₀ pulls out helim R t)) := (rfl)

@[simp]
lemma alg_phasedEliminationFixedBudget :
    (phasedEliminationFixedBudget S₀ pulls elim helim out R).alg =
      samplingRule S₀ pulls elim helim := by
  rw [phasedEliminationFixedBudget_def, alg_ofStop]

@[simp]
lemma mem_stopSet_phasedEliminationFixedBudget {h : Σ t, Hist 𝓞 α 𝓨 t} :
    h ∈ (phasedEliminationFixedBudget S₀ pulls elim helim out R).stopSet ↔
      phaseStart S₀ pulls elim (fun m ↦ truncHist m h) R = h.1 := by
  rw [phasedEliminationFixedBudget_def, mem_stopSet_ofStop]

@[simp]
lemma output_phasedEliminationFixedBudget (h : Σ t, Hist 𝓞 α 𝓨 t) :
    (phasedEliminationFixedBudget S₀ pulls elim helim out R).output h =
      Measure.dirac (out (activeSet S₀ pulls elim (fun m ↦ truncHist m h) R)) := by
  rw [phasedEliminationFixedBudget_def, output_ofStop, Kernel.sigma_apply,
    Kernel.deterministic_apply]

/-- Along a trajectory, the fixed-budget version stops at round `t` iff phase `R` of the
trajectory starts at round `t`. -/
lemma mem_stopSet_phasedEliminationFixedBudget_history {t : ℕ} :
    (⟨t, history O X Y t ω⟩ : Σ t, Hist 𝓞 α 𝓨 t) ∈
        (phasedEliminationFixedBudget S₀ pulls elim helim out R).stopSet ↔
      phaseStart S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) R = t := by
  rw [mem_stopSet_phasedEliminationFixedBudget]
  exact phaseStart_eq_congr fun m hm ↦ truncHist_mk_history_of_le hm ω

/-- **The stopping time of the fixed-budget version** is the start of phase `R`. -/
lemma stoppingTime_phasedEliminationFixedBudget :
    (phasedEliminationFixedBudget S₀ pulls elim helim out R).stoppingTime O X Y ω =
      phaseStart S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) R := by
  rw [IdentAlg.stoppingTime_eq_coe_iff, mem_stopSet_phasedEliminationFixedBudget_history]
  exact ⟨rfl, fun j hj hstop ↦ hj.ne' (mem_stopSet_phasedEliminationFixedBudget_history.1 hstop)⟩

/-- **The fixed-budget version is a fixed-budget algorithm** when the number of pulls `L r` of each
phase `r` does not depend on its active set: its budget is `∑ r < R, L r`. -/
theorem isFixedBudget_phasedEliminationFixedBudget {L : ℕ → ℕ}
    (hL : ∀ (H : ℕ → Σ m, Hist 𝓞 α 𝓨 m) r, (pulls r (activeSet S₀ pulls elim H r)).length = L r) :
    IsFixedBudget (phasedEliminationFixedBudget S₀ pulls elim helim out R)
      (∑ r ∈ range R, L r) := by
  rw [isFixedBudget_iff]
  ext h
  simp only [mem_stopSet_phasedEliminationFixedBudget, phaseStart_eq_sum, hL, Set.mem_ofPred_eq]
  exact eq_comm

variable [MeasurableSingletonClass ℐ] {P : Measure Ω} [IsProbabilityMeasure P]
  {env : Environment 𝓞 α 𝓨}

/-- **Survival bound of the fixed-budget version.** Let `out` choose an element of every nonempty
set, let `i ∈ S₀`, and let at most one answer be active after `R` phases, almost surely along an
algorithm-environment sequence of the sampling rule. Then the probability that the fixed-budget
version outputs an answer other than `i` is at most the sum over the phases `r < R` of the
probability that `i` is active in phase `r` and eliminated at its end. -/
theorem measure_outputMeasure_phasedEliminationFixedBudget_le
    (hseq : IsAlgEnvSeq O X Y (samplingRule S₀ pulls elim helim) env P)
    (hout : ∀ S : Finset ℐ, S.Nonempty → out S ∈ S) {i : ℐ} (hi : i ∈ S₀)
    (hR : ∀ᵐ ω ∂P, #(activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) R) ≤ 1) :
    (phasedEliminationFixedBudget S₀ pulls elim helim out R).outputMeasure env {i}ᶜ ≤
      ∑ r ∈ range R, P {ω | i ∈ activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) r ∧
        i ∉ activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) (r + 1)} := by
  set A := phasedEliminationFixedBudget S₀ pulls elim helim out R
  have h_real := measureReal_histOutputMeasure_ofStop_deterministic_notMem_or_le
    (stop := fun t h ↦ phaseStart S₀ pulls elim (fun m ↦ truncHist m ⟨t, h⟩) R = t)
    (hstop := fun t ↦ measurableSet_eq_fun
      (measurable_phaseStart helim (measurable_truncHist_mk t) R) measurable_const)
    (hrec := measurable_out_activeSet S₀ pulls out helim R) hseq
    (measurableSet_singleton i)
  rw [← phasedEliminationFixedBudget_def] at h_real
  simp only [Set.mem_singleton_iff] at h_real
  -- The output law is the second marginal of the joint law of the stopped history and the output.
  rw [← snd_histOutputMeasure, Measure.snd_apply (measurableSet_singleton i).compl]
  calc histOutputMeasure A env (Prod.snd ⁻¹' {i}ᶜ)
  _ ≤ histOutputMeasure A env {p | p.1 ∉ A.stopSet ∨ p.2 ≠ i} :=
    measure_mono fun p hp ↦ Or.inr hp
  _ = ENNReal.ofReal ((histOutputMeasure A env).real {p | p.1 ∉ A.stopSet ∨ p.2 ≠ i}) :=
    (ofReal_measureReal (measure_ne_top _ _)).symm
  _ ≤ P {ω | (∀ t, ¬ phaseStart S₀ pulls elim
        (fun m ↦ truncHist m ⟨t, history O X Y t ω⟩) R = t) ∨
      ∃ t, phaseStart S₀ pulls elim (fun m ↦ truncHist m ⟨t, history O X Y t ω⟩) R = t ∧
        out (activeSet S₀ pulls elim (fun m ↦ truncHist m ⟨t, history O X Y t ω⟩) R) ≠ i} := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal h_real
  _ ≤ P (⋃ r ∈ range R, {ω | i ∈ activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) r ∧
        i ∉ activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) (r + 1)}) := by
    refine measure_mono_ae ?_
    filter_upwards [hR] with ω hω hbad
    -- The fixed-budget version stops at the start of phase `R`, with output `out S_R`.
    set t := phaseStart S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) R
    have hH (m : ℕ) (hm : m ≤ t) : truncHist m ⟨t, history O X Y t ω⟩ = sigmaHistory O X Y m ω :=
    truncHist_mk_history_of_le hm ω
    have h_start : phaseStart S₀ pulls elim (fun m ↦ truncHist m ⟨t, history O X Y t ω⟩) R = t :=
      (phaseStart_eq_congr hH).2 rfl
    have hne : out (activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) R) ≠ i := by
      rcases hbad with hbad | ⟨t', ht', hne⟩
      · exact absurd h_start (hbad t)
      · have hH' (m : ℕ) (hm : m ≤ t') :
            truncHist m ⟨t', history O X Y t' ω⟩ = sigmaHistory O X Y m ω :=
          truncHist_mk_history_of_le hm ω
        rwa [activeSet_congr hH' ht'.le] at hne
    obtain ⟨r, hr, h_elim⟩ := exists_lt_mem_activeSet_notMem_activeSet_succ hi fun hi' ↦
      hne (card_le_one.1 hω _ (hout _ ⟨i, hi'⟩) _ hi')
    exact Set.mem_biUnion (mem_range.2 hr) h_elim
  _ ≤ ∑ r ∈ range R, P {ω | i ∈ activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) r ∧
        i ∉ activeSet S₀ pulls elim (fun m ↦ sigmaHistory O X Y m ω) (r + 1)} :=
    measure_biUnion_finset_le _ _

end LMLExplore.Identification
