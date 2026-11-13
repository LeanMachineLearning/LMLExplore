/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Deterministic
public import LMLExplore.Analysis.InnerProductSpace.LeastSquares
public import LMLExplore.Bandits.LinearBandit.Basic

/-!
# Phased elimination for linear bandits

Phased elimination [LS, Algorithm 12] plays a stochastic linear bandit with a finite set of arms
`α` and features `φ : α → E` in phases. Phase `ℓ` starts with a set `S_ℓ` of surviving arms
(`S_0` is the set of all arms), pulls each arm `a` a number `m ℓ S_ℓ a` of times fixed by the
survivors, computes the unregularized least-squares estimate `θ̂_ℓ` of the parameter from the
features and the rewards of that phase only, and keeps the arms whose estimated reward is within
`2 ε_ℓ` of the best estimated reward of `S_ℓ`:
`S_{ℓ+1} = {a ∈ S_ℓ | ∀ b ∈ S_ℓ, ⟪θ̂_ℓ, φ b - φ a⟫ ≤ 2 ε_ℓ}`.
In [LS], `ε_ℓ = 2^{-ℓ}` and `m ℓ S a = ⌈2 d π(a) log (k ℓ (ℓ + 1) / δ) / ε_ℓ²⌉` for a G-optimal
design `π` on `S`, so that the estimate of phase `ℓ` is `ε_ℓ`-accurate on `S_ℓ` with high
probability. The numbers of pulls `m` and the accuracies `ε` are parameters here.

If the estimate of phase `ℓ` is `ε_ℓ`-accurate on `S_ℓ`, that is `|⟪θ̂_ℓ - θ, φ b⟫| ≤ ε_ℓ` for every
`b ∈ S_ℓ`, then the elimination keeps every arm of `S_ℓ` of largest expected reward
`⟪θ, φ a⟫`, and every arm it keeps has a gap at most `4 ε_ℓ` to every arm of `S_ℓ`. When all the
phases before `ℓ` are accurate, an optimal arm survives them, the arms pulled in phase `i + 1` have
gaps at most `4 ε_i`, and the regret of the first `ℓ + 1` phases is at most
`n_0 G + ∑_{i < ℓ} 4 ε_i n_{i+1}`, where `n_i` is the length of phase `i` and `G` bounds the gaps
of all arms. This is the deterministic part of the proof of [LS, Theorem 22.1].

The survivors and the first rounds of the phases are functions of the sequence of rewards
`y : ℕ → ℝ` only: the arms pulled during a phase are determined by its survivors, through the
`schedule` that lists each arm `a` exactly `n a` times. The phase of round `t` and the arm pulled at
round `t` only depend on the rewards of the rounds before `t`, which makes phased elimination a
deterministic algorithm `phasedElimination φ m ε` on LML's interaction protocol.

## Main definitions

In the namespace `LMLExplore.Bandits.PhasedElimination`:

* `schedule n`, `scheduleArm n j`: the list of the arms pulled by a phase that pulls each arm `a`
  exactly `n a` times, and the arm at its offset `j`.
* `eliminate φ S θ̂ ε`: the arms of `S` kept by the elimination with the estimate `θ̂` and the
  accuracy `ε`.
* `survivors φ m ε y ℓ`, `phaseStart φ m ε y ℓ`, `phaseEstimate φ m ε y ℓ`: the surviving arms, the
  first round and the least-squares estimate of phase `ℓ` for the rewards `y`.
* `phaseOf φ m ε y t`, `armAt φ m ε y t`: the phase of round `t` and the arm pulled at round `t`.

In the namespace `LMLExplore.Bandits`:

* `phasedElimination φ m ε`: phased elimination as a deterministic algorithm.

## Main statements

In the namespace `LMLExplore.Bandits.PhasedElimination`:

* `sum_range_scheduleArm`: summing over a phase that pulls each arm `a` exactly `n a` times sums
  each arm `n a` times; `designOp_scheduleArm`: its design operator is `∑_a n a • φ a ⊗ φ a`.
* `mem_eliminate_of_forall_inner_le`, `inner_sub_le_of_mem_eliminate`: with an `ε`-accurate
  estimate, the elimination keeps the best arms and only keeps arms with gaps at most `4 ε`.
* `armAt_phaseStart_add`: the arm pulled `j` rounds after the start of phase `ℓ` is the arm at
  offset `j` of its schedule; `armAt_congr`: the arm pulled at round `t` only depends on the
  rewards of the rounds before `t`.
* `sum_range_phaseStart_eq`: the sum over the rounds of the first `ℓ` phases of a function of the
  arms pulled is `∑_{i < ℓ} ∑_a m i S_i a • f a`.
* `mem_survivors_of_forall_inner_le`, `inner_sub_le_of_mem_survivors_succ`: if the first phases are
  accurate, an optimal arm survives them and the arms surviving phase `ℓ` have gaps at most
  `4 ε_ℓ`.
* `sum_range_phaseStart_inner_sub_armAt_le`: the regret of the first `ℓ + 1` phases is at most
  `n_0 G + ∑_{i < ℓ} 4 ε_i n_{i+1}` if the first `ℓ` phases are accurate.

Along the runs of `phasedElimination φ m ε`, in the same namespace:

* `action_ae_eq`: the run lemma: the arm of round `t` is `armAt φ m ε Y t` for the rewards `Y` of
  the run.
* `phaseEstimate_ae_eq_leastSquaresEstimate`: the estimate of phase `ℓ` is the least-squares
  estimate of the features and the rewards of the rounds of that phase.
* `linearRegret_phaseStart_le`: if the first `ℓ` phases are accurate, the random regret of the
  first `ℓ + 1` phases is at most `n_0 G + ∑_{i < ℓ} 4 ε_i n_{i+1}`.

## Implementation notes

The rounds of a phase pull the arms in the order of the list `Finset.univ.toList`; the analysis
only uses the numbers of pulls. The phase of round `t` is the last phase `ℓ ≤ t` that starts at or
before `t`, which is the phase containing `t` when every phase with a nonempty set of survivors
pulls at least one arm.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 22 (Algorithm 12 and the proof of Theorem 22.1).
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning
open InnerProductSpace
open scoped InnerProductSpace

namespace LMLExplore.Bandits

namespace PhasedElimination

variable {α E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Schedules -/

section Schedule

variable [Fintype α]

/-- The **schedule** of a phase that pulls each arm `a` exactly `n a` times: the list of the arms
in which each arm `a` appears `n a` times, the arms being taken in the order of
`Finset.univ.toList`. -/
noncomputable def schedule (n : α → ℕ) : List α :=
  univ.toList.flatMap fun a ↦ List.replicate (n a) a

lemma schedule_def (n : α → ℕ) :
    schedule n = univ.toList.flatMap fun a ↦ List.replicate (n a) a :=
  (rfl)

/-- The schedule of a phase that pulls each arm `a` exactly `n a` times has length `∑ a, n a`. -/
@[simp]
lemma length_schedule (n : α → ℕ) : (schedule n).length = ∑ a, n a := by
  simp [schedule_def, List.length_flatMap, sum_map_toList]

/-- An arm appears in the schedule of a phase iff the phase pulls it at least once. -/
@[simp]
lemma mem_schedule {n : α → ℕ} {a : α} : a ∈ schedule n ↔ n a ≠ 0 := by
  simp [schedule_def, List.mem_flatMap, List.mem_replicate]

/-- Summing a function of the arms along the schedule of a phase that pulls each arm `a` exactly
`n a` times sums each arm `n a` times. -/
lemma sum_map_schedule {M : Type*} [AddCommMonoid M] (n : α → ℕ) (f : α → M) :
    ((schedule n).map f).sum = ∑ a, n a • f a := by
  simp [schedule_def, List.flatMap, List.map_flatten, List.sum_flatten, Function.comp_def,
    sum_map_toList]

variable [Nonempty α]

/-- The arm at offset `j` of the schedule of a phase that pulls each arm `a` exactly `n a` times,
and an arbitrary arm from the offset `∑ a, n a` on. -/
noncomputable def scheduleArm (n : α → ℕ) (j : ℕ) : α :=
  (schedule n).getD j (Classical.arbitrary α)

lemma scheduleArm_def (n : α → ℕ) (j : ℕ) :
    scheduleArm n j = (schedule n).getD j (Classical.arbitrary α) :=
  (rfl)

/-- **Sums over a phase.** Summing a function of the arms over the `∑ a, n a` rounds of a phase
that pulls each arm `a` exactly `n a` times sums each arm `n a` times. -/
theorem sum_range_scheduleArm {M : Type*} [AddCommMonoid M] (n : α → ℕ) (f : α → M) :
    ∑ j ∈ range (∑ a, n a), f (scheduleArm n j) = ∑ a, n a • f a := by
  rw [← length_schedule, ← sum_map_schedule, ← Fin.sum_univ_fun_getElem, sum_range]
  exact Fintype.sum_congr _ _ fun j ↦ by rw [scheduleArm_def, List.getD_eq_getElem _ _ j.2]

/-- A phase that pulls each arm `a` exactly `n a` times pulls the arm `a` at exactly `n a` of its
rounds. -/
theorem card_filter_scheduleArm_eq [DecidableEq α] (n : α → ℕ) (a : α) :
    #{j ∈ range (∑ b, n b) | scheduleArm n j = a} = n a := by
  rw [card_filter, sum_range_scheduleArm n fun b ↦ if b = a then 1 else 0]
  simp

/-- The arms pulled during a phase that pulls each arm `a` exactly `n a` times are arms with
`n a ≠ 0`. -/
theorem scheduleArm_ne_zero {n : α → ℕ} {j : ℕ} (hj : j < ∑ a, n a) : n (scheduleArm n j) ≠ 0 := by
  rw [← length_schedule] at hj
  rw [← mem_schedule, scheduleArm_def, List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

/-- The design operator `∑_{j < ∑ n} φ_j ⊗ φ_j` of the features of the arms pulled by a phase that
pulls each arm `a` exactly `n a` times is `∑_a n a • φ a ⊗ φ a`. -/
theorem designOp_scheduleArm (φ : α → E) (n : α → ℕ) :
    designOp 0 (fun j ↦ φ (scheduleArm n j)) (∑ a, n a) =
      ∑ a, (n a : ℝ) • rankOne ℝ (φ a) (φ a) := by
  rw [designOp_def, zero_add, sum_range_scheduleArm n fun a ↦ rankOne ℝ (φ a) (φ a)]
  simp_rw [Nat.cast_smul_eq_nsmul]

end Schedule

/-! ### Elimination -/

section Eliminate

variable {φ : α → E} {S : Finset α} {θ θ' : E} {ε : ℝ} {a b : α}

open scoped Classical in
/-- The arms of `S` kept by the **elimination** with the estimate `θ'` and the accuracy `ε`: the
arms `a ∈ S` whose estimated reward `⟪θ', φ a⟫` is within `2 ε` of the estimated reward of every
arm of `S`. -/
noncomputable def eliminate (φ : α → E) (S : Finset α) (θ' : E) (ε : ℝ) : Finset α :=
  {a ∈ S | ∀ b ∈ S, ⟪θ', φ b - φ a⟫_ℝ ≤ 2 * ε}

@[simp]
lemma mem_eliminate :
    a ∈ eliminate φ S θ' ε ↔ a ∈ S ∧ ∀ b ∈ S, ⟪θ', φ b - φ a⟫_ℝ ≤ 2 * ε := by
  classical
  simp [eliminate]

lemma eliminate_subset (φ : α → E) (S : Finset α) (θ' : E) (ε : ℝ) : eliminate φ S θ' ε ⊆ S :=
  fun _ ha ↦ (mem_eliminate.1 ha).1

/-- For a nonnegative accuracy, the elimination keeps an arm of largest estimated reward, so it
keeps a nonempty set nonempty. -/
lemma eliminate_nonempty (hS : S.Nonempty) (hε : 0 ≤ ε) : (eliminate φ S θ' ε).Nonempty := by
  obtain ⟨a, ha, hmax⟩ := S.exists_max_image (fun b ↦ ⟪θ', φ b⟫_ℝ) hS
  refine ⟨a, mem_eliminate.2 ⟨ha, fun b hb ↦ ?_⟩⟩
  rw [inner_sub_right]
  linarith [hmax b hb]

/-- With an estimate `θ'` that is `ε`-accurate on `S`, the estimated gaps are within `2 ε` of the
true gaps: `⟪θ', φ b - φ a⟫ ≤ ⟪θ, φ b - φ a⟫ + 2 ε`. -/
private lemma inner_sub_le_inner_sub_add (hacc : ∀ c ∈ S, |⟪θ' - θ, φ c⟫_ℝ| ≤ ε) (ha : a ∈ S)
    (hb : b ∈ S) : ⟪θ', φ b - φ a⟫_ℝ ≤ ⟪θ, φ b - φ a⟫_ℝ + 2 * ε := by
  have h₁ := abs_le.1 (hacc a ha)
  have h₂ := abs_le.1 (hacc b hb)
  simp only [inner_sub_left, inner_sub_right] at h₁ h₂ ⊢
  linarith [h₁.1, h₂.2]

/-- **The elimination keeps the best arms.** With an estimate that is `ε`-accurate on `S`, an arm
of `S` of largest expected reward among the arms of `S` survives the elimination. -/
theorem mem_eliminate_of_forall_inner_le (hacc : ∀ c ∈ S, |⟪θ' - θ, φ c⟫_ℝ| ≤ ε) (ha : a ∈ S)
    (hopt : ∀ b ∈ S, ⟪θ, φ b⟫_ℝ ≤ ⟪θ, φ a⟫_ℝ) : a ∈ eliminate φ S θ' ε := by
  refine mem_eliminate.2 ⟨ha, fun b hb ↦ ?_⟩
  have h := inner_sub_le_inner_sub_add hacc ha hb
  rw [inner_sub_right θ] at h
  linarith [hopt b hb]

/-- **The elimination removes the bad arms.** With an estimate that is `ε`-accurate on `S`, every
arm kept by the elimination has a gap at most `4 ε` to every arm of `S`. -/
theorem inner_sub_le_of_mem_eliminate (hacc : ∀ c ∈ S, |⟪θ' - θ, φ c⟫_ℝ| ≤ ε)
    (ha : a ∈ eliminate φ S θ' ε) (hb : b ∈ S) : ⟪θ, φ b - φ a⟫_ℝ ≤ 4 * ε := by
  obtain ⟨ha, hle⟩ := mem_eliminate.1 ha
  have h₁ := abs_le.1 (hacc a ha)
  have h₂ := abs_le.1 (hacc b hb)
  have h := hle b hb
  simp only [inner_sub_left, inner_sub_right] at h₁ h₂ h ⊢
  linarith [h₁.2, h₂.1]

end Eliminate

variable [Fintype α]

/-! ### Phases -/

section Phases

variable [FiniteDimensional ℝ E] [Nonempty α]
  (φ : α → E) (m : ℕ → Finset α → α → ℕ) (ε : ℕ → ℝ) (y : ℕ → ℝ)

/-- The least-squares estimate at the end of a phase that starts at round `s` and pulls each arm
`a` exactly `n a` times, for the rewards `y`: the unregularized least-squares estimate of the
features of the arms of the schedule and the rewards `y (s + j)` of the rounds `s + j` of the
phase. -/
noncomputable def estimate (n : α → ℕ) (s : ℕ) : E :=
  leastSquaresEstimate 0 (fun j ↦ φ (scheduleArm n j)) (fun j ↦ y (s + j)) (∑ a, n a)

lemma estimate_def (n : α → ℕ) (s : ℕ) :
    estimate φ y n s =
      leastSquaresEstimate 0 (fun j ↦ φ (scheduleArm n j)) (fun j ↦ y (s + j)) (∑ a, n a) :=
  (rfl)

/-- The surviving arms and the first round of the phase `ℓ` of phased elimination with numbers of
pulls `m` and accuracies `ε`, for the rewards `y`. Phase `0` starts at round `0` with all the arms;
phase `ℓ` pulls each arm `a` exactly `m ℓ S_ℓ a` times, where `S_ℓ` is its set of survivors, and
its survivors that `eliminate` keeps with the estimate of the phase and the accuracy `ε ℓ` are the
survivors of phase `ℓ + 1`. -/
noncomputable def phase : ℕ → Finset α × ℕ
  | 0 => (univ, 0)
  | ℓ + 1 =>
    (eliminate φ (phase ℓ).1 (estimate φ y (m ℓ (phase ℓ).1) (phase ℓ).2) (ε ℓ),
      (phase ℓ).2 + ∑ a, m ℓ (phase ℓ).1 a)

/-- The arms that survive the first `ℓ` phases of phased elimination, for the rewards `y`. -/
noncomputable def survivors (ℓ : ℕ) : Finset α :=
  (phase φ m ε y ℓ).1

/-- The first round of the phase `ℓ` of phased elimination, for the rewards `y`. -/
noncomputable def phaseStart (ℓ : ℕ) : ℕ :=
  (phase φ m ε y ℓ).2

/-- The least-squares estimate computed at the end of the phase `ℓ` of phased elimination, for the
rewards `y`. -/
noncomputable def phaseEstimate (ℓ : ℕ) : E :=
  estimate φ y (m ℓ (survivors φ m ε y ℓ)) (phaseStart φ m ε y ℓ)

lemma phase_eq (ℓ : ℕ) : phase φ m ε y ℓ = (survivors φ m ε y ℓ, phaseStart φ m ε y ℓ) :=
  (rfl)

lemma phaseEstimate_def (ℓ : ℕ) :
    phaseEstimate φ m ε y ℓ =
      estimate φ y (m ℓ (survivors φ m ε y ℓ)) (phaseStart φ m ε y ℓ) :=
  (rfl)

@[simp]
lemma survivors_zero : survivors φ m ε y 0 = univ := (rfl)

@[simp]
lemma phaseStart_zero : phaseStart φ m ε y 0 = 0 := (rfl)

lemma survivors_succ (ℓ : ℕ) :
    survivors φ m ε y (ℓ + 1) =
      eliminate φ (survivors φ m ε y ℓ) (phaseEstimate φ m ε y ℓ) (ε ℓ) :=
  (rfl)

lemma phaseStart_succ (ℓ : ℕ) :
    phaseStart φ m ε y (ℓ + 1) = phaseStart φ m ε y ℓ + ∑ a, m ℓ (survivors φ m ε y ℓ) a :=
  (rfl)

lemma survivors_succ_subset (ℓ : ℕ) : survivors φ m ε y (ℓ + 1) ⊆ survivors φ m ε y ℓ :=
  eliminate_subset _ _ _ _

lemma antitone_survivors : Antitone (survivors φ m ε y) :=
  antitone_nat_of_succ_le (survivors_succ_subset φ m ε y)

lemma monotone_phaseStart : Monotone (phaseStart φ m ε y) :=
  monotone_nat_of_le_succ fun ℓ ↦ by rw [phaseStart_succ]; exact Nat.le_add_right _ _

variable {φ m ε y}

/-- For nonnegative accuracies, the set of survivors is never empty. -/
lemma survivors_nonempty (hε : ∀ ℓ, 0 ≤ ε ℓ) (ℓ : ℕ) : (survivors φ m ε y ℓ).Nonempty := by
  induction ℓ with
  | zero => exact univ_nonempty
  | succ ℓ ih => exact eliminate_nonempty ih (hε ℓ)

/-- If every phase with a nonempty set of survivors pulls at least one arm and the accuracies are
nonnegative, phase `ℓ` starts at round `ℓ` or later. -/
lemma le_phaseStart (hε : ∀ ℓ, 0 ≤ ε ℓ) (hm : ∀ ℓ S, S.Nonempty → 0 < ∑ a, m ℓ S a) (ℓ : ℕ) :
    ℓ ≤ phaseStart φ m ε y ℓ := by
  induction ℓ with
  | zero => exact le_rfl
  | succ ℓ ih =>
    rw [phaseStart_succ]
    have := hm ℓ _ (survivors_nonempty (φ := φ) (m := m) (y := y) hε ℓ)
    omega

/-- The estimate of a phase that starts at round `s` and pulls each arm `a` exactly `n a` times
only depends on the rewards of its rounds `s + j`, `j < ∑ a, n a`. -/
lemma estimate_congr {y' : ℕ → ℝ} {n : α → ℕ} {s : ℕ}
    (h : ∀ j < ∑ a, n a, y (s + j) = y' (s + j)) : estimate φ y n s = estimate φ y' n s :=
  leastSquaresEstimate_congr (fun _ _ ↦ rfl) h

/-- The survivors and the first round of phase `ℓ` only depend on the rewards of the rounds before
the start of phase `ℓ`. -/
lemma survivors_eq_and_phaseStart_eq {y' : ℕ → ℝ} {ℓ : ℕ}
    (h : ∀ s < phaseStart φ m ε y ℓ, y s = y' s) :
    survivors φ m ε y ℓ = survivors φ m ε y' ℓ ∧ phaseStart φ m ε y ℓ = phaseStart φ m ε y' ℓ := by
  induction ℓ with
  | zero => exact ⟨rfl, rfl⟩
  | succ ℓ ih =>
    obtain ⟨hS, hs⟩ := ih fun s hs ↦ h s (hs.trans_le (monotone_phaseStart φ m ε y ℓ.le_succ))
    rw [survivors_succ, survivors_succ, phaseStart_succ, phaseStart_succ, phaseEstimate_def,
      phaseEstimate_def, ← hS, ← hs,
      estimate_congr fun j hj ↦ h _ (by rw [phaseStart_succ]; omega)]
    exact ⟨rfl, rfl⟩

/-- If two reward sequences agree before round `t`, then a phase starts at or before `t` for one
iff it does for the other. -/
lemma phaseStart_le_iff_of_eq {y' : ℕ → ℝ} {t ℓ : ℕ} (h : ∀ s < t, y s = y' s) :
    phaseStart φ m ε y ℓ ≤ t ↔ phaseStart φ m ε y' ℓ ≤ t := by
  refine ⟨fun hℓ ↦ ?_, fun hℓ ↦ ?_⟩
  · rwa [← (survivors_eq_and_phaseStart_eq fun s hs ↦ h s (hs.trans_le hℓ)).2]
  · rwa [← (survivors_eq_and_phaseStart_eq fun s hs ↦ (h s (hs.trans_le hℓ)).symm).2]

variable (φ m ε y)

/-- The **phase of round `t`**: the last phase `ℓ ≤ t` that starts at or before round `t`. -/
noncomputable def phaseOf (t : ℕ) : ℕ :=
  Nat.findGreatest (fun ℓ ↦ phaseStart φ m ε y ℓ ≤ t) t

/-- The **arm pulled at round `t`** by phased elimination for the rewards `y`: the arm at the
offset `t - phaseStart ℓ` of the schedule of the phase `ℓ` of round `t`. -/
noncomputable def armAt (t : ℕ) : α :=
  scheduleArm (m (phaseOf φ m ε y t) (survivors φ m ε y (phaseOf φ m ε y t)))
    (t - phaseStart φ m ε y (phaseOf φ m ε y t))

lemma phaseOf_def (t : ℕ) :
    phaseOf φ m ε y t = Nat.findGreatest (fun ℓ ↦ phaseStart φ m ε y ℓ ≤ t) t :=
  (rfl)

lemma armAt_def (t : ℕ) :
    armAt φ m ε y t = scheduleArm (m (phaseOf φ m ε y t) (survivors φ m ε y (phaseOf φ m ε y t)))
      (t - phaseStart φ m ε y (phaseOf φ m ε y t)) :=
  (rfl)

variable {φ m ε y}

/-- The phase of round `t` is at most `t`. -/
lemma phaseOf_le (t : ℕ) : phaseOf φ m ε y t ≤ t :=
  Nat.findGreatest_le t

/-- The phase of round `t` starts at or before round `t`. -/
lemma phaseStart_phaseOf_le (t : ℕ) : phaseStart φ m ε y (phaseOf φ m ε y t) ≤ t :=
  Nat.findGreatest_spec (P := fun ℓ ↦ phaseStart φ m ε y ℓ ≤ t) (Nat.zero_le t) (by simp)

/-- A round `t` with `phaseStart ℓ ≤ t < phaseStart (ℓ + 1)` belongs to phase `ℓ`. -/
lemma phaseOf_eq (hε : ∀ ℓ, 0 ≤ ε ℓ) (hm : ∀ ℓ S, S.Nonempty → 0 < ∑ a, m ℓ S a) {t ℓ : ℕ}
    (h₁ : phaseStart φ m ε y ℓ ≤ t) (h₂ : t < phaseStart φ m ε y (ℓ + 1)) :
    phaseOf φ m ε y t = ℓ := by
  have hℓt : ℓ ≤ t := (le_phaseStart hε hm ℓ).trans h₁
  refine le_antisymm ?_ (Nat.le_findGreatest hℓt h₁)
  by_contra! hlt
  exact h₂.not_ge ((monotone_phaseStart φ m ε y hlt).trans (phaseStart_phaseOf_le t))

/-- The arm pulled `j` rounds after the start of phase `ℓ`, for `j` less than the length
`∑ a, m ℓ S_ℓ a` of the phase, is the arm at offset `j` of the schedule of phase `ℓ`. -/
theorem armAt_phaseStart_add (hε : ∀ ℓ, 0 ≤ ε ℓ) (hm : ∀ ℓ S, S.Nonempty → 0 < ∑ a, m ℓ S a)
    {ℓ j : ℕ} (hj : j < ∑ a, m ℓ (survivors φ m ε y ℓ) a) :
    armAt φ m ε y (phaseStart φ m ε y ℓ + j) = scheduleArm (m ℓ (survivors φ m ε y ℓ)) j := by
  rw [armAt_def, phaseOf_eq hε hm (Nat.le_add_right _ _) (by rw [phaseStart_succ]; omega),
    Nat.add_sub_cancel_left]

/-- The arm pulled at round `t` only depends on the rewards of the rounds before `t`. -/
theorem armAt_congr {y' : ℕ → ℝ} {t : ℕ} (h : ∀ s < t, y s = y' s) :
    armAt φ m ε y t = armAt φ m ε y' t := by
  have hphase : phaseOf φ m ε y t = phaseOf φ m ε y' t := by
    rw [phaseOf_def, phaseOf_def]
    simp only [phaseStart_le_iff_of_eq h]
  obtain ⟨hS, hs⟩ := survivors_eq_and_phaseStart_eq (ℓ := phaseOf φ m ε y t) fun s hs ↦
    h s (hs.trans_le (phaseStart_phaseOf_le t))
  rw [armAt_def, armAt_def, ← hphase, hS, hs]

/-- **Sums over the first phases.** The sum of a function of the arms pulled during the rounds of
the first `ℓ` phases is `∑_{i < ℓ} ∑_a m i S_i a • f a`. -/
theorem sum_range_phaseStart_eq {M : Type*} [AddCommMonoid M] (hε : ∀ ℓ, 0 ≤ ε ℓ)
    (hm : ∀ ℓ S, S.Nonempty → 0 < ∑ a, m ℓ S a) (f : α → M) (ℓ : ℕ) :
    ∑ t ∈ range (phaseStart φ m ε y ℓ), f (armAt φ m ε y t) =
      ∑ i ∈ range ℓ, ∑ a, m i (survivors φ m ε y i) a • f a := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [phaseStart_succ, sum_range_add, ih, sum_range_succ,
      ← sum_range_scheduleArm (m ℓ (survivors φ m ε y ℓ)) f]
    congr 1
    exact sum_congr rfl fun j hj ↦ by rw [armAt_phaseStart_add hε hm (mem_range.1 hj)]

/-- **An optimal arm survives accurate phases.** If the estimates of the first `ℓ` phases are
accurate on their survivors, `|⟪θ̂_i - θ, φ b⟫| ≤ ε i` for `i < ℓ` and `b ∈ S_i`, then an arm of
largest expected reward survives the first `ℓ` phases. -/
theorem mem_survivors_of_forall_inner_le {θ : E} {a : α} (hopt : ∀ b, ⟪θ, φ b⟫_ℝ ≤ ⟪θ, φ a⟫_ℝ)
    {ℓ : ℕ} (hacc : ∀ i < ℓ, ∀ b ∈ survivors φ m ε y i,
      |⟪phaseEstimate φ m ε y i - θ, φ b⟫_ℝ| ≤ ε i) :
    a ∈ survivors φ m ε y ℓ := by
  induction ℓ with
  | zero => exact mem_univ a
  | succ ℓ ih =>
    exact mem_eliminate_of_forall_inner_le (hacc ℓ ℓ.lt_succ_self)
      (ih fun i hi ↦ hacc i (hi.trans ℓ.lt_succ_self)) fun b _ ↦ hopt b

/-- **The survivors of accurate phases have small gaps.** If the estimates of the first `ℓ + 1`
phases are accurate on their survivors, then every arm that survives them has a gap at most
`4 ε ℓ` to an arm of largest expected reward. -/
theorem inner_sub_le_of_mem_survivors_succ {θ : E} {a b : α}
    (hopt : ∀ c, ⟪θ, φ c⟫_ℝ ≤ ⟪θ, φ a⟫_ℝ) {ℓ : ℕ}
    (hacc : ∀ i < ℓ + 1, ∀ c ∈ survivors φ m ε y i,
      |⟪phaseEstimate φ m ε y i - θ, φ c⟫_ℝ| ≤ ε i)
    (hb : b ∈ survivors φ m ε y (ℓ + 1)) : ⟪θ, φ a - φ b⟫_ℝ ≤ 4 * ε ℓ :=
  inner_sub_le_of_mem_eliminate (hacc ℓ ℓ.lt_succ_self) hb
    (mem_survivors_of_forall_inner_le hopt fun i hi ↦ hacc i (hi.trans ℓ.lt_succ_self))

/-- **Regret of accurate phases.** Suppose that every phase pulls only surviving arms, and at least
one arm when its set of survivors is not empty, and that the accuracies are nonnegative. If the
estimates of the first `ℓ` phases are accurate on their survivors, `a` is an arm of largest
expected reward and `G` bounds the gaps of all the arms, then the regret of the first `ℓ + 1`
phases is at most `n_0 G + ∑_{i < ℓ} 4 ε_i n_{i+1}`, where `n_i = ∑_b m i S_i b` is the length of
phase `i`. This is the pathwise part of the proof of [LS, Theorem 22.1]. -/
theorem sum_range_phaseStart_inner_sub_armAt_le (hε : ∀ ℓ, 0 ≤ ε ℓ)
    (hm : ∀ ℓ S, S.Nonempty → 0 < ∑ a, m ℓ S a) (hmS : ∀ ℓ S a, a ∉ S → m ℓ S a = 0)
    {θ : E} {a : α} (hopt : ∀ b, ⟪θ, φ b⟫_ℝ ≤ ⟪θ, φ a⟫_ℝ) {G : ℝ}
    (hG : ∀ b, ⟪θ, φ a - φ b⟫_ℝ ≤ G) {ℓ : ℕ}
    (hacc : ∀ i < ℓ, ∀ b ∈ survivors φ m ε y i,
      |⟪phaseEstimate φ m ε y i - θ, φ b⟫_ℝ| ≤ ε i) :
    ∑ t ∈ range (phaseStart φ m ε y (ℓ + 1)), ⟪θ, φ a - φ (armAt φ m ε y t)⟫_ℝ ≤
      (∑ b, m 0 univ b) * G +
        ∑ i ∈ range ℓ, 4 * ε i * ∑ b, m (i + 1) (survivors φ m ε y (i + 1)) b := by
  rw [sum_range_phaseStart_eq hε hm (fun b ↦ ⟪θ, φ a - φ b⟫_ℝ) (ℓ + 1), sum_range_succ',
    survivors_zero, add_comm]
  push_cast
  refine add_le_add ?_ (sum_le_sum fun i hi ↦ ?_)
  · rw [sum_mul]
    exact sum_le_sum fun b _ ↦ by
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hG b) (Nat.cast_nonneg _)
  · rw [mul_sum]
    refine sum_le_sum fun b _ ↦ ?_
    rw [nsmul_eq_mul, mul_comm]
    by_cases hb : b ∈ survivors φ m ε y (i + 1)
    · exact mul_le_mul_of_nonneg_right
        (inner_sub_le_of_mem_survivors_succ hopt
          (fun j hj ↦ hacc j (by have := mem_range.1 hi; omega)) hb) (Nat.cast_nonneg _)
    · simp [hmS _ _ _ hb]

end Phases

/-! ### Measurability -/

section Measurability

variable [FiniteDimensional ℝ E] [Nonempty α] {φ : α → E} {m : ℕ → Finset α → α → ℕ}
  {ε : ℕ → ℝ}

/-- The estimated reward `⟪estimate φ y n s, v⟫` of a direction `v` is a measurable function of
the rewards `y`. -/
lemma measurable_inner_estimate (n : α → ℕ) (s : ℕ) (v : E) :
    Measurable fun y : ℕ → ℝ ↦ ⟪estimate φ y n s, v⟫_ℝ := by
  simp_rw [estimate_def, leastSquaresEstimate_def, map_sum, map_smul, sum_inner,
    real_inner_smul_left]
  exact Finset.measurable_sum _ fun j _ ↦ (measurable_pi_apply _).mul_const _

/-- The set of survivors of an elimination with the estimate of a phase is a measurable function of
the rewards. -/
lemma measurable_eliminate_estimate (S : Finset α) (n : α → ℕ) (s : ℕ) (r : ℝ) :
    Measurable fun y : ℕ → ℝ ↦ eliminate φ S (estimate φ y n s) r := by
  refine measurable_finset_iff.2 fun a ↦ measurableSet_setOfPred.1 ?_
  simp_rw [mem_eliminate]
  by_cases ha : a ∈ S
  · simp only [ha, true_and, Set.ofPred_forall]
    exact MeasurableSet.iInter fun b ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_le (measurable_inner_estimate n s _) measurable_const
  · simp [ha]

variable (φ m ε)

/-- The survivors and the first round of phase `ℓ` are a measurable function of the rewards. -/
lemma measurable_phase (ℓ : ℕ) : Measurable fun y : ℕ → ℝ ↦ phase φ m ε y ℓ := by
  induction ℓ with
  | zero => exact measurable_const
  | succ ℓ ih =>
    have hF : Measurable fun p : (ℕ → ℝ) × (Finset α × ℕ) ↦
        ((eliminate φ p.2.1 (estimate φ p.1 (m ℓ p.2.1) p.2.2) (ε ℓ),
          p.2.2 + ∑ a, m ℓ p.2.1 a) : Finset α × ℕ) :=
      measurable_from_prod_countable_left fun q ↦ by
        simp only
        exact (measurable_eliminate_estimate q.1 (m ℓ q.1) q.2 (ε ℓ)).prodMk measurable_const
    exact hF.comp (measurable_id.prodMk ih)

/-- The arm pulled at round `t` is a measurable function of the rewards. -/
lemma measurable_armAt [MeasurableSpace α] (t : ℕ) :
    Measurable fun y : ℕ → ℝ ↦ armAt φ m ε y t := by
  have hphaseOf : Measurable fun y : ℕ → ℝ ↦ phaseOf φ m ε y t :=
    measurable_findGreatest fun ℓ _ ↦ measurableSet_le
      ((measurable_of_countable Prod.snd).comp (measurable_phase φ m ε ℓ)) measurable_const
  have hF : Measurable fun p : (ℕ → ℝ) × ℕ ↦
      scheduleArm (m p.2 (survivors φ m ε p.1 p.2)) (t - phaseStart φ m ε p.1 p.2) :=
    measurable_from_prod_countable_left fun ℓ ↦
      (measurable_of_countable fun q : Finset α × ℕ ↦ scheduleArm (m ℓ q.1) (t - q.2)).comp
        (measurable_phase φ m ε ℓ)
  exact hF.comp (measurable_id.prodMk hphaseOf)

end Measurability

end PhasedElimination

/-! ### The algorithm -/

section Algorithm

open PhasedElimination

variable {α 𝓞 E : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSpace 𝓞]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {φ : α → E} {m : ℕ → Finset α → α → ℕ} {ε : ℕ → ℝ}

variable (φ m ε) in
/-- **Phased elimination** [LS, Algorithm 12] with features `φ`, numbers of pulls `m` and
accuracies `ε`: the deterministic algorithm that plays at round `t` the arm `armAt φ m ε y t`, for
the rewards `y` of the history. -/
noncomputable def phasedElimination : Algorithm 𝓞 α ℝ :=
  Algorithm.deterministic (fun t p ↦ armAt φ m ε (histReward p.1) t)
    fun t ↦ (measurable_armAt φ m ε t).comp ((measurable_histReward t).comp measurable_fst)

lemma phasedElimination_eq_deterministic :
    phasedElimination (𝓞 := 𝓞) φ m ε =
      Algorithm.deterministic (fun t p ↦ armAt φ m ε (histReward p.1) t)
        fun t ↦ (measurable_armAt φ m ε t).comp ((measurable_histReward t).comp measurable_fst) :=
  (rfl)

namespace PhasedElimination

variable [MeasurableSingletonClass α] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [SFinite P] {env : Environment 𝓞 α ℝ} {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}

/-- **The run lemma of phased elimination.** Along every run of phased elimination, the arm of
every round `t` is `armAt φ m ε Y t` for the sequence `Y` of the rewards of the run. -/
theorem action_ae_eq (h : IsAlgEnvSeq O A Y (phasedElimination φ m ε) env P) :
    ∀ᵐ ω ∂P, ∀ t, A t ω = armAt φ m ε (fun s ↦ Y s ω) t := by
  filter_upwards [h.action_ae_all_eq_deterministic] with ω hω t
  rw [hω t]
  exact armAt_congr fun s hs ↦ histReward_history hs ω

/-- Along every run of phased elimination, the arm pulled `j` rounds after the start of phase `ℓ`
is the arm at offset `j` of the schedule of phase `ℓ`, for `j` less than the length of phase
`ℓ`. -/
theorem action_phaseStart_add_ae_eq (h : IsAlgEnvSeq O A Y (phasedElimination φ m ε) env P)
    (hε : ∀ ℓ, 0 ≤ ε ℓ) (hm : ∀ ℓ S, S.Nonempty → 0 < ∑ a, m ℓ S a) :
    ∀ᵐ ω ∂P, ∀ ℓ, ∀ j < ∑ a, m ℓ (survivors φ m ε (fun s ↦ Y s ω) ℓ) a,
      A (phaseStart φ m ε (fun s ↦ Y s ω) ℓ + j) ω =
        scheduleArm (m ℓ (survivors φ m ε (fun s ↦ Y s ω) ℓ)) j := by
  filter_upwards [action_ae_eq h] with ω hω ℓ j hj
  rw [hω, armAt_phaseStart_add hε hm hj]

/-- **The estimates along a run.** Along every run of phased elimination, the estimate of phase
`ℓ` is the unregularized least-squares estimate of the features `φ (A t)` and the rewards `Y t` of
the rounds `t` of phase `ℓ`. -/
theorem phaseEstimate_ae_eq_leastSquaresEstimate
    (h : IsAlgEnvSeq O A Y (phasedElimination φ m ε) env P)
    (hε : ∀ ℓ, 0 ≤ ε ℓ) (hm : ∀ ℓ S, S.Nonempty → 0 < ∑ a, m ℓ S a) :
    ∀ᵐ ω ∂P, ∀ ℓ, phaseEstimate φ m ε (fun s ↦ Y s ω) ℓ =
      leastSquaresEstimate 0
        (fun j ↦ φ (A (phaseStart φ m ε (fun s ↦ Y s ω) ℓ + j) ω))
        (fun j ↦ Y (phaseStart φ m ε (fun s ↦ Y s ω) ℓ + j) ω)
        (∑ a, m ℓ (survivors φ m ε (fun s ↦ Y s ω) ℓ) a) := by
  filter_upwards [action_phaseStart_add_ae_eq h hε hm] with ω hω ℓ
  rw [phaseEstimate_def, estimate_def]
  exact leastSquaresEstimate_congr (fun j hj ↦ by rw [hω ℓ j hj]) fun _ _ ↦ rfl

/-- **Regret of accurate phases along a run.** Along every run of phased elimination, under the
assumptions of `sum_range_phaseStart_inner_sub_armAt_le`, if the estimates of the first `ℓ` phases
are accurate on their survivors, then the random regret `R̂` of the first `ℓ + 1` phases is at most
`n_0 G + ∑_{i < ℓ} 4 ε_i n_{i+1}`, where `n_i` is the length of phase `i`. -/
theorem linearRegret_phaseStart_le (h : IsAlgEnvSeq O A Y (phasedElimination φ m ε) env P)
    (hε : ∀ ℓ, 0 ≤ ε ℓ) (hm : ∀ ℓ S, S.Nonempty → 0 < ∑ a, m ℓ S a)
    (hmS : ∀ ℓ S a, a ∉ S → m ℓ S a = 0) {θ : E} {a : α}
    (hopt : ∀ b, ⟪θ, φ b⟫_ℝ ≤ ⟪θ, φ a⟫_ℝ) {G : ℝ} (hG : ∀ b, ⟪θ, φ a - φ b⟫_ℝ ≤ G) :
    ∀ᵐ ω ∂P, ∀ ℓ, (∀ i < ℓ, ∀ b ∈ survivors φ m ε (fun s ↦ Y s ω) i,
        |⟪phaseEstimate φ m ε (fun s ↦ Y s ω) i - θ, φ b⟫_ℝ| ≤ ε i) →
      linearRegret (fun _ ↦ φ) θ O A (phaseStart φ m ε (fun s ↦ Y s ω) (ℓ + 1)) ω ≤
        (∑ b, m 0 univ b) * G + ∑ i ∈ range ℓ,
          4 * ε i * ∑ b, m (i + 1) (survivors φ m ε (fun s ↦ Y s ω) (i + 1)) b := by
  have hsup : ⨆ b, ⟪θ, φ b⟫_ℝ = ⟪θ, φ a⟫_ℝ :=
    le_antisymm (ciSup_le hopt) (le_ciSup (Set.finite_range fun b ↦ ⟪θ, φ b⟫_ℝ).bddAbove a)
  filter_upwards [action_ae_eq h] with ω hω ℓ hacc
  refine le_trans (le_of_eq ?_) (sum_range_phaseStart_inner_sub_armAt_le hε hm hmS hopt hG hacc)
  rw [linearRegret_def]
  exact sum_congr rfl fun t _ ↦ by rw [hsup, hω t, inner_sub_right]

end PhasedElimination

end Algorithm

end LMLExplore.Bandits
