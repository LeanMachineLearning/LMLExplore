/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.SuccessiveRejects
public import LMLExplore.Identification.Task.MeanVector
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Median elimination

Median elimination [EMM02, EMM06] is the algorithm for `ε`-best arm identification that proceeds
in phases, `K` being the number of arms. Phase `j` pulls each of the arms that survive the first
`j` phases `t j` times, then eliminates the half of them with the smallest empirical means, computed
from the samples of phase `j` only. After `⌈log₂ K⌉` phases a single arm survives, and it is
recommended. Since the number of arms of each phase is deterministic, so is the number of rounds:
median elimination is a fixed-budget algorithm.

In phase `j`, let `a'` be a best arm among the survivors of the first `j` phases. Every arm that
survives phase `j` has a mean more than `ε_j` below that of `a'` only if the empirical mean of `a'`
is too low, or if at least half of the arms of the phase have an empirical mean too high, by
`ε_j / 2`. By Markov's inequality on the number of arms whose empirical mean is too high, this has
probability at most three times the probability of a deviation by `ε_j / 2` of the empirical mean
of one arm, that is `3 exp(-t j ε_j² / (8 σ2))` for `σ2`-sub-Gaussian arms. The best surviving mean
then loses at most `∑ j, ε_j` over the phases, except with probability at most
`∑ j, 3 exp(-t j ε_j² / (8 σ2))`. With the tolerances `ε_j = (ε / 4) (3 / 4) ^ j` and the numbers
of pulls `t j = ⌈8 σ2 ε_j⁻² log (3 · 2 ^ (j + 1) / δ)⌉` of [EMM02], the output is `ε`-good with
probability at least `1 - δ`: median elimination is `(ε, δ)`-PAC.

## Main definitions

In the namespace `LMLExplore.Identification`:

* `MedianElimination.halve S x`: the arms of `S` that survive the elimination of the `⌊#S / 2⌋`
  arms with the smallest values `x`.
* `MedianElimination.survivors g j`: the arms that survive the first `j` phases, when `g i` gives
  the statistics of the arms in phase `i`.
* `MedianElimination.samplingRule t`: the sampling rule of median elimination with numbers of pulls
  `t`, which pulls the surviving arms in a round robin.
* `medianElimination t`: median elimination with numbers of pulls `t`, as a fixed-budget
  identification algorithm.
* `MedianElimination.pullSchedule σ2 ε δ`: the numbers of pulls of [EMM02].

## Main statements

In the namespace `LMLExplore.Identification`:

* `MedianElimination.measure_exists_forall_mem_halve_add_lt_le`: one phase loses more than `ε` on
  the best mean with probability at most `3 η`, if each sum deviates by `n ε / 2` with probability
  at most `η`.
* `MedianElimination.indepFun_survivors_streamStats`: in the reward stream, the survivors of the
  first `j` phases are independent of the statistics of phase `j`.
* `MedianElimination.measureReal_exists_output_add_lt_le`: along every run, the output has a mean
  more than `∑ j, ε j` below the largest mean with probability at most
  `∑ j, 3 exp(-t j (ε j)² / (8 σ2))`, for any numbers of pulls and tolerances.
* `MedianElimination.measureReal_exists_output_add_lt_le_of_pullSchedule`: with the numbers of
  pulls of [EMM02], the output is not `ε`-good with probability at most `δ` [EMM02, Theorem 4].
* `isDeltaPAC_medianElimination`: median elimination is `δ`-PAC for `ε`-best arm identification.

## Implementation notes

All the arms of a phase are pulled the same number of times during the phase, so the eliminations
compare the sums of rewards during the phase. Ties are broken by LML's `argmin`, through
`SuccessiveRejects.eliminated`. The surviving arms are pulled in the round robin
`Finset.roundRobinOn`.

The correctness is proved in the array model of LML (`Bandits.ArrayModel`), in which the `k`-th
pull of the arm `a` returns the entry `z k a` of an array `z` of independent rewards. Along a run,
every arm that survives the first `j` phases has been pulled `∑ i < j, t i` times after them, so
that its statistic in phase `j` is the sum of the entries of indices
`∑ i < j, t i ≤ k < ∑ i ≤ j, t i` of its row (`streamStats`). These entries are independent of
those that determine the survivors of the first `j` phases, which is the independence across
phases that the analysis of [EMM02] uses. The law of the survivors does not depend on the run
(`measure_survivors_runStats_mem_eq`).

## References

* [EMM02] E. Even-Dar, S. Mannor and Y. Mansour, *PAC bounds for multi-armed bandit and Markov
  decision processes*, COLT 2002, Theorem 4 (median elimination).
* [EMM06] E. Even-Dar, S. Mannor and Y. Mansour, *Action elimination and stopping conditions for
  the multi-armed bandit and reinforcement learning problems*, JMLR 7 (2006), Theorem 10.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real
open scoped ENNReal NNReal

namespace LMLExplore.Identification.MedianElimination

open SuccessiveRejects

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-! ### Halving a set of arms -/

/-- The step of the halving: remove from `T` an arm with the smallest value `x`. -/
noncomputable def halveStep (x : α → ℝ) (T : Finset α) : Finset α := T.erase (eliminated T x)

lemma halveStep_def (x : α → ℝ) (T : Finset α) : halveStep x T = T.erase (eliminated T x) := (rfl)

/-- The arms of `S` that survive the halving by the values `x`: the `⌊#S / 2⌋` arms of `S` with the
smallest values are removed, one at a time, so that `#S - ⌊#S / 2⌋` arms remain. -/
noncomputable def halve (S : Finset α) (x : α → ℝ) : Finset α := (halveStep x)^[#S / 2] S

lemma halve_def (S : Finset α) (x : α → ℝ) : halve S x = (halveStep x)^[#S / 2] S := (rfl)

lemma iterate_halveStep_subset (S : Finset α) (x : α → ℝ) (n : ℕ) : (halveStep x)^[n] S ⊆ S := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (erase_subset _ _).trans ih

lemma card_iterate_halveStep (S : Finset α) (x : α → ℝ) {n : ℕ} (hn : n ≤ #S) :
    #((halveStep x)^[n] S) = #S - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih := ih (by omega)
    rw [Function.iterate_succ_apply', halveStep,
      card_erase_of_mem (eliminated_mem (card_pos.1 (by omega)) _), ih]
    omega

/-- An arm removed by the first `n` steps of the halving has a value at most that of every arm
that remains. -/
lemma le_of_notMem_iterate_halveStep {S : Finset α} {x : α → ℝ} {n : ℕ} {a b : α} (ha : a ∈ S)
    (ha' : a ∉ (halveStep x)^[n] S) (hb : b ∈ (halveStep x)^[n] S) : x a ≤ x b := by
  induction n with
  | zero => exact absurd ha ha'
  | succ n ih =>
    rw [Function.iterate_succ_apply', halveStep] at ha' hb
    by_cases han : a ∈ (halveStep x)^[n] S
    · rw [mem_erase, not_and_or, not_not] at ha'
      obtain rfl := ha'.resolve_right (not_not.2 han)
      exact le_of_eliminated_mem han (mem_of_mem_erase hb)
    · exact ih han (mem_of_mem_erase hb)

lemma iterate_halveStep_congr {S : Finset α} {x y : α → ℝ} (h : ∀ a ∈ S, x a = y a) (n : ℕ) :
    (halveStep x)^[n] S = (halveStep y)^[n] S := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, halveStep, halveStep,
      eliminated_def, eliminated_def]
    congr 2
    funext a
    split_ifs with ha
    · rw [h a (iterate_halveStep_subset S y n ha)]
    · rfl

lemma halve_subset (S : Finset α) (x : α → ℝ) : halve S x ⊆ S := iterate_halveStep_subset S x _

@[simp]
lemma card_halve (S : Finset α) (x : α → ℝ) : #(halve S x) = #S - #S / 2 :=
  card_iterate_halveStep S x (Nat.div_le_self _ _)

/-- An arm of `S` removed by the halving has a value at most that of every arm that remains. -/
lemma le_of_notMem_halve {S : Finset α} {x : α → ℝ} {a b : α} (ha : a ∈ S) (ha' : a ∉ halve S x)
    (hb : b ∈ halve S x) : x a ≤ x b :=
  le_of_notMem_iterate_halveStep ha ha' hb

/-- The halving of `S` only depends on the values of the arms of `S`. -/
lemma halve_congr {S : Finset α} {x y : α → ℝ} (h : ∀ a ∈ S, x a = y a) :
    halve S x = halve S y :=
  iterate_halveStep_congr h _

lemma measurable_halve [MeasurableSpace α] [MeasurableSingletonClass α] (S : Finset α) :
    Measurable (halve S) := by
  have h_step (n : ℕ) : Measurable fun x : α → ℝ ↦ (halveStep x)^[n] S := by
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      simp_rw [Function.iterate_succ_apply']
      refine (measurable_from_prod_countable_right (f := fun p : Finset α × (α → ℝ) ↦
        halveStep p.2 p.1) fun T ↦ ?_).comp (ih.prodMk measurable_id)
      simp_rw [halveStep_def, eliminated_def]
      refine (measurable_of_countable fun a : α ↦ T.erase a).comp ?_
      refine (measurable_argmin (ι := α) (α := EReal)).comp (Measurable.of_eval fun a ↦ ?_)
      exact Measurable.ite (MeasurableSet.const _)
        (measurable_coe_real_ereal.comp (measurable_pi_apply a)) measurable_const
  exact h_step _

/-! ### Phases -/

/-- The number of arms that survive the first `j` phases of median elimination with `K` arms: each
phase keeps `k - ⌊k / 2⌋ = ⌈k / 2⌉` of its `k` arms. -/
def armsCount (K : ℕ) : ℕ → ℕ
  | 0 => K
  | j + 1 => armsCount K j - armsCount K j / 2

@[simp]
lemma armsCount_zero (K : ℕ) : armsCount K 0 = K := (rfl)

lemma armsCount_succ (K j : ℕ) : armsCount K (j + 1) = armsCount K j - armsCount K j / 2 := (rfl)

/-- `⌈K / 2 ^ j⌉` arms survive the first `j` phases. -/
lemma armsCount_eq (K j : ℕ) : armsCount K j = (K + 2 ^ j - 1) / 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h2 : 0 < 2 ^ j := Nat.two_pow_pos j
    rw [armsCount_succ, ih, pow_succ, ← Nat.div_div_eq_div_mul,
      show K + 2 ^ j * 2 - 1 = (K + 2 ^ j - 1) + 2 ^ j * 1 by omega, Nat.add_mul_div_left _ _ h2]
    omega

/-- The number of phases of median elimination with `K` arms, `⌈log₂ K⌉`: after it, a single arm
survives. -/
def numPhases (K : ℕ) : ℕ := Nat.clog 2 K

lemma numPhases_def (K : ℕ) : numPhases K = Nat.clog 2 K := (rfl)

/-- A single arm survives the `⌈log₂ K⌉` phases of median elimination. -/
lemma armsCount_numPhases {K : ℕ} (hK : 0 < K) : armsCount K (numPhases K) = 1 := by
  have h := Nat.le_pow_clog one_lt_two K
  rw [armsCount_eq, numPhases]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- The number of rounds of the first `j` phases of median elimination with `K` arms, when each
arm that survives the first `i` phases is pulled `t i` times during phase `i`: phase `j` occupies
the rounds from `phaseEnd K t j` to `phaseEnd K t (j + 1)`. Phases are numbered from `0`. -/
def phaseEnd (K : ℕ) (t : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => phaseEnd K t j + armsCount K j * t j

@[simp]
lemma phaseEnd_zero (K : ℕ) (t : ℕ → ℕ) : phaseEnd K t 0 = 0 := (rfl)

lemma phaseEnd_succ (K : ℕ) (t : ℕ → ℕ) (j : ℕ) :
    phaseEnd K t (j + 1) = phaseEnd K t j + armsCount K j * t j := (rfl)

lemma monotone_phaseEnd (K : ℕ) (t : ℕ → ℕ) : Monotone (phaseEnd K t) :=
  monotone_nat_of_le_succ fun j ↦ by rw [phaseEnd_succ]; exact Nat.le_add_right _ _

/-- The number of phases of median elimination completed before round `r`, at most the number
`⌈log₂ K⌉` of phases. -/
def phaseOf (K : ℕ) (t : ℕ → ℕ) (r : ℕ) : ℕ :=
  Nat.findGreatest (fun j ↦ phaseEnd K t j ≤ r) (numPhases K)

lemma phaseOf_def (K : ℕ) (t : ℕ → ℕ) (r : ℕ) :
    phaseOf K t r = Nat.findGreatest (fun j ↦ phaseEnd K t j ≤ r) (numPhases K) := (rfl)

lemma phaseEnd_phaseOf_le (K : ℕ) (t : ℕ → ℕ) (r : ℕ) : phaseEnd K t (phaseOf K t r) ≤ r :=
  Nat.findGreatest_spec (P := fun j ↦ phaseEnd K t j ≤ r) (Nat.zero_le _) (by simp)

/-- A round of the phase `j < ⌈log₂ K⌉` comes after `j` completed phases. -/
lemma phaseOf_eq {K : ℕ} {t : ℕ → ℕ} {j r : ℕ} (hj : j < numPhases K) (h₁ : phaseEnd K t j ≤ r)
    (h₂ : r < phaseEnd K t (j + 1)) : phaseOf K t r = j := by
  refine le_antisymm ?_ (Nat.le_findGreatest hj.le h₁)
  by_contra! h
  exact h₂.not_ge ((monotone_phaseEnd K t h).trans (phaseEnd_phaseOf_le K t r))

/-! ### Survivors -/

/-- The arms that survive the first `j` phases of median elimination, when `g i` gives the
statistics of the arms in phase `i`: phase `i` keeps the half of its arms with the largest
statistics `g i`. -/
noncomputable def survivors (g : ℕ → α → ℝ) : ℕ → Finset α
  | 0 => univ
  | j + 1 => halve (survivors g j) (g j)

@[simp]
lemma survivors_zero (g : ℕ → α → ℝ) : survivors g 0 = univ := (rfl)

lemma survivors_succ (g : ℕ → α → ℝ) (j : ℕ) :
    survivors g (j + 1) = halve (survivors g j) (g j) := (rfl)

lemma survivors_succ_subset (g : ℕ → α → ℝ) (j : ℕ) : survivors g (j + 1) ⊆ survivors g j :=
  halve_subset _ _

lemma card_survivors (g : ℕ → α → ℝ) (j : ℕ) : #(survivors g j) = armsCount (Fintype.card α) j := by
  induction j with
  | zero => simp
  | succ j ih => rw [survivors_succ, card_halve, ih, armsCount_succ]

lemma survivors_nonempty (g : ℕ → α → ℝ) (j : ℕ) : (survivors g j).Nonempty := by
  rw [← card_pos, card_survivors, armsCount_eq]
  exact Nat.div_pos (by have := Fintype.card_pos (α := α); omega) (Nat.two_pow_pos j)

/-- A single arm survives the `⌈log₂ K⌉` phases. -/
lemma card_survivors_numPhases (g : ℕ → α → ℝ) :
    #(survivors g (numPhases (Fintype.card α))) = 1 := by
  rw [card_survivors, armsCount_numPhases Fintype.card_pos]

/-- The survivors of the first `j` phases only depend on the statistics, in each phase `i < j`, of
the arms that survive the first `i` phases. -/
lemma survivors_congr {g g' : ℕ → α → ℝ} {j : ℕ}
    (h : ∀ i < j, ∀ a ∈ survivors g i, g i a = g' i a) : survivors g j = survivors g' j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [survivors_succ, survivors_succ, ← ih fun i hi ↦ h i (by omega)]
    exact halve_congr (h j (by omega))

lemma measurable_survivors [MeasurableSpace α] [MeasurableSingletonClass α] (j : ℕ) :
    Measurable fun g : ℕ → α → ℝ ↦ survivors g j := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    simp_rw [survivors_succ]
    exact (measurable_from_prod_countable_right (f := fun p : Finset α × (α → ℝ) ↦
      halve p.1 p.2) fun S ↦ measurable_halve S).comp (ih.prodMk (measurable_pi_apply j))

/-- The arm played by median elimination at round `r`, when each arm that survives the first `j`
phases is pulled `t j` times during phase `j` and `g i` gives the statistics of the arms in phase
`i`: after `j` completed phases, the round robin over the arms that survive them, started at
round `phaseEnd K t j`. After the last phase, the only surviving arm is played. -/
noncomputable def armAt (t : ℕ → ℕ) (g : ℕ → α → ℝ) (r : ℕ) : α :=
  roundRobinOn (survivors g (phaseOf (Fintype.card α) t r))
    (r - phaseEnd (Fintype.card α) t (phaseOf (Fintype.card α) t r))

lemma armAt_def (t : ℕ → ℕ) (g : ℕ → α → ℝ) (r : ℕ) :
    armAt t g r = roundRobinOn (survivors g (phaseOf (Fintype.card α) t r))
      (r - phaseEnd (Fintype.card α) t (phaseOf (Fintype.card α) t r)) := (rfl)

/-- The arm played at round `r` only depends on the statistics of the phases completed before
`r`. -/
lemma armAt_congr {t : ℕ → ℕ} {g g' : ℕ → α → ℝ} {r : ℕ}
    (h : ∀ i, phaseEnd (Fintype.card α) t (i + 1) ≤ r → g i = g' i) :
    armAt t g r = armAt t g' r := by
  rw [armAt, armAt, survivors_congr fun i hi a _ ↦ by
    rw [h i ((monotone_phaseEnd _ t hi).trans (phaseEnd_phaseOf_le _ t r))]]

/-- During phase `j`, the arm played `r` rounds after the start of the phase is the round robin
over the survivors of the first `j` phases, at offset `r`. -/
lemma armAt_phaseEnd_add (t : ℕ → ℕ) (g : ℕ → α → ℝ) {j r : ℕ}
    (hj : j < numPhases (Fintype.card α)) (hr : r < armsCount (Fintype.card α) j * t j) :
    armAt t g (phaseEnd (Fintype.card α) t j + r) = roundRobinOn (survivors g j) r := by
  rw [armAt, phaseOf_eq hj (Nat.le_add_right _ _) (by rw [phaseEnd_succ]; omega),
    Nat.add_sub_cancel_left]

/-! ### The algorithm -/

/-- The statistics of the arms in each phase `j` of median elimination, computed from a history
`h`: the sum of the rewards of each arm during phase `j`. -/
noncomputable def histStats (t : ℕ → ℕ) {m : ℕ} (h : Hist Unit α ℝ m) (j : ℕ) (a : α) : ℝ :=
  histSum h (phaseEnd (Fintype.card α) t (j + 1)) a - histSum h (phaseEnd (Fintype.card α) t j) a

omit [Nonempty α] in
lemma histStats_def (t : ℕ → ℕ) {m : ℕ} (h : Hist Unit α ℝ m) (j : ℕ) (a : α) :
    histStats t h j a =
      histSum h (phaseEnd (Fintype.card α) t (j + 1)) a -
        histSum h (phaseEnd (Fintype.card α) t j) a := (rfl)

/-- The arm played by median elimination after `r` rounds with history `h`. -/
noncomputable def nextArm (t : ℕ → ℕ) (r : ℕ) (h : Hist Unit α ℝ r) : α :=
  armAt t (histStats t h) r

lemma nextArm_def (t : ℕ → ℕ) (r : ℕ) (h : Hist Unit α ℝ r) :
    nextArm t r h = armAt t (histStats t h) r := (rfl)

/-- The arm recommended by median elimination after the history `h`: the arm that survives the
`⌈log₂ K⌉` phases. -/
noncomputable def recommendation (t : ℕ → ℕ) {T : ℕ} (h : Hist Unit α ℝ T) : α :=
  roundRobinOn (survivors (histStats t h) (numPhases (Fintype.card α))) 0

lemma recommendation_def (t : ℕ → ℕ) {T : ℕ} (h : Hist Unit α ℝ T) :
    recommendation t h =
      roundRobinOn (survivors (histStats t h) (numPhases (Fintype.card α))) 0 := (rfl)

section Measurability

variable [MeasurableSpace α] [MeasurableSingletonClass α]

lemma measurable_survivors_histStats (t : ℕ → ℕ) (m j : ℕ) :
    Measurable fun h : Hist Unit α ℝ m ↦ survivors (histStats t h) j :=
  (measurable_survivors j).comp (Measurable.of_eval fun _ ↦ Measurable.of_eval fun a ↦
    (measurable_histSum m _ a).sub (measurable_histSum m _ a))

lemma measurable_nextArm (t : ℕ → ℕ) (r : ℕ) : Measurable (nextArm (α := α) t r) :=
  (measurable_of_countable fun S : Finset α ↦ roundRobinOn S _).comp
    (measurable_survivors_histStats t r _)

lemma measurable_recommendation (t : ℕ → ℕ) (T : ℕ) :
    Measurable (recommendation (α := α) t (T := T)) :=
  (measurable_of_countable fun S : Finset α ↦ roundRobinOn S 0).comp
    (measurable_survivors_histStats t T _)

/-- The sampling rule of median elimination in which each arm that survives the first `j` phases
is pulled `t j` times during phase `j`: the deterministic algorithm that plays `nextArm t`. -/
noncomputable def samplingRule (t : ℕ → ℕ) : Algorithm Unit α ℝ :=
  Algorithm.deterministic (fun r p ↦ nextArm t r p.1)
    fun r ↦ (measurable_nextArm t r).comp measurable_fst

lemma samplingRule_def (t : ℕ → ℕ) :
    samplingRule (α := α) t = Algorithm.deterministic (fun r p ↦ nextArm t r p.1)
      (fun r ↦ (measurable_nextArm t r).comp measurable_fst) := (rfl)

end Measurability

/-! ### Runs -/

/-- The statistics of the arms in each phase `j` of median elimination along the actions `A` and
rewards `R`: the sum of the rewards of each arm during phase `j`. -/
noncomputable def runStats {Ω : Type*} (t : ℕ → ℕ) (A : ℕ → Ω → α) (R : ℕ → Ω → ℝ) (ω : Ω)
    (j : ℕ) (a : α) : ℝ :=
  sumRewards A R a (phaseEnd (Fintype.card α) t (j + 1)) ω -
    sumRewards A R a (phaseEnd (Fintype.card α) t j) ω

omit [Nonempty α] in
lemma runStats_def {Ω : Type*} (t : ℕ → ℕ) (A : ℕ → Ω → α) (R : ℕ → Ω → ℝ) (ω : Ω) (j : ℕ)
    (a : α) : runStats t A R ω j a = sumRewards A R a (phaseEnd (Fintype.card α) t (j + 1)) ω -
      sumRewards A R a (phaseEnd (Fintype.card α) t j) ω := (rfl)

variable {Ω : Type*} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {t : ℕ → ℕ} {ω : Ω}

/-- Along a run of the sampling rule of median elimination, the arm played at every round is
`armAt t` for the sums of rewards of the arms in the phases. -/
lemma action_ae_eq [MeasurableSpace α] [MeasurableSingletonClass α]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [SFinite P] {O : ℕ → Ω → Unit} {ν : Kernel α ℝ}
    [IsMarkovKernel ν] (h : IsAlgEnvSeq O A R (samplingRule t) (Environment.bandit ν) P) :
    ∀ᵐ ω ∂P, ∀ r, A r ω = armAt t (runStats t A R ω) r := by
  filter_upwards [h.action_ae_all_eq_deterministic] with ω hω r
  rw [hω r, nextArm]
  refine armAt_congr fun i hi ↦ funext fun a ↦ ?_
  rw [histStats, runStats, histSum_history O A R hi ω a,
    histSum_history O A R ((monotone_phaseEnd _ t (Nat.le_succ i)).trans hi) ω a]

/-- If the actions follow median elimination, then during phase `j`, every arm that survives the
first `j` phases is pulled `t j` times. -/
lemma pullCount_phaseEnd_succ_eq_add (hω : ∀ r, A r ω = armAt t (runStats t A R ω) r) {j : ℕ}
    (hj : j < numPhases (Fintype.card α)) {a : α} (ha : a ∈ survivors (runStats t A R ω) j) :
    pullCount A a (phaseEnd (Fintype.card α) t (j + 1)) ω =
      pullCount A a (phaseEnd (Fintype.card α) t j) ω + t j := by
  set K := Fintype.card α
  set S := survivors (runStats t A R ω) j
  have hS : #S = armsCount K j := card_survivors _ j
  rw [phaseEnd_succ, ← hS, pullCount_eq_sum, pullCount_eq_sum, sum_range_add]
  simp only [sum_boole, Nat.cast_id, Nat.add_left_cancel_iff]
  calc #{r ∈ range (#S * t j) | A (phaseEnd K t j + r) ω = a}
  _ = #{r ∈ range (#S * t j) | roundRobinOn S r = a} := by
    refine congrArg card (filter_congr fun r hr ↦ ?_)
    rw [hω, armAt_phaseEnd_add t _ hj (hS ▸ mem_range.1 hr)]
  _ = t j := by simp [card_filter_roundRobinOn_eq, ha]

/-- If the actions follow median elimination, then after the first `j` phases, every arm that
survives them has been pulled `∑ i < j, t i` times. -/
lemma pullCount_phaseEnd (hω : ∀ r, A r ω = armAt t (runStats t A R ω) r) {j : ℕ}
    (hj : j ≤ numPhases (Fintype.card α)) {a : α} (ha : a ∈ survivors (runStats t A R ω) j) :
    pullCount A a (phaseEnd (Fintype.card α) t j) ω = ∑ i ∈ range j, t i := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ha' := survivors_succ_subset _ j ha
    rw [pullCount_phaseEnd_succ_eq_add hω (by omega) ha', ih (by omega) ha', sum_range_succ]

/-! ### Phases of the reward stream -/

/-- The sum of the rewards of the arm `a` in the reward stream `z` (`z k a` is the reward of the
`k`-th pull of `a`) during phase `j` of median elimination: the pulls of indices from
`∑ i < j, t i` to `∑ i ≤ j, t i`. -/
noncomputable def streamStats (t : ℕ → ℕ) (z : ℕ → α → ℝ) (j : ℕ) (a : α) : ℝ :=
  ∑ k ∈ Ico (∑ i ∈ range j, t i) (∑ i ∈ range (j + 1), t i), z k a

omit [Fintype α] [DecidableEq α] [Nonempty α] in
lemma streamStats_def (t : ℕ → ℕ) (z : ℕ → α → ℝ) (j : ℕ) (a : α) :
    streamStats t z j a = ∑ k ∈ Ico (∑ i ∈ range j, t i) (∑ i ∈ range (j + 1), t i), z k a := (rfl)

/-- If the actions follow median elimination and the sums of rewards are sums of entries of a
reward stream `z`, then the survivors of the run are those of the phase statistics of the
stream. -/
lemma survivors_runStats_eq_streamStats (hω : ∀ r, A r ω = armAt t (runStats t A R ω) r)
    {z : ℕ → α → ℝ} (hR : ∀ a n, sumRewards A R a n ω = ∑ k ∈ range (pullCount A a n ω), z k a)
    {j : ℕ} (hj : j ≤ numPhases (Fintype.card α)) :
    survivors (runStats t A R ω) j = survivors (streamStats t z) j := by
  refine survivors_congr fun i hi a ha ↦ ?_
  rw [runStats, hR, hR, pullCount_phaseEnd_succ_eq_add hω (by omega) ha,
    pullCount_phaseEnd hω (by omega) ha, streamStats, sum_range_succ,
    sum_Ico_eq_sub _ (Nat.le_add_right _ _)]

/-! ### One phase -/

/-- **One phase of median elimination** [EMM02, proof of Theorem 4]. Let `S` be a set of arms with
means `μ`, and let `Y a` be the sum of `n ≥ 0` observations of the arm `a`, which deviates from
`n μ a` by `n ε / 2` or more, upwards or downwards, with probability at most `η`. Then the
probability that every arm that survives the halving of `S` by the values `Y` has a mean more than
`ε` below that of an arm of `S` is at most `3 η`. -/
lemma measure_exists_forall_mem_halve_add_lt_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {Y : Ω → α → ℝ} (hY : ∀ a, Measurable fun ω ↦ Y ω a) (S : Finset α)
    (μ : α → ℝ) {n ε : ℝ} (hn : 0 ≤ n) (hε : 0 ≤ ε) {η : ℝ≥0∞}
    (h_up : ∀ a ∈ S, P {ω | n * ε / 2 ≤ Y ω a - n * μ a} ≤ η)
    (h_low : ∀ a ∈ S, P {ω | Y ω a - n * μ a ≤ -(n * ε / 2)} ≤ η) :
    P {ω | ∃ a ∈ S, ∀ b ∈ halve S (Y ω), μ b + ε < μ a} ≤ 3 * η := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  -- The best arm `a'` of `S`.
  obtain ⟨a', ha'S, ha'⟩ := exists_max_image S μ hS
  set m := #S - #S / 2 with hm
  have hm0 : m ≠ 0 := by have := hS.card_pos; omega
  -- The number of arms of `S` whose sum is too high.
  set N : Ω → ℝ≥0∞ := fun ω ↦
    ∑ b ∈ S, {ω | n * ε / 2 ≤ Y ω b - n * μ b}.indicator 1 ω with hN
  have h_meas (b : α) : MeasurableSet {ω | n * ε / 2 ≤ Y ω b - n * μ b} :=
    measurableSet_le measurable_const ((hY b).sub_const _)
  have h_sub : {ω | ∃ a ∈ S, ∀ b ∈ halve S (Y ω), μ b + ε < μ a} ⊆
      {ω | Y ω a' - n * μ a' ≤ -(n * ε / 2)} ∪ {ω | (m : ℝ≥0∞) ≤ N ω} := by
    rintro ω ⟨a, ha, hlt⟩
    have hlt' (b : α) (hb : b ∈ halve S (Y ω)) : μ b + ε < μ a' := (hlt b hb).trans_le (ha' a ha)
    by_cases hlow : Y ω a' - n * μ a' ≤ -(n * ε / 2)
    · exact Or.inl hlow
    refine Or.inr ?_
    -- The best arm is eliminated, so every survivor has a sum at least that of the best arm,
    -- hence too high.
    have ha'h : a' ∉ halve S (Y ω) := fun h ↦ by linarith [hlt' a' h]
    have h_high : halve S (Y ω) ⊆ {b ∈ S | n * ε / 2 ≤ Y ω b - n * μ b} := by
      intro b hb
      have h1 := le_of_notMem_halve ha'S ha'h hb
      have h2 : n * ε ≤ n * (μ a' - μ b) :=
        mul_le_mul_of_nonneg_left (by linarith [hlt' b hb]) hn
      exact mem_filter.2 ⟨halve_subset _ _ hb, by nlinarith⟩
    calc (m : ℝ≥0∞) = #(halve S (Y ω)) := by simp [hm]
    _ ≤ #{b ∈ S | n * ε / 2 ≤ Y ω b - n * μ b} := by exact_mod_cast card_le_card h_high
    _ = N ω := by
      simp only [hN, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
      rw [sum_boole]
  -- Markov's inequality for the number of arms whose sum is too high.
  have h_markov : P {ω | (m : ℝ≥0∞) ≤ N ω} ≤ 2 * η := by
    have h_int : ∫⁻ ω, N ω ∂P ≤ #S * η := by
      rw [lintegral_finsetSum _ fun b _ ↦ (measurable_one.indicator (h_meas b))]
      simp_rw [lintegral_indicator_one (h_meas _)]
      calc ∑ b ∈ S, P {ω | n * ε / 2 ≤ Y ω b - n * μ b} ≤ ∑ _b ∈ S, η := sum_le_sum h_up
      _ = #S * η := by simp
    have h := (mul_meas_ge_le_lintegral₀ (μ := P) (Finset.measurable_sum _ fun b _ ↦
      measurable_one.indicator (h_meas b)).aemeasurable (m : ℝ≥0∞)).trans h_int
    have hS2 : (#S : ℝ≥0∞) * η ≤ m * (2 * η) := by
      rw [← mul_assoc]
      gcongr
      norm_cast
      omega
    exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hm0) (by simp)).1 (h.trans hS2)
  calc P {ω | ∃ a ∈ S, ∀ b ∈ halve S (Y ω), μ b + ε < μ a}
  _ ≤ P {ω | Y ω a' - n * μ a' ≤ -(n * ε / 2)} + P {ω | (m : ℝ≥0∞) ≤ N ω} :=
    (measure_mono h_sub).trans (measure_union_le _ _)
  _ ≤ η + 2 * η := add_le_add (h_low a' ha'S) h_markov
  _ = 3 * η := by ring

/-! ### Independence of the phases of the reward stream -/

omit [Fintype α] [DecidableEq α] [Nonempty α] in
lemma measurable_streamStats (t : ℕ → ℕ) (j : ℕ) :
    Measurable fun z : ℕ → α → ℝ ↦ streamStats t z j := by
  refine measurable_pi_iff.2 fun a ↦ ?_
  simp_rw [streamStats_def]
  fun_prop

omit [Fintype α] [DecidableEq α] [Nonempty α] in
lemma measurable_streamStats_apply (t : ℕ → ℕ) (j : ℕ) (a : α) :
    Measurable fun z : ℕ → α → ℝ ↦ streamStats t z j a :=
  (measurable_pi_apply a).comp (measurable_streamStats t j)

/-- The survivors of the first `j` phases only depend on the entries of the reward stream of
indices less than `∑ i < j, t i`. -/
lemma survivors_streamStats_congr {t : ℕ → ℕ} {z z' : ℕ → α → ℝ} {j : ℕ}
    (h : ∀ k < ∑ i ∈ range j, t i, z k = z' k) :
    survivors (streamStats t z) j = survivors (streamStats t z') j := by
  refine survivors_congr fun i hi a _ ↦ sum_congr rfl fun k hk ↦ ?_
  have hij : ∑ l ∈ range (i + 1), t l ≤ ∑ l ∈ range j, t l :=
    sum_le_sum_of_subset (range_subset_range.2 hi)
  rw [h k ((mem_Ico.1 hk).2.trans_le hij)]

section Stream

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Under the law of the reward stream, the survivors of the first `j` phases are independent of
the statistics of phase `j`, which are computed from the next entries of the stream. -/
lemma indepFun_survivors_streamStats (ν : Kernel α ℝ) [IsMarkovKernel ν] (t : ℕ → ℕ) (j : ℕ) :
    IndepFun (fun z ↦ survivors (streamStats t z) j) (fun z ↦ streamStats t z j)
      (Bandits.streamMeasure ν) := by
  set U := range (∑ i ∈ range j, t i)
  set V := Ico (∑ i ∈ range j, t i) (∑ i ∈ range (j + 1), t i)
  have hUV : Disjoint U V := disjoint_left.2 fun k hU hV ↦ by
    simp only [U, V, mem_range, mem_Ico] at hU hV
    omega
  -- The extension by `0` of the entries of the stream of indices in `U`.
  let ext : (U → α → ℝ) → ℕ → α → ℝ := fun w k ↦ if h : k ∈ U then w ⟨k, h⟩ else 0
  have h_ext : Measurable ext := by
    refine measurable_pi_iff.2 fun k ↦ ?_
    by_cases h : k ∈ U
    · simp only [ext, h, ↓reduceDIte]
      exact measurable_pi_apply _
    · simp only [ext, h, ↓reduceDIte]
      exact measurable_const
  have h_indep := ((Bandits.iIndepFun_eval_streamMeasure' ν).indepFun_finset U V hUV
    fun _ ↦ measurable_pi_apply _).comp
      (φ := fun w ↦ survivors (streamStats t (ext w)) j) (ψ := fun w a ↦ ∑ k : V, w k a)
      ((measurable_survivors j).comp ((Measurable.of_eval fun _ ↦
        measurable_streamStats _ _).comp h_ext))
      (measurable_pi_iff.2 fun a ↦ Finset.measurable_sum _ fun k _ ↦ by fun_prop)
  convert h_indep using 1
  · funext z
    refine survivors_streamStats_congr fun k hk ↦ ?_
    simp [ext, U, hk]
  · funext z a
    exact (sum_coe_sort V fun k ↦ z k a).symm

/-! ### Concentration of the phase statistics -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- For `σ2`-sub-Gaussian arms, the statistic of an arm in phase `j` exceeds `t j` times its mean
by `x ≥ 0` or more with probability at most `exp(-x² / (2 t j σ2))`. -/
lemma measure_le_streamStats_sub_le {ν : Kernel α ℝ} [IsMarkovKernel ν] {σ2 : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (t : ℕ → ℕ) (j : ℕ) (a : α)
    {x : ℝ} (hx : 0 ≤ x) :
    Bandits.streamMeasure ν {z | x ≤ streamStats t z j a - t j * (ν a)[id]} ≤
      ENNReal.ofReal (exp (-x ^ 2 / (2 * t j * σ2))) := by
  have h_eq : {z : ℕ → α → ℝ | x ≤ streamStats t z j a - t j * (ν a)[id]} =
      {z | x ≤ ∑ k ∈ Ico (∑ i ∈ range j, t i) (∑ i ∈ range (j + 1), t i), (z k a - (ν a)[id])} := by
    ext z
    simp [streamStats_def, sum_sub_distrib, sum_range_succ]
  rw [h_eq, ← ofReal_measureReal]
  gcongr
  refine (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (c := fun _ ↦ σ2)
    ((Bandits.iIndepFun_eval_streamMeasure'' ν a).comp (fun _ x ↦ x - (ν a)[id]) (by fun_prop))
    (fun _ _ ↦ (hν a).congr_identDistrib
      ((Bandits.identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _)) hx).trans_eq ?_
  simp [sum_range_succ, mul_assoc]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- For `σ2`-sub-Gaussian arms, the statistic of an arm in phase `j` falls below `t j` times its
mean by `x ≥ 0` or more with probability at most `exp(-x² / (2 t j σ2))`. -/
lemma measure_streamStats_sub_le_le {ν : Kernel α ℝ} [IsMarkovKernel ν] {σ2 : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (t : ℕ → ℕ) (j : ℕ) (a : α)
    {x : ℝ} (hx : 0 ≤ x) :
    Bandits.streamMeasure ν {z | streamStats t z j a - t j * (ν a)[id] ≤ -x} ≤
      ENNReal.ofReal (exp (-x ^ 2 / (2 * t j * σ2))) := by
  have h_eq : {z : ℕ → α → ℝ | streamStats t z j a - t j * (ν a)[id] ≤ -x} =
      {z | x ≤ ∑ k ∈ Ico (∑ i ∈ range j, t i) (∑ i ∈ range (j + 1), t i),
        -(z k a - (ν a)[id])} := by
    ext z
    simp only [Set.mem_ofPred_eq, streamStats_def, sum_neg_distrib, sum_sub_distrib, sum_const,
      Nat.card_Ico, sum_range_succ, Nat.add_sub_cancel_left, nsmul_eq_mul]
    constructor <;> intro h <;> linarith
  rw [h_eq, ← ofReal_measureReal]
  gcongr
  refine (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (c := fun _ ↦ σ2)
    ((Bandits.iIndepFun_eval_streamMeasure'' ν a).comp (fun _ x ↦ -(x - (ν a)[id]))
      (by fun_prop))
    (fun k _ ↦ ((hν a).congr_identDistrib
      ((Bandits.identDistrib_eval_eval_id_streamMeasure ν k a).symm.sub_const _)).neg.congr
        (ae_of_all _ fun z ↦ by simp)) hx).trans_eq ?_
  simp [sum_range_succ, mul_assoc]

/-! ### Correctness on the reward stream -/

/-- **One phase of median elimination** on the reward stream of `σ2`-sub-Gaussian arms
[EMM02, proof of Theorem 4]: the probability that every arm that survives phase `j` has a mean
more than `ε` below that of an arm that survives the first `j` phases is at most
`3 exp(-t j ε² / (8 σ2))`. -/
lemma measure_exists_forall_mem_survivors_succ_add_lt_le {ν : Kernel α ℝ} [IsMarkovKernel ν]
    {σ2 : ℝ≥0} (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (t : ℕ → ℕ)
    (j : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    Bandits.streamMeasure ν {z | ∃ a ∈ survivors (streamStats t z) j,
      ∀ b ∈ survivors (streamStats t z) (j + 1), (ν b)[id] + ε < (ν a)[id]} ≤
      3 * ENNReal.ofReal (exp (-(t j * ε ^ 2) / (8 * σ2))) := by
  set P := Bandits.streamMeasure ν
  set μ : α → ℝ := fun a ↦ (ν a)[id]
  set η := ENNReal.ofReal (exp (-(t j * ε ^ 2) / (8 * σ2)))
  -- The phase fails from the set `S` of arms if the statistics of phase `j` lie in `Bad S`.
  set Bad : Finset α → Set (α → ℝ) := fun S ↦ {y | ∃ a ∈ S, ∀ b ∈ halve S y, μ b + ε < μ a}
  have hBad (S : Finset α) : MeasurableSet (Bad S) :=
    measurable_halve S (MeasurableSet.of_discrete (s := {T : Finset α | ∃ a ∈ S, ∀ b ∈ T,
      μ b + ε < μ a}))
  have h_exp : -(t j * ε / 2) ^ 2 / (2 * t j * σ2) = -(t j * ε ^ 2) / (8 * σ2) := by
    rcases eq_or_ne (t j : ℝ) 0 with ht | ht
    · simp [ht]
    rcases eq_or_ne (σ2 : ℝ) 0 with hσ | hσ
    · simp [hσ]
    field_simp
    ring
  have h_tail (S : Finset α) : P {z | streamStats t z j ∈ Bad S} ≤ 3 * η := by
    refine measure_exists_forall_mem_halve_add_lt_le (fun a ↦ measurable_streamStats_apply t j a)
      S μ (Nat.cast_nonneg (t j)) hε (fun a _ ↦ ?_) (fun a _ ↦ ?_)
    · refine (measure_le_streamStats_sub_le hν t j a (by positivity)).trans_eq ?_
      rw [h_exp]
    · refine (measure_streamStats_sub_le_le hν t j a (by positivity)).trans_eq ?_
      rw [h_exp]
  -- Decompose according to the survivors of the first `j` phases, which are independent of the
  -- statistics of phase `j`.
  calc P {z | ∃ a ∈ survivors (streamStats t z) j,
      ∀ b ∈ survivors (streamStats t z) (j + 1), μ b + ε < μ a}
  _ = P (⋃ S : Finset α, (fun z ↦ survivors (streamStats t z) j) ⁻¹' {S} ∩
      (fun z ↦ streamStats t z j) ⁻¹' Bad S) := by
    congr 1
    ext z
    simp [survivors_succ, Bad]
  _ ≤ ∑ S : Finset α, P ((fun z ↦ survivors (streamStats t z) j) ⁻¹' {S} ∩
      (fun z ↦ streamStats t z j) ⁻¹' Bad S) := measure_iUnion_fintype_le _ _
  _ = ∑ S : Finset α, P ((fun z ↦ survivors (streamStats t z) j) ⁻¹' {S}) *
      P {z | streamStats t z j ∈ Bad S} := by
    refine sum_congr rfl fun S _ ↦ ?_
    exact (indepFun_survivors_streamStats ν t j).measure_inter_preimage_eq_mul _ _
      (measurableSet_singleton S) (hBad S)
  _ ≤ ∑ S : Finset α, P ((fun z ↦ survivors (streamStats t z) j) ⁻¹' {S}) * (3 * η) := by
    gcongr with S
    exact h_tail S
  _ = 3 * η := by
    have h_meas : Measurable fun z ↦ survivors (streamStats t z) j :=
      (measurable_survivors (α := α) j).comp (Measurable.of_eval fun i ↦ measurable_streamStats t i)
    rw [← sum_mul, sum_measure_preimage_singleton (μ := P) univ
      (f := fun z ↦ survivors (streamStats t z) j) fun S _ ↦
      h_meas (measurableSet_singleton S)]
    simp

/-- **Correctness of median elimination on the reward stream** [EMM02, Theorem 4]. For
`σ2`-sub-Gaussian arms and tolerances `ε j ≥ 0`, the probability that the arm surviving the
`⌈log₂ K⌉` phases has a mean more than `∑ j, ε j` below the largest mean is at most
`∑ j, 3 exp(-t j (ε j)² / (8 σ2))`. -/
theorem measure_exists_add_lt_streamStats_le {ν : Kernel α ℝ} [IsMarkovKernel ν] {σ2 : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (t : ℕ → ℕ) {ε : ℕ → ℝ}
    (hε : ∀ j, 0 ≤ ε j) :
    Bandits.streamMeasure ν {z | ∃ b,
      (ν (roundRobinOn (survivors (streamStats t z) (numPhases (Fintype.card α))) 0))[id] +
        ∑ j ∈ range (numPhases (Fintype.card α)), ε j < (ν b)[id]} ≤
      ∑ j ∈ range (numPhases (Fintype.card α)),
        3 * ENNReal.ofReal (exp (-(t j * ε j ^ 2) / (8 * σ2))) := by
  set L := numPhases (Fintype.card α)
  refine (measure_mono ?_).trans ((measure_biUnion_finset_le (range L) _).trans
    (sum_le_sum fun j _ ↦ measure_exists_forall_mem_survivors_succ_add_lt_le hν t j (hε j)))
  rintro z ⟨b, hb⟩
  by_contra h
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, mem_range, not_exists, not_and, not_forall,
    not_lt] at h
  -- If no phase fails, some survivor of each phase `j` is within `∑ i < j, ε i` of `b`.
  have h_key (j : ℕ) (hj : j ≤ L) :
      ∃ c ∈ survivors (streamStats t z) j, (ν b)[id] ≤ (ν c)[id] + ∑ i ∈ range j, ε i := by
    induction j with
    | zero => exact ⟨b, mem_univ b, by simp⟩
    | succ j ih =>
      obtain ⟨c, hc, hbc⟩ := ih (by omega)
      obtain ⟨c', hc', hcc'⟩ := h j (by omega) c hc
      exact ⟨c', hc', by rw [sum_range_succ]; linarith⟩
  obtain ⟨c, hc, hbc⟩ := h_key L le_rfl
  -- The only survivor of the `⌈log₂ K⌉` phases is the recommended arm.
  have hc_eq : c = roundRobinOn (survivors (streamStats t z) L) 0 :=
    card_le_one.1 (card_survivors_numPhases _).le _ hc _
      (roundRobinOn_mem (survivors_nonempty _ _) 0)
  rw [← hc_eq] at hb
  linarith

/-- Along every run of the sampling rule of median elimination in a stochastic bandit, the law of
the survivors of the `⌈log₂ K⌉` phases is that of the survivors computed from the phases of the
reward stream. -/
lemma measure_survivors_runStats_mem_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {t : ℕ → ℕ}
    {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (h : IsAlgEnvSeq O A R (samplingRule t) (Environment.bandit ν) P) (B : Set (Finset α)) :
    P {ω | survivors (runStats t A R ω) (numPhases (Fintype.card α)) ∈ B} =
      Bandits.streamMeasure ν
        {z | survivors (streamStats t z) (numPhases (Fintype.card α)) ∈ B} := by
  set K := Fintype.card α
  set L := numPhases K
  have h_arr := Bandits.ArrayModel.isAlgEnvSeq_arrayMeasure (samplingRule t) ν
  -- The survivors are a function of the numbers of pulls and the sums of rewards.
  set F : (ℕ → α → ℕ × ℝ) → Finset α := fun p ↦
    survivors (fun j a ↦ (p (phaseEnd K t (j + 1)) a).2 - (p (phaseEnd K t j) a).2) L
  have hF : Measurable F := (measurable_survivors L).comp
    (Measurable.of_eval fun j ↦ Measurable.of_eval fun a ↦ by fun_prop)
  calc P {ω | survivors (runStats t A R ω) L ∈ B}
  _ = Bandits.ArrayModel.arrayMeasure ν {ω | survivors (runStats t
      (Bandits.ArrayModel.action (samplingRule t)) (Bandits.ArrayModel.reward (samplingRule t)) ω)
        L ∈ B} := by
    have h_id : IdentDistrib (fun ω ↦ survivors (runStats t A R ω) L)
        (fun ω ↦ survivors (runStats t (Bandits.ArrayModel.action (samplingRule t))
          (Bandits.ArrayModel.reward (samplingRule t)) ω) L)
        P (Bandits.ArrayModel.arrayMeasure ν) :=
      (h.identDistrib_pullCount_sumRewards h_arr).comp hF
    exact h_id.measure_mem_eq MeasurableSet.of_discrete
  _ = Bandits.ArrayModel.arrayMeasure ν {ω | survivors (streamStats t ω.2) L ∈ B} := by
    refine measure_congr ?_
    filter_upwards [action_ae_eq h_arr] with ω hω
    rw [survivors_runStats_eq_streamStats hω
      (fun a n ↦ Bandits.ArrayModel.sumRewards_eq (samplingRule t) a n ω) le_rfl]
  _ = Bandits.streamMeasure ν {z | survivors (streamStats t z) L ∈ B} := by
    rw [Bandits.ArrayModel.arrayMeasure, show {ω : Bandits.ArrayModel.ProbSpace α ℝ |
        survivors (streamStats t ω.2) L ∈ B} = Set.univ ×ˢ {z | survivors (streamStats t z) L ∈ B}
      by ext; simp, Measure.prod_prod]
    simp

end Stream

end LMLExplore.Identification.MedianElimination

namespace LMLExplore.Identification

open MedianElimination

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- **Median elimination** [EMM02, EMM06] in which each surviving arm is pulled `t j` times during
phase `j`, as a fixed-budget identification algorithm. With `K` arms, it proceeds in `⌈log₂ K⌉`
phases: phase `j` pulls each of the arms that survive the first `j` phases `t j` times, in a round
robin, then keeps the half of them (rounded up) with the largest sums of rewards during phase `j`,
which are the arms with the largest empirical means computed from the samples of phase `j` only.
The arm that survives the `⌈log₂ K⌉` phases is recommended at the end of the last phase. -/
noncomputable def medianElimination (t : ℕ → ℕ) : IdentAlg Unit α ℝ α :=
  fixedBudget (samplingRule t) (phaseEnd (Fintype.card α) t (numPhases (Fintype.card α)))
    (Kernel.deterministic (recommendation t) (measurable_recommendation t _))

variable {t : ℕ → ℕ}

@[simp]
lemma alg_medianElimination : (medianElimination (α := α) t).alg = samplingRule t :=
  alg_fixedBudget _ _ _

lemma outputAt_medianElimination :
    outputAt (medianElimination (α := α) t)
        (phaseEnd (Fintype.card α) t (numPhases (Fintype.card α))) =
      Kernel.deterministic (recommendation t) (measurable_recommendation t _) :=
  outputAt_fixedBudget _ _ _

lemma isFixedBudget_medianElimination :
    IsFixedBudget (medianElimination (α := α) t)
      (phaseEnd (Fintype.card α) t (numPhases (Fintype.card α))) :=
  isFixedBudget_fixedBudget _ _ _

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {out : Ω → α} {ν : Kernel α ℝ}
  [IsMarkovKernel ν]

/-- Along a run of median elimination, the output is the arm that survives the `⌈log₂ K⌉`
phases. -/
lemma MedianElimination.output_ae_eq
    (h : (medianElimination t).IsRun (Environment.bandit ν) O A R out P) :
    out =ᵐ[P] fun ω ↦
      roundRobinOn (survivors (runStats t A R ω) (numPhases (Fintype.card α))) 0 := by
  filter_upwards [h.output_ae_eq_of_outputAt_eq_deterministic isFixedBudget_medianElimination
    (measurable_recommendation t _) outputAt_medianElimination] with ω hω
  rw [hω, recommendation]
  refine congrArg (roundRobinOn · 0) (survivors_congr fun j hj a _ ↦ ?_)
  have hj' : phaseEnd (Fintype.card α) t (j + 1) ≤
      phaseEnd (Fintype.card α) t (numPhases (Fintype.card α)) := monotone_phaseEnd _ t hj
  rw [histStats, runStats, SuccessiveRejects.histSum_history O A R hj' ω a,
    SuccessiveRejects.histSum_history O A R ((monotone_phaseEnd _ t (Nat.le_succ j)).trans hj') ω a]

/-- **Correctness of median elimination**, for any numbers of pulls [EMM02, proof of Theorem 4].
Let the arms be `σ2`-sub-Gaussian and let `ε j ≥ 0` be tolerances for the phases. Along every run
of median elimination in which each surviving arm is pulled `t j` times during phase `j`, the
probability that the output has a mean more than `∑ j, ε j` below the largest mean is at most
`∑ j, 3 exp(-t j (ε j)² / (8 σ2))`, the sums ranging over the `⌈log₂ K⌉` phases. -/
theorem MedianElimination.measureReal_exists_output_add_lt_le {σ2 : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {ε : ℕ → ℝ}
    (hε : ∀ j, 0 ≤ ε j) (h : (medianElimination t).IsRun (Environment.bandit ν) O A R out P) :
    P.real {ω | ∃ b, (ν (out ω))[id] + ∑ j ∈ range (numPhases (Fintype.card α)), ε j <
        (ν b)[id]} ≤
      ∑ j ∈ range (numPhases (Fintype.card α)), 3 * exp (-(t j * ε j ^ 2) / (8 * σ2)) := by
  set L := numPhases (Fintype.card α)
  have h_alg : IsAlgEnvSeq O A R (samplingRule t) (Environment.bandit ν) P := by
    simpa using h.isAlgEnvSeq
  set B : Set (Finset α) :=
    {S | ∃ b, (ν (roundRobinOn S 0))[id] + ∑ j ∈ range L, ε j < (ν b)[id]}
  calc P.real {ω | ∃ b, (ν (out ω))[id] + ∑ j ∈ range L, ε j < (ν b)[id]}
  _ = P.real {ω | survivors (runStats t A R ω) L ∈ B} := by
    refine measureReal_congr ?_
    filter_upwards [output_ae_eq h] with ω hω
    simp [B, hω, L]
  _ = (Bandits.streamMeasure ν).real {z | survivors (streamStats t z) L ∈ B} := by
    rw [measureReal_def, measureReal_def, measure_survivors_runStats_mem_eq h_alg B]
  _ ≤ (∑ j ∈ range L, 3 * ENNReal.ofReal (exp (-(t j * ε j ^ 2) / (8 * σ2)))).toReal :=
    ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.mul_ne_top (by simp)
      ENNReal.ofReal_ne_top) (measure_exists_add_lt_streamStats_le hν t hε)
  _ = ∑ j ∈ range L, 3 * exp (-(t j * ε j ^ 2) / (8 * σ2)) := by
    rw [ENNReal.toReal_sum fun _ _ ↦ by finiteness]
    simp [ENNReal.toReal_ofReal (exp_pos _).le]

/-! ### The schedule of [EMM02] -/

namespace MedianElimination

/-- The numbers of pulls of median elimination [EMM02] for `σ2`-sub-Gaussian arms, tolerance `ε`
and confidence `δ`: in phase `j`, with the tolerance `ε_j = (ε / 4) (3 / 4) ^ j` and the confidence
`δ_j = δ / 2 ^ (j + 1)`, each surviving arm is pulled `⌈8 σ2 ε_j⁻² log (3 / δ_j)⌉` times. -/
noncomputable def pullSchedule (σ2 ε δ : ℝ) (j : ℕ) : ℕ :=
  ⌈8 * σ2 / (ε / 4 * (3 / 4) ^ j) ^ 2 * log (3 * 2 ^ (j + 1) / δ)⌉₊

lemma pullSchedule_def (σ2 ε δ : ℝ) (j : ℕ) :
    pullSchedule σ2 ε δ j = ⌈8 * σ2 / (ε / 4 * (3 / 4) ^ j) ^ 2 * log (3 * 2 ^ (j + 1) / δ)⌉₊ :=
  (rfl)

/-- With the numbers of pulls of [EMM02], phase `j` fails with probability at most
`δ / 2 ^ (j + 1)`. -/
lemma three_mul_exp_neg_pullSchedule_le {σ2 ε δ : ℝ} (hσ2 : 0 < σ2) (hε : 0 < ε) (hδ : 0 < δ)
    (j : ℕ) :
    3 * exp (-(pullSchedule σ2 ε δ j * (ε / 4 * (3 / 4) ^ j) ^ 2) / (8 * σ2)) ≤
      δ / 2 ^ (j + 1) := by
  set e := ε / 4 * (3 / 4) ^ j
  have he : e ≠ 0 := by positivity
  have hc : 0 < 3 * 2 ^ (j + 1) / δ := by positivity
  have h_log : log (3 * 2 ^ (j + 1) / δ) ≤ pullSchedule σ2 ε δ j * e ^ 2 / (8 * σ2) := by
    rw [le_div_iff₀ (by positivity)]
    have h := Nat.le_ceil (8 * σ2 / e ^ 2 * log (3 * 2 ^ (j + 1) / δ))
    rw [← pullSchedule_def] at h
    calc log (3 * 2 ^ (j + 1) / δ) * (8 * σ2)
    _ = 8 * σ2 / e ^ 2 * log (3 * 2 ^ (j + 1) / δ) * e ^ 2 := by field_simp
    _ ≤ pullSchedule σ2 ε δ j * e ^ 2 := by gcongr
  calc 3 * exp (-(pullSchedule σ2 ε δ j * e ^ 2) / (8 * σ2))
  _ ≤ 3 * exp (-log (3 * 2 ^ (j + 1) / δ)) := by
    rw [neg_div]
    gcongr
  _ = δ / 2 ^ (j + 1) := by
    rw [exp_neg, exp_log hc]
    field_simp

end MedianElimination

/-- **Median elimination is `(ε, δ)`-correct** [EMM02, Theorem 4; EMM06, Theorem 10]. For
`σ2`-sub-Gaussian arms with `σ2 > 0`, a tolerance `ε > 0` and a confidence `δ > 0`, along every run
of median elimination with the numbers of pulls of [EMM02], the output is not `ε`-good (some arm
has a mean larger than its mean plus `ε`) with probability at most `δ`. -/
theorem MedianElimination.measureReal_exists_output_add_lt_le_of_pullSchedule {σ2 : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : 0 < σ2) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (h : (medianElimination (pullSchedule σ2 ε δ)).IsRun (Environment.bandit ν) O A R out P) :
    P.real {ω | ∃ b, (ν (out ω))[id] + ε < (ν b)[id]} ≤ δ := by
  set L := numPhases (Fintype.card α)
  -- The tolerances of the phases add up to at most `ε`.
  have h_sum_ε : ∑ j ∈ range L, ε / 4 * (3 / 4 : ℝ) ^ j ≤ ε := by
    rw [← mul_sum]
    have h := geom_sum_Ico_le_of_lt_one (x := (3 / 4 : ℝ)) (m := 0) (n := L) (by norm_num)
      (by norm_num)
    rw [Nat.Ico_zero_eq_range] at h
    calc ε / 4 * ∑ j ∈ range L, (3 / 4 : ℝ) ^ j ≤ ε / 4 * ((3 / 4) ^ 0 / (1 - 3 / 4)) := by gcongr
    _ = ε := by ring
  refine le_trans (measureReal_mono fun ω hω ↦ ?_)
    ((measureReal_exists_output_add_lt_le hν (ε := fun j ↦ ε / 4 * (3 / 4) ^ j)
      (fun j ↦ by positivity) h).trans ?_)
  · obtain ⟨b, hb⟩ := hω
    exact ⟨b, by linarith⟩
  -- The failure probabilities of the phases add up to at most `δ`.
  calc ∑ j ∈ range L, 3 * exp (-(pullSchedule σ2 ε δ j * (ε / 4 * (3 / 4) ^ j) ^ 2) / (8 * σ2))
  _ ≤ ∑ j ∈ range L, δ / 2 ^ (j + 1) :=
    sum_le_sum fun j _ ↦ three_mul_exp_neg_pullSchedule_le hσ2 hε hδ j
  _ = δ / 2 * ∑ j ∈ range L, (1 / 2 : ℝ) ^ j := by
    rw [mul_sum]
    exact sum_congr rfl fun j _ ↦ by rw [pow_succ, one_div_pow]; field_simp
  _ ≤ δ / 2 * 2 := by gcongr; exact sum_geometric_two_le L
  _ = δ := by ring

/-- **Median elimination is `(ε, δ)`-PAC** [EMM02, Theorem 4; EMM06, Theorem 10]. Let the arm `a`
of the model `μ` have mean `μ a` and be `σ2`-sub-Gaussian, with `σ2 > 0`. For a tolerance `ε > 0`
and a confidence `δ > 0`, median elimination with the numbers of pulls of [EMM02] is `δ`-PAC for
`ε`-best arm identification: on every model, it stops after a fixed number of rounds and outputs an
`ε`-good arm with probability at least `1 - δ`. -/
theorem isDeltaPAC_medianElimination {ν : (α → ℝ) → Kernel α ℝ} [∀ μ, IsMarkovKernel (ν μ)]
    {σ2 : ℝ≥0} (hmean : ∀ (μ : α → ℝ) a, (ν μ a)[id] = μ a)
    (hν : ∀ (μ : α → ℝ) a, HasSubgaussianMGF (fun x ↦ x - (ν μ a)[id]) σ2 (ν μ a))
    (hσ2 : 0 < σ2) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    (epsBaiTask ν ε).IsDeltaPAC (medianElimination (pullSchedule σ2 ε δ)) δ := by
  refine IdentTask.isDeltaPAC_iff.2 ⟨fun μ _ ↦ ?_, fun μ _ ↦
    isFixedBudget_medianElimination.stopsAS _⟩
  have hrun := isRun_runMeasure (medianElimination (α := α) (pullSchedule σ2 ε δ))
    (Environment.bandit (ν μ))
  simp only [ν_epsBaiTask]
  rw [← hrun.hasLaw_output.measureReal_eq (p := fun i ↦ i ∉ (epsBaiTask ν ε).correct μ)
    MeasurableSet.of_discrete]
  refine (measureReal_mono fun ω hω ↦ ?_).trans
    (MedianElimination.measureReal_exists_output_add_lt_le_of_pullSchedule (hν μ) hσ2 hε hδ hrun)
  simp only [correct_epsBaiTask, Set.mem_ofPred_eq, not_forall, not_le] at hω
  obtain ⟨b, hb⟩ := hω
  exact ⟨b, by rwa [hmean, hmean]⟩

end LMLExplore.Identification
