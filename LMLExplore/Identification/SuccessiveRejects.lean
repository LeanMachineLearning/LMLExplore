/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.Online.Bandit.Concentration
public import LMLExplore.Data.Finset.Card
public import LMLExplore.Identification.FixedBudget
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Successive rejects

Successive rejects [ABM10] is the fixed-budget algorithm for best arm identification that proceeds
in `K - 1` phases, `K` being the number of arms. Given numbers of pulls
`0 = n 0 ≤ n 1 ≤ ⋯ ≤ n (K - 1)`, phase `k + 1` pulls each of the `K - k` arms that survive the first
`k` phases until it has been pulled `n (k + 1)` times, then eliminates the surviving arm with the
smallest empirical mean. The arm that survives the `K - 1` phases is recommended.

If the best arm `a'` is eliminated at the end of phase `k + 1`, then, since only `k` arms were
eliminated before, some arm `b` of any given set `B k` of `k + 1` other arms still survives, and the
empirical mean of `a'` after `n (k + 1)` pulls is at most that of `b`. A union bound and the
sub-Gaussian concentration of the rewards give the bound
`P(error) ≤ ∑_{k < K - 1} ∑_{b ∈ B k} exp(-n (k + 1) Δ_b² / (4 σ2))` for `σ2`-sub-Gaussian arms with
gaps `Δ`. With the numbers of pulls `n k = ⌈(T - K) / (log‾ K (K + 1 - k))⌉` of [ABM10], which
fit in a budget `T ≥ K`, and with `B k` a set of `k + 1` arms with the largest gaps, every term is
at most `exp(-(T - K) / (4 σ2 log‾ K H₂))`, with the complexity `H₂ = max_i i Δ_(i)⁻²`. This is
[ABM10, Theorem 2]: `P(error) ≤ K (K - 1) / 2 · exp(-(T - K) / (log‾ K H₂))` for rewards in
`[0, 1]`.

## Main definitions

In the namespace `LMLExplore.Identification`:

* `SuccessiveRejects.survivors g k`: the arms that survive the first `k` phases, when `g j` gives
  the statistics of the arms at the end of phase `j`.
* `SuccessiveRejects.samplingRule n`: the sampling rule of successive rejects with numbers of pulls
  `n`, which pulls the surviving arms in a round robin.
* `successiveRejects n T`: successive rejects with numbers of pulls `n` and budget `T`, as a
  fixed-budget identification algorithm.
* `SuccessiveRejects.logBar K`: the constant `log‾ K = 1 / 2 + ∑_{i = 2}^K 1 / i`.
* `SuccessiveRejects.pullSchedule K T`: the numbers of pulls of [ABM10].
* `complexityTwo ν`: the complexity `H₂` of best arm identification.

## Main statements

In the namespace `LMLExplore.Identification.SuccessiveRejects`:

* `pullCount_phaseEnd_succ`: along a run, at the end of phase `k + 1`, every arm that survives `k`
  phases has been pulled `n (k + 1)` times.
* `empMean_le_of_mem_survivors_of_notMem_survivors_succ`: along a run, the arm eliminated at the
  end of a phase has the smallest empirical mean among the arms of that phase.
* `measureReal_output_ne_le_sum`: the error bound for any numbers of pulls and any sets `B k`.
* `measureReal_output_ne_le`: [ABM10, Theorem 2] for `σ2`-sub-Gaussian arms, and
  `measureReal_output_ne_le_of_mem_Icc`, its form for rewards in `[0, 1]`.

## Implementation notes

All the surviving arms have the same number of pulls at the end of a phase, so the arm with the
smallest empirical mean is the arm with the smallest sum of rewards: the eliminations compare sums
of rewards. Ties are broken by LML's `argmin`, where [ABM10] breaks them at random. The survivors
are a function `survivors g` of the statistics `g j` of the arms at the ends of the phases, computed
from the history by the sampling rule and from the actions and rewards along a run.

## References

* [ABM10] J.-Y. Audibert, S. Bubeck and R. Munos, *Best arm identification in multi-armed
  bandits*, COLT 2010, Section 4, Theorem 2.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real
open scoped ENNReal NNReal

namespace LMLExplore.Identification.SuccessiveRejects

/-! ### Phases -/

/-- The round at which the phase `k` of successive rejects with `K` arms and numbers of pulls `n`
ends: phase `k + 1` pulls each of its `K - k` arms `n (k + 1) - n k` times. -/
def phaseEnd (K : ℕ) (n : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => phaseEnd K n k + (K - k) * (n (k + 1) - n k)

@[simp]
lemma phaseEnd_zero (K : ℕ) (n : ℕ → ℕ) : phaseEnd K n 0 = 0 := (rfl)

lemma phaseEnd_succ (K : ℕ) (n : ℕ → ℕ) (k : ℕ) :
    phaseEnd K n (k + 1) = phaseEnd K n k + (K - k) * (n (k + 1) - n k) := (rfl)

lemma monotone_phaseEnd (K : ℕ) (n : ℕ → ℕ) : Monotone (phaseEnd K n) :=
  monotone_nat_of_le_succ fun k ↦ by rw [phaseEnd_succ]; exact Nat.le_add_right _ _

/-- The number of phases of successive rejects completed before round `t`, at most `K - 1`. -/
def phaseOf (K : ℕ) (n : ℕ → ℕ) (t : ℕ) : ℕ :=
  Nat.findGreatest (fun j ↦ phaseEnd K n j ≤ t) (K - 1)

lemma phaseOf_def (K : ℕ) (n : ℕ → ℕ) (t : ℕ) :
    phaseOf K n t = Nat.findGreatest (fun j ↦ phaseEnd K n j ≤ t) (K - 1) := (rfl)

lemma phaseEnd_phaseOf_le (K : ℕ) (n : ℕ → ℕ) (t : ℕ) : phaseEnd K n (phaseOf K n t) ≤ t :=
  Nat.findGreatest_spec (P := fun j ↦ phaseEnd K n j ≤ t) (Nat.zero_le _) (by simp)

/-- A round of phase `k + 1` comes after `k` completed phases. -/
lemma phaseOf_eq {K : ℕ} {n : ℕ → ℕ} {k t : ℕ} (hk : k + 1 ≤ K - 1) (h₁ : phaseEnd K n k ≤ t)
    (h₂ : t < phaseEnd K n (k + 1)) : phaseOf K n t = k := by
  refine le_antisymm ?_ (Nat.le_findGreatest (by omega) h₁)
  by_contra! h
  exact h₂.not_ge ((monotone_phaseEnd K n h).trans (phaseEnd_phaseOf_le K n t))

/-! ### Round robins -/

section RoundRobin

variable {α : Type*} [Nonempty α]

/-- The arm played at offset `r` of a round robin over the finite set `S` (an arbitrary arm if
`S` is empty). -/
noncomputable def roundRobinOn (S : Finset α) (r : ℕ) : α :=
  if h : S.Nonempty then (S.equivFin.symm ⟨r % #S, Nat.mod_lt _ h.card_pos⟩ : α)
  else Classical.arbitrary α

lemma roundRobinOn_def (S : Finset α) (r : ℕ) :
    roundRobinOn S r = if h : S.Nonempty
      then (S.equivFin.symm ⟨r % #S, Nat.mod_lt _ h.card_pos⟩ : α) else Classical.arbitrary α :=
  (rfl)

lemma roundRobinOn_mem {S : Finset α} (hS : S.Nonempty) (r : ℕ) : roundRobinOn S r ∈ S := by
  simp only [roundRobinOn, hS, dite_true, coe_mem]

/-- A round robin over `S` during `#S * d` rounds plays each arm of `S` exactly `d` times. -/
lemma card_filter_roundRobinOn_eq [DecidableEq α] (S : Finset α) (d : ℕ) (a : α) :
    #{r ∈ range (#S * d) | roundRobinOn S r = a} = if a ∈ S then d else 0 := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  split_ifs with ha
  · have h_iff (r : ℕ) : roundRobinOn S r = a ↔ r ≡ (S.equivFin ⟨a, ha⟩ : ℕ) [MOD #S] := by
      have : roundRobinOn S r = a ↔
          S.equivFin.symm ⟨r % #S, Nat.mod_lt _ hS.card_pos⟩ = ⟨a, ha⟩ := by
        simp only [roundRobinOn, hS, dite_true, Subtype.ext_iff]
      rw [this, Equiv.symm_apply_eq, Fin.ext_iff, Nat.ModEq,
        Nat.mod_eq_of_lt (S.equivFin ⟨a, ha⟩).isLt]
    simp_rw [h_iff, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hS.card_pos,
      Nat.mul_mod_right, Nat.not_lt_zero, ite_false, add_zero,
      Nat.mul_div_cancel_left _ hS.card_pos]
  · rw [card_eq_zero, filter_eq_empty_iff]
    exact fun r _ h ↦ ha (h ▸ roundRobinOn_mem hS r)

end RoundRobin

/-! ### Survivors -/

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- The arm eliminated from the set `S` by the values `x`: an arm of `S` with the smallest value
(an arbitrary arm if `S` is empty). -/
noncomputable def eliminated (S : Finset α) (x : α → ℝ) : α :=
  argmin fun a ↦ if a ∈ S then (x a : EReal) else ⊤

lemma eliminated_def (S : Finset α) (x : α → ℝ) :
    eliminated S x = argmin fun a ↦ if a ∈ S then (x a : EReal) else ⊤ := (rfl)

lemma eliminated_mem {S : Finset α} (hS : S.Nonempty) (x : α → ℝ) : eliminated S x ∈ S := by
  obtain ⟨b, hb⟩ := hS
  by_contra h
  have hmin := isMinOn_univ_iff.1 (isMinOn_argmin fun a ↦ if a ∈ S then (x a : EReal) else ⊤) b
  rw [← eliminated_def] at hmin
  simp only [h, hb, ite_true, ite_false, top_le_iff] at hmin
  exact EReal.coe_ne_top _ hmin

lemma le_of_eliminated_mem {S : Finset α} {x : α → ℝ} (h : eliminated S x ∈ S) {b : α}
    (hb : b ∈ S) : x (eliminated S x) ≤ x b := by
  have hmin := isMinOn_univ_iff.1 (isMinOn_argmin fun a ↦ if a ∈ S then (x a : EReal) else ⊤) b
  rw [← eliminated_def] at hmin
  simpa only [h, hb, ite_true, EReal.coe_le_coe_iff] using hmin

/-- The arms that survive the first `k` phases of successive rejects, when `g j` gives the
statistics of the arms at the end of phase `j`: phase `k + 1` eliminates the surviving arm with
the smallest statistic `g (k + 1)`. -/
noncomputable def survivors (g : ℕ → α → ℝ) : ℕ → Finset α
  | 0 => univ
  | k + 1 => (survivors g k).erase (eliminated (survivors g k) (g (k + 1)))

@[simp]
lemma survivors_zero (g : ℕ → α → ℝ) : survivors g 0 = univ := (rfl)

lemma survivors_succ (g : ℕ → α → ℝ) (k : ℕ) :
    survivors g (k + 1) = (survivors g k).erase (eliminated (survivors g k) (g (k + 1))) := (rfl)

lemma survivors_succ_subset (g : ℕ → α → ℝ) (k : ℕ) : survivors g (k + 1) ⊆ survivors g k := by
  rw [survivors_succ]
  exact erase_subset _ _

lemma card_survivors (g : ℕ → α → ℝ) {k : ℕ} (hk : k < Fintype.card α) :
    #(survivors g k) = Fintype.card α - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (by omega)
    rw [survivors_succ, card_erase_of_mem (eliminated_mem (card_pos.1 (by omega)) _), ih]
    omega

/-- The survivors after `k` phases only depend on the statistics of the first `k` phases. -/
lemma survivors_congr {g g' : ℕ → α → ℝ} {k : ℕ} (h : ∀ j ≤ k, g j = g' j) :
    survivors g k = survivors g' k := by
  induction k with
  | zero => simp
  | succ k ih => rw [survivors_succ, survivors_succ, ih fun j hj ↦ h j (by omega), h (k + 1) le_rfl]

/-- An arm that survives `k` phases but not `k + 1` has the smallest statistic `g (k + 1)` among
the survivors of `k` phases. -/
lemma le_of_mem_survivors_of_notMem_survivors_succ {g : ℕ → α → ℝ} {k : ℕ} {a b : α}
    (ha : a ∈ survivors g k) (ha' : a ∉ survivors g (k + 1)) (hb : b ∈ survivors g k) :
    g (k + 1) a ≤ g (k + 1) b := by
  rw [survivors_succ, mem_erase, not_and_or, not_not] at ha'
  obtain rfl := ha'.resolve_right (not_not.2 ha)
  exact le_of_eliminated_mem ha hb

/-- The arm played by successive rejects with numbers of pulls `n` at round `t`, when `g j` gives
the statistics of the arms at the end of phase `j`: after `k` completed phases, the round robin over
the `K - k` arms that survive them, started at the end of phase `k`. -/
noncomputable def armAt (n : ℕ → ℕ) (g : ℕ → α → ℝ) (t : ℕ) : α :=
  roundRobinOn (survivors g (phaseOf (Fintype.card α) n t))
    (t - phaseEnd (Fintype.card α) n (phaseOf (Fintype.card α) n t))

lemma armAt_def (n : ℕ → ℕ) (g : ℕ → α → ℝ) (t : ℕ) :
    armAt n g t = roundRobinOn (survivors g (phaseOf (Fintype.card α) n t))
      (t - phaseEnd (Fintype.card α) n (phaseOf (Fintype.card α) n t)) := (rfl)

/-- The arm played at round `t` only depends on the statistics of the phases completed before
`t`. -/
lemma armAt_congr {n : ℕ → ℕ} {g g' : ℕ → α → ℝ} {t : ℕ}
    (h : ∀ j, phaseEnd (Fintype.card α) n j ≤ t → g j = g' j) : armAt n g t = armAt n g' t := by
  rw [armAt, armAt, survivors_congr fun j hj ↦ h j
    ((monotone_phaseEnd _ n hj).trans (phaseEnd_phaseOf_le _ n t))]

/-- During phase `k + 1`, the arm played at the round `r` rounds after the end of phase `k` is the
round robin over the survivors of `k` phases, at offset `r`. -/
lemma armAt_phaseEnd_add (n : ℕ → ℕ) (g : ℕ → α → ℝ) {k r : ℕ}
    (hk : k + 1 ≤ Fintype.card α - 1)
    (hr : r < (Fintype.card α - k) * (n (k + 1) - n k)) :
    armAt n g (phaseEnd (Fintype.card α) n k + r) = roundRobinOn (survivors g k) r := by
  rw [armAt, phaseOf_eq hk (Nat.le_add_right _ _) (by rw [phaseEnd_succ]; omega),
    Nat.add_sub_cancel_left]

/-! ### The algorithm -/

/-- The sum of the rewards of the arm `a` in the first `t` rounds of the history `h`. -/
noncomputable def histSum {m : ℕ} (h : Hist Unit α ℝ m) (t : ℕ) (a : α) : ℝ :=
  ∑ s : Fin m, if (s : ℕ) < t ∧ (h s).action = a then (h s).feedback else 0

omit [Fintype α] [Nonempty α] in
lemma histSum_def {m : ℕ} (h : Hist Unit α ℝ m) (t : ℕ) (a : α) :
    histSum h t a = ∑ s : Fin m, if (s : ℕ) < t ∧ (h s).action = a then (h s).feedback else 0 :=
  (rfl)

omit [Fintype α] [Nonempty α] in
/-- The sum of the rewards of an arm in the first `t` rounds of the history of the first `m ≥ t`
rounds is its sum of rewards before round `t`. -/
lemma histSum_history {Ω : Type*} (O : ℕ → Ω → Unit) (A : ℕ → Ω → α) (R : ℕ → Ω → ℝ) {m t : ℕ}
    (ht : t ≤ m) (ω : Ω) (a : α) : histSum (history O A R m ω) t a = sumRewards A R a t ω := by
  rw [histSum, sum_fin_eq_sum_range, sumRewards, ← sum_range_add_sum_Ico _ ht,
    sum_eq_zero (s := Ico t m) fun s hs ↦ by simp [(mem_Ico.1 hs).1.not_gt], add_zero]
  refine sum_congr rfl fun s hs ↦ ?_
  have hs := mem_range.1 hs
  simp [hs, hs.trans_le ht, history_apply]

/-- The arm played by successive rejects with numbers of pulls `n` after `t` rounds with history
`h`: `armAt n` for the sums of rewards of the arms at the ends of the phases. -/
noncomputable def nextArm (n : ℕ → ℕ) (t : ℕ) (h : Hist Unit α ℝ t) : α :=
  armAt n (fun j ↦ histSum h (phaseEnd (Fintype.card α) n j)) t

lemma nextArm_def (n : ℕ → ℕ) (t : ℕ) (h : Hist Unit α ℝ t) :
    nextArm n t h = armAt n (fun j ↦ histSum h (phaseEnd (Fintype.card α) n j)) t := (rfl)

/-- The arm recommended by successive rejects with numbers of pulls `n` after the history `h`: the
arm that survives the `K - 1` phases, for the sums of rewards at the ends of the phases. -/
noncomputable def recommendation (n : ℕ → ℕ) {T : ℕ} (h : Hist Unit α ℝ T) : α :=
  roundRobinOn (survivors (fun j ↦ histSum h (phaseEnd (Fintype.card α) n j))
    (Fintype.card α - 1)) 0

lemma recommendation_def (n : ℕ → ℕ) {T : ℕ} (h : Hist Unit α ℝ T) :
    recommendation n h = roundRobinOn (survivors (fun j ↦ histSum h (phaseEnd (Fintype.card α) n j))
      (Fintype.card α - 1)) 0 := (rfl)

section Measurability

variable [MeasurableSpace α] [MeasurableSingletonClass α]

omit [Fintype α] [Nonempty α] in
lemma measurable_histSum (m t : ℕ) (a : α) :
    Measurable fun h : Hist Unit α ℝ m ↦ histSum h t a := by
  refine Finset.measurable_sum _ fun s _ ↦ Measurable.ite ?_ ?_ measurable_const
  · rw [Set.ofPred_and]
    refine MeasurableSet.inter (MeasurableSet.const _) ?_
    exact (measurable_snd.fst.comp (measurable_pi_apply s)) (measurableSet_singleton a)
  · exact measurable_snd.snd.comp (measurable_pi_apply s)

lemma measurable_survivors (k : ℕ) : Measurable fun g : ℕ → α → ℝ ↦ survivors g k := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have he : Measurable fun g : ℕ → α → ℝ ↦ eliminated (survivors g k) (g (k + 1)) := by
      refine (measurable_argmin (ι := α) (α := EReal)).comp (Measurable.of_eval fun a ↦ ?_)
      refine Measurable.ite ((measurableSet_mem_finset a).preimage ih) ?_ measurable_const
      exact measurable_coe_real_ereal.comp ((measurable_pi_apply a).comp (measurable_pi_apply _))
    simp_rw [survivors_succ, erase_eq]
    exact ih.sdiff_finset ((measurable_of_countable fun a : α ↦ ({a} : Finset α)).comp he)

lemma measurable_survivors_histSum (m : ℕ) (n : ℕ → ℕ) (k : ℕ) :
    Measurable fun h : Hist Unit α ℝ m ↦
      survivors (fun j ↦ histSum h (phaseEnd (Fintype.card α) n j)) k :=
  (measurable_survivors k).comp
    (Measurable.of_eval fun _ ↦ Measurable.of_eval fun a ↦ measurable_histSum m _ a)

lemma measurable_nextArm (n : ℕ → ℕ) (t : ℕ) : Measurable (nextArm (α := α) n t) :=
  (measurable_of_countable fun S : Finset α ↦ roundRobinOn S _).comp
    (measurable_survivors_histSum t n _)

lemma measurable_recommendation (n : ℕ → ℕ) (T : ℕ) :
    Measurable (recommendation (α := α) n (T := T)) :=
  (measurable_of_countable fun S : Finset α ↦ roundRobinOn S 0).comp
    (measurable_survivors_histSum T n _)

/-- The sampling rule of successive rejects with numbers of pulls `n`: the deterministic algorithm
that plays `nextArm n`. -/
noncomputable def samplingRule (n : ℕ → ℕ) : Algorithm Unit α ℝ :=
  Algorithm.deterministic (fun t p ↦ nextArm n t p.1)
    fun t ↦ (measurable_nextArm n t).comp measurable_fst

lemma samplingRule_def (n : ℕ → ℕ) :
    samplingRule (α := α) n = Algorithm.deterministic (fun t p ↦ nextArm n t p.1)
      (fun t ↦ (measurable_nextArm n t).comp measurable_fst) := (rfl)

end Measurability

/-! ### Runs -/

/-- The sums of the rewards of the arms at the ends of the phases of successive rejects with numbers
of pulls `n`, along the actions `A` and rewards `R`: the statistics that decide the eliminations
along a run. -/
noncomputable def phaseSums {Ω : Type*} (n : ℕ → ℕ) (A : ℕ → Ω → α) (R : ℕ → Ω → ℝ) (ω : Ω)
    (j : ℕ) (a : α) : ℝ :=
  sumRewards A R a (phaseEnd (Fintype.card α) n j) ω

omit [Nonempty α] in
lemma phaseSums_def {Ω : Type*} (n : ℕ → ℕ) (A : ℕ → Ω → α) (R : ℕ → Ω → ℝ) (ω : Ω) (j : ℕ)
    (a : α) : phaseSums n A R ω j a = sumRewards A R a (phaseEnd (Fintype.card α) n j) ω := (rfl)

variable {Ω : Type*} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {n : ℕ → ℕ} {ω : Ω}

/-- Along a run of the sampling rule of successive rejects, the arm played at every round is
`armAt n` for the sums of rewards at the ends of the phases. -/
lemma action_ae_eq [MeasurableSpace α] [MeasurableSingletonClass α]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [SFinite P] {O : ℕ → Ω → Unit} {ν : Kernel α ℝ}
    [IsMarkovKernel ν] (h : IsAlgEnvSeq O A R (samplingRule n) (Environment.bandit ν) P) :
    ∀ᵐ ω ∂P, ∀ t, A t ω = armAt n (phaseSums n A R ω) t := by
  filter_upwards [h.action_ae_all_eq_deterministic] with ω hω t
  rw [hω t, nextArm]
  exact armAt_congr fun j hj ↦ funext fun a ↦ histSum_history O A R hj ω a

/-- If the actions follow successive rejects, then during phase `k + 1`, every arm that survives
the first `k` phases is pulled `n (k + 1) - n k` times. -/
lemma pullCount_phaseEnd_succ_eq_add (hω : ∀ t, A t ω = armAt n (phaseSums n A R ω) t) {k : ℕ}
    (hk : k + 1 ≤ Fintype.card α - 1) {a : α} (ha : a ∈ survivors (phaseSums n A R ω) k) :
    pullCount A a (phaseEnd (Fintype.card α) n (k + 1)) ω =
      pullCount A a (phaseEnd (Fintype.card α) n k) ω + (n (k + 1) - n k) := by
  set K := Fintype.card α
  set S := survivors (phaseSums n A R ω) k
  have hS : #S = K - k := card_survivors _ (by omega)
  rw [pullCount_eq_sum, ← sum_range_add_sum_Ico _ (monotone_phaseEnd K n (Nat.le_succ k)),
    ← pullCount_eq_sum, sum_Ico_eq_sum_range, phaseEnd_succ, Nat.add_sub_cancel_left, ← hS,
    sum_boole, Nat.cast_id]
  congr 1
  calc #{r ∈ range (#S * (n (k + 1) - n k)) | A (phaseEnd K n k + r) ω = a}
  _ = #{r ∈ range (#S * (n (k + 1) - n k)) | roundRobinOn S r = a} := by
    refine congrArg card (filter_congr fun r hr ↦ ?_)
    rw [hω, armAt_phaseEnd_add n _ hk (hS ▸ mem_range.1 hr)]
  _ = n (k + 1) - n k := by simp [card_filter_roundRobinOn_eq, ha]

/-- If the actions follow successive rejects with nondecreasing numbers of pulls `n` and
`n 0 = 0`, then at the end of phase `k + 1`, every arm that survives the first `k` phases has been
pulled `n (k + 1)` times. -/
lemma pullCount_phaseEnd_succ (hn0 : n 0 = 0) (hn : MonotoneOn n (Set.Iic (Fintype.card α - 1)))
    (hω : ∀ t, A t ω = armAt n (phaseSums n A R ω) t) {k : ℕ} (hk : k + 1 ≤ Fintype.card α - 1)
    {a : α} (ha : a ∈ survivors (phaseSums n A R ω) k) :
    pullCount A a (phaseEnd (Fintype.card α) n (k + 1)) ω = n (k + 1) := by
  have hmono := hn (a := k) (b := k + 1) (by simp; omega) (by simp; omega) (Nat.le_succ k)
  rw [pullCount_phaseEnd_succ_eq_add hω hk ha]
  induction k generalizing a with
  | zero => simp [hn0]
  | succ k ih =>
    rw [pullCount_phaseEnd_succ_eq_add hω (by omega) (survivors_succ_subset _ k ha),
      ih (by omega) (survivors_succ_subset _ k ha)]
    · omega
    · exact hn (by simp; omega) (by simp; omega) (Nat.le_succ k)

/-- If the actions follow successive rejects with nondecreasing numbers of pulls `n` and
`n 0 = 0`, the arm eliminated at the end of phase `k + 1` has the smallest empirical mean among
the survivors of the first `k` phases. -/
lemma empMean_le_of_mem_survivors_of_notMem_survivors_succ (hn0 : n 0 = 0)
    (hn : MonotoneOn n (Set.Iic (Fintype.card α - 1)))
    (hω : ∀ t, A t ω = armAt n (phaseSums n A R ω) t) {k : ℕ} (hk : k + 1 ≤ Fintype.card α - 1)
    {a b : α} (ha : a ∈ survivors (phaseSums n A R ω) k)
    (ha' : a ∉ survivors (phaseSums n A R ω) (k + 1)) (hb : b ∈ survivors (phaseSums n A R ω) k) :
    empMean A R a (phaseEnd (Fintype.card α) n (k + 1)) ω ≤
      empMean A R b (phaseEnd (Fintype.card α) n (k + 1)) ω := by
  rw [empMean, empMean, pullCount_phaseEnd_succ hn0 hn hω hk ha,
    pullCount_phaseEnd_succ hn0 hn hω hk hb]
  exact div_le_div_of_nonneg_right (le_of_mem_survivors_of_notMem_survivors_succ ha ha' hb)
    (Nat.cast_nonneg _)

/-- If the actions follow successive rejects with nondecreasing numbers of pulls `n` and
`n 0 = 0`, and an arm `a'` does not survive the `K - 1` phases, then for any sets `B k` of `k + 1`
arms other than `a'`, at the end of some phase `k + 1`, the arm `a'` and some arm `b ∈ B k` have
both been pulled `n (k + 1)` times and the sum of the rewards of `a'` is at most that of `b`. -/
lemma exists_sumRewards_le_of_notMem_survivors (hn0 : n 0 = 0)
    (hn : MonotoneOn n (Set.Iic (Fintype.card α - 1)))
    (hω : ∀ t, A t ω = armAt n (phaseSums n A R ω) t) {a' : α}
    (ha' : a' ∉ survivors (phaseSums n A R ω) (Fintype.card α - 1))
    {B : ℕ → Finset α} (hB : ∀ k, B k ⊆ univ.erase a')
    (hBcard : ∀ k < Fintype.card α - 1, k + 1 ≤ #(B k)) :
    ∃ k ∈ range (Fintype.card α - 1), ∃ b ∈ B k,
      pullCount A a' (phaseEnd (Fintype.card α) n (k + 1)) ω = n (k + 1) ∧
      pullCount A b (phaseEnd (Fintype.card α) n (k + 1)) ω = n (k + 1) ∧
      sumRewards A R a' (phaseEnd (Fintype.card α) n (k + 1)) ω ≤
        sumRewards A R b (phaseEnd (Fintype.card α) n (k + 1)) ω := by
  set K := Fintype.card α
  set S := survivors (phaseSums n A R ω)
  -- The phase `k + 1` at the end of which `a'` is eliminated.
  have hex : ∃ j, a' ∉ S j := ⟨_, ha'⟩
  have hj0 : Nat.find hex ≠ 0 := by
    intro h
    have h_spec := Nat.find_spec hex
    rw [h] at h_spec
    exact h_spec (mem_univ a')
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hkK : k + 1 ≤ K - 1 := by
    have := Nat.find_min' hex ha'
    omega
  have hak : a' ∈ S k := not_not.1 (Nat.find_min hex (by omega))
  have hak' : a' ∉ S (k + 1) := by
    have h_spec := Nat.find_spec hex
    rwa [hk] at h_spec
  -- Only `k` arms were eliminated before phase `k + 1`, so some arm of `B k` survives them.
  have hcard : #(univ.erase a') < #(B k) + #((S k).erase a') := by
    rw [card_erase_of_mem (mem_univ _), card_univ, card_erase_of_mem hak,
      card_survivors _ (by omega)]
    have := hBcard k (by omega)
    omega
  obtain ⟨b, hb⟩ := inter_nonempty_of_card_lt_card_add_card (hB k)
    (erase_subset_erase _ (subset_univ _)) hcard
  rw [mem_inter, mem_erase] at hb
  exact ⟨k, mem_range.2 (by omega), b, hb.1, pullCount_phaseEnd_succ hn0 hn hω hkK hak,
    pullCount_phaseEnd_succ hn0 hn hω hkK hb.2.2,
    le_of_mem_survivors_of_notMem_survivors_succ hak hak' hb.2.2⟩

end LMLExplore.Identification.SuccessiveRejects

namespace LMLExplore.Identification

open SuccessiveRejects

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- **Successive rejects** [ABM10] with numbers of pulls `n` and budget `T`, the fixed-budget
identification algorithm for best arm identification. With `K` arms, it proceeds in `K - 1`
phases: phase `k + 1` pulls each of the `K - k` arms that survive the first `k` phases, in a round
robin, until it has been pulled `n (k + 1)` times, then eliminates the surviving arm with the
smallest sum of rewards, which is the surviving arm with the smallest empirical mean
(`SuccessiveRejects.empMean_le_of_mem_survivors_of_notMem_survivors_succ`). The arm that survives
the `K - 1` phases is recommended after `T` rounds, and is pulled in the rounds that follow the
phases. The numbers of pulls are meant to be nondecreasing with `n 0 = 0`, and the phases to end
within the budget: `phaseEnd K n (K - 1) ≤ T`. -/
noncomputable def successiveRejects (n : ℕ → ℕ) (T : ℕ) : IdentAlg Unit α ℝ α :=
  fixedBudget (samplingRule n) T
    (Kernel.deterministic (recommendation n) (measurable_recommendation n T))

variable {n : ℕ → ℕ} {T : ℕ}

@[simp]
lemma alg_successiveRejects : (successiveRejects (α := α) n T).alg = samplingRule n :=
  alg_fixedBudget _ _ _

lemma outputAt_successiveRejects :
    outputAt (successiveRejects (α := α) n T) T =
      Kernel.deterministic (recommendation n) (measurable_recommendation n T) :=
  outputAt_fixedBudget _ _ _

lemma isFixedBudget_successiveRejects : IsFixedBudget (successiveRejects (α := α) n T) T :=
  isFixedBudget_fixedBudget _ _ _

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {out : Ω → α} {ν : Kernel α ℝ}
  [IsMarkovKernel ν]

/-- Along a run of successive rejects whose phases end within the budget, the output is the arm
that survives the `K - 1` phases. -/
lemma SuccessiveRejects.output_ae_eq
    (hT : phaseEnd (Fintype.card α) n (Fintype.card α - 1) ≤ T)
    (h : (successiveRejects n T).IsRun (Environment.bandit ν) O A R out P) :
    out =ᵐ[P] fun ω ↦ roundRobinOn (survivors (phaseSums n A R ω) (Fintype.card α - 1)) 0 := by
  filter_upwards [h.output_ae_eq_of_outputAt_eq_deterministic isFixedBudget_successiveRejects
    (measurable_recommendation n T) outputAt_successiveRejects] with ω hω
  rw [hω, recommendation]
  refine congrArg (roundRobinOn · 0) (survivors_congr fun j hj ↦ funext fun a ↦ ?_)
  exact histSum_history O A R ((monotone_phaseEnd _ n hj).trans hT) ω a

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
  have h_alg : IsAlgEnvSeq O A R (samplingRule n) (Environment.bandit ν) P := by
    simpa using h.isAlgEnvSeq
  have h_best : Bandits.bestArm ν = a' := by
    by_contra hne
    exact (ha' _ hne).not_ge (Bandits.le_bestArm a')
  set E : ℕ → α → Set Ω := fun k b ↦ {ω |
    pullCount A a' (phaseEnd K n (k + 1)) ω = n (k + 1) ∧
    pullCount A b (phaseEnd K n (k + 1)) ω = n (k + 1) ∧
    sumRewards A R a' (phaseEnd K n (k + 1)) ω ≤ sumRewards A R b (phaseEnd K n (k + 1)) ω}
  have h_sub : {ω | out ω ≠ a'} ≤ᵐ[P] ⋃ k ∈ range (K - 1), ⋃ b ∈ B k, E k b := by
    filter_upwards [action_ae_eq h_alg, output_ae_eq hT h] with ω hω hout hne
    -- The only survivor of the `K - 1` phases is the output, which is not `a'`.
    have hne : a' ∉ survivors (phaseSums n A R ω) (K - 1) := by
      intro hmem
      have hcard := card_survivors (phaseSums n A R ω) (k := K - 1) (by omega)
      have hmem' := roundRobinOn_mem (S := survivors (phaseSums n A R ω) (K - 1))
        (card_pos.1 (by omega)) 0
      rw [hout] at hne
      exact hne (card_le_one.1 (by omega) _ hmem' _ hmem)
    obtain ⟨k, hk, b, hb, hE⟩ := exists_sumRewards_le_of_notMem_survivors hn0 hn hω hne hB hBcard
    exact Set.mem_biUnion hk (Set.mem_biUnion hb hE)
  calc P.real {ω | out ω ≠ a'}
  _ ≤ P.real (⋃ k ∈ range (K - 1), ⋃ b ∈ B k, E k b) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae h_sub)
  _ ≤ ∑ k ∈ range (K - 1), ∑ b ∈ B k, P.real (E k b) :=
    (measureReal_biUnion_finset_le _ _).trans
      (sum_le_sum fun k _ ↦ measureReal_biUnion_finset_le _ _)
  _ ≤ ∑ k ∈ range (K - 1), ∑ b ∈ B k,
      Real.exp (-(n (k + 1) : ℝ) * Bandits.gap ν b ^ 2 / (4 * σ2)) := by
    refine sum_le_sum fun k _ ↦ sum_le_sum fun b _ ↦ ?_
    refine (Bandits.probReal_sumRewards_le_sumRewards_le h_alg a' b _ _ _).trans ?_
    rw [← h_best]
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

private lemma sum_range_inv_succ_sub (m : ℕ) :
    ∑ j ∈ range m, ((m + 1 - j : ℝ))⁻¹ = harmonic (m + 1) - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ', harmonic_succ (m + 1)]
    push_cast
    rw [sum_congr rfl fun j _ ↦ by rw [show (m + 1 + 1 - (j + 1) : ℝ) = m + 1 - j by ring], ih]
    ring

/-- `∑_{j < K - 1} 1 / (K - j) = H_K - 1`, with `H` the harmonic numbers. -/
private lemma sum_range_inv_sub_eq_harmonic_sub_one {K : ℕ} (hK : K ≠ 0) :
    ∑ j ∈ range (K - 1), ((K - j : ℝ))⁻¹ = harmonic K - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK
  rw [Nat.succ_sub_one, ← sum_range_inv_succ_sub]
  push_cast
  rfl

/-- The constant `log‾ K = 1 / 2 + ∑_{i = 2}^K 1 / i` of successive rejects [ABM10]. -/
noncomputable def logBar (K : ℕ) : ℝ := harmonic K - 1 / 2

lemma logBar_def (K : ℕ) : logBar K = harmonic K - 1 / 2 := (rfl)

lemma logBar_eq_sum {K : ℕ} (hK : K ≠ 0) :
    logBar K = ∑ j ∈ range (K - 1), ((K - j : ℝ))⁻¹ + 1 / 2 := by
  rw [sum_range_inv_sub_eq_harmonic_sub_one hK, logBar]
  ring

lemma one_half_le_logBar {K : ℕ} (hK : K ≠ 0) : 1 / 2 ≤ logBar K := by
  rw [logBar_eq_sum hK, le_add_iff_nonneg_left]
  refine sum_nonneg fun j hj ↦ inv_nonneg.2 (sub_nonneg.2 ?_)
  exact_mod_cast (mem_range.1 hj).le.trans (Nat.sub_le K 1)

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

end SuccessiveRejects

/-- The complexity `H₂` of best arm identification [ABM10]: the largest `r_b / Δ_b²` over the
arms `b`, where `Δ_b` is the gap of `b` and `r_b` is the number of arms whose gap is at most `Δ_b`.
The term of an arm of gap zero is `0`. When the best arm is unique and `Δ_(1) ≤ ⋯ ≤ Δ_(K)` are the
gaps sorted increasingly, with the gap `0` of the best arm replaced by the smallest gap of the
other arms, this is `max_i i Δ_(i)⁻²`: within a block of equal gaps, `i Δ_(i)⁻²` is largest at
the last index of the block, which is `r_b` for the arms `b` of the block. -/
noncomputable def complexityTwo (ν : Kernel α ℝ) : ℝ :=
  ⨆ b, (#{c | Bandits.gap ν c ≤ Bandits.gap ν b} : ℝ) / Bandits.gap ν b ^ 2

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
lemma complexityTwo_def (ν : Kernel α ℝ) :
    complexityTwo ν = ⨆ b, (#{c | Bandits.gap ν c ≤ Bandits.gap ν b} : ℝ) / Bandits.gap ν b ^ 2 :=
  (rfl)

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
lemma le_complexityTwo (ν : Kernel α ℝ) (b : α) :
    (#{c | Bandits.gap ν c ≤ Bandits.gap ν b} : ℝ) / Bandits.gap ν b ^ 2 ≤ complexityTwo ν :=
  le_ciSup (Set.finite_range fun b ↦
    (#{c | Bandits.gap ν c ≤ Bandits.gap ν b} : ℝ) / Bandits.gap ν b ^ 2).bddAbove b

omit [MeasurableSingletonClass α] [IsMarkovKernel ν] in
/-- If `B` is a set of arms other than the unique best arm `a'` whose gaps are at least those of
the other arms `c ≠ a'`, and `b ∈ B`, then `Δ_b² ≥ (K + 1 - #B) / H₂`: the `K + 1 - #B` arms
outside `B`, together with `b`, have gaps at most `Δ_b`. -/
lemma sub_card_div_complexityTwo_le_gap_sq {a' : α} (ha' : ∀ b ≠ a', (ν b)[id] < (ν a')[id])
    {B : Finset α} (hB : B ⊆ univ.erase a')
    (h_top : ∀ b ∈ B, ∀ c ∈ univ.erase a' \ B, Bandits.gap ν c ≤ Bandits.gap ν b)
    {b : α} (hb : b ∈ B) :
    ((Fintype.card α : ℝ) + 1 - #B) / complexityTwo ν ≤ Bandits.gap ν b ^ 2 := by
  have h_best : Bandits.bestArm ν = a' := by
    by_contra hne
    exact (ha' _ hne).not_ge (Bandits.le_bestArm a')
  have hΔ : 0 < Bandits.gap ν b := by
    rw [Bandits.gap_eq_bestArm_sub, h_best, sub_pos]
    exact ha' b (mem_erase.1 (hB hb)).1
  -- The arms outside `B`, and `b`, have gaps at most that of `b`.
  have h_rank : #(B.erase b)ᶜ ≤ #{c | Bandits.gap ν c ≤ Bandits.gap ν b} := by
    refine card_le_card fun c hc ↦ ?_
    rw [mem_compl, mem_erase, not_and_or, not_not] at hc
    rw [mem_filter_univ]
    rcases hc with rfl | hc
    · exact le_rfl
    rcases eq_or_ne c a' with rfl | hca
    · rw [← h_best, Bandits.gap_bestArm]
      exact Bandits.gap_nonneg
    · exact h_top b hb c (mem_sdiff.2 ⟨mem_erase.2 ⟨hca, mem_univ c⟩, hc⟩)
  rw [card_compl, card_erase_of_mem hb] at h_rank
  have h_rank' : (Fintype.card α : ℝ) + 1 - #B ≤ #{c | Bandits.gap ν c ≤ Bandits.gap ν b} := by
    have hBK : #B ≤ Fintype.card α := card_le_univ B
    have hB1 : 1 ≤ #B := card_pos.2 ⟨b, hb⟩
    calc (Fintype.card α : ℝ) + 1 - #B = (Fintype.card α - (#B - 1) : ℕ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub hB1]
          ring
      _ ≤ _ := by exact_mod_cast h_rank
  have hH := le_complexityTwo ν b
  have hH0 : 0 < complexityTwo ν :=
    (div_pos (by exact_mod_cast card_pos.2 ⟨b, by simp⟩) (pow_pos hΔ 2)).trans_le hH
  rw [div_le_iff₀ (pow_pos hΔ 2)] at hH
  rw [div_le_iff₀ hH0]
  nlinarith

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
  set x : ℝ := (T : ℝ) - K
  have hx : 0 ≤ x := by simp [x, hKT]
  have hL := one_half_le_logBar (K := K) (by omega)
  -- Each term of the sum is at most `exp(-(T - K) / (4 σ2 log‾ K H₂))`, since
  -- `n (k + 1) ≥ (T - K) / (log‾ K (K - k))` and `Δ_b² ≥ (K - k) / H₂` for `b ∈ B k`.
  have h_term (k : ℕ) (hk : k ∈ range (K - 1)) (b : α) (hb : b ∈ B k) :
      Real.exp (-(pullSchedule K T (k + 1) : ℝ) * Bandits.gap ν b ^ 2 / (4 * σ2)) ≤
        Real.exp (-x / (4 * σ2 * logBar K * complexityTwo ν)) := by
    have hKk : (0 : ℝ) < K - k := by
      have : (k : ℝ) + 1 < K := by exact_mod_cast (by have := mem_range.1 hk; omega : k + 1 < K)
      linarith
    have h_gap : (K - k : ℝ) / complexityTwo ν ≤ Bandits.gap ν b ^ 2 := by
      have := sub_card_div_complexityTwo_le_gap_sq ha' (hB_sub k) (hB_top k) hb
      rwa [hB_card' k hk, Nat.cast_add, Nat.cast_one, add_sub_add_right_eq_sub] at this
    have h_pulls : x / (logBar K * (K - k)) ≤ pullSchedule K T (k + 1) := by
      refine (le_of_eq ?_).trans (le_pullSchedule K T (Nat.succ_ne_zero k))
      rw [show ((K : ℝ) + 1 - ((k + 1 : ℕ) : ℝ)) = K - k by push_cast; ring]
    have h_main : x / (logBar K * complexityTwo ν) ≤
        pullSchedule K T (k + 1) * Bandits.gap ν b ^ 2 := by
      calc x / (logBar K * complexityTwo ν)
          = x / (logBar K * (K - k)) * ((K - k : ℝ) / complexityTwo ν) := by
            field_simp
        _ ≤ _ := mul_le_mul h_pulls h_gap (div_nonneg hKk.le ?_) (Nat.cast_nonneg _)
      exact (le_complexityTwo ν b).trans' (by positivity)
    refine Real.exp_le_exp.2 ?_
    rw [show -x / (4 * σ2 * logBar K * complexityTwo ν) =
      -(x / (logBar K * complexityTwo ν)) / (4 * σ2) by ring, neg_mul]
    exact div_le_div_of_nonneg_right (neg_le_neg h_main) (by positivity)
  calc ∑ k ∈ range (K - 1), ∑ b ∈ B k,
        Real.exp (-(pullSchedule K T (k + 1) : ℝ) * Bandits.gap ν b ^ 2 / (4 * σ2))
  _ ≤ ∑ k ∈ range (K - 1), ∑ _b ∈ B k, Real.exp (-x / (4 * σ2 * logBar K * complexityTwo ν)) :=
    sum_le_sum fun k hk ↦ sum_le_sum fun b hb ↦ h_term k hk b hb
  _ = (∑ k ∈ range (K - 1), ((k : ℝ) + 1)) *
      Real.exp (-x / (4 * σ2 * logBar K * complexityTwo ν)) := by
    rw [sum_mul]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [sum_const, hB_card' k hk, nsmul_eq_mul]
    push_cast
    ring
  _ = K * (K - 1) / 2 * Real.exp (-x / (4 * σ2 * logBar K * complexityTwo ν)) := by
    congr 1
    obtain ⟨m, hm⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
    have h_gauss := sum_range_id_mul_two (m + 1)
    rw [sum_range_succ'] at h_gauss
    rw [hm, Nat.add_sub_cancel]
    have : (∑ k ∈ range m, ((k : ℝ) + 1)) * 2 = (m + 1) * m := by exact_mod_cast h_gauss
    push_cast
    linarith

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
  have hσ : (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 = 1 / 4 := by
    ext
    norm_num
  have h_sub (a : α) : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) (1 / 4) (ν a) :=
    hσ ▸ hasSubgaussianMGF_of_mem_Icc aemeasurable_id (hν a)
  refine (measureReal_output_ne_le hKT h_sub ha' h).trans_eq ?_
  norm_num

end LMLExplore.Identification
