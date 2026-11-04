/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.IndexAlgorithm
public import LMLExplore.Identification.Tracking

/-!
# The cumulative tracking sampling rule

In the pure exploration algorithms of Degenne, Koolen and Ménard (2019), an online learner plays
an allocation `w(t)` at each round `t`, computed from the data, and the *cumulative tracking* rule
turns these allocations into arms: with `N_a(t)` the number of pulls of arm `a` in the first `t`
rounds, at round `t` it plays an arm minimizing the ratio `N_a(t) / ∑_{s ≤ t} w_a(s)` of the pull
count to the cumulated allocations. Equivalently, it plays an arm maximizing the index
`∑_{s ≤ t} w_a(s) / N_a(t)`, with index `⊤` for the arms not pulled yet, so that the first `K`
rounds pull every arm once, as in [DKM19], where `K` is the number of arms.

This file defines the rule as a deterministic algorithm (an index policy of LML) for any measurable
target rule, and proves that the hypothesis of the deterministic cumulative tracking lemmas of
`Identification/Tracking.lean` holds almost surely along every run. Consequently, along every run
whose targets are allocations [DKM19, Lemma 7]: after `n` rounds, every arm satisfies
`∑_{s < n} w_a(s) - (K - 1) ≤ N_a(n) ≤ ∑_{s < n} w_a(s) + 1`; the proportions of pulls get close
to the averages of the targets, and converge to the limit of the targets whenever the targets
converge.

Unlike C-tracking (`Identification/CTracking.lean`), cumulative tracking does not mix the targets
with the uniform allocation: it forces no exploration beyond the first `K` rounds, and the
deviation of the pull counts from the cumulated targets stays bounded by `K - 1` instead of growing
like `√n`.

## Main definitions

* `LMLExplore.Identification.cumulativeTrackingIndex w n h`: the index of the cumulative tracking
  rule after `n` rounds with history `h`, for the target rule `w`.
* `LMLExplore.Identification.cumulativeTracking w hw`: the cumulative tracking sampling rule with
  targets `w`, the deterministic algorithm that plays an arm of maximal `cumulativeTrackingIndex`.

## Main statements

In the namespace `LMLExplore.Identification.CumulativeTracking`, along every run of
`cumulativeTracking w hw`:

* `pullCount_card_eq_one`: almost surely, the first `K` rounds pull every arm once.
* `pullCount_mul_sum_le`: if the targets are nonnegative, then almost surely the arm played at
  round `k` minimizes `N_a(k) / ∑_{s ≤ k} w_a(s)`, in cross-multiplied form.
* `pullCount_le_sum_add_one`, `sum_sub_le_pullCount`, `abs_pullCount_sub_sum_le`: the guarantees
  of cumulative tracking [DKM19, Lemma 7].
* `tendsto_pullCount_div_sub_inv_mul_sum`, `tendsto_pullCount_div`: almost surely, the proportions
  of pulls get close to the averages of the targets, and converge to the limit of the targets
  whenever the targets converge.

## References

* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019, Algorithm 1 and Lemma 7 (in the numbering of arXiv:1906.10431).
-/

public section

open MeasureTheory ProbabilityTheory Learning Filter Finset
open scoped Topology

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} [DecidableEq α] {m𝓨 : MeasurableSpace 𝓨}
  {w : (n : ℕ) → Hist Unit α 𝓨 n → α → ℝ} {n : ℕ} {h : Hist Unit α 𝓨 n} {a : α}

/-! ### The index and the algorithm -/

/-- The index of the cumulative tracking rule with target rule `w`, after `n` rounds with history
`h`: `⊤` if the arm `a` has not been pulled, and otherwise the cumulated targets
`∑_{s ≤ n} w_a(s)` divided by the pull count `N_a` of `h`, where `w(s)` is the target `w s` of the
prefix of length `s` of `h` (for `s = n`, of `h` itself). -/
noncomputable def cumulativeTrackingIndex (w : (n : ℕ) → Hist Unit α 𝓨 n → α → ℝ) (n : ℕ)
    (h : Hist Unit α 𝓨 n) (a : α) : EReal :=
  if pullCount' n h a = 0 then ⊤ else
    ((∑ s : Fin (n + 1), w s (fun i ↦ h (Fin.castLE (Nat.lt_succ_iff.1 s.isLt) i)) a) /
      pullCount' n h a : ℝ)

/-- The index of cumulative tracking, unfolded. -/
lemma cumulativeTrackingIndex_def (w : (n : ℕ) → Hist Unit α 𝓨 n → α → ℝ) (n : ℕ)
    (h : Hist Unit α 𝓨 n) (a : α) :
    cumulativeTrackingIndex w n h a = if pullCount' n h a = 0 then ⊤ else
      (((∑ s : Fin (n + 1), w s (fun i ↦ h (Fin.castLE (Nat.lt_succ_iff.1 s.isLt) i)) a) /
        pullCount' n h a : ℝ) : EReal) :=
  (rfl)

/-- An arm that has not been pulled has index `⊤`. -/
@[simp]
lemma cumulativeTrackingIndex_of_pullCount'_eq_zero (h0 : pullCount' n h a = 0) :
    cumulativeTrackingIndex w n h a = ⊤ := by
  simp [cumulativeTrackingIndex_def, h0]

/-- The index of an arm that has been pulled is the cumulated targets divided by its pull
count. -/
lemma cumulativeTrackingIndex_of_pullCount'_ne_zero (h0 : pullCount' n h a ≠ 0) :
    cumulativeTrackingIndex w n h a =
      (((∑ s : Fin (n + 1), w s (fun i ↦ h (Fin.castLE (Nat.lt_succ_iff.1 s.isLt) i)) a) /
        pullCount' n h a : ℝ) : EReal) := by
  simp [cumulativeTrackingIndex_def, h0]

/-- The index of an arm is `⊤` if and only if the arm has not been pulled yet. -/
lemma cumulativeTrackingIndex_eq_top_iff :
    cumulativeTrackingIndex w n h a = ⊤ ↔ pullCount' n h a = 0 := by
  by_cases h0 : pullCount' n h a = 0
  · simp [h0]
  · simp [cumulativeTrackingIndex_of_pullCount'_ne_zero h0, h0]

/-- Along a sequence of rounds, the index of cumulative tracking at the history of the first `k`
rounds is `⊤` if the arm has not been pulled before round `k`, and otherwise
`∑_{s ≤ k} w_a(s) / N_a(k)`, with `w(s)` the target of the history of the first `s` rounds. -/
lemma cumulativeTrackingIndex_history {Ω : Type*} (O : ℕ → Ω → Unit) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → 𝓨) (k : ℕ) (ω : Ω) (a : α) :
    cumulativeTrackingIndex w k (history O A Y k ω) a = if pullCount A a k ω = 0 then ⊤ else
      (((∑ s ∈ range (k + 1), w s (history O A Y s ω) a) / pullCount A a k ω : ℝ) : EReal) := by
  have hS : ∑ s : Fin (k + 1),
      w s (fun i ↦ history O A Y k ω (Fin.castLE (Nat.lt_succ_iff.1 s.isLt) i)) a =
        ∑ s ∈ range (k + 1), w s (history O A Y s ω) a := by
    rw [← Fin.sum_univ_eq_sum_range (fun s ↦ w s (history O A Y s ω) a)]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [history_eq_comp_history (Nat.lt_succ_iff.1 s.isLt), Function.comp_apply]
  rw [cumulativeTrackingIndex_def, ← pullCount_eq_pullCount', hS]

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The index of cumulative tracking is a measurable function of the history if the target rule
is. -/
@[fun_prop]
lemma measurable_cumulativeTrackingIndex (hw : ∀ n, Measurable (w n)) :
    Measurable (cumulativeTrackingIndex w n) := by
  refine Measurable.of_eval fun a ↦ ?_
  simp_rw [cumulativeTrackingIndex_def]
  refine Measurable.ite ((measurableSet_singleton 0).preimage (measurable_pullCount' n a))
    measurable_const (measurable_coe_real_ereal.comp (Measurable.div ?_ ?_))
  · exact Finset.measurable_sum _ fun s _ ↦ (measurable_pi_apply a).comp
      ((hw s).comp (Measurable.of_eval fun _ ↦ measurable_pi_apply _))
  · exact measurable_from_top.comp (measurable_pullCount' n a)

variable [Fintype α] [Nonempty α]

/-- The **cumulative tracking** sampling rule with target rule `w` [DKM19, Algorithm 1]: the
deterministic algorithm that plays, after `n` rounds with history `h`, an arm of maximal
`cumulativeTrackingIndex w n h` (ties broken by LML's `argmax`), that is an arm not pulled yet if
there is one, and otherwise an arm minimizing `N_a / ∑_{s ≤ n} w_a(s)`. -/
noncomputable def cumulativeTracking (w : (n : ℕ) → Hist Unit α 𝓨 n → α → ℝ)
    (hw : ∀ n, Measurable (w n)) : Algorithm Unit α 𝓨 :=
  Bandits.indexAlgorithm (fun n x ↦ cumulativeTrackingIndex w n x.1)
    fun _ ↦ (measurable_cumulativeTrackingIndex hw).comp measurable_fst

variable {hw : ∀ n, Measurable (w n)}

/-- Cumulative tracking is the index policy whose index is `cumulativeTrackingIndex`. -/
lemma cumulativeTracking_eq_indexAlgorithm :
    cumulativeTracking w hw = Bandits.indexAlgorithm (fun n x ↦ cumulativeTrackingIndex w n x.1)
      (fun _ ↦ (measurable_cumulativeTrackingIndex hw).comp measurable_fst) :=
  (rfl)

instance : (cumulativeTracking w hw).IsDeterministic := by
  rw [cumulativeTracking_eq_indexAlgorithm]
  infer_instance

/-! ### Run lemmas -/

namespace CumulativeTracking

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {env : Environment Unit α 𝓨} {P : Measure Ω}
  [IsFiniteMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨}

/-- Cumulative tracking pulls every arm exactly once during the first `Fintype.card α` rounds. -/
lemma pullCount_card_eq_one (h : IsAlgEnvSeq O A Y (cumulativeTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ a, pullCount A a (Fintype.card α) ω = 1 := by
  rw [cumulativeTracking_eq_indexAlgorithm] at h
  exact Bandits.IndexAlgorithm.pullCount_card_eq_one h fun _ _ _ ↦
    cumulativeTrackingIndex_eq_top_iff

/-- **Tracking step of cumulative tracking.** If the targets are nonnegative, then almost surely,
the arm played at every round `k` minimizes `N_a(k) / ∑_{s ≤ k} w_a(s)`, in the cross-multiplied
form `N_{A_k}(k) ∑_{s ≤ k} w_a(s) ≤ N_a(k) ∑_{s ≤ k} w_{A_k}(s)`, with `w(s)` the target of the
history of the first `s` rounds. -/
lemma pullCount_mul_sum_le (hw0 : ∀ n h a, 0 ≤ w n h a)
    (h : IsAlgEnvSeq O A Y (cumulativeTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ k a,
      (pullCount A (A k ω) k ω : ℝ) * ∑ s ∈ range (k + 1), w s (history O A Y s ω) a ≤
        pullCount A a k ω * ∑ s ∈ range (k + 1), w s (history O A Y s ω) (A k ω) := by
  rw [cumulativeTracking_eq_indexAlgorithm] at h
  filter_upwards [Bandits.IndexAlgorithm.index_le_index_action h] with ω hω k a
  have hle := hω k a
  rw [cumulativeTrackingIndex_history, cumulativeTrackingIndex_history] at hle
  by_cases hk : pullCount A (A k ω) k ω = 0
  · -- The played arm has not been pulled yet: the left-hand side vanishes.
    rw [hk, Nat.cast_zero, zero_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun s _ ↦ hw0 _ _ _)
  · -- The played arm has a finite index, so `a` has been pulled and has a smaller index.
    have ha : pullCount A a k ω ≠ 0 := fun ha ↦ by simp [ha, hk] at hle
    simp only [ha, hk, ite_false, EReal.coe_le_coe_iff] at hle
    rw [div_le_div_iff₀ (Nat.cast_pos.2 (Nat.pos_of_ne_zero ha))
      (Nat.cast_pos.2 (Nat.pos_of_ne_zero hk))] at hle
    linarith

variable (hw0 : ∀ n h a, 0 ≤ w n h a) (hw1 : ∀ n h, ∑ a, w n h a = 1)
include hw0 hw1

/-- **Cumulative tracking, upper bound** [DKM19, Lemma 7]. If the targets are allocations, then
almost surely, after every number `n` of rounds, `N_a(n) ≤ ∑_{s < n} w_a(s) + 1` for every arm
`a`, with `w(s)` the target of the history of the first `s` rounds. -/
theorem pullCount_le_sum_add_one (h : IsAlgEnvSeq O A Y (cumulativeTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) a,
      (pullCount A a n ω : ℝ) ≤ ∑ s ∈ range n, w s (history O A Y s ω) a + 1 := by
  filter_upwards [pullCount_mul_sum_le hw0 h] with ω hω n a
  exact pullCount_le_sum_add_one_of_cumulativeTracking _ (fun k ↦ hw0 k _) (fun k ↦ hw1 k _) hω n a

/-- **Cumulative tracking, lower bound** [DKM19, Lemma 7]. If the targets are allocations, then
almost surely, after every number `n` of rounds, `∑_{s < n} w_a(s) - (K - 1) ≤ N_a(n)` for every
arm `a`, with `w(s)` the target of the history of the first `s` rounds. -/
theorem sum_sub_le_pullCount (h : IsAlgEnvSeq O A Y (cumulativeTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) a,
      ∑ s ∈ range n, w s (history O A Y s ω) a - (Fintype.card α - 1) ≤ pullCount A a n ω := by
  filter_upwards [pullCount_mul_sum_le hw0 h] with ω hω n a
  exact sum_sub_le_pullCount_of_cumulativeTracking _ (fun k ↦ hw0 k _) (fun k ↦ hw1 k _) hω n a

/-- **Tracking of cumulative tracking** [DKM19, Lemma 7]. If the targets are allocations, then
almost surely, after every number `n` of rounds, `|N_a(n) - ∑_{s < n} w_a(s)| ≤ K - 1` for every
arm `a`, with `w(s)` the target of the history of the first `s` rounds. -/
theorem abs_pullCount_sub_sum_le (h : IsAlgEnvSeq O A Y (cumulativeTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) a,
      |(pullCount A a n ω : ℝ) - ∑ s ∈ range n, w s (history O A Y s ω) a| ≤
        Fintype.card α - 1 := by
  filter_upwards [pullCount_mul_sum_le hw0 h] with ω hω n a
  exact abs_pullCount_sub_sum_le_of_cumulativeTracking _ (fun k ↦ hw0 k _) (fun k ↦ hw1 k _) hω
    n a

/-- **Proportions of pulls of cumulative tracking.** If the targets are allocations, then almost
surely, for every arm `a`, the difference between the proportion of pulls `N_a(n) / n` and the
average `n⁻¹ ∑_{s < n} w_a(s)` of the targets tends to `0`, with `w(s)` the target of the history
of the first `s` rounds. -/
theorem tendsto_pullCount_div_sub_inv_mul_sum
    (h : IsAlgEnvSeq O A Y (cumulativeTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n : ℕ ↦ (pullCount A a n ω : ℝ) / n -
      (n : ℝ)⁻¹ * ∑ s ∈ range n, w s (history O A Y s ω) a) atTop (𝓝 0) := by
  filter_upwards [pullCount_mul_sum_le hw0 h] with ω hω a
  exact tendsto_pullCount_div_sub_inv_mul_sum_of_cumulativeTracking _ (fun k ↦ hw0 k _)
    (fun k ↦ hw1 k _) hω a

/-- **Convergence of the proportions of pulls of cumulative tracking.** If the targets are
allocations, then almost surely, for every `l : α → ℝ`, if the targets `w_a(k)` of the histories
of the run converge to `l a` for every arm `a`, then the proportions of pulls `N_a(n) / n`
converge to `l a`. -/
theorem tendsto_pullCount_div (h : IsAlgEnvSeq O A Y (cumulativeTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ l : α → ℝ, (∀ a, Tendsto (fun k ↦ w k (history O A Y k ω) a) atTop (𝓝 (l a))) →
      ∀ a, Tendsto (fun n ↦ (pullCount A a n ω : ℝ) / n) atTop (𝓝 (l a)) := by
  filter_upwards [pullCount_mul_sum_le hw0 h] with ω hω l hl a
  exact tendsto_pullCount_div_of_cumulativeTracking _ (fun k ↦ hw0 k _) (fun k ↦ hw1 k _) hω
    (hl a)

end CumulativeTracking

end LMLExplore.Identification
