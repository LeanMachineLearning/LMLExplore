/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The linear program of stochastic rounding for e-BH

A stochastic rounding scheme replaces realized e-values by random ones of no larger means, and
applies e-BH to them. For one realization, the law of the rejection set of such a scheme is a
feasible point of a linear program, and conversely
(`LMLExplore.EValues.MultipleTesting.Rounding.Scheme`).
This file solves that linear program [EVR26, Note 30], the program which [XR23, Appendix,
"Generalization of stochastic rounding"] writes and leaves open.

`K` hypotheses have budgets `y i ≥ 0` (the e-values times `α / K`). A feasible point
(`ProbabilityTheory.IsRoundingFeasible`) gives a weight `p R ≥ 0` to every set `R` of
hypotheses (the probability that e-BH rejects exactly `R`), with `∑_R p R ≤ 1` and
`∑_{R ∋ i} p R / #R ≤ y i` for every `i`. Its objective
(`ProbabilityTheory.roundingObjective`) is the expected number of rejections `∑_R #R * p R`.
With the budgets sorted, `y_(1) ≥ … ≥ y_(K)` and `y_(K+1) = 0`, the largest objective is

  `V = min_{0 ≤ j ≤ K} [j + ∑_{k > j} k (k - j) (y_(k) - y_(k+1))]`

(`ProbabilityTheory.roundingValue`), attained by a nested point, which rejects the `N`
hypotheses with the largest budgets for a random `N`. U-eBH, which rejects
`N_U = max {k : u ≤ k y_(k)}` hypotheses when a uniform variable takes the value `u`
(`ProbabilityTheory.uebhCount`), gives a feasible nested point, hence does no better than `V`.

The program is symmetric in the hypotheses, so the main statements take antitone budgets
`y : Fin K → ℝ` (the hypothesis of index `i` has rank `i + 1`); the version for any order goes
through a sorting permutation.

## Main definitions

* `ProbabilityTheory.IsRoundingFeasible y p`, `ProbabilityTheory.roundingObjective p`: the
  feasible points of the linear program and their objective.
* `ProbabilityTheory.rankBudget y k`: the budget of rank `k`, `y_(k)`, with `y_(0) = y_(K+1) = 0`.
* `ProbabilityTheory.roundingDual y j`: the dual bound `D(j)`, and
  `ProbabilityTheory.roundingValue y`, its minimum over `0 ≤ j ≤ K`.
* `ProbabilityTheory.topRanks k`, `ProbabilityTheory.nestedPoint K q`: the set of the `k` first
  ranks, and the nested point that gives the weight `q k` to it.
* `ProbabilityTheory.roundingMass`, `ProbabilityTheory.roundingTailMass`,
  `ProbabilityTheory.roundingThreshold`, `ProbabilityTheory.optimalRoundingLaw`: the masses
  `c_k = k (y_(k) - y_(k+1))`, the tails `C_j = ∑_{k > j} c_k`, the threshold
  `m = min {j | C_j ≤ 1}` and the law of the number of rejections of the optimal nested point.
* `ProbabilityTheory.uebhCount y u`, `ProbabilityTheory.uebhLaw y`: the number of rejections of
  U-eBH and its law.

## Main statements

* `ProbabilityTheory.roundingObjective_le_roundingDual`: the dual bound, for budgets in any
  order.
* `ProbabilityTheory.isRoundingFeasible_nestedPoint_optimalRoundingLaw`,
  `ProbabilityTheory.roundingObjective_nestedPoint_optimalRoundingLaw`,
  `ProbabilityTheory.isGreatest_roundingObjective`: the value of the program, attained by a nested
  point [EVR26, Note 30, Theorem].
* `ProbabilityTheory.isGreatest_roundingObjective_of_antitone_comp`: the same for budgets in any
  order.
* `ProbabilityTheory.isGreatest_roundingObjective_of_sum_le_one`: when `∑ i, y i ≤ 1`, the value
  is `∑_k (2k - 1) y_(k)`.
* `ProbabilityTheory.isRoundingFeasible_nestedPoint_uebhLaw`,
  `ProbabilityTheory.integral_uebhCount_le_roundingValue`: U-eBH is feasible, so its expected
  number of rejections is at most `V` [EVR26, Note 30, Theorem, Statement 3].

## Implementation notes

The dual bound uses the weights `u_i = (i+1)(i+1-j)⁺ - i(i-j)⁺`, which do not depend on the
budgets, so it holds for budgets in any order; the optimality of `min_j D(j)` then comes from the
feasibility of the nested point, whose objective is `D(m)`. For U-eBH, the budget of the
hypothesis of rank `r` is bounded through a rank `k' ≥ r` maximizing `k y_(k)` over
`r ≤ k ≤ K`: whenever U-eBH rejects at least `r` hypotheses it rejects at least `k'`, and then
`u ≤ k' y_(k')`, so the budget used is at most `P(U ≤ k' y_(k')) / k' ≤ y_(k')`.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 30, "The
  optimal stochastic rounding for e-BH", and its Lean proof in the library `EValuesResearch` of
  github.com/RemyDegenne/evalues_research (Apache 2.0), which this file adapts, 2026.
* [XR23] Z. Xu and A. Ramdas, *More powerful multiple testing under dependence via
  randomization*, arXiv:2305.11126.
-/

public section

open MeasureTheory Finset

namespace ProbabilityTheory

variable {K : ℕ}

/-! ### The linear program -/

/-- A feasible point of the linear program (P) of stochastic rounding for e-BH with budgets `y`
([EVR26, Note 30, proof of the Theorem]): a nonnegative weight `p R` for every set `R` of
hypotheses (the probability that e-BH rejects exactly `R`), of total mass at most one, such that
every hypothesis `i` receives at most its budget `y i`, a set `R` giving `p R / |R|` to each of its
members. The weight of the empty set plays no role but in the total mass. -/
structure IsRoundingFeasible (y : Fin K → ℝ) (p : Finset (Fin K) → ℝ) : Prop where
  /-- The weights are nonnegative. -/
  nonneg : ∀ R, 0 ≤ p R
  /-- The weights have total mass at most one. -/
  sum_le_one : ∑ R, p R ≤ 1
  /-- Every hypothesis receives at most its budget. -/
  budget_le : ∀ i, ∑ R with i ∈ R, p R / R.card ≤ y i

/-- The objective `∑_R |R| p_R` of the linear program of stochastic rounding: the expected number
of rejections. -/
def roundingObjective (p : Finset (Fin K) → ℝ) : ℝ := ∑ R, (R.card : ℝ) * p R

theorem roundingObjective_def (p : Finset (Fin K) → ℝ) :
    roundingObjective p = ∑ R, (R.card : ℝ) * p R :=
  (rfl)

/-- The budget of rank `k`, counted from `1`: `y ⟨k - 1, _⟩` for `1 ≤ k ≤ K`, and `0` otherwise,
so that `rankBudget y (K + 1) = 0` as in the note. When `y` is antitone, it is the `k`-th largest
budget `y_(k)`. -/
def rankBudget (y : Fin K → ℝ) (k : ℕ) : ℝ :=
  if h : 0 < k ∧ k - 1 < K then y ⟨k - 1, h.2⟩ else 0

/-- The budget of rank `k`, for `1 ≤ k ≤ K`, is the budget of index `k - 1`. -/
theorem rankBudget_of_pos_of_le (y : Fin K → ℝ) {k : ℕ} (hk : 0 < k) (hkK : k ≤ K) :
    rankBudget y k = y ⟨k - 1, by omega⟩ :=
  dite_eq_left ⟨hk, by omega⟩

/-- The dual bound `D(j) = j + ∑_{j < k ≤ K} k (k - j) (y_(k) - y_(k+1))` of [EVR26, Note 30]. -/
def roundingDual (y : Fin K → ℝ) (j : ℕ) : ℝ :=
  j + ∑ k ∈ Ioc j K, (k : ℝ) * ((k : ℝ) - j) * (rankBudget y k - rankBudget y (k + 1))

theorem roundingDual_def (y : Fin K → ℝ) (j : ℕ) :
    roundingDual y j =
      j + ∑ k ∈ Ioc j K, (k : ℝ) * ((k : ℝ) - j) * (rankBudget y k - rankBudget y (k + 1)) :=
  (rfl)

/-- The value `V = min_{0 ≤ j ≤ K} D(j)` of the linear program of stochastic rounding: for
antitone nonnegative budgets, the largest expected number of rejections of a rounding scheme
(`isGreatest_roundingObjective`). -/
noncomputable def roundingValue (y : Fin K → ℝ) : ℝ := ⨅ j : Fin (K + 1), roundingDual y j

theorem roundingValue_def (y : Fin K → ℝ) :
    roundingValue y = ⨅ j : Fin (K + 1), roundingDual y j :=
  (rfl)

/-- The value is at most every dual bound `D(j)`, `j ≤ K`. -/
theorem roundingValue_le_roundingDual (y : Fin K → ℝ) {j : ℕ} (hj : j ≤ K) :
    roundingValue y ≤ roundingDual y j :=
  ciInf_le (Set.finite_range _).bddBelow (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (K + 1))

/-- A lower bound of every dual bound `D(j)`, `j ≤ K`, is a lower bound of the value. -/
theorem le_roundingValue {y : Fin K → ℝ} {c : ℝ} (h : ∀ j ≤ K, c ≤ roundingDual y j) :
    c ≤ roundingValue y :=
  le_ciInf fun j ↦ h j (Nat.lt_succ_iff.1 j.isLt)

/-! ### Nested points -/

/-- The set of the hypotheses of rank at most `k`, that is of index less than `k`; when the
budgets are antitone, the `k` hypotheses with the largest budgets. -/
def topRanks (k : ℕ) : Finset (Fin K) := {i | (i : ℕ) < k}

/-- The nested point with law `q`: it rejects the set `topRanks k` of the hypotheses of rank at most
`k` with probability `q k`, for `0 ≤ k ≤ K`, and no other set. -/
def nestedPoint (K : ℕ) (q : ℕ → ℝ) (R : Finset (Fin K)) : ℝ :=
  ∑ k ∈ range (K + 1), if R = topRanks k then q k else 0

theorem nestedPoint_def (K : ℕ) (q : ℕ → ℝ) (R : Finset (Fin K)) :
    nestedPoint K q R = ∑ k ∈ range (K + 1), if R = topRanks k then q k else 0 :=
  (rfl)

/-- The mass `c_k = k (y_(k) - y_(k+1))` of [EVR26, Note 30]. -/
def roundingMass (y : Fin K → ℝ) (k : ℕ) : ℝ := k * (rankBudget y k - rankBudget y (k + 1))

theorem roundingMass_def (y : Fin K → ℝ) (k : ℕ) :
    roundingMass y k = k * (rankBudget y k - rankBudget y (k + 1)) :=
  (rfl)

/-- The tail mass `C_j = ∑_{j < k ≤ K} c_k` of [EVR26, Note 30]. -/
def roundingTailMass (y : Fin K → ℝ) (j : ℕ) : ℝ := ∑ k ∈ Ioc j K, roundingMass y k

theorem roundingTailMass_def (y : Fin K → ℝ) (j : ℕ) :
    roundingTailMass y j = ∑ k ∈ Ioc j K, roundingMass y k :=
  (rfl)

/-- The threshold `m = min {j : C_j ≤ 1}` of [EVR26, Note 30]; since `C_K = 0`, `m ≤ K`. -/
noncomputable def roundingThreshold (y : Fin K → ℝ) : ℕ := sInf {j | roundingTailMass y j ≤ 1}

theorem roundingThreshold_def (y : Fin K → ℝ) :
    roundingThreshold y = sInf {j | roundingTailMass y j ≤ 1} :=
  (rfl)

/-- The law of the number `N` of rejections of the optimal nested scheme of [EVR26, Note 30,
Theorem]: `P(N = k) = c_k` for `k > m`, `P(N = m) = 1 - C_m`, and `P(N = k) = 0` for `k < m`. -/
noncomputable def optimalRoundingLaw (y : Fin K → ℝ) (k : ℕ) : ℝ :=
  if roundingThreshold y < k then roundingMass y k
  else if k = roundingThreshold y then 1 - roundingTailMass y (roundingThreshold y) else 0

theorem optimalRoundingLaw_def (y : Fin K → ℝ) (k : ℕ) :
    optimalRoundingLaw y k = if roundingThreshold y < k then roundingMass y k
      else if k = roundingThreshold y then 1 - roundingTailMass y (roundingThreshold y) else 0 :=
  (rfl)

/-! ### U-eBH -/

/-- The number `N_U = max {k : k y_(k) ≥ u}` of rejections of U-eBH when the uniform variable `U`
takes the value `u` ([EVR26, Note 30, Theorem, Statement 3]), `0` when no `1 ≤ k ≤ K` satisfies
`k y_(k) ≥ u`. -/
noncomputable def uebhCount (y : Fin K → ℝ) (u : ℝ) : ℕ :=
  ({k ∈ Icc 1 K | u ≤ k * rankBudget y k}).sup id

theorem uebhCount_def (y : Fin K → ℝ) (u : ℝ) :
    uebhCount y u = ({k ∈ Icc 1 K | u ≤ k * rankBudget y k}).sup id :=
  (rfl)

/-- The law of `N_U` for `U` uniform on `[0, 1]`: `P(N_U = k)` is the length of the set of the
`u ∈ [0, 1]` at which U-eBH rejects `k` hypotheses. -/
noncomputable def uebhLaw (y : Fin K → ℝ) (k : ℕ) : ℝ :=
  volume.real {u ∈ Set.Icc (0 : ℝ) 1 | uebhCount y u = k}

theorem uebhLaw_def (y : Fin K → ℝ) (k : ℕ) :
    uebhLaw y k = volume.real {u ∈ Set.Icc (0 : ℝ) 1 | uebhCount y u = k} :=
  (rfl)

/-! ### Sums over ranks -/

/-- The budget of rank `i + 1` is the budget of index `i`. -/
theorem rankBudget_succ (y : Fin K → ℝ) (i : Fin K) : rankBudget y (i + 1) = y i := by
  rw [rankBudget, dite_eq_left ⟨Nat.succ_pos _, by simp⟩]
  rfl

/-- The budgets of rank `0` and above `K` are `0`. -/
theorem rankBudget_eq_zero (y : Fin K → ℝ) {k : ℕ} (hk : k = 0 ∨ K < k) : rankBudget y k = 0 := by
  rw [rankBudget, dite_eq_right]
  omega

/-- A sum over the ranks `j < k ≤ n` as a sum over `range n`. -/
private lemma sum_Ioc_eq_sum_range_ite (j n : ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ Ioc j n, F k = ∑ k ∈ range n, if j ≤ k then F (k + 1) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← ih]
    by_cases hj : j ≤ n
    · rw [sum_Ioc_succ_top hj, ite_eq_left hj]
    · rw [ite_eq_right hj, add_zero, Ioc_eq_empty (by omega), Ioc_eq_empty (by omega)]

/-- A sum over the ranks `a < k ≤ K` as a sum over `range (K + 1)`. -/
private lemma sum_range_ite_lt (a K : ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ range (K + 1), (if a < k then F k else 0) = ∑ k ∈ Ioc a K, F k := by
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range, mem_Ioc]
  omega

/-- Telescoping over the ranks `i < k ≤ n`. -/
private lemma sum_Ioc_sub_succ (g : ℕ → ℝ) {i n : ℕ} (hin : i ≤ n) :
    ∑ k ∈ Ioc i n, (g k - g (k + 1)) = g (i + 1) - g (n + 1) := by
  induction n, hin using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [sum_Ioc_succ_top hn, ih]
    ring

/-- **Summation by parts** against the ranked budgets: for a potential `P` with `P 0 = 0`, the sum
of the increments `P (i + 1) - P i` weighted by the budgets is the sum of `P (k + 1)` weighted by
the decrements `y_(k+1) - y_(k+2)`. -/
private lemma sum_sub_mul_eq_sum_range (y : Fin K → ℝ) (P : ℕ → ℝ) (hP : P 0 = 0) :
    ∑ i : Fin K, (P (i + 1) - P i) * y i =
      ∑ k ∈ range K, P (k + 1) * (rankBudget y (k + 1) - rankBudget y (k + 1 + 1)) := by
  have key : ∀ n, ∑ k ∈ range n, (P (k + 1) - P k) * rankBudget y (k + 1) =
      ∑ k ∈ range n, P (k + 1) * (rankBudget y (k + 1) - rankBudget y (k + 1 + 1)) +
        P n * rankBudget y (n + 1) - P 0 * rankBudget y 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, sum_range_succ, ih]
      ring
  have hK := key K
  rw [← Fin.sum_univ_eq_sum_range (fun k ↦ (P (k + 1) - P k) * rankBudget y (k + 1)) K] at hK
  simp only [rankBudget_succ] at hK
  rw [hK, rankBudget_eq_zero y (Or.inr (Nat.lt_succ_self K)), hP]
  ring

/-! ### The dual bound -/

/-- The potential `r (r - j)⁺` of the dual weights for the multiplier `j`. -/
private def dualPotential (j r : ℕ) : ℝ := if r ≤ j then 0 else r * ((r : ℝ) - j)

/-- The dual weight `(r + 1) (r + 1 - j)⁺ - r (r - j)⁺` of the hypothesis of index `r` (rank
`r + 1`) for the multiplier `j`. -/
private def dualWeight (j r : ℕ) : ℝ := dualPotential j (r + 1) - dualPotential j r

/-- The dual weight is `0` below `j` and `2 r + 1 - j` from `j` on. -/
private lemma dualWeight_eq (j r : ℕ) :
    dualWeight j r = if r < j then (0 : ℝ) else 2 * (r : ℝ) + 1 - j := by
  unfold dualWeight dualPotential
  by_cases hr : r < j
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left hr, sub_zero]
  · by_cases hrj : r = j
    · subst hrj
      rw [ite_eq_right (by omega), ite_eq_left le_rfl, ite_eq_right hr]
      push_cast
      ring
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hr]
      push_cast
      ring

/-- The dual weights are nonnegative. -/
private lemma dualWeight_nonneg (j r : ℕ) : 0 ≤ dualWeight j r := by
  rw [dualWeight_eq]
  split_ifs with h
  · exact le_rfl
  · have : (j : ℝ) ≤ r := by exact_mod_cast not_lt.1 h
    linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

/-- The dual weights are nondecreasing in the rank. -/
private lemma monotone_dualWeight (j : ℕ) : Monotone (dualWeight j) := by
  intro r s hrs
  rw [dualWeight_eq, dualWeight_eq]
  have hrs' : (r : ℝ) ≤ s := by exact_mod_cast hrs
  split_ifs with h1 h2 h2
  · exact le_rfl
  · have : (j : ℝ) ≤ s := by exact_mod_cast not_lt.1 h2
    linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  · omega
  · linarith

/-- A nondecreasing function summed over a set `R` of indices is at least its sum over the first
`|R|` indices. -/
private lemma sum_range_card_le_sum {g : ℕ → ℝ} (hg : Monotone g) (R : Finset (Fin K)) :
    ∑ t ∈ range R.card, g t ≤ ∑ i ∈ R, g i := by
  induction R using Finset.induction_on_max with
  | empty => simp
  | insert a s has ih =>
    have hcard : s.card ≤ a := by
      calc s.card = (s.map Fin.valEmbedding).card := (card_map _).symm
        _ ≤ (range a).card := card_le_card fun x hx ↦ by
            obtain ⟨i, hi, rfl⟩ := mem_map.1 hx
            exact mem_range.2 (has i hi)
        _ = a := card_range _
    have ha : a ∉ s := fun h ↦ lt_irrefl _ (has a h)
    rw [card_insert_of_notMem ha, sum_range_succ, sum_insert ha]
    linarith [hg hcard]

/-- The dual constraint: for every set `R`, `|R|² ≤ ∑_{i ∈ R} u_i + j |R|`. -/
private lemma card_sq_le_sum_dualWeight (j : ℕ) (R : Finset (Fin K)) :
    (R.card : ℝ) ^ 2 ≤ ∑ i ∈ R, dualWeight j i + j * R.card := by
  have h := sum_range_card_le_sum (monotone_dualWeight j) R
  rw [show ∑ t ∈ range R.card, dualWeight j t = dualPotential j R.card - dualPotential j 0 from
    sum_range_sub (dualPotential j) _] at h
  have h0 : dualPotential j 0 = 0 := by simp [dualPotential]
  have hP : (R.card : ℝ) * (R.card - j) ≤ dualPotential j R.card := by
    unfold dualPotential
    split_ifs with hc
    · have : (R.card : ℝ) ≤ j := by exact_mod_cast hc
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
    · exact le_rfl
  nlinarith

/-- The dual value: `∑_i u_i y_i + j = D(j)`, by summation by parts. -/
private lemma sum_dualWeight_mul_add_eq_roundingDual (y : Fin K → ℝ) (j : ℕ) :
    ∑ i : Fin K, dualWeight j i * y i + j = roundingDual y j := by
  have h := sum_sub_mul_eq_sum_range y (dualPotential j) (by simp [dualPotential])
  change ∑ i : Fin K, dualWeight j i * y i = _ at h
  rw [h, roundingDual, add_comm, sum_Ioc_eq_sum_range_ite]
  congr 1
  refine sum_congr rfl fun k _ ↦ ?_
  unfold dualPotential
  by_cases hjk : j ≤ k
  · rw [ite_eq_left hjk, ite_eq_right (by omega)]
  · rw [ite_eq_right hjk, ite_eq_left (by omega), zero_mul]

/-- **The dual bound** [EVR26, Note 30, Theorem, proof]: every feasible point of the linear
program has objective at most `D(j)`, for every `j`. The budgets need not be sorted: `D(j)` is then
computed with the budgets in the order of the indices. -/
theorem roundingObjective_le_roundingDual {y : Fin K → ℝ} {p : Finset (Fin K) → ℝ}
    (hp : IsRoundingFeasible y p) (j : ℕ) : roundingObjective p ≤ roundingDual y j := by
  set w : Fin K → ℝ := fun i ↦ dualWeight j i with hw
  have hR : ∀ R : Finset (Fin K),
      (R.card : ℝ) * p R ≤ (∑ i ∈ R, w i) * (p R / R.card) + j * p R := by
    intro R
    rcases R.eq_empty_or_nonempty with rfl | hne
    · simpa using mul_nonneg (Nat.cast_nonneg j) (hp.nonneg ∅)
    · have hc : (0 : ℝ) < R.card := by exact_mod_cast hne.card_pos
      have key := mul_le_mul_of_nonneg_right (card_sq_le_sum_dualWeight j R)
        (div_nonneg (hp.nonneg R) hc.le)
      calc (R.card : ℝ) * p R = (R.card : ℝ) ^ 2 * (p R / R.card) := by field_simp
        _ ≤ (∑ i ∈ R, w i + j * R.card) * (p R / R.card) := key
        _ = (∑ i ∈ R, w i) * (p R / R.card) + j * p R := by field_simp
  have hswap : ∑ R : Finset (Fin K), (∑ i ∈ R, w i) * (p R / R.card) =
      ∑ i, w i * ∑ R with i ∈ R, p R / R.card := by
    simp_rw [sum_mul, mul_sum]
    exact sum_comm' fun R i ↦ by simp
  calc roundingObjective p = ∑ R, (R.card : ℝ) * p R := rfl
    _ ≤ ∑ R, ((∑ i ∈ R, w i) * (p R / R.card) + j * p R) := sum_le_sum fun R _ ↦ hR R
    _ = ∑ i, w i * ∑ R with i ∈ R, p R / R.card + j * ∑ R, p R := by
        rw [sum_add_distrib, hswap, mul_sum]
    _ ≤ ∑ i, w i * y i + j * 1 := by
        gcongr with i
        · exact dualWeight_nonneg j i
        · exact hp.budget_le i
        · exact hp.sum_le_one
    _ = roundingDual y j := by rw [mul_one, hw, sum_dualWeight_mul_add_eq_roundingDual]

/-! ### Nested points -/

/-- The indices of `topRanks k` are the numbers below `k`, for `k ≤ K`. -/
private lemma map_topRanks {k : ℕ} (hk : k ≤ K) :
    (topRanks (K := K) k).map Fin.valEmbedding = range k := by
  ext x
  simp only [topRanks, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    exact ⟨⟨x, by omega⟩, hx, rfl⟩

/-- `topRanks k` has `k` elements, for `k ≤ K`. -/
theorem card_topRanks {k : ℕ} (hk : k ≤ K) : (topRanks (K := K) k).card = k := by
  rw [← card_map Fin.valEmbedding, map_topRanks hk, card_range]

/-- Membership in `topRanks k`. -/
theorem mem_topRanks {i : Fin K} {k : ℕ} : i ∈ topRanks k ↔ (i : ℕ) < k := by
  simp [topRanks]

/-- A sum against a nested point is a sum over its law. -/
private lemma sum_mul_nestedPoint (q : ℕ → ℝ) (f : Finset (Fin K) → ℝ) :
    ∑ R, f R * nestedPoint K q R = ∑ k ∈ range (K + 1), f (topRanks k) * q k := by
  simp_rw [nestedPoint, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ ↦ ?_
  simp_rw [mul_ite, mul_zero]
  rw [sum_ite_eq' univ (topRanks k)]
  simp

/-- The objective of a nested point is the mean `∑_k k q_k` of its law. -/
theorem roundingObjective_nestedPoint (q : ℕ → ℝ) :
    roundingObjective (nestedPoint K q) = ∑ k ∈ range (K + 1), (k : ℝ) * q k := by
  rw [roundingObjective, sum_mul_nestedPoint]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [card_topRanks (Nat.lt_succ_iff.1 (mem_range.1 hk))]

/-- A nested point is feasible when its law is nonnegative, of total mass at most one, and gives
the hypothesis of index `i` at most its budget: `∑_{i < k ≤ K} q_k / k ≤ y i`. -/
theorem isRoundingFeasible_nestedPoint {y : Fin K → ℝ} {q : ℕ → ℝ} (hq : ∀ k ≤ K, 0 ≤ q k)
    (hsum : ∑ k ∈ range (K + 1), q k ≤ 1)
    (hb : ∀ i : Fin K, ∑ k ∈ Ioc (i : ℕ) K, q k / k ≤ y i) :
    IsRoundingFeasible y (nestedPoint K q) where
  nonneg R := sum_nonneg fun k hk ↦ by
    split_ifs
    · exact hq k (Nat.lt_succ_iff.1 (mem_range.1 hk))
    · exact le_rfl
  sum_le_one := by
    have h := sum_mul_nestedPoint q (fun _ : Finset (Fin K) ↦ (1 : ℝ))
    simp only [one_mul] at h
    rw [h]
    exact hsum
  budget_le i := by
    have h := sum_mul_nestedPoint q (fun R ↦ if i ∈ R then 1 / (R.card : ℝ) else 0)
    rw [sum_filter]
    calc ∑ R, (if i ∈ R then nestedPoint K q R / R.card else 0)
        = ∑ R, (if i ∈ R then 1 / (R.card : ℝ) else 0) * nestedPoint K q R := by
          refine sum_congr rfl fun R _ ↦ ?_
          split_ifs <;> ring
      _ = ∑ k ∈ range (K + 1),
            (if i ∈ topRanks k then 1 / ((topRanks (K := K) k).card : ℝ) else 0) * q k := h
      _ = ∑ k ∈ range (K + 1), if (i : ℕ) < k then q k / k else 0 := by
          refine sum_congr rfl fun k hk ↦ ?_
          rw [card_topRanks (Nat.lt_succ_iff.1 (mem_range.1 hk))]
          by_cases hik : (i : ℕ) < k
          · rw [ite_eq_left (mem_topRanks.2 hik), ite_eq_left hik]
            ring
          · rw [ite_eq_right (fun h ↦ hik (mem_topRanks.1 h)), ite_eq_right hik, zero_mul]
      _ = ∑ k ∈ Ioc (i : ℕ) K, q k / k := sum_range_ite_lt _ _ _
      _ ≤ y i := hb i

/-! ### The optimal nested scheme -/

section Optimal

variable {y : Fin K → ℝ}

/-- Nonnegative budgets give nonnegative ranked budgets. -/
theorem rankBudget_nonneg (hy0 : ∀ i, 0 ≤ y i) (k : ℕ) : 0 ≤ rankBudget y k := by
  unfold rankBudget
  split_ifs
  exacts [hy0 _, le_rfl]

/-- Antitone nonnegative budgets give ranked budgets that are antitone from rank `1` on. -/
theorem rankBudget_le_rankBudget (hy : Antitone y) (hy0 : ∀ i, 0 ≤ y i) {k l : ℕ} (hk : 0 < k)
    (hkl : k ≤ l) : rankBudget y l ≤ rankBudget y k := by
  by_cases hl : 0 < l ∧ l - 1 < K
  · rw [rankBudget, rankBudget, dite_eq_left hl, dite_eq_left ⟨hk, by omega⟩]
    exact hy (Fin.mk_le_mk.2 (by omega))
  · rw [rankBudget_eq_zero y (by omega)]
    exact rankBudget_nonneg hy0 k

/-- The masses `c_k` are nonnegative. -/
theorem roundingMass_nonneg (hy : Antitone y) (hy0 : ∀ i, 0 ≤ y i) (k : ℕ) :
    0 ≤ roundingMass y k := by
  unfold roundingMass
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact mul_nonneg (Nat.cast_nonneg k)
      (sub_nonneg.2 (rankBudget_le_rankBudget hy hy0 hk (Nat.le_succ k)))

/-- `c_k / k = y_(k) - y_(k+1)`. -/
private lemma roundingMass_div (y : Fin K → ℝ) {k : ℕ} (hk : 0 < k) :
    roundingMass y k / k = rankBudget y k - rankBudget y (k + 1) := by
  have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [roundingMass]
  field_simp

/-- `∑_{i < k ≤ K} c_k / k = y_(i+1)`. -/
private lemma sum_Ioc_roundingMass_div (y : Fin K → ℝ) {i : ℕ} (hi : i ≤ K) :
    ∑ k ∈ Ioc i K, roundingMass y k / k = rankBudget y (i + 1) := by
  rw [sum_congr rfl fun k hk ↦ roundingMass_div y (by have := (mem_Ioc.1 hk).1; omega),
    sum_Ioc_sub_succ _ hi, rankBudget_eq_zero y (Or.inr (Nat.lt_succ_self K)), sub_zero]

/-- `C_j = c_{j+1} + C_{j+1}` for `j < K`. -/
private lemma roundingTailMass_eq_add (y : Fin K → ℝ) {j : ℕ} (hj : j < K) :
    roundingTailMass y j = roundingMass y (j + 1) + roundingTailMass y (j + 1) := by
  unfold roundingTailMass
  rw [← sum_Ioc_consecutive _ (Nat.le_succ j) hj, Nat.Ioc_succ_singleton, sum_singleton]

/-- `C_K = 0`. -/
theorem roundingTailMass_self (y : Fin K → ℝ) : roundingTailMass y K = 0 := by
  simp [roundingTailMass]

/-- The threshold is at most `K`. -/
theorem roundingThreshold_le (y : Fin K → ℝ) : roundingThreshold y ≤ K :=
  Nat.sInf_le (by simp [roundingTailMass_self])

/-- `C_m ≤ 1`. -/
theorem roundingTailMass_roundingThreshold_le (y : Fin K → ℝ) :
    roundingTailMass y (roundingThreshold y) ≤ 1 :=
  Nat.sInf_mem (s := {j | roundingTailMass y j ≤ 1}) ⟨K, by simp [roundingTailMass_self]⟩

/-- `C_j > 1` below the threshold. -/
theorem one_lt_roundingTailMass {j : ℕ} (hj : j < roundingThreshold y) : 1 < roundingTailMass y j :=
  not_le.1 (Nat.notMem_of_lt_sInf hj)

/-- The optimal law splits into its masses above the threshold and its atom at the threshold. -/
private lemma optimalRoundingLaw_eq (y : Fin K → ℝ) (k : ℕ) :
    optimalRoundingLaw y k = (if roundingThreshold y < k then roundingMass y k else 0) +
      (if k = roundingThreshold y then 1 - roundingTailMass y (roundingThreshold y) else 0) := by
  unfold optimalRoundingLaw
  split_ifs <;> first | (exfalso; omega) | ring

/-- A sum against the optimal law: `∑_k g_k P(N = k) = g_m (1 - C_m) + ∑_{k > m} g_k c_k`. -/
private lemma sum_mul_optimalRoundingLaw (y : Fin K → ℝ) (g : ℕ → ℝ) :
    ∑ k ∈ range (K + 1), g k * optimalRoundingLaw y k =
      g (roundingThreshold y) * (1 - roundingTailMass y (roundingThreshold y)) +
        ∑ k ∈ Ioc (roundingThreshold y) K, g k * roundingMass y k := by
  simp_rw [optimalRoundingLaw_eq, mul_add, sum_add_distrib, mul_ite, mul_zero]
  rw [sum_range_ite_lt _ _ (fun k ↦ g k * roundingMass y k), sum_ite_eq' (range (K + 1)),
    ite_eq_left (mem_range.2 (Nat.lt_succ_of_le (roundingThreshold_le y)))]
  ring

/-- The objective of the optimal nested point is `D(m)`, that is
`∑_{k > m} k c_k + m (1 - C_m)`. -/
private lemma roundingObjective_nestedPoint_optimalRoundingLaw_eq_roundingDual (y : Fin K → ℝ) :
    roundingObjective (nestedPoint K (optimalRoundingLaw y)) =
      roundingDual y (roundingThreshold y) := by
  rw [roundingObjective_nestedPoint, sum_mul_optimalRoundingLaw, roundingDual, roundingTailMass,
    mul_sub,
    mul_one, mul_sum]
  have : ∑ k ∈ Ioc (roundingThreshold y) K, (k : ℝ) * ((k : ℝ) - roundingThreshold y) *
        (rankBudget y k - rankBudget y (k + 1)) =
      ∑ k ∈ Ioc (roundingThreshold y) K, (k : ℝ) * roundingMass y k -
        ∑ k ∈ Ioc (roundingThreshold y) K, (roundingThreshold y : ℝ) * roundingMass y k := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [roundingMass]
    ring
  rw [this]
  ring

/-- The weights of the optimal law are nonnegative, for antitone nonnegative budgets. -/
theorem optimalRoundingLaw_nonneg (hy : Antitone y) (hy0 : ∀ i, 0 ≤ y i) (k : ℕ) :
    0 ≤ optimalRoundingLaw y k := by
  have hCm := roundingTailMass_roundingThreshold_le y
  unfold optimalRoundingLaw
  split_ifs
  · exact roundingMass_nonneg hy hy0 k
  · linarith
  · exact le_rfl

/-- The optimal law is a probability law on `{0, …, K}`: `∑_{k > m} c_k + (1 - C_m) = 1`. -/
theorem sum_optimalRoundingLaw (y : Fin K → ℝ) :
    ∑ k ∈ range (K + 1), optimalRoundingLaw y k = 1 := by
  have h := sum_mul_optimalRoundingLaw y (fun _ ↦ 1)
  simp only [one_mul] at h
  rw [h, ← roundingTailMass]
  ring

/-- The optimal law gives the hypothesis of index `i` at most its budget:
`∑_{i < k ≤ K} P(N = k) / k ≤ y i`, with equality for the ranks `i + 1 > m`. -/
theorem sum_Ioc_optimalRoundingLaw_div_le (hy : Antitone y) (hy0 : ∀ i, 0 ≤ y i) (i : Fin K) :
    ∑ k ∈ Ioc (i : ℕ) K, optimalRoundingLaw y k / k ≤ y i := by
  have hmK := roundingThreshold_le y
  rcases le_or_gt (roundingThreshold y) i with hmi | hmi
  · -- rank `i + 1 > m`: the budget is spent exactly
    rw [sum_congr rfl fun k hk ↦ by
        rw [optimalRoundingLaw, ite_eq_left (by have := (mem_Ioc.1 hk).1; omega)],
      sum_Ioc_roundingMass_div y i.isLt.le, rankBudget_succ]
  · -- rank `i + 1 ≤ m`
    obtain ⟨m', hm'⟩ : ∃ m', roundingThreshold y = m' + 1 := ⟨roundingThreshold y - 1, by omega⟩
    have hlt := one_lt_roundingTailMass (y := y) (j := m') (by omega)
    rw [roundingTailMass_eq_add y (by omega), ← hm'] at hlt
    have hm0 : (0 : ℝ) < roundingThreshold y := by
      exact_mod_cast (by omega : 0 < roundingThreshold y)
    have hc : (1 - roundingTailMass y (roundingThreshold y)) / roundingThreshold y <
        rankBudget y (roundingThreshold y) - rankBudget y (roundingThreshold y + 1) := by
      rw [← roundingMass_div y (by omega), div_lt_div_iff_of_pos_right hm0]
      linarith
    rw [← sum_Ioc_consecutive _ (show (i : ℕ) ≤ roundingThreshold y by omega) hmK]
    have h1 : ∑ k ∈ Ioc (i : ℕ) (roundingThreshold y), optimalRoundingLaw y k / k =
        (1 - roundingTailMass y (roundingThreshold y)) / roundingThreshold y := by
      rw [hm', sum_Ioc_succ_top (by omega), ← hm', optimalRoundingLaw,
        ite_eq_right (lt_irrefl _), ite_eq_left rfl]
      rw [add_eq_right]
      refine sum_eq_zero fun k hk ↦ ?_
      rw [optimalRoundingLaw, ite_eq_right (by have := (mem_Ioc.1 hk).2; omega),
        ite_eq_right (by have := (mem_Ioc.1 hk).2; omega), zero_div]
    have h2 : ∑ k ∈ Ioc (roundingThreshold y) K, optimalRoundingLaw y k / k =
        rankBudget y (roundingThreshold y + 1) := by
      rw [sum_congr rfl fun k hk ↦ by
          rw [optimalRoundingLaw, ite_eq_left (mem_Ioc.1 hk).1],
        sum_Ioc_roundingMass_div y hmK]
    rw [h1, h2, ← rankBudget_succ y i]
    have := rankBudget_le_rankBudget hy hy0 (k := (i : ℕ) + 1) (l := roundingThreshold y)
      (Nat.succ_pos _) (by omega)
    linarith

/-- **The optimal scheme is feasible** [EVR26, Note 30, Theorem]: for antitone nonnegative
budgets, the nested point with law `P(N = k) = c_k` for `k > m` and `P(N = m) = 1 - C_m` is a
feasible point of the linear program. -/
theorem isRoundingFeasible_nestedPoint_optimalRoundingLaw (hy : Antitone y) (hy0 : ∀ i, 0 ≤ y i) :
    IsRoundingFeasible y (nestedPoint K (optimalRoundingLaw y)) :=
  isRoundingFeasible_nestedPoint (fun k _ ↦ optimalRoundingLaw_nonneg hy hy0 k)
    (sum_optimalRoundingLaw y).le (sum_Ioc_optimalRoundingLaw_div_le hy hy0)

/-- **The value of the optimal scheme** [EVR26, Note 30, Theorem]: for antitone nonnegative
budgets, the objective of the optimal nested point is `min_{0 ≤ j ≤ K} D(j)`. -/
theorem roundingObjective_nestedPoint_optimalRoundingLaw (hy : Antitone y) (hy0 : ∀ i, 0 ≤ y i) :
    roundingObjective (nestedPoint K (optimalRoundingLaw y)) = roundingValue y := by
  have hfeas := isRoundingFeasible_nestedPoint_optimalRoundingLaw hy hy0
  refine le_antisymm (le_roundingValue fun j _ ↦ roundingObjective_le_roundingDual hfeas j) ?_
  rw [roundingObjective_nestedPoint_optimalRoundingLaw_eq_roundingDual]
  exact roundingValue_le_roundingDual y (roundingThreshold_le y)

/-- **The value of the linear program** [EVR26, Note 30, Theorem]: for antitone nonnegative
budgets, the largest objective of a feasible point is `min_{0 ≤ j ≤ K} D(j)`. -/
theorem isGreatest_roundingObjective (hy : Antitone y) (hy0 : ∀ i, 0 ≤ y i) :
    IsGreatest (roundingObjective '' {p | IsRoundingFeasible y p}) (roundingValue y) := by
  refine ⟨⟨_, isRoundingFeasible_nestedPoint_optimalRoundingLaw hy hy0,
    roundingObjective_nestedPoint_optimalRoundingLaw hy hy0⟩, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact le_roundingValue fun j _ ↦ roundingObjective_le_roundingDual hp j

end Optimal

/-! ### Budgets in any order -/

/-- Relabelling the hypotheses by a permutation `σ` maps a feasible point for `y` to a feasible
point for `y ∘ σ`. -/
private lemma isRoundingFeasible_comp_map {y : Fin K → ℝ} {p : Finset (Fin K) → ℝ}
    (σ : Equiv.Perm (Fin K)) (hp : IsRoundingFeasible y p) :
    IsRoundingFeasible (y ∘ σ) (fun R ↦ p (R.map σ.toEmbedding)) where
  nonneg R := hp.nonneg _
  sum_le_one := by
    rw [show ∑ R : Finset (Fin K), p (R.map σ.toEmbedding) = ∑ R, p R from
      Equiv.sum_comp (Equiv.finsetCongr σ) p]
    exact hp.sum_le_one
  budget_le i := by
    calc ∑ R : Finset (Fin K) with i ∈ R, p (R.map σ.toEmbedding) / R.card
        = ∑ R, (fun R' ↦ if σ i ∈ R' then p R' / R'.card else 0) (Equiv.finsetCongr σ R) := by
          rw [sum_filter]
          refine sum_congr rfl fun R _ ↦ ?_
          simp [Equiv.finsetCongr_apply, card_map]
      _ = ∑ R, if σ i ∈ R then p R / R.card else 0 :=
          Equiv.sum_comp (Equiv.finsetCongr σ) (fun R' ↦ if σ i ∈ R' then p R' / R'.card else 0)
      _ ≤ (y ∘ σ) i := by
          rw [← sum_filter]
          exact hp.budget_le (σ i)

/-- Relabelling the hypotheses does not change the objective. -/
private lemma roundingObjective_comp_map (σ : Equiv.Perm (Fin K)) (p : Finset (Fin K) → ℝ) :
    roundingObjective (fun R ↦ p (R.map σ.toEmbedding)) = roundingObjective p := by
  unfold roundingObjective
  calc ∑ R : Finset (Fin K), (R.card : ℝ) * p (R.map σ.toEmbedding)
      = ∑ R, (fun R' : Finset (Fin K) ↦ (R'.card : ℝ) * p R') (Equiv.finsetCongr σ R) := by
        simp [Equiv.finsetCongr_apply, card_map]
    _ = ∑ R, (R.card : ℝ) * p R :=
        Equiv.sum_comp (Equiv.finsetCongr σ) (fun R' : Finset (Fin K) ↦ (R'.card : ℝ) * p R')

/-- **The value of the linear program, budgets in any order** [EVR26, Note 30, Theorem]: for
nonnegative budgets and a permutation `σ` that sorts them in nonincreasing order (one exists, for
instance `Tuple.sort y` composed with the reversal), the largest objective of a feasible point is
`min_{0 ≤ j ≤ K} D(j)`, computed with the sorted budgets `y ∘ σ`. -/
theorem isGreatest_roundingObjective_of_antitone_comp {y : Fin K → ℝ} (σ : Equiv.Perm (Fin K))
    (hy : Antitone (y ∘ σ)) (hy0 : ∀ i, 0 ≤ y i) :
    IsGreatest (roundingObjective '' {p | IsRoundingFeasible y p}) (roundingValue (y ∘ σ)) := by
  have himage : roundingObjective '' {p | IsRoundingFeasible y p} =
      roundingObjective '' {p | IsRoundingFeasible (y ∘ σ) p} := by
    ext v
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨_, isRoundingFeasible_comp_map σ hp, roundingObjective_comp_map σ p⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨_, ?_, roundingObjective_comp_map σ.symm p⟩
      have h := isRoundingFeasible_comp_map σ.symm hp
      rwa [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at h
  rw [himage]
  exact isGreatest_roundingObjective hy fun i ↦ hy0 (σ i)

/-- **The value when the budgets sum to at most one** [EVR26, Note 30, Theorem]: for antitone
nonnegative budgets with `∑_i y_i ≤ 1`, that is `∑_i x_i ≤ K / α`, the largest objective of a
feasible point is `∑_k (2k - 1) y_(k)`. -/
theorem isGreatest_roundingObjective_of_sum_le_one {y : Fin K → ℝ} (hy : Antitone y)
    (hy0 : ∀ i, 0 ≤ y i) (hsum : ∑ i, y i ≤ 1) :
    IsGreatest (roundingObjective '' {p | IsRoundingFeasible y p})
      (∑ i : Fin K, (2 * ((i : ℕ) + 1 : ℝ) - 1) * y i) := by
  -- `C_0 = ∑_i y_i ≤ 1`, so the threshold is `0`
  have hC0 : roundingTailMass y 0 = ∑ i, y i := by
    have h := sum_sub_mul_eq_sum_range y (fun r ↦ (r : ℝ)) (by simp)
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, one_mul] at h
    rw [h, roundingTailMass, sum_Ioc_eq_sum_range_ite]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [ite_eq_left (Nat.zero_le k), roundingMass]
    push_cast
    ring
  have hm : roundingThreshold y = 0 := Nat.sInf_eq_zero.2 (Or.inl (by simpa [hC0] using hsum))
  have hval : roundingValue y =
      ∑ i : Fin K, (2 * ((i : ℕ) + 1 : ℝ) - 1) * y i := by
    rw [← roundingObjective_nestedPoint_optimalRoundingLaw hy hy0,
      roundingObjective_nestedPoint_optimalRoundingLaw_eq_roundingDual, hm,
      ← sum_dualWeight_mul_add_eq_roundingDual, Nat.cast_zero, add_zero]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [dualWeight_eq, ite_eq_right (Nat.not_lt_zero _), Nat.cast_zero]
    ring
  rw [← hval]
  exact isGreatest_roundingObjective hy hy0

/-! ### U-eBH -/

section UeBH

variable {y : Fin K → ℝ}

/-- U-eBH rejects at most `K` hypotheses. -/
theorem uebhCount_le (y : Fin K → ℝ) (u : ℝ) : uebhCount y u ≤ K :=
  Finset.sup_le fun _ hk ↦ (mem_Icc.1 (mem_filter.1 hk).1).2

/-- When U-eBH rejects, its count `N` satisfies `u ≤ N y_(N)`. -/
private lemma uebhCount_mem {u : ℝ} (h : 0 < uebhCount y u) :
    uebhCount y u ∈ ({k ∈ Icc 1 K | u ≤ k * rankBudget y k} : Finset ℕ) := by
  have hne : ({k ∈ Icc 1 K | u ≤ k * rankBudget y k} : Finset ℕ).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro he
    rw [uebhCount, he, sup_empty] at h
    exact lt_irrefl _ h
  obtain ⟨l, hl, hsup⟩ := exists_mem_eq_sup _ hne id
  rw [uebhCount, hsup]
  exact hl

/-- U-eBH rejects at least `k ≥ 1` hypotheses iff some rank `l ≥ k` has `u ≤ l y_(l)`. -/
theorem le_uebhCount_iff {k : ℕ} (hk : 0 < k) {u : ℝ} :
    k ≤ uebhCount y u ↔ ∃ l, k ≤ l ∧ l ≤ K ∧ u ≤ l * rankBudget y l := by
  constructor
  · intro h
    have hl := mem_filter.1 (uebhCount_mem (y := y) (u := u) (by omega))
    exact ⟨uebhCount y u, h, (mem_Icc.1 hl.1).2, hl.2⟩
  · rintro ⟨l, hkl, hlK, hu⟩
    exact hkl.trans (le_sup (f := id) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, hlK⟩, hu⟩))

/-- The count of U-eBH is antitone in the uniform variable. -/
theorem antitone_uebhCount (y : Fin K → ℝ) : Antitone (uebhCount y) := fun _ _ huv ↦
  sup_mono fun _ hk ↦ by
    rw [mem_filter] at hk ⊢
    exact ⟨hk.1, huv.trans hk.2⟩

/-- The count of U-eBH is measurable in the uniform variable. -/
theorem measurable_uebhCount (y : Fin K → ℝ) : Measurable (uebhCount y) :=
  (antitone_uebhCount y).measurable

/-- The events of the law of U-eBH are measurable. -/
private lemma measurableSet_uebhCount_eq (y : Fin K → ℝ) (k : ℕ) :
    MeasurableSet {u ∈ Set.Icc (0 : ℝ) 1 | uebhCount y u = k} :=
  measurableSet_Icc.inter (measurable_uebhCount y (measurableSet_singleton k))

/-- The law of U-eBH summed over a set `S` of counts is the probability that the count is in
`S`. -/
private lemma sum_uebhLaw (y : Fin K → ℝ) (S : Finset ℕ) :
    ∑ k ∈ S, uebhLaw y k = volume.real {u ∈ Set.Icc (0 : ℝ) 1 | uebhCount y u ∈ S} := by
  have h : {u ∈ Set.Icc (0 : ℝ) 1 | uebhCount y u ∈ S} =
      ⋃ k ∈ S, {u ∈ Set.Icc (0 : ℝ) 1 | uebhCount y u = k} := by
    ext u
    simp
  rw [h, measureReal_biUnion_finset _ (fun k _ ↦ measurableSet_uebhCount_eq y k)
    (fun _ _ ↦ measure_ne_top_of_subset (fun _ hu ↦ hu.1) measure_Icc_lt_top.ne)]
  · rfl
  · intro k _ l _ hkl
    exact Set.disjoint_left.2 fun u hu hu' ↦ hkl (hu.2.symm.trans hu'.2)

/-- The expected count of U-eBH is the objective of the nested point with its law. -/
theorem integral_uebhCount_eq (y : Fin K → ℝ) :
    ∫ u in Set.Icc (0 : ℝ) 1, (uebhCount y u : ℝ) =
      roundingObjective (nestedPoint K (uebhLaw y)) := by
  rw [roundingObjective_nestedPoint]
  have hpt : ∀ u, (uebhCount y u : ℝ) = ∑ k ∈ range (K + 1),
      Set.indicator {u | uebhCount y u = k} (fun _ ↦ (k : ℝ)) u := by
    intro u
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [sum_ite_eq, ite_eq_left (mem_range.2 (Nat.lt_succ_of_le (uebhCount_le y u)))]
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine sum_congr rfl fun k _ ↦ ?_
    have hk : MeasurableSet {u : ℝ | uebhCount y u = k} :=
      measurable_uebhCount y (measurableSet_singleton k)
    rw [integral_indicator_const _ hk, smul_eq_mul, mul_comm, uebhLaw,
      measureReal_restrict_apply hk, Set.inter_comm]
    rfl
  · intro k _
    exact (integrable_const _).indicator (measurable_uebhCount y (measurableSet_singleton k))

/-- **U-eBH is feasible** [EVR26, Note 30, Theorem, Statement 3]: for antitone nonnegative
budgets, the nested point whose law is that of `N_U = max {k : k y_(k) ≥ U}`, for `U` uniform on
`[0, 1]`, is a feasible point of the linear program. -/
theorem isRoundingFeasible_nestedPoint_uebhLaw (hy : Antitone y)
    (hy0 : ∀ i, 0 ≤ y i) : IsRoundingFeasible y (nestedPoint K (uebhLaw y)) := by
  refine isRoundingFeasible_nestedPoint (fun k _ ↦ measureReal_nonneg) ?_ (fun i ↦ ?_)
  · rw [sum_uebhLaw]
    calc volume.real {u ∈ Set.Icc (0 : ℝ) 1 | uebhCount y u ∈ range (K + 1)}
        ≤ volume.real (Set.Icc (0 : ℝ) 1) :=
          measureReal_mono (fun u hu ↦ hu.1) measure_Icc_lt_top.ne
      _ = 1 := by simp [Real.volume_real_Icc]
  · -- a rank `k' ≥ i + 1` maximizing `k y_(k)` over the ranks `i + 1 ≤ k ≤ K`
    obtain ⟨k', hk'mem, hk'max⟩ := exists_max_image (Icc ((i : ℕ) + 1) K)
      (fun l ↦ (l : ℝ) * rankBudget y l) ⟨(i : ℕ) + 1, mem_Icc.2 ⟨le_rfl, i.isLt⟩⟩
    rw [mem_Icc] at hk'mem
    have hk'pos : (0 : ℝ) < k' := by exact_mod_cast (by omega : 0 < k')
    -- U-eBH rejects at least `k'` hypotheses as soon as it rejects at least `i + 1`, and then
    -- `u ≤ k' y_(k')`
    have hN : ∀ u, (i : ℕ) + 1 ≤ uebhCount y u →
        k' ≤ uebhCount y u ∧ u ≤ k' * rankBudget y k' := by
      intro u hu
      have hmem := (mem_filter.1 (uebhCount_mem (y := y) (u := u) (by omega))).2
      have hle := hmem.trans (hk'max _ (mem_Icc.2 ⟨hu, uebhCount_le y u⟩))
      exact ⟨(le_uebhCount_iff (by omega)).2 ⟨k', le_rfl, hk'mem.2, hle⟩, hle⟩
    have hterm : ∀ k ∈ Ioc (i : ℕ) K, uebhLaw y k / k ≤ uebhLaw y k / k' := by
      intro k hk
      rcases lt_or_ge k k' with hkk | hkk
      · have h0 : uebhLaw y k = 0 := by
          rw [uebhLaw, show {u ∈ Set.Icc (0 : ℝ) 1 | uebhCount y u = k} = ∅ from ?_,
            measureReal_empty]
          ext u
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
          intro _ hNu
          have := (hN u (by have := (mem_Ioc.1 hk).1; omega)).1
          omega
        rw [h0, zero_div, zero_div]
      · exact div_le_div_of_nonneg_left measureReal_nonneg hk'pos (by exact_mod_cast hkk)
    have hb0 : 0 ≤ (k' : ℝ) * rankBudget y k' :=
      mul_nonneg (Nat.cast_nonneg _) (rankBudget_nonneg hy0 _)
    calc ∑ k ∈ Ioc (i : ℕ) K, uebhLaw y k / k ≤ ∑ k ∈ Ioc (i : ℕ) K, uebhLaw y k / k' :=
          sum_le_sum hterm
      _ = (∑ k ∈ Ioc (i : ℕ) K, uebhLaw y k) / k' := by rw [sum_div]
      _ ≤ (k' * rankBudget y k') / k' := by
          gcongr
          rw [sum_uebhLaw]
          calc volume.real {u ∈ Set.Icc (0 : ℝ) 1 | uebhCount y u ∈ Ioc (i : ℕ) K}
              ≤ volume.real (Set.Icc 0 ((k' : ℝ) * rankBudget y k')) :=
                measureReal_mono (fun u hu ↦
                  ⟨hu.1.1, (hN u (by have := (mem_Ioc.1 hu.2).1; omega)).2⟩)
                  measure_Icc_lt_top.ne
            _ = k' * rankBudget y k' := by rw [Real.volume_real_Icc_of_le hb0, sub_zero]
      _ = rankBudget y k' := by field_simp
      _ ≤ rankBudget y ((i : ℕ) + 1) :=
          rankBudget_le_rankBudget hy hy0 (Nat.succ_pos _) hk'mem.1
      _ = y i := rankBudget_succ y i

/-- **U-eBH does no better than the optimum** [EVR26, Note 30, Theorem, Statement 3]: for
antitone nonnegative budgets, the expected number `E[N_U]` of rejections of U-eBH, for `U` uniform
on `[0, 1]`, is at most `min_{0 ≤ j ≤ K} D(j)`. -/
theorem integral_uebhCount_le_roundingValue (hy : Antitone y) (hy0 : ∀ i, 0 ≤ y i) :
    ∫ u in Set.Icc (0 : ℝ) 1, (uebhCount y u : ℝ) ≤ roundingValue y := by
  rw [integral_uebhCount_eq]
  exact le_roundingValue fun j _ ↦
    roundingObjective_le_roundingDual (isRoundingFeasible_nestedPoint_uebhLaw hy hy0) j

end UeBH

end ProbabilityTheory
