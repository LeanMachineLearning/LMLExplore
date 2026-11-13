/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Algebra.BigOperators.Intervals
public import LMLExplore.Bandits.LinearBandit.PhasedElimination.Basic
public import LMLExplore.Probability.Martingale.SubGaussian

/-!
# The regret of phased elimination

This file proves the regret bound of phased elimination with optimal designs [LS, Theorem 22.1]
for a stochastic linear bandit with finitely many arms `α`, features `φ : α → E` in a real inner
product space of dimension `d`, a parameter `θ`, σ²-sub-Gaussian noise and gaps between the
expected rewards of two arms at most `1`.

The analysis has a pathwise and a probabilistic part. Pathwise, if in every phase `ℓ` the
estimates `⟪φ b, θ̂_ℓ⟫` of the expected rewards of the survivors `b` are within the width
`ε_ℓ = 2⁻¹ ^ (ℓ + 1)`, an optimal arm is never eliminated, and every arm surviving phase `ℓ` has
gap at most `4 ε_ℓ`, so every round of phase `ℓ` has gap at most `8 ε_ℓ`. A phase has at most
`c_ℓ + s` rounds, where `c_ℓ = 2 σ² d log (k (ℓ + 1) (ℓ + 2) / δ) / ε_ℓ²` and `s` bounds the
number of support points of the designs, and summing `8 ε_ℓ` over the rounds of the phases gives
the random regret bound `32 √(σ² d n log (k n (n + 1) / δ)) + 8 s` after `n` rounds.

Probabilistically, along a run the actions of a phase are determined when it starts, so the error
`r ⟪φ b, θ̂_ℓ - θ⟫` (`r = ±1`) is a sum of the noises of the rounds of the phase with predictable
coefficients whose squares sum to `⟪φ b, V_ℓ⁺ φ b⟫ ≤ d / c_ℓ`. The exponential supermartingale of
sub-Gaussian sums then bounds the probability that `b` survives up to phase `ℓ` with an error at
least `ε_ℓ` by `δ / (k (ℓ + 1) (ℓ + 2))`, and a union bound over the arms and the phases `ℓ < n`
bounds the probability that some estimate is inaccurate by `2 δ`.

## Main statements

* `PhasedElimination.mem_survivors_of_forall_le`: an optimal arm is never eliminated.
* `PhasedElimination.inner_sub_inner_le_of_mem_survivors_succ`: the survivors of phase `ℓ + 1`
  have gaps at most `4 ε_ℓ`.
* `PhasedElimination.sum_width_mul_le`: summing the widths over the rounds of the phases.
* `PhasedElimination.sum_iSup_inner_sub_inner_nextArm_le`: the pathwise regret bound.
* `PhasedElimination.measure_mem_survivors_width_le_mul_inner_estimate_sub_le`,
  `PhasedElimination.measure_exists_width_le_abs_inner_estimate_sub_le`: the estimates are
  accurate with high probability.
* `PhasedElimination.le_measureReal_linearRegret_le`: with probability at least `1 - 2 δ`, the
  random regret after `n` rounds is at most `32 √(σ² d n log (k n (n + 1) / δ)) + 8 s`.
* `PhasedElimination.integral_linearRegret_le`,
  `PhasedElimination.integral_linearRegret_le_add_sqrt`: the expected regret is at most
  `2 n δ + 32 √(σ² d n log (k n (n + 1) / δ)) + 8 s`, and
  `2 + 32 √(σ² d n log (k n² (n + 1))) + 8 s` for `δ = 1 / n`.

## Implementation notes

The book applies the fixed-design confidence bound [LS, (20.2)] to each phase, whose design is
fixed given the previous phases. Here the conditioning is made explicit by the martingale
argument above, which only uses that the noise of each round is conditionally σ²-sub-Gaussian
given the past and the action. The union bound runs over the phases `ℓ < n`, which contain all
rounds before `n` since every phase has a round; this gives the logarithmic factor
`log (k n (n + 1) / δ)`, which is of order `log (k n)` for `δ = 1 / n`. A union bound over the
`O(log n)` phases that can start before round `n` would give a smaller factor of the same
order. With a design selection whose designs have at most `d (d + 1) / 2` support points
[LS, Theorem 21.1], `s` does not depend on the number of arms; every design selection satisfies
the bound with `s = k`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 22, Theorem 22.1.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Module Learning Convexity
open scoped ENNReal NNReal InnerProductSpace

namespace LMLExplore.Bandits.PhasedElimination

variable {α E : Type*} [Fintype α] [Nonempty α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {φ : α → E} {D : DesignSelection φ} {σ2 : ℝ≥0} {δ : ℝ} {θ : E}
  {y : ℕ → ℝ}

/-! ### The elimination argument -/

omit [Fintype α] [Nonempty α] [FiniteDimensional ℝ E] in
/-- The error of the estimate of phase `ℓ` in the direction of the difference of two arms:
`⟪θ̂, φ b - φ a⟫ = ⟪φ b, θ̂ - θ⟫ - ⟪φ a, θ̂ - θ⟫ + (⟪θ, φ b⟫ - ⟪θ, φ a⟫)`. -/
private lemma inner_sub_eq (θ' : E) (a b : α) :
    ⟪θ', φ b - φ a⟫_ℝ = ⟪φ b, θ' - θ⟫_ℝ - ⟪φ a, θ' - θ⟫_ℝ + (⟪θ, φ b⟫_ℝ - ⟪θ, φ a⟫_ℝ) := by
  simp only [inner_sub_right, real_inner_comm θ', real_inner_comm θ]
  ring

/-- **An optimal arm is never eliminated**: an arm `a'` maximizing the expected reward survives
phase `ℓ` if, in every earlier phase, the estimates of the expected rewards of the survivors are
within the width of the phase. -/
theorem mem_survivors_of_forall_le {a' : α} (hopt : ∀ a, ⟪θ, φ a⟫_ℝ ≤ ⟪θ, φ a'⟫_ℝ) {ℓ : ℕ}
    (hgood : ∀ ℓ' < ℓ, ∀ b ∈ survivors D σ2 δ y ℓ',
      |⟪φ b, estimate D σ2 δ y ℓ' - θ⟫_ℝ| < width ℓ') :
    a' ∈ survivors D σ2 δ y ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    have hmem := ih fun ℓ' hℓ' ↦ hgood ℓ' (Nat.lt_succ_of_lt hℓ')
    rw [survivors_succ, mem_eliminate]
    refine ⟨hmem, fun b hb ↦ ?_⟩
    have h1 := abs_lt.1 (hgood ℓ (Nat.lt_succ_self ℓ) b hb)
    have h2 := abs_lt.1 (hgood ℓ (Nat.lt_succ_self ℓ) _ hmem)
    rw [inner_sub_eq (θ := θ)]
    linarith [hopt b]

/-- **The survivors have small gaps**: if the estimates of the expected rewards of the survivors of
phase `ℓ` are within its width, the expected reward of every arm `a` surviving phase `ℓ` is at
least that of every survivor `a'` of phase `ℓ` minus `4 ε_ℓ`. -/
theorem inner_sub_inner_le_of_mem_survivors_succ {a' a : α} {ℓ : ℕ}
    (ha' : a' ∈ survivors D σ2 δ y ℓ) (ha : a ∈ survivors D σ2 δ y (ℓ + 1))
    (hgood : ∀ b ∈ survivors D σ2 δ y ℓ, |⟪φ b, estimate D σ2 δ y ℓ - θ⟫_ℝ| < width ℓ) :
    ⟪θ, φ a'⟫_ℝ - ⟪θ, φ a⟫_ℝ ≤ 4 * width ℓ := by
  rw [survivors_succ, mem_eliminate] at ha
  have h := ha.2 a' ha'
  have h1 := abs_lt.1 (hgood a' ha')
  have h2 := abs_lt.1 (hgood a ha.1)
  rw [inner_sub_eq (θ := θ)] at h
  linarith

/-- **The gap of the arm of round `t`** is at most `8 ε_ℓ`, where `ℓ` is the phase of round `t`,
if the gaps of the arms are at most `1` and the estimates of the survivors of the phases up to `ℓ`
are within their widths. -/
theorem iSup_inner_sub_inner_nextArm_le (hgap : ∀ a b, ⟪θ, φ a⟫_ℝ - ⟪θ, φ b⟫_ℝ ≤ 1) {t : ℕ}
    (hgood : ∀ ℓ ≤ phaseIndex D σ2 δ y t, ∀ b ∈ survivors D σ2 δ y ℓ,
      |⟪φ b, estimate D σ2 δ y ℓ - θ⟫_ℝ| < width ℓ) :
    (⨆ a, ⟪θ, φ a⟫_ℝ) - ⟪θ, φ (nextArm D σ2 δ y t)⟫_ℝ ≤ 8 * width (phaseIndex D σ2 δ y t) := by
  obtain ⟨a', ha'⟩ := Finite.exists_max fun a ↦ ⟪θ, φ a⟫_ℝ
  have hsup : (⨆ a, ⟪θ, φ a⟫_ℝ) ≤ ⟪θ, φ a'⟫_ℝ := ciSup_le ha'
  have hmem := nextArm_mem_survivors (D := D) (σ2 := σ2) (δ := δ) y t
  rcases h : phaseIndex D σ2 δ y t with _ | ℓ
  · rw [width_def]
    norm_num
    linarith [hgap a' (nextArm D σ2 δ y t)]
  · rw [h] at hmem hgood
    have hopt := mem_survivors_of_forall_le (D := D) (σ2 := σ2) (δ := δ) (y := y) ha'
      (ℓ := ℓ) fun ℓ' hℓ' ↦ hgood ℓ' (by lia)
    have := inner_sub_inner_le_of_mem_survivors_succ hopt hmem (hgood ℓ (by lia))
    rw [width_succ]
    linarith

/-! ### Counting the rounds of the phases -/

/-- The rounds `t < n` of phase `ℓ` are at most its length. -/
lemma card_filter_phaseIndex_eq_le (y : ℕ → ℝ) (n ℓ : ℕ) :
    #{t ∈ range n | phaseIndex D σ2 δ y t = ℓ} ≤ phaseLength D σ2 δ ℓ (survivors D σ2 δ y ℓ) := by
  calc #{t ∈ range n | phaseIndex D σ2 δ y t = ℓ}
      ≤ #(Ico (phaseStart D σ2 δ y ℓ) (phaseStart D σ2 δ y (ℓ + 1))) := by
        refine card_le_card fun t ht ↦ ?_
        obtain ⟨-, rfl⟩ := mem_filter.1 ht
        exact mem_Ico.2 ⟨phaseStart_phaseIndex_le y t, lt_phaseStart_phaseIndex_succ y t⟩
    _ = phaseLength D σ2 δ ℓ (survivors D σ2 δ y ℓ) := by
        rw [Nat.card_Ico, phaseStart_succ, Nat.add_sub_cancel_left]

omit [FiniteDimensional ℝ E] in
/-- For `0 < δ ≤ 1`, the sample scales are nonnegative. -/
lemma scale_nonneg (hδ : 0 < δ) (hδ1 : δ ≤ 1) (d : ℕ) (ℓ : ℕ) :
    0 ≤ scale d (Fintype.card α) σ2 δ ℓ := by
  rw [scale_def]
  have hk : (1 : ℝ) ≤ Fintype.card α := Nat.one_le_cast.2 Fintype.card_pos
  have hℓ : (1 : ℝ) ≤ (ℓ + 1) * (ℓ + 2) := by nlinarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
  have hlog : 0 ≤ log (Fintype.card α * ((ℓ + 1) * (ℓ + 2)) / δ) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hδ, one_mul]
    exact hδ1.trans (one_le_mul_of_one_le_of_one_le hk hℓ)
  positivity

omit [FiniteDimensional ℝ E] in
/-- For `0 < δ` and `ℓ < n`, the sample scale of phase `ℓ` is at most
`2 σ² d log (k n (n + 1) / δ) / ε_ℓ²`. -/
lemma scale_le (hδ : 0 < δ) (d : ℕ) {ℓ n : ℕ} (hℓ : ℓ < n) :
    scale d (Fintype.card α) σ2 δ ℓ ≤
      2 * σ2 * d * log (Fintype.card α * (n * (n + 1)) / δ) / width ℓ ^ 2 := by
  rw [scale_def]
  have hk : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
  have hℓ' : (ℓ : ℝ) + 1 ≤ n := by exact_mod_cast hℓ
  have hmul : ((ℓ : ℝ) + 1) * (ℓ + 2) ≤ n * (n + 1) := by
    nlinarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.log_le_log (by positivity) ?_) (by positivity)) (by positivity)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmul hk.le) hδ.le

/-- For `0 < δ ≤ 1`, the length of a phase with nonempty survivors `S` is at most `c_ℓ + s` when
the design of `S` has at most `s` support points. -/
lemma phaseLength_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ℓ : ℕ) {S : Finset α} (hS : S.Nonempty)
    {s : ℕ} (hs : #(D.design S hS).weights.support ≤ s) :
    (phaseLength D σ2 δ ℓ S : ℝ) ≤ scale (finrank ℝ E) (Fintype.card α) σ2 δ ℓ + s := by
  rw [phaseLength_eq_sum, phaseAllocation_def, phaseDesign_of_nonempty hS, Nat.cast_sum]
  exact (sum_allocation_le (scale_nonneg hδ hδ1 _ ℓ)).trans (by gcongr)

/-- The widths sum to at most `1`. -/
lemma sum_range_width_le_one (N : ℕ) : ∑ ℓ ∈ range N, width ℓ ≤ 1 := by
  have h : ∑ ℓ ∈ range N, width ℓ = 2⁻¹ * ∑ ℓ ∈ range N, (1 / 2 : ℝ) ^ ℓ := by
    rw [mul_sum]
    exact sum_congr rfl fun ℓ _ ↦ by rw [width_def, pow_succ', one_div]
  rw [h]
  linarith [sum_geometric_two_le N]

/-- The inverse widths `ε_ℓ⁻¹` smaller than `1 / x` (i.e. `x < ε_ℓ`) sum to at most `2 / x`. -/
lemma sum_range_ite_lt_width_inv_le {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ∑ ℓ ∈ range N, (if x < width ℓ then (width ℓ)⁻¹ else 0) ≤ 2 / x := by
  have hinv (ℓ : ℕ) : (width ℓ)⁻¹ = 2 ^ (ℓ + 1) := by rw [width_def, inv_pow, inv_inv]
  -- the sum is also at most `2 ^ (N + 1) - 2`
  suffices h : ∑ ℓ ∈ range N, (if x < width ℓ then (width ℓ)⁻¹ else 0) ≤ 2 / x ∧
      ∑ ℓ ∈ range N, (if x < width ℓ then (width ℓ)⁻¹ else 0) + 2 ≤ 2 ^ (N + 1) from h.1
  induction N with
  | zero =>
    simp only [range_zero, sum_empty]
    exact ⟨by positivity, by norm_num⟩
  | succ N ih =>
    rw [sum_range_succ]
    split_ifs with hN
    · have h2 : 2 / width N < 2 / x := div_lt_div_of_pos_left two_pos hx hN
      have h3 : 2 / width N = 2 * 2 ^ (N + 1) := by rw [div_eq_mul_inv, hinv]
      have hp : (2 : ℝ) ^ (N + 1 + 1) = 2 * 2 ^ (N + 1) := by ring
      rw [hinv, hp]
      have := ih.2
      constructor <;> linarith
    · refine ⟨by simpa using ih.1, ?_⟩
      have := ih.2
      rw [add_zero, pow_succ 2 (N + 1)]
      nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) (N + 1)]

/-- **Summing over the phases**: if `R ℓ ≥ 0` rounds of phase `ℓ` are played, with
`R ℓ ≤ a / ε_ℓ² + s` and `∑_{ℓ < N} R ℓ ≤ n`, then `∑_{ℓ < N} ε_ℓ R ℓ ≤ 2 √(2 a n) + s`. -/
theorem sum_width_mul_le {N : ℕ} {R : ℕ → ℝ} {a s n : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hR0 : ∀ ℓ, 0 ≤ R ℓ) (hR : ∀ ℓ < N, R ℓ ≤ a / width ℓ ^ 2 + s)
    (hn : ∑ ℓ ∈ range N, R ℓ ≤ n) :
    ∑ ℓ ∈ range N, width ℓ * R ℓ ≤ 2 * √(2 * a * n) + s := by
  have hw1 := sum_range_width_le_one N
  -- the phases with `ε_ℓ ≤ √(2 a / n)` contribute at most `√(2 a / n) n = √(2 a n)`, and the
  -- others, whose inverse widths are geometric, at most `2 a / √(2 a / n) + s = √(2 a n) + s`
  rcases ha.eq_or_lt with rfl | ha
  · -- without the scale term, each phase contributes at most `ε_ℓ s`
    calc ∑ ℓ ∈ range N, width ℓ * R ℓ ≤ ∑ ℓ ∈ range N, width ℓ * s :=
          sum_le_sum fun ℓ hℓ ↦ mul_le_mul_of_nonneg_left
            (by simpa using hR ℓ (mem_range.1 hℓ)) (width_pos ℓ).le
      _ = (∑ ℓ ∈ range N, width ℓ) * s := (sum_mul ..).symm
      _ ≤ 1 * s := by gcongr
      _ ≤ 2 * √(2 * 0 * n) + s := by simp
  rcases le_or_gt n 0 with hn0 | hn0
  · -- no round is played
    have hR' : ∀ ℓ ∈ range N, R ℓ = 0 :=
      (sum_eq_zero_iff_of_nonneg fun ℓ _ ↦ hR0 ℓ).1
        (le_antisymm (hn.trans hn0) (sum_nonneg fun ℓ _ ↦ hR0 ℓ))
    rw [sum_eq_zero fun ℓ hℓ ↦ by rw [hR' ℓ hℓ, mul_zero]]
    positivity
  -- the threshold `x = √(2 a n) / n`
  set q := √(2 * a * n)
  have hq : 0 < q := Real.sqrt_pos.2 (by positivity)
  have hq2 : q ^ 2 = 2 * a * n := Real.sq_sqrt (by positivity)
  set x := q / n
  have hx : 0 < x := div_pos hq hn0
  have hterm : ∀ ℓ ∈ range N, width ℓ * R ℓ ≤
      x * R ℓ + a * (if x < width ℓ then (width ℓ)⁻¹ else 0) + s * width ℓ := by
    intro ℓ hℓ
    have hw := width_pos ℓ
    split_ifs with hxw
    · have h := mul_le_mul_of_nonneg_left (hR ℓ (mem_range.1 hℓ)) hw.le
      have heq : width ℓ * (a / width ℓ ^ 2 + s) = a * (width ℓ)⁻¹ + s * width ℓ := by
        field_simp
      nlinarith [hR0 ℓ, hx.le]
    · have := mul_le_mul_of_nonneg_right (not_lt.1 hxw) (hR0 ℓ)
      nlinarith [hw]
  calc ∑ ℓ ∈ range N, width ℓ * R ℓ
      ≤ ∑ ℓ ∈ range N, (x * R ℓ + a * (if x < width ℓ then (width ℓ)⁻¹ else 0) +
          s * width ℓ) := sum_le_sum hterm
    _ = x * ∑ ℓ ∈ range N, R ℓ +
          a * ∑ ℓ ∈ range N, (if x < width ℓ then (width ℓ)⁻¹ else 0) +
          s * ∑ ℓ ∈ range N, width ℓ := by
        rw [sum_add_distrib, sum_add_distrib, mul_sum, mul_sum, mul_sum]
    _ ≤ x * n + a * (2 / x) + s * 1 := by
        gcongr
        exact sum_range_ite_lt_width_inv_le hx N
    _ = 2 * q + s := by
        have hxn : x * n = q := div_mul_cancel₀ q hn0.ne'
        have hax : a * (2 / x) = q := by
          simp only [x]
          field_simp
          nlinarith [hq2]
        rw [hxn, hax]
        ring

/-- **The pathwise regret of phased elimination.** For rewards `y`, let the gaps of the arms be at
most `1`, `0 < δ ≤ 1`, and the designs of `D` have at most `s` support points. If the estimates of
the expected rewards of the survivors of the phases `ℓ < n` are within the widths `ε_ℓ`, then the
arms played in the first `n` rounds have total gap at most
`32 √(σ² d n log (k n (n + 1) / δ)) + 8 s`. -/
theorem sum_iSup_inner_sub_inner_nextArm_le (hgap : ∀ a b, ⟪θ, φ a⟫_ℝ - ⟪θ, φ b⟫_ℝ ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {s : ℕ} (hs : ∀ S hS, #(D.design S hS).weights.support ≤ s) {n : ℕ}
    (hgood : ∀ ℓ < n, ∀ b ∈ survivors D σ2 δ y ℓ,
      |⟪φ b, estimate D σ2 δ y ℓ - θ⟫_ℝ| < width ℓ) :
    ∑ t ∈ range n, ((⨆ a, ⟪θ, φ a⟫_ℝ) - ⟪θ, φ (nextArm D σ2 δ y t)⟫_ℝ) ≤
      32 * √(σ2 * finrank ℝ E * n * log (Fintype.card α * (n * (n + 1)) / δ)) + 8 * s := by
  set Λ := log (Fintype.card α * (n * (n + 1)) / δ)
  set a : ℝ := 2 * σ2 * finrank ℝ E * Λ
  set R : ℕ → ℝ := fun ℓ ↦ #{t ∈ range n | phaseIndex D σ2 δ y t = ℓ}
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [range_zero, sum_empty]
    positivity
  have hΛ : 0 ≤ Λ := by
    have hk : (1 : ℝ) ≤ Fintype.card α := Nat.one_le_cast.2 Fintype.card_pos
    have hn' : (1 : ℝ) ≤ n * (n + 1) := by
      have : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
      nlinarith
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hδ, one_mul]
    exact hδ1.trans (one_le_mul_of_one_le_of_one_le hk hn')
  -- group the rounds by phase: each round of phase `ℓ` has gap at most `8 ε_ℓ`
  have hsplit : ∑ t ∈ range n, ((⨆ a, ⟪θ, φ a⟫_ℝ) - ⟪θ, φ (nextArm D σ2 δ y t)⟫_ℝ) ≤
      8 * ∑ ℓ ∈ range n, width ℓ * R ℓ := by
    rw [← sum_fiberwise_of_maps_to (g := phaseIndex D σ2 δ y)
      fun t ht ↦ mem_range.2 ((phaseIndex_le y t).trans_lt (mem_range.1 ht)), mul_sum]
    refine sum_le_sum fun ℓ _ ↦ ?_
    calc ∑ t ∈ range n with phaseIndex D σ2 δ y t = ℓ,
          ((⨆ a, ⟪θ, φ a⟫_ℝ) - ⟪θ, φ (nextArm D σ2 δ y t)⟫_ℝ)
        ≤ ∑ t ∈ range n with phaseIndex D σ2 δ y t = ℓ, 8 * width ℓ := by
          refine sum_le_sum fun t ht ↦ ?_
          obtain ⟨ht', hℓ⟩ := mem_filter.1 ht
          subst hℓ
          exact iSup_inner_sub_inner_nextArm_le hgap fun ℓ' hℓ' ↦
            hgood ℓ' (hℓ'.trans_lt ((phaseIndex_le y t).trans_lt (mem_range.1 ht')))
      _ = 8 * (width ℓ * R ℓ) := by
          rw [sum_const, nsmul_eq_mul]
          ring
  -- the rounds of phase `ℓ` are at most `c_ℓ + s ≤ a / ε_ℓ² + s`, and there are `n` rounds
  have hR : ∀ ℓ < n, R ℓ ≤ a / width ℓ ^ 2 + s := fun ℓ hℓ ↦
    (Nat.cast_le.2 (card_filter_phaseIndex_eq_le y n ℓ)).trans <|
      (phaseLength_le hδ hδ1 ℓ (survivors_nonempty y ℓ) (hs _ _)).trans
        (by gcongr; exact scale_le hδ _ hℓ)
  have hRn : ∑ ℓ ∈ range n, R ℓ ≤ n := by
    simp only [R]
    rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise
      fun t ht ↦ mem_range.2 ((phaseIndex_le y t).trans_lt (mem_range.1 ht)), card_range]
  have hsum := sum_width_mul_le (by positivity) (Nat.cast_nonneg s)
    (fun ℓ ↦ Nat.cast_nonneg _) hR hRn
  have hsqrt : √(2 * a * n) = 2 * √(σ2 * finrank ℝ E * n * Λ) := by
    rw [show 2 * a * n = 2 ^ 2 * (σ2 * finrank ℝ E * n * Λ) by simp only [a]; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  calc _ ≤ 8 * ∑ ℓ ∈ range n, width ℓ * R ℓ := hsplit
    _ ≤ 8 * (2 * √(2 * a * n) + s) := by gcongr
    _ = _ := by
        rw [hsqrt]
        ring

/-! ### Concentration of the estimates along a run -/

section Run

variable [MeasurableSpace α] [MeasurableSingletonClass α] {𝓞 Ω : Type*} [MeasurableSpace 𝓞]
  {mΩ : MeasurableSpace Ω} {env : Environment 𝓞 α ℝ} {P : Measure Ω}
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}

open scoped Classical in
variable (D σ2 δ) in
/-- The coefficient of the noise of round `t` in `r` times the error of the estimate of phase `ℓ`
in the direction `φ b`, for the state `p = (S_ℓ, t_ℓ)` of phase `ℓ`: `r ⟪V_ℓ⁺ φ b, φ (A t)⟫` if
`b` survives and `t` is a round of the phase, and `0` otherwise. -/
private noncomputable def coefficient (r : ℝ) (ℓ : ℕ) (b : α) (p : Finset α × ℕ) (t : ℕ) : ℝ :=
  if b ∈ p.1 ∧ p.2 ≤ t ∧ t < p.2 + phaseLength D σ2 δ ℓ p.1 then
    r * ⟪(designOp 0 (fun j ↦ φ (phaseArm D σ2 δ ℓ p.1 j)) (phaseLength D σ2 δ ℓ p.1) :
      E →ₗ[ℝ] E).moorePenroseInverse (φ b), φ (phaseArm D σ2 δ ℓ p.1 (t - p.2))⟫_ℝ
  else 0

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The coefficient of round `t` only depends on the rewards before `t`. -/
private lemma coefficient_phase_congr {y y' : ℕ → ℝ} {t : ℕ} (hyy' : ∀ s < t, y s = y' s)
    (r : ℝ) (ℓ : ℕ) (b : α) :
    coefficient D σ2 δ r ℓ b (phase D σ2 δ y ℓ) t =
      coefficient D σ2 δ r ℓ b (phase D σ2 δ y' ℓ) t := by
  by_cases ht : phaseStart D σ2 δ y ℓ ≤ t
  · rw [phase_congr hyy' ht]
  · have ht' : ¬ phaseStart D σ2 δ y' ℓ ≤ t := by rwa [← phaseStart_le_iff_of_eq hyy']
    simp only [phase_eq, coefficient, ht, ht', false_and, and_false, ite_false]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
open scoped Classical in
/-- For rewards `y`, arms `a n = nextArm D σ2 δ y n` and a survivor `b` of phase `ℓ`, the
coefficients of the rounds before the end of the phase weigh the noises `y k - ⟪θ, φ (a k)⟫`
into `r ⟪φ b, θ̂_ℓ - θ⟫`, and, for `r ^ 2 = 1` and a positive sample scale `c_ℓ`, their squares
sum to `⟪φ b, V_ℓ⁺ φ b⟫ ≤ d / c_ℓ`. -/
private lemma sum_coefficient_eq {y : ℕ → ℝ} {a : ℕ → α} (ha : ∀ n, a n = nextArm D σ2 δ y n)
    {r : ℝ} (hr : r ^ 2 = 1) {ℓ : ℕ} (hc : 0 < scale (finrank ℝ E) (Fintype.card α) σ2 δ ℓ)
    {b : α} (hb : b ∈ survivors D σ2 δ y ℓ) :
    ∑ k ∈ range (phaseStart D σ2 δ y ℓ + phaseLength D σ2 δ ℓ (survivors D σ2 δ y ℓ)),
        coefficient D σ2 δ r ℓ b (phase D σ2 δ y ℓ) k * (y k - ⟪θ, φ (a k)⟫_ℝ) =
      r * ⟪φ b, estimate D σ2 δ y ℓ - θ⟫_ℝ ∧
    ∑ k ∈ range (phaseStart D σ2 δ y ℓ + phaseLength D σ2 δ ℓ (survivors D σ2 δ y ℓ)),
        coefficient D σ2 δ r ℓ b (phase D σ2 δ y ℓ) k ^ 2 ≤
      finrank ℝ E / scale (finrank ℝ E) (Fintype.card α) σ2 δ ℓ := by
  have hQ := inner_moorePenroseInverse_designOp_phaseArm_le (D := D)
    (survivors_nonempty y ℓ) hc hb
  set S := survivors D σ2 δ y ℓ
  set t₀ := phaseStart D σ2 δ y ℓ
  set L := phaseLength D σ2 δ ℓ S
  set x : ℕ → E := fun j ↦ φ (phaseArm D σ2 δ ℓ S j)
  set V : E →ₗ[ℝ] E := (designOp 0 x L : E →ₗ[ℝ] E)
  have hw (k : ℕ) : coefficient D σ2 δ r ℓ b (phase D σ2 δ y ℓ) k =
      if t₀ ≤ k ∧ k < t₀ + L then r * ⟪V.moorePenroseInverse (φ b), x (k - t₀)⟫_ℝ else 0 := by
    have hp : phase D σ2 δ y ℓ = (S, t₀) := phase_eq y ℓ
    simp only [coefficient, hp, hb, true_and]
    exact if_congr Iff.rfl rfl rfl
  -- the rounds of the phase play the arms of its schedule, so the error of the estimate is the
  -- sum of their noises with the coefficients `⟪V⁺ φ b, x j⟫`
  have hAj (j : ℕ) (hj : j < L) : a (t₀ + j) = phaseArm D σ2 δ ℓ S j := by
    rw [ha]
    exact nextArm_phaseStart_add hj
  have herr : ⟪φ b, estimate D σ2 δ y ℓ - θ⟫_ℝ =
      ∑ j ∈ range L,
        ⟪V.moorePenroseInverse (φ b), x j⟫_ℝ * (y (t₀ + j) - ⟪θ, φ (a (t₀ + j))⟫_ℝ) := by
    rw [estimate_def, phaseEstimate_def, inner_leastSquaresEstimate_sub_eq_sum (η := fun j ↦
      y (t₀ + j) - ⟪θ, x j⟫_ℝ) θ (fun j ↦ by ring) (mem_span_phaseArm
        (survivors_nonempty y ℓ) hb)]
    refine sum_congr rfl fun j hj ↦ ?_
    rw [hAj j (mem_range.1 hj)]
  constructor
  · simp_rw [hw, ite_mul, zero_mul]
    rw [sum_range_add_ite, herr, mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [Nat.add_sub_cancel_left]
    ring
  · simp_rw [hw, ite_pow, zero_pow two_ne_zero]
    rw [sum_range_add_ite, ← sum_inner_moorePenroseInverse_designOp_sq x L (φ b)] at *
    refine le_of_eq_of_le (sum_congr rfl fun j _ ↦ ?_) hQ
    rw [Nat.add_sub_cancel_left, mul_pow, hr, one_mul]

/-- **Concentration of the estimate of a phase in one direction.** Along a run of phased
elimination in a linear bandit environment with σ²-sub-Gaussian noise, `σ² ≠ 0` and `δ > 0`, for
every phase `ℓ`, arm `b` and sign `r = ±1`, the probability that `b` survives up to phase `ℓ` and
`ε_ℓ ≤ r ⟪φ b, θ̂_ℓ - θ⟫` is at most `δ / (k (ℓ + 1) (ℓ + 2))`. -/
theorem measure_mem_survivors_width_le_mul_inner_estimate_sub_le [StandardBorelSpace Ω]
    [IsProbabilityMeasure P] (h : IsAlgEnvSeq O A Y (phasedElimination D σ2 δ) env P)
    (henv : IsSubgaussianLinearEnv (fun _ : 𝓞 ↦ φ) θ σ2 env) (hσ : σ2 ≠ 0) (hδ : 0 < δ)
    (ℓ : ℕ) (b : α) {r : ℝ} (hr : r ^ 2 = 1) :
    P {ω | b ∈ survivors D σ2 δ (fun s ↦ Y s ω) ℓ ∧
      width ℓ ≤ r * ⟪φ b, estimate D σ2 δ (fun s ↦ Y s ω) ℓ - θ⟫_ℝ} ≤
      ENNReal.ofReal (δ / (Fintype.card α * ((ℓ + 1) * (ℓ + 2)))) := by
  -- the error is a sum of the noises of the rounds of the phase with predictable coefficients
  -- whose squares sum to `⟪φ b, V_ℓ⁺ φ b⟫ ≤ d / c_ℓ`, so the exponential supermartingale of
  -- sub-Gaussian sums bounds it
  set X : ℝ := Fintype.card α * ((ℓ + 1) * (ℓ + 2))
  set Λ := log (X / δ)
  set ε := width ℓ
  have hX : 0 < X := by positivity
  have hε := width_pos ℓ
  -- if `E = 0`, the event is empty
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with hd | hd
  · have : Subsingleton E := finrank_zero_iff.1 hd
    have hempty : {ω | b ∈ survivors D σ2 δ (fun s ↦ Y s ω) ℓ ∧
        ε ≤ r * ⟪φ b, estimate D σ2 δ (fun s ↦ Y s ω) ℓ - θ⟫_ℝ} = ∅ := by
      ext ω
      simp only [Subsingleton.elim (φ b) 0, inner_zero_left, mul_zero, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false, not_and, not_le]
      exact fun _ ↦ hε
    rw [hempty, measure_empty]
    exact bot_le
  -- if `δ ≥ X`, the bound is at least `1`
  rcases le_or_gt Λ 0 with hΛ | hΛ
  · have h1 : 1 ≤ δ / X := by
      rw [Real.log_nonpos_iff (div_pos hX hδ).le, div_le_one hδ] at hΛ
      rwa [le_div_iff₀ hX, one_mul]
    exact prob_le_one.trans (ENNReal.one_le_ofReal.2 h1)
  -- the sample scale `c = 2 σ² d Λ / ε²` is positive
  set c := scale (finrank ℝ E) (Fintype.card α) σ2 δ ℓ
  have hσpos : (0 : ℝ) < σ2 := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hσ)
  have hc : 0 < c := by
    simp only [c, scale_def]
    have : (0 : ℝ) < finrank ℝ E := Nat.cast_pos.2 hd
    positivity
  -- the noises and the coefficients
  set ℱ := h.filtrationAction
  set ζ : ℕ → Ω → ℝ := fun t ω ↦ Y t ω - ⟪θ, φ (A t ω)⟫_ℝ
  set w : ℕ → Ω → ℝ := fun t ω ↦
    coefficient D σ2 δ r ℓ b (phase D σ2 δ (fun s ↦ Y s ω) ℓ) t
  have hθφ : Measurable fun a : α ↦ ⟪θ, φ a⟫_ℝ := measurable_of_countable _
  have hζ (t : ℕ) : Measurable[ℱ (t + 1)] (ζ t) :=
    (h.measurable_feedback_filtrationAction_of_lt t.lt_succ_self).sub
      (hθφ.comp ((h.adapted_action_filtrationAction t).mono (ℱ.mono t.le_succ) le_rfl))
  have hsub (t : ℕ) : HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (ζ t) σ2 P :=
    h.hasCondSubgaussianMGF_feedback_sub_inner henv (hθφ.comp measurable_snd) t
  have hw : Adapted ℱ w := fun t ↦ by
    have heq : w t = (fun p ↦ coefficient D σ2 δ r ℓ b p t) ∘ (fun y ↦ phase D σ2 δ y ℓ) ∘
        histReward ∘ history O A Y t := funext fun ω ↦
      coefficient_phase_congr (fun s hs ↦ (histReward_history hs ω).symm) r ℓ b
    rw [heq]
    exact (measurable_of_countable _).comp ((measurable_phase ℓ).comp
      ((measurable_histReward t).comp (h.measurable_history_filtrationAction t)))
  have hbound := measure_exists_le_mul_sum_sub_of_hasCondSubgaussianMGF hζ hsub hw
    (2 * Λ / ε) Λ
  have hexp : exp (-Λ) = δ / X := by
    rw [Real.exp_neg, Real.exp_log (div_pos hX hδ), inv_div]
  rw [hexp] at hbound
  refine (measure_mono_ae ?_).trans hbound
  -- on the event, the sum with the horizon `t_{ℓ+1}` exceeds `Λ`
  filter_upwards [action_ae_all_eq h] with ω hA hω
  obtain ⟨hb, hle⟩ := hω
  obtain ⟨hsum1, hsum2⟩ := sum_coefficient_eq (θ := θ) (a := fun k ↦ A k ω) hA hr hc hb
  refine ⟨phaseStart D σ2 δ (fun s ↦ Y s ω) ℓ +
    phaseLength D σ2 δ ℓ (survivors D σ2 δ (fun s ↦ Y s ω) ℓ), ?_⟩
  simp only [w, ζ]
  rw [hsum1]
  -- `λ r ⟪φ b, θ̂ - θ⟫ ≥ λ ε = 2 Λ` and `σ² λ² ∑ w² / 2 ≤ σ² λ² d / (2 c) = Λ`
  have hc' : c = 2 * σ2 * finrank ℝ E * Λ / ε ^ 2 := scale_def _ _ _ _ _
  have hε' : ε ≠ 0 := hε.ne'
  have hkey : (σ2 : ℝ) * (2 * Λ / ε) ^ 2 * (finrank ℝ E / c) / 2 = Λ := by
    rw [hc']
    field_simp
  have h1 : 2 * Λ ≤ 2 * Λ / ε * (r * ⟪φ b, estimate D σ2 δ (fun s ↦ Y s ω) ℓ - θ⟫_ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    nlinarith
  have h2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum2
    (by positivity : (0 : ℝ) ≤ σ2 * (2 * Λ / ε) ^ 2)) zero_le_two
  rw [hkey] at h2
  linarith

/-- **The estimates of all phases are accurate with high probability.** Along a run of phased
elimination in a linear bandit environment with σ²-sub-Gaussian noise, `σ² ≠ 0` and `δ > 0`, the
probability that for some phase `ℓ < n` some survivor `b` has `ε_ℓ ≤ |⟪φ b, θ̂_ℓ - θ⟫|` is at most
`2 δ`. -/
theorem measure_exists_width_le_abs_inner_estimate_sub_le [StandardBorelSpace Ω]
    [IsProbabilityMeasure P] (h : IsAlgEnvSeq O A Y (phasedElimination D σ2 δ) env P)
    (henv : IsSubgaussianLinearEnv (fun _ : 𝓞 ↦ φ) θ σ2 env) (hσ : σ2 ≠ 0) (hδ : 0 < δ)
    (n : ℕ) :
    P {ω | ∃ ℓ < n, ∃ b ∈ survivors D σ2 δ (fun s ↦ Y s ω) ℓ,
      width ℓ ≤ |⟪φ b, estimate D σ2 δ (fun s ↦ Y s ω) ℓ - θ⟫_ℝ|} ≤ ENNReal.ofReal (2 * δ) := by
  set q : ℕ → ℝ := fun ℓ ↦ δ / (Fintype.card α * ((ℓ + 1) * (ℓ + 2)))
  have hq (ℓ : ℕ) : 0 ≤ q ℓ := by positivity
  set F : ℕ → α → ℝ → Set Ω := fun ℓ b r ↦ {ω | b ∈ survivors D σ2 δ (fun s ↦ Y s ω) ℓ ∧
    width ℓ ≤ r * ⟪φ b, estimate D σ2 δ (fun s ↦ Y s ω) ℓ - θ⟫_ℝ}
  have hsub : {ω | ∃ ℓ < n, ∃ b ∈ survivors D σ2 δ (fun s ↦ Y s ω) ℓ,
      width ℓ ≤ |⟪φ b, estimate D σ2 δ (fun s ↦ Y s ω) ℓ - θ⟫_ℝ|} ⊆
      ⋃ ℓ ∈ range n, ⋃ b ∈ (univ : Finset α), (F ℓ b 1 ∪ F ℓ b (-1)) := by
    rintro ω ⟨ℓ, hℓ, b, hb, hle⟩
    simp only [Set.mem_iUnion, mem_range, mem_univ, exists_true_left]
    refine ⟨ℓ, hℓ, b, ?_⟩
    rcases le_abs.1 hle with h' | h'
    · exact Or.inl ⟨hb, by rwa [one_mul]⟩
    · exact Or.inr ⟨hb, by rwa [neg_one_mul]⟩
  have hk : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
  calc P _ ≤ P (⋃ ℓ ∈ range n, ⋃ b ∈ (univ : Finset α), (F ℓ b 1 ∪ F ℓ b (-1))) :=
        measure_mono hsub
    _ ≤ ∑ ℓ ∈ range n, ∑ b : α, (P (F ℓ b 1) + P (F ℓ b (-1))) := by
        refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun ℓ _ ↦ ?_)
        exact (measure_biUnion_finset_le _ _).trans (sum_le_sum fun b _ ↦ measure_union_le _ _)
    _ ≤ ∑ ℓ ∈ range n, ∑ _b : α, (ENNReal.ofReal (q ℓ) + ENNReal.ofReal (q ℓ)) := by
        gcongr with ℓ _ b _
        · exact measure_mem_survivors_width_le_mul_inner_estimate_sub_le h henv hσ hδ ℓ b
            (by norm_num)
        · exact measure_mem_survivors_width_le_mul_inner_estimate_sub_le h henv hσ hδ ℓ b
            (by norm_num)
    _ = ENNReal.ofReal (∑ ℓ ∈ range n, ∑ _b : α, 2 * q ℓ) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun ℓ _ ↦ sum_nonneg fun _ _ ↦ by linarith [hq ℓ]]
        refine sum_congr rfl fun ℓ _ ↦ ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by linarith [hq ℓ]]
        refine sum_congr rfl fun _ _ ↦ ?_
        rw [two_mul, ENNReal.ofReal_add (hq ℓ) (hq ℓ)]
    _ ≤ ENNReal.ofReal (2 * δ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ∑ ℓ ∈ range n, ∑ _b : α, 2 * q ℓ
            = 2 * δ * ∑ ℓ ∈ range n, (((ℓ : ℝ) + 1) * (ℓ + 2))⁻¹ := by
              rw [mul_sum]
              refine sum_congr rfl fun ℓ _ ↦ ?_
              rw [sum_const, card_univ, nsmul_eq_mul]
              simp only [q]
              field_simp
          _ ≤ 2 * δ * 1 := by gcongr; exact sum_range_inv_add_one_mul_add_two_le_one n
          _ = 2 * δ := mul_one _

/-! ### The regret of phased elimination -/

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞] in
/-- On the event where the estimates of the survivors of the phases `ℓ < n` are within their
widths, the random regret of a run of phased elimination is at most
`32 √(σ² d n log (k n (n + 1) / δ)) + 8 s`. -/
private lemma linearRegret_le_of_forall {ω : Ω} (hA : ∀ n, A n ω = nextArm D σ2 δ (fun s ↦ Y s ω) n)
    (hgap : ∀ a b, ⟪θ, φ a⟫_ℝ - ⟪θ, φ b⟫_ℝ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {s : ℕ}
    (hs : ∀ S hS, #(D.design S hS).weights.support ≤ s) {n : ℕ}
    (hgood : ∀ ℓ < n, ∀ b ∈ survivors D σ2 δ (fun s ↦ Y s ω) ℓ,
      |⟪φ b, estimate D σ2 δ (fun s ↦ Y s ω) ℓ - θ⟫_ℝ| < width ℓ) :
    linearRegret (fun _ ↦ φ) θ O A n ω ≤
      32 * √(σ2 * finrank ℝ E * n * log (Fintype.card α * (n * (n + 1)) / δ)) + 8 * s := by
  rw [linearRegret_def]
  simp_rw [hA]
  exact sum_iSup_inner_sub_inner_nextArm_le hgap hδ hδ1 hs hgood

/-- **The regret of phased elimination with high probability** [LS, Theorem 22.1]. Let phased
elimination run in a linear bandit environment with finitely many arms, features `φ`, parameter
`θ` and σ²-sub-Gaussian noise, `σ² ≠ 0`, where the gaps between the expected rewards of two arms
are at most `1`, with `0 < δ ≤ 1` and designs with at most `s` support points. Then with
probability at least `1 - 2 δ`, the random regret after `n` rounds is at most
`32 √(σ² d n log (k n (n + 1) / δ)) + 8 s`. -/
theorem le_measureReal_linearRegret_le [StandardBorelSpace Ω] [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y (phasedElimination D σ2 δ) env P)
    (henv : IsSubgaussianLinearEnv (fun _ : 𝓞 ↦ φ) θ σ2 env) (hσ : σ2 ≠ 0)
    (hgap : ∀ a b, ⟪θ, φ a⟫_ℝ - ⟪θ, φ b⟫_ℝ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {s : ℕ}
    (hs : ∀ S hS, #(D.design S hS).weights.support ≤ s) (n : ℕ) :
    1 - 2 * δ ≤ P.real {ω | linearRegret (fun _ ↦ φ) θ O A n ω ≤
      32 * √(σ2 * finrank ℝ E * n * log (Fintype.card α * (n * (n + 1)) / δ)) + 8 * s} := by
  set G := {ω | linearRegret (fun _ ↦ φ) θ O A n ω ≤
    32 * √(σ2 * finrank ℝ E * n * log (Fintype.card α * (n * (n + 1)) / δ)) + 8 * s}
  have hGc : P Gᶜ ≤ ENNReal.ofReal (2 * δ) := by
    refine (measure_mono_ae ?_).trans
      (measure_exists_width_le_abs_inner_estimate_sub_le h henv hσ hδ n)
    filter_upwards [action_ae_all_eq h] with ω hA hω
    by_contra hnot
    simp only [not_exists, not_and, not_le] at hnot
    exact hω (linearRegret_le_of_forall hA hgap hδ hδ1 hs hnot)
  have h1 : 1 ≤ P.real G + P.real Gᶜ := by
    simpa [Set.union_compl_self, probReal_univ] using measureReal_union_le (μ := P) G Gᶜ
  have h2 : P.real Gᶜ ≤ 2 * δ := ENNReal.toReal_le_of_le_ofReal (by positivity) hGc
  linarith

/-- **The expected regret of phased elimination** [LS, Theorem 22.1]: under the assumptions of
`le_measureReal_linearRegret_le`, the expected regret after `n` rounds is at most
`2 n δ + 32 √(σ² d n log (k n (n + 1) / δ)) + 8 s`. -/
theorem integral_linearRegret_le [StandardBorelSpace Ω] [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y (phasedElimination D σ2 δ) env P)
    (henv : IsSubgaussianLinearEnv (fun _ : 𝓞 ↦ φ) θ σ2 env) (hσ : σ2 ≠ 0)
    (hgap : ∀ a b, ⟪θ, φ a⟫_ℝ - ⟪θ, φ b⟫_ℝ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {s : ℕ}
    (hs : ∀ S hS, #(D.design S hS).weights.support ≤ s) (n : ℕ) :
    P[linearRegret (fun _ ↦ φ) θ O A n] ≤ 2 * n * δ +
      (32 * √(σ2 * finrank ℝ E * n * log (Fintype.card α * (n * (n + 1)) / δ)) + 8 * s) := by
  set B := 32 * √(σ2 * finrank ℝ E * n * log (Fintype.card α * (n * (n + 1)) / δ)) + 8 * s
  have hB : 0 ≤ B := by positivity
  -- the event on which the estimate of some phase is inaccurate
  set bad := {ω | ∃ ℓ < n, ∃ b ∈ survivors D σ2 δ (fun s ↦ Y s ω) ℓ,
    width ℓ ≤ |⟪φ b, estimate D σ2 δ (fun s ↦ Y s ω) ℓ - θ⟫_ℝ|}
  have hbad : P bad ≤ ENNReal.ofReal (2 * δ) :=
    measure_exists_width_le_abs_inner_estimate_sub_le h henv hσ hδ n
  have hgap' : ∀ (o : 𝓞) a b, ⟪θ, φ a⟫_ℝ - ⟪θ, φ b⟫_ℝ ≤ 1 := fun _ ↦ hgap
  -- the regret is at most `B` outside `bad`, and at most `n` everywhere
  have hle : ∀ᵐ ω ∂P,
      linearRegret (fun _ ↦ φ) θ O A n ω ≤ B + n * (toMeasurable P bad).indicator 1 ω := by
    filter_upwards [action_ae_all_eq h] with ω hA
    by_cases hω : ω ∈ bad
    · rw [Set.indicator_of_mem (subset_toMeasurable P bad hω), Pi.one_apply, mul_one]
      exact (linearRegret_le_mul hgap').trans (by linarith)
    · refine (linearRegret_le_of_forall hA hgap hδ hδ1 hs fun ℓ hℓ b hb ↦ ?_).trans
        (le_add_of_nonneg_right ?_)
      · simp only [bad, Set.mem_ofPred_eq, not_exists, not_and, not_le] at hω
        exact hω ℓ hℓ b hb
      · exact mul_nonneg n.cast_nonneg (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
  have hint : Integrable (fun ω ↦ (n : ℝ) * (toMeasurable P bad).indicator 1 ω) P :=
    ((integrable_const (1 : ℝ)).indicator (measurableSet_toMeasurable P bad)).const_mul _
  have hnonneg : 0 ≤ᵐ[P] linearRegret (fun _ ↦ φ) θ O A n := by
    obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure P
    exact ae_of_all _ fun ω' ↦ linearRegret_nonneg fun o ↦
      bddAbove_range_inner_of_gap (hgap · (A 0 ω'))
  calc P[linearRegret (fun _ ↦ φ) θ O A n]
      ≤ ∫ ω, B + n * (toMeasurable P bad).indicator 1 ω ∂P :=
        integral_mono_of_nonneg hnonneg ((integrable_const B).add hint) hle
    _ = B + n * P.real (toMeasurable P bad) := by
        rw [integral_add (integrable_const B) hint, integral_const_mul,
          integral_indicator_one (measurableSet_toMeasurable P bad)]
        simp
    _ ≤ B + n * (2 * δ) := by
        gcongr
        rw [measureReal_def, measure_toMeasurable]
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbad
    _ = 2 * n * δ + B := by ring

/-- **The expected regret of phased elimination for `δ = 1 / n`** [LS, Theorem 22.1]: under the
assumptions of `integral_linearRegret_le` with the confidence level `δ = 1 / n`, the expected
regret after `n` rounds is at most `2 + 32 √(σ² d n log (k n² (n + 1))) + 8 s`, of order
`√(σ² d n log (k n)) + s`. -/
theorem integral_linearRegret_le_add_sqrt [StandardBorelSpace Ω] [IsProbabilityMeasure P]
    {n : ℕ} (h : IsAlgEnvSeq O A Y (phasedElimination D σ2 (1 / n)) env P)
    (henv : IsSubgaussianLinearEnv (fun _ : 𝓞 ↦ φ) θ σ2 env) (hσ : σ2 ≠ 0)
    (hgap : ∀ a b, ⟪θ, φ a⟫_ℝ - ⟪θ, φ b⟫_ℝ ≤ 1) {s : ℕ}
    (hs : ∀ S hS, #(D.design S hS).weights.support ≤ s) :
    P[linearRegret (fun _ ↦ φ) θ O A n] ≤
      2 + 32 * √(σ2 * finrank ℝ E * n * log (Fintype.card α * (n * (n + 1)) * n)) + 8 * s := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [linearRegret_zero, integral_zero]
    positivity
  have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
  have h1 := integral_linearRegret_le h henv hσ hgap (by positivity)
    ((div_le_one (by positivity)).2 hn') hs n
  rw [one_div, div_inv_eq_mul, mul_inv_cancel_right₀ (by positivity : (n : ℝ) ≠ 0)] at h1
  linarith

end Run

end LMLExplore.Bandits.PhasedElimination
