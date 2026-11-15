/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Smooth
public import LMLExplore.Analysis.SumIntegralComparisons
public import LMLExplore.OnlineLearning.SubgradientDescent

/-!
# Adaptive learning rates and `L⋆` bounds

The regret bound of mirror descent with nonincreasing learning rates `η t` and an `m`-strongly
convex potential `F` is `B / η (n - 1) + ∑ t < n, η t / (2 m) * ‖y t‖ ^ 2`, where `B` bounds the
Bregman divergences `D_F(u, a t)` from the plays to the comparator. The learning rate that
balances the two terms after `n` rounds depends on the losses to come. The **adaptive learning
rates** [Ora, Section 4.2, Theorem 4.14]
`η t = √(m B / ∑ s ≤ t, ‖y s‖ ^ 2)`
use instead the losses observed so far, the loss of the current round included, and give the
regret bound `2 √(B ∑ t < n, ‖y t‖ ^ 2 / m)` against every comparator, at every horizon, with no
bound on the losses known in advance. While the losses observed so far all vanish, the learning
rate is `√(m B / 0) = 0` with Lean's division, and the step for the learning rate `0` is a
Bregman projection of the current play: the algorithm makes no step, as in [Ora].

For projected online subgradient descent with plays at distance at most `D` from the
comparator, as on a set of diameter `D`, the potential `‖·‖ ^ 2 / 2` with `B = D ^ 2 / 2` gives
the rates `η t = D / √(2 ∑ s ≤ t, ‖g s‖ ^ 2)` and the regret bound
`D √(2 ∑ t < n, ‖g t‖ ^ 2)` [Ora, Theorem 4.14]. When the squared norms of the subgradients are
controlled by the losses, `‖g t‖ ^ 2 ≤ 2 s f t (a t)`, as for nonnegative `s`-self-bounded losses
(`LMLExplore.SelfBoundedOn`), the regret is in turn controlled by the cumulative loss of the
comparator `u`: it is at most `4 s D ^ 2 + 2 D √(s ∑ t < n, f t u)` [Ora, Theorem 4.30]. This
**`L⋆` bound** is constant when the comparator has zero cumulative loss.

## Main statements

* `mirrorDescent_regret_le_two_mul_sqrt`: mirror descent with an `m`-strongly convex potential and
  the adaptive learning rates has regret at most `2 √(B ∑ t < n, ‖y t‖ ^ 2 / m)`.
* `onlineSubgradientDescent_regret_le_mul_sqrt_sum`: [Ora, Theorem 4.14] projected online
  subgradient descent with the adaptive learning rates, with plays at distance at most `D` from the
  comparator, has regret at most `D √(2 ∑ t < n, ‖g t‖ ^ 2)`.
* `onlineSubgradientDescent_regret_le_of_norm_sq_le`: [Ora, Theorem 4.30] the `L⋆` bound
  `4 s D ^ 2 + 2 D √(s ∑ t < n, f t u)` for losses with `‖g t‖ ^ 2 ≤ 2 s f t (a t)`.
* `onlineSubgradientDescent_regret_le_of_selfBoundedOn`: its form for nonnegative `s`-self-bounded
  losses.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Finset
open scoped NNReal

namespace LMLExplore.OnlineLearning

variable {n : ℕ}

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {F : E → ℝ} {u : E}

/-- The two terms of the regret bound balance at the adaptive learning rates: if `r ^ 2 = m B`,
then `B √A / r + r √A / m = 2 √(B A / m)`. -/
private lemma mul_sqrt_div_add_mul_sqrt_div_eq {r m B A : ℝ} (hr : 0 < r) (hm : 0 < m)
    (hr_sq : r ^ 2 = m * B) (hA : 0 ≤ A) :
    B * √A / r + r * √A / m = 2 * √(B * A / m) := by
  have h_B : B * √A / r = r * √A / m := by
    rw [div_eq_div_iff hr.ne' hm.ne']
    linear_combination (-√A) * hr_sq
  have h_sqrt : √(B * A / m) = r * √A / m := by
    rw [show B * A / m = (r * √A / m) ^ 2 by
      rw [div_pow, mul_pow, hr_sq, Real.sq_sqrt hA]
      field_simp]
    exact Real.sqrt_sq (by positivity)
  rw [h_B, h_sqrt]
  ring

/-- The case of `mirrorDescent_regret_le_two_mul_sqrt` with `B > 0` and a first round `t₀ < n`
with a nonzero loss. From `t₀` on, the adaptive learning rates are positive and nonincreasing;
before `t₀` the losses vanish, so that the steps are also steps for the learning rate of `t₀`,
and the bound of mirror descent with nonincreasing learning rates applies. -/
private theorem mirrorDescent_regret_le_two_mul_sqrt_of_ne_zero {m B : ℝ}
    (hF : StrongConvexOn K m F) (hm : 0 < m) (hB : 0 < B) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E)
    (F' : ℕ → E →L[ℝ] ℝ) (ha0K : a 0 ∈ K) {t₀ : ℕ} (ht₀n : t₀ < n) (hyt₀ : y t₀ ≠ 0)
    (hy_lt : ∀ t < t₀, y t = 0)
    (ha : ∀ t < n, IsMirrorDescentStep K F (√(m * B / ∑ s ∈ range (t + 1), ‖y s‖ ^ 2)) (y t)
      (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t))
    (hBu : ∀ t < n, bregDiv F u (a t) (F' t) ≤ B) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ 2 * √(B * (∑ t ∈ range n, ‖y t‖ ^ 2) / m) := by
  set S : ℕ → ℝ := fun t ↦ ∑ s ∈ range (t + 1), ‖y s‖ ^ 2 with hS_def
  set A := ∑ t ∈ range n, ‖y t‖ ^ 2 with hA_def
  have hS_mono : Monotone S := fun s t hst ↦
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun _ _ _ ↦ sq_nonneg _
  have hS_pos (t : ℕ) (ht : t₀ ≤ t) : 0 < S t :=
    calc 0 < ‖y t₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hyt₀) 2
      _ ≤ S t := single_le_sum (f := fun s ↦ ‖y s‖ ^ 2) (fun _ _ ↦ sq_nonneg _)
        (mem_range.mpr (by omega))
  -- the learning rate of round `t` is `r / √(S t)`, with `r = √(m B)`
  set r := √(m * B) with hr_def
  have hr : 0 < r := Real.sqrt_pos.mpr (mul_pos hm hB)
  have hr_sq : r ^ 2 = m * B := Real.sq_sqrt (mul_pos hm hB).le
  have h_rate (t : ℕ) : √(m * B / S t) = r / √(S t) := Real.sqrt_div' _ (by positivity)
  -- the learning rates frozen at round `t₀` before it are positive and nonincreasing
  set η : ℕ → ℝ := fun t ↦ r / √(S (max t t₀)) with hη_def
  have hη (t : ℕ) : 0 < η t := div_pos hr (Real.sqrt_pos.mpr (hS_pos _ (le_max_right _ _)))
  have hη_anti : Antitone η := fun s t hst ↦
    div_le_div_of_nonneg_left hr.le (Real.sqrt_pos.mpr (hS_pos _ (le_max_right _ _)))
      (Real.sqrt_le_sqrt (hS_mono (max_le_max hst le_rfl)))
  have ha' (t : ℕ) (ht : t < n) :
      IsMirrorDescentStep K F (η t) (y t) (a t) (F' t) (a (t + 1)) := by
    have h_step := ha t ht
    rcases lt_or_ge t t₀ with htt | htt
    · rw [hy_lt t htt] at h_step ⊢
      exact isMirrorDescentStep_zero_iff.mpr (isMirrorDescentStep_zero_iff.mp h_step)
    · simp only [hη_def, max_eq_left htt, ← h_rate]
      exact h_step
  have h := mirrorDescent_regret_le_of_strongConvexOn_of_antitone hF hm hη hη_anti y a F' ha0K ha'
    hF' hB.le hBu hu
  -- the first term is `B √A / r`, and the stability terms add up to at most `r √A / m`
  have h_first : B / η (n - 1) = B * √A / r := by
    have hn : 0 < n := (Nat.zero_le t₀).trans_lt ht₀n
    have hSn : S (n - 1) = A := by simp only [hS_def, hA_def, Nat.sub_add_cancel hn]
    simp only [hη_def, max_eq_left (Nat.le_sub_one_of_lt ht₀n), hSn, div_div_eq_mul_div]
  have h_term (t : ℕ) (ht : t ∈ range n) :
      η t / (2 * m) * ‖y t‖ ^ 2 = r / (2 * m) * (‖y t‖ ^ 2 / √(S t)) := by
    rcases lt_or_ge t t₀ with htt | htt
    · simp [hy_lt t htt]
    · simp only [hη_def, max_eq_left htt]
      ring
  have h_stab : ∑ t ∈ range n, η t / (2 * m) * ‖y t‖ ^ 2 ≤ r * √A / m := by
    rw [sum_congr rfl h_term, ← mul_sum]
    calc r / (2 * m) * ∑ t ∈ range n, ‖y t‖ ^ 2 / √(S t) ≤ r / (2 * m) * (2 * √A) :=
          mul_le_mul_of_nonneg_left (Real.sum_div_sqrt_le_two_mul_sqrt fun _ _ ↦ sq_nonneg _)
            (by positivity)
      _ = r * √A / m := by field_simp
  linarith [mul_sqrt_div_add_mul_sqrt_div_eq hr hm hr_sq (sum_nonneg fun _ _ ↦ sq_nonneg _ : 0 ≤ A)]

/-- **Mirror descent with adaptive learning rates**, the form of [Ora, Theorem 4.14] for mirror
descent with a strongly convex potential. Let `F` be `m`-strongly
convex on `K`, with `m > 0`. Let `a 0 ∈ K` and let each `a (t + 1)`, for `t < n`, be a mirror
descent step on `K` from `a t` with derivative `F' t`, for the loss `y t` and the learning rate
`η t = √(m B / ∑ s ≤ t, ‖y s‖ ^ 2)`, where `F` has derivative `F' t` within `K` at `a t` for
`t ≤ n`. If `B` bounds the Bregman divergences `D_F(u, a t)` for `t < n`, then for every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ 2 √(B ∑ t < n, ‖y t‖ ^ 2 / m)`,
where `‖y t‖` is the dual norm. While the losses observed so far vanish, the learning rate is `0`
and the step is a Bregman projection of `a t`, so that the algorithm stays at `a t`. -/
theorem mirrorDescent_regret_le_two_mul_sqrt {m B : ℝ} (hF : StrongConvexOn K m F) (hm : 0 < m)
    (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ) (ha0K : a 0 ∈ K)
    (ha : ∀ t < n, IsMirrorDescentStep K F (√(m * B / ∑ s ∈ range (t + 1), ‖y s‖ ^ 2)) (y t)
      (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t))
    (hBu : ∀ t < n, bregDiv F u (a t) (F' t) ≤ B) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ 2 * √(B * (∑ t ∈ range n, ‖y t‖ ^ 2) / m) := by
  have h_mem := mem_of_isMirrorDescentStep ha0K ha
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  -- `B ≥ 0`, as the Bregman divergences of a convex function are nonnegative
  have hB : 0 ≤ B := ((hF' 0 hn.le).hasSubgradientWithinAt
    (strongConvexOn_zero.mp (hF.mono hm.le)) ha0K u hu).trans (hBu 0 hn)
  -- if every loss vanishes, so does the regret
  by_cases hy : ∀ t < n, y t = 0
  · rw [sum_eq_zero fun t ht ↦ by simp [hy t (mem_range.mp ht)]]
    positivity
  push Not at hy
  rcases hB.eq_or_lt with hB0 | hB0
  · -- if `B = 0`, every play is the comparator, by strong convexity
    refine (sum_eq_zero fun t ht ↦ ?_).le.trans (by positivity)
    have ht := mem_range.mp ht
    have h_lower := hF.mul_norm_sub_sq_le_bregDiv (h_mem t ht.le) hu (hF' t ht.le)
    have h_sq : ‖u - a t‖ ^ 2 = 0 := by nlinarith [hBu t ht, sq_nonneg ‖u - a t‖]
    rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at h_sq
    simp [h_sq]
  -- otherwise, let `t₀` be the first round with a nonzero loss
  classical
  refine mirrorDescent_regret_le_two_mul_sqrt_of_ne_zero hF hm hB0 y a F' ha0K
    (Nat.find_spec hy).1 (Nat.find_spec hy).2 (fun t ht ↦ ?_) ha hF' hBu hu
  by_contra h
  exact Nat.find_min hy ht ⟨ht.trans (Nat.find_spec hy).1, h⟩

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E} {u : E}

/-- **Projected online subgradient descent with adaptive learning rates** [Ora, Theorem 4.14].
Let `K` be convex, and let `g t` be a subgradient of the loss `f t` within `K` at `a t`, for
`t < n`. Let `a 0 ∈ K` and let each `a (t + 1)` be a point of `K` nearest to `a t - η t • g t`, for
the learning rate `η t = D / √(2 ∑ s ≤ t, ‖g s‖ ^ 2)`. If `‖u - a t‖ ≤ D` for `t < n`, for
instance if `u ∈ K` and `K` has diameter at most `D`, then
`regret f a u n ≤ D √(2 ∑ t < n, ‖g t‖ ^ 2)`.
The learning rates need neither the horizon nor a bound on the subgradients. While the
subgradients observed so far vanish, the learning rate is `0` and the algorithm stays at `a t`. -/
theorem onlineSubgradientDescent_regret_le_mul_sqrt_sum (hK : Convex ℝ K) {D : ℝ}
    (f : ℕ → E → ℝ) (g a : ℕ → E)
    (hg : ∀ t < n, HasSubgradientWithinAt (f t) (innerSL ℝ (g t)) K (a t)) (ha0 : a 0 ∈ K)
    (ha : ∀ t < n, a (t + 1) ∈ K ∧ IsMinOn
      (fun b ↦ ‖b - (a t - (D / √(2 * ∑ s ∈ range (t + 1), ‖g s‖ ^ 2)) • g t)‖) K (a (t + 1)))
    (hD : ∀ t < n, ‖u - a t‖ ≤ D) (hu : u ∈ K) :
    regret f a u n ≤ D * √(2 * ∑ t ∈ range n, ‖g t‖ ^ 2) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [regret_def]
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 hn)
  -- the learning rates are those of `mirrorDescent_regret_le_two_mul_sqrt` for the potential
  -- `‖·‖ ^ 2 / 2`, with `m = 1` and `B = D ^ 2 / 2`
  have h_rate (S : ℝ) (hS : 0 ≤ S) : √(1 * (D ^ 2 / 2) / S) = D / √(2 * S) := by
    rw [show 1 * (D ^ 2 / 2) / S = D ^ 2 / (2 * S) by ring, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq hD0]
  have ha' (t : ℕ) (ht : t < n) : IsMirrorDescentStep K (fun b : E ↦ ‖b‖ ^ 2 / 2)
      (√(1 * (D ^ 2 / 2) / ∑ s ∈ range (t + 1), ‖innerSL ℝ (g s)‖ ^ 2)) (innerSL ℝ (g t)) (a t)
      (innerSL ℝ (a t)) (a (t + 1)) := by
    simp only [innerSL_apply_norm]
    rw [h_rate _ (sum_nonneg fun _ _ ↦ sq_nonneg _)]
    exact isMirrorDescentStep_norm_sq_div_two_iff.mpr (ha t ht)
  have hBu (t : ℕ) (ht : t < n) :
      bregDiv (fun b : E ↦ ‖b‖ ^ 2 / 2) u (a t) (innerSL ℝ (a t)) ≤ D ^ 2 / 2 := by
    rw [bregDiv_norm_sq_div_two]
    gcongr
    exact hD t ht
  have h := mirrorDescent_regret_le_two_mul_sqrt (strongConvexOn_norm_sq_div_two hK) one_pos
    (fun t ↦ innerSL ℝ (g t)) a (fun t ↦ innerSL ℝ (a t)) ha0 ha'
    (fun t _ ↦ (hasFDerivAt_norm_sq_div_two _).hasFDerivWithinAt) hBu hu
  simp only [innerSL_apply_norm] at h
  rw [regret_def]
  refine (sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt f _ a hg hu).trans (h.trans_eq ?_)
  rw [div_one, show D ^ 2 / 2 * ∑ t ∈ range n, ‖g t‖ ^ 2 =
    (D / 2) ^ 2 * (2 * ∑ t ∈ range n, ‖g t‖ ^ 2) by ring, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (by positivity)]
  ring

/-- **The `L⋆` bound of projected online subgradient descent** [Ora, Theorem 4.30]. Under the
assumptions of `onlineSubgradientDescent_regret_le_mul_sqrt_sum`, if moreover the subgradients
satisfy `‖g t‖ ^ 2 ≤ 2 s f t (a t)` for `t < n`, then
`regret f a u n ≤ 4 s D ^ 2 + 2 D √(s ∑ t < n, f t u)`.
The bound depends on the cumulative loss of the comparator, and not on the number of rounds. -/
theorem onlineSubgradientDescent_regret_le_of_norm_sq_le (hK : Convex ℝ K) {D : ℝ} {s : ℝ≥0}
    (f : ℕ → E → ℝ) (g a : ℕ → E)
    (hg : ∀ t < n, HasSubgradientWithinAt (f t) (innerSL ℝ (g t)) K (a t))
    (hgf : ∀ t < n, ‖g t‖ ^ 2 ≤ 2 * s * f t (a t)) (ha0 : a 0 ∈ K)
    (ha : ∀ t < n, a (t + 1) ∈ K ∧ IsMinOn
      (fun b ↦ ‖b - (a t - (D / √(2 * ∑ s ∈ range (t + 1), ‖g s‖ ^ 2)) • g t)‖) K (a (t + 1)))
    (hD : ∀ t < n, ‖u - a t‖ ≤ D) (hu : u ∈ K) :
    regret f a u n ≤ 4 * s * D ^ 2 + 2 * D * √(s * ∑ t ∈ range n, f t u) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [regret_def, range_zero, sum_empty, mul_zero, Real.sqrt_zero, add_zero]
    positivity
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 hn)
  set L := ∑ t ∈ range n, f t (a t)
  set U := ∑ t ∈ range n, f t u
  have h_reg : regret f a u n = L - U := by rw [regret_def, sum_sub_distrib]
  have h := onlineSubgradientDescent_regret_le_mul_sqrt_sum hK f g a hg ha0 ha hD hu
  -- the squared subgradients add up to at most `2 s L`, so that `L - U ≤ √(4 s D ^ 2 L)`
  have h_sum : 2 * ∑ t ∈ range n, ‖g t‖ ^ 2 ≤ 4 * s * L := by
    have := sum_le_sum fun t ht ↦ hgf t (mem_range.mp ht)
    rw [← mul_sum] at this
    linarith
  have h_imp : L - √(4 * s * D ^ 2 * L + 0) ≤ U := by
    have h_le : D * √(2 * ∑ t ∈ range n, ‖g t‖ ^ 2) ≤ √(4 * s * D ^ 2 * L + 0) := by
      rw [add_zero, show 4 * s * D ^ 2 * L = D ^ 2 * (4 * s * L) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hD0]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h_sum) hD0
    linarith
  -- solving for `L` gives `L ≤ 4 s D ^ 2 + U + √(4 s D ^ 2 U)`
  have h_sol := Real.le_add_add_sqrt_of_sub_sqrt_le (by positivity) h_imp
  rw [zero_add, show 4 * s * D ^ 2 * U = (2 * D) ^ 2 * (s * U) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)] at h_sol
  rw [h_reg]
  linarith

/-- **The `L⋆` bound for self-bounded losses** [Ora, Theorem 4.30]. Let `K` be convex, and let the
losses `f t` be nonnegative and `s`-self-bounded within `K`, with a subgradient `g t` within `K`
at `a t`, for `t < n`. Let `a 0 ∈ K` and let each `a (t + 1)` be a point of `K` nearest to
`a t - η t • g t`, for the learning rate `η t = D / √(2 ∑ s ≤ t, ‖g s‖ ^ 2)`. If `u ∈ K` and
`‖u - a t‖ ≤ D` for `t < n`, as on a set of diameter at most `D`, then
`regret f a u n ≤ 4 s D ^ 2 + 2 D √(s ∑ t < n, f t u)`. -/
theorem onlineSubgradientDescent_regret_le_of_selfBoundedOn (hK : Convex ℝ K) {D : ℝ}
    {s : ℝ≥0} (f : ℕ → E → ℝ) (g a : ℕ → E)
    (hf : ∀ t < n, SelfBoundedOn K s (f t)) (hf0 : ∀ t < n, ∀ x ∈ K, 0 ≤ f t x)
    (hg : ∀ t < n, HasSubgradientWithinAt (f t) (innerSL ℝ (g t)) K (a t)) (ha0 : a 0 ∈ K)
    (ha : ∀ t < n, a (t + 1) ∈ K ∧ IsMinOn
      (fun b ↦ ‖b - (a t - (D / √(2 * ∑ s ∈ range (t + 1), ‖g s‖ ^ 2)) • g t)‖) K (a (t + 1)))
    (hD : ∀ t < n, ‖u - a t‖ ≤ D) (hu : u ∈ K) :
    regret f a u n ≤ 4 * s * D ^ 2 + 2 * D * √(s * ∑ t ∈ range n, f t u) := by
  have h_mem := mem_of_isMirrorDescentStep (η := fun t ↦ D / √(2 * ∑ s ∈ range (t + 1), ‖g s‖ ^ 2))
    ha0 fun t ht ↦ isMirrorDescentStep_norm_sq_div_two_iff.mpr (ha t ht)
  refine onlineSubgradientDescent_regret_le_of_norm_sq_le hK f g a hg (fun t ht ↦ ?_) ha0 ha hD hu
  have := (hf t ht).norm_sq_le_of_nonneg (hf0 t ht) (h_mem t ht.le) (hg t ht)
  rwa [innerSL_apply_norm] at this

end InnerProductSpace

end LMLExplore.OnlineLearning
