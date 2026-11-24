/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.MultipleTesting.PRDS
import LMLExplore.Data.Finset.Card
import LMLExplore.MeasureTheory.MeasurableSpace.Constructions
import LMLExplore.EValues.MultipleTesting.Simes

/-!
# Closed BH

For `m` hypotheses with p-values `x`, Goeman's BH-like methods [Goe26, §2] are parametrized by
horizons `r k s` (`ProbabilityTheory.IsBHLikeHorizon m r`), for `0 ≤ k ≤ m` and steps
`1 ≤ s ≤ m`. They compare the `k`-th smallest p-value `x_(k)` with the threshold
`a k s = α * bhLikeRatio m r k s` [Goe26, (4)], and reject the
`bhLikeCount r α x` hypotheses with the smallest p-values: the largest `k` such that, at every
step `s`, some `k' ≤ k` with `x_(k') ≤ a k' s` has a horizon `r k' s ≥ k` [Goe26, (5)]. BH uses
the thresholds `k * α / m` of the last step only. Closed BH (`ProbabilityTheory.closedBHHorizon`)
takes the largest horizons that keep the thresholds at least those of BH [Goe26, §5].

The proof of false discovery rate control goes through the e-Closure Principle. The threshold
`a (k_s) s` at the index `k_s` (`ProbabilityTheory.bhLikeIndex`) [Goe26, (8)] is coordinatewise
nonincreasing in the p-values [Goe26, Lemmas 6 and 7], so that the threshold statistics of these
thresholds (`ProbabilityTheory.bhLikeECollection`) form an e-collection under PRDS by the lemma of
Blanchard and Roquain [Goe26, Theorem 8]. Every set of `bhLikeCount r α x` hypotheses with the
smallest p-values, with ties broken in any way, lies in the e-closure of this e-collection for the
false discovery proportion [Goe26, Lemmas 10 and 11], which bounds its false discovery rate by
`α` under PRDS [Goe26, Theorem 12], and by `α` times the expectation of the statistic of the true
nulls in general [Goe26, Theorem 13]. When the horizons satisfy `r k s * (m - k) ≤ k * s` above
the antidiagonal and before the last step `s < m`, as those of closed BH do, the method rejects
every hypothesis that BH rejects [Goe26, Proposition 16].

## Main definitions

* `ProbabilityTheory.IsBHLikeHorizon m r`: `r` is a family of horizons for `m` hypotheses
  [Goe26, (1)–(3)].
* `ProbabilityTheory.bhLikeRatio m r k s`, `ProbabilityTheory.bhLikeThreshold m r α k s`: the
  thresholds `a k s / α` and `a k s` [Goe26, (4)].
* `ProbabilityTheory.bhLikeCount r α x`: the number of rejections [Goe26, (5)].
* `ProbabilityTheory.bhLikeIndex r α x s`: the index `k_s` [Goe26, (8)].
* `ProbabilityTheory.bhLikeECollection r α p`: the e-collection [Goe26, (9)].
* `ProbabilityTheory.closedBHHorizon m`: the horizons of closed BH [Goe26, §5].

## Main statements

* `ProbabilityTheory.IsBHLikeHorizon.bhLikeRatio_mono`: the thresholds are nondecreasing in `k`
  [Goe26, Lemma 7].
* `ProbabilityTheory.IsBHLikeHorizon.mul_bhLikeRatio_le`,
  `ProbabilityTheory.IsBHLikeHorizon.div_le_div_mul_bhLikeRatio`: the horizon inequality [Goe26,
  Lemma 10].
* `ProbabilityTheory.bhLikeIndex_anti`: the index `k_s` is nonincreasing in the p-values
  [Goe26, Lemma 6].
* `ProbabilityTheory.IsBHLikeHorizon.isECollection_bhLikeECollection`: the e-collection is an
  e-collection under PRDS [Goe26, Theorem 8].
* `ProbabilityTheory.IsBHLikeHorizon.mem_eClosure_fdp_bhLikeECollection`: the rejections lie in
  its e-closure [Goe26, Lemma 11].
* `ProbabilityTheory.IsBHLikeHorizon.lintegral_fdp_le`: BH-like methods, closed BH among them,
  control the false discovery rate under PRDS [Goe26, Theorem 12].
* `ProbabilityTheory.IsBHLikeHorizon.lintegral_fdp_le_mul_lintegral_bhLikeECollection`: the
  level retained when PRDS fails [Goe26, Theorem 13].
* `ProbabilityTheory.IsBHLikeHorizon.eBH_inv_subset`: under the criterion of [Goe26,
  Proposition 16], the method rejects every hypothesis that BH rejects.
* `ProbabilityTheory.isBHLikeHorizon_closedBHHorizon`: closed BH is a BH-like method [Goe26,
  Lemmas 1 and 2].
* `ProbabilityTheory.eBH_inv_subset_of_card_eq_bhLikeCount_closedBHHorizon`: closed BH rejects
  every hypothesis that BH rejects.

## Implementation notes

Order statistics are avoided: `x_(k) ≤ a` is written `k ≤ #{i | x i ≤ a}`, and the rejection set
is any set `R` of `bhLikeCount r α x` hypotheses with `x i ≤ x j` for `i ∈ R` and `j ∉ R`, which
exists (`ProbabilityTheory.exists_card_eq_bhLikeCount`) and need not be measurable. The growth
bound [Goe26, (3)] on the horizons, a bound by a quotient `b k s`, is written multiplied out in
`ℕ`, where truncated subtraction makes it vacuous exactly when [Goe26] puts no bound. The
constraint `r 1 m = m` of [Goe26, (1)] is not imposed, since no statement here needs it; BH itself,
with `r k s = k`, is then a BH-like method. The threshold ratios are real numbers, and the
arithmetic of [Goe26, Lemmas 7 and 10] is done in `ℝ`.

## References

* [Goe26] J. Goeman, *A uniform improvement of the Benjamini–Hochberg procedure via e-Closure*,
  arXiv:2606.01854v2.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

/-! ### Horizons and thresholds -/

/-- **Horizons** of a BH-like method for `m` hypotheses [Goe26, §2]: integers `r k s` for
`0 ≤ k ≤ m` and `1 ≤ s ≤ m`, with `r k s = k` when `k + s ≤ m + 1`, except possibly at `k = 1`,
`s = m` [Goe26, (1)], with `k ≤ r k s` [Goe26, (2)], and nondecreasing in `k` with the growth
bound `r (k + 1) s ≤ b (k + 1) s` of [Goe26, (3)]. The bound is written multiplied out, in `ℕ`:
`r (k + 1) s * (c * d - r k s) ≤ d * (c - 1) * r k s` with `c = k + 1 + s - m` and `d = m - s`,
which says nothing when `c * d ≤ r k s`, exactly as in [Goe26]. [Goe26] also sets `r 1 m = m`,
which none of the statements below needs, and asks `r k s ≤ m`, which they do not need either. -/
structure IsBHLikeHorizon (m : ℕ) (r : ℕ → ℕ → ℕ) : Prop where
  /-- Up to the antidiagonal `k + s = m + 1`, the horizon of `k` is `k`, except possibly at
  `k = 1`, `s = m`. -/
  apply_eq_self ⦃k s : ℕ⦄ : 1 ≤ s → k + s ≤ m + 1 → (k = 1 → s < m) → r k s = k
  /-- The horizon of `k` is at least `k`. -/
  le_apply ⦃k s : ℕ⦄ : k ≤ m → 1 ≤ s → s ≤ m → k ≤ r k s
  /-- The horizons are nondecreasing in `k`. -/
  apply_le_apply_succ ⦃k s : ℕ⦄ : k < m → 1 ≤ s → s ≤ m → r k s ≤ r (k + 1) s
  /-- The growth bound `r (k + 1) s ≤ b (k + 1) s` [Goe26, (3)], multiplied out. -/
  apply_succ_mul_le ⦃k s : ℕ⦄ : k < m → 1 ≤ s → s ≤ m →
    r (k + 1) s * ((k + 1 + s - m) * (m - s) - r k s) ≤ (m - s) * (k + s - m) * r k s

/-- The ratio `a k s / α` of the threshold of a BH-like method to the level [Goe26, (4)]:
`k / s` when `k + s ≤ m`, and `(k + s - m) * r k s / ((r k s + s - m) * s)` otherwise. When
`r k s = k` both expressions are `k / s`. -/
noncomputable def bhLikeRatio (m : ℕ) (r : ℕ → ℕ → ℕ) (k s : ℕ) : ℝ :=
  if k + s ≤ m then k / s else ((k : ℝ) + s - m) * r k s / (((r k s : ℝ) + s - m) * s)

variable {m : ℕ} {r : ℕ → ℕ → ℕ} {k l j s t : ℕ}

theorem bhLikeRatio_of_le (h : k + s ≤ m) : bhLikeRatio m r k s = k / s :=
  ite_eq_left h

theorem bhLikeRatio_of_lt (h : m < k + s) : bhLikeRatio m r k s =
    ((k : ℝ) + s - m) * r k s / (((r k s : ℝ) + s - m) * s) :=
  ite_eq_right (not_le.2 h)

namespace IsBHLikeHorizon

variable (hr : IsBHLikeHorizon m r)
include hr

/-- The horizon of `0` is `0`. -/
theorem apply_zero (hs : 1 ≤ s) (hsm : s ≤ m) : r 0 s = 0 :=
  hr.apply_eq_self hs (by omega) (by omega)

/-- The horizons are nondecreasing in `k` up to `m`. -/
theorem apply_mono (hkl : k ≤ l) (hl : l ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) : r k s ≤ r l s := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l hkl ih => exact (ih (by omega)).trans (hr.apply_le_apply_succ (by omega) hs hsm)

/-- Above the antidiagonal, the denominator `r k s + s - m` of the threshold ratio is at least
`k + s - m`, hence positive. -/
theorem le_apply_add_sub (hk : k ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) :
    (k : ℝ) + s - m ≤ r k s + s - m := by
  have := hr.le_apply hk hs hsm
  have : (k : ℝ) ≤ r k s := by exact_mod_cast this
  linarith

/-- The threshold ratios are nonnegative. -/
theorem bhLikeRatio_nonneg (hk : k ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) : 0 ≤ bhLikeRatio m r k s := by
  rcases le_or_gt (k + s) m with h | h
  · rw [bhLikeRatio_of_le h]
    positivity
  · rw [bhLikeRatio_of_lt h]
    have h' : (m : ℝ) < k + s := by exact_mod_cast h
    have := hr.le_apply_add_sub hk hs hsm
    have : (0 : ℝ) ≤ r k s := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    exact div_nonneg (mul_nonneg (by linarith) (by assumption)) (mul_nonneg (by linarith) this)

/-- The threshold ratio of a positive `k` is positive. -/
theorem bhLikeRatio_pos (hk₀ : 1 ≤ k) (hk : k ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) :
    0 < bhLikeRatio m r k s := by
  have hs₀ : (0 : ℝ) < s := by exact_mod_cast hs
  rcases le_or_gt (k + s) m with h | h
  · rw [bhLikeRatio_of_le h]
    have : (0 : ℝ) < k := by exact_mod_cast hk₀
    positivity
  · rw [bhLikeRatio_of_lt h]
    have h' : (m : ℝ) < k + s := by exact_mod_cast h
    have := hr.le_apply_add_sub hk hs hsm
    have : (0 : ℝ) < r k s := by exact_mod_cast (hk₀.trans (hr.le_apply hk hs hsm))
    exact div_pos (mul_pos (by linarith) this) (mul_pos (by linarith) hs₀)

/-- The growth bound of the horizons in `ℝ`, above the antidiagonal, where the truncated
subtractions of `ℕ` are genuine: `r (k + 1) s * ((k + 1 + s - m) * (m - s) - r k s)` is at most
`(m - s) * (k + s - m) * r k s`, also when the left factor is negative. -/
private lemma cast_apply_succ_mul_le (hk : k < m) (hs : 1 ≤ s) (hsm : s ≤ m) (h₂ : m < k + s) :
    (r (k + 1) s : ℝ) * (((k : ℝ) + 1 + s - m) * (m - s) - r k s) ≤
      (m - s) * (k + s - m) * r k s := by
  have hb := hr.apply_succ_mul_le hk hs hsm
  have e₁ : ((k + 1 + s - m : ℕ) : ℝ) = (k : ℝ) + 1 + s - m := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have e₂ : ((m - s : ℕ) : ℝ) = (m : ℝ) - s := Nat.cast_sub hsm
  have e₃ : ((k + s - m : ℕ) : ℝ) = (k : ℝ) + s - m := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rcases le_or_gt (r k s) ((k + 1 + s - m) * (m - s)) with h | h
  · have := (Nat.cast_le (α := ℝ)).2 hb
    push_cast [Nat.cast_sub h] at this
    rwa [e₁, e₂, e₃] at this
  · have h' : ((k : ℝ) + 1 + s - m) * (m - s) < r k s := by
      rw [← e₁, ← e₂]
      exact_mod_cast h
    have : (0 : ℝ) ≤ (m - s) * (k + s - m) * r k s := by
      have : (s : ℝ) ≤ m := by exact_mod_cast hsm
      have : (0 : ℝ) ≤ r k s := Nat.cast_nonneg _
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) this
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)) this

/-- **The thresholds are nondecreasing in `k`**, one step [Goe26, Lemma 7]. This is where the
growth bound on the horizons is used: above the antidiagonal it is exactly the inequality between
consecutive threshold ratios, multiplied out. -/
theorem bhLikeRatio_le_succ (hk : k < m) (hs : 1 ≤ s) (hsm : s ≤ m) :
    bhLikeRatio m r k s ≤ bhLikeRatio m r (k + 1) s := by
  have hs₀ : (0 : ℝ) < s := by exact_mod_cast hs
  rcases le_or_gt (k + 1 + s) m with h₁ | h₁
  · rw [bhLikeRatio_of_le h₁, bhLikeRatio_of_le (by omega)]
    gcongr
    linarith
  rw [bhLikeRatio_of_lt h₁]
  have hR' := hr.le_apply_add_sub (k := k + 1) (by omega) hs hsm
  have hm₁ : (m : ℝ) < (k + 1 : ℕ) + s := by exact_mod_cast h₁
  rcases le_or_gt (k + s) m with h₂ | h₂
  · -- On the antidiagonal `k + 1 + s = m + 1`.
    rw [bhLikeRatio_of_le h₂]
    rcases Nat.eq_zero_or_pos k with rfl | hk₀
    · rw [← bhLikeRatio_of_lt h₁]
      simpa using hr.bhLikeRatio_nonneg (k := 1) (by omega) hs hsm
    rw [hr.apply_eq_self hs (by omega) (by omega)]
    have hkm : (k : ℝ) + s = m := by exact_mod_cast (by omega : k + s = m)
    push_cast
    rw [show (k : ℝ) + 1 + s - m = 1 by linarith, one_mul, one_mul]
    gcongr
    linarith
  -- Above the antidiagonal, the growth bound of the horizons.
  rw [bhLikeRatio_of_lt h₂]
  have hR := hr.le_apply_add_sub (k := k) hk.le hs hsm
  have hm₂ : (m : ℝ) < k + s := by exact_mod_cast h₂
  have hb' := hr.cast_apply_succ_mul_le hk hs hsm h₂
  push_cast
  rw [div_le_div_iff₀ (mul_pos (by linarith) hs₀) (mul_pos (by linarith) hs₀)]
  nlinarith

/-- **The thresholds are nondecreasing in `k`** up to `m` [Goe26, Lemma 7]. -/
theorem bhLikeRatio_mono (hkl : k ≤ l) (hl : l ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) :
    bhLikeRatio m r k s ≤ bhLikeRatio m r l s := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l hkl ih => exact (ih (by omega)).trans (hr.bhLikeRatio_le_succ (by omega) hs hsm)

/-- **The horizon inequality** [Goe26, Lemma 10], in arithmetic form: if `k + s ≤ m + t` and
`k ≤ j ≤ r k s`, then `(t + j - k) * s * bhLikeRatio m r k s ≤ t * j`. In
`mem_eClosure_fdp_bhLikeECollection`, `t` is the number of p-values of a set `S` of `s`
hypotheses below the threshold `a k s`, and `j` is the number of rejections. -/
theorem mul_bhLikeRatio_le (hk : k ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m) (hkj : k ≤ j)
    (hj : j ≤ r k s) (hkt : k + s ≤ m + t) :
    ((t : ℝ) + j - k) * s * bhLikeRatio m r k s ≤ t * j := by
  have hs₀ : (0 : ℝ) < s := by exact_mod_cast hs
  rcases le_or_gt (k + s) m with h | h
  · -- Below the antidiagonal the horizon is `k`, so `j = k`.
    have hjk : j = k := le_antisymm (hj.trans_eq (hr.apply_eq_self hs (by omega) (by omega))) hkj
    subst hjk
    rw [bhLikeRatio_of_le h]
    field_simp
    exact le_of_eq (by ring)
  rw [bhLikeRatio_of_lt h]
  have hR := hr.le_apply_add_sub hk hs hsm
  have hm : (m : ℝ) < k + s := by exact_mod_cast h
  have hkj' : (k : ℝ) ≤ j := by exact_mod_cast hkj
  have hj' : (j : ℝ) ≤ r k s := by exact_mod_cast hj
  have hkt' : (k : ℝ) + s ≤ m + t := by exact_mod_cast hkt
  have hsm' : (s : ℝ) ≤ m := by exact_mod_cast hsm
  have ht₀ : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hD : (0 : ℝ) < r k s + s - m := by linarith
  rw [show ((t : ℝ) + j - k) * s * ((k + s - m) * r k s / ((r k s + s - m) * s)) =
    ((t : ℝ) + j - k) * ((k + s - m) * r k s) / (r k s + s - m) by field_simp, div_le_iff₀ hD]
  -- `t * j * (r + s - m) - (t + j - k) * (k + s - m) * r = t (m - s) (r - j) + (j - k) r (t - c)`.
  nlinarith [mul_nonneg (mul_nonneg ht₀ (by linarith : (0 : ℝ) ≤ m - s))
    (by linarith : (0 : ℝ) ≤ r k s - j), mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ j - k)
    (by linarith : (0 : ℝ) ≤ r k s)) (by linarith : (0 : ℝ) ≤ t - (k + s - m))]

/-- **The horizon inequality** [Goe26, Lemma 10], in quotient form: under the hypotheses of
`mul_bhLikeRatio_le`, with `k ≥ 1`, if `n + k ≤ t + j` then
`n / j ≤ t / (s * bhLikeRatio m r k s)`. In `mem_eClosure_fdp_bhLikeECollection`, `n` is the
number of rejections in a set `S` of `s` hypotheses, so that the left side is the false discovery
proportion for `S`, and the right side is `α` times the statistic of `S`. -/
theorem div_le_div_mul_bhLikeRatio (hk₀ : 1 ≤ k) (hk : k ≤ m) (hs : 1 ≤ s) (hsm : s ≤ m)
    (hkj : k ≤ j) (hj : j ≤ r k s) (hkt : k + s ≤ m + t) {n : ℕ} (hn : n + k ≤ t + j) :
    (n : ℝ) / j ≤ t / (s * bhLikeRatio m r k s) := by
  have hθ := hr.bhLikeRatio_pos hk₀ hk hs hsm
  have hs₀ : (0 : ℝ) < s := by exact_mod_cast hs
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast (hk₀.trans hkj)
  rw [div_le_div_iff₀ hj₀ (mul_pos hs₀ hθ)]
  have : ((n + k : ℕ) : ℝ) ≤ (t + j : ℕ) := by exact_mod_cast hn
  push_cast at this
  nlinarith [hr.mul_bhLikeRatio_le hk hs hsm hkj hj hkt, mul_pos hs₀ hθ]

end IsBHLikeHorizon

/-! ### The BH-like procedure -/

/-- **The thresholds of a BH-like method** [Goe26, (4)]: `a k s = α * bhLikeRatio m r k s`, the
value against which the `k`-th smallest of `m` p-values is compared at step `s`. -/
noncomputable def bhLikeThreshold (m : ℕ) (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞) (k s : ℕ) : ℝ≥0∞ :=
  α * ENNReal.ofReal (bhLikeRatio m r k s)

theorem bhLikeThreshold_def (m : ℕ) (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞) (k s : ℕ) :
    bhLikeThreshold m r α k s = α * ENNReal.ofReal (bhLikeRatio m r k s) :=
  (rfl)

section Procedure

variable {ι : Type*} [Fintype ι] {r : ℕ → ℕ → ℕ} {α : ℝ≥0∞} {x y : ι → ℝ≥0∞} {k s : ℕ}

/-- **The number of rejections of a BH-like method** [Goe26, (5)] with horizons `r` at level `α`,
at the p-values `x` of the `m = Fintype.card ι` hypotheses: the largest `k ≤ m` such that, at
every step `1 ≤ s ≤ m`, some `k' ≤ k` whose p-value `x_(k')` is below its threshold `a k' s` has a
horizon `r k' s ≥ k`. The condition `x_(k') ≤ a k' s` on the `k'`-th smallest p-value is written
without order statistics, as `k' ≤ #{i | x i ≤ a k' s}`. The method rejects the `k` hypotheses
with the smallest p-values. -/
noncomputable def bhLikeCount (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞) (x : ι → ℝ≥0∞) : ℕ :=
  @Nat.findGreatest (fun k : ℕ ↦ ∀ s ∈ Icc 1 (Fintype.card ι), ∃ k' ∈ Iic k,
    k' ≤ #{i | x i ≤ bhLikeThreshold (Fintype.card ι) r α k' s} ∧ k ≤ r k' s)
    (fun _ ↦ decidableDforallFinset) (Fintype.card ι)

/-- **The index `k_s`** of a BH-like method at step `s` [Goe26, (8)]: the largest
`k ≤ bhLikeCount r α x` whose p-value `x_(k)` is below its threshold `a k s`. -/
noncomputable def bhLikeIndex (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞) (x : ι → ℝ≥0∞) (s : ℕ) : ℕ :=
  Nat.findGreatest (fun k : ℕ ↦ k ≤ bhLikeCount r α x ∧
    k ≤ #{i | x i ≤ bhLikeThreshold (Fintype.card ι) r α k s}) (Fintype.card ι)

theorem bhLikeCount_le (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞) (x : ι → ℝ≥0∞) :
    bhLikeCount r α x ≤ Fintype.card ι := by
  unfold bhLikeCount
  exact Nat.findGreatest_le _

/-- The defining property of `bhLikeCount r α x`, which holds since it holds at `0`. -/
private lemma bhLikeCount_spec (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞) (x : ι → ℝ≥0∞) :
    ∀ s ∈ Icc 1 (Fintype.card ι), ∃ k' ∈ Iic (bhLikeCount r α x),
      k' ≤ #{i | x i ≤ bhLikeThreshold (Fintype.card ι) r α k' s} ∧ bhLikeCount r α x ≤ r k' s :=
  Nat.findGreatest_spec (P := fun k : ℕ ↦ ∀ s ∈ Icc 1 (Fintype.card ι), ∃ k' ∈ Iic k,
    k' ≤ #{i | x i ≤ bhLikeThreshold (Fintype.card ι) r α k' s} ∧ k ≤ r k' s) (m := 0)
    (Nat.zero_le _) fun _ _ ↦ ⟨0, mem_Iic.2 le_rfl, Nat.zero_le _, Nat.zero_le _⟩

/-- At every step `s`, some `k' ≤ bhLikeCount r α x` below its threshold has a horizon at least
`bhLikeCount r α x`. -/
theorem exists_le_bhLikeCount (hs : 1 ≤ s) (hsm : s ≤ Fintype.card ι) :
    ∃ k' ≤ bhLikeCount r α x, k' ≤ #{i | x i ≤ bhLikeThreshold (Fintype.card ι) r α k' s} ∧
      bhLikeCount r α x ≤ r k' s := by
  obtain ⟨k', hk', h⟩ := bhLikeCount_spec r α x s (mem_Icc.2 ⟨hs, hsm⟩)
  exact ⟨k', mem_Iic.1 hk', h⟩

/-- Every `k ≤ m` such that, at every step `s`, some `k' ≤ k` below its threshold has a horizon at
least `k`, is at most `bhLikeCount r α x`. -/
theorem le_bhLikeCount (hk : k ≤ Fintype.card ι)
    (h : ∀ s, 1 ≤ s → s ≤ Fintype.card ι → ∃ k' ≤ k,
      k' ≤ #{i | x i ≤ bhLikeThreshold (Fintype.card ι) r α k' s} ∧ k ≤ r k' s) :
    k ≤ bhLikeCount r α x := by
  unfold bhLikeCount
  refine Nat.le_findGreatest hk fun s hs ↦ ?_
  obtain ⟨k', hk', h⟩ := h s (mem_Icc.1 hs).1 (mem_Icc.1 hs).2
  exact ⟨k', mem_Iic.2 hk', h⟩

/-- **The number of rejections is nonincreasing in the p-values** [Goe26, proof of Lemma 6]. -/
theorem bhLikeCount_anti (hxy : x ≤ y) : bhLikeCount r α y ≤ bhLikeCount r α x :=
  Nat.findGreatest_mono_left (fun k hk s hs ↦ by
    obtain ⟨k', hk', hk'N, hkr⟩ := hk s hs
    exact ⟨k', hk', hk'N.trans (card_le_card (monotone_filter_right _ fun i _ h ↦
      (hxy i).trans h)), hkr⟩) _

/-- The defining property of `bhLikeIndex r α x s`, which holds since it holds at `0`. -/
private lemma bhLikeIndex_spec (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞) (x : ι → ℝ≥0∞) (s : ℕ) :
    bhLikeIndex r α x s ≤ bhLikeCount r α x ∧
      bhLikeIndex r α x s ≤
        #{i | x i ≤ bhLikeThreshold (Fintype.card ι) r α (bhLikeIndex r α x s) s} :=
  Nat.findGreatest_spec (P := fun k : ℕ ↦ k ≤ bhLikeCount r α x ∧
    k ≤ #{i | x i ≤ bhLikeThreshold (Fintype.card ι) r α k s}) (m := 0) (Nat.zero_le _)
    ⟨Nat.zero_le _, Nat.zero_le _⟩

theorem bhLikeIndex_le_bhLikeCount (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞) (x : ι → ℝ≥0∞) (s : ℕ) :
    bhLikeIndex r α x s ≤ bhLikeCount r α x :=
  (bhLikeIndex_spec r α x s).1

/-- The p-value of rank `k_s` is below its threshold. -/
theorem bhLikeIndex_le_card_filter (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞) (x : ι → ℝ≥0∞) (s : ℕ) :
    bhLikeIndex r α x s ≤
      #{i | x i ≤ bhLikeThreshold (Fintype.card ι) r α (bhLikeIndex r α x s) s} :=
  (bhLikeIndex_spec r α x s).2

theorem le_bhLikeIndex (hk : k ≤ bhLikeCount r α x)
    (hkN : k ≤ #{i | x i ≤ bhLikeThreshold (Fintype.card ι) r α k s}) :
    k ≤ bhLikeIndex r α x s :=
  Nat.le_findGreatest (hk.trans (bhLikeCount_le r α x)) ⟨hk, hkN⟩

/-- **The index `k_s` is nonincreasing in the p-values** [Goe26, Lemma 6]. -/
theorem bhLikeIndex_anti (hxy : x ≤ y) (s : ℕ) : bhLikeIndex r α y s ≤ bhLikeIndex r α x s :=
  Nat.findGreatest_mono_left (fun _ hk ↦
    ⟨hk.1.trans (bhLikeCount_anti hxy),
      hk.2.trans (card_le_card (monotone_filter_right _ fun i _ h ↦ (hxy i).trans h))⟩) _

/-- The number of p-values below a threshold is measurable in the p-values. -/
private lemma measurable_card_filter_le (a : ℝ≥0∞) :
    Measurable fun x : ι → ℝ≥0∞ ↦ #{i | x i ≤ a} :=
  measurable_card_filter fun i ↦ measurableSet_setOfPred.1 (measurable_pi_apply i measurableSet_Iic)

theorem measurable_bhLikeCount (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞) :
    Measurable (bhLikeCount (ι := ι) r α) := by
  unfold bhLikeCount
  refine measurable_findGreatest fun _ _ ↦ measurableSet_setOfPred.2 ?_
  refine Measurable.forall fun s ↦ Measurable.imp measurable_const (Measurable.exists fun k' ↦
    measurable_const.and (Measurable.and ?_ measurable_const))
  exact measurableSet_setOfPred.1 (measurableSet_le measurable_const
    (measurable_card_filter_le _))

theorem measurable_bhLikeIndex (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞) (s : ℕ) :
    Measurable fun x : ι → ℝ≥0∞ ↦ bhLikeIndex r α x s := by
  unfold bhLikeIndex
  refine measurable_findGreatest fun k _ ↦ measurableSet_setOfPred.2 (Measurable.and ?_ ?_)
  · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const
      (measurable_bhLikeCount r α))
  · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const
      (measurable_card_filter_le _))

/-- **The number of rejections is at most the horizon of the index** [Goe26, proof of
Lemma 11]: at every step `s`, `bhLikeIndex r α x s ≤ bhLikeCount r α x ≤ r (bhLikeIndex r α x s) s`,
the first inequality being `bhLikeIndex_le_bhLikeCount`. -/
theorem IsBHLikeHorizon.bhLikeCount_le_apply_bhLikeIndex (hr : IsBHLikeHorizon (Fintype.card ι) r)
    (hs : 1 ≤ s) (hsm : s ≤ Fintype.card ι) :
    bhLikeCount r α x ≤ r (bhLikeIndex r α x s) s := by
  obtain ⟨k', hk'c, hk'N, hck'⟩ := exists_le_bhLikeCount (r := r) (α := α) (x := x) hs hsm
  exact hck'.trans (hr.apply_mono (le_bhLikeIndex hk'c hk'N)
    ((bhLikeIndex_le_bhLikeCount r α x s).trans (bhLikeCount_le r α x)) hs hsm)

/-- When the method rejects some hypothesis, the index `k_s` is positive at every step. -/
theorem IsBHLikeHorizon.one_le_bhLikeIndex (hr : IsBHLikeHorizon (Fintype.card ι) r)
    (hs : 1 ≤ s) (hsm : s ≤ Fintype.card ι) (hpos : 0 < bhLikeCount r α x) :
    1 ≤ bhLikeIndex r α x s := by
  by_contra h
  have := hr.bhLikeCount_le_apply_bhLikeIndex (α := α) (x := x) hs hsm
  rw [show bhLikeIndex r α x s = 0 by omega, hr.apply_zero hs hsm] at this
  omega

/-- The counting step of [Goe26, Lemma 11]: let `R` be a set of hypotheses with the smallest
values of `x`, with `k ≤ #R`, and let at least `k` values be at most `a`. Then, with `u` the number
of hypotheses of `S` with values at most `a`, `k + #S ≤ m + u` and `#(R ∩ S) + k ≤ u + #R`: some
`k` hypotheses of `R` have values at most `a`, and `R ∩ S` has at most `#R - k` others. -/
private lemma card_add_le_and_card_inter_add_le [DecidableEq ι] {R S : Finset ι} {a : ℝ≥0∞}
    (hRx : ∀ i ∈ R, ∀ j ∉ R, x i ≤ x j) (hkR : k ≤ #R) (hka : k ≤ #{i | x i ≤ a}) :
    k + #S ≤ Fintype.card ι + #{i ∈ S | x i ≤ a} ∧ #(R ∩ S) + k ≤ #{i ∈ S | x i ≤ a} + #R := by
  set K : Finset ι := {i | x i ≤ a}
  -- `R` and `K` are both lower sets of the values, so one contains the other.
  obtain ⟨T, hTRK, hT⟩ : ∃ T ⊆ R ∩ K, #T = k := by
    refine exists_subset_card_eq ?_
    by_cases hRK : R ⊆ K
    · rwa [inter_eq_left.2 hRK]
    · obtain ⟨i, hiR, hiK⟩ := not_subset.1 hRK
      have hKR : K ⊆ R := fun j hjK ↦ by
        by_contra hjR
        exact hiK (mem_filter.2 ⟨mem_univ _, (hRx i hiR j hjR).trans (mem_filter.1 hjK).2⟩)
      rwa [inter_eq_right.2 hKR]
  have hTR : T ⊆ R := fun i hi ↦ (mem_inter.1 (hTRK hi)).1
  have hTS : #(T ∩ S) ≤ #{i ∈ S | x i ≤ a} := card_le_card fun i hi ↦
    mem_filter.2 ⟨(mem_inter.1 hi).2, (mem_filter.1 (mem_inter.1 (hTRK (mem_inter.1 hi).1)).2).2⟩
  refine ⟨?_, ?_⟩
  · have := card_union_add_card_inter T S
    have := card_le_univ (T ∪ S)
    omega
  · have h₁ : R ∩ S ⊆ (T ∩ S) ∪ (R \ T) := fun i hi ↦ by
      by_cases hiT : i ∈ T
      · exact mem_union_left _ (mem_inter.2 ⟨hiT, (mem_inter.1 hi).2⟩)
      · exact mem_union_right _ (mem_sdiff.2 ⟨(mem_inter.1 hi).1, hiT⟩)
    have h₂ := (card_le_card h₁).trans (card_union_le _ _)
    rw [card_sdiff_of_subset hTR, hT] at h₂
    omega

end Procedure

/-! ### The e-collection and the e-closure -/

section ECollection

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Fintype ι] {r : ℕ → ℕ → ℕ} {α : ℝ≥0∞}
  {p : ι → Ω → ℝ≥0∞}

/-- **The e-collection of a BH-like method** [Goe26, (9)]: the threshold statistics
(`ProbabilityTheory.thresholdECollection`) of the p-values against the thresholds
`a (k_s p) s` at the index `k_s` of the size `s` of the set. The statistic of a set `S` is the
average over `i ∈ S` of `𝟙{p i ≤ a} / a`, with `a = a (k_{#S}) #S`. It agrees with [Goe26, (9)]
except where `k_{#S} = 0` and some p-value of `S` is `0`, where it is `∞` instead of `0`, which
only enlarges the statistic, and at the empty set, where it is `0` instead of `1`, as the
convention `e ∅ = 0` of `ProbabilityTheory.IsECollection` requires; this does not change the
e-closure for the false discovery proportion, since `fdp ∅ R = 0`. -/
noncomputable def bhLikeECollection (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞) (p : ι → Ω → ℝ≥0∞) :
    Finset ι → Ω → ℝ≥0∞ :=
  thresholdECollection p fun s x ↦ bhLikeThreshold (Fintype.card ι) r α (bhLikeIndex r α x s) s

theorem bhLikeECollection_def (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞) (p : ι → Ω → ℝ≥0∞) :
    bhLikeECollection r α p = thresholdECollection p fun s x ↦
      bhLikeThreshold (Fintype.card ι) r α (bhLikeIndex r α x s) s :=
  (rfl)

/-- **The statistic of a set** of the e-collection of a BH-like method: with
`a = a (k_{#S}) #S` the threshold at the index of the size of `S`, it is `#S⁻¹ * (u * a⁻¹)`, with
`u` the number of hypotheses of `S` whose p-values are at most `a`. -/
theorem bhLikeECollection_apply (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞) (p : ι → Ω → ℝ≥0∞) (S : Finset ι)
    (ω : Ω) : bhLikeECollection r α p S ω = (#S : ℝ≥0∞)⁻¹ *
      (#{i ∈ S | p i ω ≤ bhLikeThreshold (Fintype.card ι) r α (bhLikeIndex r α (p · ω) #S) #S} *
        (bhLikeThreshold (Fintype.card ι) r α (bhLikeIndex r α (p · ω) #S) #S)⁻¹) := by
  rw [bhLikeECollection_def, thresholdECollection_def, ← nsmul_eq_mul, ← sum_const, sum_filter]
  exact congrArg _ (sum_congr rfl fun i _ ↦ by simp [Set.indicator_apply])

theorem measurable_bhLikeThreshold_bhLikeIndex (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞) (s : ℕ) :
    Measurable fun x : ι → ℝ≥0∞ ↦
      bhLikeThreshold (Fintype.card ι) r α (bhLikeIndex r α x s) s :=
  (measurable_from_nat (f := fun k ↦ bhLikeThreshold (Fintype.card ι) r α k s)).comp
    (measurable_bhLikeIndex r α s)

/-- **The threshold at the index `k_s` is nonincreasing in the p-values** [Goe26, proof of
Theorem 8], by Lemmas 6 and 7. -/
theorem IsBHLikeHorizon.antitone_bhLikeThreshold_bhLikeIndex
    (hr : IsBHLikeHorizon (Fintype.card ι) r) (α : ℝ≥0∞) (hsm : s ≤ Fintype.card ι) :
    Antitone fun x : ι → ℝ≥0∞ ↦ bhLikeThreshold (Fintype.card ι) r α (bhLikeIndex r α x s) s := by
  intro x y hxy
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [bhLikeThreshold_def, bhLikeRatio]
  simp only [bhLikeThreshold_def]
  gcongr
  exact hr.bhLikeRatio_mono (bhLikeIndex_anti hxy s)
    ((bhLikeIndex_le_bhLikeCount r α x s).trans (bhLikeCount_le r α x)) hs hsm

theorem measurable_bhLikeECollection (hp : ∀ i, Measurable (p i)) (S : Finset ι) :
    Measurable (bhLikeECollection r α p S) :=
  measurable_thresholdECollection hp (measurable_bhLikeThreshold_bhLikeIndex r α) S

/-- **The e-collection of a BH-like method is an e-collection under PRDS** [Goe26, Theorem 8]:
if each `p i` is a p-variable for `H i` and the p-values are PRDS on the true nulls under every
probability measure, then `bhLikeECollection r α p` is an e-collection, for every level `α`. -/
theorem IsBHLikeHorizon.isECollection_bhLikeECollection (hr : IsBHLikeHorizon (Fintype.card ι) r)
    {H : ι → Set (Measure Ω)} (hp : ∀ i, IsPVar (p i) (H i))
    (hPRDS : ∀ (P : Measure Ω) [IsProbabilityMeasure P], IsPRDS p P (trueNulls H P)) (α : ℝ≥0∞) :
    IsECollection (bhLikeECollection r α p) H :=
  isECollection_thresholdECollection hp (fun _ hs ↦ hr.antitone_bhLikeThreshold_bhLikeIndex α hs)
    (measurable_bhLikeThreshold_bhLikeIndex r α) hPRDS

/-- The last step of [Goe26, Lemma 11], back in `ℝ≥0∞`: for `α ∉ {0, ∞}`, `θ > 0` and `s ≥ 1`,
the real quotient `u / (s * θ)` is `α * (s⁻¹ * (u * (α * θ)⁻¹))`. -/
private lemma ofReal_div_mul_eq_mul_inv_mul {α : ℝ≥0∞} (hα₀ : α ≠ 0) (hα : α ≠ ∞) {θ : ℝ}
    (hθ : 0 < θ) {s : ℕ} (hs : 1 ≤ s) (u : ℕ) :
    ENNReal.ofReal (u / (s * θ)) = α * ((s : ℝ≥0∞)⁻¹ * (u * (α * ENNReal.ofReal θ)⁻¹)) := by
  have hs₀ : (0 : ℝ) < s := by exact_mod_cast hs
  rw [ENNReal.ofReal_div_of_pos (mul_pos hs₀ hθ), ENNReal.ofReal_mul hs₀.le, ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, ENNReal.mul_inv (Or.inl hα₀) (Or.inl hα), ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inr (ENNReal.ofReal_pos.2 hθ).ne')]
  calc _ = α * α⁻¹ * ((s : ℝ≥0∞)⁻¹ * (ENNReal.ofReal θ)⁻¹ * u) := by
        rw [ENNReal.mul_inv_cancel hα₀ hα, one_mul]
    _ = _ := by ring

/-- **The rejections of a BH-like method lie in the e-closure of its e-collection** [Goe26,
Lemma 11]: for a level `α ∉ {0, ∞}`, every set `R` of `bhLikeCount r α (p · ω)` hypotheses with
the smallest p-values, ties broken in any way, has `fdp S R ≤ α * e S` for every set `S`. -/
theorem IsBHLikeHorizon.mem_eClosure_fdp_bhLikeECollection [DecidableEq ι]
    (hr : IsBHLikeHorizon (Fintype.card ι) r) (hα₀ : α ≠ 0) (hα : α ≠ ∞) {ω : Ω} {R : Finset ι}
    (hR : #R = bhLikeCount r α (p · ω)) (hRp : ∀ i ∈ R, ∀ j ∉ R, p i ω ≤ p j ω) :
    R ∈ eClosure fdp α (bhLikeECollection r α p) ω := by
  refine mem_eClosure.2 fun S ↦ ?_
  set m := Fintype.card ι
  set x : ι → ℝ≥0∞ := (p · ω)
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [fdp_empty_left]
  set c := bhLikeCount r α x
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · rw [card_eq_zero.1 (hR.trans h0), fdp_empty_right]
    exact zero_le
  have hs : 1 ≤ #S := hS.card_pos
  have hsm : #S ≤ m := card_le_univ S
  -- The index `k` of the step `#S`, its threshold `A = α * θ`, and the number `u` of p-values of
  -- `S` below it, with `k ≤ c ≤ r k #S`.
  set k := bhLikeIndex r α x #S
  set θ := bhLikeRatio m r k #S
  set A := bhLikeThreshold m r α k #S
  set u := #{i ∈ S | x i ≤ A}
  have hkc : k ≤ c := bhLikeIndex_le_bhLikeCount r α x #S
  have hkm : k ≤ m := hkc.trans (bhLikeCount_le r α x)
  obtain ⟨hku, hRS⟩ := card_add_le_and_card_inter_add_le (S := S) hRp (hR ▸ hkc)
    (bhLikeIndex_le_card_filter r α x #S)
  rw [hR] at hRS
  -- The horizon inequality, in `ℝ`, gives `#(R ∩ S) / c ≤ u / (#S * θ)`.
  have hθ := hr.bhLikeRatio_pos (hr.one_le_bhLikeIndex hs hsm hpos) hkm hs hsm
  have hreal := hr.div_le_div_mul_bhLikeRatio (hr.one_le_bhLikeIndex hs hsm hpos) hkm hs hsm hkc
    (hr.bhLikeCount_le_apply_bhLikeIndex hs hsm) hku hRS
  have hc₀ : (0 : ℝ) < c := by exact_mod_cast hpos
  -- Back in `ℝ≥0∞`.
  calc fdp S R = ENNReal.ofReal (((#(R ∩ S) : ℕ) : ℝ) / c) := by
        rw [fdp_def, hR, max_eq_left (by exact_mod_cast hpos), ENNReal.ofReal_div_of_pos hc₀,
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (u / (#S * θ)) := ENNReal.ofReal_le_ofReal hreal
    _ = α * ((#S : ℝ≥0∞)⁻¹ * (u * A⁻¹)) := ofReal_div_mul_eq_mul_inv_mul hα₀ hα hθ hs u
    _ = α * bhLikeECollection r α p S ω := by
        rw [bhLikeECollection_apply]

/-- **FDR of a BH-like method, with the level retained when the condition fails** [Goe26,
Theorem 13]: for a level `α ∉ {0, ∞}`, every measure `P` and every set `N` of hypotheses, the
false discovery proportion for `N` of any choice `R ω` of `bhLikeCount r α (p · ω)` hypotheses
with the smallest p-values has expectation at most `α` times the expectation of the statistic
`bhLikeECollection r α p N`. With `N` the true nulls, the false discovery rate is at most `γ * α`
when this expectation is at most `γ`, with no assumption on the dependence of the p-values. The
choice `R` need not be measurable. -/
theorem IsBHLikeHorizon.lintegral_fdp_le_mul_lintegral_bhLikeECollection [DecidableEq ι]
    (hr : IsBHLikeHorizon (Fintype.card ι) r) (hα₀ : α ≠ 0) (hα : α ≠ ∞)
    (hp : ∀ i, Measurable (p i)) {R : Ω → Finset ι} (hR : ∀ ω, #(R ω) = bhLikeCount r α (p · ω))
    (hRp : ∀ ω, ∀ i ∈ R ω, ∀ j ∉ R ω, p i ω ≤ p j ω) (N : Finset ι) (P : Measure Ω) :
    ∫⁻ ω, fdp N (R ω) ∂P ≤ α * ∫⁻ ω, bhLikeECollection r α p N ω ∂P :=
  (lintegral_mono fun ω ↦ le_biSup (fun R ↦ fdp N R)
    (hr.mem_eClosure_fdp_bhLikeECollection hα₀ hα (hR ω) (hRp ω))).trans
    (lintegral_biSup_eClosure_le_mul_lintegral fdp α
      (measurable_bhLikeECollection hp N).aemeasurable)

/-- **BH-like methods control the false discovery rate under PRDS** [Goe26, Theorem 12, with
Theorem 8]: if each `p i` is a p-variable for `H i` and the p-values are PRDS on the true nulls
under every probability measure, then for every level `α ≠ 0`, any choice `R ω` of
`bhLikeCount r α (p · ω)` hypotheses with the smallest p-values has false discovery rate at most
`α`. -/
theorem IsBHLikeHorizon.lintegral_fdp_le [DecidableEq ι] (hr : IsBHLikeHorizon (Fintype.card ι) r)
    {H : ι → Set (Measure Ω)} (hp : ∀ i, IsPVar (p i) (H i))
    (hPRDS : ∀ (P : Measure Ω) [IsProbabilityMeasure P], IsPRDS p P (trueNulls H P))
    (hα₀ : α ≠ 0) {R : Ω → Finset ι} (hR : ∀ ω, #(R ω) = bhLikeCount r α (p · ω))
    (hRp : ∀ ω, ∀ i ∈ R ω, ∀ j ∉ R ω, p i ω ≤ p j ω) (P : Measure Ω) [IsProbabilityMeasure P] :
    ∫⁻ ω, fdp (trueNulls H P) (R ω) ∂P ≤ α := by
  rcases eq_or_ne α ∞ with rfl | hα
  · exact le_top
  exact (hr.lintegral_fdp_le_mul_lintegral_bhLikeECollection hα₀ hα (fun i ↦ (hp i).measurable)
    hR hRp _ P).trans (mul_le_of_le_one_right' ((hr.isECollection_bhLikeECollection hp hPRDS
      α).lintegral_le_one P))

end ECollection

/-- **A BH-like method can always reject its number of hypotheses**: some set of
`bhLikeCount r α x` hypotheses has p-values below those of all the other hypotheses. -/
theorem exists_card_eq_bhLikeCount {ι : Type*} [Fintype ι] (r : ℕ → ℕ → ℕ) (α : ℝ≥0∞)
    (x : ι → ℝ≥0∞) : ∃ R : Finset ι, #R = bhLikeCount r α x ∧ ∀ i ∈ R, ∀ j ∉ R, x i ≤ x j := by
  classical
  obtain ⟨R, -, hR, hRx⟩ := exists_subset_card_eq_forall_le (fun i ↦ OrderDual.toDual (x i))
    (s := univ) (bhLikeCount_le r α x)
  exact ⟨R, hR, fun i hi j hj ↦ hRx i hi j (mem_sdiff.2 ⟨mem_univ j, hj⟩)⟩

/-! ### Comparison with BH -/

section BH

variable {ι : Type*} [Fintype ι] {r : ℕ → ℕ → ℕ} {α : ℝ≥0∞} {x : ι → ℝ≥0∞} {k s : ℕ}

/-- **The thresholds of a BH-like method are at least those of BH** under the criterion of
[Goe26, Proposition 16], `r k s * (m - k) ≤ k * s` above the antidiagonal `k + s = m + 1` and for
`s < m`, that is `r k s ≤ k * s / (m - k)`: then `k / m ≤ a k s / α`. -/
theorem IsBHLikeHorizon.div_le_bhLikeRatio {m : ℕ} (hr : IsBHLikeHorizon m r)
    (hBH : ∀ k s, m + 1 < k + s → s < m → r k s * (m - k) ≤ k * s) (hk : k ≤ m) (hs : 1 ≤ s)
    (hsm : s ≤ m) : (k : ℝ) / m ≤ bhLikeRatio m r k s := by
  have hs₀ : (0 : ℝ) < s := by exact_mod_cast hs
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast (hs.trans hsm)
  have hsm' : (s : ℝ) ≤ m := by exact_mod_cast hsm
  rcases le_or_gt (k + s) m with h | h
  · rw [bhLikeRatio_of_le h]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hs₀ hsm'
  rw [bhLikeRatio_of_lt h]
  have hR := hr.le_apply_add_sub hk hs hsm
  have hm : (m : ℝ) < k + s := by exact_mod_cast h
  have hkm : (k : ℝ) ≤ m := by exact_mod_cast hk
  -- The criterion, multiplied by `m - s`, in `ℝ`.
  have hcrit : (r k s : ℝ) * (m - k) * (m - s) ≤ k * s * (m - s) := by
    rcases eq_or_lt_of_le hsm with rfl | hsm₁
    · simp
    rcases le_or_gt (k + s) (m + 1) with h₁ | h₁
    · rw [hr.apply_eq_self hs h₁ (fun _ ↦ hsm₁)]
      have : (m : ℝ) - k ≤ s := by
        have : m ≤ k + s := h.le
        have : (m : ℝ) ≤ k + s := by exact_mod_cast this
        linarith
      have : (0 : ℝ) ≤ m - s := by linarith
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      gcongr
    · have := (Nat.cast_le (α := ℝ)).2 (hBH k s h₁ hsm₁)
      push_cast [Nat.cast_sub hk] at this
      exact mul_le_mul_of_nonneg_right this (by linarith)
  rw [div_le_div_iff₀ hm₀ (mul_pos (by linarith) hs₀)]
  nlinarith

/-- **A BH-like method rejects at least as many hypotheses as BH** under the criterion of [Goe26,
Proposition 16]: the number of rejections of BH, e-BH applied to `x⁻¹`, is at most
`bhLikeCount r α x`. -/
theorem IsBHLikeHorizon.card_eBH_inv_le_bhLikeCount (hr : IsBHLikeHorizon (Fintype.card ι) r)
    (hBH : ∀ k s, Fintype.card ι + 1 < k + s → s < Fintype.card ι →
      r k s * (Fintype.card ι - k) ≤ k * s) (α : ℝ≥0∞) (x : ι → ℝ≥0∞) :
    #(eBH (fun i ↦ (x i)⁻¹) α) ≤ bhLikeCount r α x := by
  set b := #(eBH (fun i ↦ (x i)⁻¹) α)
  have hbm : b ≤ Fintype.card ι := card_le_univ _
  refine le_bhLikeCount hbm fun s hs hsm ↦ ⟨b, le_rfl, card_le_card fun i hi ↦ ?_,
    hr.le_apply hbm hs hsm⟩
  have : Nonempty ι := ⟨i⟩
  have hm₀ : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine mem_filter.2 ⟨mem_univ i, ?_⟩
  -- A rejected p-value is at most `α * b / m`, which is at most the threshold `a b s`.
  have hle := isSelfConsistent_eBH.card_mul_le hi
  calc x i ≤ α * b / Fintype.card ι := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hm₀.ne'))
          (Or.inl (ENNReal.natCast_ne_top _)), mul_comm]
        exact hle
    _ = α * ENNReal.ofReal ((b : ℝ) / Fintype.card ι) := by
        rw [ENNReal.ofReal_div_of_pos hm₀, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
          mul_div_assoc]
    _ ≤ bhLikeThreshold (Fintype.card ι) r α b s := by
        rw [bhLikeThreshold_def]
        gcongr
        exact hr.div_le_bhLikeRatio hBH hbm hs hsm

/-- **A BH-like method rejects every hypothesis that BH rejects** under the criterion of [Goe26,
Proposition 16]: every set `R` of `bhLikeCount r α x` hypotheses with the smallest p-values
contains the rejection set of BH, e-BH applied to `x⁻¹`. -/
theorem IsBHLikeHorizon.eBH_inv_subset (hr : IsBHLikeHorizon (Fintype.card ι) r)
    (hBH : ∀ k s, Fintype.card ι + 1 < k + s → s < Fintype.card ι →
      r k s * (Fintype.card ι - k) ≤ k * s) {R : Finset ι} (hR : #R = bhLikeCount r α x)
    (hRx : ∀ i ∈ R, ∀ j ∉ R, x i ≤ x j) : eBH (fun i ↦ (x i)⁻¹) α ⊆ R := by
  intro j hj
  by_contra hjR
  -- Otherwise `R` is strictly contained in the BH rejection set, which is a lower set.
  have hsub : R ⊆ eBH (fun i ↦ (x i)⁻¹) α := fun i hi ↦ by
    refine mem_eBH_iff_le_mul_card.2 ((mem_eBH_iff_le_mul_card.1 hj).trans ?_)
    gcongr
    exact hRx i hi j hjR
  have := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun h ↦ hjR (h ▸ hj)⟩)
  have := hr.card_eBH_inv_le_bhLikeCount hBH α x
  omega

end BH

/-! ### Closed BH -/

/-- **The horizons of closed BH** [Goe26, §5] for `m` hypotheses: `r k s = k` when
`k + s ≤ m + 1`, except `r 1 m = m`; `r k m = m` for `k ≥ 1`; and otherwise, recursively in `k`,
the largest horizon `≤ m` allowed by the growth bound of [Goe26, (3)] and by the criterion
`r k s * (m - k) ≤ k * s` of [Goe26, Proposition 16], that is
`min (⌊b k s⌋, ⌊k * s / (m - k)⌋)`, both conditions multiplied out in `ℕ`. -/
def closedBHHorizon (m : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, s =>
    if k + 1 + s ≤ m + 1 then (if k = 0 ∧ s = m then m else k + 1)
    else if m ≤ s then m
    else Nat.findGreatest (fun q ↦ q * ((k + 1 + s - m) * (m - s) - closedBHHorizon m k s) ≤
      (m - s) * (k + s - m) * closedBHHorizon m k s ∧ q * (m - (k + 1)) ≤ (k + 1) * s) m

section ClosedBH

variable {m k s : ℕ}

@[simp]
theorem closedBHHorizon_zero (m s : ℕ) : closedBHHorizon m 0 s = 0 :=
  closedBHHorizon.eq_1 m s

theorem closedBHHorizon_succ (m k s : ℕ) : closedBHHorizon m (k + 1) s =
    if k + 1 + s ≤ m + 1 then (if k = 0 ∧ s = m then m else k + 1)
    else if m ≤ s then m
    else Nat.findGreatest (fun q ↦ q * ((k + 1 + s - m) * (m - s) - closedBHHorizon m k s) ≤
      (m - s) * (k + s - m) * closedBHHorizon m k s ∧ q * (m - (k + 1)) ≤ (k + 1) * s) m :=
  closedBHHorizon.eq_2 m s k

/-- Above the antidiagonal and before the last step, the horizon of closed BH is the largest one
allowed by both conditions. -/
private lemma closedBHHorizon_succ_of_lt (h : m + 1 < k + 1 + s) (hs : s < m) :
    closedBHHorizon m (k + 1) s = Nat.findGreatest (fun q ↦
      q * ((k + 1 + s - m) * (m - s) - closedBHHorizon m k s) ≤
        (m - s) * (k + s - m) * closedBHHorizon m k s ∧ q * (m - (k + 1)) ≤ (k + 1) * s) m := by
  rw [closedBHHorizon_succ, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem closedBHHorizon_le (hk : k ≤ m) : closedBHHorizon m k s ≤ m := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k =>
    rw [closedBHHorizon_succ]
    split_ifs
    · exact le_rfl
    · exact hk
    · exact le_rfl
    · exact Nat.findGreatest_le _

theorem closedBHHorizon_eq_self (hks : k + s ≤ m + 1) (h₁ : k = 1 → s < m) :
    closedBHHorizon m k s = k := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [closedBHHorizon_succ, ite_eq_left hks, ite_eq_right (by omega)]

/-- Above the antidiagonal and before the last step, the horizon of closed BH satisfies both the
growth bound and the criterion of [Goe26, Proposition 16], since `0` does. -/
private lemma closedBHHorizon_succ_spec_of_lt (h : m + 1 < k + 1 + s) (hs : s < m) :
    closedBHHorizon m (k + 1) s * ((k + 1 + s - m) * (m - s) - closedBHHorizon m k s) ≤
      (m - s) * (k + s - m) * closedBHHorizon m k s ∧
    closedBHHorizon m (k + 1) s * (m - (k + 1)) ≤ (k + 1) * s := by
  rw [closedBHHorizon_succ_of_lt h hs]
  exact Nat.findGreatest_spec (P := fun q ↦
    q * ((k + 1 + s - m) * (m - s) - closedBHHorizon m k s) ≤
      (m - s) * (k + s - m) * closedBHHorizon m k s ∧ q * (m - (k + 1)) ≤ (k + 1) * s)
    (Nat.zero_le _) (by simp)

/-- **The criterion of [Goe26, Proposition 16] for closed BH**: above the antidiagonal and before
the last step, `r k s * (m - k) ≤ k * s`. -/
theorem closedBHHorizon_mul_le (h : m + 1 < k + s) (hs : s < m) :
    closedBHHorizon m k s * (m - k) ≤ k * s := by
  cases k with
  | zero => omega
  | succ k => exact (closedBHHorizon_succ_spec_of_lt h hs).2

/-- [Goe26, Lemma 2]: the value `k + 1` is allowed by the growth bound, when the previous horizon
is at least `k`. -/
private lemma succ_mul_le_of_le (h : m + 1 < k + 1 + s) (hs : s < m) {q : ℕ} (hq : k ≤ q) :
    (k + 1) * ((k + 1 + s - m) * (m - s) - q) ≤ (m - s) * (k + s - m) * q := by
  obtain ⟨d, rfl⟩ : ∃ d, m = s + d := ⟨m - s, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, k = c + d := ⟨k - d, by omega⟩
  rw [show c + d + 1 + s - (s + d) = c + 1 by omega, show s + d - s = d by omega,
    show c + d + s - (s + d) = c by omega]
  rcases le_or_gt ((c + 1) * d) q with hq' | hq'
  · rw [Nat.sub_eq_zero_of_le hq', mul_zero]
    exact Nat.zero_le _
  · zify [hq'.le]
    have hq₀ : ((c : ℤ) + d) ≤ q := by exact_mod_cast hq
    nlinarith [mul_nonneg (sub_nonneg.2 hq₀) (by positivity : (0 : ℤ) ≤ (c + 1) * (d + 1)),
      mul_nonneg (by positivity : (0 : ℤ) ≤ c) (by positivity : (0 : ℤ) ≤ c + 1)]

/-- [Goe26, Lemma 1]: the previous horizon `q` is allowed by the growth bound when `q ≥ m - s`. -/
private lemma mul_le_of_le (hks : m ≤ k + s) {q : ℕ} (hq : m - s ≤ q) :
    q * ((k + 1 + s - m) * (m - s) - q) ≤ (m - s) * (k + s - m) * q := by
  calc q * ((k + 1 + s - m) * (m - s) - q) ≤ q * ((k + 1 + s - m) * (m - s) - (m - s)) := by
        gcongr
    _ = (m - s) * (k + s - m) * q := by
        rw [show k + 1 + s - m = (k + s - m) + 1 by omega, Nat.add_one_mul, Nat.add_sub_cancel]
        ring

/-- The horizons of closed BH are at least `k`. -/
theorem le_closedBHHorizon (hk : k ≤ m) : k ≤ closedBHHorizon m k s := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    rcases le_or_gt (k + 1 + s) (m + 1) with h | h
    · rw [closedBHHorizon_succ, ite_eq_left h]
      split_ifs
      · exact hk
      · exact le_rfl
    rcases le_or_gt m s with hms | hsm
    · rw [closedBHHorizon_succ, ite_eq_right (by omega), ite_eq_left hms]
      exact hk
    rw [closedBHHorizon_succ_of_lt h hsm]
    refine Nat.le_findGreatest hk ⟨succ_mul_le_of_le h hsm (ih (by omega)), ?_⟩
    exact Nat.mul_le_mul_left _ (by omega)

/-- **Closed BH is a BH-like method** [Goe26, §5]: its horizons satisfy the constraints
[Goe26, (1)–(3)]. -/
theorem isBHLikeHorizon_closedBHHorizon (m : ℕ) : IsBHLikeHorizon m (closedBHHorizon m) where
  apply_eq_self _ _ _ hks h₁ := closedBHHorizon_eq_self hks h₁
  le_apply _ _ hk _ _ := le_closedBHHorizon hk
  apply_le_apply_succ k s hk hs hsm := by
    rcases le_or_gt (k + 1 + s) (m + 1) with h | h
    · rw [closedBHHorizon_eq_self (k := k) (by omega) (by omega)]
      exact (Nat.le_succ k).trans (le_closedBHHorizon hk)
    rcases eq_or_lt_of_le hsm with rfl | hsm₁
    · rw [closedBHHorizon_succ, ite_eq_right (by omega), ite_eq_left le_rfl]
      exact closedBHHorizon_le hk.le
    rw [closedBHHorizon_succ_of_lt h hsm₁]
    have hq := le_closedBHHorizon (s := s) hk.le
    refine Nat.le_findGreatest (closedBHHorizon_le hk.le)
      ⟨mul_le_of_le (by omega) (by omega), ?_⟩
    -- The previous horizon satisfies the criterion of [Goe26, Proposition 16].
    rcases le_or_gt (k + s) (m + 1) with h' | h'
    · rw [closedBHHorizon_eq_self h' (by omega)]
      exact Nat.mul_le_mul (Nat.le_succ k) (by omega)
    · calc closedBHHorizon m k s * (m - (k + 1)) ≤ closedBHHorizon m k s * (m - k) := by
            gcongr
            omega
        _ ≤ k * s := closedBHHorizon_mul_le h' hsm₁
        _ ≤ (k + 1) * s := by gcongr; omega
  apply_succ_mul_le k s hk hs hsm := by
    rcases le_or_gt (k + 1 + s) (m + 1) with h | h
    · -- On or below the antidiagonal the factor `(k + 1 + s - m) * (m - s) - r k s` vanishes.
      rcases le_or_gt (k + 1 + s) m with h' | h'
      · rw [Nat.sub_eq_zero_of_le h', zero_mul, Nat.zero_sub, mul_zero]
        exact Nat.zero_le _
      · rw [closedBHHorizon_eq_self (k := k) (by omega) (by omega),
          show k + 1 + s - m = 1 by omega, one_mul, show m - s = k by omega, Nat.sub_self,
          mul_zero]
        exact Nat.zero_le _
    rcases eq_or_lt_of_le hsm with rfl | hsm₁
    · rw [Nat.sub_self, mul_zero, Nat.zero_sub, mul_zero]
      exact Nat.zero_le _
    exact (closedBHHorizon_succ_spec_of_lt h hsm₁).1

variable {ι : Type*} [Fintype ι] {α : ℝ≥0∞}

/-- **Closed BH rejects at least as many hypotheses as BH** [Goe26, §5]. -/
theorem card_eBH_inv_le_bhLikeCount_closedBHHorizon (α : ℝ≥0∞) (x : ι → ℝ≥0∞) :
    #(eBH (fun i ↦ (x i)⁻¹) α) ≤ bhLikeCount (closedBHHorizon (Fintype.card ι)) α x :=
  (isBHLikeHorizon_closedBHHorizon _).card_eBH_inv_le_bhLikeCount
    (fun _ _ h hs ↦ closedBHHorizon_mul_le h hs) α x

/-- **Closed BH rejects every hypothesis that BH rejects** [Goe26, §5]: every set of
`bhLikeCount (closedBHHorizon m) α x` hypotheses with the smallest p-values contains the rejection
set of BH. -/
theorem eBH_inv_subset_of_card_eq_bhLikeCount_closedBHHorizon {x : ι → ℝ≥0∞} {R : Finset ι}
    (hR : #R = bhLikeCount (closedBHHorizon (Fintype.card ι)) α x)
    (hRx : ∀ i ∈ R, ∀ j ∉ R, x i ≤ x j) : eBH (fun i ↦ (x i)⁻¹) α ⊆ R :=
  (isBHLikeHorizon_closedBHHorizon _).eBH_inv_subset (fun _ _ h hs ↦ closedBHHorizon_mul_le h hs)
    hR hRx

end ClosedBH

end ProbabilityTheory
