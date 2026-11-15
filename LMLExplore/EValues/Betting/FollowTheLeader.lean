/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Probability.ProductMeasure
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.EIntegral
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner
import TauCeti.Probability.Independence.InfinitePi
import TauCeti.Probability.StrongLaw

/-!
# Follow-the-leader betting on i.i.d. e-values

A bettor observes i.i.d. e-values `E 0, E 1, …` with law `Q` on `[0, ∞)` and bets at round `k` the
fraction `λ k ∈ [0, 1]` of its wealth on `E k`, so that the round multiplies the wealth by
`1 + λ k * (E k - 1)` and the wealth after `n` rounds is `∏ k < n, (1 + λ k * (E k - 1))`. The
follow-the-leader bettor (GREE in [WSJ26]) bets at round `n + 1` a fraction that maximizes over
`[0, 1]` the wealth that a constant fraction would have produced on `E 0, …, E n`, or
equivalently its logarithm `∑ k ≤ n, log (1 + λ * (E k - 1))`. Waudby-Smith, Sandoval and Jordan
ask whether it is almost surely log-optimal [WSJ26, Remark 2.3].

When `Q` gives no mass to `0`, almost surely, `(1/n) log` of its wealth tends to
`⨆ λ ∈ [0, 1], 𝔼_Q log (1 + λ (E - 1))`, the best growth rate of a constant fraction, which is
`+∞` when `log (1 + E)` has an infinite mean. When `Q` charges `0` and `(1, ∞)`, with positive
probability it bets everything at the second round and loses everything.

Both statements hold for all follow-the-leader fractions, measurable or not, and whatever the
rule that breaks ties: the almost sure event depends on `Q` only. No hypothesis such as
`𝔼_Q E ≤ 1` is needed.

## Main statements

* `ProbabilityTheory.ae_tendsto_log_prod_followTheLeader_div`: if `Q {0} = 0`, almost surely,
  for all follow-the-leader fractions, `(1/n) log` of the wealth tends to the best growth rate of
  a constant fraction.
* `ProbabilityTheory.measure_followTheLeader_bankrupt_pos`: if `Q {0} ≠ 0` and `Q (Ioi 1) ≠ 0`,
  with positive probability all follow-the-leader fractions lose everything at the second round.

## Implementation notes

Write `g l e = log (1 + l (e - 1))` and `f l` for the mean of `g l` under `Q`; `g · e` is concave
on `[0, 1]`, antitone when `e ≤ 1` and monotone when `e ≥ 1`. The point mass at `1` is a trivial
case.

When `log (1 + E)` has a finite mean, `f` has a maximizer `l₀` on `[0, 1]`, by compactness on
`[0, 1]` if `log E` is integrable, and otherwise on some `[0, c]` with `c < 1`, since then `f < 0`
on `[c, 1)` by monotone convergence. If `Q` is not the point mass at `1`, `f` is strictly concave
and `l₀` is its strict maximizer. By the strong law, the averages of `g a - g l₀` along the
e-values tend to `f a - f l₀ < 0` for every fraction `a ≠ l₀` of two sequences `a k → l₀` and
`b k → l₀`, one on each side of `l₀`; the concavity of the empirical objective then forces the
fractions into `[a k, b k]` eventually. There `g l e` lies between `min (g (a k) e) (g (b k) e)`
and `max (g (a k) e) (g (b k) e)`, whose means tend to `f l₀` by dominated convergence, and the
strong law for these envelopes concludes. No Lipschitz bound and no first-order condition is
used.

When `log (1 + E)` has an infinite mean, `f = +∞` on `(0, 1)`. Comparing fractions through the
bounded differences `g l - g (1 / 2)`, a reverse Fatou argument gives `a > 0` that does worse than
`1 / 2`, and `b < 1` as well when the negative part of `log E` has an infinite mean, so that the
fractions eventually stay in `[a, 1]`, or in `[a, b]`. There `g l e` is at least
`log a + log e`, or `log (min a (1 - b)) + log (1 + e)`, whose averages tend to `+∞` by the strong
law with an infinite mean.

## References

* [WSJ26] I. Waudby-Smith, R. Sandoval and M. I. Jordan, *Instance-log-optimality of
  portfolio-based e-processes and their sequential hypothesis tests*, arXiv:2504.02818v2.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

/-! ### The logarithm of one round -/

/-- The logarithm `log (1 + l (e - 1))` of the factor by which betting the fraction `l` on the
e-value `e` multiplies the wealth. -/
private noncomputable def logBetFactor (l : ℝ) (e : ℝ≥0) : ℝ := Real.log (1 + l * ((e : ℝ) - 1))

/-- The logarithm of one round is measurable in the e-value. -/
private lemma measurable_logBetFactor (l : ℝ) : Measurable (logBetFactor l) := by
  unfold logBetFactor
  fun_prop

/-- For a fraction in `[0, 1]`, the factor of a round on a positive e-value is positive. -/
private lemma one_add_mul_sub_one_pos {l e : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) (he : 0 < e) :
    0 < 1 + l * (e - 1) := by
  rcases eq_or_lt_of_le hl.2 with rfl | hl1
  · linarith
  · nlinarith [hl.1]

/-- For a fraction in `[0, 1]`, the factor of a round on a nonnegative e-value is nonnegative. -/
private lemma one_add_mul_sub_one_nonneg {l e : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) (he : 0 ≤ e) :
    0 ≤ 1 + l * (e - 1) := by
  nlinarith [hl.1, hl.2]

/-- On a positive e-value and for a fraction in `[0, 1]`, the extended logarithm of the factor of
a round is the real one. -/
private lemma log_ofReal_one_add_mul {l : ℝ} {e : ℝ≥0} (hl : l ∈ Icc (0 : ℝ) 1) (he : e ≠ 0) :
    ENNReal.log (ENNReal.ofReal (1 + l * ((e : ℝ) - 1))) = logBetFactor l e :=
  ENNReal.log_ofReal_of_pos (one_add_mul_sub_one_pos hl (by positivity))

/-- On an e-value at least `1`, the logarithm of one round is monotone in the fraction. -/
private lemma logBetFactor_le_logBetFactor_of_one_le {a b : ℝ} {e : ℝ≥0} (ha : 0 ≤ a)
    (hab : a ≤ b) (he : 1 ≤ (e : ℝ)) : logBetFactor a e ≤ logBetFactor b e :=
  Real.log_le_log (by nlinarith) (by nlinarith)

/-- On a positive e-value at most `1`, the logarithm of one round is antitone in the fraction
on `[0, 1]`. -/
private lemma logBetFactor_le_logBetFactor_of_le_one {a b : ℝ} {e : ℝ≥0} (ha : 0 ≤ a)
    (hb : b ≤ 1) (hab : a ≤ b) (he0 : e ≠ 0) (he : (e : ℝ) ≤ 1) :
    logBetFactor b e ≤ logBetFactor a e :=
  Real.log_le_log (one_add_mul_sub_one_pos ⟨ha.trans hab, hb⟩ (by positivity)) (by nlinarith)

/-- On an e-value at least `1`, the logarithm of one round with a nonnegative fraction is
nonnegative. -/
private lemma logBetFactor_nonneg {l : ℝ} {e : ℝ≥0} (hl : 0 ≤ l) (he : 1 ≤ (e : ℝ)) :
    0 ≤ logBetFactor l e :=
  Real.log_nonneg (by nlinarith)

/-- On an e-value at most `1`, the logarithm of one round with a fraction in `[0, 1]` is
nonpositive. -/
private lemma logBetFactor_nonpos {l : ℝ} {e : ℝ≥0} (hl : l ∈ Icc (0 : ℝ) 1)
    (he : (e : ℝ) ≤ 1) : logBetFactor l e ≤ 0 :=
  Real.log_nonpos (one_add_mul_sub_one_nonneg hl e.2) (by nlinarith [hl.1])

/-- The logarithm of one round with a fraction in `[0, 1]` is at most `log (1 + e)`. -/
private lemma logBetFactor_le_log_one_add {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) (e : ℝ≥0) :
    logBetFactor l e ≤ Real.log (1 + e) := by
  rcases le_total (e : ℝ) 1 with he | he
  · exact (logBetFactor_nonpos hl he).trans (Real.log_nonneg (by simp))
  · exact Real.log_le_log (by nlinarith [hl.1]) (by nlinarith [hl.1, hl.2])

/-- The logarithm of one round with a fraction in `[0, c]`, `c < 1`, is at least
`log (1 - c)`. -/
private lemma log_one_sub_le_logBetFactor {l c : ℝ} (hl : 0 ≤ l) (hlc : l ≤ c) (hc : c < 1)
    (e : ℝ≥0) : Real.log (1 - c) ≤ logBetFactor l e :=
  Real.log_le_log (by linarith) (by nlinarith [mul_nonneg hl e.coe_nonneg])

/-- A lower bound for fractions away from `0` and `1`: if `m ≤ l` and `m ≤ 1 - l` with `m > 0`,
then `log m + log (1 + e) ≤ log (1 + l (e - 1))`. -/
private lemma log_add_log_one_add_le_logBetFactor {m l : ℝ} (hm : 0 < m) (hml : m ≤ l)
    (hml' : m ≤ 1 - l) (e : ℝ≥0) : Real.log m + Real.log (1 + e) ≤ logBetFactor l e := by
  rw [← Real.log_mul hm.ne' (by positivity)]
  exact Real.log_le_log (by positivity)
    (by nlinarith [mul_le_mul_of_nonneg_right hml e.coe_nonneg])

/-- A lower bound for fractions away from `0`: if `0 < a ≤ l ≤ 1` and `e > 0`, then
`log a + log e ≤ log (1 + l (e - 1))`. -/
private lemma log_add_log_le_logBetFactor {a l : ℝ} (ha : 0 < a) (hal : a ≤ l) (hl : l ≤ 1)
    {e : ℝ≥0} (he : e ≠ 0) : Real.log a + Real.log e ≤ logBetFactor l e := by
  rw [← Real.log_mul ha.ne' (by positivity)]
  exact Real.log_le_log (by positivity)
    (by nlinarith [mul_le_mul_of_nonneg_right hal e.coe_nonneg])

/-- The round with fraction `0` has logarithm `0`. -/
private lemma logBetFactor_zero (e : ℝ≥0) : logBetFactor 0 e = 0 := by
  simp [logBetFactor]

/-- The round with fraction `1` has logarithm `log e`. -/
private lemma logBetFactor_one (e : ℝ≥0) : logBetFactor 1 e = Real.log e := by
  simp [logBetFactor]

/-- The round with fraction `1 / 2` has logarithm `log (1 + e) - log 2`. -/
private lemma logBetFactor_one_half (e : ℝ≥0) :
    logBetFactor (1 / 2) e = Real.log (1 + e) - Real.log 2 := by
  rw [logBetFactor, ← Real.log_div (by positivity) two_ne_zero]
  congr 1
  ring

/-- The logarithm of one round with a fraction in `[0, 1]` exceeds the one with fraction `1 / 2`
by at most `log 2`. -/
private lemma logBetFactor_sub_one_half_le {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) (e : ℝ≥0) :
    logBetFactor l e - logBetFactor (1 / 2) e ≤ Real.log 2 := by
  linarith [logBetFactor_le_log_one_add hl e, logBetFactor_one_half e]

/-- For fractions in `[0, c]` with `c ≤ 1` and a positive e-value,
`|log (1 + l (e - 1))| ≤ log (1 + e) + |log (1 + c (e - 1))|`. -/
private lemma abs_logBetFactor_le {l c : ℝ} {e : ℝ≥0} (hl : 0 ≤ l) (hlc : l ≤ c) (hc : c ≤ 1)
    (he : e ≠ 0) : |logBetFactor l e| ≤ Real.log (1 + e) + |logBetFactor c e| := by
  have h1 : 0 ≤ Real.log (1 + e) := Real.log_nonneg (by simp)
  rcases le_total (e : ℝ) 1 with he1 | he1
  · have h2 := logBetFactor_nonpos ⟨hl, hlc.trans hc⟩ he1
    have h3 := logBetFactor_le_logBetFactor_of_le_one hl hc hlc he he1
    rw [abs_of_nonpos h2, abs_of_nonpos (h3.trans h2)]
    linarith
  · rw [abs_of_nonneg (logBetFactor_nonneg hl he1)]
    linarith [logBetFactor_le_log_one_add ⟨hl, hlc.trans hc⟩ e, abs_nonneg (logBetFactor c e)]

/-- On a positive e-value, the logarithm of a round with a fraction between `a` and `b` in
`[0, 1]` lies between the minimum and the maximum of the logarithms of the rounds with fractions
`a` and `b`. -/
private lemma logBetFactor_mem_Icc {a l b : ℝ} {e : ℝ≥0} (ha : 0 ≤ a) (hal : a ≤ l)
    (hlb : l ≤ b) (hb : b ≤ 1) (he : e ≠ 0) :
    logBetFactor l e ∈ Icc (min (logBetFactor a e) (logBetFactor b e))
      (max (logBetFactor a e) (logBetFactor b e)) := by
  rcases le_total (e : ℝ) 1 with he1 | he1
  · exact ⟨min_le_of_right_le (logBetFactor_le_logBetFactor_of_le_one (ha.trans hal) hb hlb he he1),
      le_max_of_le_left (logBetFactor_le_logBetFactor_of_le_one ha (hlb.trans hb) hal he he1)⟩
  · exact ⟨min_le_of_left_le (logBetFactor_le_logBetFactor_of_one_le ha hal he1),
      le_max_of_le_right (logBetFactor_le_logBetFactor_of_one_le (ha.trans hal) hlb he1)⟩

/-- The logarithm of one round is continuous in the fraction where the factor does not vanish. -/
private lemma continuousAt_logBetFactor {l : ℝ} {e : ℝ≥0} (h : 1 + l * ((e : ℝ) - 1) ≠ 0) :
    ContinuousAt (fun l ↦ logBetFactor l e) l :=
  ContinuousAt.log (by fun_prop) h

/-- On a positive e-value, the logarithm of one round is continuous in the fraction on
`[0, 1]`. -/
private lemma continuousOn_logBetFactor {e : ℝ≥0} (he : e ≠ 0) :
    ContinuousOn (fun l ↦ logBetFactor l e) (Icc 0 1) := fun _ hl ↦
  (continuousAt_logBetFactor (one_add_mul_sub_one_pos hl (by positivity)).ne').continuousWithinAt

/-- On a positive e-value, the logarithm of one round is concave in the fraction on `[0, 1]`. -/
private lemma concaveOn_logBetFactor {e : ℝ≥0} (he : e ≠ 0) :
    ConcaveOn ℝ (Icc 0 1) (fun l ↦ logBetFactor l e) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  have hx' := one_add_mul_sub_one_pos hx (e := e) (by positivity)
  have hy' := one_add_mul_sub_one_pos hy (e := e) (by positivity)
  have h := strictConcaveOn_log_Ioi.concaveOn.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at h ⊢
  unfold logBetFactor
  convert h using 2
  linear_combination -hab

/-- On a positive e-value different from `1`, the logarithm of one round is strictly midpoint
concave in the fraction on `[0, 1]`. -/
private lemma add_logBetFactor_div_two_lt {x y : ℝ} {e : ℝ≥0} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) (hxy : x ≠ y) (he : e ≠ 0) (he1 : e ≠ 1) :
    (logBetFactor x e + logBetFactor y e) / 2 < logBetFactor ((x + y) / 2) e := by
  have hx' := one_add_mul_sub_one_pos hx (e := e) (by positivity)
  have hy' := one_add_mul_sub_one_pos hy (e := e) (by positivity)
  have hne : 1 + x * ((e : ℝ) - 1) ≠ 1 + y * ((e : ℝ) - 1) := by
    intro h
    have h1 : (e : ℝ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast he1)
    exact hxy (mul_right_cancel₀ h1 (by linarith))
  have h := strictConcaveOn_log_Ioi.2 hx' hy' hne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  unfold logBetFactor
  convert h using 2 <;> ring

/-- On positive e-values, the logarithm of the wealth of a constant fraction is concave in the
fraction on `[0, 1]`. -/
private lemma concaveOn_sum_logBetFactor {x : ℕ → ℝ≥0} (hx : ∀ i, x i ≠ 0) (n : ℕ) :
    ConcaveOn ℝ (Icc 0 1) (fun l ↦ ∑ i ∈ Finset.range n, logBetFactor l (x i)) := by
  induction n with
  | zero => simpa using concaveOn_const (0 : ℝ) (convex_Icc (0 : ℝ) 1)
  | succ n ih =>
    convert ih.add (concaveOn_logBetFactor (hx n)) using 1
    funext l
    exact Finset.sum_range_succ _ _

/-- On positive e-values and for fractions in `[0, 1]`, the extended logarithm of the wealth is
the sum of the real logarithms of the rounds. -/
private lemma log_prod_ofReal_eq {x : ℕ → ℝ≥0} (hx : ∀ i, x i ≠ 0) {l : ℕ → ℝ}
    (hl : ∀ i, l i ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    ENNReal.log (∏ k ∈ Finset.range n, ENNReal.ofReal (1 + l k * ((x k : ℝ) - 1))) =
      ((∑ k ∈ Finset.range n, logBetFactor (l k) (x k) : ℝ) : EReal) := by
  have hpos : ∀ k, 0 < 1 + l k * ((x k : ℝ) - 1) := fun k ↦
    one_add_mul_sub_one_pos (hl k) (NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hx k)))
  rw [← ENNReal.ofReal_prod_of_nonneg fun k _ ↦ (hpos k).le,
    ENNReal.log_ofReal_of_pos (Finset.prod_pos fun k _ ↦ hpos k),
    Real.log_prod fun k _ ↦ (hpos k).ne']
  rfl

/-- On positive e-values, a fraction in `[0, 1]` that maximizes over `[0, 1]` the wealth of a
constant fraction maximizes the sum of the real logarithms of the rounds. -/
private lemma isMaxOn_sum_logBetFactor {x : ℕ → ℝ≥0} (hx : ∀ i, x i ≠ 0) {n : ℕ} {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1)
    (h : IsMaxOn (fun c : ℝ ↦ ∏ k ∈ Finset.range n, ENNReal.ofReal (1 + c * ((x k : ℝ) - 1)))
      (Icc 0 1) l) :
    IsMaxOn (fun c ↦ ∑ k ∈ Finset.range n, logBetFactor c (x k)) (Icc 0 1) l :=
  isMaxOn_iff.2 fun c hc ↦ by
    have h' := ENNReal.log_le_log (isMaxOn_iff.1 h c hc)
    rwa [log_prod_ofReal_eq hx (l := fun _ ↦ c) (fun _ ↦ hc) n,
      log_prod_ofReal_eq hx (l := fun _ ↦ l) (fun _ ↦ hl) n, EReal.coe_le_coe_iff] at h'

/-! ### Averages -/

/-- Averages ignore finitely many terms: if `z i ≤ y i` eventually, the average of `y` is at least
the average of `z` plus a sequence tending to `0`. -/
private lemma exists_tendsto_zero_add_average_le {y z : ℕ → ℝ} (h : ∀ᶠ i in atTop, z i ≤ y i) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∀ n : ℕ,
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, z i + r n ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, y i := by
  refine ⟨fun n ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, min (y i - z i) 0,
    Tendsto.cesaro (tendsto_const_nhds.congr' ?_), fun n ↦ ?_⟩
  · filter_upwards [h] with i hi
    exact (min_eq_right (sub_nonneg.2 hi)).symm
  · rw [← mul_add, ← Finset.sum_add_distrib]
    gcongr with i
    linarith [min_le_left (y i - z i) 0]

/-- If `z i ≤ y i` eventually and the averages of `z` tend to `V > c`, the averages of `y` are
eventually larger than `c`. -/
private lemma eventually_lt_average {y z : ℕ → ℝ} (h : ∀ᶠ i in atTop, z i ≤ y i) {V c : ℝ}
    (hz : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, z i) atTop (𝓝 V))
    (hc : c < V) : ∀ᶠ n : ℕ in atTop, c < (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, y i := by
  obtain ⟨r, hr, hle⟩ := exists_tendsto_zero_add_average_le h
  have hlim := hz.add hr
  rw [add_zero] at hlim
  filter_upwards [hlim.eventually (lt_mem_nhds hc)] with n hn
  exact hn.trans_le (hle n)

/-- If `y i ≤ z i` eventually and the averages of `z` tend to `U < c`, the averages of `y` are
eventually smaller than `c`. -/
private lemma eventually_average_lt {y z : ℕ → ℝ} (h : ∀ᶠ i in atTop, y i ≤ z i) {U c : ℝ}
    (hz : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, z i) atTop (𝓝 U))
    (hc : U < c) : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, y i < c := by
  obtain ⟨r, hr, hle⟩ := exists_tendsto_zero_add_average_le h
  have hlim := hz.sub hr
  rw [sub_zero] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds hc)] with n hn
  linarith [hle n]

/-- If `z i ≤ y i` eventually and the averages of `z` tend to `+∞`, so do the averages of `y`. -/
private lemma tendsto_average_atTop {y z : ℕ → ℝ} (h : ∀ᶠ i in atTop, z i ≤ y i)
    (hz : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, z i) atTop atTop) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, y i) atTop atTop := by
  obtain ⟨r, hr, hle⟩ := exists_tendsto_zero_add_average_le h
  exact tendsto_atTop_mono hle (hz.atTop_add hr)

/-! ### The strong law along the coordinates -/

variable {Q : Measure ℝ≥0}

/-- The strong law of large numbers along the coordinates of `Q^ℕ`. -/
private lemma ae_tendsto_average [IsProbabilityMeasure Q] {f : ℝ≥0 → ℝ} (hf : Integrable f Q) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ Q),
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (x i)) atTop
        (𝓝 (∫ e, f e ∂Q)) := by
  simpa only [smul_eq_mul] using TauCeti.Probability.strong_law_ae_infinitePi Q hf

/-- The strong law of large numbers with an infinite mean along the coordinates of `Q^ℕ`: if `ψ`
is integrable, and `χ` has a negative part of finite mean and a positive part of infinite mean,
the averages of `ψ + χ` tend to `+∞`. -/
private lemma ae_tendsto_average_add_atTop [IsProbabilityMeasure Q] {ψ χ : ℝ≥0 → ℝ}
    (hψ : Integrable ψ Q) (hχ : Measurable χ) (hneg : ∫⁻ e, ENNReal.ofReal (-χ e) ∂Q ≠ ⊤)
    (hpos : ∫⁻ e, ENNReal.ofReal (χ e) ∂Q = ⊤) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ Q),
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (ψ (x i) + χ (x i))) atTop
        atTop := by
  have h0 := measurePreserving_eval_infinitePi (fun _ : ℕ ↦ Q) 0
  filter_upwards [ae_tendsto_average hψ,
    TauCeti.Probability.strong_law_ae_real_of_lintegral_eq_top
      (fun i (x : ℕ → ℝ≥0) ↦ χ (x i))
      (fun i j hij ↦ ((TauCeti.Probability.iIndepFun_eval_infinitePi _).comp (fun _ ↦ χ)
        (fun _ ↦ hχ)).indepFun hij)
      (fun i ↦ (Q.identDistrib_eval_infinitePi i 0).comp hχ)
      (by simpa only [h0.lintegral_comp (f := fun e ↦ ENNReal.ofReal (-χ e)) (by fun_prop)]
        using hneg)
      (by simpa only [h0.lintegral_comp (f := fun e ↦ ENNReal.ofReal (χ e)) (by fun_prop)]
        using hpos)] with x hψx hχx
  simp_rw [Finset.sum_add_distrib, mul_add]
  exact hψx.add_atTop (by simpa only [div_eq_inv_mul] using hχx)

/-- If `Q` gives no mass to `0`, almost every e-value is positive. -/
private lemma ae_ne_zero (hQ0 : Q {0} = 0) : ∀ᵐ e ∂Q, e ≠ 0 := by
  rw [ae_iff]
  simpa using hQ0

/-- If `Q` gives no mass to `0`, almost surely all the e-values are positive. -/
private lemma ae_forall_ne_zero [IsProbabilityMeasure Q] (hQ0 : Q {0} = 0) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ Q), ∀ i, x i ≠ 0 :=
  ae_all_iff.2 fun i ↦
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ Q) i).quasiMeasurePreserving.ae
      (ae_ne_zero hQ0)

/-! ### The expected logarithm of one round -/

/-- The finiteness of the mean of `log (1 + E)` as integrability. -/
private lemma integrable_log_one_add
    (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + (e : ℝ))) ∂Q ≠ ⊤) :
    Integrable (fun e : ℝ≥0 ↦ Real.log (1 + (e : ℝ))) Q := by
  refine ⟨(by fun_prop : Measurable fun e : ℝ≥0 ↦ Real.log (1 + (e : ℝ))).aestronglyMeasurable,
    ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun e ↦ Real.log_nonneg (by simp))]
  exact hlog.lt_top

/-- For a fraction in `[0, 1)`, the logarithm of one round is integrable. -/
private lemma integrable_logBetFactor [IsFiniteMeasure Q]
    (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + (e : ℝ))) ∂Q ≠ ⊤) {l : ℝ} (hl0 : 0 ≤ l)
    (hl1 : l < 1) : Integrable (logBetFactor l) Q := by
  refine Integrable.mono' ((integrable_log_one_add hlog).sub (integrable_const (Real.log (1 - l))))
    (measurable_logBetFactor l).aestronglyMeasurable (ae_of_all _ fun e ↦ ?_)
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  have h1 := log_one_sub_le_logBetFactor hl0 le_rfl hl1 e
  have h2 := logBetFactor_le_log_one_add ⟨hl0, hl1.le⟩ e
  have h3 : Real.log (1 - l) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have h4 : 0 ≤ Real.log (1 + e) := Real.log_nonneg (by simp)
  constructor <;> linarith

/-- If the logarithm of the round with fraction `c ≤ 1` is integrable, so is the one with any
fraction in `[0, c]`. -/
private lemma integrable_logBetFactor_of_le {l c : ℝ} (hQ0 : Q {0} = 0)
    (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + (e : ℝ))) ∂Q ≠ ⊤) (hl : 0 ≤ l) (hlc : l ≤ c)
    (hc : c ≤ 1) (hint : Integrable (logBetFactor c) Q) : Integrable (logBetFactor l) Q := by
  refine Integrable.mono' ((integrable_log_one_add hlog).add hint.abs)
    (measurable_logBetFactor l).aestronglyMeasurable ?_
  filter_upwards [ae_ne_zero hQ0] with e he
  exact abs_logBetFactor_le hl hlc hc he

/-- When the logarithm of one round is integrable, its extended integral is its integral. -/
private lemma eintegral_log_ofReal_eq (hQ0 : Q {0} = 0) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1)
    (hint : Integrable (logBetFactor l) Q) :
    ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + l * ((e : ℝ) - 1))) ∂Q =
      ∫ e, logBetFactor l e ∂Q := by
  rw [← eintegral_eq_integral hint]
  refine eintegral_congr_ae ?_
  filter_upwards [ae_ne_zero hQ0] with e he
  exact log_ofReal_one_add_mul hl he

/-- The extended logarithm of one round with a fraction in `[0, 1]` is at most
`log (1 + e)`. -/
private lemma log_ofReal_one_add_mul_le {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) (e : ℝ≥0) :
    ENNReal.log (ENNReal.ofReal (1 + l * ((e : ℝ) - 1))) ≤ (Real.log (1 + e) : EReal) := by
  rw [ENNReal.log_ofReal]
  split_ifs
  · exact bot_le
  · exact EReal.coe_le_coe_iff.2 (logBetFactor_le_log_one_add hl e)

/-- If `log E` is not integrable, the expected logarithm of the round with fraction `1` is
`⊥`. -/
private lemma eintegral_log_ofReal_eq_bot (hQ0 : Q {0} = 0)
    (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + (e : ℝ))) ∂Q ≠ ⊤)
    (hint : ¬ Integrable (logBetFactor 1) Q) :
    ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + 1 * ((e : ℝ) - 1))) ∂Q = ⊥ := by
  by_contra hbot
  apply hint
  have htop : ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + 1 * ((e : ℝ) - 1))) ∂Q ≠ ⊤ := by
    refine ne_top_of_le_ne_top (EReal.coe_ne_top (∫ e, Real.log (1 + (e : ℝ)) ∂Q)) ?_
    rw [← eintegral_eq_integral (integrable_log_one_add hlog)]
    exact eintegral_mono fun e ↦ log_ofReal_one_add_mul_le ⟨zero_le_one, le_rfl⟩ e
  refine (integrable_toReal_of_eintegral_ne_bot_of_ne_top (by fun_prop) hbot htop).congr ?_
  filter_upwards [ae_ne_zero hQ0] with e he
  rw [log_ofReal_one_add_mul ⟨zero_le_one, le_rfl⟩ he, EReal.toReal_coe]

/-- If the logarithm of the round with fraction `c ≤ 1` is integrable, the expected logarithm
of one round is continuous on `[0, c]`. -/
private lemma continuousOn_integral_logBetFactor (hQ0 : Q {0} = 0)
    (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + (e : ℝ))) ∂Q ≠ ⊤) {c : ℝ} (hc : c ≤ 1)
    (hint : Integrable (logBetFactor c) Q) :
    ContinuousOn (fun l ↦ ∫ e, logBetFactor l e ∂Q) (Icc 0 c) := by
  refine continuousOn_of_dominated (F := fun l e ↦ logBetFactor l e)
    (bound := fun e : ℝ≥0 ↦ Real.log (1 + e) + |logBetFactor c e|)
    (fun l _ ↦ (measurable_logBetFactor l).aestronglyMeasurable) (fun l hl ↦ ?_)
    ((integrable_log_one_add hlog).add hint.abs) ?_
  · filter_upwards [ae_ne_zero hQ0] with e he
    exact abs_logBetFactor_le hl.1 hl.2 hc he
  · filter_upwards [ae_ne_zero hQ0] with e he
    exact (continuousOn_logBetFactor he).mono (Icc_subset_Icc_right hc)

/-- As the fractions `a k` and `b k` in `[0, c]` tend to `l₀`, the mean of `φ` applied to the
logarithms of the rounds with fractions `a k` and `b k` tends to the mean of the logarithm of the
round with fraction `l₀`, for `φ` continuous with `φ t t = t` and `|φ s t| ≤ max |s| |t|`, such
as `min` and `max` (dominated convergence). -/
private lemma tendsto_integral_comp_logBetFactor (hQ0 : Q {0} = 0)
    (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + (e : ℝ))) ∂Q ≠ ⊤) {φ : ℝ → ℝ → ℝ}
    (hφ : Continuous fun p : ℝ × ℝ ↦ φ p.1 p.2) (hφ_abs : ∀ s t, |φ s t| ≤ max |s| |t|)
    (hφ_self : ∀ t, φ t t = t) {a b : ℕ → ℝ} {c l₀ : ℝ} (ha : ∀ k, a k ∈ Icc 0 c)
    (hb : ∀ k, b k ∈ Icc 0 c) (hc : c ≤ 1) (hint : Integrable (logBetFactor c) Q)
    (hl₀ : l₀ ∈ Icc (0 : ℝ) 1) (ha_lim : Tendsto a atTop (𝓝 l₀))
    (hb_lim : Tendsto b atTop (𝓝 l₀)) :
    Tendsto (fun k ↦ ∫ e, φ (logBetFactor (a k) e) (logBetFactor (b k) e) ∂Q) atTop
      (𝓝 (∫ e, logBetFactor l₀ e ∂Q)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun e ↦ Real.log (1 + e) + |logBetFactor c e|)
    (fun k ↦ (hφ.measurable.comp ((measurable_logBetFactor _).prodMk
      (measurable_logBetFactor _))).aestronglyMeasurable)
    ((integrable_log_one_add hlog).add hint.abs) (fun k ↦ ?_) ?_
  · filter_upwards [ae_ne_zero hQ0] with e he
    rw [Real.norm_eq_abs]
    exact (hφ_abs _ _).trans (max_le (abs_logBetFactor_le (ha k).1 (ha k).2 hc he)
      (abs_logBetFactor_le (hb k).1 (hb k).2 hc he))
  · filter_upwards [ae_ne_zero hQ0] with e he
    have hcont := (continuousAt_logBetFactor (e := e)
      (one_add_mul_sub_one_pos hl₀ (by positivity)).ne').tendsto
    rw [← hφ_self (logBetFactor l₀ e)]
    exact (hφ.tendsto (logBetFactor l₀ e, logBetFactor l₀ e)).comp
      ((hcont.comp ha_lim).prodMk_nhds (hcont.comp hb_lim))

/-- The negative part of the logarithm of one round is monotone in the fraction on `[0, 1]`. -/
private lemma ofReal_neg_logBetFactor_le {a b : ℝ} {e : ℝ≥0} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) (he : e ≠ 0) :
    ENNReal.ofReal (-logBetFactor a e) ≤ ENNReal.ofReal (-logBetFactor b e) := by
  rcases le_total (e : ℝ) 1 with he1 | he1
  · exact ENNReal.ofReal_le_ofReal
      (neg_le_neg (logBetFactor_le_logBetFactor_of_le_one ha hb hab he he1))
  · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.2 (logBetFactor_nonneg ha he1))]
    positivity

/-- If `log E` is not integrable, the expected logarithm of one round is negative for all
fractions close enough to `1`. -/
private lemma exists_integral_logBetFactor_neg [IsFiniteMeasure Q] (hQ0 : Q {0} = 0)
    (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + (e : ℝ))) ∂Q ≠ ⊤)
    (hint : ¬ Integrable (logBetFactor 1) Q) :
    ∃ c, 0 ≤ c ∧ c < 1 ∧ ∀ l ∈ Ico c 1, ∫ e, logBetFactor l e ∂Q < 0 := by
  have hbot := eintegral_log_ofReal_eq_bot hQ0 hlog hint
  have htop : ∫⁻ e, ENNReal.ofReal (-logBetFactor 1 e) ∂Q = ⊤ := by
    have h := not_not.1 (mt eintegral_ne_bot_iff_lintegral_ne_top.2 (not_not.2 hbot))
    rw [← h]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_ne_zero hQ0] with e he
    rw [log_ofReal_one_add_mul ⟨zero_le_one, le_rfl⟩ he, ← EReal.coe_neg,
      EReal.real_coe_toENNReal]
  set l : ℕ → ℝ := fun k ↦ 1 - 1 / ((k : ℝ) + 2) with hl_def
  have hl0 : ∀ k, 0 ≤ l k := fun k ↦ by
    rw [hl_def, sub_nonneg, div_le_one (by positivity)]
    linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hl1 : ∀ k, l k < 1 := fun k ↦ by
    simp only [hl_def, sub_lt_self_iff]
    positivity
  have hlmono : Monotone l := fun i j hij ↦ by
    simp only [hl_def, sub_le_sub_iff_left]
    gcongr
  have hlim : Tendsto l atTop (𝓝 1) := by
    have h : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h
    rw [sub_zero] at h2
    exact h2
  have hmc : Tendsto (fun k ↦ ∫⁻ e, ENNReal.ofReal (-logBetFactor (l k) e) ∂Q) atTop
      (𝓝 (∫⁻ e, ENNReal.ofReal (-logBetFactor 1 e) ∂Q)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun k ↦ (measurable_logBetFactor _).neg.ennreal_ofReal.aemeasurable) ?_ ?_
    · filter_upwards [ae_ne_zero hQ0] with e he i j hij
      exact ofReal_neg_logBetFactor_le (hl0 i) (hlmono hij) (hl1 j).le he
    · filter_upwards [ae_ne_zero hQ0] with e he
      refine (ENNReal.continuous_ofReal.tendsto _).comp (Tendsto.neg ?_)
      refine (continuousAt_logBetFactor ?_).tendsto.comp hlim
      simpa using he
  rw [htop] at hmc
  obtain ⟨k, hk⟩ := (hmc.eventually (lt_mem_nhds hlog.lt_top)).exists
  refine ⟨l k, hl0 k, hl1 k, fun l' hl' ↦ ?_⟩
  have hl'0 : 0 ≤ l' := (hl0 k).trans hl'.1
  have hint' := integrable_logBetFactor hlog hl'0 hl'.2
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint', sub_neg]
  have hP : ∫⁻ e, ENNReal.ofReal (logBetFactor l' e) ∂Q ≤
      ∫⁻ e, ENNReal.ofReal (Real.log (1 + (e : ℝ))) ∂Q :=
    lintegral_mono fun e ↦ ENNReal.ofReal_le_ofReal
      (logBetFactor_le_log_one_add ⟨hl'0, hl'.2.le⟩ e)
  have hN : ∫⁻ e, ENNReal.ofReal (-logBetFactor (l k) e) ∂Q ≤
      ∫⁻ e, ENNReal.ofReal (-logBetFactor l' e) ∂Q := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_ne_zero hQ0] with e he
    exact ofReal_neg_logBetFactor_le (hl0 k) hl'.1 hl'.2.le he
  exact (ENNReal.toReal_lt_toReal hint'.lintegral_lt_top.ne
    hint'.neg.lintegral_lt_top.ne).2 (hP.trans_lt (hk.trans_le hN))

/-- The expected logarithm of one round has a maximizer `l₀` on `[0, 1]`, at which it is
finite. -/
private lemma exists_isMaxOn_eintegral [IsProbabilityMeasure Q] (hQ0 : Q {0} = 0)
    (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + (e : ℝ))) ∂Q ≠ ⊤) :
    ∃ l₀ ∈ Icc (0 : ℝ) 1, Integrable (logBetFactor l₀) Q ∧ ∀ l ∈ Icc (0 : ℝ) 1,
      ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + l * ((e : ℝ) - 1))) ∂Q ≤
        ∫ e, logBetFactor l₀ e ∂Q := by
  by_cases h1 : Integrable (logBetFactor 1) Q
  · obtain ⟨l₀, hl₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one)
      (continuousOn_integral_logBetFactor hQ0 hlog le_rfl h1)
    have hint : ∀ l ∈ Icc (0 : ℝ) 1, Integrable (logBetFactor l) Q := fun l hl ↦
      integrable_logBetFactor_of_le hQ0 hlog hl.1 hl.2 le_rfl h1
    refine ⟨l₀, hl₀, hint l₀ hl₀, fun l hl ↦ ?_⟩
    rw [eintegral_log_ofReal_eq hQ0 hl (hint l hl)]
    exact EReal.coe_le_coe_iff.2 (isMaxOn_iff.1 hmax l hl)
  · obtain ⟨c, hc0, hc1, hneg⟩ := exists_integral_logBetFactor_neg hQ0 hlog h1
    obtain ⟨l₀, hl₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hc0)
      (continuousOn_integral_logBetFactor hQ0 hlog hc1.le
        (integrable_logBetFactor hlog hc0 hc1))
    have h0 : (0 : ℝ) ≤ ∫ e, logBetFactor l₀ e ∂Q := by
      simpa [logBetFactor] using isMaxOn_iff.1 hmax 0 ⟨le_rfl, hc0⟩
    refine ⟨l₀, ⟨hl₀.1, hl₀.2.trans hc1.le⟩,
      integrable_logBetFactor hlog hl₀.1 (hl₀.2.trans_lt hc1), fun l hl ↦ ?_⟩
    rcases eq_or_lt_of_le hl.2 with rfl | hl1
    · rw [eintegral_log_ofReal_eq_bot hQ0 hlog h1]
      exact bot_le
    rw [eintegral_log_ofReal_eq hQ0 hl (integrable_logBetFactor hlog hl.1 hl1)]
    refine EReal.coe_le_coe_iff.2 ?_
    rcases le_or_gt l c with hlc | hlc
    · exact isMaxOn_iff.1 hmax l ⟨hl.1, hlc⟩
    · exact ((hneg l ⟨hlc.le, hl1⟩).trans_le h0).le

/-- When `Q` is not the point mass at `1`, a maximizer `l₀` of the expected logarithm of one
round is strict: every other fraction with an integrable logarithm does strictly worse. -/
private lemma integral_logBetFactor_lt [IsProbabilityMeasure Q] (hQ0 : Q {0} = 0)
    (hQ1 : Q {1} ≠ 1) (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + (e : ℝ))) ∂Q ≠ ⊤) {l₀ : ℝ}
    (hl₀ : l₀ ∈ Icc (0 : ℝ) 1) (hint₀ : Integrable (logBetFactor l₀) Q)
    (hmax : ∀ l ∈ Icc (0 : ℝ) 1,
      ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + l * ((e : ℝ) - 1))) ∂Q ≤
        ∫ e, logBetFactor l₀ e ∂Q)
    {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) (hll₀ : l ≠ l₀) (hint : Integrable (logBetFactor l) Q) :
    ∫ e, logBetFactor l e ∂Q < ∫ e, logBetFactor l₀ e ∂Q := by
  set m := (l + l₀) / 2 with hm_def
  have hm : m ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hl.1, hl₀.1], by linarith [hl.2, hl₀.2]⟩
  have hm1 : m < 1 := by
    rcases lt_or_gt_of_ne hll₀ with h | h <;> linarith [hl.2, hl₀.2]
  have hintm := integrable_logBetFactor hlog hm.1 hm1
  have hle : ∀ l' ∈ Icc (0 : ℝ) 1, Integrable (logBetFactor l') Q →
      ∫ e, logBetFactor l' e ∂Q ≤ ∫ e, logBetFactor l₀ e ∂Q := fun l' hl' hint' ↦ by
    have h := hmax l' hl'
    rwa [eintegral_log_ofReal_eq hQ0 hl' hint', EReal.coe_le_coe_iff] at h
  have hint2 : Integrable (fun e ↦ (logBetFactor l e + logBetFactor l₀ e) / 2) Q :=
    (hint.add hint₀).div_const 2
  have hpos : 0 < ∫ e, (logBetFactor m e - (logBetFactor l e + logBetFactor l₀ e) / 2) ∂Q := by
    rw [integral_pos_iff_support_of_nonneg_ae]
    · have hS : Q ({1}ᶜ \ {0}) ≠ 0 := by
        rw [measure_sdiff_null hQ0, prob_compl_eq_one_sub (measurableSet_singleton 1)]
        exact (tsub_pos_of_lt (lt_of_le_of_ne prob_le_one hQ1)).ne'
      refine (pos_iff_ne_zero.2 hS).trans_le (measure_mono fun e he ↦ ?_)
      exact (sub_pos.2 (add_logBetFactor_div_two_lt hl hl₀ hll₀ he.2 he.1)).ne'
    · filter_upwards [ae_ne_zero hQ0] with e he
      have h := (concaveOn_logBetFactor he).2 hl hl₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at h
      rw [show (1 / 2 : ℝ) * l + 1 / 2 * l₀ = m by rw [hm_def]; ring] at h
      rw [Pi.zero_apply]
      linarith
    · exact hintm.sub hint2
  rw [integral_sub hintm hint2, integral_div, integral_add hint hint₀] at hpos
  linarith [hle l hl hint, hle m hm hintm]

/-! ### When `log (1 + E)` has an infinite mean

Then the expected logarithm of every round with a fraction in `(0, 1)` is `+∞`, and fractions are
compared through the bounded differences `log (1 + l (e - 1)) - log (1 + (e - 1) / 2)`. -/

/-- If `ofReal ∘ f ≤ ofReal ∘ g + C` with `C` finite and the positive part of `f` has an infinite
mean, so does the positive part of `g`. -/
private lemma lintegral_ofReal_eq_top_of_le_add [IsFiniteMeasure Q] {f g : ℝ≥0 → ℝ} {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hfg : ∀ e, ENNReal.ofReal (f e) ≤ ENNReal.ofReal (g e) + C)
    (hf : ∫⁻ e, ENNReal.ofReal (f e) ∂Q = ⊤) : ∫⁻ e, ENNReal.ofReal (g e) ∂Q = ⊤ := by
  have h := (lintegral_mono (μ := Q) hfg).trans_eq (lintegral_add_right _ measurable_const)
  rw [hf, lintegral_const, top_le_iff, ENNReal.add_eq_top] at h
  exact h.resolve_right (ENNReal.mul_ne_top hC (measure_ne_top _ _))

/-- For a fraction in `(0, 1)`, the difference with the round of fraction `1 / 2` is
integrable. -/
private lemma integrable_logBetFactor_sub_one_half [IsFiniteMeasure Q] {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) : Integrable (fun e ↦ logBetFactor l e - logBetFactor (1 / 2) e) Q := by
  set m := min l (1 - l)
  have hm : 0 < m := lt_min hl0 (by linarith)
  have hm1 : Real.log m ≤ 0 := Real.log_nonpos hm.le ((min_le_right _ _).trans (by linarith))
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  refine Integrable.mono' (integrable_const (Real.log 2 - Real.log m))
    ((measurable_logBetFactor l).sub (measurable_logBetFactor _)).aestronglyMeasurable
    (ae_of_all _ fun e ↦ ?_)
  have h1 := log_add_log_one_add_le_logBetFactor hm (min_le_left _ _) (min_le_right _ _) e
  have h2 := logBetFactor_sub_one_half_le ⟨hl0.le, hl1.le⟩ e
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [logBetFactor_one_half e]

/-- If `log (1 + E)` has an infinite mean, so does the round with fraction `1 / 2`. -/
private lemma lintegral_ofReal_logBetFactor_one_half_eq_top [IsFiniteMeasure Q]
    (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + (e : ℝ))) ∂Q = ⊤) :
    ∫⁻ e, ENNReal.ofReal (logBetFactor (1 / 2) e) ∂Q = ⊤ :=
  lintegral_ofReal_eq_top_of_le_add (ENNReal.ofReal_ne_top (r := Real.log 2)) (fun e ↦
    (ENNReal.ofReal_le_ofReal (by rw [logBetFactor_one_half]; linarith)).trans
      ENNReal.ofReal_add_le) hlog

/-- A reverse Fatou argument: if integrable functions bounded above by a constant converge almost
everywhere to a function whose negative part has an infinite mean, one of them has a negative
integral. -/
private lemma exists_integral_neg_of_tendsto [IsFiniteMeasure Q] {f : ℕ → ℝ≥0 → ℝ}
    {F : ℝ≥0 → ℝ} {C : ℝ} (hf : ∀ k, Integrable (f k) Q) (hfC : ∀ k e, f k e ≤ C)
    (hlim : ∀ᵐ e ∂Q, Tendsto (fun k ↦ f k e) atTop (𝓝 (F e)))
    (hF : ∫⁻ e, ENNReal.ofReal (-F e) ∂Q = ⊤) : ∃ k, ∫ e, f k e ∂Q < 0 := by
  have hfatou := lintegral_liminf_le' (μ := Q) (u := atTop)
    (f := fun k e ↦ ENNReal.ofReal (-f k e))
    (fun k ↦ (hf k).1.aemeasurable.neg.ennreal_ofReal)
  have hlhs : ∫⁻ e, liminf (fun k ↦ ENNReal.ofReal (-f k e)) atTop ∂Q = ⊤ := by
    rw [← hF]
    refine lintegral_congr_ae ?_
    filter_upwards [hlim] with e he
    exact ((ENNReal.continuous_ofReal.tendsto _).comp he.neg).liminf_eq
  rw [hlhs, top_le_iff] at hfatou
  have hB : ENNReal.ofReal C * Q univ < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  rw [← hfatou] at hB
  obtain ⟨k, hk⟩ := (eventually_lt_of_lt_liminf hB).exists
  refine ⟨k, ?_⟩
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hf k), sub_neg]
  have hP : ∫⁻ e, ENNReal.ofReal (f k e) ∂Q ≤ ENNReal.ofReal C * Q univ := by
    rw [← lintegral_const]
    exact lintegral_mono fun e ↦ ENNReal.ofReal_le_ofReal (hfC k e)
  exact (ENNReal.toReal_lt_toReal (hf k).lintegral_lt_top.ne
    (hf k).neg.lintegral_lt_top.ne).2 (hP.trans_lt hk)

/-- If `log (1 + E)` has an infinite mean, some small fraction does worse than `1 / 2`. -/
private lemma exists_integral_logBetFactor_sub_one_half_neg_of_lt [IsFiniteMeasure Q]
    (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + (e : ℝ))) ∂Q = ⊤) :
    ∃ a, 0 < a ∧ a < 1 / 2 ∧ ∫ e, (logBetFactor a e - logBetFactor (1 / 2) e) ∂Q < 0 := by
  have ha0 : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 3) := fun k ↦ by positivity
  have ha2 : ∀ k : ℕ, 1 / ((k : ℝ) + 3) < 1 / 2 := fun k ↦
    one_div_lt_one_div_of_lt two_pos (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  have hlim : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop)
  obtain ⟨k, hk⟩ := exists_integral_neg_of_tendsto
    (f := fun k e ↦ logBetFactor (1 / ((k : ℝ) + 3)) e - logBetFactor (1 / 2) e)
    (F := fun e ↦ logBetFactor 0 e - logBetFactor (1 / 2) e) (C := Real.log 2)
    (fun k ↦ integrable_logBetFactor_sub_one_half (ha0 k) ((ha2 k).trans (by norm_num)))
    (fun k e ↦ logBetFactor_sub_one_half_le ⟨(ha0 k).le, ((ha2 k).trans (by norm_num)).le⟩ e)
    (ae_of_all _ fun e ↦ ((continuousAt_logBetFactor (by simp)).tendsto.comp hlim).sub_const _)
    (by simpa [logBetFactor_zero] using lintegral_ofReal_logBetFactor_one_half_eq_top hlog)
  exact ⟨_, ha0 k, ha2 k, hk⟩

/-- If the negative part of `log E` has an infinite mean, some fraction close to `1` does worse
than `1 / 2`. -/
private lemma exists_integral_logBetFactor_sub_one_half_neg_of_gt [IsFiniteMeasure Q]
    (hQ0 : Q {0} = 0) (hlog1 : ∫⁻ e, ENNReal.ofReal (-logBetFactor 1 e) ∂Q = ⊤) :
    ∃ b, 1 / 2 < b ∧ b < 1 ∧ ∫ e, (logBetFactor b e - logBetFactor (1 / 2) e) ∂Q < 0 := by
  have hb1 : ∀ k : ℕ, 1 - 1 / ((k : ℝ) + 3) < 1 := fun k ↦ by
    simp only [sub_lt_self_iff]
    positivity
  have hb2 : ∀ k : ℕ, 1 / 2 < 1 - 1 / ((k : ℝ) + 3) := fun k ↦ by
    have : 1 / ((k : ℝ) + 3) < 1 / 2 :=
      one_div_lt_one_div_of_lt two_pos (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
    linarith
  have hlim : Tendsto (fun k : ℕ ↦ 1 - 1 / ((k : ℝ) + 3)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop
        (tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop))
    rwa [sub_zero] at h
  obtain ⟨k, hk⟩ := exists_integral_neg_of_tendsto
    (f := fun k e ↦ logBetFactor (1 - 1 / ((k : ℝ) + 3)) e - logBetFactor (1 / 2) e)
    (F := fun e ↦ logBetFactor 1 e - logBetFactor (1 / 2) e) (C := Real.log 2)
    (fun k ↦ integrable_logBetFactor_sub_one_half ((hb2 k).trans' (by norm_num)) (hb1 k))
    (fun k e ↦ logBetFactor_sub_one_half_le
      ⟨((hb2 k).trans' (by norm_num)).le, (hb1 k).le⟩ e)
    (by
      filter_upwards [ae_ne_zero hQ0] with e he
      exact ((continuousAt_logBetFactor (by simpa using he)).tendsto.comp hlim).sub_const _)
    (lintegral_ofReal_eq_top_of_le_add (ENNReal.ofReal_ne_top (r := Real.log 2)) (fun e ↦
      (ENNReal.ofReal_le_ofReal (by
        linarith [logBetFactor_one_half e, Real.log_nonneg (by simp : (1 : ℝ) ≤ 1 + e)])).trans
        ENNReal.ofReal_add_le) hlog1)
  exact ⟨_, hb2 k, hb1 k, hk⟩

/-! ### Pathwise arguments -/

/-- Consistency of follow-the-leader: if the averages of the difference of the logarithms of the
rounds with fractions `a` and `l₀` tend to a negative limit, then eventually `a` does not lie
between the fraction and `l₀`. -/
private lemma eventually_notMem_uIcc {x : ℕ → ℝ≥0} (hx : ∀ i, x i ≠ 0) {l : ℕ → ℝ}
    (hl : ∀ n, l n ∈ Icc (0 : ℝ) 1)
    (hmax : ∀ n, IsMaxOn (fun c ↦ ∑ i ∈ Finset.range (n + 1), logBetFactor c (x i)) (Icc 0 1)
      (l (n + 1)))
    {a l₀ : ℝ} (hl₀ : l₀ ∈ Icc (0 : ℝ) 1) {D : ℝ}
    (hD : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, (logBetFactor a (x i) - logBetFactor l₀ (x i))) atTop (𝓝 D))
    (hD0 : D < 0) :
    ∀ᶠ n in atTop, a ∉ uIcc (l n) l₀ := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hD.eventually (gt_mem_nhds hD0))
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn hmem
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : ∑ i ∈ Finset.range (m + 1), logBetFactor a (x i) <
      ∑ i ∈ Finset.range (m + 1), logBetFactor l₀ (x i) := by
    have h := neg_of_mul_neg_right (hN (m + 1) (by omega)) (by positivity)
    rwa [Finset.sum_sub_distrib, sub_neg] at h
  have h := (concaveOn_sum_logBetFactor hx (m + 1)).min_le_of_mem_segment (hl (m + 1)) hl₀
    (by rwa [segment_eq_uIcc])
  rw [min_eq_right (isMaxOn_iff.1 (hmax m) l₀ hl₀)] at h
  exact absurd h (not_le.2 hm)

/-- The pathwise transfer: if the fractions are eventually between `a k` and `b k`, and the
averages of the maximum and of the minimum of the logarithms of the rounds with fractions `a k`
and `b k` tend to limits that tend to `L`, then the averages of the logarithms of the rounds tend
to `L`. -/
private lemma tendsto_average_logBetFactor {x : ℕ → ℝ≥0} (hx : ∀ i, x i ≠ 0) {l : ℕ → ℝ}
    {a b u v : ℕ → ℝ} {L : ℝ} (ha0 : ∀ k, 0 ≤ a k) (hb1 : ∀ k, b k ≤ 1)
    (hab : ∀ k, ∀ᶠ n in atTop, a k ≤ l n ∧ l n ≤ b k)
    (hu : ∀ k, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      max (logBetFactor (a k) (x i)) (logBetFactor (b k) (x i))) atTop (𝓝 (u k)))
    (hv : ∀ k, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      min (logBetFactor (a k) (x i)) (logBetFactor (b k) (x i))) atTop (𝓝 (v k)))
    (huL : Tendsto u atTop (𝓝 L)) (hvL : Tendsto v atTop (𝓝 L)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, logBetFactor (l i) (x i)) atTop
      (𝓝 L) := by
  refine tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · obtain ⟨k, hk⟩ := (hvL.eventually (lt_mem_nhds hc)).exists
    refine eventually_lt_average ?_ (hv k) hk
    filter_upwards [hab k] with i hi
    exact (logBetFactor_mem_Icc (ha0 k) hi.1 hi.2 (hb1 k) (hx i)).1
  · obtain ⟨k, hk⟩ := (huL.eventually (gt_mem_nhds hc)).exists
    refine eventually_average_lt ?_ (hu k) hk
    filter_upwards [hab k] with i hi
    exact (logBetFactor_mem_Icc (ha0 k) hi.1 hi.2 (hb1 k) (hx i)).2

/-! ### The three cases of the growth rate -/

/-- Under the point mass at `1`, every round has logarithm `0`, whatever the fractions. -/
private lemma ae_tendsto_average_of_measure_one_eq_one [IsProbabilityMeasure Q]
    (hQ1 : Q {1} = 1) :
    (⨆ c ∈ Icc (0 : ℝ) 1,
        ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * ((e : ℝ) - 1))) ∂Q) = 0 ∧
      ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ Q), ∀ l : ℕ → ℝ,
        Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, logBetFactor (l i) (x i)) atTop
          (𝓝 0) := by
  have hQ : ∀ᵐ e ∂Q, e = 1 := by
    rw [ae_iff]
    exact (prob_compl_eq_zero_iff (measurableSet_singleton 1)).2 hQ1
  refine ⟨le_antisymm (iSup₂_le fun c _ ↦ ?_) (le_iSup₂_of_le 0 ⟨le_rfl, zero_le_one⟩ ?_), ?_⟩
  · refine ((eintegral_congr_ae ?_).trans (eintegral_zero Q)).le
    filter_upwards [hQ] with e he
    simp [he]
  · simp
  · filter_upwards [ae_all_iff.2 fun i ↦
      (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ Q) i).quasiMeasurePreserving.ae hQ]
      with x hx l
    simp [hx, logBetFactor]

/-- The growth rate when `log (1 + E)` has a finite mean and `Q` is not the point mass at `1`:
the fractions tend to the strict maximizer `l₀` of the expected logarithm of one round, and the
transfer goes through the minimum and the maximum of the rounds with fractions on each side of
`l₀`. -/
private lemma ae_tendsto_average_of_lintegral_ne_top [IsProbabilityMeasure Q] (hQ0 : Q {0} = 0)
    (hQ1 : Q {1} ≠ 1) (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + (e : ℝ))) ∂Q ≠ ⊤) :
    ∃ L : ℝ, (⨆ c ∈ Icc (0 : ℝ) 1,
        ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * ((e : ℝ) - 1))) ∂Q) = L ∧
      ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ Q), ∀ l : ℕ → ℝ, (∀ n, l n ∈ Icc (0 : ℝ) 1) →
        (∀ n, IsMaxOn (fun c ↦ ∑ i ∈ Finset.range (n + 1), logBetFactor c (x i)) (Icc 0 1)
          (l (n + 1))) →
        Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, logBetFactor (l i) (x i)) atTop
          (𝓝 L) := by
  obtain ⟨l₀, hl₀, hint₀, hmax₀⟩ := exists_isMaxOn_eintegral hQ0 hlog
  refine ⟨∫ e, logBetFactor l₀ e ∂Q, le_antisymm (iSup₂_le hmax₀)
    (le_iSup₂_of_le l₀ hl₀ (eintegral_log_ofReal_eq hQ0 hl₀ hint₀).ge), ?_⟩
  -- fractions `a k ↑ l₀` and `b k ↓ l₀`, all in `[0, c]` where `c = (1 + l₀) / 2`
  set c := (1 + l₀) / 2 with hc
  have hc1 : c ≤ 1 := by linarith [hl₀.2]
  have hintc : Integrable (logBetFactor c) Q := by
    rcases eq_or_lt_of_le hl₀.2 with h | h
    · rw [show c = l₀ by rw [hc, h]; norm_num]
      exact hint₀
    · exact integrable_logBetFactor hlog (by linarith [hl₀.1]) (by linarith)
  set a : ℕ → ℝ := fun k ↦ l₀ - l₀ / ((k : ℝ) + 2) with ha
  set b : ℕ → ℝ := fun k ↦ l₀ + (1 - l₀) / ((k : ℝ) + 2) with hb
  have hk2 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 2 := fun k ↦ by positivity
  have hdiv : ∀ (k : ℕ) {r : ℝ}, 0 ≤ r → r / ((k : ℝ) + 2) ≤ r / 2 := fun k r hr ↦
    div_le_div_of_nonneg_left hr two_pos (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  have ha_mem : ∀ k, a k ∈ Icc 0 c := fun k ↦ by
    have h1 := hdiv k hl₀.1
    have h2 : 0 ≤ l₀ / ((k : ℝ) + 2) := div_nonneg hl₀.1 (hk2 k).le
    exact ⟨by simp only [ha]; linarith, by simp only [ha]; linarith [hl₀.2]⟩
  have hb_mem : ∀ k, b k ∈ Icc 0 c := fun k ↦ by
    have h1 := hdiv k (sub_nonneg.2 hl₀.2)
    have h2 : 0 ≤ (1 - l₀) / ((k : ℝ) + 2) := div_nonneg (sub_nonneg.2 hl₀.2) (hk2 k).le
    exact ⟨by simp only [hb]; linarith [hl₀.1], by simp only [hb, hc]; linarith⟩
  have ha_lt : ∀ k, a k < l₀ ∨ a k = 0 := fun k ↦ by
    rcases eq_or_lt_of_le hl₀.1 with h | h
    · right
      simp [ha, ← h]
    · left
      simp only [ha, sub_lt_self_iff]
      exact div_pos h (hk2 k)
  have hb_gt : ∀ k, l₀ < b k ∨ b k = 1 := fun k ↦ by
    rcases eq_or_lt_of_le hl₀.2 with h | h
    · right
      simp [hb, h]
    · left
      simp only [hb, lt_add_iff_pos_right]
      exact div_pos (sub_pos.2 h) (hk2 k)
  have hlim0 : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have ha_lim : Tendsto a atTop (𝓝 l₀) := by
    have h := (tendsto_const_nhds (x := l₀)).sub (hlim0.const_mul l₀)
    rw [mul_zero, sub_zero] at h
    refine h.congr fun k ↦ ?_
    simp only [ha]
    ring
  have hb_lim : Tendsto b atTop (𝓝 l₀) := by
    have h := (tendsto_const_nhds (x := l₀)).add (hlim0.const_mul (1 - l₀))
    rw [mul_zero, add_zero] at h
    refine h.congr fun k ↦ ?_
    simp only [hb]
    ring
  have hint_le : ∀ l ∈ Icc 0 c, Integrable (logBetFactor l) Q := fun l hl ↦
    integrable_logBetFactor_of_le hQ0 hlog hl.1 hl.2 hc1 hintc
  filter_upwards [ae_forall_ne_zero hQ0, ae_tendsto_average hint₀,
    ae_all_iff.2 fun k ↦ ae_tendsto_average (hint_le _ (ha_mem k)),
    ae_all_iff.2 fun k ↦ ae_tendsto_average (hint_le _ (hb_mem k)),
    ae_all_iff.2 fun k ↦ ae_tendsto_average ((hint_le _ (ha_mem k)).sup (hint_le _ (hb_mem k))),
    ae_all_iff.2 fun k ↦ ae_tendsto_average ((hint_le _ (ha_mem k)).inf (hint_le _ (hb_mem k)))]
    with x hx hL₀ hA hB hU hV l hl hmax
  have hIcc : ∀ l ∈ Icc 0 c, l ∈ Icc (0 : ℝ) 1 := fun l hl ↦ ⟨hl.1, hl.2.trans hc1⟩
  have hab : ∀ k, ∀ᶠ n in atTop, a k ≤ l n ∧ l n ≤ b k := by
    intro k
    have hlow : ∀ᶠ n in atTop, a k ≤ l n := by
      rcases ha_lt k with h | h
      · have hlt := integral_logBetFactor_lt hQ0 hQ1 hlog hl₀ hint₀ hmax₀ (hIcc _ (ha_mem k))
          h.ne (hint_le _ (ha_mem k))
        filter_upwards [eventually_notMem_uIcc hx hl hmax hl₀
          (((hA k).sub hL₀).congr fun n ↦ by rw [Finset.sum_sub_distrib, mul_sub])
          (sub_neg.2 hlt)] with n hn
        exact not_lt.1 fun h' ↦ hn (Set.mem_uIcc.2 (Or.inl ⟨h'.le, h.le⟩))
      · exact Eventually.of_forall fun n ↦ h ▸ (hl n).1
    have hup : ∀ᶠ n in atTop, l n ≤ b k := by
      rcases hb_gt k with h | h
      · have hlt := integral_logBetFactor_lt hQ0 hQ1 hlog hl₀ hint₀ hmax₀ (hIcc _ (hb_mem k))
          h.ne' (hint_le _ (hb_mem k))
        filter_upwards [eventually_notMem_uIcc hx hl hmax hl₀
          (((hB k).sub hL₀).congr fun n ↦ by rw [Finset.sum_sub_distrib, mul_sub])
          (sub_neg.2 hlt)] with n hn
        exact not_lt.1 fun h' ↦ hn (Set.mem_uIcc.2 (Or.inr ⟨h.le, h'.le⟩))
      · exact Eventually.of_forall fun n ↦ h ▸ (hl n).2
    exact hlow.and hup
  exact tendsto_average_logBetFactor hx (fun k ↦ (ha_mem k).1) (fun k ↦ (hb_mem k).2.trans hc1)
    hab hU hV
    (tendsto_integral_comp_logBetFactor hQ0 hlog (φ := max) (continuous_fst.max continuous_snd)
      (fun _ _ ↦ abs_max_le_max_abs_abs) max_self ha_mem hb_mem hc1 hintc hl₀ ha_lim hb_lim)
    (tendsto_integral_comp_logBetFactor hQ0 hlog (φ := min) (continuous_fst.min continuous_snd)
      (fun _ _ ↦ abs_min_le_max_abs_abs) min_self ha_mem hb_mem hc1 hintc hl₀ ha_lim hb_lim)

/-- The growth rate when `log (1 + E)` has an infinite mean: the supremum is `+∞`, and so is the
limit. The fractions eventually stay above some `a > 0`, and below some `b < 1` if the negative
part of `log E` has an infinite mean. -/
private lemma ae_tendsto_average_of_lintegral_eq_top [IsProbabilityMeasure Q] (hQ0 : Q {0} = 0)
    (hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + (e : ℝ))) ∂Q = ⊤) :
    (⨆ c ∈ Icc (0 : ℝ) 1,
        ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * ((e : ℝ) - 1))) ∂Q) = ⊤ ∧
      ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ Q), ∀ l : ℕ → ℝ, (∀ n, l n ∈ Icc (0 : ℝ) 1) →
        (∀ n, IsMaxOn (fun c ↦ ∑ i ∈ Finset.range (n + 1), logBetFactor c (x i)) (Icc 0 1)
          (l (n + 1))) →
        Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, logBetFactor (l i) (x i)) atTop
          atTop := by
  have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hχ0 : ∀ e : ℝ≥0, 0 ≤ Real.log (1 + (e : ℝ)) := fun e ↦ Real.log_nonneg (by simp)
  refine ⟨eq_top_iff.2 (le_iSup₂_of_le (1 / 2) hhalf ?_), ?_⟩
  · have hneg : ∫⁻ e, ENNReal.ofReal (-logBetFactor (1 / 2) e) ∂Q ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal (Real.log 2) ∂Q)
        (by simp [lintegral_const]) (lintegral_mono fun e ↦ ?_)
      refine ENNReal.ofReal_le_ofReal ?_
      linarith [logBetFactor_one_half e, hχ0 e]
    rw [eintegral_congr fun e : ℝ≥0 ↦ ENNReal.log_ofReal_of_pos (by linarith [e.coe_nonneg] :
      (0 : ℝ) < 1 + 1 / 2 * ((e : ℝ) - 1)), eintegral]
    simp only [EReal.real_coe_toENNReal, ← EReal.coe_neg]
    rw [show ∫⁻ e, ENNReal.ofReal (Real.log (1 + 1 / 2 * ((e : ℝ) - 1))) ∂Q = ⊤ from
      lintegral_ofReal_logBetFactor_one_half_eq_top hlog, EReal.coe_ennreal_top]
    exact (EReal.top_sub (EReal.coe_ennreal_eq_top_iff.not.2 hneg)).ge
  obtain ⟨a, ha0, ha2, hda⟩ := exists_integral_logBetFactor_sub_one_half_neg_of_lt hlog
  have hinta := integrable_logBetFactor_sub_one_half (Q := Q) ha0 (ha2.trans (by norm_num))
  have hχm : Measurable fun e : ℝ≥0 ↦ Real.log (1 + (e : ℝ)) := by fun_prop
  by_cases hlog1 : ∫⁻ e, ENNReal.ofReal (-logBetFactor 1 e) ∂Q = ⊤
  · -- the fractions eventually stay in `[a, b] ⊆ (0, 1)`
    obtain ⟨b, hb2, hb1, hdb⟩ := exists_integral_logBetFactor_sub_one_half_neg_of_gt hQ0 hlog1
    have hintb := integrable_logBetFactor_sub_one_half (Q := Q) (hb2.trans' (by norm_num)) hb1
    have hm : 0 < min a (1 - b) := lt_min ha0 (by linarith)
    filter_upwards [ae_forall_ne_zero hQ0, ae_tendsto_average hinta, ae_tendsto_average hintb,
      ae_tendsto_average_add_atTop (integrable_const (Real.log (min a (1 - b)))) hχm
        (by simp [ENNReal.ofReal_of_nonpos (neg_nonpos.2 (hχ0 _))]) hlog]
      with x hx hA hB hT l hl hmax
    refine tendsto_average_atTop ?_ hT
    filter_upwards [eventually_notMem_uIcc hx hl hmax hhalf hA hda,
      eventually_notMem_uIcc hx hl hmax hhalf hB hdb] with i ha' hb'
    have h1 : a ≤ l i := not_lt.1 fun h ↦ ha' (Set.mem_uIcc.2 (Or.inl ⟨h.le, ha2.le⟩))
    have h2 : l i ≤ b := not_lt.1 fun h ↦ hb' (Set.mem_uIcc.2 (Or.inr ⟨hb2.le, h.le⟩))
    exact log_add_log_one_add_le_logBetFactor hm ((min_le_left _ _).trans h1)
      ((min_le_right _ _).trans (by linarith)) (x i)
  · -- the fractions eventually stay in `[a, 1]`, and `log E` has a positive part of infinite
    -- mean and a negative part of finite mean
    have hpos : ∫⁻ e, ENNReal.ofReal (logBetFactor 1 e) ∂Q = ⊤ := by
      refine lintegral_ofReal_eq_top_of_le_add (ENNReal.ofReal_ne_top (r := Real.log 2))
        (fun e ↦ ?_) hlog
      rcases le_total (e : ℝ) 1 with he | he
      · exact (ENNReal.ofReal_le_ofReal (Real.log_le_log (by positivity) (by linarith))).trans
          le_add_self
      · rw [← ENNReal.ofReal_add (logBetFactor_nonneg zero_le_one he) (Real.log_nonneg one_le_two),
          logBetFactor_one, ← Real.log_mul (by positivity) two_ne_zero]
        exact ENNReal.ofReal_le_ofReal (Real.log_le_log (by positivity) (by linarith))
    filter_upwards [ae_forall_ne_zero hQ0, ae_tendsto_average hinta,
      ae_tendsto_average_add_atTop (integrable_const (Real.log a)) (measurable_logBetFactor 1)
        hlog1 hpos] with x hx hA hT l hl hmax
    refine tendsto_average_atTop ?_ hT
    filter_upwards [eventually_notMem_uIcc hx hl hmax hhalf hA hda] with i ha'
    rw [logBetFactor_one]
    exact log_add_log_le_logBetFactor ha0
      (not_lt.1 fun h ↦ ha' (Set.mem_uIcc.2 (Or.inl ⟨h.le, ha2.le⟩))) (hl i).2 (hx i)

/-- The growth rate of follow-the-leader in terms of the real logarithms of the rounds. -/
private lemma ae_tendsto_average_logBetFactor [IsProbabilityMeasure Q] (hQ0 : Q {0} = 0) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ Q), ∀ l : ℕ → ℝ, (∀ n, l n ∈ Icc (0 : ℝ) 1) →
      (∀ n, IsMaxOn (fun c ↦ ∑ i ∈ Finset.range (n + 1), logBetFactor c (x i)) (Icc 0 1)
        (l (n + 1))) →
      Tendsto (fun n : ℕ ↦
          (((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, logBetFactor (l i) (x i) : ℝ) : EReal)) atTop
        (𝓝 (⨆ c ∈ Icc (0 : ℝ) 1,
          ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * ((e : ℝ) - 1))) ∂Q)) := by
  by_cases hQ1 : Q {1} = 1
  · obtain ⟨hsup, h⟩ := ae_tendsto_average_of_measure_one_eq_one hQ1
    rw [hsup]
    filter_upwards [h] with x hx l _ _
    exact EReal.tendsto_coe.2 (hx l)
  by_cases hlog : ∫⁻ e, ENNReal.ofReal (Real.log (1 + (e : ℝ))) ∂Q = ⊤
  · obtain ⟨hsup, h⟩ := ae_tendsto_average_of_lintegral_eq_top hQ0 hlog
    rw [hsup]
    filter_upwards [h] with x hx l hl hmax
    exact EReal.tendsto_coe_nhds_top_iff.2 (hx l hl hmax)
  · obtain ⟨L, hsup, h⟩ := ae_tendsto_average_of_lintegral_ne_top hQ0 hQ1 hlog
    rw [hsup]
    filter_upwards [h] with x hx l hl hmax
    exact EReal.tendsto_coe.2 (hx l hl hmax)

/-! ### Main results -/

/-- **Follow-the-leader betting grows at the best rate of a constant fraction when no e-value
vanishes**
[WSJ26, Remark 2.3]. Let `Q` be a probability measure on `ℝ≥0` with `Q {0} = 0`. Almost surely
under `Q^ℕ`, for all fractions `l n ∈ [0, 1]` such that `l (n + 1)` maximizes over `[0, 1]` the
wealth `∏ k ≤ n, (1 + c * (ω k - 1))` of a constant fraction `c`, the logarithm of the wealth
`∏ k < n, (1 + l k * (ω k - 1))` divided by `n` tends to the best growth rate
`⨆ c ∈ [0, 1], 𝔼_Q log (1 + c * (E - 1))` of a constant fraction. That rate is `+∞` when
`log (1 + E)` has an infinite mean. The fraction `l 0` is arbitrary in `[0, 1]`. -/
theorem ae_tendsto_log_prod_followTheLeader_div (Q : Measure ℝ≥0) [IsProbabilityMeasure Q]
    (hQ0 : Q {0} = 0) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q), ∀ l : ℕ → ℝ, (∀ n, l n ∈ Icc (0 : ℝ) 1) →
      (∀ n, IsMaxOn (fun c : ℝ ↦
        ∏ k ∈ Finset.range (n + 1), ENNReal.ofReal (1 + c * ((ω k : ℝ) - 1))) (Icc 0 1)
          (l (n + 1))) →
      Tendsto (fun n : ℕ ↦
          ENNReal.log (∏ k ∈ Finset.range n, ENNReal.ofReal (1 + l k * ((ω k : ℝ) - 1))) / n)
        atTop (𝓝 (⨆ c ∈ Icc (0 : ℝ) 1,
          ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * ((e : ℝ) - 1))) ∂Q)) := by
  filter_upwards [ae_forall_ne_zero hQ0, ae_tendsto_average_logBetFactor hQ0]
    with ω hω h l hl hmax
  refine (h l hl fun n ↦ isMaxOn_sum_logBetFactor hω (hl (n + 1)) (hmax n)).congr fun n ↦ ?_
  rw [log_prod_ofReal_eq hω hl, ← EReal.coe_natCast, ← EReal.coe_div, div_eq_inv_mul]

/-- **Follow-the-leader betting goes bankrupt with positive probability when some e-values
vanish** [WSJ26, Remark 2.3]. Let `Q` be a probability measure on `ℝ≥0` that charges `0` and
`(1, ∞)`. With positive probability under `Q^ℕ`, the wealth `∏ k < 2, (1 + l k * (ω k - 1))`
after two rounds is `0` for every fraction `l 1 ≤ 1` that maximizes over `[0, 1]` the factor
`1 + c * (ω 0 - 1)` of the first round, whatever `l 0`: on the event `{1 < ω 0, ω 1 = 0}`, such a
fraction is `1`. -/
theorem measure_followTheLeader_bankrupt_pos (Q : Measure ℝ≥0) [IsProbabilityMeasure Q]
    (hQ0 : Q {0} ≠ 0) (hQ1 : Q (Ioi 1) ≠ 0) :
    0 < Measure.infinitePi (fun _ : ℕ ↦ Q) {ω | ∀ l : ℕ → ℝ, l 1 ≤ 1 →
      IsMaxOn (fun c : ℝ ↦ ENNReal.ofReal (1 + c * ((ω 0 : ℝ) - 1))) (Icc 0 1) (l 1) →
      ∏ k ∈ Finset.range 2, ENNReal.ofReal (1 + l k * ((ω k : ℝ) - 1)) = 0} := by
  -- the event `{1 < ω 0, ω 1 = 0}` has positive probability
  set t : ℕ → Set ℝ≥0 := fun i ↦ if i = 0 then Ioi 1 else {0} with ht
  have hpos :
      0 < Measure.infinitePi (fun _ : ℕ ↦ Q) (Set.pi ((({0, 1} : Finset ℕ)) : Set ℕ) t) := by
    rw [Measure.infinitePi_pi (μ := fun _ : ℕ ↦ Q) (fun i _ ↦ by
      simp only [ht]
      split_ifs
      exacts [measurableSet_Ioi, measurableSet_singleton 0]), Finset.prod_pair zero_ne_one]
    simp only [ht, ↓reduceIte, one_ne_zero]
    exact ENNReal.mul_pos hQ1 hQ0
  refine hpos.trans_le (measure_mono fun ω hω l hl hmax ↦ ?_)
  have h0 : (1 : ℝ) < ω 0 := by exact_mod_cast (show 1 < ω 0 by simpa [t] using hω 0 (by simp))
  have h1 : ω 1 = 0 := by simpa [t] using hω 1 (by simp)
  -- on that event, the first factor is maximized by the fraction `1` only
  have hb : l 1 = 1 := by
    refine le_antisymm hl ?_
    have h := isMaxOn_iff.1 hmax 1 ⟨zero_le_one, le_rfl⟩
    rw [ENNReal.ofReal_le_ofReal_iff'] at h
    rcases h with h | h
    · nlinarith
    · linarith
  simp [Finset.prod_range_succ, hb, h1]

end ProbabilityTheory
