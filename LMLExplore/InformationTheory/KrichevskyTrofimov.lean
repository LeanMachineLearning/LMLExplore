/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
public import TauCeti.Analysis.SpecialFunctions.Beta
public import TauCeti.Probability.Distributions.Beta.Basic

/-!
# The Krichevsky–Trofimov mixture

The *Krichevsky–Trofimov distribution* [KT81] on `{0, 1} ^ n` mixes the likelihoods
`p_u(x) = u ^ k (1 - u) ^ m` of the Bernoulli laws, where `k` and `m` are the numbers of ones and
zeros of `x`, over the arcsine law `Beta(1/2, 1/2)` of the mean `u`:
`kt(x) = ∫ u ^ k (1 - u) ^ m d Beta(1/2, 1/2)(u)`. It is a universal distribution: it approximates
every Bernoulli likelihood within a factor `2 √n` [GK16, Lemma 11], uniformly in the sequence `x`.
In the form of log-likelihood ratios, `n d(k / n, p) ≤ log (2 √n kt(k, m) / (p ^ k (1 - p) ^ m))`
for every `p ∈ (0, 1)`, where `d` is the binary relative entropy: this is what turns the mixture of
the likelihood ratios of the Bernoulli laws into a deviation inequality for the empirical mean of
Bernoulli observations, and the informational threshold of the GLRT for Bernoulli arms
[GK16, Theorem 10].

## Main statements

* `LMLExplore.integral_pow_mul_one_sub_pow_betaMeasure`: the moments
  `∫ u ^ k (1 - u) ^ m d Beta(a, b) = B(a + k, b + m) / B(a, b)` of the beta laws, and
  `LMLExplore.integral_pow_mul_one_sub_pow_betaMeasure_pos`: they are positive.
* `LMLExplore.pow_mul_one_sub_pow_le_div_pow_mul_div_pow`: the maximum likelihood of `k` ones and
  `m` zeros among the Bernoulli laws is `(k / n) ^ k (m / n) ^ m`.
* `LMLExplore.div_pow_mul_div_pow_le_two_mul_sqrt_mul_integral_betaMeasure`: the maximum
  likelihood `(k / n) ^ k (m / n) ^ m` is at most `2 √n kt(k, m)` [GK16, Lemma 11].
* `LMLExplore.pow_mul_one_sub_pow_le_two_mul_sqrt_mul_integral_betaMeasure`: for every
  `u ∈ [0, 1]`, `u ^ k (1 - u) ^ m ≤ 2 √n kt(k, m)` [GK16, Lemma 11].
* `LMLExplore.mul_klBerReal_div_eq_log`: `n d(k / n, p)` is the log-likelihood ratio of the
  maximum likelihood against the Bernoulli law of mean `p`.
* `LMLExplore.mul_klBerReal_div_le_log_two_mul_sqrt_mul_integral_betaMeasure_div`: the bound in the
  form `n d(k / n, p) ≤ log (2 √n kt(k, m) / (p ^ k (1 - p) ^ m))` of a log-likelihood ratio, for
  `p ∈ (0, 1)`.

## Implementation notes

The proof of the bound is the induction of [WST95, Appendix]: by the recursion of the beta
function, `kt(k, m + 1) = kt(k, m) (m + 1 / 2) / (k + m + 1)`, and the ratio between the maximum
likelihood `(k / n) ^ k (m / n) ^ m` and `kt(k, m)` grows by a factor at most `√((n + 1) / n)` at
each step, which reduces to the two inequalities
`(m + 1) log (m + 1) - m log m - log (m + 1 / 2) ≤ 1` and `1 ≤ (n + 1 / 2) log (1 + 1 / n)`.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2.
* [KT81] R. Krichevsky and V. Trofimov, *The performance of universal encoding*, IEEE Trans.
  Inform. Theory 27 (1981).
* [WST95] F. M. J. Willems, Y. M. Shtarkov and T. J. Tjalkens, *The context-tree weighting
  method: basic properties*, IEEE Trans. Inform. Theory 41 (1995).
-/

public section

open MeasureTheory ProbabilityTheory Real Set

namespace LMLExplore

/-! ### Two inequalities on logarithms -/

/-- `1 ≤ (x + 1 / 2) log (1 + 1 / x)` for `x > 0`: the first term of the series of
`log (1 + 1 / x)` in powers of `1 / (2 x + 1)`. -/
private lemma one_le_add_half_mul_log_one_add_inv {x : ℝ} (hx : 0 < x) :
    1 ≤ (x + 1 / 2) * log (1 + x⁻¹) := by
  have h0 := le_hasSum (Real.hasSum_log_one_add_inv hx) 0 (fun j _ ↦ by positivity)
  simp only [CharP.cast_eq_zero, mul_zero, zero_add, div_one, mul_one, pow_one] at h0
  have hpos : 0 < 2 * x + 1 := by linarith
  calc (1 : ℝ) = (x + 1 / 2) * (2 * (1 / (2 * x + 1))) := by field_simp
    _ ≤ _ := by gcongr

/-- `(1 + t) log (1 + t) - t - t log (1 + t / 2) ≤ 0` for `t ≥ 0`: the function vanishes at `0`
and its derivative `log ((1 + t) / (1 + t / 2)) - t / (2 + t)` is nonpositive. -/
private lemma one_add_mul_log_sub_le {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) * log (1 + t) - t - t * log (1 + t / 2) ≤ 0 := by
  set f : ℝ → ℝ := fun t ↦ (1 + t) * log (1 + t) - t - t * log (1 + t / 2) with hf
  have hderiv : ∀ x, 0 ≤ x →
      HasDerivAt f (log (1 + x) - log (1 + x / 2) - x / (2 + x)) x := by
    intro x hx
    have h1 : (1 + x) ≠ 0 := by linarith
    have h2 : (1 + x / 2) ≠ 0 := by linarith
    have := ((((hasDerivAt_id' x).const_add 1).mul
      (((hasDerivAt_id' x).const_add 1).log h1)).sub (hasDerivAt_id' x)).sub
      ((hasDerivAt_id' x).mul ((((hasDerivAt_id' x).div_const 2).const_add 1).log h2))
    convert this using 1
    field_simp
    ring
  have hanti : AntitoneOn f (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun x hx ↦ (hderiv x hx).continuousAt.continuousWithinAt) ?_ ?_
    · intro x hx
      rw [interior_Ici] at hx
      exact (hderiv x (le_of_lt hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : 0 < x := hx
      rw [(hderiv x hx'.le).deriv]
      have hx0 : 0 < 1 + x / 2 := by linarith
      have : log (1 + x) - log (1 + x / 2) ≤ x / (2 + x) := by
        rw [← log_div (by linarith) hx0.ne']
        refine (log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
        field_simp
        ring
      linarith
  have := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  simpa [hf] using this

/-- `(m + 1) log (m + 1) - m log m - log (m + 1 / 2) ≤ 1` for every `m : ℕ`. -/
private lemma add_one_mul_log_sub_le_one (m : ℕ) :
    ((m : ℝ) + 1) * log ((m : ℝ) + 1) - m * log m - log ((m : ℝ) + 1 / 2) ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : log (1 / 2 : ℝ) = - log 2 := by rw [one_div, log_inv]
    simp only [CharP.cast_eq_zero, zero_add, one_mul, log_one, zero_mul, sub_zero, this]
    have h2 : log 2 < 1 := (log_lt_iff_lt_exp (by norm_num)).2 (by
      linarith [add_one_lt_exp (one_ne_zero (α := ℝ))])
    linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h := one_add_mul_log_sub_le (t := (m : ℝ)⁻¹) (by positivity)
  have e1 : log (1 + (m : ℝ)⁻¹) = log ((m : ℝ) + 1) - log m := by
    rw [← log_div (by positivity) hm'.ne']
    congr 1
    field_simp
  have e2 : log (1 + (m : ℝ)⁻¹ / 2) = log ((m : ℝ) + 1 / 2) - log m := by
    rw [← log_div (by positivity) hm'.ne']
    congr 1
    field_simp
  rw [e1, e2] at h
  have h' := mul_le_mul_of_nonneg_left h hm'.le
  have : (m : ℝ) * ((1 + (m : ℝ)⁻¹) * (log (↑m + 1) - log ↑m) - (m : ℝ)⁻¹ -
      (m : ℝ)⁻¹ * (log (↑m + 1 / 2) - log ↑m)) =
      ((m : ℝ) + 1) * log ((m : ℝ) + 1) - m * log m - log ((m : ℝ) + 1 / 2) - 1 := by
    field_simp
    ring
  rw [this] at h'
  linarith

/-- The step of the induction: `(m + 1) ^ (m + 1) √n n ^ n ≤ √(n + 1) (m + 1 / 2) m ^ m (n + 1) ^ n`
for `n ≥ 1`. -/
private lemma add_one_pow_mul_sqrt_mul_pow_le (m n : ℕ) (hn : 1 ≤ n) :
    ((m : ℝ) + 1) ^ (m + 1) * √(n : ℝ) * (n : ℝ) ^ n ≤
      √((n : ℝ) + 1) * ((m : ℝ) + 1 / 2) * (m : ℝ) ^ m * ((n : ℝ) + 1) ^ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmm : (0 : ℝ) < (m : ℝ) ^ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact pow_pos (by exact_mod_cast hm) m
  have hL : 0 < ((m : ℝ) + 1) ^ (m + 1) * √(n : ℝ) * (n : ℝ) ^ n := by positivity
  have hR : 0 < √((n : ℝ) + 1) * ((m : ℝ) + 1 / 2) * (m : ℝ) ^ m * ((n : ℝ) + 1) ^ n := by
    positivity
  rw [← log_le_log_iff hL hR]
  rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_pow, log_pow, log_pow, log_pow,
    log_sqrt hn'.le, log_sqrt (by positivity)]
  have hG := add_one_mul_log_sub_le_one m
  have hH := one_le_add_half_mul_log_one_add_inv hn'
  have e : log (1 + (n : ℝ)⁻¹) = log ((n : ℝ) + 1) - log n := by
    rw [← log_div (by positivity) hn'.ne']
    congr 1
    field_simp
  rw [e] at hH
  push_cast
  nlinarith

/-! ### The Krichevsky–Trofimov bound -/

/-- The moments of the beta laws: for `a, b > 0` and `k, m : ℕ`,
`∫ u ^ k (1 - u) ^ m d Beta(a, b) = B(a + k, b + m) / B(a, b)`. -/
lemma integral_pow_mul_one_sub_pow_betaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k m : ℕ) :
    ∫ u, u ^ k * (1 - u) ^ m ∂betaMeasure a b = beta (a + k) (b + m) / beta a b := by
  have h := TauCeti.Probability.integral_rpow_mul_one_sub_rpow_betaMeasure (q := k) (s := m)
    ha hb (by positivity) (by positivity)
  simpa only [Real.rpow_natCast] using h

/-- The moments `∫ u ^ k (1 - u) ^ m d Beta(a, b)` of the beta laws are positive, for `a, b > 0`. -/
lemma integral_pow_mul_one_sub_pow_betaMeasure_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k m : ℕ) : 0 < ∫ u, u ^ k * (1 - u) ^ m ∂betaMeasure a b := by
  rw [integral_pow_mul_one_sub_pow_betaMeasure ha hb]
  exact div_pos (beta_pos (by positivity) (by positivity)) (beta_pos ha hb)

/-- One more zero in the sequence: `B(1/2 + k, 1/2 + (m + 1)) = (m + 1/2) / (k + m + 1) B(1/2 + k,
1/2 + m)`. -/
private lemma beta_one_half_add_add_one (k m : ℕ) :
    beta (1 / 2 + k) (1 / 2 + (m + 1)) =
      ((m : ℝ) + 1 / 2) / ((k : ℝ) + m + 1) * beta (1 / 2 + k) (1 / 2 + m) := by
  rw [beta_comm, beta_comm (1 / 2 + (k : ℝ))]
  have : (1 / 2 : ℝ) + ((m : ℝ) + 1) = (1 / 2 + m) + 1 := by ring
  rw [this, beta_add_one_left (by positivity) (by positivity)]
  congr 1
  ring

/-- The step of the induction of `pow_mul_pow_mul_beta_le`, adding one zero to the sequence. -/
private lemma pow_mul_pow_mul_beta_le_succ {k m : ℕ} (hn : 1 ≤ k + m)
    (h : (k : ℝ) ^ k * (m : ℝ) ^ m * beta (1 / 2) (1 / 2) ≤
      2 * √((k : ℝ) + m) * ((k : ℝ) + m) ^ (k + m) * beta (1 / 2 + k) (1 / 2 + m)) :
    (k : ℝ) ^ k * ((m + 1 : ℕ) : ℝ) ^ (m + 1) * beta (1 / 2) (1 / 2) ≤
      2 * √((k : ℝ) + (m + 1 : ℕ)) * ((k : ℝ) + (m + 1 : ℕ)) ^ (k + (m + 1)) *
        beta (1 / 2 + k) (1 / 2 + (m + 1 : ℕ)) := by
  push_cast
  rw [beta_one_half_add_add_one]
  have hs := add_one_pow_mul_sqrt_mul_pow_le m (k + m) hn
  push_cast at hs
  have hn' : (0 : ℝ) < k + m := by exact_mod_cast hn
  have hpos : 0 < √((k : ℝ) + m) * ((k : ℝ) + m) ^ (k + m) := by positivity
  have hB : 0 ≤ beta (1 / 2) (1 / 2) := (beta_pos (by norm_num) (by norm_num)).le
  refine le_of_mul_le_mul_left ?_ hpos
  calc √((k : ℝ) + m) * ((k : ℝ) + m) ^ (k + m) *
        ((k : ℝ) ^ k * ((m : ℝ) + 1) ^ (m + 1) * beta (1 / 2) (1 / 2))
      = (k : ℝ) ^ k * beta (1 / 2) (1 / 2) *
        (((m : ℝ) + 1) ^ (m + 1) * √((k : ℝ) + m) * ((k : ℝ) + m) ^ (k + m)) := by ring
    _ ≤ (k : ℝ) ^ k * beta (1 / 2) (1 / 2) * (√((k : ℝ) + m + 1) * ((m : ℝ) + 1 / 2) *
        (m : ℝ) ^ m * ((k : ℝ) + m + 1) ^ (k + m)) := by gcongr
    _ = √((k : ℝ) + m + 1) * ((m : ℝ) + 1 / 2) * ((k : ℝ) + m + 1) ^ (k + m) *
        ((k : ℝ) ^ k * (m : ℝ) ^ m * beta (1 / 2) (1 / 2)) := by ring
    _ ≤ √((k : ℝ) + m + 1) * ((m : ℝ) + 1 / 2) * ((k : ℝ) + m + 1) ^ (k + m) *
        (2 * √((k : ℝ) + m) * ((k : ℝ) + m) ^ (k + m) * beta (1 / 2 + k) (1 / 2 + m)) := by
      gcongr
    _ = √((k : ℝ) + m) * ((k : ℝ) + m) ^ (k + m) *
        (2 * √((k : ℝ) + (m + 1)) * ((k : ℝ) + (m + 1)) ^ (k + (m + 1)) *
          (((m : ℝ) + 1 / 2) / ((k : ℝ) + m + 1) * beta (1 / 2 + k) (1 / 2 + m))) := by
      have : (k : ℝ) + m + 1 ≠ 0 := by positivity
      rw [← add_assoc, show k + (m + 1) = k + m + 1 from rfl, pow_succ]
      field_simp

/-- The Krichevsky–Trofimov bound in the form of [WST95]:
`k ^ k m ^ m B(1/2, 1/2) ≤ 2 √n n ^ n B(1/2 + k, 1/2 + m)` for `n = k + m ≥ 1`. -/
private lemma pow_mul_pow_mul_beta_le (k m : ℕ) (hn : 1 ≤ k + m) :
    (k : ℝ) ^ k * (m : ℝ) ^ m * beta (1 / 2) (1 / 2) ≤
      2 * √((k : ℝ) + m) * ((k : ℝ) + m) ^ (k + m) * beta (1 / 2 + k) (1 / 2 + m) := by
  set P : ℕ → ℕ → Prop := fun k m ↦ (k : ℝ) ^ k * (m : ℝ) ^ m * beta (1 / 2) (1 / 2) ≤
      2 * √((k : ℝ) + m) * ((k : ℝ) + m) ^ (k + m) * beta (1 / 2 + k) (1 / 2 + m) with hP
  have step : ∀ k m, 1 ≤ k + m → P k m → P k (m + 1) := fun _ _ hn h ↦
    pow_mul_pow_mul_beta_le_succ hn h
  have symm : ∀ k m, P k m → P m k := by
    intro k m h
    simp only [hP] at h ⊢
    rw [add_comm (m : ℝ), add_comm m, beta_comm (1 / 2 + (m : ℝ))]
    linarith
  have base : P 0 1 := by
    simp only [hP]
    have := beta_one_half_add_add_one 0 0
    norm_num at this ⊢
    rw [this]
    linarith
  have h0 : ∀ m, 1 ≤ m → P 0 m := fun m hm ↦
    Nat.le_induction base (fun m hm h ↦ step 0 m (by omega) h) m hm
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact h0 m (by omega)
  induction m with
  | zero => exact symm 0 k (h0 k hk)
  | succ m ih => exact step k m (by omega) (ih (by omega))

/-- **The Krichevsky–Trofimov bound** [GK16, Lemma 11]: the maximum likelihood
`(k / n) ^ k (m / n) ^ m` of a sequence of `n = k + m ≥ 1` observations with `k` ones and `m` zeros
is at most `2 √n` times its Krichevsky–Trofimov probability
`kt(k, m) = ∫ u ^ k (1 - u) ^ m d Beta(1/2, 1/2)(u)`. -/
theorem div_pow_mul_div_pow_le_two_mul_sqrt_mul_integral_betaMeasure {k m n : ℕ}
    (hkm : k + m = n) (hn : 0 < n) :
    ((k : ℝ) / n) ^ k * ((m : ℝ) / n) ^ m ≤
      2 * √(n : ℝ) * ∫ u, u ^ k * (1 - u) ^ m ∂betaMeasure (1 / 2) (1 / 2) := by
  have h := pow_mul_pow_mul_beta_le k m (by omega)
  have hkm' : (k : ℝ) + m = n := by exact_mod_cast hkm
  rw [hkm', hkm] at h
  rw [integral_pow_mul_one_sub_pow_betaMeasure (by norm_num) (by norm_num), div_pow, div_pow,
    div_mul_div_comm, ← pow_add, hkm]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hB := beta_pos (α := 1 / 2) (β := 1 / 2) (by norm_num) (by norm_num)
  rw [div_le_iff₀ (by positivity), mul_div_assoc', mul_comm _ ((n : ℝ) ^ n),
    ← mul_div_assoc, le_div_iff₀ hB]
  linarith

/-- The frequency factor `(k / n) ^ k` of the maximum likelihood is positive for `n > 0`, including
for `k = 0`. -/
private lemma div_pow_self_pos (k : ℕ) {n : ℕ} (hn : 0 < n) : 0 < ((k : ℝ) / n) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · positivity

/-- The log-likelihood ratio of the maximum likelihood against the Bernoulli law of mean
`p ∈ (0, 1)`, for a sequence of `n = k + m ≥ 1` observations with `k` ones and `m` zeros:
`n d(k / n, p) = log ((k / n) ^ k (m / n) ^ m / (p ^ k (1 - p) ^ m))`. -/
lemma mul_klBerReal_div_eq_log {k m n : ℕ} (hkm : k + m = n) (hn : 0 < n) {p : ℝ}
    (hp : p ∈ Ioo 0 1) :
    (n : ℝ) * klBerReal (k / n) p =
      log (((k : ℝ) / n) ^ k * ((m : ℝ) / n) ^ m / (p ^ k * (1 - p) ^ m)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hkm' : (k : ℝ) + m = n := by exact_mod_cast hkm
  have h1 : 1 - (k : ℝ) / n = m / n := by
    field_simp
    linarith
  have hk : ((k : ℝ) / n / p) ^ k ≠ 0 := by
    rw [div_pow]
    exact (div_pos (div_pow_self_pos k hn) (pow_pos hp.1 _)).ne'
  have hm : ((m : ℝ) / n / (1 - p)) ^ m ≠ 0 := by
    rw [div_pow]
    exact (div_pos (div_pow_self_pos m hn) (pow_pos (sub_pos.2 hp.2) _)).ne'
  rw [mul_div_mul_comm, ← div_pow, ← div_pow, log_mul hk hm, log_pow, log_pow, klBerReal_def, h1,
    mul_add, ← mul_assoc, ← mul_assoc, mul_div_cancel₀ _ hn'.ne', mul_div_cancel₀ _ hn'.ne']

/-- **The Krichevsky–Trofimov bound for the log-likelihood ratio** [GK16, Lemma 11]: for a
sequence of `n = k + m ≥ 1` observations with `k` ones and `m` zeros and `p ∈ (0, 1)`,
`n d(k / n, p) ≤ log (2 √n kt(k, m) / (p ^ k (1 - p) ^ m))`, where
`kt(k, m) / (p ^ k (1 - p) ^ m)` is the likelihood ratio of the Krichevsky–Trofimov mixture against
the Bernoulli law of mean `p`. -/
theorem mul_klBerReal_div_le_log_two_mul_sqrt_mul_integral_betaMeasure_div {k m n : ℕ}
    (hkm : k + m = n) (hn : 0 < n) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    (n : ℝ) * klBerReal (k / n) p ≤
      log (2 * √(n : ℝ) * ((∫ u, u ^ k * (1 - u) ^ m ∂betaMeasure (1 / 2) (1 / 2)) /
        (p ^ k * (1 - p) ^ m))) := by
  rw [mul_klBerReal_div_eq_log hkm hn hp, ← mul_div_assoc]
  have hq : 0 < p ^ k * (1 - p) ^ m := mul_pos (pow_pos hp.1 _) (pow_pos (sub_pos.2 hp.2) _)
  exact log_le_log (div_pos (mul_pos (div_pow_self_pos k hn) (div_pow_self_pos m hn)) hq)
    (div_le_div_of_nonneg_right (div_pow_mul_div_pow_le_two_mul_sqrt_mul_integral_betaMeasure
      hkm hn) hq.le)

/-- The maximum likelihood of a Bernoulli sample: `u ^ k (1 - u) ^ m ≤ (k / n) ^ k (m / n) ^ m`
for every `u ∈ [0, 1]` and `n = k + m`. -/
lemma pow_mul_one_sub_pow_le_div_pow_mul_div_pow {k m n : ℕ} (hkm : k + m = n) {u : ℝ}
    (hu : u ∈ Icc 0 1) :
    u ^ k * (1 - u) ^ m ≤ ((k : ℝ) / n) ^ k * ((m : ℝ) / n) ^ m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨rfl, rfl⟩ : k = 0 ∧ m = 0 := by omega
    simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hkm' : (k : ℝ) + m = n := by exact_mod_cast hkm
  have hR : 0 < ((k : ℝ) / n) ^ k * ((m : ℝ) / n) ^ m :=
    mul_pos (div_pow_self_pos k hn) (div_pow_self_pos m hn)
  -- at `u = 0` or `u = 1` the likelihood is `0` unless the sample is constant, where both are `1`
  rcases hu.1.eq_or_lt with rfl | hu0
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain rfl : m = n := by omega
      simp [div_self hn'.ne']
    · simp [zero_pow hk.ne', hR.le]
  rcases hu.2.eq_or_lt with rfl | hu1
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · obtain rfl : k = n := by omega
      simp [div_self hn'.ne']
    · simp [zero_pow hm.ne', hR.le]
  -- for `u ∈ (0, 1)`, the ratio of the two likelihoods is `exp (n d(k / n, u)) ≥ 1`
  have hkn : (k : ℝ) / n ∈ Icc 0 1 := ⟨by positivity, by
    rw [div_le_one hn']
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]⟩
  have hq : 0 < u ^ k * (1 - u) ^ m := mul_pos (pow_pos hu0 _) (pow_pos (sub_pos.2 hu1) _)
  have hlog : 0 ≤ log (((k : ℝ) / n) ^ k * ((m : ℝ) / n) ^ m / (u ^ k * (1 - u) ^ m)) := by
    rw [← mul_klBerReal_div_eq_log hkm hn ⟨hu0, hu1⟩]
    exact mul_nonneg hn'.le (klBerReal_nonneg hkn hu (klBer_ne_top ⟨hu0, hu1⟩))
  rwa [log_nonneg_iff (div_pos hR hq), one_le_div hq] at hlog

/-- **The Krichevsky–Trofimov bound** [GK16, Lemma 11]: for every `u ∈ [0, 1]`, the likelihood
`u ^ k (1 - u) ^ m` of a sequence of `n = k + m ≥ 1` observations with `k` ones and `m` zeros under
the Bernoulli law of mean `u` is at most `2 √n` times its Krichevsky–Trofimov probability
`kt(k, m) = ∫ v ^ k (1 - v) ^ m d Beta(1/2, 1/2)(v)`. -/
theorem pow_mul_one_sub_pow_le_two_mul_sqrt_mul_integral_betaMeasure {k m n : ℕ}
    (hkm : k + m = n) (hn : 0 < n) {u : ℝ} (hu : u ∈ Icc 0 1) :
    u ^ k * (1 - u) ^ m ≤
      2 * √(n : ℝ) * ∫ v, v ^ k * (1 - v) ^ m ∂betaMeasure (1 / 2) (1 / 2) :=
  (pow_mul_one_sub_pow_le_div_pow_mul_div_pow hkm hu).trans
    (div_pow_mul_div_pow_le_two_mul_sqrt_mul_integral_betaMeasure hkm hn)

end LMLExplore
