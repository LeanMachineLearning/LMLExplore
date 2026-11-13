/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
public import TauCeti.Analysis.SpecialFunctions.Beta
public import LMLExplore.Probability.Distributions.Beta
public import LMLExplore.Analysis.SpecialFunctions.Log.Basic

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

* `LMLExplore.div_pow_mul_div_pow_le_two_mul_sqrt_mul_integral_betaMeasure`: the maximum
  likelihood `(k / n) ^ k (m / n) ^ m` is at most `2 √n kt(k, m)` [GK16, Lemma 11].
* `LMLExplore.pow_mul_one_sub_pow_le_two_mul_sqrt_mul_integral_betaMeasure`: for every
  `u ∈ [0, 1]`, `u ^ k (1 - u) ^ m ≤ 2 √n kt(k, m)` [GK16, Lemma 11].
* `LMLExplore.mul_klBerReal_div_le_log_two_mul_sqrt_mul_integral_betaMeasure_div`: the bound in the
  form `n d(k / n, p) ≤ log (2 √n kt(k, m) / (p ^ k (1 - p) ^ m))` of a log-likelihood ratio, for
  `p ∈ (0, 1)`.

## Implementation notes

The proof of the bound is the induction of [WST95, Appendix]: by the recursion of the beta
function, `kt(k, m + 1) = kt(k, m) (m + 1 / 2) / (k + m + 1)`, and the ratio between the maximum
likelihood `(k / n) ^ k (m / n) ^ m` and `kt(k, m)` grows by a factor at most `√((n + 1) / n)` at
each step, which reduces to the two inequalities
`(m + 1) log (m + 1) - m log m - log (m + 1 / 2) ≤ 1` and `1 ≤ (n + 1 / 2) log (1 + 1 / n)`.

This file is adapted from `InformationTheory/KrichevskyTrofimov.lean` of the formalization in
RemyDegenne/Garivier2016Optimal (commit 53ac67e4, directory `ForLMLExplore/`).

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
  simp (disch := positivity) only [log_mul, log_pow, log_sqrt]
  have hG := add_one_mul_log_sub_le_one m
  have hH := Real.one_le_add_half_mul_log_one_add_inv hn'
  have e : log (1 + (n : ℝ)⁻¹) = log ((n : ℝ) + 1) - log n := by
    rw [inv_eq_one_div, log_one_add_div hn'.ne' (by positivity)]
  rw [e] at hH
  push_cast
  nlinarith

/-! ### The Krichevsky–Trofimov bound -/

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
      rw [← add_assoc, ← Nat.add_assoc, pow_succ]
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
    simp only [Nat.cast_zero, Nat.cast_one, add_zero, zero_add, pow_zero, pow_one, one_mul,
      mul_one, sqrt_one] at this ⊢
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
  exact log_le_log (div_pos (div_pow_mul_div_pow_pos k m hn) hq)
    (div_le_div_of_nonneg_right (div_pow_mul_div_pow_le_two_mul_sqrt_mul_integral_betaMeasure
      hkm hn) hq.le)

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
