/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Inequalities for the Gamma function

This file proves the inequalities for the real Gamma function that the regret bounds of
parameter-free and universal online algorithms use [Ora, Appendix A.2.2].

* **Wendel's inequality**: for `x > 0` and `s ∈ [0, 1]`,
  `x * Γ(x) ≤ (x + s) ^ (1 - s) * Γ(x + s)` and `Γ(x + s) ≤ x ^ s * Γ(x)`. Dividing by
  `x ^ s * Γ(x)`, this is the usual form `(x / (x + s)) ^ (1 - s) ≤ Γ(x + s) / (x ^ s Γ(x)) ≤ 1`.
  Both halves follow from the log-convexity of `Γ` (Mathlib's
  `Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma`) and `Γ(x + 1) = x Γ(x)`.
* **Convexity of `x log x - log Γ(x + 1 / 2)` on `[0, ∞)`** [Ora, Lemma A.13]. Its second
  derivative is `1 / x - ψ'(x + 1 / 2)`, where `ψ'` is the trigamma function. The proof needs no
  digamma function: by the Bohr–Mollerup limit `Real.BohrMollerup.tendsto_log_gamma`, the function
  is the pointwise limit of `x log x - logGammaSeq (x + 1 / 2) N`, whose second derivative
  `1 / x - ∑ m ≤ N, 1 / (x + 1 / 2 + m) ^ 2` is nonnegative because
  `1 / (y + 1 / 2) ^ 2 ≤ 1 / y - 1 / (y + 1)` telescopes. A pointwise limit of convex functions is
  convex.
* **The vertex lemma for two coordinates** [Ora, Lemma A.13]: for `a, b ≥ 0`, the function
  `a * log a + b * log b - log Γ(a + 1 / 2) - log Γ(b + 1 / 2)` on the segment `a + b = const` is
  largest at an endpoint.
* **Lemma A.12 of [Ora] for `d = 2`**: `√π Γ(t + 1) ≤ e √t Γ(t + 1 / 2)` for `t ≥ 1`, from the
  upper half of Wendel's inequality.

## Main statements

* `Real.mul_Gamma_le_rpow_mul_Gamma_add`, `Real.Gamma_add_le_rpow_mul_Gamma`: Wendel's inequality.
* `Real.convexOn_mul_log_sub_log_Gamma_add_half`: the convexity of `x log x - log Γ(x + 1 / 2)`.
* `Real.mul_log_add_mul_log_sub_log_Gamma_add_half_le`: the vertex lemma for two coordinates.
* `Real.sqrt_pi_mul_Gamma_add_one_le`: [Ora, Lemma A.12] for `d = 2`, and its logarithmic form
  `Real.log_pi_div_two_add_log_Gamma_add_one_sub_log_Gamma_add_half_le`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
* J. G. Wendel, *Note on the gamma function*, Amer. Math. Monthly 55 (1948).
-/

public section

open Filter Finset Topology

namespace Real

section Wendel

variable {x s : ℝ}

/-- **Wendel's inequality, lower half**: for `x > 0` and `s ∈ [0, 1]`,
`x * Γ(x) ≤ (x + s) ^ (1 - s) * Γ(x + s)`, that is,
`(x / (x + s)) ^ (1 - s) ≤ Γ(x + s) / (x ^ s * Γ(x))`. By log-convexity,
`Γ(x + 1) ≤ Γ(x + s) ^ s * Γ(x + s + 1) ^ (1 - s)`. -/
theorem mul_Gamma_le_rpow_mul_Gamma_add (hx : 0 < x) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    x * Gamma x ≤ (x + s) ^ (1 - s) * Gamma (x + s) := by
  have hxs : 0 < x + s := by linarith
  have hG := Gamma_pos_of_pos hxs
  rw [← Gamma_add_one hx.ne']
  rcases hs₀.eq_or_lt with rfl | hs₀
  · rw [sub_zero, rpow_one, add_zero, Gamma_add_one hx.ne']
  rcases hs₁.eq_or_lt with rfl | hs₁
  · simp
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x + s) (t := x + s + 1) hxs
    (by linarith) hs₀ (sub_pos.2 hs₁) (by ring)
  rw [Gamma_add_one hxs.ne', mul_rpow hxs.le hG.le] at h
  calc Gamma (x + 1) = Gamma (s * (x + s) + (1 - s) * (x + s + 1)) := by ring_nf
    _ ≤ Gamma (x + s) ^ s * ((x + s) ^ (1 - s) * Gamma (x + s) ^ (1 - s)) := h
    _ = (x + s) ^ (1 - s) * (Gamma (x + s) ^ s * Gamma (x + s) ^ (1 - s)) := by ring
    _ = (x + s) ^ (1 - s) * Gamma (x + s) := by
      rw [← rpow_add hG, add_sub_cancel, rpow_one]

/-- **Wendel's inequality, upper half**: for `x > 0` and `s ∈ [0, 1]`, `Γ(x + s) ≤ x ^ s * Γ(x)`.
By log-convexity, `Γ(x + s) ≤ Γ(x) ^ (1 - s) * Γ(x + 1) ^ s`. -/
theorem Gamma_add_le_rpow_mul_Gamma (hx : 0 < x) (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    Gamma (x + s) ≤ x ^ s * Gamma x := by
  have hG := Gamma_pos_of_pos hx
  rcases hs₀.eq_or_lt with rfl | hs₀
  · simp
  rcases hs₁.eq_or_lt with rfl | hs₁
  · rw [rpow_one, Gamma_add_one hx.ne']
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x) (t := x + 1) hx
    (by linarith) (sub_pos.2 hs₁) hs₀ (by ring)
  rw [Gamma_add_one hx.ne', mul_rpow hx.le hG.le] at h
  calc Gamma (x + s) = Gamma ((1 - s) * x + s * (x + 1)) := by ring_nf
    _ ≤ Gamma x ^ (1 - s) * (x ^ s * Gamma x ^ s) := h
    _ = x ^ s * (Gamma x ^ (1 - s) * Gamma x ^ s) := by ring
    _ = x ^ s * Gamma x := by rw [← rpow_add hG, sub_add_cancel, rpow_one]

end Wendel

section Convexity

/-- The telescoping bound `∑ m < k, 1 / (x + 1 / 2 + m) ^ 2 ≤ 1 / x - 1 / (x + k)`, from
`1 / (y + 1 / 2) ^ 2 ≤ 1 / y - 1 / (y + 1)`, which is `y (y + 1) ≤ (y + 1 / 2) ^ 2`. -/
private lemma sum_inv_add_half_sq_le {x : ℝ} (hx : 0 < x) (k : ℕ) :
    ∑ m ∈ range k, ((x + 1 / 2 + m) ^ 2)⁻¹ ≤ x⁻¹ - (x + k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : 0 < x + k := by positivity
    have hstep : ((x + 1 / 2 + k) ^ 2)⁻¹ ≤ (x + k)⁻¹ - (x + ((k + 1 : ℕ) : ℝ))⁻¹ := by
      have e : (x + k)⁻¹ - (x + ((k + 1 : ℕ) : ℝ))⁻¹ = ((x + k) * (x + k + 1))⁻¹ := by
        push_cast
        field_simp
        ring
      rw [e]
      exact inv_anti₀ (by positivity) (by nlinarith)
    rw [sum_range_succ]
    linarith

/-- The approximation `x log x - logGammaSeq (x + 1 / 2) N` of `x log x - log Γ(x + 1 / 2)` is
convex on `[0, ∞)`: its second derivative is `1 / x - ∑ m ≤ N, 1 / (x + 1 / 2 + m) ^ 2 ≥ 0`. -/
private lemma convexOn_mul_log_sub_logGammaSeq_add_half (N : ℕ) :
    ConvexOn ℝ (Set.Ici 0) fun x ↦ x * log x - BohrMollerup.logGammaSeq (x + 1 / 2) N := by
  have hpos {x : ℝ} (hx : 0 ≤ x) (m : ℕ) : 0 < x + 1 / 2 + m := by positivity
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
    (f' := fun x ↦ log x + 1 - log N + ∑ m ∈ range (N + 1), (x + 1 / 2 + m)⁻¹)
    (f'' := fun x ↦ x⁻¹ - ∑ m ∈ range (N + 1), ((x + 1 / 2 + m) ^ 2)⁻¹) ?_ ?_ ?_ ?_
  · simp only [BohrMollerup.logGammaSeq]
    refine (continuous_mul_log.continuousOn.sub (ContinuousOn.sub (by fun_prop) ?_))
    exact continuousOn_finsetSum _ fun m _ ↦
      ContinuousOn.log (by fun_prop) fun x hx ↦ (hpos hx m).ne'
  · intro x hx
    rw [interior_Ici] at hx
    have hx : 0 < x := hx
    refine HasDerivAt.hasDerivWithinAt ?_
    simp only [BohrMollerup.logGammaSeq]
    have hsum : HasDerivAt (fun y : ℝ ↦ ∑ m ∈ range (N + 1), log (y + 1 / 2 + m))
        (∑ m ∈ range (N + 1), (x + 1 / 2 + m)⁻¹) x := by
      refine HasDerivAt.fun_sum fun m _ ↦ ?_
      simpa using (((hasDerivAt_id x).add_const (1 / 2 : ℝ)).add_const (m : ℝ)).log
        (hpos hx.le m).ne'
    have hlin : HasDerivAt (fun y : ℝ ↦ (y + 1 / 2) * log N + log (N.factorial : ℝ)) (log N) x := by
      simpa using (((hasDerivAt_id x).add_const (1 / 2 : ℝ)).mul_const (log N)).add_const
        (log (N.factorial : ℝ))
    convert (hasDerivAt_mul_log hx.ne').sub (hlin.sub hsum) using 1
    ring
  · intro x hx
    rw [interior_Ici] at hx
    have hx : 0 < x := hx
    refine HasDerivAt.hasDerivWithinAt ?_
    have hsum : HasDerivAt (fun y : ℝ ↦ ∑ m ∈ range (N + 1), (y + 1 / 2 + m)⁻¹)
        (∑ m ∈ range (N + 1), -((x + 1 / 2 + m) ^ 2)⁻¹) x := by
      refine HasDerivAt.fun_sum fun m _ ↦ ?_
      convert (((hasDerivAt_id x).add_const (1 / 2 : ℝ)).add_const (m : ℝ)).inv
        (hpos hx.le m).ne' using 1
      · rfl
      · simp only [id, neg_div, one_div]
    convert (((hasDerivAt_log hx.ne').add_const 1).sub_const (log N)).add hsum using 1
    rw [sum_neg_distrib, sub_eq_add_neg]
  · intro x hx
    rw [interior_Ici] at hx
    have hx : 0 < x := hx
    have h := sum_inv_add_half_sq_le hx (N + 1)
    have : 0 < (x + ((N + 1 : ℕ) : ℝ))⁻¹ := by positivity
    linarith

/-- **The convexity of `x log x - log Γ(x + 1 / 2)`** on `[0, ∞)` [Ora, Lemma A.13], with
`0 log 0 = 0`. It is the pointwise limit of the convex functions
`x log x - logGammaSeq (x + 1 / 2) N` (Bohr–Mollerup). -/
theorem convexOn_mul_log_sub_log_Gamma_add_half :
    ConvexOn ℝ (Set.Ici 0) fun x ↦ x * log x - log (Gamma (x + 1 / 2)) := by
  have hlim (x : ℝ) (hx : x ∈ Set.Ici (0 : ℝ)) :
      Tendsto (fun N ↦ x * log x - BohrMollerup.logGammaSeq (x + 1 / 2) N) atTop
        (𝓝 (x * log x - log (Gamma (x + 1 / 2)))) :=
    (BohrMollerup.tendsto_log_gamma (by linarith [Set.mem_Ici.1 hx])).const_sub _
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab ↦ ?_⟩
  exact le_of_tendsto_of_tendsto' (hlim _ (convex_Ici 0 hx hy ha hb hab))
    (((hlim x hx).const_smul a).add ((hlim y hy).const_smul b))
    fun N ↦ (convexOn_mul_log_sub_logGammaSeq_add_half N).2 hx hy ha hb hab

/-- **The vertex lemma for two coordinates** [Ora, Lemma A.13]: for `a, b ≥ 0`,
`a log a + b log b - log Γ(a + 1 / 2) - log Γ(b + 1 / 2)` is at most its value
`(a + b) log (a + b) - log Γ(a + b + 1 / 2) - log Γ(1 / 2)` at the endpoint `(a + b, 0)` of the
segment of the pairs with sum `a + b`. Equivalently, with `0 ^ 0 = 1`,
`a ^ a b ^ b / (Γ(a + 1 / 2) Γ(b + 1 / 2)) ≤ (a + b) ^ (a + b) / (Γ(a + b + 1 / 2) √π)`. -/
theorem mul_log_add_mul_log_sub_log_Gamma_add_half_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * log a + b * log b - log (Gamma (a + 1 / 2)) - log (Gamma (b + 1 / 2)) ≤
      (a + b) * log (a + b) - log (Gamma (a + b + 1 / 2)) - log (Gamma (1 / 2)) := by
  set f : ℝ → ℝ := fun x ↦ x * log x - log (Gamma (x + 1 / 2))
  have hf := convexOn_mul_log_sub_log_Gamma_add_half
  have hab : 0 ≤ a + b := add_nonneg ha hb
  rcases hab.eq_or_lt with h | hab
  · obtain rfl : a = 0 := by linarith
    obtain rfl : b = 0 := by linarith
    simp
  -- `a` and `b` are the convex combinations of `a + b` and `0` with weights `a / (a + b)` and
  -- `b / (a + b)`, in both orders.
  have h0 : (0 : ℝ) ∈ Set.Ici 0 := le_rfl
  have hs : a + b ∈ Set.Ici (0 : ℝ) := hab.le
  have hw : a / (a + b) + b / (a + b) = 1 := by field_simp
  have hwa := div_nonneg ha hab.le
  have hwb := div_nonneg hb hab.le
  have h₁ := hf.2 hs h0 hwa hwb hw
  have h₂ := hf.2 hs h0 hwb hwa (by linarith)
  have ea : (a / (a + b)) • (a + b) + (b / (a + b)) • (0 : ℝ) = a := by
    rw [smul_eq_mul, smul_zero, add_zero, div_mul_cancel₀ _ hab.ne']
  have eb : (b / (a + b)) • (a + b) + (a / (a + b)) • (0 : ℝ) = b := by
    rw [smul_eq_mul, smul_zero, add_zero, div_mul_cancel₀ _ hab.ne']
  rw [ea] at h₁
  rw [eb] at h₂
  simp only [smul_eq_mul] at h₁ h₂
  simp only [zero_add, zero_mul, zero_sub] at h₁ h₂
  have : (a / (a + b) + b / (a + b)) * ((a + b) * log (a + b) - log (Gamma (a + b + 1 / 2))) +
      (a / (a + b) + b / (a + b)) * -log (Gamma (1 / 2)) =
      (a + b) * log (a + b) - log (Gamma (a + b + 1 / 2)) - log (Gamma (1 / 2)) := by
    rw [hw]; ring
  linarith

/-- **[Ora, Lemma A.12] for `d = 2`**: for `t ≥ 1`, `√π Γ(t + 1) ≤ e √t Γ(t + 1 / 2)`, that is,
`log (√π Γ(t + 1) / Γ(t + 1 / 2)) ≤ log t / 2 + 1`. By Wendel's inequality,
`Γ(t + 1) ≤ √(t + 1 / 2) Γ(t + 1 / 2)`, and `π (t + 1 / 2) ≤ e ^ 2 t`. -/
theorem sqrt_pi_mul_Gamma_add_one_le {t : ℝ} (ht : 1 ≤ t) :
    √π * Gamma (t + 1) ≤ exp 1 * √t * Gamma (t + 1 / 2) := by
  have ht' : 0 < t + 1 / 2 := by linarith
  have hW := Gamma_add_le_rpow_mul_Gamma ht' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [add_assoc, show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, ← sqrt_eq_rpow] at hW
  -- `π (t + 1 / 2) ≤ e ^ 2 t`, since `π < 3.15` and `e > 2.7`
  have he : (2.7 : ℝ) < exp 1 := lt_trans (by norm_num) exp_one_gt_d9
  have hkey : √π * √(t + 1 / 2) ≤ exp 1 * √t := by
    rw [← sqrt_mul pi_pos.le, ← sqrt_sq (exp_pos 1).le, ← sqrt_mul (sq_nonneg _)]
    refine sqrt_le_sqrt ?_
    have he2 : (7 : ℝ) < exp 1 ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_right he2 (by linarith : (0 : ℝ) < t),
      mul_lt_mul_of_pos_right pi_lt_d2 ht']
  calc √π * Gamma (t + 1) ≤ √π * (√(t + 1 / 2) * Gamma (t + 1 / 2)) :=
        mul_le_mul_of_nonneg_left hW (sqrt_nonneg _)
    _ = √π * √(t + 1 / 2) * Gamma (t + 1 / 2) := by ring
    _ ≤ exp 1 * √t * Gamma (t + 1 / 2) :=
        mul_le_mul_of_nonneg_right hkey (Gamma_pos_of_pos ht').le

/-- **The logarithmic form of [Ora, Lemma A.12] for `d = 2`**: for `t ≥ 1`,
`log π / 2 + log Γ(t + 1) - log Γ(t + 1 / 2) ≤ log t / 2 + 1`, the logarithm of
`Real.sqrt_pi_mul_Gamma_add_one_le`. -/
theorem log_pi_div_two_add_log_Gamma_add_one_sub_log_Gamma_add_half_le {t : ℝ} (ht : 1 ≤ t) :
    log π / 2 + log (Gamma (t + 1)) - log (Gamma (t + 1 / 2)) ≤ log t / 2 + 1 := by
  have h₁ := Gamma_pos_of_pos (show 0 < t + 1 by linarith)
  have h₂ := Gamma_pos_of_pos (show 0 < t + 1 / 2 by linarith)
  have h := log_le_log (by positivity) (sqrt_pi_mul_Gamma_add_one_le ht)
  rw [log_mul (by positivity) h₁.ne', log_mul (by positivity) h₂.ne',
    log_mul (by positivity) (by positivity), log_exp, log_sqrt pi_pos.le,
    log_sqrt (by linarith)] at h
  linarith

end Convexity

end Real
