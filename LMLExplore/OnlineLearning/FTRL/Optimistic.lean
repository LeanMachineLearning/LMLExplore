/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.FTRL.Stability

/-!
# Optimistic follow the regularized leader

Optimistic follow the regularized leader (optimistic FTRL) [Ora, Algorithm 7.8] predicts, before
each round `t`, a hint loss `p t : E → ℝ` for the loss `ℓ t` to come, and plays a minimizer
`x t` over a set `V` of a real normed space `E` of the objective `F t + p t`, where
`F t = ψ t + ∑ s < t, ℓ s` is the objective of FTRL with regularizers `ψ t`. Nothing is assumed on
how the hints are chosen: they may depend arbitrarily on the past, and `p t = 0` is FTRL. When the
hints predict the losses well, the regret is smaller than that of FTRL; when they predict them
badly, the worst-case bound of FTRL is essentially kept.

* For a subgradient `ĝ t` within `V` of the prediction error `ℓ t - p t` at `x t`, and objectives
  `F t + ℓ t` that are `λ t`-strongly convex on `V`, the regret against every comparator `u` is at
  most [Ora, Theorem 7.47]
  `ψ (n - 1) u - ψ 0 (x 0) + ∑ t < n, (ĝ t (x t - x (t + 1)) - λ t / 2 * ‖x t - x (t + 1)‖ ^ 2)
    + ∑ t < n - 1, (ψ t (x (t + 1)) - ψ (t + 1) (x (t + 1)))`,
  where the last point `x n` is a leader of the objective `ψ (n - 1) + ∑ s < n, ℓ s` without hint,
  hence at most the same with `‖ĝ t‖ ^ 2 / (2 λ t)` in place of the stability terms, a bound that
  needs no last point. The losses and the hints need not be convex: only `F t + ℓ t` is strongly
  convex.
* For linear losses `g t` and linear hints `p t`, regularizers `ψ t` that are `λ t`-strongly convex
  and nondecreasing in `t` on `V`, and any auxiliary linear hints `q t`, the regret is at most
  [Ora, Theorem 7.48]
  `ψ (n - 1) u - min ψ 0 + ∑ t < n, (‖g t - q t‖ ^ 2 / (2 λ t) + ‖g t‖ * ‖p t - q t‖ / λ t)`.
  With `q = p` this is implied by the previous bound for these losses; with `q = g` the first term
  vanishes, which is what delayed feedback needs [Ora, Section 7.13]. The proof compares the
  plays with those of the auxiliary hints, through the stability of the minimizers of a strongly
  convex function under linear perturbations,
  `StrongConvexOn.mul_norm_sub_le_norm_sub_of_isMinOn_add` [Ora, Lemma 7.49].

## Main statements

* `optimistic_ftrl_stability_le_of_strongConvexOn`: the stability bound of one round of
  optimistic FTRL.
* `regret_le_optimistic_ftrl_of_strongConvexOn`: [Ora, Theorem 7.47, first inequality] the
  regret of optimistic FTRL through its stability terms.
* `regret_le_optimistic_ftrl_norm_sq_div_of_strongConvexOn`: [Ora, Theorem 7.47, second
  inequality] the regret of optimistic FTRL through the dual norms of the subgradients of the
  prediction errors.
* `sum_apply_sub_le_optimistic_ftrl`: [Ora, Theorem 7.48] the improved bound for linear losses and
  linear hints, for auxiliary hints whose plays are given.
* `sum_apply_sub_le_optimistic_ftrl_of_isClosed`: [Ora, Theorem 7.48] the same bound for all
  auxiliary hints, in finite dimension, on a closed set and for lower semicontinuous
  regularizers, where the auxiliary plays exist.

## Implementation notes

[Ora] proves Theorem 7.47 by viewing optimistic FTRL as FTRL with the regularizers
`ψ t + p t`, sets the hint of round `n` (book round `T + 1`) to the hint of round `n - 1`, and
telescopes the hints. That last hint is set at the wrong round: the bound holds with no hint at
round `n`, the last point `x n` being a leader of `ψ (n - 1) + ∑ s < n, ℓ s`. The proof here does
not telescope the hints. It applies the FTRL equality `regret_le_ftrl` to the regularizers
`ψ (min t (n - 1))`, which repeat the last one, and bounds each stability term
`F t (x t) - F (t + 1) (x (t + 1)) + ℓ t (x t)` through the strong convexity of `F t + ℓ t`: since
`x t` minimizes `F t + p t` over `V`, a subgradient of `ℓ t - p t` within `V` at `x t` is one of
`F t + ℓ t`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Algorithm 7.8, Theorems 7.47 and 7.48, Lemma 7.49.
-/
public section

open Finset

namespace LMLExplore.OnlineLearning

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Set E}

/-- **Stability of optimistic FTRL** [Ora, proof of Theorem 7.47]. Let `x t ∈ V` minimize over `V`
the objective `F t + p` of optimistic FTRL with hint `p`, where `F t = ψ t + ∑ s < t, ℓ s`, let `g`
be a subgradient of the prediction error `ℓ t - p` within `V` at `x t`, and let `F t + ℓ t` be
`lam`-strongly convex on `V`. Then for every `z ∈ V`,
`F t (x t) - F (t + 1) z + ℓ t (x t) ≤ g (x t - z) - lam / 2 * ‖x t - z‖ ^ 2 + ψ t z - ψ (t + 1) z`.
This is `ftrl_stability_le_of_strongConvexOn` for the regularizers `ψ s + p` and the loss
`ℓ t - p` at round `t`, which leave the objective `F (t + 1)` unchanged. -/
theorem optimistic_ftrl_stability_le_of_strongConvexOn {ψ ℓ : ℕ → E → ℝ} {p : E → ℝ}
    {x : ℕ → E} {t : ℕ} {z : E} {g : E →L[ℝ] ℝ} {lam : ℝ}
    (hmin : IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t, ℓ s a + p a) V (x t))
    (hg : HasSubgradientWithinAt (fun a ↦ ℓ t a - p a) g V (x t))
    (hΦ : StrongConvexOn V lam fun a ↦ ψ t a + ∑ s ∈ range (t + 1), ℓ s a) (hx : x t ∈ V)
    (hz : z ∈ V) :
    (ψ t (x t) + ∑ s ∈ range t, ℓ s (x t)) - (ψ (t + 1) z + ∑ s ∈ range (t + 1), ℓ s z) +
        ℓ t (x t) ≤
      g (x t - z) - lam / 2 * ‖x t - z‖ ^ 2 + ψ t z - ψ (t + 1) z := by
  -- FTRL with the regularizers `ψ s + p` and the loss `ℓ t - p` at round `t`
  set ℓ' := Function.update ℓ t fun a ↦ ℓ t a - p a
  have hℓ't : ℓ' t = fun a ↦ ℓ t a - p a := Function.update_self _ _ _
  have hℓ' (a : E) : ∑ s ∈ range t, ℓ' s a = ∑ s ∈ range t, ℓ s a :=
    sum_congr rfl fun s hs ↦ congrFun (Function.update_of_ne (mem_range.mp hs).ne _ _) a
  have h := ftrl_stability_le_of_strongConvexOn (ψ := fun s a ↦ ψ s a + p a) (ℓ := ℓ')
    (lam := lam) (by simpa only [hℓ', add_right_comm] using hmin) (by rwa [hℓ't])
    (by convert hΦ using 2 with a; simp only [sum_range_succ, hℓ', hℓ't]; ring) hx hz
  simp only [sum_range_succ, hℓ', hℓ't] at h ⊢
  linarith

/-- **The regret of optimistic FTRL** [Ora, Algorithm 7.8, Theorem 7.47, first inequality]. Let
`x t ∈ V`, for `t ≤ n`. For `t < n`, let `x t` minimize over `V` the objective `F t + p t` of
optimistic FTRL, where `F t = ψ t + ∑ s < t, ℓ s` and `p t` is the hint of round `t`, let `g t` be
a subgradient within `V` of the prediction error `ℓ t - p t` at `x t`, and let `F t + ℓ t` be
`lam t`-strongly convex on `V`. If the last point does at least as well as `u` on the objective
`ψ (n - 1) + ∑ s < n, ℓ s` without hint (for instance if `x n` minimizes it over a set containing
`u`), then
`regret ℓ x u n ≤ ψ (n - 1) u - ψ 0 (x 0)
  + ∑ t < n, (g t (x t - x (t + 1)) - lam t / 2 * ‖x t - x (t + 1)‖ ^ 2)
  + ∑ t < n - 1, (ψ t (x (t + 1)) - ψ (t + 1) (x (t + 1)))`.
Neither the losses nor the hints need to be convex or differentiable, the regularizers need not
be monotone in `t`, and the moduli `lam t` may be of any sign. -/
theorem regret_le_optimistic_ftrl_of_strongConvexOn (ψ ℓ p : ℕ → E → ℝ) (x : ℕ → E)
    (g : ℕ → E →L[ℝ] ℝ) {lam : ℕ → ℝ} {u : E} {n : ℕ}
    (hΦ : ∀ t < n, StrongConvexOn V (lam t) fun a ↦ ψ t a + ∑ s ∈ range (t + 1), ℓ s a)
    (hx : ∀ t ≤ n, x t ∈ V)
    (hmin : ∀ t < n, IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t, ℓ s a + p t a) V (x t))
    (hg : ∀ t < n, HasSubgradientWithinAt (fun a ↦ ℓ t a - p t a) (g t) V (x t))
    (hxn : ψ (n - 1) (x n) + ∑ s ∈ range n, ℓ s (x n) ≤ ψ (n - 1) u + ∑ s ∈ range n, ℓ s u) :
    regret ℓ x u n ≤ ψ (n - 1) u - ψ 0 (x 0) +
      ∑ t ∈ range n, (g t (x t - x (t + 1)) - lam t / 2 * ‖x t - x (t + 1)‖ ^ 2) +
      ∑ t ∈ range (n - 1), (ψ t (x (t + 1)) - ψ (t + 1) (x (t + 1))) := by
  rcases n with _ | n
  · simp only [zero_tsub, range_zero, sum_empty, add_zero, regret_zero] at hxn ⊢
    linarith
  -- the FTRL equality for the regularizers `ψ (min t n)`, which repeat the last one
  have h := regret_le_ftrl (fun t ↦ ψ (min t n)) ℓ x x (u := u) (n := n + 1)
    (by simpa using hxn)
  have hψ (t : ℕ) (ht : t ≤ n) : ψ (min t n) = ψ t := by rw [min_eq_left ht]
  -- the stability term of round `t`, compared with the next point `x (t + 1)`
  have h_round : ∀ t ∈ range (n + 1),
      (ψ (min t n) (x t) + ∑ s ∈ range t, ℓ s (x t)) -
          (ψ (min (t + 1) n) (x (t + 1)) + ∑ s ∈ range (t + 1), ℓ s (x (t + 1))) + ℓ t (x t) ≤
        (g t (x t - x (t + 1)) - lam t / 2 * ‖x t - x (t + 1)‖ ^ 2) +
          (ψ (min t n) (x (t + 1)) - ψ (min (t + 1) n) (x (t + 1))) := by
    intro t ht
    have ht := mem_range.mp ht
    have h := optimistic_ftrl_stability_le_of_strongConvexOn (ψ := fun t ↦ ψ (min t n))
      (by simpa only [hψ t (by omega)] using hmin t ht) (hg t ht)
      (by simpa only [hψ t (by omega)] using hΦ t ht) (hx t (by omega)) (hx (t + 1) ht)
    linarith
  -- the increment of the repeated last regularizer vanishes
  have h_inc : ∑ t ∈ range (n + 1), (ψ (min t n) (x (t + 1)) - ψ (min (t + 1) n) (x (t + 1))) =
      ∑ t ∈ range n, (ψ t (x (t + 1)) - ψ (t + 1) (x (t + 1))) := by
    rw [sum_range_succ, min_self, min_eq_right n.le_succ, sub_self, add_zero]
    exact sum_congr rfl fun t ht ↦ by
      rw [hψ t (mem_range.mp ht).le, hψ (t + 1) (mem_range.mp ht)]
  have h_sum := (sum_le_sum h_round).trans_eq sum_add_distrib
  rw [h_inc] at h_sum
  rw [min_eq_right n.le_succ, Nat.zero_min] at h
  rw [Nat.add_sub_cancel]
  linarith

/-- **The regret of optimistic FTRL** [Ora, Theorem 7.47, second inequality]. Let `n > 0` and,
for `t < n`, let `x t ∈ V` minimize over `V` the objective `F t + p t` of optimistic FTRL, where
`F t = ψ t + ∑ s < t, ℓ s` and `p t` is the hint of round `t`, let `g t` be a subgradient within
`V` of the prediction error `ℓ t - p t` at `x t`, and let `F t + ℓ t` be `lam t`-strongly convex
on `V`, with `lam t > 0`. Then for every `u ∈ V`,
`regret ℓ x u n ≤ ψ (n - 1) u - ψ 0 (x 0) + ∑ t < n, ‖g t‖ ^ 2 / (2 lam t)
  + ∑ t < n - 1, (ψ t (x (t + 1)) - ψ (t + 1) (x (t + 1)))`,
where `‖g t‖` is the dual norm. When the hint `p t` is the loss `ℓ t` up to an additive constant,
`g t = 0` is a subgradient and the round costs nothing; with no hint, `g t` is a subgradient of
`ℓ t` and this is the bound of FTRL for convex losses, with the last regularizer repeated. -/
theorem regret_le_optimistic_ftrl_norm_sq_div_of_strongConvexOn (ψ ℓ p : ℕ → E → ℝ)
    (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) {lam : ℕ → ℝ} {u : E} {n : ℕ} (hn : 0 < n)
    (hlam : ∀ t < n, 0 < lam t)
    (hΦ : ∀ t < n, StrongConvexOn V (lam t) fun a ↦ ψ t a + ∑ s ∈ range (t + 1), ℓ s a)
    (hx : ∀ t < n, x t ∈ V)
    (hmin : ∀ t < n, IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t, ℓ s a + p t a) V (x t))
    (hg : ∀ t < n, HasSubgradientWithinAt (fun a ↦ ℓ t a - p t a) (g t) V (x t)) (hu : u ∈ V) :
    regret ℓ x u n ≤ ψ (n - 1) u - ψ 0 (x 0) + ∑ t ∈ range n, ‖g t‖ ^ 2 / (2 * lam t) +
      ∑ t ∈ range (n - 1), (ψ t (x (t + 1)) - ψ (t + 1) (x (t + 1))) := by
  -- the first inequality, with the comparator itself as the last point
  set y := Function.update x n u with hy
  have hyx (t : ℕ) (ht : t < n) : y t = x t := Function.update_of_ne ht.ne _ _
  have h := regret_le_optimistic_ftrl_of_strongConvexOn ψ ℓ p y g (V := V) (u := u) hΦ
    (fun t ht ↦ by
      rcases ht.lt_or_eq with ht | rfl
      · exact hyx t ht ▸ hx t ht
      · simpa [hy] using hu)
    (fun t ht ↦ hyx t ht ▸ hmin t ht) (fun t ht ↦ hyx t ht ▸ hg t ht) (by simp [hy])
  rw [regret_congr hyx, hyx 0 hn] at h
  have h_inc : ∑ t ∈ range (n - 1), (ψ t (y (t + 1)) - ψ (t + 1) (y (t + 1))) =
      ∑ t ∈ range (n - 1), (ψ t (x (t + 1)) - ψ (t + 1) (x (t + 1))) :=
    sum_congr rfl fun t ht ↦ by rw [hyx (t + 1) (by have := mem_range.mp ht; omega)]
  have h_stab : ∑ t ∈ range n, (g t (y t - y (t + 1)) - lam t / 2 * ‖y t - y (t + 1)‖ ^ 2) ≤
      ∑ t ∈ range n, ‖g t‖ ^ 2 / (2 * lam t) :=
    sum_le_sum fun t ht ↦ apply_sub_sub_mul_norm_sq_le (hlam t (mem_range.mp ht)) _ _ _
  linarith

/-- **The improved regret of optimistic FTRL for linear losses** [Ora, Theorem 7.48], with given
auxiliary plays. Let the losses `g t` and the hints `p t` be linear, and the regularizers `ψ t` be
`lam t`-strongly convex on `V`, with `lam t > 0`, and nondecreasing in `t` on `V`, with
`c ≤ ψ 0` on `V`. For `t < n`, let `x t ∈ V` minimize over `V` the objective
`ψ t + ∑ s < t, g s + p t` of optimistic FTRL, and let `y t ∈ V` minimize over `V` the objective
`ψ t + ∑ s < t, g s + q t` with auxiliary linear hints `q t`. Then for every `u ∈ V`,
`∑ t < n, g t (x t - u)
  ≤ ψ (n - 1) u - c + ∑ t < n, (‖g t - q t‖ ^ 2 / (2 lam t) + ‖g t‖ * ‖p t - q t‖ / lam t)`,
where the norms of `g t`, `p t` and `q t` are dual norms. The auxiliary plays enter only the proof;
`sum_apply_sub_le_optimistic_ftrl_of_isClosed` proves their existence in finite dimension. -/
theorem sum_apply_sub_le_optimistic_ftrl (ψ : ℕ → E → ℝ) (g p q : ℕ → E →L[ℝ] ℝ) (x y : ℕ → E)
    {lam : ℕ → ℝ} {c : ℝ} {u : E} {n : ℕ} (hlam : ∀ t < n, 0 < lam t)
    (hψ : ∀ t < n, StrongConvexOn V (lam t) (ψ t))
    (hψ_mono : ∀ t, t + 1 < n → ∀ a ∈ V, ψ t a ≤ ψ (t + 1) a) (hc : ∀ a ∈ V, c ≤ ψ 0 a)
    (hx : ∀ t < n, x t ∈ V)
    (hmin : ∀ t < n, IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t, g s a + p t a) V (x t))
    (hy : ∀ t < n, y t ∈ V)
    (hymin : ∀ t < n, IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t, g s a + q t a) V (y t))
    (hu : u ∈ V) :
    ∑ t ∈ range n, g t (x t - u) ≤ ψ (n - 1) u - c +
      ∑ t ∈ range n, (‖g t - q t‖ ^ 2 / (2 * lam t) + ‖g t‖ * ‖p t - q t‖ / lam t) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hc u hu
  -- the regret of the auxiliary plays, by the second inequality of Theorem 7.47
  have h_aux := regret_le_optimistic_ftrl_norm_sq_div_of_strongConvexOn ψ (fun t ↦ g t)
    (fun t ↦ q t) y (fun t ↦ g t - q t) hn hlam
    (fun t ht ↦ by simpa using (hψ t ht).add_continuousLinearMap (∑ s ∈ range (t + 1), g s))
    hy hymin
    (fun t _ ↦ hasSubgradientWithinAt_linear (g t - q t)) hu
  have h_inc : ∑ t ∈ range (n - 1), (ψ t (y (t + 1)) - ψ (t + 1) (y (t + 1))) ≤ 0 :=
    sum_nonpos fun t ht ↦ by
      have ht := mem_range.mp ht
      linarith [hψ_mono t (by omega) _ (hy (t + 1) (by omega))]
  have hy0 := hc _ (hy 0 hn)
  -- the plays and the auxiliary plays are close by the stability of linear perturbations
  have h_close : ∀ t ∈ range n, g t (x t - y t) ≤ ‖g t‖ * ‖p t - q t‖ / lam t := by
    intro t ht
    have ht := mem_range.mp ht
    have h := ((hψ t ht).add_continuousLinearMap (∑ s ∈ range t, g s)
      ).mul_norm_sub_le_norm_sub_of_isMinOn_add (hx t ht) (hy t ht) (θ₁ := p t) (θ₂ := q t)
      (by simpa using hmin t ht) (by simpa using hymin t ht)
    rw [mul_div_assoc]
    calc g t (x t - y t) ≤ ‖g t‖ * ‖x t - y t‖ := (g t).apply_le_opNorm_mul_norm _
      _ ≤ ‖g t‖ * (‖p t - q t‖ / lam t) := by
        gcongr
        rw [le_div_iff₀ (hlam t ht), mul_comm]
        exact h
  have h_split : ∑ t ∈ range n, g t (x t - u) =
      regret (fun t ↦ g t) y u n + ∑ t ∈ range n, g t (x t - y t) := by
    rw [regret_def, ← sum_add_distrib]
    exact sum_congr rfl fun t _ ↦ by simp only [map_sub]; ring
  rw [h_split, sum_add_distrib]
  linarith [sum_le_sum h_close]

/-- **The improved regret of optimistic FTRL for linear losses** [Ora, Theorem 7.48]. In finite
dimension, let `V` be closed, let the losses `g t` and the hints `p t` be linear, and let the
regularizers `ψ t` be lower semicontinuous and `lam t`-strongly convex on `V`, with `lam t > 0`,
and nondecreasing in `t` on `V`, with `c ≤ ψ 0` on `V`. For `t < n`, let `x t ∈ V` minimize over
`V` the objective `ψ t + ∑ s < t, g s + p t` of optimistic FTRL. Then for every `u ∈ V` and all
linear maps `q t`,
`∑ t < n, g t (x t - u)
  ≤ ψ (n - 1) u - c + ∑ t < n, (‖g t - q t‖ ^ 2 / (2 lam t) + ‖g t‖ * ‖p t - q t‖ / lam t)`,
where the norms of `g t`, `p t` and `q t` are dual norms. With `q = p` this is a weakening, for
linear losses and nondecreasing regularizers, of the bound of
`regret_le_optimistic_ftrl_norm_sq_div_of_strongConvexOn`; with `q = g` the bound is
`ψ (n - 1) u - c + ∑ t < n, ‖g t‖ * ‖p t - g t‖ / lam t`. -/
theorem sum_apply_sub_le_optimistic_ftrl_of_isClosed [FiniteDimensional ℝ E] (hV : IsClosed V)
    (ψ : ℕ → E → ℝ) (g p q : ℕ → E →L[ℝ] ℝ) (x : ℕ → E) {lam : ℕ → ℝ} {c : ℝ} {u : E} {n : ℕ}
    (hlam : ∀ t < n, 0 < lam t) (hψ : ∀ t < n, StrongConvexOn V (lam t) (ψ t))
    (hψ_lsc : ∀ t < n, LowerSemicontinuousOn (ψ t) V)
    (hψ_mono : ∀ t, t + 1 < n → ∀ a ∈ V, ψ t a ≤ ψ (t + 1) a) (hc : ∀ a ∈ V, c ≤ ψ 0 a)
    (hx : ∀ t < n, x t ∈ V)
    (hmin : ∀ t < n, IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t, g s a + p t a) V (x t))
    (hu : u ∈ V) :
    ∑ t ∈ range n, g t (x t - u) ≤ ψ (n - 1) u - c +
      ∑ t ∈ range n, (‖g t - q t‖ ^ 2 / (2 * lam t) + ‖g t‖ * ‖p t - q t‖ / lam t) := by
  -- the auxiliary plays exist, as minimizers of strongly convex lower semicontinuous functions
  have h_ex (t : ℕ) : ∃ y, t < n → y ∈ V ∧
      IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t, g s a + q t a) V y := by
    by_cases ht : t < n
    · obtain ⟨y, hy, hymin⟩ := (hψ t ht).exists_isMinOn_add_continuousLinearMap (hlam t ht) hV
        ⟨u, hu⟩ (hψ_lsc t ht) (∑ s ∈ range t, g s + q t)
      refine ⟨y, fun _ ↦ ⟨hy, ?_⟩⟩
      convert hymin using 1
      ext a
      simp [add_assoc]
    · exact ⟨0, fun h ↦ absurd h ht⟩
  choose y hy using h_ex
  exact sum_apply_sub_le_optimistic_ftrl ψ g p q x y hlam hψ hψ_mono hc hx hmin
    (fun t ht ↦ (hy t ht).1) (fun t ht ↦ (hy t ht).2) hu

end LMLExplore.OnlineLearning
