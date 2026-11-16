/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.FTRL.Optimistic

/-!
# Follow the regularized leader with missing and delayed feedback

Online linear optimization on a set `V` of a real normed space `E`, with losses
`g t : E →L[ℝ] ℝ`, when the learner does not observe every past loss before it plays: at round
`t`, the losses of a set `M t ⊆ range t` of past rounds are **missing**. Follow the regularized
leader on the observed losses plays a minimizer `x t` over `V` of
`ψ t + ∑ s ∈ range t \ M t, g s` [Ora, §7.13]. Nothing is assumed on the sets `M t`: they may be
arbitrary, change from round to round and depend on the past, and a loss may be missing at one
round and observed at an earlier one. A constant delay `τ`, where the loss of round `s` arrives
after round `s + τ`, is the case `M t = Ico (t - τ) t`, with the objective
`ψ t + ∑ s < t - τ, g s`.

FTRL with missing feedback is optimistic FTRL (`LMLExplore.OnlineLearning.FTRL.Optimistic`) with
the hints `-∑ s ∈ M t, g s`, which remove the missing losses from the objective. The improved bound
of optimistic FTRL for linear losses [Ora, Theorem 7.48], with the auxiliary hints `q t = g t`,
then pays at each round `‖g t‖ * ‖g t + ∑ s ∈ M t, g s‖ / lam t`: the dual norm of the current
loss times that of the sum of the current loss and the missing ones. With a delay `τ` and losses of
dual norm at most `L`, a round costs `(τ + 1) L ^ 2 / lam t`, linear in the delay.

## Main statements

* `sum_apply_sub_le_ftrl_of_missing`: the regret bound for missing feedback, for given plays of
  the leaders `ψ t + ∑ s ≤ t, g s`, which enter only the proof.
* `sum_apply_sub_le_ftrl_of_missing_of_isClosed`: the same bound in finite dimension, on a closed
  set and for lower semicontinuous regularizers, where the leaders exist.
* `sum_apply_sub_le_ftrl_of_delay_of_isClosed`: [Ora, (7.13)] the case of a constant delay `τ`,
  with the bound `ψ (n - 1) u - c + ∑ t < n, ‖g t‖ * ‖∑ t - τ ≤ s ≤ t, g s‖ / lam t`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Theorem 7.48, §7.13.
-/

public section

open Finset

namespace LMLExplore.OnlineLearning

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Set E}

/-- The objective of the observed losses is that of optimistic FTRL with the hint
`-∑ s ∈ M, g s`, which removes the missing losses. -/
private theorem ftrl_missing_objective_eq (ψ : E → ℝ) (g : ℕ → E →L[ℝ] ℝ) {M : Finset ℕ}
    {t : ℕ} (hM : M ⊆ range t) :
    (fun a ↦ ψ a + ∑ s ∈ range t, g s a + (-∑ s ∈ M, g s) a) =
      fun a ↦ ψ a + ∑ s ∈ range t \ M, g s a := by
  ext a
  rw [← sum_sdiff hM]
  simp only [neg_apply, sum_apply]
  ring

/-- The bound of optimistic FTRL for the hints `-∑ s ∈ M t, g s` and the auxiliary hints `g t` is
the bound for missing feedback. -/
private theorem sum_optimistic_ftrl_missing_eq (g : ℕ → E →L[ℝ] ℝ) (M : ℕ → Finset ℕ)
    (lam : ℕ → ℝ) (n : ℕ) :
    ∑ t ∈ range n, (‖g t - g t‖ ^ 2 / (2 * lam t) + ‖g t‖ * ‖-∑ s ∈ M t, g s - g t‖ / lam t) =
      ∑ t ∈ range n, ‖g t‖ * ‖g t + ∑ s ∈ M t, g s‖ / lam t :=
  sum_congr rfl fun t _ ↦ by
    rw [sub_self, norm_zero, ← norm_neg (-∑ s ∈ M t, g s - g t), neg_sub, sub_neg_eq_add]
    ring

/-- **FTRL with missing feedback**, for given leaders [Ora, Theorem 7.48, §7.13]. Let the losses
`g t` be linear, and the regularizers `ψ t` be `lam t`-strongly convex on `V`, with `lam t > 0`,
and nondecreasing in `t` on `V`, with `c ≤ ψ 0` on `V`. For `t < n`, let `M t ⊆ range t` be the
rounds whose losses are missing at round `t`, let `x t ∈ V` minimize over `V` the objective
`ψ t + ∑ s ∈ range t \ M t, g s` of the observed losses, and let `y t ∈ V` minimize over `V` the
objective `ψ t + ∑ s ≤ t, g s` of the leader. Then for every `u ∈ V`,
`∑ t < n, g t (x t - u) ≤ ψ (n - 1) u - c + ∑ t < n, ‖g t‖ * ‖g t + ∑ s ∈ M t, g s‖ / lam t`,
where the norms are dual norms. The leaders enter only the proof;
`sum_apply_sub_le_ftrl_of_missing_of_isClosed` does without them in finite dimension. -/
theorem sum_apply_sub_le_ftrl_of_missing (ψ : ℕ → E → ℝ) (g : ℕ → E →L[ℝ] ℝ) (M : ℕ → Finset ℕ)
    (x y : ℕ → E) {lam : ℕ → ℝ} {c : ℝ} {u : E} {n : ℕ} (hlam : ∀ t < n, 0 < lam t)
    (hψ : ∀ t < n, StrongConvexOn V (lam t) (ψ t))
    (hψ_mono : ∀ t, t + 1 < n → ∀ a ∈ V, ψ t a ≤ ψ (t + 1) a) (hc : ∀ a ∈ V, c ≤ ψ 0 a)
    (hM : ∀ t < n, M t ⊆ range t) (hx : ∀ t < n, x t ∈ V)
    (hmin : ∀ t < n, IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t \ M t, g s a) V (x t))
    (hy : ∀ t < n, y t ∈ V)
    (hymin : ∀ t < n, IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range (t + 1), g s a) V (y t))
    (hu : u ∈ V) :
    ∑ t ∈ range n, g t (x t - u) ≤
      ψ (n - 1) u - c + ∑ t ∈ range n, ‖g t‖ * ‖g t + ∑ s ∈ M t, g s‖ / lam t := by
  -- optimistic FTRL with the hints `-∑ s ∈ M t, g s`, whose auxiliary plays for the hints `g t`
  -- are the leaders
  have h := sum_apply_sub_le_optimistic_ftrl ψ g (fun t ↦ -∑ s ∈ M t, g s) g x y hlam hψ
    hψ_mono hc hx
    (fun t ht ↦ by rw [ftrl_missing_objective_eq (ψ t) g (hM t ht)]; exact hmin t ht) hy
    (fun t ht ↦ by simpa only [sum_range_succ, add_assoc] using hymin t ht) hu
  exact h.trans_eq (congrArg _ (sum_optimistic_ftrl_missing_eq g M lam n))

/-- **FTRL with missing feedback** [Ora, Theorem 7.48, §7.13]. In finite dimension, let `V` be
closed, let the losses `g t` be linear, and let the regularizers `ψ t` be lower semicontinuous and
`lam t`-strongly convex on `V`, with `lam t > 0`, and nondecreasing in `t` on `V`, with
`c ≤ ψ 0` on `V`. For `t < n`, let `M t ⊆ range t` be the rounds whose losses are missing at round
`t`, and let `x t ∈ V` minimize over `V` the objective `ψ t + ∑ s ∈ range t \ M t, g s` of the
observed losses. Then for every `u ∈ V`,
`∑ t < n, g t (x t - u) ≤ ψ (n - 1) u - c + ∑ t < n, ‖g t‖ * ‖g t + ∑ s ∈ M t, g s‖ / lam t`,
where the norms are dual norms. With no missing feedback, `M t = ∅`, this is a bound of FTRL for
linear losses. -/
theorem sum_apply_sub_le_ftrl_of_missing_of_isClosed [FiniteDimensional ℝ E] (hV : IsClosed V)
    (ψ : ℕ → E → ℝ) (g : ℕ → E →L[ℝ] ℝ) (M : ℕ → Finset ℕ) (x : ℕ → E) {lam : ℕ → ℝ} {c : ℝ}
    {u : E} {n : ℕ} (hlam : ∀ t < n, 0 < lam t) (hψ : ∀ t < n, StrongConvexOn V (lam t) (ψ t))
    (hψ_lsc : ∀ t < n, LowerSemicontinuousOn (ψ t) V)
    (hψ_mono : ∀ t, t + 1 < n → ∀ a ∈ V, ψ t a ≤ ψ (t + 1) a) (hc : ∀ a ∈ V, c ≤ ψ 0 a)
    (hM : ∀ t < n, M t ⊆ range t) (hx : ∀ t < n, x t ∈ V)
    (hmin : ∀ t < n, IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t \ M t, g s a) V (x t))
    (hu : u ∈ V) :
    ∑ t ∈ range n, g t (x t - u) ≤
      ψ (n - 1) u - c + ∑ t ∈ range n, ‖g t‖ * ‖g t + ∑ s ∈ M t, g s‖ / lam t := by
  -- optimistic FTRL with the hints `-∑ s ∈ M t, g s` and the auxiliary hints `g t`
  have h := sum_apply_sub_le_optimistic_ftrl_of_isClosed hV ψ g (fun t ↦ -∑ s ∈ M t, g s) g x
    hlam hψ hψ_lsc hψ_mono hc hx
    (fun t ht ↦ by rw [ftrl_missing_objective_eq (ψ t) g (hM t ht)]; exact hmin t ht) hu
  exact h.trans_eq (congrArg _ (sum_optimistic_ftrl_missing_eq g M lam n))

/-- **FTRL with delayed feedback** [Ora, (7.13)]. In finite dimension, let `V` be closed, let the
losses `g t` be linear, and let the regularizers `ψ t` be lower semicontinuous and
`lam t`-strongly convex on `V`, with `lam t > 0`, and nondecreasing in `t` on `V`, with
`c ≤ ψ 0` on `V`. With a constant delay `τ`, the loss of round `s` arrives after round `s + τ`:
for `t < n`, let `x t ∈ V` minimize over `V` the objective `ψ t + ∑ s < t - τ, g s` of the
losses that have arrived. Then for every `u ∈ V`,
`∑ t < n, g t (x t - u) ≤ ψ (n - 1) u - c + ∑ t < n, ‖g t‖ * ‖∑ t - τ ≤ s ≤ t, g s‖ / lam t`,
where the norms are dual norms. For losses of dual norm at most `L`, each round costs at most
`(τ + 1) L ^ 2 / lam t`. -/
theorem sum_apply_sub_le_ftrl_of_delay_of_isClosed [FiniteDimensional ℝ E] (hV : IsClosed V)
    (ψ : ℕ → E → ℝ) (g : ℕ → E →L[ℝ] ℝ) (τ : ℕ) (x : ℕ → E) {lam : ℕ → ℝ} {c : ℝ} {u : E} {n : ℕ}
    (hlam : ∀ t < n, 0 < lam t) (hψ : ∀ t < n, StrongConvexOn V (lam t) (ψ t))
    (hψ_lsc : ∀ t < n, LowerSemicontinuousOn (ψ t) V)
    (hψ_mono : ∀ t, t + 1 < n → ∀ a ∈ V, ψ t a ≤ ψ (t + 1) a) (hc : ∀ a ∈ V, c ≤ ψ 0 a)
    (hx : ∀ t < n, x t ∈ V)
    (hmin : ∀ t < n, IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range (t - τ), g s a) V (x t))
    (hu : u ∈ V) :
    ∑ t ∈ range n, g t (x t - u) ≤
      ψ (n - 1) u - c + ∑ t ∈ range n, ‖g t‖ * ‖∑ s ∈ Icc (t - τ) t, g s‖ / lam t := by
  -- the missing rounds at round `t` are `t - τ ≤ s < t`
  have h_obs (t : ℕ) : range t \ Ico (t - τ) t = range (t - τ) := by
    ext s
    simp only [mem_sdiff, mem_range, mem_Ico]
    omega
  have h_err (t : ℕ) : g t + ∑ s ∈ Ico (t - τ) t, g s = ∑ s ∈ Icc (t - τ) t, g s :=
    add_sum_Ico_eq_sum_Icc (t.sub_le τ)
  have h := sum_apply_sub_le_ftrl_of_missing_of_isClosed hV ψ g (fun t ↦ Ico (t - τ) t) x hlam
    hψ hψ_lsc hψ_mono hc (fun t _ s hs ↦ mem_range.mpr (mem_Ico.mp hs).2) hx
    (fun t ht ↦ by rw [h_obs]; exact hmin t ht) hu
  simpa only [h_err] using h

end LMLExplore.OnlineLearning
