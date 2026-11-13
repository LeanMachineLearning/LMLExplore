/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.ValueIteration.Basic
public import LMLExplore.Probability.Kernel.Dobrushin

/-!
# Span contraction of the Bellman optimality operator

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP on a measurable state space `𝓢` with bounded rewards, let `γ ≥ 0`,
and write `T` for the Bellman optimality operator `M.bellman γ`. The *span* of a bounded function
is its oscillation `sp v = sup v - inf v`, the seminorm `LMLExplore.orderUnitOsc 1`. Let
`δ_M = δ(M.P) = ⨆ (s, a) (s', a'), tvDist (P (s, a)) (P (s', a')) / 2` be the Dobrushin coefficient
of the transition kernel, taken over all pairs of state-action pairs
(`ProbabilityTheory.Kernel.dobrushinCoeff`). Then `T` contracts the span at rate `γ * δ_M`:
`sp (T u - T v) ≤ γ * δ_M * sp (u - v)` [P, Theorem 6.6.6]. Applied to `u = T v`, this gives
`sp (T² v - T v) ≤ γ * δ_M * sp (T v - v)` [P, Corollary 6.6.7], and by induction the increments of
value iteration have spans `sp (T^[n + 1] v - T^[n] v) ≤ (γ * δ_M) ^ n * sp (T v - v)`.

Since `δ_M ≤ 1`, the rate `γ * δ_M` is never worse than the rate `γ` of the sup-norm contraction,
and it can be much better: it is `0` when all the transition laws are equal, and Doeblin's
condition `φ ≤ P (s, a)` for all `(s, a)` gives `δ_M ≤ 1 - φ univ`
(`ProbabilityTheory.Kernel.dobrushinCoeff_le_one_sub_of_forall_le`). The span of the increment
`T v - v` is the quantity tested by the span stopping rule of value iteration
(`Learning.MDP.abs_value_sub_optValue_lt_of_orderUnitOsc_lt`), and the bound on the increments says
that along value iteration it decays at the rate `γ * δ_M`.

Puterman states these results on a finite state space with the coefficient
`1 - min Σ_j min (p (j | s, a), p (j | s', a'))`, which is the Dobrushin coefficient of `M.P` on a
finite space. Here they hold on a general measurable state space, with the supremum over the
actions in place of a maximum: the pointwise bound holds for every action space, and the bounds
on `LMLExplore.boundedMeasurable 𝓢` for countably many actions, where `T` acts on it as
`M.bellmanOp γ hR`.

## Main statements

* `Learning.MDP.bellman_sub_bellman_apply_sub_apply_le`: the pointwise span contraction: if the
  values of `u - v` differ by at most `c`, the values of `T u - T v` differ by at most
  `γ * δ_M * c`.
* `Learning.MDP.orderUnitOsc_bellmanOp_sub_bellmanOp_le`: the span contraction
  `sp (T u - T v) ≤ γ * δ_M * sp (u - v)` on the bounded measurable functions [P, Theorem 6.6.6].
* `Learning.MDP.orderUnitOsc_bellmanOp_iterate_succ_sub_le`: the spans of the increments of value
  iteration, `sp (T^[n + 1] v - T^[n] v) ≤ (γ * δ_M) ^ n * sp (T v - v)`; the case `n = 1` is
  [P, Corollary 6.6.7]. `Learning.MDP.bellman_iterate_succ_sub_apply_sub_apply_le` is its
  pointwise form.

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], Theorem 6.6.6, Corollary 6.6.7 and
  (8.5.6)
-/

public section

open MeasureTheory ProbabilityTheory Set Function LMLExplore Learning
open scoped ENNReal NNReal lp

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {u v : 𝓢 → ℝ} {B B' C c : ℝ}

/-- **Span contraction of the optimality operator**, pointwise form [P, Theorem 6.6.6]: with
bounded rewards, if `u` and `v` are bounded measurable and the values of `u - v` differ by at most
`c`, then the values of `T u - T v` differ by at most `γ * δ(M.P) * c`, where `T = M.bellman γ` and
`δ(M.P)` is the Dobrushin coefficient of the transition kernel. This holds for every action space:
the suprema defining `T` need not be attained. -/
theorem bellman_sub_bellman_apply_sub_apply_le [Nonempty 𝓐] (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hu : Measurable u) (huB : ∀ s, |u s| ≤ B) (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B')
    (hc : ∀ x y, (u - v) x - (u - v) y ≤ c) (s s' : 𝓢) :
    (M.bellman γ u - M.bellman γ v) s - (M.bellman γ u - M.bellman γ v) s' ≤
      γ * Kernel.dobrushinCoeff M.P * c := by
  -- the lookaheads of `u` and `v` differ by `γ` times the integral of `u - v`
  have hdiff (p : 𝓢 × 𝓐) :
      M.lookahead γ u p - M.lookahead γ v p = γ * ∫ z, (u - v) z ∂(M.P p) := by
    simp only [lookahead_def, Pi.sub_apply,
      integral_sub (integrable_of_abs_le hu huB _) (integrable_of_abs_le hv hvB _)]
    ring
  have hu_bdd := bddAbove_range_lookahead (γ := γ) hR huB
  have hv_bdd := bddAbove_range_lookahead (γ := γ) hR hvB
  -- for every `ε > 0`, pick actions `ε / 2`-greedy for `u` at `s` and for `v` at `s'`
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨a, ha⟩ := exists_lt_of_lt_ciSup (f := fun a ↦ M.lookahead γ u (s, a))
    (b := M.bellman γ u s - ε / 2) (by rw [bellman_def]; linarith)
  obtain ⟨a', ha'⟩ := exists_lt_of_lt_ciSup (f := fun a ↦ M.lookahead γ v (s', a))
    (b := M.bellman γ v s' - ε / 2) (by rw [bellman_def]; linarith)
  have hvs := lookahead_le_bellman (hv_bdd s) a
  have hus' := lookahead_le_bellman (hu_bdd s') a'
  -- the integrals of `u - v` against `P (s, a)` and `P (s', a')` differ by at most `δ(M.P) * c`
  have hδ := (le_abs_self _).trans <| Kernel.abs_integral_sub_integral_le_dobrushinCoeff_mul
    (κ := M.P) (hu.sub hv) hc (s, a) (s', a')
  have hγδ := mul_le_mul_of_nonneg_left hδ γ.coe_nonneg
  have h₁ := hdiff (s, a)
  have h₂ := hdiff (s', a')
  simp only [Pi.sub_apply]
  linarith

/-- The rate `γ * δ(M.P)` of the span contraction is nonnegative. -/
private lemma mul_dobrushinCoeff_nonneg : 0 ≤ (γ : ℝ) * Kernel.dobrushinCoeff M.P :=
  mul_nonneg γ.coe_nonneg (Kernel.dobrushinCoeff_nonneg M.P)

variable [Countable 𝓐] [Nonempty 𝓐] (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
include hR

/-- **Span contraction of the optimality operator** [P, Theorem 6.6.6]: with bounded rewards and
countably many actions, the optimality operator on the bounded measurable functions satisfies
`sp (T u - T v) ≤ γ * δ(M.P) * sp (u - v)`, where the span `sp` is the oscillation
`LMLExplore.orderUnitOsc 1` and `δ(M.P)` is the Dobrushin coefficient of the transition kernel. -/
theorem orderUnitOsc_bellmanOp_sub_bellmanOp_le (u v : boundedMeasurable 𝓢) :
    orderUnitOsc 1 (M.bellmanOp γ hR u - M.bellmanOp γ hR v) ≤
      γ * Kernel.dobrushinCoeff M.P * orderUnitOsc 1 (u - v) := by
  refine boundedMeasurable.orderUnitOsc_one_le_of_forall_sub_le
    (mul_nonneg mul_dobrushinCoeff_nonneg (orderUnitOsc_nonneg 1 (u - v))) fun s s' ↦ ?_
  simp only [boundedMeasurable.coeFn_sub, coeFn_bellmanOp]
  refine bellman_sub_bellman_apply_sub_apply_le hR (boundedMeasurable.measurable u)
    (boundedMeasurable.abs_apply_le_norm u) (boundedMeasurable.measurable v)
    (boundedMeasurable.abs_apply_le_norm v) (fun x y ↦ ?_) s s'
  simpa only [boundedMeasurable.coeFn_sub] using
    boundedMeasurable.sub_apply_le_orderUnitOsc_one (u - v) x y

/-- **Span contraction of the increments of value iteration** [P, Corollary 6.6.7, (8.5.6)]: with
bounded rewards and countably many actions, the increments of value iteration on the bounded
measurable functions satisfy `sp (T^[n + 1] v - T^[n] v) ≤ (γ * δ(M.P)) ^ n * sp (T v - v)`, where
the span `sp` is the oscillation `LMLExplore.orderUnitOsc 1` and `δ(M.P)` is the Dobrushin
coefficient of the transition kernel. The case `n = 1` is
`sp (T² v - T v) ≤ γ * δ(M.P) * sp (T v - v)` [P, Corollary 6.6.7]. -/
theorem orderUnitOsc_bellmanOp_iterate_succ_sub_le (v : boundedMeasurable 𝓢) (n : ℕ) :
    orderUnitOsc 1 ((M.bellmanOp γ hR)^[n + 1] v - (M.bellmanOp γ hR)^[n] v) ≤
      (γ * Kernel.dobrushinCoeff M.P) ^ n * orderUnitOsc 1 (M.bellmanOp γ hR v - v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply' _ n] at ih
    rw [iterate_succ_apply' _ (n + 1), iterate_succ_apply' _ n, pow_succ', mul_assoc]
    exact (orderUnitOsc_bellmanOp_sub_bellmanOp_le hR _ _).trans
      (mul_le_mul_of_nonneg_left ih mul_dobrushinCoeff_nonneg)

/-- **Span contraction of the increments of value iteration**, pointwise form
[P, Corollary 6.6.7, (8.5.6)]: with bounded rewards and countably many actions, if `v` is bounded
measurable and the values of `T v - v` differ by at most `c`, then the values of
`T^[n + 1] v - T^[n] v` differ by at most `(γ * δ(M.P)) ^ n * c`, where `δ(M.P)` is the Dobrushin
coefficient of the transition kernel. -/
theorem bellman_iterate_succ_sub_apply_sub_apply_le (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B)
    (hc : ∀ x y, (M.bellman γ v - v) x - (M.bellman γ v - v) y ≤ c) (n : ℕ) (s s' : 𝓢) :
    ((M.bellman γ)^[n + 1] v - (M.bellman γ)^[n] v) s -
        ((M.bellman γ)^[n + 1] v - (M.bellman γ)^[n] v) s' ≤
      (γ * Kernel.dobrushinCoeff M.P) ^ n * c := by
  set w := boundedMeasurable.mk v hv (bddAbove_def.2 ⟨B, forall_mem_range.2 hvB⟩)
  have hw : ⇑(w : ℓ^∞(𝓢, ℝ)) = v := boundedMeasurable.coeFn_mk ..
  have hc₀ : 0 ≤ c := by simpa using hc s s
  have hosc : orderUnitOsc 1 (M.bellmanOp γ hR w - w) ≤ c :=
    boundedMeasurable.orderUnitOsc_one_le_of_forall_sub_le hc₀ fun x y ↦ by
      simpa only [boundedMeasurable.coeFn_sub, coeFn_bellmanOp, hw] using hc x y
  have h := boundedMeasurable.sub_apply_le_orderUnitOsc_one
    ((M.bellmanOp γ hR)^[n + 1] w - (M.bellmanOp γ hR)^[n] w) s s'
  simp only [boundedMeasurable.coeFn_sub, coeFn_bellmanOp_iterate, hw] at h
  exact h.trans <| (orderUnitOsc_bellmanOp_iterate_succ_sub_le hR w n).trans
    (mul_le_mul_of_nonneg_left hosc (pow_nonneg mul_dobrushinCoeff_nonneg n))

end Learning.MDP
