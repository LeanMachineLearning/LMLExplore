/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Comparison

/-!
# Bounds on the optimal value and the span stopping rule

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP on a measurable state space `𝓢` with bounded rewards, and let
`0 ≤ γ < 1`. Write `T` for the Bellman optimality operator `M.bellman γ`, `T_π` for the evaluation
operator `M.bellmanEval γ π` of a stationary policy `π`, `P_π` for its state kernel, `v^π` for its
value and `v*` for the optimal value. For a bounded measurable `v`, the increment `T v - v` of one
step of value iteration brackets the values: if `a ≤ T v - v ≤ b` and `π` is greedy for `v`, that
is `T_π v = T v`, then for every `n`
`v + ∑ k < n, (γ P_π) ^ k (T v - v) + γ ^ n * a / (1 - γ) ≤ v^π ≤ v*` and
`v* ≤ T^[n] v + γ ^ n * b / (1 - γ)`.
This is [P, Theorem 6.6.3] with `n = m + 1`, where `a` and `b` are the infimum and the supremum
of `T v - v`; the cases `n = 0` and `n = 1` are [P, Corollary 6.6.4]. The sum on the left is
`T_π^[n] v - v` (`Learning.MDP.bellmanEval_iterate_eq_add_sum`).

For `n ≥ 2`, the upper bound printed in [P, (6.6.9)] has `T_π^[n] v`, written as
`v + ∑ k < n, (γ P_π) ^ k (T v - v)`, in place of `T^[n] v`, and it does not hold in general. For
`γ = 1 / 2`, take two states: in state `1`, two actions with reward `0` lead to state `1` and to
state `2`; in state `2`, every action has reward `1` and leads to state `2`. For `v = 0`, both
actions are greedy in state `1`, and the policy `π` staying there has `T_π^[2] v (1) = 0`, so the
printed bound gives `v* (1) ≤ 1 / 2`, while `v* (1) = 1`. The upper bound stated here, with
`T^[n] v`, is the corrected one.

Comparing the two sides for `n = 1` gives the *span stopping rule* [P, Proposition 6.6.5]: if
`γ * (b - a) < (1 - γ) * ε`, then both `T v + γ * a / (1 - γ)` and the value of every policy greedy
for `v` are within `ε` of `v*`. With `a` and `b` the infimum and the supremum of `T v - v`, the
condition reads `γ * sp (T v - v) < (1 - γ) * ε`, where `sp` is the span seminorm, the oscillation
`LMLExplore.orderUnitOsc 1`.

Puterman states these results on a finite state space. Here they hold on a general measurable
state space, with explicit bounds `a ≤ T v - v ≤ b` in place of the infimum and the supremum. The
lower bounds hold for every stationary policy `π` with `a ≤ T_π v - v`, and only the bounds
involving `v*` assume finitely many actions.

## Main statements

* `Learning.MDP.bellmanEval_iterate_succ_sub`, `Learning.MDP.bellmanEval_iterate_eq_add_sum`: the
  increments of the iterates of `T_π` are `T_π^[n + 1] v - T_π^[n] v = (γ P_π) ^ n (T_π v - v)`,
  so `T_π^[n] v = v + ∑ k < n, (γ P_π) ^ k (T_π v - v)`.
* `Learning.MDP.bellmanEval_iterate_add_le_value`, `Learning.MDP.add_sum_add_le_value`: the lower
  bound `T_π^[n] v + γ ^ n * a / (1 - γ) ≤ v^π` when `a ≤ T_π v - v` [P, Theorem 6.6.3].
* `Learning.MDP.optValue_le_bellman_iterate_add`: the upper bound
  `v* ≤ T^[n] v + γ ^ n * b / (1 - γ)` when `T v - v ≤ b`, corrected from [P, Theorem 6.6.3].
* `Learning.MDP.abs_bellman_add_sub_optValue_lt`,
  `Learning.MDP.abs_value_sub_optValue_lt_of_bellmanEval_eq`,
  `Learning.MDP.abs_value_sub_optValue_lt_of_orderUnitOsc_lt`: the span stopping rule
  [P, Proposition 6.6.5].

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §6.6.3
-/

public section

open MeasureTheory ProbabilityTheory Set Function LMLExplore Learning
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {v : 𝓢 → ℝ} {B C a b ε : ℝ}

/-- `x + c` with `c = γ ^ n * a / (1 - γ)` equals `x + γ ^ n * a + γ * c`: the constant shifts
of the bounds are the fixed points of `c ↦ γ ^ n * a + γ * c`. -/
private lemma add_div_one_sub_eq (hγ : γ < 1) (x : ℝ) (n : ℕ) :
    x + (γ : ℝ) ^ n * a / (1 - γ) = x + (γ : ℝ) ^ n * a + γ * ((γ : ℝ) ^ n * a / (1 - γ)) := by
  have h1γ : (1 - γ : ℝ) ≠ 0 := (sub_pos.2 (NNReal.coe_lt_one.2 hγ)).ne'
  field_simp
  ring

/-! ### Iterates of the evaluation operator -/

section Evaluation

variable {π : Kernel 𝓢 𝓐} [IsMarkovKernel π]

private lemma measurable_bellmanEval_iterate (hv : Measurable v) (n : ℕ) :
    Measurable ((M.bellmanEval γ π)^[n] v) := by
  induction n with
  | zero => exact hv
  | succ n ih => rw [iterate_succ']; exact measurable_bellmanEval ih

private lemma exists_abs_bellmanEval_iterate_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hvB : ∀ s, |v s| ≤ B) (n : ℕ) : ∃ B', ∀ s, |(M.bellmanEval γ π)^[n] v s| ≤ B' := by
  induction n with
  | zero => exact ⟨B, hvB⟩
  | succ n ih =>
    obtain ⟨B', hB'⟩ := ih
    exact ⟨C + γ * B', fun s ↦ by rw [iterate_succ_apply']; exact abs_bellmanEval_le hR hB' s⟩

/-- With bounded rewards, the increments of the iterates of the evaluation operator `T_π` of a
stationary policy at a bounded measurable `v` are
`T_π^[n + 1] v - T_π^[n] v = γ ^ n P_π ^ n (T_π v - v)`, where `P_π` is the state kernel of `π`. -/
theorem bellmanEval_iterate_succ_sub (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (n : ℕ) (s : 𝓢) :
    (M.bellmanEval γ π)^[n + 1] v s - (M.bellmanEval γ π)^[n] v s =
      (γ : ℝ) ^ n * ∫ s', (M.bellmanEval γ π v s' - v s') ∂((M.stateKernel π ^ n) s) := by
  have hg : Measurable fun s' ↦ M.bellmanEval γ π v s' - v s' :=
    (measurable_bellmanEval hv).sub hv
  have hgB (s' : 𝓢) : |M.bellmanEval γ π v s' - v s'| ≤ (C + γ * B) + B :=
    (abs_sub _ _).trans (add_le_add (abs_bellmanEval_le hR hvB s') (hvB s'))
  induction n generalizing s with
  | zero =>
    simp only [zero_add, iterate_one, iterate_zero, id_eq, pow_zero, one_mul, Kernel.one_eq_id,
      Kernel.id_apply]
    rw [integral_dirac' _ s hg.stronglyMeasurable]
  | succ n ih =>
    obtain ⟨B₀, hB₀⟩ := exists_abs_bellmanEval_iterate_le (π := π) (γ := γ) hR hvB n
    obtain ⟨B₁, hB₁⟩ := exists_abs_bellmanEval_iterate_le (π := π) (γ := γ) hR hvB (n + 1)
    have hm₀ := measurable_bellmanEval_iterate (M := M) (γ := γ) (π := π) hv n
    have hm₁ := measurable_bellmanEval_iterate (M := M) (γ := γ) (π := π) hv (n + 1)
    calc (M.bellmanEval γ π)^[n + 1 + 1] v s - (M.bellmanEval γ π)^[n + 1] v s
        = M.bellmanEval γ π ((M.bellmanEval γ π)^[n + 1] v) s -
            M.bellmanEval γ π ((M.bellmanEval γ π)^[n] v) s := by
          rw [iterate_succ_apply' _ (n + 1), iterate_succ_apply' _ n]
      _ = γ * ∫ s', ((M.bellmanEval γ π)^[n + 1] v s' - (M.bellmanEval γ π)^[n] v s')
            ∂(M.stateKernel π s) := by
          rw [bellmanEval_eq_policyReward_add hR hm₁ hB₁,
            bellmanEval_eq_policyReward_add hR hm₀ hB₀,
            integral_sub (integrable_of_abs_le hm₁ hB₁ _) (integrable_of_abs_le hm₀ hB₀ _)]
          ring
      _ = γ * ∫ s', (γ : ℝ) ^ n * ∫ s'', (M.bellmanEval γ π v s'' - v s'')
            ∂((M.stateKernel π ^ n) s') ∂(M.stateKernel π s) := by
          simp_rw [ih]
      _ = (γ : ℝ) ^ (n + 1) * ∫ s', (M.bellmanEval γ π v s' - v s')
            ∂((M.stateKernel π ^ (n + 1)) s) := by
          rw [integral_const_mul, pow_succ (M.stateKernel π) n, Kernel.mul_eq_comp,
            Kernel.integral_comp (integrable_of_abs_le hg hgB _)]
          ring

/-- **Expansion of the iterates of the evaluation operator**: with bounded rewards, the iterates of
the evaluation operator `T_π` of a stationary policy at a bounded measurable `v` are
`T_π^[n] v = v + ∑ k < n, γ ^ k P_π ^ k (T_π v - v)`, where `P_π` is the state kernel of `π`. As
`n → ∞`, this becomes the Newton form `Learning.MDP.value_eq_add_tsum` of the value. -/
theorem bellmanEval_iterate_eq_add_sum (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (n : ℕ) (s : 𝓢) :
    (M.bellmanEval γ π)^[n] v s = v s + ∑ k ∈ Finset.range n, (γ : ℝ) ^ k *
      ∫ s', (M.bellmanEval γ π v s' - v s') ∂((M.stateKernel π ^ k) s) := by
  have h := Finset.sum_range_sub (fun k ↦ (M.bellmanEval γ π)^[k] v s) n
  simp only [bellmanEval_iterate_succ_sub hR hv hvB, iterate_zero, id_eq] at h
  rw [h]
  ring

variable [Nonempty 𝓢]

/-- **Lower bound on the value** [P, Theorem 6.6.3]: with bounded rewards and `γ < 1`, if a bounded
measurable `v` satisfies `a ≤ T_π v - v`, where `T_π` is the evaluation operator of the stationary
policy `π`, then `T_π^[n] v + γ ^ n * a / (1 - γ) ≤ v^π` for every `n`. -/
theorem bellmanEval_iterate_add_le_value (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (ha : ∀ s, a ≤ M.bellmanEval γ π v s - v s)
    (n : ℕ) (s : 𝓢) :
    (M.bellmanEval γ π)^[n] v s + (γ : ℝ) ^ n * a / (1 - γ) ≤ M.value γ π s := by
  obtain ⟨B', hB'⟩ := exists_abs_bellmanEval_iterate_le (π := π) (γ := γ) hR hvB n
  have hm := measurable_bellmanEval_iterate (M := M) (γ := γ) (π := π) hv n
  set u := (M.bellmanEval γ π)^[n] v
  set c := (γ : ℝ) ^ n * a / (1 - γ)
  -- the increment `T_π u - u = γ ^ n P_π ^ n (T_π v - v)` is at least `γ ^ n * a`
  have hinc (s : 𝓢) : u s + (γ : ℝ) ^ n * a ≤ M.bellmanEval γ π u s := by
    have h := bellmanEval_iterate_succ_sub (M := M) (γ := γ) (π := π) hR hv hvB n s
    rw [iterate_succ_apply'] at h
    have hint : a ≤ ∫ s', (M.bellmanEval γ π v s' - v s') ∂((M.stateKernel π ^ n) s) := by
      calc a = ∫ _, a ∂((M.stateKernel π ^ n) s) := by simp
        _ ≤ _ := integral_mono (integrable_const a)
            (integrable_of_abs_le ((measurable_bellmanEval hv).sub hv)
              (fun s' ↦ (abs_sub _ _).trans (add_le_add (abs_bellmanEval_le hR hvB s') (hvB s')))
              _) ha
    linarith [mul_le_mul_of_nonneg_left hint (pow_nonneg γ.coe_nonneg n)]
  -- so `u + c` is a subsolution of the evaluation equation of `π`
  have hle : (u + fun _ ↦ c) ≤ M.bellmanEval γ π (u + fun _ ↦ c) := fun s ↦ by
    rw [bellmanEval_add_const hR hm hB' c, Pi.add_apply, Pi.add_apply,
      add_div_one_sub_eq hγ (u s) n]
    linarith [hinc s]
  exact le_value_of_le_bellmanEval hγ hR (hm.add measurable_const)
    (fun s ↦ (abs_add_le _ _).trans (add_le_add (hB' s) le_rfl)) hle s

/-- **Lower bound on the value** [P, Theorem 6.6.3], in Puterman's form: with bounded rewards and
`γ < 1`, if a bounded measurable `v` satisfies `a ≤ T_π v - v`, where `T_π` is the evaluation
operator of the stationary policy `π` and `P_π` its state kernel, then
`v + ∑ k < n, γ ^ k P_π ^ k (T_π v - v) + γ ^ n * a / (1 - γ) ≤ v^π` for every `n`. For `π`
greedy for `v`, `T_π v - v = T v - v`. -/
theorem add_sum_add_le_value (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (ha : ∀ s, a ≤ M.bellmanEval γ π v s - v s)
    (n : ℕ) (s : 𝓢) :
    v s + ∑ k ∈ Finset.range n, (γ : ℝ) ^ k *
        ∫ s', (M.bellmanEval γ π v s' - v s') ∂((M.stateKernel π ^ k) s) +
      (γ : ℝ) ^ n * a / (1 - γ) ≤ M.value γ π s := by
  rw [← bellmanEval_iterate_eq_add_sum hR hv hvB]
  exact bellmanEval_iterate_add_le_value hγ hR hv hvB ha n s

end Evaluation

/-! ### Upper bound on the optimal value -/

section Optimality

private lemma measurable_bellman_iterate [Countable 𝓐] (hv : Measurable v) (n : ℕ) :
    Measurable ((M.bellman γ)^[n] v) := by
  induction n with
  | zero => exact hv
  | succ n ih => rw [iterate_succ']; exact measurable_bellman ih

private lemma exists_abs_bellman_iterate_le [Nonempty 𝓐] (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hvB : ∀ s, |v s| ≤ B) (n : ℕ) : ∃ B', ∀ s, |(M.bellman γ)^[n] v s| ≤ B' := by
  induction n with
  | zero => exact ⟨B, hvB⟩
  | succ n ih =>
    obtain ⟨B', hB'⟩ := ih
    exact ⟨C + γ * B', fun s ↦ by rw [iterate_succ_apply']; exact abs_bellman_le hR hB' s⟩

variable [Finite 𝓐] [Nonempty 𝓐]

/-- With finitely many actions and bounded rewards, if a bounded measurable `v` satisfies
`T v - v ≤ b`, then the increments of value iteration satisfy
`T^[n + 1] v - T^[n] v ≤ γ ^ n * b`. -/
private lemma bellman_iterate_succ_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (hb : ∀ s, M.bellman γ v s - v s ≤ b) (n : ℕ) (s : 𝓢) :
    (M.bellman γ)^[n + 1] v s ≤ (M.bellman γ)^[n] v s + (γ : ℝ) ^ n * b := by
  induction n generalizing s with
  | zero => simpa using (sub_le_iff_le_add').1 (hb s)
  | succ n ih =>
    obtain ⟨B₀, hB₀⟩ := exists_abs_bellman_iterate_le (M := M) (γ := γ) hR hvB n
    obtain ⟨B₁, hB₁⟩ := exists_abs_bellman_iterate_le (M := M) (γ := γ) hR hvB (n + 1)
    have hm₀ := measurable_bellman_iterate (M := M) (γ := γ) hv n
    have hm₁ := measurable_bellman_iterate (M := M) (γ := γ) hv (n + 1)
    have hint₀ (p : 𝓢 × 𝓐) : Integrable ((M.bellman γ)^[n] v) (M.P p) :=
      integrable_of_abs_le hm₀ hB₀ _
    calc (M.bellman γ)^[n + 1 + 1] v s = M.bellman γ ((M.bellman γ)^[n + 1] v) s := by
          rw [iterate_succ_apply']
      _ ≤ M.bellman γ ((M.bellman γ)^[n] v + fun _ ↦ (γ : ℝ) ^ n * b) s :=
          bellman_mono (fun _ ↦ integrable_of_abs_le hm₁ hB₁ _)
            (fun p ↦ (hint₀ p).add (integrable_const _)) (fun _ ↦ Finite.bddAbove_range _)
            (fun s ↦ ih s) s
      _ = M.bellman γ ((M.bellman γ)^[n] v) s + γ * ((γ : ℝ) ^ n * b) := by
          rw [bellman_add_const hint₀ (fun _ ↦ Finite.bddAbove_range _), Pi.add_apply]
      _ = (M.bellman γ)^[n + 1] v s + (γ : ℝ) ^ (n + 1) * b := by
          rw [iterate_succ_apply']
          ring

variable [Nonempty 𝓢]

/-- **Upper bound on the optimal value**, the corrected upper bound of [P, Theorem 6.6.3]: with
finitely many actions, bounded rewards and `γ < 1`, if a bounded measurable `v` satisfies
`T v - v ≤ b`, where `T` is the Bellman optimality operator, then
`v* ≤ T^[n] v + γ ^ n * b / (1 - γ)` for every `n`. -/
theorem optValue_le_bellman_iterate_add (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (hb : ∀ s, M.bellman γ v s - v s ≤ b) (n : ℕ)
    (s : 𝓢) :
    M.optValue γ s ≤ (M.bellman γ)^[n] v s + (γ : ℝ) ^ n * b / (1 - γ) := by
  obtain ⟨B', hB'⟩ := exists_abs_bellman_iterate_le (M := M) (γ := γ) hR hvB n
  have hm := measurable_bellman_iterate (M := M) (γ := γ) hv n
  set u := (M.bellman γ)^[n] v
  set c := (γ : ℝ) ^ n * b / (1 - γ)
  -- `u + c` is a supersolution of the optimality equation
  have hle : M.bellman γ (u + fun _ ↦ c) ≤ u + fun _ ↦ c := fun s ↦ by
    have h := bellman_iterate_succ_le hR hv hvB hb n s
    rw [iterate_succ_apply'] at h
    rw [bellman_add_const (fun _ ↦ integrable_of_abs_le hm hB' _)
      (fun _ ↦ Finite.bddAbove_range _), Pi.add_apply, Pi.add_apply,
      add_div_one_sub_eq hγ (u s) n]
    linarith
  exact optValue_le_of_bellman_le hγ hR (hm.add measurable_const)
    (fun s ↦ (abs_add_le _ _).trans (add_le_add (hB' s) le_rfl)) hle s

/-! ### The span stopping rule -/

/-- The two-sided bound `T v + γ * a / (1 - γ) ≤ v^π ≤ v* ≤ T v + γ * b / (1 - γ)` for a stationary
policy `π` greedy for `v` and `a ≤ T v - v ≤ b` ([P, Corollary 6.6.4], the case `m = 0`). -/
private lemma bellman_add_le_value_and_optValue_le_bellman_add {π : Kernel 𝓢 𝓐}
    [IsMarkovKernel π] (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (hπ : M.bellmanEval γ π v = M.bellman γ v)
    (ha : ∀ s, a ≤ M.bellman γ v s - v s) (hb : ∀ s, M.bellman γ v s - v s ≤ b) (s : 𝓢) :
    M.bellman γ v s + γ * a / (1 - γ) ≤ M.value γ π s ∧
      M.optValue γ s ≤ M.bellman γ v s + γ * b / (1 - γ) := by
  have h₁ := bellmanEval_iterate_add_le_value hγ hR hv hvB (fun s ↦ hπ ▸ ha s) 1 s
  have h₂ := optValue_le_bellman_iterate_add hγ hR hv hvB hb 1 s
  rw [iterate_one, hπ, pow_one] at h₁
  rw [iterate_one, pow_one] at h₂
  exact ⟨h₁, h₂⟩

/-- `γ * b / (1 - γ) - γ * a / (1 - γ) < ε` when `γ * (b - a) < (1 - γ) * ε`. -/
private lemma sub_lt_of_mul_sub_lt (hγ : γ < 1) (hε : γ * (b - a) < (1 - γ) * ε) :
    γ * b / (1 - γ) - γ * a / (1 - γ) < ε := by
  rw [← sub_div, div_lt_iff₀ (sub_pos.2 (NNReal.coe_lt_one.2 hγ))]
  linarith

/-- **The span stopping rule**, its bound on the optimal value [P, Proposition 6.6.5]: with
finitely many actions, bounded rewards and `γ < 1`, if a bounded measurable `v` satisfies
`a ≤ T v - v ≤ b` with `γ * (b - a) < (1 - γ) * ε`, then `T v + γ * a / (1 - γ)` is within `ε` of
the optimal value. -/
theorem abs_bellman_add_sub_optValue_lt (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (ha : ∀ s, a ≤ M.bellman γ v s - v s)
    (hb : ∀ s, M.bellman γ v s - v s ≤ b) (hε : γ * (b - a) < (1 - γ) * ε) (s : 𝓢) :
    |M.bellman γ v s + γ * a / (1 - γ) - M.optValue γ s| < ε := by
  have := Fintype.ofFinite 𝓐
  obtain ⟨h₁, h₂⟩ := bellman_add_le_value_and_optValue_le_bellman_add hγ hR hv hvB
    (bellmanEval_greedy hv) ha hb s
  have h₃ := value_le_optValue
    (π := Kernel.deterministic _ (measurable_greedy (M := M) (γ := γ) hv)) hγ hR s
  have h₄ := sub_lt_of_mul_sub_lt hγ hε
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- **The span stopping rule**, its policy [P, Proposition 6.6.5]: with finitely many actions,
bounded rewards and `γ < 1`, if a bounded measurable `v` satisfies `a ≤ T v - v ≤ b` with
`γ * (b - a) < (1 - γ) * ε`, then every stationary policy `π` greedy for `v`, `T_π v = T v`, is
`ε`-optimal: its value is within `ε` of the optimal value. -/
theorem abs_value_sub_optValue_lt_of_bellmanEval_eq {π : Kernel 𝓢 𝓐} [IsMarkovKernel π]
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B)
    (hπ : M.bellmanEval γ π v = M.bellman γ v) (ha : ∀ s, a ≤ M.bellman γ v s - v s)
    (hb : ∀ s, M.bellman γ v s - v s ≤ b) (hε : γ * (b - a) < (1 - γ) * ε) (s : 𝓢) :
    |M.value γ π s - M.optValue γ s| < ε := by
  obtain ⟨h₁, h₂⟩ := bellman_add_le_value_and_optValue_le_bellman_add hγ hR hv hvB hπ ha hb s
  have h₃ := value_le_optValue (π := π) hγ hR s
  have h₄ := sub_lt_of_mul_sub_lt hγ hε
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- **The span stopping rule** [P, Proposition 6.6.5], with the span: with finitely many actions,
bounded rewards and `γ < 1`, if a bounded measurable `v` satisfies
`γ * sp (T v - v) < (1 - γ) * ε`, where the span `sp` is the oscillation
`LMLExplore.orderUnitOsc 1`, then every stationary policy `π` greedy for `v`, `T_π v = T v`, is
`ε`-optimal. -/
theorem abs_value_sub_optValue_lt_of_orderUnitOsc_lt {π : Kernel 𝓢 𝓐} [IsMarkovKernel π]
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B)
    (hπ : M.bellmanEval γ π v = M.bellman γ v)
    (hosc : γ * orderUnitOsc 1 (M.bellman γ v - v) < (1 - γ) * ε) (s : 𝓢) :
    |M.value γ π s - M.optValue γ s| < ε := by
  set K := (C + γ * B) + B
  have hK (s : 𝓢) : |M.bellman γ v s - v s| ≤ K :=
    (abs_sub _ _).trans (add_le_add (abs_bellman_le hR hvB s) (hvB s))
  have hIcc {a d : ℝ} : M.bellman γ v - v ∈ Icc (a • (1 : 𝓢 → ℝ)) ((a + d) • 1) ↔
      ∀ s, a ≤ M.bellman γ v s - v s ∧ M.bellman γ v s - v s ≤ a + d := by
    simp [Pi.le_def, forall_and]
  -- `T v - v` is bounded, so its span is approximated by the lengths of its bounding intervals
  set osc := orderUnitOsc 1 (M.bellman γ v - v)
  set η := ((1 - γ) * ε - γ * osc) / (γ + 1)
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  obtain ⟨d, -, hd, a, hx⟩ := exists_mem_Icc_smul_of_orderUnitOsc_lt (r := osc + η)
    ⟨2 * K, by linarith [(abs_nonneg _).trans (hK s)], -K,
      hIcc.2 fun s ↦ ⟨by linarith [neg_abs_le (M.bellman γ v s - v s), hK s],
        by linarith [le_abs_self (M.bellman γ v s - v s), hK s]⟩⟩
    (lt_add_of_pos_right _ hη)
  refine abs_value_sub_optValue_lt_of_bellmanEval_eq hγ hR hv hvB hπ (a := a) (b := a + d)
    (fun s ↦ (hIcc.1 hx s).1) (fun s ↦ (hIcc.1 hx s).2) ?_ s
  -- `γ * d ≤ γ * (osc + η) < γ * osc + (γ + 1) * η = (1 - γ) * ε`
  have hηeq : (γ + 1) * η = (1 - γ) * ε - γ * osc := mul_div_cancel₀ _ (by positivity)
  linarith [mul_le_mul_of_nonneg_left hd.le γ.coe_nonneg]

end Optimality

end Learning.MDP
