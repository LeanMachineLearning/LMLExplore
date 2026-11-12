/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.FixedPoint.DynamicProgramming
public import LMLExplore.MarkovDecisionProcess.Bellman
public import LMLExplore.MarkovDecisionProcess.Value

/-!
# Bellman operators on bounded measurable functions and value iteration

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP on a measurable state space `𝓢`, with rewards bounded by `C`, and
let `0 ≤ γ < 1`. The Bellman optimality operator `M.bellman γ`, for countably many actions, and the
evaluation operator `M.bellmanEval γ π` of a stationary policy `π` map bounded measurable functions
to bounded measurable functions. They therefore act on the Banach space
`LMLExplore.boundedMeasurable 𝓢` of bounded measurable functions with the sup norm, as
`M.bellmanOp γ hR` and `M.bellmanEvalOp γ π hR`. The evaluation operator is the affine map
`v ↦ r_π + γ P_π v`, where `r_π` is the mean reward of `π` and the state kernel
`P_π = M.stateKernel π` acts by `Kernel.integralCLM`.

On that space they satisfy Blackwell's conditions for the constant function `1`, whose order-unit
norm is the sup norm, so they are `γ`-contractions [P, Proposition 6.2.4] and Banach's fixed point
theorem applies. This gives, on a general measurable state space,
* the pointwise contraction bounds: `|v - w| ≤ D` gives `|T v - T w| ≤ γ * D` for bounded
  measurable `v` and `w`;
* a unique bounded measurable solution of the optimality equation `M.bellman γ u = u`, bounded by
  `C / (1 - γ)` (the fixed-point part of [P, Theorem 6.2.5 (a)], where `𝓢` is countable);
* the convergence of value iteration `v, T v, T² v, …` to it at the geometric rate
  `|Tⁿ v - u| ≤ γ ^ n * ‖T v - v‖ / (1 - γ)` [P, Theorem 6.3.3 (d)];
* the geometric decay of its increments, `|Tⁿ⁺¹ v - Tⁿ v| ≤ γ ^ n * D` where `D` bounds
  `|T v - v|` at every state [P, Theorem 6.3.1 (b)];
* monotone iterates: they decrease (resp. increase) from the first one with `T v ≤ v`
  (resp. `v ≤ T v`) [P, Proposition 6.3.2 (b)].

For countably many actions, the evaluation operators of the stationary policies are below the
optimality operator, and for finitely many actions, at every `v` the greedy policy for `v`, which
is measurable and deterministic, attains it. Together with Blackwell's conditions, this makes the
operators an instance of the abstract dynamic programming of `LMLExplore.IsPolicyIteration` and
`LMLExplore.IsModifiedPolicyIteration`, with `boundedMeasurable 𝓢` as space of values.

## Main definitions

* `Learning.MDP.bellmanOp M γ hR`: the optimality operator acting on `boundedMeasurable 𝓢`.
* `Learning.MDP.policyRewardBM M π hR`: the mean reward `r_π` of `π` as an element of
  `boundedMeasurable 𝓢`.
* `Learning.MDP.bellmanEvalOp M γ π hR`: the evaluation operator `v ↦ r_π + γ P_π v` of `π` acting
  on `boundedMeasurable 𝓢`.

## Main statements

* `Learning.MDP.isBlackwell_bellmanOp`, `Learning.MDP.contractingWith_bellmanOp`,
  `Learning.MDP.isBlackwell_bellmanEvalOp`, `Learning.MDP.contractingWith_bellmanEvalOp`: the
  operators satisfy Blackwell's conditions and are `γ`-contractions of `boundedMeasurable 𝓢`;
  `Learning.MDP.coeFn_bellmanEvalOp`: pointwise, the evaluation operator is `M.bellmanEval γ π`.
* `Learning.MDP.abs_bellman_sub_le`, `Learning.MDP.abs_bellmanEval_sub_le`: the contraction
  bounds, stated pointwise for bounded measurable value functions.
* `Learning.MDP.bellmanEvalOp_le_bellmanOp`, `Learning.MDP.bellmanEvalOp_greedy`: the evaluation
  operators of the stationary policies are below the optimality operator, and for finitely many
  actions the greedy policy attains it.
* `Learning.MDP.exists_bellman_eq`, `Learning.MDP.eq_of_bellman_eq`: the optimality equation has a
  unique bounded measurable solution, and it is bounded by `C / (1 - γ)`.
* `Learning.MDP.abs_bellman_iterate_sub_le`: value iteration converges geometrically to it.
* `Learning.MDP.abs_bellman_iterate_succ_sub_le`: the increments of value iteration decay
  geometrically; `Learning.MDP.bellman_iterate_succ_le`: the one-sided form
  `T^[n + 1] v - T^[n] v ≤ γ ^ n * b` when `T v - v ≤ b`.
* `Learning.MDP.antitone_bellman_iterate`, `Learning.MDP.monotone_bellman_iterate`: monotone
  iterates.

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §§6.2–6.3
* [D. Blackwell, *Discounted dynamic programming*, 1965][Bla65]
-/

public section

open MeasureTheory ProbabilityTheory Set Function LMLExplore Learning
open scoped ENNReal NNReal lp

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {u v w : 𝓢 → ℝ} {B B' C D b : ℝ}

/-! ### The optimality operator on bounded measurable functions -/

section Optimality

variable [Countable 𝓐] [Nonempty 𝓐]

variable (M γ) in
/-- The Bellman optimality operator `M.bellman γ`, for countably many actions and rewards bounded
by `C`, as a map of the bounded measurable functions on `𝓢`. -/
noncomputable def bellmanOp (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (v : boundedMeasurable 𝓢) :
    boundedMeasurable 𝓢 :=
  boundedMeasurable.mk (M.bellman γ ⇑(v : ℓ^∞(𝓢, ℝ)))
    (measurable_bellman (boundedMeasurable.measurable v))
    (bddAbove_def.2 ⟨C + γ * ‖v‖,
      forall_mem_range.2 (abs_bellman_le hR (boundedMeasurable.abs_apply_le_norm v))⟩)

variable (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)

@[simp]
lemma coeFn_bellmanOp (v : boundedMeasurable 𝓢) :
    ⇑(M.bellmanOp γ hR v : ℓ^∞(𝓢, ℝ)) = M.bellman γ ⇑(v : ℓ^∞(𝓢, ℝ)) :=
  boundedMeasurable.coeFn_mk ..

/-- The iterates of `M.bellmanOp γ hR` are those of `M.bellman γ`. -/
@[simp]
lemma coeFn_bellmanOp_iterate (n : ℕ) (v : boundedMeasurable 𝓢) :
    ⇑((M.bellmanOp γ hR)^[n] v : ℓ^∞(𝓢, ℝ)) = (M.bellman γ)^[n] ⇑(v : ℓ^∞(𝓢, ℝ)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', coeFn_bellmanOp, ih, iterate_succ_apply']

variable {hR}

/-- A bounded measurable fixed point of `M.bellman γ` is a fixed point of `M.bellmanOp γ hR`. -/
lemma isFixedPt_bellmanOp_mk (hu : Measurable u) (huB : ∀ s, |u s| ≤ B)
    (hu_eq : M.bellman γ u = u) :
    IsFixedPt (M.bellmanOp γ hR)
      (boundedMeasurable.mk u hu (bddAbove_def.2 ⟨B, forall_mem_range.2 huB⟩)) :=
  boundedMeasurable.ext fun s ↦ by rw [coeFn_bellmanOp, boundedMeasurable.coeFn_mk, hu_eq]

variable (hR)

/-- With bounded rewards and countably many actions, the optimality operator satisfies Blackwell's
conditions on the bounded measurable functions, for the constant function `1`. -/
theorem isBlackwell_bellmanOp : IsBlackwell 1 γ (M.bellmanOp γ hR) where
  monotone v w hvw := boundedMeasurable.le_def.2 fun s ↦ by
    simp only [coeFn_bellmanOp]
    exact bellman_mono (fun _ ↦ boundedMeasurable.integrable v _)
      (fun _ ↦ boundedMeasurable.integrable w _)
      (bddAbove_range_lookahead hR (boundedMeasurable.abs_apply_le_norm w))
      (boundedMeasurable.le_def.1 hvw) s
  map_add_smul_le v c _ := le_of_eq <| boundedMeasurable.ext fun s ↦ by
    simp only [coeFn_bellmanOp, boundedMeasurable.coeFn_add, boundedMeasurable.coeFn_smul,
      boundedMeasurable.coeFn_one, Pi.smul_one_eq_const]
    rw [bellman_add_const (fun _ ↦ boundedMeasurable.integrable v _)
      (bddAbove_range_lookahead hR (boundedMeasurable.abs_apply_le_norm v))]

/-- With bounded rewards, countably many actions and `γ < 1`, the optimality operator is a
`γ`-contraction of the bounded measurable functions with the sup norm [P, Proposition 6.2.4]. -/
theorem contractingWith_bellmanOp (hγ : γ < 1) : ContractingWith γ (M.bellmanOp γ hR) :=
  (isBlackwell_bellmanOp hR).contractingWith boundedMeasurable.orderUnitNorm_one_eq_norm hγ

variable {hR}

/-- With bounded rewards and countably many actions, the optimality operator is a `γ`-contraction
for the sup norm, stated pointwise: if bounded measurable `v` and `w` satisfy `|v - w| ≤ D`, then
`|M.bellman γ v - M.bellman γ w| ≤ γ * D`. -/
theorem abs_bellman_sub_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (hw : Measurable w) (hwB : ∀ s, |w s| ≤ B')
    (hD : ∀ s, |v s - w s| ≤ D) (s : 𝓢) :
    |M.bellman γ v s - M.bellman γ w s| ≤ γ * D :=
  boundedMeasurable.abs_sub_apply_le_of_isBlackwell_of_coeFn_eq (isBlackwell_bellmanOp hR)
    (coeFn_bellmanOp hR) hv hvB hw hwB hD s

/-- **The optimality equation has a solution** (the fixed-point part of [P, Theorem 6.2.5 (a)]):
with rewards bounded by `C`, countably many actions and `γ < 1`, there is a measurable `u` bounded
by `C / (1 - γ)` with `M.bellman γ u = u`. It is the only bounded measurable one
(`Learning.MDP.eq_of_bellman_eq`). -/
theorem exists_bellman_eq (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    ∃ u : 𝓢 → ℝ, Measurable u ∧ (∀ s, |u s| ≤ C / (1 - γ)) ∧ M.bellman γ u = u := by
  have hT := contractingWith_bellmanOp (γ := γ) hR hγ
  set U := ContractingWith.fixedPoint _ hT
  refine ⟨U, boundedMeasurable.measurable U, fun s ↦ ?_, ?_⟩
  · -- `‖U‖ = dist 0 U ≤ ‖T 0‖ / (1 - γ)`, and `T 0` is bounded by `C`.
    obtain ⟨a⟩ := ‹Nonempty 𝓐›
    have hC : 0 ≤ C := (abs_nonneg _).trans (abs_meanReward_le hR (s, a))
    have hT0 : ‖M.bellmanOp γ hR 0‖ ≤ C :=
      boundedMeasurable.norm_le_of_forall_le hC fun s ↦ by
        rw [coeFn_bellmanOp]
        exact (abs_bellman_le hR (B := 0) (fun s ↦ by simp) s).trans_eq (by simp)
    calc |⇑(U : ℓ^∞(𝓢, ℝ)) s| ≤ ‖U‖ := boundedMeasurable.abs_apply_le_norm U s
      _ = dist 0 U := by rw [dist_zero_left]
      _ ≤ dist 0 (M.bellmanOp γ hR 0) / (1 - γ) := hT.dist_fixedPoint_le 0
      _ ≤ C / (1 - γ) := by
        rw [dist_zero_left]
        gcongr
        exact sub_nonneg.2 (NNReal.coe_le_one.2 hγ.le)
  · rw [← coeFn_bellmanOp hR]
    exact congrArg (fun f : boundedMeasurable 𝓢 ↦ ⇑(f : ℓ^∞(𝓢, ℝ))) hT.fixedPoint_isFixedPt

/-- **The optimality equation has at most one bounded measurable solution** (the uniqueness part
of [P, Theorem 6.2.5 (a)]): with bounded rewards, countably many actions and `γ < 1`, two bounded
measurable solutions of `M.bellman γ v = v` are equal. -/
theorem eq_of_bellman_eq (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hu : Measurable u)
    (huB : ∀ s, |u s| ≤ B) (hu_eq : M.bellman γ u = u) (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B')
    (hv_eq : M.bellman γ v = v) : u = v := by
  have h := (contractingWith_bellmanOp (γ := γ) hR hγ).fixedPoint_unique'
    (isFixedPt_bellmanOp_mk hu huB hu_eq) (isFixedPt_bellmanOp_mk hv hvB hv_eq)
  have h' := congrArg (fun f : boundedMeasurable 𝓢 ↦ ⇑(f : ℓ^∞(𝓢, ℝ))) h
  simpa only [boundedMeasurable.coeFn_mk] using h'

/-- **Value iteration** [P, Theorem 6.3.3 (d)]: with bounded rewards, countably many actions and
`γ < 1`, the iterates `(M.bellman γ)^[n] v` of a bounded measurable `v` converge to the bounded
measurable solution `u` of the optimality equation at the geometric rate
`|(M.bellman γ)^[n] v - u| ≤ γ ^ n * D / (1 - γ)`, where `D` bounds `|M.bellman γ v - v|`. -/
theorem abs_bellman_iterate_sub_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (hu : Measurable u) (huB : ∀ s, |u s| ≤ B')
    (hu_eq : M.bellman γ u = u) (hD : ∀ s, |M.bellman γ v s - v s| ≤ D) (n : ℕ) (s : 𝓢) :
    |(M.bellman γ)^[n] v s - u s| ≤ γ ^ n * D / (1 - γ) := by
  have hT := contractingWith_bellmanOp (γ := γ) hR hγ
  set V := boundedMeasurable.mk v hv (bddAbove_def.2 ⟨B, forall_mem_range.2 hvB⟩)
  set U := boundedMeasurable.mk u hu (bddAbove_def.2 ⟨B', forall_mem_range.2 huB⟩)
  have hU : U = ContractingWith.fixedPoint _ hT :=
    hT.fixedPoint_unique (isFixedPt_bellmanOp_mk hu huB hu_eq)
  have hVD : dist V (M.bellmanOp γ hR V) ≤ D :=
    boundedMeasurable.dist_le_of_forall_abs_sub_le ((abs_nonneg _).trans (hD s)) fun s ↦ by
      rw [coeFn_bellmanOp, boundedMeasurable.coeFn_mk, abs_sub_comm]
      exact hD s
  calc |(M.bellman γ)^[n] v s - u s|
      = |⇑((M.bellmanOp γ hR)^[n] V : ℓ^∞(𝓢, ℝ)) s - ⇑(U : ℓ^∞(𝓢, ℝ)) s| := by
        rw [coeFn_bellmanOp_iterate, boundedMeasurable.coeFn_mk, boundedMeasurable.coeFn_mk]
    _ ≤ dist ((M.bellmanOp γ hR)^[n] V) U := boundedMeasurable.abs_sub_apply_le_dist _ _ s
    _ ≤ dist V (M.bellmanOp γ hR V) * γ ^ n / (1 - γ) := by
        rw [hU]; exact hT.apriori_dist_iterate_fixedPoint_le V n
    _ ≤ γ ^ n * D / (1 - γ) := by
        rw [mul_comm]
        gcongr
        exact sub_nonneg.2 (NNReal.coe_le_one.2 hγ.le)

/-- **The increments of value iteration decay geometrically**: with countably many actions and
rewards bounded by `C`, if a bounded measurable `v` satisfies `|T v - v| ≤ D`, then
`|T^[n + 1] v - T^[n] v| ≤ γ ^ n * D`. For `γ < 1` and `ε > 0`, the bound `δ = γ ^ n * D` meets
the stopping rule `2 * γ * δ < ε * (1 - γ)` of value iteration for all large `n`, as in
[P, Theorem 6.3.1 (b)]. -/
theorem abs_bellman_iterate_succ_sub_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (hD : ∀ s, |M.bellman γ v s - v s| ≤ D) (n : ℕ) (s : 𝓢) :
    |(M.bellman γ)^[n + 1] v s - (M.bellman γ)^[n] v s| ≤ γ ^ n * D := by
  have hT := (isBlackwell_bellmanOp (γ := γ) hR).lipschitzWith
    boundedMeasurable.orderUnitNorm_one_eq_norm
  set V := boundedMeasurable.mk v hv (bddAbove_def.2 ⟨B, forall_mem_range.2 hvB⟩)
  have hVD : dist V (M.bellmanOp γ hR V) ≤ D :=
    boundedMeasurable.dist_le_of_forall_abs_sub_le ((abs_nonneg _).trans (hD s)) fun s ↦ by
      rw [coeFn_bellmanOp, boundedMeasurable.coeFn_mk, abs_sub_comm]
      exact hD s
  calc |(M.bellman γ)^[n + 1] v s - (M.bellman γ)^[n] v s|
      = |⇑((M.bellmanOp γ hR)^[n] V : ℓ^∞(𝓢, ℝ)) s -
          ⇑((M.bellmanOp γ hR)^[n + 1] V : ℓ^∞(𝓢, ℝ)) s| := by
        rw [coeFn_bellmanOp_iterate, coeFn_bellmanOp_iterate, boundedMeasurable.coeFn_mk,
          abs_sub_comm]
    _ ≤ dist ((M.bellmanOp γ hR)^[n] V) ((M.bellmanOp γ hR)^[n + 1] V) :=
        boundedMeasurable.abs_sub_apply_le_dist _ _ s
    _ ≤ dist V (M.bellmanOp γ hR V) * γ ^ n := hT.dist_iterate_succ_le_geometric V n
    _ ≤ γ ^ n * D := by
        rw [mul_comm]
        gcongr

/-- With countably many actions and bounded rewards, if a bounded measurable `v` satisfies
`T v - v ≤ b`, then the increments of value iteration satisfy
`T^[n + 1] v - T^[n] v ≤ γ ^ n * b`. This is the one-sided companion of
`Learning.MDP.abs_bellman_iterate_succ_sub_le`. -/
theorem bellman_iterate_succ_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (hb : ∀ s, M.bellman γ v s - v s ≤ b) (n : ℕ) (s : 𝓢) :
    (M.bellman γ)^[n + 1] v s ≤ (M.bellman γ)^[n] v s + (γ : ℝ) ^ n * b := by
  choose K hK using exists_abs_bellman_iterate_le (M := M) (γ := γ) hR hvB
  have hint (k : ℕ) (p : 𝓢 × 𝓐) : Integrable ((M.bellman γ)^[k] v) (M.P p) :=
    integrable_of_abs_le (measurable_bellman_iterate hv k) (hK k) _
  induction n generalizing s with
  | zero => simpa using (sub_le_iff_le_add').1 (hb s)
  | succ n ih =>
    calc (M.bellman γ)^[n + 1 + 1] v s = M.bellman γ ((M.bellman γ)^[n + 1] v) s := by
          rw [iterate_succ_apply']
      _ ≤ M.bellman γ ((M.bellman γ)^[n] v + fun _ ↦ (γ : ℝ) ^ n * b) s :=
          bellman_mono (hint (n + 1)) (fun p ↦ (hint n p).add (integrable_const _))
            (bddAbove_range_lookahead hR
              fun s ↦ (abs_add_le _ _).trans (add_le_add (hK n s) le_rfl))
            (fun s ↦ ih s) s
      _ = M.bellman γ ((M.bellman γ)^[n] v) s + γ * ((γ : ℝ) ^ n * b) := by
          rw [bellman_add_const (hint n) (bddAbove_range_lookahead hR (hK n)), Pi.add_apply]
      _ = (M.bellman γ)^[n + 1] v s + (γ : ℝ) ^ (n + 1) * b := by
          rw [iterate_succ_apply']
          ring

/-- **Monotone iterates, decreasing case** ([P, Proposition 6.3.2 (b)]): with countably many
actions and bounded rewards, if a bounded measurable `v` satisfies `T v ≤ v`, then the iterates
`T^[n] v` decrease. Applied to an iterate `v = T^[N] v₀`, the iterates of value iteration decrease
from the first `N` with `T^[N + 1] v₀ ≤ T^[N] v₀`. -/
theorem antitone_bellman_iterate (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (h : M.bellman γ v ≤ v) :
    Antitone fun n ↦ (M.bellman γ)^[n] v := by
  set V := boundedMeasurable.mk v hv (bddAbove_def.2 ⟨B, forall_mem_range.2 hvB⟩)
  have hVv : ⇑(V : ℓ^∞(𝓢, ℝ)) = v := boundedMeasurable.coeFn_mk ..
  have hV : M.bellmanOp γ hR V ≤ V := boundedMeasurable.le_def.2 fun s ↦ by
    simpa only [coeFn_bellmanOp, hVv] using h s
  intro m n hmn s
  simpa only [coeFn_bellmanOp_iterate, hVv] using
    boundedMeasurable.le_def.1
      ((isBlackwell_bellmanOp hR).monotone.antitone_iterate_of_map_le hV hmn) s

/-- **Monotone iterates, increasing case** ([P, Proposition 6.3.2 (b)]): with countably many
actions and bounded rewards, if a bounded measurable `v` satisfies `v ≤ T v`, then the iterates
`T^[n] v` increase. Applied to an iterate `v = T^[N] v₀`, the iterates of value iteration increase
from the first `N` with `T^[N] v₀ ≤ T^[N + 1] v₀`. -/
theorem monotone_bellman_iterate (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (h : v ≤ M.bellman γ v) :
    Monotone fun n ↦ (M.bellman γ)^[n] v := by
  set V := boundedMeasurable.mk v hv (bddAbove_def.2 ⟨B, forall_mem_range.2 hvB⟩)
  have hVv : ⇑(V : ℓ^∞(𝓢, ℝ)) = v := boundedMeasurable.coeFn_mk ..
  have hV : V ≤ M.bellmanOp γ hR V := boundedMeasurable.le_def.2 fun s ↦ by
    simpa only [coeFn_bellmanOp, hVv] using h s
  intro m n hmn s
  simpa only [coeFn_bellmanOp_iterate, hVv] using
    boundedMeasurable.le_def.1
      ((isBlackwell_bellmanOp hR).monotone.monotone_iterate_of_le_map hV hmn) s

end Optimality

/-! ### The evaluation operator on bounded measurable functions -/

section Evaluation

variable {π : Kernel 𝓢 𝓐} [IsMarkovKernel π]

variable (M π) in
/-- The mean reward `r_π` of the stationary policy `π` (`Learning.MDP.policyReward`), for rewards
bounded by `C`, as a bounded measurable function on `𝓢`. -/
noncomputable def policyRewardBM (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) : boundedMeasurable 𝓢 :=
  boundedMeasurable.mk (M.policyReward π) measurable_policyReward
    (bddAbove_def.2 ⟨C, forall_mem_range.2 (abs_policyReward_le hR)⟩)

@[simp]
lemma coeFn_policyRewardBM (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    ⇑(M.policyRewardBM π hR : ℓ^∞(𝓢, ℝ)) = M.policyReward π :=
  boundedMeasurable.coeFn_mk ..

variable (M γ π) in
/-- The evaluation operator of the stationary policy `π`, for rewards bounded by `C`, as the affine
map `v ↦ r_π + γ P_π v` of the bounded measurable functions on `𝓢`, where the state kernel
`P_π = M.stateKernel π` acts by `Kernel.integralCLM`. Pointwise, it is `M.bellmanEval γ π`
(`Learning.MDP.coeFn_bellmanEvalOp`). -/
noncomputable def bellmanEvalOp (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (v : boundedMeasurable 𝓢) :
    boundedMeasurable 𝓢 :=
  M.policyRewardBM π hR + (γ : ℝ) • (M.stateKernel π).integralCLM v

lemma bellmanEvalOp_def (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (v : boundedMeasurable 𝓢) :
    M.bellmanEvalOp γ π hR v = M.policyRewardBM π hR + (γ : ℝ) • (M.stateKernel π).integralCLM v :=
  (rfl)

variable (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)

@[simp]
lemma coeFn_bellmanEvalOp (v : boundedMeasurable 𝓢) :
    ⇑(M.bellmanEvalOp γ π hR v : ℓ^∞(𝓢, ℝ)) = M.bellmanEval γ π ⇑(v : ℓ^∞(𝓢, ℝ)) := by
  ext s
  rw [bellmanEvalOp_def, boundedMeasurable.coeFn_add, Pi.add_apply,
    bellmanEval_eq_policyReward_add hR (boundedMeasurable.measurable v)
      (boundedMeasurable.abs_apply_le_norm v)]
  simp

/-- The iterates of `M.bellmanEvalOp γ π hR` are those of `M.bellmanEval γ π`. -/
@[simp]
lemma coeFn_bellmanEvalOp_iterate (n : ℕ) (v : boundedMeasurable 𝓢) :
    ⇑((M.bellmanEvalOp γ π hR)^[n] v : ℓ^∞(𝓢, ℝ)) = (M.bellmanEval γ π)^[n] ⇑(v : ℓ^∞(𝓢, ℝ)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', coeFn_bellmanEvalOp, ih, iterate_succ_apply']

variable {hR} in
/-- A bounded measurable fixed point of `M.bellmanEval γ π` is a fixed point of
`M.bellmanEvalOp γ π hR`. -/
lemma isFixedPt_bellmanEvalOp_mk (hu : Measurable u) (huB : ∀ s, |u s| ≤ B)
    (hu_eq : M.bellmanEval γ π u = u) :
    IsFixedPt (M.bellmanEvalOp γ π hR)
      (boundedMeasurable.mk u hu (bddAbove_def.2 ⟨B, forall_mem_range.2 huB⟩)) :=
  boundedMeasurable.ext fun s ↦ by rw [coeFn_bellmanEvalOp, boundedMeasurable.coeFn_mk, hu_eq]

/-- With bounded rewards, the evaluation operator of a stationary policy satisfies Blackwell's
conditions on the bounded measurable functions, for the constant function `1`: the action of the
state kernel is monotone and fixes the constants. -/
theorem isBlackwell_bellmanEvalOp : IsBlackwell 1 γ (M.bellmanEvalOp γ π hR) where
  monotone v w hvw := by
    simp only [bellmanEvalOp_def]
    gcongr
    exact Kernel.monotone_integralCLM hvw
  map_add_smul_le v c _ := le_of_eq <| by
    simp only [bellmanEvalOp_def, map_add, map_smul, Kernel.integralCLM_one]
    module

/-- With bounded rewards and `γ < 1`, the evaluation operator of a stationary policy is a
`γ`-contraction of the bounded measurable functions with the sup norm [P, Proposition 6.2.4]. -/
theorem contractingWith_bellmanEvalOp (hγ : γ < 1) : ContractingWith γ (M.bellmanEvalOp γ π hR) :=
  (isBlackwell_bellmanEvalOp hR).contractingWith boundedMeasurable.orderUnitNorm_one_eq_norm hγ

/-- With bounded rewards, the evaluation operator of a stationary policy is a `γ`-contraction for
the sup norm, stated pointwise: if bounded measurable `v` and `w` satisfy `|v - w| ≤ D`, then
`|M.bellmanEval γ π v - M.bellmanEval γ π w| ≤ γ * D`. -/
theorem abs_bellmanEval_sub_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (hw : Measurable w) (hwB : ∀ s, |w s| ≤ B')
    (hD : ∀ s, |v s - w s| ≤ D) (s : 𝓢) :
    |M.bellmanEval γ π v s - M.bellmanEval γ π w s| ≤ γ * D :=
  boundedMeasurable.abs_sub_apply_le_of_isBlackwell_of_coeFn_eq (isBlackwell_bellmanEvalOp hR)
    (coeFn_bellmanEvalOp hR) hv hvB hw hwB hD s

end Evaluation

/-- **Randomizing does not increase the supremum**: for countably many actions and bounded
rewards, the evaluation operator of every stationary policy is below the optimality operator on the
bounded measurable functions. -/
theorem bellmanEvalOp_le_bellmanOp [Countable 𝓐] [Nonempty 𝓐] {π : Kernel 𝓢 𝓐} [IsMarkovKernel π]
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (v : boundedMeasurable 𝓢) :
    M.bellmanEvalOp γ π hR v ≤ M.bellmanOp γ hR v :=
  boundedMeasurable.le_def.2 fun s ↦ by
    simpa using bellmanEval_le_bellman (M := M) (γ := γ) (π := π)
      (fun s ↦ integrable_lookahead_prodMk_left hR (boundedMeasurable.measurable v)
        (boundedMeasurable.abs_apply_le_norm v) s _)
      (bddAbove_range_lookahead hR (boundedMeasurable.abs_apply_le_norm v)) s

/-- For finitely many actions and bounded rewards, the greedy policy for a bounded measurable `v`
attains the optimality operator at `v`. -/
@[simp]
theorem bellmanEvalOp_greedy [Fintype 𝓐] [Nonempty 𝓐] (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (v : boundedMeasurable 𝓢) :
    M.bellmanEvalOp γ (Kernel.deterministic (M.greedy γ ⇑(v : ℓ^∞(𝓢, ℝ)))
      (measurable_greedy (boundedMeasurable.measurable v))) hR v = M.bellmanOp γ hR v :=
  boundedMeasurable.ext fun s ↦ by simp [boundedMeasurable.measurable v]

end Learning.MDP
