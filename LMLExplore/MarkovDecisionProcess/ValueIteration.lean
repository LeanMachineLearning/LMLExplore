/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.FixedPoint.DynamicProgramming
public import LMLExplore.MarkovDecisionProcess.Bellman

/-!
# Bellman operators on bounded measurable functions and value iteration

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP on a measurable state space `𝓢`, with rewards bounded by `C`, and
let `0 ≤ γ < 1`. The Bellman optimality operator `M.bellman γ`, for countably many actions, and the
evaluation operator `M.bellmanEval γ π` of a stationary policy `π` map bounded measurable functions
to bounded measurable functions. They therefore act on the Banach space
`LMLExplore.boundedMeasurable 𝓢` of bounded measurable functions with the sup norm, as
`M.bellmanOp γ hR` and `M.bellmanEvalOp γ π hR`.

On that space they satisfy Blackwell's conditions for the constant function `1`, whose order-unit
norm is the sup norm, so they are `γ`-contractions [P, Proposition 6.2.4] and Banach's fixed point
theorem applies. This gives, on a general measurable state space,
* a unique bounded measurable solution of the optimality equation `M.bellman γ u = u`, bounded by
  `C / (1 - γ)` (the fixed-point part of [P, Theorem 6.2.5 (a)], where `𝓢` is countable);
* the convergence of value iteration `v, T v, T² v, …` to it at the geometric rate
  `|Tⁿ v - u| ≤ γ ^ n * ‖T v - v‖ / (1 - γ)` [P, Theorem 6.3.3 (d)].

For finitely many actions, the optimality operator at `v` is the greatest value at `v` of the
evaluation operators of the measurable deterministic stationary policies. Together with Blackwell's
conditions, this makes the operators an instance of the abstract dynamic programming of
`LMLExplore.IsPolicyIteration` and `LMLExplore.IsModifiedPolicyIteration`, with
`boundedMeasurable 𝓢` as space of values.

## Main definitions

* `Learning.MDP.bellmanOp M γ hR`: the optimality operator acting on `boundedMeasurable 𝓢`.
* `Learning.MDP.bellmanEvalOp M γ π hR`: the evaluation operator of `π` acting on
  `boundedMeasurable 𝓢`.

## Main statements

* `Learning.MDP.isBlackwell_bellmanOp`, `Learning.MDP.contractingWith_bellmanOp`,
  `Learning.MDP.isBlackwell_bellmanEvalOp`, `Learning.MDP.contractingWith_bellmanEvalOp`: the
  operators satisfy Blackwell's conditions and are `γ`-contractions of `boundedMeasurable 𝓢`.
* `Learning.MDP.isGreatest_bellmanEvalOp`: for finitely many actions, the optimality operator is
  the maximum of the evaluation operators of measurable deterministic stationary policies.
* `Learning.MDP.exists_bellman_eq`, `Learning.MDP.eq_of_bellman_eq`: the optimality equation has a
  unique bounded measurable solution, and it is bounded by `C / (1 - γ)`.
* `Learning.MDP.abs_bellman_iterate_sub_le`: value iteration converges geometrically to it.

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §§6.2–6.3
* [D. Blackwell, *Discounted dynamic programming*, 1965][Bla65]
-/

public section

open MeasureTheory ProbabilityTheory Set Function LMLExplore Learning
open scoped ENNReal NNReal lp

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {u v : 𝓢 → ℝ} {B B' C D : ℝ}

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
    simp only [coeFn_bellmanOp, bellman_def]
    exact ciSup_mono (bddAbove_range_lookahead hR (boundedMeasurable.abs_apply_le_norm w) s)
      fun a ↦ lookahead_mono (boundedMeasurable.integrable v _)
        (boundedMeasurable.integrable w _) (boundedMeasurable.le_def.1 hvw)
  map_add_smul_le v c _ := le_of_eq <| boundedMeasurable.ext fun s ↦ by
    rw [coeFn_bellmanOp, boundedMeasurable.coeFn_add, boundedMeasurable.coeFn_smul_one,
      boundedMeasurable.coeFn_add, boundedMeasurable.coeFn_smul_one, coeFn_bellmanOp,
      Pi.add_apply, bellman_def, bellman_def]
    simp only [lookahead_add_const (boundedMeasurable.integrable v _)]
    exact ((OrderIso.addRight ((γ : ℝ) * c)).map_ciSup
      (bddAbove_range_lookahead hR (boundedMeasurable.abs_apply_le_norm v) s)).symm

/-- With bounded rewards, countably many actions and `γ < 1`, the optimality operator is a
`γ`-contraction of the bounded measurable functions with the sup norm [P, Proposition 6.2.4]. -/
theorem contractingWith_bellmanOp (hγ : γ < 1) : ContractingWith γ (M.bellmanOp γ hR) :=
  (isBlackwell_bellmanOp hR).contractingWith boundedMeasurable.orderUnitNorm_one_eq_norm hγ

variable {hR}

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
  have hVD : dist V (M.bellmanOp γ hR V) ≤ D := by
    rw [dist_eq_norm]
    refine boundedMeasurable.norm_le_of_forall_le ((abs_nonneg _).trans (hD s)) fun s ↦ ?_
    rw [boundedMeasurable.coeFn_sub, coeFn_bellmanOp, boundedMeasurable.coeFn_mk, Pi.sub_apply,
      abs_sub_comm]
    exact hD s
  calc |(M.bellman γ)^[n] v s - u s|
      = |⇑(((M.bellmanOp γ hR)^[n] V - U : boundedMeasurable 𝓢) : ℓ^∞(𝓢, ℝ)) s| := by
        rw [boundedMeasurable.coeFn_sub, Pi.sub_apply, coeFn_bellmanOp_iterate,
          boundedMeasurable.coeFn_mk, boundedMeasurable.coeFn_mk]
    _ ≤ dist ((M.bellmanOp γ hR)^[n] V) U := by
        rw [dist_eq_norm]; exact boundedMeasurable.abs_apply_le_norm _ s
    _ ≤ dist V (M.bellmanOp γ hR V) * γ ^ n / (1 - γ) := by
        rw [hU]; exact hT.apriori_dist_iterate_fixedPoint_le V n
    _ ≤ γ ^ n * D / (1 - γ) := by
        rw [mul_comm]
        gcongr
        exact sub_nonneg.2 (NNReal.coe_le_one.2 hγ.le)

end Optimality

/-! ### The evaluation operator on bounded measurable functions -/

section Evaluation

variable {π : Kernel 𝓢 𝓐} [IsMarkovKernel π]

variable (M γ π) in
/-- The evaluation operator `M.bellmanEval γ π` of the stationary policy `π`, for rewards bounded
by `C`, as a map of the bounded measurable functions on `𝓢`. -/
noncomputable def bellmanEvalOp (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (v : boundedMeasurable 𝓢) :
    boundedMeasurable 𝓢 :=
  boundedMeasurable.mk (M.bellmanEval γ π ⇑(v : ℓ^∞(𝓢, ℝ)))
    (measurable_bellmanEval (boundedMeasurable.measurable v))
    (bddAbove_def.2 ⟨C + γ * ‖v‖,
      forall_mem_range.2 (abs_bellmanEval_le hR (boundedMeasurable.abs_apply_le_norm v))⟩)

variable (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)

@[simp]
lemma coeFn_bellmanEvalOp (v : boundedMeasurable 𝓢) :
    ⇑(M.bellmanEvalOp γ π hR v : ℓ^∞(𝓢, ℝ)) = M.bellmanEval γ π ⇑(v : ℓ^∞(𝓢, ℝ)) :=
  boundedMeasurable.coeFn_mk ..

/-- With bounded rewards, the evaluation operator of a stationary policy satisfies Blackwell's
conditions on the bounded measurable functions, for the constant function `1`. -/
theorem isBlackwell_bellmanEvalOp : IsBlackwell 1 γ (M.bellmanEvalOp γ π hR) where
  monotone v w hvw := boundedMeasurable.le_def.2 fun s ↦ by
    simp only [coeFn_bellmanEvalOp]
    exact bellmanEval_mono hR (boundedMeasurable.measurable v)
      (boundedMeasurable.abs_apply_le_norm v) (boundedMeasurable.measurable w)
      (boundedMeasurable.abs_apply_le_norm w) (boundedMeasurable.le_def.1 hvw) s
  map_add_smul_le v c _ := le_of_eq <| boundedMeasurable.ext fun s ↦ by
    rw [coeFn_bellmanEvalOp, boundedMeasurable.coeFn_add, boundedMeasurable.coeFn_smul_one,
      boundedMeasurable.coeFn_add, boundedMeasurable.coeFn_smul_one, coeFn_bellmanEvalOp,
      bellmanEval_add_const hR (boundedMeasurable.measurable v)
        (boundedMeasurable.abs_apply_le_norm v)]

/-- With bounded rewards and `γ < 1`, the evaluation operator of a stationary policy is a
`γ`-contraction of the bounded measurable functions with the sup norm [P, Proposition 6.2.4]. -/
theorem contractingWith_bellmanEvalOp (hγ : γ < 1) : ContractingWith γ (M.bellmanEvalOp γ π hR) :=
  (isBlackwell_bellmanEvalOp hR).contractingWith boundedMeasurable.orderUnitNorm_one_eq_norm hγ

end Evaluation

/-- For finitely many actions and bounded rewards, the optimality operator at a bounded measurable
`v` is the greatest value at `v` of the evaluation operators of the measurable deterministic
stationary policies. -/
theorem isGreatest_bellmanEvalOp [Finite 𝓐] [Nonempty 𝓐] [MeasurableSingletonClass 𝓐]
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (v : boundedMeasurable 𝓢) :
    IsGreatest (range fun d : {d : 𝓢 → 𝓐 // Measurable d} ↦
      M.bellmanEvalOp γ (Kernel.deterministic d d.2) hR v) (M.bellmanOp γ hR v) := by
  obtain ⟨⟨d, hd⟩, h⟩ :=
    (isGreatest_bellmanEval (M := M) (γ := γ) (boundedMeasurable.measurable v)).1
  exact ⟨⟨⟨d, hd⟩, boundedMeasurable.ext fun s ↦ by simpa using congrFun h s⟩,
    forall_mem_range.2 fun d ↦ boundedMeasurable.le_def.2 fun s ↦ by
      simpa using bellmanEval_le_bellman (M := M) (γ := γ) (π := Kernel.deterministic d d.2) _ s⟩

end Learning.MDP
