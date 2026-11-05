/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LMLExplore.Analysis.FixedPoint.OrderUnit
public import LMLExplore.MarkovDecisionProcess.Basic
public import LMLExplore.MeasureTheory.Integral.BoundedMeasurable
public import LMLExplore.Order.ConditionallyCompleteLattice.Group
public import Mathlib.Probability.Kernel.Integral
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Bellman operators of a discounted Markov decision process

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP with mean reward `r = meanReward M.R` and transition kernel `P`, and
let `γ ≥ 0` be a discount factor. For a value function `v : 𝓢 → ℝ`, the *one-step lookahead*
`M.lookahead γ v (s, a) = r (s, a) + γ * ∫ v dP (s, a)` is the expected discounted return of playing
`a` in `s` and then collecting `v` at the next state. From it we define
* the evaluation operator `M.bellmanEval γ π` of a stationary policy `π : Kernel 𝓢 𝓐`, which
  averages the lookahead over the actions of `π`: `v ↦ r_π + γ P_π v`;
* the optimality operator `M.bellman γ`, which maximizes it over the actions:
  `M.bellman γ v s = ⨆ a, M.lookahead γ v (s, a)`;
* the greedy policy `M.greedy γ v`, which picks at every state an action attaining that maximum
  (for finitely many actions), and the predicate `M.IsApproxGreedy γ ε v d` that the deterministic
  policy `d` comes within `ε` of the maximum at every state.

These operators are monotone and adding a constant `c` to their argument adds `γ * c` to their
value. As in Blackwell's sufficient conditions, they are therefore `γ`-contractions for the sup
norm, and they preserve bounded measurable functions. The optimality operator is the pointwise
maximum of the evaluation operators of the measurable deterministic stationary policies, attained
by the greedy policy, and no randomized policy does better. These are the hypotheses of the
abstract dynamic programming of `LMLExplore.IsPolicyIteration` and
`LMLExplore.IsModifiedPolicyIteration`, with the deterministic stationary policies as decisions.

Value functions are functions `𝓢 → ℝ` and the statements are pointwise, with integrability or
boundedness hypotheses where an integral is involved. On a finite state space, where every function
is bounded and measurable, the operators satisfy `LMLExplore.IsBlackwell` for the unit `1`, hence
are `γ`-Lipschitz for the sup norm of `𝓢 → ℝ`.

The optimality operator is defined for every action space, as a supremum in `ℝ`; it is meaningful
when the lookahead is bounded above in the action. The statements about it assume that bound,
together with integrability over the actions where they average the lookahead. Finitely many
actions give both, and so do bounded rewards and a bounded measurable value function
(`Learning.MDP.bddAbove_range_lookahead`, `Learning.MDP.integrable_lookahead_prodMk_left`).

## Main definitions

* `Learning.MDP.lookahead M γ v`: the one-step lookahead `(s, a) ↦ r (s, a) + γ * ∫ v dP (s, a)`.
* `Learning.MDP.bellmanEval M γ π`: the evaluation operator of the stationary policy `π`.
* `Learning.MDP.bellman M γ`: the Bellman optimality operator.
* `Learning.MDP.greedy M γ v`: the greedy deterministic policy for `v`.
* `Learning.MDP.IsApproxGreedy M γ ε v d`: the deterministic policy `d` is `ε`-greedy for `v`;
  greedy for `ε = 0`.

## Main statements

* `Learning.MDP.bellman_sub_add_le_bellman_sub`: the support inequality: `u ↦ T u - u` lies
  above its affine minorant at `v` given by a greedy action [P, Proposition 6.4.3].
* `Learning.MDP.bellman_mono`, `Learning.MDP.bellman_add_const`,
  `Learning.MDP.bellmanEval_mono`, `Learning.MDP.bellmanEval_add_const`: monotonicity and
  `T (v + c) = T v + γ * c`.
* `Learning.MDP.const_le_bellman_const`: if `c` bounds the mean rewards from below, the constant
  `c / (1 - γ)` is below its image by `T` [P, (6.5.8)].
* `Learning.MDP.abs_bellman_sub_le`, `Learning.MDP.abs_bellmanEval_sub_le`: the operators are
  `γ`-contractions for the sup norm, stated pointwise.
* `Learning.MDP.measurable_bellman`, `Learning.MDP.abs_bellman_le`,
  `Learning.MDP.measurable_bellmanEval`, `Learning.MDP.abs_bellmanEval_le`: the operators preserve
  bounded measurable functions, and so do their iterates (`Learning.MDP.measurable_bellman_iterate`,
  `Learning.MDP.exists_abs_bellman_iterate_le`, `Learning.MDP.measurable_bellmanEval_iterate`,
  `Learning.MDP.exists_abs_bellmanEval_iterate_le`); `Learning.MDP.measurable_greedy`: the greedy
  policy of a measurable function is measurable.
* `Learning.MDP.bellmanEval_le_bellman`: randomizing does not increase the supremum
  [P, Proposition 6.2.1]; `Learning.MDP.bellmanEval_greedy`: the greedy policy attains it, so the
  optimality operator is the maximum of the evaluation operators of measurable deterministic
  stationary policies; `Learning.MDP.isApproxGreedy_iff_bellman_sub_le_bellmanEval`,
  `Learning.MDP.isApproxGreedy_zero_iff_bellmanEval_eq`: a measurable deterministic policy is
  `ε`-greedy for `v` exactly when its evaluation operator at `v` is at least the optimality
  operator minus `ε`, and, for a lookahead bounded above, greedy exactly when it attains it.
* `Learning.MDP.isBlackwell_bellman`, `Learning.MDP.contractingWith_bellman`,
  `Learning.MDP.isBlackwell_bellmanEval`, `Learning.MDP.contractingWith_bellmanEval`: on a finite
  state space, the operators satisfy Blackwell's conditions and are `γ`-contractions of `𝓢 → ℝ`
  with the sup norm.

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §§6.1–6.2, Proposition 6.4.3, (6.5.8)
* [D. Blackwell, *Discounted dynamic programming*, 1965][Bla65]
-/

public section

open MeasureTheory ProbabilityTheory Set LMLExplore Learning
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  (M : MDP 𝓢 𝓐 ℝ) (γ : ℝ≥0) {v w : 𝓢 → ℝ} {B B' C D : ℝ}

/-! ### The one-step lookahead -/

/-- The one-step lookahead `r (s, a) + γ * ∫ v dP (s, a)` of a value function `v`: the expected
discounted return of playing `a` in state `s`, then collecting `v` at the next state. -/
noncomputable def lookahead (v : 𝓢 → ℝ) (p : 𝓢 × 𝓐) : ℝ :=
  meanReward M.R p + γ * ∫ s', v s' ∂(M.P p)

lemma lookahead_def (v : 𝓢 → ℝ) (p : 𝓢 × 𝓐) :
    M.lookahead γ v p = meanReward M.R p + γ * ∫ s', v s' ∂(M.P p) :=
  (rfl)

variable {M γ}

lemma lookahead_mono {p : 𝓢 × 𝓐} (hv : Integrable v (M.P p)) (hw : Integrable w (M.P p))
    (hvw : v ≤ w) : M.lookahead γ v p ≤ M.lookahead γ w p := by
  have := integral_mono hv hw hvw
  rw [lookahead_def, lookahead_def]
  gcongr

lemma lookahead_add_const {p : 𝓢 × 𝓐} (hv : Integrable v (M.P p)) (c : ℝ) :
    M.lookahead γ (v + fun _ ↦ c) p = M.lookahead γ v p + γ * c := by
  simp only [lookahead_def, Pi.add_apply]
  rw [integral_add hv (integrable_const c)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

lemma measurable_lookahead (hv : Measurable v) : Measurable (M.lookahead γ v) :=
  (measurable_meanReward M.R).add <| measurable_const.mul
    (hv.stronglyMeasurable.integral_kernel (κ := M.P)).measurable

/-- Real rewards bounded by `C` have a mean bounded by `C`. -/
lemma abs_meanReward_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (p : 𝓢 × 𝓐) :
    |meanReward M.R p| ≤ C := by
  simpa only [Real.norm_eq_abs] using norm_meanReward_le M.R (hR p)

/-- With rewards bounded by `C` and `|v| ≤ B`, the lookahead is bounded by `C + γ * B`. -/
lemma abs_lookahead_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hvB : ∀ s, |v s| ≤ B)
    (p : 𝓢 × 𝓐) : |M.lookahead γ v p| ≤ C + γ * B := by
  rw [lookahead_def]
  refine (abs_add_le _ _).trans (add_le_add (abs_meanReward_le hR p) ?_)
  rw [abs_mul, NNReal.abs_eq]
  exact mul_le_mul_of_nonneg_left (abs_integral_le_of_abs_le hvB) γ.coe_nonneg

/-- With rewards bounded by `C` and `|v| ≤ B`, the lookahead at a state is bounded above in the
action, so that its supremum over the actions is meaningful. -/
lemma bddAbove_range_lookahead (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hvB : ∀ s, |v s| ≤ B)
    (s : 𝓢) : BddAbove (range fun a ↦ M.lookahead γ v (s, a)) :=
  ⟨C + γ * B, forall_mem_range.2 fun a ↦ (abs_le.1 (abs_lookahead_le hR hvB (s, a))).2⟩

/-- With bounded rewards, the lookahead of a bounded measurable function is integrable over the
actions, for every finite measure on them. -/
lemma integrable_lookahead_prodMk_left (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (s : 𝓢) (ν : Measure 𝓐) [IsFiniteMeasure ν] :
    Integrable (fun a ↦ M.lookahead γ v (s, a)) ν :=
  integrable_of_abs_le ((measurable_lookahead hv).comp measurable_prodMk_left)
    (fun a ↦ abs_lookahead_le hR hvB (s, a)) ν

/-- With bounded rewards, the Bellman residual `r (s, a) + γ * ∫ v dP (s, a) - v s` of a bounded
measurable function is integrable for every finite measure on the state-action pairs. -/
lemma integrable_lookahead_sub (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (ν : Measure (𝓢 × 𝓐)) [IsFiniteMeasure ν] :
    Integrable (fun p ↦ M.lookahead γ v p - v p.1) ν :=
  integrable_of_abs_le ((measurable_lookahead hv).sub (hv.comp measurable_fst))
    (fun p ↦ (abs_sub _ _).trans (add_le_add (abs_lookahead_le hR hvB p) (hvB _))) ν

/-! ### The optimality operator -/

variable (M γ) in
/-- The Bellman optimality operator `v ↦ (s ↦ ⨆ a, r (s, a) + γ * ∫ v dP (s, a))`. -/
noncomputable def bellman (v : 𝓢 → ℝ) (s : 𝓢) : ℝ := ⨆ a, M.lookahead γ v (s, a)

variable (M γ) in
lemma bellman_def (v : 𝓢 → ℝ) (s : 𝓢) : M.bellman γ v s = ⨆ a, M.lookahead γ v (s, a) :=
  (rfl)

/-- The lookahead at every action is below the optimality operator, when the lookahead is bounded
above in the action: for instance for finitely many actions (`Finite.bddAbove_range`), or for
bounded rewards and a bounded function (`Learning.MDP.bddAbove_range_lookahead`). -/
lemma lookahead_le_bellman {s : 𝓢} (hv : BddAbove (range fun a ↦ M.lookahead γ v (s, a)))
    (a : 𝓐) : M.lookahead γ v (s, a) ≤ M.bellman γ v s := by
  rw [bellman_def]
  exact le_ciSup hv a

/-- The optimality operator at `s` is at most `c` if and only if the lookahead at every action is,
when the lookahead is bounded above in the action. -/
lemma bellman_le_iff [Nonempty 𝓐] {s : 𝓢} {c : ℝ}
    (hv : BddAbove (range fun a ↦ M.lookahead γ v (s, a))) :
    M.bellman γ v s ≤ c ↔ ∀ a, M.lookahead γ v (s, a) ≤ c := by
  rw [bellman_def]
  exact ciSup_le_iff hv

/-- **Support inequality** [P, Proposition 6.4.3]: if the action `a` is greedy for `v` at the
state `s`, then `T u s - u s ≥ T v s - v s + (γ P_a (u - v) s - (u s - v s))`, where `T` is the
Bellman optimality operator and `P_a (u - v) s = ∫ (u - v) dP (s, a)`. In other words,
`u ↦ T u - u` lies above the affine map `u ↦ T v - v + (γ P_d - I) (u - v)` for a policy `d` greedy
for `v`, which is tangent to it at `v`. The lookahead of `u` is assumed bounded above in the action
at `s`, as it is for finitely many actions. -/
theorem bellman_sub_add_le_bellman_sub {u : 𝓢 → ℝ} {s : 𝓢} {a : 𝓐}
    (hu : Integrable u (M.P (s, a))) (hv : Integrable v (M.P (s, a)))
    (hu_bdd : BddAbove (range fun a ↦ M.lookahead γ u (s, a)))
    (ha : M.lookahead γ v (s, a) = M.bellman γ v s) :
    M.bellman γ v s - v s + ((γ : ℝ) * ∫ s', (u s' - v s') ∂(M.P (s, a)) - (u s - v s)) ≤
      M.bellman γ u s - u s := by
  have hle := lookahead_le_bellman hu_bdd a
  rw [lookahead_def] at hle ha
  rw [integral_sub hu hv, ← ha]
  linarith

/-- The optimality operator is monotone, when the lookahead of the larger function is bounded
above in the action at every state: for instance for finitely many actions
(`Finite.bddAbove_range`), or for bounded rewards and a bounded function
(`Learning.MDP.bddAbove_range_lookahead`). -/
theorem bellman_mono (hv : ∀ p, Integrable v (M.P p)) (hw : ∀ p, Integrable w (M.P p))
    (hw_bdd : ∀ s, BddAbove (range fun a ↦ M.lookahead γ w (s, a))) (hvw : v ≤ w) :
    M.bellman γ v ≤ M.bellman γ w := fun s ↦ by
  rw [bellman_def, bellman_def]
  exact ciSup_mono (hw_bdd s) fun _ ↦ lookahead_mono (hv _) (hw _) hvw

/-- Adding a constant `c` to the argument of the optimality operator adds `γ * c` to its value,
when the lookahead is bounded above in the action at every state: for instance for finitely many
actions (`Finite.bddAbove_range`), or for bounded rewards and a bounded function
(`Learning.MDP.bddAbove_range_lookahead`). -/
theorem bellman_add_const [Nonempty 𝓐] (hv : ∀ p, Integrable v (M.P p))
    (hv_bdd : ∀ s, BddAbove (range fun a ↦ M.lookahead γ v (s, a))) (c : ℝ) :
    M.bellman γ (v + fun _ ↦ c) = M.bellman γ v + fun _ ↦ γ * c := by
  ext s
  simp only [bellman_def, Pi.add_apply, lookahead_add_const (hv _)]
  exact ((OrderIso.addRight ((γ : ℝ) * c)).map_ciSup (hv_bdd s)).symm

/-- **A starting point for modified policy iteration** [P, (6.5.8)]: for `γ < 1`, if `c` bounds the
mean rewards from below, then the constant function `c / (1 - γ)` is below its image by the
optimality operator. The lookahead of that constant is assumed bounded above in the action, as it
is for finitely many actions or bounded rewards. -/
theorem const_le_bellman_const [Nonempty 𝓐] {c : ℝ} (hγ : γ < 1)
    (hc : ∀ p, c ≤ meanReward M.R p)
    (hbdd : ∀ s, BddAbove (range fun a ↦ M.lookahead γ (fun _ ↦ c / (1 - γ)) (s, a))) :
    (fun _ ↦ c / (1 - γ)) ≤ M.bellman γ (fun _ : 𝓢 ↦ c / (1 - γ)) := fun s ↦ by
  obtain ⟨a⟩ := ‹Nonempty 𝓐›
  refine le_trans ?_ (lookahead_le_bellman (hbdd s) a)
  -- `c / (1 - γ) = c + γ * (c / (1 - γ))`, and `c ≤ r (s, a)`
  have h1γ : (1 - γ : ℝ) ≠ 0 := (sub_pos.2 (NNReal.coe_lt_one.2 hγ)).ne'
  have hfix : c / (1 - γ) = c + γ * (c / (1 - γ)) := by
    field_simp
    ring
  rw [lookahead_def, integral_const, probReal_univ, one_smul]
  linarith [hc (s, a)]

/-- The optimality operator is a `γ`-contraction for the sup norm: if `|v - w| ≤ D` then
`|M.bellman γ v - M.bellman γ w| ≤ γ * D`. -/
theorem abs_bellman_sub_le [Finite 𝓐] [Nonempty 𝓐] (hv : ∀ p, Integrable v (M.P p))
    (hw : ∀ p, Integrable w (M.P p)) (hD : ∀ s, |v s - w s| ≤ D) (s : 𝓢) :
    |M.bellman γ v s - M.bellman γ w s| ≤ γ * D :=
  abs_sub_le_of_monotone_of_add_const hD
    (bellman_mono hv (fun p ↦ (hw p).add (integrable_const D)) fun _ ↦ Finite.bddAbove_range _)
    (bellman_mono hw (fun p ↦ (hv p).add (integrable_const D)) fun _ ↦ Finite.bddAbove_range _)
    (bellman_add_const hv (fun _ ↦ Finite.bddAbove_range _) D)
    (bellman_add_const hw (fun _ ↦ Finite.bddAbove_range _) D) s

/-- The optimality operator maps measurable functions to measurable functions, for countably many
actions. -/
theorem measurable_bellman [Countable 𝓐] (hv : Measurable v) : Measurable (M.bellman γ v) :=
  Measurable.iSup fun _ ↦ (measurable_lookahead hv).comp measurable_prodMk_right

/-- With rewards bounded by `C` and `|v| ≤ B`, the optimality operator is bounded by
`C + γ * B`. -/
theorem abs_bellman_le [Nonempty 𝓐] (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hvB : ∀ s, |v s| ≤ B)
    (s : 𝓢) : |M.bellman γ v s| ≤ C + γ * B := by
  rw [bellman_def]
  exact abs_ciSup_le fun a ↦ abs_lookahead_le hR hvB (s, a)

/-- The iterates of the optimality operator at a measurable `v` are measurable, for countably many
actions. -/
theorem measurable_bellman_iterate [Countable 𝓐] (hv : Measurable v) (n : ℕ) :
    Measurable ((M.bellman γ)^[n] v) := by
  induction n with
  | zero => exact hv
  | succ n ih => rw [Function.iterate_succ_apply']; exact measurable_bellman ih

/-- With bounded rewards, the iterates of the optimality operator at a bounded `v` are bounded. -/
theorem exists_abs_bellman_iterate_le [Nonempty 𝓐] (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hvB : ∀ s, |v s| ≤ B) (n : ℕ) : ∃ B', ∀ s, |(M.bellman γ)^[n] v s| ≤ B' := by
  induction n with
  | zero => exact ⟨B, hvB⟩
  | succ n ih =>
    obtain ⟨B', hB'⟩ := ih
    exact ⟨C + γ * B', fun s ↦ by
      rw [Function.iterate_succ_apply']; exact abs_bellman_le hR hB' s⟩

/-! ### The greedy policy -/

variable (M γ) in
/-- The greedy deterministic policy for `v`: at every state, an action maximizing the lookahead
`r (s, a) + γ * ∫ v dP (s, a)`, chosen by LML's `argmax`. -/
noncomputable def greedy [Fintype 𝓐] [Nonempty 𝓐] (v : 𝓢 → ℝ) (s : 𝓢) : 𝓐 :=
  argmax fun a ↦ M.lookahead γ v (s, a)

variable (M γ) in
lemma greedy_def [Fintype 𝓐] [Nonempty 𝓐] (v : 𝓢 → ℝ) (s : 𝓢) :
    M.greedy γ v s = argmax fun a ↦ M.lookahead γ v (s, a) :=
  (rfl)

/-- The greedy action attains the maximum in the optimality operator. -/
@[simp]
theorem lookahead_greedy [Fintype 𝓐] [Nonempty 𝓐] (v : 𝓢 → ℝ) (s : 𝓢) :
    M.lookahead γ v (s, M.greedy γ v s) = M.bellman γ v s :=
  le_antisymm (lookahead_le_bellman (Finite.bddAbove_range _) _)
    ((bellman_le_iff (Finite.bddAbove_range _)).2 fun a ↦ by
      rw [greedy_def]; exact isMaxOn_argmax (fun a ↦ M.lookahead γ v (s, a)) (Set.mem_univ a))

variable (M γ) in
/-- The deterministic policy `d` is *`ε`-greedy* for `v`: at every state `s`, the lookahead
`r (s, d s) + γ * ∫ v dP (s, d s)` at the action `d s` is at least `M.bellman γ v s - ε`. A policy
is *greedy* for `v` when it is `0`-greedy: when the lookahead is bounded above in the action, the
action `d s` then attains the supremum `M.bellman γ v s`
(`Learning.MDP.isApproxGreedy_zero_iff`). -/
def IsApproxGreedy (ε : ℝ) (v : 𝓢 → ℝ) (d : 𝓢 → 𝓐) : Prop :=
  ∀ s, M.bellman γ v s - ε ≤ M.lookahead γ v (s, d s)

variable (M γ) in
lemma isApproxGreedy_def (ε : ℝ) (v : 𝓢 → ℝ) (d : 𝓢 → 𝓐) :
    M.IsApproxGreedy γ ε v d ↔ ∀ s, M.bellman γ v s - ε ≤ M.lookahead γ v (s, d s) :=
  (Iff.rfl)

/-- An `ε`-greedy policy is `ε'`-greedy for every `ε' ≥ ε`. -/
lemma IsApproxGreedy.mono {ε ε' : ℝ} {d : 𝓢 → 𝓐} (h : M.IsApproxGreedy γ ε v d) (hε : ε ≤ ε') :
    M.IsApproxGreedy γ ε' v d :=
  fun s ↦ (sub_le_sub_left hε _).trans (h s)

/-- When the lookahead is bounded above in the action, a deterministic policy is greedy for `v`
if and only if its actions attain the optimality operator at `v`. -/
theorem isApproxGreedy_zero_iff {d : 𝓢 → 𝓐}
    (hv : ∀ s, BddAbove (range fun a ↦ M.lookahead γ v (s, a))) :
    M.IsApproxGreedy γ 0 v d ↔ ∀ s, M.lookahead γ v (s, d s) = M.bellman γ v s := by
  simp only [isApproxGreedy_def, sub_zero]
  exact forall_congr' fun s ↦ ⟨fun h ↦ le_antisymm (lookahead_le_bellman (hv s) _) h, ge_of_eq⟩

/-- The greedy policy `M.greedy γ v` is greedy for `v`. -/
theorem isApproxGreedy_greedy [Fintype 𝓐] [Nonempty 𝓐] (v : 𝓢 → ℝ) :
    M.IsApproxGreedy γ 0 v (M.greedy γ v) :=
  fun s ↦ by rw [lookahead_greedy, sub_zero]

/-- The greedy policy of a measurable function is measurable. -/
theorem measurable_greedy [Fintype 𝓐] [Nonempty 𝓐] (hv : Measurable v) :
    Measurable (M.greedy γ v) :=
  measurable_argmax.comp <| measurable_pi_iff.2 fun _ ↦
    (measurable_lookahead hv).comp measurable_prodMk_right

/-! ### The evaluation operator of a stationary policy -/

variable (M γ) in
/-- The evaluation operator `v ↦ r_π + γ P_π v` of the stationary policy `π`, which averages the
lookahead over the actions of `π`: `s ↦ ∫ a, r (s, a) + γ * ∫ v dP (s, a) ∂(π s)`. -/
noncomputable def bellmanEval (π : Kernel 𝓢 𝓐) (v : 𝓢 → ℝ) (s : 𝓢) : ℝ :=
  ∫ a, M.lookahead γ v (s, a) ∂(π s)

variable (M γ) in
lemma bellmanEval_def (π : Kernel 𝓢 𝓐) (v : 𝓢 → ℝ) (s : 𝓢) :
    M.bellmanEval γ π v s = ∫ a, M.lookahead γ v (s, a) ∂(π s) :=
  (rfl)

variable {π : Kernel 𝓢 𝓐}

/-- The evaluation operator of a deterministic stationary policy `d` is the lookahead at the action
`d s`. -/
@[simp]
theorem bellmanEval_deterministic (hv : Measurable v) {d : 𝓢 → 𝓐} (hd : Measurable d) (s : 𝓢) :
    M.bellmanEval γ (Kernel.deterministic d hd) v s = M.lookahead γ v (s, d s) := by
  rw [bellmanEval_def]
  exact Kernel.integral_deterministic' hd
    ((measurable_lookahead hv).comp measurable_prodMk_left).stronglyMeasurable

/-- A measurable deterministic policy `d` is `ε`-greedy for a measurable `v` if and only if its
evaluation operator at `v` is at least the optimality operator minus `ε`. -/
theorem isApproxGreedy_iff_bellman_sub_le_bellmanEval (hv : Measurable v) {ε : ℝ} {d : 𝓢 → 𝓐}
    (hd : Measurable d) :
    M.IsApproxGreedy γ ε v d ↔
      M.bellman γ v - (fun _ ↦ ε) ≤ M.bellmanEval γ (Kernel.deterministic d hd) v := by
  simp only [isApproxGreedy_def, Pi.le_def, Pi.sub_apply, bellmanEval_deterministic hv hd]

/-- When the lookahead is bounded above in the action, a measurable deterministic policy `d` is
greedy for a measurable `v` if and only if its evaluation operator agrees with the optimality
operator at `v`. -/
theorem isApproxGreedy_zero_iff_bellmanEval_eq (hv : Measurable v) {d : 𝓢 → 𝓐}
    (hd : Measurable d) (hv_bdd : ∀ s, BddAbove (range fun a ↦ M.lookahead γ v (s, a))) :
    M.IsApproxGreedy γ 0 v d ↔
      M.bellmanEval γ (Kernel.deterministic d hd) v = M.bellman γ v := by
  simp only [isApproxGreedy_zero_iff hv_bdd, funext_iff, bellmanEval_deterministic hv hd]

/-- With bounded rewards, the evaluation operator is monotone on bounded measurable functions. -/
theorem bellmanEval_mono [IsFiniteKernel π] (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (hw : Measurable w) (hwB : ∀ s, |w s| ≤ B')
    (hvw : v ≤ w) : M.bellmanEval γ π v ≤ M.bellmanEval γ π w := fun s ↦
  integral_mono (integrable_lookahead_prodMk_left hR hv hvB s _)
    (integrable_lookahead_prodMk_left hR hw hwB s _) fun _ ↦
    lookahead_mono (integrable_of_abs_le hv hvB _) (integrable_of_abs_le hw hwB _) hvw

/-- With bounded rewards, adding a constant `c` to a bounded measurable argument of the evaluation
operator adds `γ * c` to its value. -/
theorem bellmanEval_add_const [IsMarkovKernel π] (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (c : ℝ) :
    M.bellmanEval γ π (v + fun _ ↦ c) = M.bellmanEval γ π v + fun _ ↦ γ * c := by
  ext s
  simp only [bellmanEval_def, Pi.add_apply, lookahead_add_const (integrable_of_abs_le hv hvB _)]
  rw [integral_add (integrable_lookahead_prodMk_left hR hv hvB s _) (integrable_const _)]
  simp

/-- With bounded rewards, the evaluation operator is a `γ`-contraction for the sup norm on bounded
measurable functions: if `|v - w| ≤ D` then
`|M.bellmanEval γ π v - M.bellmanEval γ π w| ≤ γ * D`. -/
theorem abs_bellmanEval_sub_le [IsMarkovKernel π] (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (hw : Measurable w) (hwB : ∀ s, |w s| ≤ B')
    (hD : ∀ s, |v s - w s| ≤ D) (s : 𝓢) :
    |M.bellmanEval γ π v s - M.bellmanEval γ π w s| ≤ γ * D := by
  have hB (u : 𝓢 → ℝ) {B₀ : ℝ} (huB : ∀ s, |u s| ≤ B₀) (s : 𝓢) :
      |((u + fun _ ↦ D : 𝓢 → ℝ)) s| ≤ B₀ + |D| :=
    (abs_add_le _ _).trans (add_le_add (huB s) le_rfl)
  exact abs_sub_le_of_monotone_of_add_const hD
    (bellmanEval_mono hR hv hvB (hw.add measurable_const) (hB w hwB))
    (bellmanEval_mono hR hw hwB (hv.add measurable_const) (hB v hvB))
    (bellmanEval_add_const hR hv hvB D) (bellmanEval_add_const hR hw hwB D) s

/-- The evaluation operator maps measurable functions to measurable functions. -/
theorem measurable_bellmanEval [IsSFiniteKernel π] (hv : Measurable v) :
    Measurable (M.bellmanEval γ π v) :=
  ((measurable_lookahead hv).stronglyMeasurable.integral_kernel_prod_right' (κ := π)).measurable

/-- With rewards bounded by `C` and `|v| ≤ B`, the evaluation operator is bounded by
`C + γ * B`. -/
theorem abs_bellmanEval_le [IsMarkovKernel π] (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hvB : ∀ s, |v s| ≤ B) (s : 𝓢) : |M.bellmanEval γ π v s| ≤ C + γ * B := by
  rw [bellmanEval_def]
  exact abs_integral_le_of_abs_le fun a ↦ abs_lookahead_le hR hvB (s, a)

/-- The iterates of the evaluation operator of a stationary policy at a measurable `v` are
measurable. -/
theorem measurable_bellmanEval_iterate [IsSFiniteKernel π] (hv : Measurable v) (n : ℕ) :
    Measurable ((M.bellmanEval γ π)^[n] v) := by
  induction n with
  | zero => exact hv
  | succ n ih => rw [Function.iterate_succ_apply']; exact measurable_bellmanEval ih

/-- With bounded rewards, the iterates of the evaluation operator of a stationary policy at a
bounded `v` are bounded. -/
theorem exists_abs_bellmanEval_iterate_le [IsMarkovKernel π] (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hvB : ∀ s, |v s| ≤ B) (n : ℕ) : ∃ B', ∀ s, |(M.bellmanEval γ π)^[n] v s| ≤ B' := by
  induction n with
  | zero => exact ⟨B, hvB⟩
  | succ n ih =>
    obtain ⟨B', hB'⟩ := ih
    exact ⟨C + γ * B', fun s ↦ by
      rw [Function.iterate_succ_apply']; exact abs_bellmanEval_le hR hB' s⟩

/-! ### The optimality operator as the maximum of the evaluation operators -/

/-- **Randomizing does not increase the supremum** [P, Proposition 6.2.1]: the evaluation operator
of every stationary policy is below the optimality operator, when the lookahead is integrable for
the policy and bounded above in the action. Both hold for finitely many actions
(`Integrable.of_finite`, `Finite.bddAbove_range`), and for bounded rewards and a bounded measurable
function (`Learning.MDP.integrable_lookahead_prodMk_left`,
`Learning.MDP.bddAbove_range_lookahead`). -/
theorem bellmanEval_le_bellman [IsMarkovKernel π]
    (hv : ∀ s, Integrable (fun a ↦ M.lookahead γ v (s, a)) (π s))
    (hv_bdd : ∀ s, BddAbove (range fun a ↦ M.lookahead γ v (s, a))) :
    M.bellmanEval γ π v ≤ M.bellman γ v := fun s ↦ by
  rw [bellmanEval_def]
  calc ∫ a, M.lookahead γ v (s, a) ∂(π s)
      ≤ ∫ _, M.bellman γ v s ∂(π s) :=
        integral_mono (hv s) (integrable_const _) fun a ↦ lookahead_le_bellman (hv_bdd s) a
    _ = M.bellman γ v s := by simp

/-- The greedy policy for `v` attains the optimality operator at `v`. -/
@[simp]
theorem bellmanEval_greedy [Fintype 𝓐] [Nonempty 𝓐] (hv : Measurable v) :
    M.bellmanEval γ (Kernel.deterministic (M.greedy γ v) (measurable_greedy hv)) v =
      M.bellman γ v := by
  ext s
  rw [bellmanEval_deterministic hv, lookahead_greedy]

/-! ### Finite state spaces

On a finite state space with measurable singletons, every function `𝓢 → ℝ` is bounded and
measurable, and the operators satisfy Blackwell's conditions on `𝓢 → ℝ` for the unit `1`. -/

section Finite

variable [Finite 𝓢] [MeasurableSingletonClass 𝓢]

/-- On a finite state space, the optimality operator satisfies Blackwell's conditions. -/
theorem isBlackwell_bellman [Finite 𝓐] [Nonempty 𝓐] : IsBlackwell 1 γ (M.bellman γ) where
  monotone _ _ :=
    bellman_mono (fun _ ↦ .of_finite) (fun _ ↦ .of_finite) fun _ ↦ Finite.bddAbove_range _
  map_add_smul_le v c _ := by
    rw [Pi.smul_one_eq_const, Pi.smul_one_eq_const,
      bellman_add_const (fun _ ↦ .of_finite) (fun _ ↦ Finite.bddAbove_range _)]

/-- On a finite state space, the optimality operator is `γ`-Lipschitz for the sup norm. -/
theorem lipschitzWith_bellman [Fintype 𝓢] [Finite 𝓐] [Nonempty 𝓐] :
    LipschitzWith γ (M.bellman γ) :=
  isBlackwell_bellman.lipschitzWith orderUnitNorm_one_eq_norm

/-- On a finite state space, the optimality operator is a contraction for the sup norm when
`γ < 1`. -/
theorem contractingWith_bellman [Fintype 𝓢] [Finite 𝓐] [Nonempty 𝓐] (hγ : γ < 1) :
    ContractingWith γ (M.bellman γ) :=
  ⟨hγ, lipschitzWith_bellman⟩

/-- On a finite state space and with bounded rewards, the evaluation operator of a stationary
policy satisfies Blackwell's conditions. -/
theorem isBlackwell_bellmanEval [IsMarkovKernel π] (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    IsBlackwell 1 γ (M.bellmanEval γ π) where
  monotone v w hvw := by
    obtain ⟨B, hB⟩ := Finite.exists_le fun s ↦ |v s|
    obtain ⟨B', hB'⟩ := Finite.exists_le fun s ↦ |w s|
    exact bellmanEval_mono hR .of_discrete hB .of_discrete hB' hvw
  map_add_smul_le v c _ := by
    obtain ⟨B, hB⟩ := Finite.exists_le fun s ↦ |v s|
    rw [Pi.smul_one_eq_const, Pi.smul_one_eq_const, bellmanEval_add_const hR .of_discrete hB]

/-- On a finite state space and with bounded rewards, the evaluation operator of a stationary
policy is `γ`-Lipschitz for the sup norm. -/
theorem lipschitzWith_bellmanEval [Fintype 𝓢] [IsMarkovKernel π]
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) : LipschitzWith γ (M.bellmanEval γ π) :=
  (isBlackwell_bellmanEval hR).lipschitzWith orderUnitNorm_one_eq_norm

/-- On a finite state space and with bounded rewards, the evaluation operator of a stationary
policy is a contraction for the sup norm when `γ < 1`. -/
theorem contractingWith_bellmanEval [Fintype 𝓢] [IsMarkovKernel π]
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hγ : γ < 1) : ContractingWith γ (M.bellmanEval γ π) :=
  ⟨hγ, lipschitzWith_bellmanEval hR⟩

end Finite

end Learning.MDP
