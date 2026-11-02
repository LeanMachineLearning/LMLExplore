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
  (for finitely many actions).

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
when the lookahead is bounded above in the action, for instance for finitely many actions.

## Main definitions

* `Learning.MDP.lookahead M γ v`: the one-step lookahead `(s, a) ↦ r (s, a) + γ * ∫ v dP (s, a)`.
* `Learning.MDP.bellmanEval M γ π`: the evaluation operator of the stationary policy `π`.
* `Learning.MDP.bellman M γ`: the Bellman optimality operator.
* `Learning.MDP.greedy M γ v`: the greedy deterministic policy for `v`.

## Main statements

* `Learning.MDP.bellman_mono`, `Learning.MDP.bellman_add_const`,
  `Learning.MDP.bellmanEval_mono`, `Learning.MDP.bellmanEval_add_const`: monotonicity and
  `T (v + c) = T v + γ * c`.
* `Learning.MDP.abs_bellman_sub_le`, `Learning.MDP.abs_bellmanEval_sub_le`: the operators are
  `γ`-contractions for the sup norm, stated pointwise.
* `Learning.MDP.measurable_bellman`, `Learning.MDP.abs_bellman_le`,
  `Learning.MDP.measurable_bellmanEval`, `Learning.MDP.abs_bellmanEval_le`: the operators preserve
  bounded measurable functions; `Learning.MDP.measurable_greedy`: the greedy policy of a measurable
  function is measurable.
* `Learning.MDP.bellmanEval_le_bellman`: randomizing does not increase the supremum
  [P, Proposition 6.2.1]; `Learning.MDP.isGreatest_bellmanEval`: the optimality operator is the
  maximum of the evaluation operators of measurable deterministic stationary policies, attained by
  the greedy policy (`Learning.MDP.bellmanEval_greedy`).
* `Learning.MDP.isBlackwell_bellman`, `Learning.MDP.contractingWith_bellman`,
  `Learning.MDP.isBlackwell_bellmanEval`, `Learning.MDP.contractingWith_bellmanEval`: on a finite
  state space, the operators satisfy Blackwell's conditions and are `γ`-contractions of `𝓢 → ℝ`
  with the sup norm.

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §§6.1–6.2
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

/-- With bounded rewards, the lookahead of a bounded measurable function is integrable over the
actions, for every finite measure on them. -/
lemma integrable_lookahead_prodMk_left (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (s : 𝓢) (ν : Measure 𝓐) [IsFiniteMeasure ν] :
    Integrable (fun a ↦ M.lookahead γ v (s, a)) ν :=
  integrable_of_abs_le ((measurable_lookahead hv).comp measurable_prodMk_left)
    (fun a ↦ abs_lookahead_le hR hvB (s, a)) ν

/-! ### The optimality operator -/

variable (M γ) in
/-- The Bellman optimality operator `v ↦ (s ↦ ⨆ a, r (s, a) + γ * ∫ v dP (s, a))`. -/
noncomputable def bellman (v : 𝓢 → ℝ) (s : 𝓢) : ℝ := ⨆ a, M.lookahead γ v (s, a)

variable (M γ) in
lemma bellman_def (v : 𝓢 → ℝ) (s : 𝓢) : M.bellman γ v s = ⨆ a, M.lookahead γ v (s, a) :=
  (rfl)

lemma lookahead_le_bellman [Finite 𝓐] (v : 𝓢 → ℝ) (s : 𝓢) (a : 𝓐) :
    M.lookahead γ v (s, a) ≤ M.bellman γ v s := by
  rw [bellman_def]
  exact le_ciSup (Finite.bddAbove_range fun a ↦ M.lookahead γ v (s, a)) a

lemma bellman_le_iff [Finite 𝓐] [Nonempty 𝓐] {s : 𝓢} {c : ℝ} :
    M.bellman γ v s ≤ c ↔ ∀ a, M.lookahead γ v (s, a) ≤ c := by
  rw [bellman_def]
  exact ciSup_le_iff (Finite.bddAbove_range fun a ↦ M.lookahead γ v (s, a))

/-- The optimality operator is monotone. -/
theorem bellman_mono [Finite 𝓐] (hv : ∀ p, Integrable v (M.P p)) (hw : ∀ p, Integrable w (M.P p))
    (hvw : v ≤ w) : M.bellman γ v ≤ M.bellman γ w := fun s ↦ by
  rw [bellman_def, bellman_def]
  exact ciSup_mono (Finite.bddAbove_range fun a ↦ M.lookahead γ w (s, a)) fun _ ↦
    lookahead_mono (hv _) (hw _) hvw

/-- Adding a constant `c` to the argument of the optimality operator adds `γ * c` to its value. -/
theorem bellman_add_const [Finite 𝓐] [Nonempty 𝓐] (hv : ∀ p, Integrable v (M.P p)) (c : ℝ) :
    M.bellman γ (v + fun _ ↦ c) = M.bellman γ v + fun _ ↦ γ * c := by
  ext s
  simp only [bellman_def, Pi.add_apply, lookahead_add_const (hv _)]
  exact ((OrderIso.addRight ((γ : ℝ) * c)).map_ciSup (Finite.bddAbove_range _)).symm

/-- The optimality operator is a `γ`-contraction for the sup norm: if `|v - w| ≤ D` then
`|M.bellman γ v - M.bellman γ w| ≤ γ * D`. -/
theorem abs_bellman_sub_le [Finite 𝓐] [Nonempty 𝓐] (hv : ∀ p, Integrable v (M.P p))
    (hw : ∀ p, Integrable w (M.P p)) (hD : ∀ s, |v s - w s| ≤ D) (s : 𝓢) :
    |M.bellman γ v s - M.bellman γ w s| ≤ γ * D :=
  abs_sub_le_of_monotone_of_add_const hD (bellman_mono hv fun p ↦ (hw p).add (integrable_const D))
    (bellman_mono hw fun p ↦ (hv p).add (integrable_const D)) (bellman_add_const hv D)
    (bellman_add_const hw D) s

/-- The optimality operator maps measurable functions to measurable functions, for countably many
actions. -/
theorem measurable_bellman [Countable 𝓐] (hv : Measurable v) : Measurable (M.bellman γ v) :=
  Measurable.iSup fun _ ↦ (measurable_lookahead hv).comp measurable_prodMk_right

/-- With rewards bounded by `C` and `|v| ≤ B`, the optimality operator is bounded by
`C + γ * B`. -/
theorem abs_bellman_le [Nonempty 𝓐] (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hvB : ∀ s, |v s| ≤ B)
    (s : 𝓢) : |M.bellman γ v s| ≤ C + γ * B := by
  have h := fun a ↦ abs_le.1 (abs_lookahead_le (γ := γ) hR hvB (s, a))
  have hbdd : BddAbove (range fun a ↦ M.lookahead γ v (s, a)) :=
    ⟨C + γ * B, forall_mem_range.2 fun a ↦ (h a).2⟩
  obtain ⟨a⟩ := ‹Nonempty 𝓐›
  exact abs_le.2 ⟨(h a).1.trans (le_ciSup hbdd a), ciSup_le fun a ↦ (h a).2⟩

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
  le_antisymm (lookahead_le_bellman v s _)
    (bellman_le_iff.2 fun a ↦ by
      rw [greedy_def]; exact isMaxOn_argmax (fun a ↦ M.lookahead γ v (s, a)) a)

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

/-! ### The optimality operator as the maximum of the evaluation operators -/

/-- **Randomizing does not increase the supremum** [P, Proposition 6.2.1]: the evaluation operator
of every stationary policy is below the optimality operator. -/
theorem bellmanEval_le_bellman [Finite 𝓐] [MeasurableSingletonClass 𝓐] [IsMarkovKernel π]
    (v : 𝓢 → ℝ) : M.bellmanEval γ π v ≤ M.bellman γ v := fun s ↦ by
  rw [bellmanEval_def]
  calc ∫ a, M.lookahead γ v (s, a) ∂(π s)
      ≤ ∫ _, M.bellman γ v s ∂(π s) :=
        integral_mono .of_finite (integrable_const _) fun a ↦ lookahead_le_bellman v s a
    _ = M.bellman γ v s := by simp

/-- The greedy policy for `v` attains the optimality operator at `v`. -/
@[simp]
theorem bellmanEval_greedy [Fintype 𝓐] [Nonempty 𝓐] (hv : Measurable v) :
    M.bellmanEval γ (Kernel.deterministic (M.greedy γ v) (measurable_greedy hv)) v =
      M.bellman γ v := by
  ext s
  rw [bellmanEval_deterministic hv, lookahead_greedy]

/-- The optimality operator at a measurable `v` is the greatest value at `v` of the evaluation
operators of the measurable deterministic stationary policies. -/
theorem isGreatest_bellmanEval [Finite 𝓐] [Nonempty 𝓐] [MeasurableSingletonClass 𝓐]
    (hv : Measurable v) :
    IsGreatest (range fun d : {d : 𝓢 → 𝓐 // Measurable d} ↦
      M.bellmanEval γ (Kernel.deterministic d d.2) v) (M.bellman γ v) := by
  have := Fintype.ofFinite 𝓐
  exact ⟨⟨⟨_, measurable_greedy hv⟩, bellmanEval_greedy hv⟩,
    forall_mem_range.2 fun _ ↦ bellmanEval_le_bellman v⟩

/-! ### Finite state spaces

On a finite state space with measurable singletons, every function `𝓢 → ℝ` is bounded and
measurable, and the operators satisfy Blackwell's conditions on `𝓢 → ℝ` for the unit `1`. -/

section Finite

variable [Finite 𝓢] [MeasurableSingletonClass 𝓢]

/-- On a finite state space, the optimality operator satisfies Blackwell's conditions. -/
theorem isBlackwell_bellman [Finite 𝓐] [Nonempty 𝓐] : IsBlackwell 1 γ (M.bellman γ) where
  monotone _ _ := bellman_mono (fun _ ↦ .of_finite) (fun _ ↦ .of_finite)
  map_add_smul_le v c _ := by
    rw [Pi.smul_one_eq_const, Pi.smul_one_eq_const, bellman_add_const fun _ ↦ .of_finite]

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
