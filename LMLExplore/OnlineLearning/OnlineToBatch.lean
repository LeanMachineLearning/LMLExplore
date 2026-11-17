/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib
public import LMLExplore.OnlineLearning.SubgradientDescent
public import LMLExplore.Probability.HasCondDistrib
public import Mathlib.Analysis.Convex.Jensen

/-!
# Online-to-batch conversion in expectation

A stochastic optimization problem asks for a point `x` of a convex set `V` with a small *risk*
`F x`, the mean of a loss `f x ξ` under a random datum `ξ`. An online learner solves it: feed it
the losses `ℓ t = α t * f · (ξ t)` of fresh data `ξ t` at the rounds `t < n`, and return the
weighted average of its plays
`(range n).centerMass α x = (∑ t < n, α t)⁻¹ • ∑ t < n, α t • x t`.
For a convex risk and nonnegative weights `α t` of positive sum, its expected risk exceeds the
risk of every comparator `u` by at most the expected regret divided by `∑ t < n, α t`
[Ora, Theorem 3.1]:
`𝔼[F (centerMass α x)] ≤ 𝔼[F u] + 𝔼[regret_n u] / ∑ t < n, α t`.
Regret bounds that hold for every sequence of losses thus become convergence rates of stochastic
optimization.

The proof has two steps. Each play is chosen before its datum is drawn, so the loss of a play has
the mean of its risk, `𝔼[f (x t) (ξ t)] = 𝔼[F (x t)]`, and likewise for the comparator: the
expected regret is `∑ t < n, α t * (𝔼[F (x t)] - 𝔼[F u])`
(`integral_regret_eq_sum_mul_integral_sub`). Jensen's inequality for the convex `F` then bounds the
risk of the average.

## The data

The plays, the comparator and the data are random variables on a probability space. The only
assumption on the data is the one the first step needs: given the play `x t` and the comparator
`u`, the datum `ξ t` has a conditional law `κ t (x t, u)` whose risk is `F`, that is
`∫ z, f y z ∂κ t (x t ω, u ω) = F y` for all `y ∈ V` and almost every `ω`
(`ProbabilityTheory.HasCondDistrib`). This holds when `ξ t` is independent of `x t` and `u` with
a law `ρ` of risk `F`, the setting of [Ora], where the data are i.i.d. and the internal randomness
of the learner is independent of them (`integral_apply_centerMass_le_of_indepFun`). The data need
not be independent: if the plays and the comparator are measurable for a filtration `ℱ t` and
the conditional law of `ξ t` given `ℱ t` has risk `F`, then so has a conditional law of `ξ t`
given `(x t, u)`, which conditions on less information, whenever one exists (for instance when
the space of data is standard Borel). Nothing else is assumed on the dependence between the data
of different rounds.

A hypothesis on conditional means, `𝔼[f y (ξ t) | ℱ t] = F y` almost surely for each fixed `y`, is
not enough: the exceptional null set depends on `y`, and the play `x t` is random. Let the datum
`ξ 0 = x 0` be uniform on `[0, 1]`, with the loss `f y z = 0` if `y = z` and `1` otherwise. Every
fixed `y` has `f y (ξ 0) = 1` almost surely, so `F = 1`, while `f (x 0) (ξ 0) = 0`: for `n = 1`
and a deterministic comparator, the conclusion would read `1 ≤ 0`. The conditional law, which
constrains all `y` at once, rules this out.

## Main statements

* `integral_regret_eq_sum_mul_integral_sub_integral`: the expected regret of the losses
  `α t * f · (ξ t)` is `∑ t < n, α t * (𝔼[f (x t) (ξ t)] - 𝔼[f u (ξ t)])`.
* `integral_regret_eq_sum_mul_integral_sub` [Ora, Theorem 3.1, (3.1)]: the expected regret is
  `∑ t < n, α t * (𝔼[F (x t)] - 𝔼[F u])`.
* `integral_apply_centerMass_le_integral_add_integral_regret_div` [Ora, Theorem 3.1]: the
  online-to-batch conversion, against a random comparator `u`.
* `integral_apply_centerMass_le_add_integral_regret_div`: its form for a deterministic comparator,
  with the conditional laws of the data given the plays alone.
* `integral_apply_centerMass_le_of_indepFun`: its form for data independent of the plays and the
  comparator, with a common law `ρ` and the risk `y ↦ ∫ z, f y z ∂ρ`, as [Ora] states it.
* `integral_apply_smul_sum_le_of_onlineSubgradientDescent` [Ora, Theorem 3.1 with Theorem 2.13]:
  stochastic subgradient descent with a constant learning rate `η` on a convex set, bounded or
  not, has average play of expected risk at most
  `F u + (‖u - x₀‖ ^ 2 / η + η n G ^ 2) / (2 n)`, for stochastic subgradients of second moments at
  most `G ^ 2`.
* `integral_apply_centerMass_le_of_onlineSubgradientDescent_of_strongConvexOn`
  [Ora, Example 4.12]: for a `μ`-strongly convex risk `F` and convex losses `f · z`, the weights
  `t + 1` and the learning rates `2 / ((t + 2) μ)` give the expected risk
  `F u + 2 G ^ 2 / (μ (n + 1))`, with no logarithmic factor. Only the risk is strongly convex, as
  for least squares with a positive definite covariance: in expectation, the stochastic
  subgradients satisfy the subgradient inequality of the strongly convex risk.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped RealInnerProductSpace Topology

namespace LMLExplore.OnlineLearning

variable {Ω E Z : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {mZ : MeasurableSpace Z}
  {mE : MeasurableSpace E} {n : ℕ}

/-- The loss at a point `φ X` chosen before the datum has the mean of the risk: if the datum `Y`
has conditional law `κ` given `X`, of risk `F (φ (X ω))` at `φ (X ω)` for almost every `ω`, and the
loss `f (φ X) Y` is integrable, then so is the risk `F (φ X)`, with the same mean. This is
`HasCondDistrib.integrable_and_integral_comp_prodMk_eq_of_ae_integral_eq` for the loss
`(a, z) ↦ f (φ a) z`. -/
private lemma integrable_and_integral_eq_of_risk_comp [SFinite P] {𝓧 : Type*}
    {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧} {Y : Ω → Z} {κ : Kernel 𝓧 Z} [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P)
    {φ : 𝓧 → E} (hφ : Measurable φ) {f : E → Z → ℝ} (hf : Measurable (Function.uncurry f))
    {F : E → ℝ} (hF : ∀ᵐ ω ∂P, ∫ z, f (φ (X ω)) z ∂(κ (X ω)) = F (φ (X ω)))
    (hint : Integrable (fun ω ↦ f (φ (X ω)) (Y ω)) P) :
    Integrable (fun ω ↦ F (φ (X ω))) P ∧
      ∫ ω, f (φ (X ω)) (Y ω) ∂P = ∫ ω, F (φ (X ω)) ∂P :=
  h.integrable_and_integral_comp_prodMk_eq_of_ae_integral_eq (g := fun p ↦ f (φ p.1) p.2)
    (G := fun a ↦ F (φ a))
    (hf.comp ((hφ.comp measurable_fst).prodMk measurable_snd)).aestronglyMeasurable hF hint

/-- The regret of the weighted losses `α t * f · (ξ t)` is integrable when each loss is integrable
at the plays and at the comparator. -/
private lemma integrable_regret {f : E → Z → ℝ} (α : ℕ → ℝ) (x : ℕ → Ω → E) (u : Ω → E)
    (ξ : ℕ → Ω → Z) (hfx : ∀ t < n, Integrable (fun ω ↦ f (x t ω) (ξ t ω)) P)
    (hfu : ∀ t < n, Integrable (fun ω ↦ f (u ω) (ξ t ω)) P) :
    Integrable (fun ω ↦ regret (fun t y ↦ α t * f y (ξ t ω)) (fun t ↦ x t ω) (u ω) n) P := by
  simp only [regret_def]
  exact integrable_finsetSum _ fun t ht ↦
    ((hfx t (mem_range.mp ht)).const_mul _).sub ((hfu t (mem_range.mp ht)).const_mul _)

/-- The risks at the plays and at the comparator are integrable, with the means of the losses. -/
private lemma integrable_and_integral_eq_of_risk [SFinite P] {V : Set E} {f : E → Z → ℝ}
    (hf : Measurable (Function.uncurry f)) {F : E → ℝ} {x : ℕ → Ω → E} {u : Ω → E}
    {ξ : ℕ → Ω → Z} {κ : ℕ → Kernel (E × E) Z} [∀ t, IsSFiniteKernel (κ t)]
    (hκ : ∀ t < n, HasCondDistrib (ξ t) (fun ω ↦ (x t ω, u ω)) (κ t) P)
    (hF : ∀ t < n, ∀ᵐ ω ∂P, ∀ y ∈ V, ∫ z, f y z ∂(κ t (x t ω, u ω)) = F y)
    (hxV : ∀ t < n, ∀ᵐ ω ∂P, x t ω ∈ V) (huV : ∀ᵐ ω ∂P, u ω ∈ V)
    (hfx : ∀ t < n, Integrable (fun ω ↦ f (x t ω) (ξ t ω)) P)
    (hfu : ∀ t < n, Integrable (fun ω ↦ f (u ω) (ξ t ω)) P) {t : ℕ} (ht : t < n) :
    (Integrable (fun ω ↦ F (x t ω)) P ∧
      ∫ ω, f (x t ω) (ξ t ω) ∂P = ∫ ω, F (x t ω) ∂P) ∧
    (Integrable (fun ω ↦ F (u ω)) P ∧
      ∫ ω, f (u ω) (ξ t ω) ∂P = ∫ ω, F (u ω) ∂P) :=
  ⟨integrable_and_integral_eq_of_risk_comp (hκ t ht) measurable_fst hf
      (((hF t ht).and (hxV t ht)).mono fun _ hω ↦ hω.1 _ hω.2) (hfx t ht),
    integrable_and_integral_eq_of_risk_comp (hκ t ht) measurable_snd hf
      (((hF t ht).and huV).mono fun _ hω ↦ hω.1 _ hω.2) (hfu t ht)⟩

/-- The plays of projected online subgradient descent from a point of `V` stay in `V`. -/
private lemma mem_of_step {V : Set E} {x : ℕ → Ω → E} (hx₀ : ∀ ω, x 0 ω ∈ V)
    (hstep : ∀ t < n, ∀ ω, x (t + 1) ω ∈ V) {t : ℕ} (ht : t < n) (ω : Ω) : x t ω ∈ V := by
  rcases t with _ | t
  · exact hx₀ ω
  · exact hstep t (by omega) ω

/-- **The expected regret of weighted losses.** If each loss `f · (ξ t)` is integrable at the
plays and at the comparator, the expected regret of the losses `α t * f · (ξ t)` against `u` is
`∑ t < n, α t * (𝔼[f (x t) (ξ t)] - 𝔼[f u (ξ t)])`. -/
theorem integral_regret_eq_sum_mul_integral_sub_integral {f : E → Z → ℝ} (α : ℕ → ℝ)
    (x : ℕ → Ω → E) (u : Ω → E) (ξ : ℕ → Ω → Z)
    (hfx : ∀ t < n, Integrable (fun ω ↦ f (x t ω) (ξ t ω)) P)
    (hfu : ∀ t < n, Integrable (fun ω ↦ f (u ω) (ξ t ω)) P) :
    ∫ ω, regret (fun t y ↦ α t * f y (ξ t ω)) (fun t ↦ x t ω) (u ω) n ∂P =
      ∑ t ∈ range n, α t * (∫ ω, f (x t ω) (ξ t ω) ∂P - ∫ ω, f (u ω) (ξ t ω) ∂P) := by
  simp only [regret_def]
  rw [integral_finsetSum (f := fun t ω ↦ α t * f (x t ω) (ξ t ω) - α t * f (u ω) (ξ t ω)) _
    fun t ht ↦
      ((hfx t (mem_range.mp ht)).const_mul _).sub ((hfu t (mem_range.mp ht)).const_mul _)]
  refine sum_congr rfl fun t ht ↦ ?_
  have ht' := mem_range.mp ht
  rw [integral_sub ((hfx t ht').const_mul _) ((hfu t ht').const_mul _), integral_const_mul,
    integral_const_mul, mul_sub]

/-- **The expected regret is the regret of the risk** [Ora, Theorem 3.1, (3.1)]. Let the datum
`ξ t` have conditional law `κ t (x t, u)` given the play `x t` and the comparator `u`, of risk `F`
on a set `V` containing the plays and the comparator: `∫ z, f y z ∂κ t (x t ω, u ω) = F y` for
`y ∈ V`. Then the expected regret of the losses `α t * f · (ξ t)` against `u` is
`∑ t < n, α t * (𝔼[F (x t)] - 𝔼[F u])`. No convexity is needed. -/
theorem integral_regret_eq_sum_mul_integral_sub [SFinite P] {V : Set E} {f : E → Z → ℝ}
    (hf : Measurable (Function.uncurry f)) {F : E → ℝ} (α : ℕ → ℝ) (x : ℕ → Ω → E) (u : Ω → E)
    (ξ : ℕ → Ω → Z) {κ : ℕ → Kernel (E × E) Z} [∀ t, IsSFiniteKernel (κ t)]
    (hκ : ∀ t < n, HasCondDistrib (ξ t) (fun ω ↦ (x t ω, u ω)) (κ t) P)
    (hF : ∀ t < n, ∀ᵐ ω ∂P, ∀ y ∈ V, ∫ z, f y z ∂(κ t (x t ω, u ω)) = F y)
    (hxV : ∀ t < n, ∀ᵐ ω ∂P, x t ω ∈ V) (huV : ∀ᵐ ω ∂P, u ω ∈ V)
    (hfx : ∀ t < n, Integrable (fun ω ↦ f (x t ω) (ξ t ω)) P)
    (hfu : ∀ t < n, Integrable (fun ω ↦ f (u ω) (ξ t ω)) P) :
    ∫ ω, regret (fun t y ↦ α t * f y (ξ t ω)) (fun t ↦ x t ω) (u ω) n ∂P =
      ∑ t ∈ range n, α t * (∫ ω, F (x t ω) ∂P - ∫ ω, F (u ω) ∂P) := by
  rw [integral_regret_eq_sum_mul_integral_sub_integral α x u ξ hfx hfu]
  refine sum_congr rfl fun t ht ↦ ?_
  have h := integrable_and_integral_eq_of_risk hf hκ hF hxV huV hfx hfu (mem_range.mp ht)
  rw [h.1.2, h.2.2]

section NormedSpace

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Online-to-batch conversion** [Ora, Theorem 3.1]. Let `F` be convex on a set `V` containing
the plays `x t` and the comparator `u`, and let the datum `ξ t` have conditional law
`κ t (x t, u)` given the play and the comparator, of risk `F` on `V`, for `t < n`. For weights
`α t ≥ 0` of positive sum, the weighted average of the plays has expected risk
`𝔼[F (centerMass α x)] ≤ 𝔼[F u] + 𝔼[regret_n u] / ∑ t < n, α t`,
where `regret_n u` is the regret of the losses `α t * f · (ξ t)` against `u`. The comparator may
be random, for example chosen from the internal randomness of the learner. -/
theorem integral_apply_centerMass_le_integral_add_integral_regret_div [SFinite P] {V : Set E}
    {f : E → Z → ℝ} (hf : Measurable (Function.uncurry f)) {F : E → ℝ} (hFV : ConvexOn ℝ V F)
    {α : ℕ → ℝ} (hα : ∀ t < n, 0 ≤ α t) (hαn : 0 < ∑ t ∈ range n, α t) (x : ℕ → Ω → E)
    (u : Ω → E) (ξ : ℕ → Ω → Z) {κ : ℕ → Kernel (E × E) Z} [∀ t, IsSFiniteKernel (κ t)]
    (hκ : ∀ t < n, HasCondDistrib (ξ t) (fun ω ↦ (x t ω, u ω)) (κ t) P)
    (hF : ∀ t < n, ∀ᵐ ω ∂P, ∀ y ∈ V, ∫ z, f y z ∂(κ t (x t ω, u ω)) = F y)
    (hxV : ∀ t < n, ∀ᵐ ω ∂P, x t ω ∈ V) (huV : ∀ᵐ ω ∂P, u ω ∈ V)
    (hfx : ∀ t < n, Integrable (fun ω ↦ f (x t ω) (ξ t ω)) P)
    (hfu : ∀ t < n, Integrable (fun ω ↦ f (u ω) (ξ t ω)) P)
    (hint : Integrable (fun ω ↦ F ((range n).centerMass α fun t ↦ x t ω)) P) :
    ∫ ω, F ((range n).centerMass α fun t ↦ x t ω) ∂P ≤
      ∫ ω, F (u ω) ∂P +
        (∫ ω, regret (fun t y ↦ α t * f y (ξ t ω)) (fun t ↦ x t ω) (u ω) n ∂P) /
          ∑ t ∈ range n, α t := by
  set A := ∑ t ∈ range n, α t with hA
  have h t (ht : t ∈ range n) :=
    integrable_and_integral_eq_of_risk hf hκ hF hxV huV hfx hfu (mem_range.mp ht)
  -- Jensen's inequality at almost every `ω`
  have h_jensen : ∀ᵐ ω ∂P, F ((range n).centerMass α fun t ↦ x t ω) ≤
      A⁻¹ * ∑ t ∈ range n, α t * F (x t ω) := by
    have hx_all : ∀ᵐ ω ∂P, ∀ t ∈ range n, x t ω ∈ V :=
      (Filter.eventually_all_finset _).2 fun t ht ↦ hxV t (mem_range.mp ht)
    filter_upwards [hx_all] with ω hω
    refine (hFV.map_centerMass_le (fun t ht ↦ hα t (mem_range.mp ht)) hαn hω).trans_eq ?_
    simp [centerMass, ← hA, smul_eq_mul]
  have h_int_sum : Integrable (fun ω ↦ A⁻¹ * ∑ t ∈ range n, α t * F (x t ω)) P :=
    (integrable_finsetSum _ fun t ht ↦ (h t ht).1.1.const_mul _).const_mul _
  refine (integral_mono_ae hint h_int_sum h_jensen).trans_eq ?_
  rw [integral_regret_eq_sum_mul_integral_sub hf α x u ξ hκ hF hxV huV hfx hfu,
    integral_const_mul, integral_finsetSum _ fun t ht ↦ (h t ht).1.1.const_mul _]
  simp only [integral_const_mul, mul_sub, sum_sub_distrib, ← sum_mul, ← hA]
  field_simp
  ring

/-- **Online-to-batch conversion against a fixed comparator** [Ora, Theorem 3.1]. Let `F` be
convex on a set `V` containing the plays `x t` and the comparator `u`, and let the datum `ξ t`
have conditional law `κ t (x t)` given the play, of risk `F` on `V`, for `t < n`. For weights
`α t ≥ 0` of positive sum,
`𝔼[F (centerMass α x)] ≤ F u + 𝔼[regret_n u] / ∑ t < n, α t`,
where `regret_n u` is the regret of the losses `α t * f · (ξ t)` against `u`. -/
theorem integral_apply_centerMass_le_add_integral_regret_div [IsProbabilityMeasure P] {V : Set E}
    {f : E → Z → ℝ} (hf : Measurable (Function.uncurry f)) {F : E → ℝ} (hFV : ConvexOn ℝ V F)
    {α : ℕ → ℝ} (hα : ∀ t < n, 0 ≤ α t) (hαn : 0 < ∑ t ∈ range n, α t) (x : ℕ → Ω → E) {u : E}
    (ξ : ℕ → Ω → Z) {κ : ℕ → Kernel E Z} [∀ t, IsSFiniteKernel (κ t)]
    (hκ : ∀ t < n, HasCondDistrib (ξ t) (x t) (κ t) P)
    (hF : ∀ t < n, ∀ᵐ ω ∂P, ∀ y ∈ V, ∫ z, f y z ∂(κ t (x t ω)) = F y)
    (hxV : ∀ t < n, ∀ᵐ ω ∂P, x t ω ∈ V) (hu : u ∈ V)
    (hfx : ∀ t < n, Integrable (fun ω ↦ f (x t ω) (ξ t ω)) P)
    (hfu : ∀ t < n, Integrable (fun ω ↦ f u (ξ t ω)) P)
    (hint : Integrable (fun ω ↦ F ((range n).centerMass α fun t ↦ x t ω)) P) :
    ∫ ω, F ((range n).centerMass α fun t ↦ x t ω) ∂P ≤
      F u + (∫ ω, regret (fun t y ↦ α t * f y (ξ t ω)) (fun t ↦ x t ω) u n ∂P) /
        ∑ t ∈ range n, α t := by
  -- condition on the pair `(x t, u)`, whose second coordinate is constant
  have h := integral_apply_centerMass_le_integral_add_integral_regret_div hf hFV hα hαn x
    (fun _ ↦ u) ξ (κ := fun t ↦ (κ t).prodMkRight E)
    (fun t ht ↦ (hκ t ht).prod_right measurable_const)
    (fun t ht ↦ (hF t ht).mono fun ω h y hy ↦ by rw [Kernel.prodMkRight_apply]; exact h y hy)
    hxV (ae_of_all _ fun _ ↦ hu) hfx hfu hint
  rwa [integral_const, probReal_univ, one_smul] at h

/-- **Online-to-batch conversion for independent data** [Ora, Theorem 3.1], as [Ora] states it.
Let the datum `ξ t` have law `ρ` and be independent of the play `x t` and the comparator `u`, for
`t < n`, as when the data are i.i.d. and the internal randomness of the learner is independent of
them. Let the risk `y ↦ ∫ z, f y z ∂ρ` be convex on a set `V` containing the plays and the
comparator. For weights `α t ≥ 0` of positive sum, the weighted average of the plays satisfies
`𝔼[F (centerMass α x)] ≤ 𝔼[F u] + 𝔼[regret_n u] / ∑ t < n, α t`. -/
theorem integral_apply_centerMass_le_of_indepFun [IsFiniteMeasure P] {V : Set E}
    {f : E → Z → ℝ} (hf : Measurable (Function.uncurry f)) {ρ : Measure Z} [SFinite ρ]
    (hFV : ConvexOn ℝ V fun y ↦ ∫ z, f y z ∂ρ) {α : ℕ → ℝ} (hα : ∀ t < n, 0 ≤ α t)
    (hαn : 0 < ∑ t ∈ range n, α t) (x : ℕ → Ω → E) (u : Ω → E) (ξ : ℕ → Ω → Z)
    (hx : ∀ t < n, AEMeasurable (x t) P) (hu : AEMeasurable u P)
    (hind : ∀ t < n, IndepFun (fun ω ↦ (x t ω, u ω)) (ξ t) P) (hρ : ∀ t < n, HasLaw (ξ t) ρ P)
    (hxV : ∀ t < n, ∀ᵐ ω ∂P, x t ω ∈ V) (huV : ∀ᵐ ω ∂P, u ω ∈ V)
    (hfx : ∀ t < n, Integrable (fun ω ↦ f (x t ω) (ξ t ω)) P)
    (hfu : ∀ t < n, Integrable (fun ω ↦ f (u ω) (ξ t ω)) P)
    (hint : Integrable (fun ω ↦ ∫ z, f ((range n).centerMass α fun t ↦ x t ω) z ∂ρ) P) :
    ∫ ω, ∫ z, f ((range n).centerMass α fun t ↦ x t ω) z ∂ρ ∂P ≤
      ∫ ω, ∫ z, f (u ω) z ∂ρ ∂P +
        (∫ ω, regret (fun t y ↦ α t * f y (ξ t ω)) (fun t ↦ x t ω) (u ω) n ∂P) /
          ∑ t ∈ range n, α t :=
  integral_apply_centerMass_le_integral_add_integral_regret_div hf hFV hα hαn x u ξ
    (κ := fun _ ↦ Kernel.const (E × E) ρ)
    (fun t ht ↦ (hind t ht).hasCondDistrib_const ((hx t ht).prodMk hu) (hρ t ht))
    (fun _ _ ↦ ae_of_all _ fun _ _ _ ↦ by rw [Kernel.const_apply]) hxV huV hfx hfu hint

end NormedSpace

section InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- The sum of the second moments of the stochastic subgradients `g t`, each at most `G ^ 2`, is
the mean of an integrable function, at most `n G ^ 2`. -/
private lemma integrable_sum_norm_sq_and_integral_le {g : ℕ → Ω → E} {G : ℝ}
    (hg_int : ∀ t < n, Integrable (fun ω ↦ ‖g t ω‖ ^ 2) P)
    (hgG : ∀ t < n, ∫ ω, ‖g t ω‖ ^ 2 ∂P ≤ G ^ 2) :
    Integrable (fun ω ↦ ∑ t ∈ range n, ‖g t ω‖ ^ 2) P ∧
      ∫ ω, ∑ t ∈ range n, ‖g t ω‖ ^ 2 ∂P ≤ n * G ^ 2 := by
  refine ⟨integrable_finsetSum _ fun t ht ↦ hg_int t (mem_range.mp ht), ?_⟩
  rw [integral_finsetSum _ fun t ht ↦ hg_int t (mem_range.mp ht)]
  simpa using sum_le_sum fun t ht ↦ hgG t (mem_range.mp ht)

/-- **Stochastic subgradient descent with a constant learning rate** [Ora, Theorem 3.1 with
Theorem 2.13]. Let `F` be convex on a set `V`, bounded or not, and let `u ∈ V`. Let the
plays start at `x 0 = x₀ ∈ V` and let each `x (t + 1)` be a point of `V` nearest to
`x t - η • g t`, where `g t` is a subgradient of `f · (ξ t)` within `V` at `x t`, with second moment
`𝔼 ‖g t‖ ^ 2 ≤ G ^ 2`. Let the datum `ξ t` have conditional law `κ t (x t)` given the play, of risk
`F` on `V`, for `t < n`, with `n > 0`. Then the average play has expected risk
`𝔼[F ((1 / n) ∑ t < n, x t)] ≤ F u + (‖u - x₀‖ ^ 2 / η + η n G ^ 2) / (2 n)`. -/
theorem integral_apply_smul_sum_le_of_onlineSubgradientDescent [IsProbabilityMeasure P]
    {V : Set E} {f : E → Z → ℝ} (hf : Measurable (Function.uncurry f)) {F : E → ℝ}
    (hFV : ConvexOn ℝ V F)
    {η G : ℝ} (hη : 0 < η) (hn : 0 < n) (x g : ℕ → Ω → E) (ξ : ℕ → Ω → Z)
    {κ : ℕ → Kernel E Z} [∀ t, IsSFiniteKernel (κ t)]
    (hκ : ∀ t < n, HasCondDistrib (ξ t) (x t) (κ t) P)
    (hF : ∀ t < n, ∀ᵐ ω ∂P, ∀ y ∈ V, ∫ z, f y z ∂(κ t (x t ω)) = F y) {x₀ u : E}
    (hx₀ : ∀ ω, x 0 ω = x₀) (hx₀V : x₀ ∈ V) (hu : u ∈ V)
    (hg : ∀ t < n, ∀ ω,
      HasSubgradientWithinAt (fun y ↦ f y (ξ t ω)) (innerSL ℝ (g t ω)) V (x t ω))
    (hstep : ∀ t < n, ∀ ω,
      x (t + 1) ω ∈ V ∧ IsMinOn (fun b ↦ ‖b - (x t ω - η • g t ω)‖) V (x (t + 1) ω))
    (hfx : ∀ t < n, Integrable (fun ω ↦ f (x t ω) (ξ t ω)) P)
    (hfu : ∀ t < n, Integrable (fun ω ↦ f u (ξ t ω)) P)
    (hg_int : ∀ t < n, Integrable (fun ω ↦ ‖g t ω‖ ^ 2) P)
    (hgG : ∀ t < n, ∫ ω, ‖g t ω‖ ^ 2 ∂P ≤ G ^ 2)
    (hint : Integrable (fun ω ↦ F ((n : ℝ)⁻¹ • ∑ t ∈ range n, x t ω)) P) :
    ∫ ω, F ((n : ℝ)⁻¹ • ∑ t ∈ range n, x t ω) ∂P ≤
      F u + (‖u - x₀‖ ^ 2 / η + η * n * G ^ 2) / (2 * n) := by
  have h_avg (ω : Ω) : (range n).centerMass (fun _ ↦ (1 : ℝ)) (fun t ↦ x t ω) =
      (n : ℝ)⁻¹ • ∑ t ∈ range n, x t ω := by
    simp [centerMass]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h := integral_apply_centerMass_le_add_integral_regret_div hf hFV (α := fun _ ↦ 1)
    (fun _ _ ↦ zero_le_one) (by simpa using hn') x ξ hκ hF
    (fun t ht ↦ ae_of_all _ (mem_of_step (fun ω ↦ hx₀ ω ▸ hx₀V) (fun t ht ω ↦ (hstep t ht ω).1)
      ht)) hu hfx hfu (by simpa only [h_avg] using hint)
  simp only [h_avg, one_mul, sum_const, card_range, nsmul_eq_mul, mul_one] at h
  -- the regret at every `ω` is at most `‖u - x₀‖ ^ 2 / (2 η) + η / 2 * ∑ t < n, ‖g t ω‖ ^ 2`
  have h_reg (ω : Ω) : regret (fun t y ↦ f y (ξ t ω)) (fun t ↦ x t ω) u n ≤
      ‖u - x₀‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ range n, ‖g t ω‖ ^ 2 := by
    have := onlineSubgradientDescent_regret_le_norm_sub_sq_div hFV.1 hη (fun t y ↦ f y (ξ t ω))
      (fun t ↦ g t ω) (fun t ↦ x t ω) (fun t ht ↦ hg t ht ω) (fun t ht ↦ hstep t ht ω) hu
    rw [hx₀ ω] at this
    have h_last : 0 ≤ ‖u - x n ω‖ ^ 2 / (2 * η) := by positivity
    rw [sub_div] at this
    linarith
  have hG := integrable_sum_norm_sq_and_integral_le hg_int hgG
  have h_int_reg := integrable_regret (P := P) (fun _ ↦ (1 : ℝ)) x (fun _ ↦ u) ξ hfx hfu
  simp only [one_mul] at h_int_reg
  -- the expected regret is at most `(‖u - x₀‖ ^ 2 / η + η n G ^ 2) / 2`
  have h_reg_int : ∫ ω, regret (fun t y ↦ f y (ξ t ω)) (fun t ↦ x t ω) u n ∂P ≤
      (‖u - x₀‖ ^ 2 / η + η * n * G ^ 2) / 2 := by
    have h_int_rhs : Integrable
        (fun ω ↦ ‖u - x₀‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ range n, ‖g t ω‖ ^ 2) P :=
      (integrable_const _).add (hG.1.const_mul _)
    refine (integral_mono h_int_reg h_int_rhs h_reg).trans ?_
    rw [integral_add (integrable_const _) (hG.1.const_mul _), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    calc ‖u - x₀‖ ^ 2 / (2 * η) + η / 2 * ∫ ω, ∑ t ∈ range n, ‖g t ω‖ ^ 2 ∂P
        ≤ ‖u - x₀‖ ^ 2 / (2 * η) + η / 2 * (n * G ^ 2) := by
          gcongr
          exact hG.2
      _ = (‖u - x₀‖ ^ 2 / η + η * n * G ^ 2) / 2 := by field_simp
  refine h.trans ?_
  rw [← div_div]
  gcongr

/-- **The subgradient inequality of the risk, in expectation.** Let the datum `Y` have conditional
law `κ X` given the play `X`, of risk `F` on `V`, where `F` is `μ`-strongly convex on `V`, and let
`g ω` be a subgradient within `V` at `X ω ∈ V` of the convex loss `f · (Y ω)`. Then for `u ∈ V`,
`𝔼[f X Y] + 𝔼⟪g, u - X⟫ + μ / 2 * 𝔼‖u - X‖ ^ 2 ≤ 𝔼[f u Y]`. As in
`StrongConvexOn.add_add_le_of_hasSubgradientWithinAt`, the subgradient inequality at
`(1 - s) • X + s • u` is compared with the strong convexity of `F`, here in expectation, and `s`
tends to `0`. -/
private lemma integral_add_integral_inner_add_le [IsProbabilityMeasure P] [BorelSpace E]
    {V : Set E} {f : E → Z → ℝ} (hf : Measurable (Function.uncurry f)) {F : E → ℝ} {μ : ℝ}
    (hFV : StrongConvexOn V μ F) {X g : Ω → E} {Y : Ω → Z} {κ : Kernel E Z} [IsSFiniteKernel κ]
    (hκ : HasCondDistrib Y X κ P) (hF : ∀ᵐ ω ∂P, ∀ y ∈ V, ∫ z, f y z ∂(κ (X ω)) = F y)
    (hXV : ∀ ω, X ω ∈ V) {u : E} (hu : u ∈ V) (hfV : ∀ ω, ConvexOn ℝ V fun y ↦ f y (Y ω))
    (hg : ∀ ω, HasSubgradientWithinAt (fun y ↦ f y (Y ω)) (innerSL ℝ (g ω)) V (X ω))
    (hfX : Integrable (fun ω ↦ f (X ω) (Y ω)) P) (hfu : Integrable (fun ω ↦ f u (Y ω)) P)
    (hgX : Integrable (fun ω ↦ ⟪g ω, u - X ω⟫) P) (hXu : Integrable (fun ω ↦ ‖u - X ω‖ ^ 2) P) :
    ∫ ω, f (X ω) (Y ω) ∂P + ∫ ω, ⟪g ω, u - X ω⟫ ∂P + μ / 2 * ∫ ω, ‖u - X ω‖ ^ 2 ∂P ≤
      ∫ ω, f u (Y ω) ∂P := by
  -- the risks at `X` and at `u` are the means of the losses
  have hX := integrable_and_integral_eq_of_risk_comp hκ measurable_id' hf
    (hF.mono fun ω h ↦ h _ (hXV ω)) hfX
  have hU := integrable_and_integral_eq_of_risk_comp hκ (measurable_const (a := u)) hf
    (hF.mono fun ω h ↦ h _ hu) hfu
  rw [integral_const, probReal_univ, one_smul] at hU
  rw [hU.2]
  have key : ∀ s ∈ Set.Ioo (0 : ℝ) 1, ∫ ω, f (X ω) (Y ω) ∂P + ∫ ω, ⟪g ω, u - X ω⟫ ∂P +
      (1 - s) * (μ / 2 * ∫ ω, ‖u - X ω‖ ^ 2 ∂P) ≤ F u := by
    intro s hs
    have hab : 1 - s + s = 1 := sub_add_cancel 1 s
    have hφ : Measurable fun y : E ↦ (1 - s) • y + s • u :=
      (by fun_prop : Continuous fun y : E ↦ (1 - s) • y + s • u).measurable
    have hφV (ω : Ω) : (1 - s) • X ω + s • u ∈ V :=
      hFV.1 (hXV ω) hu (sub_nonneg.2 hs.2.le) hs.1.le hab
    -- the subgradient inequality and the convexity of the loss at `(1 - s) • X + s • u`
    have h_lo (ω : Ω) :
        f (X ω) (Y ω) + s * ⟪g ω, u - X ω⟫ ≤ f ((1 - s) • X ω + s • u) (Y ω) := by
      have h := hasSubgradientWithinAt_iff_le.1 (hg ω) _ (hφV ω)
      rw [show (1 - s) • X ω + s • u - X ω = s • (u - X ω) by module, map_smul, smul_eq_mul,
        innerSL_apply_apply] at h
      exact h
    have h_hi (ω : Ω) : f ((1 - s) • X ω + s • u) (Y ω) ≤
        (1 - s) * f (X ω) (Y ω) + s * f u (Y ω) := by
      simpa only [smul_eq_mul] using
        (hfV ω).2 (hXV ω) hu (sub_nonneg.2 hs.2.le) hs.1.le hab
    have h_int : Integrable (fun ω ↦ f ((1 - s) • X ω + s • u) (Y ω)) P :=
      integrable_of_le_of_le
        ((hf.comp ((hφ.comp measurable_fst).prodMk measurable_snd)).comp_aemeasurable
          hκ.aemeasurable).aestronglyMeasurable
        (ae_of_all _ h_lo) (ae_of_all _ h_hi) (hfX.add (hgX.const_mul s))
        ((hfX.const_mul _).add (hfu.const_mul _))
    have hφX := integrable_and_integral_eq_of_risk_comp hκ hφ hf
      (hF.mono fun ω h ↦ h _ (hφV ω)) h_int
    -- the strong convexity of the risk at `(1 - s) • X + s • u`
    have h_conv (ω : Ω) : F ((1 - s) • X ω + s • u) ≤
        (1 - s) * F (X ω) + s * F u - (1 - s) * s * (μ / 2 * ‖u - X ω‖ ^ 2) := by
      have h := hFV.2 (hXV ω) hu (sub_nonneg.2 hs.2.le) hs.1.le hab
      simp only [smul_eq_mul, norm_sub_rev (X ω) u] at h
      exact h
    have h_int₁ : Integrable (fun ω ↦ (1 - s) * F (X ω) + s * F u) P :=
      (hX.1.const_mul _).add (integrable_const _)
    have h_int₂ : Integrable (fun ω ↦ (1 - s) * s * (μ / 2 * ‖u - X ω‖ ^ 2)) P :=
      (hXu.const_mul _).const_mul _
    have h1 : ∫ ω, (f (X ω) (Y ω) + s * ⟪g ω, u - X ω⟫) ∂P ≤
        ∫ ω, f ((1 - s) • X ω + s • u) (Y ω) ∂P :=
      integral_mono (hfX.add (hgX.const_mul s)) h_int h_lo
    have h2 : ∫ ω, F ((1 - s) • X ω + s • u) ∂P ≤
        ∫ ω, ((1 - s) * F (X ω) + s * F u - (1 - s) * s * (μ / 2 * ‖u - X ω‖ ^ 2)) ∂P :=
      integral_mono hφX.1 (h_int₁.sub h_int₂) h_conv
    rw [integral_add hfX (hgX.const_mul s), integral_const_mul] at h1
    rw [integral_sub h_int₁ h_int₂, integral_add (hX.1.const_mul _) (integrable_const _),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const, probReal_univ, one_smul, ← hX.2] at h2
    refine le_of_mul_le_mul_left ?_ hs.1
    linarith [hφX.2]
  -- let `s` tend to `0`
  have hlim : Filter.Tendsto (fun s : ℝ ↦ ∫ ω, f (X ω) (Y ω) ∂P + ∫ ω, ⟪g ω, u - X ω⟫ ∂P +
      (1 - s) * (μ / 2 * ∫ ω, ‖u - X ω‖ ^ 2 ∂P)) (𝓝[>] 0)
      (𝓝 (∫ ω, f (X ω) (Y ω) ∂P + ∫ ω, ⟪g ω, u - X ω⟫ ∂P +
        (1 - 0) * (μ / 2 * ∫ ω, ‖u - X ω‖ ^ 2 ∂P))) :=
    ((continuous_const.add ((continuous_const.sub continuous_id).mul continuous_const)).tendsto
      0).mono_left nhdsWithin_le_nhds
  have h := le_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) key)
  rwa [sub_zero, one_mul] at h

/-- **Stochastic subgradient descent on a strongly convex risk** [Ora, Example 4.12]. Let the risk
`F` be `μ`-strongly convex on a set `V`, with `μ > 0`, and let `u ∈ V`. Let `x 0 ∈ V`, and let each
`x (t + 1)` be a point of `V` nearest to `x t - (2 / ((t + 2) μ)) • g t`, where `g t` is a
subgradient of the convex loss `f · (ξ t)` within `V` at `x t`, with second moment
`𝔼 ‖g t‖ ^ 2 ≤ G ^ 2`. Let the datum `ξ t` have conditional law `κ t (x t)` given the play, of risk
`F` on `V`, for `t < n`, with `n > 0`. Then the average of the plays with the weights `t + 1` has
expected risk
`𝔼[F (centerMass (t + 1) x)] ≤ F u + 2 G ^ 2 / (μ (n + 1))`.
The losses need not be strongly convex. In expectation, the stochastic subgradients satisfy the
subgradient inequality of the strongly convex risk, so the expected regret is at most that of the
paraboloids `f (x t) (ξ t) + ⟪g t, · - x t⟫ + μ / 2 * ‖· - x t‖ ^ 2`, which
`onlineSubgradientDescent_regret_add_one_mul_le_sum_norm_sq_div` bounds. The weights remove the
logarithmic factor of uniform averaging. -/
theorem integral_apply_centerMass_le_of_onlineSubgradientDescent_of_strongConvexOn
    [IsProbabilityMeasure P] [BorelSpace E] {V : Set E} {f : E → Z → ℝ}
    (hf : Measurable (Function.uncurry f)) {F : E → ℝ} {μ G : ℝ} (hFV : StrongConvexOn V μ F)
    (hμ : 0 < μ) (hn : 0 < n) (x g : ℕ → Ω → E) (ξ : ℕ → Ω → Z) {κ : ℕ → Kernel E Z}
    [∀ t, IsSFiniteKernel (κ t)]
    (hκ : ∀ t < n, HasCondDistrib (ξ t) (x t) (κ t) P)
    (hF : ∀ t < n, ∀ᵐ ω ∂P, ∀ y ∈ V, ∫ z, f y z ∂(κ t (x t ω)) = F y) {u : E}
    (hx₀ : ∀ ω, x 0 ω ∈ V) (hu : u ∈ V) (hfV : ∀ t < n, ∀ ω, ConvexOn ℝ V fun y ↦ f y (ξ t ω))
    (hg : ∀ t < n, ∀ ω,
      HasSubgradientWithinAt (fun y ↦ f y (ξ t ω)) (innerSL ℝ (g t ω)) V (x t ω))
    (hstep : ∀ t < n, ∀ ω, x (t + 1) ω ∈ V ∧
      IsMinOn (fun b ↦ ‖b - (x t ω - (2 / (((t : ℝ) + 2) * μ)) • g t ω)‖) V (x (t + 1) ω))
    (hfx : ∀ t < n, Integrable (fun ω ↦ f (x t ω) (ξ t ω)) P)
    (hfu : ∀ t < n, Integrable (fun ω ↦ f u (ξ t ω)) P)
    (hgx : ∀ t < n, Integrable (fun ω ↦ ⟪g t ω, u - x t ω⟫) P)
    (hxu : ∀ t < n, Integrable (fun ω ↦ ‖u - x t ω‖ ^ 2) P)
    (hg_int : ∀ t < n, Integrable (fun ω ↦ ‖g t ω‖ ^ 2) P)
    (hgG : ∀ t < n, ∫ ω, ‖g t ω‖ ^ 2 ∂P ≤ G ^ 2)
    (hint : Integrable
      (fun ω ↦ F ((range n).centerMass (fun t ↦ (t : ℝ) + 1) fun t ↦ x t ω)) P) :
    ∫ ω, F ((range n).centerMass (fun t ↦ (t : ℝ) + 1) fun t ↦ x t ω) ∂P ≤
      F u + 2 * G ^ 2 / (μ * (n + 1)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hA_eq : ∑ t ∈ range n, ((t : ℝ) + 1) = n * (n + 1) / 2 := by
    linarith [two_mul_sum_range_cast_add_one (α := ℝ) n]
  have hA : 0 < ∑ t ∈ range n, ((t : ℝ) + 1) := by
    rw [hA_eq]
    positivity
  have hxV {t : ℕ} (ht : t < n) := mem_of_step hx₀ (fun t ht ω ↦ (hstep t ht ω).1) ht
  have h := integral_apply_centerMass_le_add_integral_regret_div hf
    (strongConvexOn_zero.1 (hFV.mono hμ.le)) (fun t _ ↦ by positivity) hA x ξ hκ hF
    (fun t ht ↦ ae_of_all _ (hxV ht)) hu hfx hfu hint
  refine h.trans ?_
  gcongr F u + ?_
  have h_int_e {t : ℕ} (ht : t < n) :
      Integrable (fun ω ↦ -(⟪g t ω, u - x t ω⟫ + μ / 2 * ‖u - x t ω‖ ^ 2)) P :=
    ((hgx t ht).add ((hxu t ht).const_mul _)).neg
  -- the paraboloids `f (x t) (ξ t) + ⟪g t, · - x t⟫ + μ / 2 * ‖· - x t‖ ^ 2` have weighted regret
  -- at most `∑ t < n, ‖g t ω‖ ^ 2 / μ` at every `ω`
  have h_reg (ω : Ω) :
      ∑ t ∈ range n, ((t : ℝ) + 1) * -(⟪g t ω, u - x t ω⟫ + μ / 2 * ‖u - x t ω‖ ^ 2) ≤
        (∑ t ∈ range n, ‖g t ω‖ ^ 2) / μ := by
    have h_osd := onlineSubgradientDescent_regret_add_one_mul_le_sum_norm_sq_div hFV.1
      (fun t v ↦ f (x t ω) (ξ t ω) + ⟪g t ω, v - x t ω⟫ + μ / 2 * ‖v - x t ω‖ ^ 2)
      (fun t ↦ g t ω) (fun t ↦ x t ω) hμ (fun t _ v _ ↦ by simp) (fun t ht ↦ hstep t ht ω) hu
    rw [regret_def, ← sum_div] at h_osd
    refine le_of_eq_of_le (sum_congr rfl fun t _ ↦ ?_) h_osd
    simp only [sub_self, inner_zero_right, norm_zero]
    ring
  have hG := integrable_sum_norm_sq_and_integral_le hg_int hgG
  -- the expected regret is at most `n G ^ 2 / μ`
  have h_reg_int : ∫ ω, regret (fun t y ↦ ((t : ℝ) + 1) * f y (ξ t ω)) (fun t ↦ x t ω) u n ∂P ≤
      n * G ^ 2 / μ := by
    calc ∫ ω, regret (fun t y ↦ ((t : ℝ) + 1) * f y (ξ t ω)) (fun t ↦ x t ω) u n ∂P
        = ∑ t ∈ range n, ((t : ℝ) + 1) * (∫ ω, f (x t ω) (ξ t ω) ∂P - ∫ ω, f u (ξ t ω) ∂P) :=
          integral_regret_eq_sum_mul_integral_sub_integral _ x (fun _ ↦ u) ξ hfx hfu
      _ ≤ ∑ t ∈ range n, ((t : ℝ) + 1) *
          ∫ ω, -(⟪g t ω, u - x t ω⟫ + μ / 2 * ‖u - x t ω‖ ^ 2) ∂P := by
          refine sum_le_sum fun t ht ↦ mul_le_mul_of_nonneg_left ?_ (by positivity)
          have ht' := mem_range.mp ht
          have := integral_add_integral_inner_add_le hf hFV (hκ t ht') (hF t ht') (hxV ht') hu
            (hfV t ht') (hg t ht') (hfx t ht') (hfu t ht') (hgx t ht') (hxu t ht')
          rw [integral_neg, integral_add (hgx t ht') ((hxu t ht').const_mul _),
            integral_const_mul]
          linarith
      _ = ∫ ω, ∑ t ∈ range n,
          ((t : ℝ) + 1) * -(⟪g t ω, u - x t ω⟫ + μ / 2 * ‖u - x t ω‖ ^ 2) ∂P := by
          rw [integral_finsetSum _ fun t ht ↦ (h_int_e (mem_range.mp ht)).const_mul _]
          simp only [integral_const_mul]
      _ ≤ ∫ ω, (∑ t ∈ range n, ‖g t ω‖ ^ 2) / μ ∂P :=
          integral_mono (integrable_finsetSum _ fun t ht ↦ (h_int_e (mem_range.mp ht)).const_mul _)
            (hG.1.div_const _) h_reg
      _ ≤ n * G ^ 2 / μ := by
          rw [integral_div]
          gcongr
          exact hG.2
  rw [hA_eq]
  calc (∫ ω, regret (fun t y ↦ ((t : ℝ) + 1) * f y (ξ t ω)) (fun t ↦ x t ω) u n ∂P) /
        (n * (n + 1) / 2)
      ≤ n * G ^ 2 / μ / (n * (n + 1) / 2) := by gcongr
    _ = 2 * G ^ 2 / (μ * (n + 1)) := by field_simp

end InnerProductSpace

end LMLExplore.OnlineLearning
