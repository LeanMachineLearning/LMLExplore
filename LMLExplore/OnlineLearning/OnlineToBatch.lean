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
* `integral_apply_centerMass_le_of_onlineSubgradientDescent_of_strongConvex`
  [Ora, Example 4.12]: for losses `f · z` that are `μ`-strongly convex, the weights `t + 1` and the
  learning rates `2 / ((t + 2) μ)` give the expected risk `F u + 2 G ^ 2 / (μ (n + 1))`, with no
  logarithmic factor.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped RealInnerProductSpace

namespace LMLExplore.OnlineLearning

variable {Ω E Z : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {mZ : MeasurableSpace Z}
  {mE : MeasurableSpace E} {n : ℕ}

/-- One round of the conversion: if `Y` has conditional law `κ` given `X`, and the risk at
`φ (X ω)` of the conditional law `κ (X ω)` is `F (φ (X ω))`, then `F (φ X)` is integrable, with
the mean of `f (φ X) Y`. -/
private lemma integrable_and_integral_eq_of_hasCondDistrib [SFinite P] {𝓧 : Type*}
    {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧} {Y : Ω → Z} {κ : Kernel 𝓧 Z} [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P)
    {φ : 𝓧 → E} (hφ : Measurable φ) {f : E → Z → ℝ} (hf : Measurable (Function.uncurry f))
    {F : E → ℝ} (hF : ∀ᵐ ω ∂P, ∫ z, f (φ (X ω)) z ∂(κ (X ω)) = F (φ (X ω)))
    (hint : Integrable (fun ω ↦ f (φ (X ω)) (Y ω)) P) :
    Integrable (fun ω ↦ F (φ (X ω))) P ∧
      ∫ ω, f (φ (X ω)) (Y ω) ∂P = ∫ ω, F (φ (X ω)) ∂P := by
  have hg_meas : Measurable fun p : 𝓧 × Z ↦ f (φ p.1) p.2 :=
    hf.comp ((hφ.comp measurable_fst).prodMk measurable_snd)
  have hg : Integrable (fun p : 𝓧 × Z ↦ f (φ p.1) p.2) (P.map X ⊗ₘ κ) := by
    rw [← h.map_eq, integrable_map_measure hg_meas.aestronglyMeasurable h.aemeasurable]
    exact hint
  refine ⟨(hg.integral_measure_compProd.comp_aemeasurable h.aemeasurable_fst).congr hF, ?_⟩
  rw [h.integral_comp_prodMk_eq_integral_integral hg]
  exact integral_congr_ae hF

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
  ⟨integrable_and_integral_eq_of_hasCondDistrib (hκ t ht) measurable_fst hf
      (((hF t ht).and (hxV t ht)).mono fun _ hω ↦ hω.1 _ hω.2) (hfx t ht),
    integrable_and_integral_eq_of_hasCondDistrib (hκ t ht) measurable_snd hf
      (((hF t ht).and huV).mono fun _ hω ↦ hω.1 _ hω.2) (hfu t ht)⟩

/-- The plays of projected online subgradient descent from a point of `V` stay in `V`. -/
private lemma mem_of_step {V : Set E} {x : ℕ → Ω → E} (hx₀ : ∀ ω, x 0 ω ∈ V)
    (hstep : ∀ t < n, ∀ ω, x (t + 1) ω ∈ V) {t : ℕ} (ht : t < n) (ω : Ω) : x t ω ∈ V := by
  rcases t with _ | t
  · exact hx₀ ω
  · exact hstep t (by omega) ω

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
  simp only [regret_def]
  rw [integral_finsetSum (f := fun t ω ↦ α t * f (x t ω) (ξ t ω) - α t * f (u ω) (ξ t ω)) _
    fun t ht ↦
      ((hfx t (mem_range.mp ht)).const_mul _).sub ((hfu t (mem_range.mp ht)).const_mul _)]
  refine sum_congr rfl fun t ht ↦ ?_
  have ht' := mem_range.mp ht
  have h := integrable_and_integral_eq_of_risk hf hκ hF hxV huV hfx hfu ht'
  rw [integral_sub ((hfx t ht').const_mul _) ((hfu t ht').const_mul _), integral_const_mul,
    integral_const_mul, h.1.2, h.2.2, mul_sub]

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
    (fun t ht ↦ (hκ t ht).prod_right measurable_const) hF hxV (ae_of_all _ fun _ ↦ hu) hfx hfu
    hint
  simpa using h

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

/-- **Stochastic subgradient descent with a constant learning rate** [Ora, Theorem 3.1 with
Theorem 2.13]. Let `F` be convex on a convex set `V`, bounded or not, and let `u ∈ V`. Let the
plays start at `x 0 = x₀ ∈ V` and let each `x (t + 1)` be a point of `V` nearest to
`x t - η • g t`, where `g t` is a subgradient of `f · (ξ t)` within `V` at `x t`, with second moment
`𝔼 ‖g t‖ ^ 2 ≤ G ^ 2`. Let the datum `ξ t` have conditional law `κ t (x t)` given the play, of risk
`F` on `V`, for `t < n`, with `n > 0`. Then the average play has expected risk
`𝔼[F ((1 / n) ∑ t < n, x t)] ≤ F u + (‖u - x₀‖ ^ 2 / η + η n G ^ 2) / (2 n)`. -/
theorem integral_apply_smul_sum_le_of_onlineSubgradientDescent [IsProbabilityMeasure P]
    {V : Set E} (hV : Convex ℝ V)
    {f : E → Z → ℝ} (hf : Measurable (Function.uncurry f)) {F : E → ℝ} (hFV : ConvexOn ℝ V F)
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
    have := onlineSubgradientDescent_regret_le_norm_sub_sq_div hV hη (fun t y ↦ f y (ξ t ω))
      (fun t ↦ g t ω) (fun t ↦ x t ω) (fun t ht ↦ hg t ht ω) (fun t ht ↦ hstep t ht ω) hu
    rw [hx₀ ω] at this
    have h_last : 0 ≤ ‖u - x n ω‖ ^ 2 / (2 * η) := by positivity
    rw [sub_div] at this
    linarith
  have h_int_g : Integrable (fun ω ↦ ∑ t ∈ range n, ‖g t ω‖ ^ 2) P :=
    integrable_finsetSum _ fun t ht ↦ hg_int t (mem_range.mp ht)
  have h_int_reg := integrable_regret (P := P) (fun _ ↦ (1 : ℝ)) x (fun _ ↦ u) ξ hfx hfu
  simp only [one_mul] at h_int_reg
  -- the expected regret is at most `(‖u - x₀‖ ^ 2 / η + η n G ^ 2) / 2`
  have h_reg_int : ∫ ω, regret (fun t y ↦ f y (ξ t ω)) (fun t ↦ x t ω) u n ∂P ≤
      (‖u - x₀‖ ^ 2 / η + η * n * G ^ 2) / 2 := by
    have h_int_rhs : Integrable
        (fun ω ↦ ‖u - x₀‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ range n, ‖g t ω‖ ^ 2) P :=
      (integrable_const _).add (h_int_g.const_mul _)
    refine (integral_mono h_int_reg h_int_rhs h_reg).trans ?_
    rw [integral_add (integrable_const _) (h_int_g.const_mul _), integral_const_mul,
      integral_finsetSum _ fun t ht ↦ hg_int t (mem_range.mp ht)]
    simp only [integral_const, probReal_univ, one_smul]
    have h_sum : ∑ t ∈ range n, ∫ ω, ‖g t ω‖ ^ 2 ∂P ≤ n * G ^ 2 := by
      simpa using sum_le_sum fun t ht ↦ hgG t (mem_range.mp ht)
    calc ‖u - x₀‖ ^ 2 / (2 * η) + η / 2 * ∑ t ∈ range n, ∫ ω, ‖g t ω‖ ^ 2 ∂P
        ≤ ‖u - x₀‖ ^ 2 / (2 * η) + η / 2 * (n * G ^ 2) := by gcongr
      _ = (‖u - x₀‖ ^ 2 / η + η * n * G ^ 2) / 2 := by field_simp
  refine h.trans ?_
  rw [← div_div]
  gcongr

/-- The partial sums of the weights `t + 1`: `∑ s < t, (s + 1) = t (t + 1) / 2`. -/
private lemma sum_range_cast_add_one (t : ℕ) :
    ∑ s ∈ range t, ((s : ℝ) + 1) = t * (t + 1) / 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- **Stochastic subgradient descent on strongly convex losses** [Ora, Example 4.12]. Let `F` be
convex on a convex set `V` and let `u ∈ V`. Let `x 0 ∈ V`, and let each `x (t + 1)` be a point of
`V` nearest to `x t - (2 / ((t + 2) μ)) • g t`, where `g t` has second moment
`𝔼 ‖g t‖ ^ 2 ≤ G ^ 2` and the loss `f · (ξ t)` lies above the paraboloid
`f (x t) (ξ t) + ⟪g t, · - x t⟫ + μ / 2 * ‖· - x t‖ ^ 2` on `V`, with `μ > 0`, as when `f · z` is
`μ`-strongly convex on `V` with subgradient `g t` at `x t`. Let the datum `ξ t` have conditional
law `κ t (x t)` given the play, of risk `F` on `V`, for `t < n`, with `n > 0`. Then the average of
the plays with the weights `t + 1` has expected risk
`𝔼[F (centerMass (t + 1) x)] ≤ F u + 2 G ^ 2 / (μ (n + 1))`.
This is online subgradient descent on the losses `(t + 1) * f · (ξ t)`, which are
`(t + 1) μ`-strongly convex at the plays, with the learning rates of [Ora, Theorem 4.7]; the
weights remove the logarithmic factor of uniform averaging. -/
theorem integral_apply_centerMass_le_of_onlineSubgradientDescent_of_strongConvex
    [IsProbabilityMeasure P] {V : Set E} (hV : Convex ℝ V) {f : E → Z → ℝ}
    (hf : Measurable (Function.uncurry f)) {F : E → ℝ} (hFV : ConvexOn ℝ V F) {μ G : ℝ}
    (hμ : 0 < μ) (hn : 0 < n) (x g : ℕ → Ω → E) (ξ : ℕ → Ω → Z) {κ : ℕ → Kernel E Z}
    [∀ t, IsSFiniteKernel (κ t)]
    (hκ : ∀ t < n, HasCondDistrib (ξ t) (x t) (κ t) P)
    (hF : ∀ t < n, ∀ᵐ ω ∂P, ∀ y ∈ V, ∫ z, f y z ∂(κ t (x t ω)) = F y) {u : E}
    (hx₀ : ∀ ω, x 0 ω ∈ V) (hu : u ∈ V)
    (hfμ : ∀ t < n, ∀ ω, ∀ v ∈ V,
      f (x t ω) (ξ t ω) + ⟪g t ω, v - x t ω⟫ + μ / 2 * ‖v - x t ω‖ ^ 2 ≤ f v (ξ t ω))
    (hstep : ∀ t < n, ∀ ω, x (t + 1) ω ∈ V ∧
      IsMinOn (fun b ↦ ‖b - (x t ω - (2 / (((t : ℝ) + 2) * μ)) • g t ω)‖) V (x (t + 1) ω))
    (hfx : ∀ t < n, Integrable (fun ω ↦ f (x t ω) (ξ t ω)) P)
    (hfu : ∀ t < n, Integrable (fun ω ↦ f u (ξ t ω)) P)
    (hg_int : ∀ t < n, Integrable (fun ω ↦ ‖g t ω‖ ^ 2) P)
    (hgG : ∀ t < n, ∫ ω, ‖g t ω‖ ^ 2 ∂P ≤ G ^ 2)
    (hint : Integrable
      (fun ω ↦ F ((range n).centerMass (fun t ↦ (t : ℝ) + 1) fun t ↦ x t ω)) P) :
    ∫ ω, F ((range n).centerMass (fun t ↦ (t : ℝ) + 1) fun t ↦ x t ω) ∂P ≤
      F u + 2 * G ^ 2 / (μ * (n + 1)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hA : 0 < ∑ t ∈ range n, ((t : ℝ) + 1) := by
    rw [sum_range_cast_add_one]
    positivity
  have h := integral_apply_centerMass_le_add_integral_regret_div hf hFV
    (fun t _ ↦ by positivity) hA x ξ hκ hF
    (fun t ht ↦ ae_of_all _ (mem_of_step hx₀ (fun t ht ω ↦ (hstep t ht ω).1) ht)) hu hfx hfu hint
  refine h.trans ?_
  gcongr F u + ?_
  -- the partial sums of the moduli `(s + 1) μ` of the weighted losses
  have h_sum (t : ℕ) : ∑ s ∈ range (t + 1), ((s : ℝ) + 1) * μ = (t + 1) * (t + 2) / 2 * μ := by
    rw [← sum_mul, sum_range_cast_add_one]
    push_cast
    ring
  -- the regret at every `ω` is at most `∑ t < n, ‖g t ω‖ ^ 2 / μ`
  have h_reg (ω : Ω) : regret (fun t y ↦ ((t : ℝ) + 1) * f y (ξ t ω)) (fun t ↦ x t ω) u n ≤
      ∑ t ∈ range n, ‖g t ω‖ ^ 2 / μ := by
    have h_osd := onlineSubgradientDescent_regret_le_sum_norm_sq_div hV
      (fun t y ↦ ((t : ℝ) + 1) * f y (ξ t ω)) (fun t ↦ ((t : ℝ) + 1) • g t ω) (fun t ↦ x t ω)
      (μ := fun t ↦ ((t : ℝ) + 1) * μ) (fun t _ ↦ by rw [h_sum]; positivity)
      (fun t ht v hv ↦ by
        have := mul_le_mul_of_nonneg_left (hfμ t ht ω v hv) (by positivity : (0 : ℝ) ≤ t + 1)
        rw [real_inner_smul_left]
        linarith)
      (fun t ht ↦ by
        have h_rate : (∑ s ∈ range (t + 1), ((s : ℝ) + 1) * μ)⁻¹ • ((t : ℝ) + 1) • g t ω =
            (2 / (((t : ℝ) + 2) * μ)) • g t ω := by
          rw [h_sum, smul_smul]
          congr 1
          field_simp
        rw [h_rate]
        exact hstep t ht ω)
      hu
    refine h_osd.trans (sum_le_sum fun t _ ↦ ?_)
    rw [h_sum, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ t + 1)]
    rw [div_le_div_iff₀ (by positivity) hμ]
    have h0 : 0 ≤ ‖g t ω‖ ^ 2 * μ * ((t : ℝ) + 1) := by positivity
    nlinarith [h0]
  have h_int_g : Integrable (fun ω ↦ ∑ t ∈ range n, ‖g t ω‖ ^ 2 / μ) P :=
    integrable_finsetSum _ fun t ht ↦ (hg_int t (mem_range.mp ht)).div_const _
  have h_int_reg := integrable_regret (P := P) (fun t ↦ (t : ℝ) + 1) x (fun _ ↦ u) ξ hfx hfu
  have h_reg_int : ∫ ω, regret (fun t y ↦ ((t : ℝ) + 1) * f y (ξ t ω)) (fun t ↦ x t ω) u n ∂P ≤
      n * G ^ 2 / μ := by
    refine (integral_mono h_int_reg h_int_g h_reg).trans ?_
    rw [integral_finsetSum _ fun t ht ↦ (hg_int t (mem_range.mp ht)).div_const _]
    simp only [integral_div]
    rw [← sum_div]
    gcongr
    simpa using sum_le_sum fun t ht ↦ hgG t (mem_range.mp ht)
  rw [sum_range_cast_add_one]
  calc (∫ ω, regret (fun t y ↦ ((t : ℝ) + 1) * f y (ξ t ω)) (fun t ↦ x t ω) u n ∂P) /
        (n * (n + 1) / 2)
      ≤ n * G ^ 2 / μ / (n * (n + 1) / 2) := by gcongr
    _ = 2 * G ^ 2 / (μ * (n + 1)) := by field_simp

end InnerProductSpace

end LMLExplore.OnlineLearning
