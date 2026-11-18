/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.ReinforcementLearning.TemporalDifference.ProjectedBellman
public import Mathlib.Probability.Process.Filtration
import TauCeti.MeasureTheory.Integral.Bind

/-!
# The TD(0) direction of one observed transition

TD(0) with linear features `φ : 𝓢 → E` updates its parameter along one observed transition at a
time, in the direction `d θ (s, s') = (R (s, s') + γ ⟪φ s', θ⟫ - ⟪φ s, θ⟫) φ s` of a transition
`(s, s')` with reward `R (s, s')`. This file develops the deterministic properties of this
direction, and its moments for a transition drawn from `ν ⊗ₘ P`: the state from an invariant law
`ν` of the Markov kernel `P`, and the next state from `P`. The mean of `d θ` is then the
mean-path TD update `g θ` for the mean reward `s ↦ ∫ R (s, s') d(P s)`, and one step along `d θ`
contracts the squared distance to a zero `θ*` of `g` in expectation, up to the noise
`σ² = 𝔼 ‖d θ*‖²`. These are the per-step facts behind the finite-time analyses of TD(0) in
[BRS18].

## Main definitions

* `LMLExplore.ReinforcementLearning.tdUpdate φ R γ θ o`: the TD(0) direction `d θ o`.

## Main statements

* `LMLExplore.ReinforcementLearning.tdUpdate_sub`: `d` is affine in the parameter.
* `LMLExplore.ReinforcementLearning.measurable_add_smul_tdUpdate`: the TD(0) step
  `(θ, o) ↦ θ + a d θ o` is measurable.
* `LMLExplore.ReinforcementLearning.measurable_tdUpdate_iterate`: the TD(0) iterates are adapted
  to a filtration to which the initial parameter and the observations are adapted.
* `LMLExplore.ReinforcementLearning.norm_tdUpdate_le`: `‖d θ o‖ ≤ |R o| + (1 + γ) ‖θ‖` for
  features with `‖φ s‖ ≤ 1`.
* `LMLExplore.ReinforcementLearning.integral_tdUpdate`: `𝔼 d θ = g θ` for transitions
  `(s, s') ∼ ν ⊗ₘ P`.
* `LMLExplore.ReinforcementLearning.integral_norm_tdUpdate_sq_le`: the second moment
  `𝔼 ‖d θ‖² ≤ 2 𝔼 ‖d θ'‖² + 8 ‖⟪φ, θ' - θ⟫‖²_ν` [BRS18, Lemma 5].
* `LMLExplore.ReinforcementLearning.integral_norm_sub_add_smul_tdUpdate_sq_le`: one step from a
  fixed parameter in expectation,
  `𝔼 ‖θ* - (θ + α d θ)‖² ≤ ‖θ* - θ‖² - α (2 (1 - γ) - 8 α) ‖⟪φ, θ* - θ⟫‖²_ν + 2 α² σ²`.

## References

* [J. Bhandari, D. Russo and R. Singal, *A finite time analysis of temporal difference learning
  with linear function approximation*, 2018][BRS18], §7
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace

namespace LMLExplore.ReinforcementLearning

variable {𝓢 E : Type*} {m𝓢 : MeasurableSpace 𝓢} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {φ : 𝓢 → E} {R : 𝓢 × 𝓢 → ℝ} {γ : ℝ≥0}

/-- The **TD(0) direction** `(R (s, s') + γ ⟪φ s', θ⟫ - ⟪φ s, θ⟫) φ s` of linear
temporal-difference learning with features `φ`, at the parameter `θ` and for an observed
transition `o = (s, s')` with reward `R (s, s')`: the negative half-gradient in `θ` of the squared
sample Bellman error `(R (s, s') + γ ⟪φ s', θ⟫ - ⟪φ s, θ⟫)²`, with the target held fixed. -/
noncomputable def tdUpdate (φ : 𝓢 → E) (R : 𝓢 × 𝓢 → ℝ) (γ : ℝ≥0) (θ : E) (o : 𝓢 × 𝓢) : E :=
  (R o + γ * ⟪φ o.2, θ⟫_ℝ - ⟪φ o.1, θ⟫_ℝ) • φ o.1

theorem tdUpdate_def (θ : E) (o : 𝓢 × 𝓢) :
    tdUpdate φ R γ θ o = (R o + γ * ⟪φ o.2, θ⟫_ℝ - ⟪φ o.1, θ⟫_ℝ) • φ o.1 := (rfl)

/-- The TD(0) direction of a transition is continuous in the parameter. -/
theorem continuous_tdUpdate (o : 𝓢 × 𝓢) : Continuous fun θ ↦ tdUpdate φ R γ θ o := by
  simp only [tdUpdate_def]
  fun_prop

/-- The TD(0) direction is affine in the parameter:
`d θ o - d θ' o = (γ ⟪φ s', θ - θ'⟫ - ⟪φ s, θ - θ'⟫) φ s`. -/
theorem tdUpdate_sub (θ θ' : E) (o : 𝓢 × 𝓢) :
    tdUpdate φ R γ θ o - tdUpdate φ R γ θ' o =
      (γ * ⟪φ o.2, θ - θ'⟫_ℝ - ⟪φ o.1, θ - θ'⟫_ℝ) • φ o.1 := by
  simp only [tdUpdate_def, ← sub_smul, inner_sub_right]
  ring_nf

/-- For features with `‖φ s‖ ≤ 1`, `‖d θ o‖ ≤ |R o| + (1 + γ) ‖θ‖`. -/
theorem norm_tdUpdate_le (hφ : ∀ s, ‖φ s‖ ≤ 1) (θ : E) (o : 𝓢 × 𝓢) :
    ‖tdUpdate φ R γ θ o‖ ≤ |R o| + (1 + γ) * ‖θ‖ := by
  have h₁ : |⟪φ o.1, θ⟫_ℝ| ≤ ‖θ‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hφ _))
  have h₂ : |⟪φ o.2, θ⟫_ℝ| ≤ ‖θ‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hφ _))
  rw [tdUpdate_def, norm_smul, Real.norm_eq_abs]
  refine (mul_le_of_le_one_right (abs_nonneg _) (hφ _)).trans ?_
  calc |R o + γ * ⟪φ o.2, θ⟫_ℝ - ⟪φ o.1, θ⟫_ℝ|
      ≤ |R o + γ * ⟪φ o.2, θ⟫_ℝ| + |⟪φ o.1, θ⟫_ℝ| := abs_sub _ _
    _ ≤ |R o| + |γ * ⟪φ o.2, θ⟫_ℝ| + |⟪φ o.1, θ⟫_ℝ| := by grw [abs_add_le]
    _ = |R o| + γ * |⟪φ o.2, θ⟫_ℝ| + |⟪φ o.1, θ⟫_ℝ| := by
        rw [abs_mul, abs_of_nonneg γ.coe_nonneg]
    _ ≤ |R o| + (1 + γ) * ‖θ‖ := by nlinarith [γ.coe_nonneg]

/-- The TD(0) step `θ ↦ θ + a d θ o`, as a function of the pair `(θ, o)`, is measurable. -/
theorem measurable_add_smul_tdUpdate [Countable 𝓢] [MeasurableSingletonClass 𝓢]
    [MeasurableSpace E] [BorelSpace E] (a : ℝ) :
    Measurable fun p : E × (𝓢 × 𝓢) ↦ p.1 + a • tdUpdate φ R γ p.1 p.2 :=
  measurable_from_prod_countable_left fun o ↦
    (continuous_id.add ((continuous_tdUpdate o).const_smul a)).measurable

/-- **The iterates of TD(0) are adapted**: along `θ (t + 1) = θ t + α t d (θ t) (O t)`, the
iterates are adapted to a filtration `ℱ` for which `θ 0` is `ℱ 0`-measurable and each
observation `O t` is `ℱ (t + 1)`-measurable. -/
theorem measurable_tdUpdate_iterate [Countable 𝓢] [MeasurableSingletonClass 𝓢]
    [MeasurableSpace E] [BorelSpace E] {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℕ mΩ} {θ : ℕ → Ω → E} {O : ℕ → Ω → 𝓢 × 𝓢} {α : ℕ → ℝ}
    (hθ : ∀ t x, θ (t + 1) x = θ t x + α t • tdUpdate φ R γ (θ t x) (O t x))
    (hθ₀ : Measurable[ℱ 0] (θ 0)) (hO : ∀ t, Measurable[ℱ (t + 1)] (O t)) (t : ℕ) :
    Measurable[ℱ t] (θ t) := by
  induction t with
  | zero => exact hθ₀
  | succ t ih =>
    rw [funext (hθ t)]
    exact (measurable_add_smul_tdUpdate (α t)).comp
      ((ih.mono (ℱ.mono t.le_succ) le_rfl).prodMk (hO t))

variable [Finite 𝓢] [MeasurableSingletonClass 𝓢] {ν : Measure 𝓢} [IsProbabilityMeasure ν]
  {P : Kernel 𝓢 𝓢} [IsMarkovKernel P]

/-- **The mean of the TD(0) direction** is the mean-path TD update: for transitions
`(s, s') ∼ ν ⊗ₘ P`, `𝔼[d θ (s, s')] = g θ`, the mean-path TD update for the mean reward
`s ↦ ∫ R (s, s') d(P s)`. -/
theorem integral_tdUpdate [CompleteSpace E] (θ : E) :
    ∫ o, tdUpdate φ R γ θ o ∂(ν ⊗ₘ P) =
      meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ θ := by
  rw [Measure.integral_compProd Integrable.of_finite, meanTDUpdate_def]
  refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
  simp only [tdUpdate_def]
  rw [integral_smul_const, integral_sub Integrable.of_finite Integrable.of_finite,
    integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul]
  simp

/-- **The second moment of the TD(0) direction** [BRS18, Lemma 5]: if `ν` is invariant, `γ ≤ 1`
and `‖φ s‖ ≤ 1`, then for transitions `(s, s') ∼ ν ⊗ₘ P` and any parameters `θ` and `θ'`,
`𝔼 ‖d θ‖² ≤ 2 𝔼 ‖d θ'‖² + 8 ‖⟪φ, θ' - θ⟫‖²_ν`. -/
theorem integral_norm_tdUpdate_sq_le (hP : P.Invariant ν) (hφ : ∀ s, ‖φ s‖ ≤ 1) (hγ : γ ≤ 1)
    (θ θ' : E) :
    ∫ o, ‖tdUpdate φ R γ θ o‖ ^ 2 ∂(ν ⊗ₘ P) ≤
      2 * ∫ o, ‖tdUpdate φ R γ θ' o‖ ^ 2 ∂(ν ⊗ₘ P) + 8 * ∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν := by
  have hγ₁ : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ
  have hγ₀ : (0 : ℝ) ≤ γ := γ.coe_nonneg
  -- pointwise, `‖d θ‖² ≤ 2 ‖d θ'‖² + 4 ξ(s)² + 4 ξ(s')²` with `ξ = ⟪φ, θ' - θ⟫`
  have hpt : ∀ o : 𝓢 × 𝓢, ‖tdUpdate φ R γ θ o‖ ^ 2 ≤ 2 * ‖tdUpdate φ R γ θ' o‖ ^ 2 +
      (4 * ⟪φ o.1, θ' - θ⟫_ℝ ^ 2 + 4 * ⟪φ o.2, θ' - θ⟫_ℝ ^ 2) := by
    intro o
    have hd : ‖tdUpdate φ R γ θ o - tdUpdate φ R γ θ' o‖ ≤
        |γ * ⟪φ o.2, θ' - θ⟫_ℝ - ⟪φ o.1, θ' - θ⟫_ℝ| := by
      rw [tdUpdate_sub, norm_smul, Real.norm_eq_abs, ← abs_neg]
      refine (mul_le_of_le_one_right (abs_nonneg _) (hφ _)).trans_eq ?_
      congr 1
      rw [← neg_sub θ' θ, inner_neg_right, inner_neg_right]
      ring
    have hd2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
    rw [sq_abs] at hd2
    have hsum := norm_add_le (tdUpdate φ R γ θ' o) (tdUpdate φ R γ θ o - tdUpdate φ R γ θ' o)
    rw [add_sub_cancel] at hsum
    have hsum2 := pow_le_pow_left₀ (norm_nonneg _) hsum 2
    nlinarith [sq_nonneg (‖tdUpdate φ R γ θ' o‖ - ‖tdUpdate φ R γ θ o - tdUpdate φ R γ θ' o‖),
      sq_nonneg (γ * ⟪φ o.2, θ' - θ⟫_ℝ + ⟪φ o.1, θ' - θ⟫_ℝ), sq_nonneg ⟪φ o.2, θ' - θ⟫_ℝ,
      mul_le_mul_of_nonneg_right (mul_le_mul hγ₁ hγ₁ hγ₀ zero_le_one) (sq_nonneg ⟪φ o.2, θ' - θ⟫_ℝ)]
  -- the marginals of `ν ⊗ₘ P` are `ν`, by invariance for the second one
  have h₁ : ∫ o, ⟪φ o.1, θ' - θ⟫_ℝ ^ 2 ∂(ν ⊗ₘ P) = ∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν := by
    rw [Measure.integral_compProd Integrable.of_finite]
    simp
  have h₂ : ∫ o, ⟪φ o.2, θ' - θ⟫_ℝ ^ 2 ∂(ν ⊗ₘ P) = ∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν := by
    rw [Measure.integral_compProd Integrable.of_finite]
    dsimp only
    rw [← Measure.integral_bind P.aemeasurable Integrable.of_finite, hP.def]
  calc ∫ o, ‖tdUpdate φ R γ θ o‖ ^ 2 ∂(ν ⊗ₘ P)
      ≤ ∫ o, (2 * ‖tdUpdate φ R γ θ' o‖ ^ 2 +
          (4 * ⟪φ o.1, θ' - θ⟫_ℝ ^ 2 + 4 * ⟪φ o.2, θ' - θ⟫_ℝ ^ 2)) ∂(ν ⊗ₘ P) :=
        integral_mono Integrable.of_finite Integrable.of_finite hpt
    _ = 2 * ∫ o, ‖tdUpdate φ R γ θ' o‖ ^ 2 ∂(ν ⊗ₘ P) + 8 * ∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν := by
        rw [integral_add Integrable.of_finite Integrable.of_finite,
          integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul,
          integral_const_mul, integral_const_mul, h₁, h₂]
        ring

/-- **One TD(0) step in expectation**: if `ν` is invariant, `γ ≤ 1`, `‖φ s‖ ≤ 1` and `θ*` is a
zero of the mean-path TD update, then a step of size `α ≥ 0` from a fixed `θ` along the direction
of a transition `(s, s') ∼ ν ⊗ₘ P` satisfies
`𝔼 ‖θ* - (θ + α d θ)‖² ≤ ‖θ* - θ‖² - α (2 (1 - γ) - 8 α) ‖⟪φ, θ* - θ⟫‖²_ν + 2 α² σ²`, with
`σ² = 𝔼 ‖d θ*‖²`. -/
theorem integral_norm_sub_add_smul_tdUpdate_sq_le [CompleteSpace E] (hP : P.Invariant ν)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hγ : γ ≤ 1) {θ' : E}
    (hθ' : meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ θ' = 0) (θ : E) {α : ℝ}
    (hα : 0 ≤ α) :
    ∫ o, ‖θ' - (θ + α • tdUpdate φ R γ θ o)‖ ^ 2 ∂(ν ⊗ₘ P) ≤
      ‖θ' - θ‖ ^ 2 - α * (2 * (1 - γ) - 8 * α) * ∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν +
        2 * α ^ 2 * ∫ o, ‖tdUpdate φ R γ θ' o‖ ^ 2 ∂(ν ⊗ₘ P) := by
  have h₃ := one_sub_mul_integral_sq_le_inner_meanTDUpdate hP hθ' θ
  have h₅ := integral_norm_tdUpdate_sq_le (R := R) hP hφ hγ θ θ'
  -- expand the square
  have hexp : ∀ o, ‖θ' - (θ + α • tdUpdate φ R γ θ o)‖ ^ 2 = ‖θ' - θ‖ ^ 2 -
      2 * α * ⟪θ' - θ, tdUpdate φ R γ θ o⟫_ℝ + α ^ 2 * ‖tdUpdate φ R γ θ o‖ ^ 2 := by
    intro o
    rw [sub_add_eq_sub_sub, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]
    ring
  have hinner : ∫ o, ⟪θ' - θ, tdUpdate φ R γ θ o⟫_ℝ ∂(ν ⊗ₘ P) =
      ⟪θ' - θ, meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ θ⟫_ℝ := by
    rw [integral_inner Integrable.of_finite, integral_tdUpdate]
  simp_rw [hexp]
  rw [integral_add (Integrable.of_finite) Integrable.of_finite,
    integral_sub (integrable_const _) Integrable.of_finite, integral_const, integral_const_mul,
    integral_const_mul, hinner]
  simp only [probReal_univ, one_smul]
  nlinarith [mul_le_mul_of_nonneg_left h₃ hα, mul_le_mul_of_nonneg_left h₅ (sq_nonneg α)]

end LMLExplore.ReinforcementLearning
