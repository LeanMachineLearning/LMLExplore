/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Value
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import LMLExplore.Analysis.InnerProductSpace.LaxMilgram
import LMLExplore.Probability.Kernel.Operator
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance

/-!
# The projected Bellman equation of linear temporal-difference learning

Let `P` be a Markov kernel on a finite state space `𝓢` with an invariant probability measure `ν`,
let `r : 𝓢 → ℝ` be a reward and `γ` a discount factor, and let `φ : 𝓢 → E` be features in a real
Hilbert space `E`. Linear temporal-difference learning approximates the value `v = r + γ P v` of
the Markov reward process `(P, r)` by a function `s ↦ ⟪φ s, θ⟫` in the span of the features. Its
geometry is that of `L²(ν)`, with the squared norm `‖v‖²_ν = ∫ v² dν`:

* `P` is a nonexpansion of `‖·‖_ν` (`ProbabilityTheory.Kernel.Invariant.integral_sq_integral_le`),
  so the Bellman operator `T v = r + γ P v` is a `γ`-contraction;
* the `ν`-orthogonal projection `Π` on the span of the features is a nonexpansion, so the projected
  Bellman operator `Π T` is a `γ`-contraction;
* the fixed points of `Π T` are the functions `s ↦ ⟪φ s, θ⟫` for the zeros `θ` of the mean-path
  TD(0) update `g θ = ∫ (r s + γ ∫ ⟪φ s', θ⟫ d(P s) - ⟪φ s, θ⟫) φ s dν`, and when the features
  are linearly independent in `L²(ν)` there is exactly one such zero `θ*`;
* the TD fixed point approximates `v` within `(1 - γ²)^(-1/2)` times the best approximation error
  `‖Π v - v‖_ν`.

The projection is written through the Gram operator `Σ_ν = ∫ φ ⊗ φ dν` of the features: its
coefficients `Σ_ν⁻¹ ∫ f φ dν` solve the normal equations of weighted least squares. Linear
independence of the features is the invertibility of `Σ_ν`, which holds when
`ω ‖θ‖² ≤ ∫ ⟪φ s, θ⟫² dν` for some `ω > 0` (`isInvertible_featureGram`).

## Main definitions

* `LMLExplore.ReinforcementLearning.featureGram ν φ`: the Gram operator `Σ_ν = ∫ φ ⊗ φ dν`.
* `LMLExplore.ReinforcementLearning.featureCoeff ν φ`: the coefficients `Σ_ν⁻¹ ∫ f φ dν` of the
  projection of `f` on the features.
* `LMLExplore.ReinforcementLearning.featureProj ν φ`: the `ν`-orthogonal projection `Π` on the
  span of the features.
* `LMLExplore.ReinforcementLearning.projBellman ν φ P r γ`: the projected Bellman operator
  `Π T`, with `T v = r + γ P v`.
* `LMLExplore.ReinforcementLearning.meanTDUpdate ν φ P r γ`: the mean-path TD(0) update `g`.

## Main statements

* `LMLExplore.ReinforcementLearning.integral_sub_featureProj_mul_inner`: `f - Π f` is
  `ν`-orthogonal to the features, and
  `LMLExplore.ReinforcementLearning.integral_sq_sub_inner_eq`: the Pythagorean identity
  `‖f - ⟪φ, θ⟫‖²_ν = ‖f - Π f‖²_ν + ‖Π f - ⟪φ, θ⟫‖²_ν`.
* `LMLExplore.ReinforcementLearning.integral_sq_featureProj_le`: `Π` is a nonexpansion.
* `LMLExplore.ReinforcementLearning.integral_sq_projBellman_sub_le`: `Π T` is a `γ`-contraction
  [TVR97, Lemmas 4 and 6].
* `LMLExplore.ReinforcementLearning.projBellman_eq_self_iff`: the fixed points of `Π T` are the
  `⟪φ, θ⟫` with `g θ = 0`, and
  `LMLExplore.ReinforcementLearning.existsUnique_meanTDUpdate_eq_zero`: for `γ < 1` and linearly
  independent features, `g` has a unique zero [TVR97, Lemma 6].
* `LMLExplore.ReinforcementLearning.one_sub_sq_mul_integral_sq_sub_inner_le`: the approximation
  bound `(1 - γ²) ‖v - ⟪φ, θ*⟫‖²_ν ≤ ‖v - Π v‖²_ν` [TVR97, Theorem 1 and footnote 1],
  [BRS18, (5)], and `Learning.MDP.one_sub_sq_mul_integral_sq_value_sub_inner_le`: its instance for
  the value of a stationary policy of an MDP.
* `LMLExplore.ReinforcementLearning.one_sub_mul_integral_sq_le_inner_meanTDUpdate`,
  `LMLExplore.ReinforcementLearning.norm_meanTDUpdate_le`: the angle and the magnitude of the
  mean-path TD update, `(1 - γ) ‖⟪φ, θ* - θ⟫‖²_ν ≤ ⟪θ* - θ, g θ⟫` and
  `‖g θ‖ ≤ (1 + γ) ‖⟪φ, θ* - θ⟫‖_ν` [BRS18, Lemmas 3 and 4].

## References

* [J. N. Tsitsiklis and B. Van Roy, *An analysis of temporal-difference learning with function
  approximation*, 1997][TVR97]
* [J. Bhandari, D. Russo and R. Singal, *A finite time analysis of temporal difference learning
  with linear function approximation*, 2018][BRS18]
-/

public section

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped NNReal InnerProductSpace

namespace LMLExplore.ReinforcementLearning

variable {𝓢 E : Type*} {m𝓢 : MeasurableSpace 𝓢} [Finite 𝓢] [MeasurableSingletonClass 𝓢]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ν : Measure 𝓢} [IsFiniteMeasure ν] {φ : 𝓢 → E}

/-! ### The Gram operator of the features -/

section Gram

/-- The **Gram operator** `Σ_ν = ∫ φ ⊗ φ dν` of the features `φ` under `ν`, the operator
`θ ↦ ∫ ⟪φ s, θ⟫ φ s dν`. -/
noncomputable def featureGram (ν : Measure 𝓢) (φ : 𝓢 → E) : E →L[ℝ] E :=
  ∫ s, rankOne ℝ (φ s) (φ s) ∂ν

omit [Finite 𝓢] [MeasurableSingletonClass 𝓢] [IsFiniteMeasure ν] in
theorem featureGram_def (ν : Measure 𝓢) (φ : 𝓢 → E) :
    featureGram ν φ = ∫ s, rankOne ℝ (φ s) (φ s) ∂ν := (rfl)

theorem featureGram_apply (θ : E) : featureGram ν φ θ = ∫ s, ⟪φ s, θ⟫_ℝ • φ s ∂ν := by
  rw [featureGram_def, ContinuousLinearMap.integral_apply Integrable.of_finite]
  simp

/-- The quadratic form of the Gram operator: `⟪Σ_ν θ, θ'⟫ = ∫ ⟪φ s, θ⟫ ⟪φ s, θ'⟫ dν`. -/
theorem inner_featureGram_apply [CompleteSpace E] (θ θ' : E) :
    ⟪featureGram ν φ θ, θ'⟫_ℝ = ∫ s, ⟪φ s, θ⟫_ℝ * ⟪φ s, θ'⟫_ℝ ∂ν := by
  rw [featureGram_apply, real_inner_comm, ← integral_inner Integrable.of_finite]
  simp [real_inner_smul_right, real_inner_comm]

/-- The Gram operator only depends on the values of the linear functions `s ↦ ⟪φ s, θ⟫`. -/
theorem featureGram_eq_of_forall_inner_eq {θ θ' : E} (h : ∀ s, ⟪φ s, θ⟫_ℝ = ⟪φ s, θ'⟫_ℝ) :
    featureGram ν φ θ = featureGram ν φ θ' := by
  simp only [featureGram_apply, h]

/-- The Gram operator is invertible when the features are linearly independent in `L²(ν)` in the
quantitative sense `ω ‖θ‖² ≤ ∫ ⟪φ s, θ⟫² dν` with `ω > 0`. -/
theorem isInvertible_featureGram [CompleteSpace E] {ω : ℝ} (hω : 0 < ω)
    (h : ∀ θ, ω * ‖θ‖ ^ 2 ≤ ∫ s, ⟪φ s, θ⟫_ℝ ^ 2 ∂ν) : (featureGram ν φ).IsInvertible :=
  ContinuousLinearMap.isInvertible_of_mul_norm_sq_le_inner hω fun θ ↦ by
    simpa [inner_featureGram_apply, sq] using h θ

/-- For an invertible Gram operator, a linear function of the features determines its
coefficients. -/
theorem eq_of_forall_inner_eq (hG : (featureGram ν φ).IsInvertible) {θ θ' : E}
    (h : ∀ s, ⟪φ s, θ⟫_ℝ = ⟪φ s, θ'⟫_ℝ) : θ = θ' :=
  hG.bijective.1 (featureGram_eq_of_forall_inner_eq h)

end Gram

/-! ### The projection on the features -/

section Projection

/-- The coefficients `Σ_ν⁻¹ ∫ f φ dν` of the `ν`-orthogonal projection of `f` on the span of the
features: the solution of the normal equations `Σ_ν θ = ∫ f φ dν` of weighted least squares (and
`0` if `Σ_ν` is not invertible). -/
noncomputable def featureCoeff (ν : Measure 𝓢) [IsFiniteMeasure ν] (φ : 𝓢 → E) :
    (𝓢 → ℝ) →ₗ[ℝ] E where
  toFun f := (featureGram ν φ).inverse (∫ s, f s • φ s ∂ν)
  map_add' f g := by
    simp only [Pi.add_apply, add_smul, integral_add Integrable.of_finite Integrable.of_finite,
      map_add]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, integral_smul, map_smul, RingHom.id_apply]

theorem featureCoeff_apply (f : 𝓢 → ℝ) :
    featureCoeff ν φ f = (featureGram ν φ).inverse (∫ s, f s • φ s ∂ν) := (rfl)

/-- The **`ν`-orthogonal projection** `Π f = ⟪φ, Σ_ν⁻¹ ∫ f φ dν⟫` of `f` on the span of the
features. -/
noncomputable def featureProj (ν : Measure 𝓢) [IsFiniteMeasure ν] (φ : 𝓢 → E) :
    (𝓢 → ℝ) →ₗ[ℝ] 𝓢 → ℝ where
  toFun f s := ⟪φ s, featureCoeff ν φ f⟫_ℝ
  map_add' f g := by ext s; simp [inner_add_right]
  map_smul' c f := by ext s; simp [real_inner_smul_right]

theorem featureProj_apply (f : 𝓢 → ℝ) (s : 𝓢) :
    featureProj ν φ f s = ⟪φ s, featureCoeff ν φ f⟫_ℝ := (rfl)

/-- Without an invertible Gram operator, the projection is `0`. -/
theorem featureProj_of_not_isInvertible (hG : ¬(featureGram ν φ).IsInvertible) (f : 𝓢 → ℝ) :
    featureProj ν φ f = 0 := by
  ext s
  simp [featureProj_apply, featureCoeff_apply, hG]

/-- The coefficients of the projection solve the **normal equations** `Σ_ν θ = ∫ f φ dν`. -/
theorem featureGram_featureCoeff (hG : (featureGram ν φ).IsInvertible) (f : 𝓢 → ℝ) :
    featureGram ν φ (featureCoeff ν φ f) = ∫ s, f s • φ s ∂ν :=
  hG.self_apply_inverse _

/-- The coefficients of the projection are the unique solution of the normal equations. -/
theorem featureCoeff_eq_iff (hG : (featureGram ν φ).IsInvertible) {f : 𝓢 → ℝ} {θ : E} :
    featureCoeff ν φ f = θ ↔ featureGram ν φ θ = ∫ s, f s • φ s ∂ν := by
  refine ⟨fun h ↦ h ▸ featureGram_featureCoeff hG f, fun h ↦ ?_⟩
  rw [featureCoeff_apply, ← h, hG.inverse_apply_self]

/-- The coefficients of the projection of a linear function of the features are its
coefficients. -/
@[simp]
theorem featureCoeff_inner (hG : (featureGram ν φ).IsInvertible) (θ : E) :
    featureCoeff ν φ (fun s ↦ ⟪φ s, θ⟫_ℝ) = θ :=
  (featureCoeff_eq_iff hG).2 (featureGram_apply θ)

/-- The projection fixes the span of the features. -/
@[simp]
theorem featureProj_inner (hG : (featureGram ν φ).IsInvertible) (θ : E) :
    featureProj ν φ (fun s ↦ ⟪φ s, θ⟫_ℝ) = fun s ↦ ⟪φ s, θ⟫_ℝ := by
  ext s
  rw [featureProj_apply, featureCoeff_inner hG]

/-- The projection of `f` is the linear function `⟪φ, θ⟫` exactly when `θ` is the coefficient of
the projection. -/
theorem featureProj_eq_inner_iff (hG : (featureGram ν φ).IsInvertible) {f : 𝓢 → ℝ} {θ : E} :
    featureProj ν φ f = (fun s ↦ ⟪φ s, θ⟫_ℝ) ↔ featureCoeff ν φ f = θ := by
  refine ⟨fun h ↦ eq_of_forall_inner_eq hG fun s ↦ ?_, fun h ↦ ?_⟩
  · rw [← featureProj_apply, h]
  · ext s
    rw [featureProj_apply, h]

/-- The projection is idempotent. -/
@[simp]
theorem featureProj_featureProj (hG : (featureGram ν φ).IsInvertible) (f : 𝓢 → ℝ) :
    featureProj ν φ (featureProj ν φ f) = featureProj ν φ f :=
  featureProj_inner hG _

/-- **Orthogonality**: the residual `f - Π f` is `ν`-orthogonal to the span of the features. -/
theorem integral_sub_featureProj_mul_inner [CompleteSpace E] (hG : (featureGram ν φ).IsInvertible)
    (f : 𝓢 → ℝ) (θ : E) :
    ∫ s, (f s - featureProj ν φ f s) * ⟪φ s, θ⟫_ℝ ∂ν = 0 := by
  have h₁ : ∫ s, f s * ⟪φ s, θ⟫_ℝ ∂ν = ⟪∫ s, f s • φ s ∂ν, θ⟫_ℝ := by
    rw [real_inner_comm, ← integral_inner Integrable.of_finite]
    simp [real_inner_smul_right, real_inner_comm]
  have h₂ : ∫ s, featureProj ν φ f s * ⟪φ s, θ⟫_ℝ ∂ν =
      ⟪featureGram ν φ (featureCoeff ν φ f), θ⟫_ℝ := by
    simp [inner_featureGram_apply, featureProj_apply]
  simp only [sub_mul]
  rw [integral_sub Integrable.of_finite Integrable.of_finite, h₁, h₂,
    featureGram_featureCoeff hG, sub_self]

/-- **Pythagorean identity**: for every `θ`,
`‖f - ⟪φ, θ⟫‖²_ν = ‖f - Π f‖²_ν + ‖Π f - ⟪φ, θ⟫‖²_ν`. -/
theorem integral_sq_sub_inner_eq [CompleteSpace E] (hG : (featureGram ν φ).IsInvertible)
    (f : 𝓢 → ℝ) (θ : E) :
    ∫ s, (f s - ⟪φ s, θ⟫_ℝ) ^ 2 ∂ν =
      ∫ s, (f s - featureProj ν φ f s) ^ 2 ∂ν +
        ∫ s, (featureProj ν φ f s - ⟪φ s, θ⟫_ℝ) ^ 2 ∂ν := by
  have hc : ∀ s, featureProj ν φ f s - ⟪φ s, θ⟫_ℝ = ⟪φ s, featureCoeff ν φ f - θ⟫_ℝ := by
    simp [featureProj_apply, inner_sub_right]
  have h := integral_sub_featureProj_mul_inner hG f (featureCoeff ν φ f - θ)
  simp_rw [← hc] at h
  rw [← integral_add Integrable.of_finite Integrable.of_finite]
  calc ∫ s, (f s - ⟪φ s, θ⟫_ℝ) ^ 2 ∂ν
      = ∫ s, ((f s - featureProj ν φ f s) ^ 2 + (featureProj ν φ f s - ⟪φ s, θ⟫_ℝ) ^ 2 +
          2 * ((f s - featureProj ν φ f s) * (featureProj ν φ f s - ⟪φ s, θ⟫_ℝ))) ∂ν := by
        congr 1
        ext s
        ring
    _ = _ := by
        rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul, h,
          mul_zero, add_zero]

/-- **Best approximation**: `Π f` is the closest function to `f` in the span of the features. -/
theorem integral_sq_sub_featureProj_le [CompleteSpace E] (hG : (featureGram ν φ).IsInvertible)
    (f : 𝓢 → ℝ) (θ : E) :
    ∫ s, (f s - featureProj ν φ f s) ^ 2 ∂ν ≤ ∫ s, (f s - ⟪φ s, θ⟫_ℝ) ^ 2 ∂ν := by
  rw [integral_sq_sub_inner_eq hG f θ]
  exact le_add_of_nonneg_right (integral_nonneg fun _ ↦ sq_nonneg _)

/-- The projection is a **nonexpansion** of `L²(ν)`: `‖Π f‖²_ν ≤ ‖f‖²_ν`. -/
theorem integral_sq_featureProj_le [CompleteSpace E] (f : 𝓢 → ℝ) :
    ∫ s, featureProj ν φ f s ^ 2 ∂ν ≤ ∫ s, f s ^ 2 ∂ν := by
  by_cases hG : (featureGram ν φ).IsInvertible
  · have h := integral_sq_sub_inner_eq hG f 0
    simp only [inner_zero_right, sub_zero] at h
    rw [h]
    exact le_add_of_nonneg_left (integral_nonneg fun _ ↦ sq_nonneg _)
  · simp only [featureProj_of_not_isInvertible hG, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, integral_zero]
    exact integral_nonneg fun _ ↦ sq_nonneg _

end Projection

/-! ### The projected Bellman operator and the mean-path TD update -/

section Bellman

variable {P : Kernel 𝓢 𝓢} {r : 𝓢 → ℝ} {γ : ℝ≥0}

/-- The **projected Bellman operator** `Π T v = Π (r + γ P v)` of the Markov reward process
`(P, r)` with discount `γ`, for the `ν`-orthogonal projection `Π` on the features. -/
noncomputable def projBellman (ν : Measure 𝓢) [IsFiniteMeasure ν] (φ : 𝓢 → E) (P : Kernel 𝓢 𝓢)
    (r : 𝓢 → ℝ) (γ : ℝ≥0) (v : 𝓢 → ℝ) : 𝓢 → ℝ :=
  featureProj ν φ fun s ↦ r s + γ * ∫ s', v s' ∂(P s)

theorem projBellman_def (v : 𝓢 → ℝ) :
    projBellman ν φ P r γ v = featureProj ν φ fun s ↦ r s + γ * ∫ s', v s' ∂(P s) := (rfl)

/-- **The projected Bellman operator is a `γ`-contraction** of `L²(ν)` for an invariant measure
`ν` [TVR97, Lemmas 4 and 6], [BRS18, Lemma 2]. -/
theorem integral_sq_projBellman_sub_le [CompleteSpace E] [IsMarkovKernel P] (hP : P.Invariant ν)
    (v w : 𝓢 → ℝ) :
    ∫ s, (projBellman ν φ P r γ v s - projBellman ν φ P r γ w s) ^ 2 ∂ν ≤
      γ ^ 2 * ∫ s, (v s - w s) ^ 2 ∂ν := by
  have h : ∀ s, projBellman ν φ P r γ v s - projBellman ν φ P r γ w s =
      featureProj ν φ (fun s ↦ (γ : ℝ) * ∫ s', (v s' - w s') ∂(P s)) s := by
    intro s
    rw [projBellman_def, projBellman_def, ← Pi.sub_apply, ← map_sub]
    refine congrArg (fun f ↦ featureProj ν φ f s) (funext fun s' ↦ ?_)
    rw [Pi.sub_apply, integral_sub Integrable.of_finite Integrable.of_finite]
    ring
  simp_rw [h]
  calc _ ≤ ∫ s, ((γ : ℝ) * ∫ s', (v s' - w s') ∂(P s)) ^ 2 ∂ν := integral_sq_featureProj_le _
    _ = γ ^ 2 * ∫ s, (∫ s', (v s' - w s') ∂(P s)) ^ 2 ∂ν := by
        simp_rw [mul_pow]
        rw [integral_const_mul]
    _ ≤ γ ^ 2 * ∫ s, (v s - w s) ^ 2 ∂ν := mul_le_mul_of_nonneg_left
        (hP.integral_sq_integral_le (measurable_of_finite _) Integrable.of_finite) (by positivity)

/-- The **mean-path TD(0) update** `g θ = ∫ (r s + γ ∫ ⟪φ s', θ⟫ d(P s) - ⟪φ s, θ⟫) φ s dν` of
linear temporal-difference learning with features `φ`, for states `s` drawn from `ν` and next
states `s'` drawn from `P s`: the mean of the TD(0) direction
`(r s + γ ⟪φ s', θ⟫ - ⟪φ s, θ⟫) φ s`. -/
noncomputable def meanTDUpdate (ν : Measure 𝓢) (φ : 𝓢 → E) (P : Kernel 𝓢 𝓢) (r : 𝓢 → ℝ)
    (γ : ℝ≥0) (θ : E) : E :=
  ∫ s, (r s + γ * ∫ s', ⟪φ s', θ⟫_ℝ ∂(P s) - ⟪φ s, θ⟫_ℝ) • φ s ∂ν

omit [Finite 𝓢] [MeasurableSingletonClass 𝓢] [IsFiniteMeasure ν] in
theorem meanTDUpdate_def (θ : E) :
    meanTDUpdate ν φ P r γ θ =
      ∫ s, (r s + γ * ∫ s', ⟪φ s', θ⟫_ℝ ∂(P s) - ⟪φ s, θ⟫_ℝ) • φ s ∂ν := (rfl)

/-- The mean-path TD update is the residual of the normal equations of the projected Bellman
operator: `g θ = ∫ (T ⟪φ, θ⟫) φ dν - Σ_ν θ`. -/
theorem meanTDUpdate_eq_sub_featureGram (θ : E) :
    meanTDUpdate ν φ P r γ θ =
      (∫ s, (r s + γ * ∫ s', ⟪φ s', θ⟫_ℝ ∂(P s)) • φ s ∂ν) - featureGram ν φ θ := by
  rw [meanTDUpdate_def, featureGram_apply, ← integral_sub Integrable.of_finite Integrable.of_finite]
  simp_rw [sub_smul]

/-- **The fixed points of the projected Bellman operator in the span of the features are the
zeros of the mean-path TD update**. -/
theorem projBellman_inner_eq_iff (hG : (featureGram ν φ).IsInvertible) {θ : E} :
    projBellman ν φ P r γ (fun s ↦ ⟪φ s, θ⟫_ℝ) = (fun s ↦ ⟪φ s, θ⟫_ℝ) ↔
      meanTDUpdate ν φ P r γ θ = 0 := by
  rw [projBellman_def, featureProj_eq_inner_iff hG, featureCoeff_eq_iff hG,
    meanTDUpdate_eq_sub_featureGram, sub_eq_zero, eq_comm]

/-- **The fixed points of the projected Bellman operator** are the linear functions `⟪φ, θ⟫` of the
features whose coefficients are zeros of the mean-path TD update. -/
theorem projBellman_eq_self_iff (hG : (featureGram ν φ).IsInvertible) {v : 𝓢 → ℝ} :
    projBellman ν φ P r γ v = v ↔
      ∃ θ, v = (fun s ↦ ⟪φ s, θ⟫_ℝ) ∧ meanTDUpdate ν φ P r γ θ = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hv : v = fun s ↦ ⟪φ s, featureCoeff ν φ fun s ↦ r s + γ * ∫ s', v s' ∂(P s)⟫_ℝ := by
      conv_lhs => rw [← h]
      ext s
      rw [projBellman_def, featureProj_apply]
    refine ⟨_, hv, (projBellman_inner_eq_iff hG).1 ?_⟩
    rw [← hv, h]
  · rintro ⟨θ, rfl, hθ⟩
    exact (projBellman_inner_eq_iff hG).2 hθ

/-- The operator `A θ = ∫ (⟪φ s, θ⟫ - γ ⟪∫ φ d(P s), θ⟫) φ s dν` of the linear system
`A θ = ∫ r φ dν` whose solutions are the zeros of the mean-path TD update. -/
private noncomputable def tdOperator (ν : Measure 𝓢) (φ : 𝓢 → E) (P : Kernel 𝓢 𝓢) (γ : ℝ≥0) :
    E →L[ℝ] E :=
  ∫ s, rankOne ℝ (φ s) (φ s - (γ : ℝ) • ∫ s', φ s' ∂(P s)) ∂ν

private lemma tdOperator_apply [CompleteSpace E] [IsMarkovKernel P] (θ : E) :
    tdOperator ν φ P γ θ = ∫ s, (⟪φ s, θ⟫_ℝ - γ * ∫ s', ⟪φ s', θ⟫_ℝ ∂(P s)) • φ s ∂ν := by
  rw [tdOperator, ContinuousLinearMap.integral_apply Integrable.of_finite]
  congr 1
  ext s
  rw [rankOne_apply, inner_sub_left, real_inner_smul_left, real_inner_comm θ (∫ s', φ s' ∂(P s)),
    ← integral_inner Integrable.of_finite]
  simp_rw [real_inner_comm θ]

private lemma meanTDUpdate_eq_sub_tdOperator [CompleteSpace E] [IsMarkovKernel P] (θ : E) :
    meanTDUpdate ν φ P r γ θ = (∫ s, r s • φ s ∂ν) - tdOperator ν φ P γ θ := by
  rw [meanTDUpdate_def, tdOperator_apply, ← integral_sub Integrable.of_finite Integrable.of_finite]
  congr 1
  ext s
  rw [← sub_smul]
  ring_nf

/-- The difference of two values of the mean-path TD update is the value of `A`:
`g θ - g θ' = A (θ' - θ)`. -/
private lemma meanTDUpdate_sub [CompleteSpace E] [IsMarkovKernel P] (θ θ' : E) :
    meanTDUpdate ν φ P r γ θ - meanTDUpdate ν φ P r γ θ' = tdOperator ν φ P γ (θ' - θ) := by
  rw [meanTDUpdate_eq_sub_tdOperator, meanTDUpdate_eq_sub_tdOperator, map_sub]
  abel

/-- The coercivity of `A`: `(1 - γ) ∫ ⟪φ s, θ⟫² dν ≤ ⟪A θ, θ⟫`, from the nonexpansion of `P` in
`L²(ν)`. -/
private lemma one_sub_mul_integral_sq_le_inner_tdOperator [CompleteSpace E] [IsMarkovKernel P]
    (hP : P.Invariant ν) (θ : E) :
    (1 - γ) * ∫ s, ⟪φ s, θ⟫_ℝ ^ 2 ∂ν ≤ ⟪tdOperator ν φ P γ θ, θ⟫_ℝ := by
  have h := hP.integral_mul_integral_le (f := fun s ↦ ⟪φ s, θ⟫_ℝ) (measurable_of_finite _)
    Integrable.of_finite
  have hA : ⟪tdOperator ν φ P γ θ, θ⟫_ℝ =
      ∫ s, (⟪φ s, θ⟫_ℝ - γ * ∫ s', ⟪φ s', θ⟫_ℝ ∂(P s)) * ⟪φ s, θ⟫_ℝ ∂ν := by
    rw [tdOperator_apply, real_inner_comm, ← integral_inner Integrable.of_finite]
    simp_rw [real_inner_smul_right, real_inner_comm θ]
  have hsplit : ∫ s, (⟪φ s, θ⟫_ℝ - γ * ∫ s', ⟪φ s', θ⟫_ℝ ∂(P s)) * ⟪φ s, θ⟫_ℝ ∂ν =
      ∫ s, ⟪φ s, θ⟫_ℝ ^ 2 ∂ν - γ * ∫ s, ⟪φ s, θ⟫_ℝ * ∫ s', ⟪φ s', θ⟫_ℝ ∂(P s) ∂ν := by
    rw [← integral_const_mul, ← integral_sub Integrable.of_finite Integrable.of_finite]
    congr 1
    ext s
    ring
  rw [hA, hsplit]
  nlinarith [mul_le_mul_of_nonneg_left h γ.coe_nonneg]

/-- **The mean-path TD update has a unique zero** `θ*` [TVR97, Lemma 6], when `ν` is invariant,
`γ < 1` and the features are linearly independent in `L²(ν)` in the quantitative sense
`ω ‖θ‖² ≤ ∫ ⟪φ s, θ⟫² dν` with `ω > 0`. By `projBellman_eq_self_iff`, `⟪φ, θ*⟫` is then the
unique fixed point of the projected Bellman operator. -/
theorem existsUnique_meanTDUpdate_eq_zero [CompleteSpace E] [IsMarkovKernel P]
    (hP : P.Invariant ν) (hγ : γ < 1) {ω : ℝ} (hω : 0 < ω)
    (h : ∀ θ, ω * ‖θ‖ ^ 2 ≤ ∫ s, ⟪φ s, θ⟫_ℝ ^ 2 ∂ν) :
    ∃! θ, meanTDUpdate ν φ P r γ θ = 0 := by
  have hγ' : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hA : (tdOperator ν φ P γ).IsInvertible :=
    ContinuousLinearMap.isInvertible_of_mul_norm_sq_le_inner (mul_pos hγ' hω) fun θ ↦ by
      rw [mul_assoc]
      exact (mul_le_mul_of_nonneg_left (h θ) hγ'.le).trans
        (one_sub_mul_integral_sq_le_inner_tdOperator hP θ)
  refine ⟨(tdOperator ν φ P γ).inverse (∫ s, r s • φ s ∂ν), ?_, fun θ hθ ↦ ?_⟩
  · dsimp only
    rw [meanTDUpdate_eq_sub_tdOperator, hA.self_apply_inverse, sub_self]
  · dsimp only at hθ
    rw [meanTDUpdate_eq_sub_tdOperator, sub_eq_zero] at hθ
    rw [hθ, hA.inverse_apply_self]

/-- **The mean-path TD update points towards its zero** [BRS18, Lemma 3]: if `ν` is invariant and
`g θ* = 0`, then `(1 - γ) ‖⟪φ, θ* - θ⟫‖²_ν ≤ ⟪θ* - θ, g θ⟫`. -/
theorem one_sub_mul_integral_sq_le_inner_meanTDUpdate [CompleteSpace E] [IsMarkovKernel P]
    (hP : P.Invariant ν) {θ' : E} (hθ' : meanTDUpdate ν φ P r γ θ' = 0) (θ : E) :
    (1 - γ) * ∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν ≤ ⟪θ' - θ, meanTDUpdate ν φ P r γ θ⟫_ℝ := by
  have h := meanTDUpdate_sub (ν := ν) (φ := φ) (P := P) (r := r) (γ := γ) θ θ'
  rw [hθ', sub_zero] at h
  rw [h, real_inner_comm]
  exact one_sub_mul_integral_sq_le_inner_tdOperator hP _

/-- **The norm of the mean-path TD update** [BRS18, Lemma 4]: if `ν` is an invariant probability
measure, the features satisfy `‖φ s‖ ≤ 1` and `g θ* = 0`, then
`‖g θ‖ ≤ (1 + γ) ‖⟪φ, θ* - θ⟫‖_ν`. The source bounds `1 + γ` by `2`. -/
theorem norm_meanTDUpdate_le [CompleteSpace E] [IsProbabilityMeasure ν] [IsMarkovKernel P]
    (hP : P.Invariant ν) (hφ : ∀ s, ‖φ s‖ ≤ 1) {θ' : E} (hθ' : meanTDUpdate ν φ P r γ θ' = 0)
    (θ : E) :
    ‖meanTDUpdate ν φ P r γ θ‖ ≤ (1 + γ) * √(∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν) := by
  set x : 𝓢 → ℝ := fun s ↦ ⟪φ s, θ' - θ⟫_ℝ with hx
  set h : 𝓢 → ℝ := fun s ↦ x s - γ * ∫ s', x s' ∂(P s) with hh
  have hg : meanTDUpdate ν φ P r γ θ = ∫ s, h s • φ s ∂ν := by
    have := meanTDUpdate_sub (ν := ν) (φ := φ) (P := P) (r := r) (γ := γ) θ θ'
    rw [hθ', sub_zero] at this
    rw [this, tdOperator_apply]
  -- `‖g θ‖ ≤ ∫ |h| dν`, since `‖φ‖ ≤ 1`
  have h₁ : ‖meanTDUpdate ν φ P r γ θ‖ ≤ ∫ s, |h s| ∂ν := by
    rw [hg]
    refine (norm_integral_le_integral_norm _).trans
      (integral_mono Integrable.of_finite Integrable.of_finite fun s ↦ ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (hφ s)
  -- Jensen's inequality `(∫ |h| dν)² ≤ ∫ h² dν`
  have h₂ : (∫ s, |h s| ∂ν) ^ 2 ≤ ∫ s, h s ^ 2 ∂ν := by
    have hv := variance_nonneg (fun s ↦ |h s|) ν
    rw [variance_eq_sub ((memLp_two_iff_integrable_sq
      (measurable_of_finite _).aestronglyMeasurable).2 Integrable.of_finite)] at hv
    simpa [sq_abs] using hv
  -- `h² ≤ (1 + γ) (x² + γ (P x)²)` pointwise, and `P` is a nonexpansion of `L²(ν)`
  have h₃ : ∫ s, h s ^ 2 ∂ν ≤ (1 + γ) ^ 2 * ∫ s, x s ^ 2 ∂ν := by
    have hγ : (0 : ℝ) ≤ γ := γ.coe_nonneg
    have hP2 := hP.integral_sq_integral_le (measurable_of_finite x) Integrable.of_finite
    calc ∫ s, h s ^ 2 ∂ν
        ≤ ∫ s, (1 + γ) * (x s ^ 2 + γ * (∫ s', x s' ∂(P s)) ^ 2) ∂ν := by
          refine integral_mono Integrable.of_finite Integrable.of_finite fun s ↦ ?_
          simp only [hh]
          nlinarith [mul_nonneg hγ (sq_nonneg (x s + ∫ s', x s' ∂(P s)))]
      _ = (1 + γ) * (∫ s, x s ^ 2 ∂ν + γ * ∫ s, (∫ s', x s' ∂(P s)) ^ 2 ∂ν) := by
          rw [integral_const_mul, integral_add Integrable.of_finite Integrable.of_finite,
            integral_const_mul]
      _ ≤ (1 + γ) ^ 2 * ∫ s, x s ^ 2 ∂ν := by nlinarith [mul_le_mul_of_nonneg_left hP2 hγ]
  have hx0 : 0 ≤ ∫ s, x s ^ 2 ∂ν := integral_nonneg fun _ ↦ sq_nonneg _
  calc ‖meanTDUpdate ν φ P r γ θ‖ ≤ ∫ s, |h s| ∂ν := h₁
    _ = √((∫ s, |h s| ∂ν) ^ 2) := (Real.sqrt_sq (integral_nonneg fun _ ↦ abs_nonneg _)).symm
    _ ≤ √((1 + γ) ^ 2 * ∫ s, x s ^ 2 ∂ν) := Real.sqrt_le_sqrt (h₂.trans h₃)
    _ = (1 + γ) * √(∫ s, x s ^ 2 ∂ν) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- **Approximation bound of the TD fixed point** [TVR97, Theorem 1 and footnote 1], [BRS18, (5)]:
if `v = r + γ P v` and `g θ = 0`, then `(1 - γ²) ‖v - ⟪φ, θ⟫‖²_ν ≤ ‖v - Π v‖²_ν`. For `γ < 1`,
the TD fixed point is within `(1 - γ²)^(-1/2)` of the best approximation of `v` by the
features. -/
theorem one_sub_sq_mul_integral_sq_sub_inner_le [CompleteSpace E] [IsMarkovKernel P]
    (hP : P.Invariant ν) (hG : (featureGram ν φ).IsInvertible) {v : 𝓢 → ℝ}
    (hv : ∀ s, v s = r s + γ * ∫ s', v s' ∂(P s)) {θ : E}
    (hθ : meanTDUpdate ν φ P r γ θ = 0) :
    (1 - (γ : ℝ) ^ 2) * ∫ s, (v s - ⟪φ s, θ⟫_ℝ) ^ 2 ∂ν ≤
      ∫ s, (v s - featureProj ν φ v s) ^ 2 ∂ν := by
  have hfix := (projBellman_inner_eq_iff hG).2 hθ
  have hTv : projBellman ν φ P r γ v = featureProj ν φ v := by
    rw [projBellman_def]
    congr 1
    ext s
    exact (hv s).symm
  have hc := integral_sq_projBellman_sub_le (φ := φ) (r := r) (γ := γ) hP v
    (fun s ↦ ⟪φ s, θ⟫_ℝ)
  rw [hTv, hfix] at hc
  have hpy := integral_sq_sub_inner_eq hG v θ
  nlinarith

end Bellman

end LMLExplore.ReinforcementLearning

namespace Learning.MDP

open Learning LMLExplore.ReinforcementLearning

variable {𝓢 𝓐 E : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Finite 𝓢]
  [MeasurableSingletonClass 𝓢] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ν : Measure 𝓢} [IsFiniteMeasure ν] {φ : 𝓢 → E}

/-- **Approximation bound of the TD fixed point for the value of a stationary policy**: if `ν` is
invariant for the state kernel `P_π` of a stationary policy `π`, rewards are bounded, `γ < 1`
and `θ` is a zero of the mean-path TD update of `(P_π, r_π)`, then
`(1 - γ²) ‖v^π - ⟪φ, θ⟫‖²_ν ≤ ‖v^π - Π v^π‖²_ν`. -/
theorem one_sub_sq_mul_integral_sq_value_sub_inner_le (M : MDP 𝓢 𝓐 ℝ) {γ : ℝ≥0}
    {π : Kernel 𝓢 𝓐} [IsMarkovKernel π] {C : ℝ} (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hP : (M.stateKernel π).Invariant ν)
    (hG : (featureGram ν φ).IsInvertible) {θ : E}
    (hθ : meanTDUpdate ν φ (M.stateKernel π) (M.policyReward π) γ θ = 0) :
    (1 - (γ : ℝ) ^ 2) * ∫ s, (M.value γ π s - ⟪φ s, θ⟫_ℝ) ^ 2 ∂ν ≤
      ∫ s, (M.value γ π s - featureProj ν φ (M.value γ π) s) ^ 2 ∂ν :=
  one_sub_sq_mul_integral_sq_sub_inner_le hP hG (M.value_eq_policyReward_add hγ hR) hθ

end Learning.MDP
