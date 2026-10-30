/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.DesignOperator
public import LMLExplore.Analysis.SpecialFunctions.Gaussian.QuadraticForm
public import LMLExplore.Probability.Martingale.Mixture
public import LMLExplore.Probability.Martingale.SubGaussian
public import LMLExplore.Probability.Martingale.Ville
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# The self-normalized bound for vector-valued martingales

Let `𝓕` be a filtration on a standard Borel space, `x` a sequence of features in a
finite-dimensional real inner product space `E` with `x t` `𝓕 t`-measurable (predictable), and
`η` a real noise with `η t` `𝓕 (t + 1)`-measurable and conditionally `σ²`-sub-Gaussian given
`𝓕 t`. Let `S_t = ∑_{s < t} η s • x s` and `V_t = designOp λ x t = λ • 1 + ∑_{s < t} x s ⊗ x s`.

* For every `θ : E`, `exp (⟪θ, S_t⟫ - σ² ‖θ‖²_{V_t(0)} / 2)` is a supermartingale
  [LS, Lemma 20.2], and so is `exp (⟪θ, S_t⟫ - σ² ⟪θ, V_t θ⟫ / 2)`.
* Their mixture over the Lebesgue measure of `E` is a supermartingale (the method of mixtures,
  [LS, Lemma 20.3]), and a Gaussian integral computes it:
  `√((2π / σ²) ^ d / det V_t) * exp (‖S_t‖²_{V_t⁻¹} / (2σ²))`.
* Ville's inequality then gives **the self-normalized bound** [LS, Theorem 20.4]: with probability
  at least `1 - δ`, for all `t`, `‖S_t‖²_{V_t⁻¹} < 2σ² log (1 / δ) + σ² log (det V_t / λ ^ d)`.

## Main statements

* `LMLExplore.supermartingale_exp_inner_sum_smul_sub`: [LS, Lemma 20.2], with `σ²`.
* `LMLExplore.supermartingale_integral_exp_inner_sum_smul_sub_designOp`: the mixture is a
  supermartingale.
* `LMLExplore.measure_exists_inner_ringInverse_designOp_ge_le`: the self-normalized bound, as
  an upper bound on the probability of the bad event.
* `LMLExplore.le_measureReal_forall_inner_ringInverse_designOp_lt`: the same, as a lower bound on
  the probability of the good event.

## Implementation notes

The structure of the proof (method of mixtures, then Ville's inequality) follows the matrix
version `LMLPapers/LeanMachineLearning/SelfNormalized.lean` in the LMLPapers project
(Rémy Degenne, <https://github.com/LeanMachineLearning/LMLPapers>). The statements for operators
on an inner product space, the eigenbasis Gaussian integral computing the mixture and the `σ²`
scaling are new here.

## References

* [AYPS] Y. Abbasi-Yadkori, D. Pál and Cs. Szepesvári, *Improved algorithms for linear stochastic
  bandits*, NeurIPS 2011, Theorem 1.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemmas 20.2, 20.3 and Theorem 20.4.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Module
open scoped ENNReal NNReal InnerProductSpace

namespace LMLExplore

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {P : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {𝓕 : Filtration ℕ mΩ} {x : ℕ → Ω → E} {η : ℕ → Ω → ℝ} {σ2 : ℝ≥0}

section SecondCountable

variable [SecondCountableTopology E]

/-- **Exponential supermartingale of a vector-valued sum** [LS, Lemma 20.2]: for predictable
features `x` and a conditionally `σ²`-sub-Gaussian noise `η`, for every `θ`,
`t ↦ exp (⟪θ, ∑_{s < t} η s • x s⟫ - σ² (∑_{s < t} ⟪θ, x s⟫²) / 2)` is a supermartingale. -/
theorem supermartingale_exp_inner_sum_smul_sub [IsFiniteMeasure P]
    (hx : ∀ t, Measurable[𝓕 t] (x t)) (hη : ∀ t, Measurable[𝓕 (t + 1)] (η t))
    (hsub : ∀ t, HasCondSubgaussianMGF (𝓕 t) (𝓕.le t) (η t) σ2 P) (θ : E) :
    Supermartingale (fun t ω ↦ exp (⟪θ, ∑ s ∈ range t, η s ω • x s ω⟫_ℝ -
      σ2 * (∑ s ∈ range t, ⟪θ, x s ω⟫_ℝ ^ 2) / 2)) 𝓕 P := by
  have h := supermartingale_exp_sum_mul_of_hasCondSubgaussianMGF
    (w := fun t ω ↦ ⟪θ, x t ω⟫_ℝ) hη hsub (fun t ↦ measurable_const.inner (hx t)) 1
  have heq : (fun t ω ↦ exp (⟪θ, ∑ s ∈ range t, η s ω • x s ω⟫_ℝ -
      σ2 * (∑ s ∈ range t, ⟪θ, x s ω⟫_ℝ ^ 2) / 2)) = fun t ω ↦
      exp (1 * ∑ k ∈ range t, ⟪θ, x k ω⟫_ℝ * η k ω - σ2 * 1 ^ 2 *
        (∑ k ∈ range t, ⟪θ, x k ω⟫_ℝ ^ 2) / 2) := by
    funext t ω
    simp [inner_sum, inner_smul_right, mul_comm]
  rw [heq]
  exact h

/-- For every `θ`, `t ↦ exp (⟪θ, S_t⟫ - σ² ⟪θ, V_t θ⟫ / 2)` is a supermartingale, where
`S_t = ∑_{s < t} η s • x s` and `V_t = designOp λ x t`: it is the supermartingale of
`supermartingale_exp_inner_sum_smul_sub` times the constant `exp (-σ² λ ‖θ‖² / 2)`. -/
theorem supermartingale_exp_inner_sum_smul_sub_designOp [IsFiniteMeasure P]
    (hx : ∀ t, Measurable[𝓕 t] (x t)) (hη : ∀ t, Measurable[𝓕 (t + 1)] (η t))
    (hsub : ∀ t, HasCondSubgaussianMGF (𝓕 t) (𝓕.le t) (η t) σ2 P) (lam : ℝ) (θ : E) :
    Supermartingale (fun t ω ↦ exp (⟪θ, ∑ s ∈ range t, η s ω • x s ω⟫_ℝ -
      σ2 * ⟪θ, designOp lam (fun s ↦ x s ω) t θ⟫_ℝ / 2)) 𝓕 P := by
  have h := (supermartingale_exp_inner_sum_smul_sub hx hη hsub θ).smul_nonneg
    (exp_pos (-(σ2 * lam * ‖θ‖ ^ 2 / 2))).le
  have heq : (fun t ω ↦ exp (⟪θ, ∑ s ∈ range t, η s ω • x s ω⟫_ℝ -
      σ2 * ⟪θ, designOp lam (fun s ↦ x s ω) t θ⟫_ℝ / 2)) =
      exp (-(σ2 * lam * ‖θ‖ ^ 2 / 2)) • fun t ω ↦ exp (⟪θ, ∑ s ∈ range t, η s ω • x s ω⟫_ℝ -
        σ2 * (∑ s ∈ range t, ⟪θ, x s ω⟫_ℝ ^ 2) / 2) := by
    funext t ω
    simp only [Pi.smul_apply, smul_eq_mul, ← exp_add, inner_designOp_apply_self,
      real_inner_comm θ]
    congr 1
    ring
  rw [heq]
  exact h

end SecondCountable

variable [FiniteDimensional ℝ E]

/-- **Method of mixtures** [LS, Lemma 20.3]: for `λ > 0` and `σ² ≠ 0`, the mixture over the
Lebesgue measure of `E` of the supermartingales `exp (⟪θ, S_t⟫ - σ² ⟪θ, V_t θ⟫ / 2)` is a
supermartingale. -/
theorem supermartingale_integral_exp_inner_sum_smul_sub_designOp [IsFiniteMeasure P]
    (hx : ∀ t, Measurable[𝓕 t] (x t)) (hη : ∀ t, Measurable[𝓕 (t + 1)] (η t))
    (hsub : ∀ t, HasCondSubgaussianMGF (𝓕 t) (𝓕.le t) (η t) σ2 P) (hσ : σ2 ≠ 0) {lam : ℝ}
    (hlam : 0 < lam) :
    Supermartingale (fun t ω ↦ ∫ θ : E, exp (⟪θ, ∑ s ∈ range t, η s ω • x s ω⟫_ℝ -
      σ2 * ⟪θ, designOp lam (fun s ↦ x s ω) t θ⟫_ℝ / 2)) 𝓕 P := by
  have hσpos : (0 : ℝ) < σ2 := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hσ)
  refine supermartingale_integral_of_integrable
    (fun θ ↦ supermartingale_exp_inner_sum_smul_sub_designOp hx hη hsub lam θ)
    (fun _ _ _ ↦ (exp_pos _).le) (fun t ↦ ?_) ?_
  · -- joint measurability in `(θ, ω)`, for the σ-algebra `𝓕 t` on `Ω`
    let : MeasurableSpace Ω := 𝓕 t
    have hxs : ∀ s ∈ range t, Measurable (x s) := fun s hs ↦
      (hx s).mono (𝓕.mono (mem_range.1 hs).le) le_rfl
    have hηs : ∀ s ∈ range t, Measurable (η s) := fun s hs ↦
      (hη s).mono (𝓕.mono (mem_range.1 hs)) le_rfl
    have hS : Measurable fun p : E × Ω ↦ ∑ s ∈ range t, η s p.2 • x s p.2 :=
      Finset.measurable_fun_sum _ fun s hs ↦ by have := hxs s hs; have := hηs s hs; fun_prop
    have hQ : Measurable fun p : E × Ω ↦ ∑ s ∈ range t, ⟪x s p.2, p.1⟫_ℝ ^ 2 :=
      Finset.measurable_fun_sum _ fun s hs ↦ by have := hxs s hs; fun_prop
    simp only [inner_designOp_apply_self]
    fun_prop
  · -- integrability of the initial expectations, a Gaussian integral
    refine ((integrable_exp_inner_sub_inner_apply (isPositive_designOp hlam.le (fun _ ↦ 0) 0)
      (isUnit_designOp hlam (fun _ ↦ 0) 0) hσpos 0).const_mul (P.real Set.univ)).congr
      (ae_of_all _ fun θ ↦ ?_)
    simp

/-- **The self-normalized bound** [LS, Theorem 20.4]: for predictable features `x`, a
conditionally `σ²`-sub-Gaussian noise `η` with `σ² ≠ 0`, `λ > 0` and `δ > 0`, the probability
that for some `t`, `2σ² log (1 / δ) + σ² log (det V_t / λ ^ d) ≤ ‖S_t‖²_{V_t⁻¹}` is at most `δ`,
where `S_t = ∑_{s < t} η s • x s` and `V_t = designOp λ x t`. -/
theorem measure_exists_inner_ringInverse_designOp_ge_le [IsProbabilityMeasure P]
    (hx : ∀ t, Measurable[𝓕 t] (x t)) (hη : ∀ t, Measurable[𝓕 (t + 1)] (η t))
    (hsub : ∀ t, HasCondSubgaussianMGF (𝓕 t) (𝓕.le t) (η t) σ2 P) (hσ : σ2 ≠ 0)
    {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) :
    P {ω | ∃ t, 2 * σ2 * log (1 / δ) +
        σ2 * log (LinearMap.det (designOp lam (fun s ↦ x s ω) t : E →ₗ[ℝ] E) /
          lam ^ finrank ℝ E) ≤
      ⟪∑ s ∈ range t, η s ω • x s ω,
        Ring.inverse (designOp lam (fun s ↦ x s ω) t) (∑ s ∈ range t, η s ω • x s ω)⟫_ℝ} ≤
      ENNReal.ofReal δ := by
  have hσpos : (0 : ℝ) < σ2 := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hσ)
  set d := finrank ℝ E with hd
  have hΛ : 0 < lam ^ d := pow_pos hlam _
  have hKd : 0 < (2 * π / σ2) ^ d := by positivity
  -- the mixture in closed form
  have hclosed (t : ℕ) (ω : Ω) : ∫ θ : E, exp (⟪θ, ∑ s ∈ range t, η s ω • x s ω⟫_ℝ -
      σ2 * ⟪θ, designOp lam (fun s ↦ x s ω) t θ⟫_ℝ / 2) =
      √((2 * π / σ2) ^ d / LinearMap.det (designOp lam (fun s ↦ x s ω) t : E →ₗ[ℝ] E)) *
        exp (⟪∑ s ∈ range t, η s ω • x s ω, Ring.inverse (designOp lam (fun s ↦ x s ω) t)
          (∑ s ∈ range t, η s ω • x s ω)⟫_ℝ / (2 * σ2)) :=
    integral_exp_inner_sub_inner_apply (isPositive_designOp hlam.le _ t) (isUnit_designOp hlam _ t)
      hσpos _
  have hM0 (ω : Ω) : ∫ θ : E, exp (⟪θ, ∑ s ∈ range 0, η s ω • x s ω⟫_ℝ -
      σ2 * ⟪θ, designOp lam (fun s ↦ x s ω) 0 θ⟫_ℝ / 2) = √((2 * π / σ2) ^ d / lam ^ d) := by
    rw [hclosed, det_designOp_zero, ← hd]
    simp
  have hK : 0 < √((2 * π / σ2) ^ d / lam ^ d) := Real.sqrt_pos.2 (div_pos hKd hΛ)
  have hville := (supermartingale_integral_exp_inner_sum_smul_sub_designOp hx hη hsub hσ
    hlam).measure_exists_le_le
    (fun t ↦ ae_of_all _ fun ω ↦ integral_nonneg fun θ ↦ (exp_pos _).le) (div_pos hK hδ)
  simp only [hM0, integral_const, probReal_univ, one_smul] at hville
  rw [div_div_cancel₀ hK.ne'] at hville
  refine (measure_mono fun ω hω ↦ ?_).trans hville
  obtain ⟨t, ht⟩ := hω
  refine ⟨t, ?_⟩
  rw [hclosed]
  set D := LinearMap.det (designOp lam (fun s ↦ x s ω) t : E →ₗ[ℝ] E)
  set Q := ⟪∑ s ∈ range t, η s ω • x s ω,
    Ring.inverse (designOp lam (fun s ↦ x s ω) t) (∑ s ∈ range t, η s ω • x s ω)⟫_ℝ
  have hD : 0 < D := det_designOp_pos hlam _ t
  have hlog : log (1 / δ) + log (D / lam ^ d) / 2 ≤ Q / (2 * σ2) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hsqrt : √(D / lam ^ d) = exp (log (D / lam ^ d) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (div_pos hD hΛ)]
    ring_nf
  have hmul : (2 * π / σ2) ^ d / D * (D / lam ^ d) = (2 * π / σ2) ^ d / lam ^ d := by
    field_simp
  calc √((2 * π / σ2) ^ d / lam ^ d) / δ
      = √((2 * π / σ2) ^ d / D) * (1 / δ * √(D / lam ^ d)) := by
        rw [mul_left_comm, ← Real.sqrt_mul (div_nonneg hKd.le hD.le), hmul, one_div_mul_eq_div]
    _ ≤ √((2 * π / σ2) ^ d / D) * exp (Q / (2 * σ2)) := by
        gcongr
        rw [hsqrt, ← exp_log (one_div_pos.2 hδ), ← exp_add]
        exact exp_le_exp.2 hlog

/-- **The self-normalized bound** [LS, Theorem 20.4], good-event form: under the assumptions of
`measure_exists_inner_ringInverse_designOp_ge_le`, with probability at least `1 - δ`, for all `t`,
`‖S_t‖²_{V_t⁻¹} < 2σ² log (1 / δ) + σ² log (det V_t / λ ^ d)`. -/
theorem le_measureReal_forall_inner_ringInverse_designOp_lt [IsProbabilityMeasure P]
    (hx : ∀ t, Measurable[𝓕 t] (x t)) (hη : ∀ t, Measurable[𝓕 (t + 1)] (η t))
    (hsub : ∀ t, HasCondSubgaussianMGF (𝓕 t) (𝓕.le t) (η t) σ2 P) (hσ : σ2 ≠ 0)
    {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) :
    1 - δ ≤ P.real {ω | ∀ t, ⟪∑ s ∈ range t, η s ω • x s ω,
        Ring.inverse (designOp lam (fun s ↦ x s ω) t) (∑ s ∈ range t, η s ω • x s ω)⟫_ℝ <
      2 * σ2 * log (1 / δ) + σ2 * log (LinearMap.det (designOp lam (fun s ↦ x s ω) t :
        E →ₗ[ℝ] E) / lam ^ finrank ℝ E)} := by
  set G := {ω | ∀ t, ⟪∑ s ∈ range t, η s ω • x s ω,
      Ring.inverse (designOp lam (fun s ↦ x s ω) t) (∑ s ∈ range t, η s ω • x s ω)⟫_ℝ <
    2 * σ2 * log (1 / δ) + σ2 * log (LinearMap.det (designOp lam (fun s ↦ x s ω) t :
      E →ₗ[ℝ] E) / lam ^ finrank ℝ E)}
  have hbad : P.real Gᶜ ≤ δ := by
    refine ENNReal.toReal_le_of_le_ofReal hδ.le ((measure_mono fun ω hω ↦ ?_).trans
      (measure_exists_inner_ringInverse_designOp_ge_le hx hη hsub hσ hlam hδ))
    simpa [G] using hω
  have h1 : P.real Set.univ ≤ P.real G + P.real Gᶜ := by
    rw [← Set.union_compl_self G]
    exact measureReal_union_le _ _
  rw [probReal_univ] at h1
  linarith

end LMLExplore
