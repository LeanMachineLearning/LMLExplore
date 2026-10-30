/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.Ridge
public import LMLExplore.Probability.Martingale.SelfNormalized

/-!
# Confidence ellipsoids for ridge regression

Let `𝓕` be a filtration on a standard Borel space, `x` a sequence of features in a
finite-dimensional real inner product space `E` with `x t` `𝓕 t`-measurable (predictable), and
`η` a real noise with `η t` `𝓕 (t + 1)`-measurable and conditionally `σ²`-sub-Gaussian given
`𝓕 t`. The responses follow the linear model `y t = ⟪θ, x t⟫ + η t` for an unknown `θ : E`.
For `λ > 0`, let `V_t = designOp λ x t` and `θ̂_t = ridgeEstimate λ x y t`.

With probability at least `1 - δ`, for all `t` simultaneously, `θ` lies in the ellipsoid
centered at the ridge estimate
`‖θ̂_t - θ‖_{V_t} < √λ ‖θ‖ + √(2σ² log (1 / δ) + σ² log (det V_t / λ ^ d))`,
where `‖v‖_V = √⟪v, V v⟫` and `d` is the dimension of `E` [LS, Theorem 20.5]. If moreover
`‖x t‖ ≤ L` for all `t`, the log-determinant is at most `d log (1 + t L² / (λ d))`. These are the
confidence sets of optimistic algorithms for linear bandits.

The bound combines the deterministic estimate
`‖θ̂_t - θ‖_{V_t} ≤ √λ ‖θ‖ + ‖∑_{s < t} η s • x s‖_{V_t⁻¹}`
(`LMLExplore.sqrt_inner_ridgeEstimate_sub_le`) with the self-normalized bound for
vector-valued martingales (`LMLExplore.measure_exists_inner_ringInverse_designOp_ge_le`).

## Main statements

* `LMLExplore.measure_exists_sqrt_inner_ridgeEstimate_sub_ge_le`: the probability that the
  confidence ellipsoid fails to contain `θ` at some time is at most `δ` [LS, Theorem 20.5].
* `LMLExplore.le_measureReal_forall_sqrt_inner_ridgeEstimate_sub_lt`: the same, as a lower bound
  on the probability of the good event.
* `LMLExplore.le_measureReal_forall_sqrt_inner_ridgeEstimate_sub_lt_of_norm_le`: the good event
  with the radius `√λ ‖θ‖ + √(2σ² log (1 / δ) + σ² d log (1 + t L² / (λ d)))`, for features
  bounded by `L` [LS, Theorem 20.5 and (20.9)].

## References

* [AYPS] Y. Abbasi-Yadkori, D. Pál and Cs. Szepesvári, *Improved algorithms for linear stochastic
  bandits*, NeurIPS 2011, Theorem 2.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Theorem 20.5 and equation (20.9).
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Module
open scoped ENNReal NNReal InnerProductSpace

namespace LMLExplore

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]
  {𝓕 : Filtration ℕ mΩ} {x : ℕ → Ω → E} {η y : ℕ → Ω → ℝ} {σ2 : ℝ≥0} {lam δ : ℝ}

/-- **Confidence ellipsoids for ridge regression** [LS, Theorem 20.5]: for predictable features
`x`, a conditionally `σ²`-sub-Gaussian noise `η` with `σ² ≠ 0`, responses
`y t = ⟪θ, x t⟫ + η t`, `λ > 0` and `δ > 0`, the probability that for some `t`,
`√λ ‖θ‖ + √(2σ² log (1 / δ) + σ² log (det V_t / λ ^ d)) ≤ ‖θ̂_t - θ‖_{V_t}` is at most `δ`, where
`V_t = designOp λ x t` and `θ̂_t = ridgeEstimate λ x y t`. -/
theorem measure_exists_sqrt_inner_ridgeEstimate_sub_ge_le
    (hx : ∀ t, Measurable[𝓕 t] (x t)) (hη : ∀ t, Measurable[𝓕 (t + 1)] (η t))
    (hsub : ∀ t, HasCondSubgaussianMGF (𝓕 t) (𝓕.le t) (η t) σ2 P) (hσ : σ2 ≠ 0) (θ : E)
    (hy : ∀ t ω, y t ω = ⟪θ, x t ω⟫_ℝ + η t ω) (hlam : 0 < lam) (hδ : 0 < δ) :
    P {ω | ∃ t, √lam * ‖θ‖ + √(2 * σ2 * log (1 / δ) +
        σ2 * log (LinearMap.det (designOp lam (fun s ↦ x s ω) t : E →ₗ[ℝ] E) /
          lam ^ finrank ℝ E)) ≤
      √⟪ridgeEstimate lam (fun s ↦ x s ω) (fun s ↦ y s ω) t - θ,
        designOp lam (fun s ↦ x s ω) t
          (ridgeEstimate lam (fun s ↦ x s ω) (fun s ↦ y s ω) t - θ)⟫_ℝ} ≤
      ENNReal.ofReal δ := by
  have := FiniteDimensional.complete ℝ E
  refine (measure_mono fun ω hω ↦ ?_).trans
    (measure_exists_inner_ringInverse_designOp_ge_le hx hη hsub hσ hlam hδ)
  obtain ⟨t, ht⟩ := hω
  refine ⟨t, ?_⟩
  have h := ht.trans (sqrt_inner_ridgeEstimate_sub_le hlam (fun s ↦ x s ω) θ t (hy · ω))
  rwa [add_le_add_iff_left, Real.sqrt_le_sqrt_iff
    ((isPositive_designOp hlam.le _ t).ringInverse.inner_nonneg_right _)] at h

/-- **Confidence ellipsoids for ridge regression** [LS, Theorem 20.5], good-event form: under
the assumptions of `measure_exists_sqrt_inner_ridgeEstimate_sub_ge_le`, with probability at least
`1 - δ`, for all `t`,
`‖θ̂_t - θ‖_{V_t} < √λ ‖θ‖ + √(2σ² log (1 / δ) + σ² log (det V_t / λ ^ d))`. -/
theorem le_measureReal_forall_sqrt_inner_ridgeEstimate_sub_lt
    (hx : ∀ t, Measurable[𝓕 t] (x t)) (hη : ∀ t, Measurable[𝓕 (t + 1)] (η t))
    (hsub : ∀ t, HasCondSubgaussianMGF (𝓕 t) (𝓕.le t) (η t) σ2 P) (hσ : σ2 ≠ 0) (θ : E)
    (hy : ∀ t ω, y t ω = ⟪θ, x t ω⟫_ℝ + η t ω) (hlam : 0 < lam) (hδ : 0 < δ) :
    1 - δ ≤ P.real {ω | ∀ t,
      √⟪ridgeEstimate lam (fun s ↦ x s ω) (fun s ↦ y s ω) t - θ,
        designOp lam (fun s ↦ x s ω) t
          (ridgeEstimate lam (fun s ↦ x s ω) (fun s ↦ y s ω) t - θ)⟫_ℝ <
      √lam * ‖θ‖ + √(2 * σ2 * log (1 / δ) +
        σ2 * log (LinearMap.det (designOp lam (fun s ↦ x s ω) t : E →ₗ[ℝ] E) /
          lam ^ finrank ℝ E))} := by
  have := FiniteDimensional.complete ℝ E
  refine (le_measureReal_forall_inner_ringInverse_designOp_lt hx hη hsub hσ hlam hδ).trans
    (measureReal_mono fun ω hω t ↦ ?_)
  refine (sqrt_inner_ridgeEstimate_sub_le hlam (fun s ↦ x s ω) θ t (hy · ω)).trans_lt ?_
  rw [add_lt_add_iff_left]
  exact Real.sqrt_lt_sqrt ((isPositive_designOp hlam.le _ t).ringInverse.inner_nonneg_right _)
    (hω t)

/-- **Confidence ellipsoids for ridge regression with bounded features**
[LS, Theorem 20.5 and (20.9)]: under the assumptions of
`le_measureReal_forall_sqrt_inner_ridgeEstimate_sub_lt`, if moreover `‖x t‖ ≤ L` for all `t`,
then with probability at least `1 - δ`, for all `t`,
`‖θ̂_t - θ‖_{V_t} < √λ ‖θ‖ + √(2σ² log (1 / δ) + σ² d log (1 + t L² / (λ d)))`. -/
theorem le_measureReal_forall_sqrt_inner_ridgeEstimate_sub_lt_of_norm_le
    (hx : ∀ t, Measurable[𝓕 t] (x t)) (hη : ∀ t, Measurable[𝓕 (t + 1)] (η t))
    (hsub : ∀ t, HasCondSubgaussianMGF (𝓕 t) (𝓕.le t) (η t) σ2 P) (hσ : σ2 ≠ 0) (θ : E)
    (hy : ∀ t ω, y t ω = ⟪θ, x t ω⟫_ℝ + η t ω) {L : ℝ} (hL : ∀ t ω, ‖x t ω‖ ≤ L)
    (hlam : 0 < lam) (hδ : 0 < δ) :
    1 - δ ≤ P.real {ω | ∀ t,
      √⟪ridgeEstimate lam (fun s ↦ x s ω) (fun s ↦ y s ω) t - θ,
        designOp lam (fun s ↦ x s ω) t
          (ridgeEstimate lam (fun s ↦ x s ω) (fun s ↦ y s ω) t - θ)⟫_ℝ <
      √lam * ‖θ‖ + √(2 * σ2 * log (1 / δ) +
        σ2 * finrank ℝ E * log (1 + t * L ^ 2 / (lam * finrank ℝ E)))} := by
  refine (le_measureReal_forall_sqrt_inner_ridgeEstimate_sub_lt hx hη hsub hσ θ hy hlam
    hδ).trans (measureReal_mono fun ω hω t ↦ (hω t).trans_le ?_)
  have hdet : log (LinearMap.det (designOp lam (fun s ↦ x s ω) t : E →ₗ[ℝ] E) /
      lam ^ finrank ℝ E) ≤ finrank ℝ E * log (1 + t * L ^ 2 / (lam * finrank ℝ E)) := by
    rw [← log_pow]
    exact log_le_log (div_pos (det_designOp_pos hlam _ t) (pow_pos hlam _))
      (det_designOp_div_pow_le hlam _ fun s _ ↦ hL s ω)
  gcongr _ + √(_ + ?_)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hdet σ2.2

end LMLExplore
