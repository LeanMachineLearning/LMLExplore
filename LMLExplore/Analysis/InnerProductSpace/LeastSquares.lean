/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.MoorePenrose
public import LMLExplore.Analysis.InnerProductSpace.Ridge

/-!
# Least squares with a possibly singular design

Given covariates `x : ℕ → E` in a finite-dimensional real inner product space, responses
`y : ℕ → ℝ` and a regularization parameter `λ ≥ 0`, the *least-squares estimate* after `t`
observations is `θ̂_t = V_t⁺ ∑_{s < t} y s • x s`, where `V_t = designOp (λ • 1) x t` and `V_t⁺` is
the Moore–Penrose inverse. Unlike the ridge estimate `V_t⁻¹ ∑_{s < t} y s • x s`, it is defined
by a formula that is meaningful for `λ = 0`, when `V_t = ∑_{s < t} x s ⊗ x s` is singular as soon
as the covariates do not span `E`. This is the estimator of phased elimination with optimal designs
[LS, Chapter 22], whose designs need not span the space.

For every `λ ≥ 0`, `θ̂_t` solves the normal equations `V_t θ̂_t = ∑_{s < t} y s • x s` and
minimizes the regularized squared loss `L_t(θ) = ∑_{s < t} (y s - ⟪θ, x s⟫)² + λ ‖θ‖²`; for
`λ > 0` it is the ridge estimate. For `λ = 0` it lies in the span of the covariates and is the
least-squares solution of minimal norm: every minimizer `θ` of `L_t` satisfies
`‖θ‖² = ‖θ̂_t‖² + ‖θ - θ̂_t‖²`.

In the linear model `y s = ⟪θ, x s⟫ + η s` with `λ = 0`, the error of the estimate in a direction
`v` of the span of the covariates has no bias term:
`⟪v, θ̂_t - θ⟫ = ∑_{s < t} ⟪V_t⁺ v, x s⟫ η s`, a linear combination of the noise whose
coefficients have squared norm `∑_{s < t} ⟪V_t⁺ v, x s⟫² = ‖v‖²_{V_t⁺} = ⟪v, V_t⁺ v⟫`. This is the
deterministic part of the fixed-design confidence bound [LS, (20.2)].

## Main definitions

* `LMLExplore.leastSquaresEstimate lam x y t`: the least-squares estimate `θ̂_t`.

## Main statements

* `LMLExplore.designOp_leastSquaresEstimate`: the normal equations, for `λ ≥ 0`.
* `LMLExplore.isMinOn_ridgeLoss_leastSquaresEstimate`: `θ̂_t` minimizes `L_t` for `λ ≥ 0`
  [LS, (19.4)–(19.6)].
* `LMLExplore.leastSquaresEstimate_eq_ridgeEstimate`: for `λ > 0`, `θ̂_t` is the ridge estimate.
* `LMLExplore.leastSquaresEstimate_zero_mem_span`,
  `LMLExplore.norm_sq_eq_norm_sq_leastSquaresEstimate_add_of_ridgeLoss_le`: for `λ = 0`, `θ̂_t`
  lies in the span of the covariates and is the minimizer of minimal norm.
* `LMLExplore.inner_leastSquaresEstimate_sub_eq_sum`: the error `⟪v, θ̂_t - θ⟫` in the linear model,
  for `λ = 0` and `v` in the span of the covariates.
* `LMLExplore.sum_inner_moorePenroseInverse_designOp_sq`: `∑_{s < t} ⟪V_t⁺ v, x s⟫² = ⟪v, V_t⁺ v⟫`
  for `λ = 0`, and `LMLExplore.inner_moorePenroseInverse_designOp_pos`: this weighted norm is
  positive for nonzero `v` in the span of the covariates.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Sections 19.3, 20.1 and 22.
-/

public section

open Finset
open ContinuousLinearMap (isPositive_zero isPositive_smul_one)
open scoped InnerProductSpace

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {lam : ℝ} {x : ℕ → E} {y : ℕ → ℝ} {t : ℕ}

/-- The **least-squares estimate** `θ̂_t = V_t⁺ ∑_{s < t} y s • x s`, where
`V_t = designOp (λ • 1) x t` and `V_t⁺` is its Moore–Penrose inverse. -/
noncomputable def leastSquaresEstimate (lam : ℝ) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) : E :=
  (designOp (lam • 1) x t : E →ₗ[ℝ] E).moorePenroseInverse (∑ s ∈ range t, y s • x s)

/-- The defining equation of `leastSquaresEstimate`. -/
theorem leastSquaresEstimate_def (lam : ℝ) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) :
    leastSquaresEstimate lam x y t =
      (designOp (lam • 1) x t : E →ₗ[ℝ] E).moorePenroseInverse (∑ s ∈ range t, y s • x s) :=
  (rfl)

/-- The least-squares estimate `θ̂_t` only depends on the covariates `x s` and the responses `y s`
for `s < t`. -/
theorem leastSquaresEstimate_congr {x' : ℕ → E} {y' : ℕ → ℝ} (hx : ∀ s < t, x s = x' s)
    (hy : ∀ s < t, y s = y' s) :
    leastSquaresEstimate lam x y t = leastSquaresEstimate lam x' y' t := by
  rw [leastSquaresEstimate, leastSquaresEstimate, designOp_congr hx,
    sum_congr rfl fun s hs ↦ by rw [hx s (mem_range.1 hs), hy s (mem_range.1 hs)]]

/-- For `λ > 0`, the least-squares estimate is the ridge estimate `V_t⁻¹ ∑_{s < t} y s • x s`. -/
theorem leastSquaresEstimate_eq_ridgeEstimate (hlam : 0 < lam) (x : ℕ → E) (y : ℕ → ℝ)
    (t : ℕ) : leastSquaresEstimate lam x y t = ridgeEstimate lam x y t := by
  rw [leastSquaresEstimate,
    ContinuousLinearMap.moorePenroseInverse_eq_ringInverse (isUnit_designOp_smul_one hlam x t),
    ContinuousLinearMap.coe_coe, ridgeEstimate_def]

/-- The **normal equations**: for `λ ≥ 0`, `V_t θ̂_t = ∑_{s < t} y s • x s`. -/
theorem designOp_leastSquaresEstimate (hlam : 0 ≤ lam) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) :
    designOp (lam • 1) x t (leastSquaresEstimate lam x y t) = ∑ s ∈ range t, y s • x s :=
  (designOp (lam • 1) x t : E →ₗ[ℝ] E).isMoorePenroseInverse_moorePenroseInverse
    |>.apply_apply_of_mem_range <| span_le_range_designOp (isPositive_smul_one hlam) x t <|
      Submodule.sum_smul_mem _ _ fun s hs ↦
        Submodule.subset_span ⟨s, Set.mem_Iio.2 (mem_range.1 hs), rfl⟩

/-- For `λ ≥ 0`, the regularized squared loss is
`L_t(θ) = L_t(θ̂_t) + ⟪θ - θ̂_t, V_t (θ - θ̂_t)⟫`. -/
theorem ridgeLoss_eq_ridgeLoss_leastSquaresEstimate_add (hlam : 0 ≤ lam) (x : ℕ → E)
    (y : ℕ → ℝ) (t : ℕ) (θ : E) :
    ridgeLoss lam x y t θ = ridgeLoss lam x y t (leastSquaresEstimate lam x y t) +
      ⟪θ - leastSquaresEstimate lam x y t,
        designOp (lam • 1) x t (θ - leastSquaresEstimate lam x y t)⟫_ℝ :=
  ridgeLoss_eq_ridgeLoss_add_of_designOp_apply_eq (designOp_leastSquaresEstimate hlam x y t) θ

/-- For `λ ≥ 0`, the least-squares estimate minimizes the regularized squared loss. -/
theorem ridgeLoss_leastSquaresEstimate_le (hlam : 0 ≤ lam) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ)
    (θ : E) : ridgeLoss lam x y t (leastSquaresEstimate lam x y t) ≤ ridgeLoss lam x y t θ := by
  rw [ridgeLoss_eq_ridgeLoss_leastSquaresEstimate_add hlam x y t θ]
  exact le_add_of_nonneg_right ((isPositive_designOp_smul_one hlam x t).inner_nonneg_right _)

/-- For `λ ≥ 0`, the least-squares estimate is a minimizer of the regularized squared loss on
the whole space. -/
theorem isMinOn_ridgeLoss_leastSquaresEstimate (hlam : 0 ≤ lam) (x : ℕ → E) (y : ℕ → ℝ)
    (t : ℕ) : IsMinOn (ridgeLoss lam x y t) Set.univ (leastSquaresEstimate lam x y t) :=
  isMinOn_univ_iff.2 (ridgeLoss_leastSquaresEstimate_le hlam x y t)

/-! ### Unregularized least squares -/

/-- The unregularized least-squares estimate lies in the span of the covariates. -/
theorem leastSquaresEstimate_zero_mem_span (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) :
    leastSquaresEstimate 0 x y t ∈ Submodule.span ℝ (x '' Set.Iio t) := by
  rw [leastSquaresEstimate, zero_smul, ← range_designOp_zero,
    ← (isPositive_designOp isPositive_zero x t).isSymmetric.range_moorePenroseInverse]
  exact LinearMap.mem_range_self _ _

/-- The unregularized least-squares estimate is the **least-squares solution of minimal norm**:
every minimizer `θ` of the squared loss `L_t(θ) = ∑_{s < t} (y s - ⟪θ, x s⟫)²` satisfies
`‖θ‖² = ‖θ̂_t‖² + ‖θ - θ̂_t‖²`. -/
theorem norm_sq_eq_norm_sq_leastSquaresEstimate_add_of_ridgeLoss_le {θ : E}
    (h : ridgeLoss 0 x y t θ ≤ ridgeLoss 0 x y t (leastSquaresEstimate 0 x y t)) :
    ‖θ‖ ^ 2 = ‖leastSquaresEstimate 0 x y t‖ ^ 2 + ‖θ - leastSquaresEstimate 0 x y t‖ ^ 2 := by
  set u := leastSquaresEstimate 0 x y t
  -- `θ - u` is orthogonal to every covariate, since `∑_{s < t} ⟪x s, θ - u⟫² = 0`
  rw [ridgeLoss_eq_ridgeLoss_leastSquaresEstimate_add le_rfl x y t θ,
    inner_designOp_smul_one_apply_self, zero_mul, zero_add] at h
  have hsum : ∑ s ∈ range t, ⟪x s, θ - u⟫_ℝ ^ 2 = 0 :=
    le_antisymm (by linarith) (sum_nonneg fun _ _ ↦ sq_nonneg _)
  have h0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1
    (span_le_orthogonal_singleton_of_sum_inner_sq_eq_zero hsum
      (leastSquaresEstimate_zero_mem_span x y t))
  have := norm_add_sq_real u (θ - u)
  rw [add_sub_cancel, real_inner_comm, h0] at this
  linarith

/-- The unregularized least-squares estimate has the smallest norm among the minimizers of the
squared loss. -/
theorem norm_leastSquaresEstimate_le_of_ridgeLoss_le {θ : E}
    (h : ridgeLoss 0 x y t θ ≤ ridgeLoss 0 x y t (leastSquaresEstimate 0 x y t)) :
    ‖leastSquaresEstimate 0 x y t‖ ≤ ‖θ‖ := by
  have := norm_sq_eq_norm_sq_leastSquaresEstimate_add_of_ridgeLoss_le h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by nlinarith [sq_nonneg ‖θ - leastSquaresEstimate 0 x y t‖])

/-- The unregularized least-squares estimate is the unique minimizer of the squared loss of
minimal norm. -/
theorem eq_leastSquaresEstimate_of_ridgeLoss_le_of_norm_le {θ : E}
    (h : ridgeLoss 0 x y t θ ≤ ridgeLoss 0 x y t (leastSquaresEstimate 0 x y t))
    (hθ : ‖θ‖ ≤ ‖leastSquaresEstimate 0 x y t‖) : θ = leastSquaresEstimate 0 x y t := by
  have := norm_sq_eq_norm_sq_leastSquaresEstimate_add_of_ridgeLoss_le h
  have h2 : ‖θ - leastSquaresEstimate 0 x y t‖ ^ 2 = 0 := le_antisymm
    (by nlinarith [norm_nonneg θ, norm_nonneg (leastSquaresEstimate 0 x y t)]) (sq_nonneg _)
  rw [← sub_eq_zero]
  simpa using h2

/-! ### The linear model with a fixed design -/

/-- The weighted norm `‖v‖²_{V_t⁺}` of the unregularized design operator `V_t = V_t(0)` is the
squared norm of the coefficients `⟪V_t⁺ v, x s⟫` of the orthogonal projection of `v` onto the
span of the covariates, `V_t V_t⁺ v = ∑_{s < t} ⟪V_t⁺ v, x s⟫ • x s`:
`∑_{s < t} ⟪V_t⁺ v, x s⟫² = ⟪v, V_t⁺ v⟫`. -/
theorem sum_inner_moorePenroseInverse_designOp_sq (x : ℕ → E) (t : ℕ) (v : E) :
    ∑ s ∈ range t, ⟪(designOp 0 x t : E →ₗ[ℝ] E).moorePenroseInverse v, x s⟫_ℝ ^ 2 =
      ⟪v, (designOp 0 x t : E →ₗ[ℝ] E).moorePenroseInverse v⟫_ℝ := by
  have hsymm := (isPositive_designOp isPositive_zero x t).isSymmetric
    |>.moorePenroseInverse
  -- `∑_{s < t} ⟪V⁺ v, x s⟫² = ⟪V⁺ v, V (V⁺ v)⟫ = ⟪v, V⁺ (V (V⁺ v))⟫ = ⟪v, V⁺ v⟫`
  have h := inner_designOp_apply_self 0 x t
    ((designOp 0 x t : E →ₗ[ℝ] E).moorePenroseInverse v)
  simp only [zero_apply, inner_zero_right, zero_add, real_inner_comm _ (x _),
    ← ContinuousLinearMap.coe_coe] at h
  rw [← h, hsymm, (designOp 0 x t : E →ₗ[ℝ] E).isMoorePenroseInverse_moorePenroseInverse
    |>.apply_apply_apply']

/-- The weighted norm `‖v‖²_{V_t⁺}` of the unregularized design operator is positive for every
nonzero `v` in the span of the covariates. -/
theorem inner_moorePenroseInverse_designOp_pos {v : E}
    (hv : v ∈ Submodule.span ℝ (x '' Set.Iio t)) (hv0 : v ≠ 0) :
    0 < ⟪v, (designOp 0 x t : E →ₗ[ℝ] E).moorePenroseInverse v⟫_ℝ :=
  (isPositive_designOp isPositive_zero x t).toLinearMap.re_inner_moorePenroseInverse_apply_pos
    (range_designOp_zero x t ▸ hv) hv0

/-- **Error of the unregularized least-squares estimate** in the linear model
`y s = ⟪θ, x s⟫ + η s`: for `v` in the span of the covariates,
`⟪v, θ̂_t - θ⟫ = ∑_{s < t} ⟪V_t⁺ v, x s⟫ η s`, where `V_t = V_t(0)`. -/
theorem inner_leastSquaresEstimate_sub_eq_sum {η : ℕ → ℝ} (θ : E)
    (hy : ∀ s, y s = ⟪θ, x s⟫_ℝ + η s) {v : E} (hv : v ∈ Submodule.span ℝ (x '' Set.Iio t)) :
    ⟪v, leastSquaresEstimate 0 x y t - θ⟫_ℝ =
      ∑ s ∈ range t, ⟪(designOp 0 x t : E →ₗ[ℝ] E).moorePenroseInverse v, x s⟫_ℝ * η s := by
  rw [leastSquaresEstimate_def, zero_smul]
  set V : E →ₗ[ℝ] E := (designOp 0 x t : E →ₗ[ℝ] E)
  have hV := (isPositive_designOp isPositive_zero x t).isSymmetric
  have hb : ∑ s ∈ range t, y s • x s = V θ + ∑ s ∈ range t, η s • x s := by
    simp only [V, ContinuousLinearMap.coe_coe, designOp_apply, zero_apply,
      zero_add, hy, add_smul, sum_add_distrib, real_inner_comm θ]
  -- the bias `⟪v, V⁺ (V θ) - θ⟫` vanishes for `v = V w` in the range of `V`
  obtain ⟨w, rfl⟩ : v ∈ LinearMap.range V := by rwa [range_designOp_zero]
  have hbias : ⟪V w, V.moorePenroseInverse (V θ)⟫_ℝ = ⟪V w, θ⟫_ℝ := by
    rw [hV, V.isMoorePenroseInverse_moorePenroseInverse.apply_apply_apply, ← hV]
  rw [hb, map_add, inner_sub_right, inner_add_right, hbias, add_sub_cancel_left,
    ← hV.moorePenroseInverse, inner_sum]
  exact sum_congr rfl fun s _ ↦ by rw [real_inner_smul_right, mul_comm]

end LMLExplore
