/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Gaussian integrals of positive definite quadratic forms

For a positive invertible operator `A` on a finite-dimensional real inner product space `E` of
dimension `d`, `c > 0` and `s : E`,
`∫ θ, exp (⟪θ, s⟫ - c ⟪θ, A θ⟫ / 2) dθ = √((2π / c) ^ d / det A) * exp (⟪s, A⁻¹ s⟫ / (2c))`,
with respect to the Lebesgue measure of `E`. We diagonalize `A` in an orthonormal basis of
eigenvectors, which is a measure-preserving change of variables, and the integral becomes a
product of one-dimensional Gaussian integrals with a linear term.

This is the Gaussian integral behind the method of mixtures for vector-valued martingales.

## Main statements

* `LMLExplore.integral_exp_neg_mul_sq_add_mul`: `∫ x, exp (-b x² + c x) = √(π / b) exp (c² / (4b))`.
* `LMLExplore.integral_exp_neg_sum_mul_add`: its product version on `ι → ℝ`.
* `LMLExplore.integrable_exp_inner_sub_inner_apply`,
  `LMLExplore.integral_exp_inner_sub_inner_apply`: integrability and value of
  `θ ↦ exp (⟪θ, s⟫ - c ⟪θ, A θ⟫ / 2)` for a positive invertible operator `A`.
-/

public section

open MeasureTheory Real Finset Module
open scoped InnerProductSpace

namespace LMLExplore

/-- Completing the square: `exp (-b x² + c x) = exp (c² / (4b)) exp (-b (x - c / (2b))²)`. -/
private lemma exp_neg_mul_sq_add_mul_eq {b : ℝ} (hb : 0 < b) (c x : ℝ) :
    exp (-b * x ^ 2 + c * x) = exp (c ^ 2 / (4 * b)) * exp (-b * (x - c / (2 * b)) ^ 2) := by
  rw [← exp_add]
  congr 1
  field_simp
  ring

theorem integrable_exp_neg_mul_sq_add_mul {b : ℝ} (hb : 0 < b) (c : ℝ) :
    Integrable (fun x : ℝ ↦ exp (-b * x ^ 2 + c * x)) := by
  simp_rw [exp_neg_mul_sq_add_mul_eq hb c]
  exact ((integrable_exp_neg_mul_sq hb).comp_sub_right (c / (2 * b))).const_mul _

/-- **Gaussian integral with a linear term**: `∫ x, exp (-b x² + c x) = √(π / b) exp (c² / (4b))`
for `b > 0`. -/
theorem integral_exp_neg_mul_sq_add_mul {b : ℝ} (hb : 0 < b) (c : ℝ) :
    ∫ x : ℝ, exp (-b * x ^ 2 + c * x) = √(π / b) * exp (c ^ 2 / (4 * b)) := by
  simp_rw [exp_neg_mul_sq_add_mul_eq hb c]
  have h := integral_sub_right_eq_self (μ := volume) (fun x : ℝ ↦ exp (-b * x ^ 2)) (c / (2 * b))
  rw [integral_const_mul, h, integral_gaussian, mul_comm]

theorem integrable_exp_neg_sum_mul_add {ι : Type*} [Fintype ι] {b : ι → ℝ} (hb : ∀ i, 0 < b i)
    (c : ι → ℝ) :
    Integrable (fun v : ι → ℝ ↦ exp (-∑ i, b i * v i ^ 2 + ∑ i, c i * v i)) := by
  simp_rw [← sum_neg_distrib, ← sum_add_distrib, exp_sum, ← neg_mul]
  exact Integrable.fintype_prod (f := fun i (v : ℝ) ↦ exp (-b i * v ^ 2 + c i * v))
    fun i ↦ integrable_exp_neg_mul_sq_add_mul (hb i) (c i)

/-- Product form of the Gaussian integral with a linear term, on `ι → ℝ`. -/
theorem integral_exp_neg_sum_mul_add {ι : Type*} [Fintype ι] {b : ι → ℝ} (hb : ∀ i, 0 < b i)
    (c : ι → ℝ) :
    ∫ v : ι → ℝ, exp (-∑ i, b i * v i ^ 2 + ∑ i, c i * v i) =
      ∏ i, √(π / b i) * exp (c i ^ 2 / (4 * b i)) := by
  simp_rw [← sum_neg_distrib, ← sum_add_distrib, exp_sum, ← neg_mul]
  rw [integral_fintype_prod_volume_eq_prod (f := fun i (v : ℝ) ↦ exp (-b i * v ^ 2 + c i * v))]
  exact prod_congr rfl fun i _ ↦ integral_exp_neg_mul_sq_add_mul (hb i) (c i)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {A : E →L[ℝ] E} {c : ℝ}

omit [MeasurableSpace E] [BorelSpace E] in
/-- A positive invertible operator on a finite-dimensional real inner product space is diagonal,
with positive eigenvalues `μ`, in an orthonormal basis `b` of eigenvectors, and its determinant is
`∏ i, μ i`. -/
private lemma exists_orthonormalBasis_diag (hA : A.IsPositive) (hAu : IsUnit A) :
    ∃ (b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E) (μ : Fin (finrank ℝ E) → ℝ),
      (∀ θ i, b.repr (A θ) i = μ i * b.repr θ i) ∧ (∀ i, 0 < μ i) ∧
        LinearMap.det (A : E →ₗ[ℝ] E) = ∏ i, μ i := by
  have hT : (A : E →ₗ[ℝ] E).IsSymmetric := hA.isSymmetric
  refine ⟨hT.eigenvectorBasis rfl, hT.eigenvalues rfl, fun θ i ↦ ?_, fun i ↦ ?_, ?_⟩
  · simpa using hT.eigenvectorBasis_apply_self_apply rfl θ i
  · refine (hA.toLinearMap.nonneg_eigenvalues rfl i).lt_of_ne fun h0 ↦ ?_
    have h := hT.apply_eigenvectorBasis rfl i
    rw [← h0, RCLike.ofReal_zero, zero_smul, ContinuousLinearMap.coe_coe] at h
    have hb : hT.eigenvectorBasis rfl i = 0 := by
      rw [← A.ringInverse_apply_apply hAu (hT.eigenvectorBasis rfl i), h, map_zero]
    simpa [hb] using (hT.eigenvectorBasis rfl).orthonormal.1 i
  · simp [hT.det_eq_prod_eigenvalues rfl]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- In the coordinates `v` of an orthonormal basis `b` in which `A` is diagonal with entries `μ`,
the integrand `exp (⟪θ, s⟫ - c ⟪θ, A θ⟫ / 2)` is `exp (-∑ (c μᵢ / 2) vᵢ² + ∑ sᵢ vᵢ)`. -/
private lemma exp_inner_sub_inner_apply_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (μ : ι → ℝ) (hb : ∀ θ i, b.repr (A θ) i = μ i * b.repr θ i) (s : E) (v : ι → ℝ) :
    exp (⟪b.repr.symm (WithLp.toLp 2 v), s⟫_ℝ -
        c * ⟪b.repr.symm (WithLp.toLp 2 v), A (b.repr.symm (WithLp.toLp 2 v))⟫_ℝ / 2) =
      exp (-∑ i, c * μ i / 2 * v i ^ 2 + ∑ i, b.repr s i * v i) := by
  set θ := b.repr.symm (WithLp.toLp 2 v)
  have hθ (i : ι) : b.repr θ i = v i := by simp [θ]
  have hlin : ⟪θ, s⟫_ℝ = ∑ i, b.repr s i * v i := by
    rw [← b.repr.inner_map_map, PiLp.inner_apply]
    exact sum_congr rfl fun i _ ↦ by simp [hθ, mul_comm]
  have hquad : ⟪θ, A θ⟫_ℝ = ∑ i, μ i * v i ^ 2 := by
    rw [← b.repr.inner_map_map, PiLp.inner_apply]
    exact sum_congr rfl fun i _ ↦ by simp [hb, hθ]; ring
  have : c * (∑ i, μ i * v i ^ 2) / 2 = ∑ i, c * μ i / 2 * v i ^ 2 := by
    rw [mul_sum, sum_div]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [hlin, hquad]
  congr 1
  linarith

/-- The map `v ↦ b.repr.symm v` from `ι → ℝ` to `E` is measure preserving. -/
private lemma measurePreserving_repr_symm_toLp {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) :
    MeasurePreserving (fun v : ι → ℝ ↦ b.repr.symm (WithLp.toLp 2 v)) :=
  b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp ι)

omit [FiniteDimensional ℝ E] in
private lemma measurableEmbedding_repr_symm_toLp {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) :
    MeasurableEmbedding (fun v : ι → ℝ ↦ b.repr.symm (WithLp.toLp 2 v)) :=
  b.repr.symm.toHomeomorph.measurableEmbedding.comp (MeasurableEquiv.toLp 2 _).measurableEmbedding

/-- For a positive invertible operator `A` and `c > 0`, `θ ↦ exp (⟪θ, s⟫ - c ⟪θ, A θ⟫ / 2)` is
integrable. -/
theorem integrable_exp_inner_sub_inner_apply (hA : A.IsPositive) (hAu : IsUnit A) (hc : 0 < c)
    (s : E) :
    Integrable (fun θ : E ↦ exp (⟪θ, s⟫_ℝ - c * ⟪θ, A θ⟫_ℝ / 2)) := by
  obtain ⟨b, μ, hb, hμ, -⟩ := exists_orthonormalBasis_diag hA hAu
  rw [← (measurePreserving_repr_symm_toLp b).integrable_comp_emb
    (measurableEmbedding_repr_symm_toLp b)]
  have : (fun θ : E ↦ exp (⟪θ, s⟫_ℝ - c * ⟪θ, A θ⟫_ℝ / 2)) ∘
      (fun v ↦ b.repr.symm (WithLp.toLp 2 v)) =
      fun v ↦ exp (-∑ i, c * μ i / 2 * v i ^ 2 + ∑ i, b.repr s i * v i) :=
    funext fun v ↦ exp_inner_sub_inner_apply_eq b μ hb s v
  rw [this]
  exact integrable_exp_neg_sum_mul_add (fun i ↦ by have := hμ i; positivity) _

/-- **Gaussian integral of a positive definite quadratic form**: for a positive invertible
operator `A` on a real inner product space of dimension `d` and `c > 0`,
`∫ θ, exp (⟪θ, s⟫ - c ⟪θ, A θ⟫ / 2) = √((2π / c) ^ d / det A) * exp (⟪s, A⁻¹ s⟫ / (2c))`. -/
theorem integral_exp_inner_sub_inner_apply (hA : A.IsPositive) (hAu : IsUnit A) (hc : 0 < c)
    (s : E) :
    ∫ θ : E, exp (⟪θ, s⟫_ℝ - c * ⟪θ, A θ⟫_ℝ / 2) =
      √((2 * π / c) ^ finrank ℝ E / LinearMap.det (A : E →ₗ[ℝ] E)) *
        exp (⟪s, Ring.inverse A s⟫_ℝ / (2 * c)) := by
  obtain ⟨b, μ, hb, hμ, hdet⟩ := exists_orthonormalBasis_diag hA hAu
  rw [← (measurePreserving_repr_symm_toLp b).integral_comp
    (measurableEmbedding_repr_symm_toLp b)]
  simp_rw [exp_inner_sub_inner_apply_eq b μ hb s]
  rw [integral_exp_neg_sum_mul_add (fun i ↦ by have := hμ i; positivity)]
  -- `⟪s, A⁻¹ s⟫` in coordinates
  have hW (i : Fin (finrank ℝ E)) : b.repr (Ring.inverse A s) i = b.repr s i / μ i := by
    rw [eq_div_iff (hμ i).ne', mul_comm, ← hb, A.apply_ringInverse_apply hAu]
  have hinv : ⟪s, Ring.inverse A s⟫_ℝ = ∑ i, b.repr s i ^ 2 / μ i := by
    rw [← b.repr.inner_map_map, PiLp.inner_apply]
    exact sum_congr rfl fun i _ ↦ by simp [hW]; ring
  have h1 (i : Fin (finrank ℝ E)) : π / (c * μ i / 2) = 2 * π / c / μ i := by
    have := hμ i
    field_simp
  have h2 (i : Fin (finrank ℝ E)) :
      b.repr s i ^ 2 / (4 * (c * μ i / 2)) = b.repr s i ^ 2 / μ i / (2 * c) := by
    have := hμ i
    field_simp
    ring
  simp_rw [h1, h2]
  rw [prod_mul_distrib, ← sqrt_prod _ fun i _ ↦ by have := hμ i; positivity, ← exp_sum,
    ← sum_div, prod_div_distrib, prod_const, card_univ, Fintype.card_fin, hdet, hinv]

end LMLExplore
