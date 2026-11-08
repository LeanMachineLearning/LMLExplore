/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.Positive
public import LMLExplore.Analysis.InnerProductSpace.RankOne
public import TauCeti.Analysis.InnerProductSpace.Frame
public import TauCeti.Analysis.InnerProductSpace.Spectrum

/-!
# Design operators of regularized least squares

For an operator `V₀` and a sequence `x : ℕ → E` in a real inner product space, the *design
operator* with regularizer `V₀` is `V_t(V₀) = V₀ + ∑_{s < t} x s ⊗ x s`, where
`x ⊗ x = rankOne ℝ x x` is the operator `v ↦ ⟪x, v⟫ • x`. It is the regularized Gram operator of
least squares and of linear bandit algorithms; ridge regression with parameter `λ` uses
`V_t(λ) = V_t(λ • 1)`. Its unregularized part is Tau Ceti's frame operator of the family
`(x s)_{s < t}`. The weighted norm `‖v‖²_{V⁻¹}` is `⟪v, V⁻¹ v⟫`, with `V⁻¹ = Ring.inverse V`; it
is nonnegative for positive `V` by `ContinuousLinearMap.IsPositive.ringInverse`.

A positive definite regularizer is a positive invertible operator `V₀`
(`V₀.IsPositive` and `IsUnit V₀`); in finite dimension these are the operators with positive
eigenvalues. The ridge regularizer `λ • 1` is one for `λ > 0`
(`ContinuousLinearMap.isPositive_smul_one`, `ContinuousLinearMap.isUnit_smul_one`), with
`det (λ • 1) = λ ^ d` (`ContinuousLinearMap.det_smul_one`) and `trace (λ • 1) = λ d`
(`ContinuousLinearMap.trace_smul_one`).

## Main definitions

* `LMLExplore.designOp V₀ x t`: the design operator `V_t(V₀)`.

## Main statements

* `LMLExplore.designOp_smul_one_apply`, `LMLExplore.inner_designOp_smul_one_apply_self`:
  `V_t(λ) v = λ • v + ∑_{s < t} ⟪x s, v⟫ • x s` and `⟪v, V_t(λ) v⟫ = λ ‖v‖² + ∑_{s < t} ⟪x s, v⟫²`.
* `LMLExplore.designOp_congr`: `V_t(V₀)` only depends on the first `t` vectors.
* `LMLExplore.toLinearMap_designOp`: `V_t(V₀) = V₀ + frameOperator ℝ (fun s : Fin t ↦ x s)`.
* `LMLExplore.isPositive_designOp`: `V_t(V₀)` is positive for a positive `V₀`;
  `LMLExplore.mul_norm_sq_le_inner_designOp_apply`: `λ ‖v‖² ≤ ⟪v, V_t(λ) v⟫`.
* `LMLExplore.isUnit_designOp`: `V_t(V₀)` is invertible for a positive definite `V₀`.
* `LMLExplore.span_le_range_designOp`: for a positive `V₀`, the vectors `x s` with `s < t` lie in
  the range of `V_t(V₀)`; `LMLExplore.range_designOp_zero`: the range of the unregularized design
  operator `V_t(0)` is the span of `x 0, …, x (t - 1)`.
* `LMLExplore.mul_inner_ringInverse_designOp_apply_le`: `λ ‖v‖²_{V_t(λ)⁻¹} ≤ ‖v‖²` for `λ > 0`.
* `LMLExplore.ringInverse_designOp_succ`: the rank-one update of the inverse
  (Sherman–Morrison formula).
* `LMLExplore.det_designOp_succ`: `det V_{t+1} = det V_t * (1 + ‖x t‖²_{V_t⁻¹})`, and
  `LMLExplore.det_designOp_eq_mul_prod`: `det V_t = det V₀ * ∏_{s < t} (1 + ‖x s‖²_{V_s⁻¹})`.
* `LMLExplore.trace_designOp`: `trace V_t(V₀) = trace V₀ + ∑_{s < t} ‖x s‖²`, and
  `LMLExplore.det_designOp_le`: `det V_t(V₀) ≤ ((trace V₀ + ∑_{s < t} ‖x s‖²) / d) ^ d` for a
  positive `V₀`.
* `LMLExplore.log_det_designOp_div_le`: if `‖x s‖ ≤ L` for `s < t`, then
  `log (det V_t(V₀) / det V₀) ≤ d log ((trace V₀ + t L²) / (d det (V₀) ^ (1 / d)))`
  [LS, Lemma 19.4]; for `V₀ = λ • 1` it is `LMLExplore.log_det_designOp_div_pow_le`,
  `log (det V_t(λ) / λ ^ d) ≤ d log (1 + t L² / (λ d))`, the logarithmic form of
  `LMLExplore.det_designOp_div_pow_le`: `det V_t(λ) / λ ^ d ≤ (1 + t L² / (λ d)) ^ d` [LS, (20.9)].

The design operator, its determinant recursion `det_designOp_succ` and the bound
`det_designOp_div_pow_le` follow the matrix versions `regGram`, `det_regGram_succ` and
`log_det_regGram_le` of the LMLPapers project (Rémy Degenne,
<https://github.com/LeanMachineLearning/LMLPapers>), restated here for operators with new proofs.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 19.2, Lemma 19.4 and equations (19.9) and (20.9).
-/

public section

open ContinuousLinearMap InnerProductSpace Finset Module
open scoped InnerProductSpace

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {V₀ : E →L[ℝ] E} {lam : ℝ}

/-- The **design operator** `V_t(V₀) = V₀ + ∑_{s < t} x s ⊗ x s` with regularizer `V₀`, where
`x ⊗ x` is the rank-one operator `v ↦ ⟪x, v⟫ • x`. Ridge regression with parameter `λ` uses
`V₀ = λ • 1`. -/
noncomputable def designOp (V₀ : E →L[ℝ] E) (x : ℕ → E) (t : ℕ) : E →L[ℝ] E :=
  V₀ + ∑ s ∈ range t, rankOne ℝ (x s) (x s)

/-- The defining equation of `designOp`. -/
theorem designOp_def (V₀ : E →L[ℝ] E) (x : ℕ → E) (t : ℕ) :
    designOp V₀ x t = V₀ + ∑ s ∈ range t, rankOne ℝ (x s) (x s) :=
  (rfl)

/-- Evaluation of the design operator: `V_t(V₀) v = V₀ v + ∑_{s < t} ⟪x s, v⟫ • x s`. -/
@[simp]
theorem designOp_apply (V₀ : E →L[ℝ] E) (x : ℕ → E) (t : ℕ) (v : E) :
    designOp V₀ x t v = V₀ v + ∑ s ∈ range t, ⟪x s, v⟫_ℝ • x s := by
  simp [designOp]

@[simp]
theorem designOp_zero (V₀ : E →L[ℝ] E) (x : ℕ → E) : designOp V₀ x 0 = V₀ := by
  simp [designOp]

/-- The design operator `V_t(V₀)` only depends on the vectors `x s` for `s < t`. -/
theorem designOp_congr {x x' : ℕ → E} {t : ℕ} (h : ∀ s < t, x s = x' s) :
    designOp V₀ x t = designOp V₀ x' t := by
  rw [designOp, designOp, sum_congr rfl fun s hs ↦ by rw [h s (mem_range.1 hs)]]

/-- The design operator is updated by a rank-one term at each step. -/
theorem designOp_succ (V₀ : E →L[ℝ] E) (x : ℕ → E) (t : ℕ) :
    designOp V₀ x (t + 1) = designOp V₀ x t + rankOne ℝ (x t) (x t) := by
  rw [designOp, designOp, sum_range_succ, add_assoc]

/-- The quadratic form of the design operator:
`⟪v, V_t(V₀) v⟫ = ⟪v, V₀ v⟫ + ∑_{s < t} ⟪x s, v⟫²`. -/
theorem inner_designOp_apply_self (V₀ : E →L[ℝ] E) (x : ℕ → E) (t : ℕ) (v : E) :
    ⟪v, designOp V₀ x t v⟫_ℝ = ⟪v, V₀ v⟫_ℝ + ∑ s ∈ range t, ⟪x s, v⟫_ℝ ^ 2 := by
  rw [designOp_apply, inner_add_right, inner_sum]
  congr 1
  refine sum_congr rfl fun s _ ↦ ?_
  rw [inner_smul_right, real_inner_comm (x s) v, sq]

/-- Evaluation of the design operator with the ridge regularizer:
`V_t(λ) v = λ • v + ∑_{s < t} ⟪x s, v⟫ • x s`. -/
theorem designOp_smul_one_apply (lam : ℝ) (x : ℕ → E) (t : ℕ) (v : E) :
    designOp (lam • 1) x t v = lam • v + ∑ s ∈ range t, ⟪x s, v⟫_ℝ • x s := by
  rw [designOp_apply, smul_apply, one_apply_eq_self]

/-- The quadratic form of the design operator with the ridge regularizer:
`⟪v, V_t(λ) v⟫ = λ ‖v‖² + ∑_{s < t} ⟪x s, v⟫²`. -/
theorem inner_designOp_smul_one_apply_self (lam : ℝ) (x : ℕ → E) (t : ℕ) (v : E) :
    ⟪v, designOp (lam • 1) x t v⟫_ℝ = lam * ‖v‖ ^ 2 + ∑ s ∈ range t, ⟪x s, v⟫_ℝ ^ 2 := by
  rw [inner_designOp_apply_self, smul_apply, one_apply_eq_self, real_inner_smul_right,
    real_inner_self_eq_norm_sq]

/-- The design operator is `V₀` plus Tau Ceti's frame operator of `(x s)_{s < t}`. -/
theorem toLinearMap_designOp (V₀ : E →L[ℝ] E) (x : ℕ → E) (t : ℕ) :
    (designOp V₀ x t : E →ₗ[ℝ] E) =
      (V₀ : E →ₗ[ℝ] E) + TauCeti.frameOperator ℝ (fun s : Fin t ↦ x s) := by
  ext v
  simp [TauCeti.frameOperator_apply,
    Fin.sum_univ_eq_sum_range (fun s ↦ ⟪x s, v⟫_ℝ • x s)]

/-- The design operator is positive for a positive regularizer `V₀`. -/
theorem isPositive_designOp (hV₀ : V₀.IsPositive) (x : ℕ → E) (t : ℕ) :
    (designOp V₀ x t).IsPositive :=
  hV₀.add (isPositive_sum _ fun _ _ ↦ isPositive_rankOne_self _)

/-- The design operator `V_t(λ)` is positive for `λ ≥ 0`. -/
theorem isPositive_designOp_smul_one (hlam : 0 ≤ lam) (x : ℕ → E) (t : ℕ) :
    (designOp (lam • 1) x t).IsPositive :=
  isPositive_designOp (isPositive_smul_one hlam) x t

/-- The coercivity bound `λ ‖v‖² ≤ ⟪v, V_t(λ) v⟫`, valid for every `λ`. -/
theorem mul_norm_sq_le_inner_designOp_apply (lam : ℝ) (x : ℕ → E) (t : ℕ) (v : E) :
    lam * ‖v‖ ^ 2 ≤ ⟪v, designOp (lam • 1) x t v⟫_ℝ := by
  rw [inner_designOp_smul_one_apply_self]
  exact le_add_of_nonneg_right (sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- For a positive definite regularizer `V₀` (positive and invertible), the design operator is
invertible. -/
theorem isUnit_designOp (hV₀ : V₀.IsPositive) (hV₀u : IsUnit V₀) (x : ℕ → E) (t : ℕ) :
    IsUnit (designOp V₀ x t) := by
  induction t with
  | zero => rwa [designOp_zero]
  | succ t ih =>
    rw [designOp_succ]
    exact isUnit_add_rankOne ih _ _
      ((isPositive_designOp hV₀ x t).one_add_inner_ringInverse_pos _).ne'

/-- The design operator `V_t(λ)` is invertible for `λ > 0`. -/
theorem isUnit_designOp_smul_one (hlam : 0 < lam) (x : ℕ → E) (t : ℕ) :
    IsUnit (designOp (lam • 1) x t) :=
  isUnit_designOp (isPositive_smul_one hlam.le) (isUnit_smul_one hlam.ne') x t

/-- For `λ > 0`, `λ ‖v‖²_{V_t(λ)⁻¹} ≤ ‖v‖²`, that is `V_t(λ)⁻¹ ≤ λ⁻¹ • 1`. -/
theorem mul_inner_ringInverse_designOp_apply_le (hlam : 0 < lam) (x : ℕ → E) (t : ℕ) (v : E) :
    lam * ⟪v, Ring.inverse (designOp (lam • 1) x t) v⟫_ℝ ≤ ‖v‖ ^ 2 := by
  set u := Ring.inverse (designOp (lam • 1) x t) v
  have hu : designOp (lam • 1) x t u = v :=
    ContinuousLinearMap.apply_ringInverse_apply (isUnit_designOp_smul_one hlam x t) v
  -- `λ ‖u‖² ≤ ⟪u, V u⟫ = ⟪u, v⟫ ≤ ‖u‖ ‖v‖`, hence `λ ‖u‖ ≤ ‖v‖` and `λ ⟪v, u⟫ ≤ ‖v‖²`
  have h1 := mul_norm_sq_le_inner_designOp_apply lam x t u
  rw [hu] at h1
  have h2 : ⟪u, v⟫_ℝ ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
  have h3 : lam * ‖u‖ ≤ ‖v‖ := by
    rcases (norm_nonneg u).eq_or_lt with h | h
    · rw [← h, mul_zero]
      exact norm_nonneg v
    · nlinarith
  rw [real_inner_comm]
  nlinarith [norm_nonneg v, norm_nonneg u]

/-- **Sherman–Morrison formula** for the design operator: for a positive definite regularizer
`V₀`, `V_{t+1}⁻¹ = V_t⁻¹ - (1 + ‖x t‖²_{V_t⁻¹})⁻¹ • (V_t⁻¹ x t) ⊗ (V_t⁻¹ x t)`. -/
theorem ringInverse_designOp_succ (hV₀ : V₀.IsPositive) (hV₀u : IsUnit V₀) (x : ℕ → E) (t : ℕ) :
    Ring.inverse (designOp V₀ x (t + 1)) = Ring.inverse (designOp V₀ x t) -
      (1 + ⟪x t, Ring.inverse (designOp V₀ x t) (x t)⟫_ℝ)⁻¹ •
        rankOne ℝ (Ring.inverse (designOp V₀ x t) (x t))
          (Ring.inverse (designOp V₀ x t) (x t)) := by
  rw [designOp_succ]
  exact ringInverse_add_rankOne_of_isSymmetric (isUnit_designOp hV₀ hV₀u x t)
    (isPositive_designOp hV₀ x t).isSymmetric (x t) (x t)
    ((isPositive_designOp hV₀ x t).one_add_inner_ringInverse_pos _).ne'

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The determinant of the design operator after a rank-one update [LS, (19.9)]: for a positive
definite regularizer `V₀`, `det V_{t+1} = det V_t * (1 + ‖x t‖²_{V_t⁻¹})`. -/
theorem det_designOp_succ (hV₀ : V₀.IsPositive) (hV₀u : IsUnit V₀) (x : ℕ → E) (t : ℕ) :
    LinearMap.det (designOp V₀ x (t + 1) : E →ₗ[ℝ] E) =
      LinearMap.det (designOp V₀ x t : E →ₗ[ℝ] E) *
        (1 + ⟪x t, Ring.inverse (designOp V₀ x t) (x t)⟫_ℝ) := by
  rw [designOp_succ, det_add_rankOne (isUnit_designOp hV₀ hV₀u x t)]

/-- For a positive definite regularizer `V₀`,
`det V_t = det V₀ * ∏_{s < t} (1 + ‖x s‖²_{V_s⁻¹})`. -/
theorem det_designOp_eq_mul_prod (hV₀ : V₀.IsPositive) (hV₀u : IsUnit V₀) (x : ℕ → E) (t : ℕ) :
    LinearMap.det (designOp V₀ x t : E →ₗ[ℝ] E) =
      LinearMap.det (V₀ : E →ₗ[ℝ] E) *
        ∏ s ∈ range t, (1 + ⟪x s, Ring.inverse (designOp V₀ x s) (x s)⟫_ℝ) := by
  rw [det_eq_mul_prod_of_add_rankOne (designOp_succ V₀ x) (isUnit_designOp hV₀ hV₀u x),
    designOp_zero]

/-- The determinant of the design operator is positive for a positive definite regularizer
`V₀`. -/
theorem det_designOp_pos (hV₀ : V₀.IsPositive) (hV₀u : IsUnit V₀) (x : ℕ → E) (t : ℕ) :
    0 < LinearMap.det (designOp V₀ x t : E →ₗ[ℝ] E) :=
  (isPositive_designOp hV₀ x t).toLinearMap.det_pos
    ((LinearMap.isUnit_iff_ker_eq_bot _).1 ((isUnit_designOp hV₀ hV₀u x t).map toLinearMapRingHom))

/-- The determinant of the design operator `V_t(λ)` is positive for `λ > 0`. -/
theorem det_designOp_smul_one_pos (hlam : 0 < lam) (x : ℕ → E) (t : ℕ) :
    0 < LinearMap.det (designOp (lam • 1) x t : E →ₗ[ℝ] E) :=
  det_designOp_pos (isPositive_smul_one hlam.le) (isUnit_smul_one hlam.ne') x t

/-- The trace of the design operator: `trace V_t(V₀) = trace V₀ + ∑_{s < t} ‖x s‖²`. -/
theorem trace_designOp (V₀ : E →L[ℝ] E) (x : ℕ → E) (t : ℕ) :
    LinearMap.trace ℝ E (designOp V₀ x t : E →ₗ[ℝ] E) =
      LinearMap.trace ℝ E (V₀ : E →ₗ[ℝ] E) + ∑ s ∈ range t, ‖x s‖ ^ 2 := by
  simp [designOp, map_sum, InnerProductSpace.trace_rankOne]

/-- For a positive regularizer `V₀`, `det V_t(V₀) ≤ ((trace V₀ + ∑_{s < t} ‖x s‖²) / d) ^ d`. -/
theorem det_designOp_le (hV₀ : V₀.IsPositive) (x : ℕ → E) (t : ℕ) :
    LinearMap.det (designOp V₀ x t : E →ₗ[ℝ] E) ≤
      ((LinearMap.trace ℝ E (V₀ : E →ₗ[ℝ] E) + ∑ s ∈ range t, ‖x s‖ ^ 2) / finrank ℝ E) ^
        finrank ℝ E := by
  rw [← trace_designOp]
  exact (isPositive_designOp hV₀ x t).det_le_trace_div_finrank_pow

/-- For a positive regularizer `V₀`, if `‖x s‖ ≤ L` for all `s < t`, then
`det V_t(V₀) ≤ ((trace V₀ + t L²) / d) ^ d`. -/
theorem det_designOp_le_of_norm_le (hV₀ : V₀.IsPositive) (x : ℕ → E) {t : ℕ} {L : ℝ}
    (hx : ∀ s < t, ‖x s‖ ≤ L) :
    LinearMap.det (designOp V₀ x t : E →ₗ[ℝ] E) ≤
      ((LinearMap.trace ℝ E (V₀ : E →ₗ[ℝ] E) + t * L ^ 2) / finrank ℝ E) ^ finrank ℝ E := by
  have hsum : ∑ s ∈ range t, ‖x s‖ ^ 2 ≤ t * L ^ 2 := by
    simpa using sum_le_card_nsmul (range t) _ (L ^ 2) fun s hs ↦
      pow_le_pow_left₀ (norm_nonneg _) (hx s (mem_range.1 hs)) 2
  refine (det_designOp_le hV₀ x t).trans (pow_le_pow_left₀ ?_ ?_ _)
  · exact div_nonneg (add_nonneg hV₀.toLinearMap.trace_nonneg (sum_nonneg fun _ _ ↦ by positivity))
      (Nat.cast_nonneg _)
  · gcongr

/-- [LS, (20.9)]: for `λ > 0`, if `‖x s‖ ≤ L` for all `s < t`, then
`det V_t(λ) / λ ^ d ≤ (1 + t L² / (λ d)) ^ d`. -/
theorem det_designOp_div_pow_le (hlam : 0 < lam) (x : ℕ → E) {t : ℕ} {L : ℝ}
    (hx : ∀ s < t, ‖x s‖ ≤ L) :
    LinearMap.det (designOp (lam • 1) x t : E →ₗ[ℝ] E) / lam ^ finrank ℝ E ≤
      (1 + t * L ^ 2 / (lam * finrank ℝ E)) ^ finrank ℝ E := by
  rw [div_le_iff₀ (pow_pos hlam _), ← mul_pow]
  refine (det_designOp_le_of_norm_le (isPositive_smul_one hlam.le) x hx).trans_eq ?_
  rcases (finrank ℝ E).eq_zero_or_pos with hd | hd
  · simp [hd]
  · congr 1
    rw [trace_smul_one]
    field_simp

/-- The determinant bound of [LS, Lemma 19.4]: for a positive definite regularizer `V₀`, if
`‖x s‖ ≤ L` for all `s < t`, then
`log (det V_t(V₀) / det V₀) ≤ d log ((trace V₀ + t L²) / (d det (V₀) ^ (1 / d)))`. -/
theorem log_det_designOp_div_le (hV₀ : V₀.IsPositive) (hV₀u : IsUnit V₀) (x : ℕ → E) {t : ℕ}
    {L : ℝ} (hx : ∀ s < t, ‖x s‖ ≤ L) :
    Real.log (LinearMap.det (designOp V₀ x t : E →ₗ[ℝ] E) / LinearMap.det (V₀ : E →ₗ[ℝ] E)) ≤
      finrank ℝ E * Real.log ((LinearMap.trace ℝ E (V₀ : E →ₗ[ℝ] E) + t * L ^ 2) /
        (finrank ℝ E * LinearMap.det (V₀ : E →ₗ[ℝ] E) ^ (finrank ℝ E : ℝ)⁻¹)) := by
  set d := finrank ℝ E with hd
  set D := LinearMap.det (V₀ : E →ₗ[ℝ] E)
  set A := LinearMap.trace ℝ E (V₀ : E →ₗ[ℝ] E) + t * L ^ 2
  rcases d.eq_zero_or_pos with hd0 | hd0
  · simp [hd0, D, LinearMap.det_eq_one_of_finrank_eq_zero (hd ▸ hd0)]
  have hD : 0 < D := by simpa using det_designOp_pos hV₀ hV₀u x 0
  have hT := det_designOp_pos hV₀ hV₀u x t
  have hle : LinearMap.det (designOp V₀ x t : E →ₗ[ℝ] E) ≤ (A / d) ^ d :=
    det_designOp_le_of_norm_le hV₀ x hx
  have hA : 0 < A / d := lt_of_pow_lt_pow_left₀ d
    (div_nonneg (add_nonneg hV₀.toLinearMap.trace_nonneg (by positivity)) (Nat.cast_nonneg _))
    (by rw [zero_pow hd0.ne']; exact hT.trans_le hle)
  calc Real.log (LinearMap.det (designOp V₀ x t : E →ₗ[ℝ] E) / D)
      = Real.log (LinearMap.det (designOp V₀ x t : E →ₗ[ℝ] E)) - Real.log D :=
        Real.log_div hT.ne' hD.ne'
    _ ≤ Real.log ((A / d) ^ d) - Real.log D := by gcongr
    _ = d * Real.log (A / (d * D ^ (d : ℝ)⁻¹)) := by
        rw [Real.log_pow, ← div_div, Real.log_div hA.ne' (Real.rpow_pos_of_pos hD _).ne',
          Real.log_rpow hD]
        field_simp

/-- [LS, (20.9)] in logarithmic form: for `λ > 0`, if `‖x s‖ ≤ L` for all `s < t`, then
`log (det V_t(λ) / λ ^ d) ≤ d log (1 + t L² / (λ d))`. -/
theorem log_det_designOp_div_pow_le (hlam : 0 < lam) (x : ℕ → E) {t : ℕ} {L : ℝ}
    (hx : ∀ s < t, ‖x s‖ ≤ L) :
    Real.log (LinearMap.det (designOp (lam • 1) x t : E →ₗ[ℝ] E) / lam ^ finrank ℝ E) ≤
      finrank ℝ E * Real.log (1 + t * L ^ 2 / (lam * finrank ℝ E)) := by
  have h := log_det_designOp_div_le (isPositive_smul_one hlam.le) (isUnit_smul_one hlam.ne') x hx
  rcases (finrank ℝ E).eq_zero_or_pos with hd | hd
  · simp [hd, LinearMap.det_eq_one_of_finrank_eq_zero hd]
  rw [det_smul_one, trace_smul_one] at h
  rwa [Real.pow_rpow_inv_natCast hlam.le hd.ne', show lam * finrank ℝ E + t * L ^ 2 =
    (finrank ℝ E * lam) * (1 + t * L ^ 2 / (lam * finrank ℝ E)) by field_simp,
    mul_div_cancel_left₀ _ (by positivity)] at h

/-- For a positive regularizer `V₀`, the vectors `x s` with `s < t` lie in the range of the
design operator `V_t(V₀)`: a vector `v` of its kernel satisfies
`0 = ⟪v, V_t(V₀) v⟫ = ⟪v, V₀ v⟫ + ∑_{s < t} ⟪x s, v⟫²`, so it is orthogonal to each `x s`. -/
theorem span_le_range_designOp (hV₀ : V₀.IsPositive) (x : ℕ → E) (t : ℕ) :
    Submodule.span ℝ (x '' Set.Iio t) ≤ LinearMap.range (designOp V₀ x t : E →ₗ[ℝ] E) := by
  have hV := (isPositive_designOp hV₀ x t).isSymmetric
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range _), hV.orthogonal_range,
    Submodule.span_le]
  rintro _ ⟨s, hs, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_orthogonal]
  intro v hv
  have h := inner_designOp_apply_self V₀ x t v
  rw [show designOp V₀ x t v = 0 from hv, inner_zero_right] at h
  have hsum : ∑ s ∈ range t, ⟪x s, v⟫_ℝ ^ 2 = 0 :=
    le_antisymm (by linarith [hV₀.inner_nonneg_right v]) (sum_nonneg fun _ _ ↦ sq_nonneg _)
  rw [real_inner_comm]
  exact pow_eq_zero_iff two_ne_zero |>.1 <|
    (sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).1 hsum s (mem_range.2 hs)

/-- The range of the unregularized design operator `V_t(0) = ∑_{s < t} x s ⊗ x s` is the span of
`x 0, …, x (t - 1)`. -/
theorem range_designOp_zero (x : ℕ → E) (t : ℕ) :
    LinearMap.range (designOp 0 x t : E →ₗ[ℝ] E) = Submodule.span ℝ (x '' Set.Iio t) := by
  refine le_antisymm ?_ (span_le_range_designOp isPositive_zero x t)
  rintro _ ⟨v, rfl⟩
  simp only [ContinuousLinearMap.coe_coe, designOp_apply, zero_apply, zero_add]
  exact Submodule.sum_smul_mem _ _ fun s hs ↦
    Submodule.subset_span ⟨s, Set.mem_Iio.2 (mem_range.1 hs), rfl⟩

end FiniteDimensional

end LMLExplore
