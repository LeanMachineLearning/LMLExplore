/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.InnerProductSpace.MoorePenrose
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Basic.ENNReal.Real

/-!
# The squared norm `‖y‖²_{V⁻¹}` of a possibly singular operator, and distances to half-spaces

For an invertible positive operator `V` on a real inner product space, the squared norm of `y` for
the inverse of `V` is `‖y‖²_{V⁻¹} = ⟪y, V⁻¹ y⟫`. It is the largest value of the concave quadratic
function `x ↦ 2 ⟪y, x⟫ - ⟪x, V x⟫`, attained at `x = V⁻¹ y`. This variational form makes sense for
every linear map `V`, invertible or not, with values in `[0, ∞]`:
`‖y‖²_{V⁻¹} = sup_x (2 ⟪y, x⟫ - ⟪x, V x⟫)` (`LMLExplore.invNormSq V y`). For a positive operator
`V` it is `⟪z, V z⟫` at every `y = V z` in the range of `V`, and `∞` as soon as `y` is not
orthogonal to the kernel of `V`, along which the function is unbounded. In finite dimension it is
therefore `⟪y, V⁺ y⟫` on the range of `V`, with the Moore–Penrose inverse `V⁺`, and `∞` off it.

It is the quantity in which the squared distance to a half-space is expressed, for the seminorm
`‖x‖²_V = ⟪x, V x⟫` of a positive semidefinite `V`: for `a > 0`,
`inf {⟪x, V x⟫ | a ≤ ⟪y, x⟫} = a² / ‖y‖²_{V⁻¹}`
in `[0, ∞]`. When `‖y‖²_{V⁻¹} = ∞`, some direction of the kernel of `V` crosses the half-space at
no cost and the infimum is `0`; when `y = 0` the half-space is empty and the infimum is `∞`.
Equivalently, the squared `V`-distance from `θ` to a half-space `{λ | ⟪y, λ⟫ ≤ c}` whose
interior does not contain `θ` is `(⟪y, θ⟫ - c)² / ‖y‖²_{V⁻¹}`. For `V` the design operator
`∑_a w_a σ_a⁻² φ(a) ⊗ φ(a)` of an allocation `w`, this is the cost of moving the parameter of a
linear model with Gaussian observations across a hyperplane, which gives the characteristic times
of identification tasks whose alternatives are unions of half-spaces [FJJR19, Theorem 1].

Half of `‖·‖²_{V⁻¹}` is the convex conjugate of the quadratic function `x ↦ ⟪x, V x⟫ / 2`
(Tau Ceti's `EReal`-valued `TauCeti.fenchelConjugate` for the pairing `innerₗ E`); the definition
below is the defining supremum directly, valued in `ℝ≥0∞` like the transportation costs that use
it.

## Main definitions

* `LMLExplore.invNormSq V y`: `‖y‖²_{V⁻¹} = sup_x (2 ⟪y, x⟫ - ⟪x, V x⟫)` in `ℝ≥0∞`.

## Main statements

* `LMLExplore.invNormSq_apply`: `‖V z‖²_{V⁻¹} = ⟪z, V z⟫` for a positive `V`.
* `LMLExplore.invNormSq_ringInverse`: `‖y‖²_{V⁻¹} = ⟪y, V⁻¹ y⟫` for an invertible positive `V`.
* `LMLExplore.invNormSq_eq_ofReal_inner_moorePenroseInverse`: in finite dimension,
  `‖y‖²_{V⁻¹} = ⟪y, V⁺ y⟫` for a positive `V` and `y` in its range.
* `LMLExplore.invNormSq_eq_top_of_apply_eq_zero`, `LMLExplore.invNormSq_eq_top_iff`:
  `‖y‖²_{V⁻¹} = ∞` if `y` is not orthogonal to the kernel of `V`; in finite dimension, for a
  positive `V`, exactly when `y` is not in the range of `V`.
* `LMLExplore.biInf_ofReal_inner_apply_self_eq_div_invNormSq`: for a positive semidefinite
  quadratic form and `a > 0`, `inf {⟪x, V x⟫ | a ≤ ⟪y, x⟫} = a² / ‖y‖²_{V⁻¹}`.
* `LMLExplore.biInf_ofReal_inner_sub_apply_sub_eq_div_invNormSq`: the squared `V`-distance from
  `θ` to a half-space `{λ | ⟪y, λ⟫ ≤ c}` with `c ≤ ⟪y, θ⟫` is `(⟪y, θ⟫ - c)² / ‖y‖²_{V⁻¹}`.

## References

* [FJJR19] T. Fiez, L. Jain, K. Jamieson and L. Ratliff, *Sequential experimental design for
  transductive linear bandits*, NeurIPS 2019, Theorem 1 and its proof.
-/

public section

open LinearMap InnerProductSpace
open scoped ENNReal InnerProductSpace

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {V : E →ₗ[ℝ] E} {x y z : E}

/-- The squared norm `‖y‖²_{V⁻¹} = sup_x (2 ⟪y, x⟫ - ⟪x, V x⟫)` of `y` for the inverse of `V`, in
`ℝ≥0∞`. For a positive operator `V` it is `⟪y, V⁻¹ y⟫` when `V` is invertible
(`invNormSq_ringInverse`), `⟪y, V⁺ y⟫` on the range of `V` in finite dimension
(`invNormSq_eq_ofReal_inner_moorePenroseInverse`), and `∞` off the range (`invNormSq_eq_top_iff`).
-/
noncomputable def invNormSq (V : E →ₗ[ℝ] E) (y : E) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal (2 * ⟪y, x⟫_ℝ - ⟪x, V x⟫_ℝ)

theorem invNormSq_def (V : E →ₗ[ℝ] E) (y : E) :
    invNormSq V y = ⨆ x, ENNReal.ofReal (2 * ⟪y, x⟫_ℝ - ⟪x, V x⟫_ℝ) := (rfl)

theorem ofReal_le_invNormSq (V : E →ₗ[ℝ] E) (x y : E) :
    ENNReal.ofReal (2 * ⟪y, x⟫_ℝ - ⟪x, V x⟫_ℝ) ≤ invNormSq V y :=
  le_iSup (fun x ↦ ENNReal.ofReal (2 * ⟪y, x⟫_ℝ - ⟪x, V x⟫_ℝ)) x

theorem invNormSq_le_iff {r : ℝ≥0∞} :
    invNormSq V y ≤ r ↔ ∀ x, ENNReal.ofReal (2 * ⟪y, x⟫_ℝ - ⟪x, V x⟫_ℝ) ≤ r :=
  iSup_le_iff

/-- Evaluation of the concave quadratic function of `invNormSq` along a line:
`2 ⟪y, t x⟫ - ⟪t x, V (t x)⟫ = 2 t ⟪y, x⟫ - t² ⟪x, V x⟫`. -/
private lemma ofReal_le_invNormSq_smul (V : E →ₗ[ℝ] E) (x y : E) (t : ℝ) :
    ENNReal.ofReal (2 * t * ⟪y, x⟫_ℝ - t ^ 2 * ⟪x, V x⟫_ℝ) ≤ invNormSq V y := by
  convert ofReal_le_invNormSq V (t • x) y using 2
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- `‖0‖²_{V⁻¹} = 0` for a positive semidefinite `V`. -/
theorem invNormSq_zero (hV : ∀ x, 0 ≤ ⟪x, V x⟫_ℝ) : invNormSq V 0 = 0 :=
  nonpos_iff_eq_zero.1 <| invNormSq_le_iff.2 fun x ↦ by simp [hV x]

/-- `‖y‖²_{V⁻¹} = ∞` as soon as `y` is not orthogonal to a vector `x` of the kernel of `V`: the
concave quadratic function `2 ⟪y, ·⟫ - ⟪·, V ·⟫` is linear and unbounded along `x`. -/
theorem invNormSq_eq_top_of_apply_eq_zero (hx : V x = 0) (hxy : ⟪y, x⟫_ℝ ≠ 0) :
    invNormSq V y = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  refine le_trans (le_of_eq ?_) (ofReal_le_invNormSq_smul V x y (r / (2 * ⟪y, x⟫_ℝ)))
  rw [hx, inner_zero_right, mul_zero, sub_zero,
    show 2 * ((r : ℝ) / (2 * ⟪y, x⟫_ℝ)) * ⟪y, x⟫_ℝ = r by field_simp, ENNReal.ofReal_coe_nnreal]

/-- For a positive operator `V`, `‖V z‖²_{V⁻¹} = ⟪z, V z⟫`: the concave quadratic function
`2 ⟪V z, x⟫ - ⟪x, V x⟫ = ⟪z, V z⟫ - ⟪x - z, V (x - z)⟫` is maximal at `x = z`. -/
theorem invNormSq_apply (hV : V.IsPositive) (z : E) :
    invNormSq V (V z) = ENNReal.ofReal ⟪z, V z⟫_ℝ := by
  refine le_antisymm (invNormSq_le_iff.2 fun x ↦ ENNReal.ofReal_le_ofReal ?_) ?_
  · have h := hV.inner_nonneg_right (x - z)
    have hs := hV.isSymmetric z x
    have hc := real_inner_comm x (V z)
    simp only [map_sub, inner_sub_left, inner_sub_right] at h ⊢
    linarith
  · convert ofReal_le_invNormSq V z (V z) using 2
    rw [real_inner_comm z (V z)]
    ring

/-- `‖y‖²_{V⁻¹} = ⟪y, V⁻¹ y⟫` for an invertible positive operator `V`. -/
theorem invNormSq_ringInverse {V : E →L[ℝ] E} (hV : V.IsPositive) (hVu : IsUnit V) (y : E) :
    invNormSq (V : E →ₗ[ℝ] E) y = ENNReal.ofReal ⟪y, Ring.inverse V y⟫_ℝ := by
  have h := invNormSq_apply hV.toLinearMap (Ring.inverse V y)
  rwa [ContinuousLinearMap.coe_coe, ContinuousLinearMap.apply_ringInverse_apply hVu,
    real_inner_comm] at h

/-- For a positive operator `V`, `‖y‖²_{V⁻¹}` is finite on the range of `V`. -/
theorem invNormSq_lt_top_of_mem_range (hV : V.IsPositive) (hy : y ∈ range V) :
    invNormSq V y < ∞ := by
  obtain ⟨z, rfl⟩ := hy
  simp [invNormSq_apply hV]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- In finite dimension, `‖y‖²_{V⁻¹} = ⟪y, V⁺ y⟫` for a positive operator `V` and `y` in its
range, where `V⁺` is the Moore–Penrose inverse of `V`. -/
theorem invNormSq_eq_ofReal_inner_moorePenroseInverse (hV : V.IsPositive) (hy : y ∈ range V) :
    invNormSq V y = ENNReal.ofReal ⟪y, V.moorePenroseInverse y⟫_ℝ := by
  obtain ⟨z, rfl⟩ := hy
  rw [invNormSq_apply hV, hV.isSymmetric,
    V.isMoorePenroseInverse_moorePenroseInverse.apply_apply_apply]

/-- In finite dimension, `‖y‖²_{V⁻¹} = ∞` for a symmetric operator `V` and `y` outside its range:
`y` is then not orthogonal to the kernel of `V`, the orthogonal complement of the range. -/
theorem invNormSq_eq_top_of_notMem_range (hV : V.IsSymmetric) (hy : y ∉ range V) :
    invNormSq V y = ∞ := by
  rw [← Submodule.orthogonal_orthogonal (range V), hV.orthogonal_range,
    Submodule.mem_orthogonal] at hy
  push Not at hy
  obtain ⟨x, hx, hxy⟩ := hy
  exact invNormSq_eq_top_of_apply_eq_zero hx (by rwa [real_inner_comm])

/-- In finite dimension, for a positive operator `V`, `‖y‖²_{V⁻¹} = ∞` exactly when `y` is not in
the range of `V`. -/
theorem invNormSq_eq_top_iff (hV : V.IsPositive) : invNormSq V y = ∞ ↔ y ∉ range V :=
  ⟨fun h hy ↦ (invNormSq_lt_top_of_mem_range hV hy).ne h,
    invNormSq_eq_top_of_notMem_range hV.isSymmetric⟩

end FiniteDimensional

/-- On the half-space `{x | a ≤ ⟪y, x⟫}`, `a > 0`, the quadratic form of a positive semidefinite
`V` is at least `a² / ‖y‖²_{V⁻¹}`. -/
private lemma ofReal_sq_div_invNormSq_le (hV : ∀ x, 0 ≤ ⟪x, V x⟫_ℝ) {a : ℝ} (ha : 0 < a)
    (hx : a ≤ ⟪y, x⟫_ℝ) :
    ENNReal.ofReal (a ^ 2) / invNormSq V y ≤ ENNReal.ofReal ⟪x, V x⟫_ℝ := by
  rcases (hV x).eq_or_lt with hq | hq
  · -- `⟪x, V x⟫ = 0`: the function is linear and unbounded along `x`, so `‖y‖²_{V⁻¹} = ∞`
    have htop : invNormSq V y = ∞ := by
      refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
      refine le_trans ?_ (ofReal_le_invNormSq_smul V x y (r / (2 * a)))
      rw [← hq, mul_zero, sub_zero, ← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (r : ℝ) = 2 * (r / (2 * a)) * a := by field_simp
        _ ≤ 2 * (r / (2 * a)) * ⟪y, x⟫_ℝ := by gcongr
    simp [htop]
  · -- `⟪x, V x⟫ > 0`: evaluate the function at `t x` with `t = a / ⟪x, V x⟫`
    refine ENNReal.div_le_of_le_mul ?_
    calc ENNReal.ofReal (a ^ 2)
        = ENNReal.ofReal ⟪x, V x⟫_ℝ * ENNReal.ofReal (a ^ 2 / ⟪x, V x⟫_ℝ) := by
          rw [← ENNReal.ofReal_mul hq.le, mul_div_cancel₀ _ hq.ne']
      _ ≤ ENNReal.ofReal ⟪x, V x⟫_ℝ * ENNReal.ofReal
            (2 * (a / ⟪x, V x⟫_ℝ) * ⟪y, x⟫_ℝ - (a / ⟪x, V x⟫_ℝ) ^ 2 * ⟪x, V x⟫_ℝ) := by
          gcongr
          field_simp
          nlinarith
      _ ≤ ENNReal.ofReal ⟪x, V x⟫_ℝ * invNormSq V y := by
          gcongr
          exact ofReal_le_invNormSq_smul V x y _

/-- If `s = 2 ⟪y, z⟫ - ⟪z, V z⟫ > 0`, the point `(a / ⟪y, z⟫) z` of the half-space
`{x | a ≤ ⟪y, x⟫}` has `⟪x, V x⟫ ≤ a² / s`. -/
private lemma exists_inner_apply_self_mul_le (hV : ∀ x, 0 ≤ ⟪x, V x⟫_ℝ) (a : ℝ)
    (hs : 0 < 2 * ⟪y, z⟫_ℝ - ⟪z, V z⟫_ℝ) :
    ∃ x, a ≤ ⟪y, x⟫_ℝ ∧ ⟪x, V x⟫_ℝ * (2 * ⟪y, z⟫_ℝ - ⟪z, V z⟫_ℝ) ≤ a ^ 2 := by
  have hb : 0 < ⟪y, z⟫_ℝ := by linarith [hV z]
  refine ⟨(a / ⟪y, z⟫_ℝ) • z, ?_, ?_⟩
  · rw [real_inner_smul_right, div_mul_cancel₀ _ hb.ne']
  · -- `⟪z, V z⟫ (2 b - ⟪z, V z⟫) ≤ b²` with `b = ⟪y, z⟫`, since `(b - ⟪z, V z⟫)² ≥ 0`
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    have key : ⟪z, V z⟫_ℝ * (2 * ⟪y, z⟫_ℝ - ⟪z, V z⟫_ℝ) ≤ ⟪y, z⟫_ℝ ^ 2 := by
      nlinarith [sq_nonneg (⟪y, z⟫_ℝ - ⟪z, V z⟫_ℝ)]
    calc a / ⟪y, z⟫_ℝ * (a / ⟪y, z⟫_ℝ * ⟪z, V z⟫_ℝ) * (2 * ⟪y, z⟫_ℝ - ⟪z, V z⟫_ℝ)
        = (a / ⟪y, z⟫_ℝ) ^ 2 * (⟪z, V z⟫_ℝ * (2 * ⟪y, z⟫_ℝ - ⟪z, V z⟫_ℝ)) := by ring
      _ ≤ (a / ⟪y, z⟫_ℝ) ^ 2 * ⟪y, z⟫_ℝ ^ 2 := by gcongr
      _ = a ^ 2 := by field_simp

/-- **The squared distance to a half-space.** For a positive semidefinite `V` and `a > 0`,
the smallest value of the quadratic form `⟪x, V x⟫` on the half-space `{x | a ≤ ⟪y, x⟫}` is
`a² / ‖y‖²_{V⁻¹}`, in `ℝ≥0∞`. It is `0` when `‖y‖²_{V⁻¹} = ∞` and `∞` when `y = 0`. -/
theorem biInf_ofReal_inner_apply_self_eq_div_invNormSq (hV : ∀ x, 0 ≤ ⟪x, V x⟫_ℝ) {a : ℝ}
    (ha : 0 < a) (y : E) :
    ⨅ x ∈ {x | a ≤ ⟪y, x⟫_ℝ}, ENNReal.ofReal ⟪x, V x⟫_ℝ =
      ENNReal.ofReal (a ^ 2) / invNormSq V y := by
  have ha2 : ENNReal.ofReal (a ^ 2) ≠ 0 := by simp [ha.ne']
  refine le_antisymm ?_ (le_iInf₂ fun x hx ↦ ofReal_sq_div_invNormSq_le hV ha hx)
  rw [ENNReal.le_div_iff_mul_le (Or.inr ha2) (Or.inr ENNReal.ofReal_ne_top), invNormSq_def,
    ENNReal.mul_iSup, iSup_le_iff]
  intro z
  rcases le_or_gt (2 * ⟪y, z⟫_ℝ - ⟪z, V z⟫_ℝ) 0 with hs | hs
  · simp [ENNReal.ofReal_of_nonpos hs]
  obtain ⟨x, hx, hxs⟩ := exists_inner_apply_self_mul_le hV a hs
  calc (⨅ x ∈ {x | a ≤ ⟪y, x⟫_ℝ}, ENNReal.ofReal ⟪x, V x⟫_ℝ) *
        ENNReal.ofReal (2 * ⟪y, z⟫_ℝ - ⟪z, V z⟫_ℝ)
      ≤ ENNReal.ofReal ⟪x, V x⟫_ℝ * ENNReal.ofReal (2 * ⟪y, z⟫_ℝ - ⟪z, V z⟫_ℝ) := by
        gcongr
        exact iInf₂_le x hx
    _ ≤ ENNReal.ofReal (a ^ 2) := by
        rw [← ENNReal.ofReal_mul (hV x)]
        exact ENNReal.ofReal_le_ofReal hxs

/-- **The squared distance to a half-space**, centered form. For a positive semidefinite `V` and a
half-space `{λ | ⟪y, λ⟫ ≤ c}` whose interior does not contain `θ`, the squared `V`-distance from
`θ` to the half-space is `inf {⟪θ - λ, V (θ - λ)⟫ | ⟪y, λ⟫ ≤ c} = (⟪y, θ⟫ - c)² / ‖y‖²_{V⁻¹}`. It
is `0` when `θ` is on the boundary hyperplane. -/
theorem biInf_ofReal_inner_sub_apply_sub_eq_div_invNormSq (hV : ∀ x, 0 ≤ ⟪x, V x⟫_ℝ) {θ y : E}
    {c : ℝ} (hc : c ≤ ⟪y, θ⟫_ℝ) :
    ⨅ θ' ∈ {θ' | ⟪y, θ'⟫_ℝ ≤ c}, ENNReal.ofReal ⟪θ - θ', V (θ - θ')⟫_ℝ =
      ENNReal.ofReal ((⟪y, θ⟫_ℝ - c) ^ 2) / invNormSq V y := by
  rcases hc.eq_or_lt with hc | hc
  · -- `θ` is on the boundary of the half-space
    refine le_antisymm ((iInf₂_le θ hc.ge).trans ?_) (by simp [hc])
    simp
  rw [← biInf_ofReal_inner_apply_self_eq_div_invNormSq hV (sub_pos.2 hc)]
  refine le_antisymm (le_iInf₂ fun x hx ↦ ?_) (le_iInf₂ fun θ' hθ' ↦ ?_)
  · refine (iInf₂_le (θ - x) ?_).trans_eq (by rw [sub_sub_cancel])
    simp only [Set.mem_ofPred_eq, inner_sub_right] at hx ⊢
    linarith
  · refine iInf₂_le (θ - θ') ?_
    simp only [Set.mem_ofPred_eq, inner_sub_right] at hθ' ⊢
    linarith

end LMLExplore
