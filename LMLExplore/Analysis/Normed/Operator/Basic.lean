/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Real continuous linear functionals and the operator norm

A real continuous linear functional `f` satisfies `f x ≤ ‖f‖ * ‖x‖`, the form of the operator
norm bound `ContinuousLinearMap.le_opNorm` that pairs a loss or a dual vector with a
displacement in online learning and convex analysis. The bound is sharp on every sphere: the
supremum of `f` on the sphere of radius `r ≥ 0` about `0` is `r * ‖f‖`, the dual norm of `f`
seen from the primal side, and in a nontrivial proper space, such as a nontrivial
finite-dimensional one, it is attained, as used in [Ora]. This is the form in which the dual norm
enters the lower bounds of online linear optimization.

## Main statements

* `ContinuousLinearMap.apply_le_opNorm_mul_norm`: `f x ≤ ‖f‖ * ‖x‖` for `f : E →L[ℝ] ℝ`.
* `ContinuousLinearMap.sSup_image_sphere_eq_mul_norm`: the supremum of `f` on the sphere of
  radius `r ≥ 0` about `0` is `r * ‖f‖`.
* `ContinuousLinearMap.isGreatest_image_sphere`: in a nontrivial proper (for instance
  finite-dimensional) space, this supremum is a maximum.
* `ContinuousLinearMap.exists_lt_apply_of_lt_opNorm_real`: every `r < ‖f‖` is exceeded by some
  value `f x` with `‖x‖ < 1`, without absolute values.

## References

* [Ora] F. Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*,
  arXiv:1912.13213v10.
-/

public section

open Metric Set

namespace ContinuousLinearMap

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real continuous linear functional is bounded above by its operator norm times the norm of
its argument: `f x ≤ ‖f‖ * ‖x‖`. -/
theorem apply_le_opNorm_mul_norm (f : E →L[ℝ] ℝ) (x : E) : f x ≤ ‖f‖ * ‖x‖ :=
  (Real.le_norm_self _).trans (f.le_opNorm x)

end Seminormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℝ}

/-- Every real `r < ‖f‖` is exceeded by a value of the real continuous linear functional `f` on
the open unit ball: this is `ContinuousLinearMap.exists_lt_apply_of_lt_opNorm` without the absolute
value, using `f (-x) = -f x`. -/
theorem exists_lt_apply_of_lt_opNorm_real (f : E →L[ℝ] ℝ) (hr : r < ‖f‖) :
    ∃ x : E, ‖x‖ < 1 ∧ r < f x := by
  obtain ⟨x, hx1, hrx⟩ := f.exists_lt_apply_of_lt_opNorm hr
  rw [Real.norm_eq_abs] at hrx
  rcases abs_choice (f x) with h | h
  · exact ⟨x, hx1, h ▸ hrx⟩
  · exact ⟨-x, by rwa [norm_neg], by rwa [map_neg, ← h]⟩

/-- **The dual norm on a sphere.** The supremum of a real continuous linear functional `f` on the
sphere of radius `r ≥ 0` about `0` is `r * ‖f‖`. -/
theorem sSup_image_sphere_eq_mul_norm (f : E →L[ℝ] ℝ) (hr : 0 ≤ r) :
    sSup (f '' sphere 0 r) = r * ‖f‖ := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [sphere_eq_empty_of_subsingleton hr.ne', opNorm_subsingleton]
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ((NormedSpace.sphere_nonempty.2 hr.le).image f) ?_ fun c hc ↦ ?_
  · rintro - ⟨x, hx, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hx
    simpa [hx, mul_comm] using f.apply_le_opNorm_mul_norm x
  -- A unit vector `x` has `c / r < |f x|`, by Mathlib's supremum of `|f|` on the unit sphere;
  -- `r • x` or `-(r • x)` then has `c < f`.
  rw [← div_lt_iff₀' hr, ← f.sSup_sphere_eq_norm] at hc
  obtain ⟨-, ⟨x, hx, rfl⟩, hxc⟩ :=
    exists_lt_of_lt_csSup ((NormedSpace.sphere_nonempty.2 zero_le_one).image _) hc
  rw [mem_sphere_zero_iff_norm] at hx
  rw [div_lt_iff₀' hr] at hxc
  simp only [Real.norm_eq_abs] at hxc
  rcases le_total 0 (f x) with hfx | hfx
  · refine ⟨f (r • x), mem_image_of_mem f ?_, ?_⟩
    · simp [norm_smul, hx, abs_of_pos hr]
    · simpa [abs_of_nonneg hfx] using hxc
  · refine ⟨f (-(r • x)), mem_image_of_mem f ?_, ?_⟩
    · simp [norm_smul, hx, abs_of_pos hr]
    · simpa [abs_of_nonpos hfx] using hxc

/-- **The dual norm is attained on spheres in proper spaces.** In a
nontrivial proper (for instance finite-dimensional) real normed space, a real continuous linear
functional `f` attains its supremum `r * ‖f‖` on the sphere of radius `r ≥ 0` about `0`. -/
theorem isGreatest_image_sphere [ProperSpace E] [Nontrivial E] (f : E →L[ℝ] ℝ)
    (hr : 0 ≤ r) : IsGreatest (f '' sphere 0 r) (r * ‖f‖) := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : E) r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 hr) f.continuous.continuousOn
  have h : IsGreatest (f '' sphere 0 r) (f x) :=
    ⟨mem_image_of_mem f hx, forall_mem_image.2 fun _ hy ↦ hmax hy⟩
  rwa [← f.sSup_image_sphere_eq_mul_norm hr, h.csSup_eq]

end ContinuousLinearMap
