/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import TauCeti.Analysis.Convex.Conjugate
import Statlib.ForMathlib.EReal
import LMLExplore.Data.EReal.Operations

/-!
# Conjugates of scaled, translated and tilted functions

For real vector spaces `E` and `F` paired by a bilinear form `B`, Tau Ceti's
`TauCeti.fenchelConjugate B f y = ⨆ x, (B x y - f x)` is the Legendre–Fenchel conjugate of an
extended-real function `f : E → EReal`. This file computes the conjugates of the functions
obtained from `f` by the elementary operations of [Ora, Lemma 6.22]:

* tilting `f` by the linear function `B · y₀` shifts the argument of the conjugate by `-y₀`;
* translating the argument of `f` by `x₀` adds the linear function `B x₀ ·` to the conjugate;
* multiplying `f` by `a > 0` gives the conjugate `y ↦ a f⋆ (a⁻¹ • y)`.

Together with Tau Ceti's `TauCeti.fenchelConjugate_add_const`, the last item gives the conjugate
`y ↦ a f⋆ (a⁻¹ • y) - b` of `a f + b`. None of these needs convexity of `f`, and they hold for
every pairing; online learning uses them for the pairing of a normed space with its dual,
`(topDualPairing ℝ E).flip`, where the scaling is that of a regularizer `ψ / η` by a learning
rate.

## Main statements

* `LMLExplore.fenchelConjugate_add_linear`: `(f + B · y₀)⋆ y = f⋆ (y - y₀)`.
* `LMLExplore.fenchelConjugate_comp_sub`: `(f (· - x₀))⋆ y = f⋆ y + B x₀ y`.
* `LMLExplore.fenchelConjugate_const_mul`: `(a f)⋆ y = a f⋆ (a⁻¹ • y)` for `a > 0`.

## References

* F. Orabona, *A Modern Introduction to Online Learning*, arXiv:1912.13213v10, Lemma 6.22 [Ora].
-/

public section

open TauCeti

namespace LMLExplore

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)

/-- **Tilting by a linear function** [Ora, Lemma 6.22]: adding `B · y₀` to `f` shifts the
argument of the conjugate, `(f + B · y₀)⋆ y = f⋆ (y - y₀)`. -/
@[simp]
theorem fenchelConjugate_add_linear (f : E → EReal) (y₀ y : F) :
    fenchelConjugate B (fun x ↦ f x + (B x y₀ : EReal)) y = fenchelConjugate B f (y - y₀) := by
  simp only [fenchelConjugate_apply, map_sub, EReal.coe_sub, EReal.coe_sub_add_coe]
  refine iSup_congr fun x ↦ ?_
  simp only [sub_eq_add_neg]
  ac_rfl

/-- **Translating the argument** [Ora, Lemma 6.22]: the conjugate of `f (· - x₀)` is
`y ↦ f⋆ y + B x₀ y`. -/
@[simp]
theorem fenchelConjugate_comp_sub (f : E → EReal) (x₀ : E) (y : F) :
    fenchelConjugate B (fun x ↦ f (x - x₀)) y = fenchelConjugate B f y + (B x₀ y : EReal) := by
  simp only [fenchelConjugate_apply, ← EReal.iSup_add_coe]
  rw [← (Equiv.addRight x₀).iSup_comp]
  refine iSup_congr fun z ↦ ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, map_add, LinearMap.add_apply,
    EReal.coe_add]
  simp only [sub_eq_add_neg]
  ac_rfl

/-- **Scaling by a positive constant** [Ora, Lemma 6.22]: for `a > 0`, the conjugate of `a f` is
`y ↦ a f⋆ (a⁻¹ • y)`. -/
theorem fenchelConjugate_const_mul {a : ℝ} (ha : 0 < a) (f : E → EReal) (y : F) :
    fenchelConjugate B (fun x ↦ (a : EReal) * f x) y = a * fenchelConjugate B f (a⁻¹ • y) := by
  simp only [fenchelConjugate_apply]
  rw [EReal.iSup_coe_mul_of_nonneg ha.le]
  refine iSup_congr fun x ↦ ?_
  rw [map_smul, smul_eq_mul]
  induction f x <;> simp [EReal.coe_mul_top_of_pos ha, EReal.coe_mul_bot_of_pos ha,
    ← EReal.coe_mul, ← EReal.coe_sub, mul_sub, ha.ne']

end LMLExplore
