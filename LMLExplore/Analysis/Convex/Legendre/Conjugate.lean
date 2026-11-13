/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Coercive
public import LMLExplore.Analysis.Convex.Conjugate
public import LMLExplore.Analysis.Convex.FDeriv
public import LMLExplore.Analysis.Convex.Legendre.Basic
public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# The conjugate of a Legendre function

Let `F` be a Legendre function with domain `D` in a finite-dimensional real normed space `E`, and
let `F⋆ = fenchelConjugateOn F D` be its conjugate on the dual `E →L[ℝ] ℝ`, with effective domain
`D⋆ = {u | F⋆ u ≠ ⊤}`. This file proves the duality theorem for Legendre functions
[LS, Theorem 26.6]:

* the derivative `∇F` is a bijection from the interior of `D` onto the interior of `D⋆`, whose
  inverse is the derivative of `F⋆`: `∇F⋆ (∇F x) = x`, where a point `x` of `E` is identified
  with the evaluation `u ↦ u x` in the bidual;
* the Bregman divergences are dual: `D_F(x, y) = D_{F⋆}(∇F y, ∇F x)`;
* the real representative of `F⋆` is a Legendre function with domain `D⋆`.

No lower semicontinuity of `F` at the boundary of `D` is assumed. The point of the interior of
`D` where `∇F = u`, for `u` interior to `D⋆`, is the minimizer of the tilted function `F - u`
over `D`, which exists because the sublevel sets of `F - u` are bounded
(`LMLExplore.isBounded_setOf_le_of_mem_interior_setOf_fenchelConjugate_ne_top`). This is the map
`∇F⋆` that mirror descent and follow the regularized leader with a Legendre potential use to
return from the dual to the interior of the domain.

## Main statements

* `LMLExplore.IsLegendre.bijOn_fderiv`: [LS, Theorem 26.6 (a)], `∇F` is a bijection from the
  interior of `D` onto the interior of `D⋆`.
* `LMLExplore.IsLegendre.fderiv_toReal_fenchelConjugateOn_fderiv`,
  `LMLExplore.IsLegendre.fderiv_toReal_fenchelConjugateOn_eq_apply_iff`: its inverse is `∇F⋆`.
* `LMLExplore.IsLegendre.bregDiv_toReal_fenchelConjugateOn`: [LS, Theorem 26.6 (b)],
  `D_{F⋆}(∇F y, ∇F x) = D_F(x, y)`.
* `LMLExplore.IsLegendre.toReal_fenchelConjugateOn`: [LS, Theorem 26.6 (c)], `F⋆` is Legendre.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 26.5, Theorem 26.6 [LS].
* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, Theorem 26.5.
-/

public section

open Set Filter Topology

namespace LMLExplore.IsLegendre

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ} {D : Set E} {x y : E}
  {u : E →L[ℝ] ℝ}

variable (hF : IsLegendre F D)
include hF

/-- The derivative of a Legendre function is injective on the interior of its domain. -/
theorem injOn_fderiv : (interior D).InjOn (fderiv ℝ F) :=
  hF.strictConvexOn.injOn_of_hasFDerivWithinAt fun _ hx ↦ (hF.hasFDerivAt hx).hasFDerivWithinAt

variable [FiniteDimensional ℝ E]

/-- The derivative of a Legendre function maps the interior of its domain into the interior of
the effective domain of its conjugate. -/
theorem mapsTo_fderiv :
    MapsTo (fderiv ℝ F) (interior D) (interior {u | fenchelConjugateOn F D u ≠ ⊤}) :=
  fun _ hx ↦ mem_interior_setOf_fenchelConjugateOn_ne_top hF.convexOn hF.strictConvexOn hx
    (hF.hasSubgradientWithinAt hx)

/-- **The derivative of a Legendre function is onto the interior of the domain of its
conjugate** (part of [LS, Theorem 26.6 (a)]). Every `u` in the interior of `{u | F⋆ u ≠ ⊤}` is
the derivative of `F` at a point of the interior of `D`. -/
theorem surjOn_fderiv :
    SurjOn (fderiv ℝ F) (interior D) (interior {u | fenchelConjugateOn F D u ≠ ⊤}) := by
  classical
  intro u hu
  -- The tilted function `G = F - u` is Legendre, with bounded sublevel sets since `u` is interior
  -- to the domain of the conjugate.
  have hG := hF.add_linear (-u)
  obtain ⟨x₀, hx₀⟩ := hF.nonempty_interior
  simp only [fenchelConjugateOn_eq_fenchelConjugate] at hu
  have hbdd : Bornology.IsBounded
      {x ∈ univ ∩ D | F x + (-u) x ≤ F x₀ + (-u) x₀} := by
    refine (isBounded_setOf_le_of_mem_interior_setOf_fenchelConjugate_ne_top hu
      (F x₀ - u x₀)).subset fun x ⟨⟨_, hxD⟩, hx⟩ ↦ ?_
    simp only [neg_apply] at hx
    simp only [mem_ofPred_eq, hxD, ↓reduceIte, EReal.coe_le_coe_iff]
    linarith
  -- Its minimizer `y` over `D` is interior, and `∇F y - u = 0` there.
  obtain ⟨y, ⟨-, hyD⟩, hymin⟩ := (hG.existsUnique_isMinOn_inter_of_isBounded isClosed_univ
    convex_univ ⟨mem_univ x₀, hx₀⟩ hbdd).exists
  rw [univ_inter] at hymin
  have hy := hG.mem_interior_of_isMinOn hyD hymin
  refine ⟨y, hy, ?_⟩
  have h0 := hG.fderiv_eq_zero_of_isMinOn hyD hymin
  rwa [fderiv_fun_add (hF.hasFDerivAt hy).differentiableAt (-u).differentiableAt,
    ContinuousLinearMap.fderiv, add_neg_eq_zero] at h0

/-- **The derivative of a Legendre function is a bijection between interiors**
[LS, Theorem 26.6 (a)]: it maps the interior of the domain `D` bijectively onto the interior of
the effective domain `{u | F⋆ u ≠ ⊤}` of the conjugate. Its inverse is the derivative of the
conjugate (`fderiv_toReal_fenchelConjugateOn_fderiv`). -/
theorem bijOn_fderiv :
    BijOn (fderiv ℝ F) (interior D) (interior {u | fenchelConjugateOn F D u ≠ ⊤}) :=
  ⟨hF.mapsTo_fderiv, hF.injOn_fderiv, hF.surjOn_fderiv⟩

/-- **The derivative of the conjugate inverts the derivative** (part of
[LS, Theorem 26.6 (a)]): `∇F⋆ (∇F x) = x` for `x` in the interior of the domain, where `x` is
identified with the evaluation `u ↦ u x`. -/
theorem fderiv_toReal_fenchelConjugateOn_fderiv (hx : x ∈ interior D) :
    fderiv ℝ (fun u ↦ (fenchelConjugateOn F D u).toReal) (fderiv ℝ F x) =
      ContinuousLinearMap.apply ℝ ℝ x :=
  (hasFDerivAt_toReal_fenchelConjugateOn hF.convexOn hF.strictConvexOn hx
    (hF.hasSubgradientWithinAt hx)).fderiv

/-- **The derivative of the conjugate is the inverse of the derivative** (part of
[LS, Theorem 26.6 (a)]): for `u` in the interior of the domain of the conjugate and `x` in the
interior of `D`, `∇F⋆ u = x` if and only if `∇F x = u`. -/
theorem fderiv_toReal_fenchelConjugateOn_eq_apply_iff
    (hu : u ∈ interior {u | fenchelConjugateOn F D u ≠ ⊤}) (hx : x ∈ interior D) :
    fderiv ℝ (fun u ↦ (fenchelConjugateOn F D u).toReal) u = ContinuousLinearMap.apply ℝ ℝ x ↔
      fderiv ℝ F x = u := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ hF.fderiv_toReal_fenchelConjugateOn_fderiv hx⟩
  obtain ⟨y, hy, rfl⟩ := hF.surjOn_fderiv hu
  rw [hF.fderiv_toReal_fenchelConjugateOn_fderiv hy] at h
  have hyx : y = x := SeparatingDual.eq_iff_forall_dual_eq (R := ℝ).2 fun g ↦ by
    simpa using congr($h g)
  rw [hyx]

/-- **Duality of Bregman divergences for Legendre functions** [LS, Theorem 26.6 (b)]: for `x, y`
in the interior of the domain, `D_{F⋆}(∇F y, ∇F x) = D_F(x, y)`, where the divergence of the
conjugate is taken with its derivative at `∇F x`. -/
theorem bregDiv_toReal_fenchelConjugateOn (hx : x ∈ interior D) (hy : y ∈ interior D) :
    bregDiv (fun u ↦ (fenchelConjugateOn F D u).toReal) (fderiv ℝ F y) (fderiv ℝ F x)
        (fderiv ℝ (fun u ↦ (fenchelConjugateOn F D u).toReal) (fderiv ℝ F x)) =
      bregDiv F x y (fderiv ℝ F y) := by
  rw [hF.fderiv_toReal_fenchelConjugateOn_fderiv hx]
  exact LMLExplore.bregDiv_toReal_fenchelConjugateOn (hF.hasSubgradientWithinAt hx)
    (hF.hasSubgradientWithinAt hy) (interior_subset hx) (interior_subset hy)

/-- **The conjugate of a Legendre function is Legendre** [LS, Theorem 26.6 (c)]. In finite
dimension, the real representative of the conjugate `F⋆` is a Legendre function with domain the
effective domain `{u | F⋆ u ≠ ⊤}` of the conjugate. -/
theorem toReal_fenchelConjugateOn :
    IsLegendre (fun u ↦ (fenchelConjugateOn F D u).toReal) {u | fenchelConjugateOn F D u ≠ ⊤} := by
  set D' := {u | fenchelConjugateOn F D u ≠ ⊤}
  -- `g` inverts `∇F` on the interior of `D'`, and `∇F⋆ u` is the evaluation at `g u`.
  set g := Function.invFunOn (fderiv ℝ F) (interior D)
  have hmaps : MapsTo g (interior D') (interior D) := hF.surjOn_fderiv.mapsTo_invFunOn
  have hinv : ∀ u ∈ interior D', fderiv ℝ F (g u) = u := hF.surjOn_fderiv.rightInvOn_invFunOn
  have hderiv (u : E →L[ℝ] ℝ) (hu : u ∈ interior D') :
      HasFDerivAt (fun u ↦ (fenchelConjugateOn F D u).toReal)
        (ContinuousLinearMap.apply ℝ ℝ (g u)) u := by
    have := hasFDerivAt_toReal_fenchelConjugateOn hF.convexOn hF.strictConvexOn (hmaps hu)
      (hF.hasSubgradientWithinAt (hmaps hu))
    rwa [hinv u hu] at this
  obtain ⟨x₀, hx₀⟩ := hF.nonempty_interior
  have hconv : ConvexOn ℝ D' fun u ↦ (fenchelConjugateOn F D u).toReal :=
    convexOn_toReal_fenchelConjugateOn
  refine ⟨hconv, ⟨_, hF.mapsTo_fderiv hx₀⟩,
    fun u hu ↦ (hderiv u hu).differentiableAt.differentiableWithinAt, ?_, fun b hb ↦ ?_⟩
  · -- Strict convexity: the derivative `u ↦ g u` is injective.
    refine (hconv.subset interior_subset hconv.1.interior).strictConvexOn_of_injOn
      isOpen_interior hderiv fun u hu v hv h ↦ ?_
    have huv : g u = g v := SeparatingDual.eq_iff_forall_dual_eq (R := ℝ).2 fun f ↦ by
      simpa using congr($h f)
    rw [← hinv u hu, ← hinv v hv, huv]
  · -- Steepness: `‖g u‖ → ∞` as `u` tends to a boundary point `b` of the interior of `D'`, which
    -- is not a derivative of `F` on the interior of `D`.
    have hb' : b ∉ fderiv ℝ F '' interior D := by
      rw [hF.bijOn_fderiv.image_eq]
      exact fun h ↦ hb.2 (by rwa [interior_interior])
    refine tendsto_atTop_mono' _ ?_
      ((hF.convexOn.subset interior_subset hF.convex.interior).tendsto_norm_comp_atTop_of_steep
        isOpen_interior (fun _ hx ↦ hF.hasFDerivAt hx) hF.tendsto_norm_fderiv hb' hmaps hinv)
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [(hderiv u hu).fderiv]
    exact NormedSpace.norm_le_dual_bound ℝ (g u) (norm_nonneg _) fun f ↦ by
      simpa using (ContinuousLinearMap.apply ℝ ℝ (g u)).le_opNorm f

end LMLExplore.IsLegendre
