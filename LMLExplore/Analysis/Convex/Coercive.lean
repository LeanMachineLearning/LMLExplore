/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import TauCeti.Analysis.Convex.Conjugate
public import TauCeti.Analysis.Convex.EffectiveDomain

/-!
# The interior of the domain of the conjugate and linear growth of tilts

Let `E` be a real normed space, paired with its dual `E →L[ℝ] ℝ` by `(x, u) ↦ u x`, and let
`f⋆` be the Legendre–Fenchel conjugate of `f : E → EReal` for this pairing (Tau Ceti's
`TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f`). This file shows that a functional `u`
lies in the interior of the effective domain `{v | f⋆ v ≠ ⊤}` exactly when the tilted function
`x ↦ f x - u x` grows at least linearly: `u x + r ‖x‖ - M ≤ f x` for some `r > 0` and some `M`.
The direction from growth to the interior holds in every normed space: the conjugate is then at
most `M` on the closed ball of radius `r` around `u`. The converse needs `E` to be
finite-dimensional, so that the convex function `f⋆` is bounded above near every interior point
of its domain.

The tilted sublevel sets `{x | f x ≤ u x + c}` of a function whose conjugate is not `⊤` near `u`
are therefore bounded. This is the compactness that produces minimizers of `F - u`, and so
preimages of `u` under the gradient `∇F`, in the proof that the gradient of a Legendre function is
onto the interior of the domain of its conjugate.

No convexity, lower semicontinuity or properness of `f` is assumed: the conjugate is always
convex, and the case `f ≡ ⊤`, where the conjugate is `⊥`, is allowed.

## Main statements

* `LMLExplore.fenchelConjugate_le_of_norm_sub_le`: linear growth of `f - u` at rate `r` bounds
  the conjugate by `M` on the closed ball of radius `r` around `u`.
* `LMLExplore.mem_interior_setOf_fenchelConjugate_ne_top_iff`: in finite dimension, `u` is
  interior to the domain of the conjugate if and only if `f - u` grows at least linearly.
* `LMLExplore.isBounded_setOf_le_of_mem_interior_setOf_fenchelConjugate_ne_top`: in finite
  dimension, the tilted sublevel sets of `f` are bounded when `u` is interior to the domain of
  the conjugate.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, Theorem 10.1 (continuity
  of convex functions) and Section 14 (the domain of the conjugate and the growth of tilts).
* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 26.5, Theorem 26.6 [LS].
-/

public section

open Filter Metric Set TauCeti
open scoped Topology

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal}
  {u v : E →L[ℝ] ℝ} {r M : ℝ}

/-- **Linear growth bounds the conjugate on a ball.** If `u x + r ‖x‖ - M ≤ f x` for every `x`,
then the conjugate of `f` is at most `M` at every `v` with `‖v - u‖ ≤ r`. -/
theorem fenchelConjugate_le_of_norm_sub_le
    (hf : ∀ x, ((u x + r * ‖x‖ - M : ℝ) : EReal) ≤ f x) (hv : ‖v - u‖ ≤ r) :
    fenchelConjugate (topDualPairing ℝ E).flip f v ≤ M := by
  refine fenchelConjugate_le _ fun x ↦ EReal.coe_sub_le_comm.2 ?_
  have hvx : v x - u x ≤ r * ‖x‖ := by
    rw [← sub_apply]
    exact (le_abs_self _).trans ((v - u).le_opNorm x |>.trans (by gcongr))
  rw [LinearMap.flip_apply, topDualPairing_apply, ← EReal.coe_sub]
  exact (EReal.coe_le_coe_iff.2 (by linarith)).trans (hf x)

/-- **Linear growth puts the tilt in the interior of the domain of the conjugate.** If
`u x + r ‖x‖ - M ≤ f x` for every `x`, with `r > 0`, then the conjugate of `f` is not `⊤` on a
neighbourhood of `u` (`u` is interior to the effective domain of `f⋆`). -/
theorem mem_interior_setOf_fenchelConjugate_ne_top_of_forall_le (hr : 0 < r)
    (hf : ∀ x, ((u x + r * ‖x‖ - M : ℝ) : EReal) ≤ f x) :
    u ∈ interior {v | fenchelConjugate (topDualPairing ℝ E).flip f v ≠ ⊤} := by
  refine mem_interior.2 ⟨ball u r, fun v hv ↦ ?_, isOpen_ball, mem_ball_self hr⟩
  rw [mem_ball, dist_eq_norm] at hv
  exact ne_top_of_le_ne_top (EReal.coe_ne_top M) (fenchelConjugate_le_of_norm_sub_le hf hv.le)

/-- **Linear growth of the tilt at an interior point of the domain of the conjugate.** In finite
dimension, if the conjugate of `f` is not `⊤` on a neighbourhood of `u`, then
`u x + r ‖x‖ - M ≤ f x` for every `x`, for some `r > 0` and some `M`. -/
theorem exists_forall_le_of_mem_interior_setOf_fenchelConjugate_ne_top [FiniteDimensional ℝ E]
    (hu : u ∈ interior {v | fenchelConjugate (topDualPairing ℝ E).flip f v ≠ ⊤}) :
    ∃ r > 0, ∃ M : ℝ, ∀ x, ((u x + r * ‖x‖ - M : ℝ) : EReal) ≤ f x := by
  set g := fenchelConjugate (topDualPairing ℝ E).flip f
  -- If `f ≡ ⊤`, every bound holds.
  by_cases htop : ∀ x, f x = ⊤
  · exact ⟨1, one_pos, 0, fun x ↦ by simp [htop x]⟩
  obtain ⟨x₀, hx₀⟩ := not_forall.1 htop
  -- Otherwise `g` is never `⊥`, so its real representative is convex on its domain, hence
  -- continuous at the interior point `u`, hence bounded above near `u`.
  have hbot : ∀ v, g v ≠ ⊥ := fenchelConjugate_ne_bot _ hx₀
  have hcont : ContinuousAt (fun v ↦ (g v).toReal) u :=
    ((convexOn_toReal (convex_epigraph_fenchelConjugate _ f) hbot).continuousOn_interior u
      hu).continuousAt (isOpen_interior.mem_nhds hu)
  have hev : ∀ᶠ v in 𝓝 u, g v ≤ (((g u).toReal + 1 : ℝ) : EReal) := by
    filter_upwards [hcont.eventually (gt_mem_nhds (lt_add_one (g u).toReal)),
      mem_interior_iff_mem_nhds.1 hu] with v hv hv'
    rw [← EReal.coe_toReal hv' (hbot v)]
    exact EReal.coe_le_coe_iff.2 hv.le
  obtain ⟨ρ, hρ, hball⟩ := eventually_nhds_iff_ball.1 hev
  -- Test the Fenchel–Young inequality at `u + (ρ / 2) φ`, where `φ` norms `x`.
  refine ⟨ρ / 2, half_pos hρ, (g u).toReal + 1, fun x ↦ ?_⟩
  obtain ⟨φ, hφ, hφx⟩ := exists_dual_vector'' ℝ x
  have hmem : u + (ρ / 2) • φ ∈ ball u ρ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (half_pos hρ).le]
    nlinarith
  have hFY := (sub_le_fenchelConjugate _ f x (u + (ρ / 2) • φ)).trans (hball _ hmem)
  simp only [LinearMap.flip_apply, topDualPairing_apply, add_apply,
    smul_apply, smul_eq_mul, hφx, RCLike.ofReal_real_eq_id, id] at hFY
  rw [EReal.coe_sub]
  exact EReal.coe_sub_le_comm.1 hFY

/-- **The interior of the domain of the conjugate.** In finite dimension, `u` is interior to
`{v | f⋆ v ≠ ⊤}` if and only if `f - u` grows at least linearly: `u x + r ‖x‖ - M ≤ f x` for every
`x`, for some `r > 0` and some `M`. -/
theorem mem_interior_setOf_fenchelConjugate_ne_top_iff [FiniteDimensional ℝ E] :
    u ∈ interior {v | fenchelConjugate (topDualPairing ℝ E).flip f v ≠ ⊤} ↔
      ∃ r > 0, ∃ M : ℝ, ∀ x, ((u x + r * ‖x‖ - M : ℝ) : EReal) ≤ f x :=
  ⟨exists_forall_le_of_mem_interior_setOf_fenchelConjugate_ne_top, fun ⟨_, hr, _, hf⟩ ↦
    mem_interior_setOf_fenchelConjugate_ne_top_of_forall_le hr hf⟩

/-- **Bounded tilted sublevel sets.** In finite dimension, if the conjugate of `f` is not `⊤` on a
neighbourhood of `u`, then every sublevel set `{x | f x ≤ u x + c}` of `f - u` is bounded. -/
theorem isBounded_setOf_le_of_mem_interior_setOf_fenchelConjugate_ne_top
    [FiniteDimensional ℝ E]
    (hu : u ∈ interior {v | fenchelConjugate (topDualPairing ℝ E).flip f v ≠ ⊤}) (c : ℝ) :
    Bornology.IsBounded {x | f x ≤ ((u x + c : ℝ) : EReal)} := by
  obtain ⟨r, hr, M, hf⟩ := exists_forall_le_of_mem_interior_setOf_fenchelConjugate_ne_top hu
  refine (isBounded_closedBall (x := (0 : E)) (r := (M + c) / r)).subset fun x hx ↦ ?_
  have h := EReal.coe_le_coe_iff.1 ((hf x).trans hx)
  rw [mem_closedBall_zero_iff, le_div_iff₀ hr]
  linarith

end LMLExplore
