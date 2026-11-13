/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.Basic
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Smooth functions and the descent lemma

A function `f : E → F` on a real normed space is `s`-smooth on a set `V`, in the sense of convex
optimization [Ora, Definition 4.22], if it is differentiable on an open set containing `V` and its
derivative is `s`-Lipschitz on `V` for the operator norm: `‖f' x - f' y‖ ≤ s * ‖x - y‖`. This is
not smoothness in the sense of `ContDiff`.

On a convex set, the first-order Taylor expansion of such a function is accurate up to a quadratic
term: the Bregman divergence `D_f(y, x) = f y - f x - f' x (y - x)` satisfies
`‖D_f(y, x)‖ ≤ s / 2 * ‖y - x‖ ^ 2` [Nes18, Lemma 1.2.3]. For a real function its upper half,
`f y ≤ f x + f' x (y - x) + s / 2 * ‖y - x‖ ^ 2`, is the **descent lemma** of smooth optimization.

The bound is first proved for a derivative within the set at its points, with no open set around
it. This covers sets with empty interior, such as the simplex in `α → ℝ`, on which the inexact
mirror descent analysis of [SSKM26, Lemma 22, Theorem 2] uses it.

The proof of `Convex.norm_bregDiv_le_mul_norm_sub_sq` and its within-set form are adapted from the
formalization in the paper project RemyDegenne/Schlisselberg2026Hidden
(<https://github.com/RemyDegenne/Schlisselberg2026Hidden>, file
`Schlisselberg2026Hidden/ForLMLExplore/Analysis/Convex/Smooth.lean`, commit
`b08c8189133af6a5a8578c04ff6ae061acbdec60`, Apache-2.0).

## Main definitions

* `LMLExplore.SmoothOn V s f`: `f` is differentiable on an open set containing `V` and
  `fderiv ℝ f` is `s`-Lipschitz on `V`.

## Main statements

* `Convex.norm_bregDiv_le_mul_norm_sub_sq`: for a family `f'` of derivatives of `f` within a
  convex set `K`, `s`-Lipschitz on `K`, `‖D_f(y, x)‖ ≤ s / 2 * ‖y - x‖ ^ 2` for `x, y ∈ K`.
* `Convex.bregDiv_le_mul_norm_sub_sq`: the descent lemma in that setting, for a real function.
* `LMLExplore.SmoothOn.norm_bregDiv_le_mul_norm_sub_sq`: `‖D_f(y, x)‖ ≤ s / 2 * ‖y - x‖ ^ 2` for an
  `s`-smooth function on a convex set, with `fderiv`. For `F = ℝ` this is the two-sided bound
  `|D_f(y, x)| ≤ s / 2 * ‖y - x‖ ^ 2`.
* `LMLExplore.SmoothOn.bregDiv_le_mul_norm_sub_sq`: the descent lemma for an `s`-smooth real
  function on a convex set.

## References

* [Nes18] Y. Nesterov, *Lectures on Convex Optimization*, 2nd ed., Springer, 2018.
* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

public section

open Set AffineMap

open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {K V W : Set E} {s t : ℝ≥0} {x y : E}

namespace Convex

/-- **Quadratic bound on the first-order Taylor remainder** [Nes18, Lemma 1.2.3]. Let `K` be
convex and let `f` have a derivative `f' z` within `K` at every `z ∈ K`, with `f'` `s`-Lipschitz
on `K`. Then for `x, y ∈ K`, the Bregman divergence `D_f(y, x) = f y - f x - f' x (y - x)`
satisfies `‖D_f(y, x)‖ ≤ s / 2 * ‖y - x‖ ^ 2`. -/
theorem norm_bregDiv_le_mul_norm_sub_sq (hK : Convex ℝ K) {f : E → F} {f' : E → E →L[ℝ] F}
    (hf : ∀ z ∈ K, HasFDerivWithinAt f (f' z) K z) (hf' : LipschitzOnWith s f' K) (hx : x ∈ K)
    (hy : y ∈ K) :
    ‖bregDiv f y x (f' x)‖ ≤ s / 2 * ‖y - x‖ ^ 2 := by
  -- restrict `f` to the segment `t ↦ lineMap x y t`, `t ∈ [0, 1]`, which `K` contains
  have hmaps : MapsTo (lineMap x y) (Icc (0 : ℝ) 1) K := fun t ht ↦ hK.lineMap_mem hx hy ht
  -- the remainder `g t = f (lineMap x y t) - f x - t • f' x (y - x)` has derivative
  -- `f' (lineMap x y t) (y - x) - f' x (y - x)`, and `g 1 = D_f(y, x)`
  set g : ℝ → F := fun t ↦ f (lineMap x y t) - f x - t • f' x (y - x) with hg_def
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt g (f' (lineMap x y t) (y - x) - f' x (y - x)) (Icc 0 1) t := by
    have h1 : HasDerivWithinAt (f ∘ lineMap x y) (f' (lineMap x y t) (y - x)) (Icc 0 1) t :=
      (hf _ (hmaps ht)).comp_hasDerivWithinAt t hasDerivWithinAt_lineMap hmaps
    have h2 := ((hasDerivAt_id t).smul_const (f' x (y - x))).hasDerivWithinAt (s := Icc 0 1)
    rw [one_smul] at h2
    exact (h1.sub_const (f x)).fun_sub h2
  have hg_right (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      HasDerivWithinAt g (f' (lineMap x y t) (y - x) - f' x (y - x)) (Ici t) t :=
    (hg t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))
  -- the derivative of the remainder is at most `s t ‖y - x‖²` in norm, the derivative of the
  -- bound `s / 2 * t ^ 2 * ‖y - x‖ ^ 2`
  have h_bound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖f' (lineMap x y t) (y - x) - f' x (y - x)‖ ≤ s * t * ‖y - x‖ ^ 2 := by
    rw [← sub_apply]
    calc ‖(f' (lineMap x y t) - f' x) (y - x)‖
    _ ≤ ‖f' (lineMap x y t) - f' x‖ * ‖y - x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ s * dist (lineMap x y t) x * ‖y - x‖ := by
      rw [← dist_eq_norm]
      gcongr
      exact hf'.dist_le_mul _ (hmaps (Ico_subset_Icc_self ht)) _ hx
    _ = s * t * ‖y - x‖ ^ 2 := by
      rw [dist_lineMap_left, Real.norm_of_nonneg ht.1, dist_eq_norm']
      ring
  have hB (t : ℝ) : HasDerivAt (fun t ↦ s / 2 * t ^ 2 * ‖y - x‖ ^ 2) (s * t * ‖y - x‖ ^ 2) t := by
    convert ((hasDerivAt_pow 2 t).const_mul ((s : ℝ) / 2)).mul_const (‖y - x‖ ^ 2) using 1
    ring
  have h_main := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun t ht ↦ (hg t ht).continuousWithinAt) hg_right (by simp [hg_def]) hB h_bound
    (right_mem_Icc.mpr zero_le_one)
  have h_one : g 1 = bregDiv f y x (f' x) := by
    simp [hg_def, bregDiv]
  rwa [h_one, one_pow, mul_one] at h_main

/-- **The descent lemma** [Nes18, Lemma 1.2.3]. Let `K` be convex and let `f` have a derivative
`f' z` within `K` at every `z ∈ K`, with `f'` `s`-Lipschitz on `K`. Then for `x, y ∈ K`,
`f y ≤ f x + f' x (y - x) + s / 2 * ‖y - x‖ ^ 2`, in the form
`D_f(y, x) ≤ s / 2 * ‖y - x‖ ^ 2` of the Bregman divergence. -/
theorem bregDiv_le_mul_norm_sub_sq (hK : Convex ℝ K) {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ z ∈ K, HasFDerivWithinAt f (f' z) K z) (hf' : LipschitzOnWith s f' K) (hx : x ∈ K)
    (hy : y ∈ K) :
    bregDiv f y x (f' x) ≤ s / 2 * ‖y - x‖ ^ 2 :=
  (le_abs_self _).trans (hK.norm_bregDiv_le_mul_norm_sub_sq hf hf' hx hy)

end Convex

namespace LMLExplore

/-- A function `f : E → F` is **`s`-smooth on `V`** [Ora, Definition 4.22] if it is
differentiable on an open set containing `V` and its derivative `fderiv ℝ f` is `s`-Lipschitz on
`V`, for the operator norm: `‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ s * ‖x - y‖` for `x, y ∈ V`. This is
smoothness in the sense of convex optimization, not `ContDiff`. -/
structure SmoothOn (V : Set E) (s : ℝ≥0) (f : E → F) : Prop where
  /-- `f` is differentiable on an open set containing `V`. -/
  exists_isOpen_differentiableOn : ∃ U, IsOpen U ∧ V ⊆ U ∧ DifferentiableOn ℝ f U
  /-- The derivative of `f` is `s`-Lipschitz on `V`. -/
  lipschitzOnWith : LipschitzOnWith s (fderiv ℝ f) V

namespace SmoothOn

variable {f : E → F}

/-- An `s`-smooth function on `V` is differentiable at every point of `V`. -/
theorem differentiableAt (hf : SmoothOn V s f) (hx : x ∈ V) : DifferentiableAt ℝ f x := by
  obtain ⟨U, hU, hVU, hfU⟩ := hf.exists_isOpen_differentiableOn
  exact hfU.differentiableAt (hU.mem_nhds (hVU hx))

/-- An `s`-smooth function on `V` is differentiable on `V`. -/
theorem differentiableOn (hf : SmoothOn V s f) : DifferentiableOn ℝ f V :=
  fun _ hx ↦ (hf.differentiableAt hx).differentiableWithinAt

/-- An `s`-smooth function on `V` is `s`-smooth on every subset of `V`. -/
theorem mono (hf : SmoothOn V s f) (hWV : W ⊆ V) : SmoothOn W s f where
  exists_isOpen_differentiableOn := by
    obtain ⟨U, hU, hVU, hfU⟩ := hf.exists_isOpen_differentiableOn
    exact ⟨U, hU, hWV.trans hVU, hfU⟩
  lipschitzOnWith := hf.lipschitzOnWith.mono hWV

/-- An `s`-smooth function is `t`-smooth for every `t ≥ s`. -/
protected theorem weaken (hf : SmoothOn V s f) (hst : s ≤ t) : SmoothOn V t f where
  exists_isOpen_differentiableOn := hf.exists_isOpen_differentiableOn
  lipschitzOnWith := hf.lipschitzOnWith.weaken hst

/-- **Quadratic bound on the first-order Taylor remainder** [Nes18, Lemma 1.2.3]. If `f` is
`s`-smooth on a convex set `V`, then for `x, y ∈ V`, the Bregman divergence
`D_f(y, x) = f y - f x - fderiv ℝ f x (y - x)` satisfies `‖D_f(y, x)‖ ≤ s / 2 * ‖y - x‖ ^ 2`. -/
theorem norm_bregDiv_le_mul_norm_sub_sq (hf : SmoothOn V s f) (hV : Convex ℝ V) (hx : x ∈ V)
    (hy : y ∈ V) :
    ‖bregDiv f y x (fderiv ℝ f x)‖ ≤ s / 2 * ‖y - x‖ ^ 2 :=
  hV.norm_bregDiv_le_mul_norm_sub_sq
    (fun _ hz ↦ (hf.differentiableAt hz).hasFDerivAt.hasFDerivWithinAt) hf.lipschitzOnWith hx hy

/-- **The descent lemma** [Nes18, Lemma 1.2.3]. If `f` is `s`-smooth on a convex set `V`, then for
`x, y ∈ V`, `f y ≤ f x + fderiv ℝ f x (y - x) + s / 2 * ‖y - x‖ ^ 2`, in the form
`D_f(y, x) ≤ s / 2 * ‖y - x‖ ^ 2` of the Bregman divergence. -/
theorem bregDiv_le_mul_norm_sub_sq {f : E → ℝ} (hf : SmoothOn V s f) (hV : Convex ℝ V)
    (hx : x ∈ V) (hy : y ∈ V) :
    bregDiv f y x (fderiv ℝ f x) ≤ s / 2 * ‖y - x‖ ^ 2 :=
  (le_abs_self _).trans (hf.norm_bregDiv_le_mul_norm_sub_sq hV hx hy)

end SmoothOn

/-- A function is `s`-smooth on the whole space if and only if it is differentiable and its
derivative is `s`-Lipschitz. -/
@[simp]
theorem smoothOn_univ {f : E → F} :
    SmoothOn univ s f ↔ Differentiable ℝ f ∧ LipschitzWith s (fderiv ℝ f) := by
  refine ⟨fun hf ↦ ⟨fun x ↦ hf.differentiableAt (mem_univ x),
    lipschitzOnWith_univ.mp hf.lipschitzOnWith⟩, fun ⟨hd, hl⟩ ↦ ⟨?_, hl.lipschitzOnWith⟩⟩
  exact ⟨univ, isOpen_univ, subset_rfl, hd.differentiableOn⟩

end LMLExplore

/-- On an open set `V`, a function is `s`-smooth if and only if it is differentiable on `V` and its
derivative is `s`-Lipschitz on `V`. -/
theorem IsOpen.smoothOn_iff (hV : IsOpen V) {f : E → F} :
    LMLExplore.SmoothOn V s f ↔ DifferentiableOn ℝ f V ∧ LipschitzOnWith s (fderiv ℝ f) V :=
  ⟨fun hf ↦ ⟨hf.differentiableOn, hf.lipschitzOnWith⟩,
    fun ⟨hd, hl⟩ ↦ ⟨⟨V, hV, subset_rfl, hd⟩, hl⟩⟩
