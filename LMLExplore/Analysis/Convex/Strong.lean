/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Basic
public import LMLExplore.Analysis.Convex.Bregman.Taylor
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Strong convexity through subgradients

A function `f` on a real normed space is `m`-strongly convex on a set `s`, in Mathlib's sense
`StrongConvexOn s m f`, if
`f (a • x + b • y) ≤ a * f x + b * f y - a * b * (m / 2 * ‖x - y‖ ^ 2)` for `x, y ∈ s` and
`a, b ≥ 0` with `a + b = 1`. This file characterizes strong convexity through the subgradients
within `s` of LML's `HasSubgradientWithinAt`, which need no differentiability of `f` and make
sense at every point of `s`, including its boundary [Ora, Lemma 4.2, Theorems 4.3 and 6.9]:

* an `m`-strongly convex function lies above the paraboloid `f x + g (y - x) + m / 2 * ‖y - x‖ ^ 2`
  for each of its subgradients `g` within `s` at `x ∈ s`, and conversely a function lying above
  such a paraboloid at every point of a convex set is `m`-strongly convex there;
* when every point of `s` has a subgradient within `s`, strong convexity is equivalent to the
  strong monotonicity `m * ‖x - y‖ ^ 2 ≤ (g_x - g_y) (x - y)` of the subgradients;
* a function whose second derivative satisfies `m * ‖y - x‖ ^ 2 ≤ f'' z (y - x) (y - x)` at the
  points `z` of each segment `[x, y]` of a convex set is `m`-strongly convex there;
* an `m`-strongly convex function grows quadratically away from a minimizer, and, for `m > 0` in
  finite dimension, a lower semicontinuous `m`-strongly convex function on a nonempty closed set
  has exactly one minimizer there.

The last statement is what makes the plays of follow the regularized leader and mirror descent
with a strongly convex potential exist on closed sets that need not be bounded.

## Main statements

* `StrongConvexOn.add`: [Ora, Theorem 4.6] the sum of an `m`-strongly convex and an `n`-strongly
  convex function is `(m + n)`-strongly convex.
* `UniformConvexOn.smul`, `StrongConvexOn.smul`: a nonnegative multiple `c • f` of a uniformly
  convex function with modulus `φ` is uniformly convex with modulus `c • φ`; of an `m`-strongly
  convex function, it is `(c * m)`-strongly convex.
* `StrongConvexOn.add_add_le_of_hasSubgradientWithinAt`: [Ora, Lemma 4.2] the subgradient
  inequality `f x + g (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y` of a strongly convex function.
* `Convex.strongConvexOn_of_forall_exists_add_add_le`,
  `Convex.strongConvexOn_iff_forall_add_add_le`: [Ora, Lemma 4.2] the converse, and the resulting
  characterization.
* `StrongConvexOn.mul_norm_sub_sq_le_sub_apply_sub`,
  `Convex.strongConvexOn_of_mul_norm_sub_sq_le_sub_apply_sub`,
  `Convex.strongConvexOn_iff_mul_norm_sub_sq_le_sub_apply_sub`: [Ora, Theorem 4.3] strong
  convexity is strong monotonicity of the subgradients.
* `Convex.strongConvexOn_of_hasFDerivWithinAt2_mul_norm_sub_sq_le`: [Ora, Theorem 4.3] the
  second-order criterion along segments.
* `StrongConvexOn.add_mul_norm_sub_sq_le_of_isMinOn`: quadratic growth away from a minimizer.
* `StrongConvexOn.exists_forall_lt_of_lowerSemicontinuousWithinAt`: for `m > 0`, `f` exceeds its
  value at a point of lower semicontinuity on the points of `s` far enough from it.
* `StrongConvexOn.exists_isMinOn`, `StrongConvexOn.existsUnique_isMinOn`: [Ora, Theorem 6.9]
  existence and uniqueness of the minimizer of a lower semicontinuous strongly convex function on a
  closed set, in finite dimension.
* `StrongConvexOn.exists_isMinOn_add_continuousLinearMap`: the same existence for `f` plus a
  continuous linear map, as in the objectives of follow the regularized leader and mirror descent.
* `LMLExplore.apply_sub_sub_div_le_of_mul_norm_sq_le`: `y (a - b) - D / η ≤ η / (2 m) * ‖y‖ ^ 2`
  for a continuous linear functional `y` when `m / 2 * ‖b - a‖ ^ 2 ≤ D`, with `‖y‖` the dual norm;
  with a divergence `D` dominating the strong convexity term, it bounds the stability terms of
  follow the regularized leader and mirror descent.
* `LMLExplore.apply_sub_sub_mul_norm_sq_le`: its quadratic case
  `g (a - b) - lam / 2 * ‖a - b‖ ^ 2 ≤ ‖g‖ ^ 2 / (2 lam)` for `lam > 0`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Corollary 28.8.
* [Ora] F. Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*,
  arXiv:1912.13213v10, Lemma 4.2, Theorems 4.3, 4.6 and 6.9.
-/

public section

open Filter Finset Metric Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {m n : ℝ}
  {f g : E → ℝ} {x y : E}

/-- A nonnegative multiple `c • f` of a uniformly convex function with modulus `φ` on `s` is
uniformly convex on `s` with modulus `c • φ`. -/
theorem UniformConvexOn.smul {φ : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hf : UniformConvexOn s φ f) :
    UniformConvexOn s (c • φ) fun x ↦ c • f x := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  have h := mul_le_mul_of_nonneg_left (hf.2 hx hy ha hb hab) hc
  simp only [Pi.smul_apply, smul_eq_mul] at h ⊢
  linarith

namespace StrongConvexOn

/-- **Sums of strongly convex functions** [Ora, Theorem 4.6]. The sum of an `m`-strongly convex
function and an `n`-strongly convex function on `s` is `(m + n)`-strongly convex on `s`. -/
theorem add (hf : StrongConvexOn s m f) (hg : StrongConvexOn s n g) :
    StrongConvexOn s (m + n) (f + g) :=
  (UniformConvexOn.add hf hg).mono fun r ↦ le_of_eq (by simp only [Pi.add_apply]; ring)

/-- The sum of an `m`-strongly convex function and a convex function on `s` is `m`-strongly convex
on `s`. -/
theorem add_convexOn (hf : StrongConvexOn s m f) (hg : ConvexOn ℝ s g) :
    StrongConvexOn s m (f + g) := by
  simpa using hf.add (strongConvexOn_zero.2 hg)

/-- A nonnegative multiple `c • f` of an `m`-strongly convex function on `s` is
`(c * m)`-strongly convex on `s`. -/
theorem smul {c : ℝ} (hc : 0 ≤ c) (hf : StrongConvexOn s m f) :
    StrongConvexOn s (c * m) fun x ↦ c • f x :=
  (UniformConvexOn.smul hc hf).mono fun r ↦
    le_of_eq (by simp only [Pi.smul_apply, smul_eq_mul]; ring)

/-- **The subgradient inequality of a strongly convex function** [Ora, Lemma 4.2].
If `f` is `m`-strongly convex on `s` and `g` is a subgradient of `f` within `s` at `x ∈ s`, then
`f` lies above the paraboloid `f x + g (y - x) + m / 2 * ‖y - x‖ ^ 2` on `s`. The modulus `m` may
be negative, and `f` need not be differentiable. -/
theorem add_add_le_of_hasSubgradientWithinAt (hf : StrongConvexOn s m f) (hx : x ∈ s)
    (hy : y ∈ s) {g : E →L[ℝ] ℝ} (hg : HasSubgradientWithinAt f g s x) :
    f x + g (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  -- At `z = (1 - t) • x + t • y`, compare the subgradient inequality with strong convexity.
  have key : ∀ t ∈ Ioo (0 : ℝ) 1, f x + g (y - x) + (1 - t) * (m / 2 * ‖y - x‖ ^ 2) ≤ f y := by
    intro t ht
    have hab : 1 - t + t = 1 := sub_add_cancel 1 t
    have hconv := hf.2 hx hy (sub_nonneg.2 ht.2.le) ht.1.le hab
    have hsub :=
      hasSubgradientWithinAt_iff_le.1 hg _ (hf.1 hx hy (sub_nonneg.2 ht.2.le) ht.1.le hab)
    rw [show (1 - t) • x + t • y - x = t • (y - x) by module, map_smul, smul_eq_mul] at hsub
    simp only [smul_eq_mul, norm_sub_rev x y] at hconv
    refine le_of_mul_le_mul_left ?_ ht.1
    linarith
  -- Let `t` tend to `0`.
  have hlim : Tendsto (fun t : ℝ ↦ f x + g (y - x) + (1 - t) * (m / 2 * ‖y - x‖ ^ 2)) (𝓝[>] 0)
      (𝓝 (f x + g (y - x) + (1 - 0) * (m / 2 * ‖y - x‖ ^ 2))) :=
    ((continuous_const.add ((continuous_const.sub continuous_id).mul continuous_const)).tendsto
      0).mono_left nhdsWithin_le_nhds
  simpa using le_of_tendsto hlim (mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) key)

/-- **Strong monotonicity of the subgradients** [Ora, Theorem 4.3]. If `f` is `m`-strongly convex
on `s`, then its subgradients `g_x` and `g_y` within `s` at `x, y ∈ s` satisfy
`m * ‖x - y‖ ^ 2 ≤ (g_x - g_y) (x - y)`. -/
theorem mul_norm_sub_sq_le_sub_apply_sub (hf : StrongConvexOn s m f) (hx : x ∈ s) (hy : y ∈ s)
    {gx gy : E →L[ℝ] ℝ} (hgx : HasSubgradientWithinAt f gx s x)
    (hgy : HasSubgradientWithinAt f gy s y) :
    m * ‖x - y‖ ^ 2 ≤ (gx - gy) (x - y) := by
  have h₁ := hf.add_add_le_of_hasSubgradientWithinAt hx hy hgx
  have h₂ := hf.add_add_le_of_hasSubgradientWithinAt hy hx hgy
  rw [norm_sub_rev y x, show y - x = -(x - y) by abel, map_neg] at h₁
  rw [sub_apply]
  linarith

/-- **Quadratic growth away from a minimizer.** If `f` is `m`-strongly convex on `s` and `x ∈ s`
minimizes `f` on `s`, then `f x + m / 2 * ‖y - x‖ ^ 2 ≤ f y` for every `y ∈ s`. -/
theorem add_mul_norm_sub_sq_le_of_isMinOn (hf : StrongConvexOn s m f) (hx : x ∈ s)
    (hmin : IsMinOn f s x) (hy : y ∈ s) :
    f x + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  simpa using hf.add_add_le_of_hasSubgradientWithinAt hx hy
    (hasSubgradientWithinAt_zero_iff_isMinOn.2 hmin)

end StrongConvexOn

namespace Convex

/-- **Strong convexity from paraboloids below** [Ora, Lemma 4.2]. If every point `x` of a convex
set `s` has a linear map `g` such that `f` lies above the paraboloid
`f x + g (y - x) + m / 2 * ‖y - x‖ ^ 2` on `s`, then `f` is `m`-strongly convex on `s`. For
`m ≥ 0` such a `g` is a subgradient of `f` within `s` at `x`. -/
theorem strongConvexOn_of_forall_exists_add_add_le (hs : Convex ℝ s)
    (h : ∀ x ∈ s, ∃ g : E →L[ℝ] ℝ, ∀ y ∈ s, f x + g (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y) :
    StrongConvexOn s m f := by
  refine ⟨hs, fun x hx y hy a b ha hb hab ↦ ?_⟩
  -- Average the paraboloid inequalities at `z = a • x + b • y`, towards `x` and towards `y`.
  obtain ⟨g, hg⟩ := h _ (hs hx hy ha hb hab)
  have h₁ := hg x hx
  have h₂ := hg y hy
  obtain rfl : b = 1 - a := by linarith
  rw [show x - (a • x + (1 - a) • y) = (1 - a) • (x - y) by module, map_smul, norm_smul,
    Real.norm_of_nonneg hb, smul_eq_mul] at h₁
  rw [show y - (a • x + (1 - a) • y) = -(a • (x - y)) by module, map_neg, map_smul, norm_neg,
    norm_smul, Real.norm_of_nonneg ha, smul_eq_mul] at h₂
  simp only [smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h₁ ha, mul_le_mul_of_nonneg_left h₂ hb]

/-- **Strong convexity through subgradients** [Ora, Lemma 4.2]. On a convex set `s`
at each point of which `f` has a subgradient within `s`, `f` is `m`-strongly convex if and only if
it lies above the paraboloid `f x + g (y - x) + m / 2 * ‖y - x‖ ^ 2` for each subgradient `g`
within `s` at each `x ∈ s`. -/
theorem strongConvexOn_iff_forall_add_add_le (hs : Convex ℝ s)
    (hsub : ∀ x ∈ s, ∃ g : E →L[ℝ] ℝ, HasSubgradientWithinAt f g s x) :
    StrongConvexOn s m f ↔ ∀ x ∈ s, ∀ g : E →L[ℝ] ℝ, HasSubgradientWithinAt f g s x →
      ∀ y ∈ s, f x + g (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y :=
  ⟨fun hf _ hx _ hg _ hy ↦ hf.add_add_le_of_hasSubgradientWithinAt hx hy hg,
    fun h ↦ strongConvexOn_of_forall_exists_add_add_le hs fun x hx ↦
      (hsub x hx).imp fun g hg ↦ h x hx g hg⟩

/-- The paraboloid inequality from strongly monotone subgradients, up to the error
`m / 2 * ‖y - x‖ ^ 2 / (N + 1)` of the Riemann sum of the subgradients over the points
`x + k / (N + 1) • (y - x)` of the segment `[x, y]`. -/
private lemma add_add_sub_le_of_mul_norm_sub_sq_le_sub_apply_sub (hs : Convex ℝ s)
    {g : E → E →L[ℝ] ℝ} (hg : ∀ x ∈ s, HasSubgradientWithinAt f (g x) s x)
    (hmono : ∀ x ∈ s, ∀ y ∈ s, m * ‖x - y‖ ^ 2 ≤ (g x - g y) (x - y)) (hx : x ∈ s) (hy : y ∈ s)
    (N : ℕ) :
    f x + g x (y - x) + m / 2 * ‖y - x‖ ^ 2 - m / 2 * ‖y - x‖ ^ 2 * (1 / ((N : ℝ) + 1)) ≤ f y := by
  set M : ℝ := N + 1 with hM
  clear_value M
  have hM0 : 0 < M := by rw [hM]; positivity
  have hNM : ((N + 1 : ℕ) : ℝ) = M := by rw [hM]; push_cast; rfl
  set z : ℕ → E := fun k ↦ x + ((k : ℝ) / M) • (y - x) with hz
  have hzs (k : ℕ) (hk : k ≤ N + 1) : z k ∈ s := by
    refine hs.add_smul_sub_mem hx hy ⟨by positivity, (div_le_one hM0).2 ?_⟩
    rw [hM]
    exact_mod_cast hk
  -- Each step `z k → z (k + 1)` gains at least `g (z k) (y - x) / M`, by the subgradient
  -- inequality at `z k`, and `g (z k) (y - x) ≥ g x (y - x) + m * k / M * ‖y - x‖ ^ 2`, by strong
  -- monotonicity between `z k` and `z 0 = x`.
  have hstep (k : ℕ) (hkN : k < N + 1) :
      1 / M * (g x (y - x) + m * (k / M) * ‖y - x‖ ^ 2) ≤ f (z (k + 1)) - f (z k) := by
    have h₁ := hasSubgradientWithinAt_iff_le.1 (hg _ (hzs k hkN.le)) _ (hzs (k + 1) hkN)
    rw [show z (k + 1) - z k = (1 / M) • (y - x) by simp only [hz]; push_cast; module, map_smul,
      smul_eq_mul] at h₁
    have h₂ : g x (y - x) + m * (k / M) * ‖y - x‖ ^ 2 ≤ g (z k) (y - x) := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp [hz]
      have hkM : 0 < (k : ℝ) / M := by positivity
      have h := hmono _ (hzs k hkN.le) x hx
      rw [show z k - x = ((k : ℝ) / M) • (y - x) by simp only [hz]; abel, map_smul, norm_smul,
        Real.norm_of_nonneg hkM.le, smul_eq_mul, sub_apply] at h
      refine le_of_mul_le_mul_left ?_ hkM
      nlinarith
    linarith [mul_le_mul_of_nonneg_left h₂ (by positivity : (0 : ℝ) ≤ 1 / M)]
  -- Sum the steps: after `j` of them, `f` has gained `j / M * g x (y - x)`, plus
  -- `m / 2 * j * (j - 1) / M ^ 2 * ‖y - x‖ ^ 2`.
  have hsum (j : ℕ) (hj : j ≤ N + 1) :
      f x + j / M * g x (y - x) + m / 2 * (j * (j - 1) / M ^ 2) * ‖y - x‖ ^ 2 ≤ f (z j) := by
    induction j with
    | zero => simp [hz]
    | succ j ih =>
      push_cast
      linear_combination ih (by omega) + hstep j hj
  have hN := hsum (N + 1) le_rfl
  simp only [hz, hNM, div_self hM0.ne', one_smul, add_sub_cancel] at hN
  field_simp at hN ⊢
  linarith

/-- **Strong convexity from strongly monotone subgradients** [Ora, Theorem 4.3]. Let `g x` be a
subgradient of `f` within a convex set `s` at each `x ∈ s`. If
`m * ‖x - y‖ ^ 2 ≤ (g x - g y) (x - y)` for `x, y ∈ s`, then `f` is `m`-strongly convex on `s`. -/
theorem strongConvexOn_of_mul_norm_sub_sq_le_sub_apply_sub (hs : Convex ℝ s)
    {g : E → E →L[ℝ] ℝ} (hg : ∀ x ∈ s, HasSubgradientWithinAt f (g x) s x)
    (hmono : ∀ x ∈ s, ∀ y ∈ s, m * ‖x - y‖ ^ 2 ≤ (g x - g y) (x - y)) :
    StrongConvexOn s m f := by
  refine strongConvexOn_of_forall_exists_add_add_le hs fun x hx ↦ ⟨g x, fun y hy ↦ ?_⟩
  -- Let the number of steps of the Riemann sum tend to infinity.
  have hlim := (tendsto_const_nhds (x := f x + g x (y - x) + m / 2 * ‖y - x‖ ^ 2)).sub
    ((tendsto_const_nhds (x := m / 2 * ‖y - x‖ ^ 2)).mul tendsto_one_div_add_atTop_nhds_zero_nat)
  rw [mul_zero, sub_zero] at hlim
  exact le_of_tendsto' hlim (add_add_sub_le_of_mul_norm_sub_sq_le_sub_apply_sub hs hg hmono hx hy)

/-- **Strong convexity is strong monotonicity of the subgradients** [Ora, Theorem 4.3]. On a convex
set `s` at each point of which `f` has a subgradient within `s`, `f` is `m`-strongly convex if and
only if `m * ‖x - y‖ ^ 2 ≤ (g_x - g_y) (x - y)` for all subgradients `g_x` and `g_y` within `s` at
`x, y ∈ s`. -/
theorem strongConvexOn_iff_mul_norm_sub_sq_le_sub_apply_sub (hs : Convex ℝ s)
    (hsub : ∀ x ∈ s, ∃ g : E →L[ℝ] ℝ, HasSubgradientWithinAt f g s x) :
    StrongConvexOn s m f ↔ ∀ x ∈ s, ∀ y ∈ s, ∀ gx gy : E →L[ℝ] ℝ,
      HasSubgradientWithinAt f gx s x → HasSubgradientWithinAt f gy s y →
        m * ‖x - y‖ ^ 2 ≤ (gx - gy) (x - y) := by
  refine ⟨fun hf _ hx _ hy _ _ hgx hgy ↦ hf.mul_norm_sub_sq_le_sub_apply_sub hx hy hgx hgy,
    fun h ↦ ?_⟩
  choose! g hg using hsub
  exact strongConvexOn_of_mul_norm_sub_sq_le_sub_apply_sub hs hg fun x hx y hy ↦
    h x hx y hy _ _ (hg x hx) (hg y hy)

/-- **The second-order criterion for strong convexity along segments** [Ora, Theorem 4.3]. Let
`f` have derivative `f' z` and `f'` have derivative `f'' z` within a convex set `s`, at every
`z ∈ s`. If
`m * ‖y - x‖ ^ 2 ≤ f'' z (y - x) (y - x)` for `x, y ∈ s` and every `z` of the segment `[x, y]`,
then `f` is `m`-strongly convex on `s`. Only the directions `y - x` of segments of `s` are tested,
so the criterion applies to sets with empty interior. -/
theorem strongConvexOn_of_hasFDerivWithinAt2_mul_norm_sub_sq_le (hs : Convex ℝ s)
    {f' : E → E →L[ℝ] ℝ} {f'' : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ z ∈ s, HasFDerivWithinAt f (f' z) s z)
    (hf' : ∀ z ∈ s, HasFDerivWithinAt f' (f'' z) s z)
    (hm : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ segment ℝ x y, m * ‖y - x‖ ^ 2 ≤ f'' z (y - x) (y - x)) :
    StrongConvexOn s m f := by
  refine strongConvexOn_of_forall_exists_add_add_le hs fun x hx ↦ ⟨f' x, fun y hy ↦ ?_⟩
  obtain ⟨z, hz, heq⟩ := hs.exists_mem_segment_bregDiv_eq hf hf' hy hx
  have := hm x hx y hy z (segment_symm ℝ y x ▸ hz)
  simp only [bregDiv] at heq
  linarith

end Convex

namespace StrongConvexOn

/-- **Growth of a strongly convex function far from a point.** If `f` is `m`-strongly convex on
`s` for some `m > 0` and lower semicontinuous within `s` at `x₀ ∈ s`, then `f x₀ < f y` for every
`y ∈ s` far enough from `x₀`. -/
theorem exists_forall_lt_of_lowerSemicontinuousWithinAt {x₀ : E} (hf : StrongConvexOn s m f)
    (hm : 0 < m) (hx₀ : x₀ ∈ s) (hf_lsc : LowerSemicontinuousWithinAt f s x₀) :
    ∃ R, ∀ y ∈ s, R < ‖y - x₀‖ → f x₀ < f y := by
  -- By lower semicontinuity, `f > f x₀ - 1` on the points of `s` in a ball `B(x₀, δ)`.
  obtain ⟨δ, hδ, hδf⟩ :=
    Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 (hf_lsc _ (sub_one_lt _)))
  set r := δ / 2 with hr
  -- By strong convexity along `[x₀, y]`, `f y > f x₀` for `y ∈ s` outside
  -- `closedBall x₀ (max δ (4 / (m * r)))`, comparing with the point at distance `r` from `x₀`.
  refine ⟨max δ (4 / (m * r)), fun y hy hyR ↦ ?_⟩
  set d := ‖y - x₀‖ with hd
  have hδd : δ < d := (le_max_left _ _).trans_lt hyR
  have hmrd : 4 < m * r * d := by
    have := (le_max_right _ _).trans_lt hyR
    rwa [div_lt_iff₀' (by positivity)] at this
  set t := r / d with ht
  have hd0 : 0 < d := hδ.trans hδd
  have htd : t * d = r := div_mul_cancel₀ r hd0.ne'
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 / 2 := by rw [ht, div_le_iff₀ hd0]; linarith
  have hz := hδf (y := (1 - t) • x₀ + t • y) (by
    rw [dist_eq_norm, show (1 - t) • x₀ + t • y - x₀ = t • (y - x₀) by module, norm_smul,
      Real.norm_of_nonneg ht0.le, htd]
    linarith) (hf.1 hx₀ hy (by linarith) ht0.le (sub_add_cancel 1 t))
  have hconv := hf.2 hx₀ hy (by linarith) ht0.le (sub_add_cancel 1 t)
  simp only [smul_eq_mul, norm_sub_rev x₀ y, ← hd] at hconv
  refine lt_of_mul_lt_mul_left ?_ ht0.le
  nlinarith [mul_le_mul_of_nonneg_left (show 1 / 2 ≤ 1 - t by linarith)
    (show 0 ≤ m * r * d by positivity)]

/-- **Existence of a minimizer of a strongly convex function** [Ora, Theorem 6.9]. In finite
dimension, a function that is `m`-strongly convex for some `m > 0` and lower semicontinuous on a
nonempty closed set `s` attains its minimum on `s`. The set `s` need not be bounded. -/
theorem exists_isMinOn [FiniteDimensional ℝ E] (hf : StrongConvexOn s m f) (hm : 0 < m)
    (hs : IsClosed s) (hs_ne : s.Nonempty) (hf_lsc : LowerSemicontinuousOn f s) :
    ∃ x ∈ s, IsMinOn f s x := by
  obtain ⟨x₀, hx₀⟩ := hs_ne
  obtain ⟨R, hfar⟩ := hf.exists_forall_lt_of_lowerSemicontinuousWithinAt hm hx₀ (hf_lsc x₀ hx₀)
  -- `R ≥ 0`, since `f x₀ < f x₀` fails. A minimizer over the compact set `s ∩ closedBall x₀ R`
  -- minimizes over `s`.
  have hR : 0 ≤ R := not_lt.1 fun hR ↦ (hfar x₀ hx₀ (by simpa using hR)).false
  have hx₀K : x₀ ∈ s ∩ closedBall x₀ R := ⟨hx₀, mem_closedBall_self hR⟩
  obtain ⟨a, haK, hamin⟩ := (hf_lsc.mono inter_subset_left).exists_isMinOn ⟨x₀, hx₀K⟩
    ((isCompact_closedBall x₀ R).inter_left hs)
  refine ⟨a, haK.1, isMinOn_iff.2 fun y hy ↦ ?_⟩
  by_cases hyR : ‖y - x₀‖ ≤ R
  · exact isMinOn_iff.1 hamin y ⟨hy, mem_closedBall_iff_norm.2 hyR⟩
  · exact (isMinOn_iff.1 hamin x₀ hx₀K).trans (hfar y hy (not_le.1 hyR)).le

/-- **Existence of a minimizer of a strongly convex function plus a linear map.** In finite
dimension, if `f` is `m`-strongly convex for some `m > 0` and lower semicontinuous on a nonempty
closed set `s`, then `f + L` attains its minimum on `s` for every continuous linear map `L`. -/
theorem exists_isMinOn_add_continuousLinearMap [FiniteDimensional ℝ E]
    (hf : StrongConvexOn s m f) (hm : 0 < m) (hs : IsClosed s) (hs_ne : s.Nonempty)
    (hf_lsc : LowerSemicontinuousOn f s) (L : E →L[ℝ] ℝ) :
    ∃ x ∈ s, IsMinOn (f + ⇑L) s x :=
  (hf.add_convexOn (by simpa using L.toLinearMap.convexOn hf.1)).exists_isMinOn hm hs hs_ne
    (hf_lsc.add (L.continuous.lowerSemicontinuous.lowerSemicontinuousOn s))

/-- **Existence and uniqueness of the minimizer of a strongly convex function** [Ora,
Theorem 6.9]. In finite dimension, a function that is `m`-strongly convex for some `m > 0` and
lower semicontinuous on a nonempty closed set `s` has exactly one minimizer on `s`. -/
theorem existsUnique_isMinOn [FiniteDimensional ℝ E] (hf : StrongConvexOn s m f) (hm : 0 < m)
    (hs : IsClosed s) (hs_ne : s.Nonempty) (hf_lsc : LowerSemicontinuousOn f s) :
    ∃! x, x ∈ s ∧ IsMinOn f s x := by
  obtain ⟨x, hx, hxmin⟩ := hf.exists_isMinOn hm hs hs_ne hf_lsc
  exact ⟨x, ⟨hx, hxmin⟩, fun y ⟨hy, hymin⟩ ↦
    (hf.strictConvexOn hm).eq_of_isMinOn hymin hxmin hy hx⟩

end StrongConvexOn

namespace LMLExplore

/-- **Stability of one round.** Let `m > 0` and `η > 0`. If `D` dominates `m / 2 * ‖b - a‖ ^ 2`,
then `y (a - b) - D / η ≤ η / (2 m) * ‖y‖ ^ 2`, where `‖y‖` is the operator norm of the loss, the
dual norm of the norm of `E`. With `D = D_F(b, a)` the Bregman divergence of a potential `F`, this
bounds the stability term of a round of FTRL or mirror descent [LS, Corollary 28.8]; the
modulus `m` may depend on the base point `a`. -/
lemma apply_sub_sub_div_le_of_mul_norm_sq_le {m η D : ℝ} (hm : 0 < m) (hη : 0 < η)
    (y : E →L[ℝ] ℝ) {a b : E} (h : m / 2 * ‖b - a‖ ^ 2 ≤ D) :
    y (a - b) - D / η ≤ η / (2 * m) * ‖y‖ ^ 2 := by
  have h_apply : y (a - b) ≤ ‖b - a‖ * ‖y‖ := by
    rw [norm_sub_rev, mul_comm]
    exact (Real.le_norm_self _).trans (y.le_opNorm _)
  -- `x z - m x² / (2 η) ≤ η z² / (2 m)`, a square completion
  set x := ‖b - a‖
  set z := ‖y‖
  have h_sq : η / (2 * m) * z ^ 2 - (x * z - m / 2 * x ^ 2 / η) =
      (m * x - η * z) ^ 2 / (2 * m * η) := by
    field_simp
    ring
  have h_nonneg : 0 ≤ (m * x - η * z) ^ 2 / (2 * m * η) := by positivity
  have h_div := div_le_div_of_nonneg_right h hη.le
  linarith

/-- The quadratic case of `apply_sub_sub_div_le_of_mul_norm_sq_le`: for `lam > 0` and a
continuous linear functional `g`, `g (a - b) - lam / 2 * ‖a - b‖ ^ 2 ≤ ‖g‖ ^ 2 / (2 lam)`, where
`‖g‖` is the dual norm. -/
lemma apply_sub_sub_mul_norm_sq_le {lam : ℝ} (hlam : 0 < lam) (g : E →L[ℝ] ℝ) (a b : E) :
    g (a - b) - lam / 2 * ‖a - b‖ ^ 2 ≤ ‖g‖ ^ 2 / (2 * lam) := by
  have h := apply_sub_sub_div_le_of_mul_norm_sq_le hlam one_pos g
    (le_of_eq (by rw [norm_sub_rev]) : lam / 2 * ‖b - a‖ ^ 2 ≤ lam / 2 * ‖a - b‖ ^ 2)
  rwa [div_one, one_div_mul_eq_div] at h

end LMLExplore
