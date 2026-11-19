/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Basic
public import LMLExplore.Analysis.Convex.SpecificFunctions.Pow
public import LMLExplore.Analysis.Convex.Strong
public import LMLExplore.Analysis.Convex.VectorSpan
public import LMLExplore.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Exp-concave functions

A real function `f` on a real vector space is **`α`-exp-concave** on a convex set `V` if
`x ↦ exp (-(α * f x))` is concave on `V` [Ora, Definition 7.31]. Exp-concavity is the curvature
condition that gives logarithmic regret without strong convexity: the losses of portfolio
selection `x ↦ -log ⟨w, x⟩` are `1`-exp-concave but not strongly convex, and exp-concave losses
are mixable with the mean as substitution, which is what the Online Newton Step, the Weighted
Average Algorithm and the Aggregating Algorithm use.

This file develops the calculus of exp-concave functions [Ora, Section 7.10.1]:

* an `α`-exp-concave function is `β`-exp-concave for `0 ≤ β ≤ α`, because
  `exp (-(β * f)) = exp (-(α * f)) ^ (β / α)` and `x ↦ x ^ (β / α)` is concave and nondecreasing
  on `[0, ∞)`;
* exp-concavity is preserved by affine changes of variables and by adding constants;
* scaling: `c * f` is `α`-exp-concave if and only if `f` is `α * c`-exp-concave;
* sums: if `f` is `α`-exp-concave and `g` is `β`-exp-concave, with `α, β > 0`, then `f + g` is
  `(α⁻¹ + β⁻¹)⁻¹`-exp-concave, because `exp (-(γ * (f + g)))` is the weighted geometric mean
  `exp (-(α * f)) ^ (γ / α) * exp (-(β * g)) ^ (γ / β)` of two concave functions. Hence a
  nonnegative combination `∑ i, c i * f i` of `α`-exp-concave functions is
  `α / ∑ i, c i`-exp-concave; a convex combination of functions that are exp-concave for
  rates at least `α` is `α`-exp-concave. The rate of a plain sum degrades: `-log` is
  `1`-exp-concave on `(0, ∞)`, but `-2 log` is only `1 / 2`-exp-concave there;
* exp-concave functions are convex (for `α > 0`), by the AM-GM inequality [Ora, Proposition 7.34].

The **Hessian criterion** [Ora, Theorem 7.35] characterizes exp-concavity of twice differentiable
functions: for `α > 0` and `f` with derivatives `f'` and `f''` within `V`, `f` is `α`-exp-concave
on `V` if and only if `α * f' x v ^ 2 ≤ f'' x v v` for every `x ∈ V` and every `v` in the
direction of the affine span of `V`. [Ora] states the condition for all `v`, which is stronger
than exp-concavity when `V` has empty interior: on a segment of `ℝ²`, the curvature in the
directions transverse to the segment is irrelevant. The derivatives are taken within `V`, so no
open set around `V` is needed.

The examples [Ora, Example 7.36, Remark 7.40]: `x ↦ -log (h x)` is `1`-exp-concave for
every positive concave `h`, in particular for `h = w` a linear form on `{x | 0 < w x}`; and the
squared distance `x ↦ ‖x - y‖ ^ 2` in a real inner product space is `α`-exp-concave on every
convex set on which `2 * α * ‖x - y‖ ^ 2 ≤ 1`, so `(8 * R ^ 2)⁻¹`-exp-concave on a closed ball of
radius `R` containing `y`.

Finally, an exp-concave function lies above a quadratic in the direction of its subgradients
[Ora, Example 7.39]: if `f` is `γ`-exp-concave on `V`, `g` is a subgradient of `f` within `V` at
`x`, and `γ * |g (y - x)| ≤ 1`, then `f x + g (y - x) + γ / 4 * g (y - x) ^ 2 ≤ f y`. This is the
curvature that the Online Newton Step exploits, with `γ = min α B⁻¹` when `|g (y - x)| ≤ B`.

## Main definitions

* `LMLExplore.ExpConcaveOn V α f`: `f` is `α`-exp-concave on `V`.

## Main statements

* `LMLExplore.ExpConcaveOn.mono`: [Ora, Proposition 7.32] exp-concavity for smaller rates.
* `LMLExplore.ExpConcaveOn.comp_affineMap`: [Ora, Proposition 7.33] affine changes of variables.
* `LMLExplore.ExpConcaveOn.add`, `LMLExplore.ExpConcaveOn.fun_sum`,
  `LMLExplore.ExpConcaveOn.fun_sum_mul`: sums and nonnegative combinations.
* `LMLExplore.ExpConcaveOn.convexOn`: [Ora, Proposition 7.34] exp-concave functions are convex.
* `LMLExplore.expConcaveOn_of_hasFDerivWithinAt2_mul_apply_sq_le`,
  `LMLExplore.ExpConcaveOn.mul_apply_sq_le_of_hasFDerivWithinAt2`,
  `LMLExplore.expConcaveOn_iff_forall_mul_apply_sq_le`: [Ora, Theorem 7.35] the Hessian criterion.
* `ConcaveOn.expConcaveOn_neg_log`, `LMLExplore.expConcaveOn_neg_log_apply`: logarithmic losses.
* `LMLExplore.expConcaveOn_norm_sub_sq`, `LMLExplore.expConcaveOn_closedBall_norm_sub_sq`:
  [Ora, Example 7.36] the bounded squared loss.
* `LMLExplore.ExpConcaveOn.add_apply_add_mul_sq_le_of_hasSubgradientWithinAt`,
  `LMLExplore.ExpConcaveOn.add_apply_add_min_mul_sq_le_of_hasSubgradientWithinAt`:
  [Ora, Example 7.39] the quadratic lower bound.

## References

* [Ora] F. Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*,
  arXiv:1912.13213v10, Section 7.10.1.
-/

public section

open Real Set Filter
open scoped Topology Bregman

namespace LMLExplore

section Module

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {V W : Set E} {α β c : ℝ} {f g : E → ℝ}

/-- A function `f` is **`α`-exp-concave** on `V` [Ora, Definition 7.31] if
`x ↦ exp (-(α * f x))` is concave on `V`. In particular `V` is convex. -/
def ExpConcaveOn (V : Set E) (α : ℝ) (f : E → ℝ) : Prop :=
  ConcaveOn ℝ V fun x ↦ exp (-(α * f x))

/-- The definition of exp-concavity. -/
theorem expConcaveOn_iff : ExpConcaveOn V α f ↔ ConcaveOn ℝ V fun x ↦ exp (-(α * f x)) :=
  Iff.rfl

/-- Every function is `0`-exp-concave on a convex set. -/
theorem expConcaveOn_zero (hV : Convex ℝ V) : ExpConcaveOn V 0 f := by
  simpa [expConcaveOn_iff] using concaveOn_const (1 : ℝ) hV

/-- **Scaling**: `c * f` is `α`-exp-concave if and only if `f` is `α * c`-exp-concave. -/
@[simp]
theorem expConcaveOn_const_mul_iff :
    ExpConcaveOn V α (fun x ↦ c * f x) ↔ ExpConcaveOn V (α * c) f := by
  simp only [expConcaveOn_iff, mul_assoc]

namespace ExpConcaveOn

/-- An exp-concave function is exp-concave on a convex set. -/
theorem convex (hf : ExpConcaveOn V α f) : Convex ℝ V :=
  (expConcaveOn_iff.1 hf).1

/-- Exp-concavity on a set gives exp-concavity on its convex subsets. -/
theorem subset (hf : ExpConcaveOn V α f) (hWV : W ⊆ V) (hW : Convex ℝ W) :
    ExpConcaveOn W α f :=
  (expConcaveOn_iff.1 hf).subset hWV hW

/-- Exp-concavity only depends on the values of the function on the set. -/
theorem congr (hf : ExpConcaveOn V α f) (hfg : EqOn f g V) : ExpConcaveOn V α g :=
  (expConcaveOn_iff.1 hf).congr fun x hx ↦ by simp only [hfg hx]

/-- **Exp-concavity for smaller rates** [Ora, Proposition 7.32]: an `α`-exp-concave function is
`β`-exp-concave for every `0 ≤ β ≤ α`. -/
theorem mono (hf : ExpConcaveOn V α f) (hβ : 0 ≤ β) (hβα : β ≤ α) : ExpConcaveOn V β f := by
  rcases hβ.eq_or_lt with rfl | hβ
  · exact expConcaveOn_zero hf.convex
  have hα : 0 < α := hβ.trans_le hβα
  -- `exp (-(β * f)) = exp (-(α * f)) ^ (β / α)`
  refine ((expConcaveOn_iff.1 hf).rpow (fun x _ ↦ (exp_pos _).le) (div_nonneg hβ.le hα.le)
    ((div_le_one hα).2 hβα)).congr fun x _ ↦ ?_
  simp only [← exp_mul]
  congr 1
  field_simp

/-- **Affine changes of variables** [Ora, Proposition 7.33]: if `f` is `α`-exp-concave on `V`,
then `f ∘ A` is `α`-exp-concave on `A ⁻¹' V` for every affine map `A`. -/
theorem comp_affineMap (hf : ExpConcaveOn V α f) (A : F →ᵃ[ℝ] E) :
    ExpConcaveOn (A ⁻¹' V) α (f ∘ A) :=
  (expConcaveOn_iff.1 hf).comp_affineMap A

/-- Adding a constant preserves exp-concavity. -/
theorem add_const (hf : ExpConcaveOn V α f) (c : ℝ) : ExpConcaveOn V α fun x ↦ f x + c := by
  refine ((expConcaveOn_iff.1 hf).smul (exp_pos (-(α * c))).le).congr fun x _ ↦ ?_
  simp only [smul_eq_mul, ← exp_add]
  ring_nf

/-- **Sums of exp-concave functions**: if `f` is `α`-exp-concave and `g` is `β`-exp-concave on
`V`, with `α, β > 0`, then `x ↦ f x + g x` is `(α⁻¹ + β⁻¹)⁻¹`-exp-concave on `V`. The rate is not
`min α β` in general: `-log` is `1`-exp-concave on `(0, ∞)`, but `-2 log` is only
`1 / 2`-exp-concave there. -/
theorem add (hf : ExpConcaveOn V α f) (hg : ExpConcaveOn V β g) (hα : 0 < α) (hβ : 0 < β) :
    ExpConcaveOn V (α⁻¹ + β⁻¹)⁻¹ fun x ↦ f x + g x := by
  set γ := (α⁻¹ + β⁻¹)⁻¹ with hγ
  have hγ0 : 0 < γ := by positivity
  have hpq : γ / α + γ / β = 1 := by
    rw [hγ]
    field_simp
  -- `exp (-(γ * (f + g)))` is the weighted geometric mean of `exp (-(α * f))` and
  -- `exp (-(β * g))` with the weights `γ / α` and `γ / β`
  refine ((expConcaveOn_iff.1 hf).rpow_mul_rpow (expConcaveOn_iff.1 hg)
    (fun x _ ↦ (exp_pos _).le) (fun x _ ↦ (exp_pos _).le) (by positivity) (by positivity)
    hpq).congr fun x _ ↦ ?_
  simp only [← exp_mul, ← exp_add]
  congr 1
  field_simp
  ring

/-- **Finite sums of exp-concave functions**: if each `f i` is `α i`-exp-concave on a convex set
`V`, with `α i > 0`, then `∑ i ∈ s, f i` is `(∑ i ∈ s, (α i)⁻¹)⁻¹`-exp-concave on `V`. The empty
sum is `0`-exp-concave. -/
theorem fun_sum {ι : Type*} {s : Finset ι} {α : ι → ℝ} {f : ι → E → ℝ} (hV : Convex ℝ V)
    (hf : ∀ i ∈ s, ExpConcaveOn V (α i) (f i)) (hα : ∀ i ∈ s, 0 < α i) :
    ExpConcaveOn V (∑ i ∈ s, (α i)⁻¹)⁻¹ fun x ↦ ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using expConcaveOn_zero hV
  | insert i s hi ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hf hα
    simp only [Finset.sum_insert hi]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using hf.1
    have hpos : 0 < (∑ j ∈ s, (α j)⁻¹)⁻¹ :=
      inv_pos.2 (Finset.sum_pos (fun j hj ↦ inv_pos.2 (hα.2 j hj)) hs)
    simpa only [inv_inv] using hf.1.add (ih hf.2 hα.2) hα.1 hpos

/-- **Nonnegative combinations of exp-concave functions**: if each `f i` is `α`-exp-concave on a
convex set `V`, with `α ≥ 0`, and `c i ≥ 0`, then `∑ i ∈ s, c i * f i` is
`α / ∑ i ∈ s, c i`-exp-concave on `V`. In particular a convex combination is `α`-exp-concave. -/
theorem fun_sum_mul {ι : Type*} {s : Finset ι} {c : ι → ℝ} {f : ι → E → ℝ} (hV : Convex ℝ V)
    (hf : ∀ i ∈ s, ExpConcaveOn V α (f i)) (hα : 0 ≤ α) (hc : ∀ i ∈ s, 0 ≤ c i) :
    ExpConcaveOn V (α / ∑ i ∈ s, c i) fun x ↦ ∑ i ∈ s, c i * f i x := by
  classical
  rcases hα.eq_or_lt with rfl | hα
  · simpa using expConcaveOn_zero hV
  -- the terms with `c i = 0` vanish; the others are `α / c i`-exp-concave
  set t := s.filter fun i ↦ c i ≠ 0
  have ht : ∀ i ∈ t, 0 < c i := fun i hi ↦
    (hc i (Finset.mem_filter.1 hi).1).lt_of_ne' (Finset.mem_filter.1 hi).2
  have h := fun_sum (s := t) (α := fun i ↦ α / c i) (f := fun i x ↦ c i * f i x) hV
    (fun i hi ↦ expConcaveOn_const_mul_iff.2 (by
      rw [div_mul_cancel₀ α (ht i hi).ne']
      exact hf i (Finset.mem_filter.1 hi).1))
    (fun i hi ↦ div_pos hα (ht i hi))
  have hfun : (fun x ↦ ∑ i ∈ s, c i * f i x) = fun x ↦ ∑ i ∈ t, c i * f i x :=
    funext fun x ↦ (Finset.sum_filter_of_ne fun i _ h ↦ left_ne_zero_of_mul h).symm
  simp only [inv_div] at h
  rwa [← Finset.sum_div, inv_div, Finset.sum_filter_ne_zero, ← hfun] at h

/-- **Exp-concave functions are convex** [Ora, Proposition 7.34]: for `α > 0`, an
`α`-exp-concave function on `V` is convex on `V`. -/
theorem convexOn (hf : ExpConcaveOn V α f) (hα : 0 < α) : ConvexOn ℝ V f := by
  refine ⟨hf.convex, fun x hx y hy a b ha hb hab ↦ ?_⟩
  have h := (expConcaveOn_iff.1 hf).2 hx hy ha hb hab
  -- the AM-GM inequality bounds the weighted geometric mean of the two values of `exp (-(α * f))`
  have hgm := geom_mean_le_arith_mean2_weighted ha hb (exp_pos (-(α * f x))).le
    (exp_pos (-(α * f y))).le hab
  simp only [smul_eq_mul] at h
  rw [← exp_mul, ← exp_mul, ← exp_add] at hgm
  have := exp_le_exp.1 (hgm.trans h)
  simp only [smul_eq_mul]
  nlinarith

end ExpConcaveOn

/-- A function is `0`-exp-concave on `V` if and only if `V` is convex. -/
@[simp]
theorem expConcaveOn_zero_iff : ExpConcaveOn V 0 f ↔ Convex ℝ V :=
  ⟨ExpConcaveOn.convex, expConcaveOn_zero⟩

/-- **Logarithmic losses** [Ora, Remark 7.40]: for a positive concave function `h` on `V`,
`x ↦ -log (h x)` is `1`-exp-concave on `V`. -/
theorem _root_.ConcaveOn.expConcaveOn_neg_log {h : E → ℝ} (hh : ConcaveOn ℝ V h)
    (hpos : ∀ x ∈ V, 0 < h x) : ExpConcaveOn V 1 fun x ↦ -log (h x) :=
  hh.congr fun x hx ↦ by simp [exp_log (hpos x hx)]

/-- **The logarithmic loss of a linear form**: `x ↦ -log (w x)` is `1`-exp-concave on
`{x | 0 < w x}`. These are the losses of portfolio selection, with `w` the market vector. -/
theorem expConcaveOn_neg_log_apply (w : E →ₗ[ℝ] ℝ) :
    ExpConcaveOn {x | 0 < w x} 1 fun x ↦ -log (w x) :=
  (w.concaveOn (convex_halfSpace_gt w.isLinear 0)).expConcaveOn_neg_log fun _ hx ↦ hx

end Module

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Set E} {α γ B : ℝ}
  {f : E → ℝ} {g : E →L[ℝ] ℝ} {x y : E}

namespace ExpConcaveOn

/-- **The quadratic lower bound of exp-concave functions** [Ora, Example 7.39]. Let `f` be
`γ`-exp-concave on `V` and let `g` be a subgradient of `f` within `V` at `x ∈ V`. For `y ∈ V` with
`γ * |g (y - x)| ≤ 1`, `f x + g (y - x) + γ / 4 * g (y - x) ^ 2 ≤ f y`. -/
theorem add_apply_add_mul_sq_le_of_hasSubgradientWithinAt (hf : ExpConcaveOn V γ f)
    (hx : x ∈ V) (hg : HasSubgradientWithinAt f g V x) (hy : y ∈ V) (hgy : γ * |g (y - x)| ≤ 1) :
    f x + g (y - x) + γ / 4 * g (y - x) ^ 2 ≤ f y := by
  have hsub := hg y hy
  simp only [bregDiv] at hsub
  -- for `γ ≤ 0` the quadratic term is nonpositive, so the subgradient inequality suffices
  rcases le_or_gt γ 0 with hγ | hγ
  · nlinarith [sq_nonneg (g (y - x))]
  set c := g (y - x)
  set h : E → ℝ := fun z ↦ exp (-(γ * f z)) with hh
  -- Step 1: `h y ≤ h x * (1 - γ * c)`. Along the segment `z t = x + t • (y - x)`, concavity gives
  -- `(1 - t) * h x + t * h y ≤ h (z t)`, and the subgradient inequality
  -- `f x + t * c ≤ f (z t)` gives `h (z t) ≤ h x * exp (-(γ * c * t))`. Divide by `t` and let
  -- `t → 0⁺`.
  have hstep : ∀ t ∈ Ioo (0 : ℝ) 1, h y ≤ h x * (1 + t⁻¹ * (exp (-(γ * c) * t) - 1)) := by
    intro t ht
    have hz : x + t • (y - x) ∈ V := hf.convex.add_smul_sub_mem hx hy (Ioo_subset_Icc_self ht)
    have hcomb : (1 - t) • x + t • y = x + t • (y - x) := by module
    have hconc := (expConcaveOn_iff.1 hf).2 hx hy (sub_nonneg.2 ht.2.le) ht.1.le (by ring)
    rw [hcomb, smul_eq_mul, smul_eq_mul] at hconc
    have hsubt := hg _ hz
    simp only [bregDiv, add_sub_cancel_left, map_smul, smul_eq_mul] at hsubt
    have hhz : h (x + t • (y - x)) ≤ h x * exp (-(γ * c) * t) := by
      simp only [hh, ← exp_add]
      exact exp_le_exp.2 (by nlinarith)
    have hhx : 0 < h x := exp_pos _
    -- multiply by `t` to clear `t⁻¹`
    refine le_of_mul_le_mul_left ?_ ht.1
    have hexp : t * (h x * (1 + t⁻¹ * (exp (-(γ * c) * t) - 1))) =
        t * h x + h x * (exp (-(γ * c) * t) - 1) := by
      field_simp [ht.1.ne']
    rw [hexp]
    nlinarith
  have hlim : Tendsto (fun t : ℝ ↦ h x * (1 + t⁻¹ * (exp (-(γ * c) * t) - 1))) (𝓝[>] 0)
      (𝓝 (h x * (1 + -(γ * c)))) := by
    have hd : HasDerivAt (fun t : ℝ ↦ exp (-(γ * c) * t)) (-(γ * c)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (-(γ * c))).exp
    have := hd.tendsto_slope_zero_right
    simp only [zero_add, mul_zero, exp_zero, smul_eq_mul] at this
    exact (this.const_add 1).const_mul (h x)
  have h1 : h y ≤ h x * (1 + -(γ * c)) := ge_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht using hstep t ht)
  -- Step 2: take logarithms, with `log (1 + u) ≤ u - u ^ 2 / 4` for `u = -(γ * c) ∈ (-1, 1]`.
  have hu : 0 < 1 + -(γ * c) := pos_of_mul_pos_right ((exp_pos _).trans_le h1) (exp_pos _).le
  have hu₁ : -(γ * c) ≤ 1 := by
    have := neg_abs_le c
    nlinarith
  have hlog := Real.log_le_log (exp_pos _) h1
  rw [Real.log_mul (exp_pos _).ne' hu.ne', Real.log_exp, Real.log_exp] at hlog
  have hq := Real.log_one_add_le_sub_sq_div_four (by linarith) hu₁
  have key : γ * (f x + c + γ / 4 * c ^ 2) ≤ γ * f y := by nlinarith
  exact le_of_mul_le_mul_left key hγ

/-- **The quadratic lower bound of exp-concave functions** in the form of [Ora, Example 7.39].
Let `f` be `α`-exp-concave on `V` and let `g` be a subgradient of `f` within `V` at `x ∈ V`. For
`y ∈ V` with `|g (y - x)| ≤ B`, `f y ≥ f x + g (y - x) + β / 2 * g (y - x) ^ 2` with
`β = min α B⁻¹ / 2`. -/
theorem add_apply_add_min_mul_sq_le_of_hasSubgradientWithinAt (hf : ExpConcaveOn V α f)
    (hx : x ∈ V) (hg : HasSubgradientWithinAt f g V x) (hy : y ∈ V) (hgB : |g (y - x)| ≤ B) :
    f x + g (y - x) + min α B⁻¹ / 4 * g (y - x) ^ 2 ≤ f y := by
  have hB : 0 ≤ B := (abs_nonneg _).trans hgB
  rcases le_or_gt (min α B⁻¹) 0 with hmin | hmin
  · -- the quadratic term is nonpositive, so the subgradient inequality suffices
    have hsub := hg y hy
    simp only [bregDiv] at hsub
    nlinarith [sq_nonneg (g (y - x))]
  refine (hf.mono hmin.le (min_le_left _ _)).add_apply_add_mul_sq_le_of_hasSubgradientWithinAt
    hx hg hy ?_
  calc min α B⁻¹ * |g (y - x)| ≤ B⁻¹ * |g (y - x)| := by gcongr; exact min_le_right _ _
    _ ≤ 1 := by
      rcases hB.eq_or_lt with rfl | hB
      · simp
      · exact inv_mul_le_one_of_le₀ hgB hB.le

end ExpConcaveOn

section Hessian

variable {f' : E → E →L[ℝ] ℝ} {f'' : E → E →L[ℝ] E →L[ℝ] ℝ}

/-- The derivative of `z ↦ -exp (-(α * f z))`. -/
private lemma hasFDerivWithinAt_neg_exp_neg_mul {z : E} (hf : HasFDerivWithinAt f (f' z) V z) :
    HasFDerivWithinAt (fun z ↦ -exp (-(α * f z))) ((α * exp (-(α * f z))) • f' z) V z := by
  convert (hf.const_mul α).neg.exp.neg using 1
  ext v
  simp only [smul_apply, neg_apply, smul_eq_mul, Pi.neg_apply]
  ring

/-- The second derivative of `z ↦ -exp (-(α * f z))`, as a quadratic form. -/
private lemma exists_hasFDerivWithinAt_neg_exp_neg_mul
    (hf : ∀ z ∈ V, HasFDerivWithinAt f (f' z) V z) (hf' : HasFDerivWithinAt f' (f'' x) V x)
    (hx : x ∈ V) :
    ∃ D : E →L[ℝ] E →L[ℝ] ℝ,
      HasFDerivWithinAt (fun z ↦ (α * exp (-(α * f z))) • f' z) D V x ∧
        ∀ v, D v v = exp (-(α * f x)) * (α * f'' x v v - α ^ 2 * f' x v ^ 2) := by
  refine ⟨_, ((((hf x hx).const_mul α).neg.exp).const_mul α).smul hf', fun v ↦ ?_⟩
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, neg_apply, smul_eq_mul,
    Pi.neg_apply]
  ring

/-- **The Hessian criterion for exp-concavity**, sufficiency [Ora, Theorem 7.35]. Let `f` have
derivative `f' z` and `f'` have derivative `f'' z` within a convex set `V`, at every `z ∈ V`, and
let `α ≥ 0`. If `α * f' z (y - x) ^ 2 ≤ f'' z (y - x) (y - x)` for `x, y ∈ V` and every `z` of the
segment `[x, y]`, then `f` is `α`-exp-concave on `V`. -/
theorem expConcaveOn_of_hasFDerivWithinAt2_mul_apply_sq_le (hV : Convex ℝ V)
    (hf : ∀ z ∈ V, HasFDerivWithinAt f (f' z) V z)
    (hf' : ∀ z ∈ V, HasFDerivWithinAt f' (f'' z) V z) (hα : 0 ≤ α)
    (h : ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ segment ℝ x y, α * f' z (y - x) ^ 2 ≤ f'' z (y - x) (y - x)) :
    ExpConcaveOn V α f := by
  choose! D hD hDv using fun z (hz : z ∈ V) ↦
    exists_hasFDerivWithinAt_neg_exp_neg_mul (α := α) hf (hf' z hz) hz
  -- `-exp (-(α * f))` is convex, by the second-order criterion
  have hconv : ConvexOn ℝ V fun z ↦ -exp (-(α * f z)) := by
    refine strongConvexOn_zero.1 (hV.strongConvexOn_of_hasFDerivWithinAt2_mul_norm_sub_sq_le
      (fun z hz ↦ hasFDerivWithinAt_neg_exp_neg_mul (hf z hz)) hD fun x hx y hy z hz ↦ ?_)
    rw [hDv z (hV.segment_subset hx hy hz), zero_mul]
    have := h x hx y hy z hz
    have he := exp_pos (-(α * f z))
    nlinarith [mul_nonneg he.le (mul_nonneg hα (sub_nonneg.2 this))]
  exact expConcaveOn_iff.2 (neg_convexOn_iff.1 hconv)

/-- **The Hessian condition of exp-concave functions**, necessity [Ora, Theorem 7.35]. Let `f` be
`α`-exp-concave on `V` with `α > 0`, with derivative `f' z` within `V` at every `z ∈ V`, and let
`f'` have derivative `f'' x` within `V` at `x ∈ V`. Then `α * f' x v ^ 2 ≤ f'' x v v` for every
`v` in the direction of the affine span of `V`. -/
theorem ExpConcaveOn.mul_apply_sq_le_of_hasFDerivWithinAt2 (hfα : ExpConcaveOn V α f)
    (hα : 0 < α) (hf : ∀ z ∈ V, HasFDerivWithinAt f (f' z) V z)
    (hf' : HasFDerivWithinAt f' (f'' x) V x) (hx : x ∈ V) {v : E}
    (hv : v ∈ (affineSpan ℝ V).direction) : α * f' x v ^ 2 ≤ f'' x v v := by
  rw [direction_affineSpan] at hv
  obtain ⟨t, -, a, ha, b, hb, rfl⟩ := hfα.convex.exists_eq_smul_sub_of_mem_vectorSpan ⟨x, hx⟩ hv
  -- the second-order condition of the convex function `-exp (-(α * f))` at `x`
  obtain ⟨D, hD, hDv⟩ := exists_hasFDerivWithinAt_neg_exp_neg_mul (α := α) hf hf' hx
  have hconv : StrongConvexOn V 0 fun z ↦ -exp (-(α * f z)) :=
    strongConvexOn_zero.2 (neg_convexOn_iff.2 (expConcaveOn_iff.1 hfα))
  have h := hconv.mul_norm_sub_sq_le_of_hasFDerivWithinAt2
    (fun z hz ↦ hasFDerivWithinAt_neg_exp_neg_mul (hf z hz)) hD hx ha hb
  rw [zero_mul, hDv] at h
  have he := exp_pos (-(α * f x))
  have hab : α * f' x (a - b) ^ 2 ≤ f'' x (a - b) (a - b) := by
    have : 0 ≤ exp (-(α * f x)) * α * (f'' x (a - b) (a - b) - α * f' x (a - b) ^ 2) := by
      nlinarith
    have := (mul_nonneg_iff_of_pos_left (mul_pos he hα)).1 this
    linarith
  simp only [map_smul, smul_apply, smul_eq_mul]
  nlinarith [sq_nonneg t]

/-- **The Hessian criterion for exp-concavity** [Ora, Theorem 7.35]. Let `f` have derivative
`f' z` and `f'` have derivative `f'' z` within a convex set `V`, at every `z ∈ V`, and let
`α > 0`. Then `f` is `α`-exp-concave on `V` if and only if `α * f' x v ^ 2 ≤ f'' x v v` for every
`x ∈ V` and every `v` in the direction of the affine span of `V`. [Ora] requires the inequality for
all `v`, which is stronger than exp-concavity when `V` has empty interior. -/
theorem expConcaveOn_iff_forall_mul_apply_sq_le (hV : Convex ℝ V)
    (hf : ∀ z ∈ V, HasFDerivWithinAt f (f' z) V z)
    (hf' : ∀ z ∈ V, HasFDerivWithinAt f' (f'' z) V z) (hα : 0 < α) :
    ExpConcaveOn V α f ↔
      ∀ x ∈ V, ∀ v ∈ (affineSpan ℝ V).direction, α * f' x v ^ 2 ≤ f'' x v v := by
  refine ⟨fun h x hx v hv ↦ h.mul_apply_sq_le_of_hasFDerivWithinAt2 hα hf (hf' x hx) hx hv,
    fun h ↦ expConcaveOn_of_hasFDerivWithinAt2_mul_apply_sq_le hV hf hf' hα.le
      fun x hx y hy z hz ↦ ?_⟩
  have hv : y - x ∈ (affineSpan ℝ V).direction := by
    rw [direction_affineSpan, ← vsub_eq_sub]
    exact vsub_mem_vectorSpan ℝ hy hx
  exact h z (hV.segment_subset hx hy hz) _ hv

end Hessian

end Normed

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {V : Set E} {α R : ℝ}
  {c y : E}

/-- **The squared distance is exp-concave on bounded sets** [Ora, Example 7.36]: in a real inner
product space, `x ↦ ‖x - y‖ ^ 2` is `α`-exp-concave on every convex set `V` on which
`2 * α * ‖x - y‖ ^ 2 ≤ 1`, for `α ≥ 0`. -/
theorem expConcaveOn_norm_sub_sq (hV : Convex ℝ V) (hα : 0 ≤ α)
    (h : ∀ x ∈ V, 2 * α * ‖x - y‖ ^ 2 ≤ 1) : ExpConcaveOn V α fun x ↦ ‖x - y‖ ^ 2 := by
  have hd (z : E) : HasFDerivAt (fun x ↦ ‖x - y‖ ^ 2) (((2 : ℝ) • innerSL ℝ) (z - y)) z := by
    convert ((hasFDerivAt_id z).sub_const y).norm_sq using 1 <;> ext <;> simp
  have hd' (z : E) :
      HasFDerivAt (fun x ↦ ((2 : ℝ) • innerSL ℝ) (x - y)) ((2 : ℝ) • innerSL ℝ) z := by
    have := ((2 : ℝ) • innerSL ℝ).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const y)
    rwa [ContinuousLinearMap.comp_id] at this
  -- by the Hessian criterion, the condition is `4 * α * ⟪z - y, v⟫ ^ 2 ≤ 2 * ‖v‖ ^ 2`, which
  -- follows from the Cauchy–Schwarz inequality
  refine expConcaveOn_of_hasFDerivWithinAt2_mul_apply_sq_le hV (fun z _ ↦ (hd z).hasFDerivWithinAt)
    (fun z _ ↦ (hd' z).hasFDerivWithinAt) hα fun x hx x' hx' z hz ↦ ?_
  have hzy := h z (hV.segment_subset hx hx' hz)
  have hcs := real_inner_mul_inner_self_le (z - y) (x' - x)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  nlinarith [mul_le_mul_of_nonneg_left hcs (by positivity : (0 : ℝ) ≤ 4 * α),
    mul_le_mul_of_nonneg_right hzy (by positivity : (0 : ℝ) ≤ 2 * ‖x' - x‖ ^ 2)]

/-- **The bounded squared loss** [Ora, Example 7.36]: for `y` in a closed ball of radius `R` of a
real inner product space, `x ↦ ‖x - y‖ ^ 2` is `(8 * R ^ 2)⁻¹`-exp-concave on that ball. -/
theorem expConcaveOn_closedBall_norm_sub_sq (hy : y ∈ Metric.closedBall c R) :
    ExpConcaveOn (Metric.closedBall c R) (8 * R ^ 2)⁻¹ fun x ↦ ‖x - y‖ ^ 2 := by
  refine expConcaveOn_norm_sub_sq (convex_closedBall c R) (by positivity) fun x hx ↦ ?_
  rw [Metric.mem_closedBall] at hx hy
  have hxy : ‖x - y‖ ≤ 2 * R := by
    rw [← dist_eq_norm]
    linarith [dist_triangle_right x y c]
  calc 2 * (8 * R ^ 2)⁻¹ * ‖x - y‖ ^ 2 ≤ 2 * (8 * R ^ 2)⁻¹ * (2 * R) ^ 2 := by gcongr
    _ = (8 * R ^ 2)⁻¹ * (8 * R ^ 2) := by ring
    _ ≤ 1 := inv_mul_le_one_of_le₀ le_rfl (by positivity)

end InnerProductSpace

end LMLExplore
