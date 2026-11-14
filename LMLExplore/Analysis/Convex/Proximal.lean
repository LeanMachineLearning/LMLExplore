/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.Real.Sign
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Basic
import LMLExplore.Analysis.Convex.Bregman.Euclidean
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Proximal operators and soft thresholding

The *proximal step* of a function `r : E → ℝ` with step `η > 0` from a point `z` of a real
normed space is a minimizer of `x ↦ η * r x + ‖x - z‖ ^ 2 / 2`. It is the resolvent `J_η z` of
Tau Ceti's Moreau–Yosida approximation (`TauCeti.moreauYosidaResolvent`) for the energy `r`, read
in `EReal`. Restricting `r` to a set `V`, by the energy equal to `r` on `V` and to `⊤` outside
(the convention of Tau Ceti's convex analysis), gives the proximal steps within `V`; for `r = 0`
this energy is the indicator of `V`, and its proximal steps are the points of `V` nearest to `z`,
the projections of `z` onto `V`. On a complete convex set of a real inner product space there is
exactly one of them.

On `EuclideanSpace ℝ α`, the proximal step of the `ℓ¹` norm `lam * ∑ a, |x a|` is computed
coordinatewise by *soft thresholding*
`softThreshold c z = sign z * max (|z| - c) 0` at the level `c = η * lam`: it sets to `0` the
coordinates of absolute value at most `c` and moves the others by `c` towards `0` [Ora,
Example 7.24]. Proximal steps are the updates of FTRL with composite losses, in which a fixed
convex part `r` of the losses is kept exact instead of being linearized, and soft thresholding
is the reason why the `ℓ¹` term produces sparse plays.

## Main definitions

* `softThreshold c z`: the soft thresholding of `z : ℝ` at the level `c`.

## Main statements

* `mem_moreauYosidaResolvent_ite_iff`: the resolvent of the restriction of `r` to a nonempty set
  `V` consists of the points of `V` minimizing `η * r x + ‖x - z‖ ^ 2 / 2` over `V`.
* `mem_moreauYosidaResolvent_coe_iff`: the resolvent of a real function `r` consists of the global
  minimizers of `η * r x + ‖x - z‖ ^ 2 / 2`.
* `mem_moreauYosidaResolvent_ite_zero_iff`: the resolvent of the indicator of a nonempty set
  consists of the points of the set nearest to `z`.
* `exists_moreauYosidaResolvent_ite_zero_eq_singleton`: on a nonempty complete convex set of a
  real inner product space, it is a single point, the projection.
* `mul_abs_softThreshold_add_le`: soft thresholding minimizes `c * |x| + (x - z) ^ 2 / 2`, with
  quadratic growth away from it.
* `isMinOn_mul_sum_abs_add_norm_sub_sq_iff`, `moreauYosidaResolvent_mul_sum_abs`: the proximal
  step of the `ℓ¹` norm on `EuclideanSpace ℝ α` is coordinatewise soft thresholding.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Section 7.8, Example 7.24.
-/

public section

open Finset Set
open scoped NNReal ENNReal

namespace LMLExplore

section SeminormedAddCommGroup

variable {E : Type*} [SeminormedAddCommGroup E] {η : ℝ≥0} {r : E → ℝ} {V : Set E}
  [DecidablePred (· ∈ V)] {y z : E}

/-- **The proximal step within a set.** For a step `η > 0`, a real function `r` and a nonempty set
`V`, restrict `r` to `V` by the energy equal to `r` on `V` and to `⊤` outside. Its resolvent `J_η z`
consists of the points `y ∈ V` minimizing `η * r x + ‖x - z‖ ^ 2 / 2` over `V`. -/
theorem mem_moreauYosidaResolvent_ite_iff (hη : 0 < η) (hV : V.Nonempty) :
    y ∈ TauCeti.moreauYosidaResolvent (fun x ↦ if x ∈ V then (r x : EReal) else ⊤) η z ↔
      y ∈ V ∧ IsMinOn (fun x ↦ η * r x + ‖x - z‖ ^ 2 / 2) V y := by
  have hη' : (0 : ℝ) < η := hη
  -- the penalized energy: a real number on `V`, and `⊤` outside
  have h_energy (x : E) : (if x ∈ V then (r x : EReal) else ⊤) +
      ((edist z x ^ 2 / (2 * η) : ℝ≥0∞) : EReal) =
        if x ∈ V then ((r x + ‖x - z‖ ^ 2 / (2 * η) : ℝ) : EReal) else ⊤ := by
    rw [TauCeti.coe_edist_sq_div_eq_coe_dist_sq_div hη, dist_comm, dist_eq_norm]
    split_ifs
    · exact (EReal.coe_add _ _).symm
    · exact EReal.top_add_coe _
  -- on `V`, scaling by `η` turns the penalized energy into the proximal objective
  have h_scale (a b : E) : r a + ‖a - z‖ ^ 2 / (2 * η) ≤ r b + ‖b - z‖ ^ 2 / (2 * η) ↔
      η * r a + ‖a - z‖ ^ 2 / 2 ≤ η * r b + ‖b - z‖ ^ 2 / 2 := by
    have h (c : E) : η * r c + ‖c - z‖ ^ 2 / 2 = η * (r c + ‖c - z‖ ^ 2 / (2 * η)) := by
      field_simp
    rw [h a, h b, mul_le_mul_iff_of_pos_left hη']
  rw [TauCeti.mem_moreauYosidaResolvent_iff_isMinOn, isMinOn_univ_iff, isMinOn_iff]
  simp only [h_energy]
  constructor
  · intro h
    obtain ⟨w, hw⟩ := hV
    -- outside `V` the energy is `⊤`, above its real value at `w ∈ V`
    have hy : y ∈ V := by
      by_contra hy
      simpa [hy, hw] using h w
    refine ⟨hy, fun b hb ↦ (h_scale y b).1 ?_⟩
    have h := h b
    simp only [hy, hb, ↓reduceIte] at h
    exact EReal.coe_le_coe_iff.1 h
  · rintro ⟨hy, hmin⟩ b
    by_cases hb : b ∈ V
    · simp only [hy, hb, ↓reduceIte]
      exact EReal.coe_le_coe_iff.2 ((h_scale y b).2 (hmin b hb))
    · simp [hb]

/-- **The proximal step.** For a step `η > 0` and a real function `r`, the resolvent `J_η z` of `r`
consists of the minimizers of `η * r x + ‖x - z‖ ^ 2 / 2`. -/
theorem mem_moreauYosidaResolvent_coe_iff (hη : 0 < η) :
    y ∈ TauCeti.moreauYosidaResolvent (fun x ↦ (r x : EReal)) η z ↔
      IsMinOn (fun x ↦ η * r x + ‖x - z‖ ^ 2 / 2) univ y := by
  classical
  simpa using mem_moreauYosidaResolvent_ite_iff (r := r) (y := y) (z := z) hη
    (V := univ) ⟨0, mem_univ 0⟩

/-- **The proximal step of an indicator is the projection.** For a step `η > 0` and a nonempty set
`K`, the resolvent `J_η z` of the indicator of `K`, equal to `0` on `K` and to `⊤` outside,
consists of the points of `K` nearest to `z`; it does not depend on `η`. -/
theorem mem_moreauYosidaResolvent_ite_zero_iff {K : Set E} [DecidablePred (· ∈ K)] (hη : 0 < η)
    (hK : K.Nonempty) :
    y ∈ TauCeti.moreauYosidaResolvent (fun x ↦ if x ∈ K then (0 : EReal) else ⊤) η z ↔
      y ∈ K ∧ IsMinOn (fun x ↦ ‖x - z‖) K y := by
  have h := mem_moreauYosidaResolvent_ite_iff (r := fun _ ↦ 0) (y := y) (z := z) hη hK
  simp only [mul_zero, zero_add] at h
  -- the indicator is the restriction to `K` of the real function `0`
  have h0 : (fun x ↦ if x ∈ K then (0 : EReal) else ⊤) =
      fun x ↦ if x ∈ K then (((fun _ ↦ (0 : ℝ)) x : ℝ) : EReal) else ⊤ := by
    simp
  rw [h0, h, isMinOn_iff, isMinOn_iff]
  refine and_congr_right fun _ ↦ forall₂_congr fun b _ ↦ ?_
  rw [div_le_div_iff_of_pos_right two_pos, sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]

end SeminormedAddCommGroup

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {η : ℝ≥0} {K : Set E}
  [DecidablePred (· ∈ K)]

/-- **The projection onto a complete convex set.** In a real inner product space, for a step
`η > 0` and a nonempty complete convex set `K` (for instance a nonempty closed convex set of a
Hilbert space), the resolvent `J_η z` of the indicator of `K` is a single point: the projection
of `z` onto `K`, the point of `K` nearest to `z` (`mem_moreauYosidaResolvent_ite_zero_iff`). -/
theorem exists_moreauYosidaResolvent_ite_zero_eq_singleton (hη : 0 < η) (hK : K.Nonempty)
    (hKc : IsComplete K) (hKconv : Convex ℝ K) (z : E) :
    ∃ p, TauCeti.moreauYosidaResolvent (fun x ↦ if x ∈ K then (0 : EReal) else ⊤) η z = {p} := by
  obtain ⟨p, hpK, hp⟩ := exists_norm_eq_iInf_of_complete_convex hK hKc hKconv z
  have hpmin : IsMinOn (fun x ↦ ‖x - z‖) K p := isMinOn_iff.2 fun w hw ↦ by
    rw [norm_sub_rev, hp, norm_sub_rev]
    exact ciInf_le ⟨0, forall_mem_range.2 fun _ ↦ norm_nonneg _⟩ (⟨w, hw⟩ : K)
  -- the nearest points minimize the strictly convex function `‖· - z‖ ^ 2 / 2` on `K`
  have h_sq {q : E} (hq : IsMinOn (fun x ↦ ‖x - z‖) K q) :
      IsMinOn (fun x ↦ 1 / 2 * ‖x - z‖ ^ 2) K q := isMinOn_iff.2 fun w hw ↦ by
    have := isMinOn_iff.1 hq w hw
    gcongr
  refine ⟨p, Set.ext fun y ↦ ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩⟩
  · obtain ⟨hyK, hymin⟩ := (mem_moreauYosidaResolvent_ite_zero_iff hη hK).1 hy
    exact ((strongConvexOn_div_two_mul_norm_sub_sq hKconv 1 z).strictConvexOn one_pos).eq_of_isMinOn
      (h_sq hymin) (h_sq hpmin) hyK hpK
  · rw [mem_singleton_iff.1 hy]
    exact (mem_moreauYosidaResolvent_ite_zero_iff hη hK).2 ⟨hpK, hpmin⟩

end InnerProductSpace

section SoftThreshold

variable {c z : ℝ}

/-- The **soft thresholding** of `z : ℝ` at the level `c`: `sign z * max (|z| - c) 0`. For
`c ≥ 0` it is `0` when `|z| ≤ c`, and it is `z` moved by `c` towards `0` otherwise. It is the
proximal step of `c * |·|` (`mul_abs_softThreshold_add_le`). -/
noncomputable def softThreshold (c z : ℝ) : ℝ :=
  Real.sign z * max (|z| - c) 0

/-- The defining formula of soft thresholding. -/
theorem softThreshold_def (c z : ℝ) : softThreshold c z = Real.sign z * max (|z| - c) 0 :=
  (rfl)

/-- Soft thresholding vanishes on the points of absolute value at most the level. -/
@[simp]
theorem softThreshold_of_abs_le (h : |z| ≤ c) : softThreshold c z = 0 := by
  rw [softThreshold_def, max_eq_right (sub_nonpos.2 h), mul_zero]

/-- Soft thresholding at any level sends `0` to `0`. -/
@[simp]
theorem softThreshold_zero_right (c : ℝ) : softThreshold c 0 = 0 := by
  rw [softThreshold_def, Real.sign_zero, zero_mul]

/-- Above a nonnegative level `c`, soft thresholding subtracts `c`. -/
theorem softThreshold_of_lt (hc : 0 ≤ c) (h : c < z) : softThreshold c z = z - c := by
  have hz : 0 < z := hc.trans_lt h
  rw [softThreshold_def, Real.sign_of_pos hz, abs_of_pos hz, max_eq_left (by linarith), one_mul]

/-- Below `-c`, for a nonnegative level `c`, soft thresholding adds `c`. -/
theorem softThreshold_of_lt_neg (hc : 0 ≤ c) (h : z < -c) : softThreshold c z = z + c := by
  have hz : z < 0 := h.trans_le (neg_nonpos.2 hc)
  rw [softThreshold_def, Real.sign_of_neg hz, abs_of_neg hz, max_eq_left (by linarith)]
  ring

/-- Soft thresholding is odd. -/
@[simp]
theorem softThreshold_neg (c z : ℝ) : softThreshold c (-z) = -softThreshold c z := by
  rw [softThreshold_def, softThreshold_def, Real.sign_neg, abs_neg, neg_mul]

/-- Soft thresholding is positively homogeneous in the level and the point together. -/
theorem softThreshold_mul {η : ℝ} (hη : 0 ≤ η) (c z : ℝ) :
    softThreshold (η * c) (η * z) = η * softThreshold c z := by
  rcases hη.eq_or_lt with rfl | hη
  · rw [zero_mul, zero_mul, zero_mul, softThreshold_zero_right]
  have hmax : max (η * (|z| - c)) 0 = η * max (|z| - c) 0 := by
    rw [mul_max_of_nonneg _ _ hη.le, mul_zero]
  rw [softThreshold_def, softThreshold_def, abs_mul, abs_of_pos hη, ← mul_sub, hmax]
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hη hz), Real.sign_of_neg hz]
    ring
  · simp [Real.sign_zero]
  · rw [Real.sign_of_pos (mul_pos hη hz), Real.sign_of_pos hz]
    ring

/-- **Soft thresholding is the proximal step of `c * |·|`** [Ora, Example 7.24]. For a level
`c ≥ 0`, the point `s = softThreshold c z` minimizes `x ↦ c * |x| + (x - z) ^ 2 / 2`, with
quadratic growth: `c * |s| + (s - z) ^ 2 / 2 + (x - s) ^ 2 / 2 ≤ c * |x| + (x - z) ^ 2 / 2` for
every `x`. -/
theorem mul_abs_softThreshold_add_le (hc : 0 ≤ c) (z x : ℝ) :
    c * |softThreshold c z| + (softThreshold c z - z) ^ 2 / 2 + (x - softThreshold c z) ^ 2 / 2 ≤
      c * |x| + (x - z) ^ 2 / 2 := by
  -- in each case, the inequality reduces to `z - s ∈ c * ∂|·|(s)`, tested against `x`
  rcases le_or_gt |z| c with h | h
  · rw [softThreshold_of_abs_le h]
    have hxz : x * z ≤ |x| * c :=
      (le_abs_self _).trans ((abs_mul x z).trans_le (mul_le_mul_of_nonneg_left h (abs_nonneg x)))
    simp only [abs_zero, mul_zero, zero_add]
    nlinarith
  rcases lt_abs.1 h with h | h
  · rw [softThreshold_of_lt hc h, abs_of_pos (by linarith)]
    nlinarith [le_abs_self x]
  · rw [softThreshold_of_lt_neg hc (by linarith), abs_of_neg (by linarith)]
    nlinarith [neg_abs_le x]

end SoftThreshold

section Euclidean

variable {α : Type*} [Fintype α] {c : ℝ}

/-- **The proximal objective of the `ℓ¹` norm, in coordinates.** For a level `c ≥ 0` and a point
`z` of `EuclideanSpace ℝ α`, its coordinatewise soft thresholding `s` satisfies
`c * ∑ a, |s a| + ‖s - z‖ ^ 2 / 2 + ‖x - s‖ ^ 2 / 2 ≤ c * ∑ a, |x a| + ‖x - z‖ ^ 2 / 2` for every
`x`. -/
theorem mul_sum_abs_softThreshold_add_le (hc : 0 ≤ c) (z x : EuclideanSpace ℝ α) :
    c * ∑ a, |softThreshold c (z a)| +
        ‖WithLp.toLp 2 (fun a ↦ softThreshold c (z a)) - z‖ ^ 2 / 2 +
        ‖x - WithLp.toLp 2 (fun a ↦ softThreshold c (z a))‖ ^ 2 / 2 ≤
      c * ∑ a, |x a| + ‖x - z‖ ^ 2 / 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply, mul_sum, sum_div,
    ← sum_add_distrib]
  exact sum_le_sum fun a _ ↦ mul_abs_softThreshold_add_le hc (z a) (x a)

/-- **The proximal step of the `ℓ¹` norm is soft thresholding** [Ora, Example 7.24]. For a level
`c ≥ 0` and a point `z` of `EuclideanSpace ℝ α`, the function
`x ↦ c * ∑ a, |x a| + ‖x - z‖ ^ 2 / 2` has exactly one minimizer, the coordinatewise soft
thresholding of `z` at the level `c`. -/
theorem isMinOn_mul_sum_abs_add_norm_sub_sq_iff (hc : 0 ≤ c) (z y : EuclideanSpace ℝ α) :
    IsMinOn (fun x ↦ c * ∑ a, |x a| + ‖x - z‖ ^ 2 / 2) univ y ↔
      y = WithLp.toLp 2 (fun a ↦ softThreshold c (z a)) := by
  set s := WithLp.toLp 2 (fun a ↦ softThreshold c (z a)) with hs
  have hgrowth := mul_sum_abs_softThreshold_add_le hc z
  rw [← hs] at hgrowth
  refine ⟨fun hy ↦ ?_, fun hy ↦ hy ▸ isMinOn_univ_iff.2 fun x ↦ ?_⟩
  · -- `y` does at least as well as `s`, which beats `y` by `‖y - s‖ ^ 2 / 2`
    have h := isMinOn_univ_iff.1 hy s
    have h' := hgrowth y
    have h0 : ‖y - s‖ ^ 2 ≤ 0 := by
      simp only [s] at h h' ⊢
      linarith
    exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1
      (le_antisymm h0 (sq_nonneg _))))
  · have h := hgrowth x
    simp only [s] at h ⊢
    linarith [sq_nonneg ‖x - WithLp.toLp 2 (fun a ↦ softThreshold c (z a))‖]

/-- **The resolvent of the `ℓ¹` norm** [Ora, Example 7.24]. For a step `η > 0` and a weight
`lam ≥ 0`, the resolvent `J_η z` of `x ↦ lam * ∑ a, |x a|` on `EuclideanSpace ℝ α` is the single
point obtained from `z` by soft thresholding each coordinate at the level `η * lam`. -/
theorem moreauYosidaResolvent_mul_sum_abs {η : ℝ≥0} (hη : 0 < η) {lam : ℝ} (hlam : 0 ≤ lam)
    (z : EuclideanSpace ℝ α) :
    TauCeti.moreauYosidaResolvent (fun x : EuclideanSpace ℝ α ↦ ((lam * ∑ a, |x a| : ℝ) : EReal))
        η z =
      {WithLp.toLp 2 (fun a ↦ softThreshold (η * lam) (z a))} := by
  ext y
  rw [mem_moreauYosidaResolvent_coe_iff hη, mem_singleton_iff]
  refine Iff.trans ?_ (isMinOn_mul_sum_abs_add_norm_sub_sq_iff (mul_nonneg η.2 hlam) z y)
  simp only [mul_assoc]
  -- the two objectives differ only in the instance path to the norm of `EuclideanSpace ℝ α`
  exact Iff.rfl

end Euclidean

end LMLExplore
