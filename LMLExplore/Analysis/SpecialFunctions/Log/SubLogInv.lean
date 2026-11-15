/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The inverse of `u ↦ u - log u` on `[1, ∞)`

The function `h(u) = u - log u` is strictly increasing on `[1, ∞)`, from `h(1) = 1` to `∞`, so it
has an inverse `h⁻¹ : [1, ∞) → [1, ∞)`: `h⁻¹(x)` is the unique `u ≥ 1` with `u - log u = x`, the
larger of the two solutions of `u e^{-u} = e^{-x}`. In terms of the negative branch `W₋₁` of the
Lambert function, `h⁻¹(x) = -W₋₁(-e^{-x})`. It is the inverse function through which Kaufmann and
Koolen [KK21] express the calibration function of their time-uniform deviation inequalities for
several arms; it grows like `x + log x`:
`x + log x ≤ h⁻¹(x) ≤ x + log (x + √(2 (x - 1)))` [KK21, Proposition 8].

## Main definitions

* `Real.subLogInv x`: `h⁻¹(x)` for `x ≥ 1`, and `1` for `x ≤ 1`.

## Main statements

* `Real.strictMonoOn_sub_log`, `Real.monotoneOn_sub_log`, `Real.sub_log_lt_sub_log`,
  `Real.sub_log_le_sub_log`, `Real.one_le_sub_log`: `h` is strictly increasing on `[1, ∞)`, and
  `1 ≤ h(u)` for `u > 0`.
* `Real.subLogInv_sub_log_subLogInv`, `Real.subLogInv_sub_log`, `Real.subLogInv_eq_iff`: `subLogInv`
  is the inverse of `h` on `[1, ∞)`; `Real.subLogInv_le_iff`, `Real.lt_subLogInv_iff` compare it
  with a point of `[1, ∞)`.
* `Real.monotone_subLogInv`, `Real.strictMonoOn_subLogInv`, `Real.continuous_subLogInv`.
* `Real.add_log_le_subLogInv`, `Real.subLogInv_le_add_log_add_sqrt`
  [KK21, Proposition 8], `Real.subLogInv_le_add_log_two_mul`: `x + log x ≤ h⁻¹(x)` and
  `h⁻¹(x) ≤ x + log (x + √(2 (x - 1))) ≤ x + log (2 x)` for `x ≥ 1`.
* `Real.subLogInv_one_add_le_div`, `Real.isLeast_subLogInv_one_add` [KK21, Lemma 28]: for
  `x > 0`, the minimum of `(x - log (1 - q)) / q` over `q ∈ (0, 1)` is `h⁻¹(1 + x)`, attained at
  `q = 1 - 1 / h⁻¹(1 + x)`.

## Implementation notes

`subLogInv x` is defined with `Function.invFunOn` at `max x 1`, so that it is `1` on `(-∞, 1]`.
It is then monotone and continuous on all of `ℝ`, and `subLogInv x - log (subLogInv x) = max x 1`
for every `x`.

## References

* [KK21] E. Kaufmann and W. M. Koolen, *Mixture martingales revisited with applications to
  sequential tests and confidence intervals*, JMLR 22 (2021), Proposition 8 and Lemma 28.
-/

public section

open Set

namespace Real

/-- `u ↦ u - log u` is strictly increasing on `[1, ∞)`. -/
theorem strictMonoOn_sub_log : StrictMonoOn (fun u : ℝ ↦ u - log u) (Ici 1) := by
  intro a ha b hb hab
  simp only [mem_Ici] at ha hb
  have ha0 : 0 < a := by linarith
  have h := log_lt_sub_one_of_pos (div_pos (by linarith) ha0)
    (ne_of_gt ((one_lt_div ha0).2 hab))
  rw [log_div (by linarith) ha0.ne'] at h
  have h' : b / a - 1 ≤ b - a := by
    rw [div_sub_one ha0.ne', div_le_iff₀ ha0]
    nlinarith
  linarith

/-- `u ↦ u - log u` is monotone on `[1, ∞)`. -/
theorem monotoneOn_sub_log : MonotoneOn (fun u : ℝ ↦ u - log u) (Ici 1) :=
  strictMonoOn_sub_log.monotoneOn

/-- `a - log a < b - log b` for `1 ≤ a < b`. -/
theorem sub_log_lt_sub_log {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) : a - log a < b - log b :=
  strictMonoOn_sub_log (mem_Ici.2 ha) (mem_Ici.2 (ha.trans hab.le)) hab

/-- `a - log a ≤ b - log b` for `1 ≤ a ≤ b`. -/
theorem sub_log_le_sub_log {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : a - log a ≤ b - log b :=
  monotoneOn_sub_log (mem_Ici.2 ha) (mem_Ici.2 (ha.trans hab)) hab

/-- `1 ≤ u - log u` for `u > 0`. -/
theorem one_le_sub_log {u : ℝ} (hu : 0 < u) : 1 ≤ u - log u := by
  linarith [log_le_sub_one_of_pos hu]

/-- Every `x ≥ 1` is `u - log u` for some `u ≥ 1`. -/
private theorem exists_sub_log_eq {x : ℝ} (hx : 1 ≤ x) : ∃ u ∈ Ici (1 : ℝ), u - log u = x := by
  have h2x : (1 : ℝ) ≤ 2 * x := by linarith
  have hcont : ContinuousOn (fun u : ℝ ↦ u - log u) (Icc 1 (2 * x)) :=
    continuousOn_id.sub (continuousOn_log.mono fun u hu ↦ (by linarith [hu.1] : (0 : ℝ) < u).ne')
  have hmem : x ∈ Icc ((fun u : ℝ ↦ u - log u) 1) ((fun u : ℝ ↦ u - log u) (2 * x)) := by
    refine ⟨by simpa using hx, ?_⟩
    have hlog := log_le_sub_one_of_pos (by linarith : (0 : ℝ) < x)
    have hlog2 := log_two_lt_d9
    simp only [log_mul two_ne_zero (by linarith : x ≠ 0)]
    norm_num at hlog2
    linarith
  obtain ⟨u, hu, hux⟩ := intermediate_value_Icc h2x hcont hmem
  exact ⟨u, hu.1, hux⟩

/-- The inverse `h⁻¹` of `h(u) = u - log u` on `[1, ∞)`, extended by `1` on `(-∞, 1]`: for
`x ≥ 1`, `subLogInv x` is the unique `u ≥ 1` with `u - log u = x`. It is `-W₋₁(-e^{-x})` for the
negative branch `W₋₁` of the Lambert function. -/
noncomputable def subLogInv (x : ℝ) : ℝ :=
  Function.invFunOn (fun u : ℝ ↦ u - log u) (Ici 1) (max x 1)

private theorem subLogInv_spec (x : ℝ) :
    1 ≤ subLogInv x ∧ subLogInv x - log (subLogInv x) = max x 1 :=
  Function.invFunOn_pos (exists_sub_log_eq (le_max_right x 1))

theorem one_le_subLogInv (x : ℝ) : 1 ≤ subLogInv x :=
  (subLogInv_spec x).1

theorem subLogInv_pos (x : ℝ) : 0 < subLogInv x :=
  zero_lt_one.trans_le (one_le_subLogInv x)

@[simp]
theorem subLogInv_sub_log_subLogInv_eq_max (x : ℝ) :
    subLogInv x - log (subLogInv x) = max x 1 :=
  (subLogInv_spec x).2

/-- `subLogInv` is a right inverse of `u ↦ u - log u` on `[1, ∞)`. -/
theorem subLogInv_sub_log_subLogInv {x : ℝ} (hx : 1 ≤ x) :
    subLogInv x - log (subLogInv x) = x := by
  rw [subLogInv_sub_log_subLogInv_eq_max, max_eq_left hx]

/-- The fixed-point form `h⁻¹(x) = x + log h⁻¹(x)` of the inverse, for `x ≥ 1`. -/
theorem subLogInv_eq_add_log {x : ℝ} (hx : 1 ≤ x) : subLogInv x = x + log (subLogInv x) := by
  linarith [subLogInv_sub_log_subLogInv hx]

/-- `subLogInv` is a left inverse of `u ↦ u - log u` on `[1, ∞)`. -/
@[simp]
theorem subLogInv_sub_log {u : ℝ} (hu : 1 ≤ u) : subLogInv (u - log u) = u :=
  strictMonoOn_sub_log.injOn (one_le_subLogInv _) hu
    (by simpa using subLogInv_sub_log_subLogInv (one_le_sub_log (by linarith)))

theorem subLogInv_eq_iff {x u : ℝ} (hx : 1 ≤ x) (hu : 1 ≤ u) :
    subLogInv x = u ↔ u - log u = x := by
  constructor
  · rintro rfl
    exact subLogInv_sub_log_subLogInv hx
  · rintro rfl
    exact subLogInv_sub_log hu

theorem subLogInv_of_le_one {x : ℝ} (hx : x ≤ 1) : subLogInv x = 1 :=
  strictMonoOn_sub_log.injOn (one_le_subLogInv x) (mem_Ici.2 le_rfl) (by
    simp [subLogInv_sub_log_subLogInv_eq_max, max_eq_right hx])

@[simp]
theorem subLogInv_one : subLogInv 1 = 1 :=
  subLogInv_of_le_one le_rfl

theorem subLogInv_le_iff {x u : ℝ} (hu : 1 ≤ u) : subLogInv x ≤ u ↔ x ≤ u - log u := by
  constructor
  · intro h
    have h' := sub_log_le_sub_log (one_le_subLogInv x) h
    rw [subLogInv_sub_log_subLogInv_eq_max] at h'
    exact (le_max_left x 1).trans h'
  · intro h
    by_contra hlt
    have h' := sub_log_lt_sub_log hu (not_le.1 hlt)
    rw [subLogInv_sub_log_subLogInv_eq_max] at h'
    have h1 := one_le_sub_log (by linarith : (0 : ℝ) < u)
    exact absurd h' (not_lt.2 (max_le h h1))

theorem lt_subLogInv_iff {x u : ℝ} (hu : 1 ≤ u) : u < subLogInv x ↔ u - log u < x := by
  simpa using (subLogInv_le_iff (x := x) hu).not

theorem monotone_subLogInv : Monotone subLogInv := by
  intro x x' hxx'
  rw [subLogInv_le_iff (one_le_subLogInv x'), subLogInv_sub_log_subLogInv_eq_max]
  exact hxx'.trans (le_max_left x' 1)

theorem strictMonoOn_subLogInv : StrictMonoOn subLogInv (Ici 1) := by
  intro x hx x' hx' hxx'
  refine lt_of_le_of_ne (monotone_subLogInv hxx'.le) fun h ↦ hxx'.ne ?_
  rw [← subLogInv_sub_log_subLogInv hx, ← subLogInv_sub_log_subLogInv (x := x') hx', h]

theorem continuous_subLogInv : Continuous subLogInv := by
  let g : ℝ → Ici (1 : ℝ) := fun x ↦ ⟨subLogInv x, one_le_subLogInv x⟩
  have hg : Monotone g := fun x x' h ↦ Subtype.mk_le_mk.2 (monotone_subLogInv h)
  have hsurj : Function.Surjective g := fun u ↦
    ⟨u.1 - log u.1, Subtype.ext (subLogInv_sub_log u.2)⟩
  exact continuous_subtype_val.comp (hg.continuous_of_surjective hsurj)

/-- `x ≤ h⁻¹(x)`. -/
theorem self_le_subLogInv (x : ℝ) : x ≤ subLogInv x := by
  have h := subLogInv_sub_log_subLogInv_eq_max x
  have hlog := log_nonneg (one_le_subLogInv x)
  linarith [le_max_left x 1]

/-- `x + log x ≤ h⁻¹(x)` for `x > 0`. -/
theorem add_log_le_subLogInv {x : ℝ} (hx : 0 < x) : x + log x ≤ subLogInv x := by
  rcases le_total 1 x with h1 | h1
  · rw [subLogInv_eq_add_log h1]
    gcongr
    exact self_le_subLogInv x
  · have hlog : log x ≤ 0 := log_nonpos hx.le h1
    linarith [one_le_subLogInv x]

/-- **The bound of [KK21, Proposition 8]**: `h⁻¹(x) ≤ x + log (x + √(2 (x - 1)))` for `x ≥ 1`. -/
theorem subLogInv_le_add_log_add_sqrt {x : ℝ} (hx : 1 ≤ x) :
    subLogInv x ≤ x + log (x + √(2 * (x - 1))) := by
  set s := √(2 * (x - 1))
  have hs : 0 ≤ s := sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * (x - 1) := sq_sqrt (by linarith)
  have hxs : 0 < x + s := by linarith
  have hlog0 : 0 ≤ log (x + s) := log_nonneg (by linarith)
  -- `log (x + s) ≤ s`, since `x + s = 1 + s + s ^ 2 / 2 ≤ exp s`
  have hlogs : log (x + s) ≤ s := by
    rw [log_le_iff_le_exp hxs]
    linarith [quadratic_le_exp_of_nonneg hs]
  rw [subLogInv_le_iff (by linarith)]
  have : log (x + log (x + s)) ≤ log (x + s) := log_le_log (by linarith) (by linarith)
  linarith

/-- `h⁻¹(x) ≤ x + log (2 x)` for `x ≥ 1`. -/
theorem subLogInv_le_add_log_two_mul {x : ℝ} (hx : 1 ≤ x) : subLogInv x ≤ x + log (2 * x) := by
  refine (subLogInv_le_add_log_add_sqrt hx).trans ?_
  have hs : √(2 * (x - 1)) ≤ x := by
    rw [sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  gcongr
  linarith

/-- **[KK21, Lemma 28]**, lower bound: `h⁻¹(1 + x) ≤ (x - log (1 - q)) / q` for `x ≥ 0` and
`q ∈ (0, 1)`. -/
theorem subLogInv_one_add_le_div {x q : ℝ} (hx : 0 ≤ x) (hq0 : 0 < q) (hq1 : q < 1) :
    subLogInv (1 + x) ≤ (x - log (1 - q)) / q := by
  set u := subLogInv (1 + x)
  have hu : u - log u = 1 + x := subLogInv_sub_log_subLogInv (by linarith)
  have hu0 : 0 < u := subLogInv_pos _
  -- with `w = (1 - q) u > 0`, the claim is `log w ≤ w - 1`
  have hw := log_le_sub_one_of_pos (mul_pos (sub_pos.2 hq1) hu0)
  rw [log_mul (sub_pos.2 hq1).ne' hu0.ne'] at hw
  rw [le_div_iff₀ hq0]
  nlinarith

/-- **[KK21, Lemma 28]**: for `x > 0`, the minimum of `(x - log (1 - q)) / q` over `q ∈ (0, 1)` is
`h⁻¹(1 + x)`, attained at `q = 1 - 1 / h⁻¹(1 + x)`. -/
theorem isLeast_subLogInv_one_add {x : ℝ} (hx : 0 < x) :
    IsLeast ((fun q ↦ (x - log (1 - q)) / q) '' Ioo 0 1) (subLogInv (1 + x)) := by
  set u := subLogInv (1 + x)
  have hu : u - log u = 1 + x := subLogInv_sub_log_subLogInv (by linarith)
  have hu1 : 1 < u := by
    rw [lt_subLogInv_iff le_rfl, log_one, sub_zero]
    linarith
  have hu0 : 0 < u := by linarith
  refine ⟨⟨1 - u⁻¹, ⟨sub_pos.2 (inv_lt_one_of_one_lt₀ hu1), by simp [hu0]⟩, ?_⟩,
    ?_⟩
  · have hq : 1 - u⁻¹ ≠ 0 := (sub_pos.2 (inv_lt_one_of_one_lt₀ hu1)).ne'
    simp only [sub_sub_cancel, log_inv]
    rw [div_eq_iff hq]
    field_simp
    linarith
  · rintro _ ⟨q, ⟨hq0, hq1⟩, rfl⟩
    exact subLogInv_one_add_le_div hx.le hq0 hq1

end Real
