/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Lambert function

The map `w ↦ w * exp w` is strictly increasing on `[-1, ∞)`, from `-exp (-1)` to `∞`. The
**Lambert function** `Real.lambertW` is its inverse: its principal branch `W₀`, with
`lambertW x * exp (lambertW x) = x` and `-1 ≤ lambertW x` for `x ≥ -exp (-1)`. Below `-exp (-1)`
it is `-1`, so that it is monotone and continuous on all of `ℝ`. It maps `[0, ∞)` onto `[0, ∞)`.

The Lambert function solves the equations `y = a * exp y`, which appear when optimizing
expressions such as `a * y - y * exp (y ^ 2 / 2)`: the regret bounds of parameter-free online
learning and the lower bounds that match them are stated through it [Ora, Appendix A.2.1].
This file proves the API that these bounds use:

* `lambertW_mul_exp_lambertW`, `lambertW_mul_exp`: `lambertW` inverts `w ↦ w * exp w`;
* `le_lambertW_iff`, `lambertW_le_iff`: comparisons with `lambertW x` are comparisons with
  `w * exp w`;
* `monotone_lambertW`, `strictMonoOn_lambertW`, `continuous_lambertW`,
  `tendsto_lambertW_atTop`;
* `exp_lambertW`, `exp_lambertW_div_two`, `lambertW_eq_log_sub_log`:
  `exp (lambertW x) = x / lambertW x`, `exp (lambertW x / 2) = √(x / lambertW x)` and
  `lambertW x = log x - log (lambertW x)` for `x > 0`;
* `lambertW_le_log_one_add`, `lambertW_le_sqrt`: `lambertW x ≤ log (1 + x)` and
  `lambertW x ≤ √x` for `x ≥ 0` [Ora, Theorem A.6];
* `log_sub_log_log_le_lambertW`, `lambertW_le_log`: `log x - log (log x) ≤ lambertW x ≤ log x`
  for `x ≥ e`;
* `tendsto_lambertW_div_log`: `lambertW x / log x → 1` as `x → ∞` [Ora, Theorem A.4].

## Main definitions

* `Real.mulExpOrderIso`: `w ↦ w * exp w` as an order isomorphism from `[-1, ∞)` onto
  `[-exp (-1), ∞)`.
* `Real.lambertW`: the principal branch of the Lambert function.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Set Filter Topology

namespace Real

/-- The derivative of `w ↦ w * exp w` is `(w + 1) * exp w`. -/
lemma hasDerivAt_mul_exp (w : ℝ) : HasDerivAt (fun w ↦ w * exp w) ((w + 1) * exp w) w :=
  ((hasDerivAt_id' w).mul (hasDerivAt_exp w)).congr_deriv (by ring)

/-- The map `w ↦ w * exp w` is strictly increasing on `[-1, ∞)`. -/
lemma strictMonoOn_mul_exp : StrictMonoOn (fun w ↦ w * exp w) (Ici (-1)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) (by fun_prop) fun w hw ↦ ?_
  rw [interior_Ici, mem_Ioi] at hw
  rw [(hasDerivAt_mul_exp w).deriv]
  exact mul_pos (by linarith) (exp_pos w)

/-- The minimum of `w ↦ w * exp w` on `[-1, ∞)` is `-exp (-1)`, at `-1`. -/
lemma neg_exp_neg_one_le_mul_exp {w : ℝ} (hw : -1 ≤ w) : -exp (-1) ≤ w * exp w := by
  have h := strictMonoOn_mul_exp.monotoneOn (self_mem_Ici (a := (-1 : ℝ))) hw hw
  simpa using h

/-- The map `w ↦ w * exp w` takes every value of `[-exp (-1), ∞)` on `[-1, ∞)`. -/
lemma exists_mul_exp_eq {x : ℝ} (hx : -exp (-1) ≤ x) : ∃ w, -1 ≤ w ∧ w * exp w = x := by
  set b := max x 0
  have hb : -1 ≤ b := (le_max_right x 0).trans' (by norm_num)
  have hxb : x ≤ b * exp b := (le_max_left x 0).trans
    (le_mul_of_one_le_right (le_max_right x 0) (one_le_exp (le_max_right x 0)))
  obtain ⟨w, hw, hwx⟩ := intermediate_value_Icc hb (f := fun w ↦ w * exp w) (by fun_prop)
    ⟨by simpa using hx, hxb⟩
  exact ⟨w, hw.1, hwx⟩

/-- The map `w ↦ w * exp w` as an order isomorphism from `[-1, ∞)` onto `[-exp (-1), ∞)`. Its
inverse is the Lambert function `Real.lambertW`. -/
noncomputable def mulExpOrderIso : Ici (-1 : ℝ) ≃o Ici (-exp (-1)) :=
  StrictMono.orderIsoOfSurjective (fun w ↦ ⟨w * exp w, neg_exp_neg_one_le_mul_exp w.2⟩)
    (fun a b h ↦ Subtype.mk_lt_mk.2 (strictMonoOn_mul_exp a.2 b.2 h))
    fun x ↦ by
      obtain ⟨w, hw, hwx⟩ := exists_mul_exp_eq x.2
      exact ⟨⟨w, hw⟩, Subtype.ext hwx⟩

@[simp]
lemma coe_mulExpOrderIso_apply (w : Ici (-1 : ℝ)) :
    (mulExpOrderIso w : ℝ) = w * exp w :=
  congrArg Subtype.val (congrFun (StrictMono.coe_orderIsoOfSurjective _ _ _) w)

/-- The **Lambert function** (its principal branch `W₀`): for `x ≥ -exp (-1)`, the unique
`w ≥ -1` with `w * exp w = x`. It is `-1` for `x ≤ -exp (-1)`, and it maps `[0, ∞)` onto
`[0, ∞)`. -/
noncomputable def lambertW (x : ℝ) : ℝ :=
  mulExpOrderIso.symm (projIci (-exp (-1)) x)

lemma lambertW_def (x : ℝ) :
    lambertW x = mulExpOrderIso.symm (projIci (-exp (-1)) x) := (rfl)

variable {x w : ℝ}

/-- The Lambert function takes values in `[-1, ∞)`. -/
lemma neg_one_le_lambertW (x : ℝ) : -1 ≤ lambertW x :=
  (mulExpOrderIso.symm (projIci (-exp (-1)) x)).2

/-- The Lambert function inverts `w ↦ w * exp w`: `lambertW x * exp (lambertW x) = x` for
`x ≥ -exp (-1)`. -/
@[simp]
theorem lambertW_mul_exp_lambertW (hx : -exp (-1) ≤ x) : lambertW x * exp (lambertW x) = x := by
  have h := congrArg Subtype.val (mulExpOrderIso.apply_symm_apply (projIci (-exp (-1)) x))
  rwa [coe_mulExpOrderIso_apply, coe_projIci, max_eq_right hx] at h

/-- The Lambert function inverts `w ↦ w * exp w` on `[-1, ∞)`. -/
@[simp]
theorem lambertW_mul_exp (hw : -1 ≤ w) : lambertW (w * exp w) = w := by
  have h : projIci (-exp (-1)) (w * exp w) = mulExpOrderIso ⟨w, hw⟩ :=
    Subtype.ext (by rw [coe_projIci, max_eq_right (neg_exp_neg_one_le_mul_exp hw),
      coe_mulExpOrderIso_apply])
  rw [lambertW_def, h, OrderIso.symm_apply_apply]

/-- For `x ≥ -exp (-1)` and `w ≥ -1`, `lambertW x = w` iff `w * exp w = x`. -/
theorem lambertW_eq_iff (hx : -exp (-1) ≤ x) (hw : -1 ≤ w) :
    lambertW x = w ↔ w * exp w = x := by
  constructor
  · rintro rfl
    exact lambertW_mul_exp_lambertW hx
  · rintro rfl
    exact lambertW_mul_exp hw

/-- Below `-exp (-1)`, the Lambert function is `-1`. -/
theorem lambertW_eq_neg_one_of_le (hx : x ≤ -exp (-1)) : lambertW x = -1 := by
  have h := lambertW_mul_exp (w := -1) le_rfl
  rw [neg_one_mul] at h
  rw [lambertW_def, projIci_of_le hx, ← projIci_of_le (le_refl (-exp (-1))), ← lambertW_def, h]

@[simp]
lemma lambertW_zero : lambertW 0 = 0 := by
  simpa using lambertW_mul_exp (w := 0) (by norm_num)

@[simp]
lemma lambertW_exp_one : lambertW (exp 1) = 1 := by
  simpa using lambertW_mul_exp (w := 1) (by norm_num)

@[simp]
lemma lambertW_neg_exp_neg_one : lambertW (-exp (-1)) = -1 :=
  lambertW_eq_neg_one_of_le le_rfl

/-- The Lambert function is monotone. -/
theorem monotone_lambertW : Monotone lambertW := fun _ _ h ↦
  mulExpOrderIso.symm.monotone (monotone_projIci h)

/-- The Lambert function is strictly increasing on `[-exp (-1), ∞)`. -/
theorem strictMonoOn_lambertW : StrictMonoOn lambertW (Ici (-exp (-1))) := fun x hx y hy h ↦
  mulExpOrderIso.symm.strictMono (by
    rw [← Subtype.coe_lt_coe, coe_projIci, coe_projIci, max_eq_right hx, max_eq_right hy]
    exact h)

/-- The Lambert function is continuous. -/
@[fun_prop]
theorem continuous_lambertW : Continuous lambertW :=
  continuous_subtype_val.comp <| mulExpOrderIso.symm.continuous.comp <|
    (continuous_const.max continuous_id).subtype_mk _

/-- For `x ≥ -exp (-1)` and `w ≥ -1`, `w ≤ lambertW x` iff `w * exp w ≤ x`. -/
theorem le_lambertW_iff (hx : -exp (-1) ≤ x) (hw : -1 ≤ w) :
    w ≤ lambertW x ↔ w * exp w ≤ x := by
  conv_rhs => rw [← lambertW_mul_exp_lambertW hx]
  exact (strictMonoOn_mul_exp.le_iff_le hw (neg_one_le_lambertW x)).symm

/-- For `x ≥ -exp (-1)` and `w ≥ -1`, `lambertW x ≤ w` iff `x ≤ w * exp w`. -/
theorem lambertW_le_iff (hx : -exp (-1) ≤ x) (hw : -1 ≤ w) :
    lambertW x ≤ w ↔ x ≤ w * exp w := by
  conv_rhs => rw [← lambertW_mul_exp_lambertW hx]
  exact (strictMonoOn_mul_exp.le_iff_le (neg_one_le_lambertW x) hw).symm

/-- The Lambert function is nonnegative exactly on `[0, ∞)`. -/
@[simp]
theorem lambertW_nonneg_iff : 0 ≤ lambertW x ↔ 0 ≤ x := by
  rcases le_total x (-exp (-1)) with hx | hx
  · rw [lambertW_eq_neg_one_of_le hx]
    exact iff_of_false (by norm_num) (hx.trans_lt (neg_neg_of_pos (exp_pos _))).not_ge
  · simpa using le_lambertW_iff hx (w := 0) (by norm_num)

/-- The Lambert function is positive exactly on `(0, ∞)`. -/
@[simp]
theorem lambertW_pos_iff : 0 < lambertW x ↔ 0 < x := by
  rw [← not_le, ← not_le, not_iff_not]
  rcases le_total x (-exp (-1)) with hx | hx
  · rw [lambertW_eq_neg_one_of_le hx]
    exact iff_of_true (by norm_num) (hx.trans (neg_nonpos.2 (exp_pos _).le))
  · simpa using lambertW_le_iff hx (w := 0) (by norm_num)

theorem lambertW_nonneg (hx : 0 ≤ x) : 0 ≤ lambertW x := lambertW_nonneg_iff.2 hx

theorem lambertW_pos (hx : 0 < x) : 0 < lambertW x := lambertW_pos_iff.2 hx

/-- `lambertW x ≥ 1` exactly for `x ≥ e`. -/
@[simp]
theorem one_le_lambertW_iff : 1 ≤ lambertW x ↔ exp 1 ≤ x := by
  rcases le_total x (-exp (-1)) with hx | hx
  · rw [lambertW_eq_neg_one_of_le hx]
    refine iff_of_false (by norm_num) fun h ↦ ?_
    linarith [exp_pos 1, exp_pos (-1)]
  · simpa using le_lambertW_iff hx (w := 1) (by norm_num)

/-- The Lambert function tends to `∞` at `∞`. -/
theorem tendsto_lambertW_atTop : Tendsto lambertW atTop atTop := by
  refine monotone_lambertW.tendsto_atTop_atTop fun b ↦ ⟨max b 0 * exp (max b 0), ?_⟩
  rw [lambertW_mul_exp ((le_max_right b 0).trans' (by norm_num))]
  exact le_max_left b 0

/-- For `x > 0`, `exp (lambertW x) = x / lambertW x`. -/
theorem exp_lambertW (hx : 0 < x) : exp (lambertW x) = x / lambertW x := by
  rw [eq_div_iff (lambertW_pos hx).ne', mul_comm,
    lambertW_mul_exp_lambertW ((neg_neg_of_pos (exp_pos _)).le.trans hx.le)]

/-- For `x > 0`, `lambertW x = log x - log (lambertW x)`. -/
theorem lambertW_eq_log_sub_log (hx : 0 < x) : lambertW x = log x - log (lambertW x) := by
  have h := congrArg log
    (lambertW_mul_exp_lambertW ((neg_nonpos.2 (exp_pos (-1)).le).trans hx.le))
  rw [log_mul (lambertW_pos hx).ne' (exp_pos _).ne', log_exp] at h
  linarith

/-- For `x > 0`, `exp (lambertW x / 2) = √(x / lambertW x)` [Ora, Appendix A.2.1]. -/
theorem exp_lambertW_div_two (hx : 0 < x) : exp (lambertW x / 2) = √(x / lambertW x) := by
  rw [← exp_lambertW hx, eq_comm, sqrt_eq_iff_eq_sq (exp_pos _).le (exp_pos _).le, ← exp_nat_mul]
  congr 1
  push_cast
  ring

/-- For `x ≥ 0`, `lambertW x ≤ log (1 + x)` [Ora, Theorem A.6]. -/
theorem lambertW_le_log_one_add (hx : 0 ≤ x) : lambertW x ≤ log (1 + x) := by
  have h1x : 0 < 1 + x := by linarith
  have hlog : 0 ≤ log (1 + x) := log_nonneg (by linarith)
  rw [lambertW_le_iff ((neg_nonpos.2 (exp_pos _).le).trans hx) (by linarith), exp_log h1x]
  -- `x / (1 + x) = 1 - (1 + x)⁻¹ ≤ log (1 + x)`
  have h := one_sub_inv_le_log_of_pos h1x
  have : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
  rw [this, div_le_iff₀ h1x] at h
  linarith

/-- For `x ≥ 0`, `lambertW x ≤ √x`: `lambertW x ^ 2 ≤ lambertW x * exp (lambertW x) = x`. -/
theorem lambertW_le_sqrt (hx : 0 ≤ x) : lambertW x ≤ √x := by
  have hW := lambertW_nonneg hx
  refine le_sqrt_of_sq_le ?_
  calc lambertW x ^ 2 = lambertW x * lambertW x := sq _
    _ ≤ lambertW x * exp (lambertW x) := by
        gcongr
        linarith [add_one_le_exp (lambertW x)]
    _ = x := lambertW_mul_exp_lambertW ((neg_nonpos.2 (exp_pos _).le).trans hx)

/-- For `x ≥ e`, `lambertW x ≤ log x`. -/
theorem lambertW_le_log (hx : exp 1 ≤ x) : lambertW x ≤ log x := by
  have hx0 : 0 < x := (exp_pos 1).trans_le hx
  have hlog : 1 ≤ log x := by rwa [le_log_iff_exp_le hx0]
  rw [lambertW_le_iff ((neg_nonpos.2 (exp_pos _).le).trans hx0.le) (by linarith), exp_log hx0]
  exact le_mul_of_one_le_left hx0.le hlog

/-- For `x ≥ e`, `log x - log (log x) ≤ lambertW x`. -/
theorem log_sub_log_log_le_lambertW (hx : exp 1 ≤ x) : log x - log (log x) ≤ lambertW x := by
  have hx0 : 0 < x := (exp_pos 1).trans_le hx
  have hlog : 1 ≤ log x := by rwa [le_log_iff_exp_le hx0]
  have hloglog : 0 ≤ log (log x) := log_nonneg hlog
  have hw : -1 ≤ log x - log (log x) := by
    linarith [log_le_sub_one_of_pos (zero_lt_one.trans_le hlog)]
  rw [le_lambertW_iff ((neg_nonpos.2 (exp_pos _).le).trans hx0.le) hw, exp_sub, exp_log hx0,
    exp_log (zero_lt_one.trans_le hlog), mul_div_assoc', div_le_iff₀ (zero_lt_one.trans_le hlog)]
  nlinarith

/-- **The Lambert function is asymptotic to the logarithm** [Ora, Theorem A.4]:
`lambertW x / log x → 1` as `x → ∞`. -/
theorem tendsto_lambertW_div_log : Tendsto (fun x ↦ lambertW x / log x) atTop (𝓝 1) := by
  -- `1 - log (log x) / log x ≤ lambertW x / log x ≤ 1` for `x ≥ e`
  have h0 : Tendsto (fun x ↦ log (log x) / log x) atTop (𝓝 0) := by
    have h := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_log_atTop
    refine h.congr fun x ↦ ?_
    simp
  have hlow : Tendsto (fun x ↦ 1 - log (log x) / log x) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (exp 1)] with x hx
    have hlog : 0 < log x := zero_lt_one.trans_le (by
      rwa [le_log_iff_exp_le ((exp_pos 1).trans_le hx)])
    rw [one_sub_div hlog.ne', div_le_div_iff_of_pos_right hlog]
    exact log_sub_log_log_le_lambertW hx
  · filter_upwards [eventually_ge_atTop (exp 1)] with x hx
    have hlog : 0 < log x := zero_lt_one.trans_le (by
      rwa [le_log_iff_exp_le ((exp_pos 1).trans_le hx)])
    rw [div_le_one hlog]
    exact lambertW_le_log hx

end Real
