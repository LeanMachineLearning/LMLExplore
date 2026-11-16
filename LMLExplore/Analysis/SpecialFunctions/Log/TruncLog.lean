/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# The truncated logarithm of an extended nonnegative real

`ENNReal.truncLog c x` is the logarithm `ENNReal.log x` of `x : ℝ≥0∞` truncated above at `c : ℝ`,
as a real number: `(min (log x) c).toReal`. It is `c` at `∞` and `0` at `0` (the real part of
`log 0 = ⊥`), and `min (Real.log x.toReal) c` otherwise. Unlike `ENNReal.log`, it is a real
function, bounded on `{x | δ ≤ x}` for `δ > 0`, hence integrable under a finite measure when
composed with a measurable function bounded below by `δ`.

## Main definitions

* `ENNReal.truncLog c x`: the logarithm of `x : ℝ≥0∞` truncated above at `c`, as a real number.

## Main statements

* `ENNReal.truncLog_of_ne`: `truncLog c x = min (Real.log x.toReal) c` for `x ≠ 0, ∞`.
* `ENNReal.abs_truncLog_le`, `ENNReal.integrable_truncLog_comp`: on `{x | δ ≤ x}`, the truncated
  logarithm is bounded, hence integrable under a finite measure.
* `ENNReal.ofReal_exp_truncLog_le`: `exp (truncLog c x) ≤ x` for `x ≠ 0`.
* `ENNReal.min_log_le_truncLog_sub`: mixing `x` with a constant `ε` costs at most `- log (1 - ε)`
  in truncated logarithm.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace ENNReal

/-- The logarithm truncated above at `c`, as a real number. -/
noncomputable def truncLog (c : ℝ) (x : ℝ≥0∞) : ℝ := (min (ENNReal.log x) c).toReal

/-- The definition of the truncated logarithm, `truncLog c x = (min (log x) c).toReal`. -/
lemma truncLog_def (c : ℝ) (x : ℝ≥0∞) : truncLog c x = (min (ENNReal.log x) c).toReal := by
  rw [truncLog]

/-- The truncated logarithm is measurable. -/
lemma measurable_truncLog (c : ℝ) : Measurable (truncLog c) :=
  measurable_ereal_toReal.comp (ENNReal.measurable_log.min measurable_const)

/-- The truncated logarithm of a positive finite number. -/
lemma truncLog_of_ne {c : ℝ} {x : ℝ≥0∞} (h0 : x ≠ 0) (htop : x ≠ ∞) :
    truncLog c x = min (Real.log x.toReal) c := by
  rw [truncLog, ENNReal.log_pos_real h0 htop, ← EReal.coe_strictMono.monotone.map_min,
    EReal.toReal_coe]

/-- The truncated logarithm of `∞` is the truncation level. -/
@[simp]
lemma truncLog_top (c : ℝ) : truncLog c ∞ = c := by simp [truncLog]

/-- The truncated logarithm of `0` is `0`, the real part of `⊥ = log 0`. -/
@[simp]
lemma truncLog_zero (c : ℝ) : truncLog c 0 = 0 := by simp [truncLog]

/-- The truncated logarithm of a nonzero `x` is at most the truncation level. -/
lemma truncLog_le {c : ℝ} {x : ℝ≥0∞} (h0 : x ≠ 0) : truncLog c x ≤ c := by
  by_cases htop : x = ∞
  · rw [htop, truncLog_top]
  · rw [truncLog_of_ne h0 htop]
    exact min_le_right _ _

/-- The truncated logarithm of `x ≥ δ` is at least `min (log δ) c`. -/
lemma min_log_le_truncLog {c δ : ℝ} (hδ : 0 < δ) {x : ℝ≥0∞} (hx : ENNReal.ofReal δ ≤ x) :
    min (Real.log δ) c ≤ truncLog c x := by
  have h0 : x ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hδ) hx).ne'
  by_cases htop : x = ∞
  · rw [htop, truncLog_top]
    exact min_le_right _ _
  · rw [truncLog_of_ne h0 htop]
    exact min_le_min_right c (Real.log_le_log hδ ((ENNReal.ofReal_le_iff_le_toReal htop).1 hx))

/-- The truncated logarithm of `x ≥ δ` is at least `log δ`, if `log δ ≤ c`. -/
lemma log_le_truncLog {c δ : ℝ} (hδ : 0 < δ) {x : ℝ≥0∞} (hx : ENNReal.ofReal δ ≤ x)
    (hc : Real.log δ ≤ c) : Real.log δ ≤ truncLog c x :=
  (min_eq_left hc).symm.le.trans (min_log_le_truncLog hδ hx)

/-- The truncated logarithm of `x ≥ δ` is bounded in absolute value. -/
lemma abs_truncLog_le {c δ : ℝ} (hδ : 0 < δ) {x : ℝ≥0∞} (hx : ENNReal.ofReal δ ≤ x) :
    |truncLog c x| ≤ max |Real.log δ| |c| :=
  abs_le.2 ⟨(le_min ((neg_le_neg (le_max_left _ _)).trans (neg_abs_le _))
      ((neg_le_neg (le_max_right _ _)).trans (neg_abs_le _))).trans (min_log_le_truncLog hδ hx),
    (truncLog_le (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hδ) hx).ne').trans
      ((le_abs_self c).trans (le_max_right _ _))⟩

/-- The truncated logarithm of a measurable function bounded below by `δ > 0` is integrable
under a finite measure. -/
lemma integrable_truncLog_comp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {c δ : ℝ} (hδ : 0 < δ) {V : Ω → ℝ≥0∞} (hVm : Measurable V)
    (hVδ : ∀ ω, ENNReal.ofReal δ ≤ V ω) :
    Integrable (fun ω ↦ truncLog c (V ω)) μ :=
  Integrable.of_bound ((measurable_truncLog c).comp hVm).aestronglyMeasurable
    (max |Real.log δ| |c|) (ae_of_all _ fun ω ↦ (Real.norm_eq_abs _).trans_le
      (abs_truncLog_le hδ (hVδ ω)))

/-- The exponential of the truncated logarithm of a nonzero `x` is at most `x`. -/
lemma ofReal_exp_truncLog_le {c : ℝ} {x : ℝ≥0∞} (h0 : x ≠ 0) :
    ENNReal.ofReal (Real.exp (truncLog c x)) ≤ x := by
  by_cases htop : x = ∞
  · rw [htop]
    exact le_top
  · rw [truncLog_of_ne h0 htop]
    calc ENNReal.ofReal (Real.exp (min (Real.log x.toReal) c))
    _ ≤ ENNReal.ofReal (Real.exp (Real.log x.toReal)) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (min_le_left _ _))
    _ = x := by
      rw [Real.exp_log (ENNReal.toReal_pos h0 htop), ENNReal.ofReal_toReal htop]

/-- Mixing with a constant: `min (log x) c ≤ truncLog c ((1 - ε) x + ε) - log (1 - ε)`. -/
lemma min_log_le_truncLog_sub {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (c : ℝ) (x : ℝ≥0∞) :
    min (ENNReal.log x) c ≤
      ((truncLog c (ENNReal.ofReal (1 - ε) * x + ENNReal.ofReal ε) - Real.log (1 - ε) : ℝ) :
        EReal) := by
  have hlog : Real.log (1 - ε) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  by_cases h0 : x = 0
  · simp [h0]
  by_cases htop : x = ∞
  · have : ENNReal.ofReal (1 - ε) * x + ENNReal.ofReal ε = ∞ := by
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by linarith)).ne', top_add]
    rw [this, truncLog_top]
    exact (min_le_right _ _).trans (EReal.coe_le_coe_iff.2 (by linarith))
  have hε' : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.2 hε0).ne'
  have hV0 : ENNReal.ofReal (1 - ε) * x + ENNReal.ofReal ε ≠ 0 := by simp [hε']
  have hVtop : ENNReal.ofReal (1 - ε) * x + ENNReal.ofReal ε ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop, ENNReal.ofReal_ne_top⟩
  have hVreal : (ENNReal.ofReal (1 - ε) * x + ENNReal.ofReal ε).toReal =
      (1 - ε) * x.toReal + ε := by
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop) ENNReal.ofReal_ne_top,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hε0.le]
  rw [truncLog_of_ne hV0 hVtop, hVreal, ENNReal.log_pos_real h0 htop,
    ← EReal.coe_strictMono.monotone.map_min, EReal.coe_le_coe_iff]
  have hx : 0 < x.toReal := ENNReal.toReal_pos h0 htop
  have hL : Real.log (1 - ε) + Real.log x.toReal ≤ Real.log ((1 - ε) * x.toReal + ε) := by
    rw [← Real.log_mul (by linarith) hx.ne']
    exact Real.log_le_log (_root_.mul_pos (by linarith) hx) (by linarith)
  rw [← min_sub_sub_right]
  exact le_min ((min_le_left _ _).trans (by linarith)) ((min_le_right _ _).trans (by linarith))

end ENNReal
