/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Exponential moments of a shifted random variable

For a real random variable `X` under a measure `P`, a level `x` and a parameter
`t ∈ integrableExpSet X P`, the function `exp (t (X - x))` is integrable. If `X ≤ x` almost surely,
then `E[exp (t (X - x))]` tends to `P(X = x)` as `t → ∞`: the integrand tends to `0` where
`X < x` and is `1` where `X = x`. This limit gives the value of the Cramér rate function at the
essential supremum of `X`.

## Main statements

* `LMLExplore.integrable_exp_mul_sub`: `exp (t (X - x))` is integrable for
  `t ∈ integrableExpSet X P`.
* `LMLExplore.tendsto_integral_exp_mul_sub`: if `X ≤ x` almost surely, then
  `E[exp (t (X - x))]` tends to `P(X = x)` as `t → ∞`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter

open scoped Topology

namespace LMLExplore

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : Ω → ℝ} {P : Measure Ω} {t x : ℝ}

/-- For `t ∈ integrableExpSet X P`, the function `exp (t (X - x))` is integrable. -/
lemma integrable_exp_mul_sub (ht : t ∈ integrableExpSet X P) (x : ℝ) :
    Integrable (fun ω ↦ exp (t * (X ω - x))) P := by
  refine (ht.mul_const (exp (-(t * x)))).congr (Eventually.of_forall fun ω ↦ ?_)
  simp only [← exp_add]
  ring_nf

/-- If `X ≤ x` almost surely, then `E[exp (t (X - x))]` tends to `P(X = x)` as `t → ∞`. -/
theorem tendsto_integral_exp_mul_sub [IsFiniteMeasure P] (hX : AEMeasurable X P)
    (h : ∀ᵐ ω ∂P, X ω ≤ x) :
    Tendsto (fun t ↦ ∫ ω, exp (t * (X ω - x)) ∂P) atTop (𝓝 (P.real {ω | X ω = x})) := by
  have hmeas : NullMeasurableSet {ω | X ω = x} P := hX.nullMeasurable (measurableSet_singleton x)
  have h_eq : P.real {ω | X ω = x} = ∫ ω, {ω | X ω = x}.indicator 1 ω ∂P := by
    rw [integral_indicator₀ hmeas]
    simp
  rw [h_eq]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ 1) ?_ ?_
    (integrable_const _) ?_
  · exact Eventually.of_forall fun t ↦
      (measurable_exp.comp_aemeasurable ((hX.sub_const x).const_mul t)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 0] with t ht
    filter_upwards [h] with ω hω
    rw [norm_of_nonneg (exp_pos _).le, exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos ht (by linarith)
  · filter_upwards [h] with ω hω
    rcases hω.lt_or_eq with hlt | heq
    · have h_ne : ω ∉ {ω | X ω = x} := fun h' ↦ hlt.ne h'
      rw [indicator_of_notMem h_ne]
      exact tendsto_exp_atBot.comp
        (tendsto_id.atTop_mul_const_of_neg (sub_neg.2 hlt))
    · have h_mem : ω ∈ {ω | X ω = x} := heq
      simp only [indicator_of_mem h_mem, Pi.one_apply, heq, sub_self, mul_zero, exp_zero]
      exact tendsto_const_nhds

end LMLExplore
