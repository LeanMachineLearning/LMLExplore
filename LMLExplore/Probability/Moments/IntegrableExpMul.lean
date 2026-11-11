/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Exponential moments of a shifted or pushed-forward random variable

For a real random variable `X` under a measure `P`, a level `x` and a parameter
`t ∈ integrableExpSet X P`, the function `exp (t (X - x))` is integrable, and the cumulant
generating function at `t` is `t x + log E[exp (t (X - x))]`. If `X ≤ x` almost surely,
then `E[exp (t (X - x))]` tends to `P(X = x)` as `t → ∞`: the integrand tends to `0` where
`X < x` and is `1` where `X = x`. This limit gives the value of the Cramér rate function at the
essential supremum of `X`.

The exponential moments of `X` only depend on its law: the identity under the law `P.map X` has
the same exponential moments and the same cumulant generating function as `X` under `P`. This
turns statements about a statistic `T` of an exponential family into statements about the
natural exponential family of the law of `T`.

## Main statements

* `LMLExplore.interior_integrableExpSet_eq_univ`: if every exponential moment of `X` is finite,
  then `interior (integrableExpSet X P)` is the whole line.
* `LMLExplore.integrable_exp_mul_sub`: `exp (t (X - x))` is integrable for
  `t ∈ integrableExpSet X P`.
* `LMLExplore.cgf_eq_mul_add_log_integral_exp_mul_sub`: for `t ∈ integrableExpSet X P`,
  `cgf X P t = t x + log E[exp (t (X - x))]`.
* `LMLExplore.tendsto_integral_exp_mul_sub`: if `X ≤ x` almost surely, then
  `E[exp (t (X - x))]` tends to `P(X = x)` as `t → ∞`.
* `LMLExplore.integrableExpSet_id_map`, `LMLExplore.cgf_id_map`: the identity under the law of `X`
  has the exponential moments and the cumulant generating function of `X`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter

open scoped Topology

namespace LMLExplore

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : Ω → ℝ} {P : Measure Ω} {t x : ℝ}

/-- If every exponential moment of `X` is finite, then the interior of `integrableExpSet X P` is
the whole line. -/
lemma interior_integrableExpSet_eq_univ (h : ∀ t, Integrable (fun ω ↦ exp (t * X ω)) P) :
    interior (integrableExpSet X P) = univ := by
  rw [show integrableExpSet X P = univ from eq_univ_of_forall h, interior_univ]

/-- For `t ∈ integrableExpSet X P`, the function `exp (t (X - x))` is integrable. -/
lemma integrable_exp_mul_sub (ht : t ∈ integrableExpSet X P) (x : ℝ) :
    Integrable (fun ω ↦ exp (t * (X ω - x))) P := by
  refine (ht.mul_const (exp (-(t * x)))).congr (Eventually.of_forall fun ω ↦ ?_)
  simp only [← exp_add]
  ring_nf

/-- For `t ∈ integrableExpSet X P`, the cumulant generating function is a shifted logarithmic
exponential moment: `cgf X P t = t x + log E[exp (t (X - x))]`. -/
lemma cgf_eq_mul_add_log_integral_exp_mul_sub [NeZero P] (ht : t ∈ integrableExpSet X P)
    (x : ℝ) : cgf X P t = t * x + log (∫ ω, exp (t * (X ω - x)) ∂P) := by
  have h_eq : ∫ ω, exp (t * (X ω - x)) ∂P = mgf X P t * exp (t * -x) := by
    simp_rw [← mgf_add_const, mgf, sub_eq_add_neg]
  rw [h_eq, log_mul (mgf_pos' (NeZero.ne P) ht).ne' (exp_pos _).ne', log_exp, cgf]
  ring

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

/-- The identity under the law `P.map X` has the exponential moments of `X` under `P`. -/
lemma integrableExpSet_id_map (hX : AEMeasurable X P) :
    integrableExpSet id (P.map X) = integrableExpSet X P := by
  ext t
  exact integrable_map_measure (by fun_prop) hX

/-- The identity under the law `P.map X` has the cumulant generating function of `X` under `P`:
the analogue of `ProbabilityTheory.mgf_id_map`. -/
lemma cgf_id_map (hX : AEMeasurable X P) : cgf id (P.map X) = cgf X P := by
  ext t
  rw [cgf, cgf, mgf_id_map hX]

end LMLExplore
