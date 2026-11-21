/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.MeasureTheory.Measure.Decomposition.RadonNikodym
import Statlib.ForMathlib.InformationTheory.KullbackLeibler.EIntegral

/-!
# The relative entropy under a domination, and the logarithm of an e-variable

Two bounds that turn a comparison of measures into a bound on an expected logarithm.

* If `μ ≤ ν.withDensity (exp ∘ g)`, the log-likelihood ratio of `μ` to `ν` is at most `g`, and the
  relative entropy `KL(μ ‖ ν)` is at most the expectation of `g` under `μ`. This bounds a relative
  entropy by a domination of measures, with no density computed.
* If `KL(Q ‖ P)` is finite and `X` has `P`-expectation at most `1`, as an e-variable for `P` does,
  the positive part of `log X` has a finite `Q`-expectation, so that the expected logarithm of `X`
  under `Q` is well defined in `EReal`. This is what allows the expected logarithm under a mixture
  `Q = ρ.bind κ` to be computed as an iterated integral.

## Main statements

* `InformationTheory.coe_klDiv_le_eintegral_of_le_withDensity`: for
  `μ ≤ ν.withDensity (exp ∘ g)`, `KL(μ ‖ ν) ≤ ∫ᵉ g ∂μ`.
* `InformationTheory.lintegral_toENNReal_log_ne_top_of_klDiv_ne_top`: for `KL(Q ‖ P) < ∞` and
  `∫⁻ X ∂P ≤ 1`, `∫⁻ (log X)⁺ ∂Q < ∞`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- The relative entropy is at most the expectation of an upper bound `g` on the log-likelihood
ratio, given as a domination `μ ≤ ν.withDensity (exp ∘ g)`. -/
theorem coe_klDiv_le_eintegral_of_le_withDensity {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {g : α → ℝ}
    (h : μ ≤ ν.withDensity fun x ↦ ENNReal.ofReal (Real.exp (g x))) :
    (klDiv μ ν : EReal) ≤ ∫ᵉ x, (g x : EReal) ∂μ := by
  have hac : μ ≪ ν :=
    (Measure.absolutelyContinuous_of_le h).trans (withDensity_absolutelyContinuous _ _)
  have hle := Measure.rnDeriv_le_of_le_withDensity h
  rw [coe_klDiv_eq_eintegral_llr_of_measure_eq hac (by simp)]
  refine eintegral_mono_ae ?_
  filter_upwards [hac.ae_le hle, Measure.rnDeriv_pos hac,
    hac.ae_le (Measure.rnDeriv_lt_top μ ν)] with x h1 h2 h3
  rw [llr, EReal.coe_le_coe_iff, Real.log_le_iff_le_exp (ENNReal.toReal_pos h2.ne' h3.ne)]
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le h1

/-- If `KL(Q ‖ P)` is finite and `X` has `P`-expectation at most `1`, then the positive part of
`log X` has a finite `Q`-expectation. -/
theorem lintegral_toENNReal_log_ne_top_of_klDiv_ne_top {P Q : Measure α}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (hQP : klDiv Q P ≠ ∞) {X : α → ℝ≥0∞}
    (hX : Measurable X) (hX1 : ∫⁻ x, X x ∂P ≤ 1) :
    ∫⁻ x, (ENNReal.log (X x)).toENNReal ∂Q ≠ ∞ := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hQP
  have h_pt : ∀ᵐ x ∂Q, (ENNReal.log (X x)).toENNReal ≤
      X x / Q.rnDeriv P x + ENNReal.ofReal (llr Q P x) := by
    filter_upwards [Measure.rnDeriv_pos hac, hac.ae_le (Measure.rnDeriv_lt_top Q P)] with x h0 h1
    exact ENNReal.toENNReal_log_le_div_add h0 h1.ne
  refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae h_pt)
  rw [lintegral_add_left (f := fun x ↦ X x / Q.rnDeriv P x) (hX.div (Q.measurable_rnDeriv P))]
  refine ENNReal.add_ne_top.mpr ⟨?_, hint.lintegral_lt_top.ne⟩
  -- under `P`, the density of `Q` cancels the division
  have h_eq : ∫⁻ x, X x / Q.rnDeriv P x ∂Q = ∫⁻ x, Q.rnDeriv P x * (X x / Q.rnDeriv P x) ∂P := by
    have h := lintegral_withDensity_eq_lintegral_mul P (Q.measurable_rnDeriv P)
      (hX.div (Q.measurable_rnDeriv P))
    rwa [Measure.withDensity_rnDeriv_eq Q P hac] at h
  rw [h_eq]
  exact ne_top_of_le_ne_top ENNReal.one_ne_top
    ((lintegral_mono fun x ↦ ENNReal.mul_div_le).trans hX1)

end InformationTheory
