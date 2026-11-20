/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Martingale.TestSupermartingale
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Mixtures of nonnegative supermartingales

A mixture `n ↦ ∫ l, f l n ∂π` of a measurable family of nonnegative supermartingales `f l` with
respect to a measure `π` on the parameter space is a supermartingale, as soon as
`l ↦ ∫ f l 0 ∂μ` is `π`-integrable (Tonelli's theorem). This is the *method of mixtures* step in
the proof of self-normalized concentration bounds [LS, Lemma 20.3], where the mixture over a
Gaussian law of the exponential supermartingales `exp (⟪x, S_t⟫ - ‖x‖²_{V_t} / 2)` is bounded
with Ville's inequality.

## Main statements

* `LMLExplore.supermartingale_integral_of_integrable`: the general statement, for an s-finite
  mixing measure `π` and `l ↦ ∫ f l 0 ∂μ` integrable.
* `LMLExplore.supermartingale_integral`: the case of a finite mixing measure and initial
  expectations bounded uniformly in `l`; it contains [LS, Lemma 20.3], where `π` is a probability
  measure and every `f l 0` has expectation at most `1`.

## Implementation notes

The statements are adapted from `MeasureTheory.supermartingale_integral_of_integrable` and
`MeasureTheory.supermartingale_integral` in
`LeanMachineLearning/ForMathlib/Probability/Martingale/Mixture.lean` of the LMLPapers project
(https://github.com/LeanMachineLearning/LMLPapers). The almost sure convergence corollary proved
there is not included. The general statement is derived from the mixture of `ℝ≥0∞`-valued
supermartingales, `ProbabilityTheory.isENNSupermartingale_lintegral`, applied to the processes
`ENNReal.ofReal ∘ f l`: integrability of the initial expectations makes the mixture finite, and
its real values are the mixture of the `f l`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 20.3.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LMLExplore

variable {Ω L : Type*} {mΩ : MeasurableSpace Ω} {mL : MeasurableSpace L} {μ : Measure Ω}
  {π : Measure L}

/-- **Mixtures of supermartingales.** Let `(f l)_l` be a family of nonnegative supermartingales
such that `(l, ω) ↦ f l n ω` is `mL ⊗ ℱ n`-measurable for each `n`, and `π` an s-finite measure
on the parameter space such that `l ↦ ∫ ω, f l 0 ω ∂μ` is `π`-integrable. Then the mixture
`n ↦ ∫ l, f l n ∂π` is a supermartingale. -/
lemma supermartingale_integral_of_integrable [IsFiniteMeasure μ] [SFinite π]
    {ℱ : Filtration ℕ mΩ} {f : L → ℕ → Ω → ℝ} (hf : ∀ l, Supermartingale (f l) ℱ μ)
    (hf_nonneg : ∀ l n ω, 0 ≤ f l n ω)
    (hmeas : ∀ n, Measurable[mL.prod (ℱ n)] (fun p : L × Ω ↦ f p.1 n p.2))
    (hint : Integrable (fun l ↦ ∫ ω, f l 0 ω ∂μ) π) :
    Supermartingale (fun n ω ↦ ∫ l, f l n ω ∂π) ℱ μ := by
  -- The mixture `G` of the `ℝ≥0∞`-valued supermartingales `ENNReal.ofReal ∘ f l` is an
  -- `ℝ≥0∞`-valued supermartingale with finite initial expectation, whose real values are the
  -- mixture of the `f l`.
  set G : ℕ → Ω → ℝ≥0∞ := fun n ω ↦ ∫⁻ l, ENNReal.ofReal (f l n ω) ∂π
  have hG : IsENNSupermartingale G ℱ {μ} :=
    isENNSupermartingale_lintegral (fun _ hP ↦ hP ▸ inferInstance)
      (fun n ↦ (hmeas n).ennreal_ofReal)
      fun l ↦ (hf l).isENNSupermartingale_ofReal fun n ↦ ae_of_all _ (hf_nonneg l n)
  have hG0 : ∫⁻ ω, G 0 ω ∂μ ≠ ∞ := by
    have hm : Measurable (fun p : L × Ω ↦ f p.1 0 p.2) :=
      (hmeas 0).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le 0)) le_rfl
    rw [lintegral_lintegral_swap (hm.comp measurable_swap).ennreal_ofReal.aemeasurable]
    simp_rw [← ofReal_integral_eq_lintegral_ofReal ((hf _).integrable 0)
      (ae_of_all _ (hf_nonneg _ 0))]
    exact hint.lintegral_lt_top.ne
  have hGf : (fun n ω ↦ ∫ l, f l n ω ∂π) = fun n ω ↦ (G n ω).toReal := by
    ext n ω
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun l ↦ hf_nonneg l n ω)
      ((hmeas n).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le n)) le_rfl
        |>.comp measurable_prodMk_right).aestronglyMeasurable
  rw [hGf]
  exact hG.supermartingale_toReal (Set.mem_singleton μ) hG0

/-- **Mixtures of supermartingales**, for a finite mixing measure: if `(f l)_l` is a family of
nonnegative supermartingales such that `(l, ω) ↦ f l n ω` is `mL ⊗ ℱ n`-measurable for each `n`
and `∫ ω, f l 0 ω ∂μ ≤ C` for all `l`, then `n ↦ ∫ l, f l n ∂π` is a supermartingale. -/
lemma supermartingale_integral [IsFiniteMeasure μ] [IsFiniteMeasure π]
    {ℱ : Filtration ℕ mΩ} {f : L → ℕ → Ω → ℝ} (hf : ∀ l, Supermartingale (f l) ℱ μ)
    (hf_nonneg : ∀ l n ω, 0 ≤ f l n ω)
    (hmeas : ∀ n, Measurable[mL.prod (ℱ n)] (fun p : L × Ω ↦ f p.1 n p.2))
    (hbdd : ∃ C, ∀ l, ∫ ω, f l 0 ω ∂μ ≤ C) :
    Supermartingale (fun n ω ↦ ∫ l, f l n ω ∂π) ℱ μ := by
  obtain ⟨C, hC⟩ := hbdd
  refine supermartingale_integral_of_integrable hf hf_nonneg hmeas ?_
  have hm : Measurable (fun p : L × Ω ↦ f p.1 0 p.2) :=
    (hmeas 0).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le 0)) le_rfl
  refine Integrable.of_bound (C := C)
    hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable (ae_of_all _ fun l ↦ ?_)
  rw [Real.norm_of_nonneg (integral_nonneg (hf_nonneg l 0))]
  exact hC l

end LMLExplore
