/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Martingale.TestSupermartingale
public import LMLExplore.MeasureTheory.MeasurableSpace.Constructions
public import LMLExplore.Probability.Kernel.CondLaw
public import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Likelihood ratios of sequential predictors

Let `X k` be observations in a measurable space `𝓧`, each `ℱ (k + 1)`-measurable for a filtration
`ℱ`, and let `κ k ω` be a conditional law of `X k` given the past `ℱ k` under `P`
(`ProbabilityTheory.HasCondLaw`). A *sequential predictor* announces, before round `k`, a
prediction of `X k` with density `r k ω` with respect to `κ k ω`: `r k` is measurable for `ℱ k`
and the σ-algebra of `𝓧` jointly, and `∫⁻ x, r k ω x ∂(κ k ω) ≤ 1`. Its likelihood ratio against
the true conditional laws, `∏ k < n, r k ω (X k ω)`, is a test supermartingale for `P`, and a test
martingale when the predictions are probability measures absolutely continuous with respect to the
conditional laws [RW, §3.7, §7.5].

No independence, no identical distribution and no dominating measure are assumed: the observations
may follow any conditional law given any filtration, and the observation space is arbitrary. When
the predictions are `ℱ k`-measurable sub-Markov kernels `ρ k` and the conditional laws are finite
kernels `κ k` on a countably generated space, the density is Mathlib's `Kernel.rnDeriv (ρ k) (κ k)`.
The statements apply to every predictor with such densities, for instance plug-in predictors or
mixtures over a prior, whose predictions are the posterior predictive laws. The case of a finite
alphabet and observations independent of the past with one law `ν` is
`LMLExplore.supermartingale_predictorLikelihoodRatio`.

## Main statements

* `ProbabilityTheory.HasCondLaw.isCondEVar_comp`: the value `r ω (X ω)` of a sub-probability
  density at an observation of conditional law `κ` is a conditional e-variable.
* `ProbabilityTheory.isTestSupermartingale_prod_of_hasCondLaw`,
  `ProbabilityTheory.isTestMartingale_prod_of_hasCondLaw`: the likelihood ratio of a sequential
  predictor is a test supermartingale, and a test martingale for probability predictions.
* `ProbabilityTheory.isTestSupermartingale_prod_rnDeriv`,
  `ProbabilityTheory.isTestMartingale_prod_rnDeriv`: the same for predictions given by kernels,
  with the densities `Kernel.rnDeriv`.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614.
-/

public section

open MeasureTheory Set Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} {m mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {P : Measure Ω}

section OneStep

variable {X : Ω → 𝓧} {κ : Ω → Measure 𝓧} {r : Ω → 𝓧 → ℝ≥0∞}

/-- **A sub-probability density at the observation is a conditional e-variable.** If `κ` is a
conditional law of `X` given `m` under `P`, and `r ω` is a density of total mass at most `1` with
respect to `κ ω` for almost every `ω`, jointly measurable for `m` and `𝓧`, then `r ω (X ω)` is a
conditional e-variable given `m` for `P`. -/
theorem HasCondLaw.isCondEVar_comp (h : HasCondLaw X κ m P) (hm : m ≤ mΩ) (hX : Measurable X)
    (hr : Measurable[m.prod m𝓧] (Function.uncurry r))
    (hr1 : ∀ᵐ ω ∂P, ∫⁻ x, r ω x ∂(κ ω) ≤ 1) :
    IsCondEVar (fun ω ↦ r ω (X ω)) m {P} := by
  refine ⟨hr.comp_prodMk_of_le hm hX, ?_⟩
  rintro _ rfl s hs
  rw [h.setLIntegral_comp hm hr hs, ← setLIntegral_one]
  exact lintegral_mono_ae (ae_restrict_of_ae hr1)

/-- **A probability density at the observation is an exact conditional e-variable.** If `κ` is a
conditional law of `X` given `m` under `P`, and `r ω` is a probability density with respect to
`κ ω` for almost every `ω`, jointly measurable for `m` and `𝓧`, then `r ω (X ω)` is an exact
conditional e-variable given `m` for `P`. -/
theorem HasCondLaw.isExactCondEVar_comp (h : HasCondLaw X κ m P) (hm : m ≤ mΩ)
    (hX : Measurable X) (hr : Measurable[m.prod m𝓧] (Function.uncurry r))
    (hr1 : ∀ᵐ ω ∂P, ∫⁻ x, r ω x ∂(κ ω) = 1) :
    IsExactCondEVar (fun ω ↦ r ω (X ω)) m {P} := by
  refine ⟨hr.comp_prodMk_of_le hm hX, ?_⟩
  rintro _ rfl s hs
  rw [h.setLIntegral_comp hm hr hs, ← setLIntegral_one]
  exact lintegral_congr_ae (ae_restrict_of_ae hr1)

end OneStep

section Predictor

variable {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → 𝓧} {κ : ℕ → Ω → Measure 𝓧}
  {r : ℕ → Ω → 𝓧 → ℝ≥0∞}

/-- **The likelihood ratio of a sequential predictor is a test supermartingale** [RW, §7.5]. Let
`X k` be `ℱ (k + 1)`-measurable with conditional law `κ k` given `ℱ k` under the probability
measure `P`, and let the prediction of round `k` have the density `r k ω` with respect to `κ k ω`,
jointly measurable for `ℱ k` and `𝓧`, of total mass at most `1` for almost every `ω`. Then
`∏ k < n, r k ω (X k ω)` is a test supermartingale for `P`. -/
theorem isTestSupermartingale_prod_of_hasCondLaw [IsProbabilityMeasure P]
    (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) (hκ : ∀ k, HasCondLaw (X k) (κ k) (ℱ k) P)
    (hr : ∀ k, Measurable[(ℱ k).prod m𝓧] (Function.uncurry (r k)))
    (hr1 : ∀ k, ∀ᵐ ω ∂P, ∫⁻ x, r k ω x ∂(κ k ω) ≤ 1) :
    IsTestSupermartingale (fun n ω ↦ ∏ k ∈ range n, r k ω (X k ω)) ℱ {P} :=
  isTestSupermartingale_prod (by simpa) (fun k ↦ (hr k).comp_prodMk_of_le (ℱ.mono k.le_succ) (hX k))
    fun k ↦ (hκ k).isCondEVar_comp (ℱ.le k) ((hX k).mono (ℱ.le _) le_rfl) (hr k) (hr1 k)

/-- **The likelihood ratio of a probability predictor is a test martingale** [RW, §7.5]. Let `X k`
be `ℱ (k + 1)`-measurable with conditional law `κ k` given `ℱ k` under the probability measure
`P`, and let the prediction of round `k` have the probability density `r k ω` with respect to
`κ k ω` for almost every `ω`, jointly measurable for `ℱ k` and `𝓧`. Then
`∏ k < n, r k ω (X k ω)` is a test martingale for `P`. -/
theorem isTestMartingale_prod_of_hasCondLaw [IsProbabilityMeasure P]
    (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) (hκ : ∀ k, HasCondLaw (X k) (κ k) (ℱ k) P)
    (hr : ∀ k, Measurable[(ℱ k).prod m𝓧] (Function.uncurry (r k)))
    (hr1 : ∀ k, ∀ᵐ ω ∂P, ∫⁻ x, r k ω x ∂(κ k ω) = 1) :
    IsTestMartingale (fun n ω ↦ ∏ k ∈ range n, r k ω (X k ω)) ℱ {P} :=
  isTestMartingale_prod (by simpa) (fun k ↦ (hr k).comp_prodMk_of_le (ℱ.mono k.le_succ) (hX k))
    fun k ↦ (hκ k).isExactCondEVar_comp (ℱ.le k) ((hX k).mono (ℱ.le _) le_rfl) (hr k) (hr1 k)

end Predictor

section Kernel

open ProbabilityTheory.Kernel

variable {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → 𝓧} [MeasurableSpace.CountableOrCountablyGenerated Ω 𝓧]
  {κ ρ : (k : ℕ) → @Kernel Ω 𝓧 (ℱ k) m𝓧} [∀ k, IsFiniteKernel (κ k)] [∀ k, IsFiniteKernel (ρ k)]

/-- **The likelihood ratio of a kernel predictor is a test supermartingale.** Let `X k` be
`ℱ (k + 1)`-measurable with conditional law the finite kernel `κ k` given `ℱ k` under the
probability measure `P`, and let the prediction of round `k` be the `ℱ k`-measurable finite kernel
`ρ k`, of total mass at most `1` almost surely. Then `∏ k < n, (ρ k).rnDeriv (κ k) ω (X k ω)` is a
test supermartingale for `P`. -/
theorem isTestSupermartingale_prod_rnDeriv [IsProbabilityMeasure P]
    (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) (hκ : ∀ k, HasCondLaw (X k) (κ k) (ℱ k) P)
    (hρ : ∀ k, ∀ᵐ ω ∂P, ρ k ω univ ≤ 1) :
    IsTestSupermartingale (fun n ω ↦ ∏ k ∈ range n, (ρ k).rnDeriv (κ k) ω (X k ω)) ℱ {P} :=
  isTestSupermartingale_prod_of_hasCondLaw hX hκ (fun k ↦ measurable_rnDeriv (ρ k) (κ k))
    fun k ↦ (hρ k).mono fun ω hω ↦ by
      rw [← setLIntegral_univ]
      exact setLIntegral_rnDeriv_le MeasurableSet.univ |>.trans hω

/-- **The likelihood ratio of a kernel predictor is a test martingale.** Let `X k` be
`ℱ (k + 1)`-measurable with conditional law the finite kernel `κ k` given `ℱ k` under the
probability measure `P`, and let the prediction of round `k` be the `ℱ k`-measurable finite kernel
`ρ k`, almost surely a probability measure absolutely continuous with respect to `κ k`. Then
`∏ k < n, (ρ k).rnDeriv (κ k) ω (X k ω)` is a test martingale for `P`. -/
theorem isTestMartingale_prod_rnDeriv [IsProbabilityMeasure P]
    (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) (hκ : ∀ k, HasCondLaw (X k) (κ k) (ℱ k) P)
    (hρ : ∀ k, ∀ᵐ ω ∂P, ρ k ω univ = 1) (hρκ : ∀ k, ∀ᵐ ω ∂P, ρ k ω ≪ κ k ω) :
    IsTestMartingale (fun n ω ↦ ∏ k ∈ range n, (ρ k).rnDeriv (κ k) ω (X k ω)) ℱ {P} :=
  isTestMartingale_prod_of_hasCondLaw hX hκ (fun k ↦ measurable_rnDeriv (ρ k) (κ k))
    fun k ↦ ((hρ k).and (hρκ k)).mono fun _ hω ↦ (lintegral_rnDeriv hω.2).trans hω.1

end Kernel

end ProbabilityTheory
