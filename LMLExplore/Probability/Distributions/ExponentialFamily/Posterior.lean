/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.ConditionalProbability
public import LMLExplore.Probability.Distributions.ExponentialFamily.Basic
public import LMLExplore.Probability.Moments.Basic

/-!
# Posteriors of the natural parameter of an exponential family, and the Jeffreys prior

Let `ρ` be a measure on `𝓧` and `T : 𝓧 → ℝ` a statistic, with log-partition function
`ψ = cgf T ρ` and natural parameters `Θ`, the interior of `integrableExpSet T ρ`. After `s`
independent observations `x₁, …, x_s` from the member `ρ_θ = ρ.expFamily T θ` of the family, the
density of their joint law with respect to `ρ^{⊗ s}` is
`∏ᵢ exp (θ T(xᵢ) - ψ(θ)) = exp (θ S - s ψ(θ))`, with `S = ∑ᵢ T(xᵢ)` the sum of the statistics. It
depends on the observations only through `s` and `S`. For a prior `ν` on the natural parameter,
the posterior is therefore the probability measure proportional to `exp (θ S - s ψ(θ)) ν(dθ)` on
`Θ`, the conjugate update of [KKM13, Section 2]. It is defined for every measure `ν` on `ℝ`, which
may be infinite (an improper prior, such as Lebesgue measure): the posterior is a probability
measure when the normalizing constant `∫_Θ exp (θ S - s ψ(θ)) dν(θ)` is positive and finite, and
`0` otherwise. Mathlib's `ProbabilityTheory.posterior` is the posterior kernel of a finite prior,
determined only up to null sets of observations; the conjugate formula here is defined at every
value of the sufficient statistic `(s, S)` and for improper priors, as a sampling rule requires.

The Jeffreys prior of the family is `√ψ''(θ) dθ` on `Θ`, the square root of the Fisher
information of the natural parameter times Lebesgue measure [KKM13, Section 2]. It is
σ-finite but usually infinite: for the Gaussian family of variance `v`, `ψ'' = v` and the Jeffreys
prior is a constant multiple of Lebesgue measure.

These posteriors are the sampling laws of Thompson sampling for exponential families.

## Main definitions

* `MeasureTheory.Measure.expFamilyPosterior ρ T ν s S`: the posterior of the natural parameter for
  the prior `ν`, after `s` observations whose statistics sum to `S`.
* `MeasureTheory.Measure.jeffreysPrior ρ T`: the Jeffreys prior `√ψ''(θ) dθ` on `Θ`.

## Main statements

* `MeasureTheory.Measure.expFamilyPosterior_apply`: the posterior of a measurable set `B` is
  `∫_{Θ ∩ B} exp (θ S - s ψ(θ)) dν(θ) / ∫_Θ exp (θ S - s ψ(θ)) dν(θ)`.
* `MeasureTheory.Measure.isProbabilityMeasure_expFamilyPosterior`,
  `MeasureTheory.Measure.expFamilyPosterior_eq_zero_iff`: the posterior is a probability measure
  if the normalizing constant is positive and finite, and `0` otherwise;
  `MeasureTheory.Measure.isProbabilityMeasure_expFamilyPosterior_of_ne_zero`: a posterior that is
  not `0` is a probability measure.
* `MeasureTheory.Measure.expFamilyPosterior_smul`: the posterior does not change when the prior is
  multiplied by a positive finite constant.
* `MeasureTheory.Measure.measurable_expFamilyPosterior`: for an s-finite measure `ρ`, a measurable
  statistic and an s-finite prior, the posterior is a measurable function of `S`.

## References

* [KKM13] N. Korda, E. Kaufmann and R. Munos, *Thompson sampling for 1-dimensional exponential
  family bandits*, NeurIPS 2013.
-/

public section

open ProbabilityTheory Real Set

open scoped ENNReal

namespace MeasureTheory.Measure

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {ν : Measure ℝ}
  {s : ℕ} {S : ℝ}

/-- The posterior of the natural parameter of the exponential family of `ρ` and `T`, for the prior
`ν`, after `s` observations whose statistics sum to `S`: the measure
`exp (θ S - s ψ(θ)) ν(dθ)` with `ψ = cgf T ρ`, conditioned on the interior of the natural
parameters `integrableExpSet T ρ` (that is, restricted to it and normalized). It is a probability
measure if the normalizing constant is positive and finite
(`isProbabilityMeasure_expFamilyPosterior`) and `0` otherwise (`expFamilyPosterior_eq_zero_iff`).
-/
noncomputable def expFamilyPosterior (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (ν : Measure ℝ) (s : ℕ)
    (S : ℝ) : Measure ℝ :=
  (ν.withDensity fun θ ↦ ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ)))[|
    interior (integrableExpSet T ρ)]

/-- The defining equation of `expFamilyPosterior`. -/
lemma expFamilyPosterior_def (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (ν : Measure ℝ) (s : ℕ) (S : ℝ) :
    ρ.expFamilyPosterior T ν s S =
      (ν.withDensity fun θ ↦ ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ)))[|
        interior (integrableExpSet T ρ)] :=
  (rfl)

instance : IsZeroOrProbabilityMeasure (ρ.expFamilyPosterior T ν s S) := by
  rw [expFamilyPosterior_def]
  infer_instance

/-- The posterior of a measurable set `B` is the ratio
`∫_{Θ ∩ B} exp (θ S - s ψ(θ)) dν(θ) / ∫_Θ exp (θ S - s ψ(θ)) dν(θ)`, with `Θ` the interior of
`integrableExpSet T ρ`. -/
lemma expFamilyPosterior_apply {B : Set ℝ} (hB : MeasurableSet B) :
    ρ.expFamilyPosterior T ν s S B =
      (∫⁻ θ in interior (integrableExpSet T ρ), ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ)) ∂ν)⁻¹
        * ∫⁻ θ in interior (integrableExpSet T ρ) ∩ B,
          ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ)) ∂ν := by
  have hΘ : MeasurableSet (interior (integrableExpSet T ρ)) := isOpen_interior.measurableSet
  rw [expFamilyPosterior_def, cond_apply hΘ, withDensity_apply _ hΘ,
    withDensity_apply _ (hΘ.inter hB)]

/-- The posterior is a probability measure if its normalizing constant
`∫_Θ exp (θ S - s ψ(θ)) dν(θ)` is positive and finite. -/
lemma isProbabilityMeasure_expFamilyPosterior
    (h0 : ∫⁻ θ in interior (integrableExpSet T ρ),
      ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ)) ∂ν ≠ 0)
    (htop : ∫⁻ θ in interior (integrableExpSet T ρ),
      ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ)) ∂ν ≠ ∞) :
    IsProbabilityMeasure (ρ.expFamilyPosterior T ν s S) := by
  have hΘ : MeasurableSet (interior (integrableExpSet T ρ)) := isOpen_interior.measurableSet
  rw [expFamilyPosterior_def]
  exact cond_isProbabilityMeasure_of_finite (by rwa [withDensity_apply _ hΘ])
    (by rwa [withDensity_apply _ hΘ])

/-- A posterior that is not `0` is a probability measure. -/
lemma isProbabilityMeasure_expFamilyPosterior_of_ne_zero (h : ρ.expFamilyPosterior T ν s S ≠ 0) :
    IsProbabilityMeasure (ρ.expFamilyPosterior T ν s S) :=
  ⟨IsZeroOrProbabilityMeasure.measure_univ.resolve_left (by rwa [Measure.measure_univ_eq_zero])⟩

/-- The posterior is `0` exactly when its normalizing constant `∫_Θ exp (θ S - s ψ(θ)) dν(θ)` is
`0` or infinite, for example for an improper prior and too few observations. -/
lemma expFamilyPosterior_eq_zero_iff :
    ρ.expFamilyPosterior T ν s S = 0 ↔
      ∫⁻ θ in interior (integrableExpSet T ρ),
          ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ)) ∂ν = ∞ ∨
        ∫⁻ θ in interior (integrableExpSet T ρ),
          ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ)) ∂ν = 0 := by
  rw [expFamilyPosterior_def, cond_eq_zero,
    withDensity_apply _ isOpen_interior.measurableSet]

/-- The posterior does not depend on the normalization of the prior: multiplying the prior by a
constant `c ∉ {0, ∞}` does not change the posterior. -/
lemma expFamilyPosterior_smul {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    ρ.expFamilyPosterior T (c • ν) s S = ρ.expFamilyPosterior T ν s S := by
  rw [expFamilyPosterior_def, expFamilyPosterior_def, withDensity_smul_measure,
    cond_smul _ _ hc0 hc]

/-- For an s-finite measure `ρ`, an almost-everywhere measurable statistic `T` and an s-finite
prior `ν`, the posterior after `s` observations is a measurable function of the sum `S` of their
statistics. -/
@[fun_prop]
lemma measurable_expFamilyPosterior [SFinite ρ] (hT : AEMeasurable T ρ) (ν : Measure ℝ)
    [SFinite ν] (s : ℕ) :
    Measurable fun S ↦ ρ.expFamilyPosterior T ν s S := by
  refine Measure.measurable_of_measurable_coe _ fun B hB ↦ ?_
  simp_rw [expFamilyPosterior_apply hB]
  have hf : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal (exp (p.2 * p.1 - s * cgf T ρ p.2)) := by
    have := measurable_cgf hT
    fun_prop
  exact (hf.lintegral_prod_right' (ν := ν.restrict _)).inv.mul
    (hf.lintegral_prod_right' (ν := ν.restrict _))

/-- The Jeffreys prior of the exponential family of `ρ` and `T`: the measure `√ψ''(θ) dθ` on the
interior of the natural parameters `integrableExpSet T ρ`, with `ψ = cgf T ρ` and `ψ''(θ)` the
variance of `T` under the member of natural parameter `θ`, the Fisher information of the natural
parameter [KKM13, Section 2]. It is σ-finite and usually infinite. -/
noncomputable def jeffreysPrior (ρ : Measure 𝓧) (T : 𝓧 → ℝ) : Measure ℝ :=
  (volume.restrict (interior (integrableExpSet T ρ))).withDensity
    fun θ ↦ ENNReal.ofReal √(iteratedDeriv 2 (cgf T ρ) θ)

/-- The defining equation of `jeffreysPrior`. -/
lemma jeffreysPrior_def (ρ : Measure 𝓧) (T : 𝓧 → ℝ) :
    ρ.jeffreysPrior T = (volume.restrict (interior (integrableExpSet T ρ))).withDensity
      fun θ ↦ ENNReal.ofReal √(iteratedDeriv 2 (cgf T ρ) θ) :=
  (rfl)

instance : SigmaFinite (ρ.jeffreysPrior T) := by
  rw [jeffreysPrior_def]
  infer_instance

end MeasureTheory.Measure
