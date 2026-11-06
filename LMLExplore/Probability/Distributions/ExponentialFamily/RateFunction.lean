/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Distributions.ExponentialFamily.Mean
public import LMLExplore.Probability.Moments.RateFunction

/-!
# The rate function of the statistic of an exponential family

Let `ρ` be a measure on `𝓧` and `T : 𝓧 → ℝ` a statistic, with log-partition function
`ψ = cgf T ρ`. Under a member `ρ_η` of their exponential family, the cumulant generating function
of `T` is `t ↦ ψ(η + t) - ψ(η)`, so the Cramér rate function of `T` under `ρ_η` at a level `x`
is a supremum over the natural parameters `η + t`. At a mean `x` of the family the supremum is
attained at the natural parameter `η(x)` of `x`, and its value is the Kullback–Leibler divergence
`KL(ρ_η(x), ρ_η)`: the rate function of `T` under `ρ_η` at `x` is the divergence from the member
of mean `x` to `ρ_η`. In the mean parametrization, the rate function of `T` under the member of
mean `μ` is `d(x, μ)` at every mean `x`. This is the exponent of the Chernoff bounds for the
empirical means of the statistic, and it extends `d(·, μ)` to every real level.

## Main statements

* `LMLExplore.rateFunction_expFamily`: the rate function of `T` under `ρ_η` at a mean `x` of the
  family is `KL(ρ_η(x), ρ_η)`.
* `LMLExplore.rateFunction_expFamily_natParam`: the rate function of `T` under the member of mean
  `μ` at a mean `x` is `d(x, μ)`.
-/

public section

open MeasureTheory Measure ProbabilityTheory InformationTheory Set

open scoped ENNReal

namespace LMLExplore

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {η x μ : ℝ}

/-- The rate function of the statistic `T` under the member `ρ_η` of its exponential family, at a
mean `x` of the family, is the Kullback–Leibler divergence `KL(ρ_η(x), ρ_η)` from the member of
mean `x`. -/
theorem rateFunction_expFamily (hη : η ∈ integrableExpSet T ρ) (hx : x ∈ ρ.expFamilyMeans T) :
    rateFunction T (ρ.expFamily T η) x =
      klDiv (ρ.expFamily T (ρ.natParam T x)) (ρ.expFamily T η) := by
  have hηx := natParam_mem_interior_integrableExpSet hx
  have h_kl := toReal_klDiv_expFamily hηx hη
  rw [deriv_cgf_natParam hx] at h_kl
  rw [← ENNReal.ofReal_toReal (klDiv_ne_top (expFamily_absolutelyContinuous_expFamily _ hη)
    (integrable_llr_expFamily hηx hη)), h_kl]
  refine le_antisymm ((rateFunction_le_iff).2 fun t ht ↦ ?_) ?_
  · -- `ψ(η + t) ≥ ψ(η(x)) + x (η + t - η(x))`: the divergence from `ρ_η(x)` to `ρ_(η + t)` is
    -- nonnegative.
    rw [integrableExpSet_expFamily hη, mem_preimage] at ht
    have h_nonneg :
        0 ≤ cgf T ρ (η + t) - cgf T ρ (ρ.natParam T x) - x * (η + t - ρ.natParam T x) := by
      have h := toReal_klDiv_expFamily hηx ht
      rw [deriv_cgf_natParam hx] at h
      exact h ▸ ENNReal.toReal_nonneg
    rw [cgf_expFamily hη ht]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · -- The supremum is attained at the natural parameter `η(x)`.
    have ht : ρ.natParam T x - η ∈ integrableExpSet T (ρ.expFamily T η) := by
      rw [integrableExpSet_expFamily hη, mem_preimage, add_sub_cancel]
      exact interior_subset hηx
    refine (le_of_eq ?_).trans (ofReal_le_rateFunction ht x)
    rw [cgf_expFamily hη (by rw [add_sub_cancel]; exact interior_subset hηx), add_sub_cancel]
    congr 1
    ring

/-- The rate function of the statistic `T` under the member of mean `μ` of its exponential family
is the divergence `d(x, μ)` at every mean `x` of the family. -/
theorem rateFunction_expFamily_natParam (hx : x ∈ ρ.expFamilyMeans T)
    (hμ : μ ∈ ρ.expFamilyMeans T) :
    rateFunction T (ρ.expFamily T (ρ.natParam T μ)) x = ENNReal.ofReal (ρ.expFamilyDiv T x μ) := by
  rw [rateFunction_expFamily (interior_subset (natParam_mem_interior_integrableExpSet hμ)) hx,
    klDiv_expFamily_natParam hx hμ]

end LMLExplore
