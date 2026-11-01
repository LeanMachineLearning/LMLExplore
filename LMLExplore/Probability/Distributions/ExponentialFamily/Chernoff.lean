/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Distributions.ExponentialFamily.Mean

/-!
# Cramér–Chernoff bounds for exponential families

Let `ρ` be a measure on a measurable space `𝓧` and `T : 𝓧 → ℝ` a statistic, with log-partition
function `ψ = cgf T ρ`, and let `X i`, `i ∈ s`, be independent random variables whose law is the
member `ρ_η(μ)` of mean `μ` of the exponential family of `ρ` and `T`. For a mean `x ≥ μ` of the
family, the probability that the empirical mean of the statistics `T (X i)` is at least `x` decays
exponentially in the number `#s` of variables, at the rate given by the Kullback–Leibler divergence
`d(x, μ) = KL(ρ_η(x), ρ_η(μ))`: `P(#s * x ≤ ∑ i ∈ s, T (X i)) ≤ exp (-(#s * d(x, μ)))`, and
symmetrically for the lower tail. For a natural exponential family on `ℝ` (`T = id`), these are
bounds on the sums `∑ i ∈ s, X i` themselves.

The bound is the Chernoff bound `P(a ≤ S) ≤ exp (-t a + cgf S t)` applied with the optimal
parameter `t = η(x) - η(μ)`. The cumulant generating function of `T` under `ρ_η` is
`t ↦ ψ(η + t) - ψ(η)`, so that of a sum of `n` independent copies is `t ↦ n (ψ(η + t) - ψ(η))`
(`ProbabilityTheory.iIndepFun.cgf_sum_of_hasLaw_expFamily`), and at the optimal parameter the
exponent is `-n d(x, μ)`. No assumption on `ρ` or `T` is needed: when `T` is `ρ`-almost everywhere
constant, its only mean is `μ = x` and the bounds are trivial.

These bounds control the deviations of the empirical means of the arms of a bandit whose reward
distributions belong to an exponential family. For Bernoulli laws, `d` is the binary relative
entropy; the bounds in that form, `LMLExplore.measureReal_sum_ge_le_exp_klBerReal` and
`LMLExplore.measureReal_sum_le_le_exp_klBerReal`, hold more generally for random variables with
values in `[0, 1]`.

## Main statements

* `ProbabilityTheory.iIndepFun.measureReal_sum_ge_le_exp_expFamilyDiv`: the upper tail
  `P(#s * x ≤ ∑ i ∈ s, T (X i)) ≤ exp (-(#s * d(x, μ)))` for means `μ ≤ x` of the family.
* `ProbabilityTheory.iIndepFun.measureReal_sum_le_le_exp_expFamilyDiv`: the lower tail
  `P(∑ i ∈ s, T (X i) ≤ #s * x) ≤ exp (-(#s * d(x, μ)))` for means `x ≤ μ` of the family.

## References

* S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford University Press,
  2013, Section 2.2 (the Cramér–Chernoff method).
* A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, where these bounds control the empirical means of exponential-family arms.
-/

public section

open MeasureTheory Real Finset

namespace ProbabilityTheory

variable {Ω ι 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {P : Measure Ω}
  {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {X : ι → Ω → 𝓧} {s : Finset ι} {μ x : ℝ}

/-! ### Cramér–Chernoff bounds -/

/-- At the parameter `t = η(x) - η(μ)`, the sum of the statistics of independent random variables
with law `ρ_η(μ)` has an exponential moment of order `t`, and the exponent
`-t (#s x) + cgf (∑ i ∈ s, T (X i)) t` of the Chernoff bound is `-(#s d(x, μ))`. -/
private lemma integrable_and_neg_mul_add_cgf_sum_natParam (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, HasLaw (X i) (ρ.expFamily T (ρ.natParam T μ)) P)
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) :
    Integrable (fun ω ↦ exp ((ρ.natParam T x - ρ.natParam T μ) * ∑ i ∈ s, T (X i ω))) P ∧
      -(ρ.natParam T x - ρ.natParam T μ) * (#s * x) +
        cgf (fun ω ↦ ∑ i ∈ s, T (X i ω)) P (ρ.natParam T x - ρ.natParam T μ) =
          -(#s * ρ.expFamilyDiv T x μ) := by
  have hη' := Measure.natParam_mem_interior_integrableExpSet hμ
  have hT : AEMeasurable T ρ := aemeasurable_of_mem_interior_integrableExpSet hη'
  have hη := interior_subset hη'
  have hηt : ρ.natParam T μ + (ρ.natParam T x - ρ.natParam T μ) ∈ integrableExpSet T ρ := by
    rw [add_sub_cancel]
    exact interior_subset (Measure.natParam_mem_interior_integrableExpSet hx)
  refine ⟨h_indep.integrable_exp_mul_sum_of_hasLaw_expFamily hT hX hη hηt, ?_⟩
  rw [h_indep.cgf_sum_of_hasLaw_expFamily hT hX hη hηt, add_sub_cancel,
    Measure.expFamilyDiv_def]
  ring

/-- **Cramér–Chernoff bound for an exponential family, upper tail.** For independent random
variables `X i`, `i ∈ s`, with law the member `ρ_η(μ)` of mean `μ` of the exponential family of
`ρ` and `T`, and a mean `x ≥ μ` of the family,
`P(#s * x ≤ ∑ i ∈ s, T (X i)) ≤ exp (-(#s * d(x, μ)))`, where `d(x, μ) = KL(ρ_η(x), ρ_η(μ))`. -/
theorem iIndepFun.measureReal_sum_ge_le_exp_expFamilyDiv (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, HasLaw (X i) (ρ.expFamily T (ρ.natParam T μ)) P)
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) (hμx : μ ≤ x) :
    P.real {ω | #s * x ≤ ∑ i ∈ s, T (X i ω)} ≤ exp (-(#s * ρ.expFamilyDiv T x μ)) := by
  have := h_indep.isProbabilityMeasure
  obtain ⟨h_int, h_exp⟩ := integrable_and_neg_mul_add_cgf_sum_natParam h_indep hX hμ hx
  have h := measure_ge_le_exp_cgf (#s * x)
    (sub_nonneg.2 (Measure.monotoneOn_natParam hμ hx hμx)) h_int
  rwa [h_exp] at h

/-- **Cramér–Chernoff bound for an exponential family, lower tail.** For independent random
variables `X i`, `i ∈ s`, with law the member `ρ_η(μ)` of mean `μ` of the exponential family of
`ρ` and `T`, and a mean `x ≤ μ` of the family,
`P(∑ i ∈ s, T (X i) ≤ #s * x) ≤ exp (-(#s * d(x, μ)))`, where `d(x, μ) = KL(ρ_η(x), ρ_η(μ))`. -/
theorem iIndepFun.measureReal_sum_le_le_exp_expFamilyDiv (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, HasLaw (X i) (ρ.expFamily T (ρ.natParam T μ)) P)
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) (hxμ : x ≤ μ) :
    P.real {ω | ∑ i ∈ s, T (X i ω) ≤ #s * x} ≤ exp (-(#s * ρ.expFamilyDiv T x μ)) := by
  have := h_indep.isProbabilityMeasure
  obtain ⟨h_int, h_exp⟩ := integrable_and_neg_mul_add_cgf_sum_natParam h_indep hX hμ hx
  have h := measure_le_le_exp_cgf (#s * x)
    (sub_nonpos.2 (Measure.monotoneOn_natParam hx hμ hxμ)) h_int
  rwa [h_exp] at h

end ProbabilityTheory
