/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Distributions.ExponentialFamily.Mean
public import LMLExplore.Probability.Moments.MGF.Dominated
import LMLExplore.Probability.Distributions.ExponentialFamily.RateFunction
import LMLExplore.Probability.LargeDeviations.Chernoff

/-!
# Cramér–Chernoff bounds under domination by an exponential family

Let `ρ` be a measure on a measurable space `𝓧` and `T : 𝓧 → ℝ` a statistic, with log-partition
function `ψ = cgf T ρ`, and let `ρ_η(μ)` be the member of mean `μ` of their exponential family. A
real random variable `X` is dominated by `ρ_η(μ)` on `Set.Ici 0` if
`E[exp (t X)] ≤ E_{ρ_η(μ)}[exp (t T)]` for every `t ≥ 0`
(`LMLExplore.MGFDominatedOn X P T ρ_η(μ) (Set.Ici 0)`), and on `Set.Iic 0` if the same holds for
every `t ≤ 0`.

For independent random variables `X i`, `i ∈ s`, dominated by `ρ_η(μ)` on `Set.Ici 0` and a mean
`x ≥ μ` of
the family, the probability that the empirical mean of the `X i` is at least `x` decays
exponentially in the number `#s` of variables, at the rate given by the Kullback–Leibler divergence
`d(x, μ) = KL(ρ_η(x), ρ_η(μ))`: `P(#s * x ≤ ∑ i ∈ s, X i) ≤ exp (-(#s * d(x, μ)))`, and
symmetrically for the lower tail of variables dominated on `Set.Iic 0`. The statistics `T (Y i)` of
independent observations `Y i` with law `ρ_η(μ)` are dominated on every set, which gives these
bounds for the sums `∑ i ∈ s, T (Y i)`; for a natural exponential family on `ℝ` (`T = id`), these
are bounds on the sums `∑ i ∈ s, Y i` themselves.

These bounds are the Cramér–Chernoff bounds with the rate function
(`ProbabilityTheory.iIndepFun.measureReal_sum_ge_le_exp_of_le_rateFunction` and
`ProbabilityTheory.iIndepFun.measureReal_sum_le_le_exp_of_le_rateFunction`) at the means of the
family, where the rate function of `T` under `ρ_η(μ)` is `d(·, μ)`
(`LMLExplore.rateFunction_expFamily_natParam`). No assumption on `ρ` or `T` is needed: when `T` is
`ρ`-almost everywhere constant, its only mean is `μ = x` and the bounds are trivial.

These bounds control the deviations of the empirical means of the arms of a bandit whose reward
distributions are dominated by members of an exponential family. For Bernoulli laws, `d` is the
binary relative entropy (`LMLExplore.expFamilyDiv_bernoulliMeasure_sigmoid`), and random variables
with values in `[0, 1]` are dominated by Bernoulli laws, which gives the bounds
`LMLExplore.measureReal_sum_ge_le_exp_klBerReal` and
`LMLExplore.measureReal_sum_le_le_exp_klBerReal`.

## Main statements

* `ProbabilityTheory.iIndepFun.measureReal_sum_ge_le_exp_expFamilyDiv`: the upper tail
  `P(#s * x ≤ ∑ i ∈ s, X i) ≤ exp (-(#s * d(x, μ)))` for variables dominated by the member of
  mean `μ` on `Set.Ici 0` and means `μ ≤ x` of the family.
* `ProbabilityTheory.iIndepFun.measureReal_sum_le_le_exp_expFamilyDiv`: the lower tail
  `P(∑ i ∈ s, X i ≤ #s * x) ≤ exp (-(#s * d(x, μ)))` for variables dominated by the member of
  mean `μ` on `Set.Iic 0` and means `x ≤ μ` of the family.
* `ProbabilityTheory.iIndepFun.measureReal_sum_ge_le_exp_expFamilyDiv_of_hasLaw`,
  `ProbabilityTheory.iIndepFun.measureReal_sum_le_le_exp_expFamilyDiv_of_hasLaw`: the same bounds
  for the statistics `T (Y i)` of independent observations `Y i` with law the member of mean `μ`.

## References

* S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford University Press,
  2013, Section 2.2 (the Cramér–Chernoff method).
* A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, where these bounds control the empirical means of exponential-family arms.
-/

public section

open MeasureTheory Real Finset LMLExplore

namespace ProbabilityTheory

variable {Ω ι 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {P : Measure Ω}
  {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {X : ι → Ω → ℝ} {Y : ι → Ω → 𝓧} {s : Finset ι} {μ x : ℝ}

/-! ### Cramér–Chernoff bounds -/

/-- The family of the zero measure has the single mean `0`. -/
private lemma eq_zero_of_mem_expFamilyMeans_zero_measure
    (hx : x ∈ (0 : Measure 𝓧).expFamilyMeans T) : x = 0 := by
  obtain ⟨η, -, rfl⟩ := Measure.mem_expFamilyMeans_iff.1 hx
  simp [cgf_zero_measure]

/-- **Cramér–Chernoff bound under domination by an exponential family, upper tail.** For
independent random variables `X i`, `i ∈ s`, dominated on `Set.Ici 0` by the member `ρ_η(μ)` of
mean `μ` of the exponential family of `ρ` and `T`, and a mean `x ≥ μ` of the family,
`P(#s * x ≤ ∑ i ∈ s, X i) ≤ exp (-(#s * d(x, μ)))`, where `d(x, μ) = KL(ρ_η(x), ρ_η(μ))`. -/
theorem iIndepFun.measureReal_sum_ge_le_exp_expFamilyDiv (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedOn (X i) P T (ρ.expFamily T (ρ.natParam T μ)) (Set.Ici 0))
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) (hμx : μ ≤ x) :
    P.real {ω | #s * x ≤ ∑ i ∈ s, X i ω} ≤ exp (-(#s * ρ.expFamilyDiv T x μ)) := by
  rcases eq_zero_or_neZero ρ with rfl | _
  · -- the family of the zero measure has the single mean `0`, at which `d` vanishes
    have := h_indep.isProbabilityMeasure
    rw [eq_zero_of_mem_expFamilyMeans_zero_measure hx,
      ← eq_zero_of_mem_expFamilyMeans_zero_measure hμ, Measure.expFamilyDiv_self, mul_zero,
      neg_zero, exp_zero]
    exact measureReal_le_one
  have hη := Measure.natParam_mem_interior_integrableExpSet hμ
  have := Measure.isProbabilityMeasure_expFamily (interior_subset hη)
  exact h_indep.measureReal_sum_ge_le_exp_of_le_rateFunction hX (Measure.integrable_expFamily hη)
    (by rwa [Measure.integral_expFamily_natParam hμ]) (rateFunction_expFamily_natParam hx hμ).ge

/-- **Cramér–Chernoff bound under domination by an exponential family, lower tail.** For
independent random variables `X i`, `i ∈ s`, dominated on `Set.Iic 0` by the member `ρ_η(μ)` of
mean `μ` of the exponential family of `ρ` and `T`, and a mean `x ≤ μ` of the family,
`P(∑ i ∈ s, X i ≤ #s * x) ≤ exp (-(#s * d(x, μ)))`, where `d(x, μ) = KL(ρ_η(x), ρ_η(μ))`. -/
theorem iIndepFun.measureReal_sum_le_le_exp_expFamilyDiv (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedOn (X i) P T (ρ.expFamily T (ρ.natParam T μ)) (Set.Iic 0))
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) (hxμ : x ≤ μ) :
    P.real {ω | ∑ i ∈ s, X i ω ≤ #s * x} ≤ exp (-(#s * ρ.expFamilyDiv T x μ)) := by
  rcases eq_zero_or_neZero ρ with rfl | _
  · -- the family of the zero measure has the single mean `0`, at which `d` vanishes
    have := h_indep.isProbabilityMeasure
    rw [eq_zero_of_mem_expFamilyMeans_zero_measure hx,
      ← eq_zero_of_mem_expFamilyMeans_zero_measure hμ, Measure.expFamilyDiv_self, mul_zero,
      neg_zero, exp_zero]
    exact measureReal_le_one
  have hη := Measure.natParam_mem_interior_integrableExpSet hμ
  have := Measure.isProbabilityMeasure_expFamily (interior_subset hη)
  exact h_indep.measureReal_sum_le_le_exp_of_le_rateFunction hX (Measure.integrable_expFamily hη)
    (by rwa [Measure.integral_expFamily_natParam hμ]) (rateFunction_expFamily_natParam hx hμ).ge

/-! ### Observations with law a member of the family -/

/-- The statistics `T (Y i)`, `i ∈ s`, of independent observations with law the member `ρ_η(μ)` of
mean `μ`, as a family indexed by `s`, are independent and have the law of `T` under `ρ_η(μ)`. -/
private lemma iIndepFun.comp_subtype_and_identDistrib_of_hasLaw_expFamily
    (h_indep : iIndepFun Y P) (hY : ∀ i ∈ s, HasLaw (Y i) (ρ.expFamily T (ρ.natParam T μ)) P)
    (hμ : μ ∈ ρ.expFamilyMeans T) :
    iIndepFun (fun i : s ↦ fun ω ↦ T (Y i ω)) P ∧
      ∀ i : s, IdentDistrib (fun ω ↦ T (Y i ω)) T P (ρ.expFamily T (ρ.natParam T μ)) := by
  have hT : AEMeasurable T (ρ.expFamily T (ρ.natParam T μ)) :=
    (aemeasurable_of_mem_interior_integrableExpSet
      (Measure.natParam_mem_interior_integrableExpSet hμ)).mono_ac
      (Measure.expFamily_absolutelyContinuous ρ T _)
  exact ⟨h_indep.comp_subtype_of_hasLaw hT hY, fun i ↦ (hY i i.2).identDistrib_comp hT⟩

/-- **Cramér–Chernoff bound for an exponential family, upper tail.** For independent random
variables `Y i`, `i ∈ s`, with law the member `ρ_η(μ)` of mean `μ` of the exponential family of `ρ`
and `T`, and a mean `x ≥ μ` of the family,
`P(#s * x ≤ ∑ i ∈ s, T (Y i)) ≤ exp (-(#s * d(x, μ)))`, where `d(x, μ) = KL(ρ_η(x), ρ_η(μ))`. -/
theorem iIndepFun.measureReal_sum_ge_le_exp_expFamilyDiv_of_hasLaw (h_indep : iIndepFun Y P)
    (hY : ∀ i ∈ s, HasLaw (Y i) (ρ.expFamily T (ρ.natParam T μ)) P)
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) (hμx : μ ≤ x) :
    P.real {ω | #s * x ≤ ∑ i ∈ s, T (Y i ω)} ≤ exp (-(#s * ρ.expFamilyDiv T x μ)) := by
  obtain ⟨h_indep', h_ident⟩ :=
    h_indep.comp_subtype_and_identDistrib_of_hasLaw_expFamily hY hμ
  have h_sum (ω : Ω) : ∑ i : s, T (Y i ω) = ∑ i ∈ s, T (Y i ω) :=
    Finset.sum_coe_sort s fun i ↦ T (Y i ω)
  simpa only [card_univ, Fintype.card_coe, h_sum] using
    h_indep'.measureReal_sum_ge_le_exp_expFamilyDiv (s := univ)
      (fun i _ ↦ (h_ident i).mgfDominatedOn) hμ hx hμx

/-- **Cramér–Chernoff bound for an exponential family, lower tail.** For independent random
variables `Y i`, `i ∈ s`, with law the member `ρ_η(μ)` of mean `μ` of the exponential family of `ρ`
and `T`, and a mean `x ≤ μ` of the family,
`P(∑ i ∈ s, T (Y i) ≤ #s * x) ≤ exp (-(#s * d(x, μ)))`, where `d(x, μ) = KL(ρ_η(x), ρ_η(μ))`. -/
theorem iIndepFun.measureReal_sum_le_le_exp_expFamilyDiv_of_hasLaw (h_indep : iIndepFun Y P)
    (hY : ∀ i ∈ s, HasLaw (Y i) (ρ.expFamily T (ρ.natParam T μ)) P)
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) (hxμ : x ≤ μ) :
    P.real {ω | ∑ i ∈ s, T (Y i ω) ≤ #s * x} ≤ exp (-(#s * ρ.expFamilyDiv T x μ)) := by
  obtain ⟨h_indep', h_ident⟩ :=
    h_indep.comp_subtype_and_identDistrib_of_hasLaw_expFamily hY hμ
  have h_sum (ω : Ω) : ∑ i : s, T (Y i ω) = ∑ i ∈ s, T (Y i ω) :=
    Finset.sum_coe_sort s fun i ↦ T (Y i ω)
  simpa only [card_univ, Fintype.card_coe, h_sum] using
    h_indep'.measureReal_sum_le_le_exp_expFamilyDiv (s := univ)
      (fun i _ ↦ (h_ident i).mgfDominatedOn) hμ hx hxμ

end ProbabilityTheory
