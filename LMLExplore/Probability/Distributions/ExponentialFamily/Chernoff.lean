/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Distributions.ExponentialFamily.Mean
public import LMLExplore.Probability.Moments.MGFDominated

/-!
# Cramér–Chernoff bounds under domination by an exponential family

Let `ρ` be a measure on a measurable space `𝓧` and `T : 𝓧 → ℝ` a statistic, with log-partition
function `ψ = cgf T ρ`, and let `ρ_η(μ)` be the member of mean `μ` of their exponential family. A
real random variable `X` is dominated above by `ρ_η(μ)` if `E[exp (t X)] ≤ E_{ρ_η(μ)}[exp (t T)]`
for every `t ≥ 0` (`LMLExplore.MGFDominatedAbove X P T ρ_η(μ)`), and dominated below if the same
holds for every `t ≤ 0`.

For independent random variables `X i`, `i ∈ s`, dominated above by `ρ_η(μ)` and a mean `x ≥ μ` of
the family, the probability that the empirical mean of the `X i` is at least `x` decays
exponentially in the number `#s` of variables, at the rate given by the Kullback–Leibler divergence
`d(x, μ) = KL(ρ_η(x), ρ_η(μ))`: `P(#s * x ≤ ∑ i ∈ s, X i) ≤ exp (-(#s * d(x, μ)))`, and
symmetrically for the lower tail of variables dominated below. The statistics `T (Y i)` of
independent observations `Y i` with law `ρ_η(μ)` are dominated above and below, which gives these
bounds for the sums `∑ i ∈ s, T (Y i)`; for a natural exponential family on `ℝ` (`T = id`), these
are bounds on the sums `∑ i ∈ s, Y i` themselves.

The bound is the Chernoff bound `P(a ≤ S) ≤ exp (-t a) E[exp (t S)]` applied with the optimal
parameter `t = η(x) - η(μ)`. Under the domination, `E[exp (t S)]` for a sum `S` of `n` of the `X i`
is at most the `n`-th power of the moment generating function of `T` under `ρ_η(μ)`, which is
`exp (ψ(η(μ) + t) - ψ(η(μ)))`, and at the optimal parameter the exponent is `-n d(x, μ)`. No
assumption on `ρ` or `T` is needed: when `T` is `ρ`-almost everywhere constant, its only mean is
`μ = x` and the bounds are trivial.

These bounds control the deviations of the empirical means of the arms of a bandit whose reward
distributions are dominated by members of an exponential family. For Bernoulli laws, `d` is the
binary relative entropy (`LMLExplore.expFamilyDiv_bernoulliMeasure_sigmoid`), and random variables
with values in `[0, 1]` are dominated by Bernoulli laws, which gives the bounds
`LMLExplore.measureReal_sum_ge_le_exp_klBerReal` and
`LMLExplore.measureReal_sum_le_le_exp_klBerReal`.

## Main statements

* `ProbabilityTheory.iIndepFun.measureReal_sum_ge_le_exp_expFamilyDiv`: the upper tail
  `P(#s * x ≤ ∑ i ∈ s, X i) ≤ exp (-(#s * d(x, μ)))` for variables dominated above by the member
  of mean `μ` and means `μ ≤ x` of the family.
* `ProbabilityTheory.iIndepFun.measureReal_sum_le_le_exp_expFamilyDiv`: the lower tail
  `P(∑ i ∈ s, X i ≤ #s * x) ≤ exp (-(#s * d(x, μ)))` for variables dominated below by the member
  of mean `μ` and means `x ≤ μ` of the family.
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

/-- At the parameter `t = η(x) - η(μ)`, the statistic `T` has an exponential moment of order `t`
under the member `ρ_η(μ)` of mean `μ`, and the exponent of the Chernoff bound for `n` variables
dominated by `ρ_η(μ)`, `exp (-t (n x)) (mgf T ρ_η(μ) t) ^ n`, is at most `exp (-(n d(x, μ)))`. -/
private lemma integrable_and_exp_mul_mgf_pow_natParam_le (hμ : μ ∈ ρ.expFamilyMeans T)
    (hx : x ∈ ρ.expFamilyMeans T) (n : ℕ) :
    Integrable (fun y ↦ exp ((ρ.natParam T x - ρ.natParam T μ) * T y))
        (ρ.expFamily T (ρ.natParam T μ)) ∧
      exp (-(ρ.natParam T x - ρ.natParam T μ) * (n * x)) *
          mgf T (ρ.expFamily T (ρ.natParam T μ)) (ρ.natParam T x - ρ.natParam T μ) ^ n ≤
        exp (-(n * ρ.expFamilyDiv T x μ)) := by
  have hη := interior_subset (Measure.natParam_mem_interior_integrableExpSet hμ)
  have hηt : ρ.natParam T μ + (ρ.natParam T x - ρ.natParam T μ) ∈ integrableExpSet T ρ := by
    rw [add_sub_cancel]
    exact interior_subset (Measure.natParam_mem_interior_integrableExpSet hx)
  have h_int : ρ.natParam T x - ρ.natParam T μ ∈
      integrableExpSet T (ρ.expFamily T (ρ.natParam T μ)) := by
    rwa [Measure.integrableExpSet_expFamily hη]
  refine ⟨h_int, ?_⟩
  -- `mgf ≤ exp cgf`, and the cumulant generating function of `T` under `ρ_η(μ)` is
  -- `t ↦ ψ(η(μ) + t) - ψ(η(μ))`
  calc exp (-(ρ.natParam T x - ρ.natParam T μ) * (n * x)) *
        mgf T (ρ.expFamily T (ρ.natParam T μ)) (ρ.natParam T x - ρ.natParam T μ) ^ n
  _ ≤ exp (-(ρ.natParam T x - ρ.natParam T μ) * (n * x)) *
        exp (cgf T (ρ.expFamily T (ρ.natParam T μ)) (ρ.natParam T x - ρ.natParam T μ)) ^ n := by
    gcongr
    · exact mgf_nonneg
    · exact le_exp_log _
  _ = exp (-(n * ρ.expFamilyDiv T x μ)) := by
    rw [Measure.cgf_expFamily hη hηt, add_sub_cancel, ← exp_nat_mul, ← exp_add,
      Measure.expFamilyDiv_def]
    ring_nf

/-- **Cramér–Chernoff bound under domination by an exponential family, upper tail.** For
independent random variables `X i`, `i ∈ s`, dominated above by the member `ρ_η(μ)` of mean `μ`
of the exponential family of `ρ` and `T`, and a mean `x ≥ μ` of the family,
`P(#s * x ≤ ∑ i ∈ s, X i) ≤ exp (-(#s * d(x, μ)))`, where `d(x, μ) = KL(ρ_η(x), ρ_η(μ))`. -/
theorem iIndepFun.measureReal_sum_ge_le_exp_expFamilyDiv (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedAbove (X i) P T (ρ.expFamily T (ρ.natParam T μ)))
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) (hμx : μ ≤ x) :
    P.real {ω | #s * x ≤ ∑ i ∈ s, X i ω} ≤ exp (-(#s * ρ.expFamilyDiv T x μ)) := by
  obtain ⟨h_int, h_le⟩ := integrable_and_exp_mul_mgf_pow_natParam_le hμ hx #s
  exact (h_indep.measureReal_sum_ge_le_exp_mul_mgf_pow hX _
    (sub_nonneg.2 (Measure.monotoneOn_natParam hμ hx hμx)) h_int).trans h_le

/-- **Cramér–Chernoff bound under domination by an exponential family, lower tail.** For
independent random variables `X i`, `i ∈ s`, dominated below by the member `ρ_η(μ)` of mean `μ`
of the exponential family of `ρ` and `T`, and a mean `x ≤ μ` of the family,
`P(∑ i ∈ s, X i ≤ #s * x) ≤ exp (-(#s * d(x, μ)))`, where `d(x, μ) = KL(ρ_η(x), ρ_η(μ))`. -/
theorem iIndepFun.measureReal_sum_le_le_exp_expFamilyDiv (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedBelow (X i) P T (ρ.expFamily T (ρ.natParam T μ)))
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) (hxμ : x ≤ μ) :
    P.real {ω | ∑ i ∈ s, X i ω ≤ #s * x} ≤ exp (-(#s * ρ.expFamilyDiv T x μ)) := by
  obtain ⟨h_int, h_le⟩ := integrable_and_exp_mul_mgf_pow_natParam_le hμ hx #s
  exact (h_indep.measureReal_sum_le_le_exp_mul_mgf_pow hX _
    (sub_nonpos.2 (Measure.monotoneOn_natParam hx hμ hxμ)) h_int).trans h_le

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
      (fun i _ ↦ (h_ident i).mgfDominatedAbove) hμ hx hμx

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
      (fun i _ ↦ (h_ident i).mgfDominatedBelow) hμ hx hxμ

end ProbabilityTheory
