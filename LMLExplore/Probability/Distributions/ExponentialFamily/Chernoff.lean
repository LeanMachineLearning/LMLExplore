/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Distributions.ExponentialFamily.Mean
public import LMLExplore.Probability.Distributions.ExponentialFamily.UpperConfidence
public import LMLExplore.Probability.Moments.MGF.Dominated
import LMLExplore.Analysis.SpecialFunctions.Exp
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

The same bounds control the upper confidence level `U(μ̂, c)` of the family
(`MeasureTheory.Measure.expFamilyUpper`), the index of KL-UCB, at the empirical mean `μ̂`. It
underestimates a mean `q < μ` by the budget `L / #s` with probability at most
`exp (-L) exp (-(#s d(q, μ)))`, by the three-point identity of the extended divergence `dbar`; and
for `μ < μ + ε < c`, the sample sizes `s` at which `μ̂_s ≥ c` or `dbar(μ̂_s, c) ≤ L / s` number at
most `1 + L / d(μ + ε, c) + 1 / d(μ + ε, μ)` in expectation. These are the two concentration
lemmas of the analysis of KL-UCB [LS, Lemmas 10.7 and 10.8; GC11; CGMMS13], for arms dominated by
members of an exponential family rather than for rewards in `[0, 1]`.

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
* `ProbabilityTheory.iIndepFun.measureReal_expFamilyUpper_le_le`: for a mean `q < μ` and
  variables dominated on `Set.Iic 0`, `P(U(μ̂, L / #s) ≤ q) ≤ exp (-L) exp (-(#s d(q, μ)))`.
* `ProbabilityTheory.iIndepFun.sum_measureReal_eq_zero_or_le_div_or_expFamilyRate_div_le_le`: for
  variables dominated on `Set.Ici 0` and means `μ + ε < c`,
  `∑_{s < n} P(s = 0 ∨ c ≤ μ̂_s ∨ dbar(μ̂_s, c) ≤ L / s) ≤ 1 + L / d(μ + ε, c) + 1 / d(μ + ε, μ)`.

## References

* S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford University Press,
  2013, Section 2.2 (the Cramér–Chernoff method).
* A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, where these bounds control the empirical means of exponential-family arms.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemmas 10.7 and 10.8.
* [GC11] A. Garivier and O. Cappé, *The KL-UCB algorithm for bounded stochastic bandits and
  beyond*, COLT 2011.
* [CGMMS13] O. Cappé, A. Garivier, O.-A. Maillard, R. Munos and G. Stoltz, *Kullback–Leibler
  upper confidence bounds for optimal sequential allocation*, Ann. Statist. 41(3), 2013.
-/

public section

open MeasureTheory Real Finset LMLExplore

namespace ProbabilityTheory

variable {Ω ι 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {P : Measure Ω}
  {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {X : ι → Ω → ℝ} {Y : ι → Ω → 𝓧} {s : Finset ι} {μ x : ℝ}

/-! ### Cramér–Chernoff bounds -/

/-- For the zero measure, whose family has the single mean `0`, the Cramér–Chernoff bounds at
means of the family are trivial: the divergence vanishes and the bound is `1`. -/
private lemma measureReal_le_exp_expFamilyDiv_zero_measure [IsProbabilityMeasure P] {E : Set Ω}
    (hμ : μ ∈ (0 : Measure 𝓧).expFamilyMeans T) (hx : x ∈ (0 : Measure 𝓧).expFamilyMeans T)
    (n : ℝ) : P.real E ≤ exp (-(n * (0 : Measure 𝓧).expFamilyDiv T x μ)) := by
  simp only [Measure.expFamilyMeans_zero_measure, Set.mem_singleton_iff] at hμ hx
  simp [hμ, hx]

/-- **Cramér–Chernoff bound under domination by an exponential family, upper tail.** For
independent random variables `X i`, `i ∈ s`, dominated on `Set.Ici 0` by the member `ρ_η(μ)` of
mean `μ` of the exponential family of `ρ` and `T`, and a mean `x ≥ μ` of the family,
`P(#s * x ≤ ∑ i ∈ s, X i) ≤ exp (-(#s * d(x, μ)))`, where `d(x, μ) = KL(ρ_η(x), ρ_η(μ))`. -/
theorem iIndepFun.measureReal_sum_ge_le_exp_expFamilyDiv (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedOn (X i) P T (ρ.expFamily T (ρ.natParam T μ)) (Set.Ici 0))
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) (hμx : μ ≤ x) :
    P.real {ω | #s * x ≤ ∑ i ∈ s, X i ω} ≤ exp (-(#s * ρ.expFamilyDiv T x μ)) := by
  rcases eq_zero_or_neZero ρ with rfl | _
  · have := h_indep.isProbabilityMeasure
    exact measureReal_le_exp_expFamilyDiv_zero_measure hμ hx _
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
  · have := h_indep.isProbabilityMeasure
    exact measureReal_le_exp_expFamilyDiv_zero_measure hμ hx _
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

/-! ### Upper confidence levels -/

/-- **Underestimation by the upper confidence level.** For independent random variables `X i`,
`i ∈ s`, dominated on `Set.Iic 0` by the member `ρ_η(μ)` of mean `μ` of the exponential family of
`ρ` and `T`, a nonempty `s` with empirical mean `μ̂ = (∑ i ∈ s, X i) / #s`, a mean `q < μ` of the
family and a real `L`, the upper confidence level `U(μ̂, L / #s)` is at most `q` with probability
at most `exp (-L) exp (-(#s d(q, μ)))`. This generalizes [LS, Lemma 10.7] from rewards in `[0, 1]`
to exponential families. -/
theorem iIndepFun.measureReal_expFamilyUpper_le_le (h_indep : iIndepFun X P) (hs : s.Nonempty)
    (hX : ∀ i ∈ s, MGFDominatedOn (X i) P T (ρ.expFamily T (ρ.natParam T μ)) (Set.Iic 0))
    (hμ : μ ∈ ρ.expFamilyMeans T) {q : ℝ} (hq : q ∈ ρ.expFamilyMeans T) (hqμ : q < μ) (L : ℝ) :
    P.real {ω | ρ.expFamilyUpper T ((∑ i ∈ s, X i ω) / #s) (ENNReal.ofReal (L / #s)) ≤ q} ≤
      exp (-L) * exp (-(#s * ρ.expFamilyDiv T q μ)) := by
  have := h_indep.isProbabilityMeasure
  rcases eq_zero_or_neZero ρ with rfl | _
  · -- for the zero measure, the only mean is `0`, so `q < μ` is impossible
    rw [Measure.expFamilyMeans_zero_measure, Set.mem_singleton_iff] at hμ hq
    exact absurd (hq.trans hμ.symm) hqμ.ne
  have hT := Measure.not_ae_eq_const_of_mem_expFamilyMeans hq hμ hqμ.ne
  have hη := Measure.natParam_mem_interior_integrableExpSet hμ
  have := Measure.isProbabilityMeasure_expFamily (interior_subset hη)
  have hs0 : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  set d := ρ.expFamilyDiv T q μ
  calc P.real {ω | ρ.expFamilyUpper T ((∑ i ∈ s, X i ω) / #s) (ENNReal.ofReal (L / #s)) ≤ q}
  _ ≤ P.real {ω | (∑ i ∈ s, X i ω) / #s ≤ ∫ x, T x ∂(ρ.expFamily T (ρ.natParam T μ)) ∧
      ENNReal.ofReal (L + #s * d) ≤
        #s * rateFunction T (ρ.expFamily T (ρ.natParam T μ)) ((∑ i ∈ s, X i ω) / #s)} := by
    -- on the event, `dbar(μ̂, μ) ≥ dbar(μ̂, q) + d(q, μ) ≥ L / #s + d(q, μ)` by the three-point
    -- identity, and the lower tail Cramér–Chernoff bound with the rate function applies
    refine measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    set x := (∑ i ∈ s, X i ω) / #s
    have hxq : x ≤ q := EReal.coe_le_coe_iff.1 ((Measure.le_expFamilyUpper ρ T x _).trans hω)
    rw [Measure.integral_expFamily_natParam hμ, ← Measure.expFamilyRate_def]
    refine ⟨hxq.trans hqμ.le, ?_⟩
    -- `dbar(x, μ) = dbar(x, q) + d(q, μ) + (q - x) (η(μ) - η(q))`, with a nonnegative last term
    have h_prod : 0 ≤ (q - x) * (ρ.natParam T μ - ρ.natParam T q) :=
      mul_nonneg (sub_nonneg.2 hxq) (sub_nonneg.2 (Measure.monotoneOn_natParam hq hμ hqμ.le))
    rw [Measure.expFamilyRate_eq_add_of_mul_nonneg hq hμ h_prod]
    calc ENNReal.ofReal (L + #s * d)
    _ ≤ ENNReal.ofReal (#s * (L / #s)) + ENNReal.ofReal (#s * d) := by
      rw [mul_div_cancel₀ _ hs0.ne']
      exact ENNReal.ofReal_add_le
    _ = #s * (ENNReal.ofReal (L / #s) + ENNReal.ofReal d) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast, mul_add]
    _ ≤ #s * (ρ.expFamilyRate T x q +
        ENNReal.ofReal (d + (q - x) * (ρ.natParam T μ - ρ.natParam T q))) := by
      gcongr
      · exact Measure.le_expFamilyRate_of_expFamilyUpper_le hT hq hω
      · exact le_add_of_nonneg_right h_prod
  _ ≤ exp (-(L + #s * d)) :=
    h_indep.measureReal_le_integral_and_le_card_mul_rateFunction_le_exp hX
      (Measure.integrable_expFamily hη) _
  _ = exp (-L) * exp (-(#s * d)) := by
    rw [← exp_add, neg_add]

/-- **Overestimation of the upper confidence level.** Let `X₀, X₁, …` be independent and
dominated on `Set.Ici 0` by the member `ρ_η(μ)` of mean `μ` of the exponential family of `ρ` and
`T`, let `ε > 0` and `c > μ + ε` with `μ + ε` and `c` means of the family, and let `L ≥ 0`. Then
the expected number of sample sizes `s < n` at which `s = 0`, or the empirical mean
`μ̂_s = (X₀ + ⋯ + X_{s-1}) / s` is at least `c`, or `dbar(μ̂_s, c) ≤ L / s`, is at most
`1 + L / d(μ + ε, c) + 1 / d(μ + ε, μ)`, uniformly in `n`. This generalizes [LS, Lemma 10.8] from
rewards in `[0, 1]` to exponential families. For `c` above `μ̂_s` and below the upper confidence
level `U(μ̂_s, L / s)`, `dbar(μ̂_s, c) ≤ L / s` (`MeasureTheory.Measure.le_expFamilyUpper_iff`), so
the events contain the sample sizes at which the index of an arm of mean `μ` is at least `c`. -/
theorem iIndepFun.sum_measureReal_eq_zero_or_le_div_or_expFamilyRate_div_le_le {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X P)
    (hX : ∀ i, MGFDominatedOn (X i) P T (ρ.expFamily T (ρ.natParam T μ)) (Set.Ici 0))
    (hμ : μ ∈ ρ.expFamilyMeans T) {ε c : ℝ} (hε : 0 < ε) (hc : μ + ε < c)
    (hμε : μ + ε ∈ ρ.expFamilyMeans T) (hcM : c ∈ ρ.expFamilyMeans T) {L : ℝ} (hL : 0 ≤ L)
    (n : ℕ) :
    ∑ s ∈ range n, P.real {ω | s = 0 ∨ c ≤ (∑ i ∈ range s, X i ω) / s ∨
        ρ.expFamilyRate T ((∑ i ∈ range s, X i ω) / s) c ≤ ENNReal.ofReal (L / s)} ≤
      1 + L / ρ.expFamilyDiv T (μ + ε) c + 1 / ρ.expFamilyDiv T (μ + ε) μ := by
  have := h_indep.isProbabilityMeasure
  set D := ρ.expFamilyDiv T (μ + ε) c
  set D' := ρ.expFamilyDiv T (μ + ε) μ
  have hD : 0 < D := Measure.expFamilyDiv_pos hμε hcM hc.ne
  have hD' : 0 < D' := Measure.expFamilyDiv_pos hμε hμ (by linarith)
  -- the term of `s` is at most `1` if `s D ≤ L`, and otherwise at most the Chernoff bound
  -- `exp (-(s d(μ + ε, μ)))`: if `μ̂_s < μ + ε`, then `D ≤ dbar(μ̂_s, c)`, and `μ̂_s < c`
  have h_term (s : ℕ) : P.real {ω | s = 0 ∨ c ≤ (∑ i ∈ range s, X i ω) / s ∨
      ρ.expFamilyRate T ((∑ i ∈ range s, X i ω) / s) c ≤ ENNReal.ofReal (L / s)} ≤
        if s * D ≤ L then 1 else exp (-(D' * s)) := by
    have h_chernoff := h_indep.measureReal_sum_ge_le_exp_expFamilyDiv (s := range s)
      (fun i _ ↦ hX i) hμ hμε (by linarith)
    rw [card_range, mul_comm (s : ℝ) (ρ.expFamilyDiv T (μ + ε) μ)] at h_chernoff
    exact measureReal_eq_zero_or_le_div_or_apply_div_le_le_ite
      (Measure.antitoneOn_expFamilyRate_left hcM) hc.le
      (Measure.expFamilyRate_eq_ofReal_expFamilyDiv hμε hcM) hL h_chernoff
  calc ∑ s ∈ range n, P.real {ω | s = 0 ∨ c ≤ (∑ i ∈ range s, X i ω) / s ∨
      ρ.expFamilyRate T ((∑ i ∈ range s, X i ω) / s) c ≤ ENNReal.ofReal (L / s)}
  _ ≤ ∑ s ∈ range n, (if s * D ≤ L then 1 else exp (-(D' * s))) :=
    sum_le_sum fun s _ ↦ h_term s
  _ ≤ 1 + L / D + 1 / D' := by
    rw [one_div]
    exact sum_range_ite_mul_le_exp_neg_mul_le hD hL hD' n

end ProbabilityTheory
