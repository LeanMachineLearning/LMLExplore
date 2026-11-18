/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Distributions.ExponentialFamily.RateFunction
public import LMLExplore.Probability.Martingale.IteratedLogarithm

/-!
# Self-normalized deviations under domination by an exponential family

Let `X k` be real variables conditionally dominated, given the past, by the member `ρ_η(μ)` of mean
`μ` of the exponential family of a measure `ρ` and a statistic `T`: the conditional moment
generating function of `X k` is at most that of `T` under `ρ_η(μ)`, on the nonnegative parameters
for the upper tail and on the nonpositive ones for the lower tail. Select some of them by
predictable indicators in `{0, 1}`, and let `N t` and `μ̂ t` be the number and the mean of the
selected variables after `t` rounds. The rate function of `T` under `ρ_η(μ)` is the extended
divergence `dbar(·, μ)` of the family, so the self-normalized deviation bounds of
`LMLExplore/Probability/Martingale/RateFunction.lean` are the bounds of [GC11, Theorem 10] for the
generalized likelihood ratio statistic `N t dbar(μ̂ t, μ)`: for `x > 0` and `n ≥ 2`,
`P(∃ t, 1 ≤ N t ≤ n, μ < μ̂ t, x ≤ N t dbar(μ̂ t, μ)) ≤ e ⌈x log n⌉ exp (-x)`, and the same below
the mean. The empirical means may lie outside the open interval of means of the family, for
instance at `0` or `1` for Bernoulli observations.

When the conditional moment generating function of `X k` is bounded by that of `T` under
`ρ_η(μ)` for all parameters, the bounds of
`LMLExplore/Probability/Martingale/IteratedLogarithm.lean` control the two-sided deviation
`N t dbar(μ̂ t, μ)` at all rounds simultaneously, with a threshold growing like
`3 log (1 + log N t)` [KK21, Lemma 13, Corollary 31]: for `x ≥ 0`,
`P(∃ t, 1 ≤ N t, 2 H_{3/2}((x + log (2 ζ(2))) / 2) + 3 log (1 + log N t) ≤ N t dbar(μ̂ t, μ))`
`≤ exp (-x)`, with `H_z = LMLExplore.minMulSubLogLog z`. For a bandit arm, `w k` indicates that
the arm is pulled at round `k`, whatever the sampling rule.

## Main statements

* `LMLExplore.measure_exists_gt_and_le_mul_expFamilyRate_le`: the bound above the mean.
* `LMLExplore.measure_exists_lt_and_le_mul_expFamilyRate_le`: the bound below the mean.
* `LMLExplore.measure_exists_add_three_mul_log_le_mul_expFamilyRate_le` [KK21, Lemma 13]: for
  `c ∈ (1, 3/2]` and `x > 0`, the threshold `x + c log (2 ζ(2) / log² c) + 3 log (1 + log N t)` is
  exceeded by `N t dbar(μ̂ t, μ)` at some round with probability at most `exp (-x / c)`.
* `LMLExplore.measure_exists_two_mul_minMulSubLogLog_add_le_mul_expFamilyRate_le`
  [KK21, Corollary 31]: the threshold `2 H_{3/2}((x + log (2 ζ(2))) / 2) + 3 log (1 + log N t)` is
  exceeded at some round with probability at most `exp (-x)`, for `x ≥ 0`.

## References

* [GC11] A. Garivier and O. Cappé, *The KL-UCB algorithm for bounded stochastic bandits and
  beyond*, COLT 2011, Theorem 10, there for independent variables bounded in `[0, 1]` and the
  binary relative entropy.
* [KK21] E. Kaufmann and W. M. Koolen, *Mixture martingales revisited with applications to
  sequential tests and confidence intervals*, JMLR 22 (2021), Lemma 13 and Corollary 31.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Set

open scoped ENNReal

namespace LMLExplore

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} [NeZero ρ] {T : 𝓧 → ℝ}
  {ℱ : Filtration ℕ mΩ} {X w : ℕ → Ω → ℝ} {μ x : ℝ} {n : ℕ}

/-- **Self-normalized deviations above the mean, for an exponential family** [GC11, Theorem 10].
Let `X k` be `ℱ (k + 1)`-measurable with moment generating function conditionally bounded, on the
nonnegative parameters given `ℱ k`, by that of the statistic `T` under the member `ρ_η(μ)` of mean
`μ` of the exponential family of `ρ` and `T`, and let the selection indicators `w` be adapted with
values in `{0, 1}`. For `N t` selected variables with mean `μ̂ t` after `t` rounds, `x > 0` and
`n ≥ 2`, the probability that `1 ≤ N t ≤ n`, `μ < μ̂ t` and `x ≤ N t dbar(μ̂ t, μ)` at some round
`t` is at most `e ⌈x log n⌉ exp (-x)`. -/
theorem measure_exists_gt_and_le_mul_expFamilyRate_le (hμ : μ ∈ ρ.expFamilyMeans T)
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf T (ρ.expFamily T (ρ.natParam T μ)))
      (Ici 0 ∩ integrableExpSet T (ρ.expFamily T (ρ.natParam T μ))) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hx : 0 < x) (hn : 1 < n) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧ ∑ k ∈ range t, w k ω ≤ n ∧
      μ < (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal x ≤ ENNReal.ofReal (∑ k ∈ range t, w k ω) *
        ρ.expFamilyRate T ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω) μ} ≤
      ENNReal.ofReal (exp 1 * ⌈x * log n⌉₊ * exp (-x)) := by
  have hη := Measure.natParam_mem_interior_integrableExpSet hμ
  have := Measure.isProbabilityMeasure_expFamily (interior_subset hη)
  have h := measure_exists_gt_and_le_mul_rateFunction_le hX hψ hw hw01
    (Measure.integrable_expFamily hη) hx hn
  rw [Measure.integral_expFamily_natParam hμ] at h
  simpa only [Measure.expFamilyRate_def] using h

/-- **Self-normalized deviations below the mean, for an exponential family** [GC11, Theorem 10].
Let `X k` be `ℱ (k + 1)`-measurable with moment generating function conditionally bounded, on the
nonpositive parameters given `ℱ k`, by that of the statistic `T` under the member `ρ_η(μ)` of mean
`μ` of the exponential family of `ρ` and `T`, and let the selection indicators `w` be adapted with
values in `{0, 1}`. For `N t` selected variables with mean `μ̂ t` after `t` rounds, `x > 0` and
`n ≥ 2`, the probability that `1 ≤ N t ≤ n`, `μ̂ t < μ` and `x ≤ N t dbar(μ̂ t, μ)` at some round
`t` is at most `e ⌈x log n⌉ exp (-x)`. -/
theorem measure_exists_lt_and_le_mul_expFamilyRate_le (hμ : μ ∈ ρ.expFamilyMeans T)
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf T (ρ.expFamily T (ρ.natParam T μ)))
      (Iic 0 ∩ integrableExpSet T (ρ.expFamily T (ρ.natParam T μ))) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hx : 0 < x) (hn : 1 < n) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧ ∑ k ∈ range t, w k ω ≤ n ∧
      (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω < μ ∧
      ENNReal.ofReal x ≤ ENNReal.ofReal (∑ k ∈ range t, w k ω) *
        ρ.expFamilyRate T ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω) μ} ≤
      ENNReal.ofReal (exp 1 * ⌈x * log n⌉₊ * exp (-x)) := by
  have hη := Measure.natParam_mem_interior_integrableExpSet hμ
  have := Measure.isProbabilityMeasure_expFamily (interior_subset hη)
  have h := measure_exists_lt_and_le_mul_rateFunction_le hX hψ hw hw01
    (Measure.integrable_expFamily hη) hx hn
  rw [Measure.integral_expFamily_natParam hμ] at h
  simpa only [Measure.expFamilyRate_def] using h

/-- **Time-uniform deviations for an exponential family, with an iterated-logarithm correction**
[KK21, Lemma 13]. Let `X k` be `ℱ (k + 1)`-measurable with moment generating function conditionally
bounded given `ℱ k` by that of the statistic `T` under the member `ρ_η(μ)` of mean `μ` of the
exponential family of `ρ` and `T`, and let the selection indicators `w` be adapted with values in
`{0, 1}`. For `N t` selected variables with mean `μ̂ t` after `t` rounds, `c ∈ (1, 3/2]` and
`x > 0`, the probability that, at some round `t`, `1 ≤ N t` and
`x + c log (2 ζ(2) / log² c) + 3 log (1 + log N t) ≤ N t dbar(μ̂ t, μ)` is at most `exp (-x / c)`,
with `2 ζ(2) = π ^ 2 / 3`. -/
theorem measure_exists_add_three_mul_log_le_mul_expFamilyRate_le (hμ : μ ∈ ρ.expFamilyMeans T)
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf T (ρ.expFamily T (ρ.natParam T μ)))
      (integrableExpSet T (ρ.expFamily T (ρ.natParam T μ))) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) {c : ℝ} (hc : 1 < c)
    (hc' : c ≤ 3 / 2) (hx : 0 < x) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal (x + c * log (π ^ 2 / 3 / log c ^ 2) +
        3 * log (1 + log (∑ k ∈ range t, w k ω))) ≤
        ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          ρ.expFamilyRate T ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω) μ} ≤
      ENNReal.ofReal (exp (-(x / c))) := by
  have hη := Measure.natParam_mem_interior_integrableExpSet hμ
  have := Measure.isProbabilityMeasure_expFamily (interior_subset hη)
  simpa only [Measure.expFamilyRate_def] using
    measure_exists_add_three_mul_log_le_mul_rateFunction_le hX hψ hw hw01
      (Measure.integrable_expFamily hη) hc hc' hx

/-- **Time-uniform deviations for an exponential family, with an optimally tuned
iterated-logarithm correction** [KK21, Corollary 31]. Let `X k` be `ℱ (k + 1)`-measurable with
moment generating function conditionally bounded given `ℱ k` by that of the statistic `T` under the
member `ρ_η(μ)` of mean `μ` of the exponential family of `ρ` and `T`, and let the selection
indicators `w` be adapted with values in `{0, 1}`. For `N t` selected variables with mean `μ̂ t`
after `t` rounds and `x ≥ 0`, the probability that, at some round `t`, `1 ≤ N t` and
`2 H_{3/2}((x + log (2 ζ(2))) / 2) + 3 log (1 + log N t) ≤ N t dbar(μ̂ t, μ)` is at most
`exp (-x)`, with `H_z = LMLExplore.minMulSubLogLog z` and `2 ζ(2) = π ^ 2 / 3`. -/
theorem measure_exists_two_mul_minMulSubLogLog_add_le_mul_expFamilyRate_le
    (hμ : μ ∈ ρ.expFamilyMeans T) (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf T (ρ.expFamily T (ρ.natParam T μ)))
      (integrableExpSet T (ρ.expFamily T (ρ.natParam T μ))) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hx : 0 ≤ x) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal (2 * minMulSubLogLog (3 / 2) ((x + log (π ^ 2 / 3)) / 2) +
        3 * log (1 + log (∑ k ∈ range t, w k ω))) ≤
        ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          ρ.expFamilyRate T ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω) μ} ≤
      ENNReal.ofReal (exp (-x)) := by
  have hη := Measure.natParam_mem_interior_integrableExpSet hμ
  have := Measure.isProbabilityMeasure_expFamily (interior_subset hη)
  simpa only [Measure.expFamilyRate_def] using
    measure_exists_two_mul_minMulSubLogLog_add_le_mul_rateFunction_le hX hψ hw hw01
      (Measure.integrable_expFamily hη) hx

end LMLExplore
