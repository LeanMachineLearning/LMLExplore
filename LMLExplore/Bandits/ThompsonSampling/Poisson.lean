/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.ThompsonSampling.Basic
public import LMLExplore.Probability.Distributions.ExponentialFamily.Poisson

/-!
# Thompson sampling with the Jeffreys prior for Poisson arms

The real-valued Poisson laws `Po(ℝ, μ)` with `μ > 0` form the natural exponential family generated
by `Po(ℝ, r)`, for any rate `r ≠ 0`, with mean map `η ↦ r exp η`. Its Jeffreys prior is the
measure `μ ^ (-1 / 2) dμ` on the mean
(`LMLExplore.map_deriv_cgf_jeffreysPrior_map_cast_poissonMeasure`), and the image of the posterior
after `s ≠ 0` observations of sum `S` by the mean map is the gamma law of shape `S + 1 / 2` and
rate `s`
(`LMLExplore.map_deriv_cgf_expFamilyPosterior_map_cast_poissonMeasure_jeffreysPrior`).
So Thompson sampling with the Jeffreys prior for Poisson arms perturbs an arm with reward sum `S`
after `s ≥ 1` pulls by a mean drawn from that gamma law, and it exceeds a level `c` with the
probability that this gamma law gives to `(c, ∞)`: the quantity `G_s` of the generic bound of
follow-the-perturbed-leader [LS, Theorem 36.2]
(`LMLExplore.Bandits.ExpFamilyTS.lintegral_pullCount_le`).

## Main statements

* `LMLExplore.Bandits.expFamilyTSStackLaw_map_cast_poissonMeasure_jeffreysPrior`: the perturbation
  law of an arm pulled `s ≠ 0` times with sum of rewards `S > -1 / 2` is the image in `EReal` of
  the gamma law of shape `S + 1 / 2` and rate `s`.

## References

* [KKM13] N. Korda, E. Kaufmann and R. Munos, *Thompson sampling for 1-dimensional exponential
  family bandits*, NeurIPS 2013.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 36.
-/

public section

open MeasureTheory ProbabilityTheory

open scoped NNReal

namespace LMLExplore.Bandits

variable {s : ℕ} {S : ℝ}

/-- **Thompson sampling with the Jeffreys prior for Poisson arms samples from gamma laws**: for the
exponential family of `Po(ℝ, r)`, `r ≠ 0`, and its Jeffreys prior, the perturbation law of an arm
pulled `s ≠ 0` times with sum of rewards `S > -1 / 2` (for example `s` Poisson counts of sum `S`)
is the image in `EReal` of the gamma law of shape `S + 1 / 2` and rate `s`. -/
theorem expFamilyTSStackLaw_map_cast_poissonMeasure_jeffreysPrior {r : ℝ≥0} (hr : r ≠ 0)
    (hs : s ≠ 0) (hS : -(1 / 2) < S) :
    expFamilyTSStackLaw Po(ℝ, r) (Po(ℝ, r).jeffreysPrior id) s S =
      (gammaMeasure (S + 1 / 2) s).map ((↑) : ℝ → EReal) := by
  have hpost := map_deriv_cgf_expFamilyPosterior_map_cast_poissonMeasure_jeffreysPrior hr hs hS
  have hne := (isProbabilityMeasure_expFamilyPosterior_map_cast_poissonMeasure_jeffreysPrior hr hs
    hS).ne_zero
  rw [expFamilyTSStackLaw_of_ne_zero hs hne, ← hpost,
    Measure.map_map (by fun_prop) (measurable_deriv _), Function.comp_def]

end LMLExplore.Bandits
