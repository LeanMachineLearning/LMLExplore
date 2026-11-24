/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import LMLExplore.EValues.EProcess.LevelStoppingTime
public import Mathlib.Probability.ProductMeasure
import LMLExplore.EValues.BipolarRate.StoppingTime
import LMLExplore.Probability.Process.LevelCrossing
import Mathlib.Probability.Independence.InfinitePi
import TauCeti.Probability.Independence.InfinitePi

/-!
# The expected number of observations of the test of the product of the numeraires

Let `S₁` be a set of measures of mass at most `1` on `𝓧` (the null) and `Q₁` a probability measure
on `𝓧` (the alternative). The observations are the coordinates of `ℕ → 𝓧`, with the i.i.d. law
`Q = Measure.infinitePi fun _ ↦ Q₁`. The numeraire `X* = numeraire Q₁ S₁` is the log-optimal
e-variable for `S₁` under `Q₁`, with expected logarithm `D = maxEPower Q₁ S₁`, and the product
`∏ k < n, X* (ω k)` of the numeraires is a test supermartingale for the sequential null of the
constant one-step null `S₁`
(`ProbabilityTheory.isTestSupermartingale_prod_numeraire_sequentialNull`).
Thresholding it at `α⁻¹` is a sequential test of level `α`
(`ProbabilityTheory.IsEProcess.isLevelStoppingTime_hittingAfter`).

This file computes its expected number of observations: if `D > 0`, the first time `τ α` at
which the product reaches `α⁻¹` satisfies `𝔼_Q[τ α] / log (1/α) → 1 / D` as `α → 0`, with
`1 / ∞ = 0` [ARR26, Theorem 4.1]. The numeraires of the observations are i.i.d. factors whose
logarithm has the mean `D`, and the limit is that of the expected time for a product of i.i.d.
factors to reach a level
(`ProbabilityTheory.iIndepFun.tendsto_lintegral_hittingAfter_prod_div_log`), which comes
from the elementary renewal theorem for first passage times. No moment of `log X*` is assumed.

For a null `S₁` of probability measures, every sequential test of level `α` for the i.i.d. laws
of the members of `S₁` makes at least `log (1/α) / d` observations in expectation, with
`d = bipolarRate Q₁ S₁` (`ProbabilityTheory.toENNReal_log_inv_div_bipolarRate_le_lintegral`), and
`D ≤ d ≤ KL_inf(Q₁, S₁)`. When the rate `D` of the numeraires is the bipolar rate `d`, for
instance when `D = KL_inf(Q₁, S₁)`, as for a simple null, the test of the product of the
numeraires attains the lower bound to first order.

## Main statements

* `ProbabilityTheory.tendsto_lintegral_hittingAfter_prod_numeraire_div_log`: for `D > 0`,
  `𝔼_Q[τ α] / log (1/α) → 1 / D` as `α → 0`.
* `ProbabilityTheory.toENNReal_log_inv_div_maxEPower_le_lintegral`: if the bipolar rate is at
  most `D`, for instance if `KL_inf(Q₁, S₁) ≤ D`, every sequential test of level `α` makes at
  least `log (1/α) / D` observations in expectation.

## References

* [ARR26] S. Agrawal, A. Ram and A. Ramdas, *On stopping times of power-one sequential tests:
  tight lower and upper bounds*, arXiv:2504.19952v2, Theorem 4.1.
* [Gut09] A. Gut, *Stopped Random Walks: Limit Theorems and Applications*, 2nd edition, Springer,
  2009, Chapter 3.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}

/-- **The expected number of observations of the test of the product of the numeraires**
[ARR26, Theorem 4.1]. Let `S₁` be a null of measures of mass at most `1`, `Q₁` a probability
measure, and `D = maxEPower Q₁ S₁ > 0` the expected logarithm of the numeraire
`X* = numeraire Q₁ S₁`. Under the i.i.d. law of `Q₁`, the first time `τ α` at which the product
`∏ k < n, X* (ω k)` reaches `α⁻¹` satisfies `𝔼[τ α] / log (1/α) → 1 / D` as `α → 0`. The rate
`D` may be `⊤`, where the limit is `0`. -/
theorem tendsto_lintegral_hittingAfter_prod_numeraire_div_log (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) (hpos : 0 < maxEPower Q₁ S₁) :
    Tendsto (fun α ↦ (∫⁻ ω, ENat.toENNReal (hittingAfter
        (fun n ω ↦ ∏ k ∈ Finset.range n, numeraire Q₁ S₁ (ω k)) (Set.Ici α⁻¹) 0 ω)
        ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)) / (ENNReal.log α⁻¹).toENNReal) (𝓝[>] 0)
      (𝓝 (maxEPower Q₁ S₁).toENNReal⁻¹) := by
  have hXm := measurable_numeraire Q₁ S₁
  -- the expected logarithm of the numeraire of the first coordinate is the largest e-power
  have hD : ∫ᵉ ω, ENNReal.log (numeraire Q₁ S₁ (ω 0)) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) =
      maxEPower Q₁ S₁ := by
    rw [← eintegral_map hXm.ennreal_log (measurable_pi_apply 0),
      (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ Q₁) 0).map_eq,
      maxEPower_eq_eintegral_numeraire hS₁]
  -- the numeraires of the coordinates are i.i.d. under the i.i.d. law of `Q₁`
  have h := iIndepFun.tendsto_lintegral_hittingAfter_prod_div_log
    (X := fun k (ω : ℕ → 𝓧) ↦ numeraire Q₁ S₁ (ω k)) (iIndepFun_infinitePi fun _ ↦ hXm)
    (fun j ↦ hXm.comp (measurable_pi_apply j))
    (fun j ↦ (Measure.identDistrib_eval_infinitePi Q₁ j 0).comp hXm) (hD ▸ hpos)
  rwa [hD] at h

/-- **The lower bound on expected stopping times at the rate of the numeraire.** If the bipolar
rate of `Q₁` against a null `S₁` of probability measures is at most the expected logarithm
`D = maxEPower Q₁ S₁` of the numeraire, every sequential test of level `α` for the i.i.d. laws of
the members of `S₁` makes at least `log (1/α) / D` observations in expectation under the i.i.d.
law of `Q₁`. The hypothesis holds when `KL_inf(Q₁, S₁) ≤ D`, as for a simple null, since the
bipolar rate is at most `KL_inf(Q₁, S₁)` (`bipolarRate_le_klInf`). Then `D` is the bipolar rate,
and with `tendsto_lintegral_hittingAfter_prod_numeraire_div_log` the test of the product of the
numeraires attains this bound to first order as `α → 0`. -/
theorem toENNReal_log_inv_div_maxEPower_le_lintegral (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (h : bipolarRate Q₁ S₁ ≤ maxEPower Q₁ S₁)
    {τ : (ℕ → 𝓧) → WithTop ℕ} {α : ℝ≥0∞}
    (hτ : IsLevelStoppingTime τ Filtration.piLT (iidNull S₁) α) :
    (ENNReal.log α⁻¹).toENNReal / (maxEPower Q₁ S₁).toENNReal ≤
      ∫⁻ ω, ENat.toENNReal (τ ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by
  -- `D ≤ d ≤ D`
  have hd : bipolarRate Q₁ S₁ = maxEPower Q₁ S₁ :=
    le_antisymm h (maxLogGrowth_one Q₁ S₁ ▸ maxLogGrowth_one_le_bipolarRate Q₁ S₁)
  exact hd ▸ toENNReal_log_inv_div_bipolarRate_le_lintegral Q₁ hS₁ hτ

end ProbabilityTheory
