/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import LMLExplore.Probability.ProductMeasure
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.EValues.BipolarRate.AlmostSure
import LMLExplore.EValues.BipolarRate.EProcess
import LMLExplore.EValues.BipolarRate.Numeraire
import LMLExplore.MeasureTheory.Constructions.Pi
import LMLExplore.Probability.ProductMeasure.MixtureDomination

/-!
# The numeraires against a mixture of i.i.d. alternatives grow at the bipolar rate

Let `S₁` be a set of probability measures on `𝓧` (the null), and `ν` a finite measure on the
measures on `𝓧` that charges only probability measures (a prior on the alternatives). The
observations are the coordinates of `ℕ → 𝓧`, with the i.i.d. laws
`Measure.infinitePi fun _ ↦ P`. Write `W n` for Statlib's `numeraire` of the `n`-sample null
`{P ^ n | P ∈ S₁}` under the mixture `∫ Q' ^ n ν(dQ')`, that is `ν.bind fun Q' ↦ Q' ^ n`: the
log-optimal `n`-sample e-variable against the mixture of the i.i.d. alternatives. If `ν` charges
every Kullback–Leibler neighbourhood `{Q' | klDiv Q₁ Q' ≤ ε}` of a law `Q₁`, then almost surely
under the i.i.d. law of `Q₁`, `(1/n) log (W n)`, at the first `n` observations, tends to the
bipolar rate `bipolarRate Q₁ S₁`, also when it is infinite [EVR26, Note 14]. This is the
asymptotic log-optimality of the mixture numeraires that [RW, Chapter 6] conjectures, with the
rate `bipolarRate Q₁ S₁` of [RR26]: one sequence of `n`-sample e-variables, which does not depend
on `Q₁`, grows at the optimal rate of every alternative in the Kullback–Leibler support of `ν`.
Nothing is assumed on `𝓧`, and nothing on `S₁` besides that its members are probability
measures.

The upper bound holds for every sequence of `n`-sample e-variables
(`ProbabilityTheory.ae_limsup_log_div_le_bipolarRate`). For the lower bound, it is enough that
`W` keeps up with every sequence of `n`-sample e-variables `M n`: almost surely,
`log (M n) ≤ log (W n) + n ε` for all large `n`, for every `ε > 0`
(`ProbabilityTheory.ae_bipolarRate_le_liminf_log_div_of_forall_ae_eventually_log_le`).

* **The ratio to the mixture numeraire.** `M n / W n` has mean at most the mass of `ν` under the
  mixture, by the defining property of the numeraire.
* **Subexponential growth.** Functions of bounded mean under the mixtures are eventually at most
  `exp (n ε)`, almost surely under the i.i.d. law of `Q₁`
  (`ProbabilityTheory.ae_eventually_le_exp_of_lintegral_bind_le`): the mixture dominates an
  exponential density with respect to `Q₁ ^ n`, as in Barron's argument for the consistency of
  posterior distributions [Bar88], [BSW99].

## Main statements

* `ProbabilityTheory.ae_tendsto_log_numeraire_bind_div_bipolarRate`: the logarithm of the
  numeraire against the mixture, divided by `n`, tends to the bipolar rate almost surely.
* `ProbabilityTheory.ae_eventually_log_le_log_numeraire_bind_add`: the numeraire against the
  mixture keeps up with every sequence of `n`-sample e-variables, up to a factor `exp (n ε)`.

## Implementation notes

The mixture is `ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q'`, with `ν` a finite measure on
`Measure 𝓧` such that almost every `Q'` is a probability measure. No measurability of
`Q' ↦ Measure.pi fun _ : Fin n ↦ Q'` is assumed: it is almost everywhere measurable
(`MeasureTheory.Measure.aemeasurable_pi_self`), which makes the bind the mixture. The neighbourhoods
`{Q' | klDiv Q₁ Q' ≤ ε}` need not be measurable; `ν` of them is an outer measure.

The statements and proofs are adapted from `EValuesResearch/Results/Numeraire.lean`,
`EValuesResearch/Results/NumeraireBarronAux.lean` and
`EValuesResearch/Results/NumeraireTrimAux.lean` (commit `dd4072f`) in the paper project
`RemyDegenne/evalues_research`, which formalize [EVR26, Note 14, Theorem (2)], rewritten on the
API of LMLExplore. There the comparison of the mixture numeraire with every sequence of bets is
proved directly; here it goes through the general subexponential growth of functions of bounded
mean under the mixtures, in `LMLExplore.Probability.ProductMeasure.MixtureDomination`.

## References

* [Bar88] A. R. Barron, *The exponential convergence of posterior probabilities with implications
  for Bayes estimators of density functions*, Technical report, Department of Statistics,
  University of Illinois at Urbana-Champaign, 1988.
* [BSW99] A. Barron, M. J. Schervish and L. Wasserman, *The consistency of posterior distributions
  in nonparametric problems*, Annals of Statistics 27 (1999), 536–561.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6: Chapter 6.
* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 14, *Asymptotic log-optimality of the mixture numeraire*,
  Theorem (2).
-/

public section

open MeasureTheory Filter InformationTheory
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}

/-- **The numeraire against a mixture keeps up with every sequence of `n`-sample e-variables.**
Let `ν` be a finite measure on the measures on `𝓧` that charges only probability measures and
every Kullback–Leibler neighbourhood `{Q' | klDiv Q₁ Q' ≤ ε}` of `Q₁`. For every sequence of
e-variables `M n` for the `n`-fold products of the members of `S₁` and every `ε > 0`, almost
surely under the i.i.d. law of `Q₁`, eventually `log (M n) ≤ log (W n) + n ε` at the first `n`
observations, where `W n` is Statlib's `numeraire` of the `n`-sample null under the mixture
`∫ Q' ^ n ν(dQ')` [EVR26, Note 14]. The ratio `M n / W n` has mean at most `ν univ` under the
mixture, so it is eventually at most `exp (n ε)`, since functions of bounded mean under the
mixtures grow subexponentially (`ProbabilityTheory.ae_eventually_le_exp_of_lintegral_bind_le`,
Barron's argument [Bar88], [BSW99]). The members of `S₁` need only have mass at most `1`. If `Q₁` is
not a probability measure, its i.i.d. law is `0` and the statement holds trivially. -/
theorem ae_eventually_log_le_log_numeraire_bind_add (Q₁ : Measure 𝓧)
    (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) (ν : Measure (Measure 𝓧)) [IsFiniteMeasure ν]
    (hν : ∀ᵐ Q' ∂ν, IsProbabilityMeasure Q')
    (hν_supp : ∀ ε : ℝ≥0∞, 0 < ε → ν {Q' | klDiv Q₁ Q' ≤ ε} ≠ 0)
    {M : (n : ℕ) → (Fin n → 𝓧) → ℝ≥0∞}
    (hM : ∀ n, IsEVar (M n) ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁)) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
      ENNReal.log (M n (initSeg n ω)) ≤ ENNReal.log (numeraire
        (ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q')
        ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) (initSeg n ω)) + ((n * ε : ℝ) : EReal) := by
  by_cases hQ : IsProbabilityMeasure Q₁
  swap
  · exact Measure.ae_infinitePi_of_not_isProbabilityMeasure (i := 0) hQ
  -- the ratios to the mixture numeraires have mean at most `ν univ` under the mixtures
  have hbound (n : ℕ) : ∫⁻ x, M n x / numeraire (ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q')
      ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) x
        ∂(ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q') ≤ ν .univ := by
    calc _ ≤ (ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q') .univ :=
          lintegral_div_numeraire_le_measure_univ _ (measure_univ_le_one_of_mem_image_pi hS₁ n)
            (hM n)
    _ = ν .univ := by
      rw [Measure.bind_apply .univ
        (Measure.aemeasurable_pi_self (hν.mono fun _ _ ↦ inferInstance)), ← lintegral_one]
      exact lintegral_congr_ae (hν.mono fun Q' hQ' ↦ measure_univ)
  -- they grow subexponentially
  filter_upwards [ae_eventually_le_exp_of_lintegral_bind_le Q₁ ν hν hν_supp
    (fun n ↦ (hM n).measurable.div (measurable_numeraire _ _)) (measure_ne_top ν .univ) hbound
    hε] with ω hω
  filter_upwards [hω] with n hn
  exact ENNReal.log_le_log_add_of_div_le hn

/-- **The numeraires against a mixture of i.i.d. alternatives grow at the bipolar rate, almost
surely.** Let `ν` be a finite measure on the measures on `𝓧` that charges only probability
measures and every Kullback–Leibler neighbourhood `{Q' | klDiv Q₁ Q' ≤ ε}`, `ε > 0`, of `Q₁`.
Almost surely under the i.i.d. law of `Q₁`, the logarithm of the numeraire of the `n`-sample null
under the mixture `∫ Q' ^ n ν(dQ')`, at the first `n` observations, divided by `n`, tends to
`bipolarRate Q₁ S₁`, also when the bipolar rate is infinite [EVR26, Note 14]: the asymptotic
log-optimality of the mixture numeraires that [RW, Chapter 6] conjectures, with the rate
`bipolarRate Q₁ S₁` of [RR26]. The upper bound holds for every sequence of `n`-sample
e-variables (`ProbabilityTheory.ae_limsup_log_div_le_bipolarRate`), and the lower bound follows
from the comparison with every sequence of `n`-sample e-variables
(`ProbabilityTheory.ae_eventually_log_le_log_numeraire_bind_add`). No assumption is made on `𝓧`.
If `Q₁` is not a probability measure, its i.i.d. law is `0` and the statement holds trivially. -/
theorem ae_tendsto_log_numeraire_bind_div_bipolarRate (Q₁ : Measure 𝓧)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (ν : Measure (Measure 𝓧)) [IsFiniteMeasure ν]
    (hν : ∀ᵐ Q' ∂ν, IsProbabilityMeasure Q')
    (hν_supp : ∀ ε : ℝ≥0∞, 0 < ε → ν {Q' | klDiv Q₁ Q' ≤ ε} ≠ 0) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      Tendsto (fun n : ℕ ↦ ENNReal.log (numeraire (ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q')
        ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) (initSeg n ω)) / (n : EReal)) atTop
        (𝓝 (bipolarRate Q₁ S₁)) := by
  by_cases hQ : IsProbabilityMeasure Q₁
  swap
  · exact Measure.ae_infinitePi_of_not_isProbabilityMeasure (i := 0) hQ
  have := nonempty_of_isProbabilityMeasure Q₁
  filter_upwards [ae_limsup_log_div_le_bipolarRate Q₁ hS₁ fun n ↦ isEVar_numeraire _
      (measure_univ_le_one_of_mem_image_pi (fun P hP ↦ (hS₁ P hP).measure_univ.le) n),
    ae_bipolarRate_le_liminf_log_div_of_forall_ae_eventually_log_le Q₁ hS₁
      (T := fun n ω ↦ numeraire (ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q')
        ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) (initSeg n ω))
      fun F hF hFn h_null ε hε ↦ by
        choose G hG hFG using fun n ↦
          exists_isEVar_eq_comp_initSeg hS₁ (hF n) (hFn n) fun P hP ↦ h_null P hP n
        filter_upwards [ae_eventually_log_le_log_numeraire_bind_add Q₁
          (fun P hP ↦ (hS₁ P hP).measure_univ.le) ν hν hν_supp hG hε] with ω hω
        filter_upwards [hω] with n hn
        rw [hFG n]
        exact hn]
    with ω hsup hinf
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup

end ProbabilityTheory
