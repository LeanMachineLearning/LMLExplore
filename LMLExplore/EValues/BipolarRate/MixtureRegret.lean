/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Statlib.EValues.NumeraireExistence
import LMLExplore.Data.EReal.Inv
import LMLExplore.EValues.Numeraire
import LMLExplore.InformationTheory.KullbackLeibler.Convex
import LMLExplore.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# The regret of the mixture numeraires, and their growth in expectation

Let `S₁` be a set of measures of mass at most one on `𝓧` (the null), and `ν` a finite measure on
the measures on `𝓧` that charges only probability measures (a prior on the alternatives). Write
`W n` for Statlib's `numeraire` of the `n`-sample null `{P ^ n | P ∈ S₁}` under the mixture
`∫ Q' ^ n ν(dQ')`, that is `ν.bind fun Q' ↦ Q' ^ n`. This file bounds the regret of `W n` under an
alternative `Q₁`: the largest expected logarithm `maxLogGrowth Q₁ S₁ n` of an `n`-sample e-variable
exceeds the expected logarithm of `W n` under `Q₁ ^ n` by at most
`log (ν univ / ν B) + n (ν B)⁻¹ ∫_B KL(Q₁ ‖ Q') ν(dQ')`, for every `n` and every set `B` of
alternatives charged by `ν` [EVR26, Note 14, Theorem (1)]. An atom of `ν` at `Q₁` costs at most
`log (ν univ / ν {Q₁})` at every `n`. When `ν` charges every Kullback–Leibler neighbourhood of `Q₁`,
the bound on these neighbourhoods gives that `(1/n)` times the expected logarithm of `W n` tends to
the bipolar rate `bipolarRate Q₁ S₁`, also when it is infinite [EVR26, Note 14, Theorem (2)]: the
asymptotic log-optimality in expectation of the mixture numeraires that [RW, Chapter 6]
conjectures, with the rate of [RR26]. The almost sure form is
`ProbabilityTheory.ae_tendsto_log_numeraire_bind_div_bipolarRate`.

The regret bound comes from a general bound for the numeraire `numeraire Q T` of any null `T` of
measures of mass at most one under a finite measure `Q`,
`ProbabilityTheory.eintegral_log_le_eintegral_log_numeraire_add` in `LMLExplore.EValues.Numeraire`:
for probability measures `μ` and `R` with `R ≤ c • Q` and `KL(μ ‖ R) < ∞`, every e-variable `Y`
for `T` has `∫ log Y dμ ≤ ∫ log (numeraire Q T) dμ + log (c Q(univ)) + KL(μ ‖ R)`. For the mixtures,
`R` is the mixture over `B` alone, `c = (ν B)⁻¹`, and the relative entropy from `Q₁ ^ n` to `R` is
at most `n` times the average divergence over `B`, by the convexity of the relative entropy in
its second argument (`InformationTheory.klDiv_bind_le_lintegral`).

## Main statements

* `ProbabilityTheory.maxLogGrowth_le_eintegral_log_numeraire_bind_add`: the regret of the
  mixture numeraire [EVR26, Note 14, Theorem (1)].
* `ProbabilityTheory.maxLogGrowth_le_eintegral_log_numeraire_bind_add_log`: the regret at an atom
  of the prior.
* `ProbabilityTheory.tendsto_eintegral_log_numeraire_bind_div_bipolarRate`: the growth in
  expectation of the mixture numeraires [EVR26, Note 14, Theorem (2)].

## Implementation notes

The prior `ν` is a finite measure with `∀ᵐ Q' ∂ν, IsProbabilityMeasure Q'`, as in
`LMLExplore.EValues.BipolarRate.MixtureNumeraire`; for a probability measure `ν` the term
`log (ν univ / ν B)` is `log (1 / ν B)`. The set `B` need not be measurable: `ν B` is an outer
measure and the average over `B` a lower integral, so that no measurability of
`Q' ↦ klDiv Q₁ Q'` is assumed, nor of `Q' ↦ Q' ^ n`, which is almost everywhere measurable
(`MeasureTheory.Measure.aemeasurable_pi_self`). The bound is stated for `maxLogGrowth`, so that it
needs no finiteness of the best expected logarithm.

The statements and proofs are adapted from `EValuesResearch/Results/Numeraire.lean`,
`EValuesResearch/Results/UniversalExamples.lean` and
`EValuesResearch/Results/UniversalExamplesAux.lean` (commit `83205cb`) in the paper project
`RemyDegenne/evalues_research`, which formalize [EVR26, Note 14, Theorems (1) and (2)], rewritten
on the API of LMLExplore.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6: Chapter 6.
* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 14, *Asymptotic log-optimality of the mixture numeraire*,
  Theorems (1) and (2).
-/

public section

open MeasureTheory Filter InformationTheory
open scoped ENNReal Topology

namespace ProbabilityTheory

/-! ### The regret of the mixture numeraire -/

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}

/-- **The regret of the mixture numeraire** [EVR26, Note 14, Theorem (1)]. Let `ν` be a finite
measure on the measures on `𝓧` that charges only probability measures, and `B` a set of them with
`ν B ≠ 0` (an outer measure; `B` need not be measurable) and `∫⁻ Q' in B, klDiv Q₁ Q' ∂ν ≠ ∞`.
For every `n`, the largest expected logarithm `maxLogGrowth Q₁ S₁ n` of an `n`-sample e-variable
under `Q₁ ^ n` is at most the expected logarithm of the numeraire of the `n`-sample null under the
mixture `∫ Q' ^ n ν(dQ')`, plus `log (ν univ / ν B)` and `n` times the average over `B` of the
relative entropy from `Q₁`. For a probability measure `ν` the middle term is `log (1 / ν B)`.
The members of `S₁` need only have mass at most `1`. -/
theorem maxLogGrowth_le_eintegral_log_numeraire_bind_add (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) (ν : Measure (Measure 𝓧)) [IsFiniteMeasure ν]
    (hν : ∀ᵐ Q' ∂ν, IsProbabilityMeasure Q') {B : Set (Measure 𝓧)} (hB : ν B ≠ 0)
    (hKL : ∫⁻ Q' in B, klDiv Q₁ Q' ∂ν ≠ ∞) (n : ℕ) :
    maxLogGrowth Q₁ S₁ n ≤
      ∫ᵉ x, ENNReal.log (numeraire (ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q')
        (sampleNull S₁ n) x) ∂Measure.pi (fun _ : Fin n ↦ Q₁) +
      ENNReal.log (ν .univ / ν B) +
      n * (((ν B)⁻¹ * ∫⁻ Q' in B, klDiv Q₁ Q' ∂ν : ℝ≥0∞) : EReal) := by
  set κ : Measure 𝓧 → Measure (Fin n → 𝓧) := fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q'
  have hκ : AEMeasurable κ ν := Measure.aemeasurable_pi_self (hν.mono fun _ _ ↦ inferInstance)
  have hκp : ∀ᵐ Q' ∂ν, IsProbabilityMeasure (κ Q') := hν.mono fun Q' _ ↦ by
    simp only [κ]
    infer_instance
  have hQbar : ν.bind κ .univ = ν .univ := by
    rw [Measure.bind_apply .univ hκ, ← lintegral_one]
    exact lintegral_congr_ae (hκp.mono fun _ _ ↦ measure_univ)
  have : IsFiniteMeasure (ν.bind κ) := ⟨by rw [hQbar]; exact measure_lt_top ν _⟩
  -- the mixture `R` over `B`, a probability measure dominated by `(ν B)⁻¹ • ν.bind κ`
  set π : Measure (Measure 𝓧) := (ν B)⁻¹ • ν.restrict B with hπ_def
  have hπ : IsProbabilityMeasure π :=
    ⟨by simp [π, ENNReal.inv_mul_cancel hB (measure_ne_top ν B)]⟩
  have hκπ : AEMeasurable κ π := hκ.restrict.smul_measure _
  have hR : IsProbabilityMeasure (π.bind κ) :=
    isProbabilityMeasure_bind hκπ (Measure.ae_smul_measure (ae_restrict_of_ae hκp) _)
  have hRQ : π.bind κ ≤ (ν B)⁻¹ • ν.bind κ := by
    rw [← Measure.bind_smul _ _ hκ]
    refine Measure.bind_mono_left (hκ.smul_measure _) ?_
    rw [hπ_def]
    gcongr
    exact Measure.restrict_le_self
  -- the relative entropy from `Q₁ ^ n` to `R`, by convexity
  have hKLR : klDiv (Measure.pi fun _ : Fin n ↦ Q₁) (π.bind κ) ≤
      n * ((ν B)⁻¹ * ∫⁻ Q' in B, klDiv Q₁ Q' ∂ν) := by
    calc klDiv (Measure.pi fun _ : Fin n ↦ Q₁) (π.bind κ)
    _ ≤ ∫⁻ Q', klDiv (Measure.pi fun _ : Fin n ↦ Q₁) (κ Q') ∂π := klDiv_bind_le_lintegral hκπ
    _ = (ν B)⁻¹ * ∫⁻ Q' in B, n * klDiv Q₁ Q' ∂ν := by
      rw [lintegral_smul_measure, smul_eq_mul]
      congr 1
      refine lintegral_congr_ae ((ae_restrict_of_ae hν).mono fun Q' _ ↦ ?_)
      simp only [κ, klDiv_pi_const, Fintype.card_fin]
    _ = n * ((ν B)⁻¹ * ∫⁻ Q' in B, klDiv Q₁ Q' ∂ν) := by
      rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n), mul_left_comm]
  have hKLfin : klDiv (Measure.pi fun _ : Fin n ↦ Q₁) (π.bind κ) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n)
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hB) hKL)) hKLR
  -- the bound for every `n`-sample e-variable, from the regret of the numeraire against `R`
  rw [maxLogGrowth_def, maxEPower_le_iff]
  intro Y hY
  have h := eintegral_log_le_eintegral_log_numeraire_add
    (measure_univ_le_one_of_mem_sampleNull hS₁ n) (ENNReal.inv_ne_top.2 hB) hRQ hKLfin hY
  rw [hQbar, ← ENNReal.div_eq_inv_mul] at h
  refine h.trans (add_le_add le_rfl ?_)
  rw [← ENNReal.toEReal_natCast, ← EReal.coe_ennreal_mul]
  exact EReal.coe_ennreal_le_coe_ennreal_iff.2 hKLR

/-- **The regret of the mixture numeraire at an atom of the prior.** If the finite measure `ν`
on the probability measures has an atom at `Q₁`, then for every `n` the largest expected
logarithm `maxLogGrowth Q₁ S₁ n` of an `n`-sample e-variable exceeds the expected logarithm of the
numeraire against the mixture `∫ Q' ^ n ν(dQ')` by at most `log (ν univ / ν {Q₁})`
[EVR26, Note 14, Theorem (1)]. -/
theorem maxLogGrowth_le_eintegral_log_numeraire_bind_add_log (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) (ν : Measure (Measure 𝓧))
    [IsFiniteMeasure ν] (hν : ∀ᵐ Q' ∂ν, IsProbabilityMeasure Q') (hQ₁ : ν {Q₁} ≠ 0) (n : ℕ) :
    maxLogGrowth Q₁ S₁ n ≤
      ∫ᵉ x, ENNReal.log (numeraire (ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q')
        (sampleNull S₁ n) x) ∂Measure.pi (fun _ : Fin n ↦ Q₁) +
      ENNReal.log (ν .univ / ν {Q₁}) := by
  have h0 : ∫⁻ Q' in {Q₁}, klDiv Q₁ Q' ∂ν = 0 := by
    refine le_antisymm ((setLIntegral_mono (g := fun _ ↦ 0) measurable_const
      fun Q' hQ' ↦ ?_).trans_eq lintegral_zero) zero_le
    rw [Set.mem_singleton_iff.1 hQ', klDiv_self]
  have h := maxLogGrowth_le_eintegral_log_numeraire_bind_add Q₁ hS₁ ν hν hQ₁
    (by rw [h0]; exact ENNReal.zero_ne_top) n
  rwa [h0, mul_zero, EReal.coe_ennreal_zero, mul_zero, add_zero] at h

/-! ### The growth in expectation of the mixture numeraires -/

/-- **The mixture numeraires grow at the bipolar rate in expectation** [EVR26, Note 14,
Theorem (2)]. Let `ν` be a finite measure on the measures on `𝓧` that charges only probability
measures and every Kullback–Leibler neighbourhood `{Q' | klDiv Q₁ Q' ≤ ε}`, `ε > 0`, of `Q₁`. The
expected logarithm under `Q₁ ^ n` of the numeraire of the `n`-sample null under the mixture
`∫ Q' ^ n ν(dQ')`, divided by `n`, tends to `bipolarRate Q₁ S₁`, also when the bipolar rate is
infinite. The neighbourhoods need not be measurable, and the members of `S₁` need only have mass at
most `1`. -/
theorem tendsto_eintegral_log_numeraire_bind_div_bipolarRate (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) (ν : Measure (Measure 𝓧))
    [IsFiniteMeasure ν] (hν : ∀ᵐ Q' ∂ν, IsProbabilityMeasure Q')
    (hν_supp : ∀ ε : ℝ≥0∞, 0 < ε → ν {Q' | klDiv Q₁ Q' ≤ ε} ≠ 0) :
    Tendsto (fun n : ℕ ↦ (∫ᵉ x, ENNReal.log (numeraire
        (ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q') (sampleNull S₁ n) x)
        ∂Measure.pi (fun _ : Fin n ↦ Q₁)) / (n : EReal)) atTop (𝓝 (bipolarRate Q₁ S₁)) := by
  set E : ℕ → EReal := fun n ↦ ∫ᵉ x, ENNReal.log (numeraire
    (ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q') (sampleNull S₁ n) x)
    ∂Measure.pi (fun _ : Fin n ↦ Q₁)
  have ha := tendsto_maxLogGrowth_div_bipolarRate Q₁ hS₁
  -- the regret bound on the neighbourhood of radius `ε`
  have hreg (ε : ℝ) (hε : 0 < ε) :
      ∃ l : ℝ, ∀ n : ℕ, maxLogGrowth Q₁ S₁ n ≤ E n + ((l + n * ε : ℝ) : EReal) := by
    set B := {Q' | klDiv Q₁ Q' ≤ ENNReal.ofReal ε}
    have hB : ν B ≠ 0 := hν_supp _ (ENNReal.ofReal_pos.2 hε)
    have hle : ∫⁻ Q' in B, klDiv Q₁ Q' ∂ν ≤ ENNReal.ofReal ε * ν B :=
      (setLIntegral_mono measurable_const fun _ h ↦ h).trans_eq (setLIntegral_const _ _)
    have hBε : (ν B)⁻¹ * ∫⁻ Q' in B, klDiv Q₁ Q' ∂ν ≤ ENNReal.ofReal ε := by
      calc (ν B)⁻¹ * ∫⁻ Q' in B, klDiv Q₁ Q' ∂ν
      _ ≤ (ν B)⁻¹ * (ENNReal.ofReal ε * ν B) := by gcongr
      _ = ENNReal.ofReal ε := by
        rw [mul_comm, mul_assoc, ENNReal.mul_inv_cancel hB (measure_ne_top _ _), mul_one]
    have hl : ENNReal.log (ν .univ / ν B) = (ENNReal.log (ν .univ / ν B)).toReal :=
      (EReal.coe_toReal (by simpa using ENNReal.div_ne_top (measure_ne_top ν _) hB)
        (by simpa using ENNReal.div_ne_zero.2 ⟨(hB.bot_lt.trans_le (measure_mono
          (Set.subset_univ B))).ne', measure_ne_top ν B⟩)).symm
    refine ⟨(ENNReal.log (ν .univ / ν B)).toReal, fun n ↦
      (maxLogGrowth_le_eintegral_log_numeraire_bind_add Q₁ hS₁ ν hν hB (ne_top_of_le_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν B)) hle) n).trans ?_⟩
    rw [EReal.coe_add, ← add_assoc, ← hl]
    gcongr
    calc (n : EReal) * (((ν B)⁻¹ * ∫⁻ Q' in B, klDiv Q₁ Q' ∂ν : ℝ≥0∞) : EReal)
    _ ≤ (n : EReal) * ((ENNReal.ofReal ε : ℝ≥0∞) : EReal) := by gcongr
    _ = ((n * ε : ℝ) : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left hε.le, EReal.coe_mul, EReal.coe_natCast]
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · -- the lower bound, from the regret bound
    refine le_of_forall_lt_imp_le_of_dense fun a ha' ↦ ?_
    obtain ⟨q, haq, hq⟩ := EReal.lt_iff_exists_real_btwn.1 ha'
    obtain ⟨L, hqL, hL⟩ := EReal.lt_iff_exists_real_btwn.1 hq
    have hqL' : q < L := EReal.coe_lt_coe_iff.1 hqL
    have hε : 0 < (L - q) / 2 := by linarith
    obtain ⟨l, hl⟩ := hreg ((L - q) / 2) hε
    refine haq.le.trans (le_liminf_of_le (by isBoundedDefault) ?_)
    filter_upwards [(tendsto_order.1 ha).1 L hL, eventually_ge_atTop 1,
      (tendsto_natCast_atTop_atTop.atTop_mul_const hε).eventually_ge_atTop l]
      with n hn hn1 hln
    rw [EReal.coe_le_div_natCast_iff hn1]
    have h := ((EReal.coe_lt_div_natCast_iff hn1).1 hn).le.trans (hl n)
    rw [← (EReal.addLECancellable_coe (l + n * ((L - q) / 2))).add_le_add_iff_right]
    refine le_trans ?_ h
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith
  · -- the upper bound: the mixture numeraire is an `n`-sample e-variable
    calc limsup (fun n ↦ E n / n) atTop
    _ ≤ limsup (fun n ↦ maxLogGrowth Q₁ S₁ n / n) atTop := by
      refine limsup_le_limsup (Eventually.of_forall fun n ↦
        EReal.div_le_div_right_of_nonneg (by positivity) ?_)
      rw [maxLogGrowth_def]
      exact IsEVar.eintegral_log_le_maxEPower
        (isEVar_numeraire _ (measure_univ_le_one_of_mem_sampleNull hS₁ n)) _
    _ = bipolarRate Q₁ S₁ := ha.limsup_eq

end ProbabilityTheory
