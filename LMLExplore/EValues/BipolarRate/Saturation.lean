/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
import LMLExplore.Data.EReal.BigOperators
import LMLExplore.EValues.EffectiveSet.Basic
import LMLExplore.MeasureTheory.Constructions.Pi
import LMLExplore.MeasureTheory.Integral.EReal
import LMLExplore.MeasureTheory.Integral.MeanInequalities
import LMLExplore.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Data.EReal.BigOperators
import TauCeti.MeasureTheory.Measure.PiWithDensity

/-!
# The i.i.d. saturation of a null

Let `S₁` be a null hypothesis on `𝓧`, a set of measures. A function of `n` observations is an
e-variable for the `n`-sample null `sampleNull S₁ n` exactly when it is one for the effective null
`effectiveSet (sampleNull S₁ n)`, the measures under which every such e-variable has expectation
at most `1`. The **i.i.d. saturation** `iidSaturation S₁` is the set of the finite measures `R` on
`𝓧` whose `n`-fold products `R ^ n` are in the effective null of the `n`-sample null for every
`n ≥ 1` [EVR26, Note 43]: under the `n`-fold product of a member, no level-`α` test for the
`n`-sample null has an expectation larger than `α` (`exists_powered_test_iff`), for any `n`.

The saturation contains `S₁` when the members of `S₁` are finite measures, is solid, and its
members have mass at most one when those of `S₁` have. It is closed under geometric mixtures: if
the measures `ρ.withDensity (s i)` are in it, `ρ` σ-finite, and the weights `w i ≥ 0` sum to one,
then so is `ρ.withDensity (∏ i, s i ^ w i)`. On `n` observations its density is the geometric
mixture of the densities of the `n`-fold products, and Hölder's inequality bounds the expectation
of an `n`-sample e-variable under it by the weighted geometric mean of its expectations under the
products. Along geometric mixtures the divergence `klIntegral Q` is affine, since the
log-likelihood ratios are (`llr_withDensity_ae_eq`).

For a null of probability measures, the `n`-sample nulls of `S₁` and of the probability measures
of its saturation have the same e-variables, for every `n`. For a probability measure `Q₁` and a
null of measures of mass at most one, the bipolar rate `d = bipolarRate Q₁ S₁` is at most
`klIntegral Q₁ R` for every member `R` of the saturation, since `R ^ n` is in the effective null
of the `n`-sample null and the growth of the simple null `{R}` is `n * klIntegral Q₁ R`
(`maxLogGrowth_singleton`). The rate is zero exactly when `Q₁` is in the saturation, since the
largest e-power under a probability measure vanishes exactly on the effective null
(`maxEPower_eq_zero_iff_mem_effectiveSet`): this is the case of one alternative of
[RR26, Theorem 3.14], written with the saturation.

## Main definitions

* `ProbabilityTheory.iidSaturation S₁`: the i.i.d. saturation of the null `S₁`.

## Main statements

* `ProbabilityTheory.subset_iidSaturation`, `ProbabilityTheory.isLowerSet_iidSaturation`,
  `ProbabilityTheory.measure_univ_le_one_of_mem_iidSaturation`: the saturation contains a null of
  finite measures, is solid, and has members of mass at most one when the null has.
* `ProbabilityTheory.withDensity_prod_rpow_mem_iidSaturation`: the saturation is closed under
  geometric mixtures.
* `ProbabilityTheory.klIntegral_withDensity_prod_rpow`: `klIntegral Q` is affine along geometric
  mixtures.
* `ProbabilityTheory.isEVar_sampleNull_iidSaturation_iff`: the `n`-sample nulls of a null of
  probability measures and of the probability measures of its saturation have the same
  e-variables.
* `ProbabilityTheory.bipolarRate_le_klIntegral_of_mem_iidSaturation`,
  `ProbabilityTheory.bipolarRate_le_klInf_iidSaturation`: the bipolar rate is at most the
  divergence to every member of the saturation.
* `ProbabilityTheory.bipolarRate_eq_zero_iff_mem_iidSaturation`: the bipolar rate is zero exactly
  when the alternative is in the saturation [RR26, Theorem 3.14].

## Implementation notes

As in [EVR26, Note 43], the saturation is a set of finite measures, not of probability measures,
and `n = 0` is excluded from its definition. The divergence is Statlib's `klIntegral`, with no
correction for the mass: Mathlib's `klDiv Q₁ R` is smaller by the missing mass `1 - R univ`, and
the bipolar rate can exceed it on a member of mass below one [EVR26, Note 43, Example 3].
The statements and proofs are adapted from `EValuesResearch/Results/PartitionRate.lean`,
`EValuesResearch/Results/Saturation.lean`, `EValuesResearch/Results/SaturationAux.lean` and
`EValuesResearch/Results/CountableAlphabetRate.lean` (commit `83205cb`) in the paper project
`RemyDegenne/evalues_research`, which formalize [EVR26, Note 43, Proposition 1], rewritten on the
API of LMLExplore.

## References

* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes and the Lean
  library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and refereed
  by AI agents: Note 43, *Is the bipolar rate `KL_inf` to the i.i.d. saturation?*, Proposition 1.
-/

public section

open MeasureTheory InformationTheory Filter Set
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {P R R' : Measure 𝓧} {S₁ : Set (Measure 𝓧)}

/-! ### The saturation -/

/-- The i.i.d. saturation of a null `S₁`: the finite measures `R` on `𝓧` whose `n`-fold products
`Measure.pi fun _ : Fin n ↦ R` are in the effective null of the `n`-sample null
`sampleNull S₁ n`, for every `n ≥ 1` [EVR26, Note 43]: every `n`-sample e-variable for `S₁` has
expectation at most one under `Measure.pi fun _ : Fin n ↦ R`. -/
noncomputable def iidSaturation (S₁ : Set (Measure 𝓧)) : Set (Measure 𝓧) :=
  {R | IsFiniteMeasure R ∧
    ∀ n ≠ 0, (Measure.pi fun _ : Fin n ↦ R) ∈ effectiveSet (sampleNull S₁ n)}

/-- A measure is in the i.i.d. saturation of `S₁` exactly when it is finite and its `n`-fold
products are in the effective nulls of the `n`-sample nulls, for every `n ≥ 1`. -/
theorem mem_iidSaturation_iff : R ∈ iidSaturation S₁ ↔ IsFiniteMeasure R ∧
    ∀ n ≠ 0, (Measure.pi fun _ : Fin n ↦ R) ∈ effectiveSet (sampleNull S₁ n) :=
  Iff.rfl

/-- A null of finite measures is contained in its i.i.d. saturation [EVR26, Note 43,
Proposition 1]. -/
theorem subset_iidSaturation (hS₁ : ∀ P ∈ S₁, IsFiniteMeasure P) : S₁ ⊆ iidSaturation S₁ :=
  fun P hP ↦ ⟨hS₁ P hP, fun _ _ ↦ subset_effectiveSet (pi_mem_sampleNull hP)⟩

/-- **The i.i.d. saturation is solid** [EVR26, Note 43, Proposition 1]: a measure below a member
is a member, as the effective nulls are solid and the product of finite measures is monotone. -/
theorem isLowerSet_iidSaturation : IsLowerSet (iidSaturation S₁) := by
  intro R R' hR'R hR
  have := hR.1
  exact ⟨isFiniteMeasure_of_le R hR'R, fun n hn ↦
    mem_effectiveSet_of_le (hR.2 n hn) (Measure.pi_mono fun _ ↦ hR'R)⟩

/-- A measure below a member of the i.i.d. saturation is a member. -/
theorem mem_iidSaturation_of_le (hR : R ∈ iidSaturation S₁) (hR' : R' ≤ R) :
    R' ∈ iidSaturation S₁ :=
  isLowerSet_iidSaturation hR' hR

/-- The members of the i.i.d. saturation of a null of measures of mass at most one have mass at
most one: the constant `1` is an e-variable for the `1`-sample null. -/
theorem measure_univ_le_one_of_mem_iidSaturation (hS₁ : ∀ P ∈ S₁, P univ ≤ 1)
    (hR : R ∈ iidSaturation S₁) : R univ ≤ 1 := by
  have := hR.1
  have h := mem_effectiveSet_iff.1 (hR.2 1 one_ne_zero) 1
    (isEVar_one (measure_univ_le_one_of_mem_sampleNull hS₁ 1))
  simpa [Measure.pi_univ] using h

/-! ### Geometric mixtures -/

section GeometricMixture

variable {ι : Type*} {ρ : Measure 𝓧} {s : ι → 𝓧 → ℝ≥0∞} {t : Finset ι} {w : ι → ℝ}

/-- **The i.i.d. saturation is closed under geometric mixtures** [EVR26, Note 43,
Proposition 1]. If the measures `ρ.withDensity (s i)`, `i ∈ t`, with `ρ` σ-finite, are in the
saturation, and the weights `w i ≥ 0` sum to one, then the measure
`ρ.withDensity (∏ i ∈ t, s i ^ w i)` is in the saturation. Its `n`-fold product has, with respect
to `ρ ^ n`, the geometric mixture of the densities of the `n`-fold products, and Hölder's
inequality (`lintegral_withDensity_prod_rpow_le`) bounds the expectation of an `n`-sample
e-variable under it by the weighted geometric mean of its expectations under the products. -/
theorem withDensity_prod_rpow_mem_iidSaturation [SigmaFinite ρ]
    (hs : ∀ i ∈ t, AEMeasurable (s i) ρ)
    (hsS : ∀ i ∈ t, ρ.withDensity (s i) ∈ iidSaturation S₁) (hw : ∑ i ∈ t, w i = 1)
    (hw0 : ∀ i ∈ t, 0 ≤ w i) :
    ρ.withDensity (fun x ↦ ∏ i ∈ t, s i x ^ w i) ∈ iidSaturation S₁ := by
  have hgm : AEMeasurable (fun x ↦ ∏ i ∈ t, s i x ^ w i) ρ :=
    Finset.aemeasurable_fun_prod _ fun i hi ↦ (hs i hi).pow_const _
  have hG := isFiniteMeasure_withDensity_prod_rpow t hs hw hw0 fun i hi ↦ (hsS i hi).1
  refine ⟨hG, fun n hn ↦ mem_effectiveSet_iff.2 fun X hX ↦ ?_⟩
  -- the densities of the `n`-fold products with respect to `ρ ^ n`
  set D : ι → (Fin n → 𝓧) → ℝ≥0∞ := fun i x ↦ ∏ j, s i (x j)
  have hDm (i : ι) (hi : i ∈ t) : AEMeasurable (D i) (Measure.pi fun _ : Fin n ↦ ρ) :=
    Finset.aemeasurable_fun_prod _ fun j _ ↦
      (hs i hi).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ j)
  have hpi (i : ι) (hi : i ∈ t) : (Measure.pi fun _ : Fin n ↦ ρ.withDensity (s i)) =
      (Measure.pi fun _ : Fin n ↦ ρ).withDensity (D i) := by
    have := (hsS i hi).1
    exact TauCeti.pi_withDensity₀ _ fun _ ↦ hs i hi
  have hpiG : (Measure.pi fun _ : Fin n ↦ ρ.withDensity fun x ↦ ∏ i ∈ t, s i x ^ w i) =
      (Measure.pi fun _ : Fin n ↦ ρ).withDensity fun x ↦ ∏ i ∈ t, D i x ^ w i := by
    rw [TauCeti.pi_withDensity₀ _ fun _ ↦ hgm]
    congr 1
    funext x
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun i hi ↦ ENNReal.prod_rpow_of_nonneg (hw0 i hi)
  rw [hpiG]
  refine (lintegral_withDensity_prod_rpow_le t hDm hw hw0
    hX.measurable.aemeasurable).trans (Finset.prod_le_one fun i hi ↦ ENNReal.rpow_le_one ?_
      (hw0 i hi))
  rw [← hpi i hi]
  exact mem_effectiveSet_iff.1 ((hsS i hi).2 n hn) X hX

/-- **The divergence is affine along geometric mixtures** [EVR26, Note 43, Proposition 1]. For a
finite measure `Q`, finite measures `ρ.withDensity (s i)`, `i ∈ t`, with `ρ` σ-finite, and weights
`w i ≥ 0` summing to one, the divergence from `Q` to the geometric mixture
`ρ.withDensity (∏ i ∈ t, s i ^ w i)` is the mixture
`∑ i ∈ t, w i * klIntegral Q (ρ.withDensity (s i))` of the divergences, with `s ^ 0 = 1` and
`0 * ⊤ = 0`. Both sides are `⊤` when `Q` is not absolutely continuous with respect to a factor of
positive weight; otherwise the log-likelihood ratio against the mixture is the mixture of the
log-likelihood ratios, `Q`-almost everywhere. -/
theorem klIntegral_withDensity_prod_rpow (Q : Measure 𝓧) [IsFiniteMeasure Q] [SigmaFinite ρ]
    (hs : ∀ i ∈ t, AEMeasurable (s i) ρ)
    (hfin : ∀ i ∈ t, IsFiniteMeasure (ρ.withDensity (s i)))
    (hw : ∑ i ∈ t, w i = 1) (hw0 : ∀ i ∈ t, 0 ≤ w i) :
    klIntegral Q (ρ.withDensity fun x ↦ ∏ i ∈ t, s i x ^ w i) =
      ∑ i ∈ t, (w i : EReal) * klIntegral Q (ρ.withDensity (s i)) := by
  classical
  set g : 𝓧 → ℝ≥0∞ := fun x ↦ ∏ i ∈ t, s i x ^ w i with hg_def
  have hgm : AEMeasurable g ρ := Finset.aemeasurable_fun_prod _ fun i hi ↦ (hs i hi).pow_const _
  have hG : IsFiniteMeasure (ρ.withDensity g) :=
    isFiniteMeasure_withDensity_prod_rpow t hs hw hw0 hfin
  -- the terms of the mixture of the divergences are not `⊥`
  have hlow (i : ι) (hi : i ∈ t) : (w i : EReal) * klIntegral Q (ρ.withDensity (s i)) ≠ ⊥ := by
    have := hfin i hi
    have hk : klIntegral Q (ρ.withDensity (s i)) ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) measureReal_univ_sub_le_klIntegral
    exact (EReal.mul_ne_bot _ _).2 ⟨.inl (EReal.coe_ne_bot _), .inr hk, .inl (EReal.coe_ne_top _),
      .inl (EReal.coe_nonneg.2 (hw0 i hi))⟩
  have hs_ne (i : ι) (hi : i ∈ t) : ∀ᵐ x ∂ρ.withDensity (s i), s i x ≠ 0 :=
    (ae_withDensity_iff' (hs i hi)).2 (ae_of_all _ fun _ h ↦ h)
  have hac := absolutelyContinuous_withDensity_prod_rpow_iff t hs hw hw0 (ν := Q)
  by_cases hQG : Q ≪ ρ.withDensity g
  swap
  · -- some factor of positive weight does not dominate `Q`: both sides are `⊤`
    obtain ⟨k, hk, hwk, hQk⟩ : ∃ k ∈ t, 0 < w k ∧ ¬ Q ≪ ρ.withDensity (s k) := by
      by_contra! h
      exact hQG (hac.2 h)
    rw [klIntegral_of_not_ac hQG, ← Finset.add_sum_erase t _ hk, klIntegral_of_not_ac hQk,
      EReal.coe_mul_top_of_pos hwk]
    exact (EReal.top_add_of_ne_bot
      (EReal.sum_ne_bot.2 fun i hi ↦ hlow i (Finset.mem_of_mem_erase hi))).symm
  -- the main case: all the divergences are integrals of log-likelihood ratios
  have hQT : ∀ i ∈ t, 0 < w i → Q ≪ ρ.withDensity (s i) := hac.1 hQG
  have hQρ : Q ≪ ρ := hQG.trans (withDensity_absolutelyContinuous _ _)
  -- the factors of positive weight are positive and finite, `Q`-almost everywhere
  have hpos : ∀ᵐ x ∂Q, ∀ i ∈ t, 0 < w i → s i x ≠ 0 ∧ s i x ≠ ∞ ∧
      llr Q (ρ.withDensity (s i)) x = llr Q ρ x - Real.log (s i x).toReal := by
    rw [eventually_all_finset]
    intro i hi
    by_cases hwi : 0 < w i
    · have := hfin i hi
      have htop : ∀ᵐ x ∂ρ, s i x < ∞ := ae_lt_top' (hs i hi) (by
        rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ]
        exact measure_ne_top _ _)
      filter_upwards [(hQT i hi hwi).ae_le (hs_ne i hi), hQρ.ae_le htop,
        llr_withDensity_ae_eq (hs i hi) (hQT i hi hwi)] with x h1 h2 h3 _ using ⟨h1, h2.ne, h3⟩
    · exact ae_of_all _ fun _ h' ↦ absurd h' hwi
  -- the log-likelihood ratio against the mixture is the mixture of the log-likelihood ratios
  have hsum : ∀ᵐ x ∂Q,
      llr Q (ρ.withDensity g) x = ∑ i ∈ t, w i * llr Q (ρ.withDensity (s i)) x := by
    filter_upwards [llr_withDensity_ae_eq hgm hQG, hpos] with x hGx hp
    have hfac (i : ι) (hi : i ∈ t) :
        Real.log ((s i x ^ w i).toReal) = w i * Real.log (s i x).toReal := by
      rcases (hw0 i hi).eq_or_lt with h | h
      · rw [← h, ENNReal.rpow_zero, ENNReal.toReal_one, Real.log_one, zero_mul]
      · rw [← ENNReal.toReal_rpow,
          Real.log_rpow (ENNReal.toReal_pos (hp i hi h).1 (hp i hi h).2.1)]
    have hlog : Real.log (g x).toReal = ∑ i ∈ t, w i * Real.log (s i x).toReal := by
      rw [hg_def, ENNReal.toReal_prod, Real.log_prod fun i hi ↦ ?_]
      · exact Finset.sum_congr rfl hfac
      rcases (hw0 i hi).eq_or_lt with h | h
      · simp [← h]
      · rw [← ENNReal.toReal_rpow]
        exact (Real.rpow_pos_of_pos
          (ENNReal.toReal_pos (hp i hi h).1 (hp i hi h).2.1) _).ne'
    have hterm (i : ι) (hi : i ∈ t) : w i * llr Q (ρ.withDensity (s i)) x =
        w i * (llr Q ρ x - Real.log (s i x).toReal) := by
      rcases (hw0 i hi).eq_or_lt with h | h
      · rw [← h, zero_mul, zero_mul]
      · rw [(hp i hi h).2.2]
    rw [hGx, hlog, Finset.sum_congr rfl hterm]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul]
  -- integrate
  have hint (i : ι) (hi : i ∈ t) : ∫ᵉ x, ((w i * llr Q (ρ.withDensity (s i)) x : ℝ) : EReal) ∂Q =
      (w i : EReal) * klIntegral Q (ρ.withDensity (s i)) := by
    simp_rw [EReal.coe_mul]
    rw [eintegral_real_const_mul_of_nonneg (hw0 i hi)]
    rcases (hw0 i hi).eq_or_lt with h | h
    · rw [← h, EReal.coe_zero, zero_mul, zero_mul]
    · have := hfin i hi
      rw [klIntegral_eq_eintegral_llr (hQT i hi h)]
  rw [klIntegral_eq_eintegral_llr hQG, eintegral_congr_ae (hsum.mono fun x hx ↦ by rw [hx]),
    eintegral_congr fun x ↦ EReal.coe_finsetSum _ _,
    eintegral_finsetSum (f := fun i x ↦ ((w i * llr Q (ρ.withDensity (s i)) x : ℝ) : EReal)) t
      (fun i _ ↦ (measurable_coe_real_ereal.comp
        (measurable_const.mul (measurable_llr _ _))).aemeasurable)
      fun i hi ↦ by rw [hint i hi]; exact hlow i hi]
  exact Finset.sum_congr rfl hint

end GeometricMixture

/-! ### The e-variables and the bipolar rate -/

/-- **The saturation has the e-variables of the null** [EVR26, Note 43, Proposition 1]. For a null
`S₁` of probability measures and every `n`, a function of `n` observations is an e-variable for
the `n`-sample null of the probability measures of the i.i.d. saturation of `S₁` exactly when it
is one for the `n`-sample null of `S₁`. -/
theorem isEVar_sampleNull_iidSaturation_iff (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {n : ℕ}
    {X : (Fin n → 𝓧) → ℝ≥0∞} :
    IsEVar X (sampleNull {R ∈ iidSaturation S₁ | IsProbabilityMeasure R} n) ↔
      IsEVar X (sampleNull S₁ n) := by
  have hST : S₁ ⊆ {R ∈ iidSaturation S₁ | IsProbabilityMeasure R} := fun P hP ↦
    ⟨subset_iidSaturation (fun P hP ↦ have := hS₁ P hP; inferInstance) hP, hS₁ P hP⟩
  refine ⟨fun hX ↦ hX.anti_set (sampleNull_mono hST n), fun hX ↦ ⟨hX.measurable, ?_⟩⟩
  intro μ hμ
  obtain ⟨R, ⟨hR, hRp⟩, rfl⟩ := mem_sampleNull.1 hμ
  rcases eq_or_ne n 0 with rfl | hn
  · -- with no observation, every product is the same Dirac mass
    obtain ⟨P, hP⟩ : S₁.Nonempty := by
      -- the saturation of the empty null has no member of positive mass
      refine ne_empty_iff_nonempty.1 fun h ↦ ?_
      subst h
      have h1 := mem_effectiveSet_iff.1 (hR.2 1 one_ne_zero) (fun _ ↦ ∞)
        (by rw [sampleNull_empty]; exact isEVar_empty measurable_const)
      simp at h1
    rw [Measure.pi_of_empty, ← Measure.pi_of_empty fun _ : Fin 0 ↦ P]
    exact hX.lintegral_le_one (pi_mem_sampleNull hP)
  · exact mem_effectiveSet_iff.1 (hR.2 n hn) X hX

/-- **The bipolar rate is at most the divergence to every member of the saturation** [EVR26,
Note 43, Proposition 1]. For a probability measure `Q₁` and a null `S₁` of measures of mass at
most one, `bipolarRate Q₁ S₁ ≤ klIntegral Q₁ R` for every member `R` of the i.i.d. saturation:
`R ^ n` is in the effective null of the `n`-sample null, so the growth of `n` observations is at
most that of the simple null `{R}`, which is `n * klIntegral Q₁ R`. -/
theorem bipolarRate_le_klIntegral_of_mem_iidSaturation (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, P univ ≤ 1) (hR : R ∈ iidSaturation S₁) :
    bipolarRate Q₁ S₁ ≤ klIntegral Q₁ R := by
  refine bipolarRate_le_iff.2 fun n hn ↦ ?_
  rw [← maxLogGrowth_singleton Q₁ (measure_univ_le_one_of_mem_iidSaturation hS₁ hR) n,
    maxLogGrowth_def, maxLogGrowth_def, sampleNull_singleton, ← maxEPower_effectiveSet]
  exact maxEPower_anti (singleton_subset_iff.2 (hR.2 n hn))

/-- The bipolar rate is at most the smallest divergence `klInf Q₁ (iidSaturation S₁)` to the
i.i.d. saturation [EVR26, Note 43, Proposition 1]. -/
theorem bipolarRate_le_klInf_iidSaturation (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, P univ ≤ 1) : bipolarRate Q₁ S₁ ≤ klInf Q₁ (iidSaturation S₁) :=
  le_klInf_iff.2 fun _ hR ↦ bipolarRate_le_klIntegral_of_mem_iidSaturation Q₁ hS₁ hR

/-- **The bipolar rate is zero exactly on the saturation** [RR26, Theorem 3.14], [EVR26, Note 43,
Proposition 1]. For a probability measure `Q₁` and a null `S₁` of measures of mass at most one,
`bipolarRate Q₁ S₁ = 0` exactly when `Q₁` is in the i.i.d. saturation of `S₁`, that is, when no
e-variable of any number `n ≥ 1` of observations has expectation larger than one under the
`n`-fold product of `Q₁`. The largest e-power vanishes exactly on the effective null
(`maxEPower_eq_zero_iff_mem_effectiveSet`), and the bipolar rate vanishes exactly when the
largest e-power of every `n`-sample null does. -/
theorem bipolarRate_eq_zero_iff_mem_iidSaturation (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, P univ ≤ 1) :
    bipolarRate Q₁ S₁ = 0 ↔ Q₁ ∈ iidSaturation S₁ := by
  have h (n : ℕ) : maxLogGrowth Q₁ S₁ n = 0 ↔
      (Measure.pi fun _ : Fin n ↦ Q₁) ∈ effectiveSet (sampleNull S₁ n) := by
    rw [maxLogGrowth_def]
    exact maxEPower_eq_zero_iff_mem_effectiveSet (measure_univ_le_one_of_mem_sampleNull hS₁ n)
  rw [mem_iidSaturation_iff]
  constructor
  · intro hd
    refine ⟨inferInstance, fun n hn ↦ (h n).1 (le_antisymm ?_ (maxLogGrowth_nonneg Q₁ hS₁ n))⟩
    simpa [hd] using maxLogGrowth_le_mul_bipolarRate Q₁ S₁ hn
  · rintro ⟨-, hQ⟩
    refine le_antisymm (bipolarRate_le_iff.2 fun n hn ↦ ?_) (bipolarRate_nonneg Q₁ hS₁)
    rw [(h n).2 (hQ n hn), mul_zero]

end ProbabilityTheory
