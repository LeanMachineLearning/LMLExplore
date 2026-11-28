/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Envelope
public import LMLExplore.EValues.Null.Polar
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.InformationTheory.KullbackLeibler.Variational
import LMLExplore.Probability.LargeDeviations.EmpiricalAverage

/-!
# The bipolar rate as an exponent of large deviations

Let `T` be a null hypothesis of probability measures on a measurable space `Ω` and `Q` a measure
on `Ω`. For finitely many bounded measurable functions `g i` on `Ω` and a real `δ`, let `π m`
(`ProbabilityTheory.nbhdUpperProb T Q g δ m`) be the upper probability, the supremum over the
members `P` of `T` of the probabilities under the `m`-fold products `P ^ m`, of the event that the
empirical averages of the `g i` over `m` observations are within `δ` of their means under `Q`:
the event that the empirical measure of the observations lies in the basic neighbourhood of `Q`
given by the `g i` and `δ`, for the topology of the integrals of the bounded measurable
functions. Let `c δ` be the infimum of `klInf R T` over the probability measures `R` of that
neighbourhood (`MeasureTheory.tauNbhdInf`). Then [EVR26, Note 15]:

* `π m ≤ exp (- m c δ)` for every `m` and every `δ`, by the Sanov-type bound
  `ProbabilityTheory.ofReal_exp_mul_measure_pi_le_one`, so that the lower exponent
  `liminf (1/m) log (1 / π m)` is at least `c δ`;
* for `δ' < δ`, the upper exponent `limsup (1/m) log (1 / π m)` is at most `c δ'`: under the
  powers of a law `R` of the smaller neighbourhood the event has probability tending to one, by
  the weak law of large numbers, and a change of measure
  (`InformationTheory.log_inv_measureReal_le_toReal_klDiv_add_one_div`) gives
  `R ^ m (event) * log (1 / P ^ m (event)) ≤ m KL(R, P) + 1` for each member `P`;
* hence the suprema over the basic neighbourhoods of `Q` of the lower and of the upper exponents
  of `π m` are both the neighbourhood envelope `tauEnvelope (fun R ↦ klInf R T) Q`.

For blocks of `n` observations, `T = sampleNull S₁ n` and `Q = Q₁ ^ n`, the envelope is at most
`n * bipolarRate Q₁ S₁` (`ProbabilityTheory.tauEnvelope_le_mul_bipolarRate`), so the exponents
per observation are at most the bipolar rate, and by the variational formula
`ProbabilityTheory.bipolarRate_eq_iSup_tauEnvelope_div` their supremum over the block lengths and
the basic neighbourhoods is the bipolar rate: the rate is the exponent, at `Q₁`, of the upper
probability under the null of the events given by statistics of blocks.

The exponent of the empirical measure of single observations can be smaller than the rate: if a
member of the null lies in a smaller neighbourhood of `Q`, then `π m` tends to one
(`ProbabilityTheory.tendsto_nbhdUpperProb_atTop_nhds_one`). The members of the null of the mixtures
`(1 - ε) U + ε volume` on the circle, with `U` uniform on a finite coset, meet every basic
neighbourhood of Lebesgue measure [EVR26, Note 19], which is not proved here, while its bipolar
rate is `log (1 / ε)` (`ProbabilityTheory.bipolarRate_coset_mixtures`), positive for `ε < 1`.

## Main definitions

* `ProbabilityTheory.nbhdUpperProb T Q g δ m`: the supremum over the members of `T` of the
  probabilities under their `m`-fold products that the empirical averages of the `g i` are within
  `δ` of their means under `Q`.

## Main statements

* `ProbabilityTheory.nbhdUpperProb_eq_upperExp_indicator`: for measurable `g i`, `π m` is the
  upper expectation under the `m`-sample null of the indicator of the event.
* `ProbabilityTheory.nbhdUpperProb_le_exp`: `π m ≤ exp (- m c δ)`.
* `ProbabilityTheory.tauNbhdInf_le_liminf_log_inv_nbhdUpperProb_div`,
  `ProbabilityTheory.limsup_log_inv_nbhdUpperProb_div_le_tauNbhdInf`: the lower exponent is at
  least `c δ`, and the upper exponent at most `c δ'` for `δ' < δ`.
* `ProbabilityTheory.iSup_liminf_log_inv_nbhdUpperProb_div_eq_tauEnvelope`,
  `ProbabilityTheory.iSup_limsup_log_inv_nbhdUpperProb_div_eq_tauEnvelope`: over the basic
  neighbourhoods, both exponents have supremum the neighbourhood envelope of `klInf · T` at `Q`.
* `ProbabilityTheory.tendsto_nbhdUpperProb_atTop_nhds_one`: no decay when a member of the null
  lies in a smaller neighbourhood.
* `ProbabilityTheory.limsup_log_inv_nbhdUpperProb_div_le_mul_bipolarRate`: for blocks of `n`
  observations, the upper exponent is at most `n` times the bipolar rate.
* `ProbabilityTheory.iSup_liminf_log_inv_nbhdUpperProb_sampleNull_div_eq_bipolarRate`,
  `ProbabilityTheory.iSup_limsup_log_inv_nbhdUpperProb_sampleNull_div_eq_bipolarRate`: over the
  block lengths and the basic neighbourhoods, both exponents per observation have supremum the
  bipolar rate.

## Implementation notes

Exponents are taken in `EReal`, with `ENNReal.log`, and divided by `(m : EReal)`; basic
neighbourhoods are written with `≤ δ`, as in `MeasureTheory.tauNbhdInf`. The upper probability is
defined as a supremum of probabilities, which needs no measurability of the event; when the `g i`
are measurable, so is the event, and the upper probability is the upper expectation
`upperExp (sampleNull T m)` of its indicator (`nbhdUpperProb_eq_upperExp_indicator`). Nothing is
assumed of `Q`, which enters only through the centres `∫ g i ∂Q` of the neighbourhood. The
statements and proofs are adapted from `EValuesResearch/Results/RateGame.lean` (commit `83205cb`)
in the paper project `RemyDegenne/evalues_research`, rewritten on the API of LMLExplore. There they
are stated for the `n`-sample nulls, and the upper exponent of blocks is bounded by the bipolar
rate through the strong converse of the Stein lemma; here they are stated for every null of
probability measures, the blocks are instances, and that bound follows from the bound by the
envelope.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory InformationTheory Filter
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {T : Set (Measure Ω)} {Q : Measure Ω} {k : ℕ}
  {g : Fin k → Ω → ℝ} {δ : ℝ} {m : ℕ}

/-! ### The upper probability of a basic neighbourhood -/

/-- The supremum over the members of the null `T` of the probabilities, under their `m`-fold
products, that the empirical averages of the functions `g i` over `m` observations are within `δ`
of their means under `Q`: the upper probability under the null that the empirical measure of the
observations lies in the basic neighbourhood of `Q` given by the `g i` and `δ`. -/
noncomputable def nbhdUpperProb (T : Set (Measure Ω)) (Q : Measure Ω) {k : ℕ} (g : Fin k → Ω → ℝ)
    (δ : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ⨆ μ ∈ sampleNull T m, μ {x | ∀ i, |(∑ j, g i (x j)) / m - ∫ y, g i y ∂Q| ≤ δ}

/-- The upper probability of a basic neighbourhood, unfolded. -/
lemma nbhdUpperProb_def (T : Set (Measure Ω)) (Q : Measure Ω) (g : Fin k → Ω → ℝ) (δ : ℝ)
    (m : ℕ) : nbhdUpperProb T Q g δ m =
      ⨆ μ ∈ sampleNull T m, μ {x | ∀ i, |(∑ j, g i (x j)) / m - ∫ y, g i y ∂Q| ≤ δ} :=
  (rfl)

/-- The upper probability is at most `c` exactly when the probability of the event under the
`m`-fold product of every member of the null is. -/
lemma nbhdUpperProb_le_iff {c : ℝ≥0∞} :
    nbhdUpperProb T Q g δ m ≤ c ↔ ∀ P ∈ T,
      (Measure.pi fun _ : Fin m ↦ P) {x | ∀ i, |(∑ j, g i (x j)) / m - ∫ y, g i y ∂Q| ≤ δ} ≤ c := by
  rw [nbhdUpperProb_def]
  exact iSup₂_le_iff.trans forall_mem_sampleNull

/-- The probability of the event under the `m`-fold product of a member of the null is at most
the upper probability. -/
lemma measure_pi_le_nbhdUpperProb {P : Measure Ω} (hP : P ∈ T) :
    (Measure.pi fun _ : Fin m ↦ P) {x | ∀ i, |(∑ j, g i (x j)) / m - ∫ y, g i y ∂Q| ≤ δ} ≤
      nbhdUpperProb T Q g δ m :=
  nbhdUpperProb_le_iff.1 le_rfl P hP

/-- The upper probability under a simple null `{P}` is the probability under `P ^ m`. -/
@[simp]
lemma nbhdUpperProb_singleton (P : Measure Ω) :
    nbhdUpperProb {P} Q g δ m =
      (Measure.pi fun _ : Fin m ↦ P) {x | ∀ i, |(∑ j, g i (x j)) / m - ∫ y, g i y ∂Q| ≤ δ} := by
  simp [nbhdUpperProb_def]

/-- For a null of measures of mass at most one, the upper probability is at most one. -/
lemma nbhdUpperProb_le_one (hT : ∀ P ∈ T, P Set.univ ≤ 1) : nbhdUpperProb T Q g δ m ≤ 1 :=
  nbhdUpperProb_le_iff.2 fun _ hP ↦ (measure_mono (Set.subset_univ _)).trans
    (measure_univ_le_one_of_mem_sampleNull hT m _ (pi_mem_sampleNull hP))

/-- For measurable `g i`, the upper probability is the upper expectation under the `m`-sample null
of the indicator of the event. -/
lemma nbhdUpperProb_eq_upperExp_indicator (hg : ∀ i, Measurable (g i)) :
    nbhdUpperProb T Q g δ m = upperExp (sampleNull T m)
      ({x | ∀ i, |(∑ j, g i (x j)) / m - ∫ y, g i y ∂Q| ≤ δ}.indicator 1) := by
  have hA := measurableSet_setOf_forall_abs_sum_div_sub_le hg (fun i ↦ ∫ y, g i y ∂Q) δ m
  refine le_antisymm (nbhdUpperProb_le_iff.2 fun P hP ↦ ?_) (upperExp_le_iff.2 fun μ hμ ↦ ?_)
  · rw [← lintegral_indicator_one hA]
    exact lintegral_le_upperExp (pi_mem_sampleNull hP)
  · rw [lintegral_indicator_one hA, nbhdUpperProb_def]
    exact le_biSup (fun μ : Measure (Fin m → Ω) ↦ μ _) hμ

/-! ### The lower exponent -/

/-- **The upper probability decays at least at the rate of the neighbourhood** [EVR26, Note 15].
For a null `T` of probability measures, bounded measurable `g i` and any `δ`, the upper
probability `nbhdUpperProb T Q g δ m` that the empirical averages of the `g i` are within `δ` of
their means under `Q` is at most `exp (- m c)`, with `c` the infimum of
`klInf R T` over the probability measures `R` whose integrals of the `g i` are within `δ` of
those of `Q`. -/
theorem nbhdUpperProb_le_exp (hT : ∀ P ∈ T, IsProbabilityMeasure P) (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i, ∃ C, ∀ x, |g i x| ≤ C) (δ : ℝ) (m : ℕ) :
    nbhdUpperProb T Q g δ m ≤ EReal.exp (-(m * tauNbhdInf (fun R ↦ klInf R T) Q g δ)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simpa using nbhdUpperProb_le_one (fun P hP ↦ (hT P hP).measure_univ.le)
  choose C hC using hgb
  refine nbhdUpperProb_le_iff.2 fun P hP ↦ ?_
  have := hT P hP
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
  set A := {x : Fin m → Ω | ∀ i, |(∑ j, g i (x j)) / m - ∫ y, g i y ∂Q| ≤ δ}
  set c := tauNbhdInf (fun R ↦ klInf R T) Q g δ
  -- in logarithmic form, `m c ≤ log (1 / P ^ m (A))`
  rw [← ENNReal.log_le_log_iff, EReal.log_exp, EReal.le_neg, ← ENNReal.log_inv]
  have hlog0 : 0 ≤ ENNReal.log ((Measure.pi fun _ : Fin m ↦ P) A)⁻¹ :=
    ENNReal.zero_le_log_iff.2 (ENNReal.one_le_inv.2 prob_le_one)
  refine le_of_forall_lt_imp_le_of_dense fun b hb ↦ ?_
  rcases le_or_gt b 0 with hb0 | hb0
  · exact hb0.trans hlog0
  obtain ⟨b, rfl⟩ : ∃ x : ℝ, (x : EReal) = b :=
    ⟨b.toReal, EReal.coe_toReal (ne_top_of_lt hb) (ne_bot_of_gt hb0)⟩
  have hb0' : 0 < b := EReal.coe_pos.1 hb0
  have hbm : 0 ≤ b / m := div_nonneg hb0'.le hm'.le
  -- the level `b / m` is below the infimum of `klInf · T` over the neighbourhood
  have hbc : ((b / m : ℝ) : EReal) < c := by
    rw [EReal.coe_div, EReal.coe_natCast, EReal.div_lt_iff (by exact_mod_cast hm')
      (EReal.natCast_ne_top m), mul_comm]
    exact hb
  have h := ofReal_exp_mul_measure_pi_le_one hg hC hbm (P := P) (a := fun i ↦ ∫ x, g i x ∂Q)
    (ε := δ) (fun R hR hRg ↦ ?_) hm
  · rw [show (m : ℝ) * (b / m) = b by field_simp] at h
    calc (b : EReal) = ENNReal.log (ENNReal.ofReal (Real.exp b)) := (ENNReal.log_ofReal_exp b).symm
    _ ≤ ENNReal.log ((Measure.pi fun _ : Fin m ↦ P) A)⁻¹ :=
      ENNReal.log_le_log (ENNReal.le_inv_iff_mul_le.2 h)
  · -- a law of the neighbourhood is at relative entropy at least `b / m` from `P`
    have h1 := (hbc.trans_le (tauNbhdInf_le hR hRg)).le.trans (klInf_le_klIntegral hP)
    rw [klIntegral_eq_klDiv (by simp)] at h1
    rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_ennreal_ofReal, max_eq_left hbm]
    exact h1

/-- **The lower exponent of the upper probability** [EVR26, Note 15]. For a null `T` of
probability measures, bounded measurable `g i` and any `δ`, the lower exponent
`liminf (1/m) log (1 / π m)` of the upper probability under the null that the empirical
averages of the `g i` are within `δ` of their means under `Q` is at least the infimum of
`klInf R T` over the probability measures `R` whose integrals of the `g i` are within `δ` of
those of `Q`. -/
theorem tauNbhdInf_le_liminf_log_inv_nbhdUpperProb_div (hT : ∀ P ∈ T, IsProbabilityMeasure P)
    (hg : ∀ i, Measurable (g i)) (hgb : ∀ i, ∃ C, ∀ x, |g i x| ≤ C) (δ : ℝ) :
    tauNbhdInf (fun R ↦ klInf R T) Q g δ ≤
      liminf (fun m : ℕ ↦ ENNReal.log (nbhdUpperProb T Q g δ m)⁻¹ / m) atTop := by
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmE : (0 : EReal) < m := by exact_mod_cast hm
  have h := ENNReal.log_le_log (nbhdUpperProb_le_exp hT hg hgb δ m (Q := Q))
  rw [EReal.log_exp, EReal.le_neg] at h
  rwa [EReal.le_div_iff_mul_le hmE (EReal.natCast_ne_top m), mul_comm, ENNReal.log_inv]

/-! ### The upper exponent -/

/-- **No decay when the null meets a smaller neighbourhood.** For a null `T` of measures of mass
at most one, bounded measurable `g i` and `δ' < δ`, if a probability measure `P` of the null has
`|∫ g i ∂P - ∫ g i ∂Q| ≤ δ'` for every `i`, then the upper probability under the null that the
empirical averages of the `g i` are within `δ` of their means under `Q` tends to one. -/
theorem tendsto_nbhdUpperProb_atTop_nhds_one (hT : ∀ P ∈ T, P Set.univ ≤ 1) {P : Measure Ω}
    [IsProbabilityMeasure P] (hP : P ∈ T) (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i, ∃ C, ∀ x, |g i x| ≤ C) {δ' : ℝ} (hδ' : δ' < δ)
    (hPg : ∀ i, |∫ x, g i x ∂P - ∫ x, g i x ∂Q| ≤ δ') :
    Tendsto (nbhdUpperProb T Q g δ) atTop (𝓝 1) := by
  choose C hC using hgb
  have hgL (i : Fin k) : MemLp (g i) 2 P :=
    .of_bound (hg i).aestronglyMeasurable (C i) (.of_forall fun x ↦ (hC i x).trans' (by simp))
  set D := ∑ i, Var[g i; P] / (δ - δ') ^ 2
  have hlow (m : ℕ) (hm : m ≠ 0) : ENNReal.ofReal (1 - D / m) ≤ nbhdUpperProb T Q g δ m := by
    have h := one_sub_div_le_measureReal_pi_forall_abs_sum_div_sub_le hgL (sub_pos.2 hδ') hm
    refine (ENNReal.ofReal_le_ofReal h).trans ?_
    rw [ofReal_measureReal (by simp)]
    refine (measure_mono fun x hx ↦ ?_).trans (measure_pi_le_nbhdUpperProb hP)
    simp only [Set.mem_ofPred_eq] at hx ⊢
    intro i
    calc |(∑ j, g i (x j)) / m - ∫ y, g i y ∂Q|
    _ ≤ |(∑ j, g i (x j)) / m - ∫ y, g i y ∂P| + |∫ y, g i y ∂P - ∫ y, g i y ∂Q| :=
      abs_sub_le _ _ _
    _ ≤ (δ - δ') + δ' := add_le_add (hx i) (hPg i)
    _ = δ := by ring
  have hlim : Tendsto (fun m : ℕ ↦ ENNReal.ofReal (1 - D / m)) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := D)).div_atTop tendsto_natCast_atTop_atTop).const_sub 1
    rw [sub_zero] at h
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 1).comp h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_
    (.of_forall fun m ↦ nbhdUpperProb_le_one hT)
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact hlow m (by omega)

/-- **The upper exponent of the upper probability** [EVR26, Note 15]. For a null `T` of
probability measures, bounded measurable `g i` and `δ' < δ`, the upper exponent
`limsup (1/m) log (1 / π m)` of the upper probability under the null that the empirical
averages of the `g i` are within `δ` of their means under `Q` is at most the infimum of
`klInf R T` over the probability measures `R` whose integrals of the `g i` are within `δ'` of
those of `Q`. -/
theorem limsup_log_inv_nbhdUpperProb_div_le_tauNbhdInf (hT : ∀ P ∈ T, IsProbabilityMeasure P)
    (hg : ∀ i, Measurable (g i)) (hgb : ∀ i, ∃ C, ∀ x, |g i x| ≤ C) {δ' : ℝ} (hδ' : δ' < δ) :
    limsup (fun m : ℕ ↦ ENNReal.log (nbhdUpperProb T Q g δ m)⁻¹ / m) atTop ≤
      tauNbhdInf (fun R ↦ klInf R T) Q g δ' := by
  refine le_tauNbhdInf_iff.2 fun R hR hRg ↦ le_klInf_iff.2 fun P hP ↦ ?_
  have := hT P hP
  have := hR
  rw [klIntegral_eq_klDiv (by simp)]
  rcases eq_or_ne (klDiv R P) ⊤ with htop | htop
  · rw [htop, EReal.coe_ennreal_top]
    exact le_top
  set K := (klDiv R P).toReal with hK
  rw [← EReal.coe_ennreal_toReal htop, ← hK]
  -- under the powers of `R`, the event has probability tending to one
  set a : ℕ → ℝ := fun m ↦ (Measure.pi fun _ : Fin m ↦ R).real
    {x | ∀ i, |(∑ j, g i (x j)) / m - ∫ y, g i y ∂Q| ≤ δ} with ha
  have hRA : Tendsto a atTop (𝓝 1) := by
    have h := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp
      (tendsto_nbhdUpperProb_atTop_nhds_one (T := {R}) (by simp) (Set.mem_singleton R) hg hgb hδ'
        hRg)
    rw [ENNReal.toReal_one] at h
    refine h.congr fun m ↦ ?_
    simp [ha, measureReal_def]
  -- the bound at each large `m`
  have hbound : ∀ᶠ m in atTop, ENNReal.log (nbhdUpperProb T Q g δ m)⁻¹ / m ≤
      (((K + 1 / m) / a m : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop 1,
      hRA.eventually (lt_mem_nhds (show (2⁻¹ : ℝ) < 1 by norm_num))] with m hm ham
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hapos : 0 < a m := lt_trans (by norm_num) ham
    set A := {x : Fin m → Ω | ∀ i, |(∑ j, g i (x j)) / m - ∫ y, g i y ∂Q| ≤ δ}
    have haA : (Measure.pi fun _ : Fin m ↦ R).real A = a m := rfl
    have hpi : klDiv (Measure.pi fun _ : Fin m ↦ R) (Measure.pi fun _ : Fin m ↦ P) =
        ENNReal.ofReal (m * K) := by
      rw [klDiv_pi_const, Fintype.card_fin, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast, hK, ENNReal.ofReal_toReal htop]
    -- the members of the null charge the event
    have hac : (Measure.pi fun _ : Fin m ↦ R) ≪ Measure.pi fun _ : Fin m ↦ P :=
      (klDiv_ne_top_iff.1 (by rw [hpi]; exact ENNReal.ofReal_ne_top)).1
    have hA0 : (Measure.pi fun _ : Fin m ↦ P) A ≠ 0 := fun h0 ↦ by
      rw [← haA, measureReal_def, hac h0, ENNReal.toReal_zero] at hapos
      exact lt_irrefl _ hapos
    set p := (Measure.pi fun _ : Fin m ↦ P).real A with hp
    -- the change of measure: `R ^ m (A) log (1 / p) ≤ m K + 1`
    have hlogp : Real.log p⁻¹ ≤ (m * K + 1) / a m := by
      have h := log_inv_measureReal_le_toReal_klDiv_add_one_div (s := A)
        (by rw [hpi]; exact ENNReal.ofReal_ne_top) (haA ▸ hapos)
      rwa [hpi, ENNReal.toReal_ofReal (by positivity), haA] at h
    -- the upper probability is at least that of `P ^ m`
    have hlogπ : ENNReal.log (nbhdUpperProb T Q g δ m)⁻¹ ≤ ((Real.log p⁻¹ : ℝ) : EReal) := by
      calc ENNReal.log (nbhdUpperProb T Q g δ m)⁻¹
      _ ≤ ENNReal.log ((Measure.pi fun _ : Fin m ↦ P) A)⁻¹ :=
        ENNReal.log_le_log (ENNReal.inv_le_inv.2 (measure_pi_le_nbhdUpperProb hP))
      _ = ((Real.log p⁻¹ : ℝ) : EReal) := by
        rw [ENNReal.log_inv, ENNReal.log_pos_real hA0 (measure_ne_top _ _), Real.log_inv,
          EReal.coe_neg, hp, measureReal_def]
    have hm0 : (m : ℝ) ≠ 0 := hm'.ne'
    have ha0 : a m ≠ 0 := hapos.ne'
    calc ENNReal.log (nbhdUpperProb T Q g δ m)⁻¹ / m
    _ ≤ ((Real.log p⁻¹ : ℝ) : EReal) / m :=
      EReal.div_le_div_right_of_nonneg (by positivity) hlogπ
    _ ≤ (((m * K + 1) / a m : ℝ) : EReal) / m :=
      EReal.div_le_div_right_of_nonneg (by positivity) (EReal.coe_le_coe_iff.2 hlogp)
    _ = (((K + 1 / m) / a m : ℝ) : EReal) := by
      rw [← EReal.coe_natCast, ← EReal.coe_div]
      congr 1
      field_simp
  -- the bounds tend to `K`
  have hblim : Tendsto (fun m : ℕ ↦ (((K + 1 / m) / a m : ℝ) : EReal)) atTop (𝓝 (K : EReal)) := by
    refine (continuous_coe_real_ereal.tendsto _).comp ?_
    have h := ((tendsto_const_nhds (x := K)).add tendsto_one_div_atTop_nhds_zero_nat).div hRA
      one_ne_zero
    rw [add_zero, div_one] at h
    exact h
  calc limsup (fun m : ℕ ↦ ENNReal.log (nbhdUpperProb T Q g δ m)⁻¹ / m) atTop
  _ ≤ limsup (fun m : ℕ ↦ (((K + 1 / m) / a m : ℝ) : EReal)) atTop := limsup_le_limsup hbound
  _ = K := hblim.limsup_eq

/-! ### The exponents over the basic neighbourhoods -/

/-- **The lower exponents over the basic neighbourhoods give the envelope** [EVR26, Note 15]. For
a null `T` of probability measures, the supremum over the basic neighbourhoods of `Q` (finitely
many bounded measurable `g i` and `δ > 0`) of the lower exponent of the upper probability under
the null that the empirical measure lies in the neighbourhood is the neighbourhood envelope of
`klInf · T` at `Q`. -/
theorem iSup_liminf_log_inv_nbhdUpperProb_div_eq_tauEnvelope (Q : Measure Ω)
    (hT : ∀ P ∈ T, IsProbabilityMeasure P) :
    ⨆ (k : ℕ) (g : Fin k → Ω → ℝ) (_ : ∀ i, Measurable (g i)) (_ : ∀ i, ∃ C, ∀ x, |g i x| ≤ C)
      (δ : ℝ) (_ : 0 < δ),
      liminf (fun m : ℕ ↦ ENNReal.log (nbhdUpperProb T Q g δ m)⁻¹ / m) atTop =
        tauEnvelope (fun R ↦ klInf R T) Q := by
  refine le_antisymm (iSup_le fun k ↦ iSup_le fun g ↦ iSup_le fun hg ↦ iSup_le fun hgb ↦
    iSup_le fun δ ↦ iSup_le fun hδ ↦ ?_) (tauEnvelope_le_iff.2 fun k g hg hgb δ hδ ↦ ?_)
  · exact (liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)).trans
      ((limsup_log_inv_nbhdUpperProb_div_le_tauNbhdInf hT hg hgb (half_lt_self hδ)).trans
        (tauNbhdInf_le_tauEnvelope hg hgb (half_pos hδ)))
  · exact (tauNbhdInf_le_liminf_log_inv_nbhdUpperProb_div hT hg hgb δ).trans
      (le_iSup_of_le k (le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le hgb
        (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))))))

/-- **The upper exponents over the basic neighbourhoods give the envelope** [EVR26, Note 15]. For
a null `T` of probability measures, the supremum over the basic neighbourhoods of `Q` (finitely
many bounded measurable `g i` and `δ > 0`) of the upper exponent of the upper probability under
the null that the empirical measure lies in the neighbourhood is the neighbourhood envelope of
`klInf · T` at `Q`. -/
theorem iSup_limsup_log_inv_nbhdUpperProb_div_eq_tauEnvelope (Q : Measure Ω)
    (hT : ∀ P ∈ T, IsProbabilityMeasure P) :
    ⨆ (k : ℕ) (g : Fin k → Ω → ℝ) (_ : ∀ i, Measurable (g i)) (_ : ∀ i, ∃ C, ∀ x, |g i x| ≤ C)
      (δ : ℝ) (_ : 0 < δ),
      limsup (fun m : ℕ ↦ ENNReal.log (nbhdUpperProb T Q g δ m)⁻¹ / m) atTop =
        tauEnvelope (fun R ↦ klInf R T) Q := by
  refine le_antisymm (iSup_le fun k ↦ iSup_le fun g ↦ iSup_le fun hg ↦ iSup_le fun hgb ↦
    iSup_le fun δ ↦ iSup_le fun hδ ↦ ?_) (tauEnvelope_le_iff.2 fun k g hg hgb δ hδ ↦ ?_)
  · exact (limsup_log_inv_nbhdUpperProb_div_le_tauNbhdInf hT hg hgb (half_lt_self hδ)).trans
      (tauNbhdInf_le_tauEnvelope hg hgb (half_pos hδ))
  · exact ((tauNbhdInf_le_liminf_log_inv_nbhdUpperProb_div hT hg hgb δ).trans
      (liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault))).trans
      (le_iSup_of_le k (le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le hgb
        (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))))))

/-! ### Blocks of `n` observations -/

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}

/-- **The exponents of blocks are at most the rate** [EVR26, Note 15]. For blocks of `n ≠ 0`
observations, with `T = sampleNull S₁ n` for a null `S₁` of probability measures and `Q = Q₁ ^ n`,
the upper exponent of the upper probability under the null that the empirical averages of
bounded measurable statistics `g i` of the blocks are within `δ > 0` of their means under `Q₁ ^ n`
is at most `n * bipolarRate Q₁ S₁`: the exponent per observation is at most the bipolar rate. -/
theorem limsup_log_inv_nbhdUpperProb_div_le_mul_bipolarRate (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {n : ℕ} (hn : n ≠ 0)
    {g : Fin k → (Fin n → 𝓧) → ℝ} (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i, ∃ C, ∀ x, |g i x| ≤ C) (hδ : 0 < δ) :
    limsup (fun m : ℕ ↦ ENNReal.log (nbhdUpperProb (sampleNull S₁ n)
      (Measure.pi fun _ : Fin n ↦ Q₁) g δ m)⁻¹ / m) atTop ≤ n * bipolarRate Q₁ S₁ :=
  ((limsup_log_inv_nbhdUpperProb_div_le_tauNbhdInf (isProbabilityMeasure_of_mem_sampleNull hS₁ n)
    hg hgb (half_lt_self hδ)).trans (tauNbhdInf_le_tauEnvelope hg hgb (half_pos hδ))).trans
    (tauEnvelope_le_mul_bipolarRate Q₁ S₁ hS₁ hn)

/-- **The rate is the lower exponent of the statistics of blocks** [EVR26, Note 15]. For a null
`S₁` of probability measures, the supremum over the block lengths `n + 1` and the basic
neighbourhoods of `Q₁ ^ (n + 1)` of the lower exponent of the upper probability under the null
that the empirical measure of the blocks lies in the neighbourhood, divided by `n + 1`, is the
bipolar rate. -/
theorem iSup_liminf_log_inv_nbhdUpperProb_sampleNull_div_eq_bipolarRate (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (S₁ : Set (Measure 𝓧)) (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) :
    ⨆ n : ℕ, (⨆ (k : ℕ) (g : Fin k → (Fin (n + 1) → 𝓧) → ℝ) (_ : ∀ i, Measurable (g i))
      (_ : ∀ i, ∃ C, ∀ x, |g i x| ≤ C) (δ : ℝ) (_ : 0 < δ),
      liminf (fun m : ℕ ↦ ENNReal.log (nbhdUpperProb (sampleNull S₁ (n + 1))
        (Measure.pi fun _ : Fin (n + 1) ↦ Q₁) g δ m)⁻¹ / m) atTop) / ((n + 1 : ℕ) : EReal) =
      bipolarRate Q₁ S₁ := by
  rw [bipolarRate_eq_iSup_tauEnvelope_div Q₁ S₁ hS₁]
  refine iSup_congr fun n ↦ ?_
  rw [iSup_liminf_log_inv_nbhdUpperProb_div_eq_tauEnvelope _
    (isProbabilityMeasure_of_mem_sampleNull hS₁ _)]

/-- **The rate is the upper exponent of the statistics of blocks** [EVR26, Note 15]. For a null
`S₁` of probability measures, the supremum over the block lengths `n + 1` and the basic
neighbourhoods of `Q₁ ^ (n + 1)` of the upper exponent of the upper probability under the null
that the empirical measure of the blocks lies in the neighbourhood, divided by `n + 1`, is the
bipolar rate. -/
theorem iSup_limsup_log_inv_nbhdUpperProb_sampleNull_div_eq_bipolarRate (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (S₁ : Set (Measure 𝓧)) (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) :
    ⨆ n : ℕ, (⨆ (k : ℕ) (g : Fin k → (Fin (n + 1) → 𝓧) → ℝ) (_ : ∀ i, Measurable (g i))
      (_ : ∀ i, ∃ C, ∀ x, |g i x| ≤ C) (δ : ℝ) (_ : 0 < δ),
      limsup (fun m : ℕ ↦ ENNReal.log (nbhdUpperProb (sampleNull S₁ (n + 1))
        (Measure.pi fun _ : Fin (n + 1) ↦ Q₁) g δ m)⁻¹ / m) atTop) / ((n + 1 : ℕ) : EReal) =
      bipolarRate Q₁ S₁ := by
  rw [bipolarRate_eq_iSup_tauEnvelope_div Q₁ S₁ hS₁]
  refine iSup_congr fun n ↦ ?_
  rw [iSup_limsup_log_inv_nbhdUpperProb_div_eq_tauEnvelope _
    (isProbabilityMeasure_of_mem_sampleNull hS₁ _)]

end ProbabilityTheory
