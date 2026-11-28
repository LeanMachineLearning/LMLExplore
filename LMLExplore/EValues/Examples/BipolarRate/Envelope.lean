/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Examples.BipolarRate.Circle
public import LMLExplore.MeasureTheory.Measure.TauEnvelope
import LMLExplore.EValues.BipolarRate.Envelope
import LMLExplore.EValues.Examples.BipolarRate.FiniteSupport
import LMLExplore.MeasureTheory.Function.SimpleFunc
import LMLExplore.MeasureTheory.Group.AddCircle
import LMLExplore.MeasureTheory.Integral.BoundedMeasurable
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.Average
import TauCeti.InformationTheory.KullbackLeibler.Variational
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# The bipolar rate is not a function of the single-letter envelopes of the smallest relative entropy

For a null `S` of probability measures and a probability measure `Q`, write `a 1` for the
largest expected logarithm of an e-variable under `Q`, `Φ^τ` and `Φ^{τ,seq}` for the
neighbourhood and the sequential envelopes at `Q` of `R ↦ klInf R S`
(`MeasureTheory.tauEnvelope`, `MeasureTheory.seqTauEnvelope`) and `d` for the bipolar rate. Then
`a 1 ≤ Φ^τ ≤ d ≤ Φ^{τ,seq} ≤ klInf Q S` (`LMLExplore.EValues.BipolarRate.Envelope`). This file
computes the envelopes for two nulls, for `ε ≤ 1` [EVR26, Note 19]:

* the *finite-support null* of the mixtures `(1 - ε) F + ε Q`, with `F` a probability measure
  carried by a finite set, on any measurable space with measurable singletons: `Φ^τ = 0`, since
  the laws carried by finite sets meet every basic neighbourhood of `Q`, and, when `Q` has no
  atoms, `Φ^{τ,seq} = log (1 / ε)`, since a sequence of probability measures that converges to `Q`
  on every measurable set gives a vanishing mass to the countable set of its atoms, hence to the
  finite sets that carry the `F`;
* the *coset null* on the circle `UnitAddCircle`, at Lebesgue measure `volume`, of the mixtures
  `(1 - ε) U + ε volume`, with `U` the uniform law on a finite coset `x₀ + (1 / N) ℤ`: every basic
  neighbourhood of `volume` contains a member, so `Φ^τ = 0`, and `Φ^{τ,seq} = log (1 / ε)`, since
  the coset null is contained in the finite-support null.

For `ε < 1`, the two nulls have, at Lebesgue measure on the circle, the same `a 1` (zero), the
same envelopes (`0` and `log (1 / ε)`) and the same smallest relative entropy (`log (1 / ε)`),
but the bipolar rates `log (1 / ε)` and `0` (`ProbabilityTheory.bipolarRate_coset_mixtures`,
`ProbabilityTheory.bipolarRate_finitelySupported_mixtures_eq_zero`). So the bipolar rate is not a
function of these four numbers: the lower semicontinuity of `klInf · S` at `Q` in the
neighbourhood sense is not necessary for `d = klInf Q S`, in the sequential sense it is not
sufficient, and the supremum over the number of observations in the variational formula
`ProbabilityTheory.bipolarRate_eq_iSup_tauEnvelope_div` cannot be dropped.

## Main statements

* `ProbabilityTheory.tauEnvelope_klInf_finitelySupported_mixtures_eq_zero`,
  `ProbabilityTheory.seqTauEnvelope_klInf_finitelySupported_mixtures`: the envelopes of the
  finite-support null are `0` and `log (1 / ε)`.
* `ProbabilityTheory.exists_coset_mixture_forall_abs_integral_sub_le`: every basic neighbourhood
  of Lebesgue measure on the circle contains a member of the coset null.
* `ProbabilityTheory.tauEnvelope_klInf_coset_mixtures_eq_zero`,
  `ProbabilityTheory.seqTauEnvelope_klInf_coset_mixtures`: the envelopes of the coset null are `0`
  and `log (1 / ε)`.
* `ProbabilityTheory.not_exists_forall_bipolarRate_eq_envelopes`: on the circle, the bipolar rate
  at Lebesgue measure is not a function of `a 1`, of the two envelopes and of the smallest
  relative entropy.

## Implementation notes

A basic neighbourhood of `Q` meets the finite-support null at the mixture of `Q` with the image of
`Q` by a measurable map with finite range along which the statistics of the neighbourhood move by
less than its tolerance
(`MeasureTheory.exists_measurable_finite_range_forall_abs_integral_map_sub_le`).
For the coset null, the average `T_N f (x₀)` of a bounded measurable `f` on the coset
`x₀ + (1 / N) ℤ` is a contraction of `L¹(volume)` in `f`
(`UnitAddCircle.integral_abs_integral_uniformOn_coset_le`), and tends to `∫ f` uniformly in `x₀`
for a continuous `f` (`UnitAddCircle.exists_forall_abs_integral_uniformOn_coset_sub_le`); with
the density of the bounded continuous functions in `L¹`, some coset has averages of the
statistics close to their integrals. The lower bound on
the sequential envelope is the Donsker–Varadhan inequality for `t 𝟙_{sᶜ}`, with `s` the finite set
that carries `F`, as `t → ∞`: probability measures `R k` that converge to `Q` on every measurable
set give a vanishing mass to the countable set `C` of their atoms, hence to every finite set, so
that `klInf (R k) S ≥ t (1 - R k C) - log (ε e^t + 1 - ε)`. The lower bound for the coset null is
that of the larger finite-support null.

The statements and proofs are adapted from `EValuesResearch/Results/Envelopes.lean` and
`EValuesResearch/Results/RateVersusKL.lean` (commit `83205cb`) in the paper project
`RemyDegenne/evalues_research`, rewritten on the API of LMLExplore. The source states the
finite-support envelopes on the circle only, defines the two nulls instead of writing them in the
statements, and states the comparison of the two nulls as a list of equalities for `0 < ε < 1`.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory InformationTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ε : ℝ≥0∞}

/-! ### The finite-support null -/

/-- **The neighbourhood envelope of the finite-support null is zero** [EVR26, Note 19]: for every
probability measure `Q` on a measurable space with measurable singletons and `ε ≤ 1`, the
neighbourhood envelope at `Q` of the smallest relative entropy to the null of the mixtures
`(1 - ε) F + ε Q`, with `F` carried by a finite set, is `0`. -/
theorem tauEnvelope_klInf_finitelySupported_mixtures_eq_zero [MeasurableSingletonClass 𝓧]
    (Q : Measure 𝓧) [IsProbabilityMeasure Q] (hε : ε ≤ 1) :
    tauEnvelope (fun R ↦ klInf R {(1 - ε) • F + ε • Q | (F : Measure 𝓧)
      (_ : IsProbabilityMeasure F) (_ : ∃ s : Set 𝓧, s.Finite ∧ F sᶜ = 0)}) Q = 0 := by
  set S := {(1 - ε) • F + ε • Q | (F : Measure 𝓧) (_ : IsProbabilityMeasure F)
    (_ : ∃ s : Set 𝓧, s.Finite ∧ F sᶜ = 0)}
  have hS : ∀ P ∈ S, IsProbabilityMeasure P := fun P hP ↦
    isProbabilityMeasure_of_mem_finitelySupported_mixtures hε hP
  refine le_antisymm (tauEnvelope_le_iff.2 fun k g hg hgb δ hδ ↦ ?_)
    ((maxEPower_nonneg Q fun P hP ↦ (hS P hP).measure_univ.le).trans
      (maxEPower_le_tauEnvelope_klInf Q S hS))
  -- the image of `Q` by a map with finite range along which the `g i` move by less than `δ`
  obtain ⟨s, hs, hsf, hsg⟩ :=
    exists_measurable_finite_range_forall_abs_integral_map_sub_le hg hgb hδ Q
  have hF : Q.map s (Set.range s)ᶜ = 0 := by
    rw [Measure.map_apply hs hsf.measurableSet.compl, Set.preimage_compl, Set.preimage_range,
      Set.compl_univ, measure_empty]
  have hP : (1 - ε) • Q.map s + ε • Q ∈ S := ⟨Q.map s, inferInstance, ⟨_, hsf, hF⟩, rfl⟩
  have := hS _ hP
  refine (tauNbhdInf_le this fun i ↦ ?_).trans ((klInf_le_klIntegral hP).trans ?_)
  · obtain ⟨C, hC⟩ := hgb i
    exact LMLExplore.abs_integral_mixture_sub_le hε (LMLExplore.integrable_of_abs_le (hg i) hC _)
      (LMLExplore.integrable_of_abs_le (hg i) hC _)
      ((hsg i).trans_eq (by rw [probReal_univ, mul_one]))
  · rw [klIntegral_eq_klDiv rfl, klDiv_self, EReal.coe_ennreal_zero]

/-- **The Donsker–Varadhan bound against the finite-support null.** For `t ≥ 0` and a
probability measure `R` whose atoms all lie in a set `C`, the smallest relative entropy from `R`
to the null of the mixtures `(1 - ε) F + ε Q`, with `F` carried by a finite set and `Q` without
atoms, is at least `t (1 - R C) - log (ε e^t + 1 - ε)`. -/
private lemma le_klInf_finitelySupported_mixtures [MeasurableSingletonClass 𝓧]
    (Q : Measure 𝓧) [IsProbabilityMeasure Q] [NullSingletonClass Q] (hε : ε ≤ 1)
    (R : Measure 𝓧) [IsProbabilityMeasure R] {C : Set 𝓧} (hC : ∀ x ∉ C, R {x} = 0) {t : ℝ}
    (ht : 0 ≤ t) :
    ((t * (1 - R.real C) - Real.log (ε.toReal * Real.exp t + (1 - ε.toReal)) : ℝ) : EReal) ≤
      klInf R {(1 - ε) • F + ε • Q | (F : Measure 𝓧) (_ : IsProbabilityMeasure F)
        (_ : ∃ s : Set 𝓧, s.Finite ∧ F sᶜ = 0)} := by
  set e := ε.toReal with he_def
  refine le_klInf_iff.2 fun P hP ↦ ?_
  have hPp := isProbabilityMeasure_of_mem_finitelySupported_mixtures hε hP
  obtain ⟨F, hF, ⟨s, hs, hFs⟩, rfl⟩ := hP
  have hsm : MeasurableSet sᶜ := hs.measurableSet.compl
  set f : 𝓧 → ℝ := sᶜ.indicator fun _ ↦ t with hf_def
  have hexp_eq :
      (fun x ↦ Real.exp (f x)) = fun x ↦ 1 + sᶜ.indicator (fun _ ↦ Real.exp t - 1) x := by
    ext x
    by_cases hx : x ∈ sᶜ <;> simp [f, hx]
  have hexpi : Integrable (fun x ↦ Real.exp (f x)) ((1 - ε) • F + ε • Q) := by
    rw [hexp_eq]
    exact (integrable_const 1).add ((integrable_const _).indicator hsm)
  have hQs : Q sᶜ = 1 := by
    rw [measure_compl hs.measurableSet (measure_ne_top _ _), hs.measure_zero Q, measure_univ,
      tsub_zero]
  have hPs : ((1 - ε) • F + ε • Q).real sᶜ = e := by
    simp [measureReal_def, hFs, hQs, he_def]
  have hZ : ∫ x, Real.exp (f x) ∂((1 - ε) • F + ε • Q) = e * Real.exp t + (1 - e) := by
    rw [hexp_eq, integral_add (integrable_const _) ((integrable_const _).indicator hsm),
      integral_const, integral_indicator_const _ hsm, hPs]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  -- a finite set has at most the mass of the atoms
  have hRs : R.real s ≤ R.real C := by
    have hdiff : R (s \ C) = 0 := by
      rw [← Set.biUnion_of_singleton (s \ C),
        measure_biUnion_null_iff (hs.countable.mono Set.sdiff_subset)]
      exact fun x hx ↦ hC x hx.2
    have h := measure_le_inter_add_sdiff R s C
    rw [hdiff, add_zero] at h
    exact ENNReal.toReal_mono (measure_ne_top _ _) (h.trans (measure_mono Set.inter_subset_right))
  have hRf : ∫ x, f x ∂R = t * (1 - R.real s) := by
    rw [hf_def, integral_indicator_const _ hsm, probReal_compl_eq_one_sub hs.measurableSet,
      smul_eq_mul, mul_comm]
  have hDV := TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv (μ := R)
    (ν := (1 - ε) • F + ε • Q) ((integrable_const t).indicator hsm) hexpi
  rw [klIntegral_eq_klDiv (by simp [tsub_add_cancel_of_le hε])]
  calc ((t * (1 - R.real C) - Real.log (e * Real.exp t + (1 - e)) : ℝ) : EReal)
  _ ≤ ((∫ x, f x ∂R - Real.log (∫ x, Real.exp (f x) ∂((1 - ε) • F + ε • Q)) : ℝ) :
      EReal) := by
    rw [hRf, hZ]
    exact EReal.coe_le_coe_iff.2 (by nlinarith)
  _ ≤ ((ENNReal.ofReal (∫ x, f x ∂R -
      Real.log (∫ x, Real.exp (f x) ∂((1 - ε) • F + ε • Q))) : ℝ≥0∞) : EReal) := by
    rw [EReal.coe_ennreal_ofReal]
    exact EReal.coe_le_coe_iff.2 (le_max_left _ _)
  _ ≤ (klDiv R ((1 - ε) • F + ε • Q) : EReal) :=
    EReal.coe_ennreal_le_coe_ennreal_iff.2 hDV

/-- For `0 < e ≤ 1`, `t - log (e e^t + 1 - e) → - log e` as `t → ∞`. -/
private lemma tendsto_sub_log_mul_exp_add {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    Tendsto (fun t ↦ t - Real.log (e * Real.exp t + (1 - e))) atTop (𝓝 (-Real.log e)) := by
  -- `t - log (e e^t + 1 - e) = - log (e + (1 - e) e^{-t})`
  have heq (t : ℝ) : t - Real.log (e * Real.exp t + (1 - e)) =
      -Real.log (e + (1 - e) * Real.exp (-t)) := by
    have hpos : 0 < e + (1 - e) * Real.exp (-t) := by
      have := Real.exp_pos (-t)
      nlinarith
    have h2 : e * Real.exp t + (1 - e) = Real.exp t * (e + (1 - e) * Real.exp (-t)) := by
      rw [mul_add, ← mul_assoc, mul_comm (Real.exp t) (1 - e), mul_assoc, ← Real.exp_add,
        add_neg_cancel, Real.exp_zero, mul_one, mul_comm]
    rw [h2, Real.log_mul (Real.exp_pos t).ne' hpos.ne', Real.log_exp]
    ring
  simp_rw [heq]
  have h1 : Tendsto (fun t : ℝ ↦ e + (1 - e) * Real.exp (-t)) atTop (𝓝 e) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (1 - e)).const_add e
  exact ((Real.continuousAt_log he.ne').tendsto.comp h1).neg

/-- **The sequential envelope of the finite-support null is `log (1 / ε)`** [EVR26, Note 19].
For a probability measure `Q` without atoms on a measurable space with measurable singletons and
`ε ≤ 1`, the sequential envelope at `Q` of the smallest relative entropy to the null of the
mixtures `(1 - ε) F + ε Q`, with `F` carried by a finite set, is `log (1 / ε)`, the smallest
relative entropy itself (`ProbabilityTheory.klInf_finitelySupported_mixtures`): it is lower
semicontinuous at `Q` in the sequential sense, while the bipolar rate is `0`
(`ProbabilityTheory.bipolarRate_finitelySupported_mixtures_eq_zero`). -/
theorem seqTauEnvelope_klInf_finitelySupported_mixtures [MeasurableSingletonClass 𝓧]
    (Q : Measure 𝓧) [IsProbabilityMeasure Q] [NullSingletonClass Q] (hε : ε ≤ 1) :
    seqTauEnvelope (fun R ↦ klInf R {(1 - ε) • F + ε • Q | (F : Measure 𝓧)
      (_ : IsProbabilityMeasure F) (_ : ∃ s : Set 𝓧, s.Finite ∧ F sᶜ = 0)}) Q =
      ENNReal.log ε⁻¹ := by
  set S := {(1 - ε) • F + ε • Q | (F : Measure 𝓧) (_ : IsProbabilityMeasure F)
    (_ : ∃ s : Set 𝓧, s.Finite ∧ F sᶜ = 0)}
  refine le_antisymm (seqTauEnvelope_le.trans (klInf_finitelySupported_mixtures Q hε).le)
    (le_seqTauEnvelope_iff.2 fun R hR hRQ ↦ ?_)
  -- the countable set of the atoms of all the `R k`
  set C : Set 𝓧 := ⋃ k, {x | 0 < R k {x}} with hC_def
  have hCc : C.Countable := Set.countable_iUnion fun k ↦
    Measure.countable_meas_pos_of_disjoint_iUnion (μ := R k) (As := fun x ↦ {x})
      (fun _ ↦ measurableSet_singleton _) (fun x y hxy ↦ Set.disjoint_singleton.2 hxy)
  have hRC : Tendsto (fun k ↦ (R k).real C) atTop (𝓝 0) := by
    have h := hRQ C hCc.measurableSet
    rw [hCc.measure_zero Q] at h
    simpa [measureReal_def, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  have hatoms (k : ℕ) (x : 𝓧) (hx : x ∉ C) : R k {x} = 0 := by
    simp only [hC_def, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hx
    exact le_antisymm (hx k) zero_le
  set e := ε.toReal with he_def
  have he1 : e ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hε)
  -- let `k → ∞`
  have hlim (t : ℝ) (ht : 0 ≤ t) : ((t - Real.log (e * Real.exp t + (1 - e)) : ℝ) : EReal) ≤
      liminf (fun k ↦ klInf (R k) S) atTop := by
    have htend : Tendsto (fun k ↦ ((t * (1 - (R k).real C) -
        Real.log (e * Real.exp t + (1 - e)) : ℝ) : EReal)) atTop
        (𝓝 ((t - Real.log (e * Real.exp t + (1 - e)) : ℝ) : EReal)) := by
      refine (continuous_coe_real_ereal.tendsto _).comp ?_
      simpa using ((hRC.const_sub 1).const_mul t).sub_const (Real.log (e * Real.exp t + (1 - e)))
    rw [← htend.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall fun k ↦
      le_klInf_finitelySupported_mixtures Q hε (R k) (hatoms k) ht)
  -- let `t → ∞`
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  induction c using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hc not_top_lt
  | coe c =>
    rcases eq_or_ne ε 0 with rfl | hε0
    · have h0 : e = 0 := by simp [he_def]
      refine le_trans ?_ (hlim (max c 0) (le_max_right _ _))
      rw [h0]
      simp only [zero_mul, sub_zero, zero_add, Real.log_one]
      exact EReal.coe_le_coe_iff.2 (le_max_left _ _)
    · have hεt : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hε
      have hepos : 0 < e := ENNReal.toReal_pos hε0 hεt
      have hlogε : ENNReal.log ε⁻¹ = ((-Real.log e : ℝ) : EReal) := by
        rw [ENNReal.log_inv, ENNReal.log_pos_real hε0 hεt, EReal.coe_neg]
      rw [hlogε, EReal.coe_lt_coe_iff] at hc
      obtain ⟨t, hct, ht⟩ := (((tendsto_sub_log_mul_exp_add hepos he1).eventually
        (lt_mem_nhds hc)).and (eventually_ge_atTop 0)).exists
      exact (EReal.coe_le_coe_iff.2 hct.le).trans (hlim t ht)

/-! ### The coset null -/

/-- The coset null is contained in the finite-support null. -/
private lemma coset_mixtures_subset_finitelySupported_mixtures (ε : ℝ≥0∞) :
    {(1 - ε) • uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} +
      ε • volume | (x₀ : UnitAddCircle) (N : ℕ)} ⊆
    {(1 - ε) • F + ε • volume | (F : Measure UnitAddCircle) (_ : IsProbabilityMeasure F)
      (_ : ∃ s : Set UnitAddCircle, s.Finite ∧ F sᶜ = 0)} := by
  rintro _ ⟨x₀, N, rfl⟩
  have hfin := UnitAddCircle.finite_coset x₀ N
  exact ⟨_, isProbabilityMeasure_uniformOn hfin ⟨x₀, by simp⟩,
    ⟨_, hfin, (uniformOn_eq_zero_iff hfin).2 (Set.inter_compl_self _)⟩, rfl⟩

/-- The members of the coset null are probability measures. -/
private lemma isProbabilityMeasure_of_mem_coset_mixtures (hε : ε ≤ 1) {P : Measure UnitAddCircle}
    (hP : P ∈ {(1 - ε) • uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples
      (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} + ε • volume | (x₀ : UnitAddCircle) (N : ℕ)}) :
    IsProbabilityMeasure P := by
  obtain ⟨x₀, N, rfl⟩ := hP
  exact isProbabilityMeasure_coset_mixture hε x₀ N

/-- **Every basic neighbourhood of Lebesgue measure meets the coset null** [EVR26, Note 19]. For
`ε ≤ 1`, finitely many bounded measurable functions `g i` on the circle and `δ > 0`, some mixture
`P = (1 - ε) U + ε volume`, with `U` uniform on a finite coset `x₀ + (1 / N) ℤ`, has
`|∫ g i ∂P - ∫ g i ∂volume| ≤ δ` for every `i`. -/
theorem exists_coset_mixture_forall_abs_integral_sub_le (hε : ε ≤ 1) {k : ℕ}
    {g : Fin k → UnitAddCircle → ℝ} (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i, ∃ C, ∀ x, |g i x| ≤ C) {δ : ℝ} (hδ : 0 < δ) :
    ∃ P ∈ {(1 - ε) • uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples
      (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} + ε • volume | (x₀ : UnitAddCircle) (N : ℕ)},
      ∀ i, |∫ x, g i x ∂P - ∫ x, g i x ∂(volume : Measure UnitAddCircle)| ≤ δ := by
  choose C hC using hgb
  -- approximate each `g i` in `L¹` by a bounded continuous function
  set η : ℝ := δ / (4 * (k + 1)) with hη_def
  have hη : 0 < η := by positivity
  have hη4 : η ≤ δ / 4 := div_le_div_of_nonneg_left hδ.le (by norm_num) (by nlinarith)
  have hgi (i : Fin k) : Integrable (g i) (volume : Measure UnitAddCircle) :=
    LMLExplore.integrable_of_abs_le (hg i) (hC i) _
  choose h hh _ using fun i ↦ (hgi i).exists_boundedContinuous_integral_sub_le hη
  -- uniform Riemann sums on the cosets for the `h i`
  choose N₀ hN₀ using fun i ↦
    UnitAddCircle.exists_forall_abs_integral_uniformOn_coset_sub_le (h i) (η := δ / 4)
      (by positivity)
  set N : ℕ := (Finset.univ.sup N₀) + 1 with hN_def
  have hN : 0 < N := Nat.succ_pos _
  have hNi (i : Fin k) : N₀ i ≤ N := (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _)
  -- a coset where every `g i - h i` has a small average
  set F : UnitAddCircle → ℝ := fun x₀ ↦ ∑ i, |∫ x, (g i x - h i x) ∂uniformOn
    {x | x - x₀ ∈ AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)}| with hF_def
  have hgh_meas (i : Fin k) : Measurable fun x ↦ g i x - h i x :=
    (hg i).sub (h i).continuous.measurable
  have hgh_bdd (i : Fin k) (x : UnitAddCircle) : |g i x - h i x| ≤ C i + ‖h i‖ :=
    (abs_sub _ _).trans (add_le_add (hC i x) ((Real.norm_eq_abs _).symm.trans_le
      ((h i).norm_coe_le_norm x)))
  have hFint (i : Fin k) :=
    (UnitAddCircle.integrable_integral_uniformOn_coset (hgh_meas i) (hgh_bdd i) hN.ne').abs
  have hFle : ∫ x₀, F x₀ ≤ δ / 4 := by
    rw [hF_def, integral_finsetSum _ fun i _ ↦ hFint i]
    calc ∑ i, ∫ x₀, |∫ x, (g i x - h i x) ∂uniformOn
          {x | x - x₀ ∈ AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)}|
    _ ≤ ∑ _i : Fin k, η := Finset.sum_le_sum fun i _ ↦
        (UnitAddCircle.integral_abs_integral_uniformOn_coset_le (hgh_meas i) (hgh_bdd i)
          hN.ne').trans (hh i)
    _ = k * η := by simp
    _ ≤ δ / 4 := by
      rw [hη_def]
      calc (k : ℝ) * (δ / (4 * (k + 1))) = (δ / 4) * (k / (k + 1)) := by field_simp
      _ ≤ δ / 4 * 1 := by gcongr; exact (div_le_one (by positivity)).2 (by linarith)
      _ = δ / 4 := mul_one _
  obtain ⟨x₀, hx₀⟩ := exists_le_integral (integrable_finsetSum _ fun i _ ↦ hFint i)
  have hU := isProbabilityMeasure_uniformOn (UnitAddCircle.finite_coset x₀ N) ⟨x₀, by simp⟩
  have h2 (i : Fin k) := hN₀ i N (hNi i) hN x₀
  set U : Measure UnitAddCircle :=
    uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} with hU_def
  refine ⟨_, ⟨x₀, N, rfl⟩, fun i ↦ ?_⟩
  have hci : Integrable (g i) U := LMLExplore.integrable_of_abs_le (hg i) (hC i) _
  have hhi : Integrable (h i) U := (h i).integrable _
  refine LMLExplore.abs_integral_mixture_sub_le hε hci (hgi i) ?_
  -- the average of `g i` on the coset is close to its integral
  have h1 : |∫ x, g i x ∂U - ∫ x, h i x ∂U| ≤ δ / 4 := by
    rw [← integral_sub hci hhi]
    refine le_trans ?_ (hx₀.trans hFle)
    exact Finset.single_le_sum (f := fun i ↦ |∫ x, (g i x - h i x) ∂U|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)
  have h3 : |(∫ x, h i x) - ∫ x, g i x| ≤ η := by
    rw [← integral_sub ((h i).integrable _) (hgi i)]
    refine abs_integral_le_integral_abs.trans (le_of_eq_of_le ?_ (hh i))
    simp_rw [Real.norm_eq_abs, abs_sub_comm]
  have := abs_sub_le (∫ x, g i x ∂U) (∫ x, h i x ∂U) (∫ x, g i x)
  have := abs_sub_le (∫ x, h i x ∂U) (∫ x, h i x) (∫ x, g i x)
  linarith [h2 i]

/-- **The neighbourhood envelope of the coset null is zero** [EVR26, Note 19]: the smallest
relative entropy to the coset null is not lower semicontinuous at Lebesgue measure in the
neighbourhood sense for `ε < 1`, although the bipolar rate equals it
(`ProbabilityTheory.bipolarRate_coset_mixtures`, `ProbabilityTheory.klInf_coset_mixtures`). -/
theorem tauEnvelope_klInf_coset_mixtures_eq_zero (hε : ε ≤ 1) :
    tauEnvelope (fun R ↦ klInf R {(1 - ε) • uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples
      (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} + ε • volume | (x₀ : UnitAddCircle) (N : ℕ)})
      volume = 0 := by
  have hS := fun P hP ↦ isProbabilityMeasure_of_mem_coset_mixtures (P := P) hε hP
  refine le_antisymm (tauEnvelope_le_iff.2 fun k g hg hgb δ hδ ↦ ?_)
    ((maxEPower_nonneg _ fun P hP ↦ (hS P hP).measure_univ.le).trans
      (maxEPower_le_tauEnvelope_klInf _ _ hS))
  obtain ⟨P, hP, hPg⟩ := exists_coset_mixture_forall_abs_integral_sub_le hε hg hgb hδ
  have := hS P hP
  refine (tauNbhdInf_le this hPg).trans ((klInf_le_klIntegral hP).trans ?_)
  rw [klIntegral_eq_klDiv rfl, klDiv_self, EReal.coe_ennreal_zero]

/-- **The sequential envelope of the coset null is `log (1 / ε)`** [EVR26, Note 19]: the
smallest relative entropy to the coset null is lower semicontinuous at Lebesgue measure in the
sequential sense. -/
theorem seqTauEnvelope_klInf_coset_mixtures (hε : ε ≤ 1) :
    seqTauEnvelope (fun R ↦ klInf R {(1 - ε) • uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples
      (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} + ε • volume | (x₀ : UnitAddCircle) (N : ℕ)})
      volume = ENNReal.log ε⁻¹ :=
  le_antisymm (seqTauEnvelope_le.trans (klInf_coset_mixtures hε).le)
    ((seqTauEnvelope_klInf_finitelySupported_mixtures volume hε).symm.le.trans
      (seqTauEnvelope_mono fun _ _ ↦
        klInf_anti (coset_mixtures_subset_finitelySupported_mixtures ε)))

/-! ### The rate is not a function of the single-letter envelopes -/

/-- **No single-letter formula for the bipolar rate** [EVR26, Note 19]. On the circle, the bipolar
rate at Lebesgue measure of a null of probability measures is not a function of the largest
e-power `a 1`, of the neighbourhood and sequential envelopes of the smallest relative entropy and
of the smallest relative entropy itself. For `ε < 1`, the coset null and the finite-support null
have the same `a 1` (zero), the same envelopes (`0` and `log (1 / ε)`) and the same smallest
relative entropy (`log (1 / ε)`), and the bipolar rates `log (1 / ε)` and `0`. -/
theorem not_exists_forall_bipolarRate_eq_envelopes :
    ¬ ∃ f : EReal → EReal → EReal → EReal → EReal, ∀ S : Set (Measure UnitAddCircle),
      (∀ P ∈ S, IsProbabilityMeasure P) →
      bipolarRate volume S = f (maxLogGrowth volume S 1) (tauEnvelope (fun R ↦ klInf R S) volume)
        (seqTauEnvelope (fun R ↦ klInf R S) volume) (klInf volume S) := by
  rintro ⟨f, hf⟩
  have hε : (2⁻¹ : ℝ≥0∞) ≤ 1 := ENNReal.inv_le_one.2 one_le_two
  have hc := hf {(1 - 2⁻¹) • uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples
    (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} + 2⁻¹ • volume | (x₀ : UnitAddCircle) (N : ℕ)}
    fun P hP ↦ isProbabilityMeasure_of_mem_coset_mixtures hε hP
  have hs := hf {(1 - 2⁻¹) • F + 2⁻¹ • volume | (F : Measure UnitAddCircle)
    (_ : IsProbabilityMeasure F) (_ : ∃ s : Set UnitAddCircle, s.Finite ∧ F sᶜ = 0)}
    fun P hP ↦ isProbabilityMeasure_of_mem_finitelySupported_mixtures hε hP
  rw [bipolarRate_coset_mixtures hε, maxLogGrowth_one_coset_mixtures_eq_zero hε,
    tauEnvelope_klInf_coset_mixtures_eq_zero hε, seqTauEnvelope_klInf_coset_mixtures hε,
    klInf_coset_mixtures hε] at hc
  rw [bipolarRate_finitelySupported_mixtures_eq_zero _ hε,
    maxLogGrowth_finitelySupported_mixtures_eq_zero _ hε,
    tauEnvelope_klInf_finitelySupported_mixtures_eq_zero _ hε,
    seqTauEnvelope_klInf_finitelySupported_mixtures _ hε, klInf_finitelySupported_mixtures _ hε,
    ← hc, inv_inv, eq_comm, ENNReal.log_eq_one_iff] at hs
  exact OfNat.ofNat_ne_one 2 hs

end ProbabilityTheory
