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
less than its tolerance (`MeasureTheory.exists_measurable_finite_range_forall_abs_comp_sub_lt`).
For the coset null, the average `T_N f (x₀)` of a bounded measurable `f` on the coset
`x₀ + (1 / N) ℤ` is a contraction of `L¹(volume)` in `f`, and tends to `∫ f` uniformly in `x₀`
for a continuous `f`, by uniform continuity; with the density of the bounded continuous functions
in `L¹`, some coset has averages of the statistics close to their integrals. The lower bound on
the sequential envelope is the Donsker–Varadhan inequality for `t 𝟙_{sᶜ}`, with `s` the finite set
that carries `F`, as `t → ∞`.

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

/-- Mixing a measure `F` with `Q`, with weights `1 - ε` and `ε`, brings its integral of `f`
closer to that of `Q`. -/
private lemma abs_integral_mixture_sub_le {F Q : Measure 𝓧} (hε : ε ≤ 1) {f : 𝓧 → ℝ}
    (hfF : Integrable f F) (hfQ : Integrable f Q) {δ : ℝ} (h : |∫ x, f x ∂F - ∫ x, f x ∂Q| ≤ δ) :
    |∫ x, f x ∂((1 - ε) • F + ε • Q) - ∫ x, f x ∂Q| ≤ δ := by
  have hεt : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hε
  rw [integral_add_measure (hfF.smul_measure (by simp)) (hfQ.smul_measure hεt),
    integral_smul_measure, integral_smul_measure]
  have hsum : (1 - ε).toReal + ε.toReal = 1 := by
    rw [← ENNReal.toReal_add (by simp) hεt, tsub_add_cancel_of_le hε, ENNReal.toReal_one]
  have h1 : 0 ≤ (1 - ε).toReal := ENNReal.toReal_nonneg
  have h1' : (1 - ε).toReal ≤ 1 := by linarith [ENNReal.toReal_nonneg (a := ε)]
  have heq : (1 - ε).toReal • (∫ x, f x ∂F) + ε.toReal • (∫ x, f x ∂Q) - ∫ x, f x ∂Q =
      (1 - ε).toReal * (∫ x, f x ∂F - ∫ x, f x ∂Q) := by
    rw [smul_eq_mul, smul_eq_mul]
    linear_combination (∫ x, f x ∂Q) * hsum
  rw [heq, abs_mul, abs_of_nonneg h1]
  calc (1 - ε).toReal * |∫ x, f x ∂F - ∫ x, f x ∂Q|
  _ ≤ 1 * δ := mul_le_mul h1' h (abs_nonneg _) zero_le_one
  _ = δ := one_mul δ

/-! ### The finite-support null -/

/-- The members of the finite-support null are probability measures. -/
private lemma isProbabilityMeasure_of_mem_finitelySupported_mixtures {Q : Measure 𝓧}
    [IsProbabilityMeasure Q] (hε : ε ≤ 1) {P : Measure 𝓧}
    (hP : P ∈ {(1 - ε) • F + ε • Q | (F : Measure 𝓧) (_ : IsProbabilityMeasure F)
      (_ : ∃ s : Set 𝓧, s.Finite ∧ F sᶜ = 0)}) :
    IsProbabilityMeasure P := by
  obtain ⟨F, hF, -, rfl⟩ := hP
  exact ⟨by simp [tsub_add_cancel_of_le hε]⟩

/-- **The neighbourhood envelope of the finite-support null is zero** [EVR26, Note 19]. For every
probability measure `Q` on a measurable space with measurable singletons and `ε ≤ 1`, every basic
neighbourhood of `Q` contains a mixture `(1 - ε) F + ε Q` with `F` carried by a finite set, at
which the smallest relative entropy to the null vanishes. -/
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
  obtain ⟨s, hs, hsf, hsg⟩ := exists_measurable_finite_range_forall_abs_comp_sub_lt hg hgb hδ
  have hF : Q.map s (Set.range s)ᶜ = 0 := by
    rw [Measure.map_apply hs hsf.measurableSet.compl, Set.preimage_compl, Set.preimage_range,
      Set.compl_univ, measure_empty]
  have hP : (1 - ε) • Q.map s + ε • Q ∈ S := ⟨Q.map s, inferInstance, ⟨_, hsf, hF⟩, rfl⟩
  have := hS _ hP
  refine (tauNbhdInf_le this fun i ↦ ?_).trans ((klInf_le_klIntegral hP).trans ?_)
  · obtain ⟨C, hC⟩ := hgb i
    refine abs_integral_mixture_sub_le hε (LMLExplore.integrable_of_abs_le (hg i) hC _)
      (LMLExplore.integrable_of_abs_le (hg i) hC _) ?_
    rw [integral_map hs.aemeasurable (hg i).aestronglyMeasurable,
      ← integral_sub (LMLExplore.integrable_of_abs_le (f := fun x ↦ g i (s x)) ((hg i).comp hs)
        (fun x ↦ hC (s x)) Q) (LMLExplore.integrable_of_abs_le (hg i) hC Q)]
    exact LMLExplore.abs_integral_le_of_abs_le fun x ↦ (hsg i x).le
  · rw [klIntegral_eq_klDiv rfl, klDiv_self, EReal.coe_ennreal_zero]

/-- **The sequential envelope of the finite-support null is `log (1 / ε)`** [EVR26, Note 19].
For a probability measure `Q` without atoms on a measurable space with measurable singletons, the
smallest relative entropy to the null of the mixtures `(1 - ε) F + ε Q`, with `F` carried by a
finite set, is lower semicontinuous at `Q` in the sequential sense, while the bipolar rate is `0`
(`ProbabilityTheory.bipolarRate_finitelySupported_mixtures_eq_zero`). Probability measures `R k`
that converge to `Q` on every measurable set give a vanishing mass to the countable set `C` of
their atoms, hence to every finite set; a member `(1 - ε) F + ε Q` with `F` carried by a finite
set `s` gives mass `ε` to the complement of `s`, and the Donsker–Varadhan bound for `t 𝟙_{sᶜ}`
gives `klDiv (R k) P ≥ t (1 - R k C) - log (ε e^t + 1 - ε)`. Let `k → ∞`, then `t → ∞`. -/
theorem seqTauEnvelope_klInf_finitelySupported_mixtures [MeasurableSingletonClass 𝓧]
    (Q : Measure 𝓧) [IsProbabilityMeasure Q] [NullSingletonClass Q] (hε : ε ≤ 1) :
    seqTauEnvelope (fun R ↦ klInf R {(1 - ε) • F + ε • Q | (F : Measure 𝓧)
      (_ : IsProbabilityMeasure F) (_ : ∃ s : Set 𝓧, s.Finite ∧ F sᶜ = 0)}) Q =
      ENNReal.log ε⁻¹ := by
  set S := {(1 - ε) • F + ε • Q | (F : Measure 𝓧) (_ : IsProbabilityMeasure F)
    (_ : ∃ s : Set 𝓧, s.Finite ∧ F sᶜ = 0)}
  refine le_antisymm (seqTauEnvelope_le.trans (klInf_finitelySupported_mixtures Q hε).le)
    (le_seqTauEnvelope_iff.2 fun R hR hRQ ↦ ?_)
  have := hR
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
  set e := ε.toReal with he_def
  have he1 : e ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hε)
  -- the bound at a level `t ≥ 0`, for each `k`
  have key (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
      ((t * (1 - (R k).real C) - Real.log (e * Real.exp t + (1 - e)) : ℝ) : EReal) ≤
        klInf (R k) S := by
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
    have hRs : (R k).real s ≤ (R k).real C := by
      have hdiff : R k (s \ C) = 0 := by
        rw [← Set.biUnion_of_singleton (s \ C),
          measure_biUnion_null_iff (hs.countable.mono Set.sdiff_subset)]
        intro x hx
        have hxC : x ∉ C := hx.2
        simp only [hC_def, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hxC
        exact le_antisymm (hxC k) zero_le
      have h := measure_le_inter_add_sdiff (R k) s C
      rw [hdiff, add_zero] at h
      exact ENNReal.toReal_mono (measure_ne_top _ _) (h.trans (measure_mono Set.inter_subset_right))
    have hRf : ∫ x, f x ∂R k = t * (1 - (R k).real s) := by
      rw [hf_def, integral_indicator_const _ hsm, probReal_compl_eq_one_sub hs.measurableSet,
        smul_eq_mul, mul_comm]
    have hDV := TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv (μ := R k)
      (ν := (1 - ε) • F + ε • Q) ((integrable_const t).indicator hsm) hexpi
    rw [klIntegral_eq_klDiv (by simp [tsub_add_cancel_of_le hε])]
    calc ((t * (1 - (R k).real C) - Real.log (e * Real.exp t + (1 - e)) : ℝ) : EReal)
    _ ≤ ((∫ x, f x ∂R k - Real.log (∫ x, Real.exp (f x) ∂((1 - ε) • F + ε • Q)) : ℝ) :
        EReal) := by
      rw [hRf, hZ]
      exact EReal.coe_le_coe_iff.2 (by nlinarith)
    _ ≤ ((ENNReal.ofReal (∫ x, f x ∂R k -
        Real.log (∫ x, Real.exp (f x) ∂((1 - ε) • F + ε • Q))) : ℝ≥0∞) : EReal) := by
      rw [EReal.coe_ennreal_ofReal]
      exact EReal.coe_le_coe_iff.2 (le_max_left _ _)
    _ ≤ (klDiv (R k) ((1 - ε) • F + ε • Q) : EReal) :=
      EReal.coe_ennreal_le_coe_ennreal_iff.2 hDV
  -- let `k → ∞`
  have hlim (t : ℝ) (ht : 0 ≤ t) : ((t - Real.log (e * Real.exp t + (1 - e)) : ℝ) : EReal) ≤
      liminf (fun k ↦ klInf (R k) S) atTop := by
    have htend : Tendsto (fun k ↦ ((t * (1 - (R k).real C) -
        Real.log (e * Real.exp t + (1 - e)) : ℝ) : EReal)) atTop
        (𝓝 ((t - Real.log (e * Real.exp t + (1 - e)) : ℝ) : EReal)) := by
      refine (continuous_coe_real_ereal.tendsto _).comp ?_
      simpa using ((hRC.const_sub 1).const_mul t).sub_const (Real.log (e * Real.exp t + (1 - e)))
    rw [← htend.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall (key t ht))
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
        rw [ENNReal.log_inv, ENNReal.log_pos_real hε0 hεt]
        rfl
      rw [hlogε, EReal.coe_lt_coe_iff] at hc
      -- `t - log (e e^t + 1 - e) = - log (e + (1 - e) e^{-t}) → - log e`
      have hφ : Tendsto (fun t : ℝ ↦ -Real.log (e + (1 - e) * Real.exp (-t))) atTop
          (𝓝 (-Real.log e)) := by
        have h1 : Tendsto (fun t : ℝ ↦ e + (1 - e) * Real.exp (-t)) atTop (𝓝 e) := by
          simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (1 - e)).const_add e
        exact ((Real.continuousAt_log hepos.ne').tendsto.comp h1).neg
      obtain ⟨t, hct, ht⟩ := ((hφ.eventually (lt_mem_nhds hc)).and
        (eventually_ge_atTop 0)).exists
      refine le_trans (EReal.coe_le_coe_iff.2 hct.le) (le_of_eq_of_le ?_ (hlim t ht))
      congr 1
      have hpos : 0 < e + (1 - e) * Real.exp (-t) := by
        have := Real.exp_pos (-t)
        nlinarith
      have h2 : e * Real.exp t + (1 - e) = Real.exp t * (e + (1 - e) * Real.exp (-t)) := by
        rw [mul_add, ← mul_assoc, mul_comm (Real.exp t) (1 - e), mul_assoc, ← Real.exp_add,
          add_neg_cancel, Real.exp_zero, mul_one, mul_comm]
      rw [h2, Real.log_mul (Real.exp_pos t).ne' hpos.ne', Real.log_exp]
      ring

/-! ### The cosets of the circle -/

/-- The uniform law on the points `x₀ + j / N`, `j < N`, of the circle. -/
private noncomputable def cosetLaw (x₀ : UnitAddCircle) (N : ℕ) : Measure UnitAddCircle :=
  (N : ℝ≥0∞)⁻¹ • ∑ j ∈ Finset.range N,
    Measure.dirac (x₀ + (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle))

/-- For `N ≠ 0`, the uniform law on the coset `x₀ + (1 / N) ℤ` of the circle is the uniform law on
the points `x₀ + j / N`, `j < N`: these points are distinct and form the coset. -/
private lemma uniformOn_coset_eq_cosetLaw (x₀ : UnitAddCircle) {N : ℕ} (hN : N ≠ 0) :
    uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} =
      cosetLaw x₀ N := by
  classical
  set f : ℕ → UnitAddCircle := fun j ↦ x₀ + (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle) with hf
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
  -- the points `x₀ + j / N`, `j < N`, are distinct
  have hinj : Set.InjOn f (Finset.range N) := by
    intro j hj k hk h
    have hmem (i : ℕ) (hi : i ∈ (Finset.range N : Set ℕ)) :
        (i : ℝ) / N ∈ Set.Ico (0 : ℝ) (0 + 1) :=
      ⟨by positivity, by rw [zero_add, div_lt_one hN']; exact_mod_cast Finset.mem_range.1 hi⟩
    have h' := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem j hj) (hmem k hk)).1 (add_left_cancel h)
    exact_mod_cast (div_left_inj₀ hN'.ne').1 h'
  -- and they form the coset
  have hset : {x | x - x₀ ∈ AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} =
      ↑((Finset.range N).image f) := by
    ext x
    simp only [Set.mem_ofPred_eq, AddSubgroup.mem_zmultiples_iff, Finset.coe_image,
      Finset.coe_range, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨k, hk⟩
      have hr := Int.emod_nonneg k (Int.natCast_ne_zero.2 hN)
      have hrN := Int.emod_lt_of_pos k (Int.natCast_pos.2 (Nat.pos_of_ne_zero hN))
      refine ⟨(k % N).toNat, by omega, ?_⟩
      rw [hf, ← eq_sub_iff_add_eq', ← hk, ← AddCircle.coe_zsmul, zsmul_eq_mul]
      have hj : (((k % N).toNat : ℕ) : ℝ) = k - N * ((k / N : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hr, Int.emod_def]
        push_cast
        ring
      have hk' : (k : ℝ) * (N : ℝ)⁻¹ = (((k % N).toNat : ℕ) : ℝ) / N + ((k / N : ℤ) : ℝ) := by
        rw [hj]
        field_simp
        ring
      rw [hk', AddCircle.coe_add, ((AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨k / N, by simp⟩ :
        (((k / N : ℤ) : ℝ) : UnitAddCircle) = 0), add_zero]
    · rintro ⟨j, -, rfl⟩
      refine ⟨j, ?_⟩
      rw [hf, add_sub_cancel_left, ← AddCircle.coe_zsmul, zsmul_eq_mul, div_eq_mul_inv]
      push_cast
      rfl
  rw [hset]
  ext t ht
  rw [uniformOn, cond_apply (Finset.measurableSet _), Measure.count_apply_finset,
    Finset.card_image_of_injOn hinj, Finset.card_range, cosetLaw, smul_apply, smul_eq_mul,
    _root_.sum_apply]
  congr 1
  have hT : ↑((Finset.range N).image f) ∩ t = (↑(((Finset.range N).image f).filter (· ∈ t)) :
      Set UnitAddCircle) := by
    ext
    simp
  rw [hT, Measure.count_apply_finset, Finset.card_filter, Nat.cast_sum, Finset.sum_image hinj]
  simp [hf, Measure.dirac_apply' _ ht, Set.indicator_apply]

/-- The coset `x₀ + (1 / N) ℤ` of the circle is finite. -/
private lemma finite_coset (x₀ : UnitAddCircle) (N : ℕ) :
    {x | x - x₀ ∈ AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)}.Finite := by
  have h : IsOfFinAddOrder (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle) := by
    rcases eq_or_ne N 0 with rfl | hN
    · simp
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, Nat.pos_of_ne_zero hN, ?_⟩
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN)]
    exact AddCircle.coe_period 1
  have := h.finite_zmultiples
  exact (Set.toFinite _).preimage sub_left_injective.injOn

/-- The uniform law on a coset `x₀ + (1 / N) ℤ` of the circle is a probability measure. -/
private lemma isProbabilityMeasure_uniformOn_coset (x₀ : UnitAddCircle) (N : ℕ) :
    IsProbabilityMeasure (uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples
      (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)}) :=
  isProbabilityMeasure_uniformOn (finite_coset x₀ N) ⟨x₀, by simp⟩

/-- The coset null is contained in the finite-support null. -/
private lemma coset_mixtures_subset_finitelySupported_mixtures (ε : ℝ≥0∞) :
    {(1 - ε) • uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} +
      ε • volume | (x₀ : UnitAddCircle) (N : ℕ)} ⊆
    {(1 - ε) • F + ε • volume | (F : Measure UnitAddCircle) (_ : IsProbabilityMeasure F)
      (_ : ∃ s : Set UnitAddCircle, s.Finite ∧ F sᶜ = 0)} := by
  rintro _ ⟨x₀, N, rfl⟩
  exact ⟨_, isProbabilityMeasure_uniformOn_coset x₀ N, ⟨_, finite_coset x₀ N,
    (uniformOn_eq_zero_iff (finite_coset x₀ N)).2 (Set.inter_compl_self _)⟩, rfl⟩

/-- The members of the coset null are probability measures. -/
private lemma isProbabilityMeasure_of_mem_coset_mixtures (hε : ε ≤ 1) {P : Measure UnitAddCircle}
    (hP : P ∈ {(1 - ε) • uniformOn {x | x - x₀ ∈ AddSubgroup.zmultiples
      (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle)} + ε • volume | (x₀ : UnitAddCircle) (N : ℕ)}) :
    IsProbabilityMeasure P :=
  isProbabilityMeasure_of_mem_finitelySupported_mixtures hε
    (coset_mixtures_subset_finitelySupported_mixtures ε hP)

/-- The integral against the uniform law on the points `x₀ + j / N` is their average. -/
private lemma integral_cosetLaw (f : UnitAddCircle → ℝ) (x₀ : UnitAddCircle) (N : ℕ) :
    ∫ x, f x ∂cosetLaw x₀ N =
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, f (x₀ + (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)) := by
  rw [cosetLaw, integral_smul_measure, integral_finsetSum_measure
    fun j _ ↦ integrable_dirac eNorm_lt_top]
  simp [integral_dirac, ENNReal.toReal_inv, smul_eq_mul]

/-- The uniform law on a coset depends only on the coset: shifting the base point by a multiple
of `1 / N` does not change it. -/
private lemma cosetLaw_add_intCast_div (x₀ : UnitAddCircle) {N : ℕ} (hN : 0 < N) (m : ℤ) :
    cosetLaw (x₀ + (((m : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)) N = cosetLaw x₀ N := by
  rw [← uniformOn_coset_eq_cosetLaw _ hN.ne', ← uniformOn_coset_eq_cosetLaw _ hN.ne']
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  have hc : (((m : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle) ∈
      AddSubgroup.zmultiples (((N : ℝ)⁻¹ : ℝ) : UnitAddCircle) :=
    ⟨m, by beta_reduce; rw [← AddCircle.coe_zsmul, zsmul_eq_mul, div_eq_mul_inv]⟩
  rw [sub_add_eq_sub_sub, sub_eq_add_neg (x - x₀)]
  exact AddSubgroup.add_mem_cancel_right _ (neg_mem hc)

/-- For any two points of the circle and `N ≠ 0`, some shift of the first by a multiple of
`1 / N` is within `1 / (2 N)` of the second. -/
private lemma exists_norm_add_intCast_div_sub_le (y x₀ : UnitAddCircle) {N : ℕ} (hN : 0 < N) :
    ∃ m : ℤ, ‖y + (((m : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle) - x₀‖ ≤ 1 / (2 * N) := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (x₀ - y)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  refine ⟨round (N * t), ?_⟩
  have h : y + ((((round (N * t) : ℤ) : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle) - x₀ =
      ((((round (N * t) : ℤ) : ℝ) / N - t : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_sub]
    change _ = _ - (QuotientAddGroup.mk t : UnitAddCircle)
    rw [ht]
    abel
  rw [h, UnitAddCircle.norm_eq]
  calc |(((round (N * t) : ℤ) : ℝ) / N - t) - round ((((round (N * t) : ℤ) : ℝ) / N - t))|
  _ ≤ |(((round (N * t) : ℤ) : ℝ) / N - t) - ((0 : ℤ) : ℝ)| := round_le _ 0
  _ = |N * t - round (N * t)| / N := by
    rw [Int.cast_zero, sub_zero, ← abs_neg, neg_sub,
      show t - ((round (N * t) : ℤ) : ℝ) / N = (N * t - round (N * t)) / N by field_simp,
      abs_div, abs_of_pos hN']
  _ ≤ (1 / 2) / N := by gcongr; exact abs_sub_round _
  _ = 1 / (2 * N) := by field_simp

/-- **Uniform Riemann sums on the cosets.** For a bounded continuous function `h` on the circle
and `η > 0`, for `N` large the average of `h` on every coset `x₀ + (1 / N) ℤ` is within `η` of its
integral: by uniform continuity, two coset averages are within `η`, and the average of the coset
averages over `x₀` is the integral. -/
private lemma exists_forall_abs_integral_cosetLaw_sub_le (h : UnitAddCircle →ᵇ ℝ) {η : ℝ}
    (hη : 0 < η) : ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → 0 < N → ∀ x₀,
      |∫ x, h x ∂cosetLaw x₀ N - ∫ x, h x| ≤ η := by
  obtain ⟨δ, hδ, hδh⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous h.continuous) η hη
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / δ)
  refine ⟨N₀, fun N hN hN0 x₀ ↦ ?_⟩
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN0
  have hNδ : 1 / (2 * (N : ℝ)) < δ := by
    have h1 : 1 / δ < N := hN₀.trans_le (by exact_mod_cast hN)
    rw [div_lt_iff₀ hδ] at h1
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hint (c : UnitAddCircle) : Integrable (fun y ↦ h (y + c)) (volume : Measure UnitAddCircle) :=
    .of_bound (h.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable ‖h‖
      (.of_forall fun y ↦ h.norm_coe_le_norm _)
  -- the average over the base points of the coset averages is the integral
  have hTint : Integrable (fun y ↦ ∫ x, h x ∂cosetLaw y N) (volume : Measure UnitAddCircle) := by
    simp_rw [integral_cosetLaw]
    exact (integrable_finsetSum _ fun j _ ↦ hint _).const_mul _
  have hmean : ∫ y, (∫ x, h x ∂cosetLaw y N) = ∫ x, h x := by
    simp_rw [integral_cosetLaw]
    rw [integral_const_mul, integral_finsetSum _ fun j _ ↦ hint _]
    simp_rw [integral_add_right_eq_self (fun x ↦ h x)]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN'.ne',
      one_mul]
  -- two coset averages are within `η`
  have hpt (y : UnitAddCircle) :
      ‖∫ x, h x ∂cosetLaw x₀ N - ∫ x, h x ∂cosetLaw y N‖ ≤ η := by
    obtain ⟨m, hm⟩ := exists_norm_add_intCast_div_sub_le y x₀ hN0
    rw [← cosetLaw_add_intCast_div y hN0 m, integral_cosetLaw, integral_cosetLaw, ← mul_sub,
      ← Finset.sum_sub_distrib, Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast]
    calc (N : ℝ)⁻¹ * |∑ j ∈ Finset.range N,
          (h (x₀ + (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)) -
            h (y + (((m : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle) +
              (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)))|
    _ ≤ (N : ℝ)⁻¹ * ∑ _j ∈ Finset.range N, η := by
      gcongr
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      have hd : dist (x₀ + (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle))
          (y + (((m : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle) +
            (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)) < δ := by
        rw [dist_add_right, dist_comm, dist_eq_norm]
        exact hm.trans_lt hNδ
      have := hδh hd
      rw [Real.dist_eq] at this
      exact this.le
    _ = η := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN'.ne',
        one_mul]
  rw [← hmean]
  calc |∫ x, h x ∂cosetLaw x₀ N - ∫ y, (∫ x, h x ∂cosetLaw y N)|
  _ = ‖∫ y, (∫ x, h x ∂cosetLaw x₀ N - ∫ x, h x ∂cosetLaw y N)‖ := by
    rw [integral_sub (integrable_const _) hTint, integral_const, probReal_univ, one_smul,
      Real.norm_eq_abs]
  _ ≤ η * (volume : Measure UnitAddCircle).real Set.univ :=
    norm_integral_le_of_norm_le_const (.of_forall hpt)
  _ = η := by rw [probReal_univ, mul_one]

/-- The coset average of a bounded measurable function is an integrable function of the base
point. -/
private lemma integrable_integral_cosetLaw {f : UnitAddCircle → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) (N : ℕ) :
    Integrable (fun x₀ ↦ ∫ x, f x ∂cosetLaw x₀ N) (volume : Measure UnitAddCircle) := by
  simp_rw [integral_cosetLaw]
  exact (integrable_finsetSum _ fun j _ ↦
    LMLExplore.integrable_of_abs_le (hf.comp (measurable_add_const _)) (fun y ↦ hC _) _).const_mul _

/-- **The coset averages are a contraction of `L¹`**: the integral over the base points of the
absolute value of the coset average of `f` is at most the integral of `|f|`. -/
private lemma integral_abs_integral_cosetLaw_le {f : UnitAddCircle → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) {N : ℕ} (hN : 0 < N) :
    ∫ x₀, |∫ x, f x ∂cosetLaw x₀ N| ≤ ∫ x, ‖f x‖ := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hint (c : UnitAddCircle) :
      Integrable (fun y ↦ |f (y + c)|) (volume : Measure UnitAddCircle) :=
    LMLExplore.integrable_of_abs_le (hf.comp (measurable_add_const _)).abs
      (fun y ↦ by rw [abs_abs]; exact hC _) _
  calc ∫ x₀, |∫ x, f x ∂cosetLaw x₀ N|
  _ ≤ ∫ x₀, (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
      |f (x₀ + (((j : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle))| := by
    refine integral_mono (integrable_integral_cosetLaw hf hC N).abs
      ((integrable_finsetSum _ fun j _ ↦ hint _).const_mul _) fun x₀ ↦ ?_
    rw [integral_cosetLaw, abs_mul, abs_inv, Nat.abs_cast]
    gcongr
    exact Finset.abs_sum_le_sum_abs _ _
  _ = ∫ x, ‖f x‖ := by
    rw [integral_const_mul, integral_finsetSum _ fun j _ ↦ hint _]
    simp_rw [integral_add_right_eq_self (fun x ↦ |f x|)]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN'.ne',
      one_mul]
    simp_rw [Real.norm_eq_abs]

/-! ### The coset null -/

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
  choose N₀ hN₀ using fun i ↦ exists_forall_abs_integral_cosetLaw_sub_le (h i)
    (η := δ / 4) (by positivity)
  set N : ℕ := (Finset.univ.sup N₀) + 1 with hN_def
  have hN : 0 < N := Nat.succ_pos _
  have hNi (i : Fin k) : N₀ i ≤ N := (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _)
  -- a coset where every `g i - h i` has a small average
  set F : UnitAddCircle → ℝ := fun x₀ ↦ ∑ i, |∫ x, (g i x - h i x) ∂cosetLaw x₀ N| with hF_def
  have hgh_meas (i : Fin k) : Measurable fun x ↦ g i x - h i x :=
    (hg i).sub (h i).continuous.measurable
  have hgh_bdd (i : Fin k) (x : UnitAddCircle) : |g i x - h i x| ≤ C i + ‖h i‖ :=
    (abs_sub _ _).trans (add_le_add (hC i x) ((Real.norm_eq_abs _).symm.trans_le
      ((h i).norm_coe_le_norm x)))
  have hFint (i : Fin k) := (integrable_integral_cosetLaw (hgh_meas i) (hgh_bdd i) N).abs
  have hFle : ∫ x₀, F x₀ ≤ δ / 4 := by
    rw [hF_def, integral_finsetSum _ fun i _ ↦ hFint i]
    calc ∑ i, ∫ x₀, |∫ x, (g i x - h i x) ∂cosetLaw x₀ N|
    _ ≤ ∑ _i : Fin k, η := Finset.sum_le_sum fun i _ ↦
        (integral_abs_integral_cosetLaw_le (hgh_meas i) (hgh_bdd i) hN).trans (hh i)
    _ = k * η := by simp
    _ ≤ δ / 4 := by
      rw [hη_def]
      calc (k : ℝ) * (δ / (4 * (k + 1))) = (δ / 4) * (k / (k + 1)) := by field_simp
      _ ≤ δ / 4 * 1 := by gcongr; exact (div_le_one (by positivity)).2 (by linarith)
      _ = δ / 4 := mul_one _
  obtain ⟨x₀, hx₀⟩ := exists_le_integral (integrable_finsetSum _ fun i _ ↦ hFint i)
  have hU := isProbabilityMeasure_uniformOn_coset x₀ N
  refine ⟨_, ⟨x₀, N, rfl⟩, fun i ↦ ?_⟩
  rw [uniformOn_coset_eq_cosetLaw x₀ hN.ne'] at hU ⊢
  have hci : Integrable (g i) (cosetLaw x₀ N) := LMLExplore.integrable_of_abs_le (hg i) (hC i) _
  have hhi : Integrable (h i) (cosetLaw x₀ N) := (h i).integrable _
  refine abs_integral_mixture_sub_le hε hci (hgi i) ?_
  -- the average of `g i` on the coset is close to its integral
  have h1 : |∫ x, g i x ∂cosetLaw x₀ N - ∫ x, h i x ∂cosetLaw x₀ N| ≤ δ / 4 := by
    rw [← integral_sub hci hhi]
    refine le_trans ?_ (hx₀.trans hFle)
    exact Finset.single_le_sum (f := fun i ↦ |∫ x, (g i x - h i x) ∂cosetLaw x₀ N|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)
  have h2 := hN₀ i N (hNi i) hN x₀
  have h3 : |(∫ x, h i x) - ∫ x, g i x| ≤ η := by
    rw [← integral_sub ((h i).integrable _) (hgi i)]
    refine abs_integral_le_integral_abs.trans (le_of_eq_of_le ?_ (hh i))
    simp_rw [Real.norm_eq_abs, abs_sub_comm]
  have := abs_sub_le (∫ x, g i x ∂cosetLaw x₀ N) (∫ x, h i x ∂cosetLaw x₀ N) (∫ x, g i x)
  have := abs_sub_le (∫ x, h i x ∂cosetLaw x₀ N) (∫ x, h i x) (∫ x, g i x)
  linarith

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
sequential sense. The lower bound is that of the larger finite-support null
(`ProbabilityTheory.seqTauEnvelope_klInf_finitelySupported_mixtures`). -/
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
