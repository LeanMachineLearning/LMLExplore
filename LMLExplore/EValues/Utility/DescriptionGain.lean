/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.Measure.SigmaConvex
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Integral.Indicator
import LMLExplore.Analysis.SpecificLimits.Basic
import LMLExplore.MeasureTheory.Measure.Decomposition.RadonNikodym
import LMLExplore.MeasureTheory.Measure.TotalVariation.Basic

/-!
# The description gain of a σ-convex set and of its closure in total variation

Lardy, Grünwald and Harremoës [LGH24] describe the reverse information projection of a measure `P`
on a set `𝒞` of measures with densities with respect to a σ-finite measure `μ` through the
description gain
`D(P‖Q ⇝ R) = ∫ ln (r / q) dP - (R(Ω) - Q(Ω))`,
with `r`, `q` the densities of `R`, `Q` with respect to `μ`, and the gain
`D(P‖Q ⇝ 𝒞) = ⨆ R ∈ 𝒞, D(P‖Q ⇝ R)` of the set. They conjecture that replacing a σ-convex set by
its Choquet-convex hull does not change the gain. This file proves that the gain of a σ-convex
set `𝒞` does not change when `𝒞` is replaced by any set between `𝒞` and its closure in total
variation [EVR26, Note 27, Theorem 2 (2)–(3)]; for a set that is only convex this holds when the
gain of `𝒞` is not `-∞`. The conjecture follows with [EVR26, Note 27, Theorem 2 (1)], not proved
here, by which the Choquet-convex hull of a convex set of measures with densities with respect to
`μ` lies in its closure in total variation.

The effective null of a null hypothesis is σ-convex
(`ProbabilityTheory.isSigmaConvex_effectiveSet`), and so is every polar.

## Main definitions

* `ProbabilityTheory.descriptionGain μ P Q R`: the description gain `D(P‖Q ⇝ R)`.

## Main statements

* `ProbabilityTheory.descriptionGain_le_iSup_of_isSigmaConvex`,
  `ProbabilityTheory.descriptionGain_le_iSup_of_convex`: for `𝒞` σ-convex, or convex with gain
  `> -∞`, `D(P‖Q ⇝ R) ≤ D(P‖Q ⇝ 𝒞)` for every `R` whose density is the `P`-almost everywhere
  limit of the densities of members `Qs n` of `𝒞` with `limsup Qs n (Ω) ≤ R(Ω)`.
* `ProbabilityTheory.descriptionGain_le_iSup_of_isSigmaConvex_of_tendsto_etvDist`,
  `ProbabilityTheory.descriptionGain_le_iSup_of_convex_of_tendsto_etvDist`: the same for every
  limit `R` in total variation of members of `𝒞`.
* `ProbabilityTheory.iSup_descriptionGain_eq_of_isSigmaConvex`,
  `ProbabilityTheory.iSup_descriptionGain_eq_of_convex`: every set between `𝒞` and its closure in
  total variation has the gain of `𝒞`.

## Implementation notes

The description gain is an extended integral (`∫ᵉ`) of `ENNReal.log (r / q)`. With the
conventions of `ℝ≥0∞`, `ln (x / 0) = +∞` for `x > 0` and `ln (0 / 0) = ln 0 = -∞`, and an
undefined integral (both parts infinite) is `⊥`, so that undefined gains count as `-∞`. The
measures need not be absolutely continuous with respect to `μ`: their singular parts enter the
gain through the masses only.

The proof follows [EVR26, Note 27], in the generality of its first remark: densities converging
`P`-almost everywhere, and `limsup` of the masses at most `R(Ω)`. In Step A, for σ-convex `𝒞`, a
countable mixture `Q₀ = ∑ₖ 2⁻¹ ^ (k + 1) Qs (φ k)` of members of `𝒞` has gain `> -∞`: the
negative part of `ln (q₀ / q)` is bounded by that of `ln (r / q)` plus `ln 2` times `2` plus the
number of indices `k` with `q_{φ k} < r / 2`, whose integral `∑ₖ P (q_{φ k} < r / 2)` is finite.
Step B mixes `s Q₀ + (1 - s) Qs n` for one small explicit weight `s`, with Fatou's lemma for the
nonnegative part `ln (1 + (1 - s) q_n / (s q₀))` and the weighted arithmetic-geometric mean
inequality for the concavity of the logarithm (`ENNReal.mul_log_add_mul_log_le_log`). A limit in
total variation is such a limit along a subsequence
(`MeasureTheory.exists_seq_tendsto_ae_rnDeriv_of_tendsto_etvDist`).

The proofs are adapted from the Lean file `Results/RenyiChoquet.lean` (Part 2) of
`EValuesResearch` [EVR26], where the closure in total variation is stated with the `L¹(μ)`
distance of the densities and the members of `𝒞` are assumed absolutely continuous with respect
to `μ`; here it is Mathlib's `etvDist`, with no such assumption.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 27, and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026.
* [LGH24] T. Lardy, P. Grünwald, P. Harremoës, *Reverse information projections and optimal
  e-statistics*, IEEE Trans. Inform. Theory 70 (2024), arXiv:2306.16646.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The description gain `D(P‖Q ⇝ R) = ∫ ln (r / q) dP - (R(Ω) - Q(Ω))` of Lardy, Grünwald and
Harremoës, where `r` and `q` are the densities of `R` and `Q` with respect to `μ`. The integral
is the extended integral of `ENNReal.log (r / q)`: `ln (x / 0) = +∞` for `x > 0`,
`ln (0 / 0) = -∞`, and an undefined integral is `⊥`, so that undefined gains count as `-∞`. -/
noncomputable def descriptionGain (μ P Q R : Measure Ω) : EReal :=
  ∫ᵉ ω, ENNReal.log (R.rnDeriv μ ω / Q.rnDeriv μ ω) ∂P - ((R univ : EReal) - Q univ)

variable {μ P Q R : Measure Ω}

/-- The definition of the description gain. -/
lemma descriptionGain_def : descriptionGain μ P Q R
    = ∫ᵉ ω, ENNReal.log (R.rnDeriv μ ω / Q.rnDeriv μ ω) ∂P - ((R univ : EReal) - Q univ) := (rfl)

/-! #### The description gain of a finite measure -/

/-- For a finite `R`, the description gain is the integral of `ln (r / q)` minus the real number
`R(Ω) - Q(Ω)`. -/
lemma descriptionGain_eq_sub [IsFiniteMeasure Q] (hR : R univ ≠ ∞) :
    descriptionGain μ P Q R = ∫ᵉ ω, ENNReal.log (R.rnDeriv μ ω / Q.rnDeriv μ ω) ∂P
      - ((R.real univ - Q.real univ : ℝ) : EReal) := by
  rw [descriptionGain, EReal.coe_sub, measureReal_def, measureReal_def,
    EReal.coe_ennreal_toReal hR, EReal.coe_ennreal_toReal (measure_ne_top Q univ)]

/-- A measure of infinite mass has description gain `⊥`. -/
lemma measure_univ_ne_top_of_descriptionGain_ne_bot [IsFiniteMeasure Q]
    (h : descriptionGain μ P Q R ≠ ⊥) : R univ ≠ ∞ := by
  intro hR
  apply h
  rw [descriptionGain, hR, EReal.coe_ennreal_top,
    ← EReal.coe_ennreal_toReal (measure_ne_top Q univ), EReal.top_sub_coe, EReal.sub_top]

/-- If the description gain is not `⊥`, neither is the integral of `ln (r / q)`. -/
lemma eintegral_ne_bot_of_descriptionGain_ne_bot [IsFiniteMeasure Q]
    (h : descriptionGain μ P Q R ≠ ⊥) :
    ∫ᵉ ω, ENNReal.log (R.rnDeriv μ ω / Q.rnDeriv μ ω) ∂P ≠ ⊥ := by
  intro h'
  apply h
  rw [descriptionGain_eq_sub (measure_univ_ne_top_of_descriptionGain_ne_bot h), h',
    EReal.bot_sub]

/-! #### Step A: a countable mixture with gain `> -∞` -/

/-- The pointwise bound of Step A of the proof of Theorem 2 of Note 27: if
`f₀ ≥ 2⁻¹ ^ (k + 1) F k` for all `k`, then the negative part of `ln (f₀ / q)` is at most that of
`ln (r / q)` plus `ln 2 · (N + 2)`, where `N` is the number of indices `k` with `F k < r / 2`. -/
private lemma toENNReal_neg_log_div_le {q r f₀ : ℝ≥0∞} {F : ℕ → ℝ≥0∞}
    (hf₀ : ∀ k, 2⁻¹ ^ (k + 1) * F k ≤ f₀) :
    (-ENNReal.log (f₀ / q)).toENNReal ≤ (-ENNReal.log (r / q)).toENNReal
      + ENNReal.ofReal (Real.log 2) * ((∑' k, if F k < r / 2 then (1 : ℝ≥0∞) else 0) + 2) := by
  have hc : ENNReal.ofReal (Real.log 2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.log_pos one_lt_two
  set N := ∑' k, if F k < r / 2 then (1 : ℝ≥0∞) else 0 with hN_def
  by_cases hN : N = ∞
  · simp [hN, ENNReal.mul_top hc]
  have hex : ∃ k, ¬ F k < r / 2 := by
    by_contra! h
    apply hN
    simp only [hN_def, h, ite_true]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  classical
  set k₀ := Nat.find hex
  have hk₀ : r / 2 ≤ F k₀ := not_lt.mp (Nat.find_spec hex)
  have hk₀N : (k₀ : ℝ≥0∞) ≤ N := by
    calc (k₀ : ℝ≥0∞) = ∑ j ∈ Finset.range k₀, (1 : ℝ≥0∞) := by simp
      _ = ∑ j ∈ Finset.range k₀, if F j < r / 2 then (1 : ℝ≥0∞) else 0 :=
          Finset.sum_congr rfl fun j hj ↦ by
            simp [not_not.mp (Nat.find_min hex (Finset.mem_range.1 hj))]
      _ ≤ N := sum_le_tsum _
  set t : ℝ≥0∞ := 2⁻¹ ^ (k₀ + 2)
  have ht0 : t ≠ 0 := by simp [t]
  have htt : t ≠ ∞ := by simp [t]
  have h1 : t * r ≤ f₀ := by
    calc t * r = 2⁻¹ ^ (k₀ + 1) * (r / 2) := by
          rw [ENNReal.div_eq_inv_mul, ← mul_assoc, ← pow_succ]
      _ ≤ 2⁻¹ ^ (k₀ + 1) * F k₀ := by gcongr
      _ ≤ f₀ := hf₀ k₀
  have h2 : t * (r / q) ≤ f₀ / q := by
    rw [← mul_div_assoc]
    exact ENNReal.div_le_div_right h1 q
  have h3 : (f₀ / q)⁻¹ ≤ 2 ^ (k₀ + 2) * (r / q)⁻¹ := by
    calc (f₀ / q)⁻¹ ≤ (t * (r / q))⁻¹ := ENNReal.inv_le_inv.2 h2
      _ = t⁻¹ * (r / q)⁻¹ := ENNReal.mul_inv (Or.inl ht0) (Or.inl htt)
      _ = 2 ^ (k₀ + 2) * (r / q)⁻¹ := by rw [ENNReal.inv_pow, inv_inv]
  have hlog2 : (ENNReal.log 2).toENNReal = ENNReal.ofReal (Real.log 2) := by
    rw [← ENNReal.ofReal_ofNat 2, ENNReal.log_ofReal_of_pos two_pos]
    simp
  calc (-ENNReal.log (f₀ / q)).toENNReal = (ENNReal.log (f₀ / q)⁻¹).toENNReal := by
        rw [ENNReal.log_inv]
    _ ≤ (ENNReal.log (2 ^ (k₀ + 2) * (r / q)⁻¹)).toENNReal :=
        EReal.toENNReal_le_toENNReal (ENNReal.log_monotone h3)
    _ = (ENNReal.log (2 ^ (k₀ + 2)) + ENNReal.log (r / q)⁻¹).toENNReal := by
        rw [ENNReal.log_mul_add]
    _ ≤ (ENNReal.log (2 ^ (k₀ + 2))).toENNReal + (ENNReal.log (r / q)⁻¹).toENNReal :=
        EReal.toENNReal_add_le
    _ = ENNReal.ofReal (Real.log 2) * ((k₀ : ℝ≥0∞) + 2) + (-ENNReal.log (r / q)).toENNReal := by
        rw [ENNReal.toENNReal_log_pow, hlog2, ENNReal.log_inv, mul_comm]
        norm_num
    _ ≤ _ := by
        rw [add_comm]
        gcongr

/-- Step A of the proof of Theorem 2 of Note 27, for functions: if `∫ ln (r / q) dP > -∞`,
`∑ₖ P (F k < r / 2) < ∞` and `f₀ ≥ 2⁻¹ ^ (k + 1) F k` almost everywhere for all `k`, then
`∫ ln (f₀ / q) dP > -∞`. -/
private lemma eintegral_log_div_ne_bot_of_forall_le [IsFiniteMeasure P] {q r f₀ : Ω → ℝ≥0∞}
    {F : ℕ → Ω → ℝ≥0∞} (hq : Measurable q) (hr : Measurable r) (hF : ∀ k, Measurable (F k))
    (hr_bot : ∫ᵉ ω, ENNReal.log (r ω / q ω) ∂P ≠ ⊥)
    (hsum : ∑' k, P {ω | F k ω < r ω / 2} ≠ ∞)
    (hf₀ : ∀ᵐ ω ∂P, ∀ k, 2⁻¹ ^ (k + 1) * F k ω ≤ f₀ ω) :
    ∫ᵉ ω, ENNReal.log (f₀ ω / q ω) ∂P ≠ ⊥ := by
  rw [eintegral_ne_bot_iff_lintegral_ne_top] at hr_bot ⊢
  have hmeas : ∀ k, MeasurableSet {ω | F k ω < r ω / 2} := fun k ↦
    measurableSet_lt (hF k) (hr.div_const 2)
  have hind : ∀ k, ∫⁻ ω, (if F k ω < r ω / 2 then (1 : ℝ≥0∞) else 0) ∂P
      = P {ω | F k ω < r ω / 2} := fun k ↦ by
    rw [← lintegral_indicator_one (hmeas k)]
    congr 1
    ext ω
    simp [Set.indicator_apply]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae (hf₀.mono fun ω hω ↦
    toENNReal_neg_log_div_le (q := q ω) (r := r ω) hω))
  have hm : Measurable fun ω ↦ (-ENNReal.log (r ω / q ω)).toENNReal :=
    EReal.continuous_toENNReal.measurable.comp ((hr.div hq).ennreal_log.neg)
  rw [lintegral_add_left' hm.aemeasurable, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_right' _ aemeasurable_const,
    lintegral_tsum fun k ↦
      (Measurable.ite (hmeas k) measurable_const measurable_const).aemeasurable]
  simp only [hind, lintegral_const]
  refine ENNReal.add_ne_top.2 ⟨hr_bot, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_⟩
  exact ENNReal.add_ne_top.2 ⟨hsum, ENNReal.mul_ne_top ENNReal.ofNat_ne_top (measure_ne_top _ _)⟩

/-! #### Step B: Fatou's lemma and the concavity of the logarithm -/

/-- The concavity step of Step B of the proof of Theorem 2 of Note 27: if
`∫ ln (f₀ / q) dP = g₀` is finite and `a ≤ ∫ ln (f / q) dP`, then for `s ∈ [0, 1]`,
`s g₀ + (1 - s) a ≤ ∫ ln ((s f₀ + (1 - s) f) / q) dP`. -/
private lemma le_eintegral_log_mix {q f₀ f : Ω → ℝ≥0∞} (hq : Measurable q)
    (hf₀ : Measurable f₀) (hf : Measurable f) {s : ℝ≥0} (hs1 : s ≤ 1) {g₀ a : ℝ}
    (h₀ : ∫ᵉ ω, ENNReal.log (f₀ ω / q ω) ∂P = g₀)
    (ha : (a : EReal) ≤ ∫ᵉ ω, ENNReal.log (f ω / q ω) ∂P) :
    ((s * g₀ + (1 - s) * a : ℝ) : EReal)
      ≤ ∫ᵉ ω, ENNReal.log ((s * f₀ ω + ((1 - s : ℝ≥0) : ℝ≥0∞) * f ω) / q ω) ∂P := by
  set L₀ : Ω → EReal := fun ω ↦ ENNReal.log (f₀ ω / q ω)
  have hL₀m : Measurable L₀ := (hf₀.div hq).ennreal_log
  have hL₀_int : EIntegrable L₀ P :=
    eintegrable_of_eintegral_ne_bot (by rw [h₀]; exact EReal.coe_ne_bot _)
  have hL_bot : ∫ᵉ ω, ENNReal.log (f ω / q ω) ∂P ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) ha
  have hLm : Measurable fun ω ↦ ENNReal.log (f ω / q ω) := (hf.div hq).ennreal_log
  have hsL₀ : ∫ᵉ ω, ((s : ℝ) : EReal) * L₀ ω ∂P = ((s * g₀ : ℝ) : EReal) := by
    rw [eintegral_real_const_mul _ hL₀_int, h₀, EReal.coe_mul]
  have h1s : (((1 - s : ℝ≥0) : ℝ)) = 1 - (s : ℝ) := NNReal.coe_sub hs1
  calc ((s * g₀ + (1 - s) * a : ℝ) : EReal)
      = (((1 - s : ℝ≥0) : ℝ) : EReal) * (a : EReal) + ((s * g₀ : ℝ) : EReal) := by
        rw [h1s, ← EReal.coe_mul, ← EReal.coe_add, add_comm]
    _ ≤ (((1 - s : ℝ≥0) : ℝ) : EReal) * ∫ᵉ ω, ENNReal.log (f ω / q ω) ∂P
          + ∫ᵉ ω, ((s : ℝ) : EReal) * L₀ ω ∂P := by
        rw [hsL₀]
        gcongr
    _ = ∫ᵉ ω, ((((1 - s : ℝ≥0) : ℝ) : EReal) * ENNReal.log (f ω / q ω)
          + ((s : ℝ) : EReal) * L₀ ω) ∂P := by
        rw [eintegral_add' (hLm.const_mul _).aemeasurable
          (hL₀m.const_mul _).aemeasurable (by rw [hsL₀]; exact EReal.coe_ne_top _)
          (by rw [hsL₀]; exact EReal.coe_ne_bot _),
          eintegral_real_const_mul _ (eintegrable_of_eintegral_ne_bot hL_bot)]
    _ ≤ _ := eintegral_mono fun ω ↦
        (ENNReal.mul_log_add_mul_log_le_log (tsub_add_cancel_of_le hs1) _ _).trans_eq
          (by rw [← mul_div_assoc, ← mul_div_assoc, ← ENNReal.add_div, add_comm])

/-- Step B of the proof of Theorem 2 of Note 27, for functions (Fatou's lemma and the concavity
of the logarithm): let `∫ ln (f₀ / q) dP = g₀` be finite, `F n → f` almost everywhere,
`a ≤ ∫ ln (f / q) dP` and `s ∈ (0, 1)`. Then for every `c < s g₀ + (1 - s) a`, eventually
`c < ∫ ln ((s f₀ + (1 - s) F n) / q) dP`. -/
private lemma eventually_lt_eintegral_log_mix [IsFiniteMeasure P] {q f₀ f : Ω → ℝ≥0∞}
    {F : ℕ → Ω → ℝ≥0∞} (hq : Measurable q) (hf₀ : Measurable f₀) (hf : Measurable f)
    (hF : ∀ n, Measurable (F n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ F n ω) atTop (𝓝 (f ω))) {s : ℝ≥0} (hs0 : 0 < s)
    (hs1 : s < 1) {g₀ a c : ℝ} (h₀ : ∫ᵉ ω, ENNReal.log (f₀ ω / q ω) ∂P = g₀)
    (ha : (a : EReal) ≤ ∫ᵉ ω, ENNReal.log (f ω / q ω) ∂P)
    (hc : c < s * g₀ + (1 - s) * a) :
    ∀ᶠ n in atTop, (c : EReal) < ∫ᵉ ω, ENNReal.log
      ((s * f₀ ω + ((1 - s : ℝ≥0) : ℝ≥0∞) * F n ω) / q ω) ∂P := by
  -- With `A = s f₀`, write `ln ((A + (1 - s) G) / q)` as the nonnegative
  -- `ln (1 + (1 - s) G / A)` plus `ln (A / q)`, whose integral is a finite constant `k`. Fatou's
  -- lemma applies to the nonnegative part along `G = F n`, and the concavity of the logarithm
  -- bounds the limit `G = f` from below.
  set b : ℝ≥0∞ := ((1 - s : ℝ≥0) : ℝ≥0∞)
  have hb : b ≠ ∞ := ENNReal.coe_ne_top
  set A : Ω → ℝ≥0∞ := fun ω ↦ (s : ℝ≥0∞) * f₀ ω
  set L₀ : Ω → EReal := fun ω ↦ ENNReal.log (f₀ ω / q ω)
  have hL₀m : Measurable L₀ := (hf₀.div hq).ennreal_log
  have hL₀_bot : ∫ᵉ ω, L₀ ω ∂P ≠ ⊥ := by rw [h₀]; exact EReal.coe_ne_bot _
  have hL₀_top : ∫ᵉ ω, L₀ ω ∂P ≠ ⊤ := by rw [h₀]; exact EReal.coe_ne_top _
  have hL₀_int : EIntegrable L₀ P := eintegrable_of_eintegral_ne_bot hL₀_bot
  -- `A ∈ (0, ∞)` almost everywhere
  have hgood : ∀ᵐ ω ∂P, A ω ≠ 0 ∧ A ω ≠ ∞ := by
    filter_upwards [ae_ne_bot_of_eintegral_ne_bot hL₀m.aemeasurable hL₀_bot,
      ae_ne_top_of_eintegral_ne_top hL₀m.aemeasurable hL₀_int hL₀_top] with ω h1 h2
    simp only [L₀, ne_eq, ENNReal.log_eq_bot_iff, ENNReal.log_eq_top_iff] at h1 h2
    have hf0 : f₀ ω ≠ 0 := fun h ↦ h1 (by simp [h])
    have hft : f₀ ω ≠ ∞ := by
      intro h
      by_cases hqt : q ω = ∞
      · exact h1 (by simp [h, hqt])
      · exact h2 (by simp [h, ENNReal.top_div_of_ne_top hqt])
    exact ⟨mul_ne_zero (by simpa using hs0.ne') hf0, ENNReal.mul_ne_top ENNReal.coe_ne_top hft⟩
  -- the integral of `ln (A / q)` is finite
  set U : Ω → EReal := fun ω ↦ ENNReal.log (A ω / q ω)
  have hU : ∀ ω, U ω = ((Real.log s : ℝ) : EReal) + L₀ ω := by
    intro ω
    simp only [U, A, L₀]
    rw [mul_div_assoc, ENNReal.log_mul_add, ← ENNReal.log_ofReal_of_pos (NNReal.coe_pos.2 hs0),
      ENNReal.ofReal_coe_nnreal]
  set k : ℝ := Real.log s * P.real univ + g₀ with hk
  have hUk : ∫ᵉ ω, U ω ∂P = k := by
    simp_rw [hU]
    rw [eintegral_add' measurable_const.aemeasurable hL₀m.aemeasurable hL₀_top hL₀_bot,
      eintegral_const, h₀, ← EReal.coe_ennreal_toReal (measure_ne_top P univ), ← EReal.coe_mul,
      ← EReal.coe_add, hk, measureReal_def]
  have hUm : Measurable U := ((measurable_const.mul hf₀).div hq).ennreal_log
  -- the decomposition `ln ((A + b G) / q) = ln (1 + b G / A) + ln (A / q)`
  set H : (Ω → ℝ≥0∞) → Ω → ℝ≥0∞ :=
    fun G ω ↦ (ENNReal.log (1 + b * G ω / A ω)).toENNReal
  have hHm : ∀ G, Measurable G → Measurable (H G) := fun G hG ↦
    EReal.continuous_toENNReal.measurable.comp
      (measurable_const.add
        ((measurable_const.mul hG).div (measurable_const.mul hf₀))).ennreal_log
  have hdec : ∀ G, Measurable G →
      ∫ᵉ ω, ENNReal.log ((A ω + b * G ω) / q ω) ∂P = ∫⁻ ω, H G ω ∂P + (k : EReal) := by
    intro G hG
    rw [← hUk, ← eintegral_coe_ennreal,
      ← eintegral_add' (hHm G hG).coe_ereal_ennreal.aemeasurable hUm.aemeasurable
        (by rw [hUk]; exact EReal.coe_ne_top _) (by rw [hUk]; exact EReal.coe_ne_bot _)]
    refine eintegral_congr_ae ?_
    filter_upwards [hgood] with ω hω
    have hsplit : ENNReal.log ((A ω + b * G ω) / q ω)
        = ENNReal.log (1 + b * G ω / A ω) + ENNReal.log (A ω / q ω) := by
      rw [← ENNReal.log_mul_add, ← mul_div_assoc, add_mul, one_mul,
        ENNReal.div_mul_cancel hω.1 hω.2, add_comm]
    rw [hsplit, EReal.coe_toENNReal]
    exact ENNReal.zero_le_log_iff.2 le_self_add
  have hconc : ((s * g₀ + (1 - s) * a : ℝ) : EReal)
      ≤ ∫ᵉ ω, ENNReal.log ((A ω + b * f ω) / q ω) ∂P :=
    le_eintegral_log_mix hq hf₀ hf hs1.le h₀ ha
  -- Fatou's lemma
  have hfatou : ∫⁻ ω, H f ω ∂P ≤ liminf (fun n ↦ ∫⁻ ω, H (F n) ω ∂P) atTop := by
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (lintegral_liminf_le' fun n ↦
      (hHm _ (hF n)).aemeasurable)
    filter_upwards [hgood, hlim] with ω hω hlimω
    refine (Tendsto.liminf_eq ?_).symm
    have hc : Continuous fun x : ℝ≥0∞ ↦ (ENNReal.log (1 + b * x / A ω)).toENNReal :=
      EReal.continuous_toENNReal.comp (ENNReal.continuous_log.comp (continuous_const.add
        ((ENNReal.continuous_div_const (A ω) hω.1).comp (ENNReal.continuous_const_mul hb))))
    exact (hc.tendsto (f ω)).comp hlimω
  -- conclusion
  have hlt : (c : EReal) < ∫⁻ ω, H f ω ∂P + (k : EReal) := by
    rw [← hdec f hf]
    exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hc) hconc
  have hdec' : ∀ n, ∫ᵉ ω, ENNReal.log ((s * f₀ ω + b * F n ω) / q ω) ∂P
      = ∫⁻ ω, H (F n) ω ∂P + (k : EReal) := fun n ↦ hdec (F n) (hF n)
  simp_rw [hdec']
  rcases lt_or_ge c k with hck | hck
  · refine Eventually.of_forall fun n ↦ ?_
    calc (c : EReal) < k := EReal.coe_lt_coe_iff.2 hck
      _ ≤ _ := le_add_of_nonneg_left (EReal.coe_ennreal_nonneg _)
  · set t₀ := ENNReal.ofReal (c - k)
    have ht₀ : (t₀ : EReal) + k = c := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left (by linarith), ← EReal.coe_add, sub_add_cancel]
    have ht₀' : t₀ < ∫⁻ ω, H f ω ∂P := by
      rw [← EReal.coe_ennreal_lt_coe_ennreal_iff]
      by_contra! h
      exact absurd (add_le_add h (le_refl (k : EReal))) (not_le.2 (ht₀ ▸ hlt))
    filter_upwards [eventually_lt_of_lt_liminf (lt_of_lt_of_le ht₀' hfatou)] with n hn
    rw [← ht₀]
    exact EReal.add_lt_add_right_coe (EReal.coe_ennreal_lt_coe_ennreal_iff.2 hn) k

/-! #### Assembly -/

/-- The assembly of Step B of the proof of Theorem 2 of Note 27: let `Q₀` have gain `> -∞` and
let the densities of `Qs n` converge `P`-almost everywhere to that of `R`, with
`limsup Qs n (Ω) ≤ R(Ω)`. If `S` bounds the gains of `Q₀` and of all the mixtures
`s Q₀ + (1 - s) Qs n` with `s ∈ (0, 1)`, then `D(P‖Q ⇝ R) ≤ S`. -/
private lemma descriptionGain_le_of_forall_mix_le [SigmaFinite μ] [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (hPμ : P ≪ μ) {Q₀ : Measure Ω} (hQ₀ : ⊥ < descriptionGain μ P Q Q₀)
    {Qs : ℕ → Measure Ω}
    (h_ae : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (Qs n).rnDeriv μ ω) atTop (𝓝 (R.rnDeriv μ ω)))
    (h_mass : limsup (fun n ↦ Qs n univ) atTop ≤ R univ) {S : EReal}
    (hS₀ : descriptionGain μ P Q Q₀ ≤ S)
    (hS : ∀ s : ℝ≥0, 0 < s → s < 1 → ∀ n,
      descriptionGain μ P Q ((s : ℝ≥0∞) • Q₀ + ((1 - s : ℝ≥0) : ℝ≥0∞) • Qs n) ≤ S) :
    descriptionGain μ P Q R ≤ S := by
  -- By contradiction, take `a` real with `S < a < D(P‖Q ⇝ R)`. For a weight `s` small enough
  -- that the term `s (D(P‖Q ⇝ Q₀) - a)` is negligible, Step B and the convergence of the masses
  -- give a mixture `s Q₀ + (1 - s) Qs n` of gain larger than `S`.
  by_contra! hlt
  have hQ₀_ne : descriptionGain μ P Q Q₀ ≠ ⊥ := hQ₀.ne'
  have hQ₀_fin : Q₀ univ ≠ ∞ := measure_univ_ne_top_of_descriptionGain_ne_bot hQ₀_ne
  have : IsFiniteMeasure Q₀ := ⟨hQ₀_fin.lt_top⟩
  have hR_ne : descriptionGain μ P Q R ≠ ⊥ := ne_bot_of_gt hlt
  have hR_fin : R univ ≠ ∞ := measure_univ_ne_top_of_descriptionGain_ne_bot hR_ne
  have hS_bot : S ≠ ⊥ := ne_bot_of_le_ne_bot hQ₀_ne hS₀
  obtain ⟨S', rfl⟩ : ∃ S' : ℝ, S = S' := ⟨S.toReal, (EReal.coe_toReal hlt.ne_top hS_bot).symm⟩
  set q := Q.rnDeriv μ
  set q₀ := Q₀.rnDeriv μ
  set r := R.rnDeriv μ
  set m₀ : ℝ := Q₀.real univ - Q.real univ
  set mR : ℝ := R.real univ - Q.real univ
  have hG₀ := descriptionGain_eq_sub (μ := μ) (P := P) (Q := Q) hQ₀_fin
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : ℝ, ∫ᵉ ω, ENNReal.log (q₀ ω / q ω) ∂P = g₀ := by
    have h1 := eintegral_ne_bot_of_descriptionGain_ne_bot hQ₀_ne
    have h2 : ∫ᵉ ω, ENNReal.log (q₀ ω / q ω) ∂P ≠ ⊤ := by
      intro h
      rw [hG₀, h, EReal.top_sub_coe] at hS₀
      exact EReal.coe_ne_top S' (top_le_iff.1 hS₀)
    exact ⟨_, (EReal.coe_toReal h2 h1).symm⟩
  rw [hG₀, hg₀, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hS₀
  obtain ⟨a, haS, haR⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  rw [EReal.coe_lt_coe_iff] at haS
  have ha' : ((a + mR : ℝ) : EReal) ≤ ∫ᵉ ω, ENNReal.log (r ω / q ω) ∂P := by
    by_contra! h
    have : descriptionGain μ P Q R ≤ a := by
      rw [descriptionGain_eq_sub hR_fin]
      calc _ ≤ ((a + mR : ℝ) : EReal) - (mR : EReal) := EReal.sub_le_sub h.le le_rfl
        _ = a := by rw [← EReal.coe_sub, add_sub_cancel_right]
    exact absurd haR (not_lt.2 this)
  -- the choice of the weight `s`
  set η : ℝ := (a - S') / 4
  have hη : 0 < η := by simp only [η]; linarith
  set D : ℝ := |a - (g₀ - m₀)| + 1
  have hD : 0 < D := by positivity
  set s : ℝ≥0 := ⟨min (1 / 2) (η / D), by positivity⟩
  have hs_le : (s : ℝ) ≤ η / D := min_le_right _ _
  have hs0 : 0 < s := by
    rw [← NNReal.coe_pos]
    exact lt_min (by norm_num) (by positivity)
  have hs1 : s < 1 := by
    rw [← NNReal.coe_lt_coe]
    exact (min_le_left _ _).trans_lt (by norm_num)
  have hsη : (s : ℝ) * |a - (g₀ - m₀)| ≤ η := by
    calc (s : ℝ) * |a - (g₀ - m₀)| ≤ η / D * D := by
          gcongr
          simp [D]
      _ = η := div_mul_cancel₀ η hD.ne'
  -- eventually, the masses are almost below `R(Ω)` and the integrals are large
  have hmass_ev : ∀ᶠ n in atTop, Qs n univ < R univ + ENNReal.ofReal η :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt h_mass
      (ENNReal.lt_add_right hR_fin (by simp [hη])))
  have hB := eventually_lt_eintegral_log_mix (P := P) (q := q) (f₀ := q₀) (f := r)
    (F := fun n ↦ (Qs n).rnDeriv μ) (Measure.measurable_rnDeriv _ _)
    (Measure.measurable_rnDeriv _ _) (Measure.measurable_rnDeriv _ _)
    (fun _ ↦ Measure.measurable_rnDeriv _ _) h_ae hs0 hs1 hg₀ ha'
    (c := s * g₀ + (1 - s) * (a + mR) - η) (by linarith)
  obtain ⟨n, hn1, hn2⟩ := (hmass_ev.and hB).exists
  have hn_fin : Qs n univ ≠ ∞ := ne_top_of_lt hn1
  have : IsFiniteMeasure (Qs n) := ⟨hn_fin.lt_top⟩
  have hn1' : (Qs n).real univ < R.real univ + η := by
    have h := (ENNReal.toReal_lt_toReal hn_fin
      (ENNReal.add_ne_top.2 ⟨hR_fin, ENNReal.ofReal_ne_top⟩)).2 hn1
    rwa [ENNReal.toReal_add hR_fin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hη.le] at h
  -- the mixture `Rn`
  set Rn := (s : ℝ≥0∞) • Q₀ + ((1 - s : ℝ≥0) : ℝ≥0∞) • Qs n
  have hRn_univ : Rn univ = s * Q₀ univ + ((1 - s : ℝ≥0) : ℝ≥0∞) * Qs n univ := by
    simp [Rn]
  have hRn_fin : Rn univ ≠ ∞ := by
    rw [hRn_univ]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hQ₀_fin,
      ENNReal.mul_ne_top ENNReal.coe_ne_top hn_fin⟩
  have hsmul : Rn = s • Q₀ + (1 - s) • Qs n := by rw [ENNReal.smul_def, ENNReal.smul_def]
  have hRn_real : Rn.real univ = s * Q₀.real univ + (1 - s) * (Qs n).real univ := by
    rw [hsmul, measureReal_def, add_apply, ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp [measureReal_def, ENNReal.toReal_sub_of_le (by exact_mod_cast hs1.le : (s : ℝ≥0∞) ≤ 1)]
  have hRn_dens : ∫ᵉ ω, ENNReal.log (Rn.rnDeriv μ ω / q ω) ∂P
      = ∫ᵉ ω, ENNReal.log ((s * q₀ ω + ((1 - s : ℝ≥0) : ℝ≥0∞) * (Qs n).rnDeriv μ ω) / q ω) ∂P := by
    refine eintegral_congr_ae ?_
    filter_upwards [hPμ.ae_le
      (Measure.rnDeriv_smul_add_smul (μ := Q₀) (ν := Qs n) (ξ := μ) s (1 - s))] with ω h
    rw [hsmul, h]
    simp only [Pi.add_apply, Pi.smul_apply, ENNReal.smul_def, smul_eq_mul, q₀]
  have hgain : (S' : EReal) < descriptionGain μ P Q Rn := by
    rw [descriptionGain_eq_sub hRn_fin, hRn_dens]
    calc (S' : EReal) < ((s * g₀ + (1 - s) * (a + mR) - η : ℝ) : EReal)
          - ((Rn.real univ - Q.real univ : ℝ) : EReal) := by
          rw [← EReal.coe_sub, EReal.coe_lt_coe_iff, hRn_real]
          have hs' : (0 : ℝ) ≤ s := s.2
          have h1 : (s : ℝ) * (a - (g₀ - m₀)) ≤ (s : ℝ) * |a - (g₀ - m₀)| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hs'
          have h2 : (1 - (s : ℝ)) * ((Qs n).real univ - R.real univ) ≤ (1 - (s : ℝ)) * η :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith [(by exact_mod_cast hs1 :
              (s : ℝ) < 1)])
          have h3 : (1 - (s : ℝ)) * η ≤ η := by nlinarith
          simp only [mR, m₀, η] at h1 h2 h3 hsη ⊢
          nlinarith
      _ ≤ _ := EReal.sub_le_sub hn2.le le_rfl
  exact absurd (hS s hs0 hs1 n) (not_le.2 hgain)

/-- Step A of the proof of Theorem 2 (2) of Note 27: if `R` has gain `> -∞` and is the limit of
elements `Qs n` of a σ-convex set `𝒞` (densities converging `P`-almost everywhere,
`limsup Qs n (Ω) ≤ R(Ω)`), then some element of `𝒞`, a countable mixture
`∑ₖ 2⁻¹ ^ (k + 1) Qs (φ k)`, has gain `> -∞`. -/
private lemma exists_mem_bot_lt_descriptionGain [SigmaFinite μ] [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (hPμ : P ≪ μ) {𝒞 : Set (Measure Ω)} (h𝒞 : IsSigmaConvex 𝒞)
    {Qs : ℕ → Measure Ω} (hQs : ∀ n, Qs n ∈ 𝒞)
    (h_ae : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (Qs n).rnDeriv μ ω) atTop (𝓝 (R.rnDeriv μ ω)))
    (h_mass : limsup (fun n ↦ Qs n univ) atTop ≤ R univ) (hR : ⊥ < descriptionGain μ P Q R) :
    ∃ Q₀ ∈ 𝒞, ⊥ < descriptionGain μ P Q Q₀ := by
  have hR_ne := hR.ne'
  have hR_fin : R univ ≠ ∞ := measure_univ_ne_top_of_descriptionGain_ne_bot hR_ne
  have : IsFiniteMeasure R := ⟨hR_fin.lt_top⟩
  set q := Q.rnDeriv μ
  set r := R.rnDeriv μ with hr_def
  have hr_bot := eintegral_ne_bot_of_descriptionGain_ne_bot hR_ne
  have hr_pos : ∀ᵐ ω ∂P, r ω ≠ 0 := by
    filter_upwards [ae_ne_bot_of_eintegral_ne_bot ((Measure.measurable_rnDeriv _ _).div
      (Measure.measurable_rnDeriv _ _)).ennreal_log.aemeasurable hr_bot] with ω hω h0
    simp only [ne_eq, ENNReal.log_eq_bot_iff] at hω
    rw [hr_def] at h0
    exact hω (by rw [Pi.div_apply, h0, ENNReal.zero_div])
  have hr_top : ∀ᵐ ω ∂P, r ω ≠ ∞ := hPμ.ae_le (Measure.rnDeriv_ne_top R μ)
  have hmeas : ∀ n, MeasurableSet {ω | (Qs n).rnDeriv μ ω < r ω / 2} := fun n ↦
    measurableSet_lt (Measure.measurable_rnDeriv _ _) ((Measure.measurable_rnDeriv _ _).div_const 2)
  -- `P (q_n < r / 2) → 0`
  have hP_tend : Tendsto (fun n ↦ P {ω | (Qs n).rnDeriv μ ω < r ω / 2}) atTop (𝓝 0) := by
    have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (μ := P) atTop
      MeasurableSet.empty hmeas ?_
    · simpa using h
    filter_upwards [h_ae, hr_pos, hr_top] with ω hω h0 ht
    filter_upwards [hω.eventually (lt_mem_nhds (ENNReal.half_lt_self h0 ht))] with n hn
    simp only [mem_empty_iff_false, iff_false, not_lt]
    exact hn.le
  have hmass_ev : ∀ᶠ n in atTop, Qs n univ < R univ + 1 :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt h_mass (ENNReal.lt_add_right hR_fin one_ne_zero))
  have hφ : ∀ k : ℕ, ∃ n, P {ω | (Qs n).rnDeriv μ ω < r ω / 2} < 2⁻¹ ^ k ∧
      Qs n univ < R univ + 1 := fun k ↦
    ((hP_tend.eventually (gt_mem_nhds (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)
      k))).and hmass_ev).exists
  choose φ hφ1 hφ2 using hφ
  have hfin : ∀ k, IsFiniteMeasure (Qs (φ k)) := fun k ↦
    ⟨(hφ2 k).trans (ENNReal.add_lt_top.2 ⟨hR_fin.lt_top, ENNReal.one_lt_top⟩)⟩
  -- the countable mixture
  set w : ℕ → ℝ≥0∞ := fun k ↦ 2⁻¹ ^ (k + 1)
  have hw : ∑' k, w k = 1 := ENNReal.tsum_geometric_two_add_one
  set Q₀ := Measure.sum fun k ↦ w k • Qs (φ k)
  have hQ₀𝒞 : Q₀ ∈ 𝒞 := h𝒞.sum_smul_mem hw fun k ↦ hQs _
  have hQ₀_univ : Q₀ univ ≤ R univ + 1 := by
    rw [Measure.sum_apply _ MeasurableSet.univ]
    calc ∑' k, (w k • Qs (φ k)) univ ≤ ∑' k, w k * (R univ + 1) :=
          tsum_le_tsum fun k ↦ by
            rw [smul_apply, smul_eq_mul]
            gcongr
            exact (hφ2 k).le
      _ = R univ + 1 := by rw [ENNReal.tsum_mul_right, hw, one_mul]
  have hQ₀_fin : Q₀ univ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hR_fin, ENNReal.one_ne_top⟩) hQ₀_univ
  have : IsFiniteMeasure Q₀ := ⟨hQ₀_fin.lt_top⟩
  have hdens : ∀ᵐ ω ∂P, ∀ k, 2⁻¹ ^ (k + 1) * (Qs (φ k)).rnDeriv μ ω ≤ Q₀.rnDeriv μ ω := by
    rw [ae_all_iff]
    intro k
    have hle : w k • Qs (φ k) ≤ Q₀ := Measure.le_sum (fun k ↦ w k • Qs (φ k)) k
    filter_upwards [hPμ.ae_le (Measure.rnDeriv_le_rnDeriv_of_le hle),
      hPμ.ae_le (Measure.rnDeriv_smul_left_of_ne_top (Qs (φ k)) μ
        (by simp [w] : w k ≠ ∞))] with ω h1 h2
    rw [h2] at h1
    simpa [w] using h1
  have hsum : ∑' k, P {ω | (Qs (φ k)).rnDeriv μ ω < r ω / 2} ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (tsum_le_tsum fun k ↦ (hφ1 k).le)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hA := eintegral_log_div_ne_bot_of_forall_le (q := q) (r := r) (f₀ := Q₀.rnDeriv μ)
    (F := fun k ↦ (Qs (φ k)).rnDeriv μ) (Measure.measurable_rnDeriv _ _)
    (Measure.measurable_rnDeriv _ _) (fun _ ↦ Measure.measurable_rnDeriv _ _) hr_bot hsum hdens
  refine ⟨Q₀, hQ₀𝒞, bot_lt_iff_ne_bot.2 ?_⟩
  rw [descriptionGain_eq_sub hQ₀_fin]
  intro h
  rcases EReal.sub_eq_bot.1 h with h | h
  · exact hA h
  · exact EReal.coe_ne_top _ h

/-- **Theorem 2 (3) of Note 27**, in the form of Remark 1 of Part 2: let `𝒞` be convex with
description gain `D(P‖Q ⇝ 𝒞) > -∞`. If the densities of `Qs n ∈ 𝒞` converge `P`-almost
everywhere to the density of `R` and `limsup Qs n (Ω) ≤ R(Ω)`, then
`D(P‖Q ⇝ R) ≤ D(P‖Q ⇝ 𝒞)`.

[EVR26, Note 27, Theorem 2 (3)] -/
theorem descriptionGain_le_iSup_of_convex [SigmaFinite μ] [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (hPμ : P ≪ μ) {𝒞 : Set (Measure Ω)} (h𝒞 : Convex ℝ≥0∞ 𝒞)
    (h_bot : ⊥ < ⨆ R' ∈ 𝒞, descriptionGain μ P Q R') {Qs : ℕ → Measure Ω}
    (hQs : ∀ n, Qs n ∈ 𝒞)
    (h_ae : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (Qs n).rnDeriv μ ω) atTop (𝓝 (R.rnDeriv μ ω)))
    (h_mass : limsup (fun n ↦ Qs n univ) atTop ≤ R univ) :
    descriptionGain μ P Q R ≤ ⨆ R' ∈ 𝒞, descriptionGain μ P Q R' := by
  obtain ⟨Q₀, hQ₀𝒞, hQ₀⟩ : ∃ Q₀ ∈ 𝒞, ⊥ < descriptionGain μ P Q Q₀ := by
    simpa only [lt_iSup_iff, exists_prop] using h_bot
  refine descriptionGain_le_of_forall_mix_le hPμ hQ₀ h_ae h_mass
    (le_iSup₂ (f := fun R' _ ↦ descriptionGain μ P Q R') Q₀ hQ₀𝒞) fun s _ hs1 n ↦ ?_
  refine le_iSup₂ (f := fun R' _ ↦ descriptionGain μ P Q R') _
    (h𝒞 hQ₀𝒞 (hQs n) zero_le zero_le ?_)
  rw [← ENNReal.coe_add, add_tsub_cancel_of_le hs1.le, ENNReal.coe_one]

/-- **Theorem 2 (2) of Note 27**, in the form of Remark 1 of Part 2: let `𝒞` be σ-convex. If
the densities of `Qs n ∈ 𝒞` converge `P`-almost everywhere to the density of `R` and
`limsup Qs n (Ω) ≤ R(Ω)`, then `D(P‖Q ⇝ R) ≤ D(P‖Q ⇝ 𝒞)`.

[EVR26, Note 27, Theorem 2 (2)] -/
theorem descriptionGain_le_iSup_of_isSigmaConvex [SigmaFinite μ] [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (hPμ : P ≪ μ) {𝒞 : Set (Measure Ω)} (h𝒞 : IsSigmaConvex 𝒞)
    {Qs : ℕ → Measure Ω} (hQs : ∀ n, Qs n ∈ 𝒞)
    (h_ae : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (Qs n).rnDeriv μ ω) atTop (𝓝 (R.rnDeriv μ ω)))
    (h_mass : limsup (fun n ↦ Qs n univ) atTop ≤ R univ) :
    descriptionGain μ P Q R ≤ ⨆ R' ∈ 𝒞, descriptionGain μ P Q R' := by
  by_cases hR : descriptionGain μ P Q R = ⊥
  · rw [hR]
    exact bot_le
  obtain ⟨Q₀, hQ₀𝒞, hQ₀⟩ :=
    exists_mem_bot_lt_descriptionGain hPμ h𝒞 hQs h_ae h_mass (bot_lt_iff_ne_bot.2 hR)
  exact descriptionGain_le_iSup_of_convex hPμ h𝒞.convex
    (hQ₀.trans_le (le_iSup₂ (f := fun R' _ ↦ descriptionGain μ P Q R') Q₀ hQ₀𝒞)) hQs h_ae h_mass

/-! #### Limits in total variation

A limit `R` in total variation of measures `Qs n` is their limit in the sense of
`descriptionGain_le_iSup_of_isSigmaConvex` along a subsequence: the densities converge almost
everywhere along a subsequence (`MeasureTheory.exists_seq_tendsto_ae_rnDeriv_of_tendsto_etvDist`),
and `limsup Qs n (Ω) ≤ R(Ω)` (`MeasureTheory.limsup_measure_le_of_tendsto_etvDist`). -/

/-- **Theorem 2 (3) of Note 27**: for a convex set `𝒞` with description gain
`D(P‖Q ⇝ 𝒞) > -∞`, every limit `R` in total variation of members of `𝒞` has
`D(P‖Q ⇝ R) ≤ D(P‖Q ⇝ 𝒞)`.

[EVR26, Note 27, Theorem 2 (3)] -/
theorem descriptionGain_le_iSup_of_convex_of_tendsto_etvDist [SigmaFinite μ]
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (hPμ : P ≪ μ) {𝒞 : Set (Measure Ω)}
    (h𝒞 : Convex ℝ≥0∞ 𝒞) (h_bot : ⊥ < ⨆ R' ∈ 𝒞, descriptionGain μ P Q R')
    {Qs : ℕ → Measure Ω} (hQs : ∀ n, Qs n ∈ 𝒞)
    (hR : Tendsto (fun n ↦ etvDist (Qs n) R) atTop (𝓝 0)) :
    descriptionGain μ P Q R ≤ ⨆ R' ∈ 𝒞, descriptionGain μ P Q R' := by
  obtain ⟨ns, hns, h_ae⟩ := exists_seq_tendsto_ae_rnDeriv_of_tendsto_etvDist (ξ := μ) hR
  exact descriptionGain_le_iSup_of_convex hPμ h𝒞 h_bot (fun i ↦ hQs (ns i)) (hPμ.ae_le h_ae)
    (limsup_measure_le_of_tendsto_etvDist (hR.comp hns.tendsto_atTop) .univ)

/-- **Theorem 2 (2) of Note 27**: for a σ-convex set `𝒞`, every limit `R` in total variation of
members of `𝒞` has `D(P‖Q ⇝ R) ≤ D(P‖Q ⇝ 𝒞)`.

[EVR26, Note 27, Theorem 2 (2)] -/
theorem descriptionGain_le_iSup_of_isSigmaConvex_of_tendsto_etvDist [SigmaFinite μ]
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (hPμ : P ≪ μ) {𝒞 : Set (Measure Ω)}
    (h𝒞 : IsSigmaConvex 𝒞) {Qs : ℕ → Measure Ω} (hQs : ∀ n, Qs n ∈ 𝒞)
    (hR : Tendsto (fun n ↦ etvDist (Qs n) R) atTop (𝓝 0)) :
    descriptionGain μ P Q R ≤ ⨆ R' ∈ 𝒞, descriptionGain μ P Q R' := by
  obtain ⟨ns, hns, h_ae⟩ := exists_seq_tendsto_ae_rnDeriv_of_tendsto_etvDist (ξ := μ) hR
  exact descriptionGain_le_iSup_of_isSigmaConvex hPμ h𝒞 (fun i ↦ hQs (ns i)) (hPμ.ae_le h_ae)
    (limsup_measure_le_of_tendsto_etvDist (hR.comp hns.tendsto_atTop) .univ)

/-- **Theorem 2 (3) of Note 27**, the equality: for a convex set `𝒞` with description gain
`D(P‖Q ⇝ 𝒞) > -∞`, every set `𝒞'` between `𝒞` and its closure in total variation has the
same description gain as `𝒞`.

[EVR26, Note 27, Theorem 2 (3)] -/
theorem iSup_descriptionGain_eq_of_convex [SigmaFinite μ] [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (hPμ : P ≪ μ) {𝒞 𝒞' : Set (Measure Ω)} (h𝒞 : Convex ℝ≥0∞ 𝒞)
    (h_bot : ⊥ < ⨆ R' ∈ 𝒞, descriptionGain μ P Q R') (h𝒞𝒞' : 𝒞 ⊆ 𝒞')
    (h𝒞' : ∀ R ∈ 𝒞', ∃ Qs : ℕ → Measure Ω, (∀ n, Qs n ∈ 𝒞) ∧
      Tendsto (fun n ↦ etvDist (Qs n) R) atTop (𝓝 0)) :
    ⨆ R' ∈ 𝒞', descriptionGain μ P Q R' = ⨆ R' ∈ 𝒞, descriptionGain μ P Q R' := by
  refine le_antisymm (iSup₂_le fun R' hR' ↦ ?_) (biSup_mono h𝒞𝒞')
  obtain ⟨Qs, hQs, hR⟩ := h𝒞' R' hR'
  exact descriptionGain_le_iSup_of_convex_of_tendsto_etvDist hPμ h𝒞 h_bot hQs hR

/-- **Theorem 2 (2) of Note 27**, the equality: for a σ-convex set `𝒞`, every set `𝒞'` between
`𝒞` and its closure in total variation has the same description gain as `𝒞`.

[EVR26, Note 27, Theorem 2 (2)] -/
theorem iSup_descriptionGain_eq_of_isSigmaConvex [SigmaFinite μ] [IsFiniteMeasure P]
    [IsFiniteMeasure Q] (hPμ : P ≪ μ) {𝒞 𝒞' : Set (Measure Ω)} (h𝒞 : IsSigmaConvex 𝒞)
    (h𝒞𝒞' : 𝒞 ⊆ 𝒞')
    (h𝒞' : ∀ R ∈ 𝒞', ∃ Qs : ℕ → Measure Ω, (∀ n, Qs n ∈ 𝒞) ∧
      Tendsto (fun n ↦ etvDist (Qs n) R) atTop (𝓝 0)) :
    ⨆ R' ∈ 𝒞', descriptionGain μ P Q R' = ⨆ R' ∈ 𝒞, descriptionGain μ P Q R' := by
  refine le_antisymm (iSup₂_le fun R' hR' ↦ ?_) (biSup_mono h𝒞𝒞')
  obtain ⟨Qs, hQs, hR⟩ := h𝒞' R' hR'
  exact descriptionGain_le_iSup_of_isSigmaConvex_of_tendsto_etvDist hPμ h𝒞 hQs hR

end ProbabilityTheory
