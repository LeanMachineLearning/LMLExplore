/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.KLInf
public import LMLExplore.EValues.PVariable
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The bet on a test, and the binary relative entropy as a lower bound on the e-power

Let `φ : Ω → [0, 1]` be a test, possibly randomized, of level `p` for a null `S`
(`ProbabilityTheory.IsTest φ S p`), whose power is at least `q ≥ p` under an alternative `Q`:
`∫⁻ φ ∂Q ≥ q`. The bet on `φ`, `testBet p q φ`, pays `q / p` times `φ` plus `(1 - q) / (1 - p)`
times `1 - φ`; for the indicator of an event `s`, it is the likelihood ratio of the Bernoulli law
of parameter `q` to that of parameter `p` at the indicator of `s`, which pays `q / p` on `s` and
`(1 - q) / (1 - p)` off `s`. It is an e-variable for `S`, and its expected logarithm under `Q` is
at least the binary relative entropy `kl(q, p)`. So the largest e-power of `S` under `Q` is at
least `kl(q, p)`: a version for e-variables of the data processing inequality
`kl(Q s, P s) ≤ KL(Q, P)` of `LMLExplore.klBer_measureReal_le_klDiv`, for a composite null.

This is how lower bounds on the sample complexity of identification follow from bounds on
the expected logarithm of e-variables at a stopping time [EVR26, Note 41, Corollary 2]. For a
`δ`-correct algorithm with `δ ≤ 1 / 2`, the probability that the algorithm stops and recommends
the answer of `μ`, given the history at the stopping time, is a test of level `δ` for the
alternatives of `μ`, of power at least `1 - δ` under `μ`. It is randomized when the algorithm
draws its answer at random. The bet on it, with `p = δ` and `q = 1 - δ`, has expected logarithm at
least `kl(1 - δ, δ) = kl(δ, 1 - δ)` under `μ`.

## Main definitions

* `ProbabilityTheory.testBet p q φ`: the bet on the test `φ`, equal to
  `q / p * φ + (1 - q) / (1 - p) * (1 - φ)`.

## Main statements

* `ProbabilityTheory.lintegral_testBet_le_one`: under a measure `P` of mass at most `1` with
  `∫⁻ φ ∂P ≤ p`, the bet on `φ ≤ 1` has expectation at most `1`, for `0 < p ≤ q ≤ 1` and `p < 1`.
* `ProbabilityTheory.IsTest.isEVar_testBet`: the bet on a test of level `p` for a null of
  measures of mass at most `1` is an e-variable for that null.
* `ProbabilityTheory.klBer_le_eintegral_log_testBet`: under a probability measure `Q` with
  `q ≤ ∫⁻ φ ∂Q`, the expected logarithm of the bet on `φ ≤ 1` is at least `kl(q, p)`.
* `ProbabilityTheory.IsTest.klBer_le_maxEPower`: if `φ` is a test of level `p` for `S` and of power
  at least `q` under `Q`, then `kl(q, p)` is at most the largest e-power of `S` under `Q`.

## References

* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 41,
  `results/41-several-arms-bipolar-rate.md`, Section 3.
-/

public section

open MeasureTheory Set LMLExplore
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {p q : ℝ} {φ : Ω → ℝ≥0∞} {S : Set (Measure Ω)}

/-- The bet on the test `φ`: `q / p * φ + (1 - q) / (1 - p) * (1 - φ)`. For the indicator of an
event `s`, it is the likelihood ratio of the Bernoulli law of parameter `q` to the Bernoulli law of
parameter `p` at the indicator of `s`, equal to `q / p` on `s` and to `(1 - q) / (1 - p)` off `s`.
For `0 < p ≤ q ≤ 1` and `p < 1`, the bet on a test of level `p` for a null of measures of mass at
most `1` is an e-variable for that null (`ProbabilityTheory.IsTest.isEVar_testBet`). -/
noncomputable def testBet (p q : ℝ) (φ : Ω → ℝ≥0∞) : Ω → ℝ≥0∞ :=
  fun ω ↦ ENNReal.ofReal (q / p) * φ ω + ENNReal.ofReal ((1 - q) / (1 - p)) * (1 - φ ω)

lemma testBet_apply (p q : ℝ) (φ : Ω → ℝ≥0∞) (ω : Ω) :
    testBet p q φ ω =
      ENNReal.ofReal (q / p) * φ ω + ENNReal.ofReal ((1 - q) / (1 - p)) * (1 - φ ω) :=
  (rfl)

@[fun_prop]
lemma Measurable.testBet (hφ : Measurable φ) : Measurable (testBet p q φ) := by
  simp_rw [funext (testBet_apply p q φ)]
  fun_prop

/-- The expectation of the bet on `φ` under a measure `P`:
`q / p * ∫⁻ φ ∂P + (1 - q) / (1 - p) * ∫⁻ (1 - φ) ∂P`. -/
lemma lintegral_testBet (hφ : Measurable φ) (P : Measure Ω) :
    ∫⁻ ω, testBet p q φ ω ∂P = ENNReal.ofReal (q / p) * ∫⁻ ω, φ ω ∂P +
      ENNReal.ofReal ((1 - q) / (1 - p)) * ∫⁻ ω, 1 - φ ω ∂P := by
  simp_rw [testBet_apply]
  rw [lintegral_add_left (hφ.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The payoffs of the bet on `φ` satisfy `(1 - q) / (1 - p) ≤ 1 ≤ q / p` for `0 < p ≤ q ≤ 1`
and `p < 1`, and they are fair at the parameter `p`:
`p * (q / p) + (1 - p) * ((1 - q) / (1 - p)) = 1`. -/
private lemma testBet_payoffs (hp : p ∈ Ioo 0 1) (hpq : p ≤ q) (hq : q ≤ 1) :
    0 ≤ (1 - q) / (1 - p) ∧ (1 - q) / (1 - p) ≤ 1 ∧ 1 ≤ q / p ∧
      p * (q / p) + (1 - p) * ((1 - q) / (1 - p)) = 1 := by
  have h1p : 0 < 1 - p := sub_pos.2 hp.2
  refine ⟨div_nonneg (sub_nonneg.2 hq) h1p.le, (div_le_one h1p).2 (by linarith),
    (one_le_div hp.1).2 hpq, ?_⟩
  rw [mul_div_cancel₀ _ hp.1.ne', mul_div_cancel₀ _ h1p.ne']
  ring

/-- **The bet on a test is fair at the level `p`.** Under a measure `P` of mass at most `1` with
`∫⁻ φ ∂P ≤ p`, the bet on `φ ≤ 1` has expectation at most `1`, for `0 < p ≤ q ≤ 1` and `p < 1`. -/
theorem lintegral_testBet_le_one (hφ : Measurable φ) (hφ1 : ∀ ω, φ ω ≤ 1) (hp : p ∈ Ioo 0 1)
    (hpq : p ≤ q) (hq : q ≤ 1) {P : Measure Ω} (hP : P univ ≤ 1)
    (hPφ : ∫⁻ ω, φ ω ∂P ≤ ENNReal.ofReal p) :
    ∫⁻ ω, testBet p q φ ω ∂P ≤ 1 := by
  obtain ⟨hb0, hb1, ha1, hab⟩ := testBet_payoffs hp hpq hq
  have hfin : ∫⁻ ω, φ ω ∂P ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hPφ
  set x := (∫⁻ ω, φ ω ∂P).toReal
  have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
  have hxp : x ≤ p := ENNReal.toReal_le_of_le_ofReal hp.1.le hPφ
  -- `∫⁻ (1 - φ) ∂P = P univ - ∫⁻ φ ∂P ≤ 1 - x`
  have h1 : ∫⁻ ω, 1 - φ ω ∂P ≤ ENNReal.ofReal (1 - x) := by
    rw [lintegral_sub hφ hfin (ae_of_all _ hφ1), lintegral_one, ENNReal.ofReal_sub _ hx0,
      ENNReal.ofReal_one, ENNReal.ofReal_toReal hfin]
    exact tsub_le_tsub_right hP _
  rw [lintegral_testBet hφ, ← ENNReal.ofReal_toReal hfin]
  calc ENNReal.ofReal (q / p) * ENNReal.ofReal x +
      ENNReal.ofReal ((1 - q) / (1 - p)) * ∫⁻ ω, 1 - φ ω ∂P
  _ ≤ ENNReal.ofReal (q / p) * ENNReal.ofReal x +
      ENNReal.ofReal ((1 - q) / (1 - p)) * ENNReal.ofReal (1 - x) := by gcongr
  _ = ENNReal.ofReal (q / p * x + (1 - q) / (1 - p) * (1 - x)) := by
    rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hb0,
      ← ENNReal.ofReal_add (mul_nonneg (by linarith) hx0) (mul_nonneg hb0 (by linarith))]
  _ ≤ 1 := by
    rw [ENNReal.ofReal_le_one]
    -- `1 - (a x + b (1 - x)) = (p - x) (a - b)` for `a = q / p` and `b = (1-q) / (1-p)`
    nlinarith [mul_nonneg (sub_nonneg.2 hxp) (sub_nonneg.2 (hb1.trans ha1))]

/-- **The bet on a test is an e-variable.** For a null `S` of measures of mass at most `1`, the
bet on a test of level `p` for `S` is an e-variable for `S`, for `0 < p ≤ q ≤ 1` and `p < 1`. -/
theorem IsTest.isEVar_testBet (hφ : IsTest φ S (ENNReal.ofReal p)) (hp : p ∈ Ioo 0 1)
    (hpq : p ≤ q) (hq : q ≤ 1) (hS : ∀ P ∈ S, P univ ≤ 1) :
    IsEVar (testBet p q φ) S where
  measurable := Measurable.testBet hφ.measurable
  lintegral_le_one P hP :=
    lintegral_testBet_le_one hφ.measurable hφ.le_one hp hpq hq (hS P hP) (hφ.lintegral_le P hP)

/-- **The expected logarithm of the bet on a test.** Under a probability measure `Q` with
`q ≤ ∫⁻ φ ∂Q`, the expected logarithm of the bet on `φ ≤ 1` is at least the binary relative entropy
`kl(q, p)`, for `0 < p ≤ q < 1`. -/
theorem klBer_le_eintegral_log_testBet {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hφ : Measurable φ) (hφ1 : ∀ ω, φ ω ≤ 1) (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1)
    (hQφ : ENNReal.ofReal q ≤ ∫⁻ ω, φ ω ∂Q) :
    (klBer q p : EReal) ≤ ∫ᵉ ω, ENNReal.log (testBet p q φ ω) ∂Q := by
  have hp' : p ∈ Ioo 0 1 := ⟨hp, hpq.trans_lt hq⟩
  obtain ⟨-, hb1, ha1, -⟩ := testBet_payoffs hp' hpq hq.le
  set a := q / p
  set b := (1 - q) / (1 - p)
  have hb : 0 < b := div_pos (sub_pos.2 hq) (sub_pos.2 hp'.2)
  have ha : 0 < a := hb.trans_le (hb1.trans ha1)
  -- the bet is `a f + b (1 - f)`, for the real test `f = φ.toReal` with values in `[0, 1]`
  set f : Ω → ℝ := fun ω ↦ (φ ω).toReal
  have hf0 (ω : Ω) : 0 ≤ f ω := ENNReal.toReal_nonneg
  have hf1 (ω : Ω) : f ω ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hφ1 ω)
  set g : Ω → ℝ := fun ω ↦ a * f ω + b * (1 - f ω)
  have hgb (ω : Ω) : b ≤ g ω := by nlinarith [hf0 ω, hf1 ω, hb1.trans ha1]
  have hga (ω : Ω) : g ω ≤ a := by nlinarith [hf0 ω, hf1 ω, hb1.trans ha1]
  have hbet (ω : Ω) : testBet p q φ ω = ENNReal.ofReal (g ω) := by
    have hφω : φ ω = ENNReal.ofReal (f ω) := (ENNReal.ofReal_toReal ((hφ1 ω).trans_lt
      ENNReal.one_lt_top).ne).symm
    rw [testBet_apply, ENNReal.ofReal_add (mul_nonneg ha.le (hf0 ω))
      (mul_nonneg hb.le (sub_nonneg.2 (hf1 ω))), ENNReal.ofReal_mul ha.le,
      ENNReal.ofReal_mul hb.le, ENNReal.ofReal_sub _ (hf0 ω), ENNReal.ofReal_one, ← hφω]
  have hfm : Measurable f := hφ.ennreal_toReal
  have hgm : Measurable g := by fun_prop
  have hlog_int : Integrable (fun ω ↦ Real.log (g ω)) Q :=
    Integrable.of_mem_Icc (Real.log b) (Real.log a) (hgm.log.aemeasurable)
      (ae_of_all _ fun ω ↦ ⟨Real.log_le_log hb (hgb ω), Real.log_le_log (hb.trans_le (hgb ω))
        (hga ω)⟩)
  have hf_int : Integrable f Q :=
    Integrable.of_mem_Icc 0 1 hfm.aemeasurable (ae_of_all _ fun ω ↦ ⟨hf0 ω, hf1 ω⟩)
  -- the power `F = ∫ f ∂Q` of the test is at least `q`
  set F := ∫ ω, f ω ∂Q
  have hFeq : F = (∫⁻ ω, φ ω ∂Q).toReal :=
    integral_toReal hφ.aemeasurable (ae_of_all _ fun ω ↦ (hφ1 ω).trans_lt ENNReal.one_lt_top)
  have hF : q ≤ F := by
    rw [hFeq]
    exact (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      ((lintegral_mono hφ1).trans_eq (by simp)))).1 hQφ
  set L₁ := Real.log a
  set L₀ := Real.log b
  have hL : L₀ ≤ L₁ := Real.log_le_log hb (hb1.trans ha1)
  -- by concavity of the logarithm, `log (a f + b (1 - f)) ≥ f log a + (1 - f) log b`
  have hconc (ω : Ω) : f ω * L₁ + (1 - f ω) * L₀ ≤ Real.log (g ω) := by
    have h := strictConcaveOn_log_Ioi.concaveOn.2 (mem_Ioi.2 ha) (mem_Ioi.2 hb) (hf0 ω)
      (sub_nonneg.2 (hf1 ω)) (by ring)
    simpa only [smul_eq_mul, mul_comm (f ω), mul_comm (1 - f ω), g] using h
  have hmean : ∫ ω, (f ω * L₁ + (1 - f ω) * L₀) ∂Q = F * L₁ + (1 - F) * L₀ := by
    have : (fun ω ↦ f ω * L₁ + (1 - f ω) * L₀) = fun ω ↦ L₀ + f ω * (L₁ - L₀) := by
      ext ω; ring
    rw [this, integral_add (integrable_const _) (hf_int.mul_const _), integral_const,
      integral_mul_const, probReal_univ, one_smul]
    ring
  have hpq' : p ∈ Icc 0 1 := ⟨hp.le, hp'.2.le⟩
  have hq' : q ∈ Icc 0 1 := ⟨hp.le.trans hpq, hq.le⟩
  simp_rw [hbet, ENNReal.log_ofReal_of_pos (hb.trans_le (hgb _))]
  rw [eintegral_eq_integral hlog_int, klBer_eq_ofReal_klBerReal hq' hpq' (klBer_ne_top hp'),
    EReal.coe_ennreal_ofReal, EReal.coe_le_coe_iff]
  -- `kl(q, p) = q L₁ + (1 - q) L₀ ≤ F L₁ + (1 - F) L₀ ≤ ∫ log g ∂Q`, since `F ≥ q` and `L₀ ≤ L₁`
  have h : InformationTheory.klBerReal q p ≤ ∫ ω, Real.log (g ω) ∂Q := by
    refine le_trans ?_ (hmean.symm.trans_le (integral_mono ((hf_int.mul_const L₁).add
      (((integrable_const 1).sub hf_int).mul_const L₀)) hlog_int hconc))
    rw [InformationTheory.klBerReal_apply]
    nlinarith [mul_nonneg (sub_nonneg.2 hF) (sub_nonneg.2 hL)]
  exact max_le h ((klBerReal_nonneg_of_klBer_ne_top hq' hpq' (klBer_ne_top hp')).trans h)

/-- **The binary relative entropy is a lower bound on the largest e-power.** If `φ` is a test of
level `p` for a null `S` of measures of mass at most `1`, of power at least `q` under a
probability measure `Q`, then `kl(q, p)` is at most the largest e-power of `S` under `Q`, for
`0 < p ≤ q < 1`. -/
theorem IsTest.klBer_le_maxEPower {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hφ : IsTest φ S (ENNReal.ofReal p)) (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1)
    (hS : ∀ P ∈ S, P univ ≤ 1) (hQφ : ENNReal.ofReal q ≤ ∫⁻ ω, φ ω ∂Q) :
    (klBer q p : EReal) ≤ maxEPower Q S :=
  (klBer_le_eintegral_log_testBet hφ.measurable hφ.le_one hp hpq hq hQφ).trans
    ((hφ.isEVar_testBet ⟨hp, hpq.trans_lt hq⟩ hpq hq.le hS).eintegral_log_le_maxEPower Q)

end ProbabilityTheory
