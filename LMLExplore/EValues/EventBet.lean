/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.KLInf
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli

/-!
# The bet on an event, and the binary relative entropy as a lower bound on the e-power

Let `s` be an event of probability at most `p` under every member of a null `S`, and of
probability at least `q ≥ p` under an alternative `Q`. The bet on `s`, `eventBet p q s`, is the
likelihood ratio of the Bernoulli law of parameter `q` to that of parameter `p` at the indicator
of `s`: it pays `q / p` on `s` and `(1 - q) / (1 - p)` off `s`. It is an e-variable for `S`, and
its expected logarithm under `Q` is at least the binary relative entropy `kl(q, p)`. So the
largest e-power of `S` under `Q` is at least `kl(q, p)`: a version for e-variables of the data
processing inequality `kl(Q s, P s) ≤ KL(Q, P)` of `LMLExplore.klBer_measureReal_le_klDiv`, for a
composite null.

This is how lower bounds on the sample complexity of identification follow from bounds on
the expected logarithm of e-variables at a stopping time [EVR26, Note 41, Corollary 2]. For a
`δ`-correct algorithm with `δ ≤ 1 / 2`, the event "the algorithm stops and recommends the answer
of `μ`" has probability at most `δ` under the alternatives of `μ` and at least `1 - δ` under `μ`,
and the bet on it, with `p = δ` and `q = 1 - δ`, has expected logarithm at least
`kl(1 - δ, δ) = kl(δ, 1 - δ)` under `μ`.

## Main definitions

* `ProbabilityTheory.eventBet p q s`: the bet on the event `s`, equal to `q / p` on `s` and to
  `(1 - q) / (1 - p)` off `s`.

## Main statements

* `ProbabilityTheory.lintegral_eventBet_le_one`: under a measure `P` of mass at most `1` with
  `P s ≤ p`, the bet on `s` has expectation at most `1`, for `0 < p ≤ q ≤ 1` and `p < 1`.
* `ProbabilityTheory.isEVar_eventBet`: the bet on `s` is an e-variable for every null of measures
  of mass at most `1` that give `s` a mass at most `p`.
* `ProbabilityTheory.klBer_le_eintegral_log_eventBet`: under a probability measure `Q` with
  `q ≤ Q s`, the expected logarithm of the bet on `s` is at least `kl(q, p)`.
* `ProbabilityTheory.klBer_le_maxEPower`: if every member of `S` gives `s` a mass at most `p` and
  `Q` gives it a mass at least `q`, then `kl(q, p)` is at most the largest e-power of `S` under
  `Q`.

## References

* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 41,
  `results/41-several-arms-bipolar-rate.md`, Section 3.
-/

public section

open MeasureTheory Set LMLExplore
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {p q : ℝ} {s : Set Ω} {ω : Ω}

open scoped Classical in
/-- The bet on the event `s`: the likelihood ratio of the Bernoulli law of parameter `q` to the
Bernoulli law of parameter `p` at the indicator of `s`, equal to `q / p` on `s` and to
`(1 - q) / (1 - p)` off `s`. For `0 < p ≤ q ≤ 1` and `p < 1`, it is an e-variable for the measures
of mass at most `1` that give `s` a mass at most `p` (`ProbabilityTheory.isEVar_eventBet`). -/
noncomputable def eventBet (p q : ℝ) (s : Set Ω) : Ω → ℝ≥0∞ :=
  s.piecewise (fun _ ↦ ENNReal.ofReal (q / p)) fun _ ↦ ENNReal.ofReal ((1 - q) / (1 - p))

@[simp]
lemma eventBet_of_mem (h : ω ∈ s) : eventBet p q s ω = ENNReal.ofReal (q / p) := by
  classical
  rw [eventBet, Set.piecewise_eq_of_mem _ _ _ h]

@[simp]
lemma eventBet_of_notMem (h : ω ∉ s) : eventBet p q s ω = ENNReal.ofReal ((1 - q) / (1 - p)) := by
  classical
  rw [eventBet, Set.piecewise_eq_of_notMem _ _ _ h]

lemma measurable_eventBet (hs : MeasurableSet s) : Measurable (eventBet p q s) := by
  classical
  exact Measurable.piecewise hs measurable_const measurable_const

/-- The expectation of the bet on `s` under a measure `P`: `q / p * P s + (1 - q) / (1 - p) * P sᶜ`.
-/
lemma lintegral_eventBet (hs : MeasurableSet s) (P : Measure Ω) :
    ∫⁻ ω, eventBet p q s ω ∂P =
      ENNReal.ofReal (q / p) * P s + ENNReal.ofReal ((1 - q) / (1 - p)) * P sᶜ := by
  rw [← lintegral_add_compl _ hs, setLIntegral_congr_fun hs fun ω h ↦ eventBet_of_mem h,
    setLIntegral_congr_fun hs.compl fun ω h ↦ eventBet_of_notMem h, setLIntegral_const,
    setLIntegral_const]

/-- The payoffs of the bet on `s` satisfy `(1 - q) / (1 - p) ≤ 1 ≤ q / p` for `0 < p ≤ q ≤ 1`
and `p < 1`, and they are fair at the parameter `p`:
`p * (q / p) + (1 - p) * ((1 - q) / (1 - p)) = 1`. -/
private lemma eventBet_payoffs (hp : p ∈ Ioo 0 1) (hpq : p ≤ q) (hq : q ≤ 1) :
    0 ≤ (1 - q) / (1 - p) ∧ (1 - q) / (1 - p) ≤ 1 ∧ 1 ≤ q / p ∧
      p * (q / p) + (1 - p) * ((1 - q) / (1 - p)) = 1 := by
  have h1p : 0 < 1 - p := sub_pos.2 hp.2
  refine ⟨div_nonneg (sub_nonneg.2 hq) h1p.le, (div_le_one h1p).2 (by linarith),
    (one_le_div hp.1).2 hpq, ?_⟩
  rw [mul_div_cancel₀ _ hp.1.ne', mul_div_cancel₀ _ h1p.ne']
  ring

/-- **The bet on an event is fair at the level `p`.** Under a measure `P` of mass at most `1`
that gives the event `s` a mass at most `p`, the bet on `s` has expectation at most `1`, for
`0 < p ≤ q ≤ 1` and `p < 1`. -/
theorem lintegral_eventBet_le_one (hs : MeasurableSet s) (hp : p ∈ Ioo 0 1) (hpq : p ≤ q)
    (hq : q ≤ 1) {P : Measure Ω} (hP : P univ ≤ 1) (hPs : P.real s ≤ p) :
    ∫⁻ ω, eventBet p q s ω ∂P ≤ 1 := by
  have : IsFiniteMeasure P := ⟨hP.trans_lt ENNReal.one_lt_top⟩
  obtain ⟨hb0, hb1, ha1, hab⟩ := eventBet_payoffs hp hpq hq
  have hsum : P.real s + P.real sᶜ ≤ 1 := by
    rw [measureReal_add_measureReal_compl hs]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hP)
  rw [lintegral_eventBet hs, ← ofReal_measureReal (μ := P), ← ofReal_measureReal (μ := P),
    ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hb0,
    ← ENNReal.ofReal_add (mul_nonneg (by linarith) measureReal_nonneg)
      (mul_nonneg hb0 measureReal_nonneg), ENNReal.ofReal_le_one]
  -- `1 - (a x + b y) = (p - x) (a - b) + (1 - x - y) b` for `a = q / p` and `b = (1-q) / (1-p)`
  nlinarith [mul_nonneg (sub_nonneg.2 hPs) (sub_nonneg.2 (hb1.trans ha1)),
    mul_nonneg (sub_nonneg.2 hsum) hb0]

/-- **The bet on an event is an e-variable.** For a null `S` of measures of mass at most `1` that
give the event `s` a mass at most `p`, the bet on `s` is an e-variable for `S`, for
`0 < p ≤ q ≤ 1` and `p < 1`. -/
theorem isEVar_eventBet {S : Set (Measure Ω)} (hs : MeasurableSet s) (hp : p ∈ Ioo 0 1)
    (hpq : p ≤ q) (hq : q ≤ 1) (hS : ∀ P ∈ S, P univ ≤ 1) (hSs : ∀ P ∈ S, P.real s ≤ p) :
    IsEVar (eventBet p q s) S where
  measurable := measurable_eventBet hs
  lintegral_le_one _ hP := lintegral_eventBet_le_one hs hp hpq hq (hS _ hP) (hSs _ hP)

/-- **The expected logarithm of the bet on an event.** Under a probability measure `Q` that gives
the event `s` a mass at least `q`, the expected logarithm of the bet on `s` is at least the binary
relative entropy `kl(q, p)`, for `0 < p ≤ q < 1`. -/
theorem klBer_le_eintegral_log_eventBet {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hs : MeasurableSet s) (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1) (hQs : q ≤ Q.real s) :
    (klBer q p : EReal) ≤ ∫ᵉ ω, ENNReal.log (eventBet p q s ω) ∂Q := by
  classical
  have hp' : p ∈ Ioo 0 1 := ⟨hp, hpq.trans_lt hq⟩
  obtain ⟨-, hb1, ha1, -⟩ := eventBet_payoffs hp' hpq hq.le
  have hb : 0 < (1 - q) / (1 - p) := div_pos (sub_pos.2 hq) (sub_pos.2 hp'.2)
  have ha : 0 < q / p := div_pos (hp.trans_le hpq) hp
  set L₁ := Real.log (q / p)
  set L₀ := Real.log ((1 - q) / (1 - p))
  have hL₁ : 0 ≤ L₁ := Real.log_nonneg ha1
  have hL₀ : L₀ ≤ 0 := Real.log_nonpos hb.le hb1
  -- the logarithm of the bet is the real function equal to `L₁` on `s` and to `L₀` off `s`
  have hlog : (fun ω ↦ ENNReal.log (eventBet p q s ω)) =
      fun ω ↦ ((s.piecewise (fun _ ↦ L₁) (fun _ ↦ L₀) ω : ℝ) : EReal) := by
    ext ω
    by_cases h : ω ∈ s
    · simp [h, ENNReal.log_ofReal_of_pos ha, L₁]
    · simp [h, ENNReal.log_ofReal_of_pos hb, L₀]
  have hint : Integrable (s.piecewise (fun _ ↦ L₁) (fun _ ↦ L₀)) Q :=
    Integrable.piecewise hs.nullMeasurableSet (integrable_const L₁).integrableOn
      (integrable_const L₀).integrableOn
  have hpq' : p ∈ Icc 0 1 := ⟨hp.le, hp'.2.le⟩
  have hq' : q ∈ Icc 0 1 := ⟨hp.le.trans hpq, hq.le⟩
  rw [hlog, eintegral_eq_integral hint, integral_piecewise hs (integrable_const L₁).integrableOn
    (integrable_const L₀).integrableOn, setIntegral_const, setIntegral_const,
    probReal_compl_eq_one_sub hs, smul_eq_mul, smul_eq_mul,
    klBer_eq_ofReal_klBerReal hq' hpq' (klBer_ne_top hp'), EReal.coe_ennreal_ofReal,
    EReal.coe_le_coe_iff]
  -- `kl(q, p) = q L₁ + (1 - q) L₀ ≤ x L₁ + (1 - x) L₀` for `x = Q s ≥ q`, since `L₀ ≤ L₁`
  have h : InformationTheory.klBerReal q p ≤ Q.real s * L₁ + (1 - Q.real s) * L₀ := by
    rw [InformationTheory.klBerReal_apply]
    nlinarith [mul_nonneg (sub_nonneg.2 hQs) (sub_nonneg.2 (hL₀.trans hL₁))]
  exact max_le h ((klBerReal_nonneg_of_klBer_ne_top hq' hpq' (klBer_ne_top hp')).trans h)

/-- **The binary relative entropy is a lower bound on the largest e-power.** If every member of a
null `S` of measures of mass at most `1` gives the event `s` a mass at most `p`, and a probability
measure `Q` gives it a mass at least `q`, then `kl(q, p)` is at most the largest e-power of `S`
under `Q`, for `0 < p ≤ q < 1`. -/
theorem klBer_le_maxEPower {S : Set (Measure Ω)} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hs : MeasurableSet s) (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1) (hS : ∀ P ∈ S, P univ ≤ 1)
    (hSs : ∀ P ∈ S, P.real s ≤ p) (hQs : q ≤ Q.real s) :
    (klBer q p : EReal) ≤ maxEPower Q S :=
  (klBer_le_eintegral_log_eventBet hs hp hpq hq hQs).trans
    ((isEVar_eventBet hs ⟨hp, hpq.trans_lt hq⟩ hpq hq.le hS hSs).eintegral_log_le_maxEPower Q)

end ProbabilityTheory
