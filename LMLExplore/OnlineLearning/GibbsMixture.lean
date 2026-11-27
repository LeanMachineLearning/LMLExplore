/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Gibbs mixtures over arbitrary priors

Let `μ` be a prior, a probability measure on a measurable space `Θ` of experts (or parameters),
and let `L : Θ → ℝ` be the cumulative losses of the experts. At a temperature `λ > 0`, the
*Gibbs measure* of `L` is the tilted measure `μ.gibbs L λ = μ.tilted (fun θ ↦ -L θ / λ)`, with
density `e^{-L/λ} / ∫ e^{-L/λ} dμ` against `μ`, and the *mix loss* of `L` is
`μ.mixLoss L λ = -λ log ∫ e^{-L/λ} dμ`. They are the posterior and the cumulative loss of the
exponentially weighted average of the experts: the Weighted Average and Aggregating Algorithms
and Cover's universal portfolio are analysed through them [Ora, §11.1].

The central fact is the *variational formula* of the mix loss [Ora, (11.5), Problem 11.1]: over
probability measures `Q` with `KL(Q, μ) < ∞` under which `L` is integrable,
`μ.mixLoss L λ = inf_Q (∫ L dQ + λ KL(Q, μ))`,
attained exactly at the Gibbs measure. It is the Donsker–Varadhan formula for `-L/λ`, and here it
comes from an exact identity: for every `Q` with `KL(Q, μ) < ∞` and `L` integrable under `Q`,
`∫ L dQ + λ KL(Q, μ) = μ.mixLoss L λ + λ KL(Q, μ.gibbs L λ)`,
the change of reference from the prior to the Gibbs measure (Mathlib's
`MeasureTheory.integral_llr_tilted_right`). The mix loss also telescopes: the increment
`μ.mixLoss (L + ℓ) λ - μ.mixLoss L λ` is the mix loss of the next loss `ℓ` under the Gibbs
measure of `L`, which is how the cumulative mix loss of an online algorithm is computed. Finally,
the mix loss is nondecreasing in the temperature, by Jensen's inequality for `x ↦ x ^ p`,
`p ≤ 1`, which handles temperatures that change over time.

A finite set of experts with weights `w` is the case of the prior `∑ a, w a • δ_a`, at the
temperature `η⁻¹` of a learning rate `η`: the mix loss `LMLExplore.OnlineLearning.mixLoss` of
exponential weights, and its potential `hedgePotential`, are derived from the lemmas here in
`LMLExplore.OnlineLearning.ExponentialWeights`.

The definitions take the prior as their first explicit argument and live in the namespace
`MeasureTheory.Measure`, so that `μ.mixLoss L λ` and `μ.gibbs L λ` elaborate.

## Main definitions

* `MeasureTheory.Measure.mixLoss μ L lam`: the mix loss `-lam * log ∫ exp (-L θ / lam) ∂μ`.
* `MeasureTheory.Measure.gibbs μ L lam`: the Gibbs measure `μ.tilted fun θ ↦ -L θ / lam`.

## Main statements

* `integral_add_mul_toReal_klDiv_eq_mixLoss_add`: the identity
  `∫ L dQ + λ KL(Q, μ) = μ.mixLoss L λ + λ KL(Q, μ.gibbs L λ)`.
* `mixLoss_le_integral_add_mul_toReal_klDiv`: the variational inequality
  `μ.mixLoss L λ ≤ ∫ L dQ + λ KL(Q, μ)` for `λ > 0`.
* `integral_add_mul_toReal_klDiv_eq_mixLoss_iff`: equality holds exactly at the Gibbs measure,
  and `integral_add_mul_toReal_klDiv_gibbs` its case of the Gibbs measure.
* `isLeast_mixLoss`: the variational formula, the mix loss as the least value of
  `∫ L dQ + λ KL(Q, μ)` over probability measures `Q` with `KL(Q, μ) < ∞` under which `L` is
  integrable.
* `mixLoss_gibbs`: the telescoping identity
  `(μ.gibbs L λ).mixLoss ℓ λ = μ.mixLoss (L + ℓ) λ - μ.mixLoss L λ`.
* `mixLoss_le_mixLoss_of_le`: the mix loss is nondecreasing in the temperature.
* `le_mixLoss`, `mixLoss_le_integral`: the mix loss lies between a lower bound of the losses and
  their mean under the prior.
* `integrable_exp_neg_div_of_le`, `integrable_gibbs_of_le`: losses bounded below meet the
  integrability hypotheses of the statements above.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Real Set InformationTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {Θ : Type*} [MeasurableSpace Θ] {μ Q : Measure Θ} {L ℓ : Θ → ℝ} {lam lam' c : ℝ}

/-! ### Definitions -/

/-- The **mix loss** `-lam * log ∫ exp (-L θ / lam) ∂μ` of the cumulative losses `L` of the
experts under the prior `μ`, at the temperature `lam`. -/
noncomputable def mixLoss (μ : Measure Θ) (L : Θ → ℝ) (lam : ℝ) : ℝ :=
  -lam * log (∫ θ, exp (-L θ / lam) ∂μ)

lemma mixLoss_def (μ : Measure Θ) (L : Θ → ℝ) (lam : ℝ) :
    μ.mixLoss L lam = -lam * log (∫ θ, exp (-L θ / lam) ∂μ) := (rfl)

/-- The **Gibbs measure** of the cumulative losses `L` under the prior `μ` at the temperature
`lam`: the tilted measure `μ.tilted fun θ ↦ -L θ / lam`, with density
`exp (-L θ / lam) / ∫ exp (-L θ' / lam) ∂μ` against `μ`. -/
noncomputable def gibbs (μ : Measure Θ) (L : Θ → ℝ) (lam : ℝ) : Measure Θ :=
  μ.tilted fun θ ↦ -L θ / lam

lemma gibbs_def (μ : Measure Θ) (L : Θ → ℝ) (lam : ℝ) :
    μ.gibbs L lam = μ.tilted fun θ ↦ -L θ / lam := (rfl)

/-- The mass of a set under the Gibbs measure: the integral over it of the density
`exp (-L θ / lam) / ∫ exp (-L θ' / lam) ∂μ` against the prior. -/
lemma gibbs_apply (μ : Measure Θ) [SFinite μ] (L : Θ → ℝ) (lam : ℝ) (s : Set Θ) :
    μ.gibbs L lam s =
      ∫⁻ θ in s, ENNReal.ofReal (exp (-L θ / lam) / ∫ θ', exp (-L θ' / lam) ∂μ) ∂μ :=
  tilted_apply μ _ s

/-- The density of the Gibbs measure against the prior is
`exp (-L θ / lam) / ∫ exp (-L θ' / lam) ∂μ`. -/
lemma rnDeriv_gibbs [SigmaFinite μ] (hL : AEMeasurable (fun θ ↦ -L θ / lam) μ) :
    (μ.gibbs L lam).rnDeriv μ =ᵐ[μ]
      fun θ ↦ ENNReal.ofReal (exp (-L θ / lam) / ∫ θ', exp (-L θ' / lam) ∂μ) :=
  rnDeriv_tilted_left_self hL

/-- The Gibbs measure is the zero measure or a probability measure, like every tilted measure. -/
instance isZeroOrProbabilityMeasure_gibbs (μ : Measure Θ) (L : Θ → ℝ) (lam : ℝ) :
    IsZeroOrProbabilityMeasure (μ.gibbs L lam) :=
  isZeroOrProbabilityMeasure_tilted

/-- The Gibbs measure of a nonzero prior, when `exp (-L / lam)` is `μ`-integrable, is a
probability measure. -/
lemma isProbabilityMeasure_gibbs [NeZero μ] (hexp : Integrable (fun θ ↦ exp (-L θ / lam)) μ) :
    IsProbabilityMeasure (μ.gibbs L lam) :=
  isProbabilityMeasure_tilted hexp

lemma gibbs_absolutelyContinuous (μ : Measure Θ) (L : Θ → ℝ) (lam : ℝ) : μ.gibbs L lam ≪ μ :=
  tilted_absolutelyContinuous μ _

lemma absolutelyContinuous_gibbs (hexp : Integrable (fun θ ↦ exp (-L θ / lam)) μ) :
    μ ≪ μ.gibbs L lam :=
  absolutelyContinuous_tilted hexp

/-- Integrals against the Gibbs measure are integrals against the prior, with the density
`exp (-L θ / lam) / ∫ exp (-L θ' / lam) ∂μ`. -/
lemma integral_gibbs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Θ → E) :
    ∫ θ, g θ ∂(μ.gibbs L lam) =
      ∫ θ, (exp (-L θ / lam) / ∫ θ', exp (-L θ' / lam) ∂μ) • g θ ∂μ :=
  integral_tilted _ g

/-! ### The variational formula -/

/-- The relative entropy of the Gibbs measure against the prior is finite when the losses are
integrable under the Gibbs measure. -/
lemma klDiv_gibbs_ne_top [SigmaFinite μ]
    (hexp : Integrable (fun θ ↦ exp (-L θ / lam)) μ) (hLG : Integrable L (μ.gibbs L lam)) :
    klDiv (μ.gibbs L lam) μ ≠ ∞ := by
  refine klDiv_ne_top (gibbs_absolutelyContinuous μ L lam) ?_
  -- the log-likelihood ratio is `-L θ / lam - log Z`
  have hllr : llr (μ.gibbs L lam) μ =ᵐ[μ.gibbs L lam]
      fun θ ↦ -L θ / lam - log (∫ θ', exp (-L θ' / lam) ∂μ) := by
    rw [llr_def]
    exact (gibbs_absolutelyContinuous μ L lam).ae_le (log_rnDeriv_tilted_left_self hexp)
  rw [integrable_congr hllr]
  exact (hLG.neg.div_const lam).sub (integrable_const _)

/-- **The change of reference to the Gibbs measure.** For probability measures `μ` and `Q`, a
temperature `lam ≠ 0`, losses `L` integrable under `Q` with `exp (-L / lam)` integrable under `μ`,
and `KL(Q, μ) < ∞`:
`∫ L dQ + lam * KL(Q, μ) = μ.mixLoss L lam + lam * KL(Q, μ.gibbs L lam)`. -/
theorem integral_add_mul_toReal_klDiv_eq_mixLoss_add [IsProbabilityMeasure μ]
    [IsProbabilityMeasure Q] (hlam : lam ≠ 0) (hexp : Integrable (fun θ ↦ exp (-L θ / lam)) μ)
    (hLQ : Integrable L Q) (hQ : klDiv Q μ ≠ ∞) :
    ∫ θ, L θ ∂Q + lam * (klDiv Q μ).toReal =
      μ.mixLoss L lam + lam * (klDiv Q (μ.gibbs L lam)).toReal := by
  obtain ⟨hac, hllr⟩ := klDiv_ne_top_iff.1 hQ
  have := isProbabilityMeasure_gibbs hexp
  have hacG : Q ≪ μ.gibbs L lam := hac.trans (absolutelyContinuous_gibbs hexp)
  have hf : Integrable (fun θ ↦ -L θ / lam) Q := hLQ.neg.div_const lam
  rw [toReal_klDiv_of_measure_eq hac (by simp), toReal_klDiv_of_measure_eq hacG (by simp),
    gibbs_def, integral_llr_tilted_right hac hf hexp hllr, mixLoss_def,
    integral_div, integral_neg]
  field_simp
  ring

/-- **The variational inequality of the mix loss** [Ora, (11.5)]: at a temperature `lam > 0`,
`μ.mixLoss L lam ≤ ∫ L dQ + lam * KL(Q, μ)` for every probability measure `Q` with
`KL(Q, μ) < ∞` under which `L` is integrable. -/
theorem mixLoss_le_integral_add_mul_toReal_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
    (hlam : 0 < lam) (hexp : Integrable (fun θ ↦ exp (-L θ / lam)) μ) (hLQ : Integrable L Q)
    (hQ : klDiv Q μ ≠ ∞) :
    μ.mixLoss L lam ≤ ∫ θ, L θ ∂Q + lam * (klDiv Q μ).toReal := by
  rw [integral_add_mul_toReal_klDiv_eq_mixLoss_add hlam.ne' hexp hLQ hQ]
  exact le_add_of_nonneg_right (mul_nonneg hlam.le ENNReal.toReal_nonneg)

/-- **Equality in the change of reference holds exactly at the Gibbs measure**: for `lam ≠ 0`,
`∫ L dQ + lam * KL(Q, μ)` equals the mix loss exactly when `Q` is the Gibbs measure. For
`lam > 0` this says that the Gibbs measure is the unique minimizer of the variational formula
[Ora, Problem 11.1]. -/
theorem integral_add_mul_toReal_klDiv_eq_mixLoss_iff [IsProbabilityMeasure μ]
    [IsProbabilityMeasure Q] (hlam : lam ≠ 0) (hexp : Integrable (fun θ ↦ exp (-L θ / lam)) μ)
    (hLQ : Integrable L Q) (hQ : klDiv Q μ ≠ ∞) :
    ∫ θ, L θ ∂Q + lam * (klDiv Q μ).toReal = μ.mixLoss L lam ↔ Q = μ.gibbs L lam := by
  obtain ⟨hac, hllr⟩ := klDiv_ne_top_iff.1 hQ
  have := isProbabilityMeasure_gibbs hexp
  have hQG : klDiv Q (μ.gibbs L lam) ≠ ∞ :=
    klDiv_ne_top (hac.trans (absolutelyContinuous_gibbs hexp))
      (integrable_llr_tilted_right hac (hLQ.neg.div_const lam) hllr hexp)
  rw [integral_add_mul_toReal_klDiv_eq_mixLoss_add hlam hexp hLQ hQ, add_eq_left, mul_eq_zero,
    or_iff_right hlam, ENNReal.toReal_eq_zero_iff, or_iff_left hQG, klDiv_eq_zero_iff]

/-- **The Gibbs measure gives equality in the change of reference**: for `lam ≠ 0` and losses
integrable under the Gibbs measure,
`∫ L d(μ.gibbs L lam) + lam * KL(μ.gibbs L lam, μ) = μ.mixLoss L lam`. -/
theorem integral_add_mul_toReal_klDiv_gibbs [IsProbabilityMeasure μ] (hlam : lam ≠ 0)
    (hexp : Integrable (fun θ ↦ exp (-L θ / lam)) μ) (hLG : Integrable L (μ.gibbs L lam)) :
    ∫ θ, L θ ∂(μ.gibbs L lam) + lam * (klDiv (μ.gibbs L lam) μ).toReal = μ.mixLoss L lam :=
  have := isProbabilityMeasure_gibbs hexp
  (integral_add_mul_toReal_klDiv_eq_mixLoss_iff hlam hexp hLG (klDiv_gibbs_ne_top hexp hLG)).2 rfl

/-- **The variational formula of the mix loss** [Ora, (11.5), Problem 11.1]: at a temperature
`lam > 0`, the mix loss is the least value of `∫ L dQ + lam * KL(Q, μ)` over the probability
measures `Q` with `KL(Q, μ) < ∞` under which `L` is integrable, attained at the Gibbs measure. -/
theorem isLeast_mixLoss [IsProbabilityMeasure μ] (hlam : 0 < lam)
    (hexp : Integrable (fun θ ↦ exp (-L θ / lam)) μ) (hLG : Integrable L (μ.gibbs L lam)) :
    IsLeast {r | ∃ Q : Measure Θ, IsProbabilityMeasure Q ∧ klDiv Q μ ≠ ∞ ∧ Integrable L Q ∧
      r = ∫ θ, L θ ∂Q + lam * (klDiv Q μ).toReal} (μ.mixLoss L lam) := by
  refine ⟨⟨μ.gibbs L lam, isProbabilityMeasure_gibbs hexp, klDiv_gibbs_ne_top hexp hLG, hLG,
    (integral_add_mul_toReal_klDiv_gibbs hlam.ne' hexp hLG).symm⟩, ?_⟩
  rintro _ ⟨Q, hQ, hKL, hLQ, rfl⟩
  exact mixLoss_le_integral_add_mul_toReal_klDiv hlam hexp hLQ hKL

/-- The mix loss is at most the mean `∫ L dμ` of the losses under the prior. -/
lemma mixLoss_le_integral [IsProbabilityMeasure μ] (hlam : 0 < lam)
    (hexp : Integrable (fun θ ↦ exp (-L θ / lam)) μ) (hL : Integrable L μ) :
    μ.mixLoss L lam ≤ ∫ θ, L θ ∂μ := by
  -- the case `Q = μ` of the variational inequality
  simpa [klDiv_self] using
    mixLoss_le_integral_add_mul_toReal_klDiv hlam hexp hL (by simp)

/-- The mix loss is at least every almost sure lower bound of the losses. -/
lemma le_mixLoss [IsProbabilityMeasure μ] (hlam : 0 < lam)
    (hexp : Integrable (fun θ ↦ exp (-L θ / lam)) μ) (hc : ∀ᵐ θ ∂μ, c ≤ L θ) :
    c ≤ μ.mixLoss L lam := by
  have hle : ∫ θ, exp (-L θ / lam) ∂μ ≤ exp (-c / lam) := by
    calc ∫ θ, exp (-L θ / lam) ∂μ ≤ ∫ _, exp (-c / lam) ∂μ := by
          refine integral_mono_ae hexp (integrable_const _) ?_
          filter_upwards [hc] with θ hθ
          exact exp_le_exp.2 (div_le_div_of_nonneg_right (neg_le_neg hθ) hlam.le)
    _ = exp (-c / lam) := by simp
  have hlog := log_le_log (integral_exp_pos hexp) hle
  rw [log_exp, le_div_iff₀ hlam] at hlog
  rw [mixLoss_def]
  linarith

/-! ### The telescoping identity -/

/-- **The mix losses telescope**: the mix loss of the next losses `ℓ` under the Gibbs measure of
the cumulative losses `L` is the increment `μ.mixLoss (L + ℓ) lam - μ.mixLoss L lam`. -/
theorem mixLoss_gibbs [NeZero μ] (hexp : Integrable (fun θ ↦ exp (-L θ / lam)) μ)
    (hexp' : Integrable (fun θ ↦ exp (-(L + ℓ) θ / lam)) μ) :
    (μ.gibbs L lam).mixLoss ℓ lam = μ.mixLoss (L + ℓ) lam - μ.mixLoss L lam := by
  have hsum : (fun θ ↦ -L θ / lam) + (fun θ ↦ -ℓ θ / lam) = fun θ ↦ -(L + ℓ) θ / lam := by
    ext θ
    simp only [Pi.add_apply]
    ring
  rw [mixLoss_def, gibbs_def, integral_exp_tilted, hsum,
    log_div (integral_exp_pos hexp').ne' (integral_exp_pos hexp).ne', mixLoss_def, mixLoss_def]
  ring

/-! ### Monotonicity in the temperature -/

/-- **The mix loss is nondecreasing in the temperature**: for `0 < lam' ≤ lam`,
`μ.mixLoss L lam' ≤ μ.mixLoss L lam`. -/
theorem mixLoss_le_mixLoss_of_le [IsProbabilityMeasure μ] (hlam' : 0 < lam') (hle : lam' ≤ lam)
    (hexp : Integrable (fun θ ↦ exp (-L θ / lam')) μ) :
    μ.mixLoss L lam' ≤ μ.mixLoss L lam := by
  have hlam : 0 < lam := hlam'.trans_le hle
  set p := lam' / lam with hp
  have hp0 : 0 ≤ p := (div_pos hlam' hlam).le
  have hp1 : p ≤ 1 := (div_le_one hlam).2 hle
  have hpow (θ : Θ) : exp (-L θ / lam') ^ p = exp (-L θ / lam) := by
    rw [← exp_mul, hp]
    congr 1
    field_simp
  -- `exp (-L / lam)` is integrable, `lam⁻¹` lying between the multipliers `0` and `lam'⁻¹`
  have hexp_lam : Integrable (fun θ ↦ exp (-L θ / lam)) μ := by
    simpa only [div_eq_inv_mul] using ProbabilityTheory.integrable_exp_mul_of_le_of_le
      (X := fun θ ↦ -L θ) (a := 0) (b := lam'⁻¹) (t := lam⁻¹) (by simp)
      (by simpa only [div_eq_inv_mul] using hexp) (inv_nonneg.2 hlam.le) (inv_anti₀ hlam' hle)
  -- Jensen's inequality for the concave `x ↦ x ^ p`, `p = lam' / lam ≤ 1`
  have hjensen : ∫ θ, exp (-L θ / lam) ∂μ ≤ (∫ θ, exp (-L θ / lam') ∂μ) ^ p := by
    simp_rw [← hpow]
    refine (Real.concaveOn_rpow hp0 hp1).le_map_integral
      (continuousOn_id.rpow_const fun _ _ ↦ Or.inr hp0) isClosed_Ici
      (ae_of_all _ fun θ ↦ (exp_pos _).le) hexp ?_
    simpa only [Function.comp_def, hpow] using hexp_lam
  have hlog := log_le_log (integral_exp_pos hexp_lam) hjensen
  rw [log_rpow (integral_exp_pos hexp), hp, div_mul_eq_mul_div, le_div_iff₀ hlam] at hlog
  rw [mixLoss_def, mixLoss_def]
  linarith

/-! ### Losses bounded below -/

/-- For losses bounded below and a temperature `lam > 0`, `exp (-L / lam)` is integrable under a
finite prior. -/
lemma integrable_exp_neg_div_of_le [IsFiniteMeasure μ] (hL : AEMeasurable L μ) (hlam : 0 < lam)
    (hc : ∀ᵐ θ ∂μ, c ≤ L θ) :
    Integrable (fun θ ↦ exp (-L θ / lam)) μ := by
  simpa only [div_eq_inv_mul, Pi.neg_apply] using ProbabilityTheory.integrable_exp_mul_of_le lam⁻¹
    (-c) (inv_nonneg.2 hlam.le) hL.neg (hc.mono fun _ h ↦ neg_le_neg h)

/-- For losses bounded below and a temperature `lam > 0`, the losses are integrable under the
Gibbs measure of a finite prior. -/
lemma integrable_gibbs_of_le [IsFiniteMeasure μ] (hL : AEMeasurable L μ) (hlam : 0 < lam)
    (hc : ∀ᵐ θ ∂μ, c ≤ L θ) :
    Integrable L (μ.gibbs L lam) := by
  rw [gibbs_def, integrable_tilted_iff (integrable_exp_neg_div_of_le hL hlam hc)]
  -- `lam⁻¹` lies in the interior of the multipliers `t` with `exp (t * -L)` integrable,
  -- which contains `(0, ∞)`, so `-L * exp (-L / lam)` is integrable
  have hsub : Ioi 0 ⊆ ProbabilityTheory.integrableExpSet (fun θ ↦ -L θ) μ := fun t ht ↦
    ProbabilityTheory.integrable_exp_mul_of_le t (-c) (le_of_lt ht) hL.neg
      (hc.mono fun _ h ↦ neg_le_neg h)
  have h := (ProbabilityTheory.integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (mem_interior.2 ⟨Ioi 0, hsub, isOpen_Ioi, inv_pos.2 hlam⟩) 1).neg
  simpa only [pow_one, Pi.neg_def, neg_mul, neg_neg, smul_eq_mul, ← div_eq_inv_mul,
    mul_comm] using h

end MeasureTheory.Measure
