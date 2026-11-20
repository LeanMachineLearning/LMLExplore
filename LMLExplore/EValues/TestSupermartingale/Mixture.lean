/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.TestSupermartingale.LikelihoodRatio
public import LMLExplore.EValues.TestSupermartingale.Predictor
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Mixtures of likelihood ratio processes and Bayes factors

A family of alternatives `θ ↦ Q θ`, given by a kernel, and a prior `π` on the parameters give the
mixture `Q ∘ₘ π`. Against a simple null `{P}` and for a filtration `ℱ`, the likelihood ratio
process of the mixture is the Bayes factor of the alternative with prior `π` against `P`. Under
local absolute continuity, the mixture over `π` of the likelihood ratio processes
`((Q θ).trim (ℱ.le n)).rnDeriv (P.trim (ℱ.le n))` is the likelihood ratio process of the
mixture, and a test martingale for `P`; without it, the mixture of the likelihood ratio processes
is still a test supermartingale [HRMS21, Lemma 2; Rob70; RW, §3.7, §7.5].

In the sequential form of `ProbabilityTheory.isTestSupermartingale_prod_of_hasCondLaw`, the
alternatives are sequential predictors with densities `q θ k ω` with respect to the conditional
laws `κ k ω` of the observations `X k` given `ℱ k`, and their likelihood ratios are the products
`∏ k < n, q θ k ω (X k ω)`. Their mixture over `π` is the likelihood ratio of a single sequential
predictor, the Bayesian one, whose prediction of round `k` has the *posterior predictive density*
`ProbabilityTheory.posteriorPredictive π q X k ω`: the average of the densities `q θ k ω` under
the posterior of `π` given the observations before round `k`, the measure with density
proportional to `θ ↦ ∏ j < k, q θ j ω (X j ω)` with respect to `π`. This is the chain rule of
Bayesian mixtures: the product of the posterior predictive densities at the observations is the
mixture of the likelihood ratios. The mixture is a test supermartingale, and a test martingale
when the alternatives are probability predictions. No independence, no identical distribution
and no dominating measure are assumed.

## Main statements

* `ProbabilityTheory.isTestMartingale_rnDeriv_trim_comp`: the likelihood ratio process of the
  mixture `Q ∘ₘ π` (a Bayes factor against a simple null) is a test martingale under local
  absolute continuity.
* `ProbabilityTheory.isTestMartingale_lintegral_of_ae_eq_rnDeriv_trim`: the mixture over `π` of
  the likelihood ratio processes of the `Q θ` is a test martingale, equal to the likelihood ratio
  process of the mixture (`MeasureTheory.Measure.rnDeriv_trim_bind_ae_eq`).
* `ProbabilityTheory.isTestSupermartingale_lintegral_of_ae_eq_rnDeriv_trim`: without absolute
  continuity, the mixture of the likelihood ratio processes is a test supermartingale.
* `ProbabilityTheory.isTestSupermartingale_lintegral_prod_of_hasCondLaw`,
  `ProbabilityTheory.isTestMartingale_lintegral_prod_of_hasCondLaw`: the mixture of the
  likelihood ratios of sequential predictors is a test supermartingale, and a test martingale for
  probability predictions.
* `ProbabilityTheory.prod_posteriorPredictive`,
  `ProbabilityTheory.ae_prod_posteriorPredictive_eq`: the mixture is the likelihood ratio of the
  predictor of the posterior predictive densities.
* `ProbabilityTheory.lintegral_posteriorPredictive`,
  `ProbabilityTheory.lintegral_posteriorPredictive_le`,
  `ProbabilityTheory.lintegral_posteriorPredictive_eq_one`,
  `ProbabilityTheory.isTestSupermartingale_prod_posteriorPredictive`: the posterior predictive
  densities integrate to the weighted mixture divided by the mixture, so they are sub-probability
  densities, probability densities where the mixture is positive and finite, and their likelihood
  ratio is a test supermartingale.
* `ProbabilityTheory.not_isEVar_rnDeriv_boolKernel_comp`: with a prior on a composite null, a
  Bayes factor need not be an e-variable for the null [RW, §6.6].

## References

* [HRMS21] S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, *Time-uniform, nonparametric,
  nonasymptotic confidence sequences*, Annals of Statistics 49 (2021), arXiv:1810.08240.
* [Rob70] H. Robbins, *Statistical methods related to the law of the iterated logarithm*,
  Annals of Mathematical Statistics 41 (1970).
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614.
-/

public section

open MeasureTheory Set Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω Θ : Type*} {mΩ : MeasurableSpace Ω} {mΘ : MeasurableSpace Θ} {ℱ : Filtration ℕ mΩ}
  {P : Measure Ω} {π : Measure Θ}

/-! ### Mixtures of likelihood ratio processes -/

section LikelihoodRatio

variable {Q : Kernel Θ Ω}

/-- **Bayes factors against a simple null are test martingales** [HRMS21, Lemma 2; Rob70]. For a
probability measure `π` and a kernel `Q` of measures of mass at most `1` whose restrictions to
each `ℱ n` are, for `π`-almost every `θ`, absolutely continuous with respect to that of `P`, the
likelihood ratio process of the mixture `Q ∘ₘ π` against `P` is a test martingale for `P`. -/
theorem isTestMartingale_rnDeriv_trim_comp [SigmaFiniteFiltration P ℱ] [IsProbabilityMeasure π]
    (hQ : ∀ θ, Q θ univ ≤ 1) (hQP : ∀ n, ∀ᵐ θ ∂π, (Q θ).trim (ℱ.le n) ≪ P.trim (ℱ.le n)) :
    IsTestMartingale (fun n ↦ ((Q ∘ₘ π).trim (ℱ.le n)).rnDeriv (P.trim (ℱ.le n))) ℱ {P} := by
  refine isTestMartingale_rnDeriv_trim ?_ fun n ↦
    Measure.absolutelyContinuous_trim_bind (ℱ.le n) Q.measurable (hQP n)
  rw [Measure.bind_apply .univ Q.aemeasurable]
  calc ∫⁻ θ, Q θ univ ∂π ≤ ∫⁻ _, 1 ∂π := lintegral_mono hQ
    _ = 1 := by simp

/-- **The mixture of likelihood ratio processes is the likelihood ratio process of the mixture,
a test martingale** [HRMS21, Lemma 2; Rob70]. Let `π` be a probability measure and `Q` a kernel
of measures of mass at most `1` whose restrictions to each `ℱ n` are, for `π`-almost every `θ`,
absolutely continuous with respect to that of `P`. Let `L θ` be versions of the likelihood ratio
processes of the `Q θ` against `P`, jointly measurable in `(θ, ω)` for `ℱ n` at every time `n`.
Then the mixture `∫⁻ θ, L θ n ω ∂π` is a test martingale for `P`. It is almost surely the
likelihood ratio process of the mixture `Q ∘ₘ π` (`Measure.rnDeriv_trim_bind_ae_eq`). -/
theorem isTestMartingale_lintegral_of_ae_eq_rnDeriv_trim [SigmaFiniteFiltration P ℱ]
    [IsProbabilityMeasure π] (hQ : ∀ θ, Q θ univ ≤ 1) {L : Θ → ℕ → Ω → ℝ≥0∞}
    (hL : ∀ n, Measurable[mΘ.prod (ℱ n)] fun p : Θ × Ω ↦ L p.1 n p.2)
    (hLQ : ∀ n, ∀ᵐ θ ∂π, L θ n =ᵐ[P] ((Q θ).trim (ℱ.le n)).rnDeriv (P.trim (ℱ.le n)))
    (hQP : ∀ n, ∀ᵐ θ ∂π, (Q θ).trim (ℱ.le n) ≪ P.trim (ℱ.le n)) :
    IsTestMartingale (fun n ω ↦ ∫⁻ θ, L θ n ω ∂π) ℱ {P} := by
  have : ∀ θ, IsFiniteMeasure (Q θ) := fun θ ↦ ⟨(hQ θ).trans_lt ENNReal.one_lt_top⟩
  refine (isTestMartingale_rnDeriv_trim_comp hQ hQP).congr (adapted_lintegral hL) ?_
  rintro _ rfl n
  exact Measure.rnDeriv_trim_bind_ae_eq (ℱ.le n) Q.measurable (hL n) (hLQ n) (hQP n)

/-- **Mixtures of likelihood ratio processes are test supermartingales** [RW, §7.5]. Let `π` be a
probability measure and `Q θ` measures of mass at most `1`, and let `L θ` be versions of
the likelihood ratio processes of the `Q θ` against `P`, jointly measurable in `(θ, ω)` for `ℱ n`
at every time `n`. Then the mixture `∫⁻ θ, L θ n ω ∂π` is a test supermartingale for `P`. No
absolute continuity is assumed. -/
theorem isTestSupermartingale_lintegral_of_ae_eq_rnDeriv_trim [SigmaFiniteFiltration P ℱ]
    [IsProbabilityMeasure π] {Q : Θ → Measure Ω} (hQ : ∀ θ, Q θ univ ≤ 1)
    {L : Θ → ℕ → Ω → ℝ≥0∞}
    (hL : ∀ n, Measurable[mΘ.prod (ℱ n)] fun p : Θ × Ω ↦ L p.1 n p.2)
    (hLQ : ∀ θ n, L θ n =ᵐ[P] ((Q θ).trim (ℱ.le n)).rnDeriv (P.trim (ℱ.le n))) :
    IsTestSupermartingale (fun n ω ↦ ∫⁻ θ, L θ n ω ∂π) ℱ {P} := by
  have : SigmaFinite P := SigmaFinite.of_trim (ℱ.le 0)
  refine isTestSupermartingale_lintegral
    (fun _ hP ↦ by rw [mem_singleton_iff.1 hP]; infer_instance) hL fun θ ↦
      (isTestSupermartingale_rnDeriv_trim (hQ θ)).congr
        (fun n ↦ (hL n).comp measurable_prodMk_left) ?_
  rintro _ rfl n
  exact (hLQ θ n).symm

end LikelihoodRatio

/-! ### Bayesian mixtures of sequential predictors -/

section Predictor

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {X : ℕ → Ω → 𝓧} {κ : ℕ → Ω → Measure 𝓧}
  {q : Θ → ℕ → Ω → 𝓧 → ℝ≥0∞}

/-- The **posterior predictive density** of round `k` of the Bayesian mixture over the prior `π`
of the sequential predictors with densities `q θ`: the average of the densities `q θ k ω` under
the posterior of `π` given the observations `X j ω` before round `k`, that is
`(∫⁻ θ, (∏ j < k, q θ j ω (X j ω)) * q θ k ω x ∂π) / ∫⁻ θ, ∏ j < k, q θ j ω (X j ω) ∂π`; the
denominator is the mixture of the likelihood ratios before round `k`. -/
noncomputable def posteriorPredictive (π : Measure Θ) (q : Θ → ℕ → Ω → 𝓧 → ℝ≥0∞)
    (X : ℕ → Ω → 𝓧) (k : ℕ) (ω : Ω) (x : 𝓧) : ℝ≥0∞ :=
  (∫⁻ θ, (∏ j ∈ range k, q θ j ω (X j ω)) * q θ k ω x ∂π) /
    ∫⁻ θ, ∏ j ∈ range k, q θ j ω (X j ω) ∂π

theorem posteriorPredictive_def (k : ℕ) (ω : Ω) (x : 𝓧) :
    posteriorPredictive π q X k ω x =
      (∫⁻ θ, (∏ j ∈ range k, q θ j ω (X j ω)) * q θ k ω x ∂π) /
        ∫⁻ θ, ∏ j ∈ range k, q θ j ω (X j ω) ∂π := (rfl)

/-- At round `0` the posterior is the normalised prior, so the posterior predictive density is
the average `(∫⁻ θ, q θ 0 ω x ∂π) / π univ` of the densities of round `0`. -/
@[simp]
theorem posteriorPredictive_zero (ω : Ω) (x : 𝓧) :
    posteriorPredictive π q X 0 ω x = (∫⁻ θ, q θ 0 ω x ∂π) / π univ := by
  simp [posteriorPredictive_def]

/-! The following identities hold at a fixed `ω` and only need measurability in `θ` and `x`. -/

/-- Integrating the mixture over `x` against a measure `μ` integrates out each density. -/
private lemma lintegral_lintegral_prod_range_mul [SFinite π] (μ : Measure 𝓧) [SFinite μ]
    {k : ℕ} {ω : Ω} (hL : AEMeasurable (fun θ ↦ ∏ j ∈ range k, q θ j ω (X j ω)) π)
    (hqk : Measurable fun p : Θ × 𝓧 ↦ q p.1 k ω p.2) :
    ∫⁻ x, ∫⁻ θ, (∏ j ∈ range k, q θ j ω (X j ω)) * q θ k ω x ∂π ∂μ =
      ∫⁻ θ, (∏ j ∈ range k, q θ j ω (X j ω)) * ∫⁻ x, q θ k ω x ∂μ ∂π := by
  rw [lintegral_lintegral_swap (hL.comp_snd.mul (hqk.comp measurable_swap).aemeasurable)]
  exact lintegral_congr fun θ ↦ lintegral_const_mul _ (hqk.comp measurable_prodMk_left)

/-- The integral of the posterior predictive density of round `k` at `ω` against a measure `μ`
is the mixture of the likelihood ratios weighted by the masses of the densities of round `k`,
divided by the mixture of the likelihood ratios. -/
theorem lintegral_posteriorPredictive [SFinite π] (μ : Measure 𝓧) [SFinite μ] {k : ℕ} {ω : Ω}
    (hL : AEMeasurable (fun θ ↦ ∏ j ∈ range k, q θ j ω (X j ω)) π)
    (hqk : Measurable fun p : Θ × 𝓧 ↦ q p.1 k ω p.2) :
    ∫⁻ x, posteriorPredictive π q X k ω x ∂μ =
      (∫⁻ θ, (∏ j ∈ range k, q θ j ω (X j ω)) * ∫⁻ x, q θ k ω x ∂μ ∂π) /
        ∫⁻ θ, ∏ j ∈ range k, q θ j ω (X j ω) ∂π := by
  have hx : AEMeasurable (fun x ↦ ∫⁻ θ, (∏ j ∈ range k, q θ j ω (X j ω)) * q θ k ω x ∂π) μ :=
    (hL.comp_snd.mul (hqk.comp measurable_swap).aemeasurable).lintegral_prod_right'
  simp_rw [posteriorPredictive_def, div_eq_mul_inv]
  rw [lintegral_mul_const'' _ hx, lintegral_lintegral_prod_range_mul μ hL hqk]

/-- **The posterior predictive density is a sub-probability density.** If, for `π`-almost every
`θ`, the density `q θ k ω` has total mass at most `1` with respect to a measure `μ`, then so has
the posterior predictive density of round `k` at `ω`. -/
theorem lintegral_posteriorPredictive_le [SFinite π] (μ : Measure 𝓧) [SFinite μ] {k : ℕ} {ω : Ω}
    (hL : AEMeasurable (fun θ ↦ ∏ j ∈ range k, q θ j ω (X j ω)) π)
    (hqk : Measurable fun p : Θ × 𝓧 ↦ q p.1 k ω p.2)
    (h : ∀ᵐ θ ∂π, ∫⁻ x, q θ k ω x ∂μ ≤ 1) :
    ∫⁻ x, posteriorPredictive π q X k ω x ∂μ ≤ 1 := by
  rw [lintegral_posteriorPredictive μ hL hqk]
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  exact lintegral_mono_ae (h.mono fun θ hθ ↦ mul_le_of_le_one_right' hθ)

/-- **The posterior predictive density is a probability density** where the mixture of the
likelihood ratios is positive and finite, if `π`-almost every density `q θ k ω` is a probability
density with respect to `μ`. -/
theorem lintegral_posteriorPredictive_eq_one [SFinite π] (μ : Measure 𝓧) [SFinite μ] {k : ℕ}
    {ω : Ω} (hL : AEMeasurable (fun θ ↦ ∏ j ∈ range k, q θ j ω (X j ω)) π)
    (hqk : Measurable fun p : Θ × 𝓧 ↦ q p.1 k ω p.2) (h : ∀ᵐ θ ∂π, ∫⁻ x, q θ k ω x ∂μ = 1)
    (h0 : ∫⁻ θ, ∏ j ∈ range k, q θ j ω (X j ω) ∂π ≠ 0)
    (htop : ∫⁻ θ, ∏ j ∈ range k, q θ j ω (X j ω) ∂π ≠ ∞) :
    ∫⁻ x, posteriorPredictive π q X k ω x ∂μ = 1 := by
  rw [lintegral_posteriorPredictive μ hL hqk,
    lintegral_congr_ae (g := fun θ ↦ ∏ j ∈ range k, q θ j ω (X j ω))
      (h.mono fun θ hθ ↦ by simp only [hθ, mul_one]), ENNReal.div_self h0 htop]

/-- **One step of the chain rule of Bayesian mixtures.** Where the mixture of the likelihood
ratios up to round `k` is finite, multiplying it by the posterior predictive density of round
`k` gives the mixture of the likelihood ratios extended by the density of round `k`. -/
theorem mul_posteriorPredictive {k : ℕ} {ω : Ω} (x : 𝓧)
    (hL : AEMeasurable (fun θ ↦ ∏ j ∈ range k, q θ j ω (X j ω)) π)
    (htop : ∫⁻ θ, ∏ j ∈ range k, q θ j ω (X j ω) ∂π ≠ ∞) :
    (∫⁻ θ, ∏ j ∈ range k, q θ j ω (X j ω) ∂π) * posteriorPredictive π q X k ω x =
      ∫⁻ θ, (∏ j ∈ range k, q θ j ω (X j ω)) * q θ k ω x ∂π := by
  rw [posteriorPredictive_def]
  refine ENNReal.mul_div_cancel' (fun h0 ↦ ?_) fun h ↦ absurd h htop
  rw [lintegral_eq_zero_iff' hL] at h0
  rw [lintegral_congr_ae (g := fun _ ↦ 0)
    (h0.mono fun θ hθ ↦ by simp only [Pi.zero_apply] at hθ; simp [hθ]), lintegral_zero]

/-- **The chain rule of Bayesian mixtures.** For a probability measure `π`, where the mixtures of
the likelihood ratios before time `n` are finite, the product of the posterior predictive
densities at the observations before time `n` is the mixture over `π` of the likelihood ratios
`∏ k < n, q θ k ω (X k ω)`. -/
theorem prod_posteriorPredictive [IsProbabilityMeasure π] {n : ℕ} {ω : Ω}
    (hL : ∀ k < n, AEMeasurable (fun θ ↦ ∏ j ∈ range k, q θ j ω (X j ω)) π)
    (htop : ∀ k < n, ∫⁻ θ, ∏ j ∈ range k, q θ j ω (X j ω) ∂π ≠ ∞) :
    ∏ k ∈ range n, posteriorPredictive π q X k ω (X k ω) =
      ∫⁻ θ, ∏ k ∈ range n, q θ k ω (X k ω) ∂π := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih (fun k hk ↦ hL k (by omega)) fun k hk ↦ htop k (by omega),
      mul_posteriorPredictive _ (hL n n.lt_succ_self) (htop n n.lt_succ_self)]
    simp_rw [prod_range_succ]


variable (hX : ∀ k, Measurable[ℱ (k + 1)] (X k))
  (hq : ∀ k, Measurable[mΘ.prod ((ℱ k).prod m𝓧)] fun p : Θ × Ω × 𝓧 ↦ q p.1 k p.2.1 p.2.2)
include hX hq

/-- The likelihood ratios `∏ j < n, q θ j ω (X j ω)` are jointly measurable in `(θ, ω)` for
`ℱ n`. -/
private lemma measurable_prod_range (n : ℕ) :
    Measurable[mΘ.prod (ℱ n)] fun p : Θ × Ω ↦ ∏ j ∈ range n, q p.1 j p.2 (X j p.2) := by
  refine Finset.measurable_prod _ fun j hj ↦ ?_
  have hjn : j + 1 ≤ n := mem_range.1 hj
  have hf : @Measurable (Θ × Ω) (Θ × Ω × 𝓧) (mΘ.prod (ℱ n)) (mΘ.prod ((ℱ j).prod m𝓧))
      fun p ↦ (p.1, p.2, X j p.2) :=
    (@measurable_fst Θ Ω mΘ (ℱ n)).prodMk
      (((@measurable_snd Θ Ω mΘ (ℱ n)).mono le_rfl (ℱ.mono (by omega))).prodMk
        (((hX j).mono (ℱ.mono hjn) le_rfl).comp (@measurable_snd Θ Ω mΘ (ℱ n))))
  exact (hq j).comp hf

/-- At a fixed `ω`, the likelihood ratios `∏ j < n, q θ j ω (X j ω)` are measurable in `θ`. -/
private lemma measurable_prod_range_apply (n : ℕ) (ω : Ω) :
    Measurable fun θ ↦ ∏ j ∈ range n, q θ j ω (X j ω) :=
  (measurable_prod_range hX hq n).comp (measurable_id.prodMk (measurable_const (mα := ℱ n)))

omit hX in
/-- At a fixed `ω`, the densities `q θ k ω x` are jointly measurable in `(θ, x)`. -/
private lemma measurable_uncurry_apply (k : ℕ) (ω : Ω) :
    Measurable fun p : Θ × 𝓧 ↦ q p.1 k ω p.2 :=
  (hq k).comp (measurable_fst.prodMk ((measurable_const (mα := ℱ k)).prodMk measurable_snd))

/-- The integrand `(θ, (ω, x)) ↦ (∏ j < k, q θ j ω (X j ω)) * q θ k ω x` is jointly measurable
for `ℱ k` and `𝓧`. -/
private lemma measurable_prod_range_mul (k : ℕ) :
    Measurable[mΘ.prod ((ℱ k).prod m𝓧)] fun p : Θ × Ω × 𝓧 ↦
      (∏ j ∈ range k, q p.1 j p.2.1 (X j p.2.1)) * q p.1 k p.2.1 p.2.2 := by
  have hf : @Measurable (Θ × Ω × 𝓧) (Θ × Ω) (mΘ.prod ((ℱ k).prod m𝓧)) (mΘ.prod (ℱ k))
      fun p ↦ (p.1, p.2.1) :=
    (@measurable_fst Θ (Ω × 𝓧) mΘ ((ℱ k).prod m𝓧)).prodMk
      ((@measurable_fst Ω 𝓧 (ℱ k) m𝓧).comp (@measurable_snd Θ (Ω × 𝓧) mΘ ((ℱ k).prod m𝓧)))
  exact ((measurable_prod_range hX hq k).comp hf).mul (hq k)

/-- The mixture `(ω, x) ↦ ∫⁻ θ, (∏ j < k, q θ j ω (X j ω)) * q θ k ω x ∂π` is jointly measurable
for `ℱ k` and `𝓧`. -/
private lemma measurable_lintegral_prod_range_mul [SFinite π] (k : ℕ) :
    Measurable[(ℱ k).prod m𝓧] fun p : Ω × 𝓧 ↦
      ∫⁻ θ, (∏ j ∈ range k, q θ j p.1 (X j p.1)) * q θ k p.1 p.2 ∂π := by
  -- `Measurable.lintegral_prod_left'` takes the σ-algebra of `Ω × 𝓧` as an instance
  let _ : MeasurableSpace (Ω × 𝓧) := (ℱ k).prod m𝓧
  exact (measurable_prod_range_mul hX hq k).lintegral_prod_left'

/-- The posterior predictive density of round `k` is jointly measurable for `ℱ k` and `𝓧`. -/
theorem measurable_posteriorPredictive [SFinite π] (k : ℕ) :
    Measurable[(ℱ k).prod m𝓧] (Function.uncurry (posteriorPredictive π q X k)) := by
  have hden : Measurable[(ℱ k).prod m𝓧] fun p : Ω × 𝓧 ↦
      ∫⁻ θ, ∏ j ∈ range k, q θ j p.1 (X j p.1) ∂π :=
    (adapted_lintegral (f := ℱ) (π := π) (M := fun θ n ω ↦ ∏ j ∈ range n, q θ j ω (X j ω))
      (measurable_prod_range hX hq) k).comp
      (@measurable_fst Ω 𝓧 (ℱ k) m𝓧)
  simp_rw [Function.uncurry_def, posteriorPredictive_def]
  exact (measurable_lintegral_prod_range_mul hX hq k).div hden

omit m𝓧 hX hq in
/-- The mixture over a probability measure of the likelihood ratios is `1` at time `0`. -/
private lemma lintegral_lintegral_prod_range_zero [IsProbabilityMeasure P]
    [IsProbabilityMeasure π] : ∫⁻ ω, ∫⁻ θ, ∏ k ∈ range 0, q θ k ω (X k ω) ∂π ∂P = 1 := by
  simp

/-- Over an `ℱ n`-measurable set, the mixture of the likelihood ratios at time `n + 1` integrates
as the mixture at time `n` weighted by the masses of the densities of round `n`. -/
private lemma setLIntegral_lintegral_prod_range_succ [SFinite π] [∀ k ω, SFinite (κ k ω)]
    (hκ : ∀ k, HasCondLaw (X k) (κ k) (ℱ k) P) {n : ℕ} {s : Set Ω}
    (hs : MeasurableSet[ℱ n] s) :
    ∫⁻ ω in s, ∫⁻ θ, ∏ k ∈ range (n + 1), q θ k ω (X k ω) ∂π ∂P =
      ∫⁻ ω in s, ∫⁻ θ, (∏ k ∈ range n, q θ k ω (X k ω)) * ∫⁻ x, q θ n ω x ∂(κ n ω) ∂π ∂P := by
  simp_rw [prod_range_succ]
  rw [(hκ n).setLIntegral_comp (g := fun ω x ↦
      ∫⁻ θ, (∏ k ∈ range n, q θ k ω (X k ω)) * q θ n ω x ∂π) (ℱ.le n)
    (measurable_lintegral_prod_range_mul hX hq n) hs]
  exact lintegral_congr fun ω ↦ lintegral_lintegral_prod_range_mul _
    (measurable_prod_range_apply hX hq n ω).aemeasurable (measurable_uncurry_apply hq n ω)

/-- **Bayesian mixtures of sequential predictors are test supermartingales** [RW, §3.7, §7.5].
Let `X k` be `ℱ (k + 1)`-measurable with conditional law `κ k` given `ℱ k` under the probability
measure `P`, and let `q θ k ω` be densities with respect to `κ k ω`, jointly measurable in
`θ`, `ω` (for `ℱ k`) and `x`, of total mass at most `1` for almost every `ω` and `π`-almost every
`θ`. Then the mixture over the probability measure `π` of the likelihood ratios,
`∫⁻ θ, ∏ k < n, q θ k ω (X k ω) ∂π`, is a test supermartingale for `P`. -/
theorem isTestSupermartingale_lintegral_prod_of_hasCondLaw [IsProbabilityMeasure P]
    [IsProbabilityMeasure π] [∀ k ω, SFinite (κ k ω)] (hκ : ∀ k, HasCondLaw (X k) (κ k) (ℱ k) P)
    (hq1 : ∀ k, ∀ᵐ ω ∂P, ∀ᵐ θ ∂π, ∫⁻ x, q θ k ω x ∂(κ k ω) ≤ 1) :
    IsTestSupermartingale (fun n ω ↦ ∫⁻ θ, ∏ k ∈ range n, q θ k ω (X k ω) ∂π) ℱ {P} := by
  refine ⟨⟨adapted_lintegral (M := fun θ n ω ↦ ∏ k ∈ range n, q θ k ω (X k ω))
    (measurable_prod_range hX hq), ?_⟩, ?_⟩
  · rintro _ rfl n s hs
    rw [setLIntegral_lintegral_prod_range_succ hX hq hκ hs]
    exact lintegral_mono_ae (ae_restrict_of_ae ((hq1 n).mono fun ω hω ↦
      lintegral_mono_ae (hω.mono fun θ hθ ↦ mul_le_of_le_one_right' hθ)))
  · rintro _ rfl
    exact lintegral_lintegral_prod_range_zero.le

/-- **Bayesian mixtures of probability predictors are test martingales** [RW, §3.7, §7.5;
HRMS21, Lemma 2]. Let `X k` be `ℱ (k + 1)`-measurable with conditional law `κ k` given `ℱ k`
under the probability measure `P`, and let `q θ k ω` be probability densities with respect to
`κ k ω` for almost every `ω` and `π`-almost every `θ`, jointly measurable in `θ`, `ω` (for `ℱ k`)
and `x`. Then the mixture over the probability measure `π` of the likelihood ratios,
`∫⁻ θ, ∏ k < n, q θ k ω (X k ω) ∂π`, is a test martingale for `P`. -/
theorem isTestMartingale_lintegral_prod_of_hasCondLaw [IsProbabilityMeasure P]
    [IsProbabilityMeasure π] [∀ k ω, SFinite (κ k ω)] (hκ : ∀ k, HasCondLaw (X k) (κ k) (ℱ k) P)
    (hq1 : ∀ k, ∀ᵐ ω ∂P, ∀ᵐ θ ∂π, ∫⁻ x, q θ k ω x ∂(κ k ω) = 1) :
    IsTestMartingale (fun n ω ↦ ∫⁻ θ, ∏ k ∈ range n, q θ k ω (X k ω) ∂π) ℱ {P} := by
  refine ⟨adapted_lintegral (M := fun θ n ω ↦ ∏ k ∈ range n, q θ k ω (X k ω))
    (measurable_prod_range hX hq), ?_, ?_⟩
  · rintro _ rfl
    exact lintegral_lintegral_prod_range_zero.le
  · rintro _ rfl n s hs
    rw [setLIntegral_lintegral_prod_range_succ hX hq hκ hs]
    exact lintegral_congr_ae (ae_restrict_of_ae ((hq1 n).mono fun ω hω ↦
      lintegral_congr_ae (hω.mono fun θ hθ ↦ by simp only [hθ, mul_one])))

/-- **The Bayesian mixture is the likelihood ratio of the posterior predictive predictor.** Under
the hypotheses of `isTestSupermartingale_lintegral_prod_of_hasCondLaw`, almost surely, at every
time `n`, the product of the posterior predictive densities at the observations before `n` is the
mixture over `π` of the likelihood ratios `∏ k < n, q θ k ω (X k ω)`. -/
theorem ae_prod_posteriorPredictive_eq [IsProbabilityMeasure P] [IsProbabilityMeasure π]
    [∀ k ω, SFinite (κ k ω)] (hκ : ∀ k, HasCondLaw (X k) (κ k) (ℱ k) P)
    (hq1 : ∀ k, ∀ᵐ ω ∂P, ∀ᵐ θ ∂π, ∫⁻ x, q θ k ω x ∂(κ k ω) ≤ 1) :
    ∀ᵐ ω ∂P, ∀ n, ∏ k ∈ range n, posteriorPredictive π q X k ω (X k ω) =
      ∫⁻ θ, ∏ k ∈ range n, q θ k ω (X k ω) ∂π := by
  filter_upwards [(isTestSupermartingale_lintegral_prod_of_hasCondLaw hX hq hκ hq1).ae_lt_top
    (mem_singleton P)] with ω hω n
  exact prod_posteriorPredictive (fun k _ ↦ (measurable_prod_range_apply hX hq k ω).aemeasurable)
    fun k _ ↦ (hω k).ne

/-- **The likelihood ratio of the posterior predictive predictor is a test supermartingale.**
Under the hypotheses of `isTestSupermartingale_lintegral_prod_of_hasCondLaw`, the product of the
posterior predictive densities at the observations, `∏ k < n, posteriorPredictive π q X k ω
(X k ω)`, is a test supermartingale for `P`: the posterior predictive densities are the
predictions of a sequential predictor. -/
theorem isTestSupermartingale_prod_posteriorPredictive [IsProbabilityMeasure P]
    [IsProbabilityMeasure π] [∀ k ω, SFinite (κ k ω)] (hκ : ∀ k, HasCondLaw (X k) (κ k) (ℱ k) P)
    (hq1 : ∀ k, ∀ᵐ ω ∂P, ∀ᵐ θ ∂π, ∫⁻ x, q θ k ω x ∂(κ k ω) ≤ 1) :
    IsTestSupermartingale
      (fun n ω ↦ ∏ k ∈ range n, posteriorPredictive π q X k ω (X k ω)) ℱ {P} :=
  isTestSupermartingale_prod_of_hasCondLaw hX hκ (measurable_posteriorPredictive hX hq)
    fun k ↦ (hq1 k).mono fun ω hω ↦ lintegral_posteriorPredictive_le _
      (measurable_prod_range_apply hX hq k ω).aemeasurable (measurable_uncurry_apply hq k ω) hω

end Predictor

/-! ### Bayes factors with a prior on a composite null -/

section CompositeNull

open Measure in
/-- **A Bayes factor with a prior on a composite null need not be an e-variable** [RW, §6.6]. On
`Bool`, for the null `{dirac false, dirac true}` with the uniform prior, whose mixture is
`Kernel.boolKernel (dirac false) (dirac true) ∘ₘ π`, the Bayes factor of the alternative
`dirac true` is `2` at `true`, so that its expectation under the member `dirac true` of the null
is `2`: it is not an e-variable for the null, although it is the likelihood ratio of two
probability measures and its expectation under the mixture of the null is `1`. -/
theorem not_isEVar_rnDeriv_boolKernel_comp :
    ¬ IsEVar ((dirac true).rnDeriv (Kernel.boolKernel (dirac false) (dirac true) ∘ₘ
      ((2⁻¹ : ℝ≥0∞) • (dirac false + dirac true)))) {dirac false, dirac true} := by
  set N : Measure Bool := Kernel.boolKernel (dirac false) (dirac true) ∘ₘ
    ((2⁻¹ : ℝ≥0∞) • (dirac false + dirac true))
  set f : Bool → ℝ≥0∞ := fun b ↦ if b then 2 else 0
  have hN (b : Bool) : N {b} = 2⁻¹ := by
    simp only [N, boolKernel_comp_measure]
    cases b <;> simp
  have : IsFiniteMeasure N := by
    have hU : (univ : Set Bool) = {false} ∪ {true} := by ext b; cases b <;> simp
    refine ⟨?_⟩
    rw [hU, measure_union (by simp) (measurableSet_singleton true), hN, hN]
    simp
  -- the alternative has the density `f` with respect to the mixture of the null
  have hQ : (dirac true : Measure Bool) = N.withDensity f := by
    refine ext_iff_singleton.2 fun b ↦ ?_
    rw [withDensity_apply _ (measurableSet_singleton b), lintegral_singleton, hN]
    cases b <;> simp [f, ENNReal.mul_inv_cancel]
  have hB : (dirac true).rnDeriv N =ᵐ[N] f := by
    rw [hQ]
    exact rnDeriv_withDensity N .of_discrete
  have hBtrue : (dirac true).rnDeriv N true = 2 := by
    by_contra hne
    have h0 : N {b | (dirac true).rnDeriv N b ≠ f b} = 0 := ae_iff.1 hB
    exact (by simp [hN] : N {true} ≠ 0) (measure_mono_null (by simpa [f] using hne) h0)
  intro hE
  have h := hE.lintegral_le_one (μ := dirac true) (by simp)
  rw [lintegral_dirac, hBtrue] at h
  norm_num at h

end CompositeNull

end ProbabilityTheory
