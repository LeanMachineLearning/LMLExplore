/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.ScaleFamily
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import LMLExplore.InformationTheory.KullbackLeibler.Domination
import LMLExplore.Probability.Distributions.Gaussian.Polar
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Statlib.ForMathlib.InformationTheory.KullbackLeibler.EIntegral
import TauCeti.Analysis.Normed.Module.Normalize.Measurable

/-!
# The Bayesian t-test is GROW

The t-test observes `Y` in a finite-dimensional real inner product space `E` (for the classical
test, `E = ℝⁿ`). The null hypothesis is the Gaussian scale family `{N(0, σ² I) : σ > 0}`,
`tTestNull E '' Set.Ioi 0`. The alternative at scale `σ`, `tTestAlt W v σ`, is the law of
`σ (δ v + Z)` for an effect size `δ` drawn from a prior `W`, a mean direction `v` and a standard
Gaussian vector `Z` independent of `δ`.

Let `D = KL(Q^M ‖ P^M)` be the relative entropy between the laws of the direction `Y / ‖Y‖` under
the alternative and under the null; both laws are the same at every scale. The likelihood ratio
`T = dQ^M/dP^M (Y / ‖Y‖)` of the direction is the Bayes factor of the Bayesian t-test, which mixes
the alternative and the null over the scale with the right Haar prior `dσ / σ` [GdHK24]; here it
is used in its direction form, and that identity is not formalized. This file proves that `T` is
GROW: it maximizes the worst-case growth `inf_{σ > 0} E_{Q_σ} [log X]` among all
e-variables `X` for the null, with value `D`, as soon as the prior has a logarithmic moment,
`∫ log (1 + |δ|) dW < ∞`, and that `D` is then finite. [GdHK24, Theorem 2] and [PLdHG24,
Theorem 2, Corollary 3] assume a moment of positive order of `W` [EVR26, Note 29].

## Main definitions

* `ProbabilityTheory.tTestNull E σ`: the Gaussian law `N(0, σ² I)` on `E`.
* `ProbabilityTheory.tTestAlt W v σ`: the law of `σ (δ v + Z)` for `δ ∼ W` and `Z ∼ N(0, I)`.

## Main statements

* `ProbabilityTheory.iInf_eintegral_log_tTestAlt_le`: every e-variable `X` for the null has
  `inf_{σ > 0} E_{Q_σ} [log X] ≤ D`.
* `ProbabilityTheory.exists_eintegral_eintegral_log_tTestAlt_le`: for every `ε > 0` there is a
  prior `ρ` on the log-scale with `∫ E_{Q_{e^t}} [log X] ρ(dt) ≤ D + ε` for every e-variable `X`.
* `ProbabilityTheory.isEVar_rnDeriv_normalize_tTestNull`,
  `ProbabilityTheory.eintegral_log_rnDeriv_normalize_tTestAlt`: the Bayes factor `T` is an
  e-variable with `E_{Q_σ} [log T] = D` for every `σ > 0`.
* `ProbabilityTheory.isGreatest_iInf_eintegral_log_tTestAlt`: `D` is the largest worst-case growth
  of an e-variable for the null, attained by `T`.
* `ProbabilityTheory.klDiv_map_normalize_tTestAlt_ne_top`: `D < ∞`.
* `ProbabilityTheory.map_normalize_tTestNull`, `ProbabilityTheory.map_normalize_tTestAlt`: the law
  of the direction does not depend on the scale.
* `ProbabilityTheory.integrable_log_norm_tTestAlt`: under a logarithmic moment of `W`,
  `log ‖Y‖` is integrable under the alternative.

## Implementation notes

The t-test is the scale family of `LMLExplore.EValues.ScaleFamily` in the log-polar coordinates
`y ↦ (log ‖y‖, y / ‖y‖)`, with left inverse `(u, m) ↦ e^u m`. The log-radius of a standard
Gaussian vector is independent of its direction
(`LMLExplore.map_log_norm_prod_normalize_stdGaussian`), so the null at scale `σ` is
`scaleNull ν π₀ (log σ)` with `ν` the law of `log ‖Z‖` and `π₀` the law of `Z / ‖Z‖`, and the
alternative at scale `σ` is `scaleAlt Q (log σ)` with `Q` the law of the log-polar coordinates of
`δ v + Z`. The moment condition of the scale family asks for `E |log ‖δ v + Z‖| < ∞`: the
positive part is at most `log (1 + |δ|) + log (1 + ‖v‖) + ‖Z‖`, and the negative part has an
expectation bounded uniformly in `δ` (`LMLExplore.exists_lintegral_ofReal_neg_log_norm_add_le`).

The bound `D < ∞` follows the note: the law of the direction of `δ v + Z` is at most
`K (1 + |δ| ‖v‖)^(d - 1)` times the law of the direction of `Z`
(`LMLExplore.exists_map_normalize_add_le`), so the joint law of `(δ, Y / ‖Y‖)` under the
alternative has a density bounded by that factor with respect to `W ⊗ P^M`. Its relative entropy
is at most the expected logarithm of the factor, which is finite under the logarithmic moment,
and `D` is at most that relative entropy by the data-processing inequality.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 29, and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research
  (`Results/TTestGrow.lean`, `Results/TTestGrowAux.lean`), 2026.
* [GdHK24] P. Grünwald, R. de Heide and W. M. Koolen, *Safe testing*, J. R. Stat. Soc. Ser. B 86
  (2024), arXiv:1906.07801.
* [PLdHG24] M. F. Pérez-Ortiz, T. Lardy, R. de Heide and P. Grünwald, *E-statistics, group
  invariance and anytime-valid testing*, Ann. Statist. 52 (2024).
-/

public section

open MeasureTheory InformationTheory TauCeti
open scoped ENNReal

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The null and the alternatives -/

variable (E) in
/-- The null of the t-test at scale `σ`: the Gaussian law `N(0, σ² I)` on `E`, the law of `σ Z`
for a standard Gaussian vector `Z`. The null hypothesis is `tTestNull E '' Set.Ioi 0`. -/
noncomputable def tTestNull (σ : ℝ) : Measure E := (stdGaussian E).map (σ • ·)

omit [BorelSpace E] in
theorem tTestNull_def (σ : ℝ) : tTestNull E σ = (stdGaussian E).map (σ • ·) := (rfl)

/-- The alternative of the t-test at scale `σ`, with prior `W` on the effect size and mean
direction `v`: the law of `σ (δ v + Z)` for `δ ∼ W` and a standard Gaussian vector `Z`
independent of `δ`. For `E = ℝⁿ` and `v = (1, …, 1)` it is `∫ N(σ δ v, σ² I) W(dδ)`. -/
noncomputable def tTestAlt (W : Measure ℝ) (v : E) (σ : ℝ) : Measure E :=
  (W.prod (stdGaussian E)).map fun p ↦ σ • (p.1 • v + p.2)

omit [BorelSpace E] in
theorem tTestAlt_def (W : Measure ℝ) (v : E) (σ : ℝ) :
    tTestAlt W v σ = (W.prod (stdGaussian E)).map fun p ↦ σ • (p.1 • v + p.2) := (rfl)

instance (σ : ℝ) : IsProbabilityMeasure (tTestNull E σ) := by
  rw [tTestNull_def]
  infer_instance

instance (W : Measure ℝ) [IsProbabilityMeasure W] (v : E) (σ : ℝ) :
    IsProbabilityMeasure (tTestAlt W v σ) := by
  rw [tTestAlt_def]
  infer_instance

/-- The alternative at scale `σ` is the image of the alternative at scale `1` by `y ↦ σ y`. -/
theorem tTestAlt_eq_map (W : Measure ℝ) (v : E) (σ : ℝ) :
    tTestAlt W v σ = (tTestAlt W v 1).map (σ • ·) := by
  rw [tTestAlt_def, tTestAlt_def, Measure.map_map (measurable_const_smul σ) (by fun_prop)]
  congr 1
  ext p
  simp

/-- The law of the direction is the same under every member of the null. -/
theorem map_normalize_tTestNull {σ : ℝ} (hσ : 0 < σ) :
    (tTestNull E σ).map NormedSpace.normalize = (stdGaussian E).map NormedSpace.normalize := by
  rw [tTestNull_def, Measure.map_map measurable_normalize (measurable_const_smul σ)]
  congr 1
  ext z
  exact NormedSpace.normalize_smul_of_pos hσ z

/-- The law of the direction is the same under every alternative. -/
theorem map_normalize_tTestAlt (W : Measure ℝ) (v : E) {σ : ℝ} (hσ : 0 < σ) :
    (tTestAlt W v σ).map NormedSpace.normalize = (tTestAlt W v 1).map NormedSpace.normalize := by
  rw [tTestAlt_eq_map W v σ, Measure.map_map measurable_normalize (measurable_const_smul σ)]
  congr 1
  ext z
  exact NormedSpace.normalize_smul_of_pos hσ z

/-- The law of the direction under the alternative is absolutely continuous with respect to its
law under the null. -/
theorem map_normalize_tTestAlt_absolutelyContinuous (W : Measure ℝ) (v : E) :
    (tTestAlt W v 1).map NormedSpace.normalize ≪ (stdGaussian E).map NormedSpace.normalize := by
  obtain ⟨K, -, hbound⟩ := LMLExplore.exists_map_normalize_add_le (E := E)
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 ↦ ?_
  have hF : Measurable fun p : ℝ × E ↦ (1 : ℝ) • (p.1 • v + p.2) := by fun_prop
  rw [Measure.map_apply measurable_normalize hs, tTestAlt_def,
    Measure.map_apply hF (measurable_normalize hs),
    Measure.prod_apply (hF (measurable_normalize hs))]
  refine (lintegral_congr fun δ ↦ ?_).trans lintegral_zero
  have h := Measure.absolutelyContinuous_of_le_smul (hbound (δ • v)) h0
  rw [Measure.map_apply (by fun_prop) hs] at h
  convert h using 2
  ext z
  simp

/-! ### The Bayes factor -/

/-- **The Bayes factor of the t-test is an e-variable.** The likelihood ratio
`T = dQ^M/dP^M (Y / ‖Y‖)` of the direction is an e-variable for the Gaussian null. -/
theorem isEVar_rnDeriv_normalize_tTestNull (W : Measure ℝ) [IsProbabilityMeasure W] (v : E) :
    IsEVar (fun y ↦ ((tTestAlt W v 1).map NormedSpace.normalize).rnDeriv
      ((stdGaussian E).map NormedSpace.normalize) (NormedSpace.normalize y))
      (tTestNull E '' Set.Ioi 0) := by
  have hr := Measure.measurable_rnDeriv ((tTestAlt W v 1).map NormedSpace.normalize)
    ((stdGaussian E).map NormedSpace.normalize)
  refine ⟨hr.comp measurable_normalize, ?_⟩
  rintro μ ⟨σ, hσ, rfl⟩
  rw [← lintegral_map hr measurable_normalize, map_normalize_tTestNull hσ]
  exact Measure.lintegral_rnDeriv_le.trans_eq measure_univ

/-- **The Bayes factor of the t-test has growth `D` at every scale.** The likelihood ratio
`T = dQ^M/dP^M (Y / ‖Y‖)` of the direction has `E_{Q_σ} [log T] = D = KL(Q^M ‖ P^M)` for every
`σ > 0`. [EVR26, Note 29] -/
theorem eintegral_log_rnDeriv_normalize_tTestAlt (W : Measure ℝ) [IsProbabilityMeasure W] (v : E)
    {σ : ℝ} (hσ : 0 < σ) :
    ∫ᵉ y, ENNReal.log (((tTestAlt W v 1).map NormedSpace.normalize).rnDeriv
      ((stdGaussian E).map NormedSpace.normalize) (NormedSpace.normalize y)) ∂(tTestAlt W v σ) =
      (klDiv ((tTestAlt W v 1).map NormedSpace.normalize)
        ((stdGaussian E).map NormedSpace.normalize) : EReal) := by
  set QM := (tTestAlt W v 1).map NormedSpace.normalize
  set PM := (stdGaussian E).map NormedSpace.normalize
  have hac : QM ≪ PM := map_normalize_tTestAlt_absolutelyContinuous W v
  have hr' : Measurable fun m ↦ ENNReal.log (QM.rnDeriv PM m) :=
    (Measure.measurable_rnDeriv _ _).ennreal_log
  have h_ae : (fun m ↦ (llr QM PM m : EReal)) =ᵐ[QM] fun m ↦ ENNReal.log (QM.rnDeriv PM m) := by
    filter_upwards [Measure.rnDeriv_pos hac, hac.ae_le (Measure.rnDeriv_lt_top QM PM)]
      with m h0 htop
    rw [ENNReal.log_pos_real h0.ne' htop.ne, llr]
  rw [← eintegral_map hr' measurable_normalize, map_normalize_tTestAlt W v hσ,
    coe_klDiv_eq_eintegral_llr_of_measure_eq hac (by simp), eintegral_congr_ae h_ae]

/-! ### The reduction to a scale family in log-polar coordinates -/

section LogPolar

/-- Log-polar coordinates `y ↦ (log ‖y‖, y / ‖y‖)`. -/
private noncomputable def logPolar (y : E) : ℝ × E := (Real.log ‖y‖, NormedSpace.normalize y)

/-- The left inverse `(u, m) ↦ e^u m` of the log-polar coordinates. -/
private noncomputable def expPolar (x : ℝ × E) : E := Real.exp x.1 • x.2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma expPolar_logPolar (y : E) : expPolar (logPolar y) = y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [expPolar, logPolar]
  · rw [expPolar, logPolar, Real.exp_log (norm_pos_iff.mpr hy), NormedSpace.norm_smul_normalize]

omit [FiniteDimensional ℝ E] in
private lemma measurable_logPolar : Measurable (logPolar : E → ℝ × E) := by
  unfold logPolar
  fun_prop

private lemma measurable_expPolar : Measurable (expPolar : ℝ × E → E) := by
  unfold expPolar
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma logPolar_smul {σ : ℝ} (hσ : 0 < σ) {y : E} (hy : y ≠ 0) :
    logPolar (σ • y) = ((logPolar y).1 + Real.log σ, (logPolar y).2) := by
  rw [logPolar, logPolar, norm_smul, Real.norm_of_nonneg hσ.le,
    Real.log_mul hσ.ne' (norm_ne_zero_iff.mpr hy), add_comm, NormedSpace.normalize_smul_of_pos hσ]

/-- The law of the direction under the alternative is the second marginal of its log-polar
coordinates. -/
private lemma snd_map_logPolar_tTestAlt (W : Measure ℝ) (v : E) :
    ((tTestAlt W v 1).map logPolar).snd = (tTestAlt W v 1).map NormedSpace.normalize := by
  rw [Measure.snd, Measure.map_map measurable_snd measurable_logPolar]
  rfl

/-- The log-radius has a first moment under the null. -/
private lemma integrable_id_map_log_norm_stdGaussian :
    Integrable id ((stdGaussian E).map fun z ↦ Real.log ‖z‖) :=
  (integrable_map_measure aestronglyMeasurable_id (by fun_prop)).mpr
    LMLExplore.integrable_log_norm_stdGaussian

variable [Nontrivial E]

/-- In log-polar coordinates, the null at scale `σ` is `scaleNull ν π₀ (log σ)`, with `ν` the law
of `log ‖Z‖` and `π₀` the law of the direction of `Z`. -/
private lemma map_logPolar_tTestNull {σ : ℝ} (hσ : 0 < σ) :
    (tTestNull E σ).map logPolar = scaleNull ((stdGaussian E).map fun z ↦ Real.log ‖z‖)
      ((stdGaussian E).map NormedSpace.normalize) (Real.log σ) := by
  have h_ae : (logPolar ∘ (σ • ·)) =ᵐ[stdGaussian E]
      (fun x : ℝ × E ↦ (x.1 + Real.log σ, x.2)) ∘ logPolar := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : E))] with z hz
    exact logPolar_smul hσ hz
  rw [tTestNull_def, Measure.map_map measurable_logPolar (measurable_const_smul σ),
    Measure.map_congr h_ae, ← Measure.map_map (by fun_prop) measurable_logPolar]
  have h : (stdGaussian E).map logPolar = _ := LMLExplore.map_log_norm_prod_normalize_stdGaussian
  rw [h, scaleNull_def, ← Measure.map_id (μ := (stdGaussian E).map NormedSpace.normalize),
    Measure.map_prod_map _ _ (measurable_add_const _) measurable_id, Measure.map_id]
  rfl

/-- The alternative at scale `1` has no atom at `0`. -/
private lemma tTestAlt_singleton_zero (W : Measure ℝ) (v : E) : tTestAlt W v 1 {0} = 0 := by
  have hF : Measurable fun p : ℝ × E ↦ (1 : ℝ) • (p.1 • v + p.2) := by fun_prop
  rw [tTestAlt_def, Measure.map_apply hF (measurableSet_singleton 0),
    Measure.prod_apply (hF (measurableSet_singleton 0))]
  have h (δ : ℝ) : Prod.mk δ ⁻¹' ((fun p : ℝ × E ↦ (1 : ℝ) • (p.1 • v + p.2)) ⁻¹' {0}) =
      {-(δ • v)} := by
    ext z
    simp [eq_neg_iff_add_eq_zero, add_comm]
  simp_rw [h, measure_singleton, lintegral_zero]

/-- In log-polar coordinates, the alternative at scale `σ` is `scaleAlt Q (log σ)`, with `Q` the
image of the alternative at scale `1`. -/
private lemma map_logPolar_tTestAlt (W : Measure ℝ) (v : E) {σ : ℝ} (hσ : 0 < σ) :
    (tTestAlt W v σ).map logPolar = scaleAlt ((tTestAlt W v 1).map logPolar) (Real.log σ) := by
  have h_ae : (logPolar ∘ (σ • ·)) =ᵐ[tTestAlt W v 1]
      (fun x : ℝ × E ↦ (x.1 + Real.log σ, x.2)) ∘ logPolar := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (tTestAlt_singleton_zero W v)] with y hy
    exact logPolar_smul hσ hy
  rw [tTestAlt_eq_map, Measure.map_map measurable_logPolar (measurable_const_smul σ),
    Measure.map_congr h_ae, ← Measure.map_map (by fun_prop) measurable_logPolar, scaleAlt_def]

/-- An e-variable for the null of the t-test, read in log-polar coordinates, is an e-variable for
the null of the scale family. -/
private lemma isEVar_comp_expPolar {X : E → ℝ≥0∞} (hX : IsEVar X (tTestNull E '' Set.Ioi 0)) :
    IsEVar (fun x ↦ X (expPolar x)) (Set.range (scaleNull
      ((stdGaussian E).map fun z ↦ Real.log ‖z‖) ((stdGaussian E).map NormedSpace.normalize))) := by
  have hXm : Measurable fun x ↦ X (expPolar x) := hX.measurable.comp measurable_expPolar
  refine ⟨hXm, ?_⟩
  rintro μ ⟨t, rfl⟩
  have h := map_logPolar_tTestNull (E := E) (Real.exp_pos t)
  rw [Real.log_exp] at h
  rw [← h, lintegral_map hXm measurable_logPolar]
  simp_rw [expPolar_logPolar]
  exact hX.lintegral_le_one ⟨Real.exp t, Real.exp_pos t, rfl⟩

/-- The expected logarithm under the alternative of the t-test, in log-polar coordinates. -/
private lemma eintegral_log_tTestAlt (W : Measure ℝ) (v : E) {X : E → ℝ≥0∞} (hX : Measurable X)
    {σ : ℝ} (hσ : 0 < σ) :
    ∫ᵉ y, ENNReal.log (X y) ∂(tTestAlt W v σ) =
      ∫ᵉ x, ENNReal.log (X (expPolar x))
        ∂(scaleAlt ((tTestAlt W v 1).map logPolar) (Real.log σ)) := by
  rw [← map_logPolar_tTestAlt W v hσ, eintegral_map (f := fun x ↦ ENNReal.log (X (expPolar x)))
    (hX.comp measurable_expPolar).ennreal_log measurable_logPolar]
  simp_rw [expPolar_logPolar]

end LogPolar

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `|log ‖δ v + z‖| ≤ log (1 + |δ|) + log (1 + ‖v‖) + ‖z‖ + (log ‖δ v + z‖)⁻`: the positive part
of the logarithm is at most `log (1 + ‖δ v + z‖)`, and
`1 + ‖δ v + z‖ ≤ (1 + |δ|) (1 + ‖v‖) (1 + ‖z‖)`. -/
private lemma abs_log_norm_smul_add_le (δ : ℝ) (v z : E) :
    |Real.log ‖δ • v + z‖| ≤ Real.log (1 + |δ|) + Real.log (1 + ‖v‖) + ‖z‖ +
      max 0 (-Real.log ‖δ • v + z‖) := by
  set r := ‖δ • v + z‖ with hr_def
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr : r ≤ |δ| * ‖v‖ + ‖z‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
  have h1 : Real.log (1 + r) ≤ Real.log (1 + |δ|) + Real.log (1 + ‖v‖) + ‖z‖ := by
    have hz := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + ‖z‖)
    calc Real.log (1 + r) ≤ Real.log ((1 + |δ|) * (1 + ‖v‖) * (1 + ‖z‖)) := by
          refine Real.log_le_log (by positivity) ?_
          nlinarith [abs_nonneg δ, norm_nonneg v, norm_nonneg z,
            mul_nonneg (abs_nonneg δ) (norm_nonneg v),
            mul_nonneg (mul_nonneg (abs_nonneg δ) (norm_nonneg v)) (norm_nonneg z)]
    _ = Real.log (1 + |δ|) + Real.log (1 + ‖v‖) + Real.log (1 + ‖z‖) := by
          rw [Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity)]
    _ ≤ _ := by linarith
  have h2 : Real.log r ≤ Real.log (1 + r) := by
    rcases hr0.eq_or_lt with h | h
    · rw [← h, Real.log_zero]
      exact Real.log_nonneg (by linarith)
    · exact Real.log_le_log h (by linarith)
  have h3 : 0 ≤ Real.log (1 + r) := Real.log_nonneg (by linarith)
  have h4 := le_max_left 0 (-Real.log r)
  have h5 := le_max_right 0 (-Real.log r)
  rw [abs_le]
  constructor <;> linarith

/-- The logarithm of the norm of the observation is integrable under the alternative at scale `1`
as soon as the prior `W` on the effect size has a logarithmic moment. -/
theorem integrable_log_norm_tTestAlt (W : Measure ℝ) [IsProbabilityMeasure W] (v : E)
    (hW : Integrable (fun δ ↦ Real.log (1 + |δ|)) W) :
    Integrable (fun y ↦ Real.log ‖y‖) (tTestAlt W v 1) := by
  have hF : Measurable fun p : ℝ × E ↦ (1 : ℝ) • (p.1 • v + p.2) := by fun_prop
  rw [tTestAlt_def, integrable_map_measure (g := fun y : E ↦ Real.log ‖y‖)
    (Real.measurable_log.comp measurable_norm).aestronglyMeasurable hF.aemeasurable]
  simp only [Function.comp_def, one_smul]
  have hlog : Measurable fun p : ℝ × E ↦ Real.log ‖p.1 • v + p.2‖ := by fun_prop
  have hpos : Integrable (fun p : ℝ × E ↦ Real.log (1 + |p.1|) + Real.log (1 + ‖v‖) + ‖p.2‖)
      (W.prod (stdGaussian E)) :=
    ((hW.comp_fst _).add (integrable_const _)).add
      ((IsGaussian.integrable_id (μ := stdGaussian E)).norm.comp_snd _)
  have hneg : Integrable (fun p : ℝ × E ↦ max 0 (-Real.log ‖p.1 • v + p.2‖))
      (W.prod (stdGaussian E)) := by
    obtain ⟨K, hK, hbound⟩ := LMLExplore.exists_lintegral_ofReal_neg_log_norm_add_le (E := E)
    refine ⟨(measurable_const.max hlog.neg).aestronglyMeasurable, ?_⟩
    have h_eq (p : ℝ × E) : ‖max 0 (-Real.log ‖p.1 • v + p.2‖)‖ₑ =
        ENNReal.ofReal (-Real.log ‖p.1 • v + p.2‖) := by
      rw [Real.eNorm_eq_ofReal_abs, abs_of_nonneg (le_max_left _ _), ENNReal.ofReal_max,
        ENNReal.ofReal_zero, zero_max]
    simp_rw [HasFiniteIntegral, h_eq]
    rw [lintegral_prod (fun p : ℝ × E ↦ ENNReal.ofReal (-Real.log ‖p.1 • v + p.2‖))
      (ENNReal.measurable_ofReal.comp hlog.neg).aemeasurable]
    calc ∫⁻ δ, ∫⁻ z, ENNReal.ofReal (-Real.log ‖(δ, z).1 • v + (δ, z).2‖) ∂stdGaussian E ∂W
        ≤ ∫⁻ _, K ∂W := lintegral_mono fun δ ↦ hbound (δ • v)
    _ < ∞ := by simpa using hK.lt_top
  exact (hpos.add hneg).mono' hlog.aestronglyMeasurable (ae_of_all _ fun p ↦ by
    rw [Real.norm_eq_abs]
    exact abs_log_norm_smul_add_le p.1 v p.2)

/-! ### The GROW bound -/

omit [BorelSpace E] in
/-- In dimension zero an e-variable for the null is a constant at most `1`. -/
private lemma le_one_of_isEVar_tTestNull [Subsingleton E] {X : E → ℝ≥0∞}
    (hX : IsEVar X (tTestNull E '' Set.Ioi 0)) (y : E) : X y ≤ 1 := by
  have hc (z : E) : X z = X y := congrArg X (Subsingleton.elim z y)
  have h := hX.lintegral_le_one ⟨1, one_pos, rfl⟩
  simpa [hc] using h

/-- **The averaged bound for the t-test.** Let `W` be a prior on the effect size with a
logarithmic moment. For every `ε > 0` there is a prior `ρ` on the log-scale `t = log σ` such that
every e-variable `X` for the Gaussian null satisfies `∫ E_{Q_{e^t}} [log X] ρ(dt) ≤ D + ε`, where
`D` is the relative entropy of the laws of the direction. The prior does not depend on `X`.
[EVR26, Note 29] -/
theorem exists_eintegral_eintegral_log_tTestAlt_le (W : Measure ℝ) [IsProbabilityMeasure W]
    (v : E) (hW : Integrable (fun δ ↦ Real.log (1 + |δ|)) W) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
      ∀ X : E → ℝ≥0∞, IsEVar X (tTestNull E '' Set.Ioi 0) →
        ∫ᵉ t, ∫ᵉ y, ENNReal.log (X y) ∂(tTestAlt W v (Real.exp t)) ∂ρ ≤
          (klDiv ((tTestAlt W v 1).map NormedSpace.normalize)
            ((stdGaussian E).map NormedSpace.normalize) : EReal) + ε := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- in dimension zero, `X` is a constant at most `1`
    refine ⟨Measure.dirac 0, inferInstance, fun X hX ↦ ?_⟩
    have hc (y : E) : X y = X 0 := congrArg X (Subsingleton.elim y 0)
    calc ∫ᵉ t, ∫ᵉ y, ENNReal.log (X y) ∂(tTestAlt W v (Real.exp t)) ∂Measure.dirac 0
        = ENNReal.log (X 0) := by simp [hc, eintegral_const]
    _ ≤ 0 := ENNReal.log_le_zero_iff.mpr (le_one_of_isEVar_tTestNull hX 0)
    _ ≤ _ := add_nonneg (EReal.coe_ennreal_nonneg _) (EReal.coe_nonneg.mpr hε.le)
  have hQ : Integrable Prod.fst ((tTestAlt W v 1).map logPolar) :=
    (integrable_map_measure measurable_fst.aestronglyMeasurable
      measurable_logPolar.aemeasurable).mpr (integrable_log_norm_tTestAlt W v hW)
  obtain ⟨ρ, hρ, h⟩ := exists_eintegral_eintegral_log_scaleAlt_le _
    ((stdGaussian E).map NormedSpace.normalize) _
    (integrable_id_map_log_norm_stdGaussian (E := E)) hQ hε
  refine ⟨ρ, hρ, fun X hX ↦ ?_⟩
  have h' := h _ (isEVar_comp_expPolar hX)
  rw [snd_map_logPolar_tTestAlt] at h'
  refine le_of_eq_of_le (eintegral_congr fun t ↦ ?_) h'
  rw [eintegral_log_tTestAlt W v hX.measurable (Real.exp_pos t), Real.log_exp]

/-- **The GROW bound for the t-test.** Let `W` be a prior on the effect size with a logarithmic
moment, `∫ log (1 + |δ|) W(dδ) < ∞`. Every e-variable `X` for the Gaussian null
`{N(0, σ² I) : σ > 0}` satisfies `inf_{σ > 0} E_{Q_σ} [log X] ≤ D`, where `Q_σ` is the
alternative and `D = KL(Q^M ‖ P^M)` is the relative entropy of the laws of the direction
`Y / ‖Y‖` under the alternative and under the null. [EVR26, Note 29] -/
theorem iInf_eintegral_log_tTestAlt_le (W : Measure ℝ) [IsProbabilityMeasure W] (v : E)
    (hW : Integrable (fun δ ↦ Real.log (1 + |δ|)) W) {X : E → ℝ≥0∞}
    (hX : IsEVar X (tTestNull E '' Set.Ioi 0)) :
    ⨅ σ > 0, ∫ᵉ y, ENNReal.log (X y) ∂(tTestAlt W v σ) ≤
      (klDiv ((tTestAlt W v 1).map NormedSpace.normalize)
        ((stdGaussian E).map NormedSpace.normalize) : EReal) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- in dimension zero, `X` is a constant at most `1`
    have hc (y : E) : X y = X 0 := congrArg X (Subsingleton.elim y 0)
    calc ⨅ σ > 0, ∫ᵉ y, ENNReal.log (X y) ∂(tTestAlt W v σ)
        ≤ ∫ᵉ y, ENNReal.log (X y) ∂(tTestAlt W v 1) := iInf₂_le 1 one_pos
    _ = ENNReal.log (X 0) := by simp [hc, eintegral_const]
    _ ≤ 0 := ENNReal.log_le_zero_iff.mpr (le_one_of_isEVar_tTestNull hX 0)
    _ ≤ _ := EReal.coe_ennreal_nonneg _
  have hQ : Integrable Prod.fst ((tTestAlt W v 1).map logPolar) :=
    (integrable_map_measure measurable_fst.aestronglyMeasurable
      measurable_logPolar.aemeasurable).mpr (integrable_log_norm_tTestAlt W v hW)
  have h := iInf_eintegral_log_scaleAlt_le _ _ _
    (integrable_id_map_log_norm_stdGaussian (E := E)) hQ
    (isEVar_comp_expPolar hX)
  rw [snd_map_logPolar_tTestAlt] at h
  refine le_trans (le_iInf fun t ↦ ?_) h
  refine (iInf₂_le (Real.exp t) (Real.exp_pos t)).trans_eq ?_
  rw [eintegral_log_tTestAlt W v hX.measurable (Real.exp_pos t), Real.log_exp]

/-- **The Bayes factor of the t-test is GROW.** If the prior `W` on the effect size has a
logarithmic moment, then `D = KL(Q^M ‖ P^M)` is the largest worst-case growth
`inf_{σ > 0} E_{Q_σ} [log X]` of an e-variable `X` for the Gaussian null, and the Bayes factor
`T = dQ^M/dP^M (Y / ‖Y‖)` attains it. [EVR26, Note 29] -/
theorem isGreatest_iInf_eintegral_log_tTestAlt (W : Measure ℝ) [IsProbabilityMeasure W] (v : E)
    (hW : Integrable (fun δ ↦ Real.log (1 + |δ|)) W) :
    IsGreatest {r | ∃ X, IsEVar X (tTestNull E '' Set.Ioi 0) ∧
      r = ⨅ σ > 0, ∫ᵉ y, ENNReal.log (X y) ∂(tTestAlt W v σ)}
      (klDiv ((tTestAlt W v 1).map NormedSpace.normalize)
        ((stdGaussian E).map NormedSpace.normalize) : EReal) := by
  refine ⟨⟨_, isEVar_rnDeriv_normalize_tTestNull W v, ?_⟩, ?_⟩
  · refine le_antisymm (le_iInf₂ fun σ hσ ↦ ?_) ?_
    · exact (eintegral_log_rnDeriv_normalize_tTestAlt W v hσ).ge
    · exact (iInf₂_le 1 one_pos).trans (eintegral_log_rnDeriv_normalize_tTestAlt W v one_pos).le
  · rintro r ⟨X, hX, rfl⟩
    exact iInf_eintegral_log_tTestAlt_le W v hW hX

/-! ### Finiteness of the GROW value -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Under a logarithmic moment of `W`, `δ ↦ log (K (1 + |δ| ‖v‖)^n)` is integrable, since
`log (1 + |δ| ‖v‖) ≤ log (1 + |δ|) + log (1 + ‖v‖)`. -/
private lemma integrable_log_mul_one_add_abs_mul_pow (W : Measure ℝ) [IsProbabilityMeasure W]
    (v : E) (hW : Integrable (fun δ ↦ Real.log (1 + |δ|)) W) {K : ℝ} (hK : 0 < K) (n : ℕ) :
    Integrable (fun δ ↦ Real.log (K * (1 + |δ| * ‖v‖) ^ n)) W := by
  refine (((integrable_const (|Real.log K| + n * Real.log (1 + ‖v‖))).add
    (hW.const_mul n))).mono' (Real.measurable_log.comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun δ ↦ ?_)
  have hδv : 0 ≤ |δ| * ‖v‖ := mul_nonneg (abs_nonneg δ) (norm_nonneg v)
  have h1 : 0 ≤ Real.log (1 + |δ| * ‖v‖) := Real.log_nonneg (by linarith)
  have h2 : Real.log (1 + |δ| * ‖v‖) ≤ Real.log (1 + |δ|) + Real.log (1 + ‖v‖) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (by nlinarith [abs_nonneg δ, norm_nonneg v])
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.log_mul hK.ne' (by positivity), Real.log_pow, Real.norm_eq_abs]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (mul_nonneg hn0 h1)]
  have h3 := mul_le_mul_of_nonneg_left h2 hn0
  simp only [Pi.add_apply]
  linarith

/-- **The relative entropy of the directions is finite.** If the prior `W` on the effect size has
a logarithmic moment, then `D = KL(Q^M ‖ P^M) < ∞`. [EVR26, Note 29] -/
theorem klDiv_map_normalize_tTestAlt_ne_top (W : Measure ℝ) [IsProbabilityMeasure W] (v : E)
    (hW : Integrable (fun δ ↦ Real.log (1 + |δ|)) W) :
    klDiv ((tTestAlt W v 1).map NormedSpace.normalize)
      ((stdGaussian E).map NormedSpace.normalize) ≠ ∞ := by
  obtain ⟨K, hK, hbound⟩ := LMLExplore.exists_map_normalize_add_le (E := E)
  set n := Module.finrank ℝ E - 1
  set PM := (stdGaussian E).map NormedSpace.normalize
  have hF : Measurable fun p : ℝ × E ↦ (p.1, NormedSpace.normalize (p.1 • v + p.2)) := by
    fun_prop
  -- the joint law `R` of the effect size and the direction under the alternative
  set R := (W.prod (stdGaussian E)).map fun p ↦ (p.1, NormedSpace.normalize (p.1 • v + p.2))
  have hR_snd : R.map Prod.snd = (tTestAlt W v 1).map NormedSpace.normalize := by
    rw [Measure.map_map measurable_snd hF, tTestAlt_def,
      Measure.map_map measurable_normalize (by fun_prop)]
    congr 1
    ext p
    simp
  have hR_fst : R.map Prod.fst = W := by
    rw [Measure.map_map measurable_fst hF]
    exact Measure.map_fst_prod.trans (by simp)
  set g : ℝ → ℝ := fun δ ↦ Real.log (K * (1 + |δ| * ‖v‖) ^ n)
  have hg_meas : Measurable g := Real.measurable_log.comp (by fun_prop)
  have hg_exp (δ : ℝ) : Real.exp (g δ) = K * (1 + |δ| * ‖v‖) ^ n := Real.exp_log (by positivity)
  -- `R` has a density at most `e^{g δ}` with respect to `W ⊗ P^M`
  have hle : R ≤ (W.prod PM).withDensity fun p ↦ ENNReal.ofReal (Real.exp (g p.1)) := by
    rw [← prod_withDensity_left (f := fun δ ↦ ENNReal.ofReal (Real.exp (g δ))) (by fun_prop)]
    refine Measure.le_iff.mpr fun s hs ↦ ?_
    rw [Measure.map_apply hF hs, Measure.prod_apply (hF hs), Measure.prod_apply hs,
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (measurable_measure_prodMk_left hs)]
    refine lintegral_mono fun δ ↦ ?_
    have h := hbound (δ • v) (Prod.mk δ ⁻¹' s)
    rw [Measure.map_apply (by fun_prop) (measurable_prodMk_left hs), FunLike.coe_smul,
      Pi.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs] at h
    simp only [Pi.mul_apply]
    rw [hg_exp]
    exact h
  have hg_int : Integrable g W := integrable_log_mul_one_add_abs_mul_pow W v hW hK n
  have hKL : (klDiv R (W.prod PM) : EReal) ≤ ((∫ δ, g δ ∂W : ℝ) : EReal) := by
    refine (coe_klDiv_le_eintegral_of_le_withDensity hle).trans_eq ?_
    rw [← eintegral_eq_integral hg_int, ← hR_fst,
      eintegral_map (f := fun δ ↦ (g δ : EReal)) (by fun_prop) measurable_fst]
  have h_lt : klDiv R (W.prod PM) ≠ ∞ := by
    intro h
    rw [h, EReal.coe_ennreal_top] at hKL
    exact EReal.coe_ne_top _ (top_le_iff.mp hKL)
  have hP_snd : (W.prod PM).map Prod.snd = PM := by simp
  rw [← hR_snd, ← hP_snd]
  exact ne_top_of_le_ne_top h_lt (klDiv_map_le _ _ measurable_snd)

end ProbabilityTheory
