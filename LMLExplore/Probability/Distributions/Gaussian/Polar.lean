/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import LMLExplore.MeasureTheory.Constructions.HaarToSphere
import TauCeti.Probability.Distributions.Uniform.Sphere.Basic
import TauCeti.Probability.Distributions.Chi.Moments

/-!
# The radius and the direction of a standard Gaussian vector

For a standard Gaussian vector `Z` in a finite-dimensional real inner product space `E` of
dimension `d`, this file studies the logarithm of the norm `log ‖Z‖` and the direction
`Z / ‖Z‖` (Mathlib's `NormedSpace.normalize`), together with their behaviour under a shift
`Z ↦ c + Z`. These are the log-polar coordinates in which the Gaussian scale family
`{N(0, σ² I) : σ > 0}` becomes a location family in the log-radius, independent of the direction.

## Main statements

* `LMLExplore.stdGaussian_absolutelyContinuous_volume`,
  `LMLExplore.volume_absolutelyContinuous_stdGaussian`: the standard Gaussian law and Lebesgue
  measure are equivalent; in positive dimension the Gaussian law has no atoms.
* `LMLExplore.map_log_norm_prod_normalize_stdGaussian`: `log ‖Z‖` and `Z / ‖Z‖` are independent.
* `LMLExplore.integrable_log_norm_stdGaussian`: `log ‖Z‖` is integrable.
* `LMLExplore.exists_lintegral_ofReal_neg_log_norm_add_le`: the negative part of `log ‖c + Z‖`
  has an expectation bounded uniformly in the shift `c`.
* `LMLExplore.exists_map_normalize_add_le`: the law of the direction of `c + Z` is at most
  `K (1 + ‖c‖)^(d - 1)` times the law of the direction of `Z`, for a constant `K` that depends
  only on the dimension.

## Implementation notes

The independence is Tau Ceti's polar factorization
`TauCeti.Probability.stdGaussian_map_sphereDirection_prod_norm` (the norm, of chi law, is
independent of the uniform direction). The integrability of `log ‖Z‖` comes from the moments
`E ‖Z‖^(± 1/2) < ∞` of the chi law. The uniform bound on the negative part uses that the Gaussian
density is at most its value at the origin, and at least `e^{-1/2}` times that value on the unit
ball. The bound on the law of the direction of `c + Z` is computed in polar coordinates
(`TauCeti.lintegral_eq_lintegral_toSphere_lintegral_Ioi`): at a direction `u` its density is
`∫_0^∞ r^(d-1) φ(r u - c) dr / ∫_0^∞ r^(d-1) φ(r u) dr`, with `φ` the Gaussian density, and
`‖r u - c‖ ≥ |r - ‖c‖|`.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 29, and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026.
-/

public section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped ENNReal

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable (E) in
/-- The standard Gaussian law is absolutely continuous with respect to Lebesgue measure. -/
theorem stdGaussian_absolutelyContinuous_volume : stdGaussian E ≪ volume := by
  rw [stdGaussian_eq_withDensity_norm E]
  exact withDensity_absolutelyContinuous _ _

variable (E) in
/-- Lebesgue measure is absolutely continuous with respect to the standard Gaussian law. -/
theorem volume_absolutelyContinuous_stdGaussian : (volume : Measure E) ≪ stdGaussian E := by
  rw [stdGaussian_eq_withDensity_norm E]
  exact withDensity_absolutelyContinuous' (by fun_prop)
    (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (by positivity)).ne')

/-- In positive dimension, a standard Gaussian vector has no atoms. -/
instance [Nontrivial E] : NullSingletonClass (stdGaussian E) :=
  ⟨fun c ↦ stdGaussian_absolutelyContinuous_volume E (measure_singleton c)⟩

/-- **The log-radius and the direction of a standard Gaussian vector are independent.** -/
theorem map_log_norm_prod_normalize_stdGaussian [Nontrivial E] :
    (stdGaussian E).map (fun z ↦ (Real.log ‖z‖, NormedSpace.normalize z)) =
      ((stdGaussian E).map fun z ↦ Real.log ‖z‖).prod
        ((stdGaussian E).map NormedSpace.normalize) := by
  obtain ⟨e⟩ : Nonempty (Metric.sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  have h0 : ∀ᵐ x ∂stdGaussian E, x ≠ 0 := measure_eq_zero_iff_ae_notMem.mp (measure_singleton 0)
  have hΦ : Measurable fun x : E ↦ (sphereDirection e x, ‖x‖) :=
    (measurable_sphereDirection e).prodMk measurable_norm
  have hψ : Measurable fun p : Metric.sphere (0 : E) 1 × ℝ ↦ (Real.log p.2, (p.1 : E)) := by
    fun_prop
  have := isProbabilityMeasure_chiMeasure (Nat.cast_nonneg (Module.finrank ℝ E)) one_pos
  have h1 : (stdGaussian E).map (fun z ↦ (Real.log ‖z‖, NormedSpace.normalize z)) =
      ((uniformSphereMeasure E).prod (chiMeasure (Module.finrank ℝ E) 1)).map
        fun p ↦ (Real.log p.2, (p.1 : E)) := by
    rw [← stdGaussian_map_sphereDirection_prod_norm e, Measure.map_map hψ hΦ]
    refine Measure.map_congr ?_
    filter_upwards [h0] with x hx
    simp [coe_sphereDirection_of_ne_zero e hx]
  have hν : (stdGaussian E).map (fun z ↦ Real.log ‖z‖) =
      (chiMeasure (Module.finrank ℝ E) 1).map Real.log := by
    rw [← stdGaussian_map_norm E, Measure.map_map Real.measurable_log measurable_norm,
      Function.comp_def]
  have hπ : (stdGaussian E).map NormedSpace.normalize = (uniformSphereMeasure E).map (↑) := by
    rw [← stdGaussian_map_sphereDirection e,
      Measure.map_map measurable_subtypeVal (measurable_sphereDirection e)]
    refine Measure.map_congr ?_
    filter_upwards [h0] with x hx
    simp [coe_sphereDirection_of_ne_zero e hx]
  rw [h1, hν, hπ, Measure.map_prod_map _ _ Real.measurable_log measurable_subtypeVal,
    ← Measure.prod_swap, Measure.map_map (by fun_prop) measurable_swap]
  have h_comp : (fun p : Metric.sphere (0 : E) 1 × ℝ ↦ (Real.log p.2, (p.1 : E))) ∘ Prod.swap =
      Prod.map Real.log Subtype.val := by
    ext p <;> simp
  rw [h_comp]

/-- The logarithm of the norm of a standard Gaussian vector is integrable. -/
theorem integrable_log_norm_stdGaussian :
    Integrable (fun z ↦ Real.log ‖z‖) (stdGaussian E) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [Subsingleton.elim _ (0 : E)]
  have hd : (1 : ℝ) ≤ Module.finrank ℝ E := Nat.one_le_cast.mpr Module.finrank_pos
  have hd0 : (0 : ℝ) < Module.finrank ℝ E := by linarith
  have h_chi : Integrable Real.log (chiMeasure (Module.finrank ℝ E) 1) := by
    have h1 : Integrable (fun r : ℝ ↦ r ^ (1 / 2 : ℝ)) (chiMeasure (Module.finrank ℝ E) 1) :=
      (integrable_rpow_chiMeasure_iff hd0 one_pos _).mpr (by linarith)
    have h2 : Integrable (fun r : ℝ ↦ r ^ (-(1 / 2) : ℝ)) (chiMeasure (Module.finrank ℝ E) 1) :=
      (integrable_rpow_chiMeasure_iff hd0 one_pos _).mpr (by linarith)
    refine ((h1.const_mul 2).add (h2.const_mul 2)).mono'
      Real.measurable_log.aestronglyMeasurable ?_
    filter_upwards [ae_pos_chiMeasure hd0] with r hr
    -- `|log r| ≤ 2 r^{1/2} + 2 r^{-1/2}`, from `log x ≤ x - 1` at `x = r^{± 1/2}`
    have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hr (1 / 2 : ℝ))
    have h2 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hr (-(1 / 2) : ℝ))
    rw [Real.log_rpow hr] at h1 h2
    have h3 := Real.rpow_pos_of_pos hr (1 / 2 : ℝ)
    have h4 := Real.rpow_pos_of_pos hr (-(1 / 2) : ℝ)
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  rw [← stdGaussian_map_norm E] at h_chi
  exact (integrable_map_measure Real.measurable_log.aestronglyMeasurable
    measurable_norm.aemeasurable).mp h_chi

/-- The negative part of the logarithm of the norm is Lebesgue integrable: on the unit ball, where
it is supported, the Gaussian density is at least `κ = C e^{-1/2}`, so the Lebesgue integral is at
most `κ⁻¹` times the Gaussian expectation, which is finite. -/
private lemma lintegral_ofReal_neg_log_norm_ne_top :
    ∫⁻ z : E, ENNReal.ofReal (-Real.log ‖z‖) ≠ ∞ := by
  set C : ℝ := (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) with hC
  have hC0 : 0 < C := Real.rpow_pos_of_pos (by positivity) _
  set φ : E → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (C * Real.exp (-‖x‖ ^ 2 / 2)) with hφ_def
  have hφ : Measurable φ := by fun_prop
  have hγ : stdGaussian E = volume.withDensity φ := stdGaussian_eq_withDensity_norm E
  set g : E → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (-Real.log ‖z‖) with hg_def
  have hg : Measurable g := by fun_prop
  set κ : ℝ≥0∞ := ENNReal.ofReal (C * Real.exp (-1 / 2)) with hκ_def
  have hκ0 : κ ≠ 0 := by
    rw [hκ_def, ENNReal.ofReal_ne_zero_iff]
    positivity
  -- the expectation of `g` under the Gaussian law is finite
  have hgγ : ∫⁻ z, g z ∂stdGaussian E ≠ ∞ := by
    refine ne_top_of_le_ne_top integrable_log_norm_stdGaussian.2.ne (lintegral_mono fun z ↦ ?_)
    rw [hg_def, Real.eNorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
  -- on the unit ball the density is at least `κ`, so Lebesgue measure is controlled there
  have h_vol : ∫⁻ z, g z ≤ κ⁻¹ * ∫⁻ z, g z ∂stdGaussian E := by
    rw [hγ, lintegral_withDensity_eq_lintegral_mul _ hφ hg, ← lintegral_const_mul _ (hφ.mul hg)]
    refine lintegral_mono fun z ↦ ?_
    rcases le_or_gt 1 ‖z‖ with hz | hz
    · have : -Real.log ‖z‖ ≤ 0 := neg_nonpos.mpr (Real.log_nonneg hz)
      simp [hg_def, ENNReal.ofReal_of_nonpos this]
    · have hφz : κ ≤ φ z := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC0.le)
        refine Real.exp_le_exp.mpr ?_
        have : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
        linarith
      calc g z = κ⁻¹ * κ * g z := by rw [ENNReal.inv_mul_cancel hκ0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ κ⁻¹ * (φ z * g z) := by rw [mul_assoc]; gcongr
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hκ0) hgγ) h_vol

/-- The negative part of the logarithm of the norm of a shifted standard Gaussian vector has an
expectation bounded uniformly in the shift. -/
theorem exists_lintegral_ofReal_neg_log_norm_add_le :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧
      ∀ c : E, ∫⁻ z, ENNReal.ofReal (-Real.log ‖c + z‖) ∂stdGaussian E ≤ K := by
  set C : ℝ := (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) with hC
  have hC0 : 0 < C := Real.rpow_pos_of_pos (by positivity) _
  set φ : E → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (C * Real.exp (-‖x‖ ^ 2 / 2)) with hφ_def
  have hφ : Measurable φ := by fun_prop
  have hγ : stdGaussian E = volume.withDensity φ := stdGaussian_eq_withDensity_norm E
  set g : E → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (-Real.log ‖z‖) with hg_def
  have hg : Measurable g := by fun_prop
  refine ⟨ENNReal.ofReal C * ∫⁻ z, g z,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top lintegral_ofReal_neg_log_norm_ne_top, fun c ↦ ?_⟩
  -- the density is at most `C`, and Lebesgue measure is translation invariant
  calc ∫⁻ z, ENNReal.ofReal (-Real.log ‖c + z‖) ∂stdGaussian E
      = ∫⁻ z, g (c + z) ∂(volume.withDensity φ) := by rw [hγ]
  _ = ∫⁻ z, φ z * g (c + z) :=
        lintegral_withDensity_eq_lintegral_mul _ hφ (hg.comp (measurable_const_add c))
  _ ≤ ∫⁻ z, ENNReal.ofReal C * g (c + z) := by
        refine lintegral_mono fun z ↦ ?_
        gcongr
        refine ENNReal.ofReal_le_ofReal ?_
        have : Real.exp (-‖z‖ ^ 2 / 2) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have := sq_nonneg ‖z‖
          linarith
        nlinarith
  _ = ENNReal.ofReal C * ∫⁻ z, g z := by
        rw [lintegral_const_mul (f := fun z ↦ g (c + z)) _ (hg.comp (measurable_const_add c)),
          lintegral_add_left_eq_self g c]

/-- `(1 + |t|)^n e^{-t²/2} ≤ n! e² e^{-t²/4}`. -/
private lemma one_add_abs_pow_mul_exp_le (n : ℕ) (t : ℝ) :
    (1 + |t|) ^ n * Real.exp (-t ^ 2 / 2) ≤ n.factorial * Real.exp 2 * Real.exp (-t ^ 2 / 4) := by
  have h1 : (1 + |t|) ^ n ≤ n.factorial * Real.exp (1 + |t|) := by
    have h := Real.pow_div_factorial_le_exp (1 + |t|) (by positivity) n
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  have h2 : Real.exp (1 + |t|) * Real.exp (-t ^ 2 / 2) ≤ Real.exp 2 * Real.exp (-t ^ 2 / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (|t| - 2), sq_abs t])
  calc (1 + |t|) ^ n * Real.exp (-t ^ 2 / 2)
      ≤ n.factorial * Real.exp (1 + |t|) * Real.exp (-t ^ 2 / 2) := by gcongr
  _ = n.factorial * (Real.exp (1 + |t|) * Real.exp (-t ^ 2 / 2)) := by ring
  _ ≤ n.factorial * (Real.exp 2 * Real.exp (-t ^ 2 / 4)) := by gcongr
  _ = _ := by ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Gaussian density along a ray from the origin, shifted by `c`: for a unit vector `u`,
`∫_0^∞ r^n C e^{-‖r u - c‖²/2} dr ≤ (1 + ‖c‖)^n ∫ n! e² C e^{-t²/4} dt`, since
`‖r u - c‖ ≥ |r - ‖c‖|` and `r ≤ (1 + ‖c‖) (1 + |r - ‖c‖|)`. -/
private lemma setLIntegral_pow_mul_exp_norm_sub_le (n : ℕ) {C : ℝ} (hC : 0 ≤ C) (c : E)
    (u : Metric.sphere (0 : E) 1) :
    ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) *
        ENNReal.ofReal (C * Real.exp (-‖r • (u : E) - c‖ ^ 2 / 2)) ≤
      ENNReal.ofReal ((1 + ‖c‖) ^ n) *
        ∫⁻ t, ENNReal.ofReal (n.factorial * Real.exp 2 * C * Real.exp (-(1 / 4) * t ^ 2)) := by
  set g : ℝ → ℝ := fun t ↦ n.factorial * Real.exp 2 * C * Real.exp (-(1 / 4) * t ^ 2)
  set a := ‖c‖
  have ha : 0 ≤ a := norm_nonneg c
  calc ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) *
        ENNReal.ofReal (C * Real.exp (-‖r • (u : E) - c‖ ^ 2 / 2))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal ((1 + a) ^ n) * ENNReal.ofReal (g (r - a)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun r hr ↦ ?_
        have hr0 : 0 < r := hr
        have h_norm : |r - a| ≤ ‖r • (u : E) - c‖ := by
          have h := abs_norm_sub_norm_le (r • (u : E)) c
          rwa [norm_smul, norm_eq_of_mem_sphere u, Real.norm_of_nonneg hr0.le, mul_one] at h
        have h_sq : (r - a) ^ 2 ≤ ‖r • (u : E) - c‖ ^ 2 := by
          rw [← sq_abs (r - a)]
          exact pow_le_pow_left₀ (abs_nonneg _) h_norm 2
        have h_r : r ≤ (1 + a) * (1 + |r - a|) := by
          nlinarith [le_abs_self (r - a), abs_nonneg (r - a)]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h_exp := one_add_abs_pow_mul_exp_le n (r - a)
        calc r ^ n * (C * Real.exp (-‖r • (u : E) - c‖ ^ 2 / 2))
            ≤ ((1 + a) * (1 + |r - a|)) ^ n * (C * Real.exp (-(r - a) ^ 2 / 2)) := by
              gcongr
        _ = (1 + a) ^ n * C * ((1 + |r - a|) ^ n * Real.exp (-(r - a) ^ 2 / 2)) := by
              rw [mul_pow]; ring
        _ ≤ (1 + a) ^ n * C *
              (n.factorial * Real.exp 2 * Real.exp (-(r - a) ^ 2 / 4)) := by gcongr
        _ = (1 + a) ^ n * g (r - a) := by simp only [g]; ring_nf
  _ ≤ ∫⁻ r, ENNReal.ofReal ((1 + a) ^ n) * ENNReal.ofReal (g (r - a)) :=
        setLIntegral_le_lintegral _ _
  _ = ENNReal.ofReal ((1 + a) ^ n) * ∫⁻ t, ENNReal.ofReal (g t) := by
        rw [lintegral_const_mul _ (by fun_prop),
          lintegral_sub_right_eq_self (fun t ↦ ENNReal.ofReal (g t)) a]

/-- The law of the direction of `c + Z` in polar coordinates: the mass of the directions in `s` is
the integral over the directions `u ∈ s` of `∫_0^∞ r^(d-1) φ(r u - c) dr`, with `φ` the density
of `Z`. -/
private lemma map_normalize_add_stdGaussian_apply [Nontrivial E] (c : E) {s : Set E}
    (hs : MeasurableSet s) :
    (stdGaussian E).map (fun z ↦ NormedSpace.normalize (c + z)) s =
      ∫⁻ u : Metric.sphere (0 : E) 1, s.indicator 1 (u : E) *
        (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
          ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
            Real.exp (-‖r • (u : E) - c‖ ^ 2 / 2))) ∂(volume : Measure E).toSphere := by
  set φ : E → ℝ≥0∞ := fun x ↦ ENNReal.ofReal
    ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2))
  have hφ : Measurable φ := by fun_prop
  have hnc : Measurable fun z ↦ NormedSpace.normalize (c + z) := by fun_prop
  rw [Measure.map_apply hnc hs, stdGaussian_eq_withDensity_norm E, withDensity_apply _ (hnc hs),
    ← lintegral_indicator (hnc hs),
    ← lintegral_indicator_normalize_preimage (μ := volume) (f := fun y ↦ φ (y - c))
      (hφ.comp (measurable_sub_const c)) hs,
    ← lintegral_add_left_eq_self
      (fun y ↦ (NormedSpace.normalize ⁻¹' s).indicator (fun y ↦ φ (y - c)) y) c]
  refine lintegral_congr fun z ↦ ?_
  classical
  simp only [Set.indicator_apply, Set.mem_preimage, add_sub_cancel_left, φ]

variable (E) in
/-- The radial normalizer `∫_0^∞ r^(d-1) φ(r) dr` of the standard Gaussian law on `E`, with `φ`
its density as a function of the radius. -/
private noncomputable def gaussianRadialMass : ℝ≥0∞ :=
  ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
    ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-r ^ 2 / 2))

/-- The law of the direction of `Z` in polar coordinates: the mass of the directions in `s` is the
radial normalizer times the `toSphere` measure of `s`. This is the case `c = 0` of
`map_normalize_add_stdGaussian_apply`. -/
private lemma map_normalize_stdGaussian_apply [Nontrivial E] {s : Set E} (hs : MeasurableSet s) :
    (stdGaussian E).map NormedSpace.normalize s = gaussianRadialMass E *
      ∫⁻ u : Metric.sphere (0 : E) 1, s.indicator 1 (u : E) ∂(volume : Measure E).toSphere := by
  have h := map_normalize_add_stdGaussian_apply (0 : E) hs
  simp only [zero_add, sub_zero] at h
  rw [h, ← lintegral_const_mul (f := fun u : Metric.sphere (0 : E) 1 ↦ s.indicator 1 (u : E)) _
    ((measurable_one.indicator hs).comp measurable_subtypeVal)]
  refine lintegral_congr fun u ↦ ?_
  rw [mul_comm, gaussianRadialMass]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
  rw [norm_smul, norm_eq_of_mem_sphere u, Real.norm_of_nonneg (le_of_lt hr), mul_one]

variable (E) in
/-- The radial normalizer is positive and finite, since it times the total mass of
`volume.toSphere` is the total mass `1` of the law of the direction of `Z`. -/
private lemma gaussianRadialMass_ne_zero_ne_top [Nontrivial E] :
    gaussianRadialMass E ≠ 0 ∧ gaussianRadialMass E ≠ ∞ := by
  have h1 := map_normalize_stdGaussian_apply (E := E) MeasurableSet.univ
  rw [measure_univ] at h1
  have h0 := right_ne_zero_of_mul_eq_one h1.symm
  refine ⟨left_ne_zero_of_mul_eq_one h1.symm, fun h ↦ ?_⟩
  rw [h, ENNReal.top_mul h0] at h1
  exact ENNReal.one_ne_top h1

/-- **The density of the direction of a shifted Gaussian vector.** The law of the direction of
`c + Z`, for a standard Gaussian vector `Z`, is at most `K (1 + ‖c‖)^(d - 1)` times the law of
the direction of `Z`, for a constant `K` that depends only on the dimension `d`. -/
theorem exists_map_normalize_add_le : ∃ K : ℝ, 0 < K ∧ ∀ c : E,
    (stdGaussian E).map (fun z ↦ NormedSpace.normalize (c + z)) ≤
      ENNReal.ofReal (K * (1 + ‖c‖) ^ (Module.finrank ℝ E - 1)) •
        (stdGaussian E).map NormedSpace.normalize := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨1, one_pos, fun c ↦ ?_⟩
    simp [Subsingleton.elim c 0, Module.finrank_zero_of_subsingleton]
  set n := Module.finrank ℝ E - 1
  set C : ℝ := (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) with hC
  have hC0 : 0 < C := Real.rpow_pos_of_pos (by positivity) _
  set σ := (volume : Measure E).toSphere
  set N0 := gaussianRadialMass E
  obtain ⟨hN0, hN0'⟩ := gaussianRadialMass_ne_zero_ne_top E
  set g : ℝ → ℝ := fun t ↦ n.factorial * Real.exp 2 * C * Real.exp (-(1 / 4) * t ^ 2)
  set M0 := ∫⁻ t, ENNReal.ofReal (g t)
  have hM0 : M0 ≠ ∞ :=
    ((integrable_exp_neg_mul_sq (b := 1 / 4) (by norm_num)).const_mul
      (n.factorial * Real.exp 2 * C)).lintegral_lt_top.ne
  have h_ind (s : Set E) (hs : MeasurableSet s) :
      Measurable fun u : Metric.sphere (0 : E) 1 ↦ s.indicator (1 : E → ℝ≥0∞) (u : E) :=
    (measurable_one.indicator hs).comp measurable_subtypeVal
  have hK : M0 / N0 ≤ ENNReal.ofReal ((M0 / N0).toReal + 1) := by
    rw [← ENNReal.ofReal_toReal (ENNReal.div_ne_top hM0 hN0)]
    exact ENNReal.ofReal_le_ofReal (by rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]; linarith)
  refine ⟨(M0 / N0).toReal + 1, by positivity, fun c ↦ Measure.le_iff.mpr fun s hs ↦ ?_⟩
  rw [map_normalize_add_stdGaussian_apply c hs, smul_apply, smul_eq_mul,
    map_normalize_stdGaussian_apply hs]
  -- the radial integral is at most `(1 + ‖c‖)^n M0`, since `‖r u - c‖ ≥ |r - ‖c‖|`
  calc _ ≤ ∫⁻ u : Metric.sphere (0 : E) 1, s.indicator 1 (u : E) *
        (ENNReal.ofReal ((1 + ‖c‖) ^ n) * M0) ∂σ :=
        lintegral_mono fun u ↦ by gcongr; exact setLIntegral_pow_mul_exp_norm_sub_le n hC0.le c u
  _ = ENNReal.ofReal ((1 + ‖c‖) ^ n) * (M0 / N0) *
        (N0 * ∫⁻ u : Metric.sphere (0 : E) 1, s.indicator 1 (u : E) ∂σ) := by
        rw [lintegral_mul_const _ (h_ind s hs), mul_assoc _ (M0 / N0), ← mul_assoc (M0 / N0),
          ENNReal.div_mul_cancel hN0 hN0']
        ring
  _ ≤ ENNReal.ofReal (((M0 / N0).toReal + 1) * (1 + ‖c‖) ^ n) *
        (N0 * ∫⁻ u : Metric.sphere (0 : E) 1, s.indicator 1 (u : E) ∂σ) := by
        rw [ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal _)]
        gcongr

end LMLExplore
