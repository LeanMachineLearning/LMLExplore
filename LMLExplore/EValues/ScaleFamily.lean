/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.KLInf
public import Mathlib.MeasureTheory.Group.Convolution
import LMLExplore.InformationTheory.KullbackLeibler.Domination
import LMLExplore.MeasureTheory.Group.Convolution
import LMLExplore.Probability.Distributions.Laplace
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Statlib.ForMathlib.InformationTheory.KullbackLeibler.ChainRule
import Statlib.ForMathlib.InformationTheory.KullbackLeibler.EIntegral
import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Kernel

/-!
# GROW e-variables for a scale family

A scale family is written in log-polar coordinates: the data are pairs `(u, m) ∈ ℝ × M` of a
log-radius `u` and a direction `m` in any measurable space `M`, and the group `ℝ` of log-scales acts
by `t • (u, m) = (u + t, m)`.
* The null at log-scale `t`, `scaleNull ν π₀ t`, is the law under which the log-radius is `t` plus
  a variable of law `ν`, independent of the direction, which has law `π₀`. The null hypothesis is
  `Set.range (scaleNull ν π₀)`, the composite null of all scales.
* The alternative at log-scale `t`, `scaleAlt Q t`, is the image of a fixed law `Q` of `(u, m)` by
  the shift of the log-radius by `t`. The direction has the same law `Q.snd` under every
  alternative, and the log-radius need not be independent of it.

The *GROW* criterion asks for an e-variable `X` for the composite null that maximizes the worst-case
growth `inf_t E_{Q_t} [log X]` over the alternatives [GdHK24]. Let `D = KL(Q.snd ‖ π₀)` be the
relative entropy of the laws of the direction. If the log-radius has a first moment under `ν` and
under `Q`:
* every e-variable `X` satisfies `inf_t E_{Q_t} [log X] ≤ D`;
* the likelihood ratio of the direction, `T (u, m) = dQ.snd/dπ₀ (m)`, is an e-variable with
  `E_{Q_t} [log T] = D` for every `t`, when `Q.snd ≪ π₀`.
So `T` is GROW, and the GROW value is `D`. The t-test is the case `(u, m) = (log ‖Y‖, Y / ‖Y‖)`,
with `ν` the law of `log ‖Z‖` and `π₀` the law of `Z / ‖Z‖` for a standard Gaussian vector `Z`:
there `T` is the Bayes factor of the t-test with a prior on the effect size, and the moment
condition under `Q` asks for a logarithmic moment of the prior, where [GdHK24, Theorem 2] and
[PLdHG24, Theorem 2] assume a moment of positive order [EVR26, Note 29].

The proof bounds the relative entropy between mixtures over the log-scale. For a prior `ρ` whose
translates by `u` are at most `exp (b |u|) • ρ`, as the Laplace law of rate `b` is,
`KL(∫ Q_t ρ(dt) ‖ ∫ P_t ρ(dt)) ≤ D + b (E_Q |u| + E_ν |u|)`. Every e-variable for the null is an
e-variable for the mixture of the nulls, so its expected logarithm under the mixture of the
alternatives is at most that relative entropy, and the worst case over `t` is at most the average
over `ρ`. Letting `b → 0` gives the bound `D`.

## Main definitions

* `ProbabilityTheory.scaleNull ν π₀ t`: the null of the scale family at log-scale `t`.
* `ProbabilityTheory.scaleAlt Q t`: the alternative of the scale family at log-scale `t`.

## Main statements

* `ProbabilityTheory.klDiv_bind_scaleAlt_le`: for a prior `ρ` whose translates by `u` are at most
  `exp (b |u|) • ρ`, `KL(Q_ρ ‖ P_ρ) ≤ D + b (E_Q |u| + E_ν |u|)`.
* `ProbabilityTheory.exists_eintegral_eintegral_log_scaleAlt_le`: for every `ε > 0` there is a
  prior `ρ` with `∫ E_{Q_t} [log X] ρ(dt) ≤ D + ε` for every e-variable `X`.
* `ProbabilityTheory.iInf_eintegral_log_scaleAlt_le`: `inf_t E_{Q_t} [log X] ≤ D` for every
  e-variable `X`.
* `ProbabilityTheory.isEVar_rnDeriv_snd_scaleNull`,
  `ProbabilityTheory.eintegral_log_rnDeriv_snd_scaleAlt`: the likelihood ratio `T` of the
  direction is an e-variable with `E_{Q_t} [log T] = D` for every `t`.
* `ProbabilityTheory.isGreatest_iInf_eintegral_log_scaleAlt`: `D` is the largest worst-case growth
  of an e-variable for the null, attained by `T`.

## Implementation notes

The proof follows [EVR26, Note 29], with one change that gives a better bound under weaker
hypotheses. The mixture of the alternatives is the law of `(u + t, m)` for `(u, m) ∼ Q` and
`t ∼ ρ` independent, and the mixture of the nulls is the product of the convolution `N = ρ ∗ ν`
and of `π₀`. The chain rule for a product reference measure (Statlib's
`InformationTheory.klDiv_prod_eq_klDiv_snd_add`) splits off `D`. The note then bounds the
remainder, given the direction, by the logarithm of the largest density ratio, which needs an
exponential moment of `u` under `Q`. Here the data-processing inequality first adds `u` itself to
the observation: the remainder is at most the relative entropy from the law of `(u + t, (u, m))`
to `N ⊗ Q`, whose log-likelihood ratio is at most `b |u| + b E_ν |u|`, because the translate of
`ρ` by `u` is at most `exp (b |u|) • ρ` and `N ≥ exp (-b E_ν |u|) • ρ` by Jensen's inequality
(`MeasureTheory.Measure.ofReal_mul_exp_smul_le_conv_of_forall_map_add_le`).
Only first moments are needed.

The iterated integral `∫ E_{Q_t} [log X] ρ(dt)` is the expected logarithm under the mixture,
because the positive part of `log X` has a finite expectation under the mixture, whose relative
entropy to the mixture of the nulls is finite
(`InformationTheory.lintegral_toENNReal_log_ne_top_of_klDiv_ne_top`).

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 29, and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026.
* [GdHK24] P. Grünwald, R. de Heide and W. M. Koolen, *Safe testing*, J. R. Stat. Soc. Ser. B 86
  (2024), arXiv:1906.07801.
* [PLdHG24] M. F. Pérez-Ortiz, T. Lardy, R. de Heide and P. Grünwald, *E-statistics, group
  invariance and anytime-valid testing*, Ann. Statist. 52 (2024).
-/

public section

open MeasureTheory InformationTheory
open scoped ENNReal MeasureTheory

namespace ProbabilityTheory

variable {M : Type*} {mM : MeasurableSpace M}

/-! ### The null and the alternatives -/

/-- The null of a scale family in log-polar coordinates, at log-scale `t`: the log-radius is `t`
plus an independent variable of law `ν`, and the direction has law `π₀`. The null hypothesis of
the scale family is `Set.range (scaleNull ν π₀)`. -/
noncomputable def scaleNull (ν : Measure ℝ) (π₀ : Measure M) (t : ℝ) : Measure (ℝ × M) :=
  (ν.map (· + t)).prod π₀

theorem scaleNull_def (ν : Measure ℝ) (π₀ : Measure M) (t : ℝ) :
    scaleNull ν π₀ t = (ν.map (· + t)).prod π₀ := (rfl)

/-- The alternative of a scale family in log-polar coordinates, at log-scale `t`: the image of
`Q` by the shift `(u, m) ↦ (u + t, m)` of the log-radius. -/
noncomputable def scaleAlt (Q : Measure (ℝ × M)) (t : ℝ) : Measure (ℝ × M) :=
  Q.map fun x ↦ (x.1 + t, x.2)

theorem scaleAlt_def (Q : Measure (ℝ × M)) (t : ℝ) :
    scaleAlt Q t = Q.map fun x ↦ (x.1 + t, x.2) := (rfl)

instance (ν : Measure ℝ) [IsProbabilityMeasure ν] (π₀ : Measure M) [IsProbabilityMeasure π₀]
    (t : ℝ) : IsProbabilityMeasure (scaleNull ν π₀ t) := by
  rw [scaleNull_def]
  infer_instance

instance (Q : Measure (ℝ × M)) [IsProbabilityMeasure Q] (t : ℝ) :
    IsProbabilityMeasure (scaleAlt Q t) := by
  rw [scaleAlt_def]
  infer_instance

/-- The direction has law `π₀` under every member of the null. -/
@[simp]
theorem snd_scaleNull (ν : Measure ℝ) [IsProbabilityMeasure ν] (π₀ : Measure M) [SFinite π₀]
    (t : ℝ) :
    (scaleNull ν π₀ t).snd = π₀ := by
  rw [scaleNull_def, Measure.snd_prod]

/-- The direction has the same law `Q.snd` under every alternative. -/
@[simp]
theorem snd_scaleAlt (Q : Measure (ℝ × M)) (t : ℝ) : (scaleAlt Q t).snd = Q.snd := by
  rw [scaleAlt_def, Measure.snd_map_prodMk (by fun_prop) measurable_snd, Measure.snd]

/-! ### Mixtures over the log-scale -/

/-- The alternative depends measurably on the log-scale. -/
@[fun_prop]
theorem measurable_scaleAlt (Q : Measure (ℝ × M)) [SFinite Q] : Measurable (scaleAlt Q) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  have hF : Measurable fun p : ℝ × (ℝ × M) ↦ (p.2.1 + p.1, p.2.2) := by fun_prop
  convert measurable_measure_prodMk_left (ν := Q) (hF hs) using 2 with t
  rw [scaleAlt_def, Measure.map_apply (by fun_prop) hs, Set.preimage_preimage]

/-- The null depends measurably on the log-scale. -/
@[fun_prop]
theorem measurable_scaleNull (ν : Measure ℝ) [SFinite ν] (π₀ : Measure M) [SFinite π₀] :
    Measurable (scaleNull ν π₀) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  have h (t : ℝ) : scaleNull ν π₀ t s = ∫⁻ u, π₀ (Prod.mk (u + t) ⁻¹' s) ∂ν := by
    rw [scaleNull_def, Measure.prod_apply hs,
      lintegral_map (measurable_measure_prodMk_left hs) (measurable_add_const t)]
  simp_rw [h]
  exact ((measurable_measure_prodMk_left hs).comp
    (by fun_prop : Measurable fun p : ℝ × ℝ ↦ p.2 + p.1)).lintegral_prod_right'

/-- The `ρ`-mixture of the alternatives is the law of `(u + t, m)` for `t ∼ ρ` and `(u, m) ∼ Q`
independent. -/
theorem bind_scaleAlt (Q : Measure (ℝ × M)) [SFinite Q] (ρ : Measure ℝ) :
    ρ.bind (scaleAlt Q) = (ρ.prod Q).map fun p ↦ (p.2.1 + p.1, p.2.2) := by
  have hF : Measurable fun p : ℝ × (ℝ × M) ↦ (p.2.1 + p.1, p.2.2) := by fun_prop
  ext s hs
  rw [Measure.bind_apply hs (by fun_prop), Measure.map_apply hF hs,
    Measure.prod_apply (hF hs)]
  refine lintegral_congr fun t ↦ ?_
  rw [scaleAlt_def, Measure.map_apply (by fun_prop) hs, Set.preimage_preimage]

/-- The `ρ`-mixture of the nulls is the product of the convolution `ρ ∗ ν`, the law of `t + u` for
`t ∼ ρ` and `u ∼ ν` independent, and of `π₀`. -/
theorem bind_scaleNull (ν : Measure ℝ) [SFinite ν] (π₀ : Measure M) [SFinite π₀]
    (ρ : Measure ℝ) : ρ.bind (scaleNull ν π₀) = (ρ ∗ ν).prod π₀ := by
  ext s hs
  rw [Measure.bind_apply hs (measurable_scaleNull ν π₀).aemeasurable, Measure.prod_apply hs,
    Measure.lintegral_conv (measurable_measure_prodMk_left hs)]
  refine lintegral_congr fun t ↦ ?_
  rw [scaleNull_def, Measure.prod_apply hs,
    lintegral_map (measurable_measure_prodMk_left hs) (measurable_add_const t)]
  simp_rw [add_comm t]

/-- The direction has law `Q.snd` under every mixture of the alternatives. -/
@[simp]
theorem snd_bind_scaleAlt (Q : Measure (ℝ × M)) [SFinite Q] (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] : (ρ.bind (scaleAlt Q)).snd = Q.snd := by
  ext s hs
  rw [Measure.snd_apply hs, Measure.bind_apply (measurable_snd hs)
    (measurable_scaleAlt Q).aemeasurable]
  simp_rw [← Measure.snd_apply hs, snd_scaleAlt]
  simp

/-! ### The relative entropy between the mixtures -/

section Mixture

variable {ρ : Measure ℝ} {b : ℝ}

/-- The law of `(u + t, (u, m))`, for `(u, m) ∼ Q` and `t ∼ ρ` independent, is at most
`exp (b |u| + k)` times `N ⊗ Q` if `exp (-k) • ρ ≤ N`. -/
private lemma map_prod_le_prod_withDensity
    (hρ : ∀ u, ρ.map (· + u) ≤ ENNReal.ofReal (Real.exp (b * |u|)) • ρ) [SFinite ρ]
    (Q : Measure (ℝ × M)) [SFinite Q] {N : Measure ℝ} [SFinite N] {k : ℝ}
    (hN : ENNReal.ofReal (Real.exp (-k)) • ρ ≤ N) :
    (ρ.prod Q).map (fun p ↦ (p.2.1 + p.1, p.2)) ≤
      (N.prod Q).withDensity fun p ↦ ENNReal.ofReal (Real.exp (b * |p.2.1| + k)) := by
  have hw : Measurable fun x : ℝ × M ↦ ENNReal.ofReal (Real.exp (b * |x.1| + k)) := by fun_prop
  have hG : Measurable fun p : ℝ × (ℝ × M) ↦ (p.2.1 + p.1, p.2) := by fun_prop
  rw [← prod_withDensity_right hw]
  refine Measure.le_iff.mpr fun s hs ↦ ?_
  rw [Measure.map_apply hG hs, Measure.prod_apply_symm (hG hs), Measure.prod_apply_symm hs,
    lintegral_withDensity_eq_lintegral_mul _ hw (measurable_measure_prodMk_right hs)]
  refine lintegral_mono fun x ↦ ?_
  set sx := (fun z ↦ (z, x)) ⁻¹' s
  have hsx : MeasurableSet sx := measurable_prodMk_right hs
  have h1 : ρ ((fun t ↦ (t, x)) ⁻¹' ((fun p : ℝ × (ℝ × M) ↦ (p.2.1 + p.1, p.2)) ⁻¹' s)) =
      ρ.map (· + x.1) sx := by
    rw [Measure.map_apply (measurable_add_const _) hsx]
    congr 1
    ext t
    simp [sx, add_comm]
  have h2 : ρ sx ≤ ENNReal.ofReal (Real.exp k) * N sx := by
    have h := hN sx
    rw [smul_apply, smul_eq_mul] at h
    calc ρ sx = ENNReal.ofReal (Real.exp k) * (ENNReal.ofReal (Real.exp (-k)) * ρ sx) := by
          rw [← mul_assoc]
          simp [← ENNReal.ofReal_mul, Real.exp_nonneg, ← Real.exp_add]
    _ ≤ ENNReal.ofReal (Real.exp k) * N sx := by gcongr
  have h3 := hρ x.1 sx
  rw [smul_apply, smul_eq_mul] at h3
  rw [h1]
  calc (ρ.map (· + x.1)) sx ≤ ENNReal.ofReal (Real.exp (b * |x.1|)) * ρ sx := h3
  _ ≤ ENNReal.ofReal (Real.exp (b * |x.1|)) * (ENNReal.ofReal (Real.exp k) * N sx) := by gcongr
  _ = ENNReal.ofReal (Real.exp (b * |x.1| + k)) * N sx := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]

/-- The relative entropy from the `ρ`-mixture of the alternatives, the law of `(u + t, m)`, to
`N ⊗ Q.snd` is at most `E_Q [b |u| + k]` if `exp (-k) • ρ ≤ N`. By the data-processing inequality,
it is at most the relative entropy from the law of `(u + t, (u, m))` to `N ⊗ Q`, which
`map_prod_le_prod_withDensity` bounds. -/
private lemma klDiv_map_prod_le
    (hρ : ∀ u, ρ.map (· + u) ≤ ENNReal.ofReal (Real.exp (b * |u|)) • ρ)
    [IsProbabilityMeasure ρ] (Q : Measure (ℝ × M)) [IsProbabilityMeasure Q] {N : Measure ℝ}
    [IsProbabilityMeasure N] {k : ℝ} (hb : 0 ≤ b) (hk : 0 ≤ k)
    (hN : ENNReal.ofReal (Real.exp (-k)) • ρ ≤ N) :
    klDiv ((ρ.prod Q).map (fun p ↦ (p.2.1 + p.1, p.2.2))) (N.prod Q.snd) ≤
      ∫⁻ x, ENNReal.ofReal (b * |x.1| + k) ∂Q := by
  have hG : Measurable fun p : ℝ × (ℝ × M) ↦ (p.2.1 + p.1, p.2) := by fun_prop
  have hH : Measurable fun p : ℝ × (ℝ × M) ↦ (p.1, p.2.2) := by fun_prop
  have hR : ((ρ.prod Q).map fun p ↦ (p.2.1 + p.1, p.2)).map (fun p ↦ (p.1, p.2.2)) =
      (ρ.prod Q).map (fun p ↦ (p.2.1 + p.1, p.2.2)) := by
    simp only [Measure.map_map hH hG, Function.comp_def]
  have hNQ : (N.prod Q).map (fun p ↦ (p.1, p.2.2)) = N.prod Q.snd := by
    rw [Measure.snd, ← Measure.map_id (μ := N), Measure.map_prod_map _ _ measurable_id
      measurable_snd, Measure.map_id, Prod.map_def]
    simp only [id_eq]
  rw [← hR, ← hNQ]
  refine (klDiv_map_le _ _ hH).trans ?_
  have h := coe_klDiv_le_eintegral_of_le_withDensity (map_prod_le_prod_withDensity hρ Q hN)
  rw [eintegral_eq_lintegral_of_nonneg (fun p ↦ EReal.coe_nonneg.mpr (by positivity))] at h
  simp only [EReal.real_coe_toENNReal] at h
  rw [lintegral_map (by fun_prop) hG, lintegral_prod _ (by fun_prop)] at h
  simpa using h

/-- **The relative entropy between the mixtures.** For a prior `ρ` on the log-scale whose
translate by every `u` is at most `exp (b |u|) • ρ` (for the Laplace law of rate `b`,
`π_b (t - u) ≤ exp (b |u|) π_b (t)`), the relative entropy between the `ρ`-mixtures of the
alternatives and of the nulls exceeds the relative entropy `D = KL(Q.snd ‖ π₀)` of the laws of
the direction by at most `b (E_Q |u| + E_ν |u|)`. No moment condition is needed: the bound is
infinite when a moment is. This sharpens [EVR26, Note 29, inequality (2)], which has
`log E_Q [exp (b |u|)]` in place of `b E_Q |u|`. -/
theorem klDiv_bind_scaleAlt_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (π₀ : Measure M)
    [IsFiniteMeasure π₀] (Q : Measure (ℝ × M)) [IsProbabilityMeasure Q]
    (hρ : ∀ u, ρ.map (· + u) ≤ ENNReal.ofReal (Real.exp (b * |u|)) • ρ)
    [IsProbabilityMeasure ρ] :
    klDiv (ρ.bind (scaleAlt Q)) (ρ.bind (scaleNull ν π₀)) ≤
      klDiv Q.snd π₀ + ENNReal.ofReal b * (∫⁻ x, ‖x.1‖ₑ ∂Q + ∫⁻ u, ‖u‖ₑ ∂ν) := by
  have hb : 0 ≤ b := Measure.nonneg_of_forall_map_add_le hρ
  set X := ∫⁻ x, ‖x.1‖ₑ ∂Q with hX
  set A := ∫⁻ u, ‖u‖ₑ ∂ν with hA
  by_cases htop : ENNReal.ofReal b * (X + A) = ∞
  · rw [htop, add_top]
    exact le_top
  have hfin : b = 0 ∨ A ≠ ∞ := by
    rcases hb.eq_or_lt with h | h
    · exact .inl h.symm
    · refine .inr fun hA' ↦ htop ?_
      rw [hA', add_top, ENNReal.mul_top (ENNReal.ofReal_pos.mpr h).ne']
  set k := b * A.toReal with hk
  have hk0 : 0 ≤ k := by positivity
  -- the convolution `N = ρ ∗ ν` dominates `exp (-k) • ρ`, by Jensen's inequality
  have hN : ENNReal.ofReal (Real.exp (-k)) • ρ ≤ ρ ∗ ν := by
    rcases hfin with h0 | hA'
    · simpa [hk, h0] using Measure.lintegral_smul_le_conv_of_forall_map_add_le hρ ν
    have h := Measure.ofReal_mul_exp_smul_le_conv_of_forall_map_add_le hρ
      (ν := ν) ⟨aestronglyMeasurable_id, hA'.lt_top⟩
    have h_eq : ∫ u, |u| ∂ν = A.toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun u ↦ abs_nonneg u) (by fun_prop)]
      simp_rw [hA, Real.eNorm_eq_ofReal_abs]
    rwa [probReal_univ, one_mul, average_eq_integral, h_eq] at h
  have h_pt (x : ℝ × M) :
      ENNReal.ofReal (b * |x.1| + k) = ENNReal.ofReal b * ‖x.1‖ₑ + ENNReal.ofReal k := by
    rw [ENNReal.ofReal_add (by positivity) hk0, ENNReal.ofReal_mul hb, Real.eNorm_eq_ofReal_abs]
  have : IsProbabilityMeasure (ρ.bind (scaleAlt Q)) := by
    rw [bind_scaleAlt]; infer_instance
  -- the chain rule splits off the relative entropy of the directions
  rw [bind_scaleNull, klDiv_prod_eq_klDiv_snd_add _ (ρ ∗ ν) π₀, snd_bind_scaleAlt]
  gcongr
  rw [bind_scaleAlt]
  calc _ ≤ ∫⁻ x, ENNReal.ofReal (b * |x.1| + k) ∂Q := klDiv_map_prod_le hρ Q hb hk0 hN
  _ = ENNReal.ofReal b * (X + A) := by
    simp_rw [h_pt]
    rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ (by fun_prop),
      lintegral_const, measure_univ, mul_one, mul_add]
    congr 1
    rcases hfin with h | h
    · simp [hk, h]
    · rw [hk, ENNReal.ofReal_mul hb, ENNReal.ofReal_toReal h]

end Mixture

/-! ### The GROW bound -/

/-- **The averaged bound.** If the log-radius has a first moment under `ν` and under `Q`, then
for every `ε > 0` there is a prior `ρ` on the log-scale such that every e-variable `X` for the
null satisfies `∫ E_{Q_t} [log X] ρ(dt) ≤ D + ε`, where `D` is the relative entropy of the laws of
the direction. The prior does not depend on `X`. [EVR26, Note 29] -/
theorem exists_eintegral_eintegral_log_scaleAlt_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (π₀ : Measure M) [IsProbabilityMeasure π₀] (Q : Measure (ℝ × M)) [IsProbabilityMeasure Q]
    (hν : Integrable id ν) (hQ : Integrable Prod.fst Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
      ∀ X : ℝ × M → ℝ≥0∞, IsEVar X (Set.range (scaleNull ν π₀)) →
        ∫ᵉ t, ∫ᵉ x, ENNReal.log (X x) ∂(scaleAlt Q t) ∂ρ ≤ (klDiv Q.snd π₀ : EReal) + ε := by
  set S := (∫⁻ x, ‖x.1‖ₑ ∂Q + ∫⁻ u, ‖u‖ₑ ∂ν).toReal with hS
  have hS_ne : ∫⁻ x, ‖x.1‖ₑ ∂Q + ∫⁻ u, ‖u‖ₑ ∂ν ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hQ.2.ne, hν.2.ne⟩
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  -- the Laplace prior of scale `(S + 1) / ε`, that is of rate `ε / (S + 1)`
  set s := (S + 1) / ε with hs_def
  have hs : 0 < s := div_pos (by linarith) hε
  have hbS : ENNReal.ofReal s⁻¹ * (∫⁻ x, ‖x.1‖ₑ ∂Q + ∫⁻ u, ‖u‖ₑ ∂ν) ≤ ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal hS_ne, ← ENNReal.ofReal_mul (inv_pos.mpr hs).le, ← hS]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hs_def, inv_div, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  set ρ := TauCeti.Probability.laplaceMeasure 0 s
  have hρ : IsProbabilityMeasure ρ := TauCeti.Probability.isProbabilityMeasure_laplaceMeasure hs 0
  refine ⟨ρ, hρ, fun X hX ↦ ?_⟩
  set D := klDiv Q.snd π₀
  by_cases hD : D = ∞
  · rw [hD, EReal.coe_ennreal_top, EReal.top_add_coe]
    exact le_top
  have hQmix : IsProbabilityMeasure (ρ.bind (scaleAlt Q)) := by
    rw [bind_scaleAlt]; infer_instance
  have hPmix : IsProbabilityMeasure (ρ.bind (scaleNull ν π₀)) := by
    rw [bind_scaleNull]; infer_instance
  set Qmix := ρ.bind (scaleAlt Q)
  set Pmix := ρ.bind (scaleNull ν π₀)
  have hKL : klDiv Qmix Pmix ≤ D + ENNReal.ofReal ε :=
    (klDiv_bind_scaleAlt_le ν π₀ Q (TauCeti.Probability.laplaceMeasure_map_add_le 0 s)).trans
      (by gcongr)
  -- `X` is an e-variable for the mixture of the nulls
  have hX1 : ∫⁻ x, X x ∂Pmix ≤ 1 := by
    rw [Measure.lintegral_bind (measurable_scaleNull ν π₀).aemeasurable
      hX.measurable.aemeasurable]
    calc ∫⁻ t, ∫⁻ x, X x ∂(scaleNull ν π₀ t) ∂ρ ≤ ∫⁻ _, 1 ∂ρ :=
          lintegral_mono fun t ↦ hX.lintegral_le_one ⟨t, rfl⟩
    _ = 1 := by simp
  have hX' : IsEVar X {Pmix} := ⟨hX.measurable, by rintro μ rfl; exact hX1⟩
  -- the iterated integral is the expected logarithm under the mixture
  have h_int : EIntegrable (fun x ↦ ENNReal.log (X x)) Qmix :=
    Or.inl (lintegral_toENNReal_log_ne_top_of_klDiv_ne_top
      (ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hD, ENNReal.ofReal_ne_top⟩) hKL)
      hX.measurable hX1)
  rw [← eintegral_bind (measurable_scaleAlt Q).aemeasurable hX.measurable.ennreal_log.aemeasurable
    h_int]
  calc ∫ᵉ x, ENNReal.log (X x) ∂Qmix ≤ maxEPower Qmix {Pmix} :=
        hX'.eintegral_log_le_maxEPower Qmix
  _ = (klDiv Qmix Pmix : EReal) := maxEPower_singleton_eq_klDiv Qmix Pmix
  _ ≤ ((D + ENNReal.ofReal ε : ℝ≥0∞) : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hKL
  _ = (D : EReal) + ε := by
    rw [EReal.coe_ennreal_add, EReal.coe_ennreal_ofReal, max_eq_left hε.le]

/-- **The GROW bound.** If the log-radius has a first moment under `ν` and under `Q`, then every
e-variable `X` for the null satisfies `inf_t E_{Q_t} [log X] ≤ D`, where `D` is the relative
entropy of the laws of the direction. [EVR26, Note 29] -/
theorem iInf_eintegral_log_scaleAlt_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (π₀ : Measure M) [IsProbabilityMeasure π₀] (Q : Measure (ℝ × M)) [IsProbabilityMeasure Q]
    (hν : Integrable id ν) (hQ : Integrable Prod.fst Q) {X : ℝ × M → ℝ≥0∞}
    (hX : IsEVar X (Set.range (scaleNull ν π₀))) :
    ⨅ t, ∫ᵉ x, ENNReal.log (X x) ∂(scaleAlt Q t) ≤ (klDiv Q.snd π₀ : EReal) := by
  set D := klDiv Q.snd π₀
  refine EReal.le_of_forall_lt_iff_le.mp fun z hz ↦ ?_
  have hD : (D : EReal) = ((D : EReal).toReal : EReal) :=
    (EReal.coe_toReal hz.ne_top (EReal.coe_ennreal_ne_bot D)).symm
  have hDz : (D : EReal).toReal < z := by
    rw [hD] at hz
    exact EReal.coe_lt_coe_iff.mp hz
  obtain ⟨ρ, hρ, h⟩ :=
    exists_eintegral_eintegral_log_scaleAlt_le ν π₀ Q hν hQ (sub_pos.mpr hDz)
  calc ⨅ t, ∫ᵉ x, ENNReal.log (X x) ∂(scaleAlt Q t)
      = ∫ᵉ _, ⨅ t, ∫ᵉ x, ENNReal.log (X x) ∂(scaleAlt Q t) ∂ρ := by
        rw [eintegral_const, measure_univ, EReal.coe_ennreal_one, mul_one]
  _ ≤ ∫ᵉ t, ∫ᵉ x, ENNReal.log (X x) ∂(scaleAlt Q t) ∂ρ := eintegral_mono fun t ↦ iInf_le _ t
  _ ≤ (D : EReal) + ((z - (D : EReal).toReal : ℝ) : EReal) := h X hX
  _ = z := by
    rw [hD, ← EReal.coe_add, EReal.toReal_coe, add_sub_cancel]

/-! ### The likelihood ratio of the direction -/

/-- The likelihood ratio `T (u, m) = dQ.snd/dπ₀ (m)` of the direction is an e-variable for the
null. -/
theorem isEVar_rnDeriv_snd_scaleNull (ν : Measure ℝ) [IsProbabilityMeasure ν] (π₀ : Measure M)
    [SFinite π₀] (Q : Measure (ℝ × M)) [IsProbabilityMeasure Q] :
    IsEVar (fun x ↦ Q.snd.rnDeriv π₀ x.2) (Set.range (scaleNull ν π₀)) := by
  have hr : Measurable fun x : ℝ × M ↦ Q.snd.rnDeriv π₀ x.2 :=
    (Measure.measurable_rnDeriv _ _).comp measurable_snd
  refine ⟨hr, ?_⟩
  rintro μ ⟨t, rfl⟩
  rw [scaleNull_def, lintegral_prod _ hr.aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  exact Measure.lintegral_rnDeriv_le.trans_eq (by simp)

/-- If `Q.snd ≪ π₀`, the likelihood ratio `T (u, m) = dQ.snd/dπ₀ (m)` of the direction has
expected logarithm `D = KL(Q.snd ‖ π₀)` under every alternative. [EVR26, Note 29] -/
theorem eintegral_log_rnDeriv_snd_scaleAlt (π₀ : Measure M) [IsProbabilityMeasure π₀]
    (Q : Measure (ℝ × M)) [IsProbabilityMeasure Q] (hac : Q.snd ≪ π₀) (t : ℝ) :
    ∫ᵉ x, ENNReal.log (Q.snd.rnDeriv π₀ x.2) ∂(scaleAlt Q t) = (klDiv Q.snd π₀ : EReal) := by
  have hr' : Measurable fun m ↦ ENNReal.log (Q.snd.rnDeriv π₀ m) :=
    (Measure.measurable_rnDeriv _ _).ennreal_log
  have h_ae : (fun m ↦ (llr Q.snd π₀ m : EReal)) =ᵐ[Q.snd]
      fun m ↦ ENNReal.log (Q.snd.rnDeriv π₀ m) := by
    filter_upwards [Measure.rnDeriv_pos hac, hac.ae_le (Measure.rnDeriv_lt_top Q.snd π₀)]
      with m h0 htop
    rw [ENNReal.log_pos_real h0.ne' htop.ne, llr]
  have h := eintegral_map (μ := scaleAlt Q t) hr' measurable_snd
  rw [← Measure.snd, snd_scaleAlt] at h
  rw [← h, coe_klDiv_eq_eintegral_llr_of_measure_eq hac (by simp), eintegral_congr_ae h_ae]

/-- **The likelihood ratio of the direction is GROW.** If the log-radius has a first moment under
`ν` and under `Q`, and `Q.snd ≪ π₀`, then `D = KL(Q.snd ‖ π₀)` is the largest worst-case expected
logarithm `inf_t E_{Q_t} [log X]` of an e-variable `X` for the null, and the likelihood ratio of
the direction attains it. [EVR26, Note 29] -/
theorem isGreatest_iInf_eintegral_log_scaleAlt (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (π₀ : Measure M) [IsProbabilityMeasure π₀] (Q : Measure (ℝ × M)) [IsProbabilityMeasure Q]
    (hν : Integrable id ν) (hQ : Integrable Prod.fst Q) (hac : Q.snd ≪ π₀) :
    IsGreatest {v | ∃ X, IsEVar X (Set.range (scaleNull ν π₀)) ∧
      v = ⨅ t, ∫ᵉ x, ENNReal.log (X x) ∂(scaleAlt Q t)} (klDiv Q.snd π₀ : EReal) := by
  refine ⟨⟨_, isEVar_rnDeriv_snd_scaleNull ν π₀ Q, ?_⟩, ?_⟩
  · simp_rw [eintegral_log_rnDeriv_snd_scaleAlt π₀ Q hac, ciInf_const]
  · rintro v ⟨X, hX, rfl⟩
    exact iInf_eintegral_log_scaleAlt_le ν π₀ Q hν hQ hX

end ProbabilityTheory
