/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Integral.Average
import LMLExplore.Analysis.Convex.Integral

/-!
# Convolution with a measure whose translates are controlled

A measure `ρ` on `ℝ` is *`b`-log-Lipschitz under translation* when every translate is at most
`exp (b |u|)` times `ρ`: `ρ.map (· + u) ≤ exp (b |u|) • ρ` for every `u`. A density `p` with
`p (t - u) ≤ exp (b |u|) p t`, such as the Laplace density of rate `b`, gives such a measure.

Translating by `-u` gives the lower bound `exp (-b |u|) • ρ ≤ ρ.map (· + u)`, and integrating it
over `u ∼ ν` gives `(∫⁻ exp (-b |u|) ∂ν) • ρ ≤ ρ ∗ ν`: the convolution of `ρ` with any law
dominates a multiple of `ρ`. This is how a prior on a location parameter that is log-Lipschitz
under translation compares the mixtures of a location family with the prior itself.

## Main statements

* `MeasureTheory.Measure.nonneg_of_forall_map_add_le`: the constant `b` of a finite nonzero
  measure is nonnegative.
* `MeasureTheory.Measure.smul_le_map_add_of_forall_map_add_le`:
  `exp (-b |u|) • ρ ≤ ρ.map (· + u)`.
* `MeasureTheory.Measure.lintegral_smul_le_conv_of_forall_map_add_le`:
  `(∫⁻ exp (-b |u|) ∂ν) • ρ ≤ ρ ∗ ν`.
* `MeasureTheory.Measure.ofReal_mul_exp_smul_le_conv_of_forall_map_add_le`:
  `ν(ℝ) exp (-b ⨍ |u| ∂ν) • ρ ≤ ρ ∗ ν` when `ν` has a first moment, by Jensen's inequality.

## Implementation notes

These bounds are the domination step of [EVR26, Note 29], where a log-Lipschitz prior compares
the mixtures of the nulls of a scale family with the prior. They are adapted from
`nonneg_of_map_add_le`, `smul_le_map_add`, `ofReal_exp_neg_le_lintegral` and `smul_le_map_prod` in
`EValuesResearch/Results/TTestGrowAux.lean` (commit `562b62e`) of the paper project
`RemyDegenne/evalues_research`, stated there for probability measures `ν`, and
restated here through Mathlib's `Measure.conv`; the Jensen step reuses
`ofReal_measureReal_mul_exp_average_le_lintegral` instead of reproving it.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 29, and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {ρ : Measure ℝ} {b : ℝ}

/-- If every translate of a finite nonzero measure `ρ` on `ℝ` by `u` is at most
`exp (b |u|) • ρ`, then `0 ≤ b`. -/
theorem nonneg_of_forall_map_add_le [IsFiniteMeasure ρ] [NeZero ρ]
    (hρ : ∀ u, ρ.map (· + u) ≤ ENNReal.ofReal (Real.exp (b * |u|)) • ρ) : 0 ≤ b := by
  have h := hρ 1 Set.univ
  rw [map_apply (measurable_add_const 1) MeasurableSet.univ, Set.preimage_univ,
    smul_apply, smul_eq_mul, abs_one, mul_one] at h
  have h1 : 1 ≤ ENNReal.ofReal (Real.exp b) :=
    (ENNReal.mul_le_mul_iff_left (measure_univ_ne_zero.2 (NeZero.ne ρ))
      (measure_ne_top ρ _)).1 (by rwa [one_mul])
  rwa [ENNReal.one_le_ofReal, Real.one_le_exp_iff] at h1

/-- If every translate of `ρ` by `u` is at most `exp (b |u|) • ρ`, then every translate is at
least `exp (-b |u|) • ρ`: apply the upper bound to the translate by `-u`. -/
theorem smul_le_map_add_of_forall_map_add_le
    (hρ : ∀ u, ρ.map (· + u) ≤ ENNReal.ofReal (Real.exp (b * |u|)) • ρ) (u : ℝ) :
    ENNReal.ofReal (Real.exp (-(b * |u|))) • ρ ≤ ρ.map (· + u) := by
  have h := map_mono (hρ (-u)) (measurable_add_const u)
  rw [map_map (measurable_add_const u) (measurable_add_const (-u)),
    Measure.map_smul _ (measurable_add_const u).aemeasurable, abs_neg] at h
  have hid : ((· + u) ∘ (· + -u) : ℝ → ℝ) = id := by ext; simp
  rw [hid, map_id] at h
  calc ENNReal.ofReal (Real.exp (-(b * |u|))) • ρ
      ≤ ENNReal.ofReal (Real.exp (-(b * |u|))) •
        ENNReal.ofReal (Real.exp (b * |u|)) • ρ.map (· + u) := by gcongr
  _ = ρ.map (· + u) := by
    rw [smul_smul]
    simp [← ENNReal.ofReal_mul, Real.exp_nonneg, ← Real.exp_add]

/-- If every translate of `ρ` by `u` is at most `exp (b |u|) • ρ`, then the convolution of `ρ`
with any measure `ν` is at least `(∫⁻ exp (-b |u|) ∂ν) • ρ`. -/
theorem lintegral_smul_le_conv_of_forall_map_add_le
    (hρ : ∀ u, ρ.map (· + u) ≤ ENNReal.ofReal (Real.exp (b * |u|)) • ρ) [SFinite ρ]
    (ν : Measure ℝ) [SFinite ν] :
    (∫⁻ u, ENNReal.ofReal (Real.exp (-(b * |u|))) ∂ν) • ρ ≤ ρ ∗ ν := by
  refine le_iff.mpr fun s hs ↦ ?_
  have hF : Measurable fun p : ℝ × ℝ ↦ p.1 + p.2 := by fun_prop
  rw [conv, map_apply hF hs, prod_apply_symm (hF hs)]
  have h_sec (u : ℝ) : ρ ((fun t ↦ (t, u)) ⁻¹' ((fun p : ℝ × ℝ ↦ p.1 + p.2) ⁻¹' s)) =
      ρ.map (· + u) s := by
    rw [map_apply (measurable_add_const u) hs, Set.preimage_preimage]
  simp_rw [h_sec]
  rw [smul_apply, smul_eq_mul, ← lintegral_mul_const _ (by fun_prop)]
  refine lintegral_mono fun u ↦ ?_
  have h := smul_le_map_add_of_forall_map_add_le hρ u s
  rwa [smul_apply, smul_eq_mul] at h

/-- If every translate of `ρ` by `u` is at most `exp (b |u|) • ρ`, then the convolution of `ρ`
with a finite measure `ν` with a first moment is at least `ν(ℝ) exp (-b ⨍ |u| ∂ν) • ρ`: by
Jensen's inequality, `ν(ℝ) exp (-b ⨍ |u| ∂ν) ≤ ∫⁻ exp (-b |u|) ∂ν`. -/
theorem ofReal_mul_exp_smul_le_conv_of_forall_map_add_le
    (hρ : ∀ u, ρ.map (· + u) ≤ ENNReal.ofReal (Real.exp (b * |u|)) • ρ) [SFinite ρ]
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : Integrable id ν) :
    ENNReal.ofReal (ν.real Set.univ * Real.exp (-(b * ⨍ u, |u| ∂ν))) • ρ ≤ ρ ∗ ν := by
  refine le_trans ?_ (lintegral_smul_le_conv_of_forall_map_add_le hρ ν)
  gcongr
  have h := ofReal_measureReal_mul_exp_average_le_lintegral (hν.abs.const_mul b).neg
  rwa [average_neg, average_const_mul] at h

end MeasureTheory.Measure
