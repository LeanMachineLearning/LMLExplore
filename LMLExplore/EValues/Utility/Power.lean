/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Statlib.Divergence.Renyi.Basic
public import Statlib.EValues.RIPr
import LMLExplore.Analysis.Convex.SpecificFunctions.Pow
import LMLExplore.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Statlib.EValues.NumeraireExistence
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The power utility and its maximal expected value over e-variables

For `γ > 1`, the power utility of relative risk aversion `γ` is `x ↦ x ^ (1 - γ) / (1 - γ)`, a
Statlib `Utility` bounded above by `0`, with value `⊥` at `0`, `0` at `∞`, and derivative
`x ↦ x ^ (-γ)` on all of `ℝ≥0∞`. Its expected value under a measure `Q` is `-(γ - 1)⁻¹` times the
moment `∫⁻ X ^ (1 - γ) ∂Q`, so maximizing the expected power utility over the e-variables of a
null `S` is minimizing that moment.

The minimal moment is computed by duality with the effective null `effectiveSet S` [LRR25,
Theorem 6.1]. For an e-variable `X` and a member `P` of the effective null, Hölder's inequality
bounds the power `γ` of the affinity `∫⁻ (dQ/dP) ^ γ⁻¹ ∂P` of order `γ⁻¹` by `∫⁻ X ^ (1 - γ) ∂Q`.
Equality holds for Statlib's numeraire `Y` of the power utility (which exists since the utility is
bounded above) and the measure with density `Y ^ (-γ)`, normalized, with respect to `Q`: the
first-order condition of `Y` puts that measure in the effective null. Hence the maximal expected
power utility is `-(γ - 1)⁻¹` times the largest power `γ` of the affinity over the effective null,
and the largest affinity is attained. With Statlib's `renyiDiv`, the power `γ` of the affinity is
`Q univ * P univ ^ (γ - 1) * exp ((1 - γ) * R_{γ⁻¹}(Q, P))`.

Statlib's `renyiDiv` compares the normalized measures, while the effective null contains measures
of mass less than `1`, so the factor `P univ ^ (γ - 1)` stays in the formula. For `S = {δ₀ / 2}` on
a point and `Q = δ₀`, the e-variables are the constants at most `2` and the maximal expected
utility is `2 ^ (1 - γ) / (1 - γ)`, while `R_{γ⁻¹}(Q, P) = 0` for every nonzero `P`.

## Main definitions

* `ProbabilityTheory.powerUtility γ hγ`: the power utility `x ↦ x ^ (1 - γ) / (1 - γ)`, written
  `-((γ - 1)⁻¹ * x ^ (1 - γ))` with the product in `ℝ≥0∞`.

## Main statements

* `ProbabilityTheory.powerUtility_le_zero`: the power utility is bounded above by `0`.
* `ProbabilityTheory.deriv_powerUtility`: its derivative is `x ↦ x ^ (-γ)`, with `0 ^ (-γ) = ∞`
  and `∞ ^ (-γ) = 0`.
* `ProbabilityTheory.eintegral_powerUtility`: `∫ᵉ U (X ω) ∂Q = -((γ - 1)⁻¹ * ∫⁻ X ω ^ (1 - γ) ∂Q)`.
* `ProbabilityTheory.IsNumeraireFor.lintegral_rpow_neg_mul_le`: the first-order condition
  `∫⁻ Y ^ (-γ) * Z ∂Q ≤ ∫⁻ Y ^ (1 - γ) ∂Q` of a numeraire `Y` for the power utility.
* `ProbabilityTheory.rpow_lintegral_rnDeriv_rpow_inv_le`: weak duality,
  `(∫⁻ (dQ/dP) ^ γ⁻¹ ∂P) ^ γ ≤ ∫⁻ X ^ (1 - γ) ∂Q` when `∫⁻ X ∂P ≤ 1`.
* `ProbabilityTheory.exists_isEVar_mem_effectiveSet_rpow_lintegral_rnDeriv_eq`: strong duality,
  with an e-variable and a member of the effective null that attain it.
* `ProbabilityTheory.maxUtility_powerUtility`,
  `ProbabilityTheory.exists_isMaxOn_lintegral_rnDeriv_rpow_inv`,
  `ProbabilityTheory.maxUtility_powerUtility_eq_iSup_renyiDiv`: the maximal expected power utility
  of the e-variables of a null of masses at most `1`, through the affinity or the Rényi divergence
  to the effective null, and the attainment of the supremum [LRR25, Theorem 6.1].

## References

* M. Larsson, A. Ramdas, J. Ruf, *The numeraire e-variable and reverse information projection*
  (2025) [LRR25].
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {γ : ℝ}

/-- On `(0, ∞)`, the power utility is the real function `x ↦ -((γ - 1)⁻¹ * x ^ (1 - γ))`. -/
private lemma toReal_neg_ofReal_mul_rpow (hγ : 1 < γ) {x : ℝ} (hx : 0 < x) :
    (-((ENNReal.ofReal (γ - 1)⁻¹ * ENNReal.ofReal x ^ (1 - γ) : ℝ≥0∞) : EReal)).toReal
      = -((γ - 1)⁻¹ * x ^ (1 - γ)) := by
  have hc : 0 ≤ (γ - 1)⁻¹ := inv_nonneg.2 (by linarith)
  rw [ENNReal.ofReal_rpow_of_pos hx, ← ENNReal.ofReal_mul hc, EReal.toReal_neg_eq,
    EReal.toReal_coe_ennreal, ENNReal.toReal_ofReal (by positivity)]

/-- The power utility `x ↦ x ^ (1 - γ) / (1 - γ)` of relative risk aversion `γ > 1`, written
`-((γ - 1)⁻¹ * x ^ (1 - γ))` with the product in `ℝ≥0∞`: it is `⊥` at `0` and `0` at `∞`. -/
noncomputable def powerUtility (γ : ℝ) (hγ : 1 < γ) : Utility where
  toFun x := -((ENNReal.ofReal (γ - 1)⁻¹ * x ^ (1 - γ) : ℝ≥0∞) : EReal)
  eq_coe' x hx0 _ := by
    have h : ENNReal.ofReal (γ - 1)⁻¹ * x ^ (1 - γ) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp [ENNReal.rpow_eq_top_iff, hx0, hγ.le])
    refine ⟨?_, ?_⟩
    · rwa [ne_eq, EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff]
    · rw [ne_eq, EReal.neg_eq_top_iff]
      exact EReal.coe_ennreal_ne_bot _
  monotone' x y hxy := by
    simp only [EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
    gcongr _ * ?_
    exact ENNReal.rpow_le_rpow_of_nonpos hxy (by linarith)
  continuous' := continuous_neg.comp <| continuous_coe_ennreal_ereal.comp <|
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp ENNReal.continuous_rpow_const
  concave' := by
    have hsmul (c : ℝ≥0) (v : ℝ≥0∞) : c • (-(v : EReal)) = -(((c : ℝ≥0∞) * v : ℝ≥0∞) : EReal) := by
      rw [EReal.smul_nnreal_eq_mul, mul_neg, EReal.coe_ennreal_mul, EReal.coe_nnreal_eq_coe_real]
    have hadd (u v : ℝ≥0∞) : -(u : EReal) + -(v : EReal) = -((u + v : ℝ≥0∞) : EReal) := by
      rw [EReal.coe_ennreal_add, EReal.neg_add (.inl (EReal.coe_ennreal_ne_bot _))
        (.inr (EReal.coe_ennreal_ne_bot _)), sub_eq_add_neg]
    refine ⟨convex_univ, fun x _ y _ a b _ _ hab ↦ ?_⟩
    simp only [hsmul, hadd, EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
    have h := (ENNReal.convexOn_rpow_of_nonpos (p := 1 - γ) (by linarith)).2 (mem_univ x)
      (mem_univ y) zero_le zero_le hab
    simp only [ENNReal.smul_def, smul_eq_mul] at h ⊢
    calc ENNReal.ofReal (γ - 1)⁻¹ * (a * x + b * y) ^ (1 - γ)
    _ ≤ ENNReal.ofReal (γ - 1)⁻¹ * (a * x ^ (1 - γ) + b * y ^ (1 - γ)) := by gcongr
    _ = _ := by ring
  differentiable' := by
    refine ContDiffOn.congr (fun x hx ↦ ?_) fun x hx ↦ toReal_neg_ofReal_mul_rpow hγ hx
    exact (((Real.contDiffAt_rpow_const_of_ne (p := 1 - γ) (n := 1) (ne_of_gt hx)).const_smul
      (γ - 1)⁻¹).neg).contDiffWithinAt

variable {hγ : 1 < γ}

/-- The power utility as a function, `x ↦ -((γ - 1)⁻¹ * x ^ (1 - γ))`. -/
lemma powerUtility_apply (x : ℝ≥0∞) :
    powerUtility γ hγ x = -((ENNReal.ofReal (γ - 1)⁻¹ * x ^ (1 - γ) : ℝ≥0∞) : EReal) := (rfl)

@[simp]
lemma powerUtility_zero : powerUtility γ hγ 0 = ⊥ := by
  rw [powerUtility_apply, ENNReal.zero_rpow_of_neg (by linarith),
    ENNReal.mul_top (ENNReal.ofReal_pos.2 (inv_pos.2 (by linarith))).ne', EReal.coe_ennreal_top,
    EReal.neg_top]

@[simp]
lemma powerUtility_top : powerUtility γ hγ ∞ = 0 := by
  simp [powerUtility_apply, ENNReal.top_rpow_of_neg (show 1 - γ < 0 by linarith)]

/-- The power utility is bounded above by `0`. -/
lemma powerUtility_le_zero (x : ℝ≥0∞) : powerUtility γ hγ x ≤ 0 := by
  rw [powerUtility_apply, EReal.neg_le, neg_zero]
  exact EReal.coe_ennreal_nonneg _

/-- On `(0, ∞)`, the real form of the power utility is `x ↦ -((γ - 1)⁻¹ * x ^ (1 - γ))`. -/
@[simp]
lemma real_powerUtility {x : ℝ} (hx : 0 < x) :
    (powerUtility γ hγ).real x = -((γ - 1)⁻¹ * x ^ (1 - γ)) :=
  toReal_neg_ofReal_mul_rpow hγ hx

/-- On `(0, ∞)`, the derivative of the real form of the power utility is `x ↦ x ^ (-γ)`. -/
lemma deriv_real_powerUtility {x : ℝ} (hx : 0 < x) :
    deriv (powerUtility γ hγ).real x = x ^ (-γ) := by
  have h : HasDerivAt (fun y : ℝ ↦ -((γ - 1)⁻¹ * y ^ (1 - γ))) (x ^ (-γ)) x := by
    convert ((Real.hasDerivAt_rpow_const (p := 1 - γ) (.inl hx.ne')).const_mul (γ - 1)⁻¹).neg
      using 1
    rw [show 1 - γ - 1 = -γ by ring]
    field_simp [show γ - 1 ≠ 0 by linarith]
    ring
  refine (h.congr_of_eventuallyEq ?_).deriv
  filter_upwards [eventually_gt_nhds hx] with y hy using real_powerUtility hy

/-- The derivative of the power utility is `x ↦ x ^ (-γ)`, with `0 ^ (-γ) = ∞` and
`∞ ^ (-γ) = 0`. -/
lemma deriv_powerUtility (x : ℝ≥0∞) :
    (powerUtility γ hγ).deriv x = ((x ^ (-γ) : ℝ≥0∞) : EReal) := by
  have hγ0 : -γ < 0 := by linarith
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Utility.deriv_zero_eq, ENNReal.zero_rpow_of_neg hγ0, EReal.coe_ennreal_top]
    refine Tendsto.limsup_eq ?_
    rw [EReal.tendsto_coe_nhds_top_iff]
    have h_pos : ∀ᶠ y : ℝ≥0∞ in 𝓝[>] 0, 0 < y.toReal := by
      filter_upwards [eventually_ne_nhdsWithin (show (0 : ℝ≥0∞) ≠ ∞ by simp),
        self_mem_nhdsWithin] with y hy_top hy_pos
      exact ENNReal.toReal_pos (ne_of_gt hy_pos) hy_top
    refine ((tendsto_rpow_neg_nhdsGT_zero hγ0).comp (f := fun y : ℝ≥0∞ ↦ y.toReal) ?_).congr'
      ?_
    · rw [tendsto_nhdsWithin_iff]
      exact ⟨tendsto_nhdsWithin_of_tendsto_nhds
        ((ENNReal.continuousAt_toReal (by simp)).tendsto.trans (by simp)), h_pos⟩
    · filter_upwards [h_pos] with y hy using (deriv_real_powerUtility hy).symm
  rcases eq_or_ne x ∞ with rfl | hx_top
  · rw [(powerUtility γ hγ).deriv_top_eq_zero (b := 0) (by simpa using powerUtility_le_zero),
      ENNReal.top_rpow_of_neg hγ0, EReal.coe_ennreal_zero]
  rw [Utility.deriv_eq_coe _ hx0 hx_top,
    deriv_real_powerUtility (ENNReal.toReal_pos hx0 hx_top), ENNReal.toReal_rpow,
    EReal.coe_ennreal_toReal (by simp [ENNReal.rpow_eq_top_iff, hx0, hx_top])]

/-- The derivative of the power utility, in `ℝ≥0∞` form. -/
lemma toENNReal_deriv_powerUtility (x : ℝ≥0∞) :
    ((powerUtility γ hγ).deriv x).toENNReal = x ^ (-γ) := by
  rw [deriv_powerUtility, EReal.toENNReal_coe]

lemma deriv_powerUtility_zero : (powerUtility γ hγ).deriv 0 = ⊤ := by
  rw [deriv_powerUtility, ENNReal.zero_rpow_of_neg (by linarith), EReal.coe_ennreal_top]

/-- The expected power utility is `-(γ - 1)⁻¹` times the moment `∫⁻ X ω ^ (1 - γ) ∂Q`. -/
lemma eintegral_powerUtility {Ω : Type*} {mΩ : MeasurableSpace Ω} (Q : Measure Ω)
    (X : Ω → ℝ≥0∞) :
    ∫ᵉ ω, powerUtility γ hγ (X ω) ∂Q
      = -((ENNReal.ofReal (γ - 1)⁻¹ * ∫⁻ ω, X ω ^ (1 - γ) ∂Q : ℝ≥0∞) : EReal) := by
  rw [eintegral_eq_neg_lintegral_of_nonpos fun ω ↦ powerUtility_le_zero (X ω),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp_rw [powerUtility_apply, neg_neg, EReal.toENNReal_coe]

/-! ### The maximal expected power utility over the e-variables of a null -/

section MaxUtility

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q P : Measure Ω} {S : Set (Measure Ω)}
  {X Y Z : Ω → ℝ≥0∞}

/-- **Weak duality** for the power utility: if `∫⁻ X ∂P ≤ 1`, the affinity
`∫⁻ (dQ/dP) ^ γ⁻¹ ∂P` of order `γ⁻¹` between `Q` and `P`, raised to the power `γ`, is at most the
moment `∫⁻ X ^ (1 - γ) ∂Q` [LRR25, Theorem 6.1]. -/
theorem rpow_lintegral_rnDeriv_rpow_inv_le (hγ : 1 < γ) (hX : Measurable X)
    (hXP : ∫⁻ ω, X ω ∂P ≤ 1) :
    (∫⁻ ω, Q.rnDeriv P ω ^ γ⁻¹ ∂P) ^ γ ≤ ∫⁻ ω, X ω ^ (1 - γ) ∂Q := by
  set M := ∫⁻ ω, X ω ^ (1 - γ) ∂Q
  rcases eq_or_ne M ∞ with hM | hM
  · simp [hM]
  have ha : 0 < γ⁻¹ := inv_pos.2 (by linarith)
  have ha1 : γ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hγ
  -- `X` is `Q`-almost surely positive, so `dQ/dP` vanishes `P`-almost surely where `X = 0`
  have hQ0 : Q {ω | X ω = 0} = 0 := by
    have h := ae_lt_top (hX.pow_const (1 - γ)) hM
    rw [ae_iff] at h
    convert h using 2
    ext ω
    simp [ENNReal.rpow_eq_top_iff, show 1 - γ < 0 by linarith, show ¬γ < 1 by linarith]
  have hq0 : ∀ᵐ ω ∂P, X ω = 0 → Q.rnDeriv P ω = 0 := by
    have h : ∫⁻ ω in {ω | X ω = 0}, Q.rnDeriv P ω ∂P = 0 :=
      le_antisymm ((Measure.setLIntegral_rnDeriv_le _).trans hQ0.le) zero_le
    rw [lintegral_eq_zero_iff (Measure.measurable_rnDeriv _ _),
      EventuallyEq,
      ae_restrict_iff' (measurableSet_eq_fun hX measurable_const)] at h
    exact h
  have hXtop : ∀ᵐ ω ∂P, X ω < ∞ := ae_lt_top hX (hXP.trans_lt ENNReal.one_lt_top).ne
  -- Hölder's inequality with the exponents `γ⁻¹` and `1 - γ⁻¹`
  have h_holder : ∫⁻ ω, Q.rnDeriv P ω ^ γ⁻¹ ∂P ≤ M ^ γ⁻¹ := calc
    ∫⁻ ω, Q.rnDeriv P ω ^ γ⁻¹ ∂P
    _ ≤ ∫⁻ ω, (Q.rnDeriv P ω * X ω ^ (1 - γ)) ^ γ⁻¹ * X ω ^ (1 - γ⁻¹) ∂P := by
      refine lintegral_mono_ae ?_
      filter_upwards [hq0, hXtop] with ω hω0 hωtop
      rcases eq_or_ne (Q.rnDeriv P ω) 0 with h | h
      · simp [h, ENNReal.zero_rpow_of_pos ha]
      have hX0 : X ω ≠ 0 := fun h' ↦ h (hω0 h')
      rw [ENNReal.mul_rpow_of_nonneg _ _ ha.le, ← ENNReal.rpow_mul, mul_assoc,
        ← ENNReal.rpow_add _ _ hX0 hωtop.ne,
        show (1 - γ) * γ⁻¹ + (1 - γ⁻¹) = 0 by field_simp; ring, ENNReal.rpow_zero, mul_one]
    _ ≤ (∫⁻ ω, Q.rnDeriv P ω * X ω ^ (1 - γ) ∂P) ^ γ⁻¹ * (∫⁻ ω, X ω ∂P) ^ (1 - γ⁻¹) :=
      ENNReal.lintegral_mul_norm_pow_le
        ((Measure.measurable_rnDeriv _ _).mul (hX.pow_const _)).aemeasurable hX.aemeasurable
        ha.le (by linarith) (by ring)
    _ ≤ M ^ γ⁻¹ * 1 := by
      gcongr
      · calc ∫⁻ ω, Q.rnDeriv P ω * X ω ^ (1 - γ) ∂P
          _ = ∫⁻ ω, X ω ^ (1 - γ) ∂(P.withDensity (Q.rnDeriv P)) :=
            (lintegral_withDensity_eq_lintegral_mul₀ (Measure.measurable_rnDeriv _ _).aemeasurable
              (hX.pow_const _).aemeasurable).symm
          _ ≤ M := lintegral_mono' (Measure.withDensity_rnDeriv_le _ _) le_rfl
      · exact ENNReal.rpow_le_one hXP (by linarith)
    _ = M ^ γ⁻¹ := mul_one _
  calc (∫⁻ ω, Q.rnDeriv P ω ^ γ⁻¹ ∂P) ^ γ
  _ ≤ (M ^ γ⁻¹) ^ γ := ENNReal.rpow_le_rpow h_holder (by linarith)
  _ = M := by rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (by linarith), ENNReal.rpow_one]

/-- The first-order condition of a numeraire `Y` for the power utility among the e-variables of a
null of masses at most `1`: `∫⁻ Y ^ (-γ) * Z ∂Q ≤ ∫⁻ Y ^ (1 - γ) ∂Q` for every e-variable `Z`. -/
lemma IsNumeraireFor.lintegral_rpow_neg_mul_le (hS : ∀ P ∈ S, P univ ≤ 1)
    (hY : IsNumeraireFor (powerUtility γ hγ) Y {X | IsEVar X S} Q) (hZ : IsEVar Z S) :
    ∫⁻ ω, Y ω ^ (-γ) * Z ω ∂Q ≤ ∫⁻ ω, Y ω ^ (1 - γ) ∂Q := by
  have hYm : Measurable Y := hY.mem.measurable
  have hYY : ∀ᵐ ω ∂Q, Y ω ^ (-γ) * Y ω = Y ω ^ (1 - γ) := by
    filter_upwards [hY.ae_ne_zero deriv_powerUtility_zero (isEVar_one hS) hYm.aemeasurable]
      with ω hω
    rcases eq_or_ne (Y ω) ∞ with h | h
    · simp [h, ENNReal.top_rpow_of_neg (show -γ < 0 by linarith),
        ENNReal.top_rpow_of_neg (show 1 - γ < 0 by linarith)]
    · rw [show 1 - γ = -γ + 1 by ring, ENNReal.rpow_add _ _ hω h, ENNReal.rpow_one]
  have h := hY.lintegral_deriv_mul_le hZ hYm.aemeasurable hZ.measurable.aemeasurable
  simp only [toENNReal_deriv_powerUtility] at h
  exact h.trans (lintegral_congr_ae hYY).le

/-- The moment `∫⁻ Y ^ (1 - γ) ∂Q` of a numeraire `Y` for the power utility among the e-variables
of a null of masses at most `1` is at most that of the e-variable `1`, which is `Q univ`. -/
lemma IsNumeraireFor.lintegral_rpow_le_measure_univ (hS : ∀ P ∈ S, P univ ≤ 1)
    (hY : IsNumeraireFor (powerUtility γ hγ) Y {X | IsEVar X S} Q) :
    ∫⁻ ω, Y ω ^ (1 - γ) ∂Q ≤ Q univ := by
  have h := hY.eintegral_utility_le (isEVar_one hS) hY.mem.measurable.aemeasurable
    aemeasurable_const
  rw [eintegral_powerUtility, eintegral_powerUtility, EReal.neg_le_neg_iff,
    EReal.coe_ennreal_le_coe_ennreal_iff] at h
  have hk : ENNReal.ofReal (γ - 1)⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 (by linarith))).ne'
  simpa using (ENNReal.mul_le_mul_iff_right hk ENNReal.ofReal_ne_top).1 h

/-- **Strong duality** for the power utility [LRR25, Theorem 6.1]: some e-variable `X` and some
member `P` of the effective null make the two sides of
`rpow_lintegral_rnDeriv_rpow_inv_le` equal. The e-variable is Statlib's numeraire `Y` for the power
utility, and `P` has density `Y ^ (-γ) / ∫⁻ Y ^ (1 - γ) ∂Q` with respect to `Q`: by the first-order
condition of `Y`, it gives every e-variable a mean at most `1`. -/
theorem exists_isEVar_mem_effectiveSet_rpow_lintegral_rnDeriv_eq (hγ : 1 < γ)
    (hS : ∀ P ∈ S, P univ ≤ 1) (Q : Measure Ω) [IsFiniteMeasure Q] :
    ∃ X, IsEVar X S ∧ ∃ P ∈ effectiveSet S,
      (∫⁻ ω, Q.rnDeriv P ω ^ γ⁻¹ ∂P) ^ γ = ∫⁻ ω, X ω ^ (1 - γ) ∂Q := by
  obtain ⟨Y, hY⟩ := (isEVarClass_isEVar S hS).exists_isNumeraireFor (U := powerUtility γ hγ)
    (b := 0) (fun x ↦ by simpa using powerUtility_le_zero x) Q
  have hYS : IsEVar Y S := hY.mem
  have hYm := hYS.measurable
  refine ⟨Y, hYS, ?_⟩
  set c := ∫⁻ ω, Y ω ^ (1 - γ) ∂Q
  have ha1 : γ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hγ
  have hY0 : ∀ᵐ ω ∂Q, Y ω ≠ 0 :=
    hY.ae_ne_zero deriv_powerUtility_zero (isEVar_one hS) hYm.aemeasurable
  have hc_le : c ≤ Q univ := hY.lintegral_rpow_le_measure_univ hS
  rcases eq_or_ne c 0 with hc0 | hc0
  · refine ⟨0, fun X _ ↦ by simp, ?_⟩
    simp [hc0, ENNReal.zero_rpow_of_pos (show 0 < γ by linarith)]
  have hctop : c ≠ ∞ := (hc_le.trans_lt (measure_lt_top Q univ)).ne
  -- the dual measure `R` with density `Y ^ (-γ) / c` with respect to `Q`
  set g : Ω → ℝ≥0∞ := fun ω ↦ c⁻¹ * Y ω ^ (-γ) with hg_def
  have hg : Measurable g := (hYm.pow_const _).const_mul _
  set R := Q.withDensity g
  have hR : R ∈ effectiveSet S := fun Z hZ ↦ by
    rw [lintegral_withDensity_eq_lintegral_mul _ hg hZ.measurable]
    calc ∫⁻ ω, (g * Z) ω ∂Q
    _ = c⁻¹ * ∫⁻ ω, Y ω ^ (-γ) * Z ω ∂Q := by
      simp only [Pi.mul_apply, hg_def, mul_assoc]
      exact lintegral_const_mul _ ((hYm.pow_const _).mul hZ.measurable)
    _ ≤ c⁻¹ * c := by gcongr; exact hY.lintegral_rpow_neg_mul_le hS hZ
    _ = 1 := ENNReal.inv_mul_cancel hc0 hctop
  refine ⟨R, hR, ?_⟩
  have : IsFiniteMeasure R := isFiniteMeasure_of_mem_effectiveSet hS hR
  -- the affinity of `Q` and `R` is `∫⁻ g ^ (1 - γ⁻¹) ∂Q`
  have hg_top : ∀ᵐ ω ∂Q, g ω ≠ ∞ := by
    filter_upwards [hY0] with ω hω
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0)
      (by simp [ENNReal.rpow_eq_top_iff, hω, show 0 ≤ γ by linarith])
  have hH : ∫⁻ ω, Q.rnDeriv R ω ^ γ⁻¹ ∂R = (c⁻¹) ^ (1 - γ⁻¹) * c := by
    rw [Measure.lintegral_rpow_rnDeriv_withDensity hg.aemeasurable hg_top ha1,
      ← lintegral_const_mul _ (hYm.pow_const _)]
    refine lintegral_congr fun ω ↦ ?_
    rw [hg_def, ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ← ENNReal.rpow_mul,
      show -γ * (1 - γ⁻¹) = 1 - γ by field_simp; ring]
  rw [hH, ENNReal.inv_rpow, ← ENNReal.rpow_neg]
  nth_rw 2 [← ENNReal.rpow_one c]
  rw [← ENNReal.rpow_add _ _ hc0 hctop, ← ENNReal.rpow_mul,
    show (-(1 - γ⁻¹) + 1) * γ = 1 by field_simp; ring, ENNReal.rpow_one]

/-- **The maximal expected power utility** [LRR25, Theorem 6.1]: over the e-variables of a null of
masses at most `1`, the largest expected power utility under a finite measure `Q` is
`-(γ - 1)⁻¹` times the largest power `γ` of the affinity of order `γ⁻¹` between `Q` and a member
of the effective null. The supremum is attained
(`exists_isMaxOn_lintegral_rnDeriv_rpow_inv`). -/
theorem maxUtility_powerUtility (hγ : 1 < γ) (hS : ∀ P ∈ S, P univ ≤ 1) (Q : Measure Ω)
    [IsFiniteMeasure Q] :
    maxUtility Q S (powerUtility γ hγ) = -((ENNReal.ofReal (γ - 1)⁻¹ *
      ⨆ P ∈ effectiveSet S, (∫⁻ ω, Q.rnDeriv P ω ^ γ⁻¹ ∂P) ^ γ : ℝ≥0∞) : EReal) := by
  obtain ⟨Y, hYS, R, hR, hRY⟩ := exists_isEVar_mem_effectiveSet_rpow_lintegral_rnDeriv_eq hγ hS Q
  have h_le (X : Ω → ℝ≥0∞) (hX : IsEVar X S) :
      ⨆ P ∈ effectiveSet S, (∫⁻ ω, Q.rnDeriv P ω ^ γ⁻¹ ∂P) ^ γ ≤ ∫⁻ ω, X ω ^ (1 - γ) ∂Q :=
    iSup₂_le fun P hP ↦ rpow_lintegral_rnDeriv_rpow_inv_le hγ hX.measurable (hP X hX)
  have h_eq : ⨆ P ∈ effectiveSet S, (∫⁻ ω, Q.rnDeriv P ω ^ γ⁻¹ ∂P) ^ γ
      = ∫⁻ ω, Y ω ^ (1 - γ) ∂Q :=
    le_antisymm (h_le Y hYS) (hRY ▸ le_iSup₂ (f := fun P (_ : P ∈ effectiveSet S) ↦
      (∫⁻ ω, Q.rnDeriv P ω ^ γ⁻¹ ∂P) ^ γ) R hR)
  refine le_antisymm (iSup₂_le fun X hX ↦ ?_) ?_
  · simp only [Function.comp_apply, eintegral_powerUtility, EReal.neg_le_neg_iff,
      EReal.coe_ennreal_le_coe_ennreal_iff]
    gcongr
    exact h_le X hX
  · rw [h_eq, ← eintegral_powerUtility]
    exact hYS.eintegral_le_maxUtility Q _

/-- The largest affinity of order `γ⁻¹` between `Q` and a member of the effective null is attained:
the dual problem of the maximal expected power utility has a solution [LRR25, Theorem 6.1]. -/
theorem exists_isMaxOn_lintegral_rnDeriv_rpow_inv (hγ : 1 < γ) (hS : ∀ P ∈ S, P univ ≤ 1)
    (Q : Measure Ω) [IsFiniteMeasure Q] :
    ∃ P ∈ effectiveSet S, IsMaxOn (fun P ↦ ∫⁻ ω, Q.rnDeriv P ω ^ γ⁻¹ ∂P) (effectiveSet S) P := by
  obtain ⟨Y, hYS, R, hR, hRY⟩ := exists_isEVar_mem_effectiveSet_rpow_lintegral_rnDeriv_eq hγ hS Q
  refine ⟨R, hR, fun P hP ↦ ?_⟩
  have h := rpow_lintegral_rnDeriv_rpow_inv_le (Q := Q) hγ hYS.measurable (hP Y hYS)
  rw [← hRY] at h
  exact (ENNReal.rpow_le_rpow_iff (by linarith)).1 h

/-- **The maximal expected power utility, with Rényi divergences** [LRR25, Theorem 6.1]: with
Statlib's `renyiDiv` of order `γ⁻¹`, which compares the normalized measures,
`maxUtility Q S (powerUtility γ hγ)` is `-(γ - 1)⁻¹` times the supremum over the effective null of
`Q univ * P univ ^ (γ - 1) * exp ((1 - γ) * R_{γ⁻¹}(Q, P))`. For a probability measure `Q` and
members of mass `1` this is `exp ((1 - γ) * R_{γ⁻¹}(Q, P))`; the factor `P univ ^ (γ - 1)` cannot
be dropped, since the effective null contains measures of mass less than `1`. -/
theorem maxUtility_powerUtility_eq_iSup_renyiDiv (hγ : 1 < γ) (hS : ∀ P ∈ S, P univ ≤ 1)
    (Q : Measure Ω) [IsFiniteMeasure Q] :
    maxUtility Q S (powerUtility γ hγ) = -((ENNReal.ofReal (γ - 1)⁻¹ * ⨆ P ∈ effectiveSet S,
      Q univ * P univ ^ (γ - 1) * EReal.exp (((1 - γ : ℝ) : EReal) * renyiDiv γ⁻¹ Q P) : ℝ≥0∞) :
        EReal) := by
  rw [maxUtility_powerUtility hγ hS Q]
  congr 3
  refine iSup_congr fun P ↦ iSup_congr fun hP ↦ ?_
  have : IsFiniteMeasure P := isFiniteMeasure_of_mem_effectiveSet hS hP
  have hγ0 : 0 < γ := by linarith
  rw [lintegral_rpow_rnDeriv_eq_mul_exp_renyiDiv (inv_pos.2 hγ0) (inv_lt_one_of_one_lt₀ hγ),
    ENNReal.mul_rpow_of_nonneg _ _ hγ0.le, ENNReal.mul_rpow_of_nonneg _ _ hγ0.le,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← EReal.exp_mul, inv_mul_cancel₀ hγ0.ne',
    ENNReal.rpow_one, show (1 - γ⁻¹) * γ = γ - 1 by field_simp]
  congr 2
  induction renyiDiv γ⁻¹ Q P using ENNReal.recTopCoe with
  | top =>
    rw [EReal.coe_ennreal_top,
      EReal.coe_mul_top_of_pos (by simpa using inv_lt_one_of_one_lt₀ hγ), EReal.neg_top,
      EReal.bot_mul_coe_of_pos hγ0, EReal.coe_mul_top_of_neg (by linarith)]
  | coe r =>
    rw [EReal.coe_nnreal_eq_coe_real]
    norm_cast
    field_simp
    ring

end MaxUtility

end ProbabilityTheory
