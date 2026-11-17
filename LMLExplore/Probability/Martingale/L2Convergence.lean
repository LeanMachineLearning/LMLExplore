/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalLExpectation
public import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.MeasureTheory.Function.ConditionalLExpectation
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# Convergence of martingales bounded in `L²`

A real submartingale bounded in `Lᵖ` for some `p ≥ 1` is bounded in `L¹`, hence converges almost
surely. The increments `ζ t` of a martingale, measurable for `ℱ (t + 1)` with `E[ζ t | ℱ t] = 0`,
are orthogonal in `L²`, so the second moment of `∑ t < T, ζ t` is the sum of the second moments.
Together, these give the almost sure convergence of the martingale transform `∑ t, α t * ξ t` of
a martingale difference `ξ` with bounded conditional second moment by adapted weights `α` with
bounded `∑ t, α t ^ 2`: this is the noise of a stochastic approximation.

## Main statements

* `MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd_eLpNorm`: a submartingale bounded in `Lᵖ`,
  `1 ≤ p`, converges almost surely.
* `LMLExplore.integral_sq_sum_range_of_condExp_eq_zero`: the second moment of a sum of martingale
  increments is the sum of their second moments.
* `LMLExplore.ae_exists_tendsto_sum_mul_of_condExp_eq_zero`: the weighted noise
  `∑ t, α t * ξ t` of a stochastic approximation converges almost surely, when `ξ` is a
  martingale difference with bounded conditional second moment.

## Implementation notes

The conditional second moment of the noise is the conditional expectation `condLExp` of
`‖ξ t‖ₑ ^ 2`, so that no square integrability needs to be assumed: it follows from the bound.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℕ mΩ}

namespace MeasureTheory

/-- **Martingale convergence in `Lᵖ` form.** A real submartingale bounded in `Lᵖ` for some
`p ≥ 1` converges almost surely, on a finite measure space. -/
theorem Submartingale.exists_ae_tendsto_of_bdd_eLpNorm [IsFiniteMeasure P] {f : ℕ → Ω → ℝ}
    (hf : Submartingale f ℱ P) {p : ℝ≥0∞} (hp : 1 ≤ p) (hbdd : ⨆ n, eLpNorm (f n) p P < ∞) :
    ∀ᵐ ω ∂P, ∃ c, Tendsto (fun n ↦ f n ω) atTop (𝓝 c) := by
  have hexp : 0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal := by
    rcases eq_or_ne p ∞ with rfl | hp'
    · simp
    · have h1 : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp' hp
      simpa using inv_le_one_of_one_le₀ h1
  refine hf.exists_ae_tendsto_of_bdd ((iSup_le fun n ↦ ?_).trans_lt
    (ENNReal.mul_lt_top hbdd (ENNReal.rpow_lt_top_of_nonneg hexp (measure_ne_top P Set.univ))))
  exact (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (hf.integrable n).aestronglyMeasurable).trans
    (mul_le_mul_left (le_iSup (fun n ↦ eLpNorm (f n) p P) n) _)

end MeasureTheory

namespace LMLExplore

/-- **Martingale increments are orthogonal.** If `ζ t` is measurable for `ℱ (t + 1)`, square
integrable and `E[ζ t | ℱ t] = 0`, then `E[(∑ t < T, ζ t) ^ 2] = ∑ t < T, E[ζ t ^ 2]`. -/
theorem integral_sq_sum_range_of_condExp_eq_zero [IsFiniteMeasure P] {ζ : ℕ → Ω → ℝ}
    (hζ : ∀ t, Measurable[ℱ (t + 1)] (ζ t)) (hζ2 : ∀ t, MemLp (ζ t) 2 P)
    (hζ_mean : ∀ t, P[ζ t | ℱ t] =ᵐ[P] 0) (T : ℕ) :
    ∫ ω, (∑ t ∈ range T, ζ t ω) ^ 2 ∂P = ∑ t ∈ range T, ∫ ω, ζ t ω ^ 2 ∂P := by
  have horth {i j : ℕ} (hij : i < j) : ∫ ω, ζ i ω * ζ j ω ∂P = 0 := by
    rw [← integral_condExp (ℱ.le j)]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [condExp_mul_of_stronglyMeasurable_left
      ((hζ i).mono (ℱ.mono hij) le_rfl).stronglyMeasurable ((hζ2 i).integrable_mul (hζ2 j))
      ((hζ2 j).integrable one_le_two), hζ_mean j] with ω h1 h2
    exact h1.trans (by simp [h2])
  refine TauCeti.integral_sq_sum_of_pairwise_integral_mul_eq_zero (fun t _ ↦ hζ2 t)
    fun i _ j _ hij ↦ ?_
  rcases hij.lt_or_gt with h | h
  · exact horth h
  · simpa only [mul_comm] using horth h

/-- **The noise of a stochastic approximation converges.** Let `α t` be measurable for `ℱ t`,
with `∑ t < T, α t ^ 2 ≤ C` almost surely for every `T`. Let `ξ t` be measurable for `ℱ (t + 1)`,
with `E[ξ t | ℱ t] = 0` and `E[ξ t ^ 2 | ℱ t] ≤ K`, the latter in the sense of `condLExp`. Then the
partial sums of `α t * ξ t` converge almost surely: they form a martingale bounded in `L²`. -/
theorem ae_exists_tendsto_sum_mul_of_condExp_eq_zero [IsFiniteMeasure P] {α ξ : ℕ → Ω → ℝ}
    {K : ℝ≥0} {C : ℝ} (hα : Adapted ℱ α) (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hξ_mean : ∀ t, P[ξ t | ℱ t] =ᵐ[P] 0)
    (hξ_var : ∀ t, P⁻[fun ω ↦ ‖ξ t ω‖ₑ ^ 2 | ℱ t] ≤ᵐ[P] fun _ ↦ K)
    (hα_sq : ∀ᵐ ω ∂P, ∀ T, ∑ t ∈ range T, α t ω ^ 2 ≤ C) :
    ∀ᵐ ω ∂P, ∃ s, Tendsto (fun T ↦ ∑ t ∈ range T, α t ω * ξ t ω) atTop (𝓝 s) := by
  have hαm (t : ℕ) : Measurable (α t) := (hα t).mono (ℱ.le t) le_rfl
  have hξm (t : ℕ) : Measurable (ξ t) := (hξ t).mono (ℱ.le _) le_rfl
  -- second moments of the steps and of the noise
  have hα_lint (T : ℕ) :
      ∫⁻ ω, ∑ t ∈ range T, ‖α t ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C * P Set.univ := by
    rw [← lintegral_const]
    refine lintegral_mono_ae (hα_sq.mono fun ω hω ↦ ?_)
    simp_rw [Real.enorm_sq_eq_ofReal_sq]
    rw [← ENNReal.ofReal_sum_of_nonneg fun t _ ↦ sq_nonneg _]
    exact ENNReal.ofReal_le_ofReal (hω T)
  have hα_lt (t : ℕ) : ∫⁻ ω, ‖α t ω‖ₑ ^ 2 ∂P < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono fun ω ↦ ?_) ((hα_lint (t + 1)).trans_lt (by finiteness))
    exact single_le_sum (f := fun t ↦ ‖α t ω‖ₑ ^ 2) (fun _ _ ↦ bot_le) (self_mem_range_succ t)
  have hζ_lint (t : ℕ) :
      ∫⁻ ω, ‖α t ω * ξ t ω‖ₑ ^ 2 ∂P ≤ K * ∫⁻ ω, ‖α t ω‖ₑ ^ 2 ∂P := by
    simp_rw [eNorm_mul, mul_pow]
    have hG : Measurable[ℱ t] fun ω ↦ ‖α t ω‖ₑ ^ 2 := (measurable_eNorm.pow_const 2).comp (hα t)
    have hZ : AEMeasurable (fun ω ↦ ‖ξ t ω‖ₑ ^ 2) P := ((hξm t).eNorm.pow_const 2).aemeasurable
    rw [← TauCeti.MeasureTheory.lintegral_mul_condLExp (ℱ.le t) hZ hG,
      ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    exact lintegral_mono_ae ((hξ_var t).mono fun ω hω ↦ by
      rw [mul_comm (K : ℝ≥0∞)]
      exact mul_le_mul_right hω _)
  have hξ_lt (t : ℕ) : ∫⁻ ω, ‖ξ t ω‖ₑ ^ 2 ∂P < ∞ := by
    rw [← lintegral_condLExp (ℱ.le t)]
    exact (lintegral_mono_ae (hξ_var t)).trans_lt
      (by simpa using ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top P Set.univ))
  -- the martingale transform `S T = ∑ t < T, α t ξ t`
  set ζ : ℕ → Ω → ℝ := fun t ↦ α t * ξ t
  set S : ℕ → Ω → ℝ := fun T ω ↦ ∑ t ∈ range T, ζ t ω
  have hζm (t : ℕ) : Measurable[ℱ (t + 1)] (ζ t) :=
    ((hα t).mono (ℱ.mono t.le_succ) le_rfl).mul (hξ t)
  have hζ2 (t : ℕ) : MemLp (ζ t) 2 P :=
    ((hαm t).mul (hξm t)).aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.2
      ((hζ_lint t).trans_lt (by finiteness [hα_lt t]))
  have hξ2 (t : ℕ) : MemLp (ξ t) 2 P :=
    (hξm t).aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.2 (hξ_lt t)
  have hSm (T : ℕ) : Measurable[ℱ T] (S T) :=
    Finset.measurable_sum _ fun t ht ↦ (hζm t).mono (ℱ.mono (mem_range.1 ht)) le_rfl
  have hS2 (T : ℕ) : MemLp (S T) 2 P := memLp_finsetSum _ fun t _ ↦ hζ2 t
  have hζ_mean (T : ℕ) : P[ζ T | ℱ T] =ᵐ[P] 0 := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (hα T).stronglyMeasurable
      ((hζ2 T).integrable one_le_two) ((hξ2 T).integrable one_le_two), hξ_mean T] with ω h1 h2
    simp [ζ, h1, h2]
  -- the second moments of the martingale are bounded
  have hbdd (T : ℕ) : ∫⁻ ω, ‖S T ω‖ₑ ^ 2 ∂P ≤ K * (ENNReal.ofReal C * P Set.univ) := by
    simp_rw [Real.enorm_sq_eq_ofReal_sq]
    rw [← ofReal_integral_eq_lintegral_ofReal (hS2 T).integrable_sq
      (ae_of_all _ fun _ ↦ sq_nonneg _), integral_sq_sum_range_of_condExp_eq_zero hζm hζ2 hζ_mean,
      ENNReal.ofReal_sum_of_nonneg fun t _ ↦ integral_nonneg fun _ ↦ sq_nonneg _]
    calc ∑ t ∈ range T, ENNReal.ofReal (∫ ω, ζ t ω ^ 2 ∂P)
        = ∑ t ∈ range T, ∫⁻ ω, ‖ζ t ω‖ₑ ^ 2 ∂P := by
          refine sum_congr rfl fun t _ ↦ ?_
          simp_rw [Real.enorm_sq_eq_ofReal_sq]
          exact ofReal_integral_eq_lintegral_ofReal (hζ2 t).integrable_sq
            (ae_of_all _ fun _ ↦ sq_nonneg _)
      _ ≤ ∑ t ∈ range T, K * ∫⁻ ω, ‖α t ω‖ₑ ^ 2 ∂P := sum_le_sum fun t _ ↦ hζ_lint t
      _ = K * ∫⁻ ω, ∑ t ∈ range T, ‖α t ω‖ₑ ^ 2 ∂P := by
          rw [← mul_sum, lintegral_finsetSum _ fun t _ ↦ (hαm t).eNorm.pow_const 2]
      _ ≤ K * (ENNReal.ofReal C * P Set.univ) := mul_le_mul_right (hα_lint T) _
  have hL2 : ⨆ T, eLpNorm (S T) 2 P < ∞ := by
    refine (iSup_le fun T ↦ ?_).trans_lt (ENNReal.rpow_lt_top_of_nonneg (y := 1 / 2)
      (by norm_num) (by finiteness : K * (ENNReal.ofReal C * P Set.univ) ≠ ∞))
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (hS2 T).aestronglyMeasurable, ENNReal.toReal_ofNat]
    simp_rw [ENNReal.rpow_two]
    exact ENNReal.rpow_le_rpow (hbdd T) (by norm_num)
  have hmart : Martingale S ℱ P :=
    martingale_of_condExp_sub_eq_zero_nat (fun T ↦ (hSm T).stronglyMeasurable)
      (fun T ↦ (hS2 T).integrable one_le_two) fun T ↦ by
        have h : S (T + 1) - S T = ζ T := by
          ext ω
          simp [S, sum_range_succ]
        rw [h]
        exact hζ_mean T
  exact hmart.submartingale.exists_ae_tendsto_of_bdd_eLpNorm one_le_two hL2

end LMLExplore
