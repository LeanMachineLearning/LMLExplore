/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Log.TruncLog
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.EIntegral
import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner

/-!
# Monotone convergence for the truncations of an extended integral

Statlib's extended integral `∫ᵉ x, f x ∂μ` of a function `f` with values in `EReal` is the
difference of the lower Lebesgue integrals of its positive and negative parts. Truncating `f`
above at `k` leaves its negative part unchanged, and the positive parts of the truncations
`min f k` increase to that of `f`, so a bound on the extended integrals of the truncations is a
bound on the extended integral of `f`.

For `f = log E` with `E` nonnegative, the truncations are bounded by real integrals: mixing `E`
with a constant `ε ∈ (0, 1)` bounds its logarithm below, at a cost of at most `- log (1 - ε)`.

## Main statements

* `MeasureTheory.eintegral_le_of_forall_min_le`: if the extended integrals of the truncations
  `min f k`, `k ∈ ℕ`, are at most `D`, so is the extended integral of `f`.
* `MeasureTheory.eintegral_min_log_le_integral_truncLog_sub`: under a probability measure, the
  extended integral of `min (log E) k` is at most the integral of the truncated logarithm
  `ENNReal.truncLog k ((1 - ε) E + ε)`, minus `log (1 - ε)`.
* `MeasureTheory.exists_integrable_truncLog_lt_integral`: if the extended integral of `log f`
  exceeds a real `a`, and the negative part of `log f` has a finite mean, then so does the integral
  of the truncated logarithm `ENNReal.truncLog c f` for some level `c`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

/-- **Monotone convergence for truncations.** If the extended integrals of the truncations
`min f k`, `k ∈ ℕ`, are at most `D`, so is the extended integral of `f`. -/
theorem eintegral_le_of_forall_min_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → EReal} (hf : Measurable f) {D : EReal}
    (h : ∀ k : ℕ, ∫ᵉ x, min (f x) k ∂μ ≤ D) : ∫ᵉ x, f x ∂μ ≤ D := by
  have hmono : Monotone EReal.toENNReal := fun _ _ h ↦ EReal.toENNReal_le_toENNReal h
  have hpos (k : ℕ) (x : Ω) : (min (f x) k).toENNReal = min (f x).toENNReal k := by
    rw [hmono.map_min, show ((k : EReal)) = ((k : ℝ≥0∞) : EReal) by simp, EReal.toENNReal_coe]
  have hneg (k : ℕ) (x : Ω) : (-min (f x) k).toENNReal = (-f x).toENNReal := by
    by_cases hk : f x ≤ k
    · rw [min_eq_left hk]
    · rw [not_le] at hk
      have hk0 : (0 : EReal) ≤ k := by exact_mod_cast Nat.zero_le k
      rw [min_eq_right hk.le, EReal.toENNReal_of_nonpos (by simp),
        EReal.toENNReal_of_nonpos (by simpa using hk0.trans hk.le)]
  have h' (k : ℕ) : ((∫⁻ x, min (f x).toENNReal k ∂μ : ℝ≥0∞) : EReal) -
      ((∫⁻ x, (-f x).toENNReal ∂μ : ℝ≥0∞) : EReal) ≤ D := by
    have := h k
    simp only [eintegral, hpos, hneg] at this
    exact this
  have hm (k : ℕ) : Measurable fun x ↦ min (f x).toENNReal (k : ℝ≥0∞) :=
    (measurable_ereal_toENNReal.comp hf).min measurable_const
  have hmono' : Monotone fun (k : ℕ) x ↦ min (f x).toENNReal (k : ℝ≥0∞) :=
    fun k k' hkk' x ↦ min_le_min_left _ (by exact_mod_cast hkk')
  have hsup : ∫⁻ x, (f x).toENNReal ∂μ = ⨆ k : ℕ, ∫⁻ x, min (f x).toENNReal k ∂μ := by
    rw [← lintegral_iSup hm hmono']
    refine lintegral_congr fun x ↦ le_antisymm ?_ (iSup_le fun k ↦ min_le_left _ _)
    by_cases hx : (f x).toENNReal = ∞
    · simp [hx, ENNReal.iSup_natCast]
    · obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hx
      exact le_iSup_of_le k (min_eq_left hk.le).ge
  rw [eintegral, hsup]
  set b := ∫⁻ x, (-f x).toENNReal ∂μ
  by_cases hb : b = ∞
  · rw [hb, EReal.coe_ennreal_top, EReal.sub_top]
    exact bot_le
  have hb' : (b : EReal) ≠ ⊤ := by simpa using hb
  have hb'' : (b : EReal) ≠ ⊥ := by simp
  rw [EReal.sub_le_iff_le_add (.inl hb'') (.inl hb')]
  have hk (k : ℕ) : ((∫⁻ x, min (f x).toENNReal k ∂μ : ℝ≥0∞) : EReal) ≤ D + b :=
    (EReal.sub_le_iff_le_add (.inl hb'') (.inl hb')).1 (h' k)
  have hD : 0 ≤ D + b := (EReal.coe_ennreal_nonneg _).trans (hk 0)
  rw [← EReal.coe_toENNReal hD] at hk ⊢
  exact EReal.coe_ennreal_le_coe_ennreal_iff.2
    (iSup_le fun k ↦ EReal.coe_ennreal_le_coe_ennreal_iff.1 (hk k))

/-- Mixing with a constant, in expectation: the extended integral of the truncation at `k` of
`log E` is at most the integral of the truncated logarithm of `(1 - ε) E + ε`, minus
`log (1 - ε)`. -/
theorem eintegral_min_log_le_integral_truncLog_sub {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {E : Ω → ℝ≥0∞} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (k : ℕ) (hint : Integrable
      (fun x ↦ ENNReal.truncLog k (ENNReal.ofReal (1 - ε) * E x + ENNReal.ofReal ε)) μ) :
    ∫ᵉ x, min (ENNReal.log (E x)) k ∂μ ≤
      ((∫ x, ENNReal.truncLog k (ENNReal.ofReal (1 - ε) * E x + ENNReal.ofReal ε) ∂μ -
        Real.log (1 - ε) : ℝ) : EReal) := by
  calc ∫ᵉ x, min (ENNReal.log (E x)) k ∂μ
  _ ≤ ∫ᵉ x, ((ENNReal.truncLog k (ENNReal.ofReal (1 - ε) * E x + ENNReal.ofReal ε) -
      Real.log (1 - ε) : ℝ) : EReal) ∂μ := eintegral_mono fun x ↦ by
    have := ENNReal.min_log_le_truncLog_sub hε0 hε1 (k : ℝ) (E x)
    rwa [EReal.coe_natCast] at this
  _ = ((∫ x, (ENNReal.truncLog k (ENNReal.ofReal (1 - ε) * E x + ENNReal.ofReal ε) -
      Real.log (1 - ε)) ∂μ : ℝ) : EReal) :=
    eintegral_eq_integral (hint.sub (integrable_const _))
  _ = _ := by
    rw [integral_sub hint (integrable_const _), integral_const]
    simp

/-- **Truncation of an expected logarithm.** Let `f` be measurable, with a logarithm whose negative
part has a finite mean under a finite measure (so `f` is almost everywhere nonzero). If the extended
mean of `log f` exceeds `a`, then for some level `c` the logarithm truncated at `c` is integrable
with mean above `a`: the truncations at the levels `0, 1, 2, …` increase to `log f`. -/
theorem exists_integrable_truncLog_lt_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ≥0∞} (hf : Measurable f)
    (hneg : ∫⁻ x, (-ENNReal.log (f x)).toENNReal ∂μ ≠ ∞) {a : ℝ}
    (ha : (a : EReal) < ∫ᵉ x, ENNReal.log (f x) ∂μ) :
    ∃ c : ℝ, Integrable (fun x ↦ ENNReal.truncLog c (f x)) μ ∧
      a < ∫ x, ENNReal.truncLog c (f x) ∂μ := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (a : EReal) < ∫ᵉ x, min (ENNReal.log (f x)) (c : EReal) ∂μ := by
    by_contra! h
    exact absurd (eintegral_le_of_forall_min_le (ENNReal.measurable_log.comp hf) h) (not_le.2 ha)
  have hi := ENNReal.integrable_truncLog_comp_of_lintegral_ne_top hf hneg c
  refine ⟨c, hi, ?_⟩
  have heq : ∫ᵉ x, min (ENNReal.log (f x)) (c : EReal) ∂μ =
      ∫ᵉ x, (ENNReal.truncLog c (f x) : EReal) ∂μ := by
    refine eintegral_congr_ae ?_
    filter_upwards [ae_lt_top' (ENNReal.measurable_log.comp hf).neg.ereal_toENNReal.aemeasurable
      hneg] with x hx
    have hx0 : f x ≠ 0 := by
      rintro h0
      simp [h0] at hx
    rw [ENNReal.coe_truncLog hx0, EReal.coe_natCast]
  rw [heq, eintegral_eq_integral hi] at hc
  exact_mod_cast hc

end MeasureTheory
