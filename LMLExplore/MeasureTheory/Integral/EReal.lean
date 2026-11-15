/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.EIntegral

/-!
# Monotone convergence for the truncations of an extended integral

Statlib's extended integral `∫ᵉ x, f x ∂μ` of a function `f` with values in `EReal` is the
difference of the lower Lebesgue integrals of its positive and negative parts. Truncating `f`
above at `k` leaves its negative part unchanged, and the positive parts of the truncations
`min f k` increase to that of `f`, so a bound on the extended integrals of the truncations is a
bound on the extended integral of `f`.

## Main statements

* `MeasureTheory.eintegral_le_of_forall_min_le`: if the extended integrals of the truncations
  `min f k`, `k ∈ ℕ`, are at most `D`, so is the extended integral of `f`.
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

end MeasureTheory
