/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exponential of the norm and of the coordinates in an orthonormal basis

The exponential `exp (c ‖y‖)` of a multiple of the norm of a vector of a finite-dimensional real
inner product space is bounded by a sum of exponentials of its coordinates `⟪b i, y⟫` in an
orthonormal basis `b`. This reduces the control of the exponential moments `exp (c ‖T‖)` of a
vector statistic `T` to the real exponential moments of its coordinates. It follows from Mathlib's
`OrthonormalBasis.norm_le_card_mul_iSup_norm_inner`.

## Main statements

* `OrthonormalBasis.exp_mul_norm_le`: for `c : ℝ`, with `n` the cardinality of the index type,
  `exp (c ‖y‖) ≤ 1 + ∑ i, (exp (c √n ⟪b i, y⟫) + exp (-(c √n ⟪b i, y⟫)))`.
-/

public section

open Real

open scoped RealInnerProductSpace

namespace OrthonormalBasis

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exponential of a multiple `c ‖y‖` of the norm of a vector is at most
`1 + ∑ i, (exp (c √n ⟪b i, y⟫) + exp (-(c √n ⟪b i, y⟫)))`, where `n` is the cardinality of the
index type of the orthonormal basis `b`. -/
lemma exp_mul_norm_le (b : OrthonormalBasis ι ℝ E) (c : ℝ) (y : E) :
    exp (c * ‖y‖) ≤ 1 + ∑ i, (exp (c * √(Fintype.card ι) * ⟪b i, y⟫) +
      exp (-(c * √(Fintype.card ι) * ⟪b i, y⟫))) := by
  rcases lt_or_ge c 0 with hc | hc
  · -- For `c < 0`, the left side is at most `1`.
    calc exp (c * ‖y‖) ≤ 1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hc.le (by simp))
    _ ≤ _ := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ by positivity)
  have h_norm := b.norm_le_card_mul_iSup_norm_inner y
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Fintype.card_eq_zero, CharP.cast_eq_zero, sqrt_zero, zero_mul, norm_le_zero_iff]
      at h_norm
    simp [h_norm]
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ ‖⟪b i, y⟫‖)
  rw [← hi, norm_eq_abs] at h_norm
  calc exp (c * ‖y‖) ≤ exp |c * √(Fintype.card ι) * ⟪b i, y⟫| := by
        rw [abs_mul, abs_of_nonneg (by positivity), mul_assoc]
        gcongr
  _ ≤ exp (c * √(Fintype.card ι) * ⟪b i, y⟫) + exp (-(c * √(Fintype.card ι) * ⟪b i, y⟫)) :=
        exp_abs_le _
  _ ≤ ∑ j, (exp (c * √(Fintype.card ι) * ⟪b j, y⟫) +
        exp (-(c * √(Fintype.card ι) * ⟪b j, y⟫))) :=
        Finset.single_le_sum (f := fun j ↦ exp (c * √(Fintype.card ι) * ⟪b j, y⟫) +
          exp (-(c * √(Fintype.card ι) * ⟪b j, y⟫))) (fun j _ ↦ by positivity) (Finset.mem_univ i)
  _ ≤ _ := le_add_of_nonneg_left zero_le_one

end OrthonormalBasis
