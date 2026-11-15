/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.MultipleTesting.RunningMaxima

/-!
# E-BH on the running maxima of three test supermartingales

Let `M i`, for `i` in a finite type `ι` of three hypotheses, be test supermartingales for one
filtration, and let every hypothesis be true under `P`. This file proves that e-BH at level `α`
[WR22] applied to the running maxima `⨆ n, M i n` makes a rejection with probability at most
`3 * α / 2`, by the potential argument
`ProbabilityTheory.measure_exists_selfConsistent_le_of_key` of
`LMLExplore.EValues.MultipleTesting.RunningMaxima`.

## Main statements

* `ProbabilityTheory.measure_exists_selfConsistent_iSup_le_of_card_eq_three`: for three
  hypotheses, e-BH on the running maxima rejects with probability at most `3 * α / 2`.

## Implementation notes

The levels of a process, in units of the threshold, are `0`, `1`, `2` and `3`, cut at `1`,
`3 / 2` and `3`. The potential of each of the sixteen non-winning flag states is the minimum of
the constant `1` and of one to three affine forms, listed in `table3`. The key inequality is
checked state by state and cell by cell, by `linarith`.

## References

* [WR22] R. Wang and A. Ramdas, *False discovery rate control with e-values*, J. R. Stat. Soc.
  Ser. B 84 (2022), arXiv:2009.02824v5.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {P : Measure Ω}

/-! ### Three hypotheses -/

section Three

/-- The level of a value for three hypotheses, in units of the threshold: `3` from `3` on, `2`
on `[3 / 2, 3)`, `1` on `[1, 3 / 2)` and `0` below `1`. -/
private noncomputable def lev3 (x : ℝ≥0∞) : ℕ :=
  if 3 ≤ x then 3 else if 3 / 2 ≤ x then 2 else if 1 ≤ x then 1 else 0

/-- The level function for three hypotheses is monotone. -/
private lemma monotone_lev3 : Monotone lev3 := by
  intro x y hxy
  unfold lev3
  by_cases hx3 : 3 ≤ x
  · simp [hx3, hx3.trans hxy]
  by_cases hx2 : 3 / 2 ≤ x
  · simp only [hx3, hx2, hx2.trans hxy, ite_false, ite_true]
    split_ifs <;> omega
  by_cases hx1 : 1 ≤ x
  · simp only [hx3, hx2, hx1, hx1.trans hxy, ite_false, ite_true]
    split_ifs <;> omega
  · simp [hx3, hx2, hx1]

/-- The level of a real value for three hypotheses. -/
private lemma lev3_ofReal {x : ℝ} (hx : 0 ≤ x) :
    lev3 (ENNReal.ofReal x) =
      if 3 ≤ x then 3 else if 3 / 2 ≤ x then 2 else if 1 ≤ x then 1 else 0 := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal x ↔ 1 ≤ x := ENNReal.one_le_ofReal
  have h2 : (3 / 2 : ℝ≥0∞) ≤ ENNReal.ofReal x ↔ 3 / 2 ≤ x := by
    rw [← ENNReal.ofReal_le_ofReal_iff hx, ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  have h3 : (3 : ℝ≥0∞) ≤ ENNReal.ofReal x ↔ 3 ≤ x := by
    rw [← ENNReal.ofReal_ofNat 3, ENNReal.ofReal_le_ofReal_iff hx]
  unfold lev3
  simp only [h1, h2, h3]

/-- The levels of a real value from the flag `0`. -/
private lemma lev3_cases_zero {x : ℝ} (hx : 0 ≤ x) :
    (max 0 (lev3 (ENNReal.ofReal x)) = 0 ∧ 0 ≤ x ∧ x < 1) ∨
      (max 0 (lev3 (ENNReal.ofReal x)) = 1 ∧ 1 ≤ x ∧ x < 3 / 2) ∨
      (max 0 (lev3 (ENNReal.ofReal x)) = 2 ∧ 3 / 2 ≤ x ∧ x < 3) ∨
      (max 0 (lev3 (ENNReal.ofReal x)) = 3 ∧ 3 ≤ x ∧ 3 ≤ x) := by
  rw [lev3_ofReal hx]
  by_cases h3 : 3 ≤ x
  · exact Or.inr (Or.inr (Or.inr ⟨by simp [h3], h3, h3⟩))
  by_cases h2 : 3 / 2 ≤ x
  · exact Or.inr (Or.inr (Or.inl ⟨by simp [h3, h2], h2, not_le.1 h3⟩))
  by_cases h1 : 1 ≤ x
  · exact Or.inr (Or.inl ⟨by simp [h3, h2, h1], h1, not_le.1 h2⟩)
  · exact Or.inl ⟨by simp [h3, h2, h1], hx, not_le.1 h1⟩

/-- The levels of a real value from the flag `1`. -/
private lemma lev3_cases_one {x : ℝ} (hx : 0 ≤ x) :
    (max 1 (lev3 (ENNReal.ofReal x)) = 1 ∧ 0 ≤ x ∧ x < 3 / 2) ∨
      (max 1 (lev3 (ENNReal.ofReal x)) = 2 ∧ 3 / 2 ≤ x ∧ x < 3) ∨
      (max 1 (lev3 (ENNReal.ofReal x)) = 3 ∧ 3 ≤ x ∧ 3 ≤ x) := by
  rw [lev3_ofReal hx]
  by_cases h3 : 3 ≤ x
  · exact Or.inr (Or.inr ⟨by simp [h3], h3, h3⟩)
  by_cases h2 : 3 / 2 ≤ x
  · exact Or.inr (Or.inl ⟨by simp [h3, h2], h2, not_le.1 h3⟩)
  · exact Or.inl ⟨by simp only [h3, h2, ite_false]; split_ifs <;> simp, hx, not_le.1 h2⟩

/-- The levels of a real value from the flag `2`. -/
private lemma lev3_cases_two {x : ℝ} (hx : 0 ≤ x) :
    (max 2 (lev3 (ENNReal.ofReal x)) = 2 ∧ 0 ≤ x ∧ x < 3) ∨
      (max 2 (lev3 (ENNReal.ofReal x)) = 3 ∧ 3 ≤ x ∧ 3 ≤ x) := by
  rw [lev3_ofReal hx]
  by_cases h3 : 3 ≤ x
  · exact Or.inr ⟨by simp [h3], h3, h3⟩
  · exact Or.inl ⟨by simp only [h3, ite_false]; split_ifs <;> simp, hx, not_le.1 h3⟩

/-- The flags of three hypotheses win: one flag is `3`, or two are at least `2`, or all three
are at least `1`. -/
private def Wins3 (b : Fin 3 → ℕ) : Prop :=
  3 ≤ b 0 ∨ 3 ≤ b 1 ∨ 3 ≤ b 2 ∨ (2 ≤ b 0 ∧ 2 ≤ b 1) ∨ (2 ≤ b 0 ∧ 2 ≤ b 2) ∨
    (2 ≤ b 1 ∧ 2 ≤ b 2) ∨ (1 ≤ b 0 ∧ 1 ≤ b 1 ∧ 1 ≤ b 2)

/-- Winning for three hypotheses is decidable. -/
private instance : DecidablePred Wins3 := fun b ↦ by unfold Wins3; infer_instance

/-- The affine forms of the potential for three hypotheses in the sixteen non-winning flag
states, as pairs of coefficients and constant term. The form `0` and the unused forms are the
constant `1`. -/
private noncomputable def table3 : ℕ → ℕ → ℕ → Fin 4 → (Fin 3 → ℝ) × ℝ
  | 0, 0, 0 => ![(0, 1), (![1 / 2, 1 / 2, 1 / 2], 0), (0, 1), (0, 1)]
  | 0, 0, 1 => ![(0, 1), (![1 / 2, 1 / 2, 1 / 3], 1 / 6), (0, 1), (0, 1)]
  | 0, 0, 2 => ![(0, 1), (![2 / 3, 1, 1 / 3], 0), (![1, 2 / 3, 1 / 3], 0),
      (![3 / 4, 3 / 4, 1 / 3], 0)]
  | 0, 1, 0 => ![(0, 1), (![1 / 2, 1 / 3, 1 / 2], 1 / 6), (0, 1), (0, 1)]
  | 0, 1, 1 => ![(0, 1), (![1, 1 / 3, 2 / 3], 0), (![1, 2 / 3, 1 / 3], 0), (0, 1)]
  | 0, 1, 2 => ![(0, 1), (![1, 2 / 3, 1 / 3], 0), (0, 1), (0, 1)]
  | 0, 2, 0 => ![(0, 1), (![2 / 3, 1 / 3, 1], 0), (![1, 1 / 3, 2 / 3], 0),
      (![3 / 4, 1 / 3, 3 / 4], 0)]
  | 0, 2, 1 => ![(0, 1), (![1, 1 / 3, 2 / 3], 0), (0, 1), (0, 1)]
  | 1, 0, 0 => ![(0, 1), (![1 / 3, 1 / 2, 1 / 2], 1 / 6), (0, 1), (0, 1)]
  | 1, 0, 1 => ![(0, 1), (![1 / 3, 1, 2 / 3], 0), (![2 / 3, 1, 1 / 3], 0), (0, 1)]
  | 1, 0, 2 => ![(0, 1), (![2 / 3, 1, 1 / 3], 0), (0, 1), (0, 1)]
  | 1, 1, 0 => ![(0, 1), (![1 / 3, 2 / 3, 1], 0), (![2 / 3, 1 / 3, 1], 0), (0, 1)]
  | 1, 2, 0 => ![(0, 1), (![2 / 3, 1 / 3, 1], 0), (0, 1), (0, 1)]
  | 2, 0, 0 => ![(0, 1), (![1 / 3, 2 / 3, 1], 0), (![1 / 3, 1, 2 / 3], 0),
      (![1 / 3, 3 / 4, 3 / 4], 0)]
  | 2, 0, 1 => ![(0, 1), (![1 / 3, 1, 2 / 3], 0), (0, 1), (0, 1)]
  | 2, 1, 0 => ![(0, 1), (![1 / 3, 2 / 3, 1], 0), (0, 1), (0, 1)]
  | _, _, _ => fun _ ↦ (0, 1)

/-- The coefficients of the affine forms of the potential for three hypotheses: those of
`table3` in a non-winning state, `0` in a winning state and for the form `0`. -/
private noncomputable def coef3 (b : Fin 3 → ℕ) (j : Fin 4) : Fin 3 → ℝ :=
  if j = 0 ∨ Wins3 b then 0 else (table3 (b 0) (b 1) (b 2) j).1

/-- The constant terms of the affine forms of the potential for three hypotheses: those of
`table3` in a non-winning state, `1` in a winning state and for the form `0`. -/
private noncomputable def const3 (b : Fin 3 → ℕ) (j : Fin 4) : ℝ :=
  if j = 0 ∨ Wins3 b then 1 else (table3 (b 0) (b 1) (b 2) j).2

/-- The affine form `j` of the potential for three hypotheses in the flag state `b`, at `r`. -/
private noncomputable def ell3 (b : Fin 3 → ℕ) (j : Fin 4) (r : Fin 3 → ℝ) : ℝ :=
  ∑ i, coef3 b j i * r i + const3 b j

/-- The form `0` of the potential for three hypotheses is the constant `1`. -/
private lemma ell3_zero (b : Fin 3 → ℕ) (r : Fin 3 → ℝ) : ell3 b 0 r = 1 := by
  simp [ell3, coef3, const3]

/-- The flag state reached from the flag state `b` of three hypotheses by moving to `r`. -/
private noncomputable def step3 (b : Fin 3 → ℕ) (r : Fin 3 → ℝ) : Fin 3 → ℕ :=
  b ⊔ fun i ↦ lev3 (ENNReal.ofReal (r i))

/-- The flag state reached from `b` by moving to `r`, from its three coordinates. -/
private lemma step3_eq {b : Fin 3 → ℕ} {r : Fin 3 → ℝ} {c₀ c₁ c₂ : ℕ}
    (h0 : max (b 0) (lev3 (ENNReal.ofReal (r 0))) = c₀)
    (h1 : max (b 1) (lev3 (ENNReal.ofReal (r 1))) = c₁)
    (h2 : max (b 2) (lev3 (ENNReal.ofReal (r 2))) = c₂) : step3 b r = ![c₀, c₁, c₂] := by
  funext i
  fin_cases i
  exacts [h0, h1, h2]

/-- The affine forms of the potential for three hypotheses have nonnegative coefficients and
constant terms, and each of them either has constant term at least `1` or has positive
coefficients. -/
private lemma coef3_props (b : Fin 3 → ℕ) (j : Fin 4) :
    (∀ i, 0 ≤ coef3 b j i) ∧ 0 ≤ const3 b j ∧ (1 ≤ const3 b j ∨ ∀ i, 0 < coef3 b j i) := by
  unfold coef3 const3
  split_ifs with h
  · simp
  obtain ⟨hj, hb⟩ := not_or.1 h
  obtain ⟨b₀, b₁, b₂, rfl⟩ : ∃ b₀ b₁ b₂ : ℕ, b = ![b₀, b₁, b₂] :=
    ⟨b 0, b 1, b 2, by funext i; fin_cases i <;> rfl⟩
  have h₀ : b₀ ≤ 2 := by by_contra! h; exact hb (Or.inl h)
  have h₁ : b₁ ≤ 2 := by by_contra! h; exact hb (Or.inr (Or.inl h))
  have h₂ : b₂ ≤ 2 := by by_contra! h; exact hb (Or.inr (Or.inr (Or.inl h)))
  interval_cases b₀ <;> interval_cases b₁ <;> interval_cases b₂ <;>
    first
    | exact absurd (by decide) hb
    | fin_cases j <;> first | exact absurd rfl hj | norm_num [table3, Fin.forall_fin_succ]

/-! ### The forms in the non-winning states -/

/-- The form `1` of the potential for three hypotheses in the flag state `![0, 0, 0]`. -/
private lemma ell3_000_1 (r : Fin 3 → ℝ) :
    ell3 ![0, 0, 0] 1 r = r 0 / 2 + r 1 / 2 + r 2 / 2 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `1` of the potential for three hypotheses in the flag state `![0, 0, 1]`. -/
private lemma ell3_001_1 (r : Fin 3 → ℝ) :
    ell3 ![0, 0, 1] 1 r = r 0 / 2 + r 1 / 2 + r 2 / 3 + 1 / 6 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `1` of the potential for three hypotheses in the flag state `![0, 0, 2]`. -/
private lemma ell3_002_1 (r : Fin 3 → ℝ) :
    ell3 ![0, 0, 2] 1 r = 2 * r 0 / 3 + r 1 + r 2 / 3 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `2` of the potential for three hypotheses in the flag state `![0, 0, 2]`. -/
private lemma ell3_002_2 (r : Fin 3 → ℝ) :
    ell3 ![0, 0, 2] 2 r = r 0 + 2 * r 1 / 3 + r 2 / 3 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `3` of the potential for three hypotheses in the flag state `![0, 0, 2]`. -/
private lemma ell3_002_3 (r : Fin 3 → ℝ) :
    ell3 ![0, 0, 2] 3 r = 3 * r 0 / 4 + 3 * r 1 / 4 + r 2 / 3 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `1` of the potential for three hypotheses in the flag state `![0, 1, 0]`. -/
private lemma ell3_010_1 (r : Fin 3 → ℝ) :
    ell3 ![0, 1, 0] 1 r = r 0 / 2 + r 1 / 3 + r 2 / 2 + 1 / 6 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `1` of the potential for three hypotheses in the flag state `![0, 1, 1]`. -/
private lemma ell3_011_1 (r : Fin 3 → ℝ) :
    ell3 ![0, 1, 1] 1 r = r 0 + r 1 / 3 + 2 * r 2 / 3 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `2` of the potential for three hypotheses in the flag state `![0, 1, 1]`. -/
private lemma ell3_011_2 (r : Fin 3 → ℝ) :
    ell3 ![0, 1, 1] 2 r = r 0 + 2 * r 1 / 3 + r 2 / 3 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `1` of the potential for three hypotheses in the flag state `![0, 1, 2]`. -/
private lemma ell3_012_1 (r : Fin 3 → ℝ) :
    ell3 ![0, 1, 2] 1 r = r 0 + 2 * r 1 / 3 + r 2 / 3 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `1` of the potential for three hypotheses in the flag state `![0, 2, 0]`. -/
private lemma ell3_020_1 (r : Fin 3 → ℝ) :
    ell3 ![0, 2, 0] 1 r = 2 * r 0 / 3 + r 1 / 3 + r 2 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `2` of the potential for three hypotheses in the flag state `![0, 2, 0]`. -/
private lemma ell3_020_2 (r : Fin 3 → ℝ) :
    ell3 ![0, 2, 0] 2 r = r 0 + r 1 / 3 + 2 * r 2 / 3 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `3` of the potential for three hypotheses in the flag state `![0, 2, 0]`. -/
private lemma ell3_020_3 (r : Fin 3 → ℝ) :
    ell3 ![0, 2, 0] 3 r = 3 * r 0 / 4 + r 1 / 3 + 3 * r 2 / 4 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `1` of the potential for three hypotheses in the flag state `![0, 2, 1]`. -/
private lemma ell3_021_1 (r : Fin 3 → ℝ) :
    ell3 ![0, 2, 1] 1 r = r 0 + r 1 / 3 + 2 * r 2 / 3 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `1` of the potential for three hypotheses in the flag state `![1, 0, 0]`. -/
private lemma ell3_100_1 (r : Fin 3 → ℝ) :
    ell3 ![1, 0, 0] 1 r = r 0 / 3 + r 1 / 2 + r 2 / 2 + 1 / 6 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `1` of the potential for three hypotheses in the flag state `![1, 0, 1]`. -/
private lemma ell3_101_1 (r : Fin 3 → ℝ) :
    ell3 ![1, 0, 1] 1 r = r 0 / 3 + r 1 + 2 * r 2 / 3 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `2` of the potential for three hypotheses in the flag state `![1, 0, 1]`. -/
private lemma ell3_101_2 (r : Fin 3 → ℝ) :
    ell3 ![1, 0, 1] 2 r = 2 * r 0 / 3 + r 1 + r 2 / 3 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `1` of the potential for three hypotheses in the flag state `![1, 0, 2]`. -/
private lemma ell3_102_1 (r : Fin 3 → ℝ) :
    ell3 ![1, 0, 2] 1 r = 2 * r 0 / 3 + r 1 + r 2 / 3 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `1` of the potential for three hypotheses in the flag state `![1, 1, 0]`. -/
private lemma ell3_110_1 (r : Fin 3 → ℝ) :
    ell3 ![1, 1, 0] 1 r = r 0 / 3 + 2 * r 1 / 3 + r 2 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `2` of the potential for three hypotheses in the flag state `![1, 1, 0]`. -/
private lemma ell3_110_2 (r : Fin 3 → ℝ) :
    ell3 ![1, 1, 0] 2 r = 2 * r 0 / 3 + r 1 / 3 + r 2 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `1` of the potential for three hypotheses in the flag state `![1, 2, 0]`. -/
private lemma ell3_120_1 (r : Fin 3 → ℝ) :
    ell3 ![1, 2, 0] 1 r = 2 * r 0 / 3 + r 1 / 3 + r 2 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `1` of the potential for three hypotheses in the flag state `![2, 0, 0]`. -/
private lemma ell3_200_1 (r : Fin 3 → ℝ) :
    ell3 ![2, 0, 0] 1 r = r 0 / 3 + 2 * r 1 / 3 + r 2 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `2` of the potential for three hypotheses in the flag state `![2, 0, 0]`. -/
private lemma ell3_200_2 (r : Fin 3 → ℝ) :
    ell3 ![2, 0, 0] 2 r = r 0 / 3 + r 1 + 2 * r 2 / 3 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `3` of the potential for three hypotheses in the flag state `![2, 0, 0]`. -/
private lemma ell3_200_3 (r : Fin 3 → ℝ) :
    ell3 ![2, 0, 0] 3 r = r 0 / 3 + 3 * r 1 / 4 + 3 * r 2 / 4 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `1` of the potential for three hypotheses in the flag state `![2, 0, 1]`. -/
private lemma ell3_201_1 (r : Fin 3 → ℝ) :
    ell3 ![2, 0, 1] 1 r = r 0 / 3 + r 1 + 2 * r 2 / 3 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The form `1` of the potential for three hypotheses in the flag state `![2, 1, 0]`. -/
private lemma ell3_210_1 (r : Fin 3 → ℝ) :
    ell3 ![2, 1, 0] 1 r = r 0 / 3 + 2 * r 1 / 3 + r 2 := by
  simp [ell3, coef3, const3, table3, Wins3, Fin.sum_univ_three]
  ring

/-- The four affine forms of a flag state. -/
private lemma fin_four_cases (j : Fin 4) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
  fin_cases j <;> simp

/-! ### The key inequality in the non-winning states -/

/-- The key inequality for three hypotheses in the flag state `![0, 0, 0]`. -/
private lemma key3_000 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![0, 0, 0] r) j' r ≤ ell3 ![0, 0, 0] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_000_1] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_zero (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_zero (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_000_1 r]
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_001_1 r]
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_002_1 r, h 2, ell3_002_2 r, h 3, ell3_002_3 r]
          · linarith
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_010_1 r]
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_011_1 r, h 2, ell3_011_2 r]
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_012_1 r]
          · linarith
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_020_1 r, h 2, ell3_020_2 r, h 3, ell3_020_3 r]
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_021_1 r]
          all_goals linarith
        · linarith
      · rcases lev3_cases_zero (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_100_1 r]
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_101_1 r, h 2, ell3_101_2 r]
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_102_1 r]
          · linarith
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_110_1 r, h 2, ell3_110_2 r]
          all_goals linarith
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_120_1 r]
          all_goals linarith
        · linarith
      · rcases lev3_cases_zero (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_200_1 r, h 2, ell3_200_2 r, h 3, ell3_200_3 r]
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_201_1 r]
          all_goals linarith
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_210_1 r]
          all_goals linarith
        all_goals linarith
      · linarith

/-- The key inequality for three hypotheses in the flag state `![0, 0, 1]`. -/
private lemma key3_001 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![0, 0, 1] r) j' r ≤ ell3 ![0, 0, 1] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_001_1] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_zero (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_zero (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_one (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_001_1 r]
          · rw [step3_eq (b := ![0, 0, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_002_1 r, h 2, ell3_002_2 r, h 3, ell3_002_3 r]
          · linarith
        · rcases lev3_cases_one (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_011_1 r, h 2, ell3_011_2 r]
          · rw [step3_eq (b := ![0, 0, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_012_1 r]
          · linarith
        · rcases lev3_cases_one (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_021_1 r]
          all_goals linarith
        · linarith
      · rcases lev3_cases_zero (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_one (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_101_1 r, h 2, ell3_101_2 r]
          · rw [step3_eq (b := ![0, 0, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_102_1 r]
          · linarith
        all_goals linarith
      · rcases lev3_cases_zero (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_one (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_201_1 r]
          all_goals linarith
        all_goals linarith
      · linarith

/-- The key inequality for three hypotheses in the flag state `![0, 0, 2]`. -/
private lemma key3_002 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![0, 0, 2] r) j' r ≤ ell3 ![0, 0, 2] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_002_1, ell3_002_2, ell3_002_3] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_zero (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_zero (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_two (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 2]) l0 l1 l2] at h
            linarith [h 1, ell3_002_1 r, h 2, ell3_002_2 r, h 3, ell3_002_3 r]
          · linarith
        · rcases lev3_cases_two (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 2]) l0 l1 l2] at h
            linarith [h 1, ell3_012_1 r]
          · linarith
        all_goals linarith
      · rcases lev3_cases_zero (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_two (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 0, 2]) l0 l1 l2] at h
            linarith [h 1, ell3_102_1 r]
          · linarith
        all_goals linarith
      all_goals linarith

/-- The key inequality for three hypotheses in the flag state `![0, 1, 0]`. -/
private lemma key3_010 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![0, 1, 0] r) j' r ≤ ell3 ![0, 1, 0] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_010_1] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_zero (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_one (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 1, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_010_1 r]
          · rw [step3_eq (b := ![0, 1, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_011_1 r, h 2, ell3_011_2 r]
          · rw [step3_eq (b := ![0, 1, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_012_1 r]
          · linarith
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 1, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_020_1 r, h 2, ell3_020_2 r, h 3, ell3_020_3 r]
          · rw [step3_eq (b := ![0, 1, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_021_1 r]
          all_goals linarith
        · linarith
      · rcases lev3_cases_one (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 1, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_110_1 r, h 2, ell3_110_2 r]
          all_goals linarith
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 1, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_120_1 r]
          all_goals linarith
        · linarith
      · rcases lev3_cases_one (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 1, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_210_1 r]
          all_goals linarith
        all_goals linarith
      · linarith

/-- The key inequality for three hypotheses in the flag state `![0, 1, 1]`. -/
private lemma key3_011 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![0, 1, 1] r) j' r ≤ ell3 ![0, 1, 1] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_011_1, ell3_011_2] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_zero (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_one (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_one (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 1, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_011_1 r, h 2, ell3_011_2 r]
          · rw [step3_eq (b := ![0, 1, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_012_1 r]
          · linarith
        · rcases lev3_cases_one (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 1, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_021_1 r]
          all_goals linarith
        · linarith
      all_goals linarith

/-- The key inequality for three hypotheses in the flag state `![0, 1, 2]`. -/
private lemma key3_012 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![0, 1, 2] r) j' r ≤ ell3 ![0, 1, 2] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_012_1] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_zero (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_one (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_two (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 1, 2]) l0 l1 l2] at h
            linarith [h 1, ell3_012_1 r]
          · linarith
        all_goals linarith
      all_goals linarith

/-- The key inequality for three hypotheses in the flag state `![0, 2, 0]`. -/
private lemma key3_020 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![0, 2, 0] r) j' r ≤ ell3 ![0, 2, 0] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_020_1, ell3_020_2, ell3_020_3] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_zero (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_two (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 2, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_020_1 r, h 2, ell3_020_2 r, h 3, ell3_020_3 r]
          · rw [step3_eq (b := ![0, 2, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_021_1 r]
          all_goals linarith
        · linarith
      · rcases lev3_cases_two (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 2, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_120_1 r]
          all_goals linarith
        · linarith
      all_goals linarith

/-- The key inequality for three hypotheses in the flag state `![0, 2, 1]`. -/
private lemma key3_021 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![0, 2, 1] r) j' r ≤ ell3 ![0, 2, 1] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_021_1] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_zero (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_two (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_one (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![0, 2, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_021_1 r]
          all_goals linarith
        · linarith
      all_goals linarith

/-- The key inequality for three hypotheses in the flag state `![1, 0, 0]`. -/
private lemma key3_100 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![1, 0, 0] r) j' r ≤ ell3 ![1, 0, 0] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_100_1] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_one (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_zero (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![1, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_100_1 r]
          · rw [step3_eq (b := ![1, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_101_1 r, h 2, ell3_101_2 r]
          · rw [step3_eq (b := ![1, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_102_1 r]
          · linarith
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![1, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_110_1 r, h 2, ell3_110_2 r]
          all_goals linarith
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![1, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_120_1 r]
          all_goals linarith
        · linarith
      · rcases lev3_cases_zero (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![1, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_200_1 r, h 2, ell3_200_2 r, h 3, ell3_200_3 r]
          · rw [step3_eq (b := ![1, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_201_1 r]
          all_goals linarith
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![1, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_210_1 r]
          all_goals linarith
        all_goals linarith
      · linarith

/-- The key inequality for three hypotheses in the flag state `![1, 0, 1]`. -/
private lemma key3_101 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![1, 0, 1] r) j' r ≤ ell3 ![1, 0, 1] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_101_1, ell3_101_2] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_one (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_zero (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_one (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![1, 0, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_101_1 r, h 2, ell3_101_2 r]
          · rw [step3_eq (b := ![1, 0, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_102_1 r]
          · linarith
        all_goals linarith
      · rcases lev3_cases_zero (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_one (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![1, 0, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_201_1 r]
          all_goals linarith
        all_goals linarith
      · linarith

/-- The key inequality for three hypotheses in the flag state `![1, 0, 2]`. -/
private lemma key3_102 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![1, 0, 2] r) j' r ≤ ell3 ![1, 0, 2] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_102_1] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_one (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_zero (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_two (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![1, 0, 2]) l0 l1 l2] at h
            linarith [h 1, ell3_102_1 r]
          · linarith
        all_goals linarith
      all_goals linarith

/-- The key inequality for three hypotheses in the flag state `![1, 1, 0]`. -/
private lemma key3_110 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![1, 1, 0] r) j' r ≤ ell3 ![1, 1, 0] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_110_1, ell3_110_2] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_one (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_one (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![1, 1, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_110_1 r, h 2, ell3_110_2 r]
          all_goals linarith
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![1, 1, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_120_1 r]
          all_goals linarith
        · linarith
      · rcases lev3_cases_one (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![1, 1, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_210_1 r]
          all_goals linarith
        all_goals linarith
      · linarith

/-- The key inequality for three hypotheses in the flag state `![1, 2, 0]`. -/
private lemma key3_120 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![1, 2, 0] r) j' r ≤ ell3 ![1, 2, 0] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_120_1] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_one (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_two (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![1, 2, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_120_1 r]
          all_goals linarith
        · linarith
      all_goals linarith

/-- The key inequality for three hypotheses in the flag state `![2, 0, 0]`. -/
private lemma key3_200 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![2, 0, 0] r) j' r ≤ ell3 ![2, 0, 0] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_200_1, ell3_200_2, ell3_200_3] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_two (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_zero (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![2, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_200_1 r, h 2, ell3_200_2 r, h 3, ell3_200_3 r]
          · rw [step3_eq (b := ![2, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_201_1 r]
          all_goals linarith
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![2, 0, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_210_1 r]
          all_goals linarith
        all_goals linarith
      · linarith

/-- The key inequality for three hypotheses in the flag state `![2, 0, 1]`. -/
private lemma key3_201 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![2, 0, 1] r) j' r ≤ ell3 ![2, 0, 1] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_201_1] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_two (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_zero (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_one (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![2, 0, 1]) l0 l1 l2] at h
            linarith [h 1, ell3_201_1 r]
          all_goals linarith
        all_goals linarith
      · linarith

/-- The key inequality for three hypotheses in the flag state `![2, 1, 0]`. -/
private lemma key3_210 (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ell3 (step3 ![2, 1, 0] r) j' r ≤ ell3 ![2, 1, 0] j r := by
  rcases fin_four_cases j with rfl | rfl | rfl | rfl
  all_goals first
    | refine ⟨0, ?_⟩
      simp [ell3, coef3, const3, table3, Wins3]
      done
    | by_contra! h
      simp only [ell3_210_1] at h
      have h0 := h 0
      rw [ell3_zero] at h0
      obtain ⟨_, _, _⟩ : 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 := ⟨hr 0, hr 1, hr 2⟩
      rcases lev3_cases_two (hr 0) with ⟨l0, _, _⟩ | ⟨l0, _, _⟩
      · rcases lev3_cases_one (hr 1) with ⟨l1, _, _⟩ | ⟨l1, _, _⟩ | ⟨l1, _, _⟩
        · rcases lev3_cases_zero (hr 2) with ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩ | ⟨l2, _, _⟩
          · rw [step3_eq (b := ![2, 1, 0]) l0 l1 l2] at h
            linarith [h 1, ell3_210_1 r]
          all_goals linarith
        all_goals linarith
      · linarith

/-- **Key inequality for three hypotheses**, at real points: from every flag state `b`, every
affine form of the potential dominates at every point `r` one of the forms of the state reached
by moving to `r`. -/
private lemma key3_real (b : Fin 3 → ℕ) (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ∑ i, coef3 (b ⊔ fun i ↦ lev3 (ENNReal.ofReal (r i))) j' i * r i +
      const3 (b ⊔ fun i ↦ lev3 (ENNReal.ofReal (r i))) j' ≤
        ∑ i, coef3 b j i * r i + const3 b j := by
  by_cases hb : Wins3 b
  · exact ⟨0, by simp [coef3, const3, hb]⟩
  change ∃ j', ell3 (step3 b r) j' r ≤ ell3 b j r
  obtain ⟨b₀, b₁, b₂, rfl⟩ : ∃ b₀ b₁ b₂ : ℕ, b = ![b₀, b₁, b₂] :=
    ⟨b 0, b 1, b 2, by funext i; fin_cases i <;> rfl⟩
  have h₀ : b₀ ≤ 2 := by by_contra! h; exact hb (Or.inl h)
  have h₁ : b₁ ≤ 2 := by by_contra! h; exact hb (Or.inr (Or.inl h))
  have h₂ : b₂ ≤ 2 := by by_contra! h; exact hb (Or.inr (Or.inr (Or.inl h)))
  interval_cases b₀ <;> interval_cases b₁ <;> interval_cases b₂
  · exact key3_000 j r hr
  · exact key3_001 j r hr
  · exact key3_002 j r hr
  · exact key3_010 j r hr
  · exact key3_011 j r hr
  · exact key3_012 j r hr
  · exact key3_020 j r hr
  · exact key3_021 j r hr
  · exact absurd (by decide) hb
  · exact key3_100 j r hr
  · exact key3_101 j r hr
  · exact key3_102 j r hr
  · exact key3_110 j r hr
  · exact absurd (by decide) hb
  · exact absurd (by decide) hb
  · exact key3_120 j r hr
  · exact absurd (by decide) hb
  · exact absurd (by decide) hb
  · exact key3_200 j r hr
  · exact key3_201 j r hr
  · exact absurd (by decide) hb
  · exact key3_210 j r hr
  · exact absurd (by decide) hb
  · exact absurd (by decide) hb
  · exact absurd (by decide) hb
  · exact absurd (by decide) hb
  · exact absurd (by decide) hb

/-- The level function for three hypotheses reaches `4 - k` above the e-BH threshold `3 / k`. -/
private lemma le_lev3 (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ Fintype.card (Fin 3)) (x : ℝ≥0∞)
    (hx : (Fintype.card (Fin 3) : ℝ≥0∞) / k < x) : Fintype.card (Fin 3) + 1 - k ≤ lev3 x := by
  simp only [Fintype.card_fin] at hk3 hx ⊢
  interval_cases k
  · have : 3 ≤ x := by simpa using hx.le
    simp [lev3, this]
  · have : 3 / 2 ≤ x := by simpa using hx.le
    unfold lev3
    split_ifs <;> omega
  · have : 1 ≤ x := by
      simpa [ENNReal.div_self (three_ne_zero) ENNReal.ofNat_ne_top] using hx.le
    unfold lev3
    split_ifs <;> omega

/-- The winning flags for three hypotheses form an upper set. -/
private lemma isUpperSet_wins3 : IsUpperSet {b | Wins3 b} := by
  intro a b hab ha
  have h0 : a 0 ≤ b 0 := hab 0
  have h1 : a 1 ≤ b 1 := hab 1
  have h2 : a 2 ≤ b 2 := hab 2
  simp only [Set.mem_ofPred_eq, Wins3] at ha ⊢
  omega

/-- The bound `3 * α / 2` for three test supermartingales indexed by `Fin 3`. -/
private lemma measure_exists_selfConsistent_iSup_fin_three_le {M : Fin 3 → ℕ → Ω → ℝ≥0∞}
    (hM : ∀ i, IsTestSupermartingale (M i) ℱ {P}) (α : ℝ≥0∞) :
    P {ω | ∃ R : Finset (Fin 3), R.Nonempty ∧
      ∀ i ∈ R, (Fintype.card (Fin 3) : ℝ≥0∞) ≤ α * R.card * ⨆ n, M i n ω} ≤ 3 * α / 2 := by
  have h := measure_exists_selfConsistent_le_of_key hM monotone_lev3.measurable le_lev3
    (C := coef3) (C₀ := const3)
    (fun b j ↦ (coef3_props b j).1) (fun b j ↦ (coef3_props b j).2.1)
    (fun b j ↦ (coef3_props b j).2.2)
    (j₀ := 0) (fun b ↦ by simp [coef3, const3]) key3_real isUpperSet_wins3
    (by simp only [Fintype.card_fin]; decide)
    (fun b hb j ↦ by simp [const3, show Wins3 b from hb]) 1 (by simp [const3, Wins3, table3])
    (q := 3 / 2) (by norm_num) (by norm_num [coef3, Wins3, table3, Fin.sum_univ_three]) α
  rw [ENNReal.ofReal_div_of_pos (by norm_num)] at h
  simpa [ENNReal.div_eq_inv_mul, mul_comm, mul_left_comm] using h

end Three

/-! ### The bound -/

/-- **E-BH on the running maxima of three test supermartingales.** Let `M i` be test
supermartingales for one filtration and nulls `H i`, for three hypotheses, all true under `P`.
E-BH at level `α` applied to the running maxima `⨆ n, M i n` makes a rejection, that is, some
nonempty set `R` of hypotheses has `3 ≤ α * #R * ⨆ n, M i n ω` for every `i ∈ R`, with
probability at most `3 * α / 2`. The measure `P` need not be a probability measure. -/
theorem measure_exists_selfConsistent_iSup_le_of_card_eq_three {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = 3) {H : ι → Set (Measure Ω)} {M : ι → ℕ → Ω → ℝ≥0∞}
    (hM : ∀ i, IsTestSupermartingale (M i) ℱ (H i)) (hP : ∀ i, P ∈ H i) (α : ℝ≥0∞) :
    P {ω | ∃ R : Finset ι, R.Nonempty ∧
      ∀ i ∈ R, (Fintype.card ι : ℝ≥0∞) ≤ α * R.card * ⨆ n, M i n ω} ≤ 3 * α / 2 :=
  (measure_exists_selfConsistent_le_of_equiv (Fintype.equivFinOfCardEq hι) M α).trans
    (measure_exists_selfConsistent_iSup_fin_three_le
      (fun _ ↦ (hM _).anti_set (Set.singleton_subset_iff.2 (hP _))) α)

end ProbabilityTheory
