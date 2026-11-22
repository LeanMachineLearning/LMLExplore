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
`3 * α / 2` [EVR26, Note 18, Theorem B], by the potential argument
`ProbabilityTheory.measure_eBH_nonempty_le_of_key` of
`LMLExplore.EValues.MultipleTesting.RunningMaxima`.

## Main statements

* `ProbabilityTheory.measure_eBH_iSup_nonempty_le_of_card_eq_three`: for three
  hypotheses, e-BH on the running maxima rejects with probability at most `3 * α / 2`
  [EVR26, Note 18, Theorem B].

## Implementation notes

The levels of a process, in units of the threshold, are `0`, `1`, `2` and `3`, cut at `1`,
`3 / 2` and `3`. The potential of each of the sixteen non-winning flag states is the minimum of
the constant `1` and of one to three affine forms, listed in `table3`. The key inequality is
checked state by state and cell by cell, by `linarith`; the local tactic `key3_tac` carries the
case analysis shared by the states.

The table of forms `table3`, the level cuts and the case analysis are adapted from
`EValuesResearch/Results/RunningMaximaAux.lean` (commit `ffba78a`) in the paper project
`RemyDegenne/evalues_research`, which formalizes [EVR26, Note 18, Theorem B].

## References

* [WR22] R. Wang and A. Ramdas, *False discovery rate control with e-values*, J. R. Stat. Soc.
  Ser. B 84 (2022), arXiv:2009.02824v5.
* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 18,
  `results/18-running-maxima-general-k.md`.
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

/-- The flag `m` reached from the flag `0` by moving to a real value `x`, with the cell of `x`. -/
private lemma lev3_cases_zero {x : ℝ} (hx : 0 ≤ x) {m : ℕ}
    (hm : max 0 (lev3 (ENNReal.ofReal x)) = m) :
    (m = 0 ∧ x < 1) ∨ (m = 1 ∧ 1 ≤ x ∧ x < 3 / 2) ∨ (m = 2 ∧ 3 / 2 ≤ x ∧ x < 3) ∨
      (m = 3 ∧ 3 ≤ x) := by
  rw [← hm, lev3_ofReal hx]
  by_cases h3 : 3 ≤ x
  · exact Or.inr (Or.inr (Or.inr ⟨by simp [h3], h3⟩))
  by_cases h2 : 3 / 2 ≤ x
  · exact Or.inr (Or.inr (Or.inl ⟨by simp [h3, h2], h2, not_le.1 h3⟩))
  by_cases h1 : 1 ≤ x
  · exact Or.inr (Or.inl ⟨by simp [h3, h2, h1], h1, not_le.1 h2⟩)
  · exact Or.inl ⟨by simp [h3, h2, h1], not_le.1 h1⟩

/-- The flag `m` reached from the flag `1` by moving to a real value `x`, with the cell of `x`. -/
private lemma lev3_cases_one {x : ℝ} (hx : 0 ≤ x) {m : ℕ}
    (hm : max 1 (lev3 (ENNReal.ofReal x)) = m) :
    (m = 1 ∧ x < 3 / 2) ∨ (m = 2 ∧ 3 / 2 ≤ x ∧ x < 3) ∨ (m = 3 ∧ 3 ≤ x) := by
  rw [← hm, lev3_ofReal hx]
  by_cases h3 : 3 ≤ x
  · exact Or.inr (Or.inr ⟨by simp [h3], h3⟩)
  by_cases h2 : 3 / 2 ≤ x
  · exact Or.inr (Or.inl ⟨by simp [h3, h2], h2, not_le.1 h3⟩)
  · exact Or.inl ⟨by simp only [h3, h2, ite_false]; split_ifs <;> simp, not_le.1 h2⟩

/-- The flag `m` reached from the flag `2` by moving to a real value `x`, with the cell of `x`. -/
private lemma lev3_cases_two {x : ℝ} (hx : 0 ≤ x) {m : ℕ}
    (hm : max 2 (lev3 (ENNReal.ofReal x)) = m) : (m = 2 ∧ x < 3) ∨ (m = 3 ∧ 3 ≤ x) := by
  rw [← hm, lev3_ofReal hx]
  by_cases h3 : 3 ≤ x
  · exact Or.inr ⟨by simp [h3], h3⟩
  · exact Or.inl ⟨by simp only [h3, ite_false]; split_ifs <;> simp, not_le.1 h3⟩

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

/-- The affine form `j` of the potential for three hypotheses, from its definition. -/
private lemma ell3_def (b : Fin 3 → ℕ) (j : Fin 4) (r : Fin 3 → ℝ) :
    ell3 b j r = ∑ i, coef3 b j i * r i + const3 b j := (rfl)

/-- The form `0` of the potential for three hypotheses is the constant `1`. -/
private lemma ell3_zero (b : Fin 3 → ℕ) (r : Fin 3 → ℝ) : ell3 b 0 r = 1 := by
  simp [ell3, coef3, const3]

/-- The flag state reached from the flag state `b` of three hypotheses by moving to `r`. -/
private noncomputable def step3 (b : Fin 3 → ℕ) (r : Fin 3 → ℝ) : Fin 3 → ℕ :=
  b ⊔ fun i ↦ lev3 (ENNReal.ofReal (r i))

/-- The flag state reached from `b` by moving to `r`, from its definition. -/
private lemma step3_def (b : Fin 3 → ℕ) (r : Fin 3 → ℝ) :
    step3 b r = b ⊔ fun i ↦ lev3 (ENNReal.ofReal (r i)) := (rfl)

/-- The flag state reached from `b` by moving to `r`, as the vector of its three coordinates. -/
private lemma step3_eq_vec (b : Fin 3 → ℕ) (r : Fin 3 → ℝ) :
    step3 b r = ![step3 b r 0, step3 b r 1, step3 b r 2] := by
  funext i
  fin_cases i <;> rfl

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

/-- `key3_tac b c₀ c₁ c₂` proves the key inequality for three hypotheses in the non-winning flag
state `b`, where `c₀`, `c₁`, `c₂` list the flags reached by each coordinate from its flag in `b`
(`lev3_cases_zero`, `lev3_cases_one` or `lev3_cases_two`). A form without coefficients is the
constant `1`, which is the form `0` of every state. For the others, argue by contradiction: split
each coordinate of `r` into its cells, which fixes the state reached, evaluate the forms by the
lemmas `ell3_*` above, and compare them by `linarith`. -/
local macro "key3_tac " b:term:max c₀:term:max c₁:term:max c₂:term:max : tactic => `(tactic| (
  intro j r hr
  rcases fin_four_cases j with hj | hj | hj | hj <;> subst hj
  all_goals first
    | (refine ⟨0, ?_⟩; simp [ell3, coef3, const3, table3, Wins3]; done)
    | (by_contra! h
       have := hr 0
       have := hr 1
       have := hr 2
       rw [step3_eq_vec] at h
       generalize hm₀ : step3 $b r 0 = m₀ at h
       generalize hm₁ : step3 $b r 1 = m₁ at h
       generalize hm₂ : step3 $b r 2 = m₂ at h
       have c₀ := $c₀ (hr 0) hm₀
       have c₁ := $c₁ (hr 1) hm₁
       have c₂ := $c₂ (hr 2) hm₂
       clear hm₀ hm₁ hm₂
       casesm* _ ∨ _, _ ∧ _
       all_goals
         subst_vars
         have h0 := h 0
         have h1 := h 1
         have h2 := h 2
         have h3 := h 3
         simp only [ell3_zero, ell3_000_1, ell3_001_1, ell3_002_1, ell3_002_2, ell3_002_3,
           ell3_010_1, ell3_011_1, ell3_011_2, ell3_012_1, ell3_020_1, ell3_020_2, ell3_020_3,
           ell3_021_1, ell3_100_1, ell3_101_1, ell3_101_2, ell3_102_1, ell3_110_1, ell3_110_2,
           ell3_120_1, ell3_200_1, ell3_200_2, ell3_200_3, ell3_201_1, ell3_210_1] at h0 h1 h2 h3
         linarith)))

/-- The key inequality for three hypotheses in the flag state `![0, 0, 0]`. -/
private lemma key3_000 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![0, 0, 0] r) j' r ≤ ell3 ![0, 0, 0] j r := by
  key3_tac ![0, 0, 0] lev3_cases_zero lev3_cases_zero lev3_cases_zero

/-- The key inequality for three hypotheses in the flag state `![0, 0, 1]`. -/
private lemma key3_001 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![0, 0, 1] r) j' r ≤ ell3 ![0, 0, 1] j r := by
  key3_tac ![0, 0, 1] lev3_cases_zero lev3_cases_zero lev3_cases_one

/-- The key inequality for three hypotheses in the flag state `![0, 0, 2]`. -/
private lemma key3_002 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![0, 0, 2] r) j' r ≤ ell3 ![0, 0, 2] j r := by
  key3_tac ![0, 0, 2] lev3_cases_zero lev3_cases_zero lev3_cases_two

/-- The key inequality for three hypotheses in the flag state `![0, 1, 0]`. -/
private lemma key3_010 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![0, 1, 0] r) j' r ≤ ell3 ![0, 1, 0] j r := by
  key3_tac ![0, 1, 0] lev3_cases_zero lev3_cases_one lev3_cases_zero

/-- The key inequality for three hypotheses in the flag state `![0, 1, 1]`. -/
private lemma key3_011 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![0, 1, 1] r) j' r ≤ ell3 ![0, 1, 1] j r := by
  key3_tac ![0, 1, 1] lev3_cases_zero lev3_cases_one lev3_cases_one

/-- The key inequality for three hypotheses in the flag state `![0, 1, 2]`. -/
private lemma key3_012 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![0, 1, 2] r) j' r ≤ ell3 ![0, 1, 2] j r := by
  key3_tac ![0, 1, 2] lev3_cases_zero lev3_cases_one lev3_cases_two

/-- The key inequality for three hypotheses in the flag state `![0, 2, 0]`. -/
private lemma key3_020 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![0, 2, 0] r) j' r ≤ ell3 ![0, 2, 0] j r := by
  key3_tac ![0, 2, 0] lev3_cases_zero lev3_cases_two lev3_cases_zero

/-- The key inequality for three hypotheses in the flag state `![0, 2, 1]`. -/
private lemma key3_021 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![0, 2, 1] r) j' r ≤ ell3 ![0, 2, 1] j r := by
  key3_tac ![0, 2, 1] lev3_cases_zero lev3_cases_two lev3_cases_one

/-- The key inequality for three hypotheses in the flag state `![1, 0, 0]`. -/
private lemma key3_100 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![1, 0, 0] r) j' r ≤ ell3 ![1, 0, 0] j r := by
  key3_tac ![1, 0, 0] lev3_cases_one lev3_cases_zero lev3_cases_zero

/-- The key inequality for three hypotheses in the flag state `![1, 0, 1]`. -/
private lemma key3_101 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![1, 0, 1] r) j' r ≤ ell3 ![1, 0, 1] j r := by
  key3_tac ![1, 0, 1] lev3_cases_one lev3_cases_zero lev3_cases_one

/-- The key inequality for three hypotheses in the flag state `![1, 0, 2]`. -/
private lemma key3_102 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![1, 0, 2] r) j' r ≤ ell3 ![1, 0, 2] j r := by
  key3_tac ![1, 0, 2] lev3_cases_one lev3_cases_zero lev3_cases_two

/-- The key inequality for three hypotheses in the flag state `![1, 1, 0]`. -/
private lemma key3_110 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![1, 1, 0] r) j' r ≤ ell3 ![1, 1, 0] j r := by
  key3_tac ![1, 1, 0] lev3_cases_one lev3_cases_one lev3_cases_zero

/-- The key inequality for three hypotheses in the flag state `![1, 2, 0]`. -/
private lemma key3_120 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![1, 2, 0] r) j' r ≤ ell3 ![1, 2, 0] j r := by
  key3_tac ![1, 2, 0] lev3_cases_one lev3_cases_two lev3_cases_zero

/-- The key inequality for three hypotheses in the flag state `![2, 0, 0]`. -/
private lemma key3_200 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![2, 0, 0] r) j' r ≤ ell3 ![2, 0, 0] j r := by
  key3_tac ![2, 0, 0] lev3_cases_two lev3_cases_zero lev3_cases_zero

/-- The key inequality for three hypotheses in the flag state `![2, 0, 1]`. -/
private lemma key3_201 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![2, 0, 1] r) j' r ≤ ell3 ![2, 0, 1] j r := by
  key3_tac ![2, 0, 1] lev3_cases_two lev3_cases_zero lev3_cases_one

/-- The key inequality for three hypotheses in the flag state `![2, 1, 0]`. -/
private lemma key3_210 : ∀ (j : Fin 4) (r : Fin 3 → ℝ), (∀ i, 0 ≤ r i) →
    ∃ j', ell3 (step3 ![2, 1, 0] r) j' r ≤ ell3 ![2, 1, 0] j r := by
  key3_tac ![2, 1, 0] lev3_cases_two lev3_cases_one lev3_cases_zero

/-- **Key inequality for three hypotheses**, at real points: from every flag state `b`, every
affine form of the potential dominates at every point `r` one of the forms of the state reached
by moving to `r`. -/
private lemma key3_real (b : Fin 3 → ℕ) (j : Fin 4) (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i) :
    ∃ j', ∑ i, coef3 (b ⊔ fun i ↦ lev3 (ENNReal.ofReal (r i))) j' i * r i +
      const3 (b ⊔ fun i ↦ lev3 (ENNReal.ofReal (r i))) j' ≤
        ∑ i, coef3 b j i * r i + const3 b j := by
  by_cases hb : Wins3 b
  · exact ⟨0, by simp [coef3, const3, hb]⟩
  simp only [← step3_def, ← ell3_def]
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
private lemma measure_eBH_iSup_nonempty_le_fin_three {M : Fin 3 → ℕ → Ω → ℝ≥0∞}
    (hM : ∀ i, IsTestSupermartingale (M i) ℱ {P}) (α : ℝ≥0∞) :
    P {ω | (eBH (fun i ↦ ⨆ n, M i n ω) α).Nonempty} ≤ 3 * α / 2 := by
  have h := measure_eBH_nonempty_le_of_key hM monotone_lev3.measurable le_lev3
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
E-BH at level `α` applied to the running maxima `⨆ n, M i n` makes a rejection with probability
at most `3 * α / 2` [EVR26, Note 18, Theorem B]. The measure `P` need not be a probability
measure. -/
theorem measure_eBH_iSup_nonempty_le_of_card_eq_three {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = 3) {H : ι → Set (Measure Ω)} {M : ι → ℕ → Ω → ℝ≥0∞}
    (hM : ∀ i, IsTestSupermartingale (M i) ℱ (H i)) (hP : ∀ i, P ∈ H i) (α : ℝ≥0∞) :
    P {ω | (eBH (fun i ↦ ⨆ n, M i n ω) α).Nonempty} ≤ 3 * α / 2 := by
  -- relabel the hypotheses by `Fin 3`
  let σ := (Fintype.equivFinOfCardEq hι).symm
  have h := measure_eBH_iSup_nonempty_le_fin_three (M := fun k ↦ M (σ k))
    (fun _ ↦ (hM _).anti_set (Set.singleton_subset_iff.2 (hP _))) α
  have hset : {ω | (eBH (fun k ↦ ⨆ n, M (σ k) n ω) α).Nonempty} =
      {ω | (eBH (fun i ↦ ⨆ n, M i n ω) α).Nonempty} :=
    Set.ext fun ω ↦ eBH_comp_equiv_nonempty (e := fun i ↦ ⨆ n, M i n ω) σ
  rwa [hset] at h

end ProbabilityTheory
