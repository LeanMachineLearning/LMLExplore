/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.StaticProportions
public import LMLExplore.Identification.Task.HalfSpace.Basic
public import LMLExplore.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Star.Real

/-!
# Difficulty ratios of tasks with a flat boundary

Let the arm `a` of the vector of means `μ` have the Gaussian law of mean `μ a` and known variance
`v a ≠ 0`. A task has a *flat boundary* at `η` if, in a ball around `η`, its admissible models are
the vectors off a hyperplane through `η`, with one single correct answer on each side. For such a
task, every fixed-budget algorithm family has supremum over the admissible models of its
asymptotic ratio to the static-proportions difficulty `H^{sp}` at least `1`: the infimum over the
families of the maximal difficulty ratio to `H^{sp}` is at least `1`
[D23, Theorem 7]. Half-space identification (`halfSpaceTask ν id u`), whose boundary is the
hyperplane `u ⬝ᵥ μ = 0` everywhere, is the basic example [D23, Lemma 16]. Best arm
identification has a flat boundary at the vectors of means with exactly two best arms,
thresholding at those with exactly one mean at the threshold, and positivity at those with one
mean at the threshold and the others above it.

Write `L = ∑ a, |u a| √(v a)` for the normal vector `u` of the hyperplane.

* For half-space identification, the static-proportions difficulty is
  `H^{sp}(μ) = 2 L² / (u ⬝ᵥ μ)²` [D23, Lemma 15]: the Gaussian divergences are symmetric, so that
  `H^{sp}` is the characteristic time `T*` of the pure exploration game
  (`LMLExplore.Identification.charTime_halfSpaceTask_gaussianReal`).
* Near a flat boundary, `H^{sp}(λ)⁻¹ ≥ c (u ⬝ᵥ (λ - η))² / (2 L²)` for every `c < 1`: the
  allocation `c w* + (1 - c) / K`, mixing the optimal allocation `w* a = |u a| √(v a) / L` of the
  half-space game with the uniform one, pays at least this much for the alternatives inside the
  ball, as in the half-space game, and a positive constant for those outside it.
* At the model `μ = η - s u` close to `η`, the alternatives `λ = μ + t s (u ⬝ᵥ u) d`, for `t > 1`
  and a direction `d` with `u ⬝ᵥ d = 1` along which moving by `s` costs at most `s² / (2 L²)` for
  every allocation, are close to `η` and have
  `H^{sp}(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ)) ≤ t² / (c (t - 1)²)` for every allocation `w`. The
  asymptotic lower bound over a set of alternatives
  (`LMLExplore.Identification.IdentTask.inv_iSup_asymptoticRatio_le`, [D23, Theorem 3]) then
  bounds the inverse of the maximal ratio by this quantity, for the families whose probability of
  error at `μ` tends to `0`; the others have an infinite ratio at `μ`. Take `c = 1 - 1 / t` and
  let `t → ∞`.

## Main statements

* `LMLExplore.Identification.staticDifficulty_halfSpaceTask_gaussianReal`: [D23, Lemma 15], the
  static-proportions difficulty of Gaussian half-space identification.
* `LMLExplore.Identification.one_le_iInf_maxRatio_staticDifficulty_of_hyperplane`:
  [D23, Theorem 7], tasks with a flat boundary.
* `LMLExplore.Identification.one_le_iInf_maxRatio_staticDifficulty_halfSpaceTask_gaussianReal`:
  [D23, Lemma 16], Gaussian half-space identification.

## Implementation notes

[D23] writes `H_{𝒞^{sp}}` for the oracle difficulty of the class of static proportions
algorithms, which is `H^{sp}` for regular tasks
(`LMLExplore.Identification.IdentTask.oracleDifficulty_staticClass_eq_staticDifficulty`,
[D23, Theorem 1]). The statements here are against `H^{sp}` and need no regularity assumption. The
paper uses a Euclidean ball; the balls of the different norms of `α → ℝ` contain each other, so
the hypothesis is the same for the ball of the sup norm used here.

The proof of [D23, Theorem 7] goes through Lemmas 17 and 18 of the paper, which are misprinted, and
the proof of Lemma 18 uses a value of `H^{sp}` near `η` that Lemma 17 does not give. The proof here
avoids them: the bound on `H^{sp}` near `η` above replaces them, and Lemma 16 is the case of
Theorem 7 for half-space identification.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
* Adapted from the formalization of [D23] in the project `RemyDegenne/Degenne2023Existence`
  (same author), files `D2023/Lemma15.lean`, `D2023/Lemma16.lean` and `D2023/Theorem7.lean`, and
  `ForLMLExplore/Identification/Task/HalfSpace.lean` for the direction `d`, commit
  `208fe8bbf8820ec9093a2d7994ce94474cff3afc`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Learning

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α ℐ : Type*} {mα : MeasurableSpace α} [Fintype α] {u : α → ℝ} {v : α → ℝ≥0}

/-! ### The static-proportions difficulty of half-space identification -/

/-- **The static-proportions difficulty of Gaussian half-space identification** [D23, Lemma 15].
For Gaussian arms with variances `v a ≠ 0` and a vector of means `μ` with `u ⬝ᵥ μ ≠ 0`,
`H^{sp}(μ) = 2 (∑ a, |u a| √(v a))² / (u ⬝ᵥ μ)²`, the characteristic time of `μ`. -/
theorem staticDifficulty_halfSpaceTask_gaussianReal {ν : (α → ℝ) → Kernel α ℝ}
    [∀ μ, IsMarkovKernel (ν μ)] (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) {μ : α → ℝ} (hμ : u ⬝ᵥ μ ≠ 0) :
    (halfSpaceTask ν id u).staticDifficulty μ =
      ENNReal.ofReal (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2 / (u ⬝ᵥ μ) ^ 2) := by
  rw [IdentTask.staticDifficulty_eq_charTime _ (correct_halfSpaceTask_eq_singleton _ _)
      fun _ _ a ↦ by
        simp only [ν_halfSpaceTask, hν, klDiv_gaussianReal_gaussianReal_same_var (hv a),
          sub_sq_comm],
    charTime_halfSpaceTask_gaussianReal hv hν hμ]

/-! ### The static-proportions difficulty near a flat boundary -/

/-- A direction across the hyperplane `u ⬝ᵥ x = 0`: `d a = sign (u a) √(v a) / L`, with
`L = ∑ a, |u a| √(v a)`, has `u ⬝ᵥ d = 1`, and for every allocation `w` of the simplex and `s : ℝ`,
`∑ a, w a (s d a)² / (2 v a) ≤ s² / (2 L²)`. -/
private lemma exists_dotProduct_eq_one_sum_le (hv : ∀ a, v a ≠ 0) (hu : u ≠ 0) :
    ∃ d : α → ℝ, u ⬝ᵥ d = 1 ∧ ∀ w ∈ simplex α, ∀ s : ℝ,
      ∑ a, w a * (s * d a) ^ 2 / (2 * v a) ≤ s ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2) := by
  set L := ∑ a, |u a| * √(v a : ℝ) with hL_def
  have hL : 0 < L := sum_abs_mul_sqrt_pos hv hu
  set d : α → ℝ := fun a ↦ u a * √(v a : ℝ) / (|u a| * L)
  have hd : u ⬝ᵥ d = 1 := by
    have (a : α) : u a * d a = |u a| * √(v a : ℝ) / L := by
      rcases eq_or_ne (u a) 0 with h | h
      · simp [d, h]
      · have : |u a| ≠ 0 := abs_ne_zero.2 h
        simp only [d]
        field_simp
        rw [← sq_abs]
        ring
    rw [dotProduct, Finset.sum_congr rfl fun a _ ↦ this a, ← Finset.sum_div, ← hL_def,
      div_self hL.ne']
  refine ⟨d, hd, fun w hw s ↦ ?_⟩
  have hw0 := (mem_simplex_iff.1 hw).1
  set C := s ^ 2 / (2 * L ^ 2)
  have hC : 0 ≤ C := by positivity
  -- Each term is at most `w a C`, with equality on the arms with `u a ≠ 0`.
  calc ∑ a, w a * (s * d a) ^ 2 / (2 * v a)
      ≤ ∑ a, w a * C := Finset.sum_le_sum fun a _ ↦ ?_
    _ = C := by rw [← Finset.sum_mul, (mem_simplex_iff.1 hw).2, one_mul]
  have hva : (0 : ℝ) < v a := NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hv a))
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hw0 a)
  rcases eq_or_ne (u a) 0 with h | h
  · simpa [d, h] using hC
  · refine le_of_eq ?_
    have : |u a| ≠ 0 := abs_ne_zero.2 h
    simp only [d, C]
    rw [mul_pow, div_pow, mul_pow, mul_pow, Real.sq_sqrt hva.le, ← sq_abs (u a)]
    field_simp

/-- **Crossing the hyperplane.** For `x` and `y` strictly on the two sides of the hyperplane
`u ⬝ᵥ z = 0`, `c ≥ 0` and an allocation `w ≥ c w*`, with `w* a = |u a| √(v a) / L` and
`L = ∑ a, |u a| √(v a)`, `c (u ⬝ᵥ x)² / (2 L²) ≤ ∑ a, w a (x a - y a)² / (2 v a)`. For `c = 1` and
`w = w*`, this is the value of the Gaussian half-space game at `x`, attained at `w*`; the kernels
`ν` only serve to build that game. -/
private lemma mul_sq_dotProduct_div_le_sum (ν : (α → ℝ) → Kernel α ℝ) [∀ μ, IsMarkovKernel (ν μ)]
    (hv : ∀ a, v a ≠ 0) (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) {c : ℝ} (hc : 0 ≤ c)
    {w : α → ℝ}
    (hw : ∀ a, c * (|u a| * √(v a : ℝ) / ∑ b, |u b| * √(v b : ℝ)) ≤ w a) {x y : α → ℝ}
    (hx : u ⬝ᵥ x ≠ 0) (hxy : u ⬝ᵥ x * u ⬝ᵥ y < 0) :
    c * ((u ⬝ᵥ x) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2)) ≤
      ∑ a, w a * (x a - y a) ^ 2 / (2 * v a) := by
  have hu : u ≠ 0 := fun h ↦ hx (by simp [h])
  set w' := fun a ↦ |u a| * √(v a : ℝ) / ∑ b, |u b| * √(v b : ℝ)
  have hw' : w' ∈ simplex α := abs_mul_sqrt_div_mem_simplex hv hu
  have hi : decide (0 < u ⬝ᵥ x) = true ↔ 0 < u ⬝ᵥ x := decide_eq_true_iff
  -- `y` is an alternative to the answer of `x` in the half-space game.
  have hy : y ∈ (halfSpaceTask ν id u).alt (decide (0 < u ⬝ᵥ x)) := by
    rw [mem_alt_halfSpaceTask_iff, id_eq, hi]
    refine ⟨fun h ↦ by simp [h] at hxy, fun h ↦ ?_⟩
    rcases hx.lt_or_gt with h' | h'
    · have : ¬ 0 < u ⬝ᵥ y := fun hy ↦ h'.not_gt (h.2 hy)
      nlinarith [not_lt.1 this]
    · nlinarith [h.1 h']
  -- The cost of `y` at `w*` is at least the value of the game at `x`, attained at `w*`.
  have hopt := ((halfSpaceTask ν id u).mem_optAlloc_iff.1 (by
    rw [optAlloc_halfSpaceTask_gaussianReal hv hν hx hi]; exact Set.mem_singleton w')).2
  have h : ENNReal.ofReal ((u ⬝ᵥ x) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2)) ≤
      (halfSpaceTask ν id u).cost w' x y := by
    rw [← answerValue_halfSpaceTask_gaussianReal hv hν hx hi, ← hopt]
    exact IdentTask.altCost_le_cost _ hy w'
  rw [IdentTask.cost_gaussianReal hv (fun μ a ↦ by rw [ν_halfSpaceTask, hν])
    (mem_simplex_iff.1 hw').1] at h
  have hs := (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun a _ ↦
    div_nonneg (mul_nonneg ((mem_simplex_iff.1 hw').1 a) (sq_nonneg _)) (by positivity))).1 h
  calc c * ((u ⬝ᵥ x) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2))
      ≤ c * ∑ a, w' a * (x a - y a) ^ 2 / (2 * v a) := by gcongr
    _ = ∑ a, c * w' a * (x a - y a) ^ 2 / (2 * v a) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ ↦ by ring
    _ ≤ ∑ a, w a * (x a - y a) ^ 2 / (2 * v a) := by
        gcongr with a _
        exact hw a

/-- **Moving one arm far.** For a nonnegative allocation `w ≥ m` and two vectors `x`, `y` whose
coordinates `a` differ by at least `δ ≥ 0`, `m δ² / (2 ∑ b, v b) ≤ ∑ b, w b (x b - y b)² / (2 v b)`.
-/
private lemma mul_sq_div_le_sum (hv : ∀ a, v a ≠ 0) {w : α → ℝ} (hw : 0 ≤ w) {m : ℝ}
    (hm : ∀ a, m ≤ w a) {x y : α → ℝ} {a : α} {δ : ℝ} (hδ : 0 ≤ δ) (ha : δ ≤ |x a - y a|) :
    m * δ ^ 2 / (2 * ∑ b, (v b : ℝ)) ≤ ∑ b, w b * (x b - y b) ^ 2 / (2 * v b) := by
  have hva (b : α) : (0 : ℝ) < v b := NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hv b))
  have hvV : (v a : ℝ) ≤ ∑ b, (v b : ℝ) :=
    Finset.single_le_sum (f := fun b ↦ (v b : ℝ)) (fun b _ ↦ (hva b).le) (Finset.mem_univ a)
  have hδ2 : δ ^ 2 ≤ (x a - y a) ^ 2 := by
    rw [← sq_abs (x a - y a)]
    exact pow_le_pow_left₀ hδ ha 2
  have : 0 ≤ w a := hw a
  have := hva a
  calc m * δ ^ 2 / (2 * ∑ b, (v b : ℝ))
      ≤ w a * (x a - y a) ^ 2 / (2 * ∑ b, (v b : ℝ)) := by gcongr; exact hm a
    _ ≤ w a * (x a - y a) ^ 2 / (2 * v a) := by gcongr
    _ ≤ ∑ b, w b * (x b - y b) ^ 2 / (2 * v b) :=
        Finset.single_le_sum (f := fun b ↦ w b * (x b - y b) ^ 2 / (2 * v b))
          (fun b _ ↦ by have : 0 ≤ w b := hw b; have := hva b; positivity) (Finset.mem_univ a)

/-- The allocation `c w* + (1 - c) / K`, mixing `w* a = |u a| √(v a) / L` with the uniform
allocation, belongs to the simplex and is at least `c w*` and at least `(1 - c) / K`. -/
private lemma exists_mem_simplex_mul_le_and_le (hv : ∀ a, v a ≠ 0) (hu : u ≠ 0) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∃ w ∈ simplex α, (∀ a, c * (|u a| * √(v a : ℝ) / ∑ b, |u b| * √(v b : ℝ)) ≤ w a) ∧
      ∀ a, (1 - c) / Fintype.card α ≤ w a := by
  obtain ⟨a₀, -⟩ := Function.ne_iff.1 hu
  have : Nonempty α := ⟨a₀⟩
  have hL := sum_abs_mul_sqrt_pos hv hu
  refine ⟨c • (fun a ↦ |u a| * √(v a : ℝ) / ∑ b, |u b| * √(v b : ℝ)) +
    (1 - c) • fun _ ↦ (Fintype.card α : ℝ)⁻¹, convex_simplex α (abs_mul_sqrt_div_mem_simplex hv hu)
      (uniform_mem_simplex α) hc0 (by linarith) (by ring), fun a ↦ ?_, fun a ↦ ?_⟩ <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · exact le_add_of_nonneg_right (mul_nonneg (by linarith) (by positivity))
  · rw [div_eq_mul_inv]
    exact le_add_of_nonneg_left (mul_nonneg hc0 (by positivity))

/-- A radius `ρ ∈ (0, r / 2]` with `A ρ² ≤ B`, for `A ≥ 0` and `B > 0`. -/
private lemma exists_pos_le_and_mul_sq_le {A B r : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (hr : 0 < r) :
    ∃ ρ > 0, ρ ≤ r / 2 ∧ A * ρ ^ 2 ≤ B := by
  refine ⟨min (r / 2) √(B / (A + 1)), lt_min (by linarith) (Real.sqrt_pos.2 (by positivity)),
    min_le_left _ _, ?_⟩
  have h1 : min (r / 2) √(B / (A + 1)) ^ 2 ≤ B / (A + 1) :=
    (pow_le_pow_left₀ (le_min (by linarith) (Real.sqrt_nonneg _)) (min_le_right _ _) 2).trans_eq
      (Real.sq_sqrt (by positivity))
  rw [le_div_iff₀ (by positivity)] at h1
  nlinarith [sq_nonneg (min (r / 2) √(B / (A + 1)))]

/-- In the ball where the task has a flat boundary, an alternative `μ'` to a model `μ` off the
hyperplane lies strictly on the other side of the hyperplane. -/
private lemma mul_dotProduct_sub_neg_of_mem_alternatives {task : IdentTask α (α → ℝ) ℐ ℝ}
    {η : α → ℝ} {r : ℝ} {i j : ℐ}
    (hball : ∀ μ ∈ Metric.ball η r, (μ ∈ task.M ↔ u ⬝ᵥ (μ - η) ≠ 0) ∧
      (u ⬝ᵥ (μ - η) < 0 → task.correct μ = {i}) ∧ (0 < u ⬝ᵥ (μ - η) → task.correct μ = {j}))
    {μ μ' : α → ℝ} (hμ : μ ∈ Metric.ball η r) (hμη : u ⬝ᵥ (μ - η) ≠ 0)
    (hμ' : μ' ∈ Metric.ball η r) (hμ'μ : μ' ∈ task.alternatives μ) :
    u ⬝ᵥ (μ - η) * u ⬝ᵥ (μ' - η) < 0 := by
  obtain ⟨hμ'M, hdisj⟩ := task.mem_alternatives_iff.1 hμ'μ
  obtain ⟨hμ'0, hμ'i, hμ'j⟩ := hball μ' hμ'
  obtain ⟨-, hμi, hμj⟩ := hball μ hμ
  rcases hμη.lt_or_gt with h | h <;> rcases (hμ'0.1 hμ'M).lt_or_gt with h' | h'
  · rw [hμi h, hμ'i h'] at hdisj
    exact absurd rfl (Set.disjoint_singleton.1 hdisj)
  · exact mul_neg_of_neg_of_pos h h'
  · exact mul_neg_of_pos_of_neg h h'
  · rw [hμj h, hμ'j h'] at hdisj
    exact absurd rfl (Set.disjoint_singleton.1 hdisj)

/-- **The static-proportions difficulty near a flat boundary.** Let the arm `a` of the model `μ`
have the Gaussian law of mean `μ a` and variance `v a ≠ 0`, and let the task have, in the ball of
center `η` and radius `r`, the admissible models off the hyperplane through `η` orthogonal to
`u ≠ 0`, with the single correct answer `i` on one side and `j` on the other. For every
`c ∈ (0, 1)` there is `ρ ∈ (0, r]` such that every model `λ` at distance less than `ρ` from `η`
and off the hyperplane has `c (u ⬝ᵥ (λ - η))² / (2 L²) ≤ H^{sp}(λ)⁻¹`, with
`L = ∑ a, |u a| √(v a)`: the allocation `c w* + (1 - c) / K` pays at least that much for the
alternatives inside the ball, by the half-space game, and at least `(1 - c) / K (r / 2)² / (2 ∑ a,
v a)` for those outside it. -/
private lemma exists_ofReal_le_inv_staticDifficulty_of_hyperplane
    {task : IdentTask α (α → ℝ) ℐ ℝ} (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, task.ν μ a = gaussianReal (μ a) (v a)) {η : α → ℝ} (hu : u ≠ 0) {r : ℝ}
    (hr : 0 < r) {i j : ℐ}
    (hball : ∀ μ ∈ Metric.ball η r, (μ ∈ task.M ↔ u ⬝ᵥ (μ - η) ≠ 0) ∧
      (u ⬝ᵥ (μ - η) < 0 → task.correct μ = {i}) ∧ (0 < u ⬝ᵥ (μ - η) → task.correct μ = {j}))
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ ρ > 0, ρ ≤ r ∧ ∀ μ, dist μ η < ρ → u ⬝ᵥ (μ - η) ≠ 0 →
      ENNReal.ofReal (c * ((u ⬝ᵥ (μ - η)) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2))) ≤
        (task.staticDifficulty μ)⁻¹ := by
  obtain ⟨w, hw, hww, hwK⟩ := exists_mem_simplex_mul_le_and_le hv hu hc0.le hc1.le
  have hw0 := (mem_simplex_iff.1 hw).1
  set L := ∑ a, |u a| * √(v a : ℝ)
  have hL : 0 < L := sum_abs_mul_sqrt_pos hv hu
  set N := ∑ a, |u a|
  -- `B` bounds below the cost of the alternatives outside the ball, and the radius `ρ` makes
  -- `c (u ⬝ᵥ (μ - η))² / (2 L²) ≤ N² ρ² / (2 L²)` at most `B`.
  set B := (1 - c) / Fintype.card α * (r / 2) ^ 2 / (2 * ∑ a, (v a : ℝ))
  have hB : 0 < B := by
    obtain ⟨a₀, -⟩ := Function.ne_iff.1 hu
    have : Nonempty α := ⟨a₀⟩
    have : 0 < ∑ a, (v a : ℝ) :=
      Finset.sum_pos (fun a _ ↦ NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hv a))) Finset.univ_nonempty
    have : 0 < 1 - c := by linarith
    positivity
  set A := N ^ 2 / (2 * L ^ 2)
  obtain ⟨ρ, hρ, hρr, hAρ⟩ := exists_pos_le_and_mul_sq_le (A := A) (by positivity) hB hr
  refine ⟨ρ, hρ, hρr.trans (by linarith), fun μ hμ hμη ↦ ?_⟩
  have hμa (a : α) : |μ a - η a| < ρ := by
    simpa [Real.dist_eq] using (dist_pi_lt_iff hρ).1 hμ a
  have hμr : μ ∈ Metric.ball η r := Metric.mem_ball.2 (hμ.trans_le (hρr.trans (by linarith)))
  rw [IdentTask.inv_staticDifficulty]
  refine le_iSup₂_of_le w hw (le_iInf₂ fun μ' hμ' ↦ ?_)
  rw [IdentTask.cost_comm_gaussianReal hv hν, IdentTask.cost_gaussianReal hv hν hw0]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hμ'r : dist μ' η < r
  · -- Inside the ball, `μ'` is on the other side of the hyperplane.
    simpa only [Pi.sub_apply, sub_sub_sub_cancel_right] using
      mul_sq_dotProduct_div_le_sum task.ν hv hν hc0.le hww hμη
        (mul_dotProduct_sub_neg_of_mem_alternatives hball hμr hμη (Metric.mem_ball.2 hμ'r) hμ')
  · -- Outside the ball, some arm moves by at least `r / 2`.
    obtain ⟨a, ha⟩ : ∃ a, r ≤ |μ' a - η a| := by
      simpa [dist_pi_lt_iff hr, Real.dist_eq] using hμ'r
    have h1 : r / 2 ≤ |μ a - μ' a| := by
      have := hμa a
      have := abs_sub_abs_le_abs_sub (μ' a - η a) (μ a - η a)
      rw [sub_sub_sub_cancel_right, abs_sub_comm (μ' a) (μ a)] at this
      linarith
    have h2 : (u ⬝ᵥ (μ - η)) ^ 2 ≤ (∑ a, |u a|) ^ 2 * ρ ^ 2 := by
      rw [← mul_pow, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (abs_dotProduct_le_sum_abs_mul u fun a ↦ (hμa a).le) 2
    calc c * ((u ⬝ᵥ (μ - η)) ^ 2 / (2 * L ^ 2))
        ≤ (u ⬝ᵥ (μ - η)) ^ 2 / (2 * L ^ 2) := by
          have : 0 ≤ (u ⬝ᵥ (μ - η)) ^ 2 / (2 * L ^ 2) := by positivity
          nlinarith
      _ ≤ A * ρ ^ 2 := by
          rw [show A * ρ ^ 2 = N ^ 2 * ρ ^ 2 / (2 * L ^ 2) by ring]
          gcongr
      _ ≤ B := hAρ
      _ ≤ ∑ b, w b * (μ b - μ' b) ^ 2 / (2 * v b) :=
          mul_sq_div_le_sum hv hw0 hwK (by linarith) h1

/-! ### Tasks with a flat boundary -/

/-- The bound `H^{sp}(λ) cost_μ(w, λ) ≤ t² / (c (t - 1)²)` with `c = 1 - 1 / t`, at an alternative
`λ` with `u ⬝ᵥ (λ - η) = (t - 1) q` whose cost from `μ` is at most `(t q)² / (2 L²)` for the
allocation `w`. -/
private lemma staticDifficulty_mul_cost_le {task : IdentTask α (α → ℝ) ℐ ℝ} {L q t : ℝ}
    (hL : 0 < L) (hq : 0 < q) (ht : 1 < t) {μ lam w : α → ℝ}
    (hH : ENNReal.ofReal ((1 - t⁻¹) * (((t - 1) * q) ^ 2 / (2 * L ^ 2))) ≤
      (task.staticDifficulty lam)⁻¹)
    (hcost : task.cost w μ lam ≤ ENNReal.ofReal ((t * q) ^ 2 / (2 * L ^ 2))) :
    task.staticDifficulty lam * task.cost w μ lam ≤ ENNReal.ofReal ((1 - t⁻¹)⁻¹ ^ 3) := by
  have ht0 : 0 < t := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  have hc0 : 0 < 1 - t⁻¹ := by have : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht; linarith
  have hHlam : task.staticDifficulty lam ≤
      ENNReal.ofReal (((1 - t⁻¹) * (((t - 1) * q) ^ 2 / (2 * L ^ 2)))⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.le_inv_iff_le_inv]
    exact hH
  calc task.staticDifficulty lam * task.cost w μ lam
      ≤ ENNReal.ofReal (((1 - t⁻¹) * (((t - 1) * q) ^ 2 / (2 * L ^ 2)))⁻¹) *
        ENNReal.ofReal ((t * q) ^ 2 / (2 * L ^ 2)) := by gcongr
    _ = ENNReal.ofReal ((1 - t⁻¹)⁻¹ ^ 3) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- Moving the Gaussian model `μ` by `q` along a direction `d` as in
`exists_dotProduct_eq_one_sum_le` costs at most `q² / (2 L²)` for every allocation of the simplex.
-/
private lemma cost_add_smul_le {task : IdentTask α (α → ℝ) ℐ ℝ} (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, task.ν μ a = gaussianReal (μ a) (v a)) {d : α → ℝ}
    (hdw : ∀ w ∈ simplex α, ∀ s : ℝ,
      ∑ a, w a * (s * d a) ^ 2 / (2 * v a) ≤ s ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2))
    {w : α → ℝ} (hw : w ∈ simplex α) (μ : α → ℝ) (q : ℝ) :
    task.cost w μ (μ + q • d) ≤
      ENNReal.ofReal (q ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2)) := by
  rw [IdentTask.cost_gaussianReal hv hν (mem_simplex_iff.1 hw).1]
  refine ENNReal.ofReal_le_ofReal ((le_of_eq ?_).trans ((hdw w hw (-q)).trans_eq (by ring)))
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Small positive `s` keep `η - s u` and `η - s u + t s (u ⬝ᵥ u) d` within distance `ρ > 0` of
`η`. -/
private lemma exists_pos_dist_sub_smul_lt {η d : α → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) :
    ∃ s > 0, dist (η - s • u) η < ρ ∧ dist (η - s • u + (t * (s * u ⬝ᵥ u)) • d) η < ρ := by
  have hnear (f : ℝ → α → ℝ) (hf : Continuous f) (hf0 : f 0 = η) :
      ∀ᶠ s in 𝓝 (0 : ℝ), dist (f s) η < ρ :=
    (hf0 ▸ hf.tendsto 0).eventually (Metric.ball_mem_nhds η hρ)
  obtain ⟨s, hs0, hs1, hs2⟩ := ((eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))).and
    (((hnear (fun s ↦ η - s • u) (by fun_prop) (by simp)).and
      (hnear (fun s ↦ η - s • u + (t * (s * u ⬝ᵥ u)) • d) (by fun_prop) (by simp))).filter_mono
        nhdsWithin_le_nhds)).exists
  exact ⟨s, hs0, hs1, hs2⟩

variable [MeasurableSingletonClass α] [MeasurableSpace ℐ]

/-- The inverse of the maximal ratio of a fixed-budget family near a flat boundary is at most
`(1 - 1 / t)⁻³`, for every `t > 1`: at the model `μ = η - s u`, for `s > 0` small, the
alternatives `λ = μ + t s (u ⬝ᵥ u) d` near `η` bound it through [D23, Theorem 3]. -/
private lemma inv_maxRatio_staticDifficulty_le_of_hyperplane {task : IdentTask α (α → ℝ) ℐ ℝ}
    (hv : ∀ a, v a ≠ 0) (hν : ∀ μ a, task.ν μ a = gaussianReal (μ a) (v a)) {η : α → ℝ}
    (hu : u ≠ 0) {r : ℝ} (hr : 0 < r) {i j : ℐ} (hij : i ≠ j)
    (hball : ∀ μ ∈ Metric.ball η r, (μ ∈ task.M ↔ u ⬝ᵥ (μ - η) ≠ 0) ∧
      (u ⬝ᵥ (μ - η) < 0 → task.correct μ = {i}) ∧ (0 < u ⬝ᵥ (μ - η) → task.correct μ = {j}))
    {𝒜 : ℕ → IdentAlg Unit α ℝ ℐ} (h𝒜 : IsFixedBudgetFamily 𝒜) {t : ℝ} (ht : 1 < t) :
    (task.maxRatio task.staticDifficulty 𝒜)⁻¹ ≤ ENNReal.ofReal ((1 - t⁻¹)⁻¹ ^ 3) := by
  obtain ⟨d, hd, hdw⟩ := exists_dotProduct_eq_one_sum_le hv hu
  have hL := sum_abs_mul_sqrt_pos hv hu
  have hq : 0 < u ⬝ᵥ u := by simpa [star_trivial] using Matrix.dotProduct_star_self_pos_iff.2 hu
  have hc0 : 0 < 1 - t⁻¹ := by have : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht; linarith
  have hc1 : 1 - t⁻¹ < 1 := by have : 0 < t⁻¹ := inv_pos.2 (by linarith); linarith
  obtain ⟨ρ, hρ, hρr, hH⟩ :=
    exists_ofReal_le_inv_staticDifficulty_of_hyperplane hv hν hu hr hball hc0 hc1
  -- The model `μ = η - s u` and the alternative `λ = μ + t s (u ⬝ᵥ u) d`, for `s > 0` small.
  obtain ⟨s, hs0, hs1, hs2⟩ := exists_pos_dist_sub_smul_lt (u := u) (η := η) (d := d) hρ t
  have hsq : 0 < s * u ⬝ᵥ u := mul_pos hs0 hq
  set μ := η - s • u
  set lam := μ + (t * (s * u ⬝ᵥ u)) • d
  have hμη : u ⬝ᵥ (μ - η) = -(s * u ⬝ᵥ u) := by
    simp only [μ, sub_sub_cancel_left, dotProduct_neg, dotProduct_smul, smul_eq_mul]
  have hlamη : u ⬝ᵥ (lam - η) = (t - 1) * (s * u ⬝ᵥ u) := by
    simp only [lam, μ, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul, hd]
    ring
  have hball_of (μ' : α → ℝ) (h : dist μ' η < ρ) : μ' ∈ Metric.ball η r :=
    Metric.mem_ball.2 (h.trans_le hρr)
  have hμ0 : u ⬝ᵥ (μ - η) ≠ 0 := by rw [hμη]; exact neg_ne_zero.2 hsq.ne'
  have hμM : μ ∈ task.M := ((hball μ (hball_of μ hs1)).1).2 hμ0
  have hlam0 : 0 < u ⬝ᵥ (lam - η) := by rw [hlamη]; exact mul_pos (by linarith) hsq
  -- `H^{sp}` is finite near `η`, off the hyperplane.
  have hHtop (μ' : α → ℝ) (h : dist μ' η < ρ) (h0 : u ⬝ᵥ (μ' - η) ≠ 0) :
      task.staticDifficulty μ' ≠ ∞ :=
    ENNReal.inv_ne_zero.1 (ne_of_gt ((ENNReal.ofReal_pos.2 (by positivity)).trans_le (hH μ' h h0)))
  by_cases hp : Tendsto (task.errorProb 𝒜 μ) atTop (𝓝 0)
  swap
  · -- A family whose probability of error at `μ` does not tend to `0` has an infinite ratio.
    rw [IdentTask.maxRatio_eq_top hμM (hHtop μ hs1 hμ0) hp, ENNReal.inv_top]
    exact zero_le
  -- [D23, Theorem 3] at `μ`, over the alternatives near `η`.
  set D := {μ' | μ' ∈ task.alternatives μ ∧ dist μ' η < ρ}
  have h3 := task.inv_iSup_asymptoticRatio_le task.staticDifficulty h𝒜 hp (D := D)
    (fun μ' h ↦ (task.mem_alternatives_iff.1 h.1).2)
    (fun μ' h ↦ task.staticDifficulty_ne_zero_of_mem_alternatives
      (task.mem_alternatives_iff.2 ⟨hμM, (task.mem_alternatives_iff.1 h.1).2.symm⟩)
      fun a ↦ by simp [hν, klDiv_gaussianReal_gaussianReal_same_var (hv a)])
    (fun μ' h ↦ hHtop μ' h.2 (((hball μ' (hball_of μ' h.2)).1).1
      (task.alternatives_subset_M μ h.1)))
  refine (ENNReal.inv_le_inv.2 (IdentTask.iSup_asymptoticRatio_le_maxRatio (D := D) fun μ' h ↦
    task.alternatives_subset_M μ h.1)).trans (h3.trans (iSup₂_le fun w hw ↦ ?_))
  have hlamM : lam ∈ task.alternatives μ := by
    refine task.mem_alternatives_iff.2 ⟨((hball lam (hball_of lam hs2)).1).2 hlam0.ne', ?_⟩
    rw [(hball μ (hball_of μ hs1)).2.1 (by rw [hμη]; exact neg_neg_of_pos hsq),
      (hball lam (hball_of lam hs2)).2.2 hlam0]
    exact Set.disjoint_singleton.2 hij
  exact (iInf₂_le lam ⟨hlamM, hs2⟩).trans (staticDifficulty_mul_cost_le hL hsq ht
    (hlamη ▸ hH lam hs2 hlam0.ne') (cost_add_smul_le hv hν hdw hw μ _))

/-- **Tasks with a flat boundary** [D23, Theorem 7]. Let the arm `a` of the model `μ` have the
Gaussian law of mean `μ a` and variance `v a ≠ 0`. Suppose that in the ball of center `η` and
radius `r > 0`, the admissible models are the vectors off the hyperplane through `η` orthogonal to
`u ≠ 0`, with the single correct answer `i` on one side and `j ≠ i` on the other. Then the
infimum over the fixed-budget algorithm families of the maximal difficulty ratio to the
static-proportions difficulty is at least `1`: every fixed-budget family has supremum over the
admissible models of its asymptotic ratio to `H^{sp}` at least `1`.

The paper also assumes the regularity assumption of [D23, Theorem 1], which the statement does not
need. -/
theorem one_le_iInf_maxRatio_staticDifficulty_of_hyperplane {task : IdentTask α (α → ℝ) ℐ ℝ}
    (hv : ∀ a, v a ≠ 0) (hν : ∀ μ a, task.ν μ a = gaussianReal (μ a) (v a)) {η : α → ℝ}
    (hu : u ≠ 0) {r : ℝ} (hr : 0 < r) {i j : ℐ} (hij : i ≠ j)
    (hball : ∀ μ ∈ Metric.ball η r, (μ ∈ task.M ↔ u ⬝ᵥ (μ - η) ≠ 0) ∧
      (u ⬝ᵥ (μ - η) < 0 → task.correct μ = {i}) ∧ (0 < u ⬝ᵥ (μ - η) → task.correct μ = {j})) :
    1 ≤ ⨅ (𝒜 : ℕ → IdentAlg Unit α ℝ ℐ) (_ : IsFixedBudgetFamily 𝒜),
      task.maxRatio task.staticDifficulty 𝒜 := by
  refine le_iInf₂ fun 𝒜 h𝒜 ↦ ?_
  rw [← ENNReal.inv_le_one]
  have hlim : Tendsto (fun t : ℝ ↦ ENNReal.ofReal ((1 - t⁻¹)⁻¹ ^ 3)) atTop (𝓝 1) := by
    have : Tendsto (fun t : ℝ ↦ (1 - t⁻¹)⁻¹ ^ 3) atTop (𝓝 ((1 - 0)⁻¹ ^ 3)) :=
      ((tendsto_const_nhds.sub tendsto_inv_atTop_zero).inv₀ (by norm_num)).pow 3
    simpa using ENNReal.tendsto_ofReal this
  exact ge_of_tendsto hlim ((eventually_gt_atTop 1).mono fun t ht ↦
    inv_maxRatio_staticDifficulty_le_of_hyperplane hv hν hu hr hij hball h𝒜 ht)

/-- **Maximal difficulty ratio to `H^{sp}` at least `1` in Gaussian half-space identification**
[D23, Lemma 16]. For Gaussian arms with variances `v a ≠ 0` and the half-space task with normal
vector `u ≠ 0`, the infimum over the fixed-budget algorithm families of the maximal difficulty
ratio to the static-proportions difficulty is at least `1`. The boundary of half-space
identification is the hyperplane `u ⬝ᵥ μ = 0`, flat everywhere. -/
theorem one_le_iInf_maxRatio_staticDifficulty_halfSpaceTask_gaussianReal
    {ν : (α → ℝ) → Kernel α ℝ} [∀ μ, IsMarkovKernel (ν μ)] (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hu : u ≠ 0) :
    1 ≤ ⨅ (𝒜 : ℕ → IdentAlg Unit α ℝ Bool) (_ : IsFixedBudgetFamily 𝒜),
      (halfSpaceTask ν id u).maxRatio (halfSpaceTask ν id u).staticDifficulty 𝒜 :=
  one_le_iInf_maxRatio_staticDifficulty_of_hyperplane (η := 0) (r := 1) (i := false) (j := true)
    hv (fun μ a ↦ by rw [ν_halfSpaceTask, hν]) hu one_pos Bool.false_ne_true fun μ _ ↦ by
      refine ⟨by simp, fun h ↦ ?_, fun h ↦ ?_⟩ <;> rw [sub_zero] at h
      · simp [h.not_gt]
      · simp [h]

end LMLExplore.Identification
