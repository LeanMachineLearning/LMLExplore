/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.ExpFamily

/-!
# The pure exploration game of sphere identification with Gaussian arms

In sphere identification (`sphereTask ν c ρ`) the correct answer of a vector of means `μ` is
whether `μ` lies inside the sphere of center `c` and radius `ρ`, that is whether
`∑ a, (μ a - c a)² < ρ²`, and the admissible models are those off the sphere. The alternatives to
the correct answer of `μ` are the vectors of means on the other side of the sphere. For Gaussian
arms with a common variance `σ2`, the transportation cost `∑ a, w a (μ a - λ a)² / (2 σ2)` is a
weighted squared distance, and the game has a closed form [DK19, Lemma 39].

Write `K` for the number of arms, `d a = |μ a - c a|`, `s = ∑ a, d a` and
`q = ∑ a, (μ a - c a)²`. Moving every coordinate of `μ` away from `c` by the same amount `r`
reaches the sphere when `∑ a, (d a + r)² = ρ²`, that is `K r² + 2 s r + q - ρ² = 0`. When
`s² + K (ρ² - q) ≥ 0` (in particular under the condition `d a + r ≥ 0` below), its root
`r = (√(s² + K (ρ² - q)) - s) / K` is `sphereShift c ρ μ`. It is positive inside the sphere and
negative outside of it. The point `λ*` so obtained costs `r² / (2 σ2)` for every allocation of the
simplex, and so do points on the other side of the sphere arbitrarily close to it, which bounds
`D(μ, w, ¬i) ≤ r² / (2 σ2)` for every allocation `w`. Conversely, provided that `d a + r ≥ 0` for
every arm, the allocation `w* a = (d a + r) / ∑ b, (d b + r)` proportional to the absolute values
`d a + r` of the coordinates of `λ* - c` satisfies the identity
`∑ a, (d a + r) (d a - x a)² = ∑ a, d a (d a + r - x a)² + r (∑ a, x a² - ρ²) + r² ∑ a, (d a + r)`
for every vector `x`, which shows that every alternative costs at least `r² / (2 σ2)` at `w*`.
Hence `D(μ, ¬i) = r² / (2 σ2)`, `w*` is an optimal allocation and `T*(μ) = 2 σ2 / r²`. The
condition `d a + r ≥ 0` holds inside the sphere, where `r > 0`; outside of it, it fails when
some coordinate of `μ` is too close to that of `c`.

## Main definitions

* `LMLExplore.Identification.sphereTask ν c ρ`: sphere identification.
* `LMLExplore.Identification.sphereShift c ρ μ`: the common displacement `r` of the coordinates
  of `μ` that reaches the sphere.

## Main statements

* `LMLExplore.Identification.mem_alt_sphereTask_iff`: the alternatives of sphere identification.
* `LMLExplore.Identification.sphereShift_pos_iff`, `LMLExplore.Identification.sphereShift_ne_zero`,
  `LMLExplore.Identification.sum_sq_abs_add_sphereShift`: the sign of `sphereShift c ρ μ`, and
  the equation `∑ a, (|μ a - c a| + r)² = ρ²` defining it.
* `LMLExplore.Identification.altCost_sphereTask_gaussianBandit`,
  `LMLExplore.Identification.answerValue_sphereTask_gaussianBandit`,
  `LMLExplore.Identification.mem_optAlloc_sphereTask_gaussianBandit`,
  `LMLExplore.Identification.charTime_sphereTask_gaussianBandit`: the cost of the alternatives at
  the allocation `w*`, the value of the game, the optimality of `w*` and the characteristic
  time [DK19, Lemma 39].

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, supplementary material, Appendix H, Lemma 39.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} [Fintype α]
  {c μ : α → ℝ} {ρ : ℝ} {i : Bool}

section Task

variable (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)]

/-- *Sphere identification*: the correct answer of a vector of means `μ` is whether it lies
inside the sphere of center `c` and radius `ρ` (`true` iff `∑ a, (μ a - c a)² < ρ²`), and the
admissible models are those off the sphere. -/
noncomputable def sphereTask (c : α → ℝ) (ρ : ℝ) : IdentTask α (α → ℝ) Bool 𝓨 where
  M := {μ | ∑ a, (μ a - c a) ^ 2 ≠ ρ ^ 2}
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct μ := {i | i = true ↔ ∑ a, (μ a - c a) ^ 2 < ρ ^ 2}

@[simp]
lemma M_sphereTask : (sphereTask ν c ρ).M = {μ | ∑ a, (μ a - c a) ^ 2 ≠ ρ ^ 2} := (rfl)

@[simp]
lemma ν_sphereTask : (sphereTask ν c ρ).ν = ν := (rfl)

@[simp]
lemma correct_sphereTask (μ : α → ℝ) :
    (sphereTask ν c ρ).correct μ = {i | i = true ↔ ∑ a, (μ a - c a) ^ 2 < ρ ^ 2} := (rfl)

/-- The unique correct answer of every vector of means `μ` is `true` iff `μ` lies inside the
sphere. -/
lemma correct_sphereTask_eq_singleton :
    (sphereTask ν c ρ).correct μ = {decide (∑ a, (μ a - c a) ^ 2 < ρ ^ 2)} := by
  ext i
  cases i <;> simp

/-- Sphere identification is a single-answer task. -/
lemma isSingleAnswer_sphereTask (c : α → ℝ) (ρ : ℝ) : (sphereTask ν c ρ).IsSingleAnswer :=
  (IdentTask.isSingleAnswer_iff _).2 fun _ _ ↦ ⟨_, correct_sphereTask_eq_singleton ν⟩

/-- The alternatives to the answer `i` in sphere identification are the vectors `μ'` off the
sphere whose side of the sphere is not the one `i` prescribes. -/
lemma mem_alt_sphereTask_iff {μ' : α → ℝ} :
    μ' ∈ (sphereTask ν c ρ).alt i ↔
      ∑ a, (μ' a - c a) ^ 2 ≠ ρ ^ 2 ∧ ¬ (i = true ↔ ∑ a, (μ' a - c a) ^ 2 < ρ ^ 2) := by
  simp only [IdentTask.mem_alt_iff, M_sphereTask, correct_sphereTask, Set.mem_ofPred_eq]

/-- The alternatives to the correct answer of a model `μ` off the sphere are the vectors on the
other side of the sphere. -/
private lemma mem_alt_sphereTask_iff_mul_neg (hμ : ∑ a, (μ a - c a) ^ 2 ≠ ρ ^ 2)
    (hi : i = true ↔ ∑ a, (μ a - c a) ^ 2 < ρ ^ 2) {μ' : α → ℝ} :
    μ' ∈ (sphereTask ν c ρ).alt i ↔
      (∑ a, (μ' a - c a) ^ 2 - ρ ^ 2) * (∑ a, (μ a - c a) ^ 2 - ρ ^ 2) < 0 := by
  rw [mem_alt_sphereTask_iff, hi]
  constructor
  · rintro ⟨hne, h⟩
    rcases hne.lt_or_gt with h1 | h1 <;> rcases hμ.lt_or_gt with h2 | h2
    · exact absurd (iff_of_true h2 h1) h
    · exact mul_neg_of_neg_of_pos (sub_neg.2 h1) (sub_pos.2 h2)
    · exact mul_neg_of_pos_of_neg (sub_pos.2 h1) (sub_neg.2 h2)
    · exact absurd (iff_of_false h2.not_gt h1.not_gt) h
  · intro h
    rcases mul_neg_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [sub_pos] at h1
      rw [sub_neg] at h2
      exact ⟨h1.ne', fun h ↦ h1.not_gt (h.1 h2)⟩
    · rw [sub_neg] at h1
      rw [sub_pos] at h2
      exact ⟨h1.ne, fun h ↦ h2.not_gt (h.2 h1)⟩

end Task

/-! ### The displacement to the sphere -/

/-- The common displacement `r` of the coordinates of `μ` that reaches the sphere of center `c`
and radius `ρ`: the root `r = (√(s² + K (ρ² - q)) - s) / K` of `∑ a, (|μ a - c a| + r)² = ρ²`,
with `K` the number of arms, `s = ∑ a, |μ a - c a|` and `q = ∑ a, (μ a - c a)²`. It is positive
inside the sphere (`sphereShift_pos_iff`), and the equation holds under the condition of
`sum_sq_abs_add_sphereShift`. -/
noncomputable def sphereShift (c : α → ℝ) (ρ : ℝ) (μ : α → ℝ) : ℝ :=
  (√((∑ a, |μ a - c a|) ^ 2 + Fintype.card α * (ρ ^ 2 - ∑ a, (μ a - c a) ^ 2)) -
    ∑ a, |μ a - c a|) / Fintype.card α

lemma sphereShift_def (c : α → ℝ) (ρ : ℝ) (μ : α → ℝ) :
    sphereShift c ρ μ =
      (√((∑ a, |μ a - c a|) ^ 2 + Fintype.card α * (ρ ^ 2 - ∑ a, (μ a - c a) ^ 2)) -
        ∑ a, |μ a - c a|) / Fintype.card α := (rfl)

/-- The expansion `∑ a, (|μ a - c a| + y)² = q + 2 y s + K y²`, with `K` the number of arms,
`s = ∑ a, |μ a - c a|` and `q = ∑ a, (μ a - c a)²`. -/
private lemma sum_sq_abs_add (y : ℝ) : ∑ a, (|μ a - c a| + y) ^ 2 =
    ∑ a, (μ a - c a) ^ 2 + 2 * y * ∑ a, |μ a - c a| + Fintype.card α * y ^ 2 := by
  simp only [add_sq, sq_abs, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

variable [Nonempty α]

/-- `K r = √(s² + K (ρ² - q)) - s` for `r = sphereShift c ρ μ`, with `K` the number of arms,
`s = ∑ a, |μ a - c a|` and `q = ∑ a, (μ a - c a)²`. -/
private lemma card_mul_sphereShift (c : α → ℝ) (ρ : ℝ) (μ : α → ℝ) :
    Fintype.card α * sphereShift c ρ μ =
      √((∑ a, |μ a - c a|) ^ 2 + Fintype.card α * (ρ ^ 2 - ∑ a, (μ a - c a) ^ 2)) -
        ∑ a, |μ a - c a| := by
  have hK : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [sphereShift_def]
  field_simp

/-- The sum of the coordinates `|μ a - c a| + r` of the point reached on the sphere is the square
root `√(s² + K (ρ² - q))` in the definition of `r = sphereShift c ρ μ`. -/
lemma sum_abs_add_sphereShift (c : α → ℝ) (ρ : ℝ) (μ : α → ℝ) :
    ∑ a, (|μ a - c a| + sphereShift c ρ μ) =
      √((∑ a, |μ a - c a|) ^ 2 + Fintype.card α * (ρ ^ 2 - ∑ a, (μ a - c a) ^ 2)) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_mul_sphereShift]
  ring

/-- Under the condition `|μ a - c a| + r ≥ 0` on every arm, the expression under the square root
in the definition of `r = sphereShift c ρ μ` is positive. -/
private lemma radicand_sphereShift_pos (hρ : ρ ≠ 0)
    (h : ∀ a, 0 ≤ |μ a - c a| + sphereShift c ρ μ) :
    0 < (∑ a, |μ a - c a|) ^ 2 + Fintype.card α * (ρ ^ 2 - ∑ a, (μ a - c a) ^ 2) := by
  set r := sphereShift c ρ μ
  have hK : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
  by_contra hR
  -- The coordinates of the point reached on the sphere sum to `0`, so they all vanish.
  have h0 := sum_abs_add_sphereShift c ρ μ
  rw [Real.sqrt_eq_zero'.2 (not_lt.1 hR)] at h0
  have hd (a : α) : |μ a - c a| = -r := by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun a _ ↦ h a).1 h0 a (Finset.mem_univ a)
    linarith
  have hs : ∑ a, |μ a - c a| = Fintype.card α * -r := by simp [hd]
  have hq : ∑ a, (μ a - c a) ^ 2 = Fintype.card α * r ^ 2 := by simp [← sq_abs, hd]
  rw [hs, hq] at hR
  exact hR (by nlinarith [sq_pos_of_ne_zero hρ])

/-- **The displacement to the sphere.** Under the condition `|μ a - c a| + r ≥ 0` on every arm,
`r = sphereShift c ρ μ` solves `∑ a, (|μ a - c a| + r)² = ρ²`: moving every coordinate of `μ`
away from `c` by `r` reaches the sphere. -/
theorem sum_sq_abs_add_sphereShift (hρ : ρ ≠ 0)
    (h : ∀ a, 0 ≤ |μ a - c a| + sphereShift c ρ μ) :
    ∑ a, (|μ a - c a| + sphereShift c ρ μ) ^ 2 = ρ ^ 2 := by
  have hK : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hR := (radicand_sphereShift_pos hρ h).le
  have hL := Real.sq_sqrt hR
  rw [sum_sq_abs_add]
  refine mul_left_cancel₀ hK ?_
  linear_combination hL +
    (Fintype.card α * sphereShift c ρ μ + ∑ a, |μ a - c a| +
      √((∑ a, |μ a - c a|) ^ 2 + Fintype.card α * (ρ ^ 2 - ∑ a, (μ a - c a) ^ 2))) *
        card_mul_sphereShift c ρ μ

/-- The distance from the sphere: `ρ² - q = r (√(s² + K (ρ² - q)) + s)` for
`r = sphereShift c ρ μ`, whenever the expression under the square root is nonnegative. -/
private lemma sub_eq_sphereShift_mul
    (hR : 0 ≤ (∑ a, |μ a - c a|) ^ 2 + Fintype.card α * (ρ ^ 2 - ∑ a, (μ a - c a) ^ 2)) :
    ρ ^ 2 - ∑ a, (μ a - c a) ^ 2 = sphereShift c ρ μ *
      (√((∑ a, |μ a - c a|) ^ 2 + Fintype.card α * (ρ ^ 2 - ∑ a, (μ a - c a) ^ 2)) +
        ∑ a, |μ a - c a|) := by
  have hK : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hL := Real.sq_sqrt hR
  rw [sphereShift_def, div_mul_eq_mul_div, eq_div_iff hK]
  linear_combination -hL

/-- **The sign of the displacement to the sphere.** `sphereShift c ρ μ` is positive iff `μ` lies
inside the sphere. In that case the condition `0 ≤ |μ a - c a| + sphereShift c ρ μ` of the
statements below holds on every arm. -/
theorem sphereShift_pos_iff : 0 < sphereShift c ρ μ ↔ ∑ a, (μ a - c a) ^ 2 < ρ ^ 2 := by
  have hK : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
  have hs : 0 ≤ ∑ a, |μ a - c a| := Finset.sum_nonneg fun a _ ↦ abs_nonneg _
  rw [sphereShift_def, div_pos_iff_of_pos_right hK, sub_pos, Real.lt_sqrt hs]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- Off the sphere, the displacement to the sphere does not vanish, under the condition
`|μ a - c a| + r ≥ 0` on every arm. -/
lemma sphereShift_ne_zero (hρ : ρ ≠ 0) (hμ : ∑ a, (μ a - c a) ^ 2 ≠ ρ ^ 2)
    (h : ∀ a, 0 ≤ |μ a - c a| + sphereShift c ρ μ) : sphereShift c ρ μ ≠ 0 := by
  intro hr
  have hq := sub_eq_sphereShift_mul (radicand_sphereShift_pos hρ h).le
  rw [hr, zero_mul, sub_eq_zero] at hq
  exact hμ hq.symm

/-! ### Gaussian arms -/

variable [MeasurableSingletonClass α] {σ2 : ℝ≥0}

/-- The sign of the coordinate `μ a - c a`, taken to be `1` where it vanishes. -/
private noncomputable def sgn (c μ : α → ℝ) (a : α) : ℝ := if c a ≤ μ a then 1 else -1

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] in
private lemma sgn_mul_sub (a : α) : sgn c μ a * (μ a - c a) = |μ a - c a| := by
  unfold sgn
  split_ifs with h
  · rw [one_mul, abs_of_nonneg (sub_nonneg.2 h)]
  · rw [abs_of_neg (sub_neg.2 (not_le.1 h))]
    ring

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] in
private lemma sq_sgn_mul (a : α) (y : ℝ) : (sgn c μ a * y) ^ 2 = y ^ 2 := by
  unfold sgn
  split_ifs <;> ring

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] in
/-- Moving the coordinate `μ a` away from `c a` by `y`. -/
private lemma add_mul_sgn_sub (a : α) (y : ℝ) :
    μ a + y * sgn c μ a - c a = sgn c μ a * (|μ a - c a| + y) := by
  unfold sgn
  split_ifs with h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    ring
  · rw [abs_of_neg (sub_neg.2 (not_le.1 h))]
    ring

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- The squared distance to `c` of the vector `μ + y sgn(μ - c)` obtained by moving every
coordinate of `μ` away from `c` by `y`. -/
private lemma sum_sq_add_mul_sgn_sub (y : ℝ) :
    ∑ a, (μ a + y * sgn c μ a - c a) ^ 2 =
      ∑ a, (μ a - c a) ^ 2 + 2 * y * ∑ a, |μ a - c a| + Fintype.card α * y ^ 2 := by
  simp only [add_mul_sgn_sub, sq_sgn_mul, sum_sq_abs_add]

omit [Nonempty α] in
/-- The transportation cost of the vector `μ + y sgn(μ - c)` is `y² / (2 σ2)` for every
allocation of the simplex. -/
private lemma cost_add_mul_sgn_sphereTask_gaussianBandit (hσ2 : σ2 ≠ 0) {w : α → ℝ}
    (hw : w ∈ simplex α) (y : ℝ) :
    (sphereTask (Bandits.gaussianBandit · σ2) c ρ).cost w μ (fun a ↦ μ a + y * sgn c μ a) =
      ENNReal.ofReal (y ^ 2 / (2 * σ2)) := by
  rw [IdentTask.cost_gaussianBandit (ν_sphereTask _) hσ2 (mem_simplex_iff.1 hw).1]
  congr 1
  have hterm (a : α) : w a * (μ a - (μ a + y * sgn c μ a)) ^ 2 / (2 * σ2) =
      w a * (y ^ 2 / (2 * σ2)) := by
    rw [show μ a - (μ a + y * sgn c μ a) = sgn c μ a * -y by ring, sq_sgn_mul]
    ring
  rw [Finset.sum_congr rfl fun a _ ↦ hterm a, ← Finset.sum_mul, (mem_simplex_iff.1 hw).2,
    one_mul]

/-- **Approaching the sphere from the other side.** For a model `μ` off the sphere with
`|μ a - c a| + r ≥ 0` on every arm, every allocation `w` of the simplex has
`D(μ, w, ¬i) ≤ r² / (2 σ2)` for `r = sphereShift c ρ μ`: the vectors `μ + t r sgn(μ - c)` with
`t > 1` close to `1` are alternatives, at cost `t² r² / (2 σ2)`. -/
private lemma altCost_sphereTask_gaussianBandit_le (hσ2 : σ2 ≠ 0) (hρ : ρ ≠ 0)
    (hμ : ∑ a, (μ a - c a) ^ 2 ≠ ρ ^ 2) (hi : i = true ↔ ∑ a, (μ a - c a) ^ 2 < ρ ^ 2)
    (h : ∀ a, 0 ≤ |μ a - c a| + sphereShift c ρ μ) {w : α → ℝ} (hw : w ∈ simplex α) :
    (sphereTask (Bandits.gaussianBandit · σ2) c ρ).altCost μ w i ≤
      ENNReal.ofReal (sphereShift c ρ μ ^ 2 / (2 * σ2)) := by
  have hK : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
  have hs : 0 ≤ ∑ a, |μ a - c a| := Finset.sum_nonneg fun a _ ↦ abs_nonneg _
  have hRpos := radicand_sphereShift_pos hρ h
  have hq := sub_eq_sphereShift_mul hRpos.le
  have hr0 := sphereShift_ne_zero hρ hμ h
  have h_sphere := sum_sq_abs_add_sphereShift hρ h
  have hrK := card_mul_sphereShift c ρ μ
  set r := sphereShift c ρ μ with hr_def
  set s := ∑ a, |μ a - c a| with hs_def
  set R := s ^ 2 + Fintype.card α * (ρ ^ 2 - ∑ a, (μ a - c a) ^ 2) with hR_def
  clear_value r s R
  have hL : 0 < √R := Real.sqrt_pos.2 hRpos
  -- The moved vectors `μ + t r sgn(μ - c)`.
  set f : ℝ → α → ℝ := fun t a ↦ μ a + t * r * sgn c μ a with hf
  have hf_sq (t : ℝ) : ∑ a, (f t a - c a) ^ 2 - ρ ^ 2 =
      (t - 1) * r * (2 * √R + (t - 1) * (Fintype.card α * r)) := by
    rw [hf, sum_sq_add_mul_sgn_sub, ← h_sphere, sum_sq_abs_add, ← hs_def]
    linear_combination 2 * (t - 1) * r * hrK
  have hf_cost (t : ℝ) : (sphereTask (Bandits.gaussianBandit · σ2) c ρ).cost w μ (f t) =
      ENNReal.ofReal (t ^ 2 * (r ^ 2 / (2 * σ2))) := by
    rw [hf, cost_add_mul_sgn_sphereTask_gaussianBandit hσ2 hw]
    ring_nf
  -- For `t > 1` close to `1`, the moved vector is on the other side of the sphere.
  have h_alt : ∀ᶠ t in 𝓝[>] (1 : ℝ),
      f t ∈ (sphereTask (Bandits.gaussianBandit · σ2) c ρ).alt i := by
    have hr' : 0 < |r| := abs_pos.2 hr0
    have hlt : (1 : ℝ) < 1 + √R / (Fintype.card α * |r|) := by
      have : 0 < √R / (Fintype.card α * |r|) := by positivity
      linarith
    filter_upwards [Ioo_mem_nhdsGT hlt] with t ht
    rw [mem_alt_sphereTask_iff_mul_neg _ hμ hi, hf_sq]
    have ht1 : 0 < t - 1 := sub_pos.2 ht.1
    have ht2 : (t - 1) * (Fintype.card α * |r|) < √R := by
      have := ht.2
      rwa [← sub_lt_iff_lt_add', lt_div_iff₀ (by positivity)] at this
    have hfac : 0 < 2 * √R + (t - 1) * (Fintype.card α * r) := by
      have : -(Fintype.card α * |r|) ≤ Fintype.card α * r := by
        rw [← mul_neg]
        exact mul_le_mul_of_nonneg_left (neg_abs_le r) hK.le
      nlinarith
    have hpos : 0 < (t - 1) * (2 * √R + (t - 1) * (Fintype.card α * r)) * (√R + s) * (r * r) :=
      mul_pos (mul_pos (mul_pos ht1 hfac) (by linarith)) (mul_self_pos.2 hr0)
    have hq' : ∑ a, (μ a - c a) ^ 2 - ρ ^ 2 = -(r * (√R + s)) := by linarith
    rw [hq']
    linarith [show (t - 1) * r * (2 * √R + (t - 1) * (Fintype.card α * r)) * -(r * (√R + s)) =
      -((t - 1) * (2 * √R + (t - 1) * (Fintype.card α * r)) * (√R + s) * (r * r)) by ring]
  have hlim : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (t ^ 2 * (r ^ 2 / (2 * σ2)))) (𝓝[>] 1)
      (𝓝 (ENNReal.ofReal (r ^ 2 / (2 * σ2)))) := by
    have hc : Continuous fun t : ℝ ↦ ENNReal.ofReal (t ^ 2 * (r ^ 2 / (2 * σ2))) :=
      ENNReal.continuous_ofReal.comp ((continuous_pow 2).mul continuous_const)
    simpa using hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (1 : ℝ)))
  refine ge_of_tendsto hlim ?_
  filter_upwards [h_alt] with t ht
  rw [← hf_cost]
  exact IdentTask.altCost_le_cost _ ht w

/-- The allocation `w* a = (|μ a - c a| + r) / ∑ b, (|μ b - c b| + r)` belongs to the simplex. -/
private lemma sphereAlloc_mem_simplex (hρ : ρ ≠ 0) (h : ∀ a, 0 ≤ |μ a - c a| + sphereShift c ρ μ) :
    (fun a ↦ (|μ a - c a| + sphereShift c ρ μ) / ∑ b, (|μ b - c b| + sphereShift c ρ μ)) ∈
      simplex α := by
  have hL : 0 < ∑ b, (|μ b - c b| + sphereShift c ρ μ) := by
    rw [sum_abs_add_sphereShift]
    exact Real.sqrt_pos.2 (radicand_sphereShift_pos hρ h)
  refine mem_simplex_iff.2 ⟨fun a ↦ div_nonneg (h a) hL.le, ?_⟩
  rw [← Finset.sum_div, div_self hL.ne']

/-- **Crossing the sphere costs at least `r² / (2 σ2)` at the allocation `w*`.** For a model `μ`
off the sphere with `|μ a - c a| + r ≥ 0` on every arm, every alternative `μ'` has transportation
cost at least `r² / (2 σ2)` at the allocation `w*` proportional to `|μ a - c a| + r`, for
`r = sphereShift c ρ μ`. -/
private lemma le_cost_sphereTask_gaussianBandit (hσ2 : σ2 ≠ 0) (hρ : ρ ≠ 0)
    (hμ : ∑ a, (μ a - c a) ^ 2 ≠ ρ ^ 2) (hi : i = true ↔ ∑ a, (μ a - c a) ^ 2 < ρ ^ 2)
    (h : ∀ a, 0 ≤ |μ a - c a| + sphereShift c ρ μ) {μ' : α → ℝ}
    (hμ' : μ' ∈ (sphereTask (Bandits.gaussianBandit · σ2) c ρ).alt i) :
    ENNReal.ofReal (sphereShift c ρ μ ^ 2 / (2 * σ2)) ≤
      (sphereTask (Bandits.gaussianBandit · σ2) c ρ).cost
        (fun a ↦ (|μ a - c a| + sphereShift c ρ μ) / ∑ b, (|μ b - c b| + sphereShift c ρ μ))
        μ μ' := by
  have hs : 0 ≤ ∑ a, |μ a - c a| := Finset.sum_nonneg fun a _ ↦ abs_nonneg _
  have hRpos := radicand_sphereShift_pos hρ h
  have hq := sub_eq_sphereShift_mul hRpos.le
  have h_sphere := sum_sq_abs_add_sphereShift hρ h
  have hsum := sum_abs_add_sphereShift c ρ μ
  rw [mem_alt_sphereTask_iff_mul_neg _ hμ hi] at hμ'
  rw [IdentTask.cost_gaussianBandit (ν_sphereTask _) hσ2
    (mem_simplex_iff.1 (sphereAlloc_mem_simplex hρ h)).1, ← Finset.sum_div]
  refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (by positivity))
  set r := sphereShift c ρ μ with hr_def
  set s := ∑ a, |μ a - c a| with hs_def
  set R := s ^ 2 + Fintype.card α * (ρ ^ 2 - ∑ a, (μ a - c a) ^ 2) with hR_def
  set L := ∑ b, (|μ b - c b| + r) with hL_def
  clear_value r s R L
  have hL : 0 < L := hsum ▸ Real.sqrt_pos.2 hRpos
  -- The coordinates of `μ' - c` with the signs of those of `μ - c`.
  set x : α → ℝ := fun a ↦ sgn c μ a * (μ' a - c a) with hx
  have h_sq (a : α) : (μ a - μ' a) ^ 2 = (|μ a - c a| - x a) ^ 2 := by
    rw [← sgn_mul_sub, hx, ← mul_sub, sq_sgn_mul]
    ring
  have hx_sq : ∑ a, x a ^ 2 = ∑ a, (μ' a - c a) ^ 2 :=
    Finset.sum_congr rfl fun a _ ↦ sq_sgn_mul a _
  -- The identity `∑ a, (d a + r) (d a - x a)² = ∑ a, d a (d a + r - x a)² + r (∑ a, x a² - ρ²)
  -- + r² ∑ a, (d a + r)`, whose first two terms are nonnegative.
  have h_id : ∑ a, (|μ a - c a| + r) * (|μ a - c a| - x a) ^ 2 =
      ∑ a, |μ a - c a| * (|μ a - c a| + r - x a) ^ 2 +
        r * (∑ a, (μ' a - c a) ^ 2 - ρ ^ 2) + r ^ 2 * L := by
    rw [← hx_sq, ← h_sphere, hL_def]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  have h_nonneg : 0 ≤ ∑ a, |μ a - c a| * (|μ a - c a| + r - x a) ^ 2 :=
    Finset.sum_nonneg fun a _ ↦ mul_nonneg (abs_nonneg _) (sq_nonneg _)
  -- The alternative `μ'` and `μ` are on different sides of the sphere, and `r` has the sign of
  -- `ρ² - ∑ a, (μ a - c a)²`.
  have h_side : 0 ≤ r * (∑ a, (μ' a - c a) ^ 2 - ρ ^ 2) := by
    have h1 : 0 < (∑ a, (μ' a - c a) ^ 2 - ρ ^ 2) * (r * (√R + s)) := by
      rw [← hq]
      linarith
    have h2 : 0 < √R + s := by linarith [hsum ▸ hL]
    nlinarith
  have h_sum : ∑ a, (|μ a - c a| + r) / L * (μ a - μ' a) ^ 2 =
      (∑ a, (|μ a - c a| + r) * (|μ a - c a| - x a) ^ 2) / L := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [h_sq]; ring
  rw [h_sum, le_div_iff₀ hL, h_id]
  linarith

/-- **The cost of the alternatives at the optimal allocation of Gaussian sphere identification**
[DK19, Lemma 39]. For Gaussian arms with a common variance `σ2 ≠ 0`, a sphere of center `c` and
radius `ρ ≠ 0`, a vector of means `μ` off the sphere, its correct answer `i` and
`r = sphereShift c ρ μ` with `|μ a - c a| + r ≥ 0` on every arm, the allocation
`w* a = (|μ a - c a| + r) / ∑ b, (|μ b - c b| + r)` has `D(μ, w*, ¬i) = r² / (2 σ2)`. -/
theorem altCost_sphereTask_gaussianBandit (hσ2 : σ2 ≠ 0) (hρ : ρ ≠ 0)
    (hμ : ∑ a, (μ a - c a) ^ 2 ≠ ρ ^ 2) (hi : i = true ↔ ∑ a, (μ a - c a) ^ 2 < ρ ^ 2)
    (h : ∀ a, 0 ≤ |μ a - c a| + sphereShift c ρ μ) :
    (sphereTask (Bandits.gaussianBandit · σ2) c ρ).altCost μ
        (fun a ↦ (|μ a - c a| + sphereShift c ρ μ) / ∑ b, (|μ b - c b| + sphereShift c ρ μ)) i =
      ENNReal.ofReal (sphereShift c ρ μ ^ 2 / (2 * σ2)) :=
  le_antisymm (altCost_sphereTask_gaussianBandit_le hσ2 hρ hμ hi h (sphereAlloc_mem_simplex hρ h))
    (by
      rw [IdentTask.altCost_def]
      exact le_iInf₂ fun _ hμ' ↦ le_cost_sphereTask_gaussianBandit hσ2 hρ hμ hi h hμ')

/-- **The game value of Gaussian sphere identification** [DK19, Lemma 39]. Under the assumptions
of `altCost_sphereTask_gaussianBandit`, `D(μ, ¬i) = r² / (2 σ2)` for `r = sphereShift c ρ μ`. -/
theorem answerValue_sphereTask_gaussianBandit (hσ2 : σ2 ≠ 0) (hρ : ρ ≠ 0)
    (hμ : ∑ a, (μ a - c a) ^ 2 ≠ ρ ^ 2) (hi : i = true ↔ ∑ a, (μ a - c a) ^ 2 < ρ ^ 2)
    (h : ∀ a, 0 ≤ |μ a - c a| + sphereShift c ρ μ) :
    (sphereTask (Bandits.gaussianBandit · σ2) c ρ).answerValue μ i =
      ENNReal.ofReal (sphereShift c ρ μ ^ 2 / (2 * σ2)) := by
  refine le_antisymm ?_ ?_
  · rw [IdentTask.answerValue_def]
    exact iSup₂_le fun w hw ↦ altCost_sphereTask_gaussianBandit_le hσ2 hρ hμ hi h hw
  rw [← altCost_sphereTask_gaussianBandit hσ2 hρ hμ hi h]
  exact IdentTask.altCost_le_answerValue _ (sphereAlloc_mem_simplex hρ h)

/-- **An optimal allocation of Gaussian sphere identification** [DK19, Lemma 39]. Under the
assumptions of `altCost_sphereTask_gaussianBandit`, the allocation
`w* a = (|μ a - c a| + r) / ∑ b, (|μ b - c b| + r)` is optimal. It is the allocation
`1 / K + (|μ a - c a| - s / K) / √(s² + K (ρ² - q))` of [DK19], since the denominator
`∑ b, (|μ b - c b| + r)` is `√(s² + K (ρ² - q))`. -/
theorem mem_optAlloc_sphereTask_gaussianBandit (hσ2 : σ2 ≠ 0) (hρ : ρ ≠ 0)
    (hμ : ∑ a, (μ a - c a) ^ 2 ≠ ρ ^ 2) (hi : i = true ↔ ∑ a, (μ a - c a) ^ 2 < ρ ^ 2)
    (h : ∀ a, 0 ≤ |μ a - c a| + sphereShift c ρ μ) :
    (fun a ↦ (|μ a - c a| + sphereShift c ρ μ) / ∑ b, (|μ b - c b| + sphereShift c ρ μ)) ∈
      (sphereTask (Bandits.gaussianBandit · σ2) c ρ).optAlloc μ i := by
  rw [IdentTask.mem_optAlloc_iff, altCost_sphereTask_gaussianBandit hσ2 hρ hμ hi h,
    answerValue_sphereTask_gaussianBandit hσ2 hρ hμ hi h]
  exact ⟨sphereAlloc_mem_simplex hρ h, rfl⟩

/-- **The characteristic time of Gaussian sphere identification** [DK19, Lemma 39]. For Gaussian
arms with a common variance `σ2 ≠ 0`, a sphere of center `c` and radius `ρ ≠ 0` and a vector of
means `μ` off the sphere with `|μ a - c a| + r ≥ 0` on every arm for `r = sphereShift c ρ μ`,
`T*(μ) = 2 σ2 / r²`. -/
theorem charTime_sphereTask_gaussianBandit (hσ2 : σ2 ≠ 0) (hρ : ρ ≠ 0)
    (hμ : ∑ a, (μ a - c a) ^ 2 ≠ ρ ^ 2) (h : ∀ a, 0 ≤ |μ a - c a| + sphereShift c ρ μ) :
    (sphereTask (Bandits.gaussianBandit · σ2) c ρ).charTime μ =
      ENNReal.ofReal (2 * σ2 / sphereShift c ρ μ ^ 2) := by
  have hr := sphereShift_ne_zero hρ hμ h
  have hσ2' : (0 : ℝ) < σ2 := by positivity
  rw [IdentTask.charTime_eq_inv_answerValue _ (correct_sphereTask_eq_singleton _),
    answerValue_sphereTask_gaussianBandit hσ2 hρ hμ (by simp) h,
    ← ENNReal.ofReal_inv_of_pos (div_pos (sq_pos_of_ne_zero hr) (by positivity)), inv_div]

end LMLExplore.Identification
