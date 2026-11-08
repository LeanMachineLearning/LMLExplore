/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Convex.Simplex
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Minimizers of linear functions plus the ½-Tsallis potential on the simplex

For a vector `L : α → ℝ` over a finite nonempty set `α` and `c > 0`, the function
`p ↦ L ⬝ᵥ p - c ∑ a, √(p a)` is strictly convex on the probability simplex `simplex α`: it is a
linear function plus `c` times the ½-Tsallis potential `-∑ a, √(p a)`, up to the normalization of
the Tsallis entropy. It has a unique minimizer there, whose coordinates are given by a closed
form [ZS21]: the first-order condition
`L a - c / (2 √(p a)) = λ` with a Lagrange multiplier `λ < min L` gives
`p a = (c / (2 (L a - λ))) ^ 2`, where `λ` is the unique solution of
`∑ a, (c / (2 (L a - λ))) ^ 2 = 1` below every `L a`. The left-hand side is increasing in
`λ < min L`, small for `λ` far below `min L` and at least `1` for `λ = min L - c / 2`, so the
normalizer `λ` exists and is unique. Every coordinate of the minimizer is positive, as the
derivative of `-√` diverges at `0`, and the minimizer does not change when a constant is added to
every coordinate of `L`.

These are the weights of the Tsallis-INF algorithm for adversarial bandits [ZS21]: at round `t`
they minimize `⟨L̂, p⟩ - 4 √(t + 1) ∑ a, √(p a)` for the cumulative loss estimates `L̂` of the
rounds before `t`, which is follow the regularized leader with the ½-Tsallis potential
[ZS21], [Ora, Section 9.1.2].

## Main definitions

* `LMLExplore.tsallisNormalizer c L`: the normalizer `λ`, the supremum of the levels
  `r < min L` with `∑ a, (c / (2 (L a - r))) ^ 2 ≤ 1`.
* `LMLExplore.tsallisWeights c L`: the vector `a ↦ (c / (2 (L a - λ))) ^ 2`.

## Main statements

* `tsallisNormalizer_eq_iff`: for `c ≠ 0`, `λ` is the unique level `r` below every `L a` with
  `∑ a, (c / (2 (L a - r))) ^ 2 = 1`.
* `tsallisWeights_pos`, `tsallisWeights_mem_simplex`: for `c ≠ 0`, the weights are positive and
  form a probability vector.
* `sub_div_two_mul_sqrt_tsallisWeights`: the first-order condition
  `L a - c / (2 √(p a)) = λ`, for `c > 0`.
* `dotProduct_sub_mul_sum_sqrt_sub_eq_sum`: for `c > 0` and `q` in the simplex, the excess of the
  objective at `q` over its value at the weights `p` is `∑ a, c (√(q a) - √(p a)) ^ 2 / (2 √(p a))`.
* `isMinOn_tsallisWeights`, `isMinOn_iff_eq_tsallisWeights`: for `c > 0`, the weights minimize the
  objective over the simplex, and they are its only minimizer there.
* `tsallisNormalizer_add_const`, `tsallisWeights_add_const`: adding `r` to every coordinate of `L`
  adds `r` to the normalizer and leaves the weights unchanged.
* `tsallisNormalizer_const`, `tsallisWeights_const`: for a constant vector `r`, the normalizer is
  `r - |c| √k / 2` and the weights are uniform, with `k` the cardinality of `α`.
* `measurable_tsallisNormalizer`, `measurable_tsallisWeights`: both are measurable in `L`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
* [ZS21] J. Zimmert and Y. Seldin, *Tsallis-INF: an optimal algorithm for stochastic and
  adversarial bandits*, JMLR 22 (2021).
-/

public section

open Finset Set

namespace LMLExplore

variable {α : Type*} [Fintype α] {c r : ℝ} {L : α → ℝ}

/-- The **normalizer of the Tsallis weights** of `L` with coefficient `c`: the supremum of the
levels `r` below every `L a` with `∑ a, (c / (2 (L a - r))) ^ 2 ≤ 1`. For `c ≠ 0` and `α`
nonempty, it is the unique such level with equality (`tsallisNormalizer_eq_iff`). -/
noncomputable def tsallisNormalizer (c : ℝ) (L : α → ℝ) : ℝ :=
  sSup {r | (∀ a, r < L a) ∧ ∑ a, (c / (2 * (L a - r))) ^ 2 ≤ 1}

/-- The **Tsallis weights** of `L` with coefficient `c`: the vector
`a ↦ (c / (2 (L a - λ))) ^ 2`, with `λ` the normalizer `tsallisNormalizer c L`. For `c > 0` it is
the unique minimizer of `p ↦ L ⬝ᵥ p - c ∑ a, √(p a)` over the simplex
(`isMinOn_iff_eq_tsallisWeights`). -/
noncomputable def tsallisWeights (c : ℝ) (L : α → ℝ) : α → ℝ :=
  fun a ↦ (c / (2 * (L a - tsallisNormalizer c L))) ^ 2

lemma tsallisNormalizer_def (c : ℝ) (L : α → ℝ) :
    tsallisNormalizer c L = sSup {r | (∀ a, r < L a) ∧ ∑ a, (c / (2 * (L a - r))) ^ 2 ≤ 1} :=
  (rfl)

lemma tsallisWeights_apply (c : ℝ) (L : α → ℝ) (a : α) :
    tsallisWeights c L a = (c / (2 * (L a - tsallisNormalizer c L))) ^ 2 := (rfl)

/-- Each term `(c / (2 x)) ^ 2` is strictly decreasing in `x > 0`, for `c ≠ 0`. -/
private lemma sq_div_two_mul_lt (hc : c ≠ 0) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    (c / (2 * y)) ^ 2 < (c / (2 * x)) ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  rw [div_pow, div_pow]
  gcongr

/-- The sum `∑ a, (c / (2 (L a - r))) ^ 2` is strictly increasing in the levels `r` below every
`L a`, for `c ≠ 0`. -/
private lemma strictMonoOn_sum_sq_div (hc : c ≠ 0) [Nonempty α] :
    StrictMonoOn (fun r ↦ ∑ a, (c / (2 * (L a - r))) ^ 2) {r | ∀ a, r < L a} :=
  fun _ _ _ hr' hrr' ↦ Finset.sum_lt_sum_of_nonempty univ_nonempty fun a _ ↦
    sq_div_two_mul_lt hc (sub_pos.2 (hr' a)) (by linarith)

/-- For `c ≠ 0`, some level `r` below every `L a` has `∑ a, (c / (2 (L a - r))) ^ 2 = 1`, by the
intermediate value theorem between `min L - |c| k / 2` and `min L - |c| / 2`, with `k` the
cardinality of `α`. -/
private lemma exists_sum_sq_div_eq_one (hc : c ≠ 0) [Nonempty α] (L : α → ℝ) :
    ∃ r, (∀ a, r < L a) ∧ ∑ a, (c / (2 * (L a - r))) ^ 2 = 1 := by
  obtain ⟨a₀, -, ha₀⟩ := exists_min_image univ L univ_nonempty
  have hk : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hc' : 0 < |c| := abs_pos.2 hc
  have hr₀₁ : L a₀ - |c| * Fintype.card α / 2 ≤ L a₀ - |c| / 2 := by
    have := mul_le_mul_of_nonneg_left hk hc'.le
    linarith
  have hlt : ∀ r ∈ Icc (L a₀ - |c| * Fintype.card α / 2) (L a₀ - |c| / 2), ∀ a, r < L a :=
    fun r hr a ↦ by linarith [hr.2, ha₀ a (mem_univ a)]
  have hcont : ContinuousOn (fun r ↦ ∑ a, (c / (2 * (L a - r))) ^ 2)
      (Icc (L a₀ - |c| * Fintype.card α / 2) (L a₀ - |c| / 2)) := by
    refine continuousOn_finsetSum _ fun a _ ↦ ContinuousOn.pow (continuousOn_const.div
      (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)) fun r hr ↦ ?_) 2
    exact mul_ne_zero two_ne_zero (sub_pos.2 (hlt r hr a)).ne'
  -- at the lower level every term is at most `1 / k ^ 2`
  have h₀ : ∑ a, (c / (2 * (L a - (L a₀ - |c| * Fintype.card α / 2)))) ^ 2 ≤ 1 := by
    calc ∑ a, (c / (2 * (L a - (L a₀ - |c| * Fintype.card α / 2)))) ^ 2
        ≤ ∑ _a : α, (1 : ℝ) / (Fintype.card α : ℝ) ^ 2 := by
          refine sum_le_sum fun a _ ↦ ?_
          have hx : |c| * Fintype.card α ≤ 2 * (L a - (L a₀ - |c| * Fintype.card α / 2)) := by
            linarith [ha₀ a (mem_univ a)]
          have hx0 : 0 < |c| * Fintype.card α := by positivity
          rw [div_pow, div_le_div_iff₀ (pow_pos (by linarith) 2) (by positivity), one_mul,
            ← sq_abs c]
          calc |c| ^ 2 * (Fintype.card α : ℝ) ^ 2 = (|c| * Fintype.card α) ^ 2 := by ring
          _ ≤ _ := pow_le_pow_left₀ hx0.le hx 2
      _ = (1 : ℝ) / Fintype.card α := by
          rw [sum_const, card_univ, nsmul_eq_mul]
          field_simp
      _ ≤ 1 := (div_le_one (by positivity)).2 hk
  -- at the upper level the term of `a₀` is `1`
  have h₁ : 1 ≤ ∑ a, (c / (2 * (L a - (L a₀ - |c| / 2)))) ^ 2 := by
    have h_term : (c / (2 * (L a₀ - (L a₀ - |c| / 2)))) ^ 2 = 1 := by
      rw [show 2 * (L a₀ - (L a₀ - |c| / 2)) = |c| by ring, div_pow, sq_abs,
        div_self (pow_ne_zero 2 hc)]
    rw [← h_term]
    exact single_le_sum (f := fun a ↦ (c / (2 * (L a - (L a₀ - |c| / 2)))) ^ 2)
      (fun a _ ↦ sq_nonneg _) (mem_univ a₀)
  obtain ⟨r, hr, hr1⟩ := intermediate_value_Icc hr₀₁ hcont ⟨h₀, h₁⟩
  exact ⟨r, hlt r hr, hr1⟩

/-- **Characterization of the normalizer.** For `c ≠ 0` and `α` nonempty, `tsallisNormalizer c L`
is the unique level `r` below every `L a` with `∑ a, (c / (2 (L a - r))) ^ 2 = 1`. -/
theorem tsallisNormalizer_eq_iff (hc : c ≠ 0) [Nonempty α] :
    tsallisNormalizer c L = r ↔ (∀ a, r < L a) ∧ ∑ a, (c / (2 * (L a - r))) ^ 2 = 1 := by
  obtain ⟨r₀, hr₀, hsum⟩ := exists_sum_sq_div_eq_one hc L
  -- the levels in the supremum are exactly those below `r₀`
  have hset : {r | (∀ a, r < L a) ∧ ∑ a, (c / (2 * (L a - r))) ^ 2 ≤ 1} = Iic r₀ := by
    ext r
    simp only [mem_ofPred_eq, Set.mem_Iic]
    constructor
    · rintro ⟨hr, hle⟩
      by_contra hlt
      have := strictMonoOn_sum_sq_div hc hr₀ hr (not_le.1 hlt)
      simp only at this
      linarith
    · intro hle
      have hr : ∀ a, r < L a := fun a ↦ hle.trans_lt (hr₀ a)
      exact ⟨hr, hsum ▸ (strictMonoOn_sum_sq_div hc).monotoneOn hr hr₀ hle⟩
  rw [tsallisNormalizer_def, hset, csSup_Iic]
  constructor
  · rintro rfl
    exact ⟨hr₀, hsum⟩
  · rintro ⟨hr, hsum'⟩
    exact (strictMonoOn_sum_sq_div hc).injOn hr₀ hr (hsum.trans hsum'.symm)

/-- For `c ≠ 0`, the normalizer lies below every coordinate of `L`. -/
theorem tsallisNormalizer_lt (hc : c ≠ 0) [Nonempty α] (L : α → ℝ) (a : α) :
    tsallisNormalizer c L < L a :=
  ((tsallisNormalizer_eq_iff hc).1 rfl).1 a

/-- For `c ≠ 0`, the Tsallis weights sum to `1`. -/
theorem sum_tsallisWeights (hc : c ≠ 0) [Nonempty α] (L : α → ℝ) :
    ∑ a, tsallisWeights c L a = 1 := by
  simp_rw [tsallisWeights_apply]
  exact ((tsallisNormalizer_eq_iff hc).1 rfl).2

/-- For `c ≠ 0`, every Tsallis weight is positive. -/
theorem tsallisWeights_pos (hc : c ≠ 0) [Nonempty α] (L : α → ℝ) (a : α) :
    0 < tsallisWeights c L a := by
  have := sub_pos.2 (tsallisNormalizer_lt hc L a)
  rw [tsallisWeights_apply]
  positivity

/-- For `c ≠ 0`, the Tsallis weights form a probability vector. -/
theorem tsallisWeights_mem_simplex (hc : c ≠ 0) [Nonempty α] (L : α → ℝ) :
    tsallisWeights c L ∈ simplex α :=
  mem_simplex_iff.2 ⟨fun a ↦ (tsallisWeights_pos hc L a).le, sum_tsallisWeights hc L⟩

/-- For `c > 0`, the square root of the Tsallis weight of `a` is `c / (2 (L a - λ))`. -/
theorem sqrt_tsallisWeights (hc : 0 < c) [Nonempty α] (L : α → ℝ) (a : α) :
    √(tsallisWeights c L a) = c / (2 * (L a - tsallisNormalizer c L)) := by
  have := sub_pos.2 (tsallisNormalizer_lt hc.ne' L a)
  rw [tsallisWeights_apply, Real.sqrt_sq (by positivity)]

/-- **First-order condition.** For `c > 0`, the Tsallis weights `p` satisfy
`L a - c / (2 √(p a)) = λ` for every `a`: the gradient of `p ↦ L ⬝ᵥ p - c ∑ a, √(p a)` at `p` is
the constant vector `λ`, with `λ` the normalizer. -/
theorem sub_div_two_mul_sqrt_tsallisWeights (hc : 0 < c) [Nonempty α] (L : α → ℝ) (a : α) :
    L a - c / (2 * √(tsallisWeights c L a)) = tsallisNormalizer c L := by
  have := sub_pos.2 (tsallisNormalizer_lt hc.ne' L a)
  rw [sqrt_tsallisWeights hc]
  field_simp
  ring

/-- The algebraic identity behind the optimality of the Tsallis weights: for `y > 0`,
`(l + c / (2 y)) (x ^ 2 - y ^ 2) - c (x - y) = l (x ^ 2 - y ^ 2) + c (x - y) ^ 2 / (2 y)`. -/
private lemma add_div_mul_sub_sub_eq {l x y : ℝ} (hy : 0 < y) :
    (l + c / (2 * y)) * (x ^ 2 - y ^ 2) - c * (x - y) =
      l * (x ^ 2 - y ^ 2) + c * (x - y) ^ 2 / (2 * y) := by
  field_simp
  ring

/-- **The objective above its minimum.** For `c > 0` and `q` in the simplex, with `p` the Tsallis
weights of `L`, the excess of `L ⬝ᵥ q - c ∑ a, √(q a)` over its value at `p` is
`∑ a, c (√(q a) - √(p a)) ^ 2 / (2 √(p a))`. -/
theorem dotProduct_sub_mul_sum_sqrt_sub_eq_sum (hc : 0 < c) [Nonempty α] (L : α → ℝ)
    {q : α → ℝ} (hq : q ∈ simplex α) :
    L ⬝ᵥ q - c * ∑ a, √(q a) - (L ⬝ᵥ tsallisWeights c L - c * ∑ a, √(tsallisWeights c L a)) =
      ∑ a, c * (√(q a) - √(tsallisWeights c L a)) ^ 2 / (2 * √(tsallisWeights c L a)) := by
  have hq' := mem_simplex_iff.1 hq
  have hp a : 0 < √(tsallisWeights c L a) := Real.sqrt_pos.2 (tsallisWeights_pos hc.ne' L a)
  -- write each coordinate of `L` through the first-order condition
  have hL a : L a = tsallisNormalizer c L + c / (2 * √(tsallisWeights c L a)) := by
    linarith [sub_div_two_mul_sqrt_tsallisWeights hc L a]
  have h_eq a : L a * (q a - tsallisWeights c L a) - c * (√(q a) - √(tsallisWeights c L a)) =
      tsallisNormalizer c L * (q a - tsallisWeights c L a) +
        c * (√(q a) - √(tsallisWeights c L a)) ^ 2 / (2 * √(tsallisWeights c L a)) := by
    have h := add_div_mul_sub_sub_eq (c := c) (l := tsallisNormalizer c L) (x := √(q a)) (hp a)
    rwa [Real.sq_sqrt (hq'.1 a), Real.sq_sqrt (tsallisWeights_pos hc.ne' L a).le, ← hL a] at h
  -- the multiplier term vanishes, as `q` and `p` both sum to `1`
  have h_mul : ∑ a, tsallisNormalizer c L * (q a - tsallisWeights c L a) = 0 := by
    rw [← mul_sum, sum_sub_distrib, hq'.2, sum_tsallisWeights hc.ne', sub_self, mul_zero]
  calc L ⬝ᵥ q - c * ∑ a, √(q a) - (L ⬝ᵥ tsallisWeights c L - c * ∑ a, √(tsallisWeights c L a))
      = ∑ a, (L a * (q a - tsallisWeights c L a) - c * (√(q a) - √(tsallisWeights c L a))) := by
        simp only [dotProduct, mul_sub, sum_sub_distrib, mul_sum]
        ring
    _ = _ := by rw [sum_congr rfl fun a _ ↦ h_eq a, sum_add_distrib, h_mul, zero_add]

/-- **The Tsallis weights are a minimizer.** For `c > 0`, the Tsallis weights of `L` minimize
`p ↦ L ⬝ᵥ p - c ∑ a, √(p a)` over the simplex. -/
theorem isMinOn_tsallisWeights (hc : 0 < c) [Nonempty α] (L : α → ℝ) :
    IsMinOn (fun p ↦ L ⬝ᵥ p - c * ∑ a, √(p a)) (simplex α) (tsallisWeights c L) := by
  refine isMinOn_iff.2 fun q hq ↦ ?_
  have h := dotProduct_sub_mul_sum_sqrt_sub_eq_sum hc L hq
  have hnn : 0 ≤ ∑ a, c * (√(q a) - √(tsallisWeights c L a)) ^ 2 /
      (2 * √(tsallisWeights c L a)) := sum_nonneg fun a _ ↦ by positivity
  linarith

/-- **Uniqueness of the minimizer.** For `c > 0`, a vector of the simplex on which
`p ↦ L ⬝ᵥ p - c ∑ a, √(p a)` is at most its value at the Tsallis weights is the Tsallis weights. -/
theorem eq_tsallisWeights_of_le (hc : 0 < c) [Nonempty α] {q : α → ℝ} (hq : q ∈ simplex α)
    (hle : L ⬝ᵥ q - c * ∑ a, √(q a) ≤
      L ⬝ᵥ tsallisWeights c L - c * ∑ a, √(tsallisWeights c L a)) :
    q = tsallisWeights c L := by
  have hp a : 0 < √(tsallisWeights c L a) := Real.sqrt_pos.2 (tsallisWeights_pos hc.ne' L a)
  have hnn a : 0 ≤ c * (√(q a) - √(tsallisWeights c L a)) ^ 2 / (2 * √(tsallisWeights c L a)) :=
    by have := hp a; positivity
  have hsum := dotProduct_sub_mul_sum_sqrt_sub_eq_sum hc L hq
  have hzero := (sum_eq_zero_iff_of_nonneg fun a _ ↦ hnn a).1
    (le_antisymm (hsum ▸ sub_nonpos.2 hle) (sum_nonneg fun a _ ↦ hnn a))
  funext a
  have ha := hzero a (mem_univ a)
  rw [div_eq_zero_iff, mul_eq_zero, pow_eq_zero_iff two_ne_zero, sub_eq_zero] at ha
  rcases ha with (h | h) | h
  · exact absurd h hc.ne'
  · exact (Real.sqrt_inj ((mem_simplex_iff.1 hq).1 a) (tsallisWeights_pos hc.ne' L a).le).1 h
  · exact absurd h (by have := hp a; positivity)

/-- For `c > 0`, a vector of the simplex minimizes `p ↦ L ⬝ᵥ p - c ∑ a, √(p a)` over the simplex
if and only if it is the Tsallis weights of `L`. -/
theorem isMinOn_iff_eq_tsallisWeights (hc : 0 < c) [Nonempty α] {q : α → ℝ}
    (hq : q ∈ simplex α) :
    IsMinOn (fun p ↦ L ⬝ᵥ p - c * ∑ a, √(p a)) (simplex α) q ↔ q = tsallisWeights c L := by
  refine ⟨fun h ↦ eq_tsallisWeights_of_le hc hq ?_, fun h ↦ h ▸ isMinOn_tsallisWeights hc L⟩
  exact isMinOn_iff.1 h _ (tsallisWeights_mem_simplex hc.ne' L)

/-- For `c ≠ 0`, adding `r` to every coordinate of `L` adds `r` to the normalizer. -/
theorem tsallisNormalizer_add_const (hc : c ≠ 0) [Nonempty α] (L : α → ℝ) (r : ℝ) :
    tsallisNormalizer c (fun a ↦ L a + r) = tsallisNormalizer c L + r := by
  obtain ⟨h_lt, h_sum⟩ := (tsallisNormalizer_eq_iff hc (L := L)).1 rfl
  refine (tsallisNormalizer_eq_iff hc).2 ⟨fun a ↦ by linarith [h_lt a], ?_⟩
  simpa only [add_sub_add_right_eq_sub] using h_sum

/-- **Shift invariance.** For `c ≠ 0`, adding a constant to every coordinate of `L` does not
change the Tsallis weights. -/
theorem tsallisWeights_add_const (hc : c ≠ 0) [Nonempty α] (L : α → ℝ) (r : ℝ) :
    tsallisWeights c (fun a ↦ L a + r) = tsallisWeights c L := by
  funext a
  rw [tsallisWeights_apply, tsallisWeights_apply, tsallisNormalizer_add_const hc,
    add_sub_add_right_eq_sub]

/-- For `c ≠ 0`, the normalizer of a constant vector `r` is `r - |c| √k / 2`, with `k` the
cardinality of `α`. -/
theorem tsallisNormalizer_const (hc : c ≠ 0) [Nonempty α] (r : ℝ) :
    tsallisNormalizer c (fun _ : α ↦ r) = r - |c| * √(Fintype.card α) / 2 := by
  have hk : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hc' : 0 < |c| := abs_pos.2 hc
  refine (tsallisNormalizer_eq_iff hc).2
    ⟨fun _ ↦ by have := mul_pos hc' (Real.sqrt_pos.2 hk); linarith, ?_⟩
  rw [sum_const, card_univ, nsmul_eq_mul, show 2 * (r - (r - |c| * √(Fintype.card α) / 2)) =
    |c| * √(Fintype.card α) by ring, div_pow, mul_pow, sq_abs, Real.sq_sqrt hk.le]
  field_simp

/-- For `c ≠ 0`, the Tsallis weights of a constant vector are uniform. -/
theorem tsallisWeights_const (hc : c ≠ 0) [Nonempty α] (r : ℝ) :
    tsallisWeights c (fun _ : α ↦ r) = fun _ ↦ (Fintype.card α : ℝ)⁻¹ := by
  have hk : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  funext a
  rw [tsallisWeights_apply, tsallisNormalizer_const hc, show 2 * (r - (r - |c| *
    √(Fintype.card α) / 2)) = |c| * √(Fintype.card α) by ring, div_pow, mul_pow, sq_abs,
    Real.sq_sqrt hk.le]
  field_simp

/-- For `c ≠ 0`, the normalizer is a measurable function of `L`: it exceeds `r` exactly when `r`
lies below every `L a` with `∑ a, (c / (2 (L a - r))) ^ 2 < 1`. -/
@[fun_prop]
theorem measurable_tsallisNormalizer (hc : c ≠ 0) [Nonempty α] :
    Measurable (tsallisNormalizer (α := α) c) := by
  refine measurable_of_Ioi fun r ↦ ?_
  have h_pre : tsallisNormalizer c ⁻¹' Ioi r =
      {L : α → ℝ | ∀ a, r < L a} ∩ {L | ∑ a, (c / (2 * (L a - r))) ^ 2 < 1} := by
    ext L
    obtain ⟨h_lt, h_sum⟩ := (tsallisNormalizer_eq_iff hc (L := L)).1 rfl
    simp only [Set.mem_preimage, Set.mem_Ioi, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hr
      have hr' : ∀ a, r < L a := fun a ↦ hr.trans (h_lt a)
      exact ⟨hr', h_sum ▸ strictMonoOn_sum_sq_div hc hr' h_lt hr⟩
    · rintro ⟨hr', hlt⟩
      by_contra hle
      have := (strictMonoOn_sum_sq_div hc).monotoneOn h_lt hr' (not_lt.1 hle)
      linarith
  rw [h_pre, ofPred_forall]
  refine (MeasurableSet.iInter fun a ↦ measurableSet_lt measurable_const
    (measurable_pi_apply a)).inter (measurableSet_lt ?_ measurable_const)
  exact Finset.measurable_sum _ fun a _ ↦ (measurable_const.div (measurable_const.mul
    ((measurable_pi_apply a).sub measurable_const))).pow_const 2

/-- For `c ≠ 0`, the Tsallis weights are a measurable function of `L`. -/
@[fun_prop]
theorem measurable_tsallisWeights (hc : c ≠ 0) [Nonempty α] :
    Measurable (tsallisWeights (α := α) c) := by
  refine measurable_pi_iff.2 fun a ↦ ?_
  simp_rw [tsallisWeights_apply]
  exact (measurable_const.div (measurable_const.mul ((measurable_pi_apply a).sub
    (measurable_tsallisNormalizer hc)))).pow_const 2

end LMLExplore
