/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.ExpFamily
public import LMLExplore.Identification.Task.Classical

/-!
# The pure exploration game of half-space identification with Gaussian arms

In half-space identification (`halfSpaceTask ν id u`) the correct answer of a vector of means `μ` is
the sign of `u ⬝ᵥ μ`, and the alternatives to it are the vectors of means `λ` with `u ⬝ᵥ λ` of the
other sign. Let the arm `a` have the Gaussian law of mean `μ a` and known variance `v a ≠ 0`. The
transportation cost `∑ a, w a (μ a - λ a)² / (2 v a)` is a weighted squared distance, and the game
has a closed form [DK19, Lemma 36]. Write `L = ∑ a, |u a| √(v a)`.

* For a nonnegative allocation `w` that is positive on the arms with `u a ≠ 0`, the cost of the
  alternatives is the squared distance from `μ` to the hyperplane `u ⬝ᵥ λ = 0` in the norm
  weighted by `w a / v a`, `D(μ, w, ¬i) = (u ⬝ᵥ μ)² / (2 ∑ a, u a² v a / w a)`: by the
  Cauchy–Schwarz inequality, moving `μ` across the hyperplane costs at least this much, and
  moving it along the direction
  `u a v a / w a` costs arbitrarily little more. If instead `w a = 0` for some arm with `u a ≠ 0`,
  the mean of that arm can be moved for free and `D(μ, w, ¬i) = 0`.
* Applied to the vector `(u a √(v a))_a`, the inequality `‖x‖₁² ≤ ∑ a, x a² / w a` on the
  allocations of the simplex that are positive where `x a ≠ 0`, with equality, for `x ≠ 0`, exactly
  at `w a = |x a| / ‖x‖₁` (`LMLExplore.sq_sum_abs_lt_sum_sq_div`), gives
  `L² ≤ ∑ a, u a² v a / w a`, with equality exactly at `w a = |u a| √(v a) / L`; the other
  allocations have `D(μ, w, ¬i) = 0` by the previous point. Hence `D(μ, ¬i) = (u ⬝ᵥ μ)² / (2 L²)`,
  the only optimal allocation is `|u a| √(v a) / L`, and `T*(μ) = 2 L² / (u ⬝ᵥ μ)²`.

These values are the divergences of [DK19, Lemma 36], stated there for the hyperplane, which is
the boundary of the set of alternatives. Under the normalization `L = 1`, [D23, Lemma 15] finds
the value `2 / (u ⬝ᵥ μ)²` for the static-proportions difficulty, which this file does not define;
this matches `T*(μ)` here. The cost in that difficulty has the alternative first, which does not
matter since the Gaussian cost is symmetric
(`LMLExplore.Identification.IdentTask.cost_comm_gaussianReal`).

The Cauchy–Schwarz lower bound `le_cost_halfSpaceTask_gaussianReal` and the bound
`altCost_halfSpaceTask_gaussianReal_le` obtained by moving along a direction are adapted from the
formalization Degenne2023Existence (`github.com/RemyDegenne/Degenne2023Existence`, file
`ForLMLExplore/Identification/Task/HalfSpace.lean`, commit
`76f5b36f9219535e1049ef12f781fb5426a2b835`, by Rémy Degenne, Apache 2.0) of [D23].

## Main statements

* `LMLExplore.Identification.mem_alt_halfSpaceTask_iff`: the alternatives of half-space
  identification.
* `LMLExplore.Identification.le_cost_halfSpaceTask_gaussianReal`: crossing the hyperplane costs at
  least `(u ⬝ᵥ μ)² / (2 ∑ a, u a² v a / w a)`.
* `LMLExplore.Identification.altCost_halfSpaceTask_gaussianReal_le`: moving `μ` across the
  hyperplane along a direction `d` with `u ⬝ᵥ d = 1` bounds the cost of the alternatives.
* `LMLExplore.Identification.altCost_halfSpaceTask_gaussianReal`,
  `LMLExplore.Identification.altCost_halfSpaceTask_gaussianReal_eq_zero`: the cost of the
  alternatives for every nonnegative allocation.
* `LMLExplore.Identification.answerValue_halfSpaceTask_gaussianReal`,
  `LMLExplore.Identification.optAlloc_halfSpaceTask_gaussianReal`,
  `LMLExplore.Identification.charTime_halfSpaceTask_gaussianReal`: the value of the game, the
  unique optimal allocation and the characteristic time [DK19, Lemma 36]; cf. [D23, Lemma 15].

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, supplementary material, Appendix H, Lemma 36.
* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α Θ 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} [Fintype α]
  {u μ w : α → ℝ} {i : Bool}

/-- The alternatives to the answer `i` in half-space identification are the models `θ'` with
`u ⬝ᵥ mean θ' ≠ 0` whose sign is not the one `i` prescribes. -/
lemma mem_alt_halfSpaceTask_iff (ν : Θ → Kernel α 𝓨) [∀ θ, IsMarkovKernel (ν θ)]
    (mean : Θ → α → ℝ) {θ' : Θ} :
    θ' ∈ (halfSpaceTask ν mean u).alt i ↔
      u ⬝ᵥ mean θ' ≠ 0 ∧ ¬ (i = true ↔ 0 < u ⬝ᵥ mean θ') := by
  simp only [IdentTask.mem_alt_iff, M_halfSpaceTask, correct_halfSpaceTask, Set.mem_ofPred_eq]

/-! ### Gaussian arms -/

variable {ν : (α → ℝ) → Kernel α ℝ} [∀ μ, IsMarkovKernel (ν μ)] {v : α → ℝ≥0}

/-- The arm laws of half-space identification for the Gaussian arms `ν μ a = 𝒩(μ a, v a)`. -/
private lemma ν_halfSpaceTask_apply (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (μ : α → ℝ)
    (a : α) : (halfSpaceTask ν id u).ν μ a = gaussianReal (μ a) (v a) := by
  rw [ν_halfSpaceTask, hν]

omit [Fintype α] in
/-- Variances `v a ≠ 0` are positive. -/
private lemma coe_variance_pos (hv : ∀ a, v a ≠ 0) (a : α) : (0 : ℝ) < v a :=
  NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hv a))

/-- **Moving across the hyperplane along a direction.** For a direction `d` with `u ⬝ᵥ d = 1`, the
vectors `μ - t (u ⬝ᵥ μ) d` with `t > 1` are alternatives, which bounds the cost of the alternatives
by `(u ⬝ᵥ μ)² ∑ a, w a d a² / (2 v a)` in the limit `t → 1`. -/
lemma altCost_halfSpaceTask_gaussianReal_le (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hμ : u ⬝ᵥ μ ≠ 0)
    (hi : i = true ↔ 0 < u ⬝ᵥ μ) (hw : 0 ≤ w) {d : α → ℝ} (hd : u ⬝ᵥ d = 1) :
    (halfSpaceTask ν id u).altCost μ w i ≤
      ENNReal.ofReal ((u ⬝ᵥ μ) ^ 2 * ∑ a, w a * d a ^ 2 / (2 * v a)) := by
  set C := (u ⬝ᵥ μ) ^ 2 * ∑ a, w a * d a ^ 2 / (2 * v a)
  have key (t : ℝ) (ht : 1 < t) :
      (halfSpaceTask ν id u).altCost μ w i ≤ ENNReal.ofReal (t ^ 2 * C) := by
    have h_dot : u ⬝ᵥ (μ - (t * u ⬝ᵥ μ) • d) = (1 - t) * u ⬝ᵥ μ := by
      rw [dotProduct_sub, dotProduct_smul, hd, smul_eq_mul]
      ring
    have hmem : μ - (t * u ⬝ᵥ μ) • d ∈ (halfSpaceTask ν id u).alt i := by
      rw [mem_alt_halfSpaceTask_iff, id_eq, h_dot, hi]
      refine ⟨mul_ne_zero (by linarith) hμ, ?_⟩
      rcases hμ.lt_or_gt with h | h
      · have : 0 < (1 - t) * u ⬝ᵥ μ := mul_pos_of_neg_of_neg (by linarith) h
        simp [this, h.not_gt]
      · have : (1 - t) * u ⬝ᵥ μ < 0 := mul_neg_of_neg_of_pos (by linarith) h
        simp [h, this.not_gt]
    refine (IdentTask.altCost_le_cost _ hmem w).trans_eq ?_
    rw [IdentTask.cost_gaussianReal hv (ν_halfSpaceTask_apply hν) hw]
    congr 1
    simp only [C, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_sub_cancel, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  have hlim : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (t ^ 2 * C)) (𝓝[>] 1)
      (𝓝 (ENNReal.ofReal C)) := by
    have hc : Continuous fun t : ℝ ↦ ENNReal.ofReal (t ^ 2 * C) :=
      ENNReal.continuous_ofReal.comp ((continuous_pow 2).mul continuous_const)
    simpa using hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (1 : ℝ)))
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)

/-- **Crossing the hyperplane costs at least the squared distance to it.** For a nonnegative
allocation `w` that is positive where `u` does not vanish, the transportation cost from `μ` to an
alternative is at least `(u ⬝ᵥ μ)² / (2 ∑ a, u a² v a / w a)`, by the Cauchy–Schwarz inequality
`(u ⬝ᵥ (μ - μ'))² ≤ (∑ a, u a² v a / w a) ∑ a, w a (μ a - μ' a)² / v a`. -/
lemma le_cost_halfSpaceTask_gaussianReal (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hi : i = true ↔ 0 < u ⬝ᵥ μ) (hw : 0 ≤ w)
    (hwu : ∀ a, w a = 0 → u a = 0) {μ' : α → ℝ} (hμ' : μ' ∈ (halfSpaceTask ν id u).alt i) :
    ENNReal.ofReal ((u ⬝ᵥ μ) ^ 2 / (2 * ∑ a, u a ^ 2 * v a / w a)) ≤
      (halfSpaceTask ν id u).cost w μ μ' := by
  rw [IdentTask.cost_gaussianReal hv (ν_halfSpaceTask_apply hν) hw]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mem_alt_halfSpaceTask_iff, id_eq, hi] at hμ'
  obtain ⟨hne, hsign⟩ := hμ'
  -- `μ` and `μ'` are on different sides of the hyperplane.
  have h_sign : u ⬝ᵥ μ * u ⬝ᵥ μ' ≤ 0 := by
    rcases hne.lt_or_gt with h | h
    · have hs : 0 < u ⬝ᵥ μ := by
        by_contra hs
        exact hsign (iff_of_false hs h.not_gt)
      nlinarith
    · have hs : u ⬝ᵥ μ ≤ 0 := not_lt.1 fun hs ↦ hsign (iff_of_true hs h)
      nlinarith
  have h1 : (u ⬝ᵥ μ) ^ 2 ≤ (u ⬝ᵥ (μ - μ')) ^ 2 := by
    rw [dotProduct_sub]
    nlinarith
  have hS : 0 ≤ ∑ a, u a ^ 2 * v a / w a :=
    Finset.sum_nonneg fun a _ ↦ div_nonneg (mul_nonneg (sq_nonneg _) (v a).2) (hw a)
  have hG : 0 ≤ ∑ a, w a * (μ a - μ' a) ^ 2 / v a :=
    Finset.sum_nonneg fun a _ ↦ div_nonneg (mul_nonneg (hw a) (sq_nonneg _)) (v a).2
  have h2 : (u ⬝ᵥ (μ - μ')) ^ 2 ≤
      (∑ a, u a ^ 2 * v a / w a) * ∑ a, w a * (μ a - μ' a) ^ 2 / v a := by
    rw [dotProduct]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun a _ ↦ div_nonneg (mul_nonneg (sq_nonneg _) (v a).2) (hw a))
      (fun a _ ↦ div_nonneg (mul_nonneg (hw a) (sq_nonneg _)) (v a).2)
      fun a _ ↦ ?_
    rcases eq_or_ne (w a) 0 with h | h
    · simp [h, hwu a h]
    · have hva : (v a : ℝ) ≠ 0 := (coe_variance_pos hv a).ne'
      refine le_of_eq ?_
      simp only [Pi.sub_apply]
      field_simp
  have h_half : ∑ a, w a * (μ a - μ' a) ^ 2 / (2 * v a) =
      (∑ a, w a * (μ a - μ' a) ^ 2 / v a) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  rw [h_half, mul_comm 2, ← div_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact div_le_of_le_mul₀ hS hG (by linarith)

/-- **The cost of the alternatives in Gaussian half-space identification.** For Gaussian arms with
variances `v a ≠ 0`, a vector of means `μ` with `u ⬝ᵥ μ ≠ 0`, its correct answer `i` and a
nonnegative allocation `w` that is positive on the arms with `u a ≠ 0`,
`D(μ, w, ¬i) = (u ⬝ᵥ μ)² / (2 ∑ a, u a² v a / w a)`: the squared distance from `μ` to the
hyperplane `u ⬝ᵥ λ = 0` in the norm weighted by `w a / v a`. -/
theorem altCost_halfSpaceTask_gaussianReal (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hμ : u ⬝ᵥ μ ≠ 0)
    (hi : i = true ↔ 0 < u ⬝ᵥ μ) (hw : 0 ≤ w) (hwu : ∀ a, w a = 0 → u a = 0) :
    (halfSpaceTask ν id u).altCost μ w i =
      ENNReal.ofReal ((u ⬝ᵥ μ) ^ 2 / (2 * ∑ a, u a ^ 2 * v a / w a)) := by
  refine le_antisymm ?_ ?_
  swap
  · rw [IdentTask.altCost_def]
    exact le_iInf₂ fun μ' hμ' ↦ le_cost_halfSpaceTask_gaussianReal hv hν hi hw hwu hμ'
  have hva (a : α) : (v a : ℝ) ≠ 0 := (coe_variance_pos hv a).ne'
  set V := ∑ a, u a ^ 2 * v a / w a with hV
  have hV0 : V ≠ 0 := by
    intro h
    have hu (a : α) : u a = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun a _ ↦
        div_nonneg (mul_nonneg (sq_nonneg _) (v a).2) (hw a)).1 h a (Finset.mem_univ a)
      rcases div_eq_zero_iff.1 this with h | h
      · exact pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 h).resolve_right (hva a))
      · exact hwu a h
    exact hμ (by simp [dotProduct, hu])
  -- Move `μ` along the direction `u a v a / (w a V)`, which satisfies `u ⬝ᵥ d = 1`.
  have hd : u ⬝ᵥ (fun a ↦ u a * v a / (w a * V)) = 1 := by
    rw [dotProduct, ← div_self hV0, hV, Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  refine (altCost_halfSpaceTask_gaussianReal_le hv hν hμ hi hw hd).trans_eq
    (congrArg ENNReal.ofReal ?_)
  have h_term (a : α) : w a * (u a * v a / (w a * V)) ^ 2 / (2 * v a) =
      u a ^ 2 * v a / w a / (2 * V ^ 2) := by
    rcases eq_or_ne (w a) 0 with h | h
    · simp [h, hwu a h]
    · have := hva a
      field_simp
  rw [Finset.sum_congr rfl fun a _ ↦ h_term a, ← Finset.sum_div, ← hV]
  field_simp

/-- **Free alternatives in Gaussian half-space identification.** If an allocation `w ≥ 0` does not
sample an arm `a` with `u a ≠ 0`, the mean of `a` can be moved across the hyperplane at no cost,
and `D(μ, w, ¬i) = 0`. -/
theorem altCost_halfSpaceTask_gaussianReal_eq_zero (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hμ : u ⬝ᵥ μ ≠ 0)
    (hi : i = true ↔ 0 < u ⬝ᵥ μ) (hw : 0 ≤ w) {a : α} (hua : u a ≠ 0) (hwa : w a = 0) :
    (halfSpaceTask ν id u).altCost μ w i = 0 := by
  classical
  have hd : u ⬝ᵥ Pi.single a (u a)⁻¹ = 1 := by
    rw [dotProduct_single, mul_inv_cancel₀ hua]
  refine le_antisymm ((altCost_halfSpaceTask_gaussianReal_le hv hν hμ hi hw hd).trans_eq ?_)
    bot_le
  have h_sum : ∑ b, w b * Pi.single (M := fun _ ↦ ℝ) a (u a)⁻¹ b ^ 2 / (2 * v b) = 0 :=
    Finset.sum_eq_zero fun b _ ↦ by
      rcases eq_or_ne b a with rfl | h
      · simp [hwa]
      · simp [h]
  simp [h_sum]

omit [Fintype α] in
/-- The vector `(|u a| √(v a))_a` is the vector of absolute values of `(u a √(v a))_a`. -/
private lemma abs_mul_sqrt (a : α) : |u a * √(v a : ℝ)| = |u a| * √(v a : ℝ) := by
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

omit [Fintype α] in
/-- For variances `v a ≠ 0`, the vector `(u a √(v a))_a` vanishes exactly where `u` does. -/
private lemma mul_sqrt_eq_zero (hv : ∀ a, v a ≠ 0) {a : α} : u a * √(v a : ℝ) = 0 ↔ u a = 0 := by
  simp [(Real.sqrt_pos.2 (coe_variance_pos hv a)).ne']

omit [Fintype α] in
/-- For variances `v a ≠ 0` and `u ≠ 0`, the vector `(u a √(v a))_a` is nonzero. -/
private lemma mul_sqrt_ne_zero (hv : ∀ a, v a ≠ 0) (hu : u ≠ 0) :
    (fun a ↦ u a * √(v a : ℝ)) ≠ 0 := fun h ↦
  hu (funext fun a ↦ (mul_sqrt_eq_zero hv).1 (congrFun h a))

/-- For variances `v a ≠ 0` and `u ≠ 0`, `L = ∑ a, |u a| √(v a)` is nonzero. -/
private lemma sum_abs_mul_sqrt_ne_zero (hv : ∀ a, v a ≠ 0) (hu : u ≠ 0) :
    ∑ a, |u a| * √(v a : ℝ) ≠ 0 := by
  simpa only [abs_mul_sqrt] using sum_abs_ne_zero (mul_sqrt_ne_zero hv hu)

/-- The allocation `|u a| √(v a) / L` is the normalized absolute value of `(u a √(v a))_a`. -/
private lemma abs_mul_sqrt_div_eq :
    (fun a ↦ |u a| * √(v a : ℝ) / ∑ b, |u b| * √(v b : ℝ)) =
      fun a ↦ |u a * √(v a : ℝ)| / ∑ b, |u b * √(v b : ℝ)| := by
  simp_rw [abs_mul_sqrt]

/-- For variances `v a ≠ 0` and `u ≠ 0`, the allocation `|u a| √(v a) / L` belongs to the
simplex. -/
private lemma abs_mul_sqrt_div_mem_simplex (hv : ∀ a, v a ≠ 0) (hu : u ≠ 0) :
    (fun a ↦ |u a| * √(v a : ℝ) / ∑ b, |u b| * √(v b : ℝ)) ∈ simplex α := by
  rw [abs_mul_sqrt_div_eq]
  exact abs_div_sum_abs_mem_simplex (mul_sqrt_ne_zero hv hu)

/-- At the allocation `|u a| √(v a) / L`, the cost of the alternatives is
`(u ⬝ᵥ μ)² / (2 L²)`. -/
private lemma altCost_halfSpaceTask_gaussianReal_abs_mul_sqrt_div (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hμ : u ⬝ᵥ μ ≠ 0)
    (hi : i = true ↔ 0 < u ⬝ᵥ μ) :
    (halfSpaceTask ν id u).altCost μ
        (fun a ↦ |u a| * √(v a : ℝ) / ∑ b, |u b| * √(v b : ℝ)) i =
      ENNReal.ofReal ((u ⬝ᵥ μ) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2)) := by
  have hu : u ≠ 0 := fun h ↦ hμ (by simp [h])
  have hL := sum_abs_mul_sqrt_ne_zero hv hu
  have hw := abs_mul_sqrt_div_mem_simplex hv hu
  rw [altCost_halfSpaceTask_gaussianReal hv hν hμ hi (mem_simplex_iff.1 hw).1 fun a ha ↦
    (mul_sqrt_eq_zero hv).1 (abs_eq_zero.1 (by
      rw [abs_mul_sqrt]; exact (div_eq_zero_iff.1 ha).resolve_right hL))]
  congr 3
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rcases eq_or_ne (u a) 0 with h | h
  · simp [h]
  · have hva := coe_variance_pos hv a
    have hs : √(v a : ℝ) ≠ 0 := (Real.sqrt_pos.2 hva).ne'
    have : |u a| ≠ 0 := abs_ne_zero.2 h
    rw [← sq_abs (u a)]
    field_simp
    rw [Real.sq_sqrt hva.le]

/-- Every allocation of the simplex other than `|u a| √(v a) / L` has a cost of the alternatives
smaller than `(u ⬝ᵥ μ)² / (2 L²)`. -/
private lemma altCost_halfSpaceTask_gaussianReal_lt (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hμ : u ⬝ᵥ μ ≠ 0)
    (hi : i = true ↔ 0 < u ⬝ᵥ μ) (hw : w ∈ simplex α)
    (hne : w ≠ fun a ↦ |u a| * √(v a : ℝ) / ∑ b, |u b| * √(v b : ℝ)) :
    (halfSpaceTask ν id u).altCost μ w i <
      ENNReal.ofReal ((u ⬝ᵥ μ) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2)) := by
  have hu : u ≠ 0 := fun h ↦ hμ (by simp [h])
  have hL := sum_abs_mul_sqrt_ne_zero hv hu
  have hpos : 0 < (u ⬝ᵥ μ) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2) := by positivity
  by_cases h0 : ∃ a, u a ≠ 0 ∧ w a = 0
  · -- Some arm with `u a ≠ 0` is not sampled: the alternatives are free.
    obtain ⟨a, hua, hwa⟩ := h0
    rw [altCost_halfSpaceTask_gaussianReal_eq_zero hv hν hμ hi (mem_simplex_iff.1 hw).1 hua hwa]
    exact ENNReal.ofReal_pos.2 hpos
  simp only [not_exists, not_and] at h0
  have hwu (a : α) (ha : w a = 0) : u a = 0 := by
    by_contra h
    exact h0 a h ha
  rw [altCost_halfSpaceTask_gaussianReal hv hν hμ hi (mem_simplex_iff.1 hw).1 hwu,
    ENNReal.ofReal_lt_ofReal_iff hpos]
  -- The strict inequality `L² < ∑ a, u a² v a / w a`, for the vector `(u a √(v a))_a`.
  have h_lt := sq_sum_abs_lt_sum_sq_div (mul_sqrt_ne_zero hv hu) hw
    (fun a ha ↦ by simp [hwu a ha]) (by rwa [← abs_mul_sqrt_div_eq])
  have h_sq (a : α) : (u a * √(v a : ℝ)) ^ 2 = u a ^ 2 * v a := by
    rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg _)]
  simp_rw [abs_mul_sqrt, h_sq] at h_lt
  gcongr

/-- **The game value of Gaussian half-space identification** [DK19, Lemma 36]. For Gaussian arms
with variances `v a ≠ 0`, a vector of means `μ` with `u ⬝ᵥ μ ≠ 0` and its correct answer `i`,
`D(μ, ¬i) = (u ⬝ᵥ μ)² / (2 L²)`, with `L = ∑ a, |u a| √(v a)`. -/
theorem answerValue_halfSpaceTask_gaussianReal (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hμ : u ⬝ᵥ μ ≠ 0)
    (hi : i = true ↔ 0 < u ⬝ᵥ μ) :
    (halfSpaceTask ν id u).answerValue μ i =
      ENNReal.ofReal ((u ⬝ᵥ μ) ^ 2 / (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2)) := by
  rw [IdentTask.answerValue_def]
  refine le_antisymm (iSup₂_le fun w hw ↦ ?_) ?_
  · by_cases h : w = fun a ↦ |u a| * √(v a : ℝ) / ∑ b, |u b| * √(v b : ℝ)
    · rw [h, altCost_halfSpaceTask_gaussianReal_abs_mul_sqrt_div hv hν hμ hi]
    · exact (altCost_halfSpaceTask_gaussianReal_lt hv hν hμ hi hw h).le
  · rw [← altCost_halfSpaceTask_gaussianReal_abs_mul_sqrt_div hv hν hμ hi]
    exact le_iSup₂ (f := fun w (_ : w ∈ simplex α) ↦ (halfSpaceTask ν id u).altCost μ w i) _
      (abs_mul_sqrt_div_mem_simplex hv fun h ↦ hμ (by simp [h]))

/-- **The optimal allocation of Gaussian half-space identification** [DK19, Lemma 36]. Under the
assumptions of `answerValue_halfSpaceTask_gaussianReal`, the only optimal allocation is
`|u a| √(v a) / L`, with `L = ∑ a, |u a| √(v a)`. -/
theorem optAlloc_halfSpaceTask_gaussianReal (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hμ : u ⬝ᵥ μ ≠ 0)
    (hi : i = true ↔ 0 < u ⬝ᵥ μ) :
    (halfSpaceTask ν id u).optAlloc μ i =
      {fun a ↦ |u a| * √(v a : ℝ) / ∑ b, |u b| * √(v b : ℝ)} := by
  ext w
  rw [IdentTask.mem_optAlloc_iff, Set.mem_singleton_iff,
    answerValue_halfSpaceTask_gaussianReal hv hν hμ hi]
  refine ⟨fun ⟨hw, h⟩ ↦ ?_, ?_⟩
  · by_contra hne
    exact (altCost_halfSpaceTask_gaussianReal_lt hv hν hμ hi hw hne).ne h
  · rintro rfl
    exact ⟨abs_mul_sqrt_div_mem_simplex hv fun h ↦ hμ (by simp [h]),
      altCost_halfSpaceTask_gaussianReal_abs_mul_sqrt_div hv hν hμ hi⟩

/-- **The characteristic time of Gaussian half-space identification** [DK19, Lemma 36]. For
Gaussian arms with variances `v a ≠ 0` and a vector of means `μ` with `u ⬝ᵥ μ ≠ 0`,
`T*(μ) = 2 (∑ a, |u a| √(v a))² / (u ⬝ᵥ μ)²`; cf. [D23, Lemma 15], which finds `2 / (u ⬝ᵥ μ)²` for
the static-proportions difficulty under the normalization `∑ a, |u a| √(v a) = 1`. -/
theorem charTime_halfSpaceTask_gaussianReal (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hμ : u ⬝ᵥ μ ≠ 0) :
    (halfSpaceTask ν id u).charTime μ =
      ENNReal.ofReal (2 * (∑ a, |u a| * √(v a : ℝ)) ^ 2 / (u ⬝ᵥ μ) ^ 2) := by
  have hu : u ≠ 0 := fun h ↦ hμ (by simp [h])
  have hL := sum_abs_mul_sqrt_ne_zero hv hu
  rw [IdentTask.charTime_eq_inv_answerValue _ (correct_halfSpaceTask_eq_singleton _ _),
    answerValue_halfSpaceTask_gaussianReal hv hν hμ (by simp),
    ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div]

end LMLExplore.Identification
