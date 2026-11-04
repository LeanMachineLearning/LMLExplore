/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.ExpFamily
public import LMLExplore.Identification.Task.MeanVector

/-!
# The pure exploration game of half-space identification with Gaussian arms

In half-space identification (`halfSpaceTask ν u`) the correct answer of a vector of means `μ` is
the sign of `u ⬝ᵥ μ`, and the alternatives to it are the vectors of means `λ` with `u ⬝ᵥ λ` of the
other sign. For Gaussian arms with a common variance `σ2`, the transportation cost
`∑ a, w a (μ a - λ a)² / (2 σ2)` is a weighted squared distance, and the game has a closed form
[DK19, Lemma 36]. Write `‖u‖₁ = ∑ a, |u a|`.

* For a nonnegative allocation `w` that is positive on the arms with `u a ≠ 0`, the cost of the
  alternatives is the squared distance from `μ` to the hyperplane `u ⬝ᵥ λ = 0` in the norm of `w`,
  `D(μ, w, ¬i) = (u ⬝ᵥ μ)² / (2 σ2 ∑ a, u a² / w a)`: by the Cauchy–Schwarz inequality, moving `μ`
  across the hyperplane costs at least this much, and moving it along the direction
  `u a / w a` costs arbitrarily little more. If instead `w a = 0` for some arm with `u a ≠ 0`,
  the mean of that arm can be moved for free and `D(μ, w, ¬i) = 0`.
* By the identity `∑ a, (|u a| - ‖u‖₁ w a)² / w a = ∑ a, u a² / w a - ‖u‖₁²`
  (`LMLExplore.sum_sq_abs_sub_mul_div_eq`), `(∑ a, u a² / w a) ≥ ‖u‖₁²` on the allocations of the
  simplex that are positive where `u a ≠ 0`, with equality, for `u ≠ 0`, exactly at
  `w a = |u a| / ‖u‖₁`; the other allocations have `D(μ, w, ¬i) = 0` by the previous point. Hence
  `D(μ, ¬i) = (u ⬝ᵥ μ)² / (2 σ2 ‖u‖₁²)`, the only optimal allocation is `|u| / ‖u‖₁`, and
  `T*(μ) = 2 σ2 ‖u‖₁² / (u ⬝ᵥ μ)²`.

These values are the divergences of [DK19, Lemma 36], stated there for the hyperplane, which is
the boundary of the set of alternatives.

## Main statements

* `LMLExplore.Identification.mem_alt_halfSpaceTask_iff`: the alternatives of half-space
  identification.
* `LMLExplore.Identification.altCost_halfSpaceTask_gaussianBandit`,
  `LMLExplore.Identification.altCost_halfSpaceTask_gaussianBandit_eq_zero`: the cost of the
  alternatives for every nonnegative allocation.
* `LMLExplore.Identification.answerValue_halfSpaceTask_gaussianBandit`,
  `LMLExplore.Identification.optAlloc_halfSpaceTask_gaussianBandit`,
  `LMLExplore.Identification.charTime_halfSpaceTask_gaussianBandit`: the value of the game, the
  unique optimal allocation and the characteristic time [DK19, Lemma 36].

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, supplementary material, Appendix H, Lemma 36.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} [Fintype α]
  {u μ w : α → ℝ} {i : Bool}

/-- The alternatives to the answer `i` in half-space identification are the vectors `μ'` with
`u ⬝ᵥ μ' ≠ 0` whose sign is not the one `i` prescribes. -/
lemma mem_alt_halfSpaceTask_iff (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)]
    {μ' : α → ℝ} :
    μ' ∈ (halfSpaceTask ν u).alt i ↔ u ⬝ᵥ μ' ≠ 0 ∧ ¬ (i = true ↔ 0 < u ⬝ᵥ μ') := by
  simp only [IdentTask.mem_alt_iff, M_halfSpaceTask, correct_halfSpaceTask, Set.mem_ofPred_eq]

/-! ### Gaussian arms -/

variable [MeasurableSingletonClass α] {σ2 : ℝ≥0}

/-- **Moving across the hyperplane along a direction.** For a direction `v` with `u ⬝ᵥ v = 1`, the
vectors `μ - t (u ⬝ᵥ μ) v` with `t > 1` are alternatives, which bounds the cost of the alternatives
by `(u ⬝ᵥ μ)² (∑ a, w a v a²) / (2 σ2)` in the limit `t → 1`. -/
private lemma altCost_halfSpaceTask_gaussianBandit_le (hσ2 : σ2 ≠ 0) (hμ : u ⬝ᵥ μ ≠ 0)
    (hi : i = true ↔ 0 < u ⬝ᵥ μ) (hw : 0 ≤ w) {v : α → ℝ} (hv : u ⬝ᵥ v = 1) :
    (halfSpaceTask (Bandits.gaussianBandit · σ2) u).altCost μ w i ≤
      ENNReal.ofReal ((u ⬝ᵥ μ) ^ 2 * (∑ a, w a * v a ^ 2) / (2 * σ2)) := by
  set C := (u ⬝ᵥ μ) ^ 2 * (∑ a, w a * v a ^ 2) / (2 * σ2)
  have key (t : ℝ) (ht : 1 < t) :
      (halfSpaceTask (Bandits.gaussianBandit · σ2) u).altCost μ w i ≤
        ENNReal.ofReal (t ^ 2 * C) := by
    have h_dot : u ⬝ᵥ (μ - (t * u ⬝ᵥ μ) • v) = (1 - t) * u ⬝ᵥ μ := by
      rw [dotProduct_sub, dotProduct_smul, hv, smul_eq_mul]
      ring
    have hmem : μ - (t * u ⬝ᵥ μ) • v ∈ (halfSpaceTask (Bandits.gaussianBandit · σ2) u).alt i := by
      rw [mem_alt_halfSpaceTask_iff, h_dot, hi]
      refine ⟨mul_ne_zero (by linarith) hμ, ?_⟩
      rcases hμ.lt_or_gt with h | h
      · have : 0 < (1 - t) * u ⬝ᵥ μ := mul_pos_of_neg_of_neg (by linarith) h
        simp [this, h.not_gt]
      · have : (1 - t) * u ⬝ᵥ μ < 0 := mul_neg_of_neg_of_pos (by linarith) h
        simp [h, this.not_gt]
    refine (IdentTask.altCost_le_cost _ hmem w).trans_eq ?_
    rw [IdentTask.cost_gaussianBandit (ν_halfSpaceTask _) hσ2 hw]
    congr 1
    simp only [C, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_sub_cancel, Finset.mul_sum,
      Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  have hlim : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (t ^ 2 * C)) (𝓝[>] 1)
      (𝓝 (ENNReal.ofReal C)) := by
    have hc : Continuous fun t : ℝ ↦ ENNReal.ofReal (t ^ 2 * C) :=
      ENNReal.continuous_ofReal.comp ((continuous_pow 2).mul continuous_const)
    simpa using hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (1 : ℝ)))
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)

/-- **Crossing the hyperplane costs at least the squared distance to it.** For a nonnegative
allocation `w` that is positive where `u` does not vanish, the transportation cost from `μ` to an
alternative is at least `(u ⬝ᵥ μ)² / (2 σ2 ∑ a, u a² / w a)`, by the Cauchy–Schwarz inequality
`(u ⬝ᵥ (μ - μ'))² ≤ (∑ a, u a² / w a) ∑ a, w a (μ a - μ' a)²`. -/
private lemma le_cost_halfSpaceTask_gaussianBandit (hσ2 : σ2 ≠ 0)
    (hi : i = true ↔ 0 < u ⬝ᵥ μ) (hw : 0 ≤ w) (hwu : ∀ a, w a = 0 → u a = 0) {μ' : α → ℝ}
    (hμ' : μ' ∈ (halfSpaceTask (Bandits.gaussianBandit · σ2) u).alt i) :
    ENNReal.ofReal ((u ⬝ᵥ μ) ^ 2 / (2 * σ2 * ∑ a, u a ^ 2 / w a)) ≤
      (halfSpaceTask (Bandits.gaussianBandit · σ2) u).cost w μ μ' := by
  rw [IdentTask.cost_gaussianBandit (ν_halfSpaceTask _) hσ2 hw, ← Finset.sum_div]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mem_alt_halfSpaceTask_iff, hi] at hμ'
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
  have h2 : (u ⬝ᵥ (μ - μ')) ^ 2 ≤
      (∑ a, u a ^ 2 / w a) * ∑ a, w a * (μ a - μ' a) ^ 2 := by
    rw [dotProduct]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun a _ ↦ div_nonneg (sq_nonneg _) (hw a)) (fun a _ ↦ mul_nonneg (hw a) (sq_nonneg _))
      fun a _ ↦ ?_
    rcases eq_or_ne (w a) 0 with h | h
    · simp [h, hwu a h]
    · refine le_of_eq ?_
      simp only [Pi.sub_apply]
      field_simp
  rw [mul_comm (2 * (σ2 : ℝ)), ← div_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact div_le_of_le_mul₀ (Finset.sum_nonneg fun a _ ↦ div_nonneg (sq_nonneg _) (hw a))
    (Finset.sum_nonneg fun a _ ↦ mul_nonneg (hw a) (sq_nonneg _)) (by linarith)

/-- **The cost of the alternatives in Gaussian half-space identification.** For Gaussian arms with
a common variance `σ2 ≠ 0`, a vector of means `μ` with `u ⬝ᵥ μ ≠ 0`, its correct answer `i` and a
nonnegative allocation `w` that is positive on the arms with `u a ≠ 0`,
`D(μ, w, ¬i) = (u ⬝ᵥ μ)² / (2 σ2 ∑ a, u a² / w a)`: the squared distance from `μ` to the
hyperplane `u ⬝ᵥ λ = 0` in the norm of `w`. -/
theorem altCost_halfSpaceTask_gaussianBandit (hσ2 : σ2 ≠ 0) (hμ : u ⬝ᵥ μ ≠ 0)
    (hi : i = true ↔ 0 < u ⬝ᵥ μ) (hw : 0 ≤ w) (hwu : ∀ a, w a = 0 → u a = 0) :
    (halfSpaceTask (Bandits.gaussianBandit · σ2) u).altCost μ w i =
      ENNReal.ofReal ((u ⬝ᵥ μ) ^ 2 / (2 * σ2 * ∑ a, u a ^ 2 / w a)) := by
  refine le_antisymm ?_ ?_
  swap
  · rw [IdentTask.altCost_def]
    exact le_iInf₂ fun μ' hμ' ↦ le_cost_halfSpaceTask_gaussianBandit hσ2 hi hw hwu hμ'
  set V := ∑ a, u a ^ 2 / w a with hV
  have hV0 : V ≠ 0 := by
    intro h
    have hu (a : α) : u a = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun a _ ↦ div_nonneg (sq_nonneg (u a)) (hw a)).1
        h a (Finset.mem_univ a)
      rcases div_eq_zero_iff.1 this with h | h
      · exact pow_eq_zero_iff two_ne_zero |>.1 h
      · exact hwu a h
    exact hμ (by simp [dotProduct, hu])
  -- Move `μ` along the direction `u a / (w a V)`, which satisfies `u ⬝ᵥ v = 1`.
  have hv : u ⬝ᵥ (fun a ↦ u a / (w a * V)) = 1 := by
    rw [dotProduct, ← div_self hV0, hV, Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  refine (altCost_halfSpaceTask_gaussianBandit_le hσ2 hμ hi hw hv).trans_eq
    (congrArg ENNReal.ofReal ?_)
  have h_sum : ∑ a, w a * (u a / (w a * V)) ^ 2 = 1 / V := by
    rw [← div_self hV0, hV, div_div, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rcases eq_or_ne (w a) 0 with h | h
    · simp [h]
    · field_simp
  rw [h_sum]
  field_simp

/-- **Free alternatives in Gaussian half-space identification.** If an allocation `w ≥ 0` does not
sample an arm `a` with `u a ≠ 0`, the mean of `a` can be moved across the hyperplane at no cost,
and `D(μ, w, ¬i) = 0`. -/
theorem altCost_halfSpaceTask_gaussianBandit_eq_zero (hσ2 : σ2 ≠ 0) (hμ : u ⬝ᵥ μ ≠ 0)
    (hi : i = true ↔ 0 < u ⬝ᵥ μ) (hw : 0 ≤ w) {a : α} (hua : u a ≠ 0) (hwa : w a = 0) :
    (halfSpaceTask (Bandits.gaussianBandit · σ2) u).altCost μ w i = 0 := by
  classical
  have hv : u ⬝ᵥ Pi.single a (u a)⁻¹ = 1 := by
    rw [dotProduct_single, mul_inv_cancel₀ hua]
  refine le_antisymm ((altCost_halfSpaceTask_gaussianBandit_le hσ2 hμ hi hw hv).trans_eq ?_)
    bot_le
  have h_sum : ∑ b, w b * Pi.single (M := fun _ ↦ ℝ) a (u a)⁻¹ b ^ 2 = 0 :=
    Finset.sum_eq_zero fun b _ ↦ by
      rcases eq_or_ne b a with rfl | h
      · simp [hwa]
      · simp [h]
  simp [h_sum]

/-- At the allocation `|u| / ‖u‖₁`, the cost of the alternatives is
`(u ⬝ᵥ μ)² / (2 σ2 ‖u‖₁²)`. -/
private lemma altCost_halfSpaceTask_gaussianBandit_abs_div (hσ2 : σ2 ≠ 0) (hμ : u ⬝ᵥ μ ≠ 0)
    (hi : i = true ↔ 0 < u ⬝ᵥ μ) :
    (halfSpaceTask (Bandits.gaussianBandit · σ2) u).altCost μ (fun a ↦ |u a| / ∑ b, |u b|) i =
      ENNReal.ofReal ((u ⬝ᵥ μ) ^ 2 / (2 * σ2 * (∑ a, |u a|) ^ 2)) := by
  have hu : u ≠ 0 := fun h ↦ hμ (by simp [h])
  have hL := sum_abs_ne_zero hu
  have hw := abs_div_sum_abs_mem_simplex hu
  rw [altCost_halfSpaceTask_gaussianBandit hσ2 hμ hi (mem_simplex_iff.1 hw).1 fun a ha ↦
    abs_eq_zero.1 ((div_eq_zero_iff.1 ha).resolve_right hL)]
  congr 3
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rcases eq_or_ne (u a) 0 with h | h
  · simp [h]
  · rw [← sq_abs]
    have : |u a| ≠ 0 := abs_ne_zero.2 h
    field_simp

/-- Every allocation of the simplex other than `|u| / ‖u‖₁` has a cost of the alternatives
smaller than `(u ⬝ᵥ μ)² / (2 σ2 ‖u‖₁²)`. -/
private lemma altCost_halfSpaceTask_gaussianBandit_lt (hσ2 : σ2 ≠ 0) (hμ : u ⬝ᵥ μ ≠ 0)
    (hi : i = true ↔ 0 < u ⬝ᵥ μ) (hw : w ∈ simplex α)
    (hne : w ≠ fun a ↦ |u a| / ∑ b, |u b|) :
    (halfSpaceTask (Bandits.gaussianBandit · σ2) u).altCost μ w i <
      ENNReal.ofReal ((u ⬝ᵥ μ) ^ 2 / (2 * σ2 * (∑ a, |u a|) ^ 2)) := by
  have hu : u ≠ 0 := fun h ↦ hμ (by simp [h])
  have hL := sum_abs_ne_zero hu
  have hσ2' : (0 : ℝ) < σ2 := by positivity
  have hpos : 0 < (u ⬝ᵥ μ) ^ 2 / (2 * σ2 * (∑ a, |u a|) ^ 2) := by positivity
  by_cases h0 : ∃ a, u a ≠ 0 ∧ w a = 0
  · -- Some arm with `u a ≠ 0` is not sampled: the alternatives are free.
    obtain ⟨a, hua, hwa⟩ := h0
    rw [altCost_halfSpaceTask_gaussianBandit_eq_zero hσ2 hμ hi (mem_simplex_iff.1 hw).1 hua hwa]
    exact ENNReal.ofReal_pos.2 hpos
  simp only [not_exists, not_and] at h0
  have hwu (a : α) (ha : w a = 0) : u a = 0 := by
    by_contra h
    exact h0 a h ha
  rw [altCost_halfSpaceTask_gaussianBandit hσ2 hμ hi (mem_simplex_iff.1 hw).1 hwu,
    ENNReal.ofReal_lt_ofReal_iff hpos]
  have h_lt := sq_sum_abs_lt_sum_sq_div hu hw hwu hne
  gcongr

/-- **The game value of Gaussian half-space identification** [DK19, Lemma 36]. For Gaussian arms
with a common variance `σ2 ≠ 0`, a vector of means `μ` with `u ⬝ᵥ μ ≠ 0` and its correct answer
`i`, `D(μ, ¬i) = (u ⬝ᵥ μ)² / (2 σ2 ‖u‖₁²)`. -/
theorem answerValue_halfSpaceTask_gaussianBandit (hσ2 : σ2 ≠ 0) (hμ : u ⬝ᵥ μ ≠ 0)
    (hi : i = true ↔ 0 < u ⬝ᵥ μ) :
    (halfSpaceTask (Bandits.gaussianBandit · σ2) u).answerValue μ i =
      ENNReal.ofReal ((u ⬝ᵥ μ) ^ 2 / (2 * σ2 * (∑ a, |u a|) ^ 2)) := by
  rw [IdentTask.answerValue_def]
  refine le_antisymm (iSup₂_le fun w hw ↦ ?_) ?_
  · by_cases h : w = fun a ↦ |u a| / ∑ b, |u b|
    · rw [h, altCost_halfSpaceTask_gaussianBandit_abs_div hσ2 hμ hi]
    · exact (altCost_halfSpaceTask_gaussianBandit_lt hσ2 hμ hi hw h).le
  · rw [← altCost_halfSpaceTask_gaussianBandit_abs_div hσ2 hμ hi]
    exact le_iSup₂ (f := fun w (_ : w ∈ simplex α) ↦
      (halfSpaceTask (Bandits.gaussianBandit · σ2) u).altCost μ w i) _
      (abs_div_sum_abs_mem_simplex (fun h ↦ hμ (by simp [h])))

/-- **The optimal allocation of Gaussian half-space identification** [DK19, Lemma 36]. Under the
assumptions of `answerValue_halfSpaceTask_gaussianBandit`, the only optimal allocation is
`|u| / ‖u‖₁`. -/
theorem optAlloc_halfSpaceTask_gaussianBandit (hσ2 : σ2 ≠ 0) (hμ : u ⬝ᵥ μ ≠ 0)
    (hi : i = true ↔ 0 < u ⬝ᵥ μ) :
    (halfSpaceTask (Bandits.gaussianBandit · σ2) u).optAlloc μ i =
      {fun a ↦ |u a| / ∑ b, |u b|} := by
  ext w
  rw [IdentTask.mem_optAlloc_iff, Set.mem_singleton_iff,
    answerValue_halfSpaceTask_gaussianBandit hσ2 hμ hi]
  refine ⟨fun ⟨hw, h⟩ ↦ ?_, ?_⟩
  · by_contra hne
    exact (altCost_halfSpaceTask_gaussianBandit_lt hσ2 hμ hi hw hne).ne h
  · rintro rfl
    exact ⟨abs_div_sum_abs_mem_simplex (fun h ↦ hμ (by simp [h])),
      altCost_halfSpaceTask_gaussianBandit_abs_div hσ2 hμ hi⟩

/-- **The characteristic time of Gaussian half-space identification** [DK19, Lemma 36]. For
Gaussian arms with a common variance `σ2 ≠ 0` and a vector of means `μ` with `u ⬝ᵥ μ ≠ 0`,
`T*(μ) = 2 σ2 ‖u‖₁² / (u ⬝ᵥ μ)²`. -/
theorem charTime_halfSpaceTask_gaussianBandit (hσ2 : σ2 ≠ 0) (hμ : u ⬝ᵥ μ ≠ 0) :
    (halfSpaceTask (Bandits.gaussianBandit · σ2) u).charTime μ =
      ENNReal.ofReal (2 * σ2 * (∑ a, |u a|) ^ 2 / (u ⬝ᵥ μ) ^ 2) := by
  have hL := sum_abs_ne_zero (u := u) fun h ↦ hμ (by simp [h])
  have hσ2' : (0 : ℝ) < σ2 := by positivity
  rw [IdentTask.charTime_eq_inv_answerValue _ (correct_halfSpaceTask_eq_singleton _),
    answerValue_halfSpaceTask_gaussianBandit hσ2 hμ (by simp),
    ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div]

end LMLExplore.Identification
