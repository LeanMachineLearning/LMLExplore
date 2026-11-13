/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.Task.Classical
public import LMLExplore.Identification.Task.TransportationCost
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Transductive best-answer identification

In a linear model, the models are the vectors `θ` of a real inner product space `E`, and the arm
`a` of `θ` typically has mean `⟪φ a, θ⟫` for features `φ : α → E`. Linear best arm
identification, thresholding and the other classical tasks are those of
`LMLExplore.Identification.Task.Classical` for the mean functional `θ ↦ (⟪φ a, θ⟫)_a`. The
transductive task of Fiez, Jain, Jamieson and Ratliff (2019) asks a different question: given a
family `z : ι → E` of answers, which is not required to be the family of features, find the
answer `z i` with the largest value `⟪z i, θ⟫`. The admissible models are those with a unique
best answer. Best arm identification in the linear model is the case `ι = α`, `z = φ`
(`transductiveTask_eq_baiTask`), and a finite set `𝒵 ⊆ E` of answers is the family
`(↑) : 𝒵 → E`.

The alternatives to the answer `i` are the models with a unique best answer `j ≠ i`. For
finitely many distinct answers, the closure of this set is the union of the half-spaces
`{λ | ⟪z i - z j, λ⟫ ≤ 0}`, `j ≠ i`, so that the cost of the alternatives
`D(θ, w, ¬i) = inf_{λ ∈ ¬i} cost_θ(w, λ)` is, for a transportation cost continuous in the
alternative, the smallest cost of these half-spaces. These are the half-spaces whose costs give
the characteristic time of linear identification with Gaussian noise
`T*(θ)⁻¹ = max_w min_{z ≠ z*} ⟪z* - z, θ⟫² / (2 ‖z* - z‖²_{V_w⁻¹})` [FJJR19, Theorem 1].

## Main definitions

* `LMLExplore.Identification.transductiveTask ν z`: the transductive best-answer task with bandits
  `ν θ` and answers `z i`.

## Main statements

* `LMLExplore.Identification.isSingleAnswer_transductiveTask`: the task has a single correct answer
  on every admissible model, and `correct_transductiveTask_eq_singleton_iff` characterizes it.
* `LMLExplore.Identification.transductiveTask_eq_baiTask`: with the features as answers, the task is
  best arm identification for the mean functional `θ ↦ (⟪φ a, θ⟫)_a`.
* `LMLExplore.Identification.mem_alt_transductiveTask_iff`,
  `LMLExplore.Identification.mem_answerSet_transductiveTask_iff`: the alternatives to `i` are the
  models with a unique best answer `j ≠ i`, and the models for which `i` is correct are those with
  unique best answer `i`.
* `LMLExplore.Identification.isOpen_answerSet_transductiveTask`: for finitely many answers, the
  models with unique best answer `i` form an open set.
* `LMLExplore.Identification.closure_alt_transductiveTask`: for finitely many distinct answers, the
  closure of the alternatives to `i` is the union of the half-spaces `{λ | ⟪z i - z j, λ⟫ ≤ 0}`,
  `j ≠ i`.
* `LMLExplore.Identification.altCost_transductiveTask_eq_iInf`: for a transportation cost continuous
  on these half-spaces, `D(θ, w, ¬i)` is the infimum over `j ≠ i` of the smallest cost of the
  half-space `{λ | ⟪z i - z j, λ⟫ ≤ 0}`.
* `LMLExplore.Identification.charTime_transductiveTask_eq_inv_answerValue`: if `i` is the unique
  best answer of `θ`, then `T*(θ) = D(θ, ¬i)⁻¹`.

## References

* [FJJR19] T. Fiez, L. Jain, K. Jamieson and L. Ratliff, *Sequential experimental design for
  transductive linear bandits*, NeurIPS 2019, Section 2 and Theorem 1.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology

open scoped InnerProductSpace ENNReal

namespace LMLExplore.Identification

variable {α ι E 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ν : E → Kernel α 𝓨) [∀ θ, IsMarkovKernel (ν θ)] (z : ι → E) {θ : E} {i : ι}

/-- The *transductive best-answer task* [FJJR19] on the models `θ` of a real inner product space
`E`, with bandits `ν θ` and the family `z : ι → E` of answers: the correct answer of `θ` is the
answer `i` with the largest value `⟪z i, θ⟫`, and the admissible models are those with a unique
best answer. Linear best arm identification is the case of the features as answers
(`transductiveTask_eq_baiTask`). -/
noncomputable def transductiveTask : IdentTask α E ι 𝓨 where
  M := {θ | ∃ i, ∀ j ≠ i, ⟪z j, θ⟫_ℝ < ⟪z i, θ⟫_ℝ}
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct θ := {i | ∀ j ≠ i, ⟪z j, θ⟫_ℝ < ⟪z i, θ⟫_ℝ}

@[simp]
lemma M_transductiveTask :
    (transductiveTask ν z).M = {θ | ∃ i, ∀ j ≠ i, ⟪z j, θ⟫_ℝ < ⟪z i, θ⟫_ℝ} := (rfl)

@[simp]
lemma ν_transductiveTask : (transductiveTask ν z).ν = ν := (rfl)

@[simp]
lemma correct_transductiveTask (θ : E) :
    (transductiveTask ν z).correct θ = {i | ∀ j ≠ i, ⟪z j, θ⟫_ℝ < ⟪z i, θ⟫_ℝ} := (rfl)

/-- With the features `φ` as answers, the transductive task is best arm identification for the
mean functional `θ ↦ (⟪φ a, θ⟫)_a` of the linear model. -/
lemma transductiveTask_eq_baiTask (φ : α → E) :
    transductiveTask ν φ = baiTask ν (fun θ a ↦ ⟪φ a, θ⟫_ℝ) := by
  ext <;> simp

/-- A model has at most one best answer. -/
lemma subsingleton_correct_transductiveTask (θ : E) :
    ((transductiveTask ν z).correct θ).Subsingleton := by
  intro i hi i' hi'
  by_contra h
  simp only [correct_transductiveTask, Set.mem_ofPred_eq] at hi hi'
  exact lt_asymm (hi i' (Ne.symm h)) (hi' i h)

/-- The answer `i` is the only best answer of `θ` iff every other answer `j` has
`⟪z j, θ⟫ < ⟪z i, θ⟫`. -/
lemma correct_transductiveTask_eq_singleton_iff :
    (transductiveTask ν z).correct θ = {i} ↔ ∀ j ≠ i, ⟪z j, θ⟫_ℝ < ⟪z i, θ⟫_ℝ :=
  ⟨fun h ↦ by simpa using h.symm.subset (Set.mem_singleton i),
    fun h ↦ (subsingleton_correct_transductiveTask ν z θ).eq_singleton_of_mem h⟩

/-- The transductive task is a single-answer task: every model with a unique best answer has
exactly one correct answer, its best answer. -/
lemma isSingleAnswer_transductiveTask : (transductiveTask ν z).IsSingleAnswer := by
  refine (IdentTask.isSingleAnswer_iff _).2 ?_
  rintro θ ⟨i, hi⟩
  exact ⟨i, (correct_transductiveTask_eq_singleton_iff ν z).2 hi⟩

/-- The alternatives to the answer `i` in the transductive task are the models with a unique best
answer `j ≠ i`. -/
lemma mem_alt_transductiveTask_iff :
    θ ∈ (transductiveTask ν z).alt i ↔ ∃ j ≠ i, ∀ k ≠ j, ⟪z k, θ⟫_ℝ < ⟪z j, θ⟫_ℝ := by
  simp only [IdentTask.mem_alt_iff, M_transductiveTask, correct_transductiveTask,
    Set.mem_ofPred_eq, not_forall, not_lt, exists_prop]
  constructor
  · rintro ⟨⟨j, hj⟩, k, hki, hk⟩
    refine ⟨j, ?_, hj⟩
    rintro rfl
    exact (hj k hki).not_ge hk
  · rintro ⟨j, hji, hj⟩
    exact ⟨⟨j, hj⟩, j, hji, (hj i hji.symm).le⟩

/-- The models for which the answer `i` is correct in the transductive task are those with unique
best answer `i`. -/
lemma mem_answerSet_transductiveTask_iff :
    θ ∈ (transductiveTask ν z).answerSet i ↔ ∀ j ≠ i, ⟪z j, θ⟫_ℝ < ⟪z i, θ⟫_ℝ := by
  rw [IdentTask.mem_answerSet_iff, M_transductiveTask, correct_transductiveTask]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨i, h⟩, h⟩⟩

/-- For finitely many answers, the models with unique best answer `i` form an open set. -/
lemma isOpen_answerSet_transductiveTask [Finite ι] (i : ι) :
    IsOpen ((transductiveTask ν z).answerSet i) := by
  have h : (transductiveTask ν z).answerSet i =
      ⋂ j ∈ ({i}ᶜ : Set ι), {θ | ⟪z j, θ⟫_ℝ < ⟪z i, θ⟫_ℝ} := by
    ext θ
    rw [mem_answerSet_transductiveTask_iff]
    simp
  rw [h]
  exact (Set.toFinite _).isOpen_biInter fun j _ ↦
    isOpen_lt (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)

/-! ### The closure of the alternatives -/

/-- If the answers are distinct and some answer `j ≠ i` has `⟪z i, θ'⟫ ≤ ⟪z j, θ'⟫`, then `θ'` is
a limit of models with a unique best answer different from `i`. -/
lemma mem_closure_alt_transductiveTask [Finite ι] (hz : Function.Injective z) {θ' : E}
    (h : ∃ j ≠ i, ⟪z i, θ'⟫_ℝ ≤ ⟪z j, θ'⟫_ℝ) :
    θ' ∈ closure ((transductiveTask ν z).alt i) := by
  -- The answers `k ≠ i` with the largest value at `θ'`.
  set A : Set ι := {k | k ≠ i ∧ ∀ l, ⟪z l, θ'⟫_ℝ ≤ ⟪z k, θ'⟫_ℝ}
  have hA : A.Nonempty := by
    obtain ⟨j, hji, hj⟩ := h
    have : Nonempty ι := ⟨i⟩
    obtain ⟨k, hk⟩ := Finite.exists_max fun k ↦ ⟪z k, θ'⟫_ℝ
    by_cases hki : k = i
    · exact ⟨j, hji, fun l ↦ (hk l).trans (hki ▸ hj)⟩
    · exact ⟨k, hki, hk⟩
  -- Among them, the answer `j` farthest from `z i`, and the direction `d = z j - z i`: moving
  -- `θ'` along `d` makes `j` the unique best answer.
  obtain ⟨j, ⟨hji, hj⟩, hj_far⟩ := Set.exists_max_image A (fun k ↦ ‖z k - z i‖) A.toFinite hA
  set d := z j - z i
  have h_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k ≠ j, ⟪z k, θ' + t • d⟫_ℝ < ⟪z j, θ' + t • d⟫_ℝ := by
    refine eventually_all.2 fun k ↦ ?_
    by_cases hkj : k = j
    · exact Eventually.of_forall fun _ h ↦ absurd hkj h
    -- The gap `⟪z j - z k, θ' + t • d⟫` is affine in `t`, nonnegative at `t = 0`.
    suffices ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ⟪z j - z k, θ'⟫_ℝ + t * ⟪z j - z k, d⟫_ℝ by
      filter_upwards [this] with t ht _
      simp only [inner_add_right, inner_smul_right, inner_sub_left] at ht ⊢
      linarith
    rcases (sub_nonneg.2 (hj k)).eq_or_lt with h0 | h0
    · -- If `k` ties with `j` at `θ'`, the slope `⟪z j - z k, d⟫` is positive, since
      -- `‖z k - z i‖ ≤ ‖d‖` by the choice of `j` and `z k ≠ z j`.
      have h_le : ‖z k - z i‖ ≤ ‖d‖ := by
        by_cases hki : k = i
        · simp [hki]
        · exact hj_far k ⟨hki, fun l ↦ (hj l).trans (by linarith)⟩
      have h_ne : 0 < ‖d - (z k - z i)‖ := by
        rw [norm_pos_iff, sub_sub_sub_cancel_right, sub_ne_zero]
        exact hz.ne (Ne.symm hkj)
      have h_slope : 0 < ⟪z j - z k, d⟫_ℝ := by
        rw [← sub_sub_sub_cancel_right (z j) (z k) (z i), inner_sub_left,
          real_inner_self_eq_norm_sq, real_inner_comm]
        nlinarith [norm_sub_sq_real d (z k - z i), norm_nonneg (z k - z i), norm_nonneg d]
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [inner_sub_left, ← h0, zero_add]
      exact mul_pos ht h_slope
    · -- Otherwise the gap is positive at `t = 0`, hence for small `t`.
      rw [← inner_sub_left] at h0
      refine nhdsWithin_le_nhds ?_
      exact continuousAt_const.eventually_lt (by fun_prop) (by simpa using h0)
  have h_tendsto : Tendsto (fun t : ℝ ↦ θ' + t • d) (𝓝[>] 0) (𝓝 θ') := by
    have hc : Continuous fun t : ℝ ↦ θ' + t • d := by fun_prop
    simpa using hc.continuousWithinAt.tendsto (x := 0) (s := Set.Ioi 0)
  refine mem_closure_of_tendsto h_tendsto ?_
  filter_upwards [h_ev] with t ht
  exact (mem_alt_transductiveTask_iff ν z).2 ⟨j, hji, ht⟩

/-- For finitely many distinct answers, the closure of the alternatives to the answer `i` in the
transductive task is the union of the half-spaces `{λ | ⟪z i - z j, λ⟫ ≤ 0}`, `j ≠ i`: the models
in which some answer `j ≠ i` scores at least as much as `i`. -/
theorem closure_alt_transductiveTask [Finite ι] (hz : Function.Injective z) (i : ι) :
    closure ((transductiveTask ν z).alt i) =
      ⋃ j : {j // j ≠ i}, {θ' | ⟪z i - z j, θ'⟫_ℝ ≤ 0} := by
  refine Set.Subset.antisymm (closure_minimal (fun θ' hθ' ↦ ?_) ?_) fun θ' hθ' ↦ ?_
  · obtain ⟨j, hji, hj⟩ := (mem_alt_transductiveTask_iff ν z).1 hθ'
    refine Set.mem_iUnion.2 ⟨⟨j, hji⟩, ?_⟩
    rw [Set.mem_ofPred_eq, inner_sub_left, sub_nonpos]
    exact (hj i hji.symm).le
  · exact isClosed_iUnion_of_finite fun j ↦
      isClosed_le (continuous_const.inner continuous_id) continuous_const
  · obtain ⟨⟨j, hji⟩, hj⟩ := Set.mem_iUnion.1 hθ'
    rw [Set.mem_ofPred_eq, inner_sub_left, sub_nonpos] at hj
    exact mem_closure_alt_transductiveTask ν z hz ⟨j, hji, hj⟩

/-- For finitely many distinct answers and a transportation cost from `θ` continuous on the
half-spaces `{λ | ⟪z i - z j, λ⟫ ≤ 0}`, `j ≠ i`, the cost of the alternatives to `i` is the
smallest cost of these half-spaces,
`D(θ, w, ¬i) = min_{j ≠ i} inf {cost_θ(w, λ) | ⟪z i - z j, λ⟫ ≤ 0}` [FJJR19, Theorem 1]. -/
theorem altCost_transductiveTask_eq_iInf [Fintype α] [Finite ι] (hz : Function.Injective z)
    {w : α → ℝ} (hc : ContinuousOn ((transductiveTask ν z).cost w θ)
      (⋃ j : {j // j ≠ i}, {θ' | ⟪z i - z j, θ'⟫_ℝ ≤ 0})) :
    (transductiveTask ν z).altCost θ w i =
      ⨅ (j : {j // j ≠ i}) (θ' ∈ {θ' | ⟪z i - z j, θ'⟫_ℝ ≤ 0}),
        (transductiveTask ν z).cost w θ θ' := by
  have h_eq := closure_alt_transductiveTask ν z hz i
  rw [IdentTask.altCost_eq_biInf_of_subset_closure _ (h_eq ▸ subset_closure) h_eq.ge hc,
    iInf_iUnion]

/-- If `i` is the unique best answer of `θ`, then `T*(θ) = D(θ, ¬i)⁻¹` in the transductive task. -/
theorem charTime_transductiveTask_eq_inv_answerValue [Fintype α]
    (hi : ∀ j ≠ i, ⟪z j, θ⟫_ℝ < ⟪z i, θ⟫_ℝ) :
    (transductiveTask ν z).charTime θ = ((transductiveTask ν z).answerValue θ i)⁻¹ :=
  IdentTask.charTime_eq_inv_answerValue _ ((correct_transductiveTask_eq_singleton_iff ν z).2 hi)

end LMLExplore.Identification
