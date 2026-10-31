/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# Classical identification tasks on vectors of means

The classical identification tasks whose models are vectors of means `μ : α → ℝ`, one per arm.
Each task takes the bandit `ν μ : Kernel α 𝓨` of each mean vector as a parameter (typically arm
`a` of `ν μ` has mean `μ a`, for example `ν μ = gaussianBandit μ σ2`), and constrains the
admissible models only through the question asked. Admissible models whose means lie in given
sets (the means of an exponential family, `[0, 1]` for Bernoulli arms, ...) are obtained with
`IdentTask.restrict`.

* `baiTask ν`: best arm identification. The answer is the arm with the largest mean, on the models
  with a unique best arm.
* `topMTask ν m`: top-`m` identification. The answer is the set of the `m` arms with the largest
  means, on the models where it is unique.
* `epsBaiTask ν ε`: `ε`-best arm identification. The correct answers are the arms whose mean is
  within `ε` of the largest mean, on every model. Several answers may be correct.
* `thresholdingTask ν γ`: the answer is the set of arms with mean above `γ`, on the models with no
  mean equal to `γ`.
* `minThresholdTask ν γ`: the answer is whether the smallest mean is below `γ`, on the models
  whose smallest mean is not `γ`.
* `anyLowArmTask ν γ`: *Any Low Arm* [DK19, Example 1]. The correct answers are the arms with
  mean below `γ` (`some a`), or "none" (`none`) if all means are above `γ`, on the models where
  one of these holds. Several answers may be correct.
* `halfSpaceTask ν u`: the answer is the sign of `u ⬝ᵥ μ`, on the models with `u ⬝ᵥ μ ≠ 0`.

## Main statements

* `isSingleAnswer_baiTask`, `isSingleAnswer_topMTask`, `isSingleAnswer_thresholdingTask`,
  `isSingleAnswer_minThresholdTask`, `isSingleAnswer_halfSpaceTask`: these tasks have a single
  correct answer on every admissible model.
* `nonempty_correct_epsBaiTask`, `nonempty_correct_anyLowArmTask_iff`: every admissible model of
  the multiple-answer tasks has a correct answer.
* `correct_baiTask_subset_correct_epsBaiTask`: the best arm is `ε`-good for every `ε ≥ 0`.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016.
* [KTAS12] S. Kalyanakrishnan, A. Tewari, P. Auer and P. Stone, *PAC subset selection in
  stochastic multi-armed bandits*, ICML 2012.
* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)] {μ : α → ℝ}

/-! ### Best arm identification -/

/-- *Best arm identification* [GK16]: the correct answer of a vector of means is its arm with the
largest mean, and the admissible models are those with a unique best arm. -/
noncomputable def baiTask : IdentTask α (α → ℝ) α 𝓨 where
  M := {μ | ∃ a, ∀ b ≠ a, μ b < μ a}
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct μ := {a | ∀ b ≠ a, μ b < μ a}

@[simp]
lemma M_baiTask : (baiTask ν).M = {μ | ∃ a, ∀ b ≠ a, μ b < μ a} := (rfl)

@[simp]
lemma ν_baiTask : (baiTask ν).ν = ν := (rfl)

@[simp]
lemma correct_baiTask (μ : α → ℝ) : (baiTask ν).correct μ = {a | ∀ b ≠ a, μ b < μ a} := (rfl)

/-- A vector of means has at most one best arm. -/
lemma subsingleton_correct_baiTask (μ : α → ℝ) : ((baiTask ν).correct μ).Subsingleton := by
  intro a ha a' ha'
  by_contra h
  simp only [correct_baiTask, Set.mem_ofPred_eq] at ha ha'
  exact lt_asymm (ha a' (Ne.symm h)) (ha' a h)

lemma isSingleAnswer_baiTask : (baiTask ν).IsSingleAnswer := by
  refine (IdentTask.isSingleAnswer_iff _).2 ?_
  rintro μ ⟨a, ha⟩
  exact ⟨a, (subsingleton_correct_baiTask ν μ).eq_singleton_of_mem ha⟩

/-! ### Top-`m` identification -/

/-- *Top-`m` identification* [KTAS12]: the correct answer of a vector of means is the set of its
`m` arms with the largest means, and the admissible models are those where these arms are
separated from the others (so the set is unique, `isSingleAnswer_topMTask`). -/
noncomputable def topMTask (m : ℕ) : IdentTask α (α → ℝ) (Finset α) 𝓨 where
  M := {μ | ∃ s : Finset α, s.card = m ∧ ∀ a ∈ s, ∀ b ∉ s, μ b < μ a}
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct μ := {s | s.card = m ∧ ∀ a ∈ s, ∀ b ∉ s, μ b < μ a}

variable {m : ℕ}

@[simp]
lemma M_topMTask :
    (topMTask ν m).M = {μ | ∃ s : Finset α, s.card = m ∧ ∀ a ∈ s, ∀ b ∉ s, μ b < μ a} := (rfl)

@[simp]
lemma ν_topMTask : (topMTask ν m).ν = ν := (rfl)

@[simp]
lemma correct_topMTask (μ : α → ℝ) :
    (topMTask ν m).correct μ = {s | s.card = m ∧ ∀ a ∈ s, ∀ b ∉ s, μ b < μ a} := (rfl)

/-- A vector of means has at most one set of `m` arms whose means are larger than those of the
other arms. -/
lemma subsingleton_correct_topMTask (m : ℕ) (μ : α → ℝ) :
    ((topMTask ν m).correct μ).Subsingleton := by
  classical
  intro s hs t ht
  simp only [correct_topMTask, Set.mem_ofPred_eq] at hs ht
  by_contra hst
  -- Two distinct sets of the same cardinality: each has an element outside the other.
  obtain ⟨a, has, hat⟩ : ∃ a ∈ s, a ∉ t := by
    by_contra! h
    exact hst (Finset.eq_of_subset_of_card_le h (by rw [hs.1, ht.1]))
  obtain ⟨b, hbt, hbs⟩ : ∃ b ∈ t, b ∉ s := by
    by_contra! h
    exact hst (Finset.eq_of_subset_of_card_le h (by rw [hs.1, ht.1])).symm
  exact lt_asymm (hs.2 a has b hbs) (ht.2 b hbt a hat)

lemma isSingleAnswer_topMTask (m : ℕ) : (topMTask (α := α) ν m).IsSingleAnswer := by
  refine (IdentTask.isSingleAnswer_iff _).2 ?_
  rintro μ ⟨s, hs⟩
  exact ⟨s, (subsingleton_correct_topMTask ν m μ).eq_singleton_of_mem hs⟩

/-! ### `ε`-best arm identification -/

/-- *`ε`-best arm identification*: the correct answers of a vector of means are its `ε`-good arms,
whose mean is within `ε` of the largest mean, and every model is admissible. -/
noncomputable def epsBaiTask (ε : ℝ) : IdentTask α (α → ℝ) α 𝓨 where
  M := Set.univ
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct μ := {a | ∀ b, μ b ≤ μ a + ε}

variable {ε : ℝ}

@[simp]
lemma M_epsBaiTask : (epsBaiTask ν ε).M = Set.univ := (rfl)

@[simp]
lemma ν_epsBaiTask : (epsBaiTask ν ε).ν = ν := (rfl)

@[simp]
lemma correct_epsBaiTask (μ : α → ℝ) :
    (epsBaiTask ν ε).correct μ = {a | ∀ b, μ b ≤ μ a + ε} := (rfl)

/-- For `ε ≥ 0`, every vector of means on finitely many arms has an `ε`-good arm: an arm with the
largest mean. -/
lemma nonempty_correct_epsBaiTask [Finite α] [Nonempty α] (hε : 0 ≤ ε) (μ : α → ℝ) :
    ((epsBaiTask ν ε).correct μ).Nonempty := by
  obtain ⟨a, ha⟩ := Finite.exists_max μ
  exact ⟨a, fun b ↦ (ha b).trans (le_add_of_nonneg_right hε)⟩

/-- For `ε ≥ 0`, the best arm is `ε`-good. -/
lemma correct_baiTask_subset_correct_epsBaiTask (hε : 0 ≤ ε) (μ : α → ℝ) :
    (baiTask ν).correct μ ⊆ (epsBaiTask ν ε).correct μ := by
  intro a ha b
  simp only [correct_baiTask, Set.mem_ofPred_eq] at ha
  rcases eq_or_ne b a with rfl | hb
  · exact le_add_of_nonneg_right hε
  · exact (ha b hb).le.trans (le_add_of_nonneg_right hε)

/-! ### Thresholding -/

/-- *Thresholding*: the correct answer of a vector of means is the set of its arms with mean above
`γ`, and the admissible models are those with no mean equal to `γ`. -/
noncomputable def thresholdingTask (γ : ℝ) : IdentTask α (α → ℝ) (Finset α) 𝓨 where
  M := {μ | ∀ a, μ a ≠ γ}
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct μ := {s | ∀ a, a ∈ s ↔ γ < μ a}

variable {γ : ℝ}

@[simp]
lemma M_thresholdingTask : (thresholdingTask ν γ).M = {μ | ∀ a, μ a ≠ γ} := (rfl)

@[simp]
lemma ν_thresholdingTask : (thresholdingTask ν γ).ν = ν := (rfl)

@[simp]
lemma correct_thresholdingTask (μ : α → ℝ) :
    (thresholdingTask ν γ).correct μ = {s | ∀ a, a ∈ s ↔ γ < μ a} := (rfl)

/-- On finitely many arms, the arms with mean above `γ` form the unique correct answer of every
vector of means. -/
lemma correct_thresholdingTask_eq_singleton [Fintype α] [DecidablePred fun a ↦ γ < μ a] :
    (thresholdingTask ν γ).correct μ = {Finset.univ.filter fun a ↦ γ < μ a} := by
  ext s
  simp only [correct_thresholdingTask, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  refine ⟨fun h ↦ ?_, fun h a ↦ by simp [h]⟩
  ext a
  simp [h a]

lemma isSingleAnswer_thresholdingTask [Finite α] (γ : ℝ) :
    (thresholdingTask ν γ).IsSingleAnswer := by
  classical
  have := Fintype.ofFinite α
  exact (IdentTask.isSingleAnswer_iff _).2 fun μ _ ↦ ⟨_, correct_thresholdingTask_eq_singleton ν⟩

/-! ### Minimum threshold -/

/-- *Minimum threshold*: the correct answer of a vector of means is whether its smallest mean is
below `γ` (`true` iff some mean is below `γ`), and the admissible models are those whose smallest
mean is not `γ`: some mean is below `γ` or all means are above `γ`. -/
noncomputable def minThresholdTask (γ : ℝ) : IdentTask α (α → ℝ) Bool 𝓨 where
  M := {μ | (∃ a, μ a < γ) ∨ ∀ a, γ < μ a}
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct μ := {i | i = true ↔ ∃ a, μ a < γ}

@[simp]
lemma M_minThresholdTask :
    (minThresholdTask ν γ).M = {μ | (∃ a, μ a < γ) ∨ ∀ a, γ < μ a} := (rfl)

@[simp]
lemma ν_minThresholdTask : (minThresholdTask ν γ).ν = ν := (rfl)

@[simp]
lemma correct_minThresholdTask (μ : α → ℝ) :
    (minThresholdTask ν γ).correct μ = {i | i = true ↔ ∃ a, μ a < γ} := (rfl)

/-- The unique correct answer of every vector of means is `true` iff some mean is below `γ`. -/
lemma correct_minThresholdTask_eq_singleton [Decidable (∃ a, μ a < γ)] :
    (minThresholdTask ν γ).correct μ = {decide (∃ a, μ a < γ)} := by
  ext i
  cases i <;> simp

lemma isSingleAnswer_minThresholdTask (γ : ℝ) :
    (minThresholdTask (α := α) ν γ).IsSingleAnswer := by
  classical
  exact (IdentTask.isSingleAnswer_iff _).2 fun μ _ ↦
    ⟨_, correct_minThresholdTask_eq_singleton ν⟩

/-! ### Any Low Arm -/

/-- *Any Low Arm* [DK19, Example 1]: the correct answers of a vector of means are the arms with
mean below `γ` (answer `some a`), and "none" (answer `none`) if all means are above `γ`. The
admissible models are those with a correct answer (`nonempty_correct_anyLowArmTask_iff`): some
mean is below `γ` or all means are above `γ`. -/
noncomputable def anyLowArmTask (γ : ℝ) : IdentTask α (α → ℝ) (Option α) 𝓨 where
  M := {μ | (∃ a, μ a < γ) ∨ ∀ a, γ < μ a}
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct μ := {i | i.elim (∀ a, γ < μ a) fun a ↦ μ a < γ}

@[simp]
lemma M_anyLowArmTask : (anyLowArmTask ν γ).M = {μ | (∃ a, μ a < γ) ∨ ∀ a, γ < μ a} := (rfl)

@[simp]
lemma ν_anyLowArmTask : (anyLowArmTask ν γ).ν = ν := (rfl)

@[simp]
lemma correct_anyLowArmTask (μ : α → ℝ) :
    (anyLowArmTask ν γ).correct μ = {i | i.elim (∀ a, γ < μ a) fun a ↦ μ a < γ} := (rfl)

/-- `some a` is a correct answer of Any Low Arm iff the mean of `a` is below `γ`. -/
lemma some_mem_correct_anyLowArmTask {a : α} :
    some a ∈ (anyLowArmTask ν γ).correct μ ↔ μ a < γ := Iff.rfl

/-- `none` is a correct answer of Any Low Arm iff all means are above `γ`. -/
lemma none_mem_correct_anyLowArmTask :
    none ∈ (anyLowArmTask ν γ).correct μ ↔ ∀ a, γ < μ a := Iff.rfl

/-- A vector of means is an admissible model of Any Low Arm iff it has a correct answer. -/
lemma nonempty_correct_anyLowArmTask_iff :
    ((anyLowArmTask ν γ).correct μ).Nonempty ↔ μ ∈ (anyLowArmTask ν γ).M := by
  refine ⟨fun ⟨i, hi⟩ ↦ ?_, fun h ↦ ?_⟩
  · cases i with
    | none => exact Or.inr hi
    | some a => exact Or.inl ⟨a, hi⟩
  · rcases h with ⟨a, ha⟩ | h
    · exact ⟨some a, ha⟩
    · exact ⟨none, h⟩

/-! ### Half-space identification -/

/-- *Half-space identification*: the correct answer of a vector of means `μ` is the sign of
`u ⬝ᵥ μ` (`true` iff `0 < u ⬝ᵥ μ`), and the admissible models are those with `u ⬝ᵥ μ ≠ 0`. -/
noncomputable def halfSpaceTask (u : α → ℝ) [Fintype α] : IdentTask α (α → ℝ) Bool 𝓨 where
  M := {μ | u ⬝ᵥ μ ≠ 0}
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct μ := {i | i = true ↔ 0 < u ⬝ᵥ μ}

variable [Fintype α] {u : α → ℝ}

@[simp]
lemma M_halfSpaceTask : (halfSpaceTask ν u).M = {μ | u ⬝ᵥ μ ≠ 0} := (rfl)

@[simp]
lemma ν_halfSpaceTask : (halfSpaceTask ν u).ν = ν := (rfl)

@[simp]
lemma correct_halfSpaceTask (μ : α → ℝ) :
    (halfSpaceTask ν u).correct μ = {i | i = true ↔ 0 < u ⬝ᵥ μ} := (rfl)

/-- The unique correct answer of every vector of means `μ` is `true` iff `0 < u ⬝ᵥ μ`. -/
lemma correct_halfSpaceTask_eq_singleton :
    (halfSpaceTask ν u).correct μ = {decide (0 < u ⬝ᵥ μ)} := by
  ext i
  cases i <;> simp

lemma isSingleAnswer_halfSpaceTask (u : α → ℝ) : (halfSpaceTask ν u).IsSingleAnswer :=
  (IdentTask.isSingleAnswer_iff _).2 fun _ _ ↦ ⟨_, correct_halfSpaceTask_eq_singleton ν⟩

end LMLExplore.Identification
