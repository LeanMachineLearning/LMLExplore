/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Data.Finset.Card
public import LMLExplore.Identification.Task.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# Classical identification tasks

The classical identification tasks, which constrain the admissible models only through the question
asked about their means. Each task takes the bandit `ν θ : Kernel α 𝓨` of each model `θ` as a
parameter. Admissible models whose means lie in given sets (the means of an exponential family,
`[0, 1]` for Bernoulli arms, ...) are obtained with `IdentTask.restrict`.

Every task is stated for any type `Θ` of models with a mean functional `mean : Θ → α → ℝ`, the
mean `mean θ a` of arm `a` under the model `θ`. For example, Gaussian arms with unknown variances
are the models `θ : α → ℝ × ℝ≥0` with `mean θ a = (θ a).1`. The tasks on vectors of means
`μ : α → ℝ`, one per arm, are the case `Θ = α → ℝ`, `mean = id`, with typically arm `a` of `ν μ`
of mean `μ a`, for example `ν μ = gaussianBandit μ σ2`.

* `baiTask ν mean`: best arm identification. The answer is the arm with the largest mean, on the
  models with a unique best arm. The answers may form any type `ι`, with `mean : Θ → ι → ℝ`: the
  answer is then the one with the largest value, as in the transductive task of linear
  identification.
* `epsBaiTask ν mean ε`: `ε`-best arm identification. The correct answers are the arms whose mean
  is within `ε` of the largest mean, on every model. Several answers may be correct.
* `mulEpsBaiTask ν mean ε`: multiplicative `ε`-best arm identification [JDK23b]. The correct
  answers are the arms whose mean is at least `(1 - ε)` times the largest mean, on the models with
  positive means. Several answers may be correct.
* `topMTask ν mean m`: top-`m` identification. The answer is the set of the `m` arms with the
  largest means, on the models where it is unique.
* `thresholdingTask ν mean γ`: the answer is the set of arms with mean above `γ`, on the models
  with no mean equal to `γ`.
* `minThresholdTask ν mean γ`: the answer is whether the smallest mean is below `γ`, on the
  models whose smallest mean is not `γ`.
* `anyLowArmTask ν mean γ`: *Any Low Arm* [DK19, Example 1]. The correct answers are the arms with
  mean below `γ` (`some a`), or "none" (`none`) if all means are above `γ`, on the models where
  one of these holds. Several answers may be correct.
* `halfSpaceTask ν mean u`: the answer is the sign of `u ⬝ᵥ mean θ`, on the models with
  `u ⬝ᵥ mean θ ≠ 0`.
* `epsTopMTask ν mean m ε`: top-`m` identification with tolerance `ε` [KTAS12]. The correct
  answers are the sets of `m` arms whose means are all at least the `m`-th largest mean minus `ε`,
  on every model. Several answers may be correct.

## Main statements

* `isSingleAnswer_baiTask`, `isSingleAnswer_topMTask`, `isSingleAnswer_minThresholdTask`,
  `isSingleAnswer_halfSpaceTask`: these tasks have a single correct answer on every admissible
  model.
* `isSingleAnswer_thresholdingTask`: on finitely many arms, thresholding has a single correct
  answer on every admissible model.
* `comap_baiTask`, `comap_epsBaiTask`, `comap_mulEpsBaiTask`, `comap_topMTask`,
  `comap_thresholdingTask`, `comap_minThresholdTask`, `comap_anyLowArmTask`, `comap_halfSpaceTask`,
  `comap_epsTopMTask`:
  the pullback of a classical task along a map `f` of models is the same task for the bandits and
  the mean functional composed with `f`. In particular a task on models `Θ` whose bandits depend on
  the means only, `ν θ = ν' (mean θ)`, is the pullback along `mean` of the task on vectors of
  means for `ν'`.
* `correct_baiTask_eq_singleton_iff`: `a` is the only best arm of `θ` iff
  `mean θ b < mean θ a` for every arm `b ≠ a`.
* `nonempty_correct_epsBaiTask`: for `ε ≥ 0` and finitely many (at least one) arms, every model
  has an `ε`-good arm.
* `correct_epsBaiTask_eq_singleton_iff`: for `ε ≥ 0`, `a` is the only `ε`-good arm of `θ` iff
  `mean θ b + ε < mean θ a` for every arm `b ≠ a`.
* `nonempty_correct_anyLowArmTask_iff`: the admissible models of Any Low Arm are exactly the
  models with a correct answer.
* `correct_baiTask_subset_correct_epsBaiTask`: the best arm is `ε`-good for every `ε ≥ 0`.
* `correct_mulEpsBaiTask_eq_correct_epsBaiTask`: for `ε ≤ 1`, the multiplicatively `ε`-good arms
  are the additively `ε * max_b mean θ b`-good arms.
* `nonempty_correct_mulEpsBaiTask`, `correct_mulEpsBaiTask_eq_singleton_iff`,
  `correct_baiTask_subset_correct_mulEpsBaiTask`: for `ε ≥ 0` and nonnegative means, every model
  has a multiplicatively `ε`-good arm, `a` is the only one iff `mean θ b < (1 - ε) * mean θ a` for
  every arm `b ≠ a`, and the best arm is one.
* `mem_correct_epsTopMTask_of_forall_le`, `nonempty_correct_epsTopMTask`: for `ε ≥ 0`, a set of `m`
  arms with the largest means is a correct answer of `(ε, m)`-top identification, so every model
  has one when `m ≤ K`.
* `exists_add_lt_of_notMem_correct_epsTopMTask`: if a set `s` of `m` arms is not a correct
  answer, then for every set `t` of `m` arms with the largest means, some arm `b ∈ s \ t` has
  `mean θ b + ε < mean θ i` for some arm `i ∈ t \ s`. This is the step of the proof of
  [KTAS12, Theorem 1] that reduces a wrong answer of LUCB to a violated confidence bound.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016.
* [KTAS12] S. Kalyanakrishnan, A. Tewari, P. Auer and P. Stone, *PAC subset selection in
  stochastic multi-armed bandits*, ICML 2012.
* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019.
* [JDK23b] M. Jourdan, R. Degenne and E. Kaufmann, *An ε-best-arm identification algorithm for
  fixed-confidence and beyond*, NeurIPS 2023.
-/

public section

open MeasureTheory ProbabilityTheory

namespace LMLExplore.Identification

variable {α Θ Θ' 𝓨 ι : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}

section BestArm

/-! ### Best arm identification -/

variable (ν : Θ → Kernel α 𝓨) [∀ θ, IsMarkovKernel (ν θ)] (mean : Θ → ι → ℝ) {θ : Θ}

/-- *Best arm identification* [GK16] on a type `Θ` of models with the mean functional
`mean : Θ → α → ℝ`: the correct answer of a model `θ` is its arm with the largest mean
`mean θ a`, and the admissible models are those with a unique best arm. The task on vectors of
means is `baiTask ν id`.

More generally, the answers form any type `ι`, with the value `mean θ a` of the answer `a` under
`θ`, and the correct answer is the one with the largest value. Best arm identification is the case
`ι = α`. -/
noncomputable def baiTask : IdentTask α Θ ι 𝓨 where
  M := {θ | ∃ a, ∀ b ≠ a, mean θ b < mean θ a}
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct θ := {a | ∀ b ≠ a, mean θ b < mean θ a}

@[simp]
lemma M_baiTask : (baiTask ν mean).M = {θ | ∃ a, ∀ b ≠ a, mean θ b < mean θ a} := (rfl)

@[simp]
lemma ν_baiTask : (baiTask ν mean).ν = ν := (rfl)

@[simp]
lemma correct_baiTask (θ : Θ) :
    (baiTask ν mean).correct θ = {a | ∀ b ≠ a, mean θ b < mean θ a} := (rfl)

/-- The pullback of best arm identification along a map `f` of models is best arm identification
for the bandits and the mean functional composed with `f`. With `mean = id`, this says that for
bandits `ν' : (α → ℝ) → Kernel α 𝓨` indexed by vectors of means and a mean functional
`mean : Θ' → α → ℝ`, the task `baiTask (fun θ ↦ ν' (mean θ)) mean` is the pullback of
`baiTask ν' id` along `mean`, and similarly for the other classical tasks. -/
@[simp]
lemma comap_baiTask (f : Θ' → Θ) :
    (baiTask ν mean).comap f = baiTask (fun θ ↦ ν (f θ)) (fun θ ↦ mean (f θ)) := by
  ext <;> simp

/-- A model has at most one best arm. -/
lemma subsingleton_correct_baiTask (θ : Θ) : ((baiTask ν mean).correct θ).Subsingleton := by
  intro a ha a' ha'
  by_contra h
  simp only [correct_baiTask, Set.mem_ofPred_eq] at ha ha'
  exact lt_asymm (ha a' (Ne.symm h)) (ha' a h)

/-- The arm `a` is the only best arm of `θ` iff every other arm `b` has `mean θ b < mean θ a`. -/
lemma correct_baiTask_eq_singleton_iff {a : ι} :
    (baiTask ν mean).correct θ = {a} ↔ ∀ b ≠ a, mean θ b < mean θ a :=
  ⟨fun h ↦ by simpa using h.symm.subset (Set.mem_singleton a),
    fun h ↦ (subsingleton_correct_baiTask ν mean θ).eq_singleton_of_mem h⟩

/-- Best arm identification is a single-answer task: every model with a unique best arm has
exactly one correct answer, its best arm. -/
lemma isSingleAnswer_baiTask : (baiTask ν mean).IsSingleAnswer := by
  refine (IdentTask.isSingleAnswer_iff _).2 ?_
  rintro θ ⟨a, ha⟩
  exact ⟨a, (correct_baiTask_eq_singleton_iff ν mean).2 ha⟩

end BestArm

section MeanFunctional

variable (ν : Θ → Kernel α 𝓨) [∀ θ, IsMarkovKernel (ν θ)] (mean : Θ → α → ℝ) {θ : Θ}

/-! ### `ε`-best arm identification -/

/-- *`ε`-best arm identification* on a type `Θ` of models with the mean functional
`mean : Θ → α → ℝ`: the correct answers of a model `θ` are its `ε`-good arms, whose mean is within
`ε` of the largest mean, and every model is admissible. The task on vectors of means is
`epsBaiTask ν id ε`. -/
noncomputable def epsBaiTask (ε : ℝ) : IdentTask α Θ α 𝓨 where
  M := Set.univ
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct θ := {a | ∀ b, mean θ b ≤ mean θ a + ε}

variable {ε : ℝ}

@[simp]
lemma M_epsBaiTask : (epsBaiTask ν mean ε).M = Set.univ := (rfl)

@[simp]
lemma ν_epsBaiTask : (epsBaiTask ν mean ε).ν = ν := (rfl)

@[simp]
lemma correct_epsBaiTask (θ : Θ) :
    (epsBaiTask ν mean ε).correct θ = {a | ∀ b, mean θ b ≤ mean θ a + ε} := (rfl)

/-- The pullback of `ε`-best arm identification along a map `f` of models is `ε`-best arm
identification for the bandits and the mean functional composed with `f`. -/
@[simp]
lemma comap_epsBaiTask (f : Θ' → Θ) :
    (epsBaiTask ν mean ε).comap f = epsBaiTask (fun θ ↦ ν (f θ)) (fun θ ↦ mean (f θ)) ε := by
  ext <;> simp

/-- For `ε ≥ 0`, every model on finitely many arms has an `ε`-good arm: an arm with the largest
mean. -/
lemma nonempty_correct_epsBaiTask [Finite α] [Nonempty α] (hε : 0 ≤ ε) (θ : Θ) :
    ((epsBaiTask ν mean ε).correct θ).Nonempty := by
  obtain ⟨a, ha⟩ := Finite.exists_max (mean θ)
  exact ⟨a, fun b ↦ (ha b).trans (le_add_of_nonneg_right hε)⟩

/-- For `ε ≥ 0`, the arm `a` is the only `ε`-good arm of `θ` iff every other arm `b` has
`mean θ b + ε < mean θ a`. -/
lemma correct_epsBaiTask_eq_singleton_iff {a : α} (hε : 0 ≤ ε) :
    (epsBaiTask ν mean ε).correct θ = {a} ↔ ∀ b ≠ a, mean θ b + ε < mean θ a := by
  set μ := mean θ
  simp only [correct_epsBaiTask]
  constructor
  · intro h b hba
    have ha : ∀ c, μ c ≤ μ a + ε := by
      have : a ∈ {a' | ∀ c, μ c ≤ μ a' + ε} := h ▸ Set.mem_singleton a
      exact this
    -- An arm with a larger mean than `a` would be `ε`-good, so `a` has the largest mean.
    have ha_max : ∀ c, μ c ≤ μ a := fun c ↦ by
      by_contra! hc
      have : c ∈ {a' | ∀ c, μ c ≤ μ a' + ε} := fun d ↦ (ha d).trans (by linarith)
      rw [h, Set.mem_singleton_iff] at this
      exact hc.ne' (this ▸ rfl)
    -- If `μ a ≤ μ b + ε`, then `b` would be `ε`-good.
    by_contra! hb
    have : b ∈ {a' | ∀ c, μ c ≤ μ a' + ε} := fun c ↦ (ha_max c).trans hb
    rw [h, Set.mem_singleton_iff] at this
    exact hba this
  · intro h
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine ⟨fun hc ↦ ?_, ?_⟩
    · by_contra hca
      linarith [h c hca, hc a]
    · rintro rfl b
      rcases eq_or_ne b c with rfl | hbc
      · linarith
      · linarith [h b hbc]

/-- For `ε ≥ 0`, the best arm is `ε`-good. -/
lemma correct_baiTask_subset_correct_epsBaiTask (hε : 0 ≤ ε) (θ : Θ) :
    (baiTask ν mean).correct θ ⊆ (epsBaiTask ν mean ε).correct θ := by
  intro a ha b
  simp only [correct_baiTask, Set.mem_ofPred_eq] at ha
  rcases eq_or_ne b a with rfl | hb
  · exact le_add_of_nonneg_right hε
  · exact (ha b hb).le.trans (le_add_of_nonneg_right hε)

/-! ### Multiplicative `ε`-best arm identification -/

/-- *Multiplicative `ε`-best arm identification* [JDK23b] on a type `Θ` of models with the mean
functional `mean : Θ → α → ℝ`: the correct answers of a model `θ` are its multiplicatively
`ε`-good arms, the arms `a` with `(1 - ε) * mean θ b ≤ mean θ a` for every arm `b`, that is, whose
mean is at least `(1 - ε)` times the largest mean, and the admissible models are those with
positive means. The task on vectors of means is `mulEpsBaiTask ν id ε`. -/
noncomputable def mulEpsBaiTask (ε : ℝ) : IdentTask α Θ α 𝓨 where
  M := {θ | ∀ a, 0 < mean θ a}
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct θ := {a | ∀ b, (1 - ε) * mean θ b ≤ mean θ a}

@[simp]
lemma M_mulEpsBaiTask : (mulEpsBaiTask ν mean ε).M = {θ | ∀ a, 0 < mean θ a} := (rfl)

@[simp]
lemma ν_mulEpsBaiTask : (mulEpsBaiTask ν mean ε).ν = ν := (rfl)

@[simp]
lemma correct_mulEpsBaiTask (θ : Θ) :
    (mulEpsBaiTask ν mean ε).correct θ = {a | ∀ b, (1 - ε) * mean θ b ≤ mean θ a} := (rfl)

/-- The pullback of multiplicative `ε`-best arm identification along a map `f` of models is
multiplicative `ε`-best arm identification for the bandits and the mean functional composed with
`f`. -/
@[simp]
lemma comap_mulEpsBaiTask (f : Θ' → Θ) :
    (mulEpsBaiTask ν mean ε).comap f = mulEpsBaiTask (fun θ ↦ ν (f θ)) (fun θ ↦ mean (f θ)) ε := by
  ext <;> simp

/-- For `ε ≤ 1` and an arm `b` with the largest mean, the multiplicatively `ε`-good arms are the
additively `ε * mean θ b`-good arms: `(1 - ε) * mean θ b ≤ mean θ a` iff `a` is within
`ε * mean θ b` of the largest mean. -/
lemma correct_mulEpsBaiTask_eq_correct_epsBaiTask (hε : ε ≤ 1) {b : α}
    (hb : ∀ c, mean θ c ≤ mean θ b) :
    (mulEpsBaiTask ν mean ε).correct θ = (epsBaiTask ν mean (ε * mean θ b)).correct θ := by
  ext a
  simp only [correct_mulEpsBaiTask, correct_epsBaiTask, Set.mem_ofPred_eq]
  refine ⟨fun ha c ↦ by linarith [ha b, hb c], fun ha c ↦ ?_⟩
  nlinarith [ha b, mul_nonneg (sub_nonneg.2 hε) (sub_nonneg.2 (hb c))]

/-- For `ε ≥ 0`, every model with nonnegative means on finitely many (at least one) arms has a
multiplicatively `ε`-good arm: an arm with the largest mean. -/
lemma nonempty_correct_mulEpsBaiTask [Finite α] [Nonempty α] (hε : 0 ≤ ε)
    (hθ : ∀ b, 0 ≤ mean θ b) : ((mulEpsBaiTask ν mean ε).correct θ).Nonempty := by
  obtain ⟨a, ha⟩ := Finite.exists_max (mean θ)
  exact ⟨a, fun b ↦ by nlinarith [ha b, mul_nonneg hε (hθ b)]⟩

/-- For `ε ≥ 0` and a model with nonnegative means, the best arm is multiplicatively `ε`-good. -/
lemma correct_baiTask_subset_correct_mulEpsBaiTask (hε : 0 ≤ ε) (hθ : ∀ b, 0 ≤ mean θ b) :
    (baiTask ν mean).correct θ ⊆ (mulEpsBaiTask ν mean ε).correct θ := by
  intro a ha b
  simp only [correct_baiTask, Set.mem_ofPred_eq] at ha
  have hba : mean θ b ≤ mean θ a := by
    rcases eq_or_ne b a with rfl | hb
    · exact le_rfl
    · exact (ha b hb).le
  nlinarith [mul_nonneg hε (hθ b)]

/-- For `ε ≥ 0` and a model with nonnegative means, the arm `a` is the only multiplicatively
`ε`-good arm of `θ` iff every other arm `b` has `mean θ b < (1 - ε) * mean θ a`. -/
lemma correct_mulEpsBaiTask_eq_singleton_iff {a : α} (hε : 0 ≤ ε) (hθ : ∀ b, 0 ≤ mean θ b) :
    (mulEpsBaiTask ν mean ε).correct θ = {a} ↔ ∀ b ≠ a, mean θ b < (1 - ε) * mean θ a := by
  set μ := mean θ
  simp only [correct_mulEpsBaiTask]
  constructor
  · intro h b hba
    have ha : ∀ c, (1 - ε) * μ c ≤ μ a := by
      have : a ∈ {a' | ∀ c, (1 - ε) * μ c ≤ μ a'} := h ▸ Set.mem_singleton a
      exact this
    -- An arm with a larger mean than `a` would be `ε`-good, so `a` has the largest mean.
    have ha_max : ∀ c, μ c ≤ μ a := fun c ↦ by
      by_contra! hc
      have : c ∈ {a' | ∀ c, (1 - ε) * μ c ≤ μ a'} := fun d ↦ (ha d).trans hc.le
      rw [h, Set.mem_singleton_iff] at this
      exact hc.ne' (this ▸ rfl)
    -- If `(1 - ε) * μ a ≤ μ b`, then `b` would be `ε`-good: for `ε ≤ 1` since `μ a` is the
    -- largest mean, and for `ε > 1` since the means are nonnegative.
    by_contra! hb
    have : b ∈ {a' | ∀ c, (1 - ε) * μ c ≤ μ a'} := fun c ↦ by
      rcases le_or_gt ε 1 with hε1 | hε1
      · nlinarith [mul_nonneg (sub_nonneg.2 hε1) (sub_nonneg.2 (ha_max c))]
      · nlinarith [mul_nonneg (sub_nonneg.2 hε1.le) (hθ c), hθ b]
    rw [h, Set.mem_singleton_iff] at this
    exact hba this
  · intro h
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine ⟨fun hc ↦ ?_, ?_⟩
    · by_contra hca
      linarith [h c hca, hc a]
    · rintro rfl b
      rcases eq_or_ne b c with rfl | hbc
      · nlinarith [mul_nonneg hε (hθ b)]
      · nlinarith [h b hbc, mul_nonneg hε (hθ b), mul_nonneg hε (hθ c)]

/-! ### Top-`m` identification -/

/-- *Top-`m` identification* [KTAS12] on a type `Θ` of models with the mean functional
`mean : Θ → α → ℝ`: the correct answer of a model `θ` is the set of its `m` arms with the largest
means `mean θ a`, and the admissible models are those where these arms are separated from the
others (so the set is unique, `isSingleAnswer_topMTask`). The task on vectors of means is
`topMTask ν id m`. -/
noncomputable def topMTask (m : ℕ) : IdentTask α Θ (Finset α) 𝓨 where
  M := {θ | ∃ s : Finset α, s.card = m ∧ ∀ a ∈ s, ∀ b ∉ s, mean θ b < mean θ a}
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct θ := {s | s.card = m ∧ ∀ a ∈ s, ∀ b ∉ s, mean θ b < mean θ a}

variable {m : ℕ}

@[simp]
lemma M_topMTask : (topMTask ν mean m).M =
    {θ | ∃ s : Finset α, s.card = m ∧ ∀ a ∈ s, ∀ b ∉ s, mean θ b < mean θ a} := (rfl)

@[simp]
lemma ν_topMTask : (topMTask ν mean m).ν = ν := (rfl)

@[simp]
lemma correct_topMTask (θ : Θ) :
    (topMTask ν mean m).correct θ =
      {s | s.card = m ∧ ∀ a ∈ s, ∀ b ∉ s, mean θ b < mean θ a} := (rfl)

/-- The pullback of top-`m` identification along a map `f` of models is top-`m` identification for
the bandits and the mean functional composed with `f`. -/
@[simp]
lemma comap_topMTask (f : Θ' → Θ) :
    (topMTask ν mean m).comap f = topMTask (fun θ ↦ ν (f θ)) (fun θ ↦ mean (f θ)) m := by
  ext <;> simp

/-- A model has at most one set of `m` arms whose means are larger than those of the other
arms. -/
lemma subsingleton_correct_topMTask (m : ℕ) (θ : Θ) :
    ((topMTask ν mean m).correct θ).Subsingleton := by
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

/-- Top-`m` identification is a single-answer task: every admissible model has exactly one set of
`m` arms whose means are larger than those of the other arms. -/
lemma isSingleAnswer_topMTask (m : ℕ) : (topMTask ν mean m).IsSingleAnswer := by
  refine (IdentTask.isSingleAnswer_iff _).2 ?_
  rintro θ ⟨s, hs⟩
  exact ⟨s, (subsingleton_correct_topMTask ν mean m θ).eq_singleton_of_mem hs⟩

/-! ### Thresholding -/

/-- *Thresholding* on a type `Θ` of models with the mean functional `mean : Θ → α → ℝ`: the
correct answer of a model `θ` is the set of its arms with mean `mean θ a` above `γ`, and the
admissible models are those with no mean equal to `γ`. The task on vectors of means is
`thresholdingTask ν id γ`. -/
noncomputable def thresholdingTask (γ : ℝ) : IdentTask α Θ (Finset α) 𝓨 where
  M := {θ | ∀ a, mean θ a ≠ γ}
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct θ := {s | ∀ a, a ∈ s ↔ γ < mean θ a}

variable {γ : ℝ}

@[simp]
lemma M_thresholdingTask : (thresholdingTask ν mean γ).M = {θ | ∀ a, mean θ a ≠ γ} := (rfl)

@[simp]
lemma ν_thresholdingTask : (thresholdingTask ν mean γ).ν = ν := (rfl)

@[simp]
lemma correct_thresholdingTask (θ : Θ) :
    (thresholdingTask ν mean γ).correct θ = {s | ∀ a, a ∈ s ↔ γ < mean θ a} := (rfl)

/-- The pullback of thresholding along a map `f` of models is thresholding for the bandits and the
mean functional composed with `f`. -/
@[simp]
lemma comap_thresholdingTask (f : Θ' → Θ) :
    (thresholdingTask ν mean γ).comap f =
      thresholdingTask (fun θ ↦ ν (f θ)) (fun θ ↦ mean (f θ)) γ := by
  ext <;> simp

/-- On finitely many arms, the arms with mean above `γ` form the unique correct answer of every
model. -/
lemma correct_thresholdingTask_eq_singleton [Fintype α] [DecidablePred fun a ↦ γ < mean θ a] :
    (thresholdingTask ν mean γ).correct θ = {Finset.univ.filter fun a ↦ γ < mean θ a} := by
  ext s
  simp only [correct_thresholdingTask, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  refine ⟨fun h ↦ ?_, fun h a ↦ by simp [h]⟩
  ext a
  simp [h a]

/-- On finitely many arms, thresholding is a single-answer task: the set of arms with mean above
`γ` is the only correct answer. -/
lemma isSingleAnswer_thresholdingTask [Finite α] (γ : ℝ) :
    (thresholdingTask ν mean γ).IsSingleAnswer := by
  classical
  have := Fintype.ofFinite α
  exact (IdentTask.isSingleAnswer_iff _).2 fun θ _ ↦
    ⟨_, correct_thresholdingTask_eq_singleton ν mean⟩

/-! ### Minimum threshold -/

/-- *Minimum threshold* on a type `Θ` of models with the mean functional `mean : Θ → α → ℝ`: the
correct answer of a model `θ` is whether its smallest mean is below `γ` (`true` iff some mean
`mean θ a` is below `γ`), and the admissible models are those whose smallest mean is not `γ`: some
mean is below `γ` or all means are above `γ`. The task on vectors of means is
`minThresholdTask ν id γ`. -/
noncomputable def minThresholdTask (γ : ℝ) : IdentTask α Θ Bool 𝓨 where
  M := {θ | (∃ a, mean θ a < γ) ∨ ∀ a, γ < mean θ a}
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct θ := {i | i = true ↔ ∃ a, mean θ a < γ}

@[simp]
lemma M_minThresholdTask :
    (minThresholdTask ν mean γ).M = {θ | (∃ a, mean θ a < γ) ∨ ∀ a, γ < mean θ a} := (rfl)

@[simp]
lemma ν_minThresholdTask : (minThresholdTask ν mean γ).ν = ν := (rfl)

@[simp]
lemma correct_minThresholdTask (θ : Θ) :
    (minThresholdTask ν mean γ).correct θ = {i | i = true ↔ ∃ a, mean θ a < γ} := (rfl)

/-- The pullback of minimum threshold along a map `f` of models is minimum threshold for the bandits
and the mean functional composed with `f`. -/
@[simp]
lemma comap_minThresholdTask (f : Θ' → Θ) :
    (minThresholdTask ν mean γ).comap f =
      minThresholdTask (fun θ ↦ ν (f θ)) (fun θ ↦ mean (f θ)) γ := by
  ext <;> simp

/-- The unique correct answer of every model is `true` iff some mean is below `γ`. -/
lemma correct_minThresholdTask_eq_singleton [Decidable (∃ a, mean θ a < γ)] :
    (minThresholdTask ν mean γ).correct θ = {decide (∃ a, mean θ a < γ)} := by
  ext i
  cases i <;> simp

/-- Minimum threshold is a single-answer task: the only correct answer is whether some mean is
below `γ`. -/
lemma isSingleAnswer_minThresholdTask (γ : ℝ) :
    (minThresholdTask ν mean γ).IsSingleAnswer := by
  classical
  exact (IdentTask.isSingleAnswer_iff _).2 fun θ _ ↦
    ⟨_, correct_minThresholdTask_eq_singleton ν mean⟩

/-! ### Any Low Arm -/

/-- *Any Low Arm* [DK19, Example 1] on a type `Θ` of models with the mean functional
`mean : Θ → α → ℝ`: the correct answers of a model `θ` are the arms with mean `mean θ a` below `γ`
(answer `some a`), and "none" (answer `none`) if all means are above `γ`. The admissible models
are those with a correct answer (`nonempty_correct_anyLowArmTask_iff`): some mean is below `γ` or
all means are above `γ`. The task on vectors of means is `anyLowArmTask ν id γ`. -/
noncomputable def anyLowArmTask (γ : ℝ) : IdentTask α Θ (Option α) 𝓨 where
  M := {θ | (∃ a, mean θ a < γ) ∨ ∀ a, γ < mean θ a}
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct θ := {i | i.elim (∀ a, γ < mean θ a) fun a ↦ mean θ a < γ}

@[simp]
lemma M_anyLowArmTask :
    (anyLowArmTask ν mean γ).M = {θ | (∃ a, mean θ a < γ) ∨ ∀ a, γ < mean θ a} := (rfl)

@[simp]
lemma ν_anyLowArmTask : (anyLowArmTask ν mean γ).ν = ν := (rfl)

@[simp]
lemma correct_anyLowArmTask (θ : Θ) :
    (anyLowArmTask ν mean γ).correct θ =
      {i | i.elim (∀ a, γ < mean θ a) fun a ↦ mean θ a < γ} := (rfl)

/-- The pullback of Any Low Arm along a map `f` of models is Any Low Arm for the bandits and the
mean functional composed with `f`. -/
@[simp]
lemma comap_anyLowArmTask (f : Θ' → Θ) :
    (anyLowArmTask ν mean γ).comap f = anyLowArmTask (fun θ ↦ ν (f θ)) (fun θ ↦ mean (f θ)) γ := by
  ext <;> simp

/-- `some a` is a correct answer of Any Low Arm iff the mean of `a` is below `γ`. -/
lemma some_mem_correct_anyLowArmTask {a : α} :
    some a ∈ (anyLowArmTask ν mean γ).correct θ ↔ mean θ a < γ := Iff.rfl

/-- `none` is a correct answer of Any Low Arm iff all means are above `γ`. -/
lemma none_mem_correct_anyLowArmTask :
    none ∈ (anyLowArmTask ν mean γ).correct θ ↔ ∀ a, γ < mean θ a := Iff.rfl

/-- A model is an admissible model of Any Low Arm iff it has a correct answer. -/
lemma nonempty_correct_anyLowArmTask_iff :
    ((anyLowArmTask ν mean γ).correct θ).Nonempty ↔ θ ∈ (anyLowArmTask ν mean γ).M := by
  refine ⟨fun ⟨i, hi⟩ ↦ ?_, fun h ↦ ?_⟩
  · cases i with
    | none => exact Or.inr hi
    | some a => exact Or.inl ⟨a, hi⟩
  · rcases h with ⟨a, ha⟩ | h
    · exact ⟨some a, ha⟩
    · exact ⟨none, h⟩

/-! ### Half-space identification -/

/-- *Half-space identification* on a type `Θ` of models with the mean functional
`mean : Θ → α → ℝ`: the correct answer of a model `θ` is the sign of `u ⬝ᵥ mean θ` (`true` iff
`0 < u ⬝ᵥ mean θ`), and the admissible models are those with `u ⬝ᵥ mean θ ≠ 0`. The task on
vectors of means is `halfSpaceTask ν id u`. -/
noncomputable def halfSpaceTask (u : α → ℝ) [Fintype α] : IdentTask α Θ Bool 𝓨 where
  M := {θ | u ⬝ᵥ mean θ ≠ 0}
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct θ := {i | i = true ↔ 0 < u ⬝ᵥ mean θ}

variable [Fintype α] {u : α → ℝ}

@[simp]
lemma M_halfSpaceTask : (halfSpaceTask ν mean u).M = {θ | u ⬝ᵥ mean θ ≠ 0} := (rfl)

@[simp]
lemma ν_halfSpaceTask : (halfSpaceTask ν mean u).ν = ν := (rfl)

@[simp]
lemma correct_halfSpaceTask (θ : Θ) :
    (halfSpaceTask ν mean u).correct θ = {i | i = true ↔ 0 < u ⬝ᵥ mean θ} := (rfl)

/-- The pullback of half-space identification along a map `f` of models is half-space identification
for the bandits and the mean functional composed with `f`. -/
@[simp]
lemma comap_halfSpaceTask (f : Θ' → Θ) :
    (halfSpaceTask ν mean u).comap f = halfSpaceTask (fun θ ↦ ν (f θ)) (fun θ ↦ mean (f θ)) u := by
  ext <;> simp

/-- The unique correct answer of every model `θ` is `true` iff `0 < u ⬝ᵥ mean θ`. -/
lemma correct_halfSpaceTask_eq_singleton :
    (halfSpaceTask ν mean u).correct θ = {decide (0 < u ⬝ᵥ mean θ)} := by
  ext i
  cases i <;> simp

/-- Half-space identification is a single-answer task: the only correct answer is the sign of
`u ⬝ᵥ mean θ`. -/
lemma isSingleAnswer_halfSpaceTask (u : α → ℝ) : (halfSpaceTask ν mean u).IsSingleAnswer :=
  (IdentTask.isSingleAnswer_iff _).2 fun _ _ ↦ ⟨_, correct_halfSpaceTask_eq_singleton ν mean⟩

/-! ### Top-`m` identification with tolerance `ε` -/

/-- *Top-`m` identification with tolerance `ε`* [KTAS12] on a type `Θ` of models with the mean
functional `mean : Θ → α → ℝ`: the correct answers of a model `θ` are the sets of `m` arms that
are all *`(ε, m)`-optimal*, and every model is admissible. The arm `a` is `(ε, m)`-optimal if fewer
than `m` arms have a mean larger than `mean θ a + ε`, that is, if `mean θ a` is at least the
`m`-th largest mean minus `ε`. For `m = 1` this is `ε`-best arm identification
(`singleton_mem_correct_epsTopMTask_one_iff`). The task on vectors of means is
`epsTopMTask ν id m ε`. -/
noncomputable def epsTopMTask (m : ℕ) (ε : ℝ) : IdentTask α Θ (Finset α) 𝓨 where
  M := Set.univ
  ν := ν
  isMarkovKernel_ν _ := inferInstance
  correct θ :=
    {s | s.card = m ∧ ∀ a ∈ s, (Finset.univ.filter fun b ↦ mean θ a + ε < mean θ b).card < m}

@[simp]
lemma M_epsTopMTask : (epsTopMTask ν mean m ε).M = Set.univ := (rfl)

@[simp]
lemma ν_epsTopMTask : (epsTopMTask ν mean m ε).ν = ν := (rfl)

@[simp]
lemma correct_epsTopMTask (θ : Θ) :
    (epsTopMTask ν mean m ε).correct θ =
      {s | s.card = m ∧
        ∀ a ∈ s, (Finset.univ.filter fun b ↦ mean θ a + ε < mean θ b).card < m} := (rfl)

/-- The pullback of top-`m` identification with tolerance `ε` along a map `f` of models is top-`m`
identification with tolerance `ε` for the bandits and the mean functional composed with `f`. -/
@[simp]
lemma comap_epsTopMTask (f : Θ' → Θ) :
    (epsTopMTask ν mean m ε).comap f = epsTopMTask (fun θ ↦ ν (f θ)) (fun θ ↦ mean (f θ)) m ε := by
  ext <;> simp

/-- If every value of `μ` on the set `t` of `m` arms is at least every value outside `t` and some
arm `i ∈ t` has `μ i ≤ μ x + ε`, then fewer than `m` arms have a value larger than `μ x + ε`: they
are all arms of `t` other than `i`. -/
private lemma card_filter_add_lt_lt_of_mem {μ : α → ℝ} {t : Finset α} (ht : t.card = m)
    (ht' : ∀ a ∈ t, ∀ c ∉ t, μ c ≤ μ a) {i x : α} (hi : i ∈ t) (hle : μ i ≤ μ x + ε) :
    (Finset.univ.filter fun b ↦ μ x + ε < μ b).card < m := by
  classical
  calc (Finset.univ.filter fun b ↦ μ x + ε < μ b).card
  _ ≤ (t.erase i).card := Finset.card_le_card fun b hb ↦ by
    have hb : μ x + ε < μ b := (Finset.mem_filter.1 hb).2
    refine Finset.mem_erase.2 ⟨fun hbi ↦ by subst hbi; linarith, ?_⟩
    by_contra hbt
    linarith [ht' i hi b hbt]
  _ < m := by
    have := Finset.card_pos.2 ⟨i, hi⟩
    rw [Finset.card_erase_of_mem hi]
    omega

/-- For `ε ≥ 0`, if every mean of the set `t` of `m` arms is at least every mean outside `t`, then
`t` is a correct answer of `(ε, m)`-top identification. -/
lemma mem_correct_epsTopMTask_of_forall_le (hε : 0 ≤ ε) {t : Finset α} (ht : t.card = m)
    (ht' : ∀ a ∈ t, ∀ c ∉ t, mean θ c ≤ mean θ a) : t ∈ (epsTopMTask ν mean m ε).correct θ :=
  ⟨ht, fun _ ha ↦ card_filter_add_lt_lt_of_mem ht ht' ha (le_add_of_nonneg_right hε)⟩

/-- For `ε ≥ 0` and `m` at most the number of arms, every model has a correct answer of
`(ε, m)`-top identification: a set of `m` arms with the largest means. -/
lemma nonempty_correct_epsTopMTask (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α) (θ : Θ) :
    ((epsTopMTask ν mean m ε).correct θ).Nonempty := by
  classical
  obtain ⟨t, -, ht, ht'⟩ := Finset.exists_subset_card_eq_forall_le (mean θ)
    (s := Finset.univ) (j := m) (by rwa [Finset.card_univ])
  exact ⟨t, mem_correct_epsTopMTask_of_forall_le ν mean hε ht fun a ha c hc ↦
    ht' a ha c (Finset.mem_sdiff.2 ⟨Finset.mem_univ c, hc⟩)⟩

/-- For `ε ≥ 0`, if the set `s` of `m` arms is not a correct answer of `(ε, m)`-top identification
and every mean of the set `t` of `m` arms is at least every mean outside `t`, then some arm
`b ∈ s` outside `t` has `mean θ b + ε < mean θ i` for some arm `i ∈ t` outside `s`. -/
lemma exists_add_lt_of_notMem_correct_epsTopMTask (hε : 0 ≤ ε) {s t : Finset α}
    (hs : s.card = m) (hs' : s ∉ (epsTopMTask ν mean m ε).correct θ) (ht : t.card = m)
    (ht' : ∀ a ∈ t, ∀ c ∉ t, mean θ c ≤ mean θ a) :
    ∃ b ∈ s, b ∉ t ∧ ∃ i ∈ t, i ∉ s ∧ mean θ b + ε < mean θ i := by
  classical
  set μ := mean θ
  -- An arm `b ∈ s` that is not `(ε, m)`-optimal.
  obtain ⟨b, hbs, hb⟩ : ∃ b ∈ s, m ≤ (Finset.univ.filter fun c ↦ μ b + ε < μ c).card := by
    by_contra! h
    exact hs' ⟨hs, h⟩
  -- Every arm `i ∈ t` has `μ b + ε < μ i`: otherwise the arms with mean larger than `μ b + ε`
  -- would be arms of `t` other than `i`, and there are fewer than `m` of those.
  have hlt : ∀ i ∈ t, μ b + ε < μ i := fun i hi ↦ by
    by_contra! hib
    exact (card_filter_add_lt_lt_of_mem ht ht' hi hib).not_ge hb
  have hbt : b ∉ t := fun hbt ↦ by linarith [hlt b hbt]
  -- Since `s ≠ t` have the same size, some arm of `t` is not in `s`.
  obtain ⟨i, hit, his⟩ : ∃ i ∈ t, i ∉ s := by
    by_contra! h
    exact hbt (Finset.eq_of_subset_of_card_le h (by rw [hs, ht]) ▸ hbs)
  exact ⟨b, hbs, hbt, i, hit, his, hlt i hit⟩

/-- A set of `m` arms with the largest means is a correct answer of top-`m` identification with
tolerance `ε ≥ 0`. -/
lemma correct_topMTask_subset_correct_epsTopMTask (hε : 0 ≤ ε) (θ : Θ) :
    (topMTask ν mean m).correct θ ⊆ (epsTopMTask ν mean m ε).correct θ :=
  fun _ hs ↦ mem_correct_epsTopMTask_of_forall_le ν mean hε hs.1 fun a ha c hc ↦
    (hs.2 a ha c hc).le

/-- Top-`1` identification with tolerance `ε` is `ε`-best arm identification: `{a}` is a correct
answer iff `a` is `ε`-good. -/
lemma singleton_mem_correct_epsTopMTask_one_iff {a : α} :
    {a} ∈ (epsTopMTask ν mean 1 ε).correct θ ↔ a ∈ (epsBaiTask ν mean ε).correct θ := by
  simp only [correct_epsTopMTask, Set.mem_ofPred_eq, Finset.card_singleton, Finset.mem_singleton,
    forall_eq, true_and, Nat.lt_one_iff, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    Finset.mem_univ, not_lt, forall_const, correct_epsBaiTask]

end MeanFunctional

end LMLExplore.Identification
