/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Correctness
public import LeanMachineLearning.SequentialLearning.StationaryEnv

/-!
# Identification tasks

An identification task specifies what an identification algorithm must find out about an unknown
stochastic bandit with arms `α` and observations in `𝓨`. It consists of

* a type `Θ` of models, and for each model `θ` a bandit `ν θ : Kernel α 𝓨` (a Markov kernel: arm
  `a` returns an observation with law `ν θ a`);
* a set `M : Set Θ` of admissible models, the models on which the algorithm is evaluated;
* a type `ℐ` of answers and, for each model, the set `correct θ` of its correct answers.

Several answers may be correct for the same model, as in Degenne and Koolen (2019); a
*single-answer* task has exactly one correct answer on every admissible model. Models are not
required to be vectors of means: vectors of means, parameters of linear models and pairs
(mean, variance) are all models. The classical tasks on vectors of means are in
`LMLExplore.Identification.Task.MeanVector`.

An identification algorithm `A : IdentAlg Unit α 𝓨 ℐ` interacts with the model `θ` through the
stationary environment `stationaryEnv (task.ν θ)`. It is `δ`-correct on the task if on every
admissible model, with probability at least `1 - δ`, it stops and outputs a correct answer, and
`δ`-PAC if moreover it stops almost surely on every admissible model. These are the general
notions `LMLExplore.Identification.IsDeltaCorrect` and `LMLExplore.Identification.IsDeltaPAC`
for the family of environments indexed by the admissible models and the badness predicate "the
answer is not correct".

## Main definitions

* `LMLExplore.Identification.IdentTask α Θ ℐ 𝓨`: identification tasks.
* `IdentTask.alt task i`: the alternatives `¬i` to the answer `i`, the admissible models for which
  `i` is not correct.
* `IdentTask.answerSet task i`: the admissible models for which `i` is correct.
* `IdentTask.IsSingleAnswer task`: every admissible model has exactly one correct answer.
* `IdentTask.restrict task S`: the task with admissible models `task.M ∩ S`.
* `IdentTask.IsDeltaCorrect task A δ`, `IdentTask.IsDeltaPAC task A δ`: `δ`-correct and `δ`-PAC
  algorithms for the task.

## Main statements

* `IdentTask.alt_union_answerSet`, `IdentTask.disjoint_alt_answerSet`: the alternatives to `i` and
  the models for which `i` is correct partition the admissible models.
* `IdentTask.IsSingleAnswer.correct_eq_singleton_of_mem`: for a single-answer task, a correct
  answer of an admissible model is its only correct answer.
* `IdentTask.IsSingleAnswer.mem_alt_iff`: for a single-answer task, an admissible model is an
  alternative to `j` iff `j` is not its answer.
* `IdentTask.isDeltaCorrect_iff`, `IdentTask.isDeltaPAC_iff`: the properties on the laws of the
  runs, quantified over the admissible models.
* `IdentTask.IsDeltaPAC.isDeltaCorrect`, `IdentTask.IsDeltaCorrect.isPAC`: `δ`-PAC implies
  `δ`-correct, which implies LML's PAC property at level `δ`.
* `IdentTask.IsDeltaCorrect.one_sub_le_measureReal_histOutputMeasure`,
  `IdentTask.IsDeltaCorrect.measureReal_histOutputMeasure_le`: a `δ`-correct algorithm stops and
  answers `i` with probability at least `1 - δ` on a model whose only correct answer is `i`, and
  at most `δ` on every alternative to `i`.
* `IdentTask.IsDeltaCorrect.one_sub_le_measureReal_of_isRun`: along every run on an admissible
  model, a `δ`-correct algorithm stops with a correct answer with probability at least `1 - δ`.

## References

* R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*, NeurIPS 2019.
* A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016.
-/

public section

open MeasureTheory ProbabilityTheory Learning

namespace LMLExplore.Identification

/-- An identification task on a bandit with arms `α` and observations in `𝓨`: models `Θ`, each
with a bandit `ν θ`, a set `M` of admissible models, and the set `correct θ ⊆ ℐ` of correct
answers of each model. -/
@[ext]
structure IdentTask (α Θ ℐ 𝓨 : Type*) [MeasurableSpace α] [MeasurableSpace 𝓨] where
  /-- The admissible models. -/
  M : Set Θ
  /-- The bandit of each model: arm `a` returns an observation with law `ν θ a`. -/
  ν : Θ → Kernel α 𝓨
  /-- The bandit of each model is a Markov kernel. -/
  isMarkovKernel_ν : ∀ θ, IsMarkovKernel (ν θ)
  /-- The correct answers of each model. -/
  correct : Θ → Set ℐ

namespace IdentTask

variable {α Θ ℐ 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (task : IdentTask α Θ ℐ 𝓨) {θ : Θ} {i j : ℐ}

instance (θ : Θ) : IsMarkovKernel (task.ν θ) := task.isMarkovKernel_ν θ

/-! ### Alternatives and answer sets -/

/-- The alternatives `¬i` to the answer `i`: the admissible models for which `i` is not a correct
answer. -/
def alt (i : ℐ) : Set Θ := {θ | θ ∈ task.M ∧ i ∉ task.correct θ}

/-- The admissible models for which `i` is a correct answer. -/
def answerSet (i : ℐ) : Set Θ := {θ | θ ∈ task.M ∧ i ∈ task.correct θ}

@[simp]
lemma mem_alt_iff : θ ∈ task.alt i ↔ θ ∈ task.M ∧ i ∉ task.correct θ := Iff.rfl

@[simp]
lemma mem_answerSet_iff : θ ∈ task.answerSet i ↔ θ ∈ task.M ∧ i ∈ task.correct θ := Iff.rfl

lemma alt_subset_M (i : ℐ) : task.alt i ⊆ task.M := fun _ h ↦ h.1

lemma answerSet_subset_M (i : ℐ) : task.answerSet i ⊆ task.M := fun _ h ↦ h.1

/-- An admissible model is not an alternative to `i` iff `i` is one of its correct answers. -/
lemma notMem_alt_iff (hθ : θ ∈ task.M) : θ ∉ task.alt i ↔ i ∈ task.correct θ := by
  simp [hθ]

/-- The alternatives to `i` are the admissible models for which `i` is not correct. -/
lemma M_diff_answerSet (i : ℐ) : task.M \ task.answerSet i = task.alt i := by
  ext θ
  simp +contextual

lemma disjoint_alt_answerSet (i : ℐ) : Disjoint (task.alt i) (task.answerSet i) :=
  Set.disjoint_left.2 fun _ h h' ↦ h.2 h'.2

/-- The alternatives to `i` and the models for which `i` is correct cover the admissible models. -/
lemma alt_union_answerSet (i : ℐ) : task.alt i ∪ task.answerSet i = task.M := by
  rw [← M_diff_answerSet, Set.sdiff_union_of_subset (task.answerSet_subset_M i)]

/-! ### Single-answer tasks -/

/-- A *single-answer* task: every admissible model has exactly one correct answer. -/
def IsSingleAnswer : Prop := ∀ θ ∈ task.M, ∃ i, task.correct θ = {i}

lemma isSingleAnswer_iff : task.IsSingleAnswer ↔ ∀ θ ∈ task.M, ∃ i, task.correct θ = {i} :=
  Iff.rfl

variable {task}

/-- If the correct answer of the admissible model `θ` is `i`, then `θ` is an alternative to every
other answer. -/
lemma mem_alt_of_correct_eq_singleton (hθ : θ ∈ task.M) (hi : task.correct θ = {i})
    (hj : j ≠ i) : θ ∈ task.alt j := by
  simp [hθ, hi, hj]

/-- For a single-answer task, a correct answer `i` of an admissible model is its only correct
answer. -/
lemma IsSingleAnswer.correct_eq_singleton_of_mem (h : task.IsSingleAnswer) (hθ : θ ∈ task.M)
    (hi : i ∈ task.correct θ) : task.correct θ = {i} := by
  obtain ⟨i', hi'⟩ := h θ hθ
  rw [hi', Set.mem_singleton_iff] at hi
  rwa [hi]

/-- For a single-answer task, an admissible model with correct answer `i` is an alternative to
`j` iff `j ≠ i`. -/
lemma IsSingleAnswer.mem_alt_iff (h : task.IsSingleAnswer) (hθ : θ ∈ task.M)
    (hi : i ∈ task.correct θ) : θ ∈ task.alt j ↔ j ≠ i := by
  simp [hθ, h.correct_eq_singleton_of_mem hθ hi]

/-! ### Restriction of the admissible models -/

variable (task) in
/-- The task with the same models, bandits and correct answers as `task` and the admissible models
`task.M ∩ S`. -/
def restrict (S : Set Θ) : IdentTask α Θ ℐ 𝓨 where
  M := task.M ∩ S
  ν := task.ν
  isMarkovKernel_ν := task.isMarkovKernel_ν
  correct := task.correct

variable {S : Set Θ}

@[simp]
lemma M_restrict : (task.restrict S).M = task.M ∩ S := (rfl)

@[simp]
lemma ν_restrict : (task.restrict S).ν = task.ν := (rfl)

@[simp]
lemma correct_restrict : (task.restrict S).correct = task.correct := (rfl)

@[simp]
lemma restrict_restrict (S T : Set Θ) : (task.restrict S).restrict T = task.restrict (S ∩ T) := by
  ext <;> simp [Set.inter_assoc]

variable (task) in
@[simp]
lemma restrict_univ : task.restrict Set.univ = task := by
  ext <;> simp

@[simp]
lemma alt_restrict (i : ℐ) : (task.restrict S).alt i = task.alt i ∩ S := by
  ext θ
  simp only [mem_alt_iff, M_restrict, correct_restrict, Set.mem_inter_iff]
  tauto

@[simp]
lemma answerSet_restrict (i : ℐ) : (task.restrict S).answerSet i = task.answerSet i ∩ S := by
  ext θ
  simp only [mem_answerSet_iff, M_restrict, correct_restrict, Set.mem_inter_iff]
  tauto

lemma IsSingleAnswer.restrict (h : task.IsSingleAnswer) (S : Set Θ) :
    (task.restrict S).IsSingleAnswer :=
  fun θ hθ ↦ h θ hθ.1

/-! ### `δ`-correct and `δ`-PAC algorithms for a task -/

variable [MeasurableSpace ℐ] {A : IdentAlg Unit α 𝓨 ℐ} {δ δ' : ℝ}

variable (task) in
/-- An identification algorithm is *`δ`-correct* on a task (Degenne–Koolen 2019) if on every
admissible model `θ`, with probability at least `1 - δ`, it stops and outputs a correct answer of
`θ` (see `isDeltaCorrect_iff`). -/
def IsDeltaCorrect (A : IdentAlg Unit α 𝓨 ℐ) (δ : ℝ) : Prop :=
  Identification.IsDeltaCorrect A (fun θ : task.M ↦ stationaryEnv (task.ν θ))
    (fun θ i ↦ i ∉ task.correct θ) δ

variable (task) in
/-- An identification algorithm is *`δ`-PAC* on a task if on every admissible model it outputs
a correct answer with probability at least `1 - δ` and it stops almost surely (see
`isDeltaPAC_iff`). -/
def IsDeltaPAC (A : IdentAlg Unit α 𝓨 ℐ) (δ : ℝ) : Prop :=
  Identification.IsDeltaPAC A (fun θ : task.M ↦ stationaryEnv (task.ν θ))
    (fun θ i ↦ i ∉ task.correct θ) δ

/-- `δ`-correctness on a task is the general `δ`-correctness for the family of environments
indexed by the admissible models and the badness predicate "the answer is not correct". -/
lemma isDeltaCorrect_iff_isDeltaCorrect : task.IsDeltaCorrect A δ ↔
    Identification.IsDeltaCorrect A (fun θ : task.M ↦ stationaryEnv (task.ν θ))
      (fun θ i ↦ i ∉ task.correct θ) δ := Iff.rfl

/-- `δ`-PAC on a task is the general `δ`-PAC property for the family of environments indexed by
the admissible models and the badness predicate "the answer is not correct". -/
lemma isDeltaPAC_iff_isDeltaPAC : task.IsDeltaPAC A δ ↔
    Identification.IsDeltaPAC A (fun θ : task.M ↦ stationaryEnv (task.ν θ))
      (fun θ i ↦ i ∉ task.correct θ) δ := Iff.rfl

/-- The defining property of a `δ`-correct algorithm on a task: on every admissible model `θ`,
the joint law of the stopped history and the output gives mass at most `δ` to the event "the
algorithm does not stop or its answer is not correct for `θ`". -/
lemma isDeltaCorrect_iff : task.IsDeltaCorrect A δ ↔
    ∀ θ ∈ task.M, (histOutputMeasure A (stationaryEnv (task.ν θ))).real
      {p | p.1 ∉ A.stopSet ∨ p.2 ∉ task.correct θ} ≤ δ :=
  Identification.isDeltaCorrect_iff.trans
    ⟨fun h θ hθ ↦ h ⟨θ, hθ⟩, fun h θ ↦ h θ θ.2⟩

/-- The defining property of a `δ`-PAC algorithm on a task: on every admissible model `θ`, its
answer is not correct for `θ` with probability at most `δ`, and it stops almost surely. -/
lemma isDeltaPAC_iff : task.IsDeltaPAC A δ ↔
    (∀ θ ∈ task.M, (A.outputMeasure (stationaryEnv (task.ν θ))).real
      {i | i ∉ task.correct θ} ≤ δ) ∧
    ∀ θ ∈ task.M, StopsAS A (stationaryEnv (task.ν θ)) :=
  Identification.isDeltaPAC_iff.trans
    ⟨fun h ↦ ⟨fun θ hθ ↦ h.1 ⟨θ, hθ⟩, fun θ hθ ↦ h.2 ⟨θ, hθ⟩⟩,
      fun h ↦ ⟨fun θ ↦ h.1 θ θ.2, fun θ ↦ h.2 θ θ.2⟩⟩

/-- If `i` is the only correct answer of an admissible model `θ`, a `δ`-correct algorithm stops
and answers `i` on `θ` with probability at least `1 - δ`. -/
lemma IsDeltaCorrect.one_sub_le_measureReal_histOutputMeasure [MeasurableSingletonClass ℐ]
    (h : task.IsDeltaCorrect A δ) (hθ : θ ∈ task.M) (hi : task.correct θ = {i}) :
    1 - δ ≤ (histOutputMeasure A (stationaryEnv (task.ν θ))).real
      {p | p.1 ∈ A.stopSet ∧ p.2 = i} := by
  have hE : MeasurableSet {p : (Σ n : ℕ, Hist Unit α 𝓨 n) × ℐ | p.1 ∈ A.stopSet ∧ p.2 = i} :=
    (measurable_fst A.measurableSet_stopSet).inter (measurable_snd (measurableSet_singleton i))
  have h_compl : {p : (Σ n : ℕ, Hist Unit α 𝓨 n) × ℐ | p.1 ∈ A.stopSet ∧ p.2 = i}ᶜ =
      {p | p.1 ∉ A.stopSet ∨ p.2 ∉ task.correct θ} := by
    ext p
    simp [hi, imp_iff_not_or]
  have h_bad := isDeltaCorrect_iff.1 h θ hθ
  rw [← h_compl, probReal_compl_eq_one_sub hE] at h_bad
  linarith

/-- On every alternative to the answer `i`, a `δ`-correct algorithm stops and answers `i` with
probability at most `δ`. -/
lemma IsDeltaCorrect.measureReal_histOutputMeasure_le (h : task.IsDeltaCorrect A δ)
    (hθ : θ ∈ task.alt i) :
    (histOutputMeasure A (stationaryEnv (task.ν θ))).real {p | p.1 ∈ A.stopSet ∧ p.2 = i} ≤ δ :=
  (measureReal_mono fun p hp ↦ Or.inr (hp.2 ▸ hθ.2)).trans (isDeltaCorrect_iff.1 h θ hθ.1)

/-- A `δ`-PAC algorithm on a task stops almost surely on every admissible model. -/
lemma IsDeltaPAC.stopsAS (h : task.IsDeltaPAC A δ) (hθ : θ ∈ task.M) :
    StopsAS A (stationaryEnv (task.ν θ)) :=
  (isDeltaPAC_iff.1 h).2 θ hθ

/-- A `δ`-PAC algorithm on a task is `δ`-correct on it. -/
lemma IsDeltaPAC.isDeltaCorrect (h : task.IsDeltaPAC A δ) : task.IsDeltaCorrect A δ :=
  Identification.IsDeltaPAC.isDeltaCorrect h

/-- A `δ`-correct algorithm on a task whose sets of correct answers are measurable is PAC at
level `δ` on the admissible models. -/
lemma IsDeltaCorrect.isPAC (h : task.IsDeltaCorrect A δ)
    (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ)) :
    A.IsPAC (fun θ : task.M ↦ stationaryEnv (task.ν θ)) (fun θ i ↦ i ∉ task.correct θ) δ :=
  Identification.IsDeltaCorrect.isPAC h fun θ ↦ (hc θ θ.2).compl

lemma IsDeltaCorrect.mono (h : task.IsDeltaCorrect A δ) (hδ : δ ≤ δ') :
    task.IsDeltaCorrect A δ' :=
  Identification.IsDeltaCorrect.mono h hδ

lemma IsDeltaPAC.mono (h : task.IsDeltaPAC A δ) (hδ : δ ≤ δ') : task.IsDeltaPAC A δ' :=
  Identification.IsDeltaPAC.mono h hδ

/-- A `δ`-correct algorithm on a task is `δ`-correct on every restriction of it. -/
lemma IsDeltaCorrect.restrict (h : task.IsDeltaCorrect A δ) (S : Set Θ) :
    (task.restrict S).IsDeltaCorrect A δ :=
  Identification.IsDeltaCorrect.comp h (Set.inclusion Set.inter_subset_left)

/-- A `δ`-PAC algorithm on a task is `δ`-PAC on every restriction of it. -/
lemma IsDeltaPAC.restrict (h : task.IsDeltaPAC A δ) (S : Set Θ) :
    (task.restrict S).IsDeltaPAC A δ :=
  Identification.IsDeltaPAC.comp h (Set.inclusion Set.inter_subset_left)

section Run

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨} {out : Ω → ℐ}

/-- Along every run of a `δ`-correct algorithm on an admissible model `θ`, with probability at
most `δ` the algorithm does not stop or its answer is not correct for `θ`. -/
lemma IsDeltaCorrect.measureReal_stoppingTime_eq_top_or_notMem_of_isRun
    (h : task.IsDeltaCorrect A δ) (hθ : θ ∈ task.M) (hc : MeasurableSet (task.correct θ))
    (hrun : A.IsRun (stationaryEnv (task.ν θ)) O X Y out P) :
    P.real {ω | A.stoppingTime O X Y ω = ⊤ ∨ out ω ∉ task.correct θ} ≤ δ :=
  Identification.IsDeltaCorrect.measureReal_stoppingTime_eq_top_or_bad_of_isRun
    (θ := ⟨θ, hθ⟩) h hc.compl hrun

/-- Along every run of a `δ`-correct algorithm on an admissible model `θ`, with probability at
least `1 - δ` the algorithm stops and its answer is correct for `θ`. -/
lemma IsDeltaCorrect.one_sub_le_measureReal_of_isRun (h : task.IsDeltaCorrect A δ)
    (hθ : θ ∈ task.M) (hc : MeasurableSet (task.correct θ))
    (hrun : A.IsRun (stationaryEnv (task.ν θ)) O X Y out P) :
    1 - δ ≤ P.real {ω | A.stoppingTime O X Y ω ≠ ⊤ ∧ out ω ∈ task.correct θ} := by
  simpa using Identification.IsDeltaCorrect.one_sub_le_measureReal_of_isRun
    (θ := ⟨θ, hθ⟩) h hc.compl hrun

/-- Along every run of a `δ`-PAC algorithm on an admissible model, the stopping time is almost
surely finite. -/
lemma IsDeltaPAC.ae_stoppingTime_ne_top_of_isRun (h : task.IsDeltaPAC A δ) (hθ : θ ∈ task.M)
    (hrun : A.IsRun (stationaryEnv (task.ν θ)) O X Y out P) :
    ∀ᵐ ω ∂P, A.stoppingTime O X Y ω ≠ ⊤ :=
  (h.stopsAS hθ).ae_stoppingTime_ne_top hrun.isAlgEnvSeq

end Run

end IdentTask

end LMLExplore.Identification
