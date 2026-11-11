/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.Basic

/-!
# Measurable recommendation rules from the answer sets

A fixed-budget identification algorithm, such as a static proportions algorithm, ends by
recommending the answer `rec x` at the vector `x` of the empirical means, for a recommendation rule
`rec`. For a task asking about the means `mean θ` of its models, the empirical means converge to
`mean θ`, and the natural rule recommends the answer `i` at every point `x` that is a limit of means
of models with correct answer `i` but not a limit of means of alternatives to `i`:
`x ∈ closure (mean '' 𝒟_i)` and `x ∉ closure (mean '' ¬i)`. For a single-answer task, at most one
answer `i` has this property at each `x`, and some measurable rule has it everywhere. Such a rule
extends the correct answer function `i*` beyond the means of the admissible models, and it is the
recommendation rule with which [D23, proof of Theorem 1] builds static proportions algorithms
attaining the static error exponent. The rule is prescribed also at limits of means of admissible
models that are not themselves such means, as the empirical means `(1, 0, …, 0)` of Bernoulli arms
for best arm identification on the means `(0, 1)^K`, where it must recommend the first arm.

The means take values in any topological space `X` whose σ-algebra contains the open sets (in
[D23], the vectors of means `α → ℝ`, with `mean = id` on the models `α → ℝ`).

## Main statements

* `IdentTask.IsSingleAnswer.eq_of_mem_closure_image_answerSet_of_notMem_closure_image_alt`: for a
  single-answer task, a limit of means of models with correct answer `i` that is not a limit of
  means of alternatives to `j` has `i = j`.
* `IdentTask.IsSingleAnswer.mem_closure_image_answerSet_of_mem_closure`: with finitely many
  answers, if the closures of the means of the answer sets cover `S`, then every point of the
  closure of `S` that is not a limit of means of alternatives to `i` is a limit of means of models
  with correct answer `i`.
* `IdentTask.IsSingleAnswer.exists_measurable_rec`: for a single-answer task with countably many
  answers, a measurable recommendation rule that recommends `i` at the limits of means of models
  with correct answer `i` that are not limits of means of alternatives to `i`
  [D23, proof of Theorem 1].
* `IdentTask.apply_mean_eq_of_mem_answerSet`: such a rule recommends `i` at the means of the
  models with correct answer `i` when these means form an open set disjoint from the means of the
  alternatives to `i`.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
* Adapted from the formalization of [D23] in the project `RemyDegenne/Degenne2023Existence`
  (file `D2023/Theorem1.lean`).
-/

public section

open MeasureTheory

namespace LMLExplore.Identification.IdentTask

variable {α Θ ℐ 𝓨 X : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  [TopologicalSpace X] {task : IdentTask α Θ ℐ 𝓨} {mean : Θ → X} {θ : Θ} {i j : ℐ}

/-- For a single-answer task, if a point `x` is a limit of means of models with correct answer `i`
and is not a limit of means of alternatives to `j`, then `i = j`: for `i ≠ j`, the models with
correct answer `i` are alternatives to `j`. -/
lemma IsSingleAnswer.eq_of_mem_closure_image_answerSet_of_notMem_closure_image_alt
    (h : task.IsSingleAnswer) {x : X} (hi : x ∈ closure (mean '' task.answerSet i))
    (hj : x ∉ closure (mean '' task.alt j)) : i = j := by
  by_contra hij
  refine hj (closure_mono (Set.image_mono fun θ hθ ↦ ?_) hi)
  obtain ⟨hθM, hθi⟩ := task.mem_answerSet_iff.1 hθ
  exact (h.mem_alt_iff hθM hθi).2 (Ne.symm hij)

/-- For a single-answer task with finitely many answers, if the closures of the means of the answer
sets cover the set `S`, then every point of the closure of `S` that is not a limit of means of
alternatives to `i` is a limit of means of models with correct answer `i`. In [D23], `S` is the set
of the vectors of means of the exponential families of the arms, whose closure contains the vectors
of the empirical means. -/
lemma IsSingleAnswer.mem_closure_image_answerSet_of_mem_closure [Finite ℐ]
    (h : task.IsSingleAnswer) {S : Set X} (hS : S ⊆ ⋃ k, closure (mean '' task.answerSet k))
    {x : X} (hx : x ∈ closure S) (hi : x ∉ closure (mean '' task.alt i)) :
    x ∈ closure (mean '' task.answerSet i) := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1
    (closure_minimal hS (isClosed_iUnion_of_finite fun _ ↦ isClosed_closure) hx)
  rwa [← h.eq_of_mem_closure_image_answerSet_of_notMem_closure_image_alt hk hi]

variable (mean) in
/-- **A measurable recommendation rule** [D23, proof of Theorem 1]. For a single-answer task with
countably many answers and means in a space whose σ-algebra contains the open sets, some measurable
rule `rec` recommends the answer `i` at every limit of means of models with correct answer `i` that
is not a limit of means of alternatives to `i`. Such a point determines `i`
(`IsSingleAnswer.eq_of_mem_closure_image_answerSet_of_notMem_closure_image_alt`); the rule is not
constrained at the other points. -/
theorem IsSingleAnswer.exists_measurable_rec [MeasurableSpace ℐ] [Countable ℐ] [Nonempty ℐ]
    [MeasurableSpace X] [OpensMeasurableSpace X] (h : task.IsSingleAnswer) :
    ∃ rec : X → ℐ, Measurable rec ∧ ∀ i, ∀ x ∈ closure (mean '' task.answerSet i),
      x ∉ closure (mean '' task.alt i) → rec x = i := by
  classical
  -- `P i` is the set of the points at which the rule must recommend `i`.
  set P : ℐ → Set X := fun i ↦ closure (mean '' task.answerSet i) \ closure (mean '' task.alt i)
  have hP (i : ℐ) : MeasurableSet (P i) :=
    isClosed_closure.measurableSet.diff isClosed_closure.measurableSet
  have huniq {i j : ℐ} {x : X} (hi : x ∈ P i) (hj : x ∈ P j) : i = j :=
    h.eq_of_mem_closure_image_answerSet_of_notMem_closure_image_alt hi.1 hj.2
  set i₀ : ℐ := Classical.arbitrary ℐ
  set rec : X → ℐ := fun x ↦ if hx : ∃ i, x ∈ P i then hx.choose else i₀
  have hrec {i : ℐ} {x : X} (hx : x ∈ P i) : rec x = i := by
    have hex : ∃ i, x ∈ P i := ⟨i, hx⟩
    simp only [rec, dite_eq_left hex]
    exact huniq hex.choose_spec hx
  refine ⟨rec, measurable_to_countable' fun i ↦ ?_, fun i x hx hxi ↦ hrec ⟨hx, hxi⟩⟩
  -- The rule recommends `i` on `P i`, and on the complement of all the `P j` if `i₀ = i`.
  have hpre : rec ⁻¹' {i} = P i ∪ ((⋃ j, P j)ᶜ ∩ {_x | i₀ = i}) := by
    ext x
    by_cases hx : ∃ j, x ∈ P j
    · obtain ⟨j, hj⟩ := hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hrec hj]
      refine ⟨fun hji ↦ .inl (hji ▸ hj), ?_⟩
      rintro (hi | ⟨hU, -⟩)
      exacts [huniq hj hi, absurd (Set.mem_iUnion.2 ⟨j, hj⟩) hU]
    · have hx₀ : rec x = i₀ := by simp only [rec, dite_eq_right hx]
      simp [hx₀, not_exists.1 hx]
  rw [hpre]
  exact (hP i).union ((MeasurableSet.iUnion hP).compl.inter (MeasurableSet.const _))

/-- Let the rule `rec` recommend the answer `i` at every limit of means of models with correct
answer `i` that is not a limit of means of alternatives to `i`, as the rule of
`IsSingleAnswer.exists_measurable_rec`. If the means of the models with correct answer `i` form an
open set disjoint from the means of the alternatives to `i`, then `rec` recommends `i` at the mean
of every model with correct answer `i`. For a task on the vectors of means (`mean = id`), the
disjointness always holds, and the openness is that of the answer set of `i`. -/
lemma apply_mean_eq_of_mem_answerSet {rec : X → ℐ}
    (hrec : ∀ x ∈ closure (mean '' task.answerSet i), x ∉ closure (mean '' task.alt i) →
      rec x = i)
    (hopen : IsOpen (mean '' task.answerSet i))
    (hdisj : Disjoint (mean '' task.answerSet i) (mean '' task.alt i))
    (hθ : θ ∈ task.answerSet i) :
    rec (mean θ) = i := by
  have hmem : mean θ ∈ mean '' task.answerSet i := Set.mem_image_of_mem mean hθ
  exact hrec _ (subset_closure hmem) (Set.disjoint_left.1 (hdisj.closure_right hopen) hmem)

end LMLExplore.Identification.IdentTask
