/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.CorrectnessOnStop
public import LMLExplore.Identification.Task.Basic

/-!
# Identification algorithms that are `δ`-correct on a task when they stop

An identification algorithm `A : IdentAlg Unit α 𝓨 ℐ` is *`δ`-correct when it stops* on an
identification task if on every admissible model `θ`, with probability at most `δ`, it stops and
outputs an answer that is not correct for `θ` [EVR26, Notes 49 and 55]; nothing is asked when it
does not stop. This is the general `LMLExplore.Identification.IsDeltaCorrectOnStop` for the
family of environments indexed by the admissible models and the badness predicate "the answer is
not correct", as `IdentTask.IsDeltaCorrect` and `IdentTask.IsDeltaPAC` are for the other
guarantees.

So `δ`-PAC implies `δ`-correct, which implies LML's PAC property at level `δ` when the sets of
correct answers are measurable, which implies `δ`-correct when it stops; and an algorithm
`δ`-correct when it stops is `δ`-PAC exactly when it stops almost surely on every admissible
model. At an admissible model with the single correct answer `i`, at which it stops almost surely,
such an algorithm stops and answers `i` with probability at least `1 - δ`, and at every
alternative to `i` with probability at most `δ`: the two facts on which the lower bounds on the
sample complexity rest.

## Main definitions

* `IdentTask.IsDeltaCorrectOnStop task A δ`: `A` is `δ`-correct on the task when it stops.

## Main statements

* `IdentTask.isDeltaCorrectOnStop_iff`: the property on the laws of the runs, quantified over the
  admissible models.
* `IdentTask.IsDeltaCorrect.isDeltaCorrectOnStop`, `IdentTask.IsDeltaPAC.isDeltaCorrectOnStop`,
  `IdentTask.isDeltaCorrectOnStop_of_isPAC`: a `δ`-correct or `δ`-PAC algorithm, or one PAC at
  level `δ` on the admissible models, is `δ`-correct when it stops.
* `IdentTask.IsDeltaCorrectOnStop.isDeltaCorrect`, `IdentTask.IsDeltaCorrectOnStop.isDeltaPAC`,
  `IdentTask.isDeltaPAC_iff_isDeltaCorrectOnStop`: an algorithm `δ`-correct when it stops that
  stops almost surely on every admissible model is `δ`-correct, and `δ`-PAC when the sets of
  correct answers are measurable.
* `IdentTask.IsDeltaCorrectOnStop.one_sub_le_measureReal_histOutputMeasure`,
  `IdentTask.IsDeltaCorrectOnStop.measureReal_histOutputMeasure_le`: an algorithm `δ`-correct when
  it stops stops and answers `i` with probability at least `1 - δ` on a model whose only correct
  answer is `i`, if it stops almost surely there, and at most `δ` on every alternative to `i`.
* `IdentTask.IsDeltaCorrectOnStop.measureReal_stoppingTime_ne_top_and_notMem_of_isRun`,
  `IdentTask.IsDeltaCorrectOnStop.one_sub_le_measureReal_of_isRun`: the properties for every run.
* `IdentTask.IsDeltaCorrectOnStop.mono`, `IdentTask.IsDeltaCorrectOnStop.restrict`,
  `IdentTask.IsDeltaCorrectOnStop.comap`, `IdentTask.isDeltaCorrectOnStop_comap_iff`:
  monotonicity in the level, and the restrictions and pullbacks of a task.

## Implementation notes

The definition is adapted from `EValuesResearch/Results/DesignExperts.lean` (commit `cb8238f`) in
the paper project `RemyDegenne/evalues_research`, rewritten on the API of
`IdentTask.IsDeltaCorrect`.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 55 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory ProbabilityTheory Learning

namespace LMLExplore.Identification.IdentTask

variable {α Θ Θ' ℐ 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  {mℐ : MeasurableSpace ℐ} {task : IdentTask α Θ ℐ 𝓨} {A : IdentAlg Unit α 𝓨 ℐ} {δ δ' : ℝ}
  {θ : Θ} {i : ℐ}

variable (task) in
/-- An identification algorithm is *`δ`-correct when it stops* on a task
[EVR26, Notes 49 and 55] if on every admissible model `θ`, with probability at most `δ`, it stops
and outputs an answer that is not correct for `θ` (see `isDeltaCorrectOnStop_iff`). Nothing is
asked when it does not stop: `IsDeltaCorrect` asks, in addition, that it stop with probability at
least `1 - δ`. -/
def IsDeltaCorrectOnStop (A : IdentAlg Unit α 𝓨 ℐ) (δ : ℝ) : Prop :=
  Identification.IsDeltaCorrectOnStop A (fun θ : task.M ↦ Environment.bandit (task.ν θ))
    (fun θ i ↦ i ∉ task.correct θ) δ

/-- `δ`-correctness when stopping on a task is the general `δ`-correctness when stopping for the
family of environments indexed by the admissible models and the badness predicate "the answer is
not correct". -/
lemma isDeltaCorrectOnStop_iff_isDeltaCorrectOnStop : task.IsDeltaCorrectOnStop A δ ↔
    Identification.IsDeltaCorrectOnStop A (fun θ : task.M ↦ Environment.bandit (task.ν θ))
      (fun θ i ↦ i ∉ task.correct θ) δ := Iff.rfl

/-- The defining property of an algorithm `δ`-correct when it stops on a task: on every
admissible model `θ`, the joint law of the stopped history and the output gives mass at most `δ`
to the event "the algorithm stops and its answer is not correct for `θ`". -/
lemma isDeltaCorrectOnStop_iff : task.IsDeltaCorrectOnStop A δ ↔
    ∀ θ ∈ task.M, (histOutputMeasure A (Environment.bandit (task.ν θ))).real
      {p | p.1 ∈ A.stopSet ∧ p.2 ∉ task.correct θ} ≤ δ :=
  Identification.isDeltaCorrectOnStop_iff.trans
    ⟨fun h θ hθ ↦ h ⟨θ, hθ⟩, fun h θ ↦ h θ θ.property⟩

/-! ### Monotonicity, restriction and pullback -/

/-- The `δ`-correctness when stopping on a task is monotone in the level. -/
lemma IsDeltaCorrectOnStop.mono (h : task.IsDeltaCorrectOnStop A δ) (hδ : δ ≤ δ') :
    task.IsDeltaCorrectOnStop A δ' :=
  Identification.IsDeltaCorrectOnStop.mono h hδ

/-- An algorithm `δ`-correct when it stops on a task is `δ`-correct when it stops on every
restriction of it. -/
lemma IsDeltaCorrectOnStop.restrict (h : task.IsDeltaCorrectOnStop A δ) (S : Set Θ) :
    (task.restrict S).IsDeltaCorrectOnStop A δ :=
  isDeltaCorrectOnStop_iff.2 fun θ hθ ↦ by
    rw [M_restrict] at hθ
    simpa using isDeltaCorrectOnStop_iff.1 h θ hθ.1

/-- An algorithm `δ`-correct when it stops on a task is `δ`-correct when it stops on its pullback
along every map of models. -/
lemma IsDeltaCorrectOnStop.comap (h : task.IsDeltaCorrectOnStop A δ) (f : Θ' → Θ) :
    (task.comap f).IsDeltaCorrectOnStop A δ :=
  isDeltaCorrectOnStop_iff.2 fun θ hθ ↦ by
    rw [M_comap] at hθ
    simpa using isDeltaCorrectOnStop_iff.1 h (f θ) hθ

/-- If every admissible model of `task` is the image of a model under `f`, an algorithm is
`δ`-correct when it stops on the pullback along `f` iff it is on `task`. -/
lemma isDeltaCorrectOnStop_comap_iff {f : Θ' → Θ} (hf : task.M ⊆ Set.range f) :
    (task.comap f).IsDeltaCorrectOnStop A δ ↔ task.IsDeltaCorrectOnStop A δ := by
  refine ⟨fun h ↦ isDeltaCorrectOnStop_iff.2 fun θ hθ ↦ ?_, fun h ↦ h.comap f⟩
  obtain ⟨θ', rfl⟩ := hf hθ
  simpa using isDeltaCorrectOnStop_iff.1 h θ' (by rwa [M_comap])

/-! ### Comparison with the other guarantees -/

/-- A `δ`-correct algorithm on a task is `δ`-correct when it stops on it. -/
lemma IsDeltaCorrect.isDeltaCorrectOnStop (h : task.IsDeltaCorrect A δ) :
    task.IsDeltaCorrectOnStop A δ :=
  (isDeltaCorrect_iff_isDeltaCorrect.1 h).isDeltaCorrectOnStop

/-- A `δ`-PAC algorithm on a task is `δ`-correct when it stops on it. -/
lemma IsDeltaPAC.isDeltaCorrectOnStop (h : task.IsDeltaPAC A δ) :
    task.IsDeltaCorrectOnStop A δ :=
  (isDeltaPAC_iff_isDeltaPAC.1 h).isDeltaCorrectOnStop

/-- An algorithm PAC at level `δ` on the admissible models of a task is `δ`-correct when it stops
on it. -/
lemma isDeltaCorrectOnStop_of_isPAC
    (h : A.IsPAC (fun θ : task.M ↦ Environment.bandit (task.ν θ)) (fun θ i ↦ i ∉ task.correct θ)
      δ) :
    task.IsDeltaCorrectOnStop A δ :=
  h.isDeltaCorrectOnStop

/-- An algorithm `δ`-correct when it stops on a task, that stops almost surely on every
admissible model, is `δ`-correct on it. -/
lemma IsDeltaCorrectOnStop.isDeltaCorrect (h : task.IsDeltaCorrectOnStop A δ)
    (h_stop : ∀ θ ∈ task.M, StopsAS A (Environment.bandit (task.ν θ))) :
    task.IsDeltaCorrect A δ :=
  isDeltaCorrect_iff_isDeltaCorrect.2 <|
    Identification.IsDeltaCorrectOnStop.isDeltaCorrect h fun θ ↦ h_stop θ θ.property

/-- An algorithm `δ`-correct when it stops on a task whose sets of correct answers are
measurable, that stops almost surely on every admissible model, is `δ`-PAC on it. -/
lemma IsDeltaCorrectOnStop.isDeltaPAC (h : task.IsDeltaCorrectOnStop A δ)
    (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (h_stop : ∀ θ ∈ task.M, StopsAS A (Environment.bandit (task.ν θ))) :
    task.IsDeltaPAC A δ :=
  isDeltaPAC_of_measureReal_mem_stopSet_and_notMem_le hc (isDeltaCorrectOnStop_iff.1 h) h_stop

/-- On a task whose sets of correct answers are measurable, an algorithm is `δ`-PAC exactly when
it is `δ`-correct when it stops and stops almost surely on every admissible model. -/
lemma isDeltaPAC_iff_isDeltaCorrectOnStop (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ)) :
    task.IsDeltaPAC A δ ↔ task.IsDeltaCorrectOnStop A δ ∧
      ∀ θ ∈ task.M, StopsAS A (Environment.bandit (task.ν θ)) :=
  ⟨fun h ↦ ⟨h.isDeltaCorrectOnStop, fun _ hθ ↦ h.stopsAS hθ⟩,
    fun h ↦ h.1.isDeltaPAC hc h.2⟩

/-! ### Stopping with a given answer -/

/-- On every alternative to the answer `i`, an algorithm `δ`-correct when it stops stops and
answers `i` with probability at most `δ`. -/
lemma IsDeltaCorrectOnStop.measureReal_histOutputMeasure_le (h : task.IsDeltaCorrectOnStop A δ)
    (hθ : θ ∈ task.alt i) :
    (histOutputMeasure A (Environment.bandit (task.ν θ))).real {p | p.1 ∈ A.stopSet ∧ p.2 = i}
      ≤ δ :=
  (isDeltaCorrectOnStop_iff.1 h θ (task.mem_alt_iff.1 hθ).1).trans' <|
    measureReal_mono fun p hp ↦ ⟨hp.1, hp.2 ▸ (task.mem_alt_iff.1 hθ).2⟩

/-- If `i` is the only correct answer of an admissible model `θ` on which it stops almost surely,
an algorithm `δ`-correct when it stops stops and answers `i` on `θ` with probability at least
`1 - δ`. -/
lemma IsDeltaCorrectOnStop.one_sub_le_measureReal_histOutputMeasure
    (h : task.IsDeltaCorrectOnStop A δ) (hθ : θ ∈ task.M) (hi : task.correct θ = {i})
    (h_stop : StopsAS A (Environment.bandit (task.ν θ))) :
    1 - δ ≤ (histOutputMeasure A (Environment.bandit (task.ν θ))).real
      {p | p.1 ∈ A.stopSet ∧ p.2 = i} := by
  simpa [hi] using Identification.IsDeltaCorrectOnStop.one_sub_le_measureReal_histOutputMeasure
    (θ := ⟨θ, hθ⟩) h h_stop

/-! ### Runs -/

section Run

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨} {out : Ω → ℐ}

/-- Along every run of an algorithm `δ`-correct when it stops on an admissible model `θ`, with
probability at most `δ` the algorithm stops and its answer is not correct for `θ`. -/
lemma IsDeltaCorrectOnStop.measureReal_stoppingTime_ne_top_and_notMem_of_isRun
    (h : task.IsDeltaCorrectOnStop A δ) (hθ : θ ∈ task.M) (hc : MeasurableSet (task.correct θ))
    (hrun : A.IsRun (Environment.bandit (task.ν θ)) O X Y out P) :
    P.real {ω | A.stoppingTime O X Y ω ≠ ⊤ ∧ out ω ∉ task.correct θ} ≤ δ :=
  Identification.IsDeltaCorrectOnStop.measureReal_stoppingTime_ne_top_and_bad_of_isRun
    (θ := ⟨θ, hθ⟩) h hc.compl hrun

/-- Along every run of an algorithm `δ`-correct when it stops on an admissible model `θ` on which
it stops almost surely, with probability at least `1 - δ` the algorithm stops and its answer is
correct for `θ`. -/
lemma IsDeltaCorrectOnStop.one_sub_le_measureReal_of_isRun (h : task.IsDeltaCorrectOnStop A δ)
    (hθ : θ ∈ task.M) (hc : MeasurableSet (task.correct θ))
    (h_stop : StopsAS A (Environment.bandit (task.ν θ)))
    (hrun : A.IsRun (Environment.bandit (task.ν θ)) O X Y out P) :
    1 - δ ≤ P.real {ω | A.stoppingTime O X Y ω ≠ ⊤ ∧ out ω ∈ task.correct θ} := by
  simpa using Identification.IsDeltaCorrectOnStop.one_sub_le_measureReal_of_isRun
    (θ := ⟨θ, hθ⟩) h hc.compl h_stop hrun

end Run

end LMLExplore.Identification.IdentTask
