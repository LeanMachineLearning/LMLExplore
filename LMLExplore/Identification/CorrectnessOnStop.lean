/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.Correctness

/-!
# Identification algorithms that are `δ`-correct when they stop

An identification algorithm `A` is *`δ`-correct when it stops* for a family of environments
`env θ` and a badness predicate `bad θ` if, for every `θ`, the probability that `A` stops in
`env θ` with an output that is `bad θ` is at most `δ` [EVR26, Notes 49 and 55]. Nothing is asked
when `A` does not stop: an algorithm that never stops is `δ`-correct when it stops for every
`δ ≥ 0`. This is the guarantee of an algorithm that stops only on enough evidence and need not
gather it in every environment, such as the algorithm that learns the design of
[EVR26, Note 49], which need not stop at a model where its experts do not determine the rate of
the designs.

The guarantee is the weakest of four. A `δ`-PAC algorithm (`LMLExplore.Identification.IsDeltaPAC`)
is `δ`-correct (`LMLExplore.Identification.IsDeltaCorrect`); a `δ`-correct algorithm is PAC at
level `δ` (`Learning.IdentAlg.IsPAC`) when the badness predicate is measurable; and an algorithm
PAC at level `δ` is `δ`-correct when it stops. Conversely, an algorithm `δ`-correct when it stops
that stops almost surely in every environment of the family is `δ`-correct, and `δ`-PAC when the
badness predicate is measurable. As for the other guarantees, the property is stated on the laws
of the runs, here the joint law `histOutputMeasure A (env θ)` of the stopped history and the
output, and it comes with its statements about every run of the algorithm.

## Main definitions

* `LMLExplore.Identification.IsDeltaCorrectOnStop A env bad δ`: for every `θ`, with probability
  at most `δ`, `A` stops in `env θ` and its output is `bad θ`.

## Main statements

* `Learning.IdentAlg.IsPAC.isDeltaCorrectOnStop`,
  `LMLExplore.Identification.IsDeltaCorrect.isDeltaCorrectOnStop`,
  `LMLExplore.Identification.IsDeltaPAC.isDeltaCorrectOnStop`: an algorithm PAC at level `δ`,
  `δ`-correct or `δ`-PAC is `δ`-correct when it stops.
* `LMLExplore.Identification.IsDeltaCorrectOnStop.isDeltaCorrect`,
  `LMLExplore.Identification.IsDeltaCorrectOnStop.isDeltaPAC`,
  `LMLExplore.Identification.isDeltaPAC_iff_isDeltaCorrectOnStop`: an algorithm `δ`-correct when
  it stops that stops almost surely in every environment is `δ`-correct, and `δ`-PAC for a
  measurable badness predicate; a `δ`-PAC algorithm is exactly one that is `δ`-correct when it
  stops and stops almost surely in every environment.
* `LMLExplore.Identification.StopsAS.measureReal_notMem_stopSet_or_eq`: if `A` stops almost
  surely, not stopping does not contribute to the probability of an event of the output.
* `LMLExplore.Identification.IsDeltaCorrectOnStop.one_sub_le_measureReal_histOutputMeasure`: an
  algorithm `δ`-correct when it stops that stops almost surely in `env θ` stops there with an
  output that is not `bad θ` with probability at least `1 - δ`.
* `LMLExplore.Identification.IsDeltaCorrectOnStop.measureReal_stoppingTime_ne_top_and_bad_of_isRun`,
  `LMLExplore.Identification.IsDeltaCorrectOnStop.one_sub_le_measureReal_of_isRun`: the two
  properties for every run.
* Monotonicity in the level and in the badness predicate, and restriction to subfamilies of
  environments: `IsDeltaCorrectOnStop.mono`, `IsDeltaCorrectOnStop.mono_bad`,
  `IsDeltaCorrectOnStop.comp`.

## Implementation notes

The definition is adapted from `EValuesResearch/Results/DesignExperts.lean` (commit `cb8238f`) in
the paper project `RemyDegenne/evalues_research`, where it is stated for an identification task,
rewritten here for a family of environments and a badness predicate, on the API of
`LMLExplore.Identification.IsDeltaCorrect`.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 55 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory ProbabilityTheory Learning

variable {𝓞 𝓐 𝓨 𝓓 Ω Θ Θ' : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓓 : MeasurableSpace 𝓓} {mΩ : MeasurableSpace Ω}
  {A : IdentAlg 𝓞 𝓐 𝓨 𝓓} {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {out : Ω → 𝓓}
  {P : Measure Ω} {env : Θ → Environment 𝓞 𝓐 𝓨} {bad bad' : Θ → 𝓓 → Prop} {δ δ' : ℝ}

namespace LMLExplore.Identification

/-- `A` is *`δ`-correct when it stops* for the family of environments
`env : Θ → Environment 𝓞 𝓐 𝓨` and the badness predicate `bad : Θ → 𝓓 → Prop`: for every `θ`, with
probability at most `δ`, `A` stops in `env θ` and its output is `bad θ` [EVR26, Notes 49 and 55].
Nothing is asked when `A` does not stop; `IsDeltaCorrect` asks, in addition, that `A` stop with
probability at least `1 - δ`.
See `IsDeltaCorrectOnStop.measureReal_stoppingTime_ne_top_and_bad_of_isRun` for the corresponding
statement about any run of `A`. -/
def IsDeltaCorrectOnStop (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (env : Θ → Environment 𝓞 𝓐 𝓨)
    (bad : Θ → 𝓓 → Prop) (δ : ℝ) : Prop :=
  ∀ θ, (histOutputMeasure A (env θ)).real {p | p.1 ∈ A.stopSet ∧ bad θ p.2} ≤ δ

/-- The defining property of `IsDeltaCorrectOnStop`. -/
lemma isDeltaCorrectOnStop_iff : IsDeltaCorrectOnStop A env bad δ ↔
    ∀ θ, (histOutputMeasure A (env θ)).real {p | p.1 ∈ A.stopSet ∧ bad θ p.2} ≤ δ := Iff.rfl

/-! ### Monotonicity and restriction -/

/-- The `δ`-correctness when stopping is monotone in the level. -/
lemma IsDeltaCorrectOnStop.mono (h : IsDeltaCorrectOnStop A env bad δ) (hδ : δ ≤ δ') :
    IsDeltaCorrectOnStop A env bad δ' :=
  fun θ ↦ (h θ).trans hδ

/-- The `δ`-correctness when stopping is antitone in the badness predicate. -/
lemma IsDeltaCorrectOnStop.mono_bad (h : IsDeltaCorrectOnStop A env bad δ)
    (hbad : ∀ θ d, bad' θ d → bad θ d) : IsDeltaCorrectOnStop A env bad' δ :=
  fun θ ↦ (h θ).trans' <| measureReal_mono fun _ hp ↦ ⟨hp.1, hbad θ _ hp.2⟩

/-- The `δ`-correctness when stopping is inherited by subfamilies of environments. -/
lemma IsDeltaCorrectOnStop.comp (h : IsDeltaCorrectOnStop A env bad δ) (f : Θ' → Θ) :
    IsDeltaCorrectOnStop A (env ∘ f) (bad ∘ f) δ :=
  fun θ ↦ h (f θ)

end LMLExplore.Identification

/-! ### Comparison with the other guarantees -/

namespace Learning.IdentAlg

open LMLExplore.Identification

/-- An algorithm PAC at level `δ` is `δ`-correct when it stops. -/
lemma IsPAC.isDeltaCorrectOnStop (h : A.IsPAC env bad δ) : IsDeltaCorrectOnStop A env bad δ := by
  intro θ
  refine le_trans ?_ (h θ)
  rw [← snd_histOutputMeasure]
  calc (histOutputMeasure A (env θ)).real {p | p.1 ∈ A.stopSet ∧ bad θ p.2}
  _ ≤ (histOutputMeasure A (env θ)).real (Prod.snd ⁻¹' {d | bad θ d}) :=
    measureReal_mono fun _ hp ↦ hp.2
  _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _)
    (Measure.le_map_apply measurable_snd.aemeasurable _)

end Learning.IdentAlg

namespace LMLExplore.Identification

/-- A `δ`-correct algorithm is `δ`-correct when it stops. -/
lemma IsDeltaCorrect.isDeltaCorrectOnStop (h : IsDeltaCorrect A env bad δ) :
    IsDeltaCorrectOnStop A env bad δ :=
  fun θ ↦ (isDeltaCorrect_iff.1 h θ).trans' <| measureReal_mono fun _ hp ↦ Or.inr hp.2

/-- A `δ`-PAC algorithm is `δ`-correct when it stops. -/
lemma IsDeltaPAC.isDeltaCorrectOnStop (h : IsDeltaPAC A env bad δ) :
    IsDeltaCorrectOnStop A env bad δ :=
  h.isPAC.isDeltaCorrectOnStop

/-- If `A` stops almost surely in `env`, not stopping does not contribute to the probability of
an event of the output: the probability that `A` does not stop or its output satisfies `b` is the
probability that it stops with an output that satisfies `b`. -/
lemma StopsAS.measureReal_notMem_stopSet_or_eq {env : Environment 𝓞 𝓐 𝓨} (h : StopsAS A env)
    (b : 𝓓 → Prop) :
    (histOutputMeasure A env).real {p | p.1 ∉ A.stopSet ∨ b p.2} =
      (histOutputMeasure A env).real {p | p.1 ∈ A.stopSet ∧ b p.2} := by
  have h_ae : ∀ᵐ p ∂histOutputMeasure A env, p.1 ∈ A.stopSet :=
    ae_of_ae_map measurable_fst.aemeasurable <| by
      rw [← Measure.fst, fst_histOutputMeasure]
      exact stopsAS_iff.1 h
  exact measureReal_congr <| Filter.eventuallyEqSet_iff.2 <| h_ae.mono fun p hp ↦ by simp [hp]

/-- An algorithm `δ`-correct when it stops that stops almost surely in every environment of the
family is `δ`-correct. -/
lemma IsDeltaCorrectOnStop.isDeltaCorrect (h : IsDeltaCorrectOnStop A env bad δ)
    (h_stop : ∀ θ, StopsAS A (env θ)) : IsDeltaCorrect A env bad δ :=
  isDeltaCorrect_iff.2 fun θ ↦ ((h_stop θ).measureReal_notMem_stopSet_or_eq _).trans_le (h θ)

/-- An algorithm `δ`-correct when it stops that stops almost surely in every environment of the
family is `δ`-PAC, for a measurable badness predicate. -/
lemma IsDeltaCorrectOnStop.isDeltaPAC (h : IsDeltaCorrectOnStop A env bad δ)
    (hbad : ∀ θ, MeasurableSet {d | bad θ d}) (h_stop : ∀ θ, StopsAS A (env θ)) :
    IsDeltaPAC A env bad δ :=
  isDeltaPAC_iff.2 ⟨(h.isDeltaCorrect h_stop).isPAC hbad, h_stop⟩

/-- For a measurable badness predicate, an algorithm is `δ`-PAC exactly when it is `δ`-correct
when it stops and stops almost surely in every environment of the family. -/
lemma isDeltaPAC_iff_isDeltaCorrectOnStop (hbad : ∀ θ, MeasurableSet {d | bad θ d}) :
    IsDeltaPAC A env bad δ ↔ IsDeltaCorrectOnStop A env bad δ ∧ ∀ θ, StopsAS A (env θ) :=
  ⟨fun h ↦ ⟨h.isDeltaCorrectOnStop, h.stopsAS⟩, fun h ↦ h.1.isDeltaPAC hbad h.2⟩

/-- An algorithm `δ`-correct when it stops that stops almost surely in `env θ` stops there with
an output that is not `bad θ` with probability at least `1 - δ`. -/
lemma IsDeltaCorrectOnStop.one_sub_le_measureReal_histOutputMeasure
    (h : IsDeltaCorrectOnStop A env bad δ) {θ : Θ} (h_stop : StopsAS A (env θ)) :
    1 - δ ≤ (histOutputMeasure A (env θ)).real {p | p.1 ∈ A.stopSet ∧ ¬ bad θ p.2} := by
  set μ := histOutputMeasure A (env θ)
  have h_le : μ.real Set.univ ≤
      μ.real {p | p.1 ∈ A.stopSet ∧ ¬ bad θ p.2} + μ.real {p | p.1 ∉ A.stopSet ∨ bad θ p.2} :=
    (measureReal_mono fun p _ ↦ by by_cases hp : p.1 ∈ A.stopSet <;> simp [hp, em']).trans
      (measureReal_union_le _ _)
  rw [probReal_univ, h_stop.measureReal_notMem_stopSet_or_eq] at h_le
  linarith [h θ]

/-! ### Runs of algorithms that are `δ`-correct when they stop -/

variable [IsProbabilityMeasure P] {θ : Θ}

/-- For an algorithm `δ`-correct when it stops, in any run in `env θ`, with probability at most
`δ` the algorithm stops and its output is `bad θ`. -/
lemma IsDeltaCorrectOnStop.measureReal_stoppingTime_ne_top_and_bad_of_isRun
    (h : IsDeltaCorrectOnStop A env bad δ) (hbad : MeasurableSet {d | bad θ d})
    (hrun : A.IsRun (env θ) O X Y out P) :
    P.real {ω | A.stoppingTime O X Y ω ≠ ⊤ ∧ bad θ (out ω)} ≤ δ := by
  have h_eq := hrun.hasLaw_stoppedHist_output.measureReal_eq
    (p := fun q ↦ q.1 ∈ A.stopSet ∧ bad θ q.2)
    ((measurable_fst A.measurableSet_stopSet).inter (measurable_snd hbad))
  simp only [IdentAlg.stoppedHist_mem_stopSet_iff] at h_eq
  exact h_eq ▸ h θ

/-- For an algorithm `δ`-correct when it stops, in any run in an environment `env θ` in which it
stops almost surely, with probability at least `1 - δ` the algorithm stops and its output is not
`bad θ`. -/
lemma IsDeltaCorrectOnStop.one_sub_le_measureReal_of_isRun (h : IsDeltaCorrectOnStop A env bad δ)
    (hbad : MeasurableSet {d | bad θ d}) (h_stop : StopsAS A (env θ))
    (hrun : A.IsRun (env θ) O X Y out P) :
    1 - δ ≤ P.real {ω | A.stoppingTime O X Y ω ≠ ⊤ ∧ ¬ bad θ (out ω)} := by
  have h_eq := hrun.hasLaw_stoppedHist_output.measureReal_eq
    (p := fun q ↦ q.1 ∈ A.stopSet ∧ ¬ bad θ q.2)
    ((measurable_fst A.measurableSet_stopSet).inter (measurable_snd hbad.compl))
  simp only [IdentAlg.stoppedHist_mem_stopSet_iff] at h_eq
  exact h_eq ▸ h.one_sub_le_measureReal_histOutputMeasure h_stop

end LMLExplore.Identification
