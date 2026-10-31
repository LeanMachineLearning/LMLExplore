/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Algorithm
public import LMLExplore.Probability.HasCondDistrib

/-!
# Transport of algorithm-environment sequences

Complements to LML's `LeanMachineLearning.SequentialLearning.Algorithm`: an
algorithm-environment sequence on `(Ω', P')` is transported to `(Ω, P)` along a measurable map
`g : Ω → Ω'` carrying `P` to `P'`. This is how a run of an algorithm on a canonical space (such as
a product of the trajectory space with the space of an extra random variable) is built from a run
on a smaller space.

## Main statements

* `Learning.IsAlgEnvSeq.comp_hasLaw`: algorithm-environment sequences are transported along a
  measurable map `g : Ω → Ω'` carrying `P` to `P'`.

Adapted from the LMLPapers project (same author).
-/

public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 Ω Ω' : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨}
  {P : Measure Ω} [IsFiniteMeasure P] {P' : Measure Ω'} [IsFiniteMeasure P'] {g : Ω → Ω'}
  {O : ℕ → Ω' → 𝓞} {X : ℕ → Ω' → 𝓐} {Y : ℕ → Ω' → 𝓨}

/-- An algorithm-environment sequence is transported along a measurable map `g` carrying `P`
to `P'`. -/
lemma IsAlgEnvSeq.comp_hasLaw (h : IsAlgEnvSeq O X Y alg env P') (hg : HasLaw g P' P)
    (hgm : Measurable g) :
    IsAlgEnvSeq (fun n ↦ O n ∘ g) (fun n ↦ X n ∘ g) (fun n ↦ Y n ∘ g) alg env P where
  measurable_obs n := (h.measurable_obs n).comp hgm
  measurable_action n := (h.measurable_action n).comp hgm
  measurable_feedback n := (h.measurable_feedback n).comp hgm
  hasCondDistrib_obs n := (h.hasCondDistrib_obs n).comp_hasLaw hg
  hasCondDistrib_action n := (h.hasCondDistrib_action n).comp_hasLaw hg
  hasCondDistrib_feedback n := (h.hasCondDistrib_feedback n).comp_hasLaw hg

end Learning
