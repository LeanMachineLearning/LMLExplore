/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.Online.Bandit.ArrayProbSpace

/-!
# The rows of the array model

In LML's array model (`Bandits.ArrayModel`), a point is a pair of seeds `ω.1 t` and of a table
`ω.2 i a` of observations, the observation number `i` of the source `a`. This file records the law
of a row `fun i ↦ ω.2 i a` of the table, the observations of one source, and the run of an
algorithm when there is a single source: it then reads that row in order. Together they say that
the run of any algorithm on a single source observes an i.i.d. sequence, so that results about
algorithms on finitely many sources specialize to results about i.i.d. sequences.

## Main statements

* `Bandits.ArrayModel.hasLaw_row_arrayMeasure`: under the array measure of `ν`, the row of the
  source `a` has the i.i.d. law of `ν a`.
* `Bandits.ArrayModel.reward_unique`: with a single source, the observation of round `n` is the
  entry `n` of its row.
-/

public section

open MeasureTheory ProbabilityTheory Learning

namespace Bandits.ArrayModel

variable {α 𝓧 : Type*} {mα : MeasurableSpace α} {m𝓧 : MeasurableSpace 𝓧}

/-- Under the array measure of `ν`, the observations `ω.2 i a` of the source `a` are i.i.d. with
law `ν a`. -/
lemma hasLaw_row_arrayMeasure (ν : Kernel α 𝓧) [IsMarkovKernel ν] (a : α) :
    HasLaw (fun ω : ProbSpace α 𝓧 ↦ fun i ↦ ω.2 i a) (Measure.infinitePi fun _ : ℕ ↦ ν a)
      (arrayMeasure ν) := by
  refine ⟨by fun_prop, ?_⟩
  have h : (fun ω : ProbSpace α 𝓧 ↦ fun i ↦ ω.2 i a) =
      (fun x : ℕ → α → 𝓧 ↦ fun i ↦ x i a) ∘ Prod.snd := rfl
  rw [h, ← Measure.map_map (by fun_prop) measurable_snd, arrayMeasure, Measure.map_snd_prod,
    measure_univ, one_smul, streamMeasure,
    Measure.infinitePi_map_pi _ (fun _ ↦ measurable_pi_apply a)]
  simp_rw [Measure.infinitePi_map_eval]

/-- With a single source, every round observes it, and the observation of round `n` is the entry
`n` of its row. -/
lemma reward_unique [Unique α] [StandardBorelSpace α] (alg : Algorithm Unit α 𝓧) (n : ℕ)
    (ω : ProbSpace α 𝓧) : reward alg n ω = ω.2 n default := by
  have hp : pullCount (action alg) default n ω = n := by
    simpa using sum_pullCount (A := action alg) (t := n) (ω := ω)
  rw [reward_eq]
  dsimp only
  rw [Unique.eq_default (action alg n ω), hp]

end Bandits.ArrayModel
