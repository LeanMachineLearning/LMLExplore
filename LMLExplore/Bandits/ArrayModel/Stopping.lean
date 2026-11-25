/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.Online.Bandit.ArrayProbSpace
public import LeanMachineLearning.SequentialLearning.StoppedHistory
public import LMLExplore.Probability.ProductMeasure.Table
import LMLExplore.Data.ENat.Basic
import LMLExplore.Probability.Process.StoppedValue

/-!
# Stopping times in the array model

In LML's array model (`Bandits.ArrayModel`), a point is a pair of seeds `ω.1 t`, from which the
algorithm draws its actions, and of a table `ω.2 i a` of observations, the observation number `i`
of the source `a`. A stopping time of a run reads the seeds and the observations that the
algorithm has read so far. This file shows that the run stopped at `min τ k` is a bounded round of
the table, in the sense of `ProbabilityTheory.DependsOnBelow`: its shape, the numbers of seeds and
of observations of each source that it reads, and the variables known at time `τ` on `{τ ≤ k}`,
are determined by the entries below that shape.

## Main definitions

* `Bandits.ArrayModel.IsStoppedVar alg τ f`: `τ` and `f` are determined, on the event `{τ = t}`,
  by the seeds `ω.1 0, …, ω.1 t` and the history of the first `t` rounds of `alg`.
* `Bandits.ArrayModel.stoppedShape alg τ k`: the seeds and the observations of each source that
  the run of `alg` reads by the time `min τ k`.

## Main statements

* `Bandits.ArrayModel.IsStoppedVar.dependsOnBelow_stoppedShape`,
  `Bandits.ArrayModel.IsStoppedVar.dependsOnBelow_indicator`: the shape of the stopped run, and a
  stopped variable on `{τ ≤ k}`, are determined by the entries below that shape.
* `Bandits.ArrayModel.arrayMeasure_eq_arrayLaw`: the array measure of LML is
  `ProbabilityTheory.arrayLaw` for the uniform law of the seeds.
* `Bandits.ArrayModel.isStoppedVar_hittingAfter`: the hitting time of a stopping rule and the
  history at that time form a stopped variable.

## Implementation notes

The definitions and proofs are adapted from the draft `notes/lean-wip/SeveralArms.lean` of the
paper project `RemyDegenne/evalues_research`, which formalizes [EVR26, Note 41].

## References

* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 41,
  `results/41-several-arms-bipolar-rate.md`.
-/

public section

open MeasureTheory ProbabilityTheory Learning

namespace Bandits.ArrayModel

variable {α 𝓧 β : Type*} [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [StandardBorelSpace α] {m𝓧 : MeasurableSpace 𝓧} {alg : Algorithm Unit α 𝓧}
  {τ : ProbSpace α 𝓧 → WithTop ℕ}

/-! ### Stopping times and stopped variables in the array model -/

/-- In the array model, `τ` and `f` are determined, on the event `{τ = t}`, by the seeds
`ω.1 0, …, ω.1 t` and the history of the first `t` rounds of the algorithm `alg`: the time `τ`
is a stopping time for the information of the algorithm, its seeds and the observations it has
read, and `f` is known at that time. The hitting time of a stopping rule and the history at that
time are an instance (`Bandits.ArrayModel.isStoppedVar_hittingAfter`). -/
def IsStoppedVar (alg : Algorithm Unit α 𝓧) (τ : ProbSpace α 𝓧 → WithTop ℕ)
    (f : ProbSpace α 𝓧 → β) : Prop :=
  ∀ (ω ω' : ProbSpace α 𝓧) (t : ℕ), τ ω = t → (∀ i ≤ t, ω.1 i = ω'.1 i) →
    hist alg ω t = hist alg ω' t → τ ω' = t ∧ f ω' = f ω

lemma isStoppedVar_iff {f : ProbSpace α 𝓧 → β} :
    IsStoppedVar alg τ f ↔ ∀ (ω ω' : ProbSpace α 𝓧) (t : ℕ), τ ω = t →
      (∀ i ≤ t, ω.1 i = ω'.1 i) → hist alg ω t = hist alg ω' t → τ ω' = t ∧ f ω' = f ω :=
  Iff.rfl

/-- A function of a stopped variable is a stopped variable. -/
lemma IsStoppedVar.comp {γ : Type*} {f : ProbSpace α 𝓧 → β} (h : IsStoppedVar alg τ f)
    (g : β → γ) : IsStoppedVar alg τ fun ω ↦ g (f ω) := by
  refine isStoppedVar_iff.2 fun ω ω' t hτ hseed hhist ↦ ?_
  obtain ⟨hτ', hf⟩ := (isStoppedVar_iff.1 h) ω ω' t hτ hseed hhist
  exact ⟨hτ', by rw [hf]⟩

/-- The shape of the run of `alg` stopped at the time `min τ k`: the seeds
`ω.1 0, …, ω.1 (min τ k)` and, for each source, the observations read by that time. -/
noncomputable def stoppedShape (alg : Algorithm Unit α 𝓧) (τ : ProbSpace α 𝓧 → WithTop ℕ) (k : ℕ)
    (ω : ProbSpace α 𝓧) : ℕ × (α → ℕ) :=
  ((min (τ ω) k).untopA + 1, fun a ↦ pullCount (action alg) a (min (τ ω) k).untopA ω)

lemma stoppedShape_def (alg : Algorithm Unit α 𝓧) (τ : ProbSpace α 𝓧 → WithTop ℕ) (k : ℕ)
    (ω : ProbSpace α 𝓧) :
    stoppedShape alg τ k ω =
      ((min (τ ω) k).untopA + 1, fun a ↦ pullCount (action alg) a (min (τ ω) k).untopA ω) :=
  (rfl)

/-- The run stopped at `min τ k` reads at most `k` observations of each source. -/
lemma stoppedShape_snd_le (alg : Algorithm Unit α 𝓧) (τ : ProbSpace α 𝓧 → WithTop ℕ) (k : ℕ)
    (ω : ProbSpace α 𝓧) (a : α) : (stoppedShape alg τ k ω).2 a ≤ k :=
  (pullCount_le a _ ω).trans (WithTop.untopA_le (min_le_right _ _))

/-- The run stopped at `min τ k` reads `min τ k` observations. -/
lemma sum_stoppedShape_snd [Fintype α] (alg : Algorithm Unit α 𝓧) (τ : ProbSpace α 𝓧 → WithTop ℕ)
    (k : ℕ) (ω : ProbSpace α 𝓧) : ∑ a, (stoppedShape alg τ k ω).2 a = (min (τ ω) k).untopA :=
  sum_pullCount

lemma measurable_stoppedShape [Countable α] (alg : Algorithm Unit α 𝓧) (hτ : Measurable τ) (k : ℕ) :
    Measurable (stoppedShape alg τ k) := by
  have ht : Measurable fun ω ↦ (min (τ ω) k).untopA :=
    (hτ.min measurable_const).untopA
  refine (ht.add measurable_const).prodMk (measurable_pi_iff.2 fun a ↦ ?_)
  exact measurable_apply_of_countable
    (fun t ↦ measurable_pullCount (measurable_action alg) a t) ht

/-- Two points with the same entries below the shape of the run stopped at `min τ k` have the
same time `min τ k`, the same histories up to that time, and the same stopped variable if
`τ ≤ k`. -/
private lemma IsStoppedVar.eq_of_agreeBelow {f : ProbSpace α 𝓧 → β}
    (h : IsStoppedVar alg τ f) {k : ℕ} {ω ω' : ProbSpace α 𝓧}
    (hag : AgreeBelow (stoppedShape alg τ k ω) ω ω') :
    (min (τ ω') k).untopA = (min (τ ω) k).untopA ∧ (τ ω' ≤ k ↔ τ ω ≤ k) ∧
      (τ ω ≤ k → f ω' = f ω) ∧
      hist alg ω' (min (τ ω) k).untopA = hist alg ω (min (τ ω) k).untopA := by
  rw [agreeBelow_iff] at hag
  set t := (min (τ ω) k).untopA with ht
  have hcoe : (t : WithTop ℕ) = min (τ ω) k :=
    WithTop.natCast_untopA (WithTop.ne_top_of_le_natCast (min_le_right _ _))
  have htk : t ≤ k := WithTop.untopA_le (min_le_right _ _)
  have hseed (i : ℕ) (hi : i ≤ t) : ω.1 i = ω'.1 i :=
    hag.1 i (by simp only [stoppedShape_def]; omega)
  have hhist (j : ℕ) (hj : j ≤ t) : hist alg ω j = hist alg ω' j :=
    hist_congr alg j (fun i hi ↦ hseed i (by omega))
      fun i a hi ↦ hag.2 a i (hi.trans_le (pullCount_mono a hj ω))
  by_cases hle : τ ω ≤ k
  · have hτ : τ ω = t := by rw [hcoe, min_eq_left hle]
    obtain ⟨hτ', hf⟩ := (isStoppedVar_iff.1 h) ω ω' t hτ hseed (hhist t le_rfl)
    refine ⟨?_, by rw [hτ', hτ], fun _ ↦ hf, (hhist t le_rfl).symm⟩
    rw [hτ', min_eq_left (by exact_mod_cast htk), WithTop.untopA_natCast]
  · have hkt : t = k := by
      rw [ht, min_eq_right (not_le.1 hle).le, WithTop.untopA_natCast]
    have hle' : ¬ τ ω' ≤ k := by
      intro hle'
      obtain ⟨t', ht'⟩ := WithTop.exists_eq_natCast_of_ne_top (WithTop.ne_top_of_le_natCast hle')
      have ht'k : t' ≤ k := by rw [ht'] at hle'; exact_mod_cast hle'
      obtain ⟨hτ, -⟩ := (isStoppedVar_iff.1 h) ω' ω t' ht'
        (fun i hi ↦ (hseed i (by omega)).symm) (hhist t' (by omega)).symm
      exact hle (by rw [hτ]; exact_mod_cast ht'k)
    refine ⟨?_, by simp [hle, hle'], fun h' ↦ absurd h' hle, (hhist t le_rfl).symm⟩
    rw [min_eq_right (not_le.1 hle').le, hkt, WithTop.untopA_natCast]

/-- The shape of the run stopped at `min τ k` is determined by the entries below itself. -/
lemma IsStoppedVar.dependsOnBelow_stoppedShape {f : ProbSpace α 𝓧 → β}
    (h : IsStoppedVar alg τ f) (k : ℕ) :
    DependsOnBelow (stoppedShape alg τ k) (stoppedShape alg τ k) := by
  refine dependsOnBelow_iff.2 fun ω ω' hag ↦ ?_
  obtain ⟨ht, -, -, hhist⟩ := h.eq_of_agreeBelow hag
  simp only [stoppedShape_def, ht, Prod.mk.injEq, true_and]
  funext a
  rw [pullCount_action_eq, pullCount_action_eq, hhist]

/-- The stopped variable, on the event `{τ ≤ k}`, is determined by the entries below the shape of
the run stopped at `min τ k`. -/
lemma IsStoppedVar.dependsOnBelow_indicator [Zero β] {f : ProbSpace α 𝓧 → β}
    (h : IsStoppedVar alg τ f) (k : ℕ) :
    DependsOnBelow (stoppedShape alg τ k) ({ω | τ ω ≤ k}.indicator f) := by
  refine dependsOnBelow_iff.2 fun ω ω' hag ↦ ?_
  obtain ⟨-, hiff, hf, -⟩ := h.eq_of_agreeBelow hag
  by_cases hle : τ ω ≤ k
  · rw [Set.indicator_of_mem (s := {ω | τ ω ≤ k}) hle,
      Set.indicator_of_mem (s := {ω | τ ω ≤ k}) (hiff.2 hle), hf hle]
  · rw [Set.indicator_of_notMem (s := {ω | τ ω ≤ k}) hle,
      Set.indicator_of_notMem (s := {ω | τ ω ≤ k}) (mt hiff.1 hle)]

omit [DecidableEq α] [Nonempty α] [StandardBorelSpace α] in
/-- The array measure of LML is the law of the uniform seeds and of the table. -/
lemma arrayMeasure_eq_arrayLaw (ν : Kernel α 𝓧) :
    arrayMeasure ν = arrayLaw volume fun a ↦ ν a := by
  rw [arrayLaw_def, arrayMeasure, streamMeasure]

/-! ### Stopping rules -/

/-- In the array model, the hitting time of a stopping rule `S`, the first time at which the
history belongs to `S`, and the history at that time form a stopped variable of the algorithm. -/
lemma isStoppedVar_hittingAfter (alg : Algorithm Unit α 𝓧) (S : Set (Σ n, Hist Unit α 𝓧 n)) :
    IsStoppedVar alg
      (hittingAfter (sigmaHistory (noObs (ProbSpace α 𝓧)) (action alg) (reward alg)) S 0)
      (stoppedValue (sigmaHistory (noObs (ProbSpace α 𝓧)) (action alg) (reward alg))
        (hittingAfter (sigmaHistory (noObs (ProbSpace α 𝓧)) (action alg) (reward alg)) S 0)) := by
  refine isStoppedVar_iff.2 fun ω ω' t hτ _ hhist ↦ ?_
  set u := sigmaHistory (noObs (ProbSpace α 𝓧)) (action alg) (reward alg)
  -- the histories of `ω` and `ω'` agree up to time `t`
  have hu (j : ℕ) (hj : j ≤ t) : u j ω' = u j ω := by
    simp only [u, sigmaHistory_apply]
    rw [history_eq_comp_history hj]
    simp only [Function.comp_apply, ← hist_eq_history, hhist]
  have hτ' : hittingAfter u S 0 ω' = t := by
    have h := hτ
    rw [Nat.cast_withTop, hittingAfter_eq_coe_iff] at h ⊢
    exact ⟨h.1, by rw [hu t le_rfl]; exact h.2.1,
      fun j hj ↦ by rw [hu j hj.2.le]; exact h.2.2 j hj⟩
  refine ⟨hτ', ?_⟩
  simp only [stoppedValue, hτ, hτ', WithTop.untopA_natCast]
  exact hu t le_rfl

end Bandits.ArrayModel
