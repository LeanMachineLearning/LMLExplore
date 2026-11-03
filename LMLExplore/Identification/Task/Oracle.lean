/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.Continuity
public import LMLExplore.Topology.Order.OrderClosed

/-!
# Oracle answers and oracle allocations

In a task with several correct answers, an algorithm that knew the model `θ` would answer one of
the *oracle answers* `i_F(θ)`, the answers `i` whose game has the largest value `D(θ, ¬i)`, and
would sample the arms with an optimal allocation `w*(θ, ¬i)` of such an answer. These are the
*oracle allocations* `w*(θ) = ⋃_{i ∈ i_F(θ)} w*(θ, ¬i)`. On an admissible model, the oracle
answers are the answers of value `D(θ)`, and for finitely many answers the oracle allocations are
the maximizers over the simplex of `w ↦ max_i D(θ, w, ¬i)`, at which this maximum is `D(θ)`.

Degenne and Koolen (2019) define these objects and show that, under the continuity of
`(θ, w) ↦ D(θ, w, ¬i)` (`LMLExplore/Identification/Task/Continuity.lean`), the correspondences
`θ ↦ i_F(θ)` and `θ ↦ w*(θ)` are upper hemicontinuous: near `θ`, every oracle answer is an oracle
answer at `θ`, and the oracle allocations are close to `w*(θ)`. The sticky Track-and-Stop
algorithm commits to an answer of `i_F(θ̂)` at an estimate `θ̂` of the model and tracks its optimal
allocations; its analysis rests on these two properties.

The set `w*(θ, ¬i)` is convex for each answer, but `w*(θ)` need not be: it is convex when `θ` has a
single oracle answer [DK19, Proposition 5].

These definitions are adapted from the formalization of [DK19] in the LMLPapers project, which
defines `i_F(θ)` as the answers of value `D(θ)`; the two agree on admissible models.

## Main definitions

* `IdentTask.oracleAnswers task θ`: the oracle answers `i_F(θ)`, maximizing `D(θ, ¬i)`.
* `IdentTask.oracleAlloc task θ`: the oracle allocations `w*(θ) = ⋃_{i ∈ i_F(θ)} w*(θ, ¬i)`.

## Main statements

* `IdentTask.mem_oracleAnswers_iff_answerValue_eq_gameValue`: on an admissible model, the oracle
  answers are the answers `i` with `D(θ, ¬i) = D(θ)`.
* `IdentTask.oracleAnswers_subset_correct`: on an admissible model with `D(θ) > 0`, the oracle
  answers are correct.
* `IdentTask.mem_oracleAlloc_iff_isMaxOn`: for finitely many answers, the oracle allocations are the
  maximizers of `w ↦ max_i D(θ, w, ¬i)` on the simplex.
* `IdentTask.iSup_altCost_eq_gameValue_of_mem_oracleAlloc`: on an admissible model,
  `max_i D(θ, w, ¬i) = D(θ)` for every oracle allocation `w`.
* `IdentTask.convex_oracleAlloc_of_subsingleton`: with at most one oracle answer, the oracle
  allocations form a convex set [DK19, Proposition 5].
* `IdentTask.isCompact_oracleAlloc`, `IdentTask.oracleAlloc_nonempty`: compactness and existence
  of the oracle allocations.
* `IdentTask.eventually_oracleAnswers_subset`,
  `IdentTask.upperHemicontinuousWithinAt_oracleAnswers`: upper hemicontinuity of the oracle
  answers [DK19, Lemma 30].
* `IdentTask.upperHemicontinuousWithinAt_oracleAlloc`: upper hemicontinuity of the oracle
  allocations [DK19, Theorem 4].

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, Theorem 4 and Proposition 5, and supplementary material, Appendix F, Lemma 30.
-/

public section

open Set Filter Topology

open scoped ENNReal

namespace LMLExplore.Identification

namespace IdentTask

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (task : IdentTask α Θ ℐ 𝓨) {θ : Θ} {i : ℐ} {w : α → ℝ}

/-- The oracle answers `i_F(θ)` at the model `θ`: the answers `i` whose game has the largest value
`D(θ, ¬i)`. -/
def oracleAnswers (θ : Θ) : Set ℐ := {i | ∀ j, task.answerValue θ j ≤ task.answerValue θ i}

/-- The oracle allocations `w*(θ) = ⋃_{i ∈ i_F(θ)} w*(θ, ¬i)` at the model `θ`: the optimal
allocations of the oracle answers. -/
def oracleAlloc (θ : Θ) : Set (α → ℝ) := ⋃ i ∈ task.oracleAnswers θ, task.optAlloc θ i

lemma oracleAnswers_def (θ : Θ) :
    task.oracleAnswers θ = {i | ∀ j, task.answerValue θ j ≤ task.answerValue θ i} := (rfl)

lemma oracleAlloc_def (θ : Θ) :
    task.oracleAlloc θ = ⋃ i ∈ task.oracleAnswers θ, task.optAlloc θ i := (rfl)

@[simp]
lemma mem_oracleAnswers_iff :
    i ∈ task.oracleAnswers θ ↔ ∀ j, task.answerValue θ j ≤ task.answerValue θ i := Iff.rfl

@[simp]
lemma mem_oracleAlloc_iff :
    w ∈ task.oracleAlloc θ ↔ ∃ i ∈ task.oracleAnswers θ, w ∈ task.optAlloc θ i := by
  simp only [oracleAlloc_def, mem_iUnion, exists_prop]

/-! ### Oracle answers -/

/-- On an admissible model, the oracle answers are the answers `i` whose value `D(θ, ¬i)` is the
value `D(θ)` of the game. -/
lemma mem_oracleAnswers_iff_answerValue_eq_gameValue (hθ : θ ∈ task.M) :
    i ∈ task.oracleAnswers θ ↔ task.answerValue θ i = task.gameValue θ := by
  rw [task.gameValue_eq_iSup_answerValue hθ, mem_oracleAnswers_iff]
  exact ⟨fun h ↦ le_antisymm (le_iSup (task.answerValue θ ·) i) (iSup_le h),
    fun h j ↦ h ▸ le_iSup (task.answerValue θ ·) j⟩

/-- For finitely many (at least one) answers, there is an oracle answer. -/
lemma oracleAnswers_nonempty [Finite ℐ] [Nonempty ℐ] (θ : Θ) :
    (task.oracleAnswers θ).Nonempty :=
  let ⟨i, hi⟩ := Finite.exists_max (task.answerValue θ)
  ⟨i, task.mem_oracleAnswers_iff.2 hi⟩

/-- On an admissible model at which the game has a positive value, the oracle answers are correct:
the incorrect answers have value `0`. -/
lemma oracleAnswers_subset_correct (hθ : θ ∈ task.M) (h : 0 < task.gameValue θ) :
    task.oracleAnswers θ ⊆ task.correct θ := by
  intro i hi
  by_contra hic
  rw [task.mem_oracleAnswers_iff_answerValue_eq_gameValue hθ,
    task.answerValue_eq_zero_of_mem_alt (task.mem_alt_iff.2 ⟨hθ, hic⟩)] at hi
  exact h.ne hi

/-! ### Oracle allocations -/

lemma oracleAlloc_subset_simplex (θ : Θ) : task.oracleAlloc θ ⊆ simplex α := fun _ hw ↦ by
  obtain ⟨_, -, hw⟩ := task.mem_oracleAlloc_iff.1 hw
  exact (task.mem_optAlloc_iff.1 hw).1

/-- For finitely many (at least one) answers, the oracle allocations are the maximizers over the
simplex of `w ↦ max_i D(θ, w, ¬i)`. -/
theorem mem_oracleAlloc_iff_isMaxOn [Finite ℐ] [Nonempty ℐ] :
    w ∈ task.oracleAlloc θ ↔
      w ∈ simplex α ∧ IsMaxOn (fun v ↦ ⨆ i, task.altCost θ v i) (simplex α) w := by
  constructor
  · intro hw
    obtain ⟨i, hi, hwi⟩ := task.mem_oracleAlloc_iff.1 hw
    rw [mem_optAlloc_iff] at hwi
    refine ⟨hwi.1, isMaxOn_iff.2 fun v hv ↦ iSup_le fun j ↦ ?_⟩
    -- `D(θ, v, ¬j) ≤ D(θ, ¬j) ≤ D(θ, ¬i) = D(θ, w, ¬i)`.
    exact (task.altCost_le_answerValue hv).trans <| (task.mem_oracleAnswers_iff.1 hi j).trans <|
      hwi.2.symm.le.trans (le_iSup (task.altCost θ w ·) i)
  · rintro ⟨hw, hmax⟩
    -- An answer `i` at which `max_j D(θ, w, ¬j)` is attained is an oracle answer, and `w` is
    -- optimal for it.
    obtain ⟨i, hi⟩ := Finite.exists_max (task.altCost θ w)
    have h_le : ∀ j, task.answerValue θ j ≤ task.altCost θ w i := fun j ↦ by
      rw [answerValue_def]
      exact iSup₂_le fun v hv ↦ (le_iSup (task.altCost θ v ·) j).trans <|
        (isMaxOn_iff.1 hmax v hv).trans (iSup_le hi)
    refine task.mem_oracleAlloc_iff.2 ⟨i, fun j ↦ (h_le j).trans (task.altCost_le_answerValue hw),
      task.mem_optAlloc_iff.2 ⟨hw, (task.altCost_le_answerValue hw).antisymm (h_le i)⟩⟩

/-- On an admissible model, the oracle allocations attain the value of the game:
`max_i D(θ, w, ¬i) = D(θ)` for every `w ∈ w*(θ)`. -/
lemma iSup_altCost_eq_gameValue_of_mem_oracleAlloc (hθ : θ ∈ task.M)
    (hw : w ∈ task.oracleAlloc θ) :
    ⨆ i, task.altCost θ w i = task.gameValue θ := by
  obtain ⟨i, hi, hwi⟩ := task.mem_oracleAlloc_iff.1 hw
  rw [mem_optAlloc_iff] at hwi
  rw [task.gameValue_eq_iSup_answerValue hθ]
  refine le_antisymm (iSup_mono fun j ↦ task.altCost_le_answerValue hwi.1) (iSup_le fun j ↦ ?_)
  exact (task.mem_oracleAnswers_iff.1 hi j).trans
    (hwi.2.symm.le.trans (le_iSup (task.altCost θ w ·) i))

/-- **Convexity of the oracle allocations** [DK19, Proposition 5]. If there is at most one oracle
answer, the oracle allocations form a convex set. -/
lemma convex_oracleAlloc_of_subsingleton (h : (task.oracleAnswers θ).Subsingleton) :
    Convex ℝ (task.oracleAlloc θ) := by
  rcases h.eq_empty_or_singleton with he | ⟨i, hi⟩
  · simp only [oracleAlloc_def, he, mem_empty_iff_false, iUnion_of_empty, iUnion_empty]
    exact convex_empty
  · simpa only [oracleAlloc_def, hi, mem_singleton_iff, iUnion_iUnion_eq_left] using
      task.convex_optAlloc θ i

/-- For finitely many answers, if the cost of the alternatives to each oracle answer is upper
semicontinuous in the allocation on the simplex, the oracle allocations form a compact set. -/
lemma isCompact_oracleAlloc [Finite ℐ]
    (h : ∀ i ∈ task.oracleAnswers θ, UpperSemicontinuousOn (task.altCost θ · i) (simplex α)) :
    IsCompact (task.oracleAlloc θ) :=
  (toFinite _).isCompact_biUnion fun i hi ↦ task.isCompact_optAlloc (h i hi)

/-- For finitely many (at least one) answers, if the cost of the alternatives to each oracle answer
is upper semicontinuous in the allocation on the simplex, an oracle allocation exists. -/
lemma oracleAlloc_nonempty [Finite ℐ] [Nonempty ℐ] [Nonempty α]
    (h : ∀ i ∈ task.oracleAnswers θ, UpperSemicontinuousOn (task.altCost θ · i) (simplex α)) :
    (task.oracleAlloc θ).Nonempty := by
  obtain ⟨i, hi⟩ := task.oracleAnswers_nonempty θ
  obtain ⟨w, hw⟩ := task.optAlloc_nonempty (h i hi)
  exact ⟨w, task.mem_oracleAlloc_iff.2 ⟨i, hi, hw⟩⟩

/-! ### Upper hemicontinuity in the model -/

variable [TopologicalSpace Θ] {s : Set Θ}

/-- **The oracle answers can only shrink** [DK19, Lemma 30]. For finitely many answers, if every
value `θ ↦ D(θ, ¬i)` is continuous within `s` at `θ`, then near `θ` within `s` every oracle answer
is an oracle answer at `θ`. -/
theorem eventually_oracleAnswers_subset [Finite ℐ]
    (h : ∀ i, ContinuousWithinAt (task.answerValue · i) s θ) :
    ∀ᶠ θ' in 𝓝[s] θ, task.oracleAnswers θ' ⊆ task.oracleAnswers θ := by
  filter_upwards [eventually_setOf_forall_le_subset h] with θ' hθ' i hi
  exact task.mem_oracleAnswers_iff.2 (hθ' (task.mem_oracleAnswers_iff.1 hi))

/-- **Upper hemicontinuity of the oracle answers** [DK19, Lemma 30]. For finitely many answers, if
every value `θ ↦ D(θ, ¬i)` is continuous within `s` at `θ`, then `θ ↦ i_F(θ)` is upper
hemicontinuous within `s` at `θ`, for every topology on the answers. -/
theorem upperHemicontinuousWithinAt_oracleAnswers [Finite ℐ] [TopologicalSpace ℐ]
    (h : ∀ i, ContinuousWithinAt (task.answerValue · i) s θ) :
    UpperHemicontinuousWithinAt task.oracleAnswers s θ :=
  .of_eventually_subset (task.eventually_oracleAnswers_subset h)

/-- **Upper hemicontinuity of the oracle allocations** [DK19, Theorem 4]. For finitely many answers,
if for every answer `i` the function `(θ, w) ↦ D(θ, w, ¬i)` is continuous within `s ×ˢ simplex α`
at every point `(θ, w)` with `w` in the simplex, then `θ ↦ w*(θ)` is upper hemicontinuous within
`s` at `θ`. -/
theorem upperHemicontinuousWithinAt_oracleAlloc [Finite ℐ]
    (h : ∀ i, ∀ w ∈ simplex α, ContinuousWithinAt (fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i)
      (s ×ˢ simplex α) (θ, w)) :
    UpperHemicontinuousWithinAt task.oracleAlloc s θ :=
  UpperHemicontinuousWithinAt.biUnion_of_eventually_subset (f := fun i θ' ↦ task.optAlloc θ' i)
    (toFinite _) (fun i _ ↦ task.upperHemicontinuousWithinAt_optAlloc (h i))
    (task.eventually_oracleAnswers_subset fun i ↦ task.continuousWithinAt_answerValue (h i))

end IdentTask

end LMLExplore.Identification
