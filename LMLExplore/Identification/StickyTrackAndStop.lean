/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.TrackAndStop
public import LMLExplore.Identification.Task.Oracle

/-!
# Sticky Track-and-Stop

In a task with several correct answers, Track-and-Stop tracks the optimal allocations of an oracle
answer of the estimated model `θ̂`. When the true model `θ` has several oracle answers, the oracle
answers of `θ̂` may keep switching between them, and so may the targets, whose averages then need
not approach any set of optimal allocations: the oracle allocations `w*(θ)` need not be convex
[DK19, Proposition 5]. *Sticky Track-and-Stop* [DK19, Algorithm 1] commits to one of them. Fix a
linear order on the answers. After `n` rounds with history `h`, with a confidence region `C n h` of
models,
* the *candidate answers* `I(C) = ⋃_{λ ∈ C} i_F(λ)` are the oracle answers of the models of the
  confidence region;
* the *sticky answer* is the least candidate answer;
* the sampling rule C-tracks the targets `w(i, θ̂)` of the sticky answer `i`, typically optimal
  allocations `w*(θ̂, ¬i)` of `i` at the estimate `θ̂ = est n h`;
* the stopping rule is the GLRT with the plug-in statistic of `est`.

Degenne and Koolen take for `C n h` the admissible models `λ` with
`∑ a, N_a KL(ν_a(θ̂), ν_a(λ)) ≤ r n h` (`IdentTask.confidenceRegion`), for a radius `r n h` growing
logarithmically with `n`. As long as the true model `θ` is in the confidence region, its oracle
answers are candidates. As the region shrinks towards `θ`, the oracle answers of its models are
oracle answers of `θ`, by the upper hemicontinuity of `θ ↦ i_F(θ)` [DK19, Lemma 30]. The candidate
answers are then exactly the oracle answers of `θ`, and the sticky answer is the least oracle answer
`i_θ` of `θ`, whatever the region (`IdentTask.eventually_smallSets_stickyAnswer_eq`). The targets
are then the optimal allocations of the single answer `i_θ` at `θ̂`, which approach the convex set
`w*(θ, ¬i_θ)` (`IdentTask.eventually_smallSets_prod_stickyTarget_mem`).

On the events on which the confidence regions contain `θ` and shrink to it, Sticky Track-and-Stop
thus behaves as Track-and-Stop with C-tracking of the optimal allocations of the single answer
`i_θ`, and its proportions of pulls approach `w*(θ, ¬i_θ)`, on which `D(θ, ·, ¬i_θ) = T*(θ)⁻¹`. For
exponential-family arms, if these events have probabilities whose complements have a finite sum,
the expected sample complexity is at most `c log (1 / δ)` for small `δ`, for every `c > T*(θ)`
(`IdentTask.eventually_expectedStoppingTime_stickyTrackAndStop_le`, [DK19, Theorem 11]). The
stopping rule is the GLRT, which is `δ`-PAC for every sampling rule and every recommendation rule
([DK19, Theorem 10], `IdentTask.isDeltaPAC_stickyTrackAndStop`).

## Main definitions

* `IdentTask.candidateAnswers task C`: the candidate answers `⋃_{λ ∈ C} i_F(λ)` of a set `C` of
  models.
* `IdentTask.stickyAnswer task C`: the least candidate answer of `C`, for a well-founded linear
  order on the answers (the least answer if `C` has no candidate).
* `IdentTask.confidenceRegion task est r n h`: the admissible models `λ` with
  `∑ a, N_a KL(ν_a(θ̂), ν_a(λ)) ≤ r n h`, the confidence region of [DK19, Algorithm 1].
* `IdentTask.stickyTrackAndStop task est C w hw β rec hrec hstop`: Sticky Track-and-Stop with
  confidence regions `C`, targets `w`, thresholds `β` and recommendation `rec`.

## Main statements

* `IdentTask.candidateAnswers_eq_oracleAnswers`,
  `IdentTask.stickyAnswer_eq_stickyAnswer_singleton`: if `θ ∈ C` and the oracle answers of the
  models of `C` are oracle answers of `θ`, the candidate answers of `C` are the oracle answers of
  `θ` and the sticky answer of `C` is the least oracle answer of `θ`.
* `IdentTask.eventually_smallSets_stickyAnswer_eq`: **the sticky answer sticks** [DK19, proof of
  Theorem 11]: if the values `θ ↦ D(θ, ¬i)` are continuous at `θ`, the sticky answer of every small
  enough set of models containing `θ` is the least oracle answer of `θ`.
* `IdentTask.eventually_smallSets_prod_stickyTarget_mem`: under the continuity of the costs of the
  alternatives, the targets of the sticky answer of every small enough set of models containing
  `θ`, at every estimate close enough to `θ`, are in any given neighbourhood of `w*(θ, ¬i_θ)`.
* `IdentTask.measurable_stickyAnswer`, `IdentTask.measurable_stickyTarget`: measurability of the
  sticky answer and of the targets.
* `IdentTask.setOf_exists_notMem_confidenceRegion`: the true model leaves the confidence region of
  radius `β` at some round exactly on the deviation event that controls the error of the GLRT with
  thresholds `β`.
* `IdentTask.isDeltaPAC_stickyTrackAndStop`: **Sticky Track-and-Stop is `δ`-PAC** [DK19,
  Theorem 10] when its thresholds control the deviations of the plug-in statistic and it stops
  almost surely.
* `IdentTask.eventually_expectedStoppingTime_stickyTrackAndStop_le`: **sample complexity of
  Sticky Track-and-Stop** [DK19, Theorem 11]: for exponential-family arms and confidence regions
  that concentrate around the model `μ`, `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for
  every `c > T*(μ)`, whatever the number of oracle answers of `μ`.

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, Algorithm 1, Proposition 5, Theorems 10 and 11, and supplementary material,
  Appendix F, Lemma 30.
-/

public section

open MeasureTheory ProbabilityTheory Learning Set Filter Topology

open scoped ENNReal

namespace LMLExplore.Identification.IdentTask

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (task : IdentTask α Θ ℐ 𝓨) {C C' : Set Θ} {θ : Θ} {i j : ℐ}

/-! ### Candidate answers -/

/-- The *candidate answers* `I(C) = ⋃_{λ ∈ C} i_F(λ)` of a set `C` of models: the oracle answers
of the models of `C`. For a confidence region `C` of the true model, these are the answers that an
oracle could pick for a model compatible with the data [DK19, Algorithm 1]. -/
def candidateAnswers (C : Set Θ) : Set ℐ := ⋃ θ ∈ C, task.oracleAnswers θ

lemma candidateAnswers_def (C : Set Θ) :
    task.candidateAnswers C = ⋃ θ ∈ C, task.oracleAnswers θ := (rfl)

@[simp]
lemma mem_candidateAnswers_iff :
    i ∈ task.candidateAnswers C ↔ ∃ θ ∈ C, i ∈ task.oracleAnswers θ := by
  simp only [candidateAnswers_def, mem_iUnion, exists_prop]

@[simp]
lemma candidateAnswers_empty : task.candidateAnswers (∅ : Set Θ) = ∅ := by
  simp [candidateAnswers_def]

@[simp]
lemma candidateAnswers_singleton (θ : Θ) :
    task.candidateAnswers {θ} = task.oracleAnswers θ := by
  simp [candidateAnswers_def]

@[simp]
lemma candidateAnswers_union (C C' : Set Θ) :
    task.candidateAnswers (C ∪ C') = task.candidateAnswers C ∪ task.candidateAnswers C' :=
  biUnion_union C C' _

@[gcongr]
lemma candidateAnswers_mono (h : C ⊆ C') : task.candidateAnswers C ⊆ task.candidateAnswers C' :=
  biUnion_subset_biUnion_left h

lemma oracleAnswers_subset_candidateAnswers (hθ : θ ∈ C) :
    task.oracleAnswers θ ⊆ task.candidateAnswers C :=
  subset_biUnion_of_mem (u := task.oracleAnswers) hθ

lemma candidateAnswers_subset_iff {I : Set ℐ} :
    task.candidateAnswers C ⊆ I ↔ ∀ θ ∈ C, task.oracleAnswers θ ⊆ I :=
  iUnion₂_subset_iff

/-- If `θ ∈ C` and the oracle answers of the models of `C` are oracle answers of `θ`, the
candidate answers of `C` are the oracle answers of `θ`. -/
lemma candidateAnswers_eq_oracleAnswers (hθ : θ ∈ C)
    (h : ∀ θ' ∈ C, task.oracleAnswers θ' ⊆ task.oracleAnswers θ) :
    task.candidateAnswers C = task.oracleAnswers θ :=
  (task.candidateAnswers_subset_iff.2 h).antisymm (task.oracleAnswers_subset_candidateAnswers hθ)

/-- For finitely many (at least one) answers, a set of models has a candidate answer iff it is
nonempty. -/
lemma candidateAnswers_nonempty_iff [Finite ℐ] [Nonempty ℐ] :
    (task.candidateAnswers C).Nonempty ↔ C.Nonempty := by
  refine ⟨fun ⟨i, hi⟩ ↦ ?_, fun ⟨θ, hθ⟩ ↦ ?_⟩
  · obtain ⟨θ, hθ, -⟩ := task.mem_candidateAnswers_iff.1 hi
    exact ⟨θ, hθ⟩
  · obtain ⟨i, hi⟩ := task.oracleAnswers_nonempty θ
    exact ⟨i, task.oracleAnswers_subset_candidateAnswers hθ hi⟩

/-! ### The sticky answer -/

section Sticky

variable [LinearOrder ℐ] [WellFoundedLT ℐ] [Nonempty ℐ]

open scoped Classical in
/-- The *sticky answer* of a set `C` of models [DK19, Algorithm 1]: the least candidate answer of
`C`, that is, the least oracle answer of a model of `C`, for the order on the answers. If `C` has
no candidate answer (for finitely many answers, if `C` is empty), it is the least answer. -/
noncomputable def stickyAnswer (C : Set Θ) : ℐ :=
  if h : (task.candidateAnswers C).Nonempty then WellFoundedLT.min _ h
  else WellFoundedLT.min univ univ_nonempty

open scoped Classical in
lemma stickyAnswer_def (C : Set Θ) :
    task.stickyAnswer C = if h : (task.candidateAnswers C).Nonempty then WellFoundedLT.min _ h
      else WellFoundedLT.min univ univ_nonempty := (rfl)

/-- The sticky answer depends on the set of models only through its candidate answers. -/
lemma stickyAnswer_congr (h : task.candidateAnswers C = task.candidateAnswers C') :
    task.stickyAnswer C = task.stickyAnswer C' := by
  rw [stickyAnswer_def, stickyAnswer_def, h]

lemma stickyAnswer_mem_candidateAnswers (h : (task.candidateAnswers C).Nonempty) :
    task.stickyAnswer C ∈ task.candidateAnswers C := by
  rw [stickyAnswer_def, dite_eq_left h]
  exact wellFounded_lt.min_mem _ h

lemma stickyAnswer_le (hi : i ∈ task.candidateAnswers C) : task.stickyAnswer C ≤ i := by
  rw [stickyAnswer_def, dite_eq_left ⟨i, hi⟩]
  exact WellFoundedLT.min_le hi

/-- Without candidate answers, the sticky answer is the least answer. -/
lemma stickyAnswer_le_of_candidateAnswers_eq_empty (h : task.candidateAnswers C = ∅) (j : ℐ) :
    task.stickyAnswer C ≤ j := by
  rw [stickyAnswer_def, dite_eq_right (not_nonempty_iff_eq_empty.2 h)]
  exact WellFoundedLT.min_le (mem_univ j)

/-- For a set of models with a candidate answer, the sticky answer is its least candidate
answer. -/
lemma stickyAnswer_eq_iff (h : (task.candidateAnswers C).Nonempty) :
    task.stickyAnswer C = i ↔ i ∈ task.candidateAnswers C ∧ ∀ j ∈ task.candidateAnswers C, i ≤ j :=
  ⟨fun hi ↦ hi ▸ ⟨task.stickyAnswer_mem_candidateAnswers h, fun _ ↦ task.stickyAnswer_le⟩,
    fun ⟨hi, hle⟩ ↦ (task.stickyAnswer_le hi).antisymm
      (hle _ (task.stickyAnswer_mem_candidateAnswers h))⟩

/-- The sticky answer of a single model is its least oracle answer. -/
lemma stickyAnswer_singleton_le (hi : i ∈ task.oracleAnswers θ) : task.stickyAnswer {θ} ≤ i :=
  task.stickyAnswer_le (by rwa [candidateAnswers_singleton])

/-- For finitely many answers, the sticky answer of a single model is an oracle answer of it. -/
lemma stickyAnswer_singleton_mem_oracleAnswers [Finite ℐ] (θ : Θ) :
    task.stickyAnswer {θ} ∈ task.oracleAnswers θ := by
  rw [← candidateAnswers_singleton]
  exact task.stickyAnswer_mem_candidateAnswers
    (task.candidateAnswers_nonempty_iff.2 (singleton_nonempty θ))

/-- For finitely many answers, the sticky answer of a nonempty set of models is an oracle answer of
one of its models. -/
lemma exists_mem_stickyAnswer_mem_oracleAnswers [Finite ℐ] (hC : C.Nonempty) :
    ∃ θ ∈ C, task.stickyAnswer C ∈ task.oracleAnswers θ :=
  task.mem_candidateAnswers_iff.1
    (task.stickyAnswer_mem_candidateAnswers (task.candidateAnswers_nonempty_iff.2 hC))

/-- On an admissible model at which the game has a positive value, for finitely many answers, the
sticky answer of the model is correct. -/
lemma stickyAnswer_singleton_mem_correct [Finite ℐ] (hθ : θ ∈ task.M)
    (h : 0 < task.gameValue θ) : task.stickyAnswer {θ} ∈ task.correct θ :=
  task.oracleAnswers_subset_correct hθ h (task.stickyAnswer_singleton_mem_oracleAnswers θ)

/-- If `θ ∈ C` and the oracle answers of the models of `C` are oracle answers of `θ`, the sticky
answer of `C` is the least oracle answer of `θ`. -/
lemma stickyAnswer_eq_stickyAnswer_singleton (hθ : θ ∈ C)
    (h : ∀ θ' ∈ C, task.oracleAnswers θ' ⊆ task.oracleAnswers θ) :
    task.stickyAnswer C = task.stickyAnswer {θ} :=
  task.stickyAnswer_congr (by rw [candidateAnswers_singleton,
    task.candidateAnswers_eq_oracleAnswers hθ h])

/-! ### Measurability -/

/-- For finitely many answers, the sticky answer of a family `C x` of sets of models is
measurable, for every σ-algebra on the answers, when membership of each answer in the candidate
answers of `C x` is a measurable property of `x`. -/
theorem measurable_stickyAnswer [Finite ℐ] {mℐ : MeasurableSpace ℐ} {β : Type*}
    {mβ : MeasurableSpace β} {C : β → Set Θ}
    (hC : ∀ i, Measurable fun x ↦ i ∈ task.candidateAnswers (C x)) :
    Measurable fun x ↦ task.stickyAnswer (C x) := by
  have : Countable ℐ := Finite.to_countable
  refine measurable_to_countable' fun i ↦ ?_
  -- The sticky answer is `i` iff `i` is the least candidate, or there is no candidate and `i` is
  -- the least answer.
  have h_eq : (fun x ↦ task.stickyAnswer (C x)) ⁻¹' {i} =
      {x | (i ∈ task.candidateAnswers (C x) ∧ ∀ j, j < i → j ∉ task.candidateAnswers (C x)) ∨
        ((∀ j, j ∉ task.candidateAnswers (C x)) ∧ ∀ j, i ≤ j)} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    by_cases hx : (task.candidateAnswers (C x)).Nonempty
    · have h_none : ¬ ∀ j, j ∉ task.candidateAnswers (C x) := fun h ↦
        let ⟨j, hj⟩ := hx; h j hj
      simp only [task.stickyAnswer_eq_iff hx, h_none, false_and, or_false]
      exact and_congr_right fun _ ↦ ⟨fun h j hji hj ↦ (h j hj).not_gt hji,
        fun h j hj ↦ not_lt.1 fun hji ↦ h j hji hj⟩
    · have h_none : ∀ j, j ∉ task.candidateAnswers (C x) := fun j hj ↦ hx ⟨j, hj⟩
      have h_empty : task.candidateAnswers (C x) = ∅ := not_nonempty_iff_eq_empty.1 hx
      simp only [h_none, not_false_eq_true, and_true, false_or, implies_true, true_and]
      exact ⟨fun h j ↦ h ▸ task.stickyAnswer_le_of_candidateAnswers_eq_empty h_empty j,
        fun h ↦ (task.stickyAnswer_le_of_candidateAnswers_eq_empty h_empty i).antisymm (h _)⟩
  rw [h_eq]
  refine Measurable.setOf (Measurable.or ((hC i).and (Measurable.forall fun j ↦ ?_))
    ((Measurable.forall fun j ↦ (hC j).not).and measurable_const))
  exact measurable_const.imp (hC j).not

/-- The targets `w(i, x)` of the sticky answer `i` of a family of sets of models `C x` are
measurable when membership in the candidate answers and each `w(i, ·)` are measurable, for
finitely many answers. -/
theorem measurable_stickyTarget [Finite ℐ] {β γ : Type*} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {C : β → Set Θ} {w : ℐ → β → γ}
    (hC : ∀ i, Measurable fun x ↦ i ∈ task.candidateAnswers (C x)) (hw : ∀ i, Measurable (w i)) :
    Measurable fun x ↦ w (task.stickyAnswer (C x)) x := by
  let mℐ : MeasurableSpace ℐ := ⊤
  have : MeasurableSingletonClass ℐ := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have : Countable ℐ := Finite.to_countable
  exact (measurable_from_prod_countable_left (f := fun p : β × ℐ ↦ w p.2 p.1) hw).comp
    (measurable_id.prodMk (task.measurable_stickyAnswer hC))

/-! ### The sticky answer near a model -/

variable [TopologicalSpace Θ] {s : Set Θ}

/-- **The sticky answer sticks** [DK19, proof of Theorem 11]. For finitely many answers, if every
value `θ ↦ D(θ, ¬i)` is continuous within `s` at `θ`, then the sticky answer of every small enough
set `C` of models of `s` around `θ` that contains `θ` is the least oracle answer of `θ`: there is
a neighbourhood `U` of `θ` within `s` such that every `C ⊆ U` with `θ ∈ C` has this sticky
answer. -/
theorem eventually_smallSets_stickyAnswer_eq [Finite ℐ]
    (h : ∀ i, ContinuousWithinAt (task.answerValue · i) s θ) :
    ∀ᶠ C in (𝓝[s] θ).smallSets, θ ∈ C → task.stickyAnswer C = task.stickyAnswer {θ} :=
  eventually_smallSets.2 ⟨_, task.eventually_oracleAnswers_subset h,
    fun _ hC hθ ↦ task.stickyAnswer_eq_stickyAnswer_singleton hθ fun _ hθ' ↦ hC hθ'⟩

/-- **The targets of the sticky answer near a model** [DK19, proof of Theorem 11]. For finitely
many answers, let the costs `(θ, w) ↦ D(θ, w, ¬i)` be continuous within `s ×ˢ simplex α` at every
`(θ, w)` with `w` in the simplex, let `i_θ` be the least oracle answer of `θ`, and let the targets
`w(i_θ, θ')` be optimal allocations `w*(θ', ¬i_θ)` for the models `θ'` of `s` near `θ`. Then for
every neighbourhood `V` of `w*(θ, ¬i_θ)`, the targets `w(i, θ')` of the sticky answer `i` of every
small enough set of models of `s` around `θ` that contains `θ`, at every model `θ'` of `s` close
enough to `θ`, are in `V`. -/
theorem eventually_smallSets_prod_stickyTarget_mem [Finite ℐ]
    (h : ∀ i, ∀ w ∈ simplex α, ContinuousWithinAt
      (fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i) (s ×ˢ simplex α) (θ, w))
    {w : ℐ → Θ → α → ℝ}
    (hw : ∀ᶠ θ' in 𝓝[s] θ, w (task.stickyAnswer {θ}) θ' ∈ task.optAlloc θ' (task.stickyAnswer {θ}))
    {V : Set (α → ℝ)} (hV : V ∈ 𝓝ˢ (task.optAlloc θ (task.stickyAnswer {θ}))) :
    ∀ᶠ p in (𝓝[s] θ).smallSets ×ˢ 𝓝[s] θ, θ ∈ p.1 → w (task.stickyAnswer p.1) p.2 ∈ V := by
  have h_uhc := task.upperHemicontinuousWithinAt_optAlloc (i := task.stickyAnswer {θ})
    (h (task.stickyAnswer {θ}))
  rw [upperHemicontinuousWithinAt_iff] at h_uhc
  filter_upwards [(task.eventually_smallSets_stickyAnswer_eq
    fun i ↦ task.continuousWithinAt_answerValue (h i)).prod_mk ((h_uhc V hV).and hw)]
    with p ⟨hp, hV', hw'⟩ hθ
  rw [hp hθ]
  exact subset_of_mem_nhdsSet hV' hw'

end Sticky

/-! ### Confidence regions -/

section ConfidenceRegion

variable [DecidableEq α] (est : (n : ℕ) → Hist Unit α 𝓨 n → Θ)
  (r : (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞) {n : ℕ} {h : Hist Unit α 𝓨 n}

/-- The *confidence region* of [DK19, Algorithm 1] after `n` rounds with history `h`, for the
estimator `est` and the radius `r n h`: the admissible models `λ` whose plug-in statistic
`∑ a, N_a KL(ν_a(θ̂), ν_a(λ))` is at most `r n h`, with `N_a` the number of pulls of the arm `a` in
`h` and `θ̂ = est n h`. For exponential-family arms and the empirical means, these are the models
whose generalized log-likelihood ratio against the maximum-likelihood model is at most `r n h`. -/
def confidenceRegion (n : ℕ) (h : Hist Unit α 𝓨 n) : Set Θ :=
  {θ' | θ' ∈ task.M ∧ task.plugInCost est n h θ' ≤ r n h}

lemma confidenceRegion_def (n : ℕ) (h : Hist Unit α 𝓨 n) :
    task.confidenceRegion est r n h = {θ' | θ' ∈ task.M ∧ task.plugInCost est n h θ' ≤ r n h} :=
  (rfl)

@[simp]
lemma mem_confidenceRegion_iff :
    θ ∈ task.confidenceRegion est r n h ↔ θ ∈ task.M ∧ task.plugInCost est n h θ ≤ r n h :=
  Iff.rfl

lemma confidenceRegion_subset_M : task.confidenceRegion est r n h ⊆ task.M := fun _ hθ ↦ hθ.1

/-- An admissible estimate is in the confidence region, whatever the radius: its plug-in statistic
is `0`. -/
lemma est_mem_confidenceRegion (h_est : est n h ∈ task.M) :
    est n h ∈ task.confidenceRegion est r n h :=
  ⟨h_est, by simp [plugInCost_def, cost_self]⟩

/-- The confidence regions grow with the radius. -/
lemma confidenceRegion_mono {r' : (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞} (hr : r n h ≤ r' n h) :
    task.confidenceRegion est r n h ⊆ task.confidenceRegion est r' n h :=
  fun _ hθ ↦ ⟨hθ.1, hθ.2.trans hr⟩

/-- An admissible model `θ` leaves the confidence region of radius `β` at some round exactly on
the deviation event `∃ n, β n hₙ < ∑ a, N_a KL(ν_a(θ̂), ν_a(θ))` of `θ`, whose probability bounds
the error of the GLRT with the plug-in statistic and thresholds `β`
(`IdentTask.measureReal_histOutputMeasure_glrt_le`). -/
lemma setOf_exists_notMem_confidenceRegion {Ω : Type*} (O : ℕ → Ω → Unit) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → 𝓨) (hθ : θ ∈ task.M) :
    {ω | ∃ n, θ ∉ task.confidenceRegion est r n (history O A Y n ω)} =
      {ω | ∃ n, r n (history O A Y n ω) < task.plugInCost est n (history O A Y n ω) θ} := by
  ext ω
  simp [hθ]

end ConfidenceRegion

/-! ### Sticky Track-and-Stop -/

variable [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] {mℐ : MeasurableSpace ℐ}
  [LinearOrder ℐ] [WellFoundedLT ℐ] [Nonempty ℐ] (est : (n : ℕ) → Hist Unit α 𝓨 n → Θ)

/-- **Sticky Track-and-Stop** [DK19, Algorithm 1], for any task, any estimator `est` of the model
and confidence regions `C n h` of models: the GLRT of the task with the plug-in statistic
`IdentTask.plugInCost est`, thresholds `β`, the recommendation rule `rec` and the C-tracking
sampling rule with targets `w(i_n, θ̂)`, where `θ̂ = est n h` is the estimate of the model and
`i_n = stickyAnswer (C n h)` the sticky answer of the confidence region after `n` rounds with
history `h`. The targets `w(i, θ̂)` are typically optimal allocations `w*(θ̂, ¬i)` of the answer
`i`, and the confidence regions those of `IdentTask.confidenceRegion`. After `n` rounds with
history `h`, it stops if `β n h < GLR_n(h, ¬rec n h)` and then answers `rec n h`. Degenne and
Koolen recommend an answer of largest GLR statistic, so that the algorithm stops as soon as the GLR
statistic of some answer exceeds the threshold. -/
noncomputable def stickyTrackAndStop (C : (n : ℕ) → Hist Unit α 𝓨 n → Set Θ)
    (w : ℐ → Θ → α → ℝ)
    (hw : ∀ n, Measurable fun h : Hist Unit α 𝓨 n ↦ w (task.stickyAnswer (C n h)) (est n h))
    (β : (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞) (rec : (n : ℕ) → Hist Unit α 𝓨 n → ℐ)
    (hrec : ∀ n, Measurable (rec n))
    (hstop : ∀ n, MeasurableSet {h | β n h < task.glr (task.plugInCost est) n h (rec n h)}) :
    IdentAlg Unit α 𝓨 ℐ :=
  task.glrt (task.plugInCost est)
    (cTracking (fun n h ↦ w (task.stickyAnswer (C n h)) (est n h)) hw) β rec hrec hstop

variable {C : (n : ℕ) → Hist Unit α 𝓨 n → Set Θ} {w : ℐ → Θ → α → ℝ}
  {hw : ∀ n, Measurable fun h : Hist Unit α 𝓨 n ↦ w (task.stickyAnswer (C n h)) (est n h)}
  {β : (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞} {rec : (n : ℕ) → Hist Unit α 𝓨 n → ℐ}
  {hrec : ∀ n, Measurable (rec n)}
  {hstop : ∀ n, MeasurableSet {h | β n h < task.glr (task.plugInCost est) n h (rec n h)}}

lemma stickyTrackAndStop_def : task.stickyTrackAndStop est C w hw β rec hrec hstop =
    task.glrt (task.plugInCost est)
      (cTracking (fun n h ↦ w (task.stickyAnswer (C n h)) (est n h)) hw) β rec hrec hstop :=
  (rfl)

/-- The sampling rule of Sticky Track-and-Stop is C-tracking of the targets of the sticky answer
of the confidence region. -/
@[simp]
lemma alg_stickyTrackAndStop : (task.stickyTrackAndStop est C w hw β rec hrec hstop).alg =
    cTracking (fun n h ↦ w (task.stickyAnswer (C n h)) (est n h)) hw := by
  rw [stickyTrackAndStop_def, alg_glrt]

/-- Sticky Track-and-Stop stops after the history `h` of the first `n` rounds iff the GLR
statistic of the recommendation `rec n h` exceeds the threshold `β n h`. -/
@[simp]
lemma mem_stopSet_stickyTrackAndStop {h : Σ n, Hist Unit α 𝓨 n} :
    h ∈ (task.stickyTrackAndStop est C w hw β rec hrec hstop).stopSet ↔
      β h.1 h.2 < task.glr (task.plugInCost est) h.1 h.2 (rec h.1 h.2) := by
  rw [stickyTrackAndStop_def, mem_stopSet_glrt]

/-- Sticky Track-and-Stop answers the recommendation `rec`. -/
@[simp]
lemma output_stickyTrackAndStop (h : Σ n, Hist Unit α 𝓨 n) :
    (task.stickyTrackAndStop est C w hw β rec hrec hstop).output h =
      Measure.dirac (rec h.1 h.2) := by
  rw [stickyTrackAndStop_def, output_glrt]

/-- **Sticky Track-and-Stop is `δ`-PAC** [DK19, Theorem 10], whatever its confidence regions, its
targets and its recommendation rule: if on every admissible model `θ` the deviation event
`∃ n, β n hₙ < ∑ a, N_a KL(ν_a(θ̂), ν_a(θ))` has probability at most `δ` and the algorithm stops
almost surely, then it is `δ`-PAC on the task. By
`IdentTask.setOf_exists_notMem_confidenceRegion`, the deviation event is the event that `θ` leaves
the confidence region of radius `β` at some round. -/
theorem isDeltaPAC_stickyTrackAndStop {δ : ℝ} (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (hdev : ∀ θ ∈ task.M, (trajMeasure (task.stickyTrackAndStop est C w hw β rec hrec hstop).alg
      (Environment.bandit (task.ν θ))).real
      {ω | ∃ n, β n (history IT.obs IT.action IT.feedback n ω) <
        task.plugInCost est n (history IT.obs IT.action IT.feedback n ω) θ} ≤ δ)
    (h_stops : ∀ θ ∈ task.M, StopsAS (task.stickyTrackAndStop est C w hw β rec hrec hstop)
      (Environment.bandit (task.ν θ))) :
    task.IsDeltaPAC (task.stickyTrackAndStop est C w hw β rec hrec hstop) δ := by
  simp only [alg_stickyTrackAndStop] at hdev
  exact task.isDeltaPAC_glrt _ _ β rec hrec hstop hc hdev h_stops

end LMLExplore.Identification.IdentTask

/-! ### Sample complexity -/

namespace LMLExplore.Identification.IdentTask

open Metric Real

open scoped NNReal

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {mℐ : MeasurableSpace ℐ} [LinearOrder ℐ] [Finite ℐ] [Nonempty ℐ]
  (task : IdentTask α (α → ℝ) ℐ ℝ)
  {C : (n : ℕ) → Hist Unit α ℝ n → Set (α → ℝ)} {w : ℐ → (α → ℝ) → α → ℝ}
  {hw : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ w (task.stickyAnswer (C n h)) (empMean' n h)}
  {rec : (n : ℕ) → Hist Unit α ℝ n → ℐ} {hrec : ∀ n, Measurable (rec n)}
  {β : ℝ → (n : ℕ) → Hist Unit α ℝ n → ℝ≥0∞}
  {hstop : ∀ δ n, MeasurableSet
    {h | β δ n h < task.glr (task.plugInCost empMean') n h (rec n h)}}
  {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ}
  {r : ℕ → ℝ} {p : ℝ} {n₀ : ℕ}

/-- **Sample complexity of Sticky Track-and-Stop** [DK19, Theorem 11], for confidence regions that
concentrate. Let the rewards of each arm `a` of the admissible model `μ` be dominated on
`Set.univ` by the member of mean `μ a` of a nondegenerate exponential family `(ρ a, T a)`, and let
`(μ', w') ↦ D(μ', w', ¬i)` be continuous at every `(μ, v)` with `v` in the simplex, on the
allocations of the simplex, for every answer `i`. Let `i_μ` be the least oracle answer of `μ`. Let
the targets be allocations, those of `i_μ` optimal allocations `w(i_μ, μ') ∈ w*(μ', ¬i_μ)` for `μ'`
near `μ`, and let the GLR statistic of the recommendation be at least that of the sticky answer (as
for the sticky answer itself, or an answer of largest GLR statistic). Let the confidence regions
concentrate: for every neighbourhood `U` of `μ`, there are rounds `t₀(T)` with
`log T = o(√t₀(T))` and `t₀(T) = o(T)` such that the probabilities that the confidence region of
some round `t ≥ t₀(T)` does not contain `μ` or is not contained in `U` have a finite sum over `T`.
Then for thresholds `β δ n h ≤ log (r n / δ)` (for `n ≥ n₀`) with `r n = O(n ^ p)`, Sticky
Track-and-Stop with the empirical means as estimator satisfies `𝔼[τ_δ] ≤ c log (1 / δ)` for all
small enough `δ`, for every `c > T*(μ)`: `limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ T*(μ)`, even when
`μ` has several oracle answers. -/
theorem eventually_expectedStoppingTime_stickyTrackAndStop_le
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hμM : μ ∈ task.M)
    (h_cont : ∀ i, ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (μ, v))
    (hw_mem : ∀ i μ', w i μ' ∈ simplex α)
    (hw_opt : ∀ᶠ μ' in 𝓝 μ,
      w (task.stickyAnswer {μ}) μ' ∈ task.optAlloc μ' (task.stickyAnswer {μ}))
    (hrec_glr : ∀ n h, task.glr (task.plugInCost empMean') n h (task.stickyAnswer (C n h)) ≤
      task.glr (task.plugInCost empMean') n h (rec n h))
    (h_conf : ∀ U ∈ 𝓝 μ, ∃ t₀ : ℕ → ℕ,
      Tendsto (fun T : ℕ ↦ √(t₀ T : ℝ) / log T) atTop atTop ∧
      (∀ ε > 0, ∀ᶠ T : ℕ in atTop, (t₀ T : ℝ) ≤ ε * T) ∧
      ∑' T, trajMeasure (cTracking (fun n h ↦ w (task.stickyAnswer (C n h)) (empMean' n h)) hw)
        (Environment.bandit (task.ν μ)) {ω | ∃ t ≥ t₀ T,
          μ ∉ C t (history IT.obs IT.action IT.feedback t ω) ∨
            ¬ C t (history IT.obs IT.action IT.feedback t ω) ⊆ U} ≠ ∞)
    {c : ℝ≥0} (hc : task.charTime μ < c) (hr : r =O[atTop] fun n ↦ (n : ℝ) ^ p)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ n ≥ n₀, ∀ h, β δ n h ≤ ENNReal.ofReal (log (r n / δ))) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime
      (task.stickyTrackAndStop empMean' C w hw (β δ) rec hrec (hstop δ))
      (Environment.bandit (task.ν μ)) ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  -- On good events, from round `t₀(T)` on, the sticky answer is the least oracle answer `i₀` of
  -- `μ` and the targets approach the convex compact set `W = w*(μ, ¬i₀)`, so that the proportions
  -- of pulls of C-tracking approach it. The reduction
  -- `IdentTask.eventually_expectedStoppingTime_glrt_le_of_isBigO` concludes, since
  -- `D(μ, w, ¬i₀) = T*(μ)⁻¹` on `W`.
  set i₀ := task.stickyAnswer {μ}
  set v : (n : ℕ) → Hist Unit α ℝ n → α → ℝ :=
    fun n h ↦ w (task.stickyAnswer (C n h)) (empMean' n h)
  set alg := cTracking v hw
  set P := trajMeasure alg (Environment.bandit (task.ν μ))
  have hseq : IsAlgEnvSeq IT.obs IT.action IT.feedback alg (Environment.bandit (task.ν μ)) P :=
    IT.isAlgEnvSeq_trajMeasure alg _
  set K : ℝ := (Fintype.card α : ℝ)
  have hv0 (n : ℕ) (h : Hist Unit α ℝ n) (a : α) : 0 ≤ v n h a :=
    (mem_simplex_iff.1 (hw_mem _ _)).1 a
  have hv1 (n : ℕ) (h : Hist Unit α ℝ n) : ∑ a, v n h a = 1 := (mem_simplex_iff.1 (hw_mem _ _)).2
  -- The optimal allocations `W = w*(μ, ¬i₀)` form a convex compact set, on which
  -- `D(μ, ·, ¬i₀) = T*(μ)⁻¹`.
  set W := task.optAlloc μ i₀
  have h_usc : UpperSemicontinuousOn (task.altCost μ · i₀) (simplex α) := fun v hv ↦
    ((h_cont i₀ v hv).comp (Continuous.prodMk_right μ).continuousWithinAt
      fun _ hv' ↦ ⟨Set.mem_univ _, hv'⟩).upperSemicontinuousWithinAt
  have hW : IsCompact W := task.isCompact_optAlloc h_usc
  have hc' : (⨅ v ∈ W, task.altCost μ v i₀)⁻¹ < c :=
    (task.inv_iInf_altCost_optAlloc_le_charTime hμM
      (task.stickyAnswer_singleton_mem_oracleAnswers μ)).trans_lt hc
  obtain ⟨κ, hκ, hκc⟩ := ENNReal.exists_nnreal_lt_one_lt_mul_of_inv_lt hc'
  -- The GLR statistic of `i₀` is at least `κ T` when the empirical means are in `U` and the
  -- proportions of pulls are `η`-close to `W`.
  obtain ⟨U, hU, V, hV, hUV⟩ := task.exists_mem_nhds_mul_le_glr_plugInCost empMean'
    (rec := fun _ ↦ i₀) hW
    (fun v hv ↦ (h_cont i₀ v (task.mem_optAlloc_iff.1 hv).1).lowerSemicontinuousWithinAt)
    (fun v hv ↦ hκ.trans_le (iInf₂_le v hv)) (Eventually.of_forall fun _ ↦ rfl)
  obtain ⟨η, hη, hηV⟩ := (hasBasis_nhdsSet_thickening hW).mem_iff.1 hV
  obtain ⟨B, hB, hCB⟩ := hW.isBounded.exists_pos_norm_le
  set ε := η / 4
  have hε : 0 < ε := by positivity
  -- Near `μ`, the sticky answer of the confidence regions is `i₀` and the targets are `ε`-close
  -- to `W`.
  have h_tgt := task.eventually_smallSets_prod_stickyTarget_mem (s := Set.univ) h_cont
    (by rwa [nhdsWithin_univ]) (thickening_mem_nhdsSet W hε)
  rw [nhdsWithin_univ] at h_tgt
  obtain ⟨pa, hpa, pb, hpb, hpab⟩ := eventually_prod_iff.1 h_tgt
  have h_stick := task.eventually_smallSets_stickyAnswer_eq (s := Set.univ)
    fun i ↦ task.continuousWithinAt_answerValue (h_cont i)
  rw [nhdsWithin_univ] at h_stick
  obtain ⟨U₁, hU₁, hU₁pa⟩ := eventually_smallSets.1 (h_stick.and hpa)
  obtain ⟨t₀, ht₀_sqrt, ht₀_le, ht₀_sum⟩ := h_conf U₁ hU₁
  -- The good events of forced exploration: from round `t₀(T)` on, the empirical means are in
  -- `U` and satisfy `pb`, and the pull counts follow the cumulated targets.
  obtain ⟨E, hE_sum, hE⟩ := exists_tsum_measure_compl_ne_top_forall_ge_empMean'_mem
    (O := IT.obs) (t₀ := t₀) hT hμ (fun l u hl hu hlμ hμu ↦
      CTracking.tsum_measure_exists_ge_empMean_notMem_Ioo_ne_top hv0 hv1 hseq hν hμ hl hu hlμ hμu
        ht₀_sqrt)
    (CTracking.abs_pullCount_sub_sum_le_mul_one_add_sqrt hv0 hv1 hseq) (inter_mem hU hpb)
  -- The good events of Sticky Track-and-Stop add the concentration of the confidence regions.
  set F : ℕ → Set (ℕ → Round Unit α ℝ) := fun T ↦ E T ∩ {ω | ∀ t ≥ t₀ T,
    μ ∈ C t (history IT.obs IT.action IT.feedback t ω) ∧
      C t (history IT.obs IT.action IT.feedback t ω) ⊆ U₁}
  have hF_sum : ∑' T, P (F T)ᶜ ≠ ∞ := by
    have h_le (T : ℕ) : P (F T)ᶜ ≤ P (E T)ᶜ + P {ω | ∃ t ≥ t₀ T,
        μ ∉ C t (history IT.obs IT.action IT.feedback t ω) ∨
          ¬ C t (history IT.obs IT.action IT.feedback t ω) ⊆ U₁} := by
      refine (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
      simp only [F, compl_inter, mem_union, mem_compl_iff, mem_ofPred_eq, not_forall,
        not_and_or] at hω
      obtain hω | ⟨t, ht, hω⟩ := hω
      · exact Or.inl hω
      · exact Or.inr ⟨t, ht, hω⟩
    refine ne_top_of_le_ne_top ?_ (tsum_le_tsum h_le)
    rw [tsum_add]
    exact ENNReal.add_ne_top.2 ⟨hE_sum, ht₀_sum⟩
  -- The tracking error `(K - 1) (1 + √T)` is `o(T)`.
  have h_sqrt : Tendsto (fun T : ℕ ↦ (1 + √(T : ℝ)) / T) atTop (𝓝 0) :=
    tendsto_one_add_sqrt_div_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 ((ht₀_le _ (by positivity : 0 < η / (4 * (1 + B)))).and
    ((ht₀_le 1 one_pos).and ((h_sqrt.eventually_le_const (by positivity : 0 < η / (4 * K))).and
      (eventually_gt_atTop 0))))
  have h := task.eventually_expectedStoppingTime_glrt_le_of_isBigO (task.plugInCost empMean') alg
    rec hrec hstop hseq hF_sum hκc (T₀ := max n₀ T₁) ?_ hr
    (by filter_upwards [hβ] with δ hδ T hT h using hδ T (le_of_max_le_left hT) h)
  · simpa only [stickyTrackAndStop_def] using h
  -- After `T` rounds, on the good event of round `T`, the GLR statistic of the recommendation is
  -- at least that of `i₀`, which is at least `κ T`.
  rintro T hT ω ⟨hωE, hωC⟩
  obtain ⟨h_t₀, h_t₀1, h_sqrt_le, hT0⟩ := hT₁ T (le_of_max_le_right hT)
  obtain ⟨hω_track, hω_W⟩ := hE T ω hωE
  have hT_le : t₀ T ≤ T := by exact_mod_cast h_t₀1.trans_eq (one_mul _)
  -- From round `t₀(T)` on, the targets are `ε`-close to `W`.
  have hv_mem (k : ℕ) (hk : t₀ T ≤ k) :
      v k (history IT.obs IT.action IT.feedback k ω) ∈ thickening ε W := by
    obtain ⟨hμC, hCU⟩ := hωC k hk
    exact hpab (hU₁pa _ hCU).2 (hω_W k hk).2 hμC
  -- The proportions of pulls after `T` rounds are `η`-close to `W`.
  have hN : (fun a ↦ (pullCount IT.action a T ω : ℝ) / T) ∈ thickening η W :=
    pullCount_div_mem_thickening_of_le (fun _ ↦ hw_mem _ _) (task.convex_optAlloc μ i₀) hCB hB.le
      hv_mem (hω_track T) hT_le hT0 h_t₀ h_sqrt_le
  have h_sticky : task.stickyAnswer (C T (history IT.obs IT.action IT.feedback T ω)) = i₀ :=
    (hU₁pa _ (hωC T hT_le).2).1 (hωC T hT_le).1
  calc (κ : ℝ≥0∞) * T
  _ ≤ task.glr (task.plugInCost empMean') T (history IT.obs IT.action IT.feedback T ω) i₀ :=
    hUV T hT0.ne' _ (hω_W T hT_le).1 (hηV (by
      simpa only [pullCount_eq_pullCount' (O := IT.obs) (R' := IT.feedback)] using hN))
  _ = task.glr (task.plugInCost empMean') T (history IT.obs IT.action IT.feedback T ω)
      (task.stickyAnswer (C T (history IT.obs IT.action IT.feedback T ω))) := by rw [h_sticky]
  _ ≤ _ := hrec_glr _ _

end LMLExplore.Identification.IdentTask
