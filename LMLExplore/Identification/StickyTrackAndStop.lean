/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.ExpFamilyThreshold
public import LMLExplore.Identification.MultipleAnswerLowerBound
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
`i_θ`, and its proportions of pulls approach `w*(θ, ¬i_θ)`, on which `D(θ, ·, ¬i_θ) = T*(θ)⁻¹`.
The stopping rule is the GLRT, which is `δ`-PAC for every sampling rule and every recommendation
rule ([DK19, Theorem 10], `IdentTask.isDeltaPAC_stickyTrackAndStop`).

**Sample complexity** [DK19, Theorem 11 and Lemmas 13–17]. For arms dominated by exponential
families and the empirical means as estimator, the probabilistic part is the concentration of the
confidence regions around the true model `μ`. If the radius `r n h` is at least the threshold
`K log (2 n (n + 1)) + x_{(n + 1) ^ (-p)}` of the confidence level `(n + 1) ^ (-p)`, the
time-uniform deviation bound of the plug-in statistic (`Identification/ExpFamilyThreshold.lean`)
shows that `μ` leaves the confidence region at some round `k ≥ k₀` with probability at most
`(k₀ + 1) ^ (-p)` (`IdentTask.measure_exists_ge_notMem_confidenceRegion_le_of_klDiv_le`), which for
`k₀ = ⌈√T⌉` and `p > 2` has a finite sum over `T`. The forced exploration of C-tracking gives every
arm at least `√k / 2` pulls after `k ≥ 16 K²` rounds (`CTracking.sqrt_div_two_le_pullCount`),
so that, if the radius is `o(√k)`, the models of the confidence region are within a relative
entropy tending to `0` of the estimate on every arm (`IdentTask.klDiv_le_of_mem_confidenceRegion`).
When small relative entropies from models close to `μ` lead to models close to `μ`, as for
Gaussian arms, the confidence regions then shrink to `μ` on the good events of the concentration
of the empirical means. On these events, from round `⌈√T⌉` on, the sticky answer is `i_μ` and the
targets are close to `w*(μ, ¬i_μ)`, and the sample-complexity reduction of
`Identification/GLR.lean` gives `𝔼[τ_δ] ≤ c log (1 / δ)` for all small `δ`, for every
`c > T*(μ)`. The radius can be the threshold above itself, which is `O(log n)`
(`eventually_unionBoundThreshold_unionBoundLevel_le_mul_sqrt`).

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
* `IdentTask.klDiv_le_of_mem_confidenceRegion`, `IdentTask.confidenceRegion_subset_of_klDiv_le`:
  the models of a confidence region are close to the estimate on every arm once every arm has many
  pulls, so that the region is in every set containing the models close to the estimate.
* `IdentTask.measure_exists_ge_notMem_confidenceRegion_le_of_klDiv_le` [DK19, Lemma 14]: for arms
  dominated by exponential families, the true model stays in the confidence regions from round `k₀`
  on, except with probability `(k₀ + 1) ^ (-p)`.
* `IdentTask.eventually_expectedStoppingTime_stickyTrackAndStop_le_of_klDiv_le`,
  `IdentTask.eventually_expectedStoppingTime_stickyTrackAndStop_unionBoundThreshold_le_of_klDiv_le`:
  **sample complexity of Sticky Track-and-Stop** [DK19, Theorem 11],
  `limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ T*(μ)`, for thresholds `log (g n / δ)` with
  `g n = O(n ^ q)` and for the thresholds `K log (2 n (n + 1)) + x_δ`.
* `IdentTask.stopsAS_stickyTrackAndStop_unionBoundThreshold_of_klDiv_le`,
  `IdentTask.isDeltaPAC_stickyTrackAndStop_unionBoundThreshold_of_klDiv_le`: with the thresholds
  `K log (2 n (n + 1)) + x_δ`, Sticky Track-and-Stop stops almost surely and is `δ`-PAC for every
  `δ ∈ (0, 1]`.
* `tendsto_expectedStoppingTime_stickyTrackAndStop_unionBoundThreshold_div_log_of_klDiv_le`:
  **asymptotic optimality** [DK19, Theorems 1 and 11], `E_μ[τ_δ] / log (1 / δ) → T*(μ)`, from the
  lower bound of `Identification/MultipleAnswerLowerBound.lean`.

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, Algorithm 1, Proposition 5, Theorems 10 and 11, and supplementary material,
  Appendix G (Lemmas 13–17) and Appendix F, Lemma 30.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Set Filter Topology

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

/-- The sticky answer of a single model is at most each of its oracle answers. -/
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

/-- For countably many answers, the sticky answer of a family `C x` of sets of models is
measurable, for every σ-algebra on the answers, when membership of each answer in the candidate
answers of `C x` is a measurable property of `x`. -/
theorem measurable_stickyAnswer [Countable ℐ] {mℐ : MeasurableSpace ℐ} {β : Type*}
    {mβ : MeasurableSpace β} {C : β → Set Θ}
    (hC : ∀ i, Measurable fun x ↦ i ∈ task.candidateAnswers (C x)) :
    Measurable fun x ↦ task.stickyAnswer (C x) := by
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
countably many answers. -/
theorem measurable_stickyTarget [Countable ℐ] {β γ : Type*} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {C : β → Set Θ} {w : ℐ → β → γ}
    (hC : ∀ i, Measurable fun x ↦ i ∈ task.candidateAnswers (C x)) (hw : ∀ i, Measurable (w i)) :
    Measurable fun x ↦ w (task.stickyAnswer (C x)) x := by
  let mℐ : MeasurableSpace ℐ := ⊤
  have : MeasurableSingletonClass ℐ := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
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

/-- The models of a confidence region are close to the estimate on every arm: if every arm has
been pulled at least `c > 0` times and the radius is at most `c ε`, the relative entropy from the
arm `a` of the estimate `θ̂ = est n h` to the arm `a` of every model of the confidence region is at
most `ε`. -/
lemma klDiv_le_of_mem_confidenceRegion (hθ : θ ∈ task.confidenceRegion est r n h) {c ε : ℝ}
    (hc : 0 < c) (hN : ∀ a, c ≤ pullCount' n h a) (hr : r n h ≤ ENNReal.ofReal (c * ε)) (a : α) :
    klDiv (task.ν (est n h) a) (task.ν θ a) ≤ ENNReal.ofReal ε := by
  have h_le : ENNReal.ofReal c * klDiv (task.ν (est n h) a) (task.ν θ a) ≤
      ENNReal.ofReal c * ENNReal.ofReal ε := calc
    _ ≤ ENNReal.ofReal (pullCount' n h a) * klDiv (task.ν (est n h) a) (task.ν θ a) := by
      gcongr
      exact hN a
    _ ≤ task.plugInCost est n h θ := by
      rw [plugInCost_def, cost_def]
      exact Finset.single_le_sum (f := fun b ↦
        ENNReal.ofReal (pullCount' n h b : ℝ) * klDiv (task.ν (est n h) b) (task.ν θ b))
        (fun _ _ ↦ bot_le) (Finset.mem_univ a)
    _ ≤ ENNReal.ofReal (c * ε) := hθ.2.trans hr
    _ = ENNReal.ofReal c * ENNReal.ofReal ε := ENNReal.ofReal_mul hc.le
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top).1 h_le

/-- A confidence region is in every set `S` that contains the admissible models within relative
entropy `ε` of the estimate `θ̂ = est n h` on every arm, once every arm has been pulled at least
`c > 0` times and the radius is at most `c ε`. -/
lemma confidenceRegion_subset_of_klDiv_le {S : Set Θ} {c ε : ℝ}
    (hS : ∀ θ' ∈ task.M, (∀ a, klDiv (task.ν (est n h) a) (task.ν θ' a) ≤ ENNReal.ofReal ε) →
      θ' ∈ S)
    (hc : 0 < c) (hN : ∀ a, c ≤ pullCount' n h a) (hr : r n h ≤ ENNReal.ofReal (c * ε)) :
    task.confidenceRegion est r n h ⊆ S :=
  fun θ' hθ' ↦ hS θ' hθ'.1 (task.klDiv_le_of_mem_confidenceRegion est r hθ' hc hN hr)

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

/-! ### Sample complexity for arms dominated by exponential families -/

namespace LMLExplore.Identification.IdentTask

open Metric Real

open scoped NNReal

/-- `√⌈√T⌉ ≥ T ^ (1 / 4)` grows faster than `log T`, as the concentration of the empirical means of
C-tracking from round `⌈√T⌉` on requires. -/
private lemma tendsto_sqrt_natCeil_sqrt_div_log :
    Tendsto (fun T : ℕ ↦ √(⌈√(T : ℝ)⌉₊ : ℝ) / log T) atTop atTop := by
  have h_rpow : Tendsto (fun x : ℝ ↦ x ^ (1 / 4 : ℝ) / log x) atTop atTop := by
    have h := (isLittleO_log_rpow_atTop (r := 1 / 4) (by norm_num)).tendsto_div_nhds_zero
    have hpos : ∀ᶠ x : ℝ in atTop, log x / x ^ (1 / 4 : ℝ) ∈ Set.Ioi 0 := by
      filter_upwards [eventually_gt_atTop 1] with x hx
      exact div_pos (log_pos hx) (rpow_pos_of_pos (by linarith) _)
    exact (tendsto_nhdsWithin_iff.2 ⟨h, hpos⟩).inv_tendsto_nhdsGT_zero.congr fun x ↦ by
      rw [Pi.inv_apply, inv_div]
  refine tendsto_atTop_mono' _ ?_ (h_rpow.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_gt_atTop 1] with T hT
  have hT' : (1 : ℝ) < T := by exact_mod_cast hT
  simp only [Function.comp_apply]
  refine div_le_div_of_nonneg_right ?_ (log_pos hT').le
  rw [show (1 / 4 : ℝ) = 1 / 2 * (1 / 2) by norm_num, rpow_mul (by positivity), ← sqrt_eq_rpow,
    ← sqrt_eq_rpow]
  exact sqrt_le_sqrt (Nat.le_ceil _)

/-- The rounds `max ⌈√T⌉ k₁` from which the analysis of Sticky Track-and-Stop controls the run are
`o(T)`. -/
private lemma eventually_max_natCeil_sqrt_le_mul (k₁ : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ T : ℕ in atTop, ((max ⌈√(T : ℝ)⌉₊ k₁ : ℕ) : ℝ) ≤ c * T := by
  have h_sqrt : Tendsto (fun T : ℕ ↦ (1 + √(T : ℝ)) / T) atTop (𝓝 0) :=
    tendsto_one_add_sqrt_div_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [h_sqrt.eventually_le_const hc,
    (tendsto_const_div_atTop_nhds_zero_nat (k₁ : ℝ)).eventually_le_const hc,
    eventually_gt_atTop 0] with T h1 h2 hT0
  have hT : (0 : ℝ) < T := Nat.cast_pos.2 hT0
  rw [div_le_iff₀ hT] at h1 h2
  rw [Nat.cast_max]
  exact max_le ((Nat.ceil_lt_add_one (sqrt_nonneg _)).le.trans (by linarith)) h2

/-- The failure probabilities `(⌈√T⌉ + 1) ^ (-p)` of the confidence regions from round `⌈√T⌉` on
have a finite sum over `T` for `p > 2`. -/
private lemma tsum_ofReal_natCeil_sqrt_add_one_rpow_inv_ne_top {p : ℝ} (hp : 2 < p) :
    ∑' T : ℕ, ENNReal.ofReal (((⌈√(T : ℝ)⌉₊ : ℝ) + 1) ^ p)⁻¹ ≠ ∞ := by
  have hs : Summable fun T : ℕ ↦ (((T : ℝ) + 1) ^ (p / 2))⁻¹ := by
    have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 (by linarith : 1 < p / 2))
    simpa only [Nat.cast_add, Nat.cast_one] using h
  refine ne_top_of_le_ne_top (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hs ▸
    ENNReal.ofReal_ne_top) (tsum_le_tsum fun T ↦ ENNReal.ofReal_le_ofReal ?_)
  -- `√(T + 1) ≤ ⌈√T⌉ + 1`, so `(T + 1) ^ (p / 2) ≤ (⌈√T⌉ + 1) ^ p`.
  refine inv_anti₀ (by positivity) ?_
  have hc : √((T : ℝ) + 1) ≤ ⌈√(T : ℝ)⌉₊ + 1 := by
    rw [sqrt_le_left (by positivity)]
    nlinarith [Nat.le_ceil √(T : ℝ), sq_sqrt (Nat.cast_nonneg (α := ℝ) T),
      sqrt_nonneg (T : ℝ)]
  calc ((T : ℝ) + 1) ^ (p / 2) = √((T : ℝ) + 1) ^ p := by
        rw [sqrt_eq_rpow, ← rpow_mul (by positivity)]
        ring_nf
  _ ≤ _ := rpow_le_rpow (sqrt_nonneg _) hc (by linarith)

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {task : IdentTask α (α → ℝ) ℐ ℝ}
  {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ}
  {r : (n : ℕ) → Hist Unit α ℝ n → ℝ≥0∞} {p : ℝ}

/-- **The true model stays in the confidence regions** [DK19, Lemma 14]. Let the rewards of each
arm `a` of the admissible model `μ` be dominated on `Set.univ`, in moment generating function, by
the member of mean `μ a` of the exponential family `(ρ a, T a)`, and let the relative entropy from
the arms of any vector of means to those of `μ` be at most the extended divergence of the
families. Let the radius `r n h` of the confidence regions of the empirical means be at least the
threshold `K log (2 n (n + 1)) + x_{(n + 1) ^ (-p)}` of the confidence level `(n + 1) ^ (-p)`, for
some `p ≥ 0`. Then along a run of any sampling rule, the probability that `μ` leaves the confidence
region at some round `k ≥ k₀` is at most `(k₀ + 1) ^ (-p)`. -/
theorem measure_exists_ge_notMem_confidenceRegion_le_of_klDiv_le {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ}
    {O : ℕ → Ω → Unit}
    {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} (hμM : μ ∈ task.M)
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hkl : ∀ (μ' : α → ℝ) a,
      klDiv (task.ν μ' a) (task.ν μ a) ≤ (ρ a).expFamilyRate (T a) (μ' a) (μ a))
    (hseq : IsAlgEnvSeq O A R alg (Environment.bandit (task.ν μ)) P) (hp : 0 ≤ p)
    (hr : ∀ (n : ℕ) h, unionBoundThreshold (Fintype.card α)
      (unionBoundLevel (Fintype.card α) (((n : ℝ) + 1) ^ p)⁻¹) n ≤ r n h) (k₀ : ℕ) :
    P {ω | ∃ k ≥ k₀, μ ∉ task.confidenceRegion empMean' r k (history O A R k ω)} ≤
      ENNReal.ofReal (((k₀ : ℝ) + 1) ^ p)⁻¹ := by
  have hδ (k : ℕ) : 0 < (((k : ℝ) + 1) ^ p)⁻¹ := inv_pos.2 (rpow_pos_of_pos (by positivity) p)
  have hδ1 (k : ℕ) : (((k : ℝ) + 1) ^ p)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) k]) hp)
  refine (measure_mono fun ω hω ↦ ?_).trans
    ((measure_exists_unionBoundThreshold_lt_plugInCost_le_of_klDiv_le hμ hν hkl hseq
      (card_le_unionBoundLevel (hδ k₀) (hδ1 k₀))).trans
      (ENNReal.ofReal_le_ofReal (div_pow_mul_exp_sub_unionBoundLevel_le (hδ k₀) (hδ1 k₀))))
  obtain ⟨k, hk, hμk⟩ := hω
  have hlt : r k (history O A R k ω) < task.plugInCost empMean' k (history O A R k ω) μ := by
    simpa [mem_confidenceRegion_iff, hμM] using hμk
  refine ⟨k, lt_of_le_of_lt ((?_ : _ ≤ _).trans (hr k _)) hlt⟩
  -- The level of the confidence level `(k + 1) ^ (-p) ≤ (k₀ + 1) ^ (-p)` is the larger.
  rw [unionBoundThreshold_def, unionBoundThreshold_def]
  refine ENNReal.ofReal_le_ofReal ?_
  gcongr
  exact antitoneOn_unionBoundLevel _ ⟨hδ k, hδ1 k⟩ ⟨hδ k₀, hδ1 k₀⟩
    (inv_anti₀ (rpow_pos_of_pos (by positivity) p) (rpow_le_rpow (by positivity) (by gcongr) hp))

variable [Nonempty α] [LinearOrder ℐ] [WellFoundedLT ℐ] [Nonempty ℐ] {mℐ : MeasurableSpace ℐ}
  {w : ℐ → (α → ℝ) → α → ℝ}
  {hw : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦
    w (task.stickyAnswer (task.confidenceRegion empMean' r n h)) (empMean' n h)}
  {rec : (n : ℕ) → Hist Unit α ℝ n → ℐ} {hrec : ∀ n, Measurable (rec n)}

section GeneralThresholds

variable {β : ℝ → (n : ℕ) → Hist Unit α ℝ n → ℝ≥0∞}
  {hstop : ∀ δ n, MeasurableSet
    {h | β δ n h < task.glr (task.plugInCost empMean') n h (rec n h)}}
  {g : ℕ → ℝ} {q : ℝ} {n₀ : ℕ}

/-- **Sample complexity of Sticky Track-and-Stop** [DK19, Theorem 11 and Lemmas 13–17], for
finitely many answers, arms dominated by exponential families and the empirical means as
estimator. Let the rewards of each arm `a` of the admissible model `μ` be dominated on `Set.univ`
by the member of mean `μ a` of a nondegenerate exponential family `(ρ a, T a)`, and let the
relative entropy from the arms of any vector of means to those of `μ` be at most the extended
divergence of the families. Suppose that
* small relative entropies from a model close to `μ` lead to models close to `μ`: for every
  neighbourhood `U` of `μ` there are a neighbourhood `V` of `μ` and `ε > 0` such that every
  admissible model whose arms are within relative entropy `ε` of those of a model of `V` is in `U`;
* the radii `r n h` of the confidence regions are at least the thresholds
  `K log (2 n (n + 1)) + x_{(n + 1) ^ (-p)}` of the confidence levels `(n + 1) ^ (-p)`, for some
  `p > 2`, and `o(√n)` uniformly in the history;
* the targets `w i μ'` are allocations, and near `μ` the targets of the least oracle answer `i_μ`
  of `μ` are optimal allocations `w*(μ', ¬i_μ)`;
* the recommendation has a GLR statistic at least that of the sticky answer, as for the sticky
  answer itself or for an answer of largest GLR statistic;
* every cost `(μ', w') ↦ D(μ', w', ¬i)` is continuous at every point `(μ, v)` with `v` in the
  simplex, on the allocations of the simplex.

Then for thresholds `β δ n h ≤ log (g n / δ)` (for `n ≥ n₀`) with `g n = O(n ^ q)`, Sticky
Track-and-Stop satisfies `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every `c > T*(μ)`:
`limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ T*(μ)`, even when `μ` has several oracle answers. -/
theorem eventually_expectedStoppingTime_stickyTrackAndStop_le_of_klDiv_le [Finite ℐ]
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hkl : ∀ (μ' : α → ℝ) a,
      klDiv (task.ν μ' a) (task.ν μ a) ≤ (ρ a).expFamilyRate (T a) (μ' a) (μ a))
    (hμM : μ ∈ task.M)
    (h_sep : ∀ U ∈ 𝓝 μ, ∃ V ∈ 𝓝 μ, ∃ ε : ℝ, 0 < ε ∧ ∀ μ' ∈ V, ∀ θ' ∈ task.M,
      (∀ a, klDiv (task.ν μ' a) (task.ν θ' a) ≤ ENNReal.ofReal ε) → θ' ∈ U)
    (hp : 2 < p)
    (hr_ge : ∀ (n : ℕ) h, unionBoundThreshold (Fintype.card α)
      (unionBoundLevel (Fintype.card α) (((n : ℝ) + 1) ^ p)⁻¹) n ≤ r n h)
    (hr_le : ∀ ε > 0, ∀ᶠ n in atTop, ∀ h, r n h ≤ ENNReal.ofReal (ε * √(n : ℝ)))
    (hw_mem : ∀ i μ', w i μ' ∈ simplex α)
    (hw_opt : ∀ᶠ μ' in 𝓝 μ,
      w (task.stickyAnswer {μ}) μ' ∈ task.optAlloc μ' (task.stickyAnswer {μ}))
    (hrec_ge : ∀ n h, task.glr (task.plugInCost empMean') n h
      (task.stickyAnswer (task.confidenceRegion empMean' r n h)) ≤
        task.glr (task.plugInCost empMean') n h (rec n h))
    (h_cont : ∀ i, ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (μ, v))
    {c : ℝ≥0} (hc : task.charTime μ < c) (hg : g =O[atTop] fun n ↦ (n : ℝ) ^ q)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ n ≥ n₀, ∀ h, β δ n h ≤ ENNReal.ofReal (log (g n / δ))) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.stickyTrackAndStop empMean'
      (task.confidenceRegion empMean' r) w hw (β δ) rec hrec (hstop δ))
      (Environment.bandit (task.ν μ)) ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  -- The reduction `IdentTask.eventually_expectedStoppingTime_glrt_le_of_isBigO`: on good events
  -- `E T` with `∑ T, P((E T)ᶜ) < ∞`, the GLR statistic of the recommendation after `T` rounds is
  -- at least `κ T`, for a rate `κ > c⁻¹`. On these events, from round `max ⌈√T⌉ k₁` on, the
  -- confidence regions contain `μ` and are small, so that the sticky answer is the least oracle
  -- answer `i` of `μ` and the targets are close to `w*(μ, ¬i)` [DK19, Lemmas 16–17]; C-tracking
  -- then brings the proportions of pulls close to `w*(μ, ¬i)`.
  set K : ℝ := (Fintype.card α : ℝ)
  have hK : 0 < K := Nat.cast_pos.2 Fintype.card_pos
  set i := task.stickyAnswer {μ}
  set C := task.confidenceRegion empMean' r
  set v : (n : ℕ) → Hist Unit α ℝ n → α → ℝ :=
    fun n h ↦ w (task.stickyAnswer (C n h)) (empMean' n h)
  set alg := cTracking v hw
  set P := trajMeasure alg (Environment.bandit (task.ν μ))
  have hseq : IsAlgEnvSeq IT.obs IT.action IT.feedback alg (Environment.bandit (task.ν μ)) P :=
    IT.isAlgEnvSeq_trajMeasure alg _
  have hv_mem (n : ℕ) (h : Hist Unit α ℝ n) : v n h ∈ simplex α := hw_mem _ _
  have hv0 (n : ℕ) (h : Hist Unit α ℝ n) (a : α) : 0 ≤ v n h a :=
    (mem_simplex_iff.1 (hv_mem n h)).1 a
  have hv1 (n : ℕ) (h : Hist Unit α ℝ n) : ∑ a, v n h a = 1 := (mem_simplex_iff.1 (hv_mem n h)).2
  -- The least oracle answer `i` has value `D(μ, ¬i) = T*(μ)⁻¹`, attained on the compact convex set
  -- `W = w*(μ, ¬i)` of its optimal allocations.
  have hc' : (⨅ v ∈ task.optAlloc μ i, task.altCost μ v i)⁻¹ < c := by
    refine (ENNReal.inv_le_inv.2 (le_iInf₂ fun v hv ↦ (task.mem_optAlloc_iff.1 hv).2.ge)).trans_lt
      ?_
    rwa [(task.mem_oracleAnswers_iff_answerValue_eq_gameValue hμM).1
      (task.stickyAnswer_singleton_mem_oracleAnswers μ), ← charTime_def]
  have hW : IsCompact (task.optAlloc μ i) := task.isCompact_optAlloc fun v hv ↦
    ((h_cont i v hv).comp (Continuous.prodMk_right μ).continuousWithinAt
      fun _ hv' ↦ ⟨Set.mem_univ _, hv'⟩).upperSemicontinuousWithinAt
  -- A rate `κ` with `c⁻¹ < κ < D(μ, v, ¬i)` for `v ∈ W`, and neighbourhoods `U` of `μ` and `V`
  -- of `W` on which the GLR statistic of `i` after `T` rounds is at least `κ T`.
  obtain ⟨κ, hκ, hκc⟩ := ENNReal.exists_nnreal_lt_one_lt_mul_of_inv_lt hc'
  obtain ⟨U, hU, V, hV, hUV⟩ := task.exists_mem_nhds_mul_le_glr_plugInCost empMean' hW
    (fun v hv ↦ (h_cont i v (task.mem_optAlloc_iff.1 hv).1).lowerSemicontinuousWithinAt)
    (fun v hv ↦ hκ.trans_le (iInf₂_le v hv)) (rec := fun _ ↦ i) (Eventually.of_forall fun _ ↦ rfl)
  obtain ⟨η, hη, hηV⟩ := (hasBasis_nhdsSet_thickening hW).mem_iff.1 hV
  obtain ⟨B, hB, hWB⟩ := hW.isBounded.exists_pos_norm_le
  -- The sticky answer sticks: there are neighbourhoods `S` and `{pe}` of `μ` such that for every
  -- set of models `S' ⊆ S` containing `μ` and every estimate in `{pe}`, the sticky answer of `S'`
  -- is `i` and its target is `η / 4`-close to `W`.
  have h_tgt := task.eventually_smallSets_prod_stickyTarget_mem (s := Set.univ) h_cont
    (by rwa [nhdsWithin_univ])
    (thickening_mem_nhdsSet (task.optAlloc μ i) (by positivity : 0 < η / 4))
  have h_ans := task.eventually_smallSets_stickyAnswer_eq (s := Set.univ) (θ := μ)
    fun j ↦ task.continuousWithinAt_answerValue (h_cont j)
  rw [nhdsWithin_univ] at h_tgt h_ans
  obtain ⟨pa, hpa, pe, hpe, hp_tgt⟩ := eventually_prod_iff.1 h_tgt
  obtain ⟨S, hS, hS_sub⟩ := eventually_smallSets.1 (hpa.and h_ans)
  -- The confidence regions around estimates in `V'` are in `S` once the pull counts are at least
  -- `√k / 2` and the radius at most `ε √k / 2`.
  obtain ⟨V', hV', ε, hε, h_sep'⟩ := h_sep S hS
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 ((hr_le (ε / 2) (by positivity)).and
    (eventually_ge_atTop (16 * Fintype.card α ^ 2)))
  -- The good events: from round `⌈√T⌉` on, the run tracks the targets, the empirical means are in
  -- `U ∩ {pe} ∩ V'`, and the confidence regions contain `μ`.
  obtain ⟨E, hE_sum, hE⟩ := exists_tsum_measure_compl_ne_top_forall_ge_empMean'_mem (O := IT.obs)
    (t₀ := fun T ↦ ⌈√(T : ℝ)⌉₊) hT hμ (fun l u hl hu hlμ hμu ↦
      CTracking.tsum_measure_exists_ge_empMean_notMem_Ioo_ne_top hv0 hv1 hseq hν hμ hl hu hlμ hμu
        tendsto_sqrt_natCeil_sqrt_div_log)
    ((CTracking.abs_pullCount_sub_sum_le_mul_one_add_sqrt hv0 hv1 hseq).and
      (CTracking.sqrt_div_two_le_pullCount hv0 hv1 hseq))
    (inter_mem (inter_mem hU hpe) hV')
  set G : ℕ → Set _ := fun T ↦ {ω | ∃ k ≥ ⌈√(T : ℝ)⌉₊,
    μ ∉ C k (history IT.obs IT.action IT.feedback k ω)}
  have hG_sum : ∑' T, P (G T) ≠ ∞ := ne_top_of_le_ne_top
    (tsum_ofReal_natCeil_sqrt_add_one_rpow_inv_ne_top hp) (tsum_le_tsum fun T ↦
      measure_exists_ge_notMem_confidenceRegion_le_of_klDiv_le hμM hμ hν hkl hseq (by linarith)
        hr_ge _)
  -- The tracking error `(K - 1) (1 + √T)` and the rounds `max ⌈√T⌉ k₁` are `o(T)`.
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1
    ((eventually_max_natCeil_sqrt_le_mul k₁ (by positivity : 0 < η / (4 * (1 + B)))).and
      ((eventually_max_natCeil_sqrt_le_mul k₁ one_pos).and
        (((tendsto_one_add_sqrt_div_atTop.comp tendsto_natCast_atTop_atTop).eventually_le_const
          (by positivity : 0 < η / (4 * K))).and (eventually_gt_atTop 0))))
  simp only [stickyTrackAndStop_def]
  refine task.eventually_expectedStoppingTime_glrt_le_of_isBigO (task.plugInCost empMean') alg
    rec hrec hstop hseq (E := fun T ↦ E T ∩ (G T)ᶜ) ?_ hκc (T₀ := max n₀ T₁) ?_ hg
    (by filter_upwards [hβ] with δ hδ T hT h using hδ T (le_of_max_le_left hT) h)
  · refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hE_sum, hG_sum⟩) ?_
    rw [← tsum_add]
    refine tsum_le_tsum fun T ↦ ?_
    rw [compl_inter, compl_compl]
    exact measure_union_le _ _
  intro T hT ω ⟨hωE, hωG⟩
  obtain ⟨h_t₀, hT_le, h_sqrt_le, hT0⟩ := hT₁ T (le_of_max_le_right hT)
  obtain ⟨⟨hω_track, hω_pull⟩, hω_mean⟩ := hE T ω hωE
  set s := max ⌈√(T : ℝ)⌉₊ k₁
  have hsT : s ≤ T := by exact_mod_cast hT_le.trans_eq (one_mul _)
  -- At every round `k ≥ s`, the sticky answer is `i` and the target is `η / 4`-close to `W`.
  have h_round (k : ℕ) (hk : s ≤ k) :
      task.stickyAnswer (C k (history IT.obs IT.action IT.feedback k ω)) = i ∧
        v k (history IT.obs IT.action IT.feedback k ω) ∈
          thickening (η / 4) (task.optAlloc μ i) := by
    have hk₀ : ⌈√(T : ℝ)⌉₊ ≤ k := le_of_max_le_left hk
    obtain ⟨hr_k, hk_large⟩ := hk₁ k (le_of_max_le_right hk)
    have h_mean := hω_mean k hk₀
    have hμC : μ ∈ C k (history IT.obs IT.action IT.feedback k ω) :=
      not_not.1 fun h ↦ hωG ⟨k, hk₀, h⟩
    -- Every arm has at least `√k / 2` pulls, so the confidence region is in `S`.
    have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk_large
    have hN (a : α) : √(k : ℝ) / 2 ≤ pullCount' k (history IT.obs IT.action IT.feedback k ω) a := by
      rw [← pullCount_eq_pullCount' (R' := IT.feedback)]
      exact hω_pull k hk_large a
    have hCS : C k (history IT.obs IT.action IT.feedback k ω) ⊆ S :=
      task.confidenceRegion_subset_of_klDiv_le empMean' r (h_sep' _ h_mean.2) (by positivity) hN
        ((hr_k _).trans_eq (by ring_nf))
    obtain ⟨hpaC, hansC⟩ := hS_sub _ hCS
    exact ⟨hansC hμC, hp_tgt hpaC h_mean.1.2 hμC⟩
  -- After `T` rounds, the proportions of pulls are `η`-close to `W`.
  have hN : (fun a ↦ (pullCount IT.action a T ω : ℝ) / T) ∈ thickening η (task.optAlloc μ i) :=
    pullCount_div_mem_thickening_of_le
      (v := fun k ↦ v k (history IT.obs IT.action IT.feedback k ω)) (fun _ ↦ hv_mem _ _)
      (task.convex_optAlloc μ i) hB hWB (fun k hk ↦ (h_round k hk).2) (hω_track T) hsT hη hT0
      h_sqrt_le h_t₀
  calc (κ : ℝ≥0∞) * T
  _ ≤ task.glr (task.plugInCost empMean') T (history IT.obs IT.action IT.feedback T ω) i :=
    hUV T hT0.ne' _ (hω_mean T (le_of_max_le_left hsT)).1.1
      (by simpa only [pullCount_eq_pullCount' (O := IT.obs) (R' := IT.feedback)] using hηV hN)
  _ = task.glr (task.plugInCost empMean') T (history IT.obs IT.action IT.feedback T ω)
      (task.stickyAnswer (C T (history IT.obs IT.action IT.feedback T ω))) := by
    rw [(h_round T hsT).1]
  _ ≤ _ := hrec_ge T _

end GeneralThresholds

/-! ### Union-bound thresholds -/

variable {hstop : ∀ δ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
    (unionBoundLevel (Fintype.card α) δ) n < task.glr (task.plugInCost empMean') n h (rec n h)}}

/-- **Sample complexity of Sticky Track-and-Stop with the union-bound thresholds**
[DK19, Theorem 11]. Under the assumptions of
`IdentTask.eventually_expectedStoppingTime_stickyTrackAndStop_le_of_klDiv_le` on the model `μ`,
Sticky Track-and-Stop with the thresholds `K log (2 n (n + 1)) + x_δ` satisfies
`𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every `c > T*(μ)`:
`limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ T*(μ)`. -/
theorem eventually_expectedStoppingTime_stickyTrackAndStop_unionBoundThreshold_le_of_klDiv_le
    [Finite ℐ] (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hkl : ∀ (μ' : α → ℝ) a,
      klDiv (task.ν μ' a) (task.ν μ a) ≤ (ρ a).expFamilyRate (T a) (μ' a) (μ a))
    (hμM : μ ∈ task.M)
    (h_sep : ∀ U ∈ 𝓝 μ, ∃ V ∈ 𝓝 μ, ∃ ε : ℝ, 0 < ε ∧ ∀ μ' ∈ V, ∀ θ' ∈ task.M,
      (∀ a, klDiv (task.ν μ' a) (task.ν θ' a) ≤ ENNReal.ofReal ε) → θ' ∈ U)
    (hp : 2 < p)
    (hr_ge : ∀ (n : ℕ) h, unionBoundThreshold (Fintype.card α)
      (unionBoundLevel (Fintype.card α) (((n : ℝ) + 1) ^ p)⁻¹) n ≤ r n h)
    (hr_le : ∀ ε > 0, ∀ᶠ n in atTop, ∀ h, r n h ≤ ENNReal.ofReal (ε * √(n : ℝ)))
    (hw_mem : ∀ i μ', w i μ' ∈ simplex α)
    (hw_opt : ∀ᶠ μ' in 𝓝 μ,
      w (task.stickyAnswer {μ}) μ' ∈ task.optAlloc μ' (task.stickyAnswer {μ}))
    (hrec_ge : ∀ n h, task.glr (task.plugInCost empMean') n h
      (task.stickyAnswer (task.confidenceRegion empMean' r n h)) ≤
        task.glr (task.plugInCost empMean') n h (rec n h))
    (h_cont : ∀ i, ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (μ, v))
    {c : ℝ≥0} (hc : task.charTime μ < c) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.stickyTrackAndStop empMean'
      (task.confidenceRegion empMean' r) w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec (hstop δ)) (Environment.bandit (task.ν μ)) ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  refine eventually_le_mul_ofReal_log_of_rpow_inv (fun c' hc' s hs ↦ ?_) hc
  -- At the confidence level `δ ^ (1 / s)`, the thresholds are at most `log (g n / δ)` with
  -- `g n = (2 n (n + 1)) ^ K`.
  exact eventually_expectedStoppingTime_stickyTrackAndStop_le_of_klDiv_le
    (hstop := fun δ' ↦ hstop (δ' ^ s⁻¹)) hT hμ hν hkl hμM h_sep hp hr_ge hr_le hw_mem hw_opt
    hrec_ge h_cont hc' (isBigO_two_mul_mul_add_one_pow _)
    ((eventually_unionBoundThreshold_rpow_inv_le _ hs).mono fun _ h n hn _ ↦ h n hn)

/-- **Sticky Track-and-Stop with the union-bound thresholds stops almost surely**, with the
thresholds `K log (2 n (n + 1)) + x_δ` of every confidence level `δ ∈ (0, 1]`, on a model `μ` with
`T*(μ) < ∞` that satisfies the assumptions of
`IdentTask.eventually_expectedStoppingTime_stickyTrackAndStop_unionBoundThreshold_le_of_klDiv_le`.
-/
theorem stopsAS_stickyTrackAndStop_unionBoundThreshold_of_klDiv_le [Finite ℐ]
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hkl : ∀ (μ' : α → ℝ) a,
      klDiv (task.ν μ' a) (task.ν μ a) ≤ (ρ a).expFamilyRate (T a) (μ' a) (μ a))
    (hμM : μ ∈ task.M)
    (h_sep : ∀ U ∈ 𝓝 μ, ∃ V ∈ 𝓝 μ, ∃ ε : ℝ, 0 < ε ∧ ∀ μ' ∈ V, ∀ θ' ∈ task.M,
      (∀ a, klDiv (task.ν μ' a) (task.ν θ' a) ≤ ENNReal.ofReal ε) → θ' ∈ U)
    (hp : 2 < p)
    (hr_ge : ∀ (n : ℕ) h, unionBoundThreshold (Fintype.card α)
      (unionBoundLevel (Fintype.card α) (((n : ℝ) + 1) ^ p)⁻¹) n ≤ r n h)
    (hr_le : ∀ ε > 0, ∀ᶠ n in atTop, ∀ h, r n h ≤ ENNReal.ofReal (ε * √(n : ℝ)))
    (hw_mem : ∀ i μ', w i μ' ∈ simplex α)
    (hw_opt : ∀ᶠ μ' in 𝓝 μ,
      w (task.stickyAnswer {μ}) μ' ∈ task.optAlloc μ' (task.stickyAnswer {μ}))
    (hrec_ge : ∀ n h, task.glr (task.plugInCost empMean') n h
      (task.stickyAnswer (task.confidenceRegion empMean' r n h)) ≤
        task.glr (task.plugInCost empMean') n h (rec n h))
    (h_cont : ∀ i, ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (μ, v))
    (h_charTime : task.charTime μ ≠ ∞) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    StopsAS (task.stickyTrackAndStop empMean' (task.confidenceRegion empMean' r) w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec (hstop δ)) (Environment.bandit (task.ν μ)) := by
  have hc : task.charTime μ < (task.charTime μ).toNNReal + 1 := by
    rw [ENNReal.coe_toNNReal h_charTime]
    exact ENNReal.lt_add_right h_charTime one_ne_zero
  have h := eventually_expectedStoppingTime_stickyTrackAndStop_unionBoundThreshold_le_of_klDiv_le
    (hw := hw) (hrec := hrec) (hstop := hstop) hT hμ hν hkl hμM h_sep hp hr_ge hr_le hw_mem hw_opt
    hrec_ge h_cont hc
  simp only [stickyTrackAndStop_def] at h ⊢
  exact stopsAS_glrt_unionBoundThreshold (h.mono fun _ hδ' ↦ ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hδ').frequently hδ hδ1

/-- **Sticky Track-and-Stop for arms dominated by exponential families is `δ`-PAC**
[DK19, Theorems 10–11] for every `δ ∈ (0, 1]`, with the thresholds `K log (2 n (n + 1)) + x_δ`, on
every task with finitely many answers, under the assumptions of
`IdentTask.stopsAS_stickyTrackAndStop_unionBoundThreshold_of_klDiv_le` on every admissible model
`θ`: the exponential families `(ρ a, T a)` are nondegenerate; the rewards of each arm `a` are
dominated on `Set.univ` by the member of mean `θ a` of `(ρ a, T a)`; the relative entropy from the
arms of any vector of means to those of `θ` is at most the extended divergence of the families;
small relative entropies from models close to `θ` lead to models close to `θ`; the radii `r n h` of
the confidence regions are at least the thresholds `K log (2 n (n + 1)) + x_{(n + 1) ^ (-p)}` for
some `p > 2` and `o(√n)` uniformly in the history; the targets are allocations, and those of the
least oracle answer of `θ` are optimal allocations near `θ`; the recommendation has a GLR statistic
at least that of the sticky answer; the costs are continuous at `θ`; and `T*(θ) < ∞`. -/
theorem isDeltaPAC_stickyTrackAndStop_unionBoundThreshold_of_klDiv_le [Finite ℐ]
    [MeasurableSingletonClass ℐ] (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hμ : ∀ θ ∈ task.M, ∀ a, θ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ θ ∈ task.M, ∀ a, MGFDominatedOn id (task.ν θ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (θ a))) Set.univ)
    (hkl : ∀ θ ∈ task.M, ∀ (μ' : α → ℝ) a,
      klDiv (task.ν μ' a) (task.ν θ a) ≤ (ρ a).expFamilyRate (T a) (μ' a) (θ a))
    (h_sep : ∀ θ ∈ task.M, ∀ U ∈ 𝓝 θ, ∃ V ∈ 𝓝 θ, ∃ ε : ℝ, 0 < ε ∧ ∀ μ' ∈ V, ∀ θ' ∈ task.M,
      (∀ a, klDiv (task.ν μ' a) (task.ν θ' a) ≤ ENNReal.ofReal ε) → θ' ∈ U)
    (hp : 2 < p)
    (hr_ge : ∀ (n : ℕ) h, unionBoundThreshold (Fintype.card α)
      (unionBoundLevel (Fintype.card α) (((n : ℝ) + 1) ^ p)⁻¹) n ≤ r n h)
    (hr_le : ∀ ε > 0, ∀ᶠ n in atTop, ∀ h, r n h ≤ ENNReal.ofReal (ε * √(n : ℝ)))
    (hw_mem : ∀ i μ', w i μ' ∈ simplex α)
    (hw_opt : ∀ θ ∈ task.M, ∀ᶠ μ' in 𝓝 θ,
      w (task.stickyAnswer {θ}) μ' ∈ task.optAlloc μ' (task.stickyAnswer {θ}))
    (hrec_ge : ∀ n h, task.glr (task.plugInCost empMean') n h
      (task.stickyAnswer (task.confidenceRegion empMean' r n h)) ≤
        task.glr (task.plugInCost empMean') n h (rec n h))
    (h_cont : ∀ θ ∈ task.M, ∀ i, ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (θ, v))
    (h_charTime : ∀ θ ∈ task.M, task.charTime θ ≠ ∞) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    task.IsDeltaPAC (task.stickyTrackAndStop empMean' (task.confidenceRegion empMean' r) w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec (hstop δ)) δ := by
  have h_stops (θ : α → ℝ) (hθ : θ ∈ task.M) :=
    stopsAS_stickyTrackAndStop_unionBoundThreshold_of_klDiv_le (hw := hw) (hrec := hrec)
      (hstop := hstop) hT (hμ θ hθ) (hν θ hθ) (hkl θ hθ) hθ (h_sep θ hθ) hp
      hr_ge hr_le hw_mem (hw_opt θ hθ) hrec_ge (h_cont θ hθ) (h_charTime θ hθ) hδ hδ1
  simp only [stickyTrackAndStop_def] at h_stops ⊢
  exact isDeltaPAC_glrt_unionBoundThreshold_of_klDiv_le _ _ hδ hδ1 (hstop δ) hμ hν hkl
    (fun θ _ ↦ (Set.toFinite _).measurableSet) h_stops

/-- **Sticky Track-and-Stop is asymptotically optimal** [DK19, Theorems 1 and 11]. Under the
assumptions of `IdentTask.isDeltaPAC_stickyTrackAndStop_unionBoundThreshold_of_klDiv_le`, which
make Sticky Track-and-Stop with the thresholds `K log (2 n (n + 1)) + x_δ` `δ`-PAC, at every
admissible model `μ`, `E_μ[τ_δ] / log (1 / δ) → T*(μ)` as `δ → 0`: its sample complexity
matches the lower bound of tasks with several correct answers
(`IdentTask.eventually_mul_ofReal_log_le_expectedStoppingTime_of_finite`). -/
theorem tendsto_expectedStoppingTime_stickyTrackAndStop_unionBoundThreshold_div_log_of_klDiv_le
    [Finite ℐ] [MeasurableSingletonClass ℐ] (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hμ : ∀ θ ∈ task.M, ∀ a, θ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ θ ∈ task.M, ∀ a, MGFDominatedOn id (task.ν θ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (θ a))) Set.univ)
    (hkl : ∀ θ ∈ task.M, ∀ (μ' : α → ℝ) a,
      klDiv (task.ν μ' a) (task.ν θ a) ≤ (ρ a).expFamilyRate (T a) (μ' a) (θ a))
    (h_sep : ∀ θ ∈ task.M, ∀ U ∈ 𝓝 θ, ∃ V ∈ 𝓝 θ, ∃ ε : ℝ, 0 < ε ∧ ∀ μ' ∈ V, ∀ θ' ∈ task.M,
      (∀ a, klDiv (task.ν μ' a) (task.ν θ' a) ≤ ENNReal.ofReal ε) → θ' ∈ U)
    (hp : 2 < p)
    (hr_ge : ∀ (n : ℕ) h, unionBoundThreshold (Fintype.card α)
      (unionBoundLevel (Fintype.card α) (((n : ℝ) + 1) ^ p)⁻¹) n ≤ r n h)
    (hr_le : ∀ ε > 0, ∀ᶠ n in atTop, ∀ h, r n h ≤ ENNReal.ofReal (ε * √(n : ℝ)))
    (hw_mem : ∀ i μ', w i μ' ∈ simplex α)
    (hw_opt : ∀ θ ∈ task.M, ∀ᶠ μ' in 𝓝 θ,
      w (task.stickyAnswer {θ}) μ' ∈ task.optAlloc μ' (task.stickyAnswer {θ}))
    (hrec_ge : ∀ n h, task.glr (task.plugInCost empMean') n h
      (task.stickyAnswer (task.confidenceRegion empMean' r n h)) ≤
        task.glr (task.plugInCost empMean') n h (rec n h))
    (h_cont : ∀ θ ∈ task.M, ∀ i, ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (θ, v))
    (h_charTime : ∀ θ ∈ task.M, task.charTime θ ≠ ∞) (hμM : μ ∈ task.M) :
    Tendsto (fun δ ↦ expectedStoppingTime (task.stickyTrackAndStop empMean'
      (task.confidenceRegion empMean' r) w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec (hstop δ)) (Environment.bandit (task.ν μ)) / ENNReal.ofReal (log (1 / δ)))
      (𝓝[>] 0) (𝓝 (task.charTime μ)) := by
  refine tendsto_expectedStoppingTime_div_log_of_finite ?_ hμM (Set.toFinite _) fun c hc ↦
    eventually_expectedStoppingTime_stickyTrackAndStop_unionBoundThreshold_le_of_klDiv_le hT
      (hμ μ hμM) (hν μ hμM) (hkl μ hμM) hμM (h_sep μ hμM) hp hr_ge hr_le hw_mem (hw_opt μ hμM)
      hrec_ge (h_cont μ hμM) hc
  filter_upwards [Ioc_mem_nhdsGT one_pos] with δ hδ
  exact (isDeltaPAC_stickyTrackAndStop_unionBoundThreshold_of_klDiv_le hT hμ hν hkl h_sep hp hr_ge
    hr_le hw_mem hw_opt hrec_ge h_cont h_charTime hδ.1 hδ.2).isDeltaCorrect

end LMLExplore.Identification.IdentTask
