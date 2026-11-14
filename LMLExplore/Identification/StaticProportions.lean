/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.CumulativeTracking
public import LMLExplore.Identification.DifficultyRatio
public import LMLExplore.SequentialLearning.StaticAllocation
public import LeanMachineLearning.SequentialLearning.SumRewards

/-!
# Static proportions families and their difficulty in fixed-budget identification

A fixed-budget algorithm with *static proportions* samples the arms with fixed proportions
`w ∈ Δ_K` and recommends an answer computed from the empirical means at the end of the budget.
For arms in exponential families and a regular task, its probability of error `p_{θ,T}` at the
model `θ` satisfies
`log (1 / p_{θ,T}) / T → inf_{λ ∈ Alt(θ)} ∑ a, w a KL(ν_a(λ), ν_a(θ))`, where `Alt(θ)` is the
set of admissible models without a common correct answer with `θ` (`IdentTask.alternatives`)
[D23, Theorem 1; GJ04]. In the exponent the alternative `λ` comes first in the divergence,
unlike in the transportation costs of fixed-confidence identification (`IdentTask.altCost`): the
error is a large deviation of the empirical means of `θ` towards `λ`. The best proportions give the
*static-proportions difficulty*
`H^{sp}(θ) = (sup_{w ∈ Δ_K} inf_{λ ∈ Alt(θ)} ∑ a, w a KL(ν_a(λ), ν_a(θ)))⁻¹`, the baseline
against which [D23] compares the fixed-budget algorithm families.

A *static proportions family* (`IdentTask.IsStaticProportions`) is a fixed-budget algorithm
family that pulls each arm `a` about `T w a` times out of `T` (up to the number `K` of arms) and
recommends `rec μ̂_T` for a recommendation rule `rec` applied to the vector `μ̂_T` of the empirical
means. Cumulative tracking with constant targets realizes one for every positive allocation and
every measurable rule. The static proportions families whose rule is correct at the means of the
admissible models form the class `𝒞^{sp}` of [D23], whose oracle difficulty is `H^{sp}` for arms
in exponential families and a regular task [D23, Theorem 1].

## Main definitions

* `LMLExplore.Identification.IdentTask.staticDifficulty task θ`: the static-proportions
  difficulty `H^{sp}(θ)`.
* `LMLExplore.Identification.IdentTask.IsStaticProportions task rec 𝒜 w`: `𝒜` is a static
  proportions family with proportions `w` and recommendation rule `rec`.
* `LMLExplore.Identification.IdentTask.staticClass task mean`: the class `𝒞^{sp}` of the static
  proportions families with a recommendation rule correct at the means `mean θ` of the admissible
  models.

## Main statements

* `LMLExplore.Identification.IdentTask.inv_staticDifficulty`:
  `H^{sp}(θ)⁻¹ = sup_{w ∈ Δ_K} inf_{λ ∈ Alt(θ)} cost(w, λ, θ)`.
* `LMLExplore.Identification.IdentTask.staticDifficulty_restrict_le`: restricting the admissible
  models can only decrease the static-proportions difficulty.
* `LMLExplore.Identification.IdentTask.staticDifficulty_eq_charTime`: with symmetric divergences,
  the static-proportions difficulty of a single-answer model is its characteristic time.
* `LMLExplore.Identification.IdentTask.exists_isStaticProportions`: for positive proportions and
  a measurable recommendation rule, a static proportions family exists.
* `LMLExplore.Identification.IdentTask.IsStaticProportions.errorProb_eq`: the probability of error
  of a static proportions family is the probability that the recommendation of the empirical means
  is not correct.
* `LMLExplore.Identification.IdentTask.IsStaticProportions.hasLDP_empMean`: for arms whose
  cumulant generating functions are finite near `0`, the laws of the empirical means of a static
  proportions family satisfy the large deviation principle with rate function
  `x ↦ ∑ a, w a I_a(x a)`, for the Cramér rate functions `I_a` of the arms.
* `LMLExplore.Identification.IdentTask.IsStaticProportions.limsup_log_errorProb_div_le`,
  `LMLExplore.Identification.IdentTask.IsStaticProportions.neg_le_liminf_log_errorProb_div`: the
  error exponent of a static proportions family is between the infima of `∑ a, w a I_a(x a)` over
  the interior and over the closure of the set of the vectors `x` whose recommendation `rec x` is
  not correct [GJ04; D23, Theorem 12].
* `LMLExplore.Identification.IdentTask.IsStaticProportions.tendsto_log_errorProb_div`,
  `LMLExplore.Identification.IdentTask.IsStaticProportions.tendsto_errorComplexity`: when the two
  infima agree, the error exponent is their common value `c`, and the error complexity
  `T / log (1 / p_{θ,T})` tends to `c⁻¹`.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019.
* [GJ04] P. Glynn and S. Juneja, *A large deviations perspective on ordinal optimization*,
  Winter Simulation Conference 2004.
* Adapted from the formalization of [D23] in the project `RemyDegenne/Degenne2023Existence`
  (same author).
-/

public section

open MeasureTheory Learning Filter Topology ProbabilityTheory
open TauCeti.Probability (HasLDP)

open scoped ENNReal NNReal

namespace LMLExplore.Identification.IdentTask

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (task : IdentTask α Θ ℐ 𝓨)

/-- The static-proportions difficulty
`H^{sp}(θ) = (sup_{w ∈ Δ_K} inf_{λ ∈ Alt(θ)} ∑ a, w a KL(ν_a(λ), ν_a(θ)))⁻¹` of the model `θ`,
with the alternative `λ` first in the divergence. For arms in exponential families and under the
regularity assumption of [D23, Theorem 1], it is the best asymptotic rate `T / log (1 / p_{θ,T})`
of the static proportions algorithms at `θ`. -/
noncomputable def staticDifficulty (θ : Θ) : ℝ≥0∞ :=
  (⨆ w ∈ simplex α, ⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ)⁻¹

lemma staticDifficulty_def (θ : Θ) :
    task.staticDifficulty θ = (⨆ w ∈ simplex α, ⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ)⁻¹ :=
  (rfl)

/-- The inverse of the static-proportions difficulty is the value
`sup_{w ∈ Δ_K} inf_{λ ∈ Alt(θ)} cost(w, λ, θ)` of the static game. -/
lemma inv_staticDifficulty (θ : Θ) :
    (task.staticDifficulty θ)⁻¹ =
      ⨆ w ∈ simplex α, ⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ := by
  rw [staticDifficulty_def, inv_inv]

/-- Restricting the admissible models removes alternatives, so it can only decrease the
static-proportions difficulty. -/
lemma staticDifficulty_restrict_le (S : Set Θ) (θ : Θ) :
    (task.restrict S).staticDifficulty θ ≤ task.staticDifficulty θ := by
  rw [staticDifficulty_def, staticDifficulty_def, alternatives_restrict, cost_restrict,
    ENNReal.inv_le_inv]
  exact iSup₂_mono fun w _ ↦ biInf_mono Set.inter_subset_left

/-- For a model `θ` with the single correct answer `i`, if the divergences between the arms of `θ`
and those of its alternatives are symmetric (Gaussian arms with known variances), then the
static-proportions difficulty of `θ` is its characteristic time `T*(θ)`. -/
lemma staticDifficulty_eq_charTime {θ : Θ} {i : ℐ} (hi : task.correct θ = {i})
    (hsymm : ∀ θ' ∈ task.alternatives θ, ∀ a,
      InformationTheory.klDiv (task.ν θ' a) (task.ν θ a) =
        InformationTheory.klDiv (task.ν θ a) (task.ν θ' a)) :
    task.staticDifficulty θ = task.charTime θ := by
  rw [staticDifficulty_def, charTime_eq_inv_answerValue _ hi, answerValue_def]
  simp only [altCost_def, ← task.alternatives_eq_alt hi]
  refine congrArg _ (iSup_congr fun w ↦ iSup_congr fun _ ↦
    iInf_congr fun θ' ↦ iInf_congr fun hθ' ↦ ?_)
  simp only [cost_def, hsymm θ' hθ']

end LMLExplore.Identification.IdentTask

/-! ### Static proportions families -/

namespace LMLExplore.Identification.IdentTask

variable {α Θ ℐ : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSpace ℐ]

/-- The family `𝒜` of fixed-budget algorithms is a *static proportions* family with proportions
`w` and recommendation rule `rec`, for a task with real observations: the proportions are positive
and sum to `1`, and for every budget `T`, `𝒜 T` stops after `T` rounds, its numbers of pulls
satisfy `|N_{T,a} - T w a| ≤ K` almost surely on every admissible model, with `K` the number of
arms, and it recommends `rec μ̂_T` for the vector `μ̂_T` of the empirical means [D23, Section 2]. -/
structure IsStaticProportions (task : IdentTask α Θ ℐ ℝ) (rec : (α → ℝ) → ℐ)
    (𝒜 : ℕ → IdentAlg Unit α ℝ ℐ) (w : α → ℝ) : Prop where
  /-- The proportions are positive. -/
  pos : ∀ a, 0 < w a
  /-- The proportions sum to `1`. -/
  sum_eq_one : ∑ a, w a = 1
  /-- The algorithm with budget `T` stops after `T` rounds. -/
  isFixedBudgetFamily : IsFixedBudgetFamily 𝒜
  /-- On every admissible model, the numbers of pulls after `T` rounds are within `K` of
  `T w`. -/
  ae_abs_pullCount_sub_le : ∀ θ ∈ task.M, ∀ T,
    ∀ᵐ h ∂(trajMeasure (𝒜 T).alg (Environment.bandit (task.ν θ))),
      ∀ a, |(pullCount IT.action a T h : ℝ) - T * w a| ≤ Fintype.card α
  /-- The algorithm with budget `T` recommends `rec` of the empirical means after `T` rounds. -/
  outputAt_eq : ∀ T (h : Hist Unit α ℝ T), outputAt (𝒜 T) T h = Measure.dirac (rec (empMean' T h))

/-- The class `𝒞^{sp}` of the static proportions families [D23, Section 2], for a task asking
about the means `mean θ` of its models: the static proportions families with some positive
proportions and some recommendation rule that is correct at the means of the admissible
models. -/
def staticClass (task : IdentTask α Θ ℐ ℝ) (mean : Θ → α → ℝ) : Set (ℕ → IdentAlg Unit α ℝ ℐ) :=
  {𝒜 | ∃ rec : (α → ℝ) → ℐ, (∀ θ ∈ task.M, rec (mean θ) ∈ task.correct θ) ∧
    ∃ w, task.IsStaticProportions rec 𝒜 w}

variable {task : IdentTask α Θ ℐ ℝ} {mean : Θ → α → ℝ} {rec : (α → ℝ) → ℐ}
  {𝒜 : ℕ → IdentAlg Unit α ℝ ℐ} {w : α → ℝ}

/-- The families of the class `𝒞^{sp}` are the static proportions families with a recommendation
rule correct at the means of the admissible models. -/
@[simp]
lemma mem_staticClass_iff : 𝒜 ∈ task.staticClass mean ↔
    ∃ rec : (α → ℝ) → ℐ, (∀ θ ∈ task.M, rec (mean θ) ∈ task.correct θ) ∧
      ∃ w, task.IsStaticProportions rec 𝒜 w :=
  Iff.rfl

/-- A static proportions family whose recommendation rule is correct at the means of the
admissible models belongs to the class of static proportions families. -/
lemma IsStaticProportions.mem_staticClass (h𝒜 : task.IsStaticProportions rec 𝒜 w)
    (hrec : ∀ θ ∈ task.M, rec (mean θ) ∈ task.correct θ) : 𝒜 ∈ task.staticClass mean :=
  ⟨rec, hrec, w, h𝒜⟩

/-- The proportions of a static proportions family form an allocation. -/
lemma IsStaticProportions.mem_simplex (h𝒜 : task.IsStaticProportions rec 𝒜 w) : w ∈ simplex α :=
  mem_simplex_iff.2 ⟨fun a ↦ (h𝒜.pos a).le, h𝒜.sum_eq_one⟩

variable (task) in
/-- **Existence of static proportions families.** For positive proportions `w` summing to `1` and
a measurable recommendation rule `rec`, some family is a static proportions family with
proportions `w` and recommendation rule `rec`: cumulative tracking with the constant targets `w`,
stopped after `T` rounds with the deterministic output `rec μ̂_T` [D23, Section 2; DKM19,
Lemma 7]. -/
theorem exists_isStaticProportions [MeasurableSingletonClass α]
    (hrec : Measurable rec) (hw0 : ∀ a, 0 < w a) (hw1 : ∑ a, w a = 1) :
    ∃ 𝒜, task.IsStaticProportions rec 𝒜 w := by
  have : Nonempty ℐ := ⟨rec 0⟩
  have : Nonempty α := nonempty_of_mem_simplex (mem_simplex_iff.2 ⟨fun a ↦ (hw0 a).le, hw1⟩)
  set alg := cumulativeTracking (fun _ _ ↦ w) (𝓨 := ℝ) fun _ ↦ measurable_const
  have hmeas (T : ℕ) : Measurable fun h : Hist Unit α ℝ T ↦ rec (empMean' T h) :=
    hrec.comp (Measurable.of_eval fun a ↦ measurable_empMean' T a)
  refine ⟨fun T ↦ fixedBudget alg T (ProbabilityTheory.Kernel.deterministic _ (hmeas T)),
    hw0, hw1, isFixedBudgetFamily_iff.2 fun T ↦ isFixedBudget_fixedBudget _ _ _, fun θ _ T ↦ ?_,
    fun T h ↦ ?_⟩
  · -- Cumulative tracking keeps `|N_{T,a} - T w a| ≤ K - 1`.
    rw [alg_fixedBudget]
    filter_upwards [CumulativeTracking.abs_pullCount_sub_sum_le (fun _ _ a ↦ (hw0 a).le)
      (fun _ _ ↦ hw1) (IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit (task.ν θ)))]
      with h hh a
    have := hh T a
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    linarith
  · rw [outputAt_fixedBudget, ProbabilityTheory.Kernel.deterministic_apply]

variable (mean) in
/-- If some measurable recommendation rule is correct at the means of the admissible models, the
class of static proportions families is nonempty. -/
lemma staticClass_nonempty [MeasurableSingletonClass α] [Nonempty α] (hrec : Measurable rec)
    (hcorrect : ∀ θ ∈ task.M, rec (mean θ) ∈ task.correct θ) :
    (task.staticClass mean).Nonempty := by
  obtain ⟨𝒜, h𝒜⟩ := task.exists_isStaticProportions hrec (w := fun _ ↦ (Fintype.card α : ℝ)⁻¹)
    (fun _ ↦ by positivity) (mem_simplex_iff.1 (uniform_mem_simplex α)).2
  exact ⟨𝒜, h𝒜.mem_staticClass hcorrect⟩

/-- The probability of error of a static proportions family at `θ`, when the set of correct
answers of `θ` is measurable: the probability that the recommendation `rec μ̂_T` of the vector of
the empirical means after `T` rounds is not a correct answer of `θ`. The recommendation rule need
not be measurable. -/
lemma IsStaticProportions.errorProb_eq (h𝒜 : task.IsStaticProportions rec 𝒜 w) {θ : Θ}
    (hθ : MeasurableSet (task.correct θ)) (T : ℕ) :
    task.errorProb 𝒜 θ T = trajMeasure (𝒜 T).alg (Environment.bandit (task.ν θ))
      {h | rec (fun a ↦ empMean IT.action IT.feedback a T h) ∉ task.correct θ} := by
  set E := {h : ℕ → Round Unit α ℝ |
    rec (fun a ↦ empMean IT.action IT.feedback a T h) ∉ task.correct θ}
  have hf : Measurable fun h ↦ outputAt (𝒜 T) T (IT.hist T h) (task.correct θ)ᶜ :=
    (ProbabilityTheory.Kernel.measurable_coe _ hθ.compl).comp (IT.measurable_hist T)
  -- The output rule gives the wrong answers the mass `1` on `E` and `0` outside.
  have heq (h : ℕ → Round Unit α ℝ) :
      outputAt (𝒜 T) T (IT.hist T h) (task.correct θ)ᶜ = E.indicator 1 h := by
    have hmean : empMean' T (IT.hist T h) = fun a ↦ empMean IT.action IT.feedback a T h := by
      ext a
      rw [empMean_eq_empMean' (O := IT.obs), IT.history_obs_action_feedback]
    rw [h𝒜.outputAt_eq, Measure.dirac_apply' _ hθ.compl, hmean]
    classical
    simp only [Set.indicator_apply, Set.mem_compl_iff, E, Set.mem_ofPred_eq, Pi.one_apply]
  -- `E` is measurable as the preimage of `1` under the measurable function above, even when
  -- `rec` is not measurable.
  have hE : MeasurableSet E := by
    have : E = (fun h ↦ outputAt (𝒜 T) T (IT.hist T h) (task.correct θ)ᶜ) ⁻¹' {1} := by
      ext h
      rw [Set.mem_preimage, heq, Set.mem_singleton_iff]
      by_cases hh : h ∈ E <;> simp [hh]
    exact this ▸ hf (measurableSet_singleton 1)
  rw [errorProb_def, (h𝒜.isFixedBudgetFamily.isFixedBudget T).outputMeasure_eq,
    Measure.bind_apply hθ.compl (ProbabilityTheory.Kernel.aemeasurable _),
    lintegral_map (ProbabilityTheory.Kernel.measurable_coe _ hθ.compl) (IT.measurable_hist T),
    lintegral_congr heq, lintegral_indicator_one hE]

/-! ### The error exponent of static proportions families -/

variable [MeasurableSingletonClass α] {θ : Θ}

/-- **Large deviations of the empirical means of a static proportions family** [GJ04;
D23, Theorem 12]. If the cumulant generating function of each arm of the admissible model `θ` is
finite on a neighbourhood of `0`, the laws of the vectors of the empirical means after `T` rounds
of a static proportions family with proportions `w` satisfy the large deviation principle with
speed `1 / T` and rate function `x ↦ ∑ a, w a I_a(x a)`, with `I_a` the Cramér rate function of
the law `ν_a(θ)` of arm `a`. -/
theorem IsStaticProportions.hasLDP_empMean (h𝒜 : task.IsStaticProportions rec 𝒜 w)
    (hθ : θ ∈ task.M) (hν : ∀ a, 0 ∈ interior (integrableExpSet id (task.ν θ a))) :
    HasLDP atTop (fun T : ℕ ↦ (T : ℝ≥0)⁻¹)
      (fun T ↦ (trajMeasure (𝒜 T).alg (Environment.bandit (task.ν θ))).map
        fun h a ↦ empMean IT.action IT.feedback a T h)
      (fun x ↦ ∑ a, ENNReal.ofReal (w a) * rateFunction id (task.ν θ a) (x a)) :=
  hasLDP_empMean_rateFunction_of_abs_pullCount_sub_le hν h𝒜.pos (Fintype.card α)
    (fun T ↦ IT.isAlgEnvSeq_trajMeasure (𝒜 T).alg (Environment.bandit (task.ν θ)))
    (h𝒜.ae_abs_pullCount_sub_le θ hθ)

/-- **Upper bound on the error exponent of a static proportions family** [GJ04; D23, Theorem 12].
If the set of correct answers of the admissible model `θ` is measurable and the cumulant generating
function of each of its arms is finite on a neighbourhood of `0`, the probability of error
`p_{θ,T}` of a static proportions family with proportions `w` and recommendation rule `rec`
satisfies `limsup_T (1 / T) log p_{θ,T} ≤ -inf_x ∑ a, w a I_a(x a)`, the infimum over the closure
of the set of the vectors `x` with `rec x` not correct for `θ`, with `I_a` the Cramér rate function
of the law `ν_a(θ)` of arm `a`. -/
theorem IsStaticProportions.limsup_log_errorProb_div_le (h𝒜 : task.IsStaticProportions rec 𝒜 w)
    (hθ : θ ∈ task.M) (hcorrect : MeasurableSet (task.correct θ))
    (hν : ∀ a, 0 ∈ interior (integrableExpSet id (task.ν θ a))) :
    limsup (fun T : ℕ ↦ ENNReal.log (task.errorProb 𝒜 θ T) / T) atTop ≤
      -((⨅ x ∈ closure {x | rec x ∉ task.correct θ},
        ∑ a, ENNReal.ofReal (w a) * rateFunction id (task.ν θ a) (x a) : ℝ≥0∞) : EReal) := by
  have h := (h𝒜.hasLDP_empMean hθ hν).limsup_le_neg_iInf_closure {x | rec x ∉ task.correct θ}
  simp_rw [EReal.coe_nnreal_inv_natCast_mul] at h
  refine le_trans (limsup_le_limsup (Eventually.of_forall fun T ↦ ?_)) h
  -- The error is the event that the empirical means lie in the set where `rec` is not correct.
  rw [h𝒜.errorProb_eq hcorrect]
  exact EReal.div_le_div_right_of_nonneg (by positivity) (ENNReal.log_monotone
    (Measure.le_map_apply
      (measurable_empMean_pi IT.measurable_action IT.measurable_feedback T).aemeasurable
      {x | rec x ∉ task.correct θ}))

/-- **Lower bound on the error exponent of a static proportions family** [GJ04; D23, Theorem 12].
If the set of correct answers of the admissible model `θ` is measurable and the cumulant generating
function of each of its arms is finite on a neighbourhood of `0`, the probability of error
`p_{θ,T}` of a static proportions family with proportions `w` and recommendation rule `rec`
satisfies `-inf_x ∑ a, w a I_a(x a) ≤ liminf_T (1 / T) log p_{θ,T}`, the infimum over the
interior of the set of the vectors `x` with `rec x` not correct for `θ`, with `I_a` the Cramér rate
function of the law `ν_a(θ)` of arm `a`. -/
theorem IsStaticProportions.neg_le_liminf_log_errorProb_div
    (h𝒜 : task.IsStaticProportions rec 𝒜 w) (hθ : θ ∈ task.M)
    (hcorrect : MeasurableSet (task.correct θ))
    (hν : ∀ a, 0 ∈ interior (integrableExpSet id (task.ν θ a))) :
    -((⨅ x ∈ interior {x | rec x ∉ task.correct θ},
        ∑ a, ENNReal.ofReal (w a) * rateFunction id (task.ν θ a) (x a) : ℝ≥0∞) : EReal) ≤
      liminf (fun T : ℕ ↦ ENNReal.log (task.errorProb 𝒜 θ T) / T) atTop := by
  have h := (h𝒜.hasLDP_empMean hθ hν).lower_bound (interior {x | rec x ∉ task.correct θ})
    isOpen_interior
  simp_rw [EReal.coe_nnreal_inv_natCast_mul] at h
  refine h.trans (liminf_le_liminf (Eventually.of_forall fun T ↦ ?_))
  -- The empirical means in the interior of the set where `rec` is not correct give an error.
  rw [h𝒜.errorProb_eq hcorrect, Measure.map_apply
    (measurable_empMean_pi IT.measurable_action IT.measurable_feedback T)
    isOpen_interior.measurableSet]
  exact EReal.div_le_div_right_of_nonneg (by positivity)
    (ENNReal.log_monotone (measure_mono (Set.preimage_mono interior_subset)))

/-- **The error exponent of a static proportions family** [GJ04; D23, Theorem 12]. If moreover the
infima of `x ↦ ∑ a, w a I_a(x a)` over the interior and over the closure of the set of the vectors
`x` with `rec x` not correct for `θ` agree, then `(1 / T) log p_{θ,T}` tends to minus their common
value. -/
theorem IsStaticProportions.tendsto_log_errorProb_div (h𝒜 : task.IsStaticProportions rec 𝒜 w)
    (hθ : θ ∈ task.M) (hcorrect : MeasurableSet (task.correct θ))
    (hν : ∀ a, 0 ∈ interior (integrableExpSet id (task.ν θ a)))
    (h_eq : ⨅ x ∈ interior {x | rec x ∉ task.correct θ},
        ∑ a, ENNReal.ofReal (w a) * rateFunction id (task.ν θ a) (x a) =
      ⨅ x ∈ closure {x | rec x ∉ task.correct θ},
        ∑ a, ENNReal.ofReal (w a) * rateFunction id (task.ν θ a) (x a)) :
    Tendsto (fun T : ℕ ↦ ENNReal.log (task.errorProb 𝒜 θ T) / T) atTop
      (𝓝 (-((⨅ x ∈ closure {x | rec x ∉ task.correct θ},
        ∑ a, ENNReal.ofReal (w a) * rateFunction id (task.ν θ a) (x a) : ℝ≥0∞) : EReal))) :=
  tendsto_of_le_liminf_of_limsup_le (h_eq ▸ h𝒜.neg_le_liminf_log_errorProb_div hθ hcorrect hν)
    (h𝒜.limsup_log_errorProb_div_le hθ hcorrect hν)

/-- **The error complexity of a static proportions family** [D23, Theorem 12]. Under the hypotheses
of `IsStaticProportions.tendsto_log_errorProb_div`, the error complexity `T / log (1 / p_{θ,T})`
tends to the inverse of the error exponent `inf_x ∑ a, w a I_a(x a)`. -/
theorem IsStaticProportions.tendsto_errorComplexity (h𝒜 : task.IsStaticProportions rec 𝒜 w)
    (hθ : θ ∈ task.M) (hcorrect : MeasurableSet (task.correct θ))
    (hν : ∀ a, 0 ∈ interior (integrableExpSet id (task.ν θ a)))
    (h_eq : ⨅ x ∈ interior {x | rec x ∉ task.correct θ},
        ∑ a, ENNReal.ofReal (w a) * rateFunction id (task.ν θ a) (x a) =
      ⨅ x ∈ closure {x | rec x ∉ task.correct θ},
        ∑ a, ENNReal.ofReal (w a) * rateFunction id (task.ν θ a) (x a)) :
    Tendsto (task.errorComplexity 𝒜 θ) atTop
      (𝓝 (⨅ x ∈ closure {x | rec x ∉ task.correct θ},
        ∑ a, ENNReal.ofReal (w a) * rateFunction id (task.ν θ a) (x a))⁻¹) :=
  tendsto_errorComplexity_of_tendsto_log_div
    (h𝒜.tendsto_log_errorProb_div hθ hcorrect hν h_eq)

end LMLExplore.Identification.IdentTask
