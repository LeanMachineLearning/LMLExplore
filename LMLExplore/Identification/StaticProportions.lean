/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.CumulativeTracking
public import LMLExplore.Identification.DifficultyRatio
public import LMLExplore.Identification.Task.Recommendation
public import LMLExplore.Probability.Distributions.ExponentialFamily.RateFunction
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
in exponential families and a regular task [D23, Theorem 1]. For arms in exponential families and
a regular task (samples in the closure of the means, a rule correct at the means of the admissible
models and away from the closure of the means of their alternatives, measurable sets of correct
answers and open sets of means of alternatives), a single static proportions family with
proportions `w` has, at every admissible model, asymptotic error complexity at most
`(min_a w a)⁻¹ H^{sp}(θ)`, hence at most `K H^{sp}(θ)` for uniform sampling [D23, Theorem 5].

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
* `LMLExplore.Identification.IdentTask.IsStaticProportions.hasLDP_empMean_expFamilyRate`: for arms
  in exponential families, the rate function is `x ↦ ∑ a, w a dbar_a(x a, μ a)`, with the
  divergences of the families extended to every level [D23, Theorem 12].
* `IsStaticProportions.neg_iInf_cost_le_liminf_log_errorProb_div`,
  `IsStaticProportions.limsup_log_errorProb_div_le_neg_iInf_cost`,
  `IsStaticProportions.tendsto_errorComplexity_inv_iInf_cost` (in
  `LMLExplore.Identification.IdentTask`):
  for arms in exponential families, a task asking about the means of its models whose alternatives
  have open means, and a recommendation rule correct at the means of the alternatives and at the
  vectors of the closure of the means that are not limits of means of alternatives, the error
  exponent is `inf_{λ ∈ Alt(θ)} ∑ a, w a KL(ν_a(λ), ν_a(θ))` [D23, Theorem 1].
* `LMLExplore.Identification.IdentTask.staticDifficulty_le_oracleDifficulty_staticClass`,
  `LMLExplore.Identification.IdentTask.oracleDifficulty_staticClass_eq_staticDifficulty`: for arms
  in exponential families and a single-answer task with finitely many answers whose answer sets
  have open means, disjoint from the means of their alternatives, with closures covering the
  vectors of means of the families, the oracle difficulty of the class `𝒞^{sp}` is the
  static-proportions difficulty `H^{sp}` [D23, Theorem 1].
* `LMLExplore.Identification.IdentTask.asymptoticRatio_staticDifficulty_le_of_limsup_le`: a family
  whose error complexity at `θ` is asymptotically at most the inverse of the cost of the
  alternatives with `w` has asymptotic difficulty ratio at most `(min_a w a)⁻¹` to `H^{sp}` at `θ`.
* `IsStaticProportions.maxRatio_staticDifficulty_le`,
  `IsStaticProportions.maxRatio_staticDifficulty_le_card` (in
  `LMLExplore.Identification.IdentTask`): for arms in exponential families and a regular task
  (samples in the closure of the means, a rule correct at the means of the admissible models and
  away from the closure of the means of their alternatives, measurable sets of correct answers,
  open sets of means of alternatives), a static proportions family with proportions `w` has
  maximal difficulty ratio at most `(min_a w a)⁻¹` to `H^{sp}`, and uniform sampling at most `K`
  [D23, Theorem 5].

## Implementation notes

[D23, Theorem 1] lets static proportions algorithms recommend an arbitrary extension of the correct
answer function to the vectors of the empirical means; the rate formula fails for some extensions,
as when the empirical means of Bernoulli arms are a vertex of `[0, 1]^K` that is a limit of models
with a single answer. The statements here constrain the recommendation rule at the vectors of the
closure of the means of the families instead, and the rule of
`IdentTask.IsSingleAnswer.exists_measurable_rec` satisfies the constraint. They also assume that
the samples of each family lie in the closure of its means, which [D23] uses implicitly.

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

/-- An alternative to `θ` at finite divergence from `θ` on every arm makes the static-proportions
difficulty of `θ` positive: every allocation pays a finite cost to this alternative. -/
lemma staticDifficulty_ne_zero_of_mem_alternatives {θ θ₀ : Θ} (h₀ : θ₀ ∈ task.alternatives θ)
    (h : ∀ a, InformationTheory.klDiv (task.ν θ₀ a) (task.ν θ a) ≠ ∞) :
    task.staticDifficulty θ ≠ 0 := by
  rw [staticDifficulty_def, ENNReal.inv_ne_zero]
  exact ne_top_of_le_ne_top (iSup_ne_top h)
    (iSup₂_le fun w hw ↦ (iInf₂_le θ₀ h₀).trans (task.cost_le_iSup_klDiv hw θ₀ θ))

/-- **The difficulty ratio to the static-proportions difficulty** [D23, proof of Theorem 5]. Let
the model `θ` have a positive static-proportions difficulty, and let the error complexity of the
family `𝒜` at `θ` be asymptotically at most `L_w⁻¹`, for the cost
`L_w = inf_{λ ∈ Alt(θ)} ∑ a, w a KL(ν_a(λ), ν_a(θ))` of the alternatives with the vector `w`, as
for static proportions `w` (`IsStaticProportions.tendsto_errorComplexity_inv_iInf_cost`). Then
the asymptotic difficulty ratio of `𝒜` at `θ` to the static-proportions difficulty is at most
`(min_a w a)⁻¹`: every allocation `w'` has `(min_a w a) L_{w'} ≤ L_w`. -/
theorem asymptoticRatio_staticDifficulty_le_of_limsup_le {mℐ : MeasurableSpace ℐ}
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} {θ : Θ} {w : α → ℝ} (hθ : task.staticDifficulty θ ≠ 0)
    (h : limsup (task.errorComplexity 𝒜 θ) atTop ≤
      (⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ)⁻¹) :
    task.asymptoticRatio task.staticDifficulty 𝒜 θ ≤ (⨅ a, ENNReal.ofReal (w a))⁻¹ := by
  set m := ⨅ a, ENNReal.ofReal (w a)
  set L := ⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ
  set V := ⨆ w' ∈ simplex α, ⨅ θ' ∈ task.alternatives θ, task.cost w' θ' θ with hV_def
  have hV : V ≠ ∞ := by rwa [staticDifficulty_def, ENNReal.inv_ne_zero] at hθ
  -- `m V ≤ L`: each allocation `w'` costs at most `m⁻¹` times as much as `w`.
  have hmV : m * V ≤ L := by
    simp only [hV_def, ENNReal.mul_iSup]
    refine iSup₂_le fun w' hw' ↦ le_iInf₂ fun θ' hθ' ↦ ?_
    calc m * ⨅ θ'' ∈ task.alternatives θ, task.cost w' θ'' θ ≤ m * task.cost w' θ' θ := by
          gcongr
          exact iInf₂_le θ' hθ'
      _ ≤ task.cost w θ' θ := task.iInf_ofReal_mul_cost_le w hw' θ' θ
  rw [asymptoticRatio_eq_limsup_div hθ, staticDifficulty_def, ENNReal.div_eq_inv_mul, inv_inv,
    ← hV_def]
  rcases eq_or_ne V 0 with hV0 | hV0
  · rw [hV0, zero_mul]
    exact zero_le
  calc V * limsup (task.errorComplexity 𝒜 θ) atTop ≤ V * L⁻¹ := by gcongr
    _ ≤ V * (m * V)⁻¹ := by gcongr
    _ = m⁻¹ := by
      rw [ENNReal.mul_inv (Or.inr hV) (Or.inr hV0), mul_comm m⁻¹, ← mul_assoc,
        ENNReal.mul_inv_cancel hV0 hV, one_mul]

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

/-! ### Arms in exponential families -/

variable {mean : Θ → α → ℝ} {ρ : α → Measure ℝ}

/-- In a static proportions family, once every arm has been pulled, the empirical mean of each arm
stays in any convex set carrying its law: for `T` large, almost surely, the empirical mean of every
arm `a` after `T` rounds lies in the convex set `C a`, if the law of arm `a` of the admissible model
`θ` is concentrated on `C a`. -/
lemma IsStaticProportions.eventually_ae_empMean_mem (h𝒜 : task.IsStaticProportions rec 𝒜 w)
    (hθ : θ ∈ task.M) {C : α → Set ℝ} (hC : ∀ a, Convex ℝ (C a))
    (hν : ∀ a, ∀ᵐ x ∂(task.ν θ a), x ∈ C a) :
    ∀ᶠ T : ℕ in atTop, ∀ᵐ h ∂(trajMeasure (𝒜 T).alg (Environment.bandit (task.ν θ))),
      ∀ a, empMean IT.action IT.feedback a T h ∈ C a := by
  -- For `T` large, `T w a > K`, so every arm has been pulled at least once.
  have hpos : ∀ᶠ T : ℕ in atTop, ∀ a, (Fintype.card α : ℝ) < T * w a :=
    eventually_all.2 fun a ↦ (tendsto_natCast_atTop_atTop.atTop_mul_const (h𝒜.pos a))
      |>.eventually_gt_atTop _
  filter_upwards [hpos] with T hT
  filter_upwards [ae_empMean_mem (IT.isAlgEnvSeq_trajMeasure (𝒜 T).alg _) hC hν,
    h𝒜.ae_abs_pullCount_sub_le θ hθ T] with h hh hN a
  refine hh a T fun h0 ↦ ?_
  have := (abs_le.1 (hN a)).1
  rw [h0, Nat.cast_zero] at this
  linarith [hT a]

omit [DecidableEq α] [MeasurableSpace ℐ] [MeasurableSingletonClass α] in
/-- On the means of exponential families, the static exponent is the cost: if the arms of the
admissible models are the members of exponential families with means `mean θ a`, the sum
`∑ a, w a dbar(mean θ' a, mean θ a)` of the extended divergences is the cost
`∑ a, w a KL(ν_a(θ'), ν_a(θ))`, alternative first. -/
lemma sum_expFamilyRate_mean_eq_cost
    (hmean : ∀ θ ∈ task.M, ∀ a, mean θ a ∈ (ρ a).expFamilyMeans id)
    (hν : ∀ θ ∈ task.M, ∀ a, task.ν θ a = (ρ a).expFamily id ((ρ a).natParam id (mean θ a)))
    {θ' : Θ} (hθ : θ ∈ task.M) (hθ' : θ' ∈ task.M) (w : α → ℝ) :
    ∑ a, ENNReal.ofReal (w a) * (ρ a).expFamilyRate id (mean θ' a) (mean θ a) =
      task.cost w θ' θ := by
  rw [cost_def]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [hν θ' hθ' a, hν θ hθ a, Measure.klDiv_expFamily_natParam (hmean θ' hθ' a) (hmean θ hθ a),
    Measure.expFamilyRate_eq_ofReal_expFamilyDiv (hmean θ' hθ' a) (hmean θ hθ a)]

/-- **Large deviations of the empirical means for arms in exponential families** [D23, Theorem 12].
If arm `a` of the admissible model `θ` is the member of mean `μ a` of the exponential family
generated by `ρ a` with the statistic `id`, the laws of the vectors of the empirical means after `T`
rounds of a static proportions family with proportions `w` satisfy the large deviation principle
with speed `1 / T` and rate function `x ↦ ∑ a, w a dbar_a(x a, μ a)`, with `dbar_a` the divergence
of the family extended to every level (`Measure.expFamilyRate`). -/
theorem IsStaticProportions.hasLDP_empMean_expFamilyRate (h𝒜 : task.IsStaticProportions rec 𝒜 w)
    (hθ : θ ∈ task.M) {μ : α → ℝ} (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans id)
    (hν : ∀ a, task.ν θ a = (ρ a).expFamily id ((ρ a).natParam id (μ a))) :
    HasLDP atTop (fun T : ℕ ↦ (T : ℝ≥0)⁻¹)
      (fun T ↦ (trajMeasure (𝒜 T).alg (Environment.bandit (task.ν θ))).map
        fun h a ↦ empMean IT.action IT.feedback a T h)
      (fun x ↦ ∑ a, ENNReal.ofReal (w a) * (ρ a).expFamilyRate id (x a) (μ a)) := by
  simp only [Measure.expFamilyRate_def, ← hν]
  refine h𝒜.hasLDP_empMean hθ fun a ↦ ?_
  rw [hν a]
  exact Measure.zero_mem_interior_integrableExpSet_expFamily
    (Measure.natParam_mem_interior_integrableExpSet (hμ a))

/-- **Lower bound on the error exponent of static proportions for arms in exponential families**
[D23, proof of Theorem 1]. Let the arms of the admissible models be the members of exponential
families with means `mean θ a`, and let `θ` be an admissible model whose set of correct answers is
measurable and the means of whose alternatives form an open set. A static proportions family with
proportions `w` and a recommendation rule correct at the means of the alternatives to `θ`
satisfies `-inf_{λ ∈ Alt(θ)} ∑ a, w a KL(ν_a(λ), ν_a(θ)) ≤ liminf_T (1 / T) log p_{θ,T}`: it errs
whenever the empirical means are the means of an alternative. -/
theorem IsStaticProportions.neg_iInf_cost_le_liminf_log_errorProb_div
    (h𝒜 : task.IsStaticProportions rec 𝒜 w)
    (hmean : ∀ θ ∈ task.M, ∀ a, mean θ a ∈ (ρ a).expFamilyMeans id)
    (hν : ∀ θ ∈ task.M, ∀ a, task.ν θ a = (ρ a).expFamily id ((ρ a).natParam id (mean θ a)))
    (hrec : ∀ θ' ∈ task.alternatives θ, rec (mean θ') ∈ task.correct θ')
    (hθ : θ ∈ task.M) (hcorrect : MeasurableSet (task.correct θ))
    (hopen : IsOpen (mean '' task.alternatives θ)) :
    -((⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ : ℝ≥0∞) : EReal) ≤
      liminf (fun T : ℕ ↦ ENNReal.log (task.errorProb 𝒜 θ T) / T) atTop := by
  have hν0 (a : α) : 0 ∈ interior (integrableExpSet id (task.ν θ a)) := by
    rw [hν θ hθ a]
    exact Measure.zero_mem_interior_integrableExpSet_expFamily
      (Measure.natParam_mem_interior_integrableExpSet (hmean θ hθ a))
  -- At the means of an alternative `θ'`, the recommendation is correct for `θ'`, hence not for `θ`.
  have hsub : mean '' task.alternatives θ ⊆ interior {x | rec x ∉ task.correct θ} := by
    refine hopen.subset_interior_iff.2 ?_
    rintro _ ⟨θ', hθ', rfl⟩
    exact Set.disjoint_right.1 (task.mem_alternatives_iff.1 hθ').2 (hrec θ' hθ')
  refine (h𝒜.neg_le_liminf_log_errorProb_div hθ hcorrect hν0).trans'
    (EReal.neg_le_neg_iff.2 (EReal.coe_ennreal_le_coe_ennreal_iff.2 ((biInf_mono hsub).trans ?_)))
  -- On the means of the alternatives, the Cramér rate function is the cost.
  rw [iInf_image]
  refine (iInf_congr fun θ' ↦ iInf_congr fun hθ' ↦ ?_).le
  rw [← sum_expFamilyRate_mean_eq_cost hmean hν hθ (task.alternatives_subset_M θ hθ') w]
  simp only [Measure.expFamilyRate_def, ← hν θ hθ]

/-- **Upper bound on the error exponent of static proportions for arms in exponential families**
[D23, proof of Theorem 1]. Let the arms of the admissible models be the members of exponential
families with means `mean θ a`, generated by laws `ρ a` with samples in the closure of their means
under which `id` is not almost everywhere constant. Let `θ` be an admissible model whose set of
correct answers is measurable. A static proportions family with proportions `w` and a
recommendation rule correct for `θ` at every vector of the closure of the means of the families
that is not a limit of means of alternatives to `θ` satisfies
`limsup_T (1 / T) log p_{θ,T} ≤ -inf_{λ ∈ Alt(θ)} ∑ a, w a KL(ν_a(λ), ν_a(θ))`: it errs only when
the empirical means are a limit of means of alternatives, at which the rate function is at least
the infimum by its continuity on the closure of the means. -/
theorem IsStaticProportions.limsup_log_errorProb_div_le_neg_iInf_cost
    (h𝒜 : task.IsStaticProportions rec 𝒜 w) (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hmean : ∀ θ ∈ task.M, ∀ a, mean θ a ∈ (ρ a).expFamilyMeans id)
    (hν : ∀ θ ∈ task.M, ∀ a, task.ν θ a = (ρ a).expFamily id ((ρ a).natParam id (mean θ a)))
    (hrec : ∀ x : α → ℝ, (∀ a, x a ∈ closure ((ρ a).expFamilyMeans id)) →
      x ∉ closure (mean '' task.alternatives θ) → rec x ∈ task.correct θ)
    (hθ : θ ∈ task.M) (hcorrect : MeasurableSet (task.correct θ)) :
    limsup (fun T : ℕ ↦ ENNReal.log (task.errorProb 𝒜 θ T) / T) atTop ≤
      -((⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ : ℝ≥0∞) : EReal) := by
  set C : Set (α → ℝ) := Set.univ.pi fun a ↦ closure ((ρ a).expFamilyMeans id)
  set F := C ∩ closure (mean '' task.alternatives θ)
  have hF : IsClosed F := (isClosed_set_pi fun a _ ↦ isClosed_closure).inter isClosed_closure
  set J : (α → ℝ) → ℝ≥0∞ := fun x ↦ ∑ a, ENNReal.ofReal (w a) * (ρ a).expFamilyRate id (x a)
    (mean θ a)
  -- The rate function is continuous on `C`, so at least the infimum on the limits of means of
  -- alternatives in `C`.
  have hJ : ContinuousOn J C := continuousOn_finsetSum _ fun a _ ↦
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_continuousOn
      ((Measure.continuousOn_expFamilyRate_left (hρ a) (hmean θ hθ a)).comp
        (continuous_apply a).continuousOn fun x hx ↦ hx a (Set.mem_univ a))
  have hJF : ⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ ≤ ⨅ x ∈ F, J x := by
    refine le_iInf₂ fun x hx ↦ ?_
    have hsub : mean '' task.alternatives θ ⊆ C := by
      rintro _ ⟨θ', hθ', rfl⟩ a -
      exact subset_closure (hmean θ' (task.alternatives_subset_M θ hθ') a)
    refine closure_minimal ?_ isClosed_Ici (((hJ x hx.1).mono hsub).mem_closure_image hx.2)
    rintro _ ⟨_, ⟨θ', hθ', rfl⟩, rfl⟩
    calc ⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ ≤ task.cost w θ' θ := iInf₂_le θ' hθ'
      _ = J (mean θ') :=
        (sum_expFamilyRate_mean_eq_cost hmean hν hθ (task.alternatives_subset_M θ hθ') w).symm
  -- For `T` large, the empirical means lie in `C`, and the family errs only when they are in `F`.
  have hle : ∀ᶠ T : ℕ in atTop, task.errorProb 𝒜 θ T ≤
      (trajMeasure (𝒜 T).alg (Environment.bandit (task.ν θ))).map
        (fun h a ↦ empMean IT.action IT.feedback a T h) F := by
    have hC (a : α) : ∀ᵐ x ∂(task.ν θ a), x ∈ closure ((ρ a).expFamilyMeans id) := by
      rw [hν θ hθ a]
      exact (Measure.expFamily_absolutelyContinuous (ρ a) id _).ae_le (hρ_closure a)
    filter_upwards [h𝒜.eventually_ae_empMean_mem hθ
      (fun a ↦ Measure.convex_expFamilyMeans.closure) hC] with T hT
    rw [h𝒜.errorProb_eq hcorrect, Measure.map_apply
      (measurable_empMean_pi IT.measurable_action IT.measurable_feedback T) hF.measurableSet]
    refine measure_mono_ae ?_
    filter_upwards [hT] with h hh herr
    exact ⟨fun a _ ↦ hh a, by_contra fun hcl ↦ herr (hrec _ hh hcl)⟩
  have h := (h𝒜.hasLDP_empMean_expFamilyRate hθ (hmean θ hθ) (hν θ hθ)).limsup_le_neg_iInf_closure F
  simp_rw [EReal.coe_nnreal_inv_natCast_mul] at h
  rw [hF.closure_eq] at h
  refine le_trans (limsup_le_limsup (hle.mono fun T hT ↦ ?_)) (h.trans
    (EReal.neg_le_neg_iff.2 (EReal.coe_ennreal_le_coe_ennreal_iff.2 hJF)))
  exact EReal.div_le_div_right_of_nonneg (by positivity) (ENNReal.log_monotone hT)

/-- **The error complexity of static proportions for arms in exponential families** [D23,
Theorem 1]. Under the hypotheses of `IsStaticProportions.neg_iInf_cost_le_liminf_log_errorProb_div`
and `IsStaticProportions.limsup_log_errorProb_div_le_neg_iInf_cost`, the error complexity
`T / log (1 / p_{θ,T})` of a static proportions family with proportions `w` tends to
`(inf_{λ ∈ Alt(θ)} ∑ a, w a KL(ν_a(λ), ν_a(θ)))⁻¹`. -/
theorem IsStaticProportions.tendsto_errorComplexity_inv_iInf_cost
    (h𝒜 : task.IsStaticProportions rec 𝒜 w) (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hmean : ∀ θ ∈ task.M, ∀ a, mean θ a ∈ (ρ a).expFamilyMeans id)
    (hν : ∀ θ ∈ task.M, ∀ a, task.ν θ a = (ρ a).expFamily id ((ρ a).natParam id (mean θ a)))
    (hrec_alt : ∀ θ' ∈ task.alternatives θ, rec (mean θ') ∈ task.correct θ')
    (hrec : ∀ x : α → ℝ, (∀ a, x a ∈ closure ((ρ a).expFamilyMeans id)) →
      x ∉ closure (mean '' task.alternatives θ) → rec x ∈ task.correct θ)
    (hθ : θ ∈ task.M) (hcorrect : MeasurableSet (task.correct θ))
    (hopen : IsOpen (mean '' task.alternatives θ)) :
    Tendsto (task.errorComplexity 𝒜 θ) atTop
      (𝓝 (⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ)⁻¹) :=
  tendsto_errorComplexity_of_tendsto_log_div (tendsto_of_le_liminf_of_limsup_le
    (h𝒜.neg_iInf_cost_le_liminf_log_errorProb_div hmean hν hrec_alt hθ hcorrect hopen)
    (h𝒜.limsup_log_errorProb_div_le_neg_iInf_cost hρ hρ_closure hmean hν hrec hθ hcorrect))

/-- **The static-proportions difficulty is at most the oracle difficulty of static proportions**
[D23, proof of Theorem 1]. Let the arms of the admissible models be the members of exponential
families with means `mean θ a`, and let `θ` be an admissible model whose set of correct answers is
measurable and the means of whose alternatives form an open set. Then `H^{sp}(θ) ≤ H_{𝒞^{sp}}(θ)`:
every family of the class has proportions in the simplex, and its error complexity is eventually
at least the inverse of its error exponent. -/
theorem staticDifficulty_le_oracleDifficulty_staticClass
    (hmean : ∀ θ ∈ task.M, ∀ a, mean θ a ∈ (ρ a).expFamilyMeans id)
    (hν : ∀ θ ∈ task.M, ∀ a, task.ν θ a = (ρ a).expFamily id ((ρ a).natParam id (mean θ a)))
    (hθ : θ ∈ task.M) (hcorrect : MeasurableSet (task.correct θ))
    (hopen : IsOpen (mean '' task.alternatives θ)) :
    task.staticDifficulty θ ≤ task.oracleDifficulty (task.staticClass mean) θ := by
  refine le_oracleDifficulty_iff.2 fun 𝒜 h𝒜 ↦ ?_
  obtain ⟨rec, hrec, w, h𝒜⟩ := mem_staticClass_iff.1 h𝒜
  calc task.staticDifficulty θ ≤ (⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ)⁻¹ := by
        rw [staticDifficulty_def, ENNReal.inv_le_inv]
        exact le_iSup₂ (f := fun w (_ : w ∈ simplex α) ↦
          ⨅ θ' ∈ task.alternatives θ, task.cost w θ' θ) w h𝒜.mem_simplex
    _ ≤ liminf (task.errorComplexity 𝒜 θ) atTop :=
        inv_le_liminf_errorComplexity_of_neg_le_liminf
          (h𝒜.neg_iInf_cost_le_liminf_log_errorProb_div hmean hν
            (fun θ' hθ' ↦ hrec θ' (task.alternatives_subset_M θ hθ')) hθ hcorrect hopen)
    _ ≤ limsup (task.errorComplexity 𝒜 θ) atTop := liminf_le_limsup

/-- **The oracle difficulty of static proportions for arms in exponential families** [D23,
Theorem 1]. Consider a single-answer task with finitely many answers asking about the means
`mean θ` of its models, whose arms are the members of exponential families with these means,
generated by laws `ρ a` with samples in the closure of their means under which `id` is not almost
everywhere constant. Suppose that the means of the models with correct answer `i` form an open set,
disjoint from the means of the alternatives to `i`, and that the closures of these sets cover the
vectors of means of the families. Then at every admissible model `θ` whose set of correct answers
is measurable, the oracle difficulty of the class of static proportions families is the
static-proportions difficulty
`H^{sp}(θ) = (sup_{w ∈ Δ_K} inf_{λ ∈ Alt(θ)} ∑ a, w a KL(ν_a(λ), ν_a(θ)))⁻¹`.

For a task on the vectors of means (`mean = id`) the disjointness always holds, and these are the
conditions of [D23, Assumption 1] that the proof uses. -/
theorem oracleDifficulty_staticClass_eq_staticDifficulty [Finite ℐ]
    (hsingle : task.IsSingleAnswer) (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hmean : ∀ θ ∈ task.M, ∀ a, mean θ a ∈ (ρ a).expFamilyMeans id)
    (hν : ∀ θ ∈ task.M, ∀ a, task.ν θ a = (ρ a).expFamily id ((ρ a).natParam id (mean θ a)))
    (hopen : ∀ i, IsOpen (mean '' task.answerSet i))
    (hdisj : ∀ i, Disjoint (mean '' task.answerSet i) (mean '' task.alt i))
    (hcover : Set.univ.pi (fun a ↦ (ρ a).expFamilyMeans id) ⊆
      ⋃ i, closure (mean '' task.answerSet i))
    (hθ : θ ∈ task.M) (hcorrect : MeasurableSet (task.correct θ)) :
    task.oracleDifficulty (task.staticClass mean) θ = task.staticDifficulty θ := by
  obtain ⟨i, hi⟩ := task.isSingleAnswer_iff.1 hsingle θ hθ
  have : Nonempty ℐ := ⟨i⟩
  -- The means of the alternatives to `θ` are the union of the means of the other answer sets.
  have hopen_alt : IsOpen (mean '' task.alternatives θ) := by
    rw [task.alternatives_eq_alt hi, hsingle.alt_eq_biUnion_answerSet, Set.image_iUnion₂]
    exact isOpen_iUnion fun j ↦ isOpen_iUnion fun _ ↦ hopen j
  refine le_antisymm ?_
    (staticDifficulty_le_oracleDifficulty_staticClass hmean hν hθ hcorrect hopen_alt)
  -- A measurable recommendation rule correct at the means of the admissible models, and correct
  -- for `θ` at the vectors of the closure of the means that are not limits of alternatives.
  obtain ⟨rec, hrec_meas, hrec⟩ := hsingle.exists_measurable_rec (X := α → ℝ) mean
  have hrec_M (θ' : Θ) (hθ' : θ' ∈ task.M) : rec (mean θ') ∈ task.correct θ' := by
    obtain ⟨j, hj⟩ := task.isSingleAnswer_iff.1 hsingle θ' hθ'
    have hθ'j : θ' ∈ task.answerSet j := task.mem_answerSet_iff.2 ⟨hθ', hj ▸ Set.mem_singleton j⟩
    rw [apply_mean_eq_of_mem_answerSet (hrec j) (hopen j) (hdisj j) hθ'j, hj]
    exact Set.mem_singleton j
  have hrec_θ (x : α → ℝ) (hx : ∀ a, x a ∈ closure ((ρ a).expFamilyMeans id))
      (hxi : x ∉ closure (mean '' task.alternatives θ)) : rec x ∈ task.correct θ := by
    rw [task.alternatives_eq_alt hi] at hxi
    have hxS : x ∈ closure (Set.univ.pi fun a ↦ (ρ a).expFamilyMeans id) := by
      rw [closure_pi_set]
      exact fun a _ ↦ hx a
    rw [hrec i x (hsingle.mem_closure_image_answerSet_of_mem_closure hcover hxS hxi) hxi, hi]
    exact Set.mem_singleton i
  -- For every positive allocation, a static proportions family with this rule attains its
  -- exponent, and the supremum over the positive allocations is the supremum over the simplex.
  rw [staticDifficulty_def, ← task.iSup_pos_iInf_cost_eq]
  simp only [ENNReal.inv_iSup]
  refine le_iInf₂ fun w hw ↦ le_iInf fun hpos ↦ ?_
  obtain ⟨𝒜, h𝒜⟩ := task.exists_isStaticProportions hrec_meas hpos (mem_simplex_iff.1 hw).2
  calc task.oracleDifficulty (task.staticClass mean) θ ≤ limsup (task.errorComplexity 𝒜 θ) atTop :=
        oracleDifficulty_le_limsup (h𝒜.mem_staticClass hrec_M)
    _ = _ := (h𝒜.tendsto_errorComplexity_inv_iInf_cost hρ hρ_closure hmean hν
        (fun θ' hθ' ↦ hrec_M θ' (task.alternatives_subset_M θ hθ')) hrec_θ hθ hcorrect
        hopen_alt).limsup_eq

/-! ### The difficulty ratio of static proportions -/

/-- **The difficulty ratio of static proportions at a model** [D23, Theorem 5]. Under the
hypotheses of `IsStaticProportions.tendsto_errorComplexity_inv_iInf_cost` at the admissible model
`θ`, the asymptotic difficulty ratio at `θ` of a static proportions family with proportions `w` to
the static-proportions difficulty is at most `(min_a w a)⁻¹`. At a model without alternatives, the
family eventually never errs, and the ratio is `0`. -/
theorem IsStaticProportions.asymptoticRatio_staticDifficulty_le
    (h𝒜 : task.IsStaticProportions rec 𝒜 w) (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hmean : ∀ θ ∈ task.M, ∀ a, mean θ a ∈ (ρ a).expFamilyMeans id)
    (hν : ∀ θ ∈ task.M, ∀ a, task.ν θ a = (ρ a).expFamily id ((ρ a).natParam id (mean θ a)))
    (hrec_alt : ∀ θ' ∈ task.alternatives θ, rec (mean θ') ∈ task.correct θ')
    (hrec : ∀ x : α → ℝ, (∀ a, x a ∈ closure ((ρ a).expFamilyMeans id)) →
      x ∉ closure (mean '' task.alternatives θ) → rec x ∈ task.correct θ)
    (hθ : θ ∈ task.M) (hcorrect : MeasurableSet (task.correct θ))
    (hopen : IsOpen (mean '' task.alternatives θ)) :
    task.asymptoticRatio task.staticDifficulty 𝒜 θ ≤ (⨅ a, ENNReal.ofReal (w a))⁻¹ := by
  rcases (task.alternatives θ).eq_empty_or_nonempty with hemp | ⟨θ₀, hθ₀⟩
  · -- Without alternatives, `rec` is correct on the closure of the means, where the empirical
    -- means eventually lie.
    refine (asymptoticRatio_eq_zero_of_eventually_errorProb_eq_zero ?_).trans_le zero_le
    have hC (a : α) : ∀ᵐ x ∂(task.ν θ a), x ∈ closure ((ρ a).expFamilyMeans id) := by
      rw [hν θ hθ a]
      exact (Measure.expFamily_absolutelyContinuous (ρ a) id _).ae_le (hρ_closure a)
    filter_upwards [h𝒜.eventually_ae_empMean_mem hθ
      (fun a ↦ Measure.convex_expFamilyMeans.closure) hC] with T hT
    rw [h𝒜.errorProb_eq hcorrect]
    exact ae_iff.1 (hT.mono fun h hh ↦ hrec _ hh (by simp [hemp]))
  · -- An alternative at finite divergence makes the static-proportions difficulty positive.
    have hθ₀M := task.alternatives_subset_M θ hθ₀
    refine task.asymptoticRatio_staticDifficulty_le_of_limsup_le
      (task.staticDifficulty_ne_zero_of_mem_alternatives hθ₀ fun a ↦ ?_)
      (h𝒜.tendsto_errorComplexity_inv_iInf_cost hρ hρ_closure hmean hν hrec_alt hrec hθ hcorrect
        hopen).limsup_eq.le
    rw [hν θ₀ hθ₀M a, hν θ hθ a, Measure.klDiv_expFamily_natParam (hmean θ₀ hθ₀M a) (hmean θ hθ a)]
    exact ENNReal.ofReal_ne_top

/-- **The maximal difficulty ratio of static proportions** [D23, Theorem 5]. Consider a task
asking about the means `mean θ` of its models, whose arms are the members of exponential families
with these means, generated by laws `ρ a` with samples in the closure of their means under which
`id` is not almost everywhere constant. Let `𝒜` be a static proportions family with proportions
`w` whose recommendation rule is correct at the means of the admissible models and, for each
admissible model `θ`, at the vectors of the closure of the means that are not limits of means of
alternatives to `θ`. If the sets of correct answers are measurable and the means of the
alternatives to each admissible model form an open set, then the maximal difficulty ratio of `𝒜`
to the static-proportions difficulty is at most `(min_a w a)⁻¹`, which is finite.

Under the hypotheses of `oracleDifficulty_staticClass_eq_staticDifficulty`, the
static-proportions difficulty is the oracle difficulty of the class of static proportions
families, against which [D23] states this bound. -/
theorem IsStaticProportions.maxRatio_staticDifficulty_le
    (h𝒜 : task.IsStaticProportions rec 𝒜 w) (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hmean : ∀ θ ∈ task.M, ∀ a, mean θ a ∈ (ρ a).expFamilyMeans id)
    (hν : ∀ θ ∈ task.M, ∀ a, task.ν θ a = (ρ a).expFamily id ((ρ a).natParam id (mean θ a)))
    (hrec_M : ∀ θ ∈ task.M, rec (mean θ) ∈ task.correct θ)
    (hrec : ∀ θ ∈ task.M, ∀ x : α → ℝ, (∀ a, x a ∈ closure ((ρ a).expFamilyMeans id)) →
      x ∉ closure (mean '' task.alternatives θ) → rec x ∈ task.correct θ)
    (hcorrect : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (hopen : ∀ θ ∈ task.M, IsOpen (mean '' task.alternatives θ)) :
    task.maxRatio task.staticDifficulty 𝒜 ≤ (⨅ a, ENNReal.ofReal (w a))⁻¹ := by
  rw [maxRatio_def]
  exact iSup₂_le fun θ hθ ↦ h𝒜.asymptoticRatio_staticDifficulty_le hρ hρ_closure hmean hν
    (fun θ' hθ' ↦ hrec_M θ' (task.alternatives_subset_M θ hθ')) (hrec θ hθ) hθ (hcorrect θ hθ)
    (hopen θ hθ)

/-- **The maximal difficulty ratio of uniform sampling** [D23, Theorem 5]. Under the hypotheses of
`IsStaticProportions.maxRatio_staticDifficulty_le`, a static proportions family with the uniform
proportions `1 / K` has maximal difficulty ratio at most `K` to the static-proportions
difficulty. -/
theorem IsStaticProportions.maxRatio_staticDifficulty_le_card
    (h𝒜 : task.IsStaticProportions rec 𝒜 fun _ ↦ (Fintype.card α : ℝ)⁻¹)
    (hρ : ∀ a c, ¬ id =ᵐ[ρ a] fun _ ↦ c)
    (hρ_closure : ∀ a, ∀ᵐ x ∂(ρ a), x ∈ closure ((ρ a).expFamilyMeans id))
    (hmean : ∀ θ ∈ task.M, ∀ a, mean θ a ∈ (ρ a).expFamilyMeans id)
    (hν : ∀ θ ∈ task.M, ∀ a, task.ν θ a = (ρ a).expFamily id ((ρ a).natParam id (mean θ a)))
    (hrec_M : ∀ θ ∈ task.M, rec (mean θ) ∈ task.correct θ)
    (hrec : ∀ θ ∈ task.M, ∀ x : α → ℝ, (∀ a, x a ∈ closure ((ρ a).expFamilyMeans id)) →
      x ∉ closure (mean '' task.alternatives θ) → rec x ∈ task.correct θ)
    (hcorrect : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (hopen : ∀ θ ∈ task.M, IsOpen (mean '' task.alternatives θ)) :
    task.maxRatio task.staticDifficulty 𝒜 ≤ Fintype.card α := by
  have : Nonempty α := nonempty_of_mem_simplex h𝒜.mem_simplex
  exact (h𝒜.maxRatio_staticDifficulty_le hρ hρ_closure hmean hν hrec_M hrec hcorrect
    hopen).trans_eq (inv_iInf_ofReal_uniform α)

end LMLExplore.Identification.IdentTask
