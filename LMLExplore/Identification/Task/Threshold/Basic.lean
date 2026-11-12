/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.ExpFamily
public import LMLExplore.Identification.Task.Classical
public import LMLExplore.Bandits.Instances
public import LMLExplore.Probability.Distributions.ExponentialFamily.Gaussian

/-!
# The pure exploration game of thresholding and minimum-threshold tasks

For the tasks that compare the means of the arms with a threshold `γ`, the transportation costs
and the characteristic time have closed forms. Let the arm `a` belong to an exponential family
`(ρ a, T a)` with divergence `d_a` in the mean parametrization, so that the transportation cost
from a vector of means `μ` to a vector of means `λ` of the families is
`cost_μ(w, λ) = ∑ a, w a d_a(μ a, λ a)`, and let `γ` be a mean of every family.

* *Thresholding* (`thresholdingTask ν id γ`): the alternatives to the set `S*` of the arms of `μ`
  with mean above `γ` are the vectors in which some arm `a` crossed `γ`. The infimum of their costs
  is approached by moving a single arm to the other side of `γ`, ever closer to `γ`, so that
  `D(μ, w, ¬S*) = min_a w a d_a(μ a, γ)`. The allocation maximizing it is proportional to
  `d_a(μ a, γ)⁻¹`, and `T*(μ) = ∑ a, d_a(μ a, γ)⁻¹`. For Gaussian arms with variance `σ2`,
  `T*(μ) = ∑ a, 2 σ2 / (μ a - γ)²`.
* *Minimum threshold* (`minThresholdTask ν id γ`): if all the means are above `γ` (answer `false`),
  the alternatives are the vectors with some mean below `γ`, and the game is that of thresholding:
  `D(μ, w, ¬false) = min_a w a d_a(μ a, γ)` and `T*(μ) = ∑ a, d_a(μ a, γ)⁻¹`
  [DK19, Lemma 37; KKG18, Lemma 1]. If some mean is below `γ` (answer `true`), the alternatives
  are the vectors with all means above `γ`: every arm with mean at most `γ` has to be moved above
  `γ`, and the infimum of the costs is reached in the limit where these arms are moved to `γ`:
  `D(μ, w, ¬true) = ∑ a, w a d_a(μ a, max (μ a) γ)`, whose supremum over the simplex is
  `D(μ, ¬true) = max_a d_a(μ a, max (μ a) γ)`, and `T*(μ) = (max_a d_a(μ a, max (μ a) γ))⁻¹`. For
  Gaussian arms with a common variance `σ2`, this is `2 σ2 / (μ a₀ - γ)²` for an arm `a₀` of
  smallest mean [DK19, Lemma 38; KKG18, Lemma 1].

The admissible models are the vectors of means of the families, `task.restrict S` with
`S = {λ | ∀ c, λ c ∈ (ρ c).expFamilyMeans (T c)}`, as for best arm identification in
`LMLExplore/Identification/Task/BestArm/Basic.lean`. Each arm has its own family: the arms do not
interact in these tasks. The transportation costs between such vectors of means are computed in
`LMLExplore/Identification/Task/ExpFamily.lean`, and the game of a weighted minimum
`min_a w a c a` is solved by `IdentTask.answerValue_eq_of_altCost_eq_iInf` and
`IdentTask.optAlloc_eq_of_altCost_eq_iInf`.

## Main statements

* `LMLExplore.Identification.mem_alt_thresholdingTask_iff`,
  `LMLExplore.Identification.mem_alt_minThresholdTask_false_iff`,
  `LMLExplore.Identification.mem_alt_minThresholdTask_true_iff`: the alternatives of thresholding
  and of minimum threshold.
* `LMLExplore.Identification.altCost_thresholdingTask_restrict`,
  `LMLExplore.Identification.answerValue_thresholdingTask_restrict`,
  `LMLExplore.Identification.charTime_thresholdingTask_restrict`,
  `LMLExplore.Identification.optAlloc_thresholdingTask_restrict`: for thresholding,
  `D(μ, w, ¬S*) = min_a w a d_a(μ a, γ)`, `D(μ, ¬S*) = (∑ a, d_a(μ a, γ)⁻¹)⁻¹`,
  `T*(μ) = ∑ a, d_a(μ a, γ)⁻¹`, and the only optimal allocation is proportional to
  `d_a(μ a, γ)⁻¹`.
* `LMLExplore.Identification.altCost_thresholdingTask_gaussianBandit`,
  `LMLExplore.Identification.charTime_thresholdingTask_gaussianBandit`: for Gaussian arms,
  `D(μ, w, ¬S*) = min_a w a (μ a - γ)² / (2 σ2)` and `T*(μ) = ∑ a, 2 σ2 / (μ a - γ)²`.
* `LMLExplore.Identification.altCost_minThresholdTask_restrict_false`,
  `LMLExplore.Identification.answerValue_minThresholdTask_restrict_false`,
  `LMLExplore.Identification.charTime_minThresholdTask_restrict_false`,
  `LMLExplore.Identification.optAlloc_minThresholdTask_restrict_false`: the same closed forms for
  minimum threshold when all the means are above `γ` [DK19, Lemma 37].
* `LMLExplore.Identification.altCost_minThresholdTask_restrict_true`,
  `LMLExplore.Identification.answerValue_minThresholdTask_restrict_true`,
  `LMLExplore.Identification.charTime_minThresholdTask_restrict_true`: for minimum threshold,
  `D(μ, w, ¬true) = ∑ a, w a d_a(μ a, max (μ a) γ)`, `D(μ, ¬true) = max_a d_a(μ a, max (μ a) γ)`
  and, when some mean is below `γ`, `T*(μ) = (max_a d_a(μ a, max (μ a) γ))⁻¹` [DK19, Lemma 38].
* `LMLExplore.Identification.charTime_minThresholdTask_gaussianBandit_false`,
  `LMLExplore.Identification.charTime_minThresholdTask_gaussianBandit_true`: for Gaussian arms,
  `T*(μ) = ∑ a, 2 σ2 / (μ a - γ)²` if all the means are above `γ`, and
  `T*(μ) = 2 σ2 / (μ a₀ - γ)²` if the smallest mean `μ a₀` is below `γ`.

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, supplementary material, Appendix H.2, Lemmas 37 and 38.
* [KKG18] E. Kaufmann, W. M. Koolen and A. Garivier, *Sequential test for the lowest mean: from
  Thompson to Murphy sampling*, NeurIPS 2018, Lemma 1.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Measure Set

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α Θ 𝓨 ℐ : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} [Fintype α]
  {ρ : α → Measure 𝓨} {T : α → 𝓨 → ℝ} {γ : ℝ} {μ w : α → ℝ}

/-! ### Thresholding -/

section Thresholding

omit [Fintype α] in
/-- The alternatives to a set of arms `s` in thresholding are the models with no mean equal to `γ`
in which some arm is on the other side of `γ` than `s` prescribes. -/
lemma mem_alt_thresholdingTask_iff (ν : Θ → Kernel α 𝓨) [∀ θ, IsMarkovKernel (ν θ)]
    (mean : Θ → α → ℝ) {s : Finset α} {θ' : Θ} :
    θ' ∈ (thresholdingTask ν mean γ).alt s ↔
      (∀ a, mean θ' a ≠ γ) ∧ ∃ a, ¬ (a ∈ s ↔ γ < mean θ' a) := by
  simp only [IdentTask.mem_alt_iff, M_thresholdingTask, correct_thresholdingTask,
    Set.mem_ofPred_eq, not_forall]

variable (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)]

/-- **The cost of the alternatives in thresholding.** Let the arm laws belong to exponential
families `(ρ a, T a)` with divergences `d_a`, in the sense that
`KL(ν_c(μ), ν_c(μ')) = d_c(μ c, μ' c)` for all vectors of means `μ'` of the families, let `γ` be a
mean of every family and let `μ` be a vector of means of the families with no mean equal to `γ`,
whose correct answer is the set `s` of the arms with mean above `γ`. Then on the vectors of means
of the families, for every nonnegative allocation `w`, `D(μ, w, ¬s) = min_a w a d_a(μ a, γ)`: this
infimum is approached by moving a single arm across `γ`, ever closer to `γ`. -/
theorem altCost_thresholdingTask_restrict (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, μ a ≠ γ) {s : Finset α} (hs : ∀ a, a ∈ s ↔ γ < μ a) (hw : 0 ≤ w) :
    ((thresholdingTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).altCost
        μ w s =
      ⨅ a, ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) γ) := by
  classical
  refine le_antisymm (le_iInf fun a ↦ ?_) ?_
  · -- Upper bound: move the mean of `a` across `γ`, close to `γ`.
    have h_alt {x : ℝ} (hxγ : (γ < x ↔ ¬ γ < μ a)) (hx : x ≠ γ)
        (hxm : x ∈ (ρ a).expFamilyMeans (T a)) :
        Function.update μ a x ∈ ((thresholdingTask ν id γ).restrict
          {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).alt s := by
      rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_thresholdingTask_iff, id_eq]
      refine ⟨⟨(Function.forall_update_iff μ fun _ y ↦ y ≠ γ).2 ⟨hx, fun c _ ↦ hμγ c⟩,
        a, ?_⟩, (Function.forall_update_iff μ fun c y ↦ y ∈ (ρ c).expFamilyMeans (T c)).2
          ⟨hxm, fun c _ ↦ hμ c⟩⟩
      rw [hs a, Function.update_self]
      tauto
    have hm := expFamilyMeans_mem_nhds (hT a) (hγ a)
    rcases (hμγ a).lt_or_gt with ha | ha
    · refine IdentTask.altCost_le_ofReal_mul_of_eventually (l := 𝓝[>] γ) (by simp)
        (fun c ↦ isDivergenceOn_expFamilyDiv (hT c)) hν hw hμ a (hγ a) nhdsWithin_le_nhds ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hm] with x (hx : γ < x) hxm
      exact h_alt (iff_of_true hx ha.not_gt) hx.ne' hxm
    · refine IdentTask.altCost_le_ofReal_mul_of_eventually (l := 𝓝[<] γ) (by simp)
        (fun c ↦ isDivergenceOn_expFamilyDiv (hT c)) hν hw hμ a (hγ a) nhdsWithin_le_nhds ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hm] with x (hx : x < γ) hxm
      exact h_alt (iff_of_false hx.not_gt (not_not.2 ha)) hx.ne hxm
  · -- Lower bound: some arm `a` is on different sides of `γ` in `μ` and `μ'`.
    rw [IdentTask.altCost_def]
    refine le_iInf₂ fun μ' hμ' ↦ ?_
    rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_thresholdingTask_iff, id_eq] at hμ'
    obtain ⟨⟨-, a, ha⟩, hμ'⟩ := hμ'
    rw [hs a] at ha
    have h_mem : γ ∈ uIcc (μ a) (μ' a) := by
      rw [Set.mem_uIcc]
      by_cases h1 : γ < μ a
      · exact Or.inr ⟨not_lt.1 fun h2 ↦ ha (iff_of_true h1 h2), h1.le⟩
      · exact Or.inl ⟨not_lt.1 h1, (lt_of_not_ge fun h2 ↦ ha (iff_of_false h1 h2.not_gt)).le⟩
    exact (iInf_le _ a).trans
      (IdentTask.ofReal_mul_le_cost (by simp) hν hw hμ' a (isDivergenceOn_expFamilyDiv (hT a))
        (hμ a) (hγ a) h_mem)

/-- **The game value of thresholding.** Under the assumptions of
`altCost_thresholdingTask_restrict`, the value of the correct answer `s` is
`D(μ, ¬s) = (∑ a, d_a(μ a, γ)⁻¹)⁻¹`. -/
theorem answerValue_thresholdingTask_restrict
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, μ a ≠ γ) {s : Finset α} (hs : ∀ a, a ∈ s ↔ γ < μ a) :
    ((thresholdingTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).answerValue
        μ s =
      ENNReal.ofReal (∑ a, ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹)⁻¹ :=
  IdentTask.answerValue_eq_of_altCost_eq_iInf _ (fun a ↦ expFamilyDiv_pos (hμ a) (hγ a) (hμγ a))
    fun _ hw ↦ altCost_thresholdingTask_restrict ν hT hγ hμ hν hμγ hs (mem_simplex_iff.1 hw).1

/-- **The optimal allocation of thresholding.** Under the assumptions of
`altCost_thresholdingTask_restrict`, the only optimal allocation of the correct answer `s` is
proportional to `d_a(μ a, γ)⁻¹`. -/
theorem optAlloc_thresholdingTask_restrict [Nonempty α]
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, μ a ≠ γ) {s : Finset α} (hs : ∀ a, a ∈ s ↔ γ < μ a) :
    ((thresholdingTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).optAlloc
        μ s =
      {fun a ↦ ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹ /
        ∑ b, ((ρ b).expFamilyDiv (T b) (μ b) γ)⁻¹} :=
  IdentTask.optAlloc_eq_of_altCost_eq_iInf _ (fun a ↦ expFamilyDiv_pos (hμ a) (hγ a) (hμγ a))
    fun _ hw ↦ altCost_thresholdingTask_restrict ν hT hγ hμ hν hμγ hs (mem_simplex_iff.1 hw).1

/-- **The characteristic time of thresholding.** Under the assumptions of
`altCost_thresholdingTask_restrict`, `T*(μ) = ∑ a, d_a(μ a, γ)⁻¹`. -/
theorem charTime_thresholdingTask_restrict [Nonempty α]
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, μ a ≠ γ) :
    ((thresholdingTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).charTime μ =
      ENNReal.ofReal (∑ a, ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹) := by
  classical
  have hs (a : α) : a ∈ Finset.univ.filter (γ < μ ·) ↔ γ < μ a := by simp
  have hpos := sum_inv_pos fun a ↦ expFamilyDiv_pos (hμ a) (hγ a) (hμγ a)
  rw [IdentTask.charTime_eq_inv_answerValue _
      (by rw [IdentTask.correct_restrict, correct_thresholdingTask_eq_singleton ν id, id_eq]),
    answerValue_thresholdingTask_restrict ν hT hγ hμ hν hμγ hs, ENNReal.ofReal_inv_of_pos hpos,
    inv_inv]

/-! #### Gaussian arms -/

variable [MeasurableSingletonClass α] {σ2 : ℝ≥0}

/-- **The cost of the alternatives in Gaussian thresholding.** For Gaussian arms with a common
variance `σ2 ≠ 0`, a vector of means `μ` with no mean equal to `γ`, whose correct answer is the set
`s` of the arms with mean above `γ`, and a nonnegative allocation `w`,
`D(μ, w, ¬s) = min_a w a (μ a - γ)² / (2 σ2)`. -/
theorem altCost_thresholdingTask_gaussianBandit (hσ2 : σ2 ≠ 0) (hμγ : ∀ a, μ a ≠ γ)
    {s : Finset α} (hs : ∀ a, a ∈ s ↔ γ < μ a) (hw : 0 ≤ w) :
    (thresholdingTask (Bandits.gaussianBandit · σ2) id γ).altCost μ w s =
      ⨅ a, ENNReal.ofReal (w a * (μ a - γ) ^ 2 / (2 * σ2)) := by
  rw [← (thresholdingTask (Bandits.gaussianBandit · σ2) id γ).restrict_univ,
    ← setOf_forall_mem_expFamilyMeans_gaussianReal 0 hσ2,
    altCost_thresholdingTask_restrict (ρ := fun _ ↦ gaussianReal 0 σ2) (T := fun _ ↦ id) _
      (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
      (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (fun μ' _ ↦ Bandits.klDiv_gaussianBandit_eq_ofReal_expFamilyDiv hσ2 μ μ')
      hμγ hs hw]
  simp only [expFamilyDiv_gaussianReal 0 hσ2, mul_div_assoc]

/-- **The characteristic time of Gaussian thresholding.** For Gaussian arms with a common variance
`σ2 ≠ 0` and a vector of means `μ` with no mean equal to `γ`, `T*(μ) = ∑ a, 2 σ2 / (μ a - γ)²`. -/
theorem charTime_thresholdingTask_gaussianBandit [Nonempty α] (hσ2 : σ2 ≠ 0)
    (hμγ : ∀ a, μ a ≠ γ) :
    (thresholdingTask (Bandits.gaussianBandit · σ2) id γ).charTime μ =
      ENNReal.ofReal (∑ a, 2 * σ2 / (μ a - γ) ^ 2) := by
  rw [← (thresholdingTask (Bandits.gaussianBandit · σ2) id γ).restrict_univ,
    ← setOf_forall_mem_expFamilyMeans_gaussianReal 0 hσ2,
    charTime_thresholdingTask_restrict (ρ := fun _ ↦ gaussianReal 0 σ2) (T := fun _ ↦ id) _
      (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
      (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (fun μ' _ ↦ Bandits.klDiv_gaussianBandit_eq_ofReal_expFamilyDiv hσ2 μ μ')
      hμγ]
  simp only [expFamilyDiv_gaussianReal 0 hσ2, inv_div]

end Thresholding

/-! ### Minimum threshold -/

section MinThreshold

section MeanFunctional

variable (ν : Θ → Kernel α 𝓨) [∀ θ, IsMarkovKernel (ν θ)] (mean : Θ → α → ℝ) {θ' : Θ}

omit [Fintype α] in
/-- The alternatives to `false` in minimum threshold are the models with some mean below `γ`. -/
lemma mem_alt_minThresholdTask_false_iff :
    θ' ∈ (minThresholdTask ν mean γ).alt false ↔ ∃ a, mean θ' a < γ := by
  simp only [IdentTask.mem_alt_iff, M_minThresholdTask, correct_minThresholdTask,
    Set.mem_ofPred_eq, Bool.false_eq_true, false_iff, not_not]
  exact ⟨And.right, fun h ↦ ⟨Or.inl h, h⟩⟩

omit [Fintype α] in
/-- The alternatives to `true` in minimum threshold are the models with all means above `γ`. -/
lemma mem_alt_minThresholdTask_true_iff :
    θ' ∈ (minThresholdTask ν mean γ).alt true ↔ ∀ a, γ < mean θ' a := by
  simp only [IdentTask.mem_alt_iff, M_minThresholdTask, correct_minThresholdTask,
    Set.mem_ofPred_eq, true_iff]
  exact ⟨fun ⟨h, h'⟩ ↦ h.resolve_left h', fun h ↦
    ⟨Or.inr h, fun ⟨a, ha⟩ ↦ (h a).not_gt ha⟩⟩

end MeanFunctional

variable (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)]

/-- **The cost of the alternatives to `false` in minimum threshold** [DK19, Lemma 37;
KKG18, Lemma 1]. Under the assumptions of `altCost_thresholdingTask_restrict` on the arm laws, if
all the means of `μ` are at least `γ`, then on the vectors of means of the families, for every
nonnegative allocation `w`, `D(μ, w, ¬false) = min_a w a d_a(μ a, γ)`: this infimum is
approached by moving a single arm below `γ`, ever closer to `γ`. -/
theorem altCost_minThresholdTask_restrict_false (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, γ ≤ μ a) (hw : 0 ≤ w) :
    ((minThresholdTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).altCost
        μ w false =
      ⨅ a, ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) γ) := by
  classical
  refine le_antisymm (le_iInf fun a ↦ ?_) ?_
  · -- Upper bound: move the mean of `a` below `γ`, close to `γ`.
    refine IdentTask.altCost_le_ofReal_mul_of_eventually (l := 𝓝[<] γ) (by simp)
      (fun c ↦ isDivergenceOn_expFamilyDiv (hT c)) hν hw hμ a (hγ a) nhdsWithin_le_nhds ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (expFamilyMeans_mem_nhds (hT a) (hγ a))] with x (hx : x < γ) hxm
    rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_minThresholdTask_false_iff]
    exact ⟨⟨a, by simpa using hx⟩,
      (Function.forall_update_iff μ fun c y ↦ y ∈ (ρ c).expFamilyMeans (T c)).2
        ⟨hxm, fun c _ ↦ hμ c⟩⟩
  · -- Lower bound: some arm `a` of an alternative has mean below `γ`.
    rw [IdentTask.altCost_def]
    refine le_iInf₂ fun μ' hμ' ↦ ?_
    rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_minThresholdTask_false_iff, id_eq] at hμ'
    obtain ⟨⟨a, ha⟩, hμ'⟩ := hμ'
    exact (iInf_le _ a).trans (IdentTask.ofReal_mul_le_cost (by simp) hν hw hμ' a
      (isDivergenceOn_expFamilyDiv (hT a)) (hμ a) (hγ a)
      (Set.mem_uIcc.2 (Or.inr ⟨ha.le, hμγ a⟩)))

/-- **The game value of the answer `false` in minimum threshold** [DK19, Lemma 37;
KKG18, Lemma 1]. Under the assumptions of `altCost_minThresholdTask_restrict_false`, if all the
means of `μ` are above `γ`, then `D(μ, ¬false) = (∑ a, d_a(μ a, γ)⁻¹)⁻¹`. -/
theorem answerValue_minThresholdTask_restrict_false
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, γ < μ a) :
    ((minThresholdTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).answerValue
        μ false =
      ENNReal.ofReal (∑ a, ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹)⁻¹ :=
  IdentTask.answerValue_eq_of_altCost_eq_iInf _
    (fun a ↦ expFamilyDiv_pos (hμ a) (hγ a) (hμγ a).ne')
    fun _ hw ↦ altCost_minThresholdTask_restrict_false ν hT hγ hμ hν (fun a ↦ (hμγ a).le)
      (mem_simplex_iff.1 hw).1

/-- **The optimal allocation of the answer `false` in minimum threshold** [DK19, Lemma 37;
KKG18, Lemma 1]. Under the assumptions of `altCost_minThresholdTask_restrict_false`, the only
optimal allocation of `false` is proportional to `d_a(μ a, γ)⁻¹`. -/
theorem optAlloc_minThresholdTask_restrict_false [Nonempty α] (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, γ < μ a) :
    ((minThresholdTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).optAlloc
        μ false =
      {fun a ↦ ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹ /
        ∑ b, ((ρ b).expFamilyDiv (T b) (μ b) γ)⁻¹} :=
  IdentTask.optAlloc_eq_of_altCost_eq_iInf _
    (fun a ↦ expFamilyDiv_pos (hμ a) (hγ a) (hμγ a).ne')
    fun _ hw ↦ altCost_minThresholdTask_restrict_false ν hT hγ hμ hν (fun a ↦ (hμγ a).le)
      (mem_simplex_iff.1 hw).1

/-- **The characteristic time of minimum threshold when all the means are above the threshold**
[DK19, Lemma 37; KKG18, Lemma 1]. Under the assumptions of
`altCost_minThresholdTask_restrict_false`, `T*(μ) = ∑ a, d_a(μ a, γ)⁻¹`. -/
theorem charTime_minThresholdTask_restrict_false [Nonempty α] (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, γ < μ a) :
    ((minThresholdTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).charTime μ =
      ENNReal.ofReal (∑ a, ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹) := by
  classical
  have hc (a : α) : 0 < (ρ a).expFamilyDiv (T a) (μ a) γ :=
    expFamilyDiv_pos (hμ a) (hγ a) (hμγ a).ne'
  have hpos := sum_inv_pos hc
  have h_corr : ((minThresholdTask ν id γ).restrict
      {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).correct μ = {false} := by
    rw [IdentTask.correct_restrict, correct_minThresholdTask_eq_singleton, id_eq,
      decide_eq_false (not_exists.2 fun a ha ↦ lt_asymm ha (hμγ a))]
  rw [IdentTask.charTime_eq_inv_answerValue _ h_corr,
    answerValue_minThresholdTask_restrict_false ν hT hγ hμ hν hμγ, ENNReal.ofReal_inv_of_pos hpos,
    inv_inv]

/-- **The cost of the alternatives to `true` in minimum threshold** [DK19, Lemma 38;
KKG18, Lemma 1]. Under the assumptions of `altCost_thresholdingTask_restrict` on the arm laws, on
the vectors of means of the families, for every nonnegative allocation `w`,
`D(μ, w, ¬true) = ∑ a, w a d_a(μ a, max (μ a) γ)`: the alternatives have all their means above `γ`,
and the cost is the infimum over the alternatives that raise every mean at most `γ` to a level
`x > γ`, as `x` decreases to `γ`. -/
theorem altCost_minThresholdTask_restrict_true (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hw : 0 ≤ w) :
    ((minThresholdTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).altCost
        μ w true =
      ∑ a, ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) (max (μ a) γ)) := by
  have hmax (c : α) {x : ℝ} (hx : x ∈ (ρ c).expFamilyMeans (T c)) :
      max (μ c) x ∈ (ρ c).expFamilyMeans (T c) := by
    rcases max_choice (μ c) x with h | h <;> rw [h]
    exacts [hμ c, hx]
  have hνt : ((minThresholdTask ν id γ).restrict
      {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).ν = ν := by
    simp
  refine le_antisymm ?_ ?_
  · -- Upper bound: raise every mean below `x > γ` to `x`, and let `x` decrease to `γ`.
    refine IdentTask.altCost_le_sum_ofReal_mul_of_eventually hνt
      (fun c ↦ isDivergenceOn_expFamilyDiv (hT c)) hν hw hμ
      (μx := fun x c ↦ max (μ c) x) (l := 𝓝[>] γ) nhdsWithin_le_nhds
      (fun _ ↦ (continuous_const.max continuous_id).continuousAt) (fun c ↦ hmax c (hγ c)) ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : γ < x) hS
    rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_minThresholdTask_true_iff]
    exact ⟨fun c ↦ hx.trans_le (le_max_right _ _), hS⟩
  · -- Lower bound: an alternative has all its means above `γ`.
    rw [IdentTask.altCost_def]
    refine le_iInf₂ fun μ' hμ' ↦ ?_
    rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_minThresholdTask_true_iff, id_eq] at hμ'
    obtain ⟨hgt, hμ'⟩ := hμ'
    have hge (c : α) : γ ≤ μ' c := (hgt c).le
    rw [IdentTask.cost_eq_sum_ofReal_mul hνt hν hw hμ']
    refine Finset.sum_le_sum fun c _ ↦ ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (expFamilyDiv_le_expFamilyDiv_of_mem_uIcc (hT c) (hmax c (hγ c)) (hμ' c) ?_) (hw c))
    rcases le_total (μ c) γ with h | h
    · rw [max_eq_right h]
      exact Set.mem_uIcc.2 (Or.inl ⟨h, hge c⟩)
    · rw [max_eq_left h]
      exact Set.left_mem_uIcc

/-- **The game value of the answer `true` in minimum threshold** [DK19, Lemma 38;
KKG18, Lemma 1]. Under the assumptions of `altCost_minThresholdTask_restrict_true`,
`D(μ, ¬true) = max_a d_a(μ a, max (μ a) γ)`. -/
theorem answerValue_minThresholdTask_restrict_true (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c))) :
    ((minThresholdTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).answerValue
        μ true =
      ⨆ a, ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (max (μ a) γ)) := by
  have hmax (a : α) : max (μ a) γ ∈ (ρ a).expFamilyMeans (T a) := by
    rcases max_choice (μ a) γ with h | h <;> rw [h]
    exacts [hμ a, hγ a]
  rw [IdentTask.answerValue_def, ← iSup_simplex_ofReal_dotProduct]
  refine iSup_congr fun w ↦ iSup_congr fun hw ↦ ?_
  rw [altCost_minThresholdTask_restrict_true ν hT hγ hμ hν (mem_simplex_iff.1 hw).1, dotProduct,
    ENNReal.ofReal_sum_of_nonneg fun a _ ↦
      mul_nonneg ((mem_simplex_iff.1 hw).1 a) (expFamilyDiv_nonneg (hμ a) (hmax a))]

/-- **The characteristic time of minimum threshold when some mean is below the threshold**
[DK19, Lemma 38; KKG18, Lemma 1]. Under the assumptions of
`altCost_minThresholdTask_restrict_true`, if some mean of `μ` is below `γ`, then
`T*(μ) = (max_a d_a(μ a, max (μ a) γ))⁻¹`. -/
theorem charTime_minThresholdTask_restrict_true (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (h : ∃ a, μ a < γ) :
    ((minThresholdTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).charTime μ =
      (⨆ a, ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (max (μ a) γ)))⁻¹ := by
  classical
  have h_corr : ((minThresholdTask ν id γ).restrict
      {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).correct μ = {true} := by
    rw [IdentTask.correct_restrict, correct_minThresholdTask_eq_singleton, id_eq, decide_eq_true h]
  rw [IdentTask.charTime_eq_inv_answerValue _ h_corr,
    answerValue_minThresholdTask_restrict_true ν hT hγ hμ hν]

/-! #### Gaussian arms -/

variable [MeasurableSingletonClass α] {σ2 : ℝ≥0}

/-- **The characteristic time of Gaussian minimum threshold when all the means are above the
threshold** [DK19, Lemma 37]. For Gaussian arms with a common variance `σ2 ≠ 0` and a vector of
means `μ` with all its means above `γ`, `T*(μ) = ∑ a, 2 σ2 / (μ a - γ)²`. -/
theorem charTime_minThresholdTask_gaussianBandit_false [Nonempty α] (hσ2 : σ2 ≠ 0)
    (hμγ : ∀ a, γ < μ a) :
    (minThresholdTask (Bandits.gaussianBandit · σ2) id γ).charTime μ =
      ENNReal.ofReal (∑ a, 2 * σ2 / (μ a - γ) ^ 2) := by
  rw [← (minThresholdTask (Bandits.gaussianBandit · σ2) id γ).restrict_univ,
    ← setOf_forall_mem_expFamilyMeans_gaussianReal 0 hσ2,
    charTime_minThresholdTask_restrict_false (ρ := fun _ ↦ gaussianReal 0 σ2) (T := fun _ ↦ id) _
      (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
      (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (fun μ' _ ↦ Bandits.klDiv_gaussianBandit_eq_ofReal_expFamilyDiv hσ2 μ μ')
      hμγ]
  simp only [expFamilyDiv_gaussianReal 0 hσ2, inv_div]

/-- **The characteristic time of Gaussian minimum threshold when some mean is below the
threshold** [DK19, Lemma 38]. For Gaussian arms with a common variance `σ2 ≠ 0` and a vector of
means `μ` whose smallest mean `μ a₀` is below `γ`, `T*(μ) = 2 σ2 / (μ a₀ - γ)²`. -/
theorem charTime_minThresholdTask_gaussianBandit_true (hσ2 : σ2 ≠ 0) {a₀ : α}
    (ha₀ : ∀ a, μ a₀ ≤ μ a) (hγ : μ a₀ < γ) :
    (minThresholdTask (Bandits.gaussianBandit · σ2) id γ).charTime μ =
      ENNReal.ofReal (2 * σ2 / (μ a₀ - γ) ^ 2) := by
  have hσ2' : 0 < (σ2 : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hσ2)
  rw [← (minThresholdTask (Bandits.gaussianBandit · σ2) id γ).restrict_univ,
    ← setOf_forall_mem_expFamilyMeans_gaussianReal 0 hσ2,
    charTime_minThresholdTask_restrict_true (ρ := fun _ ↦ gaussianReal 0 σ2) (T := fun _ ↦ id) _
      (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
      (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (fun μ' _ ↦ Bandits.klDiv_gaussianBandit_eq_ofReal_expFamilyDiv hσ2 μ μ')
      ⟨a₀, hγ⟩]
  simp only [expFamilyDiv_gaussianReal 0 hσ2]
  -- The largest divergence to the alternatives is that of the arm with the smallest mean.
  have h_sup : ⨆ a, ENNReal.ofReal ((μ a - max (μ a) γ) ^ 2 / (2 * σ2)) =
      ENNReal.ofReal ((μ a₀ - γ) ^ 2 / (2 * σ2)) := by
    refine le_antisymm (iSup_le fun a ↦ ENNReal.ofReal_le_ofReal ?_)
      (le_iSup_of_le a₀ (by rw [max_eq_right hγ.le]))
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rcases le_total (μ a) γ with h | h
    · rw [max_eq_right h]
      nlinarith [ha₀ a]
    · rw [max_eq_left h, sub_self]
      simpa using sq_nonneg (μ a₀ - γ)
  have hpos : 0 < (μ a₀ - γ) ^ 2 / (2 * σ2) := by
    have : 0 < (μ a₀ - γ) ^ 2 := by nlinarith [mul_pos (sub_pos.2 hγ) (sub_pos.2 hγ)]
    positivity
  rw [h_sup, ← ENNReal.ofReal_inv_of_pos hpos, inv_div]

end MinThreshold

end LMLExplore.Identification
