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
and the characteristic time have closed forms. Let the arm `a` have a real divergence `d_a` on an
open set `S_a` of means (`IsDivergenceOn`), in the sense that `KL(ν_a(μ), ν_a(λ)) = d_a(μ a, λ a)`
for the vectors of means `λ` in `S`, so that the transportation cost from `μ` to such a `λ` is
`cost_μ(w, λ) = ∑ a, w a d_a(μ a, λ a)`, and let `γ` be in every `S_a`. The arms of per-arm
exponential families, with the divergences `d_a(μ, μ')` of the families in the mean
parametrization on their sets of means, are an instance (`isDivergenceOn_expFamilyDiv`).

* *Thresholding* (`thresholdingTask ν id γ`): the alternatives to the set `S*` of the arms of `μ`
  with mean above `γ` are the vectors in which some arm `a` crossed `γ`. The infimum of their costs
  is approached by moving a single arm to the other side of `γ`, ever closer to `γ`, so that
  `D(μ, w, ¬S*) = min_a w a d_a(μ a, γ)`. The allocation maximizing it is proportional to
  `d_a(μ a, γ)⁻¹`, and `T*(μ) = ∑ a, d_a(μ a, γ)⁻¹`. For Gaussian arms with known variances
  `v a`, `T*(μ) = ∑ a, 2 v a / (μ a - γ)²`.
* *Minimum threshold* (`minThresholdTask ν id γ`): if all the means are above `γ` (answer `false`),
  the alternatives are the vectors with some mean below `γ`, and the game is that of thresholding:
  `D(μ, w, ¬false) = min_a w a d_a(μ a, γ)` and `T*(μ) = ∑ a, d_a(μ a, γ)⁻¹`
  [DK19, Lemma 37; KKG18, Lemma 1]. If some mean is below `γ` (answer `true`), the alternatives
  are the vectors with all means above `γ`: every arm with mean at most `γ` has to be moved above
  `γ`, and the infimum of the costs is reached in the limit where these arms are moved to `γ`:
  `D(μ, w, ¬true) = ∑ a, w a d_a(μ a, max (μ a) γ)`, whose supremum over the simplex is
  `D(μ, ¬true) = max_a d_a(μ a, max (μ a) γ)`, and `T*(μ) = (max_a d_a(μ a, max (μ a) γ))⁻¹`. For
  Gaussian arms with known variances `v a`, this is `2 v a₀ / (μ a₀ - γ)²` for an arm `a₀` below
  `γ` maximizing `(μ a - γ)² / v a` among the arms below `γ`; with a common variance, `a₀` is an
  arm of smallest mean [DK19, Lemma 38; KKG18, Lemma 1].

The Gaussian arms with known variances `v a ≠ 0` are the arm laws `ν μ a = 𝒩(μ a, v a)`, for
instance the bandits `Bandits.gaussianMeanVarBandit fun a ↦ (μ a, v a)`; the Gaussian bandits
`Bandits.gaussianBandit μ σ2` with a common variance are the case of a constant `v`.

The admissible models are the vectors of means in `S`, `task.restrict {λ | ∀ c, λ c ∈ S c}`. Each
arm has its own divergence: the arms do not interact in these tasks. The transportation costs
between such vectors of means are computed in `LMLExplore/Identification/Task/ExpFamily.lean`,
which also uses only the hypotheses `IsDivergenceOn`, and the game of a weighted minimum
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
* `LMLExplore.Identification.altCost_thresholdingTask_gaussianReal`,
  `LMLExplore.Identification.charTime_thresholdingTask_gaussianReal`: for Gaussian arms with
  variances `v a`, `D(μ, w, ¬S*) = min_a w a (μ a - γ)² / (2 v a)` and
  `T*(μ) = ∑ a, 2 v a / (μ a - γ)²`.
* `LMLExplore.Identification.altCost_thresholdingTask_gaussianBandit`,
  `LMLExplore.Identification.charTime_thresholdingTask_gaussianBandit`: their cases of a common
  variance `σ2`.
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
* `LMLExplore.Identification.charTime_minThresholdTask_gaussianReal_false`,
  `LMLExplore.Identification.charTime_minThresholdTask_gaussianReal_true`: for Gaussian arms with
  variances `v a`, `T*(μ) = ∑ a, 2 v a / (μ a - γ)²` if all the means are above `γ`, and
  `T*(μ) = 2 v a₀ / (μ a₀ - γ)²` if the arm `a₀` below `γ` maximizes `(μ a - γ)² / v a` among the
  arms below `γ`.
* `LMLExplore.Identification.charTime_minThresholdTask_gaussianBandit_false`,
  `LMLExplore.Identification.charTime_minThresholdTask_gaussianBandit_true`: their cases of a
  common variance `σ2`, where `a₀` is an arm of smallest mean.

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
  {S : α → Set ℝ} {d : α → ℝ → ℝ → ℝ} {γ : ℝ} {μ w : α → ℝ}

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

/-- **The cost of the alternatives in thresholding.** Let each arm `c` have a divergence `d_c` on
an open set `S_c` of means, in the sense that `KL(ν_c(μ), ν_c(μ')) = d_c(μ c, μ' c)` for all
vectors of means `μ'` in `S`, let `γ` be in every `S_c` and let `μ` be a vector of means in `S` with
no mean equal to `γ`, whose correct answer is the set `s` of the arms with mean above `γ`. Then on
the vectors of means in `S`, for every nonnegative allocation `w`,
`D(μ, w, ¬s) = min_a w a d_a(μ a, γ)`: this infimum is approached by moving a single arm across
`γ`, ever closer to `γ`. -/
theorem altCost_thresholdingTask_restrict (hd : ∀ a, IsDivergenceOn (d a) (S a))
    (hγ : ∀ a, γ ∈ S a) (hμ : ∀ a, μ a ∈ S a)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hμγ : ∀ a, μ a ≠ γ) {s : Finset α} (hs : ∀ a, a ∈ s ↔ γ < μ a) (hw : 0 ≤ w) :
    ((thresholdingTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ S c}).altCost μ w s =
      ⨅ a, ENNReal.ofReal (w a * d a (μ a) γ) := by
  classical
  refine le_antisymm (le_iInf fun a ↦ ?_) ?_
  · -- Upper bound: move the mean of `a` across `γ`, close to `γ`.
    have h_alt {x : ℝ} (hxγ : (γ < x ↔ ¬ γ < μ a)) (hx : x ≠ γ)
        (hxm : x ∈ S a) :
        Function.update μ a x ∈ ((thresholdingTask ν id γ).restrict
          {μ' | ∀ c, μ' c ∈ S c}).alt s := by
      rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_thresholdingTask_iff, id_eq]
      refine ⟨⟨(Function.forall_update_iff μ fun _ y ↦ y ≠ γ).2 ⟨hx, fun c _ ↦ hμγ c⟩,
        a, ?_⟩, (Function.forall_update_iff μ fun c y ↦ y ∈ S c).2
          ⟨hxm, fun c _ ↦ hμ c⟩⟩
      rw [hs a, Function.update_self]
      tauto
    have hm := (hd a).isOpen.mem_nhds (hγ a)
    rcases (hμγ a).lt_or_gt with ha | ha
    · refine IdentTask.altCost_le_ofReal_mul_of_eventually (l := 𝓝[>] γ) (by simp)
        hd hν hw hμ a (hγ a) nhdsWithin_le_nhds ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hm] with x (hx : γ < x) hxm
      exact h_alt (iff_of_true hx ha.not_gt) hx.ne' hxm
    · refine IdentTask.altCost_le_ofReal_mul_of_eventually (l := 𝓝[<] γ) (by simp)
        hd hν hw hμ a (hγ a) nhdsWithin_le_nhds ?_
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
      (IdentTask.ofReal_mul_le_cost (by simp) hν hw hμ' a (hd a)
        (hμ a) (hγ a) h_mem)

/-- **The game value of thresholding.** Under the assumptions of
`altCost_thresholdingTask_restrict`, the value of the correct answer `s` is
`D(μ, ¬s) = (∑ a, d_a(μ a, γ)⁻¹)⁻¹`. -/
theorem answerValue_thresholdingTask_restrict
    (hd : ∀ a, IsDivergenceOn (d a) (S a))
    (hγ : ∀ a, γ ∈ S a) (hμ : ∀ a, μ a ∈ S a)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hμγ : ∀ a, μ a ≠ γ) {s : Finset α} (hs : ∀ a, a ∈ s ↔ γ < μ a) :
    ((thresholdingTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ S c}).answerValue μ s =
      ENNReal.ofReal (∑ a, (d a (μ a) γ)⁻¹)⁻¹ :=
  IdentTask.answerValue_eq_of_altCost_eq_iInf _ (fun a ↦ (hd a).pos (hμ a) (hγ a) (hμγ a))
    fun _ hw ↦ altCost_thresholdingTask_restrict ν hd hγ hμ hν hμγ hs (mem_simplex_iff.1 hw).1

/-- **The optimal allocation of thresholding.** Under the assumptions of
`altCost_thresholdingTask_restrict`, the only optimal allocation of the correct answer `s` is
proportional to `d_a(μ a, γ)⁻¹`. -/
theorem optAlloc_thresholdingTask_restrict [Nonempty α]
    (hd : ∀ a, IsDivergenceOn (d a) (S a))
    (hγ : ∀ a, γ ∈ S a) (hμ : ∀ a, μ a ∈ S a)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hμγ : ∀ a, μ a ≠ γ) {s : Finset α} (hs : ∀ a, a ∈ s ↔ γ < μ a) :
    ((thresholdingTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ S c}).optAlloc μ s =
      {fun a ↦ (d a (μ a) γ)⁻¹ /
        ∑ b, (d b (μ b) γ)⁻¹} :=
  IdentTask.optAlloc_eq_of_altCost_eq_iInf _ (fun a ↦ (hd a).pos (hμ a) (hγ a) (hμγ a))
    fun _ hw ↦ altCost_thresholdingTask_restrict ν hd hγ hμ hν hμγ hs (mem_simplex_iff.1 hw).1

/-- **The characteristic time of thresholding.** Under the assumptions of
`altCost_thresholdingTask_restrict`, `T*(μ) = ∑ a, d_a(μ a, γ)⁻¹`. -/
theorem charTime_thresholdingTask_restrict [Nonempty α]
    (hd : ∀ a, IsDivergenceOn (d a) (S a))
    (hγ : ∀ a, γ ∈ S a) (hμ : ∀ a, μ a ∈ S a)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hμγ : ∀ a, μ a ≠ γ) :
    ((thresholdingTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ S c}).charTime μ =
      ENNReal.ofReal (∑ a, (d a (μ a) γ)⁻¹) := by
  classical
  have hs (a : α) : a ∈ Finset.univ.filter (γ < μ ·) ↔ γ < μ a := by simp
  have hpos := sum_inv_pos fun a ↦ (hd a).pos (hμ a) (hγ a) (hμγ a)
  rw [IdentTask.charTime_eq_inv_answerValue _
      (by rw [IdentTask.correct_restrict, correct_thresholdingTask_eq_singleton ν id, id_eq]),
    answerValue_thresholdingTask_restrict ν hd hγ hμ hν hμγ hs, ENNReal.ofReal_inv_of_pos hpos,
    inv_inv]

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
all the means of `μ` are at least `γ`, then on the vectors of means in `S`, for every
nonnegative allocation `w`, `D(μ, w, ¬false) = min_a w a d_a(μ a, γ)`: this infimum is
approached by moving a single arm below `γ`, ever closer to `γ`. -/
theorem altCost_minThresholdTask_restrict_false (hd : ∀ a, IsDivergenceOn (d a) (S a))
    (hγ : ∀ a, γ ∈ S a) (hμ : ∀ a, μ a ∈ S a)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hμγ : ∀ a, γ ≤ μ a) (hw : 0 ≤ w) :
    ((minThresholdTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ S c}).altCost μ w false =
      ⨅ a, ENNReal.ofReal (w a * d a (μ a) γ) := by
  classical
  refine le_antisymm (le_iInf fun a ↦ ?_) ?_
  · -- Upper bound: move the mean of `a` below `γ`, close to `γ`.
    refine IdentTask.altCost_le_ofReal_mul_of_eventually (l := 𝓝[<] γ) (by simp)
      hd hν hw hμ a (hγ a) nhdsWithin_le_nhds ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds ((hd a).isOpen.mem_nhds (hγ a))] with x (hx : x < γ) hxm
    rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_minThresholdTask_false_iff]
    exact ⟨⟨a, by simpa using hx⟩,
      (Function.forall_update_iff μ fun c y ↦ y ∈ S c).2
        ⟨hxm, fun c _ ↦ hμ c⟩⟩
  · -- Lower bound: some arm `a` of an alternative has mean below `γ`.
    rw [IdentTask.altCost_def]
    refine le_iInf₂ fun μ' hμ' ↦ ?_
    rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_minThresholdTask_false_iff, id_eq] at hμ'
    obtain ⟨⟨a, ha⟩, hμ'⟩ := hμ'
    exact (iInf_le _ a).trans (IdentTask.ofReal_mul_le_cost (by simp) hν hw hμ' a
      (hd a) (hμ a) (hγ a)
      (Set.mem_uIcc.2 (Or.inr ⟨ha.le, hμγ a⟩)))

/-- **The game value of the answer `false` in minimum threshold** [DK19, Lemma 37;
KKG18, Lemma 1]. Under the assumptions of `altCost_minThresholdTask_restrict_false`, if all the
means of `μ` are above `γ`, then `D(μ, ¬false) = (∑ a, d_a(μ a, γ)⁻¹)⁻¹`. -/
theorem answerValue_minThresholdTask_restrict_false
    (hd : ∀ a, IsDivergenceOn (d a) (S a))
    (hγ : ∀ a, γ ∈ S a) (hμ : ∀ a, μ a ∈ S a)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hμγ : ∀ a, γ < μ a) :
    ((minThresholdTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ S c}).answerValue μ false =
      ENNReal.ofReal (∑ a, (d a (μ a) γ)⁻¹)⁻¹ :=
  IdentTask.answerValue_eq_of_altCost_eq_iInf _
    (fun a ↦ (hd a).pos (hμ a) (hγ a) (hμγ a).ne')
    fun _ hw ↦ altCost_minThresholdTask_restrict_false ν hd hγ hμ hν (fun a ↦ (hμγ a).le)
      (mem_simplex_iff.1 hw).1

/-- **The optimal allocation of the answer `false` in minimum threshold** [DK19, Lemma 37;
KKG18, Lemma 1]. Under the assumptions of `altCost_minThresholdTask_restrict_false`, the only
optimal allocation of `false` is proportional to `d_a(μ a, γ)⁻¹`. -/
theorem optAlloc_minThresholdTask_restrict_false [Nonempty α] (hd : ∀ a, IsDivergenceOn (d a) (S a))
    (hγ : ∀ a, γ ∈ S a) (hμ : ∀ a, μ a ∈ S a)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hμγ : ∀ a, γ < μ a) :
    ((minThresholdTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ S c}).optAlloc μ false =
      {fun a ↦ (d a (μ a) γ)⁻¹ /
        ∑ b, (d b (μ b) γ)⁻¹} :=
  IdentTask.optAlloc_eq_of_altCost_eq_iInf _
    (fun a ↦ (hd a).pos (hμ a) (hγ a) (hμγ a).ne')
    fun _ hw ↦ altCost_minThresholdTask_restrict_false ν hd hγ hμ hν (fun a ↦ (hμγ a).le)
      (mem_simplex_iff.1 hw).1

/-- **The characteristic time of minimum threshold when all the means are above the threshold**
[DK19, Lemma 37; KKG18, Lemma 1]. Under the assumptions of
`altCost_minThresholdTask_restrict_false`, `T*(μ) = ∑ a, d_a(μ a, γ)⁻¹`. -/
theorem charTime_minThresholdTask_restrict_false [Nonempty α] (hd : ∀ a, IsDivergenceOn (d a) (S a))
    (hγ : ∀ a, γ ∈ S a) (hμ : ∀ a, μ a ∈ S a)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hμγ : ∀ a, γ < μ a) :
    ((minThresholdTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ S c}).charTime μ =
      ENNReal.ofReal (∑ a, (d a (μ a) γ)⁻¹) := by
  classical
  have hc (a : α) : 0 < d a (μ a) γ :=
    (hd a).pos (hμ a) (hγ a) (hμγ a).ne'
  have hpos := sum_inv_pos hc
  have h_corr : ((minThresholdTask ν id γ).restrict
      {μ' | ∀ c, μ' c ∈ S c}).correct μ = {false} := by
    rw [IdentTask.correct_restrict, correct_minThresholdTask_eq_singleton, id_eq,
      decide_eq_false (not_exists.2 fun a ha ↦ lt_asymm ha (hμγ a))]
  rw [IdentTask.charTime_eq_inv_answerValue _ h_corr,
    answerValue_minThresholdTask_restrict_false ν hd hγ hμ hν hμγ, ENNReal.ofReal_inv_of_pos hpos,
    inv_inv]

/-- **The cost of the alternatives to `true` in minimum threshold** [DK19, Lemma 38;
KKG18, Lemma 1]. Under the assumptions of `altCost_thresholdingTask_restrict` on the arm laws, on
the vectors of means in `S`, for every nonnegative allocation `w`,
`D(μ, w, ¬true) = ∑ a, w a d_a(μ a, max (μ a) γ)`: the alternatives have all their means above `γ`,
and the cost is the infimum over the alternatives that raise every mean at most `γ` to a level
`x > γ`, as `x` decreases to `γ`. -/
theorem altCost_minThresholdTask_restrict_true (hd : ∀ a, IsDivergenceOn (d a) (S a))
    (hγ : ∀ a, γ ∈ S a) (hμ : ∀ a, μ a ∈ S a)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hw : 0 ≤ w) :
    ((minThresholdTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ S c}).altCost μ w true =
      ∑ a, ENNReal.ofReal (w a * d a (μ a) (max (μ a) γ)) := by
  have hmax (c : α) {x : ℝ} (hx : x ∈ S c) :
      max (μ c) x ∈ S c := by
    rcases max_choice (μ c) x with h | h <;> rw [h]
    exacts [hμ c, hx]
  have hνt : ((minThresholdTask ν id γ).restrict
      {μ' | ∀ c, μ' c ∈ S c}).ν = ν := by
    simp
  refine le_antisymm ?_ ?_
  · -- Upper bound: raise every mean below `x > γ` to `x`, and let `x` decrease to `γ`.
    refine IdentTask.altCost_le_sum_ofReal_mul_of_eventually hνt
      hd hν hw hμ
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
      ((hd c).le_of_mem_uIcc (hμ c) (hmax c (hγ c)) (hμ' c) ?_) (hw c))
    rcases le_total (μ c) γ with h | h
    · rw [max_eq_right h]
      exact Set.mem_uIcc.2 (Or.inl ⟨h, hge c⟩)
    · rw [max_eq_left h]
      exact Set.left_mem_uIcc

/-- **The game value of the answer `true` in minimum threshold** [DK19, Lemma 38;
KKG18, Lemma 1]. Under the assumptions of `altCost_minThresholdTask_restrict_true`,
`D(μ, ¬true) = max_a d_a(μ a, max (μ a) γ)`. -/
theorem answerValue_minThresholdTask_restrict_true (hd : ∀ a, IsDivergenceOn (d a) (S a))
    (hγ : ∀ a, γ ∈ S a) (hμ : ∀ a, μ a ∈ S a)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c))) :
    ((minThresholdTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ S c}).answerValue μ true =
      ⨆ a, ENNReal.ofReal (d a (μ a) (max (μ a) γ)) := by
  have hmax (a : α) : max (μ a) γ ∈ S a := by
    rcases max_choice (μ a) γ with h | h <;> rw [h]
    exacts [hμ a, hγ a]
  rw [IdentTask.answerValue_def, ← iSup_simplex_ofReal_dotProduct]
  refine iSup_congr fun w ↦ iSup_congr fun hw ↦ ?_
  rw [altCost_minThresholdTask_restrict_true ν hd hγ hμ hν (mem_simplex_iff.1 hw).1, dotProduct,
    ENNReal.ofReal_sum_of_nonneg fun a _ ↦
      mul_nonneg ((mem_simplex_iff.1 hw).1 a) ((hd a).nonneg (hμ a) (hmax a))]

/-- **The characteristic time of minimum threshold when some mean is below the threshold**
[DK19, Lemma 38; KKG18, Lemma 1]. Under the assumptions of
`altCost_minThresholdTask_restrict_true`, if some mean of `μ` is below `γ`, then
`T*(μ) = (max_a d_a(μ a, max (μ a) γ))⁻¹`. -/
theorem charTime_minThresholdTask_restrict_true (hd : ∀ a, IsDivergenceOn (d a) (S a))
    (hγ : ∀ a, γ ∈ S a) (hμ : ∀ a, μ a ∈ S a)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (h : ∃ a, μ a < γ) :
    ((minThresholdTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ S c}).charTime μ =
      (⨆ a, ENNReal.ofReal (d a (μ a) (max (μ a) γ)))⁻¹ := by
  classical
  have h_corr : ((minThresholdTask ν id γ).restrict
      {μ' | ∀ c, μ' c ∈ S c}).correct μ = {true} := by
    rw [IdentTask.correct_restrict, correct_minThresholdTask_eq_singleton, id_eq, decide_eq_true h]
  rw [IdentTask.charTime_eq_inv_answerValue _ h_corr,
    answerValue_minThresholdTask_restrict_true ν hd hγ hμ hν]

end MinThreshold

/-! ### Gaussian arms -/

section Gaussian

variable {ν : (α → ℝ) → Kernel α ℝ} [∀ μ, IsMarkovKernel (ν μ)] {v : α → ℝ≥0}

/-- **The cost of the alternatives in Gaussian thresholding.** For Gaussian arms with variances
`v a ≠ 0`, a vector of means `μ` with no mean equal to `γ`, whose correct answer is the set `s` of
the arms with mean above `γ`, and a nonnegative allocation `w`,
`D(μ, w, ¬s) = min_a w a (μ a - γ)² / (2 v a)`. -/
theorem altCost_thresholdingTask_gaussianReal (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hμγ : ∀ a, μ a ≠ γ) {s : Finset α}
    (hs : ∀ a, a ∈ s ↔ γ < μ a) (hw : 0 ≤ w) :
    (thresholdingTask ν id γ).altCost μ w s =
      ⨅ a, ENNReal.ofReal (w a * (μ a - γ) ^ 2 / (2 * v a)) := by
  rw [← (thresholdingTask ν id γ).restrict_univ,
    ← setOf_forall_mem_expFamilyMeans_gaussianReal 0 hv,
    altCost_thresholdingTask_restrict (S := fun a ↦ (gaussianReal 0 (v a)).expFamilyMeans id) _
      (fun a ↦ isDivergenceOn_expFamilyDiv (not_ae_eq_const_gaussianReal 0 (hv a)))
      (fun a ↦ mem_expFamilyMeans_gaussianReal 0 (hv a) _)
      (fun a ↦ mem_expFamilyMeans_gaussianReal 0 (hv a) _)
      (fun μ' _ ↦ klDiv_eq_ofReal_expFamilyDiv_gaussianReal hv hν μ μ') hμγ hs hw]
  exact iInf_congr fun a ↦ by rw [expFamilyDiv_gaussianReal 0 (hv a), mul_div_assoc]

/-- **The characteristic time of Gaussian thresholding.** For Gaussian arms with variances
`v a ≠ 0` and a vector of means `μ` with no mean equal to `γ`, `T*(μ) = ∑ a, 2 v a / (μ a - γ)²`. -/
theorem charTime_thresholdingTask_gaussianReal [Nonempty α] (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hμγ : ∀ a, μ a ≠ γ) :
    (thresholdingTask ν id γ).charTime μ = ENNReal.ofReal (∑ a, 2 * v a / (μ a - γ) ^ 2) := by
  rw [← (thresholdingTask ν id γ).restrict_univ,
    ← setOf_forall_mem_expFamilyMeans_gaussianReal 0 hv,
    charTime_thresholdingTask_restrict (S := fun a ↦ (gaussianReal 0 (v a)).expFamilyMeans id) _
      (fun a ↦ isDivergenceOn_expFamilyDiv (not_ae_eq_const_gaussianReal 0 (hv a)))
      (fun a ↦ mem_expFamilyMeans_gaussianReal 0 (hv a) _)
      (fun a ↦ mem_expFamilyMeans_gaussianReal 0 (hv a) _)
      (fun μ' _ ↦ klDiv_eq_ofReal_expFamilyDiv_gaussianReal hv hν μ μ') hμγ]
  exact congrArg ENNReal.ofReal (Finset.sum_congr rfl fun a _ ↦ by
    rw [expFamilyDiv_gaussianReal 0 (hv a), inv_div])

/-- **The characteristic time of Gaussian minimum threshold when all the means are above the
threshold** [DK19, Lemma 37]. For Gaussian arms with variances `v a ≠ 0` and a vector of means `μ`
with all its means above `γ`, `T*(μ) = ∑ a, 2 v a / (μ a - γ)²`. -/
theorem charTime_minThresholdTask_gaussianReal_false [Nonempty α] (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) (hμγ : ∀ a, γ < μ a) :
    (minThresholdTask ν id γ).charTime μ = ENNReal.ofReal (∑ a, 2 * v a / (μ a - γ) ^ 2) := by
  rw [← (minThresholdTask ν id γ).restrict_univ,
    ← setOf_forall_mem_expFamilyMeans_gaussianReal 0 hv,
    charTime_minThresholdTask_restrict_false
      (S := fun a ↦ (gaussianReal 0 (v a)).expFamilyMeans id) _
      (fun a ↦ isDivergenceOn_expFamilyDiv (not_ae_eq_const_gaussianReal 0 (hv a)))
      (fun a ↦ mem_expFamilyMeans_gaussianReal 0 (hv a) _)
      (fun a ↦ mem_expFamilyMeans_gaussianReal 0 (hv a) _)
      (fun μ' _ ↦ klDiv_eq_ofReal_expFamilyDiv_gaussianReal hv hν μ μ') hμγ]
  exact congrArg ENNReal.ofReal (Finset.sum_congr rfl fun a _ ↦ by
    rw [expFamilyDiv_gaussianReal 0 (hv a), inv_div])

/-- **The characteristic time of Gaussian minimum threshold when some mean is below the
threshold** [DK19, Lemma 38]. For Gaussian arms with variances `v a ≠ 0` and a vector of means `μ`
with an arm `a₀` below `γ` that maximizes `(μ a - γ)² / v a` among the arms below `γ`,
`T*(μ) = 2 v a₀ / (μ a₀ - γ)²`. -/
theorem charTime_minThresholdTask_gaussianReal_true (hv : ∀ a, v a ≠ 0)
    (hν : ∀ μ a, ν μ a = gaussianReal (μ a) (v a)) {a₀ : α} (hγ : μ a₀ < γ)
    (ha₀ : ∀ a, μ a < γ → (μ a - γ) ^ 2 / v a ≤ (μ a₀ - γ) ^ 2 / v a₀) :
    (minThresholdTask ν id γ).charTime μ = ENNReal.ofReal (2 * v a₀ / (μ a₀ - γ) ^ 2) := by
  rw [← (minThresholdTask ν id γ).restrict_univ,
    ← setOf_forall_mem_expFamilyMeans_gaussianReal 0 hv,
    charTime_minThresholdTask_restrict_true
      (S := fun a ↦ (gaussianReal 0 (v a)).expFamilyMeans id) _
      (fun a ↦ isDivergenceOn_expFamilyDiv (not_ae_eq_const_gaussianReal 0 (hv a)))
      (fun a ↦ mem_expFamilyMeans_gaussianReal 0 (hv a) _)
      (fun a ↦ mem_expFamilyMeans_gaussianReal 0 (hv a) _)
      (fun μ' _ ↦ klDiv_eq_ofReal_expFamilyDiv_gaussianReal hv hν μ μ') ⟨a₀, hγ⟩]
  -- The largest divergence to the alternatives is that of the arm `a₀`.
  have h_sup : ⨆ a, ENNReal.ofReal ((gaussianReal 0 (v a)).expFamilyDiv id (μ a)
      (max (μ a) γ)) = ENNReal.ofReal ((μ a₀ - γ) ^ 2 / (2 * v a₀)) := by
    refine le_antisymm (iSup_le fun a ↦ ENNReal.ofReal_le_ofReal ?_)
      (le_iSup_of_le a₀ (by rw [max_eq_right hγ.le, expFamilyDiv_gaussianReal 0 (hv a₀)]))
    rw [expFamilyDiv_gaussianReal 0 (hv a)]
    rcases lt_or_ge (μ a) γ with h | h
    · rw [max_eq_right h.le, div_mul_eq_div_div_swap, div_mul_eq_div_div_swap]
      exact div_le_div_of_nonneg_right (ha₀ a h) zero_le_two
    · rw [max_eq_left h, sub_self, zero_pow two_ne_zero, zero_div]
      positivity
  have hpos : 0 < (μ a₀ - γ) ^ 2 / (2 * v a₀) := by
    have : 0 < (μ a₀ - γ) ^ 2 := by nlinarith [mul_pos (sub_pos.2 hγ) (sub_pos.2 hγ)]
    have : 0 < (v a₀ : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hv a₀))
    positivity
  rw [h_sup, ← ENNReal.ofReal_inv_of_pos hpos, inv_div]

/-- **The cost of the alternatives in Gaussian thresholding with a common variance.** For Gaussian
arms with a common variance `σ2 ≠ 0`, a vector of means `μ` with no mean equal to `γ`, whose
correct answer is the set `s` of the arms with mean above `γ`, and a nonnegative allocation `w`,
`D(μ, w, ¬s) = min_a w a (μ a - γ)² / (2 σ2)`. -/
theorem altCost_thresholdingTask_gaussianBandit [MeasurableSingletonClass α] {σ2 : ℝ≥0}
    (hσ2 : σ2 ≠ 0) (hμγ : ∀ a, μ a ≠ γ) {s : Finset α} (hs : ∀ a, a ∈ s ↔ γ < μ a) (hw : 0 ≤ w) :
    (thresholdingTask (Bandits.gaussianBandit · σ2) id γ).altCost μ w s =
      ⨅ a, ENNReal.ofReal (w a * (μ a - γ) ^ 2 / (2 * σ2)) :=
  altCost_thresholdingTask_gaussianReal (v := fun _ ↦ σ2) (fun _ ↦ hσ2)
    (Bandits.gaussianBandit_apply · σ2) hμγ hs hw

/-- **The characteristic time of Gaussian thresholding with a common variance.** For Gaussian arms
with a common variance `σ2 ≠ 0` and a vector of means `μ` with no mean equal to `γ`,
`T*(μ) = ∑ a, 2 σ2 / (μ a - γ)²`. -/
theorem charTime_thresholdingTask_gaussianBandit [MeasurableSingletonClass α] [Nonempty α]
    {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0) (hμγ : ∀ a, μ a ≠ γ) :
    (thresholdingTask (Bandits.gaussianBandit · σ2) id γ).charTime μ =
      ENNReal.ofReal (∑ a, 2 * σ2 / (μ a - γ) ^ 2) :=
  charTime_thresholdingTask_gaussianReal (v := fun _ ↦ σ2) (fun _ ↦ hσ2)
    (Bandits.gaussianBandit_apply · σ2) hμγ

/-- **The characteristic time of Gaussian minimum threshold with a common variance when all the
means are above the threshold** [DK19, Lemma 37]. For Gaussian arms with a common variance
`σ2 ≠ 0` and a vector of means `μ` with all its means above `γ`, `T*(μ) = ∑ a, 2 σ2 / (μ a - γ)²`.
-/
theorem charTime_minThresholdTask_gaussianBandit_false [MeasurableSingletonClass α] [Nonempty α]
    {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0) (hμγ : ∀ a, γ < μ a) :
    (minThresholdTask (Bandits.gaussianBandit · σ2) id γ).charTime μ =
      ENNReal.ofReal (∑ a, 2 * σ2 / (μ a - γ) ^ 2) :=
  charTime_minThresholdTask_gaussianReal_false (v := fun _ ↦ σ2) (fun _ ↦ hσ2)
    (Bandits.gaussianBandit_apply · σ2) hμγ

/-- **The characteristic time of Gaussian minimum threshold with a common variance when some mean
is below the threshold** [DK19, Lemma 38]. For Gaussian arms with a common variance `σ2 ≠ 0` and a
vector of means `μ` whose smallest mean `μ a₀` is below `γ`, `T*(μ) = 2 σ2 / (μ a₀ - γ)²`. -/
theorem charTime_minThresholdTask_gaussianBandit_true [MeasurableSingletonClass α] {σ2 : ℝ≥0}
    (hσ2 : σ2 ≠ 0) {a₀ : α} (ha₀ : ∀ a, μ a₀ ≤ μ a) (hγ : μ a₀ < γ) :
    (minThresholdTask (Bandits.gaussianBandit · σ2) id γ).charTime μ =
      ENNReal.ofReal (2 * σ2 / (μ a₀ - γ) ^ 2) :=
  charTime_minThresholdTask_gaussianReal_true (v := fun _ ↦ σ2) (fun _ ↦ hσ2)
    (Bandits.gaussianBandit_apply · σ2) hγ fun a ha ↦
      div_le_div_of_nonneg_right (by nlinarith [ha₀ a]) σ2.2

end Gaussian

end LMLExplore.Identification
