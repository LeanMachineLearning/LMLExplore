/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.Oracle
public import LMLExplore.Identification.Task.Threshold.Basic

/-!
# The pure exploration game of Any Low Arm

In *Any Low Arm* (`anyLowArmTask ν id γ`) [DK19, Example 1], the correct answers of a vector of
means `μ` are the arms `a` with mean below a threshold `γ` (answer `some a`), and "none" (answer
`none`) if all the means are above `γ`. It is the running example of a task with multiple correct
answers. Let the arm `a` belong to an exponential family `(ρ a, T a)` with divergence `d_a` in the
mean parametrization, and let `γ` be a mean of every family.

* The alternatives to an arm `a` are the vectors in which the mean of `a` is at least `γ`. If
  `μ a ≤ γ`, the infimum of their costs is approached by moving the mean of `a` above `γ`, ever
  closer to `γ`, so that `D(μ, w, ¬a) = w a d_a(μ a, γ)` and `D(μ, ¬a) = d_a(μ a, γ)`, attained
  only at the vertex `w = Pi.single a 1` when `μ a < γ`: the best way to check that an arm is low
  is to sample only that arm.
* The alternatives to `none` are those of the answer `false` of minimum threshold, the vectors with
  some mean below `γ`, so that the game of `none` is the game of thresholding
  (`LMLExplore/Identification/Task/Threshold/Basic.lean`): if all the means are above `γ`,
  `D(μ, ¬none) = (∑ a, d_a(μ a, γ)⁻¹)⁻¹` and `T*(μ) = ∑ a, d_a(μ a, γ)⁻¹`.
* If some mean is below `γ`, the oracle answers are the arms `a` maximizing
  `d_a(μ a, max (μ a) γ)` and the oracle allocations are the corresponding vertices of the
  simplex, with `T*(μ) = (max_a d_a(μ a, max (μ a) γ))⁻¹`. When two distinct arms attain this
  maximum, the oracle allocations `w*(μ)` form a set of two or more vertices, which is not convex
  [DK19, Proposition 5]: the convexity of each `w*(μ, ¬i)` does not extend to `w*(μ)`. This is why
  the guarantee of Track-and-Stop for tasks with multiple correct answers involves the convex hull
  of `w*(μ)`, and why the sticky variant of Degenne and Koolen commits to one oracle answer. For
  Gaussian arms with a common variance, the oracle allocations are the vertices of the arms of
  smallest mean, and two arms with the same smallest mean below `γ` give this non-convex set.

The costs are computed on the vectors of means of the families,
`S = {λ | ∀ c, λ c ∈ (ρ c).expFamilyMeans (T c)}`, as for thresholding and minimum threshold. The
statements follow those of the formalization of [DK19, Example 1] in the LMLPapers project.

## Main statements

* `LMLExplore.Identification.mem_alt_anyLowArmTask_some_iff`,
  `LMLExplore.Identification.mem_alt_anyLowArmTask_none_iff`: the alternatives of Any Low Arm.
* `LMLExplore.Identification.altCost_anyLowArmTask_restrict_some`,
  `LMLExplore.Identification.answerValue_anyLowArmTask_restrict_some`,
  `LMLExplore.Identification.optAlloc_anyLowArmTask_restrict_some`: for an arm with `μ a ≤ γ`,
  `D(μ, w, ¬a) = w a d_a(μ a, γ)` and `D(μ, ¬a) = d_a(μ a, γ)`, and if `μ a < γ` the only optimal
  allocation is `Pi.single a 1`.
* `LMLExplore.Identification.altCost_anyLowArmTask_restrict_none`,
  `LMLExplore.Identification.answerValue_anyLowArmTask_restrict_none`,
  `LMLExplore.Identification.optAlloc_anyLowArmTask_restrict_none`,
  `LMLExplore.Identification.charTime_anyLowArmTask_restrict_of_forall_lt`: if all the means are
  above `γ`, `D(μ, w, ¬none) = min_a w a d_a(μ a, γ)`, `D(μ, ¬none) = (∑ a, d_a(μ a, γ)⁻¹)⁻¹`, the
  only optimal allocation is proportional to `d_a(μ a, γ)⁻¹`, and `T*(μ) = ∑ a, d_a(μ a, γ)⁻¹`.
* `LMLExplore.Identification.gameValue_anyLowArmTask_restrict_of_exists_lt`,
  `LMLExplore.Identification.charTime_anyLowArmTask_restrict_of_exists_lt`: if some mean is below
  `γ`, `D(μ) = max_a d_a(μ a, max (μ a) γ)` and `T*(μ) = (max_a d_a(μ a, max (μ a) γ))⁻¹`.
* `LMLExplore.Identification.oracleAnswers_anyLowArmTask_restrict_of_exists_lt`,
  `LMLExplore.Identification.oracleAlloc_anyLowArmTask_restrict_of_exists_lt`: if some mean is
  below `γ`, the oracle answers are the arms maximizing `d_a(μ a, max (μ a) γ)`, and the oracle
  allocations are their vertices `Pi.single a 1`.
* `LMLExplore.Identification.not_convex_oracleAlloc_anyLowArmTask_restrict`: if two distinct arms
  maximize `d_a(μ a, max (μ a) γ)`, the oracle allocations are not convex [DK19, Proposition 5].
* `LMLExplore.Identification.oracleAlloc_anyLowArmTask_gaussianBandit`,
  `LMLExplore.Identification.not_convex_oracleAlloc_anyLowArmTask_gaussianBandit`: for Gaussian
  arms with a common variance and a smallest mean below `γ`, the oracle allocations are the vertices
  of the arms of smallest mean, and they are not convex when two distinct arms have the smallest
  mean.

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, Example 1 and Proposition 5.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Measure Set

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α Θ 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} [Fintype α]
  {ρ : α → Measure 𝓨} {T : α → 𝓨 → ℝ} {γ : ℝ} {μ w : α → ℝ}

section MeanFunctional

variable (ν : Θ → Kernel α 𝓨) [∀ θ, IsMarkovKernel (ν θ)] (mean : Θ → α → ℝ) {θ' : Θ}

omit [Fintype α] in
/-- The alternatives to an arm `a` in Any Low Arm are the admissible models in which the mean of
`a` is at least `γ`. -/
lemma mem_alt_anyLowArmTask_some_iff {a : α} :
    θ' ∈ (anyLowArmTask ν mean γ).alt (some a) ↔
      γ ≤ mean θ' a ∧ ((∃ b, mean θ' b < γ) ∨ ∀ b, γ < mean θ' b) := by
  simp only [IdentTask.mem_alt_iff, M_anyLowArmTask, Set.mem_ofPred_eq,
    some_mem_correct_anyLowArmTask, not_lt]
  exact and_comm

omit [Fintype α] in
/-- The alternatives to `none` in Any Low Arm are the models with some mean below `γ`. -/
lemma mem_alt_anyLowArmTask_none_iff :
    θ' ∈ (anyLowArmTask ν mean γ).alt none ↔ ∃ a, mean θ' a < γ := by
  simp only [IdentTask.mem_alt_iff, M_anyLowArmTask, Set.mem_ofPred_eq,
    none_mem_correct_anyLowArmTask]
  exact ⟨fun ⟨h, h'⟩ ↦ h.resolve_right h', fun h ↦
    ⟨Or.inl h, fun h' ↦ let ⟨a, ha⟩ := h; (h' a).not_gt ha⟩⟩

end MeanFunctional

variable (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)]

/-! ### The answers `some a` -/

/-- **The cost of the alternatives to an arm in Any Low Arm** [DK19, Example 1]. Let the arm laws
belong to exponential families `(ρ a, T a)` with divergences `d_a`, in the sense that
`KL(ν_c(μ), ν_c(μ')) = d_c(μ c, μ' c)` for all vectors of means `μ'` of the families, let `γ` be a
mean of every family and let `μ` be a vector of means of the families with `μ a ≤ γ`. Then on the
vectors of means of the families, for every nonnegative allocation `w`,
`D(μ, w, ¬a) = w a d_a(μ a, γ)`: this infimum is approached by moving the mean of `a` above `γ`,
ever closer to `γ`. -/
theorem altCost_anyLowArmTask_restrict_some (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    {a : α} (ha : μ a ≤ γ) (hw : 0 ≤ w) :
    ((anyLowArmTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).altCost
        μ w (some a) =
      ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) γ) := by
  classical
  have hνt : ((anyLowArmTask ν id γ).restrict
      {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).ν = ν := by
    simp
  refine le_antisymm ?_ ?_
  · -- Upper bound: move the mean of `a` to `x > γ`, as well as the means equal to `γ` so that the
    -- moved vector is admissible, and let `x` decrease to `γ`.
    let μx : ℝ → α → ℝ := fun x c ↦ if c = a ∨ μ c = γ then x else μ c
    have hcont (c : α) : ContinuousAt (fun x ↦ μx x c) γ := by
      by_cases hc : c = a ∨ μ c = γ <;> simp only [μx, hc, ite_true, ite_false]
      exacts [continuousAt_id, continuousAt_const]
    have hmem (c : α) : μx γ c ∈ (ρ c).expFamilyMeans (T c) := by
      by_cases hc : c = a ∨ μ c = γ <;> simp only [μx, hc, ite_true, ite_false]
      exacts [hγ c, hμ c]
    -- In the limit, only the move of `a` costs something.
    have h_lim : ∑ c, ENNReal.ofReal (w c * (ρ c).expFamilyDiv (T c) (μ c) (μx γ c)) =
        ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) γ) := by
      rw [Finset.sum_eq_single a (fun c _ hc ↦ ?_) (by simp)]
      · simp [μx]
      · by_cases hcγ : μ c = γ
        · simp [μx, hcγ, expFamilyDiv_self]
        · simp [μx, hc, hcγ, expFamilyDiv_self]
    rw [← h_lim]
    refine IdentTask.altCost_le_sum_ofReal_mul_of_eventually hνt
      (fun c ↦ isDivergenceOn_expFamilyDiv (hT c)) hν hw hμ (l := 𝓝[>] γ) nhdsWithin_le_nhds
      hcont hmem ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : γ < x) hS
    have hne (c : α) : μx x c ≠ γ := by
      by_cases hc : c = a ∨ μ c = γ
      · simpa [μx, hc] using hx.ne'
      · simpa [μx, hc] using (not_or.1 hc).2
    rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_anyLowArmTask_some_iff]
    refine ⟨⟨by simp [μx, hx.le], ?_⟩, hS⟩
    by_cases h : ∃ b, μx x b < γ
    · exact Or.inl h
    · exact Or.inr fun b ↦ (not_lt.1 fun hb ↦ h ⟨b, hb⟩).lt_of_ne' (hne b)
  · -- Lower bound: an alternative has the mean of `a` at least `γ`.
    rw [IdentTask.altCost_def]
    refine le_iInf₂ fun μ' hμ' ↦ ?_
    rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_anyLowArmTask_some_iff] at hμ'
    exact IdentTask.ofReal_mul_le_cost hνt hν hw hμ'.2 a (isDivergenceOn_expFamilyDiv (hT a))
      (hμ a) (hγ a) (Set.mem_uIcc.2 (Or.inl ⟨ha, hμ'.1.1⟩))

/-- **The game value of an arm in Any Low Arm** [DK19, Example 1]. Under the assumptions of
`altCost_anyLowArmTask_restrict_some`, if `μ a ≤ γ`, then `D(μ, ¬a) = d_a(μ a, γ)`. -/
theorem answerValue_anyLowArmTask_restrict_some (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    {a : α} (ha : μ a ≤ γ) :
    ((anyLowArmTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).answerValue
        μ (some a) =
      ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) γ) := by
  classical
  rw [IdentTask.answerValue_def]
  refine le_antisymm (iSup₂_le fun v hv ↦ ?_) (le_iSup₂_of_le (Pi.single a 1) (single_mem_simplex a)
    ?_)
  · rw [altCost_anyLowArmTask_restrict_some ν hT hγ hμ hν ha (mem_simplex_iff.1 hv).1]
    exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (expFamilyDiv_nonneg (hμ a) (hγ a))
      ((simplex_subset_Icc hv).2 a))
  · rw [altCost_anyLowArmTask_restrict_some ν hT hγ hμ hν ha
      (mem_simplex_iff.1 (single_mem_simplex a)).1]
    simp

/-- **The optimal allocation of an arm in Any Low Arm** [DK19, Example 1]. Under the assumptions of
`altCost_anyLowArmTask_restrict_some`, if `μ a < γ`, then the only optimal allocation of the answer
`a` is the vertex `Pi.single a 1`: sample only the arm `a`. -/
theorem optAlloc_anyLowArmTask_restrict_some [DecidableEq α] (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    {a : α} (ha : μ a < γ) :
    ((anyLowArmTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).optAlloc
        μ (some a) = {Pi.single a 1} := by
  have hd := expFamilyDiv_pos (hμ a) (hγ a) ha.ne
  ext v
  rw [IdentTask.mem_optAlloc_iff, answerValue_anyLowArmTask_restrict_some ν hT hγ hμ hν ha.le,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hv, hva⟩
    rw [altCost_anyLowArmTask_restrict_some ν hT hγ hμ hν ha.le (mem_simplex_iff.1 hv).1,
      ENNReal.ofReal_eq_ofReal_iff (mul_nonneg ((mem_simplex_iff.1 hv).1 a) hd.le) hd.le,
      mul_eq_right₀ hd.ne'] at hva
    exact eq_single_of_mem_simplex hv hva
  · rintro rfl
    refine ⟨single_mem_simplex a, ?_⟩
    rw [altCost_anyLowArmTask_restrict_some ν hT hγ hμ hν ha.le
      (mem_simplex_iff.1 (single_mem_simplex a)).1]
    simp

/-! ### The answer `none` -/

/-- The cost of the alternatives to `none` in Any Low Arm is the cost of the alternatives to
`false` in minimum threshold: both are the vectors with some mean below `γ`. -/
private lemma altCost_anyLowArmTask_restrict_none_eq (S : Set (α → ℝ)) (μ w : α → ℝ) :
    ((anyLowArmTask ν id γ).restrict S).altCost μ w none =
      ((minThresholdTask ν id γ).restrict S).altCost μ w false := by
  have h_alt : (anyLowArmTask ν id γ).alt none = (minThresholdTask ν id γ).alt false := Set.ext
    fun _ ↦ (mem_alt_anyLowArmTask_none_iff ν id).trans
      (mem_alt_minThresholdTask_false_iff ν id).symm
  simp only [IdentTask.altCost_def, IdentTask.cost_def, IdentTask.alt_restrict, h_alt,
    IdentTask.ν_restrict, ν_anyLowArmTask, ν_minThresholdTask]

/-- **The cost of the alternatives to `none` in Any Low Arm** [DK19, Example 1]. Under the
assumptions of `altCost_anyLowArmTask_restrict_some` on the arm laws, if all the means of `μ` are
at least `γ`, then on the vectors of means of the families, for every nonnegative allocation `w`,
`D(μ, w, ¬none) = min_a w a d_a(μ a, γ)`. -/
theorem altCost_anyLowArmTask_restrict_none (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, γ ≤ μ a) (hw : 0 ≤ w) :
    ((anyLowArmTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).altCost
        μ w none =
      ⨅ a, ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) γ) := by
  rw [altCost_anyLowArmTask_restrict_none_eq,
    altCost_minThresholdTask_restrict_false ν hT hγ hμ hν hμγ hw]

/-- **The game value of `none` in Any Low Arm** [DK19, Example 1]. Under the assumptions of
`altCost_anyLowArmTask_restrict_some` on the arm laws, if all the means of `μ` are above `γ`, then
`D(μ, ¬none) = (∑ a, d_a(μ a, γ)⁻¹)⁻¹`. -/
theorem answerValue_anyLowArmTask_restrict_none
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, γ < μ a) :
    ((anyLowArmTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).answerValue
        μ none =
      ENNReal.ofReal (∑ a, ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹)⁻¹ := by
  rw [← answerValue_minThresholdTask_restrict_false ν hT hγ hμ hν hμγ]
  simp only [IdentTask.answerValue_def, altCost_anyLowArmTask_restrict_none_eq]

/-- **The optimal allocation of `none` in Any Low Arm** [DK19, Example 1]. Under the assumptions of
`altCost_anyLowArmTask_restrict_some` on the arm laws, if all the means of `μ` are above `γ`, then
the only optimal allocation of `none` is proportional to `d_a(μ a, γ)⁻¹`. -/
theorem optAlloc_anyLowArmTask_restrict_none [Nonempty α]
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, γ < μ a) :
    ((anyLowArmTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).optAlloc
        μ none =
      {fun a ↦ ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹ /
        ∑ b, ((ρ b).expFamilyDiv (T b) (μ b) γ)⁻¹} := by
  rw [← optAlloc_minThresholdTask_restrict_false ν hT hγ hμ hν hμγ]
  ext v
  simp only [IdentTask.mem_optAlloc_iff, IdentTask.answerValue_def,
    altCost_anyLowArmTask_restrict_none_eq]

/-- **The characteristic time of Any Low Arm when all the means are above the threshold**
[DK19, Example 1]. Under the assumptions of `altCost_anyLowArmTask_restrict_some` on the arm laws,
if all the means of `μ` are above `γ`, then `T*(μ) = ∑ a, d_a(μ a, γ)⁻¹`. -/
theorem charTime_anyLowArmTask_restrict_of_forall_lt [Nonempty α]
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, γ < μ a) :
    ((anyLowArmTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).charTime μ =
      ENNReal.ofReal (∑ a, ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹) := by
  have hpos := sum_inv_pos fun a ↦ expFamilyDiv_pos (hμ a) (hγ a) (hμγ a).ne'
  have h_corr : ((anyLowArmTask ν id γ).restrict
      {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).correct μ = {none} := by
    ext i
    cases i with
    | none => simpa using hμγ
    | some a => simpa using (hμγ a).le
  rw [IdentTask.charTime_eq_inv_answerValue _ h_corr,
    answerValue_anyLowArmTask_restrict_none ν hT hγ hμ hν hμγ, ENNReal.ofReal_inv_of_pos hpos,
    inv_inv]

/-! ### Oracle answers and oracle allocations -/

/-- If some mean is below `γ`, the value of every arm `a` is `D(μ, ¬a) = d_a(μ a, max (μ a) γ)`:
`d_a(μ a, γ)` for the arms below `γ`, and `0` for the arms above `γ`, which are incorrect. -/
private lemma answerValue_anyLowArmTask_restrict_some_of_exists_lt
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (h : ∃ b, μ b < γ) (a : α) :
    ((anyLowArmTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).answerValue
        μ (some a) =
      ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (max (μ a) γ)) := by
  rcases le_or_gt (μ a) γ with ha | ha
  · rw [max_eq_right ha, answerValue_anyLowArmTask_restrict_some ν hT hγ hμ hν ha]
  · rw [max_eq_left ha.le, expFamilyDiv_self, ENNReal.ofReal_zero]
    refine IdentTask.answerValue_eq_zero_of_mem_alt _ ?_
    rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_anyLowArmTask_some_iff]
    exact ⟨⟨ha.le, Or.inl h⟩, hμ⟩

/-- If some mean is below `γ`, the answer `none` is incorrect and has value `0`. -/
private lemma answerValue_anyLowArmTask_restrict_none_of_exists_lt
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a)) (h : ∃ b, μ b < γ) :
    ((anyLowArmTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).answerValue
        μ none = 0 := by
  refine IdentTask.answerValue_eq_zero_of_mem_alt _ ?_
  rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_anyLowArmTask_none_iff]
  exact ⟨h, hμ⟩

/-- **The value of the game of Any Low Arm when some mean is below the threshold**
[DK19, Example 1]. Under the assumptions of `altCost_anyLowArmTask_restrict_some` on the arm laws,
if some mean of `μ` is below `γ`, then `D(μ) = max_a d_a(μ a, max (μ a) γ)`, the largest value of
the arms below `γ`. -/
theorem gameValue_anyLowArmTask_restrict_of_exists_lt (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (h : ∃ b, μ b < γ) :
    ((anyLowArmTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).gameValue μ =
      ⨆ a, ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (max (μ a) γ)) := by
  rw [IdentTask.gameValue_eq_iSup_answerValue _ (by
    rw [IdentTask.M_restrict, M_anyLowArmTask]; exact ⟨Or.inl h, hμ⟩),
    iSup_option,
    answerValue_anyLowArmTask_restrict_none_of_exists_lt ν hμ h, zero_max]
  exact iSup_congr (answerValue_anyLowArmTask_restrict_some_of_exists_lt ν hT hγ hμ hν h)

/-- **The characteristic time of Any Low Arm when some mean is below the threshold**
[DK19, Example 1]. Under the assumptions of `altCost_anyLowArmTask_restrict_some` on the arm laws,
if some mean of `μ` is below `γ`, then `T*(μ) = (max_a d_a(μ a, max (μ a) γ))⁻¹`. -/
theorem charTime_anyLowArmTask_restrict_of_exists_lt (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (h : ∃ b, μ b < γ) :
    ((anyLowArmTask ν id γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).charTime μ =
      (⨆ a, ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (max (μ a) γ)))⁻¹ := by
  rw [IdentTask.charTime_def, gameValue_anyLowArmTask_restrict_of_exists_lt ν hT hγ hμ hν h]

/-- **The oracle answers of Any Low Arm** [DK19, Example 1]. Under the assumptions of
`altCost_anyLowArmTask_restrict_some` on the arm laws, if some mean of `μ` is below `γ`, then the
oracle answers are the arms `a` maximizing `d_a(μ a, max (μ a) γ)`. -/
theorem oracleAnswers_anyLowArmTask_restrict_of_exists_lt
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (h : ∃ b, μ b < γ) :
    ((anyLowArmTask ν id γ).restrict
        {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).oracleAnswers μ =
      some '' {a | ∀ b, (ρ b).expFamilyDiv (T b) (μ b) (max (μ b) γ) ≤
        (ρ a).expFamilyDiv (T a) (μ a) (max (μ a) γ)} := by
  have hnn (a : α) : 0 ≤ (ρ a).expFamilyDiv (T a) (μ a) (max (μ a) γ) := by
    rcases max_choice (μ a) γ with h' | h' <;> rw [h']
    exacts [expFamilyDiv_nonneg (hμ a) (hμ a), expFamilyDiv_nonneg (hμ a) (hγ a)]
  have hsome := answerValue_anyLowArmTask_restrict_some_of_exists_lt ν hT hγ hμ hν h
  have hnone := answerValue_anyLowArmTask_restrict_none_of_exists_lt ν hμ h
  obtain ⟨b, hb⟩ := h
  have hbpos : 0 < (ρ b).expFamilyDiv (T b) (μ b) (max (μ b) γ) := by
    rw [max_eq_right hb.le]
    exact expFamilyDiv_pos (hμ b) (hγ b) hb.ne
  ext i
  cases i with
  | none =>
    simp only [IdentTask.mem_oracleAnswers_iff, Set.mem_image, reduceCtorEq, and_false,
      exists_false, iff_false, not_forall, not_le, hnone]
    exact ⟨some b, by rw [hsome]; exact ENNReal.ofReal_pos.2 hbpos⟩
  | some a =>
    simp only [IdentTask.mem_oracleAnswers_iff, Set.mem_image, Option.some.injEq,
      exists_eq_right, Set.mem_ofPred_eq, Option.forall, hnone, zero_le, true_and, hsome,
      ENNReal.ofReal_le_ofReal_iff (hnn a)]

/-- **The oracle allocations of Any Low Arm** [DK19, Example 1]. Under the assumptions of
`altCost_anyLowArmTask_restrict_some` on the arm laws, if some mean of `μ` is below `γ`, then the
oracle allocations are the vertices `Pi.single a 1` of the arms `a` maximizing
`d_a(μ a, max (μ a) γ)`. -/
theorem oracleAlloc_anyLowArmTask_restrict_of_exists_lt [DecidableEq α]
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (h : ∃ b, μ b < γ) :
    ((anyLowArmTask ν id γ).restrict
        {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).oracleAlloc μ =
      (fun a ↦ Pi.single a 1) '' {a | ∀ b, (ρ b).expFamilyDiv (T b) (μ b) (max (μ b) γ) ≤
        (ρ a).expFamilyDiv (T a) (μ a) (max (μ a) γ)} := by
  -- A maximizing arm is below `γ`, since the arms above `γ` have value `0`.
  have hlt {a : α} (ha : ∀ b, (ρ b).expFamilyDiv (T b) (μ b) (max (μ b) γ) ≤
      (ρ a).expFamilyDiv (T a) (μ a) (max (μ a) γ)) : μ a < γ := by
    obtain ⟨b, hb⟩ := h
    by_contra hge
    have h_le := ha b
    rw [max_eq_left (not_lt.1 hge), expFamilyDiv_self, max_eq_right hb.le] at h_le
    exact (expFamilyDiv_pos (hμ b) (hγ b) hb.ne).not_ge h_le
  ext v
  rw [IdentTask.oracleAlloc_def,
    oracleAnswers_anyLowArmTask_restrict_of_exists_lt ν hT hγ hμ hν h, Set.biUnion_image]
  simp only [Set.mem_iUnion, exists_prop, Set.mem_image]
  refine exists_congr fun a ↦ and_congr_right fun ha ↦ ?_
  rw [optAlloc_anyLowArmTask_restrict_some ν hT hγ hμ hν (hlt ha), Set.mem_singleton_iff, eq_comm]

/-- **The oracle allocations of Any Low Arm need not be convex** [DK19, Proposition 5]. Under the
assumptions of `altCost_anyLowArmTask_restrict_some` on the arm laws, if some mean of `μ` is below
`γ` and two distinct arms `a` and `b` both maximize `d_c(μ c, max (μ c) γ)`, then the oracle
allocations `w*(μ)` are not convex, while each `w*(μ, ¬i)` is (`IdentTask.convex_optAlloc`). -/
theorem not_convex_oracleAlloc_anyLowArmTask_restrict (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (h : ∃ b, μ b < γ) {a b : α} (hab : a ≠ b)
    (ha : ∀ c, (ρ c).expFamilyDiv (T c) (μ c) (max (μ c) γ) ≤
      (ρ a).expFamilyDiv (T a) (μ a) (max (μ a) γ))
    (hb : ∀ c, (ρ c).expFamilyDiv (T c) (μ c) (max (μ c) γ) ≤
      (ρ b).expFamilyDiv (T b) (μ b) (max (μ b) γ)) :
    ¬ Convex ℝ (((anyLowArmTask ν id γ).restrict
        {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).oracleAlloc μ) := by
  classical
  rw [oracleAlloc_anyLowArmTask_restrict_of_exists_lt ν hT hγ hμ hν h]
  exact not_convex_image_single ha hb hab

/-! ### Gaussian arms -/

variable [MeasurableSingletonClass α] {σ2 : ℝ≥0}

/-- **The oracle allocations of Gaussian Any Low Arm** [DK19, Example 1]. For Gaussian arms with a
common variance `σ2 ≠ 0` and a vector of means `μ` whose smallest mean `μ a₀` is below `γ`, the
oracle allocations are the vertices `Pi.single a 1` of the arms `a` of smallest mean. -/
theorem oracleAlloc_anyLowArmTask_gaussianBandit [DecidableEq α] (hσ2 : σ2 ≠ 0) {a₀ : α}
    (ha₀ : ∀ a, μ a₀ ≤ μ a) (hγ : μ a₀ < γ) :
    (anyLowArmTask (Bandits.gaussianBandit · σ2) id γ).oracleAlloc μ =
      (fun a ↦ Pi.single a 1) '' {a | μ a = μ a₀} := by
  rw [← (anyLowArmTask (Bandits.gaussianBandit · σ2) id γ).restrict_univ,
    ← setOf_forall_mem_expFamilyMeans_gaussianReal 0 hσ2,
    oracleAlloc_anyLowArmTask_restrict_of_exists_lt (ρ := fun _ ↦ gaussianReal 0 σ2)
      (T := fun _ ↦ id) _
      (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
      (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (fun μ' _ ↦ Bandits.klDiv_gaussianBandit_eq_ofReal_expFamilyDiv hσ2 μ μ') ⟨a₀, hγ⟩]
  simp only [expFamilyDiv_gaussianReal 0 hσ2]
  congr 1
  -- The arms maximizing `(μ a - max (μ a) γ)² / (2 σ2)` are those of smallest mean.
  have hσ2' : 0 < 2 * (σ2 : ℝ) := by
    have := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hσ2)
    positivity
  ext a
  simp only [Set.mem_ofPred_eq, div_le_div_iff_of_pos_right hσ2']
  constructor
  · intro ha
    have h_le := ha a₀
    rw [max_eq_right hγ.le] at h_le
    rcases le_or_gt γ (μ a) with h | h
    · rw [max_eq_left h, sub_self] at h_le
      nlinarith [mul_pos (sub_pos.2 hγ) (sub_pos.2 hγ)]
    · rw [max_eq_right h.le] at h_le
      nlinarith [ha₀ a]
  · intro ha b
    rw [ha, max_eq_right hγ.le]
    rcases le_total (μ b) γ with h | h
    · rw [max_eq_right h]
      nlinarith [ha₀ b]
    · rw [max_eq_left h, sub_self]
      simpa using sq_nonneg (μ a₀ - γ)

/-- **A model of Gaussian Any Low Arm with non-convex oracle allocations** [DK19, Proposition 5].
For Gaussian arms with a common variance `σ2 ≠ 0`, if two distinct arms `a` and `b` share the
smallest mean `μ a = μ b < γ`, then the oracle allocations `w*(μ)`, which contain the vertices
`Pi.single a 1` and `Pi.single b 1` but not their midpoint, are not convex. -/
theorem not_convex_oracleAlloc_anyLowArmTask_gaussianBandit (hσ2 : σ2 ≠ 0) {a b : α}
    (hab : a ≠ b) (hμab : μ a = μ b) (ha : ∀ c, μ a ≤ μ c) (hγ : μ a < γ) :
    ¬ Convex ℝ ((anyLowArmTask (Bandits.gaussianBandit · σ2) id γ).oracleAlloc μ) := by
  classical
  rw [oracleAlloc_anyLowArmTask_gaussianBandit hσ2 ha hγ]
  exact not_convex_image_single (s := {c | μ c = μ a}) rfl hμab.symm hab

end LMLExplore.Identification
