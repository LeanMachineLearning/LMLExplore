/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.MeanVector
public import LMLExplore.Identification.Task.TransportationCost
public import LMLExplore.Bandits.Instances
public import LMLExplore.Probability.Distributions.ExponentialFamily.Gaussian

/-!
# The pure exploration game of thresholding and minimum-threshold tasks

For the tasks that compare the means of the arms with a threshold `γ`, the transportation costs
and the characteristic time have closed forms. Let the arm `a` belong to an exponential family
`(ρ a, T a)` with divergence `d_a` in the mean parametrization, so that the transportation cost
from a vector of means `μ` to a vector of means `λ` of the families is
`cost_μ(w, λ) = ∑ a, w a d_a(μ a, λ a)`, and let `γ` be a mean of every family.

* *Thresholding* (`thresholdingTask ν γ`): the alternatives to the set `S*` of the arms of `μ` with
  mean above `γ` are the vectors in which some arm `a` crossed `γ`. The cheapest of them moves a
  single arm to the other side of `γ`, as close to `γ` as wanted, so that
  `D(μ, w, ¬S*) = min_a w a d_a(μ a, γ)`. The allocation maximizing it is proportional to
  `d_a(μ a, γ)⁻¹`, and `T*(μ) = ∑ a, d_a(μ a, γ)⁻¹`. For Gaussian arms with variance `σ2`,
  `T*(μ) = ∑ a, 2 σ2 / (μ a - γ)²`.
* *Minimum threshold* (`minThresholdTask ν γ`): if all the means are above `γ` (answer `false`),
  the alternatives are the vectors with some mean below `γ`, and the game is that of thresholding:
  `D(μ, w, ¬false) = min_a w a d_a(μ a, γ)` and `T*(μ) = ∑ a, d_a(μ a, γ)⁻¹`
  [DK19, Lemma 37; KKG18, Lemma 1]. If some mean is below `γ` (answer `true`), the alternatives
  are the vectors with all means above `γ`: every arm below `γ` has to be moved to `γ`, so that
  `D(μ, w, ¬true) = ∑ a, w a d_a(μ a, max (μ a) γ)`, maximized by sampling only an arm of largest
  `d_a(μ a, max (μ a) γ)`, and `T*(μ) = (max_a d_a(μ a, max (μ a) γ))⁻¹`. For Gaussian arms with a
  common variance `σ2`, this is `2 σ2 / (μ a₀ - γ)²` for an arm `a₀` of smallest mean
  [DK19, Lemma 38; KKG18, Lemma 1].

The admissible models are the vectors of means of the families, `task.restrict S` with
`S = {λ | ∀ c, λ c ∈ (ρ c).expFamilyMeans (T c)}`, as for best arm identification in
`LMLExplore/Identification/Task/BestArm.lean`. Each arm has its own family: the arms do not interact
in these tasks.

## Main statements

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

variable {α 𝓨 ℐ : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} [Fintype α]
  {ρ : α → Measure 𝓨} {T : α → 𝓨 → ℝ} {γ : ℝ} {μ w : α → ℝ}

/-! ### Transportation costs of arms in exponential families -/

section Cost

variable {task : IdentTask α (α → ℝ) ℐ 𝓨} {i : ℐ} {ν : (α → ℝ) → Kernel α 𝓨}

/-- On the vectors of means of the families, the transportation cost from `μ` to `μ'` is
`∑ c, w c d_c(μ c, μ' c)` when the divergences between the arm laws are those of the families. -/
private lemma cost_eq_sum
    (hνt : task.ν = ν) (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hw : 0 ≤ w) {μ' : α → ℝ} (hμ' : ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) :
    task.cost w μ μ' = ∑ c, ENNReal.ofReal (w c * (ρ c).expFamilyDiv (T c) (μ c) (μ' c)) := by
  rw [IdentTask.cost_def, hνt]
  exact Finset.sum_congr rfl fun c _ ↦ by rw [hν μ' hμ' c, ENNReal.ofReal_mul (hw c)]

/-- Moving the mean of the arm `a` of `μ` to a mean `x` of its family costs `w a d_a(μ a, x)`. -/
private lemma cost_update_eq [DecidableEq α]
    (hνt : task.ν = ν) (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hw : 0 ≤ w) (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c)) (a : α) {x : ℝ}
    (hx : x ∈ (ρ a).expFamilyMeans (T a)) :
    task.cost w μ (Function.update μ a x) =
      ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) x) := by
  have hμx : ∀ c, Function.update μ a x c ∈ (ρ c).expFamilyMeans (T c) :=
    (Function.forall_update_iff μ fun c y ↦ y ∈ (ρ c).expFamilyMeans (T c)).2
      ⟨hx, fun c _ ↦ hμ c⟩
  rw [cost_eq_sum hνt hν hw hμx, Finset.sum_eq_single a (fun c _ hc ↦ ?_) (by simp)]
  · simp
  · simp [Function.update_of_ne hc, expFamilyDiv_self]

/-- **Moving one arm close to the threshold.** If the vectors obtained from `μ` by moving the mean
of the arm `a` to `x` are alternatives to `i` for all `x` near `γ` along a filter `l ≤ 𝓝 γ`, then
`D(μ, w, ¬i) ≤ w a d_a(μ a, γ)`. -/
private lemma altCost_le_of_eventually [DecidableEq α] (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hνt : task.ν = ν) (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hw : 0 ≤ w) (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c)) (a : α)
    (hγ : γ ∈ (ρ a).expFamilyMeans (T a)) {l : Filter ℝ} [l.NeBot] (hl : l ≤ 𝓝 γ)
    (h_alt : ∀ᶠ x in l, Function.update μ a x ∈ task.alt i) :
    task.altCost μ w i ≤ ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) γ) := by
  have h_tendsto : Tendsto (fun x ↦ ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) x)) l
      (𝓝 (ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) γ))) :=
    (ENNReal.continuous_ofReal.continuousAt.comp (continuousAt_const.mul
      (hasDerivAt_expFamilyDiv_right (hT a) (μ a) hγ).continuousAt)).tendsto.mono_left hl
  refine ge_of_tendsto h_tendsto ?_
  filter_upwards [h_alt, hl (expFamilyMeans_mem_nhds (hT a) hγ)] with x hx hxm
  rw [← cost_update_eq hνt hν hw hμ a hxm]
  exact task.altCost_le_cost hx w

/-- **A lower bound on the cost of a model in which one arm crossed the threshold.** If `γ` lies
between `μ a` and `μ' a`, then `w a d_a(μ a, γ) ≤ cost_μ(w, μ')`. -/
private lemma ofReal_mul_expFamilyDiv_le_cost (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hνt : task.ν = ν) (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hw : 0 ≤ w) {μ' : α → ℝ} (hμ' : ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) (a : α)
    (hγ : γ ∈ (ρ a).expFamilyMeans (T a)) (h : γ ∈ uIcc (μ a) (μ' a)) :
    ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) γ) ≤ task.cost w μ μ' := by
  rw [cost_eq_sum hνt hν hw hμ']
  refine le_trans ?_ (Finset.single_le_sum (f := fun c ↦
    ENNReal.ofReal (w c * (ρ c).expFamilyDiv (T c) (μ c) (μ' c))) (fun _ _ ↦ zero_le)
    (Finset.mem_univ a))
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (expFamilyDiv_le_expFamilyDiv_of_mem_uIcc (hT a) hγ (hμ' a) h) (hw a))

end Cost

/-! ### The game value of a weighted minimum -/

section MinGame

variable {task : IdentTask α (α → ℝ) ℐ 𝓨} {i : ℐ} {c : α → ℝ}

/-- At the allocation proportional to `c⁻¹`, all the weighted entries `w a c a` equal
`(∑ b, (c b)⁻¹)⁻¹`. -/
private lemma iInf_ofReal_inv_div_sum_inv_mul [Nonempty α] (hc : ∀ a, 0 < c a) :
    ⨅ a, ENNReal.ofReal ((c a)⁻¹ / (∑ b, (c b)⁻¹) * c a) =
      ENNReal.ofReal (∑ b, (c b)⁻¹)⁻¹ := by
  have h (a : α) : ENNReal.ofReal ((c a)⁻¹ / (∑ b, (c b)⁻¹) * c a) =
      ENNReal.ofReal (∑ b, (c b)⁻¹)⁻¹ := by
    congr 1
    field_simp [(hc a).ne']
  simp_rw [h]
  exact iInf_const

/-- If `D(μ, w, ¬i) = min_a w a c a` on the simplex, for positive weights `c`, then
`D(μ, ¬i) = (∑ a, (c a)⁻¹)⁻¹`. -/
private lemma answerValue_eq_of_altCost_eq_iInf [Nonempty α] (hc : ∀ a, 0 < c a)
    (h : ∀ w ∈ simplex α, task.altCost μ w i = ⨅ a, ENNReal.ofReal (w a * c a)) :
    task.answerValue μ i = ENNReal.ofReal (∑ a, (c a)⁻¹)⁻¹ := by
  have hv := inv_div_sum_inv_mem_simplex hc
  rw [IdentTask.answerValue_def]
  refine le_antisymm (iSup₂_le fun w hw ↦ ?_) ?_
  · obtain ⟨a, ha⟩ := exists_mul_le_inv_sum_inv hw hc
    rw [h w hw]
    exact (iInf_le _ a).trans (ENNReal.ofReal_le_ofReal ha)
  · refine le_of_eq_of_le ?_ (le_iSup₂ (f := fun w _ ↦ task.altCost μ w i) _ hv)
    rw [h _ hv, iInf_ofReal_inv_div_sum_inv_mul hc]

/-- If `D(μ, w, ¬i) = min_a w a c a` on the simplex, for positive weights `c`, then the only
optimal allocation is proportional to `c⁻¹`. -/
private lemma optAlloc_eq_of_altCost_eq_iInf [Nonempty α] (hc : ∀ a, 0 < c a)
    (h : ∀ w ∈ simplex α, task.altCost μ w i = ⨅ a, ENNReal.ofReal (w a * c a)) :
    task.optAlloc μ i = {fun a ↦ (c a)⁻¹ / ∑ b, (c b)⁻¹} := by
  have hv := inv_div_sum_inv_mem_simplex hc
  ext v
  rw [IdentTask.mem_optAlloc_iff, Set.mem_singleton_iff, answerValue_eq_of_altCost_eq_iInf hc h]
  refine ⟨fun ⟨hv', hv_eq⟩ ↦ eq_inv_div_sum_inv_of_le_mul hv' hc fun a ↦ ?_, ?_⟩
  · rw [h v hv'] at hv_eq
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ((mem_simplex_iff.1 hv').1 a) (hc a).le)).1
      (hv_eq ▸ iInf_le _ a)
  · rintro rfl
    exact ⟨hv, by rw [h _ hv, iInf_ofReal_inv_div_sum_inv_mul hc]⟩

end MinGame

/-! ### Thresholding -/

section Thresholding

variable (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)]

/-- **The cost of the alternatives in thresholding.** Let the arm laws belong to exponential
families `(ρ a, T a)` with divergences `d_a`, in the sense that
`KL(ν_c(μ), ν_c(μ')) = d_c(μ c, μ' c)` for all vectors of means `μ'` of the families, let `γ` be a
mean of every family and let `μ` be a vector of means of the families with no mean equal to `γ`,
whose correct answer is the set `s` of the arms with mean above `γ`. Then on the vectors of means
of the families, for every nonnegative allocation `w`, `D(μ, w, ¬s) = min_a w a d_a(μ a, γ)`: the
cheapest alternatives move a single arm across `γ`. -/
theorem altCost_thresholdingTask_restrict (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, μ a ≠ γ) {s : Finset α} (hs : ∀ a, a ∈ s ↔ γ < μ a) (hw : 0 ≤ w) :
    ((thresholdingTask ν γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).altCost
        μ w s =
      ⨅ a, ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) γ) := by
  classical
  refine le_antisymm (le_iInf fun a ↦ ?_) ?_
  · -- Upper bound: move the mean of `a` across `γ`, close to `γ`.
    have h_alt {x : ℝ} (hxγ : (γ < x ↔ ¬ γ < μ a)) (hx : x ≠ γ)
        (hxm : x ∈ (ρ a).expFamilyMeans (T a)) :
        Function.update μ a x ∈ ((thresholdingTask ν γ).restrict
          {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).alt s := by
      simp only [IdentTask.alt_restrict, Set.mem_inter_iff, IdentTask.mem_alt_iff,
        M_thresholdingTask, correct_thresholdingTask, Set.mem_ofPred_eq]
      refine ⟨⟨(Function.forall_update_iff μ fun _ y ↦ y ≠ γ).2 ⟨hx, fun c _ ↦ hμγ c⟩,
        fun h ↦ ?_⟩, (Function.forall_update_iff μ fun c y ↦ y ∈ (ρ c).expFamilyMeans (T c)).2
          ⟨hxm, fun c _ ↦ hμ c⟩⟩
      have h' := (h a).symm.trans (hs a)
      simp only [Function.update_self] at h'
      tauto
    have hm := expFamilyMeans_mem_nhds (hT a) (hγ a)
    rcases (hμγ a).lt_or_gt with ha | ha
    · refine altCost_le_of_eventually (l := 𝓝[>] γ) hT (by simp) hν hw hμ a (hγ a)
        nhdsWithin_le_nhds ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hm] with x (hx : γ < x) hxm
      exact h_alt (iff_of_true hx ha.not_gt) hx.ne' hxm
    · refine altCost_le_of_eventually (l := 𝓝[<] γ) hT (by simp) hν hw hμ a (hγ a)
        nhdsWithin_le_nhds ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hm] with x (hx : x < γ) hxm
      exact h_alt (iff_of_false hx.not_gt (not_not.2 ha)) hx.ne hxm
  · -- Lower bound: some arm `a` is on different sides of `γ` in `μ` and `μ'`.
    rw [IdentTask.altCost_def]
    refine le_iInf₂ fun μ' hμ' ↦ ?_
    simp only [IdentTask.alt_restrict, Set.mem_inter_iff, IdentTask.mem_alt_iff,
      M_thresholdingTask, correct_thresholdingTask, Set.mem_ofPred_eq] at hμ'
    obtain ⟨⟨-, h_corr⟩, hμ'⟩ := hμ'
    obtain ⟨a, ha⟩ : ∃ a, ¬ (γ < μ a ↔ γ < μ' a) := by
      by_contra! h
      exact h_corr fun a ↦ (hs a).trans (h a)
    have h_mem : γ ∈ uIcc (μ a) (μ' a) := by
      rw [Set.mem_uIcc]
      by_cases h1 : γ < μ a
      · exact Or.inr ⟨not_lt.1 fun h2 ↦ ha (iff_of_true h1 h2), h1.le⟩
      · exact Or.inl ⟨not_lt.1 h1, (lt_of_not_ge fun h2 ↦ ha (iff_of_false h1 h2.not_gt)).le⟩
    exact (iInf_le _ a).trans
      (ofReal_mul_expFamilyDiv_le_cost hT (by simp) hν hw hμ' a (hγ a) h_mem)

/-- **The game value of thresholding.** Under the assumptions of
`altCost_thresholdingTask_restrict`, the value of the correct answer `s` is
`D(μ, ¬s) = (∑ a, d_a(μ a, γ)⁻¹)⁻¹`. -/
theorem answerValue_thresholdingTask_restrict [Nonempty α]
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, μ a ≠ γ) {s : Finset α} (hs : ∀ a, a ∈ s ↔ γ < μ a) :
    ((thresholdingTask ν γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).answerValue
        μ s =
      ENNReal.ofReal (∑ a, ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹)⁻¹ :=
  answerValue_eq_of_altCost_eq_iInf (fun a ↦ expFamilyDiv_pos (hμ a) (hγ a) (hμγ a))
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
    ((thresholdingTask ν γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).optAlloc
        μ s =
      {fun a ↦ ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹ /
        ∑ b, ((ρ b).expFamilyDiv (T b) (μ b) γ)⁻¹} :=
  optAlloc_eq_of_altCost_eq_iInf (fun a ↦ expFamilyDiv_pos (hμ a) (hγ a) (hμγ a))
    fun _ hw ↦ altCost_thresholdingTask_restrict ν hT hγ hμ hν hμγ hs (mem_simplex_iff.1 hw).1

/-- **The characteristic time of thresholding.** Under the assumptions of
`altCost_thresholdingTask_restrict`, `T*(μ) = ∑ a, d_a(μ a, γ)⁻¹`. -/
theorem charTime_thresholdingTask_restrict [Nonempty α]
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, μ a ≠ γ) :
    ((thresholdingTask ν γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).charTime μ =
      ENNReal.ofReal (∑ a, ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹) := by
  classical
  have hs (a : α) : a ∈ Finset.univ.filter (γ < μ ·) ↔ γ < μ a := by simp
  have hpos : 0 < ∑ a, ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹ :=
    Finset.sum_pos (fun a _ ↦ inv_pos.2 (expFamilyDiv_pos (hμ a) (hγ a) (hμγ a)))
      Finset.univ_nonempty
  rw [IdentTask.charTime_eq_inv_answerValue _
      (by rw [IdentTask.correct_restrict]; exact correct_thresholdingTask_eq_singleton ν),
    answerValue_thresholdingTask_restrict ν hT hγ hμ hν hμγ hs, ENNReal.ofReal_inv_of_pos hpos,
    inv_inv]

/-! #### Gaussian arms -/

variable [MeasurableSingletonClass α] {σ2 : ℝ≥0}

omit [Fintype α] in
/-- For Gaussian arms with a common variance `σ2 ≠ 0`, every vector of means is a vector of means
of the exponential family of `𝒩(0, σ2)`: thresholding restricted to them is thresholding. -/
private lemma restrict_thresholdingTask_gaussianBandit [Countable α] (hσ2 : σ2 ≠ 0) :
    (thresholdingTask (Bandits.gaussianBandit · σ2) γ).restrict
        {μ' : α → ℝ | ∀ c, μ' c ∈ (gaussianReal 0 σ2).expFamilyMeans id} =
      thresholdingTask (Bandits.gaussianBandit · σ2) γ := by
  simp [expFamilyMeans_gaussianReal 0 hσ2]

/-- **The cost of the alternatives in Gaussian thresholding.** For Gaussian arms with a common
variance `σ2 ≠ 0`, a vector of means `μ` with no mean equal to `γ`, whose correct answer is the set
`s` of the arms with mean above `γ`, and a nonnegative allocation `w`,
`D(μ, w, ¬s) = min_a w a (μ a - γ)² / (2 σ2)`. -/
theorem altCost_thresholdingTask_gaussianBandit (hσ2 : σ2 ≠ 0) (hμγ : ∀ a, μ a ≠ γ)
    {s : Finset α} (hs : ∀ a, a ∈ s ↔ γ < μ a) (hw : 0 ≤ w) :
    (thresholdingTask (Bandits.gaussianBandit · σ2) γ).altCost μ w s =
      ⨅ a, ENNReal.ofReal (w a * (μ a - γ) ^ 2 / (2 * σ2)) := by
  rw [← restrict_thresholdingTask_gaussianBandit hσ2,
    altCost_thresholdingTask_restrict (ρ := fun _ ↦ gaussianReal 0 σ2) (T := fun _ ↦ id) _
      (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2) (fun _ ↦ by simp [hσ2])
      (fun _ ↦ by simp [hσ2])
      (fun μ' _ c ↦ by rw [Bandits.klDiv_gaussianBandit _ _ hσ2, expFamilyDiv_gaussianReal 0 hσ2])
      hμγ hs hw]
  simp only [expFamilyDiv_gaussianReal 0 hσ2, mul_div_assoc]

/-- **The characteristic time of Gaussian thresholding.** For Gaussian arms with a common variance
`σ2 ≠ 0` and a vector of means `μ` with no mean equal to `γ`, `T*(μ) = ∑ a, 2 σ2 / (μ a - γ)²`. -/
theorem charTime_thresholdingTask_gaussianBandit [Nonempty α] (hσ2 : σ2 ≠ 0)
    (hμγ : ∀ a, μ a ≠ γ) :
    (thresholdingTask (Bandits.gaussianBandit · σ2) γ).charTime μ =
      ENNReal.ofReal (∑ a, 2 * σ2 / (μ a - γ) ^ 2) := by
  rw [← restrict_thresholdingTask_gaussianBandit hσ2,
    charTime_thresholdingTask_restrict (ρ := fun _ ↦ gaussianReal 0 σ2) (T := fun _ ↦ id) _
      (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2) (fun _ ↦ by simp [hσ2])
      (fun _ ↦ by simp [hσ2])
      (fun μ' _ c ↦ by rw [Bandits.klDiv_gaussianBandit _ _ hσ2, expFamilyDiv_gaussianReal 0 hσ2])
      hμγ]
  simp only [expFamilyDiv_gaussianReal 0 hσ2, inv_div]

end Thresholding

/-! ### Minimum threshold -/

section MinThreshold

variable (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)]

/-- **The cost of the alternatives to `false` in minimum threshold** [DK19, Lemma 37;
KKG18, Lemma 1]. Under the assumptions of `altCost_thresholdingTask_restrict` on the arm laws, if
all the means of `μ` are at least `γ`, then on the vectors of means of the families, for every
nonnegative allocation `w`, `D(μ, w, ¬false) = min_a w a d_a(μ a, γ)`: the cheapest alternatives
move a single arm below `γ`. -/
theorem altCost_minThresholdTask_restrict_false (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, γ ≤ μ a) (hw : 0 ≤ w) :
    ((minThresholdTask ν γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).altCost
        μ w false =
      ⨅ a, ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) γ) := by
  classical
  refine le_antisymm (le_iInf fun a ↦ ?_) ?_
  · -- Upper bound: move the mean of `a` below `γ`, close to `γ`.
    refine altCost_le_of_eventually (l := 𝓝[<] γ) hT (by simp) hν hw hμ a (hγ a)
      nhdsWithin_le_nhds ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (expFamilyMeans_mem_nhds (hT a) (hγ a))] with x (hx : x < γ) hxm
    simp only [IdentTask.alt_restrict, Set.mem_inter_iff, IdentTask.mem_alt_iff,
      M_minThresholdTask, correct_minThresholdTask, Set.mem_ofPred_eq]
    have h_ex : ∃ c, Function.update μ a x c < γ := ⟨a, by simpa using hx⟩
    exact ⟨⟨Or.inl h_ex, fun h ↦ Bool.false_ne_true (h.2 h_ex)⟩,
      (Function.forall_update_iff μ fun c y ↦ y ∈ (ρ c).expFamilyMeans (T c)).2
        ⟨hxm, fun c _ ↦ hμ c⟩⟩
  · -- Lower bound: some arm `a` of an alternative has mean below `γ`.
    rw [IdentTask.altCost_def]
    refine le_iInf₂ fun μ' hμ' ↦ ?_
    simp only [IdentTask.alt_restrict, Set.mem_inter_iff, IdentTask.mem_alt_iff,
      M_minThresholdTask, correct_minThresholdTask, Set.mem_ofPred_eq] at hμ'
    obtain ⟨⟨-, h_corr⟩, hμ'⟩ := hμ'
    obtain ⟨a, ha⟩ : ∃ a, μ' a < γ := by
      by_contra h
      exact h_corr ⟨fun h' ↦ absurd h' Bool.false_ne_true, fun h' ↦ absurd h' h⟩
    exact (iInf_le _ a).trans (ofReal_mul_expFamilyDiv_le_cost hT (by simp) hν hw hμ' a (hγ a)
      (Set.mem_uIcc.2 (Or.inr ⟨ha.le, hμγ a⟩)))

/-- **The game value of the answer `false` in minimum threshold** [DK19, Lemma 37;
KKG18, Lemma 1]. Under the assumptions of `altCost_minThresholdTask_restrict_false`, if all the
means of `μ` are above `γ`, then `D(μ, ¬false) = (∑ a, d_a(μ a, γ)⁻¹)⁻¹`. -/
theorem answerValue_minThresholdTask_restrict_false [Nonempty α]
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hμγ : ∀ a, γ < μ a) :
    ((minThresholdTask ν γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).answerValue
        μ false =
      ENNReal.ofReal (∑ a, ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹)⁻¹ :=
  answerValue_eq_of_altCost_eq_iInf (fun a ↦ expFamilyDiv_pos (hμ a) (hγ a) (hμγ a).ne')
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
    ((minThresholdTask ν γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).optAlloc
        μ false =
      {fun a ↦ ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹ /
        ∑ b, ((ρ b).expFamilyDiv (T b) (μ b) γ)⁻¹} :=
  optAlloc_eq_of_altCost_eq_iInf (fun a ↦ expFamilyDiv_pos (hμ a) (hγ a) (hμγ a).ne')
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
    ((minThresholdTask ν γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).charTime μ =
      ENNReal.ofReal (∑ a, ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹) := by
  classical
  have hc (a : α) : 0 < (ρ a).expFamilyDiv (T a) (μ a) γ :=
    expFamilyDiv_pos (hμ a) (hγ a) (hμγ a).ne'
  have hpos : 0 < ∑ a, ((ρ a).expFamilyDiv (T a) (μ a) γ)⁻¹ :=
    Finset.sum_pos (fun a _ ↦ inv_pos.2 (hc a)) Finset.univ_nonempty
  have h_corr : ((minThresholdTask ν γ).restrict
      {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).correct μ = {false} := by
    rw [IdentTask.correct_restrict, correct_minThresholdTask_eq_singleton,
      decide_eq_false (not_exists.2 fun a ha ↦ lt_asymm ha (hμγ a))]
  rw [IdentTask.charTime_eq_inv_answerValue _ h_corr,
    answerValue_minThresholdTask_restrict_false ν hT hγ hμ hν hμγ, ENNReal.ofReal_inv_of_pos hpos,
    inv_inv]

/-- **The cost of the alternatives to `true` in minimum threshold** [DK19, Lemma 38;
KKG18, Lemma 1]. Under the assumptions of `altCost_thresholdingTask_restrict` on the arm laws, on
the vectors of means of the families, for every nonnegative allocation `w`,
`D(μ, w, ¬true) = ∑ a, w a d_a(μ a, max (μ a) γ)`: the alternatives have all their means above `γ`,
and the cheapest of them raise every mean below `γ` to `γ`. -/
theorem altCost_minThresholdTask_restrict_true (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hw : 0 ≤ w) :
    ((minThresholdTask ν γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).altCost
        μ w true =
      ∑ a, ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) (max (μ a) γ)) := by
  have hmax (c : α) {x : ℝ} (hx : x ∈ (ρ c).expFamilyMeans (T c)) :
      max (μ c) x ∈ (ρ c).expFamilyMeans (T c) := by
    rcases max_choice (μ c) x with h | h <;> rw [h]
    exacts [hμ c, hx]
  have hνt : ((minThresholdTask ν γ).restrict
      {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).ν = ν := by
    simp
  refine le_antisymm ?_ ?_
  · -- Upper bound: raise every mean below `x > γ` to `x`, and let `x` decrease to `γ`.
    have h_tendsto : Tendsto
        (fun x ↦ ∑ c, ENNReal.ofReal (w c * (ρ c).expFamilyDiv (T c) (μ c) (max (μ c) x)))
        (𝓝[>] γ)
        (𝓝 (∑ c, ENNReal.ofReal (w c * (ρ c).expFamilyDiv (T c) (μ c) (max (μ c) γ)))) := by
      refine tendsto_finsetSum _ fun c _ ↦ ?_
      have hd := (hasDerivAt_expFamilyDiv_right (hT c) (μ c) (hmax c (hγ c))).continuousAt
      exact (ENNReal.continuous_ofReal.continuousAt.comp (continuousAt_const.mul
        (hd.comp (continuous_const.max continuous_id).continuousAt))).tendsto.mono_left
        nhdsWithin_le_nhds
    refine ge_of_tendsto h_tendsto ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
      (eventually_all.2 fun c ↦ expFamilyMeans_mem_nhds (hT c) (hγ c))] with x (hx : γ < x) hxm
    have hS (c : α) : max (μ c) x ∈ (ρ c).expFamilyMeans (T c) := hmax c (hxm c)
    have hgt (c : α) : γ < max (μ c) x := hx.trans_le (le_max_right _ _)
    rw [← cost_eq_sum hνt hν hw hS]
    refine IdentTask.altCost_le_cost _ ?_ w
    simp only [IdentTask.alt_restrict, Set.mem_inter_iff, IdentTask.mem_alt_iff,
      M_minThresholdTask, correct_minThresholdTask, Set.mem_ofPred_eq]
    refine ⟨⟨Or.inr hgt, fun h ↦ ?_⟩, hS⟩
    obtain ⟨c, hc⟩ := h.1 trivial
    exact (hgt c).not_gt hc
  · -- Lower bound: an alternative has all its means above `γ`.
    rw [IdentTask.altCost_def]
    refine le_iInf₂ fun μ' hμ' ↦ ?_
    simp only [IdentTask.alt_restrict, Set.mem_inter_iff, IdentTask.mem_alt_iff,
      M_minThresholdTask, correct_minThresholdTask, Set.mem_ofPred_eq] at hμ'
    obtain ⟨⟨-, h_corr⟩, hμ'⟩ := hμ'
    have hge (c : α) : γ ≤ μ' c := not_lt.1 fun hc ↦ h_corr ⟨fun _ ↦ ⟨c, hc⟩, fun _ ↦ trivial⟩
    rw [cost_eq_sum hνt hν hw hμ']
    refine Finset.sum_le_sum fun c _ ↦ ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (expFamilyDiv_le_expFamilyDiv_of_mem_uIcc (hT c) (hmax c (hγ c)) (hμ' c) ?_) (hw c))
    rcases le_total (μ c) γ with h | h
    · rw [max_eq_right h]
      exact Set.mem_uIcc.2 (Or.inl ⟨h, hge c⟩)
    · rw [max_eq_left h]
      exact Set.left_mem_uIcc

/-- **The game value of the answer `true` in minimum threshold** [DK19, Lemma 38;
KKG18, Lemma 1]. Under the assumptions of `altCost_minThresholdTask_restrict_true`,
`D(μ, ¬true) = max_a d_a(μ a, max (μ a) γ)`, attained by sampling only an arm maximizing
`d_a(μ a, max (μ a) γ)`. -/
theorem answerValue_minThresholdTask_restrict_true (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c))) :
    ((minThresholdTask ν γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).answerValue
        μ true =
      ⨆ a, ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (max (μ a) γ)) := by
  rw [IdentTask.answerValue_def, ← iSup_simplex_sum_ofReal_mul]
  exact iSup_congr fun w ↦ iSup_congr fun hw ↦
    altCost_minThresholdTask_restrict_true ν hT hγ hμ hν (mem_simplex_iff.1 hw).1

/-- **The characteristic time of minimum threshold when some mean is below the threshold**
[DK19, Lemma 38; KKG18, Lemma 1]. Under the assumptions of
`altCost_minThresholdTask_restrict_true`, if some mean of `μ` is below `γ`, then
`T*(μ) = (max_a d_a(μ a, max (μ a) γ))⁻¹`. -/
theorem charTime_minThresholdTask_restrict_true (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (h : ∃ a, μ a < γ) :
    ((minThresholdTask ν γ).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).charTime μ =
      (⨆ a, ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (max (μ a) γ)))⁻¹ := by
  classical
  have h_corr : ((minThresholdTask ν γ).restrict
      {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).correct μ = {true} := by
    rw [IdentTask.correct_restrict, correct_minThresholdTask_eq_singleton, decide_eq_true h]
  rw [IdentTask.charTime_eq_inv_answerValue _ h_corr,
    answerValue_minThresholdTask_restrict_true ν hT hγ hμ hν]

/-! #### Gaussian arms -/

variable [MeasurableSingletonClass α] {σ2 : ℝ≥0}

omit [Fintype α] in
/-- For Gaussian arms with a common variance `σ2 ≠ 0`, every vector of means is a vector of means
of the exponential family of `𝒩(0, σ2)`: minimum threshold restricted to them is minimum
threshold. -/
private lemma restrict_minThresholdTask_gaussianBandit [Countable α] (hσ2 : σ2 ≠ 0) :
    (minThresholdTask (Bandits.gaussianBandit · σ2) γ).restrict
        {μ' : α → ℝ | ∀ c, μ' c ∈ (gaussianReal 0 σ2).expFamilyMeans id} =
      minThresholdTask (Bandits.gaussianBandit · σ2) γ := by
  simp [expFamilyMeans_gaussianReal 0 hσ2]

/-- **The characteristic time of Gaussian minimum threshold when all the means are above the
threshold** [DK19, Lemma 37]. For Gaussian arms with a common variance `σ2 ≠ 0` and a vector of
means `μ` with all its means above `γ`, `T*(μ) = ∑ a, 2 σ2 / (μ a - γ)²`. -/
theorem charTime_minThresholdTask_gaussianBandit_false [Nonempty α] (hσ2 : σ2 ≠ 0)
    (hμγ : ∀ a, γ < μ a) :
    (minThresholdTask (Bandits.gaussianBandit · σ2) γ).charTime μ =
      ENNReal.ofReal (∑ a, 2 * σ2 / (μ a - γ) ^ 2) := by
  rw [← restrict_minThresholdTask_gaussianBandit hσ2,
    charTime_minThresholdTask_restrict_false (ρ := fun _ ↦ gaussianReal 0 σ2) (T := fun _ ↦ id) _
      (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2) (fun _ ↦ by simp [hσ2])
      (fun _ ↦ by simp [hσ2])
      (fun μ' _ c ↦ by rw [Bandits.klDiv_gaussianBandit _ _ hσ2, expFamilyDiv_gaussianReal 0 hσ2])
      hμγ]
  simp only [expFamilyDiv_gaussianReal 0 hσ2, inv_div]

/-- **The characteristic time of Gaussian minimum threshold when some mean is below the
threshold** [DK19, Lemma 38]. For Gaussian arms with a common variance `σ2 ≠ 0` and a vector of
means `μ` whose smallest mean `μ a₀` is below `γ`, `T*(μ) = 2 σ2 / (μ a₀ - γ)²`. -/
theorem charTime_minThresholdTask_gaussianBandit_true (hσ2 : σ2 ≠ 0) {a₀ : α}
    (ha₀ : ∀ a, μ a₀ ≤ μ a) (hγ : μ a₀ < γ) :
    (minThresholdTask (Bandits.gaussianBandit · σ2) γ).charTime μ =
      ENNReal.ofReal (2 * σ2 / (μ a₀ - γ) ^ 2) := by
  have hσ2' : 0 < (σ2 : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hσ2)
  rw [← restrict_minThresholdTask_gaussianBandit hσ2,
    charTime_minThresholdTask_restrict_true (ρ := fun _ ↦ gaussianReal 0 σ2) (T := fun _ ↦ id) _
      (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2) (fun _ ↦ by simp [hσ2])
      (fun _ ↦ by simp [hσ2])
      (fun μ' _ c ↦ by rw [Bandits.klDiv_gaussianBandit _ _ hσ2, expFamilyDiv_gaussianReal 0 hσ2])
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
