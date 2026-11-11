/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.StaticProportions
public import LMLExplore.Identification.Task.Threshold.Basic

/-!
# Static proportions in minimum threshold identification

The minimum threshold task (*positivity* in [D23]) asks whether some arm has a mean below the
threshold `γ`. Let the arm `a` belong to an exponential family `(ρ a, T a)` with divergence `d_a`
in the mean parametrization, let `γ` be a mean of every family, and let the models be the vectors
of means of the families. This file computes the static-proportions difficulty
`H^{sp}(μ) = (sup_{w ∈ Δ_K} inf_{λ ∈ Alt(μ)} ∑ a, w a d_a(λ a, μ a))⁻¹`
(`IdentTask.staticDifficulty`), in which the alternative comes first in the divergence, in closed
form. These are the counterparts, with the divergences reversed, of the characteristic times of
`LMLExplore/Identification/Task/Threshold/Basic.lean`.

* If all the means of `μ` are above `γ` (answer `false`), the alternatives are the vectors with
  some mean below `γ`, and the cost of the alternatives is approached by moving a single arm
  below `γ`, ever closer to `γ`: `inf_{λ ∈ ¬false} ∑ a, w a d_a(λ a, μ a) = min_a w a d_a(γ, μ a)`.
  Hence `H^{sp}(μ) = ∑ a, d_a(γ, μ a)⁻¹`.
* If some mean of `μ` is below `γ` (answer `true`), the alternatives are the vectors with all
  means above `γ`, and the infimum of the costs is reached in the limit where the arms below `γ`
  are moved to `γ`: `inf_{λ ∈ ¬true} ∑ a, w a d_a(λ a, μ a) = ∑ a, w a d_a(max (μ a) γ, μ a)`.
  Hence `H^{sp}(μ) = (max_a d_a(max (μ a) γ, μ a))⁻¹`, and `H^{sp}(μ) ≤ d_j(γ, μ j)⁻¹` for every
  arm `j` with `μ j < γ` [D23, proof of Theorem 6].

These closed forms enter the proof that positivity has maximal difficulty ratio `K` to the
static-proportions difficulty [D23, Theorem 6]: the upper bound `H^{sp}(λ) ≤ d_j(γ, λ j)⁻¹` at the
models with one arm below `γ`, and the finiteness of `H^{sp}(μ)` at the models with all their means
above `γ`.

For Gaussian arms with a common variance `σ2`, the divergences are symmetric, and the
static-proportions difficulty is the characteristic time: `H^{sp}(μ) = ∑ a, 2 σ2 / (μ a - γ)²` if
all the means are above `γ`, and `H^{sp}(μ) = 2 σ2 / (μ a₀ - γ)²` if the smallest mean `μ a₀` is
below `γ`.

## Main statements

* `LMLExplore.Identification.iInf_cost_minThresholdTask_restrict_false`,
  `LMLExplore.Identification.staticDifficulty_minThresholdTask_restrict_false`: if all the means of
  `μ` are above `γ`, the cost of the alternatives is `min_a w a d_a(γ, μ a)` and
  `H^{sp}(μ) = ∑ a, d_a(γ, μ a)⁻¹`.
* `LMLExplore.Identification.iInf_cost_minThresholdTask_restrict_true`,
  `LMLExplore.Identification.staticDifficulty_minThresholdTask_restrict_true`: the cost of the
  alternatives to `true` is `∑ a, w a d_a(max (μ a) γ, μ a)` and, if some mean of `μ` is below `γ`,
  `H^{sp}(μ) = (max_a d_a(max (μ a) γ, μ a))⁻¹`.
* `LMLExplore.Identification.staticDifficulty_minThresholdTask_restrict_le_of_lt`:
  [D23, proof of Theorem 6], `H^{sp}(μ) ≤ d_j(γ, μ j)⁻¹` if `μ j < γ`.
* `LMLExplore.Identification.staticDifficulty_minThresholdTask_gaussianBandit_false`,
  `LMLExplore.Identification.staticDifficulty_minThresholdTask_gaussianBandit_true`: the Gaussian
  closed forms.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
* Adapted from the formalization of [D23] in the project `RemyDegenne/Degenne2023Existence`
  (same author), file `D2023/Theorem6.lean` (`staticDifficulty_minThresholdTask_le`), commit
  `4be4d55b7a280ce4323561650013981c111301e2`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Measure Set

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} [Fintype α]
  {ρ : α → Measure 𝓨} {T : α → 𝓨 → ℝ} {γ : ℝ} {μ w : α → ℝ}
  (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)]

/-- **The cost of the alternatives to `false`, alternative first.** Let the arm laws belong to
exponential families `(ρ a, T a)` with divergences `d_a`, in the sense that
`KL(ν_c(μ'), ν_c(μ)) = d_c(μ' c, μ c)` for all vectors of means `μ'` of the families, and let `γ` be
a mean of every family. If all the means of the vector of means `μ` are at least `γ`, then on the
vectors of means of the families, for every nonnegative allocation `w`,
`inf_{λ ∈ ¬false} ∑ a, w a d_a(λ a, μ a) = min_a w a d_a(γ, μ a)`: this infimum is approached by
moving a single arm below `γ`, ever closer to `γ`. -/
theorem iInf_cost_minThresholdTask_restrict_false (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ' c) (ν μ c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ' c) (μ c)))
    (hμγ : ∀ a, γ ≤ μ a) (hw : 0 ≤ w) :
    ⨅ μ' ∈ ((minThresholdTask ν id γ).restrict
        {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).alt false,
      ((minThresholdTask ν id γ).restrict
        {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).cost w μ' μ =
      ⨅ a, ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) γ (μ a)) := by
  classical
  have hνt : ((minThresholdTask ν id γ).restrict
      {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).ν = ν := by
    simp
  refine le_antisymm (le_iInf fun a ↦ ?_) (le_iInf₂ fun μ' hμ' ↦ ?_)
  · -- Upper bound: move the mean of `a` below `γ`, close to `γ`.
    have h_tendsto : Tendsto (fun x ↦ ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) x (μ a)))
        (𝓝[<] γ) (𝓝 (ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) γ (μ a)))) :=
      (ENNReal.continuous_ofReal.continuousAt.comp (continuousAt_const.mul
        (hasDerivAt_expFamilyDiv_left (hT a) (hγ a) (μ a)).continuousAt)).tendsto.mono_left
        nhdsWithin_le_nhds
    refine ge_of_tendsto h_tendsto ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (expFamilyMeans_mem_nhds (hT a) (hγ a))] with x (hx : x < γ) hxm
    have hμx : ∀ c, Function.update μ a x c ∈ (ρ c).expFamilyMeans (T c) :=
      (Function.forall_update_iff μ fun c y ↦ y ∈ (ρ c).expFamilyMeans (T c)).2
        ⟨hxm, fun c _ ↦ hμ c⟩
    refine (iInf₂_le (Function.update μ a x) ?_).trans_eq ?_
    · rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_minThresholdTask_false_iff]
      exact ⟨⟨a, by simpa using hx⟩, hμx⟩
    · rw [IdentTask.cost_eq_sum_ofReal_mul_expFamilyDiv_left hνt hν hw hμx,
        Finset.sum_eq_single a (fun c _ hc ↦ ?_) (by simp)]
      · simp
      · simp [Function.update_of_ne hc, expFamilyDiv_self]
  · -- Lower bound: some arm `a` of an alternative has its mean below `γ`.
    rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_minThresholdTask_false_iff, id_eq] at hμ'
    obtain ⟨⟨a, ha⟩, hμ'⟩ := hμ'
    rw [IdentTask.cost_eq_sum_ofReal_mul_expFamilyDiv_left hνt hν hw hμ']
    refine (iInf_le _ a).trans (le_trans ?_ (Finset.single_le_sum (f := fun c ↦
      ENNReal.ofReal (w c * (ρ c).expFamilyDiv (T c) (μ' c) (μ c))) (fun _ _ ↦ zero_le)
      (Finset.mem_univ a)))
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (expFamilyDiv_le_expFamilyDiv_left_of_mem_uIcc (hT a) (hμ a) (hγ a) (hμ' a)
        (Set.mem_uIcc.2 (Or.inr ⟨ha.le, hμγ a⟩))) (hw a))

/-- **The static-proportions difficulty of minimum threshold when all the means are above the
threshold.** Under the assumptions of `iInf_cost_minThresholdTask_restrict_false`, if all the means
of `μ` are above `γ`, then `H^{sp}(μ) = ∑ a, d_a(γ, μ a)⁻¹`. -/
theorem staticDifficulty_minThresholdTask_restrict_false [Nonempty α]
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ' c) (ν μ c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ' c) (μ c)))
    (hμγ : ∀ a, γ < μ a) :
    ((minThresholdTask ν id γ).restrict
        {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).staticDifficulty μ =
      ENNReal.ofReal (∑ a, ((ρ a).expFamilyDiv (T a) γ (μ a))⁻¹) := by
  classical
  have hc (a : α) : 0 < (ρ a).expFamilyDiv (T a) γ (μ a) :=
    expFamilyDiv_pos (hγ a) (hμ a) (hμγ a).ne
  have h_corr : ((minThresholdTask ν id γ).restrict
      {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).correct μ = {false} := by
    rw [IdentTask.correct_restrict, correct_minThresholdTask_eq_singleton, id_eq,
      decide_eq_false (not_exists.2 fun a ha ↦ lt_asymm ha (hμγ a))]
  rw [IdentTask.staticDifficulty_def, IdentTask.alternatives_eq_alt (h := h_corr),
    biSup_congr fun w hw ↦ iInf_cost_minThresholdTask_restrict_false ν hT hγ hμ hν
      (fun a ↦ (hμγ a).le) (mem_simplex_iff.1 hw).1,
    iSup_simplex_iInf_ofReal_mul hc, ENNReal.ofReal_inv_of_pos (sum_inv_pos hc), inv_inv]

/-- **The cost of the alternatives to `true`, alternative first.** Under the assumptions of
`iInf_cost_minThresholdTask_restrict_false` on the arm laws, on the vectors of means of the
families, for every nonnegative allocation `w`,
`inf_{λ ∈ ¬true} ∑ a, w a d_a(λ a, μ a) = ∑ a, w a d_a(max (μ a) γ, μ a)`: the alternatives have
all their means above `γ`, and the cost is the infimum over the alternatives that raise every mean
at most `γ` to a level `x > γ`, as `x` decreases to `γ`. -/
theorem iInf_cost_minThresholdTask_restrict_true (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ' c) (ν μ c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ' c) (μ c)))
    (hw : 0 ≤ w) :
    ⨅ μ' ∈ ((minThresholdTask ν id γ).restrict
        {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).alt true,
      ((minThresholdTask ν id γ).restrict
        {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).cost w μ' μ =
      ∑ a, ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (max (μ a) γ) (μ a)) := by
  have hmax (c : α) {x : ℝ} (hx : x ∈ (ρ c).expFamilyMeans (T c)) :
      max (μ c) x ∈ (ρ c).expFamilyMeans (T c) := by
    rcases max_choice (μ c) x with h | h <;> rw [h]
    exacts [hμ c, hx]
  have hνt : ((minThresholdTask ν id γ).restrict
      {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).ν = ν := by
    simp
  refine le_antisymm ?_ (le_iInf₂ fun μ' hμ' ↦ ?_)
  · -- Upper bound: raise every mean below `x > γ` to `x`, and let `x` decrease to `γ`.
    have h_tendsto : Tendsto
        (fun x ↦ ∑ c, ENNReal.ofReal (w c * (ρ c).expFamilyDiv (T c) (max (μ c) x) (μ c)))
        (𝓝[>] γ)
        (𝓝 (∑ c, ENNReal.ofReal (w c * (ρ c).expFamilyDiv (T c) (max (μ c) γ) (μ c)))) := by
      refine (tendsto_finsetSum _ fun c _ ↦ ?_).mono_left nhdsWithin_le_nhds
      exact (ENNReal.continuous_ofReal.continuousAt.comp (continuousAt_const.mul
        ((hasDerivAt_expFamilyDiv_left (hT c) (hmax c (hγ c)) (μ c)).continuousAt.comp
          (continuous_const.max continuous_id).continuousAt))).tendsto
    refine ge_of_tendsto h_tendsto ?_
    have h_mem : ∀ᶠ x in 𝓝[>] γ, ∀ c, x ∈ (ρ c).expFamilyMeans (T c) :=
      nhdsWithin_le_nhds (eventually_all.2 fun c ↦ expFamilyMeans_mem_nhds (hT c) (hγ c))
    filter_upwards [self_mem_nhdsWithin, h_mem] with x (hx : γ < x) hxm
    have hμx : ∀ c, max (μ c) x ∈ (ρ c).expFamilyMeans (T c) := fun c ↦ hmax c (hxm c)
    refine (iInf₂_le (fun c ↦ max (μ c) x) ?_).trans_eq
      (IdentTask.cost_eq_sum_ofReal_mul_expFamilyDiv_left hνt hν hw hμx)
    rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_minThresholdTask_true_iff]
    exact ⟨fun c ↦ hx.trans_le (le_max_right _ _), hμx⟩
  · -- Lower bound: an alternative has all its means above `γ`.
    rw [IdentTask.alt_restrict, Set.mem_inter_iff, mem_alt_minThresholdTask_true_iff, id_eq] at hμ'
    obtain ⟨hgt, hμ'⟩ := hμ'
    rw [IdentTask.cost_eq_sum_ofReal_mul_expFamilyDiv_left hνt hν hw hμ']
    refine Finset.sum_le_sum fun c _ ↦ ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (expFamilyDiv_le_expFamilyDiv_left_of_mem_uIcc (hT c) (hμ c) (hmax c (hγ c)) (hμ' c) ?_)
      (hw c))
    rcases le_total (μ c) γ with h | h
    · rw [max_eq_right h]
      exact Set.mem_uIcc.2 (Or.inl ⟨h, (hgt c).le⟩)
    · rw [max_eq_left h]
      exact Set.left_mem_uIcc

/-- **The static-proportions difficulty of minimum threshold when some mean is below the
threshold.** Under the assumptions of `iInf_cost_minThresholdTask_restrict_true`, if some mean of
`μ` is below `γ`, then `H^{sp}(μ) = (max_a d_a(max (μ a) γ, μ a))⁻¹`. -/
theorem staticDifficulty_minThresholdTask_restrict_true (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ' c) (ν μ c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ' c) (μ c)))
    (h : ∃ a, μ a < γ) :
    ((minThresholdTask ν id γ).restrict
        {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).staticDifficulty μ =
      (⨆ a, ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (max (μ a) γ) (μ a)))⁻¹ := by
  classical
  have hmax (a : α) : max (μ a) γ ∈ (ρ a).expFamilyMeans (T a) := by
    rcases max_choice (μ a) γ with h | h <;> rw [h]
    exacts [hμ a, hγ a]
  have h_corr : ((minThresholdTask ν id γ).restrict
      {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).correct μ = {true} := by
    rw [IdentTask.correct_restrict, correct_minThresholdTask_eq_singleton, id_eq, decide_eq_true h]
  rw [IdentTask.staticDifficulty_def, IdentTask.alternatives_eq_alt (h := h_corr),
    ← iSup_simplex_ofReal_dotProduct]
  congr 1
  refine biSup_congr fun w hw ↦ ?_
  rw [iInf_cost_minThresholdTask_restrict_true ν hT hγ hμ hν (mem_simplex_iff.1 hw).1, dotProduct,
    ENNReal.ofReal_sum_of_nonneg fun a _ ↦
      mul_nonneg ((mem_simplex_iff.1 hw).1 a) (expFamilyDiv_nonneg (hmax a) (hμ a))]

/-- **An arm below the threshold bounds the static-proportions difficulty**
[D23, proof of Theorem 6]. Under the assumptions of `iInf_cost_minThresholdTask_restrict_true`,
every arm `j` with `μ j < γ` gives `H^{sp}(μ) ≤ d_j(γ, μ j)⁻¹`: sampling only `j`, the alternatives
must raise `μ j` above `γ`. -/
theorem staticDifficulty_minThresholdTask_restrict_le_of_lt
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : ∀ a, γ ∈ (ρ a).expFamilyMeans (T a)) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ' c) (ν μ c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ' c) (μ c)))
    {j : α} (hj : μ j < γ) :
    ((minThresholdTask ν id γ).restrict
        {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).staticDifficulty μ ≤
      (ENNReal.ofReal ((ρ j).expFamilyDiv (T j) γ (μ j)))⁻¹ := by
  rw [staticDifficulty_minThresholdTask_restrict_true ν hT hγ hμ hν ⟨j, hj⟩, ENNReal.inv_le_inv]
  exact le_iSup_of_le j (by rw [max_eq_right hj.le])

/-! ### Gaussian arms -/

variable [MeasurableSingletonClass α] {σ2 : ℝ≥0}

/-- **The static-proportions difficulty of Gaussian minimum threshold when all the means are above
the threshold.** For Gaussian arms with a common variance `σ2 ≠ 0` and a vector of means `μ` with
all its means above `γ`, `H^{sp}(μ) = ∑ a, 2 σ2 / (μ a - γ)²`, the characteristic time
(`charTime_minThresholdTask_gaussianBandit_false`). -/
theorem staticDifficulty_minThresholdTask_gaussianBandit_false [Nonempty α] (hσ2 : σ2 ≠ 0)
    (hμγ : ∀ a, γ < μ a) :
    (minThresholdTask (Bandits.gaussianBandit · σ2) id γ).staticDifficulty μ =
      ENNReal.ofReal (∑ a, 2 * σ2 / (μ a - γ) ^ 2) := by
  rw [← (minThresholdTask (Bandits.gaussianBandit · σ2) id γ).restrict_univ,
    ← setOf_forall_mem_expFamilyMeans_gaussianReal 0 hσ2,
    staticDifficulty_minThresholdTask_restrict_false (ρ := fun _ ↦ gaussianReal 0 σ2)
      (T := fun _ ↦ id) _
      (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
      (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (fun μ' _ ↦ Bandits.klDiv_gaussianBandit_eq_ofReal_expFamilyDiv hσ2 μ' μ)
      hμγ]
  simp only [expFamilyDiv_gaussianReal 0 hσ2, inv_div, sub_sq_comm γ]

/-- **The static-proportions difficulty of Gaussian minimum threshold when some mean is below the
threshold.** For Gaussian arms with a common variance `σ2 ≠ 0` and a vector of means `μ` whose
smallest mean `μ a₀` is below `γ`, `H^{sp}(μ) = 2 σ2 / (μ a₀ - γ)²`, the characteristic time
(`charTime_minThresholdTask_gaussianBandit_true`). -/
theorem staticDifficulty_minThresholdTask_gaussianBandit_true (hσ2 : σ2 ≠ 0) {a₀ : α}
    (ha₀ : ∀ a, μ a₀ ≤ μ a) (hγ : μ a₀ < γ) :
    (minThresholdTask (Bandits.gaussianBandit · σ2) id γ).staticDifficulty μ =
      ENNReal.ofReal (2 * σ2 / (μ a₀ - γ) ^ 2) := by
  rw [← (minThresholdTask (Bandits.gaussianBandit · σ2) id γ).restrict_univ,
    ← setOf_forall_mem_expFamilyMeans_gaussianReal 0 hσ2,
    staticDifficulty_minThresholdTask_restrict_true (ρ := fun _ ↦ gaussianReal 0 σ2)
      (T := fun _ ↦ id) _
      (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
      (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (fun μ' _ ↦ Bandits.klDiv_gaussianBandit_eq_ofReal_expFamilyDiv hσ2 μ' μ)
      ⟨a₀, hγ⟩]
  simp only [expFamilyDiv_gaussianReal 0 hσ2]
  -- The largest divergence from the alternatives is that of the arm with the smallest mean.
  have h_sup : ⨆ a, ENNReal.ofReal ((max (μ a) γ - μ a) ^ 2 / (2 * σ2)) =
      ENNReal.ofReal ((μ a₀ - γ) ^ 2 / (2 * σ2)) := by
    refine le_antisymm (iSup_le fun a ↦ ENNReal.ofReal_le_ofReal ?_)
      (le_iSup_of_le a₀ (by rw [max_eq_right hγ.le, sub_sq_comm]))
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rcases le_total (μ a) γ with h | h
    · rw [max_eq_right h]
      nlinarith [ha₀ a]
    · rw [max_eq_left h, sub_self]
      simpa using sq_nonneg (μ a₀ - γ)
  have hpos : 0 < (μ a₀ - γ) ^ 2 / (2 * σ2) := by
    have : 0 < (μ a₀ - γ) ^ 2 := by nlinarith [mul_pos (sub_pos.2 hγ) (sub_pos.2 hγ)]
    have hσ2' : 0 < (σ2 : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hσ2)
    positivity
  rw [h_sup, ← ENNReal.ofReal_inv_of_pos hpos, inv_div]

end LMLExplore.Identification
