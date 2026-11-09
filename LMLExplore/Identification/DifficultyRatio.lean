/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.ErrorLowerBound
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli

/-!
# Difficulty ratios of fixed-budget identification and their lower bounds

A fixed-budget algorithm family `𝒜` (`IsFixedBudgetFamily`) has, for every budget `T`, an
algorithm `𝒜 T` that stops after `T` rounds. Its probability of error `p_{θ,T}(𝒜)` on the model
`θ` of an identification task decreases exponentially in `T` for good families, and the speed of
this decrease is measured by the complexity `h_{θ,T}(𝒜) = T / log (1 / p_{θ,T}(𝒜))`, so that
`p_{θ,T}(𝒜) = exp (-T / h_{θ,T}(𝒜))`.
Against a *difficulty function* `H : Θ → ℝ≥0∞`, the *difficulty ratio*
`R_{H,T}(𝒜, θ) = h_{θ,T}(𝒜) / H(θ)` compares the family to the baseline `H`: it is at most `1`
when the probability of error is at most `exp (-T / H(θ))`. Its `limsup` in `T` is the asymptotic
ratio `R_{H,∞}(𝒜, θ)`, and its supremum over the admissible models the maximal ratio of `𝒜`.
These quantities are `ℝ≥0∞`-valued: `h = 0` when `p = 0` and `h = ∞` when `p = 1` and `T > 0`.

The lower bounds of [D23] say that no family has a small difficulty ratio everywhere. If `μ` and
`λ` have no common correct answer, an algorithm that is correct on `μ` with high probability and
collects little information against `λ` errs often on `λ`. With the proportions of pulls `w`
of `𝒜 T` at `μ` and the transportation cost `cost(w, μ, λ) = ∑ a, w a KL(ν_a(μ), ν_a(λ))`,
Theorem 2 of [D23] reads
`R_{H,T}(𝒜, λ)⁻¹ (1 - p_{μ,T}(𝒜)) ≤ H(λ) cost(w, μ, λ) + log 2 / √T`.
Asymptotically, for a set `D` of alternatives to `μ`, every family whose probability of error at
`μ` tends to `0` satisfies
`(sup_{λ ∈ D} R_{H,∞}(𝒜, λ))⁻¹ ≤ max_{w ∈ Δ_K} inf_{λ ∈ D} H(λ) cost(w, μ, λ)` (Theorem 3), and
with `liminf_T sup_{λ ∈ D} R_{H,T}(𝒜, λ)` in place of `sup_{λ ∈ D} R_{H,∞}(𝒜, λ)` when `H` is
bounded on `D` (Theorem 13). When the alternatives `λ⁽ʲ⁾` differ from `μ` on the arm `j` only, the
right-hand side is at most `(∑_j 1 / (H(λ⁽ʲ⁾) KL(ν_j(μ), ν_j(λ⁽ʲ⁾))))⁻¹` (Corollary 4). These bounds
are the starting point of the results of [D23] on the existence of a complexity in fixed-budget
identification.

## Main definitions

In the namespace `LMLExplore.Identification.IdentTask`:

* `errorProb task 𝒜 θ T`: the probability of error `p_{θ,T}(𝒜)`.
* `errorComplexity task 𝒜 θ T`: the complexity `h_{θ,T}(𝒜) = T / log (1 / p_{θ,T}(𝒜))`.
* `difficultyRatio task H 𝒜 θ T`, `asymptoticRatio task H 𝒜 θ`, `maxRatio task H 𝒜`: the
  difficulty ratios `R_{H,T}(𝒜, θ)`, `R_{H,∞}(𝒜, θ)` and the maximal difficulty ratio
  `sup_{θ ∈ M} R_{H,∞}(𝒜, θ)`.
* `IsConsistent task 𝒜`: `p_{θ,T}(𝒜) → 0` at every admissible model `θ`.

## Main statements

* `IdentTask.inv_difficultyRatio`: `R_{H,T}(𝒜, θ)⁻¹ = H(θ) log (1 / p_{θ,T}(𝒜)) / T`.
* `IdentTask.one_sub_errorProb_mul_neg_log_errorProb_le`: the change of measure
  `(1 - p_{μ,T}(𝒜)) log (1 / p_{λ,T}(𝒜)) ≤ ∑ a, E_μ[N_{T,a}] KL(ν_a(μ), ν_a(λ)) + log 2` for two
  models without a common correct answer.
* `IdentTask.inv_difficultyRatio_mul_le`, `IdentTask.inv_difficultyRatio_mul_le_cost`:
  [D23, Theorem 2].
* `IdentTask.eventually_mul_inv_difficultyRatio_le`: Theorem 2 for all large budgets at once, for
  a family whose probability of error at `μ` tends to `0`.
* `IdentTask.inv_iSup_asymptoticRatio_le`, `IdentTask.inv_maxRatio_le`: [D23, Theorem 3].
* `IdentTask.sum_inv_le_iSup_asymptoticRatio`: [D23, Corollary 4].
* `IdentTask.inv_liminf_iSup_difficultyRatio_le`: [D23, Theorem 13].
* `IdentTask.inv_liminf_iSup_difficultyRatio_le_liminf`: [D23, Corollary 14].

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
* Adapted from the formalization of [D23] in the project `RemyDegenne/Degenne2023Existence`
  (same author).
-/

public section

open MeasureTheory Filter Topology InformationTheory Learning

open scoped ENNReal

namespace LMLExplore.Identification.IdentTask

variable {α Θ ℐ 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  {mℐ : MeasurableSpace ℐ}

/-! ### Definitions -/

section Definitions

variable (task : IdentTask α Θ ℐ 𝓨)

/-- The probability of error `p_{θ,T}(𝒜)` of the family `𝒜` with budget `T` on the model `θ`: the
probability that the output of `𝒜 T` in the bandit of `θ` is not a correct answer of `θ`. -/
noncomputable def errorProb (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) (θ : Θ) (T : ℕ) : ℝ≥0∞ :=
  (𝒜 T).outputMeasure (Environment.bandit (task.ν θ)) (task.correct θ)ᶜ

/-- The error complexity `h_{θ,T}(𝒜) = T / log (1 / p_{θ,T}(𝒜))` of the family `𝒜` with budget
`T` on the model `θ`, so that `p_{θ,T}(𝒜) = exp (-T / h_{θ,T}(𝒜))`. It is `0` if
`p_{θ,T}(𝒜) = 0` and `∞` if `p_{θ,T}(𝒜) = 1` and `T > 0`. -/
noncomputable def errorComplexity (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) (θ : Θ) (T : ℕ) : ℝ≥0∞ :=
  T / (-ENNReal.log (task.errorProb 𝒜 θ T)).toENNReal

/-- The difficulty ratio `R_{H,T}(𝒜, θ) = h_{θ,T}(𝒜) / H(θ)` of the family `𝒜` with budget `T` to
the difficulty function `H` at the model `θ`. It is larger than `1` if the probability of error is
larger than `exp (-T / H(θ))`. -/
noncomputable def difficultyRatio (H : Θ → ℝ≥0∞) (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) (θ : Θ) (T : ℕ) :
    ℝ≥0∞ :=
  task.errorComplexity 𝒜 θ T / H θ

/-- The asymptotic difficulty ratio `R_{H,∞}(𝒜, θ) = limsup_{T → ∞} R_{H,T}(𝒜, θ)`. -/
noncomputable def asymptoticRatio (H : Θ → ℝ≥0∞) (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) (θ : Θ) :
    ℝ≥0∞ :=
  limsup (task.difficultyRatio H 𝒜 θ) atTop

/-- The maximal difficulty ratio `sup_{θ ∈ M} R_{H,∞}(𝒜, θ)` of the family `𝒜` to the difficulty
function `H`, over the admissible models. -/
noncomputable def maxRatio (H : Θ → ℝ≥0∞) (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) : ℝ≥0∞ :=
  ⨆ θ ∈ task.M, task.asymptoticRatio H 𝒜 θ

/-- The family `𝒜` is *consistent*: its probability of error tends to `0` at every admissible
model. -/
def IsConsistent (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) : Prop :=
  ∀ θ ∈ task.M, Tendsto (task.errorProb 𝒜 θ) atTop (𝓝 0)

variable {task} {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} {H : Θ → ℝ≥0∞} {θ : Θ} {T : ℕ}

lemma errorProb_def (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) (θ : Θ) (T : ℕ) :
    task.errorProb 𝒜 θ T =
      (𝒜 T).outputMeasure (Environment.bandit (task.ν θ)) (task.correct θ)ᶜ := (rfl)

lemma errorComplexity_def (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) (θ : Θ) (T : ℕ) :
    task.errorComplexity 𝒜 θ T = T / (-ENNReal.log (task.errorProb 𝒜 θ T)).toENNReal := (rfl)

lemma difficultyRatio_def (H : Θ → ℝ≥0∞) (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) (θ : Θ) (T : ℕ) :
    task.difficultyRatio H 𝒜 θ T = task.errorComplexity 𝒜 θ T / H θ := (rfl)

lemma asymptoticRatio_def (H : Θ → ℝ≥0∞) (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) (θ : Θ) :
    task.asymptoticRatio H 𝒜 θ = limsup (task.difficultyRatio H 𝒜 θ) atTop := (rfl)

lemma maxRatio_def (H : Θ → ℝ≥0∞) (𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ) :
    task.maxRatio H 𝒜 = ⨆ θ ∈ task.M, task.asymptoticRatio H 𝒜 θ := (rfl)

lemma isConsistent_iff :
    task.IsConsistent 𝒜 ↔ ∀ θ ∈ task.M, Tendsto (task.errorProb 𝒜 θ) atTop (𝓝 0) := Iff.rfl

/-- For a difficulty `H θ` positive and finite and a budget `T ≠ 0`, the inverse of the difficulty
ratio is `R_{H,T}(𝒜, θ)⁻¹ = H(θ) log (1 / p_{θ,T}(𝒜)) / T`. -/
lemma inv_difficultyRatio (hH₀ : H θ ≠ 0) (hH : H θ ≠ ∞) (hT : T ≠ 0) :
    (task.difficultyRatio H 𝒜 θ T)⁻¹ =
      H θ * ((-ENNReal.log (task.errorProb 𝒜 θ T)).toENNReal / T) := by
  rw [difficultyRatio_def, errorComplexity_def, ENNReal.inv_div (Or.inl hH) (Or.inl hH₀),
    ENNReal.div_eq_inv_mul, ENNReal.inv_div (Or.inr (ENNReal.natCast_ne_top T))
      (Or.inr (by exact_mod_cast hT)), mul_comm]

/-- The asymptotic difficulty ratios at the models of `D` are at most the maximal difficulty ratio
when `D` consists of admissible models. -/
lemma iSup_asymptoticRatio_le_maxRatio {D : Set Θ} (hD : D ⊆ task.M) :
    ⨆ θ ∈ D, task.asymptoticRatio H 𝒜 θ ≤ task.maxRatio H 𝒜 :=
  iSup₂_mono' fun θ hθ ↦ ⟨θ, hD hθ, le_rfl⟩

end Definitions

/-! ### The non-asymptotic lower bound -/

variable [Fintype α] [DecidableEq α] [MeasurableSingletonClass α]
  [MeasurableSpace.CountablyGenerated 𝓨]

/-- **Change of measure for the probabilities of error of a fixed-budget algorithm**
[D23, proof of Theorem 2]. Let `𝒜 T` stop after `T` rounds, and let `μ`, `λ` be two models
without a common correct answer. Then
`(1 - p_{μ,T}(𝒜)) log (1 / p_{λ,T}(𝒜)) ≤ ∑ a, E_μ[N_{T,a}] KL(ν_a(μ), ν_a(λ)) + log 2`, where
`N_{T,a}` is the number of pulls of the arm `a` in the first `T` rounds. -/
theorem one_sub_errorProb_mul_neg_log_errorProb_le (task : IdentTask α Θ ℐ 𝓨)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} {T : ℕ} (h𝒜 : IsFixedBudget (𝒜 T) T) {μ μ' : Θ}
    (hμμ' : Disjoint (task.correct μ) (task.correct μ')) :
    (1 - task.errorProb 𝒜 μ T) * (-ENNReal.log (task.errorProb 𝒜 μ' T)).toENNReal ≤
      ∑ a, (∫⁻ ω, (pullCount IT.action a T ω : ℝ≥0∞)
          ∂(trajMeasure (𝒜 T).alg (Environment.bandit (task.ν μ)))) *
          klDiv (task.ν μ a) (task.ν μ' a) + ENNReal.ofReal (Real.log 2) := by
  set P := (𝒜 T).outputMeasure (Environment.bandit (task.ν μ))
  set P' := (𝒜 T).outputMeasure (Environment.bandit (task.ν μ'))
  -- The event `E` that the output is a correct answer of `μ`, up to a `P`-null set.
  set E := (toMeasurable P (task.correct μ)ᶜ)ᶜ with hE_def
  have hE : MeasurableSet E := (measurableSet_toMeasurable _ _).compl
  have hPE : P E = 1 - task.errorProb 𝒜 μ T := by
    rw [hE_def, prob_compl_eq_one_sub (measurableSet_toMeasurable _ _), measure_toMeasurable,
      errorProb_def]
  have hP'E : P' E ≤ task.errorProb 𝒜 μ' T := by
    rw [errorProb_def]
    refine measure_mono ?_
    calc E ⊆ task.correct μ := by
          rw [hE_def, Set.compl_subset_comm]
          exact subset_toMeasurable _ _
      _ ⊆ (task.correct μ')ᶜ := hμμ'.subset_compl_right
  -- The data processing inequality for `E`, and `kl(p, q) ≥ p log (1 / q) - log 2`.
  have hkl := (klBer_measureReal_le_klDiv hE).trans
    (h𝒜.klDiv_outputMeasure_le (task.ν μ) (task.ν μ'))
  have hlow := ofReal_mul_neg_log_le_klBer_add_log_two (p := P.real E) (q := P'.real E)
    ⟨measureReal_nonneg, measureReal_le_one⟩ ⟨measureReal_nonneg, measureReal_le_one⟩
  rw [ofReal_measureReal, ofReal_measureReal, hPE] at hlow
  calc (1 - task.errorProb 𝒜 μ T) * (-ENNReal.log (task.errorProb 𝒜 μ' T)).toENNReal
      ≤ (1 - task.errorProb 𝒜 μ T) * (-ENNReal.log (P' E)).toENNReal := by
        gcongr
        exact EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (ENNReal.log_monotone hP'E))
    _ ≤ _ := hlow.trans (add_le_add hkl le_rfl)

/-- **Non-asymptotic lower bound on the difficulty ratio** [D23, Theorem 2]. Let `H` be a
difficulty function, `𝒜` an algorithm family whose algorithm `𝒜 T` stops after `T` rounds, and
`μ`, `λ` two models without a common correct answer, with `0 < H(λ) ≤ √T`. Then
`R_{H,T}(𝒜, λ)⁻¹ (1 - p_{μ,T}(𝒜)) ≤ H(λ) ∑ a, E_μ[N_{T,a} / T] KL(ν_a(μ), ν_a(λ)) + log 2 / √T`,
where `N_{T,a}` is the number of pulls of the arm `a` in the first `T` rounds.

The paper writes the term `log 2 / √T` on the left with a minus sign, which is the same in real
numbers; here the quantities are in `ℝ≥0∞`. The paper's `μ, λ ∈ 𝒟` and `i*(λ) ≠ i*(μ)` are
replaced by the disjointness of the correct answers of `μ` and `λ`, and `H(λ) ≠ 0` is the
positivity of the paper's `H : 𝒟 → ℝ⁺`. -/
theorem inv_difficultyRatio_mul_le (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} {T : ℕ} (h𝒜 : IsFixedBudget (𝒜 T) T) {μ μ' : Θ}
    (hμμ' : Disjoint (task.correct μ) (task.correct μ')) (hH₀ : H μ' ≠ 0)
    (hH : H μ' ≤ ENNReal.ofReal √T) :
    (task.difficultyRatio H 𝒜 μ' T)⁻¹ * (1 - task.errorProb 𝒜 μ T) ≤
      H μ' * ∑ a, (∫⁻ ω, (pullCount IT.action a T ω : ℝ≥0∞)
          ∂(trajMeasure (𝒜 T).alg (Environment.bandit (task.ν μ)))) / T *
          klDiv (task.ν μ a) (task.ν μ' a) +
        ENNReal.ofReal (Real.log 2 / √T) := by
  have hT : T ≠ 0 := by
    rintro rfl
    exact hH₀ (by simpa using hH)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero hT
  -- Multiply the change of measure by `H(λ) / T`, with `H(λ) / T ≤ 1 / √T`.
  have hsum : H μ' * ∑ a, (∫⁻ ω, (pullCount IT.action a T ω : ℝ≥0∞)
      ∂(trajMeasure (𝒜 T).alg (Environment.bandit (task.ν μ)))) / T *
        klDiv (task.ν μ a) (task.ν μ' a) = H μ' / T * ∑ a, (∫⁻ ω, (pullCount IT.action a T ω : ℝ≥0∞)
      ∂(trajMeasure (𝒜 T).alg (Environment.bandit (task.ν μ)))) *
        klDiv (task.ν μ a) (task.ν μ' a) := by
    simp_rw [ENNReal.div_eq_inv_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    ring
  have hlog : H μ' / T * ENNReal.ofReal (Real.log 2) ≤ ENNReal.ofReal (Real.log 2 / √T) :=
    calc H μ' / T * ENNReal.ofReal (Real.log 2)
        ≤ ENNReal.ofReal √T / ENNReal.ofReal T * ENNReal.ofReal (Real.log 2) := by
          rw [ENNReal.ofReal_natCast]
          gcongr
      _ = ENNReal.ofReal (Real.log 2 / √T) := by
          rw [← ENNReal.ofReal_div_of_pos hTpos, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have hs : √(T : ℝ) * √T = T := Real.mul_self_sqrt hTpos.le
          rw [div_mul_eq_mul_div, div_eq_div_iff hTpos.ne' (Real.sqrt_pos.2 hTpos).ne']
          linear_combination (Real.log 2) * hs
  calc (task.difficultyRatio H 𝒜 μ' T)⁻¹ * (1 - task.errorProb 𝒜 μ T)
      = H μ' / T * ((1 - task.errorProb 𝒜 μ T) *
          (-ENNReal.log (task.errorProb 𝒜 μ' T)).toENNReal) := by
        rw [inv_difficultyRatio hH₀ (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH) hT,
          ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        ring
    _ ≤ _ := by
        grw [task.one_sub_errorProb_mul_neg_log_errorProb_le h𝒜 hμμ', mul_add, hsum, hlog]

/-- **Theorem 2 with the expected proportions of pulls** [D23, Theorem 2]: under the hypotheses of
`inv_difficultyRatio_mul_le`,
`R_{H,T}(𝒜, λ)⁻¹ (1 - p_{μ,T}(𝒜)) ≤ H(λ) cost(w_T, μ, λ) + log 2 / √T`, where `w_T` are the
expected proportions of pulls of `𝒜 T` at `μ` and `cost(w, μ, λ) = ∑ a, w a KL(ν_a(μ), ν_a(λ))`
is the transportation cost. -/
theorem inv_difficultyRatio_mul_le_cost (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} {T : ℕ} (h𝒜 : IsFixedBudget (𝒜 T) T) {μ μ' : Θ}
    (hμμ' : Disjoint (task.correct μ) (task.correct μ')) (hH₀ : H μ' ≠ 0)
    (hH : H μ' ≤ ENNReal.ofReal √T) :
    (task.difficultyRatio H 𝒜 μ' T)⁻¹ * (1 - task.errorProb 𝒜 μ T) ≤
      H μ' * task.cost (expectedPullProportion (𝒜 T) (Environment.bandit (task.ν μ))) μ μ' +
        ENNReal.ofReal (Real.log 2 / √T) := by
  have hT : T ≠ 0 := by
    rintro rfl
    simp_all
  convert inv_difficultyRatio_mul_le task H h𝒜 hμμ' hH₀ hH using 3
  rw [cost_def]
  congr 1 with a
  rw [h𝒜.lintegral_pullCount_div hT]

/-- **Theorem 2 for large budgets** [D23, proofs of Theorems 3 and 13]. Let `𝒜` be a fixed-budget
family whose probability of error at the model `μ` tends to `0`, and let `c < 1` and `B < ∞`. For
every large enough budget `T`, every model `λ` without a common correct answer with `μ` with
`0 < H(λ) ≤ B` satisfies `c R_{H,T}(𝒜, λ)⁻¹ ≤ H(λ) cost(w_T, μ, λ) + log 2 / √T`, where `w_T` are
the expected proportions of pulls of `𝒜 T` at `μ`. -/
theorem eventually_mul_inv_difficultyRatio_le (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} (h𝒜 : IsFixedBudgetFamily 𝒜) {μ : Θ}
    (hμ : Tendsto (task.errorProb 𝒜 μ) atTop (𝓝 0)) {c : ℝ≥0∞} (hc : c < 1) {B : ℝ≥0∞}
    (hB : B ≠ ∞) :
    ∀ᶠ T in atTop, ∀ μ', Disjoint (task.correct μ) (task.correct μ') → H μ' ≠ 0 → H μ' ≤ B →
        c * (task.difficultyRatio H 𝒜 μ' T)⁻¹ ≤
          H μ' * task.cost (expectedPullProportion (𝒜 T) (Environment.bandit (task.ν μ))) μ μ' +
            ENNReal.ofReal (Real.log 2 / √T) := by
  have h1 : ∀ᶠ T in atTop, task.errorProb 𝒜 μ T < 1 - c :=
    hμ.eventually (gt_mem_nhds (tsub_pos_of_lt hc))
  have h2 : ∀ᶠ T : ℕ in atTop, B ≤ ENNReal.ofReal √T := by
    filter_upwards [eventually_ge_atTop ⌈B.toReal ^ 2⌉₊] with T hT
    rw [← ENNReal.ofReal_toReal hB]
    exact ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le ((Nat.le_ceil _).trans
      (by exact_mod_cast hT)))
  filter_upwards [h1, h2] with T hp hBT μ' hμμ' hH₀ hH
  have hc' : c ≤ 1 - task.errorProb 𝒜 μ T :=
    ENNReal.le_sub_of_add_le_left (ne_top_of_lt hp) (lt_tsub_iff_right.1 hp).le
  calc c * (task.difficultyRatio H 𝒜 μ' T)⁻¹
      ≤ (task.difficultyRatio H 𝒜 μ' T)⁻¹ * (1 - task.errorProb 𝒜 μ T) := by
        rw [mul_comm]
        gcongr
    _ ≤ _ := inv_difficultyRatio_mul_le_cost task H (h𝒜.isFixedBudget T) hμμ' hH₀ (hH.trans hBT)

/-! ### The asymptotic lower bounds -/

/-- **Theorem 2 along a subsequence of budgets.** Let `𝒜` be a fixed-budget family whose
probability of error at the model `μ` tends to `0`, and `λ` a model without a common correct
answer with `μ`, at finite divergences `KL(ν_a(μ), ν_a(λ))`, with `H(λ)` positive and finite. If
along the budgets `ψ n → ∞` the expected proportions of pulls of `𝒜 (ψ n)` at `μ` converge to
`w₀`, then `liminf_T R_{H,T}(𝒜, λ)⁻¹ ≤ H(λ) cost(w₀, μ, λ)`. -/
theorem liminf_inv_difficultyRatio_le_of_tendsto (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} (h𝒜 : IsFixedBudgetFamily 𝒜) {μ μ' : Θ}
    (hμ : Tendsto (task.errorProb 𝒜 μ) atTop (𝓝 0))
    (hμμ' : Disjoint (task.correct μ) (task.correct μ')) (hH₀ : H μ' ≠ 0) (hH : H μ' ≠ ∞)
    (hfin : ∀ a, klDiv (task.ν μ a) (task.ν μ' a) ≠ ∞) {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop)
    {w₀ : α → ℝ}
    (hw₀ : Tendsto (fun n ↦ expectedPullProportion (𝒜 (ψ n)) (Environment.bandit (task.ν μ)))
      atTop (𝓝 w₀)) :
    liminf (fun T ↦ (task.difficultyRatio H 𝒜 μ' T)⁻¹) atTop ≤ H μ' * task.cost w₀ μ μ' := by
  refine hψ.liminf_le_liminf_comp.trans (ENNReal.le_of_forall_lt_one_mul_le fun c hc ↦ ?_)
  have hcost : Tendsto (fun n ↦ H μ' * task.cost (expectedPullProportion (𝒜 (ψ n))
      (Environment.bandit (task.ν μ))) μ μ' + ENNReal.ofReal (Real.log 2 / √(ψ n))) atTop
      (𝓝 (H μ' * task.cost w₀ μ μ')) := by
    rw [← add_zero (H μ' * task.cost w₀ μ μ'), ← ENNReal.ofReal_zero]
    refine Tendsto.add (ENNReal.Tendsto.const_mul ?_ (Or.inr hH)) (ENNReal.tendsto_ofReal
      (tendsto_const_nhds.div_atTop ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).comp
        hψ)))
    simp_rw [cost_def]
    refine tendsto_finsetSum _ fun a _ ↦ ENNReal.Tendsto.mul_const ?_ (Or.inr (hfin a))
    exact ENNReal.tendsto_ofReal (((continuous_apply a).tendsto w₀).comp hw₀)
  calc c * liminf ((fun T ↦ (task.difficultyRatio H 𝒜 μ' T)⁻¹) ∘ ψ) atTop
      ≤ c * limsup ((fun T ↦ (task.difficultyRatio H 𝒜 μ' T)⁻¹) ∘ ψ) atTop := by
        gcongr
        exact liminf_le_limsup
    _ = limsup (fun n ↦ c * (task.difficultyRatio H 𝒜 μ' (ψ n))⁻¹) atTop :=
        (ENNReal.limsup_const_mul_of_ne_top (ne_top_of_lt hc)).symm
    _ ≤ H μ' * task.cost w₀ μ μ' := by
        refine (limsup_le_limsup ?_).trans_eq hcost.limsup_eq
        filter_upwards [hψ.eventually (eventually_mul_inv_difficultyRatio_le task H h𝒜 hμ hc
          hH)] with n hn
        exact hn μ' hμμ' hH₀ le_rfl

omit [DecidableEq α] in
/-- **Asymptotic lower bound on the difficulty ratio over a set of alternatives**
[D23, Theorem 3]. Let `𝒜` be a fixed-budget algorithm family whose probability of error at the
model `μ` tends to `0`, and `D` a set of models without a common correct answer with `μ`, on which
the difficulty function `H` is positive and finite. Then
`(sup_{λ ∈ D} R_{H,∞}(𝒜, λ))⁻¹ ≤ max_{w ∈ Δ_K} inf_{λ ∈ D} H(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ))`.

The paper assumes `𝒜` consistent, `μ ∈ 𝒟` and `D ⊆ Alt(μ)`; only the convergence to `0` of the
probability of error at `μ` and the disjointness of the correct answers are needed. The bound
also holds at the alternatives at infinite divergence from `μ` on some arm. -/
theorem inv_iSup_asymptoticRatio_le (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} (h𝒜 : IsFixedBudgetFamily 𝒜) {μ : Θ}
    (hμ : Tendsto (task.errorProb 𝒜 μ) atTop (𝓝 0)) {D : Set Θ}
    (hD : ∀ μ' ∈ D, Disjoint (task.correct μ) (task.correct μ')) (hH₀ : ∀ μ' ∈ D, H μ' ≠ 0)
    (hH : ∀ μ' ∈ D, H μ' ≠ ∞) :
    (⨆ μ' ∈ D, task.asymptoticRatio H 𝒜 μ')⁻¹ ≤
      ⨆ w ∈ simplex α, ⨅ μ' ∈ D, H μ' * task.cost w μ μ' := by
  classical
  -- A subsequence `ψ` of budgets along which the expected proportions of pulls converge to `w₀`.
  set w : ℕ → α → ℝ := fun T ↦ expectedPullProportion (𝒜 T) (Environment.bandit (task.ν μ))
  obtain ⟨w₀, hw₀, φ, hφ, hlim⟩ := (isCompact_simplex α).tendsto_subseq
    (x := fun n ↦ w (n + 1))
    (fun n ↦ (h𝒜.isFixedBudget _).expectedPullProportion_mem_simplex n.succ_ne_zero _)
  have hψ : Tendsto (fun n ↦ φ n + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop
  -- `(sup_{λ ∈ D} R_{H,∞}(𝒜, λ))⁻¹ = inf_{λ ∈ D} liminf_T R_{H,T}(𝒜, λ)⁻¹`.
  simp_rw [ENNReal.inv_iSup, asymptoticRatio_def, ENNReal.inv_limsup]
  refine ENNReal.le_of_forall_lt_one_mul_le fun c hc ↦ ?_
  have : Nonempty α := nonempty_of_mem_simplex hw₀
  have hc1 : c.toNNReal < 1 := by
    rwa [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hc.ne_top, ENNReal.coe_one]
  -- Mix the limit proportions with the uniform allocation, which has positive entries.
  set v : α → ℝ := (c.toNNReal : ℝ) • w₀ + (1 - (c.toNNReal : ℝ)) • fun _ ↦ (Fintype.card α : ℝ)⁻¹
  have hv : v ∈ simplex α := convex_simplex α hw₀ (uniform_mem_simplex α) c.toNNReal.coe_nonneg
    (by linarith [NNReal.coe_lt_one.2 hc1]) (by ring)
  have hu : 0 < (1 - (c.toNNReal : ℝ)) * (Fintype.card α : ℝ)⁻¹ :=
    mul_pos (by linarith [NNReal.coe_lt_one.2 hc1]) (by positivity)
  have hva (a : α) : 0 < v a := by
    have := mul_nonneg c.toNNReal.coe_nonneg ((mem_simplex_iff.1 hw₀).1 a)
    simp only [v, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    positivity
  -- `c cost(w₀, μ, λ) ≤ cost(v, μ, λ)`.
  have hcv (μ' : Θ) : c * task.cost w₀ μ μ' ≤ task.cost v μ μ' := by
    calc c * task.cost w₀ μ μ' = task.cost (c.toNNReal • w₀) μ μ' := by
          rw [cost_smul, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_toNNReal hc.ne_top]
      _ ≤ task.cost v μ μ' := monotone_cost task μ μ' fun a ↦ by
          simp only [v, Pi.add_apply, Pi.smul_apply, NNReal.smul_def, smul_eq_mul]
          linarith
  refine le_iSup₂_of_le (f := fun w _ ↦ ⨅ μ' ∈ D, H μ' * task.cost w μ μ') v hv ?_
  calc c * ⨅ μ' ∈ D, liminf (fun T ↦ (task.difficultyRatio H 𝒜 μ' T)⁻¹) atTop
      ≤ ⨅ μ' ∈ D, c * liminf (fun T ↦ (task.difficultyRatio H 𝒜 μ' T)⁻¹) atTop :=
        le_iInf₂ fun μ' hμ' ↦ by gcongr; exact iInf₂_le μ' hμ'
    _ ≤ ⨅ μ' ∈ D, H μ' * task.cost v μ μ' := iInf₂_mono fun μ' hμ' ↦ ?_
  by_cases hfin : ∀ a, klDiv (task.ν μ a) (task.ν μ' a) ≠ ∞
  · calc c * liminf (fun T ↦ (task.difficultyRatio H 𝒜 μ' T)⁻¹) atTop
        ≤ c * (H μ' * task.cost w₀ μ μ') := by
          gcongr
          exact liminf_inv_difficultyRatio_le_of_tendsto task H h𝒜 hμ (hD μ' hμ') (hH₀ μ' hμ')
            (hH μ' hμ') hfin hψ hlim
      _ = H μ' * (c * task.cost w₀ μ μ') := mul_left_comm _ _ _
      _ ≤ H μ' * task.cost v μ μ' := by gcongr; exact hcv μ'
  · -- At an infinite divergence on the arm `a`, `v a > 0` makes the cost infinite.
    push Not at hfin
    obtain ⟨a, ha⟩ := hfin
    rw [task.cost_eq_top_of_klDiv_eq_top (hva a) ha, ENNReal.mul_top (hH₀ μ' hμ')]
    exact le_top

omit [DecidableEq α] in
/-- **Asymptotic lower bound on the maximal difficulty ratio** [D23, Theorem 3]. Let `𝒜` be a
consistent fixed-budget algorithm family and `H` a difficulty function that is positive and
finite on the admissible models. Then `(sup_{λ ∈ 𝒟} R_{H,∞}(𝒜, λ))⁻¹` is at most
`inf_{μ ∈ 𝒟} max_{w ∈ Δ_K} inf_{λ ∈ Alt(μ)} H(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ))`. -/
theorem inv_maxRatio_le (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} (h𝒜 : IsFixedBudgetFamily 𝒜) (hcons : task.IsConsistent 𝒜)
    (hH₀ : ∀ μ' ∈ task.M, H μ' ≠ 0) (hH : ∀ μ' ∈ task.M, H μ' ≠ ∞) :
    (task.maxRatio H 𝒜)⁻¹ ≤
      ⨅ μ ∈ task.M, ⨆ w ∈ simplex α, ⨅ μ' ∈ task.alternatives μ, H μ' * task.cost w μ μ' := by
  refine le_iInf₂ fun μ hμ ↦ le_trans ?_ (inv_iSup_asymptoticRatio_le task H h𝒜 (hcons μ hμ)
    (fun μ' h ↦ (task.mem_alternatives_iff.1 h).2)
    (fun μ' h ↦ hH₀ μ' (task.alternatives_subset_M μ h))
    (fun μ' h ↦ hH μ' (task.alternatives_subset_M μ h)))
  rw [ENNReal.inv_le_inv]
  exact iSup_asymptoticRatio_le_maxRatio (task.alternatives_subset_M μ)

omit [Fintype α] [DecidableEq α] in
/-- **The lower bound from alternatives along the coordinates** [D23, Corollary 4]. Let `𝒜` be a
fixed-budget algorithm family whose probability of error at the model `μ` tends to `0`, `s` a set
of arms and, for every arm `j ∈ s`, `λ j` a model without a common correct answer with `μ`, whose
arms other than `j` have the same laws as those of `μ`, and at which the difficulty function `H` is
positive and finite. Then
`∑_{j ∈ s} 1 / (H(λ j) KL(ν_j(μ), ν_j(λ j))) ≤ sup_{j ∈ s} R_{H,∞}(𝒜, λ j)`.

The paper takes `s` to be all the arms and assumes `𝒜` consistent; the convergence to `0` of the
probability of error at `μ` suffices, as in `inv_iSup_asymptoticRatio_le`. -/
theorem sum_inv_le_iSup_asymptoticRatio [Finite α] (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} (h𝒜 : IsFixedBudgetFamily 𝒜) {μ : Θ}
    (hμ : Tendsto (task.errorProb 𝒜 μ) atTop (𝓝 0)) (s : Finset α) (μ' : α → Θ)
    (hdisj : ∀ j ∈ s, Disjoint (task.correct μ) (task.correct (μ' j)))
    (hν : ∀ j ∈ s, ∀ a ≠ j, task.ν (μ' j) a = task.ν μ a) (hH₀ : ∀ j ∈ s, H (μ' j) ≠ 0)
    (hH : ∀ j ∈ s, H (μ' j) ≠ ∞) :
    ∑ j ∈ s, (H (μ' j) * klDiv (task.ν μ j) (task.ν (μ' j) j))⁻¹ ≤
      ⨆ j ∈ s, task.asymptoticRatio H 𝒜 (μ' j) := by
  have := Fintype.ofFinite α
  classical
  have h := inv_iSup_asymptoticRatio_le task H h𝒜 hμ (D := μ' '' s)
    (by rintro _ ⟨j, hj, rfl⟩; exact hdisj j hj) (by rintro _ ⟨j, hj, rfl⟩; exact hH₀ j hj)
    (by rintro _ ⟨j, hj, rfl⟩; exact hH j hj)
  rw [iSup_image] at h
  simp only [Finset.mem_coe] at h
  -- The cost of `w` at `λ j` is `w j KL(ν_j(μ), ν_j(λ j))`.
  have hcost (w : α → ℝ) (j : α) (hj : j ∈ s) : H (μ' j) * task.cost w μ (μ' j) =
      H (μ' j) * klDiv (task.ν μ j) (task.ν (μ' j) j) * ENNReal.ofReal (w j) := by
    rw [cost_def, Finset.sum_eq_single j
      (fun a _ ha ↦ by rw [hν j hj a ha, klDiv_self, mul_zero]) (by simp)]
    ring
  have h2 : ⨆ w ∈ simplex α, ⨅ μ'' ∈ μ' '' s, H μ'' * task.cost w μ μ'' =
      ⨆ w ∈ simplex α, ⨅ j ∈ s,
        H (μ' j) * klDiv (task.ν μ j) (task.ν (μ' j) j) * ENNReal.ofReal (w j) := by
    refine iSup_congr fun w ↦ iSup_congr fun _ ↦ ?_
    rw [iInf_image]
    exact iInf_congr fun j ↦ iInf_congr fun hj ↦ hcost w j hj
  exact ENNReal.inv_le_inv.1 (h.trans (h2.trans_le (iSup_iInf_mul_ofReal_le_inv_sum_inv s _)))

omit [DecidableEq α] in
/-- **Lower bound on the liminf of the maximal difficulty ratio over a set of alternatives**
[D23, Theorem 13]. Let `𝒜` be a fixed-budget algorithm family whose probability of error at the
model `μ` tends to `0`, and `D` a set of models without a common correct answer with `μ`, on which
the difficulty function `H` is positive and bounded. Then
`(liminf_T sup_{λ ∈ D} R_{H,T}(𝒜, λ))⁻¹` is at most
`max_{w ∈ Δ_K} inf_{λ ∈ D} H(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ))`.

The paper's `μ ∈ 𝒟` and `D ⊆ Alt(μ)` are replaced by the disjointness of the correct answers, and
`H(λ) ≠ 0` is the positivity of the paper's `H : 𝒟 → ℝ⁺`. -/
theorem inv_liminf_iSup_difficultyRatio_le (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} (h𝒜 : IsFixedBudgetFamily 𝒜) {μ : Θ}
    (hμ : Tendsto (task.errorProb 𝒜 μ) atTop (𝓝 0)) {D : Set Θ}
    (hD : ∀ μ' ∈ D, Disjoint (task.correct μ) (task.correct μ')) (hH₀ : ∀ μ' ∈ D, H μ' ≠ 0)
    (hH : ⨆ μ' ∈ D, H μ' ≠ ∞) :
    (liminf (fun T ↦ ⨆ μ' ∈ D, task.difficultyRatio H 𝒜 μ' T) atTop)⁻¹ ≤
      ⨆ w ∈ simplex α, ⨅ μ' ∈ D, H μ' * task.cost w μ μ' := by
  classical
  set V := ⨆ w ∈ simplex α, ⨅ μ' ∈ D, H μ' * task.cost w μ μ'
  -- `(liminf_T sup_{λ ∈ D} R_{H,T})⁻¹ = limsup_T inf_{λ ∈ D} R_{H,T}⁻¹`.
  rw [ENNReal.inv_liminf]
  simp_rw [ENNReal.inv_iSup]
  refine ENNReal.le_of_forall_lt_one_mul_le fun c hc ↦ ?_
  rw [← ENNReal.limsup_const_mul_of_ne_top (ne_top_of_lt hc)]
  have hlim : Tendsto (fun T : ℕ ↦ V + ENNReal.ofReal (Real.log 2 / √T)) atTop (𝓝 V) := by
    simpa using tendsto_const_nhds.add (ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)))
  refine (limsup_le_limsup ?_).trans_eq hlim.limsup_eq
  filter_upwards [eventually_mul_inv_difficultyRatio_le task H h𝒜 hμ hc hH,
    eventually_ne_atTop 0] with T hT hT0
  have hw := (h𝒜.isFixedBudget T).expectedPullProportion_mem_simplex hT0
    (Environment.bandit (task.ν μ))
  calc c * ⨅ μ' ∈ D, (task.difficultyRatio H 𝒜 μ' T)⁻¹
      ≤ ⨅ μ' ∈ D, c * (task.difficultyRatio H 𝒜 μ' T)⁻¹ :=
        le_iInf₂ fun μ' hμ' ↦ by gcongr; exact iInf₂_le μ' hμ'
    _ ≤ ⨅ μ' ∈ D, (H μ' * task.cost (expectedPullProportion (𝒜 T)
          (Environment.bandit (task.ν μ))) μ μ' + ENNReal.ofReal (Real.log 2 / √T)) :=
        iInf₂_mono fun μ' hμ' ↦ hT μ' (hD μ' hμ') (hH₀ μ' hμ')
          (le_iSup₂ (f := fun μ' _ ↦ H μ') μ' hμ')
    _ = (⨅ μ' ∈ D, H μ' * task.cost (expectedPullProportion (𝒜 T)
          (Environment.bandit (task.ν μ))) μ μ') + ENNReal.ofReal (Real.log 2 / √T) := by
        simp only [ENNReal.iInf_add]
    _ ≤ V + ENNReal.ofReal (Real.log 2 / √T) := by
        gcongr
        exact le_iSup₂ (f := fun w _ ↦ ⨅ μ' ∈ D, H μ' * task.cost w μ μ') _ hw

omit [DecidableEq α] in
/-- **Lower bound on the liminf of the maximal difficulty ratio** [D23, Corollary 14]. Let `𝒜` be
a consistent fixed-budget algorithm family and `H` a difficulty function that is positive on the
admissible models. With `Alt_x(μ)` the alternatives `λ` to `μ` with `H(λ) ≤ x`,
`(liminf_T sup_{λ ∈ 𝒟} R_{H,T}(𝒜, λ))⁻¹` is at most
`liminf_{x → ∞} inf_{μ ∈ 𝒟} max_{w ∈ Δ_K} inf_{λ ∈ Alt_x(μ)} H(λ) ∑ a, w a KL(ν_a(μ), ν_a(λ))`.

`H(λ) ≠ 0` is the positivity of the paper's `H : 𝒟 → ℝ⁺`. -/
theorem inv_liminf_iSup_difficultyRatio_le_liminf (task : IdentTask α Θ ℐ 𝓨) (H : Θ → ℝ≥0∞)
    {𝒜 : ℕ → IdentAlg Unit α 𝓨 ℐ} (h𝒜 : IsFixedBudgetFamily 𝒜) (hcons : task.IsConsistent 𝒜)
    (hH₀ : ∀ μ' ∈ task.M, H μ' ≠ 0) :
    (liminf (fun T ↦ ⨆ μ' ∈ task.M, task.difficultyRatio H 𝒜 μ' T) atTop)⁻¹ ≤
      liminf (fun x : ℝ ↦ ⨅ μ ∈ task.M, ⨆ w ∈ simplex α,
        ⨅ μ' ∈ {μ' | μ' ∈ task.alternatives μ ∧ H μ' ≤ ENNReal.ofReal x},
          H μ' * task.cost w μ μ') atTop := by
  refine le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall fun x ↦ ?_)
  refine le_iInf₂ fun μ hμ ↦ le_trans ?_ (inv_liminf_iSup_difficultyRatio_le task H h𝒜
    (hcons μ hμ) (D := {μ' | μ' ∈ task.alternatives μ ∧ H μ' ≤ ENNReal.ofReal x})
    (fun μ' h ↦ (task.mem_alternatives_iff.1 h.1).2)
    (fun μ' h ↦ hH₀ μ' (task.alternatives_subset_M μ h.1))
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup₂_le fun μ' h ↦ h.2)))
  -- `sup_{λ ∈ Alt_x(μ)} R_{H,T} ≤ sup_{λ ∈ 𝒟} R_{H,T}`.
  rw [ENNReal.inv_le_inv]
  exact liminf_le_liminf (Eventually.of_forall fun T ↦ iSup₂_mono' fun μ' h ↦
    ⟨μ', task.alternatives_subset_M μ h.1, le_rfl⟩)

end LMLExplore.Identification.IdentTask
