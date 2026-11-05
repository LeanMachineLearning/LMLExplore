/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.LowerBound
public import LMLExplore.Identification.Task.TopM

/-!
# Lower bound on the sample complexity of top-`m` identification

Let the arm `c` of a bandit belong to an exponential family `(ρ c, T c)` with divergence `d_c` in
the mean parametrization, and let `μ` be a vector of means of the families whose `m` largest
means, attained on the set of arms `s`, are larger than the other ones. Write `μ_[m]` for the
smallest mean in `s` and `μ_[m+1]` for the largest mean outside `s`. Kaufmann, Cappé and Garivier
[KCG16, Theorem 4] prove that every `δ`-correct algorithm for top-`m` identification, with
`δ ≤ 1 / 2`, satisfies
`E_μ[τ] ≥ (∑_{a ∈ s} d_a(μ a, μ_[m+1])⁻¹ + ∑_{a ∉ s} d_a(μ a, μ_[m])⁻¹) kl(δ, 1 - δ)`,
hence `E_μ[τ] ≥ (∑_{a ∈ s} d_a(μ a, μ_[m+1])⁻¹ + ∑_{a ∉ s} d_a(μ a, μ_[m])⁻¹) log (1 / (2.4 δ))`.

The bound holds arm by arm: an arm `a ∈ s` leaves the top-`m` set when its mean is moved below
`μ_[m+1]`, at cost `d_a(μ a, μ_[m+1])` per pull of `a`, so that the change of measure gives
`kl(δ, 1 - δ) ≤ E_μ[N_a(τ)] d_a(μ a, μ_[m+1])`; symmetrically for `a ∉ s` and `μ_[m]`. Summing
over the arms with Wald's identity `E_μ[τ] = ∑ a, E_μ[N_a(τ)]` gives the lower bound. Arms with
equal means are allowed: the alternatives used to move an arm out of (or into) the top-`m` set
also move every other arm outside `s` (or inside `s`), except the arm with mean `μ_[m+1]` (or
`μ_[m]`), by an amount `t` that vanishes in the limit
(`LMLExplore/Identification/Task/TopM.lean`).

The algorithm is only required to be `δ`-correct on the vectors of means of the families
(`IdentTask.restrict`), so that the bound applies to algorithms designed for a given family.

## Main statements

In the namespace `LMLExplore.Identification.IdentTask`:

* `IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_topMTask_of_mem`,
  `IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_topMTask_of_notMem`:
  `kl(δ, 1 - δ) ≤ E_μ[N_a(τ)] d_a(μ a, μ_[m+1])` for `a ∈ s`, and
  `kl(δ, 1 - δ) ≤ E_μ[N_a(τ)] d_a(μ a, μ_[m])` for `a ∉ s`.
* `IsDeltaCorrect.mul_klBer_le_expectedStoppingTime_topMTask`: the lower bound in terms of
  `kl(δ, 1 - δ)` [KCG16, Theorem 4].
* `IsDeltaCorrect.mul_ofReal_log_le_expectedStoppingTime_topMTask`: the lower bound in terms of
  `log (1 / (c δ))` for `c ≥ 2.4` [KCG16, Theorem 4].

## References

* [KCG16] E. Kaufmann, O. Cappé and A. Garivier, *On the complexity of best-arm identification in
  multi-armed bandit models*, JMLR 17 (2016), Theorem 4.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Learning

open scoped ENNReal

namespace LMLExplore.Identification.IdentTask

variable {α 𝓨 : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {m𝓨 : MeasurableSpace 𝓨} [MeasurableSpace.CountablyGenerated 𝓨]
  {mℐ : MeasurableSpace (Finset α)} [MeasurableSingletonClass (Finset α)]
  {ρ : α → Measure 𝓨} {T : α → 𝓨 → ℝ} {ν : (α → ℝ) → Kernel α 𝓨} [∀ μ, IsMarkovKernel (ν μ)]
  {μ : α → ℝ} {m : ℕ} {s : Finset α} {a b : α} {A : IdentAlg Unit α 𝓨 (Finset α)} {δ : ℝ}

/-- `IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_of_altCost_le` for top-`m` identification on
the vectors of means of the families: if `A` is `δ`-correct with `δ ≤ 1 / 2` and `E_μ[τ] < ∞`,
then `kl(δ, 1 - δ) ≤ E_μ[N_a(τ)] x` for every arm
`a` and every `x` such that `D(μ, w, ¬s) ≤ w a x` for all nonnegative allocations `w`. -/
private lemma IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_of_altCost_le_topMTask
    (hA : ((topMTask ν m).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).IsDeltaCorrect
      A δ) (hδ : δ ≤ 1 / 2) (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c))
    (hs : s ∈ (topMTask ν m).correct μ) (h : expectedStoppingTime A (Environment.bandit (ν μ)) ≠ ∞)
    {x : ℝ} (h_alt : ∀ w : α → ℝ, 0 ≤ w →
      ((topMTask ν m).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).altCost μ w s ≤
        ENNReal.ofReal (w a * x)) :
    klBer δ (1 - δ) ≤ (∫⁻ ω, (pullCount IT.action a
        (ENat.toNat (A.stoppingTime IT.obs IT.action IT.feedback ω)) ω : ℝ≥0∞)
          ∂(trajMeasure A.alg (Environment.bandit (ν μ)))) * ENNReal.ofReal x := by
  have hμM : μ ∈ (topMTask ν m).M := by
    have hs' := hs
    simp only [correct_topMTask, Set.mem_ofPred_eq] at hs'
    simp only [M_topMTask, Set.mem_ofPred_eq]
    exact ⟨s, hs'⟩
  simpa using hA.klBer_le_lintegral_pullCount_mul_of_altCost_le_restrict hδ hμM hμ
    ((subsingleton_correct_topMTask ν m μ).eq_singleton_of_mem hs) (by simpa using h) h_alt

omit [Fintype α] in
/-- **Lower bound on the number of pulls of an arm of the top-`m` set** [KCG16, proof of
Theorem 4]. Let the arm `c` belong to an exponential family `(ρ c, T c)` with divergence `d_c`, let
`μ` be a vector of means of the families whose top-`m` set is `s`, and let `b ∉ s` be an arm with
the largest mean outside `s`. Let `A` be `δ`-correct for top-`m` identification on the vectors of
means of the families, with `δ ≤ 1 / 2` and `E_μ[τ] < ∞`. For `a ∈ s` such that `μ b` is a mean
of the family of `a`, `kl(δ, 1 - δ) ≤ E_μ[N_a(τ)] d_a(μ a, μ b)`. -/
theorem IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_topMTask_of_mem [Finite α]
    (hA : ((topMTask ν m).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).IsDeltaCorrect
      A δ) (hδ : δ ≤ 1 / 2) (hT : ∀ c x, ¬ T c =ᵐ[ρ c] fun _ ↦ x)
    (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hs : s ∈ (topMTask ν m).correct μ) (ha : a ∈ s) (hb : b ∉ s)
    (hb_max : ∀ c ∉ s, μ c ≤ μ b) (hba : μ b ∈ (ρ a).expFamilyMeans (T a))
    (h : expectedStoppingTime A (Environment.bandit (ν μ)) ≠ ∞) :
    klBer δ (1 - δ) ≤ (∫⁻ ω, (pullCount IT.action a
        (ENat.toNat (A.stoppingTime IT.obs IT.action IT.feedback ω)) ω : ℝ≥0∞)
          ∂(trajMeasure A.alg (Environment.bandit (ν μ)))) *
        ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (μ b)) := by
  have := Fintype.ofFinite α
  exact hA.klBer_le_lintegral_pullCount_mul_of_altCost_le_topMTask hδ hμ hs h fun _ hw ↦
    altCost_topMTask_restrict_le_ofReal_mul_expFamilyDiv_of_mem ν hT hμ hν
      hs ha hb hb_max hba hw

omit [Fintype α] in
/-- **Lower bound on the number of pulls of an arm outside the top-`m` set** [KCG16, proof of
Theorem 4]. Let the arm `c` belong to an exponential family `(ρ c, T c)` with divergence `d_c`, let
`μ` be a vector of means of the families whose top-`m` set is `s`, and let `b ∈ s` be an arm with
the smallest mean in `s`. Let `A` be `δ`-correct for top-`m` identification on the vectors of
means of the families, with `δ ≤ 1 / 2` and `E_μ[τ] < ∞`. For `a ∉ s` such that `μ b` is a mean
of the family of `a`, `kl(δ, 1 - δ) ≤ E_μ[N_a(τ)] d_a(μ a, μ b)`. -/
theorem IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_topMTask_of_notMem [Finite α]
    (hA : ((topMTask ν m).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).IsDeltaCorrect
      A δ) (hδ : δ ≤ 1 / 2) (hT : ∀ c x, ¬ T c =ᵐ[ρ c] fun _ ↦ x)
    (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hs : s ∈ (topMTask ν m).correct μ) (ha : a ∉ s) (hb : b ∈ s)
    (hb_min : ∀ c ∈ s, μ b ≤ μ c) (hba : μ b ∈ (ρ a).expFamilyMeans (T a))
    (h : expectedStoppingTime A (Environment.bandit (ν μ)) ≠ ∞) :
    klBer δ (1 - δ) ≤ (∫⁻ ω, (pullCount IT.action a
        (ENat.toNat (A.stoppingTime IT.obs IT.action IT.feedback ω)) ω : ℝ≥0∞)
          ∂(trajMeasure A.alg (Environment.bandit (ν μ)))) *
        ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (μ b)) := by
  have := Fintype.ofFinite α
  exact hA.klBer_le_lintegral_pullCount_mul_of_altCost_le_topMTask hδ hμ hs h fun _ hw ↦
    altCost_topMTask_restrict_le_ofReal_mul_expFamilyDiv_of_notMem ν hT hμ hν
      hs ha hb hb_min hba hw

/-- **Lower bound on the sample complexity of top-`m` identification** [KCG16, Theorem 4]. Let the
arm `c` belong to an exponential family `(ρ c, T c)` with divergence `d_c`, let `μ` be a vector of
means of the families whose top-`m` set is `s`, let `b₀ ∉ s` be an arm with the largest mean
outside `s` and `b₁ ∈ s` an arm with the smallest mean in `s`, and suppose that `μ b₀` is a mean of
the families of the arms of `s` and `μ b₁` of the families of the other arms. If `A` is
`δ`-correct for top-`m` identification on the vectors of means of the families, with `δ ≤ 1 / 2`,
then `(∑_{a ∈ s} d_a(μ a, μ b₀)⁻¹ + ∑_{a ∉ s} d_a(μ a, μ b₁)⁻¹) kl(δ, 1 - δ) ≤ E_μ[τ]`. -/
theorem IsDeltaCorrect.mul_klBer_le_expectedStoppingTime_topMTask {b₀ b₁ : α}
    (hA : ((topMTask ν m).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).IsDeltaCorrect
      A δ) (hδ : δ ≤ 1 / 2) (hT : ∀ c x, ¬ T c =ᵐ[ρ c] fun _ ↦ x)
    (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hs : s ∈ (topMTask ν m).correct μ) (hb₀ : b₀ ∉ s) (hb₀_max : ∀ c ∉ s, μ c ≤ μ b₀)
    (hb₁ : b₁ ∈ s) (hb₁_min : ∀ c ∈ s, μ b₁ ≤ μ c)
    (hb₀s : ∀ a ∈ s, μ b₀ ∈ (ρ a).expFamilyMeans (T a))
    (hb₁s : ∀ a ∉ s, μ b₁ ∈ (ρ a).expFamilyMeans (T a)) :
    (∑ a ∈ s, (ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (μ b₀)))⁻¹ +
        ∑ a ∈ sᶜ, (ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (μ b₁)))⁻¹) *
        klBer δ (1 - δ) ≤
      expectedStoppingTime A (Environment.bandit (ν μ)) := by
  rcases eq_or_ne (expectedStoppingTime A (Environment.bandit (ν μ))) ∞ with h | h
  · simp [h]
  -- Divide the lower bound on the number of pulls of each arm by its divergence, then sum over
  -- the arms with Wald's identity.
  rw [expectedStoppingTime_eq_sum_lintegral_pullCount (.of_expectedStoppingTime_ne_top h),
    ← Finset.sum_add_sum_compl s, add_mul, Finset.sum_mul, Finset.sum_mul]
  simp_rw [← ENNReal.div_eq_inv_mul]
  exact add_le_add (Finset.sum_le_sum fun a ha ↦ ENNReal.div_le_of_le_mul <|
      hA.klBer_le_lintegral_pullCount_mul_topMTask_of_mem hδ hT hμ hν hs ha hb₀ hb₀_max
        (hb₀s a ha) h)
    (Finset.sum_le_sum fun a ha ↦ ENNReal.div_le_of_le_mul <|
      hA.klBer_le_lintegral_pullCount_mul_topMTask_of_notMem hδ hT hμ hν hs
        (Finset.mem_compl.1 ha) hb₁ hb₁_min (hb₁s a (Finset.mem_compl.1 ha)) h)

/-- **Lower bound on the sample complexity of top-`m` identification in logarithmic form**
[KCG16, Theorem 4]. Under the assumptions of `mul_klBer_le_expectedStoppingTime_topMTask` (except
`δ ≤ 1 / 2`), for every `c ≥ 2.4`,
`(∑_{a ∈ s} d_a(μ a, μ b₀)⁻¹ + ∑_{a ∉ s} d_a(μ a, μ b₁)⁻¹) log (1 / (c δ)) ≤ E_μ[τ]`; the constant
of Kaufmann, Cappé and Garivier is `c = 2.4`. -/
theorem IsDeltaCorrect.mul_ofReal_log_le_expectedStoppingTime_topMTask {b₀ b₁ : α}
    (hA : ((topMTask ν m).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).IsDeltaCorrect
      A δ) {c : ℝ} (hc : 2.4 ≤ c) (hT : ∀ c x, ¬ T c =ᵐ[ρ c] fun _ ↦ x)
    (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hs : s ∈ (topMTask ν m).correct μ) (hb₀ : b₀ ∉ s) (hb₀_max : ∀ c ∉ s, μ c ≤ μ b₀)
    (hb₁ : b₁ ∈ s) (hb₁_min : ∀ c ∈ s, μ b₁ ≤ μ c)
    (hb₀s : ∀ a ∈ s, μ b₀ ∈ (ρ a).expFamilyMeans (T a))
    (hb₁s : ∀ a ∉ s, μ b₁ ∈ (ρ a).expFamilyMeans (T a)) :
    (∑ a ∈ s, (ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (μ b₀)))⁻¹ +
        ∑ a ∈ sᶜ, (ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (μ b₁)))⁻¹) *
        ENNReal.ofReal (Real.log (1 / (c * δ))) ≤
      expectedStoppingTime A (Environment.bandit (ν μ)) :=
  mul_ofReal_log_le_of_mul_klBer_le hc fun hδ ↦
    hA.mul_klBer_le_expectedStoppingTime_topMTask hδ hT hμ hν hs hb₀ hb₀_max hb₁ hb₁_min hb₀s hb₁s

end LMLExplore.Identification.IdentTask
