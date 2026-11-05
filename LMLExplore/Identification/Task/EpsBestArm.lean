/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.ExpFamily
public import LMLExplore.Identification.Task.Classical

/-!
# The alternatives of `ε`-best arm identification and the cost of the alternatives

In `ε`-best arm identification (`epsBaiTask ν id ε`), the correct answers of a vector of means `μ`
are its `ε`-good arms, the arms `a` with `μ b ≤ μ a + ε` for every arm `b`. An arm `a` is thus not
`ε`-good for `μ'` exactly when some arm `b` has `μ' a + ε < μ' b`.

Let the arm `c` belong to an exponential family `(ρ c, T c)` with divergence `d_c` in the mean
parametrization. The arm `a` stops being `ε`-good once one of the following happens:

* the mean of another arm `b` is moved above `μ a + ε`; as the new mean decreases to `μ a + ε`,
  this costs `D(μ, w, ¬a) ≤ w b d_b(μ b, μ a + ε)`;
* the mean of `a` is moved below `μ b - ε` for another arm `b`; as the new mean increases to
  `μ b - ε`, this costs `D(μ, w, ¬a) ≤ w a d_a(μ a, μ b - ε)`.

Each of these bounds involves a single arm. Through the change of measure
`kl(δ, 1 - δ) ≤ D(μ, n, ¬a)` for the expected numbers of pulls `n` of a `δ`-correct algorithm
(`LMLExplore.Identification.IdentTask.IsDeltaCorrect.klBer_le_altCost`), they give a lower bound on
the expected number of pulls of every arm, whose sum is a lower bound on the sample complexity of
`ε`-best arm identification, of the order of `K / ε²` for Bernoulli arms [MT04, Theorem 1]
(`LMLExplore/Identification/EpsBestArmLowerBound.lean`).

## Main statements

* `LMLExplore.Identification.mem_alt_epsBaiTask_iff`: a model `θ` is an alternative to `a` iff
  some arm `b` has `mean θ a + ε < mean θ b`, for any mean functional `mean`.
* `LMLExplore.Identification.altCost_epsBaiTask_restrict_le_ofReal_mul_expFamilyDiv_add`: for an
  arm `b ≠ a`, `D(μ, w, ¬a) ≤ w b d_b(μ b, μ a + ε)`.
* `LMLExplore.Identification.altCost_epsBaiTask_restrict_le_ofReal_mul_expFamilyDiv_sub`: for an
  arm `b ≠ a`, `D(μ, w, ¬a) ≤ w a d_a(μ a, μ b - ε)`.

## References

* [MT04] S. Mannor and J. N. Tsitsiklis, *The sample complexity of exploration in the multi-armed
  bandit problem*, JMLR 5 (2004), Theorem 1.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Measure

open scoped ENNReal

namespace LMLExplore.Identification

variable {α Θ 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  {ρ : α → Measure 𝓨} {T : α → 𝓨 → ℝ} {μ μ' w : α → ℝ} {ε : ℝ} {a b : α}

/-- In `ε`-best arm identification, `θ` is an alternative to the arm `a` iff `a` is not `ε`-good
for `θ`: some arm `b` has `mean θ a + ε < mean θ b`. -/
lemma mem_alt_epsBaiTask_iff (ν : Θ → Kernel α 𝓨) [∀ θ, IsMarkovKernel (ν θ)]
    (mean : Θ → α → ℝ) {θ : Θ} :
    θ ∈ (epsBaiTask ν mean ε).alt a ↔ ∃ b, mean θ a + ε < mean θ b := by
  simp [IdentTask.mem_alt_iff]

variable (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)]

variable [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- **The cost of raising another arm above `μ a + ε`.** Let the arm `c` belong to an exponential
family `(ρ c, T c)` with divergence `d_c` and let `μ` be a vector of means of the families. For
arms `b ≠ a` such that `μ a + ε` is a mean of the family of `b` and every nonnegative allocation
`w`, `D(μ, w, ¬a) ≤ w b d_b(μ b, μ a + ε)` in `ε`-best arm identification, within the vectors of
means of the families: moving the mean of `b` above `μ a + ε` makes `a` not `ε`-good. -/
theorem altCost_epsBaiTask_restrict_le_ofReal_mul_expFamilyDiv_add
    (hT : ∀ c x, ¬ T c =ᵐ[ρ c] fun _ ↦ x) (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hba : b ≠ a) (hb : μ a + ε ∈ (ρ b).expFamilyMeans (T b)) (hw : 0 ≤ w) :
    ((epsBaiTask ν id ε).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).altCost μ w a ≤
      ENNReal.ofReal (w b * (ρ b).expFamilyDiv (T b) (μ b) (μ a + ε)) := by
  classical
  exact IdentTask.altCost_restrict_le_ofReal_mul_expFamilyDiv_of_tendsto (by simp) hν hw hT
    hμ b hb (l := 𝓝[>] (μ a + ε))
    (((continuous_const.update b continuous_id).tendsto _).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun x hx ↦ (mem_alt_epsBaiTask_iff ν id).2
      ⟨b, by simpa [Function.update_of_ne hba.symm] using hx⟩)

omit [DecidableEq α] in
/-- **The cost of lowering `a` below `μ b - ε`.** Let the arm `c` belong to an exponential family
`(ρ c, T c)` with divergence `d_c` and let `μ` be a vector of means of the families. For arms
`b ≠ a` such that `μ b - ε` is a mean of the family of `a` and every nonnegative allocation `w`,
`D(μ, w, ¬a) ≤ w a d_a(μ a, μ b - ε)` in `ε`-best arm identification, within the vectors of means
of the families: moving the mean of `a` below `μ b - ε` makes `a` not `ε`-good. -/
theorem altCost_epsBaiTask_restrict_le_ofReal_mul_expFamilyDiv_sub
    (hT : ∀ c x, ¬ T c =ᵐ[ρ c] fun _ ↦ x) (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hba : b ≠ a) (ha : μ b - ε ∈ (ρ a).expFamilyMeans (T a)) (hw : 0 ≤ w) :
    ((epsBaiTask ν id ε).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).altCost μ w a ≤
      ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) (μ b - ε)) := by
  classical
  exact IdentTask.altCost_restrict_le_ofReal_mul_expFamilyDiv_of_tendsto (by simp) hν hw hT
    hμ a ha (l := 𝓝[<] (μ b - ε))
    (((continuous_const.update a continuous_id).tendsto _).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun x hx ↦ (mem_alt_epsBaiTask_iff ν id).2
      ⟨b, by simpa [Function.update_of_ne hba] using (lt_sub_iff_add_lt.1 hx)⟩)

end LMLExplore.Identification
