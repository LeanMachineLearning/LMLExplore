/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.BestArm
public import LMLExplore.Identification.Task.TopTwo.Basic

/-!
# The `β`-optimal allocation of best arm identification

Top Two sampling rules for best arm identification sample the leader, an estimate of the best
arm, with a fixed probability `β`, and the proportions of their samples target the `β`-optimal
allocations: the maximizers of the cost of the alternatives `D(μ, w, ¬a)` among the allocations
that give the proportion `β` to the best arm `a`. This file shows that, for arms in an exponential
family with divergence `d`, at a vector of means `μ` of the family with unique best arm `a` and
for `β > 0`, there is at most one `β`-optimal allocation, and exactly one for `β ∈ (0, 1]` as soon
as there are two arms, and that it is characterized by the equality of the costs of the pairs
`(a, b)`, `b ≠ a` [R16, Proposition 7]. That a `β`-optimal allocation equalizes these costs,
`LMLExplore.Identification.betaAnswerValue_baiTask_restrict_eq_of_mem_betaOptAlloc`, is proved in
`LMLExplore/Identification/Task/BestArm.lean`, where it gives the equalization property of the
optimal allocation [GK16, Lemma 4] as the case `β = w a`.

By the closed form [GK16, Lemma 3] of the cost of the alternatives, on the allocations with
`w a = β`, `D(μ, w, ¬a) = min_{b ≠ a} C_b(w b)`, where `C_b(x) = β d(μ a, m_b) + x d(μ b, m_b)`
with `m_b = (β μ a + x μ b) / (β + x)` is the cost of the alternatives in which `b` beats `a`. Each
`C_b` is strictly increasing (`MeasureTheory.Measure.strictMonoOn_expFamilyPairCost`), so that the
weights of an allocation that equalizes these costs are determined by their common value, and the
constraint `∑ b ≠ a, w b = 1 - β` determines that value.

For `β ∈ (0, 1)`, the `β`-value `D_β(μ, ¬a)`, the inverse of the `β`-characteristic time, is
positive, and the `β`-optimal allocation gives a positive proportion to every arm. The `β`-optimal
allocation is the asymptotic target of the proportions of samples of the Top Two algorithms with
parameter `β` [R16; JDBdHK22].

## Main statements

* `LMLExplore.Identification.betaAnswerValue_baiTask_restrict_pos`: for `β ∈ (0, 1)` and two arms,
  `D_β(μ, ¬a) > 0`.
* `LMLExplore.Identification.expFamilyPairCost_eq_of_mem_betaOptAlloc_baiTask_restrict`: for
  `β > 0`, the costs of the pairs `(a, b)` and `(a, c)` at two `β`-optimal allocations are equal.
* `LMLExplore.Identification.mem_betaOptAlloc_baiTask_restrict_iff`: for `β > 0`, the
  `β`-optimal allocations are the allocations with `w a = β` that equalize the costs of the pairs
  [R16, Proposition 7].
* `LMLExplore.Identification.subsingleton_betaOptAlloc_baiTask_restrict`,
  `LMLExplore.Identification.exists_betaOptAlloc_baiTask_restrict_eq_singleton`: for `β > 0`,
  there is at most one `β`-optimal allocation, and exactly one for `β ∈ (0, 1]` and two arms
  [R16, Proposition 7].
* `LMLExplore.Identification.pos_of_mem_betaOptAlloc_baiTask_restrict`: for `β ∈ (0, 1)`, the
  `β`-optimal allocation has positive entries.

## References

* [R16] D. Russo, *Simple Bayesian algorithms for best arm identification*, COLT 2016;
  Operations Research 68 (2020). Proposition 7 in the numbering of arXiv:1602.08448v4.
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Lemmas 3 and 4.
* [JDBdHK22] M. Jourdan, R. Degenne, D. Baudry, R. de Heide and E. Kaufmann, *Top two algorithms
  revisited*, NeurIPS 2022.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Measure

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)] {ρ : Measure 𝓨} {T : 𝓨 → ℝ}
  {μ w : α → ℝ} {a b : α} {β : ℝ}

/-- For arms in an exponential family (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`)
and a vector of means `μ` of the family with unique best arm `a`, the `β`-value `D_β(μ, ¬a)` of the
answer `a` is positive for `β ∈ (0, 1)`, as soon as there is an arm `b ≠ a`: it is at least
`min(β, 1 - β) D(μ, ¬a)` [R16, Lemma 3]. The `β`-characteristic time `T*_β(μ) = D_β(μ, ¬a)⁻¹` is
then finite. -/
theorem betaAnswerValue_baiTask_restrict_pos (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) (hba : b ≠ a) (hβ : β ∈ Set.Ioo 0 1) :
    0 < ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).betaAnswerValue μ a a β :=
  (ENNReal.mul_pos (by simpa using lt_min hβ.1 (sub_pos.2 hβ.2))
    (answerValue_baiTask_restrict_pos ν hT hμ hν ha).ne').trans_le
    (IdentTask.ofReal_min_mul_answerValue_le_betaAnswerValue _ hba μ a β)

/-- For arms in an exponential family (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`),
a vector of means `μ` of the family with unique best arm `a` and `β > 0`, the costs
`β d(μ a, m_b) + w b d(μ b, m_b)` and `β d(μ a, m'_c) + w' c d(μ c, m'_c)` of the pairs `(a, b)`
and `(a, c)`, `b, c ≠ a`, at two `β`-optimal allocations `w` and `w'` are equal: both are the
`β`-value `D_β(μ, ¬a)` (`betaAnswerValue_baiTask_restrict_eq_of_mem_betaOptAlloc`). -/
theorem expFamilyPairCost_eq_of_mem_betaOptAlloc_baiTask_restrict
    (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) (hβ : 0 < β) {w' : α → ℝ} {c : α}
    (hw : w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).betaOptAlloc μ a a β)
    (hw' : w' ∈
      ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).betaOptAlloc μ a a β)
    (hba : b ≠ a) (hca : c ≠ a) :
    ρ.expFamilyPairCost T (μ a) (μ b) β (w b) = ρ.expFamilyPairCost T (μ a) (μ c) β (w' c) := by
  have hw0 := (mem_simplex_iff.1 ((IdentTask.mem_betaOptAlloc_iff _).1 hw).1).1
  have hw0' := (mem_simplex_iff.1 ((IdentTask.mem_betaOptAlloc_iff _).1 hw').1).1
  exact (ENNReal.ofReal_eq_ofReal_iff (expFamilyPairCost_nonneg (hμ a) (hμ b) hβ.le (hw0 b))
    (expFamilyPairCost_nonneg (hμ a) (hμ c) hβ.le (hw0' c))).1
    ((betaAnswerValue_baiTask_restrict_eq_of_mem_betaOptAlloc ν hT hμ hν ha hβ hw hba).symm.trans
      (betaAnswerValue_baiTask_restrict_eq_of_mem_betaOptAlloc ν hT hμ hν ha hβ hw' hca))

/-- **The `β`-optimal allocations of best arm identification** [R16, Proposition 7]. For arms in
an exponential family (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`), a vector of
means `μ` of the family with unique best arm `a` and `β > 0`, an allocation `w` is `β`-optimal for
the answer `a` with the arm `a` iff it gives the proportion `β` to `a` and equalizes the costs
`β d(μ a, m_b) + w b d(μ b, m_b)` of the pairs `(a, b)`, `b ≠ a`, where
`m_b = (β μ a + w b μ b) / (β + w b)`. -/
theorem mem_betaOptAlloc_baiTask_restrict_iff (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) (hβ : 0 < β) :
    w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).betaOptAlloc μ a a β ↔
      w ∈ simplex α ∧ w a = β ∧ ∀ b ≠ a, ∀ c ≠ a,
        ρ.expFamilyPairCost T (μ a) (μ b) β (w b) = ρ.expFamilyPairCost T (μ a) (μ c) β (w c) := by
  classical
  set task := (baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}
  have ha' := apply_le_of_forall_ne_lt ha
  refine ⟨fun hw ↦ ⟨(task.mem_betaOptAlloc_iff.1 hw).1, (task.mem_betaOptAlloc_iff.1 hw).2.1,
    fun b hb c hc ↦ expFamilyPairCost_eq_of_mem_betaOptAlloc_baiTask_restrict ν hT hμ hν ha hβ hw hw
      hb hc⟩, fun ⟨hws, hwa, hw_eq⟩ ↦ ?_⟩
  have hw0 := (mem_simplex_iff.1 hws).1
  -- A `β`-optimal allocation `u` exists, since the cost of the alternatives is continuous in the
  -- allocation and `w` has `w a = β`.
  obtain ⟨u, hu_mem, hu_max⟩ := ((continuousOn_altCost_baiTask_restrict_left ν hT hμ hν ha').mono
    ((Set.sep_subset _ _).trans simplex_subset_nonneg)).upperSemicontinuousOn.exists_isMaxOn
    ⟨w, Set.mem_sep_iff.2 ⟨hws, hwa⟩⟩ (isCompact_setOf_mem_simplex_apply_eq a β)
  have hu := task.mem_betaOptAlloc_iff_isMaxOn.2 ⟨hu_mem, hu_max⟩
  obtain ⟨hus, hua, -⟩ := task.mem_betaOptAlloc_iff.1 hu
  have hu0 := (mem_simplex_iff.1 hus).1
  refine task.mem_betaOptAlloc_iff_isMaxOn.2 ⟨Set.mem_sep_iff.2 ⟨hws, hwa⟩, fun v hv ↦ ?_⟩
  refine (isMaxOn_iff.1 hu_max v hv).trans ?_
  dsimp only
  rw [altCost_baiTask_restrict_eq_inf ν hT hμ hν ha' hu0, hua,
    altCost_baiTask_restrict_eq_inf ν hT hμ hν ha' hw0, hwa]
  refine Finset.le_inf fun b hb ↦ ?_
  have hba := (Finset.mem_filter.1 hb).2
  refine (Finset.inf_le hb).trans (ENNReal.ofReal_le_ofReal (not_lt.1 fun hlt ↦ ?_))
  -- Otherwise the common cost of the pairs is smaller at `w` than at `u`, so that every arm
  -- `c ≠ a` has a smaller weight in `w` than in `u`, while both sum to `1 - β`.
  have h_lt {c : α} (hca : c ≠ a) : w c < u c := by
    refine (strictMonoOn_expFamilyPairCost (hμ a) (hμ c) (ha c hca).ne' hβ).lt_iff_lt
      (Set.mem_Ici.2 (hw0 c)) (Set.mem_Ici.2 (hu0 c)) |>.1 ?_
    rw [hw_eq c hca b hba,
      expFamilyPairCost_eq_of_mem_betaOptAlloc_baiTask_restrict ν hT hμ hν ha hβ hu hu hca hba]
    exact hlt
  have h_sum {v : α → ℝ} (hv : v ∈ simplex α) (hva : v a = β) :
      ∑ c ∈ Finset.univ.erase a, v c = 1 - β := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ a), (mem_simplex_iff.1 hv).2, hva]
  have h := Finset.sum_lt_sum_of_nonempty ⟨b, Finset.mem_erase.2 ⟨hba, Finset.mem_univ b⟩⟩
    fun c hc ↦ h_lt (Finset.ne_of_mem_erase hc)
  rw [h_sum hws hwa, h_sum hus hua] at h
  exact h.false

/-- **The `β`-optimal allocation of best arm identification is unique** [R16, Proposition 7]. For
arms in an exponential family (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`), a
vector of means `μ` of the family with unique best arm `a` and `β > 0`, there is at most one
`β`-optimal allocation of the answer `a` with the arm `a`. -/
theorem subsingleton_betaOptAlloc_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) (hβ : 0 < β) :
    Set.Subsingleton
      (((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).betaOptAlloc μ a a β) := by
  set task := (baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}
  intro w hw w' hw'
  obtain ⟨hws, hwa, -⟩ := task.mem_betaOptAlloc_iff.1 hw
  obtain ⟨hws', hwa', -⟩ := task.mem_betaOptAlloc_iff.1 hw'
  have hw0 := (mem_simplex_iff.1 hws).1
  have hw0' := (mem_simplex_iff.1 hws').1
  funext c
  rcases eq_or_ne c a with rfl | hca
  · rw [hwa, hwa']
  -- The cost of the pair `(a, c)` is the `β`-value at both allocations, and it is injective in
  -- the weight of `c`.
  refine (strictMonoOn_expFamilyPairCost (hμ a) (hμ c) (ha c hca).ne' hβ).injOn
    (Set.mem_Ici.2 (hw0 c)) (Set.mem_Ici.2 (hw0' c)) ?_
  exact expFamilyPairCost_eq_of_mem_betaOptAlloc_baiTask_restrict ν hT hμ hν ha hβ hw hw' hca hca

/-- **The `β`-optimal allocation of best arm identification** [R16, Proposition 7]. For arms in an
exponential family (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`), a vector of means
`μ` of the family with unique best arm `a` and `β ∈ (0, 1]`, there is exactly one `β`-optimal
allocation of the answer `a` with the arm `a`, as soon as there is an arm `b ≠ a`. It equalizes the
costs of the pairs of arms (`betaAnswerValue_baiTask_restrict_eq_of_mem_betaOptAlloc`) and, for
`β < 1`, has positive entries (`pos_of_mem_betaOptAlloc_baiTask_restrict`). -/
theorem exists_betaOptAlloc_baiTask_restrict_eq_singleton (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) (hba : b ≠ a) (hβ : β ∈ Set.Ioc 0 1) :
    ∃ w, ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).betaOptAlloc μ a a β =
      {w} := by
  have ha' := apply_le_of_forall_ne_lt ha
  obtain ⟨w, hw⟩ := IdentTask.betaOptAlloc_nonempty _
    ((continuousOn_altCost_baiTask_restrict_left ν hT hμ hν ha').mono
      simplex_subset_nonneg).upperSemicontinuousOn hba (Set.Ioc_subset_Icc_self hβ)
  exact ⟨w, (subsingleton_betaOptAlloc_baiTask_restrict ν hT hμ hν ha hβ.1).eq_singleton_of_mem hw⟩

/-- **The `β`-optimal allocation of best arm identification has positive entries.** For arms in
an exponential family (as in `altCost_baiTask_restrict_eq_iInf_expFamilyPairCost`), a vector of
means `μ` of the family with unique best arm `a` and `β ∈ (0, 1)`, every `β`-optimal allocation of
the answer `a` with the arm `a` gives a positive proportion to every arm. -/
theorem pos_of_mem_betaOptAlloc_baiTask_restrict (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b < μ a) (hβ : β ∈ Set.Ioo 0 1)
    (hw : w ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).betaOptAlloc μ a a β)
    (c : α) : 0 < w c := by
  obtain ⟨hws, hwa, -⟩ := (IdentTask.mem_betaOptAlloc_iff _).1 hw
  rcases eq_or_ne c a with rfl | hca
  · exact hwa ▸ hβ.1
  -- If `w c = 0`, the pair `(a, c)` costs nothing, so that the `β`-value vanishes.
  refine ((mem_simplex_iff.1 hws).1 c).lt_of_ne' fun hc ↦ ?_
  have h := betaAnswerValue_baiTask_restrict_eq_of_mem_betaOptAlloc ν hT hμ hν ha hβ.1 hw hca
  rw [hc, expFamilyPairCost_eq_zero (Or.inr rfl), ENNReal.ofReal_zero] at h
  exact (betaAnswerValue_baiTask_restrict_pos ν hT hμ hν ha hca hβ).ne' h

end LMLExplore.Identification
