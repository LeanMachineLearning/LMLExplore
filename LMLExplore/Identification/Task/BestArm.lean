/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.MeanVector
public import LMLExplore.Identification.Task.TransportationCost
public import LMLExplore.Probability.Distributions.ExponentialFamily.Mean

/-!
# The alternatives of best arm identification and their closure

For best arm identification (`baiTask ν`), the alternatives to an arm `a` are the vectors of means
with a unique best arm `b ≠ a`. This set is not closed: its limits include the vectors where `a`
ties with another best arm, which have no correct answer. The cost of the alternatives
`D(μ, w, ¬a) = inf_{λ ∈ ¬a} ∑ b, w b KL(ν_b(μ), ν_b(λ))` is an infimum over this set, and the
analysis of best arm identification of Garivier and Kaufmann (2016) computes it on the closed set
`{λ | ∃ b ≠ a, λ a ≤ λ b}` of the vectors whose largest mean is attained at an arm `b ≠ a`, one
arm `b` at a time.

The admissible models of an identification problem are the vectors whose means lie in the mean
sets of the arm families (the means of an exponential family form an open interval), that is
`(baiTask ν).restrict S` for an open set `S` of vectors of means. Within `S`, the closure of the
alternatives to `a` is the closed set above, and when the transportation cost is continuous there,
the cost of the alternatives is the infimum of the cost over it.

When the arms belong to an exponential family with divergence `d` and `a` is a best arm of `μ`,
the infimum for the arm `b` is attained by moving the means of `a` and `b` to their mean weighted
by the allocation, which gives the closed form of the cost of the alternatives used to compute the
optimal allocations of best arm identification [GK16, Lemma 3].

## Main statements

* `LMLExplore.Identification.mem_alt_baiTask_iff`: the alternatives to `a` are the vectors with a
  unique best arm `b ≠ a`.
* `LMLExplore.Identification.closure_alt_baiTask_restrict_inter`: for `S` open, the closure of the
  alternatives to `a` within `S` is `{λ | ∃ b ≠ a, λ a ≤ λ b} ∩ S`;
  `LMLExplore.Identification.closure_alt_baiTask` is the case `S = univ`.
* `LMLExplore.Identification.altCost_baiTask_restrict_eq_iInf`: for `S` open and a transportation
  cost continuous on `{λ | ∃ b ≠ a, λ a ≤ λ b} ∩ S`,
  `D(μ, w, ¬a) = min_{b ≠ a} inf {cost_μ(w, λ) | λ ∈ S, λ a ≤ λ b}`.
* `LMLExplore.Identification.altCost_baiTask_restrict_eq_iInf_expFamilyDiv`: for arms in an
  exponential family with divergence `d`, a best arm `a` of `μ` and a nonnegative allocation `w`,
  `D(μ, w, ¬a) = min_{b ≠ a} (w a d(μ a, m_b) + w b d(μ b, m_b))` on the vectors of means of the
  family, with `m_b = (w a μ a + w b μ b) / (w a + w b)` [GK16, Lemma 3].

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Section 2 and Lemma 3.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Measure

open scoped ENNReal

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (ν : (α → ℝ) → Kernel α 𝓨) [∀ μ, IsMarkovKernel (ν μ)] {S : Set (α → ℝ)} {a : α}
  {μ' : α → ℝ}

/-- The alternatives to the arm `a` in best arm identification are the vectors of means with a
unique best arm `b ≠ a`. -/
lemma mem_alt_baiTask_iff : μ' ∈ (baiTask ν).alt a ↔ ∃ b ≠ a, ∀ c ≠ b, μ' c < μ' b := by
  simp only [IdentTask.mem_alt_iff, M_baiTask, correct_baiTask, Set.mem_ofPred_eq, not_forall,
    not_lt, exists_prop]
  constructor
  · rintro ⟨⟨b, hb⟩, c, hca, hc⟩
    refine ⟨b, ?_, hb⟩
    rintro rfl
    exact (hb c hca).not_ge hc
  · rintro ⟨b, hba, hb⟩
    exact ⟨⟨b, hb⟩, b, hba, (hb a hba.symm).le⟩

section Closure

variable [Finite α]

/-- For a neighbourhood `S` of a vector of means `μ'` in which some arm `b ≠ a` has mean at least
that of `a`, the vector `μ'` lies in the closure of the alternatives to `a` of
`(baiTask ν).restrict S`. -/
lemma mem_closure_alt_baiTask_restrict (hS : S ∈ 𝓝 μ')
    (hμ' : ∃ b ≠ a, μ' a ≤ μ' b) : μ' ∈ closure (((baiTask ν).restrict S).alt a) := by
  classical
  -- An arm `b ≠ a` with the largest mean.
  obtain ⟨b, hba, hb⟩ : ∃ b ≠ a, ∀ c, μ' c ≤ μ' b := by
    obtain ⟨b, hba, hab⟩ := hμ'
    have : Nonempty α := ⟨a⟩
    obtain ⟨d, hd⟩ := Finite.exists_max μ'
    by_cases hda : d = a
    · exact ⟨b, hba, fun c ↦ (hda ▸ hd c).trans hab⟩
    · exact ⟨d, hda, hd⟩
  -- The path `t ↦ μ' + t • Pi.single b 1` tends to `μ'` and lies in the alternatives for small
  -- `t > 0`: raising the largest mean makes `b` the unique best arm.
  set f : ℝ → α → ℝ := fun t ↦ μ' + t • Pi.single b 1 with hf
  have hf_tendsto : Tendsto f (𝓝[>] 0) (𝓝 μ') := by
    have hf_cont : Continuous f := by fun_prop
    simpa [hf] using hf_cont.continuousWithinAt.tendsto (x := 0) (s := Set.Ioi 0)
  refine mem_closure_of_tendsto hf_tendsto ?_
  filter_upwards [hf_tendsto.eventually hS, self_mem_nhdsWithin] with t htS ht
  rw [IdentTask.alt_restrict]
  refine ⟨(mem_alt_baiTask_iff ν).2 ⟨b, hba, fun c hcb ↦ ?_⟩, htS⟩
  simpa [hf, Pi.single_apply, hcb] using (hb c).trans_lt (lt_add_of_pos_right _ ht)

/-- For an open set `S` of vectors of means, the closure within `S` of the alternatives to the arm
`a` in best arm identification restricted to `S` is the set of the vectors of `S` in which some
arm `b ≠ a` has mean at least that of `a`, that is, whose largest mean is attained at an arm
`b ≠ a`. -/
theorem closure_alt_baiTask_restrict_inter (hS : IsOpen S) (a : α) :
    closure (((baiTask ν).restrict S).alt a) ∩ S = {μ' | ∃ b ≠ a, μ' a ≤ μ' b} ∩ S := by
  refine Set.Subset.antisymm (fun μ' ⟨hμ', hμ'S⟩ ↦ ⟨?_, hμ'S⟩)
    (fun μ' ⟨hμ', hμ'S⟩ ↦ ⟨mem_closure_alt_baiTask_restrict ν (hS.mem_nhds hμ'S) hμ', hμ'S⟩)
  -- The set is closed, as a finite union of the closed sets `{μ' | μ' a ≤ μ' b}`, `b ≠ a`, and it
  -- contains the alternatives.
  have h_closed : IsClosed {μ' : α → ℝ | ∃ b ≠ a, μ' a ≤ μ' b} := by
    simp only [Set.ofPred_exists]
    refine isClosed_iUnion_of_finite fun b ↦ ?_
    by_cases hba : b = a
    · simp [hba]
    · simpa [hba] using isClosed_le (continuous_apply a) (continuous_apply b)
  refine closure_minimal (fun μ'' hμ'' ↦ ?_) h_closed hμ'
  rw [IdentTask.alt_restrict] at hμ''
  obtain ⟨b, hba, hb⟩ := (mem_alt_baiTask_iff ν).1 hμ''.1
  exact ⟨b, hba, (hb a hba.symm).le⟩

/-- The closure of the alternatives to the arm `a` in best arm identification is the set of the
vectors of means in which some arm `b ≠ a` has mean at least that of `a`, that is, whose largest
mean is attained at an arm `b ≠ a`. -/
theorem closure_alt_baiTask (a : α) :
    closure ((baiTask ν).alt a) = {μ' | ∃ b ≠ a, μ' a ≤ μ' b} := by
  simpa using closure_alt_baiTask_restrict_inter ν isOpen_univ a

end Closure

variable [Fintype α]

/-- For an open set `S` of vectors of means and a transportation cost from `μ` continuous on the
vectors of `S` in which some arm `b ≠ a` has mean at least that of `a`, the cost of the
alternatives to `a` in best arm identification restricted to `S` is
`D(μ, w, ¬a) = min_{b ≠ a} inf {cost_μ(w, λ) | λ ∈ S, λ a ≤ λ b}` [GK16, Section 2]. -/
theorem altCost_baiTask_restrict_eq_iInf (hS : IsOpen S) {μ : α → ℝ} {w : α → ℝ}
    (hc : ContinuousOn ((baiTask ν).cost w μ) ({μ' | ∃ b ≠ a, μ' a ≤ μ' b} ∩ S)) :
    ((baiTask ν).restrict S).altCost μ w a =
      ⨅ (b) (_ : b ≠ a) (μ' ∈ S) (_ : μ' a ≤ μ' b), (baiTask ν).cost w μ μ' := by
  have h_eq := closure_alt_baiTask_restrict_inter ν hS a
  have h_alt : ((baiTask ν).restrict S).alt a ⊆ {μ' | ∃ b ≠ a, μ' a ≤ μ' b} ∩ S := fun μ' hμ' ↦
    h_eq ▸ ⟨subset_closure hμ', ((baiTask ν).alt_restrict a ▸ hμ').2⟩
  rw [IdentTask.altCost_eq_biInf_of_subset_closure _ h_alt (fun μ' hμ' ↦ (h_eq.symm.subset hμ').1)
    (by rwa [IdentTask.cost_restrict]), IdentTask.cost_restrict]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, iInf_and, iInf_exists]
  -- Bring the arm `b` and the condition `b ≠ a` in front, then swap the two conditions on `μ'`.
  rw [iInf_comm]
  refine iInf_congr fun b ↦ ?_
  rw [iInf_comm]
  exact iInf_congr fun _ ↦ iInf_congr fun _ ↦ iInf_comm

section ExpFamily

/-! ### Arms in an exponential family -/

variable {ρ : Measure 𝓨} {T : 𝓨 → ℝ} {μ w : α → ℝ}

/-- On the vectors of means of an exponential family, the transportation cost from `μ` to `μ'` is
`∑ c, w c d(μ c, μ' c)` when the divergences between the arm laws are those of the family. -/
private lemma cost_baiTask_eq_ofReal_sum (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hw : 0 ≤ w) {μ' : α → ℝ} (hμ' : ∀ c, μ' c ∈ ρ.expFamilyMeans T) :
    (baiTask ν).cost w μ μ' = ENNReal.ofReal (∑ c, w c * ρ.expFamilyDiv T (μ c) (μ' c)) := by
  rw [IdentTask.cost_def, ENNReal.ofReal_sum_of_nonneg fun c _ ↦
    mul_nonneg (hw c) (expFamilyDiv_nonneg (hμ c) (hμ' c))]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [ν_baiTask, hν μ' hμ' c, ENNReal.ofReal_mul (hw c)]

/-- Moving the means of two arms `a ≠ b` of `μ` to a common mean `z` of the family gives a vector
of means of the family in which `b` is at least as good as `a`, at transportation cost
`w a d(μ a, z) + w b d(μ b, z)` from `μ`. -/
private lemma iInf_cost_baiTask_le (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hw : 0 ≤ w) {b : α} (hba : b ≠ a) {z : ℝ} (hz : z ∈ ρ.expFamilyMeans T) :
    ⨅ μ' ∈ {μ' : α → ℝ | ∀ c, μ' c ∈ ρ.expFamilyMeans T}, ⨅ (_ : μ' a ≤ μ' b),
        (baiTask ν).cost w μ μ' ≤
      ENNReal.ofReal (w a * ρ.expFamilyDiv T (μ a) z + w b * ρ.expFamilyDiv T (μ b) z) := by
  classical
  set μ' := Function.update (Function.update μ a z) b z
  have hμ' (c : α) : μ' c ∈ ρ.expFamilyMeans T := by
    simp only [μ', Function.update_apply]
    split_ifs
    exacts [hz, hz, hμ c]
  refine (iInf₂_le μ' hμ').trans (iInf_le_of_le (by simp [μ', hba.symm]) ?_)
  rw [cost_baiTask_eq_ofReal_sum ν hμ hν hw hμ',
    ← Finset.sum_subset (Finset.subset_univ {a, b}) fun c _ hc ↦ ?_, Finset.sum_pair hba.symm]
  · simp [μ', hba.symm]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    simp [μ', hc.1, hc.2, expFamilyDiv_self]

/-- **The cost of the alternatives in best arm identification with arms in an exponential
family** [GK16, Lemma 3]. Let the arm laws of best arm identification belong to an exponential
family with divergence `d`, in the sense that `KL(ν_c(μ), ν_c(μ')) = d(μ c, μ' c)` for all vectors
of means `μ'` of the family (for example when `ν μ' c` is the member of mean `μ' c`, by
`klDiv_expFamily_natParam`), and let `a` be a best arm of `μ`. Then on the vectors of means of the
family, for every nonnegative allocation `w`,
`D(μ, w, ¬a) = min_{b ≠ a} (w a d(μ a, m_b) + w b d(μ b, m_b))`, where
`m_b = (w a μ a + w b μ b) / (w a + w b)` is the mean of `μ a` and `μ b` weighted by `w`: the
cost of the alternatives in which `b` beats `a` is approached by moving both means to `m_b`. -/
theorem altCost_baiTask_restrict_eq_iInf_expFamilyDiv
    (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (ha : ∀ b, μ b ≤ μ a) (hw : 0 ≤ w) :
    ((baiTask ν).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).altCost μ w a =
      ⨅ (b) (_ : b ≠ a), ENNReal.ofReal
        (w a * ρ.expFamilyDiv T (μ a) ((w a * μ a + w b * μ b) / (w a + w b)) +
          w b * ρ.expFamilyDiv T (μ b) ((w a * μ a + w b * μ b) / (w a + w b))) := by
  classical
  have hw' (c : α) : 0 ≤ w c := hw c
  set S := {μ' : α → ℝ | ∀ c, μ' c ∈ ρ.expFamilyMeans T} with hS_def
  have hS : IsOpen S := by
    rw [hS_def, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun c ↦ (isOpen_expFamilyMeans hT).preimage (continuous_apply c)
  have h_cost {μ' : α → ℝ} (hμ' : μ' ∈ S) := cost_baiTask_eq_ofReal_sum ν hμ hν hw hμ'
  -- The cost is continuous on the vectors of means of the family, so that the alternatives can
  -- be replaced by their closure, in which `b` is at least as good as `a` for some `b ≠ a`.
  have hc : ContinuousOn ((baiTask ν).cost w μ) S := by
    refine ContinuousOn.congr ?_ fun μ' hμ' ↦ h_cost hμ'
    refine ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_finsetSum _ fun c _ ↦ continuousOn_const.mul ?_)
    exact (continuousOn_expFamilyDiv hT).comp (f := fun μ' : α → ℝ ↦ (μ c, μ' c)) (by fun_prop)
      fun μ' hμ' ↦ ⟨hμ c, hμ' c⟩
  rw [altCost_baiTask_restrict_eq_iInf ν hS (hc.mono Set.inter_subset_right)]
  refine iInf_congr fun b ↦ iInf_congr fun hba ↦ le_antisymm ?_ ?_
  · -- Upper bound: move the means of `a` and `b` to the weighted mean `m_b`, a mean of the
    -- family between `μ b` and `μ a` (or to `μ a` if both weights vanish).
    rcases (add_nonneg (hw a) (hw b)).eq_or_lt with hW | hW
    · obtain ⟨hwa, hwb⟩ : w a = 0 ∧ w b = 0 :=
        ⟨by linarith [hw' a, hw' b], by linarith [hw' a, hw' b]⟩
      simpa [hwa, hwb, hS_def] using iInf_cost_baiTask_le ν hμ hν hw hba (hμ a)
    refine iInf_cost_baiTask_le ν hμ hν hw hba
      (convex_expFamilyMeans.ordConnected.out (hμ b) (hμ a) ⟨?_, ?_⟩)
    · rw [le_div_iff₀ hW]
      nlinarith [ha b, hw' a]
    · rw [div_le_iff₀ hW]
      nlinarith [ha b, hw' b]
  · -- Lower bound: drop the arms other than `a` and `b`, then move both means to `m_b`.
    refine le_iInf₂ fun μ' hμ' ↦ le_iInf fun hab ↦ ?_
    rw [h_cost hμ']
    refine ENNReal.ofReal_le_ofReal ((mul_expFamilyDiv_add_mul_expFamilyDiv_le hT (hμ a) (hμ b)
      (ha b) (hw a) (hw b) (hμ' a) (hμ' b) hab).trans ?_)
    rw [← Finset.sum_pair (f := fun c ↦ w c * ρ.expFamilyDiv T (μ c) (μ' c)) hba.symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ ↦
      mul_nonneg (hw c) (expFamilyDiv_nonneg (hμ c) (hμ' c))

end ExpFamily

end LMLExplore.Identification
