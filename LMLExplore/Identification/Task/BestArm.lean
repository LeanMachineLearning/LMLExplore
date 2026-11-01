/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.MeanVector
public import LMLExplore.Identification.Task.TransportationCost

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

## Main statements

* `LMLExplore.Identification.mem_alt_baiTask_iff`: the alternatives to `a` are the vectors with a
  unique best arm `b ≠ a`.
* `LMLExplore.Identification.closure_alt_baiTask_restrict_inter`: for `S` open, the closure of the
  alternatives to `a` within `S` is `{λ | ∃ b ≠ a, λ a ≤ λ b} ∩ S`;
  `LMLExplore.Identification.closure_alt_baiTask` is the case `S = univ`.
* `LMLExplore.Identification.altCost_baiTask_restrict_eq_iInf`: for `S` open and a transportation
  cost continuous on that set,
  `D(μ, w, ¬a) = min_{b ≠ a} inf {cost_μ(w, λ) | λ ∈ S, λ a ≤ λ b}`.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Section 2.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology

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

/-- A vector of means in which some arm `b ≠ a` has mean at least that of `a` is a limit of
alternatives to `a`: raising the largest mean, attained at an arm `b ≠ a`, makes `b` the unique
best arm. -/
lemma mem_closure_alt_baiTask_restrict (hS : IsOpen S) (hμ'S : μ' ∈ S)
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
  -- `t > 0`.
  set f : ℝ → α → ℝ := fun t ↦ μ' + t • Pi.single b 1 with hf
  have hf_tendsto : Tendsto f (𝓝[>] 0) (𝓝 μ') := by
    have hf_cont : Continuous f := by fun_prop
    simpa [hf] using hf_cont.continuousWithinAt.tendsto (x := 0) (s := Set.Ioi 0)
  refine mem_closure_of_tendsto hf_tendsto ?_
  filter_upwards [hf_tendsto.eventually (hS.mem_nhds hμ'S), self_mem_nhdsWithin] with t htS ht
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
    (fun μ' ⟨hμ', hμ'S⟩ ↦ ⟨mem_closure_alt_baiTask_restrict ν hS hμ'S hμ', hμ'S⟩)
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

end LMLExplore.Identification
