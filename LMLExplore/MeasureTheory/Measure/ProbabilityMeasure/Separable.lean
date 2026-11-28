/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import TauCeti.MeasureTheory.Measure.Portmanteau

/-!
# Separability of the topology of convergence in distribution

Let `X` be a separable pseudo-metrizable space whose σ-algebra contains the open sets. The
probability measures on `X`, with the topology of convergence in distribution, form a separable
space, and a second countable one, since Mathlib makes this topology pseudo-metrizable through the
Lévy–Prokhorov distance (`MeasureTheory.LevyProkhorov.probabilityMeasureHomeomorph`).

A countable dense set is that of the laws `∑ j < N, (a j / M) • δ_{d j}` carried by finitely many
terms of a dense sequence `d`, with rational weights. To approximate a law `P` on a pseudo-metric
space within `2 δ` for the Lévy–Prokhorov distance, cut the space into the cells
`disjointed (fun k ↦ ball (d k) δ)`, keep the first `N` cells, which carry all the mass of `P` but
`δ`, give the point `d k` the mass of the cell `k` rounded down to a multiple of `1 / M`, where
`N / M ≤ δ`, and give the rest of the mass to `d N`.

Tau Ceti has the same two instances for a second countable space whose σ-algebra is standard
Borel and is the Borel σ-algebra (`MeasureTheory.ProbabilityMeasure.instSeparableSpace`,
`MeasureTheory.ProbabilityMeasure.instSecondCountableTopology`), through the Wasserstein spaces.
They are the special case of the instances here, which need neither a Borel σ-algebra nor a
standard Borel space.

## Main definitions

* `MeasureTheory.ProbabilityMeasure.ratAtomLaws d`: the laws `∑ j < N, (a j / M) • δ_{d j}`, for
  `N M : ℕ` and `a : Fin N → ℕ`.

## Main statements

* `MeasureTheory.ProbabilityMeasure.countable_ratAtomLaws`: there are countably many of them.
* `MeasureTheory.ProbabilityMeasure.exists_mem_ratAtomLaws_levyProkhorovDist_lt`: on a
  pseudo-metric space, they are dense for the Lévy–Prokhorov distance when `d` has dense range.
* `MeasureTheory.ProbabilityMeasure.dense_ratAtomLaws`: they are dense for the topology of
  convergence in distribution.
* `MeasureTheory.instSeparableSpaceProbabilityMeasure`,
  `MeasureTheory.instSecondCountableTopologyProbabilityMeasure`: the topology of convergence in
  distribution of the probability measures on a separable pseudo-metrizable space is separable
  and second countable [Par67, Chapter II, Section 6].

## Implementation notes

The statements and proofs are adapted from
`EValuesResearch/ForLMLExplore/MeasureTheory/Measure/ProbabilityMeasure/Separable.lean` (commit
`cb8238f`) in the paper project `RemyDegenne/evalues_research`, which proves the separability
that [EVR26, Note 55, Corollary 9] uses, rewritten on the API of LMLExplore: the cells are the
balls around the terms of `d` made disjoint, whose masses outside finitely many balls are bounded
by Tau Ceti's `MeasureTheory.Measure.tendsto_measure_compl_biUnion_lt_ball`.

The instances are named as Mathlib's `MeasureTheory.instMetrizableSpaceProbabilityMeasure`, and
not as Tau Ceti's, so that both modules can be imported together.

## References

* [Par67] K. R. Parthasarathy, *Probability Measures on Metric Spaces*, Academic Press, 1967,
  Chapter II, Section 6.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 55 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 55, *Classes that are not dominated: attaining the rate and `D*`
  with one procedure*, Corollary 9.
-/

public section

open Function Set TopologicalSpace
open scoped ENNReal

namespace MeasureTheory

namespace ProbabilityMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The probability measures carried by finitely many terms of the sequence `d`, with rational
weights: the laws `∑ j < N, (a j / M) • δ_{d j}`, for `N M : ℕ` and `a : Fin N → ℕ`. -/
def ratAtomLaws (d : ℕ → Ω) : Set (ProbabilityMeasure Ω) :=
  ⋃ (N : ℕ) (M : ℕ) (a : Fin N → ℕ),
    {P | (P : Measure Ω) = ∑ j, ((a j : ℝ≥0∞) / M) • Measure.dirac (d j)}

/-- A law carried by finitely many terms of `d`, with rational weights, is a sum
`∑ j < N, (a j / M) • δ_{d j}`. -/
@[simp]
theorem mem_ratAtomLaws {d : ℕ → Ω} {P : ProbabilityMeasure Ω} :
    P ∈ ratAtomLaws d ↔ ∃ (N M : ℕ) (a : Fin N → ℕ),
      (P : Measure Ω) = ∑ j, ((a j : ℝ≥0∞) / M) • Measure.dirac (d j) := by
  simp only [ratAtomLaws, mem_iUnion, mem_ofPred_eq]

/-- There are countably many laws carried by finitely many terms of a sequence, with rational
weights. -/
theorem countable_ratAtomLaws (d : ℕ → Ω) : (ratAtomLaws d).Countable :=
  countable_iUnion fun _ ↦ countable_iUnion fun _ ↦ countable_iUnion fun _ ↦
    Subsingleton.countable fun _ hP _ hQ ↦ toMeasure_injective (hP.trans hQ.symm)

/-- Rounding the masses of finitely many disjoint measurable sets down to multiples of `1 / M`
keeps their sum at most `M`. -/
private theorem sum_floor_measureReal_mul_le (P : Measure Ω) [IsProbabilityMeasure P]
    {C : ℕ → Set Ω} (hC : ∀ k, MeasurableSet (C k)) (hCdisj : Pairwise (Disjoint on C))
    (N M : ℕ) : ∑ k ∈ Finset.range N, ⌊P.real (C k) * M⌋₊ ≤ M := by
  have h : ∑ k ∈ Finset.range N, P.real (C k) ≤ 1 := by
    rw [← measureReal_biUnion_finset (fun i _ j _ hij ↦ hCdisj hij) fun k _ ↦ hC k]
    exact measureReal_le_one
  have h' : (∑ k ∈ Finset.range N, ⌊P.real (C k) * M⌋₊ : ℝ) ≤ M := calc
    ∑ k ∈ Finset.range N, (⌊P.real (C k) * M⌋₊ : ℝ)
    _ ≤ ∑ k ∈ Finset.range N, P.real (C k) * M :=
      Finset.sum_le_sum fun k _ ↦ Nat.floor_le (by positivity)
    _ ≤ M := by rw [← Finset.sum_mul]; nlinarith
  exact_mod_cast h'

/-- Rounding the mass of a set down to a multiple of `1 / M` loses at most `1 / M`. -/
private theorem measure_le_floor_measureReal_mul_div_add (P : Measure Ω) [IsFiniteMeasure P]
    (s : Set Ω) {M : ℕ} (hM : 0 < M) :
    P s ≤ (⌊P.real s * M⌋₊ : ℝ≥0∞) / M + 1 / M := by
  have hM0 : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have h : P.real s ≤ ((⌊P.real s * M⌋₊ + 1 : ℕ) : ℝ) / M := by
    rw [le_div_iff₀ hM0]
    push_cast
    exact (Nat.lt_floor_add_one _).le
  calc P s = ENNReal.ofReal (P.real s) := (ofReal_measureReal).symm
  _ ≤ ENNReal.ofReal (((⌊P.real s * M⌋₊ + 1 : ℕ) : ℝ) / M) := ENNReal.ofReal_le_ofReal h
  _ = _ := by
    rw [ENNReal.ofReal_div_of_pos hM0, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    push_cast
    exact ENNReal.add_div

/-- The law `∑ k < n, (a k / M) • δ_{d k}` is a probability measure when `∑ k < n, a k = M`
and `M ≠ 0`. -/
private theorem isProbabilityMeasure_sum_div_smul_dirac (d : ℕ → Ω) {n M : ℕ} {a : ℕ → ℕ}
    (hM : M ≠ 0) (ha : ∑ k ∈ Finset.range n, a k = M) :
    IsProbabilityMeasure
      (∑ k ∈ Finset.range n, ((a k : ℝ≥0∞) / M) • Measure.dirac (d k)) := by
  constructor
  simp [ENNReal.div_eq_inv_mul, ← Finset.mul_sum, ← Nat.cast_sum, ha, ENNReal.inv_mul_cancel, hM]

/-- **Laws with finitely many atoms are dense for the Lévy–Prokhorov distance.** On a
pseudo-metric space, if the sequence `d` has dense range, every probability measure is within any
`ε > 0` of a law carried by finitely many terms of `d`, with rational weights. -/
theorem exists_mem_ratAtomLaws_levyProkhorovDist_lt [PseudoMetricSpace Ω]
    [OpensMeasurableSpace Ω] {d : ℕ → Ω} (hd : DenseRange d) (P : ProbabilityMeasure Ω) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Q ∈ ratAtomLaws d, levyProkhorovDist (P : Measure Ω) (Q : Measure Ω) < ε := by
  classical
  set δ := ε / 3
  have hδ : 0 < δ := by positivity
  -- the cells: the balls of radius `δ` around the terms of `d`, made disjoint
  set C := disjointed fun k ↦ Metric.ball (d k) δ
  have hC (k : ℕ) : MeasurableSet (C k) := .disjointed (fun _ ↦ measurableSet_ball) k
  -- the first `N` cells carry all the mass but `δ`
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 <|
    (Measure.tendsto_measure_compl_biUnion_lt_ball (P : Measure Ω) hd hδ).eventually
      (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ))
  obtain ⟨N, hN⟩ : ∃ N, (P : Measure Ω) (⋃ k ∈ Finset.range N, C k)ᶜ < ENNReal.ofReal δ := by
    refine ⟨n + 1, ?_⟩
    rw [biUnion_range_succ_disjointed, partialSups_eq_biUnion_range]
    simpa only [Finset.mem_range] using hn (n + 1) n.le_succ
  -- the weights `a k / M`, rounded down, with `N / M ≤ δ`
  obtain ⟨M, hM⟩ := exists_nat_gt ((N : ℝ) / δ)
  have hM0 : (0 : ℝ) < M := (by positivity : (0 : ℝ) ≤ N / δ).trans_lt hM
  have hNM : ∑ _k ∈ Finset.range N, (1 : ℝ≥0∞) / M ≤ ENNReal.ofReal δ := by
    have h : (N : ℝ) / M ≤ δ := by
      rw [div_lt_iff₀ hδ] at hM
      rw [div_le_iff₀ hM0]
      linarith
    calc ∑ _k ∈ Finset.range N, (1 : ℝ≥0∞) / M = ENNReal.ofReal (N / M) := by
          rw [ENNReal.ofReal_div_of_pos hM0]; simp [div_eq_mul_inv]
    _ ≤ _ := ENNReal.ofReal_le_ofReal h
  set a : ℕ → ℕ := fun k ↦ ⌊(P : Measure Ω).real (C k) * M⌋₊
  have hsum_a : ∑ k ∈ Finset.range N, a k ≤ M :=
    sum_floor_measureReal_mul_le _ hC (disjoint_disjointed _) N M
  -- the law `Q`: the weight `a k / M` at `d k` for `k < N`, and the rest at `d N`
  set a' : ℕ → ℕ := fun k ↦ if k < N then a k else M - ∑ i ∈ Finset.range N, a i
  set Qm : Measure Ω := ∑ k ∈ Finset.range (N + 1), ((a' k : ℝ≥0∞) / M) • Measure.dirac (d k)
  have hQm (s : Set Ω) :
      Qm s = ∑ k ∈ Finset.range (N + 1), (a' k : ℝ≥0∞) / M * Measure.dirac (d k) s := by
    simp [Qm]
  have hQ : IsProbabilityMeasure Qm := by
    refine isProbabilityMeasure_sum_div_smul_dirac d (Nat.cast_pos.1 hM0).ne' ?_
    have h : ∑ k ∈ Finset.range N, a' k = ∑ k ∈ Finset.range N, a k :=
      Finset.sum_congr rfl fun k hk ↦ by simp [a', Finset.mem_range.1 hk]
    rw [Finset.sum_range_succ, h]
    simpa [a'] using Nat.add_sub_cancel' hsum_a
  refine ⟨⟨Qm, hQ⟩, mem_ratAtomLaws.2 ⟨N + 1, M, fun j ↦ a' j, ?_⟩, ?_⟩
  · exact (Fin.sum_univ_eq_sum_range (fun k ↦ ((a' k : ℝ≥0∞) / M) • Measure.dirac (d k))
      (N + 1)).symm
  -- the Lévy–Prokhorov distance is at most `2 δ`
  rw [coe_mk]
  refine (levyProkhorovDist_le_of_forall_le _ _ (by positivity : 0 ≤ 2 * δ)
    fun ε' B hε' hB ↦ ?_).trans_lt (by simp only [δ]; linarith)
  set T := Metric.thickening ε' B
  -- the mass of `B` in the cell `k` is at most the weight of `d k` if `d k ∈ T`, plus `1 / M`
  have hcell (k : ℕ) : (P : Measure Ω) (B ∩ C k) ≤
      (a k : ℝ≥0∞) / M * Measure.dirac (d k) T + 1 / M := by
    rcases (B ∩ C k).eq_empty_or_nonempty with h | ⟨ω, hωB, hωC⟩
    · simp [h]
    have hω : dist ω (d k) < δ := disjointed_subset _ k hωC
    rw [Measure.dirac_apply_of_mem (Metric.mem_thickening_iff.2
      ⟨ω, hωB, (dist_comm (d k) ω ▸ hω).trans (by linarith)⟩), mul_one]
    exact (measure_mono inter_subset_right).trans
      (measure_le_floor_measureReal_mul_div_add _ _ (Nat.cast_pos.1 hM0))
  have hQT : ∑ k ∈ Finset.range N, (a k : ℝ≥0∞) / M * Measure.dirac (d k) T ≤ Qm T := by
    rw [hQm, Finset.sum_range_succ]
    refine le_add_right (Finset.sum_le_sum fun k hk ↦ ?_)
    simp [a', Finset.mem_range.1 hk]
  have hB_sub : B ⊆ (⋃ k ∈ Finset.range N, B ∩ C k) ∪ (⋃ k ∈ Finset.range N, C k)ᶜ := by
    intro ω hω
    by_cases h : ω ∈ ⋃ k ∈ Finset.range N, C k
    · obtain ⟨k, hk, hωk⟩ := mem_iUnion₂.1 h
      exact Or.inl (mem_iUnion₂.2 ⟨k, hk, hω, hωk⟩)
    · exact Or.inr h
  calc (P : Measure Ω) B
  _ ≤ ∑ k ∈ Finset.range N, (P : Measure Ω) (B ∩ C k) + ENNReal.ofReal δ :=
    (measure_mono hB_sub).trans <| (measure_union_le _ _).trans <|
      add_le_add (measure_biUnion_finset_le _ _) hN.le
  _ ≤ ∑ k ∈ Finset.range N, ((a k : ℝ≥0∞) / M * Measure.dirac (d k) T + 1 / M) +
      ENNReal.ofReal δ := by
    gcongr with k
    exact hcell k
  _ ≤ Qm T + ENNReal.ofReal δ + ENNReal.ofReal δ := by
    rw [Finset.sum_add_distrib]
    gcongr
  _ = Qm T + ENNReal.ofReal (2 * δ) := by
    rw [add_assoc, ← ENNReal.ofReal_add hδ.le hδ.le, two_mul]
  _ ≤ Qm T + ENNReal.ofReal ε' := by
    gcongr

/-- **Laws with finitely many atoms are dense for convergence in distribution.** On a
pseudo-metrizable space whose σ-algebra contains the open sets, if the sequence `d` has dense
range, the laws carried by finitely many terms of `d`, with rational weights, are dense for the
topology of convergence in distribution. -/
theorem dense_ratAtomLaws {X : Type*} [TopologicalSpace X] [PseudoMetrizableSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {d : ℕ → X} (hd : DenseRange d) :
    Dense (ratAtomLaws d) := by
  let := pseudoMetrizableSpacePseudoMetric X
  have : SeparableSpace X := .of_denseRange d hd
  set e := LevyProkhorov.probabilityMeasureHomeomorph (Ω := X)
  have hdense : Dense (e '' ratAtomLaws d) := by
    refine Metric.dense_iff.2 fun x r hr ↦ ?_
    obtain ⟨Q, hQ, hPQ⟩ := exists_mem_ratAtomLaws_levyProkhorovDist_lt hd (e.symm x) hr
    exact ⟨e Q, by rwa [Metric.mem_ball, dist_comm], mem_image_of_mem _ hQ⟩
  rw [← e.symm_image_image (ratAtomLaws d)]
  exact e.symm.isDenseEmbedding.dense_image.2 hdense

end ProbabilityMeasure

variable {X : Type*} [TopologicalSpace X] [PseudoMetrizableSpace X] [SeparableSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

/-- **The topology of convergence in distribution on a separable space is separable**
[Par67, Chapter II, Section 6]. The laws carried by finitely many terms of a dense sequence, with
rational weights, form a countable dense set
(`MeasureTheory.ProbabilityMeasure.dense_ratAtomLaws`). -/
instance instSeparableSpaceProbabilityMeasure : SeparableSpace (ProbabilityMeasure X) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have : IsEmpty (ProbabilityMeasure X) := ⟨fun P ↦
      hX.elim (nonempty_of_isProbabilityMeasure (μ := (P : Measure X))).some⟩
    infer_instance
  obtain ⟨d, hd⟩ := exists_dense_seq X
  exact ⟨⟨_, ProbabilityMeasure.countable_ratAtomLaws d, ProbabilityMeasure.dense_ratAtomLaws hd⟩⟩

/-- **The topology of convergence in distribution on a separable space is second countable**
[Par67, Chapter II, Section 6]: it is separable and pseudo-metrizable. -/
instance instSecondCountableTopologyProbabilityMeasure :
    SecondCountableTopology (ProbabilityMeasure X) := by
  let := pseudoMetrizableSpacePseudoMetric (ProbabilityMeasure X)
  exact UniformSpace.secondCountable_of_separable _

end MeasureTheory
