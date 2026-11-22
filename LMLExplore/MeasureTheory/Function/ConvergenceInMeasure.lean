/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Convergence in measure along a countably generated filter

Mathlib characterizes convergence in measure of a sequence by subsequences
(`MeasureTheory.exists_seq_tendstoInMeasure_atTop_iff`): under a finite measure, a sequence
converges in measure exactly when every subsequence has a further subsequence that converges almost
everywhere. This file extends the criterion to families indexed by a countably generated filter,
such as `𝓝[>] 1` for a family indexed by a real parameter, through the sequences that tend to the
filter. It is the tool to pass convergence in measure through continuous operations: along an
almost everywhere convergent subsequence, the operation is applied pointwise.

## Main statements

* `MeasureTheory.tendstoInMeasure_iff_forall_seq_tendstoInMeasure`: convergence in measure along a
  countably generated filter is convergence in measure along every sequence that tends to it.
* `MeasureTheory.tendstoInMeasure_of_forall_seq_exists_subseq_tendsto_ae`: under a finite measure,
  a family that is eventually almost everywhere strongly measurable converges in measure when
  every sequence of indices tending to the filter has a subsequence along which the family
  converges almost everywhere.
-/

public section

open Filter
open scoped Topology

namespace MeasureTheory

variable {α ι E : Type*} {m : MeasurableSpace α} {μ : Measure α} {l : Filter ι}
  {f : ι → α → E} {g : α → E}

/-- Convergence in measure along a countably generated filter is convergence in measure along
every sequence of indices that tends to the filter. -/
theorem tendstoInMeasure_iff_forall_seq_tendstoInMeasure [EDist E] [l.IsCountablyGenerated] :
    TendstoInMeasure μ f l g ↔
      ∀ u : ℕ → ι, Tendsto u atTop l → TendstoInMeasure μ (fun n ↦ f (u n)) atTop g :=
  ⟨fun h _ hu ↦ h.comp hu,
    fun h ε hε ↦ tendsto_iff_seq_tendsto.2 fun u hu ↦ h u hu ε hε⟩

/-- **Convergence in measure from almost everywhere convergent subsequences.** Under a finite
measure, a family indexed by a countably generated filter, almost everywhere strongly measurable
for indices eventually in the filter, converges in measure to `g` when every sequence of indices
tending to the filter has a subsequence along which the family converges to `g` almost
everywhere. -/
theorem tendstoInMeasure_of_forall_seq_exists_subseq_tendsto_ae [PseudoEMetricSpace E]
    [IsFiniteMeasure μ] [l.IsCountablyGenerated]
    (hf : ∀ᶠ i in l, AEStronglyMeasurable (f i) μ)
    (h : ∀ u : ℕ → ι, Tendsto u atTop l → ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun n ↦ f (u (ns n)) x) atTop (𝓝 (g x))) :
    TendstoInMeasure μ f l g := by
  refine tendstoInMeasure_iff_forall_seq_tendstoInMeasure.2 fun u hu ↦ ?_
  -- shift the sequence so that every one of its terms is almost everywhere strongly measurable
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually hf)
  have hv : TendstoInMeasure μ (fun n ↦ f (u (n + N))) atTop g := by
    refine (exists_seq_tendstoInMeasure_atTop_iff fun n ↦ hN _ (Nat.le_add_left N n)).2
      fun ns hns ↦ ?_
    exact h _ ((hu.comp (tendsto_add_atTop_nat N)).comp hns.tendsto_atTop)
  exact fun ε hε ↦ (tendsto_add_atTop_iff_nat N).1 (hv ε hε)

end MeasureTheory
