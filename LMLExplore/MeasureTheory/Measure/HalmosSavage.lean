/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import LMLExplore.MeasureTheory.Function.EssSupFamily

/-!
# The Halmos–Savage lemma

A family of measures `ν i` dominated by a σ-finite measure `μ` has a countable
subfamily with the same null measurable sets: a measurable set that is null for every member of
the subfamily is null for every member of the family [HS49, Lemma 7]. The members of the
subfamily, summed or mixed, give one measure whose null sets are those of the whole family, which
may be uncountable. This is how a dominated null of statistical models is replaced by a countable
one, or by a single law.

The densities `(ν i).rnDeriv μ` are dominated `μ`-almost everywhere by the supremum of a sequence
of them (`MeasureTheory.exists_seq_forall_ae_le_iSup`), and a measurable set null for the members
of that sequence is a set on which their densities, hence all the densities, vanish.

## Main statements

* `MeasureTheory.Measure.exists_countable_forall_measure_eq_zero`: the Halmos–Savage lemma.

## References

* [HS49] P. R. Halmos and L. J. Savage, *Application of the Radon–Nikodym theorem to the theory of
  sufficient statistics*, Ann. Math. Statist. 20 (1949), 225–241, Lemma 7.
-/

public section

open Set

namespace MeasureTheory.Measure

variable {α ι : Type*} {mα : MeasurableSpace α} {μ : Measure α} {ν : ι → Measure α}

/-- **The Halmos–Savage lemma** [HS49, Lemma 7]. A family of measures absolutely continuous with
respect to a σ-finite measure has a countable subfamily with the same null measurable sets: a
measurable set that is null for every member of the subfamily is null for every member of the
family. -/
theorem exists_countable_forall_measure_eq_zero [SigmaFinite μ] (hν : ∀ i, ν i ≪ μ) :
    ∃ s : Set ι, s.Countable ∧ ∀ A, MeasurableSet A → (∀ i ∈ s, ν i A = 0) → ∀ i, ν i A = 0 := by
  -- each member is s-finite, being absolutely continuous with respect to `μ`
  have (i : ι) : SFinite (ν i) := sfinite_of_absolutelyContinuous (hν i)
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨∅, countable_empty, fun _ _ _ i ↦ isEmptyElim i⟩
  -- a sequence of densities whose supremum dominates every density almost everywhere
  obtain ⟨s, hs⟩ := exists_seq_forall_ae_le_iSup (μ := μ) (f := fun i ↦ (ν i).rnDeriv μ)
    fun i ↦ (measurable_rnDeriv _ _).aemeasurable
  -- a measurable set is null for a member exactly when its density vanishes almost everywhere on it
  have h_null (i : ι) {A : Set α} (hA : MeasurableSet A) :
      ν i A = 0 ↔ ∀ᵐ x ∂μ, x ∈ A → (ν i).rnDeriv μ x = 0 := by
    rw [← setLIntegral_rnDeriv' (hν i) hA, setLIntegral_eq_zero_iff hA (measurable_rnDeriv _ _)]
  refine ⟨range s, countable_range s, fun A hA h i ↦ (h_null i hA).2 ?_⟩
  filter_upwards [hs i, ae_all_iff.2 fun n ↦ (h_null (s n) hA).1 (h _ (mem_range_self n))]
    with x hx hxs hxA
  exact le_antisymm (hx.trans (iSup_le fun n ↦ (hxs n hxA).le)) zero_le

end MeasureTheory.Measure
