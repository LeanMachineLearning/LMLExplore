/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import TauCeti.Probability.Process.PathLaw.Basic

/-!
# Events symmetric in the first coordinates of a sequence

For `n : ℕ`, the events on `ℕ → α` that are symmetric in the first `n + 1` coordinates form a
σ-algebra: that of the measurable events invariant under the swap of the coordinates `0` and `i`
for every `i ≤ n` (Tau Ceti's `TauCeti.Probability.permReindex`). These σ-algebras decrease in `n`.
Tau Ceti's `exchangeableSigma` is the σ-algebra of the events invariant under all finitely
supported permutations, which is contained in each of them.

## Main definitions

* `ProbabilityTheory.prefixExchangeableSigma α n`: the σ-algebra of the events on `ℕ → α` that are
  symmetric in the first `n + 1` coordinates.

## Main statements

* `ProbabilityTheory.measurableSet_prefixExchangeableSigma_iff`: its events are the measurable
  events invariant under the swaps of the coordinates `0` and `i ≤ n`.
* `ProbabilityTheory.prefixExchangeableSigma_anti`: it is antitone in `n`.
* `ProbabilityTheory.prefixExchangeableSigma_le`: it is contained in the product σ-algebra.
-/

public section

open MeasureTheory TauCeti.Probability

namespace ProbabilityTheory

/-- The σ-algebra of the measurable events on `ℕ → α` that are invariant under the swap of the
coordinates `0` and `i` for every `i ≤ n`. These swaps generate the permutations of the first
`n + 1` coordinates, so these are the events symmetric in the first `n + 1` coordinates. -/
@[instance_reducible]
def prefixExchangeableSigma (α : Type*) [MeasurableSpace α] (n : ℕ) : MeasurableSpace (ℕ → α) :=
  ⨅ i ≤ n, MeasurableSpace.invariants (permReindex (α := α) (Equiv.swap 0 i))

variable {α : Type*} [MeasurableSpace α]

/-- An event is symmetric in the first `n + 1` coordinates when it is measurable and invariant
under the swaps of the coordinates `0` and `i ≤ n`. -/
theorem measurableSet_prefixExchangeableSigma_iff {n : ℕ} {s : Set (ℕ → α)} :
    MeasurableSet[prefixExchangeableSigma α n] s ↔
      ∀ i ≤ n, MeasurableSet s ∧ permReindex (Equiv.swap 0 i) ⁻¹' s = s := by
  simp only [MeasurableSpace.measurableSet_iInf, MeasurableSpace.measurableSet_invariants]

variable (α) in
/-- Fewer events are symmetric in more coordinates. -/
theorem prefixExchangeableSigma_anti : Antitone (prefixExchangeableSigma α) := fun _ _ hnm ↦
  biInf_mono fun _ hi ↦ hi.trans hnm

variable (α) in
/-- The symmetric events are measurable. -/
theorem prefixExchangeableSigma_le (n : ℕ) : prefixExchangeableSigma α n ≤ MeasurableSpace.pi :=
  (iInf₂_le 0 (Nat.zero_le n)).trans (MeasurableSpace.invariants_le _)

end ProbabilityTheory
