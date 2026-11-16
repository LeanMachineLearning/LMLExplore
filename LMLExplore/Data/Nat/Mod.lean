/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.Nat.Init
import Mathlib.Tactic.SplitIfs

/-!
# Shifting residues modulo `K`

For residues `h` and `x` modulo `K` and a shift `u ≤ K`, the shift `(h + u) % K` is `x` exactly
when `h` is the shift `(x + K - u) % K` of `x` by `-u`. The cycle lemma of the lower bound for
e-BH on running maxima (`LMLExplore.EValues.MultipleTesting.RunningMaxima.LowerBound`) uses it to
count shifted heights.

## Main statements

* `Nat.add_mod_eq_iff`: `(h + u) % K = x ↔ h = (x + K - u) % K` for `h, x < K` and `u ≤ K`.

## Implementation notes

The statement and its proof are adapted from the helper `add_mod_eq_iff` of
`EValuesResearch/Results/RunningMaxima.lean` (commit `ffba78a`) in the paper project
`RemyDegenne/evalues_research`, with its hypothesis `u < K` weakened to `u ≤ K`.
-/

public section

namespace Nat

/-- Shifting residues modulo `K`: for `h, x < K` and `u ≤ K`, `(h + u) % K = x` exactly when
`h = (x + K - u) % K`. -/
theorem add_mod_eq_iff {K h u x : ℕ} (hh : h < K) (hu : u ≤ K) (hx : x < K) :
    (h + u) % K = x ↔ h = (x + K - u) % K := by
  have e1 : (h + u) % K = if h + u < K then h + u else h + u - K := by
    split_ifs with h'
    · exact Nat.mod_eq_of_lt h'
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have e2 : (x + K - u) % K = if x < u then x + K - u else x - u := by
    split_ifs with h'
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  rw [e1, e2]
  split_ifs <;> omega

end Nat
