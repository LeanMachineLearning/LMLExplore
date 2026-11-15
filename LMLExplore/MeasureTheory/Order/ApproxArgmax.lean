/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Order.ConditionallyCompleteLattice.Group
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable approximate maximizers over countable index types

The supremum of a family of reals indexed by an infinite type need not be attained, but for every
`ε > 0` some index comes within `ε` of it. Over a countable index type such an index can be chosen
measurably in the family: for `f : ℕ → ℝ`, the least index `i` with `f i > (⨆ j, f j) - ε` is a
measurable function `approxArgmaxNat ε` of `f`, for the product σ-algebra on `ℕ → ℝ`. A countable
index type `ι` is enumerated by a surjection `ℕ → ι`, along which the least such index gives the
measurable `ε`-maximizer `approxArgmax ε : (ι → ℝ) → ι`.

These are the infinite counterparts of LML's `argmax` on a finite index type, which attains the
maximum. In dynamic programming over countably many actions, they give measurable `ε`-greedy
policies, whose values come within `ε` of the optimality operator at every state.

When the family is not bounded above, `⨆ j, f j = 0` in `ℝ`, and the statements still hold: some
value then exceeds every bound, in particular `-ε` (`exists_iSup_sub_lt`).

## Main definitions

* `LMLExplore.approxArgmaxNat ε f`: the least index `i : ℕ` with `(⨆ j, f j) - ε < f i`, for
  `ε > 0`.
* `LMLExplore.approxArgmax ε f`: for a countable `ι`, an index `i : ι` with
  `(⨆ j, f j) - ε < f i`, for `ε > 0`.

## Main statements

* `LMLExplore.isLeast_approxArgmaxNat`: `approxArgmaxNat ε f` is the least index whose value
  exceeds `(⨆ j, f j) - ε`.
* `LMLExplore.measurable_approxArgmaxNat`, `LMLExplore.measurable_approxArgmax`: the approximate
  maximizers are measurable functions of the family.
* `LMLExplore.iSup_sub_lt_apply_approxArgmax`: the value at `approxArgmax ε f` exceeds
  `(⨆ j, f j) - ε`.
-/

public section

open MeasureTheory Set

namespace LMLExplore

variable {ε : ℝ}

/-! ### Approximate maximizers over `ℕ` -/

/-- The least index `i` with `f i > (⨆ j, f j) - ε`, for `ε > 0` (`0` for `ε ≤ 0`). -/
noncomputable def approxArgmaxNat (ε : ℝ) (f : ℕ → ℝ) : ℕ :=
  if hε : 0 < ε then Nat.find (exists_iSup_sub_lt f hε) else 0

lemma approxArgmaxNat_of_pos (hε : 0 < ε) (f : ℕ → ℝ) :
    approxArgmaxNat ε f = Nat.find (exists_iSup_sub_lt f hε) := by
  simp only [approxArgmaxNat, hε, ↓reduceDIte]

lemma approxArgmaxNat_of_nonpos (hε : ε ≤ 0) (f : ℕ → ℝ) : approxArgmaxNat ε f = 0 := by
  simp only [approxArgmaxNat, hε.not_gt, ↓reduceDIte]

/-- For `ε > 0`, the value of `f` at `approxArgmaxNat ε f` exceeds `(⨆ j, f j) - ε`. -/
theorem iSup_sub_lt_apply_approxArgmaxNat (hε : 0 < ε) (f : ℕ → ℝ) :
    (⨆ j, f j) - ε < f (approxArgmaxNat ε f) := by
  rw [approxArgmaxNat_of_pos hε]
  exact Nat.find_spec (exists_iSup_sub_lt f hε)

/-- `approxArgmaxNat ε f` is at most every index whose value exceeds `(⨆ j, f j) - ε`. -/
theorem approxArgmaxNat_le {f : ℕ → ℝ} {i : ℕ} (hi : (⨆ j, f j) - ε < f i) :
    approxArgmaxNat ε f ≤ i := by
  by_cases hε : 0 < ε
  · rw [approxArgmaxNat_of_pos hε]
    exact Nat.find_min' _ hi
  · rw [approxArgmaxNat_of_nonpos (not_lt.1 hε)]
    exact i.zero_le

/-- For `ε > 0`, `approxArgmaxNat ε f` is the least index whose value exceeds
`(⨆ j, f j) - ε`. -/
theorem isLeast_approxArgmaxNat (hε : 0 < ε) (f : ℕ → ℝ) :
    IsLeast {i | (⨆ j, f j) - ε < f i} (approxArgmaxNat ε f) :=
  ⟨iSup_sub_lt_apply_approxArgmaxNat hε f, fun _ hi ↦ approxArgmaxNat_le hi⟩

/-- The least index within `ε` of the supremum is a measurable function of the family, for the
product σ-algebra on `ℕ → ℝ`. -/
@[fun_prop]
theorem measurable_approxArgmaxNat (ε : ℝ) : Measurable (approxArgmaxNat ε) := by
  by_cases hε : 0 < ε
  · rw [show approxArgmaxNat ε = _ from funext (approxArgmaxNat_of_pos hε)]
    exact measurable_find _ fun k ↦ measurableSet_lt
      ((Measurable.iSup fun j ↦ measurable_pi_apply j).sub_const ε) (measurable_pi_apply k)
  · rw [show approxArgmaxNat ε = _ from funext (approxArgmaxNat_of_nonpos (not_lt.1 hε))]
    exact measurable_const

/-! ### Approximate maximizers over a countable type -/

variable {ι : Type*} [Countable ι] [Nonempty ι]

/-- For a countable `ι` and `ε > 0`, an index `i` with `f i > (⨆ j, f j) - ε`: the first one along
a fixed enumeration `ℕ → ι` of `ι`. -/
noncomputable def approxArgmax (ε : ℝ) (f : ι → ℝ) : ι :=
  (exists_surjective_nat ι).choose (approxArgmaxNat ε (f ∘ (exists_surjective_nat ι).choose))

/-- For `ε > 0`, the value of `f` at `approxArgmax ε f` exceeds `(⨆ j, f j) - ε`. -/
theorem iSup_sub_lt_apply_approxArgmax (hε : 0 < ε) (f : ι → ℝ) :
    (⨆ j, f j) - ε < f (approxArgmax ε f) := by
  have h := iSup_sub_lt_apply_approxArgmaxNat hε (f ∘ (exists_surjective_nat ι).choose)
  rwa [Function.comp_def, (exists_surjective_nat ι).choose_spec.iSup_comp f] at h

/-- The approximate maximizer over a countable type is a measurable function of the family, for
the product σ-algebra on `ι → ℝ` and every σ-algebra on `ι`. -/
@[fun_prop]
theorem measurable_approxArgmax [MeasurableSpace ι] (ε : ℝ) :
    Measurable (approxArgmax ε : (ι → ℝ) → ι) :=
  measurable_from_nat.comp <| (measurable_approxArgmaxNat ε).comp <|
    Measurable.of_eval fun _ ↦ measurable_pi_apply _

end LMLExplore
