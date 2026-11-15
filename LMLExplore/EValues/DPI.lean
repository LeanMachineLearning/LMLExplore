/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Statlib.EValues.DPI

/-!
# The maximal utility of e-variables

Companion lemmas for Statlib's `maxUtility P S U`, the maximal expected utility of an e-variable
for `S` under `P`.

## Main statements

* `ProbabilityTheory.maxUtility_zero_measure`: the maximal utility under the zero measure is `0`.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

/-- The maximal utility of e-variables under the zero measure vanishes. -/
@[simp]
lemma maxUtility_zero_measure {Ω : Type*} [MeasurableSpace Ω] (T : Set (Measure Ω))
    (U : Utility) : maxUtility 0 T U = 0 :=
  le_antisymm (iSup₂_le fun _ _ ↦ (eintegral_zero_measure _).le)
    (le_iSup₂_of_le _ (isEVar_fun_one T) (eintegral_zero_measure _).ge)

end ProbabilityTheory
