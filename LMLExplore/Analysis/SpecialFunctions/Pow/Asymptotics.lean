/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Powers near `0` from above

A complement to `Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`: for `t > 0`, the power
`x ↦ x ^ t` maps small positive numbers to small positive numbers. It reparametrizes statements
that hold for all small enough `δ > 0`, such as the asymptotic bounds of fixed-confidence
identification at small confidence levels, by the confidence level `δ ^ t`.

## Main statements

* `Real.tendsto_rpow_nhdsGT_zero`: for `t > 0`, `x ^ t → 0⁺` as `x → 0⁺`.
-/

public section

open Filter Set

open scoped Topology

namespace Real

/-- For `t > 0`, `x ^ t` tends to `0` from above as `x` does. -/
theorem tendsto_rpow_nhdsGT_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x : ℝ ↦ x ^ t) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x hx ↦
    rpow_pos_of_pos hx t⟩
  simpa [zero_rpow ht.ne'] using
    ((continuousAt_rpow_const 0 t (Or.inr ht.le)).tendsto).mono_left nhdsWithin_le_nhds

end Real
