/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Linear maps on `PiLp p (fun _ : ι ↦ R)` and their values at the basis vectors

Over a finite type `ι`, a linear map on `PiLp p (fun _ : ι ↦ R)` is determined by its values at
the basis vectors `PiLp.single p i 1`: it sends `x` to `∑ i, x i • L (PiLp.single p i 1)`.
In online linear optimization on the probability simplex, this identifies a linear loss with the
vector of the losses of the vertices.

## Main statements

* `PiLp.apply_eq_sum_smul_apply_single`: `L x = ∑ i, x i • L (PiLp.single p i 1)`.
-/

public section

open Finset WithLp
open scoped ENNReal

namespace PiLp

variable {ι : Type*} [Fintype ι] (p : ℝ≥0∞)

/-- A linear map on `PiLp p (fun _ : ι ↦ R)` is determined by its values at the basis vectors:
`L x = ∑ i, x i • L (PiLp.single p i 1)`. -/
theorem apply_eq_sum_smul_apply_single [DecidableEq ι] {R M F : Type*} [Ring R]
    [AddCommMonoid M] [Module R M] [FunLike F (PiLp p fun _ : ι ↦ R) M] [LinearMapClass F R _ M]
    (L : F) (x : PiLp p fun _ : ι ↦ R) :
    L x = ∑ i, x i • L (single p i 1) := by
  conv_lhs => rw [← (basisFun p R ι).sum_repr x]
  simp [map_sum, map_smul, basisFun_apply]

end PiLp
