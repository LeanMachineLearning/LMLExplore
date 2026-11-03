/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Linear functionals on `PiLp p (fun _ : ι ↦ R)` and their values at the basis vectors

Over a finite type `ι`, a linear map on `PiLp p (fun _ : ι ↦ R)` is determined by its values at
the basis vectors `PiLp.single p i 1`: it sends `x` to `∑ i, x i • L (PiLp.single p i 1)`.
Conversely, for weights `ℓ : ι → 𝕜`, the functional `∑ i, ℓ i • PiLp.proj p _ i` sends `x` to
`∑ i, ℓ i * x i` and takes the value `ℓ c` at `PiLp.single p c 1`. In online linear optimization
on the probability simplex, this identifies a linear loss with the vector of the losses of the
vertices.

## Main statements

* `PiLp.apply_eq_sum_smul_apply_single`: `L x = ∑ i, x i • L (PiLp.single p i 1)`.
* `PiLp.sum_smul_proj_apply`, `PiLp.sum_smul_proj_apply_single`: the functional
  `∑ i, ℓ i • PiLp.proj p _ i` sends `x` to `∑ i, ℓ i * x i` and `PiLp.single p c 1` to `ℓ c`.
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

variable {𝕜 : Type*} [NormedCommRing 𝕜]

/-- The functional `∑ i, ℓ i • PiLp.proj p _ i` on `PiLp p (fun _ : ι ↦ 𝕜)` sends `x` to
`∑ i, ℓ i * x i`. -/
theorem sum_smul_proj_apply (ℓ : ι → 𝕜) (x : PiLp p fun _ : ι ↦ 𝕜) :
    (∑ i, ℓ i • proj (𝕜 := 𝕜) p (fun _ : ι ↦ 𝕜) i) x = ∑ i, ℓ i * x i := by
  simp

/-- The functional `∑ i, ℓ i • PiLp.proj p _ i` on `PiLp p (fun _ : ι ↦ 𝕜)` takes the value `ℓ c`
at the basis vector `PiLp.single p c 1`. -/
theorem sum_smul_proj_apply_single [DecidableEq ι] (ℓ : ι → 𝕜) (c : ι) :
    (∑ i, ℓ i • proj (𝕜 := 𝕜) p (fun _ : ι ↦ 𝕜) i) (single p c 1) = ℓ c := by
  simp [single_apply]

end PiLp
