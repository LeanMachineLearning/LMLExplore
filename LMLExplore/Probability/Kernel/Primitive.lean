/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Kernel.Dobrushin
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import TauCeti.Probability.Kernel.Matrix

/-!
# Primitive Markov chains on finite spaces

A Markov kernel `κ` on a finite space is *primitive* when its transition matrix
`κ.toMatrix` is primitive in the sense of Mathlib's `Matrix.IsPrimitive`: some power of it has
only positive entries. Such a kernel has Dobrushin coefficient `δ(κ ^ m) < 1` for some `m > 0`,
hence is uniformly ergodic.

## Main statements

* `ProbabilityTheory.Kernel.exists_dobrushinCoeff_pow_lt_one_of_isPrimitive`: a Markov kernel on
  a finite space whose transition matrix is primitive has `δ(κ ^ m) < 1` for some `m > 0`.
* `ProbabilityTheory.Kernel.isUniformlyErgodic_of_isPrimitive`: such a kernel on a nonempty
  finite space is uniformly ergodic.
-/

public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} [IsMarkovKernel κ]
  [Fintype α] [DecidableEq α] [MeasurableSingletonClass α]

/-- **Primitive chains**: a Markov kernel on a finite space whose transition matrix is primitive
(some power has only positive entries) has `δ(κ ^ m) < 1` for some `m > 0`. -/
theorem exists_dobrushinCoeff_pow_lt_one_of_isPrimitive
    (h : (κ.toMatrix.map ((↑) : ℝ≥0 → ℝ)).IsPrimitive) :
    ∃ m > 0, dobrushinCoeff (κ ^ m) < 1 := by
  obtain ⟨m, hm, hpos⟩ := h.exists_pos_pow
  -- the entries of the `m`-th power of the matrix are the masses of `κ ^ m`
  have hmat : κ.toMatrix.map ((↑) : ℝ≥0 → ℝ) ^ m = (κ ^ m).toMatrix.map (↑) := by
    simpa [toMatrix_pow] using (map_pow (NNReal.toRealHom.mapMatrix (m := α)) κ.toMatrix m).symm
  have hpow (x y : α) : 0 < (κ ^ m) x {y} := by
    have hxy := hpos x y
    rw [hmat, Matrix.map_apply, NNReal.coe_pos, toMatrix_apply, ENNReal.toNNReal_pos_iff] at hxy
    exact hxy.1
  exact ⟨m, hm, dobrushinCoeff_lt_one_iff.2 fun x y ↦ ⟨x, hpow x x, hpow y x⟩⟩

/-- **Primitive chains are uniformly ergodic**: a Markov kernel on a nonempty finite space whose
transition matrix is primitive is uniformly ergodic. For a geometric rate of convergence, see
`exists_dobrushinCoeff_pow_lt_one_of_isPrimitive` and `tvDist_pow_apply_le_two_mul_pow_div`. -/
theorem isUniformlyErgodic_of_isPrimitive [Nonempty α]
    (h : (κ.toMatrix.map ((↑) : ℝ≥0 → ℝ)).IsPrimitive) :
    IsUniformlyErgodic κ :=
  let ⟨_, _, hm⟩ := exists_dobrushinCoeff_pow_lt_one_of_isPrimitive h
  isUniformlyErgodic_of_dobrushinCoeff_pow_lt_one hm

end ProbabilityTheory.Kernel
