/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Orthonormal coordinates on `ι → ℝ`

For an orthonormal basis `b` of a finite-dimensional real inner product space `E`, the map
`v ↦ b.repr.symm (WithLp.toLp 2 v)` from `ι → ℝ` to `E`, which sends coordinates in `b` to the
corresponding vector, is a measurable embedding and preserves the volume. This is the change of
variables that turns integrals over `E` into integrals over `ι → ℝ`.

## Main statements

* `OrthonormalBasis.measurePreserving_repr_symm_toLp`
* `OrthonormalBasis.measurableEmbedding_repr_symm_toLp`
-/

public section

open MeasureTheory

namespace OrthonormalBasis

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The map `v ↦ b.repr.symm (WithLp.toLp 2 v)` from `ι → ℝ` to `E` is volume preserving. -/
theorem measurePreserving_repr_symm_toLp [FiniteDimensional ℝ E] (b : OrthonormalBasis ι ℝ E) :
    MeasurePreserving (fun v : ι → ℝ ↦ b.repr.symm (WithLp.toLp 2 v)) :=
  b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp ι)

/-- The map `v ↦ b.repr.symm (WithLp.toLp 2 v)` from `ι → ℝ` to `E` is a measurable embedding. -/
theorem measurableEmbedding_repr_symm_toLp (b : OrthonormalBasis ι ℝ E) :
    MeasurableEmbedding (fun v : ι → ℝ ↦ b.repr.symm (WithLp.toLp 2 v)) :=
  b.repr.symm.toHomeomorph.measurableEmbedding.comp (MeasurableEquiv.toLp 2 _).measurableEmbedding

end OrthonormalBasis
