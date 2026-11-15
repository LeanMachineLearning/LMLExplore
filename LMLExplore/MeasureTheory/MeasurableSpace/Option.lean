/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import TauCeti.MeasureTheory.MeasurableSpace.Option

/-!
# Measurable singletons of optional values

Tau Ceti's measurable structure on `Option X` (`Option.instMeasurableSpace`) makes `none` a
measurable singleton and `some` a measurable embedding. Hence `Option X` has measurable singletons
whenever `X` does. In particular, for a finite type `X` with measurable singletons, every subset of
`Option X` is measurable, so that a finite set of random outcomes, one of which may be a
distinguished value `none`, can serve as the action set of a randomized algorithm.
-/

public section

namespace Option

variable {X : Type*} [MeasurableSpace X]

/-- Optional values have measurable singletons when the present values do. -/
instance instMeasurableSingletonClass [MeasurableSingletonClass X] :
    MeasurableSingletonClass (Option X) where
  measurableSet_singleton o := by
    rcases o with _ | x
    · exact measurableSet_none
    · rw [← Set.image_singleton]
      exact measurableEmbedding_some.measurableSet_image' (measurableSet_singleton x)

end Option
