/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Probability.Process.Stopping

/-!
# Measurability of stopping times valued in `ℕ∞`

A stopping time of a filtration indexed by `ℕ` takes values in `WithTop ℕ`, which Mathlib equips
with its Borel σ-algebra, and `IsStoppingTime.measurable'` is measurability for that σ-algebra.
The same type seen as `ℕ∞` carries the discrete σ-algebra `⊤`; the two instances are not
syntactically equal. This file states measurability of such a stopping time for the discrete
σ-algebra of `ℕ∞`.

## Main statements

* `MeasureTheory.IsStoppingTime.measurable_enat`: a stopping time `τ : Ω → ℕ∞` of a filtration
  indexed by `ℕ` is measurable for the discrete σ-algebra of `ℕ∞`.
-/

public section

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {f : Filtration ℕ mΩ} {τ : Ω → ℕ∞}

/-- A stopping time `τ : Ω → ℕ∞` of a filtration indexed by `ℕ` is measurable for the discrete
σ-algebra of `ℕ∞`.

`IsStoppingTime.measurable'` gives measurability for the Borel σ-algebra of `WithTop ℕ`, a
different instance on the same type. -/
lemma measurable_enat (hτ : IsStoppingTime f τ) : Measurable τ :=
  -- the preimage of each (Borel-measurable) singleton is measurable
  measurable_to_countable' fun x ↦ hτ.measurable' (measurableSet_singleton (α := WithTop ℕ) x)

end MeasureTheory.IsStoppingTime
