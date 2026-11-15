/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Basic

/-!
# Integrability of the coordinates of an exchangeable sequence

Under an exchangeable law on `ℕ → α` (Tau Ceti's `TauCeti.Probability.ExchangeableLaw`), every
coordinate has the law of the first one, since swapping the coordinates `0` and `i` preserves the
law. In particular, a function of the coordinate `i` is integrable as soon as the same function of
the coordinate `0` is.

## Main statements

* `TauCeti.Probability.ExchangeableLaw.integrable_comp_eval`: a function of a coordinate of an
  exchangeable sequence is integrable when the same function of the first coordinate is.
-/

public section

open MeasureTheory

namespace TauCeti.Probability

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {ρ : Measure (ℕ → α)}

/-- Under an exchangeable law, a function of the coordinate `i` is integrable when the same
function of the coordinate `0` is. -/
theorem ExchangeableLaw.integrable_comp_eval (hρ : ExchangeableLaw ρ) {f : α → E}
    (hf : Integrable (fun ω ↦ f (ω 0)) ρ) (i : ℕ) : Integrable (fun ω ↦ f (ω i)) ρ := by
  simpa [Function.comp_def] using
    ((hρ.measurePreserving_permReindex (Equiv.swap 0 i)).integrable_comp
      hf.aestronglyMeasurable).2 hf

end TauCeti.Probability
