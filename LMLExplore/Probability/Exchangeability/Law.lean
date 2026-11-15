/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Basic

/-!
# Integrals of the coordinates of an exchangeable sequence

Under an exchangeable law on `ℕ → α` (Tau Ceti's `TauCeti.Probability.ExchangeableLaw`), every
coordinate has the law of the first one, since swapping the coordinates `0` and `i` preserves the
law. In particular, a function of the coordinate `i` is integrable as soon as the same function of
the coordinate `0` is, and on an event invariant under that swap the two functions have the same
integral.

## Main statements

* `TauCeti.Probability.ExchangeableLaw.integrable_comp_eval`: a function of a coordinate of an
  exchangeable sequence is integrable when the same function of the first coordinate is.
* `TauCeti.Probability.ExchangeableLaw.setIntegral_comp_eval_eq_of_preimage_eq`: on an event
  invariant under the swap of the coordinates `0` and `i`, a function of the coordinate `i` has the
  same integral as the same function of the coordinate `0`.
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

/-- Under an exchangeable law, on an event invariant under the swap of the coordinates `0` and `i`,
a function of the coordinate `i` has the same integral as the same function of the coordinate
`0`. -/
theorem ExchangeableLaw.setIntegral_comp_eval_eq_of_preimage_eq [NormedSpace ℝ E]
    (hρ : ExchangeableLaw ρ) (f : α → E) {i : ℕ} {s : Set (ℕ → α)}
    (hs : permReindex (Equiv.swap 0 i) ⁻¹' s = s) :
    ∫ ω in s, f (ω i) ∂ρ = ∫ ω in s, f (ω 0) ∂ρ := by
  have hinv : Function.Involutive (permReindex (α := α) (Equiv.swap 0 i)) := fun ω ↦ by
    ext j
    simp
  have h := (hρ.measurePreserving_permReindex (Equiv.swap 0 i)).setIntegral_preimage_emb
    (MeasurableEquiv.ofInvolutive _ hinv (measurable_reindex _)).measurableEmbedding
    (fun ω ↦ f (ω 0)) s
  rw [hs] at h
  simpa using h

end TauCeti.Probability
