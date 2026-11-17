/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Constant bounds on the conditional expectation of a bounded real function

If an integrable real function `f` is at least `a` almost everywhere under a nonzero finite
measure `μ`, then its conditional expectation given a sub-σ-algebra `m` is at least `a` almost
everywhere, so an almost sure constant upper bound `μ[f | m] ≤ c` forces `a ≤ c`. Symmetrically,
if `f ≤ b` almost everywhere, an almost sure constant lower bound `c ≤ μ[f | m]` forces `c ≤ b`.
For instance, the conditional mean of a variable with values in `[0, 1]` cannot be bounded above
by a negative constant, nor below by a constant larger than `1`.

## Main statements

* `LMLExplore.le_of_ae_le_of_condExp_le`: if `a ≤ f` and `μ[f | m] ≤ c` almost everywhere, then
  `a ≤ c`.
* `LMLExplore.le_of_le_condExp_of_ae_le`: if `c ≤ μ[f | m]` and `f ≤ b` almost everywhere, then
  `c ≤ b`.
-/

public section

open MeasureTheory

namespace LMLExplore

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] [NeZero μ]
  {f : Ω → ℝ} {a b c : ℝ}

/-- If `a ≤ f` almost everywhere and the conditional expectation of `f` given a sub-σ-algebra `m`
is at most `c` almost everywhere, under a nonzero finite measure, then `a ≤ c`. -/
lemma le_of_ae_le_of_condExp_le (hm : m ≤ mΩ) (hf : Integrable f μ) (ha : ∀ᵐ ω ∂μ, a ≤ f ω)
    (hc : μ[f | m] ≤ᵐ[μ] fun _ ↦ c) : a ≤ c := by
  have h := condExp_mono (m := m) (integrable_const a) hf ha
  rw [condExp_const hm] at h
  obtain ⟨_, h1, h2⟩ := (h.and hc).exists
  exact h1.trans h2

/-- If the conditional expectation of `f` given a sub-σ-algebra `m` is at least `c` almost
everywhere and `f ≤ b` almost everywhere, under a nonzero finite measure, then `c ≤ b`. -/
lemma le_of_le_condExp_of_ae_le (hm : m ≤ mΩ) (hf : Integrable f μ)
    (hc : (fun _ ↦ c) ≤ᵐ[μ] μ[f | m]) (hb : ∀ᵐ ω ∂μ, f ω ≤ b) : c ≤ b := by
  have h := condExp_mono (m := m) hf (integrable_const b) hb
  rw [condExp_const hm] at h
  obtain ⟨_, h1, h2⟩ := (hc.and h).exists
  exact h1.trans h2

end LMLExplore
