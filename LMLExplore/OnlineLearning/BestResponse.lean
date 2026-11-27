/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Best-Response

Best-Response is the online learner on a set `Θ` that sees the loss `ℓ_t` of the current round
before playing, and plays the point mass at a selected model `br ℓ_t`. For a selection of
minimizers of the losses, it has no regret: this is the alternative player of the pure exploration
games of [DKM19, Lemma 3].

## Main definitions

* `LMLExplore.OnlineLearning.bestResponse br t ℓ`: the point mass at `br (ℓ t)`, played at round
  `t` given the losses `ℓ` of the rounds up to and including `t`.

## Main statements

* `LMLExplore.OnlineLearning.sum_sum_bestResponse_le`: if the selected models minimize the losses
  against a model `θ`, the cumulative expected loss of Best-Response is at most that of `θ`.

## References

* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019, Lemma 3.
-/

public section

open Convexity Finset

namespace LMLExplore.OnlineLearning

variable {Θ : Type*}

/-- **Best-Response**, for a selection `br` of models: at round `t`, the point mass at the model
`br ℓ_t` chosen for the loss `ℓ_t` of the current round. For a selection of minimizers of the
losses, it has no regret (`sum_sum_bestResponse_le`). -/
noncomputable def bestResponse (br : (Θ → ℝ) → Θ) (t : ℕ) (ℓ : Fin (t + 1) → Θ → ℝ) :
    StdSimplex ℝ Θ :=
  StdSimplex.single (br (ℓ (Fin.last t)))

lemma bestResponse_def (br : (Θ → ℝ) → Θ) (t : ℕ) (ℓ : Fin (t + 1) → Θ → ℝ) :
    bestResponse br t ℓ = StdSimplex.single (br (ℓ (Fin.last t))) := (rfl)

/-- The expected loss of Best-Response is the loss of the selected model. -/
@[simp]
lemma bestResponse_weights_sum_mul (br : (Θ → ℝ) → Θ) (t : ℕ) (ℓ : Fin (t + 1) → Θ → ℝ)
    (f : Θ → ℝ) :
    ((bestResponse br t ℓ).weights.sum fun θ r ↦ r * f θ) = f (br (ℓ (Fin.last t))) := by
  rw [bestResponse_def, StdSimplex.weights_single, Finsupp.sum_single_index (zero_mul _), one_mul]

/-- **Best-Response has no regret**: on a sequence of losses `ℓ`, if the selected models minimize
the losses `ℓ s` against the model `θ` at the rounds `s < t`, then
`∑_{s < t} E_{θ' ∼ q_s} ℓ s θ' ≤ ∑_{s < t} ℓ s θ`. -/
theorem sum_sum_bestResponse_le (br : (Θ → ℝ) → Θ) (ℓ : ℕ → Θ → ℝ) {t : ℕ} {θ : Θ}
    (hbr : ∀ s < t, ℓ s (br (ℓ s)) ≤ ℓ s θ) :
    ∑ s ∈ range t, ((bestResponse br s fun i ↦ ℓ i).weights.sum fun θ' r ↦ r * ℓ s θ') ≤
      ∑ s ∈ range t, ℓ s θ := by
  refine Finset.sum_le_sum fun s hs ↦ ?_
  rw [bestResponse_weights_sum_mul, Fin.val_last]
  exact hbr s (Finset.mem_range.1 hs)

end LMLExplore.OnlineLearning
