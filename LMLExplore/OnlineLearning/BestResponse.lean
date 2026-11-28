/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.Learner.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Best-Response

Best-Response is the online learner on a set `Θ` that sees the loss `ℓ_t` of the current round
before playing, and plays the point mass at a selected model `br ℓ_t`. For a selection of
minimizers of the losses, it has no regret: this is the alternative player of the pure exploration
games of [DKM19, Lemma 3].

## Main definitions

* `LMLExplore.OnlineLearning.bestResponse br`: the online learner that plays the point mass at
  `br ℓ_t`, given the loss `ℓ_t` of the current round as context.

## Main statements

* `LMLExplore.OnlineLearning.hasRegretBound_bestResponse`: if the selected models minimize the
  losses against a model `θ`, the regret of Best-Response against `θ` is nonpositive.

## References

* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019, Lemma 3.
-/

public section

open Convexity

namespace LMLExplore.OnlineLearning

variable {Θ G : Type*}

/-- **Best-Response**, for a selection `br` of models, as an online learner whose context is the
loss of the current round: at round `t`, the point mass at the model `br ℓ_t` chosen for the loss
`ℓ_t` of the round. For a selection of minimizers of the losses, it has no regret
(`hasRegretBound_bestResponse`). -/
noncomputable def bestResponse (br : (Θ → ℝ) → Θ) : OnlineLearner (Θ → ℝ) G (StdSimplex ℝ Θ) where
  play _ _ ℓ := StdSimplex.single (br ℓ)

lemma play_bestResponse (br : (Θ → ℝ) → Θ) (t : ℕ) (h : Fin t → (Θ → ℝ) × G) (ℓ : Θ → ℝ) :
    (bestResponse br).play t h ℓ = StdSimplex.single (br ℓ) := (rfl)

/-- Best-Response plays the point mass at the model selected for the loss of the current round. -/
@[simp]
lemma run_bestResponse (br : (Θ → ℝ) → Θ) (c : ℕ → Θ → ℝ) (g : ℕ → G) (t : ℕ) :
    (bestResponse br).run c g t = StdSimplex.single (br (c t)) := by
  rw [OnlineLearner.run_def, play_bestResponse]

/-- **Best-Response has no regret**: for the expected losses `q ↦ E_{θ' ∼ q} ℓ θ'`, the regret of
Best-Response against the model `θ` is nonpositive on every sequence of losses `ℓ` such that the
model selected for the context of each round has a loss at most that of `θ`. With the losses as
contexts, this holds when the selected models minimize the losses against `θ`. -/
theorem hasRegretBound_bestResponse (br : (Θ → ℝ) → Θ) (θ : Θ) :
    (bestResponse (G := Θ → ℝ) br).HasRegretBound
      (fun ℓ q ↦ q.weights.sum fun θ' r ↦ r * ℓ θ') (fun c ℓ ↦ ℓ (br c) ≤ ℓ θ)
      {StdSimplex.single θ} fun _ _ _ _ ↦ 0 := by
  rw [OnlineLearner.hasRegretBound_iff]
  rintro c ℓ n hbr _ rfl
  refine regret_le_sum_of_le_add (ε := 0) (fun t ht ↦ ?_) |>.trans_eq (by simp)
  simpa [run_bestResponse, StdSimplex.weights_single, Finsupp.sum_single_index] using hbr t ht

end LMLExplore.OnlineLearning
