/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Convex.FenchelMoreau

/-!
# The regret–reward duality

In online linear optimization, a learner plays `x t` and suffers the linear loss of `y t` at each
round. Its *reward* after `n` rounds is `-∑ t < n, y t (x t)`: in the coin-betting game, it is
the money won. The **regret–reward duality** [Ora, Theorem 13.5] says that a lower bound on the
reward by a function `φ` of the negated sum of the losses is the same as an upper bound on the
regret against every comparator `u` by the Fenchel conjugate `φ⋆ u`:
`-∑ t < n, y t (x t) ≥ φ (-∑ t < n, y t)` if and only if `∑ t < n, y t (x t - u) ≤ φ⋆ u` for
every `u`. Parameter-free algorithms are designed and analysed through it: a bettor that keeps a
large wealth on every sequence of coins has a small regret against every comparator, with no
learning rate to tune.

The plays lie in a real vector space `E` and the losses in a real vector space `F`, paired by a
bilinear map `B : F →ₗ[ℝ] E →ₗ[ℝ] ℝ`. The conjugate of `φ : F → EReal` is Tau Ceti's
`TauCeti.fenchelConjugate B φ u = ⨆ θ, (B θ u - φ θ)`. The two pairings of online learning are:
* the losses in the dual `E →L[ℝ] ℝ` of a normed space, with `B = topDualPairing ℝ E`;
* one-dimensional losses and plays, with `B = LinearMap.mul ℝ ℝ`, where the conjugate of a wealth
  bound `θ ↦ β * exp (θ ^ 2 / (2 * α))` is bounded by
  `LMLExplore.fenchelConjugate_mul_exp_sq_div_le`.

The implication from the reward to the regret holds for every `φ`, and is the Fenchel–Young
inequality at `θ = -∑ t < n, y t`. The converse needs `φ = φ⋆⋆`, which is the Fenchel–Moreau
theorem `TauCeti.fenchelConjugate_flip_fenchelConjugate_eq`: `φ` has a convex epigraph, is lower
semicontinuous and never takes the value `⊥`, and the pairing represents every continuous linear
functional on `F`. For the dual of a normed space, the last condition is reflexivity, which holds
in finite dimension (`NormedSpace.surjective_inclusionInDoubleDual`).

## Main statements

* `LMLExplore.OnlineLearning.sum_apply_sub_le_fenchelConjugate`: a reward bound gives a regret
  bound against every comparator.
* `LMLExplore.OnlineLearning.forall_sum_apply_sub_le_fenchelConjugate_iff`: the regret–reward
  duality, for a pairing that represents the continuous dual of the losses.
* `LMLExplore.OnlineLearning.forall_sum_apply_sub_le_fenchelConjugate_topDualPairing_iff`: the
  regret–reward duality for losses in the dual of a reflexive normed space [Ora, Theorem 13.5].

## References

* F. Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*,
  arXiv:1912.13213v10, Theorem 13.5 [Ora].
* H. B. McMahan and F. Orabona, *Unconstrained online linear learning in Hilbert spaces: minimax
  algorithms and normal approximations*, COLT 2014, where the duality is first proved.
-/

public section

open Finset TauCeti

namespace LMLExplore.OnlineLearning

section Pairing

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {φ : F → EReal} {y : ℕ → F} {x : ℕ → E} {n : ℕ}

/-- **From reward to regret** [Ora, Theorem 13.5]: if the reward `-∑ t < n, B (y t) (x t)` of the
plays `x` on the losses `y` is at least `φ (-∑ t < n, y t)`, then the regret against every
comparator `u` is at most the Fenchel conjugate `φ⋆ u`. No assumption on `φ` is needed. -/
theorem sum_apply_sub_le_fenchelConjugate (B : F →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (h : φ (-∑ t ∈ range n, y t) ≤ ((-∑ t ∈ range n, B (y t) (x t) : ℝ) : EReal)) (u : E) :
    ((∑ t ∈ range n, B (y t) (x t - u) : ℝ) : EReal) ≤ fenchelConjugate B φ u := by
  have hsum : ∑ t ∈ range n, B (y t) (x t - u) =
      B (-∑ t ∈ range n, y t) u - -∑ t ∈ range n, B (y t) (x t) := by
    simp only [map_sub, map_neg, map_sum, LinearMap.neg_apply, LinearMap.sum_apply,
      sum_sub_distrib]
    ring
  rw [hsum, EReal.coe_sub]
  exact (EReal.sub_le_sub le_rfl h).trans (sub_le_fenchelConjugate B φ _ u)

/-- **The regret–reward duality** [Ora, Theorem 13.5]. Let the pairing `B` represent every
continuous linear functional on the locally convex space `F` of losses, and let `φ : F → EReal`
have a convex epigraph, be lower semicontinuous and never take the value `⊥`. Then the regret of
the plays `x` on the losses `y` is at most `φ⋆ u` against every comparator `u` if and only if their
reward `-∑ t < n, B (y t) (x t)` is at least `φ (-∑ t < n, y t)`. -/
theorem forall_sum_apply_sub_le_fenchelConjugate_iff [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    (B : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀ ℓ : F →L[ℝ] ℝ, ∃ u, ∀ θ, B θ u = ℓ θ)
    (hφ : Convex ℝ {p : F × ℝ | φ p.1 ≤ p.2}) (hlsc : LowerSemicontinuous φ)
    (hbot : ∀ θ, φ θ ≠ ⊥) :
    (∀ u, ((∑ t ∈ range n, B (y t) (x t - u) : ℝ) : EReal) ≤ fenchelConjugate B φ u) ↔
      φ (-∑ t ∈ range n, y t) ≤ ((-∑ t ∈ range n, B (y t) (x t) : ℝ) : EReal) := by
  refine ⟨fun h ↦ ?_, sum_apply_sub_le_fenchelConjugate B⟩
  -- By Fenchel–Moreau, `φ = φ⋆⋆`, and each term `B θ u - φ⋆ u` of `φ⋆⋆ θ` at
  -- `θ = -∑ t < n, y t` is at most `B θ u` minus the regret against `u`, which is the reward.
  rw [← fenchelConjugate_flip_fenchelConjugate_eq hB hφ hlsc hbot]
  refine fenchelConjugate_le _ fun u ↦ ?_
  have hsum : -∑ t ∈ range n, B (y t) (x t) =
      B.flip u (-∑ t ∈ range n, y t) - ∑ t ∈ range n, B (y t) (x t - u) := by
    simp only [map_sub, map_neg, map_sum, sum_sub_distrib, LinearMap.flip_apply]
    ring
  rw [hsum, EReal.coe_sub]
  exact EReal.sub_le_sub le_rfl (h u)

end Pairing

/-- **The regret–reward duality for losses in the dual of a normed space** [Ora, Theorem 13.5].
Let `E` be a reflexive real normed space (for instance a finite-dimensional one,
`NormedSpace.surjective_inclusionInDoubleDual`), and let `φ` on the dual `E →L[ℝ] ℝ` have a convex
epigraph, be lower semicontinuous and never take the value `⊥`. Then the regret
`∑ t < n, y t (x t - u)` is at most the conjugate `φ⋆ u = ⨆ θ, (θ u - φ θ)` for every `u` if and
only if the reward `-∑ t < n, y t (x t)` is at least `φ (-∑ t < n, y t)`. -/
theorem forall_sum_apply_sub_le_fenchelConjugate_topDualPairing_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    {φ : (E →L[ℝ] ℝ) → EReal} (hφ : Convex ℝ {p : (E →L[ℝ] ℝ) × ℝ | φ p.1 ≤ p.2})
    (hlsc : LowerSemicontinuous φ) (hbot : ∀ θ, φ θ ≠ ⊥) {y : ℕ → E →L[ℝ] ℝ} {x : ℕ → E}
    {n : ℕ} :
    (∀ u, ((∑ t ∈ range n, y t (x t - u) : ℝ) : EReal) ≤
        fenchelConjugate (topDualPairing ℝ E) φ u) ↔
      φ (-∑ t ∈ range n, y t) ≤ ((-∑ t ∈ range n, y t (x t) : ℝ) : EReal) := by
  have hB (ℓ : (E →L[ℝ] ℝ) →L[ℝ] ℝ) : ∃ u, ∀ θ, topDualPairing ℝ E θ u = ℓ θ :=
    (hE ℓ).imp fun u hu θ ↦ by rw [topDualPairing_apply, ← hu, NormedSpace.dual_def]
  simpa only [topDualPairing_apply] using
    forall_sum_apply_sub_le_fenchelConjugate_iff (topDualPairing ℝ E) hB hφ hlsc hbot (y := y)
      (x := x) (n := n)

end LMLExplore.OnlineLearning
