/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Convex.Simplex
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Sion

/-!
# Von Neumann's minimax theorem on the probability simplex

A player who chooses a mixed strategy `w` in the probability simplex of a finite type `α` against
an opponent choosing a vector `y` in a convex set `Y ⊆ α → ℝ` receives the payoff
`w ⬝ᵥ y = ∑ a, w a * y a`. Von Neumann's minimax theorem states that the order of play does not
matter:
`sup_{w ∈ Δ_α} inf_{y ∈ Y} w ⬝ᵥ y = inf_{y ∈ Y} sup_{w ∈ Δ_α} w ⬝ᵥ y = inf_{y ∈ Y} max_a y a`.
No compactness of `Y` is needed: the simplex is compact.

This file proves the theorem for payoffs `ENNReal.ofReal (w ⬝ᵥ y)` valued in `ℝ≥0∞`, the form in
which nonnegative games appear in bandit identification, where the payoffs are transportation
costs (`LMLExplore/Identification/Task/Minimax.lean`). It is a consequence of Mathlib's
`Sion.minimax'`, applied in the order dual of `ℝ≥0∞`.

## Main statements

* `LMLExplore.iSup_simplex_ofReal_dotProduct`: `sup_{w ∈ Δ_α} w ⬝ᵥ y = max_a y a`.
* `LMLExplore.iSup_simplex_iInf_ofReal_dotProduct`: von Neumann's minimax theorem on the simplex.

## References

* J. von Neumann, *Zur Theorie der Gesellschaftsspiele*, Math. Ann. 100 (1928), 295–320.
* M. Sion, *On general minimax theorems*, Pacific J. Math. 8 (1958), 171–176.
-/

public section

open OrderDual

open scoped ENNReal

namespace LMLExplore

variable {α : Type*} [Fintype α]

/-- The largest payoff `w ⬝ᵥ y` of a mixed strategy `w` of the simplex is the largest entry of
`y`. -/
lemma iSup_simplex_ofReal_dotProduct (y : α → ℝ) :
    ⨆ w ∈ simplex α, ENNReal.ofReal (w ⬝ᵥ y) = ⨆ a, ENNReal.ofReal (y a) := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · have h : simplex α = ∅ :=
      Set.eq_empty_of_forall_notMem fun w hw ↦ by simpa using (mem_simplex_iff.1 hw).2
    simp [h]
  obtain ⟨b, -, hb⟩ := Finset.exists_max_image Finset.univ y Finset.univ_nonempty
  refine le_antisymm (iSup₂_le fun w hw ↦ ?_) (iSup_le fun a ↦ ?_)
  · obtain ⟨hw0, hw1⟩ := mem_simplex_iff.1 hw
    refine le_iSup_of_le b (ENNReal.ofReal_le_ofReal ?_)
    calc w ⬝ᵥ y ≤ ∑ a, w a * y b :=
          Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (hb a (Finset.mem_univ a)) (hw0 a)
      _ = y b := by rw [← Finset.sum_mul, hw1, one_mul]
  · refine le_iSup₂_of_le (Pi.single a 1) (single_mem_simplex a) ?_
    rw [single_dotProduct, one_mul]

/-- **Von Neumann's minimax theorem** on the probability simplex, for payoffs in `ℝ≥0∞`: for a
convex set `Y` of vectors,
`sup_{w ∈ Δ_α} inf_{y ∈ Y} w ⬝ᵥ y = inf_{y ∈ Y} max_a y a = inf_{y ∈ Y} sup_{w ∈ Δ_α} w ⬝ᵥ y`. -/
theorem iSup_simplex_iInf_ofReal_dotProduct [Nonempty α] {Y : Set (α → ℝ)} (hY : Convex ℝ Y) :
    ⨆ w ∈ simplex α, ⨅ y ∈ Y, ENNReal.ofReal (w ⬝ᵥ y) = ⨅ y ∈ Y, ⨆ a, ENNReal.ofReal (y a) := by
  simp_rw [← iSup_simplex_ofReal_dotProduct]
  -- Sion's theorem in `ℝ≥0∞ᵒᵈ`, with the simplex as the compact set, exchanges `⨆` and `⨅`.
  have hcont (w y : α → ℝ) : Continuous (fun z : α → ℝ ↦ toDual (ENNReal.ofReal (z ⬝ᵥ y))) ∧
      Continuous (fun z : α → ℝ ↦ toDual (ENNReal.ofReal (w ⬝ᵥ z))) :=
    ⟨continuous_toDual.comp (ENNReal.continuous_ofReal.comp (by fun_prop)),
      continuous_toDual.comp (ENNReal.continuous_ofReal.comp (by fun_prop))⟩
  have hlin (w y : α → ℝ) (s : Set (α → ℝ)) (hs : Convex ℝ s) :
      QuasilinearOn ℝ s (fun z : α → ℝ ↦ toDual (ENNReal.ofReal (z ⬝ᵥ y))) ∧
      QuasilinearOn ℝ s (fun z : α → ℝ ↦ toDual (ENNReal.ofReal (w ⬝ᵥ z))) := by
    have h₁ : QuasilinearOn ℝ s fun z : α → ℝ ↦ z ⬝ᵥ y :=
      ⟨((dotProductBilin ℝ ℝ).flip y).convexOn hs |>.quasiconvexOn,
        ((dotProductBilin ℝ ℝ).flip y).concaveOn hs |>.quasiconcaveOn⟩
    have h₂ : QuasilinearOn ℝ s fun z : α → ℝ ↦ w ⬝ᵥ z :=
      ⟨(dotProductBilin ℝ ℝ w).convexOn hs |>.quasiconvexOn,
        (dotProductBilin ℝ ℝ w).concaveOn hs |>.quasiconcaveOn⟩
    have hmono : Monotone ENNReal.ofReal := fun _ _ h ↦ ENNReal.ofReal_le_ofReal h
    exact ⟨(h₁.monotone_comp hmono).dual, (h₂.monotone_comp hmono).dual⟩
  have h := Sion.minimax' (f := fun w y : α → ℝ ↦ toDual (ENNReal.ofReal (w ⬝ᵥ y)))
    (simplex_nonempty α) (convex_simplex α) (isCompact_simplex α)
    (fun y _ ↦ (hcont 0 y).1.lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun y _ ↦ (hlin 0 y _ (convex_simplex α)).1.1) hY
    (fun w _ ↦ (hcont w 0).2.upperSemicontinuous.upperSemicontinuousOn _)
    (fun w _ ↦ (hlin w 0 Y hY).2.2)
  simpa only [ofDual_iInf, ofDual_iSup, ofDual_toDual] using congrArg ofDual h

end LMLExplore
