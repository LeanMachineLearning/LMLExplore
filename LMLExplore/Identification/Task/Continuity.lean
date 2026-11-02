/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.TransportationCost
public import LMLExplore.Topology.Semicontinuity.Berge
public import LMLExplore.Topology.Semicontinuity.Hemicontinuity

/-!
# Continuity of the value of the pure exploration game

Asymptotically optimal identification algorithms such as Track-and-Stop sample the arms with
proportions that track an optimal allocation `w*(θ̂, ¬i)` at the current estimate `θ̂` of the
model, and stop when the cost `D(θ̂, w, ¬i)` of the alternatives is large enough. Their analysis
needs these quantities to depend continuously on the model: as `θ̂ → θ`, the value `D(θ̂, ¬i)` of
the game must converge to `D(θ, ¬i)`, and the optimal allocations at `θ̂` must eventually be close
to those at `θ`.

Degenne and Koolen (2019) derive these properties from the joint continuity of
`(θ, w) ↦ D(θ, w, ¬i)` on the models times the simplex, through Berge's maximum theorem
(`LMLExplore/Topology/Semicontinuity/Berge.lean`): the value `D(θ, ¬i) = sup_{w ∈ Δ_K} D(θ, w, ¬i)`
is a supremum over a fixed compact set. This file proves these consequences, at a point within a
set of models `s`, under that continuity hypothesis:
* the value `D(θ, ¬i)` of an answer is continuous [DK19, Lemma 28];
* the optimal allocations `w*(θ, ¬i)` are upper hemicontinuous [DK19, Lemma 28], with nonempty
  compact values;
* for finitely many answers, the value `D(θ)` of the game and the characteristic time `T*(θ)` are
  continuous on the admissible models [DK19, Lemma 29].

Upper hemicontinuity of `w*(·, ¬i)` at `θ` means that for every open set `U` containing
`w*(θ, ¬i)`, `w*(θ', ¬i) ⊆ U` for `θ'` close to `θ`; when `w*(θ, ¬i)` is a single allocation,
the optimal allocations at nearby models converge to it.

## Main statements

* `IdentTask.isCompact_optAlloc`, `IdentTask.optAlloc_nonempty`: if `w ↦ D(θ, w, ¬i)` is upper
  semicontinuous on the simplex, the optimal allocations form a nonempty compact set.
* `IdentTask.continuousWithinAt_answerValue`: continuity of `θ ↦ D(θ, ¬i)`.
* `IdentTask.upperHemicontinuousWithinAt_optAlloc`: upper hemicontinuity of `θ ↦ w*(θ, ¬i)`.
* `IdentTask.continuousWithinAt_gameValue`, `IdentTask.continuousWithinAt_charTime`: continuity
  of `θ ↦ D(θ)` and of `θ ↦ T*(θ)` for finitely many answers.

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, supplementary material, Appendix F, Lemmas 28 and 29.
-/

public section

open Set Filter Topology

open scoped ENNReal

namespace LMLExplore.Identification

namespace IdentTask

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (task : IdentTask α Θ ℐ 𝓨) {θ : Θ} {i : ℐ} {w : α → ℝ}

/-- If the cost of the alternatives is upper semicontinuous in the allocation on the simplex, the
optimal allocations form a compact set. -/
lemma isCompact_optAlloc (h : UpperSemicontinuousOn (task.altCost θ · i) (simplex α)) :
    IsCompact (task.optAlloc θ i) := by
  convert h.isCompact_setOfPred_isMaxOn (isCompact_simplex α) using 1
  ext w
  exact task.mem_optAlloc_iff_isMaxOn

/-- If the cost of the alternatives is upper semicontinuous in the allocation on the simplex, an
optimal allocation exists: the supremum `D(θ, ¬i)` is attained. -/
lemma optAlloc_nonempty [Nonempty α]
    (h : UpperSemicontinuousOn (task.altCost θ · i) (simplex α)) :
    (task.optAlloc θ i).Nonempty := by
  obtain ⟨w, hw, hmax⟩ := h.exists_isMaxOn (simplex_nonempty α) (isCompact_simplex α)
  exact ⟨w, task.mem_optAlloc_iff_isMaxOn.2 ⟨hw, hmax⟩⟩

/-- The cost of the alternatives as a function on the models times the simplex, as a subtype. -/
private noncomputable def altCostSimplex (task : IdentTask α Θ ℐ 𝓨) (i : ℐ) (θ : Θ)
    (w : simplex α) : ℝ≥0∞ :=
  task.altCost θ w i

private lemma iSup_altCostSimplex (θ : Θ) :
    ⨆ w ∈ (univ : Set (simplex α)), altCostSimplex task i θ w = task.answerValue θ i := by
  simp only [mem_univ, iSup_pos, altCostSimplex, answerValue_def]
  exact (iSup_subtype' (p := (· ∈ simplex α)) (f := fun w _ ↦ task.altCost θ w i)).symm

variable [TopologicalSpace Θ] {s : Set Θ}

/-! ### Continuity in the model, through Berge's maximum theorem -/

/-- Continuity within `s ×ˢ simplex α` of `(θ, w) ↦ D(θ, w, ¬i)` is continuity within
`s ×ˢ univ` of its restriction to the subtype `simplex α`. -/
private lemma continuousWithinAt_altCostSimplex {w : simplex α}
    (h : ContinuousWithinAt (fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i) (s ×ˢ simplex α)
      (θ, w)) :
    ContinuousWithinAt ↿(altCostSimplex task i) (s ×ˢ univ) (θ, w) :=
  h.comp (x := (θ, w)) (t := s ×ˢ simplex α) (f := fun p : Θ × simplex α ↦ (p.1, (p.2 : α → ℝ)))
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousWithinAt
    fun p hp ↦ ⟨hp.1, p.2.2⟩

/-- **Continuity of the value of an answer** [DK19, Lemma 28]. If `(θ, w) ↦ D(θ, w, ¬i)` is
continuous within `s ×ˢ simplex α` at every point `(θ, w)` with `w` in the simplex, then the value
`θ ↦ D(θ, ¬i)` of the game of the answer `i` is continuous within `s` at `θ`. -/
theorem continuousWithinAt_answerValue
    (h : ∀ w ∈ simplex α, ContinuousWithinAt (fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i)
      (s ×ˢ simplex α) (θ, w)) :
    ContinuousWithinAt (task.answerValue · i) s θ := by
  have : CompactSpace (simplex α) := isCompact_iff_compactSpace.1 (isCompact_simplex α)
  simp_rw [← iSup_altCostSimplex task]
  exact (UpperHemicontinuousWithinAt.const (z := (univ : Set (simplex α))))
    |>.continuousWithinAt_biSup .const isCompact_univ
    fun v _ ↦ continuousWithinAt_altCostSimplex task (h v v.2)

/-- **Upper hemicontinuity of the optimal allocations** [DK19, Lemma 28]. If
`(θ, w) ↦ D(θ, w, ¬i)` is continuous within `s ×ˢ simplex α` at every point `(θ, w)` with `w` in
the simplex, then the optimal allocations `θ ↦ w*(θ, ¬i)` are upper hemicontinuous within `s` at
`θ`: for every open set `U ⊇ w*(θ, ¬i)`, `w*(θ', ¬i) ⊆ U` for `θ' ∈ s` close enough to `θ`. -/
theorem upperHemicontinuousWithinAt_optAlloc
    (h : ∀ w ∈ simplex α, ContinuousWithinAt (fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i)
      (s ×ˢ simplex α) (θ, w)) :
    UpperHemicontinuousWithinAt (task.optAlloc · i) s θ := by
  have : CompactSpace (simplex α) := isCompact_iff_compactSpace.1 (isCompact_simplex α)
  have hm : LowerSemicontinuousWithinAt
      (fun θ ↦ ⨆ w ∈ (univ : Set (simplex α)), altCostSimplex task i θ w) s θ := by
    simp_rw [iSup_altCostSimplex task]
    exact (task.continuousWithinAt_answerValue h).lowerSemicontinuousWithinAt
  have h_uhc := ((UpperHemicontinuousWithinAt.const
    (z := (univ : Set (simplex α)))).upperHemicontinuousWithinAt_isMaxOn isCompact_univ (fun v _ ↦
      (continuousWithinAt_altCostSimplex task (h v v.2)).upperSemicontinuousWithinAt) hm).image
    continuous_subtype_val
  -- The maximizers in the subtype are the optimal allocations.
  convert h_uhc using 2 with θ'
  ext v
  simp only [mem_image, mem_univ, true_and, mem_optAlloc_iff_isMaxOn, isMaxOn_iff,
    Subtype.forall, altCostSimplex, Subtype.exists, exists_and_right, exists_eq_right,
    mem_ofPred_eq, forall_const, exists_prop]

/-- **Continuity of the value of the game** [DK19, Lemma 29]. For finitely many answers, if for
every answer `i` the function `(θ, w) ↦ D(θ, w, ¬i)` is continuous within `s ×ˢ simplex α` at
every point `(θ, w)` with `w` in the simplex, then the value `θ ↦ D(θ)` of the game is continuous
within a set `s` of admissible models at an admissible model `θ`. -/
theorem continuousWithinAt_gameValue [Finite ℐ] (hs : s ⊆ task.M) (hθ : θ ∈ task.M)
    (h : ∀ i, ∀ w ∈ simplex α, ContinuousWithinAt (fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i)
      (s ×ˢ simplex α) (θ, w)) :
    ContinuousWithinAt task.gameValue s θ := by
  have : Fintype ℐ := Fintype.ofFinite ℐ
  have h_sup : ContinuousWithinAt (fun θ ↦ (Finset.univ : Finset ℐ).sup (task.answerValue θ))
      s θ :=
    ContinuousWithinAt.finset_sup_apply fun i _ ↦ task.continuousWithinAt_answerValue (h i)
  refine h_sup.congr (fun θ' hθ' ↦ ?_) ?_
  · rw [task.gameValue_eq_iSup_answerValue (hs hθ'), Finset.sup_univ_eq_iSup]
  · rw [task.gameValue_eq_iSup_answerValue hθ, Finset.sup_univ_eq_iSup]

/-- **Continuity of the characteristic time** [DK19, Lemma 29]. Under the hypotheses of
`continuousWithinAt_gameValue`, the characteristic time `θ ↦ T*(θ) = D(θ)⁻¹` is continuous within
`s` at `θ`. -/
theorem continuousWithinAt_charTime [Finite ℐ] (hs : s ⊆ task.M) (hθ : θ ∈ task.M)
    (h : ∀ i, ∀ w ∈ simplex α, ContinuousWithinAt (fun p : Θ × (α → ℝ) ↦ task.altCost p.1 p.2 i)
      (s ×ˢ simplex α) (θ, w)) :
    ContinuousWithinAt task.charTime s θ := by
  rw [show task.charTime = fun θ ↦ (task.gameValue θ)⁻¹ from funext task.charTime_def]
  exact (task.continuousWithinAt_gameValue hs hθ h).inv

end IdentTask

end LMLExplore.Identification
