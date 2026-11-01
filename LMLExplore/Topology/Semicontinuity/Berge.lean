/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Berge's maximum theorem

For a correspondence `C : X → Set Y` and a function `f : X → Y → β` with values in a complete
linear order, we study the value function `x ↦ ⨆ y ∈ C x, f x y` and the solution correspondence
`x ↦ {y ∈ C x | IsMaxOn (f x) (C x) y}`, together with their duals for `⨅` and `IsMinOn`.

Berge's maximum theorem states that if `C` is continuous (upper and lower hemicontinuous) with
compact values and `f` is continuous, then the value function is continuous and the solution
correspondence is upper hemicontinuous with compact values. We prove it in its semicontinuous
form, one half at a time, and at a point within a set, so that it applies to the
restriction of a correspondence to a subset of its domain:
* a supremum over an upper hemicontinuous compact-valued correspondence of an upper
  semicontinuous function is upper semicontinuous;
* a supremum over a lower hemicontinuous correspondence of a lower semicontinuous function is
  lower semicontinuous (no compactness is needed);
* the maximizers of an upper semicontinuous function over an upper hemicontinuous compact-valued
  correspondence form an upper hemicontinuous correspondence, as soon as the value function is
  lower semicontinuous.

The continuity statements are the analogues for a varying compact set of Mathlib's
`IsCompact.continuous_sSup` and `IsCompact.continuous_sInf`, which treat a fixed compact set and
a conditionally complete order. For the constant correspondence on a compact space, the lower
semicontinuity of infima is Tau Ceti's `TauCeti.lowerSemicontinuous_iInf_of_compactSpace`. The
order `β` carries no topology except in the continuity statements.

In bandit identification, these statements give the continuity in the model of the value of the
pure exploration game and the upper hemicontinuity of its optimal allocations [DK19, Appendix D].

## Main statements

* `UpperHemicontinuousWithinAt.upperSemicontinuousWithinAt_biSup`,
  `LowerHemicontinuousWithinAt.lowerSemicontinuousWithinAt_biSup`: semicontinuity of the value
  function `x ↦ ⨆ y ∈ C x, f x y`.
* `UpperHemicontinuousWithinAt.continuousWithinAt_biSup`: **Berge's maximum theorem**, continuity
  of the value function.
* `UpperHemicontinuousWithinAt.upperHemicontinuousWithinAt_isMaxOn`: upper hemicontinuity of the
  solution correspondence `x ↦ {y ∈ C x | IsMaxOn (f x) (C x) y}`.
* `UpperSemicontinuousOn.isCompact_setOf_isMaxOn`: the solution correspondence has compact values.
* The dual statements for `⨅` and `IsMinOn`, and the versions at a point.

## References

* C. Berge, *Topological spaces*, Oliver and Boyd (1963), Chapter VI, Section 3.
* C. D. Aliprantis and K. C. Border, *Infinite dimensional analysis*, Springer (2006),
  Lemmas 17.29–17.30 and Theorem 17.31.
* R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*, NeurIPS 2019,
  Appendix D, Theorem 22.
-/

public section

open Set Filter Topology Function

variable {X Y β : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLinearOrder β]
  {C : X → Set Y} {f : X → Y → β} {s : Set X} {x : X}

/-! ### Semicontinuity of the value function -/

/-- A supremum over an upper hemicontinuous correspondence with compact values of a function that
is upper semicontinuous at every point of the graph over `x` is upper semicontinuous at `x`. -/
theorem UpperHemicontinuousWithinAt.upperSemicontinuousWithinAt_biSup
    (hC : UpperHemicontinuousWithinAt C s x) (hK : IsCompact (C x))
    (hf : ∀ y ∈ C x, UpperSemicontinuousWithinAt ↿f (s ×ˢ univ) (x, y)) :
    UpperSemicontinuousWithinAt (fun x ↦ ⨆ y ∈ C x, f x y) s x := by
  intro t ht
  -- Find a level `c` above the value at `x` such that values below `c` stay below `d < t`.
  obtain ⟨c, hc, d, hd, hcd⟩ : ∃ c, (⨆ y ∈ C x, f x y) < c ∧ ∃ d < t, ∀ e < c, e ≤ d := by
    by_cases h : (⨆ y ∈ C x, f x y) ⋖ t
    · exact ⟨t, ht, _, ht, fun e he ↦ h.le_of_lt he⟩
    · obtain ⟨c, h₁, h₂⟩ := (not_covBy_iff ht).1 h
      exact ⟨c, h₁, c, h₂, fun e he ↦ he.le⟩
  have hmem : {p : X × Y | ↿f p < c} ∈ 𝓝[s] x ×ˢ 𝓝ˢ (C x) := by
    refine hK.mem_prod_nhdsSet_of_forall fun y hy ↦ ?_
    have := hf y hy c ((le_biSup (f x) hy).trans_lt hc)
    rwa [nhdsWithin_prod_eq, nhdsWithin_univ] at this
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.1 hmem
  filter_upwards [hU, hC V hV] with x' hx' hV'
  refine lt_of_le_of_lt (iSup₂_le fun y hy ↦ ?_) hd
  exact hcd _ (hUV (mk_mem_prod hx' (subset_of_mem_nhdsSet hV' hy)))

/-- A supremum over a lower hemicontinuous correspondence of a function that is lower
semicontinuous at every point of the graph over `x` is lower semicontinuous at `x`. -/
theorem LowerHemicontinuousWithinAt.lowerSemicontinuousWithinAt_biSup
    (hC : LowerHemicontinuousWithinAt C s x)
    (hf : ∀ y ∈ C x, LowerSemicontinuousWithinAt ↿f (s ×ˢ univ) (x, y)) :
    LowerSemicontinuousWithinAt (fun x ↦ ⨆ y ∈ C x, f x y) s x := by
  intro t ht
  obtain ⟨y, hy, hty⟩ := lt_biSup_iff.1 ht
  have := hf y hy t hty
  rw [nhdsWithin_prod_eq, nhdsWithin_univ] at this
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.1 this
  obtain ⟨W, hWV, hWo, hyW⟩ := mem_nhds_iff.1 hV
  filter_upwards [hU, hC W ⟨hWo, y, hy, hyW⟩] with x' hx' hW'
  obtain ⟨y', hy', hy'W⟩ := hW'.2
  exact (hUV (mk_mem_prod hx' (hWV hy'W))).trans_le (le_biSup _ hy')

-- The statements about `⨅` and `IsMinOn` are those about `⨆` and `IsMaxOn` in the order dual
-- `βᵒᵈ`, where infima, semicontinuity and minimizers are suprema, the opposite semicontinuity
-- and maximizers by definition, as in Mathlib's `upperSemicontinuous_iInf`.
/-- An infimum over an upper hemicontinuous correspondence with compact values of a function that
is lower semicontinuous at every point of the graph over `x` is lower semicontinuous at `x`. -/
theorem UpperHemicontinuousWithinAt.lowerSemicontinuousWithinAt_biInf
    (hC : UpperHemicontinuousWithinAt C s x) (hK : IsCompact (C x))
    (hf : ∀ y ∈ C x, LowerSemicontinuousWithinAt ↿f (s ×ˢ univ) (x, y)) :
    LowerSemicontinuousWithinAt (fun x ↦ ⨅ y ∈ C x, f x y) s x :=
  hC.upperSemicontinuousWithinAt_biSup (β := βᵒᵈ) hK hf

/-- An infimum over a lower hemicontinuous correspondence of a function that is upper
semicontinuous at every point of the graph over `x` is upper semicontinuous at `x`. -/
theorem LowerHemicontinuousWithinAt.upperSemicontinuousWithinAt_biInf
    (hC : LowerHemicontinuousWithinAt C s x)
    (hf : ∀ y ∈ C x, UpperSemicontinuousWithinAt ↿f (s ×ˢ univ) (x, y)) :
    UpperSemicontinuousWithinAt (fun x ↦ ⨅ y ∈ C x, f x y) s x :=
  hC.lowerSemicontinuousWithinAt_biSup (β := βᵒᵈ) hf

/-- A supremum over an upper hemicontinuous correspondence with compact values of a function that
is upper semicontinuous at every point of the graph over `x` is upper semicontinuous at `x`. -/
theorem UpperHemicontinuousAt.upperSemicontinuousAt_biSup
    (hC : UpperHemicontinuousAt C x) (hK : IsCompact (C x))
    (hf : ∀ y ∈ C x, UpperSemicontinuousAt ↿f (x, y)) :
    UpperSemicontinuousAt (fun x ↦ ⨆ y ∈ C x, f x y) x := by
  rw [← upperHemicontinuousWithinAt_univ_iff] at hC
  simp_rw [← upperSemicontinuousWithinAt_univ_iff, ← univ_prod_univ] at hf ⊢
  exact hC.upperSemicontinuousWithinAt_biSup hK hf

/-- A supremum over a lower hemicontinuous correspondence of a function that is lower
semicontinuous at every point of the graph over `x` is lower semicontinuous at `x`. -/
theorem LowerHemicontinuousAt.lowerSemicontinuousAt_biSup
    (hC : LowerHemicontinuousAt C x) (hf : ∀ y ∈ C x, LowerSemicontinuousAt ↿f (x, y)) :
    LowerSemicontinuousAt (fun x ↦ ⨆ y ∈ C x, f x y) x := by
  rw [← lowerHemicontinuousWithinAt_univ_iff] at hC
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff, ← univ_prod_univ] at hf ⊢
  exact hC.lowerSemicontinuousWithinAt_biSup hf

/-- An infimum over an upper hemicontinuous correspondence with compact values of a function that
is lower semicontinuous at every point of the graph over `x` is lower semicontinuous at `x`. -/
theorem UpperHemicontinuousAt.lowerSemicontinuousAt_biInf
    (hC : UpperHemicontinuousAt C x) (hK : IsCompact (C x))
    (hf : ∀ y ∈ C x, LowerSemicontinuousAt ↿f (x, y)) :
    LowerSemicontinuousAt (fun x ↦ ⨅ y ∈ C x, f x y) x :=
  hC.upperSemicontinuousAt_biSup (β := βᵒᵈ) hK hf

/-- An infimum over a lower hemicontinuous correspondence of a function that is upper
semicontinuous at every point of the graph over `x` is upper semicontinuous at `x`. -/
theorem LowerHemicontinuousAt.upperSemicontinuousAt_biInf
    (hC : LowerHemicontinuousAt C x) (hf : ∀ y ∈ C x, UpperSemicontinuousAt ↿f (x, y)) :
    UpperSemicontinuousAt (fun x ↦ ⨅ y ∈ C x, f x y) x :=
  hC.lowerSemicontinuousAt_biSup (β := βᵒᵈ) hf

/-! ### Berge's maximum theorem: continuity of the value function -/

section Continuity

variable [TopologicalSpace β] [OrderTopology β]

/-- **Berge's maximum theorem**, continuity of the value function: a supremum over a continuous
(upper and lower hemicontinuous) correspondence with compact values of a function that is
continuous at every point of the graph over `x` is continuous at `x`. -/
theorem UpperHemicontinuousWithinAt.continuousWithinAt_biSup
    (hCu : UpperHemicontinuousWithinAt C s x) (hCl : LowerHemicontinuousWithinAt C s x)
    (hK : IsCompact (C x)) (hf : ∀ y ∈ C x, ContinuousWithinAt ↿f (s ×ˢ univ) (x, y)) :
    ContinuousWithinAt (fun x ↦ ⨆ y ∈ C x, f x y) s x := by
  simp_rw [continuousWithinAt_iff_lower_upperSemicontinuousWithinAt] at hf ⊢
  exact ⟨hCl.lowerSemicontinuousWithinAt_biSup fun y hy ↦ (hf y hy).1,
    hCu.upperSemicontinuousWithinAt_biSup hK fun y hy ↦ (hf y hy).2⟩

/-- **Berge's maximum theorem** for infima: an infimum over a continuous (upper and lower
hemicontinuous) correspondence with compact values of a function that is continuous at every
point of the graph over `x` is continuous at `x`. -/
theorem UpperHemicontinuousWithinAt.continuousWithinAt_biInf
    (hCu : UpperHemicontinuousWithinAt C s x) (hCl : LowerHemicontinuousWithinAt C s x)
    (hK : IsCompact (C x)) (hf : ∀ y ∈ C x, ContinuousWithinAt ↿f (s ×ˢ univ) (x, y)) :
    ContinuousWithinAt (fun x ↦ ⨅ y ∈ C x, f x y) s x :=
  hCu.continuousWithinAt_biSup (β := βᵒᵈ) hCl hK hf

/-- **Berge's maximum theorem**, continuity of the value function at a point. -/
theorem UpperHemicontinuousAt.continuousAt_biSup
    (hCu : UpperHemicontinuousAt C x) (hCl : LowerHemicontinuousAt C x)
    (hK : IsCompact (C x)) (hf : ∀ y ∈ C x, ContinuousAt ↿f (x, y)) :
    ContinuousAt (fun x ↦ ⨆ y ∈ C x, f x y) x := by
  simp_rw [continuousAt_iff_lower_upperSemicontinuousAt] at hf ⊢
  exact ⟨hCl.lowerSemicontinuousAt_biSup fun y hy ↦ (hf y hy).1,
    hCu.upperSemicontinuousAt_biSup hK fun y hy ↦ (hf y hy).2⟩

/-- **Berge's maximum theorem** for infima, at a point. -/
theorem UpperHemicontinuousAt.continuousAt_biInf
    (hCu : UpperHemicontinuousAt C x) (hCl : LowerHemicontinuousAt C x)
    (hK : IsCompact (C x)) (hf : ∀ y ∈ C x, ContinuousAt ↿f (x, y)) :
    ContinuousAt (fun x ↦ ⨅ y ∈ C x, f x y) x :=
  hCu.continuousAt_biSup (β := βᵒᵈ) hCl hK hf

end Continuity

/-! ### The solution correspondence -/

/-- The maximizers of a function that is upper semicontinuous on a compact set form a compact
set. -/
theorem UpperSemicontinuousOn.isCompact_setOf_isMaxOn {g : Y → β} {K : Set Y}
    (hg : UpperSemicontinuousOn g K) (hK : IsCompact K) : IsCompact {y ∈ K | IsMaxOn g K y} := by
  convert hg.isCompact_inter_preimage_Ici hK (⨆ y ∈ K, g y) using 1
  ext y
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ici, isMaxOn_iff, iSup₂_le_iff]

/-- The minimizers of a function that is lower semicontinuous on a compact set form a compact
set. -/
theorem LowerSemicontinuousOn.isCompact_setOf_isMinOn {g : Y → β} {K : Set Y}
    (hg : LowerSemicontinuousOn g K) (hK : IsCompact K) : IsCompact {y ∈ K | IsMinOn g K y} :=
  UpperSemicontinuousOn.isCompact_setOf_isMaxOn (β := βᵒᵈ) hg hK

/-- **Berge's maximum theorem**, upper hemicontinuity of the solution correspondence: the
maximizers `{y ∈ C x | IsMaxOn (f x) (C x) y}` of a function `f x` over an upper hemicontinuous
correspondence `C` with compact values are upper hemicontinuous at `x`, if `f` is upper
semicontinuous at every point of the graph over `x` and the value function
`x ↦ ⨆ y ∈ C x, f x y` is lower semicontinuous at `x`.

The value function is lower semicontinuous when `C` is lower hemicontinuous and `f` is lower
semicontinuous (`LowerHemicontinuousWithinAt.lowerSemicontinuousWithinAt_biSup`). -/
theorem UpperHemicontinuousWithinAt.upperHemicontinuousWithinAt_isMaxOn
    (hC : UpperHemicontinuousWithinAt C s x) (hK : IsCompact (C x))
    (hf : ∀ y ∈ C x, UpperSemicontinuousWithinAt ↿f (s ×ˢ univ) (x, y))
    (hm : LowerSemicontinuousWithinAt (fun x ↦ ⨆ y ∈ C x, f x y) s x) :
    UpperHemicontinuousWithinAt (fun x ↦ {y ∈ C x | IsMaxOn (f x) (C x) y}) s x := by
  refine upperHemicontinuousWithinAt_iff_forall_isOpen.2 fun U hU hsub ↦ ?_
  -- Near the points of `C x` outside `U`, the function is below the value function.
  have key : ∀ y ∈ C x \ U, {p : X × Y | ↿f p < ⨆ z ∈ C p.1, f p.1 z} ∈ 𝓝[s] x ×ˢ 𝓝 y := by
    rintro y ⟨hy, hyU⟩
    obtain ⟨z, hz, hyz⟩ : ∃ z ∈ C x, f x y < f x z := by
      by_contra! h
      exact hyU (hsub ⟨hy, isMaxOn_iff.2 h⟩)
    have hlt : f x y < ⨆ z ∈ C x, f x z := hyz.trans_le (le_biSup _ hz)
    -- Separate `f x y` from the value at `x` by a level `c` and a level `d`.
    obtain ⟨c, hc, d, hd, hcd⟩ : ∃ c, f x y < c ∧ ∃ d < ⨆ z ∈ C x, f x z, ∀ e < c, e ≤ d := by
      by_cases h : f x y ⋖ ⨆ z ∈ C x, f x z
      · exact ⟨_, hlt, _, hlt, fun e he ↦ h.le_of_lt he⟩
      · obtain ⟨c, h₁, h₂⟩ := (not_covBy_iff hlt).1 h
        exact ⟨c, h₁, c, h₂, fun e he ↦ he.le⟩
    have h₁ := hf y hy c hc
    rw [nhdsWithin_prod_eq, nhdsWithin_univ] at h₁
    filter_upwards [h₁, (hm d hd).prod_inl (𝓝 y)] with p hp₁ hp₂
    exact (hcd _ hp₁).trans_lt hp₂
  obtain ⟨W, hW, V, hV, hWV⟩ := mem_prod_iff.1 ((hK.diff hU).mem_prod_nhdsSet_of_forall key)
  have hVU : V ∪ U ∈ 𝓝ˢ (C x) := by
    refine nhdsSet_mono (subset_sdiff_union (C x) U) ?_
    rw [nhdsSet_union]
    exact union_mem_sup hV (hU.mem_nhdsSet.2 subset_rfl)
  filter_upwards [hW, hC _ hVU] with x' hx' hC'
  rintro y' ⟨hy', hmax⟩
  refine (subset_of_mem_nhdsSet hC' hy').resolve_left fun hyV ↦ ?_
  exact (hWV (mk_mem_prod hx' hyV)).not_ge (iSup₂_le fun z hz ↦ isMaxOn_iff.1 hmax z hz)

/-- **Berge's maximum theorem** for infima, upper hemicontinuity of the solution correspondence:
the minimizers `{y ∈ C x | IsMinOn (f x) (C x) y}` of a function `f x` over an upper
hemicontinuous correspondence `C` with compact values are upper hemicontinuous at `x`, if `f` is
lower semicontinuous at every point of the graph over `x` and the value function
`x ↦ ⨅ y ∈ C x, f x y` is upper semicontinuous at `x`. -/
theorem UpperHemicontinuousWithinAt.upperHemicontinuousWithinAt_isMinOn
    (hC : UpperHemicontinuousWithinAt C s x) (hK : IsCompact (C x))
    (hf : ∀ y ∈ C x, LowerSemicontinuousWithinAt ↿f (s ×ˢ univ) (x, y))
    (hm : UpperSemicontinuousWithinAt (fun x ↦ ⨅ y ∈ C x, f x y) s x) :
    UpperHemicontinuousWithinAt (fun x ↦ {y ∈ C x | IsMinOn (f x) (C x) y}) s x :=
  hC.upperHemicontinuousWithinAt_isMaxOn (β := βᵒᵈ) hK hf hm

/-- **Berge's maximum theorem**, upper hemicontinuity of the solution correspondence at a
point. -/
theorem UpperHemicontinuousAt.upperHemicontinuousAt_isMaxOn
    (hC : UpperHemicontinuousAt C x) (hK : IsCompact (C x))
    (hf : ∀ y ∈ C x, UpperSemicontinuousAt ↿f (x, y))
    (hm : LowerSemicontinuousAt (fun x ↦ ⨆ y ∈ C x, f x y) x) :
    UpperHemicontinuousAt (fun x ↦ {y ∈ C x | IsMaxOn (f x) (C x) y}) x := by
  rw [← upperHemicontinuousWithinAt_univ_iff] at hC ⊢
  rw [← lowerSemicontinuousWithinAt_univ_iff] at hm
  simp_rw [← upperSemicontinuousWithinAt_univ_iff, ← univ_prod_univ] at hf
  exact hC.upperHemicontinuousWithinAt_isMaxOn hK hf hm

/-- **Berge's maximum theorem** for infima, upper hemicontinuity of the solution correspondence at
a point. -/
theorem UpperHemicontinuousAt.upperHemicontinuousAt_isMinOn
    (hC : UpperHemicontinuousAt C x) (hK : IsCompact (C x))
    (hf : ∀ y ∈ C x, LowerSemicontinuousAt ↿f (x, y))
    (hm : UpperSemicontinuousAt (fun x ↦ ⨅ y ∈ C x, f x y) x) :
    UpperHemicontinuousAt (fun x ↦ {y ∈ C x | IsMinOn (f x) (C x) y}) x :=
  hC.upperHemicontinuousAt_isMaxOn (β := βᵒᵈ) hK hf hm
