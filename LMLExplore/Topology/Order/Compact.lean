/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Closedness of the set of vectors dominated by a continuous family

Let `Φ : T → ι → ℝ` be a continuous family of vectors, with `ι` finite. The set of the vectors `v`
with `v ≤ Φ t` for some `t` is closed as soon as, for every bound `R`, the parameters `t` of the
dominating elements of the vectors bounded by `R` lie in a compact set: the set is then locally
the projection of a closed subset of a product with a compact factor.

## Main statements

* `LMLExplore.isClosed_setOf_exists_le`: the closedness criterion above.
-/

public section

open Set

namespace LMLExplore

/-- The set of vectors dominated by a continuous family `Φ` is closed, when the parameters of the
dominating elements of bounded vectors lie in a compact set. -/
theorem isClosed_setOf_exists_le {ι T : Type*} [Finite ι] [TopologicalSpace T]
    {Φ : T → ι → ℝ} (hΦ : Continuous Φ)
    (hK : ∀ R : ℝ, ∃ K : Set T, IsCompact K ∧
      ∀ t (v : ι → ℝ), (∀ i, |v i| ≤ R) → v ≤ Φ t → t ∈ K) :
    IsClosed {v : ι → ℝ | ∃ t, v ≤ Φ t} := by
  have := Fintype.ofFinite ι
  refine closure_subset_iff_isClosed.1 fun w hw ↦ ?_
  obtain ⟨K, hKc, hKmem⟩ := hK (‖w‖ + 1)
  -- the vectors dominated through a parameter of `K` form a closed set
  have hKcl : IsClosed {v : ι → ℝ | ∃ t ∈ K, v ≤ Φ t} := by
    have := isCompact_iff_compactSpace.1 hKc
    have heq : {v : ι → ℝ | ∃ t ∈ K, v ≤ Φ t} =
        Prod.fst '' {p : (ι → ℝ) × K | p.1 ≤ Φ p.2} := by
      ext v
      constructor
      · rintro ⟨t, htK, hv⟩
        exact ⟨(v, ⟨t, htK⟩), hv, rfl⟩
      · rintro ⟨⟨v', t⟩, hv, rfl⟩
        exact ⟨t, t.2, hv⟩
    rw [heq]
    exact isClosedMap_fst_of_compactSpace _
      (isClosed_le continuous_fst (hΦ.comp (continuous_subtype_val.comp continuous_snd)))
  -- near `w`, every dominated vector is dominated through a parameter of `K`
  have hsub : Metric.ball w 1 ∩ {v | ∃ t, v ≤ Φ t} ⊆ {v | ∃ t ∈ K, v ≤ Φ t} := by
    rintro v ⟨hv, t, ht⟩
    refine ⟨t, hKmem t v (fun i ↦ ?_) ht, ht⟩
    have h1 := norm_le_pi_norm v i
    have h2 := norm_sub_norm_le v w
    rw [Metric.mem_ball, dist_eq_norm] at hv
    rw [← Real.norm_eq_abs]
    linarith
  obtain ⟨t, -, ht⟩ := hKcl.closure_subset
    (closure_mono hsub (Metric.isOpen_ball.inter_closure ⟨Metric.mem_ball_self one_pos, hw⟩))
  exact ⟨t, ht⟩

end LMLExplore
