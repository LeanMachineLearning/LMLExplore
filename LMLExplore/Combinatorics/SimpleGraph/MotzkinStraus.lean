/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Motzkin–Straus theorem

For a finite simple graph `G` with clique number `ω` and adjacency matrix `A`, the maximum of the
quadratic form `w ⬝ᵥ A *ᵥ w` over the probability vectors `w` on the vertices is `1 - 1 / ω`,
attained by the uniform vector on a maximum clique [MS65]. Equivalently, in homogeneous form,
`ω * (w ⬝ᵥ A *ᵥ w) ≤ (ω - 1) * (∑ v, w v) ^ 2` for every nonnegative `w`.

The quadratic form `w ⬝ᵥ A *ᵥ w` is the probability that two vertices drawn independently from
`w` are adjacent, so the theorem computes the largest such probability. This is what describes
the e-variables `c * 𝟙{x₀ ~ x₁}` of two i.i.d. observations on the vertices
(`ProbabilityTheory.isEVar_mul_indicator_adj_iff`).

## Main statements

* `SimpleGraph.cliqueNum_mul_dotProduct_mulVec_adjMatrix_le`: the homogeneous form.
* `SimpleGraph.dotProduct_mulVec_adjMatrix_le`: for a probability vector `w`,
  `w ⬝ᵥ A *ᵥ w ≤ (ω - 1) / ω`.
* `SimpleGraph.exists_dotProduct_mulVec_adjMatrix_eq`: the bound is attained.
* `SimpleGraph.dotProduct_mulVec_adjMatrix_eq_of_isClique`: for a weight supported on a clique,
  `w ⬝ᵥ A *ᵥ w = (∑ v, w v) ^ 2 - ∑ v, w v ^ 2`.
* `SimpleGraph.cliqueNum_mul_dotProduct_mulVec_adjMatrix_le_of_isClique`: the homogeneous form
  for a weight supported on a clique.

## Implementation notes

The inequality is proved by the classical weight-shifting argument: moving all the weight of one
of two non-adjacent vertices of the support to the other, in the direction that does not decrease
the quadratic form (which is affine along that direction), shrinks the support until it is a
clique; on a clique of size `k ≤ ω` the quadratic form is `1 - ∑ v, w v ^ 2 ≤ 1 - 1 / k`. The
proofs are adapted from `EValuesResearch.adjMatrix_quadForm_le` in the Lean library of the
research notes github.com/RemyDegenne/evalues_research (Apache 2.0).

## References

* [MS65] T. S. Motzkin and E. G. Straus, *Maxima for graphs and a new proof of a theorem of
  Turán*, Canad. J. Math. 17 (1965), 533–540.
-/

public section

open Matrix Finset

namespace SimpleGraph

variable {V : Type*}

/-- The value at each vertex of a weight after moving weight `t` from `b` to `a`. -/
private lemma add_smul_single_sub_single_apply [DecidableEq V] (w : V → ℝ) {a b : V}
    (hab : a ≠ b) (t : ℝ) (v : V) :
    (w + t • (Pi.single a 1 - Pi.single b 1) : V → ℝ) v =
      if v = a then w a + t else if v = b then w b - t else w v := by
  by_cases hva : v = a
  · subst hva
    simp [hab]
  · by_cases hvb : v = b
    · subst hvb
      simp [hva, sub_eq_add_neg]
    · simp [hva, hvb]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Moving weight `t` from a vertex `b` to a non-adjacent vertex `a` changes the quadratic form of
the adjacency matrix by an amount linear in `t`. -/
private lemma dotProduct_mulVec_adjMatrix_add_smul [DecidableEq V] (w : V → ℝ) {a b : V}
    (hab : ¬ G.Adj a b) (t : ℝ) :
    (w + t • (Pi.single a 1 - Pi.single b 1)) ⬝ᵥ
        G.adjMatrix ℝ *ᵥ (w + t • (Pi.single a 1 - Pi.single b 1)) =
      w ⬝ᵥ G.adjMatrix ℝ *ᵥ w +
        2 * t * ((Pi.single a 1 - Pi.single b 1) ⬝ᵥ G.adjMatrix ℝ *ᵥ w) := by
  set d : V → ℝ := Pi.single a 1 - Pi.single b 1
  have h_symm : w ⬝ᵥ G.adjMatrix ℝ *ᵥ d = d ⬝ᵥ G.adjMatrix ℝ *ᵥ w := by
    rw [dotProduct_mulVec, ← mulVec_transpose, transpose_adjMatrix, dotProduct_comm]
  have h_dd : d ⬝ᵥ G.adjMatrix ℝ *ᵥ d = 0 := by
    have hba : ¬ G.Adj b a := fun h ↦ hab h.symm
    simp [d, mulVec_sub, sub_dotProduct, dotProduct_sub, adjMatrix_apply, hab, hba]
  rw [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, add_dotProduct, dotProduct_smul,
    dotProduct_smul, smul_dotProduct, smul_dotProduct, h_symm, h_dd]
  simp only [smul_eq_mul]
  ring

/-- One weight-shifting step: moving weight `t` from `b` to a non-adjacent vertex `a`, in the
direction that does not decrease the quadratic form and until one of the two weights vanishes,
keeps the weight nonnegative with the same total and shrinks its support. -/
private lemma shift_weight_step [DecidableEq V] (w : V → ℝ) (hw : 0 ≤ w) {a b : V}
    (hab : a ≠ b) (hadj : ¬ G.Adj a b) (ha : w a ≠ 0) (hb : w b ≠ 0) {t : ℝ} (ht₁ : -w a ≤ t)
    (ht₂ : t ≤ w b) (ht : w a + t = 0 ∨ w b - t = 0)
    (htD : 0 ≤ t * ((Pi.single a 1 - Pi.single b 1) ⬝ᵥ G.adjMatrix ℝ *ᵥ w)) :
    0 ≤ (w + t • (Pi.single a 1 - Pi.single b 1) : V → ℝ) ∧
      ∑ v, (w + t • (Pi.single a 1 - Pi.single b 1) : V → ℝ) v = ∑ v, w v ∧
      w ⬝ᵥ G.adjMatrix ℝ *ᵥ w ≤ (w + t • (Pi.single a 1 - Pi.single b 1)) ⬝ᵥ
        G.adjMatrix ℝ *ᵥ (w + t • (Pi.single a 1 - Pi.single b 1)) ∧
      #{v | (w + t • (Pi.single a 1 - Pi.single b 1) : V → ℝ) v ≠ 0} < #{v | w v ≠ 0} := by
  have hval := add_smul_single_sub_single_apply w hab t
  refine ⟨fun v ↦ ?_, ?_, ?_, ?_⟩
  · rw [Pi.zero_apply, hval]
    split_ifs
    · linarith
    · linarith
    · exact hw v
  · simp [sum_add_distrib, ← mul_sum, sum_sub_distrib]
  · rw [dotProduct_mulVec_adjMatrix_add_smul G w hadj t]
    linarith
  · refine card_lt_card ((ssubset_iff_of_subset fun v hv ↦ ?_).2 ?_)
    · simp only [mem_filter, mem_univ, true_and] at hv ⊢
      rw [hval] at hv
      split_ifs at hv with hva hvb
      · rwa [hva]
      · rwa [hvb]
      · exact hv
    · rcases ht with ht | ht
      · exact ⟨a, by simpa using ha, by simp [hval, ht]⟩
      · exact ⟨b, by simpa using hb, by simp [hval, hab.symm, ht]⟩

/-- A nonnegative weight on the vertices can be replaced by one with the same total, supported on
a clique, without decreasing the quadratic form of the adjacency matrix. The proof is by
induction on a bound `n` on the size of the support. -/
private lemma exists_isClique_support_le (n : ℕ) (w : V → ℝ) (hw : 0 ≤ w)
    (hn : #{v | w v ≠ 0} ≤ n) :
    ∃ w' : V → ℝ, 0 ≤ w' ∧ ∑ v, w' v = ∑ v, w v ∧
      w ⬝ᵥ G.adjMatrix ℝ *ᵥ w ≤ w' ⬝ᵥ G.adjMatrix ℝ *ᵥ w' ∧
      ∀ u v, w' u ≠ 0 → w' v ≠ 0 → u ≠ v → G.Adj u v := by
  classical
  induction n generalizing w with
  | zero =>
    refine ⟨w, hw, rfl, le_rfl, fun u v hu _ _ ↦ absurd hn ?_⟩
    exact Nat.not_le_of_gt (card_pos.2 ⟨u, by simpa using hu⟩)
  | succ n ih =>
    by_cases hcl : ∀ u v, w u ≠ 0 → w v ≠ 0 → u ≠ v → G.Adj u v
    · exact ⟨w, hw, rfl, le_rfl, hcl⟩
    push Not at hcl
    obtain ⟨a, b, ha, hb, hab, hadj⟩ := hcl
    have hwa : 0 ≤ w a := hw a
    have hwb : 0 ≤ w b := hw b
    -- move all the weight of `b` to `a`, or all the weight of `a` to `b`
    obtain ⟨t, ht₁, ht₂, ht, htD⟩ : ∃ t : ℝ, -w a ≤ t ∧ t ≤ w b ∧ (w a + t = 0 ∨ w b - t = 0) ∧
        0 ≤ t * ((Pi.single a 1 - Pi.single b 1) ⬝ᵥ G.adjMatrix ℝ *ᵥ w) := by
      rcases le_or_gt 0 ((Pi.single a 1 - Pi.single b 1) ⬝ᵥ G.adjMatrix ℝ *ᵥ w) with hD | hD
      · exact ⟨w b, by linarith, le_rfl, .inr (sub_self _), mul_nonneg hwb hD⟩
      · exact ⟨-w a, le_rfl, by linarith, .inl (add_neg_cancel _),
          mul_nonneg_of_nonpos_of_nonpos (by linarith) hD.le⟩
    obtain ⟨hw₁, hsum, hF, hcard⟩ := shift_weight_step G w hw hab hadj ha hb ht₁ ht₂ ht htD
    obtain ⟨w', hw', hsum', hF', hcl'⟩ := ih _ hw₁ (by omega)
    exact ⟨w', hw', hsum'.trans hsum, hF.trans hF', hcl'⟩

/-- For a weight supported on a clique, the quadratic form of the adjacency matrix is the square
of the total weight minus the sum of the squares of the weights. -/
theorem dotProduct_mulVec_adjMatrix_eq_of_isClique (w : V → ℝ)
    (hw : G.IsClique {v | w v ≠ 0}) :
    w ⬝ᵥ G.adjMatrix ℝ *ᵥ w = (∑ v, w v) ^ 2 - ∑ v, w v ^ 2 := by
  classical
  rw [dotProduct_mulVec_adjMatrix, sq, sum_mul_sum]
  have h_diag : ∑ v, w v ^ 2 = ∑ u, ∑ v, if u = v then w u * w v else 0 := by
    simp [sq]
  rw [h_diag, ← sum_sub_distrib]
  refine sum_congr rfl fun u _ ↦ ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun v _ ↦ ?_
  by_cases huv : u = v
  · subst huv
    simp
  by_cases hadj : G.Adj u v
  · simp [hadj, huv]
  · have : w u = 0 ∨ w v = 0 := by
      by_contra h
      push Not at h
      exact hadj (hw h.1 h.2 huv)
    rcases this with h | h <;> simp [hadj, huv, h]

/-- The Motzkin–Straus inequality for a weight supported on a clique: if the support of `w` is a
clique of a finite graph with clique number `ω`, then
`ω * (w ⬝ᵥ A *ᵥ w) ≤ (ω - 1) * (∑ v, w v) ^ 2`, where `A` is the adjacency matrix. -/
theorem cliqueNum_mul_dotProduct_mulVec_adjMatrix_le_of_isClique (w : V → ℝ)
    (hw : G.IsClique {v | w v ≠ 0}) :
    G.cliqueNum * (w ⬝ᵥ G.adjMatrix ℝ *ᵥ w) ≤ (G.cliqueNum - 1) * (∑ v, w v) ^ 2 := by
  classical
  rw [dotProduct_mulVec_adjMatrix_eq_of_isClique G w hw]
  set K : Finset V := {v | w v ≠ 0}
  have hK : G.IsClique (K : Set V) := by simpa [K] using hw
  have h_sum : ∑ v, w v = ∑ v ∈ K, w v := (sum_filter_ne_zero _).symm
  have h_sq : ∑ v, w v ^ 2 = ∑ v ∈ K, w v ^ 2 := by
    rw [sum_filter]
    refine sum_congr rfl fun v _ ↦ ?_
    split_ifs with h
    · rfl
    · simp only [ne_eq, not_not] at h
      simp [h]
  have h_cs : (∑ v, w v) ^ 2 ≤ (G.cliqueNum : ℝ) * ∑ v, w v ^ 2 := by
    rw [h_sum, h_sq]
    exact sq_sum_le_card_mul_sum_sq.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hK.card_le_cliqueNum) (sum_nonneg fun v _ ↦ sq_nonneg _))
  nlinarith

/-- **Motzkin–Straus theorem**, homogeneous form: for a nonnegative weight `w` on the vertices of
a finite graph with clique number `ω`, `ω * (w ⬝ᵥ A *ᵥ w) ≤ (ω - 1) * (∑ v, w v) ^ 2`, where `A` is
the adjacency matrix. -/
theorem cliqueNum_mul_dotProduct_mulVec_adjMatrix_le (w : V → ℝ) (hw : 0 ≤ w) :
    G.cliqueNum * (w ⬝ᵥ G.adjMatrix ℝ *ᵥ w) ≤ (G.cliqueNum - 1) * (∑ v, w v) ^ 2 := by
  classical
  obtain ⟨w', hw', hsum, hF, hcl⟩ := exists_isClique_support_le G _ w hw le_rfl
  calc (G.cliqueNum : ℝ) * (w ⬝ᵥ G.adjMatrix ℝ *ᵥ w)
  _ ≤ G.cliqueNum * (w' ⬝ᵥ G.adjMatrix ℝ *ᵥ w') := by gcongr
  _ ≤ (G.cliqueNum - 1) * (∑ v, w' v) ^ 2 :=
    cliqueNum_mul_dotProduct_mulVec_adjMatrix_le_of_isClique G w' fun u hu v hv huv ↦
      hcl u v hu hv huv
  _ = (G.cliqueNum - 1) * (∑ v, w v) ^ 2 := by rw [hsum]

/-- **Motzkin–Straus theorem**: for a probability vector `w` on the vertices of a finite graph
with clique number `ω`, the quadratic form of the adjacency matrix is at most `(ω - 1) / ω`. -/
theorem dotProduct_mulVec_adjMatrix_le (w : V → ℝ) (hw : 0 ≤ w) (hw₁ : ∑ v, w v = 1) :
    w ⬝ᵥ G.adjMatrix ℝ *ᵥ w ≤ (G.cliqueNum - 1) / G.cliqueNum := by
  have h := cliqueNum_mul_dotProduct_mulVec_adjMatrix_le G w hw
  rw [hw₁, one_pow, mul_one] at h
  have : Nonempty V := by
    by_contra hV
    rw [not_nonempty_iff] at hV
    simp at hw₁
  have hω : (0 : ℝ) < G.cliqueNum := by
    exact_mod_cast Nat.pos_of_ne_zero G.cliqueNum_ne_zero_of_finite
  rw [le_div_iff₀ hω]
  linarith

/-- The bound of the Motzkin–Straus theorem is attained: on a nonempty finite graph with clique
number `ω`, the uniform probability vector on a maximum clique has quadratic form `(ω - 1) / ω`
for the adjacency matrix. -/
theorem exists_dotProduct_mulVec_adjMatrix_eq [Nonempty V] :
    ∃ w : V → ℝ, 0 ≤ w ∧ ∑ v, w v = 1 ∧
      w ⬝ᵥ G.adjMatrix ℝ *ᵥ w = (G.cliqueNum - 1) / G.cliqueNum := by
  classical
  obtain ⟨K, hK⟩ := G.maximumClique_exists
  have hcard := G.maximumClique_card_eq_cliqueNum K hK
  have hω : (G.cliqueNum : ℝ) ≠ 0 := by exact_mod_cast G.cliqueNum_ne_zero_of_finite
  set w : V → ℝ := fun v ↦ if v ∈ K then (G.cliqueNum : ℝ)⁻¹ else 0
  have hsum : ∑ v, w v = 1 := by
    simp only [w, sum_ite_mem, univ_inter, sum_const, hcard, nsmul_eq_mul]
    field_simp
  refine ⟨w, fun v ↦ ?_, hsum, ?_⟩
  · simp only [Pi.zero_apply, w]
    split_ifs <;> positivity
  rw [dotProduct_mulVec_adjMatrix_eq_of_isClique, hsum]
  · simp only [w, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_ite_mem,
      univ_inter, sum_const, hcard, nsmul_eq_mul]
    field_simp
  · intro u hu v hv huv
    simp only [Set.mem_ofPred_eq, w, ne_eq, ite_eq_right_iff, inv_eq_zero, Nat.cast_eq_zero,
      Classical.not_imp] at hu hv
    exact hK.isClique hu.1 hv.1 huv

end SimpleGraph
