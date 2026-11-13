/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The probability simplex

The probability simplex `simplex α` of a finite type `α` is the set of vectors `w : α → ℝ` with
nonnegative entries summing to `1`: the probability distributions on `α`, as allocations of samples
to arms, mixed strategies, or weights of an online learner.

It is stated directly on `α → ℝ`, with the topology and the order of that space: Mathlib's set
`stdSimplex` is deprecated, and its replacement `Convexity.StdSimplex` is a type of finitely
supported distributions, not a subset of `α → ℝ`.

## Main definitions

* `LMLExplore.simplex α`: the vectors `w : α → ℝ` with nonnegative entries summing to `1`.

## Main statements

* `LMLExplore.mem_simplex_iff`: membership in the simplex.
* `LMLExplore.add_eq_one_of_mem_simplex`: on a type with two elements `a` and `b`, the entries of
  a vector of the simplex satisfy `w a + w b = 1`.
* `LMLExplore.simplex_subset_nonneg`: the simplex consists of nonnegative vectors.
* `LMLExplore.single_mem_simplex`: the vertices `Pi.single a 1` lie in the simplex.
* `LMLExplore.eq_single_of_mem_simplex`: a vector of the simplex with an entry equal to `1` is a
  vertex.
* `LMLExplore.not_convex_image_single`: a set of vertices with two distinct elements is not
  convex.
* `LMLExplore.uniform_mem_simplex`: the uniform distribution lies in the simplex.
* `LMLExplore.simplex_nonempty`: the simplex of a nonempty type is nonempty.
* `LMLExplore.eq_one_of_mem_simplex`: on a type with at most one element, the simplex is the
  single point `fun _ ↦ 1`.
* `LMLExplore.convex_simplex`: the simplex is convex.
* `LMLExplore.sum_ofReal_mul_le_iSup`: an average `∑ a, w a * x a` of extended nonnegative reals
  with weights `w` of the simplex is at most their supremum.
* `LMLExplore.smul_sub_single_mem_simplex`: removing a mass `s < 1` from an entry of a vector of
  the simplex and rescaling by `(1 - s)⁻¹` stays in the simplex.
* `LMLExplore.sub_single_add_indicator_mem_simplex`: moving a mass `s ≤ w b` from an entry of a
  vector of the simplex to the entries of a nonempty finset, in equal parts, stays in the simplex.
* `LMLExplore.exists_mem_simplex_apply_eq_and_smul_le`: a vector of the simplex with a prescribed
  entry `v_a = β` dominating a multiple `c w` of a vector of the simplex.
* `LMLExplore.isCompact_simplex`: the simplex is compact.
* `LMLExplore.exists_mul_le_inv_sum_inv`, `LMLExplore.eq_inv_div_sum_inv_of_le_mul`: for positive
  weights `c`, every vector `w` of the simplex has an entry with
  `w a c a ≤ (∑ b, (c b)⁻¹)⁻¹`, and the vector proportional to `c⁻¹`
  (`LMLExplore.inv_div_sum_inv_mem_simplex`) is the only one with `w a c a` at least this value
  for all `a`: it is the unique maximizer of `w ↦ min_a w a c a` on the simplex.
* `LMLExplore.sq_dotProduct_le_dotProduct_sq_of_mem_simplex`: Jensen's inequality for the square,
  `(w ⬝ᵥ v) ^ 2 ≤ w ⬝ᵥ v ^ 2` for every vector `w` of the simplex.
* `LMLExplore.sum_sqrt_mul_one_sub_le_sqrt`: `∑ a, √(w a) * (1 - w a) ≤ √(k - 1)` for every
  vector `w` of the simplex, with `k` the cardinality of `α`.
* `LMLExplore.sum_inv_pos`: for positive weights `c` on a nonempty type, `0 < ∑ b, (c b)⁻¹`.
* `LMLExplore.iInf_ofReal_inv_div_sum_inv_mul`: at the vector proportional to `c⁻¹`, the smallest
  weighted entry `min_a w a c a` is `(∑ b, (c b)⁻¹)⁻¹`.
* `LMLExplore.iSup_simplex_iInf_ofReal_mul`: for positive weights `c`,
  `sup_{w ∈ Δ} min_a w a c a = (∑ a, (c a)⁻¹)⁻¹`, in `ℝ≥0∞`.
* `LMLExplore.iSup_iInf_mul_ofReal_le_inv_sum_inv`: for weights `c ∈ [0, ∞]` on a finite set `s`
  of coordinates, `sup_{w ∈ Δ} min_{j ∈ s} c j w j ≤ (∑_{j ∈ s} (c j)⁻¹)⁻¹`, in `ℝ≥0∞`.
* `LMLExplore.abs_div_sum_abs_mem_simplex`, `LMLExplore.sq_sum_abs_lt_sum_sq_div`: for a nonzero
  vector `u`, the vector `|u| / ‖u‖₁` lies in the simplex, and it is the unique minimizer of
  `w ↦ ∑ a, u a² / w a` on the vectors of the simplex that are positive where `u` does not
  vanish, with minimum `‖u‖₁²`.
* `LMLExplore.iSup_simplex_ofReal_dotProduct`: the supremum of `w ↦ w ⬝ᵥ y` over the simplex is
  the supremum of the entries of `y`, in `ℝ≥0∞`.
* `LMLExplore.convex_setOf_nonneg_support_subset_sum_eq_one`: the finitely supported probability
  weights with support in a set form a convex set.
* `LMLExplore.convex_setOf_mem_simplex_apply_eq`, `LMLExplore.isCompact_setOf_mem_simplex_apply_eq`:
  the vectors of the simplex with a prescribed entry `w a = β` form a convex compact set.
-/

public section

namespace LMLExplore

variable {α : Type*} [Fintype α]

variable (α) in
/-- The probability simplex of `α`: vectors `w : α → ℝ` with nonnegative entries summing to `1`. -/
def simplex : Set (α → ℝ) := {w | (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1}

@[simp]
lemma mem_simplex_iff {w : α → ℝ} : w ∈ simplex α ↔ (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1 := Iff.rfl

/-- On a type whose only elements are `a ≠ b`, the entries of a vector `w` of the simplex satisfy
`w a + w b = 1`. -/
lemma add_eq_one_of_mem_simplex {w : α → ℝ} {a b : α} (hab : a ≠ b) (h : ∀ c, c = a ∨ c = b)
    (hw : w ∈ simplex α) : w a + w b = 1 :=
  Fintype.sum_eq_add (f := w) a b hab (fun c hc ↦ absurd (h c) (not_or.2 hc)) ▸ hw.2

lemma simplex_subset_nonneg : simplex α ⊆ Set.Ici 0 := fun _ hw ↦ hw.1

/-- The vertex `Pi.single a 1` of the simplex: the distribution concentrated on `a`. -/
lemma single_mem_simplex [DecidableEq α] (a : α) : Pi.single a 1 ∈ simplex α :=
  ⟨fun b ↦ by by_cases h : b = a <;> simp [h], by simp⟩

variable (α) in
/-- The uniform distribution `fun _ ↦ (card α)⁻¹` on a nonempty type lies in the simplex. -/
lemma uniform_mem_simplex [Nonempty α] : (fun _ ↦ (Fintype.card α : ℝ)⁻¹) ∈ simplex α :=
  ⟨fun _ ↦ by positivity, by simp⟩

variable (α) in
lemma simplex_nonempty [Nonempty α] : (simplex α).Nonempty :=
  ⟨_, uniform_mem_simplex α⟩

variable (α) in
lemma convex_simplex : Convex ℝ (simplex α) := by
  intro w hw v hv a b ha hb hab
  refine ⟨fun x ↦ ?_, ?_⟩
  · simpa using add_nonneg (mul_nonneg ha (hw.1 x)) (mul_nonneg hb (hv.1 x))
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw.2, hv.2, hab]

variable (α) in
lemma isClosed_simplex : IsClosed (simplex α) := by
  have h : simplex α = (⋂ a, {w | 0 ≤ w a}) ∩ {w | ∑ a, w a = 1} := by ext; simp
  rw [h]
  exact (isClosed_iInter fun a ↦ isClosed_le continuous_const (continuous_apply a)).inter
    (isClosed_eq (by fun_prop) continuous_const)

/-- An average `∑ a, w a * x a` of extended nonnegative reals with weights `w` of the simplex is at
most their supremum. -/
lemma sum_ofReal_mul_le_iSup {w : α → ℝ} (hw : w ∈ simplex α) (x : α → ENNReal) :
    ∑ a, ENNReal.ofReal (w a) * x a ≤ ⨆ a, x a :=
  calc ∑ a, ENNReal.ofReal (w a) * x a ≤ ∑ a, ENNReal.ofReal (w a) * ⨆ b, x b :=
        Finset.sum_le_sum fun a _ ↦ by gcongr; exact le_iSup x a
    _ = ⨆ a, x a := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun a _ ↦ hw.1 a, hw.2,
          ENNReal.ofReal_one, one_mul]

/-- A vector of the simplex with an entry equal to `1` is the vertex `Pi.single a 1`. -/
lemma eq_single_of_mem_simplex [DecidableEq α] {w : α → ℝ} (hw : w ∈ simplex α) {a : α}
    (ha : w a = 1) : w = Pi.single a 1 := by
  have h0 : ∑ b ∈ Finset.univ.erase a, w b = 0 := by
    have hsum := (mem_simplex_iff.1 hw).2
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ha] at hsum
    linarith
  ext b
  by_cases hb : b = a
  · simp [hb, ha]
  · simp [hb, (Finset.sum_eq_zero_iff_of_nonneg fun c _ ↦ (mem_simplex_iff.1 hw).1 c).1 h0 b
      (Finset.mem_erase.2 ⟨hb, Finset.mem_univ b⟩)]

omit [Fintype α] in
/-- A set of vertices `Pi.single a 1` of the simplex containing two distinct vertices is not
convex: the midpoint of two distinct vertices is not a vertex. -/
lemma not_convex_image_single [DecidableEq α] {s : Set α} {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) : ¬ Convex ℝ ((fun c ↦ Pi.single c (1 : ℝ)) '' s) := by
  intro h
  obtain ⟨c, -, hc⟩ := h ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hca := congrFun hc a
  by_cases hac : a = c
  · subst hac
    simp [hab] at hca
  · simp [Ne.symm hac, hab] at hca

/-- The entries of a vector of the simplex lie in `[0, 1]`. -/
lemma simplex_subset_Icc : simplex α ⊆ Set.Icc 0 1 := by
  refine fun w hw ↦ ⟨hw.1, fun a ↦ ?_⟩
  simpa [hw.2] using Finset.single_le_sum (fun b _ ↦ hw.1 b) (Finset.mem_univ a)

/-- Removing a mass `s < 1` from an entry `w b ≥ s` of a vector `w` of the simplex and rescaling
by `(1 - s)⁻¹` gives a vector of the simplex. -/
lemma smul_sub_single_mem_simplex [DecidableEq α] {w : α → ℝ} (hw : w ∈ simplex α) {b : α}
    {s : ℝ} (hsb : s ≤ w b) (hs1 : s < 1) : (1 - s)⁻¹ • (w - Pi.single b s) ∈ simplex α := by
  refine ⟨fun c ↦ mul_nonneg (inv_nonneg.2 (sub_nonneg.2 hs1.le)) ?_, ?_⟩
  · by_cases hcb : c = b
    · subst hcb
      simpa using hsb
    · simpa [hcb] using hw.1 c
  · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_pi_single', Finset.mem_univ, ite_true, hw.2]
    field_simp [(sub_pos.2 hs1).ne']

/-- Moving a mass `0 ≤ s ≤ w b` from the entry `b` of a vector `w` of the simplex to the entries
of a nonempty finset `R`, in equal parts `s / #R`, gives a vector of the simplex. -/
lemma sub_single_add_indicator_mem_simplex [DecidableEq α] {w : α → ℝ} (hw : w ∈ simplex α)
    {b : α} {s : ℝ} (hs0 : 0 ≤ s) (hsb : s ≤ w b) {R : Finset α} (hR : R.Nonempty) :
    w - Pi.single b s + (R : Set α).indicator (fun _ ↦ s / R.card) ∈ simplex α := by
  have hr : 0 ≤ s / R.card := div_nonneg hs0 (Nat.cast_nonneg _)
  refine ⟨fun c ↦ add_nonneg ?_ (Set.indicator_nonneg (fun _ _ ↦ hr) c), ?_⟩
  · by_cases hcb : c = b
    · subst hcb
      simpa using hsb
    · simpa [hcb] using hw.1 c
  · simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_pi_single', Finset.mem_univ, ite_true, hw.2,
      Finset.sum_indicator_subset _ R.subset_univ, Finset.sum_const, nsmul_eq_mul]
    field_simp [(Nat.cast_pos.2 hR.card_pos).ne' (α := ℝ)]
    ring

/-- Given a vector `w` of the simplex, an entry `a`, another entry `b ≠ a` and a scalar `c ≥ 0`
with `c w_a ≤ β` and `c (1 - w_a) ≤ 1 - β`, some vector `v` of the simplex has `v_a = β` and
dominates `c w` entrywise: it adds the missing mass `β - c w_a` to the entry `a` and the rest to
the entry `b`. -/
lemma exists_mem_simplex_apply_eq_and_smul_le {w : α → ℝ} (hw : w ∈ simplex α) {a b : α}
    (hab : b ≠ a) {c β : ℝ} (hc : 0 ≤ c) (hca : c * w a ≤ β) (hcb : c * (1 - w a) ≤ 1 - β) :
    ∃ v ∈ simplex α, v a = β ∧ c • w ≤ v := by
  classical
  have h₁ : 0 ≤ β - c * w a := sub_nonneg.2 hca
  have h₂ : 0 ≤ 1 - β - c * (1 - w a) := by linarith
  set v := c • w + Pi.single a (β - c * w a) + Pi.single b (1 - β - c * (1 - w a)) with hv
  have hle : c • w ≤ v := fun x ↦ by
    have h (y : α) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ (Pi.single y r : α → ℝ) x := by
      rw [Pi.single_apply]; split_ifs <;> simp [hr]
    simp only [hv, Pi.add_apply]
    linarith [h a h₁, h b h₂]
  refine ⟨v, ⟨fun x ↦ (mul_nonneg hc (hw.1 x)).trans (hle x), ?_⟩, ?_, hle⟩
  · simp only [hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hw.2, Finset.sum_pi_single', Finset.mem_univ, ite_true]
    ring
  · simp [hv, hab.symm]

variable (α) in
lemma isCompact_simplex : IsCompact (simplex α) :=
  isCompact_Icc.of_isClosed_subset (isClosed_simplex α) simplex_subset_Icc

/-- The finitely supported probability weights with support in a set `s`, the weights of the
elements of Mathlib's `Convexity.StdSimplex 𝕜 β` supported in `s`, form a convex set. -/
lemma convex_setOf_nonneg_support_subset_sum_eq_one {𝕜 β : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [IsOrderedRing 𝕜] (s : Set β) :
    Convex 𝕜 {q : β →₀ 𝕜 | 0 ≤ q ∧ ↑q.support ⊆ s ∧ q.sum (fun _ r ↦ r) = 1} := by
  classical
  intro q₁ hq₁ q₂ hq₂ b₁ b₂ hb₁ hb₂ hb
  refine ⟨fun x ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · simpa using add_nonneg (mul_nonneg hb₁ (hq₁.1 x)) (mul_nonneg hb₂ (hq₂.1 x))
  · rcases Finset.mem_union.1 (Finsupp.support_add hx) with h | h
    exacts [hq₁.2.1 (Finsupp.support_smul h), hq₂.2.1 (Finsupp.support_smul h)]
  · simp [Finsupp.sum_add_index', Finsupp.sum_smul_index, ← Finsupp.mul_sum, hq₁.2.2, hq₂.2.2, hb]

/-! ### The vectors of the simplex with a prescribed entry -/

/-- The vectors of the simplex with a prescribed entry `w a = β` form a convex set. -/
lemma convex_setOf_mem_simplex_apply_eq (a : α) (β : ℝ) :
    Convex ℝ {w ∈ simplex α | w a = β} :=
  (convex_simplex α).inter (convex_hyperplane (LinearMap.proj a : (α → ℝ) →ₗ[ℝ] ℝ).isLinear β)

lemma isClosed_setOf_mem_simplex_apply_eq (a : α) (β : ℝ) :
    IsClosed {w ∈ simplex α | w a = β} :=
  (isClosed_simplex α).inter (isClosed_eq (continuous_apply a) continuous_const)

/-- The vectors of the simplex with a prescribed entry `w a = β` form a compact set. -/
lemma isCompact_setOf_mem_simplex_apply_eq (a : α) (β : ℝ) :
    IsCompact {w ∈ simplex α | w a = β} :=
  (isCompact_simplex α).of_isClosed_subset (isClosed_setOf_mem_simplex_apply_eq a β)
    (Set.sep_subset _ _)

/-! ### Linear functions and the smallest weighted entry on the simplex -/

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

variable {w c : α → ℝ}

/-- A type whose simplex has an element is nonempty. -/
lemma nonempty_of_mem_simplex (hw : w ∈ simplex α) : Nonempty α := by
  by_contra h
  rw [not_nonempty_iff] at h
  simpa using hw.2

/-- On a type with at most one element, the only point of the simplex is the constant `1`. -/
lemma eq_one_of_mem_simplex [Subsingleton α] (hw : w ∈ simplex α) : w = fun _ ↦ 1 := by
  funext a
  rw [← hw.2, Fintype.sum_subsingleton _ a]

/-- An average `∑ a, w a * c a` of positive values `c` with weights `w` of the simplex is
positive. -/
lemma sum_mul_pos_of_mem_simplex (hw : w ∈ simplex α) (hc : ∀ a, 0 < c a) :
    0 < ∑ a, w a * c a := by
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hw.2.trans_ne one_ne_zero)
  exact Finset.sum_pos' (fun b _ ↦ mul_nonneg (hw.1 b) (hc b).le)
    ⟨a, Finset.mem_univ a, mul_pos ((hw.1 a).lt_of_ne' ha) (hc a)⟩

/-- **Jensen's inequality for the square on the simplex**: the square of an average `w ⬝ᵥ v` with
weights `w` of the simplex is at most the average `w ⬝ᵥ v ^ 2` of the squares. -/
lemma sq_dotProduct_le_dotProduct_sq_of_mem_simplex (hw : w ∈ simplex α) (v : α → ℝ) :
    (w ⬝ᵥ v) ^ 2 ≤ w ⬝ᵥ v ^ 2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ (r := fun a ↦ w a * v a)
    (fun a _ ↦ hw.1 a) (fun a _ ↦ mul_nonneg (hw.1 a) (sq_nonneg (v a)))
    (fun a _ ↦ by rw [mul_pow, sq, mul_assoc])
  rwa [hw.2, one_mul] at h

/-- For every vector `w` of the simplex, `∑ a, √(w a) * (1 - w a) ≤ √(k - 1)`, with `k` the
cardinality of `α`: by the Cauchy–Schwarz inequality, the square of the sum is at most
`(∑ a, w a) * ∑ a, (1 - w a) ^ 2 ≤ k - 1`. -/
lemma sum_sqrt_mul_one_sub_le_sqrt (hw : w ∈ simplex α) :
    ∑ a, √(w a) * (1 - w a) ≤ √((Fintype.card α : ℝ) - 1) := by
  have hw1 := simplex_subset_Icc hw
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun a ↦ √(w a) * (1 - w a)) (g := fun a ↦ (1 - w a) ^ 2) (fun a _ ↦ hw.1 a)
    (fun a _ ↦ sq_nonneg _) (fun a _ ↦ by rw [mul_pow, Real.sq_sqrt (hw.1 a)])
  rw [hw.2, one_mul] at h
  have h2 : ∑ a, (1 - w a) ^ 2 ≤ (Fintype.card α : ℝ) - 1 := by
    calc ∑ a, (1 - w a) ^ 2 ≤ ∑ a, (1 - w a) := Finset.sum_le_sum fun a _ ↦ by
          have h0 : 0 ≤ w a := hw.1 a
          have h1 : w a ≤ 1 := hw1.2 a
          nlinarith [mul_nonneg h0 (sub_nonneg.2 h1)]
    _ = (Fintype.card α : ℝ) - 1 := by simp [Finset.sum_sub_distrib, hw.2]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (h.trans h2))

/-- For positive weights `c` on a nonempty type, the sum of the inverses `∑ b, (c b)⁻¹` is
positive. -/
lemma sum_inv_pos [Nonempty α] (hc : ∀ a, 0 < c a) : 0 < ∑ b, (c b)⁻¹ :=
  Finset.sum_pos (fun b _ ↦ inv_pos.2 (hc b)) Finset.univ_nonempty

/-- For positive weights `c` on a nonempty type, the vector proportional to the inverses `c⁻¹`
belongs to the simplex. -/
lemma inv_div_sum_inv_mem_simplex [Nonempty α] (hc : ∀ a, 0 < c a) :
    (fun a ↦ (c a)⁻¹ / ∑ b, (c b)⁻¹) ∈ simplex α := by
  have hs := sum_inv_pos hc
  exact ⟨fun a ↦ div_nonneg (inv_pos.2 (hc a)).le hs.le, by rw [← Finset.sum_div, div_self hs.ne']⟩

/-- For positive weights `c`, every vector `w` of the simplex has an entry with
`w a c a ≤ (∑ b, (c b)⁻¹)⁻¹`: the smallest weighted entry `min_a w a c a` is at most
`(∑ b, (c b)⁻¹)⁻¹`. -/
lemma exists_mul_le_inv_sum_inv (hw : w ∈ simplex α) (hc : ∀ a, 0 < c a) :
    ∃ a, w a * c a ≤ (∑ b, (c b)⁻¹)⁻¹ := by
  have := nonempty_of_mem_simplex hw
  have hs := sum_inv_pos hc
  -- Since `∑ a, w a = 1 = ∑ a, (c a)⁻¹ / s`, some entry has `w a ≤ (c a)⁻¹ / s`.
  obtain ⟨a, -, ha⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty
    (f := w) (g := fun a ↦ (c a)⁻¹ / ∑ b, (c b)⁻¹)
    (by rw [hw.2, (inv_div_sum_inv_mem_simplex hc).2])
  refine ⟨a, (mul_le_mul_of_nonneg_right ha (hc a).le).trans_eq ?_⟩
  field_simp [(hc a).ne']

/-- For positive weights `c`, the only vector `w` of the simplex with
`(∑ b, (c b)⁻¹)⁻¹ ≤ w a c a` for every `a` is the vector proportional to `c⁻¹`. -/
lemma eq_inv_div_sum_inv_of_le_mul (hw : w ∈ simplex α) (hc : ∀ a, 0 < c a)
    (h : ∀ a, (∑ b, (c b)⁻¹)⁻¹ ≤ w a * c a) : w = fun a ↦ (c a)⁻¹ / ∑ b, (c b)⁻¹ := by
  have := nonempty_of_mem_simplex hw
  have hs := sum_inv_pos hc
  -- Each entry is at least `(c a)⁻¹ / s`, and both vectors sum to `1`.
  have hle (a : α) : (c a)⁻¹ / ∑ b, (c b)⁻¹ ≤ w a := by
    rw [div_eq_inv_mul, ← le_div_iff₀ (inv_pos.2 (hc a)), div_inv_eq_mul]
    exact h a
  have h_eq := (Finset.sum_eq_sum_iff_of_le fun a _ ↦ hle a).1
    (by rw [(inv_div_sum_inv_mem_simplex hc).2, hw.2])
  exact funext fun a ↦ (h_eq a (Finset.mem_univ a)).symm

/-- For positive weights `c`, at the vector proportional to `c⁻¹` all the weighted entries
`w a c a` equal `(∑ b, (c b)⁻¹)⁻¹`, and so does their infimum, in `ℝ≥0∞`. -/
lemma iInf_ofReal_inv_div_sum_inv_mul [Nonempty α] (hc : ∀ a, 0 < c a) :
    ⨅ a, ENNReal.ofReal ((c a)⁻¹ / (∑ b, (c b)⁻¹) * c a) =
      ENNReal.ofReal (∑ b, (c b)⁻¹)⁻¹ := by
  have h (a : α) : ENNReal.ofReal ((c a)⁻¹ / (∑ b, (c b)⁻¹) * c a) =
      ENNReal.ofReal (∑ b, (c b)⁻¹)⁻¹ := by
    congr 1
    field_simp [(hc a).ne']
  simp_rw [h]
  exact iInf_const

/-- **Maximin of a weighted minimum over the simplex**: for positive weights `c`,
`max_{w ∈ Δ} min_a w a c a = (∑ a, (c a)⁻¹)⁻¹`, in `ℝ≥0∞`. On a nonempty type the maximum is
attained at the vector proportional to `c⁻¹` (`iInf_ofReal_inv_div_sum_inv_mul`), and only there
(`eq_inv_div_sum_inv_of_le_mul`). -/
lemma iSup_simplex_iInf_ofReal_mul (hc : ∀ a, 0 < c a) :
    ⨆ w ∈ simplex α, ⨅ a, ENNReal.ofReal (w a * c a) = ENNReal.ofReal (∑ a, (c a)⁻¹)⁻¹ := by
  rcases isEmpty_or_nonempty α with hα | hα
  · have h : simplex α = ∅ :=
      Set.eq_empty_of_forall_notMem fun w hw ↦ by simpa using (mem_simplex_iff.1 hw).2
    simp [h]
  refine le_antisymm (iSup₂_le fun w hw ↦ ?_) ?_
  · obtain ⟨a, ha⟩ := exists_mul_le_inv_sum_inv hw hc
    exact (iInf_le _ a).trans (ENNReal.ofReal_le_ofReal ha)
  · exact (iInf_ofReal_inv_div_sum_inv_mul hc).symm.le.trans
      (le_iSup₂ (f := fun w _ ↦ ⨅ a, ENNReal.ofReal (w a * c a)) _
        (inv_div_sum_inv_mem_simplex hc))

/-- **Maximin of weighted entries over the simplex**: for weights `c j ∈ [0, ∞]` on a finite set
`s` of coordinates, every vector `w` of the simplex has
`min_{j ∈ s} c j w j ≤ (∑_{j ∈ s} (c j)⁻¹)⁻¹`, in `ℝ≥0∞`. For positive finite weights on all the
coordinates, the bound is attained at the vector proportional to `c⁻¹`
(`iInf_ofReal_inv_div_sum_inv_mul`). -/
lemma iSup_iInf_mul_ofReal_le_inv_sum_inv (s : Finset α) (c : α → ENNReal) :
    ⨆ w ∈ simplex α, ⨅ j ∈ s, c j * ENNReal.ofReal (w j) ≤ (∑ j ∈ s, (c j)⁻¹)⁻¹ := by
  refine iSup₂_le fun w hw ↦ ENNReal.le_inv_iff_mul_le.2 ?_
  rw [Finset.mul_sum]
  calc ∑ j ∈ s, (⨅ j ∈ s, c j * ENNReal.ofReal (w j)) * (c j)⁻¹
      ≤ ∑ j ∈ s, ENNReal.ofReal (w j) := Finset.sum_le_sum fun j hj ↦
        calc (⨅ j ∈ s, c j * ENNReal.ofReal (w j)) * (c j)⁻¹
            ≤ c j * ENNReal.ofReal (w j) * (c j)⁻¹ := by gcongr; exact iInf₂_le j hj
          _ = ENNReal.ofReal (w j) * (c j * (c j)⁻¹) := by ring
          _ ≤ ENNReal.ofReal (w j) := mul_le_of_le_one_right' (ENNReal.mul_inv_le_one _)
    _ ≤ ∑ j, ENNReal.ofReal (w j) := Finset.sum_le_sum_of_subset (Finset.subset_univ s)
    _ = 1 := by rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hw.1 j, hw.2, ENNReal.ofReal_one]

/-! ### The vector proportional to `|u|` -/

variable {u : α → ℝ}

/-- For a nonzero vector `u`, the `ℓ¹` norm `∑ a, |u a|` is nonzero. -/
lemma sum_abs_ne_zero (hu : u ≠ 0) : ∑ a, |u a| ≠ 0 := fun h ↦
  hu <| funext fun a ↦ abs_eq_zero.1
    ((Finset.sum_eq_zero_iff_of_nonneg fun a _ ↦ abs_nonneg (u a)).1 h a (Finset.mem_univ a))

/-- For a nonzero vector `u`, the vector `|u| / ‖u‖₁` proportional to `|u|` belongs to the
simplex. -/
lemma abs_div_sum_abs_mem_simplex (hu : u ≠ 0) :
    (fun a ↦ |u a| / ∑ b, |u b|) ∈ simplex α := by
  refine ⟨fun a ↦ div_nonneg (abs_nonneg _) (Finset.sum_nonneg fun b _ ↦ abs_nonneg _), ?_⟩
  rw [← Finset.sum_div, div_self (sum_abs_ne_zero hu)]

/-- The identity `∑ a, (|u a| - ‖u‖₁ w a)² / w a = ∑ a, u a² / w a - ‖u‖₁²` for a vector `w` of the
simplex that is positive where `u` does not vanish: its left-hand side is nonnegative and, for
`u ≠ 0`, vanishes only at `w = |u| / ‖u‖₁`. -/
lemma sum_sq_abs_sub_mul_div_eq (hw : w ∈ simplex α) (hwu : ∀ a, w a = 0 → u a = 0) :
    ∑ a, (|u a| - (∑ b, |u b|) * w a) ^ 2 / w a =
      ∑ a, u a ^ 2 / w a - (∑ b, |u b|) ^ 2 := by
  set L := ∑ b, |u b|
  have h_term (a : α) :
      (|u a| - L * w a) ^ 2 / w a = u a ^ 2 / w a - 2 * L * |u a| + L ^ 2 * w a := by
    rcases eq_or_ne (w a) 0 with h | h
    · simp [h, hwu a h]
    · rw [sub_sq, sq_abs]
      field_simp
  rw [Finset.sum_congr rfl fun a _ ↦ h_term a, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, (mem_simplex_iff.1 hw).2]
  ring

/-- For a nonzero vector `u` and a vector `w` of the simplex that is positive where `u` does not
vanish, `‖u‖₁² < ∑ a, u a² / w a` unless `w = |u| / ‖u‖₁`: the vector `|u| / ‖u‖₁` is the unique
minimizer of `w ↦ ∑ a, u a² / w a` on the vectors of the simplex that are positive where `u` does
not vanish. -/
lemma sq_sum_abs_lt_sum_sq_div (hu : u ≠ 0) (hw : w ∈ simplex α)
    (hwu : ∀ a, w a = 0 → u a = 0) (hne : w ≠ fun a ↦ |u a| / ∑ b, |u b|) :
    (∑ a, |u a|) ^ 2 < ∑ a, u a ^ 2 / w a := by
  have h_nonneg (a : α) : 0 ≤ (|u a| - (∑ b, |u b|) * w a) ^ 2 / w a :=
    div_nonneg (sq_nonneg _) (hw.1 a)
  rw [← sub_pos, ← sum_sq_abs_sub_mul_div_eq hw hwu]
  refine (Finset.sum_nonneg fun a _ ↦ h_nonneg a).lt_of_ne fun h ↦ hne (funext fun a ↦ ?_)
  have ha := (Finset.sum_eq_zero_iff_of_nonneg fun a _ ↦ h_nonneg a).1 h.symm a
    (Finset.mem_univ a)
  rcases div_eq_zero_iff.1 ha with ha | ha
  · rw [eq_div_iff (sum_abs_ne_zero hu)]
    linarith [pow_eq_zero_iff two_ne_zero |>.1 ha]
  · rw [ha, hwu a ha, abs_zero, zero_div]

end LMLExplore
