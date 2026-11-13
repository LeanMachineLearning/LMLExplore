/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Caratheodory
public import LMLExplore.Analysis.InnerProductSpace.MoorePenrose
public import LMLExplore.Analysis.InnerProductSpace.Positive
public import LMLExplore.Analysis.InnerProductSpace.RankOne
public import LMLExplore.Analysis.InnerProductSpace.Symmetric.Finrank
public import LMLExplore.LinearAlgebra.AffineSpace.Independent
public import LMLExplore.Geometry.Convex.ConvexSpace.Defs
public import LMLExplore.Topology.Algebra.Module.Determinant
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import TauCeti.Analysis.InnerProductSpace.Spectrum

/-!
# Optimal designs and the Kiefer–Wolfowitz theorem

A *design* on a set `𝒜` of a real inner product space `E` is a finitely supported probability
measure `w` on `E` with support in `𝒜`, an element of Mathlib's `Convexity.StdSimplex ℝ E` with
`↑w.weights.support ⊆ 𝒜`; finite support is what compact infinite sets need [LS, Exercise 21.3].
Its *design operator* is `V(w) = ∑_a w a • a ⊗ a`, where `a ⊗ a = rankOne ℝ a a` is the operator
`v ↦ ⟪a, v⟫ • a`. Least squares on a fixed design that repeats each point `b` in proportion to
`w b` estimates `⟪a, θ⟫` with a variance proportional to `‖a‖²_{V(w)⁻¹} = ⟪a, V(w)⁻¹ a⟫`, so a
good design makes
`g(w) = sup_{a ∈ 𝒜} ⟪a, V(w)⁻¹ a⟫` small: a *G-optimal design* minimizes `g`. It is the
exploration distribution of phased elimination and of the exploration of adversarial linear
bandits [LS, Chapters 21, 22 and 27].

On a space of dimension `d`, every design with invertible `V(w)` has `∑_a w a ⟪a, V(w)⁻¹ a⟫ = d`,
the trace of `V(w)⁻¹ V(w)`, so `g(w) ≥ d`. The **Kiefer–Wolfowitz theorem** [LS, Theorem 21.1]
states that `g(w) = d` is attained when `𝒜` is compact and spans `E`. The design is obtained as a
*D-optimal design*, a maximizer of `det V(w)`: the design operators of the designs on `𝒜` are the
convex hull of the compact set `{a ⊗ a | a ∈ 𝒜}`, which is compact, and moving a maximizer `w`
towards the Dirac mass at `a ∈ 𝒜` cannot increase the determinant. By the matrix determinant lemma
this gives `1 + s ⟪a, V(w)⁻¹ a⟫ ≤ (1 + s) ^ d` for `s > 0`, and the derivative at `s = 0` gives
`⟪a, V(w)⁻¹ a⟫ ≤ d`. When `𝒜` spans only a subspace `K` of dimension `m`, the theorem applied in
`K` gives a design whose G-value, computed with the Moore–Penrose inverse `V(w)⁺` on `E`, is at
most `m` [LS, Exercise 21.6].

Conversely, a design `w` with `⟪a, V(w)⁻¹ a⟫ ≤ d` on `𝒜` is D-optimal: for every design `w'` on
`𝒜`, the AM-GM inequality for the eigenvalues of `V(w)^{-1/2} V(w') V(w)^{-1/2}` gives
`det V(w') ≤ det V(w) (trace (V(w)⁻¹ V(w')) / d) ^ d`, and the trace is
`∑_a w' a ⟪a, V(w)⁻¹ a⟫ ≤ d`. With the G-value `g(w)` taken to be `∞` when some `a ∈ 𝒜` lies
outside the span of the support of `w`, this gives the **equivalence theorem** [LS, Theorem 21.1]:
for a compact set `𝒜` spanning `E`, a design on `𝒜` minimizes `g` iff it maximizes `det V` iff
`g(w) = d`.

The optimal design can be chosen with at most `d (d + 1) / 2` support points [LS, Theorem 21.1],
which bounds the number of distinct actions that phased elimination plays in a phase. If
`⟪a, V(w)⁻¹ a⟫ ≤ d` on the support of `w`, then `⟪a, V(w)⁻¹ a⟫ = d` there, so the rank-one
operators `a ⊗ a` of the support lie on the hyperplane `{X | trace (V(w)⁻¹ X) = d}`, which does not
pass through `0`. By Carathéodory's theorem `V(w)` is a convex combination of affinely independent
such operators; on that hyperplane they are linearly independent, and they are symmetric, so there
are at most `d (d + 1) / 2` of them, the dimension of the space of symmetric operators. Choosing one
point `a` for each of them gives a design with the same design operator, hence the same G-value.

## Main definitions

* `LMLExplore.designOperator w`: the design operator `V(w) = ∑_a w a • a ⊗ a` of `w`.
* `LMLExplore.gValue 𝒜 w`: the G-value `g(w) = sup_{a ∈ 𝒜} ⟪a, V(w)⁺ a⟫` in `ℝ≥0∞`, where a point
  of `𝒜` outside the range of `V(w)` contributes `∞`.

## Main statements

* `LMLExplore.designOperator_map`: the design operator of the image `w.map φ` of a design on a
  finite type of arms by a feature map `φ` is `∑ i, w i • φ i ⊗ φ i`.
* `LMLExplore.isPositive_sum_smul_rankOne`, `LMLExplore.smul_sum_smul_rankOne_le`,
  `LMLExplore.isUnit_sum_smul_rankOne_of_mul_le`: for a feature map `φ`, the weighted sum
  `∑ i ∈ s, w i • φ i ⊗ φ i` is positive for nonnegative weights (on a finite type, monotone in
  the weights in the Loewner order, and invertible above an invertible one).
* `LMLExplore.sum_mul_inner_ringInverse_sum_smul_rankOne`: for a feature map `φ` and real weights
  `w` with `V = ∑ i ∈ s, w i • φ i ⊗ φ i` invertible, `∑ i ∈ s, w i ⟪φ i, V⁻¹ φ i⟫ = d`. The
  corresponding facts for the design operator are the case of the identity feature map on the
  support of the design.
* `LMLExplore.designOperator_map_subtype_apply`: on a subspace `K`, the design operator on `E` of
  a design on `K` restricts to its design operator on `K`.
* `LMLExplore.designOperator_convexCombPair`: `V(w)` is affine in `w`.
* `LMLExplore.mem_convexHull_image_rankOne_iff`: the convex hull of `{a ⊗ a | a ∈ 𝒜}` is the set
  of design operators of the designs on `𝒜`.
* `LMLExplore.ker_designOperator`, `LMLExplore.range_designOperator`,
  `LMLExplore.isUnit_designOperator_iff`: the kernel of `V(w)` is the orthogonal complement of the
  span of the support of `w`, its range is that span, and `V(w)` is invertible iff the support
  spans `E`; `LMLExplore.det_designOperator_pos`: then `det V(w) > 0`.
* `LMLExplore.trace_comp_designOperator`: `trace (B V(w)) = ∑_a w a ⟪a, B a⟫`; hence
  `LMLExplore.sum_mul_inner_ringInverse_designOperator`: `∑_a w a ⟪a, V(w)⁻¹ a⟫ = d`.
* `LMLExplore.exists_mem_support_finrank_le_inner_ringInverse_designOperator`: every design with
  invertible `V(w)` has a support point with `d ≤ ⟪a, V(w)⁻¹ a⟫`, so `g(w) ≥ d`.
* `LMLExplore.inner_ringInverse_designOperator_eq_finrank`: if `⟪a, V(w)⁻¹ a⟫ ≤ d` on the support
  of `w`, equality holds there [LS, Exercise 21.5].
* `LMLExplore.inner_ringInverse_designOperator_le_finrank_of_isMaxOn`: a D-optimal design on `𝒜`
  with invertible design operator has `⟪a, V(w)⁻¹ a⟫ ≤ d` for every `a ∈ 𝒜`.
* `LMLExplore.isMaxOn_det_designOperator_of_inner_ringInverse_le_finrank`: conversely, a design
  with invertible design operator and `⟪a, V(w)⁻¹ a⟫ ≤ d` for every `a ∈ 𝒜` is D-optimal on `𝒜`
  [LS, Theorem 21.1].
* `LMLExplore.exists_design_inner_ringInverse_le_finrank`: **Kiefer–Wolfowitz** [LS, Theorem 21.1,
  Exercise 21.3]: a nonempty compact set `𝒜` spanning `E` carries a design `w` with invertible
  design operator and `⟪a, V(w)⁻¹ a⟫ ≤ d` for every `a ∈ 𝒜`.
* `LMLExplore.exists_mem_simplex_inner_ringInverse_le_finrank`: **Kiefer–Wolfowitz for finitely
  many arms**: if the features `φ i` of finitely many arms span `E`, some weights `w` in the
  simplex have `⟪φ i, V⁻¹ φ i⟫ ≤ d` for every arm, with `V = ∑ i, w i • φ i ⊗ φ i` invertible.
* `LMLExplore.inner_moorePenroseInverse_designOperator_map_subtype`: for a design on a subspace
  `K` with invertible design operator `V_K(w)` on `K`, `⟪a, V(w)⁺ a⟫ = ⟪a, V_K(w)⁻¹ a⟫` on `K`.
* `LMLExplore.exists_designOperator_eq_card_support_le`: a design with invertible design operator
  and `⟪a, V(w)⁻¹ a⟫ ≤ d` on its support has the design operator of a design supported in its
  support with at most `d (d + 1) / 2` points [LS, Theorem 21.1].
* `LMLExplore.exists_design_inner_ringInverse_le_finrank_and_card_support_le`: **Kiefer–Wolfowitz
  with the support bound** [LS, Theorem 21.1]: the design of
  `exists_design_inner_ringInverse_le_finrank` can be chosen with at most `d (d + 1) / 2` support
  points.
* `LMLExplore.exists_design_inner_moorePenroseInverse_le_finrank_and_card_support_le`:
  **Kiefer–Wolfowitz on the span with the support bound** [LS, Exercise 21.6]: if the span of a
  compact set `𝒜` has dimension `m ≥ 1`, then `𝒜` carries a design whose support spans the span of
  `𝒜` and has at most `m (m + 1) / 2` points, with `⟪a, V(w)⁺ a⟫ ≤ m` on `𝒜` and equality on the
  support.
* `LMLExplore.exists_design_inner_moorePenroseInverse_le_finrank`: **Kiefer–Wolfowitz on the
  span** [LS, Exercise 21.6]: a nonempty compact set `𝒜` carries a design `w` whose support spans
  the span of `𝒜`, with `⟪a, V(w)⁺ a⟫ ≤ dim (span 𝒜)` for every `a ∈ 𝒜`.
* `LMLExplore.exists_design_map_inner_moorePenroseInverse_le_finrank`: the same for a design on a
  nonempty finite set `S` of arms with features `φ`: the features of `S` lie in the range of the
  design operator `V` of the image design, and `⟪φ i, V⁺ φ i⟫ ≤ dim (span (φ '' S))` on `S`.
* `LMLExplore.finrank_le_gValue`: if `𝒜` spans `E`, every design on `𝒜` has `d ≤ g(w)`;
  `LMLExplore.exists_gValue_eq_finrank`: on a nonempty compact spanning set, `g(w) = d` is
  attained.
* `LMLExplore.tfae_isMinOn_gValue_isMaxOn_det_designOperator`: **the Kiefer–Wolfowitz equivalence
  theorem** [LS, Theorem 21.1]: on a compact set spanning `E`, a design is G-optimal iff it is
  D-optimal iff its G-value is `d`.
* `LMLExplore.designOperator_map_barycenter`,
  `LMLExplore.inner_ringInverse_designOperator_map_barycenter`: the uniform design on an
  orthonormal basis `b` of `E` has design operator `V = d⁻¹ • 1`, so `⟪a, V⁻¹ a⟫ = d ‖a‖²`;
  `LMLExplore.gValue_map_barycenter`: its G-value on `𝒜` is `d sup_{a ∈ 𝒜} ‖a‖²`.
* `LMLExplore.gValue_map_barycenter_eq_finrank`, `LMLExplore.isMinOn_gValue_map_barycenter`: on a
  set `𝒜` containing `b` and contained in the closed unit ball, such as the unit sphere or the
  basis itself (the standard basis of `EuclideanSpace ℝ ι` for `EuclideanSpace.basisFun`), the
  uniform design on `b` has G-value `d` and is G-optimal.

The proof of the Kiefer–Wolfowitz theorem follows `exists_isGOptimalDesign` of the
`colt-2026-83` project (Rémy Degenne, <https://github.com/RemyDegenne/colt-2026-83>), stated
there for matrices on `EuclideanSpace ℝ ι`, restated here for operators and finitely supported
probability measures.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 21.
* J. Kiefer and J. Wolfowitz, *The equivalence of two extremum problems*, Canad. J. Math. 12
  (1960).
-/

public section

open ContinuousLinearMap InnerProductSpace Module Filter Convexity
open scoped ENNReal InnerProductSpace Topology Finset

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **design operator** `V(w) = ∑_a w a • a ⊗ a` of a finitely supported probability measure
`w` on `E`, where `a ⊗ a` is the rank-one operator `v ↦ ⟪a, v⟫ • a`. -/
noncomputable def designOperator (w : StdSimplex ℝ E) : E →L[ℝ] E :=
  Finsupp.linearCombination ℝ (fun a : E ↦ rankOne ℝ a a) w.weights

/-- The design operator is the sum of the rank-one operators of the support points, weighted by
`w`. -/
theorem designOperator_def (w : StdSimplex ℝ E) :
    designOperator w = w.weights.sum fun a c ↦ c • rankOne ℝ a a :=
  Finsupp.linearCombination_apply ℝ w.weights

/-- Evaluation of the design operator: `V(w) v = ∑_a w a • ⟪a, v⟫ • a`. -/
theorem designOperator_apply (w : StdSimplex ℝ E) (v : E) :
    designOperator w v = w.weights.sum fun a c ↦ c • ⟪a, v⟫_ℝ • a := by
  simp [designOperator_def, Finsupp.sum, sum_apply]

/-- The quadratic form of the design operator: `⟪v, V(w) v⟫ = ∑_a w a * ⟪a, v⟫²`. -/
theorem inner_designOperator_apply_self (w : StdSimplex ℝ E) (v : E) :
    ⟪v, designOperator w v⟫_ℝ = w.weights.sum fun a c ↦ c * ⟪a, v⟫_ℝ ^ 2 := by
  rw [designOperator_apply, Finsupp.sum, inner_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [real_inner_smul_right, real_inner_comm a v]
  ring

/-- The design operator of the Dirac mass at `a` is `a ⊗ a`. -/
@[simp]
theorem designOperator_single (a : E) :
    designOperator (StdSimplex.single a : StdSimplex ℝ E) = rankOne ℝ a a := by
  simp [designOperator]

/-- The design operator is affine: the design operator of the convex combination of two designs is
the convex combination of their design operators. -/
@[simp]
theorem designOperator_convexCombPair (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (w w' : StdSimplex ℝ E) :
    designOperator (convexCombPair s t hs ht hst w w') =
      s • designOperator w + t • designOperator w' := by
  simp [designOperator]

/-- The design operator of the image of a design on a finite type of arms by a feature map `φ`
is `∑ i, w i • φ i ⊗ φ i`: allocations on finitely many arms are designs on their features. -/
@[simp]
theorem designOperator_map {ι : Type*} [Fintype ι] (φ : ι → E) (w : StdSimplex ℝ ι) :
    designOperator (w.map φ) = ∑ i, w.weights i • rankOne ℝ (φ i) (φ i) := by
  rw [designOperator, StdSimplex.weights_map, Finsupp.linearCombination_mapDomain,
    Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ fun _ ↦ by simp]
  rfl

/-- The trace of `B ∘ ∑ i ∈ s, w i • φ i ⊗ φ i` is `∑ i ∈ s, w i * ⟪φ i, B (φ i)⟫`, for every
family of real coefficients `w`. -/
theorem trace_comp_sum_smul_rankOne [FiniteDimensional ℝ E] {ι : Type*} (s : Finset ι)
    (B : E →L[ℝ] E) (φ : ι → E) (w : ι → ℝ) :
    LinearMap.trace ℝ E (B ∘L ∑ i ∈ s, w i • rankOne ℝ (φ i) (φ i) : E →ₗ[ℝ] E) =
      ∑ i ∈ s, w i * ⟪φ i, B (φ i)⟫_ℝ := by
  simp [comp_finsetSum, comp_rankOne, trace_rankOne]

/-- If `V = ∑ i ∈ s, w i • φ i ⊗ φ i` is invertible on a space of dimension `d`, then
`∑ i ∈ s, w i * ⟪φ i, V⁻¹ φ i⟫ = d`, the trace of `V⁻¹ V`. For weights `w` in the simplex of a
finite type, `V` is the design operator of the image design `w.map φ` (`designOperator_map`). -/
theorem sum_mul_inner_ringInverse_sum_smul_rankOne [FiniteDimensional ℝ E] {ι : Type*}
    {s : Finset ι} {φ : ι → E} {w : ι → ℝ}
    (hu : IsUnit (∑ i ∈ s, w i • rankOne ℝ (φ i) (φ i))) :
    ∑ i ∈ s, w i * ⟪φ i, Ring.inverse (∑ i ∈ s, w i • rankOne ℝ (φ i) (φ i)) (φ i)⟫_ℝ =
      finrank ℝ E := by
  rw [← trace_comp_sum_smul_rankOne, ← mul_def, Ring.inverse_mul_cancel _ hu, toLinearMap_one,
    LinearMap.trace_one]

/-- For weights `w` nonnegative on `s`, `∑ i ∈ s, w i • φ i ⊗ φ i` is positive. -/
theorem isPositive_sum_smul_rankOne {ι : Type*} (s : Finset ι) (φ : ι → E) {w : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) : (∑ i ∈ s, w i • rankOne ℝ (φ i) (φ i)).IsPositive :=
  isPositive_sum _ fun i hi ↦ (isPositive_rankOne_self (φ i)).smul_of_nonneg (hw i hi)

/-- If `c * v i ≤ w i` for every `i`, then `c • ∑ i, v i • φ i ⊗ φ i ≤ ∑ i, w i • φ i ⊗ φ i` in
the Loewner order. -/
theorem smul_sum_smul_rankOne_le {ι : Type*} [Fintype ι] {φ : ι → E} {v w : ι → ℝ} {c : ℝ}
    (h : ∀ i, c * v i ≤ w i) :
    c • ∑ i, v i • rankOne ℝ (φ i) (φ i) ≤ ∑ i, w i • rankOne ℝ (φ i) (φ i) := by
  rw [ContinuousLinearMap.le_def, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine isPositive_sum _ fun i _ ↦ ?_
  rw [smul_smul, ← sub_smul]
  exact (isPositive_rankOne_self (φ i)).smul_of_nonneg (sub_nonneg.2 (h i))

/-- If `∑ i, v i • φ i ⊗ φ i` is invertible for nonnegative weights `v`, and `c * v i ≤ w i` for
every `i` with `c > 0`, then `∑ i, w i • φ i ⊗ φ i` is invertible. -/
theorem isUnit_sum_smul_rankOne_of_mul_le [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    {φ : ι → E} {v w : ι → ℝ} {c : ℝ} (hv : ∀ i, 0 ≤ v i)
    (hvu : IsUnit (∑ i, v i • rankOne ℝ (φ i) (φ i))) (hc : 0 < c) (h : ∀ i, c * v i ≤ w i) :
    IsUnit (∑ i, w i • rankOne ℝ (φ i) (φ i)) := by
  have hcu : IsUnit (c • ∑ i, v i • rankOne ℝ (φ i) (φ i)) := by
    simpa [Units.smul_def] using hvu.smul (Units.mk0 c hc.ne')
  have hvp := isPositive_sum_smul_rankOne Finset.univ φ fun i _ ↦ hv i
  exact (hvp.smul_of_nonneg hc.le).isUnit_of_le hcu (smul_sum_smul_rankOne_le h)

/-- The design operator on `E` of a design on a subspace `K` restricts on `K` to the design
operator on `K`: `V(w) v = V_K(w) v` for `v ∈ K`. -/
theorem designOperator_map_subtype_apply {K : Submodule ℝ E} (w : StdSimplex ℝ K) (v : K) :
    designOperator (w.map (↑)) (v : E) = ↑(designOperator w v) := by
  rw [designOperator, StdSimplex.weights_map, Finsupp.linearCombination_mapDomain,
    Finsupp.linearCombination_apply, designOperator_apply, Finsupp.sum, Finsupp.sum,
    Submodule.coe_sum, sum_apply]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  simp [Submodule.coe_inner]

/-- The design operator is positive. -/
theorem isPositive_designOperator (w : StdSimplex ℝ E) : (designOperator w).IsPositive := by
  rw [designOperator_def]
  exact isPositive_sum_smul_rankOne _ id fun a _ ↦ w.nonneg a

/-- The convex hull of the rank-one operators `a ⊗ a` of the points `a ∈ 𝒜` is the set of design
operators of the designs on `𝒜`. -/
theorem mem_convexHull_image_rankOne_iff {𝒜 : Set E} {V : E →L[ℝ] E} :
    V ∈ convexHull ℝ ((fun a ↦ rankOne ℝ a a) '' 𝒜) ↔
      ∃ w : StdSimplex ℝ E, ↑w.weights.support ⊆ 𝒜 ∧ designOperator w = V := by
  refine ⟨fun hV ↦ ?_, ?_⟩
  · refine convexHull_min (t := {V | ∃ w : StdSimplex ℝ E, ↑w.weights.support ⊆ 𝒜 ∧
      designOperator w = V}) ?_ ?_ hV
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨StdSimplex.single a, by simpa using ha, designOperator_single a⟩
    · rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩ s t hs ht hst
      exact ⟨convexCombPair s t hs ht hst w w',
        (StdSimplex.support_weights_convexCombPair_subset s t hs ht hst w w').trans
          (Set.union_subset hw hw'),
        designOperator_convexCombPair s t hs ht hst w w'⟩
  · rintro ⟨w, hw, rfl⟩
    rw [designOperator_def]
    exact (convex_convexHull ℝ _).sum_mem (fun a _ ↦ w.nonneg a) w.total
      fun a ha ↦ subset_convexHull ℝ _ ⟨a, hw ha, rfl⟩

/-- The kernel of the design operator is the orthogonal complement of the span of the support of
the design. -/
theorem ker_designOperator (w : StdSimplex ℝ E) :
    LinearMap.ker (designOperator w : E →ₗ[ℝ] E) =
      (Submodule.span ℝ (w.weights.support : Set E))ᗮ := by
  ext v
  rw [LinearMap.mem_ker, coe_coe, ← Submodule.span_singleton_le_iff_mem,
    ← Submodule.isOrtho_iff_le, Submodule.isOrtho_span]
  simp only [Set.mem_singleton_iff, forall_eq, Finset.mem_coe]
  refine ⟨fun hv a ha ↦ ?_, fun hv ↦ ?_⟩
  · have h := inner_designOperator_apply_self w v
    rw [hv, inner_zero_right, Finsupp.sum, eq_comm, Finset.sum_eq_zero_iff_of_nonneg
      fun b _ ↦ mul_nonneg (w.nonneg b) (sq_nonneg _)] at h
    rw [real_inner_comm]
    exact pow_eq_zero_iff two_ne_zero |>.1 <|
      (mul_eq_zero.1 (h a ha)).resolve_left (StdSimplex.weights_pos_of_mem_support ha).ne'
  · rw [designOperator_apply, Finsupp.sum]
    exact Finset.sum_eq_zero fun a ha ↦ by rw [real_inner_comm, hv ha, zero_smul, smul_zero]

/-- The trace of `B V(w)` is `∑_a w a ⟪a, B a⟫`. -/
theorem trace_comp_designOperator [FiniteDimensional ℝ E] (B : E →L[ℝ] E) (w : StdSimplex ℝ E) :
    LinearMap.trace ℝ E (B ∘L designOperator w : E →ₗ[ℝ] E) =
      w.weights.sum fun a c ↦ c * ⟪a, B a⟫_ℝ := by
  rw [designOperator_def, Finsupp.sum, Finsupp.sum]
  exact trace_comp_sum_smul_rankOne _ B id _

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The design operator is invertible iff the support of the design spans `E`. -/
theorem isUnit_designOperator_iff (w : StdSimplex ℝ E) :
    IsUnit (designOperator w) ↔ Submodule.span ℝ (w.weights.support : Set E) = ⊤ := by
  rw [isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot, ker_designOperator,
    Submodule.orthogonal_eq_bot_iff]

/-- The range of the design operator is the span of the support of the design. -/
theorem range_designOperator (w : StdSimplex ℝ E) :
    LinearMap.range (designOperator w : E →ₗ[ℝ] E) =
      Submodule.span ℝ (w.weights.support : Set E) := by
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range _),
    (isPositive_designOperator w).isSymmetric.orthogonal_range, ker_designOperator,
    Submodule.orthogonal_orthogonal]

/-- An invertible design operator has positive determinant. -/
theorem det_designOperator_pos {w : StdSimplex ℝ E} (hu : IsUnit (designOperator w)) :
    0 < (designOperator w).det :=
  (isPositive_designOperator w).toLinearMap.det_pos
    ((LinearMap.isUnit_iff_ker_eq_bot _).1 (isUnit_iff_isUnit_toLinearMap.1 hu))

/-- A design with invertible design operator `V(w)` on a space of dimension `d` satisfies
`∑_a w a ⟪a, V(w)⁻¹ a⟫ = d`. -/
theorem sum_mul_inner_ringInverse_designOperator {w : StdSimplex ℝ E}
    (hu : IsUnit (designOperator w)) :
    (w.weights.sum fun a c ↦ c * ⟪a, Ring.inverse (designOperator w) a⟫_ℝ) = finrank ℝ E := by
  rw [designOperator_def, Finsupp.sum] at hu ⊢
  exact sum_mul_inner_ringInverse_sum_smul_rankOne (φ := id) hu

/-- Every design with invertible design operator `V(w)` on a space of dimension `d` has a support
point `a` with `d ≤ ⟪a, V(w)⁻¹ a⟫`: the G-value `sup_{a ∈ 𝒜} ⟪a, V(w)⁻¹ a⟫` of a design on `𝒜` is
at least `d`. -/
theorem exists_mem_support_finrank_le_inner_ringInverse_designOperator {w : StdSimplex ℝ E}
    (hu : IsUnit (designOperator w)) :
    ∃ a ∈ w.weights.support, (finrank ℝ E : ℝ) ≤ ⟪a, Ring.inverse (designOperator w) a⟫_ℝ := by
  by_contra! h
  have hlt := Finset.sum_lt_sum_of_nonempty w.support_weights_nonempty fun a ha ↦
    mul_lt_mul_of_pos_left (h a ha) (StdSimplex.weights_pos_of_mem_support ha)
  have htotal : ∑ a ∈ w.weights.support, w.weights a = 1 := by simpa [Finsupp.sum] using w.total
  rw [← Finset.sum_mul, htotal, one_mul] at hlt
  have hsum := sum_mul_inner_ringInverse_designOperator hu
  rw [Finsupp.sum] at hsum
  linarith

/-- If a design satisfies `⟪a, V(w)⁻¹ a⟫ ≤ d` on its support, then `⟪a, V(w)⁻¹ a⟫ = d` on its
support [LS, Exercise 21.5]. -/
theorem inner_ringInverse_designOperator_eq_finrank {w : StdSimplex ℝ E}
    (hu : IsUnit (designOperator w))
    (h : ∀ a ∈ w.weights.support, ⟪a, Ring.inverse (designOperator w) a⟫_ℝ ≤ finrank ℝ E)
    {a : E} (ha : a ∈ w.weights.support) :
    ⟪a, Ring.inverse (designOperator w) a⟫_ℝ = finrank ℝ E := by
  have htotal : ∑ b ∈ w.weights.support, w.weights b = 1 := by simpa [Finsupp.sum] using w.total
  have hsum : ∑ b ∈ w.weights.support, w.weights b *
      (finrank ℝ E - ⟪b, Ring.inverse (designOperator w) b⟫_ℝ) = 0 := by
    have := sum_mul_inner_ringInverse_designOperator hu
    rw [Finsupp.sum] at this
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, htotal, this, one_mul, sub_self]
  rw [Finset.sum_eq_zero_iff_of_nonneg fun b hb ↦
    mul_nonneg (w.nonneg b) (sub_nonneg.2 (h b hb))] at hsum
  linarith [(mul_eq_zero.1 (hsum a ha)).resolve_left (StdSimplex.weights_pos_of_mem_support ha).ne']

/-- Moving a design `w` with invertible design operator towards the Dirac mass at `a`, with weights
`(1 + s)⁻¹` and `(1 + s)⁻¹ s`, multiplies `det V(w)` by `(1 + s ⟪a, V(w)⁻¹ a⟫) / (1 + s) ^ d`, by
the matrix determinant lemma. -/
private theorem det_designOperator_convexCombPair_single {w : StdSimplex ℝ E}
    (hu : IsUnit (designOperator w)) (a : E) {s : ℝ} (h₁ : 0 ≤ (1 + s)⁻¹)
    (h₂ : 0 ≤ (1 + s)⁻¹ * s) (hst : (1 + s)⁻¹ + (1 + s)⁻¹ * s = 1) :
    (designOperator (convexCombPair _ _ h₁ h₂ hst w (.single a))).det =
      ((1 + s) ^ finrank ℝ E)⁻¹ * (designOperator w).det *
        (1 + s * ⟪a, Ring.inverse (designOperator w) a⟫_ℝ) := by
  have hV : designOperator (convexCombPair _ _ h₁ h₂ hst w (.single a)) =
      (1 + s)⁻¹ • (designOperator w + rankOne ℝ (s • a) a) := by
    simp [smul_add, smul_smul]
  simp only [det, hV, toLinearMap_smul, LinearMap.det_smul]
  rw [det_add_rankOne hu, map_smul, real_inner_smul_right, inv_pow]
  ring

/-- **D-optimal designs are G-optimal** [LS, Theorem 21.1]. Let `w` be a design on `𝒜` with
invertible design operator `V(w)` that maximizes `det V(w)` among the designs on `𝒜`. Then
`⟪a, V(w)⁻¹ a⟫ ≤ d` for every `a ∈ 𝒜`. -/
theorem inner_ringInverse_designOperator_le_finrank_of_isMaxOn {𝒜 : Set E} {w : StdSimplex ℝ E}
    (hw : ↑w.weights.support ⊆ 𝒜) (hu : IsUnit (designOperator w))
    (hmax : IsMaxOn (fun w' ↦ (designOperator w').det)
      {w' : StdSimplex ℝ E | ↑w'.weights.support ⊆ 𝒜} w)
    {a : E} (ha : a ∈ 𝒜) :
    ⟪a, Ring.inverse (designOperator w) a⟫_ℝ ≤ finrank ℝ E := by
  set g := ⟪a, Ring.inverse (designOperator w) a⟫_ℝ
  set d := finrank ℝ E
  have hdet := det_designOperator_pos hu
  -- moving `w` towards the Dirac mass at `a` cannot increase the determinant
  have hle : ∀ s : ℝ, 0 < s → 1 + s * g ≤ (1 + s) ^ d := by
    intro s hs
    have h1s : 0 < 1 + s := by linarith
    have hst : (1 + s)⁻¹ + (1 + s)⁻¹ * s = 1 := by field_simp
    let w' := convexCombPair _ _ (inv_nonneg.2 h1s.le) (by positivity) hst w (.single a)
    have hw' : ↑w'.weights.support ⊆ 𝒜 :=
      (StdSimplex.support_weights_convexCombPair_subset _ _ _ _ hst w _).trans
        (Set.union_subset hw (by simpa using ha))
    have h : ((1 + s) ^ d)⁻¹ * (designOperator w).det * (1 + s * g) ≤ (designOperator w).det :=
      det_designOperator_convexCombPair_single hu a _ _ hst ▸ hmax hw'
    rw [mul_assoc, inv_mul_le_iff₀ (by positivity)] at h
    exact le_of_mul_le_mul_left (by linarith) hdet
  -- the derivative of `s ↦ (1 + s) ^ d` at `0` is `d`
  have hlim := HasDerivAt.tendsto_slope_zero_right (hasDerivAt_pow d (1 : ℝ))
  simp only [one_pow, mul_one] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  rw [smul_eq_mul, le_inv_mul_iff₀ hs]
  linarith [hle s hs]

/-- **A design with `g(w) ≤ d` is D-optimal** [LS, Theorem 21.1]. Let `w` be a design with
invertible design operator `V(w)` such that `⟪a, V(w)⁻¹ a⟫ ≤ d` for every `a ∈ 𝒜`. Then `w`
maximizes `det V(w')` among the designs `w'` on `𝒜`. -/
theorem isMaxOn_det_designOperator_of_inner_ringInverse_le_finrank {𝒜 : Set E}
    {w : StdSimplex ℝ E} (hu : IsUnit (designOperator w))
    (h : ∀ a ∈ 𝒜, ⟪a, Ring.inverse (designOperator w) a⟫_ℝ ≤ finrank ℝ E) :
    IsMaxOn (fun w' ↦ (designOperator w').det)
      {w' : StdSimplex ℝ E | ↑w'.weights.support ⊆ 𝒜} w := by
  intro w' (hw' : ↑w'.weights.support ⊆ 𝒜)
  set V := designOperator w
  set d := finrank ℝ E
  have hdet := det_designOperator_pos hu
  have hkey := (isPositive_designOperator w).ringInverse.det_mul_det_le_trace_comp_div_finrank_pow
    (isPositive_designOperator w')
  rw [trace_comp_designOperator, Finsupp.sum] at hkey
  -- the trace `∑_a w' a ⟪a, V⁻¹ a⟫` lies in `[0, d]`
  have htotal : ∑ a ∈ w'.weights.support, w'.weights a = 1 := by
    simpa [Finsupp.sum] using w'.total
  have htr_nonneg : 0 ≤ ∑ a ∈ w'.weights.support, w'.weights a * ⟪a, Ring.inverse V a⟫_ℝ :=
    Finset.sum_nonneg fun a _ ↦
      mul_nonneg (w'.nonneg a) ((isPositive_designOperator w).ringInverse.inner_nonneg_right a)
  have htr_le : ∑ a ∈ w'.weights.support, w'.weights a * ⟪a, Ring.inverse V a⟫_ℝ ≤ d := by
    calc ∑ a ∈ w'.weights.support, w'.weights a * ⟪a, Ring.inverse V a⟫_ℝ
        ≤ ∑ a ∈ w'.weights.support, w'.weights a * d :=
          Finset.sum_le_sum fun a ha ↦ mul_le_mul_of_nonneg_left (h a (hw' ha)) (w'.nonneg a)
      _ = d := by rw [← Finset.sum_mul, htotal, one_mul]
  have hpow : ((∑ a ∈ w'.weights.support, w'.weights a * ⟪a, Ring.inverse V a⟫_ℝ) / d) ^ d ≤ 1 :=
    pow_le_one₀ (div_nonneg htr_nonneg d.cast_nonneg) (div_le_one_of_le₀ htr_le d.cast_nonneg)
  calc (designOperator w').det
      = V.det * ((Ring.inverse V).det * (designOperator w').det) := by
        rw [← mul_assoc, mul_comm V.det, det_ringInverse_mul_det hu, one_mul]
    _ ≤ V.det * 1 := mul_le_mul_of_nonneg_left (hkey.trans hpow) hdet.le
    _ = V.det := mul_one _

/-- If a nonempty set `𝒜` spans `E`, some design on `𝒜` has an invertible design operator. -/
theorem exists_design_isUnit_designOperator {𝒜 : Set E} (hne : 𝒜.Nonempty)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) :
    ∃ w : StdSimplex ℝ E, ↑w.weights.support ⊆ 𝒜 ∧ IsUnit (designOperator w) := by
  classical
  obtain ⟨a₀, ha₀⟩ := hne
  obtain ⟨b, hb𝒜, hbspan, hbli⟩ := exists_linearIndependent ℝ 𝒜
  -- the uniform design on the finite set `t = {a₀} ∪ b`
  set t := insert a₀ hbli.set_finite_of_isNoetherian.toFinset
  have ht𝒜 : ↑t ⊆ 𝒜 := by simpa [t, Set.insert_subset_iff] using ⟨ha₀, hb𝒜⟩
  have htpos : (0 : ℝ) < t.card := by simp [t]
  let u : StdSimplex ℝ t :=
    { weights := Finsupp.equivFunOnFinite.symm fun _ ↦ (t.card : ℝ)⁻¹
      nonneg := fun _ ↦ by simp
      total := by simp [Finsupp.sum_fintype, htpos.ne'] }
  refine ⟨u.map (↑), (StdSimplex.support_weights_map_subset _ u).trans ?_,
    (isUnit_designOperator_iff _).2 ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact ht𝒜 y.2
  · refine eq_top_iff.2 ((hspan.symm.trans hbspan.symm).le.trans (Submodule.span_mono ?_))
    intro x hx
    have hxt : x ∈ t := by simp [t, hx]
    rw [Finset.mem_coe, Finsupp.mem_support_iff, StdSimplex.weights_map,
      ← Subtype.coe_mk x hxt, Finsupp.mapDomain_apply_of_injective Subtype.val_injective]
    simp [u, htpos.ne']

/-- On a set `𝒜` spanning `E`, a design that maximizes `det V(w)` among the designs on `𝒜` has an
invertible design operator. -/
theorem isUnit_designOperator_of_isMaxOn {𝒜 : Set E} (hspan : Submodule.span ℝ 𝒜 = ⊤)
    {w : StdSimplex ℝ E} (hw : ↑w.weights.support ⊆ 𝒜)
    (hmax : IsMaxOn (fun w' ↦ (designOperator w').det)
      {w' : StdSimplex ℝ E | ↑w'.weights.support ⊆ 𝒜} w) :
    IsUnit (designOperator w) := by
  obtain ⟨a, ha⟩ := w.support_weights_nonempty
  obtain ⟨w₀, hw₀, hu₀⟩ := exists_design_isUnit_designOperator ⟨a, hw ha⟩ hspan
  rw [isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_isUnit_det]
  exact ((det_designOperator_pos hu₀).trans_le (hmax hw₀)).ne'.isUnit

/-- **The Kiefer–Wolfowitz theorem** [LS, Theorem 21.1, Exercise 21.3]. A nonempty compact set
`𝒜` spanning a real inner product space `E` of dimension `d` carries a design `w` with invertible
design operator `V(w)` and `⟪a, V(w)⁻¹ a⟫ ≤ d` for every `a ∈ 𝒜`: its G-value is `d`, the
smallest possible (`exists_mem_support_finrank_le_inner_ringInverse_designOperator`). -/
theorem exists_design_inner_ringInverse_le_finrank {𝒜 : Set E} (h𝒜 : IsCompact 𝒜)
    (hne : 𝒜.Nonempty) (hspan : Submodule.span ℝ 𝒜 = ⊤) :
    ∃ w : StdSimplex ℝ E, ↑w.weights.support ⊆ 𝒜 ∧ IsUnit (designOperator w) ∧
      ∀ a ∈ 𝒜, ⟪a, Ring.inverse (designOperator w) a⟫_ℝ ≤ finrank ℝ E := by
  -- a maximizer of the determinant on the compact convex hull of the `a ⊗ a`
  have hC : IsCompact (convexHull ℝ ((fun a : E ↦ rankOne ℝ a a) '' 𝒜)) :=
    (h𝒜.image ((rankOne ℝ).continuous.clm_apply continuous_id)).convexHull ℝ
  obtain ⟨a₀, ha₀⟩ := hne
  obtain ⟨V, hV, hmax⟩ := hC.exists_isMaxOn
    ⟨_, subset_convexHull ℝ _ (Set.mem_image_of_mem _ ha₀)⟩ continuous_det.continuousOn
  obtain ⟨w, hw, rfl⟩ := mem_convexHull_image_rankOne_iff.1 hV
  have hmax' : IsMaxOn (fun w' ↦ (designOperator w').det)
      {w' : StdSimplex ℝ E | ↑w'.weights.support ⊆ 𝒜} w := fun w' hw' ↦
    hmax (mem_convexHull_image_rankOne_iff.2 ⟨w', hw', rfl⟩)
  have hu := isUnit_designOperator_of_isMaxOn hspan hw hmax'
  exact ⟨w, hw, hu, fun _ ha ↦
    inner_ringInverse_designOperator_le_finrank_of_isMaxOn hw hu hmax' ha⟩

/-- **The Kiefer–Wolfowitz theorem for finitely many arms** [LS, Theorem 21.1]. If the features
`φ i` of the elements of a nonempty finite type span `E`, of dimension `d`, some weights `w` in the
simplex have an invertible design operator `V = ∑ i, w i • φ i ⊗ φ i` with `⟪φ i, V⁻¹ φ i⟫ ≤ d`
for every `i`: the Kiefer–Wolfowitz design on the features, pulled back to the arms. -/
theorem exists_mem_simplex_inner_ringInverse_le_finrank {ι : Type*} [Fintype ι] [Nonempty ι]
    {φ : ι → E} (hspan : Submodule.span ℝ (Set.range φ) = ⊤) :
    ∃ w ∈ LMLExplore.simplex ι, IsUnit (∑ i, w i • rankOne ℝ (φ i) (φ i)) ∧
      ∀ i, ⟪φ i, Ring.inverse (∑ i, w i • rankOne ℝ (φ i) (φ i)) (φ i)⟫_ℝ ≤ finrank ℝ E := by
  obtain ⟨w, hw, hu, hle⟩ := exists_design_inner_ringInverse_le_finrank
    (Set.finite_range φ).isCompact (Set.range_nonempty φ) hspan
  -- the design is supported on the features, so it is the image of a design on the arms
  obtain ⟨v, rfl⟩ := (StdSimplex.mem_range_map_iff φ w).2 fun x hx ↦ by
    by_contra h
    exact hx (hw (Finsupp.mem_support_iff.2 h))
  rw [designOperator_map] at hu hle
  exact ⟨v.weights, v.weights_mem_simplex, hu, fun i ↦ hle _ ⟨i, rfl⟩⟩

/-- Let `w` be a design on a subspace `K` whose design operator `V_K(w)` on `K` is invertible. For
`a ∈ K`, the weighted norm of `a` for the Moore–Penrose inverse of the design operator `V(w)` on
`E` is its weighted norm for the inverse of `V_K(w)`: `⟪a, V(w)⁺ a⟫ = ⟪a, V_K(w)⁻¹ a⟫`. -/
theorem inner_moorePenroseInverse_designOperator_map_subtype {K : Submodule ℝ E}
    {w : StdSimplex ℝ K} (hu : IsUnit (designOperator w)) (a : K) :
    ⟪(a : E), (designOperator (w.map ((↑) : K → E)) : E →ₗ[ℝ] E).moorePenroseInverse a⟫_ℝ =
      ⟪a, Ring.inverse (designOperator w) a⟫_ℝ := by
  set V := designOperator (w.map ((↑) : K → E))
  -- `V` maps `V_K(w)⁻¹ v` to `v` for `v ∈ K`, so `K` lies in the range of `V`
  have hV : ∀ v : K, V ↑(Ring.inverse (designOperator w) v) = v := fun v ↦ by
    rw [designOperator_map_subtype_apply, apply_ringInverse_apply hu]
  have hmem : ∀ v : K, (v : E) ∈ LinearMap.range (V : E →ₗ[ℝ] E) := fun v ↦
    ⟨_, by rw [coe_coe, hV]⟩
  calc ⟪(a : E), (V : E →ₗ[ℝ] E).moorePenroseInverse a⟫_ℝ
      = ⟪(a : E), (V : E →ₗ[ℝ] E).moorePenroseInverse
          ((V : E →ₗ[ℝ] E) ↑(Ring.inverse (designOperator w) a))⟫_ℝ := by rw [coe_coe, hV]
    _ = ⟪a, Ring.inverse (designOperator w) a⟫_ℝ := by
      rw [(isPositive_designOperator _).toLinearMap.isSymmetric
        |>.moorePenroseInverse_apply_apply_of_mem_range (hmem _), Submodule.coe_inner]

/-- **Support reduction of G-optimal designs** [LS, Theorem 21.1]. Let `w` be a design with
invertible design operator `V(w)` on a nontrivial real inner product space of dimension `d`, with
`⟪a, V(w)⁻¹ a⟫ ≤ d` on its support. Then some design `w'`, supported in the support of `w`, has the
same design operator and at most `d (d + 1) / 2` support points. In particular `w'` has the same
G-value as `w` on every set. -/
theorem exists_designOperator_eq_card_support_le [Nontrivial E] {w : StdSimplex ℝ E}
    (hu : IsUnit (designOperator w))
    (h : ∀ a ∈ w.weights.support, ⟪a, Ring.inverse (designOperator w) a⟫_ℝ ≤ finrank ℝ E) :
    ∃ w' : StdSimplex ℝ E, w'.weights.support ⊆ w.weights.support ∧
      designOperator w' = designOperator w ∧
      #w'.weights.support ≤ finrank ℝ E * (finrank ℝ E + 1) / 2 := by
  classical
  set S := w.weights.support
  -- the linear form `X ↦ trace (V(w)⁻¹ X)` takes the value `d` at `a ⊗ a` for `a` in the support
  let ℓ : (E →L[ℝ] E) →ₗ[ℝ] ℝ :=
    LinearMap.trace ℝ E ∘ₗ coeLM ℝ ∘ₗ LinearMap.mulLeft ℝ (Ring.inverse (designOperator w))
  have hℓ : ∀ a ∈ S, ℓ (rankOne ℝ a a) = finrank ℝ E := fun a ha ↦ by
    rw [← inner_ringInverse_designOperator_eq_finrank hu h ha]
    simp [ℓ, mul_def, comp_rankOne, trace_rankOne]
  -- by Carathéodory's theorem, `V(w)` is a convex combination of affinely independent `a ⊗ a`
  have hV : designOperator w ∈ convexHull ℝ ((fun a ↦ rankOne ℝ a a) '' ↑S) :=
    mem_convexHull_image_rankOne_iff.2 ⟨w, subset_rfl, rfl⟩
  rw [convexHull_eq_union] at hV
  simp only [Set.mem_iUnion] at hV
  obtain ⟨t, htS, hai, hVt⟩ := hV
  -- they lie on the hyperplane `{X | ℓ X = d}`, so they are linearly independent symmetric
  -- operators, of which there are at most `d (d + 1) / 2`
  have hlin : LinearIndependent ℝ ((↑) : t → E →L[ℝ] E) :=
    hai.linearIndependent_of_forall_apply_eq ℓ (Nat.cast_ne_zero.2 finrank_pos.ne') fun X ↦ by
      obtain ⟨a, ha, hX⟩ := htS X.2
      rw [← hX, hℓ a ha]
  have hcard : #t ≤ finrank ℝ E * (finrank ℝ E + 1) / 2 := by
    have hlin' := hlin.map' (coeLM ℝ) (LinearMap.ker_eq_bot.2 coe_injective)
    rw [← Fintype.card_coe]
    refine hlin'.fintype_card_le_of_isSymmetric fun X ↦ ?_
    obtain ⟨a, -, hX⟩ := htS X.2
    simp [← hX]
  -- one point `a` of the support for each operator `a ⊗ a` of `t` carries the design `w'`
  obtain ⟨S', hS'S, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn _ t htS
  have hVS' : designOperator w ∈ convexHull ℝ ((fun a ↦ rankOne ℝ a a) '' ↑S') := by
    rwa [← Finset.coe_image, himg]
  obtain ⟨w', hw', hVw'⟩ := mem_convexHull_image_rankOne_iff.1 hVS'
  refine ⟨w', fun a ha ↦ hS'S (hw' ha), hVw', ?_⟩
  calc #w'.weights.support ≤ #S' := Finset.card_le_card fun a ha ↦ hw' ha
    _ = #t := by rw [← himg, Finset.card_image_of_injOn hinj]
    _ ≤ _ := hcard

/-- **The Kiefer–Wolfowitz theorem with the support bound** [LS, Theorem 21.1, Exercise 21.3]. A
compact set `𝒜` spanning a nontrivial real inner product space `E` of dimension `d` carries a
design `w` with invertible design operator `V(w)`, with `⟪a, V(w)⁻¹ a⟫ ≤ d` for every `a ∈ 𝒜`, and
with at most `d (d + 1) / 2` support points. -/
theorem exists_design_inner_ringInverse_le_finrank_and_card_support_le [Nontrivial E] {𝒜 : Set E}
    (h𝒜 : IsCompact 𝒜) (hspan : Submodule.span ℝ 𝒜 = ⊤) :
    ∃ w : StdSimplex ℝ E, ↑w.weights.support ⊆ 𝒜 ∧ IsUnit (designOperator w) ∧
      (∀ a ∈ 𝒜, ⟪a, Ring.inverse (designOperator w) a⟫_ℝ ≤ finrank ℝ E) ∧
      #w.weights.support ≤ finrank ℝ E * (finrank ℝ E + 1) / 2 := by
  have hne : 𝒜.Nonempty := Set.nonempty_iff_ne_empty.2 fun h ↦ by
    simp [h] at hspan
  obtain ⟨w, hw, hu, hle⟩ := exists_design_inner_ringInverse_le_finrank h𝒜 hne hspan
  obtain ⟨w', hw'w, hV, hcard⟩ :=
    exists_designOperator_eq_card_support_le hu fun a ha ↦ hle a (hw ha)
  exact ⟨w', (Finset.coe_subset.2 hw'w).trans hw, hV ▸ hu, hV ▸ hle, hcard⟩

/-- **The Kiefer–Wolfowitz theorem on the span of a compact set, with the support bound**
[LS, Theorem 21.1, Exercises 21.3 and 21.6]. Let `𝒜` be a compact set of a finite-dimensional real
inner product space whose span has dimension `m ≥ 1`. Then `𝒜` carries a design `w` whose support
spans the span of `𝒜` and has at most `m (m + 1) / 2` points, such that, with the Moore–Penrose
inverse `V(w)⁺` of its design operator, `⟪a, V(w)⁺ a⟫ ≤ m` for every `a ∈ 𝒜`, with equality on the
support of `w`: its G-value is `m`. -/
theorem exists_design_inner_moorePenroseInverse_le_finrank_and_card_support_le {𝒜 : Set E}
    (h𝒜 : IsCompact 𝒜) (h0 : Submodule.span ℝ 𝒜 ≠ ⊥) :
    ∃ w : StdSimplex ℝ E, ↑w.weights.support ⊆ 𝒜 ∧
      Submodule.span ℝ (w.weights.support : Set E) = Submodule.span ℝ 𝒜 ∧
      (∀ a ∈ 𝒜, ⟪a, (designOperator w : E →ₗ[ℝ] E).moorePenroseInverse a⟫_ℝ ≤
        finrank ℝ (Submodule.span ℝ 𝒜)) ∧
      (∀ a ∈ w.weights.support, ⟪a, (designOperator w : E →ₗ[ℝ] E).moorePenroseInverse a⟫_ℝ =
        finrank ℝ (Submodule.span ℝ 𝒜)) ∧
      #w.weights.support ≤
        finrank ℝ (Submodule.span ℝ 𝒜) * (finrank ℝ (Submodule.span ℝ 𝒜) + 1) / 2 := by
  classical
  set K := Submodule.span ℝ 𝒜
  have : Nontrivial K := Submodule.nontrivial_iff_ne_bot.2 h0
  -- the Kiefer–Wolfowitz theorem in `K` for the preimage of `𝒜`, which is compact and spans `K`
  have h𝒜K : IsCompact (((↑) : K → E) ⁻¹' 𝒜) :=
    K.isClosed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isCompact_preimage h𝒜
  obtain ⟨w, hw, hu, hle, hcard⟩ :=
    exists_design_inner_ringInverse_le_finrank_and_card_support_le h𝒜K
      Submodule.span_span_coe_preimage
  -- its image in `E` has the image of its support as support
  have hsupp : (w.map ((↑) : K → E)).weights.support = w.weights.support.image (↑) := by
    rw [StdSimplex.weights_map, Finsupp.mapDomain_support_of_injective Subtype.val_injective]
  refine ⟨w.map (↑), ?_, ?_, fun a ha ↦ ?_, fun a ha ↦ ?_, ?_⟩
  · rw [hsupp, Finset.coe_image]
    exact Set.image_subset_iff.2 hw
  · rw [hsupp, Finset.coe_image, ← K.coe_subtype, Submodule.span_image,
      (isUnit_designOperator_iff w).1 hu, Submodule.map_subtype_top]
  · exact (inner_moorePenroseInverse_designOperator_map_subtype hu
      ⟨a, Submodule.subset_span ha⟩).trans_le (hle _ ha)
  · rw [hsupp, Finset.mem_image] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact (inner_moorePenroseInverse_designOperator_map_subtype hu b).trans
      (inner_ringInverse_designOperator_eq_finrank hu (fun c hc ↦ hle c (hw hc)) hb)
  · rw [hsupp]
    exact Finset.card_image_le.trans hcard

/-- **The Kiefer–Wolfowitz theorem on the span of a compact set** [LS, Theorem 21.1, Exercises 21.3
and 21.6]. A nonempty compact set `𝒜` of a finite-dimensional real inner product space carries a
design `w` whose support spans the span of `𝒜`, such that, with the Moore–Penrose inverse `V(w)⁺`
of its design operator, `⟪a, V(w)⁺ a⟫ ≤ m` for every `a ∈ 𝒜`, where `m` is the dimension of the
span of `𝒜`. The set `𝒜` need not span `E`. -/
theorem exists_design_inner_moorePenroseInverse_le_finrank {𝒜 : Set E} (h𝒜 : IsCompact 𝒜)
    (hne : 𝒜.Nonempty) :
    ∃ w : StdSimplex ℝ E, ↑w.weights.support ⊆ 𝒜 ∧
      Submodule.span ℝ (w.weights.support : Set E) = Submodule.span ℝ 𝒜 ∧ ∀ a ∈ 𝒜,
      ⟪a, (designOperator w : E →ₗ[ℝ] E).moorePenroseInverse a⟫_ℝ ≤
        finrank ℝ (Submodule.span ℝ 𝒜) := by
  by_cases h0 : Submodule.span ℝ 𝒜 = ⊥
  · -- then `𝒜 ⊆ {0}`, so the Dirac mass at a point of `𝒜` has G-value `0`
    obtain ⟨a₀, ha₀⟩ := hne
    have h0₀ : a₀ = 0 := Submodule.span_eq_bot.1 h0 a₀ ha₀
    refine ⟨.single a₀, by simp [StdSimplex.single, ha₀], ?_, fun a ha ↦ ?_⟩
    · rw [h0]
      simp [StdSimplex.single, h0₀]
    · simp [Submodule.span_eq_bot.1 h0 a ha]
  · obtain ⟨w, hw, hspan, hle, -⟩ :=
      exists_design_inner_moorePenroseInverse_le_finrank_and_card_support_le h𝒜 h0
    exact ⟨w, hw, hspan, hle⟩

/-- **The Kiefer–Wolfowitz theorem for finitely many arms** [LS, Theorem 21.1, Exercise 21.6]. Let
`φ : ι → E` be a feature map and `S` a nonempty finite set of arms. Some design `w` on the arms,
supported in `S`, has an image design `w.map φ` whose design operator `V` has the features of `S`
in its range and satisfies `⟪φ i, V⁺ φ i⟫ ≤ m` for every `i ∈ S`, where `m` is the dimension of the
span of the features of `S`. -/
theorem exists_design_map_inner_moorePenroseInverse_le_finrank {ι : Type*} (φ : ι → E)
    {S : Finset ι} (hS : S.Nonempty) :
    ∃ w : StdSimplex ℝ ι, w.weights.support ⊆ S ∧
      (∀ i ∈ S, φ i ∈ LinearMap.range (designOperator (w.map φ) : E →ₗ[ℝ] E)) ∧
      ∀ i ∈ S, ⟪φ i, (designOperator (w.map φ) : E →ₗ[ℝ] E).moorePenroseInverse (φ i)⟫_ℝ ≤
        finrank ℝ (Submodule.span ℝ (φ '' S)) := by
  classical
  obtain ⟨π, hπ, hspan, hle⟩ := exists_design_inner_moorePenroseInverse_le_finrank
    (S.finite_toSet.image φ).isCompact ((Finset.coe_nonempty.2 hS).image φ)
  have : Nonempty ι := ⟨hS.choose⟩
  -- an arm of `S` above each feature of `S`
  have hsec : ∀ v ∈ φ '' S, ∃ i ∈ S, φ i = v := fun v ⟨i, hi, hv⟩ ↦ ⟨i, hi, hv⟩
  choose! g hgS hgφ using hsec
  -- the design `π.map g` on the arms has image `π`
  have hmap : (π.map g).map φ = π := by
    rw [← StdSimplex.weights_inj, StdSimplex.map_map, StdSimplex.weights_map,
      Finsupp.mapDomain_congr fun v hv ↦ hgφ v (hπ hv)]
    exact Finsupp.mapDomain_id
  refine ⟨π.map g, fun i hi ↦ ?_, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hi)
    exact hgS v (hπ hv)
  · rw [hmap, range_designOperator, hspan]
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  · rw [hmap]
    exact hle _ ⟨i, hi, rfl⟩

/-! ### The G-value and the equivalence theorem -/

open Classical in
/-- The **G-value** `g(w) = sup_{a ∈ 𝒜} ‖a‖²_{V(w)⁺}` of a design `w` on a set `𝒜`, in `ℝ≥0∞`. The
point `a ∈ 𝒜` contributes `⟪a, V(w)⁺ a⟫` if it lies in the range of the design operator `V(w)`,
the span of the support of `w`, and `∞` otherwise: least squares on a design estimates `⟪a, θ⟫`
with a variance proportional to `⟪a, V(w)⁺ a⟫` when `a` lies in the span of the design, and does
not estimate it at all otherwise. When `V(w)` is invertible, `g(w) = sup_{a ∈ 𝒜} ⟪a, V(w)⁻¹ a⟫`
(`gValue_eq_iSup_of_isUnit`). -/
noncomputable def gValue (𝒜 : Set E) (w : StdSimplex ℝ E) : ℝ≥0∞ :=
  ⨆ a ∈ 𝒜, if a ∈ LinearMap.range (designOperator w : E →ₗ[ℝ] E) then
    ENNReal.ofReal ⟪a, (designOperator w : E →ₗ[ℝ] E).moorePenroseInverse a⟫_ℝ else ∞

open Classical in
theorem gValue_def (𝒜 : Set E) (w : StdSimplex ℝ E) :
    gValue 𝒜 w = ⨆ a ∈ 𝒜, if a ∈ LinearMap.range (designOperator w : E →ₗ[ℝ] E) then
      ENNReal.ofReal ⟪a, (designOperator w : E →ₗ[ℝ] E).moorePenroseInverse a⟫_ℝ else ∞ :=
  (rfl)

/-- For a design with invertible design operator, `g(w) = sup_{a ∈ 𝒜} ⟪a, V(w)⁻¹ a⟫`. -/
theorem gValue_eq_iSup_of_isUnit (𝒜 : Set E) {w : StdSimplex ℝ E}
    (hu : IsUnit (designOperator w)) :
    gValue 𝒜 w = ⨆ a ∈ 𝒜, ENNReal.ofReal ⟪a, Ring.inverse (designOperator w) a⟫_ℝ := by
  have hrange : LinearMap.range (designOperator w : E →ₗ[ℝ] E) = ⊤ := by
    rw [range_designOperator, ← isUnit_designOperator_iff]
    exact hu
  simp [gValue_def, hrange, moorePenroseInverse_eq_ringInverse hu]

/-- `g(w) ≤ c` iff every `a ∈ 𝒜` lies in the range of `V(w)` with `⟪a, V(w)⁺ a⟫ ≤ c`. -/
theorem gValue_le_ofReal_iff {𝒜 : Set E} {w : StdSimplex ℝ E} {c : ℝ} (hc : 0 ≤ c) :
    gValue 𝒜 w ≤ ENNReal.ofReal c ↔ ∀ a ∈ 𝒜, a ∈ LinearMap.range (designOperator w : E →ₗ[ℝ] E) ∧
      ⟪a, (designOperator w : E →ₗ[ℝ] E).moorePenroseInverse a⟫_ℝ ≤ c := by
  simp only [gValue_def, iSup₂_le_iff]
  refine forall₂_congr fun a _ ↦ ?_
  split_ifs with h
  · simp [h, ENNReal.ofReal_le_ofReal_iff hc]
  · simp [h]

/-- For a design with invertible design operator, `g(w) ≤ c` iff `⟪a, V(w)⁻¹ a⟫ ≤ c` for every
`a ∈ 𝒜`. -/
theorem gValue_le_ofReal_iff_of_isUnit {𝒜 : Set E} {w : StdSimplex ℝ E}
    (hu : IsUnit (designOperator w)) {c : ℝ} (hc : 0 ≤ c) :
    gValue 𝒜 w ≤ ENNReal.ofReal c ↔ ∀ a ∈ 𝒜, ⟪a, Ring.inverse (designOperator w) a⟫_ℝ ≤ c := by
  simp only [gValue_eq_iSup_of_isUnit 𝒜 hu, iSup₂_le_iff, ENNReal.ofReal_le_ofReal_iff hc]

/-- A design of finite G-value on `𝒜` has `𝒜` in the range of its design operator. -/
theorem mem_range_designOperator_of_gValue_ne_top {𝒜 : Set E} {w : StdSimplex ℝ E}
    (h : gValue 𝒜 w ≠ ∞) {a : E} (ha : a ∈ 𝒜) :
    a ∈ LinearMap.range (designOperator w : E →ₗ[ℝ] E) := by
  by_contra hna
  refine h (top_le_iff.1 ?_)
  rw [gValue_def]
  exact le_iSup₂_of_le a ha (by simp [hna])

/-- If `𝒜` spans `E`, a design of finite G-value on `𝒜` has an invertible design operator. -/
theorem isUnit_designOperator_of_gValue_ne_top {𝒜 : Set E} (hspan : Submodule.span ℝ 𝒜 = ⊤)
    {w : StdSimplex ℝ E} (h : gValue 𝒜 w ≠ ∞) : IsUnit (designOperator w) := by
  rw [isUnit_designOperator_iff, ← range_designOperator, eq_top_iff, ← hspan,
    Submodule.span_le]
  exact fun a ha ↦ mem_range_designOperator_of_gValue_ne_top h ha

/-- If `𝒜` spans `E`, of dimension `d`, every design on `𝒜` has G-value at least `d`. -/
theorem finrank_le_gValue {𝒜 : Set E} (hspan : Submodule.span ℝ 𝒜 = ⊤) {w : StdSimplex ℝ E}
    (hw : ↑w.weights.support ⊆ 𝒜) : (finrank ℝ E : ℝ≥0∞) ≤ gValue 𝒜 w := by
  by_cases h : gValue 𝒜 w = ∞
  · exact h ▸ le_top
  have hu := isUnit_designOperator_of_gValue_ne_top hspan h
  obtain ⟨a, ha, hle⟩ := exists_mem_support_finrank_le_inner_ringInverse_designOperator hu
  rw [gValue_eq_iSup_of_isUnit 𝒜 hu, ← ENNReal.ofReal_natCast]
  exact le_iSup₂_of_le a (hw ha) (ENNReal.ofReal_le_ofReal hle)

/-- **The Kiefer–Wolfowitz theorem** [LS, Theorem 21.1] in terms of the G-value: a nonempty compact
set `𝒜` spanning `E`, of dimension `d`, carries a design of G-value `d`, the smallest possible
(`finrank_le_gValue`). -/
theorem exists_gValue_eq_finrank {𝒜 : Set E} (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) :
    ∃ w : StdSimplex ℝ E, ↑w.weights.support ⊆ 𝒜 ∧ gValue 𝒜 w = finrank ℝ E := by
  obtain ⟨w, hw, hu, hle⟩ := exists_design_inner_ringInverse_le_finrank h𝒜 hne hspan
  refine ⟨w, hw, le_antisymm ?_ (finrank_le_gValue hspan hw)⟩
  rw [← ENNReal.ofReal_natCast, gValue_le_ofReal_iff_of_isUnit hu (Nat.cast_nonneg _)]
  exact hle

/-- **The Kiefer–Wolfowitz equivalence theorem** [LS, Theorem 21.1]. Let `𝒜` be a compact set
spanning a real inner product space `E` of dimension `d`, and `w` a design on `𝒜`. The following
are equivalent:
1. `w` is G-optimal: it minimizes the G-value `g` among the designs on `𝒜`;
2. `w` is D-optimal: it maximizes `det V(w)` (equivalently `log det V(w)`, which is `-∞` for a
   singular design operator) among the designs on `𝒜`;
3. `g(w) = d`. -/
theorem tfae_isMinOn_gValue_isMaxOn_det_designOperator {𝒜 : Set E} (h𝒜 : IsCompact 𝒜)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) {w : StdSimplex ℝ E} (hw : ↑w.weights.support ⊆ 𝒜) :
    [IsMinOn (gValue 𝒜) {w' : StdSimplex ℝ E | ↑w'.weights.support ⊆ 𝒜} w,
      IsMaxOn (fun w' ↦ (designOperator w').det)
        {w' : StdSimplex ℝ E | ↑w'.weights.support ⊆ 𝒜} w,
      gValue 𝒜 w = finrank ℝ E].TFAE := by
  have hd : (finrank ℝ E : ℝ≥0∞) = ENNReal.ofReal (finrank ℝ E) := (ENNReal.ofReal_natCast _).symm
  tfae_have 1 → 3 := fun hmin ↦ by
    obtain ⟨a, ha⟩ := w.support_weights_nonempty
    obtain ⟨w₀, hw₀, hg₀⟩ := exists_gValue_eq_finrank h𝒜 ⟨a, hw ha⟩ hspan
    exact le_antisymm ((hmin hw₀).trans hg₀.le) (finrank_le_gValue hspan hw)
  tfae_have 3 → 1 := fun h w' hw' ↦ h ▸ finrank_le_gValue hspan hw'
  tfae_have 3 → 2 := fun h ↦ by
    have hu := isUnit_designOperator_of_gValue_ne_top hspan (h ▸ ENNReal.natCast_ne_top _)
    exact isMaxOn_det_designOperator_of_inner_ringInverse_le_finrank hu
      ((gValue_le_ofReal_iff_of_isUnit hu (Nat.cast_nonneg _)).1 (by rw [h, hd]))
  tfae_have 2 → 3 := fun hmax ↦ by
    have hu := isUnit_designOperator_of_isMaxOn hspan hw hmax
    refine le_antisymm ?_ (finrank_le_gValue hspan hw)
    rw [hd, gValue_le_ofReal_iff_of_isUnit hu (Nat.cast_nonneg _)]
    exact fun a ha ↦ inner_ringInverse_designOperator_le_finrank_of_isMaxOn hw hu hmax ha
  tfae_finish

end FiniteDimensional

/-! ### The uniform design on an orthonormal basis -/

section OrthonormalBasis

variable {ι : Type*} [Fintype ι] [Nonempty ι] (b : OrthonormalBasis ι ℝ E)

include b in
/-- The dimension of `E`, which has an orthonormal basis indexed by a nonempty type, is nonzero. -/
private theorem natCast_finrank_ne_zero : (finrank ℝ E : ℝ) ≠ 0 := by
  simp [finrank_eq_card_basis b.toBasis, Fintype.card_ne_zero]

omit [Nonempty ι] in
/-- A set containing an orthonormal basis of `E` spans `E`. -/
private theorem span_eq_top_of_range_subset {𝒜 : Set E} (hb : Set.range b ⊆ 𝒜) :
    Submodule.span ℝ 𝒜 = ⊤ :=
  eq_top_mono (Submodule.span_mono (by simpa using hb)) b.toBasis.span_eq

/-- The design operator of the uniform design on an orthonormal basis `b` of `E`, of dimension
`d`, is `V = d⁻¹ • 1`. -/
theorem designOperator_map_barycenter :
    designOperator ((StdSimplex.barycenter : StdSimplex ℝ ι).map b) =
      (finrank ℝ E : ℝ)⁻¹ • (1 : E →L[ℝ] E) := by
  simp_rw [designOperator_map, StdSimplex.weights_barycenter_apply, ← Finset.smul_sum,
    b.sum_rankOne_eq_id, finrank_eq_card_basis b.toBasis, ContinuousLinearMap.one_def]

/-- The design operator of the uniform design on an orthonormal basis is invertible. -/
theorem isUnit_designOperator_map_barycenter :
    IsUnit (designOperator ((StdSimplex.barycenter : StdSimplex ℝ ι).map b)) := by
  rw [designOperator_map_barycenter]
  exact (Units.mk0 _ (inv_ne_zero (natCast_finrank_ne_zero b)) • (1 : (E →L[ℝ] E)ˣ)).isUnit

/-- The design operator `V = d⁻¹ • 1` of the uniform design on an orthonormal basis of `E`, of
dimension `d`, has inverse `V⁻¹ = d • 1`. -/
theorem ringInverse_designOperator_map_barycenter :
    Ring.inverse (designOperator ((StdSimplex.barycenter : StdSimplex ℝ ι).map b)) =
      (finrank ℝ E : ℝ) • (1 : E →L[ℝ] E) := by
  simpa using (Ring.inverse_mul_eq_iff_eq_mul _ 1 ((finrank ℝ E : ℝ) • (1 : E →L[ℝ] E))
    (isUnit_designOperator_map_barycenter b)).2 (by
      rw [designOperator_map_barycenter, smul_mul_smul_comm, one_mul,
        inv_mul_cancel₀ (natCast_finrank_ne_zero b), one_smul])

/-- For the uniform design on an orthonormal basis of `E`, of dimension `d`, the weighted norm of
every vector is `‖a‖²_{V⁻¹} = d ‖a‖²`. -/
theorem inner_ringInverse_designOperator_map_barycenter (a : E) :
    ⟪a, Ring.inverse (designOperator ((StdSimplex.barycenter : StdSimplex ℝ ι).map b)) a⟫_ℝ =
      finrank ℝ E * ‖a‖ ^ 2 := by
  rw [ringInverse_designOperator_map_barycenter, smul_apply, one_apply_eq_self,
    real_inner_smul_right, real_inner_self_eq_norm_sq]

/-- The G-value of the uniform design on an orthonormal basis of `E`, of dimension `d`, on a set
`𝒜` is `g = d sup_{a ∈ 𝒜} ‖a‖²`. -/
theorem gValue_map_barycenter [FiniteDimensional ℝ E] (𝒜 : Set E) :
    gValue 𝒜 ((StdSimplex.barycenter : StdSimplex ℝ ι).map b) =
      ⨆ a ∈ 𝒜, ENNReal.ofReal (finrank ℝ E * ‖a‖ ^ 2) := by
  simp_rw [gValue_eq_iSup_of_isUnit 𝒜 (isUnit_designOperator_map_barycenter b),
    inner_ringInverse_designOperator_map_barycenter]

/-- **The uniform design on an orthonormal basis is G-optimal**. Let `𝒜`
contain an orthonormal basis `b` of `E`, of dimension `d`, and lie in the closed unit ball, as the
unit sphere and the basis itself do. Then the uniform design on `b`, a design on `𝒜`
(`Convexity.StdSimplex.support_weights_map_subset_range`), has G-value `d` on `𝒜`, the smallest
possible. -/
theorem gValue_map_barycenter_eq_finrank [FiniteDimensional ℝ E] {𝒜 : Set E}
    (hb : Set.range b ⊆ 𝒜) (h𝒜 : 𝒜 ⊆ Metric.closedBall 0 1) :
    gValue 𝒜 ((StdSimplex.barycenter : StdSimplex ℝ ι).map b) = finrank ℝ E := by
  refine le_antisymm ?_ (finrank_le_gValue (span_eq_top_of_range_subset b hb)
    ((StdSimplex.support_weights_map_subset_range b _).trans hb))
  rw [← ENNReal.ofReal_natCast, gValue_le_ofReal_iff_of_isUnit
    (isUnit_designOperator_map_barycenter b) (Nat.cast_nonneg _)]
  intro a ha
  rw [inner_ringInverse_designOperator_map_barycenter]
  have : ‖a‖ ≤ 1 := by simpa using h𝒜 ha
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) (pow_le_one₀ (norm_nonneg a) this)

/-- The uniform design on an orthonormal basis `b` minimizes the G-value among the designs on a set
`𝒜` that contains `b` and lies in the closed unit ball. -/
theorem isMinOn_gValue_map_barycenter [FiniteDimensional ℝ E] {𝒜 : Set E}
    (hb : Set.range b ⊆ 𝒜) (h𝒜 : 𝒜 ⊆ Metric.closedBall 0 1) :
    IsMinOn (gValue 𝒜) {w : StdSimplex ℝ E | ↑w.weights.support ⊆ 𝒜}
      ((StdSimplex.barycenter : StdSimplex ℝ ι).map b) :=
  fun _ hw ↦ (gValue_map_barycenter_eq_finrank b hb h𝒜).trans_le
    (finrank_le_gValue (span_eq_top_of_range_subset b hb) hw)

end OrthonormalBasis

end LMLExplore
