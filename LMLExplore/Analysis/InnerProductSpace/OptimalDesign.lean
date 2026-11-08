/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Convex.Caratheodory
public import LMLExplore.Analysis.InnerProductSpace.MoorePenrose
public import LMLExplore.Analysis.InnerProductSpace.RankOne
public import LMLExplore.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.InnerProductSpace.Trace
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
`K` gives a design whose G-value, computed with the Moore–Penrose inverse `V(w)⁺` on `E`, is `m`
[LS, Exercise 21.6].

## Main definitions

* `LMLExplore.designOperator w`: the design operator `V(w) = ∑_a w a • a ⊗ a` of `w`.

## Main statements

* `LMLExplore.designOperator_map`: the design operator of the image `w.map φ` of a design on a
  finite type of arms by a feature map `φ` is `∑ i, w i • φ i ⊗ φ i`.
* `LMLExplore.designOperator_map_subtype_apply`: on a subspace `K`, the design operator on `E` of
  a design on `K` restricts to its design operator on `K`.
* `LMLExplore.designOperator_convexCombPair`: `V(w)` is affine in `w`.
* `LMLExplore.mem_convexHull_image_rankOne_iff`: the convex hull of `{a ⊗ a | a ∈ 𝒜}` is the set
  of design operators of the designs on `𝒜`.
* `LMLExplore.ker_designOperator`, `LMLExplore.isUnit_designOperator_iff`: the kernel of `V(w)` is
  the orthogonal complement of the span of the support of `w`, and `V(w)` is invertible iff the
  support spans `E`; `LMLExplore.det_designOperator_pos`: then `det V(w) > 0`.
* `LMLExplore.trace_comp_designOperator`: `trace (B V(w)) = ∑_a w a ⟪a, B a⟫`; hence
  `LMLExplore.sum_mul_inner_ringInverse_designOperator`: `∑_a w a ⟪a, V(w)⁻¹ a⟫ = d`.
* `LMLExplore.exists_mem_support_finrank_le_inner_ringInverse_designOperator`: every design with
  invertible `V(w)` has a support point with `d ≤ ⟪a, V(w)⁻¹ a⟫`, so `g(w) ≥ d`.
* `LMLExplore.inner_ringInverse_designOperator_eq_finrank`: if `⟪a, V(w)⁻¹ a⟫ ≤ d` on the support
  of `w`, equality holds there [LS, Exercise 21.5].
* `LMLExplore.inner_ringInverse_designOperator_le_finrank_of_isMaxOn`: a D-optimal design on `𝒜`
  with invertible design operator has `⟪a, V(w)⁻¹ a⟫ ≤ d` for every `a ∈ 𝒜`.
* `LMLExplore.exists_design_inner_ringInverse_le_finrank`: **Kiefer–Wolfowitz** [LS, Theorem 21.1,
  Exercise 21.3]: a nonempty compact set `𝒜` spanning `E` carries a design `w` with invertible
  design operator and `⟪a, V(w)⁻¹ a⟫ ≤ d` for every `a ∈ 𝒜`.
* `LMLExplore.inner_moorePenroseInverse_designOperator_map_subtype`: for a design on a subspace
  `K` with invertible design operator `V_K(w)` on `K`, `⟪a, V(w)⁺ a⟫ = ⟪a, V_K(w)⁻¹ a⟫` on `K`.
* `LMLExplore.exists_design_inner_moorePenroseInverse_le_finrank`: **Kiefer–Wolfowitz on the
  span** [LS, Exercise 21.6]: a nonempty compact set `𝒜` carries a design `w` with
  `⟪a, V(w)⁺ a⟫ ≤ dim (span 𝒜)` for every `a ∈ 𝒜`.

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
open scoped InnerProductSpace Topology

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
theorem designOperator_convexCombPair (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (w w' : StdSimplex ℝ E) :
    designOperator (convexCombPair s t hs ht hst w w') =
      s • designOperator w + t • designOperator w' := by
  simp [designOperator]

/-- The design operator of the image of a design on a finite type of arms by a feature map `φ`
is `∑ i, w i • φ i ⊗ φ i`: allocations on finitely many arms are designs on their features. -/
theorem designOperator_map {ι : Type*} [Fintype ι] (φ : ι → E) (w : StdSimplex ℝ ι) :
    designOperator (w.map φ) = ∑ i, w.weights i • rankOne ℝ (φ i) (φ i) := by
  rw [designOperator, StdSimplex.weights_map, Finsupp.linearCombination_mapDomain,
    Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ fun _ ↦ by simp]
  rfl

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
  exact isPositive_sum _ fun a _ ↦ (isPositive_rankOne_self a).smul_of_nonneg (w.nonneg a)

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
    have hpos : 0 < w.weights a :=
      (w.nonneg a).lt_of_ne (Finsupp.mem_support_iff.1 ha).symm
    rw [real_inner_comm]
    exact pow_eq_zero_iff two_ne_zero |>.1 <| (mul_eq_zero.1 (h a ha)).resolve_left hpos.ne'
  · rw [designOperator_apply, Finsupp.sum]
    exact Finset.sum_eq_zero fun a ha ↦ by rw [real_inner_comm, hv ha, zero_smul, smul_zero]

/-- The trace of `B V(w)` is `∑_a w a ⟪a, B a⟫`. -/
theorem trace_comp_designOperator [FiniteDimensional ℝ E] (B : E →L[ℝ] E) (w : StdSimplex ℝ E) :
    LinearMap.trace ℝ E (B ∘L designOperator w : E →ₗ[ℝ] E) =
      w.weights.sum fun a c ↦ c * ⟪a, B a⟫_ℝ := by
  simp [designOperator_def, Finsupp.sum, comp_finsetSum, comp_rankOne, trace_rankOne]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The design operator is invertible iff the support of the design spans `E`. -/
theorem isUnit_designOperator_iff (w : StdSimplex ℝ E) :
    IsUnit (designOperator w) ↔ Submodule.span ℝ (w.weights.support : Set E) = ⊤ := by
  rw [isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot, ker_designOperator,
    Submodule.orthogonal_eq_bot_iff]

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
  rw [← trace_comp_designOperator, ← mul_def, Ring.inverse_mul_cancel _ hu, toLinearMap_one,
    LinearMap.trace_one]

/-- Every design with invertible design operator `V(w)` on a space of dimension `d` has a support
point `a` with `d ≤ ⟪a, V(w)⁻¹ a⟫`: the G-value `sup_{a ∈ 𝒜} ⟪a, V(w)⁻¹ a⟫` of a design on `𝒜` is
at least `d`. -/
theorem exists_mem_support_finrank_le_inner_ringInverse_designOperator {w : StdSimplex ℝ E}
    (hu : IsUnit (designOperator w)) :
    ∃ a ∈ w.weights.support, (finrank ℝ E : ℝ) ≤ ⟪a, Ring.inverse (designOperator w) a⟫_ℝ := by
  by_contra! h
  have hlt := Finset.sum_lt_sum_of_nonempty w.support_weights_nonempty fun a ha ↦
    mul_lt_mul_of_pos_left (h a ha) ((w.nonneg a).lt_of_ne (Finsupp.mem_support_iff.1 ha).symm)
  have htotal : ∑ a ∈ w.weights.support, w.weights a = 1 := w.total
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
  have htotal : ∑ b ∈ w.weights.support, w.weights b = 1 := w.total
  have hsum : ∑ b ∈ w.weights.support, w.weights b *
      (finrank ℝ E - ⟪b, Ring.inverse (designOperator w) b⟫_ℝ) = 0 := by
    have := sum_mul_inner_ringInverse_designOperator hu
    rw [Finsupp.sum] at this
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, htotal, this, one_mul, sub_self]
  rw [Finset.sum_eq_zero_iff_of_nonneg fun b hb ↦
    mul_nonneg (w.nonneg b) (sub_nonneg.2 (h b hb))] at hsum
  have hpos : 0 < w.weights a := (w.nonneg a).lt_of_ne (Finsupp.mem_support_iff.1 ha).symm
  linarith [(mul_eq_zero.1 (hsum a ha)).resolve_left hpos.ne']

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
    have hV : designOperator w' = (1 + s)⁻¹ • (designOperator w + rankOne ℝ (s • a) a) := by
      rw [designOperator_convexCombPair, designOperator_single, map_smul, smul_apply, smul_add,
        smul_smul]
    have h := hmax hw'
    simp only [Set.mem_ofPred_eq, det, hV, toLinearMap_smul, LinearMap.det_smul] at h
    rw [det_add_rankOne hu, map_smul, real_inner_smul_right, ← mul_assoc,
      mul_comm _ (LinearMap.det _), mul_assoc] at h
    rwa [inv_pow, ← div_eq_inv_mul, mul_le_iff_le_one_right hdet,
      div_le_one (by positivity)] at h
  -- the derivative of `s ↦ (1 + s) ^ d` at `0` is `d`
  have hlim := HasDerivAt.tendsto_slope_zero_right (hasDerivAt_pow d (1 : ℝ))
  simp only [one_pow, mul_one] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  rw [smul_eq_mul, le_inv_mul_iff₀ hs]
  linarith [hle s hs]

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
  refine ⟨u.map (↑), fun x hx ↦ ?_, (isUnit_designOperator_iff _).2 ?_⟩
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    exact ht𝒜 y.2
  · refine eq_top_iff.2 ((hspan.symm.trans hbspan.symm).le.trans (Submodule.span_mono ?_))
    intro x hx
    have hxt : x ∈ t := by simp [t, hx]
    rw [Finset.mem_coe, Finsupp.mem_support_iff, StdSimplex.weights_map,
      ← Subtype.coe_mk x hxt, Finsupp.mapDomain_apply_of_injective Subtype.val_injective]
    simp [u, htpos.ne']

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
    (h𝒜.image ((rankOne ℝ).continuous.clm_apply continuous_id)).convexHull
  obtain ⟨a₀, ha₀⟩ := hne
  obtain ⟨V, hV, hmax⟩ := hC.exists_isMaxOn
    ⟨_, subset_convexHull ℝ _ (Set.mem_image_of_mem _ ha₀)⟩ continuous_det.continuousOn
  obtain ⟨w, hw, rfl⟩ := mem_convexHull_image_rankOne_iff.1 hV
  have hmax' : IsMaxOn (fun w' ↦ (designOperator w').det)
      {w' : StdSimplex ℝ E | ↑w'.weights.support ⊆ 𝒜} w := fun w' hw' ↦
    hmax (mem_convexHull_image_rankOne_iff.2 ⟨w', hw', rfl⟩)
  -- its determinant is at least that of a design with invertible design operator
  obtain ⟨w₀, hw₀, hu₀⟩ := exists_design_isUnit_designOperator ⟨a₀, ha₀⟩ hspan
  have hu : IsUnit (designOperator w) := by
    rw [isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_isUnit_det]
    exact ((det_designOperator_pos hu₀).trans_le (hmax' hw₀)).ne'.isUnit
  exact ⟨w, hw, hu, fun _ ha ↦
    inner_ringInverse_designOperator_le_finrank_of_isMaxOn hw hu hmax' ha⟩

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

/-- **The Kiefer–Wolfowitz theorem on the span of a compact set** [LS, Theorem 21.1, Exercises 21.3
and 21.6]. A nonempty compact set `𝒜` of a finite-dimensional real inner product space carries a
design `w` such that, with the Moore–Penrose inverse `V(w)⁺` of its design operator,
`⟪a, V(w)⁺ a⟫ ≤ m` for every `a ∈ 𝒜`, where `m` is the dimension of the span of `𝒜`. The set `𝒜`
need not span `E`. -/
theorem exists_design_inner_moorePenroseInverse_le_finrank {𝒜 : Set E} (h𝒜 : IsCompact 𝒜)
    (hne : 𝒜.Nonempty) :
    ∃ w : StdSimplex ℝ E, ↑w.weights.support ⊆ 𝒜 ∧ ∀ a ∈ 𝒜,
      ⟪a, (designOperator w : E →ₗ[ℝ] E).moorePenroseInverse a⟫_ℝ ≤
        finrank ℝ (Submodule.span ℝ 𝒜) := by
  classical
  set K := Submodule.span ℝ 𝒜
  -- the Kiefer–Wolfowitz theorem in `K` for the preimage of `𝒜`, which is compact and spans `K`
  have h𝒜K : IsCompact (((↑) : K → E) ⁻¹' 𝒜) :=
    K.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isCompact_preimage h𝒜
  obtain ⟨a₀, ha₀⟩ := hne
  obtain ⟨w, hw, hu, hle⟩ := exists_design_inner_ringInverse_le_finrank h𝒜K
    ⟨⟨a₀, Submodule.subset_span ha₀⟩, ha₀⟩ Submodule.span_span_coe_preimage
  refine ⟨w.map (↑), fun x hx ↦ ?_, fun a ha ↦ ?_⟩
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    exact hw hy
  · exact (inner_moorePenroseInverse_designOperator_map_subtype hu
      ⟨a, Submodule.subset_span ha⟩).trans_le (hle _ ha)

end FiniteDimensional

end LMLExplore
