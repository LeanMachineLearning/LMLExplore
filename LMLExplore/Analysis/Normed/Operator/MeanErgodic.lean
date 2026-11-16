/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.NormedSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import LMLExplore.Analysis.Normed.Module.FiniteDimension
public import LMLExplore.Analysis.Normed.Ring.PowerBounded
public import LMLExplore.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Yosida's mean ergodic theorem

Let `T` be a continuous linear operator on a normed space `E` over `ℝ` or `ℂ` that is *power
bounded*: `sup_n ‖T ^ n‖ < ∞` (`LMLExplore.IsPowerBounded`, a predicate on any seminormed ring).
Its Cesàro means `(N : 𝕜)⁻¹ • ∑ k ∈ range N, T ^ k x`, which are Mathlib's Birkhoff averages
`birkhoffAverage 𝕜 T id N x`, converge exactly on the subspace
`ker (1 - T) ⊕ closure (range (1 - T))`, which is closed when `E` is complete. The limit is a
bounded projection `Π` onto the fixed points `ker (1 - T)` of `T`, along
`closure (range (1 - T))`, and `Π T = T Π = Π ^ 2 = Π`. In finite dimension the decomposition is
the whole space and the Cesàro means converge in operator norm.

When the Cesàro means of a Markov kernel's action converge everywhere (for instance for a finite
chain), `Π` maps a reward to the long-run average reward of the chain; for a stochastic matrix it
is the limiting matrix.

This is the Banach-space form of the von Neumann theorem
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`, whose contractions are power
bounded (`LMLExplore.IsPowerBounded.of_norm_le_one`). The convergence to `0` on
`closure (range (1 - T))`, by equicontinuity from the telescoping on `range (1 - T)`, follows the
proof of Mathlib's `LinearMap.tendsto_birkhoffAverage_of_ker_subset_closure`.

## Main definitions

* `LMLExplore.IsPowerBounded.meanErgodicProj`: the limit `Π` of the Cesàro means, as a
  continuous linear map, when `ker (1 - T) ⊔ closure (range (1 - T))` is the whole space.

## Main statements

* `LMLExplore.IsPowerBounded.exists_tendsto_birkhoffAverage_iff`: the Cesàro means at
  `x` converge iff `x ∈ ker (1 - T) ⊔ closure (range (1 - T))`.
* `LMLExplore.IsPowerBounded.disjoint_ker_topologicalClosure_range`: the sum is direct.
* `LMLExplore.IsPowerBounded.isClosed_ker_sup_topologicalClosure_range`: the sum is closed
  in a Banach space.
* `LMLExplore.IsPowerBounded.tendsto_birkhoffAverage_self_iff` and
  `LMLExplore.IsPowerBounded.tendsto_birkhoffAverage_zero_iff`: the limit is `x` exactly on
  `ker (1 - T)` and `0` exactly on `closure (range (1 - T))`.
* `LMLExplore.IsPowerBounded.meanErgodicProj_mul`,
  `LMLExplore.IsPowerBounded.mul_meanErgodicProj`,
  `LMLExplore.IsPowerBounded.meanErgodicProj_mul_self`: `Π T = T Π = Π ^ 2 = Π`.
* `LMLExplore.IsPowerBounded.meanErgodicProj_mul_one_sub`,
  `LMLExplore.IsPowerBounded.one_sub_mul_meanErgodicProj`: `Π (1 - T) = (1 - T) Π = 0`.
* `LMLExplore.IsPowerBounded.meanErgodicProj_apply_eq_self_iff` and
  `LMLExplore.IsPowerBounded.meanErgodicProj_apply_eq_zero_iff`: `Π x = x` exactly on
  `ker (1 - T)` and `Π x = 0` exactly on `closure (range (1 - T))`.
* `LMLExplore.IsPowerBounded.tendsto_cesaro_meanErgodicProj`: in finite dimension, the
  Cesàro means converge to `Π` in operator norm.

## References

* U. Krengel, *Ergodic Theorems*, de Gruyter, 1985, §2.1.
* K. Yosida, *Mean ergodic theorem in Banach spaces*, Proc. Imp. Acad. Tokyo 14 (1938), 292–294.
-/

public section

open Filter Finset Function Module Topology

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {T : E →L[𝕜] E} {x y : E}

/-- The Birkhoff averages of `T` are its Cesàro means `(N : 𝕜)⁻¹ • ∑ k ∈ range N, T ^ k`. -/
lemma birkhoffAverage_eq_smul_sum_pow (T : E →L[𝕜] E) (N : ℕ) :
    birkhoffAverage 𝕜 T _root_.id N = ⇑((N : 𝕜)⁻¹ • ∑ k ∈ range N, T ^ k) := by
  ext x
  simp [birkhoffAverage, birkhoffSum, FunLike.coe_pow_eq_iterate, sum_apply]

/-- `T` commutes with its Birkhoff averages. -/
lemma apply_birkhoffAverage (T : E →L[𝕜] E) (N : ℕ) (x : E) :
    T (birkhoffAverage 𝕜 T _root_.id N x) = birkhoffAverage 𝕜 T _root_.id N (T x) := by
  rw [map_birkhoffAverage 𝕜 𝕜 T, ← birkhoffAverage_comp_apply, Function.comp_id, Function.id_comp]

/-- The Birkhoff averages of `T` are additive in the point. -/
lemma birkhoffAverage_apply_add (T : E →L[𝕜] E) (N : ℕ) (x y : E) :
    birkhoffAverage 𝕜 T _root_.id N (x + y) =
      birkhoffAverage 𝕜 T _root_.id N x + birkhoffAverage 𝕜 T _root_.id N y := by
  rw [birkhoffAverage_eq_smul_sum_pow, map_add]

/-- The Birkhoff averages of `T` commute with subtraction in the point. -/
lemma birkhoffAverage_apply_sub (T : E →L[𝕜] E) (N : ℕ) (x y : E) :
    birkhoffAverage 𝕜 T _root_.id N (x - y) =
      birkhoffAverage 𝕜 T _root_.id N x - birkhoffAverage 𝕜 T _root_.id N y := by
  rw [birkhoffAverage_eq_smul_sum_pow, map_sub]

/-- The Birkhoff averages of `T` commute with scalar multiplication in the point. -/
lemma birkhoffAverage_apply_smul (T : E →L[𝕜] E) (N : ℕ) (c : 𝕜) (x : E) :
    birkhoffAverage 𝕜 T _root_.id N (c • x) = c • birkhoffAverage 𝕜 T _root_.id N x := by
  rw [birkhoffAverage_eq_smul_sum_pow, map_smul]

/-- The Cesàro means at a fixed point of `T` converge to it. -/
lemma tendsto_birkhoffAverage_of_mem_ker (hx : x ∈ (1 - T).ker) :
    Tendsto (birkhoffAverage 𝕜 T _root_.id · x) atTop (𝓝 x) :=
  Function.IsFixedPt.tendsto_birkhoffAverage 𝕜 (mem_ker_one_sub_iff.1 hx) _root_.id

/-- A point minus one of its Cesàro means lies in the range of `1 - T`. -/
lemma sub_birkhoffAverage_mem_range {N : ℕ} (hN : N ≠ 0) (x : E) :
    x - birkhoffAverage 𝕜 T _root_.id N x ∈ (1 - T).range := by
  refine ⟨((N : 𝕜)⁻¹ • ∑ k ∈ range N, ∑ j ∈ range k, T ^ j) x, ?_⟩
  have hN' : (N : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 hN
  have key : (1 - T) * ((N : 𝕜)⁻¹ • ∑ k ∈ range N, ∑ j ∈ range k, T ^ j) =
      1 - (N : 𝕜)⁻¹ • ∑ k ∈ range N, T ^ k := by
    rw [mul_smul_comm, mul_sum]
    simp_rw [mul_neg_geom_sum]
    rw [sum_sub_distrib, sum_const, card_range, ← Nat.cast_smul_eq_nsmul 𝕜, smul_sub,
      inv_smul_smul₀ hN']
  rw [coe_coe, ← mul_apply_eq_comp (1 - T), key, birkhoffAverage_eq_smul_sum_pow, one_sub_apply]

/-- The difference between a point and the limit of its Cesàro means lies in the closure of the
range of `1 - T`. -/
lemma sub_mem_topologicalClosure_range_of_tendsto
    (h : Tendsto (birkhoffAverage 𝕜 T _root_.id · x) atTop (𝓝 y)) :
    x - y ∈ (1 - T).range.topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact mem_closure_of_tendsto (tendsto_const_nhds.sub h)
    ((eventually_ne_atTop 0).mono fun N hN ↦ sub_birkhoffAverage_mem_range hN x)

end ContinuousLinearMap

namespace LMLExplore.IsPowerBounded

open ContinuousLinearMap

section NontriviallyNormedField

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {T : E →L[𝕜] E}

/-- The orbit of a point under a power-bounded operator is bounded. -/
lemma isBounded_range_iterate (hT : IsPowerBounded T) (x : E) :
    Bornology.IsBounded (Set.range fun n : ℕ ↦ (⇑T)^[n] x) :=
  isBounded_iff_forall_norm_le.2 ⟨(⨆ k, ‖T ^ k‖) * ‖x‖, Set.forall_mem_range.2 fun n ↦ by
    rw [← FunLike.coe_pow_eq_iterate]
    exact le_of_opNorm_le _ (hT.norm_pow_le n) x⟩

end NontriviallyNormedField

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {T : E →L[𝕜] E} {x y : E}

/-- The Cesàro means of a power-bounded operator are bounded by `⨆ k, ‖T ^ k‖`. -/
lemma norm_smul_sum_pow_le (hT : IsPowerBounded T) (N : ℕ) :
    ‖(N : 𝕜)⁻¹ • ∑ k ∈ range N, T ^ k‖ ≤ ⨆ k, ‖T ^ k‖ := by
  rcases eq_or_ne N 0 with rfl | hN
  · simpa using hT.iSup_norm_pow_nonneg
  calc ‖(N : 𝕜)⁻¹ • ∑ k ∈ range N, T ^ k‖
      ≤ (N : ℝ)⁻¹ * ∑ _k ∈ range N, ⨆ k, ‖T ^ k‖ := by
        rw [norm_smul, norm_inv, RCLike.norm_natCast]
        gcongr
        exact (norm_sum_le _ _).trans (sum_le_sum fun k _ ↦ hT.norm_pow_le k)
    _ = ⨆ k, ‖T ^ k‖ := by simp [hN]

/-- The Cesàro means of a power-bounded operator at `x` are bounded by `⨆ k, ‖T ^ k‖ * ‖x‖`. -/
lemma norm_birkhoffAverage_le (hT : IsPowerBounded T) (N : ℕ) (x : E) :
    ‖birkhoffAverage 𝕜 T _root_.id N x‖ ≤ (⨆ k, ‖T ^ k‖) * ‖x‖ := by
  rw [birkhoffAverage_eq_smul_sum_pow]
  exact le_of_opNorm_le _ (hT.norm_smul_sum_pow_le N) x

/-- The Cesàro means of a power-bounded operator are uniformly Lipschitz. -/
lemma lipschitzWith_birkhoffAverage (hT : IsPowerBounded T) (N : ℕ) :
    LipschitzWith (⨆ k, ‖T ^ k‖).toNNReal (birkhoffAverage 𝕜 T _root_.id N) := by
  rw [birkhoffAverage_eq_smul_sum_pow]
  refine (ContinuousLinearMap.lipschitzWith _).weaken ?_
  rw [← NNReal.coe_le_coe, coe_nnNorm, Real.coe_toNNReal _ hT.iSup_norm_pow_nonneg]
  exact hT.norm_smul_sum_pow_le N

/-- **The Cesàro limit is invariant under `T`**: if the Cesàro means at `x` converge to `y`, so do
the Cesàro means at `T x`. In operator form, `Π T = Π`. -/
theorem tendsto_birkhoffAverage_apply (hT : IsPowerBounded T)
    (h : Tendsto (birkhoffAverage 𝕜 T _root_.id · x) atTop (𝓝 y)) :
    Tendsto (birkhoffAverage 𝕜 T _root_.id · (T x)) atTop (𝓝 y) := by
  have := (tendsto_birkhoffAverage_apply_sub_birkhoffAverage 𝕜
    (g := _root_.id) (hT.isBounded_range_iterate x)).add h
  simpa using this

/-- **The Cesàro limit is a fixed point**: if the Cesàro means at `x` converge to `y`, then
`T y = y`. In operator form, `T Π = Π`. -/
theorem apply_eq_of_tendsto_birkhoffAverage (hT : IsPowerBounded T)
    (h : Tendsto (birkhoffAverage 𝕜 T _root_.id · x) atTop (𝓝 y)) : T y = y := by
  refine tendsto_nhds_unique ?_ (hT.tendsto_birkhoffAverage_apply h)
  simpa [Function.comp_def, apply_birkhoffAverage] using (T.continuous.tendsto y).comp h

/-- The Cesàro means of a power-bounded operator converge to `0` on the closure of the range of
`1 - T`. -/
theorem tendsto_birkhoffAverage_of_mem_topologicalClosure_range (hT : IsPowerBounded T)
    (hx : x ∈ (1 - T).range.topologicalClosure) :
    Tendsto (birkhoffAverage 𝕜 T _root_.id · x) atTop (𝓝 0) := by
  have hclosed : IsClosed {x : E | Tendsto (birkhoffAverage 𝕜 T _root_.id · x) atTop (𝓝 0)} :=
    ((LipschitzWith.uniformEquicontinuous _ _
      hT.lipschitzWith_birkhoffAverage).equicontinuous).isClosed_setOfPred_tendsto
      continuous_const
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx
  refine closure_minimal ?_ hclosed hx
  rintro _ ⟨z, rfl⟩
  have := (tendsto_birkhoffAverage_apply_sub_birkhoffAverage 𝕜
    (g := _root_.id) (hT.isBounded_range_iterate z)).neg
  simp only [neg_sub, neg_zero] at this
  refine this.congr fun N ↦ ?_
  rw [coe_coe, one_sub_apply, birkhoffAverage_apply_sub]

/-- **The sum `ker (1 - T) ⊕ closure (range (1 - T))` is direct** for a power-bounded `T`. -/
theorem disjoint_ker_topologicalClosure_range (hT : IsPowerBounded T) :
    Disjoint ((1 - T).ker) (1 - T).range.topologicalClosure := by
  rw [Submodule.disjoint_def]
  exact fun x hx hx' ↦ tendsto_nhds_unique (tendsto_birkhoffAverage_of_mem_ker hx)
    (hT.tendsto_birkhoffAverage_of_mem_topologicalClosure_range hx')

/-- **Yosida's mean ergodic theorem**: the Cesàro means of a power-bounded operator `T` at `x`
converge iff `x ∈ ker (1 - T) ⊕ closure (range (1 - T))`. -/
theorem exists_tendsto_birkhoffAverage_iff (hT : IsPowerBounded T) :
    (∃ y, Tendsto (birkhoffAverage 𝕜 T _root_.id · x) atTop (𝓝 y)) ↔
      x ∈ (1 - T).ker ⊔ (1 - T).range.topologicalClosure := by
  constructor
  · rintro ⟨y, h⟩
    refine Submodule.mem_sup.2 ⟨y, ?_, x - y, sub_mem_topologicalClosure_range_of_tendsto h,
      add_sub_cancel _ _⟩
    exact mem_ker_one_sub_iff.2 (hT.apply_eq_of_tendsto_birkhoffAverage h)
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨a + 0, ((tendsto_birkhoffAverage_of_mem_ker ha).add
      (hT.tendsto_birkhoffAverage_of_mem_topologicalClosure_range hb)).congr fun N ↦
      (birkhoffAverage_apply_add T N a b).symm⟩

/-- The limit of the Cesàro means at `x` is `x` exactly when `x` is a fixed point of `T`. -/
theorem tendsto_birkhoffAverage_self_iff (hT : IsPowerBounded T) :
    Tendsto (birkhoffAverage 𝕜 T _root_.id · x) atTop (𝓝 x) ↔ x ∈ (1 - T).ker :=
  ⟨fun h ↦ mem_ker_one_sub_iff.2 (hT.apply_eq_of_tendsto_birkhoffAverage h),
    tendsto_birkhoffAverage_of_mem_ker⟩

/-- The limit of the Cesàro means at `x` is `0` exactly when `x` lies in the closure of the range
of `1 - T`. -/
theorem tendsto_birkhoffAverage_zero_iff (hT : IsPowerBounded T) :
    Tendsto (birkhoffAverage 𝕜 T _root_.id · x) atTop (𝓝 0) ↔
      x ∈ (1 - T).range.topologicalClosure :=
  ⟨fun h ↦ by simpa using sub_mem_topologicalClosure_range_of_tendsto h,
    hT.tendsto_birkhoffAverage_of_mem_topologicalClosure_range⟩

/-- The limit of the Cesàro means is bounded by `⨆ k, ‖T ^ k‖` times the norm of the point. -/
theorem norm_le_of_tendsto_birkhoffAverage (hT : IsPowerBounded T)
    (h : Tendsto (birkhoffAverage 𝕜 T _root_.id · x) atTop (𝓝 y)) :
    ‖y‖ ≤ (⨆ k, ‖T ^ k‖) * ‖x‖ :=
  le_of_tendsto h.norm (Eventually.of_forall fun N ↦ hT.norm_birkhoffAverage_le N x)

/-- In a Banach space, the subspace `ker (1 - T) ⊕ closure (range (1 - T))` on which the Cesàro
means of a power-bounded operator converge is closed. -/
theorem isClosed_ker_sup_topologicalClosure_range [CompleteSpace E] (hT : IsPowerBounded T) :
    IsClosed (((1 - T).ker ⊔ (1 - T).range.topologicalClosure : Submodule 𝕜 E) : Set E) := by
  -- In a complete space this is the set of points with Cauchy Cesàro means, a closed set because
  -- the differences of Cesàro means are uniformly Lipschitz.
  have hset : (((1 - T).ker ⊔ (1 - T).range.topologicalClosure : Submodule 𝕜 E) : Set E) =
      {x | Tendsto (fun p : ℕ × ℕ ↦ birkhoffAverage 𝕜 T _root_.id p.1 x -
        birkhoffAverage 𝕜 T _root_.id p.2 x) atTop (𝓝 0)} := by
    ext x
    rw [SetLike.mem_coe, ← hT.exists_tendsto_birkhoffAverage_iff, Set.mem_ofPred_eq,
      tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero, ← dist_eq_norm]
    exact ⟨fun ⟨_, h⟩ ↦ cauchySeq_iff_tendsto_dist_atTop_0.1 h.cauchySeq,
      fun h ↦ cauchySeq_tendsto_of_complete (cauchySeq_iff_tendsto_dist_atTop_0.2 h)⟩
  rw [hset]
  exact ((LipschitzWith.uniformEquicontinuous _ _ fun p : ℕ × ℕ ↦
    (hT.lipschitzWith_birkhoffAverage p.1).sub
      (hT.lipschitzWith_birkhoffAverage p.2)).equicontinuous).isClosed_setOfPred_tendsto
    continuous_const

/-- In finite dimension, the Cesàro means of a power-bounded operator converge everywhere:
`ker (1 - T) ⊕ closure (range (1 - T))` is the whole space. -/
theorem ker_sup_topologicalClosure_range_eq_top [FiniteDimensional 𝕜 E]
    (hT : IsPowerBounded T) :
    (1 - T).ker ⊔ (1 - T).range.topologicalClosure = ⊤ := by
  have hdisj := hT.disjoint_ker_topologicalClosure_range
  rw [(Submodule.isClosed_of_finiteDimensional _).submodule_topologicalClosure_eq] at hdisj ⊢
  refine Submodule.eq_top_of_disjoint _ _ ?_ hdisj
  rw [add_comm]
  exact ((1 - T : E →L[𝕜] E) : E →ₗ[𝕜] E).finrank_range_add_finrank_ker.ge

/-- When `ker (1 - T) ⊔ closure (range (1 - T))` is the whole space, the fixed points of a
power-bounded `T` and the closure of the range of `1 - T` are complementary. -/
theorem isCompl_ker_topologicalClosure_range (hT : IsPowerBounded T)
    (hF : (1 - T).ker ⊔ (1 - T).range.topologicalClosure = ⊤) :
    IsCompl ((1 - T).ker) (1 - T).range.topologicalClosure :=
  ⟨hT.disjoint_ker_topologicalClosure_range, codisjoint_iff.2 hF⟩

section MeanErgodicProj

variable (hT : IsPowerBounded T)
  (hF : (1 - T).ker ⊔ (1 - T).range.topologicalClosure = ⊤)
include hT hF

private lemma tendsto_birkhoffAverage_limUnder (x : E) :
    Tendsto (birkhoffAverage 𝕜 T _root_.id · x) atTop
      (𝓝 (limUnder atTop (birkhoffAverage 𝕜 T _root_.id · x))) :=
  tendsto_nhds_limUnder (hT.exists_tendsto_birkhoffAverage_iff.2 (hF ▸ Submodule.mem_top))

/-- The *mean ergodic projection* `Π` of a power-bounded operator `T` whose Cesàro means converge
everywhere, that is, such that `ker (1 - T) ⊔ closure (range (1 - T))` is the whole space: `Π x`
is the limit of the Cesàro means `(N : 𝕜)⁻¹ • ∑ k ∈ range N, T ^ k x`. It is the projection onto
`ker (1 - T)` along `closure (range (1 - T))`. -/
noncomputable def meanErgodicProj : E →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun x := limUnder atTop (birkhoffAverage 𝕜 T _root_.id · x)
      map_add' x y := by
        refine tendsto_nhds_unique (hT.tendsto_birkhoffAverage_limUnder hF (x + y)) ?_
        refine ((hT.tendsto_birkhoffAverage_limUnder hF x).add
          (hT.tendsto_birkhoffAverage_limUnder hF y)).congr fun N ↦
          (birkhoffAverage_apply_add T N x y).symm
      map_smul' c x := by
        rw [RingHom.id_apply]
        refine tendsto_nhds_unique (hT.tendsto_birkhoffAverage_limUnder hF (c • x)) ?_
        exact ((hT.tendsto_birkhoffAverage_limUnder hF x).const_smul c).congr fun N ↦
          (birkhoffAverage_apply_smul T N c x).symm }
    (⨆ k, ‖T ^ k‖) fun x ↦
      hT.norm_le_of_tendsto_birkhoffAverage (hT.tendsto_birkhoffAverage_limUnder hF x)

/-- **Yosida's mean ergodic theorem**: the Cesàro means of `T` at `x` converge to the mean
ergodic projection of `x`. -/
theorem tendsto_birkhoffAverage_meanErgodicProj (x : E) :
    Tendsto (birkhoffAverage 𝕜 T _root_.id · x) atTop (𝓝 (hT.meanErgodicProj hF x)) :=
  hT.tendsto_birkhoffAverage_limUnder hF x

/-- The mean ergodic projection of `x` is the limit of the Cesàro means of `T` at `x`. -/
theorem meanErgodicProj_apply_eq_iff :
    hT.meanErgodicProj hF x = y ↔ Tendsto (birkhoffAverage 𝕜 T _root_.id · x) atTop (𝓝 y) :=
  ⟨fun h ↦ h ▸ hT.tendsto_birkhoffAverage_meanErgodicProj hF x,
    tendsto_nhds_unique (hT.tendsto_birkhoffAverage_meanErgodicProj hF x)⟩

/-- The operator norm of the mean ergodic projection is at most `⨆ k, ‖T ^ k‖`. -/
theorem norm_meanErgodicProj_le : ‖hT.meanErgodicProj hF‖ ≤ ⨆ k, ‖T ^ k‖ :=
  LinearMap.mkContinuous_norm_le _ hT.iSup_norm_pow_nonneg _

/-- `Π (T x) = Π x`. -/
@[simp]
theorem meanErgodicProj_apply_apply (x : E) :
    hT.meanErgodicProj hF (T x) = hT.meanErgodicProj hF x :=
  (hT.meanErgodicProj_apply_eq_iff hF).2
    (hT.tendsto_birkhoffAverage_apply (hT.tendsto_birkhoffAverage_meanErgodicProj hF x))

/-- `T (Π x) = Π x`. -/
@[simp]
theorem apply_meanErgodicProj_apply (x : E) :
    T (hT.meanErgodicProj hF x) = hT.meanErgodicProj hF x :=
  hT.apply_eq_of_tendsto_birkhoffAverage (hT.tendsto_birkhoffAverage_meanErgodicProj hF x)

/-- `Π (Π x) = Π x`. -/
@[simp]
theorem meanErgodicProj_meanErgodicProj_apply (x : E) :
    hT.meanErgodicProj hF (hT.meanErgodicProj hF x) = hT.meanErgodicProj hF x :=
  (hT.meanErgodicProj_apply_eq_iff hF).2
    (tendsto_birkhoffAverage_of_mem_ker
      (mem_ker_one_sub_iff.2 (hT.apply_meanErgodicProj_apply hF x)))

/-- `Π x = x` exactly when `x` is a fixed point of `T`. -/
theorem meanErgodicProj_apply_eq_self_iff : hT.meanErgodicProj hF x = x ↔ x ∈ (1 - T).ker := by
  rw [meanErgodicProj_apply_eq_iff, hT.tendsto_birkhoffAverage_self_iff]

/-- `Π x = 0` exactly when `x` lies in the closure of the range of `1 - T`. -/
theorem meanErgodicProj_apply_eq_zero_iff :
    hT.meanErgodicProj hF x = 0 ↔ x ∈ (1 - T).range.topologicalClosure := by
  rw [meanErgodicProj_apply_eq_iff, hT.tendsto_birkhoffAverage_zero_iff]

/-- `Π` fixes the fixed points of `T`. -/
theorem meanErgodicProj_apply_of_mem_ker (hx : x ∈ (1 - T).ker) : hT.meanErgodicProj hF x = x :=
  (hT.meanErgodicProj_apply_eq_self_iff hF).2 hx

/-- `Π T = Π`. -/
@[simp]
theorem meanErgodicProj_mul : hT.meanErgodicProj hF * T = hT.meanErgodicProj hF := by
  ext x
  exact hT.meanErgodicProj_apply_apply hF x

/-- `T Π = Π`. -/
@[simp]
theorem mul_meanErgodicProj : T * hT.meanErgodicProj hF = hT.meanErgodicProj hF := by
  ext x
  exact hT.apply_meanErgodicProj_apply hF x

/-- `Π T ^ n = Π`. -/
@[simp]
theorem meanErgodicProj_mul_pow (n : ℕ) :
    hT.meanErgodicProj hF * T ^ n = hT.meanErgodicProj hF := by
  induction n with
  | zero => rw [pow_zero, mul_one]
  | succ n ih => rw [pow_succ, ← mul_assoc, ih, meanErgodicProj_mul]

/-- `T ^ n Π = Π`. -/
@[simp]
theorem pow_mul_meanErgodicProj (n : ℕ) :
    T ^ n * hT.meanErgodicProj hF = hT.meanErgodicProj hF := by
  induction n with
  | zero => rw [pow_zero, one_mul]
  | succ n ih => rw [pow_succ', mul_assoc, ih, mul_meanErgodicProj]

/-- `Π (1 - T) = 0`. -/
@[simp]
theorem meanErgodicProj_mul_one_sub : hT.meanErgodicProj hF * (1 - T) = 0 := by
  rw [mul_sub, mul_one, meanErgodicProj_mul, sub_self]

/-- `(1 - T) Π = 0`. -/
@[simp]
theorem one_sub_mul_meanErgodicProj : (1 - T) * hT.meanErgodicProj hF = 0 := by
  rw [sub_mul, one_mul, mul_meanErgodicProj, sub_self]

/-- `Π ^ 2 = Π`: the mean ergodic projection is a projection. -/
theorem isIdempotentElem_meanErgodicProj : IsIdempotentElem (hT.meanErgodicProj hF) := by
  ext x
  exact hT.meanErgodicProj_meanErgodicProj_apply hF x

/-- `Π * Π = Π`. -/
@[simp]
theorem meanErgodicProj_mul_self :
    hT.meanErgodicProj hF * hT.meanErgodicProj hF = hT.meanErgodicProj hF :=
  (hT.isIdempotentElem_meanErgodicProj hF).eq

/-- The range of the mean ergodic projection is the space of fixed points of `T`. -/
theorem range_meanErgodicProj :
    (hT.meanErgodicProj hF).range = (1 - T).ker := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨x, (hT.meanErgodicProj_apply_eq_iff hF).2
    (tendsto_birkhoffAverage_of_mem_ker hx)⟩⟩
  rintro ⟨x, rfl⟩
  exact mem_ker_one_sub_iff.2 (hT.apply_meanErgodicProj_apply hF x)

/-- The kernel of the mean ergodic projection is the closure of the range of `1 - T`. -/
theorem ker_meanErgodicProj :
    (hT.meanErgodicProj hF).ker = (1 - T).range.topologicalClosure := by
  ext x
  rw [LinearMap.mem_ker, coe_coe, meanErgodicProj_apply_eq_zero_iff]

end MeanErgodicProj

/-- **Uniform mean ergodic theorem in finite dimension**: the Cesàro means
`(N : 𝕜)⁻¹ • ∑ k ∈ range N, T ^ k` of a power-bounded operator on a finite-dimensional space
converge in operator norm to its mean ergodic projection. -/
theorem tendsto_cesaro_meanErgodicProj [FiniteDimensional 𝕜 E] (hT : IsPowerBounded T) :
    Tendsto (fun N : ℕ ↦ (N : 𝕜)⁻¹ • ∑ k ∈ range N, T ^ k) atTop
      (𝓝 (hT.meanErgodicProj hT.ker_sup_topologicalClosure_range_eq_top)) := by
  refine LMLExplore.tendsto_clm_apply.2 fun x ↦ ?_
  simpa [birkhoffAverage_eq_smul_sum_pow] using
    hT.tendsto_birkhoffAverage_meanErgodicProj hT.ker_sup_topologicalClosure_range_eq_top x

end LMLExplore.IsPowerBounded
