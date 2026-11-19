/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import LMLExplore.Analysis.Convex.Simplex
public import LMLExplore.Analysis.Matrix.Operator
public import LMLExplore.Analysis.Normed.Operator.Deviation
public import LMLExplore.Topology.Instances.Matrix

/-!
# The limiting and deviation matrices of a stochastic matrix

Let `P` be a row-stochastic matrix indexed by a finite type `S`. Acting on functions `S → ℝ` by
`mulVec`, it is a contraction for the sup norm, so Yosida's mean ergodic theorem and the group
inverse of `1 - P` apply to it. This file specializes them to matrices.

* The *limiting matrix* `P* = lim_N N⁻¹ ∑ k < N, P ^ k` is stochastic and satisfies
  `P P* = P* P = P* P* = P*`. Each of its rows is an invariant probability vector of `P`, so every
  finite Markov chain has an invariant law. When the powers `P ^ n` converge, their limit is `P*`.
* The *deviation matrix* `D = (1 - P + P*)⁻¹ - P*` is the group inverse of `1 - P`:
  `(1 - P) D = D (1 - P) = 1 - P*` and `D P* = P* D = 0`. It is the Cesàro limit of the partial
  sums `∑ k < n, (P ^ k - P*)`, and the sum of the series `∑ n, (P ^ n - P*)` when the powers of
  `P` converge.
* For a reward vector `r`, `(g, h) = (P* r, D r)` is the unique solution of the evaluation
  equations `(1 - P) g = 0`, `g + (1 - P) h = r`, `P* h = 0`: these are the gain and the bias of
  the Markov reward process `(P, r)`. As `γ ↑ 1`, `(1 - γ) (1 - γ P)⁻¹ → P*` and
  `((1 - γ) (1 - γ P)⁻¹ - P*) / (1 - γ) → D`.

The bridge to the operator theory is the algebra equivalence
`Matrix.toContinuousLinAlgEquiv'` between square matrices and continuous linear operators on
`S → ℝ` (`LMLExplore.Analysis.Matrix.Operator`), under which `P*` is the mean ergodic projection
(`Matrix.toContinuousLinAlgEquiv'_limitingMatrix`) and `D` the deviation operator
(`Matrix.toContinuousLinAlgEquiv'_deviationMatrix`) of the action of `P`.

## Main definitions

* `Matrix.limitingMatrix`: the limit of the Cesàro means of the powers of a matrix.
* `Matrix.deviationMatrix`: `(1 - P + P*)⁻¹ - P*`.

## Main statements

* `Matrix.tendsto_cesaro_limitingMatrix`, `Matrix.limitingMatrix_mem_rowStochastic`,
  `Matrix.limitingMatrix_mulVec_eq_self_iff`,
  `Matrix.mul_limitingMatrix`, `Matrix.limitingMatrix_mul`, `Matrix.limitingMatrix_mul_self`.
* `Matrix.limitingMatrix_apply_vecMul`, `Matrix.exists_mem_simplex_vecMul_eq_self`: the rows of
  `P*` are invariant, and every stochastic matrix has an invariant probability vector.
* `Matrix.limitingMatrix_eq_of_tendsto_pow`, `Matrix.hasSum_pow_sub_limitingMatrix`.
* `Matrix.isUnit_one_sub_add_limitingMatrix`, `Matrix.one_sub_mul_deviationMatrix`,
  `Matrix.deviationMatrix_mul_one_sub`, `Matrix.deviationMatrix_mul_limitingMatrix`,
  `Matrix.limitingMatrix_mul_deviationMatrix`: `D` is the group inverse of `1 - P`, and
  `Matrix.eq_deviationMatrix_of_mul_one_sub`, `Matrix.eq_deviationMatrix_of_one_sub_mul`
  characterize it.
* `Matrix.tendsto_cesaro_sum_pow_sub_limitingMatrix`.
* `Matrix.eq_limitingMatrix_mulVec_and_eq_deviationMatrix_mulVec_iff`: the evaluation
  equations [P, Theorem 8.2.6].
* `Matrix.eq_limitingMatrix_mulVec_and_eq_deviationMatrix_mulVec_add_iff`: all solutions of the
  first two evaluation equations.
* `Matrix.inv_one_sub_smul_eq_laurent`: the Laurent expansion of the resolvent
  [P, Theorem 8.2.3].
* `Matrix.tendsto_one_sub_smul_inv_one_sub_smul_limitingMatrix`,
  `Matrix.tendsto_inv_smul_one_sub_smul_inv_one_sub_smul_sub_deviationMatrix`: the limits of the
  resolvent as `γ ↑ 1` [P, Corollaries 8.2.4–8.2.5].

## References

* [P] M. L. Puterman, *Markov Decision Processes*, Wiley, 1994, Appendix A and Section 8.2.
* T. Lattimore and C. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Exercises 38.7 and 38.9.
-/

public section

open Filter Finset LMLExplore Topology
open scoped Ring

namespace Matrix

variable {S : Type*} [Fintype S] [DecidableEq S]

variable {P : Matrix S S ℝ}

/-! ### The limiting matrix -/

/-- The *limiting matrix* `P*` of a square matrix `P`: the limit of the Cesàro means
`N⁻¹ ∑ k < N, P ^ k` of its powers. For a row-stochastic matrix the limit exists
(`Matrix.tendsto_cesaro_limitingMatrix`); when the Cesàro means do not converge, the value is
junk. -/
noncomputable def limitingMatrix (P : Matrix S S ℝ) : Matrix S S ℝ :=
  limUnder atTop fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ k ∈ range n, P ^ k

theorem limitingMatrix_def (P : Matrix S S ℝ) :
    P.limitingMatrix = limUnder atTop fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ k ∈ range n, P ^ k :=
  (rfl)

section Limiting

variable (hP : P ∈ rowStochastic ℝ S)
include hP

/-- The actions of the Cesàro means of `P` converge to the mean ergodic projection. -/
private lemma tendsto_toContinuousLinAlgEquiv'_cesaro :
    Tendsto (fun n : ℕ ↦ toContinuousLinAlgEquiv' ℝ ((n : ℝ)⁻¹ • ∑ k ∈ range n, P ^ k)) atTop
      (𝓝 ((isPowerBounded_toContinuousLinAlgEquiv' hP).meanErgodicProj
        (isPowerBounded_toContinuousLinAlgEquiv' hP).ker_sup_topologicalClosure_range_eq_top)) := by
  simpa [map_sum, map_pow] using
    (isPowerBounded_toContinuousLinAlgEquiv' hP).tendsto_cesaro_meanErgodicProj

/-- The Cesàro means `N⁻¹ ∑ k < N, P ^ k` of a stochastic matrix converge to its limiting
matrix. -/
theorem tendsto_cesaro_limitingMatrix :
    Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ k ∈ range n, P ^ k) atTop (𝓝 P.limitingMatrix) := by
  refine tendsto_nhds_limUnder ⟨(toContinuousLinAlgEquiv' ℝ).symm
    ((isPowerBounded_toContinuousLinAlgEquiv' hP).meanErgodicProj
      (isPowerBounded_toContinuousLinAlgEquiv' hP).ker_sup_topologicalClosure_range_eq_top), ?_⟩
  rw [← tendsto_toContinuousLinAlgEquiv'_iff, AlgEquiv.apply_symm_apply]
  exact tendsto_toContinuousLinAlgEquiv'_cesaro hP

/-- The limiting matrix of `P` acts as the mean ergodic projection of the action of `P`. -/
theorem toContinuousLinAlgEquiv'_limitingMatrix :
    toContinuousLinAlgEquiv' ℝ P.limitingMatrix =
      (isPowerBounded_toContinuousLinAlgEquiv' hP).meanErgodicProj
        (isPowerBounded_toContinuousLinAlgEquiv' hP).ker_sup_topologicalClosure_range_eq_top :=
  tendsto_nhds_unique (tendsto_toContinuousLinAlgEquiv'_iff.2 (tendsto_cesaro_limitingMatrix hP))
    (tendsto_toContinuousLinAlgEquiv'_cesaro hP)

/-- `P P* = P*`. -/
theorem mul_limitingMatrix : P * P.limitingMatrix = P.limitingMatrix :=
  (toContinuousLinAlgEquiv' ℝ).injective <| by
    rw [map_mul, toContinuousLinAlgEquiv'_limitingMatrix hP, IsPowerBounded.mul_meanErgodicProj]

/-- `P* P = P*`. -/
theorem limitingMatrix_mul : P.limitingMatrix * P = P.limitingMatrix :=
  (toContinuousLinAlgEquiv' ℝ).injective <| by
    rw [map_mul, toContinuousLinAlgEquiv'_limitingMatrix hP, IsPowerBounded.meanErgodicProj_mul]

/-- `P ^ n P* = P*`. -/
theorem pow_mul_limitingMatrix (n : ℕ) : P ^ n * P.limitingMatrix = P.limitingMatrix :=
  (toContinuousLinAlgEquiv' ℝ).injective <| by
    rw [map_mul, map_pow, toContinuousLinAlgEquiv'_limitingMatrix hP,
      IsPowerBounded.pow_mul_meanErgodicProj]

/-- `P* P ^ n = P*`. -/
theorem limitingMatrix_mul_pow (n : ℕ) : P.limitingMatrix * P ^ n = P.limitingMatrix :=
  (toContinuousLinAlgEquiv' ℝ).injective <| by
    rw [map_mul, map_pow, toContinuousLinAlgEquiv'_limitingMatrix hP,
      IsPowerBounded.meanErgodicProj_mul_pow]

/-- `P* P* = P*`: the limiting matrix is idempotent. -/
theorem limitingMatrix_mul_self : P.limitingMatrix * P.limitingMatrix = P.limitingMatrix :=
  (toContinuousLinAlgEquiv' ℝ).injective <| by
    rw [map_mul, toContinuousLinAlgEquiv'_limitingMatrix hP,
      IsPowerBounded.meanErgodicProj_mul_self]

/-- A vector is fixed by `P*` exactly when it is harmonic for `P`: `P* v = v ↔ P v = v`. -/
theorem limitingMatrix_mulVec_eq_self_iff {v : S → ℝ} :
    P.limitingMatrix *ᵥ v = v ↔ P *ᵥ v = v := by
  rw [← toContinuousLinAlgEquiv'_apply, toContinuousLinAlgEquiv'_limitingMatrix hP,
    IsPowerBounded.meanErgodicProj_apply_eq_self_iff, ContinuousLinearMap.mem_ker_one_sub_iff,
    toContinuousLinAlgEquiv'_apply]

/-- The limiting matrix of a stochastic matrix is stochastic. -/
theorem limitingMatrix_mem_rowStochastic : P.limitingMatrix ∈ rowStochastic ℝ S := by
  refine isClosed_rowStochastic.mem_of_tendsto (tendsto_cesaro_limitingMatrix hP)
    (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  -- The Cesàro mean is a convex combination of the stochastic matrices `P ^ k`.
  rw [smul_sum]
  refine convex_rowStochastic.sum_mem (fun _ _ ↦ by positivity) ?_
    fun k _ ↦ pow_mem hP k
  rw [sum_const, card_range, nsmul_eq_mul, mul_inv_cancel₀ (by positivity)]

/-- Every row of the limiting matrix is a probability vector. -/
theorem limitingMatrix_apply_mem_simplex (i : S) : P.limitingMatrix i ∈ simplex S :=
  mem_simplex_iff.2 ⟨fun j ↦ (limitingMatrix_mem_rowStochastic hP).1 i j,
    sum_row_of_mem_rowStochastic (limitingMatrix_mem_rowStochastic hP) i⟩

/-- Every row of the limiting matrix is invariant: `P* i ᵥ* P = P* i`. -/
theorem limitingMatrix_apply_vecMul (i : S) :
    P.limitingMatrix i ᵥ* P = P.limitingMatrix i := by
  ext j
  rw [← mul_apply_eq_vecMul, limitingMatrix_mul hP]

/-- Every stochastic matrix on a nonempty finite type has an invariant probability vector. -/
theorem exists_mem_simplex_vecMul_eq_self [Nonempty S] : ∃ π ∈ simplex S, π ᵥ* P = π :=
  let i := Classical.arbitrary S
  ⟨P.limitingMatrix i, limitingMatrix_apply_mem_simplex hP i, limitingMatrix_apply_vecMul hP i⟩

/-- If the powers of a stochastic matrix converge, their limit is the limiting matrix. -/
theorem limitingMatrix_eq_of_tendsto_pow {L : Matrix S S ℝ}
    (h : Tendsto (fun n ↦ P ^ n) atTop (𝓝 L)) : P.limitingMatrix = L :=
  (toContinuousLinAlgEquiv' ℝ).injective <| by
    have hL := Filter.Tendsto.cesaro_smul (tendsto_toContinuousLinAlgEquiv'_iff.2 h)
    simp only [map_pow] at hL
    rw [toContinuousLinAlgEquiv'_limitingMatrix hP]
    exact tendsto_nhds_unique
      (isPowerBounded_toContinuousLinAlgEquiv' hP).tendsto_cesaro_meanErgodicProj hL

/-- `(P - P*) ^ (n + 1) = P ^ (n + 1) - P*`. -/
theorem sub_limitingMatrix_pow_succ (n : ℕ) :
    (P - P.limitingMatrix) ^ (n + 1) = P ^ (n + 1) - P.limitingMatrix := by
  induction n with
  | zero => rw [zero_add, pow_one, pow_one]
  | succ n ih =>
    rw [pow_succ, ih]
    simp [sub_mul, mul_sub, ← pow_succ, pow_mul_limitingMatrix hP, limitingMatrix_mul hP,
      limitingMatrix_mul_self hP]

end Limiting

/-! ### The deviation matrix -/

/-- The *deviation matrix* `D = (1 - P + P*)⁻¹ - P*` of a square matrix `P`, with `P*` its
limiting matrix. For a stochastic matrix it is the group inverse of `1 - P`
(`Matrix.one_sub_mul_deviationMatrix`, `Matrix.deviationMatrix_mul_limitingMatrix`). -/
noncomputable def deviationMatrix (P : Matrix S S ℝ) : Matrix S S ℝ :=
  (1 - P + P.limitingMatrix)⁻¹ - P.limitingMatrix

theorem deviationMatrix_def (P : Matrix S S ℝ) :
    P.deviationMatrix = (1 - P + P.limitingMatrix)⁻¹ - P.limitingMatrix :=
  (rfl)

section Deviation

variable (hP : P ∈ rowStochastic ℝ S)
include hP

/-- The matrix `1 - P + P*` of a stochastic matrix is invertible. -/
theorem isUnit_one_sub_add_limitingMatrix : IsUnit (1 - P + P.limitingMatrix) := by
  rw [← isUnit_map_iff (toContinuousLinAlgEquiv' ℝ), map_add, map_sub,
    map_one, toContinuousLinAlgEquiv'_limitingMatrix hP]
  exact (isPowerBounded_toContinuousLinAlgEquiv' hP).isUnit_one_sub_add_meanErgodicProj
    (isPowerBounded_toContinuousLinAlgEquiv' hP).ker_sup_range_eq_top

/-- The deviation matrix of `P` acts as the deviation operator of the action of `P`. -/
theorem toContinuousLinAlgEquiv'_deviationMatrix :
    toContinuousLinAlgEquiv' ℝ P.deviationMatrix =
      (isPowerBounded_toContinuousLinAlgEquiv' hP).deviation
        (isPowerBounded_toContinuousLinAlgEquiv' hP).ker_sup_range_eq_top := by
  rw [deviationMatrix_def, map_sub, toContinuousLinAlgEquiv'_inv, map_add, map_sub,
    map_one, toContinuousLinAlgEquiv'_limitingMatrix hP,
    IsPowerBounded.ringInverse_one_sub_add_meanErgodicProj, add_sub_cancel_right]

/-- `(1 - P) D = 1 - P*`. -/
theorem one_sub_mul_deviationMatrix : (1 - P) * P.deviationMatrix = 1 - P.limitingMatrix :=
  (toContinuousLinAlgEquiv' ℝ).injective <| by
    rw [map_mul, map_sub, map_sub, map_one, toContinuousLinAlgEquiv'_deviationMatrix hP,
      toContinuousLinAlgEquiv'_limitingMatrix hP, IsPowerBounded.one_sub_mul_deviation]

/-- `D (1 - P) = 1 - P*`. -/
theorem deviationMatrix_mul_one_sub : P.deviationMatrix * (1 - P) = 1 - P.limitingMatrix :=
  (toContinuousLinAlgEquiv' ℝ).injective <| by
    rw [map_mul, map_sub, map_sub, map_one, toContinuousLinAlgEquiv'_deviationMatrix hP,
      toContinuousLinAlgEquiv'_limitingMatrix hP, IsPowerBounded.deviation_mul_one_sub]

/-- `D P* = 0`. -/
theorem deviationMatrix_mul_limitingMatrix : P.deviationMatrix * P.limitingMatrix = 0 :=
  (toContinuousLinAlgEquiv' ℝ).injective <| by
    rw [map_mul, map_zero, toContinuousLinAlgEquiv'_deviationMatrix hP,
      toContinuousLinAlgEquiv'_limitingMatrix hP, IsPowerBounded.deviation_mul_meanErgodicProj]

/-- `P* D = 0`. -/
theorem limitingMatrix_mul_deviationMatrix : P.limitingMatrix * P.deviationMatrix = 0 :=
  (toContinuousLinAlgEquiv' ℝ).injective <| by
    rw [map_mul, map_zero, toContinuousLinAlgEquiv'_deviationMatrix hP,
      toContinuousLinAlgEquiv'_limitingMatrix hP, IsPowerBounded.meanErgodicProj_mul_deviation]

/-- `D` is the only matrix `X` with `X (1 - P) = 1 - P*` and `X P* = 0`. -/
theorem eq_deviationMatrix_of_mul_one_sub {X : Matrix S S ℝ}
    (h₁ : X * (1 - P) = 1 - P.limitingMatrix) (h₂ : X * P.limitingMatrix = 0) :
    X = P.deviationMatrix :=
  (toContinuousLinAlgEquiv' ℝ).injective <| by
    rw [toContinuousLinAlgEquiv'_deviationMatrix hP]
    refine IsPowerBounded.eq_deviation_of_mul_one_sub _ _ ?_ ?_
    · simpa [toContinuousLinAlgEquiv'_limitingMatrix hP] using congr(toContinuousLinAlgEquiv' ℝ $h₁)
    · simpa [toContinuousLinAlgEquiv'_limitingMatrix hP] using congr(toContinuousLinAlgEquiv' ℝ $h₂)

/-- `D` is the only matrix `X` with `(1 - P) X = 1 - P*` and `P* X = 0`. -/
theorem eq_deviationMatrix_of_one_sub_mul {X : Matrix S S ℝ}
    (h₁ : (1 - P) * X = 1 - P.limitingMatrix) (h₂ : P.limitingMatrix * X = 0) :
    X = P.deviationMatrix :=
  (toContinuousLinAlgEquiv' ℝ).injective <| by
    rw [toContinuousLinAlgEquiv'_deviationMatrix hP]
    refine IsPowerBounded.eq_deviation_of_one_sub_mul _ _ ?_ ?_
    · simpa [toContinuousLinAlgEquiv'_limitingMatrix hP] using congr(toContinuousLinAlgEquiv' ℝ $h₁)
    · simpa [toContinuousLinAlgEquiv'_limitingMatrix hP] using congr(toContinuousLinAlgEquiv' ℝ $h₂)

/-- The partial sums of the deviations are `∑ k < n, (P ^ k - P*) = D (1 - P ^ n)`. -/
theorem sum_range_pow_sub_limitingMatrix (n : ℕ) :
    ∑ k ∈ range n, (P ^ k - P.limitingMatrix) = P.deviationMatrix * (1 - P ^ n) :=
  (toContinuousLinAlgEquiv' ℝ).injective <| by
    simp only [map_sum, map_sub, map_mul, map_pow, map_one,
      toContinuousLinAlgEquiv'_deviationMatrix hP, toContinuousLinAlgEquiv'_limitingMatrix hP]
    exact IsPowerBounded.sum_range_pow_sub_meanErgodicProj _ _ n

/-- The deviation matrix is the Cesàro limit of the partial sums `∑ k < n, (P ^ k - P*)`. -/
theorem tendsto_cesaro_sum_pow_sub_limitingMatrix :
    Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ • ∑ n ∈ range N, ∑ k ∈ range n,
      (P ^ k - P.limitingMatrix)) atTop (𝓝 P.deviationMatrix) := by
  rw [← tendsto_toContinuousLinAlgEquiv'_iff, toContinuousLinAlgEquiv'_deviationMatrix hP]
  simpa only [map_smul, map_sum, map_sub, map_pow, toContinuousLinAlgEquiv'_limitingMatrix hP]
    using (isPowerBounded_toContinuousLinAlgEquiv' hP).tendsto_cesaro_sum_pow_sub_meanErgodicProj
      (isPowerBounded_toContinuousLinAlgEquiv' hP).ker_sup_range_eq_top

/-- If the powers of a stochastic matrix converge, the deviation matrix is the sum of the series
`∑ n, (P ^ n - P*)`. -/
theorem hasSum_pow_sub_limitingMatrix {L : Matrix S S ℝ}
    (h : Tendsto (fun n ↦ P ^ n) atTop (𝓝 L)) :
    HasSum (fun n ↦ P ^ n - P.limitingMatrix) P.deviationMatrix := by
  rw [← limitingMatrix_eq_of_tendsto_pow hP h] at h
  -- The powers of `Q = P - P*` are `P ^ n - P*` for `n ≥ 1`, so they tend to `0`, and the
  -- geometric series of `Q` acting on `S → ℝ` converges.
  set Q := toContinuousLinAlgEquiv' ℝ (P - P.limitingMatrix)
  have hQ : ∀ n, Q ^ (n + 1) = toContinuousLinAlgEquiv' ℝ (P ^ (n + 1) - P.limitingMatrix) :=
    fun n ↦ by rw [← map_pow, sub_limitingMatrix_pow_succ hP]
  have hQ₀ : Tendsto (fun n ↦ Q ^ n) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    simp only [hQ, ← map_zero (toContinuousLinAlgEquiv' ℝ)]
    exact tendsto_toContinuousLinAlgEquiv'_iff.2
      (by simpa using ((tendsto_add_atTop_iff_nat 1).2 h).sub_const P.limitingMatrix)
  have hsum : Summable fun n ↦ P ^ n - P.limitingMatrix := by
    rw [← summable_nat_add_iff 1, ← summable_toContinuousLinAlgEquiv'_iff]
    simp only [← hQ]
    exact (summable_nat_add_iff 1).2 (summable_pow_of_tendsto_pow_atTop_nhds_zero hQ₀)
  rw [hsum.hasSum_iff_tendsto_nat]
  simp only [sum_range_pow_sub_limitingMatrix hP]
  have hD : Tendsto (fun n ↦ P.deviationMatrix * (1 - P ^ n)) atTop
      (𝓝 (P.deviationMatrix * (1 - P.limitingMatrix))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub h)
  rwa [mul_sub, mul_one, deviationMatrix_mul_limitingMatrix hP, sub_zero] at hD

/-- **The evaluation equations** [P, Theorem 8.2.6]. For a stochastic matrix `P` and a reward
vector `r`, the gain `g = P* r` and the bias `h = D r` form the unique solution of
`(1 - P) g = 0`, `g + (1 - P) h = r` and `P* h = 0`. -/
theorem eq_limitingMatrix_mulVec_and_eq_deviationMatrix_mulVec_iff {g h r : S → ℝ} :
    g = P.limitingMatrix *ᵥ r ∧ h = P.deviationMatrix *ᵥ r ↔
      (1 - P) *ᵥ g = 0 ∧ g + (1 - P) *ᵥ h = r ∧ P.limitingMatrix *ᵥ h = 0 := by
  simp only [← toContinuousLinAlgEquiv'_apply, map_sub, map_one,
    toContinuousLinAlgEquiv'_limitingMatrix hP, toContinuousLinAlgEquiv'_deviationMatrix hP]
  exact (isPowerBounded_toContinuousLinAlgEquiv' hP).eq_meanErgodicProj_and_eq_deviation_iff
    (isPowerBounded_toContinuousLinAlgEquiv' hP).ker_sup_range_eq_top

/-- **All solutions of the evaluation equations** [P, Theorem 8.2.6]. For a stochastic matrix
`P` and a reward vector `r`, the pairs `(g, h)` with `(1 - P) g = 0` and `g + (1 - P) h = r` are
those with `g = P* r` and `h = D r + P* h`: the gain is determined, and the bias up to the vector
`P* h`, which is fixed by `P`. -/
theorem eq_limitingMatrix_mulVec_and_eq_deviationMatrix_mulVec_add_iff {g h r : S → ℝ} :
    g = P.limitingMatrix *ᵥ r ∧ h = P.deviationMatrix *ᵥ r + P.limitingMatrix *ᵥ h ↔
      (1 - P) *ᵥ g = 0 ∧ g + (1 - P) *ᵥ h = r := by
  -- apply the normalized evaluation equations to `h - P* h`, which `1 - P` maps like `h` and
  -- `P*` maps to `0`
  have h₁ : (1 - P) *ᵥ (h - P.limitingMatrix *ᵥ h) = (1 - P) *ᵥ h := by
    rw [mulVec_sub, mulVec_mulVec, sub_mul, one_mul, mul_limitingMatrix hP, sub_self,
      zero_mulVec, sub_zero]
  have h₂ : P.limitingMatrix *ᵥ (h - P.limitingMatrix *ᵥ h) = 0 := by
    rw [mulVec_sub, mulVec_mulVec, limitingMatrix_mul_self hP, sub_self]
  have := eq_limitingMatrix_mulVec_and_eq_deviationMatrix_mulVec_iff hP (g := g)
    (h := h - P.limitingMatrix *ᵥ h) (r := r)
  rwa [h₁, h₂, sub_eq_iff_eq_add, eq_self_iff_true, and_true] at this

/-- **Laurent expansion of the resolvent** [P, Theorem 8.2.3]. For `0 < γ < 1` and
`u = (1 - γ) / γ` with `u ‖D‖ < 1`, where `‖D‖` is the operator norm of the action of `D` on
`S → ℝ` for the sup norm, `(1 - γ P)⁻¹ = (1 + u) (u⁻¹ P* + ∑ₙ (-u) ^ n D ^ (n + 1))`. The series
converges (`Matrix.summable_neg_pow_smul_pow_succ`). -/
theorem inv_one_sub_smul_eq_laurent {γ u : ℝ} (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (hu : u = (1 - γ) / γ) (hD : u * ‖toContinuousLinAlgEquiv' ℝ P.deviationMatrix‖ < 1) :
    (1 - γ • P)⁻¹ = (1 + u) • (u⁻¹ • P.limitingMatrix +
      ∑' n : ℕ, (-u) ^ n • P.deviationMatrix ^ (n + 1)) :=
  (toContinuousLinAlgEquiv' ℝ).injective <| by
    have hT := isPowerBounded_toContinuousLinAlgEquiv' hP
    simpa only [map_smul, map_add, map_sub, map_one, map_pow, toContinuousLinAlgEquiv'_inv,
      toContinuousLinAlgEquiv'_tsum, toContinuousLinAlgEquiv'_limitingMatrix hP,
      toContinuousLinAlgEquiv'_deviationMatrix hP, RCLike.ofReal_real_eq_id, id_eq] using
      hT.ringInverse_one_sub_smul_eq_laurent hT.ker_sup_range_eq_top hγ₀ hγ₁ hu
        (by rwa [← toContinuousLinAlgEquiv'_deviationMatrix hP])

/-- `(1 - γ) (1 - γ P)⁻¹ → P*` as `γ ↑ 1` [P, Corollary 8.2.5]. -/
theorem tendsto_one_sub_smul_inv_one_sub_smul_limitingMatrix :
    Tendsto (fun γ : ℝ ↦ (1 - γ) • (1 - γ • P)⁻¹) (𝓝[<] 1) (𝓝 P.limitingMatrix) := by
  rw [← tendsto_toContinuousLinAlgEquiv'_iff, toContinuousLinAlgEquiv'_limitingMatrix hP]
  simpa only [map_smul, toContinuousLinAlgEquiv'_inv, map_sub, map_one, RCLike.ofReal_real_eq_id,
    id_eq] using
    (isPowerBounded_toContinuousLinAlgEquiv' hP).tendsto_one_sub_smul_ringInverse_one_sub_smul
      (isPowerBounded_toContinuousLinAlgEquiv' hP).ker_sup_range_eq_top

/-- `((1 - γ) (1 - γ P)⁻¹ - P*) / (1 - γ) → D` as `γ ↑ 1` [P, Corollary 8.2.4]: the resolvent
is `(1 - γ P)⁻¹ = (1 - γ)⁻¹ P* + D + o(1)`. -/
theorem tendsto_inv_smul_one_sub_smul_inv_one_sub_smul_sub_deviationMatrix :
    Tendsto (fun γ : ℝ ↦ (1 - γ)⁻¹ • ((1 - γ) • (1 - γ • P)⁻¹ - P.limitingMatrix)) (𝓝[<] 1)
      (𝓝 P.deviationMatrix) := by
  have hT := isPowerBounded_toContinuousLinAlgEquiv' hP
  rw [← tendsto_toContinuousLinAlgEquiv'_iff, toContinuousLinAlgEquiv'_deviationMatrix hP]
  simpa only [map_smul, map_sub, toContinuousLinAlgEquiv'_inv, map_one,
    toContinuousLinAlgEquiv'_limitingMatrix hP, RCLike.ofReal_real_eq_id, id_eq] using
    hT.tendsto_inv_smul_one_sub_smul_ringInverse_one_sub_smul_sub hT.ker_sup_range_eq_top

end Deviation

end Matrix
