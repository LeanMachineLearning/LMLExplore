/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import LMLExplore.LinearAlgebra.Matrix.Polynomial

/-!
# The resolvent `(1 - a • M)⁻¹` as a rational function of `a`

For a square matrix `M`, the entries of `(1 - a • M)⁻¹` are rational functions of the scalar `a`:
by Cramer's rule they are the entries of the adjugate of the polynomial matrix `1 - X • M`,
evaluated at `a`, divided by its determinant, the reversed characteristic polynomial
`M.charpolyRev`, evaluated at `a`. The denominator has degree at most the size `card n` of the
matrix and the numerators degree at most `card n - 1`.

When every row of `M` has `ℓ¹`-norm at most `1`, as for a stochastic matrix, the matrix
`1 - a • M` is strictly diagonally dominant for `‖a‖ < 1`, so the denominator does not vanish on
the open unit ball. Two such rational functions therefore agree on the whole ball or only at
finitely many points of it, and over `ℝ` one of them eventually stays strictly below the other, or
they eventually agree, as `a` increases to `1`.

For a stochastic matrix `P`, a reward vector `r` and a discount factor `γ ∈ [0, 1)`, the vector
`(1 - γ • P)⁻¹ *ᵥ r` is the discounted value `∑ₙ γⁿ Pⁿ r` of the Markov reward process, so these
results describe the dependence of discounted values on the discount factor, used to compare
stationary policies of a finite Markov decision process for all discount factors close to `1`
(Blackwell optimality) [P, Lemma 10.1.3, Theorem 10.1.4].

## Main definitions

* `Matrix.charmatrixRev M`: the polynomial matrix `1 - X • M`, whose determinant is
  `M.charpolyRev`.

## Main statements

* `Matrix.inv_one_sub_smul_apply`, `Matrix.inv_one_sub_smul_mulVec_apply`: the entries of
  `(1 - a • M)⁻¹` and of `(1 - a • M)⁻¹ *ᵥ v` as quotients of polynomials evaluated at `a`.
* `Matrix.natDegree_charpolyRev_le`, `Matrix.natDegree_adjugate_charmatrixRev_apply_le`: the
  degree bounds on the denominator and the numerators.
* `Matrix.det_one_sub_smul_ne_zero`: `1 - a • M` is nonsingular when every row of `a • M` has
  `ℓ¹`-norm less than `1`.
* `Matrix.eqOn_or_finite_setOf_inv_one_sub_smul_mulVec_apply_eq`: two such rational functions
  agree on the open unit ball or at finitely many of its points.
* `Matrix.eventually_trichotomy_inv_one_sub_smul_mulVec_apply`: over `ℝ`, as `γ` increases to
  `1`, one of the two functions is eventually strictly below the other, or they eventually agree.

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], Lemma 10.1.3
-/

public section

open Polynomial Filter Topology Set

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable {R : Type*} [CommRing R] (M : Matrix n n R)

/-- The reversed characteristic matrix `1 - X • M` of a square matrix `M`: a matrix of
polynomials of degree at most `1`, whose determinant is the reversed characteristic polynomial
`M.charpolyRev` and whose evaluation at `a` is `1 - a • M`. -/
noncomputable def charmatrixRev : Matrix n n R[X] :=
  1 - (X : R[X]) • M.map C

omit [Fintype n] in
theorem charmatrixRev_apply (i j : n) :
    M.charmatrixRev i j = (1 : Matrix n n R[X]) i j - X * C (M i j) := by
  simp [charmatrixRev]

@[simp]
theorem det_charmatrixRev : M.charmatrixRev.det = M.charpolyRev := (rfl)

omit [Fintype n] in
@[simp]
theorem map_eval_charmatrixRev (a : R) : M.charmatrixRev.map (eval a) = 1 - a • M := by
  ext i j
  rcases eq_or_ne i j with rfl | hij <;> simp [charmatrixRev_apply, *] <;> ring

/-- The reversed characteristic polynomial evaluated at `a` is the determinant of `1 - a • M`. -/
theorem eval_charpolyRev_eq_det (a : R) : M.charpolyRev.eval a = (1 - a • M).det := by
  rw [← det_charmatrixRev, ← coe_evalRingHom, RingHom.map_det, RingHom.mapMatrix_apply,
    coe_evalRingHom, map_eval_charmatrixRev]

/-- The adjugate of `1 - a • M` is the adjugate of the polynomial matrix `1 - X • M` evaluated
at `a`. -/
theorem adjugate_one_sub_smul (a : R) :
    (1 - a • M).adjugate = M.charmatrixRev.adjugate.map (eval a) := by
  rw [← map_eval_charmatrixRev, ← coe_evalRingHom, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, RingHom.map_adjugate]

omit [Fintype n] in
/-- The entries of `1 - X • M` have degree at most `1`. -/
theorem natDegree_charmatrixRev_apply_le (i j : n) : (M.charmatrixRev i j).natDegree ≤ 1 := by
  rw [charmatrixRev_apply, Matrix.one_apply]
  split_ifs <;> compute_degree

/-- The reversed characteristic polynomial of an `n × n` matrix has degree at most `card n`. -/
theorem natDegree_charpolyRev_le : M.charpolyRev.natDegree ≤ Fintype.card n := by
  simpa [← det_charmatrixRev] using natDegree_det_le_sum M.natDegree_charmatrixRev_apply_le

/-- The entries of the adjugate of `1 - X • M` have degree at most `card n - 1`. -/
theorem natDegree_adjugate_charmatrixRev_apply_le (i j : n) :
    (M.charmatrixRev.adjugate i j).natDegree ≤ Fintype.card n - 1 := by
  rw [adjugate_apply]
  refine (natDegree_det_le_sum (d := fun k ↦ if k = j then 0 else 1) fun k l ↦ ?_).trans ?_
  · rcases eq_or_ne k j with rfl | hk
    · rw [updateRow_self, Pi.single_apply]
      split_ifs <;> simp
    · simpa [updateRow_ne hk, hk] using M.natDegree_charmatrixRev_apply_le k l
  · simp [Finset.sum_ite, Finset.filter_ne']

/-- The coordinates of `adjugate (1 - X • M) *ᵥ v` have degree at most `card n - 1`. -/
theorem natDegree_adjugate_charmatrixRev_mulVec_apply_le (v : n → R) (i : n) :
    ((M.charmatrixRev.adjugate *ᵥ fun j ↦ C (v j)) i).natDegree ≤ Fintype.card n - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun j _ ↦
    (natDegree_mul_C_le _ _).trans (M.natDegree_adjugate_charmatrixRev_apply_le i j)

/-- Evaluating `adjugate (1 - X • M) *ᵥ v` at `a` gives `adjugate (1 - a • M) *ᵥ v`. -/
theorem eval_adjugate_charmatrixRev_mulVec_apply (v : n → R) (i : n) (a : R) :
    ((M.charmatrixRev.adjugate *ᵥ fun j ↦ C (v j)) i).eval a = ((1 - a • M).adjugate *ᵥ v) i := by
  simp [mulVec, dotProduct, eval_finsetSum, adjugate_one_sub_smul]

end CommRing

section Field

variable {K : Type*} [Field K] (M : Matrix n n K)

/-- **Cramer's rule for the resolvent**: every entry of `(1 - a • M)⁻¹` is a polynomial of degree
at most `card n - 1` divided by `M.charpolyRev`, both evaluated at `a`. Both sides vanish when
`1 - a • M` is singular. -/
theorem inv_one_sub_smul_apply (a : K) (i j : n) :
    (1 - a • M)⁻¹ i j = (M.charmatrixRev.adjugate i j).eval a / M.charpolyRev.eval a := by
  rw [inv_def, Matrix.smul_apply, adjugate_one_sub_smul, map_apply, eval_charpolyRev_eq_det,
    Ring.inverse_eq_inv', smul_eq_mul, div_eq_inv_mul]

/-- Every coordinate of `(1 - a • M)⁻¹ *ᵥ v` is a polynomial of degree at most `card n - 1`
divided by `M.charpolyRev`, both evaluated at `a`. -/
theorem inv_one_sub_smul_mulVec_apply (a : K) (v : n → K) (i : n) :
    ((1 - a • M)⁻¹ *ᵥ v) i =
      ((M.charmatrixRev.adjugate *ᵥ fun j ↦ C (v j)) i).eval a / M.charpolyRev.eval a := by
  rw [eval_adjugate_charmatrixRev_mulVec_apply, inv_def, smul_mulVec, Pi.smul_apply,
    eval_charpolyRev_eq_det, Ring.inverse_eq_inv', smul_eq_mul, div_eq_inv_mul]

end Field

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜] {M : Matrix n n 𝕜}

/-- If every row of `a • M` has `ℓ¹`-norm less than `1`, for instance if every row of `M` has
`ℓ¹`-norm at most `1` and `‖a‖ < 1`, then `1 - a • M` is strictly diagonally dominant, hence
nonsingular. -/
theorem det_one_sub_smul_ne_zero {a : 𝕜} (h : ∀ i, ‖a‖ * ∑ j, ‖M i j‖ < 1) :
    (1 - a • M).det ≠ 0 := by
  refine det_ne_zero_of_sum_row_lt_diag fun i ↦ ?_
  have hoff : ∑ j ∈ Finset.univ.erase i, ‖(1 - a • M) i j‖ =
      ‖a‖ * (∑ j, ‖M i j‖ - ‖M i i‖) := by
    rw [← Finset.sum_erase_eq_sub (Finset.mem_univ i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Matrix.sub_apply, Matrix.one_apply_ne (Finset.ne_of_mem_erase hj).symm, zero_sub,
      norm_neg, Matrix.smul_apply, smul_eq_mul, norm_mul]
  have hdiag : 1 - ‖a‖ * ‖M i i‖ ≤ ‖(1 - a • M) i i‖ := by
    rw [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, ← norm_mul]
    simpa using norm_sub_norm_le (1 : 𝕜) (a * M i i)
  rw [hoff]
  rw [mul_sub]
  linarith [h i]

/-- If every row of `a • M` has `ℓ¹`-norm less than `1`, then `1 - a • M` is invertible. -/
theorem isUnit_one_sub_smul {a : 𝕜} (h : ∀ i, ‖a‖ * ∑ j, ‖M i j‖ < 1) : IsUnit (1 - a • M) :=
  (isUnit_iff_isUnit_det _).2 (det_one_sub_smul_ne_zero h).isUnit

/-- The denominator `M.charpolyRev` does not vanish at `a` when every row of `a • M` has
`ℓ¹`-norm less than `1`. -/
theorem eval_charpolyRev_ne_zero {a : 𝕜} (h : ∀ i, ‖a‖ * ∑ j, ‖M i j‖ < 1) :
    M.charpolyRev.eval a ≠ 0 := by
  rw [eval_charpolyRev_eq_det]
  exact det_one_sub_smul_ne_zero h

omit [DecidableEq n] in
private theorem mul_sum_norm_lt_one (hM : ∀ i, ∑ j, ‖M i j‖ ≤ 1) {a : 𝕜} (ha : ‖a‖ < 1) (i : n) :
    ‖a‖ * ∑ j, ‖M i j‖ < 1 :=
  (mul_le_of_le_one_right (norm_nonneg a) (hM i)).trans_lt ha

/-- The coordinates of `(1 - a • M)⁻¹ *ᵥ v` are continuous in `a` on the open unit ball when
every row of `M` has `ℓ¹`-norm at most `1`. -/
theorem continuousOn_inv_one_sub_smul_mulVec_apply (hM : ∀ i, ∑ j, ‖M i j‖ ≤ 1) (v : n → 𝕜)
    (i : n) : ContinuousOn (fun a : 𝕜 ↦ ((1 - a • M)⁻¹ *ᵥ v) i) (Metric.ball 0 1) := by
  have hc : ContinuousOn (fun a : 𝕜 ↦ ((M.charmatrixRev.adjugate *ᵥ fun j ↦ C (v j)) i).eval a /
      M.charpolyRev.eval a) (Metric.ball 0 1) :=
    (Polynomial.continuousOn _).div (Polynomial.continuousOn _) fun a ha ↦
      eval_charpolyRev_ne_zero (mul_sum_norm_lt_one hM (mem_ball_zero_iff.1 ha))
  exact hc.congr fun a _ ↦ inv_one_sub_smul_mulVec_apply M a v i

/-- Two rational functions `a ↦ ((1 - a • M)⁻¹ *ᵥ v) i` and `a ↦ ((1 - a • N)⁻¹ *ᵥ w) i`, for
matrices whose rows have `ℓ¹`-norm at most `1`, agree on the whole open unit ball or only at
finitely many of its points. -/
theorem eqOn_or_finite_setOf_inv_one_sub_smul_mulVec_apply_eq {N : Matrix n n 𝕜}
    (hM : ∀ i, ∑ j, ‖M i j‖ ≤ 1) (hN : ∀ i, ∑ j, ‖N i j‖ ≤ 1) (v w : n → 𝕜) (i : n) :
    EqOn (fun a : 𝕜 ↦ ((1 - a • M)⁻¹ *ᵥ v) i) (fun a ↦ ((1 - a • N)⁻¹ *ᵥ w) i)
        (Metric.ball 0 1) ∨
      {a ∈ Metric.ball (0 : 𝕜) 1 | ((1 - a • M)⁻¹ *ᵥ v) i = ((1 - a • N)⁻¹ *ᵥ w) i}.Finite := by
  set p := (M.charmatrixRev.adjugate *ᵥ fun j ↦ C (v j)) i
  set q := (N.charmatrixRev.adjugate *ᵥ fun j ↦ C (w j)) i
  have key : ∀ a ∈ Metric.ball (0 : 𝕜) 1, ((1 - a • M)⁻¹ *ᵥ v) i = ((1 - a • N)⁻¹ *ᵥ w) i ↔
      (p * N.charpolyRev - q * M.charpolyRev).IsRoot a := by
    intro a ha
    rw [mem_ball_zero_iff] at ha
    rw [inv_one_sub_smul_mulVec_apply, inv_one_sub_smul_mulVec_apply,
      div_eq_div_iff (eval_charpolyRev_ne_zero (mul_sum_norm_lt_one hM ha))
        (eval_charpolyRev_ne_zero (mul_sum_norm_lt_one hN ha)), IsRoot,
      eval_sub, eval_mul, eval_mul, sub_eq_zero]
  by_cases hD : p * N.charpolyRev - q * M.charpolyRev = 0
  · exact Or.inl fun a ha ↦ (key a ha).2 (by simp [hD])
  · exact Or.inr <| (finite_setOfPred_isRoot hD).subset fun a ha ↦ (key a ha.1).1 ha.2

end NormedField

/-- As `γ` increases to `1`, of two rational functions `γ ↦ ((1 - γ • M)⁻¹ *ᵥ v) i` and
`γ ↦ ((1 - γ • N)⁻¹ *ᵥ w) i`, for real matrices whose rows have `ℓ¹`-norm at most `1`, one is
eventually strictly below the other, or they eventually agree. -/
theorem eventually_trichotomy_inv_one_sub_smul_mulVec_apply {M N : Matrix n n ℝ}
    (hM : ∀ i, ∑ j, ‖M i j‖ ≤ 1) (hN : ∀ i, ∑ j, ‖N i j‖ ≤ 1) (v w : n → ℝ) (i : n) :
    (∀ᶠ γ : ℝ in 𝓝[<] 1, ((1 - γ • M)⁻¹ *ᵥ v) i < ((1 - γ • N)⁻¹ *ᵥ w) i) ∨
      (∀ᶠ γ : ℝ in 𝓝[<] 1, ((1 - γ • M)⁻¹ *ᵥ v) i = ((1 - γ • N)⁻¹ *ᵥ w) i) ∨
      (∀ᶠ γ : ℝ in 𝓝[<] 1, ((1 - γ • N)⁻¹ *ᵥ w) i < ((1 - γ • M)⁻¹ *ᵥ v) i) := by
  set f := fun γ : ℝ ↦ ((1 - γ • M)⁻¹ *ᵥ v) i
  set g := fun γ : ℝ ↦ ((1 - γ • N)⁻¹ *ᵥ w) i
  have hball : Metric.ball (0 : ℝ) 1 = Ioo (-1) 1 := by
    rw [Real.ball_eq_Ioo, zero_sub, zero_add]
  have h1 : (-1 : ℝ) < 1 := by norm_num
  rcases eqOn_or_finite_setOf_inv_one_sub_smul_mulVec_apply_eq hM hN v w i with h | h
  · refine Or.inr (Or.inl ?_)
    filter_upwards [Ioo_mem_nhdsLT h1] with γ hγ
    exact h (hball ▸ hγ)
  -- Off the finite set of crossings, `f ≠ g` on an interval `(l, 1)`, where both are continuous.
  obtain ⟨l, hl, hsub⟩ : ∃ l ∈ Iio (1 : ℝ), Ioo l 1 ⊆ Ioo (-1) 1 ∩
      {a | a ∉ {a ∈ Metric.ball (0 : ℝ) 1 | f a = g a}} := by
    refine mem_nhdsLT_iff_exists_Ioo_subset.1 (inter_mem (Ioo_mem_nhdsLT h1) ?_)
    refine mem_nhdsWithin_of_mem_nhds (h.isClosed.isOpen_compl.mem_nhds fun h1 ↦ ?_)
    simp [Real.norm_eq_abs] at h1
  have hne : ∀ γ ∈ Ioo l 1, f γ ≠ g γ := fun γ hγ hfg ↦
    (hsub hγ).2 ⟨hball ▸ (hsub hγ).1, hfg⟩
  have hcont : ∀ {P : Matrix n n ℝ} (_ : ∀ i, ∑ j, ‖P i j‖ ≤ 1) (u : n → ℝ),
      ContinuousOn (fun γ : ℝ ↦ ((1 - γ • P)⁻¹ *ᵥ u) i) (Ioo l 1) := fun hP u ↦
    (continuousOn_inv_one_sub_smul_mulVec_apply hP u i).mono
      (hball ▸ fun γ hγ ↦ (hsub hγ).1)
  by_cases hfg : ∀ γ ∈ Ioo l 1, f γ ≤ g γ
  · refine Or.inl ?_
    filter_upwards [Ioo_mem_nhdsLT hl] with γ hγ
    exact (hfg γ hγ).lt_of_ne (hne γ hγ)
  by_cases hgf : ∀ γ ∈ Ioo l 1, g γ ≤ f γ
  · refine Or.inr (Or.inr ?_)
    filter_upwards [Ioo_mem_nhdsLT hl] with γ hγ
    exact (hgf γ hγ).lt_of_ne (hne γ hγ).symm
  -- Otherwise `f - g` changes sign on `(l, 1)`, so it vanishes there.
  push Not at hfg hgf
  obtain ⟨a, ha, hfa⟩ := hgf
  obtain ⟨b, hb, hgb⟩ := hfg
  obtain ⟨x, hx, hfx⟩ := isPreconnected_Ioo.intermediate_value₂ ha hb (hcont hM v) (hcont hN w)
    hfa.le hgb.le
  exact absurd hfx (hne x hx)

end Matrix
