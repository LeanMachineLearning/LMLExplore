/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditional expectations of deterministic combinations

Let `m` be a sub-σ-algebra and `N i`, for `i` in a finite type, real functions. For deterministic
weights `c i`, the conditional expectation of `∑ i, c i N i` given `m` is `∑ i, c i E[N i | m]`,
and by the Cauchy–Schwarz inequality the conditional second moment of `∑ i, v i N i` is at most
`(∑ i, |v i|) ∑ i, |v i| E[N i ^ 2 | m]`. This is how the conditional variance of a fixed linear
combination of noises, such as a row of a matrix applied to a vector of martingale differences,
is controlled by the conditional variances of the noises.

## Main statements

* `LMLExplore.condExp_sum_const_mul`: `E[∑ i, c i N i | m] = ∑ i, c i E[N i | m]` almost
  everywhere.
* `LMLExplore.condExp_sq_sum_mul_le`: `E[(∑ i, v i N i) ^ 2 | m] ≤
  (∑ i, |v i|) ∑ i, |v i| E[N i ^ 2 | m]` almost everywhere.
-/

public section

open MeasureTheory Finset

namespace LMLExplore

variable {Ω ι : Type*} [Fintype ι] {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {N : ι → Ω → ℝ}

/-- The conditional expectation of a deterministic combination `∑ i, c i N i` of integrable
functions is the combination `∑ i, c i E[N i | m]` of their conditional expectations. -/
theorem condExp_sum_const_mul (c : ι → ℝ) (hN : ∀ i, Integrable (N i) μ) :
    μ[fun ω ↦ ∑ i, c i * N i ω | m] =ᵐ[μ] fun ω ↦ ∑ i, c i * μ[N i | m] ω := by
  have hfun : (fun ω ↦ ∑ i, c i * N i ω) = ∑ i, fun ω ↦ c i * N i ω := by
    funext ω
    rw [Finset.sum_apply]
  rw [hfun]
  filter_upwards [condExp_finsetSum (s := univ) (fun i _ ↦ (hN i).const_mul (c i)) (μ := μ) m,
    ae_all_iff.2 fun i ↦ condExp_smul (μ := μ) (c i) (N i) m] with ω h₁ h₂
  rw [h₁, Finset.sum_apply]
  exact sum_congr rfl fun i _ ↦ h₂ i

/-- The conditional second moment of a deterministic combination `∑ i, v i N i` of square
integrable functions is at most `(∑ i, |v i|) ∑ i, |v i| E[N i ^ 2 | m]`, by the Cauchy–Schwarz
inequality. -/
theorem condExp_sq_sum_mul_le (v : ι → ℝ) (hN : ∀ i, Integrable (fun ω ↦ N i ω ^ 2) μ)
    (h : Integrable (fun ω ↦ (∑ i, v i * N i ω) ^ 2) μ) :
    μ[fun ω ↦ (∑ i, v i * N i ω) ^ 2 | m] ≤ᵐ[μ]
      fun ω ↦ (∑ i, |v i|) * ∑ i, |v i| * μ[fun ω ↦ N i ω ^ 2 | m] ω := by
  have hle : (fun ω ↦ (∑ i, v i * N i ω) ^ 2) ≤ᵐ[μ]
      fun ω ↦ ∑ i, ((∑ i, |v i|) * |v i|) * N i ω ^ 2 := .of_forall fun ω ↦ by
    refine (sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ ↦ abs_nonneg (v i))
      (fun i _ ↦ mul_nonneg (abs_nonneg (v i)) (sq_nonneg (N i ω)))
      (fun i _ ↦ le_of_eq (by rw [mul_pow, ← sq_abs (v i)]; ring))).trans_eq ?_
    rw [mul_sum]
    exact sum_congr rfl fun i _ ↦ by ring
  have hint : Integrable (fun ω ↦ ∑ i, ((∑ i, |v i|) * |v i|) * N i ω ^ 2) μ :=
    integrable_finsetSum _ fun i _ ↦ (hN i).const_mul _
  filter_upwards [condExp_mono h hint hle, condExp_sum_const_mul (m := m) _ hN] with ω h₁ h₂
  refine (h₁.trans_eq h₂).trans_eq ?_
  rw [mul_sum]
  exact sum_congr rfl fun i _ ↦ by rw [mul_assoc]

end LMLExplore
