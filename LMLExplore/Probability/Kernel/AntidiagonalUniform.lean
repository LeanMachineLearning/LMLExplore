/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.UniformOn
import LMLExplore.MeasureTheory.Measure.Singletons

/-!
# The uniform law on an antidiagonal

The kernel `ProbabilityTheory.Kernel.antidiagonalUniform : Kernel ℕ (ℕ × ℕ)` maps `s` to the
uniform law on the `s + 1` pairs `(j, k)` of natural numbers with `j + k = s`. A law on pairs
whose mass at a point depends only on the sum of the coordinates, such as the product of two
equal geometric laws, has the conditional law `Kernel.antidiagonalUniform` given the sum.

## Main definitions

* `ProbabilityTheory.Kernel.antidiagonalUniform`: the uniform law on the pairs with sum `s`.

## Main statements

* `ProbabilityTheory.Kernel.antidiagonalUniform_singleton`: the mass of a point.
* `ProbabilityTheory.Kernel.ae_add_antidiagonalUniform`: under `Kernel.antidiagonalUniform s`,
  the coordinates add up to `s`.
* `ProbabilityTheory.Kernel.antidiagonalUniform_comp_singleton`: the masses of the points under
  `Kernel.antidiagonalUniform ∘ₘ ν`.
* `ProbabilityTheory.Kernel.antidiagonalUniform_comp_map_add_of_singleton`: a law on pairs whose
  masses depend only on the sum has the conditional law `Kernel.antidiagonalUniform` given the
  sum.
* `ProbabilityTheory.Kernel.absolutelyContinuous_antidiagonalUniform_comp`: every law on pairs is
  absolutely continuous with respect to `Kernel.antidiagonalUniform ∘ₘ μ.map (x.1 + x.2)`.
-/

public section

open MeasureTheory Set Finset

open scoped ENNReal

namespace ProbabilityTheory

/-- **The uniform law on an antidiagonal**: for `s : ℕ`, the uniform law on the `s + 1` pairs
`(j, k)` of natural numbers with `j + k = s`. Its first coordinate is uniform on `{0, …, s}`. -/
noncomputable def Kernel.antidiagonalUniform : Kernel ℕ (ℕ × ℕ) :=
  Kernel.ofFunOfCountable fun s ↦ uniformOn (antidiagonal s : Set (ℕ × ℕ))

/-- The uniform law on the pairs with sum `s`. -/
@[simp]
theorem Kernel.antidiagonalUniform_apply (s : ℕ) :
    Kernel.antidiagonalUniform s = uniformOn (antidiagonal s : Set (ℕ × ℕ)) := by
  unfold Kernel.antidiagonalUniform
  rfl

/-- The uniform law on an antidiagonal is a Markov kernel. -/
instance Kernel.isMarkovKernel_antidiagonalUniform : IsMarkovKernel Kernel.antidiagonalUniform :=
  ⟨fun s ↦ by
    rw [Kernel.antidiagonalUniform_apply]
    exact isProbabilityMeasure_uniformOn (finite_toSet _) ⟨(0, s), by simp⟩⟩

/-- The mass of a point under the uniform law on the pairs with sum `s`. -/
theorem Kernel.antidiagonalUniform_singleton (s : ℕ) (x : ℕ × ℕ) :
    Kernel.antidiagonalUniform s {x} = if x.1 + x.2 = s then ((s : ℝ≥0∞) + 1)⁻¹ else 0 := by
  classical
  rw [Kernel.antidiagonalUniform_apply, ← coe_singleton, uniformOn_apply_finset,
    Nat.card_antidiagonal]
  split_ifs with hx
  · rw [Finset.inter_singleton_of_mem (mem_antidiagonal.mpr hx)]
    simp
  · rw [Finset.inter_singleton_of_notMem (by simpa using hx)]
    simp

/-- Under the uniform law on the pairs with sum `s`, the coordinates add up to `s`. -/
theorem Kernel.ae_add_antidiagonalUniform (s : ℕ) :
    ∀ᵐ x ∂Kernel.antidiagonalUniform s, x.1 + x.2 = s := by
  rw [ae_iff, Kernel.antidiagonalUniform_apply, ← uniformOn_inter_self (finite_toSet _)]
  convert measure_empty (μ := uniformOn (antidiagonal s : Set (ℕ × ℕ)))
  ext x
  simp

/-! ### Laws on pairs whose masses depend on the sum -/

section Pairs

variable {μ : Measure (ℕ × ℕ)}

/-- The mass of a point under `Kernel.antidiagonalUniform ∘ₘ ν`. -/
theorem Kernel.antidiagonalUniform_comp_singleton (ν : Measure ℕ) (x : ℕ × ℕ) :
    (Kernel.antidiagonalUniform ∘ₘ ν) {x} =
      ν {x.1 + x.2} * (((x.1 + x.2 : ℕ) : ℝ≥0∞) + 1)⁻¹ := by
  rw [Measure.bind_apply (measurableSet_singleton x) (Kernel.aemeasurable _), lintegral_countable']
  simp_rw [Kernel.antidiagonalUniform_singleton]
  rw [tsum_eq_single (x.1 + x.2) fun s hs ↦ by simp [Ne.symm hs]]
  simp [mul_comm]

/-- A law on pairs whose mass at a point depends only on the sum has the conditional law
`Kernel.antidiagonalUniform` given the sum. -/
theorem Kernel.antidiagonalUniform_comp_map_add_of_singleton {g : ℕ → ℝ≥0∞}
    (h : ∀ x, μ {x} = g (x.1 + x.2)) :
    Kernel.antidiagonalUniform ∘ₘ μ.map (fun x ↦ x.1 + x.2) = μ := by
  refine Measure.ext_iff_singleton.mpr fun x ↦ ?_
  rw [Kernel.antidiagonalUniform_comp_singleton, Measure.map_add_singleton_eq_sum_antidiagonal,
    Finset.sum_congr rfl fun y hy ↦ by rw [h y, mem_antidiagonal.mp hy], Finset.sum_const,
    Nat.card_antidiagonal, nsmul_eq_mul, h x, mul_comm _ (g _), mul_assoc]
  push_cast
  rw [ENNReal.mul_inv_cancel (by positivity) (by simp), mul_one]

/-- Every law on pairs is absolutely continuous with respect to the law with its law of the sum
and the conditional law `Kernel.antidiagonalUniform` given the sum. -/
theorem Kernel.absolutelyContinuous_antidiagonalUniform_comp (μ : Measure (ℕ × ℕ)) :
    μ ≪ Kernel.antidiagonalUniform ∘ₘ μ.map (fun x ↦ x.1 + x.2) := by
  refine Measure.AbsolutelyContinuous.mk fun t _ ht ↦ ?_
  rw [← biUnion_of_singleton t, measure_biUnion_null_iff t.to_countable] at ht ⊢
  intro x hx
  have hx' := ht x hx
  rw [Kernel.antidiagonalUniform_comp_singleton, mul_eq_zero,
    Measure.map_add_singleton_eq_sum_antidiagonal, Finset.sum_eq_zero_iff] at hx'
  exact hx'.resolve_right (by simp) x (mem_antidiagonal.mpr rfl)

end Pairs

end ProbabilityTheory
