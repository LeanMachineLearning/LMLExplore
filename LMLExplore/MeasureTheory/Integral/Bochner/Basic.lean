/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Expectations of finite suprema, of finite sums and of shifts by constants

## Main statements

* `MeasureTheory.Integrable.iSup`, `MeasureTheory.iSup_integral_le`: the pointwise supremum of
  finitely many integrable real functions is integrable, and its integral is at least the
  supremum of their integrals. Regrets against the best of finitely many comparators, whose
  expectation is compared with the best expected regret, use them.
* `MeasureTheory.integral_sub_const`, `MeasureTheory.integral_const_sub`: under a probability
  measure, the integral of `f - c` is `∫ f - c`, and that of `c - f` is `c - ∫ f`.
* `MeasureTheory.integral_const_sub_sum`: under a probability measure, the expectation of
  `c - ∑ i ∈ s, g i` is `c - ∑ i ∈ s, ∫ g i ∂P`.
* `MeasureTheory.integral_sum_le_add_mul_of_ae_le`: under a probability measure, an almost sure
  bound `∑ i ∈ s, Z i ≤ B + c ∑ i ∈ s, V i` with `c ≥ 0` gives `∫ ∑ i ∈ s, Z i ∂P ≤ B + c C` when
  the expectations of the `V i` sum to at most `C`.
-/

public section

open Finset

namespace MeasureTheory

section Supremum

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Finite ι] {f : ι → Ω → ℝ}

/-- The pointwise supremum of finitely many integrable real functions is integrable. -/
lemma Integrable.iSup (hf : ∀ i, Integrable (f i) μ) : Integrable (fun ω ↦ ⨆ i, f i ω) μ := by
  have := Fintype.ofFinite ι
  refine Integrable.mono' (integrable_finsetSum univ fun i _ ↦ (hf i).abs)
    (AEMeasurable.iSup fun i ↦ (hf i).aemeasurable).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ f i ω)
  rw [← hj, Real.norm_eq_abs]
  exact single_le_sum (f := fun i ↦ |f i ω|) (fun i _ ↦ abs_nonneg _) (mem_univ j)

/-- The supremum of the integrals of finitely many integrable real functions is at most the
integral of their pointwise supremum. -/
lemma iSup_integral_le (hf : ∀ i, Integrable (f i) μ) :
    ⨆ i, ∫ ω, f i ω ∂μ ≤ ∫ ω, ⨆ i, f i ω ∂μ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  exact ciSup_le fun i ↦ integral_mono (hf i) (Integrable.iSup hf) fun ω ↦
    le_ciSup (Set.finite_range fun i ↦ f i ω).bddAbove i

end Supremum

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {s : Finset ι}

section Const

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : Ω → E}

/-- Under a probability measure, the integral of an integrable function minus a constant is the
integral of the function minus the constant. -/
lemma integral_sub_const (hf : Integrable f P) (c : E) :
    ∫ ω, (f ω - c) ∂P = ∫ ω, f ω ∂P - c := by
  rw [integral_sub hf (integrable_const c), integral_const, probReal_univ, one_smul]

/-- Under a probability measure, the integral of a constant minus an integrable function is the
constant minus the integral of the function. -/
lemma integral_const_sub (c : E) (hf : Integrable f P) :
    ∫ ω, (c - f ω) ∂P = c - ∫ ω, f ω ∂P := by
  rw [integral_sub (integrable_const c) hf, integral_const, probReal_univ, one_smul]

end Const

/-- Under a probability measure, the expectation of a constant minus a finite sum of integrable
real functions is the constant minus the sum of their expectations. -/
lemma integral_const_sub_sum (c : ℝ) {g : ι → Ω → ℝ} (hg : ∀ i ∈ s, Integrable (g i) P) :
    ∫ ω, (c - ∑ i ∈ s, g i ω) ∂P = c - ∑ i ∈ s, ∫ ω, g i ω ∂P := by
  rw [integral_const_sub c (integrable_finsetSum _ hg), integral_finsetSum _ hg]

/-- If almost surely `∑ i ∈ s, Z i ≤ B + c ∑ i ∈ s, V i` with `c ≥ 0`, where the `Z i` and `V i`
are integrable and the expectations of the `V i` sum to at most `C`, then the expectation of
`∑ i ∈ s, Z i` is at most `B + c C`. The analyses of Exp3 and Exp4 use it to turn pathwise bounds
into bounds on the expected estimated regret. -/
lemma integral_sum_le_add_mul_of_ae_le {Z V : ι → Ω → ℝ} {B c C : ℝ} (hc : 0 ≤ c)
    (hZ : ∀ i ∈ s, Integrable (Z i) P) (hV : ∀ i ∈ s, Integrable (V i) P)
    (hVC : ∑ i ∈ s, ∫ ω, V i ω ∂P ≤ C)
    (hZV : ∀ᵐ ω ∂P, ∑ i ∈ s, Z i ω ≤ B + c * ∑ i ∈ s, V i ω) :
    ∫ ω, ∑ i ∈ s, Z i ω ∂P ≤ B + c * C := by
  calc ∫ ω, ∑ i ∈ s, Z i ω ∂P
  _ ≤ ∫ ω, B + c * ∑ i ∈ s, V i ω ∂P := by
      refine integral_mono_ae (integrable_finsetSum _ hZ)
        ((integrable_const _).add ((integrable_finsetSum _ hV).const_mul _)) ?_
      filter_upwards [hZV] with ω hω
      exact hω
  _ = B + c * ∑ i ∈ s, ∫ ω, V i ω ∂P := by
      rw [integral_add (integrable_const _) ((integrable_finsetSum _ hV).const_mul _),
        integral_const_mul, integral_finsetSum _ hV, integral_const, probReal_univ, one_smul]
  _ ≤ B + c * C := by gcongr

end MeasureTheory
