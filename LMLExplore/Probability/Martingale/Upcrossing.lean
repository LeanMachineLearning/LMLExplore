/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Martingale.Upcrossing

/-!
# Doob's upcrossing inequality with the initial term

For a real submartingale `f`, a time `N` and real numbers `a`, `b`, the number `U_N` of upcrossings
of `[a, b]` that `f` completes before `N` satisfies Doob's inequality

`(b - a) 𝔼[U_N] ≤ 𝔼[(f N - a)⁺] - 𝔼[(f 0 - a)⁺]`.

Mathlib's `MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part` drops
the last term. Keeping it matters when the bound must not depend on the location of the process:
for a martingale started at a value of mean `m`, the right-hand side is at most
`𝔼[(f N - a)⁺] - (m - a)⁺`, which stays bounded as `a` and `b` move away from `m`.

The number of upcrossings completed before `N` is a function of the process up to time `N`, so
the upcrossing counts of an adapted process form an adapted process.

## Main statements

* `MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_posPart_sub`: Doob's
  upcrossing inequality with the initial term.
* `MeasureTheory.StronglyAdapted.adapted_upcrossingsBefore`: the upcrossing counts of an adapted
  process are adapted.
-/

public section

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {f : ℕ → Ω → ℝ} {a b : ℝ}

/-- The number of upcrossings of `[a, b]` that an adapted process completes before time `N` is
measurable at time `N`: the upcrossing counts form an adapted process. -/
theorem StronglyAdapted.adapted_upcrossingsBefore (hf : StronglyAdapted ℱ f) (hab : a < b) :
    Adapted ℱ fun N ↦ upcrossingsBefore a b f N := by
  intro N
  dsimp only
  have : upcrossingsBefore a b f N = fun ω ↦
      ∑ i ∈ Finset.Ico 1 (N + 1), {n | upperCrossingTime a b f N n ω < N}.indicator 1 i := by
    ext ω
    exact upcrossingsBefore_eq_sum hab
  rw [this]
  refine Finset.measurable_fun_sum _ fun i _ ↦ Measurable.indicator
    (s := {ω | upperCrossingTime a b f N i ω < N}) measurable_const ?_
  simpa only [ENat.some_eq_natCast, Nat.cast_lt] using!
    hf.isStoppingTime_upperCrossingTime.measurableSet_lt_of_pred N

/-- **Doob's upcrossing inequality** with the initial term: for a submartingale `f`,
`(b - a) 𝔼[U_N] ≤ 𝔼[(f N - a)⁺] - 𝔼[(f 0 - a)⁺]`, where `U_N` is the number of upcrossings of
`[a, b]` completed before `N`. -/
theorem Submartingale.mul_integral_upcrossingsBefore_le_integral_posPart_sub [IsFiniteMeasure μ]
    (a b : ℝ) (hf : Submartingale f ℱ μ) (N : ℕ) :
    (b - a) * ∫ ω, (upcrossingsBefore a b f N ω : ℝ) ∂μ ≤
      ∫ ω, (f N ω - a)⁺ ∂μ - ∫ ω, (f 0 ω - a)⁺ ∂μ := by
  set g : ℕ → Ω → ℝ := fun n ω ↦ (f n ω - a)⁺ with hg_def
  have hg : Submartingale g ℱ μ := (hf.sub_martingale (martingale_const _ _ a)).pos
  rcases le_or_gt b a with hba | hab
  · -- the left-hand side is nonpositive and the right-hand side is nonnegative
    refine (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hba)
      (integral_nonneg fun ω ↦ Nat.cast_nonneg _)).trans ?_
    exact sub_nonneg.2 (by simpa using hg.setIntegral_le (Nat.zero_le N) MeasurableSet.univ)
  have hab' : (0 : ℝ) < b - a := sub_pos.2 hab
  calc (b - a) * ∫ ω, (upcrossingsBefore a b f N ω : ℝ) ∂μ
      = (b - a) * ∫ ω, (upcrossingsBefore 0 (b - a) g N ω : ℝ) ∂μ := by
        simp_rw [hg_def, upcrossingsBefore_pos_eq hab]
    _ ≤ ∫ ω, (∑ k ∈ Finset.range N,
          upcrossingStrat 0 (b - a) g N k * (g (k + 1) - g k)) ω ∂μ := by
        rw [← integral_const_mul]
        refine integral_mono_of_nonneg ?_
          ((hg.sum_upcrossingStrat_mul 0 (b - a) N).integrable N) ?_
        · exact .of_forall fun ω ↦ mul_nonneg hab'.le (Nat.cast_nonneg _)
        · filter_upwards with ω
          simpa [sub_zero] using mul_upcrossingsBefore_le (f := g) (posPart_nonneg _) hab'
    _ ≤ ∫ ω, g N ω ∂μ - ∫ ω, g 0 ω ∂μ := hg.sum_mul_upcrossingStrat_le

end MeasureTheory
