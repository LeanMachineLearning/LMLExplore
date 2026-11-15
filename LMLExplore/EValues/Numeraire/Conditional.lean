/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Numeraire

/-!
# Numeraires of nulls with a common conditional law given a statistic

Let `T : Ω → 𝓨` be a statistic and `κ : Kernel 𝓨 Ω` a kernel such that `κ y` is carried by the
fiber `T ⁻¹' {y}`. Suppose that `κ` is the conditional law given `T` of every member `P` of a
null `S`, in the sense that `P = κ ∘ₘ P.map T`. For an alternative `Q`, the measure
`κ ∘ₘ Q.map T` has the law of `T` under `Q` and the conditional law `κ` of the null given `T`.

The likelihood ratio of `Q` to `κ ∘ₘ Q.map T` integrates to one against `κ y` for `Q.map T`-almost
every `y`: its conditional expectation given `T` is one. So it is an e-variable for `S`, with
expectation exactly the mass `P univ` (one for probability measures) under every member `P` of `S`
such that the law of `T` under `P` is absolutely continuous with respect to its law under `Q`. This
is the conditional e-variable of [HGLLA24]. When moreover `κ ∘ₘ Q.map T` belongs to the effective
null of `S` (for example when it is a mixture of members of `S`, by
`ProbabilityTheory.comp_mem_effectiveSet`), this likelihood ratio is the numeraire of `S` under
`Q` by the criterion of [LRR25, Theorem 4.1] (`ProbabilityTheory.isNumeraire_of_ae_eq_rnDeriv`),
and `κ ∘ₘ Q.map T` is the reverse information projection of `Q` on `S` when it is equivalent to
`Q` (`ProbabilityTheory.ripr_eq_of_isEVar_rnDeriv`).

## Main statements

* `ProbabilityTheory.ae_lintegral_rnDeriv_comp_map_eq_one`: the likelihood ratio of `Q` to
  `κ ∘ₘ Q.map T` has conditional expectation one given `T`.
* `ProbabilityTheory.lintegral_rnDeriv_comp_map`, `ProbabilityTheory.isEVar_rnDeriv_comp_map`: it
  is an exact e-variable for every null of which `κ` is the conditional law given `T`.

## References

* [HGLLA24] Y. Hao, P. Grünwald, T. Lardy, L. Long and R. Adams, *E-values for k-sample tests
  with exponential families*, arXiv:2303.00471.
* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4, Theorem 4.1.
-/

public section

open MeasureTheory Set

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓨 : MeasurableSpace 𝓨} {T : Ω → 𝓨}
  {κ : Kernel 𝓨 Ω} {S : Set (Measure Ω)} {Q P : Measure Ω}

/-- **The conditional expectation of the likelihood ratio given the statistic is one.** If `κ y`
is carried by the fiber `T ⁻¹' {y}` for `Q.map T`-almost every `y` and the finite measure `Q` is
absolutely continuous with respect to `κ ∘ₘ Q.map T`, the likelihood ratio of `Q` to
`κ ∘ₘ Q.map T` has integral one against `κ y` for `Q.map T`-almost every `y`. -/
theorem ae_lintegral_rnDeriv_comp_map_eq_one [IsFiniteMeasure Q] [IsFiniteKernel κ]
    (hT : Measurable T) (hκ : ∀ᵐ y ∂Q.map T, ∀ᵐ x ∂κ y, T x = y) (hQ : Q ≪ κ ∘ₘ Q.map T) :
    ∀ᵐ y ∂Q.map T, ∫⁻ x, Q.rnDeriv (κ ∘ₘ Q.map T) x ∂κ y = 1 := by
  set ν := Q.map T
  set X := Q.rnDeriv (κ ∘ₘ ν)
  have hX : Measurable X := Measure.measurable_rnDeriv _ _
  have hφ : Measurable fun y ↦ ∫⁻ x, X x ∂κ y := hX.lintegral_kernel
  refine (withDensity_eq_iff_of_sigmaFinite (g := 1) hφ.aemeasurable aemeasurable_one).mp ?_
  rw [withDensity_one]
  ext A hA
  rw [withDensity_apply _ hA, Measure.map_apply hT hA, ← lintegral_indicator hA]
  calc ∫⁻ y, A.indicator (fun y ↦ ∫⁻ x, X x ∂κ y) y ∂ν
  _ = ∫⁻ y, ∫⁻ x, (T ⁻¹' A).indicator X x ∂κ y ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [hκ] with y hκ
    by_cases hy : y ∈ A
    · rw [indicator_of_mem hy]
      refine lintegral_congr_ae ?_
      filter_upwards [hκ] with x hx
      rw [indicator_of_mem (show x ∈ T ⁻¹' A by simpa [hx])]
    · rw [indicator_of_notMem hy, lintegral_congr_ae (g := 0), Pi.zero_def, lintegral_zero]
      filter_upwards [hκ] with x hx
      rw [indicator_of_notMem (show x ∉ T ⁻¹' A by simpa [hx]), Pi.zero_apply]
  _ = ∫⁻ x, (T ⁻¹' A).indicator X x ∂(κ ∘ₘ ν) :=
    (Measure.lintegral_bind κ.aemeasurable (hX.indicator (hT hA)).aemeasurable).symm
  _ = Q (T ⁻¹' A) := by
    rw [lintegral_indicator (hT hA), ← withDensity_apply _ (hT hA),
      Measure.withDensity_rnDeriv_eq _ _ hQ]

/-- **The likelihood ratio to `κ ∘ₘ Q.map T` has expectation one under the null.** Under a
measure `P` whose conditional law given `T` is `κ` and such that the law of `T` under `P` is
absolutely continuous with respect to its law under `Q`, the likelihood ratio of `Q` to
`κ ∘ₘ Q.map T` has expectation the mass of `P`. -/
theorem lintegral_rnDeriv_comp_map [IsFiniteMeasure Q] [IsFiniteKernel κ] (hT : Measurable T)
    (hκ : ∀ᵐ y ∂Q.map T, ∀ᵐ x ∂κ y, T x = y) (hQ : Q ≪ κ ∘ₘ Q.map T) (hP : κ ∘ₘ P.map T = P)
    (hPQ : P.map T ≪ Q.map T) :
    ∫⁻ x, Q.rnDeriv (κ ∘ₘ Q.map T) x ∂P = P univ := by
  conv_lhs => rw [← hP]
  rw [Measure.lintegral_bind κ.aemeasurable (Measure.measurable_rnDeriv _ _).aemeasurable,
    lintegral_congr_ae (hPQ.ae_le (ae_lintegral_rnDeriv_comp_map_eq_one hT hκ hQ)),
    lintegral_one, Measure.map_apply hT .univ, preimage_univ]

/-- **The conditional e-variable** [HGLLA24]. If `κ` is the conditional law given `T` of every
member of a null `S` of finite measures, under each of which the law of `T` is absolutely
continuous with respect to its law under `Q`, the likelihood ratio of `Q` to `κ ∘ₘ Q.map T` is an
e-variable for `S`, exact by `lintegral_rnDeriv_comp_map`. -/
theorem isEVar_rnDeriv_comp_map [IsFiniteMeasure Q] [IsFiniteKernel κ] (hT : Measurable T)
    (hκ : ∀ᵐ y ∂Q.map T, ∀ᵐ x ∂κ y, T x = y) (hQ : Q ≪ κ ∘ₘ Q.map T)
    (hS : ∀ P ∈ S, IsFiniteMeasure P) (hSκ : ∀ P ∈ S, κ ∘ₘ P.map T = P)
    (hSQ : ∀ P ∈ S, P.map T ≪ Q.map T) :
    IsEVar (Q.rnDeriv (κ ∘ₘ Q.map T)) S :=
  .of_lintegral_le_measure_univ hS (Measure.measurable_rnDeriv _ _) fun P hP ↦
    (lintegral_rnDeriv_comp_map hT hκ hQ (hSκ P hP) (hSQ P hP)).le

end ProbabilityTheory
