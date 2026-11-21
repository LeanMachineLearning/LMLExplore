/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Numeraire
import LMLExplore.Probability.Kernel.Basic
import Mathlib.Probability.Distributions.Bernoulli

/-!
# The conditional e-variable and the conditional numeraire given a statistic

Let `T : Ω → 𝓨` be a statistic and `κ : Kernel 𝓨 Ω` a kernel such that `κ y` is carried by the
fiber `T ⁻¹' {y}`. Suppose that `κ` is the conditional law given `T` of every member `P` of a
null `S`, in the sense that `P = κ ∘ₘ P.map T`. For an alternative `Q`, the measure
`κ ∘ₘ Q.map T` has the law of `T` under `Q` and the conditional law `κ` of the null given `T`.

The likelihood ratio of `Q` to `κ ∘ₘ Q.map T` integrates to one against `κ y` for `Q.map T`-almost
every `y`: its conditional expectation given `T` is one. So it has expectation exactly the mass
`P univ` under every member `P` of `S` such that the law of `T` under `P` is absolutely continuous
with respect to its law under `Q`, and it is an e-variable for `S` when the members of `S` have
mass at most `1`, exact for probability measures. This is the conditional e-variable of
[HGLLA24].

The general notion of a conditional e-variable given a σ-algebra, `ProbabilityTheory.IsCondEVar`,
is in `LMLExplore.Probability.Martingale.CondEVariable`. This file treats the σ-algebra generated
by a statistic `T` through the kernel `κ` rather than through that notion, and its conclusions are
unconditional e-variables for `S`.

When moreover `κ ∘ₘ Q.map T` belongs to the effective null of `S` (for example when it is a
mixture of members of `S`, by `ProbabilityTheory.comp_mem_effectiveSet`) and dominates `Q`, this
likelihood ratio is the numeraire of `S` under `Q`, by the criterion of [LRR25, Theorem 4.1]
(`ProbabilityTheory.isNumeraire_of_ae_eq_rnDeriv`): this is the conditional numeraire. When
`κ ∘ₘ Q.map T` is moreover absolutely continuous with respect to `Q`, it is the reverse information
projection of `Q` on `S`. The two-sample numeraires of
`LMLExplore.EValues.TwoSample.Exponential` and `LMLExplore.EValues.TwoSample.Geometric` are
instances.

The hypothesis that the law of `T` under each member of `S` is absolutely continuous with respect
to its law under `Q` cannot be dropped. The likelihood ratio is determined only almost everywhere
for `κ ∘ₘ Q.map T`, so not at all on the fibers of `T` that `Q.map T` does not charge, and a member
of the null may live there. On four points, a version of the likelihood ratio that is too large on
such a fiber is not an e-variable [EVR26, verification notes, §6].

## Main statements

* `ProbabilityTheory.ae_lintegral_rnDeriv_comp_map_eq_one`: the likelihood ratio of `Q` to
  `κ ∘ₘ Q.map T` has conditional expectation one given `T`.
* `ProbabilityTheory.lintegral_rnDeriv_comp_map`, `ProbabilityTheory.isEVar_rnDeriv_comp_map`: it
  is an e-variable, exact for probability measures, for every null of measures of mass at most
  `1` of which `κ` is the conditional law given `T`.
* `ProbabilityTheory.isNumeraire_rnDeriv_comp_map`,
  `ProbabilityTheory.isNumeraire_of_ae_eq_rnDeriv_comp_map`: **the conditional numeraire**, for
  the likelihood ratio and for each of its versions.
* `ProbabilityTheory.ripr_eq_comp_map`: `κ ∘ₘ Q.map T` is then the reverse information projection
  when it is equivalent to `Q`.
* `ProbabilityTheory.exists_ae_eq_rnDeriv_comp_map_not_isEVar`: without the absolute continuity
  of the laws of `T`, a version of the likelihood ratio need not be an e-variable.

## References

* [HGLLA24] Y. Hao, P. Grünwald, T. Lardy, L. Long and R. Adams, *E-values for k-sample tests
  with exponential families*, arXiv:2303.00471.
* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4, Theorem 4.1.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, paper project
  `RemyDegenne/evalues_research` (2026), `notes/book/verification-math.md`, §6 (the four-point
  counterexample).
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
member of a null `S` of measures of mass at most `1`, under each of which the law of `T` is
absolutely continuous with respect to its law under `Q`, the likelihood ratio of `Q` to
`κ ∘ₘ Q.map T` is an e-variable for `S`, exact for probability measures by
`lintegral_rnDeriv_comp_map`. -/
theorem isEVar_rnDeriv_comp_map [IsFiniteMeasure Q] [IsFiniteKernel κ] (hT : Measurable T)
    (hκ : ∀ᵐ y ∂Q.map T, ∀ᵐ x ∂κ y, T x = y) (hQ : Q ≪ κ ∘ₘ Q.map T)
    (hS : ∀ P ∈ S, P univ ≤ 1) (hSκ : ∀ P ∈ S, κ ∘ₘ P.map T = P)
    (hSQ : ∀ P ∈ S, P.map T ≪ Q.map T) :
    IsEVar (Q.rnDeriv (κ ∘ₘ Q.map T)) S :=
  ⟨Measure.measurable_rnDeriv _ _, fun P hP ↦
    (lintegral_rnDeriv_comp_map hT hκ hQ (hSκ P hP) (hSQ P hP)).trans_le (hS P hP)⟩

/-- **The conditional numeraire**, for every version of the likelihood ratio. If `κ` is the
conditional law given `T` of every member of a null `S` of measures of mass at most `1`, under each
of which the law of `T` is absolutely continuous with respect to its law under the probability
measure `Q`, and if `κ ∘ₘ Q.map T` dominates `Q` and belongs to the effective null of `S`, then
every measurable function equal to the likelihood ratio of `Q` to `κ ∘ₘ Q.map T` almost everywhere
for `κ ∘ₘ Q.map T` is the numeraire of `S` under `Q`. The absolute continuity of the laws of `T`
cannot be dropped (`ProbabilityTheory.exists_ae_eq_rnDeriv_comp_map_not_isEVar`). -/
theorem isNumeraire_of_ae_eq_rnDeriv_comp_map [IsProbabilityMeasure Q] [IsFiniteKernel κ]
    {X : Ω → ℝ≥0∞} (hT : Measurable T) (hκ : ∀ᵐ y ∂Q.map T, ∀ᵐ x ∂κ y, T x = y)
    (hQ : Q ≪ κ ∘ₘ Q.map T) (hS : ∀ P ∈ S, P univ ≤ 1) (hSκ : ∀ P ∈ S, κ ∘ₘ P.map T = P)
    (hSQ : ∀ P ∈ S, P.map T ≪ Q.map T) (hmem : κ ∘ₘ Q.map T ∈ effectiveSet S)
    (hX : Measurable X) (hXQ : X =ᵐ[κ ∘ₘ Q.map T] Q.rnDeriv (κ ∘ₘ Q.map T)) :
    IsNumeraire X S Q :=
  isNumeraire_of_ae_eq_rnDeriv hS
    ((isEVar_rnDeriv_comp_map hT hκ hQ hS hSκ hSQ).congr hX fun P hP ↦
      ((hSκ P hP ▸ (hSQ P hP).comp_right κ : P ≪ κ ∘ₘ Q.map T)).ae_le hXQ.symm)
    hmem hQ (hQ.ae_le hXQ)

/-- **The conditional numeraire** [HGLLA24; LRR25, Theorem 4.1]. If `κ` is the conditional law
given `T` of every member of a null `S` of measures of mass at most `1`, under each of which the law
of `T` is absolutely continuous with respect to its law under the probability measure `Q`, and if
`κ ∘ₘ Q.map T` dominates `Q` and belongs to the effective null of `S`, then the likelihood ratio of
`Q` to `κ ∘ₘ Q.map T` is the numeraire of `S` under `Q`. -/
theorem isNumeraire_rnDeriv_comp_map [IsProbabilityMeasure Q] [IsFiniteKernel κ]
    (hT : Measurable T) (hκ : ∀ᵐ y ∂Q.map T, ∀ᵐ x ∂κ y, T x = y) (hQ : Q ≪ κ ∘ₘ Q.map T)
    (hS : ∀ P ∈ S, P univ ≤ 1) (hSκ : ∀ P ∈ S, κ ∘ₘ P.map T = P)
    (hSQ : ∀ P ∈ S, P.map T ≪ Q.map T) (hmem : κ ∘ₘ Q.map T ∈ effectiveSet S) :
    IsNumeraire (Q.rnDeriv (κ ∘ₘ Q.map T)) S Q :=
  isNumeraire_of_ae_eq_rnDeriv_comp_map hT hκ hQ hS hSκ hSQ hmem
    (Measure.measurable_rnDeriv _ _) .rfl

/-- **The conditional reverse information projection.** Under the hypotheses of
`ProbabilityTheory.isNumeraire_rnDeriv_comp_map`, if moreover `κ ∘ₘ Q.map T` is absolutely
continuous with respect to `Q`, it is the reverse information projection of `Q` on `S`. -/
theorem ripr_eq_comp_map [IsProbabilityMeasure Q] [IsFiniteKernel κ]
    (hT : Measurable T) (hκ : ∀ᵐ y ∂Q.map T, ∀ᵐ x ∂κ y, T x = y) (hQ : Q ≪ κ ∘ₘ Q.map T)
    (hQ' : κ ∘ₘ Q.map T ≪ Q) (hS : ∀ P ∈ S, P univ ≤ 1) (hSκ : ∀ P ∈ S, κ ∘ₘ P.map T = P)
    (hSQ : ∀ P ∈ S, P.map T ≪ Q.map T) (hmem : κ ∘ₘ Q.map T ∈ effectiveSet S) :
    ripr Q S = κ ∘ₘ Q.map T :=
  ripr_eq_of_isEVar_rnDeriv hS hmem hQ hQ' (isEVar_rnDeriv_comp_map hT hκ hQ hS hSκ hSQ)

/-! ### The absolute continuity of the laws of the statistic is needed -/

/-- **The conditional numeraire needs the absolute continuity of the laws of the statistic.** On
the four-point space `Bool × Bool` with the statistic `T = Prod.fst`, let `κ t` be a fair coin on
the fiber `{t} × Bool`, let the null be `S = {κ false, κ true}` and the alternative the point mass
`Q` at `(false, true)`. Then `κ` is the conditional law given `T` of both members of `S`, and
`κ ∘ₘ Q.map T = κ false` belongs to `S`, hence to its effective null, and dominates `Q`. But some
version of the likelihood ratio of `Q` to `κ ∘ₘ Q.map T`, equal to it almost everywhere for
`κ ∘ₘ Q.map T`, is not an e-variable for `S`, so not a numeraire: the law of `T` under `κ true`,
the point mass at `true`, is not absolutely continuous with respect to its law under `Q`, the point
mass at `false`, and the likelihood ratio is arbitrary on the fiber of `true`. -/
theorem exists_ae_eq_rnDeriv_comp_map_not_isEVar :
    ∃ (κ : Kernel Bool (Bool × Bool)) (Q : Measure (Bool × Bool)), IsMarkovKernel κ ∧
      IsProbabilityMeasure Q ∧ (∀ y, ∀ᵐ x ∂κ y, x.1 = y) ∧ Q ≪ κ ∘ₘ Q.map Prod.fst ∧
      (∀ P ∈ range κ, κ ∘ₘ P.map Prod.fst = P) ∧
      κ ∘ₘ Q.map Prod.fst ∈ effectiveSet (range κ) ∧
      ∃ X : Bool × Bool → ℝ≥0∞, Measurable X ∧
        X =ᵐ[κ ∘ₘ Q.map Prod.fst] Q.rnDeriv (κ ∘ₘ Q.map Prod.fst) ∧ ¬ IsEVar X (range κ) := by
  let p : unitInterval := ⟨2⁻¹, by norm_num, by norm_num⟩
  let κ : Kernel Bool (Bool × Bool) :=
    Kernel.ofFunOfCountable fun t ↦ bernoulliMeasure (t, true) (t, false) p
  have hfib (t : Bool) : ∀ᵐ x ∂κ t, x.1 = t := by
    rw [ae_iff, Kernel.ofFunOfCountable_apply,
      bernoulliMeasure_apply_of_notMem_of_notMem p .of_discrete (by simp) (by simp)]
  have hmap (t : Bool) : (κ t).map Prod.fst = Measure.dirac t := by
    rw [Measure.map_congr (hfib t), Measure.map_const, measure_univ, one_smul]
  have hcomp (t : Bool) : κ ∘ₘ Measure.dirac t = κ t := Measure.dirac_bind κ.measurable t
  have hQ : (Measure.dirac (false, true)).map Prod.fst = Measure.dirac false :=
    Measure.map_dirac' measurable_fst _
  refine ⟨κ, Measure.dirac (false, true), inferInstance, inferInstance, hfib, ?_, ?_,
    ?_, fun x ↦ if x.1 then 2 else (Measure.dirac (false, true)).rnDeriv (κ false) x,
    .of_discrete, ?_, ?_⟩
  · rw [hQ, hcomp]
    refine Measure.AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_
    rw [Measure.dirac_apply' _ hs, indicator_of_notMem]
    intro hmem
    have h := measure_mono_null (singleton_subset_iff.mpr hmem) hs0
    rw [Kernel.ofFunOfCountable_apply,
      bernoulliMeasure_apply_of_mem_of_notMem p .of_discrete (by simp) (by simp)] at h
    rw [ENNReal.coe_eq_zero, ← NNReal.coe_eq_zero, unitInterval.coe_toNNReal] at h
    norm_num [p] at h
  · rintro _ ⟨t, rfl⟩
    rw [hmap, hcomp]
  · rw [hQ, hcomp]
    exact subset_effectiveSet ⟨false, rfl⟩
  · rw [hQ, hcomp]
    filter_upwards [hfib false] with x hx
    simp [hx]
  · intro hX
    have h := hX.lintegral_le_one ⟨true, rfl⟩
    rw [lintegral_congr_ae ((hfib true).mono fun x hx ↦ (by simp [hx] :
      (if x.1 then 2 else (Measure.dirac (false, true)).rnDeriv (κ false) x) = 2)), lintegral_const,
      measure_univ, mul_one] at h
    norm_num at h

end ProbabilityTheory
