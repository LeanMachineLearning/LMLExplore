/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import TauCeti.MeasureTheory.Measure.Mixture.Basic

/-!
# Radon–Nikodym derivatives of restrictions to coarser σ-algebras

For measures `μ` and `ν` and sub-σ-algebras `m ≤ m'` of the ambient σ-algebra, compare the
Radon–Nikodym derivatives `(μ.trim hm).rnDeriv (ν.trim hm)` and
`(μ.trim hm').rnDeriv (ν.trim hm')` of the restrictions of `μ` and `ν` to `m` and `m'`. Over a
set of the coarser σ-algebra `m`, the set integral against `ν` of the derivative on `m'` is at
most that of the derivative on `m`: refining the σ-algebra can only move mass of `μ` from the
absolutely continuous part to the singular part. No absolute continuity is assumed. Applied to a
filtration, this says that the process of Radon–Nikodym derivatives of the restrictions of `μ` and
`ν` is an `ℝ≥0∞`-valued supermartingale for `ν`.

The restriction to `m` of a mixture `π.bind Q` of measures is the mixture of the restrictions, and
when every component is absolutely continuous with respect to `ν` on `m`, the Radon–Nikodym
derivative of the mixture on `m` is the mixture `∫⁻ θ, f θ x ∂π` of jointly measurable versions
`f θ` of the derivatives of the components. Applied to a filtration, this identifies the mixture
of likelihood ratio processes with the likelihood ratio process of the mixture.

## Main statements

* `MeasureTheory.Measure.setLIntegral_rnDeriv_trim_le`,
  `MeasureTheory.Measure.setLIntegral_rnDeriv_trim`: over an `m`-measurable set `s`, the set
  integral of `(μ.trim hm).rnDeriv (ν.trim hm)` against `ν` is at most `μ s`, with equality when
  `μ.trim hm ≪ ν.trim hm`.
* `MeasureTheory.Measure.setLIntegral_rnDeriv_trim_le_of_le`: for `m ≤ m'` and an
  `m`-measurable set `s`, `∫⁻ x in s, (μ.trim hm').rnDeriv (ν.trim hm') x ∂ν` is at most
  `∫⁻ x in s, (μ.trim hm).rnDeriv (ν.trim hm) x ∂ν`.
* `MeasureTheory.Measure.trim_bind`, `MeasureTheory.Measure.absolutelyContinuous_trim_bind`: the
  restriction of a mixture is the mixture of the restrictions, and it is absolutely continuous
  when almost every component is.
* `MeasureTheory.Measure.rnDeriv_trim_bind_ae_eq`: the Radon–Nikodym derivative of the
  restriction of a mixture is the mixture of the derivatives of the restrictions of its
  components.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} {m m' m0 : MeasurableSpace α} {μ ν : Measure α}

/-- Over an `m`-measurable set `s`, the set integral against `ν` of the Radon–Nikodym derivative
of the restrictions of `μ` and `ν` to `m` is at most `μ s`. -/
theorem setLIntegral_rnDeriv_trim_le (hm : m ≤ m0) {s : Set α} (hs : MeasurableSet[m] s) :
    ∫⁻ x in s, (μ.trim hm).rnDeriv (ν.trim hm) x ∂ν ≤ μ s := by
  rw [← setLIntegral_trim hm (measurable_rnDeriv _ _) hs, ← trim_measurableSet_eq hm hs]
  exact setLIntegral_rnDeriv_le _

/-- If the restriction of `μ` to `m` is absolutely continuous with respect to that of `ν`, then
over an `m`-measurable set `s`, the set integral against `ν` of the Radon–Nikodym derivative of
the restrictions is `μ s`. -/
theorem setLIntegral_rnDeriv_trim (hm : m ≤ m0)
    [(μ.trim hm).HaveLebesgueDecomposition (ν.trim hm)] (hμν : μ.trim hm ≪ ν.trim hm)
    {s : Set α} (hs : MeasurableSet[m] s) :
    ∫⁻ x in s, (μ.trim hm).rnDeriv (ν.trim hm) x ∂ν = μ s := by
  rw [← setLIntegral_trim hm (measurable_rnDeriv _ _) hs, setLIntegral_rnDeriv' hμν hs,
    trim_measurableSet_eq hm hs]

/-- **Refining the σ-algebra decreases set integrals of the Radon–Nikodym derivative.**
For sub-σ-algebras `m ≤ m'` of the ambient σ-algebra and an `m`-measurable set `s`, the set
integral over `s` of the Radon–Nikodym derivative of the restrictions of `μ` and `ν` to `m'` is at
most that of the derivative of their restrictions to `m`. -/
theorem setLIntegral_rnDeriv_trim_le_of_le (hm : m ≤ m0) (hm' : m' ≤ m0) (hmm' : m ≤ m')
    [(μ.trim hm).HaveLebesgueDecomposition (ν.trim hm)] {s : Set α} (hs : MeasurableSet[m] s) :
    ∫⁻ x in s, (μ.trim hm').rnDeriv (ν.trim hm') x ∂ν ≤
      ∫⁻ x in s, (μ.trim hm).rnDeriv (ν.trim hm) x ∂ν := by
  -- `N` carries `ν` on `m` and no mass of the singular part of `μ` on `m`.
  obtain ⟨N, hN, hsingN, hνN⟩ := mutuallySingular_singularPart (μ.trim hm) (ν.trim hm)
  have hsN : MeasurableSet[m] (s ∩ N) := hs.inter hN
  rw [trim_measurableSet_eq hm hN.compl] at hνN
  have hsing : (μ.trim hm).singularPart (ν.trim hm) (s ∩ N) = 0 :=
    measure_mono_null inter_subset_right hsingN
  have hs_ae : s ∩ N =ᵐ[ν] s := inter_ae_eq_left_of_ae_eq_univ (ae_eq_univ.mpr hνN)
  calc ∫⁻ x in s, (μ.trim hm').rnDeriv (ν.trim hm') x ∂ν
      = ∫⁻ x in s ∩ N, (μ.trim hm').rnDeriv (ν.trim hm') x ∂ν := setLIntegral_congr hs_ae.symm
    _ ≤ μ (s ∩ N) := setLIntegral_rnDeriv_trim_le hm' (hmm' _ hsN)
    _ = ∫⁻ x in s ∩ N, (μ.trim hm).rnDeriv (ν.trim hm) x ∂(ν.trim hm) := by
        rw [← trim_measurableSet_eq hm hsN, ← withDensity_apply _ hsN]
        conv_lhs => rw [haveLebesgueDecomposition_add (μ.trim hm) (ν.trim hm)]
        rw [add_apply, hsing, zero_add]
    _ ≤ ∫⁻ x in s, (μ.trim hm).rnDeriv (ν.trim hm) x ∂(ν.trim hm) :=
        lintegral_mono_set inter_subset_left
    _ = ∫⁻ x in s, (μ.trim hm).rnDeriv (ν.trim hm) x ∂ν :=
        setLIntegral_trim hm (measurable_rnDeriv _ _) hs

/-! ### Mixtures -/

section Mixture

variable {Θ : Type*} {mΘ : MeasurableSpace Θ} {π : Measure Θ} {Q : Θ → Measure α}

/-- The restriction of a family of measures to a sub-σ-algebra `m` is measurable for the
σ-algebra of measures on `m`. -/
private lemma measurable_trim (hm : m ≤ m0) (hQ : Measurable Q) :
    Measurable[mΘ, @instMeasurableSpace α m] fun θ ↦ (Q θ).trim hm :=
  measurable_of_measurable_coe (mα := m) _ fun s hs ↦ by
    simp_rw [trim_measurableSet_eq hm hs]
    exact (measurable_coe (hm s hs)).comp hQ

/-- The restriction to a sub-σ-algebra `m` of a mixture of measures is the mixture of their
restrictions to `m`. -/
theorem trim_bind (hm : m ≤ m0) (hQ : Measurable Q) :
    (π.bind Q).trim hm = bind (mβ := m) π fun θ ↦ (Q θ).trim hm := by
  refine @Measure.ext α m _ _ fun s hs ↦ ?_
  rw [trim_measurableSet_eq hm hs, bind_apply (hm s hs) hQ.aemeasurable,
    bind_apply (mβ := m) hs (measurable_trim hm hQ).aemeasurable]
  exact lintegral_congr fun θ ↦ (trim_measurableSet_eq hm hs).symm

/-- The restriction to a sub-σ-algebra `m` of a mixture of measures is absolutely continuous with
respect to that of `ν` when the restrictions of almost all of its components are. -/
theorem absolutelyContinuous_trim_bind (hm : m ≤ m0) (hQ : Measurable Q)
    (hQν : ∀ᵐ θ ∂π, (Q θ).trim hm ≪ ν.trim hm) : (π.bind Q).trim hm ≪ ν.trim hm := by
  refine AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_
  have hQs : Measurable fun θ ↦ Q θ s := (measurable_coe (hm s hs)).comp hQ
  rw [trim_measurableSet_eq hm hs, bind_apply (hm s hs) hQ.aemeasurable, lintegral_eq_zero_iff hQs]
  filter_upwards [hQν] with θ hθ
  rw [← trim_measurableSet_eq hm hs]
  exact hθ hs0

/-- **The Radon–Nikodym derivative of a mixture is the mixture of the derivatives.** Let `Q θ` be
a measurable family of finite measures whose restrictions to a sub-σ-algebra `m` are, for almost
every `θ`, absolutely continuous with respect to that of `ν`, and let `f θ` be versions of the
Radon–Nikodym derivatives `((Q θ).trim hm).rnDeriv (ν.trim hm)`, jointly measurable for the
σ-algebra of `Θ` and `m`. Then the derivative of the restriction of the mixture `π.bind Q` is
`ν`-almost everywhere the mixture `∫⁻ θ, f θ x ∂π`. -/
theorem rnDeriv_trim_bind_ae_eq (hm : m ≤ m0) [SFinite π] [SigmaFinite (ν.trim hm)]
    (hQ : Measurable Q) [∀ θ, IsFiniteMeasure (Q θ)] {f : Θ → α → ℝ≥0∞}
    (hf : Measurable[mΘ.prod m] (Function.uncurry f))
    (hfQ : ∀ᵐ θ ∂π, f θ =ᵐ[ν] ((Q θ).trim hm).rnDeriv (ν.trim hm))
    (hQν : ∀ᵐ θ ∂π, (Q θ).trim hm ≪ ν.trim hm) :
    ((π.bind Q).trim hm).rnDeriv (ν.trim hm) =ᵐ[ν] fun x ↦ ∫⁻ θ, f θ x ∂π := by
  have hdens : ∀ᵐ θ ∂π, (Q θ).trim hm = (ν.trim hm).withDensity (f θ) := by
    filter_upwards [hfQ, hQν] with θ hθ hθν
    have hfθ : Measurable[m] (f θ) := hf.comp (measurable_prodMk_left (m := mΘ))
    rw [withDensity_congr_ae ((StronglyMeasurable.ae_eq_trim_iff hm hfθ.stronglyMeasurable
      (measurable_rnDeriv _ _).stronglyMeasurable).2 hθ), withDensity_rnDeriv_eq _ _ hθν]
  rw [trim_bind hm hQ]
  exact ae_eq_of_ae_eq_trim (@rnDeriv_bind_withDensity Θ α mΘ m π (ν.trim hm) _ f _ _ hf hdens)

end Mixture

end MeasureTheory.Measure
