/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Radon–Nikodym derivatives of restrictions to coarser σ-algebras

For measures `μ` and `ν` and sub-σ-algebras `m ≤ m'` of the ambient σ-algebra, compare the
Radon–Nikodym derivatives `(μ.trim hm).rnDeriv (ν.trim hm)` and
`(μ.trim hm').rnDeriv (ν.trim hm')` of the restrictions of `μ` and `ν` to `m` and `m'`. Over a
set of the coarser σ-algebra `m`, the set integral against `ν` of the derivative on `m'` is at
most that of the derivative on `m`: refining the σ-algebra can only move mass of `μ` from the
absolutely continuous part to the singular part. No absolute continuity is assumed. Applied to a
filtration, this says that the density process of `μ` with respect to `ν` is an `ℝ≥0∞`-valued
supermartingale for `ν`.

## Main statements

* `MeasureTheory.Measure.setLIntegral_rnDeriv_trim_le`,
  `MeasureTheory.Measure.setLIntegral_rnDeriv_trim`: over an `m`-measurable set `s`, the set
  integral of `(μ.trim hm).rnDeriv (ν.trim hm)` against `ν` is at most `μ s`, with equality when
  `μ.trim hm ≪ ν.trim hm`.
* `MeasureTheory.Measure.setLIntegral_rnDeriv_trim_le_of_le`: for `m ≤ m'` and an
  `m`-measurable set `s`, `∫⁻ x in s, (μ.trim hm').rnDeriv (ν.trim hm') x ∂ν` is at most
  `∫⁻ x in s, (μ.trim hm).rnDeriv (ν.trim hm) x ∂ν`.
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

/-- **The density process is a supermartingale.** For sub-σ-algebras `m ≤ m'` of the ambient
σ-algebra and an `m`-measurable set `s`, the set integral over `s` of the Radon–Nikodym derivative
of the restrictions of `μ` and `ν` to `m'` is at most that of the derivative of their
restrictions to `m`. -/
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

end MeasureTheory.Measure
