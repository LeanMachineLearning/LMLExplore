/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.TestSupermartingale
public import LMLExplore.MeasureTheory.Measure.Decomposition.RNDerivTrim
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
import TauCeti.MeasureTheory.Measure.ProjectiveLimit.Nat

/-!
# Likelihood ratio processes

For measures `P` and `Q` on `Ω` and a filtration `ℱ`, the likelihood ratio process of `Q` against
`P` is `n ↦ (Q.trim (ℱ.le n)).rnDeriv (P.trim (ℱ.le n))`, the Radon–Nikodym derivative of the
restrictions of `Q` and `P` to the information available at time `n`. It is the basic
construction of test supermartingales for a simple null `{P}` [RW, §7.5]: it is always a test
supermartingale for `P`, with no absolute continuity between `Q` and `P`, and it is a test
martingale when `Q` is locally absolutely continuous with respect to `P`, that is,
`Q.trim (ℱ.le n) ≪ P.trim (ℱ.le n)` for every `n`. For i.i.d. observations and
`Filtration.piLE`, the process is `∏ i ≤ n, Q₁.rnDeriv P₁ (ω i)` (Statlib's
`ProbabilityTheory.rnDeriv_trim_piLE_infinitePi`).

Conversely, on a sequence space `Π n, X n` of standard Borel spaces with the filtration
`Filtration.piLE` of the observations so far, every test martingale `M` for `P` with
`∫⁻ M 0 ∂P = 1` is the likelihood ratio process of some probability measure `Q` against `P`
[RRLK, Proposition 4]: the measures `A ↦ ∫⁻ ω in A, M n ω ∂P` on the σ-algebras of the filtration
are consistent because `M` is a martingale, and Kolmogorov's extension theorem glues them into
`Q`. Test martingales and likelihood ratios are therefore the same objects.

## Main statements

* `ProbabilityTheory.isTestSupermartingale_rnDeriv_trim`: the likelihood ratio process of a
  measure `Q` with `Q univ ≤ 1` against `P` is a test supermartingale for `P`.
* `ProbabilityTheory.isTestMartingale_rnDeriv_trim`: it is a test martingale when `Q` is locally
  absolutely continuous with respect to `P`.
* `ProbabilityTheory.IsTestMartingale.exists_trim_piLE_eq_withDensity`,
  `ProbabilityTheory.IsTestMartingale.exists_rnDeriv_trim_piLE_ae_eq`: every test martingale on a
  sequence space of standard Borel spaces with initial expectation `1` is the likelihood ratio
  process of a probability measure [RRLK, Proposition 4].

## Implementation notes

The extension step of [RRLK, Proposition 4] is Tau Ceti's sequence form of Kolmogorov's extension
theorem, `TauCeti.Measure.exists_map_frestrictLe_eq`, which builds the measure from its
finite-prefix laws by successive disintegration and the Ionescu–Tulcea theorem. Only the
coordinates after the first need to be standard Borel.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614.
* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3.
-/

public section

open MeasureTheory Set Filtration
open scoped ENNReal

namespace ProbabilityTheory

section LikelihoodRatio

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {P Q : Measure Ω}

/-- The likelihood ratio process `n ↦ (Q.trim (ℱ.le n)).rnDeriv (P.trim (ℱ.le n))` of a finite
measure `Q` against `P` is an `ℝ≥0∞`-valued supermartingale for `P`. No absolute continuity is
assumed. -/
theorem isENNSupermartingale_rnDeriv_trim [IsFiniteMeasure Q] [SigmaFiniteFiltration P ℱ] :
    IsENNSupermartingale (fun n ↦ (Q.trim (ℱ.le n)).rnDeriv (P.trim (ℱ.le n))) ℱ {P} where
  adapted _ := Measure.measurable_rnDeriv _ _
  setLIntegral_succ_le := by
    rintro _ rfl n s hs
    exact Measure.setLIntegral_rnDeriv_trim_le_of_le (ℱ.le n) (ℱ.le (n + 1))
      (ℱ.mono n.le_succ) hs

/-- **Likelihood ratio processes are test supermartingales** [RW, §7.5]. For a measure `Q` with
`Q univ ≤ 1`, the likelihood ratio process `n ↦ (Q.trim (ℱ.le n)).rnDeriv (P.trim (ℱ.le n))` is a
test supermartingale for `P`. No absolute continuity is assumed. -/
theorem isTestSupermartingale_rnDeriv_trim [SigmaFiniteFiltration P ℱ] (hQ : Q univ ≤ 1) :
    IsTestSupermartingale (fun n ↦ (Q.trim (ℱ.le n)).rnDeriv (P.trim (ℱ.le n))) ℱ {P} := by
  have : IsFiniteMeasure Q := ⟨hQ.trans_lt ENNReal.one_lt_top⟩
  refine ⟨isENNSupermartingale_rnDeriv_trim, ?_⟩
  rintro _ rfl
  rw [← setLIntegral_univ]
  exact (Measure.setLIntegral_rnDeriv_trim_le (ℱ.le 0) MeasurableSet.univ).trans hQ

/-- **Likelihood ratio processes are test martingales** under local absolute continuity
[RW, §7.5]. For a measure `Q` with `Q univ ≤ 1` and `Q.trim (ℱ.le n) ≪ P.trim (ℱ.le n)` for every
`n`, the likelihood ratio process `n ↦ (Q.trim (ℱ.le n)).rnDeriv (P.trim (ℱ.le n))` is a test
martingale for `P`. -/
theorem isTestMartingale_rnDeriv_trim [SigmaFiniteFiltration P ℱ] (hQ : Q univ ≤ 1)
    (hQP : ∀ n, Q.trim (ℱ.le n) ≪ P.trim (ℱ.le n)) :
    IsTestMartingale (fun n ↦ (Q.trim (ℱ.le n)).rnDeriv (P.trim (ℱ.le n))) ℱ {P} := by
  have : IsFiniteMeasure Q := ⟨hQ.trans_lt ENNReal.one_lt_top⟩
  refine ⟨fun _ ↦ Measure.measurable_rnDeriv _ _,
    (isTestSupermartingale_rnDeriv_trim hQ).lintegral_zero_le, ?_⟩
  rintro _ rfl n s hs
  rw [Measure.setLIntegral_rnDeriv_trim (ℱ.le (n + 1)) (hQP (n + 1)) (ℱ.mono n.le_succ s hs),
    Measure.setLIntegral_rnDeriv_trim (ℱ.le n) (hQP n) hs]

end LikelihoodRatio

/-! ### Test martingales are likelihood ratio processes -/

section Converse

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] {P : Measure (Π n, X n)}
  {M : ℕ → (Π n, X n) → ℝ≥0∞}

/-- **Test martingales are likelihood ratio processes** [RRLK, Proposition 4]. On a sequence
space `Π n, X n` whose coordinates after the first are standard Borel, with the filtration
`Filtration.piLE` of the observations so far, let `M` be a test martingale for `P` with
`∫⁻ M 0 ∂P = 1`. Then some probability measure `Q` has density `M n` with respect to `P` on the
σ-algebra of every time `n`. -/
theorem IsTestMartingale.exists_trim_piLE_eq_withDensity [∀ n, StandardBorelSpace (X (n + 1))]
    (hM : IsTestMartingale M (piLE (X := X)) {P}) (h0 : ∫⁻ ω, M 0 ω ∂P = 1) :
    ∃ Q : Measure (Π n, X n), IsProbabilityMeasure Q ∧
      ∀ n, Q.trim ((piLE (X := X)).le n) = (P.trim ((piLE (X := X)).le n)).withDensity (M n) := by
  -- The prefix `ω 0, …, ω n` generates the σ-algebra of time `n`.
  have hfr (n : ℕ) : Measurable[piLE (X := X) n] (Preorder.frestrictLe n) := by
    rw [piLE_eq_comap_frestrictLe]
    exact comap_measurable _
  -- The laws of the prefixes `ω 0, …, ω n` under the measure of density `M n` with respect to `P`.
  let R (n : ℕ) : Measure (Π i : Finset.Iic n, X i) :=
    (P.withDensity (M n)).map (Preorder.frestrictLe n)
  have hR (n : ℕ) : IsProbabilityMeasure (R n) := by
    refine ⟨?_⟩
    rw [Measure.map_apply (Preorder.measurable_frestrictLe n) MeasurableSet.univ, preimage_univ,
      withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      hM.lintegral_eq (mem_singleton P) 0 n, h0]
  -- They are consistent because `M` is a martingale.
  have hRcons (n : ℕ) : (R (n + 1)).map (Preorder.frestrictLe₂ n.le_succ) = R n := by
    ext A hA
    have hpre := hfr n hA
    rw [Measure.map_map (Preorder.measurable_frestrictLe₂ _) (Preorder.measurable_frestrictLe _),
      Preorder.frestrictLe₂_comp_frestrictLe,
      Measure.map_apply (Preorder.measurable_frestrictLe n) hA,
      Measure.map_apply (Preorder.measurable_frestrictLe n) hA,
      withDensity_apply _ ((piLE (X := X)).le n _ hpre),
      withDensity_apply _ ((piLE (X := X)).le n _ hpre)]
    exact hM.setLIntegral_eq (mem_singleton P) n.le_succ hpre
  obtain ⟨Q, hQ, hQR⟩ := TauCeti.Measure.exists_map_frestrictLe_eq R hRcons
  refine ⟨Q, hQ, fun n ↦ ?_⟩
  rw [← trim_withDensity _ (hM.adapted n)]
  refine @Measure.ext _ (piLE (X := X) n) _ _ fun s hs ↦ ?_
  rw [piLE_eq_comap_frestrictLe] at hs
  obtain ⟨A, hA, rfl⟩ := hs
  have hpre := hfr n hA
  rw [trim_measurableSet_eq _ hpre, trim_measurableSet_eq _ hpre,
    ← Measure.map_apply (Preorder.measurable_frestrictLe n) hA, hQR n,
    Measure.map_apply (Preorder.measurable_frestrictLe n) hA]

/-- **Test martingales are likelihood ratio processes** [RRLK, Proposition 4], in Radon–Nikodym
form. On a sequence space `Π n, X n` whose coordinates after the first are standard Borel, with
the filtration `ℱ = Filtration.piLE`, every test martingale `M` for a measure `P` that is
σ-finite on the filtration, with `∫⁻ M 0 ∂P = 1`, is `P`-almost surely the likelihood ratio
process `n ↦ (Q.trim (ℱ.le n)).rnDeriv (P.trim (ℱ.le n))` of a probability measure `Q` that is
locally absolutely continuous with respect to `P`. -/
theorem IsTestMartingale.exists_rnDeriv_trim_piLE_ae_eq [∀ n, StandardBorelSpace (X (n + 1))]
    [SigmaFiniteFiltration P (piLE (X := X))]
    (hM : IsTestMartingale M (piLE (X := X)) {P}) (h0 : ∫⁻ ω, M 0 ω ∂P = 1) :
    ∃ Q : Measure (Π n, X n), IsProbabilityMeasure Q ∧ ∀ n,
      Q.trim ((piLE (X := X)).le n) ≪ P.trim ((piLE (X := X)).le n) ∧
      (Q.trim ((piLE (X := X)).le n)).rnDeriv (P.trim ((piLE (X := X)).le n)) =ᵐ[P] M n := by
  obtain ⟨Q, hQ, hQM⟩ := hM.exists_trim_piLE_eq_withDensity h0
  refine ⟨Q, hQ, fun n ↦ ⟨?_, ?_⟩⟩
  · rw [hQM n]
    exact withDensity_absolutelyContinuous _ _
  · rw [hQM n]
    exact ae_eq_of_ae_eq_trim (Measure.rnDeriv_withDensity _ (hM.adapted n))

end Converse

end ProbabilityTheory
