/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.StoppedNull
public import LMLExplore.EValues.KLInf

/-!
# Optimal e-processes

E-processes for a null `S` are the e-variables of the stopped null `stoppedNull ℱ S` on the space
of stopped paths (`isEProcess_iff_isEVar_stoppedNull`). Statlib's existence of numeraires then
gives, for every null of measures of mass at most one and every finite measure on the stopped
paths, an e-process that is a numeraire, with no dominating measure. For the mixture over a
probability measure `ρ` on the times of the stopped laws of a probability measure `Q` at the
constant times, this is an e-process `E*` with `∑' n, ρ {n} * ∫⁻ E n / E* n ∂Q ≤ 1` for every
e-process `E` [EVR26, Note 40, Theorem 1], the form without a dominating measure of
[KG22, Theorem 5]; it maximizes the expected logarithm over the e-processes, and the maximum is the
smallest relative entropy from the mixture to the effective null of the stopped null, by the
duality of [LRR25].

## Main statements

* `ProbabilityTheory.exists_isEProcess_isNumeraire_stoppedNull`: for every finite measure on the
  stopped paths, some e-process is a numeraire of the stopped null.
* `ProbabilityTheory.isGreatest_eintegral_log_isEProcess`: under a probability measure on the
  stopped paths, the largest expected logarithm of an e-process is the smallest relative entropy
  to the effective null of the stopped null, and it is attained.
* `ProbabilityTheory.exists_isEProcess_forall_tsum_lintegral_div_le_one`: for probability
  measures `Q` on `Ω` and `ρ` on the times, some e-process `E*` has
  `∑' n, ρ {n} * ∫⁻ E n / E* n ∂Q ≤ 1` for every e-process `E` [EVR26, Note 40, Theorem 1].

## Implementation notes

The existence of optimal e-processes is adapted from the file `notes/lean-wip/StoppedPaths.lean`
(commit `c6c6ba8`) of the paper project `RemyDegenne/evalues_research` (Apache 2.0), with the
stopped paths carrying Tau Ceti's progressive σ-algebra in place of a σ-algebra of its own.

## References

* [KG22] W. M. Koolen and P. Grünwald, *Log-optimal anytime-valid e-values*, Int. J. Approx.
  Reason. 141 (2022), Theorem 5.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, the notes and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026, Note 40.
* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {S : Set (Measure Ω)}

/-- **Existence of an optimal e-process.** For a null of measures of mass at most one, with no
dominating measure, and every finite measure `R` on the stopped paths, some e-process `E` for `S`
is a numeraire of the stopped null against `R`: `Function.uncurry E` maximizes the expected
logarithm under `R`, and `∫⁻ Function.uncurry F / Function.uncurry E ∂R ≤ 1` for every
e-process `F` when `R` is a probability measure. -/
theorem exists_isEProcess_isNumeraire_stoppedNull (hS : ∀ P ∈ S, P univ ≤ 1)
    (R : @Measure (ℕ × Ω) ℱ.progressive) [IsFiniteMeasure R] :
    ∃ E : ℕ → Ω → ℝ≥0∞, IsEProcess E ℱ S ∧
      IsNumeraire (Function.uncurry E) (stoppedNull ℱ S) R := by
  obtain ⟨X, hX⟩ := exists_isNumeraire R (stoppedNull ℱ S) fun _ ↦
    measure_univ_le_one_of_mem_stoppedNull hS
  rw [← Function.uncurry_curry X] at hX
  exact ⟨Function.curry X, isEProcess_iff_isEVar_stoppedNull.2 hX.isEVar, hX⟩

/-- **The largest expected logarithm of an e-process.** For a null of measures of mass at most
one and a probability measure `R` on the stopped paths, the expected logarithms under `R` of the
e-processes, read on the stopped paths, have a largest element, the smallest relative entropy
from `R` to the effective null of the stopped null. -/
theorem isGreatest_eintegral_log_isEProcess (hS : ∀ P ∈ S, P univ ≤ 1)
    (R : @Measure (ℕ × Ω) ℱ.progressive) [IsProbabilityMeasure R] :
    IsGreatest ((fun F : ℕ → Ω → ℝ≥0∞ ↦ ∫ᵉ x, ENNReal.log (Function.uncurry F x) ∂R) ''
      {F | IsEProcess F ℱ S}) (klInf R (effectiveSet (stoppedNull ℱ S))) := by
  have hS' : ∀ μ ∈ stoppedNull ℱ S, μ univ ≤ 1 := fun _ ↦ measure_univ_le_one_of_mem_stoppedNull hS
  rw [← maxEPower_eq_klInf_effectiveSet hS']
  obtain ⟨E, hE, hX⟩ := exists_isEProcess_isNumeraire_stoppedNull hS R
  refine ⟨⟨E, hE, ?_⟩, ?_⟩
  · rw [maxEPower_def, hX.maxUtility_eq_eintegral]
  · rintro _ ⟨F, hF, rfl⟩
    exact (isEProcess_iff_isEVar_stoppedNull.1 hF).eintegral_log_le_maxEPower R

/-- **An e-process that is optimal for a distribution over times** [EVR26, Note 40, Theorem 1;
KG22, Theorem 5]. For a null
of measures of mass at most one, with no dominating measure, and probability measures `Q` on `Ω`
and `ρ` on the times, some e-process `E*` satisfies `∑' n, ρ {n} * ∫⁻ E n / E* n ∂Q ≤ 1` for
every e-process `E`. It is the numeraire of the stopped null against the mixture
`Measure.sum fun n ↦ ρ {n} • stoppedLaw ℱ Q fun _ ↦ n` of the stopped laws of `Q` at the constant
times, so that `isGreatest_eintegral_log_isEProcess` computes its expected logarithm under the
mixture. -/
theorem exists_isEProcess_forall_tsum_lintegral_div_le_one (hS : ∀ P ∈ S, P univ ≤ 1)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (ρ : Measure ℕ) [IsProbabilityMeasure ρ] :
    ∃ E : ℕ → Ω → ℝ≥0∞, IsEProcess E ℱ S ∧
      IsNumeraire (Function.uncurry E) (stoppedNull ℱ S)
        (Measure.sum fun n ↦ ρ {n} • stoppedLaw ℱ Q fun _ ↦ n) ∧
      ∀ F : ℕ → Ω → ℝ≥0∞, IsEProcess F ℱ S → ∑' n, ρ {n} * ∫⁻ ω, F n ω / E n ω ∂Q ≤ 1 := by
  obtain ⟨E, hE, hX⟩ := exists_isEProcess_isNumeraire_stoppedNull hS
    (Measure.sum fun n ↦ ρ {n} • stoppedLaw ℱ Q fun _ ↦ n)
  refine ⟨E, hE, hX, fun F hF ↦ ?_⟩
  have hF' := isEProcess_iff_isEVar_stoppedNull.1 hF
  have h := hX.lintegral_div_le_one hF'
  rwa [lintegral_sum_smul_stoppedLaw_const ρ Q
    (f := fun x ↦ Function.uncurry F x / Function.uncurry E x)
    (hF'.measurable.div hX.measurable)] at h

end ProbabilityTheory
