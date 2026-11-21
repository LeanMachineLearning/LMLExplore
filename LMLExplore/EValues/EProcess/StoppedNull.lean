/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.KLInf
public import LMLExplore.EValues.Null.QuasiSure
public import LMLExplore.Probability.Process.StoppedLaw

/-!
# E-processes are the e-variables of the stopped null

For a filtration `ℱ` indexed by `ℕ`, the space of stopped paths is `ℕ × Ω` with the progressive
σ-algebra `Filtration.progressive ℱ`, whose measurable functions are the adapted processes, and a
stopping time `τ` with values in `ℕ` sends a measure `P` on `Ω` to the law `stoppedLaw ℱ P τ` of
the stopped path `ω ↦ (τ ω, ω)`. The stopped null `stoppedNull ℱ S` of a null `S` is the set of
the stopped laws of its members at all such stopping times. An adapted process `E` is an
e-process for `S` exactly when `Function.uncurry E` is an e-variable for the stopped null
[KG22, Section 3], with no hypothesis on the null: e-processes are the e-variables of one null on
one measurable space, and the theory of e-variables applies to them. Its closure under `liminf`
gives the closure of e-processes under the time-wise `liminf`, and the quasi-sure filter of the
stopped null is read time by time.

Statlib's existence of numeraires then gives, for every null of measures of mass at most one and
every finite measure on the stopped paths, an e-process that is a numeraire, with no dominating
measure. For the mixture over a probability measure `ρ` on the times of the stopped laws of a
probability measure `Q` at the constant times, this is an e-process `E*` with
`∑' n, ρ {n} * ∫⁻ E n / E* n ∂Q ≤ 1` for every e-process `E` [EVR26, Note 40, Theorem 1], the form
without a dominating measure of [KG22, Theorem 5]; it maximizes the expected logarithm over the
e-processes, and the maximum is the smallest relative entropy from the mixture to the effective
null of the stopped null, by the duality of [LRR25].

## Main definitions

* `ProbabilityTheory.stoppedNull ℱ S`: the stopped laws of the members of `S` at the stopping
  times with values in `ℕ`.

## Main statements

* `ProbabilityTheory.isEProcess_iff_isEVar_stoppedNull`: an adapted process is an e-process
  exactly when it is an e-variable on the space of stopped paths for the stopped null.
* `ProbabilityTheory.eventually_quasiSure_stoppedNull_iff`: a progressive property holds
  quasi-surely for the stopped null exactly when it holds quasi-surely for the null at every time.
* `ProbabilityTheory.isEProcess_liminf`: the time-wise `liminf` of a sequence of e-processes is an
  e-process.
* `ProbabilityTheory.exists_isEProcess_isNumeraire_stoppedNull`: for every finite measure on the
  stopped paths, some e-process is a numeraire of the stopped null.
* `ProbabilityTheory.isGreatest_eintegral_log_isEProcess`: under a probability measure on the
  stopped paths, the largest expected logarithm of an e-process is the smallest relative entropy
  to the effective null of the stopped null, and it is attained.
* `ProbabilityTheory.exists_isEProcess_forall_tsum_lintegral_div_le_one`: for probability
  measures `Q` on `Ω` and `ρ` on the times, some e-process `E*` has
  `∑' n, ρ {n} * ∫⁻ E n / E* n ∂Q ≤ 1` for every e-process `E` [EVR26, Note 40, Theorem 1].

## Implementation notes

The stopped paths, the stopped null and the existence of optimal e-processes are adapted from the
file `notes/lean-wip/StoppedPaths.lean` (commit `c6c6ba8`) of the paper project
`RemyDegenne/evalues_research` (Apache 2.0), which works with a σ-algebra of its own on `ℕ × Ω`;
here it is Tau Ceti's progressive σ-algebra, which in discrete time has the same measurable sets
(`Filtration.measurableSet_progressive_iff_of_countable`).

## References

* [KG22] W. M. Koolen and P. Grünwald, *Log-optimal anytime-valid e-values*, Int. J. Approx.
  Reason. 141 (2022), Section 3 and Theorem 5.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, the notes and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026, Note 40.
* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {S T : Set (Measure Ω)}
  {P : Measure Ω} {τ : Ω → ℕ} {E : ℕ → Ω → ℝ≥0∞}

/-! ### The stopped null -/

/-- The **stopped null** of a null `S` for a filtration `ℱ` indexed by `ℕ`: the stopped laws
`stoppedLaw ℱ P τ` of the members `P` of `S` at the stopping times `τ` with values in `ℕ`, a null
on the space `ℕ × Ω` of stopped paths with the progressive σ-algebra of `ℱ`. -/
def stoppedNull (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω)) :
    Set (@Measure (ℕ × Ω) ℱ.progressive) :=
  {μ | ∃ P ∈ S, ∃ τ : Ω → ℕ, IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ)) ∧ stoppedLaw ℱ P τ = μ}

theorem stoppedNull_def (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω)) :
    stoppedNull ℱ S = {μ | ∃ P ∈ S, ∃ τ : Ω → ℕ,
      IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ)) ∧ stoppedLaw ℱ P τ = μ} := (rfl)

@[simp]
theorem mem_stoppedNull {μ : @Measure (ℕ × Ω) ℱ.progressive} :
    μ ∈ stoppedNull ℱ S ↔ ∃ P ∈ S, ∃ τ : Ω → ℕ,
      IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ)) ∧ stoppedLaw ℱ P τ = μ :=
  Iff.rfl

/-- The stopped law of a member of the null at a stopping time is in the stopped null. -/
theorem stoppedLaw_mem_stoppedNull (hP : P ∈ S)
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ))) :
    stoppedLaw ℱ P τ ∈ stoppedNull ℱ S :=
  ⟨P, hP, τ, hτ, rfl⟩

@[gcongr]
theorem stoppedNull_mono (hST : S ⊆ T) : stoppedNull ℱ S ⊆ stoppedNull ℱ T := by
  rintro _ ⟨P, hP, τ, hτ, rfl⟩
  exact ⟨P, hST hP, τ, hτ, rfl⟩

@[simp]
theorem stoppedNull_empty : stoppedNull ℱ (∅ : Set (Measure Ω)) = ∅ := by
  ext
  simp

theorem stoppedNull_union : stoppedNull ℱ (S ∪ T) = stoppedNull ℱ S ∪ stoppedNull ℱ T := by
  ext
  simp only [mem_stoppedNull, mem_union]
  grind

/-- The stopped laws of a null of probability measures are probability measures. -/
theorem isProbabilityMeasure_of_mem_stoppedNull (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    {μ : @Measure (ℕ × Ω) ℱ.progressive} (hμ : μ ∈ stoppedNull ℱ S) : IsProbabilityMeasure μ := by
  obtain ⟨P, hP, τ, -, rfl⟩ := hμ
  have := hS P hP
  infer_instance

/-- The stopped laws of a null of measures of mass at most one have mass at most one. -/
theorem measure_univ_le_one_of_mem_stoppedNull (hS : ∀ P ∈ S, P univ ≤ 1)
    {μ : @Measure (ℕ × Ω) ℱ.progressive} (hμ : μ ∈ stoppedNull ℱ S) : μ univ ≤ 1 := by
  obtain ⟨P, hP, τ, hτ, rfl⟩ := hμ
  rw [stoppedLaw_univ hτ.measurable_nat]
  exact hS P hP

/-! ### E-processes as e-variables on stopped paths -/

/-- **E-processes are the e-variables of the stopped null** [KG22, Section 3]. A process `E` is an
e-process for `S` exactly when `Function.uncurry E` is an e-variable on the space of stopped paths
for the stopped null `stoppedNull ℱ S`. No hypothesis on the null is needed. -/
theorem isEProcess_iff_isEVar_stoppedNull :
    IsEProcess E ℱ S ↔ IsEVar (Function.uncurry E) (stoppedNull ℱ S) := by
  refine ⟨fun hE ↦ ?_, fun hE ↦ ?_⟩
  · have hE_meas := Filtration.measurable_uncurry_progressive_iff.2 hE.adapted
    refine ⟨hE_meas, ?_⟩
    rintro _ ⟨P, hP, τ, hτ, rfl⟩
    rw [lintegral_stoppedLaw hτ.measurable_nat hE_meas]
    exact hE.lintegral_le_one hτ hP
  · refine .of_lintegral_le_one (Filtration.measurable_uncurry_progressive_iff.1 hE.measurable)
      fun τ hτ P hP ↦ ?_
    have h := hE.lintegral_le_one (stoppedLaw_mem_stoppedNull hP hτ)
    rwa [lintegral_stoppedLaw hτ.measurable_nat hE.measurable] at h

/-- **The quasi-sure filter of the stopped null.** A property of stopped paths given by a
progressive set holds quasi-surely for the stopped null exactly when, at every time `n`, it holds
quasi-surely for the null. In particular a progressive set is polar for the stopped null exactly
when each of its sections is polar for the null. -/
theorem eventually_quasiSure_stoppedNull_iff {p : ℕ × Ω → Prop}
    (hp : MeasurableSet[ℱ.progressive] {x | p x}) :
    (∀ᶠ x in quasiSure (stoppedNull ℱ S), p x) ↔ ∀ n, ∀ᶠ ω in quasiSure S, p (n, ω) := by
  simp only [eventually_quasiSure_iff]
  refine ⟨fun h n P hP ↦ ?_, ?_⟩
  · have h' := h _ (stoppedLaw_mem_stoppedNull (τ := fun _ ↦ n) hP (isStoppingTime_natCast n))
    rwa [ae_stoppedLaw_iff measurable_const hp] at h'
  · rintro h _ ⟨P, hP, τ, hτ, rfl⟩
    rw [ae_stoppedLaw_iff hτ.measurable_nat hp]
    filter_upwards [ae_all_iff.2 fun n ↦ h n P hP] with ω hω using hω (τ ω)

/-- **The time-wise `liminf` of e-processes.** For a sequence `E k` of e-processes, the process
`fun n ω ↦ liminf (fun k ↦ E k n ω) atTop` is an e-process. On the stopped paths, this is the
closure of e-variables under `liminf` (Statlib's `isEVar_liminf`) for the stopped null. -/
theorem isEProcess_liminf {E : ℕ → ℕ → Ω → ℝ≥0∞} (hE : ∀ k, IsEProcess (E k) ℱ S) :
    IsEProcess (fun n ω ↦ liminf (fun k ↦ E k n ω) atTop) ℱ S :=
  isEProcess_iff_isEVar_stoppedNull.2
    (isEVar_liminf fun k ↦ isEProcess_iff_isEVar_stoppedNull.1 (hE k))

/-! ### Optimal e-processes -/

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
  have := isProbabilityMeasure_sum_smul_stoppedLaw_const (ℱ := ℱ) ρ Q
  obtain ⟨E, hE, hX⟩ := exists_isEProcess_isNumeraire_stoppedNull hS
    (Measure.sum fun n ↦ ρ {n} • stoppedLaw ℱ Q fun _ ↦ n)
  refine ⟨E, hE, hX, fun F hF ↦ ?_⟩
  have hF' := isEProcess_iff_isEVar_stoppedNull.1 hF
  have h := hX.lintegral_div_le_one hF'
  rwa [lintegral_sum_smul_stoppedLaw_const ρ Q
    (f := fun x ↦ Function.uncurry F x / Function.uncurry E x)
    (hF'.measurable.div hX.measurable)] at h

end ProbabilityTheory
