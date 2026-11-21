/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Null.QuasiSure
public import LMLExplore.Probability.Process.StoppedLaw

/-!
# E-processes are the e-variables of the stopped null

For a filtration `ℱ` indexed by `ℕ`, the space of stopped paths is `ℕ × Ω` with the progressive
σ-algebra `Filtration.progressive ℱ`, whose measurable functions are the adapted processes, and a
stopping time `τ` that is finite everywhere sends a measure `P` on `Ω` to the law of the stopped
path `ω ↦ ((τ ω).untopA, ω)`, the stopped law `stoppedLaw ℱ P fun ω ↦ (τ ω).untopA`. The stopped
null `stoppedNull ℱ S` of a null `S` is the set of the stopped laws of its members at all such
stopping times. An adapted process `E` is an
e-process for `S` exactly when `Function.uncurry E` is an e-variable for the stopped null
[KG22, Section 3], with no hypothesis on the null: e-processes are the e-variables of one null on
one measurable space, and the theory of e-variables applies to them. Its closure under `liminf`
gives the closure of e-processes under the time-wise `liminf`, and the quasi-sure filter of the
stopped null is read time by time.

## Main definitions

* `ProbabilityTheory.stoppedNull ℱ S`: the stopped laws of the members of `S` at the stopping
  times that are finite everywhere.

## Main statements

* `ProbabilityTheory.isEProcess_iff_isEVar_stoppedNull`: an adapted process is an e-process
  exactly when it is an e-variable on the space of stopped paths for the stopped null.
* `ProbabilityTheory.eventually_quasiSure_stoppedNull_iff`: a progressive property holds
  quasi-surely for the stopped null exactly when it holds quasi-surely for the null at every time.
* `ProbabilityTheory.isEProcess_liminf`: the time-wise `liminf` of a sequence of e-processes is an
  e-process.

## Implementation notes

The stopped null and its characterization of e-processes are adapted from the file
`notes/lean-wip/StoppedPaths.lean` (commit `c6c6ba8`) of the paper project
`RemyDegenne/evalues_research` (Apache 2.0), which works with a σ-algebra of its own on `ℕ × Ω`;
here it is Tau Ceti's progressive σ-algebra, which in discrete time has the same measurable sets
(`Filtration.measurableSet_progressive_iff_of_countable`).

## References

* [KG22] W. M. Koolen and P. Grünwald, *Log-optimal anytime-valid e-values*, Int. J. Approx.
  Reason. 141 (2022), Section 3.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {S T : Set (Measure Ω)}
  {P : Measure Ω} {τ : Ω → WithTop ℕ} {E : ℕ → Ω → ℝ≥0∞}

/-! ### The stopped null -/

/-- The **stopped null** of a null `S` for a filtration `ℱ` indexed by `ℕ`: the stopped laws
`stoppedLaw ℱ P fun ω ↦ (τ ω).untopA` of the members `P` of `S` at the stopping times `τ` that are
finite everywhere, a null on the space `ℕ × Ω` of stopped paths with the progressive σ-algebra of
`ℱ`. -/
def stoppedNull (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω)) :
    Set (@Measure (ℕ × Ω) ℱ.progressive) :=
  {μ | ∃ P ∈ S, ∃ τ : Ω → WithTop ℕ, IsStoppingTime ℱ τ ∧ (∀ ω, τ ω ≠ ⊤) ∧
    stoppedLaw ℱ P (fun ω ↦ (τ ω).untopA) = μ}

theorem stoppedNull_def (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω)) :
    stoppedNull ℱ S = {μ | ∃ P ∈ S, ∃ τ : Ω → WithTop ℕ, IsStoppingTime ℱ τ ∧ (∀ ω, τ ω ≠ ⊤) ∧
      stoppedLaw ℱ P (fun ω ↦ (τ ω).untopA) = μ} := (rfl)

@[simp]
theorem mem_stoppedNull {μ : @Measure (ℕ × Ω) ℱ.progressive} :
    μ ∈ stoppedNull ℱ S ↔ ∃ P ∈ S, ∃ τ : Ω → WithTop ℕ, IsStoppingTime ℱ τ ∧ (∀ ω, τ ω ≠ ⊤) ∧
      stoppedLaw ℱ P (fun ω ↦ (τ ω).untopA) = μ :=
  Iff.rfl

/-- The stopped law of a member of the null at a stopping time that is finite everywhere is in the
stopped null. -/
theorem stoppedLaw_mem_stoppedNull (hP : P ∈ S) (hτ : IsStoppingTime ℱ τ)
    (hτ_top : ∀ ω, τ ω ≠ ⊤) :
    stoppedLaw ℱ P (fun ω ↦ (τ ω).untopA) ∈ stoppedNull ℱ S :=
  ⟨P, hP, τ, hτ, hτ_top, rfl⟩

@[gcongr]
theorem stoppedNull_mono (hST : S ⊆ T) : stoppedNull ℱ S ⊆ stoppedNull ℱ T := by
  rintro _ ⟨P, hP, τ, hτ, hτ_top, rfl⟩
  exact ⟨P, hST hP, τ, hτ, hτ_top, rfl⟩

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
  obtain ⟨P, hP, τ, -, -, rfl⟩ := hμ
  have := hS P hP
  infer_instance

/-- The stopped laws of a null of measures of mass at most one have mass at most one. -/
theorem measure_univ_le_one_of_mem_stoppedNull (hS : ∀ P ∈ S, P univ ≤ 1)
    {μ : @Measure (ℕ × Ω) ℱ.progressive} (hμ : μ ∈ stoppedNull ℱ S) : μ univ ≤ 1 := by
  obtain ⟨P, hP, τ, hτ, -, rfl⟩ := hμ
  rw [stoppedLaw_univ hτ.measurable'.untopA]
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
    rintro _ ⟨P, hP, τ, hτ, hτ_top, rfl⟩
    rw [lintegral_stoppedLaw hτ.measurable'.untopA hE_meas]
    exact hE.lintegral_le_one hτ hτ_top hP
  · refine .of_lintegral_le_one (Filtration.measurable_uncurry_progressive_iff.1 hE.measurable)
      fun τ hτ N hτN P hP ↦ ?_
    have h := hE.lintegral_le_one (stoppedLaw_mem_stoppedNull hP hτ
      fun ω ↦ ne_top_of_le_ne_top (WithTop.natCast_ne_top N) (hτN ω))
    rwa [lintegral_stoppedLaw hτ.measurable'.untopA hE.measurable] at h

/-- **The quasi-sure filter of the stopped null.** A property of stopped paths given by a
progressive set holds quasi-surely for the stopped null exactly when, at every time `n`, it holds
quasi-surely for the null. In particular a progressive set is polar for the stopped null exactly
when each of its sections is polar for the null. -/
theorem eventually_quasiSure_stoppedNull_iff {p : ℕ × Ω → Prop}
    (hp : MeasurableSet[ℱ.progressive] {x | p x}) :
    (∀ᶠ x in quasiSure (stoppedNull ℱ S), p x) ↔ ∀ n, ∀ᶠ ω in quasiSure S, p (n, ω) := by
  simp only [eventually_quasiSure_iff]
  refine ⟨fun h n P hP ↦ ?_, ?_⟩
  · have h' := h _ (stoppedLaw_mem_stoppedNull hP (isStoppingTime_natCast n)
      fun _ ↦ WithTop.natCast_ne_top n)
    rwa [ae_stoppedLaw_iff measurable_const hp, WithTop.untopA_natCast] at h'
  · rintro h _ ⟨P, hP, τ, hτ, -, rfl⟩
    rw [ae_stoppedLaw_iff hτ.measurable'.untopA hp]
    filter_upwards [ae_all_iff.2 fun n ↦ h n P hP] with ω hω using hω _

/-- **The time-wise `liminf` of e-processes.** For a sequence `E k` of e-processes, the process
`fun n ω ↦ liminf (fun k ↦ E k n ω) atTop` is an e-process. On the stopped paths, this is the
closure of e-variables under `liminf` (Statlib's `isEVar_liminf`) for the stopped null. -/
theorem isEProcess_liminf {E : ℕ → ℕ → Ω → ℝ≥0∞} (hE : ∀ k, IsEProcess (E k) ℱ S) :
    IsEProcess (fun n ω ↦ liminf (fun k ↦ E k n ω) atTop) ℱ S :=
  isEProcess_iff_isEVar_stoppedNull.2
    (isEVar_liminf fun k ↦ isEProcess_iff_isEVar_stoppedNull.1 (hE k))

end ProbabilityTheory
