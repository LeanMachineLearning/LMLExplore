/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Process.Progressive
public import LMLExplore.Probability.Process.StoppedValue
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.EIntegral

/-!
# The law of a stopped path

For a filtration `ℱ` indexed by a countable preorder `ι` with measurable singletons, such as `ℕ`,
a measure `P` on `Ω` and a random time `τ : Ω → ι`, the stopped law `stoppedLaw ℱ P τ` is the law
under `P` of the stopped path `ω ↦ (τ ω, ω)`, a measure on the space of stopped paths `ι × Ω` with
the progressive σ-algebra `Filtration.progressive ℱ` [KG22, Section 3]. The measurable functions
on that space are the adapted processes (`Filtration.measurable_uncurry_progressive_iff`), and the
integral of such a process `E` under the stopped law is the integral of its value
`fun ω ↦ E (τ ω) ω` at `τ` (`lintegral_stoppedLaw`). Statements about the values of adapted
processes at random times thus become statements about one function under a family of measures on
one measurable space: e-processes are the e-variables of the stopped laws of a null.

## Main definitions

* `MeasureTheory.stoppedLaw ℱ P τ`: the law of `ω ↦ (τ ω, ω)` under `P`, on `ι × Ω` with the
  progressive σ-algebra of `ℱ`.

## Main statements

* `MeasureTheory.stoppedLaw_apply`, `MeasureTheory.lintegral_stoppedLaw`,
  `MeasureTheory.eintegral_stoppedLaw`, `MeasureTheory.ae_stoppedLaw_iff`: the measure of a
  progressive set, the integrals of a progressive function with values in `ℝ≥0∞` and in `EReal`,
  and the almost-sure properties under a stopped law, at a measurable random time.
* `MeasureTheory.stoppedLaw_univ`: a stopped law has the mass of the measure.
* `MeasureTheory.stoppedLaw_setOf_mem`: under the stopped law at a random time `τ` that is finite
  everywhere, the stopped paths `(n, ω)` with `ω ∈ B n` have the mass of the event `B τ` read at
  `τ` (`MeasureTheory.stoppedEvent`).
* `MeasureTheory.lintegral_sum_smul_stoppedLaw_const`: under the mixture over a measure `ρ` on the
  times of the stopped laws at the constant times, the integral of a progressive function `f` is
  `∑' i, ρ {i} * ∫⁻ ω, f (i, ω) ∂P`; it is a probability measure when `ρ` and `P` are.

## Implementation notes

The stopped paths and their laws are adapted from the file `notes/lean-wip/StoppedPaths.lean`
(commit `c6c6ba8`) of the paper project `RemyDegenne/evalues_research` (Apache 2.0), which works
with a σ-algebra of its own on `ℕ × Ω`; here it is Tau Ceti's progressive σ-algebra, which for a
countable index has the same measurable sets
(`Filtration.measurableSet_progressive_iff_of_countable`), and the index is any countable preorder
with measurable singletons.

## References

* [KG22] W. M. Koolen and P. Grünwald, *Log-optimal anytime-valid e-values*, Int. J. Approx.
  Reason. 141 (2022), Section 3 (the space of stopped paths).
-/

public section

open Set Filter
open scoped ENNReal

namespace MeasureTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι] [MeasurableSpace ι]

/-- The **stopped law** of a measure `P` at a random time `τ`: the law under `P` of the stopped path
`ω ↦ (τ ω, ω)`, a measure on `ι × Ω` with the progressive σ-algebra of the filtration `ℱ`. For a
constant time `i` it is the law of `ω ↦ (i, ω)`, which sees `P` only on `ℱ i`. -/
noncomputable def stoppedLaw (ℱ : Filtration ι mΩ) (P : Measure Ω) (τ : Ω → ι) :
    @Measure (ι × Ω) ℱ.progressive :=
  @Measure.map Ω (ι × Ω) mΩ ℱ.progressive (fun ω ↦ (τ ω, ω)) P

variable {ℱ : Filtration ι mΩ} {P : Measure Ω} {τ : Ω → ι}

theorem stoppedLaw_def :
    stoppedLaw ℱ P τ = @Measure.map Ω (ι × Ω) mΩ ℱ.progressive (fun ω ↦ (τ ω, ω)) P := (rfl)

instance [IsFiniteMeasure P] : IsFiniteMeasure (stoppedLaw ℱ P τ) := by
  rw [stoppedLaw_def]
  infer_instance

instance [IsProbabilityMeasure P] : IsProbabilityMeasure (stoppedLaw ℱ P τ) := by
  rw [stoppedLaw_def]
  infer_instance

instance [SFinite P] : SFinite (stoppedLaw ℱ P τ) := by
  rw [stoppedLaw_def]
  infer_instance

variable [Countable ι] [MeasurableSingletonClass ι]

/-- The measure of a progressive set of stopped paths under a stopped law at a measurable random
time. -/
theorem stoppedLaw_apply (hτ : Measurable τ) {s : Set (ι × Ω)}
    (hs : MeasurableSet[ℱ.progressive] s) :
    stoppedLaw ℱ P τ s = P {ω | (τ ω, ω) ∈ s} :=
  @Measure.map_apply Ω (ι × Ω) mΩ ℱ.progressive P _
    (Filtration.measurable_prodMk_progressive hτ) s hs

/-- A stopped law at a measurable random time has the mass of the measure. -/
@[simp]
theorem stoppedLaw_univ (hτ : Measurable τ) : stoppedLaw ℱ P τ univ = P univ := by
  simp [stoppedLaw_apply hτ (@MeasurableSet.univ _ ℱ.progressive)]

/-- The integral of a progressive function of the stopped path under a stopped law is the integral
of its value at the random time. -/
theorem lintegral_stoppedLaw (hτ : Measurable τ) {f : ι × Ω → ℝ≥0∞}
    (hf : Measurable[ℱ.progressive] f) :
    ∫⁻ x, f x ∂(stoppedLaw ℱ P τ) = ∫⁻ ω, f (τ ω, ω) ∂P :=
  @lintegral_map Ω (ι × Ω) mΩ ℱ.progressive P f _ hf
    (Filtration.measurable_prodMk_progressive hτ)

/-- The extended integral of a progressive `EReal`-valued function of the stopped path under a
stopped law is the extended integral of its value at the random time. -/
theorem eintegral_stoppedLaw (hτ : Measurable τ) {f : ι × Ω → EReal}
    (hf : Measurable[ℱ.progressive] f) :
    ∫ᵉ x, f x ∂(stoppedLaw ℱ P τ) = ∫ᵉ ω, f (τ ω, ω) ∂P :=
  eintegral_map (mβ := ℱ.progressive) hf (Filtration.measurable_prodMk_progressive hτ)

/-- A property of stopped paths given by a progressive set holds almost everywhere under a stopped
law exactly when it holds almost surely at the random time. -/
theorem ae_stoppedLaw_iff (hτ : Measurable τ) {p : ι × Ω → Prop}
    (hp : MeasurableSet[ℱ.progressive] {x | p x}) :
    (∀ᵐ x ∂(stoppedLaw ℱ P τ), p x) ↔ ∀ᵐ ω ∂P, p (τ ω, ω) :=
  ae_map_iff (mβ := ℱ.progressive)
    (@Measurable.aemeasurable Ω (ι × Ω) mΩ ℱ.progressive _ P
      (Filtration.measurable_prodMk_progressive hτ)) hp

/-- **Mixtures over the times.** Under the mixture, with the weights `ρ {i}` of a measure `ρ` on
the times, of the stopped laws of `P` at the constant times `i`, the integral of a progressive
function `f` of the stopped path is `∑' i, ρ {i} * ∫⁻ ω, f (i, ω) ∂P`. -/
theorem lintegral_sum_smul_stoppedLaw_const (ρ : Measure ι) (P : Measure Ω) {f : ι × Ω → ℝ≥0∞}
    (hf : Measurable[ℱ.progressive] f) :
    ∫⁻ x, f x ∂(Measure.sum fun i ↦ ρ {i} • stoppedLaw ℱ P fun _ ↦ i)
      = ∑' i, ρ {i} * ∫⁻ ω, f (i, ω) ∂P := by
  rw [lintegral_sum_measure]
  refine tsum_congr fun i ↦ ?_
  rw [lintegral_smul_measure, smul_eq_mul, lintegral_stoppedLaw measurable_const hf]

/-- The mixture over a probability measure on the times of the stopped laws of a probability
measure at the constant times is a probability measure. -/
instance isProbabilityMeasure_sum_smul_stoppedLaw_const {ρ : Measure ι} [IsProbabilityMeasure ρ]
    {P : Measure Ω} [IsProbabilityMeasure P] :
    IsProbabilityMeasure (Measure.sum fun i ↦ ρ {i} • stoppedLaw ℱ P fun _ ↦ i) := by
  constructor
  have h := lintegral_sum_smul_stoppedLaw_const (ℱ := ℱ) ρ P (f := fun _ ↦ 1)
    (@measurable_const _ _ _ ℱ.progressive _)
  have hρ := lintegral_countable' (μ := ρ) fun _ ↦ 1
  simp only [lintegral_const, measure_univ, mul_one, one_mul] at h hρ
  rw [h, ← hρ]

/-- Under the stopped law at a measurable random time `τ` that is finite everywhere, the set of
stopped paths `(n, ω)` with `ω ∈ B n`, for events `B n` of the filtration, has the mass of the
event `B τ` read at `τ`. -/
theorem stoppedLaw_setOf_mem {ℱ : Filtration ℕ mΩ} {P : Measure Ω} {B : ℕ → Set Ω}
    (hB : ∀ n, MeasurableSet[ℱ n] (B n)) {τ : Ω → WithTop ℕ} (hτ : Measurable τ)
    (hτ_top : ∀ ω, τ ω ≠ ⊤) :
    stoppedLaw ℱ P (fun ω ↦ (τ ω).untopA) {x | x.2 ∈ B x.1} = P (stoppedEvent B τ) := by
  rw [stoppedLaw_apply hτ.untopA
    (Filtration.measurableSet_progressive_iff_of_countable.2 hB),
    stoppedEvent_of_forall_ne_top B hτ_top]
  simp

end MeasureTheory
