/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Martingale.CondEVariable
public import LMLExplore.EValues.EffectiveSet.Basic
public import LMLExplore.EValues.EProcess.Basic
public import LMLExplore.Probability.Process.Adapted
public import LMLExplore.Probability.Process.Stopping
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Closure properties of e-processes

An e-process for a null `S` and a filtration `ℱ` (`ProbabilityTheory.IsEProcess`) is an adapted
`ℝ≥0∞`-valued process whose value at every stopping time with values in `ℕ` is an e-variable for
`S`. This file proves the operations under which e-processes are closed, beyond those of
`LMLExplore.EValues.EProcess.Basic` (restriction of the null, domination, convex combinations):

* **Enlarging the null.** A null and its effective null have the same e-processes; this covers
  every mixture `κ ∘ₘ π` of members of the null over a probability measure. A process is an
  e-process for `S ∪ T` exactly when it is one for `S` and for `T`.
* **Minima.** The minimum of an e-process for `S` and one for `T` is an e-process for `S ∪ T`:
  a statistician who does not know which of two nulls to test can take the smaller evidence.
* **Mixtures.** A mixture `∫⁻ θ, E θ n ω ∂π`, over a probability measure `π`, of a jointly
  measurable family of e-processes is an e-process, with no integrability condition.
* **Time mixtures** [RW, (7.12), Proposition 7.23]. For e-variables `E j` measurable for `ℱ j`,
  such as e-variables computed from the first `j` observations, and weights `w j` of sum at
  most `1`, the nondecreasing process `n ↦ ∑ j ≤ n, w j * E j` is an e-process. This turns a
  sequence of fixed-sample e-variables, which in general is not an e-process, into one.
* **Optional continuation** [RW, Proposition 7.9]. For e-processes `A` and `B` and a stopping
  time `τ` with `1 ≤ B n` whenever `n ≤ τ`, the process `stoppedProcess A τ * B`, which carries
  the evidence `A τ` gathered up to `τ` and continues it with the new experiment `B`, is an
  e-process.

Optional continuation rests on a conditional form of validity: if an e-process `E` is at least `1`
at a stopping time `ρ`, then its value at every later stopping time `σ` is a conditional e-variable
given the σ-algebra at `ρ` (`ProbabilityTheory.IsEProcess.isCondEVar_of_one_le`). It follows from
the validity of `E` at the stopping time equal to `σ` on an event of that σ-algebra and to `ρ`
off it (`MeasureTheory.IsStoppingTime.piecewise_of_stoppingTime_le`).

## Main statements

* `ProbabilityTheory.isEProcess_effectiveSet_iff`: a null and its effective null have the same
  e-processes.
* `ProbabilityTheory.IsEProcess.singleton_comp`: an e-process for a null is one for every mixture
  of its members over a probability measure.
* `ProbabilityTheory.IsEProcess.union`, `ProbabilityTheory.isEProcess_union_iff`: e-processes for
  a union of nulls.
* `ProbabilityTheory.IsEProcess.inf`: the minimum of an e-process for `S` and one for `T` is an
  e-process for `S ∪ T`.
* `ProbabilityTheory.isEProcess_lintegral`: mixtures of e-processes over a probability measure.
* `ProbabilityTheory.isEProcess_sum_mul`: time mixtures of e-variables [RW, Proposition 7.23].
* `ProbabilityTheory.IsEProcess.isCondEVar_of_one_le`: the value of an e-process at a stopping
  time `σ` is a conditional e-variable given the σ-algebra at a stopping time `ρ ≤ σ` at which
  the process is at least `1`.
* `ProbabilityTheory.IsEProcess.stoppedProcess_mul`: optional continuation of e-processes
  [RW, Proposition 7.9].

## Implementation notes

[RW] proves Proposition 7.9 by dominating `B` with a test supermartingale `M` for each member of
the null and multiplying it with the stopped dominating supermartingale of `A`. The supermartingale
inequality of that product at the times `n ≤ τ` uses `M n = 1` there, which domination does not
give. The proof here uses the conditional validity of `B` at the stopping time `min τ σ` instead,
and needs no supermartingale.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, Proposition 7.9, (7.12) and Proposition 7.23.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {S T : Set (Measure Ω)}
  {E F : ℕ → Ω → ℝ≥0∞}

/-! ### Enlarging the null -/

/-- A null and its effective null have the same e-processes, as they have the same e-variables
(Statlib's `isEVar_effectiveSet_iff`). -/
@[simp]
theorem isEProcess_effectiveSet_iff : IsEProcess E ℱ (effectiveSet S) ↔ IsEProcess E ℱ S :=
  ⟨fun hE ↦ hE.anti_set subset_effectiveSet, fun hE ↦
    ⟨hE.adapted, fun τ hτ ↦ isEVar_effectiveSet_iff.2 (hE.isEVar_stoppedValue τ hτ)⟩⟩

/-- **Mixtures of the null.** An e-process for a null is an e-process for every mixture
`κ ∘ₘ π`, over a probability measure `π`, of a kernel with values `π`-almost surely in the
null. -/
theorem IsEProcess.singleton_comp (hE : IsEProcess E ℱ S) {Θ : Type*} {mΘ : MeasurableSpace Θ}
    {π : Measure Θ} [IsProbabilityMeasure π] {κ : Kernel Θ Ω} (hκ : ∀ᵐ θ ∂π, κ θ ∈ S) :
    IsEProcess E ℱ {κ ∘ₘ π} :=
  (isEProcess_effectiveSet_iff.2 hE).anti_set <| singleton_subset_iff.2 <|
    comp_mem_effectiveSet (by simp) (hκ.mono fun _ hθ ↦ subset_effectiveSet hθ)

/-- A process that is an e-process for `S` and for `T` is an e-process for `S ∪ T`. -/
theorem IsEProcess.union (hS : IsEProcess E ℱ S) (hT : IsEProcess E ℱ T) :
    IsEProcess E ℱ (S ∪ T) :=
  ⟨hS.adapted, fun τ hτ ↦ (hS.isEVar_stoppedValue τ hτ).union (hT.isEVar_stoppedValue τ hτ)⟩

/-- A process is an e-process for `S ∪ T` exactly when it is one for `S` and for `T`. -/
theorem isEProcess_union_iff : IsEProcess E ℱ (S ∪ T) ↔ IsEProcess E ℱ S ∧ IsEProcess E ℱ T :=
  ⟨fun h ↦ ⟨h.anti_set subset_union_left, h.anti_set subset_union_right⟩,
    fun h ↦ h.1.union h.2⟩

/-! ### Minima -/

/-- **Minima of e-processes.** The minimum of an e-process for `S` and an e-process for `T` is an
e-process for `S ∪ T`. -/
theorem IsEProcess.inf (hE : IsEProcess E ℱ S) (hF : IsEProcess F ℱ T) :
    IsEProcess (E ⊓ F) ℱ (S ∪ T) := by
  have hEF : Adapted ℱ (E ⊓ F) := fun n ↦ (hE.adapted n).min (hF.adapted n)
  exact (hE.mono hEF inf_le_left).union (hF.mono hEF inf_le_right)

/-! ### Mixtures -/

/-- **Mixtures of e-processes.** For a probability measure `π` and a family `E θ` of e-processes
for a null of finite measures, jointly measurable in `(θ, ω)` for `ℱ n` at every time `n`, the
mixture `∫⁻ θ, E θ n ω ∂π` is an e-process. No integrability is needed. -/
theorem isEProcess_lintegral {Θ : Type*} {mΘ : MeasurableSpace Θ} {π : Measure Θ}
    [IsProbabilityMeasure π] {E : Θ → ℕ → Ω → ℝ≥0∞} (hS : ∀ P ∈ S, IsFiniteMeasure P)
    (hE_meas : ∀ n, Measurable[mΘ.prod (ℱ n)] fun p : Θ × Ω ↦ E p.1 n p.2)
    (hE : ∀ θ, IsEProcess (E θ) ℱ S) :
    IsEProcess (fun n ω ↦ ∫⁻ θ, E θ n ω ∂π) ℱ S := by
  have hM := adapted_lintegral (π := π) hE_meas
  refine ⟨hM, fun τ hτ ↦ ⟨hM.measurable_apply_stoppingTime hτ, fun P hP ↦ ?_⟩⟩
  have := hS P hP
  -- the value at `τ` is jointly measurable, since `τ` takes countably many values
  have h_meas : Measurable fun q : Ω × Θ ↦ E q.2 (τ q.1) q.1 :=
    measurable_apply_of_countable (u := fun n (q : Ω × Θ) ↦ E q.2 n q.1)
      (fun n ↦ ((hE_meas n).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le n)) le_rfl).comp
        measurable_swap) (hτ.measurable_nat.comp measurable_fst)
  calc ∫⁻ ω, ∫⁻ θ, E θ (τ ω) ω ∂π ∂P
  _ = ∫⁻ θ, ∫⁻ ω, E θ (τ ω) ω ∂P ∂π := lintegral_lintegral_swap h_meas.aemeasurable
  _ ≤ ∫⁻ _, 1 ∂π := lintegral_mono fun θ ↦ ((hE θ).isEVar_stoppedValue τ hτ).lintegral_le_one hP
  _ = 1 := by simp

/-- **Time mixtures of e-variables** [RW, (7.12), Proposition 7.23]. For e-variables `E j` that
are `ℱ j`-measurable, and weights `w j` with `∑' j, w j ≤ 1`, the nondecreasing process
`n ↦ ∑ j ≤ n, w j * E j` is an e-process. -/
theorem isEProcess_sum_mul (hE_meas : ∀ j, Measurable[ℱ j] (E j)) (hE : ∀ j, IsEVar (E j) S)
    {w : ℕ → ℝ≥0∞}
    (hw : ∑' j, w j ≤ 1) :
    IsEProcess (fun n ω ↦ ∑ j ∈ Finset.Iic n, w j * E j ω) ℱ S := by
  have hM : Adapted ℱ (fun n ω ↦ ∑ j ∈ Finset.Iic n, w j * E j ω) := fun n ↦
    Finset.measurable_fun_sum _ fun j hj ↦
      ((hE_meas j).mono (ℱ.mono (Finset.mem_Iic.1 hj)) le_rfl).const_mul (w j)
  -- at every time, the process is at most the e-variable `∑' j, w j * E j`
  exact ⟨hM, fun τ hτ ↦ (isEVar_tsum_mul hE hw).mono (hM.measurable_apply_stoppingTime hτ)
    fun ω ↦ sum_le_tsum _⟩

/-! ### Conditional validity and optional continuation -/

/-- **Conditional validity of e-processes.** For a null of probability measures, an e-process `E`
and stopping times `ρ ≤ σ` with values in `ℕ` such that `1 ≤ E (ρ ω) ω` for every `ω`, the value
`fun ω ↦ E (σ ω) ω` at `σ` is a conditional e-variable given the σ-algebra at `ρ`. -/
theorem IsEProcess.isCondEVar_of_one_le (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hE : IsEProcess E ℱ S) {ρ σ : Ω → ℕ} (hρ : IsStoppingTime ℱ fun ω ↦ (ρ ω : WithTop ℕ))
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℕ)) (hρσ : ρ ≤ σ)
    (hE1 : ∀ ω, 1 ≤ E (ρ ω) ω) :
    IsCondEVar (fun ω ↦ E (σ ω) ω) hρ.measurableSpace S := by
  classical
  refine ⟨hE.measurable_stoppedValue hσ, fun P hP s hs ↦ ?_⟩
  have := hS P hP
  have hs' : MeasurableSet s := hρ.measurableSpace_le s hs
  -- the time equal to `σ` on `s` and to `ρ` off `s` is a stopping time
  have hσs : IsStoppingTime ℱ fun ω ↦ (s.piecewise σ ρ ω : WithTop ℕ) := by
    have h := hσ.piecewise_of_stoppingTime_le hρ hρ (fun ω ↦ WithTop.coe_le_coe.2 (hρσ ω))
      (fun _ ↦ le_rfl) hs
    rwa [piecewise_op (h := fun _ (n : ℕ) ↦ (n : WithTop ℕ))] at h
  -- validity at that time, split into `s`, where it reads `E σ`, and `sᶜ`, where `1 ≤ E ρ`
  refine (ENNReal.add_le_add_iff_right (measure_ne_top P sᶜ)).1 ?_
  calc ∫⁻ ω in s, E (σ ω) ω ∂P + P sᶜ
  _ ≤ ∫⁻ ω in s, E (σ ω) ω ∂P + ∫⁻ ω in sᶜ, E (ρ ω) ω ∂P := by
    gcongr
    exact (setLIntegral_one sᶜ).symm.trans_le (lintegral_mono hE1)
  _ = ∫⁻ ω, E (s.piecewise σ ρ ω) ω ∂P := by
    rw [← lintegral_add_compl (fun ω ↦ E (s.piecewise σ ρ ω) ω) hs']
    congr 1
    · refine setLIntegral_congr_fun hs' fun ω hω ↦ ?_
      rw [piecewise_eq_of_mem _ _ _ hω]
    · refine setLIntegral_congr_fun hs'.compl fun ω hω ↦ ?_
      rw [piecewise_eq_of_notMem _ _ _ hω]
  _ ≤ 1 := (hE.isEVar_stoppedValue _ hσs).lintegral_le_one hP
  _ = P s + P sᶜ := by rw [measure_add_measure_compl hs', measure_univ]

/-- **Optional continuation of e-processes** [RW, Proposition 7.9]. For a null of probability
measures, e-processes `A` and `B` and a stopping time `τ` such that `1 ≤ B n` whenever `n ≤ τ`, the
process `stoppedProcess A τ * B`, equal to `A n * B n` (so at least `A n`) up to `τ` and to
`A τ * B n` after it, is an e-process. -/
theorem IsEProcess.stoppedProcess_mul (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    {A B : ℕ → Ω → ℝ≥0∞} (hA : IsEProcess A ℱ S) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ)
    (hB : IsEProcess B ℱ S) (hB1 : ∀ (n : ℕ) ω, (n : WithTop ℕ) ≤ τ ω → 1 ≤ B n ω) :
    IsEProcess (stoppedProcess A τ * B) ℱ S := by
  have hM : Adapted ℱ (stoppedProcess A τ * B) :=
    (hA.adapted.stoppedProcess_of_discrete hτ).mul hB.adapted
  refine ⟨hM, fun σ hσ ↦ ⟨hM.measurable_apply_stoppingTime hσ, fun P hP ↦ ?_⟩⟩
  -- `ρ = min σ τ`, the time at which `A` is read, with values in `ℕ`
  have hmin_ne (ω : Ω) : min (σ ω : WithTop ℕ) (τ ω) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : Ω → ℕ, ∀ ω, ρ ω = (min (σ ω : WithTop ℕ) (τ ω)).untopA :=
    ⟨_, fun _ ↦ rfl⟩
  have hρ_coe (ω : Ω) : (ρ ω : WithTop ℕ) = min (σ ω : WithTop ℕ) (τ ω) := by
    rw [hρ_def, WithTop.natCast_untopA (hmin_ne ω)]
  have hρ : IsStoppingTime ℱ fun ω ↦ (ρ ω : WithTop ℕ) := by
    simp_rw [hρ_coe]
    exact hσ.min hτ
  have hρσ : ρ ≤ σ := fun ω ↦ WithTop.coe_le_coe.1 ((hρ_coe ω).trans_le (min_le_left _ _))
  have hB_cond : IsCondEVar (fun ω ↦ B (σ ω) ω) hρ.measurableSpace S :=
    hB.isCondEVar_of_one_le hS hρ hσ hρσ fun ω ↦
      hB1 _ ω ((hρ_coe ω).trans_le (min_le_right _ _))
  -- the value of `A` read at `ρ` is known at `ρ`
  have hAρ : Measurable[hρ.measurableSpace] fun ω ↦ A (ρ ω) ω :=
    hA.adapted.measurable_measurableSpace_apply_stoppingTime hρ
  -- the value at `σ` is `A ρ * B σ`
  have h_eq : (fun ω ↦ (stoppedProcess A τ * B) (σ ω) ω) =
      fun ω ↦ A (ρ ω) ω * B (σ ω) ω := by
    ext ω
    simp only [Pi.mul_apply]
    rw [stoppedProcess_eq_stoppedValue_apply, stoppedValue, hρ_def, Nat.cast_withTop]
  rw [h_eq]
  exact (hB_cond.lintegral_mul_le (hρ.measurableSpace_le) hP hAρ).trans
    ((hA.isEVar_stoppedValue ρ hρ).lintegral_le_one hP)

end ProbabilityTheory
