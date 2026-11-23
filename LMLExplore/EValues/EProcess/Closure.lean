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
`ℝ≥0∞`-valued process whose value at every bounded stopping time is an e-variable for `S`. This
file proves the operations under which e-processes are closed, beyond those of
`LMLExplore.EValues.EProcess.Basic` (restriction of the null, domination, convex combinations):

* **Enlarging the null.** A null and its effective null have the same e-processes; this covers
  every mixture `κ ∘ₘ π` of members of the null over a probability measure. A process is an
  e-process for `S ∪ T` exactly when it is one for `S` and for `T`.
* **Minima.** The minimum of an e-process for `S` and one for `T` is an e-process for `S ∪ T`:
  a statistician who does not know which of two nulls to test can take the smaller evidence.
* **Mixtures.** A mixture `∫⁻ θ, E θ n ω ∂π`, over a probability measure `π`, of a jointly
  measurable family of e-processes is an e-process, with no integrability condition.
* **Countable mixtures.** A combination `∑' i, w i * E i n ω` of countably many e-processes with
  weights of sum at most `1` is an e-process, for every null.
* **Mixtures of held bets.** For a countable family of e-variables `E i`, each measurable at a
  time `t i`, and weights `w i` of sum at most `1`, the process that holds each bet `w i * E i`
  from its time `t i` on is an e-process. The case `t = id` is the **time mixture**
  [RW, (7.12), Proposition 7.23]: for e-variables `E j` measurable for `ℱ j`, such as
  e-variables computed from the first `j` observations, the nondecreasing process
  `n ↦ ∑ j ≤ n, w j * E j` is an e-process. This turns a sequence of fixed-sample e-variables,
  which in general is not an e-process, into one.
* **Optional continuation** [RW, Proposition 7.9]. For e-processes `A` and `B` and a stopping
  time `τ` with `1 ≤ B n` whenever `n ≤ τ`, the process `stoppedProcess A τ * B`, which carries
  the evidence `A τ` gathered up to `τ` and continues it with the new experiment `B`, is an
  e-process.

Optional continuation rests on a conditional form of validity: if an e-process `E` is at least `1`
at a stopping time `ρ`, then its value at every later stopping time `σ` that is finite everywhere
is a conditional e-variable given the σ-algebra at `ρ`
(`ProbabilityTheory.IsEProcess.isCondEVar_of_one_le`). It follows from the validity of `E` at the
stopping time equal to `σ` on an event of that σ-algebra and to `ρ` off it
(`MeasureTheory.IsStoppingTime.piecewise_of_stoppingTime_le`).

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
* `ProbabilityTheory.isEProcess_tsum_mul`: countable mixtures of e-processes.
* `ProbabilityTheory.isEProcess_tsum_ite_le_mul`: countable mixtures of held bets.
* `ProbabilityTheory.isEProcess_sum_mul`: time mixtures of e-variables [RW, Proposition 7.23].
* `ProbabilityTheory.IsEProcess.isCondEVar_of_one_le`: the value of an e-process at a stopping
  time `σ` that is finite everywhere is a conditional e-variable given the σ-algebra at a stopping
  time `ρ ≤ σ` at which the process is at least `1`.
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
    ⟨hE.adapted, fun _ hτ _ hτN ↦ isEVar_effectiveSet_iff.2 (hE.isEVar_stoppedValue_of_le hτ hτN)⟩⟩

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
  ⟨hS.adapted, fun _ hτ _ hτN ↦
    (hS.isEVar_stoppedValue_of_le hτ hτN).union (hT.isEVar_stoppedValue_of_le hτ hτN)⟩

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
  refine .of_lintegral_le_one hM fun τ hτ N hτN P hP ↦ ?_
  have := hS P hP
  -- the value at `τ` is jointly measurable, since `τ` takes countably many values
  have h_meas : Measurable fun q : Ω × Θ ↦ stoppedValue (E q.2) τ q.1 :=
    measurable_apply_of_countable (u := fun n (q : Ω × Θ) ↦ E q.2 n q.1)
      (fun n ↦ ((hE_meas n).mono (MeasurableSpace.prod_mono le_rfl (ℱ.le n)) le_rfl).comp
        measurable_swap) (hτ.measurable'.untopA.comp measurable_fst)
  calc ∫⁻ ω, stoppedValue (fun n ω ↦ ∫⁻ θ, E θ n ω ∂π) τ ω ∂P
  _ = ∫⁻ θ, ∫⁻ ω, stoppedValue (E θ) τ ω ∂P ∂π := lintegral_lintegral_swap h_meas.aemeasurable
  _ ≤ ∫⁻ _, 1 ∂π := lintegral_mono fun θ ↦
    ((hE θ).isEVar_stoppedValue_of_le hτ hτN).lintegral_le_one hP
  _ = 1 := by simp

/-- **Countable mixtures of e-processes.** For e-processes `E i` indexed by a countable type and
weights `w i` of sum at most `1`, the process `∑' i, w i * E i n ω` is an e-process. Unlike
`ProbabilityTheory.isEProcess_lintegral`, this needs no finiteness of the members of the null. -/
theorem isEProcess_tsum_mul {ι : Type*} [Countable ι] {E : ι → ℕ → Ω → ℝ≥0∞}
    (hE : ∀ i, IsEProcess (E i) ℱ S) {w : ι → ℝ≥0∞} (hw : ∑' i, w i ≤ 1) :
    IsEProcess (fun n ω ↦ ∑' i, w i * E i n ω) ℱ S :=
  -- `Measurable.tsum` takes the σ-algebra as an anonymous instance, so `ℱ n` is installed as one
  ⟨fun n ↦ letI := ℱ n; Measurable.tsum fun i ↦ ((hE i).adapted n).const_mul (w i),
    fun _ hτ _ hτN ↦ isEVar_tsum_mul (fun i ↦ (hE i).isEVar_stoppedValue_of_le hτ hτN) hw⟩

/-- **Mixtures of held bets.** For a countable family of e-variables `E i`, each measurable at a
time `t i` of the filtration, and weights `w i` with `∑' i, w i ≤ 1`, the process that holds each
weighted bet `w i * E i` from its time `t i` on, `n ↦ ∑' i, if t i ≤ n then w i * E i else 0`, is
an e-process: its value at every time is at most the e-variable `∑' i, w i * E i`. -/
theorem isEProcess_tsum_ite_le_mul {ι : Type*} [Countable ι] {t : ι → ℕ}
    {E : ι → Ω → ℝ≥0∞} (hE_meas : ∀ i, Measurable[ℱ (t i)] (E i)) (hE : ∀ i, IsEVar (E i) S)
    {w : ι → ℝ≥0∞} (hw : ∑' i, w i ≤ 1) :
    IsEProcess (fun n ω ↦ ∑' i, if t i ≤ n then w i * E i ω else 0) ℱ S := by
  have hM : Adapted ℱ (fun n ω ↦ ∑' i, if t i ≤ n then w i * E i ω else 0) := by
    intro n
    -- the sum is measurable for the σ-algebra `ℱ n`, made the instance
    let _ : MeasurableSpace Ω := ℱ n
    refine Measurable.tsum fun i ↦ ?_
    split_ifs with h
    · exact ((hE_meas i).mono (ℱ.mono h) le_rfl).const_mul (w i)
    · exact measurable_const
  refine ⟨hM, fun τ hτ _ _ ↦ (isEVar_tsum_mul hE hw).mono
    (measurable_stoppedValue_of_countable (fun _ ↦ hM.measurable) hτ.measurable')
    fun ω ↦ tsum_le_tsum fun i ↦ ?_⟩
  split_ifs
  exacts [le_rfl, zero_le]

/-- **Time mixtures of e-variables** [RW, (7.12), Proposition 7.23]. For e-variables `E j` that
are `ℱ j`-measurable, and weights `w j` with `∑' j, w j ≤ 1`, the nondecreasing process
`n ↦ ∑ j ≤ n, w j * E j` is an e-process: the mixture of the bets `E j` held from time `j` on
(`ProbabilityTheory.isEProcess_tsum_ite_le_mul`). -/
theorem isEProcess_sum_mul (hE_meas : ∀ j, Measurable[ℱ j] (E j)) (hE : ∀ j, IsEVar (E j) S)
    {w : ℕ → ℝ≥0∞}
    (hw : ∑' j, w j ≤ 1) :
    IsEProcess (fun n ω ↦ ∑ j ∈ Finset.Iic n, w j * E j ω) ℱ S := by
  convert isEProcess_tsum_ite_le_mul (t := id) hE_meas hE hw using 3 with n ω
  simp only [id]
  rw [tsum_eq_sum (s := Finset.Iic n) fun j hj ↦ ite_eq_right_iff.2 fun h ↦
    absurd (Finset.mem_Iic.2 h) hj, Finset.sum_ite_of_true fun j hj ↦ Finset.mem_Iic.1 hj]

/-! ### Conditional validity and optional continuation -/

/-- **Conditional validity of e-processes.** For a null of probability measures, an e-process `E`
and stopping times `ρ ≤ σ`, with `σ` finite everywhere, such that `1 ≤ stoppedValue E ρ ω` for
every `ω`, the value `stoppedValue E σ` at `σ` is a conditional e-variable given the σ-algebra at
`ρ`. -/
theorem IsEProcess.isCondEVar_of_one_le (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hE : IsEProcess E ℱ S) {ρ σ : Ω → WithTop ℕ} (hρ : IsStoppingTime ℱ ρ)
    (hσ : IsStoppingTime ℱ σ) (hσ_top : ∀ ω, σ ω ≠ ⊤) (hρσ : ρ ≤ σ)
    (hE1 : ∀ ω, 1 ≤ stoppedValue E ρ ω) :
    IsCondEVar (stoppedValue E σ) hρ.measurableSpace S := by
  classical
  refine ⟨hE.measurable_stoppedValue hσ, fun P hP s hs ↦ ?_⟩
  have := hS P hP
  have hs' : MeasurableSet s := hρ.measurableSpace_le s hs
  -- the time equal to `σ` on `s` and to `ρ` off `s` is a stopping time, finite everywhere
  have hσs : IsStoppingTime ℱ (s.piecewise σ ρ) :=
    hσ.piecewise_of_stoppingTime_le hρ hρ hρσ (fun _ ↦ le_rfl) hs
  have hσs_top (ω : Ω) : s.piecewise σ ρ ω ≠ ⊤ := by
    by_cases hω : ω ∈ s
    · rw [piecewise_eq_of_mem _ _ _ hω]
      exact hσ_top ω
    · rw [piecewise_eq_of_notMem _ _ _ hω]
      exact ne_top_of_le_ne_top (hσ_top ω) (hρσ ω)
  -- validity at that time, split into `s`, where it reads `E σ`, and `sᶜ`, where `1 ≤ E ρ`
  refine (ENNReal.add_le_add_iff_right (measure_ne_top P sᶜ)).1 ?_
  calc ∫⁻ ω in s, stoppedValue E σ ω ∂P + P sᶜ
  _ ≤ ∫⁻ ω in s, stoppedValue E σ ω ∂P + ∫⁻ ω in sᶜ, stoppedValue E ρ ω ∂P := by
    gcongr
    exact (setLIntegral_one sᶜ).symm.trans_le (lintegral_mono hE1)
  _ = ∫⁻ ω, stoppedValue E (s.piecewise σ ρ) ω ∂P := by
    rw [← lintegral_add_compl (stoppedValue E (s.piecewise σ ρ)) hs']
    congr 1
    · refine setLIntegral_congr_fun hs' fun ω hω ↦ ?_
      exact stoppedValue_congr (piecewise_eq_of_mem _ _ _ hω).symm
    · refine setLIntegral_congr_fun hs'.compl fun ω hω ↦ ?_
      exact stoppedValue_congr (piecewise_eq_of_notMem _ _ _ hω).symm
  _ ≤ 1 := (hE.isEVar_stoppedValue hσs hσs_top).lintegral_le_one hP
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
  refine .of_lintegral_le_one hM fun σ hσ N hσN P hP ↦ ?_
  have hσ_top (ω : Ω) : σ ω ≠ ⊤ := WithTop.ne_top_of_le_natCast (hσN ω)
  -- `ρ = min σ τ`, the time at which `A` is read
  set ρ : Ω → WithTop ℕ := fun ω ↦ min (σ ω) (τ ω) with hρ_def
  have hρ : IsStoppingTime ℱ ρ := hσ.min hτ
  have hρ_top (ω : Ω) : ρ ω ≠ ⊤ := ne_top_of_le_ne_top (hσ_top ω) (min_le_left _ _)
  have hB_cond : IsCondEVar (stoppedValue B σ) hρ.measurableSpace S :=
    hB.isCondEVar_of_one_le hS hρ hσ hσ_top (fun ω ↦ min_le_left _ _) fun ω ↦
      hB1 _ ω ((WithTop.natCast_untopA (hρ_top ω)).trans_le (min_le_right _ _))
  -- the value of `A` read at `ρ` is known at `ρ`
  have hAρ : Measurable[hρ.measurableSpace] (stoppedValue A ρ) :=
    hA.adapted.measurable_stoppedValue hρ
  -- the value at `σ` is `A ρ * B σ`
  have h_eq : stoppedValue (stoppedProcess A τ * B) σ =
      fun ω ↦ stoppedValue A ρ ω * stoppedValue B σ ω := by
    ext ω
    rw [stoppedValue_mul, Pi.mul_apply, stoppedValue_stoppedProcess_apply (hσ_top ω)]
  rw [h_eq]
  exact (hB_cond.lintegral_mul_le (hρ.measurableSpace_le) hP hAρ).trans
    ((hA.isEVar_stoppedValue hρ hρ_top).lintegral_le_one hP)

end ProbabilityTheory
