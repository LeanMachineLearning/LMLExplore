/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Process.Stopping
public import TauCeti.Probability.Process.StoppedValue

/-!
# The value of a process at a possibly infinite time

The value of a process `M : ι → Ω → ℝ≥0∞` at a time `τ : Ω → WithTop ι` that may be infinite is
given a meaning by taking the `limsup` of `M` where `τ = ⊤` [RRLK; RLKR23, (1.2)]. This is the
limit of the stopped process wherever `M` converges, which is the case almost surely for
`ℝ≥0∞`-valued supermartingales with finite initial expectation under a finite measure.

## Main definitions

* `ProbabilityTheory.stoppedValueLimsup M τ`: the value of `M` at a time `τ : Ω → WithTop ι`,
  with `limsup` at infinity.

## Main statements

* `ProbabilityTheory.tendsto_stoppedProcess_stoppedValueLimsup`: the stopped process converges to
  `stoppedValueLimsup M τ` wherever `τ` is finite and wherever `M` converges.
* `ProbabilityTheory.limsup_stoppedProcess`: `stoppedValueLimsup M τ` is the `limsup` of the
  stopped process.
* `ProbabilityTheory.measurable_stoppedValueLimsup`: measurability at a measurable time.

## References

* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167.
* [RLKR23] J. Ruf, M. Larsson, W. M. Koolen and A. Ramdas, *A composite generalization of Ville's
  martingale theorem using e-processes*, Electron. J. Probab. 28 (2023), arXiv:2203.04485.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section StoppedValueLimsup

variable {ι : Type*} [Nonempty ι] [LinearOrder ι] {M : ι → Ω → ℝ≥0∞} {τ : Ω → WithTop ι}
  {ω : Ω}

/-- The value of a process `M : ι → Ω → ℝ≥0∞` at a time `τ : Ω → WithTop ι`: `M (τ ω) ω` where
`τ ω` is finite and `limsup (M · ω)` where `τ ω = ⊤` [RRLK; RLKR23, (1.2)]. Unlike Mathlib's
`MeasureTheory.stoppedValue`, whose value at `⊤` is arbitrary, it is the limit of the stopped
process wherever `M` converges (`ProbabilityTheory.tendsto_stoppedProcess_stoppedValueLimsup`). -/
noncomputable def stoppedValueLimsup (M : ι → Ω → ℝ≥0∞) (τ : Ω → WithTop ι) (ω : Ω) : ℝ≥0∞ :=
  if τ ω = ⊤ then limsup (fun n ↦ M n ω) atTop else stoppedValue M τ ω

theorem stoppedValueLimsup_of_eq_top (h : τ ω = ⊤) :
    stoppedValueLimsup M τ ω = limsup (fun n ↦ M n ω) atTop := by
  simp [stoppedValueLimsup, h]

theorem stoppedValueLimsup_of_ne_top (h : τ ω ≠ ⊤) :
    stoppedValueLimsup M τ ω = stoppedValue M τ ω := by
  simp [stoppedValueLimsup, h]

theorem stoppedValueLimsup_of_eq_coe {i : ι} (h : τ ω = i) :
    stoppedValueLimsup M τ ω = M i ω := by
  rw [stoppedValueLimsup_of_ne_top (h ▸ WithTop.coe_ne_top), stoppedValue_of_eq h]

/-- `stoppedValueLimsup M τ ω` depends on `τ` only through `τ ω`. -/
theorem stoppedValueLimsup_congr {σ : Ω → WithTop ι} (h : σ ω = τ ω) :
    stoppedValueLimsup M σ ω = stoppedValueLimsup M τ ω := by
  simp [stoppedValueLimsup, stoppedValue, h]

/-- At a time with finite values, `stoppedValueLimsup` is the value of the process. -/
@[simp]
theorem stoppedValueLimsup_coe (M : ι → Ω → ℝ≥0∞) (τ : Ω → ι) :
    stoppedValueLimsup M (fun ω ↦ (τ ω : WithTop ι)) = fun ω ↦ M (τ ω) ω :=
  funext fun _ ↦ stoppedValueLimsup_of_eq_coe rfl

/-- At a constant finite time, `stoppedValueLimsup` is the value of the process. -/
theorem stoppedValueLimsup_const (M : ι → Ω → ℝ≥0∞) (i : ι) :
    stoppedValueLimsup M (fun _ ↦ (i : WithTop ι)) = M i :=
  funext fun _ ↦ stoppedValueLimsup_of_eq_coe rfl

/-- At the time `⊤`, `stoppedValueLimsup` is the `limsup` of the process. -/
@[simp]
theorem stoppedValueLimsup_top (M : ι → Ω → ℝ≥0∞) :
    stoppedValueLimsup M (fun _ ↦ ⊤) = fun ω ↦ limsup (fun n ↦ M n ω) atTop :=
  funext fun _ ↦ stoppedValueLimsup_of_eq_top rfl

/-- The stopped process at a time after `τ ω` is `stoppedValueLimsup M τ ω`. -/
theorem stoppedProcess_eq_stoppedValueLimsup {i : ι} (h : τ ω ≤ i) :
    stoppedProcess M τ i ω = stoppedValueLimsup M τ ω := by
  rw [stoppedProcess_eq_of_ge h, stoppedValueLimsup_of_ne_top (ne_top_of_le_ne_top
    WithTop.coe_ne_top h), stoppedValue]

/-- The stopped process converges to `stoppedValueLimsup M τ` wherever `τ` is finite, and wherever
`M` converges. -/
theorem tendsto_stoppedProcess_stoppedValueLimsup
    (hM : τ ω = ⊤ → Tendsto (fun n ↦ M n ω) atTop (𝓝 (limsup (fun n ↦ M n ω) atTop))) :
    Tendsto (fun n ↦ stoppedProcess M τ n ω) atTop (𝓝 (stoppedValueLimsup M τ ω)) := by
  cases h : τ ω with
  | top =>
    simp_rw [stoppedValueLimsup_of_eq_top h, stoppedProcess_eq_of_le (h ▸ le_top)]
    exact hM h
  | coe k =>
    exact tendsto_atTop_of_eventually_const (i₀ := k) fun n hn ↦
      stoppedProcess_eq_stoppedValueLimsup (h ▸ WithTop.coe_le_coe.2 hn)

/-- `stoppedValueLimsup M τ ω` is the `limsup` of the stopped process. -/
theorem limsup_stoppedProcess (M : ι → Ω → ℝ≥0∞) (τ : Ω → WithTop ι) (ω : Ω) :
    limsup (fun n ↦ stoppedProcess M τ n ω) atTop = stoppedValueLimsup M τ ω := by
  cases h : τ ω with
  | top => simp_rw [stoppedValueLimsup_of_eq_top h, stoppedProcess_eq_of_le (h ▸ le_top)]
  | coe k => exact (tendsto_stoppedProcess_stoppedValueLimsup fun h' ↦ by simp [h] at h').limsup_eq

end StoppedValueLimsup

/-- The value of a measurable process at a measurable time is measurable. -/
theorem measurable_stoppedValueLimsup {M : ℕ → Ω → ℝ≥0∞} {τ : Ω → WithTop ℕ}
    (hM : ∀ n, Measurable (M n)) (hτ : Measurable τ) : Measurable (stoppedValueLimsup M τ) :=
  Measurable.ite (hτ (measurableSet_singleton ⊤)) (Measurable.limsup hM)
    (measurable_stoppedValue_of_countable hM hτ)

end ProbabilityTheory
