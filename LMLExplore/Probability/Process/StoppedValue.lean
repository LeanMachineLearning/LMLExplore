/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Probability.Process.Stopping

/-!
# The value of a process at a possibly infinite time

A random time of a filtration indexed by `ℕ` takes values in `WithTop ℕ`. Mathlib's
`MeasureTheory.stoppedValue u τ` reads the process at `τ ω` where it is finite and takes an
arbitrary value where `τ ω = ⊤`. Anytime-valid inference needs a canonical value at infinity: the
value of a process at a possibly infinite stopping time is `u (τ ω) ω` where `τ ω` is finite and
`limsup (u · ω)` where it is infinite [RRLK; RLKR23, (1.2)]. For nonnegative supermartingales with
finite initial expectation, which converge almost surely, this is the almost sure limit, and
optional stopping holds at every stopping time with this convention.

## Main definitions

* `MeasureTheory.stoppedValueLimsup u τ`: the value of `u` at the random time `τ`, with
  `limsup (u · ω)` where `τ ω = ⊤`.

## Main statements

* `MeasureTheory.stoppedValueLimsup_of_eq_natCast`, `MeasureTheory.stoppedValueLimsup_of_eq_top`:
  its values at finite and infinite times.
* `MeasureTheory.stoppedValueLimsup_natCast`: at an `ℕ`-valued random time it reads the process at
  that time.
* `MeasureTheory.stoppedValueLimsup_eq_stoppedValue`: where `τ` is finite it agrees with Mathlib's
  `stoppedValue`.
* `MeasureTheory.tendsto_stoppedValueLimsup_min`: for a convergent process, the values at the
  truncated times `min τ N` converge to the value at `τ`.
* `MeasureTheory.measurable_stoppedValueLimsup`: it is measurable for measurable `u n` and `τ`.

## References

* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167.
* [RLKR23] J. Ruf, M. Larsson, W. M. Koolen and A. Ramdas, *A composite generalization of Ville's
  martingale theorem using e-processes*, Electron. J. Probab. 28 (2023), arXiv:2203.04485.
-/

public section

open Filter Topology

namespace MeasureTheory

variable {Ω β : Type*} {τ : Ω → WithTop ℕ} {ω : Ω}

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice β] {u : ℕ → Ω → β}

/-- The value of the process `u` at the random time `τ : Ω → WithTop ℕ`: `u n ω` where
`τ ω = n`, and `limsup (u · ω)` where `τ ω = ⊤` [RRLK; RLKR23, (1.2)]. Unlike Mathlib's
`stoppedValue`, its value at infinity is meaningful: for an almost surely convergent process it is
the limit. -/
noncomputable def stoppedValueLimsup (u : ℕ → Ω → β) (τ : Ω → WithTop ℕ) (ω : Ω) : β :=
  if τ ω = ⊤ then limsup (fun n ↦ u n ω) atTop else u (τ ω).untopA ω

/-- Where the random time is finite, `stoppedValueLimsup` reads the process at that time. -/
theorem stoppedValueLimsup_of_eq_natCast {n : ℕ} (h : τ ω = n) :
    stoppedValueLimsup u τ ω = u n ω := by
  simp only [stoppedValueLimsup, h, WithTop.natCast_ne_top, ↓reduceIte]
  -- `Nat.cast` into `WithTop ℕ` is `WithTop.some`, which `untop` inverts.
  rw [WithTop.untopA_eq_untop (WithTop.natCast_ne_top n),
    (WithTop.untop_eq_iff _).2 (Nat.cast_withTop n)]

/-- Where the random time is infinite, `stoppedValueLimsup` is the `limsup` of the process. -/
theorem stoppedValueLimsup_of_eq_top (h : τ ω = ⊤) :
    stoppedValueLimsup u τ ω = limsup (fun n ↦ u n ω) atTop := by
  simp [stoppedValueLimsup, h]

/-- The value of a process at a random time at `ω` depends only on the time at `ω`. -/
theorem stoppedValueLimsup_congr {τ' : Ω → WithTop ℕ} (h : τ ω = τ' ω) :
    stoppedValueLimsup u τ ω = stoppedValueLimsup u τ' ω := by
  simp only [stoppedValueLimsup, h]

/-- At a finite random time, the coercion of an `ℕ`-valued one, `stoppedValueLimsup` reads the
process at that time. -/
@[simp]
theorem stoppedValueLimsup_natCast (u : ℕ → Ω → β) (τ : Ω → ℕ) :
    stoppedValueLimsup u (fun ω ↦ (τ ω : WithTop ℕ)) = fun ω ↦ u (τ ω) ω :=
  funext fun _ ↦ stoppedValueLimsup_of_eq_natCast rfl

/-- At a constant finite time, `stoppedValueLimsup` is the process at that time. -/
theorem stoppedValueLimsup_const (u : ℕ → Ω → β) (n : ℕ) :
    stoppedValueLimsup u (fun _ ↦ (n : WithTop ℕ)) = u n :=
  stoppedValueLimsup_natCast u fun _ ↦ n

/-- At the constant time `⊤`, `stoppedValueLimsup` is the `limsup` of the process. -/
@[simp]
theorem stoppedValueLimsup_top (u : ℕ → Ω → β) :
    stoppedValueLimsup u (fun _ ↦ ⊤) = fun ω ↦ limsup (fun n ↦ u n ω) atTop :=
  funext fun _ ↦ stoppedValueLimsup_of_eq_top rfl

/-- Where the random time is finite, `stoppedValueLimsup` agrees with Mathlib's `stoppedValue`. -/
theorem stoppedValueLimsup_eq_stoppedValue (h : τ ω ≠ ⊤) :
    stoppedValueLimsup u τ ω = stoppedValue u τ ω := by
  simp [stoppedValueLimsup, stoppedValue, h]

/-- For a process that converges at `ω` (to its `limsup`), the values at the truncated times
`min τ N` converge to the value at `τ`. -/
theorem tendsto_stoppedValueLimsup_min [TopologicalSpace β]
    (h : Tendsto (fun n ↦ u n ω) atTop (𝓝 (limsup (fun n ↦ u n ω) atTop))) :
    Tendsto (fun N : ℕ ↦ stoppedValueLimsup u (fun ω ↦ min (τ ω) N) ω) atTop
      (𝓝 (stoppedValueLimsup u τ ω)) := by
  induction hτω : τ ω using WithTop.recTopCoe with
  | top =>
    rw [stoppedValueLimsup_of_eq_top hτω]
    exact h.congr fun N ↦ (stoppedValueLimsup_of_eq_natCast (by simp [hτω])).symm
  | coe b =>
    rw [← Nat.cast_withTop] at hτω
    rw [stoppedValueLimsup_of_eq_natCast hτω]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop b] with N hN
    refine (stoppedValueLimsup_of_eq_natCast ?_).symm
    rw [hτω, min_eq_left (by exact_mod_cast hN)]

end ConditionallyCompleteLattice

/-- The value of a process of measurable functions at a measurable random time is measurable. -/
theorem measurable_stoppedValueLimsup [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
    [OrderTopology β] [SecondCountableTopology β] [MeasurableSpace β] [BorelSpace β]
    {mΩ : MeasurableSpace Ω} {u : ℕ → Ω → β} (hu : ∀ n, Measurable (u n)) (hτ : Measurable τ) :
    Measurable (stoppedValueLimsup u τ) := by
  have h : Measurable fun p : Ω × WithTop ℕ ↦ stoppedValueLimsup u (fun _ ↦ p.2) p.1 := by
    refine measurable_from_prod_countable_left fun k ↦ ?_
    cases k with
    | top => simpa using Measurable.limsup hu
    | coe n => simpa using hu n
  exact h.comp (measurable_id.prodMk hτ)

end MeasureTheory
