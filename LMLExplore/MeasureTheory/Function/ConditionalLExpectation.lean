/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalLExpectation

/-!
# Comparison and pasting of conditional Lebesgue expectations

Two facts about Mathlib's conditional expectation `P⁻[X|m]` of an `ℝ≥0∞`-valued function, which
needs no integrability or measurability of `X`:
* it is almost everywhere below an `m`-measurable function `Y` exactly when the set integrals of
  `X` over `m`-measurable sets are below those of `Y`;
* it commutes with pasting two functions along an `m`-measurable set.

The second fact makes the conditional expectations of the values of a process at the stopping
times after a given time a family directed upward, the step behind the Snell envelope of optimal
stopping.

## Main statements

* `MeasureTheory.condLExp_ae_le_iff_forall_setLIntegral_le`: comparison with an `m`-measurable
  function through set integrals.
* `MeasureTheory.condLExp_piecewise`: `P⁻[s.piecewise X Y|m] =ᵐ[P] s.piecewise P⁻[X|m] P⁻[Y|m]`
  for an `m`-measurable set `s`.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : Ω → ℝ≥0∞}

/-- For a sub-σ-algebra `m` on which `P` is σ-finite and an `m`-measurable `Y`, the conditional
expectation `P⁻[X|m]` is almost everywhere below `Y` exactly when the integral of `X` over every
`m`-measurable set is at most that of `Y`. -/
theorem condLExp_ae_le_iff_forall_setLIntegral_le (hm : m ≤ mΩ) [SigmaFinite (P.trim hm)]
    (hY : Measurable[m] Y) :
    P⁻[X|m] ≤ᵐ[P] Y ↔ ∀ s, MeasurableSet[m] s → ∫⁻ ω in s, X ω ∂P ≤ ∫⁻ ω in s, Y ω ∂P := by
  refine ⟨fun h s hs ↦ ?_, fun h ↦ ?_⟩
  · rw [← setLIntegral_condLExp hm P X hs]
    exact lintegral_mono_ae (ae_restrict_of_ae h)
  · refine ae_le_of_ae_le_trim (hm := hm) <| ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (μ := P.trim hm) (measurable_condLExp _ _ _) fun s hs _ ↦ ?_
    rw [setLIntegral_condLExp_trim hm _ _ hs, setLIntegral_trim hm hY hs]
    exact h s hs

/-- The conditional expectation given `m` of two functions pasted along an `m`-measurable set is
almost everywhere the pasting of their conditional expectations. No measurability or
integrability of the functions is needed. -/
theorem condLExp_piecewise (hm : m ≤ mΩ) [SigmaFinite (P.trim hm)] {s : Set Ω}
    [DecidablePred (· ∈ s)] (hs : MeasurableSet[m] s) (X Y : Ω → ℝ≥0∞) :
    P⁻[s.piecewise X Y|m] =ᵐ[P] s.piecewise P⁻[X|m] P⁻[Y|m] := by
  refine (ae_eq_condLExp hm P _
    ((measurable_condLExp m P X).piecewise hs (measurable_condLExp m P Y)) fun t ht ↦ ?_).symm
  have hs' : MeasurableSet s := hm s hs
  have ht' : MeasurableSet t := hm t ht
  -- Split `t` along `s`; on each part both sides reduce to one conditional expectation.
  rw [← lintegral_inter_add_sdiff _ t hs', ← lintegral_inter_add_sdiff (s.piecewise X Y) t hs']
  congr 1
  · calc ∫⁻ ω in t ∩ s, s.piecewise P⁻[X|m] P⁻[Y|m] ω ∂P = ∫⁻ ω in t ∩ s, P⁻[X|m] ω ∂P :=
          setLIntegral_congr_fun (ht'.inter hs') fun ω hω ↦ piecewise_eq_of_mem _ _ _ hω.2
      _ = ∫⁻ ω in t ∩ s, X ω ∂P := setLIntegral_condLExp hm P X (ht.inter hs)
      _ = ∫⁻ ω in t ∩ s, s.piecewise X Y ω ∂P :=
          (setLIntegral_congr_fun (ht'.inter hs') fun ω hω ↦ piecewise_eq_of_mem s X Y hω.2).symm
  · calc ∫⁻ ω in t \ s, s.piecewise P⁻[X|m] P⁻[Y|m] ω ∂P = ∫⁻ ω in t \ s, P⁻[Y|m] ω ∂P :=
          setLIntegral_congr_fun (ht'.diff hs') fun ω hω ↦ piecewise_eq_of_notMem _ _ _ hω.2
      _ = ∫⁻ ω in t \ s, Y ω ∂P := setLIntegral_condLExp hm P Y (ht.diff hs)
      _ = ∫⁻ ω in t \ s, s.piecewise X Y ω ∂P :=
          (setLIntegral_congr_fun (ht'.diff hs') fun ω hω ↦ piecewise_eq_of_notMem s X Y hω.2).symm

end MeasureTheory
