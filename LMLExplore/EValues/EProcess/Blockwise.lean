/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.Basic
public import LMLExplore.Probability.Process.Stopping

/-!
# Blockwise e-processes

A gambler who bets on blocks of observations, rather than on each observation, revises the wealth
only at the ends `t 0 < t 1 < ⋯` of the blocks, for a strictly increasing `t : ℕ → ℕ`. The wealth
is then a *blockwise e-process* [RR26, Definitions 2.3–2.5]: an e-process `E` for the reduced
filtration `ℱ.comp ht.monotone`, whose time `k` is the time `t k` of `ℱ` (Tau Ceti's
`MeasureTheory.Filtration.comp`). Its validity is asked only at the stopping times that take
values among the block ends.

A blockwise e-process is **lifted** to an e-process for `ℱ` by setting it to `0` off the block ends
[RR26, Definition 2.3]: the lifted process `Function.extend t E 0` is `E k` at the time `t k` and
`0` at every other time. A stopping time `τ` of `ℱ` is dominated, in value, by the first block end
after it, a stopping time of the reduced filtration, so the lifted process is an e-process. In
general the value cannot be held between the ends of the blocks instead of being set to `0`: a
gambler who sees the first observations of a block could then stop exactly when they make the bet
on that block look unfavourable.

Conversely, an e-process `E` for `ℱ` **sampled** along a monotone time map `t`, `k ↦ E (t k)`, is an
e-process for the sampled filtration: a stopping time of the sampled filtration is read on the
clock of `ℱ` (`MeasureTheory.IsStoppingTime.map_of_comp`). Lifting and sampling are inverse to each
other, so a process is a blockwise e-process exactly when its lift is an e-process.

## Main statements

* `ProbabilityTheory.IsEProcess.comp`: an e-process sampled along a monotone time map is an
  e-process for the sampled filtration.
* `ProbabilityTheory.IsEProcess.extend`: the lift of a blockwise e-process, `0` off the block ends,
  is an e-process [RR26, Definition 2.3].
* `ProbabilityTheory.isEProcess_extend_iff`: a process is a blockwise e-process exactly when its
  lift is an e-process.

## References

* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1,
  Definitions 2.3–2.5.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {S : Set (Measure Ω)}
  {t : ℕ → ℕ} {E : ℕ → Ω → ℝ≥0∞}

/-- **Sampling an e-process.** For a monotone time map `t`, an e-process `E` for `ℱ`, read at the
times `t k`, is an e-process for the sampled filtration `ℱ.comp ht`, whose time `k` is `ℱ (t k)`.
-/
theorem IsEProcess.comp (hE : IsEProcess E ℱ S) (ht : Monotone t) :
    IsEProcess (fun k ↦ E (t k)) (ℱ.comp ht) S where
  adapted := hE.adapted.comp ht
  isEVar_stoppedValue_of_le κ hκ N hκN := by
    have hκ_top (ω : Ω) : κ ω ≠ ⊤ := WithTop.ne_top_of_le_natCast (hκN ω)
    -- the value at `κ` is the value of `E` at the time `κ` read on the clock of `ℱ`
    have h_eq : stoppedValue (fun k ↦ E (t k)) κ = stoppedValue E fun ω ↦ (κ ω).map t := by
      ext ω
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (hκ_top ω)
      simp [stoppedValue, ← hk]
    rw [h_eq]
    refine hE.isEVar_stoppedValue_of_le (hκ.map_of_comp ht) (N := t N) fun ω ↦ ?_
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (hκ_top ω)
    have hkN : k ≤ N := by
      have := hκN ω
      rwa [← hk, Nat.cast_withTop, WithTop.coe_le_coe] at this
    rw [← hk, WithTop.map_coe, Nat.cast_withTop, WithTop.coe_le_coe]
    exact ht hkN

/-- **Lifting a blockwise e-process** [RR26, Definition 2.3]. For a strictly increasing sequence
`t` of block ends and an e-process `E` for the reduced filtration `ℱ.comp ht.monotone`, whose time
`k` is `ℱ (t k)`, the lifted process `Function.extend t E 0`, equal to `E k` at the time `t k` and
to `0` at every other time, is an e-process for `ℱ`. Its value at a bounded stopping time `τ` of `ℱ`
is at most the value of `E` at the index of the first block end after `τ`, a stopping time of the
reduced filtration. -/
theorem IsEProcess.extend (ht : StrictMono t) (hE : IsEProcess E (ℱ.comp ht.monotone) S) :
    IsEProcess (Function.extend t E 0) ℱ S := by
  refine .of_lintegral_le_one (fun j ↦ ?_) fun τ hτ N hτN P hP ↦ ?_
  · by_cases hj : ∃ k, t k = j
    · obtain ⟨k, rfl⟩ := hj
      rw [ht.injective.extend_apply]
      exact (Filtration.measurable_comp_iff ℱ ht.monotone k).1 (hE.adapted k)
    · rw [Function.extend_apply' _ _ _ hj]
      exact measurable_const
  -- the index of the first block end after `τ`, at most `N` since `τ ≤ N ≤ t N`
  have hex (ω : Ω) : ∃ k, τ ω ≤ t k :=
    ⟨N, (hτN ω).trans (Nat.cast_le.2 (ht.id_le N))⟩
  classical
  set κ : Ω → WithTop ℕ := fun ω ↦ Nat.find (hex ω) with hκ_def
  have hκ_le (ω : Ω) (k : ℕ) : κ ω ≤ k ↔ τ ω ≤ t k := by
    rw [hκ_def, Nat.cast_le, Nat.find_le_iff]
    exact ⟨fun ⟨m, hmk, hm⟩ ↦ hm.trans (Nat.cast_le.2 (ht.monotone hmk)), fun h ↦ ⟨k, le_rfl, h⟩⟩
  have hκ : IsStoppingTime (ℱ.comp ht.monotone) κ := fun k ↦ by
    have h_eq : {ω | κ ω ≤ WithTop.some k} = {ω | τ ω ≤ t k} := by
      ext ω
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← Nat.cast_withTop]
      exact hκ_le ω k
    rw [h_eq]
    exact (Filtration.measurableSet_comp_iff ℱ ht.monotone k).2
      (hτ.measurableSet_le_natCast (t k))
  have hκN (ω : Ω) : κ ω ≤ N := (hκ_le ω N).2 ((hτN ω).trans (Nat.cast_le.2 (ht.id_le N)))
  -- the lifted process at `τ` is at most `E` at `κ`
  refine (lintegral_mono fun ω ↦ ?_).trans
    ((hE.isEVar_stoppedValue_of_le hκ hκN).lintegral_le_one hP)
  simp only [stoppedValue]
  by_cases hj : ∃ k, t k = (τ ω).untopA
  · obtain ⟨k, hk⟩ := hj
    have hτk : τ ω = t k := by
      rw [hk, WithTop.natCast_untopA (WithTop.ne_top_of_le_natCast (hτN ω))]
    have hκk : Nat.find (hex ω) = k := by
      have h := hτk.symm.trans_le (Nat.find_spec (hex ω))
      rw [Nat.cast_le, ht.le_iff_le] at h
      exact le_antisymm (Nat.find_min' _ hτk.le) h
    rw [← hk, ht.injective.extend_apply, hκ_def]
    simp [hκk]
  · rw [Function.extend_apply' _ _ _ hj]
    exact zero_le

/-- **Blockwise e-processes are lifted e-processes.** For a strictly increasing sequence `t` of
block ends, a process `E` is an e-process for the reduced filtration `ℱ.comp ht.monotone` exactly
when its lift `Function.extend t E 0`, equal to `E k` at the time `t k` and to `0` at every other
time, is an e-process for `ℱ`. -/
theorem isEProcess_extend_iff (ht : StrictMono t) :
    IsEProcess (Function.extend t E 0) ℱ S ↔ IsEProcess E (ℱ.comp ht.monotone) S := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.extend ht⟩
  convert h.comp ht.monotone with k
  exact (ht.injective.extend_apply E 0 k).symm

end ProbabilityTheory
