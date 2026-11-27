/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import TauCeti.Topology.Semicontinuity.Sequences

/-!
# Sequential and topological lower semicontinuity at a point

Tau Ceti's `TauCeti.SeqLowerSemicontinuousWithinAt f s x` asks that `y < f (u n)` eventually, for
every `y < f x` and every sequence `u` in `s` that converges to `x`. Lower semicontinuity implies
it (`LowerSemicontinuousWithinAt.seqLowerSemicontinuousWithinAt`), and on a sequential space the
global notions agree (`TauCeti.seqLowerSemicontinuous_iff_lowerSemicontinuous`). This file proves
that the notions at a point agree when the neighbourhood filter of the point within `s` is
countably generated, in particular at every point of a first-countable space: a failure of lower
semicontinuity within `s` at `x` is then witnessed by a sequence in `s` that converges to `x`.

## Main statements

* `TauCeti.seqLowerSemicontinuousWithinAt_iff_lowerSemicontinuousWithinAt`: sequential lower
  semicontinuity within `s` at `x` is lower semicontinuity within `s` at `x` when `𝓝[s] x` is
  countably generated.
* `TauCeti.seqLowerSemicontinuousAt_iff_lowerSemicontinuousAt`: the same at `x`, when `𝓝 x` is
  countably generated.

## Implementation notes

The argument is adapted from the proof of `EValuesResearch.bipolarRate_eq_klInf_of_le_liminf` in
`EValuesResearch/Results/WeakSemicontinuity.lean` (commit `83205cb`) in the paper project
`RemyDegenne/evalues_research`, rewritten on the API of Tau Ceti.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {X β : Type*} [TopologicalSpace X] [Preorder β] {f : X → β} {s : Set X} {x : X}

/-- When `𝓝[s] x` is countably generated, a function sequentially lower semicontinuous within `s`
at `x` is lower semicontinuous within `s` at `x`. -/
theorem SeqLowerSemicontinuousWithinAt.lowerSemicontinuousWithinAt
    [(𝓝[s] x).IsCountablyGenerated] (hf : SeqLowerSemicontinuousWithinAt f s x) :
    LowerSemicontinuousWithinAt f s x := by
  intro y hy
  by_contra h
  -- a sequence in `s` converging to `x` along which `f` stays at most `y`
  obtain ⟨u, hu, hus⟩ := frequently_iff_seq_forall.1
    ((not_eventually.1 h).and_eventually self_mem_nhdsWithin)
  obtain ⟨n, hn⟩ :=
    (hf.eventually_lt (fun n ↦ (hus n).2) (hu.mono_right nhdsWithin_le_nhds) hy).exists
  exact (hus n).1 hn

/-- When `𝓝[s] x` is countably generated, sequential lower semicontinuity within `s` at `x` is
lower semicontinuity within `s` at `x`. -/
theorem seqLowerSemicontinuousWithinAt_iff_lowerSemicontinuousWithinAt
    [(𝓝[s] x).IsCountablyGenerated] :
    SeqLowerSemicontinuousWithinAt f s x ↔ LowerSemicontinuousWithinAt f s x :=
  ⟨fun hf ↦ hf.lowerSemicontinuousWithinAt, fun hf ↦ hf.seqLowerSemicontinuousWithinAt⟩

/-- When `𝓝 x` is countably generated, in particular in a first-countable space, a function
sequentially lower semicontinuous at `x` is lower semicontinuous at `x`. -/
theorem SeqLowerSemicontinuousAt.lowerSemicontinuousAt [(𝓝 x).IsCountablyGenerated]
    (hf : SeqLowerSemicontinuousAt f x) : LowerSemicontinuousAt f x :=
  lowerSemicontinuousWithinAt_univ_iff.1
    (seqLowerSemicontinuousWithinAt_univ_iff.2 hf).lowerSemicontinuousWithinAt

/-- When `𝓝 x` is countably generated, in particular in a first-countable space, sequential lower
semicontinuity at `x` is lower semicontinuity at `x`. -/
theorem seqLowerSemicontinuousAt_iff_lowerSemicontinuousAt [(𝓝 x).IsCountablyGenerated] :
    SeqLowerSemicontinuousAt f x ↔ LowerSemicontinuousAt f x :=
  ⟨fun hf ↦ hf.lowerSemicontinuousAt, fun hf ↦ hf.seqLowerSemicontinuousAt⟩

end TauCeti
