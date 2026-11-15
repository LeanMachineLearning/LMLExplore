/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Extending a lower semicontinuous function by `⊤` off a closed set

A function `f` that is lower semicontinuous on a closed set `s`, with values in an order with a
top element, stays lower semicontinuous on the whole space once extended by `⊤` off `s`. For a
real function and the extension `x ↦ if x ∈ s then (f x : EReal) else ⊤`, this is the passage from
lower semicontinuity on a closed domain to the properness and lower semicontinuity of convex
analysis.

## Main statements

* `LowerSemicontinuousOn.lowerSemicontinuous_ite_top`: if `f` is lower semicontinuous on a closed
  set `s`, then `x ↦ if x ∈ s then f x else ⊤` is lower semicontinuous.
-/

public section

open Filter Set

variable {α γ : Type*} [TopologicalSpace α] [Preorder γ] [OrderTop γ] {f : α → γ} {s : Set α}

/-- **Extension by `⊤` off a closed set.** If `f` is lower semicontinuous on a closed set `s`,
then `f` extended by `⊤` off `s` is lower semicontinuous. -/
theorem LowerSemicontinuousOn.lowerSemicontinuous_ite_top [DecidablePred (· ∈ s)]
    (hf : LowerSemicontinuousOn f s) (hs : IsClosed s) :
    LowerSemicontinuous fun x ↦ if x ∈ s then f x else ⊤ := by
  intro x y hy
  by_cases hx : x ∈ s
  · simp only [hx, ite_true] at hy
    filter_upwards [eventually_nhdsWithin_iff.1 (hf x hx y hy)] with z hz
    split_ifs with hzs
    exacts [hz hzs, hy.trans_le le_top]
  · simp only [hx, ite_false] at hy
    filter_upwards [hs.isOpen_compl.mem_nhds hx] with z hz
    simpa [show z ∉ s from hz] using hy
