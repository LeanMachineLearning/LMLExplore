/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDense

/-!
# Approximation of a measurable function by functions with finitely many values in a set

A measurable function `f` with values in a separable set `s` of a pseudo-emetric space is the
pointwise limit of measurable functions with finitely many values, all in `s`. This repackages
`MeasureTheory.SimpleFunc.approxOn` as plain functions, which is convenient when the measurable
space is not an instance (for instance a σ-algebra of a filtration).

## Main statements

* `Measurable.exists_seq_finite_range_tendsto`: a measurable `f` with values in `s` is the
  pointwise limit of measurable functions with finite range in `s`.
-/

public section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology

variable {α β : Type*} [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]
  {mβ : MeasurableSpace β}

/-- A measurable function `f` with values in a separable set `s` is the pointwise limit of
measurable functions with finitely many values, all in `s`. -/
theorem Measurable.exists_seq_finite_range_tendsto {f : β → α} (hf : Measurable f) {s : Set α}
    [SeparableSpace s] (hfs : ∀ x, f x ∈ s) :
    ∃ g : ℕ → β → α, (∀ n, Measurable (g n)) ∧ (∀ n, (range (g n)).Finite) ∧
      (∀ n x, g n x ∈ s) ∧ ∀ x, Tendsto (fun n ↦ g n x) atTop (𝓝 (f x)) := by
  rcases isEmpty_or_nonempty β with hβ | ⟨⟨x₀⟩⟩
  · exact ⟨fun _ ↦ f, fun _ ↦ hf, fun _ ↦ finite_range f, fun _ ↦ hfs,
      fun _ ↦ tendsto_const_nhds⟩
  · exact ⟨fun n ↦ SimpleFunc.approxOn f hf s (f x₀) (hfs x₀) n, fun _ ↦ SimpleFunc.measurable _,
      fun _ ↦ SimpleFunc.finite_range _, SimpleFunc.approxOn_mem hf (hfs x₀),
      fun x ↦ SimpleFunc.tendsto_approxOn hf (hfs x₀) (subset_closure (hfs x))⟩
