/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
import LMLExplore.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.Integral.Pi

/-!
# Lebesgue integrals against product measures

An integral against a product of two σ-finite measures indexed by `Fin 2` is an iterated
integral. Against a product of finitely many σ-finite measures, the integral of a function of the
images of the coordinates under maps to finite types is a sum over the masses of the fibres.

## Main statements

* `MeasureTheory.lintegral_pi_fin_two`:
  `∫⁻ e, F e ∂Measure.pi μ = ∫⁻ x, ∫⁻ y, F ![x, y] ∂μ 1 ∂μ 0` for `μ : Fin 2 → Measure α`.
* `MeasureTheory.lintegral_pi_fin_two_mul`: the integral of `u (e 0) * v (e 1)` is the product of
  the integrals of `u` and `v`.
* `MeasureTheory.lintegral_pi_comp_eq_sum`: the integral of `g fun i ↦ φ i (e i)`, for maps `φ i`
  to finite types, is `∑ k, g k * ∏ i, μ i (φ i ⁻¹' {k i})`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- The integral against a product of two σ-finite measures, indexed by `Fin 2`, is an iterated
integral. -/
lemma lintegral_pi_fin_two (μ : Fin 2 → Measure α) [∀ i, SigmaFinite (μ i)]
    {F : (Fin 2 → α) → ℝ≥0∞} (hF : AEMeasurable F (Measure.pi μ)) :
    ∫⁻ e, F e ∂Measure.pi μ = ∫⁻ x, ∫⁻ y, F ![x, y] ∂μ 1 ∂μ 0 := by
  have h := (measurePreserving_piFinTwo μ).symm
  rw [← h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), lintegral_prod]
  · refine lintegral_congr fun x ↦ lintegral_congr fun y ↦ congrArg F ?_
    ext i
    fin_cases i <;> simp [MeasurableEquiv.piFinTwo_symm_apply]
  · exact (h.aemeasurable_comp_iff (MeasurableEquiv.measurableEmbedding _)).2 hF

/-- The integral of `u (e 0) * v (e 1)` against a product of two σ-finite measures is the
product of the integrals. -/
lemma lintegral_pi_fin_two_mul (μ : Fin 2 → Measure α) [∀ i, SigmaFinite (μ i)]
    {u v : α → ℝ≥0∞} (hu : AEMeasurable u (μ 0)) (hv : AEMeasurable v (μ 1)) :
    ∫⁻ e, u (e 0) * v (e 1) ∂Measure.pi μ = (∫⁻ x, u x ∂μ 0) * ∫⁻ y, v y ∂μ 1 := by
  simpa [Fin.prod_univ_two] using
    TauCeti.lintegral_fintype_prod_eq_prod₀ μ (f := ![u, v]) (Fin.forall_fin_two.2 ⟨hu, hv⟩)

/-- The integral of `g fun i ↦ φ i (e i)` against a product of finitely many σ-finite measures,
where the maps `φ i` take values in finite types, in terms of the masses of the fibres of the
`φ i`. -/
lemma lintegral_pi_comp_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω κ : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] [∀ i, Fintype (κ i)] [∀ i, MeasurableSpace (κ i)]
    [∀ i, MeasurableSingletonClass (κ i)] (μ : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (μ i)]
    {φ : ∀ i, Ω i → κ i} (hφ : ∀ i, Measurable (φ i)) (g : (∀ i, κ i) → ℝ≥0∞) :
    ∫⁻ e, g (fun i ↦ φ i (e i)) ∂Measure.pi μ = ∑ k, g k * ∏ i, μ i (φ i ⁻¹' {k i}) := by
  have hΦ : Measurable fun (e : ∀ i, Ω i) i ↦ φ i (e i) :=
    .of_eval fun i ↦ (hφ i).comp (measurable_pi_apply i)
  rw [lintegral_comp_eq_sum_measure_preimage_singleton hΦ.aemeasurable g]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hpre : (fun (e : ∀ i, Ω i) i ↦ φ i (e i)) ⁻¹' {k} = Set.univ.pi fun i ↦ φ i ⁻¹' {k i} := by
    ext e
    simp [funext_iff]
  rw [hpre, Measure.pi_pi]

end MeasureTheory
