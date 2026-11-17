/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Conditional probability measures

Complements to Mathlib's `ProbabilityTheory.cond`.

## Main statements

* `ProbabilityTheory.cond_smul`: conditioning a measure on a set does not change when the measure
  is multiplied by a constant `c ∉ {0, ∞}`.
* `ProbabilityTheory.cond_map`: conditioning the image of a measure on a set is the image of the
  measure conditioned on the preimage of that set.
* `ProbabilityTheory.hasLaw_pi_cond_of_measure_inter_forall_mem`: if
  `P(F ∩ {∀ i, Z i ∈ B i}) = P(F) ∏ i, μ i (B i)` for all measurable boxes `B`, then `Z` has law
  `Measure.pi μ` under `P` conditioned on `F`.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Conditioning a measure on a set does not change when the measure is multiplied by a constant
`c ∉ {0, ∞}`. -/
lemma cond_smul (μ : Measure Ω) (s : Set Ω) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    (c • μ)[|s] = μ[|s] := by
  rw [cond, cond, Measure.restrict_smul, smul_apply, smul_eq_mul, smul_smul,
    ENNReal.mul_inv (Or.inl hc0) (Or.inl hc), mul_right_comm, ENNReal.inv_mul_cancel hc0 hc,
    one_mul]

/-- Conditioning the image of `μ` by `f` on a measurable set `s` is the image by `f` of `μ`
conditioned on the preimage `f ⁻¹' s`. -/
lemma cond_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω} {f : Ω → Ω'}
    (hf : AEMeasurable f μ) {s : Set Ω'} (hs : MeasurableSet s) :
    (μ.map f)[|s] = (μ[|f ⁻¹' s]).map f := by
  rw [cond, cond, Measure.map_smul _ (hf.mono_measure Measure.restrict_le_self),
    Measure.restrict_map_of_aemeasurable hf hs, Measure.map_apply_of_aemeasurable hf hs]

/-- **Product law under a conditioned measure.** Let `Z` be a measurable random vector indexed by a
finite type and `F` an event of finite positive probability. If for every measurable box `B` the
probability that `F` holds and that `Z i ∈ B i` for all `i` is `P(F) ∏ i, μ i (B i)`, then under
`P` conditioned on `F` the coordinates of `Z` are independent, `Z i` having law `μ i`. -/
lemma hasLaw_pi_cond_of_measure_inter_forall_mem {ι : Type*} [Fintype ι] {𝓨 : ι → Type*}
    [∀ i, MeasurableSpace (𝓨 i)] {μ : ∀ i, Measure (𝓨 i)} [∀ i, SigmaFinite (μ i)]
    {P : Measure Ω} {Z : Ω → ∀ i, 𝓨 i} (hZ : Measurable Z) {F : Set Ω} (hPF : P F ≠ 0)
    (hPF_top : P F ≠ ∞)
    (h : ∀ B : ∀ i, Set (𝓨 i), (∀ i, MeasurableSet (B i)) →
      P (F ∩ {ω | ∀ i, Z ω i ∈ B i}) = P F * ∏ i, μ i (B i)) :
    HasLaw Z (Measure.pi μ) P[|F] := by
  refine ⟨hZ.aemeasurable, (Measure.pi_eq fun B hB ↦ ?_).symm⟩
  rw [Measure.map_apply hZ (.univ_pi hB), cond_apply' (hZ (.univ_pi hB))]
  simp only [Set.preimage, Set.mem_univ_pi]
  rw [h B hB, ← mul_assoc, ENNReal.inv_mul_cancel hPF hPF_top, one_mul]

end ProbabilityTheory
