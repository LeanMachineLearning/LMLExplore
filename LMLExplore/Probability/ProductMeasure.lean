/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Independence.InfinitePi

/-!
# Infinite products of probability measures: the first terms and the next terms

Under the infinite product `Measure.infinitePi` of copies of a probability measure `μ`, the first
`n` coordinates have the product law `Measure.pi`, and they are independent of the next `m`
coordinates.

## Main definitions

* `MeasureTheory.initSeg n`: the first `n` terms of a sequence, as a function on `Fin n`.

## Main statements

* `MeasureTheory.exists_measurable_eq_comp_initSeg`: a measurable function of the first `n` terms
  of a sequence factors measurably through `initSeg n`.
* `MeasureTheory.measurePreserving_initSeg`: the first `n` terms of an i.i.d. sequence have the
  product law.
* `MeasureTheory.Measure.infinitePi_fin_mem_and_forall_add_mem`: for an i.i.d. sequence, the
  first `n` terms and the next `m` terms are independent.
-/

public section

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-! ### The first terms of a sequence -/

/-- The first `n` terms of a sequence. -/
def initSeg (n : ℕ) (ω : ℕ → 𝓧) : Fin n → 𝓧 := fun i ↦ ω i

/-- The coordinates of the initial segment are the first coordinates of the sequence. -/
@[simp]
lemma initSeg_apply (n : ℕ) (ω : ℕ → 𝓧) (i : Fin n) : initSeg n ω i = ω i := (rfl)

/-- The initial segment is a measurable function of the sequence. -/
@[fun_prop]
lemma measurable_initSeg (n : ℕ) : Measurable (initSeg (𝓧 := 𝓧) n) :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- A measurable function of the first `n` terms of a sequence is a measurable function of the
initial segment of length `n`. -/
lemma exists_measurable_eq_comp_initSeg [Nonempty 𝓧] {β : Type*} [MeasurableSpace β]
    {f : (ℕ → 𝓧) → β} {n : ℕ} (hf : Measurable f) (hfn : DependsOn f (Set.Iio n)) :
    ∃ g : (Fin n → 𝓧) → β, Measurable g ∧ f = g ∘ initSeg n := by
  classical
  -- extend a finite sequence by a constant
  let x₀ : 𝓧 := Classical.arbitrary 𝓧
  let ext : (Fin n → 𝓧) → ℕ → 𝓧 := fun y i ↦ if h : i < n then y ⟨i, h⟩ else x₀
  have hext : Measurable ext := by
    refine Measurable.of_eval fun i ↦ ?_
    by_cases h : i < n
    · simp only [ext, h, ↓reduceDIte]
      exact measurable_pi_apply _
    · simp only [ext, h, ↓reduceDIte]
      exact measurable_const
  refine ⟨f ∘ ext, hf.comp hext, funext fun ω ↦ hfn fun i hi ↦ ?_⟩
  simp only [Set.mem_Iio] at hi
  simp [ext, hi]

/-- The first `n` terms of an i.i.d. sequence have the product law. -/
lemma measurePreserving_initSeg (P : Measure 𝓧) [IsProbabilityMeasure P] (n : ℕ) :
    MeasurePreserving (initSeg n) (Measure.infinitePi fun _ : ℕ ↦ P)
      (Measure.pi fun _ : Fin n ↦ P) := by
  refine ⟨measurable_initSeg n, ?_⟩
  rw [← Measure.infinitePi_eq_pi]
  exact Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective

end MeasureTheory

namespace MeasureTheory.Measure

open ProbabilityTheory Finset in
/-- **The first terms of an i.i.d. sequence and the next terms are independent.** For an i.i.d.
sequence `z` of law `μ`, the first `n` terms `(z i)_{i < n}` lie in `B` and the next `m` terms lie
in `C` with probability `μ^⊗n(B) μ(C)^m`. -/
theorem infinitePi_fin_mem_and_forall_add_mem {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n m : ℕ) {B : Set (Fin n → X)} {C : Set X} (hB : MeasurableSet B)
    (hC : MeasurableSet C) :
    (Measure.infinitePi fun _ : ℕ ↦ μ) {z | (fun i : Fin n ↦ z i) ∈ B ∧ ∀ j < m, z (n + j) ∈ C} =
      Measure.pi (fun _ : Fin n ↦ μ) B * μ C ^ m := by
  -- The first `n` terms and the next `m` terms are independent.
  have h_ind := (iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ ↦ id)
    (fun _ ↦ measurable_id)).indepFun_finset (range n) (Ico n (n + m))
    (Finset.disjoint_left.2 fun i hi hi' ↦ by simp at hi hi'; omega) (fun _ ↦ by fun_prop)
  simp only [id] at h_ind
  have h_fin : Measurable fun (u : {i // i ∈ range n} → X) (i : Fin n) ↦
      u ⟨i, mem_range.2 i.2⟩ := by fun_prop
  have h_set : {z : ℕ → X | (fun i : Fin n ↦ z i) ∈ B ∧ ∀ j < m, z (n + j) ∈ C} =
      (fun z (i : range n) ↦ z i) ⁻¹' ((fun u (i : Fin n) ↦ u ⟨i, mem_range.2 i.2⟩) ⁻¹' B) ∩
        (fun z (i : Ico n (n + m)) ↦ z i) ⁻¹' (Set.univ.pi fun _ ↦ C) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, true_implies, Subtype.forall, mem_Ico]
    refine and_congr Iff.rfl ⟨fun h i hi ↦ ?_, fun h j hj ↦ h _ ⟨by omega, by omega⟩⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi.1
    exact h j (by omega)
  rw [h_set, h_ind.measure_inter_preimage_eq_mul _ _ (h_fin hB) (.univ_pi fun _ ↦ hC)]
  congr 1
  · -- The first `n` terms are `n` independent samples of `μ`.
    have h_pi : (Measure.infinitePi fun _ : ℕ ↦ μ).map (fun z (i : Fin n) ↦ z i) =
        Measure.pi fun _ : Fin n ↦ μ := by
      rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
    rw [← h_pi, Measure.map_apply (by fun_prop) hB, ← Set.preimage_comp]
    -- Both sides are the preimage of `B` under `z ↦ (z i)_{i : Fin n}`: the composite
    -- `(fun u i ↦ u ⟨i, _⟩) ∘ (fun z i ↦ z i)` unfolds to `fun z i ↦ z ↑⟨i, _⟩`, and
    -- `↑⟨i, _⟩ = i` is `Subtype.val` applied to a constructor.
    rfl
  · have h_pi : (fun z (i : Ico n (n + m)) ↦ z i) ⁻¹' (Set.univ.pi fun _ ↦ C) =
        ((Ico n (n + m) : Finset ℕ) : Set ℕ).pi fun _ ↦ C := by
      ext z
      simp
    rw [h_pi, Measure.infinitePi_pi _ fun _ _ ↦ hC, Finset.prod_const, Nat.card_Ico,
      Nat.add_sub_cancel_left]

end MeasureTheory.Measure
