/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Process.Filtration
public import TauCeti.Probability.Process.PathLaw.Shift
import LMLExplore.MeasureTheory.Constructions.Pi
import LMLExplore.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Probability.Independence.Integration

/-!
# Infinite products of probability measures: coordinatewise properties, first and next terms

Under the infinite product `Measure.infinitePi` of copies of a probability measure `μ`, the first
`n` coordinates have the product law `Measure.pi`, and they are independent of the next `m`
coordinates. Under a countable product, almost surely every coordinate has a property that almost
every point of its factor has. The shift `(shift 𝓧)^[t]` by `t` coordinates (Tau Ceti's
`TauCeti.Probability.shift`) preserves the i.i.d. law, and the first `t` coordinates are
independent of the shifted sequence.

If `Q + ∑ i, b i • P i = ∑ i, c i • P i` for a probability measure `Q` and probability measures
`P i`, two functions of the first `N + 1` observations with equal integrals under the i.i.d. law of
every convex combination of the `P i` have equal integrals under the i.i.d. law of `Q`. This is
the polarization step of [EVR26, Note 03, Theorem 1], adapted from
`EValuesResearch/Results/TestMartingaleConverse.lean` (commit `6f05c5f`) in the paper project
`RemyDegenne/evalues_research`.

## Main statements

* `MeasureTheory.Measure.infinitePi_of_not_isProbabilityMeasure`: the infinite product of a family
  of measures that are not all probability measures is `0`.
* `MeasureTheory.measurePreserving_initSeg`: the first `n` terms `initSeg n` of an i.i.d. sequence
  have the product law.
* `MeasureTheory.Measure.ae_forall_apply_infinitePi`: if, for each `i` of a countable index type,
  `p i` holds almost everywhere under `μ i`, then almost surely under `Measure.infinitePi μ` every
  coordinate `x i` satisfies `p i`.
* `MeasureTheory.Measure.infinitePi_fin_mem_and_forall_add_mem`: for an i.i.d. sequence, the
  first `n` terms and the next `m` terms are independent.
* `MeasureTheory.measurePreserving_shift_iterate`: the shift by `t` terms preserves the i.i.d. law.
* `MeasureTheory.indepFun_initSeg_shift_iterate`: the first `t` terms are independent of the
  terms after them.
* `MeasureTheory.lintegral_mul_comp_shift_iterate`, `MeasureTheory.integral_mul_comp_shift_iterate`:
  the expectation of the product of a function of the first `t` terms and a function of the terms
  after them is the product of the expectations.
* `MeasureTheory.Measure.lintegral_infinitePi_eq_of_add_sum_eq_sum`: polarization for i.i.d. laws,
  from the convex combinations of finitely many probability measures to every probability measure
  in their linear span.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 03, *Converse of the power-one theorem for test martingales*,
  Theorem 1.
-/

public section

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- The infinite product `Measure.infinitePi μ` is `0` unless every `μ i` is a probability
measure. -/
lemma Measure.infinitePi_of_not_isProbabilityMeasure {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] {μ : (i : ι) → Measure (X i)}
    (h : ¬ ∀ i, IsProbabilityMeasure (μ i)) : Measure.infinitePi μ = 0 :=
  dite_eq_right h

/-- The first `n` terms of an i.i.d. sequence have the product law. -/
lemma measurePreserving_initSeg (P : Measure 𝓧) [IsProbabilityMeasure P] (n : ℕ) :
    MeasurePreserving (initSeg n) (Measure.infinitePi fun _ : ℕ ↦ P)
      (Measure.pi fun _ : Fin n ↦ P) := by
  refine ⟨measurable_initSeg n, ?_⟩
  rw [initSeg_def, ← Measure.infinitePi_eq_pi]
  exact Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective

section Shift

open ProbabilityTheory
open scoped ENNReal
open TauCeti.Probability (shift shift_iterate_eq_reindex measurable_shift_iterate)

/-- The shift by `t` terms preserves the i.i.d. law. -/
lemma measurePreserving_shift_iterate (P : Measure 𝓧) [IsProbabilityMeasure P] (t : ℕ) :
    MeasurePreserving ((shift 𝓧)^[t]) (Measure.infinitePi fun _ : ℕ ↦ P)
      (Measure.infinitePi fun _ : ℕ ↦ P) := by
  refine ⟨measurable_shift_iterate t, ?_⟩
  rw [shift_iterate_eq_reindex]
  exact Measure.map_infinitePi_infinitePi_of_inj (add_left_injective t)

/-- Under an i.i.d. law, the first `t` terms are independent of the terms after them. -/
lemma indepFun_initSeg_shift_iterate (P : Measure 𝓧) [IsProbabilityMeasure P] (t : ℕ) :
    IndepFun (initSeg t) ((shift 𝓧)^[t]) (Measure.infinitePi fun _ : ℕ ↦ P) := by
  have h := (iIndepFun_infinitePi (P := fun _ : ℕ ↦ P) (X := fun _ x ↦ x)
    (fun _ ↦ measurable_id)).indepFun_set (Set.Iio t) (Set.Ici t)
    (Set.disjoint_left.2 fun i (hi : i < t) (hi' : t ≤ i) ↦ (not_lt.2 hi') hi)
    (fun i ↦ measurable_pi_apply i)
  rw [shift_iterate_eq_reindex, initSeg_def]
  exact h.comp (φ := fun (y : Set.Iio t → 𝓧) (i : Fin t) ↦ y ⟨i, i.2⟩)
    (ψ := fun (y : Set.Ici t → 𝓧) (i : ℕ) ↦ y ⟨i + t, Nat.le_add_left t i⟩)
    (by fun_prop) (by fun_prop)

/-- Under an i.i.d. law, the expectation of the product of a function of the first `t` terms and
a function of the terms after them is the product of their expectations. -/
lemma lintegral_mul_comp_shift_iterate (P : Measure 𝓧) [IsProbabilityMeasure P]
    {f g : (ℕ → 𝓧) → ℝ≥0∞} {t : ℕ} (hf : Measurable f) (hft : DependsOn f (Set.Iio t))
    (hg : Measurable g) :
    ∫⁻ ω, f ω * g ((shift 𝓧)^[t] ω) ∂Measure.infinitePi (fun _ : ℕ ↦ P) =
      (∫⁻ ω, f ω ∂Measure.infinitePi (fun _ : ℕ ↦ P)) *
        ∫⁻ ω, g ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) := by
  have := nonempty_of_isProbabilityMeasure P
  obtain ⟨F, hF, rfl⟩ := exists_measurable_eq_comp_initSeg hf hft
  rw [← (measurePreserving_shift_iterate P t).lintegral_comp hg]
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hF.comp (measurable_initSeg t))
    (hg.comp (measurable_shift_iterate t)) ((indepFun_initSeg_shift_iterate P t).comp hF hg)

/-- Under an i.i.d. law, the expectation of the product of a real function of the first `t` terms
and a real function of the terms after them is the product of their expectations. -/
lemma integral_mul_comp_shift_iterate (P : Measure 𝓧) [IsProbabilityMeasure P]
    {f g : (ℕ → 𝓧) → ℝ} {t : ℕ} (hf : Measurable f) (hft : DependsOn f (Set.Iio t))
    (hg : Measurable g) :
    ∫ ω, f ω * g ((shift 𝓧)^[t] ω) ∂Measure.infinitePi (fun _ : ℕ ↦ P) =
      (∫ ω, f ω ∂Measure.infinitePi (fun _ : ℕ ↦ P)) *
        ∫ ω, g ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) := by
  have := nonempty_of_isProbabilityMeasure P
  obtain ⟨F, hF, rfl⟩ := exists_measurable_eq_comp_initSeg hf hft
  have hmap : ∫ ω, g ((shift 𝓧)^[t] ω) ∂Measure.infinitePi (fun _ : ℕ ↦ P) =
      ∫ ω, g ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) := by
    rw [← integral_map (measurable_shift_iterate t).aemeasurable
      (by rw [(measurePreserving_shift_iterate P t).map_eq]; exact hg.aestronglyMeasurable),
      (measurePreserving_shift_iterate P t).map_eq]
  rw [← hmap]
  exact ((indepFun_initSeg_shift_iterate P t).comp hF hg).integral_fun_mul_eq_mul_integral
    (hF.comp (measurable_initSeg t)).aestronglyMeasurable
    (hg.comp (measurable_shift_iterate t)).aestronglyMeasurable

end Shift

end MeasureTheory

namespace MeasureTheory.Measure

/-- Under a countable product of probability measures, if almost every point of each factor
satisfies a property, then almost surely every coordinate does. -/
theorem ae_forall_apply_infinitePi {ι : Type*} [Countable ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {p : ∀ i, X i → Prop} (h : ∀ i, ∀ᵐ x ∂μ i, p i x) :
    ∀ᵐ x ∂Measure.infinitePi μ, ∀ i, p i (x i) :=
  ae_all_iff.2 fun i ↦ (measurePreserving_eval_infinitePi μ i).quasiMeasurePreserving.ae (h i)

open ProbabilityTheory Finset in
/-- **The first terms of an i.i.d. sequence and the next terms are independent.** For an i.i.d.
sequence `z` of law `μ`, the first `n` terms `(z i)_{i < n}` lie in `B` and the next `m` terms lie
in `C` with probability `μ^⊗n(B) μ(C)^m`. -/
theorem infinitePi_fin_mem_and_forall_add_mem {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n m : ℕ) {B : Set (Fin n → X)} {C : Set X} (hB : MeasurableSet B)
    (hC : MeasurableSet C) :
    (Measure.infinitePi fun _ : ℕ ↦ μ) {z | initSeg n z ∈ B ∧ ∀ j < m, z (n + j) ∈ C} =
      Measure.pi (fun _ : Fin n ↦ μ) B * μ C ^ m := by
  -- The first `n` terms and the next `m` terms are independent.
  have h_ind := (iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ ↦ id)
    (fun _ ↦ measurable_id)).indepFun_finset (range n) (Ico n (n + m))
    (Finset.disjoint_left.2 fun i hi hi' ↦ by simp at hi hi'; omega) (fun _ ↦ by fun_prop)
  simp only [id] at h_ind
  have h_fin : Measurable fun (u : {i // i ∈ range n} → X) (i : Fin n) ↦
      u ⟨i, mem_range.2 i.2⟩ := by fun_prop
  have h_set : {z : ℕ → X | initSeg n z ∈ B ∧ ∀ j < m, z (n + j) ∈ C} =
      (fun z (i : range n) ↦ z i) ⁻¹' ((fun u (i : Fin n) ↦ u ⟨i, mem_range.2 i.2⟩) ⁻¹' B) ∩
        (fun z (i : Ico n (n + m)) ↦ z i) ⁻¹' (Set.univ.pi fun _ ↦ C) := by
    ext z
    simp only [initSeg_def, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, true_implies, Subtype.forall, mem_Ico]
    refine and_congr Iff.rfl ⟨fun h i hi ↦ ?_, fun h j hj ↦ h _ ⟨by omega, by omega⟩⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi.1
    exact h j (by omega)
  rw [h_set, h_ind.measure_inter_preimage_eq_mul _ _ (h_fin hB) (.univ_pi fun _ ↦ hC)]
  congr 1
  · -- The first `n` terms are `n` independent samples of `μ`.
    rw [← (measurePreserving_initSeg μ n).map_eq, Measure.map_apply (measurable_initSeg n) hB,
      ← Set.preimage_comp, initSeg_def]
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

open scoped NNReal ENNReal in
/-- **Polarization for i.i.d. laws.** Let `Q` be a probability measure and `P i` probability
measures with `Q + ∑ i, b i • P i = ∑ i, c i • P i`. If two functions of the first `N + 1`
observations have equal integrals under the i.i.d. law of every convex combination of the `P i`,
finite for the first function, then they have equal integrals under the i.i.d. law of `Q`. -/
lemma lintegral_infinitePi_eq_of_add_sum_eq_sum {𝓧 ι : Type*} {m𝓧 : MeasurableSpace 𝓧}
    [Fintype ι] {P : ι → Measure 𝓧} [∀ i, IsProbabilityMeasure (P i)] {b c : ι → ℝ≥0}
    {Q : Measure 𝓧} [IsProbabilityMeasure Q] (hQ : Q + ∑ i, b i • P i = ∑ i, c i • P i) {N : ℕ}
    {f g : (ℕ → 𝓧) → ℝ≥0∞} (hf : Measurable[Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) N] f)
    (hg : Measurable[Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) N] g)
    (hfg : ∀ w : ι → ℝ≥0, ∑ i, w i = 1 →
      ∫⁻ ω, f ω ∂Measure.infinitePi (fun _ ↦ ∑ i, w i • P i) =
        ∫⁻ ω, g ω ∂Measure.infinitePi (fun _ ↦ ∑ i, w i • P i))
    (hf_ne : ∀ w : ι → ℝ≥0, ∑ i, w i = 1 →
      ∫⁻ ω, f ω ∂Measure.infinitePi (fun _ ↦ ∑ i, w i • P i) ≠ ∞) :
    ∫⁻ ω, f ω ∂Measure.infinitePi (fun _ ↦ Q) = ∫⁻ ω, g ω ∂Measure.infinitePi (fun _ ↦ Q) := by
  rw [Filtration.piLE_eq_comap_frestrictLe] at hf hg
  obtain ⟨f', hf', rfl⟩ := hf.exists_eq_measurable_comp
  obtain ⟨g', hg', rfl⟩ := hg.exists_eq_measurable_comp
  have h (μ : Measure 𝓧) [IsProbabilityMeasure μ] {H : (Finset.Iic N → 𝓧) → ℝ≥0∞}
      (hH : Measurable H) :
      ∫⁻ ω, (H ∘ Preorder.frestrictLe N) ω ∂Measure.infinitePi (fun _ ↦ μ) =
        ∫⁻ x, H x ∂Measure.pi (fun _ : Finset.Iic N ↦ μ) :=
    lintegral_restrict_infinitePi _ hH
  rw [h Q hf', h Q hg']
  refine lintegral_pi_eq_of_add_sum_eq_sum hQ (fun w hw ↦ ?_) fun w hw ↦ ?_
  · have := isProbabilityMeasure_sum_smul (P := P) hw
    rw [← h _ hf', ← h _ hg']
    exact hfg w hw
  · have := isProbabilityMeasure_sum_smul (P := P) hw
    rw [← h _ hf']
    exact hf_ne w hw

end MeasureTheory.Measure
