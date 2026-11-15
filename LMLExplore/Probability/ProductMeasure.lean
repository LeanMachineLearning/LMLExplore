/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Process.Stopping
public import Statlib.ForMathlib.Probability.Process.Filtration
import LMLExplore.MeasureTheory.Constructions.Pi
import LMLExplore.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Probability.Independence.Integration

/-!
# Infinite products of probability measures: the first terms and the next terms

Under the infinite product `Measure.infinitePi` of copies of a probability measure `μ`, the first
`n` coordinates have the product law `Measure.pi`, and they are independent of the next `m`
coordinates. With the filtration `Filtration.piLE` of the first coordinates, whose time `n` has seen
the coordinates `0, …, n`, the coordinate `n + 1` is independent of time `n`; functions of the first
coordinates are adapted, and random times that are functions of the first coordinates are stopping
times.

If `Q + ∑ i, b i • P i = ∑ i, c i • P i` for a probability measure `Q` and probability measures
`P i`, two functions of the first `N + 1` observations with equal integrals under the i.i.d. law of
every convex combination of the `P i` have equal integrals under the i.i.d. law of `Q`. This is
the polarization step of [EVR26, Note 03, Theorem 1], adapted from
`EValuesResearch/Results/TestMartingaleConverse.lean` (commit `6f05c5f`) in the paper project
`RemyDegenne/evalues_research`.

## Main statements

* `MeasureTheory.measurePreserving_initSeg`: the first `n` terms `initSeg n` of an i.i.d. sequence
  have the product law.
* `MeasureTheory.Measure.infinitePi_fin_mem_and_forall_add_mem`: for an i.i.d. sequence, the
  first `n` terms and the next `m` terms are independent.
* `MeasureTheory.Measure.lintegral_infinitePi_eq_of_add_sum_eq_sum`: polarization for i.i.d. laws,
  from the convex combinations of finitely many probability measures to every probability measure
  in their linear span.
* `MeasureTheory.Filtration.measurable_piLE_initSeg`,
  `MeasureTheory.Filtration.adapted_piLE_comp_initSeg`,
  `MeasureTheory.Filtration.isStoppingTime_piLE_comp_initSeg`: the first `k` terms are measurable
  at time `n` of `Filtration.piLE` for `k ≤ n + 1`, functions of the first `n + 1` terms form an
  adapted process, and a function of the first `k + 1` terms that is at least `k` is a stopping
  time.
* `ProbabilityTheory.indep_piLE_comap_eval_succ`: for an i.i.d. sequence, the term `n + 1` is
  independent of `Filtration.piLE n`.
* `ProbabilityTheory.setLIntegral_comp_eval_succ`: for an event `s` of `Filtration.piLE n`,
  `∫⁻ ω in s, f (ω (n + 1)) = P^ℕ s * ∫⁻ f ∂P` under an i.i.d. law.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 03, *Converse of the power-one theorem for test martingales*,
  Theorem 1.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- The first `n` terms of an i.i.d. sequence have the product law. -/
lemma measurePreserving_initSeg (P : Measure 𝓧) [IsProbabilityMeasure P] (n : ℕ) :
    MeasurePreserving (initSeg n) (Measure.infinitePi fun _ : ℕ ↦ P)
      (Measure.pi fun _ : Fin n ↦ P) := by
  refine ⟨measurable_initSeg n, ?_⟩
  rw [initSeg_def, ← Measure.infinitePi_eq_pi]
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

namespace MeasureTheory.Filtration

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- For `k ≤ n + 1`, the first `k` terms of a sequence are measurable at time `n` of
`Filtration.piLE`. -/
lemma measurable_piLE_initSeg {k n : ℕ} (hk : k ≤ n + 1) :
    Measurable[piLE (X := fun _ : ℕ ↦ 𝓧) n] (initSeg k) := by
  rw [initSeg_def]
  exact @Measurable.of_eval _ _ _ (piLE n) _ _ fun i ↦ measurable_piLE_apply (by have := i.2; omega)

/-- The process of the values of measurable functions `X n` of the first `n + 1` terms of a
sequence is adapted to `Filtration.piLE`. -/
lemma adapted_piLE_comp_initSeg {β : Type*} [MeasurableSpace β]
    {X : (n : ℕ) → (Fin (n + 1) → 𝓧) → β} (hX : ∀ n, Measurable (X n)) :
    Adapted (piLE (X := fun _ : ℕ ↦ 𝓧)) fun n ω ↦ X n (initSeg (n + 1) ω) :=
  fun n ↦ (hX n).comp (measurable_piLE_initSeg le_rfl)

/-- A random time that is a measurable function, at least `k`, of the first `k + 1` terms of a
sequence is a stopping time of `Filtration.piLE`. -/
lemma isStoppingTime_piLE_comp_initSeg {k : ℕ} {T : (Fin (k + 1) → 𝓧) → ℕ}
    (hT : Measurable T) (hTk : ∀ x, k ≤ T x) :
    IsStoppingTime (piLE (X := fun _ : ℕ ↦ 𝓧)) fun ω ↦ (T (initSeg (k + 1) ω) : WithTop ℕ) := by
  intro i
  by_cases hi : k ≤ i
  · exact measurable_piLE_initSeg (by omega)
      (hT (MeasurableSet.of_discrete (s := {m : ℕ | (m : WithTop ℕ) ≤ i})))
  · -- before time `k` the random time has not stopped yet
    convert @MeasurableSet.empty _ (piLE (X := fun _ : ℕ ↦ 𝓧) i) using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact Nat.cast_lt.2 (lt_of_lt_of_le (by omega) (hTk _))

end MeasureTheory.Filtration

namespace ProbabilityTheory

open MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- Under an i.i.d. law, the term `n + 1` of a sequence is independent of its first `n + 1`
terms, that is, of time `n` of `Filtration.piLE`. -/
lemma indep_piLE_comap_eval_succ (μ : Measure 𝓧) [IsProbabilityMeasure μ] (n : ℕ) :
    Indep (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) n) (m𝓧.comap fun ω : ℕ → 𝓧 ↦ ω (n + 1))
      (Measure.infinitePi fun _ ↦ μ) := by
  have h := (iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ ↦ id)
    fun _ ↦ measurable_id).indepFun_finset (Finset.Iic n) {n + 1} (by simp)
    fun i ↦ measurable_pi_apply i
  have h' : (fun ω : ℕ → 𝓧 ↦ Preorder.frestrictLe n ω)
      ⟂ᵢ[Measure.infinitePi fun _ ↦ μ] fun ω ↦ ω (n + 1) := by
    exact h.comp measurable_id (measurable_pi_apply ⟨n + 1, by simp⟩)
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (IndepFun_iff_Indep _ _ _).mp h'

/-- For an event `s` determined by the first `n + 1` terms of an i.i.d. sequence of law `μ`,
`∫⁻ ω in s, f (ω (n + 1)) ∂μ^ℕ = μ^ℕ s * ∫⁻ f ∂μ`. -/
lemma setLIntegral_comp_eval_succ (μ : Measure 𝓧) [IsProbabilityMeasure μ]
    {f : 𝓧 → ℝ≥0∞} (hf : Measurable f) (n : ℕ) {s : Set (ℕ → 𝓧)}
    (hs : MeasurableSet[Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) n] s) :
    ∫⁻ ω in s, f (ω (n + 1)) ∂(Measure.infinitePi fun _ ↦ μ) =
      (Measure.infinitePi fun _ ↦ μ) s * ∫⁻ x, f x ∂μ := by
  have hs' : MeasurableSet s := Filtration.le _ n _ hs
  have h1 : Measurable[Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) n]
      (s.indicator (1 : (ℕ → 𝓧) → ℝ≥0∞)) :=
    Measurable.indicator (m := Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) n) measurable_const hs
  calc ∫⁻ ω in s, f (ω (n + 1)) ∂(Measure.infinitePi fun _ ↦ μ)
      = ∫⁻ ω, s.indicator 1 ω * f (ω (n + 1)) ∂(Measure.infinitePi fun _ ↦ μ) := by
        rw [← lintegral_indicator hs']
        congr 1 with ω
        by_cases h : ω ∈ s <;> simp [h]
    _ = (∫⁻ ω, s.indicator 1 ω ∂(Measure.infinitePi fun _ ↦ μ)) *
          ∫⁻ ω, f (ω (n + 1)) ∂(Measure.infinitePi fun _ ↦ μ) :=
        lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
          (Filtration.le _ n) (measurable_pi_apply (n + 1)).comap_le
          (indep_piLE_comap_eval_succ μ n) h1 (hf.comp (comap_measurable _))
    _ = (Measure.infinitePi fun _ ↦ μ) s * ∫⁻ x, f x ∂μ := by
        rw [lintegral_indicator_one hs',
          (measurePreserving_eval_infinitePi (fun _ ↦ μ) (n + 1)).lintegral_comp hf]

end ProbabilityTheory
