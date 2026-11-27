/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.MeasurableSpace.Constructions
public import LMLExplore.Probability.Process.Filtration
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Process.Filtration
public import TauCeti.Probability.Ergodic.BernoulliShift
import LMLExplore.MeasureTheory.Constructions.Pi
import LMLExplore.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Probability.Independence.Integration
import TauCeti.Probability.Process.PathLaw.Shift

/-!
# Infinite products of probability measures: coordinatewise properties, first and next terms

Under the infinite product `Measure.infinitePi` of copies of a probability measure `μ`, the first
`n` coordinates have the product law `Measure.pi`, and they are independent of the next `m`
coordinates. The shift of an i.i.d. sequence is again i.i.d. with the same law, and the first `t`
terms are independent of the terms after them. Under a countable product, almost surely every
coordinate has a property that almost every point of its factor has. With the filtration
`Filtration.piLE` of the first coordinates, whose time `n` has seen the coordinates `0, …, n`, the
coordinate `n + 1` is independent of time `n`.

If `Q + ∑ i, b i • P i = ∑ i, c i • P i` for a probability measure `Q` and probability measures
`P i`, two functions of the first `N` observations with equal integrals under the i.i.d. law of
every convex combination of the `P i` have equal integrals under the i.i.d. law of `Q`. This is
the polarization step of [EVR26, Note 03, Theorem 1], adapted from
`EValuesResearch/Results/TestMartingaleConverse.lean` (commit `6f05c5f`) in the paper project
`RemyDegenne/evalues_research`.

## Main statements

* `MeasureTheory.measurePreserving_initSeg`, `MeasureTheory.lintegral_comp_initSeg_infinitePi`:
  the first `n` terms `initSeg n` of an i.i.d. sequence have the product law.
* `MeasureTheory.tendsto_measure_pi_of_ae_eventually_iff`: if almost surely, eventually, the
  first `n` terms of an i.i.d. sequence are in `C n` exactly when the sequence is in `A`, then the
  probability of `C n` under the product law tends to that of `A`; the special cases
  `MeasureTheory.tendsto_measure_pi_one_of_ae_eventually_mem` and
  `MeasureTheory.tendsto_measure_pi_zero_of_ae_eventually_notMem` have limits `1` and `0`.
* `MeasureTheory.ae_eventually_lt_exp_of_lintegral_le`: functions of the first `n` terms with
  bounded mean under the product law are eventually below `exp (n ε)` almost surely, by Markov's
  inequality and the Borel–Cantelli lemma.
* `MeasureTheory.Measure.ae_forall_apply_infinitePi`: if, for each `i` of a countable index type,
  `p i` holds almost everywhere under `μ i`, then almost surely under `Measure.infinitePi μ` every
  coordinate `x i` satisfies `p i`.
* `MeasureTheory.Measure.ae_forall_notMem_infinitePi`: if each `N i` is `μ i`-null, then almost
  surely under `Measure.infinitePi μ` no coordinate `x i` is in `N i`.
* `MeasureTheory.Measure.ae_of_ae_infinitePi_map`: a property of almost every point of the
  product of the images `(μ i).map (f i)` holds for the coordinatewise image of almost every point
  of the product of the `μ i`.
* `MeasureTheory.Measure.infinitePi_fin_mem_and_forall_add_mem`: for an i.i.d. sequence, the
  first `n` terms and the next `m` terms are independent.
* `MeasureTheory.measurePreserving_shift`, `MeasureTheory.measurePreserving_shift_iterate`: the
  shift and its iterates preserve the i.i.d. law.
* `MeasureTheory.shift_iterate_eqOn`: two sequences that agree on the first `t` terms have shifts
  by `s` that agree on the first `t - s` terms.
* `MeasureTheory.dependsOn_comp_shift_iterate`: a function of the first `L` terms, read after
  the shift by `a`, is a function of the first `a + L` terms;
  `MeasureTheory.dependsOn_mul_comp_shift_iterate`: the product of a function of the first `n`
  terms and a function of the first `m` terms after them is a function of the first `n + m` terms.
* `MeasureTheory.indepFun_initSeg_shift_iterate`: the first `t` terms are independent of the
  terms after them.
* `MeasureTheory.lintegral_mul_comp_shift_iterate`, `MeasureTheory.integral_mul_comp_shift_iterate`:
  the expectation of the product of a function of the first `t` terms and a function of the terms
  after them is the product of the expectations.
* `MeasureTheory.Measure.infinitePi_eq_zero_of_not_isProbabilityMeasure`: the infinite product
  is `0` as soon as one factor is not a probability measure.
* `MeasureTheory.Measure.infinitePi_update`, `MeasureTheory.Measure.lintegral_infinitePi_update`:
  a product with the factor `j` replaced by `ν` is the law of a point of the product with the
  coordinate `j` replaced by an independent draw from `ν`, and Tonelli's theorem at that
  coordinate.
* `MeasureTheory.Measure.lintegral_infinitePi_congr_of_dependsOn`: the integral of a function of
  finitely many coordinates only depends on the factors of these coordinates.
* `MeasureTheory.Measure.lintegral_infinitePi_eq_of_add_sum_eq_sum`: polarization for i.i.d. laws,
  from the convex combinations of finitely many probability measures to every probability measure
  in their linear span.
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

/-- The integral of a function of the first `n` terms of an i.i.d. sequence is its integral under
the product law: the form of `measurePreserving_initSeg` for an integrand written with
`fun i ↦ ω i`. -/
lemma lintegral_comp_initSeg_infinitePi (P : Measure 𝓧) [IsProbabilityMeasure P] {n : ℕ}
    {f : (Fin n → 𝓧) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω : ℕ → 𝓧, f (fun i ↦ ω i) ∂(Measure.infinitePi fun _ ↦ P) =
      ∫⁻ x, f x ∂(Measure.pi fun _ : Fin n ↦ P) := by
  simpa only [initSeg_def] using (measurePreserving_initSeg P n).lintegral_comp hf

open Filter Topology in
/-- If almost surely under the i.i.d. law of `P`, eventually, the first `n` terms are in `C n`
exactly when the sequence is in `A`, then the probability of `C n` under the product law tends to
that of `A`. -/
lemma tendsto_measure_pi_of_ae_eventually_iff (P : Measure 𝓧) [IsProbabilityMeasure P]
    {C : (n : ℕ) → Set (Fin n → 𝓧)} (hC : ∀ n, MeasurableSet (C n)) {A : Set (ℕ → 𝓧)}
    (hA : MeasurableSet A)
    (h : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ P),
      ∀ᶠ n : ℕ in atTop, initSeg n ω ∈ C n ↔ ω ∈ A) :
    Tendsto (fun n : ℕ ↦ Measure.pi (fun _ : Fin n ↦ P) (C n)) atTop
      (𝓝 (Measure.infinitePi (fun _ : ℕ ↦ P) A)) := by
  refine (tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop hA
    (fun n ↦ measurable_initSeg n (hC n)) h).congr fun n ↦ ?_
  exact (measurePreserving_initSeg P n).measure_preimage (hC n).nullMeasurableSet

open Filter Topology in
/-- If almost surely under the i.i.d. law of `P` the first `n` terms are eventually in `C n`, then
the probability of `C n` under the product law tends to `1`. -/
lemma tendsto_measure_pi_one_of_ae_eventually_mem (P : Measure 𝓧) [IsProbabilityMeasure P]
    {C : (n : ℕ) → Set (Fin n → 𝓧)} (hC : ∀ n, MeasurableSet (C n))
    (h : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ P), ∀ᶠ n : ℕ in atTop, initSeg n ω ∈ C n) :
    Tendsto (fun n : ℕ ↦ Measure.pi (fun _ : Fin n ↦ P) (C n)) atTop (𝓝 1) := by
  simpa using tendsto_measure_pi_of_ae_eventually_iff P hC MeasurableSet.univ (by simpa using h)

open Filter Topology in
/-- If almost surely under the i.i.d. law of `P` the first `n` terms are eventually outside
`C n`, then the probability of `C n` under the product law tends to `0`. -/
lemma tendsto_measure_pi_zero_of_ae_eventually_notMem (P : Measure 𝓧) [IsProbabilityMeasure P]
    {C : (n : ℕ) → Set (Fin n → 𝓧)} (hC : ∀ n, MeasurableSet (C n))
    (h : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ P), ∀ᶠ n : ℕ in atTop, initSeg n ω ∉ C n) :
    Tendsto (fun n : ℕ ↦ Measure.pi (fun _ : Fin n ↦ P) (C n)) atTop (𝓝 0) := by
  simpa using tendsto_measure_pi_of_ae_eventually_iff P hC MeasurableSet.empty (by simpa using h)

open ProbabilityTheory
open TauCeti.Probability (shift shift_iterate_apply shift_iterate_eq_reindex
  measurable_shift_iterate)

/-- If two sequences agree on the first `t` terms, their shifts by `s` agree on the first `t - s`
terms. -/
lemma shift_iterate_eqOn {t : ℕ} {ω ω' : ℕ → 𝓧} (h : ∀ i < t, ω i = ω' i) (s : ℕ) :
    ∀ i < t - s, (shift 𝓧)^[s] ω i = (shift 𝓧)^[s] ω' i := fun i hi ↦ by
  simp only [shift_iterate_apply]
  exact h _ (by omega)

/-- The shift preserves the i.i.d. law. -/
lemma measurePreserving_shift (P : Measure 𝓧) [IsProbabilityMeasure P] :
    MeasurePreserving (shift 𝓧) (Measure.infinitePi fun _ : ℕ ↦ P)
      (Measure.infinitePi fun _ : ℕ ↦ P) :=
  (Measure.ergodic_shift_infinitePi_const P).toMeasurePreserving

/-- The iterates of the shift preserve the i.i.d. law. -/
lemma measurePreserving_shift_iterate (P : Measure 𝓧) [IsProbabilityMeasure P] (t : ℕ) :
    MeasurePreserving (shift 𝓧)^[t] (Measure.infinitePi fun _ : ℕ ↦ P)
      (Measure.infinitePi fun _ : ℕ ↦ P) :=
  (measurePreserving_shift P).iterate t

/-- A function of the first `L` terms, read on the sequence shifted by `a`, is a function of the
first `a + L` terms. -/
lemma dependsOn_comp_shift_iterate {β : Type*} {L : ℕ} {g : (ℕ → 𝓧) → β}
    (hg : DependsOn g (Set.Iio L)) (a : ℕ) :
    DependsOn (g ∘ (shift 𝓧)^[a]) (Set.Iio (a + L)) := by
  intro ω ω' h
  refine hg fun i hi ↦ ?_
  simp only [TauCeti.Probability.shift_iterate_apply]
  exact h _ (by simp only [Set.mem_Iio] at hi ⊢; omega)

/-- **Concatenation.** The product of a function of the first `n` terms and a function of the
first `m` terms of the sequence shifted by `n` is a function of the first `n + m` terms. -/
lemma dependsOn_mul_comp_shift_iterate {M : Type*} [Mul M] {f g : (ℕ → 𝓧) → M} {n m : ℕ}
    (hf : DependsOn f (Set.Iio n)) (hg : DependsOn g (Set.Iio m)) :
    DependsOn (fun ω ↦ f ω * g ((shift 𝓧)^[n] ω)) (Set.Iio (n + m)) := by
  intro ω ω' h
  have hg' : g ((shift 𝓧)^[n] ω) = g ((shift 𝓧)^[n] ω') := dependsOn_comp_shift_iterate hg n h
  simp only
  rw [hf fun i hi ↦ h i (Set.Iio_subset_Iio (Nat.le_add_right n m) hi), hg']

/-- Under an i.i.d. law, the first `t` terms are independent of the terms after them. -/
lemma indepFun_initSeg_shift_iterate (P : Measure 𝓧) [IsProbabilityMeasure P] (t : ℕ) :
    IndepFun (initSeg t) ((shift 𝓧)^[t]) (Measure.infinitePi fun _ : ℕ ↦ P) := by
  have h := (iIndepFun_infinitePi (P := fun _ : ℕ ↦ P) (X := fun _ x ↦ x)
    (fun _ ↦ measurable_id)).indepFun_set (Set.Iio t) (Set.Ici t)
    (Set.disjoint_left.2 fun i (hi : i < t) (hi' : t ≤ i) ↦ (not_lt.2 hi') hi)
    (fun i ↦ measurable_pi_apply i)
  rw [shift_iterate_eq_reindex, initSeg_def]
  exact h.comp (φ := fun (y : Set.Iio t → 𝓧) (i : Fin t) ↦ y ⟨i, i.isLt⟩)
    (ψ := fun (y : Set.Ici t → 𝓧) (i : ℕ) ↦ y ⟨i + t, Nat.le_add_left t i⟩)
    (by fun_prop) (by fun_prop)

/-- Under an i.i.d. law, a function of the first `t` terms is independent of a function of the
terms after them: the expectation of their product is the product of their expectations. -/
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

end MeasureTheory

namespace MeasureTheory.Measure

/-- The infinite product of a family of measures is `0` as soon as one of them is not a probability
measure. -/
lemma infinitePi_eq_zero_of_not_isProbabilityMeasure {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] {μ : (i : ι) → Measure (X i)} {i : ι}
    (h : ¬ IsProbabilityMeasure (μ i)) :
    Measure.infinitePi μ = 0 := by
  have h' : ¬ ∀ j, IsProbabilityMeasure (μ j) := fun h' ↦ h (h' i)
  simp [Measure.infinitePi, h']

/-- Under a countable product of probability measures, if almost every point of each factor
satisfies a property, then almost surely every coordinate does. -/
theorem ae_forall_apply_infinitePi {ι : Type*} [Countable ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {p : ∀ i, X i → Prop} (h : ∀ i, ∀ᵐ x ∂μ i, p i x) :
    ∀ᵐ x ∂Measure.infinitePi μ, ∀ i, p i (x i) :=
  ae_all_iff.2 fun i ↦ (measurePreserving_eval_infinitePi μ i).quasiMeasurePreserving.ae (h i)

/-- Under a countable product of probability measures, if each `N i` is null for `μ i`, then
almost surely no coordinate `x i` is in `N i`. -/
theorem ae_forall_notMem_infinitePi {ι : Type*} [Countable ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {N : ∀ i, Set (X i)} (h : ∀ i, μ i (N i) = 0) :
    ∀ᵐ x ∂Measure.infinitePi μ, ∀ i, x i ∉ N i :=
  ae_forall_apply_infinitePi μ fun i ↦ measure_eq_zero_iff_ae_notMem.1 (h i)

/-- If almost every point of the product of the images `(μ i).map (f i)` satisfies a property,
then so does the image `fun i ↦ f i (x i)` of almost every point of the product of the `μ i`:
the product of the images is the image of the product. -/
theorem ae_of_ae_infinitePi_map {ι : Type*} {X Y : ι → Type*} [∀ i, MeasurableSpace (X i)]
    [∀ i, MeasurableSpace (Y i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {f : ∀ i, X i → Y i} (hf : ∀ i, Measurable (f i)) {p : (∀ i, Y i) → Prop}
    (h : ∀ᵐ y ∂Measure.infinitePi (fun i ↦ (μ i).map (f i)), p y) :
    ∀ᵐ x ∂Measure.infinitePi μ, p fun i ↦ f i (x i) := by
  rw [← infinitePi_map_pi μ hf] at h
  exact ae_of_ae_map (Measurable.of_eval fun i ↦ (hf i).comp (measurable_pi_apply i)).aemeasurable
    h

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
      u ⟨i, mem_range.2 i.isLt⟩ := by fun_prop
  have h_set : {z : ℕ → X | initSeg n z ∈ B ∧ ∀ j < m, z (n + j) ∈ C} =
      (fun z (i : range n) ↦ z i) ⁻¹' ((fun u (i : Fin n) ↦ u ⟨i, mem_range.2 i.isLt⟩) ⁻¹' B) ∩
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
measures with `Q + ∑ i, b i • P i = ∑ i, c i • P i`. If two functions of the first `N`
observations, measurable at time `N` of `Filtration.piLT`, have equal integrals under the i.i.d.
law of every convex combination of the `P i`, finite for the first function, then they have equal
integrals under the i.i.d. law of `Q`. -/
lemma lintegral_infinitePi_eq_of_add_sum_eq_sum {𝓧 ι : Type*} {m𝓧 : MeasurableSpace 𝓧}
    [Fintype ι] {P : ι → Measure 𝓧} [∀ i, IsProbabilityMeasure (P i)] {b c : ι → ℝ≥0}
    {Q : Measure 𝓧} [IsProbabilityMeasure Q] (hQ : Q + ∑ i, b i • P i = ∑ i, c i • P i) {N : ℕ}
    {f g : (ℕ → 𝓧) → ℝ≥0∞} (hf : Measurable[Filtration.piLT (X := fun _ : ℕ ↦ 𝓧) N] f)
    (hg : Measurable[Filtration.piLT (X := fun _ : ℕ ↦ 𝓧) N] g)
    (hfg : ∀ w : ι → ℝ≥0, ∑ i, w i = 1 →
      ∫⁻ ω, f ω ∂Measure.infinitePi (fun _ ↦ ∑ i, w i • P i) =
        ∫⁻ ω, g ω ∂Measure.infinitePi (fun _ ↦ ∑ i, w i • P i))
    (hf_ne : ∀ w : ι → ℝ≥0, ∑ i, w i = 1 →
      ∫⁻ ω, f ω ∂Measure.infinitePi (fun _ ↦ ∑ i, w i • P i) ≠ ∞) :
    ∫⁻ ω, f ω ∂Measure.infinitePi (fun _ ↦ Q) = ∫⁻ ω, g ω ∂Measure.infinitePi (fun _ ↦ Q) := by
  rw [Filtration.piLT_eq_comap_initSeg] at hf hg
  obtain ⟨f', hf', rfl⟩ := hf.exists_eq_measurable_comp
  obtain ⟨g', hg', rfl⟩ := hg.exists_eq_measurable_comp
  have h (μ : Measure 𝓧) [IsProbabilityMeasure μ] {H : (Fin N → 𝓧) → ℝ≥0∞}
      (hH : Measurable H) :
      ∫⁻ ω, (H ∘ initSeg N) ω ∂Measure.infinitePi (fun _ ↦ μ) =
        ∫⁻ x, H x ∂Measure.pi (fun _ : Fin N ↦ μ) :=
    (measurePreserving_initSeg μ N).lintegral_comp hH
  rw [h Q hf', h Q hg']
  refine lintegral_pi_eq_of_add_sum_eq_sum hQ (fun w hw ↦ ?_) fun w hw ↦ ?_
  · have := isProbabilityMeasure_sum_smul (P := P) hw
    rw [← h _ hf', ← h _ hg']
    exact hfg w hw
  · have := isProbabilityMeasure_sum_smul (P := P) hw
    rw [← h _ hf']
    exact hf_ne w hw

section Update

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- **A product with one factor replaced.** The product of probability measures `μ i` in which the
factor `j` is replaced by `ν` is the law of a point drawn from the product of the `μ i`, in which
the coordinate `j` is replaced by an independent draw from `ν`. -/
theorem infinitePi_update [DecidableEq ι] (μ : (i : ι) → Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (j : ι) (ν : Measure (X j)) [IsProbabilityMeasure ν] :
    infinitePi (Function.update μ j ν) =
      ((infinitePi μ).prod ν).map fun p ↦ Function.update p.1 j p.2 := by
  have : ∀ i, IsProbabilityMeasure (Function.update μ j ν i) := fun i ↦ by
    rcases eq_or_ne i j with rfl | h
    · rwa [Function.update_self]
    · rw [Function.update_of_ne h]
      infer_instance
  refine (eq_infinitePi _ fun s t ht ↦ ?_).symm
  rw [map_apply measurable_update' (.pi s.countable_toSet fun i _ ↦ ht i)]
  have h_pre : (fun p : (Π i, X i) × X j ↦ Function.update p.1 j p.2) ⁻¹' (s : Set ι).pi t =
      ((s.erase j : Finset ι) : Set ι).pi t ×ˢ (if j ∈ s then t j else Set.univ) := by
    ext ⟨ω, x⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe, Finset.mem_erase]
    refine ⟨fun h ↦ ⟨fun i hi ↦ ?_, ?_⟩, fun h i hi ↦ ?_⟩
    · simpa [Function.update_of_ne hi.1] using h i hi.2
    · split_ifs with hj
      · simpa using h j hj
      · exact Set.mem_univ x
    · rcases eq_or_ne i j with rfl | hij
      · simpa [hi] using h.2
      · simpa [Function.update_of_ne hij] using h.1 i ⟨hij, hi⟩
  rw [h_pre, prod_prod, infinitePi_pi _ fun i _ ↦ ht i]
  by_cases hj : j ∈ s
  · rw [ite_eq_left hj, ← Finset.mul_prod_erase s _ hj, Function.update_self, mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun i hi ↦ by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  · rw [ite_eq_right hj, measure_univ, mul_one, Finset.erase_eq_of_notMem hj]
    exact Finset.prod_congr rfl fun i hi ↦ by
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]

/-- **Tonelli's theorem at one coordinate.** The integral under a product of probability measures
in which the factor `j` is `ν` is the integral, in the coordinate `j` under `ν`, of the integral
under the product of the `μ i` with the coordinate `j` replaced. -/
theorem lintegral_infinitePi_update [DecidableEq ι] (μ : (i : ι) → Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (j : ι) (ν : Measure (X j)) [IsProbabilityMeasure ν]
    {f : (Π i, X i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f ω ∂infinitePi (Function.update μ j ν) =
      ∫⁻ x, ∫⁻ ω, f (Function.update ω j x) ∂infinitePi μ ∂ν := by
  rw [infinitePi_update, lintegral_map hf measurable_update']
  exact lintegral_prod_symm _ (hf.comp measurable_update').aemeasurable

/-- The integral of a function of finitely many coordinates under a product of probability
measures only depends on the factors of these coordinates. -/
theorem lintegral_infinitePi_congr_of_dependsOn {μ μ' : (i : ι) → Measure (X i)}
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (μ' i)] {s : Finset ι}
    (h : ∀ i ∈ s, μ i = μ' i) {f : (Π i, X i) → ℝ≥0∞} (hf : Measurable f)
    (hfs : DependsOn f s) :
    ∫⁻ ω, f ω ∂infinitePi μ = ∫⁻ ω, f ω ∂infinitePi μ' := by
  classical
  rcases isEmpty_or_nonempty (Π i, X i) with hX | ⟨⟨x₀⟩⟩
  · simp [lintegral_of_isEmpty]
  set g : (Π i : s, X i) → ℝ≥0∞ := fun y ↦ f (Function.updateFinset x₀ s y)
  have hfg (ω : Π i, X i) : f ω = g (s.restrict ω) :=
    hfs fun i hi ↦ by simp [Function.updateFinset, Finset.mem_coe.1 hi]
  have hg : Measurable g := hf.comp measurable_updateFinset
  simp_rw [hfg]
  rw [lintegral_restrict_infinitePi μ hg, lintegral_restrict_infinitePi μ' hg]
  congr 2
  exact funext fun i ↦ h i i.property

end Update

end MeasureTheory.Measure

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

open Filter in
/-- **Functions of bounded mean are eventually below every exponential.** If the functions `F n`
of `n` observations have mean at most `C < ∞` under the product law `P ^ n`, then for every
`ε > 0`, almost surely under the i.i.d. law of `P`, `F n < exp (n ε)` at the first `n`
observations for all large `n`. Markov's inequality bounds the probability that
`exp (n ε) ≤ F n` by `C exp (- n ε)`, and the Borel–Cantelli lemma applies. -/
lemma ae_eventually_lt_exp_of_lintegral_le (P : Measure 𝓧) [IsProbabilityMeasure P]
    {F : (n : ℕ) → (Fin n → 𝓧) → ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) (Measure.pi fun _ : Fin n ↦ P)) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hFC : ∀ n, ∫⁻ x, F n x ∂(Measure.pi fun _ : Fin n ↦ P) ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ P), ∀ᶠ n : ℕ in atTop,
      F n (initSeg n ω) < ENNReal.ofReal (Real.exp (n * ε)) := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ P)
  set A : ℕ → Set (ℕ → 𝓧) := fun n ↦
    {ω | ENNReal.ofReal (Real.exp (n * ε)) ≤ F n (initSeg n ω)}
  -- Markov's inequality
  have hA (n : ℕ) : μ (A n) ≤ C * ENNReal.ofReal (Real.exp (-ε)) ^ n := by
    have hmap := (measurePreserving_initSeg P n).map_eq
    have hFm : AEMeasurable (F n) (μ.map (initSeg n)) := hmap ▸ hF n
    calc μ (A n) ≤ (∫⁻ ω, F n (initSeg n ω) ∂μ) / ENNReal.ofReal (Real.exp (n * ε)) :=
        meas_ge_le_lintegral_div (hFm.comp_measurable (measurable_initSeg n))
          (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top
    _ ≤ C / ENNReal.ofReal (Real.exp (n * ε)) := by
      gcongr
      rw [← lintegral_map' hFm (measurable_initSeg n).aemeasurable, hmap]
      exact hFC n
    _ = C * ENNReal.ofReal (Real.exp (-ε)) ^ n := by
      rw [div_eq_mul_inv, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_natCast_mul,
        ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
      ring_nf
  -- the Borel–Cantelli lemma
  have hsum : ∑' n, μ (A n) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hA)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top hC (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 ?_).ne')
    rw [ENNReal.ofReal_lt_one]
    exact Real.exp_lt_one_iff.2 (neg_lt_zero.2 hε)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  simpa only [A, Set.mem_ofPred_eq, not_le] using hn

end MeasureTheory

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
    -- the second family is read off at the only point `n + 1` of `{n + 1}`
    simpa [Function.comp_def, Preorder.frestrictLe, Finset.restrict_def] using
      h.comp measurable_id (measurable_pi_apply ⟨n + 1, Finset.mem_singleton_self _⟩)
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
