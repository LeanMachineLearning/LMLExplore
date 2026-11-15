/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.Prod
import LMLExplore.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Algebra.BigOperators.Fin
import TauCeti.MeasureTheory.Constructions.Pi
import TauCeti.MeasureTheory.Integral.Pi

/-!
# Product measures: coordinatewise images, restricted factors, bounds by lines, `Fin 2` integrals

Under the product measure `Measure.pi μ`, the law of a function `f` of the coordinatewise images
`X i (y i)` is the law of `f` under the product of the laws of the `X i`. For example, the law of
the empirical mean of a statistic `X` of independent samples of `P` is the law of the empirical
mean of independent samples of the law of `X`.

Restricting every factor of a product of copies of `μ` to a set `B` of finite positive measure
gives the product of the conditional measures `μ[|B]`, scaled by `μ(B)` to the number of factors.

Under a product of probability measures, a measurable set whose lines along one coordinate `i`
all have `μ i`-measure at most `c` has product measure at most `c`, by resampling the coordinate
`i` and integrating the measures of the lines.

An integral against a product of two σ-finite measures indexed by `Fin 2` is an iterated
integral, and the integral of a function of the images of the two coordinates under a map to a
finite type is a double sum over the masses of the fibres.

## Main statements

* `MeasureTheory.Measure.map_pi_comp_eq_map_pi_map`:
  `(Measure.pi μ).map (fun y ↦ f fun i ↦ X i (y i)) = (Measure.pi fun i ↦ (μ i).map (X i)).map f`.
* `MeasureTheory.Measure.pi_restrict_eq_pow_smul_pi_cond`:
  `Measure.pi (fun _ ↦ μ.restrict B) = μ B ^ card ι • Measure.pi (fun _ ↦ μ[|B])`.
* `MeasureTheory.Measure.pi_eval_preimage_le`: for measures of mass at most `1`, the product
  measure of the cylinder `{y | y i ∈ s}` is at most `μ i s`, for every set `s`.
* `MeasureTheory.Measure.pi_le_of_forall_measure_update_preimage_le`: under a product of
  probability measures, a measurable set whose lines `{t | update x i t ∈ E}` along one coordinate
  `i` all have `μ i`-measure at most `c` has product measure at most `c`.
* `MeasureTheory.lintegral_pi_fin_two`:
  `∫⁻ e, F e ∂Measure.pi μ = ∫⁻ x, ∫⁻ y, F ![x, y] ∂μ 1 ∂μ 0` for `μ : Fin 2 → Measure α`.
* `MeasureTheory.lintegral_pi_fin_two_mul`: the integral of `u (e 0) * v (e 1)` is the product of
  the integrals of `u` and `v`.
* `MeasureTheory.lintegral_pi_fin_two_comp_eq_sum`: the integral of `f (φ (e 0)) (φ (e 1))`, for a
  map `φ` to a finite type, is `∑ i, ∑ j, f i j * μ 0 (φ ⁻¹' {i}) * μ 1 (φ ⁻¹' {j})`.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {ι : Type*} [Fintype ι] {Ω 𝓨 : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
  [∀ i, MeasurableSpace (𝓨 i)] {β : Type*} {mβ : MeasurableSpace β}

/-- The law under a product measure of a function `f` of the coordinatewise images `X i (y i)` is
the law of `f` under the product of the laws of the `X i`. -/
lemma map_pi_comp_eq_map_pi_map {μ : ∀ i, Measure (Ω i)} {X : ∀ i, Ω i → 𝓨 i}
    [hμ : ∀ i, SigmaFinite ((μ i).map (X i))] (hX : ∀ i, AEMeasurable (X i) (μ i))
    {f : (∀ i, 𝓨 i) → β} (hf : AEMeasurable f (Measure.pi fun i ↦ (μ i).map (X i))) :
    (Measure.pi μ).map (fun y ↦ f fun i ↦ X i (y i)) =
      (Measure.pi fun i ↦ (μ i).map (X i)).map f := by
  have (i : ι) := (hμ i).of_map _ (hX i)
  have hX' : AEMeasurable (fun (y : ∀ i, Ω i) i ↦ X i (y i)) (Measure.pi μ) :=
    .of_eval fun i ↦ (hX i).comp_quasiMeasurePreserving (quasiMeasurePreserving_eval _ i)
  rw [← pi_map_pi hX] at hf ⊢
  rw [AEMeasurable.map_map_of_aemeasurable hf hX']
  rfl

open ProbabilityTheory in
/-- Restricting every factor of a product of copies of `μ` to a set `B` of finite positive measure
gives the product of the conditional measures `μ[|B]`, scaled by `μ(B) ^ card ι`. -/
lemma pi_restrict_eq_pow_smul_pi_cond {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [SigmaFinite μ] {B : Set α} (hB0 : μ B ≠ 0) (hB : μ B ≠ ⊤) :
    Measure.pi (fun _ : ι ↦ μ.restrict B) =
      μ B ^ Fintype.card ι • Measure.pi (fun _ : ι ↦ μ[|B]) := by
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.card_univ, ← Finset.prod_const,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [cond_apply' (hs i), Measure.restrict_apply (hs i), ← mul_assoc,
    ENNReal.mul_inv_cancel hB0 hB, one_mul, Set.inter_comm]

/-- For measures of mass at most `1`, the product measure of the cylinder `eval i ⁻¹' s` of a set
`s`, measurable or not, is at most `μ i s`. -/
lemma pi_eval_preimage_le {μ : ∀ i, Measure (Ω i)} [∀ i, IsZeroOrProbabilityMeasure (μ i)]
    (i : ι) (s : Set (Ω i)) :
    Measure.pi μ (Function.eval i ⁻¹' s) ≤ μ i s := by
  classical
  rw [← Set.univ_pi_update_univ, Measure.pi_pi,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i), Function.update_self]
  exact mul_le_of_le_one_right' (Finset.prod_le_one fun j _ ↦ prob_le_one)

/-- **Bounding a product measure by its lines.** Under a product of probability measures, a
measurable set `E` whose lines `{t | update x i t ∈ E}` along one coordinate `i` all have
`μ i`-measure at most `c` has measure at most `c`: resampling the coordinate `i` preserves the
product measure, and Fubini integrates the measures of the lines. -/
lemma pi_le_of_forall_measure_update_preimage_le [DecidableEq ι] {μ : ∀ i, Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] {E : Set (∀ i, Ω i)} (hE : MeasurableSet E) (i : ι)
    {c : ℝ≥0∞} (h : ∀ x, μ i (Function.update x i ⁻¹' E) ≤ c) :
    Measure.pi μ E ≤ c := by
  rw [← (TauCeti.measurePreserving_update_prod_pi μ i).measure_preimage hE.nullMeasurableSet,
    Measure.prod_apply (measurable_update' hE)]
  exact (lintegral_mono fun x ↦ h x).trans_eq (by simp)

end MeasureTheory.Measure

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

/-- A function `f (φ (e 0)) (φ (e 1))` of the images of the two coordinates under a measurable map
`φ` to a finite type is measurable. -/
lemma measurable_pi_fin_two_comp {κ β : Type*} [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] [MeasurableSpace β] {φ : α → κ} (hφ : Measurable φ)
    (f : κ → κ → β) : Measurable fun e : Fin 2 → α ↦ f (φ (e 0)) (φ (e 1)) :=
  (measurable_of_finite (Function.uncurry f)).comp
    ((hφ.comp (measurable_pi_apply 0)).prodMk (hφ.comp (measurable_pi_apply 1)))

/-- The integral of `f (φ (e 0)) (φ (e 1))` against a product of two σ-finite measures, where `φ`
takes values in a finite type, in terms of the masses of the fibres of `φ`. -/
lemma lintegral_pi_fin_two_comp_eq_sum {κ : Type*} [Fintype κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (μ : Fin 2 → Measure α) [∀ i, SigmaFinite (μ i)]
    {φ : α → κ} (hφ : Measurable φ) (f : κ → κ → ℝ≥0∞) :
    ∫⁻ e, f (φ (e 0)) (φ (e 1)) ∂Measure.pi μ =
      ∑ i, ∑ j, f i j * μ 0 (φ ⁻¹' {i}) * μ 1 (φ ⁻¹' {j}) := by
  rw [lintegral_pi_fin_two μ (measurable_pi_fin_two_comp hφ f).aemeasurable]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [lintegral_comp_eq_sum_measure_preimage_singleton hφ.aemeasurable (f _)]
  rw [lintegral_comp_eq_sum_measure_preimage_singleton hφ.aemeasurable
    (fun i ↦ ∑ j, f i j * μ 1 (φ ⁻¹' {j}))]
  simp_rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

end MeasureTheory
