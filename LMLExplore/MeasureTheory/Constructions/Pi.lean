/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Probability.ConditionalProbability
import TauCeti.MeasureTheory.Constructions.Pi
import TauCeti.MeasureTheory.Integral.Pi

/-!
# Product measures: laws of coordinatewise images, restricted factors and bounds by lines

Under the product measure `Measure.pi μ`, the law of a function `f` of the coordinatewise images
`X i (y i)` is the law of `f` under the product of the laws of the `X i`. For example, the law of
the empirical mean of a statistic `X` of independent samples of `P` is the law of the empirical
mean of independent samples of the law of `X`.

Restricting every factor of a product of copies of `μ` to a set `B` of finite positive measure
gives the product of the conditional measures `μ[|B]`, scaled by `μ(B)` to the number of factors.

Under a product of probability measures, a measurable set whose lines along one coordinate `i`
all have `μ i`-measure at most `c` has product measure at most `c`, by resampling the coordinate
`i` and integrating the measures of the lines.

The product of finite mixtures of measures is the mixture, over the choices of one component for
each coordinate, of the products of the components. For measurable maps `G i` to finite
measures, the product `Measure.pi fun i ↦ G i (x i)` depends measurably on `x`, and binding a
product measure along it gives the product of the binds: an independent sample from `μ i` followed
by independent draws from the `G i (x i)` is an independent sample from the mixtures.

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
* `MeasureTheory.Measure.pi_sum_smul`: the product of the finite mixtures `∑ k, w i k • μ i k` is
  `∑ σ, (∏ i, w i (σ i)) • Measure.pi fun i ↦ μ i (σ i)`.
* `MeasureTheory.Measure.measurable_pi_comp`: `x ↦ Measure.pi fun i ↦ G i (x i)` is measurable.
* `MeasureTheory.Measure.pi_bind_pi`: binding `Measure.pi μ` along
  `x ↦ Measure.pi fun i ↦ G i (x i)` gives `Measure.pi fun i ↦ (μ i).bind (G i)`.
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

/-! ### Products of mixtures -/

/-- **Products of finite mixtures.** The product of the finite mixtures `∑ k, w i k • μ i k` is the
mixture of the products `Measure.pi fun i ↦ μ i (σ i)` over the choices `σ` of a component for
each coordinate, with weights `∏ i, w i (σ i)`. -/
lemma pi_sum_smul [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)] (w : ∀ i, κ i → ℝ≥0∞)
    (μ : ∀ i, κ i → Measure (Ω i)) [∀ i, SigmaFinite (∑ k, w i k • μ i k)]
    [∀ i k, SigmaFinite (μ i k)] :
    Measure.pi (fun i ↦ ∑ k, w i k • μ i k) =
      ∑ σ : ∀ i, κ i, (∏ i, w i (σ i)) • Measure.pi fun i ↦ μ i (σ i) := by
  refine Measure.pi_eq fun s _ ↦ ?_
  simp only [_root_.sum_apply, smul_apply, smul_eq_mul, Measure.pi_pi, Fintype.prod_sum,
    ← Finset.prod_mul_distrib]

/-- The product of the finite measures `G i (x i)` depends measurably on `x` when each `G i` is
measurable. -/
lemma measurable_pi_comp {G : ∀ i, Ω i → Measure (𝓨 i)} [∀ i x, IsFiniteMeasure (G i x)]
    (hG : ∀ i, Measurable (G i)) :
    Measurable fun x : ∀ i, Ω i ↦ Measure.pi fun i ↦ G i (x i) := by
  have h_box (s : ∀ i, Set (𝓨 i)) (hs : ∀ i, MeasurableSet (s i)) :
      Measurable fun x : ∀ i, Ω i ↦ Measure.pi (fun i ↦ G i (x i)) (Set.univ.pi s) := by
    simp_rw [Measure.pi_pi]
    exact Finset.measurable_prod _ fun i _ ↦
      ((measurable_coe (hs i)).comp (hG i)).comp (measurable_pi_apply i)
  refine Measurable.measure_of_isPiSystem generateFrom_pi.symm isPiSystem_pi ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact h_box s fun i ↦ hs i (Set.mem_univ i)
  · simpa using h_box (fun _ ↦ Set.univ) fun _ ↦ .univ

/-- **Binding a product measure coordinatewise.** Binding `Measure.pi μ` along the products of
the finite measures `G i (x i)` gives the product of the binds `(μ i).bind (G i)`: for probability
measures, an independent sample of the `μ i`, followed by independent draws from the
`G i (x i)`, is an independent sample of the mixtures. -/
lemma pi_bind_pi {μ : ∀ i, Measure (Ω i)} [∀ i, SigmaFinite (μ i)]
    {G : ∀ i, Ω i → Measure (𝓨 i)} [∀ i x, IsFiniteMeasure (G i x)]
    [∀ i, SigmaFinite ((μ i).bind (G i))] (hG : ∀ i, Measurable (G i)) :
    (Measure.pi μ).bind (fun x ↦ Measure.pi fun i ↦ G i (x i)) =
      Measure.pi fun i ↦ (μ i).bind (G i) := by
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  rw [bind_apply (.univ_pi hs) (measurable_pi_comp hG).aemeasurable]
  simp_rw [Measure.pi_pi]
  rw [TauCeti.lintegral_fintype_prod_eq_prod μ (f := fun i x ↦ G i x (s i))
    fun i ↦ (measurable_coe (hs i)).comp (hG i)]
  exact Finset.prod_congr rfl fun i _ ↦ (bind_apply (hs i) (hG i).aemeasurable).symm

end MeasureTheory.Measure
