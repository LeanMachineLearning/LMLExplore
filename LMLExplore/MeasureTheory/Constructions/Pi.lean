/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ConditionalProbability
import LMLExplore.Algebra.BigOperators.Field
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import TauCeti.MeasureTheory.Constructions.Pi

/-!
# Product measures: laws of coordinatewise images, restricted factors, mixtures and bounds by lines

Under the product measure `Measure.pi μ`, the law of a function `f` of the coordinatewise images
`X i (y i)` is the law of `f` under the product of the laws of the `X i`. For example, the law of
the empirical mean of a statistic `X` of independent samples of `P` is the law of the empirical
mean of independent samples of the law of `X`.

Restricting every factor of a product of copies of `μ` to a set `B` of finite positive measure
gives the product of the conditional measures `μ[|B]`, scaled by `μ(B)` to the number of factors.

The product of copies of a multiple `s • ν` is `s ^ card ι` times the product of copies of `ν`, and
the product of copies of a finite mixture `∑ k, w k • R k` is the mixture of the products
`Measure.pi (fun i ↦ R (e i))` over the assignments `e : ι → κ`, with weights `∏ i, w (e i)`.
Expanding the product of copies of `Q + t • B` this way makes its integrals polynomials in `t`,
which is how equal integrals under the products of copies of the convex combinations of finitely
many measures `P i` transfer to every probability measure `Q` with
`Q + ∑ i, b i • P i = ∑ i, c i • P i`. This polarization argument is the proof of
[EVR26, Note 03, Theorem 1], and the lemmas are adapted from
`EValuesResearch/Results/TestMartingaleConverse.lean` (commit `6f05c5f`) in the paper project
`RemyDegenne/evalues_research`.

Under a product of probability measures, a measurable set whose lines along one coordinate `i`
all have `μ i`-measure at most `c` has product measure at most `c`, by resampling the coordinate
`i` and integrating the measures of the lines.

## Main statements

* `MeasureTheory.Measure.map_pi_comp_eq_map_pi_map`:
  `(Measure.pi μ).map (fun y ↦ f fun i ↦ X i (y i)) = (Measure.pi fun i ↦ (μ i).map (X i)).map f`.
* `MeasureTheory.Measure.pi_restrict_eq_pow_smul_pi_cond`:
  `Measure.pi (fun _ ↦ μ.restrict B) = μ B ^ card ι • Measure.pi (fun _ ↦ μ[|B])`.
* `MeasureTheory.Measure.pi_const_smul`:
  `Measure.pi (fun _ ↦ s • ν) = s ^ card ι • Measure.pi (fun _ ↦ ν)`.
* `MeasureTheory.Measure.pi_sum_smul`, `MeasureTheory.Measure.lintegral_pi_sum_smul`:
  `Measure.pi (fun _ ↦ ∑ k, w k • R k) = ∑ e, (∏ i, w (e i)) • Measure.pi (fun i ↦ R (e i))`, and
  the corresponding expansion of integrals.
* `MeasureTheory.Measure.lintegral_pi_eq_of_add_sum_eq_sum`: if `Q + ∑ i, b i • P i =
  ∑ i, c i • P i`, two functions with equal integrals under the products of copies of every convex
  combination of the `P i`, finite for the first one, have equal integrals under the product of
  copies of `Q`.
* `MeasureTheory.Measure.pi_eval_preimage_le`: for measures of mass at most `1`, the product
  measure of the cylinder `{y | y i ∈ s}` is at most `μ i s`, for every set `s`.
* `MeasureTheory.Measure.pi_le_of_forall_measure_update_preimage_le`: under a product of
  probability measures, a measurable set whose lines `{t | update x i t ∈ E}` along one coordinate
  `i` all have `μ i`-measure at most `c` has product measure at most `c`.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 03, *Converse of the power-one theorem for test martingales*,
  Theorem 1.
-/

public section

open scoped ENNReal NNReal

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

/-- The product of copies of a multiple `s • ν` of a σ-finite measure is `s ^ card ι` times the
product of copies of `ν`. -/
lemma pi_const_smul {α : Type*} {mα : MeasurableSpace α} (ν : Measure α) [SigmaFinite ν]
    (s : ℝ≥0) :
    Measure.pi (fun _ : ι ↦ s • ν) = s ^ Fintype.card ι • Measure.pi (fun _ : ι ↦ ν) := by
  refine Measure.pi_eq fun A hA ↦ ?_
  simp only [smul_apply, Measure.pi_pi, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow]

/-- **Product of copies of a mixture.** The product of copies of a finite mixture
`∑ k, w k • R k` of finite measures is the mixture of the products `Measure.pi (fun i ↦ R (e i))`
over the assignments `e : ι → κ`, with weights `∏ i, w (e i)`. -/
lemma pi_sum_smul [DecidableEq ι] {α κ : Type*} {mα : MeasurableSpace α} [Fintype κ]
    {R : κ → Measure α} [∀ k, IsFiniteMeasure (R k)] (w : κ → ℝ≥0) :
    Measure.pi (fun _ : ι ↦ ∑ k, w k • R k) =
      ∑ e : ι → κ, (∏ i, (w (e i) : ℝ≥0∞)) • Measure.pi (fun i ↦ R (e i)) := by
  refine Measure.pi_eq fun A hA ↦ ?_
  simp only [sum_apply, smul_apply, Measure.pi_pi, smul_eq_mul, Measure.nnreal_smul_coe_apply,
    Fintype.prod_sum, Finset.prod_mul_distrib]

/-- The integral under the product of copies of a finite mixture `∑ k, w k • R k` of finite
measures is a polynomial in the weights: the sum over the assignments `e : ι → κ` of
`∏ i, w (e i)` times the integral under `Measure.pi (fun i ↦ R (e i))`. -/
lemma lintegral_pi_sum_smul [DecidableEq ι] {α κ : Type*} {mα : MeasurableSpace α} [Fintype κ]
    {R : κ → Measure α} [∀ k, IsFiniteMeasure (R k)] (w : κ → ℝ≥0) (F : (ι → α) → ℝ≥0∞) :
    ∫⁻ x, F x ∂Measure.pi (fun _ : ι ↦ ∑ k, w k • R k) =
      ∑ e : ι → κ, (∏ i, (w (e i) : ℝ≥0∞)) * ∫⁻ x, F x ∂Measure.pi (fun i ↦ R (e i)) := by
  rw [pi_sum_smul]
  simp only [lintegral_finsetSum_measure, lintegral_smul_measure, smul_eq_mul]

/-- **Identity theorem for the polynomials of the polarization.** Two families `a` and `a'` of
finite coefficients indexed by `ι → Bool` whose polynomials
`t ↦ ∑ e, (∏ i, bif e i then t else 1) * a e` agree for every `t > 1` agree for every `t ≥ 0`. -/
private lemma sum_prod_bif_mul_eq_of_one_lt [DecidableEq ι] {a a' : (ι → Bool) → ℝ≥0∞}
    (ha : ∀ e, a e ≠ ∞) (ha' : ∀ e, a' e ≠ ∞)
    (h : ∀ t : ℝ≥0, 1 < t → ∑ e, (∏ i, ((bif e i then t else 1 : ℝ≥0) : ℝ≥0∞)) * a e =
      ∑ e, (∏ i, ((bif e i then t else 1 : ℝ≥0) : ℝ≥0∞)) * a' e) (t : ℝ≥0) :
    ∑ e, (∏ i, ((bif e i then t else 1 : ℝ≥0) : ℝ≥0∞)) * a e =
      ∑ e, (∏ i, ((bif e i then t else 1 : ℝ≥0) : ℝ≥0∞)) * a' e := by
  have hfin (c : (ι → Bool) → ℝ≥0∞) (hc : ∀ e, c e ≠ ∞) (t : ℝ≥0) (e : ι → Bool) :
      (∏ i, ((bif e i then t else 1 : ℝ≥0) : ℝ≥0∞)) * c e ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.prod_ne_top fun _ _ ↦ ENNReal.coe_ne_top) (hc e)
  -- the real polynomials
  set φ : ((ι → Bool) → ℝ≥0∞) → ℝ → ℝ :=
    fun c x ↦ ∑ e : ι → Bool, (∏ i, bif e i then x else 1) * (c e).toReal
  have hφ_eq (c : (ι → Bool) → ℝ≥0∞) (hc : ∀ e, c e ≠ ∞) (t : ℝ≥0) :
      φ c t = (∑ e, (∏ i, ((bif e i then t else 1 : ℝ≥0) : ℝ≥0∞)) * c e).toReal := by
    rw [ENNReal.toReal_sum fun e _ ↦ hfin c hc t e]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    cases e i <;> simp
  have han (c : (ι → Bool) → ℝ≥0∞) : AnalyticOnNhd ℝ (φ c) Set.univ := fun x _ ↦
    Finset.analyticAt_fun_sum _ fun e _ ↦ (Finset.analyticAt_fun_prod _ fun i _ ↦ by
      cases e i
      · exact analyticAt_const
      · exact analyticAt_id).mul analyticAt_const
  -- they agree on `(1, ∞)`, hence everywhere
  have hφ : φ a = φ a' := (han a).eq_of_eventuallyEq (han a') (z₀ := 2) <| by
    filter_upwards [lt_mem_nhds (by norm_num : (1 : ℝ) < 2)] with x hx
    have hx' : (x.toNNReal : ℝ) = x := Real.coe_toNNReal _ (by linarith)
    have h1 : 1 < x.toNNReal := by
      rw [← NNReal.coe_lt_coe, hx', NNReal.coe_one]
      exact hx
    rw [← hx', hφ_eq a ha, hφ_eq a' ha', h _ h1]
  have ht := congrFun hφ t
  rw [hφ_eq a ha, hφ_eq a' ha'] at ht
  exact (ENNReal.toReal_eq_toReal_iff' (ENNReal.sum_ne_top.2 fun e _ ↦ hfin a ha t e)
    (ENNReal.sum_ne_top.2 fun e _ ↦ hfin a' ha' t e)).1 ht

/-- **Polarization.** Let `Q` be a probability measure and `P k` finite measures with
`Q + ∑ k, b k • P k = ∑ k, c k • P k`. If two functions on `ι → α` have equal integrals under the
product of copies of every convex combination of the `P k`, finite for the first function, then
they have equal integrals under the product of copies of `Q`. -/
lemma lintegral_pi_eq_of_add_sum_eq_sum {α κ : Type*} {mα : MeasurableSpace α} [Fintype κ]
    {P : κ → Measure α} [∀ k, IsFiniteMeasure (P k)] {b c : κ → ℝ≥0} {Q : Measure α}
    [IsProbabilityMeasure Q] (hQ : Q + ∑ k, b k • P k = ∑ k, c k • P k)
    {F G : (ι → α) → ℝ≥0∞}
    (hFG : ∀ w : κ → ℝ≥0, ∑ k, w k = 1 →
      ∫⁻ x, F x ∂Measure.pi (fun _ ↦ ∑ k, w k • P k) =
        ∫⁻ x, G x ∂Measure.pi (fun _ ↦ ∑ k, w k • P k))
    (hF : ∀ w : κ → ℝ≥0, ∑ k, w k = 1 →
      ∫⁻ x, F x ∂Measure.pi (fun _ ↦ ∑ k, w k • P k) ≠ ∞) :
    ∫⁻ x, F x ∂Measure.pi (fun _ : ι ↦ Q) = ∫⁻ x, G x ∂Measure.pi (fun _ : ι ↦ Q) := by
  classical
  set B := ∑ k, b k • P k with hB
  -- `Q + t • B` as the mixture of `R true = B` and `R false = Q` with weights `t` and `1`
  set R : Bool → Measure α := fun k ↦ bif k then B else Q with hR
  have : IsFiniteMeasure B := by rw [hB]; infer_instance
  have : ∀ k, IsFiniteMeasure (R k) := fun k ↦ by
    cases k <;> simp only [hR, Bool.cond_false, Bool.cond_true] <;> infer_instance
  set A : ((ι → α) → ℝ≥0∞) → (ι → Bool) → ℝ≥0∞ :=
    fun H e ↦ ∫⁻ x, H x ∂Measure.pi (fun i ↦ R (e i))
  have hpoly (H : (ι → α) → ℝ≥0∞) (t : ℝ≥0) :
      ∫⁻ x, H x ∂Measure.pi (fun _ : ι ↦ Q + t • B) =
        ∑ e : ι → Bool, (∏ i, ((bif e i then t else 1 : ℝ≥0) : ℝ≥0∞)) * A H e := by
    have hmix : Q + t • B = ∑ k, (bif k then t else 1 : ℝ≥0) • R k := by simp [hR, add_comm]
    rw [hmix, lintegral_pi_sum_smul]
  -- for `t ≥ 1`, `Q + t • B` is a positive multiple of a convex combination of the `P k`
  have hgood (t : ℝ≥0) (ht : 1 ≤ t) :
      ∫⁻ x, F x ∂Measure.pi (fun _ : ι ↦ Q + t • B) =
        ∫⁻ x, G x ∂Measure.pi (fun _ : ι ↦ Q + t • B) ∧
      ∫⁻ x, F x ∂Measure.pi (fun _ : ι ↦ Q + t • B) ≠ ∞ := by
    have hμ : Q + t • B = ∑ k, (c k + (t - 1) * b k) • P k := by
      calc Q + t • B = (Q + B) + (t - 1) • B := by
            conv_lhs => rw [← add_tsub_cancel_of_le ht, add_smul, one_smul]
            rw [add_assoc]
        _ = ∑ k, (c k + (t - 1) * b k) • P k := by
            rw [hQ, hB, Finset.smul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun k _ ↦ by rw [smul_smul, ← add_smul]
    have hs : ∑ k, (c k + (t - 1) * b k) ≠ 0 := by
      intro h0
      have h : Q + t • B = 0 := by
        rw [hμ]
        exact Finset.sum_eq_zero fun k hk ↦ by rw [Finset.sum_eq_zero_iff.1 h0 k hk, zero_smul]
      have h' := congrArg (· Set.univ) h
      simp at h'
    have hv : ∑ k, (c k + (t - 1) * b k) / ∑ j, (c j + (t - 1) * b j) = 1 := by
      rw [← Finset.sum_div, div_self hs]
    rw [hμ, Finset.sum_smul_eq_smul_sum_div_smul hs, pi_const_smul, lintegral_smul_measure,
      lintegral_smul_measure, hFG _ hv]
    refine ⟨rfl, ?_⟩
    rw [ENNReal.smul_def, smul_eq_mul, ← hFG _ hv]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (hF _ hv)
  -- the coefficients of the polynomials are finite, as the case `t = 1` shows
  have hA_ne (H : (ι → α) → ℝ≥0∞)
      (hH : ∫⁻ x, H x ∂Measure.pi (fun _ : ι ↦ Q + (1 : ℝ≥0) • B) ≠ ∞) (e : ι → Bool) :
      A H e ≠ ∞ := by
    have hw1 (k : Bool) : (bif k then (1 : ℝ≥0) else 1) = 1 := by cases k <;> rfl
    rw [hpoly] at hH
    simp only [hw1, ENNReal.coe_one, Finset.prod_const_one, one_mul] at hH
    exact ENNReal.sum_ne_top.1 hH e (Finset.mem_univ e)
  obtain ⟨h1eq, h1ne⟩ := hgood 1 le_rfl
  have h0 := sum_prod_bif_mul_eq_of_one_lt (hA_ne F h1ne) (hA_ne G (by rwa [← h1eq]))
    (fun t ht ↦ by rw [← hpoly, ← hpoly]; exact (hgood t ht.le).1) 0
  rw [← hpoly, ← hpoly] at h0
  simpa only [zero_smul, add_zero] using h0

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
