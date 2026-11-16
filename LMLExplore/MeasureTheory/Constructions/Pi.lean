/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Probability.ConditionalProbability
import LMLExplore.Algebra.BigOperators.Field
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import Statlib.ForMathlib.MeasureTheory.Measure.Decomposition.RNDerivProd
import TauCeti.MeasureTheory.Constructions.Pi
import TauCeti.MeasureTheory.Integral.Pi

/-!
# Measures on products: monotonicity, laws of coordinatewise images, restricted factors, mixtures,
bounds by lines, binds and fixed prefixes

The product of finite measures is monotone in its factors.

Under the product measure `Measure.pi μ`, the law of a function `f` of the coordinatewise images
`X i (y i)` is the law of `f` under the product of the laws of the `X i`. For example, the law of
the empirical mean of a statistic `X` of independent samples of `P` is the law of the empirical
mean of independent samples of the law of `X`.

Restricting every factor of a product of copies of `μ` to a set `B` of finite positive measure
gives the product of the conditional measures `μ[|B]`, scaled by `μ(B)` to the number of factors.

The product of copies of a multiple `s • ν` is `s ^ card ι` times the product of copies of `ν`.
The product of finite mixtures `∑ k, w i k • μ i k` of measures is the mixture, over the choices
`σ` of one component for each coordinate, of the products `Measure.pi fun i ↦ μ i (σ i)`, with
weights `∏ i, w i (σ i)`; in particular the product of copies of a finite mixture
`∑ k, w k • R k` is the mixture of the products `Measure.pi (fun i ↦ R (e i))` over the
assignments `e : ι → κ`, with weights `∏ i, w (e i)`. Expanding the product of copies of
`Q + t • B` this way makes its integrals polynomials in `t`, which is how equal integrals under
the products of copies of the convex combinations of finitely many measures `P i` transfer to
every probability measure `Q` with `Q + ∑ i, b i • P i = ∑ i, c i • P i`.
This polarization argument is the proof of [EVR26, Note 03, Theorem 1], and the lemmas are
adapted from `EValuesResearch/Results/TestMartingaleConverse.lean` (commit `6f05c5f`) in the
paper project `RemyDegenne/evalues_research`.

Under a product of probability measures, a measurable set whose lines along one coordinate `i`
all have `μ i`-measure at most `c` has product measure at most `c`, by resampling the coordinate
`i` and integrating the measures of the lines.

For measurable maps `G i` to finite measures, the product `Measure.pi fun i ↦ G i (x i)` depends
measurably on `x`, and binding a product measure along it gives the product of the binds: an
independent sample from `μ i` followed by independent draws from the `G i (x i)` is an
independent sample from the mixtures. These two lemmas, and the per-coordinate form of
`pi_sum_smul`, are adapted from the helpers `pi_sum_ennreal_smul`, `measurable_pi_comp` and
`lintegral_lintegral_pi_comp` of `EValuesResearch/Results/RateVersusKL.lean` (commit `dd4072f`)
in the paper project `RemyDegenne/evalues_research` (same author), where all the coordinates
share one mixture or one kernel. For measurable maps `κ i` whose values are almost everywhere
finite, `b ↦ Measure.pi fun i ↦ κ i b` is almost everywhere measurable: for a measure `ν` that
charges only finite measures, `ν.bind fun μ ↦ Measure.pi fun _ ↦ μ` is then the mixture of the
powers of the members of `ν` (`Measure.bind` along a map that is not almost everywhere
measurable is `0`).

Under a measure on `ℕ → β` that agrees almost surely with a path `ω` on the first `k` coordinates,
a set that only depends on these coordinates is almost surely full or empty according to whether
it contains `ω`.

A function of the images of the coordinates under measurable maps to finite types is measurable.

## Main statements

* `MeasureTheory.Measure.pi_mono`: if `μ i ≤ ν i` for every `i`, with every `ν i` finite, then
  `Measure.pi μ ≤ Measure.pi ν`.
* `MeasureTheory.Measure.map_pi_comp_eq_map_pi_map`:
  `(Measure.pi μ).map (fun y ↦ f fun i ↦ X i (y i)) = (Measure.pi fun i ↦ (μ i).map (X i)).map f`.
* `MeasureTheory.Measure.pi_restrict_eq_pow_smul_pi_cond`:
  `Measure.pi (fun _ ↦ μ.restrict B) = μ B ^ card ι • Measure.pi (fun _ ↦ μ[|B])`.
* `MeasureTheory.Measure.pi_const_smul`:
  `Measure.pi (fun _ ↦ s • ν) = s ^ card ι • Measure.pi (fun _ ↦ ν)`.
* `MeasureTheory.Measure.pi_sum_smul`: the product of the finite mixtures `∑ k, w i k • μ i k` is
  `∑ σ, (∏ i, w i (σ i)) • Measure.pi fun i ↦ μ i (σ i)`.
* `MeasureTheory.Measure.lintegral_pi_sum_smul`: the integral of `F` under
  `Measure.pi (fun _ ↦ ∑ k, w k • R k)` is
  `∑ e, (∏ i, w (e i)) * ∫⁻ x, F x ∂Measure.pi (fun i ↦ R (e i))`.
* `MeasureTheory.Measure.lintegral_pi_eq_of_add_sum_eq_sum`: if `Q + ∑ i, b i • P i =
  ∑ i, c i • P i`, two functions with equal integrals under the products of copies of every convex
  combination of the `P i`, finite for the first one, have equal integrals under the product of
  copies of `Q`.
* `MeasureTheory.Measure.pi_eval_preimage_le`: for measures of mass at most `1`, the product
  measure of the cylinder `{y | y i ∈ s}` is at most `μ i s`, for every set `s`.
* `MeasureTheory.Measure.pi_le_of_forall_measure_update_preimage_le`: under a product of
  probability measures, a measurable set whose lines `{t | update x i t ∈ E}` along one coordinate
  `i` all have `μ i`-measure at most `c` has product measure at most `c`.
* `MeasureTheory.Measure.measurable_pi_comp`: `x ↦ Measure.pi fun i ↦ G i (x i)` is measurable.
* `MeasureTheory.Measure.aemeasurable_pi`: `b ↦ Measure.pi fun i ↦ κ i b` is almost everywhere
  measurable where the `κ i b` are almost everywhere finite.
* `MeasureTheory.Measure.pi_bind_pi`: binding `Measure.pi μ` along
  `x ↦ Measure.pi fun i ↦ G i (x i)` gives `Measure.pi fun i ↦ (μ i).bind (G i)`.
* `MeasureTheory.measurable_pi_comp_of_finite`: `fun e ↦ g fun i ↦ φ i (e i)` is measurable for
  measurable maps `φ i` to finite types.
* `MeasureTheory.setLIntegral_eq_ite_of_ae_prefix`, `MeasureTheory.measure_eq_ite_of_ae_prefix`:
  under a measure that agrees almost surely with `ω` on the first `k` coordinates, the integral
  over, and the measure of, a set that only depends on these coordinates.

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

/-- **Monotonicity of the product measure.** The product of finite measures is monotone in its
factors: if `μ i ≤ ν i` for every `i`, then `Measure.pi μ ≤ Measure.pi ν`. -/
@[gcongr]
lemma pi_mono {μ ν : ∀ i, Measure (Ω i)} [∀ i, IsFiniteMeasure (ν i)] (h : ∀ i, μ i ≤ ν i) :
    Measure.pi μ ≤ Measure.pi ν := by
  have (i : ι) : IsFiniteMeasure (μ i) := isFiniteMeasure_of_le (ν i) (h i)
  rw [pi_eq_withDensity_prod_rnDeriv fun i ↦ absolutelyContinuous_of_le (h i)]
  calc (Measure.pi ν).withDensity (fun x ↦ ∏ i, (μ i).rnDeriv (ν i) (x i))
  _ ≤ (Measure.pi ν).withDensity 1 := by
    refine withDensity_mono ?_
    filter_upwards [ae_le_pi fun i ↦ rnDeriv_le_one_of_le (h i)] with x hx
    exact Finset.prod_le_one fun i _ ↦ hx i
  _ = Measure.pi ν := withDensity_one

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

/-- The integral under the product of copies of a finite mixture `∑ k, w k • R k` of finite
measures is a polynomial in the weights: the sum over the assignments `e : ι → κ` of
`∏ i, w (e i)` times the integral under `Measure.pi (fun i ↦ R (e i))`. -/
lemma lintegral_pi_sum_smul [DecidableEq ι] {α κ : Type*} {mα : MeasurableSpace α} [Fintype κ]
    {R : κ → Measure α} [∀ k, IsFiniteMeasure (R k)] (w : κ → ℝ≥0) (F : (ι → α) → ℝ≥0∞) :
    ∫⁻ x, F x ∂Measure.pi (fun _ : ι ↦ ∑ k, w k • R k) =
      ∑ e : ι → κ, (∏ i, (w (e i) : ℝ≥0∞)) * ∫⁻ x, F x ∂Measure.pi (fun i ↦ R (e i)) := by
  have (k : κ) : IsFiniteMeasure ((w k : ℝ≥0∞) • R k) := by
    rw [← ENNReal.smul_def]
    infer_instance
  simp_rw [ENNReal.smul_def]
  rw [pi_sum_smul (fun _ k ↦ (w k : ℝ≥0∞)) (fun _ ↦ R)]
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

/-! ### Binds of products -/

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

/-- The product of the measures `κ i b` depends almost everywhere measurably on `b` when each `κ i`
is measurable and almost every `κ i b` is finite. For instance, `μ ↦ Measure.pi fun _ ↦ μ` is
almost everywhere measurable for a measure on the measures that charges only finite ones. -/
lemma aemeasurable_pi {κ : ∀ i, β → Measure (𝓨 i)} (hκ : ∀ i, Measurable (κ i)) {ν : Measure β}
    (hfin : ∀ i, ∀ᵐ b ∂ν, IsFiniteMeasure (κ i b)) :
    AEMeasurable (fun b ↦ Measure.pi fun i ↦ κ i b) ν := by
  classical
  -- replace the infinite values by `0`
  set G : ∀ i, β → Measure (𝓨 i) := fun i b ↦ if κ i b .univ < ∞ then κ i b else 0
  have hG (i : ι) : Measurable (G i) :=
    Measurable.ite (measurableSet_lt ((measurable_coe .univ).comp (hκ i)) measurable_const) (hκ i)
      measurable_const
  have (i : ι) (b : β) : IsFiniteMeasure (G i b) := by
    by_cases h : κ i b .univ < ∞
    · simpa only [G, h, ite_true] using (⟨h⟩ : IsFiniteMeasure (κ i b))
    · simp only [G, h, ite_false]
      infer_instance
  refine ⟨fun b ↦ Measure.pi fun i ↦ G i b,
    (measurable_pi_comp (Ω := fun _ ↦ β) hG).comp (.of_eval fun _ ↦ measurable_id),
    ?_⟩
  filter_upwards [ae_all_iff.2 hfin] with b hb
  simp only [G, measure_lt_top, ite_true]

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

namespace MeasureTheory

/-- A function `g fun i ↦ φ i (e i)` of the images of the coordinates under measurable maps `φ i`
to finite types is measurable. -/
lemma measurable_pi_comp_of_finite {ι : Type*} [Countable ι] {Ω κ : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] [Finite (∀ i, κ i)] [∀ i, MeasurableSpace (κ i)]
    [∀ i, MeasurableSingletonClass (κ i)] {β : Type*} [MeasurableSpace β] {φ : ∀ i, Ω i → κ i}
    (hφ : ∀ i, Measurable (φ i)) (g : (∀ i, κ i) → β) :
    Measurable fun e : ∀ i, Ω i ↦ g fun i ↦ φ i (e i) :=
  (measurable_of_finite g).comp (.of_eval fun i ↦ (hφ i).comp (measurable_pi_apply i))

variable {β : Type*} [MeasurableSpace β] {μ : Measure (ℕ → β)} {k : ℕ} {ω : ℕ → β}
  {s : Set (ℕ → β)}

open scoped Classical in
/-- Under a measure that agrees almost surely with `ω` on the first `k` coordinates, the integral
over a set that only depends on these coordinates is the whole integral if the set contains `ω`,
and `0` otherwise. -/
theorem setLIntegral_eq_ite_of_ae_prefix (hpre : ∀ᵐ ω' ∂μ, ∀ i < k, ω' i = ω i)
    (hs : MeasurableSet[MeasurableSpace.comap (fun (ω : ℕ → β) (i : Fin k) ↦ ω i)
      MeasurableSpace.pi] s) (G : (ℕ → β) → ℝ≥0∞) :
    ∫⁻ ω' in s, G ω' ∂μ = if ω ∈ s then ∫⁻ ω', G ω' ∂μ else 0 := by
  obtain ⟨B, -, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
  have hae : ∀ᵐ ω' ∂μ, (ω' ∈ (fun (ω : ℕ → β) (i : Fin k) ↦ ω i) ⁻¹' B ↔
      ω ∈ (fun (ω : ℕ → β) (i : Fin k) ↦ ω i) ⁻¹' B) := by
    filter_upwards [hpre] with ω' h
    have : (fun i : Fin k ↦ ω' i) = fun i : Fin k ↦ ω i := funext fun i ↦ h i i.2
    simp only [Set.mem_preimage, this]
  split_ifs with hω
  · rw [Measure.restrict_eq_self_of_ae_mem (hae.mono fun ω' h ↦ h.2 hω)]
  · rw [Measure.restrict_eq_zero.2 (measure_eq_zero_iff_ae_notMem.2
      (hae.mono fun ω' h h' ↦ hω (h.1 h'))), lintegral_zero_measure]

open scoped Classical in
/-- Under a measure that agrees almost surely with `ω` on the first `k` coordinates, a set that
only depends on these coordinates has full measure if it contains `ω`, and measure `0`
otherwise. -/
theorem measure_eq_ite_of_ae_prefix (hpre : ∀ᵐ ω' ∂μ, ∀ i < k, ω' i = ω i)
    (hs : MeasurableSet[MeasurableSpace.comap (fun (ω : ℕ → β) (i : Fin k) ↦ ω i)
      MeasurableSpace.pi] s) :
    μ s = if ω ∈ s then μ Set.univ else 0 := by
  have h := setLIntegral_eq_ite_of_ae_prefix hpre hs fun _ ↦ 1
  rwa [setLIntegral_one, lintegral_one] at h

end MeasureTheory
