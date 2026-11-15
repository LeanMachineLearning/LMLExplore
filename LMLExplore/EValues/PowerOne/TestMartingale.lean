/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.TestSupermartingale
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Probability.ProductMeasure
import LMLExplore.Analysis.Convex.ENNReal
import LMLExplore.MeasureTheory.Constructions.Pi
import LMLExplore.MeasureTheory.Measure.ProbabilityMeasure.Convex
import LMLExplore.Probability.Martingale.OptionalStopping
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Test martingales for convex i.i.d. nulls have no power against the span of the null

The observations are the coordinates of `ℕ → 𝓧`. For a set `S₁` of probability measures on `𝓧`,
the i.i.d. null is the set of the laws `Measure.infinitePi fun _ ↦ P` with `P ∈ S₁`. Zhang, Ramdas
and Wang conjecture that if a test martingale for the i.i.d. null has power one against the i.i.d.
law of `Q₁`, then `Q₁` lies outside the linear span of `S₁`, perhaps under additional conditions
[ZRW24, §7].

For a convex `S₁` this holds [EVR26, Note 03, Theorem 1], for every filtration each of whose
σ-algebras depends on finitely many observations. Let `Q₁` be a probability measure in the linear
span of `S₁`, written as `Q₁ + ∑ i, b i • P i = ∑ i, c i • P i` with finitely many `P i ∈ S₁` and
`b i, c i ≥ 0`. Then every test martingale for the i.i.d. null whose initial value has expectation
`1` under the null is a test martingale under the i.i.d. law of `Q₁`. In particular its `limsup`
is almost surely finite under that law: it does not have power one against `Q₁`.

Convexity is needed. For the null of the two point masses on `Bool`, the fair coin is the midpoint
of the null, yet the process equal to `1` while all observations agree, and to `2 ^ n` at time `n`
once two different ones have been seen, is a test martingale for the i.i.d. null that tends to `∞`
almost surely under i.i.d. fair coin flips [EVR26, Note 03, Counterexample 1].

## Main statements

* `ProbabilityTheory.isTestMartingale_infinitePi_of_add_sum_eq_sum`: for a convex null, a test
  martingale for the i.i.d. null with initial expectation `1` is a test martingale under the i.i.d.
  law of every probability measure in the linear span of the null.
* `ProbabilityTheory.ae_limsup_lt_top_infinitePi_of_add_sum_eq_sum`: such a test martingale has an
  almost surely finite `limsup` under that law, so it does not have power one against it.
* `ProbabilityTheory.exists_isTestMartingale_dirac_tendsto_top`: for the null of the two point
  masses on `Bool`, some test martingale for the i.i.d. null with initial value `1` tends to `∞`
  almost surely under i.i.d. fair coin flips.

## Implementation notes

An `ℱ n`-measurable set and the values `M n` and `M (n + 1)` are functions of the first `N + 1`
observations for some `N`, so their integrals under `Measure.infinitePi` are integrals under
`Measure.pi` over `Finset.Iic N`. The finite-dimensional step is a polarization argument. Write
`B = ∑ i, b i • P i`. The integral of a function of finitely many observations under the product
of copies of `Q₁ + t • B` is a polynomial in `t`. For `t ≥ 1`, the measure `Q₁ + t • B` is a
positive multiple of a convex combination of the `P i`, which lies in the null, so the identities
of the martingale hold for these `t`. By the identity theorem for analytic functions they hold at
`t = 0`, that is under `Q₁`.

The statements and proofs are adapted from `EValuesResearch/Results/TestMartingaleConverse.lean`
(commit `6f05c5f`) in the paper project `RemyDegenne/evalues_research`, which formalizes
[EVR26, Note 03] (`results/03-test-martingale-converse.md` there).

## References

* [ZRW24] Z. Zhang, A. Ramdas and R. Wang, *On the existence of powerful p-values and e-values for
  composite hypotheses*, Ann. Statist. 52 (2024), arXiv:2305.16539: §7.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 03, *Converse of the power-one theorem for test martingales*,
  Theorem 1 and Counterexample 1.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-! ### Polarization -/

/-- **Identity theorem for the polynomials of the polarization.** Two families `a` and `a'` of
finite coefficients indexed by `J → Bool` whose polynomials
`t ↦ ∑ e, (∏ j, bif e j then t else 1) * a e` agree for every `t > 1` agree for every `t ≥ 0`. -/
private lemma sum_prod_bif_mul_eq_of_one_lt {J : Type*} [Fintype J] [DecidableEq J]
    {a a' : (J → Bool) → ℝ≥0∞} (ha : ∀ e, a e ≠ ∞) (ha' : ∀ e, a' e ≠ ∞)
    (h : ∀ t : ℝ≥0, 1 < t → ∑ e, (∏ j, ((bif e j then t else 1 : ℝ≥0) : ℝ≥0∞)) * a e =
      ∑ e, (∏ j, ((bif e j then t else 1 : ℝ≥0) : ℝ≥0∞)) * a' e) (t : ℝ≥0) :
    ∑ e, (∏ j, ((bif e j then t else 1 : ℝ≥0) : ℝ≥0∞)) * a e =
      ∑ e, (∏ j, ((bif e j then t else 1 : ℝ≥0) : ℝ≥0∞)) * a' e := by
  have hfin (c : (J → Bool) → ℝ≥0∞) (hc : ∀ e, c e ≠ ∞) (t : ℝ≥0) (e : J → Bool) :
      (∏ j, ((bif e j then t else 1 : ℝ≥0) : ℝ≥0∞)) * c e ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.prod_ne_top fun _ _ ↦ ENNReal.coe_ne_top) (hc e)
  -- the real polynomials
  set φ : ((J → Bool) → ℝ≥0∞) → ℝ → ℝ :=
    fun c x ↦ ∑ e : J → Bool, (∏ j, bif e j then x else 1) * (c e).toReal
  have hφ_eq (c : (J → Bool) → ℝ≥0∞) (hc : ∀ e, c e ≠ ∞) (t : ℝ≥0) :
      φ c t = (∑ e, (∏ j, ((bif e j then t else 1 : ℝ≥0) : ℝ≥0∞)) * c e).toReal := by
    rw [ENNReal.toReal_sum fun e _ ↦ hfin c hc t e]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_prod]
    congr 1
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    cases e j <;> simp
  have han (c : (J → Bool) → ℝ≥0∞) : AnalyticOnNhd ℝ (φ c) Set.univ := fun x _ ↦
    Finset.analyticAt_fun_sum _ fun e _ ↦ (Finset.analyticAt_fun_prod _ fun j _ ↦ by
      cases e j
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

/-- **Polarization.** Let `Q` be a probability measure and `P i` finite measures with
`Q + ∑ i, b i • P i = ∑ i, c i • P i`. If two functions of the observations indexed by a finite
type `J` have equal integrals under the product of copies of every convex combination of the
`P i`, finite for the first function, then they have equal integrals under the product of copies
of `Q`. -/
private lemma lintegral_pi_eq_of_add_sum_eq_sum {J ι : Type*} [Fintype J] [Fintype ι]
    {P : ι → Measure 𝓧} [∀ i, IsFiniteMeasure (P i)] {b c : ι → ℝ≥0} {Q : Measure 𝓧}
    [IsProbabilityMeasure Q] (hQ : Q + ∑ i, b i • P i = ∑ i, c i • P i)
    {F G : (J → 𝓧) → ℝ≥0∞}
    (hFG : ∀ w : ι → ℝ≥0, ∑ i, w i = 1 →
      ∫⁻ x, F x ∂Measure.pi (fun _ ↦ ∑ i, w i • P i) =
        ∫⁻ x, G x ∂Measure.pi (fun _ ↦ ∑ i, w i • P i))
    (hF : ∀ w : ι → ℝ≥0, ∑ i, w i = 1 →
      ∫⁻ x, F x ∂Measure.pi (fun _ ↦ ∑ i, w i • P i) ≠ ∞) :
    ∫⁻ x, F x ∂Measure.pi (fun _ : J ↦ Q) = ∫⁻ x, G x ∂Measure.pi (fun _ : J ↦ Q) := by
  classical
  set B := ∑ i, b i • P i with hB
  -- `Q + t • B` as the mixture of `R true = B` and `R false = Q` with weights `t` and `1`
  set R : Bool → Measure 𝓧 := fun k ↦ bif k then B else Q with hR
  have : IsFiniteMeasure B := by rw [hB]; infer_instance
  have : ∀ k, IsFiniteMeasure (R k) := fun k ↦ by
    cases k <;> simp only [hR, Bool.cond_false, Bool.cond_true] <;> infer_instance
  set α : ((J → 𝓧) → ℝ≥0∞) → (J → Bool) → ℝ≥0∞ :=
    fun H e ↦ ∫⁻ x, H x ∂Measure.pi (fun j ↦ R (e j))
  have hpoly (H : (J → 𝓧) → ℝ≥0∞) (t : ℝ≥0) :
      ∫⁻ x, H x ∂Measure.pi (fun _ : J ↦ Q + t • B) =
        ∑ e : J → Bool, (∏ j, ((bif e j then t else 1 : ℝ≥0) : ℝ≥0∞)) * α H e := by
    have hmix : Q + t • B = ∑ k, (bif k then t else 1 : ℝ≥0) • R k := by simp [hR, add_comm]
    rw [hmix, Measure.lintegral_pi_sum_smul]
  -- for `t ≥ 1`, `Q + t • B` is a positive multiple of a convex combination of the `P i`
  have hgood (t : ℝ≥0) (ht : 1 ≤ t) :
      ∫⁻ x, F x ∂Measure.pi (fun _ : J ↦ Q + t • B) =
        ∫⁻ x, G x ∂Measure.pi (fun _ : J ↦ Q + t • B) ∧
      ∫⁻ x, F x ∂Measure.pi (fun _ : J ↦ Q + t • B) ≠ ∞ := by
    have hμ : Q + t • B = ∑ i, (c i + (t - 1) * b i) • P i := by
      calc Q + t • B = (Q + B) + (t - 1) • B := by
            conv_lhs => rw [← add_tsub_cancel_of_le ht, add_smul, one_smul]
            rw [add_assoc]
        _ = ∑ i, (c i + (t - 1) * b i) • P i := by
            rw [hQ, hB, Finset.smul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_smul, ← add_smul]
    have hs : ∑ i, (c i + (t - 1) * b i) ≠ 0 := by
      intro h0
      have h : Q + t • B = 0 := by
        rw [hμ]
        exact Finset.sum_eq_zero fun i hi ↦ by rw [Finset.sum_eq_zero_iff.1 h0 i hi, zero_smul]
      have h' := congrArg (· Set.univ) h
      simp at h'
    have hv : ∑ i, (c i + (t - 1) * b i) / ∑ j, (c j + (t - 1) * b j) = 1 := by
      rw [← Finset.sum_div, div_self hs]
    rw [hμ, Finset.sum_smul_eq_smul_sum_div_smul hs, Measure.pi_const_smul,
      lintegral_smul_measure, lintegral_smul_measure, hFG _ hv]
    refine ⟨rfl, ?_⟩
    rw [ENNReal.smul_def, smul_eq_mul, ← hFG _ hv]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (hF _ hv)
  -- the coefficients of the polynomials are finite, as the case `t = 1` shows
  have hα_ne (H : (J → 𝓧) → ℝ≥0∞)
      (hH : ∫⁻ x, H x ∂Measure.pi (fun _ : J ↦ Q + (1 : ℝ≥0) • B) ≠ ∞) (e : J → Bool) :
      α H e ≠ ∞ := by
    have hw1 (k : Bool) : (bif k then (1 : ℝ≥0) else 1) = 1 := by cases k <;> rfl
    rw [hpoly] at hH
    simp only [hw1, ENNReal.coe_one, Finset.prod_const_one, one_mul] at hH
    exact ENNReal.sum_ne_top.1 hH e (Finset.mem_univ e)
  obtain ⟨h1eq, h1ne⟩ := hgood 1 le_rfl
  have h0 := sum_prod_bif_mul_eq_of_one_lt (hα_ne F h1ne) (hα_ne G (by rwa [← h1eq]))
    (fun t ht ↦ by rw [← hpoly, ← hpoly]; exact (hgood t ht.le).1) 0
  rw [← hpoly, ← hpoly] at h0
  simpa only [zero_smul, add_zero] using h0

/-- **Polarization for i.i.d. laws.** Let `Q` be a probability measure and `P i` probability
measures with `Q + ∑ i, b i • P i = ∑ i, c i • P i`. If two functions of the first `N + 1`
observations have equal integrals under the i.i.d. law of every convex combination of the `P i`,
finite for the first function, then they have equal integrals under the i.i.d. law of `Q`. -/
private lemma lintegral_infinitePi_eq_of_add_sum_eq_sum {ι : Type*} [Fintype ι]
    {P : ι → Measure 𝓧} [∀ i, IsProbabilityMeasure (P i)] {b c : ι → ℝ≥0} {Q : Measure 𝓧}
    [IsProbabilityMeasure Q] (hQ : Q + ∑ i, b i • P i = ∑ i, c i • P i) {N : ℕ}
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

/-! ### Test martingales for convex i.i.d. nulls -/

/-- **Test martingales for a convex i.i.d. null have no power against its linear span.** Let `S₁`
be a convex set of measures and `Q₁` a probability measure in its linear span, written as
`Q₁ + ∑ i, b i • P i = ∑ i, c i • P i` with finitely many probability measures `P i ∈ S₁`. Let `ℱ`
be a filtration each of whose σ-algebras depends on finitely many observations. Then a test
martingale for the i.i.d. laws of the members of `S₁` whose initial value has expectation `1`
under each of them is a test martingale for the i.i.d. law of `Q₁` [EVR26, Note 03, Theorem 1].
This proves, for convex nulls, the conjecture of [ZRW24, §7] that a test martingale with power one
against `Q₁` forces `Q₁` out of the linear span of the null. -/
theorem isTestMartingale_infinitePi_of_add_sum_eq_sum {S₁ : Set (Measure 𝓧)}
    (hS₁ : Convex ℝ≥0∞ S₁) {ι : Type*} [Fintype ι] {P : ι → Measure 𝓧}
    [∀ i, IsProbabilityMeasure (P i)] (hP : ∀ i, P i ∈ S₁) {b c : ι → ℝ≥0} {Q₁ : Measure 𝓧}
    [IsProbabilityMeasure Q₁] (hQ₁ : Q₁ + ∑ i, b i • P i = ∑ i, c i • P i)
    {ℱ : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → 𝓧))}
    (hℱ : ∀ n, ∃ N, ℱ n ≤ Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) N) {M : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hM : IsTestMartingale M ℱ ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁))
    (hM0 : ∀ P ∈ S₁, ∫⁻ ω, M 0 ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) = 1) :
    IsTestMartingale M ℱ {Measure.infinitePi fun _ : ℕ ↦ Q₁} := by
  have hmem (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) : ∑ i, w i • P i ∈ S₁ :=
    hS₁.sum_nnreal_smul_mem hw fun i _ ↦ hP i
  have hnull (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) : Measure.infinitePi (fun _ : ℕ ↦ ∑ i, w i • P i) ∈
      (fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁ :=
    ⟨_, hmem w hw, rfl⟩
  refine ⟨hM.adapted, ?_, ?_⟩
  · rintro _ rfl
    obtain ⟨N, hN⟩ := hℱ 0
    refine (lintegral_infinitePi_eq_of_add_sum_eq_sum hQ₁ ((hM.adapted 0).mono hN le_rfl)
      (measurable_const (a := (1 : ℝ≥0∞))) (fun w hw ↦ ?_) fun w hw ↦ ?_).trans_le (by simp)
    · have := isProbabilityMeasure_sum_smul (P := P) hw
      rw [hM0 _ (hmem w hw)]
      simp
    · rw [hM0 _ (hmem w hw)]
      exact ENNReal.one_ne_top
  · rintro _ rfl n s hs
    obtain ⟨N₁, hN₁⟩ := hℱ n
    obtain ⟨N₂, hN₂⟩ := hℱ (n + 1)
    have h₁ : ℱ n ≤ Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) (max N₁ N₂) :=
      hN₁.trans (Filtration.mono _ (le_max_left _ _))
    have h₂ : ℱ (n + 1) ≤ Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) (max N₁ N₂) :=
      hN₂.trans (Filtration.mono _ (le_max_right _ _))
    have hs' : MeasurableSet s := ℱ.le n s hs
    rw [← lintegral_indicator hs', ← lintegral_indicator hs']
    refine lintegral_infinitePi_eq_of_add_sum_eq_sum hQ₁
      (((hM.adapted (n + 1)).mono h₂ le_rfl).indicator (h₁ s hs))
      (((hM.adapted n).mono h₁ le_rfl).indicator (h₁ s hs)) (fun w hw ↦ ?_) fun w hw ↦ ?_
    · rw [lintegral_indicator hs', lintegral_indicator hs']
      exact hM.setLIntegral_succ_eq _ (hnull w hw) n s hs
    · have := isProbabilityMeasure_sum_smul (P := P) hw
      rw [lintegral_indicator hs']
      exact ((setLIntegral_le_lintegral _ _).trans_lt
        ((hM.isTestSupermartingale.lintegral_le_one (hnull w hw) (n + 1)).trans_lt
          ENNReal.one_lt_top)).ne

/-- **No power one against the linear span of a convex i.i.d. null.** Under the hypotheses of
`isTestMartingale_infinitePi_of_add_sum_eq_sum`, the test martingale has an almost surely finite
`limsup` under the i.i.d. law of `Q₁`: it does not have power one against `Q₁`
[EVR26, Note 03, Theorem 1]. -/
theorem ae_limsup_lt_top_infinitePi_of_add_sum_eq_sum {S₁ : Set (Measure 𝓧)}
    (hS₁ : Convex ℝ≥0∞ S₁) {ι : Type*} [Fintype ι] {P : ι → Measure 𝓧}
    [∀ i, IsProbabilityMeasure (P i)] (hP : ∀ i, P i ∈ S₁) {b c : ι → ℝ≥0} {Q₁ : Measure 𝓧}
    [IsProbabilityMeasure Q₁] (hQ₁ : Q₁ + ∑ i, b i • P i = ∑ i, c i • P i)
    {ℱ : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → 𝓧))}
    (hℱ : ∀ n, ∃ N, ℱ n ≤ Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) N) {M : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hM : IsTestMartingale M ℱ ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁))
    (hM0 : ∀ P ∈ S₁, ∫⁻ ω, M 0 ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) = 1) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), limsup (fun n ↦ M n ω) atTop < ∞ :=
  (isTestMartingale_infinitePi_of_add_sum_eq_sum hS₁ hP hQ₁ hℱ hM
    hM0).isTestSupermartingale.ae_limsup_lt_top (Set.mem_singleton _)

/-! ### Convexity is needed -/

/-- The process of the counterexample: `1` while the observations up to time `n` all equal the
first one, and `2 ^ n` once two different values have been seen. -/
private noncomputable def doublingProcess (n : ℕ) (ω : ℕ → Bool) : ℝ≥0∞ :=
  if ∀ i ≤ n, ω i = ω 0 then 1 else 2 ^ n

/-- The doubling process equals `1` on constant sequences. -/
private lemma doublingProcess_const (n : ℕ) (x : Bool) : doublingProcess n (fun _ ↦ x) = 1 := by
  simp [doublingProcess]

/-- The doubling process is a test martingale for the i.i.d. laws of the two point masses on
`Bool`: under each of them the observations are almost surely constant and the process stays at
`1`. -/
private lemma isTestMartingale_doublingProcess :
    IsTestMartingale doublingProcess (Filtration.piLE (X := fun _ : ℕ ↦ Bool))
      ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) ''
        {Measure.dirac false, Measure.dirac true}) := by
  have hmem : ∀ μ ∈ ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) ''
      {Measure.dirac false, Measure.dirac true}), ∃ x : Bool, μ = Measure.dirac (fun _ ↦ x) := by
    rintro μ ⟨P, hP, rfl⟩
    rcases hP with rfl | rfl
    · exact ⟨false, Measure.infinitePi_dirac (fun _ ↦ false)⟩
    · exact ⟨true, Measure.infinitePi_dirac (fun _ ↦ true)⟩
  have hadapted : Adapted (Filtration.piLE (X := fun _ : ℕ ↦ Bool)) doublingProcess := by
    intro n
    rw [Filtration.piLE_eq_comap_frestrictLe]
    have h : doublingProcess n = (fun y : (Finset.Iic n → Bool) ↦
        if ∀ i : Finset.Iic n, y i = y ⟨0, Finset.mem_Iic.2 n.zero_le⟩ then (1 : ℝ≥0∞)
        else 2 ^ n) ∘ Preorder.frestrictLe n := by
      ext ω
      simp only [doublingProcess, Function.comp_apply, Preorder.frestrictLe, Finset.restrict,
        Subtype.forall, Finset.mem_Iic]
      exact if_congr Iff.rfl rfl rfl
    rw [h]
    exact (measurable_of_finite _).comp (comap_measurable _)
  refine ⟨hadapted, fun μ hμ ↦ ?_, fun μ hμ n s hs ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := hmem μ hμ
    rw [lintegral_dirac, doublingProcess_const]
  · obtain ⟨x, rfl⟩ := hmem μ hμ
    classical
    rw [restrict_dirac' (Filtration.le _ n s hs)]
    split_ifs
    · rw [lintegral_dirac, lintegral_dirac, doublingProcess_const, doublingProcess_const]
    · simp

/-- Under i.i.d. fair coin flips, two different values appear almost surely. -/
private lemma ae_exists_ne_infinitePi_coin : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦
    (2⁻¹ : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true)), ∃ i, ω i ≠ ω 0 := by
  have : IsProbabilityMeasure ((2⁻¹ : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true)) :=
    ⟨by simp [ENNReal.inv_two_add_inv_two]⟩
  -- a constant sequence has probability at most `2⁻¹ ^ n` for every `n`, hence `0`
  have hconst (x : Bool) : Measure.infinitePi (fun _ : ℕ ↦
      (2⁻¹ : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true)) {fun _ ↦ x} = 0 := by
    have hx : ((2⁻¹ : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true)) {x} = 2⁻¹ := by
      cases x <;> simp
    have hle (n : ℕ) : Measure.infinitePi (fun _ : ℕ ↦
        (2⁻¹ : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true)) {fun _ ↦ x} ≤ 2⁻¹ ^ n := by
      calc _ ≤ Measure.infinitePi (fun _ : ℕ ↦
            (2⁻¹ : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true))
            (Set.pi (Finset.range n : Set ℕ) fun _ ↦ {x}) := measure_mono fun ω hω ↦ by simp_all
        _ = 2⁻¹ ^ n := by
          rw [Measure.infinitePi_pi _ fun _ _ ↦ measurableSet_singleton x, hx, Finset.prod_const,
            Finset.card_range]
    exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num)) hle) bot_le
  refine measure_mono_null (fun ω hω ↦ ?_) (measure_union_null (hconst false) (hconst true))
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_not] at hω
  have hω' : ω = fun _ ↦ ω 0 := funext hω
  cases h : ω 0
  · exact Or.inl (hω'.trans (by rw [h]))
  · exact Or.inr (hω'.trans (by rw [h]))

/-- Once two different values have been seen, the doubling process tends to `∞`. -/
private lemma tendsto_doublingProcess {ω : ℕ → Bool} (hω : ∃ i, ω i ≠ ω 0) :
    Tendsto (fun n ↦ doublingProcess n ω) atTop (𝓝 ∞) := by
  obtain ⟨i, hi⟩ := hω
  refine (ENNReal.tendsto_pow_atTop_nhds_top_iff.2 (by norm_num : (1 : ℝ≥0∞) < 2)).congr' ?_
  filter_upwards [eventually_ge_atTop i] with n hn
  rw [doublingProcess, ite_eq_right fun h ↦ hi (h i hn)]

/-- **Convexity is needed.** For the null of the two point masses on `Bool`, whose midpoint is the
fair coin, some test martingale for the i.i.d. null with initial value `1`, for the filtration of
the observations, tends to `∞` almost surely under i.i.d. fair coin flips
[EVR26, Note 03, Counterexample 1]. -/
theorem exists_isTestMartingale_dirac_tendsto_top :
    ∃ M : ℕ → (ℕ → Bool) → ℝ≥0∞, M 0 = 1 ∧
      IsTestMartingale M (Filtration.piLE (X := fun _ : ℕ ↦ Bool))
        ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) ''
          {Measure.dirac false, Measure.dirac true}) ∧
      ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦
          (2⁻¹ : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true)),
        Tendsto (fun n ↦ M n ω) atTop (𝓝 ∞) :=
  ⟨doublingProcess, funext fun ω ↦ by simp [doublingProcess], isTestMartingale_doublingProcess,
    ae_exists_ne_infinitePi_coin.mono fun _ ↦ tendsto_doublingProcess⟩

end ProbabilityTheory
