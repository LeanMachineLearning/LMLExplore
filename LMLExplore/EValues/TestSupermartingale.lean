/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.CondEVariable
public import LMLExplore.Probability.Martingale.Basic
public import LMLExplore.Probability.Process.Adapted

/-!
# Test supermartingales and wealth processes

A test supermartingale for a set of measures `S` is an `ℝ≥0∞`-valued process that is a
supermartingale under every `P ∈ S` and starts with expectation at most `1` [RW, Definition 7.3;
ShSVV11]. Values are in `ℝ≥0∞`, the supermartingale property is stated with set integrals and no
integrability condition is imposed beyond that of the initial value, so that products of
e-variables taking infinite values and nonintegrable bets are covered. Test supermartingales are
the processes against which e-processes are defined and through which Ville's inequality bounds
the probability that a sequential test ever rejects.

The main construction is the wealth of a gambler who reinvests at every round: an initial wealth
`M₀` with expectation at most `1` (an e-variable, for a null of probability measures) times the
product of the factors `F k`, each a conditional e-variable given the past `ℱ k`
(`ProbabilityTheory.IsCondEVar`). Conversely, every test supermartingale is almost surely such a
wealth process. It contains the products of sequential e-variables
[RW, Proposition 7.20; GdHK24, Proposition 2], the wealth of portfolios `∑ i, w k i * E k i` of
conditional e-variables with predictable weights [WSJ26], and betting
`∏ k, (1 - c k + c k * E k)` with predictable bets `c k ≤ 1` [RW, Definition 7.21; WSR24].

## Main definitions

* `ProbabilityTheory.IsENNSupermartingale M ℱ S`: `M : ℕ → Ω → ℝ≥0∞` is adapted and
  `∫⁻ ω in s, M (n + 1) ω ∂P ≤ ∫⁻ ω in s, M n ω ∂P` for every `P ∈ S`, `n` and
  `ℱ n`-measurable `s`.
* `ProbabilityTheory.IsTestSupermartingale M ℱ S`: moreover `∫⁻ M 0 ∂P ≤ 1` for every `P ∈ S`.
* `ProbabilityTheory.IsTestMartingale M ℱ S`: the same, with equalities of the set integrals.

## Main statements

* `MeasureTheory.Supermartingale.isTestSupermartingale_ofReal`,
  `ProbabilityTheory.IsTestSupermartingale.supermartingale_toReal`: the bridges with Mathlib's
  real supermartingales.
* `ProbabilityTheory.IsTestSupermartingale.ae_lt_top`: a test supermartingale is almost surely
  finite.
* `ProbabilityTheory.isTestSupermartingale_mul_prod`, `ProbabilityTheory.isTestMartingale_mul_prod`:
  wealth processes `M₀ * ∏ k < n, F k` of conditional e-variables.
* `ProbabilityTheory.isTestSupermartingale_portfolio`,
  `ProbabilityTheory.isTestSupermartingale_prod`,
  `ProbabilityTheory.isTestSupermartingale_betting_condEVar` and their martingale versions:
  portfolios, products of sequential e-variables and betting.
* `ProbabilityTheory.IsENNSupermartingale.isCondEVar_div`,
  `ProbabilityTheory.IsTestSupermartingale.ae_eq_mul_prod_div`: conversely, every test
  supermartingale is almost surely the wealth `M 0 * ∏ k < n, M (k + 1) / M k` of its successive
  ratios, which are conditional e-variables [WSR24, Proposition 3].

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614.
* [ShSVV11] G. Shafer, A. Shen, N. Vereshchagin and V. Vovk, *Test martingales, Bayes factors and
  p-values*, Statist. Sci. 26 (2011), arXiv:0912.4269.
* [GdHK24] P. Grünwald, R. de Heide and W. M. Koolen, *Safe testing*, J. R. Stat. Soc. Ser. B 86
  (2024), arXiv:1906.07801.
* [WSR24] I. Waudby-Smith and A. Ramdas, *Estimating means of bounded random variables by
  betting*, J. R. Stat. Soc. Ser. B 86 (2024), arXiv:2010.09686.
* [WSJ26] I. Waudby-Smith, R. Sandoval and M. I. Jordan, *Instance-log-optimality of
  portfolio-based e-processes and their sequential hypothesis tests*, arXiv:2504.02818.
-/

public section

open MeasureTheory Set Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {S T : Set (Measure Ω)}
  {P : Measure Ω} {M M' : ℕ → Ω → ℝ≥0∞}

/-- `M : ℕ → Ω → ℝ≥0∞` is a supermartingale for the filtration `ℱ` under every member of `S`:
it is adapted and `∫⁻ ω in s, M (n + 1) ω ∂P ≤ ∫⁻ ω in s, M n ω ∂P` for every `P ∈ S`, every `n`
and every `ℱ n`-measurable `s`. No integrability is assumed. -/
structure IsENNSupermartingale (M : ℕ → Ω → ℝ≥0∞) (ℱ : Filtration ℕ mΩ)
    (S : Set (Measure Ω)) : Prop where
  adapted : Adapted ℱ M
  setLIntegral_succ_le : ∀ P ∈ S, ∀ n s, MeasurableSet[ℱ n] s →
    ∫⁻ ω in s, M (n + 1) ω ∂P ≤ ∫⁻ ω in s, M n ω ∂P

/-- `M : ℕ → Ω → ℝ≥0∞` is a test supermartingale for the filtration `ℱ` and the null `S`: a
supermartingale under every member of `S` with `∫⁻ M 0 ∂P ≤ 1` for every `P ∈ S`
[RW, Definition 7.3]. -/
structure IsTestSupermartingale (M : ℕ → Ω → ℝ≥0∞) (ℱ : Filtration ℕ mΩ)
    (S : Set (Measure Ω)) : Prop extends IsENNSupermartingale M ℱ S where
  lintegral_zero_le : ∀ P ∈ S, ∫⁻ ω, M 0 ω ∂P ≤ 1

/-- `M : ℕ → Ω → ℝ≥0∞` is a test martingale for the filtration `ℱ` and the null `S`: it is
adapted, `∫⁻ M 0 ∂P ≤ 1` and `∫⁻ ω in s, M (n + 1) ω ∂P = ∫⁻ ω in s, M n ω ∂P` for every
`P ∈ S`, every `n` and every `ℱ n`-measurable `s` [RW, Definition 7.3]. -/
structure IsTestMartingale (M : ℕ → Ω → ℝ≥0∞) (ℱ : Filtration ℕ mΩ)
    (S : Set (Measure Ω)) : Prop where
  adapted : Adapted ℱ M
  lintegral_zero_le : ∀ P ∈ S, ∫⁻ ω, M 0 ω ∂P ≤ 1
  setLIntegral_succ_eq : ∀ P ∈ S, ∀ n s, MeasurableSet[ℱ n] s →
    ∫⁻ ω in s, M (n + 1) ω ∂P = ∫⁻ ω in s, M n ω ∂P

/-! ### Supermartingales in `ℝ≥0∞` -/

namespace IsENNSupermartingale

/-- Each value of an `ℝ≥0∞`-valued supermartingale is measurable. -/
theorem measurable (hM : IsENNSupermartingale M ℱ S) (n : ℕ) : Measurable (M n) :=
  (hM.adapted n).mono (ℱ.le n) le_rfl

/-- A supermartingale under every member of `T` is one under every member of a subset of `T`. -/
theorem anti_set (hST : S ⊆ T) (hM : IsENNSupermartingale M ℱ T) :
    IsENNSupermartingale M ℱ S :=
  ⟨hM.adapted, fun P hP ↦ hM.setLIntegral_succ_le P (hST hP)⟩

/-- An adapted process almost surely equal at every time to a supermartingale, under every member
of the null, is a supermartingale. -/
theorem congr (hM : IsENNSupermartingale M ℱ S) (hM' : Adapted ℱ M')
    (h : ∀ P ∈ S, ∀ n, M n =ᵐ[P] M' n) : IsENNSupermartingale M' ℱ S :=
  ⟨hM', fun P hP n s hs ↦ by
    rw [← lintegral_congr_ae (ae_restrict_of_ae (h P hP (n + 1))),
      ← lintegral_congr_ae (ae_restrict_of_ae (h P hP n))]
    exact hM.setLIntegral_succ_le P hP n s hs⟩

/-- The set integrals of an `ℝ≥0∞`-valued supermartingale over an `ℱ i`-measurable set do not
increase after time `i`. -/
theorem setLIntegral_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S) {i j : ℕ} (hij : i ≤ j)
    {s : Set Ω} (hs : MeasurableSet[ℱ i] s) :
    ∫⁻ ω in s, M j ω ∂P ≤ ∫⁻ ω in s, M i ω ∂P := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (hM.setLIntegral_succ_le P hP j s (ℱ.mono hij s hs)).trans ih

/-- The expectations of an `ℝ≥0∞`-valued supermartingale do not increase. -/
theorem lintegral_le (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S) {i j : ℕ} (hij : i ≤ j) :
    ∫⁻ ω, M j ω ∂P ≤ ∫⁻ ω, M i ω ∂P := by
  simpa using hM.setLIntegral_le hP hij MeasurableSet.univ

/-- An `ℝ≥0∞`-valued supermartingale with finite initial expectation is almost surely finite at
every time. -/
theorem ae_lt_top (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) : ∀ᵐ ω ∂P, ∀ n, M n ω < ∞ :=
  ae_all_iff.2 fun n ↦
    MeasureTheory.ae_lt_top (hM.measurable n) ((hM.lintegral_le hP n.zero_le).trans_lt h0.lt_top).ne

/-- An `ℝ≥0∞`-valued supermartingale with finite initial expectation under a finite measure has
real values forming a real supermartingale. -/
theorem supermartingale_toReal (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) :
    Supermartingale (fun n ω ↦ (M n ω).toReal) ℱ P := by
  have hofReal (n : ℕ) : (fun ω ↦ ENNReal.ofReal (M n ω).toReal) =ᵐ[P] M n := by
    filter_upwards [hM.ae_lt_top hP h0] with ω hω using ENNReal.ofReal_toReal (hω n).ne
  refine LMLExplore.supermartingale_of_setLIntegral_succ_le (fun n ↦ (hM.adapted n).ennreal_toReal)
    (fun n ↦ ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)
    (integrable_toReal_of_lintegral_ne_top (hM.measurable 0).aemeasurable h0) fun n s hs ↦ ?_
  rw [lintegral_congr_ae (ae_restrict_of_ae (hofReal (n + 1))),
    lintegral_congr_ae (ae_restrict_of_ae (hofReal n))]
  exact hM.setLIntegral_succ_le P hP n s hs

end IsENNSupermartingale

/-! ### Test supermartingales and test martingales -/

namespace IsTestSupermartingale

/-- Each value of a test supermartingale is measurable. -/
theorem measurable (hM : IsTestSupermartingale M ℱ S) (n : ℕ) : Measurable (M n) :=
  hM.toIsENNSupermartingale.measurable n

/-- A test supermartingale for `T` is one for every subset of `T`. -/
theorem anti_set (hST : S ⊆ T) (hM : IsTestSupermartingale M ℱ T) :
    IsTestSupermartingale M ℱ S :=
  ⟨hM.toIsENNSupermartingale.anti_set hST, fun P hP ↦ hM.lintegral_zero_le P (hST hP)⟩

/-- An adapted process almost surely equal at every time to a test supermartingale, under every
member of the null, is a test supermartingale. -/
theorem congr (hM : IsTestSupermartingale M ℱ S) (hM' : Adapted ℱ M')
    (h : ∀ P ∈ S, ∀ n, M n =ᵐ[P] M' n) : IsTestSupermartingale M' ℱ S :=
  ⟨hM.toIsENNSupermartingale.congr hM' h, fun P hP ↦
    (lintegral_congr_ae (h P hP 0)).symm.trans_le (hM.lintegral_zero_le P hP)⟩

/-- Every value of a test supermartingale has expectation at most `1`. -/
theorem lintegral_le_one (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S) (n : ℕ) :
    ∫⁻ ω, M n ω ∂P ≤ 1 :=
  (hM.lintegral_le hP n.zero_le).trans (hM.lintegral_zero_le P hP)

/-- Every value of a test supermartingale for a null of probability measures is an
e-variable. -/
theorem isEVar (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hM : IsTestSupermartingale M ℱ S)
    (n : ℕ) : IsEVar (M n) S :=
  IsEVar.of_lintegral_le_one hS (hM.measurable n) fun _ hP ↦ hM.lintegral_le_one hP n

/-- A test supermartingale is almost surely finite at every time. -/
theorem ae_lt_top (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S) :
    ∀ᵐ ω ∂P, ∀ n, M n ω < ∞ :=
  hM.toIsENNSupermartingale.ae_lt_top hP
    ((hM.lintegral_zero_le P hP).trans_lt ENNReal.one_lt_top).ne

/-- The real values of a test supermartingale form a real supermartingale under every finite
member of the null. -/
theorem supermartingale_toReal (hM : IsTestSupermartingale M ℱ S) (hP : P ∈ S)
    [IsFiniteMeasure P] : Supermartingale (fun n ω ↦ (M n ω).toReal) ℱ P :=
  hM.toIsENNSupermartingale.supermartingale_toReal hP
    ((hM.lintegral_zero_le P hP).trans_lt ENNReal.one_lt_top).ne

end IsTestSupermartingale

namespace IsTestMartingale

/-- Each value of a test martingale is measurable. -/
theorem measurable (hM : IsTestMartingale M ℱ S) (n : ℕ) : Measurable (M n) :=
  (hM.adapted n).mono (ℱ.le n) le_rfl

/-- A test martingale is a test supermartingale. -/
theorem isTestSupermartingale (hM : IsTestMartingale M ℱ S) : IsTestSupermartingale M ℱ S :=
  ⟨⟨hM.adapted, fun P hP n s hs ↦ (hM.setLIntegral_succ_eq P hP n s hs).le⟩,
    hM.lintegral_zero_le⟩

/-- A test martingale for `T` is one for every subset of `T`. -/
theorem anti_set (hST : S ⊆ T) (hM : IsTestMartingale M ℱ T) : IsTestMartingale M ℱ S :=
  ⟨hM.adapted, fun P hP ↦ hM.lintegral_zero_le P (hST hP),
    fun P hP ↦ hM.setLIntegral_succ_eq P (hST hP)⟩

/-- An adapted process almost surely equal at every time to a test martingale, under every member
of the null, is a test martingale. -/
theorem congr (hM : IsTestMartingale M ℱ S) (hM' : Adapted ℱ M')
    (h : ∀ P ∈ S, ∀ n, M n =ᵐ[P] M' n) : IsTestMartingale M' ℱ S :=
  ⟨hM', fun P hP ↦ (lintegral_congr_ae (h P hP 0)).symm.trans_le (hM.lintegral_zero_le P hP),
    fun P hP n s hs ↦ by
      rw [← lintegral_congr_ae (ae_restrict_of_ae (h P hP (n + 1))),
        ← lintegral_congr_ae (ae_restrict_of_ae (h P hP n))]
      exact hM.setLIntegral_succ_eq P hP n s hs⟩

/-- The set integrals of a test martingale over an `ℱ i`-measurable set are constant after
time `i`. -/
theorem setLIntegral_eq (hM : IsTestMartingale M ℱ S) (hP : P ∈ S) {i j : ℕ} (hij : i ≤ j)
    {s : Set Ω} (hs : MeasurableSet[ℱ i] s) :
    ∫⁻ ω in s, M j ω ∂P = ∫⁻ ω in s, M i ω ∂P := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih => exact (hM.setLIntegral_succ_eq P hP j s (ℱ.mono hij s hs)).trans ih

/-- The expectations of a test martingale are constant. -/
theorem lintegral_eq (hM : IsTestMartingale M ℱ S) (hP : P ∈ S) (i j : ℕ) :
    ∫⁻ ω, M j ω ∂P = ∫⁻ ω, M i ω ∂P := by
  have h (n : ℕ) : ∫⁻ ω, M n ω ∂P = ∫⁻ ω, M 0 ω ∂P := by
    simpa using hM.setLIntegral_eq hP n.zero_le MeasurableSet.univ
  rw [h j, h i]

end IsTestMartingale

/-- The constant process `1` is a test martingale for every null of probability measures. -/
theorem isTestMartingale_one (hS : ∀ P ∈ S, IsProbabilityMeasure P) :
    IsTestMartingale 1 ℱ S :=
  ⟨fun _ ↦ measurable_const, fun P hP ↦ by have := hS P hP; simp, fun _ _ _ _ _ ↦ rfl⟩

/-- A real nonnegative supermartingale with initial expectation at most `1` is, through
`ENNReal.ofReal`, a test supermartingale for the null `{P}`. -/
theorem _root_.MeasureTheory.Supermartingale.isTestSupermartingale_ofReal
    [SigmaFiniteFiltration P ℱ] {M : ℕ → Ω → ℝ} (hM : Supermartingale M ℱ P)
    (hM_nonneg : ∀ n, 0 ≤ᵐ[P] M n) (h0 : ∫ ω, M 0 ω ∂P ≤ 1) :
    IsTestSupermartingale (fun n ω ↦ ENNReal.ofReal (M n ω)) ℱ {P} := by
  refine ⟨⟨fun n ↦ (hM.stronglyAdapted n).measurable.ennreal_ofReal, ?_⟩, ?_⟩
  · rintro P' rfl n s hs
    rw [← ofReal_integral_eq_lintegral_ofReal (hM.integrable (n + 1)).restrict
        (ae_restrict_of_ae (hM_nonneg (n + 1))),
      ← ofReal_integral_eq_lintegral_ofReal (hM.integrable n).restrict
        (ae_restrict_of_ae (hM_nonneg n))]
    exact ENNReal.ofReal_le_ofReal (hM.setIntegral_le n.le_succ hs)
  · rintro P' rfl
    rw [← ofReal_integral_eq_lintegral_ofReal (hM.integrable 0) (hM_nonneg 0)]
    exact ENNReal.ofReal_le_one.2 h0

/-! ### Wealth processes -/

/-- **Wealth of a reinvesting gambler.** For an `ℱ 0`-measurable initial wealth `M₀` with
expectation at most `1` under every member of `S`, and factors `F k` that are
`ℱ (k + 1)`-measurable conditional e-variables given `ℱ k`, the wealth
`M₀ * ∏ k < n, F k` is a test supermartingale. -/
theorem isTestSupermartingale_mul_prod {M₀ : Ω → ℝ≥0∞} (hM₀ : Measurable[ℱ 0] M₀)
    (hM₀_le : ∀ P ∈ S, ∫⁻ ω, M₀ ω ∂P ≤ 1) {F : ℕ → Ω → ℝ≥0∞}
    (hF_meas : ∀ k, Measurable[ℱ (k + 1)] (F k)) (hF : ∀ k, IsCondEVar (F k) (ℱ k) S) :
    IsTestSupermartingale (fun n ω ↦ M₀ ω * ∏ k ∈ range n, F k ω) ℱ S := by
  refine ⟨⟨adapted_mul_prod_range hM₀ hF_meas, fun P hP n s hs ↦ ?_⟩, by simpa using hM₀_le⟩
  simp_rw [prod_range_succ, ← mul_assoc]
  exact (hF n).setLIntegral_mul_le (ℱ.le n) hP (adapted_mul_prod_range hM₀ hF_meas n) hs

/-- **Wealth of a reinvesting gambler, exact case.** For an `ℱ 0`-measurable initial wealth `M₀`
with expectation at most `1` under every member of `S`, and factors `F k` that are
`ℱ (k + 1)`-measurable exact conditional e-variables given `ℱ k`, the wealth
`M₀ * ∏ k < n, F k` is a test martingale. -/
theorem isTestMartingale_mul_prod {M₀ : Ω → ℝ≥0∞} (hM₀ : Measurable[ℱ 0] M₀)
    (hM₀_le : ∀ P ∈ S, ∫⁻ ω, M₀ ω ∂P ≤ 1) {F : ℕ → Ω → ℝ≥0∞}
    (hF_meas : ∀ k, Measurable[ℱ (k + 1)] (F k)) (hF : ∀ k, IsExactCondEVar (F k) (ℱ k) S) :
    IsTestMartingale (fun n ω ↦ M₀ ω * ∏ k ∈ range n, F k ω) ℱ S := by
  refine ⟨adapted_mul_prod_range hM₀ hF_meas, by simpa using hM₀_le, fun P hP n s hs ↦ ?_⟩
  simp_rw [prod_range_succ, ← mul_assoc]
  exact (hF n).setLIntegral_mul_eq (ℱ.le n) hP (adapted_mul_prod_range hM₀ hF_meas n) hs

/-- **Wealth of portfolios** [WSJ26]. For conditional e-variables `E k i` given `ℱ k` that are
`ℱ (k + 1)`-measurable, and `ℱ k`-measurable portfolios `w k` with `∑ i, w k ω i ≤ 1`, the wealth
`M₀ * ∏ k < n, ∑ i, w k ω i * E k i ω` is a test supermartingale for every `ℱ 0`-measurable
initial wealth `M₀` with expectation at most `1`. -/
theorem isTestSupermartingale_portfolio [Fintype ι] {M₀ : Ω → ℝ≥0∞}
    (hM₀ : Measurable[ℱ 0] M₀) (hM₀_le : ∀ P ∈ S, ∫⁻ ω, M₀ ω ∂P ≤ 1)
    {E : ℕ → ι → Ω → ℝ≥0∞} (hE_meas : ∀ k i, Measurable[ℱ (k + 1)] (E k i))
    (hE : ∀ k i, IsCondEVar (E k i) (ℱ k) S) {w : ℕ → Ω → ι → ℝ≥0∞}
    (hw : ∀ k i, Measurable[ℱ k] (fun ω ↦ w k ω i)) (hw_sum : ∀ k ω, ∑ i, w k ω i ≤ 1) :
    IsTestSupermartingale (fun n ω ↦ M₀ ω * ∏ k ∈ range n, ∑ i, w k ω i * E k i ω) ℱ S :=
  isTestSupermartingale_mul_prod hM₀ hM₀_le
    (fun k ↦ Finset.measurable_fun_sum _ fun i _ ↦
      ((hw k i).mono (ℱ.mono k.le_succ) le_rfl).mul (hE_meas k i))
    fun k ↦ isCondEVar_sum_mul (ℱ.le k) (hE k) (hw k) (hw_sum k)

/-- **Wealth of portfolios, exact case** [WSJ26]. For exact conditional e-variables `E k i` given
`ℱ k` that are `ℱ (k + 1)`-measurable, and `ℱ k`-measurable portfolios `w k` with
`∑ i, w k ω i = 1`, the wealth `M₀ * ∏ k < n, ∑ i, w k ω i * E k i ω` is a test martingale for
every `ℱ 0`-measurable initial wealth `M₀` with expectation at most `1`. -/
theorem isTestMartingale_portfolio [Fintype ι] {M₀ : Ω → ℝ≥0∞}
    (hM₀ : Measurable[ℱ 0] M₀) (hM₀_le : ∀ P ∈ S, ∫⁻ ω, M₀ ω ∂P ≤ 1)
    {E : ℕ → ι → Ω → ℝ≥0∞} (hE_meas : ∀ k i, Measurable[ℱ (k + 1)] (E k i))
    (hE : ∀ k i, IsExactCondEVar (E k i) (ℱ k) S) {w : ℕ → Ω → ι → ℝ≥0∞}
    (hw : ∀ k i, Measurable[ℱ k] (fun ω ↦ w k ω i)) (hw_sum : ∀ k ω, ∑ i, w k ω i = 1) :
    IsTestMartingale (fun n ω ↦ M₀ ω * ∏ k ∈ range n, ∑ i, w k ω i * E k i ω) ℱ S :=
  isTestMartingale_mul_prod hM₀ hM₀_le
    (fun k ↦ Finset.measurable_fun_sum _ fun i _ ↦
      ((hw k i).mono (ℱ.mono k.le_succ) le_rfl).mul (hE_meas k i))
    fun k ↦ isExactCondEVar_sum_mul (ℱ.le k) (hE k) (hw k) (hw_sum k)

/-- **Products of sequential e-variables** [RW, Proposition 7.20; GdHK24, Proposition 2]. For
conditional e-variables `E k` given `ℱ k` that are `ℱ (k + 1)`-measurable, `∏ k < n, E k` is a
test supermartingale for every null of probability measures. -/
theorem isTestSupermartingale_prod (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    {E : ℕ → Ω → ℝ≥0∞} (hE_meas : ∀ k, Measurable[ℱ (k + 1)] (E k))
    (hE : ∀ k, IsCondEVar (E k) (ℱ k) S) :
    IsTestSupermartingale (fun n ω ↦ ∏ k ∈ range n, E k ω) ℱ S := by
  simpa using isTestSupermartingale_portfolio (ℱ := ℱ) (ι := Unit) (M₀ := 1) (w := fun _ _ _ ↦ 1)
    measurable_const (fun P hP ↦ by have := hS P hP; simp) (fun k _ ↦ hE_meas k)
    (fun k _ ↦ hE k) (fun _ _ ↦ measurable_const) (fun _ _ ↦ by simp)

/-- **Products of sequential e-variables, exact case.** For exact conditional e-variables `E k`
given `ℱ k` that are `ℱ (k + 1)`-measurable, `∏ k < n, E k` is a test martingale for every null
of probability measures. -/
theorem isTestMartingale_prod (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    {E : ℕ → Ω → ℝ≥0∞} (hE_meas : ∀ k, Measurable[ℱ (k + 1)] (E k))
    (hE : ∀ k, IsExactCondEVar (E k) (ℱ k) S) :
    IsTestMartingale (fun n ω ↦ ∏ k ∈ range n, E k ω) ℱ S := by
  simpa using isTestMartingale_portfolio (ℱ := ℱ) (ι := Unit) (M₀ := 1) (w := fun _ _ _ ↦ 1)
    measurable_const (fun P hP ↦ by have := hS P hP; simp) (fun k _ ↦ hE_meas k)
    (fun k _ ↦ hE k) (fun _ _ ↦ measurable_const) (fun _ _ ↦ by simp)

/-- **Betting** [RW, Definition 7.21; WSR24]. For conditional e-variables `E k` given `ℱ k` that
are `ℱ (k + 1)`-measurable, and `ℱ k`-measurable bets `c k ≤ 1`, the wealth
`∏ k < n, (1 - c k + c k * E k)` is a test supermartingale for every null of probability
measures. -/
theorem isTestSupermartingale_betting_condEVar (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    {E : ℕ → Ω → ℝ≥0∞} (hE_meas : ∀ k, Measurable[ℱ (k + 1)] (E k))
    (hE : ∀ k, IsCondEVar (E k) (ℱ k) S) {c : ℕ → Ω → ℝ≥0∞}
    (hc : ∀ k, Measurable[ℱ k] (c k)) (hc_le : ∀ k ω, c k ω ≤ 1) :
    IsTestSupermartingale (fun n ω ↦ ∏ k ∈ range n, (1 - c k ω + c k ω * E k ω)) ℱ S := by
  have := isTestSupermartingale_portfolio (ℱ := ℱ) (M₀ := 1) (w := fun k ω ↦ ![1 - c k ω, c k ω])
    (E := fun k ↦ ![1, E k]) measurable_const (fun P hP ↦ by have := hS P hP; simp)
    (fun k i ↦ by fin_cases i <;> simp [measurable_one, hE_meas k])
    (fun k i ↦ by fin_cases i <;> simp [hE k])
    (fun k i ↦ by fin_cases i <;> simp [(hc k).const_sub, hc k])
    (fun k ω ↦ by simp [tsub_add_cancel_of_le (hc_le k ω)])
  simpa [Fin.sum_univ_two] using this

/-- **Betting, exact case.** For exact conditional e-variables `E k` given `ℱ k` that are
`ℱ (k + 1)`-measurable, and `ℱ k`-measurable bets `c k ≤ 1`, the wealth
`∏ k < n, (1 - c k + c k * E k)` is a test martingale for every null of probability measures. -/
theorem isTestMartingale_betting_condEVar (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    {E : ℕ → Ω → ℝ≥0∞} (hE_meas : ∀ k, Measurable[ℱ (k + 1)] (E k))
    (hE : ∀ k, IsExactCondEVar (E k) (ℱ k) S) {c : ℕ → Ω → ℝ≥0∞}
    (hc : ∀ k, Measurable[ℱ k] (c k)) (hc_le : ∀ k ω, c k ω ≤ 1) :
    IsTestMartingale (fun n ω ↦ ∏ k ∈ range n, (1 - c k ω + c k ω * E k ω)) ℱ S := by
  have := isTestMartingale_portfolio (ℱ := ℱ) (M₀ := 1) (w := fun k ω ↦ ![1 - c k ω, c k ω])
    (E := fun k ↦ ![1, E k]) measurable_const (fun P hP ↦ by have := hS P hP; simp)
    (fun k i ↦ by fin_cases i <;> simp [measurable_one, hE_meas k])
    (fun k i ↦ by fin_cases i <;> simp [hE k])
    (fun k i ↦ by fin_cases i <;> simp [(hc k).const_sub, hc k])
    (fun k ω ↦ by simp [tsub_add_cancel_of_le (hc_le k ω)])
  simpa [Fin.sum_univ_two] using this

/-! ### Test supermartingales as wealth processes -/

/-- The successive ratios `M (k + 1) / M k` of an `ℝ≥0∞`-valued supermartingale, with
`0 / 0 = 0` and `x / ∞ = 0`, are conditional e-variables given `ℱ k`. -/
theorem IsENNSupermartingale.isCondEVar_div (hM : IsENNSupermartingale M ℱ S) (k : ℕ) :
    IsCondEVar (fun ω ↦ M (k + 1) ω / M k ω) (ℱ k) S := by
  refine ⟨(hM.measurable (k + 1)).div (hM.measurable k), fun P hP s hs ↦ ?_⟩
  -- pull the `ℱ k`-measurable factor `𝟙_s / M k` out of the supermartingale inequality
  have hY : Measurable[ℱ k] (s.indicator fun ω ↦ (M k ω)⁻¹) := (hM.adapted k).inv.indicator hs
  calc ∫⁻ ω in s, M (k + 1) ω / M k ω ∂P
      = ∫⁻ ω, s.indicator (fun ω ↦ (M k ω)⁻¹) ω * M (k + 1) ω ∂P := by
        rw [← lintegral_indicator (ℱ.le k s hs)]
        congr 1 with ω
        by_cases hω : ω ∈ s <;> simp [hω, div_eq_mul_inv, mul_comm]
    _ ≤ ∫⁻ ω, s.indicator (fun ω ↦ (M k ω)⁻¹) ω * M k ω ∂P :=
        lintegral_mul_le_lintegral_mul_of_forall_setLIntegral_le (ℱ.le k)
          (hM.measurable (k + 1)).aemeasurable (hM.measurable k).aemeasurable
          (hM.setLIntegral_succ_le P hP k) hY
    _ ≤ ∫⁻ ω, s.indicator 1 ω ∂P := lintegral_mono fun ω ↦ by
        by_cases hω : ω ∈ s <;> simp [hω, ENNReal.inv_mul_le_one]
    _ = P s := lintegral_indicator_one (ℱ.le k s hs)

/-- **`ℝ≥0∞`-valued supermartingales are wealth processes** [WSR24, Proposition 3]. An
`ℝ≥0∞`-valued supermartingale with finite initial expectation under `P` is `P`-almost surely its
initial value times the product of its successive ratios `M (k + 1) / M k`, with `0 / 0 = 0`;
these ratios are conditional e-variables (`IsENNSupermartingale.isCondEVar_div`). -/
theorem IsENNSupermartingale.ae_eq_mul_prod_div (hM : IsENNSupermartingale M ℱ S) (hP : P ∈ S)
    (h0 : ∫⁻ ω, M 0 ω ∂P ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ n, M n ω = M 0 ω * ∏ k ∈ range n, M (k + 1) ω / M k ω := by
  -- almost surely, the process stays at `0` once it reaches it
  have hzero : ∀ᵐ ω ∂P, ∀ k, M k ω = 0 → M (k + 1) ω = 0 := by
    refine ae_all_iff.2 fun k ↦ ?_
    have hs : MeasurableSet[ℱ k] {ω | M k ω = 0} := hM.adapted k (measurableSet_singleton 0)
    have h : ∫⁻ ω in {ω | M k ω = 0}, M (k + 1) ω ∂P = 0 := by
      refine le_antisymm ((hM.setLIntegral_succ_le P hP k _ hs).trans_eq ?_) bot_le
      exact (setLIntegral_eq_zero_iff (ℱ.le k _ hs) (hM.measurable k)).2
        (ae_of_all _ fun _ hω ↦ hω)
    exact (setLIntegral_eq_zero_iff (ℱ.le k _ hs) (hM.measurable (k + 1))).1 h
  filter_upwards [hzero, hM.ae_lt_top hP h0] with ω hz hfin n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ← mul_assoc, ← ih]
    rcases eq_or_ne (M n ω) 0 with h | h
    · simp [h, hz n h]
    · exact (ENNReal.mul_div_cancel h (hfin n).ne).symm

/-- **Test supermartingales are wealth processes** [WSR24, Proposition 3]. A test supermartingale
is almost surely, under every member of the null, its initial value times the product of its
successive ratios `M (k + 1) / M k`, with `0 / 0 = 0`, which are conditional e-variables. -/
theorem IsTestSupermartingale.ae_eq_mul_prod_div (hM : IsTestSupermartingale M ℱ S)
    (hP : P ∈ S) :
    ∀ᵐ ω ∂P, ∀ n, M n ω = M 0 ω * ∏ k ∈ range n, M (k + 1) ω / M k ω :=
  hM.toIsENNSupermartingale.ae_eq_mul_prod_div hP
    ((hM.lintegral_zero_le P hP).trans_lt ENNReal.one_lt_top).ne

end ProbabilityTheory
