/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.InformationTheory.KullbackLeibler.Cond
public import Mathlib.MeasureTheory.Constructions.Pi
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.InformationTheory.KullbackLeibler.Pi
import LMLExplore.Probability.LargeDeviations.EmpiricalAverage
import LMLExplore.Probability.ProductMeasure
import Statlib.Divergence.KullbackLeibler.Basic
import TauCeti.Probability.StrongLaw

/-!
# Empirical averages of integrable functions under product laws

For countably many measurable functions `f i` on `𝓧`, integrable but possibly unbounded, and `m`
observations `x : Fin m → 𝓧`, this file bounds the probability under an i.i.d. law `P ^ m` that
the empirical averages `(∑ j, f i (x j)) / m` lie within `ε` of given values `a i`, from both
sides.

* From above, by a Sanov-type bound [Csi84]: if every probability measure `R` that integrates the
  `f i` with `|∫ f i dR - a i| ≤ ε` is at relative entropy at least `c` from `P`, the probability
  is at most `exp (- m c)`. This is Csiszár's argument for Sanov's upper bound on a convex set:
  condition `P ^ m` on the event, whose relative entropy to `P ^ m` is at most
  `log (1 / P ^ m (A))` (`InformationTheory.klDiv_cond_le`), and bound it from below by the
  superadditivity of the relative entropy over the coordinates
  (`InformationTheory.sum_klDiv_map_eval_le`) and its convexity, at the average of the marginals
  of the conditioned law. That average integrates the `f i`, since each marginal of the
  conditioned law is at most `P / P ^ m (A)`, so it satisfies the constraints.
* From below, by the weak law of large numbers, deduced from the strong law: the probability
  that the empirical average of an integrable `g` is more than `ε` away from `q` tends to `0` when
  `|∫ g dQ - q| < ε`.

`LMLExplore.Probability.LargeDeviations.EmpiricalAverage` has the Sanov-type bound for finitely
many bounded functions and the weak law with Chebyshev's rate for square-integrable ones; the
bound here is for integrable functions, as the test functions of the boxes of
`LMLExplore.EValues.BipolarRate.Design.TestEnvelope` need.

## Main statements

* `ProbabilityTheory.ofReal_exp_mul_measure_pi_le_one_of_integrable`: the Sanov-type bound for
  countably many integrable functions.
* `ProbabilityTheory.ofReal_exp_mul_le_one_of_ofReal_le_klDiv_cond`: Csiszár's conditioning step,
  `exp c * P A ≤ 1` when the law conditioned on `A` is at relative entropy at least `c` from `P`.
* `ProbabilityTheory.mul_klDiv_sum_smul_map_eval_le`: `m` times the relative entropy from the
  average of the marginals of a law on `Fin m → 𝓧` is at most the sum of the relative entropies
  of the marginals.
* `ProbabilityTheory.tendsto_measure_pi_lt_abs_sum_div_sub`: the weak law of large numbers for an
  integrable function.

## Implementation notes

The statements and proofs are adapted from `EValuesResearch/Results/DesignTestFunctionsAux.lean`
(commit `cb8238f`) in the paper project `RemyDegenne/evalues_research`, rewritten on the API of
LMLExplore; the bound for one sample space follows the proof of
`ProbabilityTheory.ofReal_exp_mul_measure_pi_le_one`.

## References

* [Csi84] I. Csiszár, *Sanov property, generalized I-projection and a conditional limit theorem*,
  Ann. Probab. 12 (1984), 768–793.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 55 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 55, *Classes that are not dominated: attaining the rate and `D*`
  with one procedure*, Proposition 8.
-/

public section

open MeasureTheory InformationTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-! ### The average of the marginals -/

/-- A measurable function that is integrable along every coordinate under a measure `μ` on
`Fin m → 𝓧` is integrable under the average of the marginals of `μ`. -/
lemma integrable_sum_smul_map_eval {m : ℕ} (μ : Measure (Fin m → 𝓧)) {g : 𝓧 → ℝ}
    (hg : Measurable g) (hgμ : ∀ j, Integrable (fun x ↦ g (x j)) μ) :
    Integrable g (∑ j : Fin m, (((m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) • μ.map fun x ↦ x j) :=
  integrable_finsetSum_measure.2 fun j _ ↦ ((integrable_map_measure hg.aestronglyMeasurable
    (measurable_pi_apply j).aemeasurable).2 (hgμ j)).smul_measure ENNReal.coe_ne_top

/-- The integral of a measurable function `g`, integrable along every coordinate under `μ`, against
the average of the marginals of `μ` is the integral of the empirical average of `g` against `μ`.
This is `ProbabilityTheory.integral_sum_smul_map_eval` for integrable rather than bounded `g`. -/
lemma integral_sum_smul_map_eval_of_integrable {m : ℕ} (μ : Measure (Fin m → 𝓧)) {g : 𝓧 → ℝ}
    (hg : Measurable g) (hgμ : ∀ j, Integrable (fun x ↦ g (x j)) μ) :
    ∫ x, g x ∂(∑ j : Fin m, (((m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) • μ.map fun x ↦ x j) =
      ∫ x, (∑ j, g (x j)) / m ∂μ := by
  rw [integral_finsetSum_measure fun j _ ↦ ((integrable_map_measure hg.aestronglyMeasurable
    (measurable_pi_apply j).aemeasurable).2 (hgμ j)).smul_measure ENNReal.coe_ne_top]
  have hj (j : Fin m) : ∫ x, g x ∂(μ.map fun x ↦ x j) = ∫ x, g (x j) ∂μ :=
    integral_map (measurable_pi_apply j).aemeasurable hg.aestronglyMeasurable
  simp_rw [integral_smul_measure, hj]
  rw [integral_div, integral_finsetSum _ fun j _ ↦ hgμ j]
  simp [div_eq_inv_mul, Finset.mul_sum]

/-- If the empirical average of a measurable `g`, integrable along every coordinate, is almost
surely within `ε` of `a` under a probability measure `μ` on `Fin m → 𝓧`, then so is the integral
of `g` against the average of the marginals of `μ`. This is
`ProbabilityTheory.abs_integral_sum_smul_map_eval_sub_le` for integrable rather than bounded
`g`. -/
lemma abs_integral_sum_smul_map_eval_sub_le_of_integrable {m : ℕ} (μ : Measure (Fin m → 𝓧))
    [IsProbabilityMeasure μ] {g : 𝓧 → ℝ} (hg : Measurable g)
    (hgμ : ∀ j, Integrable (fun x ↦ g (x j)) μ) {a ε : ℝ}
    (hμ : ∀ᵐ x ∂μ, |(∑ j, g (x j)) / m - a| ≤ ε) :
    |∫ x, g x ∂(∑ j : Fin m, (((m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) • μ.map fun x ↦ x j) - a| ≤ ε := by
  rw [integral_sum_smul_map_eval_of_integrable μ hg hgμ]
  have hint : Integrable (fun x : Fin m → 𝓧 ↦ (∑ j, g (x j)) / m) μ :=
    (integrable_finsetSum _ fun j _ ↦ hgμ j).div_const _
  have heq : ∫ x, (∑ j, g (x j)) / m ∂μ - a = ∫ x, ((∑ j, g (x j)) / m - a) ∂μ := by
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [heq, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ε) ?_).trans (by simp)
  simpa only [Real.norm_eq_abs] using hμ

/-- **Convexity over the coordinates.** For a finite measure `μ` on `Fin m → 𝓧` and a finite
measure `P` on `𝓧`, `m` times the relative entropy from the average of the marginals of `μ` to `P`
is at most the sum of the relative entropies of the marginals to `P`. -/
lemma mul_klDiv_sum_smul_map_eval_le {m : ℕ} (μ : Measure (Fin m → 𝓧)) [IsFiniteMeasure μ]
    (P : Measure 𝓧) [IsFiniteMeasure P] :
    (m : ℝ≥0∞) * klDiv (∑ j : Fin m, (((m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) • μ.map fun x ↦ x j) P ≤
      ∑ j, klDiv (μ.map fun x ↦ x j) P := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hw : ∑ _j : Fin m, ((m : ℝ≥0)⁻¹ : ℝ≥0) = 1 := by
    simp [hm]
  calc (m : ℝ≥0∞) * klDiv (∑ j : Fin m, (((m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) • μ.map fun x ↦ x j) P
  _ ≤ m * ∑ j : Fin m, (((m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * klDiv (μ.map fun x ↦ x j) P := by
    gcongr
    exact klDiv_sum_smul_left_le hw
  _ = ∑ j, klDiv (μ.map fun x ↦ x j) P := by
    simp [Finset.mul_sum, ← mul_assoc, ENNReal.coe_inv, hm, ENNReal.mul_inv_cancel]

/-! ### The Sanov-type bound -/

/-- **Csiszár's conditioning step.** If the probability measure `P` conditioned on an event `A` of
positive probability is at relative entropy at least `c` from `P`, then `exp c * P A ≤ 1`: that
relative entropy is at most `log (1 / P A)` (`InformationTheory.klDiv_cond_le`). -/
lemma ofReal_exp_mul_le_one_of_ofReal_le_klDiv_cond {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {A : Set Ω} (hA : P A ≠ 0) {c : ℝ}
    (h : ENNReal.ofReal c ≤ klDiv (P[|A]) P) :
    ENNReal.ofReal (Real.exp c) * P A ≤ 1 := by
  have hc : ((c : ℝ) : EReal) ≤ ENNReal.log (P A)⁻¹ := by
    calc ((c : ℝ) : EReal)
    _ ≤ ((ENNReal.ofReal c : ℝ≥0∞) : EReal) := by
      rw [EReal.coe_ennreal_ofReal]
      exact EReal.coe_le_coe_iff.2 (le_max_left c 0)
    _ ≤ (klDiv (P[|A]) P : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.2 h
    _ ≤ ENNReal.log (P A)⁻¹ := klDiv_cond_le hA
  refine ENNReal.le_inv_iff_mul_le.1 (ENNReal.log_le_log_iff.1 ?_)
  rwa [ENNReal.log_ofReal_exp]

/-- **Sanov-type bound for integrable functions** [Csi84]. Let `f i`, for `i` in a countable type,
be measurable and `P`-integrable functions. If every probability measure `R` that integrates the
`f i` with `|∫ f i dR - a i| ≤ ε` for every `i` is at relative entropy at least `c` from `P`, then
the probability under `P ^ m` that the empirical averages of all the `f i` are within `ε` of the
`a i` is at most `exp (- m c)`. The functions need not be bounded: this is
`ProbabilityTheory.ofReal_exp_mul_measure_pi_le_one` for integrable functions. -/
theorem ofReal_exp_mul_measure_pi_le_one_of_integrable {ι : Type*} [Countable ι]
    {f : ι → 𝓧 → ℝ} (hf : ∀ i, Measurable (f i)) {P : Measure 𝓧} [IsProbabilityMeasure P]
    (hfP : ∀ i, Integrable (f i) P) {a : ι → ℝ} {ε c : ℝ}
    (hU : ∀ R : Measure 𝓧, IsProbabilityMeasure R →
      (∀ i, Integrable (f i) R ∧ |∫ x, f i x ∂R - a i| ≤ ε) → ENNReal.ofReal c ≤ klDiv R P)
    (m : ℕ) :
    ENNReal.ofReal (Real.exp (m * c)) *
      (Measure.pi fun _ : Fin m ↦ P) {x | ∀ i, |(∑ j, f i (x j)) / m - a i| ≤ ε} ≤ 1 := by
  set A := {x : Fin m → 𝓧 | ∀ i, |(∑ j, f i (x j)) / m - a i| ≤ ε}
  set Pm := Measure.pi fun _ : Fin m ↦ P
  rcases eq_or_ne m 0 with rfl | hm
  · simpa using prob_le_one
  rcases eq_or_ne (Pm A) 0 with h0 | h0
  · simp [h0]
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ measurableSet_le (by fun_prop) measurable_const
  -- the law `μ` of `m` observations conditioned on the event, and the average `R` of its marginals
  set μ := Pm[|A]
  have : IsProbabilityMeasure μ := cond_isProbabilityMeasure h0
  have hfμ (i : ι) (j : Fin m) : Integrable (fun x ↦ f i (x j)) μ :=
    ((measurePreserving_eval (fun _ : Fin m ↦ P) j).integrable_comp_of_integrable
      (hfP i)).restrict.smul_measure (ENNReal.inv_ne_top.2 h0)
  set R := ∑ j : Fin m, (((m : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) • μ.map fun x ↦ x j
  have hR : IsProbabilityMeasure R := isProbabilityMeasure_sum_smul_map_eval hm μ
  have hRU (i : ι) : Integrable (f i) R ∧ |∫ x, f i x ∂R - a i| ≤ ε := by
    refine ⟨integrable_sum_smul_map_eval μ (hf i) (hfμ i),
      abs_integral_sum_smul_map_eval_sub_le_of_integrable μ (hf i) (hfμ i) ?_⟩
    filter_upwards [ae_cond_mem hA] with x hx
    exact hx i
  -- `R` satisfies the constraints, so by convexity and superadditivity over the coordinates the
  -- relative entropy from `μ` to `P ^ m` is at least `m c`
  refine ofReal_exp_mul_le_one_of_ofReal_le_klDiv_cond h0 ?_
  calc ENNReal.ofReal (m * c)
  _ ≤ m * ENNReal.ofReal c := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  _ ≤ m * klDiv R P := by
    gcongr
    exact hU R hR hRU
  _ ≤ ∑ j, klDiv (μ.map fun x ↦ x j) P := mul_klDiv_sum_smul_map_eval_le μ P
  _ ≤ klDiv μ Pm := sum_klDiv_map_eval_le (fun _ ↦ P) μ

/-! ### The weak law of large numbers -/

/-- **Weak law of large numbers** for an integrable function, from the strong law: if
`|∫ g dQ - q| < ε`, the probability under `Q ^ m` that the empirical average of `g` is more than
`ε` away from `q` tends to `0`. -/
theorem tendsto_measure_pi_lt_abs_sum_div_sub {Q : Measure 𝓧} [IsProbabilityMeasure Q]
    {g : 𝓧 → ℝ} (hg : Measurable g) (hgQ : Integrable g Q) {q ε : ℝ}
    (hq : |∫ y, g y ∂Q - q| < ε) :
    Tendsto (fun m : ℕ ↦ (Measure.pi fun _ : Fin m ↦ Q) {x | ε < |(∑ j, g (x j)) / m - q|})
      atTop (𝓝 0) := by
  refine tendsto_measure_pi_zero_of_ae_eventually_notMem Q
    (fun m ↦ measurableSet_lt measurable_const (by fun_prop)) ?_
  have hopen : IsOpen {y : ℝ | |y - q| < ε} :=
    isOpen_lt (continuous_abs.comp (continuous_sub_right q)) continuous_const
  filter_upwards [TauCeti.Probability.strong_law_ae_infinitePi Q hgQ] with ω hω
  filter_upwards [hω.eventually (hopen.mem_nhds hq)] with m hm
  simp only [initSeg_def, not_lt, smul_eq_mul] at hm ⊢
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ g (ω i)) m, div_eq_inv_mul]
  exact hm.le

end ProbabilityTheory
