/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import LMLExplore.EValues.Null.Basic
public import LMLExplore.Probability.Distributions.ProdBernoulli
public import LMLExplore.Probability.Martingale.TestSupermartingale
public import Mathlib.Probability.Process.HittingTime
import LMLExplore.EValues.BipolarRate.Finite
import LMLExplore.EValues.EffectiveSet.Basic
import LMLExplore.EValues.TestSupermartingale.ConvexHull
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Condorcet null: one observation carries no evidence, at a positive bipolar rate

Three candidates are compared in pairs; an observation is a vector of three independent coins,
the coin `0` (resp. `1`) showing whether candidate 1 beats candidate 2 (resp. 3), with law
`prodBernoulli θ` for parameters `θ` in the box `[1/20, 19/20] ^ 3`. The null "candidate 1 is not
the Condorcet winner", closed, is the set of the laws `prodBernoulli θ` for `θ` in the box with
`θ 0 ≤ 1/2` or `θ 1 ≤ 1/2`, a union of two convex pieces; the alternative is the law of the coins
`(7/10, 3/5, c)`, for `c` in `[1/20, 19/20]` [EVR26, Note 32, Statement 3].

* The alternative is a mixture of three laws of the null, the coins `(19/20, 1/2, c)`,
  `(1/2, 19/20, c)` and `(t, t, c)` with `t = (11/100 - √(7/1000)) / (3/10)`, with weights about
  `0.5523`, `0.3300` and `0.1177`. So one observation carries no evidence, `a₁ = 0`, and every test
  supermartingale for the i.i.d. null, being one for the i.i.d. null of the convex hull
  (`ProbabilityTheory.isTestSupermartingale_iidNull_convexHull`), has tests with no power against
  the alternative: they reject with probability at most their level under its i.i.d. law.
* The bipolar rate is nevertheless the smallest relative entropy `KL_inf` from the alternative to
  the null, `kl(3/5, 1/2)`, about `0.0201`, attained at the coins `(7/10, 1/2, c)`: on the finite
  alphabet of the three coins, the bipolar rate is `KL_inf` for every null
  (`ProbabilityTheory.bipolarRate_eq_klInf_of_finite`). Since the null is a finite union of convex
  pieces, the minimum over the pieces of the likelihood ratios against the projections on the
  pieces attains it (`ProbabilityTheory.ae_tendsto_log_minLikelihoodRatio_prodBernoulli_div`).

## Main definitions

* `ProbabilityTheory.condorcetParams`: the parameters of the Condorcet null.

## Main statements

* `ProbabilityTheory.prodBernoulli_condorcet_mem_convexHull`: the alternative is in the convex
  hull of the null.
* `ProbabilityTheory.maxEPower_prodBernoulli_condorcet_eq_zero`: `a₁ = 0`.
* `ProbabilityTheory.measure_hittingAfter_lt_top_le_condorcet`: the tests of the test
  supermartingales for the i.i.d. null have no power against the alternative.
* `ProbabilityTheory.klInf_prodBernoulli_condorcet`,
  `ProbabilityTheory.bipolarRate_prodBernoulli_condorcet`: `d = KL_inf = kl(3/5, 1/2)`.

## Implementation notes

The mixture is checked on the four cells of the first two coins, from three identities on the
weights (the two means `7/10` and `3/5`, and the mass `21/50` of two wins of candidate 1), which
follow from `(3/20) t² - (11/100) t + 17/2000 = 0`. The statements and proofs are adapted from
`EValuesResearch/Results/ConvexPiecesTests.lean` (commit `83205cb`) in the paper project
`RemyDegenne/evalues_research`, rewritten on the API of LMLExplore: the mixture is stated as a
membership in the convex hull.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory InformationTheory Set LMLExplore
open scoped ENNReal

namespace ProbabilityTheory

/-- The parameters of the null "candidate 1 is not the Condorcet winner" of [EVR26, Note 32],
closed: the vectors of the box `[1/20, 19/20] ^ 3` whose first or second coordinate, the
probabilities that candidate 1 beats candidates 2 and 3, is at most `1/2`. -/
def condorcetParams : Set (Fin 3 → ℝ) :=
  {θ | (∀ i, θ i ∈ Icc (1 / 20) (19 / 20)) ∧ (θ 0 ≤ 1 / 2 ∨ θ 1 ≤ 1 / 2)}

/-- Membership in the parameters of the Condorcet null. -/
theorem mem_condorcetParams_iff {θ : Fin 3 → ℝ} :
    θ ∈ condorcetParams ↔ (∀ i, θ i ∈ Icc (1 / 20) (19 / 20)) ∧ (θ 0 ≤ 1 / 2 ∨ θ 1 ≤ 1 / 2) :=
  Iff.rfl

/-- A vector `![a, b, c]` of three reals of `[1/20, 19/20]` with `a ≤ 1/2` or `b ≤ 1/2` is a
parameter of the Condorcet null. -/
private lemma vecCons_mem_condorcetParams {a b c : ℝ} (ha : a ∈ Icc (1 / 20) (19 / 20))
    (hb : b ∈ Icc (1 / 20) (19 / 20)) (hc : c ∈ Icc (1 / 20) (19 / 20))
    (h : a ≤ 1 / 2 ∨ b ≤ 1 / 2) : ![a, b, c] ∈ condorcetParams := by
  refine ⟨fun i ↦ ?_, by simpa using h⟩
  fin_cases i
  · simpa using ha
  · simpa using hb
  · simpa using hc

/-- The laws of the Condorcet null charge every point: their parameters are in the open cube. -/
private lemma prodBernoulli_singleton_ne_zero_of_mem_condorcetParams :
    ∀ P ∈ prodBernoulli '' condorcetParams, ∀ x, P {x} ≠ 0 := by
  rintro _ ⟨θ, hθ, rfl⟩ x
  refine prodBernoulli_singleton_ne_zero (fun i _ ↦ ?_) x
  have := hθ.1 i
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- The mass of a point under the coins `![a, b, c]`, for parameters in `[0, 1]`. -/
private lemma prodBernoulli_vecCons_singleton {a b c : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1) (x : Fin 3 → Bool) :
    prodBernoulli ![a, b, c] {x} = ENNReal.ofReal ((if x 0 then a else 1 - a) *
      (if x 1 then b else 1 - b) * (if x 2 then c else 1 - c)) := by
  have hθ : ![a, b, c] ∈ univ.pi fun _ ↦ Icc (0 : ℝ) 1 := by
    intro i _
    fin_cases i
    · simpa using ha
    · simpa using hb
    · simpa using hc
  rw [prodBernoulli_singleton hθ, Fin.prod_univ_three]
  simp

/-- The parameter `t = (11/100 - √(7/1000)) / (3/10)` of the third law of the mixture is a root of
`(3/20) t² - (11/100) t + 17/2000`, and lies in `[1/20, 11/30]`. -/
private lemma condorcet_root :
    let t : ℝ := (11 / 100 - Real.sqrt (7 / 1000)) / (3 / 10)
    3 / 20 * t ^ 2 - 11 / 100 * t + 17 / 2000 = 0 ∧ 1 / 20 ≤ t ∧ t ≤ 11 / 30 := by
  intro t
  have hs : Real.sqrt (7 / 1000) ^ 2 = 7 / 1000 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt (7 / 1000) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (7 / 1000) ≤ 19 / 200 := by nlinarith
  have ht : t = 10 / 3 * (11 / 100 - Real.sqrt (7 / 1000)) := by
    simp only [t]
    ring
  clear_value t
  subst ht
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (5 / 3 : ℝ) * hs
  · linarith
  · linarith

/-- The weights of the mixture: `w₃ = (3/20) / (29/20 - 2 t)`, `w₁ = (1 - w₃) / 2 + 1/9` and
`w₂ = (1 - w₃) / 2 - 1/9` are nonnegative, and give the two means `7/10`, `3/5` and the mass
`21/50` of two wins of candidate 1. -/
private lemma condorcet_weights :
    let t : ℝ := (11 / 100 - Real.sqrt (7 / 1000)) / (3 / 10)
    let w₃ : ℝ := 3 / 20 / (29 / 20 - 2 * t)
    0 ≤ w₃ ∧ 0 ≤ (1 - w₃) / 2 - 1 / 9 ∧
      ((1 - w₃) / 2 + 1 / 9) * (19 / 20) + ((1 - w₃) / 2 - 1 / 9) * (1 / 2) + w₃ * t = 7 / 10 ∧
      ((1 - w₃) / 2 + 1 / 9) * (1 / 2) + ((1 - w₃) / 2 - 1 / 9) * (19 / 20) + w₃ * t = 3 / 5 ∧
      ((1 - w₃) / 2 + 1 / 9) * (19 / 20 * (1 / 2)) + ((1 - w₃) / 2 - 1 / 9) * (1 / 2 * (19 / 20)) +
        w₃ * (t * t) = 7 / 10 * (3 / 5) := by
  intro t w₃
  obtain ⟨ht, ht1, ht2⟩ : 3 / 20 * t ^ 2 - 11 / 100 * t + 17 / 2000 = 0 ∧ 1 / 20 ≤ t ∧
      t ≤ 11 / 30 := condorcet_root
  have hD : 0 < 29 / 20 - 2 * t := by linarith
  have hwD : w₃ * (29 / 20 - 2 * t) = 3 / 20 := div_mul_cancel₀ _ hD.ne'
  have hw0 : 0 ≤ w₃ := div_nonneg (by norm_num) hD.le
  clear_value w₃ t
  have hw1 : w₃ ≤ 1 / 4 := by nlinarith
  have hthis : 3 / 20 * (19 / 40 - t ^ 2) = 11 / 200 * (29 / 20 - 2 * t) := by
    linear_combination (-1 : ℝ) * ht
  have hj : w₃ * (19 / 40 - t ^ 2) = 11 / 200 := by
    linear_combination (20 / 3 * w₃) * hthis + (11 / 30 : ℝ) * hwD
  refine ⟨hw0, by linarith, ?_, ?_, ?_⟩
  · linear_combination (-1 / 2 : ℝ) * hwD
  · linear_combination (-1 / 2 : ℝ) * hwD
  · linear_combination (-1 : ℝ) * hj

/-- **The alternative `(7/10, 3/5, c)` is a mixture of three laws of the Condorcet null**
[EVR26, Note 32, Statement 3]. For `c ∈ [1/20, 19/20]`, the law of the coins `(7/10, 3/5, c)` is
the mixture of the laws of the coins `(19/20, 1/2, c)`, `(1/2, 19/20, c)` and `(t, t, c)`, with
`t = (11/100 - √(7/1000)) / (3/10)`, the smaller root of `(3/20) t² - (11/100) t + 17/2000`, and
the weights `w₁ = (1 - w₃) / 2 + 1/9`, `w₂ = (1 - w₃) / 2 - 1/9` and `w₃ = (3/20) / (29/20 - 2 t)`,
about `0.5523`, `0.3300` and `0.1177`. So it is in the convex hull of the null. -/
theorem prodBernoulli_condorcet_mem_convexHull {c : ℝ} (hc : c ∈ Icc (1 / 20) (19 / 20)) :
    prodBernoulli ![7 / 10, 3 / 5, c] ∈ convexHull ℝ≥0∞ (prodBernoulli '' condorcetParams) := by
  set t : ℝ := (11 / 100 - Real.sqrt (7 / 1000)) / (3 / 10) with ht
  set w₃ : ℝ := 3 / 20 / (29 / 20 - 2 * t)
  obtain ⟨-, ht1, ht2⟩ : 3 / 20 * t ^ 2 - 11 / 100 * t + 17 / 2000 = 0 ∧ 1 / 20 ≤ t ∧
      t ≤ 11 / 30 := condorcet_root
  obtain ⟨hw0, hw2, hm1, hm2, hj⟩ : 0 ≤ w₃ ∧ 0 ≤ (1 - w₃) / 2 - 1 / 9 ∧
      ((1 - w₃) / 2 + 1 / 9) * (19 / 20) + ((1 - w₃) / 2 - 1 / 9) * (1 / 2) + w₃ * t = 7 / 10 ∧
      ((1 - w₃) / 2 + 1 / 9) * (1 / 2) + ((1 - w₃) / 2 - 1 / 9) * (19 / 20) + w₃ * t = 3 / 5 ∧
      ((1 - w₃) / 2 + 1 / 9) * (19 / 20 * (1 / 2)) +
        ((1 - w₃) / 2 - 1 / 9) * (1 / 2 * (19 / 20)) + w₃ * (t * t) = 7 / 10 * (3 / 5) :=
    condorcet_weights
  clear_value w₃ t
  have hw1 : 0 ≤ (1 - w₃) / 2 + 1 / 9 := by linarith
  have hbox (a : ℝ) (h1 : 1 / 20 ≤ a) (h2 : a ≤ 19 / 20) : a ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  have hc01 := hbox c hc.1 hc.2
  -- the identity of the measures, on the singletons
  have hmix : prodBernoulli ![7 / 10, 3 / 5, c] =
      ENNReal.ofReal ((1 - w₃) / 2 + 1 / 9) • prodBernoulli ![19 / 20, 1 / 2, c] +
        ENNReal.ofReal ((1 - w₃) / 2 - 1 / 9) • prodBernoulli ![1 / 2, 19 / 20, c] +
          ENNReal.ofReal w₃ • prodBernoulli ![t, t, c] := by
    refine Measure.ext_of_singleton fun x ↦ ?_
    simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [prodBernoulli_vecCons_singleton (hbox _ (by norm_num) (by norm_num))
        (hbox _ (by norm_num) (by norm_num)) hc01,
      prodBernoulli_vecCons_singleton (hbox _ (by norm_num) (by norm_num))
        (hbox _ (by norm_num) (by norm_num)) hc01,
      prodBernoulli_vecCons_singleton (hbox _ (by norm_num) (by norm_num))
        (hbox _ (by norm_num) (by norm_num)) hc01,
      prodBernoulli_vecCons_singleton (hbox _ ht1 (by linarith)) (hbox _ ht1 (by linarith)) hc01]
    set g : ℝ := if x 2 then c else 1 - c
    have hg : 0 ≤ g := by
      simp only [g]
      split_ifs <;> linarith [hc01.1, hc01.2]
    have hcell (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
        0 ≤ (if x 0 then a else 1 - a) * (if x 1 then b else 1 - b) * g := by
      refine mul_nonneg (mul_nonneg ?_ ?_) hg <;> split_ifs <;> linarith [ha.1, ha.2, hb.1, hb.2]
    have h1 := mul_nonneg hw1 (hcell _ _ (hbox (19 / 20) (by norm_num) (by norm_num))
      (hbox (1 / 2) (by norm_num) (by norm_num)))
    have h2 := mul_nonneg hw2 (hcell _ _ (hbox (1 / 2) (by norm_num) (by norm_num))
      (hbox (19 / 20) (by norm_num) (by norm_num)))
    have h3 := mul_nonneg hw0 (hcell _ _ (hbox _ ht1 (by linarith)) (hbox _ ht1 (by linarith)))
    rw [← ENNReal.ofReal_mul hw1, ← ENNReal.ofReal_mul hw2, ← ENNReal.ofReal_mul hw0,
      ← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (add_nonneg h1 h2) h3]
    congr 1
    rcases Bool.eq_false_or_eq_true (x 0) with h0 | h0 <;>
      rcases Bool.eq_false_or_eq_true (x 1) with h1 | h1 <;>
      simp only [h0, h1, Bool.false_eq_true, ↓reduceIte]
    · linear_combination (-g) * hj
    · linear_combination (-g) * hm1 + g * hj
    · linear_combination (-g) * hm2 + g * hj
    · linear_combination g * hm1 + g * hm2 - g * hj
  rw [hmix]
  exact add_add_smul_mem_convexHull
    (mem_image_of_mem _ (vecCons_mem_condorcetParams ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ hc (Or.inr le_rfl)))
    (mem_image_of_mem _ (vecCons_mem_condorcetParams ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ hc (Or.inl le_rfl)))
    (mem_image_of_mem _ (vecCons_mem_condorcetParams ⟨ht1, by linarith⟩ ⟨ht1, by linarith⟩ hc
      (Or.inl (by linarith))))
    hw1 hw2 hw0 (by ring)

/-- **One observation carries no evidence against the Condorcet null**
[EVR26, Note 32, Statement 3]. For `c ∈ [1/20, 19/20]`, the law of the coins `(7/10, 3/5, c)` is
a mixture of laws of the null (`prodBernoulli_condorcet_mem_convexHull`), so no e-variable of one
observation has a positive expected logarithm under it: `a₁ = 0`. -/
theorem maxEPower_prodBernoulli_condorcet_eq_zero {c : ℝ} (hc : c ∈ Icc (1 / 20) (19 / 20)) :
    maxEPower (prodBernoulli ![7 / 10, 3 / 5, c]) (prodBernoulli '' condorcetParams) = 0 :=
  maxEPower_eq_zero_of_mem_effectiveSet (by rintro _ ⟨θ, -, rfl⟩; simp)
    (convexHull_subset_effectiveSet (prodBernoulli_condorcet_mem_convexHull hc))

/-- **The tests of the test supermartingales for the Condorcet null have no power**
[EVR26, Note 32, Statement 3]. For `c ∈ [1/20, 19/20]` and a test supermartingale `M` for the
i.i.d. null of the Condorcet null, in the filtration `Filtration.piLT` of the past observations,
the test that rejects the first time `M` reaches `α⁻¹` rejects with probability at most `α` under
the i.i.d. law of the coins `(7/10, 3/5, c)`, which is in the i.i.d. null of the convex hull of
the null. -/
theorem measure_hittingAfter_lt_top_le_condorcet {c : ℝ} (hc : c ∈ Icc (1 / 20) (19 / 20))
    {M : ℕ → (ℕ → Fin 3 → Bool) → ℝ≥0∞}
    (hM : IsTestSupermartingale M Filtration.piLT (iidNull (prodBernoulli '' condorcetParams)))
    (α : ℝ≥0∞) :
    Measure.infinitePi (fun _ : ℕ ↦ prodBernoulli ![7 / 10, 3 / 5, c])
      {ω | hittingAfter M (Ici α⁻¹) 0 ω < ⊤} ≤ α := by
  have hS : ∀ P ∈ prodBernoulli '' condorcetParams, IsProbabilityMeasure P := by
    rintro _ ⟨θ, -, rfl⟩
    infer_instance
  have hM' := (isTestSupermartingale_iidNull_convexHull hS
    prodBernoulli_singleton_ne_zero_of_mem_condorcetParams hM).anti_set
      (singleton_subset_iff.2 (infinitePi_mem_iidNull (prodBernoulli_condorcet_mem_convexHull hc)))
  exact ((hM'.isEProcess (by rintro _ rfl; infer_instance)).isLevelStoppingTime_hittingAfter
    α).measure_lt_top_le _ rfl

/-- **The smallest relative entropy to the Condorcet null** [EVR26, Note 32, Statement 3]. For
`c ∈ [1/20, 19/20]`, the smallest relative entropy from the coins `(7/10, 3/5, c)` to the Condorcet
null is `kl(3/5, 1/2) = (3/5) log (6/5) + (2/5) log (4/5)`, about `0.0201`, the smaller of
`kl(7/10, 1/2)` and `kl(3/5, 1/2)`, attained at the coins `(7/10, 1/2, c)`. -/
theorem klInf_prodBernoulli_condorcet {c : ℝ} (hc : c ∈ Icc (1 / 20) (19 / 20)) :
    klInf (prodBernoulli ![7 / 10, 3 / 5, c]) (prodBernoulli '' condorcetParams) =
      (klBer (3 / 5) (1 / 2) : EReal) := by
  rw [klInf_eq_coe_iInf_klDiv (by rintro _ ⟨θ, -, rfl⟩; simp), iInf_image]
  congr 1
  refine le_antisymm ?_ (le_iInf₂ fun θ hθ ↦ ?_)
  · refine (iInf₂_le _ (vecCons_mem_condorcetParams (a := 7 / 10) (b := 1 / 2)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ hc (Or.inr le_rfl))).trans_eq ?_
    rw [klDiv_prodBernoulli, Fin.sum_univ_three]
    simp [klBer_self]
  · rw [klDiv_prodBernoulli, Fin.sum_univ_three]
    have hb (i : Fin 3) : θ i ∈ Icc (1 / 20 : ℝ) (19 / 20) := hθ.1 i
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rcases hθ.2 with h0 | h1
    · calc klBer (3 / 5) (1 / 2) ≤ klBer (7 / 10) (1 / 2) :=
          klBer_le_klBer le_rfl (by norm_num) (by norm_num)
        _ ≤ klBer (7 / 10) (θ 0) :=
          (strictAntiOn_klBer (by norm_num)).antitoneOn
            ⟨by linarith [(hb 0).1], by linarith⟩ ⟨by norm_num, by norm_num⟩ h0
        _ ≤ _ := le_add_right (le_add_right le_rfl)
    · calc klBer (3 / 5) (1 / 2) ≤ klBer (3 / 5) (θ 1) :=
          (strictAntiOn_klBer (by norm_num)).antitoneOn
            ⟨by linarith [(hb 1).1], by linarith⟩ ⟨by norm_num, by norm_num⟩ h1
        _ ≤ _ := le_add_right (le_add_left le_rfl)

/-- **The bipolar rate against the Condorcet null is the smallest relative entropy**
[EVR26, Note 32, Statement 3]. For `c ∈ [1/20, 19/20]`, the bipolar rate of the coins
`(7/10, 3/5, c)` against the Condorcet null is `KL_inf = kl(3/5, 1/2)`, although one observation
carries no evidence (`maxEPower_prodBernoulli_condorcet_eq_zero`). -/
theorem bipolarRate_prodBernoulli_condorcet {c : ℝ} (hc : c ∈ Icc (1 / 20) (19 / 20)) :
    bipolarRate (prodBernoulli ![7 / 10, 3 / 5, c]) (prodBernoulli '' condorcetParams) =
      (klBer (3 / 5) (1 / 2) : EReal) := by
  rw [bipolarRate_eq_klInf_of_finite _ _ (by rintro _ ⟨θ, -, rfl⟩; infer_instance),
    klInf_prodBernoulli_condorcet hc]

end ProbabilityTheory
