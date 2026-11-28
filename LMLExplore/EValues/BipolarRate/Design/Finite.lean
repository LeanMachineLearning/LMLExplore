/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Design.Growth
import LMLExplore.Data.EReal.Inv
import LMLExplore.EValues.BipolarRate.Finite
import TauCeti.Data.EReal.Operations

/-!
# The rate and the growth of the designs on a finite alphabet

Finitely many sources `a : α` produce observations in a common measurable space `𝓧`, an instance
is a family `μ : α → Measure 𝓧` of probability measures, and `Λ` is a set of such instances. The
rate `D* = designRate μ Λ` of the designs is the best expected logarithm per observation of an
e-variable of the table of a design (`ProbabilityTheory.designRate`). It is at most the entropy
constant

  `v(μ, Λ) = ⨆ w ∈ Δ, ⨅ ν ∈ Λ, ∑ a, w a * klDiv (μ a) (ν a)`

over the probability vectors `w` (`ProbabilityTheory.designRate_le_iSup_iInf_sum_mul_klDiv`),
which is the inverse `1 / T*` of the characteristic time of [GK16] when `Λ` is the set of the
alternatives to the single correct answer of a model of an identification task
(`LMLExplore.Identification.IdentTask.designRate_eq_inv_charTime_of_finite`). On a finite
alphabet the two constants are equal [EVR26, Note 41, Proposition 5], and the growth
`designGrowth μ Λ x` of the designs proportional to `x : α → ℝ≥0` is the entropy bound
`⨅ ν ∈ Λ, ∑ a, x a * klDiv (μ a) (ν a)` [EVR26, Note 41, Section 6].

Both equalities come from the bipolar rates of the tables of the designs. The table of a design
`r` lives on a finite alphabet, where the bipolar rate is the smallest relative entropy to the
null (`ProbabilityTheory.bipolarRate_eq_klInf_of_finite`), so by the tensorization of the
relative entropy its bipolar rate is `⨅ ν ∈ Λ, ∑ a, r a * klDiv (μ a) (ν a)`. More generally,
whenever the bipolar rates of the tables of the designs `r ≠ 0` are `⨅ s ∈ S, ∑ a, r a * k s a`
for a family of costs `k s : α → ℝ≥0∞`, the rate of the designs is
`⨆ w ∈ Δ, ⨅ s ∈ S, ∑ a, w a * k s a` [EVR26, Note 41, Section 5].

## Main statements

* `ProbabilityTheory.klDiv_designLaw`: the relative entropy between the tables of a design is
  `∑ a, n a * klDiv (μ a) (ν a)`.
* `ProbabilityTheory.bipolarRate_designLaw_eq_iInf_sum_mul_klDiv_of_finite`: on a finite
  alphabet, the bipolar rate of the tables of a design `r` is
  `⨅ ν ∈ Λ, ∑ a, r a * klDiv (μ a) (ν a)`.
* `ProbabilityTheory.designRate_eq_iSup_iInf_of_bipolarRate_designLaw_eq`: the rate of the
  designs when the bipolar rates of the tables are given by a family of costs.
* `ProbabilityTheory.designRate_eq_iSup_iInf_sum_mul_klDiv_of_finite`: on a finite alphabet, the
  rate of the designs is the entropy constant.
* `ProbabilityTheory.designGrowth_eq_iInf_sum_mul_klDiv_of_finite`: on a finite alphabet, the
  growth of the designs proportional to `x` is the entropy bound.

## Implementation notes

The lower bounds take the designs `⌈m w⌉` for the rate, and `⌈q x⌉` on the support of `x` for the
growth. Since the bound `⨅ s ∈ S, ∑ a, w a * k s a` is monotone and positively homogeneous in
`w`, and `⌈m w⌉` has at most `m + Fintype.card α` observations, no concavity or continuity of the
bound in `w` is used. The statements and proofs are adapted from
`EValuesResearch/Results/DesignConstants.lean` (commit `cb8238f`) in the paper project
`RemyDegenne/evalues_research`, rewritten on the API of LMLExplore.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 55 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 41, *The lower bound at the bipolar rate, with several arms*.
-/

public section

open MeasureTheory InformationTheory Filter
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {α 𝓧 : Type*} [Fintype α] {m𝓧 : MeasurableSpace 𝓧} {Λ : Set (α → Measure 𝓧)}

/-- The relative entropy between the tables of a design under two instances of probability
measures is `∑ a, n a * klDiv (μ a) (ν a)`, by the tensorization of the relative entropy. -/
theorem klDiv_designLaw (μ ν : α → Measure 𝓧) [∀ a, IsProbabilityMeasure (μ a)]
    [∀ a, IsProbabilityMeasure (ν a)] (n : α → ℕ) :
    klDiv (designLaw μ n) (designLaw ν n) = ∑ a, (n a : ℝ≥0∞) * klDiv (μ a) (ν a) := by
  rw [designLaw_def, designLaw_def, klDiv_pi, Fintype.sum_sigma]
  simp

/-- **The bipolar rate of the tables of a design on a finite alphabet.** On a finite type, with
any σ-algebra, the bipolar rate of the tables of the design `r` against the tables of the
instances of `Λ` is `⨅ ν ∈ Λ, ∑ a, r a * klDiv (μ a) (ν a)`, with `0 * ∞ = 0`
[EVR26, Note 41, Proposition 5]. -/
theorem bipolarRate_designLaw_eq_iInf_sum_mul_klDiv_of_finite [Finite 𝓧] (μ : α → Measure 𝓧)
    [∀ a, IsProbabilityMeasure (μ a)] (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a))
    (r : α → ℕ) :
    bipolarRate (designLaw μ r) ((fun ν ↦ designLaw ν r) '' Λ) =
      ((⨅ ν ∈ Λ, ∑ a, (r a : ℝ≥0∞) * klDiv (μ a) (ν a) : ℝ≥0∞) : EReal) := by
  have hS : ∀ P ∈ (fun ν ↦ designLaw ν r) '' Λ, IsProbabilityMeasure P := by
    rintro _ ⟨ν, hν, rfl⟩
    have := hΛ ν hν
    infer_instance
  rw [bipolarRate_eq_klInf_of_finite _ _ hS,
    klInf_eq_coe_iInf_klDiv fun P hP ↦ by have := hS P hP; simp, iInf_image]
  congr 1
  refine iInf_congr fun ν ↦ iInf_congr fun hν ↦ ?_
  have := hΛ ν hν
  exact klDiv_designLaw μ ν r

/-- **The rate of the designs from the bipolar rates of the tables.** If the bipolar rate of the
tables of every design `r ≠ 0` is `⨅ s ∈ S, ∑ a, r a * k s a` for a family of costs
`k s : α → ℝ≥0∞`, then the rate of the designs is `⨆ w ∈ Δ, ⨅ s ∈ S, ∑ a, w a * k s a` over the
probability vectors `w`, with `0 * ∞ = 0` [EVR26, Note 41, Section 5]. -/
theorem designRate_eq_iSup_iInf_of_bipolarRate_designLaw_eq {ι : Type*} (μ : α → Measure 𝓧)
    [∀ a, IsProbabilityMeasure (μ a)] (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a))
    {S : Set ι} {k : ι → α → ℝ≥0∞}
    (h : ∀ r : α → ℕ, r ≠ 0 → bipolarRate (designLaw μ r) ((fun ν ↦ designLaw ν r) '' Λ) =
      ((⨅ s ∈ S, ∑ a, (r a : ℝ≥0∞) * k s a : ℝ≥0∞) : EReal)) :
    designRate μ Λ = ((⨆ w ∈ LMLExplore.simplex α, ⨅ s ∈ S,
      ∑ a, ENNReal.ofReal (w a) * k s a : ℝ≥0∞) : EReal) := by
  set V := ⨆ w ∈ LMLExplore.simplex α, ⨅ s ∈ S, ∑ a, ENNReal.ofReal (w a) * k s a
  refine le_antisymm ?_ ?_
  · -- the bound of the design `r` is `|r|` times the bound of its proportions `r / |r|`
    rw [designRate_eq_iSup_bipolarRate μ hΛ]
    refine iSup_le fun r ↦ ?_
    rcases eq_or_ne r 0 with rfl | hr
    · simpa using EReal.coe_ennreal_nonneg V
    have hN := Fintype.sum_pos (pos_iff_ne_zero.2 hr)
    set N := ∑ a, r a
    have hN0 : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    set w : α → ℝ := fun a ↦ r a / N
    have hw : w ∈ LMLExplore.simplex α := by
      refine LMLExplore.mem_simplex_iff.2 ⟨fun a ↦ by positivity, ?_⟩
      rw [← Finset.sum_div, ← Nat.cast_sum, div_self (by exact_mod_cast hN.ne')]
    have hr_eq (a : α) : (r a : ℝ≥0∞) = N * ENNReal.ofReal (w a) := by
      rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hN), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast, ENNReal.mul_div_cancel hN0 (ENNReal.natCast_ne_top N)]
    rw [h r hr, EReal.div_natCast_le_iff hN, ← ENNReal.toEReal_natCast, ← EReal.coe_ennreal_mul,
      EReal.coe_ennreal_le_coe_ennreal_iff]
    calc ⨅ s ∈ S, ∑ a, (r a : ℝ≥0∞) * k s a
    _ = N * ⨅ s ∈ S, ∑ a, ENNReal.ofReal (w a) * k s a := by
      simp_rw [ENNReal.mul_iInf_of_ne hN0 (ENNReal.natCast_ne_top N), Finset.mul_sum,
        ← mul_assoc, hr_eq]
    _ ≤ N * V := by
      gcongr
      exact le_iSup₂ (f := fun w _ ↦ ⨅ s ∈ S, ∑ a, ENNReal.ofReal (w a) * k s a) w hw
  rw [← EReal.coe_toENNReal (designRate_nonneg μ Λ), EReal.coe_ennreal_le_coe_ennreal_iff]
  refine iSup₂_le fun w hw ↦ ?_
  obtain ⟨hw0, hw1⟩ := LMLExplore.mem_simplex_iff.1 hw
  set g := ⨅ s ∈ S, ∑ a, ENNReal.ofReal (w a) * k s a
  set D := (designRate μ Λ).toENNReal
  set K := Fintype.card α
  -- for every `m ≥ 1`, the design `⌈m w⌉` gives `m g ≤ (m + K) D`
  have key (m : ℕ) (hm : 0 < m) : (m : ℝ≥0∞) * g ≤ (m + K) * D := by
    set r : α → ℕ := fun a ↦ ⌈(m : ℝ) * w a⌉₊
    have hr_ge (a : α) : (m : ℝ) * w a ≤ r a := Nat.le_ceil _
    have hr_le (a : α) : (r a : ℝ) ≤ m * w a + 1 :=
      (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg _) (hw0 a))).le
    have hsum_ge : (m : ℝ) ≤ ∑ a, (r a : ℝ) := by
      calc (m : ℝ) = ∑ a, (m : ℝ) * w a := by rw [← Finset.mul_sum, hw1, mul_one]
      _ ≤ ∑ a, (r a : ℝ) := Finset.sum_le_sum fun a _ ↦ hr_ge a
    have hsum_le : ∑ a, r a ≤ m + K := by
      have h : (∑ a, (r a : ℝ)) ≤ m + K := by
        calc ∑ a, (r a : ℝ) ≤ ∑ a, ((m : ℝ) * w a + 1) := Finset.sum_le_sum fun a _ ↦ hr_le a
        _ = m + K := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hw1, mul_one, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul, mul_one]
      exact_mod_cast h
    have hr0 : r ≠ 0 := by
      rintro hr
      have : (m : ℝ) ≤ 0 := by simpa [hr] using hsum_ge
      exact (Nat.cast_pos.2 hm).not_ge this
    -- `m g` is at most the bound of `r`, which is the bipolar rate of its tables
    have h1 : (m : ℝ≥0∞) * g ≤ ⨅ s ∈ S, ∑ a, (r a : ℝ≥0∞) * k s a := by
      refine le_iInf₂ fun s hs ↦ (mul_le_mul_right (iInf₂_le s hs) _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ ↦ ?_
      rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ← ENNReal.ofReal_natCast]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hr_ge a)) _
    have h2 := bipolarRate_designLaw_le μ hΛ hr0
    rw [h r hr0, ← EReal.coe_toENNReal (designRate_nonneg μ Λ),
      ← ENNReal.toEReal_natCast, ← EReal.coe_ennreal_mul,
      EReal.coe_ennreal_le_coe_ennreal_iff] at h2
    refine h1.trans (h2.trans (mul_le_mul_left ?_ _))
    exact_mod_cast hsum_le
  -- letting `m → ∞`, `g ≤ D`
  rcases eq_or_ne D ⊤ with hD | hD
  · rw [hD]
    exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top K) hD) (ENNReal.coe_ne_zero.2 hε.ne'))
  have hm' : (K : ℝ≥0∞) * D ≤ (m + 1 : ℕ) * ε := by
    rw [ENNReal.div_lt_iff (Or.inl (ENNReal.coe_ne_zero.2 hε.ne')) (Or.inl ENNReal.coe_ne_top)]
      at hm
    exact hm.le.trans (mul_le_mul_left (by exact_mod_cast Nat.le_succ m) _)
  have hm0 : ((m + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  refine (ENNReal.mul_le_mul_iff_right hm0 (ENNReal.natCast_ne_top _)).1 ?_
  calc ((m + 1 : ℕ) : ℝ≥0∞) * g ≤ ((m + 1 : ℕ) + K) * D := key (m + 1) m.succ_pos
  _ = (m + 1 : ℕ) * D + K * D := add_mul _ _ _
  _ ≤ (m + 1 : ℕ) * D + (m + 1 : ℕ) * ε := by gcongr
  _ = (m + 1 : ℕ) * (D + ε) := (mul_add _ _ _).symm

/-- **The rate of the designs on a finite alphabet is the entropy constant.** On a finite type,
with any σ-algebra, the rate of the designs of an instance `μ` against any set `Λ` of instances is
`⨆ w ∈ Δ, ⨅ ν ∈ Λ, ∑ a, w a * klDiv (μ a) (ν a)` over the probability vectors `w`, with
`0 * ∞ = 0` [EVR26, Note 41, Proposition 5]. With `Λ` the alternatives to the single correct
answer of a model of an identification task, this is `D* = 1 / T*` [GK16]
(`LMLExplore.Identification.IdentTask.designRate_eq_inv_charTime_of_finite`). -/
theorem designRate_eq_iSup_iInf_sum_mul_klDiv_of_finite [Finite 𝓧] (μ : α → Measure 𝓧)
    [∀ a, IsProbabilityMeasure (μ a)] (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) :
    designRate μ Λ = ((⨆ w ∈ LMLExplore.simplex α, ⨅ ν ∈ Λ,
      ∑ a, ENNReal.ofReal (w a) * klDiv (μ a) (ν a) : ℝ≥0∞) : EReal) :=
  designRate_eq_iSup_iInf_of_bipolarRate_designLaw_eq μ hΛ fun r _ ↦
    bipolarRate_designLaw_eq_iInf_sum_mul_klDiv_of_finite μ hΛ r

/-- **The growth of the designs on a finite alphabet is the entropy bound.** On a finite type,
with any σ-algebra, the growth of the designs proportional to `x : α → ℝ≥0` is
`designGrowth μ Λ x = ⨅ ν ∈ Λ, ∑ a, x a * klDiv (μ a) (ν a)`, with `0 * ∞ = 0`
[EVR26, Note 41, Section 6]. -/
theorem designGrowth_eq_iInf_sum_mul_klDiv_of_finite [Finite 𝓧] (μ : α → Measure 𝓧)
    [∀ a, IsProbabilityMeasure (μ a)] (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a))
    (x : α → ℝ≥0) :
    designGrowth μ Λ x = ((⨅ ν ∈ Λ, ∑ a, (x a : ℝ≥0∞) * klDiv (μ a) (ν a) : ℝ≥0∞) : EReal) := by
  refine le_antisymm (designGrowth_le_iInf_sum_mul_klDiv hΛ x) ?_
  have hΛ1 : ∀ ν ∈ Λ, ∀ a, ν a Set.univ ≤ 1 := fun ν hν a ↦ by
    have := hΛ ν hν a
    exact prob_le_one
  set g := ⨅ ν ∈ Λ, ∑ a, (x a : ℝ≥0∞) * klDiv (μ a) (ν a)
  refine EReal.ge_of_forall_gt_iff_ge.1 fun ℓ hℓ ↦ ?_
  -- a nonpositive `ℓ` is below the growth, which is nonnegative
  rcases le_or_gt ℓ 0 with hℓ0 | hℓ0
  · exact (EReal.coe_le_coe_iff.2 hℓ0).trans (designGrowth_nonneg μ hΛ1 x)
  refine le_designGrowth_of_forall_sub_le fun ε hε ↦ ?_
  -- a denominator `q` with `1 / q < ε`, and the design `r = ⌈q x⌉` on the support of `x`
  obtain ⟨q, hq⟩ := exists_nat_gt (ε⁻¹ : ℝ≥0)
  have hq0 : 0 < q := by exact_mod_cast (inv_pos.2 hε).trans hq
  have hqε : 1 ≤ (q : ℝ≥0) * ε := by
    rw [← inv_le_iff_one_le_mul₀ hε]
    exact hq.le
  set r : α → ℕ := fun a ↦ if x a = 0 then 0 else ⌈(q : ℝ≥0) * x a⌉₊
  have hr_ge (a : α) : (q : ℝ≥0∞) * x a ≤ r a := by
    by_cases hx : x a = 0
    · simp [r, hx]
    · simp only [r, hx, ↓reduceIte]
      exact_mod_cast Nat.le_ceil _
  -- the bipolar rate of the tables of `r` exceeds `q ℓ`
  have hbr : ((q * ℓ : ℝ) : EReal) <
      bipolarRate (designLaw μ r) ((fun ν ↦ designLaw ν r) '' Λ) := by
    rw [bipolarRate_designLaw_eq_iInf_sum_mul_klDiv_of_finite μ hΛ r]
    have h1 : ENNReal.ofReal ℓ < g := by
      rwa [← EReal.coe_ennreal_lt_coe_ennreal_iff, EReal.coe_ennreal_ofReal, max_eq_left hℓ0.le]
    have h2 : (q : ℝ≥0∞) * ENNReal.ofReal ℓ < (q : ℝ≥0∞) * g := by
      rw [mul_comm, mul_comm (q : ℝ≥0∞)]
      exact ENNReal.mul_lt_mul_left (by exact_mod_cast hq0.ne') (ENNReal.natCast_ne_top q) h1
    -- the bound is monotone and positively homogeneous in the proportions
    have h3 : (q : ℝ≥0∞) * g ≤ ⨅ ν ∈ Λ, ∑ a, (r a : ℝ≥0∞) * klDiv (μ a) (ν a) := by
      refine le_iInf₂ fun ν hν ↦ (mul_le_mul_right (iInf₂_le ν hν) _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ ↦ ?_
      rw [← mul_assoc]
      exact mul_le_mul_left (hr_ge a) _
    have h4 := h2.trans_le h3
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h4
    calc ((q * ℓ : ℝ) : EReal) = ((ENNReal.ofReal (q * ℓ) : ℝ≥0∞) : EReal) := by
          rw [EReal.coe_ennreal_ofReal, max_eq_left (by positivity)]
    _ < _ := EReal.coe_ennreal_lt_coe_ennreal_iff.2 h4
  -- eventually `a_k ≥ k q ℓ` for the `k`-sample values `a_k` of the tables of `r`
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ((tendsto_maxLogGrowth_div_bipolarRate (designLaw μ r)
    (by
      rintro _ ⟨ν, hν, rfl⟩
      have := hΛ ν hν
      exact prob_le_one)).eventually (eventually_gt_nhds hbr))
  refine ⟨q * (k₀ + 1) * ℓ, fun m hm ↦ ?_⟩
  rcases lt_or_ge m (q * (k₀ + 1)) with hmk | hmk
  · -- few observations: the value is nonnegative
    refine le_trans ?_ (designValue_nonneg μ hΛ1 _)
    have : (m : ℝ) ≤ q * (k₀ + 1) := by exact_mod_cast hmk.le
    exact EReal.coe_nonpos.2 (by nlinarith)
  -- many observations: the design `⌈m (x + ε 𝟙_{supp x})⌉` contains `k = ⌊m / q⌋` tables of `r`
  set k := m / q with hk_def
  have hk : k₀ + 1 ≤ k := (Nat.le_div_iff_mul_le hq0).2 (by rw [mul_comm]; exact hmk)
  have hk0 : 0 < k := by omega
  have hkq : (k : ℝ≥0) * q ≤ m := by exact_mod_cast Nat.div_mul_le_self m q
  have hdesign : k • r ≤ proportionalDesign x ε m := by
    intro a
    by_cases hx : x a = 0
    · simp [r, hx, proportionalDesign_of_eq_zero hx]
    rw [proportionalDesign_of_ne_zero hx]
    simp only [Pi.smul_apply, smul_eq_mul, r, hx, ↓reduceIte]
    refine Nat.cast_le.1 (le_trans ?_ (Nat.le_ceil ((m : ℝ≥0) * (x a + ε))))
    -- `k ⌈q x a⌉ ≤ k (q x a + 1) ≤ m x a + m ε`
    have hceil : (⌈(q : ℝ≥0) * x a⌉₊ : ℝ≥0) ≤ q * x a + 1 :=
      (Nat.ceil_lt_add_one zero_le).le
    have hkε : (k : ℝ≥0) ≤ m * ε := by
      calc (k : ℝ≥0) ≤ k * (q * ε) := le_mul_of_one_le_right zero_le hqε
      _ = k * q * ε := (mul_assoc _ _ _).symm
      _ ≤ m * ε := by gcongr
    push_cast
    calc (k : ℝ≥0) * ⌈(q : ℝ≥0) * x a⌉₊ ≤ k * (q * x a + 1) := by gcongr
    _ = k * q * x a + k := by ring
    _ ≤ m * x a + m * ε := by gcongr
    _ = m * (x a + ε) := (mul_add _ _ _).symm
  calc ((m * ℓ - q * (k₀ + 1) * ℓ : ℝ) : EReal) ≤ ((k * (q * ℓ) : ℝ) : EReal) := by
        rw [EReal.coe_le_coe_iff]
        have h1 : (m : ℝ) ≤ k * q + q := by exact_mod_cast (Nat.lt_div_mul_add hq0).le
        have h2 : (q : ℝ) ≤ q * (k₀ + 1) := le_mul_of_one_le_right (Nat.cast_nonneg _)
          (by linarith [(Nat.cast_nonneg k₀ : (0 : ℝ) ≤ k₀)])
        nlinarith
  _ ≤ maxLogGrowth (designLaw μ r) ((fun ν ↦ designLaw ν r) '' Λ) k :=
        ((EReal.coe_lt_div_natCast_iff hk0).1 (hk₀ k (by omega))).le
  _ = designValue μ Λ (k • r) := maxLogGrowth_designLaw μ hΛ r k
  _ ≤ designValue μ Λ (proportionalDesign x ε m) := designValue_mono hΛ hdesign

end ProbabilityTheory
