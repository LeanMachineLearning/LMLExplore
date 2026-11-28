/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Design.Growth
import LMLExplore.Basic.ENNReal.BigOperators
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
relative entropy (`ProbabilityTheory.klDiv_designLaw`) its bipolar rate is
`⨅ ν ∈ Λ, ∑ a, r a * klDiv (μ a) (ν a)`. Whenever the bipolar rates of the tables of the designs
`r ≠ 0` are `⨅ s ∈ S, ∑ a, r a * k s a` for a family of costs `k s : α → ℝ≥0∞`, the rate of the
designs is `⨆ w ∈ Δ, ⨅ s ∈ S, ∑ a, w a * k s a` [EVR26, Note 41, Section 5]
(`ProbabilityTheory.designRate_eq_iSup_iInf_of_bipolarRate_designLaw_eq`).

## Main statements

* `ProbabilityTheory.bipolarRate_designLaw_eq_iInf_sum_mul_klDiv_of_finite`: on a finite
  alphabet, the bipolar rate of the tables of a design `r` is
  `⨅ ν ∈ Λ, ∑ a, r a * klDiv (μ a) (ν a)`.
* `ProbabilityTheory.designRate_eq_iSup_iInf_sum_mul_klDiv_of_finite`: on a finite alphabet, the
  rate of the designs is the entropy constant.
* `ProbabilityTheory.designGrowth_eq_iInf_sum_mul_klDiv_of_finite`: on a finite alphabet, the
  growth of the designs proportional to `x` is the entropy bound.

## Implementation notes

The lower bound on the growth takes the designs `⌈q x⌉` on the support of `x`. Since the bound
`⨅ ν ∈ Λ, ∑ a, x a * klDiv (μ a) (ν a)` is monotone and positively homogeneous in `x`
(`ENNReal.mul_iInf_sum_mul_le_iInf_sum_mul`), no concavity or continuity of the bound in `x` is
used. The statements and proofs are adapted from
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
    have h3 : (q : ℝ≥0∞) * g ≤ ⨅ ν ∈ Λ, ∑ a, (r a : ℝ≥0∞) * klDiv (μ a) (ν a) :=
      ENNReal.mul_iInf_sum_mul_le_iInf_sum_mul hr_ge
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
