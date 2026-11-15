/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Numeraire.Conditional
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Probability.UniformOn
import TauCeti.Probability.Distributions.Geometric.Measurability
import TauCeti.Probability.Distributions.Uniform.Basic

/-!
# The numeraire of two geometric observations against a common success probability

Two independent observations `X₁, X₂` in `ℕ` have the geometric laws `Geom(p₁)` and `Geom(p₂)`
of Mathlib's `ProbabilityTheory.geometricMeasure`, and the null hypothesis is that they have a
common, unknown success probability: it is the set of the products `Geom(p) ⊗ Geom(p)`. Under
every member of the null the mass of a pair `(j, k)` depends only on `j + k`, so, given the sum
`s`, the first observation is uniform on `{0, …, s}`: the conditional law given the sum is
`ProbabilityTheory.Kernel.antidiagonalUniform s` for every member.

For the alternative `Q = Geom(p₁) ⊗ Geom(p₂)`, the likelihood ratio of `Q` to the law
`Kernel.antidiagonalUniform ∘ₘ Q.map (x.1 + x.2)`, under which the sum has its law under `Q` and,
given the sum `s`, the first observation is uniform on `{0, …, s}`, is the numeraire of the null
under `Q` (`ProbabilityTheory.isNumeraire_rnDeriv_antidiagonalUniform_comp`). As for two
exponential observations (`ProbabilityTheory.isNumeraire_rnDeriv_segmentUniform_comp`), that law
is the mixture of the members `Geom(1 / m) ⊗ Geom(1 / m)` of the null over `m` uniform between
`1 / p₁` and `1 / p₂`, that is, over the mean `m - 1` uniform between the two means, so that it
belongs to the effective null.

## Main definitions

* `ProbabilityTheory.Kernel.antidiagonalUniform`: the uniform law on the pairs `(j, k)` of natural
  numbers with `j + k = s`.

## Main statements

* `ProbabilityTheory.isNumeraire_rnDeriv_antidiagonalUniform_comp`: the numeraire of two geometric
  observations against a common success probability.

## Implementation notes

Mathlib's `geometricMeasure 0` is the point mass at `0`, as is `geometricMeasure 1`, so the
statement holds for every pair of success probabilities except those for which `Q` is the point
mass at `(0, 0)`. The mixture is computed on the masses of the points, through the antiderivative
`(1 - 1 / m) ^ (s + 1) / (s + 1)` of `(1 - 1 / m) ^ s / m ^ 2`.

## References

* [HGLLA24] Y. Hao, P. Grünwald, T. Lardy, L. Long and R. Adams, *E-values for k-sample tests
  with exponential families*, arXiv:2303.00471.
* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4, Theorem 4.1.
-/

public section

open MeasureTheory Set Finset TauCeti.Probability

open scoped ENNReal

namespace ProbabilityTheory

/-! ### The uniform law on an antidiagonal -/

/-- **The uniform law on an antidiagonal**: for `s : ℕ`, the uniform law on the `s + 1` pairs
`(j, k)` of natural numbers with `j + k = s`. Its first coordinate is uniform on `{0, …, s}`. -/
noncomputable def Kernel.antidiagonalUniform : Kernel ℕ (ℕ × ℕ) :=
  Kernel.ofFunOfCountable fun s ↦ uniformOn (antidiagonal s : Set (ℕ × ℕ))

/-- The uniform law on the pairs with sum `s`. -/
theorem Kernel.antidiagonalUniform_apply (s : ℕ) :
    Kernel.antidiagonalUniform s = uniformOn (antidiagonal s : Set (ℕ × ℕ)) := by
  unfold Kernel.antidiagonalUniform
  rfl

/-- The uniform law on an antidiagonal is a Markov kernel. -/
instance Kernel.isMarkovKernel_antidiagonalUniform : IsMarkovKernel Kernel.antidiagonalUniform :=
  ⟨fun s ↦ by
    rw [Kernel.antidiagonalUniform_apply]
    exact isProbabilityMeasure_uniformOn (finite_toSet _) ⟨(0, s), by simp⟩⟩

/-- The mass of a point under the uniform law on the pairs with sum `s`. -/
theorem Kernel.antidiagonalUniform_singleton (s : ℕ) (x : ℕ × ℕ) :
    Kernel.antidiagonalUniform s {x} = if x.1 + x.2 = s then ((s : ℝ≥0∞) + 1)⁻¹ else 0 := by
  classical
  rw [Kernel.antidiagonalUniform_apply, ← coe_singleton, uniformOn_apply_finset,
    Nat.card_antidiagonal]
  split_ifs with hx
  · rw [Finset.inter_singleton_of_mem (mem_antidiagonal.mpr hx)]
    simp
  · rw [Finset.inter_singleton_of_notMem (by simpa using hx)]
    simp

/-- Under the uniform law on the pairs with sum `s`, the coordinates add up to `s`. -/
theorem Kernel.ae_add_antidiagonalUniform (s : ℕ) :
    ∀ᵐ x ∂Kernel.antidiagonalUniform s, x.1 + x.2 = s := by
  rw [ae_iff, Kernel.antidiagonalUniform_apply, ← uniformOn_inter_self (finite_toSet _)]
  convert measure_empty (μ := uniformOn (antidiagonal s : Set (ℕ × ℕ)))
  ext x
  simp

/-! ### Laws on pairs whose masses depend on the sum -/

section Pairs

variable {μ : Measure (ℕ × ℕ)}

/-- The law of the sum at a point is the sum of the masses of the pairs with that sum. -/
private lemma map_add_singleton (μ : Measure (ℕ × ℕ)) (s : ℕ) :
    μ.map (fun x ↦ x.1 + x.2) {s} = ∑ x ∈ antidiagonal s, μ {x} := by
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton s),
    sum_measure_singleton]
  congr 1
  ext x
  simp

/-- The mass of a point under `Kernel.antidiagonalUniform ∘ₘ ν`. -/
private lemma antidiagonalUniform_comp_singleton (ν : Measure ℕ) (x : ℕ × ℕ) :
    (Kernel.antidiagonalUniform ∘ₘ ν) {x} =
      ν {x.1 + x.2} * (((x.1 + x.2 : ℕ) : ℝ≥0∞) + 1)⁻¹ := by
  rw [Measure.bind_apply (measurableSet_singleton x) (Kernel.aemeasurable _), lintegral_countable']
  simp_rw [Kernel.antidiagonalUniform_singleton]
  rw [tsum_eq_single (x.1 + x.2) fun s hs ↦ by simp [Ne.symm hs]]
  simp [mul_comm]

/-- A law on pairs whose mass at a point depends only on the sum has the conditional law
`Kernel.antidiagonalUniform` given the sum. -/
private lemma antidiagonalUniform_comp_map_add_of_singleton {g : ℕ → ℝ≥0∞}
    (h : ∀ x, μ {x} = g (x.1 + x.2)) :
    Kernel.antidiagonalUniform ∘ₘ μ.map (fun x ↦ x.1 + x.2) = μ := by
  refine Measure.ext_iff_singleton.mpr fun x ↦ ?_
  rw [antidiagonalUniform_comp_singleton, map_add_singleton,
    sum_congr rfl fun y hy ↦ by rw [h y, mem_antidiagonal.mp hy], sum_const,
    Nat.card_antidiagonal, nsmul_eq_mul, h x, mul_comm _ (g _), mul_assoc]
  push_cast
  rw [ENNReal.mul_inv_cancel (by positivity) (by simp), mul_one]

/-- Every law on pairs is absolutely continuous with respect to the law with its law of the sum
and the conditional law `Kernel.antidiagonalUniform` given the sum. -/
private lemma absolutelyContinuous_antidiagonalUniform_comp (μ : Measure (ℕ × ℕ)) :
    μ ≪ Kernel.antidiagonalUniform ∘ₘ μ.map (fun x ↦ x.1 + x.2) := by
  refine Measure.AbsolutelyContinuous.mk fun t _ ht ↦ ?_
  rw [← biUnion_of_singleton t, measure_biUnion_null_iff t.to_countable] at ht ⊢
  intro x hx
  have hx' := ht x hx
  rw [antidiagonalUniform_comp_singleton, mul_eq_zero, map_add_singleton,
    Finset.sum_eq_zero_iff] at hx'
  exact hx'.resolve_right (by simp) x (mem_antidiagonal.mpr rfl)

end Pairs

/-! ### Geometric laws -/

section Geometric

variable {p₁ p₂ : unitInterval}

/-- The geometric law with success probability `1` is the point mass at `0`, as is the junk value
`geometricMeasure 0`. -/
private lemma geometricMeasure_one : geometricMeasure 1 = geometricMeasure 0 := by
  have h0 : geometricMeasure 0 = Measure.dirac 0 := by simp [geometricMeasure]
  refine Measure.ext_iff_singleton.mpr fun n ↦ ?_
  rw [geometricMeasure_singleton one_ne_zero n, h0]
  rcases n with _ | n <;> simp

/-- Every geometric law is one with a positive success probability. -/
private lemma exists_ne_zero_geometricMeasure_eq (p : unitInterval) :
    ∃ q : unitInterval, q ≠ 0 ∧ geometricMeasure q = geometricMeasure p := by
  by_cases hp : p = 0
  · exact ⟨1, one_ne_zero, hp ▸ geometricMeasure_one⟩
  · exact ⟨p, hp, rfl⟩

/-- The mass of a point under a product of geometric laws with positive success
probabilities. -/
private lemma prod_geometricMeasure_singleton (h₁ : p₁ ≠ 0) (h₂ : p₂ ≠ 0) (x : ℕ × ℕ) :
    (geometricMeasure p₁).prod (geometricMeasure p₂) {x} =
      ENNReal.ofReal ((1 - p₁) ^ x.1 * p₁ * ((1 - p₂) ^ x.2 * p₂)) := by
  rw [← singleton_prod_singleton, Measure.prod_prod, geometricMeasure_singleton h₁,
    geometricMeasure_singleton h₂, ← ENNReal.ofReal_mul (geometricMeasure_nonneg _ _)]

/-- The mass of a point under `Geom(p) ⊗ Geom(p)` depends only on the sum. -/
private lemma exists_prod_geometricMeasure_self_singleton (p : unitInterval) :
    ∃ g : ℕ → ℝ≥0∞, ∀ x : ℕ × ℕ,
      (geometricMeasure p).prod (geometricMeasure p) {x} = g (x.1 + x.2) := by
  obtain ⟨q, hq, hqp⟩ := exists_ne_zero_geometricMeasure_eq p
  refine ⟨fun s ↦ ENNReal.ofReal ((1 - q) ^ s * q ^ 2), fun x ↦ ?_⟩
  rw [← hqp, prod_geometricMeasure_singleton hq hq]
  congr 1
  ring

/-- The point `0` has positive mass under every geometric law. -/
private lemma geometricMeasure_singleton_zero_pos (p : unitInterval) :
    0 < geometricMeasure p {0} := by
  obtain ⟨q, hq, hqp⟩ := exists_ne_zero_geometricMeasure_eq p
  rw [← hqp, geometricMeasure_singleton hq]
  simpa using unitInterval.pos_iff_ne_zero.mpr hq

/-- If one of the two geometric laws is not a point mass, the sum charges every point. -/
private lemma map_add_prod_geometricMeasure_singleton_pos
    (h : (p₁ ≠ 0 ∧ p₁ ≠ 1) ∨ (p₂ ≠ 0 ∧ p₂ ≠ 1)) (s : ℕ) :
    0 < ((geometricMeasure p₁).prod (geometricMeasure p₂)).map (fun x ↦ x.1 + x.2) {s} := by
  rw [map_add_singleton]
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · refine (lt_of_lt_of_le ?_ (single_le_sum (fun _ _ ↦ zero_le) (mem_antidiagonal.mpr
      (add_zero s) : (s, 0) ∈ antidiagonal s)))
    rw [← singleton_prod_singleton, Measure.prod_prod]
    refine ENNReal.mul_pos ?_ (geometricMeasure_singleton_zero_pos p₂).ne'
    rw [geometricMeasure_singleton h0]
    exact (ENNReal.ofReal_pos.mpr (geometricMeasure_pos h0 h1 s)).ne'
  · refine (lt_of_lt_of_le ?_ (single_le_sum (fun _ _ ↦ zero_le) (mem_antidiagonal.mpr
      (zero_add s) : (0, s) ∈ antidiagonal s)))
    rw [← singleton_prod_singleton, Measure.prod_prod]
    refine ENNReal.mul_pos (geometricMeasure_singleton_zero_pos p₁).ne' ?_
    rw [geometricMeasure_singleton h0]
    exact (ENNReal.ofReal_pos.mpr (geometricMeasure_pos h0 h1 s)).ne'

/-- The sum of the masses of `Geom(p₁) ⊗ Geom(p₂)` on the pairs with sum `s`. -/
private lemma sum_antidiagonal_geom {p₁ p₂ : ℝ} (h : p₁ ≠ p₂) (s : ℕ) :
    ∑ y ∈ antidiagonal s, (1 - p₁) ^ y.1 * p₁ * ((1 - p₂) ^ y.2 * p₂) =
      p₁ * p₂ * ((1 - p₁) ^ (s + 1) - (1 - p₂) ^ (s + 1)) / (p₂ - p₁) := by
  rw [eq_div_iff (sub_ne_zero.mpr h.symm), Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hg := geom_sum₂_mul (1 - p₁) (1 - p₂) (s + 1)
  simp only [add_tsub_cancel_right] at hg
  rw [show p₂ - p₁ = (1 - p₁) - (1 - p₂) by ring, mul_assoc, ← hg]
  simp only [sum_mul, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  ring

/-- The geometric laws, as a kernel. -/
private noncomputable def geomKernel : Kernel unitInterval ℕ :=
  ⟨geometricMeasure, measurable_geometricMeasure⟩

/-- The geometric laws are probability measures. -/
private instance : IsMarkovKernel geomKernel := ⟨fun _ ↦ isProbabilityMeasure_geometricMeasure⟩

/-- The laws `Geom(1 / m) ⊗ Geom(1 / m)`, as a kernel (the success probability is clipped to
`[0, 1]`). -/
private noncomputable def geomPairInvKernel : Kernel ℝ (ℕ × ℕ) :=
  (geomKernel ×ₖ geomKernel).comap (fun m : ℝ ↦ projIcc 0 1 zero_le_one m⁻¹) (by fun_prop)

/-- The mass of a point under the mixture of the laws `Geom(1 / m) ⊗ Geom(1 / m)` over `m`
uniform on `(a, b]`, for `1 ≤ a < b`. -/
private lemma geomPairInvKernel_comp_singleton {a b : ℝ} (ha : 1 ≤ a) (hab : a < b)
    (x : ℕ × ℕ) :
    (geomPairInvKernel ∘ₘ uniformMeasure a b) {x} =
      ENNReal.ofReal ((b - a)⁻¹ * (((1 - b⁻¹) ^ (x.1 + x.2 + 1) - (1 - a⁻¹) ^ (x.1 + x.2 + 1)) /
        (((x.1 + x.2 : ℕ) : ℝ) + 1))) := by
  set s := x.1 + x.2
  have hpos : ∀ m ∈ uIcc a b, 0 < m := fun m hm ↦ by
    rw [uIcc_of_le hab.le] at hm
    linarith [hm.1]
  have hderiv : ∀ m ∈ uIcc a b, HasDerivAt (fun m : ℝ ↦ (1 - m⁻¹) ^ (s + 1) / (s + 1))
      ((1 - m⁻¹) ^ s * (m ^ 2)⁻¹) m := fun m hm ↦
    ((((hasDerivAt_inv (hpos m hm).ne').const_sub 1).pow (s + 1)).div_const _).congr_deriv
      (by field_simp; push_cast; ring)
  have hcont : ContinuousOn (fun m : ℝ ↦ (1 - m⁻¹) ^ s * (m ^ 2)⁻¹) (uIcc a b) := by
    refine ContinuousOn.mul (by fun_prop (disch := exact fun m hm ↦ (hpos m hm).ne')) ?_
    fun_prop (disch := exact fun m hm ↦ pow_ne_zero 2 (hpos m hm).ne')
  have hmass : ∀ m ∈ Ioc a b, geomPairInvKernel m {x} =
      ENNReal.ofReal ((1 - m⁻¹) ^ s * (m ^ 2)⁻¹) := by
    intro m hm
    have hm0 : 0 < m := by linarith [hm.1]
    have hinv : m⁻¹ ∈ Icc (0 : ℝ) 1 := ⟨by positivity, inv_le_one_of_one_le₀ (by linarith [hm.1])⟩
    have hne : projIcc (0 : ℝ) 1 zero_le_one m⁻¹ ≠ 0 := by
      rw [ne_eq, ← Subtype.coe_inj, projIcc_of_mem _ hinv]
      exact (inv_pos.mpr hm0).ne'
    rw [geomPairInvKernel, Kernel.comap_apply, Kernel.prod_apply]
    change (geometricMeasure _).prod (geometricMeasure _) {x} = _
    rw [prod_geometricMeasure_singleton hne hne, projIcc_of_mem _ hinv]
    congr 1
    simp only [s]
    ring
  rw [Measure.bind_apply (measurableSet_singleton x) (Kernel.aemeasurable _),
    uniformMeasure_eq_smul, lintegral_smul_measure, setLIntegral_congr_fun measurableSet_Ioc hmass,
    ← ofReal_integral_eq_lintegral_ofReal, ← intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable,
    smul_eq_mul, ← ENNReal.ofReal_inv_of_pos (sub_pos.mpr hab),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (sub_pos.mpr hab).le), sub_div]
  · rw [uIcc_of_le hab.le] at hcont
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · refine ae_restrict_of_forall_mem measurableSet_Ioc fun m hm ↦ ?_
    have : 0 ≤ 1 - m⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ (by linarith [hm.1]))
    positivity

/-- **The conditional law given the sum is a mixture of members of the null**: for distinct
positive success probabilities, the law with the law of the sum under `Geom(p₁) ⊗ Geom(p₂)` and
the conditional law `Kernel.antidiagonalUniform` given the sum is the mixture of the laws
`Geom(1 / m) ⊗ Geom(1 / m)` over `m` uniform between `1 / p₁` and `1 / p₂`. -/
private lemma antidiagonalUniform_comp_map_add_prod_geometricMeasure (h₁ : p₁ ≠ 0)
    (h₂ : p₂ ≠ 0) (h : p₁ ≠ p₂) :
    Kernel.antidiagonalUniform ∘ₘ
        ((geometricMeasure p₁).prod (geometricMeasure p₂)).map (fun x ↦ x.1 + x.2) =
      geomPairInvKernel ∘ₘ uniformMeasure (min (p₁ : ℝ)⁻¹ (p₂ : ℝ)⁻¹)
        (max (p₁ : ℝ)⁻¹ (p₂ : ℝ)⁻¹) := by
  have h₁' : (0 : ℝ) < p₁ := unitInterval.pos_iff_ne_zero.mpr h₁
  have h₂' : (0 : ℝ) < p₂ := unitInterval.pos_iff_ne_zero.mpr h₂
  have hne : (p₁ : ℝ) ≠ p₂ := Subtype.coe_injective.ne h
  have ha : 1 ≤ min (p₁ : ℝ)⁻¹ (p₂ : ℝ)⁻¹ :=
    le_min (one_le_inv₀ h₁' |>.mpr p₁.2.2) (one_le_inv₀ h₂' |>.mpr p₂.2.2)
  have hab : min (p₁ : ℝ)⁻¹ (p₂ : ℝ)⁻¹ < max (p₁ : ℝ)⁻¹ (p₂ : ℝ)⁻¹ :=
    min_lt_max.mpr (inv_injective.ne hne)
  refine Measure.ext_iff_singleton.mpr fun x ↦ ?_
  have hc : (((x.1 + x.2 : ℕ) : ℝ≥0∞) + 1)⁻¹ = ENNReal.ofReal (((x.1 + x.2 : ℕ) : ℝ) + 1)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  have hnn : ∀ y ∈ antidiagonal (x.1 + x.2),
      0 ≤ (1 - (p₁ : ℝ)) ^ y.1 * p₁ * ((1 - p₂) ^ y.2 * p₂) := fun y _ ↦
    mul_nonneg (geometricMeasure_nonneg _ _) (geometricMeasure_nonneg _ _)
  rw [antidiagonalUniform_comp_singleton, map_add_singleton,
    sum_congr rfl fun y _ ↦ prod_geometricMeasure_singleton h₁ h₂ y,
    ← ENNReal.ofReal_sum_of_nonneg hnn, hc, ← ENNReal.ofReal_mul (sum_nonneg hnn),
    sum_antidiagonal_geom hne, geomPairInvKernel_comp_singleton ha hab]
  congr 1
  have h21 : (p₂ : ℝ) - p₁ ≠ 0 := sub_ne_zero.mpr hne.symm
  rcases hne.lt_or_gt with h' | h'
  · have hinv : (p₂ : ℝ)⁻¹ ≤ (p₁ : ℝ)⁻¹ := (inv_strictAnti₀ h₁' h').le
    rw [min_eq_right hinv, max_eq_left hinv, inv_inv, inv_inv]
    field_simp
  · have hinv : (p₁ : ℝ)⁻¹ ≤ (p₂ : ℝ)⁻¹ := (inv_strictAnti₀ h₂' h').le
    rw [min_eq_left hinv, max_eq_right hinv, inv_inv, inv_inv]
    field_simp
    ring

/-- A measure on `ℕ` is absolutely continuous with respect to a measure that charges every
point. -/
private lemma absolutelyContinuous_of_singleton_pos {μ ν : Measure ℕ} (h : ∀ s, 0 < ν {s}) :
    μ ≪ ν :=
  Measure.AbsolutelyContinuous.mk fun t _ ht ↦ by
    rcases t.eq_empty_or_nonempty with rfl | ⟨s, hs⟩
    · exact measure_empty
    · exact absurd ht ((h s).trans_le (measure_mono (singleton_subset_iff.mpr hs))).ne'

/-- The law with the law of the sum under `Geom(p₁) ⊗ Geom(p₂)` and the conditional law
`Kernel.antidiagonalUniform` given the sum is in the effective null. -/
private lemma antidiagonalUniform_comp_mem_effectiveSet (p₁ p₂ : unitInterval) :
    Kernel.antidiagonalUniform ∘ₘ
        ((geometricMeasure p₁).prod (geometricMeasure p₂)).map (fun x ↦ x.1 + x.2) ∈
      effectiveSet (Set.range fun p : unitInterval ↦
        (geometricMeasure p).prod (geometricMeasure p)) := by
  have hS : ∀ P ∈ Set.range fun p : unitInterval ↦ (geometricMeasure p).prod (geometricMeasure p),
      P univ ≤ 1 := by
    rintro _ ⟨p, rfl⟩
    exact prob_le_one
  obtain ⟨q₁, hq₁, hq₁p⟩ := exists_ne_zero_geometricMeasure_eq p₁
  obtain ⟨q₂, hq₂, hq₂p⟩ := exists_ne_zero_geometricMeasure_eq p₂
  rw [← hq₁p, ← hq₂p]
  rcases eq_or_ne q₁ q₂ with rfl | h
  · obtain ⟨g, hg⟩ := exists_prod_geometricMeasure_self_singleton q₁
    rw [antidiagonalUniform_comp_map_add_of_singleton hg]
    exact subset_effectiveSet hS ⟨q₁, rfl⟩
  have := isProbabilityMeasure_uniformMeasure
    (min_lt_max.mpr (inv_injective.ne (Subtype.coe_injective.ne h)) :
      min (q₁ : ℝ)⁻¹ (q₂ : ℝ)⁻¹ < max (q₁ : ℝ)⁻¹ (q₂ : ℝ)⁻¹)
  rw [antidiagonalUniform_comp_map_add_prod_geometricMeasure hq₁ hq₂ h]
  refine comp_mem_effectiveSet prob_le_one (ae_of_all _ fun m ↦ subset_effectiveSet hS ?_)
  refine ⟨projIcc 0 1 zero_le_one m⁻¹, ?_⟩
  rw [geomPairInvKernel, Kernel.comap_apply, Kernel.prod_apply]
  rfl

end Geometric

/-! ### The numeraire -/

/-- **The numeraire of two geometric observations against a common success probability.** If one
of the laws `Geom(p₁)` and `Geom(p₂)` is not a point mass, the likelihood ratio of
`Geom(p₁) ⊗ Geom(p₂)` to the law under which the sum of the two observations has its law under
`Geom(p₁) ⊗ Geom(p₂)` and, given the sum `s`, the first observation is uniform on `{0, …, s}`, is
the numeraire of the null of the products `Geom(p) ⊗ Geom(p)`: it is an e-variable, and no
e-variable has a larger expected logarithm under `Geom(p₁) ⊗ Geom(p₂)`
(`ProbabilityTheory.IsNumeraire.eintegral_log_le`). -/
theorem isNumeraire_rnDeriv_antidiagonalUniform_comp {p₁ p₂ : unitInterval}
    (h : (p₁ ≠ 0 ∧ p₁ ≠ 1) ∨ (p₂ ≠ 0 ∧ p₂ ≠ 1)) :
    IsNumeraire (((geometricMeasure p₁).prod (geometricMeasure p₂)).rnDeriv
        (Kernel.antidiagonalUniform ∘ₘ
          ((geometricMeasure p₁).prod (geometricMeasure p₂)).map fun x ↦ x.1 + x.2))
      (Set.range fun p : unitInterval ↦ (geometricMeasure p).prod (geometricMeasure p))
      ((geometricMeasure p₁).prod (geometricMeasure p₂)) := by
  refine isNumeraire_of_ae_eq_rnDeriv (isEVar_rnDeriv_comp_map (measurable_of_countable _)
    (ae_of_all _ Kernel.ae_add_antidiagonalUniform)
    (absolutelyContinuous_antidiagonalUniform_comp _) (by rintro _ ⟨p, rfl⟩; infer_instance) ?_ ?_)
    (antidiagonalUniform_comp_mem_effectiveSet p₁ p₂)
    (absolutelyContinuous_antidiagonalUniform_comp _) .rfl
  · rintro _ ⟨p, rfl⟩
    obtain ⟨g, hg⟩ := exists_prod_geometricMeasure_self_singleton p
    exact antidiagonalUniform_comp_map_add_of_singleton hg
  · rintro _ ⟨p, rfl⟩
    exact absolutelyContinuous_of_singleton_pos (map_add_prod_geometricMeasure_singleton_pos h)

end ProbabilityTheory
