/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.CondEVariable.Statistic
public import LMLExplore.EValues.Numeraire
public import LMLExplore.Probability.Kernel.AntidiagonalUniform
public import Mathlib.Probability.Distributions.Geometric
import LMLExplore.Algebra.BigOperators.NatAntidiagonal
import LMLExplore.MeasureTheory.Measure.Singletons
import LMLExplore.Probability.Distributions.Geometric
import LMLExplore.Probability.Distributions.Uniform
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
under `Q` (`ProbabilityTheory.isNumeraire_rnDeriv_antidiagonalUniform_comp`), as computed in
[EVR26, Note 28]. As for two exponential observations
(`ProbabilityTheory.isNumeraire_rnDeriv_segmentUniform_comp`), for distinct positive success
probabilities `p₁ ≠ p₂` that law is the mixture of the members `Geom(1 / m) ⊗ Geom(1 / m)` of the
null over `m` uniform between `1 / p₁` and `1 / p₂`, that is, over the mean `m - 1` uniform between
the two means; when `p₁ = p₂` it is `Q` itself. In both cases it belongs to the effective null.

## Main statements

* `ProbabilityTheory.isNumeraire_rnDeriv_antidiagonalUniform_comp`: the numeraire of two geometric
  observations against a common success probability [EVR26, Note 28].

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
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, paper project
  `RemyDegenne/evalues_research` (2026), Note 28.
-/

public section

open MeasureTheory Set Finset TauCeti.Probability

open scoped ENNReal

namespace ProbabilityTheory

/-! ### Geometric laws -/

section Geometric

variable {p₁ p₂ : unitInterval}

/-- The mass of a point under `Geom(p) ⊗ Geom(p)` depends only on the sum. -/
private lemma exists_prod_geometricMeasure_self_singleton (p : unitInterval) :
    ∃ g : ℕ → ℝ≥0∞, ∀ x : ℕ × ℕ,
      (geometricMeasure p).prod (geometricMeasure p) {x} = g (x.1 + x.2) := by
  obtain ⟨q, hq, hqp⟩ := exists_ne_zero_geometricMeasure_eq p
  refine ⟨fun s ↦ ENNReal.ofReal ((1 - q) ^ s * q ^ 2), fun x ↦ ?_⟩
  rw [← hqp, prod_geometricMeasure_singleton hq hq]
  congr 1
  ring

/-- If one of the two geometric laws is not a point mass, the sum charges every point. -/
private lemma map_add_prod_geometricMeasure_singleton_pos
    (h : (p₁ ≠ 0 ∧ p₁ ≠ 1) ∨ (p₂ ≠ 0 ∧ p₂ ≠ 1)) (s : ℕ) :
    0 < ((geometricMeasure p₁).prod (geometricMeasure p₂)).map (fun x ↦ x.1 + x.2) {s} := by
  rw [Measure.map_add_singleton_eq_sum_antidiagonal]
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

/-- The geometric laws, as a kernel. -/
private noncomputable def geomKernel : Kernel unitInterval ℕ :=
  ⟨geometricMeasure, measurable_geometricMeasure⟩

/-- The geometric laws are probability measures. -/
private instance : IsMarkovKernel geomKernel := ⟨fun _ ↦ isProbabilityMeasure_geometricMeasure⟩

/-- The geometric kernel maps `p` to `Geom(p)`. -/
private lemma geomKernel_apply (p : unitInterval) : geomKernel p = geometricMeasure p := rfl

/-- The laws `Geom(1 / m) ⊗ Geom(1 / m)`, as a kernel (the success probability is clipped to
`[0, 1]`). -/
private noncomputable def geomPairInvKernel : Kernel ℝ (ℕ × ℕ) :=
  (geomKernel ×ₖ geomKernel).comap (fun m : ℝ ↦ projIcc 0 1 zero_le_one m⁻¹) (by fun_prop)

/-- The kernel `geomPairInvKernel` maps `m` to `Geom(1 / m) ⊗ Geom(1 / m)`, with the success
probability clipped to `[0, 1]`. -/
private lemma geomPairInvKernel_apply (m : ℝ) :
    geomPairInvKernel m = (geometricMeasure (projIcc 0 1 zero_le_one m⁻¹)).prod
      (geometricMeasure (projIcc 0 1 zero_le_one m⁻¹)) := by
  rw [geomPairInvKernel, Kernel.comap_apply, Kernel.prod_apply, geomKernel_apply]

/-- The mass of a point under the mixture of the laws `Geom(1 / m) ⊗ Geom(1 / m)` over `m`
uniform between two distinct `a, b ≥ 1`. -/
private lemma geomPairInvKernel_comp_singleton {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≠ b)
    (x : ℕ × ℕ) :
    (geomPairInvKernel ∘ₘ uniformMeasure (min a b) (max a b)) {x} =
      ENNReal.ofReal ((b - a)⁻¹ * (((1 - b⁻¹) ^ (x.1 + x.2 + 1) - (1 - a⁻¹) ^ (x.1 + x.2 + 1)) /
        (((x.1 + x.2 : ℕ) : ℝ) + 1))) := by
  set s := x.1 + x.2
  have hone : ∀ m ∈ uIcc a b, 1 ≤ m := fun m hm ↦ (le_inf ha hb).trans hm.1
  have hderiv : ∀ m ∈ uIcc a b, HasDerivAt (fun m : ℝ ↦ (1 - m⁻¹) ^ (s + 1) / (s + 1))
      ((1 - m⁻¹) ^ s * (m ^ 2)⁻¹) m := fun m hm ↦
    ((((hasDerivAt_inv (zero_lt_one.trans_le (hone m hm)).ne').const_sub 1).pow (s + 1)).div_const
      _).congr_deriv (by field_simp; push_cast; ring)
  have hcont : ContinuousOn (fun m : ℝ ↦ (1 - m⁻¹) ^ s * (m ^ 2)⁻¹) (uIcc a b) := by
    refine ContinuousOn.mul
      (by fun_prop (disch := exact fun m hm ↦ (zero_lt_one.trans_le (hone m hm)).ne')) ?_
    fun_prop (disch := exact fun m hm ↦ pow_ne_zero 2 (zero_lt_one.trans_le (hone m hm)).ne')
  have hmass : ∀ᵐ m ∂uniformMeasure (min a b) (max a b), geomPairInvKernel m {x} =
      ENNReal.ofReal ((1 - m⁻¹) ^ s * (m ^ 2)⁻¹) := by
    filter_upwards [ae_mem_Ioc_uniformMeasure] with m hm
    have hm1 : 1 ≤ m := (le_min ha hb).trans hm.1.le
    have hinv : m⁻¹ ∈ Icc (0 : ℝ) 1 := ⟨by positivity, inv_le_one_of_one_le₀ hm1⟩
    have hne : projIcc (0 : ℝ) 1 zero_le_one m⁻¹ ≠ 0 := by
      rw [ne_eq, ← Subtype.coe_inj, projIcc_of_mem _ hinv]
      exact (inv_pos.mpr (zero_lt_one.trans_le hm1)).ne'
    rw [geomPairInvKernel_apply, prod_geometricMeasure_singleton hne hne, projIcc_of_mem _ hinv]
    congr 1
    simp only [s]
    ring
  rw [Measure.bind_apply (measurableSet_singleton x) (Kernel.aemeasurable _),
    lintegral_congr_ae hmass,
    lintegral_ofReal_uniformMeasure_min_max_of_hasDerivAt hab hderiv hcont fun m hm ↦ ?_, sub_div]
  have : 0 ≤ 1 - m⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ (hone m (uIoc_subset_uIcc hm)))
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
  have h12 : (p₁ : ℝ) - p₂ ≠ 0 := sub_ne_zero.mpr hne
  have h21 : (p₂ : ℝ) - p₁ ≠ 0 := sub_ne_zero.mpr hne.symm
  refine Measure.ext_iff_singleton.mpr fun x ↦ ?_
  set s := x.1 + x.2
  have hc : ((s : ℝ≥0∞) + 1)⁻¹ = ENNReal.ofReal ((s : ℝ) + 1)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  have hnn : ∀ y ∈ antidiagonal s,
      0 ≤ (1 - (p₁ : ℝ)) ^ y.1 * p₁ * ((1 - p₂) ^ y.2 * p₂) := fun y _ ↦
    mul_nonneg (geometricMeasure_nonneg _ _) (geometricMeasure_nonneg _ _)
  -- the law of the sum at `s`, a geometric sum over the antidiagonal
  have hsum : ∑ y ∈ antidiagonal s, (1 - (p₁ : ℝ)) ^ y.1 * p₁ * ((1 - p₂) ^ y.2 * p₂) =
      p₁ * p₂ * ((1 - p₁) ^ (s + 1) - (1 - p₂) ^ (s + 1)) / (p₂ - p₁) := by
    rw [eq_div_iff h21, ← Nat.sum_antidiagonal_pow_mul_pow_mul_sub, sum_mul, sum_mul, mul_sum]
    refine sum_congr rfl fun y _ ↦ ?_
    ring
  rw [Kernel.antidiagonalUniform_comp_singleton, Measure.map_add_singleton_eq_sum_antidiagonal,
    sum_congr rfl fun y _ ↦ prod_geometricMeasure_singleton h₁ h₂ y,
    ← ENNReal.ofReal_sum_of_nonneg hnn, hc, ← ENNReal.ofReal_mul (sum_nonneg hnn), hsum,
    geomPairInvKernel_comp_singleton (one_le_inv₀ h₁' |>.mpr p₁.2.2)
      (one_le_inv₀ h₂' |>.mpr p₂.2.2) (inv_injective.ne hne), inv_inv, inv_inv]
  congr 1
  field_simp
  ring

/-- The law with the law of the sum under `Geom(p₁) ⊗ Geom(p₂)` and the conditional law
`Kernel.antidiagonalUniform` given the sum is in the effective null. -/
private lemma antidiagonalUniform_comp_mem_effectiveSet (p₁ p₂ : unitInterval) :
    Kernel.antidiagonalUniform ∘ₘ
        ((geometricMeasure p₁).prod (geometricMeasure p₂)).map (fun x ↦ x.1 + x.2) ∈
      effectiveSet (Set.range fun p : unitInterval ↦
        (geometricMeasure p).prod (geometricMeasure p)) := by
  obtain ⟨q₁, hq₁, hq₁p⟩ := exists_ne_zero_geometricMeasure_eq p₁
  obtain ⟨q₂, hq₂, hq₂p⟩ := exists_ne_zero_geometricMeasure_eq p₂
  rw [← hq₁p, ← hq₂p]
  rcases eq_or_ne q₁ q₂ with rfl | h
  · obtain ⟨g, hg⟩ := exists_prod_geometricMeasure_self_singleton q₁
    rw [Kernel.antidiagonalUniform_comp_map_add_of_singleton hg]
    exact subset_effectiveSet ⟨q₁, rfl⟩
  have := isProbabilityMeasure_uniformMeasure
    (min_lt_max.mpr (inv_injective.ne (Subtype.coe_injective.ne h)) :
      min (q₁ : ℝ)⁻¹ (q₂ : ℝ)⁻¹ < max (q₁ : ℝ)⁻¹ (q₂ : ℝ)⁻¹)
  rw [antidiagonalUniform_comp_map_add_prod_geometricMeasure hq₁ hq₂ h]
  refine comp_mem_effectiveSet prob_le_one (ae_of_all _ fun m ↦ subset_effectiveSet ?_)
  exact ⟨projIcc 0 1 zero_le_one m⁻¹, (geomPairInvKernel_apply m).symm⟩

end Geometric

/-! ### The numeraire -/

/-- **The numeraire of two geometric observations against a common success probability.** If one
of the laws `Geom(p₁)` and `Geom(p₂)` is not a point mass, the likelihood ratio of
`Geom(p₁) ⊗ Geom(p₂)` to the law under which the sum of the two observations has its law under
`Geom(p₁) ⊗ Geom(p₂)` and, given the sum `s`, the first observation is uniform on `{0, …, s}`, is
the numeraire of the null of the products `Geom(p) ⊗ Geom(p)`: it is an e-variable, and no
e-variable has a larger expected logarithm under `Geom(p₁) ⊗ Geom(p₂)`
(`ProbabilityTheory.IsNumeraire.eintegral_log_le`). This is the geometric instance of
[EVR26, Note 28]. -/
theorem isNumeraire_rnDeriv_antidiagonalUniform_comp {p₁ p₂ : unitInterval}
    (h : (p₁ ≠ 0 ∧ p₁ ≠ 1) ∨ (p₂ ≠ 0 ∧ p₂ ≠ 1)) :
    IsNumeraire (((geometricMeasure p₁).prod (geometricMeasure p₂)).rnDeriv
        (Kernel.antidiagonalUniform ∘ₘ
          ((geometricMeasure p₁).prod (geometricMeasure p₂)).map fun x ↦ x.1 + x.2))
      (Set.range fun p : unitInterval ↦ (geometricMeasure p).prod (geometricMeasure p))
      ((geometricMeasure p₁).prod (geometricMeasure p₂)) := by
  have hS : ∀ P ∈ Set.range fun p : unitInterval ↦ (geometricMeasure p).prod (geometricMeasure p),
      P univ ≤ 1 := by
    rintro _ ⟨p, rfl⟩
    exact prob_le_one
  refine isNumeraire_rnDeriv_comp_map (measurable_of_countable _)
    (ae_of_all _ Kernel.ae_add_antidiagonalUniform)
    (Kernel.absolutelyContinuous_antidiagonalUniform_comp _) hS ?_ ?_
    (antidiagonalUniform_comp_mem_effectiveSet p₁ p₂)
  · rintro _ ⟨p, rfl⟩
    obtain ⟨g, hg⟩ := exists_prod_geometricMeasure_self_singleton p
    exact Kernel.antidiagonalUniform_comp_map_add_of_singleton hg
  · rintro _ ⟨p, rfl⟩
    exact Measure.absolutelyContinuous_of_forall_singleton_pos
      (map_add_prod_geometricMeasure_singleton_pos h)

end ProbabilityTheory
