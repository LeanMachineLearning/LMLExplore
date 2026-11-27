/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Statlib.EValues.RIPr
public import LMLExplore.EValues.KLInf
public import LMLExplore.EValues.EVariable
public import LMLExplore.EValues.Null.Polar
public import LMLExplore.EValues.PVariable
public import LMLExplore.MeasureTheory.Measure.AbsolutelyContinuousSet

/-!
# The effective null

The effective null of a null hypothesis `S : Set (Measure Ω)` is Statlib's `effectiveSet S`: the
measures `μ` under which every e-variable `X` for `S` has `∫⁻ X ∂μ ≤ 1`. It is the set over which
the duality `maxEPower_eq_klInf_effectiveSet` minimizes, and it describes the
alternatives that a null can be tested against: e-variables cannot distinguish `S` from its
effective null, and every measure outside its effective null is detected by a level-`α` test.

This file proves the structural properties of the effective null on any measurable space, with no
dominating measure and no convexity. Unless stated otherwise below, the results hold for any set of
measures `S`. The effective null is the polar `polarNull {X | IsEVar X S}` of the e-variables of
`S` (`effectiveSet_eq_polarNull`), so that its monotonicity, convexity, solidity and closure under
setwise limits are those of every polar (`LMLExplore.EValues.Null.Polar`). Statlib's
`isEVar_effectiveSet_iff` and `effectiveSet_effectiveSet` say that `S` and its effective null have
the same e-variables and the same effective null.

## Main statements

* `ProbabilityTheory.comp_mem_effectiveSet`: the effective null contains every mixture `κ ∘ₘ π` of
  members of the effective null over a measure `π` of mass at most `1`, in particular every
  mixture of members of `S` over a probability measure (with Statlib's `subset_effectiveSet`).
* `ProbabilityTheory.convex_effectiveSet`, `ProbabilityTheory.convexHull_subset_effectiveSet`: the
  effective null is convex and contains the convex hull of `S`.
* `ProbabilityTheory.isSigmaConvex_effectiveSet`: the effective null contains the countable
  mixtures of its members.
* `ProbabilityTheory.isLowerSet_effectiveSet`: the effective null is solid.
* `ProbabilityTheory.mem_effectiveSet_of_measure_le_liminf`,
  `ProbabilityTheory.mem_effectiveSet_of_tendsto`: the effective null is closed under setwise
  convergence, along any filter, and more generally contains every measure `μ` with
  `μ s ≤ liminf (μs · s)` for every measurable `s`, for a net `μs` eventually in it.
* `ProbabilityTheory.absolutelyContinuousSet_of_mem_effectiveSet`: every member of the effective
  null is absolutely continuous with respect to `S`
  (`MeasureTheory.Measure.AbsolutelyContinuousSet`).
* `ProbabilityTheory.absolutelyContinuous_of_mem_effectiveSet`: if every member of `S` is
  absolutely continuous with respect to `μ`, so is every member of the effective null.
* `ProbabilityTheory.exists_isEVar_le_lt_lintegral_of_notMem_effectiveSet`: a measure outside the
  effective null of `S` is detected by a bounded e-variable.
* `ProbabilityTheory.isTest_effectiveSet_iff`: the tests of level `α` for the effective null of
  `S` are the tests of level `α` for `S`.
* `ProbabilityTheory.exists_powered_test_iff`: a measure `Q` admits, for some `α ∈ (0, 1)`, a
  level-`α` test for `S` with power larger than `α` under `Q` exactly when `Q` is not in the
  effective null of `S` [RW, Theorem 6.10].
* `ProbabilityTheory.maxEPower_eq_zero_of_mem_effectiveSet`: for a null of measures of mass at
  most `1`, no e-variable for `S` has a positive expected logarithm under a probability measure of
  the effective null of `S`: the largest e-power is `0`.
* `ProbabilityTheory.maxEPower_eq_zero_iff_mem_effectiveSet`: conversely, under a probability
  measure outside the effective null, some e-variable has a positive expected logarithm.

## Implementation notes

The direction of `maxEPower_eq_zero_iff_mem_effectiveSet` from the vanishing to the membership is
stated, in its contrapositive form and with another proof, in
`EValuesResearch/Results/PartitionRate.lean` (commit `83205cb`) in the paper project
`RemyDegenne/evalues_research`; the proof here goes through the reverse information projection.

## References

* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810, Definition 3.1 and Lemma 4.5.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, Fact 3.6, §6.3.1 and Theorem 6.10.
-/

public section

open MeasureTheory Filter Set

open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S T : Set (Measure Ω)} {μ ν Q : Measure Ω}

/-- The effective null is monotone in the null. -/
@[gcongr]
theorem effectiveSet_mono (hST : S ⊆ T) : effectiveSet S ⊆ effectiveSet T := by
  rw [effectiveSet_eq_polarNull, effectiveSet_eq_polarNull]
  exact polarNull_anti fun _ hX ↦ hX.anti_set hST

/-- The effective null contains every mixture `κ ∘ₘ π` over a measure `π` of mass at most `1` of
a kernel `κ` whose values are `π`-almost surely in the effective null. With
Statlib's `subset_effectiveSet`, this contains every mixture over a probability measure of a kernel
with values in the null [LRR25, Definition 3.1]. -/
theorem comp_mem_effectiveSet {Θ : Type*} {mΘ : MeasurableSpace Θ} {π : Measure Θ}
    {κ : Kernel Θ Ω} (hπ : π univ ≤ 1) (hκ : ∀ᵐ θ ∂π, κ θ ∈ effectiveSet S) :
    κ ∘ₘ π ∈ effectiveSet S := by
  intro X hX
  rw [Measure.lintegral_bind κ.aemeasurable hX.measurable.aemeasurable]
  calc ∫⁻ θ, ∫⁻ ω, X ω ∂κ θ ∂π
  _ ≤ ∫⁻ _, 1 ∂π := lintegral_mono_ae (hκ.mono fun θ hθ ↦ hθ X hX)
  _ ≤ 1 := by simpa using hπ

/-- The effective null is convex, as every polar is. -/
theorem convex_effectiveSet : Convex ℝ≥0∞ (effectiveSet S) := by
  rw [effectiveSet_eq_polarNull]
  exact convex_polarNull _

/-- The effective null is σ-convex, as every polar is: it contains the countable mixtures of its
members. -/
theorem isSigmaConvex_effectiveSet : IsSigmaConvex (effectiveSet S) := by
  rw [effectiveSet_eq_polarNull]
  exact isSigmaConvex_polarNull _

/-- The effective null contains the convex hull of the null. -/
theorem convexHull_subset_effectiveSet : convexHull ℝ≥0∞ S ⊆ effectiveSet S :=
  convexHull_min subset_effectiveSet convex_effectiveSet

/-- The effective null is solid, as every polar is: a measure below a member of the effective
null is a member. -/
theorem isLowerSet_effectiveSet : IsLowerSet (effectiveSet S) := by
  rw [effectiveSet_eq_polarNull]
  exact isLowerSet_polarNull _

/-- A measure below a member of the effective null is a member of the effective null. -/
theorem mem_effectiveSet_of_le (hν : ν ∈ effectiveSet S) (hμν : μ ≤ ν) : μ ∈ effectiveSet S :=
  isLowerSet_effectiveSet hμν hν

/-- If `μs i` is eventually in the effective null along a filter, and `μ s` is at most the limit
inferior of `μs i s` for every measurable set `s`, then `μ` is in the effective null. -/
theorem mem_effectiveSet_of_measure_le_liminf {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → Measure Ω} (hμs : ∀ᶠ i in l, μs i ∈ effectiveSet S)
    (h : ∀ s, MeasurableSet s → μ s ≤ liminf (fun i ↦ μs i s) l) :
    μ ∈ effectiveSet S := by
  rw [effectiveSet_eq_polarNull] at hμs ⊢
  exact mem_polarNull_of_measure_le_liminf hμs h

/-- The effective null is closed under setwise convergence, as every polar is: if `μs i s` tends
to `μ s` along a filter for every measurable set `s`, and `μs i` is eventually in the effective
null, then so is `μ`. The filter is arbitrary, so that the effective null is closed for the
topology of setwise convergence and not only sequentially closed. -/
theorem mem_effectiveSet_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {μs : ι → Measure Ω}
    (hμs : ∀ᶠ i in l, μs i ∈ effectiveSet S)
    (h : ∀ s, MeasurableSet s → Tendsto (fun i ↦ μs i s) l (𝓝 (μ s))) :
    μ ∈ effectiveSet S := by
  rw [effectiveSet_eq_polarNull] at hμs ⊢
  exact mem_polarNull_of_tendsto hμs h

/-- A measurable set that is null for every member of `S` is null for every member of the
effective null of `S`. -/
theorem measure_eq_zero_of_mem_effectiveSet (hμ : μ ∈ effectiveSet S) {s : Set Ω}
    (hs : MeasurableSet s) (hS : ∀ P ∈ S, P s = 0) : μ s = 0 := by
  classical
  have h : ∞ * μ s ≤ 1 := by
    rw [← lintegral_indicator_const hs]
    refine (lintegral_mono fun ω ↦ ?_).trans (hμ _ (isEVar_piecewise_top hs hS))
    by_cases hω : ω ∈ s <;> simp [hω]
  by_contra h_ne
  simp [ENNReal.top_mul h_ne] at h

/-- Every member of the effective null of `S` is absolutely continuous with respect to `S`. -/
theorem absolutelyContinuousSet_of_mem_effectiveSet (hμ : μ ∈ effectiveSet S) :
    μ.AbsolutelyContinuousSet S :=
  Measure.absolutelyContinuousSet_iff.mpr fun _ hs h ↦ measure_eq_zero_of_mem_effectiveSet hμ hs h

/-- If every member of `S` is absolutely continuous with respect to a measure `ν`, so is every
member of the effective null of `S`. -/
theorem absolutelyContinuous_of_mem_effectiveSet (hμ : μ ∈ effectiveSet S)
    (hS : ∀ P ∈ S, P ≪ ν) : μ ≪ ν :=
  (absolutelyContinuousSet_of_mem_effectiveSet hμ).absolutelyContinuous hS

/-- The truncation `min X c` of an e-variable `X` for `S` at any level `c` is an e-variable for
`S`. -/
theorem IsEVar.min_const {X : Ω → ℝ≥0∞} (hX : IsEVar X S) (c : ℝ≥0∞) :
    IsEVar (fun ω ↦ min (X ω) c) S :=
  hX.mono (hX.measurable.min measurable_const) fun _ ↦ min_le_left _ _

/-- **Bounds on the null hold on the effective null.** If every member of `S` gives an integral
at most `c` to a measurable function `φ`, so does every member of the effective null of `S`. -/
theorem lintegral_le_of_mem_effectiveSet (hμ : μ ∈ effectiveSet S) {φ : Ω → ℝ≥0∞}
    (hφ : Measurable φ) {c : ℝ≥0∞} (h : ∀ P ∈ S, ∫⁻ ω, φ ω ∂P ≤ c) : ∫⁻ ω, φ ω ∂μ ≤ c := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hc ↦ ?_
  -- `φ / (c + ε)` is an e-variable for `S`
  have hd0 : c + ε ≠ 0 := by simpa using fun _ ↦ hε.ne'
  have hd_top : c + ε ≠ ∞ := ENNReal.add_ne_top.2 ⟨hc.ne, ENNReal.coe_ne_top⟩
  have h_div (ν : Measure Ω) : ∫⁻ ω, φ ω / (c + ε) ∂ν = (∫⁻ ω, φ ω ∂ν) / (c + ε) := by
    simp_rw [div_eq_mul_inv]
    exact lintegral_mul_const _ hφ
  have hY : IsEVar (fun ω ↦ φ ω / (c + ε)) S := ⟨hφ.div_const _, fun P hP ↦ by
    rw [h_div, ENNReal.div_le_iff hd0 hd_top, one_mul]
    exact (h P hP).trans le_self_add⟩
  have h_le := hμ _ hY
  rwa [h_div, ENNReal.div_le_iff hd0 hd_top, one_mul] at h_le

/-- A measure `Q` outside the effective null of a null `S` is detected by a
bounded e-variable: some e-variable for `S` bounded by an integer `N ≥ 2` has expectation larger
than `1` under `Q`. -/
theorem exists_isEVar_le_lt_lintegral_of_notMem_effectiveSet (hQ : Q ∉ effectiveSet S) :
    ∃ Y : Ω → ℝ≥0∞, ∃ N : ℕ, 2 ≤ N ∧ IsEVar Y S ∧ (∀ ω, Y ω ≤ N) ∧ 1 < ∫⁻ ω, Y ω ∂Q := by
  obtain ⟨X, hX, hXQ⟩ : ∃ X, IsEVar X S ∧ 1 < ∫⁻ ω, X ω ∂Q := by
    simpa [mem_effectiveSet_iff] using hQ
  -- `Y` is the truncation `min X N` of an e-variable `X` with expectation larger than `1` under
  -- `Q`, for `N` large enough. By monotone convergence, the truncations `min X N` have
  -- expectation larger than `1` under `Q` from some level `N ≥ 2` on.
  have hXm := hX.measurable
  have h_tendsto : Tendsto (fun N : ℕ ↦ ∫⁻ ω, min (X ω) N ∂Q) atTop (𝓝 (∫⁻ ω, X ω ∂Q)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun N ↦ by fun_prop) (.of_forall
      fun ω N M hNM ↦ min_le_min_left _ (by exact_mod_cast hNM)) (.of_forall fun ω ↦ ?_)
    simpa using (tendsto_const_nhds (x := X ω)).min ENNReal.tendsto_nat_nhds_top
  obtain ⟨N, hNQ, hN2⟩ := ((h_tendsto.eventually (lt_mem_nhds hXQ)).and
    (eventually_ge_atTop 2)).exists
  exact ⟨fun ω ↦ min (X ω) N, N, hN2, hX.min_const N,
    fun ω ↦ min_le_right _ _, hNQ⟩

/-- The tests of level `α` for the effective null of `S` are the tests of level `α` for `S`: a
test for `S` keeps its level under every member of the effective null. This is the form for tests
of Statlib's `isEVar_effectiveSet_iff`, through [RW, Fact 3.6]. -/
@[simp]
theorem isTest_effectiveSet_iff {φ : Ω → ℝ≥0∞} {α : ℝ≥0∞} :
    IsTest φ (effectiveSet S) α ↔ IsTest φ S α := by
  simp_rw [isTest_iff_measurable_isEVar_div, isEVar_effectiveSet_iff]

/-- A measure `Q` is outside the effective null of a null `S` exactly when, for some level
`α ∈ (0, 1)`, some test `φ` of level `α` for `S` has expectation larger than `α` under `Q`
[RW, Theorem 6.10, for a null of probability measures]. -/
theorem exists_powered_test_iff (Q : Measure Ω) :
    (∃ α : ℝ≥0∞, 0 < α ∧ α < 1 ∧ ∃ φ : Ω → ℝ≥0∞, IsTest φ S α ∧ α < ∫⁻ ω, φ ω ∂Q) ↔
      Q ∉ effectiveSet S := by
  constructor
  · -- A test of level `α` for `S` has level `α` under every member of the effective null.
    rintro ⟨α, -, -, φ, hφ, hφQ⟩ hQ
    exact ((isTest_effectiveSet_iff.2 hφ).lintegral_le Q hQ).not_gt hφQ
  · -- A bounded e-variable with expectation larger than `1` under `Q`, divided by its bound `N`,
    -- is a level-`N⁻¹` test with power larger than `N⁻¹` under `Q` [RW, Fact 3.6].
    intro hQ
    obtain ⟨Y, N, hN2, hY, hYN, hYQ⟩ := exists_isEVar_le_lt_lintegral_of_notMem_effectiveSet hQ
    have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have hNtop : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
    have hNinv : (N : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hNtop
    have hNinv' : (N : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hN0
    -- `Y / N` divided by the level `N⁻¹` is the e-variable `Y`.
    have hφ : IsTest (fun ω ↦ Y ω / N) S (N : ℝ≥0∞)⁻¹ := by
      refine (isTest_iff_isEVar_div hNinv hNinv').2 ⟨fun ω ↦ ?_, ?_⟩
      · exact ENNReal.div_le_of_le_mul (by simpa using hYN ω)
      · simpa [div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel hN0 hNtop] using hY
    refine ⟨(N : ℝ≥0∞)⁻¹, pos_iff_ne_zero.2 hNinv, ENNReal.inv_lt_one.2
      (by exact_mod_cast (by omega : 1 < N)), _, hφ, ?_⟩
    simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const _ hY.measurable]
    simpa [mul_comm] using ENNReal.mul_lt_mul_right hNinv hNinv' hYQ

/-- For a null of measures of mass at most `1`, under a probability measure `P` of its effective
null, no e-variable for `S` has a positive expected logarithm: the largest e-power is `0`. This
extends Statlib's `maxUtility_eq_zero_of_mem` from the members of `S` to its effective null, which
has the same e-variables (`maxEPower_effectiveSet`). -/
theorem maxEPower_eq_zero_of_mem_effectiveSet {P : Measure Ω} [IsProbabilityMeasure P]
    (hS : ∀ μ ∈ S, μ univ ≤ 1) (hP : P ∈ effectiveSet S) : maxEPower P S = 0 := by
  rw [← maxEPower_effectiveSet, maxEPower_def]
  exact maxUtility_eq_zero_of_mem (fun _ hμ ↦ measure_univ_le_one_of_mem_effectiveSet hS hμ) hP

/-- For a null of measures of mass at most `1`, the largest e-power under a probability measure
`Q` vanishes exactly when `Q` is in the effective null of `S`: some e-variable for `S` has a
positive expected logarithm under every probability measure outside the effective null. The
largest e-power is the divergence `klIntegral Q (ripr Q S)` to the reverse information projection
(Statlib's `maxUtility_eq_klIntegral_ripr`), which is `klDiv Q (ripr Q S)` plus the missing mass
`1 - ripr Q S univ ≥ 0`. If it vanishes, so does `klDiv Q (ripr Q S)`, and `Q` is the reverse
information projection, a member of the effective null. -/
theorem maxEPower_eq_zero_iff_mem_effectiveSet [IsProbabilityMeasure Q]
    (hS : ∀ μ ∈ S, μ univ ≤ 1) : maxEPower Q S = 0 ↔ Q ∈ effectiveSet S := by
  refine ⟨fun h ↦ ?_, maxEPower_eq_zero_of_mem_effectiveSet hS⟩
  rw [maxEPower_def, maxUtility_eq_klIntegral_ripr hS, klIntegral_eq_klDiv_add_sub,
    probReal_univ] at h
  have hR : (ripr Q S).real univ ≤ 1 := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using ripr_univ_le_one Q (S := S))
  have hk : InformationTheory.klDiv Q (ripr Q S) ≠ ∞ := by
    intro hk
    rw [hk, EReal.coe_ennreal_top, EReal.top_add_coe, EReal.top_sub_coe] at h
    exact EReal.top_ne_zero h
  rw [← ENNReal.ofReal_toReal hk, EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg,
    ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_eq_zero] at h
  have hQ : InformationTheory.klDiv Q (ripr Q S) = 0 := by
    rw [← ENNReal.ofReal_toReal hk, ENNReal.ofReal_eq_zero]
    linarith
  rw [InformationTheory.klDiv_eq_zero_iff] at hQ
  exact hQ ▸ ripr_mem_effectiveSet Q hS

end ProbabilityTheory
