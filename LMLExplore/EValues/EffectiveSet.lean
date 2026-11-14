/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Statlib.EValues.RIPr
public import LMLExplore.MeasureTheory.Integral.Lebesgue.Add

/-!
# The effective null

The effective null of a null hypothesis `S : Set (Measure Ω)` is Statlib's `effectiveSet S`: the
measures `μ` under which every e-variable `X` for `S` has `∫⁻ X ∂μ ≤ 1`. It is the set over which
Statlib's duality `maxUtility_eq_iInf_klIntegral_effectiveSet` minimizes, and it describes the
alternatives that a null can be tested against: e-variables cannot distinguish `S` from its
effective null, and every probability measure outside of it is detected by a level-`α` test.

This file proves the structural properties of the effective null, for any set of measures `S` on
any measurable space, with no dominating measure and no convexity.

## Main statements

* `ProbabilityTheory.subset_effectiveSet_iff`: `S ⊆ effectiveSet S` exactly when every member of
  `S` has mass at most `1`.
* `ProbabilityTheory.comp_mem_effectiveSet`: the effective null contains every mixture `κ ∘ₘ π` of
  members of the effective null over a measure `π` of mass at most `1`, in particular every mixture
  of members of `S` over a probability measure.
* `ProbabilityTheory.convex_effectiveSet`, `ProbabilityTheory.convexHull_subset_effectiveSet`: the
  effective null is convex, and contains the convex hull of `S`.
* `ProbabilityTheory.isLowerSet_effectiveSet`: the effective null is solid.
* `ProbabilityTheory.mem_effectiveSet_of_tendsto`: the effective null is closed under setwise
  convergence, along any filter.
* `ProbabilityTheory.isEVar_effectiveSet_inter_iff`: `S` and the probability measures of its
  effective null have the same e-variables, so that
  `ProbabilityTheory.effectiveSet_effectiveSet_inter` they have the same effective null.
* `ProbabilityTheory.absolutelyContinuous_of_mem_effectiveSet`: if every member of `S` is
  absolutely continuous with respect to `μ`, so is every member of the effective null.
* `ProbabilityTheory.exists_test_iff_notMem_effectiveSet`: a measure `Q` admits, for some
  `α ∈ (0, 1)`, a level-`α` test for `S` with power larger than `α` under `Q` exactly when `Q` is
  not in the effective null of `S` [RW, Theorem 6.10].

## References

* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810, Definition 3.1 and Lemma 4.5.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, §6.3.1 and Theorem 6.10.
-/

public section

open MeasureTheory Filter Set

open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S T : Set (Measure Ω)} {μ ν Q : Measure Ω}

/-- The effective null is monotone in the null. -/
theorem effectiveSet_mono (hST : S ⊆ T) : effectiveSet S ⊆ effectiveSet T :=
  fun _ hμ X hX ↦ hμ X (hX.anti_set hST)

/-- A null is contained in its effective null exactly when each of its members has mass at
most `1`; in particular a null of probability measures is contained in its effective null. -/
theorem subset_effectiveSet_iff : S ⊆ effectiveSet S ↔ ∀ P ∈ S, P univ ≤ 1 :=
  ⟨fun h _ hP ↦ measure_univ_le_one_of_mem_effectiveSet (h hP),
    fun hS P hP _ hX ↦ (hX.lintegral_le_measure_univ P hP).trans (hS P hP)⟩

/-- A null of measures of mass at most `1` is contained in its effective null. -/
theorem subset_effectiveSet (hS : ∀ P ∈ S, P univ ≤ 1) : S ⊆ effectiveSet S :=
  subset_effectiveSet_iff.mpr hS

/-- The effective null contains every mixture `κ ∘ₘ π` over a measure `π` of mass at most `1` of
a kernel `κ` whose values are `π`-almost surely in the effective null. With
`subset_effectiveSet`, this contains every mixture over a probability measure of a kernel with
values in a null of probability measures [LRR25, Definition 3.1]. -/
theorem comp_mem_effectiveSet {Θ : Type*} {mΘ : MeasurableSpace Θ} {π : Measure Θ}
    {κ : Kernel Θ Ω} (hπ : π univ ≤ 1) (hκ : ∀ᵐ θ ∂π, κ θ ∈ effectiveSet S) :
    κ ∘ₘ π ∈ effectiveSet S := by
  intro X hX
  rw [Measure.lintegral_bind κ.aemeasurable hX.measurable.aemeasurable]
  calc ∫⁻ θ, ∫⁻ ω, X ω ∂κ θ ∂π
  _ ≤ ∫⁻ _, 1 ∂π := lintegral_mono_ae (hκ.mono fun θ hθ ↦ hθ X hX)
  _ ≤ 1 := by simpa using hπ

/-- The effective null is convex. -/
theorem convex_effectiveSet : Convex ℝ≥0∞ (effectiveSet S) := by
  intro μ hμ ν hν a b _ _ hab
  -- A convex combination is a mixture over the two-point space `Bool`.
  have h_eq : Kernel.boolKernel μ ν ∘ₘ (a • Measure.dirac false + b • Measure.dirac true) =
      a • μ + b • ν := by
    simp [Measure.comp_add, Measure.comp_smul, Measure.dirac_bind (Kernel.measurable _)]
  rw [← h_eq]
  refine comp_mem_effectiveSet (by simp [hab]) (.of_forall fun x ↦ ?_)
  cases x <;> simpa

/-- The effective null of a null of measures of mass at most `1` contains its convex hull. -/
theorem convexHull_subset_effectiveSet (hS : ∀ P ∈ S, P univ ≤ 1) :
    convexHull ℝ≥0∞ S ⊆ effectiveSet S :=
  convexHull_min (subset_effectiveSet hS) convex_effectiveSet

/-- The effective null is solid: a measure below a member of the effective null is a member. -/
theorem isLowerSet_effectiveSet : IsLowerSet (effectiveSet S) :=
  fun _ _ hμν hν X hX ↦ (lintegral_mono' hμν le_rfl).trans (hν X hX)

/-- A measure below a member of the effective null is a member of the effective null. -/
theorem mem_effectiveSet_of_le (hν : ν ∈ effectiveSet S) (hμν : μ ≤ ν) : μ ∈ effectiveSet S :=
  isLowerSet_effectiveSet hμν hν

/-- The effective null is closed under setwise convergence: if `μs i s` tends to `μ s` along a
filter for every measurable set `s`, and `μs i` is eventually in the effective null, then so is
`μ`. The filter is arbitrary, so that the effective null is closed for the topology of setwise
convergence and not only sequentially closed. -/
theorem mem_effectiveSet_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {μs : ι → Measure Ω}
    (hμs : ∀ᶠ i in l, μs i ∈ effectiveSet S)
    (h : ∀ s, MeasurableSet s → Tendsto (fun i ↦ μs i s) l (𝓝 (μ s))) :
    μ ∈ effectiveSet S := fun X hX ↦
  (lintegral_le_liminf_lintegral_of_tendsto_measure hX.measurable h).trans
    (liminf_le_of_frequently_le (hμs.mono fun _ hi ↦ hi X hX).frequently)

/-- A measurable set that is null for every member of `S` is null for every member of the
effective null of `S`. -/
theorem measure_eq_zero_of_mem_effectiveSet (hμ : μ ∈ effectiveSet S) {s : Set Ω}
    (hs : MeasurableSet s) (hS : ∀ P ∈ S, P s = 0) : μ s = 0 := by
  classical
  -- The function equal to `∞` on `s` and to `1` elsewhere is an e-variable for `S`.
  have hX : IsEVar (s.piecewise (fun _ ↦ ∞) 1) S :=
    (isEVar_one S).congr (measurable_const.piecewise hs measurable_const) fun P hP ↦ by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hS P hP)] with ω hω
      simp [hω]
  have h : ∞ * μ s ≤ 1 := by
    rw [← lintegral_indicator_const hs]
    refine (lintegral_mono fun ω ↦ ?_).trans (hμ _ hX)
    by_cases hω : ω ∈ s <;> simp [hω]
  by_contra h_ne
  simp [ENNReal.top_mul h_ne] at h

/-- If every member of `S` is absolutely continuous with respect to a measure `ν`, so is every
member of the effective null of `S`. -/
theorem absolutelyContinuous_of_mem_effectiveSet (hμ : μ ∈ effectiveSet S)
    (hS : ∀ P ∈ S, P ≪ ν) : μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hνs ↦ ?_
  exact measure_eq_zero_of_mem_effectiveSet hμ hs fun P hP ↦ hS P hP hνs

/-- The e-variables for the probability measures of the effective null of `S` are e-variables
for `S`. -/
theorem IsEVar.effectiveSet_inter {X : Ω → ℝ≥0∞} (hX : IsEVar X S) :
    IsEVar X (effectiveSet S ∩ {μ | IsProbabilityMeasure μ}) :=
  .of_lintegral_le_one (S := effectiveSet S ∩ {μ | IsProbabilityMeasure μ}) (fun _ hμ ↦ hμ.2)
    hX.measurable fun _ hμ ↦ hμ.1 X hX

/-- A null of probability measures and the probability measures of its effective null have the
same e-variables. -/
theorem isEVar_effectiveSet_inter_iff (hS : ∀ P ∈ S, IsProbabilityMeasure P) {X : Ω → ℝ≥0∞} :
    IsEVar X (effectiveSet S ∩ {μ | IsProbabilityMeasure μ}) ↔ IsEVar X S := by
  refine ⟨fun hX ↦ hX.anti_set fun P hP ↦ ?_, IsEVar.effectiveSet_inter⟩
  exact ⟨subset_effectiveSet (fun P hP ↦ (hS P hP).measure_univ.le) hP, hS P hP⟩

/-- A null of probability measures and the probability measures of its effective null have the
same effective null. -/
theorem effectiveSet_effectiveSet_inter (hS : ∀ P ∈ S, IsProbabilityMeasure P) :
    effectiveSet (effectiveSet S ∩ {μ | IsProbabilityMeasure μ}) = effectiveSet S := by
  ext μ
  simp only [mem_effectiveSet_iff, isEVar_effectiveSet_inter_iff hS]

/-- A measure `Q` is outside the effective null of a null `S` of probability measures exactly
when, for some level `α ∈ (0, 1)`, some level-`α` test `φ` for `S` (a measurable function with
values in `[0, 1]` and expectation at most `α` under every member of `S`) has expectation larger
than `α` under `Q` [RW, Theorem 6.10]. -/
theorem exists_test_iff_notMem_effectiveSet (hS : ∀ P ∈ S, IsProbabilityMeasure P) :
    (∃ α : ℝ≥0∞, 0 < α ∧ α < 1 ∧ ∃ φ : Ω → ℝ≥0∞, Measurable φ ∧ φ ≤ 1 ∧
      (∀ P ∈ S, ∫⁻ ω, φ ω ∂P ≤ α) ∧ α < ∫⁻ ω, φ ω ∂Q) ↔ Q ∉ effectiveSet S := by
  constructor
  · rintro ⟨α, hα0, hα1, φ, hφ, -, hφS, hφQ⟩ hQ
    -- `α⁻¹ * φ` is an e-variable for `S`, so its expectation under `Q` is at most `1`.
    have hX : IsEVar (fun ω ↦ α⁻¹ * φ ω) S := by
      refine .of_lintegral_le_one hS (measurable_const.mul hφ) fun P hP ↦ ?_
      rw [lintegral_const_mul _ hφ]
      exact ENNReal.inv_mul_le_iff hα0.ne' (hα1.trans ENNReal.one_lt_top).ne |>.mpr <|
        by simpa using hφS P hP
    have h := hQ _ hX
    rw [lintegral_const_mul _ hφ,
      ENNReal.inv_mul_le_iff hα0.ne' (hα1.trans ENNReal.one_lt_top).ne, mul_one] at h
    exact (h.trans_lt hφQ).false
  · -- An e-variable with expectation larger than `1` under `Q`, truncated at a large level `N`
    -- and divided by `N`, is a level-`N⁻¹` test with power larger than `N⁻¹` under `Q`.
    intro hQ
    obtain ⟨X, hX, hXQ⟩ : ∃ X, IsEVar X S ∧ 1 < ∫⁻ ω, X ω ∂Q := by
      simpa [mem_effectiveSet_iff] using hQ
    -- By monotone convergence, the truncations `min X N` have expectation larger than `1` under
    -- `Q` from some level `N ≥ 2` on.
    have hXm := hX.measurable
    have h_tendsto : Tendsto (fun N : ℕ ↦ ∫⁻ ω, min (X ω) N ∂Q) atTop (𝓝 (∫⁻ ω, X ω ∂Q)) := by
      refine lintegral_tendsto_of_tendsto_of_monotone (fun N ↦ by fun_prop) (.of_forall
        fun ω N M hNM ↦ min_le_min_left _ (by exact_mod_cast hNM)) (.of_forall fun ω ↦ ?_)
      simpa using (tendsto_const_nhds (x := X ω)).min ENNReal.tendsto_nat_nhds_top
    obtain ⟨N, hNQ, hN2⟩ := ((h_tendsto.eventually (lt_mem_nhds hXQ)).and
      (eventually_ge_atTop 2)).exists
    have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have hNtop : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
    refine ⟨(N : ℝ≥0∞)⁻¹, ENNReal.inv_pos.mpr hNtop, ENNReal.inv_lt_one.mpr
      (by exact_mod_cast (by omega : 1 < N)), fun ω ↦ (N : ℝ≥0∞)⁻¹ * min (X ω) N, by fun_prop,
      fun ω ↦ ?_, fun P hP ↦ ?_, ?_⟩
    · calc (N : ℝ≥0∞)⁻¹ * min (X ω) N ≤ (N : ℝ≥0∞)⁻¹ * N := by gcongr; exact min_le_right _ _
      _ = 1 := ENNReal.inv_mul_cancel hN0 hNtop
    · have := hS P hP
      rw [lintegral_const_mul _ (by fun_prop)]
      calc (N : ℝ≥0∞)⁻¹ * ∫⁻ ω, min (X ω) N ∂P ≤ (N : ℝ≥0∞)⁻¹ * ∫⁻ ω, X ω ∂P := by
            gcongr with ω; exact min_le_left _ _
      _ ≤ (N : ℝ≥0∞)⁻¹ * 1 := by
            gcongr; simpa using hX.lintegral_le_measure_univ P hP
      _ = (N : ℝ≥0∞)⁻¹ := mul_one _
    · rw [lintegral_const_mul _ (by fun_prop)]
      calc (N : ℝ≥0∞)⁻¹ = (N : ℝ≥0∞)⁻¹ * 1 := (mul_one _).symm
      _ < (N : ℝ≥0∞)⁻¹ * ∫⁻ ω, min (X ω) N ∂Q :=
            ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr hNtop) (ENNReal.inv_ne_top.mpr hN0)
              hNQ

end ProbabilityTheory
