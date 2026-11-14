/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Statlib.EValues.RIPr
public import LMLExplore.MeasureTheory.Integral.Lebesgue.Setwise

/-!
# The effective null

The effective null of a set of measures `S` is Statlib's `effectiveSet S`: the measures `μ` under
which every e-variable for `S` has `∫⁻ X ∂μ ≤ 1`. It is the set of measures against which `S`
cannot be distinguished by e-variables, and the duality
`maxUtility P S logUtility = ⨅ μ ∈ effectiveSet S, klIntegral P μ` of Statlib minimizes over it.
This file describes its structure, for any set of measures `S` on any measurable space, with no
dominating measure:

* it contains the members of `S` of mass at most `1`, and every mixture `κ ∘ₘ π` of members of
  the effective null over a measure `π` of mass at most `1`, hence, when the members of `S` have
  mass at most `1`, every such mixture of members of `S` and the convex hull of `S`;
* it is solid (`μ ≤ ν ∈ effectiveSet S` gives `μ ∈ effectiveSet S`) and closed under setwise
  convergence;
* when the members of `S` are probability measures, `S` and the probability measures of
  `effectiveSet S` have the same e-variables, so that the effective null of the latter is
  `effectiveSet S` again;
* for a null of probability measures, the effective null is the set of alternatives against which
  no level-`α` test for `S` has power larger than `α` [RW, Theorem 6.10]: a measure `Q` lies
  outside it exactly when some test of level `α ∈ (0, 1)` for `S` has `Q`-power larger than `α`.

## Main statements

* `ProbabilityTheory.comp_mem_effectiveSet`, `ProbabilityTheory.comp_mem_effectiveSet_of_mem`:
  mixtures.
* `ProbabilityTheory.convex_effectiveSet`, `ProbabilityTheory.convexHull_subset_effectiveSet`.
* `ProbabilityTheory.mem_effectiveSet_of_le`: solidity.
* `ProbabilityTheory.mem_effectiveSet_of_frequently_of_tendsto`: closure under setwise
  convergence.
* `ProbabilityTheory.isEVar_effectiveSet_inter_iff`: the same e-variables.
* `ProbabilityTheory.mem_effectiveSet_iff_forall_bounded`: bounded e-variables suffice to test
  membership.
* `ProbabilityTheory.exists_powered_test_iff`: powered tests exist exactly outside the effective
  null [RW, Theorem 6.10].

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, arXiv:2410.23614v6, §6.3.1,
  Theorem 6.10, Fact 3.6.
* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), Definition 3.1.
-/

public section

open Filter Set Topology
open scoped ENNReal

namespace ProbabilityTheory

open MeasureTheory

variable {𝓧 Θ ι : Type*} {m𝓧 : MeasurableSpace 𝓧} {mΘ : MeasurableSpace Θ}
  {S T : Set (Measure 𝓧)} {μ ν : Measure 𝓧}

/-- The effective null is monotone in the null. -/
lemma effectiveSet_mono (hST : S ⊆ T) : effectiveSet S ⊆ effectiveSet T :=
  fun _ hμ X hX ↦ hμ X (hX.anti_set hST)

/-- A member of `S` of mass at most `1` belongs to the effective null of `S`. -/
lemma mem_effectiveSet_of_mem (hμS : μ ∈ S) (hμ : μ .univ ≤ 1) : μ ∈ effectiveSet S :=
  fun _ hX ↦ (hX.lintegral_le_measure_univ μ hμS).trans hμ

/-- A member of `S` belongs to the effective null of `S` exactly when its mass is at most `1`. -/
lemma mem_effectiveSet_iff_of_mem (hμS : μ ∈ S) : μ ∈ effectiveSet S ↔ μ .univ ≤ 1 :=
  ⟨measure_univ_le_one_of_mem_effectiveSet, mem_effectiveSet_of_mem hμS⟩

/-- A null whose members have mass at most `1`, in particular a null of probability measures, is
contained in its effective null. -/
lemma subset_effectiveSet (hS : ∀ μ ∈ S, μ .univ ≤ 1) : S ⊆ effectiveSet S :=
  fun μ hμ ↦ mem_effectiveSet_of_mem hμ (hS μ hμ)

/-! ### Mixtures and convexity -/

/-- The effective null is closed under mixtures: for a measure `π` of mass at most `1` and a
kernel `κ` whose values lie `π`-almost surely in the effective null, `κ ∘ₘ π` lies in the effective
null. -/
lemma comp_mem_effectiveSet {π : Measure Θ} {κ : Kernel Θ 𝓧}
    (hκ : ∀ᵐ θ ∂π, κ θ ∈ effectiveSet S) (hπ : π .univ ≤ 1) :
    κ ∘ₘ π ∈ effectiveSet S := by
  intro X hX
  rw [Measure.lintegral_bind κ.aemeasurable hX.measurable.aemeasurable]
  calc ∫⁻ θ, ∫⁻ x, X x ∂κ θ ∂π
  _ ≤ ∫⁻ _, 1 ∂π := lintegral_mono_ae (hκ.mono fun θ hθ ↦ hθ X hX)
  _ ≤ 1 := by simpa using hπ

/-- Every mixture `κ ∘ₘ π` of members of `S` of mass at most `1` over a measure `π` of mass at
most `1`, in particular every mixture of a probability null over a probability measure, belongs to
the effective null of `S`. -/
lemma comp_mem_effectiveSet_of_mem (hS : ∀ μ ∈ S, μ .univ ≤ 1) {π : Measure Θ}
    {κ : Kernel Θ 𝓧} (hκ : ∀ᵐ θ ∂π, κ θ ∈ S) (hπ : π .univ ≤ 1) :
    κ ∘ₘ π ∈ effectiveSet S :=
  comp_mem_effectiveSet (hκ.mono fun _ hθ ↦ subset_effectiveSet hS hθ) hπ

/-- The effective null is convex. -/
lemma convex_effectiveSet (S : Set (Measure 𝓧)) : Convex ℝ≥0∞ (effectiveSet S) := by
  intro μ hμ ν hν a b _ _ hab X hX
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  calc a * ∫⁻ x, X x ∂μ + b * ∫⁻ x, X x ∂ν
  _ ≤ a * 1 + b * 1 := by gcongr; exacts [hμ X hX, hν X hX]
  _ = 1 := by rw [mul_one, mul_one, hab]

/-- The convex hull of a null whose members have mass at most `1` is contained in its effective
null. -/
lemma convexHull_subset_effectiveSet (hS : ∀ μ ∈ S, μ .univ ≤ 1) :
    convexHull ℝ≥0∞ S ⊆ effectiveSet S :=
  convexHull_min (subset_effectiveSet hS) (convex_effectiveSet S)

/-! ### Solidity and closedness -/

/-- The effective null is solid: a measure below a member of the effective null belongs to it. -/
lemma mem_effectiveSet_of_le (hμν : μ ≤ ν) (hν : ν ∈ effectiveSet S) : μ ∈ effectiveSet S :=
  fun X hX ↦ (lintegral_mono' hμν le_rfl).trans (hν X hX)

/-- The effective null is closed under setwise convergence: if `μs i s` tends to `μ s` along `l`
for every measurable set `s`, and `μs i` lies frequently along `l` in the effective null, then so
does `μ`. -/
lemma mem_effectiveSet_of_frequently_of_tendsto {l : Filter ι} {μs : ι → Measure 𝓧}
    (h : ∀ s, MeasurableSet s → Tendsto (fun i ↦ μs i s) l (𝓝 (μ s)))
    (hμs : ∃ᶠ i in l, μs i ∈ effectiveSet S) :
    μ ∈ effectiveSet S :=
  fun X hX ↦ lintegral_le_of_frequently_of_tendsto_measure h (hμs.mono fun _ hi ↦ hi X hX)

/-- The effective null is closed under setwise convergence: if `μs i s` tends to `μ s` along a
nontrivial filter `l` for every measurable set `s`, and `μs i` lies eventually along `l` in the
effective null, then so does `μ`. -/
lemma mem_effectiveSet_of_tendsto {l : Filter ι} [l.NeBot] {μs : ι → Measure 𝓧}
    (h : ∀ s, MeasurableSet s → Tendsto (fun i ↦ μs i s) l (𝓝 (μ s)))
    (hμs : ∀ᶠ i in l, μs i ∈ effectiveSet S) :
    μ ∈ effectiveSet S :=
  mem_effectiveSet_of_frequently_of_tendsto h hμs.frequently

/-! ### The e-variables of the effective null -/

/-- A null of probability measures and the probability measures of its effective null have the
same e-variables. -/
lemma isEVar_effectiveSet_inter_iff (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) {X : 𝓧 → ℝ≥0∞} :
    IsEVar X (effectiveSet S ∩ {μ | IsProbabilityMeasure μ}) ↔ IsEVar X S := by
  refine ⟨fun hX ↦ hX.anti_set (S := S) fun μ hμ ↦ ?_, fun hX ↦ ?_⟩
  · have := hS μ hμ
    exact ⟨mem_effectiveSet_of_mem hμ prob_le_one, this⟩
  · exact IsEVar.of_lintegral_le_one (S := effectiveSet S ∩ {μ | IsProbabilityMeasure μ})
      (fun μ hμ ↦ hμ.2) hX.measurable fun μ hμ ↦ hμ.1 X hX

/-- The effective null of the probability measures of the effective null of a null of probability
measures is the effective null itself. -/
lemma effectiveSet_effectiveSet_inter (hS : ∀ μ ∈ S, IsProbabilityMeasure μ) :
    effectiveSet (effectiveSet S ∩ {μ | IsProbabilityMeasure μ}) = effectiveSet S := by
  ext μ
  simp only [mem_effectiveSet_iff, isEVar_effectiveSet_inter_iff hS]

/-- Membership in the effective null of a null of finite measures can be tested with bounded
e-variables only. -/
lemma mem_effectiveSet_iff_forall_bounded (hS : ∀ μ ∈ S, IsFiniteMeasure μ) :
    μ ∈ effectiveSet S ↔
      ∀ X : 𝓧 → ℝ≥0∞, IsEVar X S → ∀ C : ℝ≥0∞, C ≠ ∞ → (∀ x, X x ≤ C) → ∫⁻ x, X x ∂μ ≤ 1 := by
  refine ⟨fun hμ X hX _ _ _ ↦ hμ X hX, fun h X hX ↦ ?_⟩
  -- Truncate `X` at the integers: `X = ⨆ n, min (X x) n`, and the truncations are bounded
  -- e-variables.
  have hX_eq : ∀ x, X x = ⨆ n : ℕ, min (X x) n := fun x ↦ by
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hmeas : ∀ n : ℕ, Measurable fun x ↦ min (X x) n := fun n ↦ hX.measurable.min measurable_const
  rw [lintegral_congr hX_eq,
    lintegral_iSup hmeas fun m n hmn x ↦ min_le_min_left _ (mod_cast hmn)]
  exact iSup_le fun n ↦ h _ (hX.mono hS (hmeas n) fun x ↦ min_le_left _ _) n
    (ENNReal.natCast_ne_top n) fun x ↦ min_le_right _ _

/-! ### Tests and the effective null -/

/-- **Powered tests exist exactly outside the effective null** [RW, Theorem 6.10]. For a null of
probability measures `S` and a measure `Q`, some test `φ` (a measurable function with values in
`[0, 1]`) of level `α ∈ (0, 1)` for `S` has `Q`-power `∫⁻ φ ∂Q` larger than `α` exactly when `Q`
does not belong to the effective null of `S`. -/
theorem exists_powered_test_iff (hS : ∀ P ∈ S, IsProbabilityMeasure P) (Q : Measure 𝓧) :
    (∃ α : ℝ≥0∞, 0 < α ∧ α < 1 ∧ ∃ φ : 𝓧 → ℝ≥0∞, Measurable φ ∧ (∀ x, φ x ≤ 1) ∧
        (∀ P ∈ S, ∫⁻ x, φ x ∂P ≤ α) ∧ α < ∫⁻ x, φ x ∂Q) ↔
      Q ∉ effectiveSet S := by
  constructor
  · -- `φ / α` is an e-variable for `S` with `Q`-expectation larger than `1`.
    rintro ⟨α, hα0, hα1, φ, hφ, -, hφS, hφQ⟩ hQ
    have hα_top : α ≠ ∞ := (hα1.trans ENNReal.one_lt_top).ne
    have hE : IsEVar (fun x ↦ α⁻¹ * φ x) S := by
      refine .of_lintegral_le_one hS (hφ.const_mul _) fun P hP ↦ ?_
      rw [lintegral_const_mul _ hφ]
      calc α⁻¹ * ∫⁻ x, φ x ∂P
      _ ≤ α⁻¹ * α := by gcongr; exact hφS P hP
      _ = 1 := ENNReal.inv_mul_cancel hα0.ne' hα_top
    have hQ_le := hQ _ hE
    rw [lintegral_const_mul _ hφ] at hQ_le
    refine (ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr hα_top)
      (ENNReal.inv_ne_top.mpr hα0.ne') hφQ).not_ge ?_
    rwa [ENNReal.inv_mul_cancel hα0.ne' hα_top]
  · -- A bounded e-variable `X ≤ C` with `Q`-expectation larger than `1`, divided by
    -- `D = max C 2`, is a test of level `D⁻¹ < 1` [RW, Fact 3.6].
    intro hQ
    rw [mem_effectiveSet_iff_forall_bounded fun P hP ↦ have := hS P hP; inferInstance] at hQ
    push Not at hQ
    obtain ⟨X, hX, C, hC, hXC, hXQ⟩ := hQ
    set D := max C 2 with hD
    have hD_top : D ≠ ∞ := max_ne_top hC ENNReal.ofNat_ne_top
    have hD0 : D ≠ 0 := (two_ne_zero.bot_lt.trans_le (le_max_right C 2)).ne'
    have hφ : Measurable fun x ↦ D⁻¹ * X x := hX.measurable.const_mul _
    refine ⟨D⁻¹, ENNReal.inv_pos.mpr hD_top, ?_, fun x ↦ D⁻¹ * X x, hφ, fun x ↦ ?_,
      fun P hP ↦ ?_, ?_⟩
    · exact ENNReal.inv_lt_one.mpr (ENNReal.one_lt_two.trans_le (le_max_right C 2))
    · calc D⁻¹ * X x
      _ ≤ D⁻¹ * D := by gcongr; exact (hXC x).trans (le_max_left C 2)
      _ = 1 := ENNReal.inv_mul_cancel hD0 hD_top
    · have := hS P hP
      rw [lintegral_const_mul _ hX.measurable]
      calc D⁻¹ * ∫⁻ x, X x ∂P
      _ ≤ D⁻¹ * 1 := by gcongr; simpa using hX.lintegral_le_measure_univ P hP
      _ = D⁻¹ := mul_one _
    · rw [lintegral_const_mul _ hX.measurable]
      calc D⁻¹ = D⁻¹ * 1 := (mul_one _).symm
      _ < D⁻¹ * ∫⁻ x, X x ∂Q :=
        ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr hD_top)
          (ENNReal.inv_ne_top.mpr hD0) hXQ

end ProbabilityTheory
