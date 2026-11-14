/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.PVariable
public import LMLExplore.Topology.Instances.ENNReal.Lemmas

/-!
# Post-hoc validity

A family of tests `φ : ℝ≥0∞ → Ω → ℝ≥0∞`, indexed by the levels `α ∈ (0, 1)`, is **post-hoc valid**
for a null `S` when `∫⁻ ω, ⨆ α ∈ Ioo 0 1, φ α ω / α ∂P ≤ 1` for every `P ∈ S`. A test of
level `α` controls `∫⁻ φ α / α ≤ 1` at one level fixed in advance; post-hoc validity controls it
for a level chosen after seeing the data: `∫⁻ ω, φ (ℓ ω) ω / ℓ ω ∂P ≤ 1` for every random level
`ℓ`, so that the statistician may report the smallest level at which the data reject without
inflating the type I error in this ratio sense. This file proves that for families of measurable
tests nondecreasing in the level the two forms are equivalent, and that post-hoc validity is testing
with an e-variable:

* the tests `min (α * E) 1` and `𝟙{α⁻¹ ≤ E}` of an e-variable `E` are post-hoc valid;
* conversely, a post-hoc valid family of `[0, 1]`-valued tests nondecreasing in the level is
  dominated by `min (α * E) 1` for the e-variable `E = ⨆ α ∈ Ioo 0 1, φ α / α`;
* a p-variable `p` is post-hoc, in the sense that its tests `𝟙{p ≤ α}` are post-hoc valid,
  exactly when `p⁻¹`, truncated to `0` on `{1 ≤ p}`, is an e-variable.

For a family nondecreasing in the level, the supremum over the levels `Ioo 0 1` is the supremum
over a countable dense set of levels (`ENNReal.biSup_Ioo_div_eq_biSup_inter_of_dense`), so it is
measurable as soon as each test is, and no measurable selection theorem is needed.

## Main definitions

* `ProbabilityTheory.IsPostHocValid φ S`: the family of tests `φ` is post-hoc valid for `S`.

## Main statements

* `ProbabilityTheory.IsPostHocValid.lintegral_le`: each test `φ α` of a post-hoc valid family has
  level `α`.
* `ProbabilityTheory.isPostHocValid_iff_forall_lintegral_div_le_one`: for a family of measurable
  tests nondecreasing in the level, post-hoc validity is validity at every measurable random
  level.
* `ProbabilityTheory.IsEVar.isPostHocValid_min_mul`,
  `ProbabilityTheory.IsEVar.isPostHocValid_indicator`:
  the tests of an e-variable are post-hoc valid.
* `ProbabilityTheory.isPostHocValid_iff_isEVar_iSup`,
  `ProbabilityTheory.isPostHocValid_iff_exists_isEVar`: post-hoc validity of a family
  nondecreasing in the level is the e-variable property of `⨆ α ∈ Ioo 0 1, φ α / α`, and a family of
  `[0, 1]`-valued tests is post-hoc valid exactly when it is dominated by the tests
  `min (α * E) 1` of an e-variable `E`.
* `ProbabilityTheory.isPostHocValid_indicator_iff_isEVar`: the tests `𝟙{p ≤ α}` of a statistic `p`
  are post-hoc valid exactly when `p⁻¹`, truncated to `0` on `{1 ≤ p}`, is an e-variable, and
  `ProbabilityTheory.isPVar_of_isPostHocValid_indicator`: such a `p` is a p-variable.

## References

* A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6: Definition 4.1 and Propositions 4.3–4.4.
* N. W. Koning, *Post-hoc α hypothesis testing and the post-hoc p-value*, arXiv:2312.08040
  (2023): Theorem 2.
* P. D. Grünwald, *Beyond Neyman–Pearson: E-values enable hypothesis testing with a data-driven
  alpha*, Proc. Natl. Acad. Sci. USA 121 (2024): Proposition 1.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S T : Set (Measure Ω)}
  {φ ψ : ℝ≥0∞ → Ω → ℝ≥0∞} {E p : Ω → ℝ≥0∞} {P : Measure Ω}

/-- A family of tests `φ`, indexed by the levels `α ∈ (0, 1)`, is **post-hoc valid** for the null
`S` when `∫⁻ ω, ⨆ α ∈ Ioo 0 1, φ α ω / α ∂P ≤ 1` for every `P ∈ S`. The tests are meant to be
`[0, 1]`-valued, but the definition does not ask it. -/
structure IsPostHocValid (φ : ℝ≥0∞ → Ω → ℝ≥0∞) (S : Set (Measure Ω)) : Prop where
  lintegral_iSup_div_le_one : ∀ P ∈ S, ∫⁻ ω, ⨆ α ∈ Ioo (0 : ℝ≥0∞) 1, φ α ω / α ∂P ≤ 1

theorem IsPostHocValid.anti_set (hST : S ⊆ T) (h : IsPostHocValid φ T) :
    IsPostHocValid φ S where
  lintegral_iSup_div_le_one P hP := h.lintegral_iSup_div_le_one P (hST hP)

/-- A family of tests almost surely below a post-hoc valid family, under every member of the null,
is post-hoc valid. -/
theorem IsPostHocValid.mono (h : IsPostHocValid φ S)
    (hψφ : ∀ P ∈ S, ∀ᵐ ω ∂P, ∀ α ∈ Ioo (0 : ℝ≥0∞) 1, ψ α ω ≤ φ α ω) :
    IsPostHocValid ψ S where
  lintegral_iSup_div_le_one P hP := by
    refine le_trans (lintegral_mono_ae ?_) (h.lintegral_iSup_div_le_one P hP)
    filter_upwards [hψφ P hP] with ω hω
    exact iSup₂_mono fun α hα ↦ ENNReal.div_le_div_right (hω α hα) α

/-- Validity at a random level: for a post-hoc valid family and any level `ℓ ω ∈ (0, 1)` chosen
from the data, measurable or not, `∫⁻ ω, φ (ℓ ω) ω / ℓ ω ∂P ≤ 1`. -/
theorem IsPostHocValid.lintegral_div_le_one (h : IsPostHocValid φ S) (hP : P ∈ S)
    {ℓ : Ω → ℝ≥0∞} (hℓ : ∀ ω, ℓ ω ∈ Ioo 0 1) :
    ∫⁻ ω, φ (ℓ ω) ω / ℓ ω ∂P ≤ 1 :=
  le_trans (lintegral_mono fun ω ↦ le_iSup₂ (f := fun α _ ↦ φ α ω / α) (ℓ ω) (hℓ ω))
    (h.lintegral_iSup_div_le_one P hP)

/-- Each test `φ α` of a post-hoc valid family has level `α`. -/
theorem IsPostHocValid.lintegral_le (h : IsPostHocValid φ S) (hP : P ∈ S) {α : ℝ≥0∞}
    (hα : α ∈ Ioo 0 1) :
    ∫⁻ ω, φ α ω ∂P ≤ α := by
  have h_le : ∫⁻ ω, φ α ω / α ∂P ≤ 1 := h.lintegral_div_le_one hP (ℓ := fun _ ↦ α) fun _ ↦ hα
  calc ∫⁻ ω, φ α ω ∂P = (∫⁻ ω, φ α ω / α ∂P) * α := by
        rw [← lintegral_mul_const' _ _ (ne_top_of_lt hα.2)]
        simp_rw [ENNReal.div_mul_cancel hα.1.ne' (ne_top_of_lt hα.2)]
  _ ≤ 1 * α := by gcongr
  _ = α := one_mul α

/-! ### Reduction to countably many levels -/

/-- For a family nondecreasing in the level, the supremum over the levels `Ioo 0 1` is a supremum
over a countable set of levels. -/
private lemma exists_countable_iSup_div_eq
    (hmono : ∀ ω, MonotoneOn (φ · ω) (Ioo 0 1)) :
    ∃ D ⊆ Ioo (0 : ℝ≥0∞) 1, D.Countable ∧
      ∀ ω, ⨆ α ∈ Ioo (0 : ℝ≥0∞) 1, φ α ω / α = ⨆ α ∈ D, φ α ω / α := by
  obtain ⟨D, hD_count, hD_dense⟩ := TopologicalSpace.exists_countable_dense ℝ≥0∞
  exact ⟨Ioo 0 1 ∩ D, inter_subset_left, hD_count.mono inter_subset_right,
    fun ω ↦ ENNReal.biSup_Ioo_div_eq_biSup_inter_of_dense hD_dense (hmono ω)⟩

/-- For a family of measurable tests nondecreasing in the level, `⨆ α ∈ Ioo 0 1, φ α / α` is
measurable. -/
theorem measurable_iSup_div (hφ : ∀ α ∈ Ioo (0 : ℝ≥0∞) 1, Measurable (φ α))
    (hmono : ∀ ω, MonotoneOn (φ · ω) (Ioo 0 1)) :
    Measurable fun ω ↦ ⨆ α ∈ Ioo (0 : ℝ≥0∞) 1, φ α ω / α := by
  obtain ⟨D, hD_sub, hD_count, hD_eq⟩ := exists_countable_iSup_div_eq hmono
  simp_rw [hD_eq]
  exact .biSup D hD_count fun α hα ↦ (hφ α (hD_sub hα)).div_const α

/-- Over finitely many levels `a i`, the largest ratio `φ (a i) ω / a i` is attained at a
measurable random level, whose ratio is measurable. -/
private lemma exists_measurable_iSup_div_le {ι : Type*} (hφ : ∀ α ∈ Ioo (0 : ℝ≥0∞) 1,
    Measurable (φ α)) {a : ι → ℝ≥0∞} (ha : ∀ i, a i ∈ Ioo 0 1) (t : Finset ι) :
    ∃ ℓ : Ω → ℝ≥0∞, Measurable ℓ ∧ (∀ ω, ℓ ω ∈ Ioo 0 1) ∧
      Measurable (fun ω ↦ φ (ℓ ω) ω / ℓ ω) ∧
      ∀ ω, ⨆ i ∈ t, φ (a i) ω / a i ≤ φ (ℓ ω) ω / ℓ ω := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h_half : (2⁻¹ : ℝ≥0∞) ∈ Ioo 0 1 :=
      ⟨ENNReal.inv_pos.2 ENNReal.ofNat_ne_top, ENNReal.inv_lt_one.2 ENNReal.one_lt_two⟩
    exact ⟨fun _ ↦ 2⁻¹, measurable_const, fun _ ↦ h_half, (hφ _ h_half).div_const _,
      fun _ ↦ by simp⟩
  | insert i t _ ih =>
    obtain ⟨ℓ, hℓ, hℓ_mem, hℓ_ratio, hℓ_le⟩ := ih
    -- keep `ℓ` where its ratio is at least the one of the new level `a i`, else switch to `a i`
    set s := {ω | φ (a i) ω / a i ≤ φ (ℓ ω) ω / ℓ ω}
    have hs : MeasurableSet s := measurableSet_le ((hφ _ (ha i)).div_const _) hℓ_ratio
    have h_ratio : (fun ω ↦ φ (s.piecewise ℓ (fun _ ↦ a i) ω) ω / s.piecewise ℓ (fun _ ↦ a i) ω)
        = s.piecewise (fun ω ↦ φ (ℓ ω) ω / ℓ ω) (fun ω ↦ φ (a i) ω / a i) := by
      ext ω
      by_cases hω : ω ∈ s <;> simp [hω]
    refine ⟨s.piecewise ℓ (fun _ ↦ a i), hℓ.piecewise hs measurable_const,
      fun ω ↦ ?_, ?_, fun ω ↦ ?_⟩
    · by_cases hω : ω ∈ s <;> simp [hω, hℓ_mem ω, ha i]
    · rw [h_ratio]
      exact hℓ_ratio.piecewise hs ((hφ _ (ha i)).div_const _)
    · rw [Finset.iSup_insert, congrFun h_ratio ω]
      by_cases hω : ω ∈ s
      · rw [piecewise_eq_of_mem _ _ _ hω]
        exact sup_le hω (hℓ_le ω)
      · simp only [hω, not_false_eq_true, piecewise_eq_of_notMem, sup_le_iff, le_refl, true_and]
        exact (hℓ_le ω).trans (not_le.1 hω).le

/-- **Post-hoc validity at random levels.** For a family of measurable tests nondecreasing in the
level, post-hoc validity is validity at every measurable random level `ℓ : Ω → (0, 1)`. -/
theorem isPostHocValid_iff_forall_lintegral_div_le_one
    (hφ : ∀ α ∈ Ioo (0 : ℝ≥0∞) 1, Measurable (φ α))
    (hmono : ∀ ω, MonotoneOn (φ · ω) (Ioo 0 1)) :
    IsPostHocValid φ S ↔ ∀ P ∈ S, ∀ ℓ : Ω → ℝ≥0∞, Measurable ℓ → (∀ ω, ℓ ω ∈ Ioo 0 1) →
      ∫⁻ ω, φ (ℓ ω) ω / ℓ ω ∂P ≤ 1 := by
  refine ⟨fun h P hP ℓ _ hℓ ↦ h.lintegral_div_le_one hP hℓ, fun h ↦ ⟨fun P hP ↦ ?_⟩⟩
  obtain ⟨D, hD_sub, hD_count, hD_eq⟩ := exists_countable_iSup_div_eq hmono
  have := hD_count.to_subtype
  -- the supremum over `D` is the increasing limit of the suprema over its finite subsets
  have h_eq (ω : Ω) : ⨆ α ∈ Ioo (0 : ℝ≥0∞) 1, φ α ω / α =
      ⨆ t : Finset D, ⨆ α ∈ t, φ (α : ℝ≥0∞) ω / α := by
    rw [hD_eq, ← iSup_subtype'', iSup_eq_iSup_finset]
  simp_rw [h_eq]
  rw [lintegral_iSup_directed]
  · refine iSup_le fun t ↦ ?_
    obtain ⟨ℓ, hℓ, hℓ_mem, -, hℓ_le⟩ :=
      exists_measurable_iSup_div_le hφ (a := fun α : D ↦ (α : ℝ≥0∞)) (fun α ↦ hD_sub α.2) t
    exact (lintegral_mono hℓ_le).trans (h P hP ℓ hℓ hℓ_mem)
  · refine fun t ↦ (Measurable.biSup (t : Set D) t.countable_toSet fun α _ ↦ ?_).aemeasurable
    exact (hφ α (hD_sub α.2)).div_const _
  · exact Monotone.directed_le fun t₁ t₂ h ω ↦ biSup_mono fun _ hα ↦ Finset.mem_of_subset h hα

/-! ### Post-hoc validity and e-variables -/

/-- The tests `min (α * E) 1` of an e-variable `E` are post-hoc valid. -/
theorem IsEVar.isPostHocValid_min_mul (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hE : IsEVar E S) :
    IsPostHocValid (fun α ω ↦ min (α * E ω) 1) S where
  lintegral_iSup_div_le_one P hP := by
    have := hS P hP
    refine le_trans (lintegral_mono fun ω ↦ iSup₂_le fun α hα ↦ ?_) (hE.lintegral_le_one hP)
    calc min (α * E ω) 1 / α
    _ ≤ E ω * α / α := by
      rw [mul_comm]
      gcongr
      exact min_le_left _ _
    _ = E ω := ENNReal.mul_div_cancel_right hα.1.ne' (ne_top_of_lt hα.2)

/-- The tests `𝟙{α⁻¹ ≤ E}` that reject when an e-variable `E` reaches `α⁻¹` are post-hoc
valid. -/
theorem IsEVar.isPostHocValid_indicator (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hE : IsEVar E S) :
    IsPostHocValid (fun α ↦ {ω | α⁻¹ ≤ E ω}.indicator 1) S := by
  refine (hE.isPostHocValid_min_mul hS).mono fun P _ ↦ ae_of_all _ fun ω α hα ↦ ?_
  by_cases hαE : α⁻¹ ≤ E ω
  · rw [indicator_of_mem (by exact hαE), Pi.one_apply, le_min_iff]
    refine ⟨?_, le_rfl⟩
    calc 1 = α * α⁻¹ := (ENNReal.mul_inv_cancel hα.1.ne' (ne_top_of_lt hα.2)).symm
    _ ≤ α * E ω := by gcongr
  · simp [hαE]

/-- A `[0, 1]`-valued test `φ α` is at most `min (α * E) 1` for `E = ⨆ β ∈ Ioo 0 1, φ β / β`. -/
theorem le_min_mul_iSup_div {α : ℝ≥0∞} (hα : α ∈ Ioo 0 1) {ω : Ω} (hφ1 : φ α ω ≤ 1) :
    φ α ω ≤ min (α * ⨆ β ∈ Ioo (0 : ℝ≥0∞) 1, φ β ω / β) 1 := by
  refine le_min ?_ hφ1
  calc φ α ω = α * (φ α ω / α) := (ENNReal.mul_div_cancel hα.1.ne' (ne_top_of_lt hα.2)).symm
  _ ≤ α * ⨆ β ∈ Ioo (0 : ℝ≥0∞) 1, φ β ω / β := by
    gcongr
    exact le_iSup₂ (f := fun β _ ↦ φ β ω / β) α hα

/-- For a family of measurable tests nondecreasing in the level and a null of probability
measures, post-hoc validity says that `⨆ α ∈ Ioo 0 1, φ α / α` is an e-variable. -/
theorem isPostHocValid_iff_isEVar_iSup (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hφ : ∀ α ∈ Ioo (0 : ℝ≥0∞) 1, Measurable (φ α))
    (hmono : ∀ ω, MonotoneOn (φ · ω) (Ioo 0 1)) :
    IsPostHocValid φ S ↔ IsEVar (fun ω ↦ ⨆ α ∈ Ioo (0 : ℝ≥0∞) 1, φ α ω / α) S := by
  rw [isEVar_iff_lintegral_le_one hS]
  exact ⟨fun h ↦ ⟨measurable_iSup_div hφ hmono, h.lintegral_iSup_div_le_one⟩, fun h ↦ ⟨h.2⟩⟩

/-- **Post-hoc validity is testing with an e-variable.** For a null of probability measures, a
family of measurable `[0, 1]`-valued tests nondecreasing in the level is post-hoc valid exactly
when it is dominated by the tests `min (α * E) 1` of an e-variable `E`; one can take
`E = ⨆ α ∈ Ioo 0 1, φ α / α`. -/
theorem isPostHocValid_iff_exists_isEVar (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hφ : ∀ α ∈ Ioo (0 : ℝ≥0∞) 1, Measurable (φ α))
    (hmono : ∀ ω, MonotoneOn (φ · ω) (Ioo 0 1)) (hφ1 : ∀ α ∈ Ioo (0 : ℝ≥0∞) 1, ∀ ω, φ α ω ≤ 1) :
    IsPostHocValid φ S ↔
      ∃ E, IsEVar E S ∧ ∀ α ∈ Ioo (0 : ℝ≥0∞) 1, ∀ ω, φ α ω ≤ min (α * E ω) 1 := by
  refine ⟨fun h ↦ ⟨_, (isPostHocValid_iff_isEVar_iSup hS hφ hmono).1 h,
    fun α hα ω ↦ le_min_mul_iSup_div hα (hφ1 α hα ω)⟩, fun ⟨E, hE, hφE⟩ ↦ ?_⟩
  exact (hE.isPostHocValid_min_mul hS).mono fun P _ ↦ ae_of_all _ fun ω α hα ↦ hφE α hα ω

/-! ### Post-hoc p-variables -/

/-- The post-hoc supremum of the tests `𝟙{p ≤ α}` of a statistic `p` is `p⁻¹`, truncated to `0`
on `{1 ≤ p}`. -/
theorem iSup_indicator_le_div_eq_indicator_inv (p : Ω → ℝ≥0∞) (ω : Ω) :
    ⨆ α ∈ Ioo (0 : ℝ≥0∞) 1, {ω | p ω ≤ α}.indicator 1 ω / α =
      {ω | p ω < 1}.indicator (fun ω ↦ (p ω)⁻¹) ω := by
  by_cases hp1 : p ω < 1
  · rw [indicator_of_mem (by exact hp1)]
    refine le_antisymm (iSup₂_le fun α hα ↦ ?_) (le_of_forall_lt fun r hr ↦ ?_)
    · by_cases hpα : p ω ≤ α
      · rw [indicator_of_mem (by exact hpα), Pi.one_apply, one_div]
        exact ENNReal.inv_le_inv.2 hpα
      · simp [hpα]
    -- a level `α` slightly above `p ω` has `r < α⁻¹`
    obtain ⟨α, hpα, hα⟩ := exists_between (lt_min (ENNReal.lt_inv_iff_lt_inv.1 hr) hp1)
    have hα_mem : α ∈ Ioo (0 : ℝ≥0∞) 1 := ⟨zero_le.trans_lt hpα, hα.trans_le (min_le_right _ _)⟩
    calc r < α⁻¹ := ENNReal.lt_inv_iff_lt_inv.1 (hα.trans_le (min_le_left _ _))
    _ = {ω | p ω ≤ α}.indicator 1 ω / α := by
      rw [indicator_of_mem (by exact hpα.le), Pi.one_apply, one_div]
    _ ≤ _ := le_iSup₂ (f := fun β _ ↦ {ω | p ω ≤ β}.indicator 1 ω / β) α hα_mem
  · rw [indicator_of_notMem (by exact hp1)]
    refine le_antisymm (iSup₂_le fun α hα ↦ ?_) zero_le
    rw [indicator_of_notMem (by exact fun hpα ↦ hp1 (lt_of_le_of_lt hpα hα.2)), ENNReal.zero_div]

/-- **Post-hoc p-variables.** For a null of probability measures, the tests `𝟙{p ≤ α}` of a
measurable statistic `p` are post-hoc valid exactly when `p⁻¹`, truncated to `0` on `{1 ≤ p}`, is
an e-variable. -/
theorem isPostHocValid_indicator_iff_isEVar (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hp : Measurable p) :
    IsPostHocValid (fun α ↦ {ω | p ω ≤ α}.indicator 1) S ↔
      IsEVar ({ω | p ω < 1}.indicator fun ω ↦ (p ω)⁻¹) S := by
  -- the tests are measurable and nondecreasing in the level, and their post-hoc supremum is the
  -- truncated inverse of `p`
  have hmono (ω : Ω) : MonotoneOn (fun α ↦ {ω | p ω ≤ α}.indicator (1 : Ω → ℝ≥0∞) ω) (Ioo 0 1) :=
    fun _ _ _ _ hαβ ↦
      indicator_le_indicator_of_subset (fun _ h ↦ le_trans h hαβ) (fun _ ↦ zero_le) ω
  rw [isPostHocValid_iff_isEVar_iSup hS
    (fun _ _ ↦ measurable_one.indicator (measurableSet_le hp measurable_const)) hmono,
    funext (iSup_indicator_le_div_eq_indicator_inv p)]

/-- A post-hoc p-variable is a p-variable: if the tests `𝟙{p ≤ α}` of a measurable `p` are
post-hoc valid for a null of probability measures, then `p` is a p-variable. -/
theorem isPVar_of_isPostHocValid_indicator (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hp : Measurable p) (h : IsPostHocValid (fun α ↦ {ω | p ω ≤ α}.indicator 1) S) :
    IsPVar p S where
  measurable := hp
  measure_le_le P hP α := by
    have := hS P hP
    -- `P {p ≤ α} ≤ ε` for every `ε > α`: at the level `ε` if `ε < 1`, and trivially otherwise
    refine le_of_forall_gt_imp_ge_of_dense fun ε hαε ↦ ?_
    rcases lt_or_ge ε 1 with hε1 | hε1
    · have hε : ε ∈ Ioo (0 : ℝ≥0∞) 1 := ⟨zero_le.trans_lt hαε, hε1⟩
      calc P {ω | p ω ≤ α} ≤ P {ω | p ω ≤ ε} := measure_mono fun ω hω ↦ le_trans hω hαε.le
      _ = ∫⁻ ω, {ω | p ω ≤ ε}.indicator 1 ω ∂P :=
        (lintegral_indicator_one (measurableSet_le hp measurable_const)).symm
      _ ≤ ε := h.lintegral_le hP hε
    · exact prob_le_one.trans hε1

end ProbabilityTheory
