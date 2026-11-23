/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Closed solid convex sets of nonnegative functions

Brannath and Schachermayer's bipolar theorem in `L⁰₊(μ)` [BS99] describes the sets of
nonnegative measurable functions that are polars: they are the sets that are convex, solid (a
measurable function below a member almost everywhere is a member) and closed under convergence in
`μ`-probability. This file develops that class of sets for `ℝ≥0∞`-valued functions and proves the
separation theorem behind the bipolar theorem: an almost everywhere finite measurable function
outside such a set is separated from it by one nonnegative weight `g`, with `∫⁻ f * g ∂μ ≤ 1` on
the set and `1 < ∫⁻ X * g ∂μ`.

Closedness is stated with almost everywhere limits of sequences, and only for almost everywhere
finite limits, the elements of `L⁰₊(μ)` (`MeasureTheory.IsAESeqClosed`). For a finite measure and
almost everywhere finite measurable members this is closedness under limits in `μ`-probability: a
sequence that converges in probability has an almost everywhere convergent subsequence, which
gives `MeasureTheory.IsAESeqClosed.mem_of_tendstoInMeasure`, and an almost everywhere convergent
sequence converges in probability. The almost everywhere form needs no metric on `ℝ≥0∞` and
depends only on the null sets of `μ`, so that statements extend from finite to s-finite measures
through `Measure.toFinite`.

## Main definitions

* `MeasureTheory.IsAESolid μ D`: a measurable function `μ`-almost everywhere below a member of `D`
  is a member.
* `MeasureTheory.IsAESeqClosed μ D`: a measurable, `μ`-almost everywhere finite, `μ`-almost
  everywhere limit of a sequence of members of `D` is a member.
* `MeasureTheory.closedSolidConvexHull μ 𝓔`: the smallest set of functions that contains `𝓔` and
  is convex, solid and closed.

## Main statements

* `MeasureTheory.closedSolidConvexHull_subset`: the hull is contained in every convex, solid and
  closed set that contains `𝓔`.
* `MeasureTheory.IsAESeqClosed.mem_of_tendstoInMeasure`: a closed set contains the limits in
  `μ`-probability of its almost everywhere finite members.
* `MeasureTheory.exists_lintegral_mul_le_one_lt`: **the separation theorem**. For a finite
  `μ`, a nonempty convex, solid and closed `D` and a measurable, almost everywhere finite
  `X ∉ D`, some measurable `g : Ω → ℝ≥0` of finite integral has `∫⁻ f * g ∂μ ≤ 1` for every
  measurable `f ∈ D` and `1 < ∫⁻ X * g ∂μ`.

The proof truncates `X` to a bounded function outside `D`, separates it in the Hilbert space
`L²(μ)` from the closed convex set of the square-integrable members of `D` with the Hahn–Banach
theorem, represents the separating functional by a function `g` through the Riesz representation,
and replaces `g` by its positive part, which solidity allows. Truncating the members of `D` and
monotone convergence extend the bound from the square-integrable members to all of them.

## References

* [BS99] W. Brannath and W. Schachermayer, *A bipolar theorem for `L⁰₊(Ω, F, P)`*, Séminaire de
  Probabilités XXXIII, Lecture Notes in Math. 1709 (1999), Theorem 1.3.
-/

public section

open Filter Set
open scoped ENNReal NNReal Topology InnerProductSpace

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {D 𝓔 𝓕 : Set (Ω → ℝ≥0∞)}

/-! ### Solid and closed sets of functions -/

/-- A set `D` of functions is **solid** for `μ` when every measurable function that is
`μ`-almost everywhere below a member of `D` is a member of `D`. -/
def IsAESolid (μ : Measure Ω) (D : Set (Ω → ℝ≥0∞)) : Prop :=
  ∀ ⦃f g : Ω → ℝ≥0∞⦄, f ∈ D → Measurable g → g ≤ᵐ[μ] f → g ∈ D

/-- A set `D` of functions is **closed** for `μ` when every measurable, `μ`-almost everywhere
finite function that is the `μ`-almost everywhere limit of a sequence of members of `D` is a member
of `D`: the closedness of `D ∩ L⁰₊(μ)` in `L⁰₊(μ)`. -/
def IsAESeqClosed (μ : Measure Ω) (D : Set (Ω → ℝ≥0∞)) : Prop :=
  ∀ ⦃f : ℕ → Ω → ℝ≥0∞⦄ ⦃g : Ω → ℝ≥0∞⦄, (∀ n, f n ∈ D) → Measurable g → (∀ᵐ ω ∂μ, g ω ≠ ∞) →
    (∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω) atTop (𝓝 (g ω))) → g ∈ D

lemma isAESolid_iff : IsAESolid μ D ↔
    ∀ ⦃f g : Ω → ℝ≥0∞⦄, f ∈ D → Measurable g → g ≤ᵐ[μ] f → g ∈ D :=
  Iff.rfl

lemma isAESeqClosed_iff : IsAESeqClosed μ D ↔
    ∀ ⦃f : ℕ → Ω → ℝ≥0∞⦄ ⦃g : Ω → ℝ≥0∞⦄, (∀ n, f n ∈ D) → Measurable g →
      (∀ᵐ ω ∂μ, g ω ≠ ∞) → (∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω) atTop (𝓝 (g ω))) → g ∈ D :=
  Iff.rfl

/-- The elimination rule of solidity. -/
lemma IsAESolid.mem (hD : IsAESolid μ D) {f g : Ω → ℝ≥0∞} (hf : f ∈ D) (hg : Measurable g)
    (hgf : g ≤ᵐ[μ] f) : g ∈ D :=
  hD hf hg hgf

/-- The elimination rule of closedness. -/
lemma IsAESeqClosed.mem (hD : IsAESeqClosed μ D) {f : ℕ → Ω → ℝ≥0∞} {g : Ω → ℝ≥0∞}
    (hf : ∀ n, f n ∈ D) (hg : Measurable g) (hg_top : ∀ᵐ ω ∂μ, g ω ≠ ∞)
    (hfg : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω) atTop (𝓝 (g ω))) : g ∈ D :=
  hD hf hg hg_top hfg

/-- A solid set contains every measurable function almost everywhere equal to a member. -/
lemma IsAESolid.mem_of_ae_eq (hD : IsAESolid μ D) {f g : Ω → ℝ≥0∞} (hf : f ∈ D)
    (hg : Measurable g) (hgf : g =ᵐ[μ] f) : g ∈ D :=
  hD hf hg hgf.le

/-- A nonempty solid set contains `0`. -/
lemma IsAESolid.zero_mem (hD : IsAESolid μ D) (hne : D.Nonempty) : 0 ∈ D := by
  obtain ⟨f, hf⟩ := hne
  exact hD hf measurable_const (ae_of_all _ fun ω ↦ zero_le)

/-- Solidity passes to a measure with fewer null sets. -/
lemma IsAESolid.mono_ac (hD : IsAESolid μ D) (h : μ ≪ ν) : IsAESolid ν D :=
  fun _ _ hf hg hgf ↦ hD hf hg (h.ae_le hgf)

/-- Closedness passes to a measure with fewer null sets. -/
lemma IsAESeqClosed.mono_ac (hD : IsAESeqClosed μ D) (h : μ ≪ ν) : IsAESeqClosed ν D :=
  fun _ _ hf hg hg_top hfg ↦ hD hf hg (h.ae_le hg_top) (h.ae_le hfg)

/-- **Closedness under convergence in probability.** Under any measure, a closed set contains the
limit of a sequence of almost everywhere finite members that converges in `μ`-probability, with
the distance of the real values. -/
theorem IsAESeqClosed.mem_of_tendstoInMeasure (hD : IsAESeqClosed μ D) {f : ℕ → Ω → ℝ≥0∞}
    {g : Ω → ℝ≥0∞} (hf : ∀ n, f n ∈ D) (hf_top : ∀ n, ∀ᵐ ω ∂μ, f n ω ≠ ∞) (hg : Measurable g)
    (hg_top : ∀ᵐ ω ∂μ, g ω ≠ ∞)
    (hfg : TendstoInMeasure μ (fun n ω ↦ (f n ω).toReal) atTop (fun ω ↦ (g ω).toReal)) :
    g ∈ D := by
  obtain ⟨ns, -, hns⟩ := hfg.exists_seq_tendsto_ae
  refine hD (fun n ↦ hf (ns n)) hg hg_top ?_
  filter_upwards [hns, hg_top, ae_all_iff.2 fun n ↦ hf_top (ns n)] with ω hω hgω hfω
  have h := (ENNReal.continuous_ofReal.tendsto _).comp hω
  simp only [Function.comp_def, ENNReal.ofReal_toReal (hfω _), ENNReal.ofReal_toReal hgω] at h
  exact h

/-! ### The closed solid convex hull -/

/-- The **closed solid convex hull** of a set `𝓔` of functions: the smallest set of functions that
contains `𝓔` and is convex, solid and closed for `μ`. For a nonempty set `𝓔` of measurable
functions and an s-finite `μ`, its almost everywhere finite members are those of the bipolar of `𝓔`
[BS99, Theorem 1.3]. -/
def closedSolidConvexHull (μ : Measure Ω) (𝓔 : Set (Ω → ℝ≥0∞)) : Set (Ω → ℝ≥0∞) :=
  ⋂₀ {D | 𝓔 ⊆ D ∧ Convex ℝ≥0∞ D ∧ IsAESolid μ D ∧ IsAESeqClosed μ D}

lemma mem_closedSolidConvexHull_iff {f : Ω → ℝ≥0∞} :
    f ∈ closedSolidConvexHull μ 𝓔 ↔
      ∀ D, 𝓔 ⊆ D → Convex ℝ≥0∞ D → IsAESolid μ D → IsAESeqClosed μ D → f ∈ D := by
  simp [closedSolidConvexHull, and_imp]

lemma subset_closedSolidConvexHull : 𝓔 ⊆ closedSolidConvexHull μ 𝓔 :=
  fun _ hf ↦ mem_closedSolidConvexHull_iff.2 fun _ hD _ _ _ ↦ hD hf

/-- The closed solid convex hull is contained in every convex, solid and closed set that contains
`𝓔`. -/
lemma closedSolidConvexHull_subset (h𝓔 : 𝓔 ⊆ D) (hconv : Convex ℝ≥0∞ D) (hsolid : IsAESolid μ D)
    (hclosed : IsAESeqClosed μ D) : closedSolidConvexHull μ 𝓔 ⊆ D :=
  fun _ hf ↦ mem_closedSolidConvexHull_iff.1 hf D h𝓔 hconv hsolid hclosed

lemma convex_closedSolidConvexHull : Convex ℝ≥0∞ (closedSolidConvexHull μ 𝓔) :=
  convex_sInter fun _ hD ↦ hD.2.1

lemma isAESolid_closedSolidConvexHull : IsAESolid μ (closedSolidConvexHull μ 𝓔) :=
  fun _ _ hf hg hgf ↦ mem_closedSolidConvexHull_iff.2 fun _ h𝓔 hconv hsolid hclosed ↦
    hsolid (mem_closedSolidConvexHull_iff.1 hf _ h𝓔 hconv hsolid hclosed) hg hgf

lemma isAESeqClosed_closedSolidConvexHull : IsAESeqClosed μ (closedSolidConvexHull μ 𝓔) :=
  fun _ _ hf hg hg_top hfg ↦ mem_closedSolidConvexHull_iff.2 fun _ h𝓔 hconv hsolid hclosed ↦
    hclosed (fun n ↦ mem_closedSolidConvexHull_iff.1 (hf n) _ h𝓔 hconv hsolid hclosed) hg hg_top
      hfg

/-- A convex, solid and closed set is its own closed solid convex hull. -/
lemma closedSolidConvexHull_eq_self (hconv : Convex ℝ≥0∞ D) (hsolid : IsAESolid μ D)
    (hclosed : IsAESeqClosed μ D) : closedSolidConvexHull μ D = D :=
  (closedSolidConvexHull_subset subset_rfl hconv hsolid hclosed).antisymm
    subset_closedSolidConvexHull

/-- A set is its own closed solid convex hull exactly when it is convex, solid and closed. -/
lemma closedSolidConvexHull_eq_self_iff :
    closedSolidConvexHull μ D = D ↔ Convex ℝ≥0∞ D ∧ IsAESolid μ D ∧ IsAESeqClosed μ D := by
  refine ⟨fun h ↦ ?_, fun ⟨hconv, hsolid, hclosed⟩ ↦ closedSolidConvexHull_eq_self hconv hsolid
    hclosed⟩
  rw [← h]
  exact ⟨convex_closedSolidConvexHull, isAESolid_closedSolidConvexHull,
    isAESeqClosed_closedSolidConvexHull⟩

/-- Taking the closed solid convex hull is idempotent. -/
@[simp]
lemma closedSolidConvexHull_closedSolidConvexHull :
    closedSolidConvexHull μ (closedSolidConvexHull μ 𝓔) = closedSolidConvexHull μ 𝓔 :=
  closedSolidConvexHull_eq_self convex_closedSolidConvexHull isAESolid_closedSolidConvexHull
    isAESeqClosed_closedSolidConvexHull

lemma closedSolidConvexHull_mono (h : 𝓔 ⊆ 𝓕) :
    closedSolidConvexHull μ 𝓔 ⊆ closedSolidConvexHull μ 𝓕 :=
  closedSolidConvexHull_subset (h.trans subset_closedSolidConvexHull)
    convex_closedSolidConvexHull isAESolid_closedSolidConvexHull
    isAESeqClosed_closedSolidConvexHull

/-- The closed solid convex hull depends only on the null sets of the measure. -/
lemma closedSolidConvexHull_congr_ae (h : ae μ = ae ν) :
    closedSolidConvexHull μ 𝓔 = closedSolidConvexHull ν 𝓔 := by
  have key : ∀ {μ ν : Measure Ω}, ae μ = ae ν →
      closedSolidConvexHull μ 𝓔 ⊆ closedSolidConvexHull ν 𝓔 := fun h ↦
    closedSolidConvexHull_subset subset_closedSolidConvexHull convex_closedSolidConvexHull
      (isAESolid_closedSolidConvexHull.mono_ac (Measure.ae_le_iff_absolutelyContinuous.1 h.ge))
      (isAESeqClosed_closedSolidConvexHull.mono_ac
        (Measure.ae_le_iff_absolutelyContinuous.1 h.ge))
  exact (key h).antisymm (key h.symm)

/-! ### The separation theorem -/

/-- A closed set that does not contain a measurable, almost everywhere finite function `X` misses
one of its truncations `min X n`. -/
lemma IsAESeqClosed.exists_min_notMem (hD : IsAESeqClosed μ D) {X : Ω → ℝ≥0∞}
    (hX : Measurable X) (hX_top : ∀ᵐ ω ∂μ, X ω ≠ ∞) (hXD : X ∉ D) :
    ∃ n : ℕ, (fun ω ↦ min (X ω) n) ∉ D := by
  by_contra! h
  refine hXD (hD h hX hX_top (ae_of_all _ fun ω ↦ ?_))
  simpa using (tendsto_const_nhds (x := X ω)).min ENNReal.tendsto_nat_nhds_top

section Separation

variable [IsFiniteMeasure μ]

/-- The square-integrable real functions whose positive part is in `D`. -/
private def realPart (μ : Measure Ω) (D : Set (Ω → ℝ≥0∞)) : Set (Lp ℝ 2 μ) :=
  {h | (fun ω ↦ ENNReal.ofReal (h ω)) ∈ D}

omit [IsFiniteMeasure μ] in
private lemma measurable_ofReal_Lp (h : Lp ℝ 2 μ) : Measurable fun ω ↦ ENNReal.ofReal (h ω) :=
  (Lp.stronglyMeasurable h).measurable.ennreal_ofReal

omit [IsFiniteMeasure μ] in
private lemma convex_realPart (hconv : Convex ℝ≥0∞ D) (hsolid : IsAESolid μ D) :
    Convex ℝ (realPart μ D) := by
  intro h₁ h₁D h₂ h₂D a b ha hb hab
  refine hsolid (hconv h₁D h₂D zero_le zero_le
    (by rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one])) (measurable_ofReal_Lp _) ?_
  filter_upwards [Lp.coeFn_add (a • h₁) (b • h₂), Lp.coeFn_smul a h₁, Lp.coeFn_smul b h₂]
    with ω hω h₁ω h₂ω
  simp only [hω, Pi.add_apply, h₁ω, h₂ω, Pi.smul_apply, smul_eq_mul]
  refine (ENNReal.ofReal_add_le).trans ?_
  rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]

omit [IsFiniteMeasure μ] in
private lemma isClosed_realPart (hclosed : IsAESeqClosed μ D) : IsClosed (realPart μ D) := by
  refine IsSeqClosed.isClosed fun u h hu hlim ↦ ?_
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  exact hclosed (fun n ↦ hu (ns n)) (measurable_ofReal_Lp h)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_ne_top)
    (hns.mono fun ω hω ↦ (ENNReal.continuous_ofReal.tendsto _).comp hω)

/-- A functional `h ↦ ∫ g₀ * h` below `u` on `realPart μ D` bounds `∫⁻ min f n * g₀⁺` by `u` for
every measurable `f ∈ D`: the truncation of `f` to `[0, n]` and to the set where `g₀` is
positive is a square-integrable member of `D`. -/
private lemma lintegral_min_mul_ofReal_le (hsolid : IsAESolid μ D) {g₀ : Lp ℝ 2 μ} {u : ℝ}
    (hD : ∀ h ∈ realPart μ D, ∫ ω, g₀ ω * h ω ∂μ < u) {f : Ω → ℝ≥0∞} (hf : f ∈ D)
    (hfm : Measurable f) (n : ℕ) :
    ∫⁻ ω, min (f ω) n * ENNReal.ofReal (g₀ ω) ∂μ ≤ ENNReal.ofReal u := by
  have hg₀ : Measurable g₀ := (Lp.stronglyMeasurable g₀).measurable
  set r : Ω → ℝ := fun ω ↦ if 0 < g₀ ω then (min (f ω) n).toReal else 0
  have hr : Measurable r := Measurable.ite (measurableSet_lt measurable_const hg₀)
    (hfm.min measurable_const).ennreal_toReal measurable_const
  have hr_le ω : ‖r ω‖ ≤ n := by
    simp only [r]
    split_ifs
    · simpa [Real.norm_eq_abs] using
        ENNReal.toReal_le_coe_of_le_coe (min_le_right (f ω) (n : ℝ≥0∞))
    · simp
  have hrL : MemLp r 2 μ := MemLp.of_bound hr.aestronglyMeasurable n (ae_of_all _ hr_le)
  have hrD : hrL.toLp r ∈ realPart μ D :=
    hsolid hf (measurable_ofReal_Lp _) <| (MemLp.coeFn_toLp hrL).mono fun ω hω ↦ by
      simp only [hω, r]
      split_ifs
      · exact (ENNReal.ofReal_toReal_le).trans (min_le_left _ _)
      · simp
  have h_eq : (fun ω ↦ min (f ω) n * ENNReal.ofReal (g₀ ω)) =
      fun ω ↦ ENNReal.ofReal (g₀ ω * r ω) := by
    ext ω
    simp only [r]
    split_ifs with h
    · rw [ENNReal.ofReal_mul h.le, ENNReal.ofReal_toReal
        (min_lt_of_right_lt (ENNReal.natCast_lt_top n)).ne, mul_comm]
    · simp [ENNReal.ofReal_eq_zero.2 (not_lt.1 h)]
  have hint : Integrable (fun ω ↦ g₀ ω * r ω) μ := by
    simpa [mul_comm] using ((Lp.memLp g₀).integrable one_le_two).bdd_mul
      hr.aestronglyMeasurable (ae_of_all _ hr_le)
  have hnonneg : 0 ≤ᵐ[μ] fun ω ↦ g₀ ω * r ω := ae_of_all _ fun ω ↦ by
    simp only [r]
    split_ifs with h
    · exact mul_nonneg h.le ENNReal.toReal_nonneg
    · simp
  rw [h_eq, ← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  refine ENNReal.ofReal_le_ofReal ((le_of_eq ?_).trans (hD _ hrD).le)
  exact integral_congr_ae ((MemLp.coeFn_toLp hrL).mono fun ω hω ↦ by simp [hω])

/-- A functional `h ↦ ∫ g₀ * h` below `u` on `realPart μ D` bounds `∫⁻ f * g₀⁺` by `u` for every
measurable `f ∈ D`, by monotone convergence along the truncations `min f n`. -/
private lemma lintegral_mul_ofReal_le (hsolid : IsAESolid μ D) {g₀ : Lp ℝ 2 μ} {u : ℝ}
    (hD : ∀ h ∈ realPart μ D, ∫ ω, g₀ ω * h ω ∂μ < u) {f : Ω → ℝ≥0∞} (hf : f ∈ D)
    (hfm : Measurable f) :
    ∫⁻ ω, f ω * ENNReal.ofReal (g₀ ω) ∂μ ≤ ENNReal.ofReal u :=
  calc ∫⁻ ω, f ω * ENNReal.ofReal (g₀ ω) ∂μ
      = ∫⁻ ω, ⨆ n : ℕ, min (f ω) n * ENNReal.ofReal (g₀ ω) ∂μ := by
        congr with ω
        rw [← ENNReal.iSup_mul, ← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    _ = ⨆ n : ℕ, ∫⁻ ω, min (f ω) n * ENNReal.ofReal (g₀ ω) ∂μ :=
        lintegral_iSup (fun n ↦ (hfm.min measurable_const).mul
          (Lp.stronglyMeasurable g₀).measurable.ennreal_ofReal) fun m n hmn ω ↦ by gcongr
    _ ≤ ENNReal.ofReal u := iSup_le (lintegral_min_mul_ofReal_le hsolid hD hf hfm)

omit [IsFiniteMeasure μ] in
private lemma lintegral_mul_toNNReal_div {u : ℝ} (hu : 0 < u) (F : Ω → ℝ≥0∞) (g₀ : Ω → ℝ) :
    ∫⁻ ω, F ω * (g₀ ω / u).toNNReal ∂μ =
      (∫⁻ ω, F ω * ENNReal.ofReal (g₀ ω) ∂μ) / ENNReal.ofReal u := by
  have hu' : (ENNReal.ofReal u)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by simpa using hu)
  simp_rw [ENNReal.ofNNReal_toNNReal, ENNReal.ofReal_div_of_pos hu, ← mul_div_assoc,
    div_eq_mul_inv]
  rw [lintegral_mul_const' _ _ hu']

/-- The separation theorem for a bounded function and a finite measure. -/
private lemma exists_lintegral_mul_le_one_lt_of_le (hconv : Convex ℝ≥0∞ D)
    (hsolid : IsAESolid μ D) (hclosed : IsAESeqClosed μ D) (hne : D.Nonempty)
    {X : Ω → ℝ≥0∞} (hX : Measurable X) {N : ℝ≥0} (hXN : ∀ ω, X ω ≤ N) (hXD : X ∉ D) :
    ∃ g : Ω → ℝ≥0, Measurable g ∧ ∫⁻ ω, g ω ∂μ ≠ ∞ ∧
      (∀ f ∈ D, Measurable f → ∫⁻ ω, f ω * g ω ∂μ ≤ 1) ∧ 1 < ∫⁻ ω, X ω * g ω ∂μ := by
  have hX_top ω : X ω ≠ ∞ := ((hXN ω).trans_lt ENNReal.coe_lt_top).ne
  -- `X` as an element of `L²(μ)`, outside the closed convex set `realPart μ D`
  have hXL : MemLp (fun ω ↦ (X ω).toReal) 2 μ :=
    MemLp.of_bound hX.ennreal_toReal.aestronglyMeasurable N (ae_of_all _ fun ω ↦ by
      simpa [Real.norm_eq_abs] using ENNReal.toReal_le_coe_of_le_coe (hXN ω))
  have hxD : hXL.toLp _ ∉ realPart μ D := fun hx ↦ hXD <| hsolid.mem_of_ae_eq hx hX <|
    (MemLp.coeFn_toLp hXL).mono fun ω hω ↦ by simp [hω, ENNReal.ofReal_toReal (hX_top ω)]
  obtain ⟨φ, u, hφD, hφx⟩ := geometric_hahn_banach_closed_point
    (convex_realPart hconv hsolid) (isClosed_realPart hclosed) hxD
  -- the Riesz representative `g₀` of the separating functional
  set g₀ := (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm φ
  have hφ (h : Lp ℝ 2 μ) : φ h = ∫ ω, g₀ ω * h ω ∂μ := by
    rw [← InnerProductSpace.toDual_symm_apply, L2.inner_def]
    simp [g₀, mul_comm]
  simp_rw [hφ] at hφD hφx
  -- `0` is in `realPart μ D`, so the level `u` is positive
  have hu : 0 < u := by
    have h0 : (0 : Lp ℝ 2 μ) ∈ realPart μ D :=
      hsolid.mem_of_ae_eq (hsolid.zero_mem hne) (measurable_ofReal_Lp _)
        ((Lp.coeFn_zero ℝ 2 μ).mono fun ω hω ↦ by dsimp only; rw [hω]; simp)
    refine lt_of_eq_of_lt ?_ (hφD 0 h0)
    rw [integral_congr_ae ((Lp.coeFn_zero ℝ 2 μ).mono fun ω hω ↦ by rw [hω])]
    simp
  -- the weight is the positive part of `g₀ / u`
  refine ⟨fun ω ↦ (g₀ ω / u).toNNReal,
    ((Lp.stronglyMeasurable g₀).measurable.div_const u).real_toNNReal,
    (((Lp.memLp g₀).integrable one_le_two).div_const u).lintegral_lt_top.ne, fun f hf hfm ↦ ?_, ?_⟩
  · rw [lintegral_mul_toNNReal_div hu, ENNReal.div_le_iff (by simp [hu])
      ENNReal.ofReal_ne_top, one_mul]
    exact lintegral_mul_ofReal_le hsolid hφD hf hfm
  · rw [lintegral_mul_toNNReal_div hu, ENNReal.lt_div_iff_mul_lt (by simp [hu])
      (Or.inl ENNReal.ofReal_ne_top), one_mul]
    have hx : u < ∫ ω, g₀ ω * (X ω).toReal ∂μ :=
      hφx.trans_eq (integral_congr_ae ((MemLp.coeFn_toLp hXL).mono fun ω hω ↦ by simp [hω]))
    refine (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hx, hu.trans hx⟩).trans_le
      (TauCeti.MeasureTheory.ofReal_integral_le_lintegral_ofReal.trans_eq
        (lintegral_congr fun ω ↦ ?_))
    rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hX_top ω), mul_comm]

/-- **The separation theorem**, the separation step in the proof of [BS99, Theorem 1.3], here
through `L²(μ)` rather than `L¹`–`L∞` duality. For a finite measure `μ`, a measurable,
almost everywhere finite function `X` outside a nonempty convex, solid and closed set `D` is
separated from `D` by a measurable weight `g : Ω → ℝ≥0` of finite integral: `∫⁻ f * g ∂μ ≤ 1`
for every measurable `f ∈ D`, and `1 < ∫⁻ X * g ∂μ`. -/
theorem exists_lintegral_mul_le_one_lt (hconv : Convex ℝ≥0∞ D) (hsolid : IsAESolid μ D)
    (hclosed : IsAESeqClosed μ D) (hne : D.Nonempty) {X : Ω → ℝ≥0∞} (hX : Measurable X)
    (hX_top : ∀ᵐ ω ∂μ, X ω ≠ ∞) (hXD : X ∉ D) :
    ∃ g : Ω → ℝ≥0, Measurable g ∧ ∫⁻ ω, g ω ∂μ ≠ ∞ ∧
      (∀ f ∈ D, Measurable f → ∫⁻ ω, f ω * g ω ∂μ ≤ 1) ∧ 1 < ∫⁻ ω, X ω * g ω ∂μ := by
  obtain ⟨n, hn⟩ := hclosed.exists_min_notMem hX hX_top hXD
  obtain ⟨g, hg, hg_top, hD, hXg⟩ := exists_lintegral_mul_le_one_lt_of_le hconv hsolid hclosed
    hne (hX.min measurable_const) (N := n) (fun ω ↦ by simp) hn
  exact ⟨g, hg, hg_top, hD, hXg.trans_le (lintegral_mono fun ω ↦ by gcongr; exact min_le_left _ _)⟩

end Separation

end MeasureTheory
