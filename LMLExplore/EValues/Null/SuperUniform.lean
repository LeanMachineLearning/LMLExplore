/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Null.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.Order.Monotone

/-!
# The super-uniform null

A probability measure `μ` on `ℝ≥0∞` is super-uniform when `μ (Iic α) ≤ α` for every level `α`:
it charges every initial segment `[0, α]` at most as much as the uniform law on `[0, 1]` does. The
super-uniform laws are the laws of the p-variables: a measurable `p` is a p-variable for a null
`S` of probability measures exactly when its law under every member of `S` is super-uniform
[RW, Definition 1.2]. The **super-uniform null** `superUniformNull` collects them, so that
statements about all p-variables of all nulls become statements about one null on `ℝ≥0∞`: an
e-variable `f` for `superUniformNull` turns every p-variable `p` of every null of probability
measures into the e-variable `f ∘ p`, and conversely the identity is a p-variable for
`superUniformNull`.

A super-uniform law dominates the uniform law on `[0, 1]` stochastically, so the integral of an
antitone function against it is at most the integral of that function on `[0, 1]`. This gives the
e-variables of the super-uniform null: a measurable `f` is one exactly when its antitone envelope
`u ↦ ⨆ q ≥ u, f q` has integral at most one on `[0, 1]`. The envelope is the best a bet `f` can do
against a law that may put the mass of `[0, u]` at any point above `u`: for the converse, the law
of `q (U)`, for a uniform `U` and a measurable selection `q x ≥ x` that nearly attains the envelope
on the cells of a grid, is super-uniform. For an antitone `f` the envelope is `f`, which is the
calibration theorem [VW21, Proposition 2.1].

## Main definitions

* `ProbabilityTheory.superUniformNull`: the super-uniform probability measures on `ℝ≥0∞`.

## Main statements

* `ProbabilityTheory.subset_superUniformNull_iff`: the super-uniform null is the largest null of
  probability measures on `ℝ≥0∞` for which the identity is a p-variable.
* `ProbabilityTheory.isPVar_iff_mapNull_subset_superUniformNull`: a measurable `p` is a p-variable
  for a null of probability measures exactly when its laws under the members are super-uniform.
* `ProbabilityTheory.IsEVar.comp_isPVar`: an e-variable for the super-uniform null, composed with
  a p-variable for a null of probability measures, is an e-variable for that null.
* `ProbabilityTheory.map_mem_superUniformNull_of_ofReal_le`: the law of a measurable function above
  a uniform variable on `[0, 1]` is super-uniform.
* `ProbabilityTheory.lintegral_le_of_mem_superUniformNull`: a super-uniform law dominates the
  uniform law on `[0, 1]` stochastically.
* `ProbabilityTheory.isEVar_superUniformNull_iff`: a measurable `f` is an e-variable for the
  super-uniform null exactly when its antitone envelope has integral at most one on `[0, 1]`, and
  `ProbabilityTheory.isEVar_superUniformNull_iff_of_antitone`: the case of an antitone `f`.

## Implementation notes

The definition and `isPVar_iff_mapNull_subset_superUniformNull` follow the prototype of
`notes/book/Suggested.lean` (commit `158797d`) in the paper project `RemyDegenne/evalues_research`
(Apache 2.0).

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, Definition 1.2.
* [VW21] V. Vovk and R. Wang, *E-values: calibration, combination and applications*, Ann. Statist.
  49 (2021), arXiv:1912.06116v4, Proposition 2.1.
-/

public section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S : Set (Measure Ω)} {P : Measure Ω}
  {p : Ω → ℝ≥0∞} {T : Set (Measure ℝ≥0∞)} {μ : Measure ℝ≥0∞} {f : ℝ≥0∞ → ℝ≥0∞}

/-- The **super-uniform null**: the probability measures `μ` on `ℝ≥0∞` with `μ (Iic α) ≤ α` for
every `α`. These are the laws of the p-variables
(`ProbabilityTheory.isPVar_iff_mapNull_subset_superUniformNull`). -/
def superUniformNull : Set (Measure ℝ≥0∞) :=
  {μ | IsProbabilityMeasure μ ∧ ∀ α, μ (Iic α) ≤ α}

@[simp]
theorem mem_superUniformNull :
    μ ∈ superUniformNull ↔ IsProbabilityMeasure μ ∧ ∀ α, μ (Iic α) ≤ α :=
  Iff.rfl

theorem isProbabilityMeasure_of_mem_superUniformNull (hμ : μ ∈ superUniformNull) :
    IsProbabilityMeasure μ :=
  hμ.1

theorem measure_Iic_le_of_mem_superUniformNull (hμ : μ ∈ superUniformNull) (α : ℝ≥0∞) :
    μ (Iic α) ≤ α :=
  hμ.2 α

/-- The identity of `ℝ≥0∞` is a p-variable for the super-uniform null. -/
theorem isPVar_id_superUniformNull : IsPVar id superUniformNull :=
  ⟨measurable_id, fun _ hμ ↦ hμ.2⟩

/-- The super-uniform null is the largest null of probability measures on `ℝ≥0∞` for which the
identity is a p-variable. -/
theorem subset_superUniformNull_iff :
    T ⊆ superUniformNull ↔ (∀ μ ∈ T, IsProbabilityMeasure μ) ∧ IsPVar id T :=
  ⟨fun h ↦ ⟨fun _ hμ ↦ (h hμ).1, isPVar_id_superUniformNull.anti_set h⟩,
    fun h μ hμ ↦ ⟨h.1 μ hμ, h.2.measure_le_le μ hμ⟩⟩

/-- The law of a p-variable under a probability measure of the null is super-uniform. -/
theorem IsPVar.map_mem_superUniformNull (hp : IsPVar p S) (hP : P ∈ S) [IsProbabilityMeasure P] :
    P.map p ∈ superUniformNull := by
  refine ⟨inferInstance, fun α ↦ ?_⟩
  rw [Measure.map_apply hp.measurable measurableSet_Iic]
  exact hp.measure_le_le P hP α

/-- **The laws of the p-variables are the super-uniform laws**: a measurable `p` is a p-variable
for a null of probability measures exactly when its law under every member of the null is
super-uniform. -/
theorem isPVar_iff_mapNull_subset_superUniformNull (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hp : Measurable p) : IsPVar p S ↔ mapNull p S ⊆ superUniformNull := by
  rw [subset_superUniformNull_iff, isPVar_mapNull_iff hp measurable_id, Function.id_comp]
  exact ⟨fun h ↦ ⟨isProbabilityMeasure_of_mem_mapNull hS, h⟩, And.right⟩

/-- **E-variables for the super-uniform null turn p-variables into e-variables**: for a null of
probability measures and a p-variable `p`, `f ∘ p` is an e-variable whenever `f` is one for the
super-uniform null. Conversely, the identity is a p-variable for the super-uniform null
(`isPVar_id_superUniformNull`). -/
theorem IsEVar.comp_isPVar (hf : IsEVar f superUniformNull)
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hp : IsPVar p S) : IsEVar (f ∘ p) S :=
  (isEVar_mapNull_iff hp.measurable hf.measurable).1
    (hf.anti_set ((isPVar_iff_mapNull_subset_superUniformNull hS hp.measurable).1 hp))

/-- The law of a measurable function `q` above a uniform variable on `[0, 1]`, that is, with
`ENNReal.ofReal x ≤ q x` for `x ∈ [0, 1]`, is super-uniform. -/
theorem map_mem_superUniformNull_of_ofReal_le {q : ℝ → ℝ≥0∞} (hq : Measurable q)
    (h_le : ∀ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal x ≤ q x) :
    (volume.restrict (Icc (0 : ℝ) 1)).map q ∈ superUniformNull := by
  have : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
  refine (isExactPVar_ofReal_volume.toIsPVar.mono hq fun P hP ↦ ?_).map_mem_superUniformNull
    (mem_singleton _)
  rw [mem_singleton_iff.1 hP]
  exact ae_restrict_of_forall_mem measurableSet_Icc h_le

/-- The uniform law on `[0, 1]`, as a law on `ℝ≥0∞`, is super-uniform. -/
theorem map_ofReal_mem_superUniformNull :
    (volume.restrict (Icc (0 : ℝ) 1)).map ENNReal.ofReal ∈ superUniformNull :=
  map_mem_superUniformNull_of_ofReal_le ENNReal.measurable_ofReal fun _ _ ↦ le_rfl

/-- **A super-uniform law dominates the uniform law stochastically**: the integral of an antitone
function against a super-uniform law is at most its integral against the uniform law on
`[0, 1]`. -/
theorem lintegral_le_of_mem_superUniformNull (hμ : μ ∈ superUniformNull) (hf : Antitone f) :
    ∫⁻ x, f x ∂μ ≤ ∫⁻ x in Icc (0 : ℝ) 1, f (ENNReal.ofReal x) :=
  have := hμ.1
  isPVar_id_superUniformNull.lintegral_comp_le hμ prob_le_one hf

/-- An antitone `f` is an e-variable for the super-uniform null exactly when its integral on
`[0, 1]` is at most one [VW21, Proposition 2.1]. -/
theorem isEVar_superUniformNull_iff_of_antitone (hf : Antitone f) :
    IsEVar f superUniformNull ↔ ∫⁻ x in Icc (0 : ℝ) 1, f (ENNReal.ofReal x) ≤ 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨hf.measurable, fun μ hμ ↦
    (lintegral_le_of_mem_superUniformNull hμ hf).trans h⟩⟩
  rw [← lintegral_map hf.measurable ENNReal.measurable_ofReal]
  exact h.lintegral_le_one map_ofReal_mem_superUniformNull

/-- An e-variable for the super-uniform null, composed with a measurable selection `v ∘ h` above a
uniform variable on `[0, 1]` that takes countably many values, has an antitone envelope of
integral at most one on `[0, 1]`: at each of the countably many values `v k`, a sequence of points
`r k m ≥ v k` nearly attains the envelope, and the laws of `r (h x) m` are super-uniform. -/
private lemma lintegral_iSup_comp_le_one (hf : IsEVar f superUniformNull) {h : ℝ → ℕ}
    (hh : Measurable h) {v : ℕ → ℝ≥0∞} (hv : ∀ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal x ≤ v (h x)) :
    ∫⁻ x in Icc (0 : ℝ) 1, ⨆ q ≥ v (h x), f q ≤ 1 := by
  have h_sel : ∀ k, ∃ r : ℕ → ℝ≥0∞, (∀ m, v k ≤ r m) ∧
      Tendsto (fun m ↦ f (r m)) atTop (𝓝 (⨆ q ≥ v k, f q)) := by
    intro k
    obtain ⟨u, -, hu, hmem⟩ := exists_seq_tendsto_sSup (S := f '' Ici (v k))
      ⟨_, mem_image_of_mem f self_mem_Ici⟩ (OrderTop.bddAbove _)
    choose r hr hru using hmem
    refine ⟨r, hr, ?_⟩
    rw [sSup_image, ← funext hru] at hu
    exact hu
  choose r hr hr_tendsto using h_sel
  have hq : ∀ m, Measurable fun x ↦ r (h x) m := fun m ↦
    (measurable_from_nat (f := fun k ↦ r k m)).comp hh
  calc ∫⁻ x in Icc (0 : ℝ) 1, ⨆ q ≥ v (h x), f q
      = ∫⁻ x in Icc (0 : ℝ) 1, liminf (fun m ↦ f (r (h x) m)) atTop :=
        lintegral_congr fun x ↦ (hr_tendsto (h x)).liminf_eq.symm
    _ ≤ liminf (fun m ↦ ∫⁻ x in Icc (0 : ℝ) 1, f (r (h x) m)) atTop :=
        lintegral_liminf_le fun m ↦ hf.measurable.comp (hq m)
    _ ≤ 1 := by
      refine liminf_le_of_frequently_le' (.of_forall fun m ↦ ?_)
      rw [← lintegral_map hf.measurable (hq m)]
      exact hf.lintegral_le_one
        (map_mem_superUniformNull_of_ofReal_le (hq m) fun x hx ↦ (hv x hx).trans (hr _ m))

/-- **The e-variables of the super-uniform null**: a measurable `f : ℝ≥0∞ → ℝ≥0∞` is an
e-variable for the super-uniform null exactly when its antitone envelope `u ↦ ⨆ q ≥ u, f q` has
integral at most one on `[0, 1]`. A super-uniform law may move the mass of `[0, u]` to any point
above `u`, so a bet against all of them is worth what the envelope is worth against the uniform
law. For an antitone `f`, the envelope is `f` (`isEVar_superUniformNull_iff_of_antitone`). -/
theorem isEVar_superUniformNull_iff (hf : Measurable f) :
    IsEVar f superUniformNull ↔ ∫⁻ x in Icc (0 : ℝ) 1, ⨆ q ≥ ENNReal.ofReal x, f q ≤ 1 := by
  have h_anti : Antitone fun u ↦ ⨆ q ≥ u, f q := fun u w huw ↦
    biSup_mono fun q (hq : w ≤ q) ↦ huw.trans hq
  have h_le : ∀ q, f q ≤ ⨆ q' ≥ q, f q' := fun q ↦
    le_iSup₂ (f := fun q' (_ : q' ≥ q) ↦ f q') q le_rfl
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨hf, fun μ hμ ↦ (lintegral_mono h_le).trans
    ((lintegral_le_of_mem_superUniformNull hμ h_anti).trans h)⟩⟩
  -- the envelope on `[0, 1]` is the limit, at its continuity points, of its values at the grid
  -- points `⌈x (n + 1)⌉₊ / (n + 1) ≥ x`, which `lintegral_iSup_comp_le_one` bounds
  set F : ℝ → ℝ≥0∞ := fun x ↦ ⨆ q ≥ ENNReal.ofReal x, f q
  have hF_anti : Antitone F := h_anti.comp_monotone ENNReal.ofReal_mono
  set y : ℕ → ℝ → ℝ := fun n x ↦ (⌈x * (n + 1)⌉₊ : ℝ) / (n + 1)
  have hy_meas : ∀ n, Measurable (y n) := fun n ↦
    (measurable_from_nat (f := fun k : ℕ ↦ (k : ℝ) / (n + 1))).comp
      (measurable_id.mul_const _).nat_ceil
  have h_ae : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1), F x ≤ liminf (fun n ↦ F (y n x)) atTop := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (hF_anti.countable_not_continuousAt.ae_notMem volume)] with x hx hcont
    have h_lim : Tendsto (fun n : ℕ ↦ y n x) atTop (𝓝 x) :=
      (tendsto_nat_ceil_mul_div_atTop hx.1).comp
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    exact ((not_not.1 hcont).tendsto.comp h_lim).liminf_eq.ge
  calc ∫⁻ x in Icc (0 : ℝ) 1, F x
      ≤ ∫⁻ x in Icc (0 : ℝ) 1, liminf (fun n ↦ F (y n x)) atTop := lintegral_mono_ae h_ae
    _ ≤ liminf (fun n ↦ ∫⁻ x in Icc (0 : ℝ) 1, F (y n x)) atTop :=
        lintegral_liminf_le fun n ↦ hF_anti.measurable.comp (hy_meas n)
    _ ≤ 1 := by
      refine liminf_le_of_frequently_le' (.of_forall fun n ↦ ?_)
      have hn : (0 : ℝ) < n + 1 := n.cast_add_one_pos
      refine lintegral_iSup_comp_le_one h (measurable_id.mul_const _).nat_ceil
        (v := fun k ↦ ENNReal.ofReal ((k : ℝ) / (n + 1))) fun x _ ↦ ENNReal.ofReal_le_ofReal ?_
      rw [le_div_iff₀ hn]
      exact Nat.le_ceil _

end ProbabilityTheory
