/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-!
# The essential supremum of a family of functions

For a family `f : ι → Ω → ℝ≥0∞` of functions, indexed by an arbitrary, possibly uncountable,
type, the pointwise supremum `fun ω ↦ ⨆ i, f i ω` need not be measurable, and changing each
`f i` on a null set may change it everywhere. The **essential supremum** of the family is the
almost everywhere least function that dominates every `f i` almost everywhere. For an s-finite
measure it exists, it is the supremum of a countable subfamily, and it is unique up to null sets.
It is the object behind the Snell envelope of optimal stopping, the essential supremum over
stopping times of conditional expectations.

This is not Mathlib's `essSup g μ`, the essential supremum of the values of one function, which is
a constant.

The existence proof is the argument of [FS16, §A.5], with the bounded decreasing transform
`x ↦ (1 + x)⁻¹` and a finite measure with the null sets of `μ` (Mathlib's `Measure.toFinite`):
a sequence of members minimizing the integral of `(1 + sup)⁻¹` dominates every member, since
adjoining a member can only lower the integrand and so cannot change it except on a null set.

## Main definitions

* `MeasureTheory.essSupFamily f μ`: the essential supremum of the family `f` with respect to `μ`.
  It is the supremum of a countable subfamily, and `0` when no countable subfamily dominates the
  family almost everywhere.

## Main statements

* `MeasureTheory.exists_seq_forall_ae_le_iSup`: for an s-finite measure, every nonempty family
  of almost everywhere measurable functions is dominated almost everywhere by the supremum of a
  sequence of its members.
* `MeasureTheory.ae_le_essSupFamily`, `MeasureTheory.essSupFamily_ae_le`,
  `MeasureTheory.essSupFamily_ae_le_iff`, `MeasureTheory.ae_eq_essSupFamily_iff`: the essential
  supremum dominates every member, is below every function that dominates every member, and is
  characterized up to null sets by these two properties.
* `MeasureTheory.measurable_essSupFamily`: it is measurable for every σ-algebra for which the
  members are, in particular for a sub-σ-algebra; `MeasureTheory.aemeasurable_essSupFamily`: it is
  almost everywhere measurable when the members are.
* `MeasureTheory.exists_countable_essSupFamily_eq`, `MeasureTheory.exists_seq_essSupFamily_eq`:
  it is the supremum of a countable subfamily.
* `MeasureTheory.exists_seq_monotone_ae_eq_essSupFamily`: for a family directed upward almost
  everywhere, it is almost everywhere the supremum of an almost everywhere increasing sequence of
  members, and `MeasureTheory.setLIntegral_essSupFamily_of_directed`: its integral over any set is
  the supremum of the integrals of the members.

## References

* [FS16] H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*,
  4th edition, De Gruyter, 2016, §A.5.
* A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential inference
  must rely on nonnegative martingales*, arXiv:2009.03167v3, Appendix A.
-/

public section

open Filter Set
open scoped ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f g : ι → Ω → ℝ≥0∞}
  {h : Ω → ℝ≥0∞}

/-- For an s-finite measure, every nonempty family of almost everywhere measurable functions with
values in `ℝ≥0∞` is dominated almost everywhere by the supremum of a sequence of its members. -/
theorem exists_seq_forall_ae_le_iSup [SFinite μ] [Nonempty ι] (hf : ∀ i, AEMeasurable (f i) μ) :
    ∃ s : ℕ → ι, ∀ i, f i ≤ᵐ[μ] fun ω ↦ ⨆ n, f (s n) ω := by
  -- The value of a sequence of indices: the `μ.toFinite`-integral of `(1 + sup)⁻¹`.
  let v : (ℕ → ι) → ℝ≥0∞ := fun s ↦ ∫⁻ ω, (1 + ⨆ n, f (s n) ω)⁻¹ ∂μ.toFinite
  have hv_anti {s t : ℕ → ι} (hst : ∀ ω, ⨆ n, f (s n) ω ≤ ⨆ n, f (t n) ω) : v t ≤ v s :=
    lintegral_mono fun ω ↦ ENNReal.inv_le_inv.2 (add_le_add_right (hst ω) 1)
  -- A sequence of sequences whose values tend to the infimum of the values.
  obtain ⟨u, -, hu, hu_mem⟩ := exists_seq_tendsto_sInf (range_nonempty v) (OrderBot.bddBelow _)
  choose s hs using hu_mem
  -- Their concatenation `t` attains the infimum.
  let t : ℕ → ι := fun m ↦ s (Nat.unpair m).1 (Nat.unpair m).2
  have ht_iSup (ω : Ω) : ⨆ m, f (t m) ω = ⨆ k, ⨆ n, f (s k n) ω :=
    iSup_unpair fun k n ↦ f (s k n) ω
  have ht_min (r : ℕ → ι) : v t ≤ v r := by
    refine (ge_of_tendsto' hu fun k ↦ ?_).trans (sInf_le (mem_range_self r))
    rw [← hs k]
    exact hv_anti fun ω ↦ (ht_iSup ω).symm ▸ le_iSup (fun k ↦ ⨆ n, f (s k n) ω) k
  refine ⟨t, fun i ↦ ?_⟩
  -- Adjoining `i` to `t` does not lower the value, hence does not change the supremum a.e.
  let t' : ℕ → ι := fun n ↦ if n = 0 then i else t (n - 1)
  have ht'_iSup (ω : Ω) : ⨆ n, f (t' n) ω = f i ω ⊔ ⨆ n, f (t n) ω := by
    rw [← sup_iSup_nat_succ]
    simp [t']
  have h_meas : AEMeasurable (fun ω ↦ (1 + ⨆ n, f (t n) ω)⁻¹) μ.toFinite :=
    ((AEMeasurable.iSup fun n ↦ hf (t n)).const_add 1).inv.mono_ac
      (toFinite_absolutelyContinuous μ)
  have h_fin : ∫⁻ ω, (1 + ⨆ n, f (t' n) ω)⁻¹ ∂μ.toFinite ≠ ∞ := by
    refine ne_top_of_le_ne_top (measure_ne_top μ.toFinite univ) ?_
    rw [← lintegral_one]
    exact lintegral_mono fun ω ↦ ENNReal.inv_le_one.2 le_self_add
  have h_eq := ae_eq_of_ae_le_of_lintegral_le
    (ae_of_all _ fun ω ↦ ENNReal.inv_le_inv.2 (add_le_add_right
      ((ht'_iSup ω).symm ▸ le_sup_right) 1)) h_fin h_meas (ht_min t')
  rw [ae_toFinite] at h_eq
  filter_upwards [h_eq] with ω hω
  rw [inv_inj, ENNReal.add_right_inj ENNReal.one_ne_top, ht'_iSup] at hω
  exact hω ▸ le_sup_left

open scoped Classical in
/-- The **essential supremum** of a family `f` of functions with values in `ℝ≥0∞` with respect to
a measure `μ`: the almost everywhere least function that dominates every `f i` almost everywhere.
It is defined as the supremum of a sequence of members that dominates every member almost
everywhere, which exists for an s-finite measure and almost everywhere measurable members
(`exists_seq_forall_ae_le_iSup`), and is `0` when no such sequence exists. -/
noncomputable def essSupFamily (f : ι → Ω → ℝ≥0∞) (μ : Measure Ω) : Ω → ℝ≥0∞ :=
  if hs : ∃ s : ℕ → ι, ∀ i, f i ≤ᵐ[μ] fun ω ↦ ⨆ n, f (s n) ω then
    fun ω ↦ ⨆ n, f (hs.choose n) ω
  else 0

open scoped Classical in
/-- The defining equation of `essSupFamily`. -/
theorem essSupFamily_def (f : ι → Ω → ℝ≥0∞) (μ : Measure Ω) :
    essSupFamily f μ = if hs : ∃ s : ℕ → ι, ∀ i, f i ≤ᵐ[μ] fun ω ↦ ⨆ n, f (s n) ω then
      fun ω ↦ ⨆ n, f (hs.choose n) ω
    else 0 := (rfl)

/-- The essential supremum of an empty family is `0`. -/
@[simp]
theorem essSupFamily_of_isEmpty [IsEmpty ι] : essSupFamily f μ = 0 := by
  simp [essSupFamily_def]

/-- The essential supremum of a family is the supremum of a countable subfamily. -/
theorem exists_countable_essSupFamily_eq (f : ι → Ω → ℝ≥0∞) (μ : Measure Ω) :
    ∃ C : Set ι, C.Countable ∧ essSupFamily f μ = fun ω ↦ ⨆ i ∈ C, f i ω := by
  by_cases hs : ∃ s : ℕ → ι, ∀ i, f i ≤ᵐ[μ] fun ω ↦ ⨆ n, f (s n) ω
  · refine ⟨range hs.choose, countable_range _, ?_⟩
    simp only [essSupFamily_def, hs, dite_true, iSup_range]
  · refine ⟨∅, countable_empty, ?_⟩
    simp only [essSupFamily_def, hs, dite_false]
    simp [Pi.zero_def]

/-- The essential supremum of a family is pointwise below the pointwise supremum. -/
theorem essSupFamily_le_iSup (f : ι → Ω → ℝ≥0∞) (μ : Measure Ω) :
    essSupFamily f μ ≤ fun ω ↦ ⨆ i, f i ω := by
  obtain ⟨C, -, hC⟩ := exists_countable_essSupFamily_eq f μ
  rw [hC]
  exact fun ω ↦ iSup₂_le fun i _ ↦ le_iSup (fun i ↦ f i ω) i

/-- The essential supremum of a family dominates every member almost everywhere as soon as some
sequence of members does. -/
private theorem ae_le_essSupFamily_of_exists
    (hs : ∃ s : ℕ → ι, ∀ i, f i ≤ᵐ[μ] fun ω ↦ ⨆ n, f (s n) ω) (i : ι) :
    f i ≤ᵐ[μ] essSupFamily f μ := by
  simp only [essSupFamily_def, hs, dite_true]
  exact hs.choose_spec i

/-- For an s-finite measure, the essential supremum of a family of almost everywhere measurable
functions dominates every member almost everywhere. -/
theorem ae_le_essSupFamily [SFinite μ] (hf : ∀ i, AEMeasurable (f i) μ) (i : ι) :
    f i ≤ᵐ[μ] essSupFamily f μ :=
  have : Nonempty ι := ⟨i⟩
  ae_le_essSupFamily_of_exists (exists_seq_forall_ae_le_iSup hf) i

/-- The essential supremum of a family is almost everywhere below every function that dominates
every member almost everywhere. -/
theorem essSupFamily_ae_le (hh : ∀ i, f i ≤ᵐ[μ] h) : essSupFamily f μ ≤ᵐ[μ] h := by
  obtain ⟨C, hC, hC_eq⟩ := exists_countable_essSupFamily_eq f μ
  have : Countable C := hC.to_subtype
  filter_upwards [ae_all_iff.2 fun i : C ↦ hh i] with ω hω
  rw [hC_eq]
  exact iSup₂_le fun i hi ↦ hω ⟨i, hi⟩

/-- For an s-finite measure and almost everywhere measurable members, a function dominates the
essential supremum of a family almost everywhere exactly when it dominates every member. -/
theorem essSupFamily_ae_le_iff [SFinite μ] (hf : ∀ i, AEMeasurable (f i) μ) :
    essSupFamily f μ ≤ᵐ[μ] h ↔ ∀ i, f i ≤ᵐ[μ] h :=
  ⟨fun hh i ↦ (ae_le_essSupFamily hf i).trans hh, essSupFamily_ae_le⟩

/-- For an s-finite measure and almost everywhere measurable members, the essential supremum of a
family is characterized up to null sets as the function that dominates every member almost
everywhere and is almost everywhere below every function that does. -/
theorem ae_eq_essSupFamily_iff [SFinite μ] (hf : ∀ i, AEMeasurable (f i) μ) :
    h =ᵐ[μ] essSupFamily f μ ↔
      (∀ i, f i ≤ᵐ[μ] h) ∧ ∀ h' : Ω → ℝ≥0∞, (∀ i, f i ≤ᵐ[μ] h') → h ≤ᵐ[μ] h' := by
  refine ⟨fun hh ↦ ⟨fun i ↦ (ae_le_essSupFamily hf i).trans hh.symm.le, fun h' hh' ↦
    hh.le.trans (essSupFamily_ae_le hh')⟩, fun ⟨hh, hmin⟩ ↦ ?_⟩
  exact (hmin _ (ae_le_essSupFamily hf)).antisymm (essSupFamily_ae_le hh)

/-- The essential supremum is monotone in the family, up to null sets. -/
theorem essSupFamily_mono_ae [SFinite μ] (hg : ∀ i, AEMeasurable (g i) μ)
    (hfg : ∀ i, f i ≤ᵐ[μ] g i) : essSupFamily f μ ≤ᵐ[μ] essSupFamily g μ :=
  essSupFamily_ae_le fun i ↦ (hfg i).trans (ae_le_essSupFamily hg i)

/-- The essential supremum of a family of functions that are measurable for a σ-algebra `m`,
for instance a sub-σ-algebra, is `m`-measurable. -/
theorem measurable_essSupFamily {m : MeasurableSpace Ω} (hf : ∀ i, Measurable[m] (f i)) :
    Measurable[m] (essSupFamily f μ) := by
  obtain ⟨C, hC, hC_eq⟩ := exists_countable_essSupFamily_eq f μ
  rw [hC_eq]
  exact Measurable.biSup C hC fun i _ ↦ hf i

/-- The essential supremum of a family of almost everywhere measurable functions is almost
everywhere measurable. -/
theorem aemeasurable_essSupFamily (hf : ∀ i, AEMeasurable (f i) μ) :
    AEMeasurable (essSupFamily f μ) μ := by
  obtain ⟨C, hC, hC_eq⟩ := exists_countable_essSupFamily_eq f μ
  rw [hC_eq]
  exact AEMeasurable.biSup C hC fun i _ ↦ hf i

/-- For an s-finite measure, the essential supremum of a nonempty family of almost everywhere
measurable functions is the supremum of a sequence of members. -/
theorem exists_seq_essSupFamily_eq [SFinite μ] [Nonempty ι] (hf : ∀ i, AEMeasurable (f i) μ) :
    ∃ s : ℕ → ι, essSupFamily f μ = fun ω ↦ ⨆ n, f (s n) ω := by
  have hs := exists_seq_forall_ae_le_iSup hf
  exact ⟨hs.choose, by simp only [essSupFamily_def, hs, dite_true]⟩

/-- The essential supremum of a countable family is almost everywhere its pointwise supremum,
for every measure and with no measurability assumption. -/
theorem essSupFamily_ae_eq_iSup [Countable ι] (f : ι → Ω → ℝ≥0∞) (μ : Measure Ω) :
    essSupFamily f μ =ᵐ[μ] fun ω ↦ ⨆ i, f i ω := by
  refine EventuallyLE.antisymm (ae_of_all μ (essSupFamily_le_iSup f μ)) ?_
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ae_of_all _ fun ω ↦ by simp
  obtain ⟨s, hs⟩ := exists_surjective_nat ι
  have hex : ∃ s : ℕ → ι, ∀ i, f i ≤ᵐ[μ] fun ω ↦ ⨆ n, f (s n) ω :=
    ⟨s, fun i ↦ ae_of_all _ fun ω ↦ by
      obtain ⟨n, rfl⟩ := hs i
      exact le_iSup (fun n ↦ f (s n) ω) n⟩
  filter_upwards [ae_all_iff.2 (ae_le_essSupFamily_of_exists hex)] with ω hω
  exact iSup_le hω

/-- For an s-finite measure, the essential supremum of a nonempty family of almost everywhere
measurable functions that is directed upward almost everywhere is almost everywhere the supremum
of an almost everywhere increasing sequence of members. -/
theorem exists_seq_monotone_ae_eq_essSupFamily [SFinite μ] [Nonempty ι]
    (hf : ∀ i, AEMeasurable (f i) μ) (hd : Directed (· ≤ᵐ[μ] ·) f) :
    ∃ s : ℕ → ι, (∀ᵐ ω ∂μ, Monotone fun n ↦ f (s n) ω) ∧
      essSupFamily f μ =ᵐ[μ] fun ω ↦ ⨆ n, f (s n) ω := by
  obtain ⟨u, hu⟩ := exists_seq_essSupFamily_eq hf
  choose j hj₁ hj₂ using hd
  -- `s (n + 1)` dominates both `s n` and `u (n + 1)`.
  let s : ℕ → ι := fun n ↦ Nat.rec (u 0) (fun k sk ↦ j sk (u (k + 1))) n
  have hs_succ (n : ℕ) : s (n + 1) = j (s n) (u (n + 1)) := rfl
  have hus (n : ℕ) : f (u n) ≤ᵐ[μ] f (s n) := by
    cases n with
    | zero => exact EventuallyLE.refl _ _
    | succ n => exact hs_succ n ▸ hj₂ _ _
  refine ⟨s, ?_, ?_⟩
  · filter_upwards [ae_all_iff.2 fun n ↦ hs_succ n ▸ hj₁ (s n) (u (n + 1))] with ω hω
    exact monotone_nat_of_le_succ hω
  · refine EventuallyLE.antisymm ?_ ?_
    · filter_upwards [ae_all_iff.2 hus] with ω hω
      rw [hu]
      exact iSup_mono hω
    · filter_upwards [ae_all_iff.2 fun n ↦ ae_le_essSupFamily hf (s n)] with ω hω
      exact iSup_le hω

/-- For an s-finite measure and a family of almost everywhere measurable functions directed upward
almost everywhere, the integral of the essential supremum over any set is the supremum of the
integrals of the members. -/
theorem setLIntegral_essSupFamily_of_directed [SFinite μ] (hf : ∀ i, AEMeasurable (f i) μ)
    (hd : Directed (· ≤ᵐ[μ] ·) f) (s : Set Ω) :
    ∫⁻ ω in s, essSupFamily f μ ω ∂μ = ⨆ i, ∫⁻ ω in s, f i ω ∂μ := by
  refine le_antisymm ?_ (iSup_le fun i ↦ lintegral_mono_ae
    (ae_restrict_of_ae (ae_le_essSupFamily hf i)))
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  obtain ⟨u, hmono, heq⟩ := exists_seq_monotone_ae_eq_essSupFamily hf hd
  rw [lintegral_congr_ae (ae_restrict_of_ae heq),
    lintegral_iSup' (fun n ↦ (hf (u n)).restrict) (ae_restrict_of_ae hmono)]
  exact iSup_le fun n ↦ le_iSup (fun i ↦ ∫⁻ ω in s, f i ω ∂μ) (u n)

end MeasureTheory
