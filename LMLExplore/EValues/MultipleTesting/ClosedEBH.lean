/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.MultipleTesting.EBH
public import LMLExplore.Data.Finset.Card
import LMLExplore.EValues.EVariable

/-!
# The closed e-BH procedure

Hypotheses are indexed by a finite type `ι` of cardinality `K`, with nulls
`H : ι → Set (Measure Ω)` and e-variables `E i` for `H i`, under arbitrary dependence. The mean
e-collection (`ProbabilityTheory.meanECollection`) assigns to each nonempty set `S` of hypotheses
the average `∑ i ∈ S, E i / #S` of its e-values, an e-variable for the intersection of the nulls
of `S`, the only admissible symmetric way of merging arbitrarily dependent e-values up to mixing
with the constant `1` [VW21]. Its e-closure for the false discovery proportion is the closed e-BH
procedure [XSF+26, §5.1]: the candidate family of the mean-consistent sets
(`ProbabilityTheory.IsMeanConsistent`), the rejection sets `R` with
`fdp S R ≤ α * ∑ i ∈ S, e i / #S` for every set `S`. By the e-Closure Principle, it controls the
false discovery rate at level `α` simultaneously over its members, so that any of them may be
chosen after seeing the data [XSF+26, Theorem 14].

Closed e-BH improves e-BH uniformly [XSF+26, Theorem 17]: every self-consistent set is
mean-consistent, in particular the e-BH rejection set, and for two hypotheses or more some
realization of the e-values makes a hypothesis mean-consistent while e-BH rejects nothing.

The largest mean-consistent sets can be taken among the hypotheses with the largest e-values
[XSF+26, Lemma 52], through the general exchange argument
`ProbabilityTheory.mem_eClosure_of_forall_le`: if a set of size `r` is mean-consistent, then so is
every set of `r` hypotheses with the largest e-values, whatever the order among ties. The closed
e-BH rejection set of [XSF+26, §5.1] is such a set of the largest size, with ties broken by the
index of the hypothesis. A largest mean-consistent set need not be unique [XSF+26, Example 23],
but every largest one made of the largest e-values contains the e-BH rejection set.

## Main definitions

* `ProbabilityTheory.meanECollection E`: the mean e-collection `S ↦ ∑ i ∈ S, E i / #S`.
* `ProbabilityTheory.IsMeanConsistent e α R`: the rejection set `R` is mean-consistent at level
  `α` for the e-values `e`, that is, belongs to the closed e-BH family.

## Main statements

* `ProbabilityTheory.isECollection_meanECollection`: the means of e-variables form an
  e-collection.
* `ProbabilityTheory.mem_eClosure_meanECollection_iff`: the e-closure of the mean e-collection for
  the false discovery proportion consists of the mean-consistent sets.
* `ProbabilityTheory.lintegral_biSup_isMeanConsistent_fdp_le`,
  `ProbabilityTheory.lintegral_biSup_isMeanConsistent_fdp_le_of_isEVar`: closed e-BH controls the
  false discovery rate simultaneously, at level `α * ∑ i ∈ N, ∫⁻ E i / #N` for every set `N` and
  every measure, hence at level `α` with e-variables, under every measure [XSF+26, Theorem 14].
* `ProbabilityTheory.IsSelfConsistent.isMeanConsistent`,
  `ProbabilityTheory.exists_eBH_eq_empty_isMeanConsistent_singleton`: closed e-BH improves e-BH
  uniformly [XSF+26, Theorem 17].
* `ProbabilityTheory.IsMeanConsistent.of_forall_le`,
  `ProbabilityTheory.exists_isMeanConsistent_forall_card_le`: the largest mean-consistent sets
  among the largest e-values [XSF+26, Lemma 52].
* `ProbabilityTheory.eBH_subset_of_forall_card_le`: such a largest set contains the e-BH rejection
  set.

## References

* [XSF+26] Z. Xu, A. Solari, L. Fischer, R. de Heide, A. Ramdas and J. Goeman, *Bringing closure
  to false discovery rate control: a general principle for multiple testing*,
  arXiv:2509.02517v3.
* [VW21] V. Vovk and R. Wang, *E-values: calibration, combination and applications*, Ann.
  Statist. 49 (2021), arXiv:1912.06116.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The mean e-collection -/

section MeanECollection

variable {E : ι → Ω → ℝ≥0∞}

/-- The **mean e-collection** of statistics `E i`: the statistic of a set `S` of hypotheses is the
average `∑ i ∈ S, E i / #S` of its e-values, and that of the empty set is `0` [XSF+26, §5.1]. -/
noncomputable def meanECollection (E : ι → Ω → ℝ≥0∞) (S : Finset ι) (ω : Ω) : ℝ≥0∞ :=
  (∑ i ∈ S, E i ω) / #S

theorem meanECollection_def (E : ι → Ω → ℝ≥0∞) (S : Finset ι) (ω : Ω) :
    meanECollection E S ω = (∑ i ∈ S, E i ω) / #S := (rfl)

@[simp]
theorem meanECollection_empty (E : ι → Ω → ℝ≥0∞) : meanECollection E ∅ = 0 := by
  ext ω
  simp [meanECollection_def]

@[simp]
theorem meanECollection_singleton (E : ι → Ω → ℝ≥0∞) (i : ι) (ω : Ω) :
    meanECollection E {i} ω = E i ω := by
  simp [meanECollection_def]

/-- The mean of measurable statistics is measurable. -/
theorem measurable_meanECollection (hE : ∀ i, Measurable (E i)) (S : Finset ι) :
    Measurable (meanECollection E S) :=
  (Finset.measurable_sum S fun i _ ↦ hE i).div_const _

/-- The mean e-collection is symmetric and nondecreasing in the e-values: replacing a member of a
set by a hypothesis with a larger e-value does not decrease the mean. -/
theorem meanECollection_insert_le_insert [DecidableEq ι] {S : Finset ι} {i j : ι} {ω : Ω}
    (hi : i ∉ S) (hj : j ∉ S) (hij : E i ω ≤ E j ω) :
    meanECollection E (insert i S) ω ≤ meanECollection E (insert j S) ω := by
  rw [meanECollection_def, meanECollection_def, sum_insert hi, sum_insert hj,
    card_insert_of_notMem hi, card_insert_of_notMem hj]
  gcongr

/-- The mean of e-variables `E i` for the hypotheses `i ∈ S` is an e-variable for the
intersection of their nulls. -/
theorem isEVar_meanECollection {H : ι → Set (Measure Ω)} {S : Finset ι}
    (hE : ∀ i ∈ S, IsEVar (E i) (H i)) :
    IsEVar (meanECollection E S) (⋂ i ∈ S, H i) := by
  have h := isEVar_finsetSum_mul (S := ⋂ i ∈ S, H i) S
    (fun i hi ↦ (hE i hi).anti_set (Set.biInter_subset_of_mem hi))
    (w := fun _ ↦ (#S : ℝ≥0∞)⁻¹) (by
      rw [sum_const, nsmul_eq_mul]
      exact ENNReal.mul_inv_le_one _)
  convert h using 1
  funext ω
  rw [meanECollection_def, ENNReal.sum_div]
  exact sum_congr rfl fun i _ ↦ ENNReal.div_eq_inv_mul

/-- **The means of e-variables form an e-collection** [XSF+26, §5.1]. -/
theorem isECollection_meanECollection [Fintype ι] {H : ι → Set (Measure Ω)}
    (hE : ∀ i, IsEVar (E i) (H i)) : IsECollection (meanECollection E) H :=
  IsECollection.of_isEVar (fun _ _ ↦ isEVar_meanECollection fun i _ ↦ hE i)
    (meanECollection_empty E)

end MeanECollection

/-! ### Mean-consistent sets -/

section MeanConsistent

variable [DecidableEq ι] {e e' : ι → ℝ≥0∞} {α α' : ℝ≥0∞} {R T : Finset ι}

/-- A rejection set `R` is **mean-consistent** at level `α` for the e-values `e` [XSF+26, §5.1]
when `fdp S R ≤ α * ∑ i ∈ S, e i / #S` for every set `S` of hypotheses: `R` belongs to the
e-closure of the mean e-collection for the false discovery proportion, the candidate family of
the closed e-BH procedure. -/
def IsMeanConsistent (e : ι → ℝ≥0∞) (α : ℝ≥0∞) (R : Finset ι) : Prop :=
  ∀ S, fdp S R ≤ α * ((∑ i ∈ S, e i) / #S)

theorem isMeanConsistent_iff :
    IsMeanConsistent e α R ↔ ∀ S, fdp S R ≤ α * ((∑ i ∈ S, e i) / #S) := Iff.rfl

/-- **The closed e-BH family is the e-closure of the mean e-collection** for the false discovery
proportion. -/
theorem mem_eClosure_meanECollection_iff {E : ι → Ω → ℝ≥0∞} {ω : Ω} :
    R ∈ eClosure fdp α (meanECollection E) ω ↔ IsMeanConsistent (E · ω) α R := by
  simp only [mem_eClosure, isMeanConsistent_iff, meanECollection_def]

@[simp]
theorem isMeanConsistent_empty : IsMeanConsistent e α ∅ := fun S ↦ by simp

/-- Mean-consistency is monotone in the level and in the e-values. -/
theorem IsMeanConsistent.mono (h : IsMeanConsistent e α R) (hα : α ≤ α') (he : e ≤ e') :
    IsMeanConsistent e' α' R := fun S ↦ (h S).trans (by gcongr; exact he _)

/-- **Self-consistent sets are mean-consistent** [XSF+26, Theorem 17]. -/
theorem IsSelfConsistent.isMeanConsistent [Fintype ι] (h : IsSelfConsistent e α R) :
    IsMeanConsistent e α R := fun S ↦ by
  refine (h.fdp_le S).trans ?_
  rw [← ENNReal.sum_div]
  gcongr
  exact card_le_univ S

/-- **The e-BH rejection set is mean-consistent**: closed e-BH improves e-BH in simultaneity
[XSF+26, Theorem 17]. -/
theorem isMeanConsistent_eBH [Fintype ι] : IsMeanConsistent e α (eBH e α) :=
  isSelfConsistent_eBH.isMeanConsistent

section Example

variable [Fintype ι] {i₀ i₁ : ι} {x : ι → ℝ≥0∞}

omit [DecidableEq ι] in
/-- In the example of `exists_eBH_eq_empty_isMeanConsistent_singleton`, with values
`x = α * e` equal to `K - 1/2` at `i₀`, `1/2` at `i₁` and `0` elsewhere, e-BH rejects nothing: a
nonempty self-consistent set would consist of `i₀` and `i₁`, and neither can be rejected. -/
private lemma eBH_div_eq_empty (h : i₀ ≠ i₁) (hα₀ : α ≠ 0) (hα : α ≠ ∞)
    (hx₀ : x i₀ = Fintype.card ι - 2⁻¹) (hx₁ : x i₁ = 2⁻¹) (hx : ∀ i, i ≠ i₀ → i ≠ i₁ → x i = 0) :
    eBH (fun i ↦ x i / α) α = ∅ := by
  classical
  have hK : 2 ≤ Fintype.card ι := Fintype.one_lt_card_iff.2 ⟨i₀, i₁, h⟩
  have hK2 : (2 : ℝ≥0∞) ≤ Fintype.card ι := by exact_mod_cast hK
  refine eq_empty_of_forall_notMem fun i hi ↦ ?_
  obtain ⟨R, hR, hiR⟩ := mem_eBH_iff_exists.1 hi
  have hR' (j : ι) (hj : j ∈ R) : (Fintype.card ι : ℝ≥0∞) ≤ #R * x j := by
    have := isSelfConsistent_iff.1 hR j hj
    rwa [mul_comm α, mul_assoc, ENNReal.mul_div_cancel hα₀ hα] at this
  have hmem (j : ι) (hj : j ∈ R) : j = i₀ ∨ j = i₁ := by
    by_contra! hne
    have := hR' j hj
    rw [hx j hne.1 hne.2, mul_zero, nonpos_iff_eq_zero, Nat.cast_eq_zero] at this
    omega
  by_cases hi₁ : i₁ ∈ R
  · -- The hypothesis `i₁` would need `K ≤ #R / 2 ≤ 1`.
    have hcard : #R ≤ 2 := (card_le_card fun j hj ↦ by simpa using hmem j hj).trans card_le_two
    have := (hR' i₁ hi₁).trans (mul_le_mul' (Nat.cast_le.2 hcard) le_rfl)
    rw [hx₁, Nat.cast_ofNat, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top] at this
    exact absurd (hK2.trans this) (by norm_num)
  · -- The set would be `{i₀}`, which needs `K ≤ K - 1/2`.
    have hi₀R : i₀ ∈ R := ((hmem i hiR).resolve_right fun h' ↦ hi₁ (h' ▸ hiR)) ▸ hiR
    have hRi : R = {i₀} := eq_singleton_iff_unique_mem.2
      ⟨hi₀R, fun j hj ↦ (hmem j hj).resolve_right fun h' ↦ hi₁ (h' ▸ hj)⟩
    have := hR' i₀ hi₀R
    rw [hRi, card_singleton, Nat.cast_one, one_mul, hx₀] at this
    exact absurd this (not_le.2 (ENNReal.sub_lt_self (ENNReal.natCast_ne_top _)
      (Nat.cast_ne_zero.2 (by omega)) (by simp)))

/-- In the example of `exists_eBH_eq_empty_isMeanConsistent_singleton`, the set `{i₀}` is
mean-consistent: every set `S ∋ i₀` has `#S ≤ ∑ i ∈ S, x i`, which is `K` when `i₁ ∈ S` and
`K - 1/2 ≥ #S` otherwise. -/
private lemma isMeanConsistent_div_singleton (h : i₀ ≠ i₁) (hα₀ : α ≠ 0) (hα : α ≠ ∞)
    (hx₀ : x i₀ = Fintype.card ι - 2⁻¹) (hx₁ : x i₁ = 2⁻¹) :
    IsMeanConsistent (fun i ↦ x i / α) α {i₀} := fun S ↦ by
  have hhalf : (2 : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.2 one_le_two
  by_cases hS : i₀ ∈ S
  · have hfdp : fdp S {i₀} = 1 := by simp [fdp_def, hS]
    rw [hfdp, ← ENNReal.sum_div, ← mul_div_assoc, ENNReal.mul_div_cancel hα₀ hα,
      ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.2 (card_ne_zero_of_mem hS)))
        (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
    by_cases hS₁ : i₁ ∈ S
    · have hK : (1 : ℝ≥0∞) ≤ Fintype.card ι := Nat.one_le_cast.2 (card_pos.2 ⟨i₀, hS⟩
        |>.trans_le (card_le_univ S))
      calc (#S : ℝ≥0∞) ≤ Fintype.card ι := by exact_mod_cast card_le_univ S
        _ = x i₀ + x i₁ := by rw [hx₀, hx₁, tsub_add_cancel_of_le (hhalf.trans hK)]
        _ = ∑ i ∈ {i₀, i₁}, x i := (sum_pair h).symm
        _ ≤ ∑ i ∈ S, x i := sum_le_sum_of_subset (insert_subset hS (singleton_subset_iff.2 hS₁))
    · have hlt : #S + 1 ≤ Fintype.card ι := by
        rw [← card_univ]
        exact card_lt_card ((ssubset_iff_of_subset (subset_univ S)).2 ⟨i₁, mem_univ _, hS₁⟩)
      calc (#S : ℝ≥0∞) ≤ Fintype.card ι - 2⁻¹ := by
            refine ENNReal.le_sub_of_add_le_right (by simp) ?_
            calc (#S : ℝ≥0∞) + 2⁻¹ ≤ #S + 1 := by gcongr
              _ ≤ Fintype.card ι := by exact_mod_cast hlt
        _ = x i₀ := hx₀.symm
        _ ≤ ∑ i ∈ S, x i := single_le_sum (fun _ _ ↦ zero_le) hS
  · simp [fdp_def, hS]

/-- **Closed e-BH improves e-BH strictly** [XSF+26, Theorem 17]: for two distinct hypotheses
`i₀` and `i₁` and a level `α ∉ {0, ∞}`, some e-values make `{i₀}` mean-consistent while e-BH
rejects nothing. They are `e i₀ = (K - 1/2) / α`, `e i₁ = 1 / (2 α)` and `e i = 0` otherwise. -/
theorem exists_eBH_eq_empty_isMeanConsistent_singleton (h : i₀ ≠ i₁) (hα₀ : α ≠ 0)
    (hα : α ≠ ∞) : ∃ e : ι → ℝ≥0∞, eBH e α = ∅ ∧ IsMeanConsistent e α {i₀} := by
  obtain ⟨x, hx₀, hx₁, hx⟩ : ∃ x : ι → ℝ≥0∞, x i₀ = Fintype.card ι - 2⁻¹ ∧ x i₁ = 2⁻¹ ∧
      ∀ i, i ≠ i₀ → i ≠ i₁ → x i = 0 :=
    ⟨Pi.single i₀ ((Fintype.card ι : ℝ≥0∞) - 2⁻¹) + Pi.single i₁ 2⁻¹, by simp [h.symm],
      by simp [h], fun i h₀ h₁ ↦ by simp [h₀, h₁]⟩
  exact ⟨fun i ↦ x i / α, eBH_div_eq_empty h hα₀ hα hx₀ hx₁ hx,
    isMeanConsistent_div_singleton h hα₀ hα hx₀ hx₁⟩

end Example

/-- **The largest mean-consistent sets among the largest e-values** [XSF+26, Lemma 52]: if a set
`R` is mean-consistent, then so is every set `T` of the same size whose e-values are at least
those outside it, whatever the order among ties. -/
theorem IsMeanConsistent.of_forall_le (h : IsMeanConsistent e α R) (hT : #T = #R)
    (hTe : ∀ i ∈ T, ∀ j ∉ T, e j ≤ e i) : IsMeanConsistent e α T :=
  mem_eClosure_meanECollection_iff.1 <|
    mem_eClosure_of_forall_le (Ω := Unit) (e := meanECollection fun i _ ↦ e i) (ω := ())
      (fun _ _ _ _ _ hR hNR ↦ fdp_le_fdp hR hNR)
      (fun _ _ _ hi hj hij ↦ meanECollection_insert_le_insert hi hj hij)
      (mem_eClosure_meanECollection_iff.2 h) hT hTe

/-- **Closed e-BH** [XSF+26, §5.1, Lemma 52]: some mean-consistent set has the largest size among
the mean-consistent sets and consists of the hypotheses with the largest e-values. -/
theorem exists_isMeanConsistent_forall_card_le [Finite ι] (e : ι → ℝ≥0∞) (α : ℝ≥0∞) :
    ∃ T, IsMeanConsistent e α T ∧ (∀ R, IsMeanConsistent e α R → #R ≤ #T) ∧
      ∀ i ∈ T, ∀ j ∉ T, e j ≤ e i := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨R, hR, hRmax⟩ := exists_max_image ({R | IsMeanConsistent e α R} : Finset (Finset ι))
    card ⟨∅, by simp⟩
  obtain ⟨T, -, hT, hTe⟩ := exists_subset_card_eq_forall_le e (card_le_univ R)
  refine ⟨T, ((mem_filter.1 hR).2).of_forall_le hT fun i hi j hj ↦ hTe i hi j (by simpa),
    fun R' hR' ↦ hT ▸ hRmax R' (by simpa using hR'), fun i hi j hj ↦ hTe i hi j (by simpa)⟩

/-- **A largest mean-consistent set among the largest e-values contains the e-BH rejection
set**: closed e-BH improves e-BH in power [XSF+26, Theorem 17]. -/
theorem eBH_subset_of_forall_card_le [Fintype ι]
    (hT : ∀ R, IsMeanConsistent e α R → #R ≤ #T) (hTe : ∀ i ∈ T, ∀ j ∉ T, e j ≤ e i) :
    eBH e α ⊆ T := by
  intro i hi
  by_contra hiT
  -- Every member of `T` has an e-value at least that of `i`, so is rejected by e-BH.
  have hsub : T ⊆ eBH e α := fun j hj ↦ mem_eBH_iff_le_mul_card.2
    ((mem_eBH_iff_le_mul_card.1 hi).trans (by gcongr; exact hTe j hj i hiT))
  exact absurd (hT _ isMeanConsistent_eBH)
    (not_le.2 (card_lt_card ⟨hsub, fun h ↦ hiT (h hi)⟩))

end MeanConsistent

/-! ### False discovery rate control -/

section FDR

variable [DecidableEq ι] {E : ι → Ω → ℝ≥0∞} {α : ℝ≥0∞}

/-- **Closed e-BH controls the false discovery rate simultaneously** [XSF+26, Theorem 14]: for
statistics `E i` almost everywhere measurable for a measure `P` and every set `N` of hypotheses,
the expected largest false discovery proportion of a mean-consistent set is at most
`α * ∑ i ∈ N, ∫⁻ E i / #N`. -/
theorem lintegral_biSup_isMeanConsistent_fdp_le {P : Measure Ω}
    (hE : ∀ i, AEMeasurable (E i) P) (N : Finset ι) :
    ∫⁻ ω, ⨆ (R) (_ : IsMeanConsistent (E · ω) α R), fdp N R ∂P ≤
      α * ((∑ i ∈ N, ∫⁻ ω, E i ω ∂P) / #N) := by
  simp_rw [← mem_eClosure_meanECollection_iff]
  refine (lintegral_biSup_eClosure_le_mul_lintegral fdp α
    ((Finset.aemeasurable_fun_sum N fun i _ ↦ hE i).div_const _)).trans_eq ?_
  simp_rw [meanECollection_def, ← lintegral_finsetSum_div fun i _ ↦ hE i, ENNReal.sum_div]

/-- **Closed e-BH controls the false discovery rate at level `α` simultaneously** for
e-variables, under arbitrary dependence [XSF+26, Theorem 14]: for every measure `P`, the
expected largest false discovery proportion of a mean-consistent set, with the true nulls of `P`,
is at most `α`, so that the rejection set may be chosen among the mean-consistent sets after
seeing the data. -/
theorem lintegral_biSup_isMeanConsistent_fdp_le_of_isEVar [Fintype ι] {H : ι → Set (Measure Ω)}
    (hE : ∀ i, IsEVar (E i) (H i)) (α : ℝ≥0∞) (P : Measure Ω) :
    ∫⁻ ω, ⨆ (R) (_ : IsMeanConsistent (E · ω) α R), fdp (trueNulls H P) R ∂P ≤ α := by
  refine (lintegral_biSup_isMeanConsistent_fdp_le (fun i ↦ (hE i).measurable.aemeasurable)
    _).trans (mul_le_of_le_one_right' (ENNReal.div_le_of_le_mul ?_))
  rw [one_mul, ← nsmul_one, ← sum_const]
  exact sum_le_sum fun i hi ↦ (hE i).lintegral_le_one (mem_trueNulls.1 hi)

end FDR

end ProbabilityTheory
