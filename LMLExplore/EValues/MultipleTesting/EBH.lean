/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.MultipleTesting.EClosure
public import LMLExplore.MeasureTheory.Integral.Lebesgue.Add

/-!
# Compound e-variables and the e-BH procedure

Hypotheses are indexed by a finite type `ι` of cardinality `K`, with nulls
`H : ι → Set (Measure Ω)`. Statistics `E i : Ω → ℝ≥0∞` are compound e-variables
(`ProbabilityTheory.IsCompoundEVar`) when the expectations of the statistics of the true nulls sum
to at most `K` under every probability measure [IWR, Definition 2.1; RW, Definition 9.1]:
e-variables for the hypotheses `H i` are compound e-variables, but a compound e-variable need not
be an e-variable. The means `S ↦ ∑ i ∈ S, E i / K` of statistics form an e-collection exactly when
the statistics are compound e-variables [XSF+26, Proposition 24], so that the procedures of this
file are instances of the e-Closure Principle of `LMLExplore.EValues.MultipleTesting.EClosure`.

A set `R` of hypotheses is self-consistent at level `α` for realized values `e : ι → ℝ≥0∞`
(`ProbabilityTheory.IsSelfConsistent`) when `K ≤ α * #R * e i` for every `i ∈ R`; for a level
`α ∉ {0, ∞}`, this says that every rejected e-value is at least `K / (α * #R)` [WR22, §5; RW,
Definition 9.9]. Every self-consistent
set belongs to the e-closure of the mean e-collection for the false discovery proportion. Hence
every self-consistent rejection procedure has false discovery rate at most
`α * (∑ i ∈ N, ∫⁻ E i) / K` for the true nulls `N`, so at most `α` for compound e-variables and at
most `α * #N / K` for e-variables, whatever their dependence; the bound holds post hoc, uniformly
over the levels [RW, Theorem 9.11; WR22, Proposition 2; IWR, Theorem 4.3].

The e-BH procedure (`ProbabilityTheory.eBH`) [WR22, (5); RW, Definition 9.8] rejects the
hypotheses `i` with `K ≤ α * k* * e i`, for the largest `k* ≤ K` such that at least `k*`
hypotheses `j` satisfy `K ≤ α * k* * e j`; for a level `α ∉ {0, ∞}` and `k* ≠ 0`, these are the
hypotheses whose e-values are at least `K / (α * k*)`. It rejects `k*` hypotheses, and it is the
largest self-consistent set and the union of all of them. Conversely, every measurable rejection
procedure `R` that controls the false discovery rate at a level `α ∉ {0, ∞}` is the e-BH procedure
applied to its universal compound e-values `K * 𝟙{i ∈ R} / (α * max #R 1)` [IWR, Theorem 4.4; RW,
Theorems 9.18–9.19].

## Main definitions

* `ProbabilityTheory.IsCompoundEVar E H`: the statistics `E i` are compound e-variables for the
  hypotheses `H`.
* `ProbabilityTheory.IsSelfConsistent e α R`: the rejection set `R` is self-consistent at level
  `α` for the e-values `e`.
* `ProbabilityTheory.eBH e α`: the rejection set of the e-BH procedure at level `α`.
* `ProbabilityTheory.universalEValue α R`: the universal compound e-values of a rejection set.

## Main statements

* `ProbabilityTheory.isECollection_sum_div_iff`: the means of statistics form an e-collection
  exactly when the statistics are compound e-variables [XSF+26, Proposition 24].
* `ProbabilityTheory.IsECollection.isCompoundEVar_of_ae_sum_le`,
  `ProbabilityTheory.sum_universalEValue_le_of_mem_eClosure`: statistics dominated by an
  e-collection are compound e-variables, and the universal compound e-values of a member of an
  e-closure are dominated [XSF+26, Proposition 26].
* `ProbabilityTheory.IsSelfConsistent.mem_eClosure`: a self-consistent set belongs to the
  e-closure of the mean e-collection for the false discovery proportion.
* `ProbabilityTheory.isGreatest_eBH`, `ProbabilityTheory.mem_eBH_iff_exists`: e-BH is the largest
  self-consistent set and the union of all of them [WR22, §5]; it makes a rejection exactly when
  some nonempty set is self-consistent (`ProbabilityTheory.eBH_nonempty_iff`).
* `ProbabilityTheory.card_eBH`, `ProbabilityTheory.mem_eBH_iff_le_mul_card`: the number of
  rejections of e-BH, and its threshold form [WR22, Proposition 1].
* `ProbabilityTheory.mem_eBH_iff_one_le_mul`: for one hypothesis, e-BH is the e-test.
* `ProbabilityTheory.isSelfConsistent_div_iff`, `ProbabilityTheory.eBH_div`: dividing the level
  by `c` is dividing the e-values by `c`.
* `ProbabilityTheory.eBH_zero`, `ProbabilityTheory.eBH_mono`,
  `ProbabilityTheory.mem_eBH_comp_equiv`, `ProbabilityTheory.card_eBH_comp_equiv`,
  `ProbabilityTheory.eBH_comp_equiv_nonempty`: e-BH rejects nothing at level `0`, is monotone in
  the level and the e-values, and commutes with relabelling the hypotheses.
* `ProbabilityTheory.measurable_eBH`, `ProbabilityTheory.measurable_eBH_id`,
  `ProbabilityTheory.measurable_card_eBH`: e-BH and its number of rejections are measurable.
* `ProbabilityTheory.lintegral_iSup_fdp_div_le_of_isSelfConsistent`,
  `ProbabilityTheory.lintegral_fdp_le_of_isSelfConsistent`: the post-hoc and fixed-level bounds
  on the false discovery rate of self-consistent procedures.
* `ProbabilityTheory.IsCompoundEVar.lintegral_iSup_fdp_div_le_one`,
  `ProbabilityTheory.IsCompoundEVar.lintegral_fdp_le`,
  `ProbabilityTheory.lintegral_iSup_fdp_div_le_of_isEVar`,
  `ProbabilityTheory.lintegral_fdp_le_of_isEVar`: false discovery rate control by self-consistent
  procedures with compound e-variables and with e-variables [RW, Theorem 9.11; WR22,
  Proposition 2; IWR, Theorem 4.3].
* `ProbabilityTheory.IsCompoundEVar.lintegral_fdp_eBH_le`,
  `ProbabilityTheory.lintegral_fdp_eBH_le_of_isEVar`: false discovery rate control by e-BH
  [WR22, Theorem 2; IWR, Theorem 4.3].
* `ProbabilityTheory.isCompoundEVar_universalEValue`,
  `ProbabilityTheory.forall_lintegral_fdp_le_iff_exists_isCompoundEVar`: the universal compound
  e-values of a procedure that controls the false discovery rate, and the universality of e-BH
  with compound e-variables [IWR, Theorem 4.4; RW, Theorems 9.18–9.19].

## References

* [WR22] R. Wang and A. Ramdas, *False discovery rate control with e-values*, J. R. Stat. Soc.
  Ser. B 84 (2022), arXiv:2009.02824v5.
* [IWR] N. Ignatiadis, R. Wang and A. Ramdas, *Asymptotic and compound e-values: multiple testing
  and empirical Bayes*, arXiv:2409.19812v4.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6.
* [XSF+26] Z. Xu, A. Solari, L. Fischer, R. de Heide, A. Ramdas and J. Goeman, *Bringing closure
  to false discovery rate control: a general principle for multiple testing*,
  arXiv:2509.02517v3.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω} [Fintype ι]

/-- The number of hypotheses is nonzero as soon as there is one. -/
private lemma natCast_card_ne_zero (i : ι) : (Fintype.card ι : ℝ≥0∞) ≠ 0 :=
  haveI : Nonempty ι := ⟨i⟩
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

/-! ### Self-consistent rejection sets -/

section SelfConsistent

variable {e e' : ι → ℝ≥0∞} {α α' : ℝ≥0∞} {R R' : Finset ι}

/-- A rejection set `R` is **self-consistent** at level `α` for the e-values `e` [WR22, §5; RW,
Definition 9.9] when `K ≤ α * #R * e i` for every `i ∈ R`, with `K` the number of hypotheses. For
a level `α ∉ {0, ∞}`, this says that every rejected e-value is at least `K / (α * #R)`. -/
def IsSelfConsistent (e : ι → ℝ≥0∞) (α : ℝ≥0∞) (R : Finset ι) : Prop :=
  ∀ i ∈ R, (Fintype.card ι : ℝ≥0∞) ≤ α * #R * e i

theorem isSelfConsistent_iff :
    IsSelfConsistent e α R ↔ ∀ i ∈ R, (Fintype.card ι : ℝ≥0∞) ≤ α * #R * e i :=
  Iff.rfl

@[simp]
theorem isSelfConsistent_empty : IsSelfConsistent e α ∅ := by
  simp [isSelfConsistent_iff]

/-- Self-consistency is preserved by raising the level and the e-values. -/
theorem IsSelfConsistent.mono (h : IsSelfConsistent e α R) (hα : α ≤ α') (he : e ≤ e') :
    IsSelfConsistent e' α' R :=
  fun i hi ↦ (h i hi).trans (by gcongr; exact he i)

/-- **Dividing the level is dividing the e-values**: a set is self-consistent at level `α / c`
for the e-values `e` exactly when it is self-consistent at level `α` for the e-values `e i / c`.
-/
theorem isSelfConsistent_div_iff {c : ℝ≥0∞} :
    IsSelfConsistent e (α / c) R ↔ IsSelfConsistent (fun i ↦ e i / c) α R := by
  simp only [isSelfConsistent_iff, div_eq_mul_inv, mul_right_comm α c⁻¹, mul_assoc, mul_comm c⁻¹]

/-- The union of two self-consistent sets is self-consistent. -/
theorem IsSelfConsistent.union [DecidableEq ι] (h : IsSelfConsistent e α R)
    (h' : IsSelfConsistent e α R') : IsSelfConsistent e α (R ∪ R') := by
  intro i hi
  rcases mem_union.1 hi with hi | hi
  · exact (h i hi).trans (by gcongr; exact subset_union_left)
  · exact (h' i hi).trans (by gcongr; exact subset_union_right)

/-- **The false discovery proportion of a self-consistent set** [WR22, (12)]: for every set `N`
of hypotheses, `fdp N R ≤ α * ∑ i ∈ N, e i / K`. Each rejected hypothesis of `N` contributes
`1 / #R ≤ α * e i / K`. -/
theorem IsSelfConsistent.fdp_le [DecidableEq ι] (h : IsSelfConsistent e α R) (N : Finset ι) :
    fdp N R ≤ α * ∑ i ∈ N, e i / Fintype.card ι := by
  rcases R.eq_empty_or_nonempty with rfl | hR
  · simp
  obtain ⟨j, hj⟩ := hR
  have hR0 : (#R : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (card_ne_zero_of_mem hj)
  -- Each rejected hypothesis contributes `1 / #R`, at most `α * e i / K` by self-consistency.
  have hi : ∀ i ∈ R, (#R : ℝ≥0∞)⁻¹ ≤ α * (e i / Fintype.card ι) := fun i hi ↦
    calc (#R : ℝ≥0∞)⁻¹ = (#R : ℝ≥0∞)⁻¹ * Fintype.card ι / Fintype.card ι :=
          (ENNReal.mul_div_cancel_right (natCast_card_ne_zero j) (ENNReal.natCast_ne_top _)).symm
      _ ≤ (#R : ℝ≥0∞)⁻¹ * (α * #R * e i) / Fintype.card ι := by gcongr; exact h i hi
      _ = (#R : ℝ≥0∞)⁻¹ * #R * (α * e i) / Fintype.card ι := by ac_rfl
      _ = α * (e i / Fintype.card ι) := by
          rw [ENNReal.inv_mul_cancel hR0 (ENNReal.natCast_ne_top _), one_mul, mul_div_assoc]
  calc fdp N R = ∑ _ ∈ R ∩ N, (#R : ℝ≥0∞)⁻¹ := fdp_eq_sum_inv_card N R
    _ ≤ ∑ i ∈ R ∩ N, α * (e i / Fintype.card ι) :=
        sum_le_sum fun i hi' ↦ hi i (mem_inter.1 hi').1
    _ ≤ ∑ i ∈ N, α * (e i / Fintype.card ι) :=
        sum_le_sum_of_subset inter_subset_right
    _ = α * ∑ i ∈ N, e i / Fintype.card ι := (mul_sum ..).symm

/-- **Self-consistent sets belong to the e-closure** of the mean e-collection
`S ↦ ∑ i ∈ S, E i / K` for the false discovery proportion. -/
theorem IsSelfConsistent.mem_eClosure [DecidableEq ι] {E : ι → Ω → ℝ≥0∞} {ω : Ω}
    (h : IsSelfConsistent (E · ω) α R) :
    R ∈ eClosure fdp α (fun S ω ↦ ∑ i ∈ S, E i ω / Fintype.card ι) ω :=
  ProbabilityTheory.mem_eClosure.2 fun S ↦ h.fdp_le S

end SelfConsistent

/-! ### The e-BH procedure -/

section EBH

variable {e : ι → ℝ≥0∞} {α : ℝ≥0∞} {R : Finset ι} {i : ι}

/-- **The e-BH procedure** at level `α` for the e-values `e` [WR22, (5); RW, Definition 9.8]:
with `K` the number of hypotheses and `k*` the largest `k ≤ K` such that at least `k` hypotheses
`j` satisfy `K ≤ α * k * e j`, it rejects the hypotheses `i` with `K ≤ α * k* * e i`. For a level
`α ∉ {0, ∞}` and `k* ≠ 0`, these are the hypotheses whose e-values are at least `K / (α * k*)`,
and the condition on `k ≠ 0` is the condition `k * e[k] / K ≥ 1 / α` of [WR22, (5)] on the
`k`-th largest e-value `e[k]`, written without order statistics. e-BH rejects `k*` hypotheses
(`card_eBH`). -/
noncomputable def eBH (e : ι → ℝ≥0∞) (α : ℝ≥0∞) : Finset ι :=
  ({i | (Fintype.card ι : ℝ≥0∞) ≤ α * (Nat.findGreatest
    (fun k ↦ k ≤ #{j | (Fintype.card ι : ℝ≥0∞) ≤ α * k * e j}) (Fintype.card ι) : ℕ) * e i} :
    Finset ι)

theorem eBH_def (e : ι → ℝ≥0∞) (α : ℝ≥0∞) :
    eBH e α = ({i | (Fintype.card ι : ℝ≥0∞) ≤ α * (Nat.findGreatest
      (fun k ↦ k ≤ #{j | (Fintype.card ι : ℝ≥0∞) ≤ α * k * e j}) (Fintype.card ι) : ℕ) * e i} :
      Finset ι) :=
  (rfl)

/-- The number `k*` of rejections of e-BH bounds every self-consistent set: at least `#R`
hypotheses `j` of a self-consistent `R` satisfy `K ≤ α * #R * e j`. -/
private lemma card_le_findGreatest (h : IsSelfConsistent e α R) :
    #R ≤ Nat.findGreatest
      (fun k ↦ k ≤ #{j | (Fintype.card ι : ℝ≥0∞) ≤ α * k * e j}) (Fintype.card ι) :=
  Nat.le_findGreatest (card_le_univ R)
    (card_le_card fun j hj ↦ mem_filter.2 ⟨mem_univ j, h j hj⟩)

/-- At least `k*` hypotheses `j` satisfy `K ≤ α * k* * e j`, for the number `k*` of rejections of
e-BH. -/
private lemma findGreatest_le_card_filter :
    Nat.findGreatest (fun k ↦ k ≤ #{j | (Fintype.card ι : ℝ≥0∞) ≤ α * k * e j}) (Fintype.card ι) ≤
      #{j | (Fintype.card ι : ℝ≥0∞) ≤ α * (Nat.findGreatest
        (fun k ↦ k ≤ #{j | (Fintype.card ι : ℝ≥0∞) ≤ α * k * e j}) (Fintype.card ι) : ℕ) * e j} :=
  Nat.findGreatest_spec (P := fun k ↦ k ≤ #{j | (Fintype.card ι : ℝ≥0∞) ≤ α * k * e j})
    (Nat.zero_le _) (Nat.zero_le _)

/-- A self-consistent set is contained in the e-BH rejection set. -/
theorem IsSelfConsistent.subset_eBH (h : IsSelfConsistent e α R) : R ⊆ eBH e α := by
  intro i hi
  rw [eBH_def, mem_filter]
  exact ⟨mem_univ i, (h i hi).trans (by gcongr; exact card_le_findGreatest h)⟩

/-- The e-BH rejection set is self-consistent. -/
theorem isSelfConsistent_eBH : IsSelfConsistent e α (eBH e α) := by
  intro i hi
  rw [eBH_def, mem_filter] at hi
  refine hi.2.trans ?_
  gcongr
  exact findGreatest_le_card_filter

/-- **e-BH is the largest self-consistent set** [WR22, §5; RW, Definition 9.9]. -/
theorem isGreatest_eBH : IsGreatest {R | IsSelfConsistent e α R} (eBH e α) :=
  ⟨isSelfConsistent_eBH, fun _ h ↦ h.subset_eBH⟩

/-- **e-BH is the union of all self-consistent sets**: it rejects `i` exactly when some
self-consistent set contains `i`. -/
theorem mem_eBH_iff_exists : i ∈ eBH e α ↔ ∃ R, IsSelfConsistent e α R ∧ i ∈ R :=
  ⟨fun hi ↦ ⟨_, isSelfConsistent_eBH, hi⟩, fun ⟨_, h, hi⟩ ↦ h.subset_eBH hi⟩

/-- **e-BH makes a rejection exactly when some nonempty set is self-consistent.** -/
theorem eBH_nonempty_iff : (eBH e α).Nonempty ↔ ∃ R, R.Nonempty ∧ IsSelfConsistent e α R :=
  ⟨fun h ↦ ⟨_, h, isSelfConsistent_eBH⟩, fun ⟨_, hR, h⟩ ↦ Finset.Nonempty.mono h.subset_eBH hR⟩

/-- **The number of rejections of e-BH** is `k*`, the largest `k ≤ K` such that at least `k`
hypotheses `j` satisfy `K ≤ α * k * e j`. -/
theorem card_eBH : #(eBH e α) = Nat.findGreatest
    (fun k ↦ k ≤ #{j | (Fintype.card ι : ℝ≥0∞) ≤ α * k * e j}) (Fintype.card ι) := by
  refine le_antisymm (card_le_findGreatest isSelfConsistent_eBH) ?_
  rw [eBH_def]
  exact findGreatest_le_card_filter

/-- **The threshold form of e-BH** [WR22, Proposition 1]: e-BH rejects `i` exactly when
`K ≤ α * #(eBH e α) * e i`. For a level `α ∉ {0, ∞}` and a nonempty rejection set, this says that
`e i` is at least `K / (α * #(eBH e α))`. -/
theorem mem_eBH_iff_le_mul_card :
    i ∈ eBH e α ↔ (Fintype.card ι : ℝ≥0∞) ≤ α * #(eBH e α) * e i := by
  conv_lhs => rw [eBH_def]
  rw [mem_filter, card_eBH]
  exact and_iff_right (mem_univ i)

/-- **e-BH for one hypothesis is the e-test**: it rejects exactly when `1 ≤ α * e i`. For a
level `α ∉ {0, ∞}`, this says that the e-value is at least `α⁻¹`. -/
theorem mem_eBH_iff_one_le_mul [Unique ι] : i ∈ eBH e α ↔ 1 ≤ α * e i := by
  have hR (R : Finset ι) (hi : i ∈ R) : R = {i} :=
    eq_singleton_iff_unique_mem.2 ⟨hi, fun j _ ↦ Subsingleton.elim j i⟩
  refine mem_eBH_iff_exists.trans ⟨fun ⟨R, h, hi⟩ ↦ ?_, fun h ↦ ⟨{i}, ?_, mem_singleton_self i⟩⟩
  · simpa [hR R hi] using h i hi
  · simpa [isSelfConsistent_iff] using h

/-- At level `0`, e-BH rejects nothing. -/
@[simp]
theorem eBH_zero (e : ι → ℝ≥0∞) : eBH e 0 = ∅ :=
  eq_empty_of_forall_notMem fun i hi ↦ by
    have h := mem_eBH_iff_le_mul_card.1 hi
    rw [zero_mul, zero_mul] at h
    have : Nonempty ι := ⟨i⟩
    exact absurd h (not_le.2 (Nat.cast_pos.2 Fintype.card_pos))

/-- **e-BH is monotone** in the level and in the e-values. -/
theorem eBH_mono {e' : ι → ℝ≥0∞} {α' : ℝ≥0∞} (hα : α ≤ α') (he : e ≤ e') :
    eBH e α ⊆ eBH e' α' :=
  (isSelfConsistent_eBH.mono hα he).subset_eBH

/-- **e-BH at a divided level** is e-BH applied to the divided e-values. -/
theorem eBH_div (e : ι → ℝ≥0∞) (α c : ℝ≥0∞) : eBH e (α / c) = eBH (fun i ↦ e i / c) α := by
  have h := isGreatest_eBH (e := e) (α := α / c)
  simp_rw [isSelfConsistent_div_iff] at h
  exact h.unique isGreatest_eBH

/-- **e-BH commutes with relabelling the hypotheses**: for a bijection `σ : κ ≃ ι`, e-BH applied
to `e ∘ σ` rejects `i` exactly when e-BH applied to `e` rejects `σ i`. -/
theorem mem_eBH_comp_equiv [Fintype κ] (σ : κ ≃ ι) {i : κ} : i ∈ eBH (e ∘ σ) α ↔ σ i ∈ eBH e α := by
  have hK : Fintype.card κ = Fintype.card ι := Fintype.card_congr σ
  have hc (k : ℕ) : #{j : κ | (Fintype.card ι : ℝ≥0∞) ≤ α * k * e (σ j)} =
      #{j : ι | (Fintype.card ι : ℝ≥0∞) ≤ α * k * e j} :=
    card_equiv σ fun j ↦ by simp
  simp only [eBH_def, mem_filter, mem_univ, true_and, Function.comp_apply, hK, hc]

/-- Relabelling the hypotheses does not change the number of rejections of e-BH. -/
theorem card_eBH_comp_equiv [Fintype κ] (σ : κ ≃ ι) : #(eBH (e ∘ σ) α) = #(eBH e α) :=
  card_equiv σ fun _ ↦ mem_eBH_comp_equiv σ

/-- Relabelling the hypotheses does not change whether e-BH makes a rejection. -/
theorem eBH_comp_equiv_nonempty [Fintype κ] (σ : κ ≃ ι) :
    (eBH (e ∘ σ) α).Nonempty ↔ (eBH e α).Nonempty := by
  rw [← card_pos, card_eBH_comp_equiv, card_pos]

/-- The e-BH rejection set is measurable in measurable e-values. -/
theorem measurable_eBH {E : ι → Ω → ℝ≥0∞} (hE : ∀ i, Measurable (E i)) (α : ℝ≥0∞) :
    Measurable fun ω ↦ eBH (E · ω) α := by
  have hset (c : Ω → ℝ≥0∞) (hc : Measurable c) :
      Measurable fun ω ↦ ({j | (Fintype.card ι : ℝ≥0∞) ≤ c ω * E j ω} : Finset ι) :=
    measurable_finset_iff.2 fun j ↦ by
      simpa using measurableSet_setOfPred.1 (measurableSet_le measurable_const (hc.mul (hE j)))
  -- The number of rejections `k*` is measurable, as a largest index of measurable conditions.
  have hk : Measurable fun ω ↦ Nat.findGreatest
      (fun k ↦ k ≤ #{j | (Fintype.card ι : ℝ≥0∞) ≤ α * k * E j ω}) (Fintype.card ι) :=
    measurable_findGreatest fun k _ ↦ measurableSet_le measurable_const
      ((Measurable.of_discrete (f := fun s : Finset ι ↦ #s)).comp (hset _ measurable_const))
  simp_rw [eBH_def]
  exact hset _ (measurable_const.mul (measurable_from_nat.comp hk))

/-- The e-BH rejection set is measurable in the e-values. -/
theorem measurable_eBH_id (α : ℝ≥0∞) : Measurable fun s : ι → ℝ≥0∞ ↦ eBH s α :=
  measurable_eBH (E := fun i (s : ι → ℝ≥0∞) ↦ s i) measurable_pi_apply α

/-- The number of rejections of e-BH is measurable in the e-values. -/
theorem measurable_card_eBH (α : ℝ≥0∞) :
    Measurable fun s : ι → ℝ≥0∞ ↦ (#(eBH s α) : ℝ≥0∞) :=
  (measurable_of_finite fun R : Finset ι ↦ (#R : ℝ≥0∞)).comp (measurable_eBH_id α)

end EBH

/-! ### Compound e-variables -/

section Compound

variable {H H' : ι → Set (Measure Ω)} {E E' : ι → Ω → ℝ≥0∞}

/-- **Compound e-variables** for the hypotheses `H` [IWR, Definition 2.1; RW, Definition 9.1]:
measurable statistics `E i` whose expectations over the true nulls sum to at most the number `K`
of hypotheses, under every probability measure. -/
structure IsCompoundEVar (E : ι → Ω → ℝ≥0∞) (H : ι → Set (Measure Ω)) : Prop where
  /-- Each statistic is measurable. -/
  measurable (i : ι) : Measurable (E i)
  /-- The expectations of the statistics of the true nulls sum to at most `K`. -/
  sum_lintegral_le (P : Measure Ω) [IsProbabilityMeasure P] :
    ∑ i ∈ trueNulls H P, ∫⁻ ω, E i ω ∂P ≤ Fintype.card ι

/-- The expectations of e-variables over the true nulls sum to at most the number of true
nulls. -/
theorem sum_lintegral_le_card_trueNulls (hE : ∀ i, IsEVar (E i) (H i)) (P : Measure Ω) :
    ∑ i ∈ trueNulls H P, ∫⁻ ω, E i ω ∂P ≤ #(trueNulls H P) := by
  rw [cast_card]
  exact sum_le_sum fun i hi ↦ (hE i).lintegral_le_one (mem_trueNulls.1 hi)

/-- **E-variables are compound e-variables** [IWR, §2; RW, §9.1]. -/
theorem IsCompoundEVar.of_isEVar (hE : ∀ i, IsEVar (E i) (H i)) : IsCompoundEVar E H where
  measurable i := (hE i).measurable
  sum_lintegral_le P _ := (sum_lintegral_le_card_trueNulls hE P).trans
    (Nat.cast_le.2 (card_le_univ _))

/-- Compound e-variables for `H` are compound e-variables for smaller hypotheses. -/
theorem IsCompoundEVar.anti_set (hE : IsCompoundEVar E H) (hH : ∀ i, H' i ⊆ H i) :
    IsCompoundEVar E H' where
  measurable := hE.measurable
  sum_lintegral_le P _ := (sum_le_sum_of_subset fun i hi ↦
    mem_trueNulls.2 (hH i (mem_trueNulls.1 hi))).trans (hE.sum_lintegral_le P)

/-- Measurable statistics below compound e-variables are compound e-variables. -/
theorem IsCompoundEVar.of_le (hE : IsCompoundEVar E H) (hE' : ∀ i, Measurable (E' i))
    (hle : ∀ i ω, E' i ω ≤ E i ω) : IsCompoundEVar E' H where
  measurable := hE'
  sum_lintegral_le P _ :=
    (sum_le_sum fun i _ ↦ lintegral_mono (hle i)).trans (hE.sum_lintegral_le P)

/-- **Compound e-variables and e-collections** [XSF+26, Proposition 24]: the means
`S ↦ ∑ i ∈ S, E i / K` of statistics form an e-collection exactly when the statistics are
compound e-variables. -/
theorem isECollection_sum_div_iff :
    IsECollection (fun S ω ↦ ∑ i ∈ S, E i ω / Fintype.card ι) H ↔ IsCompoundEVar E H := by
  have hle (hE : ∀ i, Measurable (E i)) (P : Measure Ω) :
      ∫⁻ ω, ∑ i ∈ trueNulls H P, E i ω / Fintype.card ι ∂P ≤ 1 ↔
        ∑ i ∈ trueNulls H P, ∫⁻ ω, E i ω ∂P ≤ Fintype.card ι := by
    rw [lintegral_finsetSum_div fun i _ ↦ (hE i).aemeasurable]
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
    · simp [Finset.eq_empty_of_isEmpty (trueNulls H P)]
    rw [ENNReal.div_le_iff (natCast_card_ne_zero i) (ENNReal.natCast_ne_top _), one_mul]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun S ↦ Finset.measurable_sum S fun i _ ↦
    (h.measurable i).div_const _, funext fun _ ↦ sum_empty,
    fun P _ ↦ (hle h.measurable P).2 (h.sum_lintegral_le P)⟩⟩
  -- The statistic of `{i}` is `E i / K`, from which `E i` is recovered.
  have hE (i : ι) : Measurable (E i) := by
    have := (h.measurable {i}).mul_const (Fintype.card ι : ℝ≥0∞)
    simp only [sum_singleton] at this
    simpa [ENNReal.div_mul_cancel (natCast_card_ne_zero i) (ENNReal.natCast_ne_top _)] using this
  exact ⟨hE, fun P _ ↦ (hle hE P).1 (h.lintegral_le_one P)⟩

/-- **Statistics dominated by an e-collection are compound e-variables** [XSF+26,
Proposition 26]: measurable statistics whose sum over the true nulls is almost surely at most `K`
times the statistic of the true nulls of an e-collection, under every probability measure, are
compound e-variables. -/
theorem IsECollection.isCompoundEVar_of_ae_sum_le {e : Finset ι → Ω → ℝ≥0∞}
    (he : IsECollection e H) (hE : ∀ i, Measurable (E i))
    (hle : ∀ (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ᵐ ω ∂P, ∑ i ∈ trueNulls H P, E i ω ≤ Fintype.card ι * e (trueNulls H P) ω) :
    IsCompoundEVar E H where
  measurable := hE
  sum_lintegral_le P _ := by
    calc ∑ i ∈ trueNulls H P, ∫⁻ ω, E i ω ∂P = ∫⁻ ω, ∑ i ∈ trueNulls H P, E i ω ∂P :=
          (lintegral_finsetSum _ fun i _ ↦ hE i).symm
      _ ≤ ∫⁻ ω, Fintype.card ι * e (trueNulls H P) ω ∂P := lintegral_mono_ae (hle P)
      _ = Fintype.card ι * ∫⁻ ω, e (trueNulls H P) ω ∂P :=
          lintegral_const_mul _ (he.measurable _)
      _ ≤ Fintype.card ι := mul_le_of_le_one_right' (he.lintegral_le_one P)

/-- Compound e-variables give the mean e-collection `S ↦ ∑ i ∈ S, E i / K`. -/
theorem IsCompoundEVar.isECollection (hE : IsCompoundEVar E H) :
    IsECollection (fun S ω ↦ ∑ i ∈ S, E i ω / Fintype.card ι) H :=
  isECollection_sum_div_iff.2 hE

end Compound

/-! ### False discovery rate control by self-consistent procedures -/

section FDR

variable [DecidableEq ι] {H : ι → Set (Measure Ω)} {E : ι → Ω → ℝ≥0∞} {α : ℝ≥0∞}
  {D : Ω → Finset ι}

/-- **The post-hoc false discovery rate of self-consistent procedures** [RW, Theorem 9.11]: for
statistics `E i` almost everywhere measurable for a measure `P`, rejection sets `D k ω`
self-consistent at levels `α k` and every set `N` of hypotheses, the expected largest ratio of the
false discovery proportion to the level is at most `(∑ i ∈ N, ∫⁻ E i) / K`. The level may thus be
chosen after seeing the data. -/
theorem lintegral_iSup_fdp_div_le_of_isSelfConsistent {P : Measure Ω}
    (hE : ∀ i, AEMeasurable (E i) P) {α : κ → ℝ≥0∞} {D : κ → Ω → Finset ι}
    (hD : ∀ k ω, IsSelfConsistent (E · ω) (α k) (D k ω)) (N : Finset ι) :
    ∫⁻ ω, ⨆ k, fdp N (D k ω) / α k ∂P ≤ (∑ i ∈ N, ∫⁻ ω, E i ω ∂P) / Fintype.card ι :=
  (lintegral_mono fun ω ↦ iSup_le fun k ↦ ENNReal.div_le_of_le_mul' ((hD k ω).fdp_le N)).trans_eq
    (lintegral_finsetSum_div (fun i _ ↦ hE i) _)

/-- **The false discovery rate of a self-consistent procedure** [WR22, Proposition 2; RW,
Theorem 9.11]: for statistics `E i` almost everywhere measurable for a measure `P`, rejection sets
`D ω` self-consistent at level `α` and every set `N` of hypotheses, the expected false discovery
proportion is at most `α * (∑ i ∈ N, ∫⁻ E i) / K`. -/
theorem lintegral_fdp_le_of_isSelfConsistent {P : Measure Ω} (hE : ∀ i, AEMeasurable (E i) P)
    (hD : ∀ ω, IsSelfConsistent (E · ω) α (D ω)) (N : Finset ι) :
    ∫⁻ ω, fdp N (D ω) ∂P ≤ α * (∑ i ∈ N, ∫⁻ ω, E i ω ∂P) / Fintype.card ι := by
  calc ∫⁻ ω, fdp N (D ω) ∂P ≤ ∫⁻ ω, α * ∑ i ∈ N, E i ω / Fintype.card ι ∂P :=
        lintegral_mono fun ω ↦ (hD ω).fdp_le N
    _ = α * (∑ i ∈ N, ∫⁻ ω, E i ω ∂P) / Fintype.card ι := by
        rw [lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum N fun i _ ↦ (hE i).div_const _),
          lintegral_finsetSum_div fun i _ ↦ hE i, mul_div_assoc]

/-- **Post-hoc false discovery rate control with compound e-variables** [RW, Theorem 9.11]: for
rejection sets `D k ω` self-consistent at levels `α k` for compound e-variables, the expected
largest ratio of the false discovery proportion of the true nulls to the level is at most one,
under every probability measure. This is the post-hoc e-Closure Principle for the mean
e-collection. -/
theorem IsCompoundEVar.lintegral_iSup_fdp_div_le_one (hE : IsCompoundEVar E H)
    {α : κ → ℝ≥0∞} {D : κ → Ω → Finset ι} (hD : ∀ k ω, IsSelfConsistent (E · ω) (α k) (D k ω))
    (P : Measure Ω) [IsProbabilityMeasure P] :
    ∫⁻ ω, ⨆ k, fdp (trueNulls H P) (D k ω) / α k ∂P ≤ 1 :=
  (lintegral_mono fun ω ↦ iSup_le fun k ↦ le_iSup_of_le k (le_iSup₂_of_le (D k ω)
    (hD k ω).mem_eClosure le_rfl)).trans
    (hE.isECollection.lintegral_iSup_div_le_one (fun _ ↦ fdp) α P)

/-- **False discovery rate control with compound e-variables** [RW, Theorem 9.11; IWR,
Theorem 4.3]: a rejection procedure self-consistent at level `α` for compound e-variables has
false discovery rate at most `α` under every probability measure, whatever the dependence of the
statistics. This is the e-Closure Principle for the mean e-collection. -/
theorem IsCompoundEVar.lintegral_fdp_le (hE : IsCompoundEVar E H)
    (hD : ∀ ω, IsSelfConsistent (E · ω) α (D ω)) (P : Measure Ω) [IsProbabilityMeasure P] :
    ∫⁻ ω, fdp (trueNulls H P) (D ω) ∂P ≤ α :=
  (lintegral_mono fun ω ↦ le_iSup₂_of_le (f := fun R _ ↦ fdp (trueNulls H P) R) (D ω)
    (hD ω).mem_eClosure le_rfl).trans (hE.isECollection.lintegral_biSup_eClosure_le fdp α P)

/-- **False discovery rate control with e-variables** [WR22, Proposition 2]: a rejection procedure
self-consistent at level `α` for e-variables has false discovery rate at most `α * #N / K`, with
`N` the true nulls, under every measure and whatever the dependence of the e-variables. -/
theorem lintegral_fdp_le_of_isEVar (hE : ∀ i, IsEVar (E i) (H i))
    (hD : ∀ ω, IsSelfConsistent (E · ω) α (D ω)) (P : Measure Ω) :
    ∫⁻ ω, fdp (trueNulls H P) (D ω) ∂P ≤ α * #(trueNulls H P) / Fintype.card ι :=
  (lintegral_fdp_le_of_isSelfConsistent (fun i ↦ (hE i).measurable.aemeasurable) hD _).trans
    (by gcongr; exact sum_lintegral_le_card_trueNulls hE P)

/-- **Post-hoc false discovery rate control with e-variables** [RW, Theorem 9.11]: for rejection
sets `D k ω` self-consistent at levels `α k` for e-variables, the expected largest ratio of the
false discovery proportion to the level is at most `#N / K`, with `N` the true nulls. -/
theorem lintegral_iSup_fdp_div_le_of_isEVar (hE : ∀ i, IsEVar (E i) (H i)) {α : κ → ℝ≥0∞}
    {D : κ → Ω → Finset ι} (hD : ∀ k ω, IsSelfConsistent (E · ω) (α k) (D k ω))
    (P : Measure Ω) :
    ∫⁻ ω, ⨆ k, fdp (trueNulls H P) (D k ω) / α k ∂P ≤
      #(trueNulls H P) / Fintype.card ι :=
  (lintegral_iSup_fdp_div_le_of_isSelfConsistent (fun i ↦ (hE i).measurable.aemeasurable) hD
    _).trans
    (by gcongr; exact sum_lintegral_le_card_trueNulls hE P)

/-- **False discovery rate control by e-BH with compound e-variables** [IWR, Theorem 4.3; RW,
Theorem 9.11]. -/
theorem IsCompoundEVar.lintegral_fdp_eBH_le (hE : IsCompoundEVar E H) (α : ℝ≥0∞) (P : Measure Ω)
    [IsProbabilityMeasure P] : ∫⁻ ω, fdp (trueNulls H P) (eBH (E · ω) α) ∂P ≤ α :=
  hE.lintegral_fdp_le (fun _ ↦ isSelfConsistent_eBH) P

/-- **False discovery rate control by e-BH with e-variables** [WR22, Theorem 2]: e-BH applied to
arbitrarily dependent e-variables has false discovery rate at most `α * #N / K`, with `N` the true
nulls. -/
theorem lintegral_fdp_eBH_le_of_isEVar (hE : ∀ i, IsEVar (E i) (H i)) (α : ℝ≥0∞)
    (P : Measure Ω) :
    ∫⁻ ω, fdp (trueNulls H P) (eBH (E · ω) α) ∂P ≤ α * #(trueNulls H P) / Fintype.card ι :=
  lintegral_fdp_le_of_isEVar hE (fun _ ↦ isSelfConsistent_eBH) P

end FDR

/-! ### Universality of e-BH -/

section Universality

variable [DecidableEq ι] {H : ι → Set (Measure Ω)} {α : ℝ≥0∞} {R S : Finset ι} {i : ι}

/-- **The universal compound e-values** of a rejection set `R` at level `α` [IWR, (4); RW, (9.3);
XSF+26, (10)]: `K * 𝟙{i ∈ R} / (α * max #R 1)`, with `K` the number of hypotheses. -/
noncomputable def universalEValue (α : ℝ≥0∞) (R : Finset ι) (i : ι) : ℝ≥0∞ :=
  if i ∈ R then (Fintype.card ι : ℝ≥0∞) / (α * max (#R : ℝ≥0∞) 1) else 0

theorem universalEValue_def (α : ℝ≥0∞) (R : Finset ι) (i : ι) :
    universalEValue α R i =
      if i ∈ R then (Fintype.card ι : ℝ≥0∞) / (α * max (#R : ℝ≥0∞) 1) else 0 :=
  (rfl)

@[simp]
theorem universalEValue_of_mem (hi : i ∈ R) :
    universalEValue α R i = (Fintype.card ι : ℝ≥0∞) / (α * #R) := by
  simp only [universalEValue_def, hi, ↓reduceIte]
  rw [max_eq_left (Nat.one_le_cast.2 (card_pos.2 ⟨i, hi⟩))]

@[simp]
theorem universalEValue_of_notMem (hi : i ∉ R) : universalEValue α R i = 0 := by
  simp [universalEValue_def, hi]

/-- The universal compound e-values of the members of `S` sum to `K / α` times the false
discovery proportion of `R` when the set of true nulls is `S`. -/
theorem sum_universalEValue (α : ℝ≥0∞) (R S : Finset ι) :
    ∑ i ∈ S, universalEValue α R i = Fintype.card ι / α * fdp S R := by
  simp [universalEValue_def, fdp_def, sum_ite_mem, div_eq_mul_inv, ENNReal.mul_inv, inter_comm,
    mul_assoc, mul_left_comm]

/-- The universal compound e-values of a measurable rejection procedure are measurable. -/
theorem measurable_universalEValue {R : Ω → Finset ι} (hR : Measurable R) (α : ℝ≥0∞) (i : ι) :
    Measurable fun ω ↦ universalEValue α (R ω) i :=
  (Measurable.of_discrete (f := fun R : Finset ι ↦ universalEValue α R i)).comp hR

/-- The e-BH procedure applied to the universal compound e-values of `R` rejects exactly `R`, for
a level `α ∉ {0, ∞}` [IWR, proof of Theorem 4.4]. -/
theorem eBH_universalEValue (hα₀ : α ≠ 0) (hα : α ≠ ∞) (R : Finset ι) :
    eBH (universalEValue α R) α = R := by
  refine subset_antisymm (fun i hi ↦ ?_) (IsSelfConsistent.subset_eBH fun i hi ↦ ?_)
  · -- A hypothesis outside `R` has e-value `0`, below every positive threshold.
    by_contra hiR
    exact natCast_card_ne_zero i (by simpa [hiR] using mem_eBH_iff_le_mul_card.1 hi)
  · have hR0 : α * (#R : ℝ≥0∞) ≠ 0 :=
      mul_ne_zero hα₀ (Nat.cast_ne_zero.2 (card_ne_zero_of_mem hi))
    rw [universalEValue_of_mem hi, ENNReal.mul_div_cancel hR0
      (ENNReal.mul_ne_top hα (ENNReal.natCast_ne_top _))]

/-- **From false discovery rate control to compound e-variables** [RW, Theorem 9.18; IWR, proof
of Theorem 4.4]: if a measurable rejection procedure `R` has false discovery rate at most `α`
under every probability measure, then its universal compound e-values are compound
e-variables. -/
theorem isCompoundEVar_universalEValue {R : Ω → Finset ι} (hR : Measurable R)
    (hfdr : ∀ (P : Measure Ω) [IsProbabilityMeasure P], ∫⁻ ω, fdp (trueNulls H P) (R ω) ∂P ≤ α) :
    IsCompoundEVar (fun i ω ↦ universalEValue α (R ω) i) H where
  measurable := measurable_universalEValue hR α
  sum_lintegral_le P _ := by
    rw [← lintegral_finsetSum _ fun i _ ↦ measurable_universalEValue hR α i]
    simp_rw [sum_universalEValue]
    rw [lintegral_const_mul (f := fun ω ↦ fdp (trueNulls H P) (R ω)) _
      ((Measurable.of_discrete (f := fdp (trueNulls H P))).comp hR)]
    calc (Fintype.card ι : ℝ≥0∞) / α * ∫⁻ ω, fdp (trueNulls H P) (R ω) ∂P
        ≤ Fintype.card ι / α * α := by gcongr; exact hfdr P
      _ ≤ Fintype.card ι := (mul_comm _ _).trans_le ENNReal.mul_div_le

/-- **The universal compound e-values of a member of an e-closure** [XSF+26, Proposition 26]: if
`R` belongs to the e-closure of `e` for the false discovery proportion at level `α`, then the
universal compound e-values of `R` over every set `S` of hypotheses sum to at most `K * e S`. -/
theorem sum_universalEValue_le_of_mem_eClosure {e : Finset ι → Ω → ℝ≥0∞} {ω : Ω}
    (hR : R ∈ eClosure fdp α e ω) (S : Finset ι) :
    ∑ i ∈ S, universalEValue α R i ≤ Fintype.card ι * e S ω := by
  rw [sum_universalEValue]
  calc (Fintype.card ι : ℝ≥0∞) / α * fdp S R ≤ Fintype.card ι / α * (α * e S ω) := by
        gcongr; exact ProbabilityTheory.mem_eClosure.1 hR S
    _ = Fintype.card ι / α * α * e S ω := (mul_assoc ..).symm
    _ ≤ Fintype.card ι * e S ω := by
        gcongr; exact (mul_comm _ _).trans_le ENNReal.mul_div_le

/-- **The universality of e-BH with compound e-variables** [IWR, Theorem 4.4; RW,
Theorems 9.18–9.19]: for a level `α ∉ {0, ∞}`, a measurable rejection procedure controls the
false discovery rate at level `α` under every probability measure exactly when it is the e-BH
procedure applied to some compound e-variables. -/
theorem forall_lintegral_fdp_le_iff_exists_isCompoundEVar (hα₀ : α ≠ 0) (hα : α ≠ ∞)
    {R : Ω → Finset ι} (hR : Measurable R) :
    (∀ (P : Measure Ω) [IsProbabilityMeasure P], ∫⁻ ω, fdp (trueNulls H P) (R ω) ∂P ≤ α) ↔
      ∃ E, IsCompoundEVar E H ∧ ∀ ω, eBH (E · ω) α = R ω := by
  refine ⟨fun hfdr ↦ ⟨_, isCompoundEVar_universalEValue hR hfdr,
    fun ω ↦ eBH_universalEValue hα₀ hα (R ω)⟩, fun ⟨E, hE, hER⟩ P _ ↦ ?_⟩
  simpa only [hER] using hE.lintegral_fdp_eBH_le α P

end Universality

end ProbabilityTheory
