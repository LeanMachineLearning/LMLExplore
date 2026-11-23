/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.MultipleTesting.EBH

/-!
# The Simes p-value, and the Benjamini–Hochberg procedure at random times

The Benjamini–Hochberg procedure (BH) at level `α` on p-values `p : ι → ℝ≥0∞` is e-BH applied to
the e-values `p⁻¹`: a set `R` is self-consistent for `p⁻¹` (`ProbabilityTheory.IsSelfConsistent`)
when every `i ∈ R` has `K * p i ≤ α * #R`, i.e. `p i ≤ α * #R / K`, with `K` the number of
hypotheses (the compliant procedures of [Su18]); `eBH (fun i ↦ (p i)⁻¹) α` is the largest such
set, the set that BH rejects.

The Simes p-value of the p-values of a set `N` of hypotheses (`ProbabilityTheory.simesPValue`) is
the smallest, over the nonempty `U ⊆ N`, of `#N * p i / #U` maximized over `i ∈ U`: with the
p-values of `N` ordered as `p₍₁₎ ≤ ⋯ ≤ p₍K₀₎`, it is Simes's `min_v K₀ p₍ᵥ₎ / v` [Sim86]. It is at
most `c` exactly when, for some `v ≥ 1`, at least `v` of the p-values of `N` are at most
`c * v / K₀` (`ProbabilityTheory.simesPValue_le_iff_exists_le_card_filter`). The Simes inequality
for the true nulls `N` is the statement that this is a p-variable. By [Sim86] it holds for
independent p-variables, which this file does not prove; it holds when the p-values of `N` coincide
and are a p-variable (`ProbabilityTheory.simesPValue_of_forall_eq`), and for a single true null
exactly when its p-value is a p-variable (`ProbabilityTheory.simesPValue_singleton`).

The FDR-linking theorem of Su [Su18, Theorems 2 and 3] rests on a bound of the false discovery
proportion of every compliant set by the Simes p-value of the true nulls alone, whatever the other
p-values and the dependence between them: `fdp N R ≤ a / simesPValue N p` with `a = α * #N / K`, the
level times the proportion of true nulls
(`ProbabilityTheory.IsSelfConsistent.fdp_le_div_simesPValue`). Under the Simes inequality, the
expected largest false discovery proportion over all compliant sets is therefore at most
`a * (1 + log (1 / a))` for `a ≤ 1`, and at most `α` when every hypothesis is a true null and the
Simes test of level `α` is valid, in the form of [FXR26] for the supremum over self-consistent sets.

This applies to BH at random times [EVR26, Note 34]. For p-processes `p i t`, indexed by any type of
times, BH applied to the current p-values at a time `t` rejects a set that is self-consistent for
the running infima `⨅ t, p i t` (`ProbabilityTheory.isSelfConsistent_eBH_inv_iInf`). So when the
running infima of the true nulls satisfy the Simes inequality, as they do by [Sim86] for independent
anytime-valid p-processes, the false discovery rate of BH at every random time, a stopping time or
not, is at most the expected largest false discovery proportion over time, which is at most
`a * (1 + log (1 / a))`, and at most `α` when every hypothesis is a true null. Applied to `p = E⁻¹`,
this is e-BH on the current values of e-processes `E`, with the running maxima of `E`.

## Main definitions

* `ProbabilityTheory.simesPValue N p`: the Simes p-value of the p-values `p i`, `i ∈ N`.

## Main statements

* `ProbabilityTheory.simesPValue_le_iff`: the Simes p-value is at most `c ≠ ∞` exactly when some
  nonempty `U ⊆ N` has `#N * p i ≤ c * #U` for every `i ∈ U`.
* `ProbabilityTheory.IsSelfConsistent.fdp_le_div_simesPValue`: **Su's pointwise bound**
  `fdp N R ≤ α * #N / K / simesPValue N p` for every set `R` self-consistent for `p⁻¹`.
* `ProbabilityTheory.lintegral_iSup_fdp_le_of_isPVar_simesPValue`: **the FDR-linking bound**
  `a * (1 - log a)` on the expected largest false discovery proportion of the self-consistent
  sets, under the Simes inequality [Su18, Theorems 2 and 3; FXR26];
  `ProbabilityTheory.lintegral_iSup_fdp_univ_le_of_measure_simesPValue_le`: `α` when every
  hypothesis is a true null.
* `ProbabilityTheory.lintegral_iSup_fdp_eBH_le_of_isPVar_simesPValue` and
  `ProbabilityTheory.lintegral_fdp_eBH_le_of_isPVar_simesPValue`: **BH at random times**, the
  bound `a * (1 - log a)` on the expected largest false discovery proportion of BH over time and on
  the false discovery rate of BH at any random time, when the running infima of the true nulls
  satisfy the Simes inequality [EVR26, Note 34];
  `ProbabilityTheory.lintegral_iSup_fdp_univ_eBH_le_of_measure_simesPValue_le` and
  `ProbabilityTheory.lintegral_fdp_univ_eBH_le_of_measure_simesPValue_le`: the bound `α` when
  every hypothesis is a true null.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, research notes of
  github.com/RemyDegenne/evalues_research, 2026, written and refereed by AI agents: Note 34,
  `results/34-stopped-bh-monotone-evidence.md`, statements 1 to 3.
* [FXR26] L. Fischer, Z. Xu and A. Ramdas, *An online generalization of the (e-)Benjamini–Hochberg
  procedure*, arXiv:2407.20683.
* [Sim86] R. J. Simes, *An improved Bonferroni procedure for multiple tests of significance*,
  Biometrika 73(3) (1986), 751–754.
* [Su18] W. J. Su, *The FDR-linking theorem*, arXiv:1812.08965.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω ι T : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The Simes p-value -/

section Simes

variable {N U : Finset ι} {p q : ι → ℝ≥0∞} {c x : ℝ≥0∞} {i : ι}

/-- **The Simes p-value** of the p-values `p i` of the hypotheses `i ∈ N` [Sim86]: the smallest,
over the nonempty sets `U ⊆ N`, of the largest of the values `#N * p i / #U`, `i ∈ U`. With the
p-values of `N` ordered as `p₍₁₎ ≤ ⋯ ≤ p₍K₀₎`, it is `min_v K₀ * p₍ᵥ₎ / v`, the best `U` of
cardinality `v` being the `v` smallest p-values. It is `∞` for `N = ∅`. -/
noncomputable def simesPValue (N : Finset ι) (p : ι → ℝ≥0∞) : ℝ≥0∞ :=
  {U ∈ N.powerset | U.Nonempty}.inf fun U ↦ U.sup fun i ↦ #N * p i / #U

theorem simesPValue_def (N : Finset ι) (p : ι → ℝ≥0∞) :
    simesPValue N p = {U ∈ N.powerset | U.Nonempty}.inf fun U ↦ U.sup fun i ↦ #N * p i / #U :=
  (rfl)

/-- The Simes p-value is at most `c` as soon as some nonempty `U ⊆ N` has `#N * p i ≤ c * #U`
for every `i ∈ U`. -/
theorem simesPValue_le (hU : U ⊆ N) (hU₀ : U.Nonempty) (h : ∀ i ∈ U, #N * p i ≤ c * #U) :
    simesPValue N p ≤ c := by
  refine (inf_le (mem_filter.2 ⟨mem_powerset.2 hU, hU₀⟩)).trans (Finset.sup_le fun i hi ↦ ?_)
  exact (ENNReal.div_le_iff (Nat.cast_ne_zero.2 hU₀.card_pos.ne') (ENNReal.natCast_ne_top _)).2
    (h i hi)

/-- **The Simes p-value is at most a finite `c`** exactly when some nonempty `U ⊆ N` has
`#N * p i ≤ c * #U`, i.e. `p i ≤ c * #U / #N`, for every `i ∈ U`. -/
theorem simesPValue_le_iff (hc : c ≠ ∞) :
    simesPValue N p ≤ c ↔ ∃ U ⊆ N, U.Nonempty ∧ ∀ i ∈ U, #N * p i ≤ c * #U := by
  refine ⟨fun h ↦ ?_, fun ⟨U, hU, hU₀, h⟩ ↦ simesPValue_le hU hU₀ h⟩
  obtain ⟨U, hU, hUc⟩ := (Finset.inf_le_iff hc.lt_top).1 h
  obtain ⟨hU, hU₀⟩ := mem_filter.1 hU
  refine ⟨U, mem_powerset.1 hU, hU₀, fun i hi ↦ ?_⟩
  exact (ENNReal.div_le_iff (Nat.cast_ne_zero.2 hU₀.card_pos.ne') (ENNReal.natCast_ne_top _)).1
    ((Finset.sup_le_iff.1 hUc) i hi)

/-- **The Simes event**: the Simes p-value is at most a finite `c` exactly when, for some
`v ≥ 1`, at least `v` of the p-values of `N` are at most `c * v / #N`. -/
theorem simesPValue_le_iff_exists_le_card_filter (hc : c ≠ ∞) :
    simesPValue N p ≤ c ↔ ∃ v : ℕ, 1 ≤ v ∧ v ≤ #{i ∈ N | #N * p i ≤ c * v} := by
  rw [simesPValue_le_iff hc]
  refine ⟨fun ⟨U, hU, hU₀, h⟩ ↦ ⟨#U, hU₀.card_pos, card_le_card fun i hi ↦
    mem_filter.2 ⟨hU hi, h i hi⟩⟩, fun ⟨v, hv, hvN⟩ ↦ ?_⟩
  refine ⟨{i ∈ N | #N * p i ≤ c * v}, filter_subset _ N, card_pos.1 (by omega), fun i hi ↦ ?_⟩
  exact (mem_filter.1 hi).2.trans (by gcongr)

/-- **Bonferroni's bound**: the Simes p-value is at most `#N * p i` for every `i ∈ N`. -/
theorem simesPValue_le_card_mul (hi : i ∈ N) : simesPValue N p ≤ #N * p i :=
  simesPValue_le (singleton_subset_iff.2 hi) (singleton_nonempty i) (by simp)

@[simp]
theorem simesPValue_empty (p : ι → ℝ≥0∞) : simesPValue ∅ p = ∞ := by
  simp [simesPValue_def]

/-- The Simes p-value of a single hypothesis is its p-value. -/
@[simp]
theorem simesPValue_singleton (i : ι) (p : ι → ℝ≥0∞) : simesPValue {i} p = p i := by
  refine le_antisymm
    (by simpa using simesPValue_le_card_mul (N := {i}) (p := p) (mem_singleton_self i))
    (Finset.le_inf fun U hU ↦ ?_)
  obtain ⟨hU, hU₀⟩ := mem_filter.1 hU
  rw [(subset_singleton_iff.1 (mem_powerset.1 hU)).resolve_left hU₀.ne_empty]
  simp

/-- When the p-values of a nonempty `N` all equal `x`, so does their Simes p-value: the Simes
inequality then holds as soon as `x` is a p-variable. -/
theorem simesPValue_of_forall_eq (hN : N.Nonempty) (h : ∀ i ∈ N, p i = x) :
    simesPValue N p = x := by
  have hN₀ : (#N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hN.card_pos.ne'
  refine le_antisymm (simesPValue_le subset_rfl hN fun i hi ↦ by rw [h i hi, mul_comm])
    (Finset.le_inf fun U hU ↦ ?_)
  obtain ⟨hU, ⟨j, hj⟩⟩ := mem_filter.1 hU
  refine le_sup_of_le hj ?_
  rw [h j (mem_powerset.1 hU hj), ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.2
    (card_ne_zero_of_mem hj))) (Or.inl (ENNReal.natCast_ne_top _)), mul_comm]
  gcongr
  exact mem_powerset.1 hU

/-- The Simes p-value is monotone in the p-values. -/
@[gcongr]
theorem simesPValue_mono (hpq : p ≤ q) : simesPValue N p ≤ simesPValue N q :=
  inf_mono_fun fun U _ ↦ sup_mono_fun fun i _ ↦ by gcongr; exact hpq i

/-- The Simes p-value of measurable p-values is measurable. -/
theorem measurable_simesPValue {p : ι → Ω → ℝ≥0∞} (hp : ∀ i, Measurable (p i)) :
    Measurable fun ω ↦ simesPValue N (p · ω) := by
  simp only [simesPValue_def, Finset.inf_eq_iInf, Finset.sup_eq_iSup]
  exact Measurable.biInf _ (Finset.countable_toSet _) fun U _ ↦
    Measurable.biSup _ (Finset.countable_toSet _) fun i _ ↦ ((hp i).const_mul _).div_const _

end Simes

/-! ### The FDR-linking theorem -/

section Linking

variable [Fintype ι] {N R : Finset ι} {p : ι → ℝ≥0∞} {α : ℝ≥0∞} {i : ι}

/-- **The rejected p-values of a compliant set**: if `R` is self-consistent at level `α` for the
e-values `p⁻¹`, every `i ∈ R` has `K * p i ≤ α * #R`, i.e. `p i ≤ α * #R / K`. -/
theorem IsSelfConsistent.card_mul_le (h : IsSelfConsistent (fun i ↦ (p i)⁻¹) α R) (hi : i ∈ R) :
    (Fintype.card ι : ℝ≥0∞) * p i ≤ α * #R :=
  calc (Fintype.card ι : ℝ≥0∞) * p i ≤ α * #R * (p i)⁻¹ * p i := by
        gcongr
        exact isSelfConsistent_iff.1 h i hi
    _ ≤ α * #R := by
        rw [mul_assoc]
        exact mul_le_of_le_one_right' (ENNReal.inv_mul_le_one _)

/-- **Su's pointwise bound** [Su18, proof of Theorem 2]: if `R` is self-consistent at level `α`
for the e-values `p⁻¹`, its false discovery proportion for the true nulls `N` is at most
`a / simesPValue N p`, with `a = α * #N / K`, whatever the p-values outside `N`. -/
theorem IsSelfConsistent.fdp_le_div_simesPValue [DecidableEq ι]
    (h : IsSelfConsistent (fun i ↦ (p i)⁻¹) α R) (N : Finset ι) :
    fdp N R ≤ α * #N / Fintype.card ι / simesPValue N p := by
  rcases (R ∩ N).eq_empty_or_nonempty with hRN | ⟨j, hj⟩
  · simp [fdp_def, hRN]
  obtain ⟨hjR, hjN⟩ := mem_inter.1 hj
  have : Nonempty ι := ⟨j⟩
  have hK₀ : (Fintype.card ι : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hR₀ : (#R : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (card_ne_zero_of_mem hjR)
  have hV₀ : (#(R ∩ N) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (card_ne_zero_of_mem hj)
  -- a rejected true null `j` has a finite p-value, and the level is nonzero
  have hjK := isSelfConsistent_iff.1 h j hjR
  have hα₀ : α ≠ 0 := by
    rintro rfl
    simp at hjK
  have hpj : p j ≠ ∞ := by
    rintro hp
    simp [hp] at hjK
  have ha₀ : α * #N / Fintype.card ι ≠ 0 := ENNReal.div_ne_zero.2
    ⟨mul_ne_zero hα₀ (Nat.cast_ne_zero.2 (card_ne_zero_of_mem hjN)), ENNReal.natCast_ne_top _⟩
  have hS : simesPValue N p ≠ ∞ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hpj) (simesPValue_le_card_mul hjN)
  -- the `v = #(R ∩ N)` rejected true nulls have `p i ≤ α * #R / K`, so the Simes p-value of `N`
  -- is at most `a * #R / v = a / fdp N R`, witnessed by `U = R ∩ N`
  have hSle : simesPValue N p ≤ α * #N / Fintype.card ι * (#R / #(R ∩ N)) := by
    refine simesPValue_le inter_subset_right ⟨j, hj⟩ fun i hi ↦ ?_
    have hpi : p i ≤ α * #R / Fintype.card ι :=
      (ENNReal.le_div_iff_mul_le (Or.inl hK₀) (Or.inl (ENNReal.natCast_ne_top _))).2
        (by rw [mul_comm]; exact h.card_mul_le (mem_inter.1 hi).1)
    calc (#N : ℝ≥0∞) * p i ≤ #N * (α * #R / Fintype.card ι) := by gcongr
      _ = α * #N / Fintype.card ι * (#R / #(R ∩ N)) * #(R ∩ N) := by
        rw [mul_assoc _ (_ / _), ENNReal.div_mul_cancel hV₀ (ENNReal.natCast_ne_top _)]
        simp only [div_eq_mul_inv]
        ring
  rw [fdp_def, max_eq_left (Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2
      (Nat.cast_ne_zero.1 hR₀))), ENNReal.le_div_iff_mul_le (Or.inr ha₀) (Or.inl hS)]
  calc (#(R ∩ N) : ℝ≥0∞) / #R * simesPValue N p
      ≤ #(R ∩ N) / #R * (α * #N / Fintype.card ι * (#R / #(R ∩ N))) := by gcongr
    _ = α * #N / Fintype.card ι * ((#(R ∩ N) * (#(R ∩ N) : ℝ≥0∞)⁻¹) * (#R * (#R : ℝ≥0∞)⁻¹)) := by
        simp only [div_eq_mul_inv]
        ring
    _ = α * #N / Fintype.card ι := by
        rw [ENNReal.mul_inv_cancel hV₀ (ENNReal.natCast_ne_top _),
          ENNReal.mul_inv_cancel hR₀ (ENNReal.natCast_ne_top _), mul_one, mul_one]

/-- **The FDR-linking theorem, unconditionally** [Su18, proof of Theorem 2]: under any measure, the
expected largest false discovery proportion of the sets self-consistent for `p⁻¹` is at most the
expectation of `min 1 (a / S)`, for `S` the Simes p-value of the true nulls `N` and
`a = α * #N / K`. Only the law of `S`, a function of the p-values of the true nulls, enters the
bound. -/
theorem lintegral_iSup_fdp_le_lintegral_min_one_div_simesPValue [DecidableEq ι]
    (p : ι → Ω → ℝ≥0∞) (N : Finset ι) (α : ℝ≥0∞) (P : Measure Ω) :
    ∫⁻ ω, ⨆ (R : Finset ι) (_ : IsSelfConsistent (fun i ↦ (p i ω)⁻¹) α R), fdp N R ∂P ≤
      ∫⁻ ω, min 1 (α * #N / Fintype.card ι / simesPValue N (p · ω)) ∂P :=
  lintegral_mono fun _ ↦ iSup₂_le fun R hR ↦ le_min (fdp_le_one N R) (hR.fdp_le_div_simesPValue N)

/-- **The FDR-linking bound under the Simes inequality** [Su18, Theorems 2 and 3; FXR26]: if the
Simes p-value of the p-values of the true nulls `N` is a p-variable under a measure `P` of mass at
most `1`, then the expected largest false discovery proportion of the sets self-consistent for
`p⁻¹`, in particular the false discovery rate of BH and of every compliant procedure, is at most
`a * (1 - log a) = a * (1 + log (1 / a))`, for `a = α * #N / K ≤ 1`. -/
theorem lintegral_iSup_fdp_le_of_isPVar_simesPValue [DecidableEq ι] {p : ι → Ω → ℝ≥0∞}
    {N : Finset ι} {P : Measure Ω} (hS : IsPVar (fun ω ↦ simesPValue N (p · ω)) {P})
    (hP : P Set.univ ≤ 1) (ha : α * #N / Fintype.card ι ≤ 1) :
    ∫⁻ ω, ⨆ (R : Finset ι) (_ : IsSelfConsistent (fun i ↦ (p i ω)⁻¹) α R), fdp N R ∂P ≤
      ENNReal.ofReal ((α * #N / Fintype.card ι).toReal *
        (1 - Real.log (α * #N / Fintype.card ι).toReal)) :=
  (lintegral_iSup_fdp_le_lintegral_min_one_div_simesPValue p N α P).trans
    (hS.lintegral_min_one_div_le rfl hP ha)

/-- **The FDR-linking bound when every hypothesis is a true null** [EVR26, Note 34, statement 3]:
if the Simes test of level `α` on all the p-values is valid under `P`, i.e. the Simes p-value is
at most `α` with probability at most `α`, then the expected largest false discovery proportion of
the sets self-consistent for `p⁻¹`, the probability that some nonempty set is, is at most `α`. -/
theorem lintegral_iSup_fdp_univ_le_of_measure_simesPValue_le [DecidableEq ι]
    {p : ι → Ω → ℝ≥0∞} {P : Measure Ω} (hS : P {ω | simesPValue univ (p · ω) ≤ α} ≤ α) :
    ∫⁻ ω, ⨆ (R : Finset ι) (_ : IsSelfConsistent (fun i ↦ (p i ω)⁻¹) α R), fdp univ R ∂P ≤
      α := by
  -- a nonempty self-consistent set makes the Simes p-value at most `α`
  have key : ∀ ω, ⨆ (R : Finset ι) (_ : IsSelfConsistent (fun i ↦ (p i ω)⁻¹) α R), fdp univ R ≤
      {ω | simesPValue univ (p · ω) ≤ α}.indicator (fun _ ↦ 1) ω := fun ω ↦ iSup₂_le fun R hR ↦ by
    rcases R.eq_empty_or_nonempty with rfl | hR₀
    · simp
    have hSα : simesPValue univ (p · ω) ≤ α :=
      simesPValue_le (subset_univ R) hR₀ fun i hi ↦ by
        simpa only [card_univ] using hR.card_mul_le hi
    rw [Set.indicator_of_mem (show ω ∈ {ω | simesPValue univ (p · ω) ≤ α} from hSα)]
    exact fdp_le_one univ R
  calc _ ≤ ∫⁻ ω, {ω | simesPValue univ (p · ω) ≤ α}.indicator (fun _ ↦ 1) ω ∂P := lintegral_mono key
    _ ≤ 1 * P {ω | simesPValue univ (p · ω) ≤ α} := lintegral_indicator_const_le _ 1
    _ ≤ α := by rwa [one_mul]

end Linking

/-! ### The Benjamini–Hochberg procedure at random times -/

section RandomTime

variable [Fintype ι] {N : Finset ι} {α : ℝ≥0∞}

/-- **BH at any time is compliant for the running infima** [EVR26, Note 34, statement 1]: for
p-processes `p i t`, the set that BH rejects at level `α` on the p-values at time `t` is
self-consistent for the running infima `⨅ s, p i s`. -/
theorem isSelfConsistent_eBH_inv_iInf (p : ι → T → ℝ≥0∞) (α : ℝ≥0∞) (t : T) :
    IsSelfConsistent (fun i ↦ (⨅ s, p i s)⁻¹) α (eBH (fun i ↦ (p i t)⁻¹) α) :=
  isSelfConsistent_eBH.mono le_rfl fun _ ↦ ENNReal.inv_le_inv.2 (iInf_le _ t)

/-- The largest false discovery proportion over time of BH on p-processes is at most the largest
false discovery proportion of the sets self-consistent for the running infima. -/
private lemma iSup_fdp_eBH_le [DecidableEq ι] (p : ι → T → ℝ≥0∞) (N : Finset ι) (α : ℝ≥0∞) :
    ⨆ t, fdp N (eBH (fun i ↦ (p i t)⁻¹) α) ≤
      ⨆ (R : Finset ι) (_ : IsSelfConsistent (fun i ↦ (⨅ s, p i s)⁻¹) α R), fdp N R :=
  iSup_le fun t ↦ le_iSup₂_of_le (f := fun R _ ↦ fdp N R) _
    (isSelfConsistent_eBH_inv_iInf p α t) le_rfl

/-- **BH over time** [EVR26, Note 34, statement 2]: if the Simes p-value of the running infima of
the p-processes of the true nulls `N` is a p-variable under a measure `P` of mass at most `1`, the
expected largest false discovery proportion of BH over time is at most `a * (1 - log a)`, for
`a = α * #N / K ≤ 1`. -/
theorem lintegral_iSup_fdp_eBH_le_of_isPVar_simesPValue [DecidableEq ι] {p : ι → T → Ω → ℝ≥0∞}
    {P : Measure Ω} (hS : IsPVar (fun ω ↦ simesPValue N fun i ↦ ⨅ t, p i t ω) {P})
    (hP : P Set.univ ≤ 1) (ha : α * #N / Fintype.card ι ≤ 1) :
    ∫⁻ ω, ⨆ t, fdp N (eBH (fun i ↦ (p i t ω)⁻¹) α) ∂P ≤
      ENNReal.ofReal ((α * #N / Fintype.card ι).toReal *
        (1 - Real.log (α * #N / Fintype.card ι).toReal)) :=
  (lintegral_mono fun ω ↦ iSup_fdp_eBH_le (p · · ω) N α).trans
    (lintegral_iSup_fdp_le_of_isPVar_simesPValue (p := fun i ω ↦ ⨅ t, p i t ω) hS hP ha)

/-- **BH at a random time** [EVR26, Note 34, statement 2]: if the Simes p-value of the running
infima of the p-processes of the true nulls `N` is a p-variable under a measure `P` of mass at
most `1`, then for every random time `τ`, a stopping time or not and not even measurable, the
false discovery rate of BH applied at time `τ` is at most `a * (1 - log a)`, for
`a = α * #N / K ≤ 1`. -/
theorem lintegral_fdp_eBH_le_of_isPVar_simesPValue [DecidableEq ι] {p : ι → T → Ω → ℝ≥0∞}
    {P : Measure Ω} (hS : IsPVar (fun ω ↦ simesPValue N fun i ↦ ⨅ t, p i t ω) {P})
    (hP : P Set.univ ≤ 1) (ha : α * #N / Fintype.card ι ≤ 1) (τ : Ω → T) :
    ∫⁻ ω, fdp N (eBH (fun i ↦ (p i (τ ω) ω)⁻¹) α) ∂P ≤
      ENNReal.ofReal ((α * #N / Fintype.card ι).toReal *
        (1 - Real.log (α * #N / Fintype.card ι).toReal)) :=
  (lintegral_mono fun ω ↦ le_iSup (fun t ↦ fdp N (eBH (fun i ↦ (p i t ω)⁻¹) α)) (τ ω)).trans
    (lintegral_iSup_fdp_eBH_le_of_isPVar_simesPValue hS hP ha)

/-- **BH over time when every hypothesis is a true null** [EVR26, Note 34, statement 3]: if the
Simes test of level `α` on the running infima of all the p-processes is valid under `P`, the
probability that BH rejects at some time is at most `α`. -/
theorem lintegral_iSup_fdp_univ_eBH_le_of_measure_simesPValue_le [DecidableEq ι]
    {p : ι → T → Ω → ℝ≥0∞} {P : Measure Ω}
    (hS : P {ω | simesPValue univ (fun i ↦ ⨅ t, p i t ω) ≤ α} ≤ α) :
    ∫⁻ ω, ⨆ t, fdp univ (eBH (fun i ↦ (p i t ω)⁻¹) α) ∂P ≤ α :=
  (lintegral_mono fun ω ↦ iSup_fdp_eBH_le (p · · ω) univ α).trans
    (lintegral_iSup_fdp_univ_le_of_measure_simesPValue_le (p := fun i ω ↦ ⨅ t, p i t ω) hS)

/-- **BH at a random time when every hypothesis is a true null** [EVR26, Note 34, statement 3]:
if the Simes test of level `α` on the running infima of all the p-processes is valid under `P`,
then for every random time `τ` the false discovery rate of BH applied at time `τ` is at most
`α`. -/
theorem lintegral_fdp_univ_eBH_le_of_measure_simesPValue_le [DecidableEq ι]
    {p : ι → T → Ω → ℝ≥0∞} {P : Measure Ω}
    (hS : P {ω | simesPValue univ (fun i ↦ ⨅ t, p i t ω) ≤ α} ≤ α) (τ : Ω → T) :
    ∫⁻ ω, fdp univ (eBH (fun i ↦ (p i (τ ω) ω)⁻¹) α) ∂P ≤ α :=
  (lintegral_mono fun ω ↦ le_iSup (fun t ↦ fdp univ (eBH (fun i ↦ (p i t ω)⁻¹) α)) (τ ω)).trans
    (lintegral_iSup_fdp_univ_eBH_le_of_measure_simesPValue_le hS)

end RandomTime

end ProbabilityTheory
