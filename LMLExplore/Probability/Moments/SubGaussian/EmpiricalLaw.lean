/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Algebra.Order.BigOperators.Group.Finset
public import LMLExplore.Probability.Moments.KLChernoff
public import Mathlib.Probability.HasLaw

/-!
# The `ℓ¹` deviation of empirical laws

Let `Y i`, `i ∈ s`, be independent random variables with law `p` on a finite type `β` with
`m = Fintype.card β` elements, and let `p̂(b) = #{i ∈ s | Y i = b} / #s` be their empirical law.
The `ℓ¹` distance `∑ b, |p̂(b) - p(b)|` is twice the largest deviation `p̂(B) - p(B)` over the
`2 ^ m - 2` nonempty proper subsets `B` of `β` (`Finset.sum_abs_eq_two_nsmul_sum_filter_pos`).
Hoeffding's inequality bounds each of these deviations, and a union bound gives [WOSVW03, Theorem
2.1], [LS, Exercise 5.17]: for `ε > 0`, `P(ε ≤ ∑ b, |p̂(b) - p(b)|) ≤ (2 ^ m - 2) exp (-#s ε² / 2)`.
Inverted, with probability at least `1 - δ`,
`∑ b, |p̂(b) - p(b)| < √(2 (log (1 / δ) + m log 2) / #s)`.

Through a measurable map `c : α → β`, the same bounds hold for random variables `X i` with law `ν`
on any measurable space `α` and the measurable partition of `α` into the cells `c ⁻¹' {b}`. For
finite state spaces, this bounds the total variation distance between a transition law and its
empirical estimate from independent samples.

## Main statements

* `LMLExplore.measureReal_le_sum_empirical_sub_le`: Hoeffding's inequality for the empirical mass
  of a fixed set.
* `LMLExplore.measure_sum_abs_empirical_sub_ge_le`: the tail bound on a finite type.
* `LMLExplore.le_measureReal_sum_abs_empirical_sub_lt`: the high-probability form on a finite type.
* `LMLExplore.measure_sum_abs_empirical_preimage_sub_ge_le`,
  `LMLExplore.le_measureReal_sum_abs_empirical_preimage_sub_lt`: the same bounds for the cells of a
  measurable partition.

## References

* [T. Weissman, E. Ordentlich, G. Seroussi, S. Verdú and M. J. Weinberger, *Inequalities for the
  L1 deviation of the empirical distribution*][WOSVW03]
* [T. Lattimore and C. Szepesvári, *Bandit Algorithms*][LS]
-/

public section

open Finset MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace LMLExplore

variable {Ω ι β : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [Fintype β] [DecidableEq β] [MeasurableSpace β] [MeasurableSingletonClass β]

omit [Fintype β] in
/-- **Hoeffding's inequality for the empirical law of a set.** If the `Y i`, `i ∈ s`, are
independent with law `p`, then for `ε ≥ 0` the empirical mass `p̂(B) = ∑ b ∈ B, p̂(b)` of a finite
set `B`, where `p̂(b) = #{i ∈ s | Y i = b} / #s`, satisfies
`P(ε ≤ p̂(B) - p(B)) ≤ exp (-2 #s ε²)`. It is Hoeffding's inequality
(`LMLExplore.measureReal_card_mul_add_le_sum_le`) for the indicators `1[Y i ∈ B]`. -/
theorem measureReal_le_sum_empirical_sub_le {Y : ι → Ω → β} (h_indep : iIndepFun Y P)
    {p : Measure β} {s : Finset ι} (hY : ∀ i ∈ s, HasLaw (Y i) p P)
    (B : Finset β) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ ∑ b ∈ B, ((#{i ∈ s | Y i ω = b} : ℝ) / #s - p.real {b})} ≤
      exp (-2 * #s * ε ^ 2) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  have := (hY i₀ hi₀).isProbabilityMeasure_iff.1 ‹_›
  have hn : (0 : ℝ) < #s := by exact_mod_cast card_pos.2 ⟨i₀, hi₀⟩
  -- The indicator `f = 1[· ∈ B]`, so that `#s * p̂(B) = ∑ i ∈ s, f (Y i)`.
  set f : β → ℝ := fun y ↦ if y ∈ B then 1 else 0 with hf
  have hf_meas : Measurable f :=
    Measurable.ite (p := (· ∈ B)) B.finite_toSet.measurableSet measurable_const measurable_const
  have hfY (i : ι) (hi : i ∈ s) : P[f ∘ Y i] = p.real B := by
    rw [(hY i hi).integral_comp hf_meas.aestronglyMeasurable, hf,
      ← integral_indicator_one (B.finite_toSet.measurableSet)]
    congr 1 with y
    simp [Set.indicator_apply]
  have h_eq (ω : Ω) : ∑ b ∈ B, ((#{i ∈ s | Y i ω = b} : ℝ) / #s - p.real {b}) =
      (∑ i ∈ s, f (Y i ω)) / #s - p.real B := by
    have hcount : ∑ b ∈ B, (#{i ∈ s | Y i ω = b} : ℝ) = ∑ i ∈ s, f (Y i ω) := by
      simp_rw [natCast_card_filter]
      rw [sum_comm]
      exact sum_congr rfl fun i _ ↦ by simp [hf, sum_ite_eq]
    rw [sum_sub_distrib, ← sum_div, hcount, sum_measureReal_singleton]
  have h_set : {ω | ε ≤ ∑ b ∈ B, ((#{i ∈ s | Y i ω = b} : ℝ) / #s - p.real {b})} =
      {ω | #s * (p.real B + ε) ≤ ∑ i ∈ s, (f ∘ Y i) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, h_eq, Function.comp_apply]
    rw [le_sub_iff_add_le', le_div_iff₀ hn, mul_comm]
  rw [h_set]
  refine (measureReal_card_mul_add_le_sum_le (h_indep.comp (fun _ ↦ f) fun _ ↦ hf_meas)
    (fun i hi ↦ hf_meas.comp_aemeasurable (hY i hi).aemeasurable)
    (fun i _ ↦ ae_of_all _ fun ω ↦ by by_cases h : Y i ω ∈ B <;> simp [hf, h])
    (fun i hi ↦ (hfY i hi).le) hε).trans_eq ?_
  congr 1
  ring

/-- **The `ℓ¹` deviation of the empirical law** [WOSVW03, Theorem 2.1], [LS, Exercise 5.17]. If
the `Y i`, `i ∈ s`, are independent with law `p` on a finite type `β`, then for `ε > 0` the
empirical law `p̂(b) = #{i ∈ s | Y i = b} / #s` satisfies
`P(ε ≤ ∑ b, |p̂(b) - p(b)|) ≤ (2 ^ card β - 2) exp (-#s ε² / 2)`. -/
theorem measure_sum_abs_empirical_sub_ge_le {Y : ι → Ω → β} (h_indep : iIndepFun Y P)
    {p : Measure β} {s : Finset ι} (hs : s.Nonempty) (hY : ∀ i ∈ s, HasLaw (Y i) p P)
    {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ ∑ b, |(#{i ∈ s | Y i ω = b} : ℝ) / #s - p.real {b}|} ≤
      (2 ^ Fintype.card β - 2) * exp (-#s * ε ^ 2 / 2) := by
  obtain ⟨i₀, hi₀⟩ := hs
  have := (hY i₀ hi₀).isProbabilityMeasure_iff.1 ‹_›
  have hn : (0 : ℝ) < #s := by exact_mod_cast card_pos.2 ⟨i₀, hi₀⟩
  -- The nonempty proper subsets of `β`.
  set T : Finset (Finset β) := (univ.erase ∅).erase univ with hT
  have : Nonempty β := nonempty_of_isProbabilityMeasure p
  have hT_card : (#T : ℝ) = 2 ^ Fintype.card β - 2 := by
    have h_ne : (univ : Finset β) ≠ ∅ := univ_nonempty.ne_empty
    have h1 : 2 ≤ 2 ^ Fintype.card β := le_self_pow₀ one_le_two Fintype.card_ne_zero
    rw [hT, card_erase_of_mem (mem_erase.2 ⟨h_ne, mem_univ _⟩),
      card_erase_of_mem (mem_univ _), card_univ, Fintype.card_finset]
    rw [Nat.sub_sub, Nat.cast_sub h1]
    norm_num
  -- On the bad event, the positive part of `p̂ - p` is a nonempty proper subset with deviation at
  -- least `ε / 2`.
  have h_sub : {ω | ε ≤ ∑ b, |(#{i ∈ s | Y i ω = b} : ℝ) / #s - p.real {b}|} ⊆
      ⋃ B ∈ T, {ω | ε / 2 ≤ ∑ b ∈ B, ((#{i ∈ s | Y i ω = b} : ℝ) / #s - p.real {b})} := by
    intro ω hω
    set u : β → ℝ := fun b ↦ (#{i ∈ s | Y i ω = b} : ℝ) / #s - p.real {b}
    have hu : ∑ b, u b = 0 := by
      have hcount : ∑ b, (#{i ∈ s | Y i ω = b} : ℝ) = #s := by
        exact_mod_cast (card_eq_sum_card_fiberwise fun i _ ↦ mem_univ (Y i ω)).symm
      simp only [u, sum_sub_distrib, ← sum_div, hcount, div_self hn.ne', sum_measureReal_singleton,
        coe_univ, probReal_univ, sub_self]
    have h_two := sum_abs_eq_two_nsmul_sum_filter_pos hu
    rw [two_nsmul] at h_two
    have hω' : ε ≤ ∑ b, |u b| := hω
    have hpos : ε / 2 ≤ ∑ b with 0 < u b, u b := by linarith
    refine Set.mem_iUnion₂.2 ⟨univ.filter fun b ↦ 0 < u b, ?_, hpos⟩
    refine mem_erase.2 ⟨fun h ↦ ?_, mem_erase.2 ⟨fun h ↦ ?_, mem_univ _⟩⟩
    · rw [h, hu] at hpos
      linarith
    · rw [h, sum_empty] at hpos
      linarith
  calc P.real {ω | ε ≤ ∑ b, |(#{i ∈ s | Y i ω = b} : ℝ) / #s - p.real {b}|}
      ≤ P.real (⋃ B ∈ T,
          {ω | ε / 2 ≤ ∑ b ∈ B, ((#{i ∈ s | Y i ω = b} : ℝ) / #s - p.real {b})}) :=
        measureReal_mono h_sub (measure_ne_top _ _)
    _ ≤ ∑ B ∈ T, P.real
          {ω | ε / 2 ≤ ∑ b ∈ B, ((#{i ∈ s | Y i ω = b} : ℝ) / #s - p.real {b})} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _B ∈ T, exp (-2 * #s * (ε / 2) ^ 2) :=
        sum_le_sum fun B _ ↦
          measureReal_le_sum_empirical_sub_le h_indep hY B (by positivity)
    _ = (2 ^ Fintype.card β - 2) * exp (-#s * ε ^ 2 / 2) := by
      rw [sum_const, nsmul_eq_mul, hT_card]
      congr 2
      ring

/-- **The `ℓ¹` deviation of the empirical law**, high-probability form [WOSVW03], [LS, Exercise
5.17]. If the `Y i`, `i ∈ s`, are independent with law `p` on a finite type `β`, then for `δ > 0`,
with probability at least `1 - δ`, the empirical law `p̂(b) = #{i ∈ s | Y i = b} / #s` satisfies
`∑ b, |p̂(b) - p(b)| < √(2 (log (1 / δ) + card β log 2) / #s)`. -/
theorem le_measureReal_sum_abs_empirical_sub_lt {Y : ι → Ω → β} (h_indep : iIndepFun Y P)
    {p : Measure β} {s : Finset ι} (hs : s.Nonempty) (hY : ∀ i ∈ s, HasLaw (Y i) p P)
    {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ P.real {ω | ∑ b, |(#{i ∈ s | Y i ω = b} : ℝ) / #s - p.real {b}| <
      √(2 * (log (1 / δ) + Fintype.card β * log 2) / #s)} := by
  obtain hδ₁ | hδ₁ := le_or_gt 1 δ
  · exact (sub_nonpos.2 hδ₁).trans measureReal_nonneg
  obtain ⟨i₀, hi₀⟩ := hs
  have hn : (0 : ℝ) < #s := by exact_mod_cast card_pos.2 ⟨i₀, hi₀⟩
  set m : ℕ := Fintype.card β
  set r := √(2 * (log (1 / δ) + m * log 2) / #s)
  have hL : 0 < log (1 / δ) + m * log 2 := by
    have : 0 < log (1 / δ) := log_pos (by rw [one_div]; exact one_lt_inv_iff₀.2 ⟨hδ, hδ₁⟩)
    have : 0 ≤ (m : ℝ) * log 2 := by positivity
    linarith
  have hr : 0 < r := sqrt_pos.2 (by positivity)
  have h_exp : exp (-#s * r ^ 2 / 2) = δ / 2 ^ m := by
    rw [sq_sqrt (by positivity), show -#s * (2 * (log (1 / δ) + m * log 2) / #s) / 2 =
      log δ - m * log 2 by field_simp; rw [one_div, log_inv]; ring, exp_sub, exp_log hδ,
      ← log_pow, exp_log (by positivity)]
  have h_bad : P.real {ω | r ≤ ∑ b, |(#{i ∈ s | Y i ω = b} : ℝ) / #s - p.real {b}|} ≤ δ := by
    refine (measure_sum_abs_empirical_sub_ge_le h_indep ⟨i₀, hi₀⟩ hY hr).trans ?_
    rw [h_exp, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have h_union : (Set.univ : Set Ω) ⊆
      {ω | ∑ b, |(#{i ∈ s | Y i ω = b} : ℝ) / #s - p.real {b}| < r} ∪
        {ω | r ≤ ∑ b, |(#{i ∈ s | Y i ω = b} : ℝ) / #s - p.real {b}|} :=
    fun ω _ ↦ by
      rw [Set.mem_union, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
      exact lt_or_ge _ _
  have h_one := (measureReal_mono (μ := P) h_union).trans (measureReal_union_le _ _)
  rw [probReal_univ] at h_one
  linarith

variable {α : Type*} {mα : MeasurableSpace α}

/-- **The `ℓ¹` deviation of the empirical law on a partition** [WOSVW03, Theorem 2.1], [LS,
Exercise 5.17]. If the `X i`, `i ∈ s`, are independent with law `ν` and `c` maps `α` measurably to
a finite type, then for `ε > 0` the empirical frequencies of the cells `c ⁻¹' {b}` satisfy
`P(ε ≤ ∑ b, |#{i ∈ s | c (X i) = b} / #s - ν (c ⁻¹' {b})|) ≤ (2 ^ card β - 2) exp (-#s ε² / 2)`. -/
theorem measure_sum_abs_empirical_preimage_sub_ge_le {X : ι → Ω → α} (h_indep : iIndepFun X P)
    {ν : Measure α} {s : Finset ι} (hs : s.Nonempty) (hX : ∀ i ∈ s, HasLaw (X i) ν P)
    {c : α → β} (hc : Measurable c) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ ∑ b, |(#{i ∈ s | c (X i ω) = b} : ℝ) / #s - ν.real (c ⁻¹' {b})|} ≤
      (2 ^ Fintype.card β - 2) * exp (-#s * ε ^ 2 / 2) := by
  simpa [map_measureReal_apply hc (measurableSet_singleton _)] using
    measure_sum_abs_empirical_sub_ge_le (Y := fun i ↦ c ∘ X i) (p := ν.map c)
      (h_indep.comp (fun _ ↦ c) fun _ ↦ hc) hs
      (fun i hi ↦ (hasLaw_map hc.aemeasurable).comp (hX i hi)) hε

/-- **The `ℓ¹` deviation of the empirical law on a partition**, high-probability form [WOSVW03],
[LS, Exercise 5.17]. If the `X i`, `i ∈ s`, are independent with law `ν` and `c` maps `α`
measurably to a finite type, then for `δ > 0`, with probability at least `1 - δ`, the empirical
frequencies of the cells `c ⁻¹' {b}` satisfy
`∑ b, |#{i ∈ s | c (X i) = b} / #s - ν (c ⁻¹' {b})| < √(2 (log (1 / δ) + card β log 2) / #s)`. -/
theorem le_measureReal_sum_abs_empirical_preimage_sub_lt {X : ι → Ω → α}
    (h_indep : iIndepFun X P) {ν : Measure α} {s : Finset ι} (hs : s.Nonempty)
    (hX : ∀ i ∈ s, HasLaw (X i) ν P) {c : α → β} (hc : Measurable c) {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ P.real {ω | ∑ b, |(#{i ∈ s | c (X i ω) = b} : ℝ) / #s - ν.real (c ⁻¹' {b})| <
      √(2 * (log (1 / δ) + Fintype.card β * log 2) / #s)} := by
  simpa [map_measureReal_apply hc (measurableSet_singleton _)] using
    le_measureReal_sum_abs_empirical_sub_lt (Y := fun i ↦ c ∘ X i) (p := ν.map c)
      (h_indep.comp (fun _ ↦ c) fun _ ↦ hc) hs
      (fun i hi ↦ (hasLaw_map hc.aemeasurable).comp (hX i hi)) hδ

end LMLExplore
