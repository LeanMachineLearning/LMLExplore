/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import LMLExplore.Algebra.Order.Antidiag.FinsuppEquiv
public import LMLExplore.InformationTheory.KullbackLeibler.Finite
public import TauCeti.Probability.Process.EmpiricalMeasure

/-!
# The method of types and Sanov's bound

Let `α` be a finite type with `m = Fintype.card α` elements. The *type* of a sequence
`x : Fin n → α` is its vector of counts `LMLExplore.typeCount x : α → ℕ`, `a ↦ #{k | x k = a}`,
and its empirical distribution is Tau Ceti's empirical measure
`TauCeti.Probability.empiricalFiniteMeasure x`, which gives each letter `a` the mass
`typeCount x a / n`. The *type class* of `x` is the set of sequences with the same type as `x`.
The method of types bounds the probability of a deviation of the empirical distribution of an
i.i.d. sample by a union bound over the types, which are few [CT, Theorem 11.1.1], of the
probabilities of the type classes, which are exponentially small [CT, Theorem 11.1.4].

Let `X : Fin n → Ω → α` be independent with law `ν`, and `p̂ₙ` be the empirical distribution of
`(X 0, …, X (n - 1))`.

## Main statements

* `LMLExplore.card_image_typeCount_le`: there are at most `(n + 1) ^ (m - 1)` types of sequences
  of length `n`, hence at most `(n + 1) ^ m`.
* `LMLExplore.measure_typeCount_eq_le`: the type class of `x` has probability at most
  `exp (-n t)` whenever `t ≤ KL(p̂(x) ‖ ν)`, where `p̂(x)` is the empirical distribution of `x`.
* `LMLExplore.measure_lt_klDiv_empiricalFiniteMeasure_le`: **Sanov's bound**
  `ℙ(KL(p̂ₙ ‖ ν) > t) ≤ (n + 1) ^ (m - 1) exp (-n t)`, which implies the bound
  `(n + 1) ^ m exp (-n t)` of [CT, Theorem 11.2.1] and [EV26, Lemma 19].
* `LMLExplore.measure_log_div_lt_klDiv_empiricalFiniteMeasure_le`: its confidence form: for
  `δ > 0` and `n ≥ 1`, `KL(p̂ₙ ‖ ν) ≤ ((m - 1) log (n + 1) + log (1 / δ)) / n` with probability at
  least `1 - δ`.

## References

* [CT] T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006.
* [EV26] A. Essakine and C. Vernade, *Tight sample complexity bounds for entropic best policy
  identification*, COLT 2026, arXiv:2605.13717.

The method-of-types bounds are adapted from the formalization Essakine2026Tight
(`github.com/RemyDegenne/Essakine2026Tight`, file
`ForLMLExplore/InformationTheory/MethodOfTypes.lean`, commit
`520dd39a55fa4e9a62a4a2d51f48163926176a5d`, by Rémy Degenne, Apache 2.0) of [EV26].
-/

public section

open Finset MeasureTheory ProbabilityTheory Real InformationTheory TauCeti.Probability
open scoped ENNReal

namespace LMLExplore

variable {α : Type*} [DecidableEq α] {n : ℕ}

section Types

/-- The *type* of a finite sequence `x : Fin n → α`: the number `#{k | x k = a}` of occurrences
of each letter `a`. -/
def typeCount (x : Fin n → α) (a : α) : ℕ := #{k | x k = a}

lemma typeCount_def (x : Fin n → α) (a : α) : typeCount x a = #{k | x k = a} := (rfl)

/-- A letter has a positive count if and only if it occurs in the sequence. -/
lemma typeCount_pos_iff {x : Fin n → α} {a : α} : 0 < typeCount x a ↔ ∃ k, x k = a := by
  simp [typeCount_def, card_pos, Finset.Nonempty]

/-- A letter has count zero if and only if it does not occur in the sequence. -/
@[simp]
lemma typeCount_eq_zero_iff {x : Fin n → α} {a : α} : typeCount x a = 0 ↔ ∀ k, x k ≠ a := by
  simp [typeCount_def, filter_eq_empty_iff]

/-- The counts of a sequence of length `n` sum to `n`. -/
@[simp]
lemma sum_typeCount [Fintype α] (x : Fin n → α) : ∑ a, typeCount x a = n := by
  simp_rw [typeCount_def]
  rw [← card_eq_sum_card_fiberwise fun k _ ↦ mem_univ (x k), card_univ, Fintype.card_fin]

/-- The type of a sequence of length `n` is a vector of natural numbers of sum `n`. -/
lemma typeCount_mem_piAntidiag [Fintype α] (x : Fin n → α) :
    typeCount x ∈ piAntidiag univ n := by
  simp

/-- A product over the terms of a sequence only depends on its type:
`∏ k, f (x k) = ∏ a, f a ^ typeCount x a`. -/
lemma prod_comp_eq_prod_pow_typeCount [Fintype α] {M : Type*} [CommMonoid M] (f : α → M)
    (x : Fin n → α) : ∏ k, f (x k) = ∏ a, f a ^ typeCount x a := by
  rw [← prod_fiberwise' univ x f]
  refine prod_congr rfl fun a _ ↦ ?_
  rw [prod_const, typeCount_def]

/-- **The number of types**: the sequences of length `n` with letters in a finite type with `m`
elements have at most `(n + 1) ^ (m - 1)` types. -/
theorem card_image_typeCount_le [Fintype α] :
    #(univ.image (typeCount : (Fin n → α) → α → ℕ)) ≤ (n + 1) ^ (Fintype.card α - 1) :=
  (card_le_card (image_subset_iff.2 fun x _ ↦ typeCount_mem_piAntidiag x)).trans
    (card_piAntidiag_nat_le_pow univ n)

variable [MeasurableSpace α]

omit [DecidableEq α] in
/-- The empirical distribution of a finite family `x` is absolutely continuous with respect to a
measure `ν` as soon as every term of `x` is an atom of `ν`. -/
lemma empiricalFiniteMeasure_absolutelyContinuous {κ : Type*} [Fintype κ] {ν : Measure α}
    {x : κ → α} (hx : ∀ i, ν {x i} ≠ 0) : (empiricalFiniteMeasure x : Measure α) ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hνs ↦ ?_
  rw [empiricalFiniteMeasure_apply hs]
  refine mul_eq_zero_of_right _ (sum_eq_zero fun i _ ↦ Set.indicator_of_notMem (fun hi ↦ ?_) _)
  exact hx i (measure_mono_null (Set.singleton_subset_iff.2 hi) hνs)

variable [MeasurableSingletonClass α]

/-- The empirical distribution of a sequence of length `n` gives each letter `a` the mass
`typeCount x a / n`. -/
lemma measureReal_empiricalFiniteMeasure_singleton (x : Fin n → α) (a : α) :
    (empiricalFiniteMeasure x : Measure α).real {a} = typeCount x a / n := by
  rw [measureReal_def, empiricalFiniteMeasure_apply (measurableSet_singleton a), Fintype.card_fin]
  simp [Set.indicator_apply, typeCount_def, div_eq_inv_mul, eq_comm]

/-- The product measure of a type class: `ν^{⊗n}{y | typeCount y = N}` is the number of sequences
of type `N` times `∏ a, ν{a} ^ N a`. -/
lemma pi_setOf_typeCount_eq [Fintype α] {ν : Measure α} [SigmaFinite ν] (N : α → ℕ) :
    Measure.pi (fun _ : Fin n ↦ ν) {y | typeCount y = N}
      = #{y : Fin n → α | typeCount y = N} * ∏ a, ν {a} ^ N a := by
  have hset : {y : Fin n → α | typeCount y = N}
      = ((univ.filter fun y : Fin n → α ↦ typeCount y = N : Finset _) : Set (Fin n → α)) := by
    simp
  rw [hset, ← sum_measure_singleton, ← nsmul_eq_mul, ← sum_const]
  refine sum_congr rfl fun y hy ↦ ?_
  rw [Measure.pi_singleton, prod_comp_eq_prod_pow_typeCount (fun a ↦ ν {a}) y,
    (mem_filter.1 hy).2]

/-- **The ratio of the probabilities of a sequence under `ν` and under its type**: if every term
of `x` is an atom of `ν`, then `∏ a, ν{a} ^ N a = (∏ a, Q{a} ^ N a) exp (-n KL(Q ‖ ν))`, where
`N = typeCount x` and `Q` is the empirical distribution of `x`, and the relative entropy is that of
the vectors of masses [CT, Theorem 11.1.2]. -/
lemma prod_measureReal_pow_typeCount_eq_mul_exp [Fintype α] {ν : Measure α} [IsFiniteMeasure ν]
    {x : Fin n → α} (hx : ∀ k, ν {x k} ≠ 0) :
    ∏ a, ν.real {a} ^ typeCount x a
      = (∏ a, (empiricalFiniteMeasure x : Measure α).real {a} ^ typeCount x a)
        * exp (-(n * ∑ a, (empiricalFiniteMeasure x : Measure α).real {a}
          * log ((empiricalFiniteMeasure x : Measure α).real {a} / ν.real {a}))) := by
  rw [mul_sum, ← sum_neg_distrib, exp_sum, ← prod_mul_distrib]
  refine prod_congr rfl fun a _ ↦ ?_
  rcases Nat.eq_zero_or_pos (typeCount x a) with hNa | hNa
  · rw [measureReal_empiricalFiniteMeasure_singleton, hNa]
    simp
  obtain ⟨k, rfl⟩ := typeCount_pos_iff.1 hNa
  have hn : (n : ℝ) ≠ 0 := by
    have : 0 < n := k.pos
    positivity
  have hνa : 0 < ν.real {x k} := ENNReal.toReal_pos (hx k) (measure_ne_top ν _)
  have hQa : 0 < (empiricalFiniteMeasure x : Measure α).real {x k} := by
    rw [measureReal_empiricalFiniteMeasure_singleton]
    positivity
  have hnQ : n * (empiricalFiniteMeasure x : Measure α).real {x k} = typeCount x (x k) := by
    rw [measureReal_empiricalFiniteMeasure_singleton]
    field_simp
  rw [← mul_assoc, hnQ, ← log_pow, ← log_inv, exp_log (by positivity), div_pow]
  field_simp

end Types

section Sanov

variable [MeasurableSpace α] [MeasurableSingletonClass α]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Fin n → Ω → α} {ν : Measure α}

/-- **The probability of a type class**: if `X` is an i.i.d. sample of size `n` with law `ν` on a
finite type, then the sample has the type of a sequence `x` with probability at most `exp (-n t)`
whenever `t ≤ KL(p̂(x) ‖ ν)`, where `p̂(x)` is the empirical distribution of `x`
[CT, Theorem 11.1.4]. -/
theorem measure_typeCount_eq_le [Finite α] (hX : iIndepFun X μ) (hlaw : ∀ k, HasLaw (X k) ν μ)
    (x : Fin n → α) {t : ℝ}
    (ht : ENNReal.ofReal t ≤ klDiv (empiricalFiniteMeasure x : Measure α) ν) :
    μ {ω | typeCount (fun k ↦ X k ω) = typeCount x} ≤ ENNReal.ofReal (exp (-(n * t))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using prob_le_one
  have : Fintype α := Fintype.ofFinite α
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : IsProbabilityMeasure ν := (hlaw ⟨0, hn⟩).isProbabilityMeasure_iff.1 inferInstance
  set Q := (empiricalFiniteMeasure x : Measure α)
  set N := typeCount x
  -- the law of the sample is `ν^{⊗n}`
  rw [(hX.hasLaw_pi hlaw).measure_eq (p := fun y ↦ typeCount y = N)
    (Set.toFinite _).measurableSet, pi_setOf_typeCount_eq]
  -- if a letter of `x` has mass zero under `ν`, the type class is `ν^{⊗n}`-null
  by_cases hsupp : ∀ a, 0 < N a → ν {a} ≠ 0
  swap
  · push Not at hsupp
    obtain ⟨a, hNa, hνa⟩ := hsupp
    rw [prod_eq_zero (mem_univ a) (by rw [hνa, zero_pow hNa.ne']), mul_zero]
    exact zero_le
  have hx (k : Fin n) : ν {x k} ≠ 0 := hsupp _ (typeCount_pos_iff.2 ⟨k, rfl⟩)
  -- the type class has `Q^{⊗n}`-probability at most one
  have hQle : (#{y : Fin n → α | typeCount y = N} : ℝ) * ∏ a, Q.real {a} ^ N a ≤ 1 := by
    simpa [measureReal_def, pi_setOf_typeCount_eq, ENNReal.toReal_prod] using
      measureReal_le_one (μ := Measure.pi fun _ : Fin n ↦ Q) (s := {y | typeCount y = N})
  -- the relative entropy of `Q` with respect to `ν` is at least `t`
  have hac : Q ≪ ν := empiricalFiniteMeasure_absolutelyContinuous hx
  have htKL : t ≤ ∑ a, Q.real {a} * log (Q.real {a} / ν.real {a}) := by
    have h := toReal_klDiv_eq_sum_mul_log_div hac
    rw [probReal_univ, probReal_univ, add_sub_cancel_right] at h
    rw [← h]
    exact (ENNReal.ofReal_le_iff_le_toReal (klDiv_ne_top hac Integrable.of_finite)).1 ht
  have hreal : ∏ a, ν {a} ^ N a = ENNReal.ofReal (∏ a, ν.real {a} ^ N a) := by
    rw [ENNReal.ofReal_prod_of_nonneg fun a _ ↦ by positivity]
    refine prod_congr rfl fun a _ ↦ ?_
    rw [ENNReal.ofReal_pow measureReal_nonneg, ofReal_measureReal (measure_ne_top ν _)]
  rw [hreal, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [prod_measureReal_pow_typeCount_eq_mul_exp hx, ← mul_assoc]
  calc _ ≤ 1 * exp (-(n * t)) := by gcongr
    _ = exp (-(n * t)) := one_mul _

omit [DecidableEq α] in
/-- **Sanov's bound** [CT, Theorem 11.2.1], [EV26, Lemma 19]: if `X` is an i.i.d. sample of size
`n` with law `ν` on a finite type with `m` elements, then its empirical distribution `p̂ₙ`
satisfies `ℙ(KL(p̂ₙ ‖ ν) > t) ≤ (n + 1) ^ (m - 1) exp (-n t)` for every `t`. The exponent `m - 1`
improves on the exponent `m` of [CT, Theorem 11.2.1] and of the proof of [EV26, Lemma 19]. -/
theorem measure_lt_klDiv_empiricalFiniteMeasure_le [Fintype α] (hX : iIndepFun X μ)
    (hlaw : ∀ k, HasLaw (X k) ν μ) (t : ℝ) :
    μ {ω | ENNReal.ofReal t < klDiv (empiricalFiniteMeasure fun k ↦ X k ω : Measure α) ν}
      ≤ ENNReal.ofReal ((n + 1) ^ (Fintype.card α - 1) * exp (-(n * t))) := by
  classical
  -- the types of the sequences whose empirical distribution is far from `ν`
  set C := (univ.filter fun x : Fin n → α ↦
    ENNReal.ofReal t < klDiv (empiricalFiniteMeasure x : Measure α) ν).image typeCount
  have hsub : {ω | ENNReal.ofReal t < klDiv (empiricalFiniteMeasure fun k ↦ X k ω : Measure α) ν}
      ⊆ ⋃ N ∈ C, {ω | typeCount (fun k ↦ X k ω) = N} := fun ω hω ↦
    Set.mem_biUnion (mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, hω⟩)) rfl
  have hcard : #C ≤ (n + 1) ^ (Fintype.card α - 1) :=
    (card_le_card (image_subset_image (filter_subset _ _))).trans card_image_typeCount_le
  calc _ ≤ μ (⋃ N ∈ C, {ω | typeCount (fun k ↦ X k ω) = N}) := measure_mono hsub
    _ ≤ ∑ N ∈ C, μ {ω | typeCount (fun k ↦ X k ω) = N} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _N ∈ C, ENNReal.ofReal (exp (-(n * t))) := by
        refine sum_le_sum fun N hN ↦ ?_
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hN
        exact measure_typeCount_eq_le hX hlaw x (mem_filter.1 hx).2.le
    _ = #C * ENNReal.ofReal (exp (-(n * t))) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ((n + 1) ^ (Fintype.card α - 1) : ℕ) * ENNReal.ofReal (exp (-(n * t))) := by gcongr
    _ = ENNReal.ofReal ((n + 1) ^ (Fintype.card α - 1) * exp (-(n * t))) := by
        rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast]
        norm_cast

omit [DecidableEq α] in
/-- **Sanov's bound**, confidence form: if `X` is an i.i.d. sample of size `n ≥ 1` with law `ν` on
a finite type with `m` elements and `δ > 0`, then with probability at least `1 - δ` its empirical
distribution `p̂ₙ` satisfies `KL(p̂ₙ ‖ ν) ≤ ((m - 1) log (n + 1) + log (1 / δ)) / n`. -/
theorem measure_log_div_lt_klDiv_empiricalFiniteMeasure_le [Fintype α] (hX : iIndepFun X μ)
    (hlaw : ∀ k, HasLaw (X k) ν μ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | ENNReal.ofReal (((Fintype.card α - 1 : ℕ) * log (n + 1) + log (1 / δ)) / n)
        < klDiv (empiricalFiniteMeasure fun k ↦ X k ω : Measure α) ν}
      ≤ ENNReal.ofReal δ := by
  refine (measure_lt_klDiv_empiricalFiniteMeasure_le hX hlaw _).trans_eq ?_
  have hnR : (n : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hnR, ← log_pow, ← log_mul (by positivity) (by positivity), exp_neg,
    exp_log (by positivity)]
  congr 1
  field_simp

end Sanov

end LMLExplore
