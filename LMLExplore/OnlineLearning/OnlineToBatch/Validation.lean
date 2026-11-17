/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.OnlineToBatch.HighProbability

/-!
# Selection on a validation sample

An online learner run on `n` data produces `n` plays, and an online-to-batch conversion must turn
them into one predictor. When the risk is not convex, the average play is of no use, but the
best of the plays is at least as good as their average. Its risk is unknown, and it is estimated
on fresh data: a **validation sample**.

This file proves that the empirical risk minimizer over a finite set of candidates, fixed before
the validation data are seen, is close to the best candidate [Ora, Theorem 3.17]. Let `c i`,
for `i` in a finite type `ι`, be candidates known at time `0` of a filtration `ℱ`, let
`ξ 0, …, ξ (m - 1)` be the validation data, with `ξ t` known at time `t + 1`, and let `f` be a
loss with values in `[0, 1]` whose conditional mean given `ℱ t` at each candidate is its risk:
`μ[f (c i) (ξ t) | ℱ t] = F (c i)`. If `c (k ω)` minimizes the cumulative validation loss
`∑ t < m, f (c i) (ξ t)` over the candidates, then for `δ > 0`, with probability at least
`1 - δ`,
`F (c (k ω)) ≤ F (c i) + √(2 log (2 |ι| / δ) / m)` for every candidate `i`.

The candidates may be random, for instance the plays of an online learner on a training sample:
what matters is that they are known before the validation data are drawn. The proof bounds the
deviation of the validation loss of every candidate from its risk, by the two-sided
Azuma–Hoeffding inequality `measureReal_le_abs_sum_sub_le` and a union bound over the candidates.
The selected candidate is random, so no concentration inequality applies to it directly; the
uniform deviation bound applies to it as to every candidate. The constant improves by a factor `2`
the `2 √(2 log (2 |ι| / δ) / m)` of [Ora, Theorem 3.17], whose proof uses Hoeffding's inequality
with the exponent `-ε ^ 2 m / 8` in place of `-ε ^ 2 m / 2`.

## Main statements

* `LMLExplore.OnlineLearning.measureReal_exists_add_sqrt_lt_le`: [Ora, Theorem 3.17] the risk of
  the empirical risk minimizer over the candidates exceeds that of some candidate by more than
  `√(2 log (2 |ι| / δ) / m)` with probability at most `δ`.
* `LMLExplore.OnlineLearning.measureReal_exists_add_sqrt_lt_le_of_indep`: the same bound for
  validation data independent of the past with a common law `ρ`, and the risk
  `F y = ∫ z, f y z ∂ρ`.

## References

* [Ora] F. Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*,
  arXiv:1912.13213v10, Theorem 3.17.
-/

public section

open MeasureTheory ProbabilityTheory Real Finset

namespace LMLExplore.OnlineLearning

variable {Ω α Z ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ} {mα : MeasurableSpace α} {mZ : MeasurableSpace Z} [Fintype ι]
  {f : α → Z → ℝ} {F : α → ℝ} {c : ι → Ω → α} {k : Ω → ι} {ξ : ℕ → Ω → Z} {m : ℕ} {δ : ℝ}

/-- **Selection on a validation sample** [Ora, Theorem 3.17]. Let `c i`, for `i` in a finite type
`ι`, be candidates known at time `0`, `f` a loss with values in `[0, 1]` whose conditional mean
given `ℱ t` at each candidate is its risk `F (c i)` for `t < m`, and `c (k ω)` a candidate with the
smallest cumulative loss on the validation data `ξ 0, …, ξ (m - 1)`. Then for `m ≠ 0` and `δ > 0`,
the event that some candidate `i` has `F (c i) + √(2 log (2 |ι| / δ) / m) < F (c (k ω))` has
probability at most `δ`. -/
theorem measureReal_exists_add_sqrt_lt_le (hf : Measurable (Function.uncurry f))
    (hf01 : ∀ y z, f y z ∈ Set.Icc 0 1) (hc : ∀ i, Measurable[ℱ 0] (c i))
    (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hF : ∀ i, ∀ t < m, μ[fun ω ↦ f (c i ω) (ξ t ω) | ℱ t] =ᵐ[μ] fun ω ↦ F (c i ω))
    (hk : ∀ ω i, ∑ t ∈ range m, f (c (k ω) ω) (ξ t ω) ≤ ∑ t ∈ range m, f (c i ω) (ξ t ω))
    (hm : m ≠ 0) (hδ : 0 < δ) :
    μ.real {ω | ∃ i, F (c i ω) + √(2 * log (2 * Fintype.card ι / δ) / m) < F (c (k ω) ω)} ≤
      δ := by
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact measureReal_le_one.trans hδ1
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [hδ.le]
  set K : ℝ := (Fintype.card ι : ℝ)
  have hK : 1 ≤ K := Nat.one_le_cast.2 Fintype.card_pos
  have hm' : (0 : ℝ) < m := by positivity
  set L := log (2 * K / δ)
  have hL : 0 < L := log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  -- The deviation `ε` of the cumulative validation loss of each candidate from `m` times its
  -- risk, chosen so that each candidate deviates by `ε` with probability at most `δ / K`.
  set ε : ℝ := m * √(L / (2 * m)) with hε_def
  have hε : 0 ≤ ε := by positivity
  have hεm : 2 * ε / m = √(2 * L / m) := by
    rw [show 2 * L / m = 2 ^ 2 * (L / (2 * m)) by field_simp, sqrt_mul (by positivity),
      sqrt_sq zero_le_two, hε_def]
    field_simp
  have hdev (i : ι) :
      μ.real {ω | ε ≤ |∑ t ∈ range m, (F (c i ω) - f (c i ω) (ξ t ω))|} ≤ δ / K := by
    refine (measureReal_le_abs_sum_sub_le (x := fun _ ↦ c i) hf hf01
      (fun t ↦ (hc i).mono (ℱ.mono t.zero_le) le_rfl) hξ (hF i) hε).trans_eq ?_
    rw [mul_pow, sq_sqrt (by positivity),
      show -2 * ((m : ℝ) ^ 2 * (L / (2 * m))) / m = -L by field_simp, exp_neg,
      exp_log (by positivity)]
    field_simp
  refine (measureReal_mono fun ω hω ↦ ?_).trans ((measureReal_iUnion_fintype_le fun i ↦
    {ω | ε ≤ |∑ t ∈ range m, (F (c i ω) - f (c i ω) (ξ t ω))|}).trans ?_)
  · -- If every candidate deviates by less than `ε`, the selected candidate is within `2 ε / m`
    -- of every candidate.
    obtain ⟨i, hi⟩ := hω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    by_contra! h
    have hdi := (abs_lt.1 (h i)).1
    have hdk := (abs_lt.1 (h (k ω))).2
    simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at hdi hdk
    rw [← hεm] at hi
    have hi' := mul_lt_mul_of_pos_right hi hm'
    rw [add_mul, div_mul_cancel₀ _ hm'.ne'] at hi'
    linarith [hk ω i]
  · refine (sum_le_sum fun i _ ↦ hdev i).trans_eq ?_
    rw [sum_const, card_univ, nsmul_eq_mul, mul_div_cancel₀ _ (by positivity)]

/-- **Selection on a validation sample for independent data** [Ora, Theorem 3.17]. If each
validation datum `ξ t`, `t < m`, is independent of `ℱ t` with law `ρ`, the loss `f` has values in
`[0, 1]`, and `c (k ω)` is a candidate known at time `0` with the smallest cumulative validation
loss, then for the risk `F y = ∫ z, f y z ∂ρ`, `m ≠ 0` and `δ > 0`, the event that some candidate
`i` has `F (c i) + √(2 log (2 |ι| / δ) / m) < F (c (k ω))` has probability at most `δ`. -/
theorem measureReal_exists_add_sqrt_lt_le_of_indep {ρ : Measure Z}
    (hf : Measurable (Function.uncurry f)) (hf01 : ∀ y z, f y z ∈ Set.Icc 0 1)
    (hc : ∀ i, Measurable[ℱ 0] (c i)) (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hindep : ∀ t < m, Indep (mZ.comap (ξ t)) (ℱ t) μ) (hρ : ∀ t < m, μ.map (ξ t) = ρ)
    (hk : ∀ ω i, ∑ t ∈ range m, f (c (k ω) ω) (ξ t ω) ≤ ∑ t ∈ range m, f (c i ω) (ξ t ω))
    (hm : m ≠ 0) (hδ : 0 < δ) :
    μ.real {ω | ∃ i, ∫ z, f (c i ω) z ∂ρ + √(2 * log (2 * Fintype.card ι / δ) / m) <
      ∫ z, f (c (k ω) ω) z ∂ρ} ≤ δ :=
  measureReal_exists_add_sqrt_lt_le (F := fun y ↦ ∫ z, f y z ∂ρ) hf hf01 hc hξ
    (fun i t ht ↦ condExp_ae_eq_integral_of_indep hf hf01
      ((hc i).mono (ℱ.mono t.zero_le) le_rfl) hξ (hindep t ht) (hρ t ht)) hk hm hδ

end LMLExplore.OnlineLearning
