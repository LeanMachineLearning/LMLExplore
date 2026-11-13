/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.MinimaxLowerBound

/-!
# Finite-time instance-dependent lower bounds

The Lai–Robbins lower bound (`LMLExplore.Bandits.LaiRobbins`) is asymptotic: it holds for
algorithms whose regret is `o(n ^ p)` for every `p > 0`. This file proves its finite-time
analogue [LS, §16.2], where consistency is replaced by a bound `C n ^ p` on the regret at a single
horizon `n` on a neighbourhood of the bandit.

Let `ν` and `ν'` be two bandits that differ only in the law of the arm `i`, and write
`Δ = min (μ_i(ν') - μ*(ν), Δ_i(ν))`, which is `min (λ - Δ_i, Δ_i)` for `λ = μ_i(ν') - μ_i(ν)`.
The divergence decomposition and the two-bandit inequality of the minimax lower bound give
`Δ n exp (-E_ν[T_i(n)] D(ν_i, ν'_i)) / 2 ≤ R_n(ν) + R_n(ν')`, and taking logarithms,
`E_ν[T_i(n)] ≥ log (Δ n / (2 (R_n(ν) + R_n(ν')))) / D(ν_i, ν'_i)` [LS, Lemma 16.3]. Here the
denominator inside the logarithm is `2` where [LS, (16.4)] has `4`, because the two-bandit
inequality applies the Bretagnolle–Huber inequality at every round rather than once.

For a Gaussian bandit with variance `σ²`, means `μ` and gaps `Δ`, the alternative bandit moves the
mean of a suboptimal arm `i` to `μ_i + (1 + ε) Δ_i`. If the regret at horizon `n` is at most
`C n ^ p` on every Gaussian bandit with means in `∏_a [μ_a, μ_a + 2 Δ_a]`, then
`E[R_n] ≥ 2 σ² / (1 + ε)² ∑_{a : Δ_a > 0} ((1 - p) log n + log (ε Δ_a / (4 C)))⁺ / Δ_a`
for every `ε ∈ (0, 1]` [LS, Theorem 16.4], with `4 C` where [LS] has `8 C`.

## Main statements

* `LMLExplore.Bandits.mul_exp_neg_le_integral_regret_add_integral_regret`: the two-bandit
  inequality for bandits that differ in one arm, in exponential form.
* `LMLExplore.Bandits.log_div_le_integral_pullCount`: [LS, Lemma 16.3].
* `LMLExplore.Bandits.le_integral_pullCount_gaussianBandit`: the lower bound on the expected
  number of pulls of a suboptimal arm of a Gaussian bandit.
* `LMLExplore.Bandits.le_integral_regret_gaussianBandit`: [LS, Theorem 16.4] for Gaussian bandits
  with variance `σ²`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemma 16.3 and Theorem 16.4.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset Real Learning Bandits
open scoped ENNReal NNReal

namespace LMLExplore.Bandits

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]

section Runs

variable [Finite α] [DecidableEq α] {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
  {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
  [IsProbabilityMeasure P']
  {A : ℕ → Ω → α} {A' : ℕ → Ω' → α} {ν ν' : Kernel α ℝ} [IsMarkovKernel ν] [IsMarkovKernel ν']
  {alg : Algorithm Unit α ℝ} {O : ℕ → Ω → Unit} {R : ℕ → Ω → ℝ} {O' : ℕ → Ω' → Unit}
  {R' : ℕ → Ω' → ℝ} {i : α}

/-- **Two-bandit inequality for bandits that differ in one arm.** Run an algorithm against two
stationary bandits `ν` and `ν'` that differ only in the law of the arm `i`, with
`D(ν_i, ν'_i) < ∞`. With `Δ = min (μ_i(ν') - μ*(ν), Δ_i(ν))`, the two expected regrets at horizon
`n` add up to at least `Δ n exp (-E_ν[T_i(n)] D(ν_i, ν'_i)) / 2`. The bound is only informative
when `i` is suboptimal in `ν` and its mean in `ν'` exceeds every mean of `ν`, so that `Δ > 0`. -/
theorem mul_exp_neg_le_integral_regret_add_integral_regret
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P)
    (h' : IsAlgEnvSeq O' A' R' alg (Environment.bandit ν') P') (hνν' : ∀ a ≠ i, ν a = ν' a)
    (hD : klDiv (ν i) (ν' i) ≠ ∞) (n : ℕ) :
    min ((ν' i)[id] - ⨆ a, (ν a)[id]) (gap ν i) * n *
        exp (-((∫ ω, (pullCount A i n ω : ℝ) ∂P) * (klDiv (ν i) (ν' i)).toReal)) / 2 ≤
      ∫ ω, regret ν A n ω ∂P + ∫ ω, regret ν' A' n ω ∂P' := by
  set Δ := min ((ν' i)[id] - ⨆ a, (ν a)[id]) (gap ν i)
  set T := ∫ ω, (pullCount A i n ω : ℝ) ∂P
  set D := (klDiv (ν i) (ν' i)).toReal
  rcases lt_or_ge Δ 0 with hΔ | hΔ
  · -- For `Δ < 0` the left-hand side is nonpositive and the regrets are nonnegative.
    have hl : Δ * n * exp (-(T * D)) / 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hΔ.le (Nat.cast_nonneg n)) (exp_pos _).le) zero_le_two
    exact hl.trans (add_nonneg (integral_nonneg fun _ ↦ regret_nonneg)
      (integral_nonneg fun _ ↦ regret_nonneg))
  -- In `ν'`, every arm other than `i` has gap at least `Δ`.
  have hgap' : ∀ b ≠ i, Δ ≤ gap ν' b := fun b hb ↦ by
    have h1 := sub_le_gap ν' b i
    have h2 : (ν b)[id] ≤ ⨆ b, (ν b)[id] :=
      le_ciSup (f := fun b ↦ (ν b)[id]) (Set.finite_range _).bddAbove b
    rw [← hνν' b hb] at h1
    exact (min_le_left _ _).trans (by linarith)
  -- The relative entropy between the laws of the histories is at most `T D`.
  have hKL := h.klDiv_map_history_le_ofReal_integral_pullCount_mul h' hνν'
    (ENNReal.ofReal_toReal hD).ge n
  have htwo := le_integral_regret_add_integral_regret' h h' hΔ (min_le_right _ _) hgap' n
    (hKL.trans_lt ENNReal.ofReal_lt_top).ne
  have hK := ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (integral_nonneg fun _ ↦ Nat.cast_nonneg _) ENNReal.toReal_nonneg) hKL
  calc Δ * n * exp (-(T * D)) / 2
      ≤ Δ * n * exp (-(klDiv (P.map (history O A R n)) (P'.map (history O' A' R' n))).toReal) /
          2 := by gcongr
    _ ≤ _ := htwo

/-- **[LS, Lemma 16.3].** Run an algorithm against two stationary bandits `ν` and `ν'` that differ
only in the law of the arm `i`, where `i` is suboptimal in `ν` and its mean in `ν'` exceeds every
mean of `ν`, with `D(ν_i, ν'_i) < ∞`. With `Δ = min (μ_i(ν') - μ*(ν), Δ_i(ν))`,
`E_ν[T_i(n)] ≥ log (Δ n / (2 (R_n(ν) + R_n(ν')))) / D(ν_i, ν'_i)`. [LS, (16.4)] has `4` where this
statement has `2`. -/
theorem log_div_le_integral_pullCount (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P)
    (h' : IsAlgEnvSeq O' A' R' alg (Environment.bandit ν') P') (hνν' : ∀ a ≠ i, ν a = ν' a)
    (hi : 0 < gap ν i) (hmean : (⨆ a, (ν a)[id]) < (ν' i)[id]) (hD : klDiv (ν i) (ν' i) ≠ ∞)
    (n : ℕ) :
    log (min ((ν' i)[id] - ⨆ a, (ν a)[id]) (gap ν i) * n /
        (2 * (∫ ω, regret ν A n ω ∂P + ∫ ω, regret ν' A' n ω ∂P'))) /
          (klDiv (ν i) (ν' i)).toReal ≤ ∫ ω, (pullCount A i n ω : ℝ) ∂P := by
  set Δ := min ((ν' i)[id] - ⨆ a, (ν a)[id]) (gap ν i)
  set S := ∫ ω, regret ν A n ω ∂P + ∫ ω, regret ν' A' n ω ∂P'
  set T := ∫ ω, (pullCount A i n ω : ℝ) ∂P
  set D := (klDiv (ν i) (ν' i)).toReal
  have hΔ : 0 < Δ := lt_min (sub_pos.mpr hmean) hi
  have hS : 0 ≤ S := add_nonneg (integral_nonneg fun _ ↦ regret_nonneg)
    (integral_nonneg fun _ ↦ regret_nonneg)
  have hTD : 0 ≤ T * D := mul_nonneg (integral_nonneg fun _ ↦ Nat.cast_nonneg _)
    ENNReal.toReal_nonneg
  refine div_le_of_le_mul₀ ENNReal.toReal_nonneg (integral_nonneg fun _ ↦ Nat.cast_nonneg _) ?_
  rcases (by positivity : (0 : ℝ) ≤ Δ * n / (2 * S)).eq_or_lt with h0 | hpos
  · rw [← h0, log_zero]
    exact hTD
  -- The argument of the logarithm is at most `exp (T D)`.
  have hS0 : 0 < S := hS.lt_of_ne fun h0 ↦ by simp [← h0] at hpos
  have hexp := mul_exp_neg_le_integral_regret_add_integral_regret h h' hνν' hD n
  have hle : Δ * n / (2 * S) ≤ exp (T * D) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : Δ * n * exp (-(T * D)) / 2 * exp (T * D) = Δ * n / 2 := by
      simp [div_mul_eq_mul_div, mul_assoc, ← exp_add]
    have h2 := mul_le_mul_of_nonneg_right hexp (exp_pos (T * D)).le
    linarith
  calc log (Δ * n / (2 * S)) ≤ log (exp (T * D)) := log_le_log hpos hle
    _ = T * D := log_exp _

end Runs

section Gaussian

variable {alg : Algorithm Unit α ℝ} {μ : α → ℝ} {σ2 : ℝ≥0} {C p ε : ℝ} {n : ℕ}

/-- **Lower bound on the number of pulls of a Gaussian arm at a finite horizon.** Let `alg` have
expected regret at most `C n ^ p` at horizon `n ≠ 0` on every Gaussian bandit with variance
`σ² ≠ 0` and means in `∏_a [μ_a, μ_a + 2 Δ_a]`, where `Δ_a` are the gaps of the Gaussian bandit
with means `μ`. Then for every suboptimal arm `i` and every `ε ∈ (0, 1]`, on the Gaussian bandit
with means `μ`,
`E[T_i(n)] ≥ 2 σ² ((1 - p) log n + log (ε Δ_i / (4 C))) / ((1 + ε)² Δ_i²)`. -/
theorem le_integral_pullCount_gaussianBandit [Finite α] [DecidableEq α] (hσ2 : σ2 ≠ 0)
    (hC : 0 < C) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : n ≠ 0)
    (hreg : ∀ μ' : α → ℝ, (∀ a, μ' a ∈ Set.Icc (μ a) (μ a + 2 * gap (gaussianBandit μ σ2) a)) →
      ∫ ω, regret (gaussianBandit μ' σ2) IT.action n ω
        ∂(trajMeasure alg (Environment.bandit (gaussianBandit μ' σ2))) ≤ C * n ^ p)
    {i : α} (hi : 0 < gap (gaussianBandit μ σ2) i) :
    2 * σ2 / ((1 + ε) ^ 2 * gap (gaussianBandit μ σ2) i ^ 2) *
        ((1 - p) * log n + log (ε * gap (gaussianBandit μ σ2) i / (4 * C))) ≤
      ∫ ω, (pullCount IT.action i n ω : ℝ)
        ∂(trajMeasure alg (Environment.bandit (gaussianBandit μ σ2))) := by
  set Δ := gap (gaussianBandit μ σ2) i with hΔ
  -- The alternative bandit moves the mean of the arm `i` to `μ_i + (1 + ε) Δ_i`.
  obtain ⟨μ', hμ'i, hμ'⟩ : ∃ μ' : α → ℝ, μ' i = μ i + (1 + ε) * Δ ∧ ∀ a ≠ i, μ' a = μ a :=
    ⟨Function.update μ i (μ i + (1 + ε) * Δ), Function.update_self .., fun a ha ↦
      Function.update_of_ne ha ..⟩
  set T := ∫ ω, (pullCount IT.action i n ω : ℝ)
    ∂(trajMeasure alg (Environment.bandit (gaussianBandit μ σ2)))
  have hsup : (⨆ a, (gaussianBandit μ σ2 a)[id]) = μ i + Δ := by
    have : Δ = (⨆ a, (gaussianBandit μ σ2 a)[id]) - μ i := by
      rw [hΔ, gap, integral_id_gaussianBandit]
    linarith
  have hν'i : (gaussianBandit μ' σ2 i)[id] = μ i + (1 + ε) * Δ := by
    rw [integral_id_gaussianBandit, hμ'i]
  have hνν' : ∀ a ≠ i, gaussianBandit μ σ2 a = gaussianBandit μ' σ2 a := fun a ha ↦ by
    rw [gaussianBandit_apply, gaussianBandit_apply, hμ' a ha]
  have hσ : (0 : ℝ) < σ2 := by positivity
  set D := ((1 + ε) * Δ) ^ 2 / (2 * σ2)
  have hD : klDiv (gaussianBandit μ σ2 i) (gaussianBandit μ' σ2 i) = ENNReal.ofReal D := by
    rw [klDiv_gaussianBandit _ _ hσ2, hμ'i]
    congr 2
    ring
  have hDpos : 0 < D := by positivity
  have hmin : min ((gaussianBandit μ' σ2 i)[id] - ⨆ a, (gaussianBandit μ σ2 a)[id]) Δ =
      ε * Δ := by
    rw [hν'i, hsup, show μ i + (1 + ε) * Δ - (μ i + Δ) = ε * Δ by ring]
    exact min_eq_left (mul_le_of_le_one_left hi.le hε1)
  -- The regrets on `ν` and on `ν'` are at most `C n ^ p`.
  have hR := hreg μ fun a ↦
    ⟨le_rfl, by linarith [gap_nonneg (ν := gaussianBandit μ σ2) (a := a)]⟩
  have hR' := hreg μ' fun a ↦ by
    by_cases ha : a = i
    · subst ha
      rw [hμ'i, ← hΔ]
      exact ⟨by nlinarith, by nlinarith⟩
    · rw [hμ' a ha]
      exact ⟨le_rfl, by linarith [gap_nonneg (ν := gaussianBandit μ σ2) (a := a)]⟩
  have hexp := mul_exp_neg_le_integral_regret_add_integral_regret
    (IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit (gaussianBandit μ σ2)))
    (IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit (gaussianBandit μ' σ2))) hνν'
    (hD ▸ ENNReal.ofReal_ne_top) n
  rw [hmin, hD, ENNReal.toReal_ofReal hDpos.le] at hexp
  -- Hence `ε Δ n exp (-T D) ≤ 4 C n ^ p`, and taking logarithms gives the bound on `T D`.
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnp : 0 < (n : ℝ) ^ p := rpow_pos_of_pos hn0 p
  have h1 : ε * Δ * n * exp (-(T * D)) ≤ 4 * C * n ^ p := by linarith
  have hlog := log_le_log (by positivity) h1
  rw [log_mul (by positivity) (exp_pos _).ne', log_mul (by positivity) hn0.ne', log_exp,
    log_mul (by positivity) hnp.ne', log_rpow hn0] at hlog
  have hTD : (1 - p) * log n + log (ε * Δ / (4 * C)) ≤ T * D := by
    rw [log_div (by positivity) (by positivity)]
    linarith
  calc 2 * σ2 / ((1 + ε) ^ 2 * Δ ^ 2) * ((1 - p) * log n + log (ε * Δ / (4 * C)))
      = ((1 - p) * log n + log (ε * Δ / (4 * C))) / D := by
        simp only [D]
        field_simp
    _ ≤ T := (div_le_iff₀ hDpos).mpr hTD

/-- **[LS, Theorem 16.4]** for Gaussian bandits with variance `σ²`. Let `alg` have expected regret
at most `C n ^ p` at horizon `n ≠ 0` on every Gaussian bandit with variance `σ²` and means in
`∏_a [μ_a, μ_a + 2 Δ_a]`, where `Δ_a` are the gaps of the Gaussian bandit with means `μ`. Then for
every `ε ∈ (0, 1]`, on the Gaussian bandit with means `μ`,
`E[R_n] ≥ 2 σ² / (1 + ε)² ∑_{a : Δ_a > 0} ((1 - p) log n + log (ε Δ_a / (4 C)))⁺ / Δ_a`.
[LS] has `8 C` where this statement has `4 C`. -/
theorem le_integral_regret_gaussianBandit [Fintype α] (hC : 0 < C) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hn : n ≠ 0)
    (hreg : ∀ μ' : α → ℝ, (∀ a, μ' a ∈ Set.Icc (μ a) (μ a + 2 * gap (gaussianBandit μ σ2) a)) →
      ∫ ω, regret (gaussianBandit μ' σ2) IT.action n ω
        ∂(trajMeasure alg (Environment.bandit (gaussianBandit μ' σ2))) ≤ C * n ^ p) :
    2 * σ2 / (1 + ε) ^ 2 * ∑ a ∈ univ.filter (fun a ↦ 0 < gap (gaussianBandit μ σ2) a),
        max 0 ((1 - p) * log n + log (ε * gap (gaussianBandit μ σ2) a / (4 * C))) /
          gap (gaussianBandit μ σ2) a ≤
      ∫ ω, regret (gaussianBandit μ σ2) IT.action n ω
        ∂(trajMeasure alg (Environment.bandit (gaussianBandit μ σ2))) := by
  classical
  set ν := gaussianBandit μ σ2
  set P := trajMeasure alg (Environment.bandit ν)
  have hT (a : α) : 0 ≤ ∫ ω, (pullCount IT.action a n ω : ℝ) ∂P :=
    integral_nonneg fun _ ↦ Nat.cast_nonneg _
  -- For `σ² = 0` the left-hand side vanishes.
  rcases eq_or_ne σ2 0 with hσ2 | hσ2
  · rw [hσ2, NNReal.coe_zero, mul_zero, zero_div, zero_mul]
    exact integral_nonneg fun _ ↦ regret_nonneg
  -- Otherwise, bound each term of the regret decomposition.
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount
    (IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν)).measurable_action, mul_sum]
  refine (sum_le_sum fun a ha ↦ ?_).trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    fun a _ _ ↦ mul_nonneg gap_nonneg (hT a))
  have hgap : 0 < gap ν a := (mem_filter.mp ha).2
  set X := (1 - p) * log n + log (ε * gap ν a / (4 * C))
  rcases le_total X 0 with hX | hX
  · rw [max_eq_left hX, zero_div, mul_zero]
    exact mul_nonneg gap_nonneg (hT a)
  rw [max_eq_right hX]
  calc 2 * σ2 / (1 + ε) ^ 2 * (X / gap ν a)
      = gap ν a * (2 * σ2 / ((1 + ε) ^ 2 * gap ν a ^ 2) * X) := by
        field_simp
    _ ≤ gap ν a * ∫ ω, (pullCount IT.action a n ω : ℝ) ∂P :=
        mul_le_mul_of_nonneg_left
          (le_integral_pullCount_gaussianBandit hσ2 hC hε0 hε1 hn hreg hgap) hgap.le

end Gaussian

end LMLExplore.Bandits
