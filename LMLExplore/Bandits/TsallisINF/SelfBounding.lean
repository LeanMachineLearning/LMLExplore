/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.TsallisINF.PseudoRegret
public import LMLExplore.NumberTheory.Harmonic.Bounds

/-!
# Tsallis-INF in the adversarial regime with a self-bounding constraint

Tsallis-INF (`LMLExplore.Bandits.tsallisINF`) has pseudo-regret of order `√(k n)` against every
adaptive adversary (`LMLExplore.Bandits.TsallisINF.pseudoRegret_le_sqrt`). This file proves that
the same algorithm, with no change of its learning rates, has logarithmic pseudo-regret in the
adversarial regime with a self-bounding constraint, which contains the stochastic bandits with a
unique optimal arm [ZS21], [Ora, Section 9.3]: it adapts to the regime without knowing it.

The finer analysis keeps the penalties of the changes of learning rate at the weights of their
rounds (`OnlineLearning.tsallisWeights_regret_succ_le_sum_sub_mul`). With `P t` the weights of
round `t`, every round contributes at most `12 / √(t + 1) * ∑ b ≠ a', E[√(P t b)]` to the
pseudo-regret, for every arm `a'`. If the pseudo-regret dominates the expected gaps of the plays,
`∑ t < n, ∑ b ≠ a', Δ b E[P t b] ≤ R_n` for gaps `Δ b > 0` (the adversarial regime with a
self-bounding constraint of [ZS21] with corruption `C = 0`), then
`R_n ≤ 2 R_n - ∑ t < n, ∑ b ≠ a', Δ b E[P t b]`, and each term
`24 / √(t + 1) * E[√(P t b)] - Δ b E[P t b]` is at most `144 / ((t + 1) Δ b)`. Summing,
`R_n ≤ 144 (1 + log n) ∑ b ≠ a', 1 / Δ b`.

Against a stochastic bandit `Environment.bandit ν`, the pseudo-regret is the expected regret, which
is exactly `∑ t < n, ∑ b, gap ν b E[P t b]` (`WeightAlgorithm.integral_regret_eq`), so the
constraint holds for the gaps of `ν` whenever the optimal arm `a'` is unique.

## Main statements

* `TsallisINF.pseudoRegret_le_sum_integral_sum_sqrt`: against every environment with feedbacks in
  `[0, 1]` and for every arm `a'`,
  `R_n ≤ ∑ t < n, 12 / √(t + 1) * ∑ b ≠ a', E[√(P t b)]`.
* `TsallisINF.pseudoRegret_le_log_of_selfBounding`: under the self-bounding constraint with gaps
  `Δ b > 0` for `b ≠ a'`, `R_n ≤ 144 (1 + log n) ∑ b ≠ a', 1 / Δ b`.
* `TsallisINF.integral_regret_le_log`: against a stochastic bandit with rewards in `[0, 1]` and a
  unique optimal arm `a'`, the expected regret is at most
  `144 (1 + log n) ∑ b ≠ a', 1 / gap ν b`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
* [ZS21] J. Zimmert and Y. Seldin, *Tsallis-INF: an optimal algorithm for stochastic and
  adversarial bandits*, JMLR 22 (2021).
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real

namespace LMLExplore.Bandits

variable {α 𝓞 Ω : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [MeasurableSpace 𝓞]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {env : Environment 𝓞 α ℝ} {n : ℕ}

namespace TsallisINF

/-- Along a run of Tsallis-INF, the square root of the weight of an arm at round `t` is
integrable. -/
private lemma integrable_sqrt_tsallisINFWeights (h : IsAlgEnvSeq O A Y tsallisINF env P) (t : ℕ)
    (b : α) : Integrable (fun ω ↦ √(tsallisINFWeights t (history O A Y t ω) b)) P :=
  WeightAlgorithm.integrable_comp_weights_of_bound (isAlgEnvSeq_tsallisINF_iff.1 h) t
    (measurable_pi_apply b).sqrt (C := 1) fun p hp ↦ by
      rw [abs_of_nonneg (sqrt_nonneg _)]
      exact sqrt_le_one.2 ((simplex_subset_Icc hp).2 b)

/-- **Pseudo-regret of Tsallis-INF in terms of the weights of the other arms** [ZS21],
[Ora, Section 9.3]. Along a run of Tsallis-INF against any environment whose feedbacks of the
rounds `t < n` are almost surely in `[0, 1]`, with `P t` the weights of round `t`, the
pseudo-regret after `n` rounds satisfies, for every arm `a'`,
`R_n ≤ ∑ t < n, 12 / √(t + 1) * ∑ b ≠ a', E[√(P t b)]`. -/
theorem pseudoRegret_le_sum_integral_sum_sqrt (h : IsAlgEnvSeq O A Y tsallisINF env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) (a' : α) :
    pseudoRegret env O A Y P n ≤ ∑ t ∈ range n, 12 / √((t : ℝ) + 1) *
      ∑ b ∈ univ.erase a', P[fun ω ↦ √(tsallisINFWeights t (history O A Y t ω) b)] := by
  refine pseudoRegret_le_iff.2 fun a ↦ ?_
  have hYt (t : ℕ) (ht : t ∈ range n) : ∀ᵐ ω ∂P, Y t ω ∈ Set.Icc 0 1 :=
    hY.mono fun _ hω ↦ hω t (mem_range.1 ht)
  have hVint (t : ℕ) (ht : t ∈ range n) := integrable_sum_mul_sqrt_mul_sq (t := t) h (hYt t ht)
  have hS (t : ℕ) : Integrable (fun ω ↦ ∑ b ∈ univ.erase a',
      √(tsallisINFWeights t (history O A Y t ω) b)) P :=
    integrable_finsetSum _ fun b _ ↦ integrable_sqrt_tsallisINFWeights h t b
  have hI (t : ℕ) (ht : t ∈ range n) : Integrable (fun ω ↦ 4 / √((t : ℝ) + 1) *
      (∑ b ∈ univ.erase a', √(tsallisINFWeights t (history O A Y t ω) b) +
        ∑ b, tsallisINFWeights t (history O A Y t ω) b *
          √(tsallisINFWeights t (history O A Y t ω) b) *
          (iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b -
            (1 - Y t ω)) ^ 2)) P :=
    ((hS t).add (hVint t ht)).const_mul _
  rw [WeightAlgorithm.integral_sum_means_sub_eq_integral_sum_one_sub_sub_iwEstimator
    (isAlgEnvSeq_tsallisINF_iff.1 h) (fun t ht ↦ hYt t (mem_range.2 ht))
    fun t _ ↦ ae_of_all _ fun ω ↦ tsallisINFWeights_pos _ _ a]
  calc P[fun ω ↦ ∑ t ∈ range n, ((1 - Y t ω) -
        iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) a)]
  -- take expectations in the pathwise bound
  _ ≤ P[fun ω ↦ ∑ t ∈ range n, 4 / √((t : ℝ) + 1) *
        (∑ b ∈ univ.erase a', √(tsallisINFWeights t (history O A Y t ω) b) +
          ∑ b, tsallisINFWeights t (history O A Y t ω) b *
            √(tsallisINFWeights t (history O A Y t ω) b) *
            (iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b -
              (1 - Y t ω)) ^ 2)] := by
      refine integral_mono_ae (integrable_finsetSum _ fun t ht ↦
          integrable_one_sub_sub_iwEstimator h (hYt t ht) a) (integrable_finsetSum _ hI) ?_
      filter_upwards [hY] with ω hω using sum_one_sub_sub_iwEstimator_le_sum_sqrt O A Y ω hω a a'
  _ = ∑ t ∈ range n, 4 / √((t : ℝ) + 1) *
        (P[fun ω ↦ ∑ b ∈ univ.erase a', √(tsallisINFWeights t (history O A Y t ω) b)] +
          P[fun ω ↦ ∑ b, tsallisINFWeights t (history O A Y t ω) b *
            √(tsallisINFWeights t (history O A Y t ω) b) *
            (iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) b -
              (1 - Y t ω)) ^ 2]) := by
      rw [integral_finsetSum _ hI]
      refine sum_congr rfl fun t ht ↦ ?_
      rw [integral_const_mul, integral_add (hS t) (hVint t ht)]
  -- the expected local norm of a round is at most `2 E[∑ b ≠ a', √(P t b)]`
  _ ≤ ∑ t ∈ range n, 4 / √((t : ℝ) + 1) *
        (P[fun ω ↦ ∑ b ∈ univ.erase a', √(tsallisINFWeights t (history O A Y t ω) b)] +
          2 * P[fun ω ↦ ∑ b ∈ univ.erase a', √(tsallisINFWeights t (history O A Y t ω) b)]) := by
      gcongr with t ht
      refine (integral_sum_mul_sqrt_mul_sq_le_integral_sum_sqrt_mul_one_sub h (hYt t ht)).trans ?_
      rw [← integral_const_mul]
      refine integral_mono ?_ ((hS t).const_mul 2) fun ω ↦
        sum_sqrt_mul_one_sub_le_two_mul_sum_erase (tsallisINFWeights_mem_simplex _ _) a'
      refine WeightAlgorithm.integrable_comp_weights_of_bound (isAlgEnvSeq_tsallisINF_iff.1 h) t
        (g := fun p ↦ ∑ b, √(p b) * (1 - p b))
        (Finset.measurable_sum _ fun b _ ↦ (measurable_pi_apply b).sqrt.mul
          (measurable_const.sub (measurable_pi_apply b))) (C := √((Fintype.card α : ℝ) - 1))
        fun p hp ↦ (abs_of_nonneg (sum_nonneg fun b _ ↦ mul_nonneg (sqrt_nonneg _)
          (sub_nonneg.2 ((simplex_subset_Icc hp).2 b)))).trans_le (sum_sqrt_mul_one_sub_le_sqrt hp)
  _ = ∑ t ∈ range n, 12 / √((t : ℝ) + 1) *
        ∑ b ∈ univ.erase a', P[fun ω ↦ √(tsallisINFWeights t (history O A Y t ω) b)] := by
      refine sum_congr rfl fun t _ ↦ ?_
      rw [integral_finsetSum _ fun b _ ↦ integrable_sqrt_tsallisINFWeights h t b]
      ring

/-- **Logarithmic pseudo-regret of Tsallis-INF under a self-bounding constraint** [ZS21],
[Ora, Section 9.3]. Along a run of Tsallis-INF against any environment whose
feedbacks of the rounds `t < n` are almost surely in `[0, 1]`, with `P t` the weights of
round `t`, let an arm `a'` and gaps `Δ b > 0` of the arms `b ≠ a'` satisfy the self-bounding
constraint `∑ t < n, ∑ b ≠ a', Δ b E[P t b] ≤ R_n`. Then the pseudo-regret after `n` rounds is
`R_n ≤ 144 (1 + log n) ∑ b ≠ a', 1 / Δ b`. -/
theorem pseudoRegret_le_log_of_selfBounding (h : IsAlgEnvSeq O A Y tsallisINF env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) {a' : α} {Δ : α → ℝ}
    (hΔ : ∀ b ≠ a', 0 < Δ b)
    (hR : ∑ t ∈ range n, ∑ b ∈ univ.erase a',
      Δ b * P[fun ω ↦ tsallisINFWeights t (history O A Y t ω) b] ≤ pseudoRegret env O A Y P n) :
    pseudoRegret env O A Y P n ≤ 144 * (1 + log n) * ∑ b ∈ univ.erase a', (Δ b)⁻¹ := by
  have hU := pseudoRegret_le_sum_integral_sum_sqrt h hY a'
  -- the contribution of the arm `b ≠ a'` at round `t` is at most `144 / ((t + 1) Δ b)`
  have h_term (t : ℕ) (b : α) (hb : b ∈ univ.erase a') :
      24 / √((t : ℝ) + 1) * P[fun ω ↦ √(tsallisINFWeights t (history O A Y t ω) b)] -
        Δ b * P[fun ω ↦ tsallisINFWeights t (history O A Y t ω) b] ≤
        144 * ((Δ b)⁻¹ * ((t : ℝ) + 1)⁻¹) := by
    have hΔb := hΔ b (ne_of_mem_erase hb)
    have hS := integrable_sqrt_tsallisINFWeights h t b
    have hP := WeightAlgorithm.integrable_weights_apply (isAlgEnvSeq_tsallisINF_iff.1 h) t b
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hS.const_mul _)
      (hP.const_mul _)]
    refine (integral_mono ((hS.const_mul _).sub (hP.const_mul _))
      (integrable_const (144 * ((Δ b)⁻¹ * ((t : ℝ) + 1)⁻¹))) fun ω ↦ ?_).trans_eq (by simp)
    -- pointwise, `2 √p q ≤ Δ p + Δ⁻¹ q ^ 2` with `q = 12 / √(t + 1)`
    have hW := (simplex_subset_Icc (tsallisINFWeights_mem_simplex t (history O A Y t ω))).1 b
    have hq := two_mul_le_add_mul_sq (a := √(tsallisINFWeights t (history O A Y t ω) b))
      (b := 12 / √((t : ℝ) + 1)) hΔb
    rw [sq_sqrt hW, div_pow, sq_sqrt (by positivity)] at hq
    simp only [Pi.sub_apply]
    linear_combination hq
  calc pseudoRegret env O A Y P n
  _ ≤ 2 * ∑ t ∈ range n, 12 / √((t : ℝ) + 1) *
        ∑ b ∈ univ.erase a', P[fun ω ↦ √(tsallisINFWeights t (history O A Y t ω) b)] -
      ∑ t ∈ range n, ∑ b ∈ univ.erase a',
        Δ b * P[fun ω ↦ tsallisINFWeights t (history O A Y t ω) b] := by linarith
  _ = ∑ t ∈ range n, ∑ b ∈ univ.erase a',
        (24 / √((t : ℝ) + 1) * P[fun ω ↦ √(tsallisINFWeights t (history O A Y t ω) b)] -
          Δ b * P[fun ω ↦ tsallisINFWeights t (history O A Y t ω) b]) := by
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun t _ ↦ ?_
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun b _ ↦ by ring
  _ ≤ ∑ t ∈ range n, ∑ b ∈ univ.erase a', 144 * ((Δ b)⁻¹ * ((t : ℝ) + 1)⁻¹) :=
      sum_le_sum fun t _ ↦ sum_le_sum fun b hb ↦ h_term t b hb
  _ = 144 * (∑ t ∈ range n, ((t : ℝ) + 1)⁻¹) * ∑ b ∈ univ.erase a', (Δ b)⁻¹ := by
      rw [sum_comm]
      simp only [mul_sum, sum_mul]
      exact sum_congr rfl fun b _ ↦ sum_congr rfl fun t _ ↦ by ring
  _ ≤ 144 * (1 + log n) * ∑ b ∈ univ.erase a', (Δ b)⁻¹ := by
      have hΔ0 : 0 ≤ ∑ b ∈ univ.erase a', (Δ b)⁻¹ :=
        sum_nonneg fun b hb ↦ (inv_pos.2 (hΔ b (ne_of_mem_erase hb))).le
      gcongr
      exact Real.sum_range_inv_add_one_le n

/-- **Logarithmic regret of Tsallis-INF in stochastic bandits** [ZS21],
[Ora, Section 9.3]. Along a run of Tsallis-INF against a stochastic bandit
`Environment.bandit ν` whose rewards are almost surely in `[0, 1]`, with a unique optimal arm
`a'` (every other arm has a positive gap), the expected regret after `n` rounds is at most
`144 (1 + log n) ∑ b ≠ a', 1 / gap ν b`. The algorithm is the one of the adversarial bound
`pseudoRegret_le_sqrt`: it does not know whether the environment is stochastic. -/
theorem integral_regret_le_log {ν : Kernel α ℝ} [IsMarkovKernel ν] {O : ℕ → Ω → Unit}
    (h : IsAlgEnvSeq O A Y tsallisINF (Environment.bandit ν) P)
    (hν : ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc (0 : ℝ) 1) {a' : α}
    (hgap : ∀ b ≠ a', 0 < _root_.Bandits.gap ν b) (n : ℕ) :
    P[_root_.Bandits.regret ν A n] ≤
      144 * (1 + log n) * ∑ b ∈ univ.erase a', (_root_.Bandits.gap ν b)⁻¹ := by
  have hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1 :=
    (h.ae_forall_feedback_mem_bandit measurableSet_Icc hν).mono fun ω hω t _ ↦ hω t
  have hνi (a : α) : Integrable id (ν a) :=
    Integrable.of_mem_Icc 0 1 measurable_id.aemeasurable (hν a)
  rw [← h.pseudoRegret_bandit hνi n]
  refine pseudoRegret_le_log_of_selfBounding h hY hgap ?_
  -- the expected regret is the sum of the expected gaps under the weights, and `gap ν a' ≥ 0`
  rw [h.pseudoRegret_bandit hνi n, WeightAlgorithm.integral_regret_eq
    (isAlgEnvSeq_tsallisINF_iff.1 h) ν n]
  refine sum_le_sum fun t _ ↦ sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun b _ _ ↦
    mul_nonneg _root_.Bandits.gap_nonneg
      (integral_nonneg fun ω ↦ (tsallisINFWeights_pos _ _ _).le)

end TsallisINF

end LMLExplore.Bandits
