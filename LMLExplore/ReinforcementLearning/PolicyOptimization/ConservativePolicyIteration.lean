/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.PerformanceDifference

import LMLExplore.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Conservative policy iteration

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP with rewards bounded by `C` and nonnegative mean rewards, let
`0 ≤ γ < 1` and let `μ` be the starting law. The **policy advantage** of a policy `π'` over a
stationary policy `π` [KL02, §4] is the mean advantage of the actions of `π'` along
the state occupancy measure `d^π_μ` of `π`:
`𝔸_π(π') = ∫ (∫ A^π (s, ·) dπ' s) dd^π_μ (s)`.
**Conservative policy iteration** (CPI) [KL02], [AJKS, §14.1] improves a stationary policy `π_t`
by a small step towards the output `π'_t` of a greedy oracle:
`π_{t+1} = (1 - α) π_t + α π'_t`. The step is small so that the occupancy measure barely moves:
by the policy-mixture lemma `Learning.MDP.tvDist_fst_occupancy_le_of_mixture`, `d^{π_{t+1}}_μ` is
within `2 α γ / (1 - γ)` of `d^{π_t}_μ` in total variation. Through the performance difference
lemma, this gives the **improvement lower bound** [AJKS, Theorem 14.2]
`∫ v^{π_{t+1}} dμ - ∫ v^{π_t} dμ ≥ α / (1 - γ) * (𝔸_t - 2 α γ C / (1 - γ) ^ 2)`
with `𝔸_t = 𝔸_{π_t}(π'_t)`.

For `1 / 5 ≤ γ`, the step `α = 𝔸_t (1 - γ) ^ 2 / (4 γ C)` lies in `[0, 1]` when `𝔸_t ≥ 0`, and
improves the value by at least `𝔸_t ^ 2 (1 - γ) / (8 γ C)` [AJKS, Theorem 14.3]. CPI stops at the
first `t` with `𝔸_t ≤ ε`. Since the values lie in `[0, C / (1 - γ)]`, it stops within
`8 γ C ^ 2 / (ε ^ 2 (1 - γ) ^ 2)` iterations. For rewards in `[0, 1]` (`C = 1`) this is
`8 γ / (ε ^ 2 (1 - γ) ^ 2)`; [AJKS, Theorem 14.3] prints `8 γ / ε ^ 2`, which drops the factor
`(1 - γ) ^ {-2}` coming from the range of the values.

At the stopping time, a policy class `Λ` approximates the greedy policies of `π` within `ε_Λ`
when some `π'' ∈ Λ` has `∫ (⨆ a, A^π (s, a)) dd^π_μ (s) ≤ 𝔸_π(π'') + ε_Λ`. If `π'` is
`ε`-greedy over `Λ` and `𝔸_π(π') ≤ ε`, then for every stationary policy `σ` whose state
occupancy measure is dominated by `D • μ` (that is, with mismatch coefficient
`‖d^σ_μ / μ‖_∞ ≤ D`),
`∫ v^σ dμ - ∫ v^π dμ ≤ D * (2 ε + ε_Λ) / (1 - γ) ^ 2` [AJKS, Theorem 14.4]. This follows from
the general bound `∫ v^σ dμ - ∫ v^π dμ ≤ D / (1 - γ) ^ 2 * ∫ (⨆ a, A^π (s, a)) dd^π_μ (s)`
on countable action sets,
`Learning.MDP.integral_value_sub_integral_value_le_mul_integral_iSup_advantage`.

## Main definitions

* `Learning.MDP.policyAdvantage M γ π π' μ`: the policy advantage `𝔸_π(π')` of `π'` over the
  stationary policy `π`, from the starting law `μ`.

## Main statements

* `Learning.MDP.policyAdvantage_of_mixture`: the policy advantage of the mixture
  `(1 - α) π + α π''` over `π` is `α 𝔸_π(π'')`.
* `Learning.MDP.mul_sub_le_integral_value_sub_integral_value_of_mixture`: the improvement lower
  bound of a mixture step [AJKS, Theorem 14.2];
  `Learning.MDP.policyAdvantage_sq_mul_div_le_integral_value_sub_integral_value`: its value for
  the step `α = 𝔸 (1 - γ) ^ 2 / (4 γ C)` [AJKS, Theorem 14.3].
* `LMLExplore.ReinforcementLearning.cpi_iterations_le`: CPI stops within
  `8 γ C ^ 2 / (ε ^ 2 (1 - γ) ^ 2)` iterations [AJKS, Theorem 14.3], corrected.
* `LMLExplore.ReinforcementLearning.integral_value_sub_integral_value_cpi_le`: the output of CPI
  is `D * (2 ε + ε_Λ) / (1 - γ) ^ 2`-optimal [AJKS, Theorem 14.4].

## References

* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], §14.1, Theorems 14.2–14.4
* [S. Kakade and J. Langford, *Approximately optimal approximate reinforcement learning*,
  ICML 2002][KL02], §§4–6
-/

public section

open MeasureTheory ProbabilityTheory Learning LMLExplore
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Nonempty 𝓢]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {C : ℝ} {μ : Measure 𝓢}

/-! ### The policy advantage -/

variable (M γ) in
/-- The **policy advantage** `𝔸_π(π') = ∫ (∫ A^π (s, ·) dπ' s) dd^π_μ (s)` of a policy `π'` over
the stationary policy `π` [KL02, §4]: the mean advantage over `π` of the actions of
`π'`, along the state occupancy measure `d^π_μ` of `π` from the starting law `μ`. -/
noncomputable def policyAdvantage (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] (π' : Kernel 𝓢 𝓐)
    (μ : Measure 𝓢) : ℝ :=
  ∫ s, ∫ a, M.advantage γ π (s, a) ∂(π' s) ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π) μ).fst

variable (M γ) in
lemma policyAdvantage_def (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] (π' : Kernel 𝓢 𝓐)
    (μ : Measure 𝓢) :
    M.policyAdvantage γ π π' μ =
      ∫ s, ∫ a, M.advantage γ π (s, a) ∂(π' s)
        ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π) μ).fst :=
  (rfl)

variable {π π' π'' : Kernel 𝓢 𝓐} [IsMarkovKernel π]

/-- With bounded rewards and `γ < 1`, a stationary policy has no advantage over itself. -/
theorem policyAdvantage_self (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    M.policyAdvantage γ π π μ = 0 := by
  simp [policyAdvantage_def, integral_advantage hγ hR]

/-- With mean rewards in `[0, C]` and `γ < 1`, the policy advantage is bounded by `C / (1 - γ)`.
-/
theorem abs_policyAdvantage_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hr : ∀ p, 0 ≤ meanReward M.R p) [IsMarkovKernel π'] :
    |M.policyAdvantage γ π π' μ| ≤ C / (1 - γ) := by
  have := isProbabilityMeasure_occupancy (M := M) (alg := Algorithm.markov fun _ ↦ π) (μ := μ) hγ
  exact abs_integral_le_of_abs_le (abs_integral_advantage_le hγ hR hr)

/-! ### The improvement of a mixture step -/

omit [Nonempty 𝓢] in
/-- Along the mixture `π' = (1 - α) π + α π''`, the mean advantage over `π` is `α` times the mean
advantage of the actions of `π''`, since the advantage of `π` has mean zero under `π`. -/
private lemma integral_advantage_of_mixture (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    [IsMarkovKernel π''] {α : ℝ≥0} (hπ' : ∀ s, π' s = (1 - α) • π s + α • π'' s) (s : 𝓢) :
    ∫ a, M.advantage γ π (s, a) ∂(π' s) = α * ∫ a, M.advantage γ π (s, a) ∂(π'' s) := by
  rw [hπ' s, integral_add_measure
    (integrable_advantage_prodMk_left hγ hR s _).smul_measure_nnreal
    (integrable_advantage_prodMk_left hγ hR s _).smul_measure_nnreal,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure, integral_advantage hγ hR s]
  simp [NNReal.smul_def]

/-- **The policy advantage of a mixture**: with bounded rewards and `γ < 1`, the mixture
`π' = (1 - α) π + α π''` has policy advantage `𝔸_π(π') = α 𝔸_π(π'')` over `π`. -/
theorem policyAdvantage_of_mixture (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    [IsMarkovKernel π''] {α : ℝ≥0} (hπ' : ∀ s, π' s = (1 - α) • π s + α • π'' s) :
    M.policyAdvantage γ π π' μ = α * M.policyAdvantage γ π π'' μ := by
  simp_rw [policyAdvantage_def, integral_advantage_of_mixture hγ hR hπ']
  exact integral_const_mul _ _

/-- **The improvement lower bound of a mixture step** [AJKS, Theorem 14.2]: with mean rewards in
`[0, C]`, `γ < 1` and `α ≤ 1`, the mixture `π' = (1 - α) π + α π''` of the stationary policies
`π` and `π''` improves the value from the probability measure `μ` by at least
`α / (1 - γ) * (𝔸_π(π'') - 2 α γ C / (1 - γ) ^ 2)`. -/
theorem mul_sub_le_integral_value_sub_integral_value_of_mixture (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hr : ∀ p, 0 ≤ meanReward M.R p) [IsProbabilityMeasure μ]
    [IsMarkovKernel π'] [IsMarkovKernel π''] {α : ℝ≥0} (hα : α ≤ 1)
    (hπ' : ∀ s, π' s = (1 - α) • π s + α • π'' s) :
    α / (1 - γ) * (M.policyAdvantage γ π π'' μ - 2 * α * γ * C / (1 - γ) ^ 2) ≤
      ∫ s, M.value γ π' s ∂μ - ∫ s, M.value γ π s ∂μ := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  set d' := (M.occupancy γ (Algorithm.markov fun _ ↦ π') μ).fst
  set d := (M.occupancy γ (Algorithm.markov fun _ ↦ π) μ).fst
  set f : 𝓢 → ℝ := fun s ↦ ∫ a, M.advantage γ π (s, a) ∂(π'' s)
  have := isProbabilityMeasure_occupancy (M := M) (alg := Algorithm.markov fun _ ↦ π') (μ := μ) hγ
  have := isProbabilityMeasure_occupancy (M := M) (alg := Algorithm.markov fun _ ↦ π) (μ := μ) hγ
  have hf : Measurable f := measurable_integral_advantage hγ hR π''
  have hfB (s : 𝓢) : ‖f s‖ ≤ C / (1 - γ) := abs_integral_advantage_le hγ hR hr s
  have hB : 0 ≤ C / (1 - γ) := (norm_nonneg _).trans (hfB (Classical.arbitrary 𝓢))
  -- the performance difference lemma, with the advantages of the mixture rewritten through `π''`
  rw [integral_value_sub_integral_value hγ hR π π']
  simp_rw [integral_advantage_of_mixture hγ hR hπ']
  rw [integral_const_mul]
  -- the occupancy measures of `π'` and `π` are within `2 α γ / (1 - γ)` in total variation
  have h_tv : ‖∫ s, f s ∂d' - ∫ s, f s ∂d‖ ≤ C / (1 - γ) * (2 * α * γ / (1 - γ)) :=
    (norm_integral_sub_integral_le_mul_tvDist hf.aestronglyMeasurable hf.aestronglyMeasurable
      (.of_forall hfB) (.of_forall hfB)).trans
      (mul_le_mul_of_nonneg_left (tvDist_fst_occupancy_le_of_mixture hγ hα hπ') hB)
  have h_key : M.policyAdvantage γ π π'' μ - 2 * α * γ * C / (1 - γ) ^ 2 ≤ ∫ s, f s ∂d' := by
    have h_eq : C / (1 - γ) * (2 * α * γ / (1 - γ)) = 2 * α * γ * C / (1 - γ) ^ 2 := by
      field_simp
    rw [policyAdvantage_def, ← h_eq]
    linarith [neg_abs_le (∫ s, f s ∂d' - ∫ s, f s ∂d), (Real.norm_eq_abs _).symm.trans_le h_tv]
  calc α / (1 - γ) * (M.policyAdvantage γ π π'' μ - 2 * α * γ * C / (1 - γ) ^ 2)
      ≤ α / (1 - γ) * ∫ s, f s ∂d' :=
        mul_le_mul_of_nonneg_left h_key (div_nonneg α.coe_nonneg h1γ.le)
    _ = (1 - γ : ℝ)⁻¹ * (α * ∫ s, f s ∂d') := by ring

/-- **The improvement of the conservative step** [AJKS, Theorem 14.3]: with mean rewards in
`[0, C]` and `1 / 5 ≤ γ < 1`, let `𝔸 = 𝔸_π(π'')`. If the step `α = 𝔸 (1 - γ) ^ 2 / (4 γ C)` is
nonnegative, then the mixture `π' = (1 - α) π + α π''` improves the value from the probability
measure `μ` by at least `𝔸 ^ 2 (1 - γ) / (8 γ C)`. The proof applies Theorem 14.2, as the step is
then automatically at most `1`. -/
theorem policyAdvantage_sq_mul_div_le_integral_value_sub_integral_value (hγ₀ : 1 / 5 ≤ γ)
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hr : ∀ p, 0 ≤ meanReward M.R p)
    [IsProbabilityMeasure μ] [IsMarkovKernel π'] [IsMarkovKernel π''] {α : ℝ≥0}
    (hα : (α : ℝ) = M.policyAdvantage γ π π'' μ * (1 - γ) ^ 2 / (4 * γ * C))
    (hπ' : ∀ s, π' s = (1 - α) • π s + α • π'' s) :
    M.policyAdvantage γ π π'' μ ^ 2 * (1 - γ) / (8 * γ * C) ≤
      ∫ s, M.value γ π' s ∂μ - ∫ s, M.value γ π s ∂μ := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hγ₀' : (1 / 5 : ℝ) ≤ γ := by exact_mod_cast hγ₀
  have hγpos : (0 : ℝ) < γ := by linarith
  have hAabs := abs_policyAdvantage_le (μ := μ) (π := π) (π' := π'') hγ hR hr
  have hC : 0 ≤ C := by simpa using (le_div_iff₀ h1γ).1 ((abs_nonneg _).trans hAabs)
  rcases hC.eq_or_lt with rfl | hC
  · -- with `C = 0` the bound is `0`, and the step is `α = 0`
    have hα0 : α = 0 := by
      rw [← NNReal.coe_eq_zero, hα]
      simp
    have h := mul_sub_le_integral_value_sub_integral_value_of_mixture hγ hR hr (μ := μ)
      (zero_le_one' _) (hα0 ▸ hπ')
    simpa using h
  -- the step lies in `[0, 1]` because `𝔸 ≤ C / (1 - γ)` and `1 - γ ≤ 4 γ`
  have hα1 : α ≤ 1 := by
    rw [← NNReal.coe_le_coe, hα, NNReal.coe_one, div_le_one (by positivity)]
    calc M.policyAdvantage γ π π'' μ * (1 - γ) ^ 2 ≤ C / (1 - γ) * (1 - γ) ^ 2 := by
          gcongr
          exact le_of_abs_le hAabs
      _ = C * (1 - γ) := by field_simp
      _ ≤ 4 * γ * C := by nlinarith
  refine le_trans (le_of_eq ?_)
    (mul_sub_le_integral_value_sub_integral_value_of_mixture hγ hR hr hα1 hπ')
  rw [hα]
  field_simp
  ring

end Learning.MDP

namespace LMLExplore.ReinforcementLearning

open Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Nonempty 𝓢]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {C : ℝ} {μ : Measure 𝓢} [IsProbabilityMeasure μ]

/-- **Conservative policy iteration stops** [AJKS, Theorem 14.3], corrected: with mean rewards in
`[0, C]`, `1 / 5 ≤ γ < 1` and `ε > 0`, let the stationary policies `π_t` follow the CPI update
`π_{t+1} = (1 - α_t) π_t + α_t π'_t`, with the step `α_t = 𝔸_t (1 - γ) ^ 2 / (4 γ C)` and the
policy advantage `𝔸_t = 𝔸_{π_t}(π'_t)` from the starting law `μ`. If CPI has not stopped before
round `T`, that is `ε < 𝔸_t` for every `t < T`, then `T ≤ 8 γ C ^ 2 / (ε ^ 2 (1 - γ) ^ 2)`.
For `C = 1`, the source prints the bound `8 γ / ε ^ 2`. -/
theorem cpi_iterations_le (hγ₀ : 1 / 5 ≤ γ) (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hr : ∀ p, 0 ≤ meanReward M.R p) {π π' : ℕ → Kernel 𝓢 𝓐} [∀ t, IsMarkovKernel (π t)]
    [∀ t, IsMarkovKernel (π' t)] {α : ℕ → ℝ≥0} {ε : ℝ} (hε : 0 < ε) {T : ℕ}
    (hπ : ∀ t < T, ∀ s, π (t + 1) s = (1 - α t) • π t s + α t • π' t s)
    (hα : ∀ t < T,
      (α t : ℝ) = M.policyAdvantage γ (π t) (π' t) μ * (1 - γ) ^ 2 / (4 * γ * C))
    (hA : ∀ t < T, ε < M.policyAdvantage γ (π t) (π' t) μ) :
    (T : ℝ) ≤ 8 * γ * C ^ 2 / (ε ^ 2 * (1 - γ) ^ 2) := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hγpos : (0 : ℝ) < γ := by
    have : (1 / 5 : ℝ) ≤ γ := by exact_mod_cast hγ₀
    linarith
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp only [CharP.cast_eq_zero]
    positivity
  -- the policy advantage of the first round is positive and at most `C / (1 - γ)`, so `C > 0`
  have hC : 0 < C := by
    have h := (hε.trans (hA 0 hT)).trans_le
      (le_of_abs_le (abs_policyAdvantage_le (μ := μ) (π := π 0) (π' := π' 0) hγ hR hr))
    exact (div_pos_iff_of_pos_right h1γ).1 h
  -- each round improves the value by at least `c = ε ^ 2 (1 - γ) / (8 γ C)`
  set c := ε ^ 2 * (1 - γ) / (8 * γ * C)
  have h_step (t : ℕ) (ht : t < T) :
      c ≤ ∫ s, M.value γ (π (t + 1)) s ∂μ - ∫ s, M.value γ (π t) s ∂μ := by
    refine le_trans ?_ (policyAdvantage_sq_mul_div_le_integral_value_sub_integral_value hγ₀ hγ hR
      hr (hα t ht) (hπ t ht))
    have := hA t ht
    unfold c
    gcongr
  have h_sum (n : ℕ) (hn : n ≤ T) :
      n * c ≤ ∫ s, M.value γ (π n) s ∂μ - ∫ s, M.value γ (π 0) s ∂μ := by
    induction n with
    | zero => simp
    | succ n ih =>
      have := ih (by omega)
      have := h_step n (by omega)
      push_cast
      linarith
  -- the values lie in `[0, C / (1 - γ)]`
  have h_top : ∫ s, M.value γ (π T) s ∂μ ≤ C / (1 - γ) :=
    le_of_abs_le (abs_integral_le_of_abs_le (abs_value_le hγ hR))
  have h_bot : 0 ≤ ∫ s, M.value γ (π 0) s ∂μ := integral_nonneg (value_nonneg hγ hR hr)
  have h := (h_sum T le_rfl).trans (by linarith : _ ≤ C / (1 - γ))
  unfold c at h
  rw [le_div_iff₀ (by positivity)]
  calc (T : ℝ) * (ε ^ 2 * (1 - γ) ^ 2)
      = T * (ε ^ 2 * (1 - γ) / (8 * γ * C)) * (8 * γ * C * (1 - γ)) := by field_simp
    _ ≤ C / (1 - γ) * (8 * γ * C * (1 - γ)) := by gcongr
    _ = 8 * γ * C ^ 2 := by field_simp

/-- **The output of conservative policy iteration is near-optimal** [AJKS, Theorem 14.4]: on a
countable action set, with bounded rewards and `γ < 1`, let `π` be the stationary policy at
which CPI stops, with the oracle output `π'`, and let `Λ` be the policy class of the oracle.
Assume that
* `π'` is `ε`-greedy over `Λ`: `𝔸_π(π'') ≤ 𝔸_π(π') + ε` for every `π'' ∈ Λ`;
* CPI stops at `π`: `𝔸_π(π') ≤ ε`;
* `Λ` approximates the greedy policies of `π` within `ε_Λ`: some `π'' ∈ Λ` has
  `∫ (⨆ a, A^π (s, a)) dd^π_μ (s) ≤ 𝔸_π(π'') + ε_Λ`.

Then every stationary policy `σ` with `d^σ_μ ≤ D • μ` has
`∫ v^σ dμ - ∫ v^π dμ ≤ D * (2 ε + ε_Λ) / (1 - γ) ^ 2`. -/
theorem integral_value_sub_integral_value_cpi_le [Countable 𝓐] [Nonempty 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {π π' : Kernel 𝓢 𝓐} [IsMarkovKernel π]
    {Λ : Set (Kernel 𝓢 𝓐)} {ε εΛ : ℝ}
    (hgreedy : ∀ π'' ∈ Λ, M.policyAdvantage γ π π'' μ ≤ M.policyAdvantage γ π π' μ + ε)
    (hstop : M.policyAdvantage γ π π' μ ≤ ε)
    (happrox : ∃ π'' ∈ Λ, ∫ s, ⨆ a, M.advantage γ π (s, a)
      ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π) μ).fst ≤ M.policyAdvantage γ π π'' μ + εΛ)
    (σ : Kernel 𝓢 𝓐) [IsMarkovKernel σ] {D : ℝ≥0}
    (hD : (M.occupancy γ (Algorithm.markov fun _ ↦ σ) μ).fst ≤ D • μ) :
    ∫ s, M.value γ σ s ∂μ - ∫ s, M.value γ π s ∂μ ≤ D * (2 * ε + εΛ) / (1 - γ) ^ 2 := by
  obtain ⟨π'', hπ'', h⟩ := happrox
  have h_greedy : ∫ s, ⨆ a, M.advantage γ π (s, a)
      ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π) μ).fst ≤ 2 * ε + εΛ := by
    linarith [hgreedy π'' hπ'']
  refine (integral_value_sub_integral_value_le_mul_integral_iSup_advantage hγ hR σ hD).trans ?_
  rw [mul_div_right_comm]
  gcongr

end LMLExplore.ReinforcementLearning
