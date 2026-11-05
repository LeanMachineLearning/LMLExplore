/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Episodic.Optimal
public import LMLExplore.MarkovDecisionProcess.Episodic.PerformanceDifference
import Mathlib.Analysis.Convex.Integral

/-!
# The pessimistic decomposition in an episodic MDP

Let `M : EpisodicMDP 𝓢 𝓐` be an episodic MDP with a horizon `H`, and let `Q̂_h` and `V̂_h` be
estimates of the action values and of the values, computed by backward induction from
`V̂_H = 0`, together with the Markov policy `π̂` they induce: `V̂_h s = ∫ Q̂_h (s, a) dπ̂_h(a | s)`.
The *model evaluation error* of the estimates at the step `h` is

`ι_h (s, a) = r_h (s, a) + ∫ V̂_{h+1} dP_h (s, a) - Q̂_h (s, a)`,

the amount by which `Q̂_h` underestimates the Bellman backup of `V̂_{h+1}`. This file bounds the
suboptimality of `π̂` with respect to an arbitrary comparator Markov policy `π`. The expectations
along the episodes of a policy `π` started from a law `μ` are the integrals against its state
marginals `μ_h` and its occupancy measures `d^π_h`.

* **Decomposition of suboptimality** [JYW21, Lemma 3.1]: the suboptimality
  `∫ V^π_0 dμ - ∫ V^π̂_0 dμ` is the sum of an optimization error
  `∑_h ∫ (∫ Q̂_h (s, ·) dπ_h s - V̂_h s) dμ_h`, of the evaluation errors along `π`,
  `∑_h ∫ ι_h dd^π_h`, and of minus the evaluation errors along `π̂`, `-∑_h ∫ ι_h dd^π̂_h`.
* **Pessimism.** If `π̂` is greedy for `Q̂` (`Q̂_h (s, a) ≤ V̂_h s`), the optimization error is
  nonpositive, and if the estimates are pessimistic (`ι_h ≥ 0`), so is the last sum: the
  suboptimality is at most `∑_h ∫ ι_h dd^π_h`, an error along the comparator only.
* **Pessimistic value iteration** [JYW21, Algorithm 1, Lemma 5.1, Theorem 4.2]. Let rewards lie
  in `[0, 1]`, and let `Q̂_h = min (T̂_h - Γ_h, H - h)⁺` for estimates `T̂_h` of the backups
  `r_h + P_h V̂_{h+1}` and penalties `Γ_h`. If the penalties dominate the estimation errors,
  `|T̂_h - (r_h + P_h V̂_{h+1})| ≤ Γ_h`, then `0 ≤ ι_h ≤ 2 Γ_h`, hence
  `∫ V^π_0 dμ - ∫ V^π̂_0 dμ ≤ 2 ∑_h ∫ Γ_h dd^π_h` for every Markov policy `π`; for the optimal
  policy `π*`, this is `∫ V*_0 dμ - ∫ V^π̂_0 dμ ≤ 2 ∑_h ∫ Γ_h dd^{π*}_h`.

The bound of pessimistic value iteration is deterministic: in offline reinforcement learning, the
backups `T̂_h` and the penalties `Γ_h` are computed from a dataset, and the bound holds on the event
where the penalties dominate the estimation errors. [JYW21] state the decomposition and the bound
for the optimal policy and an initial state `x`; here the comparator is an arbitrary Markov policy,
the initial state has an arbitrary law `μ` (a Dirac mass for [JYW21]), the state and action spaces
are general measurable spaces, and the estimates are only assumed measurable (and bounded, for the
decomposition).

## Main statements

* `Learning.MDP.Episodic.EpisodicMDP.integral_value_sub_integral_value_eq_sum_add_sum_sub_sum`:
  the decomposition of suboptimality [JYW21, Lemma 3.1].
* `Learning.MDP.Episodic.EpisodicMDP.integral_value_sub_integral_value_le_sum`: the
  suboptimality of a greedy policy for pessimistic estimates is at most the evaluation errors
  along the comparator.
* `Learning.MDP.Episodic.EpisodicMDP.integral_value_sub_integral_value_le_two_mul_sum`: the
  suboptimality of pessimistic value iteration against every Markov policy.
* `Learning.MDP.Episodic.EpisodicMDP.integral_optValue_sub_integral_value_le_two_mul_sum`: the
  suboptimality of pessimistic value iteration [JYW21, Theorem 4.2].

## References

* [Y. Jin, Z. Yang and Z. Wang, *Is pessimism provably efficient for offline RL?*, ICML 2021,
  arXiv:2012.15085][JYW21], Algorithm 1, Lemma 3.1, Theorem 4.2 and Lemma 5.1
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset LMLExplore

namespace Learning.MDP.Episodic.EpisodicMDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {M : EpisodicMDP 𝓢 𝓐} {π π' : ℕ → Kernel 𝓢 𝓐} [∀ h, IsMarkovKernel (π h)]
  [∀ h, IsMarkovKernel (π' h)] {μ : Measure 𝓢} [IsProbabilityMeasure μ] {H : ℕ} {C B : ℝ}
  {V : ℕ → 𝓢 → ℝ} {Q : ℕ → 𝓢 → 𝓐 → ℝ}

/-! ### The decomposition of suboptimality -/

/-- The values `V h s = ∫ Q h s a dπ'_h(a | s)` induced by measurable action values `Q h` before
the horizon, with `V H = 0`, are measurable up to the horizon. -/
private lemma measurable_of_eq_integral (hQ : ∀ h < H, Measurable fun p : 𝓢 × 𝓐 ↦ Q h p.1 p.2)
    (hVH : ∀ s, V H s = 0) (hVQ : ∀ h < H, ∀ s, V h s = ∫ a, Q h s a ∂(π' h s)) {h : ℕ}
    (hh : h ≤ H) : Measurable (V h) := by
  obtain hh | rfl := hh.lt_or_eq
  · rw [funext (hVQ h hh)]
    exact ((hQ h hh).stronglyMeasurable.integral_kernel_prod_right' (κ := π' h)).measurable
  · rw [funext hVH]
    exact measurable_const

/-- **Decomposition of suboptimality** [JYW21, Lemma 3.1]: for rewards in `[-C, C]`, Markov
policies `π` and `π'` and an initial probability measure `μ`, let `Q h` be measurable estimates of
the action values, bounded before the horizon `H`, and let `V h s = ∫ Q h s a dπ'_h(a | s)` before
the horizon, with `V H = 0`. Then the suboptimality `∫ V^π_0 dμ - ∫ V^π'_0 dμ` of `π'` with respect
to `π` is the sum of
* the optimization errors `∫ (∫ Q h s a dπ_h(a | s) - V h s) dμ_h` for `h < H`, against the laws
  `μ_h` of the state under `π`;
* the model evaluation errors `∫ (r_h + P_h V (h + 1) - Q h) dd^π_h` for `h < H`, against the
  occupancy measures of `π`;
* minus the model evaluation errors `∫ (r_h + P_h V (h + 1) - Q h) dd^π'_h` for `h < H`, against
  the occupancy measures of `π'`. -/
theorem integral_value_sub_integral_value_eq_sum_add_sum_sub_sum
    (hM : M.RewardsIn (Set.Icc (-C) C)) (hQ : ∀ h < H, Measurable fun p : 𝓢 × 𝓐 ↦ Q h p.1 p.2)
    (hQB : ∀ h < H, ∀ s a, |Q h s a| ≤ B) (hVH : ∀ s, V H s = 0)
    (hVQ : ∀ h < H, ∀ s, V h s = ∫ a, Q h s a ∂(π' h s)) :
    ∫ s, M.value H π 0 s ∂μ - ∫ s, M.value H π' 0 s ∂μ =
      ∑ h ∈ range H, ∫ s, (∫ a, Q h s a ∂(π h s) - V h s) ∂(M.stateMarginal π μ h) +
        ∑ h ∈ range H, ∫ p, (M.meanReward h p.1 p.2 + ∫ s', V (h + 1) s' ∂(M.trans h p) -
          Q h p.1 p.2) ∂(M.occupancy π μ h) -
        ∑ h ∈ range H, ∫ p, (M.meanReward h p.1 p.2 + ∫ s', V (h + 1) s' ∂(M.trans h p) -
          Q h p.1 p.2) ∂(M.occupancy π' μ h) := by
  have hV (h : ℕ) (hh : h ≤ H) : Measurable (V h) := measurable_of_eq_integral hQ hVH hVQ hh
  have hVB (h : ℕ) (hh : h ≤ H) (s : 𝓢) : |V h s| ≤ |B| := by
    obtain hh | rfl := hh.lt_or_eq
    · rw [hVQ h hh]
      exact abs_integral_le_of_abs_le fun a ↦ (hQB h hh s a).trans (le_abs_self B)
    · simp [hVH]
  -- the value difference along `π` and along `π'`
  have h₁ := integral_sub_integral_value (π := π) (μ := μ) hM hV hVB hQ hQB
  have h₂ := integral_sub_integral_value (π := π') (μ := μ) hM hV hVB hQ hQB
  -- along `π'`, the mismatch terms vanish
  have h₀ : ∑ h ∈ range H, ∫ s, (V h s - ∫ a, Q h s a ∂(π' h s)) ∂(M.stateMarginal π' μ h) = 0 :=
    sum_eq_zero fun h hh ↦ by simp [hVQ h (mem_range.1 hh)]
  rw [h₀, zero_add] at h₂
  simp only [hVH, integral_zero, add_zero] at h₁ h₂
  -- the terms of the statement are the opposites of those of the value difference
  have e₁ : ∑ h ∈ range H, ∫ s, (∫ a, Q h s a ∂(π h s) - V h s) ∂(M.stateMarginal π μ h) =
      -∑ h ∈ range H, ∫ s, (V h s - ∫ a, Q h s a ∂(π h s)) ∂(M.stateMarginal π μ h) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun h _ ↦ ?_
    rw [← integral_neg]
    simp_rw [neg_sub]
  have e₂ (σ : ℕ → Kernel 𝓢 𝓐) :
      ∑ h ∈ range H, ∫ p, (M.meanReward h p.1 p.2 + ∫ s', V (h + 1) s' ∂(M.trans h p) -
        Q h p.1 p.2) ∂(M.occupancy σ μ h) =
      -∑ h ∈ range H, ∫ p, (Q h p.1 p.2 - M.meanReward h p.1 p.2 -
        ∫ s', V (h + 1) s' ∂(M.trans h p)) ∂(M.occupancy σ μ h) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun h _ ↦ ?_
    rw [← integral_neg]
    congr 1 with p
    ring
  rw [e₁, e₂, e₂]
  linarith

/-! ### Greedy policies for pessimistic estimates -/

/-- **Pessimism**: for rewards in `[-C, C]`, a Markov policy `π` and an initial probability measure
`μ`, let `Q h` be measurable estimates of the action values, bounded before the horizon `H`, and
let `π'` be a Markov policy greedy for them, with values `V h s = ∫ Q h s a dπ'_h(a | s)` before
the horizon and `V H = 0`: `Q h s a ≤ V h s`. If the estimates are pessimistic,
`Q h ≤ r_h + P_h V (h + 1)`, then the suboptimality `∫ V^π_0 dμ - ∫ V^π'_0 dμ` of `π'` with respect
to `π` is at most the sum over the steps `h < H` of the integrals of the model evaluation errors
`r_h + P_h V (h + 1) - Q h` against the occupancy measures `d^π_h` of `π`. -/
theorem integral_value_sub_integral_value_le_sum (hM : M.RewardsIn (Set.Icc (-C) C))
    (hQ : ∀ h < H, Measurable fun p : 𝓢 × 𝓐 ↦ Q h p.1 p.2)
    (hQB : ∀ h < H, ∀ s a, |Q h s a| ≤ B) (hVH : ∀ s, V H s = 0)
    (hVQ : ∀ h < H, ∀ s, V h s = ∫ a, Q h s a ∂(π' h s))
    (hQV : ∀ h < H, ∀ s a, Q h s a ≤ V h s)
    (hpess : ∀ h < H, ∀ s a,
      Q h s a ≤ M.meanReward h s a + ∫ s', V (h + 1) s' ∂(M.trans h (s, a))) :
    ∫ s, M.value H π 0 s ∂μ - ∫ s, M.value H π' 0 s ∂μ ≤
      ∑ h ∈ range H, ∫ p, (M.meanReward h p.1 p.2 + ∫ s', V (h + 1) s' ∂(M.trans h p) -
        Q h p.1 p.2) ∂(M.occupancy π μ h) := by
  rw [integral_value_sub_integral_value_eq_sum_add_sum_sub_sum hM hQ hQB hVH hVQ]
  -- the optimization errors are nonpositive, since `π'` is greedy
  have h₁ : ∑ h ∈ range H, ∫ s, (∫ a, Q h s a ∂(π h s) - V h s) ∂(M.stateMarginal π μ h) ≤ 0 := by
    refine sum_nonpos fun h hh ↦ integral_nonpos fun s ↦ sub_nonpos.2 ?_
    have hh : h < H := mem_range.1 hh
    have hint : Integrable (fun a ↦ Q h s a) (π h s) :=
      integrable_of_abs_le ((hQ h hh).comp measurable_prodMk_left) (hQB h hh s) _
    simpa using integral_mono hint (integrable_const (V h s)) (hQV h hh s)
  -- the model evaluation errors along `π'` are nonnegative, since the estimates are pessimistic
  have h₂ : 0 ≤ ∑ h ∈ range H, ∫ p, (M.meanReward h p.1 p.2 + ∫ s', V (h + 1) s' ∂(M.trans h p) -
      Q h p.1 p.2) ∂(M.occupancy π' μ h) :=
    sum_nonneg fun h hh ↦ integral_nonneg fun p ↦ sub_nonneg.2 (hpess h (mem_range.1 hh) p.1 p.2)
  linarith

/-! ### Pessimistic value iteration -/

/-- The estimates of pessimistic value iteration, `Q h = min (T h - Γ h, H - h)⁺`, lie in
`[0, H - h]` before the horizon, and so do the values `V h = ∫ Q h dπ'_h` they induce, with
`V H = 0`. -/
private lemma mem_Icc_of_eq_max_min (hQ : ∀ h < H, Measurable fun p : 𝓢 × 𝓐 ↦ Q h p.1 p.2)
    (hVH : ∀ s, V H s = 0) (hVQ : ∀ h < H, ∀ s, V h s = ∫ a, Q h s a ∂(π' h s))
    {T Γ : ℕ → 𝓢 → 𝓐 → ℝ}
    (hQT : ∀ h < H, ∀ s a, Q h s a = max (min (T h s a - Γ h s a) (H - h : ℕ)) 0) {h : ℕ}
    (hh : h ≤ H) (s : 𝓢) : V h s ∈ Set.Icc 0 ((H - h : ℕ) : ℝ) := by
  obtain hh | rfl := hh.lt_or_eq
  · have hQI (a : 𝓐) : Q h s a ∈ Set.Icc 0 ((H - h : ℕ) : ℝ) := by
      rw [hQT h hh s a]
      exact ⟨le_max_right _ _, max_le (min_le_right _ _) (Nat.cast_nonneg _)⟩
    rw [hVQ h hh]
    exact Convex.integral_mem (convex_Icc _ _) isClosed_Icc (.of_forall hQI)
      (.of_mem_Icc _ _ ((hQ h hh).comp measurable_prodMk_left).aemeasurable (.of_forall hQI))
  · simp [hVH]

/-- **Suboptimality of pessimistic value iteration** against every comparator ([JYW21, Lemma 5.1,
Theorem 4.2], for an arbitrary comparator): for rewards in `[0, 1]`, a Markov policy `π` and an
initial probability measure `μ`, let `Q h` be the measurable estimates of pessimistic value
iteration, `Q h = min (T h - Γ h, H - h)⁺` before the horizon `H`, with the values
`V h s = ∫ Q h s a dπ'_h(a | s)` of a Markov policy `π'` greedy for them and `V H = 0`. If the
penalties `Γ h` dominate the errors of the estimated backups,
`|T h - (r_h + P_h V (h + 1))| ≤ Γ h`, and are integrable against the occupancy measures `d^π_h`
of `π`, then the suboptimality `∫ V^π_0 dμ - ∫ V^π'_0 dμ` of `π'` is at most
`2 ∑_{h < H} ∫ Γ h dd^π_h`. -/
theorem integral_value_sub_integral_value_le_two_mul_sum (hM : M.RewardsIn (Set.Icc 0 1))
    (hQ : ∀ h < H, Measurable fun p : 𝓢 × 𝓐 ↦ Q h p.1 p.2) (hVH : ∀ s, V H s = 0)
    (hVQ : ∀ h < H, ∀ s, V h s = ∫ a, Q h s a ∂(π' h s))
    (hQV : ∀ h < H, ∀ s a, Q h s a ≤ V h s) {T Γ : ℕ → 𝓢 → 𝓐 → ℝ}
    (hQT : ∀ h < H, ∀ s a, Q h s a = max (min (T h s a - Γ h s a) (H - h : ℕ)) 0)
    (hTΓ : ∀ h < H, ∀ s a,
      |T h s a - (M.meanReward h s a + ∫ s', V (h + 1) s' ∂(M.trans h (s, a)))| ≤ Γ h s a)
    (hΓ : ∀ h < H, Integrable (fun p : 𝓢 × 𝓐 ↦ Γ h p.1 p.2) (M.occupancy π μ h)) :
    ∫ s, M.value H π 0 s ∂μ - ∫ s, M.value H π' 0 s ∂μ ≤
      2 * ∑ h ∈ range H, ∫ p, Γ h p.1 p.2 ∂(M.occupancy π μ h) := by
  -- the backups of the values lie in `[0, H - h]`
  have hBV (h : ℕ) (hh : h < H) (s : 𝓢) (a : 𝓐) :
      M.meanReward h s a + ∫ s', V (h + 1) s' ∂(M.trans h (s, a)) ∈
        Set.Icc 0 ((H - h : ℕ) : ℝ) := by
    simpa using meanReward_add_integral_mem_Icc hM hh
      (measurable_of_eq_integral hQ hVH hVQ (h := h + 1) hh)
      (fun s' ↦ by simpa using mem_Icc_of_eq_max_min hQ hVH hVQ hQT (h := h + 1) hh s') s a
  -- the model evaluation errors lie in `[0, 2 Γ h]` [JYW21, Lemma 5.1]
  have hι (h : ℕ) (hh : h < H) (s : 𝓢) (a : 𝓐) :
      0 ≤ M.meanReward h s a + ∫ s', V (h + 1) s' ∂(M.trans h (s, a)) - Q h s a ∧
        M.meanReward h s a + ∫ s', V (h + 1) s' ∂(M.trans h (s, a)) - Q h s a ≤
          2 * Γ h s a := by
    have hx := hBV h hh s a
    have hT := abs_sub_le_iff.1 (hTΓ h hh s a)
    rw [hQT h hh s a]
    constructor
    · exact sub_nonneg.2 (max_le (min_le_of_left_le (by linarith)) hx.1)
    · exact sub_le_comm.1 (le_max_of_le_left (le_min (by linarith) (by linarith [hx.2])))
  have hQB (h : ℕ) (hh : h < H) (s : 𝓢) (a : 𝓐) : |Q h s a| ≤ H := by
    rw [hQT h hh s a, abs_of_nonneg (le_max_right _ _)]
    exact max_le ((min_le_right _ _).trans (by simp)) (Nat.cast_nonneg _)
  have hM' : M.RewardsIn (Set.Icc (-1) 1) := hM.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)
  refine (integral_value_sub_integral_value_le_sum hM' hQ hQB hVH hVQ hQV
    fun h hh s a ↦ sub_nonneg.1 (hι h hh s a).1).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun h hh ↦ ?_
  have hh : h < H := mem_range.1 hh
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (.of_forall fun p ↦ (hι h hh p.1 p.2).1) ((hΓ h hh).const_mul 2)
    (.of_forall fun p ↦ (hι h hh p.1 p.2).2)

/-- **Suboptimality of pessimistic value iteration** [JYW21, Theorem 4.2]: for rewards in `[0, 1]`,
a finite nonempty action set and an initial probability measure `μ`, let `Q h` be the measurable
estimates of pessimistic value iteration, `Q h = min (T h - Γ h, H - h)⁺` before the horizon `H`,
with the values `V h s = ∫ Q h s a dπ'_h(a | s)` of a Markov policy `π'` greedy for them and
`V H = 0`. If the penalties `Γ h` dominate the errors of the estimated backups,
`|T h - (r_h + P_h V (h + 1))| ≤ Γ h`, and are integrable against the occupancy measures
`d^{π*}_h` of the greedy optimal policy `π*`, then `∫ V*_0 dμ - ∫ V^π'_0 dμ` is at most
`2 ∑_{h < H} ∫ Γ h dd^{π*}_h`. -/
theorem integral_optValue_sub_integral_value_le_two_mul_sum [Fintype 𝓐] [Nonempty 𝓐]
    (hM : M.RewardsIn (Set.Icc 0 1)) (hQ : ∀ h < H, Measurable fun p : 𝓢 × 𝓐 ↦ Q h p.1 p.2)
    (hVH : ∀ s, V H s = 0) (hVQ : ∀ h < H, ∀ s, V h s = ∫ a, Q h s a ∂(π' h s))
    (hQV : ∀ h < H, ∀ s a, Q h s a ≤ V h s) {T Γ : ℕ → 𝓢 → 𝓐 → ℝ}
    (hQT : ∀ h < H, ∀ s a, Q h s a = max (min (T h s a - Γ h s a) (H - h : ℕ)) 0)
    (hTΓ : ∀ h < H, ∀ s a,
      |T h s a - (M.meanReward h s a + ∫ s', V (h + 1) s' ∂(M.trans h (s, a)))| ≤ Γ h s a)
    (hΓ : ∀ h < H, Integrable (fun p : 𝓢 × 𝓐 ↦ Γ h p.1 p.2)
      (M.occupancy (fun k ↦ Kernel.deterministic (M.optPolicy H k) (measurable_optPolicy k)) μ h)) :
    ∫ s, M.optValue H 0 s ∂μ - ∫ s, M.value H π' 0 s ∂μ ≤
      2 * ∑ h ∈ range H, ∫ p, Γ h p.1 p.2
        ∂(M.occupancy (fun k ↦ Kernel.deterministic (M.optPolicy H k) (measurable_optPolicy k))
          μ h) := by
  simpa only [value_optPolicy] using
    integral_value_sub_integral_value_le_two_mul_sum hM hQ hVH hVQ hQV hQT hTΓ hΓ

end Learning.MDP.Episodic.EpisodicMDP
