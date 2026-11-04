/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Episodic.Occupancy

/-!
# The extended value-difference identity in an episodic MDP

Let `M : EpisodicMDP 𝓢 𝓐` be an episodic MDP with bounded rewards, `π : ℕ → Kernel 𝓢 𝓐` a Markov
policy, `μ` a probability measure on the states, `H` a horizon, and write `μ_h` and `d^π_h` for
the state marginals and the occupancy measures of `π` from `μ`. Let `V̂_h` and `Q̂_h` be bounded
measurable estimates of the values and action values. The value of `π` and the integral of `V̂_0`
differ by two sums along the episodes of `π` and a terminal term
(`Learning.MDP.Episodic.EpisodicMDP.integral_sub_integral_value`):

`∫ V̂_0 dμ - ∫ V^π_0 dμ = ∑_{h < H} ∫ (V̂_h s - ∫ Q̂_h (s, a) dπ_h(a | s)) dμ_h
  + ∑_{h < H} ∫ (Q̂_h - r_h - P_h V̂_{h+1}) dd^π_h + ∫ V̂_H dμ_H`.

The first sum measures how far `V̂` is from the averages of `Q̂` under `π`, the second sum is
made of the Bellman errors of `Q̂` with respect to `V̂`. This identity is the starting point of the
analyses of planning with estimated models, of optimistic exploration and of pessimistic offline
learning. It specializes to:
* **the extended value-difference identity** [JYW21, Lemma A.1]: for `V̂_h s = ∫ Q̂_h (s, a)
  dπ'_h(a | s)` with a second Markov policy `π'` and `Q̂_H = 0`, the first sum is the
  policy-mismatch term `∑_h ∫ (∫ Q̂_h (s, ·) dπ'_h s - ∫ Q̂_h (s, ·) dπ_h s) dμ_h`;
* **the performance difference lemma**, the episodic form of [AJKS, Lemma 1.16]: for
  `V̂ = V^π'` and `Q̂ = Q^π'`, the Bellman errors vanish and `∫ V^π_0 dμ - ∫ V^π'_0 dμ` is the sum
  over the steps of the integrals of the advantages `Q^π'_h (s, a) - V^π'_h s` against `d^π_h`;
* **the optimistic decomposition**: if `V̂_H = 0`, `V̂_h s ≤ ∫ Q̂_h (s, a) dπ_h(a | s)` and
  `Q̂_h ≤ r_h + b_h + P̂_h V̂_{h+1}` for bonuses `b_h` and estimated transition kernels `P̂_h`,
  then `∫ V̂_0 dμ - ∫ V^π_0 dμ ≤ ∑_h ∫ (b_h + P̂_h V̂_{h+1} - P_h V̂_{h+1}) dd^π_h`.

[JYW21, Lemma A.1] is stated for an initial state `s`; here the initial state has an arbitrary
law `μ`, the state and action spaces are general measurable spaces, and the expectations along
the episodes of `π` are integrals against its occupancy measures. Along every run of `π` in the
augmented MDP, these integrals are the expectations of the corresponding sums
(`Learning.MDP.Episodic.EpisodicMDP.integral_sum_eq_sum_integral_occupancy`). The discounted form
of the extended value-difference identity is `Learning.MDP.integral_integral_sub_integral_value`.

## Main statements

* `Learning.MDP.Episodic.EpisodicMDP.integral_sub_integral_value`: the value difference for
  arbitrary bounded measurable estimates `V̂` and `Q̂`.
* `Learning.MDP.Episodic.EpisodicMDP.integral_integral_sub_integral_value`: the extended
  value-difference identity [JYW21, Lemma A.1].
* `Learning.MDP.Episodic.EpisodicMDP.integral_value_sub_integral_value`: the episodic performance
  difference lemma.
* `Learning.MDP.Episodic.EpisodicMDP.integral_sub_integral_value_le`: the optimistic
  decomposition.

## References

* [Y. Jin, Z. Yang and Z. Wang, *Is pessimism provably efficient for offline RL?*, ICML 2021,
  arXiv:2012.15085][JYW21], Lemma A.1
* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], Lemma 1.16
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset LMLExplore

namespace Learning.MDP.Episodic.EpisodicMDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {M : EpisodicMDP 𝓢 𝓐} {π : ℕ → Kernel 𝓢 𝓐} [∀ h, IsMarkovKernel (π h)] {μ : Measure 𝓢}
  [IsProbabilityMeasure μ] {H : ℕ} {C B B' : ℝ} {V : ℕ → 𝓢 → ℝ} {Q : ℕ → 𝓢 → 𝓐 → ℝ}

/-- The integral against the law `μ_h` of the state of `V s - ∫ Q (s, a) dπ_h(a | s)` is the
integral of `V s - Q (s, a)` against the occupancy measure `d^π_h`. -/
private lemma integral_sub_integral_stateMarginal {V : 𝓢 → ℝ} {Q : 𝓢 → 𝓐 → ℝ}
    (hV : Measurable V) (hVB : ∀ s, |V s| ≤ B) (hQ : Measurable fun p : 𝓢 × 𝓐 ↦ Q p.1 p.2)
    (hQB : ∀ s a, |Q s a| ≤ B') (h : ℕ) :
    ∫ s, (V s - ∫ a, Q s a ∂(π h s)) ∂(M.stateMarginal π μ h) =
      ∫ p, (V p.1 - Q p.1 p.2) ∂(M.occupancy π μ h) := by
  rw [occupancy_def, Measure.integral_compProd (integrable_of_abs_le
    (f := fun p : 𝓢 × 𝓐 ↦ V p.1 - Q p.1 p.2) ((hV.comp measurable_fst).sub hQ)
    (fun p ↦ (abs_sub _ _).trans (add_le_add (hVB p.1) (hQB p.1 p.2))) _)]
  refine integral_congr_ae (.of_forall fun s ↦ ?_)
  dsimp only
  rw [integral_sub (integrable_const _) (integrable_of_abs_le (f := fun a ↦ Q s a)
    (hQ.comp measurable_prodMk_left) (hQB s) _), integral_const, probReal_univ, one_smul]

/-- **Value difference along the occupancy measures**: for rewards in `[-C, C]`, a Markov policy
`π` and an initial probability measure `μ`, let `V h` and `Q h` be measurable estimates of the
values and the action values, bounded up to the horizon `H`. Then `∫ V 0 dμ - ∫ V^π_0 dμ` is the
sum of
* the mismatch terms `∫ (V h s - ∫ Q h s a dπ_h(a | s)) dμ_h` for `h < H`, against the laws `μ_h`
  of the state;
* the Bellman errors `∫ (Q h - r_h - ∫ V (h + 1) dP_h) dd^π_h` for `h < H`, against the occupancy
  measures `d^π_h`;
* the terminal term `∫ V H dμ_H`. -/
theorem integral_sub_integral_value (hM : M.RewardsIn (Set.Icc (-C) C))
    (hV : ∀ h ≤ H, Measurable (V h)) (hVB : ∀ h ≤ H, ∀ s, |V h s| ≤ B)
    (hQ : ∀ h < H, Measurable fun p : 𝓢 × 𝓐 ↦ Q h p.1 p.2)
    (hQB : ∀ h < H, ∀ s a, |Q h s a| ≤ B') :
    ∫ s, V 0 s ∂μ - ∫ s, M.value H π 0 s ∂μ =
      ∑ h ∈ range H, ∫ s, (V h s - ∫ a, Q h s a ∂(π h s)) ∂(M.stateMarginal π μ h) +
        ∑ h ∈ range H, ∫ p, (Q h p.1 p.2 - M.meanReward h p.1 p.2 -
          ∫ s', V (h + 1) s' ∂(M.trans h p)) ∂(M.occupancy π μ h) +
        ∫ s, V H s ∂(M.stateMarginal π μ H) := by
  -- extend `V` by zero beyond the horizon, to apply the telescoping identity
  set W : ℕ → 𝓢 → ℝ := fun h ↦ if h ≤ H then V h else 0
  have hWV {h : ℕ} (hh : h ≤ H) : W h = V h := by simp [W, hh]
  have hWm (h : ℕ) : Measurable (W h) := by
    by_cases hh : h ≤ H
    · exact hWV hh ▸ hV h hh
    · simp only [W, hh, ↓reduceIte]
      exact measurable_const
  have hWB (h : ℕ) (s : 𝓢) : |W h s| ≤ |B| := by
    by_cases hh : h ≤ H
    · exact hWV hh ▸ (hVB h hh s).trans (le_abs_self B)
    · simp [W, hh]
  have htel := integral_eq_sum_integral_occupancy_add (M := M) (π := π) (μ := μ) hWm hWB H
  rw [hWV le_rfl, hWV (Nat.zero_le H)] at htel
  rw [htel, integral_value_eq_sum_integral_occupancy hM H, add_sub_right_comm,
    ← sum_sub_distrib, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun h hh ↦ ?_
  have hh : h < H := mem_range.1 hh
  rw [hWV hh.le, hWV (h := h + 1) hh, integral_sub_integral_stateMarginal (hV h hh.le)
    (hVB h hh.le) (hQ h hh) (hQB h hh)]
  -- all the integrands are bounded and measurable
  have hPV : Measurable fun p ↦ ∫ s', V (h + 1) s' ∂(M.trans h p) :=
    ((hV (h + 1) hh).stronglyMeasurable.integral_kernel (κ := M.trans h)).measurable
  have iV : Integrable (fun p : 𝓢 × 𝓐 ↦ V h p.1) (M.occupancy π μ h) :=
    integrable_of_abs_le ((hV h hh.le).comp measurable_fst) (fun p ↦ hVB h hh.le p.1) _
  have iPV : Integrable (fun p ↦ ∫ s', V (h + 1) s' ∂(M.trans h p)) (M.occupancy π μ h) :=
    integrable_of_abs_le hPV (fun p ↦ abs_integral_le_of_abs_le (hVB (h + 1) hh)) _
  have ir : Integrable (fun p : 𝓢 × 𝓐 ↦ M.meanReward h p.1 p.2) (M.occupancy π μ h) :=
    integrable_of_abs_le (M.measurable_meanReward h)
      (fun p ↦ abs_le.2 (meanReward_mem_Icc hM h p.1 p.2)) _
  have iQ : Integrable (fun p : 𝓢 × 𝓐 ↦ Q h p.1 p.2) (M.occupancy π μ h) :=
    integrable_of_abs_le (hQ h hh) (fun p ↦ hQB h hh p.1 p.2) _
  have iQr : Integrable (fun p : 𝓢 × 𝓐 ↦ Q h p.1 p.2 - M.meanReward h p.1 p.2)
      (M.occupancy π μ h) :=
    iQ.sub ir
  rw [integral_sub iV iPV, integral_sub iV iQ, integral_sub iQr iPV, integral_sub iQ ir]
  ring

/-- **Extended value-difference identity** [JYW21, Lemma A.1]: for rewards in `[-C, C]`, Markov
policies `π` and `π'` and an initial probability measure `μ`, let `Q h` be measurable estimates of
the action values, bounded before the horizon `H`, with `Q H = 0`, and let
`V̂_h s = ∫ Q h s a dπ'_h(a | s)`. Then `∫ V̂_0 dμ - ∫ V^π_0 dμ` is the sum of
* the policy-mismatch terms `∫ (∫ Q h s a dπ'_h(a | s) - ∫ Q h s a dπ_h(a | s)) dμ_h` for
  `h < H`, against the laws `μ_h` of the state under `π`;
* the Bellman errors `∫ (Q h - r_h - P_h V̂_{h+1}) dd^π_h` for `h < H`, against the occupancy
  measures `d^π_h` of `π`. -/
theorem integral_integral_sub_integral_value (hM : M.RewardsIn (Set.Icc (-C) C))
    {π' : ℕ → Kernel 𝓢 𝓐} [∀ h, IsMarkovKernel (π' h)]
    (hQ : ∀ h < H, Measurable fun p : 𝓢 × 𝓐 ↦ Q h p.1 p.2)
    (hQB : ∀ h < H, ∀ s a, |Q h s a| ≤ B) (hQH : ∀ s a, Q H s a = 0) :
    ∫ s, ∫ a, Q 0 s a ∂(π' 0 s) ∂μ - ∫ s, M.value H π 0 s ∂μ =
      ∑ h ∈ range H, ∫ s, (∫ a, Q h s a ∂(π' h s) - ∫ a, Q h s a ∂(π h s))
          ∂(M.stateMarginal π μ h) +
        ∑ h ∈ range H, ∫ p, (Q h p.1 p.2 - M.meanReward h p.1 p.2 -
          ∫ s', ∫ a, Q (h + 1) s' a ∂(π' (h + 1) s') ∂(M.trans h p)) ∂(M.occupancy π μ h) := by
  have hVm (h : ℕ) (hh : h ≤ H) : Measurable fun s ↦ ∫ a, Q h s a ∂(π' h s) := by
    obtain hh | rfl := hh.lt_or_eq
    · exact ((hQ h hh).stronglyMeasurable.integral_kernel_prod_right' (κ := π' h)).measurable
    · simp [hQH]
  have hVB (h : ℕ) (hh : h ≤ H) (s : 𝓢) : |∫ a, Q h s a ∂(π' h s)| ≤ |B| := by
    obtain hh | rfl := hh.lt_or_eq
    · exact abs_integral_le_of_abs_le fun a ↦ (hQB h hh s a).trans (le_abs_self B)
    · simp [hQH]
  simpa [hQH] using integral_sub_integral_value (V := fun h s ↦ ∫ a, Q h s a ∂(π' h s)) (μ := μ)
    (π := π) hM hVm hVB hQ hQB

/-- **Performance difference lemma**, the episodic form of [AJKS, Lemma 1.16]: for rewards in
`[-C, C]`, Markov policies `π` and `π'` and an initial probability measure `μ`, the value of `π`
exceeds the value of `π'` by the sum over the steps `h < H` of the integrals of the advantages
`Q^π'_h (s, a) - V^π'_h s` of `π'` against the occupancy measures `d^π_h` of `π`. -/
theorem integral_value_sub_integral_value (hM : M.RewardsIn (Set.Icc (-C) C))
    (π' : ℕ → Kernel 𝓢 𝓐) [∀ h, IsMarkovKernel (π' h)] :
    ∫ s, M.value H π 0 s ∂μ - ∫ s, M.value H π' 0 s ∂μ =
      ∑ h ∈ range H, ∫ p, (M.qValue H π' h p.1 p.2 - M.value H π' h p.1)
        ∂(M.occupancy π μ h) := by
  have hQB (h : ℕ) (hh : h < H) (s : 𝓢) (a : 𝓐) : |M.qValue H π' h s a| ≤ H * |C| := by
    have hQ := qValue_mem_Icc (π := π') hM hh s a
    rw [mul_neg] at hQ
    calc |M.qValue H π' h s a| ≤ (H - h : ℕ) * C := abs_le.2 hQ
      _ ≤ (H - h : ℕ) * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) (Nat.cast_nonneg _)
      _ ≤ H * |C| :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) (abs_nonneg C)
  have h := integral_sub_integral_value (V := M.value H π') (Q := M.qValue H π') (μ := μ)
    (π := π) hM (fun h _ ↦ measurable_value h) (fun h _ ↦ abs_value_le_mul_abs hM h)
    (fun h _ ↦ measurable_qValue h) hQB
  -- the Bellman errors of `Q^π'` with respect to `V^π'` vanish
  have h_bellman (h : ℕ) (p : 𝓢 × 𝓐) : M.qValue H π' h p.1 p.2 - M.meanReward h p.1 p.2 -
      ∫ s', M.value H π' (h + 1) s' ∂(M.trans h p) = 0 := by
    simp [qValue_def]
  simp only [h_bellman, integral_zero, sum_const_zero, add_zero, value_self] at h
  rw [← neg_sub, h, ← sum_neg_distrib]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk : k < H := mem_range.1 hk
  rw [integral_sub_integral_stateMarginal (measurable_value k) (abs_value_le_mul_abs hM k)
    (measurable_qValue k) (hQB k hk), ← integral_neg]
  refine integral_congr_ae (.of_forall fun p ↦ ?_)
  dsimp only
  ring

/-- **Optimistic decomposition**: for rewards in `[-C, C]`, a Markov policy `π` and an initial
probability measure `μ`, let `V h` and `Q h` be measurable estimates of the values and the action
values, bounded up to the horizon `H`, with `V H = 0`. Let `P' h` be Markov kernels (estimated
transition kernels) and `b h` bounded measurable bonuses. If, before the horizon,
* `V h s ≤ ∫ Q h s a dπ_h(a | s)`, and
* `Q h s a ≤ r_h (s, a) + b h s a + ∫ V (h + 1) dP' h (s, a)`,

then `∫ V 0 dμ - ∫ V^π_0 dμ` is at most the sum over the steps `h < H` of the integrals of
`b h + ∫ V (h + 1) dP' h - ∫ V (h + 1) dP_h` against the occupancy measures `d^π_h` of `π`. -/
theorem integral_sub_integral_value_le (hM : M.RewardsIn (Set.Icc (-C) C))
    (hV : ∀ h ≤ H, Measurable (V h)) (hVB : ∀ h ≤ H, ∀ s, |V h s| ≤ B) (hVH : ∀ s, V H s = 0)
    (hQ : ∀ h < H, Measurable fun p : 𝓢 × 𝓐 ↦ Q h p.1 p.2)
    (hQB : ∀ h < H, ∀ s a, |Q h s a| ≤ B') {P' : ℕ → Kernel (𝓢 × 𝓐) 𝓢}
    [∀ h, IsMarkovKernel (P' h)] {b : ℕ → 𝓢 → 𝓐 → ℝ} {B'' : ℝ}
    (hb : ∀ h < H, Measurable fun p : 𝓢 × 𝓐 ↦ b h p.1 p.2)
    (hbB : ∀ h < H, ∀ s a, |b h s a| ≤ B'')
    (hVQ : ∀ h < H, ∀ s, V h s ≤ ∫ a, Q h s a ∂(π h s))
    (hQV : ∀ h < H, ∀ s a,
      Q h s a ≤ M.meanReward h s a + b h s a + ∫ s', V (h + 1) s' ∂(P' h (s, a))) :
    ∫ s, V 0 s ∂μ - ∫ s, M.value H π 0 s ∂μ ≤
      ∑ h ∈ range H, ∫ p, (b h p.1 p.2 + ∫ s', V (h + 1) s' ∂(P' h p) -
        ∫ s', V (h + 1) s' ∂(M.trans h p)) ∂(M.occupancy π μ h) := by
  rw [integral_sub_integral_value hM hV hVB hQ hQB]
  simp only [hVH, integral_zero, add_zero]
  -- the mismatch terms are nonpositive
  have h_mismatch : ∑ h ∈ range H, ∫ s, (V h s - ∫ a, Q h s a ∂(π h s)) ∂(M.stateMarginal π μ h) ≤
      0 :=
    sum_nonpos fun h hh ↦ integral_nonpos fun s ↦ sub_nonpos.2 (hVQ h (mem_range.1 hh) s)
  -- the Bellman errors are bounded by the bonuses and the errors of the estimated kernels
  have h_bellman : ∑ h ∈ range H, ∫ p, (Q h p.1 p.2 - M.meanReward h p.1 p.2 -
        ∫ s', V (h + 1) s' ∂(M.trans h p)) ∂(M.occupancy π μ h) ≤
      ∑ h ∈ range H, ∫ p, (b h p.1 p.2 + ∫ s', V (h + 1) s' ∂(P' h p) -
        ∫ s', V (h + 1) s' ∂(M.trans h p)) ∂(M.occupancy π μ h) := by
    refine sum_le_sum fun h hh ↦ ?_
    have hh : h < H := mem_range.1 hh
    have hPV (κ : Kernel (𝓢 × 𝓐) 𝓢) [IsMarkovKernel κ] :
        Integrable (fun p ↦ ∫ s', V (h + 1) s' ∂(κ p)) (M.occupancy π μ h) :=
      integrable_of_abs_le ((hV (h + 1) hh).stronglyMeasurable.integral_kernel (κ := κ)).measurable
        (fun p ↦ abs_integral_le_of_abs_le (hVB (h + 1) hh)) _
    have ir : Integrable (fun p : 𝓢 × 𝓐 ↦ M.meanReward h p.1 p.2) (M.occupancy π μ h) :=
      integrable_of_abs_le (M.measurable_meanReward h)
        (fun p ↦ abs_le.2 (meanReward_mem_Icc hM h p.1 p.2)) _
    have iQ : Integrable (fun p : 𝓢 × 𝓐 ↦ Q h p.1 p.2) (M.occupancy π μ h) :=
      integrable_of_abs_le (hQ h hh) (fun p ↦ hQB h hh p.1 p.2) _
    have ib : Integrable (fun p : 𝓢 × 𝓐 ↦ b h p.1 p.2) (M.occupancy π μ h) :=
      integrable_of_abs_le (hb h hh) (fun p ↦ hbB h hh p.1 p.2) _
    refine integral_mono ((iQ.sub ir).sub (hPV (M.trans h))) ((ib.add (hPV (P' h))).sub
      (hPV (M.trans h))) fun p ↦ ?_
    dsimp only
    linarith [hQV h hh p.1 p.2]
  linarith

end Learning.MDP.Episodic.EpisodicMDP
