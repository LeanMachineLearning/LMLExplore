/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Real.Sqrt
public import LMLExplore.Bandits.AdversarialRegret
public import LMLExplore.Bandits.Exp4.IX

/-!
# High-probability regret bounds of Exp4-IX and Exp3-IX against an adaptive adversary

Exp4-IX (`LMLExplore.Bandits.exp4IX`) runs exponential weights over a finite set `β` of `M`
experts on the implicit-exploration estimates `Ŷ t a = 𝟙{A t = a} (1 - Y t) / (P t a + γ t)` of
the losses `1 - Y t`. The implicit exploration `γ t > 0` biases the estimates downwards, and this
bias makes them concentrate without any variance term [Neu15, Lemma 1]: the weighted deviations
`∑ t < n, ∑ a, c t a * (Ŷ t a - (1 - μ t a))` from the conditional means `μ t a` of the rewards,
for coefficients `0 ≤ c t a ≤ 2 γ t` known before round `t` and vanishing on the arms of weight
zero, exceed `log (1 / δ)` with probability at most `δ`
(`WeightAlgorithm.measure_log_one_div_le_sum_sum_mul_iwEstimator_add_sub_le`).

Against any environment whose feedback at the rounds `t < n` is almost surely in `[0, 1]` (an
adaptive adversary, which includes oblivious reward tables and stochastic bandits), this file
combines this concentration with the pathwise bound `Exp4IX.sum_one_sub_sub_dotProduct_le` on the
estimated regret. For nonincreasing learning rates `η t > 0` and implicit-exploration parameters
`γ t ≥ 0` with `η t ≤ 2 γ t` and `γ (n - 1) > 0`, with probability at least `1 - δ` the expert
random regret `R̂ᴱ_n = max_m ∑ t < n, (⟨adv (O t) m, μ t⟩ - Y t)` (`expertRandomRegret`), with
`μ t a = env.means O A Y a t`, satisfies
`R̂ᴱ_n < log M / η (n - 1) + k ∑ t < n, (γ t + η t / 2) + log (2 M / δ) / (2 γ (n - 1)) +
  log (2 / δ)`, with `k` the number of arms.

The two tunings of [Neu15] follow, with sharper constants in front of `log (2 / δ)`:

* constant rates `η = 2 γ = √(2 log M / (n k))` give
  `R̂ᴱ_n < 2 √(2 n k log M) + (√(n k / (2 log M)) + 1) log (2 / δ)` [Neu15, Theorem 2], where
  [Neu15] has `√(2 n k / log M)` in place of `√(n k / (2 log M))`;
* for Exp3-IX, the instance of Exp4-IX with the experts `α` that each recommend one arm, the
  anytime rates `η t = 2 γ t = √(log k / (k (t + 1)))` give
  `R̂_n < 4 √(n k log k) + (√(n k / log k) + 1) log (2 / δ)` for the random regret
  `R̂_n = max_a ∑ t < n, (μ t a - Y t)` [Neu15, Theorem 1], where [Neu15] has `2 √(n k / log k)` in
  place of `√(n k / log k)`.

## Main statements

* `Exp4IX.measure_le_mul_sum_dotProduct_sub_le`: the estimated losses of an expert concentrate
  around its expected losses.
* `Exp4IX.measure_le_expertRandomRegret_le`: the high-probability bound on the expert random
  regret of Exp4-IX for nonincreasing rates.
* `Exp4IX.measure_two_mul_sqrt_add_le_expertRandomRegret_le`: [Neu15, Theorem 2].
* `Exp4IX.measure_four_mul_sqrt_add_le_randomRegret_le`: [Neu15, Theorem 1].

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
* [Neu15] G. Neu, *Explore no more: improved high-probability regret bounds for non-stochastic
  bandits*, NeurIPS 2015.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real

namespace LMLExplore.Bandits.Exp4IX

variable {α β 𝓞 : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]
  {adv : 𝓞 → β → simplex α} {η γ : ℕ → ℝ}

omit [DecidableEq α] [Fintype β] in
/-- If the observations come from a probability space, the arms are nonempty, as the advice of the
experts is in the simplex of the arms. -/
private lemma nonempty_arms {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (adv : 𝓞 → β → simplex α) (O : ℕ → Ω → 𝓞) : Nonempty α :=
  have := nonempty_of_isProbabilityMeasure P
  nonempty_of_mem_simplex (adv (O 0 (Classical.arbitrary Ω)) (Classical.arbitrary β)).2

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞]
  {hadv : Measurable adv}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {env : Environment 𝓞 α ℝ} {n : ℕ} {δ : ℝ}

/-- **Concentration of the estimated losses of an expert** [Neu15, Lemma 1]. Along a run of
Exp4-IX against any environment whose feedback at every round `t < n` is almost surely in
`[0, 1]`, with `Ŷ t` the implicit-exploration estimates of the losses `1 - Y t` and
`μ t a = env.means O A Y a t` the conditional means of the rewards, for `0 ≤ c ≤ γ t` at the
rounds `t < n`, `δ > 0` and every expert `m`, the probability that
`log (1 / δ) ≤ 2 c ∑ t < n, (adv (O t) m ⬝ᵥ Ŷ t - ∑ a, adv (O t) m a * (1 - μ t a))` is at most
`δ`. -/
theorem measure_le_mul_sum_dotProduct_sub_le (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) {c : ℝ} (hc : 0 ≤ c) (hcγ : ∀ t < n, c ≤ γ t)
    (hδ : 0 < δ) (m : β) :
    P {ω | log (1 / δ) ≤ 2 * c * ∑ t ∈ range n, ((adv (O t ω) m : α → ℝ) ⬝ᵥ
        iwEstimator (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t)
          (A t ω) (1 - Y t ω) - ∑ a, (adv (O t ω) m : α → ℝ) a * (1 - env.means O A Y a t ω))} ≤
      ENNReal.ofReal δ := by
  have := nonempty_arms P adv O
  rw [exp4IX_def] at h
  have hE : ∀ a, Measurable fun o ↦ 2 * c * (adv o m : α → ℝ) a := fun a ↦
    measurable_const.mul ((measurable_pi_apply a).comp
      (measurable_subtype_coe.comp ((measurable_pi_apply m).comp hadv)))
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (WeightAlgorithm.measure_log_one_div_le_sum_sum_mul_iwEstimator_add_sub_le h hY
      (c := fun t a ω ↦ 2 * c * (adv (O t ω) m : α → ℝ) a)
      (fun t _ a ↦ Measurable.comp (mα := h.filtrationObs t)
        (g := fun o ↦ 2 * c * (adv o m : α → ℝ) a) (hE a) (h.adapted_obs_filtrationObs t))
      (fun t _ a ω ↦ mul_nonneg (by positivity) ((mem_simplex_iff.1 (adv (O t ω) m).2).1 a))
      (fun t ht a ω ↦ by
        have h1 := (simplex_subset_Icc (adv (O t ω) m).2).2 a
        have h0 := (mem_simplex_iff.1 (adv (O t ω) m).2).1 a
        calc 2 * c * (adv (O t ω) m : α → ℝ) a ≤ 2 * c * 1 :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ 2 * γ t := by linarith [hcγ t ht])
      (fun t _ a ω ha ↦ by rw [adv_apply_eq_zero_of_exp4IXWeights_eq_zero ha m, mul_zero]) hδ)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine hω.trans_eq ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [dotProduct, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ by ring

/-- **High-probability regret bound of Exp4-IX** [Neu15, proofs of Theorems 1 and 2]. Along a run
of Exp4-IX against any environment whose feedback at every round `t < n` is almost surely in
`[0, 1]`, for nonincreasing learning rates `η t > 0` and implicit-exploration parameters
`γ t ≥ 0` with `η t ≤ 2 γ t` at the rounds `t < n` and `γ (n - 1) > 0`, and for `δ > 0`, the
probability that the expert random regret `max_m ∑ t < n, (∑ a, adv (O t) m a * μ t a - Y t)` is
at least
`log M / η (n - 1) + k ∑ t < n, (γ t + η t / 2) + log (2 M / δ) / (2 γ (n - 1)) + log (2 / δ)`
is at most `δ`, with `μ t a = env.means O A Y a t` the conditional means of the rewards, `M` the
number of experts and `k` the number of arms. -/
theorem measure_le_expertRandomRegret_le (h : IsAlgEnvSeq O A Y (exp4IX adv hadv η γ) env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) (hη : ∀ t, 0 < η t) (hη_anti : Antitone η)
    (hγ : ∀ t, 0 ≤ γ t) (hγ_anti : Antitone γ) (hγn : 0 < γ (n - 1))
    (hηγ : ∀ t < n, η t ≤ 2 * γ t) (hδ : 0 < δ) :
    P {ω | log (Fintype.card β) / η (n - 1) +
        Fintype.card α * ∑ t ∈ range n, (γ t + η t / 2) +
          log (2 * Fintype.card β / δ) / (2 * γ (n - 1)) + log (2 / δ) ≤
        expertRandomRegret env (fun o m ↦ (adv o m : α → ℝ)) O A Y n ω} ≤ ENNReal.ofReal δ := by
  have := nonempty_arms P adv O
  have h' := h
  rw [exp4IX_def] at h'
  set M : ℝ := (Fintype.card β : ℝ) with hM_def
  have hM : 0 < M := Nat.cast_pos.2 Fintype.card_pos
  set δ₁ : ℝ := δ / (2 * M) with hδ₁_def
  have hδ₁ : 0 < δ₁ := by positivity
  have hlog1 : log (1 / δ₁) = log (2 * M / δ) := by rw [hδ₁_def, one_div_div]
  have hlog2 : log (1 / (δ / 2)) = log (2 / δ) := by rw [one_div_div]
  -- the estimates of the losses of round `t`
  set Yh : ℕ → Ω → α → ℝ := fun t ω ↦ iwEstimator
    (fun a ↦ exp4IXWeights adv η γ t (history O A Y t ω) (O t ω) a + γ t) (A t ω) (1 - Y t ω)
    with hYh
  -- the deviations of the estimated losses of the experts, and of the sums of the estimates
  set E1 : β → Set Ω := fun m ↦ {ω | log (1 / δ₁) ≤ 2 * γ (n - 1) * ∑ t ∈ range n,
    ((adv (O t ω) m : α → ℝ) ⬝ᵥ Yh t ω -
      ∑ a, (adv (O t ω) m : α → ℝ) a * (1 - env.means O A Y a t ω))} with hE1_def
  set E2 : Set Ω := {ω | Fintype.card α * ∑ t ∈ range n, (γ t + η t / 2) + log (1 / (δ / 2)) ≤
    ∑ t ∈ range n, (γ t + η t / 2) * ∑ a, Yh t ω a} with hE2_def
  have hE1 : ∀ m, P (E1 m) ≤ ENNReal.ofReal δ₁ := fun m ↦
    measure_le_mul_sum_dotProduct_sub_le h hY hγn.le
      (fun t ht ↦ hγ_anti (Nat.le_sub_one_of_lt ht)) hδ₁ m
  have hE2 : P E2 ≤ ENNReal.ofReal (δ / 2) :=
    WeightAlgorithm.measure_add_le_sum_mul_sum_iwEstimator_le h' hY (γ := γ)
      (b := fun t ↦ γ t + η t / 2)
      (fun t _ ↦ by linarith [hγ t, hη t]) (fun t ht ↦ by linarith [hηγ t ht]) (half_pos hδ)
  calc _ ≤ P ((⋃ m, E1 m) ∪ E2) := measure_mono_ae ?_
    _ ≤ ∑ m, P (E1 m) + P E2 :=
        (measure_union_le _ _).trans (add_le_add (measure_iUnion_fintype_le _ _) le_rfl)
    _ ≤ ∑ _m : β, ENNReal.ofReal δ₁ + ENNReal.ofReal (δ / 2) :=
        add_le_add (Finset.sum_le_sum fun m _ ↦ hE1 m) hE2
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ hδ₁.le,
          ← ENNReal.ofReal_add (Finset.sum_nonneg fun _ _ ↦ hδ₁.le) (half_pos hδ).le]
        congr 1
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hM_def, hδ₁_def]
        field_simp
        ring
  -- outside these events, the regret against every expert is below the bound
  filter_upwards [hY, ae_all_iff.2 fun t ↦ WeightAlgorithm.ae_weights_action_pos h' t]
    with ω hYω hA hbad
  by_contra hgood
  simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hgood
  obtain ⟨hgood1, hgood2⟩ := hgood
  obtain ⟨m, hm⟩ := exists_eq_ciSup_of_finite (f := fun m ↦ ∑ t ∈ range n,
    (∑ a, (adv (O t ω) m : α → ℝ) a * env.means O A Y a t ω - Y t ω))
  simp only [expertRandomRegret_def, ← hm] at hbad
  -- the pathwise bound on the estimated regret against `m`
  have hpath := sum_one_sub_sub_dotProduct_le (adv := adv) O A Y ω hη hη_anti hγ hYω
    (fun t _ ↦ (add_pos_of_pos_of_nonneg (hA t) (hγ t)).ne') m
  -- the regret against `m` is the estimated regret plus the deviation of the estimated losses
  have hsplit : ∑ t ∈ range n, (∑ a, (adv (O t ω) m : α → ℝ) a * env.means O A Y a t ω - Y t ω) =
      ∑ t ∈ range n, ((1 - Y t ω) - (adv (O t ω) m : α → ℝ) ⬝ᵥ Yh t ω) +
        ∑ t ∈ range n, ((adv (O t ω) m : α → ℝ) ⬝ᵥ Yh t ω -
          ∑ a, (adv (O t ω) m : α → ℝ) a * (1 - env.means O A Y a t ω)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    have hE := (mem_simplex_iff.1 (adv (O t ω) m).2).2
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hE]
    ring
  have h1 : ∑ t ∈ range n, ((adv (O t ω) m : α → ℝ) ⬝ᵥ Yh t ω -
      ∑ a, (adv (O t ω) m : α → ℝ) a * (1 - env.means O A Y a t ω)) <
      log (2 * M / δ) / (2 * γ (n - 1)) := by
    have := hgood1 m
    simp only [hE1_def, Set.mem_ofPred_eq, not_le, hlog1] at this
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have h2 := hgood2
  simp only [hE2_def, Set.mem_ofPred_eq, not_le, hlog2] at h2
  simp only [hYh] at hsplit h1 h2
  linarith

/-- **High-probability regret bound of Exp4-IX** [Neu15, Theorem 2]. Along a run of Exp4-IX with
`M ≥ 2` experts, the constant learning rate `η = √(2 log M / (n k))` and the implicit exploration
`γ = η / 2`, against any environment whose feedback at every round `t < n` is almost surely in
`[0, 1]`, for `n > 0` and `δ > 0`, the probability that the expert random regret is at least
`2 √(2 n k log M) + (√(n k / (2 log M)) + 1) log (2 / δ)` is at most `δ`, with `k` the number of
arms. [Neu15] states this bound with `√(2 n k / log M)` in place of `√(n k / (2 log M))`. -/
theorem measure_two_mul_sqrt_add_le_expertRandomRegret_le
    (h : IsAlgEnvSeq O A Y (exp4IX adv hadv
      (fun _ ↦ √(2 * log (Fintype.card β) / (n * Fintype.card α)))
      (fun _ ↦ √(2 * log (Fintype.card β) / (n * Fintype.card α)) / 2)) env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) (hM : 1 < Fintype.card β) (hn : 0 < n)
    (hδ : 0 < δ) :
    P {ω | 2 * √(2 * n * Fintype.card α * log (Fintype.card β)) +
        (√(n * Fintype.card α / (2 * log (Fintype.card β))) + 1) * log (2 / δ) ≤
        expertRandomRegret env (fun o m ↦ (adv o m : α → ℝ)) O A Y n ω} ≤ ENNReal.ofReal δ := by
  have := nonempty_arms P adv O
  set k : ℝ := (Fintype.card α : ℝ) with hk
  have hk0 : 0 < k := Nat.cast_pos.2 Fintype.card_pos
  set L : ℝ := log (Fintype.card β) with hL
  have hL0 : 0 < L := log_pos (by exact_mod_cast hM)
  set N : ℝ := n * k with hN
  have hN0 : 0 < N := mul_pos (Nat.cast_pos.2 hn) hk0
  set η₀ : ℝ := √(2 * L / N) with hη₀
  have hη₀0 : 0 < η₀ := sqrt_pos.2 (by positivity)
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_le_expertRandomRegret_le h hY (fun _ ↦ hη₀0) antitone_const
      (fun _ ↦ (half_pos hη₀0).le) antitone_const (half_pos hη₀0) (fun _ _ ↦ by linarith) hδ)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine le_trans (le_of_eq ?_) hω
  -- the bound of `measure_le_expertRandomRegret_le` is
  -- `(2 L + log (2 / δ)) / η₀ + N η₀ + log (2 / δ)`
  have hlog : log (2 * Fintype.card β / δ) = L + log (2 / δ) := by
    rw [hL, ← log_mul (by positivity) (by positivity)]
    congr 1
    ring
  have hbal : L / η₀ + η₀ * N / 2 = √(2 * N * L) := div_sqrt_add_sqrt_mul_div_two L hN0.le
  have hinv : 1 / η₀ = √(N / (2 * L)) := by rw [hη₀, one_div, ← sqrt_inv, inv_div]
  have hsq : √(2 * n * k * L) = √(2 * N * L) := by rw [hN]; ring_nf
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hlog]
  rw [hsq, ← hbal, ← hinv, hN]
  field_simp
  ring

/-- **High-probability regret bound of Exp3-IX with anytime rates** [Neu15, Theorem 1]. Along a run
of Exp3-IX, the instance of Exp4-IX with the experts `α` that each recommend one arm, with
`k ≥ 2` arms, the anytime learning rates `η t = √(log k / (k (t + 1)))` and the implicit
exploration `γ t = η t / 2`, against any environment whose feedback at every round `t < n` is
almost surely in `[0, 1]`, for `n > 0` and `δ > 0`, the probability that the random regret
`max_a ∑ t < n, (μ t a - Y t)` is at least `4 √(n k log k) + (√(n k / log k) + 1) log (2 / δ)` is
at most `δ`, with `μ t a = env.means O A Y a t` the conditional means of the rewards. The rates do
not depend on the horizon `n` nor on `δ`. [Neu15] states this bound with `2 √(n k / log k)` in
place of `√(n k / log k)`. -/
theorem measure_four_mul_sqrt_add_le_randomRegret_le [Nonempty α]
    (h : IsAlgEnvSeq O A Y (exp4IX (fun _ b ↦ ⟨Pi.single b 1, single_mem_simplex b⟩)
      measurable_const (fun t ↦ √(log (Fintype.card α) / (Fintype.card α * (t + 1))))
      (fun t ↦ √(log (Fintype.card α) / (Fintype.card α * (t + 1))) / 2)) env P)
    (hY : ∀ᵐ ω ∂P, ∀ t < n, Y t ω ∈ Set.Icc 0 1) (hk : 1 < Fintype.card α) (hn : 0 < n)
    (hδ : 0 < δ) :
    P {ω | 4 * √(n * Fintype.card α * log (Fintype.card α)) +
        (√(n * Fintype.card α / log (Fintype.card α)) + 1) * log (2 / δ) ≤
        randomRegret env O A Y n ω} ≤ ENNReal.ofReal δ := by
  set k : ℝ := (Fintype.card α : ℝ) with hk_def
  have hk0 : 0 < k := Nat.cast_pos.2 Fintype.card_pos
  set L : ℝ := log (Fintype.card α) with hL
  have hL0 : 0 < L := log_pos (by exact_mod_cast hk)
  set η : ℕ → ℝ := fun t ↦ √(L / (k * (t + 1))) with hη_def
  have hη : ∀ t, 0 < η t := fun t ↦ sqrt_pos.2 (by positivity)
  have hη_anti : Antitone η := fun s t hst ↦ by
    simp only [hη_def]
    gcongr
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_le_expertRandomRegret_le h hY hη hη_anti (fun t ↦ (half_pos (hη t)).le)
      (fun s t hst ↦ div_le_div_of_nonneg_right (hη_anti hst) zero_le_two) (half_pos (hη _))
      (fun t _ ↦ by linarith) hδ)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  -- with the experts that each recommend one arm, the expert random regret is the random regret
  have hR : expertRandomRegret env
      (fun o m ↦ ((⟨Pi.single m 1, single_mem_simplex m⟩ : simplex α) : α → ℝ)) O A Y n ω =
      randomRegret env O A Y n ω := expertRandomRegret_single
  rw [hR]
  refine le_trans ?_ hω
  -- the learning rate of the last round and the sum of the learning rates
  have hinv : 1 / η (n - 1) = √(n * k / L) := by
    simp only [hη_def]
    rw [Nat.cast_pred hn, sub_add_cancel, one_div, ← sqrt_inv, inv_div, mul_comm k]
  have hLη : L * √(n * k / L) = √(n * k * L) := mul_sqrt_div_eq_sqrt_mul _ hL0.le
  have hterm : ∀ t : ℕ, k * η t = √(L * k) * (√((t : ℝ) + 1))⁻¹ := fun t ↦ by
    simp only [hη_def]
    rw [← div_div, sqrt_div' _ (by positivity : (0 : ℝ) ≤ t + 1),
      ← mul_sqrt_div_eq_sqrt_mul L hk0.le]
    ring
  have hsum : k * ∑ t ∈ range n, (η t / 2 + η t / 2) ≤ 2 * √(n * k * L) := by
    calc k * ∑ t ∈ range n, (η t / 2 + η t / 2)
        = √(L * k) * ∑ t ∈ range n, (√((t : ℝ) + 1))⁻¹ := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ ↦ by rw [← hterm]; ring
      _ ≤ √(L * k) * (2 * √n) :=
          mul_le_mul_of_nonneg_left (sum_range_inv_sqrt_add_one_le n) (sqrt_nonneg _)
      _ = 2 * √(n * k * L) := by
          rw [mul_left_comm, ← sqrt_mul (by positivity)]
          ring_nf
  have hlog : log (2 * k / δ) = L + log (2 / δ) := by
    rw [hL, ← log_mul (by positivity) (by positivity)]
    congr 1
    ring
  have hη' := (hη (n - 1)).ne'
  rw [hlog]
  calc L / η (n - 1) + k * ∑ t ∈ range n, (η t / 2 + η t / 2) +
        (L + log (2 / δ)) / (2 * (η (n - 1) / 2)) + log (2 / δ)
      = 2 * (L * (1 / η (n - 1))) + k * ∑ t ∈ range n, (η t / 2 + η t / 2) +
        (1 / η (n - 1) + 1) * log (2 / δ) := by
        field_simp
        ring_nf
    _ ≤ 4 * √(n * k * L) + (√(n * k / L) + 1) * log (2 / δ) := by
        rw [hinv, hLη]
        linarith

end LMLExplore.Bandits.Exp4IX
