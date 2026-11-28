/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.ReinforcementLearning.QLearning.Synchronous
import LMLExplore.Analysis.Convex.Integral
import LMLExplore.MarkovDecisionProcess.MarkovPolicy
import LMLExplore.Probability.Kernel.Resolvent
import LMLExplore.Probability.Moments.Variance

/-!
# The upper bound on the error of synchronous Q-learning

The error `Δ t = Q t - Q*` of synchronous Q-learning satisfies the upper bound
`Δ (t + 1) ≤ (1 - η (t + 1)) Δ t + η (t + 1) γ (P^{π t} Δ t + (P_{t+1} - P) V t)`
[LCCWC24, (33a), (34)], where `π t` is greedy for the iterate `Q t`, `V t s = ⨆ a, Q t (s, a)`
and `P^π` is the state-action kernel of `π`. Unlike the lower bound
(`LMLExplore.ReinforcementLearning.QLearning.LowerBound`), the kernels `P^{π t}` change with the
iteration and depend on the samples, so the noise cannot be propagated along a fixed kernel. As in
[LCCWC24, Appendix B.2], the recursion is unrolled with the scalar learning-rate weights
`η^i_k = η i ∏_{j=i+1}^k (1 - η j)` over a window of `L` iterations, which gives
`Δ k ≤ ρ_k C / (1 - γ) + ξ k + ∑_{k - L ≤ i < k} η^{i+1}_k γ P^{π i} Δ i` with
`ρ_k = ∏_{j=k-L+1}^k (1 - η j)` and the windowed noise `ξ k = ∑_{k - L ≤ i < k} η^{i+1}_k γ
(P_{i+1} - P) V i`, a martingale sum with deterministic weights, controlled by Freedman's
inequality [LCCWC24, (39)].

The source then expands this inequality `H = log T / (1 - γ)` times and bounds the expansion with
[LCCWC24, Lemma 5]. Here the expansion is replaced by a comparison with an explicit supersolution
`u` of `b + γ P^{π i} u ≤ u`, valid simultaneously for all the greedy kernels of the window:
* if `x k ≤ b + ∑_{k - L ≤ i < k} w k i γ κ i (x i)` with weights summing to at most `1`, and
  `x ≤ u + c` on the iterations `m ≤ k ≤ t`, then `x k ≤ u + γ ^ j c` from the iteration
  `m + j L` on (`LMLExplore.ReinforcementLearning.le_add_pow_mul_of_le_add_sum_mul_integral`);
* if `w ≥ 0` is a supersolution for `b ^ 2`, then `√(w / (1 - γ))` is one for `b`
  (`ProbabilityTheory.Kernel.add_mul_integral_sqrt_le_sqrt`), and the Freedman bound `b` of the
  noise is the square root of a combination of the one-step variances `Var_P(V*)`;
* for every kernel `K` on pairs with `P (V* ^ 2) ≤ K (Q* ^ 2) + e`, such as the state-action
  kernel of a policy greedy for an iterate close to `Q*`, the function
  `(2 C ^ 2 / (1 - γ) + γ ^ 2 e) / (1 - γ) - Q* ^ 2` is a supersolution for `γ ^ 2 Var_P(V*)`
  (`LMLExplore.ReinforcementLearning.sq_mul_variance_optValue_add_mul_integral_le`), the
  telescoping argument of [LCCWC24, (97)–(98)] in closed form.

Together these bound `Δ t` from above with high probability, in terms of a bound `D` on the errors
of the window, as in [LCCWC24, Lemma 1].

## Main statements

* `LMLExplore.ReinforcementLearning.le_add_pow_mul_of_le_add_sum_mul_integral`: comparison of an
  averaged recursive inequality with a common supersolution, by generations of `L` iterations.
* `LMLExplore.ReinforcementLearning.sq_mul_variance_optValue_add_mul_integral_le`: the
  supersolution for the one-step variances of the optimal value along near-greedy kernels, a
  closed form of [LCCWC24, Lemma 5].
* `LMLExplore.ReinforcementLearning.syncQLearning_sub_optQValue_le_window`: the upper bound on the
  error unrolled over a window [LCCWC24, (38)–(39)].
* `LMLExplore.ReinforcementLearning.measure_exists_lt_syncQLearning_sub_optQValue_le`: the
  high-probability upper bound on the error of Q-learning, the core of [LCCWC24, Lemma 1].

## References

* [LCCWC24] G. Li, C. Cai, Y. Chen, Y. Wei and Y. Chi, *Is Q-learning minimax optimal? A tight
  sample complexity analysis*, Operations Research (2024), arXiv:2102.06548.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP Bandits
open scoped NNReal

namespace LMLExplore.ReinforcementLearning

/-! ### Comparison with a common supersolution -/

section Comparison

variable {α : Type*} {mα : MeasurableSpace α} {κ : ℕ → Kernel α α} [∀ i, IsMarkovKernel (κ i)]
  {x : ℕ → α → ℝ} {w : ℕ → ℕ → ℝ} {b u : α → ℝ} {γ c : ℝ} {m L t : ℕ}

/-- **Comparison with a common supersolution, by generations.** Let `L > 0`, let the functions
`x k` satisfy the averaged recursive inequality
`x k ≤ b + ∑_{k - L ≤ i < k} w k i γ κ i (x i)` for `m + L ≤ k ≤ t`, with nonnegative weights
adding up to at most `1`, and let `u ≥ 0` be a common supersolution, `b + γ κ i u ≤ u` for
`m ≤ i < t`. If `x k ≤ u + c` for `m ≤ k ≤ t`, with `c ≥ 0` and `γ ≥ 0`, then
`x k ≤ u + γ ^ j c` for `m + j L ≤ k ≤ t`: each generation of `L` iterations contracts the excess
over `u` by `γ`. -/
theorem le_add_pow_mul_of_le_add_sum_mul_integral (hγ : 0 ≤ γ) (hc : 0 ≤ c) (hu : ∀ y, 0 ≤ u y)
    (hL : 0 < L) (hxi : ∀ i y, Integrable (x i) (κ i y)) (hui : ∀ i y, Integrable u (κ i y))
    (hsup : ∀ i ∈ Ico m t, ∀ y, b y + γ * ∫ z, u z ∂(κ i y) ≤ u y)
    (hw : ∀ k ∈ Icc (m + L) t, ∀ i ∈ Ico (k - L) k, 0 ≤ w k i)
    (hw1 : ∀ k ∈ Icc (m + L) t, ∑ i ∈ Ico (k - L) k, w k i ≤ 1)
    (hx : ∀ k ∈ Icc (m + L) t, ∀ y,
      x k y ≤ b y + ∑ i ∈ Ico (k - L) k, w k i * (γ * ∫ z, x i z ∂(κ i y)))
    (hxc : ∀ k ∈ Icc m t, ∀ y, x k y ≤ u y + c) (j : ℕ) :
    ∀ k ∈ Icc (m + j * L) t, ∀ y, x k y ≤ u y + γ ^ j * c := by
  induction j with
  | zero => simpa using hxc
  | succ j ih =>
    intro k hk y
    obtain ⟨hk₁, hk₂⟩ := mem_Icc.1 hk
    have hjL : j * L + L = (j + 1) * L := by ring
    have hkL : k ∈ Icc (m + L) t := mem_Icc.2 ⟨by omega, hk₂⟩
    -- the window of `k` lies in the previous generation
    have hwin (i : ℕ) (hi : i ∈ Ico (k - L) k) : i ∈ Icc (m + j * L) t ∧ i ∈ Ico m t := by
      have := mem_Ico.1 hi
      exact ⟨mem_Icc.2 ⟨by omega, by omega⟩, mem_Ico.2 ⟨by omega, by omega⟩⟩
    -- `b ≤ u` at `y`, by the supersolution property at the last iteration of the window
    have hbu : b y ≤ u y := by
      have h₁ := hsup (k - 1) (hwin (k - 1) (mem_Ico.2 ⟨by omega, by omega⟩)).2 y
      have h₂ : 0 ≤ γ * ∫ z, u z ∂(κ (k - 1) y) := mul_nonneg hγ (integral_nonneg hu)
      linarith
    calc x k y ≤ b y + ∑ i ∈ Ico (k - L) k, w k i * (γ * ∫ z, x i z ∂(κ i y)) := hx k hkL y
      _ ≤ b y + ∑ i ∈ Ico (k - L) k, w k i * ((u y - b y) + γ ^ (j + 1) * c) := by
        gcongr with i hi
        · exact hw k hkL i hi
        · calc γ * ∫ z, x i z ∂(κ i y) ≤ γ * ∫ z, (u z + γ ^ j * c) ∂(κ i y) :=
                mul_le_mul_of_nonneg_left (integral_mono (hxi i y)
                  ((hui i y).add (integrable_const _)) fun z ↦ ih i (hwin i hi).1 z) hγ
            _ = γ * ∫ z, u z ∂(κ i y) + γ ^ (j + 1) * c := by
                rw [integral_add (hui i y) (integrable_const _), integral_const, probReal_univ,
                  one_smul]
                ring
            _ ≤ (u y - b y) + γ ^ (j + 1) * c := by linarith [hsup i (hwin i hi).2 y]
      _ = b y + (∑ i ∈ Ico (k - L) k, w k i) * ((u y - b y) + γ ^ (j + 1) * c) := by
        rw [sum_mul]
      _ ≤ b y + 1 * ((u y - b y) + γ ^ (j + 1) * c) := by
        gcongr
        exact hw1 k hkL
      _ = u y + γ ^ (j + 1) * c := by ring

end Comparison

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Finite 𝓢]
  [Nonempty 𝓢] [MeasurableSingletonClass 𝓢] [Finite 𝓐] [Nonempty 𝓐] [MeasurableSingletonClass 𝓐]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {η : ℕ → ℝ} {Q₀ : 𝓢 × 𝓐 → ℝ} {C : ℝ}

/-! ### The one-step variances of the optimal value along near-greedy kernels -/

/-- **A supersolution for the one-step variances of the optimal value** [LCCWC24, (97)–(98)].
With rewards in `[0, C]` and `γ < 1`, let `K` be a Markov kernel on the state-action pairs with
`P (V* ^ 2) ≤ K (Q* ^ 2) + e` at `p`, as for the state-action kernel of a policy `π` with
`V* ^ 2 ≤ Q* (·, π ·) ^ 2 + e`. Then `G - Q* ^ 2`, with
`G = (2 C ^ 2 / (1 - γ) + γ ^ 2 e) / (1 - γ)`, satisfies at `p` the supersolution inequality
`γ ^ 2 Var_P(V*) + γ K (G - Q* ^ 2) ≤ G - Q* ^ 2`. Since it holds for every such kernel at once,
for `e ≥ 0` the discounted sums of `γ ^ 2 Var_P(V*)` along any sequence of near-greedy kernels
are at most `G`: this is the content of [LCCWC24, Lemma 5], there obtained by telescoping along
each sequence. -/
theorem sq_mul_variance_optValue_add_mul_integral_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) {K : Kernel (𝓢 × 𝓐) (𝓢 × 𝓐)} [IsMarkovKernel K]
    {e : ℝ} {p : 𝓢 × 𝓐}
    (hK : ∫ s, M.optValue γ s ^ 2 ∂(M.P p) ≤ ∫ q, M.optQValue γ q ^ 2 ∂(K p) + e) :
    (γ : ℝ) ^ 2 * Var[M.optValue γ; M.P p] +
        γ * ∫ q, ((2 * (C / (1 - γ)) * C + γ ^ 2 * e) / (1 - γ) - M.optQValue γ q ^ 2) ∂(K p) ≤
      (2 * (C / (1 - γ)) * C + γ ^ 2 * e) / (1 - γ) - M.optQValue γ p ^ 2 := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  have hγ1 : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ.le
  have hRabs : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C := fun p ↦ (hR p).mono fun x hx ↦
    abs_le.2 ⟨by linarith [hx.1, hx.2], hx.2⟩
  have hr (q : 𝓢 × 𝓐) : meanReward M.R q ∈ Set.Icc 0 C := by
    rw [meanReward_def]
    exact integral_mem_Icc_of_ae_mem_Icc aemeasurable_id (hR q)
  have hQ₀ := optQValue_nonneg hγ hRabs (fun q ↦ (hr q).1) p
  have hQB := (le_abs_self _).trans (abs_optQValue_le hγ hRabs p)
  have hIK : 0 ≤ ∫ q, M.optQValue γ q ^ 2 ∂(K p) := integral_nonneg fun q ↦ sq_nonneg _
  set G := (2 * (C / (1 - γ)) * C + γ ^ 2 * e) / (1 - γ) with hG_def
  have hG : (1 - γ) * G = 2 * (C / (1 - γ)) * C + γ ^ 2 * e := by
    rw [hG_def]
    field_simp
  -- `Var_P(V*) = P (V* ^ 2) - (P V*) ^ 2` and the Bellman equation `Q* = r + γ P V*`
  rw [variance_eq_sub .of_discrete, integral_sub (integrable_const _) .of_finite, integral_const,
    probReal_univ, one_smul, optQValue_def (p := p)]
  simp only [Pi.pow_apply]
  have hQ := optQValue_def (M := M) (γ := γ) p
  rw [hQ] at hQ₀ hQB
  -- `P (V* ^ 2) ≤ K (Q* ^ 2) + e`, `γ ^ 2 K (Q* ^ 2) ≤ γ K (Q* ^ 2)` and `r Q* ≤ C ^ 2 / (1 - γ)`
  nlinarith [mul_le_mul_of_nonneg_left hK (sq_nonneg (γ : ℝ)),
    mul_nonneg (mul_nonneg γ.coe_nonneg (sub_nonneg.2 hγ1)) hIK,
    mul_le_mul (hr p).2 hQB hQ₀ ((hr p).1.trans (hr p).2), sq_nonneg (meanReward M.R p)]

/-! ### The windowed error recursion -/

/-- **The upper bound on the error unrolled over a window** [LCCWC24, (38)–(39)]. With rewards in
`[0, C]`, `γ < 1`, learning rates in `[0, 1]`, `0 ≤ Q₀ ≤ C / (1 - γ)` and policies `π i` greedy
for the iterates `Q i`, the error `Δ k = Q k - Q*` satisfies
`Δ k ≤ ρ_k C / (1 - γ) + ∑_{k - L ≤ i < k} η^{i+1}_k γ ((P_{i+1} - P) V i + P^{π i} Δ i)`, with
`ρ_k = ∏_{j=k-L+1}^k (1 - η j)`, the learning-rate weights `η^i_k = learningRateWeight η k i`, the
sampling noise `(P_{i+1} - P) V i p = V i (ω i p) - P V i p` of `V i s = ⨆ a, Q i (s, a)` and the
state-action kernel `P^{π i}` of `π i`. -/
theorem syncQLearning_sub_optQValue_le_window (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ))) {ω : ℕ → 𝓢 × 𝓐 → 𝓢} {π : ℕ → 𝓢 → 𝓐}
    (hπ : ∀ i s, syncQLearning (meanReward M.R) γ η Q₀ i ω (s, π i s) =
      ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (s, a)) (L k : ℕ) (p : 𝓢 × 𝓐) :
    syncQLearning (meanReward M.R) γ η Q₀ k ω p - M.optQValue γ p ≤
      (∏ j ∈ Ioc (k - L) k, (1 - η j)) * (C / (1 - γ)) +
        ∑ i ∈ Ico (k - L) k, γ * learningRateWeight η k (i + 1) *
          ((⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (ω i p, a)) -
            ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a) ∂(M.P p)) +
        ∑ i ∈ Ico (k - L) k, learningRateWeight η k (i + 1) * (γ *
          ∫ q, (syncQLearning (meanReward M.R) γ η Q₀ i ω q - M.optQValue γ q)
            ∂(M.saKernel (Kernel.deterministic (π i) (measurable_of_finite _)) p)) := by
  have hRabs : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C := fun p ↦ (hR p).mono fun x hx ↦
    abs_le.2 ⟨by linarith [hx.1, hx.2], hx.2⟩
  have h := le_prod_mul_add_sum_learningRateWeight_mul_of_le (n := k - L)
    (x := fun t ↦ syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p)
    (y := fun i ↦ γ *
      ((∫ s', (syncQLearning (meanReward M.R) γ η Q₀ (i - 1) ω (s', π (i - 1) s') -
          M.optQValue γ (s', π (i - 1) s')) ∂(M.P p)) +
        ((⨆ a, syncQLearning (meanReward M.R) γ η Q₀ (i - 1) ω (ω (i - 1) p, a)) -
          ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ (i - 1) ω (s', a) ∂(M.P p))))
    (fun t _ ↦ (hη t).2) (fun t _ ↦ by
      simpa only [Nat.add_sub_cancel, mul_assoc] using
        syncQLearning_succ_sub_optQValue_le hγ hRabs (hη t).1 (hπ t) p) (Nat.sub_le k L)
  -- the contracted error at `k - L` is at most `ρ_k C / (1 - γ)`
  have hρ : (∏ j ∈ Ioc (k - L) k, (1 - η j)) *
      (syncQLearning (meanReward M.R) γ η Q₀ (k - L) ω p - M.optQValue γ p) ≤
      (∏ j ∈ Ioc (k - L) k, (1 - η j)) * (C / (1 - γ)) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans
      (abs_syncQLearning_sub_optQValue_le hγ hR hη hQ₀ _ ω p))
      (prod_nonneg fun j hj ↦ sub_nonneg.2 (learningRate_mem_Icc_of_mem_Ioc hη hj).2)
  refine h.trans ?_
  rw [← Ico_add_one_add_one_eq_Ioc (k - L) k, ← sum_Ico_add', add_assoc, ← sum_add_distrib]
  refine add_le_add (by simpa only [Ico_add_one_add_one_eq_Ioc] using hρ) (le_of_eq ?_)
  refine sum_congr rfl fun i _ ↦ ?_
  rw [integral_saKernel_deterministic _ .of_finite, Nat.add_sub_cancel]
  ring

/-! ### The deterministic analysis on the event of the noise bounds -/

omit [Finite 𝓢] [MeasurableSingletonClass 𝓢] [MeasurableSingletonClass 𝓐] in
/-- For policies `π` greedy for `Q` within `D` of `Q*`, the value estimate `V s = ⨆ a, Q (s, a)` is
within `D` of `V*`, and `V* ^ 2 ≤ Q* (·, π ·) ^ 2 + 4 B D` with `B = C / (1 - γ)`. -/
private lemma abs_iSup_sub_optValue_le_and_sq_optValue_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) {Q : 𝓢 × 𝓐 → ℝ} {π : 𝓢 → 𝓐}
    (hπ : ∀ s, Q (s, π s) = ⨆ a, Q (s, a)) {D : ℝ} (hD : ∀ q, |Q q - M.optQValue γ q| ≤ D)
    (s : 𝓢) :
    |(⨆ a, Q (s, a)) - M.optValue γ s| ≤ D ∧
      M.optValue γ s ^ 2 ≤ M.optQValue γ (s, π s) ^ 2 + 4 * (C / (1 - γ)) * D := by
  have hRabs : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C := fun p ↦ (hR p).mono fun x hx ↦
    abs_le.2 ⟨by linarith [hx.1, hx.2], hx.2⟩
  have hr₀ (q : 𝓢 × 𝓐) : 0 ≤ meanReward M.R q := by
    rw [meanReward_def]
    exact integral_nonneg_of_ae ((hR q).mono fun x hx ↦ hx.1)
  have hV : |(⨆ a, Q (s, a)) - M.optValue γ s| ≤ D := by
    rw [← iSup_optQValue hγ hRabs s]
    exact abs_ciSup_sub_ciSup_le (Set.finite_range _).bddAbove fun a ↦ hD (s, a)
  refine ⟨hV, ?_⟩
  -- `0 ≤ Q* (s, π s) ≤ V* s ≤ B` and `V* s - Q* (s, π s) ≤ 2 D`
  have h₀ := optQValue_nonneg hγ hRabs hr₀ (s, π s)
  have h₁ := optQValue_le_optValue hγ hRabs s (π s)
  have h₂ := (le_abs_self _).trans (abs_optValue_le hγ hRabs s)
  have h₃ := (abs_sub_le_iff.1 (hD (s, π s))).1
  have h₄ := (abs_sub_le_iff.1 hV).2
  rw [← hπ s] at h₄
  nlinarith

/-- The weights `η^{i+1}_k` of the window `k - L ≤ i < k` add up to at most `1`, for learning
rates in `[0, 1]`. -/
private lemma sum_Ico_learningRateWeight_le_one (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (L k : ℕ) : ∑ i ∈ Ico (k - L) k, learningRateWeight η k (i + 1) ≤ 1 := by
  rw [sum_Ico_add' (fun i ↦ learningRateWeight η k i), Ico_add_one_add_one_eq_Ioc]
  exact sum_Ioc_learningRateWeight_le_one hη _ _

omit [MeasurableSingletonClass 𝓐] in
/-- **The quadratic variation of the windowed noise in terms of the errors** [LCCWC24, (71),
(95)]. If the weights of the window `k - L < i ≤ k` are at most `β ≥ 0` and the errors of its
iterations are at most `D ≥ 0`, then
`∑_{k - L ≤ i < k} (γ η^{i+1}_k) ^ 2 Var_P(V i) ≤ γ ^ 2 β (Var_P(V*) + 4 B D)` with
`B = C / (1 - γ)`: the one-step variances of the value estimates exceed those of `V*` by at most
`4 B D`. -/
private lemma sum_sq_mul_variance_iSup_syncQLearning_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ))) {β D : ℝ} (hβ₀ : 0 ≤ β) (hD₀ : 0 ≤ D) {L k : ℕ}
    (hβ : ∀ i ∈ Ioc (k - L) k, learningRateWeight η k i ≤ β) {ω : ℕ → 𝓢 × 𝓐 → 𝓢}
    (hD : ∀ i ∈ Ico (k - L) k, ∀ q,
      |syncQLearning (meanReward M.R) γ η Q₀ i ω q - M.optQValue γ q| ≤ D) (p : 𝓢 × 𝓐) :
    ∑ i ∈ Ico (k - L) k, (γ * learningRateWeight η k (i + 1)) ^ 2 *
        Var[fun s' ↦ ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a); M.P p] ≤
      γ ^ 2 * β * (Var[M.optValue γ; M.P p] + 4 * (C / (1 - γ)) * D) := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  have hRabs : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C := fun p ↦ (hR p).mono fun x hx ↦
    abs_le.2 ⟨by linarith [hx.1, hx.2], hx.2⟩
  have hr (q : 𝓢 × 𝓐) : meanReward M.R q ∈ Set.Icc 0 C := by
    rw [meanReward_def]
    exact integral_mem_Icc_of_ae_mem_Icc aemeasurable_id (hR q)
  have hB : C + γ * (C / (1 - γ)) ≤ C / (1 - γ) := by
    refine le_of_eq ?_
    field_simp
    ring
  have hB₀ : 0 ≤ C / (1 - γ) := div_nonneg ((hr p).1.trans (hr p).2) h1γ.le
  have hX : 0 ≤ γ ^ 2 * β * (Var[M.optValue γ; M.P p] + 4 * (C / (1 - γ)) * D) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hβ₀) (add_nonneg (variance_nonneg _ _)
      (mul_nonneg (mul_nonneg zero_le_four hB₀) hD₀))
  calc _ ≤ ∑ i ∈ Ico (k - L) k, learningRateWeight η k (i + 1) *
        (γ ^ 2 * β * (Var[M.optValue γ; M.P p] + 4 * (C / (1 - γ)) * D)) := by
        refine sum_le_sum fun i hi ↦ ?_
        have hw₀ : 0 ≤ learningRateWeight η k (i + 1) := learningRateWeight_nonneg (hη i).1
          fun j hj ↦ (learningRate_mem_Icc_of_mem_Ioc hη hj).2
        have hwβ := hβ (i + 1) (by simp only [mem_Ioc]; have := mem_Ico.1 hi; omega)
        have hVar := variance_le_variance_add_of_abs_sub_le (μ := M.P p)
          (measurable_of_finite (fun s' ↦ ⨆ a,
            syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a))).aemeasurable
          (measurable_of_finite (M.optValue γ)).aemeasurable
          (.of_forall fun s ↦ abs_ciSup_le fun a ↦ by
            have := syncQLearning_mem_Icc hη hr hQ₀ hB i ω (s, a)
            exact abs_le.2 ⟨by linarith [this.1, hB₀], this.2⟩)
          (.of_forall (abs_optValue_le hγ hRabs))
          (.of_forall fun s ↦ (abs_iSup_sub_optValue_le_and_sq_optValue_le hγ hR
            (fun s ↦ (exists_eq_ciSup_of_finite (f := fun a ↦
              syncQLearning (meanReward M.R) γ η Q₀ i ω (s, a))).choose_spec) (hD i hi) s).1)
        have hV₀ := variance_nonneg (fun s' ↦ ⨆ a,
          syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a)) (M.P p)
        calc (γ * learningRateWeight η k (i + 1)) ^ 2 * Var[fun s' ↦ ⨆ a,
              syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a); M.P p]
            = learningRateWeight η k (i + 1) * (γ ^ 2 * learningRateWeight η k (i + 1) *
                Var[fun s' ↦ ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a); M.P p]) := by
              ring
          _ ≤ _ := by gcongr
    _ ≤ 1 * (γ ^ 2 * β * (Var[M.optValue γ; M.P p] + 4 * (C / (1 - γ)) * D)) := by
        rw [← sum_mul]
        exact mul_le_mul_of_nonneg_right (sum_Ico_learningRateWeight_le_one hη L k) hX
    _ = _ := one_mul _

/-- The supersolution of the upper bound: with `B = C / (1 - γ)`, `a ≥ 0`, `β, ℓ, D ≥ 0` and a
Markov kernel `K` with `P (V* ^ 2) ≤ K (Q* ^ 2) + 4 B D` at `p`, the function
`w = A + 18 β ℓ (G - Q* ^ 2)`, with `A = (2 a ^ 2 + 72 β ℓ γ ^ 2 B D) / (1 - γ)` and
`G = (2 B C + 4 γ ^ 2 B D) / (1 - γ)`, is nonnegative and is a supersolution at `p` for the square
of `a + 3 √(γ ^ 2 β (Var_P(V*) + 4 B D) ℓ)`. -/
private lemma sq_add_mul_integral_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C)
    {K : Kernel (𝓢 × 𝓐) (𝓢 × 𝓐)} [IsMarkovKernel K] {a β ℓ D : ℝ} (hβ₀ : 0 ≤ β)
    (hℓ : 0 ≤ ℓ) (hD₀ : 0 ≤ D) {p : 𝓢 × 𝓐}
    (hK : ∫ s, M.optValue γ s ^ 2 ∂(M.P p) ≤
      ∫ q, M.optQValue γ q ^ 2 ∂(K p) + 4 * (C / (1 - γ)) * D) :
    (a + 3 * √(γ ^ 2 * β * (Var[M.optValue γ; M.P p] + 4 * (C / (1 - γ)) * D) * ℓ)) ^ 2 +
        γ * ∫ q, ((2 * a ^ 2 + 72 * β * ℓ * γ ^ 2 * (C / (1 - γ)) * D) / (1 - γ) +
          18 * β * ℓ * ((2 * (C / (1 - γ)) * C + γ ^ 2 * (4 * (C / (1 - γ)) * D)) / (1 - γ) -
            M.optQValue γ q ^ 2)) ∂(K p) ≤
      (2 * a ^ 2 + 72 * β * ℓ * γ ^ 2 * (C / (1 - γ)) * D) / (1 - γ) +
        18 * β * ℓ * ((2 * (C / (1 - γ)) * C + γ ^ 2 * (4 * (C / (1 - γ)) * D)) / (1 - γ) -
          M.optQValue γ p ^ 2) := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  have hC : 0 ≤ C := by
    obtain ⟨x, hx⟩ := (hR p).exists
    exact hx.1.trans hx.2
  have hσ := sq_mul_variance_optValue_add_mul_integral_le hγ hR hK
  set B := C / (1 - γ)
  set G := (2 * B * C + γ ^ 2 * (4 * B * D)) / (1 - γ)
  set A := (2 * a ^ 2 + 72 * β * ℓ * γ ^ 2 * B * D) / (1 - γ)
  have hA : (1 - γ) * A = 2 * a ^ 2 + 72 * β * ℓ * γ ^ 2 * B * D := by
    simp only [A]
    field_simp
  -- the square of the noise bound is at most `2 a ^ 2 + 18 γ ^ 2 β (Var_P(V*) + 4 B D) ℓ`
  have hv : 0 ≤ γ ^ 2 * β * (Var[M.optValue γ; M.P p] + 4 * B * D) * ℓ :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hβ₀)
      (add_nonneg (variance_nonneg _ _) (by positivity))) hℓ
  have hsq := Real.sq_sqrt hv
  have hb2 : (a + 3 * √(γ ^ 2 * β * (Var[M.optValue γ; M.P p] + 4 * B * D) * ℓ)) ^ 2 ≤
      2 * a ^ 2 + 18 * (γ ^ 2 * β * (Var[M.optValue γ; M.P p] + 4 * B * D) * ℓ) := by
    nlinarith [sq_nonneg (a - 3 * √(γ ^ 2 * β * (Var[M.optValue γ; M.P p] + 4 * B * D) * ℓ))]
  rw [integral_add (integrable_const _) (Integrable.of_finite.const_mul _), integral_const,
    probReal_univ, one_smul, integral_const_mul]
  have h18 : 0 ≤ 18 * β * ℓ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hσ h18]

omit [Finite 𝓢] [MeasurableSingletonClass 𝓢] [Finite 𝓐] [MeasurableSingletonClass 𝓐] in
/-- The supersolution of `LMLExplore.ReinforcementLearning.sq_add_mul_integral_le` is nonnegative,
and the square root of its quotient by `1 - γ` is at most
`√(2 a ^ 2 + 36 β ℓ B (C + 4 γ ^ 2 D)) / (1 - γ)`. -/
private lemma sqrt_supersolution_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C)
    {a β ℓ D : ℝ} (hβ₀ : 0 ≤ β) (hℓ : 0 ≤ ℓ) (hD₀ : 0 ≤ D) (p : 𝓢 × 𝓐) :
    0 ≤ (2 * a ^ 2 + 72 * β * ℓ * γ ^ 2 * (C / (1 - γ)) * D) / (1 - γ) +
        18 * β * ℓ * ((2 * (C / (1 - γ)) * C + γ ^ 2 * (4 * (C / (1 - γ)) * D)) / (1 - γ) -
          M.optQValue γ p ^ 2) ∧
      √(((2 * a ^ 2 + 72 * β * ℓ * γ ^ 2 * (C / (1 - γ)) * D) / (1 - γ) +
        18 * β * ℓ * ((2 * (C / (1 - γ)) * C + γ ^ 2 * (4 * (C / (1 - γ)) * D)) / (1 - γ) -
          M.optQValue γ p ^ 2)) / (1 - γ)) ≤
        √(2 * a ^ 2 + 36 * β * ℓ * (C / (1 - γ)) * (C + 4 * γ ^ 2 * D)) / (1 - γ) := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  have hRabs : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C := fun p ↦ (hR p).mono fun x hx ↦
    abs_le.2 ⟨by linarith [hx.1, hx.2], hx.2⟩
  have hC : 0 ≤ C := by
    obtain ⟨x, hx⟩ := (hR p).exists
    exact hx.1.trans hx.2
  have hQ := abs_le.1 (abs_optQValue_le hγ hRabs p)
  set B := C / (1 - γ) with hB
  have hB₀ : 0 ≤ B := div_nonneg hC h1γ.le
  have hBC : 2 * B ^ 2 = 2 * B * C / (1 - γ) := by
    rw [hB]
    field_simp
  -- `G - Q* ^ 2 ≥ 2 B ^ 2 - B ^ 2 ≥ 0`
  have hG : 0 ≤ (2 * B * C + γ ^ 2 * (4 * B * D)) / (1 - γ) - M.optQValue γ p ^ 2 := by
    have h₁ : 2 * B ^ 2 ≤ (2 * B * C + γ ^ 2 * (4 * B * D)) / (1 - γ) := by
      rw [hBC]
      gcongr
      exact le_add_of_nonneg_right (by positivity)
    nlinarith [sq_abs (M.optQValue γ p), abs_nonneg (M.optQValue γ p),
      mul_self_le_mul_self (abs_nonneg _) (abs_le.2 hQ)]
  have h18 : 0 ≤ 18 * β * ℓ := by positivity
  refine ⟨add_nonneg (div_nonneg (by positivity) h1γ.le) (mul_nonneg h18 hG), ?_⟩
  -- the supersolution is at most `A + 18 β ℓ G = (2 a ^ 2 + 36 β ℓ B (C + 4 γ ^ 2 D)) / (1 - γ)`
  have hAG : (2 * a ^ 2 + 72 * β * ℓ * γ ^ 2 * B * D) / (1 - γ) +
      18 * β * ℓ * ((2 * B * C + γ ^ 2 * (4 * B * D)) / (1 - γ)) =
      (2 * a ^ 2 + 36 * β * ℓ * B * (C + 4 * γ ^ 2 * D)) / (1 - γ) := by
    field_simp
    ring
  have h2 : (2 * a ^ 2 + 72 * β * ℓ * γ ^ 2 * B * D) / (1 - γ) +
      18 * β * ℓ * ((2 * B * C + γ ^ 2 * (4 * B * D)) / (1 - γ) - M.optQValue γ p ^ 2) ≤
      (2 * a ^ 2 + 36 * β * ℓ * B * (C + 4 * γ ^ 2 * D)) / (1 - γ) := by
    nlinarith [mul_nonneg h18 (sq_nonneg (M.optQValue γ p))]
  calc √(((2 * a ^ 2 + 72 * β * ℓ * γ ^ 2 * B * D) / (1 - γ) +
        18 * β * ℓ * ((2 * B * C + γ ^ 2 * (4 * B * D)) / (1 - γ) - M.optQValue γ p ^ 2)) /
          (1 - γ))
      ≤ √((2 * a ^ 2 + 36 * β * ℓ * B * (C + 4 * γ ^ 2 * D)) / (1 - γ) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [pow_two (1 - (γ : ℝ)), ← div_div]
        exact div_le_div_of_nonneg_right h2 h1γ.le
    _ = √(2 * a ^ 2 + 36 * β * ℓ * B * (C + 4 * γ ^ 2 * D)) / (1 - γ) := by
        rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq h1γ.le]

/-- **The upper bound on the error on the event of the noise bounds.** Under the assumptions of
`LMLExplore.ReinforcementLearning.measure_exists_lt_syncQLearning_sub_optQValue_le`, if the
errors of the iterates `m ≤ k < t` are at most `D` and the windowed noises
`ξ k p = ∑_{k - L ≤ i < k} γ η^{i+1}_k (P_{i+1} - P) V i p` are at most `3 √(W k p ℓ) + 2 b ℓ`
for `m + L ≤ k ≤ t`, with `W k p = ∑_{k - L ≤ i < k} (γ η^{i+1}_k) ^ 2 Var_P(V i) p`, then
`Δ t ≤ γ ^ J B + √(2 (ρ B + 2 b ℓ) ^ 2 + 36 β ℓ B (C + 4 γ ^ 2 D)) / (1 - γ)` with
`B = C / (1 - γ)`. -/
private lemma syncQLearning_sub_optQValue_le_of_noise_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ))) {b β ρ D ℓ : ℝ} (hℓ : 0 ≤ ℓ) {m L J t : ℕ}
    (hL : 0 < L) (hJ : m + J * L ≤ t)
    (hβ : ∀ k ∈ Icc (m + L) t, ∀ i ∈ Ioc (k - L) k, learningRateWeight η k i ≤ β)
    (hρ : ∀ k ∈ Icc (m + L) t, ∏ j ∈ Ioc (k - L) k, (1 - η j) ≤ ρ) {ω : ℕ → 𝓢 × 𝓐 → 𝓢}
    (hD : ∀ k ∈ Ico m t, ∀ q,
      |syncQLearning (meanReward M.R) γ η Q₀ k ω q - M.optQValue γ q| ≤ D)
    (hξ : ∀ k ∈ Icc (m + L) t, ∀ p,
      ∑ i ∈ Ico (k - L) k, γ * learningRateWeight η k (i + 1) *
          ((⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (ω i p, a)) -
            ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a) ∂(M.P p)) ≤
        3 * √((∑ i ∈ Ico (k - L) k, (γ * learningRateWeight η k (i + 1)) ^ 2 *
          Var[fun s' ↦ ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a); M.P p]) * ℓ) +
          2 * b * ℓ)
    (p : 𝓢 × 𝓐) :
    syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p ≤
      γ ^ J * (C / (1 - γ)) +
        √(2 * (ρ * (C / (1 - γ)) + 2 * b * ℓ) ^ 2 +
          36 * β * ℓ * (C / (1 - γ)) * (C + 4 * γ ^ 2 * D)) / (1 - γ) := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  have hRabs : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C := fun p ↦ (hR p).mono fun x hx ↦
    abs_le.2 ⟨by linarith [hx.1, hx.2], hx.2⟩
  have hr (q : 𝓢 × 𝓐) : meanReward M.R q ∈ Set.Icc 0 C := by
    rw [meanReward_def]
    exact integral_mem_Icc_of_ae_mem_Icc aemeasurable_id (hR q)
  have hC : 0 ≤ C := (hr p).1.trans (hr p).2
  have hB : C + γ * (C / (1 - γ)) ≤ C / (1 - γ) := by
    refine le_of_eq ?_
    field_simp
    ring
  rcases lt_or_ge t (m + L) with hmt | hmt
  · -- no window fits before `t`: then `J = 0`, and the bound is the range of the errors
    obtain rfl : J = 0 := by
      by_contra hJ0
      have : L ≤ J * L := Nat.le_mul_of_pos_left L (Nat.pos_of_ne_zero hJ0)
      omega
    rw [pow_zero, one_mul]
    exact le_add_of_le_of_nonneg ((le_abs_self _).trans
      (abs_syncQLearning_sub_optQValue_le hγ hR hη hQ₀ t ω p))
      (div_nonneg (Real.sqrt_nonneg _) h1γ.le)
  -- otherwise the weights of a window and the errors of its iterations give `β, D ≥ 0`
  have hβ₀ : 0 ≤ β := (learningRateWeight_nonneg
    (learningRate_mem_Icc_of_mem_Ioc hη (k := 0) (t := m + L) (by simp only [mem_Ioc]; omega)).1
    fun j hj ↦ (learningRate_mem_Icc_of_mem_Ioc hη hj).2).trans
      (hβ (m + L) (mem_Icc.2 ⟨le_rfl, hmt⟩) (m + L) (by simp only [mem_Ioc]; omega))
  have hD₀ : 0 ≤ D := (abs_nonneg _).trans (hD m (mem_Ico.2 ⟨le_rfl, by omega⟩) p)
  set B := C / (1 - γ) with hB_def
  have hB₀ : 0 ≤ B := div_nonneg hC h1γ.le
  set Q := fun k ↦ syncQLearning (meanReward M.R) γ η Q₀ k ω with hQ_def
  -- policies greedy for the iterates, and their state-action kernels
  choose π hπ using fun i s ↦ exists_eq_ciSup_of_finite (f := fun a ↦ Q i (s, a))
  set K := fun i ↦ M.saKernel (Kernel.deterministic (π i) (measurable_of_finite _)) with hK_def
  have hVD (i : ℕ) (hi : i ∈ Ico m t) (s : 𝓢) :=
    abs_iSup_sub_optValue_le_and_sq_optValue_le hγ hR (hπ i) (hD i hi) s
  -- the noise bound `b q = a + 3 √(γ ^ 2 β (Var_P(V*) + 4 B D) ℓ)`, uniform over the window
  set a := ρ * B + 2 * b * ℓ with ha_def
  set bf : 𝓢 × 𝓐 → ℝ := fun q ↦
    a + 3 * √(γ ^ 2 * β * (Var[M.optValue γ; M.P q] + 4 * B * D) * ℓ) with hbf
  -- its square has the supersolution `w`, for all the greedy kernels of the window
  set w : 𝓢 × 𝓐 → ℝ := fun q ↦ (2 * a ^ 2 + 72 * β * ℓ * γ ^ 2 * B * D) / (1 - γ) +
    18 * β * ℓ * ((2 * B * C + γ ^ 2 * (4 * B * D)) / (1 - γ) - M.optQValue γ q ^ 2) with hw
  have hw₀ (q : 𝓢 × 𝓐) : 0 ≤ w q := (sqrt_supersolution_le hγ hR hβ₀ hℓ hD₀ q).1
  have hsup (i : ℕ) (hi : i ∈ Ico m t) (q : 𝓢 × 𝓐) :
      bf q + γ * ∫ z, √(w z / (1 - γ)) ∂(K i q) ≤ √(w q / (1 - γ)) := by
    refine Kernel.add_mul_integral_sqrt_le_sqrt hγ hw₀ .of_finite ?_
    refine sq_add_mul_integral_le hγ hR hβ₀ hℓ hD₀ ?_
    rw [hK_def, integral_saKernel_deterministic _ .of_finite]
    refine (integral_mono .of_finite (Integrable.of_finite.add (integrable_const _))
      fun s ↦ (hVD i hi s).2).trans_eq ?_
    rw [Pi.add_def, integral_add .of_finite (integrable_const _), integral_const, probReal_univ,
      one_smul]
  -- the window recursion, with the noise bounded by `b`
  have hrec (k : ℕ) (hk : k ∈ Icc (m + L) t) (q : 𝓢 × 𝓐) :
      Q k q - M.optQValue γ q ≤ bf q + ∑ i ∈ Ico (k - L) k, learningRateWeight η k (i + 1) *
        (γ * ∫ z, (Q i z - M.optQValue γ z) ∂(K i q)) := by
    have h := syncQLearning_sub_optQValue_le_window hγ hR hη hQ₀ (hπ ·  ·) L k q
    have hwin (i : ℕ) (hi : i ∈ Ico (k - L) k) : i ∈ Ico m t := by
      have := mem_Ico.1 hi
      have := mem_Icc.1 hk
      exact mem_Ico.2 ⟨by omega, by omega⟩
    -- `W k q ≤ γ ^ 2 β (Var_P(V*) + 4 B D)`
    have hW := sum_sq_mul_variance_iSup_syncQLearning_le hγ hR hη hQ₀ hβ₀ hD₀ (hβ k hk)
      (fun i hi ↦ hD i (hwin i hi)) q
    have hξk := (hξ k hk q).trans (add_le_add_left (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_right hW hℓ)) zero_le_three) _)
    have hρk := mul_le_mul_of_nonneg_right (hρ k hk) hB₀
    simp only [hbf, ha_def]
    linarith
  -- the comparison with the supersolution `√(w / (1 - γ))`, by `J` generations of `L` iterations
  have hcomp := le_add_pow_mul_of_le_add_sum_mul_integral (κ := K)
    (x := fun k q ↦ Q k q - M.optQValue γ q) (w := fun k i ↦ learningRateWeight η k (i + 1))
    (b := bf) (u := fun q ↦ √(w q / (1 - γ))) (c := B) γ.coe_nonneg hB₀
    (fun q ↦ Real.sqrt_nonneg _) hL (fun _ _ ↦ .of_finite) (fun _ _ ↦ .of_finite) hsup
    (fun k _ i _ ↦ learningRateWeight_nonneg (hη i).1
      fun j hj ↦ (learningRate_mem_Icc_of_mem_Ioc hη hj).2)
    (fun k _ ↦ sum_Ico_learningRateWeight_le_one hη L k) hrec
    (fun k _ q ↦ ((le_abs_self _).trans
      (abs_syncQLearning_sub_optQValue_le hγ hR hη hQ₀ k ω q)).trans
        (le_add_of_nonneg_left (Real.sqrt_nonneg _))) J t (mem_Icc.2 ⟨hJ, le_rfl⟩) p
  have hu := (sqrt_supersolution_le hγ hR (a := a) hβ₀ hℓ hD₀ p).2
  simp only [hQ_def] at hcomp
  linarith

/-! ### The high-probability upper bound -/

omit [Nonempty 𝓢] [MeasurableSingletonClass 𝓐] in
/-- **Freedman's inequality for the windowed noise** [LCCWC24, (70)–(73)]. With rewards in
`[0, C]`, `γ < 1`, learning rates in `[0, 1]` and `0 ≤ Q₀ ≤ C / (1 - γ)`, let `k ≤ t`, let the
weights `η^i_k` of the window `k - L < i ≤ k` be at most `β`, and let `b > 0` with
`γ β C / (1 - γ) ≤ b`. Then for every pair `p`, with probability at least `1 - δ`, the windowed
noise `ξ k p = ∑_{k - L ≤ i < k} γ η^{i+1}_k (P_{i+1} - P) V i p` is at most
`3 √(W ℓ) + 2 b ℓ`, with `W = ∑_{k - L ≤ i < k} (γ η^{i+1}_k) ^ 2 Var_P(V i) p`,
`ℓ = max 1 (log (K / δ))` and `K = ⌈log₄ t⌉ + 1`. -/
private lemma measure_lt_sum_mul_iSup_syncQLearning_sub_integral_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ))) {δ b β : ℝ} (hδ : 0 < δ) (hb : 0 < b)
    {L k t : ℕ} (hkt : k ≤ t) (hβ : ∀ i ∈ Ioc (k - L) k, learningRateWeight η k i ≤ β)
    (hβb : γ * β * (C / (1 - γ)) ≤ b) (p : 𝓢 × 𝓐) :
    streamMeasure M.P {ω | 3 * √((∑ i ∈ Ico (k - L) k, (γ * learningRateWeight η k (i + 1)) ^ 2 *
          Var[fun s' ↦ ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a); M.P p]) *
          max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) +
        2 * b * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ)) <
      ∑ i ∈ Ico (k - L) k, γ * learningRateWeight η k (i + 1) *
        ((⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (ω i p, a)) -
          ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a) ∂(M.P p))} ≤
      ENNReal.ofReal δ := by
  classical
  have := Fintype.ofFinite 𝓢
  have := Fintype.ofFinite 𝓐
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  have hr (q : 𝓢 × 𝓐) : meanReward M.R q ∈ Set.Icc 0 C := by
    rw [meanReward_def]
    exact integral_mem_Icc_of_ae_mem_Icc aemeasurable_id (hR q)
  have hB : C + γ * (C / (1 - γ)) ≤ C / (1 - γ) := by
    refine le_of_eq ?_
    field_simp
    ring
  have hB₀ : 0 ≤ C / (1 - γ) := div_nonneg ((hr p).1.trans (hr p).2) h1γ.le
  -- the weight of the noise of iteration `i` at the pair `p`
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ i,
      c i = if i ∈ Ico (k - L) k then γ * learningRateWeight η k (i + 1) else 0 :=
    ⟨_, fun _ ↦ rfl⟩
  have hc₀ (i : ℕ) : 0 ≤ c i := by
    rw [hc i]
    split_ifs
    · exact mul_nonneg γ.coe_nonneg (learningRateWeight_nonneg (hη i).1
        fun j hj ↦ (learningRate_mem_Icc_of_mem_Ioc hη hj).2)
    · exact le_rfl
  have hsum (i : ℕ) (f : 𝓢 × 𝓐 → ℝ) :
      ∑ q, (if q = p then c i else 0) * f q = c i * f p := by
    simp
  have habs (i : ℕ) (q : 𝓢 × 𝓐) : |if q = p then c i else 0| = if q = p then c i else 0 := by
    split_ifs
    · exact abs_of_nonneg (hc₀ i)
    · exact abs_zero
  have hsum_abs (i : ℕ) : ∑ q, |if q = p then c i else 0| = c i := by
    simp_rw [habs]
    simp
  have hsub : Ico (k - L) k ⊆ range t := fun i hi ↦ mem_range.2 (by
    have := mem_Ico.1 hi
    omega)
  have h := measure_three_mul_sqrt_add_lt_sum_sum_mul_iSup_syncQLearning_le (P := M.P) hη hr hQ₀
    hB hδ hb t (fun i q ↦ if q = p then c i else 0) fun i _ ↦ by
      rw [hsum_abs, hc i]
      split_ifs with hi
      · have hw := hβ (i + 1) (by simp only [mem_Ioc]; have := mem_Ico.1 hi; omega)
        calc γ * learningRateWeight η k (i + 1) * (C / (1 - γ))
            ≤ γ * β * (C / (1 - γ)) := by gcongr
          _ ≤ b := hβb
      · simpa using hb.le
  refine (measure_mono fun ω hω ↦ ?_).trans h
  -- in these weights, the quadratic variation bound is `W` and the noise is `ξ k p`
  have hW : ∑ i ∈ range t, (∑ q, |if q = p then c i else 0|) * ∑ q,
      |if q = p then c i else 0| *
        Var[fun s' ↦ ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a); M.P q] =
      ∑ i ∈ Ico (k - L) k, (γ * learningRateWeight η k (i + 1)) ^ 2 *
        Var[fun s' ↦ ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a); M.P p] := by
    simp_rw [hsum_abs, habs, hsum]
    rw [← sum_subset hsub fun i _ hi ↦ ?_]
    · refine sum_congr rfl fun i hi ↦ ?_
      simp only [hc i, hi, ite_true]
      ring
    · simp [hc i, hi]
  have hN : ∑ i ∈ range t, ∑ q, (if q = p then c i else 0) *
      ((⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (ω i q, a)) -
        ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a) ∂(M.P q)) =
      ∑ i ∈ Ico (k - L) k, γ * learningRateWeight η k (i + 1) *
        ((⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (ω i p, a)) -
          ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a) ∂(M.P p)) := by
    simp_rw [hsum]
    rw [← sum_subset hsub fun i _ hi ↦ ?_]
    · exact sum_congr rfl fun i hi ↦ by simp only [hc i, hi, ite_true]
    · simp [hc i, hi]
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [hW, hN]
  exact hω

/-- **The high-probability upper bound on the error of synchronous Q-learning**, the core of
[LCCWC24, Lemma 1]. With rewards in `[0, C]`, `γ < 1`, learning rates in `[0, 1]` and
`0 ≤ Q₀ ≤ C / (1 - γ)`, write `B = C / (1 - γ)`. Let `L > 0` be the length of a window and
`m + J L ≤ t`, and for `m + L ≤ k ≤ t` let the learning-rate weights `η^i_k` of the window
`k - L < i ≤ k` be at most `β`, and the contraction `∏_{j=k-L+1}^k (1 - η j)` over the window be
at most `ρ`. Let `b > 0` with `γ β B ≤ b`, and let `D` be real. Then with probability at least
`1 - (t + 1 - m - L) S A δ`, with `S` and `A` the numbers of states and actions, either an
error `|Q k - Q*|` of the iterations `m ≤ k < t` exceeds `D`, or for every pair `p`,
`Q t p - Q* p ≤ γ ^ J B + √(2 (ρ B + 2 b ℓ) ^ 2 + 36 β ℓ B (C + 4 γ ^ 2 D)) / (1 - γ)`, with
`ℓ = max 1 (log (K / δ))` and `K = ⌈log₄ t⌉ + 1`.

With the learning rates of [LCCWC24, Theorem 2], `β` is of order `log⁴ T / ((1 - γ) T)`, and
after replacing `δ` by `δ / (S A T)` the second term is of order
`√(log⁴ T log (S A T log T / δ) (1 + D) / ((1 - γ) ^ 4 T))`, the bound of the source. The
source expands the upper bound `H = log T / (1 - γ)` times along the greedy kernels; here the
expansion is replaced by the comparison with a common supersolution
(`LMLExplore.ReinforcementLearning.le_add_pow_mul_of_le_add_sum_mul_integral`), and the bound
has no factor `1 / γ ^ 2`. -/
theorem measure_exists_lt_syncQLearning_sub_optQValue_le [Fintype 𝓢] [Fintype 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ))) {δ b β ρ D : ℝ} (hδ : 0 < δ) (hb : 0 < b)
    {m L J t : ℕ} (hL : 0 < L) (hJ : m + J * L ≤ t)
    (hβ : ∀ k ∈ Icc (m + L) t, ∀ i ∈ Ioc (k - L) k, learningRateWeight η k i ≤ β)
    (hβb : γ * β * (C / (1 - γ)) ≤ b)
    (hρ : ∀ k ∈ Icc (m + L) t, ∏ j ∈ Ioc (k - L) k, (1 - η j) ≤ ρ) :
    streamMeasure M.P {ω | (∀ k ∈ Ico m t, ∀ q,
        |syncQLearning (meanReward M.R) γ η Q₀ k ω q - M.optQValue γ q| ≤ D) ∧
      ∃ p, γ ^ J * (C / (1 - γ)) +
          √(2 * (ρ * (C / (1 - γ)) +
              2 * b * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) ^ 2 +
            36 * β * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ)) * (C / (1 - γ)) *
              (C + 4 * γ ^ 2 * D)) / (1 - γ) <
        syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p} ≤
      ENNReal.ofReal ((t + 1 - (m + L) : ℕ) * Fintype.card 𝓢 * Fintype.card 𝓐 * δ) := by
  set ℓ := max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))
  have hℓ : 0 ≤ ℓ := zero_le_one.trans (le_max_left _ _)
  -- the windowed noise exceeds its Freedman bound at some iteration and some pair
  set E : ℕ → 𝓢 × 𝓐 → Set (ℕ → 𝓢 × 𝓐 → 𝓢) := fun k p ↦ {ω |
    3 * √((∑ i ∈ Ico (k - L) k, (γ * learningRateWeight η k (i + 1)) ^ 2 *
        Var[fun s' ↦ ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a); M.P p]) * ℓ) +
      2 * b * ℓ <
    ∑ i ∈ Ico (k - L) k, γ * learningRateWeight η k (i + 1) *
      ((⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (ω i p, a)) -
        ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ i ω (s', a) ∂(M.P p))} with hE
  calc streamMeasure M.P _ ≤ streamMeasure M.P (⋃ k ∈ Icc (m + L) t, ⋃ p, E k p) := by
        refine measure_mono fun ω ⟨hD, p, hp⟩ ↦ ?_
        by_contra hω
        simp only [Set.mem_iUnion, not_exists, hE, Set.mem_ofPred_eq, not_lt] at hω
        exact (syncQLearning_sub_optQValue_le_of_noise_le hγ hR hη hQ₀ hℓ hL hJ hβ hρ hD
          (fun k hk p ↦ hω k hk p) p).not_gt hp
    _ ≤ ∑ k ∈ Icc (m + L) t, streamMeasure M.P (⋃ p, E k p) := measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Icc (m + L) t, ∑ p, streamMeasure M.P (E k p) :=
        sum_le_sum fun k _ ↦ measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k ∈ Icc (m + L) t, ∑ _p : 𝓢 × 𝓐, ENNReal.ofReal δ :=
        sum_le_sum fun k hk ↦ sum_le_sum fun p _ ↦
          measure_lt_sum_mul_iSup_syncQLearning_sub_integral_le hγ hR hη hQ₀ hδ hb
            (mem_Icc.1 hk).2 (hβ k hk) hβb p
    _ = ENNReal.ofReal ((t + 1 - (m + L) : ℕ) * Fintype.card 𝓢 * Fintype.card 𝓐 * δ) := by
        rw [sum_const, sum_const, card_univ, Fintype.card_prod, Nat.card_Icc, nsmul_eq_mul,
          nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        ring

end LMLExplore.ReinforcementLearning
