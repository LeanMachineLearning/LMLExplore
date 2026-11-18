/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.InformationTheory.KullbackLeibler.Finite
public import LMLExplore.MarkovDecisionProcess.Optimality
public import LMLExplore.MarkovDecisionProcess.PerformanceDifference
public import LMLExplore.ReinforcementLearning.PolicyOptimization.SoftmaxPolicy

/-!
# Natural policy gradient

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP on a countable state space with finitely many actions and bounded
rewards, let `0 ≤ γ < 1` and let `η > 0` be a step size. **Natural policy gradient** (NPG) with
the softmax parametrization and exact values [AKLM21, §5.3] starts from the uniform policy
`π_0` and updates, in every state, the policy by multiplicative weights on the advantage:
`π_{t+1} (a | s) = π_t (a | s) * exp (η * A^{π_t} (s, a) / (1 - γ)) / Z_t s`, where
`Z_t s = ∑ a, π_t (a | s) * exp (η * A^{π_t} (s, a) / (1 - γ))` [AKLM21, Lemma 5.1]. Here it is
defined by its parameters `θ_0 = 0`, `θ_{t+1} = θ_t + η / (1 - γ) * A^{π_t}`, with
`π_t = softmaxPolicy θ_t`; the multiplicative form is `softmax_npgParam_succ`.

The analysis of [AKLM21, Lemma 5.1, Theorem 5.3] is the one of exponential weights run in every
state on the advantages, glued together by the performance difference lemma
`Learning.MDP.integral_value_sub_integral_value`:
* by the Gibbs variational principle, `0 ≤ log Z_t s ≤ η / (1 - γ) * ∫ A^{π_t} (s, ·) dπ_{t+1} s`,
  and since the state marginal of an occupancy measure from `μ` dominates `(1 - γ) • μ`, the
  values increase: `(1 - γ) / η * ∫ log Z_t dμ ≤ ∫ v^{π_{t+1}} dμ - ∫ v^{π_t} dμ`
  for every initial law `μ`;
* for a comparison policy `π` with state occupancy measure `d` from the evaluation law `ρ`, the
  logarithms of the weights telescope, so that
  `∑ t < T, (∫ v^π dρ - ∫ v^{π_t} dρ) ≤ log |𝓐| / η + (1 - γ)⁻¹ ∑ t < T, ∫ log Z_t dd`, and the
  improvement bound at `μ = d` bounds the last sum by `C / (1 - γ)` for rewards in `[0, C]`.

Since the values increase, this gives the convergence rate
`∫ v* dρ - ∫ v^{π_T} dρ ≤ log |𝓐| / (η T) + 1 / ((1 - γ) ^ 2 T)` for rewards in `[0, 1]`, with
no dependence on the number of states, on distribution mismatch coefficients or on the step size
beyond the first term [AKLM21, Theorem 5.3].

## Main definitions

* `LMLExplore.ReinforcementLearning.npgParam M γ η t`: the parameters `θ_t` of the softmax
  policies of natural policy gradient with step `η`.
* `LMLExplore.ReinforcementLearning.npgLogPartition M γ η t s`: the logarithm `log Z_t s` of the
  normalization of the update at the state `s`.

## Main statements

* `LMLExplore.ReinforcementLearning.softmax_npgParam_zero`,
  `LMLExplore.ReinforcementLearning.softmax_npgParam_succ`: NPG starts from the uniform policy and
  updates it by multiplicative weights on the advantage.
* `LMLExplore.ReinforcementLearning.mul_integral_npgLogPartition_le`: the improvement lower bound
  [AKLM21, Lemma 5.1]; `LMLExplore.ReinforcementLearning.monotone_value_npg`: the values of the
  iterates increase.
* `LMLExplore.ReinforcementLearning.sum_integral_value_sub_integral_value_npg_le`: the cumulative
  suboptimality of the iterates against any stationary policy.
* `LMLExplore.ReinforcementLearning.integral_value_sub_le_integral_value_npg`,
  `LMLExplore.ReinforcementLearning.value_npg_ge`: global convergence of NPG at the rate `1 / T`
  [AKLM21, Theorem 5.3].

## References

* [A. Agarwal, S. M. Kakade, J. D. Lee and G. Mahajan, *On the theory of policy gradient methods:
  optimality, approximation, and distribution shift*, JMLR 22 (2021), arXiv:1908.00261][AKLM21],
  §5.3, Lemma 5.1, Theorem 5.3
* [S. M. Kakade, *A natural policy gradient*, NeurIPS 2001][Kak01]
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP LMLExplore.OnlineLearning
open Real (log exp)
open scoped NNReal

namespace LMLExplore.ReinforcementLearning

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Countable 𝓢]
  [MeasurableSingletonClass 𝓢] [Fintype 𝓐]

/-! ### The iterates -/

section Defs

variable (M : MDP 𝓢 𝓐 ℝ) (γ : ℝ≥0) (η : ℝ)

/-- The parameters of **natural policy gradient** with step `η` and exact advantages, from
`θ_0 = 0`: `θ_{t+1} (s, a) = θ_t (s, a) + η / (1 - γ) * A^{π_t} (s, a)`, where
`π_t = softmaxPolicy θ_t` is the `t`-th policy [AKLM21, §5.3]. -/
noncomputable def npgParam : ℕ → 𝓢 → 𝓐 → ℝ
  | 0 => 0
  | t + 1 => fun s a ↦ npgParam t s a +
      η / (1 - γ) * M.advantage γ (softmaxPolicy (npgParam t)) (s, a)

@[simp]
lemma npgParam_zero : npgParam M γ η 0 = 0 := by
  rw [npgParam]

lemma npgParam_succ (t : ℕ) :
    npgParam M γ η (t + 1) = fun s a ↦ npgParam M γ η t s a +
      η / (1 - γ) * M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a) := by
  rw [npgParam]

/-- The logarithm `log Z_t s` of the normalization
`Z_t s = ∑ a, π_t (a | s) * exp (η / (1 - γ) * A^{π_t} (s, a))` of the update of natural policy
gradient at the state `s` [AKLM21, Lemma 5.1]. -/
noncomputable def npgLogPartition (t : ℕ) (s : 𝓢) : ℝ :=
  log (∑ a, softmax (npgParam M γ η t s) a *
    exp (η / (1 - γ) * M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a)))

lemma npgLogPartition_def (t : ℕ) (s : 𝓢) :
    npgLogPartition M γ η t s = log (∑ a, softmax (npgParam M γ η t s) a *
      exp (η / (1 - γ) * M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a))) := (rfl)

end Defs

variable {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {η C : ℝ}

/-- Natural policy gradient starts from the uniform policy. -/
lemma softmax_npgParam_zero (s : 𝓢) :
    softmax (npgParam M γ η 0 s) = fun _ ↦ (Fintype.card 𝓐 : ℝ)⁻¹ := by
  simp

variable [Nonempty 𝓐]

/-- **The policy form of natural policy gradient** [AKLM21, Lemma 5.1]: the policy `π_{t+1}` is
the multiplicative-weights update of `π_t` on the advantage `η / (1 - γ) * A^{π_t}`,
`π_{t+1} (a | s) = π_t (a | s) * exp (η / (1 - γ) * A^{π_t} (s, a)) / Z_t s`. -/
theorem softmax_npgParam_succ (t : ℕ) (s : 𝓢) (a : 𝓐) :
    softmax (npgParam M γ η (t + 1) s) a = softmax (npgParam M γ η t s) a *
        exp (η / (1 - γ) * M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a)) /
      ∑ b, softmax (npgParam M γ η t s) b *
        exp (η / (1 - γ) * M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, b)) := by
  rw [npgParam_succ]
  exact softmax_add_apply _ _ a

/-- The logarithms of the probabilities of natural policy gradient: `log π_{t+1} (a | s)` is
`log π_t (a | s) + η / (1 - γ) * A^{π_t} (s, a) - log Z_t s`. -/
theorem log_softmax_npgParam_succ (t : ℕ) (s : 𝓢) (a : 𝓐) :
    log (softmax (npgParam M γ η (t + 1) s) a) = log (softmax (npgParam M γ η t s) a) +
      η / (1 - γ) * M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a) -
        npgLogPartition M γ η t s := by
  have hZ : 0 < ∑ b, softmax (npgParam M γ η t s) b *
      exp (η / (1 - γ) * M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, b)) :=
    sum_pos (fun b _ ↦ mul_pos (softmax_pos _ b) (Real.exp_pos _)) univ_nonempty
  rw [softmax_npgParam_succ, Real.log_div (mul_pos (softmax_pos _ a) (Real.exp_pos _)).ne' hZ.ne',
    Real.log_mul (softmax_pos _ a).ne' (Real.exp_pos _).ne', Real.log_exp, npgLogPartition_def]

/-! ### The update in one state -/

section OneState

variable [MeasurableSingletonClass 𝓐] (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
include hγ hR

/-- The advantage of `π_t` has mean zero under `π_t`. -/
private lemma sum_softmax_npgParam_mul_advantage (t : ℕ) (s : 𝓢) :
    ∑ a, softmax (npgParam M γ η t s) a *
      M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a) = 0 := by
  have h := integral_advantage (π := softmaxPolicy (npgParam M γ η t)) hγ hR s
  rw [integral_softmaxPolicy] at h
  simpa using h

/-- The logarithm of the normalization of natural policy gradient is nonnegative: by Jensen's
inequality, `log Z_t s` is at least the mean `η / (1 - γ) * ∫ A^{π_t} (s, ·) dπ_t s = 0`. -/
theorem npgLogPartition_nonneg (t : ℕ) (s : 𝓢) : 0 ≤ npgLogPartition M γ η t s := by
  have h := sum_mul_sub_sum_mul_log_div_le_log_sum_mul_exp
    (softmax_mem_simplex (npgParam M γ η t s)) (softmax_mem_simplex _) (fun _ h ↦ h)
    (fun a ↦ η / (1 - γ) * M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a))
  simp_rw [div_self (softmax_pos _ _).ne', Real.log_one, mul_zero, sum_const_zero, sub_zero,
    mul_left_comm _ (η / (1 - γ) : ℝ), ← mul_sum, sum_softmax_npgParam_mul_advantage hγ hR,
    mul_zero] at h
  rwa [npgLogPartition_def]

omit hγ hR in
/-- The logarithm of the normalization of natural policy gradient is at most the average advantage
of the new policy: `log Z_t s ≤ η / (1 - γ) * ∫ A^{π_t} (s, ·) dπ_{t+1} s`. This is Gibbs'
inequality for `π_{t+1} s` with respect to `π_t s`. -/
theorem npgLogPartition_le_mul_integral_advantage (t : ℕ) (s : 𝓢) :
    npgLogPartition M γ η t s ≤ η / (1 - γ) *
      ∫ a, M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a)
        ∂(softmaxPolicy (npgParam M γ η (t + 1)) s) := by
  have h := sum_mul_log_div_nonneg (softmax_nonneg (npgParam M γ η (t + 1) s))
    (softmax_nonneg (npgParam M γ η t s)) (fun a h ↦ absurd h (softmax_pos _ a).ne') (by simp)
  have h_log (a : 𝓐) : log (softmax (npgParam M γ η (t + 1) s) a / softmax (npgParam M γ η t s) a) =
      η / (1 - γ) * M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a) -
        npgLogPartition M γ η t s := by
    rw [Real.log_div (softmax_pos _ a).ne' (softmax_pos _ a).ne', log_softmax_npgParam_succ]
    ring
  simp_rw [h_log, mul_sub, sum_sub_distrib, ← sum_mul, sum_softmax, one_mul,
    mul_left_comm _ (η / (1 - γ) : ℝ), ← mul_sum] at h
  rw [integral_softmaxPolicy]
  simpa using h

omit hγ hR in
/-- **Mirror-descent identity** of natural policy gradient: for every probability measure `ν` on
the actions, `η / (1 - γ) * ∫ A^{π_t} (s, ·) dν` is the increase
`∫ log π_{t+1} (· | s) dν - ∫ log π_t (· | s) dν` plus `log Z_t s`. -/
private lemma mul_integral_advantage_eq (t : ℕ) (s : 𝓢) (ν : Measure 𝓐) [IsProbabilityMeasure ν] :
    η / (1 - γ) * ∫ a, M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a) ∂ν =
      ∫ a, (log (softmax (npgParam M γ η (t + 1) s) a) - log (softmax (npgParam M γ η t s) a)) ∂ν +
        npgLogPartition M γ η t s := by
  have h (a : 𝓐) : log (softmax (npgParam M γ η (t + 1) s) a) -
      log (softmax (npgParam M γ η t s) a) =
        η / (1 - γ) * M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a) -
          npgLogPartition M γ η t s := by
    rw [log_softmax_npgParam_succ]
    ring
  simp_rw [h]
  rw [integral_sub (Integrable.of_finite.const_mul _) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul, sub_add_cancel]

omit hγ hR in
/-- Summed over the rounds, the mirror-descent identities telescope: for every probability measure
`ν` on the actions, `η / (1 - γ) * ∑ t < T, ∫ A^{π_t} (s, ·) dν ≤ log |𝓐| + ∑ t < T, log Z_t s`. -/
private lemma mul_sum_integral_advantage_le (s : 𝓢) (ν : Measure 𝓐) [IsProbabilityMeasure ν]
    (T : ℕ) :
    η / (1 - γ) * ∑ t ∈ range T, ∫ a, M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a) ∂ν ≤
      log (Fintype.card 𝓐) + ∑ t ∈ range T, npgLogPartition M γ η t s := by
  simp_rw [mul_sum, mul_integral_advantage_eq _ s ν, sum_add_distrib]
  gcongr
  rw [← integral_finsetSum _ fun _ _ ↦ Integrable.of_finite]
  have h_tel (a : 𝓐) : ∑ t ∈ range T, (log (softmax (npgParam M γ η (t + 1) s) a) -
      log (softmax (npgParam M γ η t s) a)) =
        log (softmax (npgParam M γ η T s) a) - log (softmax (npgParam M γ η 0 s) a) :=
    sum_range_sub (fun t ↦ log (softmax (npgParam M γ η t s) a)) T
  simp_rw [h_tel, softmax_npgParam_zero, Real.log_inv]
  -- `log π_T (a | s) ≤ 0`
  refine (integral_mono Integrable.of_finite (integrable_const _) fun a ↦ ?_).trans_eq
    (by rw [integral_const, probReal_univ, one_smul])
  have h := Real.log_nonpos (softmax_nonneg (npgParam M γ η T s) a)
    ((simplex_subset_Icc (softmax_mem_simplex _)).2 a)
  dsimp only
  linarith

end OneState

/-! ### Improvement and convergence -/

variable [MeasurableSingletonClass 𝓐] [Nonempty 𝓢] (hγ : γ < 1)
  (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hη : 0 < η)
include hγ hR hη

omit [Nonempty 𝓢] in
/-- The logarithm of the normalization is integrable, since
`0 ≤ log Z_t s ≤ η / (1 - γ) * (2 * C / (1 - γ))`. -/
private lemma integrable_npgLogPartition (t : ℕ) (μ : Measure 𝓢) [IsFiniteMeasure μ] :
    Integrable (npgLogPartition M γ η t) μ := by
  have h1γ : 0 < (1 - γ : ℝ) := sub_pos.2 (by exact_mod_cast hγ)
  refine integrable_of_abs_le (B := η / (1 - γ) * (2 * C / (1 - γ))) (measurable_of_countable _)
    (fun s ↦ ?_) μ
  rw [abs_of_nonneg (npgLogPartition_nonneg hγ hR t s)]
  refine (npgLogPartition_le_mul_integral_advantage t s).trans ?_
  gcongr
  exact (le_abs_self _).trans (abs_integral_le_of_abs_le fun _ ↦ abs_advantage_le hγ hR _)

omit [MeasurableSingletonClass 𝓐] [Nonempty 𝓢] hη in
/-- The average advantage `s ↦ ∫ A^{π_t} (s, ·) dπ s` is integrable. -/
private lemma integrable_integral_advantage (t : ℕ) (π : Kernel 𝓢 𝓐) [IsMarkovKernel π]
    (μ : Measure 𝓢) [IsFiniteMeasure μ] :
    Integrable (fun s ↦ ∫ a, M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a) ∂(π s)) μ :=
  integrable_of_abs_le (measurable_of_countable _)
    (fun _ ↦ abs_integral_le_of_abs_le fun _ ↦ abs_advantage_le hγ hR _) μ

/-- **Improvement lower bound for natural policy gradient** [AKLM21, Lemma 5.1]: for every initial
law `μ`, `(1 - γ) / η * ∫ log Z_t dμ ≤ ∫ v^{π_{t+1}} dμ - ∫ v^{π_t} dμ`. Since `log Z_t ≥ 0`
(`npgLogPartition_nonneg`), the values of the iterates increase. -/
theorem mul_integral_npgLogPartition_le (t : ℕ) (μ : Measure 𝓢) [IsProbabilityMeasure μ] :
    (1 - γ) / η * ∫ s, npgLogPartition M γ η t s ∂μ ≤
      ∫ s, M.value γ (softmaxPolicy (npgParam M γ η (t + 1))) s ∂μ -
        ∫ s, M.value γ (softmaxPolicy (npgParam M γ η t)) s ∂μ := by
  have h1γ : 0 < (1 - γ : ℝ) := sub_pos.2 (by exact_mod_cast hγ)
  set d := (M.occupancy γ (Algorithm.markov fun _ ↦ softmaxPolicy (npgParam M γ η (t + 1))) μ).fst
  rw [integral_value_sub_integral_value hγ hR]
  -- the state marginal `d` of the occupancy measure of `π_{t+1}` dominates `(1 - γ) • μ`
  have h_dom : (1 - γ) * ∫ s, npgLogPartition M γ η t s ∂μ ≤
      ∫ s, npgLogPartition M γ η t s ∂d := by
    have h := integral_mono_measure smul_le_occupancy_fst
      (ae_of_all _ (npgLogPartition_nonneg hγ hR t)) (integrable_npgLogPartition hγ hR hη t d)
    rwa [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, NNReal.coe_sub hγ.le,
      NNReal.coe_one] at h
  -- in every state, `log Z_t ≤ η / (1 - γ) * ∫ A^{π_t} dπ_{t+1}`
  have h_state : ∫ s, npgLogPartition M γ η t s ∂d ≤ η / (1 - γ) *
      ∫ s, ∫ a, M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a)
        ∂(softmaxPolicy (npgParam M γ η (t + 1)) s) ∂d := by
    rw [← integral_const_mul]
    exact integral_mono (integrable_npgLogPartition hγ hR hη t d)
      ((integrable_integral_advantage hγ hR t _ d).const_mul _)
      (npgLogPartition_le_mul_integral_advantage t)
  calc (1 - γ) / η * ∫ s, npgLogPartition M γ η t s ∂μ
      = ((1 - γ) * ∫ s, npgLogPartition M γ η t s ∂μ) / η := by ring
    _ ≤ (η / (1 - γ) * ∫ s, ∫ a, M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a)
        ∂(softmaxPolicy (npgParam M γ η (t + 1)) s) ∂d) / η :=
        div_le_div_of_nonneg_right (h_dom.trans h_state) hη.le
    _ = (1 - γ : ℝ)⁻¹ * ∫ s, ∫ a, M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a)
        ∂(softmaxPolicy (npgParam M γ η (t + 1)) s) ∂d := by field_simp

/-- **The values of natural policy gradient increase**: in every state `s`, `t ↦ v^{π_t} s` is
monotone. -/
theorem monotone_value_npg (s : 𝓢) :
    Monotone fun t ↦ M.value γ (softmaxPolicy (npgParam M γ η t)) s := by
  refine monotone_nat_of_le_succ fun t ↦ ?_
  have h := mul_integral_npgLogPartition_le hγ hR hη t (Measure.dirac s)
  simp only [integral_dirac] at h
  have : 0 ≤ (1 - γ : ℝ) / η * npgLogPartition M γ η t s :=
    mul_nonneg (div_nonneg (sub_nonneg.2 (by exact_mod_cast hγ.le)) hη.le)
      (npgLogPartition_nonneg hγ hR t s)
  linarith

/-- With bounded nonnegative mean rewards, the logarithms of the normalizations of natural policy
gradient have bounded sums: `∑ t < T, ∫ log Z_t dμ ≤ η / (1 - γ) * C / (1 - γ)`. -/
private lemma sum_integral_npgLogPartition_le (hr : ∀ p, 0 ≤ meanReward M.R p) (T : ℕ)
    (μ : Measure 𝓢) [IsProbabilityMeasure μ] :
    ∑ t ∈ range T, ∫ s, npgLogPartition M γ η t s ∂μ ≤ η / (1 - γ) * (C / (1 - γ)) := by
  have h1γ : 0 < (1 - γ : ℝ) := sub_pos.2 (by exact_mod_cast hγ)
  -- each term is at most `η / (1 - γ)` times the increase of the value, which telescopes
  have h_le (t : ℕ) : ∫ s, npgLogPartition M γ η t s ∂μ ≤ η / (1 - γ) *
      (∫ s, M.value γ (softmaxPolicy (npgParam M γ η (t + 1))) s ∂μ -
        ∫ s, M.value γ (softmaxPolicy (npgParam M γ η t)) s ∂μ) := by
    have h := mul_integral_npgLogPartition_le hγ hR hη t μ
    rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ h1γ]
    linarith
  refine (sum_le_sum fun t _ ↦ h_le t).trans ?_
  rw [← mul_sum, sum_range_sub (fun t ↦ ∫ s, M.value γ (softmaxPolicy (npgParam M γ η t)) s ∂μ)]
  gcongr
  have h_T := integral_mono (integrable_of_abs_le (measurable_value hγ hR) (abs_value_le hγ hR) μ)
    (integrable_const _) fun s ↦ (le_abs_self _).trans
      (abs_value_le (π := softmaxPolicy (npgParam M γ η T)) hγ hR s)
  have h_0 := integral_nonneg (μ := μ) (f := M.value γ (softmaxPolicy (npgParam M γ η 0)))
    fun s ↦ value_nonneg hγ hR hr s
  rw [integral_const, probReal_univ, one_smul] at h_T
  linarith

/-- **Cumulative suboptimality of natural policy gradient** [AKLM21, proof of Theorem 5.3]: with
rewards bounded by `C` with nonnegative means, for every stationary policy `π` and evaluation law
`ρ`, `∑ t < T, (∫ v^π dρ - ∫ v^{π_t} dρ) ≤ log |𝓐| / η + C / (1 - γ) ^ 2`. -/
theorem sum_integral_value_sub_integral_value_npg_le (hr : ∀ p, 0 ≤ meanReward M.R p)
    (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] (ρ : Measure 𝓢) [IsProbabilityMeasure ρ] (T : ℕ) :
    ∑ t ∈ range T, (∫ s, M.value γ π s ∂ρ -
        ∫ s, M.value γ (softmaxPolicy (npgParam M γ η t)) s ∂ρ) ≤
      log (Fintype.card 𝓐) / η + C / (1 - γ) ^ 2 := by
  have h1γ : 0 < (1 - γ : ℝ) := sub_pos.2 (by exact_mod_cast hγ)
  have := isProbabilityMeasure_occupancy (M := M) (alg := Algorithm.markov fun _ ↦ π) (μ := ρ) hγ
  set d := (M.occupancy γ (Algorithm.markov fun _ ↦ π) ρ).fst
  -- the performance difference lemma against `π`, with the advantages of the iterates
  simp_rw [integral_value_sub_integral_value hγ hR _ π, ← mul_sum]
  rw [← integral_finsetSum _ fun t _ ↦ integrable_integral_advantage hγ hR t π d]
  -- in every state, the mirror-descent identities telescope
  have h_tel : η / (1 - γ) * ∫ s, ∑ t ∈ range T,
      ∫ a, M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a) ∂(π s) ∂d ≤
        log (Fintype.card 𝓐) + ∑ t ∈ range T, ∫ s, npgLogPartition M γ η t s ∂d := by
    rw [← integral_const_mul, ← integral_finsetSum _
      fun t _ ↦ integrable_npgLogPartition hγ hR hη t d]
    refine (integral_mono ((integrable_finsetSum _
        fun t _ ↦ integrable_integral_advantage hγ hR t π d).const_mul _)
      ((integrable_const _).add (integrable_finsetSum _
        fun t _ ↦ integrable_npgLogPartition hγ hR hη t d))
      fun s ↦ mul_sum_integral_advantage_le s (π s) T).trans_eq ?_
    rw [integral_add' (integrable_const _) (integrable_finsetSum _
        fun t _ ↦ integrable_npgLogPartition hγ hR hη t d), integral_const, probReal_univ,
      one_smul]
  have h_sum := sum_integral_npgLogPartition_le hγ hR hη hr T d
  -- multiply by `(1 - γ)⁻¹ = (η / (1 - γ)) / η`
  calc (1 - γ : ℝ)⁻¹ * ∫ s, ∑ t ∈ range T,
        ∫ a, M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a) ∂(π s) ∂d
      = (η / (1 - γ) * ∫ s, ∑ t ∈ range T,
        ∫ a, M.advantage γ (softmaxPolicy (npgParam M γ η t)) (s, a) ∂(π s) ∂d) / η := by
        field_simp
    _ ≤ (log (Fintype.card 𝓐) + η / (1 - γ) * (C / (1 - γ))) / η :=
        div_le_div_of_nonneg_right (h_tel.trans (by linarith)) hη.le
    _ = log (Fintype.card 𝓐) / η + C / (1 - γ) ^ 2 := by
        field_simp

/-- **Global convergence of natural policy gradient** against a stationary policy
[AKLM21, Theorem 5.3]: with rewards bounded by `C` with nonnegative means, for every stationary
policy `π`, evaluation law `ρ` and `T > 0`,
`∫ v^π dρ - log |𝓐| / (η T) - C / ((1 - γ) ^ 2 T) ≤ ∫ v^{π_T} dρ`. -/
theorem integral_value_sub_le_integral_value_npg (hr : ∀ p, 0 ≤ meanReward M.R p)
    (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] (ρ : Measure 𝓢) [IsProbabilityMeasure ρ] {T : ℕ}
    (hT : 0 < T) :
    ∫ s, M.value γ π s ∂ρ - log (Fintype.card 𝓐) / (η * T) - C / ((1 - γ) ^ 2 * T) ≤
      ∫ s, M.value γ (softmaxPolicy (npgParam M γ η T)) s ∂ρ := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have h_int (t : ℕ) : Integrable (M.value γ (softmaxPolicy (npgParam M γ η t))) ρ :=
    integrable_of_abs_le (measurable_value hγ hR) (abs_value_le hγ hR) ρ
  -- the last iterate is the best one, so `T` times its suboptimality is at most the sum
  have h_mono : (T : ℝ) * (∫ s, M.value γ π s ∂ρ -
      ∫ s, M.value γ (softmaxPolicy (npgParam M γ η T)) s ∂ρ) ≤
        ∑ t ∈ range T, (∫ s, M.value γ π s ∂ρ -
          ∫ s, M.value γ (softmaxPolicy (npgParam M γ η t)) s ∂ρ) := by
    have h_card (x : ℝ) : (T : ℝ) * x = ∑ _t ∈ range T, x := by simp
    rw [h_card]
    exact sum_le_sum fun t ht ↦ sub_le_sub_left (integral_mono (h_int t) (h_int T) fun s ↦
      monotone_value_npg hγ hR hη s (mem_range.1 ht).le) _
  have h := h_mono.trans (sum_integral_value_sub_integral_value_npg_le hγ hR hη hr π ρ T)
  rw [div_mul_eq_div_div, div_mul_eq_div_div, sub_sub, ← add_div, sub_le_comm, le_div_iff₀ hT']
  linarith

omit hR in
/-- **Global convergence of natural policy gradient** [AKLM21, Theorem 5.3]: with rewards in
`[0, 1]`, for every evaluation law `ρ` and `T > 0`, the `T`-th iterate of natural policy gradient
with step `η > 0` satisfies
`∫ v* dρ - log |𝓐| / (η T) - 1 / ((1 - γ) ^ 2 T) ≤ ∫ v^{π_T} dρ`. -/
theorem value_npg_ge (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 1) (ρ : Measure 𝓢)
    [IsProbabilityMeasure ρ] {T : ℕ} (hT : 0 < T) :
    ∫ s, M.optValue γ s ∂ρ - log (Fintype.card 𝓐) / (η * T) - 1 / ((1 - γ) ^ 2 * T) ≤
      ∫ s, M.value γ (softmaxPolicy (npgParam M γ η T)) s ∂ρ := by
  have hR' : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ 1 :=
    fun p ↦ (hR p).mono fun x hx ↦ abs_le.2 ⟨by linarith [hx.1], hx.2⟩
  have hr (p : 𝓢 × 𝓐) : 0 ≤ meanReward M.R p := by
    rw [meanReward_def]
    exact integral_nonneg_of_ae ((hR p).mono fun _ hx ↦ hx.1)
  -- the greedy policy for `v*` is optimal
  have hg := measurable_greedy (M := M) (γ := γ) (measurable_optValue hγ hR')
  rw [← value_greedy_optValue hγ hR' hg]
  exact integral_value_sub_le_integral_value_npg hγ hR' hη hr _ ρ hT

end LMLExplore.ReinforcementLearning
