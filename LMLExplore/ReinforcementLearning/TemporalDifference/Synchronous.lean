/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.MarkovPolicy
public import LMLExplore.Probability.Kernel.Resolvent
public import LMLExplore.ReinforcementLearning.QLearning.Synchronous
import LMLExplore.Analysis.Convex.Integral
import LMLExplore.Analysis.SpecialFunctions.Exp
import LMLExplore.MarkovDecisionProcess.ReturnVariance
import LMLExplore.Probability.Moments.Variance

/-!
# The error of synchronous TD learning

Synchronous TD learning on the generative model is synchronous Q-learning
(`LMLExplore.ReinforcementLearning.syncQLearning`) with one action: at iteration `t + 1`, the value
of every state `s` moves towards `r s + γ V t (ω t s)`, with a fresh sample `ω t s` of the next
state. Its error `Δ t = V t - V*` obeys the linear recursion
`Δ (t + 1) = (I - η (t + 1) (I - γ P)) Δ t + η (t + 1) γ (P_{t+1} - P) V t` [LCCWC24, (110)],
where `P` is the transition kernel and `(P_{t+1} - P) V t s = V t (ω t s) - P V t s` is the
sampling noise. The sharp analysis of TD learning [LCCWC24, Theorem 1 and Appendix C] unrolls this
recursion with the operators `I - η i (I - γ P)` themselves, rather than with scalar weights as for
Q-learning, so that the variances of the noise accumulate through the resolvent `(I - γ P)⁻¹`.

The noise term, Freedman's inequality for it and the bound on its quadratic variation are stated
along the propagators of any kernel on the state-action pairs, so that they also control the lower
bound on the errors of synchronous Q-learning [LCCWC24, Lemma 2] along the state-action kernel of
a policy greedy for the optimal action value, in
`LMLExplore.ReinforcementLearning.QLearning.LowerBound`.

This file develops that unrolling, its first probabilistic consequence, and the bound on the
quadratic variation of the noise in terms of the late errors.
* **The propagators.** For a finite kernel `κ` on a finite space, `κ.tdStep γ c = I - c (I - γ κ)`
  and `κ.tdPropagator γ η k t = (I - η t (I - γ κ)) ⋯ (I - η (k + 1) (I - γ κ))`. For learning
  rates in `[0, 1]`, the propagators are positive operators. For a Markov kernel `κ`, they multiply
  constants by `∏_{i = k + 1}^t (1 - η i (1 - γ))` [LCCWC24, (109)], and, for `γ < 1` and learning
  rates in `[0, 1]`, their weighted sums are dominated by the resolvent:
  `∑_{k = m + 1}^t η k Φ k t f ≤ (I - γ κ)⁻¹ f` for `f ≥ 0`
  [LCCWC24, Section C.2, proof of (117)]. The dynamics `x (t + 1) = (I - η (t + 1) (I - γ κ)) x t +
  e t` unroll to `x t = Φ 0 t (x 0) + ∑_{k < t} Φ (k + 1) t (e k)`, and its supersolutions lie
  above this unrolled form.
* **The error decomposition** [LCCWC24, (110)–(111)]: with one action and the state-action
  kernel `P` of the unique policy, `Δ t = Φ 0 t Δ 0 + ξ t`, with the noise term
  `ξ t = ∑_{k < t} η (k + 1) γ Φ (k + 1) t (P_{k+1} - P) V k`.
* **Freedman's inequality for the noise** [LCCWC24, (113)–(116)]: each entry of the noise term is
  a sum of martingale differences under the generative model, whose conditional variances are
  bounded by the entries of `Φ (k + 1) t Var_P(V k)`. Freedman's inequality and a union bound over
  the entries and the two signs bound the error of the `t`-th iterate with high probability by
  `ρ 0 t C / (1 - γ) + 3 √(W ℓ) + 2 b ℓ`, with `ρ k t = ∏_{i = k + 1}^t (1 - η i (1 - γ))`, the
  quadratic variation bound
  `W = ∑_{k < t} (η (k + 1) γ) ^ 2 ρ (k + 1) t Φ (k + 1) t Var_P(V k)`
  (`LMLExplore.ReinforcementLearning.tdNoiseVarBound`), a bound `b` on the increments and a
  logarithmic factor `ℓ`. A union bound gives this bound at all the iterations of a finite set.
* **The quadratic variation in terms of the errors** [LCCWC24, (117), (95) and (120)]: splitting
  the sum at an iteration `m`, the early propagators are bounded by their action on constants and
  the late weighted sums by the resolvent. With rewards in `[0, C]` and `B = C / (1 - γ)`, the
  late variances `Var_P(V k)` exceed `Var_P(V*)` by at most `4 B D` when the late errors
  `|V k - V*|` are at most `D`, and `γ ^ 2 (I - γ P^π)⁻¹ Var_P(V*) ≤ B ^ 2` for a policy `π`
  greedy for `Q*`, so that `W` is at most
  `B ^ 2 ∑_{k < m} (η (k + 1) γ ρ (k + 1) t) ^ 2 + β (B ^ 2 + 4 γ ^ 2 B D / (1 - γ))`, where `β`
  bounds the late weights `η (k + 1) ρ (k + 1) t`.

The resulting sample complexity of synchronous TD learning with rescaled linear learning rates is
in `LMLExplore.ReinforcementLearning.TemporalDifference.SampleComplexity`.

## Main definitions

* `ProbabilityTheory.Kernel.tdStep κ γ c`: the step `I - c (I - γ κ)` of the mean dynamics.
* `ProbabilityTheory.Kernel.tdPropagator κ γ η k t`: the propagator `Φ k t` of the mean dynamics
  from iteration `k` to iteration `t`.
* `LMLExplore.ReinforcementLearning.tdNoise`: the noise term `ξ t` of the error decomposition,
  along the propagators of a kernel on the state-action pairs.
* `LMLExplore.ReinforcementLearning.tdNoiseVarBound`: the bound `W` on its quadratic variation.

## Main statements

* `ProbabilityTheory.Kernel.tdPropagator_nonneg`, `ProbabilityTheory.Kernel.tdPropagator_const`,
  `ProbabilityTheory.Kernel.abs_tdPropagator_le`: positivity, action on constants and the
  resulting sup-norm bound [LCCWC24, (109)].
* `ProbabilityTheory.Kernel.tdPropagator_apply_eq_sum`: the propagator as a matrix.
* `ProbabilityTheory.Kernel.sum_mul_tdPropagator_succ`,
  `ProbabilityTheory.Kernel.sum_mul_tdPropagator_le_integral_resolvent`: the recursion of the
  weighted sums of propagators and their domination by the resolvent.
* `ProbabilityTheory.Kernel.sum_sq_mul_prod_mul_tdPropagator_le`: the quadratic variation weights
  of the propagators, split at an iteration `m` [LCCWC24, (117)].
* `ProbabilityTheory.Kernel.eq_tdPropagator_add_sum`,
  `ProbabilityTheory.Kernel.tdPropagator_add_sum_le`: unrolling the dynamics and its
  supersolutions.
* `LMLExplore.ReinforcementLearning.syncQLearning_succ_sub_optQValue_eq_tdStep`,
  `LMLExplore.ReinforcementLearning.syncQLearning_sub_optQValue_eq_tdPropagator`: the error
  recursion of TD learning and its unrolled form [LCCWC24, (110)–(111)].
* `LMLExplore.ReinforcementLearning.measure_three_mul_sqrt_add_lt_mul_tdNoise_le`:
  Freedman's inequality for each entry of the noise term.
* `LMLExplore.ReinforcementLearning.measure_exists_lt_abs_syncQLearning_sub_optQValue_le`: the
  high-probability bound on the error of the `t`-th iterate of TD learning.
* `LMLExplore.ReinforcementLearning.measure_exists_mem_exists_lt_abs_syncQLearning_sub_optQValue_le`
  : the same bound at all the iterations of a finite set.
* `LMLExplore.ReinforcementLearning.prod_one_sub_mul_one_sub_nonneg`: the products
  `ρ k t = ∏_{i = k + 1}^t (1 - η i (1 - γ))` are nonnegative.
* `LMLExplore.ReinforcementLearning.mul_integral_variance_optValue_le`:
  `γ ^ 2 (I - γ P^π)⁻¹ Var_P(V*) ≤ (C / (1 - γ)) ^ 2` for a policy `π` greedy for `Q*`.
* `LMLExplore.ReinforcementLearning.tdNoiseVarBound_le`: the quadratic variation bound in terms of
  the late errors [LCCWC24, (117), (95) and (120)].

## References

* [LCCWC24] G. Li, C. Cai, Y. Chen, Y. Wei and Y. Chi, *Is Q-learning minimax optimal? A tight
  sample complexity analysis*, Operations Research (2024), arXiv:2102.06548.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP Bandits
open scoped NNReal

/-! ### The propagators of the mean dynamics -/

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} [Finite α] [MeasurableSingletonClass α]
  (κ : Kernel α α) [IsFiniteKernel κ] (γ : ℝ≥0) (η : ℕ → ℝ)

/-- The step `I - c (I - γ κ)` of the mean dynamics of TD learning with learning rate `c`, for a
finite kernel `κ` on a finite space: it maps `f` to `x ↦ (1 - c) f x + c γ ∫ f dκ x`. -/
noncomputable def tdStep (c : ℝ) : Module.End ℝ (α → ℝ) where
  toFun f x := (1 - c) * f x + c * γ * ∫ y, f y ∂(κ x)
  map_add' f g := by
    funext x
    simp only [Pi.add_apply, integral_add (.of_finite) (.of_finite)]
    ring
  map_smul' a f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul, RingHom.id_apply]
    ring

variable {κ γ} in
@[simp]
lemma tdStep_apply (c : ℝ) (f : α → ℝ) (x : α) :
    tdStep κ γ c f x = (1 - c) * f x + c * γ * ∫ y, f y ∂(κ x) :=
  (rfl)

/-- The propagator `Φ k t = (I - η t (I - γ κ)) ⋯ (I - η (k + 1) (I - γ κ))` of the mean dynamics
of TD learning from iteration `k` to iteration `t`, for `k ≤ t`; it is the identity for `t ≤ k`. -/
noncomputable def tdPropagator (k : ℕ) : ℕ → Module.End ℝ (α → ℝ)
  | 0 => 1
  | t + 1 => if k ≤ t then tdStep κ γ (η (t + 1)) * tdPropagator k t else 1

variable {κ γ η}

/-- The propagator `Φ k 0` is the identity. -/
@[simp]
lemma tdPropagator_zero (k : ℕ) : tdPropagator κ γ η k 0 = 1 :=
  (rfl)

/-- The propagator `Φ k t` is the identity for `t ≤ k`. -/
lemma tdPropagator_of_le {k t : ℕ} (h : t ≤ k) : tdPropagator κ γ η k t = 1 := by
  cases t with
  | zero => exact tdPropagator_zero k
  | succ t => simp [tdPropagator, show ¬ k ≤ t by omega]

/-- The propagator `Φ t t` is the identity. -/
@[simp]
lemma tdPropagator_self (t : ℕ) : tdPropagator κ γ η t t = 1 :=
  tdPropagator_of_le le_rfl

/-- The recursion `Φ k (t + 1) = (I - η (t + 1) (I - γ κ)) Φ k t` of the propagators, for
`k ≤ t`. -/
lemma tdPropagator_succ {k t : ℕ} (h : k ≤ t) :
    tdPropagator κ γ η k (t + 1) = tdStep κ γ (η (t + 1)) * tdPropagator κ γ η k t := by
  simp [tdPropagator, h]

/-- For a learning rate in `[0, 1]`, the step `I - c (I - γ κ)` maps nonnegative functions to
nonnegative functions. -/
lemma tdStep_nonneg {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) {f : α → ℝ} (hf : 0 ≤ f) :
    0 ≤ tdStep κ γ c f := fun x ↦ by
  rw [Pi.zero_apply, tdStep_apply]
  exact add_nonneg (mul_nonneg (sub_nonneg.2 hc.2) (hf x))
    (mul_nonneg (mul_nonneg hc.1 γ.coe_nonneg) (integral_nonneg hf))

/-- For a learning rate in `[0, 1]`, the step `I - c (I - γ κ)` is monotone. -/
lemma tdStep_mono {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) {f g : α → ℝ} (hfg : f ≤ g) :
    tdStep κ γ c f ≤ tdStep κ γ c g := by
  have := tdStep_nonneg (κ := κ) (γ := γ) hc (sub_nonneg.2 hfg)
  rwa [map_sub, sub_nonneg] at this

/-- The step `I - c (I - γ κ)` multiplies constants by `1 - c (1 - γ)`. -/
lemma tdStep_const [IsMarkovKernel κ] (c a : ℝ) :
    tdStep κ γ c (fun _ ↦ a) = fun _ ↦ (1 - c * (1 - γ)) * a := by
  funext x
  simp only [tdStep_apply, MeasureTheory.integral_const, probReal_univ, one_smul]
  ring

/-- For learning rates in `[0, 1]`, the propagator `Φ k t` maps nonnegative functions to
nonnegative functions. -/
lemma tdPropagator_nonneg {k t : ℕ} (hη : ∀ i ∈ Ioc k t, η i ∈ Set.Icc (0 : ℝ) 1) {f : α → ℝ}
    (hf : 0 ≤ f) : 0 ≤ tdPropagator κ γ η k t f := by
  induction t with
  | zero => simpa [tdPropagator] using hf
  | succ t ih =>
    rcases le_or_gt k t with hk | hk
    · rw [tdPropagator_succ hk, mul_apply_eq_comp]
      exact tdStep_nonneg (hη _ (mem_Ioc.2 ⟨by omega, le_rfl⟩))
        (ih fun i hi ↦ hη i (Ioc_subset_Ioc_right t.le_succ hi))
    · rwa [tdPropagator_of_le (by omega), one_apply_eq_self]

/-- For learning rates in `[0, 1]`, the propagator `Φ k t` is monotone. -/
lemma tdPropagator_mono {k t : ℕ} (hη : ∀ i ∈ Ioc k t, η i ∈ Set.Icc (0 : ℝ) 1) {f g : α → ℝ}
    (hfg : f ≤ g) : tdPropagator κ γ η k t f ≤ tdPropagator κ γ η k t g := by
  have := tdPropagator_nonneg (κ := κ) (γ := γ) hη (sub_nonneg.2 hfg)
  rwa [map_sub, sub_nonneg] at this

/-- The propagator `Φ k t` multiplies constants by `∏_{i = k + 1}^t (1 - η i (1 - γ))`. -/
lemma tdPropagator_const [IsMarkovKernel κ] (k t : ℕ) (a : ℝ) :
    tdPropagator κ γ η k t (fun _ ↦ a) =
      fun _ ↦ (∏ i ∈ Ioc k t, (1 - η i * (1 - γ))) * a := by
  induction t with
  | zero => simp [tdPropagator]
  | succ t ih =>
    rcases le_or_gt k t with hk | hk
    · rw [tdPropagator_succ hk, mul_apply_eq_comp, ih, tdStep_const, prod_Ioc_succ_top hk]
      funext x
      ring
    · rw [tdPropagator_of_le (by omega), Ioc_eq_empty (by omega)]
      simp

/-- For learning rates in `[0, 1]`, if `|f| ≤ B`, then
`|Φ k t f| ≤ (∏_{i = k + 1}^t (1 - η i (1 - γ))) B`. -/
lemma abs_tdPropagator_le [IsMarkovKernel κ] {k t : ℕ}
    (hη : ∀ i ∈ Ioc k t, η i ∈ Set.Icc (0 : ℝ) 1) {f : α → ℝ} {B : ℝ} (hf : ∀ y, |f y| ≤ B)
    (x : α) :
    |tdPropagator κ γ η k t f x| ≤ (∏ i ∈ Ioc k t, (1 - η i * (1 - γ))) * B := by
  have h₁ := tdPropagator_mono (κ := κ) (γ := γ) hη (g := fun _ ↦ B)
    (fun y ↦ (abs_le.1 (hf y)).2) x
  have h₂ := tdPropagator_mono (κ := κ) (γ := γ) hη (f := fun _ ↦ -B)
    (fun y ↦ (abs_le.1 (hf y)).1) x
  rw [tdPropagator_const] at h₁ h₂
  exact abs_le.2 ⟨by linarith, h₁⟩

/-- The step `Φ 0 (t + 1) x₀ + ∑_{k ≤ t} Φ (k + 1) (t + 1) (e k)` of the unrolled dynamics is
the image of `Φ 0 t x₀ + ∑_{k < t} Φ (k + 1) t (e k)` under the step `I - η (t + 1) (I - γ κ)`,
plus `e t`. -/
private lemma tdPropagator_add_sum_succ (x₀ : α → ℝ) (e : ℕ → α → ℝ) (t : ℕ) :
    tdPropagator κ γ η 0 (t + 1) x₀ +
        ∑ k ∈ range (t + 1), tdPropagator κ γ η (k + 1) (t + 1) (e k) =
      tdStep κ γ (η (t + 1))
          (tdPropagator κ γ η 0 t x₀ + ∑ k ∈ range t, tdPropagator κ γ η (k + 1) t (e k)) +
        e t := by
  rw [map_add, map_sum, sum_range_succ, tdPropagator_self, tdPropagator_succ (Nat.zero_le t),
    mul_apply_eq_comp, one_apply_eq_self, add_assoc]
  congr 2
  refine sum_congr rfl fun k hk ↦ ?_
  rw [tdPropagator_succ (mem_range.1 hk), mul_apply_eq_comp]

/-- **Unrolling the dynamics** `x (t + 1) = (I - η (t + 1) (I - γ κ)) x t + e t`: then
`x t = Φ 0 t (x 0) + ∑_{k < t} Φ (k + 1) t (e k)`. -/
lemma eq_tdPropagator_add_sum {x e : ℕ → α → ℝ}
    (h : ∀ t, x (t + 1) = tdStep κ γ (η (t + 1)) (x t) + e t) (t : ℕ) :
    x t = tdPropagator κ γ η 0 t (x 0) + ∑ k ∈ range t, tdPropagator κ γ η (k + 1) t (e k) := by
  induction t with
  | zero => simp
  | succ t ih => rw [tdPropagator_add_sum_succ, ← ih, h]

/-- **Unrolling a supersolution of the dynamics.** For learning rates in `[0, 1]`, if
`(I - η (t + 1) (I - γ κ)) x t + e t ≤ x (t + 1)` for every `t`, then
`Φ 0 t (x 0) + ∑_{k < t} Φ (k + 1) t (e k) ≤ x t`, since the steps are monotone. -/
lemma tdPropagator_add_sum_le {x e : ℕ → α → ℝ} (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (h : ∀ t, tdStep κ γ (η (t + 1)) (x t) + e t ≤ x (t + 1)) (t : ℕ) :
    tdPropagator κ γ η 0 t (x 0) + ∑ k ∈ range t, tdPropagator κ γ η (k + 1) t (e k) ≤ x t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [tdPropagator_add_sum_succ]
    exact (add_le_add (tdStep_mono (hη t) ih) le_rfl).trans (h t)

/-- The propagator `Φ k t` is the matrix with the entries `Φ k t 𝟙_y x`: for every `f`,
`Φ k t f x = ∑ y, Φ k t 𝟙_y x f y`. -/
lemma tdPropagator_apply_eq_sum [Fintype α] [DecidableEq α] (k t : ℕ) (f : α → ℝ) (x : α) :
    tdPropagator κ γ η k t f x = ∑ y, tdPropagator κ γ η k t (Pi.single y 1) x * f y := by
  conv_lhs => rw [pi_eq_sum_univ' f, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- The entries of the propagator `Φ k t` add up to `∏_{i = k + 1}^t (1 - η i (1 - γ))`. -/
lemma sum_tdPropagator_single [IsMarkovKernel κ] [Fintype α] [DecidableEq α] (k t : ℕ) (x : α) :
    ∑ y, tdPropagator κ γ η k t (Pi.single y 1) x = ∏ i ∈ Ioc k t, (1 - η i * (1 - γ)) := by
  have h := tdPropagator_apply_eq_sum (κ := κ) (γ := γ) (η := η) k t (fun _ ↦ 1) x
  rw [tdPropagator_const, mul_one] at h
  simpa using h.symm

/-- The entries of `a Φ k t` have absolute values adding up to
`|a| ∏_{i = k + 1}^t (1 - η i (1 - γ))`, for learning rates in `[0, 1]`. -/
private lemma sum_abs_mul_tdPropagator_single [IsMarkovKernel κ] [Fintype α] [DecidableEq α]
    {k t : ℕ} (hη : ∀ i ∈ Ioc k t, η i ∈ Set.Icc (0 : ℝ) 1) (a : ℝ) (x : α) :
    ∑ y, |a * tdPropagator κ γ η k t (Pi.single y 1) x| =
      |a| * ∏ i ∈ Ioc k t, (1 - η i * (1 - γ)) := by
  simp_rw [abs_mul, abs_of_nonneg (tdPropagator_nonneg hη (Pi.single_nonneg.2 zero_le_one) x),
    ← mul_sum, sum_tdPropagator_single]

/-- Weighting `f` with the absolute values of the entries of `a Φ k t` gives `|a| Φ k t f`, for
learning rates in `[0, 1]`. -/
private lemma sum_abs_mul_tdPropagator_single_mul [Fintype α] [DecidableEq α] {k t : ℕ}
    (hη : ∀ i ∈ Ioc k t, η i ∈ Set.Icc (0 : ℝ) 1) (a : ℝ) (f : α → ℝ) (x : α) :
    ∑ y, |a * tdPropagator κ γ η k t (Pi.single y 1) x| * f y =
      |a| * tdPropagator κ γ η k t f x := by
  simp_rw [abs_mul, abs_of_nonneg (tdPropagator_nonneg hη (Pi.single_nonneg.2 zero_le_one) x),
    mul_assoc, ← mul_sum]
  rw [tdPropagator_apply_eq_sum k t f x]

/-- Weighting `f` with the entries of `a Φ k t` gives `a Φ k t f`. -/
private lemma sum_mul_tdPropagator_single_mul [Fintype α] [DecidableEq α] (k t : ℕ) (a : ℝ)
    (f : α → ℝ) (x : α) :
    ∑ y, a * tdPropagator κ γ η k t (Pi.single y 1) x * f y = a * tdPropagator κ γ η k t f x := by
  simp_rw [mul_assoc, ← mul_sum]
  rw [tdPropagator_apply_eq_sum k t f x]

/-- The recursion of the weighted sums of propagators: for `m ≤ t`, the sum
`∑_{k = m + 1}^{t + 1} η k Φ k (t + 1) f` is the image of `∑_{k = m + 1}^t η k Φ k t f` under the
step `I - η (t + 1) (I - γ κ)`, plus `η (t + 1) f`. -/
lemma sum_mul_tdPropagator_succ {m t : ℕ} (hm : m ≤ t) (f : α → ℝ) (x : α) :
    ∑ k ∈ Ioc m (t + 1), η k * tdPropagator κ γ η k (t + 1) f x =
      tdStep κ γ (η (t + 1)) (fun x ↦ ∑ k ∈ Ioc m t, η k * tdPropagator κ γ η k t f x) x +
        η (t + 1) * f x := by
  have : (fun x ↦ ∑ k ∈ Ioc m t, η k * tdPropagator κ γ η k t f x) =
      ∑ k ∈ Ioc m t, η k • tdPropagator κ γ η k t f := by
    funext x
    simp
  rw [sum_Ioc_succ_top hm, this, map_sum, tdPropagator_self, one_apply_eq_self]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine sum_congr rfl fun k hk ↦ ?_
  rw [tdPropagator_succ (mem_Ioc.1 hk).2, mul_apply_eq_comp]

/-- **The propagators are dominated by the resolvent** [LCCWC24, Section C.2]. For `γ < 1`,
learning rates in `[0, 1]` and `f ≥ 0`,
`∑_{k = m + 1}^t η k Φ k t f ≤ (I - γ κ)⁻¹ f = R_γ(κ) f`. -/
theorem sum_mul_tdPropagator_le_integral_resolvent [IsMarkovKernel κ] (hγ : γ < 1) {m t : ℕ}
    (hη : ∀ i ∈ Ioc m t, η i ∈ Set.Icc (0 : ℝ) 1) {f : α → ℝ} (hf : 0 ≤ f) (x : α) :
    ∑ k ∈ Ioc m t, η k * tdPropagator κ γ η k t f x ≤ ∫ y, f y ∂(Kernel.resolvent γ κ x) := by
  obtain ⟨B, hB⟩ := (Set.finite_range fun y ↦ |f y|).bddAbove
  have hfB (y : α) : |f y| ≤ B := hB ⟨y, rfl⟩
  have := Kernel.isFiniteKernel_resolvent (κ := κ) hγ
  set u : α → ℝ := fun x ↦ ∫ y, f y ∂(Kernel.resolvent γ κ x) with hu
  -- `u = R_γ f` solves `u = f + γ κ u`, so that `η f = u - (I - η (I - γ κ)) u`
  have hfix (c : ℝ) (x : α) : tdStep κ γ c u x + c * f x = u x := by
    simp only [tdStep_apply, hu]
    rw [Kernel.integral_resolvent_eq_add hγ (.of_discrete) hfB x]
    ring
  induction t generalizing x with
  | zero => simpa using integral_nonneg hf
  | succ t ih =>
    rcases le_or_gt m t with hm | hm
    · have hη' : η (t + 1) ∈ Set.Icc (0 : ℝ) 1 := hη _ (mem_Ioc.2 ⟨by omega, le_rfl⟩)
      have hle := tdStep_nonneg (κ := κ) (γ := γ) hη'
        (sub_nonneg.2 (fun x ↦ ih (fun i hi ↦ hη i (Ioc_subset_Ioc_right t.le_succ hi)) x :
          (fun x ↦ ∑ k ∈ Ioc m t, η k * tdPropagator κ γ η k t f x) ≤ u)) x
      rw [map_sub, Pi.sub_apply, Pi.zero_apply, sub_nonneg] at hle
      calc _ = _ := sum_mul_tdPropagator_succ hm f x
        _ ≤ tdStep κ γ (η (t + 1)) u x + η (t + 1) * f x := by linarith
        _ = u x := hfix _ x
    · rw [Ioc_eq_empty (by omega), sum_empty]
      exact integral_nonneg hf

/-- **The quadratic variation weights of the propagators, split at an iteration `m`**
[LCCWC24, (117)]. For `γ < 1`, learning rates in `[0, 1]`, nonnegative functions `g k` and
`m ≤ t`, the weighted sum
`∑_{k < t} (η (k + 1) γ) ^ 2 ρ (k + 1) t Φ (k + 1) t (g k)`, with
`ρ k t = ∏_{i = k + 1}^t (1 - η i (1 - γ))`, is at most
`G ∑_{k < m} (η (k + 1) γ ρ (k + 1) t) ^ 2 + γ ^ 2 β (I - γ κ)⁻¹ v`, where `G` bounds the early
functions `g k`, `k < m`, `v ≥ 0` dominates the late ones, `m ≤ k < t`, and `β ≥ 0` bounds the
late weights `η (k + 1) ρ (k + 1) t`. -/
theorem sum_sq_mul_prod_mul_tdPropagator_le [IsMarkovKernel κ] (hγ : γ < 1) {m t : ℕ}
    (hmt : m ≤ t) (hη : ∀ i ∈ Ioc 0 t, η i ∈ Set.Icc (0 : ℝ) 1) {g : ℕ → α → ℝ} {v : α → ℝ}
    {G β : ℝ} (hg : ∀ k ∈ Ico m t, 0 ≤ g k) (hgG : ∀ k < m, ∀ y, |g k y| ≤ G)
    (hgv : ∀ k ∈ Ico m t, g k ≤ v) (hv : 0 ≤ v) (hβ₀ : 0 ≤ β)
    (hβ : ∀ k ∈ Ico m t, η (k + 1) * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) ≤ β) (x : α) :
    ∑ k ∈ range t, (η (k + 1) * γ) ^ 2 * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) *
        tdPropagator κ γ η (k + 1) t (g k) x ≤
      G * ∑ k ∈ range m, (η (k + 1) * γ * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) ^ 2 +
        γ ^ 2 * β * ∫ y, v y ∂(resolvent γ κ x) := by
  have hηk (k : ℕ) : ∀ i ∈ Ioc (k + 1) t, η i ∈ Set.Icc (0 : ℝ) 1 := fun i hi ↦
    hη i (Ioc_subset_Ioc_left (Nat.zero_le _) hi)
  have hρ (k : ℕ) : 0 ≤ ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) :=
    Real.prod_one_sub_mul_nonneg (sub_nonneg.2 (by exact_mod_cast hγ.le))
      (by linarith [γ.coe_nonneg]) (hηk k)
  rw [← sum_range_add_sum_Ico _ hmt]
  refine add_le_add ?_ ?_
  · -- the early terms: `|Φ (k + 1) t (g k)| ≤ ρ (k + 1) t G`
    rw [mul_sum]
    refine sum_le_sum fun k hk ↦ ?_
    have hk := mem_range.1 hk
    have h := (le_abs_self _).trans (abs_tdPropagator_le (κ := κ) (γ := γ) (hηk k) (hgG k hk) x)
    calc _ ≤ (η (k + 1) * γ) ^ 2 * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) *
          ((∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) * G) := by
          have := hρ k
          gcongr
      _ = _ := by ring
  · -- the late terms: `η (k + 1) ρ (k + 1) t ≤ β`, `g k ≤ v`, and the resolvent domination
    have hlate (k : ℕ) (hk : k ∈ Ico m t) :
        (η (k + 1) * γ) ^ 2 * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) *
            tdPropagator κ γ η (k + 1) t (g k) x ≤
          γ ^ 2 * β * (η (k + 1) * tdPropagator κ γ η (k + 1) t v x) := by
      have hηk1 : η (k + 1) ∈ Set.Icc (0 : ℝ) 1 :=
        hη _ (mem_Ioc.2 ⟨k.succ_pos, (mem_Ico.1 hk).2⟩)
      have hΦ₀ : 0 ≤ tdPropagator κ γ η (k + 1) t (g k) x :=
        tdPropagator_nonneg (hηk k) (hg k hk) x
      have hΦ : tdPropagator κ γ η (k + 1) t (g k) x ≤ tdPropagator κ γ η (k + 1) t v x :=
        tdPropagator_mono (hηk k) (hgv k hk) x
      calc _ = (γ : ℝ) ^ 2 * (η (k + 1) * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) *
            (η (k + 1) * tdPropagator κ γ η (k + 1) t (g k) x) := by ring
        _ ≤ _ := by
          gcongr
          · exact mul_nonneg hηk1.1 hΦ₀
          · exact hβ k hk
          · exact hηk1.1
    refine (sum_le_sum hlate).trans ?_
    rw [← mul_sum, sum_Ico_add' (fun k ↦ η k * tdPropagator κ γ η k t v x),
      Ico_add_one_add_one_eq_Ioc]
    gcongr
    exact sum_mul_tdPropagator_le_integral_resolvent hγ
      (fun i hi ↦ hη i (Ioc_subset_Ioc_left (Nat.zero_le _) hi)) hv x

end ProbabilityTheory.Kernel

namespace LMLExplore.ReinforcementLearning

/-! ### The error decompositions -/

section TD

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Finite 𝓢]
  [Nonempty 𝓢] [MeasurableSingletonClass 𝓢] [Finite 𝓐] [MeasurableSingletonClass 𝓐]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {η : ℕ → ℝ} {Q₀ : 𝓢 × 𝓐 → ℝ} {C : ℝ}

/-- **One step of the error of synchronous TD learning** [LCCWC24, (110)]. With one action, the
error `Δ t = Q t - Q*` satisfies
`Δ (t + 1) = (I - η (t + 1) (I - γ P)) Δ t + η (t + 1) γ (P_{t+1} - P) V t`, where `P` is the
state-action kernel of the unique policy and `(P_{t+1} - P) V t p = V t (ω t p) - P V t p` is the
sampling noise of the value estimate `V t s = Q t (s, default)`. -/
theorem syncQLearning_succ_sub_optQValue_eq_tdStep [Unique 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (t : ℕ) (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) :
    syncQLearning (meanReward M.R) γ η Q₀ (t + 1) ω p - M.optQValue γ p =
      Kernel.tdStep
        (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) γ (η (t + 1))
          (fun q ↦ syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q) p +
        η (t + 1) * γ * (syncQLearning (meanReward M.R) γ η Q₀ t ω (ω t p, default) -
          ∫ s', syncQLearning (meanReward M.R) γ η Q₀ t ω (s', default) ∂(M.P p)) := by
  rw [syncQLearning_succ_sub_optQValue_of_unique hγ hR, Kernel.tdStep_apply,
    integral_saKernel_deterministic _ .of_finite]
  ring

variable (M γ η Q₀) in
omit [Nonempty 𝓢] in
/-- The noise `ξ t p = ∑_{k < t} η (k + 1) γ Φ (k + 1) t ((P_{k+1} - P) V k) p` of the error
decompositions of synchronous Q-learning, where `Φ k t` is the propagator of the mean dynamics with
a kernel `κ` on the state-action pairs and `(P_{k+1} - P) V k q = V k (ω k q) - P V k q` is the
sampling noise of the value estimate `V k s = ⨆ a, Q k (s, a)` at iteration `k + 1`. With one
action and the state-action kernel of the unique policy, it is the noise of synchronous TD
learning; with the state-action kernel of a policy greedy for `Q*`, it is the noise of the lower
bound on the errors of synchronous Q-learning. -/
noncomputable def tdNoise (κ : Kernel (𝓢 × 𝓐) (𝓢 × 𝓐)) [IsFiniteKernel κ] (t : ℕ)
    (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) : ℝ :=
  ∑ k ∈ range t, η (k + 1) * γ * κ.tdPropagator γ η (k + 1) t
    (fun q ↦ (⨆ a, syncQLearning (meanReward M.R) γ η Q₀ k ω (ω k q, a)) -
      ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ k ω (s', a) ∂(M.P q)) p

omit [Nonempty 𝓢] in
/-- The noise `ξ t p` as the sum over the iterations `k < t` of the propagated sampling noises. -/
lemma tdNoise_def (κ : Kernel (𝓢 × 𝓐) (𝓢 × 𝓐)) [IsFiniteKernel κ] (t : ℕ)
    (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) :
    tdNoise M γ η Q₀ κ t ω p = ∑ k ∈ range t, η (k + 1) * γ * κ.tdPropagator γ η (k + 1) t
      (fun q ↦ (⨆ a, syncQLearning (meanReward M.R) γ η Q₀ k ω (ω k q, a)) -
        ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ k ω (s', a) ∂(M.P q)) p :=
  (rfl)

omit [Nonempty 𝓢] in
/-- The noise `ξ t` is the sum of the propagated sampling noises `η (k + 1) γ (P_{k+1} - P) V k`,
as functions on the state-action pairs. -/
lemma tdNoise_eq_sum_apply (κ : Kernel (𝓢 × 𝓐) (𝓢 × 𝓐)) [IsFiniteKernel κ] (t : ℕ)
    (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) :
    tdNoise M γ η Q₀ κ t ω p = (∑ k ∈ range t, κ.tdPropagator γ η (k + 1) t
      ((η (k + 1) * γ) • fun q ↦ (⨆ a, syncQLearning (meanReward M.R) γ η Q₀ k ω (ω k q, a)) -
        ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ k ω (s', a) ∂(M.P q))) p := by
  simp [tdNoise_def, Finset.sum_apply]

/-- **The error decomposition of synchronous TD learning** [LCCWC24, (111)]. With one action, the
error `Δ t = Q t - Q*` is `Δ t = Φ 0 t Δ 0 + ξ t`, where `Φ k t` is the propagator of the mean
dynamics with the state-action kernel `P` of the unique policy and
`ξ t = ∑_{k < t} η (k + 1) γ Φ (k + 1) t (P_{k+1} - P) V k` is the noise term
`LMLExplore.ReinforcementLearning.tdNoise`, with the sampling noise
`(P_{k+1} - P) V k p = V k (ω k p) - P V k p` of the value estimate `V k s = Q k (s, default)` at
iteration `k + 1`. -/
theorem syncQLearning_sub_optQValue_eq_tdPropagator [Unique 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (t : ℕ) (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) :
    syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p =
      Kernel.tdPropagator
        (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) γ η 0 t
          (fun q ↦ Q₀ q - M.optQValue γ q) p +
        tdNoise M γ η Q₀ (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const))
          t ω p := by
  have h := Kernel.eq_tdPropagator_add_sum
    (κ := M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) (γ := γ)
    (η := η) (x := fun t q ↦ syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q)
    (e := fun t ↦ (η (t + 1) * γ) • fun q ↦
      (⨆ a, syncQLearning (meanReward M.R) γ η Q₀ t ω (ω t q, a)) -
        ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ t ω (s', a) ∂(M.P q))
    (fun t ↦ funext fun q ↦ by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ciSup_unique]
      exact syncQLearning_succ_sub_optQValue_eq_tdStep hγ hR t ω q) t
  rw [congrFun h p, Pi.add_apply, tdNoise_eq_sum_apply]
  simp only [syncQLearning_zero]

/-- For `γ < 1` and learning rates in `[0, 1]` from iteration `1` on, the products
`ρ k t = ∏_{i = k + 1}^t (1 - η i (1 - γ))` are nonnegative. -/
lemma prod_one_sub_mul_one_sub_nonneg (hγ : γ < 1) (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (k t : ℕ) : 0 ≤ ∏ i ∈ Ioc k t, (1 - η i * (1 - γ)) :=
  Real.prod_one_sub_mul_nonneg (sub_nonneg.2 (by exact_mod_cast hγ.le))
    (by linarith [γ.coe_nonneg]) fun _ hi ↦ learningRate_mem_Icc_of_mem_Ioc hη hi

variable (M γ η Q₀) in
omit [Nonempty 𝓢] in
/-- The bound `W t p = ∑_{k < t} (η (k + 1) γ) ^ 2 ρ (k + 1) t Φ (k + 1) t Var_P(V k) p` on the
quadratic variation of the noise `LMLExplore.ReinforcementLearning.tdNoise` with the kernel `κ`,
where `ρ k t = ∏_{i = k + 1}^t (1 - η i (1 - γ))`, `Φ k t` is the propagator of the mean dynamics
with `κ` and `Var_P(V k) q` is the variance of the value estimate `V k s = ⨆ a, Q k (s, a)` under
`P q`. -/
noncomputable def tdNoiseVarBound (κ : Kernel (𝓢 × 𝓐) (𝓢 × 𝓐)) [IsFiniteKernel κ] (t : ℕ)
    (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) : ℝ :=
  ∑ k ∈ range t, (η (k + 1) * γ) ^ 2 * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) *
    κ.tdPropagator γ η (k + 1) t
      (fun q ↦ Var[fun s' ↦ ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ k ω (s', a); M.P q]) p

omit [Nonempty 𝓢] in
/-- The bound `W t p` as the sum over the iterations `k < t` of the propagated variances. -/
lemma tdNoiseVarBound_def (κ : Kernel (𝓢 × 𝓐) (𝓢 × 𝓐)) [IsFiniteKernel κ] (t : ℕ)
    (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) :
    tdNoiseVarBound M γ η Q₀ κ t ω p =
      ∑ k ∈ range t, (η (k + 1) * γ) ^ 2 * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) *
        κ.tdPropagator γ η (k + 1) t
          (fun q ↦ Var[fun s' ↦ ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ k ω (s', a); M.P q])
            p :=
  (rfl)

omit [Nonempty 𝓢] in
/-- **Freedman's inequality for the noise of synchronous Q-learning**, one-sided
[LCCWC24, (113)–(116)]. With rewards in `[0, C]`, learning rates in `[0, 1]` and
`0 ≤ Q₀ ≤ C / (1 - γ)`, let `κ` be a Markov kernel on the state-action pairs, let `σ` be `1` or
`-1` and `b > 0` with `η (k + 1) γ ρ (k + 1) t C / (1 - γ) ≤ b` for every `k < t`, where
`ρ k t = ∏_{i = k + 1}^t (1 - η i (1 - γ))`. Then for every pair `p`, with probability at least
`1 - δ`, the noise `ξ t p` with the kernel `κ` (`LMLExplore.ReinforcementLearning.tdNoise`)
satisfies `σ ξ t p ≤ 3 √(W ℓ) + 2 b ℓ`, with the quadratic variation bound
`W = LMLExplore.ReinforcementLearning.tdNoiseVarBound M γ η Q₀ κ t ω p`,
`ℓ = max 1 (log (K / δ))` and `K = ⌈log₄ t⌉ + 1`. -/
theorem measure_three_mul_sqrt_add_lt_mul_tdNoise_le [Nonempty 𝓐]
    {κ : Kernel (𝓢 × 𝓐) (𝓢 × 𝓐)} [IsMarkovKernel κ] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ))) {δ b σ : ℝ} (hδ : 0 < δ) (hb : 0 < b)
    (hσ : |σ| = 1) (t : ℕ)
    (hvb : ∀ k < t, η (k + 1) * γ * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) * (C / (1 - γ)) ≤ b)
    (p : 𝓢 × 𝓐) :
    streamMeasure M.P {ω | 3 * √(tdNoiseVarBound M γ η Q₀ κ t ω p *
          max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) +
        2 * b * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ)) <
      σ * tdNoise M γ η Q₀ κ t ω p} ≤ ENNReal.ofReal δ := by
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
  have hηk (k : ℕ) : ∀ i ∈ Ioc (k + 1) t, η i ∈ Set.Icc (0 : ℝ) 1 := fun i hi ↦
    learningRate_mem_Icc_of_mem_Ioc hη hi
  have hc (k : ℕ) : |σ * (η (k + 1) * γ)| = η (k + 1) * γ := by
    rw [abs_mul, hσ, one_mul, abs_of_nonneg (mul_nonneg (hη k).1 γ.coe_nonneg)]
  -- the weights of the noises are `σ η (k + 1) γ` times the entries of `Φ (k + 1) t`
  have h := measure_three_mul_sqrt_add_lt_sum_sum_mul_iSup_syncQLearning_le (P := M.P) hη hr hQ₀
    hB hδ hb t (fun k y ↦ σ * (η (k + 1) * γ) * κ.tdPropagator γ η (k + 1) t (Pi.single y 1) p)
    fun k hk ↦ by
      rw [Kernel.sum_abs_mul_tdPropagator_single (hηk k), hc]
      exact hvb k hk
  -- in these weights, the quadratic variation bound is `W` and the noise is `σ ξ t p`
  have hW (ω : ℕ → 𝓢 × 𝓐 → 𝓢) : ∑ k ∈ range t,
      (∑ y, |σ * (η (k + 1) * γ) * κ.tdPropagator γ η (k + 1) t (Pi.single y 1) p|) *
        ∑ y, |σ * (η (k + 1) * γ) * κ.tdPropagator γ η (k + 1) t (Pi.single y 1) p| *
          Var[fun s' ↦ ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ k ω (s', a); M.P y] =
      tdNoiseVarBound M γ η Q₀ κ t ω p := by
    rw [tdNoiseVarBound_def]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [Kernel.sum_abs_mul_tdPropagator_single (hηk k),
      Kernel.sum_abs_mul_tdPropagator_single_mul (hηk k), hc]
    ring
  have hξ (ω : ℕ → 𝓢 × 𝓐 → 𝓢) : ∑ k ∈ range t, ∑ y,
      σ * (η (k + 1) * γ) * κ.tdPropagator γ η (k + 1) t (Pi.single y 1) p *
        ((⨆ a, syncQLearning (meanReward M.R) γ η Q₀ k ω (ω k y, a)) -
          ∫ s', ⨆ a, syncQLearning (meanReward M.R) γ η Q₀ k ω (s', a) ∂(M.P y)) =
      σ * tdNoise M γ η Q₀ κ t ω p := by
    simp_rw [tdNoise_def, Kernel.sum_mul_tdPropagator_single_mul, mul_sum]
    exact sum_congr rfl fun k _ ↦ by ring
  simp only [hW, hξ] at h
  exact h

/-- If the error of the `t`-th iterate of synchronous TD learning exceeds
`ρ 0 t C / (1 - γ) + a`, with `ρ 0 t = ∏_{i = 1}^t (1 - η i (1 - γ))`, then the noise `ξ t p`
of the error decomposition exceeds `a` in absolute value: the contracted initial error is at most
`ρ 0 t C / (1 - γ)`. -/
private lemma lt_abs_tdNoise_of_lt_abs_syncQLearning_sub_optQValue [Unique 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ))) {a : ℝ} {t : ℕ} {ω : ℕ → 𝓢 × 𝓐 → 𝓢}
    {p : 𝓢 × 𝓐}
    (h : (∏ i ∈ Ioc 0 t, (1 - η i * (1 - γ))) * (C / (1 - γ)) + a <
      |syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p|) :
    a < |tdNoise M γ η Q₀ (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const))
      t ω p| := by
  have hRabs : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C := fun p ↦ (hR p).mono fun x hx ↦
    abs_le.2 ⟨by linarith [hx.1, hx.2], hx.2⟩
  have h₀ := Kernel.abs_tdPropagator_le
    (κ := M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) (γ := γ)
    (k := 0) (t := t) (fun i hi ↦ learningRate_mem_Icc_of_mem_Ioc hη hi)
    (f := fun q ↦ Q₀ q - M.optQValue γ q)
    (fun q ↦ by simpa using abs_syncQLearning_sub_optQValue_le (η := η) hγ hR hη hQ₀ 0 ω q) p
  rw [syncQLearning_sub_optQValue_eq_tdPropagator hγ hRabs] at h
  linarith [(abs_add_le _ _).trans_lt' h]

/-- **The high-probability error bound of synchronous TD learning** [LCCWC24, (112)–(116)]. With
one action, rewards in `[0, C]`, `γ < 1`, learning rates in `[0, 1]` and
`0 ≤ Q₀ ≤ C / (1 - γ)`, let `b > 0` with `η (k + 1) γ ρ (k + 1) t C / (1 - γ) ≤ b` for every
`k < t`, where `ρ k t = ∏_{i = k + 1}^t (1 - η i (1 - γ))`. Then with probability at least
`1 - 2 S δ`, with `S` the number of states, for every pair `p`, the error of the `t`-th iterate
satisfies `|Q t p - Q* p| ≤ ρ 0 t C / (1 - γ) + 3 √(W p ℓ) + 2 b ℓ`, with the quadratic variation
bound `W p = LMLExplore.ReinforcementLearning.tdNoiseVarBound M γ η Q₀ κ t ω p` for the
state-action kernel `κ` of the unique policy, `ℓ = max 1 (log (K / δ))` and
`K = ⌈log₄ t⌉ + 1`: the initial error is contracted by the mean dynamics and the sampling noise is
controlled by Freedman's inequality. -/
theorem measure_exists_lt_abs_syncQLearning_sub_optQValue_le [Fintype 𝓢] [Unique 𝓐]
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C)
    (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1) (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ)))
    {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b) (t : ℕ)
    (hvb : ∀ k < t,
      η (k + 1) * γ * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) * (C / (1 - γ)) ≤ b) :
    streamMeasure M.P {ω | ∃ p, (∏ i ∈ Ioc 0 t, (1 - η i * (1 - γ))) * (C / (1 - γ)) +
        (3 * √(tdNoiseVarBound M γ η Q₀
            (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) t ω p *
          max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) +
        2 * b * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) <
      |syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p|} ≤
      ENNReal.ofReal (2 * Fintype.card 𝓢 * δ) := by
  -- the noise exceeds its bound from above or from below at some pair
  set E : ℝ → 𝓢 × 𝓐 → Set (ℕ → 𝓢 × 𝓐 → 𝓢) := fun σ p ↦ {ω |
    3 * √(tdNoiseVarBound M γ η Q₀
        (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) t ω p *
      max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) +
      2 * b * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ)) <
    σ * tdNoise M γ η Q₀ (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const))
      t ω p} with hE
  have hE₁ (σ : ℝ) (hσ : |σ| = 1) (p : 𝓢 × 𝓐) : streamMeasure M.P (E σ p) ≤ ENNReal.ofReal δ :=
    measure_three_mul_sqrt_add_lt_mul_tdNoise_le hγ hR hη hQ₀ hδ hb hσ t hvb p
  calc streamMeasure M.P _ ≤ streamMeasure M.P (⋃ p, (E 1 p ∪ E (-1) p)) :=
        measure_mono fun ω hω ↦ by
          obtain ⟨p, hp⟩ := hω
          refine Set.mem_iUnion.2 ⟨p, ?_⟩
          simpa only [hE, Set.mem_union, Set.mem_ofPred_eq, one_mul, neg_one_mul] using
            lt_abs.1 (lt_abs_tdNoise_of_lt_abs_syncQLearning_sub_optQValue hγ hR hη hQ₀ hp)
    _ ≤ ∑ p, streamMeasure M.P (E 1 p ∪ E (-1) p) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : 𝓢 × 𝓐, (ENNReal.ofReal δ + ENNReal.ofReal δ) := sum_le_sum fun p _ ↦
        (measure_union_le _ _).trans (add_le_add (hE₁ 1 abs_one p) (hE₁ (-1) (by simp) p))
    _ = ENNReal.ofReal (2 * Fintype.card 𝓢 * δ) := by
        rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_unique (α := 𝓐), mul_one,
          nsmul_eq_mul, ← ENNReal.ofReal_add hδ.le hδ.le,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-! ### The quadratic variation in terms of the errors -/

/-- **The resolvent of the one-step variances of the optimal value** [LCCWC24, Section C.2]. With
rewards in `[0, C]`, `γ < 1` and a policy `π` greedy for the optimal action value,
`Q* (s, π s) = V* s`, the resolvent `(I - γ P^π)⁻¹` of the state-action kernel `P^π` of `π`,
applied to the one-step variances `Var_P(V*)` of the optimal value, satisfies
`γ ^ 2 (I - γ P^π)⁻¹ Var_P(V*) ≤ (C / (1 - γ)) ^ 2`. This improves the bound
`(I - γ P)⁻¹ Var_P(V*) ≤ 2 / (γ ^ 2 (1 - γ) ^ 2)` of the source, for `C = 1`, by a factor `2`.
-/
theorem mul_integral_variance_optValue_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) {π : 𝓢 → 𝓐}
    (hπ : ∀ s, M.optQValue γ (s, π s) = M.optValue γ s) (p : 𝓢 × 𝓐) :
    (γ : ℝ) ^ 2 * ∫ q, Var[M.optValue γ; M.P q]
        ∂(Kernel.resolvent γ (M.saKernel (Kernel.deterministic π (measurable_of_finite π))) p) ≤
      (C / (1 - γ)) ^ 2 := by
  have : Nonempty 𝓐 := ⟨π (Classical.arbitrary 𝓢)⟩
  have hRabs : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C := fun p ↦ (hR p).mono fun x hx ↦
    abs_le.2 ⟨by linarith [hx.1, hx.2], hx.2⟩
  have hr₀ (q : 𝓢 × 𝓐) : 0 ≤ meanReward M.R q := by
    rw [meanReward_def]
    exact integral_nonneg_of_ae ((hR q).mono fun x hx ↦ hx.1)
  have hQ := optQValue_eq_integral_resolvent_of_greedy (M := M) hγ hRabs
    (measurable_of_finite π) hπ
  have hVB (y : 𝓢 × 𝓐) : ∫ z, meanReward M.R z ∂(Kernel.resolvent γ
      (M.saKernel (Kernel.deterministic π (measurable_of_finite π))) y) ≤ C / (1 - γ) := by
    rw [← congrFun hQ y]
    exact (le_abs_self _).trans (abs_optQValue_le hγ hRabs y)
  -- `Var_P(V*) = Var_{P^π}(Q*)`, since `V* = Q* (·, π ·)`
  have hV : M.optValue γ = fun s ↦ M.optQValue γ (s, π s) := funext fun s ↦ (hπ s).symm
  simp_rw [hV, ← variance_saKernel_deterministic (measurable_of_finite π)
    (measurable_of_finite (M.optQValue γ)).aemeasurable]
  rw [hQ]
  have h := Kernel.mul_integral_variance_integral_resolvent_le
    (κ := M.saKernel (Kernel.deterministic π (measurable_of_finite π))) hγ
    (measurable_of_finite _) (abs_meanReward_le hRabs) hr₀ hVB p
  nlinarith [sq_nonneg (C / (1 - γ) - ∫ z, meanReward M.R z ∂(Kernel.resolvent γ
    (M.saKernel (Kernel.deterministic π (measurable_of_finite π))) p))]

omit [Nonempty 𝓢] in
/-- The bound `W t p` on the quadratic variation of the noise is nonnegative, for learning rates in
`[0, 1]` and `γ < 1`. -/
lemma tdNoiseVarBound_nonneg {κ : Kernel (𝓢 × 𝓐) (𝓢 × 𝓐)} [IsFiniteKernel κ] (hγ : γ < 1)
    (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) :
    0 ≤ tdNoiseVarBound M γ η Q₀ κ t ω p := by
  rw [tdNoiseVarBound_def]
  refine sum_nonneg fun k _ ↦ mul_nonneg (mul_nonneg (sq_nonneg _)
    (prod_one_sub_mul_one_sub_nonneg hγ hη _ _))
    (Kernel.tdPropagator_nonneg (fun i hi ↦ learningRate_mem_Icc_of_mem_Ioc hη hi)
      (fun q ↦ variance_nonneg _ _) p)

/-- **The quadratic variation of the noise in terms of the errors** [LCCWC24, (117), (95) and
(120)]. With rewards in `[0, C]`, `γ < 1`, learning rates in `[0, 1]`, `0 ≤ Q₀ ≤ C / (1 - γ)`
and a policy `π` greedy for the optimal action value, `Q* (s, π s) = V* s`, let `m ≤ t`, let
`D ≥ 0` bound the errors `|V k - V*|` of the value estimates `V k s = ⨆ a, Q k (s, a)` at the late
iterations `m ≤ k < t`, and let `β ≥ 0` bound the late weights `η (k + 1) ρ (k + 1) t`, where
`ρ k t = ∏_{i = k + 1}^t (1 - η i (1 - γ))`. Then the bound
`W t p = LMLExplore.ReinforcementLearning.tdNoiseVarBound M γ η Q₀ P^π t ω p` on the quadratic
variation of the noise with the state-action kernel `P^π` of `π` satisfies
`W t p ≤ B ^ 2 ∑_{k < m} (η (k + 1) γ ρ (k + 1) t) ^ 2 + β (B ^ 2 + 4 γ ^ 2 B D / (1 - γ))`, with
`B = C / (1 - γ)`: the early variances are at most `B ^ 2`, the late ones exceed `Var_P(V*)` by at
most `4 B D`, and the resolvent of `Var_P(V*)` is at most `B ^ 2 / γ ^ 2`. -/
theorem tdNoiseVarBound_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C)
    (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1) (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ)))
    {π : 𝓢 → 𝓐} (hπ : ∀ s, M.optQValue γ (s, π s) = M.optValue γ s)
    {m t : ℕ} (hmt : m ≤ t) {ω : ℕ → 𝓢 × 𝓐 → 𝓢} {D β : ℝ} (hD₀ : 0 ≤ D)
    (hD : ∀ k ∈ Ico m t, ∀ s,
      |(⨆ a, syncQLearning (meanReward M.R) γ η Q₀ k ω (s, a)) - M.optValue γ s| ≤ D)
    (hβ₀ : 0 ≤ β) (hβ : ∀ k ∈ Ico m t, η (k + 1) * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) ≤ β)
    (p : 𝓢 × 𝓐) :
    tdNoiseVarBound M γ η Q₀ (M.saKernel (Kernel.deterministic π (measurable_of_finite π))) t ω
        p ≤
      (C / (1 - γ)) ^ 2 *
          ∑ k ∈ range m, (η (k + 1) * γ * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) ^ 2 +
        β * ((C / (1 - γ)) ^ 2 + 4 * γ ^ 2 * (C / (1 - γ)) * D / (1 - γ)) := by
  have : Nonempty 𝓐 := ⟨π (Classical.arbitrary 𝓢)⟩
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
  set B := C / (1 - γ)
  -- the value estimates and the optimal value lie in `[-B, B]`
  have hV (k : ℕ) (s : 𝓢) : |⨆ a, syncQLearning (meanReward M.R) γ η Q₀ k ω (s, a)| ≤ B := by
    have := iSup_syncQLearning_mem_Icc hη hr hQ₀ hB k ω s
    exact abs_le.2 ⟨by linarith [this.1, this.2], this.2⟩
  have hVs (s : 𝓢) : |M.optValue γ s| ≤ B := abs_optValue_le hγ hRabs s
  have := Kernel.isFiniteKernel_resolvent
    (κ := M.saKernel (Kernel.deterministic π (measurable_of_finite π))) hγ
  rw [tdNoiseVarBound_def]
  refine (Kernel.sum_sq_mul_prod_mul_tdPropagator_le hγ hmt
    (fun i hi ↦ learningRate_mem_Icc_of_mem_Ioc hη hi) (G := B ^ 2)
    (v := fun q ↦ Var[M.optValue γ; M.P q] + 4 * B * D)
    (fun k _ q ↦ variance_nonneg _ _)
    (fun k _ q ↦ by
      rw [abs_of_nonneg (variance_nonneg _ _)]
      exact variance_le_sq_of_abs_le (measurable_of_finite _).aemeasurable (.of_forall (hV k)))
    (fun k hk q ↦ variance_le_variance_add_of_abs_sub_le (measurable_of_finite _).aemeasurable
      (measurable_of_finite _).aemeasurable (.of_forall (hV k)) (.of_forall hVs)
      (.of_forall (hD k hk)))
    (fun q ↦ add_nonneg (variance_nonneg _ _)
      (mul_nonneg (mul_nonneg zero_le_four ((abs_nonneg _).trans (hVs (Classical.arbitrary 𝓢))))
        hD₀))
    hβ₀ hβ p).trans ?_
  -- the resolvent of `Var_P(V*) + 4 B D` is at most `B ^ 2 / γ ^ 2 + 4 B D / (1 - γ)`
  have hσ := mul_integral_variance_optValue_le hγ hR hπ p
  rw [integral_add .of_finite (integrable_const _), integral_const,
    Kernel.measureReal_resolvent_univ hγ, smul_eq_mul]
  have h₁ : (γ : ℝ) ^ 2 * β * (∫ q, Var[M.optValue γ; M.P q]
      ∂(Kernel.resolvent γ (M.saKernel (Kernel.deterministic π (measurable_of_finite π))) p) +
        (1 - (γ : ℝ))⁻¹ * (4 * B * D)) =
      β * ((γ : ℝ) ^ 2 * ∫ q, Var[M.optValue γ; M.P q]
        ∂(Kernel.resolvent γ (M.saKernel (Kernel.deterministic π (measurable_of_finite π))) p)) +
        β * (4 * γ ^ 2 * B * D / (1 - γ)) := by
    rw [div_eq_mul_inv]
    ring
  have h₂ := mul_le_mul_of_nonneg_left hσ hβ₀
  linarith

/-- **The high-probability error bound of synchronous TD learning at several iterations**
[LCCWC24, Section C.2, Step 3]. Under the assumptions of
`measure_exists_lt_abs_syncQLearning_sub_optQValue_le`, let `I` be a finite set of iterations and
let `b > 0` bound the weights `η (k + 1) γ ρ (k + 1) t C / (1 - γ)` for every `t ∈ I` and `k < t`.
Then with probability at least `1 - 2 S #I δ`, for every iteration `t ∈ I` and every pair `p`, the
error of the `t`-th iterate satisfies
`|Q t p - Q* p| ≤ ρ 0 t C / (1 - γ) + 3 √(W t p ℓ t) + 2 b ℓ t`, with
`ℓ t = max 1 (log ((⌈log₄ t⌉ + 1) / δ))`. -/
theorem measure_exists_mem_exists_lt_abs_syncQLearning_sub_optQValue_le [Fintype 𝓢] [Unique 𝓐]
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C)
    (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1) (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ)))
    {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b) (I : Finset ℕ)
    (hvb : ∀ t ∈ I, ∀ k < t,
      η (k + 1) * γ * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) * (C / (1 - γ)) ≤ b) :
    streamMeasure M.P {ω | ∃ t ∈ I, ∃ p,
      (∏ i ∈ Ioc 0 t, (1 - η i * (1 - γ))) * (C / (1 - γ)) +
        (3 * √(tdNoiseVarBound M γ η Q₀
            (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) t ω p *
          max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) +
        2 * b * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) <
      |syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p|} ≤
      ENNReal.ofReal (2 * Fintype.card 𝓢 * #I * δ) := by
  refine (measure_mono fun ω hω ↦ ?_).trans ((measure_biUnion_finset_le I _).trans
    ((sum_le_sum fun t ht ↦ measure_exists_lt_abs_syncQLearning_sub_optQValue_le hγ hR hη hQ₀ hδ
      hb t (hvb t ht)).trans_eq ?_))
  · obtain ⟨t, ht, hω⟩ := hω
    exact Set.mem_biUnion ht hω
  · rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

end TD

end LMLExplore.ReinforcementLearning
