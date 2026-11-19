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

This file develops that unrolling and its first probabilistic consequence.
* **The propagators.** For a finite kernel `κ` on a finite space, `κ.tdStep γ c = I - c (I - γ κ)`
  and `κ.tdPropagator γ η k t = (I - η t (I - γ κ)) ⋯ (I - η (k + 1) (I - γ κ))`. For learning
  rates in `[0, 1]`, the propagators are positive operators which multiply constants by
  `∏_{i = k + 1}^t (1 - η i (1 - γ))` [LCCWC24, (109)], and their weighted sums are dominated by
  the resolvent: `∑_{k = m + 1}^t η k Φ k t f ≤ (I - γ κ)⁻¹ f` for `f ≥ 0`
  [LCCWC24, Section C.2, proof of (117)].
* **The error decomposition** [LCCWC24, (110)–(111)]: with one action and the state-action kernel
  `P` of the unique policy, `Δ t = Φ 0 t Δ 0 + ∑_{k < t} η (k + 1) γ Φ (k + 1) t (P_{k+1} - P) V k`.
* **Freedman's inequality for the noise** [LCCWC24, (113)–(116)]: each entry of the noise term is
  a sum of martingale differences under the generative model, whose conditional variances are
  bounded by the entries of `Φ (k + 1) t Var_P(V k)`. Freedman's inequality and a union bound over
  the entries and the two signs bound the error of the `t`-th iterate with high probability by
  `ρ 0 t C / (1 - γ) + 3 √(W ℓ) + 2 b ℓ`, with `ρ k t = ∏_{i = k + 1}^t (1 - η i (1 - γ))`, the
  quadratic variation bound
  `W = ∑_{k < t} (η (k + 1) γ) ^ 2 ρ (k + 1) t Φ (k + 1) t Var_P(V k)`, a bound `b` on the
  increments and a logarithmic factor `ℓ`.

The deterministic analysis of the quadratic variation for rescaled linear learning rates and the
resulting sample complexity are not in this file.

## Main definitions

* `ProbabilityTheory.Kernel.tdStep κ γ c`: the step `I - c (I - γ κ)` of the mean dynamics.
* `ProbabilityTheory.Kernel.tdPropagator κ γ η k t`: the propagator `Φ k t` of the mean dynamics
  from iteration `k` to iteration `t`.

## Main statements

* `ProbabilityTheory.Kernel.tdPropagator_nonneg`, `ProbabilityTheory.Kernel.tdPropagator_const`,
  `ProbabilityTheory.Kernel.abs_tdPropagator_le`: positivity, action on constants and the
  resulting sup-norm bound [LCCWC24, (109)].
* `ProbabilityTheory.Kernel.tdPropagator_apply_eq_sum`: the propagator as a matrix.
* `ProbabilityTheory.Kernel.sum_mul_tdPropagator_le_integral_resolvent`: domination of the
  weighted sums of propagators by the resolvent.
* `LMLExplore.ReinforcementLearning.syncQLearning_succ_sub_optQValue_eq_tdStep`,
  `LMLExplore.ReinforcementLearning.syncQLearning_sub_optQValue_eq_tdPropagator`: the error
  recursion and its unrolled form [LCCWC24, (110)–(111)].
* `LMLExplore.ReinforcementLearning.measure_three_mul_sqrt_add_lt_mul_sum_tdPropagator_le`:
  Freedman's inequality for each entry of the noise term.
* `LMLExplore.ReinforcementLearning.measure_exists_lt_abs_syncQLearning_sub_optQValue_le`: the
  high-probability bound on the error of the `t`-th iterate.

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
    · -- the sum at `t + 1` is the image of the sum at `t` under the step `t + 1`, plus `η f`
      have hsum : ∑ k ∈ Ioc m (t + 1), η k * tdPropagator κ γ η k (t + 1) f x =
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
      have hη' : η (t + 1) ∈ Set.Icc (0 : ℝ) 1 := hη _ (mem_Ioc.2 ⟨by omega, le_rfl⟩)
      have hle := tdStep_nonneg (κ := κ) (γ := γ) hη'
        (sub_nonneg.2 (fun x ↦ ih (fun i hi ↦ hη i (Ioc_subset_Ioc_right t.le_succ hi)) x :
          (fun x ↦ ∑ k ∈ Ioc m t, η k * tdPropagator κ γ η k t f x) ≤ u)) x
      rw [map_sub, Pi.sub_apply, Pi.zero_apply, sub_nonneg] at hle
      calc _ = _ := hsum
        _ ≤ tdStep κ γ (η (t + 1)) u x + η (t + 1) * f x := by linarith
        _ = u x := hfix _ x
    · rw [Ioc_eq_empty (by omega), sum_empty]
      exact integral_nonneg hf

end ProbabilityTheory.Kernel

namespace LMLExplore.ReinforcementLearning

/-! ### The error decomposition of synchronous TD learning -/

section TD

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Finite 𝓢]
  [Nonempty 𝓢] [MeasurableSingletonClass 𝓢] [Unique 𝓐] [MeasurableSingletonClass 𝓐]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {η : ℕ → ℝ} {Q₀ : 𝓢 × 𝓐 → ℝ} {C : ℝ}

/-- **One step of the error of synchronous TD learning** [LCCWC24, (110)]. With one action, the
error `Δ t = Q t - Q*` satisfies
`Δ (t + 1) = (I - η (t + 1) (I - γ P)) Δ t + η (t + 1) γ (P_{t+1} - P) V t`, where `P` is the
state-action kernel of the unique policy and `(P_{t+1} - P) V t p = V t (ω t p) - P V t p` is the
sampling noise of the value estimate `V t s = Q t (s, default)`. -/
theorem syncQLearning_succ_sub_optQValue_eq_tdStep (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (t : ℕ) (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) :
    syncQLearning (meanReward M.R) γ η Q₀ (t + 1) ω p - M.optQValue γ p =
      Kernel.tdStep
        (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) γ (η (t + 1))
          (fun q ↦ syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q) p +
        η (t + 1) * γ * (syncQLearning (meanReward M.R) γ η Q₀ t ω (ω t p, default) -
          ∫ s', syncQLearning (meanReward M.R) γ η Q₀ t ω (s', default) ∂(M.P p)) := by
  have hv (s : 𝓢) : M.optQValue γ (s, default) = M.optValue γ s := by
    rw [← iSup_optQValue hγ hR s, ciSup_unique]
  rw [syncQLearning_succ_sub_optQValue, ciSup_unique, Kernel.tdStep_apply,
    integral_saKernel_deterministic _ .of_finite]
  simp only [hv]
  rw [integral_sub (.of_finite) (.of_finite)]
  ring

/-- **The error decomposition of synchronous TD learning** [LCCWC24, (111)]. With one action, the
error `Δ t = Q t - Q*` is
`Δ t = Φ 0 t Δ 0 + ∑_{k < t} η (k + 1) γ Φ (k + 1) t (P_{k+1} - P) V k`, where `Φ k t` is the
propagator of the mean dynamics with the state-action kernel `P` of the unique policy and
`(P_{k+1} - P) V k p = V k (ω k p) - P V k p` is the sampling noise of the value estimate
`V k s = Q k (s, default)` at iteration `k + 1`. -/
theorem syncQLearning_sub_optQValue_eq_tdPropagator (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (t : ℕ) (ω : ℕ → 𝓢 × 𝓐 → 𝓢) (p : 𝓢 × 𝓐) :
    syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p =
      Kernel.tdPropagator
        (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) γ η 0 t
          (fun q ↦ Q₀ q - M.optQValue γ q) p +
        ∑ k ∈ range t, η (k + 1) * γ *
          Kernel.tdPropagator
            (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) γ η
            (k + 1) t (fun q ↦ syncQLearning (meanReward M.R) γ η Q₀ k ω (ω k q, default) -
              ∫ s', syncQLearning (meanReward M.R) γ η Q₀ k ω (s', default) ∂(M.P q)) p := by
  set κ := M.saKernel (Kernel.deterministic (fun _ : 𝓢 ↦ (default : 𝓐)) measurable_const)
  set N : ℕ → 𝓢 × 𝓐 → ℝ := fun k q ↦ syncQLearning (meanReward M.R) γ η Q₀ k ω (ω k q, default) -
    ∫ s', syncQLearning (meanReward M.R) γ η Q₀ k ω (s', default) ∂(M.P q)
  suffices h : (fun q ↦ syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q) =
      κ.tdPropagator γ η 0 t (fun q ↦ Q₀ q - M.optQValue γ q) +
        ∑ k ∈ range t, (η (k + 1) * γ) • κ.tdPropagator γ η (k + 1) t (N k) by
    rw [congrFun h p]
    simp [Finset.sum_apply, κ, N]
  induction t with
  | zero => simp
  | succ t ih =>
    have hstep : (fun q ↦ syncQLearning (meanReward M.R) γ η Q₀ (t + 1) ω q - M.optQValue γ q) =
        κ.tdStep γ (η (t + 1)) (fun q ↦ syncQLearning (meanReward M.R) γ η Q₀ t ω q -
          M.optQValue γ q) + (η (t + 1) * γ) • N t := by
      funext q
      rw [syncQLearning_succ_sub_optQValue_eq_tdStep hγ hR, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
    rw [hstep, ih, map_add, map_sum, sum_range_succ, Kernel.tdPropagator_self,
      Kernel.tdPropagator_succ (Nat.zero_le t), mul_apply_eq_comp, one_apply_eq_self, add_assoc]
    congr 2
    refine sum_congr rfl fun k hk ↦ ?_
    rw [map_smul, Kernel.tdPropagator_succ (mem_range.1 hk), mul_apply_eq_comp]

/-- Learning rates in `[0, 1]` from iteration `1` on are in `[0, 1]` on every `Ioc k t`. -/
private lemma mem_Icc_of_mem_Ioc (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1) {k t i : ℕ}
    (hi : i ∈ Ioc k t) : η i ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by have := (mem_Ioc.1 hi).1; omega⟩
  exact hη j

omit [Nonempty 𝓢] in
/-- **Freedman's inequality for the noise of synchronous TD learning**, one-sided
[LCCWC24, (113)–(116)]. With one action, rewards in `[0, C]`, learning rates in `[0, 1]` and
`0 ≤ Q₀ ≤ C / (1 - γ)`, let `σ` be `1` or `-1` and `b > 0` with
`η (k + 1) γ ρ (k + 1) t C / (1 - γ) ≤ b` for every `k < t`, where
`ρ k t = ∏_{i = k + 1}^t (1 - η i (1 - γ))`. Then for every pair `p`, with probability at least
`1 - δ`, the noise `ξ t p = ∑_{k < t} η (k + 1) γ Φ (k + 1) t ((P_{k+1} - P) V k) p` of the error
decomposition satisfies `σ ξ t p ≤ 3 √(W ℓ) + 2 b ℓ`, with
`W = ∑_{k < t} (η (k + 1) γ) ^ 2 ρ (k + 1) t Φ (k + 1) t Var_P(V k) p`,
`ℓ = max 1 (log (K / δ))` and `K = ⌈log₄ t⌉ + 1`. -/
theorem measure_three_mul_sqrt_add_lt_mul_sum_tdPropagator_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ))) {δ b σ : ℝ} (hδ : 0 < δ) (hb : 0 < b)
    (hσ : |σ| = 1) (t : ℕ)
    (hvb : ∀ k < t, η (k + 1) * γ * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) * (C / (1 - γ)) ≤ b)
    (p : 𝓢 × 𝓐) :
    streamMeasure M.P {ω | 3 * √((∑ k ∈ range t, (η (k + 1) * γ) ^ 2 *
          (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) *
          Kernel.tdPropagator
            (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) γ η
            (k + 1) t (fun q ↦ Var[fun s' ↦ syncQLearning (meanReward M.R) γ η Q₀ k ω (s', default);
              M.P q]) p) * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) +
        2 * b * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ)) <
      σ * ∑ k ∈ range t, η (k + 1) * γ *
        Kernel.tdPropagator
          (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) γ η
          (k + 1) t (fun q ↦ syncQLearning (meanReward M.R) γ η Q₀ k ω (ω k q, default) -
            ∫ s', syncQLearning (meanReward M.R) γ η Q₀ k ω (s', default) ∂(M.P q)) p} ≤
      ENNReal.ofReal δ := by
  classical
  have := Fintype.ofFinite 𝓢
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  have hr (q : 𝓢 × 𝓐) : meanReward M.R q ∈ Set.Icc 0 C := by
    rw [meanReward_def]
    exact integral_mem_Icc_of_ae_mem_Icc aemeasurable_id (hR q)
  have hB : C + γ * (C / (1 - γ)) ≤ C / (1 - γ) := by
    refine le_of_eq ?_
    field_simp
    ring
  have hηk (k : ℕ) : ∀ i ∈ Ioc (k + 1) t, η i ∈ Set.Icc (0 : ℝ) 1 := fun i hi ↦
    mem_Icc_of_mem_Ioc hη hi
  have hc (k : ℕ) : |σ * (η (k + 1) * γ)| = η (k + 1) * γ := by
    rw [abs_mul, hσ, one_mul, abs_of_nonneg (mul_nonneg (hη k).1 γ.coe_nonneg)]
  -- the weights of the noises are `σ η (k + 1) γ` times the entries of `Φ (k + 1) t`
  have h := measure_three_mul_sqrt_add_lt_sum_sum_mul_iSup_syncQLearning_le (P := M.P) hη hr hQ₀
    hB hδ hb t
    (fun k y ↦ σ * (η (k + 1) * γ) * Kernel.tdPropagator (M.saKernel (Kernel.deterministic
      (fun _ ↦ default) measurable_const)) γ η (k + 1) t (Pi.single y 1) p) fun k hk ↦ by
        rw [Kernel.sum_abs_mul_tdPropagator_single (hηk k), hc]
        exact hvb k hk
  simp only [ciSup_unique] at h
  refine (measure_mono fun ω hω ↦ ?_).trans h
  simp only [Set.mem_ofPred_eq] at hω ⊢
  convert hω using 3
  · congr 2
    refine sum_congr rfl fun k _ ↦ ?_
    rw [Kernel.sum_abs_mul_tdPropagator_single (hηk k),
      Kernel.sum_abs_mul_tdPropagator_single_mul (hηk k), hc]
    ring
  · simp_rw [Kernel.sum_mul_tdPropagator_single_mul, mul_sum]
    exact sum_congr rfl fun k _ ↦ by ring

/-- **The high-probability error bound of synchronous TD learning** [LCCWC24, (112)–(116)]. With
one action, rewards in `[0, C]`, `γ < 1`, learning rates in `[0, 1]` and
`0 ≤ Q₀ ≤ C / (1 - γ)`, let `b > 0` with `η (k + 1) γ ρ (k + 1) t C / (1 - γ) ≤ b` for every
`k < t`, where `ρ k t = ∏_{i = k + 1}^t (1 - η i (1 - γ))`. Then with probability at least
`1 - 2 S δ`, with `S` the number of states, for every pair `p`, the error of the `t`-th iterate
satisfies `|Q t p - Q* p| ≤ ρ 0 t C / (1 - γ) + 3 √(W p ℓ) + 2 b ℓ`, with
`W p = ∑_{k < t} (η (k + 1) γ) ^ 2 ρ (k + 1) t Φ (k + 1) t Var_P(V k) p`,
`ℓ = max 1 (log (K / δ))` and `K = ⌈log₄ t⌉ + 1`: the initial error is contracted by the mean
dynamics and the sampling noise is controlled by Freedman's inequality. -/
theorem measure_exists_lt_abs_syncQLearning_sub_optQValue_le [Fintype 𝓢] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (C / (1 - γ))) {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b) (t : ℕ)
    (hvb : ∀ k < t,
      η (k + 1) * γ * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) * (C / (1 - γ)) ≤ b) :
    streamMeasure M.P {ω | ∃ p, (∏ i ∈ Ioc 0 t, (1 - η i * (1 - γ))) * (C / (1 - γ)) +
        (3 * √((∑ k ∈ range t, (η (k + 1) * γ) ^ 2 * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) *
          Kernel.tdPropagator
            (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) γ η
            (k + 1) t (fun q ↦ Var[fun s' ↦ syncQLearning (meanReward M.R) γ η Q₀ k ω (s', default);
              M.P q]) p) * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) +
        2 * b * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) <
      |syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p|} ≤
      ENNReal.ofReal (2 * Fintype.card 𝓢 * δ) := by
  have hRabs : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C := fun p ↦ (hR p).mono fun x hx ↦
    abs_le.2 ⟨by linarith [hx.1, hx.2], hx.2⟩
  have hηk : ∀ i ∈ Ioc 0 t, η i ∈ Set.Icc (0 : ℝ) 1 := fun i hi ↦ mem_Icc_of_mem_Ioc hη hi
  -- the noise exceeds its bound from above or from below at some pair
  set E : ℝ → 𝓢 × 𝓐 → Set (ℕ → 𝓢 × 𝓐 → 𝓢) := fun σ p ↦ {ω | 3 * √((∑ k ∈ range t,
      (η (k + 1) * γ) ^ 2 * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) *
        Kernel.tdPropagator
          (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) γ η
          (k + 1) t (fun q ↦ Var[fun s' ↦ syncQLearning (meanReward M.R) γ η Q₀ k ω (s', default);
            M.P q]) p) * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) +
      2 * b * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ)) <
    σ * ∑ k ∈ range t, η (k + 1) * γ *
      Kernel.tdPropagator (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) γ η
        (k + 1) t (fun q ↦ syncQLearning (meanReward M.R) γ η Q₀ k ω (ω k q, default) -
          ∫ s', syncQLearning (meanReward M.R) γ η Q₀ k ω (s', default) ∂(M.P q)) p} with hE
  have hsub : {ω | ∃ p, (∏ i ∈ Ioc 0 t, (1 - η i * (1 - γ))) * (C / (1 - γ)) +
        (3 * √((∑ k ∈ range t, (η (k + 1) * γ) ^ 2 * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) *
          Kernel.tdPropagator
            (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) γ η
            (k + 1) t (fun q ↦ Var[fun s' ↦ syncQLearning (meanReward M.R) γ η Q₀ k ω (s', default);
              M.P q]) p) * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) +
        2 * b * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) <
      |syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p|} ⊆
      ⋃ p, (E 1 p ∪ E (-1) p) := by
    intro ω ⟨p, hp⟩
    refine Set.mem_iUnion.2 ⟨p, ?_⟩
    -- the contracted initial error is at most `ρ 0 t C / (1 - γ)`
    have h₀ := Kernel.abs_tdPropagator_le
      (κ := M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) (γ := γ) hηk
      (f := fun q ↦ Q₀ q - M.optQValue γ q)
      (fun q ↦ by simpa using abs_syncQLearning_sub_optQValue_le (η := η) hγ hR hη hQ₀ 0 ω q) p
    rw [syncQLearning_sub_optQValue_eq_tdPropagator hγ hRabs] at hp
    have h₁ := (abs_add_le _ _).trans_lt' hp
    simp only [hE, Set.mem_union, Set.mem_ofPred_eq, one_mul, neg_one_mul]
    exact lt_abs.1 (by linarith)
  have hE₁ (σ : ℝ) (hσ : |σ| = 1) (p : 𝓢 × 𝓐) : streamMeasure M.P (E σ p) ≤ ENNReal.ofReal δ :=
    measure_three_mul_sqrt_add_lt_mul_sum_tdPropagator_le hγ hR hη hQ₀ hδ hb hσ t hvb p
  calc streamMeasure M.P _ ≤ streamMeasure M.P (⋃ p, (E 1 p ∪ E (-1) p)) := measure_mono hsub
    _ ≤ ∑ p, streamMeasure M.P (E 1 p ∪ E (-1) p) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : 𝓢 × 𝓐, (ENNReal.ofReal δ + ENNReal.ofReal δ) := sum_le_sum fun p _ ↦
        (measure_union_le _ _).trans (add_le_add (hE₁ 1 abs_one p) (hE₁ (-1) (by simp) p))
    _ = ENNReal.ofReal (2 * Fintype.card 𝓢 * δ) := by
        rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_unique (α := 𝓐), mul_one,
          nsmul_eq_mul, ← ENNReal.ofReal_add hδ.le hδ.le,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end TD

end LMLExplore.ReinforcementLearning
