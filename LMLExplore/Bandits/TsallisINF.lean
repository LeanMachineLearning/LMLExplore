/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Convex.Tsallis
public import LMLExplore.Bandits.ImportanceWeighted
public import LMLExplore.Bandits.WeightAlgorithm

/-!
# Tsallis-INF

Tsallis-INF [ZS21], [Ora, Algorithm 9.6] is the weight-based algorithm for
adversarial bandits with finitely many arms `α` that plays at round `t` the weights
`P t = argmin_{p ∈ simplex α} (⟨L̂ t, p⟩ - 4 √(t + 1) ∑ a, √(p a))`: follow the regularized leader
on the cumulative loss estimates `L̂ t = ∑ s < t, Ŷ s` with the ½-Tsallis potential
`-∑ a, √(p a)`, whose coefficient `4 √(t + 1)` grows with the rounds and does not depend on a
horizon. The estimates
`Ŷ s a = 𝟙{A s = a} (1 - X s) / P s a` are the importance-weighted estimates of the losses
`1 - X s`, computed from the arm `A s` drawn from `P s` and its observed reward `X s`. Tsallis-INF
ignores the observations of the environment.

The weights are the Tsallis weights `tsallisWeights (4 √(t + 1)) (L̂ t)`, the unique minimizer of
the objective over the simplex. All of them are positive, so the loss estimates are conditionally
unbiased, and they do not change when a constant is added to every coordinate of a loss estimate:
the analysis of Tsallis-INF runs follow the regularized leader on the estimates shifted by the
loss of the played arm.

## Main definitions

* `LMLExplore.Bandits.tsallisINFSum n h`: the cumulative loss estimates `L̂ n` of Tsallis-INF,
  computed from the history `h` of the first `n` rounds.
* `LMLExplore.Bandits.tsallisINFWeights n h`: the weights
  `P n = tsallisWeights (4 √(n + 1)) (L̂ n)` of Tsallis-INF at round `n`.
* `LMLExplore.Bandits.tsallisINF`: the Tsallis-INF algorithm.

## Main statements

* `tsallisINFWeights_pos`, `tsallisINFWeights_mem_simplex`: the weights are positive and form a
  probability vector.
* `tsallisINFWeights_zero`: the first weights are uniform.
* `isMinOn_tsallisINFWeights`, `isMinOn_iff_eq_tsallisINFWeights`: the weights of round `n`
  minimize `p ↦ ⟨L̂ n, p⟩ - 4 √(n + 1) ∑ a, √(p a)` over the simplex, and they are its only
  minimizer there.
* `tsallisINFWeights_history_eq`: along every sequence of actions and feedbacks, the weights of
  round `n` are the Tsallis weights of the cumulative importance-weighted loss estimates of the
  rounds `t < n`.
* `tsallisINFWeights_history_eq_add_const`: the same holds after adding a constant `r t` to every
  coordinate of the estimate of each round `t`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
* [ZS21] J. Zimmert and Y. Seldin, *Tsallis-INF: an optimal algorithm for stochastic and
  adversarial bandits*, JMLR 22 (2021).
-/

public section

open MeasureTheory Learning Finset

namespace LMLExplore.Bandits

variable {α 𝓞 : Type*} [Fintype α] [DecidableEq α]

section Weights

/-- The cumulative loss estimates of Tsallis-INF, computed from the history `h` of the first `n`
rounds: `∑ s < n, Ŷ s` with `Ŷ s = iwEstimator (P s) (A s) (1 - X s)` the importance-weighted
estimate of the losses of round `s`, for the action `A s` and the reward `X s` of round `s` of `h`
and the weights `P s = tsallisWeights (4 √(s + 1)) (∑ r < s, Ŷ r)` of round `s`. -/
noncomputable def tsallisINFSum : (n : ℕ) → Hist 𝓞 α ℝ n → α → ℝ
  | 0, _ => 0
  | n + 1, h => tsallisINFSum n (Fin.init h) +
      iwEstimator (tsallisWeights (4 * √((n : ℝ) + 1)) (tsallisINFSum n (Fin.init h)))
        (h (Fin.last n)).action (1 - (h (Fin.last n)).feedback)

/-- The weights of Tsallis-INF after the history `h` of the first `n` rounds: the Tsallis weights
with coefficient `4 √(n + 1)` of the cumulative loss estimates `tsallisINFSum n h`, which minimize
`p ↦ ⟨tsallisINFSum n h, p⟩ - 4 √(n + 1) ∑ a, √(p a)` over the simplex. -/
noncomputable def tsallisINFWeights (n : ℕ) (h : Hist 𝓞 α ℝ n) : α → ℝ :=
  tsallisWeights (4 * √((n : ℝ) + 1)) (tsallisINFSum n h)

lemma tsallisINFWeights_def (n : ℕ) (h : Hist 𝓞 α ℝ n) :
    tsallisINFWeights n h = tsallisWeights (4 * √((n : ℝ) + 1)) (tsallisINFSum n h) := (rfl)

@[simp]
lemma tsallisINFSum_zero (h : Hist 𝓞 α ℝ 0) : tsallisINFSum 0 h = 0 := by
  rw [tsallisINFSum]

lemma tsallisINFSum_succ (n : ℕ) (h : Hist 𝓞 α ℝ (n + 1)) :
    tsallisINFSum (n + 1) h = tsallisINFSum n (Fin.init h) +
      iwEstimator (tsallisINFWeights n (Fin.init h)) (h (Fin.last n)).action
        (1 - (h (Fin.last n)).feedback) := by
  rw [tsallisINFSum, tsallisINFWeights_def]

/-- The coefficient `4 √(n + 1)` of the potential of Tsallis-INF is positive. -/
private lemma four_mul_sqrt_add_one_pos (n : ℕ) : 0 < 4 * √((n : ℝ) + 1) := by positivity

variable [Nonempty α]

/-- The first weights of Tsallis-INF are uniform. -/
@[simp]
lemma tsallisINFWeights_zero (h : Hist 𝓞 α ℝ 0) :
    tsallisINFWeights 0 h = fun _ ↦ (Fintype.card α : ℝ)⁻¹ := by
  rw [tsallisINFWeights_def, tsallisINFSum_zero]
  exact tsallisWeights_const (four_mul_sqrt_add_one_pos 0).ne' 0

lemma tsallisINFWeights_pos (n : ℕ) (h : Hist 𝓞 α ℝ n) (a : α) :
    0 < tsallisINFWeights n h a :=
  tsallisWeights_pos (four_mul_sqrt_add_one_pos n).ne' _ a

lemma tsallisINFWeights_mem_simplex (n : ℕ) (h : Hist 𝓞 α ℝ n) :
    tsallisINFWeights n h ∈ simplex α :=
  tsallisWeights_mem_simplex (four_mul_sqrt_add_one_pos n).ne' _

/-- **The weights of Tsallis-INF as follow the regularized leader.** The weights of round `n`
minimize `p ↦ ⟨L̂ n, p⟩ - 4 √(n + 1) ∑ a, √(p a)` over the simplex, with `L̂ n` the cumulative loss
estimates. -/
theorem isMinOn_tsallisINFWeights (n : ℕ) (h : Hist 𝓞 α ℝ n) :
    IsMinOn (fun p ↦ tsallisINFSum n h ⬝ᵥ p - 4 * √((n : ℝ) + 1) * ∑ a, √(p a)) (simplex α)
      (tsallisINFWeights n h) :=
  isMinOn_tsallisWeights (four_mul_sqrt_add_one_pos n) _

/-- The weights of round `n` are the only minimizer over the simplex of
`p ↦ ⟨L̂ n, p⟩ - 4 √(n + 1) ∑ a, √(p a)`. -/
theorem isMinOn_iff_eq_tsallisINFWeights (n : ℕ) (h : Hist 𝓞 α ℝ n) {q : α → ℝ}
    (hq : q ∈ simplex α) :
    IsMinOn (fun p ↦ tsallisINFSum n h ⬝ᵥ p - 4 * √((n : ℝ) + 1) * ∑ a, √(p a)) (simplex α) q ↔
      q = tsallisINFWeights n h :=
  isMinOn_iff_eq_tsallisWeights (four_mul_sqrt_add_one_pos n) hq

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞]

@[fun_prop]
lemma measurable_tsallisINFSum (n : ℕ) : Measurable (tsallisINFSum (𝓞 := 𝓞) (α := α) n) := by
  induction n with
  | zero =>
    rw [funext tsallisINFSum_zero]
    exact measurable_const
  | succ n ih =>
    have hS := ih.comp (measurable_finInit (β := fun _ ↦ _))
    have hP := measurable_tsallisWeights (α := α) (four_mul_sqrt_add_one_pos n).ne'
    rw [funext (tsallisINFSum_succ n)]
    simp_rw [tsallisINFWeights_def]
    fun_prop

@[fun_prop]
lemma measurable_tsallisINFWeights (n : ℕ) :
    Measurable (tsallisINFWeights (𝓞 := 𝓞) (α := α) n) :=
  (measurable_tsallisWeights (four_mul_sqrt_add_one_pos n).ne').comp (measurable_tsallisINFSum n)

end Weights

section Algorithm

variable [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace 𝓞]

/-- **Tsallis-INF** [ZS21], [Ora, Algorithm 9.6]: the weight-based algorithm that draws its
action of round `n` from the weights `tsallisINFWeights n h`, the minimizer over the simplex of
`p ↦ ⟨L̂ n, p⟩ - 4 √(n + 1) ∑ a, √(p a)` for the cumulative importance-weighted loss estimates
`L̂ n` computed from the history `h`. It ignores the observations. -/
noncomputable def tsallisINF : Algorithm 𝓞 α ℝ :=
  weightAlgorithm (fun n x ↦ tsallisINFWeights n x.1)
    (fun n a ↦ (measurable_pi_apply a).comp ((measurable_tsallisINFWeights n).comp measurable_fst))
    (fun n x ↦ tsallisINFWeights_mem_simplex n x.1)

lemma tsallisINF_def :
    tsallisINF (𝓞 := 𝓞) (α := α) = weightAlgorithm (fun n x ↦ tsallisINFWeights n x.1)
      (fun n a ↦ (measurable_pi_apply a).comp ((measurable_tsallisINFWeights n).comp
        measurable_fst))
      (fun n x ↦ tsallisINFWeights_mem_simplex n x.1) := (rfl)

/-- The policy of Tsallis-INF at round `n` draws its action from the weights
`tsallisINFWeights n h` of the history `h`. -/
@[simp]
lemma tsallisINF_policy_apply (n : ℕ) (x : Hist 𝓞 α ℝ n × 𝓞) :
    (tsallisINF (𝓞 := 𝓞) (α := α)).policy n x = weightedMeasure (tsallisINFWeights n x.1) := by
  rw [tsallisINF_def, weightAlgorithm_policy, weightKernel_apply]

end Algorithm

section History

variable {Ω : Type*} (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ)

/-- Along a sequence of observations `O`, actions `A` and feedbacks `Y`, the cumulative loss
estimates of Tsallis-INF after `n` rounds are the sums of the importance-weighted estimates of the
losses `1 - Y t` of the rounds `t < n`. -/
lemma tsallisINFSum_history (n : ℕ) (ω : Ω) :
    tsallisINFSum n (history O A Y n ω) = ∑ t ∈ range n,
      iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω) := by
  induction n with
  | zero => simp
  | succ n ih => simp [tsallisINFSum_succ, Finset.sum_range_succ, ih, history_apply]

/-- **Tsallis-INF as follow the regularized leader along a run.** Along a sequence of
observations `O`, actions `A` and feedbacks `Y`, the weights of Tsallis-INF at round `n` are the
Tsallis weights with coefficient `4 √(n + 1)` of the cumulative importance-weighted estimates of
the losses `1 - Y t` of the rounds `t < n`. -/
lemma tsallisINFWeights_history_eq (n : ℕ) (ω : Ω) :
    tsallisINFWeights n (history O A Y n ω) = tsallisWeights (4 * √((n : ℝ) + 1)) (∑ t ∈ range n,
      iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω) (1 - Y t ω)) := by
  rw [tsallisINFWeights_def, tsallisINFSum_history]

/-- **Shift invariance along a run.** Adding a constant `r t` to every coordinate of the
importance-weighted loss estimate of each round `t < n` does not change the weights of
Tsallis-INF at round `n`. -/
lemma tsallisINFWeights_history_eq_add_const [Nonempty α] (r : ℕ → ℝ) (n : ℕ) (ω : Ω) :
    tsallisINFWeights n (history O A Y n ω) = tsallisWeights (4 * √((n : ℝ) + 1))
      (fun a ↦ ∑ t ∈ range n, (iwEstimator (tsallisINFWeights t (history O A Y t ω)) (A t ω)
        (1 - Y t ω) a + r t)) := by
  simp_rw [sum_add_distrib]
  rw [tsallisWeights_add_const (four_mul_sqrt_add_one_pos n).ne', tsallisINFWeights_history_eq]
  congr 1
  funext a
  simp

end History

end LMLExplore.Bandits
