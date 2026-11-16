/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.Exp4.Basic
public import LMLExplore.Bandits.Exp4.PseudoRegret

/-!
# Regret of Exp3 and Exp4 against oblivious adversaries

An oblivious adversary fixes in advance a reward table `x : ℕ → α → ℝ` and, in a bandit with
expert advice, the advice `E : ℕ → β → simplex α` of the experts: the learner observes the advice
`E t` at round `t` and receives the reward `x t (A t)` of its action. For rewards in `[0, 1]`, with
`k` arms and `M` experts, Exp3 with learning rate `η > 0` has adversarial regret
`R_n(x) ≤ log k / η + η n k / 2` and Exp4 has regret against the best expert
`R_n ≤ log M / η + η n k / 2`; the learning rates `η = √(2 log k / (n k))` and
`η = √(2 log M / (n k))` give [LS, Theorem 11.2] `R_n(x) ≤ √(2 n k log k)` and
[LS, Theorem 18.1] `R_n ≤ √(2 n k log M)`.

These bounds are the bounds on the pseudo-regret against any environment of
`LMLExplore/Bandits/Exp4/PseudoRegret.lean`, for an environment whose observations and feedbacks
are almost surely those of the table: there the pseudo-regret is the adversarial regret
(`Exp3.pseudoRegret_eq_advRegret`) and the expert pseudo-regret is the regret against the advice
(`Exp4IX.expertPseudoRegret_eq_expertRegret`). The environments `Environment.evalSeq x _` of LML
and `Environment.ofSeq E x _` are such environments.

## Main statements

* `Exp3.advRegret_le`: for a run of Exp3 whose feedback is the reward `x t (A t) ∈ [0, 1]` of its
  action, `R_n(x) ≤ log k / η + η n k / 2`.
* `Exp3.advRegret_le_sqrt`: [LS, Theorem 11.2]. With `η = √(2 log k / (n k))`,
  `R_n(x) ≤ √(2 n k log k)`.
* `exp3_advRegret_le`, `exp3_advRegret_le_sqrt`: the same bounds for runs against LML's
  `Environment.evalSeq x _`.
* `Exp4.expertRegret_le`: for a run of Exp4 whose observations are the advice `E t` and whose
  feedback is the reward `x t (A t) ∈ [0, 1]` of its action, `R_n ≤ log M / η + η n k / 2`.
* `Exp4.expertRegret_nonpos_of_subsingleton`: with a single expert, the regret is nonpositive.
* `Exp4.expertRegret_le_sqrt`: [LS, Theorem 18.1]. With `η = √(2 log M / (n k))`,
  `R_n ≤ √(2 n k log M)`.
* `exp4_expertRegret_le`, `exp4_expertRegret_le_sqrt`: the same bounds for runs against
  `Environment.ofSeq E x _`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real

namespace LMLExplore.Bandits

variable {α β Ω : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [Nonempty α] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {x : ℕ → α → ℝ} {n : ℕ} {η : ℝ}

namespace Exp3

variable {𝓞 : Type*} [MeasurableSpace 𝓞] {O : ℕ → Ω → 𝓞} {env : Environment 𝓞 α ℝ}

/-- **Regret of Exp3.** Along a run of Exp3 with learning rate `η > 0` whose feedback at every
round `t < n` is the reward `x t (A t) ∈ [0, 1]` of its action, the adversarial regret after `n`
rounds is at most `log k / η + η n k / 2`, with `k` the number of arms. -/
theorem advRegret_le (hη : 0 < η) (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t)
    (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1) (h : IsAlgEnvSeq O A Y (exp3 η) env P) :
    advRegret x A P n ≤ log (Fintype.card α) / η + η * n * Fintype.card α / 2 := by
  rw [← pseudoRegret_eq_advRegret (by rwa [exp3_def] at h) hY]
  exact pseudoRegret_le h hη (ae_feedback_mem_Icc hY hx)

/-- **Regret of Exp3** [LS, Theorem 11.2]: along a run of Exp3 with learning rate
`η = √(2 log k / (n k))` whose feedback at every round `t < n` is the reward `x t (A t) ∈ [0, 1]`
of its action, the adversarial regret after `n` rounds is at most `√(2 n k log k)`, with `k` the
number of arms. -/
theorem advRegret_le_sqrt (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t)
    (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3 √(2 * log (Fintype.card α) / (n * Fintype.card α))) env P) :
    advRegret x A P n ≤ √(2 * n * Fintype.card α * log (Fintype.card α)) := by
  rw [← pseudoRegret_eq_advRegret (by rwa [exp3_def] at h) hY]
  exact pseudoRegret_le_sqrt h (ae_feedback_mem_Icc hY hx)

end Exp3

section EvalSeq

variable {O : ℕ → Ω → Unit} {hxm : ∀ t, Measurable (x t)}

/-- **Regret of Exp3** against an oblivious adversary: along a run of Exp3 with learning rate
`η > 0` against LML's evaluation environment `Environment.evalSeq x _` with rewards in `[0, 1]` at
the rounds `t < n`, the adversarial regret after `n` rounds is at most `log k / η + η n k / 2`. -/
theorem exp3_advRegret_le (hη : 0 < η) (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp3 η) (Environment.evalSeq x hxm) P) :
    advRegret x A P n ≤ log (Fintype.card α) / η + η * n * Fintype.card α / 2 :=
  Exp3.advRegret_le hη (fun t _ ↦ h.feedback_ae_eq_evalSeq t) hx h

/-- **Regret of Exp3** [LS, Theorem 11.2]: along a run of Exp3 with learning rate
`η = √(2 log k / (n k))` against LML's evaluation environment `Environment.evalSeq x _` with rewards
in `[0, 1]` at the rounds `t < n`, the adversarial regret after `n` rounds is at most
`√(2 n k log k)`, with `k` the number of arms. -/
theorem exp3_advRegret_le_sqrt (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y
      (exp3 √(2 * log (Fintype.card α) / (n * Fintype.card α))) (Environment.evalSeq x hxm) P) :
    advRegret x A P n ≤ √(2 * n * Fintype.card α * log (Fintype.card α)) :=
  Exp3.advRegret_le_sqrt (fun t _ ↦ h.feedback_ae_eq_evalSeq t) hx h

end EvalSeq

variable [Fintype β] [Nonempty β] {O : ℕ → Ω → β → simplex α} {E : ℕ → β → simplex α}

namespace Exp4

variable {env : Environment (β → simplex α) α ℝ}

/-- **Regret of Exp4.** Along a run of Exp4 with learning rate `η > 0` whose observation of every
round `t < n` is the advice `E t` and whose feedback is the reward `x t (A t) ∈ [0, 1]` of its
action, the regret against the best expert after `n` rounds is at most `log M / η + η n k / 2`,
with `k` the number of arms and `M` the number of experts. -/
theorem expertRegret_le (hη : 0 < η) (hO : ∀ t < n, O t =ᵐ[P] fun _ ↦ E t)
    (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t) (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp4 η) env P) :
    expertRegret (fun t m ↦ (E t m : α → ℝ)) x A P n ≤
      log (Fintype.card β) / η + η * n * Fintype.card α / 2 := by
  rw [exp4_def] at h
  refine (Exp4IX.expertPseudoRegret_eq_expertRegret h hO hY).symm.trans_le
    ((Exp4IX.expertPseudoRegret_le h (fun _ ↦ hη) antitone_const (fun _ ↦ le_rfl)
      (ae_feedback_mem_Icc hY hx)).trans_eq ?_)
  simp only [Pi.zero_apply, zero_add, sum_const, card_range, nsmul_eq_mul]
  ring

/-- **Regret of Exp4 with a single expert.** Along a run of Exp4 with any learning rate whose
observation of every round `t < n` is the advice `E t` of the single expert and whose feedback is
the reward `x t (A t) ∈ [0, 1]` of its action, the regret against that expert is nonpositive: Exp4
follows the advice. -/
theorem expertRegret_nonpos_of_subsingleton [Subsingleton β]
    (hO : ∀ t < n, O t =ᵐ[P] fun _ ↦ E t) (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t)
    (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1) (h : IsAlgEnvSeq O A Y (exp4 η) env P) :
    expertRegret (fun t m ↦ (E t m : α → ℝ)) x A P n ≤ 0 := by
  rw [exp4_def] at h
  exact (Exp4IX.expertPseudoRegret_eq_expertRegret h hO hY).symm.trans_le
    (Exp4IX.expertPseudoRegret_nonpos_of_subsingleton h (ae_feedback_mem_Icc hY hx))

/-- **Regret of Exp4** [LS, Theorem 18.1]: along a run of Exp4 with learning rate
`η = √(2 log M / (n k))` whose observation of every round `t < n` is the advice `E t` and whose
feedback is the reward `x t (A t) ∈ [0, 1]` of its action, the regret against the best expert after
`n` rounds is at most `√(2 n k log M)`, with `k` the number of arms and `M` the number of
experts. -/
theorem expertRegret_le_sqrt (hO : ∀ t < n, O t =ᵐ[P] fun _ ↦ E t)
    (hY : ∀ t < n, Y t =ᵐ[P] x t ∘ A t) (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp4 √(2 * log (Fintype.card β) / (n * Fintype.card α))) env P) :
    expertRegret (fun t m ↦ (E t m : α → ℝ)) x A P n ≤
      √(2 * n * Fintype.card α * log (Fintype.card β)) := by
  rw [exp4_def] at h
  exact (Exp4IX.expertPseudoRegret_eq_expertRegret h hO hY).symm.trans_le
    (Exp4IX.expertPseudoRegret_le_sqrt h (ae_feedback_mem_Icc hY hx))

end Exp4

section OfSeq

variable {hxm : ∀ t, Measurable (x t)}

/-- **Regret of Exp4** against oblivious experts and rewards: along a run of Exp4 with learning
rate `η > 0` against `Environment.ofSeq E x _`, which announces the advice `E t` and pays the
reward `x t a ∈ [0, 1]` of the action `a` at the rounds `t < n`, the regret against the best expert
after `n` rounds is at most `log M / η + η n k / 2`. -/
theorem exp4_expertRegret_le (hη : 0 < η) (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp4 η) (Environment.ofSeq E x hxm) P) :
    expertRegret (fun t m ↦ (E t m : α → ℝ)) x A P n ≤
      log (Fintype.card β) / η + η * n * Fintype.card α / 2 :=
  Exp4.expertRegret_le hη (fun t _ ↦ h.obs_ofSeq_ae_eq t) (fun t _ ↦ h.feedback_ofSeq_ae_eq t) hx h

/-- **Regret of Exp4** [LS, Theorem 18.1]: along a run of Exp4 with learning rate
`η = √(2 log M / (n k))` against `Environment.ofSeq E x _`, which announces the advice `E t` and
pays the reward `x t a ∈ [0, 1]` of the action `a` at the rounds `t < n`, the regret against the
best expert after `n` rounds is at most `√(2 n k log M)`, with `k` the number of arms and `M` the
number of experts. -/
theorem exp4_expertRegret_le_sqrt (hx : ∀ t < n, ∀ a, x t a ∈ Set.Icc 0 1)
    (h : IsAlgEnvSeq O A Y (exp4 √(2 * log (Fintype.card β) / (n * Fintype.card α)))
      (Environment.ofSeq E x hxm) P) :
    expertRegret (fun t m ↦ (E t m : α → ℝ)) x A P n ≤
      √(2 * n * Fintype.card α * log (Fintype.card β)) :=
  Exp4.expertRegret_le_sqrt (fun t _ ↦ h.obs_ofSeq_ae_eq t) (fun t _ ↦ h.feedback_ofSeq_ae_eq t)
    hx h

end OfSeq

end LMLExplore.Bandits
