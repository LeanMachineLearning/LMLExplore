/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.SequentialLearning.Environments.OfSeq

/-!
# Adversarial regret and regret against expert advice

In an adversarial bandit with finitely many arms `α`, an oblivious adversary fixes a reward table
`x : ℕ → α → ℝ` in advance: the reward of arm `a` at round `t` is `x t a`. The learner observes
only the reward `x t (A t)` of the arm it plays, which is a run against LML's evaluation
environment `onlineEvalEnv x _`. Its **adversarial regret** after `n` rounds is [LS, (11.1)]
`R_n(x) = max_a ∑_{t < n} x t a - E[∑_{t < n} x t (A t)]`,
the expected shortfall of its total reward against the best fixed arm in hindsight.

In a bandit with expert advice [LS, Chapter 18], each expert `m` of a set `β` recommends at round
`t` a distribution `E t m : α → ℝ` over the arms, and the learner sees this advice before acting:
a run against `Environment.ofSeq E x _`, whose observation at round `t` is the advice `E t`. The
regret against the best expert [LS, (18.6)] is
`max_m ∑_{t < n} ⟨E t m, x t⟩ - E[∑_{t < n} x t (A t)]`,
with `⟨E t m, x t⟩ = ∑_a E t m a * x t a` the expected reward of following expert `m` at round `t`.
With the experts `α` that each recommend one arm, it is the adversarial regret.

Both regrets compare an expected reward with a deterministic benchmark, as the table and the advice
are fixed in advance. Rewards are maximized, as for LML's stochastic `regret`. They may be
negative, since a learner that switches arms can beat every fixed arm.

## Main definitions

* `LMLExplore.Bandits.advRegret x A P n`: the adversarial regret `R_n(x)` of the actions `A` under
  `P`.
* `LMLExplore.Bandits.expertRegret E x A P n`: the regret of the actions `A` under `P` against the
  best expert of the advice `E`.

## Main statements

* `advRegret_le_iff`, `sum_sub_integral_le_advRegret`: the adversarial regret is at most `B` iff
  the regret against every fixed arm is at most `B`; it is at least the regret against any fixed
  arm.
* `Learning.IsAlgEnvSeq.advRegret_eq_sub_integral_sum_feedback`: for a run against
  `onlineEvalEnv x _`, the expected reward of the learner in the adversarial regret is the expected
  total observed feedback.
* `advRegret_of_subsingleton`: with a single arm, the adversarial regret of every learner is `0`.
* `expertRegret_le_iff`, `sum_sub_integral_le_expertRegret`,
  `Learning.IsAlgEnvSeq.expertRegret_eq_sub_integral_sum_feedback`: the same statements for the
  regret against expert advice, the last one for runs against `Environment.ofSeq o x _` with any
  observations `o`, such as the advice `E`.
* `expertRegret_single`: with the experts that each recommend one arm, the regret against expert
  advice is the adversarial regret.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning

namespace LMLExplore.Bandits

variable {α β Ω : Type*} {mΩ : MeasurableSpace Ω}
  {x : ℕ → α → ℝ} {A : ℕ → Ω → α} {P : Measure Ω} {n : ℕ} {B : ℝ}

section AdvRegret

/-- The **adversarial regret** after `n` rounds of the actions `A` under `P`, for the reward table
`x`: the total reward `max_a ∑_{t < n} x t a` of the best fixed arm in hindsight minus the expected
total reward `E[∑_{t < n} x t (A t)]` of the learner [LS, (11.1)]. -/
noncomputable def advRegret (x : ℕ → α → ℝ) (A : ℕ → Ω → α) (P : Measure Ω) (n : ℕ) : ℝ :=
  (⨆ a, ∑ t ∈ range n, x t a) - P[fun ω ↦ ∑ t ∈ range n, x t (A t ω)]

lemma advRegret_def (x : ℕ → α → ℝ) (A : ℕ → Ω → α) (P : Measure Ω) (n : ℕ) :
    advRegret x A P n = (⨆ a, ∑ t ∈ range n, x t a) - P[fun ω ↦ ∑ t ∈ range n, x t (A t ω)] :=
  (rfl)

/-- The adversarial regret is at least the regret against any fixed arm `a`. -/
lemma sum_sub_integral_le_advRegret [Finite α] (a : α) :
    ∑ t ∈ range n, x t a - P[fun ω ↦ ∑ t ∈ range n, x t (A t ω)] ≤ advRegret x A P n := by
  rw [advRegret_def]
  gcongr
  exact le_ciSup (Finite.bddAbove_range fun a ↦ ∑ t ∈ range n, x t a) a

/-- The adversarial regret is at most `B` iff the regret against every fixed arm is at most `B`. -/
lemma advRegret_le_iff [Finite α] [Nonempty α] :
    advRegret x A P n ≤ B ↔
      ∀ a, ∑ t ∈ range n, x t a - P[fun ω ↦ ∑ t ∈ range n, x t (A t ω)] ≤ B := by
  simp_rw [advRegret_def, sub_le_iff_le_add]
  exact ciSup_le_iff (Finite.bddAbove_range _)

/-- With a single arm, the adversarial regret of every learner is `0`. -/
lemma advRegret_of_subsingleton [Subsingleton α] [IsProbabilityMeasure P] :
    advRegret x A P n = 0 := by
  obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure P
  have : Unique α := uniqueOfSubsingleton (A 0 ω)
  have hA : ∀ t ω, A t ω = default := fun _ _ ↦ Unique.eq_default _
  simp [advRegret_def, hA]

/-- Along a run of an algorithm against LML's evaluation environment `onlineEvalEnv x _`, the
expected total reward in the adversarial regret is the expected total observed feedback. -/
lemma _root_.Learning.IsAlgEnvSeq.advRegret_eq_sub_integral_sum_feedback [MeasurableSpace α]
    [IsProbabilityMeasure P] {hx : ∀ t, Measurable (x t)} {alg : Algorithm Unit α ℝ}
    {O : ℕ → Ω → Unit} {Y : ℕ → Ω → ℝ} (h : IsAlgEnvSeq O A Y alg (onlineEvalEnv x hx) P)
    (n : ℕ) :
    advRegret x A P n = (⨆ a, ∑ t ∈ range n, x t a) - P[fun ω ↦ ∑ t ∈ range n, Y t ω] := by
  rw [advRegret_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [forall_feedback_onlineEvalEnv_ae_eq_eval_action h] with ω hω
  simp [hω]

end AdvRegret

section ExpertRegret

variable [Fintype α] {E : ℕ → β → α → ℝ}

/-- The regret after `n` rounds of the actions `A` under `P` against the best expert of the
advice `E`, for the reward table `x`: the total expected reward
`max_m ∑_{t < n} ∑_a E t m a * x t a` of the best expert in hindsight minus the expected total
reward `E[∑_{t < n} x t (A t)]` of the learner [LS, (18.6)]. Expert `m` recommends at round `t`
the distribution `E t m` over the arms. -/
noncomputable def expertRegret (E : ℕ → β → α → ℝ) (x : ℕ → α → ℝ) (A : ℕ → Ω → α)
    (P : Measure Ω) (n : ℕ) : ℝ :=
  (⨆ m, ∑ t ∈ range n, ∑ a, E t m a * x t a) - P[fun ω ↦ ∑ t ∈ range n, x t (A t ω)]

lemma expertRegret_def (E : ℕ → β → α → ℝ) (x : ℕ → α → ℝ) (A : ℕ → Ω → α) (P : Measure Ω)
    (n : ℕ) :
    expertRegret E x A P n =
      (⨆ m, ∑ t ∈ range n, ∑ a, E t m a * x t a) - P[fun ω ↦ ∑ t ∈ range n, x t (A t ω)] :=
  (rfl)

/-- The regret against expert advice is at least the regret against any expert `m`. -/
lemma sum_sub_integral_le_expertRegret [Finite β] (m : β) :
    ∑ t ∈ range n, ∑ a, E t m a * x t a - P[fun ω ↦ ∑ t ∈ range n, x t (A t ω)] ≤
      expertRegret E x A P n := by
  rw [expertRegret_def]
  gcongr
  exact le_ciSup (Finite.bddAbove_range fun m ↦ ∑ t ∈ range n, ∑ a, E t m a * x t a) m

/-- The regret against expert advice is at most `B` iff the regret against every expert is at
most `B`. -/
lemma expertRegret_le_iff [Finite β] [Nonempty β] :
    expertRegret E x A P n ≤ B ↔
      ∀ m, ∑ t ∈ range n, ∑ a, E t m a * x t a - P[fun ω ↦ ∑ t ∈ range n, x t (A t ω)] ≤ B := by
  simp_rw [expertRegret_def, sub_le_iff_le_add]
  exact ciSup_le_iff (Finite.bddAbove_range _)

/-- With the experts `α` that each recommend one arm, the regret against expert advice is the
adversarial regret. -/
@[simp]
lemma expertRegret_single [DecidableEq α] :
    expertRegret (fun _ m ↦ Pi.single m 1) x A P n = advRegret x A P n := by
  simp [expertRegret_def, advRegret_def, Pi.single_apply]

/-- Along a run of an algorithm that receives the reward `x t a` of its action `a` at round `t`,
that is, a run against `Environment.ofSeq o x _` for any observation sequence `o` (such as the
advice `E`), the expected total reward in the regret against expert advice is the expected total
observed feedback. -/
lemma _root_.Learning.IsAlgEnvSeq.expertRegret_eq_sub_integral_sum_feedback {𝓞 : Type*}
    [MeasurableSpace 𝓞] [MeasurableSpace α] [IsProbabilityMeasure P] {o : ℕ → 𝓞}
    {hx : ∀ t, Measurable (x t)} {alg : Algorithm 𝓞 α ℝ} {O : ℕ → Ω → 𝓞} {Y : ℕ → Ω → ℝ}
    (h : IsAlgEnvSeq O A Y alg (Environment.ofSeq o x hx) P) (n : ℕ) :
    expertRegret E x A P n =
      (⨆ m, ∑ t ∈ range n, ∑ a, E t m a * x t a) - P[fun ω ↦ ∑ t ∈ range n, Y t ω] := by
  rw [expertRegret_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h.feedback_ofSeq_ae_all_eq] with ω hω
  simp [hω]

end ExpertRegret

end LMLExplore.Bandits
