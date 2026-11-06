/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.Bandit.Regret
public import Mathlib.Algebra.Order.Group.CompleteLattice
public import LMLExplore.MeasureTheory.Integral.Bochner.Basic
public import LMLExplore.SequentialLearning.Environments.OfSeq
public import LMLExplore.SequentialLearning.Wald

/-!
# Adversarial regret and regret against expert advice

In an adversarial bandit with finitely many arms `α`, an oblivious adversary fixes a reward table
`x : ℕ → α → ℝ` in advance: the reward of arm `a` at round `t` is `x t a`. The learner observes
only the reward `x t (A t)` of the arm it plays, which is a run against LML's evaluation
environment `Environment.evalSeq x _`. Its **adversarial regret** after `n` rounds is [LS, (11.1)]
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

Against any environment `env : Environment 𝓞 α ℝ`, for instance an adaptive adversary that reacts
to the past actions, the benchmark is random. The mean reward of arm `a` at round `t` given the
past and the observation of round `t` is LML's `m_t(a) = env.means O A Y a t`, and the
**pseudo-regret** and the **random regret** are [BCB12, Section 3]
`max_a E[∑_{t < n} (m_t(a) - Y t)]` and `max_a ∑_{t < n} (m_t(a) - Y t)`.
With advice `adv (O t) m : α → ℝ` computed from the observation of round `t`, their expert
versions compare the learner with the expected rewards `∑_a adv (O t) m a * m_t(a)` of the
experts `m`. The adversarial regret and the regret against expert advice are the pseudo-regrets
against `Environment.evalSeq x _` and `Environment.ofSeq o x _`, and against a stationary bandit
`Environment.bandit ν` the pseudo-regret is the expected stochastic regret.

## Main definitions

* `LMLExplore.Bandits.advRegret x A P n`: the adversarial regret `R_n(x)` of the actions `A` under
  `P`.
* `LMLExplore.Bandits.expertRegret E x A P n`: the regret of the actions `A` under `P` against the
  best expert of the advice `E`.
* `LMLExplore.Bandits.pseudoRegret env O A Y P n`, `LMLExplore.Bandits.randomRegret env O A Y n`:
  the pseudo-regret and the random regret of a run against `env`.
* `LMLExplore.Bandits.expertPseudoRegret env adv O A Y P n`,
  `LMLExplore.Bandits.expertRandomRegret env adv O A Y n`: their versions against the experts of
  the advice `adv`.

## Main statements

* `advRegret_le_iff`, `sum_sub_integral_le_advRegret`: the adversarial regret is at most `B` iff
  the regret against every fixed arm is at most `B`; it is at least the regret against any fixed
  arm.
* `Learning.IsAlgEnvSeq.advRegret_eq_sub_integral_sum_feedback`: for a run against
  `Environment.evalSeq x _`, the expected reward of the learner in the adversarial regret is the
  expected total observed feedback.
* `advRegret_of_subsingleton`: with a single arm, the adversarial regret of every learner is `0`.
* `expertRegret_le_iff`, `sum_sub_integral_le_expertRegret`,
  `Learning.IsAlgEnvSeq.expertRegret_eq_sub_integral_sum_feedback`: the same statements for the
  regret against expert advice, the last one for runs against `Environment.ofSeq o x _` with any
  observations `o`, such as the advice `E`.
* `expertRegret_single`: with the experts that each recommend one arm, the regret against expert
  advice is the adversarial regret.
* `pseudoRegret_le_integral_randomRegret`, `expertPseudoRegret_le_integral_expertRandomRegret`: the
  pseudo-regret is at most the expected random regret.
* `expertPseudoRegret_single`, `expertRandomRegret_single`: with the experts that each recommend
  one arm, the expert regrets are the pseudo-regret and the random regret.
* `Learning.IsAlgEnvSeq.expertPseudoRegret_ofSeq`, `Learning.IsAlgEnvSeq.pseudoRegret_evalSeq`: the
  regret against expert advice and the adversarial regret are the pseudo-regrets against
  `Environment.ofSeq o x _` and `Environment.evalSeq x _`.
* `Learning.IsAlgEnvSeq.randomRegret_detFeedback_ae_eq`,
  `Learning.IsAlgEnvSeq.randomRegret_evalSeq_ae_eq`: against an adaptive adversary with reward
  tables `f t ((h, o), ·)`, the random regret is almost surely
  `max_a ∑_{t < n} (f t ((H t, O t), a) - f t ((H t, O t), A t))`, and against
  `Environment.evalSeq x _` it is `max_a ∑_{t < n} (x t a - x t (A t))`.
* `Learning.IsAlgEnvSeq.pseudoRegret_bandit`: against `Environment.bandit ν` with integrable arms,
  the pseudo-regret is LML's expected stochastic regret.

## References

* [BCB12] S. Bubeck and N. Cesa-Bianchi, *Regret analysis of stochastic and nonstochastic
  multi-armed bandit problems*, Foundations and Trends in Machine Learning 5(1), 2012.
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

/-- Along a run of an algorithm against LML's evaluation environment `Environment.evalSeq x _`, the
expected total reward in the adversarial regret is the expected total observed feedback. -/
lemma _root_.Learning.IsAlgEnvSeq.advRegret_eq_sub_integral_sum_feedback [MeasurableSpace α]
    [IsProbabilityMeasure P] {hx : ∀ t, Measurable (x t)} {alg : Algorithm Unit α ℝ}
    {O : ℕ → Ω → Unit} {Y : ℕ → Ω → ℝ} (h : IsAlgEnvSeq O A Y alg (Environment.evalSeq x hx) P)
    (n : ℕ) :
    advRegret x A P n = (⨆ a, ∑ t ∈ range n, x t a) - P[fun ω ↦ ∑ t ∈ range n, Y t ω] := by
  rw [advRegret_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h.feedback_ae_all_eq_evalSeq] with ω hω
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

section PseudoRegret

variable {𝓞 : Type*} [MeasurableSpace 𝓞] [MeasurableSpace α] {env : Environment 𝓞 α ℝ}
  {O : ℕ → Ω → 𝓞} {Y : ℕ → Ω → ℝ} {ω : Ω}

/-- The **pseudo-regret** after `n` rounds of the run `(O, A, Y)` under `P` against the
environment `env`: `max_a E[∑_{t < n} (m_t(a) - Y t)]`, where `m_t(a) = env.means O A Y a t` is
the mean reward of arm `a` at round `t` given the history and the observation of round `t`
[BCB12, Section 3]. The environment may be an adaptive adversary. -/
noncomputable def pseudoRegret (env : Environment 𝓞 α ℝ) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → ℝ) (P : Measure Ω) (n : ℕ) : ℝ :=
  ⨆ a, P[fun ω ↦ ∑ t ∈ range n, (env.means O A Y a t ω - Y t ω)]

lemma pseudoRegret_def (env : Environment 𝓞 α ℝ) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → ℝ) (P : Measure Ω) (n : ℕ) :
    pseudoRegret env O A Y P n = ⨆ a, P[fun ω ↦ ∑ t ∈ range n, (env.means O A Y a t ω - Y t ω)] :=
  (rfl)

/-- The **random regret** after `n` rounds of the run `(O, A, Y)` at `ω` against the environment
`env`: `max_a ∑_{t < n} (m_t(a) - Y t)`, with the conditional means `m_t(a) = env.means O A Y a t`
of the rewards. -/
noncomputable def randomRegret (env : Environment 𝓞 α ℝ) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ⨆ a, ∑ t ∈ range n, (env.means O A Y a t ω - Y t ω)

lemma randomRegret_def (env : Environment 𝓞 α ℝ) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α)
    (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    randomRegret env O A Y n ω = ⨆ a, ∑ t ∈ range n, (env.means O A Y a t ω - Y t ω) :=
  (rfl)

/-- The pseudo-regret is at least the expected regret against any fixed arm `a`. -/
lemma integral_sum_sub_le_pseudoRegret [Finite α] (a : α) :
    P[fun ω ↦ ∑ t ∈ range n, (env.means O A Y a t ω - Y t ω)] ≤ pseudoRegret env O A Y P n := by
  rw [pseudoRegret_def]
  exact Finite.le_ciSup (fun a ↦ P[fun ω ↦ ∑ t ∈ range n, (env.means O A Y a t ω - Y t ω)]) a

/-- The pseudo-regret is at most `B` iff the expected regret against every fixed arm is at most
`B`. -/
lemma pseudoRegret_le_iff [Finite α] [Nonempty α] :
    pseudoRegret env O A Y P n ≤ B ↔
      ∀ a, P[fun ω ↦ ∑ t ∈ range n, (env.means O A Y a t ω - Y t ω)] ≤ B := by
  rw [pseudoRegret_def]
  exact ciSup_le_iff (Finite.bddAbove_range _)

/-- The random regret is at least the regret against any fixed arm `a`. -/
lemma sum_sub_le_randomRegret [Finite α] (a : α) :
    ∑ t ∈ range n, (env.means O A Y a t ω - Y t ω) ≤ randomRegret env O A Y n ω := by
  rw [randomRegret_def]
  exact Finite.le_ciSup (fun a ↦ ∑ t ∈ range n, (env.means O A Y a t ω - Y t ω)) a

/-- The random regret is at most `B` iff the regret against every fixed arm is at most `B`. -/
lemma randomRegret_le_iff [Finite α] [Nonempty α] :
    randomRegret env O A Y n ω ≤ B ↔ ∀ a, ∑ t ∈ range n, (env.means O A Y a t ω - Y t ω) ≤ B := by
  rw [randomRegret_def]
  exact ciSup_le_iff (Finite.bddAbove_range _)

/-- The pseudo-regret is at most the expected random regret, when the conditional means of every
arm and the rewards are integrable. -/
lemma pseudoRegret_le_integral_randomRegret [Finite α]
    (hm : ∀ a t, Integrable (fun ω ↦ env.means O A Y a t ω) P) (hY : ∀ t, Integrable (Y t) P) :
    pseudoRegret env O A Y P n ≤ P[randomRegret env O A Y n] :=
  iSup_integral_le fun a ↦ integrable_finsetSum _ fun t _ ↦ (hm a t).sub (hY t)

section Expert

variable [Fintype α] {adv : 𝓞 → β → α → ℝ}

/-- The **expert pseudo-regret** after `n` rounds of the run `(O, A, Y)` under `P` against the
environment `env`, for the advice `adv`: expert `m` recommends at round `t` the distribution
`adv (O t) m` over the arms, computed from the observation of round `t`, and the expert
pseudo-regret is `max_m E[∑_{t < n} (∑_a adv (O t) m a * m_t(a) - Y t)]`, with the conditional
means `m_t(a) = env.means O A Y a t` of the rewards ([LS, (18.6)] for advice and rewards fixed in
advance). -/
noncomputable def expertPseudoRegret (env : Environment 𝓞 α ℝ) (adv : 𝓞 → β → α → ℝ)
    (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ) (P : Measure Ω) (n : ℕ) : ℝ :=
  ⨆ m, P[fun ω ↦ ∑ t ∈ range n, (∑ a, adv (O t ω) m a * env.means O A Y a t ω - Y t ω)]

lemma expertPseudoRegret_def (env : Environment 𝓞 α ℝ) (adv : 𝓞 → β → α → ℝ)
    (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ) (P : Measure Ω) (n : ℕ) :
    expertPseudoRegret env adv O A Y P n =
      ⨆ m, P[fun ω ↦ ∑ t ∈ range n, (∑ a, adv (O t ω) m a * env.means O A Y a t ω - Y t ω)] :=
  (rfl)

/-- The **expert random regret** after `n` rounds of the run `(O, A, Y)` at `ω` against the
environment `env`, for the advice `adv`: `max_m ∑_{t < n} (∑_a adv (O t) m a * m_t(a) - Y t)`,
with the conditional means `m_t(a) = env.means O A Y a t` of the rewards. -/
noncomputable def expertRandomRegret (env : Environment 𝓞 α ℝ) (adv : 𝓞 → β → α → ℝ)
    (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ⨆ m, ∑ t ∈ range n, (∑ a, adv (O t ω) m a * env.means O A Y a t ω - Y t ω)

lemma expertRandomRegret_def (env : Environment 𝓞 α ℝ) (adv : 𝓞 → β → α → ℝ)
    (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    expertRandomRegret env adv O A Y n ω =
      ⨆ m, ∑ t ∈ range n, (∑ a, adv (O t ω) m a * env.means O A Y a t ω - Y t ω) :=
  (rfl)

/-- The expert pseudo-regret is at least the expected regret against any expert `m`. -/
lemma integral_sum_sub_le_expertPseudoRegret [Finite β] (m : β) :
    P[fun ω ↦ ∑ t ∈ range n, (∑ a, adv (O t ω) m a * env.means O A Y a t ω - Y t ω)] ≤
      expertPseudoRegret env adv O A Y P n := by
  rw [expertPseudoRegret_def]
  exact Finite.le_ciSup (fun m ↦ P[fun ω ↦ ∑ t ∈ range n,
    (∑ a, adv (O t ω) m a * env.means O A Y a t ω - Y t ω)]) m

/-- The expert pseudo-regret is at most `B` iff the expected regret against every expert is at
most `B`. -/
lemma expertPseudoRegret_le_iff [Finite β] [Nonempty β] :
    expertPseudoRegret env adv O A Y P n ≤ B ↔
      ∀ m, P[fun ω ↦ ∑ t ∈ range n, (∑ a, adv (O t ω) m a * env.means O A Y a t ω - Y t ω)] ≤
        B := by
  rw [expertPseudoRegret_def]
  exact ciSup_le_iff (Finite.bddAbove_range _)

/-- The expert random regret is at least the regret against any expert `m`. -/
lemma sum_sub_le_expertRandomRegret [Finite β] (m : β) :
    ∑ t ∈ range n, (∑ a, adv (O t ω) m a * env.means O A Y a t ω - Y t ω) ≤
      expertRandomRegret env adv O A Y n ω := by
  rw [expertRandomRegret_def]
  exact Finite.le_ciSup (fun m ↦ ∑ t ∈ range n,
    (∑ a, adv (O t ω) m a * env.means O A Y a t ω - Y t ω)) m

/-- The expert random regret is at most `B` iff the regret against every expert is at most
`B`. -/
lemma expertRandomRegret_le_iff [Finite β] [Nonempty β] :
    expertRandomRegret env adv O A Y n ω ≤ B ↔
      ∀ m, ∑ t ∈ range n, (∑ a, adv (O t ω) m a * env.means O A Y a t ω - Y t ω) ≤ B := by
  rw [expertRandomRegret_def]
  exact ciSup_le_iff (Finite.bddAbove_range _)

/-- The expert pseudo-regret is at most the expected expert random regret, when the expected
rewards of the experts and the rewards are integrable. -/
lemma expertPseudoRegret_le_integral_expertRandomRegret [Finite β]
    (hm : ∀ m t, Integrable (fun ω ↦ ∑ a, adv (O t ω) m a * env.means O A Y a t ω) P)
    (hY : ∀ t, Integrable (Y t) P) :
    expertPseudoRegret env adv O A Y P n ≤ P[expertRandomRegret env adv O A Y n] :=
  iSup_integral_le fun m ↦ integrable_finsetSum _ fun t _ ↦ (hm m t).sub (hY t)

/-- With the experts `α` that each recommend one arm, the expert pseudo-regret is the
pseudo-regret. -/
@[simp]
lemma expertPseudoRegret_single [DecidableEq α] :
    expertPseudoRegret env (fun _ m ↦ Pi.single m 1) O A Y P n = pseudoRegret env O A Y P n := by
  simp [expertPseudoRegret_def, pseudoRegret_def, Pi.single_apply]

/-- With the experts `α` that each recommend one arm, the expert random regret is the random
regret. -/
@[simp]
lemma expertRandomRegret_single [DecidableEq α] :
    expertRandomRegret env (fun _ m ↦ Pi.single m 1) O A Y n ω = randomRegret env O A Y n ω := by
  simp [expertRandomRegret_def, randomRegret_def, Pi.single_apply]

/-- Along a run against `Environment.ofSeq o x _`, whose observations are `o` and whose rewards are
the table `x`, the expert pseudo-regret for the advice `adv` is the regret against the expert
advice `adv (o t)` fixed in advance. With the advice as observations (`adv = id`), it is the
regret against the advice `o`. -/
lemma _root_.Learning.IsAlgEnvSeq.expertPseudoRegret_ofSeq [Finite β] [Nonempty β]
    [MeasurableSingletonClass 𝓞] [MeasurableSingletonClass α] [IsProbabilityMeasure P] {o : ℕ → 𝓞}
    {hx : ∀ t, Measurable (x t)} {alg : Algorithm 𝓞 α ℝ}
    (h : IsAlgEnvSeq O A Y alg (Environment.ofSeq o x hx) P) (adv : 𝓞 → β → α → ℝ) (n : ℕ) :
    expertPseudoRegret (Environment.ofSeq o x hx) adv O A Y P n =
      expertRegret (fun t ↦ adv (o t)) x A P n := by
  have hint (t : ℕ) : Integrable (fun ω ↦ x t (A t ω)) P :=
    Integrable.of_finite.comp_measurable (h.measurable_action t)
  rw [expertPseudoRegret_def, expertRegret_def, ciSup_sub (Finite.bddAbove_range _)]
  refine iSup_congr fun m ↦ ?_
  calc P[fun ω ↦ ∑ t ∈ range n,
        (∑ a, adv (O t ω) m a * (Environment.ofSeq o x hx).means O A Y a t ω - Y t ω)]
    _ = P[fun ω ↦ ∑ t ∈ range n, (∑ a, adv (o t) m a * x t a - x t (A t ω))] := by
      refine integral_congr_ae ?_
      filter_upwards [h.obs_ofSeq_ae_all_eq, h.feedback_ofSeq_ae_all_eq] with ω hO hY
      simp [hO, hY, Kernel.deterministic_apply]
    _ = ∑ t ∈ range n, ∑ a, adv (o t) m a * x t a - P[fun ω ↦ ∑ t ∈ range n, x t (A t ω)] := by
      simp_rw [sum_sub_distrib]
      rw [integral_const_sub_sum _ fun t _ ↦ hint t, integral_finsetSum _ fun t _ ↦ hint t]

end Expert

/-- Along a run against LML's evaluation environment `Environment.evalSeq x _`, the pseudo-regret
is the adversarial regret `R_n(x)`. -/
lemma _root_.Learning.IsAlgEnvSeq.pseudoRegret_evalSeq [Finite α] [Nonempty α]
    [MeasurableSingletonClass α] [IsProbabilityMeasure P] {hx : ∀ t, Measurable (x t)}
    {alg : Algorithm Unit α ℝ} {O : ℕ → Ω → Unit}
    (h : IsAlgEnvSeq O A Y alg (Environment.evalSeq x hx) P) (n : ℕ) :
    pseudoRegret (Environment.evalSeq x hx) O A Y P n = advRegret x A P n := by
  classical
  have := Fintype.ofFinite α
  rw [← Environment.ofSeq_unit] at h ⊢
  rw [← expertPseudoRegret_single, h.expertPseudoRegret_ofSeq, expertRegret_single]

/-- Along a run against LML's `Environment.detFeedback obs f hf`, an adaptive adversary whose
reward table at round `t` is `f t ((h, o), ·)` for the history `h` and the observation `o` of
round `t`, the random regret is almost surely the regret
`max_a ∑_{t < n} (f t ((H t, O t), a) - f t ((H t, O t), A t))` against the best fixed arm. -/
lemma _root_.Learning.IsAlgEnvSeq.randomRegret_detFeedback_ae_eq [SFinite P]
    {obs : (n : ℕ) → Kernel (Hist 𝓞 α ℝ n) 𝓞} [∀ n, IsMarkovKernel (obs n)]
    {f : (n : ℕ) → (Hist 𝓞 α ℝ n × 𝓞) × α → ℝ} {hf : ∀ n, Measurable (f n)}
    {alg : Algorithm 𝓞 α ℝ} (h : IsAlgEnvSeq O A Y alg (Environment.detFeedback obs f hf) P)
    (n : ℕ) :
    randomRegret (Environment.detFeedback obs f hf) O A Y n =ᵐ[P] fun ω ↦
      ⨆ a, ∑ t ∈ range n, (f t ((history O A Y t ω, O t ω), a) -
        f t ((history O A Y t ω, O t ω), A t ω)) := by
  filter_upwards [ae_all_iff.2 h.feedback_detFeedback_ae_eq] with ω hω
  simp [randomRegret_def, hω]

/-- Along a run against LML's evaluation environment `Environment.evalSeq x _`, the random regret
is almost surely `max_a ∑_{t < n} (x t a - x t (A t))`. -/
lemma _root_.Learning.IsAlgEnvSeq.randomRegret_evalSeq_ae_eq [SFinite P]
    {hx : ∀ t, Measurable (x t)} {alg : Algorithm Unit α ℝ} {O : ℕ → Ω → Unit}
    (h : IsAlgEnvSeq O A Y alg (Environment.evalSeq x hx) P) (n : ℕ) :
    randomRegret (Environment.evalSeq x hx) O A Y n =ᵐ[P] fun ω ↦
      ⨆ a, ∑ t ∈ range n, (x t a - x t (A t ω)) := by
  rw [Environment.evalSeq_eq_deterministic, Environment.deterministic_def] at h ⊢
  exact h.randomRegret_detFeedback_ae_eq n

/-- Along a run against a stationary bandit `Environment.bandit ν` with finitely many arms and
integrable reward distributions, the pseudo-regret is LML's expected stochastic regret. -/
lemma _root_.Learning.IsAlgEnvSeq.pseudoRegret_bandit [Finite α] [Nonempty α]
    [MeasurableSingletonClass α] [IsProbabilityMeasure P] {ν : Kernel α ℝ} [IsMarkovKernel ν]
    {alg : Algorithm Unit α ℝ} {O : ℕ → Ω → Unit}
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (hν : ∀ a, Integrable id (ν a)) (n : ℕ) :
    pseudoRegret (Environment.bandit ν) O A Y P n = P[Bandits.regret ν A n] := by
  have hY (t : ℕ) : Integrable (Y t) P := h.integrable_feedback_bandit hν t
  have hmA (t : ℕ) : Integrable (fun ω ↦ (ν (A t ω))[id]) P :=
    Integrable.of_finite.comp_measurable (g := fun a ↦ ∫ y, id y ∂(ν a)) (h.measurable_action t)
  -- the expected reward of round `t` is the expected mean of the arm played at round `t`
  have hE (t : ℕ) : P[Y t] = P[fun ω ↦ (ν (A t ω))[id]] := by
    simpa [means_bandit] using h.setIntegral_feedback (hY t) MeasurableSet.univ
  -- both sides are `n * μ a - ∑ t, E[μ (A t)]` maximized over the arm `a`: pull the expectation
  -- through the sums, then the supremum out of `n * ⨆ a, μ a` and of the subtraction
  simp_rw [pseudoRegret_def, means_bandit, sum_sub_distrib, Bandits.regret, sum_const, card_range,
    nsmul_eq_mul, integral_const_sub_sum _ fun t _ ↦ hY t,
    integral_const_sub_sum _ fun t _ ↦ hmA t, hE, Real.mul_iSup_of_nonneg (Nat.cast_nonneg n),
    ciSup_sub (Finite.bddAbove_range _)]

end PseudoRegret

end LMLExplore.Bandits
