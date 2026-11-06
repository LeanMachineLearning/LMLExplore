/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.SequentialLearning.Environments.Deterministic

/-!
# The environment given by fixed sequences of observations and feedback functions

`Environment.ofSeq o g hg` announces the observation `o n` at round `n`, whatever the history, and
answers the action `a` of round `n` with the feedback `g n a`. Both are fixed in advance: the
environment is an oblivious adversary that reveals the side information `o n` before each action.

In a bandit with expert advice [LS, Chapter 18], the observation `o n` is the advice of the experts
at round `n` and `g n a` is the reward of arm `a` at round `n`. Without observations
(`o = fun _ ↦ ()`), `Environment.ofSeq` is LML's `Environment.evalSeq g hg`. It is the deterministic
adaptive adversary `Environment.deterministic` whose observations and feedback functions do not
depend on the history.

## Main definitions

* `Learning.Environment.ofSeq o g hg : Environment 𝓞 𝓐 𝓨`: the environment with observations `o n`
  and feedback `g n a`.

## Main statements

* `Learning.Environment.ofSeq_unit`: without observations, `Environment.ofSeq` is
  `Environment.evalSeq`.
* `Learning.Environment.ofSeq_eq_deterministic`: `Environment.ofSeq o g hg` is the deterministic
  adaptive adversary with observations `o n` and feedback `g n a` whatever the history.
* `Learning.Environment.feedbackCondObsAction_ofSeq`: `Environment.ofSeq o g hg` is oblivious, and
  the conditional law of its feedback given the observation and the action `a` of round `n` is the
  Dirac mass at `g n a`.
* `Learning.IsAlgEnvSeq.obs_ofSeq_ae_all_eq`: along a run against `Environment.ofSeq o g hg`, the
  observations are almost surely the sequence `o`.
* `Learning.IsAlgEnvSeq.feedback_ofSeq_ae_all_eq`: along such a run, the feedback of round `n` is
  almost surely `g n` evaluated at the action of round `n`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} [MeasurableSpace 𝓞] [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]
  {o : ℕ → 𝓞} {g : ℕ → 𝓐 → 𝓨} {hg : ∀ n, Measurable (g n)}

/-- The environment that announces the observation `o n` at round `n` and answers the action `a`
of round `n` with the feedback `g n a`, whatever the history. -/
noncomputable def Environment.ofSeq (o : ℕ → 𝓞) (g : ℕ → 𝓐 → 𝓨) (hg : ∀ n, Measurable (g n)) :
    Environment 𝓞 𝓐 𝓨 where
  obs n := Kernel.const _ (Measure.dirac (o n))
  feedback n := (Kernel.deterministic (g n) (hg n)).prodMkLeft _

@[simp]
lemma Environment.obs_ofSeq (o : ℕ → 𝓞) (g : ℕ → 𝓐 → 𝓨) (hg : ∀ n, Measurable (g n)) (n : ℕ) :
    (Environment.ofSeq o g hg).obs n = Kernel.const _ (Measure.dirac (o n)) :=
  (rfl)

@[simp]
lemma Environment.feedback_ofSeq (o : ℕ → 𝓞) (g : ℕ → 𝓐 → 𝓨) (hg : ∀ n, Measurable (g n))
    (n : ℕ) :
    (Environment.ofSeq o g hg).feedback n = (Kernel.deterministic (g n) (hg n)).prodMkLeft _ :=
  (rfl)

/-- Without observations, `Environment.ofSeq` is LML's evaluation environment
`Environment.evalSeq`. -/
lemma Environment.ofSeq_unit (g : ℕ → 𝓐 → 𝓨) (hg : ∀ n, Measurable (g n)) :
    Environment.ofSeq (fun _ ↦ ()) g hg = Environment.evalSeq g hg := by
  ext n : 2 <;> simp [Kernel.prodMkLeft_deterministic]

/-- `Environment.ofSeq o g hg` is the deterministic adaptive adversary whose observations `o n` and
feedback functions `g n` do not depend on the history. -/
lemma Environment.ofSeq_eq_deterministic (o : ℕ → 𝓞) (g : ℕ → 𝓐 → 𝓨)
    (hg : ∀ n, Measurable (g n)) :
    Environment.ofSeq o g hg =
      Environment.deterministic (fun n _ ↦ o n) (fun _ ↦ measurable_const) (fun n p ↦ g n p.2)
        (fun n ↦ (hg n).comp measurable_snd) := by
  ext n : 2
  · ext h : 1
    rw [Environment.obs_ofSeq, Environment.obs_deterministic, Kernel.const_apply,
      Kernel.deterministic_apply]
  · rw [Environment.feedback_ofSeq, Environment.feedback_deterministic,
      Kernel.prodMkLeft_deterministic]

instance (o : ℕ → 𝓞) (g : ℕ → 𝓐 → 𝓨) (hg : ∀ n, Measurable (g n)) :
    (Environment.ofSeq o g hg).IsOblivious where
  exists_obs_eq_const := ⟨fun n ↦ Measure.dirac (o n), fun _ ↦ inferInstance, fun _ ↦ rfl⟩
  exists_feedback_eq_comap := ⟨fun n ↦ Kernel.deterministic (fun p ↦ g n p.2) (by fun_prop),
    fun _ ↦ inferInstance, fun _ ↦ rfl⟩

/-- The conditional law of the feedback given the observation and the action in
`Environment.ofSeq o g hg` is the deterministic kernel of `g n` applied to the action. -/
@[simp]
lemma Environment.feedbackCondObsAction_ofSeq (o : ℕ → 𝓞) (g : ℕ → 𝓐 → 𝓨)
    (hg : ∀ n, Measurable (g n)) (n : ℕ) :
    (Environment.ofSeq o g hg).feedbackCondObsAction n =
      Kernel.deterministic (fun p ↦ g n p.2) (by fun_prop) :=
  Environment.feedbackCondObsAction_eq_of_feedback_eq _ rfl

instance (o : ℕ → 𝓞) (g : ℕ → 𝓐 → 𝓨) (hg : ∀ n, Measurable (g n)) :
    (Environment.ofSeq o g hg).HasDeterministicFeedback where
  exists_f n := ⟨fun p ↦ g n p.2, by fun_prop, Kernel.prodMkLeft_deterministic _⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm 𝓞 𝓐 𝓨}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

/-- Along a run against `Environment.ofSeq o g hg`, the observation of round `n` is almost surely
`o n`. -/
lemma IsAlgEnvSeq.obs_ofSeq_ae_eq [MeasurableSingletonClass 𝓞]
    (h : IsAlgEnvSeq O A Y alg (Environment.ofSeq o g hg) P) (n : ℕ) :
    O n =ᵐ[P] fun _ ↦ o n :=
  (h.hasCondDistrib_obs n).hasLaw_of_const.ae_eq_of_dirac

/-- Along a run against `Environment.ofSeq o g hg`, the observations are almost surely the
sequence `o`. -/
lemma IsAlgEnvSeq.obs_ofSeq_ae_all_eq [MeasurableSingletonClass 𝓞]
    (h : IsAlgEnvSeq O A Y alg (Environment.ofSeq o g hg) P) :
    ∀ᵐ ω ∂P, ∀ n, O n ω = o n :=
  ae_all_iff.2 h.obs_ofSeq_ae_eq

/-- Along a run against `Environment.ofSeq o g hg`, the feedback of round `n` is almost surely
`g n` evaluated at the action of round `n`. -/
lemma IsAlgEnvSeq.feedback_ofSeq_ae_eq [MeasurableEq 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.ofSeq o g hg) P) (n : ℕ) :
    Y n =ᵐ[P] g n ∘ A n := by
  have hY := h.hasCondDistrib_feedback_feedbackCondObsAction n
  rw [Environment.feedbackCondObsAction_ofSeq] at hY
  exact hY.ae_eq_of_deterministic

/-- Along a run against `Environment.ofSeq o g hg`, the feedback of every round is almost surely
`g` evaluated at the action of that round. -/
lemma IsAlgEnvSeq.feedback_ofSeq_ae_all_eq [MeasurableEq 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.ofSeq o g hg) P) :
    ∀ᵐ ω ∂P, ∀ n, Y n ω = g n (A n ω) :=
  ae_all_iff.2 h.feedback_ofSeq_ae_eq

end Learning
