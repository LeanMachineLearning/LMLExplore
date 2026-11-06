/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.EvaluationEnv
public import LeanMachineLearning.SequentialLearning.Means

/-!
# Deterministic adaptive adversaries

A deterministic adaptive adversary computes the observation of round `n` from the history of the
first `n` rounds, `o n h`, and the feedback of round `n` from the history, that observation and the
action, `f n ((h, o), a)`. It reacts to the past actions of the learner but uses no randomness of
its own. `Environment.deterministic o ho f hf` is this environment: LML's `Environment.detFeedback`
with deterministic observations.

In an adversarial bandit [LS, Chapter 11], `f n ((h, o), ·)` is the reward table of round `n`,
chosen by an adversary that has seen the past actions. In a bandit with expert advice
[LS, Chapter 18], `o n h` is the advice of the experts at round `n`, which may depend on the
history. Tables and advice fixed in advance are the cases of LML's `Environment.evalSeq`
(`Learning.Environment.evalSeq_eq_deterministic`) and of LMLExplore's `Environment.ofSeq`.

## Main definitions

* `Learning.Environment.deterministic o ho f hf`: the environment with observations `o n h` and
  feedback `f n ((h, o), a)`.

## Main statements

* `Learning.means_detFeedback`: the conditional mean of the feedback of `Environment.detFeedback`
  at an action `a` is the value of its feedback function at `a`.
* `Learning.IsAlgEnvSeq.feedback_ae_eq_detFeedback`: along a run against
  `Environment.detFeedback obs f hf`, the feedback is almost surely the value of `f` at the
  history, the observation and the action.
* `Learning.IsAlgEnvSeq.obs_ae_eq_deterministic`: along a run against
  `Environment.deterministic o ho f hf`, the observation is almost surely `o` of the history.
* `Learning.Environment.evalSeq_eq_deterministic`: LML's `Environment.evalSeq g hg` is the
  deterministic environment with the tables `g n` that do not depend on the history.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} [MeasurableSpace 𝓞] [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]
  {o : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n → 𝓞} {ho : ∀ n, Measurable (o n)}
  {obs : (n : ℕ) → Kernel (Hist 𝓞 𝓐 𝓨 n) 𝓞} [∀ n, IsMarkovKernel (obs n)]
  {f : (n : ℕ) → (Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐 → 𝓨} {hf : ∀ n, Measurable (f n)}

/-- The environment of a **deterministic adaptive adversary**: the observation of round `n` is
`o n h` and the feedback of round `n` is `f n ((h, o), a)`, for the history `h` of the first `n`
rounds, the observation `o` and the action `a` of round `n`. -/
noncomputable def Environment.deterministic (o : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n → 𝓞)
    (ho : ∀ n, Measurable (o n)) (f : (n : ℕ) → (Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐 → 𝓨)
    (hf : ∀ n, Measurable (f n)) : Environment 𝓞 𝓐 𝓨 :=
  Environment.detFeedback (fun n ↦ Kernel.deterministic (o n) (ho n)) f hf

/-- `Environment.deterministic o ho f hf` is LML's `Environment.detFeedback` with the
deterministic observation kernels of `o`. -/
lemma Environment.deterministic_def (o : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n → 𝓞)
    (ho : ∀ n, Measurable (o n)) (f : (n : ℕ) → (Hist 𝓞 𝓐 𝓨 n × 𝓞) × 𝓐 → 𝓨)
    (hf : ∀ n, Measurable (f n)) :
    Environment.deterministic o ho f hf =
      Environment.detFeedback (fun n ↦ Kernel.deterministic (o n) (ho n)) f hf :=
  (rfl)

@[simp]
lemma Environment.obs_deterministic (n : ℕ) :
    (Environment.deterministic o ho f hf).obs n = Kernel.deterministic (o n) (ho n) :=
  (rfl)

@[simp]
lemma Environment.feedback_deterministic (n : ℕ) :
    (Environment.deterministic o ho f hf).feedback n = Kernel.deterministic (f n) (hf n) :=
  (rfl)

instance : (Environment.deterministic o ho f hf).HasDeterministicFeedback := by
  rw [Environment.deterministic_def]
  infer_instance

/-- LML's evaluation environment `Environment.evalSeq g hg` is the deterministic adaptive
adversary without observations whose reward tables `g n` do not depend on the history. -/
lemma Environment.evalSeq_eq_deterministic (g : ℕ → 𝓐 → 𝓨) (hg : ∀ n, Measurable (g n)) :
    Environment.evalSeq g hg =
      Environment.deterministic (fun _ _ ↦ ()) (fun _ ↦ measurable_const) (fun n p ↦ g n p.2)
        (fun n ↦ (hg n).comp measurable_snd) := by
  ext n : 2
  · ext h : 1
    rw [obs_evalSeq, Environment.obs_deterministic, Kernel.const_apply, Kernel.deterministic_apply]
  · rfl

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm 𝓞 𝓐 𝓨} {P : Measure Ω} [SFinite P]
  {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

/-- The conditional mean of the feedback of `Environment.detFeedback obs f hf` at the action `a` of
round `n` is `f n ((h, o), a)`, for the history `h` and the observation `o` of the run. -/
@[simp]
lemma means_detFeedback [NormedAddCommGroup 𝓨] [NormedSpace ℝ 𝓨] [CompleteSpace 𝓨]
    [MeasurableSingletonClass 𝓨]
    (a : 𝓐) (n : ℕ) (ω : Ω) :
    (Environment.detFeedback obs f hf).means O A Y a n ω =
      f n ((history O A Y n ω, O n ω), a) := by
  simp [Environment.means, Environment.feedbackKernel, Kernel.deterministic_apply]

/-- Along a run against `Environment.detFeedback obs f hf`, the feedback of round `n` is almost
surely `f n` of the history, the observation and the action of round `n`. -/
lemma IsAlgEnvSeq.feedback_ae_eq_detFeedback [MeasurableEq 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.detFeedback obs f hf) P) (n : ℕ) :
    Y n =ᵐ[P] fun ω ↦ f n ((history O A Y n ω, O n ω), A n ω) :=
  (h.hasCondDistrib_feedback n).ae_eq_of_deterministic (hf := hf n)

/-- Along a run against `Environment.deterministic o ho f hf`, the observation of round `n` is
almost surely `o n` of the history of the first `n` rounds. -/
lemma IsAlgEnvSeq.obs_ae_eq_deterministic [MeasurableEq 𝓞]
    (h : IsAlgEnvSeq O A Y alg (Environment.deterministic o ho f hf) P) (n : ℕ) :
    O n =ᵐ[P] fun ω ↦ o n (history O A Y n ω) :=
  (h.hasCondDistrib_obs n).ae_eq_of_deterministic (hf := ho n)

end Learning
