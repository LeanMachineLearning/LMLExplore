/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.EvaluationEnv

/-!
# The environment given by fixed sequences of observations and feedback functions

`Environment.ofSeq o g hg` announces the observation `o n` at round `n`, whatever the history, and
answers the action `a` of round `n` with the feedback `g n a`. Both are fixed in advance: the
environment is an oblivious adversary that reveals the side information `o n` before each action.

In a bandit with expert advice [LS, Chapter 18], the observation `o n` is the advice of the experts
at round `n` and `g n a` is the reward of arm `a` at round `n`. Without observations
(`o = fun _ ↦ ()`), `Environment.ofSeq` is LML's `onlineEvalEnv g hg`.

## Main definitions

* `Learning.Environment.ofSeq o g hg : Environment 𝓞 𝓐 𝓨`: the environment with observations `o n`
  and feedback `g n a`.

## Main statements

* `Learning.Environment.ofSeq_unit`: without observations, `Environment.ofSeq` is
  `onlineEvalEnv`.
* `Learning.Environment.feedbackCondAction_ofSeq`: `Environment.ofSeq o g hg` is oblivious, and
  the conditional law of its feedback given the action `a` of round `n` is the Dirac mass at
  `g n a`.
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

/-- Without observations, `Environment.ofSeq` is LML's evaluation environment `onlineEvalEnv`. -/
lemma Environment.ofSeq_unit (g : ℕ → 𝓐 → 𝓨) (hg : ∀ n, Measurable (g n)) :
    Environment.ofSeq (fun _ ↦ ()) g hg = onlineEvalEnv g hg := by
  ext n : 2 <;> simp [onlineEvalEnv]

instance (o : ℕ → 𝓞) (g : ℕ → 𝓐 → 𝓨) (hg : ∀ n, Measurable (g n)) :
    IsObliviousEnv (Environment.ofSeq o g hg) :=
  ⟨⟨fun n ↦ Kernel.deterministic (g n) (hg n), fun _ ↦ inferInstance, fun _ ↦ rfl⟩⟩

/-- The conditional law of the feedback given the action in `Environment.ofSeq o g hg` is the
deterministic kernel of `g n`. -/
@[simp]
lemma Environment.feedbackCondAction_ofSeq (o : ℕ → 𝓞) (g : ℕ → 𝓐 → 𝓨)
    (hg : ∀ n, Measurable (g n)) (n : ℕ) :
    feedbackCondAction (Environment.ofSeq o g hg) n = Kernel.deterministic (g n) (hg n) := by
  rcases isEmpty_or_nonempty 𝓐 with h𝓐 | ⟨⟨a⟩⟩
  · ext a : 1
    exact h𝓐.elim a
  have : Nonempty (Hist 𝓞 𝓐 𝓨 n × 𝓞) := ⟨(fun _ ↦ (o 0, a, g 0 a), o 0)⟩
  have h_eq := feedback_eq_feedbackCondAction (Environment.ofSeq o g hg) n
  rw [Environment.feedback_ofSeq, Kernel.prodMkLeft_inj] at h_eq
  exact h_eq.symm

instance (o : ℕ → 𝓞) (g : ℕ → 𝓐 → 𝓨) (hg : ∀ n, Measurable (g n)) :
    IsDeterministicEnv (Environment.ofSeq o g hg) where
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
  have hY := IsObliviousEnv.hasCondDistrib_feedback h n
  rw [Environment.feedbackCondAction_ofSeq] at hY
  exact ae_eq_of_hasCondDistrib_deterministic (hg n) (h.measurable_action n).aemeasurable
    (h.measurable_feedback n).aemeasurable hY

/-- Along a run against `Environment.ofSeq o g hg`, the feedback of every round is almost surely
`g` evaluated at the action of that round. -/
lemma IsAlgEnvSeq.feedback_ofSeq_ae_all_eq [MeasurableEq 𝓨]
    (h : IsAlgEnvSeq O A Y alg (Environment.ofSeq o g hg) P) :
    ∀ᵐ ω ∂P, ∀ n, Y n ω = g n (A n ω) :=
  ae_all_iff.2 h.feedback_ofSeq_ae_eq

end Learning
