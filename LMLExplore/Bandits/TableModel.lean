/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.Bandit.ArrayProbSpace
public import LeanMachineLearning.SequentialLearning.EvaluationEnv
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
public import LMLExplore.MeasureTheory.MeasurableSpace.Constructions

/-!
# A stochastic bandit is a mixture of reward tables

In a stochastic bandit with reward kernel `ν : Kernel 𝓐 𝓡`, the reward of round `t` can be read
from a table `x : ℕ → 𝓐 → 𝓡` drawn before the first round: the reward of round `t` is `x t (A t)`
for the action `A t` of round `t`, and the rows `x t` of the table are independent with law
`⨂ a, ν a` (LML's `streamMeasure ν`). Given the table, the learner plays against the oblivious
adversary that has fixed the table in advance, LML's evaluation environment
`Environment.evalSeq x _`. So the law of a run against the stochastic bandit
`Environment.bandit ν` is the mixture, over the tables `x ∼ streamMeasure ν`, of the laws of the
runs against `Environment.evalSeq x _`. This is how adversarial regret bounds are compared with
stochastic regret bounds, and how lower bounds on the stochastic regret transfer to the
adversarial regret.

The proof realizes both runs on one space, as in LML's array model (`Bandits.ArrayModel`), which
reads the rewards of each action from a table indexed by the number of pulls of that action. In
the *table model* here, the table is indexed by the rounds. On `ArrayModel.ProbSpace 𝓐 𝓡`, the
space of pairs `ω = (u, x)` of a sequence `u : ℕ → I` of uniform variables and a table `x`, the
action of round `t` is `ArrayModel.algFunction alg t (H t) (u t)` for the history `H t` of the
first `t` rounds, and its reward is `x t (A t)`. Under `ArrayModel.arrayMeasure ν`, the product of
the uniform law and `streamMeasure ν`, this is a run against `Environment.bandit ν`; for a fixed
table `x`, under the uniform law of `u` alone, it is a run against `Environment.evalSeq x _`.
Fubini's theorem on the product then gives the mixture. The proofs of the conditional laws of the
table model adapt those of LML's array model (`ArrayModel.isAlgEnvSeq_arrayMeasure`).

## Main definitions

* `LMLExplore.Bandits.TableModel.hist`, `LMLExplore.Bandits.TableModel.action`,
  `LMLExplore.Bandits.TableModel.reward`: the history, the action and the reward of each round in
  the table model.

## Main statements

* `LMLExplore.Bandits.TableModel.isAlgEnvSeq_bandit`: under `ArrayModel.arrayMeasure ν`, the table
  model is a run against `Environment.bandit ν`.
* `LMLExplore.Bandits.TableModel.isAlgEnvSeq_evalSeq`: for a fixed table `x`, under the uniform
  law, the table model is a run against `Environment.evalSeq x _`.
* `LMLExplore.Bandits.trajMeasure_bandit_eq_bind`: the law of the run against
  `Environment.bandit ν` is the mixture over `x ∼ streamMeasure ν` of the laws of the runs against
  `Environment.evalSeq x _`.
* `LMLExplore.Bandits.integral_trajMeasure_bandit`: the corresponding identity for integrals.
* `LMLExplore.Bandits.measurable_trajMeasure_evalSeq`: the law of the run against
  `Environment.evalSeq x _` is a measurable function of the table `x`.
* `LMLExplore.Bandits.integrable_sum_eval_streamMeasure`,
  `LMLExplore.Bandits.integral_sum_eval_streamMeasure`: the total reward of an arm over the first
  `n` rows of a table `x ∼ streamMeasure ν` is integrable, with expectation `n` times the mean of
  the arm.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 4.6 (the stack of rewards).
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Bandits
open scoped unitInterval

namespace LMLExplore.Bandits

variable {𝓐 𝓡 : Type*} [MeasurableSpace 𝓐] [MeasurableSpace 𝓡] [Nonempty 𝓐]
  [StandardBorelSpace 𝓐]

namespace TableModel

/-- The history of the first `n` rounds in the table model: at round `t`, the action is drawn from
the uniform variable `ω.1 t` through `ArrayModel.algFunction`, and its reward is read in row `t`
of the table `ω.2`. -/
noncomputable def hist (alg : Algorithm Unit 𝓐 𝓡) (ω : ArrayModel.ProbSpace 𝓐 𝓡) :
    (n : ℕ) → Hist Unit 𝓐 𝓡 n
  | 0 => default
  | n + 1 => Fin.snoc (hist alg ω n) ((), ArrayModel.algFunction alg n (hist alg ω n) (ω.1 n),
      ω.2 n (ArrayModel.algFunction alg n (hist alg ω n) (ω.1 n)))

/-- The action of round `n` in the table model. -/
noncomputable def action (alg : Algorithm Unit 𝓐 𝓡) (n : ℕ) (ω : ArrayModel.ProbSpace 𝓐 𝓡) :
    𝓐 :=
  ArrayModel.algFunction alg n (hist alg ω n) (ω.1 n)

/-- The reward of round `n` in the table model: the entry of row `n` of the table at the action of
round `n`. -/
noncomputable def reward (alg : Algorithm Unit 𝓐 𝓡) (n : ℕ) (ω : ArrayModel.ProbSpace 𝓐 𝓡) :
    𝓡 :=
  ω.2 n (action alg n ω)

lemma action_def (alg : Algorithm Unit 𝓐 𝓡) (n : ℕ) (ω : ArrayModel.ProbSpace 𝓐 𝓡) :
    action alg n ω = ArrayModel.algFunction alg n (hist alg ω n) (ω.1 n) := (rfl)

lemma reward_def (alg : Algorithm Unit 𝓐 𝓡) (n : ℕ) (ω : ArrayModel.ProbSpace 𝓐 𝓡) :
    reward alg n ω = ω.2 n (action alg n ω) := (rfl)

@[simp]
lemma hist_zero (alg : Algorithm Unit 𝓐 𝓡) (ω : ArrayModel.ProbSpace 𝓐 𝓡) :
    hist alg ω 0 = default := (rfl)

lemma hist_succ (alg : Algorithm Unit 𝓐 𝓡) (ω : ArrayModel.ProbSpace 𝓐 𝓡) (n : ℕ) :
    hist alg ω (n + 1) = Fin.snoc (hist alg ω n) ((), action alg n ω, reward alg n ω) := (rfl)

/-- The history in the table model is the history of its action and reward processes. -/
lemma hist_eq_history (alg : Algorithm Unit 𝓐 𝓡) (ω : ArrayModel.ProbSpace 𝓐 𝓡) (n : ℕ) :
    hist alg ω n = history (noObs _) (action alg) (reward alg) n ω := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n hn =>
    ext i : 1
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · rw [hist_succ, Fin.snoc_last]
      simp [history_apply, noObs]
    · rw [hist_succ, Fin.snoc_castSucc, hn]
      simp [history_apply]

/-- The history of the first `n` rounds only reads the uniform variables and the rows of the table
of these rounds. -/
lemma hist_congr (alg : Algorithm Unit 𝓐 𝓡) {n : ℕ} {ω ω' : ArrayModel.ProbSpace 𝓐 𝓡}
    (h₁ : ∀ i < n, ω.1 i = ω'.1 i) (h₂ : ∀ i < n, ω.2 i = ω'.2 i) :
    hist alg ω n = hist alg ω' n := by
  induction n with
  | zero => rfl
  | succ n hn =>
    have h : hist alg ω n = hist alg ω' n :=
      hn (fun i hi ↦ h₁ i (by omega)) fun i hi ↦ h₂ i (by omega)
    simp only [hist_succ, action, reward, h, h₁ n (by omega), h₂ n (by omega)]

section Measurability

variable [Countable 𝓐]

@[fun_prop]
lemma measurable_hist (alg : Algorithm Unit 𝓐 𝓡) (n : ℕ) :
    Measurable (fun ω ↦ hist alg ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n hn =>
    have ha : Measurable fun ω : ArrayModel.ProbSpace 𝓐 𝓡 ↦
        ArrayModel.algFunction alg n (hist alg ω n) (ω.1 n) := by fun_prop
    have h_eq : (fun ω ↦ hist alg ω (n + 1)) =
        (MeasurableEquiv.finSuccProd (Round Unit 𝓐 𝓡) n).symm ∘
          (fun ω ↦ (hist alg ω n, ((), ArrayModel.algFunction alg n (hist alg ω n) (ω.1 n),
            ω.2 n (ArrayModel.algFunction alg n (hist alg ω n) (ω.1 n))))) := by
      ext ω : 1
      rw [Function.comp_apply, MeasurableEquiv.finSuccProd_symm_apply]
      simp only [hist_succ, action_def, reward_def]
    rw [h_eq]
    exact (MeasurableEquiv.measurable _).comp (hn.prodMk (measurable_const.prodMk
      (ha.prodMk ((measurable_eval_apply n).comp (measurable_snd.prodMk ha)))))

@[fun_prop]
lemma measurable_action (alg : Algorithm Unit 𝓐 𝓡) (n : ℕ) : Measurable (action alg n) := by
  unfold action
  fun_prop

@[fun_prop]
lemma measurable_reward (alg : Algorithm Unit 𝓐 𝓡) (n : ℕ) : Measurable (reward alg n) :=
  (measurable_eval_apply n).comp (measurable_snd.prodMk (measurable_action alg n))

end Measurability

section Laws

variable [Countable 𝓐]

/-- The history of the first `n` rounds is measurable with respect to the uniform variables of
these rounds and the table. -/
private lemma measurable_hist_comap (alg : Algorithm Unit 𝓐 𝓡) (n : ℕ) :
    Measurable[MeasurableSpace.comap (fun ω : ArrayModel.ProbSpace 𝓐 𝓡 ↦
      (fun i : Fin n ↦ ω.1 i, ω.2)) inferInstance] (hist alg · n) := by
  have h_eq : (hist alg · n) =
      ((hist alg · n) ∘ (fun p ↦ (fun i : ℕ ↦ if hi : i < n then p.1 ⟨i, hi⟩ else 0, p.2))) ∘
        (fun ω ↦ (fun (i : Fin n) ↦ ω.1 i, ω.2)) := by
    ext ω : 1
    exact hist_congr alg (fun i hi ↦ by simp [hi]) fun _ _ ↦ rfl
  rw [h_eq]
  refine measurable_comp_comap _ (Measurable.comp (by fun_prop) ?_)
  refine Measurable.prodMk ?_ (by fun_prop)
  rw [measurable_pi_iff]
  intro i
  by_cases hi : i < n
  · simp only [hi, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [hi, ↓reduceDIte]
    exact measurable_const

variable (ξ : Measure (ℕ → 𝓐 → 𝓡)) [IsProbabilityMeasure ξ]

/-- The uniform variable of round `n` is independent of the history of the first `n` rounds,
whatever the law `ξ` of the table. -/
private lemma indepFun_fst_hist (alg : Algorithm Unit 𝓐 𝓡) (n : ℕ) :
    IndepFun (fun ω ↦ ω.1 n) (hist alg · n)
      ((Measure.infinitePi fun _ : ℕ ↦ (volume : Measure I)).prod ξ) := by
  have h : IndepFun (fun ω : ℕ → I ↦ ω n) (fun ω (i : Fin n) ↦ ω i)
      (Measure.infinitePi fun _ : ℕ ↦ (volume : Measure I)) := by
    refine (iIndepFun_infinitePi fun _ ↦ measurable_id).indepFun_of_measurable_iSup_comap
      (fun _ ↦ measurable_pi_apply _) (S := Set.Iio n) (by simp) ?_
    rw [measurable_iff_comap_le, MeasurableSpace.comap_pi]
    exact iSup_le fun i ↦ le_iSup₂_of_le (i : ℕ) (Set.mem_Iio.2 i.2) le_rfl
  exact (h.fst_prod (ν := ξ) (by fun_prop) (by fun_prop)).of_measurable_right
    (measurable_hist_comap alg n)

/-- The conditional law of the action of round `n` given the history is the policy of the
algorithm, whatever the law `ξ` of the table. -/
lemma hasCondDistrib_action_hist (alg : Algorithm Unit 𝓐 𝓡) (n : ℕ) :
    HasCondDistrib (action alg n) (hist alg · n) ((alg.policy n).sectL ())
      ((Measure.infinitePi fun _ : ℕ ↦ (volume : Measure I)).prod ξ) := by
  have hU : HasCondDistrib (fun ω ↦ ω.1 n) (fun ω ↦ (hist alg ω n, hist alg ω n))
      (Kernel.const _ (volume : Measure I))
      ((Measure.infinitePi fun _ : ℕ ↦ (volume : Measure I)).prod ξ) :=
    ((indepFun_fst_hist ξ alg n).symm.comp (measurable_id.prodMk measurable_id)
      measurable_id).hasCondDistrib_const (by fun_prop)
      ((hasLaw_eval_infinitePi (fun _ : ℕ ↦ (volume : Measure I)) n).comp (hasLaw_fst_prod _ _))
  have h := ((hasCondDistrib_self (X := (hist alg · n)) (by fun_prop)).compProd hU).comp_left
    (ArrayModel.measurable_algFunction alg n)
  have h_ker : (alg.policy n).sectL () = (Kernel.id ⊗ₖ Kernel.const _ volume).map
      (Function.uncurry (ArrayModel.algFunction alg n)) := by
    ext h s hs
    rw [Kernel.sectL_apply, Kernel.map_apply' _ (ArrayModel.measurable_algFunction alg n) _ hs,
      Kernel.compProd_apply (ArrayModel.measurable_algFunction alg n hs), Kernel.id_apply]
    simp only [Kernel.const_apply]
    rw [lintegral_dirac' _ (measurable_measure_prodMk_left
        (ArrayModel.measurable_algFunction alg n hs)),
      ← ArrayModel.algFunction_map alg n h, Measure.map_apply (by fun_prop) hs, ← Set.preimage_comp]
    simp only [Function.comp_def, Function.uncurry_apply_pair]
  have h_eq : action alg n =
      Function.uncurry (ArrayModel.algFunction alg n) ∘ fun ω ↦ (hist alg ω n, ω.1 n) := by
    funext ω
    rw [action_def, Function.comp_apply, Function.uncurry_apply_pair]
  rw [h_ker, h_eq]
  exact h

/-- The action of round `n` has conditional law the policy of the algorithm given the history and
the (trivial) observation, whatever the law `ξ` of the table. -/
lemma hasCondDistrib_action (alg : Algorithm Unit 𝓐 𝓡) (n : ℕ) :
    HasCondDistrib (action alg n)
      (fun ω ↦ (history (noObs _) (action alg) (reward alg) n ω, noObs _ n ω)) (alg.policy n)
      ((Measure.infinitePi fun _ : ℕ ↦ (volume : Measure I)).prod ξ) := by
  refine hasCondDistrib_prodMk_right_unique_iff.mpr ?_
  simpa only [hist_eq_history] using hasCondDistrib_action_hist ξ alg n

/-- The table with row `n` removed: the rows before `n` are kept and the later ones are shifted
down by one. The history and the action of round `n` only read the uniform variables and this
table. -/
private def dropRow (n : ℕ) (ω : ArrayModel.ProbSpace 𝓐 𝓡) : ArrayModel.ProbSpace 𝓐 𝓡 :=
  (ω.1, fun i ↦ if i < n then ω.2 i else ω.2 (i + 1))

omit [Countable 𝓐] in
private lemma hist_action_dropRow (alg : Algorithm Unit 𝓐 𝓡) (n : ℕ)
    (ω : ArrayModel.ProbSpace 𝓐 𝓡) :
    (hist alg (dropRow n ω) n, action alg n (dropRow n ω)) = (hist alg ω n, action alg n ω) := by
  have h : hist alg (dropRow n ω) n = hist alg ω n :=
    hist_congr alg (fun _ _ ↦ rfl) fun i hi ↦ by simp [dropRow, hi]
  simp only [action, h]
  simp only [dropRow]

/-- Under `ArrayModel.arrayMeasure ν`, row `n` of the table is independent of the history and the
action of round `n`. -/
private lemma indepFun_row_hist_action (alg : Algorithm Unit 𝓐 𝓡) (ν : Kernel 𝓐 𝓡)
    [IsMarkovKernel ν] (n : ℕ) :
    IndepFun (fun ω : ArrayModel.ProbSpace 𝓐 𝓡 ↦ ω.2 n)
      (fun ω ↦ (hist alg ω n, action alg n ω)) (ArrayModel.arrayMeasure ν) := by
  let T : (ℕ → 𝓐 → 𝓡) → (ℕ → 𝓐 → 𝓡) := fun x i ↦ if i < n then x i else x (i + 1)
  have hT : Measurable[⨆ j ∈ {j : ℕ | j ≠ n},
      MeasurableSpace.comap (fun x : ℕ → 𝓐 → 𝓡 ↦ x j) inferInstance] T := by
    rw [measurable_iff_comap_le, MeasurableSpace.comap_pi]
    refine iSup_le fun i ↦ ?_
    by_cases hi : i < n
    · simp only [T, hi, ↓reduceIte]
      exact le_iSup₂_of_le i (by simp; omega) le_rfl
    · simp only [T, hi, ↓reduceIte]
      exact le_iSup₂_of_le (i + 1) (by simp; omega) le_rfl
  have hTm : Measurable T :=
    hT.mono (iSup₂_le fun j _ ↦ Measurable.comap_le (by fun_prop)) le_rfl
  have h := ((iIndepFun_eval_streamMeasure' ν).indepFun_of_measurable_iSup_comap
    (fun _ ↦ by fun_prop) (i := n) (by simp) hT).snd_prod
    (μ := Measure.infinitePi fun _ : ℕ ↦ (volume : Measure I)) (by fun_prop) hTm
  have h_eq : (fun ω ↦ (hist alg ω n, action alg n ω)) =
      (fun ω ↦ (hist alg ω n, action alg n ω)) ∘ (fun ω ↦ (ω.1, T ω.2)) := by
    ext ω : 1
    exact (hist_action_dropRow alg n ω).symm
  rw [h_eq]
  exact h.comp measurable_id (by fun_prop)

/-- Under `ArrayModel.arrayMeasure ν`, the conditional law of the reward of round `n` given the
history and the action of round `n` is `ν` at that action. -/
private lemma hasCondDistrib_reward_hist_action (alg : Algorithm Unit 𝓐 𝓡) (ν : Kernel 𝓐 𝓡)
    [IsMarkovKernel ν] (n : ℕ) :
    HasCondDistrib (reward alg n) (fun ω ↦ (hist alg ω n, action alg n ω))
      (ν.prodMkLeft _) (ArrayModel.arrayMeasure ν) := by
  have hg : Measurable fun p : (Hist Unit 𝓐 𝓡 n × 𝓐) × (𝓐 → 𝓡) ↦ p.2 p.1.2 :=
    measurable_from_prod_countable_left (f := fun q : (𝓐 → 𝓡) × 𝓐 ↦ q.1 q.2)
      (fun a ↦ by fun_prop) |>.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hW : HasCondDistrib (fun ω : ArrayModel.ProbSpace 𝓐 𝓡 ↦ ω.2 n)
      (fun ω ↦ ((hist alg ω n, action alg n ω), (hist alg ω n, action alg n ω)))
      (Kernel.const _ (Measure.infinitePi ν)) (ArrayModel.arrayMeasure ν) :=
    ((indepFun_row_hist_action alg ν n).symm.comp (measurable_id.prodMk measurable_id)
      measurable_id).hasCondDistrib_const (by fun_prop)
      ((hasLaw_eval_streamMeasure ν n).comp (hasLaw_snd_prod _ _))
  have h := ((hasCondDistrib_self
    (X := fun ω : ArrayModel.ProbSpace 𝓐 𝓡 ↦ (hist alg ω n, action alg n ω))
    (by fun_prop)).compProd hW).comp_left hg
  have h_ker : (Kernel.id ⊗ₖ Kernel.const _ (Measure.infinitePi ν)).map
      (fun p : (Hist Unit 𝓐 𝓡 n × 𝓐) × (𝓐 → 𝓡) ↦ p.2 p.1.2) = ν.prodMkLeft _ := by
    ext p s hs
    rw [Kernel.map_apply' _ hg _ hs, Kernel.compProd_apply (hg hs), Kernel.id_apply]
    simp only [Kernel.const_apply]
    rw [lintegral_dirac' _ (measurable_measure_prodMk_left (hg hs)), Kernel.prodMkLeft_apply,
      ← Measure.infinitePi_map_eval ν p.2, Measure.map_apply (measurable_pi_apply _) hs,
      ← Set.preimage_comp]
    simp only [Function.comp_def]
  have h_eq : reward alg n = (fun p : (Hist Unit 𝓐 𝓡 n × 𝓐) × (𝓐 → 𝓡) ↦ p.2 p.1.2) ∘
      fun ω ↦ ((hist alg ω n, action alg n ω), ω.2 n) := by
    funext ω
    rw [reward_def, Function.comp_apply]
  rw [h_ker] at h
  rw [h_eq]
  exact h

/-- Under `ArrayModel.arrayMeasure ν`, the table model is a run of the algorithm against the
stochastic bandit `Environment.bandit ν`. -/
theorem isAlgEnvSeq_bandit (alg : Algorithm Unit 𝓐 𝓡) (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν] :
    IsAlgEnvSeq (noObs _) (action alg) (reward alg) alg (Environment.bandit ν)
      (ArrayModel.arrayMeasure ν) where
  hasCondDistrib_obs n :=
    hasCondDistrib_unit (measurable_history (fun _ ↦ measurable_const)
      (measurable_action alg) (measurable_reward alg) n).aemeasurable _ _
  hasCondDistrib_action := hasCondDistrib_action _ alg
  hasCondDistrib_feedback n := by
    let e : (Hist Unit 𝓐 𝓡 n × 𝓐) ≃ᵐ ((Hist Unit 𝓐 𝓡 n × Unit) × 𝓐) :=
      { toFun := fun p ↦ ((p.1, ()), p.2)
        invFun := fun p ↦ (p.1.1, p.2)
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        measurable_toFun := by simp only [Equiv.coe_fn_mk]; fun_prop
        measurable_invFun := by simp only [Equiv.symm_mk, Equiv.coe_fn_mk]; fun_prop }
    rw [feedback_bandit]
    have h := (hasCondDistrib_reward_hist_action alg ν n).measurableEquiv_comp_right e
    simp only [hist_eq_history] at h
    -- `h` is the goal up to unfolding `e`: `⇑e ∘ (H, A)` is `((H, noObs _ n), A)` since
    -- `noObs _ n ω = ()`, and `(ν.prodMkLeft _).comap e.symm` is `ν.prodMkLeft _`.
    exact h

/-- For a fixed table `x`, the history of the table model `u ↦ (u, x)` is measurable. -/
private lemma measurable_history_evalSeq (alg : Algorithm Unit 𝓐 𝓡) (x : ℕ → 𝓐 → 𝓡) (n : ℕ) :
    Measurable (history (noObs (ℕ → I)) (fun n u ↦ action alg n (u, x))
      (fun n u ↦ reward alg n (u, x)) n) :=
  measurable_history (fun _ ↦ measurable_const)
    (fun n ↦ (measurable_action alg n).comp measurable_prodMk_right)
    (fun n ↦ (measurable_reward alg n).comp measurable_prodMk_right) n

/-- For a fixed table `x`, under the uniform law of the variables `u`, the table model
`u ↦ (u, x)` is a run of the algorithm against the oblivious adversary
`Environment.evalSeq x hx` that has fixed the table `x`. -/
theorem isAlgEnvSeq_evalSeq (alg : Algorithm Unit 𝓐 𝓡) (x : ℕ → 𝓐 → 𝓡)
    (hx : ∀ n, Measurable (x n)) :
    IsAlgEnvSeq (noObs _) (fun n u ↦ action alg n (u, x)) (fun n u ↦ reward alg n (u, x)) alg
      (Environment.evalSeq x hx) (Measure.infinitePi fun _ : ℕ ↦ (volume : Measure I)) where
  hasCondDistrib_obs n := hasCondDistrib_unit (measurable_history_evalSeq alg x n).aemeasurable _ _
  hasCondDistrib_action n := by
    have h := (hasCondDistrib_action (Measure.dirac x) alg n).comp_hasLaw
      ⟨measurable_prodMk_right.aemeasurable, (Measure.prod_dirac x).symm⟩
    -- The history commutes with precomposition by `u ↦ (u, x)`.
    have h_hist : (fun ω ↦ (history (noObs _) (action alg) (reward alg) n ω,
          noObs (ArrayModel.ProbSpace 𝓐 𝓡) n ω)) ∘ (fun u : ℕ → I ↦ (u, x)) =
        fun u ↦ (history (noObs (ℕ → I)) (fun n u ↦ action alg n (u, x))
          (fun n u ↦ reward alg n (u, x)) n u, noObs (ℕ → I) n u) := by
      funext u
      simp only [Function.comp_apply, noObs_apply, Prod.mk.injEq, and_true]
      funext i
      simp only [history_apply, noObs_apply]
    rwa [h_hist, Function.comp_def] at h
  hasCondDistrib_feedback n := by
    rw [feedback_evalSeq]
    have h := hasCondDistrib_comp_self (X := fun u ↦ ((history (noObs (ℕ → I))
        (fun n u ↦ action alg n (u, x)) (fun n u ↦ reward alg n (u, x)) n u, noObs (ℕ → I) n u),
        action alg n (u, x))) (μ := Measure.infinitePi fun _ : ℕ ↦ (volume : Measure I))
      (f := fun p : (Hist Unit 𝓐 𝓡 n × Unit) × 𝓐 ↦ x n p.2) ((hx n).comp measurable_snd)
      (((measurable_history_evalSeq alg x n).prodMk measurable_const).prodMk
        ((measurable_action alg n).comp measurable_prodMk_right)).aemeasurable
    have h_eq : (fun u ↦ reward alg n (u, x)) = fun u ↦ x n (action alg n (u, x)) := by
      funext u
      rw [reward_def]
    simp only [Function.comp_def] at h
    rw [h_eq]
    exact h

end Laws

end TableModel

section StreamMeasure

variable {α : Type*} [MeasurableSpace α] {ν : Kernel α ℝ} [IsMarkovKernel ν] {a : α}

/-- The total reward `∑_{t < n} x t a` of arm `a` over the first `n` rows of a table
`x ∼ streamMeasure ν` is integrable when the arm is. -/
lemma integrable_sum_eval_streamMeasure (hν : Integrable id (ν a)) (n : ℕ) :
    Integrable (fun x : ℕ → α → ℝ ↦ ∑ t ∈ range n, x t a) (streamMeasure ν) :=
  integrable_finsetSum _ fun t _ ↦ integrable_eval_streamMeasure ν t a hν

/-- The expected total reward `∑_{t < n} x t a` of arm `a` over the first `n` rows of a table
`x ∼ streamMeasure ν` is `n` times its mean. -/
lemma integral_sum_eval_streamMeasure (hν : Integrable id (ν a)) (n : ℕ) :
    ∫ x, ∑ t ∈ range n, x t a ∂(streamMeasure ν) = n * (ν a)[id] := by
  rw [integral_finsetSum _ fun t _ ↦ integrable_eval_streamMeasure ν t a hν]
  simp [integral_eval_streamMeasure]

end StreamMeasure

section Mixture

variable [Countable 𝓐] (alg : Algorithm Unit 𝓐 𝓡) (ν : Kernel 𝓐 𝓡) [IsMarkovKernel ν]

private lemma measurable_trajectory_table :
    Measurable (trajectory (noObs _) (TableModel.action alg) (TableModel.reward alg)) :=
  measurable_trajectory (fun _ ↦ measurable_const) (TableModel.measurable_action alg)
    (TableModel.measurable_reward alg)

/-- For a fixed table `x`, the law of the run against `Environment.evalSeq x _` is the image of the
uniform law under the table model `u ↦ (u, x)`. -/
private lemma trajMeasure_evalSeq_eq_map (x : ℕ → 𝓐 → 𝓡) (hx : ∀ n, Measurable (x n)) :
    trajMeasure alg (Environment.evalSeq x hx) =
      (Measure.infinitePi fun _ : ℕ ↦ (volume : Measure I)).map
        ((trajectory (noObs _) (TableModel.action alg) (TableModel.reward alg)) ∘
          fun u ↦ (u, x)) :=
  ((TableModel.isAlgEnvSeq_evalSeq alg x hx).map_trajectory).symm

/-- For a fixed table `x`, the probability of a measurable set `S` of trajectories under the run
against `Environment.evalSeq x _` is the uniform probability of the variables `u` for which the
table model `(u, x)` has its trajectory in `S`. -/
private lemma trajMeasure_evalSeq_apply_eq (x : ℕ → 𝓐 → 𝓡) (hx : ∀ n, Measurable (x n))
    {S : Set (ℕ → Round Unit 𝓐 𝓡)} (hS : MeasurableSet S) :
    trajMeasure alg (Environment.evalSeq x hx) S =
      (Measure.infinitePi fun _ : ℕ ↦ (volume : Measure I)) ((fun u ↦ (u, x)) ⁻¹'
        (trajectory (noObs _) (TableModel.action alg) (TableModel.reward alg) ⁻¹' S)) := by
  rw [trajMeasure_evalSeq_eq_map, Measure.map_apply
    ((measurable_trajectory_table alg).comp measurable_prodMk_right) hS, Set.preimage_comp]

/-- For a fixed table `x`, the expectation of `f` under the run against `Environment.evalSeq x _`
is the expectation over the uniform variables `u` of `f` at the trajectory of the table model
`(u, x)`. -/
private lemma integral_trajMeasure_evalSeq_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ℕ → Round Unit 𝓐 𝓡) → E} (hf : StronglyMeasurable f) (x : ℕ → 𝓐 → 𝓡)
    (hx : ∀ n, Measurable (x n)) :
    ∫ τ, f τ ∂(trajMeasure alg (Environment.evalSeq x hx)) =
      ∫ u, (f ∘ trajectory (noObs _) (TableModel.action alg) (TableModel.reward alg)) (u, x)
        ∂(Measure.infinitePi fun _ : ℕ ↦ (volume : Measure I)) := by
  rw [trajMeasure_evalSeq_eq_map, integral_map
    ((measurable_trajectory_table alg).comp measurable_prodMk_right).aemeasurable
    hf.aestronglyMeasurable]
  simp only [Function.comp_apply]

/-- The probability of a measurable set of trajectories under the run against
`Environment.evalSeq x _` is a measurable function of the table `x`. -/
lemma measurable_trajMeasure_evalSeq_apply
    {S : Set (ℕ → Round Unit 𝓐 𝓡)} (hS : MeasurableSet S) :
    Measurable fun x : ℕ → 𝓐 → 𝓡 ↦
      trajMeasure alg (Environment.evalSeq x fun _ ↦ .of_discrete) S := by
  simp_rw [trajMeasure_evalSeq_apply_eq alg _ _ hS]
  exact measurable_measure_prodMk_right (hS.preimage (measurable_trajectory_table alg))

/-- The law of the run against `Environment.evalSeq x _` is a measurable function of the table
`x`, as a measure-valued map. -/
lemma measurable_trajMeasure_evalSeq :
    Measurable fun x : ℕ → 𝓐 → 𝓡 ↦ trajMeasure alg (Environment.evalSeq x fun _ ↦ .of_discrete) :=
  Measure.measurable_of_measurable_coe _ fun _ hS ↦ measurable_trajMeasure_evalSeq_apply alg hS

/-- **A stochastic bandit is a mixture of reward tables.** The law of the run of an algorithm
against the stochastic bandit `Environment.bandit ν` is the mixture, over the tables `x` whose
rows are independent with law `⨂ a, ν a`, of the laws of the runs against the oblivious
adversaries `Environment.evalSeq x _`. -/
theorem trajMeasure_bandit_eq_bind :
    trajMeasure alg (Environment.bandit ν) =
      (streamMeasure ν).bind fun x ↦
        trajMeasure alg (Environment.evalSeq x fun _ ↦ .of_discrete) := by
  ext S hS
  rw [Measure.bind_apply hS (measurable_trajMeasure_evalSeq alg).aemeasurable,
    ← (TableModel.isAlgEnvSeq_bandit alg ν).map_trajectory,
    Measure.map_apply (measurable_trajectory_table alg) hS, ArrayModel.arrayMeasure,
    Measure.prod_apply_symm (hS.preimage (measurable_trajectory_table alg))]
  exact lintegral_congr fun x ↦ (trajMeasure_evalSeq_apply_eq alg x _ hS).symm

variable {E : Type*} [NormedAddCommGroup E] {f : (ℕ → Round Unit 𝓐 𝓡) → E}

/-- The integral of `f` along the table model is integrable on the product space when `f` is
integrable under the run against the stochastic bandit. -/
private lemma integrable_comp_trajectory_table (hf : Integrable f (trajMeasure alg
    (Environment.bandit ν))) :
    Integrable (f ∘ trajectory (noObs _) (TableModel.action alg) (TableModel.reward alg))
      (ArrayModel.arrayMeasure ν) := by
  rw [← (TableModel.isAlgEnvSeq_bandit alg ν).map_trajectory] at hf
  exact hf.comp_measurable (measurable_trajectory_table alg)

/-- The expectation of `f` under the run against `Environment.evalSeq x _` is an integrable
function of the table `x ∼ streamMeasure ν`, when `f` is strongly measurable and integrable under
the run against the stochastic bandit `Environment.bandit ν`. -/
lemma integrable_integral_trajMeasure_evalSeq [NormedSpace ℝ E]
    (hf_meas : StronglyMeasurable f) (hf : Integrable f (trajMeasure alg (Environment.bandit ν))) :
    Integrable (fun x ↦ ∫ τ, f τ ∂(trajMeasure alg (Environment.evalSeq x fun _ ↦ .of_discrete)))
      (streamMeasure ν) := by
  simp_rw [integral_trajMeasure_evalSeq_eq alg hf_meas]
  exact (integrable_comp_trajectory_table alg ν hf).integral_prod_right

/-- **A stochastic bandit is a mixture of reward tables**, for integrals: the expectation of `f`
under the run against the stochastic bandit `Environment.bandit ν` is the average over the tables
`x ∼ streamMeasure ν` of its expectations under the runs against `Environment.evalSeq x _`. -/
theorem integral_trajMeasure_bandit [NormedSpace ℝ E]
    (hf_meas : StronglyMeasurable f) (hf : Integrable f (trajMeasure alg (Environment.bandit ν))) :
    ∫ τ, f τ ∂(trajMeasure alg (Environment.bandit ν)) =
      ∫ x, ∫ τ, f τ ∂(trajMeasure alg (Environment.evalSeq x fun _ ↦ .of_discrete))
        ∂(streamMeasure ν) := by
  set F := f ∘ trajectory (noObs _) (TableModel.action alg) (TableModel.reward alg)
  calc ∫ τ, f τ ∂(trajMeasure alg (Environment.bandit ν))
    _ = ∫ ω, F ω ∂(ArrayModel.arrayMeasure ν) := by
      rw [← (TableModel.isAlgEnvSeq_bandit alg ν).map_trajectory, integral_map
        (measurable_trajectory_table alg).aemeasurable (by
          rw [(TableModel.isAlgEnvSeq_bandit alg ν).map_trajectory]
          exact hf_meas.aestronglyMeasurable)]
      simp only [F, Function.comp_apply]
    _ = ∫ x, ∫ u, F (u, x) ∂(Measure.infinitePi fun _ : ℕ ↦ (volume : Measure I))
        ∂(streamMeasure ν) :=
      integral_prod_symm _ (integrable_comp_trajectory_table alg ν hf)
    _ = _ := by simp_rw [integral_trajMeasure_evalSeq_eq alg hf_meas, F]

end Mixture

end LMLExplore.Bandits
