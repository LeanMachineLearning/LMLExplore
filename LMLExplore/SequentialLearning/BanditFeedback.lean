/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.SequentialLearning.Algorithm
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ConditionalProbability

/-!
# Feedbacks of a block of rounds with predetermined actions

Consider a run of an algorithm against a stochastic bandit `Environment.bandit ν`, and an event `F`
known when the action of round `n` is chosen (an event of `h.filtrationAction n`). Suppose that on
`F` the actions of the rounds `n, n + 1, …, n + L - 1` are almost surely the predetermined arms
`a 0, …, a (L - 1)`. Then, conditionally on `F`, the feedbacks of these `L` rounds are independent,
the feedback of round `n + j` having law `ν (a j)`. The actions may depend on the feedbacks of the
block: only their values on `F` are fixed. For `L = 1` this is LML's
`Learning.IsAlgEnvSeq.hasLaw_feedback_cond_bandit`, the law of the feedback of one round given the
past and the action of that round.

This is how the observations of an algorithm that commits to a sequence of arms in advance, such as
a phase of a phased-elimination algorithm, are analyzed: given the information at the start of the
block, the block is a sample from the product of the laws of its arms.

## Main statements

* `Learning.IsAlgEnvSeq.measure_inter_forall_feedback_mem_bandit`:
  `P(F ∩ {∀ j < L, Y_{n+j} ∈ B j}) = P(F) ∏_{j < L} ν (a j) (B j)`.
* `Learning.IsAlgEnvSeq.hasLaw_pi_feedback_cond_bandit`: the vector `(Y_{n+j})_{j < L}` has law the
  product measure `Measure.pi fun j ↦ ν (a j)` under `P[|F]`.
-/

public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace Learning

variable {𝓐 𝓨 Ω : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}

variable {alg : Algorithm Unit 𝓐 𝓨} {ν : Kernel 𝓐 𝓨} [IsMarkovKernel ν]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

/-- **Feedbacks of a block of rounds with predetermined actions.** Along a run against the
stochastic bandit `Environment.bandit ν`, let `F` be an event known when the action of round `n`
is chosen, on which the actions of the rounds `n + j`, `j < L`, are almost surely `a j`. Then the
probability that `F` holds and that the feedback of round `n + j` lies in `B j` for every `j < L`
is `P(F) ∏_{j < L} ν (a j) (B j)`. -/
theorem IsAlgEnvSeq.measure_inter_forall_feedback_mem_bandit [SFinite P]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) {n L : ℕ} {F : Set Ω}
    (hF : MeasurableSet[h.filtrationAction n] F) {a : Fin L → 𝓐}
    (ha : ∀ j : Fin L, ∀ᵐ ω ∂P, ω ∈ F → A (n + j) ω = a j) {B : Fin L → Set 𝓨}
    (hB : ∀ j, MeasurableSet (B j)) :
    P (F ∩ {ω | ∀ j, Y (n + j) ω ∈ B j}) = P F * ∏ j, ν (a j) (B j) := by
  induction L with
  | zero => simp
  | succ L ih =>
    -- The event of the first `L` rounds of the block, known when the action of round `n + L` is
    -- chosen.
    set G := F ∩ {ω | ∀ j : Fin L, Y (n + j) ω ∈ B j.castSucc} with hG_def
    have hG : MeasurableSet[h.filtrationAction (n + L)] G := by
      refine (h.filtrationAction.mono (Nat.le_add_right n L) _ hF).inter ?_
      simp only [Set.ofPred_forall]
      exact .iInter fun j ↦ h.measurable_feedback_filtrationAction_of_lt (by omega) (hB _)
    have h_eq : F ∩ {ω | ∀ j, Y (n + j) ω ∈ B j} = G ∩ Y (n + L) ⁻¹' B (Fin.last L) := by
      ext ω
      simp only [Fin.forall_fin_succ', Fin.val_castSucc, Fin.val_last, hG_def, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_preimage, and_assoc]
    have hY : Measurable (Y (n + L)) := h.measurable_feedback (n + L)
    -- On `G`, the feedback of round `n + L` has law `ν (a (Fin.last L))`.
    have h_last : P (G ∩ Y (n + L) ⁻¹' B (Fin.last L)) = P G * ν (a (Fin.last L)) (B (Fin.last L))
        := by
      calc P (G ∩ Y (n + L) ⁻¹' B (Fin.last L))
          = ∫⁻ ω in G, (B (Fin.last L)).indicator 1 (Y (n + L) ω) ∂P := by
            rw [Set.inter_comm, ← Measure.restrict_apply (hY (hB _)),
              ← lintegral_indicator_one (hY (hB _))]
            exact lintegral_congr fun ω ↦ Set.indicator_comp_right (g := 1) (Y (n + L))
        _ = ∫⁻ ω in G, ν (A (n + L) ω) (B (Fin.last L)) ∂P := by
            rw [h.setLIntegral_comp_feedback hG (measurable_one.indicator (hB _))]
            simp [Environment.feedbackKernel, feedback_bandit, lintegral_indicator_one (hB _)]
        _ = ∫⁻ _ in G, ν (a (Fin.last L)) (B (Fin.last L)) ∂P := by
            refine setLIntegral_congr_fun_ae (h.filtrationAction.le _ _ hG) ?_
            filter_upwards [ha (Fin.last L)] with ω hω hωG
            have hA := hω hωG.1
            rw [Fin.val_last] at hA
            rw [hA]
        _ = P G * ν (a (Fin.last L)) (B (Fin.last L)) := by rw [setLIntegral_const, mul_comm]
    rw [h_eq, h_last, ih (fun j ↦ ha j.castSucc) (fun j ↦ hB j.castSucc),
      Fin.prod_univ_castSucc, mul_assoc]

/-- **Feedbacks of a block of rounds with predetermined actions**, law form. Along a run against
the stochastic bandit `Environment.bandit ν`, let `F` be an event of positive probability, known
when the action of round `n` is chosen, on which the actions of the rounds `n + j`, `j < L`, are
almost surely `a j`. Then under `P` conditioned on `F`, the feedbacks of these rounds are
independent, the feedback of round `n + j` having law `ν (a j)`. -/
theorem IsAlgEnvSeq.hasLaw_pi_feedback_cond_bandit [IsFiniteMeasure P]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) {n L : ℕ} {F : Set Ω}
    (hF : MeasurableSet[h.filtrationAction n] F) (hPF : P F ≠ 0) {a : Fin L → 𝓐}
    (ha : ∀ j : Fin L, ∀ᵐ ω ∂P, ω ∈ F → A (n + j) ω = a j) :
    HasLaw (fun ω (j : Fin L) ↦ Y (n + j) ω) (Measure.pi fun j ↦ ν (a j)) P[|F] := by
  have hYm : Measurable fun ω (j : Fin L) ↦ Y (n + j) ω :=
    Measurable.of_eval fun j ↦ h.measurable_feedback (n + j)
  refine ⟨hYm.aemeasurable, (Measure.pi_eq fun B hB ↦ ?_).symm⟩
  rw [Measure.map_apply hYm (.univ_pi hB), cond_apply (h.filtrationAction.le _ _ hF)]
  have h_pre : (fun ω (j : Fin L) ↦ Y (n + j) ω) ⁻¹' Set.univ.pi B =
      {ω | ∀ j, Y (n + j) ω ∈ B j} := by
    ext ω
    simp [Set.mem_pi]
  rw [h_pre, h.measure_inter_forall_feedback_mem_bandit hF ha hB, ← mul_assoc,
    ENNReal.inv_mul_cancel hPF (measure_ne_top P F), one_mul]

end Learning
