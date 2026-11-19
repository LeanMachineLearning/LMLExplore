/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.ConditionalProbability
public import LMLExplore.SequentialLearning.Algorithm
import LMLExplore.Probability.HasCondDistrib
import LMLExplore.Probability.Martingale.Hoeffding

/-!
# Feedbacks of a stochastic bandit along a run

This file studies the feedbacks of a run of an algorithm against a stochastic bandit
`Environment.bandit ν`, given the past and the action of their round.

**Blocks of rounds with predetermined actions.** Consider an event `F` known when the action of
round `n` is chosen (an event of `h.filtrationAction n`). Suppose that on `F` the actions of the
rounds `n, n + 1, …, n + L - 1` are almost surely the predetermined arms `a 0, …, a (L - 1)`.
Then, conditionally on `F`, the feedbacks of these `L` rounds are independent, the feedback of
round `n + j` having law `ν (a j)`. The actions may depend on the feedbacks of the block: only
their values on `F` are fixed. For `L = 1` this is LML's
`Learning.IsAlgEnvSeq.hasLaw_feedback_cond_bandit`, the law of the feedback of one round given the
past and the action of that round.

This is how the observations of an algorithm that commits to a sequence of arms in advance, such as
a phase of a phased-elimination algorithm, are analyzed: given the information at the start of the
block, the block is a sample from the product of the laws of its arms.

**Concentration around the conditional means.** Given the past and the action `A k` of round
`k`, a function `g k (A k, Y k)` of the action and the feedback has conditional mean
`∫ y, g k (A k, y) ∂(ν (A k))`. For bounded functions, the deviations from these conditional means
are martingale differences, and the Azuma–Hoeffding inequality bounds their sum. This compares a
quantity realized along the run with its version averaged over the feedbacks given the actions,
such as a regret at the realized feedbacks with a pseudo-regret.

## Main statements

* `Learning.IsAlgEnvSeq.measure_inter_forall_feedback_mem_bandit`:
  `P(F ∩ {∀ j < L, Y_{n+j} ∈ B j}) = P(F) ∏_{j < L} ν (a j) (B j)`.
* `Learning.IsAlgEnvSeq.hasLaw_pi_feedback_cond_bandit`: the vector `(Y_{n+j})_{j < L}` has law the
  product measure `Measure.pi fun j ↦ ν (a j)` under `P[|F]`.
* `Learning.IsAlgEnvSeq.condExp_comp_action_feedback_bandit`: the conditional expectation of
  `g (A n, Y n)` given the past and the action of round `n` is `∫ y, g (A n, y) ∂(ν (A n))`.
* `Learning.IsAlgEnvSeq.measureReal_le_abs_sum_integral_sub_le_bandit`: for `g k` with values in
  `[a k, b k]`, the Azuma–Hoeffding bound
  `P(ε ≤ |∑ k < n, (∫ y, g k (A k, y) ∂(ν (A k)) - g k (A k, Y k))|)
    ≤ 2 exp (-2 ε ^ 2 / ∑ k < n, (b k - a k) ^ 2)`.
* `Learning.IsAlgEnvSeq.le_measureReal_abs_sum_integral_sub_le_bandit`: its `1 - δ` form, with
  probability at least `1 - δ` the sum of the deviations is at most
  `√(∑ k < n, (b k - a k) ^ 2 * log (2 / δ) / 2)` in absolute value.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real

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
    HasLaw (fun ω (j : Fin L) ↦ Y (n + j) ω) (Measure.pi fun j ↦ ν (a j)) P[|F] :=
  hasLaw_pi_cond_of_measure_inter_forall_mem (Z := fun ω (j : Fin L) ↦ Y (n + j) ω)
    (Measurable.of_eval fun j ↦ h.measurable_feedback (n + j)) hPF (measure_ne_top P F)
    fun _ hB ↦ h.measure_inter_forall_feedback_mem_bandit hF ha hB

/-! ### Concentration around the conditional means -/

/-- **Conditional mean of a function of the action and the feedback.** Along a run against the
stochastic bandit `Environment.bandit ν`, given the past and the action of round `n`, the
function `g (A n, Y n)` of the action and the feedback of round `n` has conditional expectation
`∫ y, g (A n, y) ∂(ν (A n))`. -/
theorem IsAlgEnvSeq.condExp_comp_action_feedback_bandit [IsFiniteMeasure P]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) (n : ℕ) {g : 𝓐 × 𝓨 → ℝ}
    (hg : Measurable g) (hint : Integrable (fun ω ↦ g (A n ω, Y n ω)) P) :
    P[fun ω ↦ g (A n ω, Y n ω) | h.filtrationAction n] =ᵐ[P]
      fun ω ↦ ∫ y, g (A n ω, y) ∂(ν (A n ω)) := by
  have hX : Measurable fun ω ↦ ((history O A Y n ω, O n ω), A n ω) :=
    ((h.measurable_history n).prodMk (h.measurable_obs n)).prodMk (h.measurable_action n)
  -- the feedback has conditional law `ν (A n)` given the past and the action
  have hcd := h.hasCondDistrib_feedback n
  rw [feedback_bandit] at hcd
  have hg' : Measurable fun z : ((Hist Unit 𝓐 𝓨 n × Unit) × 𝓐) × 𝓨 ↦ g (z.1.2, z.2) :=
    hg.comp (measurable_fst.snd.prodMk measurable_snd)
  rw [h.filtrationAction_eq_comap]
  filter_upwards [hcd.condExp_prod_ae_eq_integral hX
    ((hcd.integrable_comp_prodMk_iff hg'.aestronglyMeasurable).1 hint)] with ω hω
  rw [hω, Kernel.prodMkLeft_apply]

/-- **Azuma–Hoeffding inequality for the feedbacks of a stochastic bandit.** Along a run against
`Environment.bandit ν`, let `g k` be measurable with values in `[a k, b k]`. Then for `ε ≥ 0`, the
sum of the deviations of `g k (A k, Y k)` from their conditional means
`∫ y, g k (A k, y) ∂(ν (A k))` satisfies
`P(ε ≤ |∑ k < n, (∫ y, g k (A k, y) ∂(ν (A k)) - g k (A k, Y k))|)
  ≤ 2 exp (-2 ε ^ 2 / ∑ k < n, (b k - a k) ^ 2)`. -/
theorem IsAlgEnvSeq.measureReal_le_abs_sum_integral_sub_le_bandit [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) {g : ℕ → 𝓐 × 𝓨 → ℝ}
    (hg : ∀ k, Measurable (g k)) {a b : ℕ → ℝ} (hgab : ∀ k p, g k p ∈ Set.Icc (a k) (b k))
    (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤
        |∑ k ∈ range n, (∫ y, g k (A k ω, y) ∂(ν (A k ω)) - g k (A k ω, Y k ω))|} ≤
      2 * exp (-2 * ε ^ 2 / ∑ k ∈ range n, (b k - a k) ^ 2) := by
  -- `g k (A k, Y k)` is known after round `k`, that is when the action of round `k + 1` is chosen
  have hX : ∀ k, Measurable[h.filtrationAction (k + 1)] fun ω ↦ g k (A k ω, Y k ω) := fun k ↦
    ((hg k).comp ((h.adapted_action k).prodMk (h.adapted_feedback k))).mono
      (h.filtration_le_filtrationAction_succ k) le_rfl
  have hce : ∀ k, P[fun ω ↦ g k (A k ω, Y k ω) | h.filtrationAction k] =ᵐ[P]
      fun ω ↦ ∫ y, g k (A k ω, y) ∂(ν (A k ω)) := fun k ↦
    h.condExp_comp_action_feedback_bandit k (hg k)
      (.of_mem_Icc (a k) (b k) ((hX k).mono (h.filtrationAction.le _) le_rfl).aemeasurable
        (.of_forall fun ω ↦ hgab k _))
  have hset : {ω | ε ≤ |∑ k ∈ range n,
        (P[fun ω ↦ g k (A k ω, Y k ω) | h.filtrationAction k] ω - g k (A k ω, Y k ω))|} =ᵐ[P]
      {ω | ε ≤ |∑ k ∈ range n, (∫ y, g k (A k ω, y) ∂(ν (A k ω)) - g k (A k ω, Y k ω))|} := by
    filter_upwards [ae_all_iff.2 hce] with ω hω
    rw [sum_congr rfl fun k _ ↦ congrArg (· - g k (A k ω, Y k ω)) (hω k)]
  rw [← measureReal_congr hset]
  exact LMLExplore.measureReal_le_abs_sum_condExp_sub_le hX n
    (fun k _ ↦ .of_forall fun ω ↦ hgab k _) hε

/-- **Azuma–Hoeffding inequality for the feedbacks of a stochastic bandit, with probability
`1 - δ`.** Along a run against `Environment.bandit ν`, let `g k` be measurable with values in
`[a k, b k]`. Then for `δ > 0`, with probability at least `1 - δ`, the sum of the deviations of
`g k (A k, Y k)` from their conditional means `∫ y, g k (A k, y) ∂(ν (A k))` is at most
`√(∑ k < n, (b k - a k) ^ 2 * log (2 / δ) / 2)` in absolute value. -/
theorem IsAlgEnvSeq.le_measureReal_abs_sum_integral_sub_le_bandit [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) {g : ℕ → 𝓐 × 𝓨 → ℝ}
    (hg : ∀ k, Measurable (g k)) {a b : ℕ → ℝ} (hgab : ∀ k p, g k p ∈ Set.Icc (a k) (b k))
    (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ P.real {ω |
      |∑ k ∈ range n, (∫ y, g k (A k ω, y) ∂(ν (A k ω)) - g k (A k ω, Y k ω))| ≤
        √((∑ k ∈ range n, (b k - a k) ^ 2) * log (2 / δ) / 2)} := by
  set D : Ω → ℝ := fun ω ↦ ∑ k ∈ range n, (∫ y, g k (A k ω, y) ∂(ν (A k ω)) - g k (A k ω, Y k ω))
  set S := ∑ k ∈ range n, (b k - a k) ^ 2
  set ε := √(S * log (2 / δ) / 2)
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact (sub_nonpos.2 hδ1).trans measureReal_nonneg
  have hlog : 0 < log (2 / δ) := log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hS : 0 ≤ S := sum_nonneg fun k _ ↦ sq_nonneg _
  -- either `|D| ≤ ε`, or `ε ≤ |D|`, which has probability at most `δ`
  have hu := measureReal_union_le (μ := P) {ω | |D ω| ≤ ε} {ω | ε ≤ |D ω|}
  rw [show {ω | |D ω| ≤ ε} ∪ {ω | ε ≤ |D ω|} = Set.univ from
    Set.eq_univ_of_forall fun ω ↦ le_total (|D ω|) ε, probReal_univ] at hu
  rcases hS.eq_or_lt with hS0 | hSpos
  · -- if every range is a point, then every `g k` is constant and every deviation is `0`
    have hba : ∀ k ∈ range n, b k = a k := fun k hk ↦ by
      have := (sum_eq_zero_iff_of_nonneg fun k _ ↦ sq_nonneg (b k - a k)).1 hS0.symm k hk
      linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 this]
    have hga : ∀ k ∈ range n, ∀ p, g k p = a k := fun k hk p ↦
      le_antisymm ((hgab k p).2.trans_eq (hba k hk)) (hgab k p).1
    refine (sub_le_self _ hδ.le).trans_eq ?_
    rw [← probReal_univ (μ := P)]
    congr 1
    refine (Set.eq_univ_of_forall fun ω ↦ ?_).symm
    have hD : D ω = 0 := sum_eq_zero fun k hk ↦ by simp [hga k hk]
    change |D ω| ≤ ε
    rw [hD, abs_zero]
    positivity
  -- at this level, the tail bound is exactly `δ`
  have hexp : 2 * exp (-2 * ε ^ 2 / S) = δ := by
    rw [sq_sqrt (by positivity),
      show -2 * (S * log (2 / δ) / 2) / S = -log (2 / δ) by field_simp,
      exp_neg, exp_log (by positivity)]
    field_simp
  have htail := h.measureReal_le_abs_sum_integral_sub_le_bandit hg hgab n (ε := ε) (by positivity)
  linarith

end Learning
