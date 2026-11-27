/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Strong
public import LMLExplore.Identification.CumulativeTracking
public import LMLExplore.Identification.GLR
public import LMLExplore.Identification.OptimisticSaddlePoint
public import LMLExplore.OnlineLearning.AdaHedge
public import LMLExplore.OnlineLearning.BestResponse

/-!
# Pure exploration by solving games

The pure exploration meta-algorithm of [DKM19, Algorithm 1] solves the pure exploration game
online. After `n` rounds with history `h`, it computes a candidate answer `j = cand n h` (in
[DKM19], the answer of the most likely model of a confidence region around the estimates), and
two learners attached to `j` play the game of `j`:

* the *allocation player* of `j` plays weights `w_n` on the arms, from the optimistic gains of
  the previous rounds whose candidate was `j`;
* the *alternative player* of `j` plays a finitely supported distribution `q_n` on the models,
  from the losses `λ ↦ ∑ a, w_s a d_a(x_{s,a}, λ)` of the previous rounds whose candidate was `j`
  and, so that it may best-respond, from the loss of round `n`, where `x_s` are the estimates of
  the arm means and `d_a(y, λ)` is the divergence from a mean `y` to the arm `a` of a model `λ`;
* the gains of round `n` are the *optimistic* gains
  `U_n a = max (bonus a) (max (E_{λ ∼ q_n} d_a(lo_a, λ)) (E_{λ ∼ q_n} d_a(hi_a, λ)))`, for an
  exploration bonus (in [DKM19], `f(n) / N_a`) and a confidence interval `[lo_a, hi_a]` for the
  mean of arm `a`: the largest expected divergence over the confidence interval when the
  divergences are convex in the mean.

The arms are sampled by cumulative tracking of the weights (`cumulativeTracking`), and the
algorithm stops with the GLRT of the candidate answer, for the evidence
`Z_n(h, λ) = ∑ a, N_a d_a(x_a, λ)`.

The learners of the answer `j` are fed the gains and losses of all the rounds, with zero gains and
losses at the rounds whose candidate is not `j`: these rounds contribute nothing to the regret of
the learners of `j`, and for AdaHedge they do not change the cumulative losses.

This file defines the meta-algorithm as an identification algorithm for any choice of these
ingredients, proves that it is `δ`-PAC whenever it stops almost surely and the deviations of the
evidence at the true model are controlled ([DKM19, Theorem 1], from `IdentTask.isDeltaPAC_glrt`),
and proves that the regret bounds of the learners make it an approximate optimistic saddle point
algorithm along every trajectory [DKM19, Definition 2, Appendix D.2], which is the input of the
analysis of `Identification/OptimisticSaddlePoint.lean`. AdaHedge on gains
(`OnlineLearning.adaHedgeAlloc`) is an allocation player of regret `2 Δ_t` and Best-Response
(`OnlineLearning.bestResponse`) is an alternative player without regret, the instance of
[DKM19, Lemma 3].

## Main definitions

* `LMLExplore.Identification.GameSamplingRule`: the ingredients of the meta-algorithm: the
  candidate answers, the estimates, the confidence intervals, the exploration bonuses, the
  divergences and the two families of learners.
* `GameSamplingRule.loss`, `GameSamplingRule.optimisticGain`: the loss of the alternative player
  and the optimistic gains.
* `GameSamplingRule.feedback`: the gains and losses fed to the learners at the rounds of a history.
* `GameSamplingRule.weights`, `GameSamplingRule.altDist`, `GameSamplingRule.gains`: the plays of
  the two learners of the candidate answer and the optimistic gains, after `n` rounds with history
  `h`.
* `GameSamplingRule.gainSeq`, `GameSamplingRule.lossSeq`: along a trajectory, the gains and losses
  fed to the learners of an answer.
* `GameSamplingRule.evidence`: the evidence `∑ a, N_a d_a(x_a, λ)` of the GLRT.
* `LMLExplore.Identification.IdentTask.gameExploration`: the meta-algorithm [DKM19, Algorithm 1].

## Main statements

* `GameSamplingRule.feedback_history`, `GameSamplingRule.weights_history`,
  `GameSamplingRule.altDist_history`: along a trajectory, the learners of the candidate answer are
  fed the gains and losses `gainSeq` and `lossSeq` of their answer.
* `GameSamplingRule.sum_gains_le_sum_sum_mul_add_of_regret`: **the meta-algorithm is an
  approximate optimistic saddle point algorithm** [DKM19, Definition 2, Appendix D.2]: along every
  trajectory, if the learners of `j` have regrets `Rk` and `Rl` on the gains and losses fed to
  them, then on the rounds of `j`,
  `∑ U_s a ≤ ∑ ∑ b, w_s b d_b(x_{s,b}, λ) + (Rk + Rl + ∑ ∑ b, w_s b C_s b)`, where `C_s a` bounds
  the optimism `U_s a - E_{λ ∼ q_s} d_a(x_{s,a}, λ)`.
* `GameSamplingRule.sum_gains_le_sum_sum_mul_add_of_adaHedge`: the same inequality for AdaHedge
  against Best-Response, with slack `2 Δ_t + ∑ ∑ b, w_s b C_s b` [DKM19, Lemma 3].
* `GameSamplingRule.bonus_le_optimisticGain`,
  `GameSamplingRule.sum_mul_divergence_le_optimisticGain`: the optimistic gains are at least the
  exploration bonus, and at least the expected divergence at every mean of the confidence interval
  when the divergences are convex in the mean.
* `LMLExplore.Identification.IdentTask.isDeltaPAC_gameExploration`: the meta-algorithm is `δ`-PAC
  [DKM19, Theorem 1].

## References

* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019 (arXiv:1906.10431).
-/

public section

open MeasureTheory ProbabilityTheory Learning Convexity Finset

open scoped ENNReal

namespace LMLExplore.Identification

/-- The ingredients of the pure exploration meta-algorithm of [DKM19, Algorithm 1], for arms `α`,
models `Θ`, answers `ℐ` and observations `𝓨`. The candidate answer, the estimates of the means, the
confidence intervals and the exploration bonuses are functions of the history `h` of the first `n`
rounds, and each answer `j` has two learners:
* the allocation player `alloc j t g`, the weights on the arms that it plays at round `t` given
  the gains `g` of the rounds before `t`;
* the alternative player `alt j t ℓ`, the finitely supported distribution on the models that it
  plays at round `t` given the losses `ℓ` of the rounds up to and including `t`. -/
structure GameSamplingRule (α Θ ℐ 𝓨 : Type*) where
  /-- The candidate answer after `n` rounds with history `h`. -/
  cand : (n : ℕ) → Hist Unit α 𝓨 n → ℐ
  /-- The estimates of the means of the arms after `n` rounds with history `h`. -/
  est : (n : ℕ) → Hist Unit α 𝓨 n → α → ℝ
  /-- The lower ends of the confidence intervals of the means of the arms. -/
  lower : (n : ℕ) → Hist Unit α 𝓨 n → α → ℝ
  /-- The upper ends of the confidence intervals of the means of the arms. -/
  upper : (n : ℕ) → Hist Unit α 𝓨 n → α → ℝ
  /-- The exploration bonuses of the arms. -/
  bonus : (n : ℕ) → Hist Unit α 𝓨 n → α → ℝ
  /-- The divergence `divergence a y θ` from the mean `y` to the arm `a` of the model `θ`. -/
  divergence : α → ℝ → Θ → ℝ
  /-- The allocation player of each answer: its weights at round `t`, given the gains of the
  rounds before `t`. -/
  alloc : ℐ → (t : ℕ) → (Fin t → α → ℝ) → α → ℝ
  /-- The alternative player of each answer: its distribution on the models at round `t`, given
  the losses of the rounds up to and including `t`. -/
  alt : ℐ → (t : ℕ) → (Fin (t + 1) → Θ → ℝ) → StdSimplex ℝ Θ

namespace GameSamplingRule

variable {α Θ ℐ 𝓨 : Type*} (G : GameSamplingRule α Θ ℐ 𝓨)

/-! ### Losses and optimistic gains -/

section Gain

/-- The optimistic gains of the arms after `n` rounds with history `h`, against the distribution
`q` on the models: the gain of the arm `a` is the largest of its exploration bonus and of the
expected divergences `E_{θ ∼ q} divergence a ξ θ` at the two ends `ξ` of its confidence interval. -/
noncomputable def optimisticGain (n : ℕ) (h : Hist Unit α 𝓨 n) (q : StdSimplex ℝ Θ) (a : α) : ℝ :=
  max (G.bonus n h a) (max (q.weights.sum fun θ r ↦ r * G.divergence a (G.lower n h a) θ)
    (q.weights.sum fun θ r ↦ r * G.divergence a (G.upper n h a) θ))

lemma optimisticGain_def (n : ℕ) (h : Hist Unit α 𝓨 n) (q : StdSimplex ℝ Θ) (a : α) :
    G.optimisticGain n h q a = max (G.bonus n h a)
      (max (q.weights.sum fun θ r ↦ r * G.divergence a (G.lower n h a) θ)
        (q.weights.sum fun θ r ↦ r * G.divergence a (G.upper n h a) θ)) := (rfl)

/-- The optimistic gain of an arm is at least its exploration bonus. -/
lemma bonus_le_optimisticGain (n : ℕ) (h : Hist Unit α 𝓨 n) (q : StdSimplex ℝ Θ) (a : α) :
    G.bonus n h a ≤ G.optimisticGain n h q a :=
  le_max_left _ _

/-- **Optimism of the gains.** If the divergences `divergence a · θ` of the models in the support of
`q` are convex on the confidence interval of the arm `a`, then the optimistic gain of `a` is at
least the expected divergence `E_{θ ∼ q} divergence a ξ θ` at every mean `ξ` of the confidence
interval. -/
lemma sum_mul_divergence_le_optimisticGain {n : ℕ} {h : Hist Unit α 𝓨 n} {q : StdSimplex ℝ Θ}
    {a : α}
    (hconv : ∀ θ ∈ q.weights.support,
      ConvexOn ℝ (Set.Icc (G.lower n h a) (G.upper n h a)) (G.divergence a · θ))
    {ξ : ℝ} (hξ : ξ ∈ Set.Icc (G.lower n h a) (G.upper n h a)) :
    (q.weights.sum fun θ r ↦ r * G.divergence a ξ θ) ≤ G.optimisticGain n h q a := by
  have hlu : G.lower n h a ≤ G.upper n h a := hξ.1.trans hξ.2
  -- the expected divergence is convex in the mean, as a combination with nonnegative weights
  have hconv' : ConvexOn ℝ (Set.Icc (G.lower n h a) (G.upper n h a))
      fun ξ ↦ q.weights.sum fun θ r ↦ r * G.divergence a ξ θ := by
    have h := StrongConvexOn.fun_sum (m := fun _ ↦ 0)
      (f := fun θ ξ ↦ q.weights θ • G.divergence a ξ θ) (convex_Icc _ _) fun θ hθ ↦
        strongConvexOn_zero.2 ((hconv θ hθ).smul (StdSimplex.weights_nonneg (w := q) θ))
    rw [Finset.sum_const_zero, strongConvexOn_zero] at h
    simpa only [Finsupp.sum, smul_eq_mul] using h
  refine le_max_of_le_right ?_
  exact hconv'.le_max_of_mem_Icc (Set.left_mem_Icc.2 hlu) (Set.right_mem_Icc.2 hlu) hξ

variable [Fintype α]

/-- The loss of the alternative player after `n` rounds with history `h`, for the weights `w` of
the allocation player: the model `θ` costs `∑ a, w a * divergence a (est a) θ`. -/
noncomputable def loss (n : ℕ) (h : Hist Unit α 𝓨 n) (w : α → ℝ) (θ : Θ) : ℝ :=
  ∑ a, w a * G.divergence a (G.est n h a) θ

lemma loss_def (n : ℕ) (h : Hist Unit α 𝓨 n) (w : α → ℝ) (θ : Θ) :
    G.loss n h w θ = ∑ a, w a * G.divergence a (G.est n h a) θ := (rfl)

end Gain

section Evidence

variable [Fintype α] [DecidableEq α]

/-- The evidence of the GLRT of the meta-algorithm after `n` rounds with history `h` against the
model `θ`: `∑ a, N_a d_a(x_a, θ)`, with `N_a` the number of pulls of the arm `a` and `x_a` its
estimated mean. -/
noncomputable def evidence (n : ℕ) (h : Hist Unit α 𝓨 n) (θ : Θ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ a, (pullCount' n h a : ℝ) * G.divergence a (G.est n h a) θ)

lemma evidence_def (n : ℕ) (h : Hist Unit α 𝓨 n) (θ : Θ) :
    G.evidence n h θ =
      ENNReal.ofReal (∑ a, (pullCount' n h a : ℝ) * G.divergence a (G.est n h a) θ) := (rfl)

end Evidence

/-! ### The plays of the learners -/

variable [Fintype α] [DecidableEq ℐ]

/-- The gains and losses of round `n`, with history `h` of the first `n` rounds, given the gains and
losses `F` of these rounds: the learners of the candidate answer `j` play from their gains and
losses in `F`, and they get the optimistic gains and the loss of round `n`, the learners of the
other answers get zero. -/
noncomputable def roundFeedback (n : ℕ) (h : Hist Unit α 𝓨 n)
    (F : Fin n → (ℐ → α → ℝ) × (ℐ → Θ → ℝ)) : (ℐ → α → ℝ) × (ℐ → Θ → ℝ) :=
  (Pi.single (G.cand n h) (G.optimisticGain n h (G.alt (G.cand n h) n
      (Fin.snoc (fun i ↦ (F i).2 (G.cand n h))
        (G.loss n h (G.alloc (G.cand n h) n fun i ↦ (F i).1 (G.cand n h)))))),
    Pi.single (G.cand n h) (G.loss n h (G.alloc (G.cand n h) n fun i ↦ (F i).1 (G.cand n h))))

/-- The gains and losses fed to the learners of every answer at the rounds of the history `h` of
the first `n` rounds, computed round by round with `roundFeedback`. -/
noncomputable def feedback : (n : ℕ) → Hist Unit α 𝓨 n → Fin n → (ℐ → α → ℝ) × (ℐ → Θ → ℝ)
  | 0, _ => Fin.elim0
  | n + 1, h => Fin.snoc (feedback n (Fin.init h)) (G.roundFeedback n (Fin.init h)
      (feedback n (Fin.init h)))

lemma feedback_succ (n : ℕ) (h : Hist Unit α 𝓨 (n + 1)) :
    G.feedback (n + 1) h = Fin.snoc (G.feedback n (Fin.init h))
      (G.roundFeedback n (Fin.init h) (G.feedback n (Fin.init h))) := by
  rw [feedback]

/-- The weights played by the allocation player of the candidate answer after `n` rounds with
history `h`. -/
noncomputable def weights (n : ℕ) (h : Hist Unit α 𝓨 n) : α → ℝ :=
  G.alloc (G.cand n h) n fun i ↦ (G.feedback n h i).1 (G.cand n h)

lemma weights_def (n : ℕ) (h : Hist Unit α 𝓨 n) :
    G.weights n h = G.alloc (G.cand n h) n fun i ↦ (G.feedback n h i).1 (G.cand n h) := (rfl)

/-- If the allocation players play allocations, so do the weights of the candidate answer. -/
lemma weights_mem_simplex (halloc : ∀ j t g, G.alloc j t g ∈ simplex α) (n : ℕ)
    (h : Hist Unit α 𝓨 n) : G.weights n h ∈ simplex α := by
  rw [weights_def]
  exact halloc _ _ _

/-- The distribution on the models played by the alternative player of the candidate answer after
`n` rounds with history `h`, which also sees the loss of the current weights. -/
noncomputable def altDist (n : ℕ) (h : Hist Unit α 𝓨 n) : StdSimplex ℝ Θ :=
  G.alt (G.cand n h) n
    (Fin.snoc (fun i ↦ (G.feedback n h i).2 (G.cand n h)) (G.loss n h (G.weights n h)))

lemma altDist_def (n : ℕ) (h : Hist Unit α 𝓨 n) :
    G.altDist n h = G.alt (G.cand n h) n
      (Fin.snoc (fun i ↦ (G.feedback n h i).2 (G.cand n h)) (G.loss n h (G.weights n h))) := (rfl)

/-- The optimistic gains of the arms after `n` rounds with history `h`, against the distribution
played by the alternative player. -/
noncomputable def gains (n : ℕ) (h : Hist Unit α 𝓨 n) : α → ℝ :=
  G.optimisticGain n h (G.altDist n h)

lemma gains_def (n : ℕ) (h : Hist Unit α 𝓨 n) :
    G.gains n h = G.optimisticGain n h (G.altDist n h) := (rfl)

/-- The gains and losses of round `n` are the optimistic gains and the loss of the weights, fed to
the learners of the candidate answer. -/
lemma roundFeedback_feedback (n : ℕ) (h : Hist Unit α 𝓨 n) :
    G.roundFeedback n h (G.feedback n h) =
      (Pi.single (G.cand n h) (G.gains n h), Pi.single (G.cand n h) (G.loss n h (G.weights n h))) :=
  (rfl)

/-! ### Along a trajectory -/

section Trajectory

variable {Ω : Type*} (O : ℕ → Ω → Unit) (A : ℕ → Ω → α) (Y : ℕ → Ω → 𝓨) (ω : Ω)

/-- Along a trajectory, the gains fed to the learners of the answer `j` at round `s`: the optimistic
gains of round `s` if its candidate answer is `j`, and zero otherwise. -/
noncomputable def gainSeq (j : ℐ) (s : ℕ) : α → ℝ :=
  if G.cand s (history O A Y s ω) = j then G.gains s (history O A Y s ω) else 0

/-- Along a trajectory, the losses fed to the learners of the answer `j` at round `s`: the loss of
the weights of round `s` if its candidate answer is `j`, and zero otherwise. -/
noncomputable def lossSeq (j : ℐ) (s : ℕ) : Θ → ℝ :=
  if G.cand s (history O A Y s ω) = j then
    G.loss s (history O A Y s ω) (G.weights s (history O A Y s ω)) else 0

lemma gainSeq_def (j : ℐ) (s : ℕ) :
    G.gainSeq O A Y ω j s =
      if G.cand s (history O A Y s ω) = j then G.gains s (history O A Y s ω) else 0 := (rfl)

lemma lossSeq_def (j : ℐ) (s : ℕ) :
    G.lossSeq O A Y ω j s = if G.cand s (history O A Y s ω) = j then
      G.loss s (history O A Y s ω) (G.weights s (history O A Y s ω)) else 0 := (rfl)

variable {O A Y ω} {j : ℐ} {s : ℕ}

@[simp]
lemma gainSeq_of_cand_eq (hs : G.cand s (history O A Y s ω) = j) :
    G.gainSeq O A Y ω j s = G.gains s (history O A Y s ω) := by
  simp [gainSeq_def, hs]

@[simp]
lemma gainSeq_of_cand_ne (hs : G.cand s (history O A Y s ω) ≠ j) : G.gainSeq O A Y ω j s = 0 := by
  simp [gainSeq_def, hs]

@[simp]
lemma lossSeq_of_cand_eq (hs : G.cand s (history O A Y s ω) = j) :
    G.lossSeq O A Y ω j s = G.loss s (history O A Y s ω) (G.weights s (history O A Y s ω)) := by
  simp [lossSeq_def, hs]

@[simp]
lemma lossSeq_of_cand_ne (hs : G.cand s (history O A Y s ω) ≠ j) : G.lossSeq O A Y ω j s = 0 := by
  simp [lossSeq_def, hs]

variable (O A Y ω)

/-- Along a trajectory, the gains and losses fed to the learners at round `i` of the history of
the first `n` rounds do not depend on `n`: they are the gains `gainSeq` and the losses `lossSeq` of
round `i`. -/
lemma feedback_history (n : ℕ) (i : Fin n) :
    G.feedback n (history O A Y n ω) i =
      (fun j ↦ G.gainSeq O A Y ω j i, fun j ↦ G.lossSeq O A Y ω j i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [feedback_succ, init_history]
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last, roundFeedback_feedback, Fin.val_last]
      ext j <;> simp [gainSeq_def, lossSeq_def, Pi.single_apply, eq_comm]
    | cast i => rw [Fin.snoc_castSucc, ih, Fin.val_castSucc]

/-- Along a trajectory, the allocation player of the candidate answer `j` plays from the gains
`gainSeq` of `j` of the previous rounds. -/
lemma weights_history (n : ℕ) :
    G.weights n (history O A Y n ω) = G.alloc (G.cand n (history O A Y n ω)) n
      fun i ↦ G.gainSeq O A Y ω (G.cand n (history O A Y n ω)) i := by
  simp_rw [weights_def, feedback_history]

/-- Along a trajectory, the alternative player of the candidate answer `j` plays from the losses
`lossSeq` of `j` of the rounds up to and including the current one. -/
lemma altDist_history (n : ℕ) :
    G.altDist n (history O A Y n ω) = G.alt (G.cand n (history O A Y n ω)) n
      fun i ↦ G.lossSeq O A Y ω (G.cand n (history O A Y n ω)) i := by
  rw [altDist_def]
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => rw [Fin.snoc_last, Fin.val_last, lossSeq_of_cand_eq _ rfl]
  | cast i => rw [Fin.snoc_castSucc, feedback_history, Fin.val_castSucc]

/-- Along a trajectory, the cumulative gains fed to the learners of `j` are the cumulative
optimistic gains of the rounds whose candidate answer is `j`. -/
lemma sum_gainSeq_apply (t : ℕ) (j : ℐ) (a : α) :
    ∑ s ∈ range t, G.gainSeq O A Y ω j s a =
      ∑ s ∈ range t with G.cand s (history O A Y s ω) = j, G.gains s (history O A Y s ω) a := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  by_cases hs : G.cand s (history O A Y s ω) = j <;> simp [hs]

/-- Along a trajectory, the cumulative losses fed to the learners of `j` are the cumulative losses
of the weights of the rounds whose candidate answer is `j`. -/
lemma sum_lossSeq_apply (t : ℕ) (j : ℐ) (θ : Θ) :
    ∑ s ∈ range t, G.lossSeq O A Y ω j s θ =
      ∑ s ∈ range t with G.cand s (history O A Y s ω) = j,
        G.loss s (history O A Y s ω) (G.weights s (history O A Y s ω)) θ := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  by_cases hs : G.cand s (history O A Y s ω) = j <;> simp [hs]

/-- Along a trajectory, the cumulative gain of the allocation player of `j` on the gains fed to it
is the cumulative gain of the weights on the rounds whose candidate answer is `j`. -/
lemma sum_sum_alloc_mul_gainSeq (t : ℕ) (j : ℐ) :
    ∑ s ∈ range t,
        ∑ b, G.alloc j s (fun i ↦ G.gainSeq O A Y ω j i) b * G.gainSeq O A Y ω j s b =
      ∑ s ∈ range t with G.cand s (history O A Y s ω) = j,
        ∑ b, G.weights s (history O A Y s ω) b * G.gains s (history O A Y s ω) b := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  by_cases hs : G.cand s (history O A Y s ω) = j
  · rw [G.weights_history, hs]
    simp [hs]
  · simp [hs]

/-- Along a trajectory, the cumulative expected loss of the alternative player of `j` on the
losses fed to it is the cumulative expected loss of `altDist` on the rounds whose candidate answer
is `j`. -/
lemma sum_alt_weights_sum_mul_lossSeq (t : ℕ) (j : ℐ) :
    ∑ s ∈ range t, ((G.alt j s fun i ↦ G.lossSeq O A Y ω j i).weights.sum fun θ' r ↦
        r * G.lossSeq O A Y ω j s θ') =
      ∑ s ∈ range t with G.cand s (history O A Y s ω) = j,
        ((G.altDist s (history O A Y s ω)).weights.sum fun θ' r ↦
          r * G.loss s (history O A Y s ω) (G.weights s (history O A Y s ω)) θ') := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  by_cases hs : G.cand s (history O A Y s ω) = j
  · rw [G.altDist_history, hs]
    simp [hs]
  · simp [hs]

/-- **The meta-algorithm is an approximate optimistic saddle point algorithm**
[DKM19, Definition 2, Appendix D.2]. Along a trajectory, let the allocation player of the answer
`j` have regret at most `Rk` after `t` rounds on the gains `gainSeq` fed to it, and its alternative
player have regret at most `Rl` against the model `θ` on the losses `lossSeq`. If the weights are
nonnegative and the optimistic gains of the rounds of `j` exceed the expected divergences
`E_{θ' ∼ q_s} divergence a (x_{s,a}) θ'` at the estimates by at most `C s a`, then on the rounds
`s < t` whose candidate answer is `j`,
`∑ U_s a ≤ ∑ ∑ b, w_s b divergence b (x_{s,b}) θ + (Rk + Rl + ∑ ∑ b, w_s b C s b)` for every
arm `a`.

This is the saddle-point inequality `sum_le_sum_sum_mul_add_of_regret` on the rounds of `j`, and
the hypothesis of `IdentTask.card_mul_answerValue_le_iInf_add` and
`IdentTask.mul_card_filter_notMem_correct_le` on these rounds. -/
theorem sum_gains_le_sum_sum_mul_add_of_regret {t : ℕ} (j : ℐ) {θ : Θ} {C : ℕ → α → ℝ}
    {Rk Rl : ℝ}
    (hw : ∀ s < t, G.cand s (history O A Y s ω) = j → ∀ a, 0 ≤ G.weights s (history O A Y s ω) a)
    (hUC : ∀ s < t, G.cand s (history O A Y s ω) = j → ∀ a, G.gains s (history O A Y s ω) a ≤
      ((G.altDist s (history O A Y s ω)).weights.sum fun θ' r ↦
        r * G.divergence a (G.est s (history O A Y s ω) a) θ') + C s a)
    (hRk : ∀ a, ∑ s ∈ range t, G.gainSeq O A Y ω j s a ≤ ∑ s ∈ range t,
      ∑ b, G.alloc j s (fun i ↦ G.gainSeq O A Y ω j i) b * G.gainSeq O A Y ω j s b + Rk)
    (hRl : ∑ s ∈ range t, ((G.alt j s fun i ↦ G.lossSeq O A Y ω j i).weights.sum fun θ' r ↦
      r * G.lossSeq O A Y ω j s θ') ≤ ∑ s ∈ range t, G.lossSeq O A Y ω j s θ + Rl) (a : α) :
    ∑ s ∈ range t with G.cand s (history O A Y s ω) = j, G.gains s (history O A Y s ω) a ≤
      ∑ s ∈ range t with G.cand s (history O A Y s ω) = j,
        ∑ b, G.weights s (history O A Y s ω) b *
          G.divergence b (G.est s (history O A Y s ω) b) θ +
      (Rk + Rl + ∑ s ∈ range t with G.cand s (history O A Y s ω) = j,
        ∑ b, G.weights s (history O A Y s ω) b * C s b) := by
  rw [sum_alt_weights_sum_mul_lossSeq, sum_lossSeq_apply] at hRl
  simp only [loss_def] at hRl
  refine sum_le_sum_sum_mul_add_of_regret (w := fun s ↦ G.weights s (history O A Y s ω))
    (U := fun s ↦ G.gains s (history O A Y s ω)) (q := fun s ↦ G.altDist s (history O A Y s ω))
    (ℓ := fun s b θ' ↦ G.divergence b (G.est s (history O A Y s ω) b) θ')
    (fun s hs ↦ hw s (mem_range.1 (mem_filter.1 hs).1) (mem_filter.1 hs).2)
    (fun s hs ↦ hUC s (mem_range.1 (mem_filter.1 hs).1) (mem_filter.1 hs).2) (fun a ↦ ?_) hRl a
  rw [← sum_gainSeq_apply, ← sum_sum_alloc_mul_gainSeq]
  exact hRk a

end Trajectory

end GameSamplingRule

namespace IdentTask

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [DecidableEq ℐ] {mℐ : MeasurableSpace ℐ} {m𝓨 : MeasurableSpace 𝓨}
  (task : IdentTask α Θ ℐ 𝓨) (G : GameSamplingRule α Θ ℐ 𝓨) (hw : ∀ n, Measurable (G.weights n))
  (β : (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞) (hcand : ∀ n, Measurable (G.cand n))
  (hstop : ∀ n, MeasurableSet {h | β n h < task.glr G.evidence n h (G.cand n h)})

/-- **The pure exploration meta-algorithm** [DKM19, Algorithm 1]: the GLRT of the candidate answer
with the evidence `∑ a, N_a d_a(x_a, λ)` and thresholds `β`, with the cumulative tracking of the
weights of the allocation player of the candidate answer as sampling rule. After `n` rounds with
history `h`, it stops if `β n h < inf_{λ ∈ ¬j} ∑ a, N_a d_a(x_a, λ)` for the candidate answer
`j = cand n h`, and then answers `j`. -/
noncomputable def gameExploration : IdentAlg Unit α 𝓨 ℐ :=
  task.glrt G.evidence (cumulativeTracking G.weights hw) β G.cand hcand hstop

lemma gameExploration_def : task.gameExploration G hw β hcand hstop =
    task.glrt G.evidence (cumulativeTracking G.weights hw) β G.cand hcand hstop := (rfl)

/-- The sampling rule of the meta-algorithm is the cumulative tracking of the weights. -/
@[simp]
lemma alg_gameExploration :
    (task.gameExploration G hw β hcand hstop).alg = cumulativeTracking G.weights hw := by
  rw [gameExploration_def, alg_glrt]

/-- The meta-algorithm stops after the history `h` of the first `n` rounds iff the GLR statistic of
the candidate answer exceeds the threshold `β n h`. -/
@[simp]
lemma mem_stopSet_gameExploration {h : Σ n, Hist Unit α 𝓨 n} :
    h ∈ (task.gameExploration G hw β hcand hstop).stopSet ↔
      β h.1 h.2 < task.glr G.evidence h.1 h.2 (G.cand h.1 h.2) := by
  rw [gameExploration_def, mem_stopSet_glrt]

/-- The meta-algorithm answers the candidate answer. -/
@[simp]
lemma output_gameExploration (h : Σ n, Hist Unit α 𝓨 n) :
    (task.gameExploration G hw β hcand hstop).output h = Measure.dirac (G.cand h.1 h.2) := by
  rw [gameExploration_def, output_glrt]

/-- **The meta-algorithm is `δ`-PAC** [DKM19, Theorem 1]: if on every admissible model `θ` the
evidence against `θ` exceeds the thresholds with probability at most `δ` and the meta-algorithm
stops almost surely, then it is `δ`-PAC on the task, whatever its learners. -/
theorem isDeltaPAC_gameExploration {δ : ℝ} (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (hdev : ∀ θ ∈ task.M, (trajMeasure (cumulativeTracking G.weights hw)
      (Environment.bandit (task.ν θ))).real
      {ω | ∃ n, β n (history IT.obs IT.action IT.feedback n ω) <
        G.evidence n (history IT.obs IT.action IT.feedback n ω) θ} ≤ δ)
    (h_stops : ∀ θ ∈ task.M,
      StopsAS (task.gameExploration G hw β hcand hstop) (Environment.bandit (task.ν θ))) :
    task.IsDeltaPAC (task.gameExploration G hw β hcand hstop) δ :=
  task.isDeltaPAC_glrt G.evidence _ β G.cand hcand hstop hc hdev h_stops

end IdentTask

namespace GameSamplingRule

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] [Nonempty α] [DecidableEq ℐ] (G : GameSamplingRule α Θ ℐ 𝓨)
  {Ω : Type*} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨} {ω : Ω}

/-- **AdaHedge against Best-Response is an approximate optimistic saddle point algorithm**
[DKM19, Lemma 3]. If the allocation player of the answer `j` is AdaHedge on gains and its
alternative player is Best-Response for a selection `br`, then along a trajectory, if the selected
models minimize the losses of the rounds of `j` against the model `θ` and the optimistic gains of
these rounds exceed the expected divergences at the estimates by at most `C s a`, then on the
rounds `s < t` whose candidate answer is `j`,
`∑ U_s a ≤ ∑ ∑ b, w_s b divergence b (x_{s,b}) θ + (2 Δ_t + ∑ ∑ b, w_s b C s b)` for every arm
`a`, with `Δ_t` the cumulative mixability gap of AdaHedge on the opposite of the gains of `j`. -/
theorem sum_gains_le_sum_sum_mul_add_of_adaHedge (j : ℐ)
    (halloc : G.alloc j = OnlineLearning.adaHedgeAlloc) {br : (Θ → ℝ) → Θ}
    (halt : G.alt j = OnlineLearning.bestResponse br) {t : ℕ} {θ : Θ} {C : ℕ → α → ℝ}
    (hbr : ∀ s < t, G.cand s (history O A Y s ω) = j →
      G.loss s (history O A Y s ω) (G.weights s (history O A Y s ω))
          (br (G.loss s (history O A Y s ω) (G.weights s (history O A Y s ω)))) ≤
        G.loss s (history O A Y s ω) (G.weights s (history O A Y s ω)) θ)
    (hUC : ∀ s < t, G.cand s (history O A Y s ω) = j → ∀ a, G.gains s (history O A Y s ω) a ≤
      ((G.altDist s (history O A Y s ω)).weights.sum fun θ' r ↦
        r * G.divergence a (G.est s (history O A Y s ω) a) θ') + C s a) (a : α) :
    ∑ s ∈ range t with G.cand s (history O A Y s ω) = j, G.gains s (history O A Y s ω) a ≤
      ∑ s ∈ range t with G.cand s (history O A Y s ω) = j,
        ∑ b, G.weights s (history O A Y s ω) b *
          G.divergence b (G.est s (history O A Y s ω) b) θ +
      (2 * OnlineLearning.adaHedgeGap (fun s ↦ -G.gainSeq O A Y ω j s) t +
        ∑ s ∈ range t with G.cand s (history O A Y s ω) = j,
          ∑ b, G.weights s (history O A Y s ω) b * C s b) := by
  have hw : ∀ s < t, G.cand s (history O A Y s ω) = j →
      ∀ a, 0 ≤ G.weights s (history O A Y s ω) a := fun s _ hs ↦ by
    rw [weights_history, hs, halloc]
    exact (mem_simplex_iff.1 (OnlineLearning.adaHedgeAlloc_mem_simplex _ _)).1
  have hRl : ∑ s ∈ range t, ((G.alt j s fun i ↦ G.lossSeq O A Y ω j i).weights.sum fun θ' r ↦
      r * G.lossSeq O A Y ω j s θ') ≤ ∑ s ∈ range t, G.lossSeq O A Y ω j s θ + 0 := by
    rw [halt, add_zero]
    refine OnlineLearning.sum_sum_bestResponse_le br _ fun s hs ↦ ?_
    by_cases hj : G.cand s (history O A Y s ω) = j
    · rw [lossSeq_of_cand_eq _ hj]
      exact hbr s hs hj
    · simp [lossSeq_of_cand_ne _ hj]
  have hRk : ∀ a, ∑ s ∈ range t, G.gainSeq O A Y ω j s a ≤ ∑ s ∈ range t,
      ∑ b, G.alloc j s (fun i ↦ G.gainSeq O A Y ω j i) b * G.gainSeq O A Y ω j s b +
        2 * OnlineLearning.adaHedgeGap (fun s ↦ -G.gainSeq O A Y ω j s) t := fun a ↦ by
    rw [halloc]
    exact OnlineLearning.sum_le_sum_sum_adaHedgeAlloc_mul_add _ t a
  have key := G.sum_gains_le_sum_sum_mul_add_of_regret O A Y ω j hw hUC hRk hRl a
  rwa [add_zero] at key

end GameSamplingRule

end LMLExplore.Identification
