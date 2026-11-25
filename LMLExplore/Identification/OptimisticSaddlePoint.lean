/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Geometry.Convex.ConvexSpace.Defs
public import LMLExplore.Identification.Task.Minimax

/-!
# The saddle-point analysis of sampling rules that solve the pure exploration game

The sampling rules of [DKM19] solve the pure exploration game online. At each round `s` they
compute a candidate answer `j`, and two learners attached to `j` play the game of `j`: an
allocation player plays proportions `w s` of the arms, an alternative player plays a finitely
supported distribution `q s` on the alternatives to `j`, and the arms are sampled by tracking the
allocations. The allocation player is fed *optimistic* gains `U s a`, upper confidence bounds on
the expected divergence `E_{λ ∼ q s}[d(μ_a, λ_a)]` from the unknown mean `μ_a`, and the alternative
player is fed the losses `λ ↦ ∑ a, w s a d(x_{s,a}, λ_a)` at the empirical means `x_s`. The
stopping rule is the generalized likelihood ratio test.

This file contains the deterministic part of the analysis of these rules [DKM19, Appendix D], for
one trajectory: every statement is about fixed sequences of plays, gains, counts and estimates,
and is meant to be applied along each trajectory of a run, on the concentration events. Round `s`
uses the statistics of the first `s` observations, which [DKM19] index by `s - 1`.

* **The saddle-point inequality** [DKM19, Appendix D.2]. If the allocation player has regret at
  most `Rk` on the gains `U` and the alternative player has regret at most `Rl` on its losses,
  then for every alternative `λ` and every arm `a`,
  `∑_{s ∈ S} U s a ≤ ∑_{s ∈ S} ∑ b, w s b d(x_{s,b}, λ_b) + Rk + Rl + ∑_{s ∈ S} ∑ b, w s b C s b`,
  where `C s a` bounds the optimism `U s a - E_{λ ∼ q s}[d(x_{s,a}, λ_a)]`. This is the property
  of an *approximate optimistic saddle point algorithm* of [DKM19, Definition 2]; the slack
  `C s a` is bounded by [DKM19, Lemma 15].
* **Rounds of the correct answer** [DKM19, Appendix D.6]. When the gains are optimistic at the
  rounds `s ∈ S'`, weak duality for the distributions `q s`
  (`IdentTask.card_mul_answerValue_le_iSup_sum_sum_klDiv`) turns the saddle-point inequality into
  `#S' · D(μ, ¬j) ≤ ∑_{s ∈ S} ∑ b, w s b d(x_{s,b}, λ_b) + slack`. Tracking and the Lipschitz
  continuity of the divergences in the mean [DKM19, Lemmas 14 and 17] then bound the right-hand
  side by the statistic `∑ a, N_a d(x_a, λ_a)` of the generalized likelihood ratio at the current
  round, so that the generalized likelihood ratio of `j` grows at rate `D(μ, ¬j)` on the rounds
  whose candidate is `j`.
* **Rounds of a wrong answer** [DKM19, Appendix D.5]. When the candidate answer `j` is wrong, the
  true model `μ` is an alternative to `j`, so the saddle-point inequality at `λ = μ` bounds the
  optimistic gains by divergences from `μ`, which concentration makes small. Since the optimistic
  gains are at least the exploration bonus `g s / N_{s,a}` and, by a separation assumption on the
  model, a wrong candidate always has an arm with a bonus at least `ε` [DKM19, Lemma 18], the
  gains of that arm grow linearly with the number of rounds of `j`. This bounds the number of
  rounds whose candidate answer is wrong.

## Main statements

* `LMLExplore.Identification.sum_le_sum_sum_mul_add_of_regret`: the saddle-point inequality.
* `LMLExplore.Identification.sub_sum_weights_mul_le_max`: the optimism slack is at most
  `max c (L ρ)` [DKM19, Lemma 15].
* `LMLExplore.Identification.sum_sum_mul_le_sum_mul_add`: the transfer from the rounds to the
  statistic of the current round [DKM19, Lemmas 14 and 17].
* `LMLExplore.Identification.IdentTask.card_mul_answerValue_le_ofReal`: optimism and weak duality.
* `LMLExplore.Identification.IdentTask.card_mul_answerValue_le_iInf_add`: the rounds of the
  correct answer [DKM19, Appendix D.6].
* `LMLExplore.Identification.IdentTask.exists_le_two_mul_div_of_mem_alt`: a wrong candidate has an
  arm with a large exploration bonus [DKM19, Lemma 18].
* `LMLExplore.Identification.mul_card_le_sum_of_le_div`: the linear increase of the gains of an
  arm with a large bonus.
* `LMLExplore.Identification.IdentTask.mul_card_filter_notMem_correct_le`: the rounds of the wrong
  answers [DKM19, Appendix D.5].

## Implementation notes

The distribution `q s` of the alternative player is a finitely supported probability distribution,
`Convexity.StdSimplex ℝ Θ`, and expectations under it are written
`(q s).weights.sum fun λ r ↦ r * f λ`, as in `LMLExplore.Identification.Task.Minimax`. A
best-response alternative player plays a Dirac mass. The divergences `d a y λ` from a mean `y` to
the arm `a` of a model `λ` are real-valued functions, and the true divergences only enter through
the optimism hypothesis, stated with `klDiv`, so that the arm laws need not form an exponential
family.

## References

* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019 (arXiv:1906.10431).
-/

public section

open MeasureTheory InformationTheory Convexity Finset

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α Θ : Type*} [Fintype α] {mα : MeasurableSpace α}

/-! ### The saddle-point inequality -/

/-- **The saddle-point inequality** [DKM19, Appendix D.2]. On rounds `S`, let an allocation player
play nonnegative weights `w s` against the gains `U s`, with regret at most `Rk` against every arm,
and an alternative player play distributions `q s` against the losses
`λ ↦ ∑ b, w s b * ℓ s b λ`, with regret at most `Rl` against `λ`. If the gains exceed the
expected losses of the arms by at most `C s a`, then for every arm `a`,
`∑_{s ∈ S} U s a ≤ ∑_{s ∈ S} ∑ b, w s b ℓ s b λ + (Rk + Rl + ∑_{s ∈ S} ∑ b, w s b C s b)`.

Two learners with these regrets form an approximate optimistic saddle point algorithm in the sense
of [DKM19, Definition 2]. A best-response alternative player, playing a minimizer of its loss,
has `Rl = 0`. -/
theorem sum_le_sum_sum_mul_add_of_regret {S : Finset ℕ} {w U C : ℕ → α → ℝ}
    {q : ℕ → StdSimplex ℝ Θ} {ℓ : ℕ → α → Θ → ℝ} {Rk Rl : ℝ} {θ : Θ}
    (hw : ∀ s ∈ S, ∀ a, 0 ≤ w s a)
    (hUC : ∀ s ∈ S, ∀ a, U s a ≤ ((q s).weights.sum fun θ' r ↦ r * ℓ s a θ') + C s a)
    (hRk : ∀ a, ∑ s ∈ S, U s a ≤ ∑ s ∈ S, ∑ b, w s b * U s b + Rk)
    (hRl : ∑ s ∈ S, ((q s).weights.sum fun θ' r ↦ r * ∑ b, w s b * ℓ s b θ') ≤
      ∑ s ∈ S, ∑ b, w s b * ℓ s b θ + Rl) (a : α) :
    ∑ s ∈ S, U s a ≤
      ∑ s ∈ S, ∑ b, w s b * ℓ s b θ + (Rk + Rl + ∑ s ∈ S, ∑ b, w s b * C s b) := by
  have h : ∑ s ∈ S, ∑ b, w s b * U s b ≤
      ∑ s ∈ S, ((q s).weights.sum fun θ' r ↦ r * ∑ b, w s b * ℓ s b θ') +
        ∑ s ∈ S, ∑ b, w s b * C s b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun s hs ↦ ?_
    rw [← StdSimplex.sum_mul_weights_sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun b _ ↦ ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hUC s hs b) (hw s hs b)
  linarith [hRk a]

/-- **The optimism slack** [DKM19, Lemma 15]. Let a gain `u` be at most the maximum of a bonus `c`
and of the expected loss `E_{λ ∼ q}[ℓ ξ λ]` at a point `ξ` within `ρ` of `x`, for losses that are
nonnegative at `x` and `L`-Lipschitz on a set containing `x` and `ξ`. Then `u` exceeds the
expected loss at `x` by at most `max c (L ρ)`.

In [DKM19], `u` is the optimistic gain of an arm, `c` its exploration bonus, `x` its empirical
mean and `ξ` an endpoint of its confidence interval, of width `ρ` by the sub-Gaussian
assumption. -/
theorem sub_sum_weights_mul_le_max {q : StdSimplex ℝ Θ} {ℓ : ℝ → Θ → ℝ} {J : Set ℝ} {L : ℝ≥0}
    (hℓ : ∀ θ ∈ q.weights.support, LipschitzOnWith L (ℓ · θ) J) {x ξ : ℝ} (hx : x ∈ J)
    (hξ : ξ ∈ J) (hℓ0 : ∀ θ ∈ q.weights.support, 0 ≤ ℓ x θ) {u c ρ : ℝ}
    (hu : u ≤ max c (q.weights.sum fun θ r ↦ r * ℓ ξ θ)) (hρ : |ξ - x| ≤ ρ) :
    u - (q.weights.sum fun θ r ↦ r * ℓ x θ) ≤ max c (L * ρ) := by
  have h0 : 0 ≤ q.weights.sum fun θ r ↦ r * ℓ x θ :=
    Finsupp.sum_nonneg fun θ hθ ↦ mul_nonneg (q.nonneg θ) (hℓ0 θ hθ)
  rcases le_max_iff.1 hu with hu | hu
  · exact le_max_of_le_left (by linarith)
  · have h : (q.weights.sum fun θ r ↦ r * ℓ ξ θ) ≤
        (q.weights.sum fun θ r ↦ r * ℓ x θ) + L * ρ := by
      rw [← StdSimplex.weights_sum_mul_add_const]
      refine Finsupp.sum_le_sum fun θ hθ ↦ mul_le_mul_of_nonneg_left
        (((hℓ θ hθ).le_add_mul hξ hx).trans ?_) (q.nonneg θ)
      rw [Real.dist_eq]
      gcongr
    exact le_max_of_le_right (by linarith)

/-- **From the rounds to the current statistic** [DKM19, Lemmas 14 and 17]. Let the counts `N`
track the weights `w` played at the rounds before `n` up to `κ`, and let `g a` (the divergence to
the arm `a` of an alternative, as a function of the mean) be `L`-Lipschitz on a set `I`
containing the true means `m`, the current estimates `x` and the estimates `xs s` of the rounds
`s ∈ S`, nonnegative and at most `D` at the true means. If the estimates are within `r a`, resp.
`r' s a`, of the true means, then the weighted divergences at the estimates of the rounds `s ∈ S`
are bounded by the statistic `∑ a, N a g a (x a)` of the current round:
`∑_{s ∈ S} ∑ a, w s a g a (xs s a) ≤ ∑ a, N a g a (x a) + (L ∑ a, N a r a + κ K D +
L ∑_{s ∈ S} ∑ a, w s a r' s a)`. -/
theorem sum_sum_mul_le_sum_mul_add {n : ℕ} {S : Finset ℕ} (hS : S ⊆ range n) {w : ℕ → α → ℝ}
    (hw : ∀ s < n, ∀ a, 0 ≤ w s a) {N : α → ℝ} (hN : ∀ a, 0 ≤ N a) {κ : ℝ} (hκ : 0 ≤ κ)
    (htrack : ∀ a, ∑ s ∈ range n, w s a - κ ≤ N a) {g : α → ℝ → ℝ} {I : Set ℝ} {L : ℝ≥0}
    (hg : ∀ a, LipschitzOnWith L (g a) I) {m x : α → ℝ} {xs : ℕ → α → ℝ} {D : ℝ}
    (hg0 : ∀ a, 0 ≤ g a (m a)) (hgD : ∀ a, g a (m a) ≤ D) (hm : ∀ a, m a ∈ I) (hx : ∀ a, x a ∈ I)
    (hxs : ∀ s ∈ S, ∀ a, xs s a ∈ I) {r : α → ℝ} {r' : ℕ → α → ℝ} (hr : ∀ a, |x a - m a| ≤ r a)
    (hr' : ∀ s ∈ S, ∀ a, |xs s a - m a| ≤ r' s a) :
    ∑ s ∈ S, ∑ a, w s a * g a (xs s a) ≤ ∑ a, N a * g a (x a) +
      (L * ∑ a, N a * r a + κ * Fintype.card α * D + L * ∑ s ∈ S, ∑ a, w s a * r' s a) := by
  have hwS : ∀ s ∈ S, ∀ a, 0 ≤ w s a := fun s hs ↦ hw s (Finset.mem_range.1 (hS hs))
  -- Lemma 14: move the divergences of the rounds from the estimates to the true means.
  have h1 : ∑ s ∈ S, ∑ a, w s a * g a (xs s a) ≤
      ∑ s ∈ S, ∑ a, w s a * g a (m a) + L * ∑ s ∈ S, ∑ a, w s a * r' s a := by
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun s hs ↦ Finset.sum_le_sum fun a _ ↦ ?_
    have h := (hg a).le_add_mul (hxs s hs a) (hm a)
    rw [Real.dist_eq] at h
    have h' : g a (xs s a) ≤ g a (m a) + L * r' s a := h.trans (by gcongr; exact hr' s hs a)
    nlinarith [mul_le_mul_of_nonneg_left h' (hwS s hs a)]
  -- Drop the condition `s ∈ S` and use tracking: the rounds before `n` gave arm `a` the weight
  -- `∑ s < n, w s a ≤ N a + κ`.
  have h2 : ∑ s ∈ S, ∑ a, w s a * g a (m a) ≤ ∑ a, N a * g a (m a) + κ * Fintype.card α * D := by
    calc ∑ s ∈ S, ∑ a, w s a * g a (m a) ≤ ∑ s ∈ range n, ∑ a, w s a * g a (m a) :=
          Finset.sum_le_sum_of_subset_of_nonneg hS fun s hs _ ↦ Finset.sum_nonneg fun a _ ↦
            mul_nonneg (hw s (Finset.mem_range.1 hs) a) (hg0 a)
      _ = ∑ a, (∑ s ∈ range n, w s a) * g a (m a) := by
          rw [Finset.sum_comm]
          simp_rw [Finset.sum_mul]
      _ ≤ ∑ a, (N a + κ) * g a (m a) :=
          Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_right (by linarith [htrack a]) (hg0 a)
      _ ≤ ∑ a, (N a * g a (m a) + κ * D) :=
          Finset.sum_le_sum fun a _ ↦ by nlinarith [hgD a, hg0 a]
      _ = ∑ a, N a * g a (m a) + κ * Fintype.card α * D := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  -- Lemma 17: move the statistic from the true means to the current estimates.
  have h3 : ∑ a, N a * g a (m a) ≤ ∑ a, N a * g a (x a) + L * ∑ a, N a * r a := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ ↦ ?_
    have h := (hg a).le_add_mul (hm a) (hx a)
    rw [Real.dist_eq, abs_sub_comm] at h
    have h' : g a (m a) ≤ g a (x a) + L * r a := h.trans (by gcongr; exact hr a)
    nlinarith [mul_le_mul_of_nonneg_left h' (hN a)]
  linarith

namespace IdentTask

variable {ℐ 𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} (task : IdentTask α Θ ℐ 𝓨) {θ : Θ} {i : ℐ}

/-- **Optimism and weak duality** [DKM19, Appendix D.6]. If the alternative player plays
distributions on the alternatives to `i` at the rounds `s ∈ S'`, and the nonnegative gains `U s a`
of these rounds are upper bounds on the expected divergences `E_{λ ∼ q s}[KL(ν_a(θ), ν_a(λ))]`,
then any common upper bound `G` on the total gains `∑_{s ∈ S} U s a` of the arms, over rounds
`S ⊇ S'`, is at least `#S'` times the value `D(θ, ¬i)`. -/
theorem card_mul_answerValue_le_ofReal {S S' : Finset ℕ} (hS' : S' ⊆ S)
    {q : ℕ → StdSimplex ℝ Θ} {U : ℕ → α → ℝ} {G : ℝ}
    (hq : ∀ s ∈ S', ↑(q s).weights.support ⊆ task.alt i) (hU0 : ∀ s ∈ S, ∀ a, 0 ≤ U s a)
    (hopt : ∀ s ∈ S', ∀ a, ((q s).weights.sum fun θ' r ↦
      ENNReal.ofReal r * klDiv (task.ν θ a) (task.ν θ' a)) ≤ ENNReal.ofReal (U s a))
    (hG : ∀ a, ∑ s ∈ S, U s a ≤ G) :
    (#S' : ℝ≥0∞) * task.answerValue θ i ≤ ENNReal.ofReal G := by
  refine (task.card_mul_answerValue_le_iSup_sum_sum_klDiv hq).trans (iSup_le fun a ↦ ?_)
  calc ∑ s ∈ S', ((q s).weights.sum fun θ' r ↦
        ENNReal.ofReal r * klDiv (task.ν θ a) (task.ν θ' a))
      ≤ ∑ s ∈ S', ENNReal.ofReal (U s a) := Finset.sum_le_sum fun s hs ↦ hopt s hs a
    _ = ENNReal.ofReal (∑ s ∈ S', U s a) :=
        (ENNReal.ofReal_sum_of_nonneg fun s hs ↦ hU0 s (hS' hs) a).symm
    _ ≤ ENNReal.ofReal G := ENNReal.ofReal_le_ofReal <|
        (Finset.sum_le_sum_of_subset_of_nonneg hS' fun s hs _ ↦ hU0 s hs a).trans (hG a)

/-- **The rounds of the correct answer** [DKM19, Appendix D.6]. Let the rounds `S` before `n` be
those of the learners of the answer `i`, with the saddle-point inequality of slack `y`
(`LMLExplore.Identification.sum_le_sum_sum_mul_add_of_regret`) against every alternative to `i`
for the losses `d b (xs s b) λ` at the estimates `xs s`, and let the gains be optimistic at the
rounds of `S' ⊆ S` (where the true model `θ` is in the confidence region). Let the counts `N`
track the weights up to `κ`, and the divergences `d a · λ` be `L`-Lipschitz on a set containing
the true means `m` and the estimates, nonnegative and at most `D` at the true means. If the
current estimates `x` and the estimates `xs s` are within `r a` and `r' s a` of the true means,
the statistic of the generalized likelihood ratio of `i` at the current round grows at rate
`D(θ, ¬i)` on the rounds of `S'`:
`#S' · D(θ, ¬i) ≤ inf_{λ ∈ ¬i} ∑ a, N a d a (x a) λ + (L ∑ a, N a r a + κ K D +
L ∑_{s ∈ S} ∑ a, w s a r' s a + y)`. -/
theorem card_mul_answerValue_le_iInf_add {n : ℕ} {S S' : Finset ℕ} (hS : S ⊆ range n)
    (hS' : S' ⊆ S) {w : ℕ → α → ℝ} (hw : ∀ s < n, ∀ a, 0 ≤ w s a) {N : α → ℝ}
    (hN : ∀ a, 0 ≤ N a) {κ : ℝ} (hκ : 0 ≤ κ) (htrack : ∀ a, ∑ s ∈ range n, w s a - κ ≤ N a)
    {d : α → ℝ → Θ → ℝ} {I : Set ℝ} {L : ℝ≥0}
    (hd : ∀ θ' ∈ task.alt i, ∀ a, LipschitzOnWith L (d a · θ') I) {m x : α → ℝ}
    {xs : ℕ → α → ℝ} {D : ℝ} (hd0 : ∀ θ' ∈ task.alt i, ∀ a, 0 ≤ d a (m a) θ')
    (hdD : ∀ θ' ∈ task.alt i, ∀ a, d a (m a) θ' ≤ D) (hm : ∀ a, m a ∈ I) (hx : ∀ a, x a ∈ I)
    (hxs : ∀ s ∈ S, ∀ a, xs s a ∈ I) {r : α → ℝ} {r' : ℕ → α → ℝ} (hr : ∀ a, |x a - m a| ≤ r a)
    (hr' : ∀ s ∈ S, ∀ a, |xs s a - m a| ≤ r' s a) {q : ℕ → StdSimplex ℝ Θ} {U : ℕ → α → ℝ}
    {y : ℝ} (hq : ∀ s ∈ S', ↑(q s).weights.support ⊆ task.alt i)
    (hU0 : ∀ s ∈ S, ∀ a, 0 ≤ U s a)
    (hopt : ∀ s ∈ S', ∀ a, ((q s).weights.sum fun θ' r ↦
      ENNReal.ofReal r * klDiv (task.ν θ a) (task.ν θ' a)) ≤ ENNReal.ofReal (U s a))
    (hsaddle : ∀ θ' ∈ task.alt i, ∀ a,
      ∑ s ∈ S, U s a ≤ ∑ s ∈ S, ∑ b, w s b * d b (xs s b) θ' + y) :
    (#S' : ℝ≥0∞) * task.answerValue θ i ≤
      (⨅ θ' ∈ task.alt i, ENNReal.ofReal (∑ a, N a * d a (x a) θ')) +
        ENNReal.ofReal (L * ∑ a, N a * r a + κ * Fintype.card α * D +
          L * ∑ s ∈ S, ∑ a, w s a * r' s a + y) := by
  rw [ENNReal.iInf_add]
  refine le_iInf fun θ' ↦ ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hθ' ↦ ?_
  refine (task.card_mul_answerValue_le_ofReal hS' hq hU0 hopt fun a ↦ ?_).trans
    ENNReal.ofReal_add_le
  have := sum_sum_mul_le_sum_mul_add hS hw hN hκ htrack (hd θ' hθ') (hd0 θ' hθ') (hdD θ' hθ') hm
    hx hxs hr hr'
  linarith [hsaddle θ' hθ' a]

omit [Fintype α] in
/-- **A wrong candidate has an arm with a large exploration bonus** [DKM19, Lemma 18]. Let every
alternative `λ` to `i` be separated from `μ` on some arm `a`, in the sense that
`ε ≤ d a y λ + d a y μ` for every mean `y` (for divergences of exponential families, that the
Chernoff information between the arms `a` of `λ` and `μ` is at least `ε`). If an alternative `μ'`
to `i` (the model of a wrong candidate answer) and the true model `μ` are both in the confidence
region `{λ | ∀ a, N a d a (x a) λ ≤ f}` around the estimates `x`, then some arm has
`ε ≤ 2 f / N a`. -/
theorem exists_le_two_mul_div_of_mem_alt {d : α → ℝ → Θ → ℝ} {μ μ' : Θ} {ε : ℝ}
    (hsep : ∀ θ' ∈ task.alt i, ∃ a, ∀ y, ε ≤ d a y θ' + d a y μ) (hμ' : μ' ∈ task.alt i)
    {N x : α → ℝ} (hN : ∀ a, 0 < N a) {f : ℝ} (hμ'f : ∀ a, N a * d a (x a) μ' ≤ f)
    (hμf : ∀ a, N a * d a (x a) μ ≤ f) :
    ∃ a, ε ≤ 2 * (f / N a) := by
  obtain ⟨a, ha⟩ := hsep μ' hμ'
  refine ⟨a, (ha (x a)).trans ?_⟩
  rw [two_mul]
  exact add_le_add ((le_div_iff₀ (hN a)).2 (by rw [mul_comm]; exact hμ'f a))
    ((le_div_iff₀ (hN a)).2 (by rw [mul_comm]; exact hμf a))

end IdentTask

/-- **Linear increase of the optimistic gains** [DKM19, Appendix D.5]. Let the gains `U s` of the
rounds `s ∈ S` be at least the exploration bonus `g s / N s` of an arm with positive counts
`N s ≤ N t`, where `c g t ≤ g s` for nonnegative `g`, and let the bonus at the round `t` be at
least `ε`. Then the gains of the rounds of `S` add up to at least `c ε #S`. -/
theorem mul_card_le_sum_of_le_div {S : Finset ℕ} {g N U : ℕ → ℝ} {t : ℕ} {c ε : ℝ} (hc : 0 ≤ c)
    (hg : ∀ s ∈ S, 0 ≤ g s) (hcg : ∀ s ∈ S, c * g t ≤ g s) (hN : ∀ s ∈ S, 0 < N s)
    (hNt : ∀ s ∈ S, N s ≤ N t) (hU : ∀ s ∈ S, g s / N s ≤ U s) (hε : ε ≤ g t / N t) :
    c * ε * #S ≤ ∑ s ∈ S, U s := by
  rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun s hs ↦ ?_
  calc c * ε ≤ c * g t / N t := by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hε hc
    _ ≤ g s / N t := div_le_div_of_nonneg_right (hcg s hs) ((hN s hs).le.trans (hNt s hs))
    _ ≤ g s / N s := div_le_div_of_nonneg_left (hg s hs) (hN s hs) (hNt s hs)
    _ ≤ U s := hU s hs

namespace IdentTask

variable {ℐ 𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} (task : IdentTask α Θ ℐ 𝓨)

/-- **The rounds of the wrong answers** [DKM19, Appendix D.5]. Let the learners of each answer `j`
satisfy the saddle-point inequality of slack `y j` on the rounds of `R` whose candidate answer is
`j`, against every alternative to `j`, for the losses `d b (xs s b) λ` at the estimates `xs s`,
and let the losses at the true model `μ ∈ M` be at most `e s b ≥ 0` on `R`. On the later rounds
`R' ⊆ R`, let the nonnegative gains be at least the exploration bonuses `g s / N s a` (with
positive counts, monotone in the round, nonnegative `g` and `c g t ≤ g s`), and at every round of
`R'` whose candidate is not a correct answer of `μ`, let some arm have a bonus at least `ε` (for
instance by `LMLExplore.Identification.IdentTask.exists_le_two_mul_div_of_mem_alt`). Then
`c ε` times the number of rounds of `R'` with a wrong candidate is at most the slacks of the
wrong answers plus `∑_s ∑ b, w s b e s b` over the rounds of `R` with a wrong candidate.

For a wrong answer `j`, the true model `μ` is an alternative to `j`, so that the gains of the
rounds of `j` are bounded by the losses at `μ`, while the gains of the arm with a large bonus at
the last round of `j` grow linearly with the number of rounds of `j`. -/
theorem mul_card_filter_notMem_correct_le {μ : Θ} (hμ : μ ∈ task.M) {R R' : Finset ℕ}
    (hR' : R' ⊆ R) {cand : ℕ → ℐ} [DecidablePred (· ∈ task.correct μ)] [DecidableEq ℐ]
    {w U : ℕ → α → ℝ} {d : α → ℝ → Θ → ℝ} {xs : ℕ → α → ℝ} {y : ℐ → ℝ}
    (hsaddle : ∀ j, ∀ θ' ∈ task.alt j, ∀ a, ∑ s ∈ R with cand s = j, U s a ≤
      ∑ s ∈ R with cand s = j, ∑ b, w s b * d b (xs s b) θ' + y j)
    (hw : ∀ s ∈ R, ∀ a, 0 ≤ w s a) {e : ℕ → α → ℝ} (he : ∀ s ∈ R, ∀ b, d b (xs s b) μ ≤ e s b)
    (he0 : ∀ s ∈ R, ∀ b, 0 ≤ e s b) (hU0 : ∀ s ∈ R, ∀ a, 0 ≤ U s a) {g : ℕ → ℝ}
    {N : ℕ → α → ℝ} {c ε : ℝ} (hc : 0 ≤ c) (hg : ∀ s ∈ R', 0 ≤ g s)
    (hcg : ∀ s ∈ R', ∀ t ∈ R', c * g t ≤ g s) (hN : ∀ s ∈ R', ∀ a, 0 < N s a)
    (hNmono : ∀ s ∈ R', ∀ t ∈ R', s ≤ t → ∀ a, N s a ≤ N t a)
    (hU : ∀ s ∈ R', ∀ a, g s / N s a ≤ U s a)
    (hwit : ∀ s ∈ R', cand s ∉ task.correct μ → ∃ a, ε ≤ g s / N s a) :
    c * ε * #{s ∈ R' | cand s ∉ task.correct μ} ≤
      ∑ j ∈ {s ∈ R' | cand s ∉ task.correct μ}.image cand, y j +
        ∑ s ∈ R with cand s ∉ task.correct μ, ∑ b, w s b * e s b := by
  set W' := {s ∈ R' | cand s ∉ task.correct μ}
  set F : ℕ → ℝ := fun s ↦ ∑ b, w s b * e s b
  -- The rounds of `R'` with a wrong answer `j` are the rounds of `W'` with candidate `j`.
  have hfib : ∀ j ∉ task.correct μ, {s ∈ R' | cand s = j} = {s ∈ W' | cand s = j} := by
    intro j hj
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun s _ ↦ ⟨fun h ↦ ⟨h ▸ hj, h⟩, fun h ↦ h.2⟩
  have hj : ∀ j ∈ W'.image cand, c * ε * #{s ∈ W' | cand s = j} ≤
      y j + ∑ s ∈ R with cand s = j, F s := by
    intro j hjW
    obtain ⟨t₀, ht₀W, rfl⟩ := Finset.mem_image.1 hjW
    have hj : cand t₀ ∉ task.correct μ := (Finset.mem_filter.1 ht₀W).2
    rw [← hfib _ hj]
    set S' := {s ∈ R' | cand s = cand t₀}
    set S := {s ∈ R | cand s = cand t₀}
    have hS'R : S' ⊆ R' := Finset.filter_subset _ _
    have hSR : S ⊆ R := Finset.filter_subset _ _
    have hS'S : S' ⊆ S := Finset.filter_subset_filter _ hR'
    have hne : S'.Nonempty := ⟨t₀, Finset.mem_filter.2 ⟨(Finset.mem_filter.1 ht₀W).1, rfl⟩⟩
    -- The last round `t` of `S'` has an arm `a` with a bonus at least `ε`.
    set t := S'.max' hne
    have htS : t ∈ S' := S'.max'_mem hne
    have htR : t ∈ R' := hS'R htS
    have hct : cand t = cand t₀ := (Finset.mem_filter.1 htS).2
    obtain ⟨a, ha⟩ := hwit t htR (hct ▸ hj)
    have hlin := mul_card_le_sum_of_le_div (S := S') (N := (N · a)) (U := (U · a)) hc
      (fun s hs ↦ hg s (hS'R hs)) (fun s hs ↦ hcg s (hS'R hs) t htR)
      (fun s hs ↦ hN s (hS'R hs) a) (fun s hs ↦ hNmono s (hS'R hs) t htR (S'.le_max' s hs) a)
      (fun s hs ↦ hU s (hS'R hs) a) ha
    have hsub : ∑ s ∈ S', U s a ≤ ∑ s ∈ S, U s a :=
      Finset.sum_le_sum_of_subset_of_nonneg hS'S fun s hs _ ↦ hU0 s (hSR hs) a
    -- The true model is an alternative to the wrong answer, so the saddle-point inequality
    -- applies at `μ`.
    have hsad := hsaddle (cand t₀) μ (task.mem_alt_iff.2 ⟨hμ, hj⟩) a
    have hloss : ∑ s ∈ S, ∑ b, w s b * d b (xs s b) μ ≤ ∑ s ∈ S, F s :=
      Finset.sum_le_sum fun s hs ↦ Finset.sum_le_sum fun b _ ↦
        mul_le_mul_of_nonneg_left (he s (hSR hs) b) (hw s (hSR hs) b)
    linarith
  -- The rounds of `R` whose candidate is a wrong answer met in `R'` have a wrong candidate.
  have hfib' : ∑ j ∈ W'.image cand, ∑ s ∈ R with cand s = j, F s ≤
      ∑ s ∈ R with cand s ∉ task.correct μ, F s := by
    rw [Finset.sum_fiberwise_eq_sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun s hs ↦ ?_) fun s hs _ ↦
      Finset.sum_nonneg fun b _ ↦ mul_nonneg (hw s (Finset.mem_filter.1 hs).1 b)
        (he0 s (Finset.mem_filter.1 hs).1 b)
    obtain ⟨hsR, hsW⟩ := Finset.mem_filter.1 hs
    obtain ⟨t, htW, hts⟩ := Finset.mem_image.1 hsW
    exact Finset.mem_filter.2 ⟨hsR, hts ▸ (Finset.mem_filter.1 htW).2⟩
  have hmaps : ∀ s ∈ W', cand s ∈ W'.image cand := fun s hs ↦ Finset.mem_image_of_mem cand hs
  calc c * ε * #W' = ∑ j ∈ W'.image cand, c * ε * #{s ∈ W' | cand s = j} := by
        rw [← Finset.mul_sum, Finset.card_eq_sum_card_image cand W']
        push_cast
        rfl
    _ ≤ ∑ j ∈ W'.image cand, (y j + ∑ s ∈ R with cand s = j, F s) := Finset.sum_le_sum hj
    _ ≤ _ := by rw [Finset.sum_add_distrib]; exact add_le_add le_rfl hfib'

end IdentTask

end LMLExplore.Identification
