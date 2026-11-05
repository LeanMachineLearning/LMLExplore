/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.OnlineLearning.MirrorDescent
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Mirror descent and FTRL with bandit feedback

In an adversarial linear bandit on a real normed space `E`, an adversary chooses at round `t` a
loss `y t` in the dual `E →L[ℝ] ℝ` of `E`, possibly depending on the past actions of the learner
(an adaptive adversary). The learner plays a random action `A t` and only observes the loss
`y t (A t)`. Its expected regret against `u` after `n` rounds is `E[∑ t < n, y t (A t - u)]`.

Online stochastic mirror descent and follow the regularized leader [LS, Algorithm 16] reduce this
problem to online linear optimization with full information: they run mirror descent or FTRL on
estimates `Y t` of the losses, producing plays `a t`, and at round `t` sample the action `A t`
from a distribution with mean `a t`. If the estimates are unbiased, the expected regret is the
expected regret of the full-information algorithm on the estimated losses, so that the bounds of
`LMLExplore.OnlineLearning.MirrorDescent` and `LMLExplore.OnlineLearning.FTRL` transfer in
expectation [LS, Theorem 28.10].

The probabilistic conditions are stated round by round, relative to a σ-algebra `m t` describing
the information available before the action of round `t` is sampled (typically the past actions
and observations): the loss `y t` and the play `a t` are `m t`-measurable, the action has
conditional mean `a t` and the estimate `Y t` has conditional mean `y t`. Losses fixed in advance
by an oblivious adversary are the constant random losses. The full-information bounds are applied
on each sample path, so the plays may depend on the past estimates and the losses on the past
actions in an arbitrary way. [LS] assumes a Legendre potential and losses fixed in advance; the
statements here only use the hypotheses of the full-information bounds, the derivatives of the
potential at the plays and, for mirror descent, its convexity.

## Main definitions

* `IsUnbiasedRound m P y A a Y`: the action `A` has conditional mean `a` given `m` and the
  estimate `Y` of the random loss `y` has conditional mean `y` given `m`, with the integrability
  that this requires. The play `a` and the loss `y` are then `m`-measurable.

## Main statements

* `integral_sum_apply_sub_eq_integral_sum_apply_sub`: if every round is unbiased, the expected
  regret against `u` equals `E[∑ t < n, Y t (a t - u)]`, the expected regret of the plays on the
  estimated losses.
* `integral_sum_apply_sub_le_of_ae_le`: an almost sure bound on the regret of the plays on the
  estimated losses bounds the expected regret.
* `mirrorDescent_integral_regret_le`, `ftrl_integral_regret_le`: [LS, Theorem 28.10], first
  bound, for mirror descent and for FTRL.
* `mirrorDescent_integral_regret_le_sub_add_sum_bregDiv`: [LS, Theorem 28.10], second bound,
  through the unconstrained steps of mirror descent.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory Finset LMLExplore.OnlineLearning

namespace LMLExplore.Bandits

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A round of a linear bandit algorithm is **unbiased** with respect to the σ-algebra `m`, for
the random loss `y`, the random action `A`, the random play `a` and the random loss estimate `Y`,
if the action has conditional mean `a` given `m` (the action is sampled from a distribution with
mean `a`) and the estimate has conditional mean `y` given `m` (the estimate is unbiased). The
integrability conditions make these expectations meaningful. These are the conditions of
[LS, Theorem 28.10], for losses chosen by an adaptive adversary: as conditional expectations given
`m`, the play and the loss are `m`-measurable (`IsUnbiasedRound.aestronglyMeasurable_play`,
`IsUnbiasedRound.aestronglyMeasurable_loss`), so the adversary chooses the loss of the round from
the information in `m`. -/
structure IsUnbiasedRound {mΩ : MeasurableSpace Ω} (m : MeasurableSpace Ω) (P : Measure[mΩ] Ω)
    (y : Ω → E →L[ℝ] ℝ) (A a : Ω → E) (Y : Ω → E →L[ℝ] ℝ) : Prop where
  /-- `m` is a sub-σ-algebra. -/
  le : m ≤ mΩ
  /-- The action is integrable. -/
  integrable_action : Integrable A P
  /-- The action has conditional mean `a` given `m`. -/
  condExp_action : P[A | m] =ᵐ[P] a
  /-- The loss of the action is integrable. -/
  integrable_apply_action : Integrable (fun ω ↦ y ω (A ω)) P
  /-- The loss estimate is integrable. -/
  integrable_estimate : Integrable Y P
  /-- The loss estimate has conditional mean `y` given `m`. -/
  condExp_estimate : P[Y | m] =ᵐ[P] y
  /-- The estimated loss of the play is integrable. -/
  integrable_estimate_apply_play : Integrable (fun ω ↦ Y ω (a ω)) P

namespace IsUnbiasedRound

variable {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω} {y : Ω → E →L[ℝ] ℝ} {A a : Ω → E}
  {Y : Ω → E →L[ℝ] ℝ}

/-- The play of an unbiased round is `m`-measurable: it is the conditional mean of the action. -/
lemma aestronglyMeasurable_play (h : IsUnbiasedRound m P y A a Y) :
    AEStronglyMeasurable[m] a P :=
  stronglyMeasurable_condExp.aestronglyMeasurable.congr h.condExp_action

/-- The loss of an unbiased round is `m`-measurable: it is the conditional mean of the
estimate. -/
lemma aestronglyMeasurable_loss (h : IsUnbiasedRound m P y A a Y) :
    AEStronglyMeasurable[m] y P :=
  stronglyMeasurable_condExp.aestronglyMeasurable.congr h.condExp_estimate

/-- The play of an unbiased round is integrable. -/
lemma integrable_play [CompleteSpace E] (h : IsUnbiasedRound m P y A a Y) : Integrable a P :=
  integrable_condExp.congr h.condExp_action

/-- The loss of an unbiased round is integrable. -/
lemma integrable_loss (h : IsUnbiasedRound m P y A a Y) : Integrable y P :=
  integrable_condExp.congr h.condExp_estimate

/-- In an unbiased round, the expected loss of the action is the expected loss of the play. -/
lemma integral_apply_action [CompleteSpace E] [IsFiniteMeasure P]
    (h : IsUnbiasedRound m P y A a Y) :
    ∫ ω, y ω (A ω) ∂P = ∫ ω, y ω (a ω) ∂P := by
  -- pull the `m`-measurable loss out of the conditional expectation
  have h_pull := condExp_bilin_of_aestronglyMeasurable_left
    (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)) h.aestronglyMeasurable_loss
    h.integrable_apply_action h.integrable_action
  rw [← integral_condExp h.le]
  refine integral_congr_ae ?_
  filter_upwards [h_pull, h.condExp_action] with ω h_pull_ω h_act_ω
  simpa [h_act_ω] using h_pull_ω

/-- In an unbiased round, the expected estimated loss of the play is its expected loss. -/
lemma integral_estimate_apply_play [IsFiniteMeasure P] (h : IsUnbiasedRound m P y A a Y) :
    ∫ ω, Y ω (a ω) ∂P = ∫ ω, y ω (a ω) ∂P := by
  -- pull the `m`-measurable play out of the conditional expectation
  have h_pull := condExp_bilin_of_aestronglyMeasurable_right
    (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)) h.aestronglyMeasurable_play
    h.integrable_estimate_apply_play h.integrable_estimate
  rw [← integral_condExp h.le]
  refine integral_congr_ae ?_
  filter_upwards [h_pull, h.condExp_estimate] with ω h_pull_ω h_est_ω
  simpa [h_est_ω] using h_pull_ω

/-- In an unbiased round, the expected estimated loss of a fixed point `u` is its expected
loss. -/
lemma integral_estimate_apply [IsFiniteMeasure P] (h : IsUnbiasedRound m P y A a Y) (u : E) :
    ∫ ω, Y ω u ∂P = ∫ ω, y ω u ∂P := by
  rw [← ContinuousLinearMap.integral_apply h.integrable_estimate,
    ← ContinuousLinearMap.integral_apply h.integrable_loss, ← integral_condExp h.le (f := Y),
    integral_congr_ae h.condExp_estimate]

/-- In an unbiased round, the loss of the action against a fixed point `u` is integrable. -/
lemma integrable_apply_action_sub (h : IsUnbiasedRound m P y A a Y) (u : E) :
    Integrable (fun ω ↦ y ω (A ω - u)) P := by
  simp_rw [map_sub]
  exact h.integrable_apply_action.sub (h.integrable_loss.apply_continuousLinearMap u)

/-- In an unbiased round, the estimated loss of the play against a fixed point `u` is
integrable. -/
lemma integrable_estimate_apply_play_sub (h : IsUnbiasedRound m P y A a Y) (u : E) :
    Integrable (fun ω ↦ Y ω (a ω - u)) P := by
  simp_rw [map_sub]
  exact h.integrable_estimate_apply_play.sub (h.integrable_estimate.apply_continuousLinearMap u)

/-- In an unbiased round, the expected loss of the action against a fixed point `u` is the
expected estimated loss of the play against `u`. -/
lemma integral_apply_action_sub [CompleteSpace E] [IsFiniteMeasure P]
    (h : IsUnbiasedRound m P y A a Y) (u : E) :
    ∫ ω, y ω (A ω - u) ∂P = ∫ ω, Y ω (a ω - u) ∂P := by
  simp_rw [map_sub]
  rw [integral_sub h.integrable_apply_action (h.integrable_loss.apply_continuousLinearMap u),
    integral_sub h.integrable_estimate_apply_play
      (h.integrable_estimate.apply_continuousLinearMap u),
    h.integral_apply_action, h.integral_estimate_apply_play, h.integral_estimate_apply]

end IsUnbiasedRound

variable [CompleteSpace E] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {m : ℕ → MeasurableSpace Ω} {y : ℕ → Ω → E →L[ℝ] ℝ}
  {A a : ℕ → Ω → E} {Y : ℕ → Ω → E →L[ℝ] ℝ} {n : ℕ} {K D : Set E} {F : E → ℝ} {η : ℝ} {u : E}

/-- **Regret with unbiased estimates.** If every round `t < n` is unbiased with respect to `m t`,
then for every `u`, the expected regret `E[∑ t < n, y t (A t - u)]` of the actions equals the
expected regret `E[∑ t < n, Y t (a t - u)]` of the plays on the estimated losses. The losses
`y t` are random and `m t`-measurable, chosen by an adaptive adversary. This is the first step of
the proof of [LS, Theorem 28.10]. -/
theorem integral_sum_apply_sub_eq_integral_sum_apply_sub
    (h : ∀ t < n, IsUnbiasedRound (m t) P (y t) (A t) (a t) (Y t)) (u : E) :
    ∫ ω, ∑ t ∈ range n, y t ω (A t ω - u) ∂P = ∫ ω, ∑ t ∈ range n, Y t ω (a t ω - u) ∂P := by
  rw [integral_finsetSum _ fun t ht ↦ (h t (mem_range.mp ht)).integrable_apply_action_sub u,
    integral_finsetSum _ fun t ht ↦ (h t (mem_range.mp ht)).integrable_estimate_apply_play_sub u]
  exact sum_congr rfl fun t ht ↦ (h t (mem_range.mp ht)).integral_apply_action_sub u

/-- **Regret bounds transfer to unbiased estimates.** If every round `t < n` is unbiased with
respect to `m t` and the regret `∑ t < n, Y t (a t - u)` of the plays on the estimated losses is
almost surely at most an integrable `B`, then the expected regret of the actions against `u` is at
most `E[B]`. -/
theorem integral_sum_apply_sub_le_of_ae_le
    (h : ∀ t < n, IsUnbiasedRound (m t) P (y t) (A t) (a t) (Y t)) {B : Ω → ℝ}
    (hB : Integrable B P) (h_le : ∀ᵐ ω ∂P, ∑ t ∈ range n, Y t ω (a t ω - u) ≤ B ω) :
    ∫ ω, ∑ t ∈ range n, y t ω (A t ω - u) ∂P ≤ ∫ ω, B ω ∂P := by
  rw [integral_sum_apply_sub_eq_integral_sum_apply_sub h u]
  exact integral_mono_ae (integrable_finsetSum _ fun t ht ↦
    (h t (mem_range.mp ht)).integrable_estimate_apply_play_sub u) hB h_le

/-- **Regret of mirror descent with bandit feedback** [LS, Theorem 28.10], first bound. Let `F`
be convex on `K` and `η > 0`. Let every round `t < n` be unbiased with respect to `m t`, and let
the plays be, almost surely, mirror descent on `K` for the estimated losses: `a 0 ∈ K` minimizes
`F` over `K`, each `a (t + 1)`, for `t < n`, is a mirror descent step from `a t` with derivative
`F' t` for the loss `Y t`, and `F` has derivative `F' t` within `K` at `a t` for `t ≤ n`. Then
for every `u ∈ K`, if the bound below is integrable,
`E[∑ t < n, y t (A t - u)] ≤ E[(F u - F (a 0)) / η + ∑ t < n, Y t (a t - a (t + 1))
  - (∑ t < n, D_F(a (t + 1), a t)) / η]`,
with `D_F` the Bregman divergence. -/
theorem mirrorDescent_integral_regret_le (hF : ConvexOn ℝ K F) (hη : 0 < η)
    (h : ∀ t < n, IsUnbiasedRound (m t) P (y t) (A t) (a t) (Y t)) (F' : ℕ → Ω → E →L[ℝ] ℝ)
    (ha0 : ∀ᵐ ω ∂P, IsMinOn F K (a 0 ω)) (ha0K : ∀ᵐ ω ∂P, a 0 ω ∈ K)
    (ha : ∀ᵐ ω ∂P, ∀ t < n, IsMirrorDescentStep K F η (Y t ω) (a t ω) (F' t ω) (a (t + 1) ω))
    (hF' : ∀ᵐ ω ∂P, ∀ t ≤ n, HasFDerivWithinAt F (F' t ω) K (a t ω)) (hu : u ∈ K)
    (h_int : Integrable (fun ω ↦ (F u - F (a 0 ω)) / η +
      ∑ t ∈ range n, Y t ω (a t ω - a (t + 1) ω) -
        (∑ t ∈ range n, bregDiv F (a (t + 1) ω) (a t ω) (F' t ω)) / η) P) :
    ∫ ω, ∑ t ∈ range n, y t ω (A t ω - u) ∂P ≤
      ∫ ω, ((F u - F (a 0 ω)) / η + ∑ t ∈ range n, Y t ω (a t ω - a (t + 1) ω) -
        (∑ t ∈ range n, bregDiv F (a (t + 1) ω) (a t ω) (F' t ω)) / η) ∂P := by
  refine integral_sum_apply_sub_le_of_ae_le h h_int ?_
  filter_upwards [ha0, ha0K, ha, hF'] with ω ha0ω ha0Kω haω hF'ω
  exact mirrorDescent_regret_le hF hη (fun t ↦ Y t ω) (fun t ↦ a t ω) (fun t ↦ F' t ω) ha0ω ha0Kω
    haω hF'ω hu

/-- **Regret of FTRL with bandit feedback** [LS, Theorem 28.10], first bound. Let `K` be convex
and `η > 0`. Let every round `t < n` be unbiased with respect to `m t`, and let the plays be,
almost surely, FTRL on `K` for the estimated losses: each `a t`, for `t ≤ n`, is a play of FTRL
with potential `F` and learning rate `η` for the losses `Y`, where `F` has derivative `F' t`
within `K` at `a t` for `t < n`. Then for every `u ∈ K`, if the bound below is integrable,
`E[∑ t < n, y t (A t - u)] ≤ E[(F u - F (a 0)) / η + ∑ t < n, Y t (a t - a (t + 1))
  - (∑ t < n, D_F(a (t + 1), a t)) / η]`,
with `D_F` the Bregman divergence. As in `ftrl_regret_le`, the potential need not be convex. -/
theorem ftrl_integral_regret_le (hK : Convex ℝ K) (hη : 0 < η)
    (h : ∀ t < n, IsUnbiasedRound (m t) P (y t) (A t) (a t) (Y t))
    (ha : ∀ᵐ ω ∂P, ∀ t ≤ n, IsFTRLPlay K F η (fun s ↦ Y s ω) t (a t ω))
    (F' : ℕ → Ω → E →L[ℝ] ℝ) (hF' : ∀ᵐ ω ∂P, ∀ t < n, HasFDerivWithinAt F (F' t ω) K (a t ω))
    (hu : u ∈ K)
    (h_int : Integrable (fun ω ↦ (F u - F (a 0 ω)) / η +
      ∑ t ∈ range n, Y t ω (a t ω - a (t + 1) ω) -
        (∑ t ∈ range n, bregDiv F (a (t + 1) ω) (a t ω) (F' t ω)) / η) P) :
    ∫ ω, ∑ t ∈ range n, y t ω (A t ω - u) ∂P ≤
      ∫ ω, ((F u - F (a 0 ω)) / η + ∑ t ∈ range n, Y t ω (a t ω - a (t + 1) ω) -
        (∑ t ∈ range n, bregDiv F (a (t + 1) ω) (a t ω) (F' t ω)) / η) ∂P := by
  refine integral_sum_apply_sub_le_of_ae_le h h_int ?_
  filter_upwards [ha, hF'] with ω haω hF'ω
  exact ftrl_regret_le hK hη (fun t ↦ Y t ω) (fun t ↦ a t ω) haω (fun t ↦ F' t ω) hF'ω hu

/-- **Regret of mirror descent with bandit feedback through the unconstrained steps**
[LS, Theorem 28.10], second bound. Let `F` be convex on a set `D` containing the convex set `K`,
and let `η > 0`. Let every round `t < n` be unbiased with respect to `m t`, and let the plays be,
almost surely, mirror descent on `K` for the estimated losses, as in
`mirrorDescent_integral_regret_le`. Let `b (t + 1) ∈ D` be, almost surely, a point where `F` has
derivative `G t = F' t - η Y t` within `D`, the unconstrained step of mirror descent. Then for
every `u ∈ K`, if the bound below is integrable,
`E[∑ t < n, y t (A t - u)] ≤ E[(F u - F (a 0) + ∑ t < n, D_F(a t, b (t + 1))) / η]`,
with `D_F` the Bregman divergence. -/
theorem mirrorDescent_integral_regret_le_sub_add_sum_bregDiv (hF : ConvexOn ℝ D F)
    (hKD : K ⊆ D) (hK : Convex ℝ K) (hη : 0 < η)
    (h : ∀ t < n, IsUnbiasedRound (m t) P (y t) (A t) (a t) (Y t)) (F' : ℕ → Ω → E →L[ℝ] ℝ)
    (ha0 : ∀ᵐ ω ∂P, IsMinOn F K (a 0 ω)) (ha0K : ∀ᵐ ω ∂P, a 0 ω ∈ K)
    (ha : ∀ᵐ ω ∂P, ∀ t < n, IsMirrorDescentStep K F η (Y t ω) (a t ω) (F' t ω) (a (t + 1) ω))
    (hF' : ∀ᵐ ω ∂P, ∀ t ≤ n, HasFDerivWithinAt F (F' t ω) K (a t ω)) (b : ℕ → Ω → E)
    (G : ℕ → Ω → E →L[ℝ] ℝ) (hG : ∀ᵐ ω ∂P, ∀ t < n, G t ω = F' t ω - η • Y t ω)
    (hb : ∀ᵐ ω ∂P, ∀ t < n, b (t + 1) ω ∈ D)
    (hGb : ∀ᵐ ω ∂P, ∀ t < n, HasFDerivWithinAt F (G t ω) D (b (t + 1) ω)) (hu : u ∈ K)
    (h_int : Integrable (fun ω ↦
      (F u - F (a 0 ω) + ∑ t ∈ range n, bregDiv F (a t ω) (b (t + 1) ω) (G t ω)) / η) P) :
    ∫ ω, ∑ t ∈ range n, y t ω (A t ω - u) ∂P ≤
      ∫ ω, (F u - F (a 0 ω) + ∑ t ∈ range n, bregDiv F (a t ω) (b (t + 1) ω) (G t ω)) / η ∂P := by
  refine integral_sum_apply_sub_le_of_ae_le h h_int ?_
  filter_upwards [ha0, ha0K, ha, hF', hG, hb, hGb] with ω ha0ω ha0Kω haω hF'ω hGω hbω hGbω
  exact mirrorDescent_regret_le_sub_add_sum_bregDiv hF hKD hK hη (fun t ↦ Y t ω) (fun t ↦ a t ω)
    (fun t ↦ F' t ω) ha0ω ha0Kω haω hF'ω (fun t ↦ b t ω) (fun t ↦ G t ω) hGω hbω hGbω hu

end LMLExplore.Bandits
