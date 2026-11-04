/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Optimality
public import LMLExplore.MeasureTheory.Measure.TotalVariation.Basic

/-!
# The simulation lemma

Let `M` and `M'` be two MDPs on the same state and action spaces, with the same mean reward `r`
and transition kernels `P` and `P'`; typically `M'` is a model of `M` estimated from samples of its
transitions. For a stationary policy `π` and `0 ≤ γ < 1`, the action values of `π` in the two
models are the resolvents of their state-action kernels applied to `r`,
`Q^π_M = R_γ(P^π_SA) r` and `Q^π_M' = R_γ(P'^π_SA) r`. The simulation identity for resolvents
(`ProbabilityTheory.Kernel.integral_resolvent_sub_integral_resolvent`) compares them through the
one-step difference of the transition kernels acting on the value of `π` in `M`:

`Q^π_M - Q^π_M' = γ R_γ(P'^π_SA) ((P - P') v^π_M)`.

Since `R_γ(P'^π_SA)` has mass `(1 - γ)⁻¹`, an error of at most `ε` in the one-step predictions
`|∫ v^π_M dP (s, a) - ∫ v^π_M dP' (s, a)| ≤ ε` of the model results in an error of at most
`γ ε / (1 - γ)` in the action values and the values of `π`. This is the basic tool for planning
with an estimated model: errors in the transitions are measured only through the value of the
policy, not uniformly over all functions.

With finitely many actions, the same comparison holds for the optimal action values, as
componentwise bounds. Let `π*` be an optimal stationary policy of `M` and `π'*` one of `M'`, and
write `v*` for the optimal value of `M`. Then

`γ R_γ(P'^π'*_SA) ((P - P') v*) ≤ Q*_M - Q*_M' ≤ γ R_γ(P'^π*_SA) ((P - P') v*)`.

The upper bound is the simulation lemma for `π*`, since `π*` is suboptimal in `M'`. The lower
bound compares `Q*_M - Q*_M'` with the solution of the resolvent equation of `P'^π'*_SA`: it is a
supersolution, because `π'*` is suboptimal in `M`. Only the fixed function `v*` of `M` enters the
transition error, so that an error of at most `ε` in the one-step predictions of `v*` results in
an error of at most `γ ε / (1 - γ)` in the optimal action values and the optimal values.

When the transition kernels are within `η` in total variation, `tvDist (P (s, a)) (P' (s, a)) ≤ η`
(Mathlib's `tvDist`, with values in `[0, 2]`), and the rewards of `M` satisfy `|r| ≤ C`, the
one-step predictions of every function bounded by `C / (1 - γ)`, such as `v^π_M` and `v*`, differ
by at most `C η / (1 - γ)` (`MeasureTheory.abs_integral_sub_integral_le_mul_tvDist`). The action
values, values, optimal action values and optimal values of the two MDPs then differ by at most
`γ C η / (1 - γ) ^ 2`. This is the form in which the simulation lemma is used for a model estimated
from samples, whose kernels concentrate in total variation around the true ones.

## Main statements

* `Learning.MDP.qValue_sub_qValue`: **the simulation lemma** [AJKS, Lemma 2.2],
  `Q^π_M - Q^π_M' = γ R_γ(P'^π_SA) ((P - P') v^π_M)`.
* `Learning.MDP.abs_qValue_sub_qValue_le`, `Learning.MDP.abs_value_sub_value_le`: if
  `|(P - P') v^π_M| ≤ ε`, the action values and the values of `π` in the two models differ by at
  most `γ ε / (1 - γ)`.
* `Learning.MDP.optQValue_sub_optQValue_le`, `Learning.MDP.le_optQValue_sub_optQValue`:
  **the componentwise bounds** [AJKS, Lemma 2.5] on `Q*_M - Q*_M'`.
* `Learning.MDP.abs_optQValue_sub_optQValue_le`, `Learning.MDP.abs_optValue_sub_optValue_le`: if
  `|(P - P') v*| ≤ ε`, the optimal action values and the optimal values of the two models differ by
  at most `γ ε / (1 - γ)`.
* `Learning.MDP.abs_qValue_sub_qValue_le_of_tvDist_le`,
  `Learning.MDP.abs_value_sub_value_le_of_tvDist_le`,
  `Learning.MDP.abs_optQValue_sub_optQValue_le_of_tvDist_le`,
  `Learning.MDP.abs_optValue_sub_optValue_le_of_tvDist_le`: if the transition kernels are within
  `η` in total variation and `|r| ≤ C`, these four pairs differ by at most `γ C η / (1 - γ) ^ 2`.

## References

* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], Lemmas 2.2 and 2.5
-/

public section

open MeasureTheory ProbabilityTheory LMLExplore Learning
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {M M' : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {π : Kernel 𝓢 𝓐} [IsMarkovKernel π] {C C' ε : ℝ}

/-- **The simulation lemma** [AJKS, Lemma 2.2]: for two MDPs `M` and `M'` with the same mean
reward and bounded rewards, `γ < 1` and a stationary policy `π`, the action values of `π` differ by
the resolvent of the state-action kernel of `π` in `M'` applied to the one-step difference of the
transition kernels acting on the value of `π` in `M`:
`Q^π_M - Q^π_M' = γ R_γ(P'^π_SA) ((P - P') v^π_M)`. -/
theorem qValue_sub_qValue (hr : meanReward M'.R = meanReward M.R) (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') (p : 𝓢 × 𝓐) :
    M.qValue γ π p - M'.qValue γ π p =
      γ * ∫ q, (∫ s, M.value γ π s ∂(M.P q) - ∫ s, M.value γ π s ∂(M'.P q))
        ∂(Kernel.resolvent γ (M'.saKernel π) p) := by
  have h := Kernel.integral_resolvent_sub_integral_resolvent (κ := M'.saKernel π) (M.saKernel π)
    hγ (measurable_meanReward M.R) (abs_meanReward_le hR) p
  have hQ' := qValue_eq_integral_resolvent (M := M') (π := π) hγ hR' p
  rw [hr] at hQ'
  simp_rw [← hQ', ← qValue_eq_integral_resolvent hγ hR, integral_qValue_saKernel _ hγ hR] at h
  rw [← neg_sub, h, ← mul_neg, ← integral_neg]
  simp_rw [neg_sub]

/-- **The simulation bound**: for two MDPs `M` and `M'` with the same mean reward and bounded
rewards, `γ < 1` and a stationary policy `π`, if the one-step predictions of the value of `π` in
`M` differ by at most `ε`, `|∫ v^π_M dP (s, a) - ∫ v^π_M dP' (s, a)| ≤ ε`, then the action values
of `π` differ by at most `γ ε / (1 - γ)`. -/
theorem abs_qValue_sub_qValue_le (hr : meanReward M'.R = meanReward M.R) (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    (hε : ∀ q, |∫ s, M.value γ π s ∂(M.P q) - ∫ s, M.value γ π s ∂(M'.P q)| ≤ ε)
    (p : 𝓢 × 𝓐) :
    |M.qValue γ π p - M'.qValue γ π p| ≤ γ * ε / (1 - γ) := by
  rw [qValue_sub_qValue hr hγ hR hR']
  exact Kernel.abs_mul_integral_resolvent_le hγ hε p

/-- For two MDPs `M` and `M'` with the same mean reward and bounded rewards, `γ < 1` and a
stationary policy `π`, if the one-step predictions of the value of `π` in `M` differ by at most
`ε`, `|∫ v^π_M dP (s, a) - ∫ v^π_M dP' (s, a)| ≤ ε`, then the values of `π` differ by at most
`γ ε / (1 - γ)`. -/
theorem abs_value_sub_value_le (hr : meanReward M'.R = meanReward M.R) (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    (hε : ∀ q, |∫ s, M.value γ π s ∂(M.P q) - ∫ s, M.value γ π s ∂(M'.P q)| ≤ ε) (s : 𝓢) :
    |M.value γ π s - M'.value γ π s| ≤ γ * ε / (1 - γ) := by
  rw [← integral_qValue hγ hR, ← integral_qValue hγ hR',
    ← integral_sub (integrable_qValue_prodMk_left hγ hR s _)
      (integrable_qValue_prodMk_left hγ hR' s _)]
  exact abs_integral_le_of_abs_le fun a ↦ abs_qValue_sub_qValue_le hr hγ hR hR' hε (s, a)

/-! ### Bounds in total variation -/

/-- If the transition kernels of `M` and `M'` are within `η` in total variation, the one-step
predictions of a measurable function bounded by `B` differ by at most `B * η`. -/
private lemma abs_integral_sub_integral_le_of_tvDist_le {v : 𝓢 → ℝ} {B η : ℝ}
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (hη : ∀ q, tvDist (M.P q) (M'.P q) ≤ η)
    (q : 𝓢 × 𝓐) :
    |∫ s, v s ∂(M.P q) - ∫ s, v s ∂(M'.P q)| ≤ B * η :=
  (abs_integral_sub_integral_le_mul_tvDist hv.aestronglyMeasurable hv.aestronglyMeasurable
    (.of_forall hvB) (.of_forall hvB)).trans
    (mul_le_mul_of_nonneg_left (hη q) ((abs_nonneg _).trans (hvB q.1)))

/-- **The simulation bound in total variation**, a consequence of the simulation lemma
[AJKS, Lemma 2.2]: for two MDPs `M` and `M'` with the same mean reward and bounded rewards,
`|r| ≤ C` for `M`, `γ < 1` and a stationary policy `π`, if the transition kernels are within `η`
in total variation, `tvDist (P (s, a)) (P' (s, a)) ≤ η`, then the action values of `π` differ by
at most `γ C η / (1 - γ) ^ 2`. -/
theorem abs_qValue_sub_qValue_le_of_tvDist_le (hr : meanReward M'.R = meanReward M.R)
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    {η : ℝ} (hη : ∀ q, tvDist (M.P q) (M'.P q) ≤ η) (p : 𝓢 × 𝓐) :
    |M.qValue γ π p - M'.qValue γ π p| ≤ γ * C * η / (1 - γ) ^ 2 :=
  (abs_qValue_sub_qValue_le hr hγ hR hR' (abs_integral_sub_integral_le_of_tvDist_le
    (measurable_value hγ hR) (abs_value_le hγ hR) hη) p).trans_eq (by rw [sq, ← div_div]; ring)

/-- **The simulation bound in total variation**, for values: for two MDPs `M` and `M'` with the
same mean reward and bounded rewards, `|r| ≤ C` for `M`, `γ < 1` and a stationary policy `π`, if
the transition kernels are within `η` in total variation, then the values of `π` differ by at
most `γ C η / (1 - γ) ^ 2`. -/
theorem abs_value_sub_value_le_of_tvDist_le (hr : meanReward M'.R = meanReward M.R)
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    {η : ℝ} (hη : ∀ q, tvDist (M.P q) (M'.P q) ≤ η) (s : 𝓢) :
    |M.value γ π s - M'.value γ π s| ≤ γ * C * η / (1 - γ) ^ 2 :=
  (abs_value_sub_value_le hr hγ hR hR' (abs_integral_sub_integral_le_of_tvDist_le
    (measurable_value hγ hR) (abs_value_le hγ hR) hη) s).trans_eq (by rw [sq, ← div_div]; ring)

/-! ### Componentwise bounds on the optimal action values -/

section Optimal

variable [Nonempty 𝓢] [Nonempty 𝓐] [Finite 𝓐] {π' : Kernel 𝓢 𝓐} [IsMarkovKernel π']

/-- **Componentwise upper bound** [AJKS, Lemma 2.5]: for two MDPs `M` and `M'` with the same mean
reward, finitely many actions, bounded rewards and `γ < 1`, and an optimal stationary policy `π`
of `M`, the optimal action values satisfy
`Q*_M - Q*_M' ≤ γ R_γ(P'^π_SA) ((P - P') v*_M)`. -/
theorem optQValue_sub_optQValue_le (hr : meanReward M'.R = meanReward M.R) (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    (hπ : M.value γ π = M.optValue γ) (p : 𝓢 × 𝓐) :
    M.optQValue γ p - M'.optQValue γ p ≤
      γ * ∫ q, (∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q))
        ∂(Kernel.resolvent γ (M'.saKernel π) p) := by
  rw [← hπ, ← qValue_eq_optQValue hπ, ← qValue_sub_qValue hr hγ hR hR' p]
  exact sub_le_sub_left (qValue_le_optQValue hγ hR' p) _

/-- **Componentwise lower bound** [AJKS, Lemma 2.5]: for two MDPs `M` and `M'` with the same mean
reward, finitely many actions, bounded rewards and `γ < 1`, and an optimal stationary policy `π'`
of `M'`, the optimal action values satisfy
`γ R_γ(P'^π'_SA) ((P - P') v*_M) ≤ Q*_M - Q*_M'`. -/
theorem le_optQValue_sub_optQValue (hr : meanReward M'.R = meanReward M.R) (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    (hπ' : M'.value γ π' = M'.optValue γ) (p : 𝓢 × 𝓐) :
    γ * ∫ q, (∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q))
        ∂(Kernel.resolvent γ (M'.saKernel π') p) ≤
      M.optQValue γ p - M'.optQValue γ p := by
  have hv := measurable_optValue hγ hR
  have hvB := abs_optValue_le hγ hR
  have hQ := measurable_optQValue hγ hR
  have hQ' := measurable_optQValue hγ hR'
  -- `Q*_M - Q*_M'` is a supersolution of the resolvent equation `u = γ (P - P') v* + γ P'^π'_SA u`
  rw [← integral_const_mul]
  refine Kernel.integral_resolvent_le_of_add_le hγ (B := γ * (C / (1 - γ) + C / (1 - γ)))
    (u := fun q ↦ M.optQValue γ q - M'.optQValue γ q)
    (((hv.stronglyMeasurable.integral_kernel (κ := M.P)).measurable.sub
      (hv.stronglyMeasurable.integral_kernel (κ := M'.P)).measurable).const_mul _)
    (fun q ↦ ?_) (hQ.sub hQ')
    (fun q ↦ (abs_sub _ _).trans
      (add_le_add (abs_optQValue_le hγ hR q) (abs_optQValue_le hγ hR' q)))
    (fun q ↦ ?_) p
  · rw [abs_mul, NNReal.abs_eq]
    gcongr
    exact (abs_sub _ _).trans
      (add_le_add (abs_integral_le_of_abs_le hvB) (abs_integral_le_of_abs_le hvB))
  have hint := integrable_of_abs_le hQ (abs_optQValue_le hγ hR) (M'.saKernel π' q)
  have hint' := integrable_of_abs_le hQ' (abs_optQValue_le hγ hR') (M'.saKernel π' q)
  -- `π'` is suboptimal in `M`: `P'^π'_SA Q*_M ≤ P' v*_M`
  have h₁ := integral_optQValue_saKernel_le (π := π') M' hγ hR q
  -- `π'` is optimal in `M'`: `P'^π'_SA Q*_M' = P' v*_M'`
  have h₂ : ∫ w, M'.optQValue γ w ∂(M'.saKernel π' q) = ∫ s, M'.optValue γ s ∂(M'.P q) := by
    rw [← qValue_eq_optQValue hπ', integral_qValue_saKernel M' hγ hR' q, hπ']
  have h₃ := mul_le_mul_of_nonneg_left h₁ γ.coe_nonneg
  rw [integral_sub hint hint', h₂, optQValue_def M γ q, optQValue_def M' γ q, hr, Pi.sub_apply]
  linarith

/-- For two MDPs `M` and `M'` with the same mean reward, finitely many actions, bounded rewards
and `γ < 1`, if the one-step predictions of the optimal value `v*` of `M` differ by at most `ε`,
`|∫ v* dP (s, a) - ∫ v* dP' (s, a)| ≤ ε`, then the optimal action values of the two MDPs differ by
at most `γ ε / (1 - γ)`. -/
theorem abs_optQValue_sub_optQValue_le (hr : meanReward M'.R = meanReward M.R) (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    (hε : ∀ q, |∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)| ≤ ε)
    (p : 𝓢 × 𝓐) :
    |M.optQValue γ p - M'.optQValue γ p| ≤ γ * ε / (1 - γ) := by
  have := Fintype.ofFinite 𝓐
  have hb (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] :=
    Kernel.abs_mul_integral_resolvent_le (κ := M'.saKernel π) hγ hε p
  -- the greedy policies for the optimal values are optimal stationary policies
  have hg := measurable_greedy (M := M) (γ := γ) (measurable_optValue hγ hR)
  have hg' := measurable_greedy (M := M') (γ := γ) (measurable_optValue hγ hR')
  exact abs_le.2 ⟨(neg_le_of_abs_le (hb _)).trans
    (le_optQValue_sub_optQValue hr hγ hR hR' (value_greedy_optValue hγ hR' hg') p),
    (optQValue_sub_optQValue_le hr hγ hR hR' (value_greedy_optValue hγ hR hg) p).trans
      (le_of_abs_le (hb _))⟩

/-- For two MDPs `M` and `M'` with the same mean reward, finitely many actions, bounded rewards
and `γ < 1`, if the one-step predictions of the optimal value `v*` of `M` differ by at most `ε`,
`|∫ v* dP (s, a) - ∫ v* dP' (s, a)| ≤ ε`, then the optimal values of the two MDPs differ by at most
`γ ε / (1 - γ)`. -/
theorem abs_optValue_sub_optValue_le (hr : meanReward M'.R = meanReward M.R) (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    (hε : ∀ q, |∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)| ≤ ε) (s : 𝓢) :
    |M.optValue γ s - M'.optValue γ s| ≤ γ * ε / (1 - γ) := by
  have h a := abs_le.1 (abs_optQValue_sub_optQValue_le hr hγ hR hR' hε (s, a))
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · rw [sub_le_iff_le_add, ← iSup_optQValue hγ hR s]
    exact ciSup_le fun a ↦ by linarith [(h a).2, optQValue_le_optValue hγ hR' s a]
  · rw [sub_le_iff_le_add, ← iSup_optQValue hγ hR' s]
    exact ciSup_le fun a ↦ by linarith [(h a).1, optQValue_le_optValue hγ hR s a]

/-- **The simulation bound in total variation**, for optimal action values: for two MDPs `M` and
`M'` with the same mean reward, finitely many actions, bounded rewards, `|r| ≤ C` for `M`, and
`γ < 1`, if the transition kernels are within `η` in total variation, then the optimal action
values of the two MDPs differ by at most `γ C η / (1 - γ) ^ 2`. -/
theorem abs_optQValue_sub_optQValue_le_of_tvDist_le (hr : meanReward M'.R = meanReward M.R)
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    {η : ℝ} (hη : ∀ q, tvDist (M.P q) (M'.P q) ≤ η) (p : 𝓢 × 𝓐) :
    |M.optQValue γ p - M'.optQValue γ p| ≤ γ * C * η / (1 - γ) ^ 2 :=
  (abs_optQValue_sub_optQValue_le hr hγ hR hR' (abs_integral_sub_integral_le_of_tvDist_le
    (measurable_optValue hγ hR) (abs_optValue_le hγ hR) hη) p).trans_eq
    (by rw [sq, ← div_div]; ring)

/-- **The simulation bound in total variation**, for optimal values: for two MDPs `M` and `M'`
with the same mean reward, finitely many actions, bounded rewards, `|r| ≤ C` for `M`, and
`γ < 1`, if the transition kernels are within `η` in total variation, then the optimal values of
the two MDPs differ by at most `γ C η / (1 - γ) ^ 2`. -/
theorem abs_optValue_sub_optValue_le_of_tvDist_le (hr : meanReward M'.R = meanReward M.R)
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    {η : ℝ} (hη : ∀ q, tvDist (M.P q) (M'.P q) ≤ η) (s : 𝓢) :
    |M.optValue γ s - M'.optValue γ s| ≤ γ * C * η / (1 - γ) ^ 2 :=
  (abs_optValue_sub_optValue_le hr hγ hR hR' (abs_integral_sub_integral_le_of_tvDist_le
    (measurable_optValue hγ hR) (abs_optValue_le hγ hR) hη) s).trans_eq
    (by rw [sq, ← div_div]; ring)

end Optimal

end Learning.MDP
