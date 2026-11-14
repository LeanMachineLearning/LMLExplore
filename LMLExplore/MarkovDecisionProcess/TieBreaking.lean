/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Simulation
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.ConditionalProbability
import LMLExplore.MeasureTheory.Constructions.Pi
import LMLExplore.MeasureTheory.Measure.Real

/-!
# Breaking ties between optimal action values by perturbing the rewards

The optimal policy of an MDP need not be unique, and two actions may have optimal action values
arbitrarily close to each other. Adding a small random perturbation to the rewards separates the
optimal action values of distinct actions with high probability. This is the tie-breaking step of
the perturbed model-based planning algorithm of [LWCGC24, Lemma 6]: with probability at least
`1 - δ`, every state of the perturbed model has a unique optimal action, whose optimal action
value exceeds that of every other action by a polynomially small margin.

The deterministic part holds on any measurable state space with finitely many actions, bounded
rewards and `γ < 1`. Let `M` and `M'` be two MDPs with the same transition kernel. If the mean
rewards of `M'` are at least those of `M`, so are the optimal action values and the optimal values
(`Learning.MDP.optQValue_le_optQValue_of_meanReward_le` in
`LMLExplore.MarkovDecisionProcess.Simulation`). Suppose moreover that the mean rewards only differ
at one pair `p`. Then the increase of the optimal value at every state is at most the increase `D`
of the optimal action value at `p`, the optimal action value at every other pair `q` increases by
at most `γ D`, and the gap `Q* p - Q* q` increases by at least `(1 - γ)` times the increase of the
reward at `p`.

So, as a function of the reward `τ` at `p`, the gap `Q*_τ p - Q*_τ q` increases at rate at least
`1 - γ`, and it is at most `ω` in absolute value only on an interval of length `2 ω / (1 - γ)`.
This monotonicity statement takes the place of the phase transition in the reward of
[LWCGC24, proof of Lemma 6].

For finite state and action spaces with `S` states and `A` actions, let `ζ` be a random vector of
independent rewards `ζ p` whose laws have densities bounded by `L` with respect to the Lebesgue
measure. Given the other coordinates, the gap between the optimal action values of two distinct
actions `a₁ ≠ a₂` at a state `s` is at most `ω` with probability at most `2 L ω / (1 - γ)`, by
resampling the coordinate `ζ (s, a₁)`. A union bound over the `S A²` triples `(s, a₁, a₂)` shows
that, with probability at least `1 - δ`, all such gaps of the MDP with transition kernel `P` and
deterministic rewards `r + ζ` exceed `δ (1 - γ) / (2 L S A²)`. For `ζ p` uniform on `[0, ξ]`, this
is the separation `ξ δ (1 - γ) / (2 S A²)`, better than the `ξ δ (1 - γ) / (3 S A²)` of
[LWCGC24, Lemma 6]. On this event, every state has a unique optimal action, whose optimal action
value exceeds that of every other action by more than the separation. The transition kernel `P`
is an arbitrary fixed kernel, such as the empirical kernel of the samples of a generative model,
which the perturbation is independent of.

## Main statements

* `Learning.MDP.optValue_sub_optValue_le_optQValue_sub_optQValue`: raising the reward at one pair
  `p` raises the optimal value by at most the increase of the optimal action value at `p`.
* `Learning.MDP.optQValue_sub_optQValue_le_mul_optQValue_sub_optQValue`: it raises the optimal
  action value at every other pair by at most `γ` times the increase at `p`.
* `Learning.MDP.mul_meanReward_sub_le_optQValue_sub_sub_optQValue_sub`: it raises the gap
  `Q* p - Q* q` by at least `(1 - γ)` times the increase of the reward.
* `Learning.MDP.optQValue_add_lt_optValue_of_forall_lt_abs_optQValue_sub`: if the optimal action
  values of distinct actions at `s` differ by more than `ω`, an optimal action at `s` beats every
  other action by more than `ω`; for `0 ≤ ω`, it is then the unique optimal action.
* `Learning.MDP.continuous_optQValue_ofDet`: for finite state and action spaces, the optimal
  action values are continuous in the deterministic rewards.
* `Learning.MDP.le_measureReal_pi_forall_lt_abs_optQValue_ofDet_sub`: **tie-breaking**, for
  independent perturbations with densities bounded by `L`.
* `Learning.MDP.le_measureReal_pi_cond_Icc_forall_lt_abs_optQValue_ofDet_sub`: **tie-breaking**
  for uniform perturbations on `[0, ξ]` [LWCGC24, Lemma 6].

## References

* [G. Li, Y. Wei, Y. Chi, Y. Gu and Y. Chen, *Breaking the sample size barrier in model-based
  reinforcement learning with a generative model*, Operations Research, 2024][LWCGC24], Lemma 6
  and its proof in Appendix B.5 (arXiv:2005.12900)
-/

public section

open MeasureTheory ProbabilityTheory Set LMLExplore Learning
open scoped ENNReal NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}

section Deterministic

variable [Nonempty 𝓢] [Nonempty 𝓐] [Finite 𝓐] {M M' : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {C C' : ℝ}

/-! ### Raising the reward at one pair -/

variable {p q : 𝓢 × 𝓐}

omit [Nonempty 𝓢] [Nonempty 𝓐] [Finite 𝓐] in
/-- Mean rewards that agree outside the pair `p` and increase at `p` increase everywhere. -/
private lemma meanReward_le_of_eq_of_ne (hr : ∀ q ≠ p, meanReward M'.R q = meanReward M.R q)
    (hp : meanReward M.R p ≤ meanReward M'.R p) (q : 𝓢 × 𝓐) :
    meanReward M.R q ≤ meanReward M'.R q :=
  (eq_or_ne q p).elim (· ▸ hp) fun hq ↦ (hr q hq).ge

/-- If two MDPs have the same transition kernel and the same mean reward at `q`, their optimal
action values at `q` differ by `γ` times the one-step prediction of the difference of their
optimal values. -/
lemma optQValue_sub_optQValue_eq_mul_integral (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') (hP : M'.P = M.P)
    (hq : meanReward M'.R q = meanReward M.R q) :
    M'.optQValue γ q - M.optQValue γ q =
      γ * ∫ s, (M'.optValue γ s - M.optValue γ s) ∂(M.P q) := by
  rw [optQValue_def, optQValue_def, hq, hP, add_sub_add_left_eq_sub, ← mul_sub,
    integral_sub (integrable_optValue hγ hR' _) (integrable_optValue hγ hR _)]

/-- **Raising the reward at one pair raises the optimal value by at most the increase of the
optimal action value at that pair.** For two MDPs with finitely many actions, bounded rewards, the
same transition kernel and `γ < 1`, whose mean rewards agree outside the pair `p` and satisfy
`r p ≤ r' p`, the optimal values satisfy `v*' s - v* s ≤ Q*' p - Q* p` at every state `s`. -/
theorem optValue_sub_optValue_le_optQValue_sub_optQValue (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') (hP : M'.P = M.P)
    (hr : ∀ q ≠ p, meanReward M'.R q = meanReward M.R q)
    (hp : meanReward M.R p ≤ meanReward M'.R p) (s : 𝓢) :
    M'.optValue γ s - M.optValue γ s ≤ M'.optQValue γ p - M.optQValue γ p := by
  have hD : 0 ≤ M'.optQValue γ p - M.optQValue γ p := sub_nonneg.2
    (optQValue_le_optQValue_of_meanReward_le hγ hR hR' hP (meanReward_le_of_eq_of_ne hr hp) p)
  -- `d` is the largest increase of the optimal value; the optimal action values at the other
  -- pairs increase by at most `γ d`, so `d` is at most the increase at `p` or at most `γ d`, and
  -- in the second case `d ≤ 0`
  have hbdd : BddAbove (range fun s ↦ M'.optValue γ s - M.optValue γ s) :=
    ⟨C' / (1 - γ) + C / (1 - γ), by
      rintro _ ⟨s, rfl⟩
      exact (le_abs_self _).trans ((abs_sub _ _).trans
        (add_le_add (abs_optValue_le hγ hR' s) (abs_optValue_le hγ hR s)))⟩
  set d := ⨆ s, (M'.optValue γ s - M.optValue γ s)
  have hle (s : 𝓢) : M'.optValue γ s - M.optValue γ s ≤ d := le_ciSup hbdd s
  -- at the other pairs, the optimal action value increases by at most `γ d`
  have hq (q : 𝓢 × 𝓐) (hq : q ≠ p) : M'.optQValue γ q - M.optQValue γ q ≤ γ * d := by
    rw [optQValue_sub_optQValue_eq_mul_integral hγ hR hR' hP (hr q hq)]
    gcongr
    exact (integral_mono ((integrable_optValue hγ hR' _).sub (integrable_optValue hγ hR _))
      (integrable_const d) hle).trans_eq (by simp)
  -- the optimal value at `s'` increases by at most the increase at an optimal action of `M'`
  have hs (s' : 𝓢) : M'.optValue γ s' - M.optValue γ s' ≤
      max (M'.optQValue γ p - M.optQValue γ p) (γ * d) := by
    obtain ⟨a, ha⟩ := exists_eq_ciSup_of_finite (f := fun a ↦ M'.optQValue γ (s', a))
    have h₁ := optQValue_le_optValue hγ hR s' a
    rw [← iSup_optQValue hγ hR' s', ← ha]
    rcases eq_or_ne (s', a) p with h | h
    · rw [← h]
      exact le_max_of_le_left (by linarith)
    · exact le_max_of_le_right ((by linarith : _ ≤ M'.optQValue γ (s', a) -
        M.optQValue γ (s', a)).trans (hq _ h))
  rcases le_max_iff.1 (ciSup_le hs) with h | h
  · exact (hle s).trans h
  · -- `d ≤ γ d` with `γ < 1` forces `d ≤ 0`
    have hd : d ≤ 0 := by
      by_contra! hd
      exact (mul_lt_of_lt_one_left hd hγ).not_ge h
    exact (hle s).trans (hd.trans hD)

/-- **Raising the reward at one pair raises the optimal action values at the other pairs by at
most `γ` times the increase at that pair.** For two MDPs with finitely many actions, bounded
rewards, the same transition kernel and `γ < 1`, whose mean rewards agree outside the pair `p`
and satisfy `r p ≤ r' p`, every pair `q ≠ p` satisfies `Q*' q - Q* q ≤ γ (Q*' p - Q* p)`. -/
theorem optQValue_sub_optQValue_le_mul_optQValue_sub_optQValue (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') (hP : M'.P = M.P)
    (hr : ∀ q ≠ p, meanReward M'.R q = meanReward M.R q)
    (hp : meanReward M.R p ≤ meanReward M'.R p) (hq : q ≠ p) :
    M'.optQValue γ q - M.optQValue γ q ≤ γ * (M'.optQValue γ p - M.optQValue γ p) := by
  rw [optQValue_sub_optQValue_eq_mul_integral hγ hR hR' hP (hr q hq)]
  gcongr
  exact (integral_mono ((integrable_optValue hγ hR' _).sub (integrable_optValue hγ hR _))
    (integrable_const _)
    (optValue_sub_optValue_le_optQValue_sub_optQValue hγ hR hR' hP hr hp)).trans_eq (by simp)

/-- **The gaps of the optimal action values grow at rate at least `1 - γ` in the reward**
[LWCGC24, proof of Lemma 6]. For two MDPs with finitely many actions, bounded rewards, the same
transition kernel and `γ < 1`, whose mean rewards agree outside the pair `p` and satisfy
`r p ≤ r' p`, the gap between the optimal action values at `p` and at any pair `q ≠ p` satisfies
`(1 - γ) (r' p - r p) ≤ (Q*' p - Q*' q) - (Q* p - Q* q)`. -/
theorem mul_meanReward_sub_le_optQValue_sub_sub_optQValue_sub (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') (hP : M'.P = M.P)
    (hr : ∀ q ≠ p, meanReward M'.R q = meanReward M.R q)
    (hp : meanReward M.R p ≤ meanReward M'.R p) (hq : q ≠ p) :
    (1 - γ) * (meanReward M'.R p - meanReward M.R p) ≤
      M'.optQValue γ p - M'.optQValue γ q - (M.optQValue γ p - M.optQValue γ q) := by
  have h₁ := optQValue_sub_optQValue_le_mul_optQValue_sub_optQValue hγ hR hR' hP hr hp hq
  -- the optimal action value at `p` increases by at least the reward, since `v* ≤ v*'`
  have h₂ : meanReward M'.R p - meanReward M.R p ≤ M'.optQValue γ p - M.optQValue γ p := by
    have hv := integral_mono (integrable_optValue hγ hR (M.P p))
      (integrable_optValue hγ hR' (M.P p))
      (optValue_le_optValue_of_meanReward_le hγ hR hR' hP (meanReward_le_of_eq_of_ne hr hp))
    rw [optQValue_def, optQValue_def, hP]
    nlinarith [γ.coe_nonneg]
  have h₃ := mul_le_mul_of_nonneg_left h₂ (sub_nonneg.2 (NNReal.coe_le_one.2 hγ.le))
  linarith

/-! ### Separated optimal action values -/

/-- If the optimal action values of any two distinct actions at `s` differ by more than `ω`, then
for an optimal action `a` at `s`, with `Q* (s, a) = v* s`, every other action `a'` satisfies
`Q* (s, a') + ω < v* s`. If moreover `0 ≤ ω`, then `a` is the only optimal action at `s`. -/
theorem optQValue_add_lt_optValue_of_forall_lt_abs_optQValue_sub (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {s : 𝓢} {ω : ℝ}
    (hω : ∀ a₁ a₂, a₁ ≠ a₂ → ω < |M.optQValue γ (s, a₁) - M.optQValue γ (s, a₂)|) {a a' : 𝓐}
    (ha : M.optQValue γ (s, a) = M.optValue γ s) (ha' : a' ≠ a) :
    M.optQValue γ (s, a') + ω < M.optValue γ s := by
  have h := hω a a' ha'.symm
  rw [abs_of_nonneg (sub_nonneg.2 (ha ▸ optQValue_le_optValue hγ hR s a'))] at h
  linarith

end Deterministic

/-! ### Tie-breaking by random rewards -/

section TieBreaking

variable [MeasurableSingletonClass 𝓢] [MeasurableSingletonClass 𝓐] (P : Kernel (𝓢 × 𝓐) 𝓢)
  [IsMarkovKernel P] {γ : ℝ≥0}

/-- Deterministic rewards on finitely many pairs are bounded by the sum of their absolute
values. -/
private lemma ae_abs_ofDet_R_le_sum [Fintype 𝓢] [Fintype 𝓐] (r : 𝓢 × 𝓐 → ℝ) (p : 𝓢 × 𝓐) :
    ∀ᵐ x ∂((ofDet P r (measurable_of_finite r)).R p), |x| ≤ ∑ q, |r q| :=
  ae_abs_ofDet_R_le P _ (fun q ↦ Finset.single_le_sum (f := fun q ↦ |r q|)
    (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ q)) p

/-- For finite state and action spaces and `γ < 1`, the optimal action values of the MDP with
transition kernel `P` and deterministic rewards `r` are continuous in `r`. -/
theorem continuous_optQValue_ofDet [Finite 𝓢] [Finite 𝓐] [Nonempty 𝓢] [Nonempty 𝓐]
    (hγ : γ < 1) (q : 𝓢 × 𝓐) :
    Continuous fun r : 𝓢 × 𝓐 → ℝ ↦ (ofDet P r (measurable_of_finite r)).optQValue γ q := by
  have := Fintype.ofFinite 𝓢
  have := Fintype.ofFinite 𝓐
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  refine Metric.continuous_iff.2 fun r ε hε ↦ ⟨ε * (1 - γ), mul_pos hε h1γ, fun r' hr' ↦ ?_⟩
  rw [Real.dist_eq]
  refine (abs_optQValue_sub_optQValue_le hγ (ae_abs_ofDet_R_le_sum P r')
    (ae_abs_ofDet_R_le_sum P r) (δ := dist r' r) (ε := 0) (fun q ↦ ?_) (fun q ↦ by simp)
    q).trans_lt ?_
  · simpa [Real.dist_eq] using dist_le_pi_dist r' r q
  · rwa [mul_zero, zero_div, add_zero, div_lt_iff₀ h1γ]

/-- Along the coordinate `(s, a₁)` of the perturbation, the rewards at which the optimal action
values of `a₁` and of `a₂ ≠ a₁` at `s` are within `ω` form a set of diameter at most
`2 ω / (1 - γ)`, since their gap grows at rate at least `1 - γ`. -/
private lemma ediam_setOf_abs_optQValue_ofDet_sub_le [Finite 𝓢] [Finite 𝓐] [Nonempty 𝓢]
    [Nonempty 𝓐] [DecidableEq (𝓢 × 𝓐)] (hγ : γ < 1) (r x : 𝓢 × 𝓐 → ℝ) {s : 𝓢} {a₁ a₂ : 𝓐}
    (ha : a₁ ≠ a₂) (ω : ℝ) :
    Metric.ediam {τ | |(ofDet P (r + Function.update x (s, a₁) τ)
        (measurable_of_finite _)).optQValue γ (s, a₁) -
      (ofDet P (r + Function.update x (s, a₁) τ) (measurable_of_finite _)).optQValue γ (s, a₂)| ≤
        ω} ≤ ENNReal.ofReal (2 * ω / (1 - γ)) := by
  have := Fintype.ofFinite 𝓢
  have := Fintype.ofFinite 𝓐
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  have hline {τ τ' : ℝ} (hττ' : τ ≤ τ')
      (hτ : |(ofDet P (r + Function.update x (s, a₁) τ)
        (measurable_of_finite _)).optQValue γ (s, a₁) -
      (ofDet P (r + Function.update x (s, a₁) τ) (measurable_of_finite _)).optQValue γ (s, a₂)| ≤
        ω)
      (hτ' : |(ofDet P (r + Function.update x (s, a₁) τ')
        (measurable_of_finite _)).optQValue γ (s, a₁) -
      (ofDet P (r + Function.update x (s, a₁) τ') (measurable_of_finite _)).optQValue γ (s, a₂)| ≤
        ω) :
      τ' - τ ≤ 2 * ω / (1 - γ) := by
    have h := mul_meanReward_sub_le_optQValue_sub_sub_optQValue_sub hγ
      (ae_abs_ofDet_R_le_sum P _) (ae_abs_ofDet_R_le_sum P _) (by simp)
      (M := ofDet P (r + Function.update x (s, a₁) τ) (measurable_of_finite _))
      (M' := ofDet P (r + Function.update x (s, a₁) τ') (measurable_of_finite _))
      (p := (s, a₁)) (q := (s, a₂)) (fun q hq ↦ by simp [Function.update_of_ne hq])
      (by simpa using hττ') (by simpa using ha.symm)
    simp only [ofDet_R, meanReward_deterministic, Pi.add_apply, Function.update_self,
      add_sub_add_left_eq_sub] at h
    rw [le_div_iff₀ h1γ, mul_comm]
    linarith [(abs_le.1 hτ).1, (abs_le.1 hτ').2]
  refine Metric.ediam_le fun τ hτ τ' hτ' ↦ ?_
  rw [edist_dist, Real.dist_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases le_total τ τ' with h | h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
    exact hline h hτ hτ'
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact hline h hτ' hτ

/-- Given the other coordinates of an independent perturbation `ζ` with densities at most `L`, the
optimal action values of `a₁` and of `a₂ ≠ a₁` at `s` are within `ω` with probability at most
`2 L ω / (1 - γ)`. -/
private lemma measure_pi_abs_optQValue_ofDet_sub_le [Fintype 𝓢] [Fintype 𝓐] [Nonempty 𝓢]
    [Nonempty 𝓐] (r : 𝓢 × 𝓐 → ℝ) (hγ : γ < 1) {ν : 𝓢 × 𝓐 → Measure ℝ}
    [∀ p, IsProbabilityMeasure (ν p)] {L : ℝ} (hν : ∀ p t, ν p t ≤ ENNReal.ofReal L * volume t)
    {s : 𝓢} {a₁ a₂ : 𝓐} (ha : a₁ ≠ a₂) (ω : ℝ) :
    Measure.pi ν {ζ | |(ofDet P (r + ζ) (measurable_of_finite _)).optQValue γ (s, a₁) -
        (ofDet P (r + ζ) (measurable_of_finite _)).optQValue γ (s, a₂)| ≤ ω} ≤
      ENNReal.ofReal L * ENNReal.ofReal (2 * ω / (1 - γ)) := by
  classical
  have hg : Continuous fun ζ : 𝓢 × 𝓐 → ℝ ↦
      (ofDet P (r + ζ) (measurable_of_finite _)).optQValue γ (s, a₁) -
        (ofDet P (r + ζ) (measurable_of_finite _)).optQValue γ (s, a₂) :=
    ((continuous_optQValue_ofDet P hγ _).comp (continuous_const.add continuous_id)).sub
      ((continuous_optQValue_ofDet P hγ _).comp (continuous_const.add continuous_id))
  -- resample the coordinate `(s, a₁)`: the lines along it are short intervals
  refine Measure.pi_le_of_forall_measure_update_preimage_le
    (measurableSet_le hg.abs.measurable measurable_const) (s, a₁) fun x ↦ (hν _ _).trans ?_
  gcongr
  exact (Real.volume_le_diam _).trans (ediam_setOf_abs_optQValue_ofDet_sub_le P hγ r x ha ω)

/-- **Tie-breaking by random rewards** [LWCGC24, Lemma 6]. Let `𝓢` and `𝓐` be finite, with `S`
states and `A` actions, let `P` be a transition kernel, `r` a reward function and `γ < 1`. Let
the rewards `ζ p` be independent, with laws `ν p` of densities at most `L` with respect to the
Lebesgue measure. For `δ ≥ 0`, with probability at least `1 - δ`, the MDP with transition kernel
`P` and deterministic rewards `r + ζ` separates the optimal action values of any two distinct
actions at every state by more than `δ (1 - γ) / (2 L S A²)`. -/
theorem le_measureReal_pi_forall_lt_abs_optQValue_ofDet_sub [Fintype 𝓢] [Fintype 𝓐]
    [Nonempty 𝓢] [Nonempty 𝓐] (r : 𝓢 × 𝓐 → ℝ) (hγ : γ < 1)
    {ν : 𝓢 × 𝓐 → Measure ℝ} [∀ p, IsProbabilityMeasure (ν p)] {L : ℝ}
    (hν : ∀ p t, ν p t ≤ ENNReal.ofReal L * volume t) {δ : ℝ} (hδ : 0 ≤ δ) :
    1 - δ ≤ (Measure.pi ν).real {ζ | ∀ s a₁ a₂, a₁ ≠ a₂ →
      δ * (1 - γ) / (2 * L * (Fintype.card 𝓢 * Fintype.card 𝓐 ^ 2)) <
        |(ofDet P (r + ζ) (measurable_of_finite _)).optQValue γ (s, a₁) -
          (ofDet P (r + ζ) (measurable_of_finite _)).optQValue γ (s, a₂)|} := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  -- the densities are positive, since the laws are probability measures
  have hL : 0 < L := by
    have h := hν (Classical.arbitrary _) univ
    rw [measure_univ, Real.volume_univ] at h
    by_contra! hL
    simp [ENNReal.ofReal_of_nonpos hL] at h
  set K : ℝ := Fintype.card 𝓢 * Fintype.card 𝓐 ^ 2
  have hK : 0 < K := by
    have := Fintype.card_pos (α := 𝓢)
    have := Fintype.card_pos (α := 𝓐)
    positivity
  -- a union bound over the triples `(s, a₁, a₂)` with `a₁ ≠ a₂`
  refine (one_sub_le_measureReal_compl_iUnion hδ (s := fun i : 𝓢 × 𝓐 × 𝓐 ↦ {ζ | i.2.1 ≠ i.2.2 ∧
    |(ofDet P (r + ζ) (measurable_of_finite _)).optQValue γ (i.1, i.2.1) -
      (ofDet P (r + ζ) (measurable_of_finite _)).optQValue γ (i.1, i.2.2)| ≤
        δ * (1 - γ) / (2 * L * K)}) fun i ↦ ?_).trans
    (measureReal_mono fun ζ hζ s a₁ a₂ ha ↦ ?_)
  swap
  · simp only [mem_compl_iff, mem_iUnion, not_exists] at hζ
    exact not_le.1 fun h ↦ hζ (s, a₁, a₂) ⟨ha, h⟩
  obtain ⟨s, a₁, a₂⟩ := i
  rcases eq_or_ne a₁ a₂ with rfl | ha
  · simp only [ne_eq, not_true_eq_false, false_and, ofPred_false, measureReal_empty]
    positivity
  rw [ofPred_and]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ((measure_mono inter_subset_right).trans
    ((measure_pi_abs_optQValue_ofDet_sub_le P r hγ hν ha _).trans_eq ?_))
  rw [← ENNReal.ofReal_mul hL.le, Fintype.card_prod, Fintype.card_prod]
  congr 1
  simp only [K, Nat.cast_mul]
  field_simp

/-- **Tie-breaking by uniform random rewards** [LWCGC24, Lemma 6]. Let `𝓢` and `𝓐` be finite,
with `S` states and `A` actions, let `P` be a transition kernel, `r` a reward function, `γ < 1`
and `ξ > 0`. Let the rewards `ζ p` be independent and uniform on `[0, ξ]`. For `δ ≥ 0`, with
probability at least `1 - δ`, the MDP with transition kernel `P` and deterministic rewards
`r + ζ` separates the optimal action values of any two distinct actions at every state by more
than `ξ δ (1 - γ) / (2 S A²)`. By
`Learning.MDP.optQValue_add_lt_optValue_of_forall_lt_abs_optQValue_sub`, every state then has a
unique optimal action, whose optimal action value exceeds that of every other action by more than
this separation. [LWCGC24, Lemma 6] has the separation `ξ δ (1 - γ) / (3 S A²)`. -/
theorem le_measureReal_pi_cond_Icc_forall_lt_abs_optQValue_ofDet_sub [Fintype 𝓢] [Fintype 𝓐]
    [Nonempty 𝓢] [Nonempty 𝓐] (r : 𝓢 × 𝓐 → ℝ) (hγ : γ < 1) {ξ δ : ℝ} (hξ : 0 < ξ) (hδ : 0 ≤ δ) :
    1 - δ ≤ (Measure.pi fun _ : 𝓢 × 𝓐 ↦ volume[|Icc 0 ξ]).real {ζ | ∀ s a₁ a₂, a₁ ≠ a₂ →
      ξ * δ * (1 - γ) / (2 * (Fintype.card 𝓢 * Fintype.card 𝓐 ^ 2)) <
        |(ofDet P (r + ζ) (measurable_of_finite _)).optQValue γ (s, a₁) -
          (ofDet P (r + ζ) (measurable_of_finite _)).optQValue γ (s, a₂)|} := by
  have hIcc : volume (Icc 0 ξ) = ENNReal.ofReal ξ := by simp
  have : IsProbabilityMeasure (volume[|Icc 0 ξ]) :=
    cond_isProbabilityMeasure_of_finite (by simp [hIcc, hξ]) (by simp [hIcc])
  -- the uniform law on `[0, ξ]` has density `ξ⁻¹`
  have hν (t : Set ℝ) : volume[|Icc 0 ξ] t ≤ ENNReal.ofReal ξ⁻¹ * volume t := by
    rw [cond_apply measurableSet_Icc, hIcc, ENNReal.ofReal_inv_of_pos hξ]
    gcongr
    exact inter_subset_right
  have h := le_measureReal_pi_forall_lt_abs_optQValue_ofDet_sub P r hγ (fun _ ↦ hν) hδ
  have heq : δ * (1 - γ) / (2 * ξ⁻¹ * (Fintype.card 𝓢 * Fintype.card 𝓐 ^ 2)) =
      ξ * δ * (1 - γ) / (2 * (Fintype.card 𝓢 * Fintype.card 𝓐 ^ 2)) := by
    field_simp
  simpa only [heq] using h

end TieBreaking

end Learning.MDP
