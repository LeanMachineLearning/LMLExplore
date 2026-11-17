/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalLExpectation
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.SpecialFunctions.Exp
import TauCeti.MeasureTheory.Function.ConditionalLExpectation
import LMLExplore.Analysis.Normed.Group.Basic
import LMLExplore.Analysis.Normed.Ring.Pi
import LMLExplore.Probability.Martingale.L2Convergence

/-!
# Asynchronous stochastic approximation

On a finite index type `ι`, the asynchronous stochastic approximation recursion is
`x (t + 1) i = x t i + α t i * (F (x t) i - x t i + w t i)`: each coordinate `i` moves towards
the `i`-th coordinate of `F (x t)` with its own step size `α t i ∈ [0, 1]`, corrupted by a
martingale-difference noise `w t i` whose conditional variance may grow quadratically with the
past iterates. Coordinates that are not updated at time `t` have `α t i = 0`. This is the
recursion of asynchronous Q-learning and of tabular temporal-difference learning, with `F` a
Bellman operator. We prove, after Tsitsiklis [Tsi94] and without delays:
* if `‖F y / v‖ ≤ β * ‖y / v‖ + D` with `β < 1`, for the maximum norm weighted by positive
  weights `v`, then the iterates are almost surely bounded [Tsi94, Theorem 1];
* if `F` is a pseudo-contraction towards `x'` for such a norm,
  `‖(F y - x') / v‖ ≤ β * ‖(y - x') / v‖`, and `∑ t, α t i = ∞`, then the iterates converge to
  `x'` almost surely [Tsi94, Theorem 3].

The step sizes are adapted, with `∑ t, α t i ^ 2 ≤ C` almost surely for a deterministic `C`.

## Main statements

* `LMLExplore.le_add_two_mul_of_le_one_sub_mul_add`,
  `LMLExplore.eventually_le_add_of_le_one_sub_mul_add`: deterministic comparisons for the
  averaging recursion `u (t + 1) ≤ (1 - α t) * u t + α t * (c + ξ t)`, on a finite window and
  asymptotically.
* `LMLExplore.abs_le_add_two_mul_of_eq_one_sub_mul_add`,
  `LMLExplore.eventually_abs_le_add_of_eq_one_sub_mul_add`: their two-sided forms, for the
  recursion `u (t + 1) = (1 - α t) * u t + α t * (f t + ξ t)` with `|f t| ≤ c`.
* `LMLExplore.ae_bddAbove_range_norm_of_norm_div_le_mul_add`: the iterates are bounded.
* `LMLExplore.ae_tendsto_of_norm_sub_div_le_mul`: the iterates converge to the fixed point.
* `LMLExplore.ae_tendsto_of_averaging`: with `F` constant, the coordinates are independent
  averaging recursions, which converge to the constant.

## Implementation notes

The maximum norm weighted by `v` is written `‖y / v‖`, with the sup norm of `ι → ℝ` and the
coordinatewise quotient. The conditional second moment of the noise is the conditional
expectation `condLExp` of `‖w t i‖ₑ ^ 2`, bounded by `A + B * ⨆ τ ≤ t, ‖x τ‖ₑ ^ 2`; the noise is
also assumed integrable, so that the condition `E[w t i | ℱ t] = 0` is meaningful.

The weighted noise sums converge by
`LMLExplore.ae_exists_tendsto_sum_mul_of_condExp_eq_zero`, applied to the noise multiplied by
bounded adapted factors. The boundedness theorem rescales the noise by a scale of the iterates,
an adapted nondecreasing process that stays put as long as the weighted norm of the iterates is
at most `q` times the scale and jumps to that norm otherwise, as in the proof of
[Tsi94, Theorem 1]. The rescaled noise has a bounded conditional second moment, so its weighted
sums converge; once their tails are below `(q - 1) / 2` and the scale has jumped, the comparison
on finite windows keeps the iterates below `q` times the scale forever, so the scale stops moving.
For the convergence theorem, the noise is truncated where the bounded iterates would leave a ball,
and the asymptotic comparison turns an eventual bound `D` on the weighted distance to `x'` into
the eventual bound `β * D + η`.

## References

* [Tsi94] J. N. Tsitsiklis, *Asynchronous stochastic approximation and Q-learning*, Machine
  Learning 16 (1994), 185–202.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal

namespace LMLExplore

/-! ### Deterministic comparisons for the averaging recursion -/

section Deterministic

variable {α ξ u : ℕ → ℝ} {c s : ℝ}

/-- **Comparison for the averaging recursion, on a finite window.** Let `0 ≤ α t ≤ 1` and let the
partial sums of `α t * ξ t` stay within `δ` of `s` on the window `[t₀, T]`. If
`u (t + 1) ≤ (1 - α t) * u t + α t * (c + ξ t)` on the window and `u t₀ ≤ c`, then
`u t ≤ c + 2 δ` on the window. -/
theorem le_add_two_mul_of_le_one_sub_mul_add {δ : ℝ} {t₀ T : ℕ}
    (hα : ∀ t, t₀ ≤ t → t < T → α t ∈ Set.Icc (0 : ℝ) 1)
    (hS : ∀ t, t₀ ≤ t → t ≤ T → |∑ τ ∈ range t, α τ * ξ τ - s| ≤ δ) (hu₀ : u t₀ ≤ c)
    (hu : ∀ t, t₀ ≤ t → t < T → u (t + 1) ≤ (1 - α t) * u t + α t * (c + ξ t))
    {t : ℕ} (ht₀ : t₀ ≤ t) (htT : t ≤ T) :
    u t ≤ c + 2 * δ := by
  -- `z t = u t - c - (S t - s)` satisfies `z (t + 1) ≤ (1 - α t) z t - α t (S t - s)`
  suffices h : u t - c - (∑ τ ∈ range t, α τ * ξ τ - s) ≤ δ by
    linarith [(abs_le.1 (hS t ht₀ htT)).2]
  induction t, ht₀ using Nat.le_induction with
  | base => linarith [(abs_le.1 (hS t₀ le_rfl htT)).1]
  | succ t ht ih =>
    have htT' : t < T := htT
    obtain ⟨h0, h1⟩ := hα t ht htT'
    have hR := (abs_le.1 (hS t ht htT'.le)).1
    rw [sum_range_succ]
    nlinarith [mul_le_mul_of_nonneg_left (ih htT'.le) (sub_nonneg.2 h1), hu t ht htT',
      mul_le_mul_of_nonneg_left (neg_le.1 hR) h0]

/-- **Asymptotic comparison for the averaging recursion.** Let `0 ≤ α t ≤ 1` with
`∑ α t = ∞`, and let the partial sums of `α t * ξ t` converge. If eventually
`u (t + 1) ≤ (1 - α t) * u t + α t * (c + ξ t)`, then `u t ≤ c + η` eventually, for every
`η > 0`. -/
theorem eventually_le_add_of_le_one_sub_mul_add (hα : ∀ t, α t ∈ Set.Icc (0 : ℝ) 1)
    (hα_sum : Tendsto (fun T ↦ ∑ t ∈ range T, α t) atTop atTop)
    (hS : Tendsto (fun T ↦ ∑ t ∈ range T, α t * ξ t) atTop (𝓝 s))
    (hu : ∀ᶠ t in atTop, u (t + 1) ≤ (1 - α t) * u t + α t * (c + ξ t)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in atTop, u t ≤ c + η := by
  set S := fun T ↦ ∑ t ∈ range T, α t * ξ t
  set A := fun T ↦ ∑ t ∈ range T, α t
  have hR : ∀ᶠ t in atTop, |S t - s| ≤ η / 3 :=
    (hS.eventually (Metric.closedBall_mem_nhds s (ε := η / 3) (by positivity))).mono
      fun t ht ↦ by rwa [Real.dist_eq] at ht
  obtain ⟨t₁, ht₁⟩ := eventually_atTop.1 (hu.and hR)
  -- `p t = u t - c - (S t - s) - η / 3` decays at least like `exp (A t₁ - A t)`
  set p := fun t ↦ u t - c - (S t - s) - η / 3
  have hp : ∀ t, t₁ ≤ t → p t ≤ max (p t₁) 0 * Real.exp (A t₁ - A t) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => simp
    | succ t ht ih =>
      obtain ⟨h0, h1⟩ := hα t
      have hstep : p (t + 1) ≤ (1 - α t) * p t := by
        have hRt := (abs_le.1 (ht₁ t ht).2).1
        simp only [p, S, sum_range_succ]
        nlinarith [(ht₁ t ht).1]
      have hA : A (t + 1) = A t + α t := sum_range_succ _ _
      calc p (t + 1) ≤ (1 - α t) * p t := hstep
        _ ≤ (1 - α t) * (max (p t₁) 0 * Real.exp (A t₁ - A t)) :=
          mul_le_mul_of_nonneg_left ih (sub_nonneg.2 h1)
        _ ≤ Real.exp (-α t) * (max (p t₁) 0 * Real.exp (A t₁ - A t)) :=
          mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg _) (by positivity)
        _ = max (p t₁) 0 * Real.exp (A t₁ - A (t + 1)) := by
          rw [hA, mul_left_comm, ← Real.exp_add]
          ring_nf
  have hlim : Tendsto (fun t ↦ max (p t₁) 0 * Real.exp (A t₁ - A t)) atTop (𝓝 0) := by
    have : Tendsto (fun t ↦ A t₁ - A t) atTop atBot :=
      tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp hα_sum)
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul (max (p t₁) 0)
  filter_upwards [hlim.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < η / 3)), hR,
    eventually_ge_atTop t₁] with t h1 h2 h3
  have := hp t h3
  have := (abs_le.1 h2).2
  simp only [p] at *
  linarith

/-- Two-sided form of `le_add_two_mul_of_le_one_sub_mul_add`, for the recursion
`u (t + 1) = (1 - α t) * u t + α t * (f t + ξ t)` with `|f t| ≤ c` on the window. -/
theorem abs_le_add_two_mul_of_eq_one_sub_mul_add {f : ℕ → ℝ} {δ : ℝ} {t₀ T : ℕ}
    (hα : ∀ t, t₀ ≤ t → t < T → α t ∈ Set.Icc (0 : ℝ) 1)
    (hS : ∀ t, t₀ ≤ t → t ≤ T → |∑ τ ∈ range t, α τ * ξ τ - s| ≤ δ) (hu₀ : |u t₀| ≤ c)
    (hu : ∀ t, t₀ ≤ t → t < T → u (t + 1) = (1 - α t) * u t + α t * (f t + ξ t))
    (hf : ∀ t, t₀ ≤ t → t < T → |f t| ≤ c) {t : ℕ} (ht₀ : t₀ ≤ t) (htT : t ≤ T) :
    |u t| ≤ c + 2 * δ := by
  refine abs_le.2 ⟨?_, ?_⟩
  · have := le_add_two_mul_of_le_one_sub_mul_add (u := fun t ↦ -u t) (ξ := fun t ↦ -ξ t)
      (s := -s) (c := c) (δ := δ) hα (fun t h1 h2 ↦ ?_) (neg_le.1 (abs_le.1 hu₀).1)
      (fun t h1 h2 ↦ ?_) ht₀ htT
    · linarith
    · simpa [abs_sub_comm, sum_neg_distrib, ← sub_eq_neg_add] using hS t h1 h2
    · obtain ⟨h0, -⟩ := hα t h1 h2
      rw [hu t h1 h2]
      nlinarith [(abs_le.1 (hf t h1 h2)).1]
  · refine le_add_two_mul_of_le_one_sub_mul_add hα hS (abs_le.1 hu₀).2 (fun t h1 h2 ↦ ?_) ht₀ htT
    obtain ⟨h0, -⟩ := hα t h1 h2
    rw [hu t h1 h2]
    nlinarith [(abs_le.1 (hf t h1 h2)).2]

/-- Two-sided form of `eventually_le_add_of_le_one_sub_mul_add`, for the recursion
`u (t + 1) = (1 - α t) * u t + α t * (f t + ξ t)` with eventually `|f t| ≤ c`. -/
theorem eventually_abs_le_add_of_eq_one_sub_mul_add {f : ℕ → ℝ} (hα : ∀ t, α t ∈ Set.Icc (0 : ℝ) 1)
    (hα_sum : Tendsto (fun T ↦ ∑ t ∈ range T, α t) atTop atTop)
    (hS : Tendsto (fun T ↦ ∑ t ∈ range T, α t * ξ t) atTop (𝓝 s))
    (hu : ∀ t, u (t + 1) = (1 - α t) * u t + α t * (f t + ξ t))
    (hf : ∀ᶠ t in atTop, |f t| ≤ c) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in atTop, |u t| ≤ c + η := by
  have hS' : Tendsto (fun T ↦ ∑ t ∈ range T, α t * -ξ t) atTop (𝓝 (-s)) := by
    simpa [sum_neg_distrib] using hS.neg
  have h1 : ∀ᶠ t in atTop, u (t + 1) ≤ (1 - α t) * u t + α t * (c + ξ t) :=
    hf.mono fun t ht ↦ by
      rw [hu t]
      nlinarith [(abs_le.1 ht).2, (hα t).1]
  have h2 : ∀ᶠ t in atTop, -u (t + 1) ≤ (1 - α t) * -u t + α t * (c + -ξ t) :=
    hf.mono fun t ht ↦ by
      rw [hu t]
      nlinarith [(abs_le.1 ht).1, (hα t).1]
  filter_upwards [eventually_le_add_of_le_one_sub_mul_add hα hα_sum hS h1 hη,
    eventually_le_add_of_le_one_sub_mul_add (u := fun t ↦ -u t) hα hα_sum hS' h2 hη]
    with t h1 h2
  exact abs_le.2 ⟨by linarith, h1⟩

end Deterministic

/-! ### The scale of the iterates -/

section Scale

/-- The scale of a sequence `m`, a variant of the one in the proof of [Tsi94, Theorem 1]: it
starts at `max G₀ (m 0)`, stays put as long as `m t ≤ q * scale t`, and jumps to `m (t + 1)` when
this fails. -/
private noncomputable def scale (G₀ q : ℝ) (m : ℕ → ℝ) : ℕ → ℝ
  | 0 => max G₀ (m 0)
  | t + 1 => if m (t + 1) ≤ q * scale G₀ q m t then scale G₀ q m t else m (t + 1)

variable {G₀ q : ℝ} {m : ℕ → ℝ}

private lemma scale_zero (G₀ q : ℝ) (m : ℕ → ℝ) : scale G₀ q m 0 = max G₀ (m 0) := by
  rw [scale]

private lemma scale_succ (G₀ q : ℝ) (m : ℕ → ℝ) (t : ℕ) :
    scale G₀ q m (t + 1)
      = if m (t + 1) ≤ q * scale G₀ q m t then scale G₀ q m t else m (t + 1) := by
  rw [scale]

private lemma le_scale (hG₀ : 0 ≤ G₀) (hq : 1 ≤ q) (t : ℕ) : G₀ ≤ scale G₀ q m t := by
  induction t with
  | zero => exact (scale_zero G₀ q m).symm ▸ le_max_left _ _
  | succ t ih =>
    rw [scale_succ]
    split_ifs with h
    · exact ih
    · exact ih.trans ((le_mul_of_one_le_left (hG₀.trans ih) hq).trans (not_le.1 h).le)

private lemma monotone_scale (hG₀ : 0 ≤ G₀) (hq : 1 ≤ q) : Monotone (scale G₀ q m) := by
  refine monotone_nat_of_le_succ fun t ↦ ?_
  rw [scale_succ]
  split_ifs with h
  · exact le_rfl
  · exact (le_mul_of_one_le_left (hG₀.trans (le_scale hG₀ hq t)) hq).trans (not_le.1 h).le

private lemma le_mul_scale (hG₀ : 0 ≤ G₀) (hq : 1 ≤ q) (t : ℕ) : m t ≤ q * scale G₀ q m t := by
  cases t with
  | zero =>
    rw [scale_zero]
    exact (le_max_right _ _).trans
      (le_mul_of_one_le_left (hG₀.trans (le_max_left _ _)) hq)
  | succ t =>
    rw [scale_succ]
    split_ifs with h
    · exact h
    · have h0 : 0 ≤ m (t + 1) := (mul_nonneg (zero_le_one.trans hq)
        (hG₀.trans (le_scale hG₀ hq t))).trans (not_le.1 h).le
      exact le_mul_of_one_le_left h0 hq

private lemma scale_succ_eq_or (G₀ q : ℝ) (m : ℕ → ℝ) (t : ℕ) :
    scale G₀ q m (t + 1) = scale G₀ q m t ∨ m (t + 1) = scale G₀ q m (t + 1) := by
  rw [scale_succ]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma measurable_scale {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ}
    {m : ℕ → Ω → ℝ} (hm : ∀ t, Measurable[ℱ t] (m t)) (t : ℕ) :
    Measurable[ℱ t] fun ω ↦ scale G₀ q (fun τ ↦ m τ ω) t := by
  induction t with
  | zero =>
    simp_rw [scale_zero]
    exact measurable_const.max (hm 0)
  | succ t ih =>
    simp_rw [scale_succ]
    have ih' := ih.mono (ℱ.mono t.le_succ) le_rfl
    exact Measurable.ite (measurableSet_le (hm (t + 1)) (measurable_const.mul ih')) ih' (hm _)

end Scale

/-! ### Asynchronous stochastic approximation -/

section Asynchronous

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℕ mΩ} [Fintype ι]
  {x α w : ℕ → Ω → ι → ℝ} {A B : ℝ≥0} {C : ℝ}

/-- The noise of the asynchronous recursion, multiplied by adapted factors `φ t` with
`|φ t| ≤ b` and `|φ t| * ‖x τ‖ ≤ c` for `τ ≤ t`, has convergent weighted partial sums. -/
private lemma ae_exists_tendsto_sum_mul_mul [IsFiniteMeasure P] (hαm : Adapted ℱ α)
    (hα_sq : ∀ᵐ ω ∂P, ∀ i T, ∑ t ∈ range T, α t ω i ^ 2 ≤ C)
    (hwm : ∀ t, Measurable[ℱ (t + 1)] (w t)) (hw_int : ∀ t i, Integrable (fun ω ↦ w t ω i) P)
    (hw_mean : ∀ t i, P[fun ω ↦ w t ω i | ℱ t] =ᵐ[P] 0)
    (hw_var : ∀ t i, P⁻[fun ω ↦ ‖w t ω i‖ₑ ^ 2 | ℱ t] ≤ᵐ[P]
      fun ω ↦ A + B * ⨆ τ ≤ t, ‖x τ ω‖ₑ ^ 2)
    {φ : ℕ → Ω → ℝ} (hφ : Adapted ℱ φ) {b c : ℝ} (hφb : ∀ t ω, |φ t ω| ≤ b)
    (hφx : ∀ t ω τ, τ ≤ t → |φ t ω| * ‖x τ ω‖ ≤ c) (i : ι) :
    ∀ᵐ ω ∂P, ∃ s, Tendsto (fun T ↦ ∑ t ∈ range T, α t ω i * (φ t ω * w t ω i)) atTop (𝓝 s) := by
  refine ae_exists_tendsto_sum_mul_of_condExp_eq_zero (ℱ := ℱ) (α := fun t ω ↦ α t ω i)
    (ξ := fun t ω ↦ φ t ω * w t ω i)
    (K := (ENNReal.ofReal b ^ 2 * A + B * ENNReal.ofReal c ^ 2).toNNReal)
    (fun t ↦ (measurable_pi_apply i).comp (hαm t)) (fun t ↦ ?_) (fun t ↦ ?_) (fun t ↦ ?_)
    (hα_sq.mono fun ω hω T ↦ hω i T)
  · exact ((hφ t).mono (ℱ.mono t.le_succ) le_rfl).mul ((measurable_pi_apply i).comp (hwm t))
  · have hint : Integrable (φ t * fun ω ↦ w t ω i) P :=
      (hw_int t i).bdd_mul ((hφ t).mono (ℱ.le t) le_rfl).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ by simpa [Real.norm_eq_abs] using hφb t ω)
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (hφ t).stronglyMeasurable hint
      (hw_int t i), hw_mean t i] with ω h1 h2
    exact h1.trans (by simp [h2])
  · have hG : Measurable[ℱ t] fun ω ↦ ‖φ t ω‖ₑ ^ 2 := (measurable_eNorm.pow_const 2).comp (hφ t)
    have hZ : AEMeasurable (fun ω ↦ ‖w t ω i‖ₑ ^ 2) P :=
      ((measurable_eNorm.pow_const 2).comp
        ((measurable_pi_apply i).comp ((hwm t).mono (ℱ.le _) le_rfl))).aemeasurable
    have hprod : (fun ω ↦ ‖φ t ω * w t ω i‖ₑ ^ 2)
        = (fun ω ↦ ‖φ t ω‖ₑ ^ 2) * fun ω ↦ ‖w t ω i‖ₑ ^ 2 := by
      ext ω
      simp [eNorm_mul, mul_pow]
    filter_upwards [TauCeti.MeasureTheory.condLExp_mul_of_measurable_left (ℱ.le t) hG hZ,
      hw_var t i] with ω h1 h2
    have hφω : ‖φ t ω‖ₑ ≤ ENNReal.ofReal b := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hφb t ω)
    have hsup : ‖φ t ω‖ₑ ^ 2 * ⨆ τ ≤ t, ‖x τ ω‖ₑ ^ 2 ≤ ENNReal.ofReal c ^ 2 := by
      simp_rw [ENNReal.mul_iSup]
      refine iSup₂_le fun τ hτ ↦ ?_
      rw [← mul_pow, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      gcongr
      simpa [Real.norm_eq_abs] using hφx t ω τ hτ
    rw [hprod, h1, Pi.mul_apply]
    calc ‖φ t ω‖ₑ ^ 2 * P⁻[fun ω ↦ ‖w t ω i‖ₑ ^ 2 | ℱ t] ω
        ≤ ‖φ t ω‖ₑ ^ 2 * (A + B * ⨆ τ ≤ t, ‖x τ ω‖ₑ ^ 2) := mul_le_mul_right h2 _
      _ = ‖φ t ω‖ₑ ^ 2 * A + B * (‖φ t ω‖ₑ ^ 2 * ⨆ τ ≤ t, ‖x τ ω‖ₑ ^ 2) := by ring
      _ ≤ ENNReal.ofReal b ^ 2 * A + B * ENNReal.ofReal c ^ 2 := by gcongr
      _ = _ := (ENNReal.coe_toNNReal (by finiteness)).symm

/-- The deterministic part of the boundedness theorem, along one trajectory: if the noise
rescaled by the scale of the iterates has convergent weighted partial sums, the scale is
bounded. -/
private lemma exists_scale_le {F : (ι → ℝ) → ι → ℝ} {v : ι → ℝ} {β D G₀ q : ℝ}
    {x α w : ℕ → ι → ℝ}
    (hx : ∀ t i, x (t + 1) i = x t i + α t i * (F (x t) i - x t i + w t i))
    (hα : ∀ t i, α t i ∈ Set.Icc (0 : ℝ) 1) (hv : ∀ i, 0 < v i) (hβ : 0 ≤ β) (hD : 0 ≤ D)
    (hq : 1 < q) (hG₀ : 0 < G₀) (hρ : β * q + D / G₀ ≤ 1)
    (hF : ∀ y, ‖F y / v‖ ≤ β * ‖y / v‖ + D)
    (hS : ∀ i, ∃ s, Tendsto (fun T ↦ ∑ t ∈ range T,
      α t i * ((v i * scale G₀ q (fun τ ↦ ‖x τ / v‖) t)⁻¹ * w t i)) atTop (𝓝 s)) :
    ∃ g, ∀ t, scale G₀ q (fun τ ↦ ‖x τ / v‖) t ≤ g := by
  set N := fun τ ↦ ‖x τ / v‖
  set G := scale G₀ q N
  have hG₀G : ∀ t, G₀ ≤ G t := le_scale hG₀.le hq.le
  have hNG : ∀ t, N t ≤ q * G t := le_mul_scale hG₀.le hq.le
  choose s hs using hS
  -- after some time `T₀`, the rescaled noise sums stay within `(q - 1) / 2` of their limits
  obtain ⟨T₀, hT₀⟩ : ∃ T₀, ∀ t ≥ T₀, ∀ i,
      |∑ τ ∈ range t, α τ i * ((v i * G τ)⁻¹ * w τ i) - s i| ≤ (q - 1) / 2 := by
    refine eventually_atTop.1 (eventually_all.2 fun i ↦ ?_)
    refine ((hs i).eventually (Metric.closedBall_mem_nhds (s i) (ε := (q - 1) / 2)
      (by linarith))).mono fun t ht ↦ ?_
    rwa [Real.dist_eq] at ht
  -- from a time `t₀ ≥ T₀` with `N t₀ ≤ G t₀`, the iterates never leave the ball of radius
  -- `q * G t₀`, so the scale never moves again
  have key (t₀ : ℕ) (hT : T₀ ≤ t₀) (hN : N t₀ ≤ G t₀) (n : ℕ) :
      ∀ τ, t₀ ≤ τ → τ ≤ t₀ + n → G τ = G t₀ := by
    set g := G t₀
    have hg : 0 < g := hG₀.trans_le (hG₀G t₀)
    induction n with
    | zero =>
      intro τ h1 h2
      obtain rfl : τ = t₀ := by omega
      rfl
    | succ n ih =>
      intro τ h1 h2
      rcases Nat.lt_or_ge τ (t₀ + n + 1) with h | h
      · exact ih τ h1 (by omega)
      obtain rfl : τ = t₀ + n + 1 := le_antisymm h2 h
      have hgt : G (t₀ + n) = g := ih _ (by omega) le_rfl
      suffices hN' : N (t₀ + n + 1) ≤ q * G (t₀ + n) by
        rw [← hgt]
        simp [G, scale_succ, hN']
      rw [hgt]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
      -- the coordinate `i`, rescaled by `v i * g`, follows the averaging recursion
      have hvg : 0 < v i * g := mul_pos (hv i) hg
      have hcmp := abs_le_add_two_mul_of_eq_one_sub_mul_add (α := fun τ ↦ α τ i)
        (ξ := fun τ ↦ (v i * G τ)⁻¹ * w τ i) (u := fun τ ↦ x τ i / (v i * g))
        (f := fun τ ↦ F (x τ) i / (v i * g)) (s := s i) (c := 1) (t₀ := t₀) (T := t₀ + n + 1)
        (fun τ _ _ ↦ hα τ i) (fun τ hτ _ ↦ hT₀ τ (hT.trans hτ) i) ?_ ?_ ?_ (by omega) le_rfl
      · have : |x (t₀ + n + 1) i / v i| ≤ q * g := by
          rw [show x (t₀ + n + 1) i / (v i * g) = x (t₀ + n + 1) i / v i / g by
            rw [div_div], abs_div, abs_of_pos hg, div_le_iff₀ hg] at hcmp
          linarith
        simpa [abs_div, abs_of_pos (hv i)] using this
      · rw [abs_div, abs_of_pos hvg, div_le_one hvg]
        calc |x t₀ i| = v i * |x t₀ i / v i| := by
              rw [abs_div, abs_of_pos (hv i), mul_div_cancel₀ _ (hv i).ne']
          _ ≤ v i * g := mul_le_mul_of_nonneg_left
              ((abs_div_le_norm_div _ _ i).trans hN) (hv i).le
      · intro τ hτ₁ hτ₂
        have hGτ : G τ = g := ih τ hτ₁ (by omega)
        simp only [hGτ, hx τ i]
        field_simp
        ring
      · intro τ hτ₁ hτ₂
        have hGτ : G τ = g := ih τ hτ₁ (by omega)
        rw [abs_div, abs_of_pos hvg, div_le_one hvg]
        have hFτ : |F (x τ) i / v i| ≤ g := by
          refine (abs_div_le_norm_div _ _ i).trans ((hF _).trans ?_)
          have h1 : β * N τ ≤ β * q * g := by
            rw [mul_assoc, ← hGτ]
            exact mul_le_mul_of_nonneg_left (hNG τ) hβ
          have h2 : D ≤ (1 - β * q) * g := by
            have : D / G₀ ≤ 1 - β * q := by linarith
            have h0 : 0 ≤ 1 - β * q := (div_nonneg hD hG₀.le).trans this
            rw [div_le_iff₀ hG₀] at this
            exact this.trans (mul_le_mul_of_nonneg_left (hG₀G t₀) h0)
          linarith
        calc |F (x τ) i| = v i * |F (x τ) i / v i| := by
              rw [abs_div, abs_of_pos (hv i), mul_div_cancel₀ _ (hv i).ne']
          _ ≤ v i * g := mul_le_mul_of_nonneg_left hFτ (hv i).le
  -- either the scale moves after `T₀`, and then stops, or it never moves after `T₀`
  by_cases h : ∃ t₀, T₀ ≤ t₀ ∧ N t₀ ≤ G t₀
  · obtain ⟨t₀, hT, hN⟩ := h
    refine ⟨G t₀, fun t ↦ ?_⟩
    rcases le_total t t₀ with ht | ht
    · exact monotone_scale hG₀.le hq.le ht
    · exact (key t₀ hT hN (t - t₀) t ht (by omega)).le
  · push Not at h
    have hconst : ∀ n, G (T₀ + n) = G T₀ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rcases scale_succ_eq_or G₀ q N (T₀ + n) with h' | h'
        · exact h'.trans ih
        · exact absurd h'.le (h _ (by omega)).not_ge
    refine ⟨G T₀, fun t ↦ ?_⟩
    rcases le_total t T₀ with ht | ht
    · exact monotone_scale hG₀.le hq.le ht
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
      exact (hconst n).le

/-- **Boundedness of asynchronous stochastic approximation** [Tsi94, Theorem 1]. On a finite
index type `ι`, let `x (t + 1) i = x t i + α t i * (F (x t) i - x t i + w t i)`, with:
* adapted iterates and adapted step sizes `α t i ∈ [0, 1]`, with `∑ t, α t i ^ 2 ≤ C` almost
  surely;
* a noise `w t`, measurable for `ℱ (t + 1)`, with integrable coordinates, `E[w t i | ℱ t] = 0`
  and `E[w t i ^ 2 | ℱ t] ≤ A + B * max_{τ ≤ t} ‖x τ‖ ^ 2`, the latter in the sense of `condLExp`
  and with the maximum norm `‖x τ‖`;
* `‖F y / v‖ ≤ β * ‖y / v‖ + D` with `β < 1`, for the maximum norm `‖y / v‖ = max_i |y i| / v i`
  weighted by positive weights `v i`.

Then the iterates are almost surely bounded. -/
theorem ae_bddAbove_range_norm_of_norm_div_le_mul_add [IsFiniteMeasure P]
    {F : (ι → ℝ) → ι → ℝ} {v : ι → ℝ} {β D : ℝ}
    (hx : ∀ t ω i, x (t + 1) ω i = x t ω i + α t ω i * (F (x t ω) i - x t ω i + w t ω i))
    (hxm : Adapted ℱ x) (hαm : Adapted ℱ α) (hα : ∀ t ω i, α t ω i ∈ Set.Icc (0 : ℝ) 1)
    (hα_sq : ∀ᵐ ω ∂P, ∀ i T, ∑ t ∈ range T, α t ω i ^ 2 ≤ C)
    (hwm : ∀ t, Measurable[ℱ (t + 1)] (w t)) (hw_int : ∀ t i, Integrable (fun ω ↦ w t ω i) P)
    (hw_mean : ∀ t i, P[fun ω ↦ w t ω i | ℱ t] =ᵐ[P] 0)
    (hw_var : ∀ t i, P⁻[fun ω ↦ ‖w t ω i‖ₑ ^ 2 | ℱ t] ≤ᵐ[P]
      fun ω ↦ A + B * ⨆ τ ≤ t, ‖x τ ω‖ₑ ^ 2)
    (hv : ∀ i, 0 < v i) (hβ : β < 1) (hF : ∀ y, ‖F y / v‖ ≤ β * ‖y / v‖ + D) :
    ∀ᵐ ω ∂P, BddAbove (Set.range fun t ↦ ‖x t ω‖) := by
  -- constants: `β' ≥ 0`, `D' ≥ 0`, the jump factor `q > 1` and the least scale `G₀`
  set β' := max β 0
  set D' := max D 0
  have hβ' : β' < 1 := max_lt hβ one_pos
  have hβ'0 : 0 ≤ β' := le_max_right _ _
  have hD' : 0 ≤ D' := le_max_right _ _
  have hF' (y : ι → ℝ) : ‖F y / v‖ ≤ β' * ‖y / v‖ + D' :=
    (hF y).trans (add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      (le_max_left _ _))
  set q := 2 / (1 + β')
  set G₀ := 2 * D' / (1 - β') + 1
  have h1β : 0 < 1 - β' := sub_pos.2 hβ'
  have hq : 1 < q := (one_lt_div (by positivity)).2 (by linarith)
  have hG₀ : 0 < G₀ := by positivity
  have hρ : β' * q + D' / G₀ ≤ 1 := by
    have h1 : D' / G₀ ≤ (1 - β') / 2 := by
      rw [div_le_iff₀ hG₀]
      have : (1 - β') / 2 * G₀ = D' + (1 - β') / 2 := by
        simp only [G₀]
        field_simp
      linarith
    have h2 : β' * q = 2 * β' / (1 + β') := by simp only [q]; ring
    have h3 : 2 * β' / (1 + β') ≤ 1 - (1 - β') / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  -- the noise, rescaled by the scale of the iterates, has convergent weighted partial sums
  set N : ℕ → Ω → ℝ := fun t ω ↦ ‖x t ω / v‖
  have hdiv : Measurable fun y : ι → ℝ ↦ y / v :=
    measurable_pi_iff.2 fun i ↦ by
      simpa using (measurable_pi_apply (X := fun _ : ι ↦ ℝ) i).div_const (v i)
  have hNm (t : ℕ) : Measurable[ℱ t] (N t) := continuous_norm.measurable.comp (hdiv.comp (hxm t))
  set G : ℕ → Ω → ℝ := fun t ω ↦ scale G₀ q (fun τ ↦ N τ ω) t
  have hGm (t : ℕ) : Measurable[ℱ t] (G t) := measurable_scale hNm t
  have hG₀G (t : ℕ) (ω : Ω) : G₀ ≤ G t ω := le_scale hG₀.le hq.le t
  have hnoise (i : ι) : ∀ᵐ ω ∂P, ∃ s, Tendsto (fun T ↦ ∑ t ∈ range T,
      α t ω i * ((v i * G t ω)⁻¹ * w t ω i)) atTop (𝓝 s) := by
    refine ae_exists_tendsto_sum_mul_mul hαm hα_sq hwm hw_int hw_mean hw_var
      (φ := fun t ω ↦ (v i * G t ω)⁻¹) (b := (v i * G₀)⁻¹) (c := ‖v‖ * q / v i)
      (fun t ↦ (measurable_const.mul (hGm t)).inv) (fun t ω ↦ ?_) (fun t ω τ hτ ↦ ?_) i
    · have hGt : 0 < G t ω := hG₀.trans_le (hG₀G t ω)
      rw [abs_of_pos (inv_pos.2 (mul_pos (hv i) hGt))]
      exact inv_anti₀ (mul_pos (hv i) hG₀) (mul_le_mul_of_nonneg_left (hG₀G t ω) (hv i).le)
    · have hGt : 0 < G t ω := hG₀.trans_le (hG₀G t ω)
      rw [abs_of_pos (inv_pos.2 (mul_pos (hv i) hGt)), inv_mul_le_iff₀ (mul_pos (hv i) hGt)]
      calc ‖x τ ω‖ ≤ ‖v‖ * N τ ω := norm_le_norm_mul_norm_div hv _
        _ ≤ ‖v‖ * (q * G t ω) := mul_le_mul_of_nonneg_left
            ((le_mul_scale (m := fun τ ↦ N τ ω) hG₀.le hq.le τ).trans
            (mul_le_mul_of_nonneg_left (monotone_scale hG₀.le hq.le hτ) (by linarith)))
            (norm_nonneg _)
        _ = v i * G t ω * (‖v‖ * q / v i) := by field_simp [(hv i).ne']
  filter_upwards [ae_all_iff.2 hnoise] with ω hω
  obtain ⟨g, hg⟩ := exists_scale_le (x := fun t ↦ x t ω) (α := fun t ↦ α t ω)
    (w := fun t ↦ w t ω) (fun t i ↦ hx t ω i) (fun t i ↦ hα t ω i) hv hβ'0 hD' hq hG₀ hρ hF' hω
  refine ⟨‖v‖ * (q * g), ?_⟩
  rintro _ ⟨t, rfl⟩
  calc ‖x t ω‖ ≤ ‖v‖ * N t ω := norm_le_norm_mul_norm_div hv _
    _ ≤ ‖v‖ * (q * g) := mul_le_mul_of_nonneg_left ((le_mul_scale hG₀.le hq.le t).trans
        (mul_le_mul_of_nonneg_left (hg t) (by linarith))) (norm_nonneg _)

/-- The deterministic part of the convergence theorem, along one bounded trajectory: if the
noise has convergent weighted partial sums, the iterates converge to the fixed point. -/
private lemma tendsto_of_norm_sub_div_le_mul {F : (ι → ℝ) → ι → ℝ} {v x' : ι → ℝ} {β : ℝ}
    {x α w : ℕ → ι → ℝ}
    (hx : ∀ t i, x (t + 1) i = x t i + α t i * (F (x t) i - x t i + w t i))
    (hα : ∀ t i, α t i ∈ Set.Icc (0 : ℝ) 1)
    (hα_sum : ∀ i, Tendsto (fun T ↦ ∑ t ∈ range T, α t i) atTop atTop)
    (hv : ∀ i, 0 < v i) (hβ0 : 0 ≤ β) (hβ : β < 1)
    (hF : ∀ y, ‖(F y - x') / v‖ ≤ β * ‖(y - x') / v‖)
    (hS : ∀ i, ∃ s, Tendsto (fun T ↦ ∑ t ∈ range T, α t i * ((v i)⁻¹ * w t i)) atTop (𝓝 s))
    (hbdd : BddAbove (Set.range fun t ↦ ‖x t‖)) :
    Tendsto x atTop (𝓝 x') := by
  set e := fun t ↦ ‖(x t - x') / v‖
  choose s hs using hS
  -- one round: if eventually `e t ≤ D`, then eventually `e t ≤ β D + η`
  have hstep (D : ℝ) (hD : ∀ᶠ t in atTop, e t ≤ D) (η : ℝ) (hη : 0 < η) :
      ∀ᶠ t in atTop, e t ≤ β * D + η := by
    have hD0 : 0 ≤ D := by
      obtain ⟨t, ht⟩ := hD.exists
      exact (norm_nonneg _).trans ht
    have hi (i : ι) : ∀ᶠ t in atTop, |(x t i - x' i) / v i| ≤ β * D + η := by
      refine eventually_abs_le_add_of_eq_one_sub_mul_add (α := fun t ↦ α t i)
        (ξ := fun t ↦ (v i)⁻¹ * w t i) (f := fun t ↦ (F (x t) i - x' i) / v i) (hα · i)
        (hα_sum i) (hs i) (fun t ↦ ?_) (hD.mono fun t ht ↦ ?_) hη
      · simp only [hx t i]
        field_simp [(hv i).ne']
        ring
      · have := abs_div_le_norm_div (F (x t) - x') v i
        simp only [Pi.sub_apply] at this
        exact this.trans ((hF _).trans (mul_le_mul_of_nonneg_left ht hβ0))
    filter_upwards [eventually_all.2 hi] with t ht
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
    simpa [Real.norm_eq_abs, abs_div] using ht i
  -- iterating the rounds with the contraction factor `β₁ = (1 + β) / 2`
  obtain ⟨R, hR⟩ := hbdd
  set D₀ := (R + ‖x'‖) * ‖v⁻¹‖
  have he0 (t : ℕ) : e t ≤ D₀ :=
    calc e t = ‖(x t - x') * v⁻¹‖ := by simp only [e, div_eq_mul_inv]
      _ ≤ ‖x t - x'‖ * ‖v⁻¹‖ := norm_mul_le _ _
      _ ≤ D₀ := mul_le_mul_of_nonneg_right
          ((norm_sub_le _ _).trans (add_le_add_left (hR ⟨t, rfl⟩) _)) (norm_nonneg _)
  have hD₀ : 0 ≤ D₀ := (norm_nonneg _).trans (he0 0)
  set β₁ := (1 + β) / 2
  have hβ₁ : β₁ < 1 := by simp only [β₁]; linarith
  have hβ₁0 : 0 ≤ β₁ := by positivity
  have hlim (η : ℝ) (hη : 0 < η) : ∀ᶠ t in atTop, e t ≤ η := by
    have hk (k : ℕ) : ∀ᶠ t in atTop, e t ≤ max (β₁ ^ k * D₀) η := by
      induction k with
      | zero => exact Eventually.of_forall fun t ↦ (he0 t).trans (by simp)
      | succ k ih =>
        set D := max (β₁ ^ k * D₀) η
        have hDη : η ≤ D := le_max_right _ _
        filter_upwards [hstep D ih ((1 - β) * η / 2) (by nlinarith)] with t ht
        calc e t ≤ β * D + (1 - β) * η / 2 := ht
          _ ≤ β₁ * D := by
            simp only [β₁]
            nlinarith
          _ = max (β₁ ^ (k + 1) * D₀) (β₁ * η) := by
            rw [mul_max_of_nonneg _ _ hβ₁0, pow_succ]
            ring_nf
          _ ≤ max (β₁ ^ (k + 1) * D₀) η :=
            max_le_max le_rfl (mul_le_of_le_one_left hη.le hβ₁.le)
    obtain ⟨k, hk'⟩ := exists_pow_lt_of_lt_one (div_pos hη (by linarith : 0 < D₀ + 1)) hβ₁
    filter_upwards [hk k] with t ht
    refine ht.trans (max_le ?_ le_rfl)
    rw [lt_div_iff₀ (by linarith)] at hk'
    nlinarith [pow_nonneg hβ₁0 k]
  have he : Tendsto e atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun t ↦ ha.trans_le (norm_nonneg _),
      fun a ha ↦ (hlim (a / 2) (by positivity)).mono fun t ht ↦ ht.trans_lt (by linarith)⟩
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun t ↦ norm_nonneg _)
    (fun t ↦ norm_le_norm_mul_norm_div hv _) ?_)
  simpa using he.const_mul ‖v‖

/-- **Convergence of asynchronous stochastic approximation** [Tsi94, Theorem 3]. On a finite
index type `ι`, let `x (t + 1) i = x t i + α t i * (F (x t) i - x t i + w t i)`, with:
* adapted iterates and adapted step sizes `α t i ∈ [0, 1]`, with `∑ t, α t i = ∞` and
  `∑ t, α t i ^ 2 ≤ C` almost surely;
* a noise `w t`, measurable for `ℱ (t + 1)`, with integrable coordinates, `E[w t i | ℱ t] = 0`
  and `E[w t i ^ 2 | ℱ t] ≤ A + B * max_{τ ≤ t} ‖x τ‖ ^ 2`, the latter in the sense of `condLExp`
  and with the maximum norm `‖x τ‖`;
* `F` a pseudo-contraction towards `x'` for a weighted maximum norm:
  `‖(F y - x') / v‖ ≤ β * ‖(y - x') / v‖` with `β < 1` and positive weights `v i`.

Then the iterates converge to `x'` almost surely. -/
theorem ae_tendsto_of_norm_sub_div_le_mul [IsFiniteMeasure P]
    {F : (ι → ℝ) → ι → ℝ} {v x' : ι → ℝ} {β : ℝ}
    (hx : ∀ t ω i, x (t + 1) ω i = x t ω i + α t ω i * (F (x t ω) i - x t ω i + w t ω i))
    (hxm : Adapted ℱ x) (hαm : Adapted ℱ α) (hα : ∀ t ω i, α t ω i ∈ Set.Icc (0 : ℝ) 1)
    (hα_sum : ∀ᵐ ω ∂P, ∀ i, Tendsto (fun T ↦ ∑ t ∈ range T, α t ω i) atTop atTop)
    (hα_sq : ∀ᵐ ω ∂P, ∀ i T, ∑ t ∈ range T, α t ω i ^ 2 ≤ C)
    (hwm : ∀ t, Measurable[ℱ (t + 1)] (w t)) (hw_int : ∀ t i, Integrable (fun ω ↦ w t ω i) P)
    (hw_mean : ∀ t i, P[fun ω ↦ w t ω i | ℱ t] =ᵐ[P] 0)
    (hw_var : ∀ t i, P⁻[fun ω ↦ ‖w t ω i‖ₑ ^ 2 | ℱ t] ≤ᵐ[P]
      fun ω ↦ A + B * ⨆ τ ≤ t, ‖x τ ω‖ₑ ^ 2)
    (hv : ∀ i, 0 < v i) (hβ : β < 1) (hF : ∀ y, ‖(F y - x') / v‖ ≤ β * ‖(y - x') / v‖) :
    ∀ᵐ ω ∂P, Tendsto (fun t ↦ x t ω) atTop (𝓝 x') := by
  set β' := max β 0
  have hF' (y : ι → ℝ) : ‖(F y - x') / v‖ ≤ β' * ‖(y - x') / v‖ :=
    (hF y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- the iterates are bounded
  have hbdd := ae_bddAbove_range_norm_of_norm_div_le_mul_add (D := (1 + β') * ‖x' / v‖) hx hxm
    hαm hα hα_sq hwm hw_int hw_mean hw_var hv (max_lt hβ one_pos) fun y ↦ by
      have hsub (z : ι → ℝ) : (z - x') / v = z / v - x' / v := by
        ext i
        simp [sub_div]
      refine norm_le_mul_norm_add_mul_norm_of_norm_sub_le_mul (le_max_right β 0) ?_
      simpa only [hsub] using hF' y
  -- the noise, truncated where the iterates leave the ball of radius `m`, converges
  have htrunc (m : ℕ) (i : ι) : ∀ᵐ ω ∂P, ∃ s, Tendsto (fun T ↦ ∑ t ∈ range T, α t ω i *
      ((if ∀ τ ≤ t, ‖x τ ω‖ ≤ m then (v i)⁻¹ else 0) * w t ω i)) atTop (𝓝 s) := by
    refine ae_exists_tendsto_sum_mul_mul hαm hα_sq hwm hw_int hw_mean hw_var (b := (v i)⁻¹)
      (c := m * (v i)⁻¹) (fun t ↦ Measurable.ite ?_ measurable_const measurable_const)
      (fun t ω ↦ ?_) (fun t ω τ hτ ↦ ?_) i
    · have : {ω | ∀ τ ≤ t, ‖x τ ω‖ ≤ m} = ⋂ τ, ⋂ (_ : τ ≤ t), {ω | ‖x τ ω‖ ≤ m} := by
        ext ω
        simp
      rw [this]
      exact MeasurableSet.iInter fun τ ↦ MeasurableSet.iInter fun hτ ↦ measurableSet_le
        (continuous_norm.measurable.comp ((hxm τ).mono (ℱ.mono hτ) le_rfl)) measurable_const
    · have := (inv_pos.2 (hv i)).le
      split_ifs <;> simp [abs_of_nonneg this, this]
    · have := (inv_pos.2 (hv i)).le
      split_ifs with h
      · rw [abs_of_nonneg this, mul_comm]
        exact mul_le_mul_of_nonneg_right (h τ hτ) this
      · simp only [abs_zero, zero_mul]
        positivity
  filter_upwards [hbdd, hα_sum, ae_all_iff.2 fun m ↦ ae_all_iff.2 (htrunc m)] with ω hb hs hω
  refine tendsto_of_norm_sub_div_le_mul (x := fun t ↦ x t ω) (α := fun t ↦ α t ω)
    (w := fun t ↦ w t ω) (fun t i ↦ hx t ω i) (fun t i ↦ hα t ω i) hs hv (le_max_right _ _)
    (max_lt hβ one_pos) hF' (fun i ↦ ?_) hb
  -- on this trajectory, the truncation is inactive at a large enough radius
  obtain ⟨R, hR⟩ := hb
  obtain ⟨m, hm⟩ := exists_nat_ge R
  have hin (t : ℕ) : ∀ τ ≤ t, ‖x τ ω‖ ≤ m := fun τ _ ↦ (hR ⟨τ, rfl⟩).trans hm
  have h (t : ℕ) : (if ∀ τ ≤ t, ‖x τ ω‖ ≤ m then (v i)⁻¹ else 0) = (v i)⁻¹ :=
    ite_eq_left_iff.2 fun h' ↦ absurd (hin t) h'
  simpa only [h] using hω m i

/-- The degenerate case of a constant map `F = c`: each coordinate is an
independent averaging recursion `x (t + 1) i = (1 - α t i) * x t i + α t i * (c i + w t i)`, and
the iterates converge to `c` almost surely. -/
theorem ae_tendsto_of_averaging [IsFiniteMeasure P] {c : ι → ℝ}
    (hx : ∀ t ω i, x (t + 1) ω i = x t ω i + α t ω i * (c i - x t ω i + w t ω i))
    (hxm : Adapted ℱ x) (hαm : Adapted ℱ α) (hα : ∀ t ω i, α t ω i ∈ Set.Icc (0 : ℝ) 1)
    (hα_sum : ∀ᵐ ω ∂P, ∀ i, Tendsto (fun T ↦ ∑ t ∈ range T, α t ω i) atTop atTop)
    (hα_sq : ∀ᵐ ω ∂P, ∀ i T, ∑ t ∈ range T, α t ω i ^ 2 ≤ C)
    (hwm : ∀ t, Measurable[ℱ (t + 1)] (w t)) (hw_int : ∀ t i, Integrable (fun ω ↦ w t ω i) P)
    (hw_mean : ∀ t i, P[fun ω ↦ w t ω i | ℱ t] =ᵐ[P] 0)
    (hw_var : ∀ t i, P⁻[fun ω ↦ ‖w t ω i‖ₑ ^ 2 | ℱ t] ≤ᵐ[P]
      fun ω ↦ A + B * ⨆ τ ≤ t, ‖x τ ω‖ₑ ^ 2) :
    ∀ᵐ ω ∂P, Tendsto (fun t ↦ x t ω) atTop (𝓝 c) :=
  ae_tendsto_of_norm_sub_div_le_mul (F := fun _ ↦ c) (v := 1) (β := 0) hx hxm hαm hα hα_sum
    hα_sq hwm hw_int hw_mean hw_var (fun _ ↦ one_pos) one_pos fun _ ↦ by simp

end Asynchronous

end LMLExplore
