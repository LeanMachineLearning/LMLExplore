/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.SpecificLimits.Normed
public import LMLExplore.Probability.Kernel.Dobrushin

/-!
# The Poisson equation of a uniformly ergodic kernel

For a Markov kernel `κ : Kernel α α` and a bounded measurable function `f`, the *Poisson
equation* asks for a bounded measurable `g` and a constant `c` with `g - κ g = f - c`, where
`κ g = x ↦ ∫ g dκ x`. A solution turns the additive functional `∑ k < n, (f (X k) - c)` of a chain
with kernel `κ` into a martingale plus the bounded term `g (X 0) - g (X n)`, which is how laws of
large numbers and concentration bounds for Markov chains are derived from those for martingales
(`MarkovChain/Poisson.lean`).

Let `π` be an invariant probability measure of `κ`, and suppose `δ(κ ^ m) < 1` for some `m`,
where `δ` is the Dobrushin coefficient. Then the deviations `κ ^ n f - π f` decay geometrically:
`‖κ ^ n f - π f‖ ≤ δ(κ ^ m) ^ (n / m) osc f`, where `osc f = sup f - inf f`. Their series
`g = ∑ n, (κ ^ n f - π f)` converges in the Banach space of bounded measurable functions, with
`‖g‖ ≤ m osc f / (1 - δ(κ ^ m))`, and solves the Poisson equation with `c = π f`. Conversely, every
bounded solution `(u, c)` of the equation has `c = π f` and `u = g + b` for a constant `b`: the
bounded harmonic functions of `κ`, those with `κ h = h`, are constant.

## Main definitions

* `ProbabilityTheory.Kernel.poissonSolution κ π f`: the bounded measurable function
  `∑' n, (κ ^ n f - (∫ f dπ) • 1)`.

## Main statements

* `ProbabilityTheory.Kernel.norm_integralCLM_pow_sub_smul_one_le`: the deviation bound
  `‖κ ^ n f - π f‖ ≤ δ(κ ^ n) osc f`.
* `ProbabilityTheory.Kernel.hasSum_poissonSolution`: the series defining the solution converges.
* `ProbabilityTheory.Kernel.norm_poissonSolution_le`: `‖g‖ ≤ m osc f / (1 - δ(κ ^ m))`.
* `ProbabilityTheory.Kernel.poissonSolution_sub_integralCLM`: `g - κ g = f - π f`.
* `ProbabilityTheory.Kernel.exists_eq_smul_one_of_integralCLM_eq`: bounded harmonic functions are
  constant.
* `ProbabilityTheory.Kernel.Invariant.eq_integral_of_sub_integralCLM_eq`: the constant of every
  bounded solution is the invariant mean, for any invariant probability measure.
* `ProbabilityTheory.Kernel.eq_integral_and_exists_eq_poissonSolution_add`: uniqueness of the
  bounded solutions up to constants.

## References

* [S. Meyn and R. L. Tweedie, *Markov chains and stochastic stability*, 2nd edition, 2009][MT09],
  Chapter 17
-/

public section

open MeasureTheory Filter Topology LMLExplore
open scoped ENNReal lp

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} [IsMarkovKernel κ]
  {π : Measure α} [IsProbabilityMeasure π] {m : ℕ}

/-! ### Harmonic functions -/

/-- **Bounded harmonic functions are constant.** If `δ(κ ^ m) < 1` for some `m`, every bounded
measurable function `h` with `κ h = h` is constant. -/
theorem exists_eq_smul_one_of_integralCLM_eq (hm : dobrushinCoeff (κ ^ m) < 1)
    {h : boundedMeasurable α} (hh : κ.integralCLM h = h) :
    ∃ c : ℝ, h = c • 1 := by
  refine boundedMeasurable.orderUnitOsc_one_eq_zero_iff.1
    (le_antisymm ?_ (orderUnitOsc_nonneg _ _))
  -- `osc h = osc (κ ^ n h) ≤ δ(κ ^ n) osc h`, and `δ(κ ^ n) → 0`
  have hle (n : ℕ) : orderUnitOsc 1 h ≤ dobrushinCoeff (κ ^ n) * orderUnitOsc 1 h := by
    have hpow : (κ ^ n).integralCLM h = h := by
      induction n with
      | zero => exact integralCLM_pow_zero h
      | succ n ih => rw [integralCLM_pow_succ, ih, hh]
    simpa [hpow] using orderUnitOsc_integralCLM_le (κ := κ ^ n) h
  have hlim : Tendsto (fun n ↦ dobrushinCoeff (κ ^ n) * orderUnitOsc 1 h) atTop (𝓝 0) := by
    simpa using (tendsto_dobrushinCoeff_pow κ hm).mul_const (orderUnitOsc 1 h)
  exact ge_of_tendsto' hlim hle

/-! ### Geometric decay of the deviations -/

/-- **Decay of the deviations from the invariant mean.** For an invariant probability measure `π`
of `κ`, the `n`-step averages `κ ^ n f` are within `δ(κ ^ n) osc f` of the constant `∫ f dπ` in
sup norm. -/
theorem norm_integralCLM_pow_sub_smul_one_le (hπ : κ.Invariant π) (f : boundedMeasurable α)
    (n : ℕ) :
    ‖(κ ^ n).integralCLM f - (∫ x, (f : ℓ^∞(α, ℝ)) x ∂π) • 1‖ ≤
      dobrushinCoeff (κ ^ n) * orderUnitOsc 1 f := by
  have hc : 0 ≤ dobrushinCoeff (κ ^ n) * orderUnitOsc 1 f :=
    mul_nonneg (dobrushinCoeff_nonneg _) (orderUnitOsc_nonneg _ _)
  refine boundedMeasurable.norm_le_of_forall_le hc fun x ↦ ?_
  -- `∫ f dπ = ∫ (κ ^ n f) dπ` by invariance, and the values of `κ ^ n f` differ by at most
  -- `δ(κ ^ n) osc f`
  set F := ((κ ^ n).integralCLM f : ℓ^∞(α, ℝ))
  have hF : ∫ y, F y ∂π = ∫ y, (f : ℓ^∞(α, ℝ)) y ∂π := (hπ.pow n).integral_integralCLM f
  have hdiff : F x - ∫ y, F y ∂π = ∫ y, (F x - F y) ∂π := by
    rw [integral_sub (integrable_const _) (boundedMeasurable.integrable _ _), integral_const,
      probReal_univ, one_smul]
  have hle : |∫ y, (F x - F y) ∂π| ≤ dobrushinCoeff (κ ^ n) * orderUnitOsc 1 f := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (.of_forall fun y ↦ ?_)).trans_eq
      (by rw [probReal_univ, mul_one])
    rw [Real.norm_eq_abs]
    simpa only [F, integralCLM_apply] using abs_integral_sub_integral_le_dobrushinCoeff_mul
      (boundedMeasurable.measurable f) (boundedMeasurable.sub_apply_le_orderUnitOsc_one f) x y
  rw [boundedMeasurable.sub_smul_one_apply, ← hF]
  exact hdiff ▸ hle

/-- If `δ(κ ^ 0) < 1`, every bounded measurable function has oscillation zero: `κ ^ 0` is the
identity kernel, which contracts no oscillation unless all of them vanish. -/
private lemma orderUnitOsc_eq_zero_of_dobrushinCoeff_pow_zero_lt_one
    (hm : dobrushinCoeff (κ ^ 0) < 1) (f : boundedMeasurable α) :
    orderUnitOsc 1 f = 0 := by
  have h := orderUnitOsc_integralCLM_le (κ := κ ^ 0) f
  rw [integralCLM_pow_zero] at h
  nlinarith [orderUnitOsc_nonneg (1 : boundedMeasurable α) f]

/-- The terms of the series defining the solution of the Poisson equation are bounded by
`δ(κ ^ m) ^ (n / m) osc f`. -/
private lemma norm_integralCLM_pow_sub_smul_one_le_pow_div (hπ : κ.Invariant π)
    (f : boundedMeasurable α) (m n : ℕ) :
    ‖(κ ^ n).integralCLM f - (∫ x, (f : ℓ^∞(α, ℝ)) x ∂π) • 1‖ ≤
      dobrushinCoeff (κ ^ m) ^ (n / m) * orderUnitOsc 1 f :=
  (norm_integralCLM_pow_sub_smul_one_le hπ f n).trans
    (mul_le_mul_of_nonneg_right (dobrushinCoeff_pow_le_pow_div κ m n) (orderUnitOsc_nonneg _ _))

/-! ### The solution of the Poisson equation -/

/-- The *solution of the Poisson equation* `g - κ g = f - π f` for a bounded measurable `f`: the
series `∑' n, (κ ^ n f - (∫ f dπ) • 1)` of bounded measurable functions. It converges when `π` is
an invariant probability measure of `κ` and `δ(κ ^ m) < 1` for some `m`
(`hasSum_poissonSolution`); it is then the solution (`poissonSolution_sub_integralCLM`), unique up
to constants (`eq_integral_and_exists_eq_poissonSolution_add`), and bounded by
`m osc f / (1 - δ(κ ^ m))` (`norm_poissonSolution_le`). -/
noncomputable def poissonSolution (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α)
    (f : boundedMeasurable α) : boundedMeasurable α :=
  ∑' n, ((κ ^ n).integralCLM f - (∫ x, (f : ℓ^∞(α, ℝ)) x ∂π) • 1)

lemma poissonSolution_def (κ : Kernel α α) [IsMarkovKernel κ] (π : Measure α)
    (f : boundedMeasurable α) :
    poissonSolution κ π f = ∑' n, ((κ ^ n).integralCLM f - (∫ x, (f : ℓ^∞(α, ℝ)) x ∂π) • 1) :=
  (rfl)

/-- If `δ(κ ^ m) < 1` for some `m` and `π` is an invariant probability measure of `κ`, the series
`∑ n, (κ ^ n f - (∫ f dπ) • 1)` defining the solution of the Poisson equation converges
absolutely. -/
theorem summable_norm_integralCLM_pow_sub_smul_one (hπ : κ.Invariant π)
    (hm : dobrushinCoeff (κ ^ m) < 1) (f : boundedMeasurable α) :
    Summable fun n ↦ ‖(κ ^ n).integralCLM f - (∫ x, (f : ℓ^∞(α, ℝ)) x ∂π) • 1‖ := by
  -- pass to `m + 1 ≠ 0`, whose Dobrushin coefficient is at most that of `κ ^ m`
  have hm' : dobrushinCoeff (κ ^ (m + 1)) < 1 :=
    (antitone_dobrushinCoeff_pow κ (Nat.le_succ m)).trans_lt hm
  refine .of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_integralCLM_pow_sub_smul_one_le_pow_div hπ f (m + 1)) ?_
  exact ((hasSum_pow_div_of_lt_one (dobrushinCoeff_nonneg _) hm').summable).mul_right _

/-- If `δ(κ ^ m) < 1` for some `m` and `π` is an invariant probability measure of `κ`, the series
`∑ n, (κ ^ n f - (∫ f dπ) • 1)` converges, in sup norm, to `poissonSolution κ π f`. -/
theorem hasSum_poissonSolution (hπ : κ.Invariant π) (hm : dobrushinCoeff (κ ^ m) < 1)
    (f : boundedMeasurable α) :
    HasSum (fun n ↦ (κ ^ n).integralCLM f - (∫ x, (f : ℓ^∞(α, ℝ)) x ∂π) • 1)
      (poissonSolution κ π f) :=
  (summable_norm_integralCLM_pow_sub_smul_one hπ hm f).of_norm.hasSum

/-- **Bound on the solution of the Poisson equation.** If `δ(κ ^ m) < 1` and `π` is an invariant
probability measure of `κ`, then `g = poissonSolution κ π f` satisfies
`‖g‖ ≤ m osc f / (1 - δ(κ ^ m))`. -/
theorem norm_poissonSolution_le (hπ : κ.Invariant π) (hm : dobrushinCoeff (κ ^ m) < 1)
    (f : boundedMeasurable α) :
    ‖poissonSolution κ π f‖ ≤ m * orderUnitOsc 1 f / (1 - dobrushinCoeff (κ ^ m)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm₀
  · -- for `m = 0`, every bounded measurable function is constant, so that the terms vanish
    have hf := orderUnitOsc_eq_zero_of_dobrushinCoeff_pow_zero_lt_one hm f
    have h0 : poissonSolution κ π f = 0 := by
      rw [poissonSolution_def]
      refine (tsum_congr fun n ↦ norm_le_zero_iff.1 ?_).trans tsum_zero
      simpa [hf] using norm_integralCLM_pow_sub_smul_one_le hπ f n
    simp [h0]
  have : NeZero m := ⟨hm₀.ne'⟩
  have hρ := hasSum_pow_div_of_lt_one (dobrushinCoeff_nonneg (κ ^ m)) hm (m := m)
  refine ((hasSum_poissonSolution hπ hm f).norm_le_of_bounded (hρ.mul_right (orderUnitOsc 1 f))
    (norm_integralCLM_pow_sub_smul_one_le_pow_div hπ f m)).trans_eq ?_
  ring

/-- **The Poisson equation.** If `δ(κ ^ m) < 1` and `π` is an invariant probability measure of
`κ`, then `g = poissonSolution κ π f` solves `g - κ g = f - (∫ f dπ) • 1`. -/
theorem poissonSolution_sub_integralCLM (hπ : κ.Invariant π) (hm : dobrushinCoeff (κ ^ m) < 1)
    (f : boundedMeasurable α) :
    poissonSolution κ π f - κ.integralCLM (poissonSolution κ π f) =
      f - (∫ x, (f : ℓ^∞(α, ℝ)) x ∂π) • 1 := by
  have hsum := hasSum_poissonSolution hπ hm f
  set c := ∫ x, (f : ℓ^∞(α, ℝ)) x ∂π
  -- `κ` maps the `n`-th term of the series to the `(n + 1)`-th one
  have hshift (n : ℕ) : κ.integralCLM ((κ ^ n).integralCLM f - c • 1) =
      (κ ^ (n + 1)).integralCLM f - c • 1 := by
    rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul, integralCLM_one,
      integralCLM_pow_succ]
  rw [← (κ.integralCLM.hasSum hsum).tsum_eq, tsum_congr hshift, ← hsum.tsum_eq,
    hsum.summable.tsum_eq_zero_add,
    integralCLM_pow_zero, add_sub_cancel_right]

/-- **The constant of the Poisson equation.** If `π` is an invariant probability measure of `κ`,
every bounded solution `(u, c)` of `u - κ u = f - c • 1` has `c = ∫ f dπ`: integrating the equation
against `π` gives `0 = ∫ f dπ - c`. -/
theorem Invariant.eq_integral_of_sub_integralCLM_eq (hπ : κ.Invariant π)
    {f u : boundedMeasurable α} {c : ℝ} (hu : u - κ.integralCLM u = f - c • 1) :
    c = ∫ x, (f : ℓ^∞(α, ℝ)) x ∂π := by
  have h := congrArg (fun v : boundedMeasurable α ↦ ∫ x, (v : ℓ^∞(α, ℝ)) x ∂π) hu
  simp only [boundedMeasurable.coeFn_sub, Pi.sub_apply, boundedMeasurable.sub_smul_one_apply] at h
  rw [integral_sub (boundedMeasurable.integrable _ _) (boundedMeasurable.integrable _ _),
    hπ.integral_integralCLM, sub_self,
    integral_sub (boundedMeasurable.integrable _ _) (integrable_const c), integral_const,
    probReal_univ, one_smul] at h
  linarith

/-- **Uniqueness for the Poisson equation.** If `δ(κ ^ m) < 1` and `π` is an invariant probability
measure of `κ`, every bounded solution `(u, c)` of `u - κ u = f - c • 1` has `c = ∫ f dπ`, and `u`
differs from `poissonSolution κ π f` by a constant. -/
theorem eq_integral_and_exists_eq_poissonSolution_add (hπ : κ.Invariant π)
    (hm : dobrushinCoeff (κ ^ m) < 1) {f u : boundedMeasurable α} {c : ℝ}
    (hu : u - κ.integralCLM u = f - c • 1) :
    c = ∫ x, (f : ℓ^∞(α, ℝ)) x ∂π ∧ ∃ b : ℝ, u = poissonSolution κ π f + b • 1 := by
  have hc := hπ.eq_integral_of_sub_integralCLM_eq hu
  refine ⟨hc, ?_⟩
  -- the difference of two solutions is harmonic, hence constant
  obtain ⟨b, hb⟩ := exists_eq_smul_one_of_integralCLM_eq hm
    (h := u - poissonSolution κ π f) (by
      have hg := poissonSolution_sub_integralCLM hπ hm f
      rw [← hc] at hg
      rw [ContinuousLinearMap.map_sub]
      linear_combination (norm := abel_nf) hg - hu)
  exact ⟨b, by rw [← hb, add_sub_cancel]⟩

end ProbabilityTheory.Kernel
