/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.Probability.Moments.Variance
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Variances under a kernel, and of bounded random variables

The variance `Var[X; η b]` of a measurable real function `X` under the laws of an s-finite kernel
`η` is a measurable function of the starting point `b`, as the integrals of `X` and of `X ^ 2` are.
This is what makes one-step variances such as `κ (V ^ 2) - (κ V) ^ 2` of a Markov kernel `κ`
themselves integrable against kernels, in variance recursions of Markov chains.

A real random variable with `|X| ≤ B` almost surely has variance at most `B ^ 2`, the symmetric
case of Mathlib's `ProbabilityTheory.variance_le_sq_of_bounded`.

The standard deviation `√Var[X; μ]` is a seminorm on square-integrable random variables: the
Cauchy–Schwarz inequality `cov[X, Y] ^ 2 ≤ Var[X] Var[Y]` gives the triangle inequality
`√Var[X + Y] ≤ √Var[X] + √Var[Y]`. In particular, two random variables within `D` of each other
almost surely have standard deviations within `D`. This compares the variance of an unknown
function, such as the optimal value of a Markov decision process, with the variance of a nearby
computable one, and transfers a Bernstein-type bound on the deviation `∫ Y dμ - ∫ Y dν` of the
nearby function `Y` to `X`.

## Main statements

* `Measurable.variance_kernel`: `b ↦ Var[X; η b]` is measurable.
* `ProbabilityTheory.variance_le_sq_of_abs_le`: `|X| ≤ B` almost surely gives `Var[X; μ] ≤ B ^ 2`.
* `ProbabilityTheory.sq_covariance_le_variance_mul_variance`: the Cauchy–Schwarz inequality
  `cov[X, Y; μ] ^ 2 ≤ Var[X; μ] * Var[Y; μ]`.
* `ProbabilityTheory.sqrt_variance_add_le`: `√Var[X + Y; μ] ≤ √Var[X; μ] + √Var[Y; μ]`.
* `ProbabilityTheory.sqrt_variance_le_sqrt_variance_add_of_abs_sub_le`: if `|X - Y| ≤ D` almost
  surely, then `√Var[X; μ] ≤ √Var[Y; μ] + D`.
* `ProbabilityTheory.abs_integral_sub_integral_le_of_abs_sub_le`: a Bernstein-type bound
  `|∫ Y dμ - ∫ Y dν| ≤ a √Var[Y; μ] + b` transfers to every `X` uniformly within `d` of `Y`, at
  the cost of `(2 + a) d`.
-/

public section

open MeasureTheory ProbabilityTheory

variable {β δ : Type*} {mβ : MeasurableSpace β} {mδ : MeasurableSpace δ}

/-- The variance of a measurable real function under the laws of an s-finite kernel is a
measurable function of the starting point. -/
theorem Measurable.variance_kernel {η : Kernel β δ} [IsSFiniteKernel η] {X : δ → ℝ}
    (hX : Measurable X) :
    Measurable fun b ↦ Var[X; η b] := by
  simp only [variance, evariance]
  have h_mean : Measurable fun b ↦ ∫ z, X z ∂(η b) :=
    hX.stronglyMeasurable.integral_kernel.measurable
  refine ENNReal.measurable_toReal.comp (Measurable.lintegral_kernel_prod_right'
    (f := fun p : β × δ ↦ ‖X p.2 - ∫ z, X z ∂(η p.1)‖ₑ ^ 2) ?_)
  exact ((hX.comp measurable_snd).sub (h_mean.comp measurable_fst)).eNorm.pow_const 2

namespace ProbabilityTheory

section FiniteMeasure

variable {μ : Measure β} [IsFiniteMeasure μ] {X Y : β → ℝ}

/-- **The Cauchy–Schwarz inequality for the covariance**: for square-integrable real random
variables `X` and `Y` under a finite measure, `cov[X, Y; μ] ^ 2 ≤ Var[X; μ] * Var[Y; μ]`. -/
theorem sq_covariance_le_variance_mul_variance (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] ^ 2 ≤ Var[X; μ] * Var[Y; μ] := by
  -- the quadratic `t ↦ Var[t • X + Y] = Var[X] t ^ 2 + 2 cov[X, Y] t + Var[Y]` is nonnegative
  have h (t : ℝ) : 0 ≤ Var[X; μ] * (t * t) + 2 * cov[X, Y; μ] * t + Var[Y; μ] := by
    have h₀ := variance_nonneg (t • X + Y) μ
    rw [variance_add (hX.const_smul t) hY, variance_smul, covariance_smul_left] at h₀
    linear_combination h₀
  have h_discrim := discrim_le_zero h
  rw [discrim] at h_discrim
  linear_combination h_discrim / 4

/-- **The triangle inequality for the standard deviation**: for square-integrable real random
variables `X` and `Y` under a finite measure, `√Var[X + Y; μ] ≤ √Var[X; μ] + √Var[Y; μ]`. -/
theorem sqrt_variance_add_le (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    √Var[X + Y; μ] ≤ √Var[X; μ] + √Var[Y; μ] := by
  have hcov : cov[X, Y; μ] ≤ √Var[X; μ] * √Var[Y; μ] := by
    rw [← Real.sqrt_mul (variance_nonneg X μ)]
    exact (le_abs_self _).trans (Real.abs_le_sqrt (sq_covariance_le_variance_mul_variance hX hY))
  rw [Real.sqrt_le_left (by positivity), variance_add hX hY, add_sq,
    Real.sq_sqrt (variance_nonneg X μ), Real.sq_sqrt (variance_nonneg Y μ)]
  linarith

end FiniteMeasure

variable {μ : Measure β} [IsProbabilityMeasure μ] {X Y : β → ℝ} {B : ℝ}

/-- A real random variable bounded by `B` in absolute value almost surely has variance at most
`B ^ 2`. -/
theorem variance_le_sq_of_abs_le (hX : AEMeasurable X μ) (hXB : ∀ᵐ b ∂μ, |X b| ≤ B) :
    Var[X; μ] ≤ B ^ 2 :=
  (variance_le_sq_of_bounded (a := -B) (b := B) (hXB.mono fun _ ↦ abs_le.1) hX).trans_eq
    (by ring)

/-- Two square-integrable real random variables within `D` of each other almost surely have
standard deviations within `D`: `√Var[X; μ] ≤ √Var[Y; μ] + D`. -/
theorem sqrt_variance_le_sqrt_variance_add_of_abs_sub_le (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    {D : ℝ} (hD : ∀ᵐ b ∂μ, |X b - Y b| ≤ D) :
    √Var[X; μ] ≤ √Var[Y; μ] + D := by
  have hD₀ : 0 ≤ D := by
    obtain ⟨b, hb⟩ := hD.exists
    exact (abs_nonneg _).trans hb
  have h := sqrt_variance_add_le hY (hX.sub hY)
  rw [add_sub_cancel] at h
  refine h.trans ?_
  gcongr
  rw [Real.sqrt_le_left hD₀]
  exact variance_le_sq_of_abs_le (hX.sub hY).aemeasurable hD

/-- **Perturbation of a Bernstein-type bound.** If `Y` satisfies the Bernstein-type bound
`|∫ Y dμ - ∫ Y dν| ≤ a √Var[Y; μ] + b`, with `a ≥ 0`, between two probability measures, and `X` is
uniformly within `d` of `Y`, then `|∫ X dμ - ∫ X dν| ≤ a √Var[X; μ] + (2 + a) d + b`. -/
theorem abs_integral_sub_integral_le_of_abs_sub_le {ν : Measure β} [IsProbabilityMeasure ν]
    (hXμ : MemLp X 2 μ) (hYμ : MemLp Y 2 μ) (hXν : Integrable X ν) (hYν : Integrable Y ν)
    {a b d : ℝ} (ha : 0 ≤ a) (hXY : ∀ x, |X x - Y x| ≤ d)
    (hY : |∫ x, Y x ∂μ - ∫ x, Y x ∂ν| ≤ a * √Var[Y; μ] + b) :
    |∫ x, X x ∂μ - ∫ x, X x ∂ν| ≤ a * √Var[X; μ] + (2 + a) * d + b := by
  -- the integrals of `X` and `Y` against a probability measure are within `d`
  have h_int {ρ : Measure β} [IsProbabilityMeasure ρ] (hX : Integrable X ρ)
      (hY : Integrable Y ρ) : |∫ x, X x ∂ρ - ∫ x, Y x ∂ρ| ≤ d := by
    rw [← integral_sub hX hY]
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := ρ) (f := fun x ↦ X x - Y x)
        (.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le (hXY x))
  have hμ := h_int (hXμ.integrable one_le_two) (hYμ.integrable one_le_two)
  have hν := h_int hXν hYν
  have hσ : a * √Var[Y; μ] ≤ a * (√Var[X; μ] + d) :=
    mul_le_mul_of_nonneg_left (sqrt_variance_le_sqrt_variance_add_of_abs_sub_le hYμ hXμ
      (ae_of_all _ fun x ↦ by rw [abs_sub_comm]; exact hXY x)) ha
  calc |∫ x, X x ∂μ - ∫ x, X x ∂ν|
      = |(∫ x, X x ∂μ - ∫ x, Y x ∂μ) - (∫ x, X x ∂ν - ∫ x, Y x ∂ν) +
          (∫ x, Y x ∂μ - ∫ x, Y x ∂ν)| := by ring_nf
    _ ≤ |∫ x, X x ∂μ - ∫ x, Y x ∂μ| + |∫ x, X x ∂ν - ∫ x, Y x ∂ν| +
          |∫ x, Y x ∂μ - ∫ x, Y x ∂ν| := (abs_add_le _ _).trans (by gcongr; exact abs_sub _ _)
    _ ≤ a * √Var[X; μ] + (2 + a) * d + b := by linarith

end ProbabilityTheory
