/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.Probability.Moments.Variance
import Mathlib.Algebra.QuadraticDiscriminant
import LMLExplore.Algebra.Order.Ring.Abs
import LMLExplore.Analysis.Convex.Integral

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

The variance is also the least centred second moment, `Var[X; μ] ≤ ∫ (X - c) ^ 2 ∂μ`, which
transports variances: between two functions within `D` of each other, and between two laws on a
finite space at a cost proportional to their `ℓ¹` distance [MDJKLV21, Lemma 12]. These variance
transports, and `variance_le_integral_sub_sq` and `variance_le_mul_integral_sub`, are adapted from
the paper project Essakine2026Tight (`github.com/RemyDegenne/Essakine2026Tight`, file
`Essakine2026Tight/ForLMLExplore/Probability/Moments/VarianceTransport.lean`, by Rémy Degenne,
Apache 2.0).

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
* `ProbabilityTheory.variance_le_integral_sub_sq`: `Var[X; μ] ≤ ∫ (X - c) ^ 2 ∂μ`.
* `ProbabilityTheory.variance_le_mul_integral_sub`: `X ∈ [c, d]` gives
  `Var[X; μ] ≤ (d - c) (𝔼 X - c)`.
* `ProbabilityTheory.variance_le_two_mul_variance_add_mul_integral_abs_sub`: if `|X - Y| ≤ D`, then
  `Var[X; μ] ≤ 2 Var[Y; μ] + 2 D 𝔼 |X - Y|`.
* `ProbabilityTheory.variance_le_variance_add_mul_sum_abs_sub`: on a finite space, for `f` with
  values in `[c, d]`, `Var[f; ν] ≤ Var[f; μ] + (d - c) ^ 2 / 2 * ∑ x, |μ {x} - ν {x}|`.

## References

* [MDJKLV21] P. Ménard, O. D. Domingues, A. Jonsson, E. Kaufmann, E. Leurent and M. Valko,
  *Fast active learning for pure exploration in reinforcement learning*, ICML 2021.
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
  exact ((hX.comp measurable_snd).sub (h_mean.comp measurable_fst)).enorm.pow_const 2

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

/-- The variance is the least centred second moment: `Var[X; μ] ≤ ∫ (X - c) ^ 2 ∂μ` for every
`c`. -/
theorem variance_le_integral_sub_sq (hX : AEStronglyMeasurable X μ) (c : ℝ) :
    Var[X; μ] ≤ ∫ b, (X b - c) ^ 2 ∂μ := by
  have h := variance_le_expectation_sq (μ := μ) (X := fun b ↦ X b - c)
    (hX.sub aestronglyMeasurable_const)
  rwa [variance_sub_const hX c] at h

/-- A real random variable with values in `[c, d]` almost surely has variance at most
`(d - c) (𝔼 X - c)`; for `X ∈ [0, B]`, `Var[X; μ] ≤ B 𝔼 X`. This weakens the Bhatia–Davis
inequality `ProbabilityTheory.variance_le_sub_mul_sub`. -/
theorem variance_le_mul_integral_sub {c d : ℝ} (hX : AEMeasurable X μ)
    (h : ∀ᵐ b ∂μ, X b ∈ Set.Icc c d) : Var[X; μ] ≤ (d - c) * (μ[X] - c) := by
  have hm : μ[X] ∈ Set.Icc c d := integral_mem_Icc_of_ae_mem_Icc hX h
  refine (variance_le_sub_mul_sub h hX).trans ?_
  nlinarith [hm.1, hm.2]

/-- **Transport of the variance between two functions** [MDJKLV21, Lemma 12]: if `|X - Y| ≤ D`
almost surely, then `Var[X; μ] ≤ 2 Var[Y; μ] + 2 D 𝔼 |X - Y|`. The source states it for
functions with values in `[0, D]`. -/
theorem variance_le_two_mul_variance_add_mul_integral_abs_sub (hX : AEStronglyMeasurable X μ)
    (hY : MemLp Y 2 μ) {D : ℝ} (hD : ∀ᵐ b ∂μ, |X b - Y b| ≤ D) :
    Var[X; μ] ≤ 2 * Var[Y; μ] + 2 * D * ∫ b, |X b - Y b| ∂μ := by
  have hYc : Integrable (fun b ↦ (Y b - μ[Y]) ^ 2) μ := (hY.sub (memLp_const _)).integrable_sq
  have habs : Integrable (fun b ↦ |X b - Y b|) μ :=
    .of_bound (hX.sub hY.aestronglyMeasurable).norm D
      (hD.mono fun b hb ↦ by rwa [Real.norm_eq_abs, abs_abs])
  calc Var[X; μ] ≤ ∫ b, (X b - μ[Y]) ^ 2 ∂μ := variance_le_integral_sub_sq hX _
    _ ≤ ∫ b, (2 * D * |X b - Y b| + 2 * (Y b - μ[Y]) ^ 2) ∂μ := by
        refine integral_mono_of_nonneg (.of_forall fun _ ↦ sq_nonneg _)
          ((habs.const_mul _).add (hYc.const_mul _)) ?_
        filter_upwards [hD] with b hb
        have hsq : (X b - Y b) ^ 2 ≤ D * |X b - Y b| := by
          rw [← sq_abs]
          nlinarith [abs_nonneg (X b - Y b)]
        nlinarith [sq_nonneg (X b - Y b - (Y b - μ[Y]))]
    _ = 2 * Var[Y; μ] + 2 * D * ∫ b, |X b - Y b| ∂μ := by
        rw [integral_add (habs.const_mul _) (hYc.const_mul _), integral_const_mul,
          integral_const_mul, variance_eq_integral hY.aestronglyMeasurable.aemeasurable]
        ring

/-- **Transport of the variance between two laws on a finite space** [MDJKLV21, Lemma 12]: for
probability measures `μ` and `ν` on a finite type and `f` with values in `[c, d]`,
`Var[f; ν] ≤ Var[f; μ] + (d - c) ^ 2 / 2 * ∑ x, |μ {x} - ν {x}|`. This sharpens the factor `3` of
the source to `1 / 2`. -/
theorem variance_le_variance_add_mul_sum_abs_sub {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {μ ν : Measure ι} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : ι → ℝ} {c d : ℝ} (hf : ∀ x, f x ∈ Set.Icc c d) :
    Var[f; ν] ≤ Var[f; μ] + (d - c) ^ 2 / 2 * ∑ x, |μ.real {x} - ν.real {x}| := by
  have hfm : Measurable f := measurable_of_finite f
  set m := μ[f]
  have hm : m ∈ Set.Icc c d := integral_mem_Icc_of_ae_mem_Icc hfm.aemeasurable (.of_forall hf)
  -- the centred square `(f - m) ^ 2` has values in `[0, (d - c) ^ 2]`
  have hg x : (f x - m) ^ 2 ∈ Set.Icc 0 ((d - c) ^ 2) := sq_sub_mem_Icc_of_mem_Icc (hf x) hm
  have hsum (ρ : Measure ι) [IsProbabilityMeasure ρ] :
      ∫ x, (f x - m) ^ 2 ∂ρ = ∑ x, ρ.real {x} * (f x - m) ^ 2 := by
    simp [integral_fintype Integrable.of_finite]
  have hμ : Var[f; μ] = ∑ x, μ.real {x} * (f x - m) ^ 2 := by
    rw [variance_eq_integral hfm.aemeasurable, hsum]
  -- subtracting the constant `(d - c) ^ 2 / 2` does not change the difference of the sums
  have hshift : ∑ x, ν.real {x} * (f x - m) ^ 2 - ∑ x, μ.real {x} * (f x - m) ^ 2
      = ∑ x, (ν.real {x} - μ.real {x}) * ((f x - m) ^ 2 - (d - c) ^ 2 / 2) := by
    have h1 : ∑ x, ν.real {x} = ∑ x, μ.real {x} := by simp
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1]
    ring
  have hterm x : (ν.real {x} - μ.real {x}) * ((f x - m) ^ 2 - (d - c) ^ 2 / 2)
      ≤ (d - c) ^ 2 / 2 * |μ.real {x} - ν.real {x}| := by
    rw [abs_sub_comm]
    refine (le_abs_self _).trans ?_
    rw [abs_mul, mul_comm]
    gcongr
    rw [abs_le]
    constructor <;> linarith [(hg x).1, (hg x).2]
  calc Var[f; ν] ≤ ∑ x, ν.real {x} * (f x - m) ^ 2 := by
        rw [← hsum]; exact variance_le_integral_sub_sq hfm.aestronglyMeasurable m
    _ = Var[f; μ] + ∑ x, (ν.real {x} - μ.real {x}) * ((f x - m) ^ 2 - (d - c) ^ 2 / 2) := by
        rw [← hshift, hμ]; ring
    _ ≤ Var[f; μ] + (d - c) ^ 2 / 2 * ∑ x, |μ.real {x} - ν.real {x}| := by
        rw [Finset.mul_sum]
        exact add_le_add_right (Finset.sum_le_sum fun x _ ↦ hterm x) _

end ProbabilityTheory
