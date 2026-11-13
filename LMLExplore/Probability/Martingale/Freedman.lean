/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Exp
public import LMLExplore.Probability.Martingale.Basic
public import LMLExplore.Probability.Martingale.Ville
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Moments.Basic

/-!
# Freedman's inequality

Let `ℱ` be a filtration and `X` a real process with `X n` `ℱ (n + 1)`-measurable, square
integrable, with conditional mean `E[X n | ℱ n] ≤ 0` and bounded above by `b > 0`. Write
`S n = ∑ k < n, X k` for its partial sums and `W n = ∑ k < n, E[X k ^ 2 | ℱ k]` for its
predictable quadratic variation. Freedman's inequality bounds the probability that `S` ever
reaches a level `a` while `W` stays below `σ²` by `exp (-a ^ 2 / (2 (σ² + a b / 3)))`, the
Bernstein exponent with the variance replaced by `W`. These are the variance-aware deviation
bounds of martingales with bounded increments: unlike the Azuma–Hoeffding bound they scale with
the conditional variances rather than with the range.

The argument rests on Bennett's bound `exp (l x) ≤ 1 + l x + ψ_b(l) x ^ 2` for `x ≤ b`, with
`ψ_b(l) = (exp (l b) - 1 - l b) / b ^ 2` (`Real.exp_mul_le_one_add_mul_add_mul_sq`). Integrated
conditionally, it gives `E[exp (l X n - c E[X n ^ 2 | ℱ n]) | ℱ n] ≤ 1` for `l ≥ 0` and every
`c ≥ ψ_b(l)`. Then `exp (l S n - c W n)` is a nonnegative supermartingale started at `1`, and
Ville's inequality bounds the probability that it ever exceeds `exp x` by `exp (-x)`, for all
times simultaneously; in the terms of [HRMS20], `S` is sub-Poisson with scale `b` and variance
process `W`. Choosing `l = a / (σ² + a b / 3)` gives Freedman's inequality. With `l = η`
and `c = η ^ 2`, which dominates `ψ_{1/η}(η) = (e - 2) η ^ 2`, it gives the fixed-`η` form: if
`η X n ≤ 1`, then with probability at least `1 - δ`, `S n < η W n + log (1 / δ) / η` for every
`n`. For `|X n| ≤ b`, applying the fixed-`η` form along the grid `η = 2 ^ (-j) / b`, `j < K`, with
`K = ⌈log₄ N⌉ + 1`, and a union bound give the peeled form: with probability at least `1 - δ`,
`S n ≤ 3 √(W n ℓ) + 2 b ℓ` for every `n ≤ N`, where `ℓ = max 1 (log (K / δ))`. It adapts to the
unknown size of `W n` at the price of the logarithmic factor `K`.

## Main statements

* `LMLExplore.condExp_exp_mul_le`: Bennett's bound under a conditional expectation,
  `E[exp (l X) | m] ≤ 1 + l E[X | m] + ψ_b(l) E[X ^ 2 | m]` for `X ≤ b` and `l ≥ 0`.
* `LMLExplore.condExp_exp_mul_sub_mul_condExp_sq_le_one`: the one-step bound
  `E[exp (l X - c E[X ^ 2 | m]) | m] ≤ 1` for `X ≤ b`, `E[X | m] ≤ 0`, `l ≥ 0` and `c ≥ ψ_b(l)`.
* `LMLExplore.supermartingale_exp_mul_sum_sub_mul_sum_condExp_sq`: `exp (l S n - c W n)` is a
  supermartingale.
* `LMLExplore.measure_exists_le_mul_sum_sub_mul_sum_condExp_sq_le`: the time-uniform bound
  `P(∃ n, x ≤ l S n - c W n) ≤ exp (-x)`.
* `LMLExplore.measure_exists_le_sum_and_sum_condExp_sq_le_le`: **Freedman's inequality**
  `P(∃ n, a ≤ S n ∧ W n ≤ σ²) ≤ exp (-a ^ 2 / (2 (σ² + a b / 3)))` for `a, σ² ≥ 0`.
* `LMLExplore.measure_exists_mul_sum_condExp_sq_add_log_div_le_sum_le`: the fixed-`η` form
  `P(∃ n, η W n + log (1 / δ) / η ≤ S n) ≤ δ` for `η X n ≤ 1`.
* `LMLExplore.measure_exists_three_mul_sqrt_add_lt_sum_le`: the peeled form
  `P(∃ n ≤ N, 3 √(W n ℓ) + 2 b ℓ < S n) ≤ δ` for `|X n| ≤ b`.

## Implementation notes

The increments are indexed as in Mathlib's Azuma–Hoeffding inequality: `X n` is
`ℱ (n + 1)`-measurable and its conditional moments are taken given `ℱ n`. The statements need no
assumption on the measurable space, since the one-step bound is proved with the conditional
expectation rather than a conditional distribution. The upper bound `X n ≤ b` and the conditional
mean are only required almost surely.

## References

* [Fre75] D. A. Freedman, *On tail probabilities for martingales*, Annals of Probability 3 (1975),
  100–118.
* [BLM13] S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford
  University Press, 2013, Theorems 2.9 and 2.10.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Exercises 5.14 and 5.15.
* [HRMS20] S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, *Time-uniform Chernoff bounds via
  nonnegative supermartingales*, Probability Surveys 17 (2020), 257–317.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real
open scoped ENNReal

namespace LMLExplore

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Bennett's bound under a conditional expectation.** If `X ≤ b` almost surely with `b > 0` and
`X ^ 2` is integrable, then for `l ≥ 0`,
`E[exp (l X) | m] ≤ 1 + l E[X | m] + ψ_b(l) E[X ^ 2 | m]` almost surely, with
`ψ_b(l) = (exp (l b) - 1 - l b) / b ^ 2`. -/
theorem condExp_exp_mul_le [IsFiniteMeasure μ] (hm : m ≤ mΩ) {X : Ω → ℝ} {b l : ℝ} (hb : 0 < b)
    (hl : 0 ≤ l) (hX : AEStronglyMeasurable X μ) (hX2 : Integrable (fun ω ↦ X ω ^ 2) μ)
    (h_bdd : ∀ᵐ ω ∂μ, X ω ≤ b) :
    μ[fun ω ↦ exp (l * X ω) | m] ≤ᵐ[μ] fun ω ↦
      1 + l * μ[X | m] ω + (exp (l * b) - 1 - l * b) / b ^ 2 * μ[fun ω ↦ X ω ^ 2 | m] ω := by
  set ψ := (exp (l * b) - 1 - l * b) / b ^ 2 with hψ_def
  have hXint : Integrable X μ := ((memLp_two_iff_integrable_sq hX).2 hX2).integrable one_le_two
  have hQ₁ : Integrable ((fun _ ↦ (1 : ℝ)) + l • X) μ := (integrable_const 1).add (hXint.smul l)
  -- integrate `exp (l X) ≤ 1 + l X + ψ X ^ 2` conditionally, term by term
  have hle : μ[fun ω ↦ exp (l * X ω) | m] ≤ᵐ[μ]
      μ[(fun _ ↦ (1 : ℝ)) + l • X + ψ • fun ω ↦ X ω ^ 2 | m] := by
    refine condExp_mono (integrable_exp_mul_of_le l b hl hX.aemeasurable h_bdd)
      (hQ₁.add (hX2.smul ψ)) ?_
    filter_upwards [h_bdd] with ω hω
    simpa [hψ_def] using exp_mul_le_one_add_mul_add_mul_sq hb hl hω
  filter_upwards [hle, condExp_add hQ₁ (hX2.smul ψ) m,
    condExp_add (integrable_const (1 : ℝ)) (hXint.smul l) m, condExp_smul l X m,
    condExp_smul ψ (fun ω ↦ X ω ^ 2) m] with ω h h₁ h₂ h₃ h₄
  simpa only [h₁, Pi.add_apply, h₂, condExp_const hm, h₃, h₄, Pi.smul_apply, smul_eq_mul]
    using h

/-- If `X ≤ b` almost surely, then for `l, c ≥ 0` the exponent `l X - c E[X ^ 2 | m]` is at most
`l b` almost surely, so its exponential is integrable. -/
theorem integrable_exp_mul_sub_mul_condExp_sq [IsFiniteMeasure μ] (hm : m ≤ mΩ) {X : Ω → ℝ}
    {b l c : ℝ} (hl : 0 ≤ l) (hc : 0 ≤ c) (hX : AEStronglyMeasurable X μ)
    (h_bdd : ∀ᵐ ω ∂μ, X ω ≤ b) :
    Integrable (fun ω ↦ exp (l * X ω - c * μ[fun ω ↦ X ω ^ 2 | m] ω)) μ := by
  simpa using integrable_exp_mul_of_le 1 (l * b) zero_le_one
    ((hX.const_mul l).sub ((stronglyMeasurable_condExp.mono hm).aestronglyMeasurable.const_mul
      c)).aemeasurable (by
      filter_upwards [h_bdd, condExp_nonneg (μ := μ) (m := m)
        (ae_of_all _ fun ω ↦ sq_nonneg (X ω))] with ω hω hW
      simp only [Pi.sub_apply, Pi.zero_apply] at hW ⊢
      nlinarith [mul_le_mul_of_nonneg_left hω hl, mul_nonneg hc hW])

/-- **The one-step bound behind Freedman's inequality.** If `X ≤ b` almost surely with `b > 0`,
`X ^ 2` is integrable and `E[X | m] ≤ 0`, then for `l ≥ 0` and
`c ≥ ψ_b(l) = (exp (l b) - 1 - l b) / b ^ 2`,
`E[exp (l X - c E[X ^ 2 | m]) | m] ≤ 1` almost surely. -/
theorem condExp_exp_mul_sub_mul_condExp_sq_le_one [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) {X : Ω → ℝ} {b l c : ℝ} (hb : 0 < b) (hl : 0 ≤ l)
    (hc : (exp (l * b) - 1 - l * b) / b ^ 2 ≤ c) (hX : AEStronglyMeasurable X μ)
    (hX2 : Integrable (fun ω ↦ X ω ^ 2) μ) (h_mean : μ[X | m] ≤ᵐ[μ] 0)
    (h_bdd : ∀ᵐ ω ∂μ, X ω ≤ b) :
    μ[fun ω ↦ exp (l * X ω - c * μ[fun ω ↦ X ω ^ 2 | m] ω) | m] ≤ᵐ[μ] 1 := by
  set W := μ[fun ω ↦ X ω ^ 2 | m]
  have hc0 : 0 ≤ c := (exp_sub_one_sub_id_div_sq_nonneg (l * b) b).trans hc
  have hW0 : 0 ≤ᵐ[μ] W := condExp_nonneg (ae_of_all _ fun ω ↦ sq_nonneg (X ω))
  -- `exp (l X - c W)` is the `m`-measurable factor `exp (-c W)` times `exp (l X)`
  have h_eq : (fun ω ↦ exp (l * X ω - c * W ω)) =
      (fun ω ↦ exp (-(c * W ω))) * fun ω ↦ exp (l * X ω) := by
    ext ω
    rw [Pi.mul_apply, ← exp_add, neg_add_eq_sub]
  have hprod : Integrable ((fun ω ↦ exp (-(c * W ω))) * fun ω ↦ exp (l * X ω)) μ := by
    rw [← h_eq]
    exact integrable_exp_mul_sub_mul_condExp_sq hm hl hc0 hX h_bdd
  have hE : StronglyMeasurable[m] fun ω ↦ exp (-(c * W ω)) :=
    (stronglyMeasurable_condExp.measurable.const_mul c).neg.exp.stronglyMeasurable
  rw [h_eq]
  filter_upwards [condExp_mul_of_stronglyMeasurable_left hE hprod
      (integrable_exp_mul_of_le l b hl hX.aemeasurable h_bdd),
    condExp_exp_mul_le hm hb hl hX hX2 h_bdd, h_mean, hW0] with ω h₁ h₂ h₃ h₄
  rw [h₁, Pi.mul_apply, Pi.one_apply]
  -- `exp (-c W) (1 + l E[X | m] + ψ W) ≤ exp (-c W) (1 + c W) ≤ exp (-c W) exp (c W) = 1`
  calc exp (-(c * W ω)) * μ[fun ω ↦ exp (l * X ω) | m] ω
      ≤ exp (-(c * W ω)) * (1 + c * W ω) := by
        gcongr
        nlinarith [mul_le_mul_of_nonneg_right hc h₄, mul_nonpos_of_nonneg_of_nonpos hl h₃]
    _ ≤ exp (-(c * W ω)) * exp (c * W ω) := by
        gcongr
        linarith [add_one_le_exp (c * W ω)]
    _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]

section Process

variable {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ} {b l c : ℝ}

/-- **The exponential supermartingale of Freedman's inequality.** Let `X n` be
`ℱ (n + 1)`-measurable, with `X n ^ 2` integrable, `E[X n | ℱ n] ≤ 0` and `X n ≤ b` almost surely,
with `b > 0`. For `l ≥ 0` and `c ≥ (exp (l b) - 1 - l b) / b ^ 2`, the process
`exp (l ∑ k < n, X k - c ∑ k < n, E[X k ^ 2 | ℱ k])` is a supermartingale. -/
theorem supermartingale_exp_mul_sum_sub_mul_sum_condExp_sq [IsFiniteMeasure μ] (hb : 0 < b)
    (hl : 0 ≤ l) (hc : (exp (l * b) - 1 - l * b) / b ^ 2 ≤ c)
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n)) (hX2 : ∀ n, Integrable (fun ω ↦ X n ω ^ 2) μ)
    (h_mean : ∀ n, μ[X n | ℱ n] ≤ᵐ[μ] 0) (h_bdd : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ b) :
    Supermartingale (fun n ω ↦ exp (l * ∑ k ∈ range n, X k ω
      - c * ∑ k ∈ range n, μ[fun ω ↦ X k ω ^ 2 | ℱ k] ω)) ℱ μ := by
  have hc0 : 0 ≤ c := (exp_sub_one_sub_id_div_sq_nonneg (l * b) b).trans hc
  -- the rounds are `Z k = l X k - c E[X k ^ 2 | ℱ k]`
  have h_eq : (fun n ω ↦ exp (l * ∑ k ∈ range n, X k ω
      - c * ∑ k ∈ range n, μ[fun ω ↦ X k ω ^ 2 | ℱ k] ω)) = fun n ω ↦
      exp (∑ k ∈ range n, (l * X k ω - c * μ[fun ω ↦ X k ω ^ 2 | ℱ k] ω)) := by
    ext n ω
    rw [sum_sub_distrib, mul_sum, mul_sum]
  rw [h_eq]
  have hXm : ∀ n, AEStronglyMeasurable (X n) μ := fun n ↦
    ((hX n).mono (ℱ.le _) le_rfl).aestronglyMeasurable
  refine supermartingale_exp_sum_of_condExp_exp_le_one (fun n ↦ ?_)
    (fun n ↦ integrable_exp_mul_sub_mul_condExp_sq (ℱ.le n) hl hc0 (hXm n) (h_bdd n))
    fun n ↦ condExp_exp_mul_sub_mul_condExp_sq_le_one (ℱ.le n) hb hl hc (hXm n) (hX2 n)
      (h_mean n) (h_bdd n)
  exact ((hX n).const_mul l).sub ((stronglyMeasurable_condExp.measurable.mono
    (ℱ.mono n.le_succ) le_rfl).const_mul c)

/-- **Time-uniform exponential bound.** Under the hypotheses of
`supermartingale_exp_mul_sum_sub_mul_sum_condExp_sq`, for every `x : ℝ`, the probability that
`x ≤ l ∑ k < n, X k - c ∑ k < n, E[X k ^ 2 | ℱ k]` for some `n` is at most `exp (-x)`. -/
theorem measure_exists_le_mul_sum_sub_mul_sum_condExp_sq_le [IsProbabilityMeasure μ]
    (hb : 0 < b) (hl : 0 ≤ l) (hc : (exp (l * b) - 1 - l * b) / b ^ 2 ≤ c)
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n)) (hX2 : ∀ n, Integrable (fun ω ↦ X n ω ^ 2) μ)
    (h_mean : ∀ n, μ[X n | ℱ n] ≤ᵐ[μ] 0) (h_bdd : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ b) (x : ℝ) :
    μ {ω | ∃ n, x ≤ l * ∑ k ∈ range n, X k ω
      - c * ∑ k ∈ range n, μ[fun ω ↦ X k ω ^ 2 | ℱ k] ω} ≤ ENNReal.ofReal (exp (-x)) := by
  have h := (supermartingale_exp_mul_sum_sub_mul_sum_condExp_sq hb hl hc hX hX2 h_mean
    h_bdd).measure_exists_le_le (fun n ↦ ae_of_all _ fun ω ↦ (exp_pos _).le) (exp_pos x)
  simpa [← exp_neg] using h

/-- **Freedman's inequality** [Fre75], the martingale analogue of Bernstein's inequality
[BLM13, Theorem 2.10]. Let `X n` be
`ℱ (n + 1)`-measurable, with `X n ^ 2` integrable, `E[X n | ℱ n] ≤ 0` and `X n ≤ b` almost surely,
with `b > 0`. For `a ≥ 0` and `σ² ≥ 0`, the probability that, for some `n`,
`a ≤ ∑ k < n, X k` while `∑ k < n, E[X k ^ 2 | ℱ k] ≤ σ²`, is at most
`exp (-a ^ 2 / (2 (σ² + a b / 3)))`. -/
theorem measure_exists_le_sum_and_sum_condExp_sq_le_le [IsProbabilityMeasure μ] {a σ2 : ℝ}
    (hb : 0 < b) (ha : 0 ≤ a) (hσ2 : 0 ≤ σ2)
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n)) (hX2 : ∀ n, Integrable (fun ω ↦ X n ω ^ 2) μ)
    (h_mean : ∀ n, μ[X n | ℱ n] ≤ᵐ[μ] 0) (h_bdd : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ b) :
    μ {ω | ∃ n, a ≤ ∑ k ∈ range n, X k ω ∧
      ∑ k ∈ range n, μ[fun ω ↦ X k ω ^ 2 | ℱ k] ω ≤ σ2} ≤
      ENNReal.ofReal (exp (-(a ^ 2 / (2 * (σ2 + a * b / 3))))) := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using prob_le_one
  -- the parameter `l = a / D` with `D = σ² + a b / 3`, and `c = ψ_b(l)`
  set D := σ2 + a * b / 3 with hD_def
  have hD : 0 < D := by positivity
  set l := a / D with hl_def
  have hl : 0 ≤ l := by positivity
  set c := (exp (l * b) - 1 - l * b) / b ^ 2 with hc_def
  have hc0 : 0 ≤ c := exp_sub_one_sub_id_div_sq_nonneg (l * b) b
  -- `c σ² ≤ a ^ 2 / (2 D)`, from `exp u - 1 - u ≤ u ^ 2 / (2 (1 - u / 3))` at `u = l b < 3`
  have hcσ : c * σ2 ≤ a ^ 2 / (2 * D) := by
    rcases hσ2.eq_or_lt with rfl | hσ2
    · simp only [mul_zero]
      positivity
    have hu3 : l * b < 3 := by
      rw [hl_def, div_mul_eq_mul_div, div_lt_iff₀ hD, hD_def]
      linarith
    have h1 : 1 - l * b / 3 = σ2 / D := by
      rw [hl_def, hD_def]
      field_simp
      ring
    calc c * σ2 ≤ (l * b) ^ 2 / (2 * (1 - l * b / 3)) / b ^ 2 * σ2 := by
          gcongr
          exact div_le_div_of_nonneg_right (exp_sub_one_sub_id_le_sq_div (by positivity) hu3)
            (sq_nonneg b)
      _ = a ^ 2 / (2 * D) := by
          rw [h1, hl_def]
          field_simp
  refine (measure_mono fun ω hω ↦ ?_).trans
    (measure_exists_le_mul_sum_sub_mul_sum_condExp_sq_le hb hl le_rfl hX hX2 h_mean h_bdd
      (a ^ 2 / (2 * D)))
  obtain ⟨n, hS, hW⟩ := hω
  refine ⟨n, ?_⟩
  -- `l a - c σ² ≥ a ^ 2 / D - a ^ 2 / (2 D) = a ^ 2 / (2 D)`
  have hla : l * a = a ^ 2 / D := by rw [hl_def]; ring
  have h2 : a ^ 2 / (2 * D) = a ^ 2 / D - a ^ 2 / (2 * D) := by field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left hS hl, mul_le_mul_of_nonneg_left hW hc0]

/-- **Freedman's inequality, fixed-`η` form.** Let `X n` be `ℱ (n + 1)`-measurable, with `X n ^ 2`
integrable, `E[X n | ℱ n] ≤ 0` and `η X n ≤ 1` almost surely, with `η > 0`. For `δ > 0`, the
probability that `η ∑ k < n, E[X k ^ 2 | ℱ k] + log (1 / δ) / η ≤ ∑ k < n, X k` for some `n` is at
most `δ`. -/
theorem measure_exists_mul_sum_condExp_sq_add_log_div_le_sum_le [IsProbabilityMeasure μ]
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n)) (hX2 : ∀ n, Integrable (fun ω ↦ X n ω ^ 2) μ)
    (h_mean : ∀ n, μ[X n | ℱ n] ≤ᵐ[μ] 0) (h_bdd : ∀ n, ∀ᵐ ω ∂μ, η * X n ω ≤ 1) :
    μ {ω | ∃ n, η * ∑ k ∈ range n, μ[fun ω ↦ X k ω ^ 2 | ℱ k] ω + log (1 / δ) / η ≤
      ∑ k ∈ range n, X k ω} ≤ ENNReal.ofReal δ := by
  -- `b = 1 / η`, `l = η` and `c = η ^ 2 ≥ ψ_{1/η}(η) = (e - 2) η ^ 2`
  have hbdd : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ 1 / η := fun n ↦ (h_bdd n).mono fun ω hω ↦ by
    rwa [le_div_iff₀ hη, mul_comm]
  have hc : (exp (η * (1 / η)) - 1 - η * (1 / η)) / (1 / η) ^ 2 ≤ η ^ 2 := by
    field_simp
    have := exp_one_lt_d9
    nlinarith [sq_nonneg η]
  refine (measure_mono fun ω hω ↦ ?_).trans
    ((measure_exists_le_mul_sum_sub_mul_sum_condExp_sq_le (one_div_pos.2 hη) hη.le hc hX hX2
      h_mean hbdd (log (1 / δ))).trans_eq ?_)
  · obtain ⟨n, hn⟩ := hω
    refine ⟨n, ?_⟩
    have h := mul_le_mul_of_nonneg_left hn hη.le
    rw [mul_add, mul_div_cancel₀ _ hη.ne'] at h
    nlinarith
  · rw [one_div, log_inv, neg_neg, exp_log hδ]

/-- The deterministic step of the peeling argument: if `S < W / (2 ^ j b) + ℓ 2 ^ j b` for every
`j ≤ J`, where `0 ≤ W ≤ N b ^ 2`, `N ≤ 4 ^ J` and `ℓ ≥ 1`, then `S ≤ 3 √(W ℓ) + 2 b ℓ`. -/
private theorem le_three_mul_sqrt_add_of_forall_lt {S W b ℓ : ℝ} {N J : ℕ} (hb : 0 < b)
    (hℓ : 1 ≤ ℓ) (hW0 : 0 ≤ W) (hWN : W ≤ N * b ^ 2) (hJ : (N : ℝ) ≤ 4 ^ J)
    (h : ∀ j ≤ J, S < W / (2 ^ j * b) + ℓ * (2 ^ j * b)) :
    S ≤ 3 * √(W * ℓ) + 2 * b * ℓ := by
  have hr := sqrt_nonneg (W * ℓ)
  rcases le_or_gt W (b ^ 2 * ℓ) with hWℓ | hWℓ
  · -- small variance: the grid point `j = 0`
    have h0 := h 0 (Nat.zero_le _)
    simp only [pow_zero, one_mul] at h0
    have : W / b ≤ b * ℓ := by rw [div_le_iff₀ hb]; nlinarith
    nlinarith
  -- large variance: the first `j` with `W ≤ 4 ^ j b ^ 2 ℓ`, so that `4 W > 4 ^ j b ^ 2 ℓ`
  have hWJ : W ≤ 4 ^ J * b ^ 2 * ℓ := by
    have h4 : (0 : ℝ) < 4 ^ J * b ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hJ (sq_nonneg b)]
  have hex : ∃ j, W ≤ 4 ^ j * b ^ 2 * ℓ := ⟨J, hWJ⟩
  classical
  set j := Nat.find hex
  have hj : W ≤ 4 ^ j * b ^ 2 * ℓ := Nat.find_spec hex
  have hjJ : j ≤ J := Nat.find_min' hex hWJ
  have hj0 : j ≠ 0 := fun h0 ↦ by
    have := h0 ▸ hj
    simp only [pow_zero, one_mul] at this
    linarith
  have hjmin : 4 ^ (j - 1) * b ^ 2 * ℓ < W := not_le.1 (Nat.find_min hex (Nat.sub_lt
    (Nat.pos_of_ne_zero hj0) one_pos))
  -- with `q = 2 ^ j b`: `W ≤ q ^ 2 ℓ < 4 W`, hence `W / q + ℓ q ≤ 3 √(W ℓ)`
  have hS := h j hjJ
  have hq2 : (2 ^ j * b) ^ 2 = 4 ^ j * b ^ 2 := by
    rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  have hq : (0 : ℝ) < 2 ^ j * b := by positivity
  generalize 2 ^ j * b = q at hS hq2 hq
  have h4 : (4 : ℝ) ^ j = 4 * 4 ^ (j - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)]
  have hsq : √(W * ℓ) ^ 2 = W * ℓ := sq_sqrt (by positivity)
  have h₁ : W / q ≤ √(W * ℓ) := by
    rw [div_le_iff₀ hq]
    refine (pow_le_pow_iff_left₀ hW0 (by positivity) two_ne_zero).1 ?_
    calc W ^ 2 ≤ W * (4 ^ j * b ^ 2 * ℓ) := by rw [sq]; gcongr
      _ = (√(W * ℓ) * q) ^ 2 := by rw [mul_pow, hsq, hq2]; ring
  have h₂ : ℓ * q ≤ 2 * √(W * ℓ) := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    calc (ℓ * q) ^ 2 = ℓ * (4 * (4 ^ (j - 1) * b ^ 2 * ℓ)) := by rw [mul_pow, hq2, h4]; ring
      _ ≤ ℓ * (4 * W) := by gcongr
      _ = (2 * √(W * ℓ)) ^ 2 := by rw [mul_pow, hsq]; ring
  linarith [mul_pos hb (by linarith : (0 : ℝ) < ℓ)]

/-- **Freedman's inequality, peeled form.** Let `X n` be `ℱ (n + 1)`-measurable, with
`E[X n | ℱ n] ≤ 0` and `|X n| ≤ b` almost surely, with `b > 0`. Let `N : ℕ`, `δ > 0`,
`K = ⌈log₄ N⌉ + 1` and `ℓ = max 1 (log (K / δ))`. With probability at least `1 - δ`, for every
`n ≤ N`, `∑ k < n, X k ≤ 3 √(ℓ ∑ k < n, E[X k ^ 2 | ℱ k]) + 2 b ℓ`. -/
theorem measure_exists_three_mul_sqrt_add_lt_sum_le [IsProbabilityMeasure μ] {δ : ℝ} (hb : 0 < b)
    (hδ : 0 < δ) (N : ℕ) (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (h_mean : ∀ n, μ[X n | ℱ n] ≤ᵐ[μ] 0) (h_bdd : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ b) :
    μ {ω | ∃ n ≤ N,
      3 * √((∑ k ∈ range n, μ[fun ω ↦ X k ω ^ 2 | ℱ k] ω) *
        max 1 (log ((⌈logb 4 N⌉₊ + 1 : ℝ) / δ))) +
        2 * b * max 1 (log ((⌈logb 4 N⌉₊ + 1 : ℝ) / δ)) < ∑ k ∈ range n, X k ω} ≤
      ENNReal.ofReal δ := by
  set J := ⌈logb 4 N⌉₊ with hJ_def
  set ℓ := max 1 (log ((J + 1 : ℝ) / δ)) with hℓ_def
  have hK : (0 : ℝ) < J + 1 := by positivity
  have hJ : (N : ℝ) ≤ 4 ^ J := by
    rcases (Nat.cast_nonneg N : (0 : ℝ) ≤ N).eq_or_lt with h0 | hN
    · rw [← h0]; positivity
    rw [← rpow_natCast, ← logb_le_iff_le_rpow (by norm_num) hN]
    exact Nat.le_ceil _
  have hX2 : ∀ n, Integrable (fun ω ↦ X n ω ^ 2) μ := fun n ↦
    Integrable.of_bound (((hX n).mono (ℱ.le _) le_rfl).pow_const 2).aestronglyMeasurable (b ^ 2)
      ((h_bdd n).mono fun ω hω ↦ by
        rw [norm_pow, Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hω 2)
  -- almost surely, `0 ≤ E[X k ^ 2 | ℱ k] ≤ b ^ 2` for every `k`
  have hW : ∀ᵐ ω ∂μ, ∀ k, 0 ≤ μ[fun ω ↦ X k ω ^ 2 | ℱ k] ω ∧
      μ[fun ω ↦ X k ω ^ 2 | ℱ k] ω ≤ b ^ 2 := by
    refine ae_all_iff.2 fun k ↦ ?_
    have hle : μ[fun ω ↦ X k ω ^ 2 | ℱ k] ≤ᵐ[μ] μ[fun _ ↦ b ^ 2 | ℱ k] :=
      condExp_mono (hX2 k) (integrable_const _) ((h_bdd k).mono fun ω hω ↦
        calc X k ω ^ 2 = |X k ω| ^ 2 := (sq_abs _).symm
          _ ≤ b ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hω 2)
    rw [condExp_const (ℱ.le k)] at hle
    filter_upwards [hle, condExp_nonneg (μ := μ) (m := ℱ k)
      (ae_of_all _ fun ω ↦ sq_nonneg (X k ω))] with ω h₁ h₂ using ⟨h₂, h₁⟩
  -- the fixed-`η` events for `η = 1 / (2 ^ j b)`, `j ≤ J`, each of probability at most `δ / K`
  set E : ℕ → Set Ω := fun j ↦ {ω | ∃ n, 1 / (2 ^ j * b) *
    ∑ k ∈ range n, μ[fun ω ↦ X k ω ^ 2 | ℱ k] ω + log (1 / (δ / (J + 1))) / (1 / (2 ^ j * b)) ≤
      ∑ k ∈ range n, X k ω} with hE_def
  have hE : ∀ j, μ (E j) ≤ ENNReal.ofReal (δ / (J + 1)) := fun j ↦
    measure_exists_mul_sum_condExp_sq_add_log_div_le_sum_le (by positivity) (by positivity) hX
      hX2 h_mean fun n ↦ (h_bdd n).mono fun ω hω ↦ by
        rw [one_div_mul_eq_div, div_le_one (by positivity)]
        calc X n ω ≤ |X n ω| := le_abs_self _
          _ ≤ b := hω
          _ ≤ 2 ^ j * b := le_mul_of_one_le_left hb.le (one_le_pow₀ (by norm_num))
  calc μ _ ≤ μ (⋃ j ∈ range (J + 1), E j) := by
        refine measure_mono_ae ?_
        filter_upwards [hW] with ω hω hbad
        obtain ⟨n, hnN, hn⟩ := hbad
        by_contra hnot
        simp only [Set.mem_iUnion, mem_range, not_exists] at hnot
        refine hn.not_ge (le_three_mul_sqrt_add_of_forall_lt hb (le_max_left _ _)
          (sum_nonneg fun k _ ↦ (hω k).1) ?_ hJ fun j hj ↦ ?_)
        · calc ∑ k ∈ range n, μ[fun ω ↦ X k ω ^ 2 | ℱ k] ω ≤ ∑ k ∈ range n, b ^ 2 :=
                sum_le_sum fun k _ ↦ (hω k).2
            _ ≤ N * b ^ 2 := by
                rw [sum_const, card_range, nsmul_eq_mul]
                gcongr
        · have hj' : ω ∉ E j := hnot j (Nat.lt_succ_of_le hj)
          simp only [hE_def, Set.mem_ofPred_eq, not_exists, not_le] at hj'
          refine (hj' n).trans_le ?_
          field_simp
          gcongr
          exact le_max_right _ _
    _ ≤ ∑ j ∈ range (J + 1), μ (E j) := measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ range (J + 1), ENNReal.ofReal (δ / (J + 1)) := sum_le_sum fun j _ ↦ hE j
    _ = ENNReal.ofReal δ := by
        rw [sum_const, card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        field_simp

end Process

end LMLExplore
