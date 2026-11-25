/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Conjugate.Basic
public import LMLExplore.EValues.SubPsi

/-!
# Linear boundaries through a point for sub-ψ processes

The line-crossing inequality (`ProbabilityTheory.IsSubPsiProcess.measure_exists_add_mul_le_le`)
bounds the probability that an `l₀`-sub-ψ process `(S, V)` ever crosses the line `a + b V` by
`l₀ exp (-a D b)`, with `D` the decay transform [HRMS20, Theorem 1(a)]. This file proves the other
three forms of [HRMS20, Theorem 1]. They fix a point `(m, x)` of the `(V, S)` plane instead of an
intercept, and compare the time-uniform bound with the Cramér–Chernoff bound
`exp (-m ψ⋆ (x / m))` at the fixed intrinsic time `m`. Here `ψ⋆ u = ⨆ t ∈ Λ, (t u - ψ t)` is the
Legendre–Fenchel transform of `ψ` on `Λ`: LMLExplore's `fenchelConjugateOn ψ Λ` at the functional
`t ↦ t u` (`ContinuousLinearMap.toSpanSingleton ℝ u`).

Each bound comes from Ville's inequality at a single parameter `t ∈ Λ`, `t ≥ 0`. If
`S n ≥ x + b (V n - m)`, then `t S n - ψ t V n ≥ t x - m ψ t` as soon as `ψ t = b t`, or as soon as
`ψ t ≤ b t` and `V n ≥ m`; so the crossing has probability at most `l₀ exp (-(t x - m ψ t))`. If
`x / m` is a subgradient of `ψ` on `Λ` at `t`, the Fenchel–Young equality makes the exponent
`t x - m ψ t = m ψ⋆ (x / m)`. For a CGF-like `ψ` [HRMS20, Definition 2], which is convex and
differentiable on `Λ = [0, λ_max)`, the subgradients are the derivatives. Then `t` is
`(ψ')⁻¹ (x / m)`, which is also `(ψ⋆)' (x / m)`
(`LMLExplore.hasDerivAt_toReal_fenchelConjugateOn_toSpanSingleton`). So `ψ t / t` is the *slope
transform* `s (x / m) = ψ ((ψ⋆)' (x / m)) / (ψ⋆)' (x / m)` of [HRMS20, (2.6)]. The statements below
take the point `t` and the slope `ψ t / t` as given. This lets them hold for every `ψ`, not only
for CGF-like ones.

With `s = ψ t / t` and `D` the decay transform, the forms are:
* (b) the line of slope `s` through `(m, x)` is crossed with probability at most
  `l₀ exp (-m ψ⋆ (x / m))`. This is the Cramér–Chernoff bound at the intrinsic time `m`, made
  uniform over time;
* (c) the same bound for the normalised process: at a point `(m, x)` with the subgradient `x`,
  the probability that `S / V ≥ x - (x - s) (V - m) / V` at some time with `V > 0` is at most
  `l₀ exp (-m ψ⋆ x)`. This is (b) at the point `(m, m x)`, divided by `V`;
* (d) after the intrinsic time `m`, the line of slope `b` through `(m, x)` is crossed with
  probability at most `l₀ exp (-m ψ⋆ (x / m))` when `s ≤ b`. It is crossed with probability at
  most `l₀ exp (-(x - c m) D b)` when `c m ≤ x`, for every `c ≤ b` with `ψ t ≤ c t` at the
  parameters of `D b`. [HRMS20] takes `c = min b b_max`, with `b_max = sup ψ'`, and assumes
  `x > m b_max` or `b < s (x / m)`; for `m ≥ 0` either gives `c m ≤ x`, the second because
  `s u < u` [HRMS20, Lemma 2(vi)].

With `m = 0` and `c = b`, (d) contains the line-crossing inequality (a). Since the line of (b) has
a nonnegative slope when `ψ t ≥ 0`, (b) also bounds the probability that `S` reaches `x` while
`V ≤ m` by `l₀ exp (-m ψ⋆ (x / m))`: this is the Freedman-style form [HRMS20, Figure 1]. Two
instances close the file. For the one-sided conditionally sub-Gaussian null, (b) gives the bound
`exp (-x ^ 2 / (2 m))` on the probability that the random walk crosses the line
`x + x / (2 m) (n - m)`. For Freedman's supermartingale differences bounded above by `b`, which
are sub-Poisson, the Freedman-style form is Freedman's inequality in Bennett's form
[Fre75, Theorem 1.6].

## Main statements

* `ProbabilityTheory.IsSubPsiProcess.measure_inter_exists_add_mul_sub_le_le_of_mem`,
  `ProbabilityTheory.IsSubPsiProcess.measure_inter_exists_le_and_add_mul_sub_le_le_of_mem`: the
  bound `l₀ exp (-(t x - m ψ t))` at one parameter, conditionally on `ℱ 0`, for a line of slope
  `b` with `ψ t = b t`, and after the intrinsic time `m` for a slope `b` with `ψ t ≤ b t`.
* `ProbabilityTheory.IsSubPsiProcess.measure_exists_add_div_mul_sub_le_le` [HRMS20,
  Theorem 1(b)]: `P(∃ n, x + s (V n - m) ≤ S n) ≤ l₀ exp (-m ψ⋆ (x / m))`.
* `ProbabilityTheory.IsSubPsiProcess.measure_exists_sub_div_mul_sub_le_div_le` [HRMS20,
  Theorem 1(c)]: `P(∃ n, 0 < V n ∧ x - (x - s) / V n (V n - m) ≤ S n / V n) ≤ l₀ exp (-m ψ⋆ x)`.
* `ProbabilityTheory.IsSubPsiProcess.measure_exists_le_and_add_mul_sub_le_le_of_div_le`,
  `ProbabilityTheory.IsSubPsiProcess.measure_exists_le_and_add_mul_sub_le_le` [HRMS20,
  Theorem 1(d)]: the two cases of `P(∃ n, m ≤ V n ∧ x + b (V n - m) ≤ S n)`.
* `ProbabilityTheory.IsSubPsiProcess.measure_exists_le_and_le_le`: the Freedman-style form
  `P(∃ n, V n ≤ m ∧ x ≤ S n) ≤ l₀ exp (-m ψ⋆ (x / m))`.
* `ProbabilityTheory.measure_exists_add_div_mul_sub_le_sum_le_of_mem_oneSidedCondSubgaussianNull`:
  (b) for the one-sided conditionally sub-Gaussian null.
* `ProbabilityTheory.measure_exists_sum_condExp_sq_le_and_le_sum_le`: Freedman's inequality in
  Bennett's form, `P(∃ n, W n ≤ m ∧ x ≤ S n) ≤ exp (-(m / b²) h (b x / m))` with
  `h u = (1 + u) log (1 + u) - u` and `W` the sum of the conditional second moments.

Each of the forms (b), (c), (d) and the Freedman-style form also has a version conditional on
`ℱ 0`, named `measure_inter_…`.

## References

* [HRMS20] S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, *Time-uniform Chernoff bounds via
  nonnegative supermartingales*, Probab. Surveys 17 (2020), 257–317, arXiv:1808.03204.
* [Fre75] D. A. Freedman, *On tail probabilities for martingales*, Ann. Probab. 3 (1975), 100–118.
-/

public section

open MeasureTheory Set Finset Real
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {𝒩 : Set (Measure Ω)}
  {P : Measure Ω} {S V X : ℕ → Ω → ℝ} {ψ : ℝ → ℝ} {Λ : Set ℝ} {l₀ : ℝ≥0∞} {t b c m x : ℝ}
  {s : Set Ω}

/-- At a subgradient `x / m` of `ψ` on `Λ` at `t ∈ Λ`, with `m ≠ 0`, the Cramér–Chernoff exponent
`m ψ⋆ (x / m)` is `t x - m ψ t`, by the Fenchel–Young equality. -/
private lemma exp_neg_mul_fenchelConjugateOn (ht : t ∈ Λ) (hm : m ≠ 0)
    (hu : HasSubgradientWithinAt ψ (ContinuousLinearMap.toSpanSingleton ℝ (x / m)) Λ t) :
    EReal.exp (-(m * LMLExplore.fenchelConjugateOn ψ Λ
      (ContinuousLinearMap.toSpanSingleton ℝ (x / m)))) =
      ENNReal.ofReal (exp (-(t * x - m * ψ t))) := by
  rw [(LMLExplore.hasSubgradientWithinAt_iff_fenchelConjugateOn_eq ht).1 hu, ← EReal.coe_mul,
    ← EReal.coe_neg, EReal.exp_coe, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  congr 3
  field_simp

namespace IsSubPsiProcess

/-! ### The bounds at one parameter -/

/-- **Crossing a line through a point, at one parameter** [HRMS20, proof of Theorem 1(b)],
conditionally on `ℱ 0`. For a parameter `t ≥ 0` of `Λ` and a slope `b` with `ψ t = b t`, the
probability that `s` holds and `S` crosses the line `x + b (V - m)` at some time is at most
`l₀ exp (-(t x - m ψ t)) P s`, for every point `(m, x)`. -/
theorem measure_inter_exists_add_mul_sub_le_le_of_mem (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩)
    (hP : P ∈ 𝒩) (ht : t ∈ Λ) (ht0 : 0 ≤ t) (hψ : ψ t = b * t) (x m : ℝ)
    (hs : MeasurableSet[ℱ 0] s) :
    P (s ∩ {ω | ∃ n, x + b * (V n ω - m) ≤ S n ω}) ≤
      l₀ * ENNReal.ofReal (exp (-(t * x - m * ψ t))) * P s := by
  refine (measure_mono fun ω hω ↦ ?_).trans
    (h.measure_inter_exists_le_mul_sub_mul_le hP ht (t * x - m * ψ t) hs)
  obtain ⟨hωs, n, hn⟩ := hω
  refine ⟨hωs, n, ?_⟩
  -- `t S n ≥ t (x + b (V n - m)) = t x + ψ t (V n - m)`
  have := mul_le_mul_of_nonneg_left hn ht0
  rw [hψ]
  linarith

/-- **Crossing a line through a point after the intrinsic time `m`, at one parameter**
[HRMS20, proof of Theorem 1(d)], conditionally on `ℱ 0`. For a parameter `t ≥ 0` of `Λ` and a
slope `b` with `ψ t ≤ b t`, the probability that `s` holds and `S` crosses the line
`x + b (V - m)` at some time at which `V ≥ m` is at most `l₀ exp (-(t x - m ψ t)) P s`. -/
theorem measure_inter_exists_le_and_add_mul_sub_le_le_of_mem (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩)
    (hP : P ∈ 𝒩) (ht : t ∈ Λ) (ht0 : 0 ≤ t) (hψ : ψ t ≤ b * t) (x m : ℝ)
    (hs : MeasurableSet[ℱ 0] s) :
    P (s ∩ {ω | ∃ n, m ≤ V n ω ∧ x + b * (V n ω - m) ≤ S n ω}) ≤
      l₀ * ENNReal.ofReal (exp (-(t * x - m * ψ t))) * P s := by
  refine (measure_mono fun ω hω ↦ ?_).trans
    (h.measure_inter_exists_le_mul_sub_mul_le hP ht (t * x - m * ψ t) hs)
  obtain ⟨hωs, n, hmV, hn⟩ := hω
  refine ⟨hωs, n, ?_⟩
  -- `t S n ≥ t x + b t (V n - m) ≥ t x + ψ t (V n - m)`, since `V n - m ≥ 0`
  have h₁ := mul_le_mul_of_nonneg_left hn ht0
  have h₂ := mul_le_mul_of_nonneg_right hψ (sub_nonneg.2 hmV)
  linarith

/-! ### The line through a point with the slope transform -/

/-- **The line through a point with the slope transform** [HRMS20, Theorem 1(b)], conditionally
on `ℱ 0`. Let `m ≠ 0` and let `x / m` be a subgradient of `ψ` on `Λ` at a positive parameter
`t ∈ Λ`. For a CGF-like `ψ`, `t = (ψ')⁻¹ (x / m)` and `ψ t / t` is the slope transform
`s (x / m)`. Then the probability that `s` holds and `S` crosses the line `x + (ψ t / t) (V - m)`
through the point `(m, x)` at some time is at most `l₀ exp (-m ψ⋆ (x / m)) P s`. -/
theorem measure_inter_exists_add_div_mul_sub_le_le (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩)
    (hP : P ∈ 𝒩) (hm : m ≠ 0) (ht : t ∈ Λ) (ht0 : 0 < t)
    (hu : HasSubgradientWithinAt ψ (ContinuousLinearMap.toSpanSingleton ℝ (x / m)) Λ t)
    (hs : MeasurableSet[ℱ 0] s) :
    P (s ∩ {ω | ∃ n, x + ψ t / t * (V n ω - m) ≤ S n ω}) ≤
      l₀ * EReal.exp (-(m * LMLExplore.fenchelConjugateOn ψ Λ
        (ContinuousLinearMap.toSpanSingleton ℝ (x / m)))) * P s := by
  rw [exp_neg_mul_fenchelConjugateOn ht hm hu]
  exact h.measure_inter_exists_add_mul_sub_le_le_of_mem hP ht ht0.le
    (div_mul_cancel₀ (ψ t) ht0.ne').symm x m hs

/-- **The line through a point with the slope transform** [HRMS20, Theorem 1(b)]. Under every
probability measure `P` of the null, let `m ≠ 0` and let `x / m` be a subgradient of `ψ` on `Λ`
at a positive parameter `t ∈ Λ`. For a CGF-like `ψ`, `t = (ψ')⁻¹ (x / m)` and `ψ t / t` is the
slope transform `s (x / m)`. Then the probability that `S` ever crosses the line
`x + (ψ t / t) (V - m)` through the point `(m, x)` is at most `l₀ exp (-m ψ⋆ (x / m))`. -/
theorem measure_exists_add_div_mul_sub_le_le (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩) (hP : P ∈ 𝒩)
    [IsProbabilityMeasure P] (hm : m ≠ 0) (ht : t ∈ Λ) (ht0 : 0 < t)
    (hu : HasSubgradientWithinAt ψ (ContinuousLinearMap.toSpanSingleton ℝ (x / m)) Λ t) :
    P {ω | ∃ n, x + ψ t / t * (V n ω - m) ≤ S n ω} ≤
      l₀ * EReal.exp (-(m * LMLExplore.fenchelConjugateOn ψ Λ
        (ContinuousLinearMap.toSpanSingleton ℝ (x / m)))) := by
  simpa using h.measure_inter_exists_add_div_mul_sub_le_le hP hm ht ht0 hu MeasurableSet.univ

/-- **The line through a point for the normalised process** [HRMS20, Theorem 1(c)], conditionally
on `ℱ 0`. Let `m ≠ 0` and let `x` be a subgradient of `ψ` on `Λ` at a positive parameter
`t ∈ Λ`, so that `ψ t / t` is the slope transform `s x` for a CGF-like `ψ`. Then the probability
that `s` holds and, at some time with `V > 0`, `S / V ≥ x - (x - ψ t / t) / V (V - m)` is at most
`l₀ exp (-m ψ⋆ x) P s`. -/
theorem measure_inter_exists_sub_div_mul_sub_le_div_le (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩)
    (hP : P ∈ 𝒩) (hm : m ≠ 0) (ht : t ∈ Λ) (ht0 : 0 < t)
    (hu : HasSubgradientWithinAt ψ (ContinuousLinearMap.toSpanSingleton ℝ x) Λ t)
    (hs : MeasurableSet[ℱ 0] s) :
    P (s ∩ {ω | ∃ n, 0 < V n ω ∧ x - (x - ψ t / t) / V n ω * (V n ω - m) ≤ S n ω / V n ω}) ≤
      l₀ * EReal.exp (-(m * LMLExplore.fenchelConjugateOn ψ Λ
        (ContinuousLinearMap.toSpanSingleton ℝ x))) * P s := by
  -- this is (b) at the point `(m, m x)`
  have hmx : m * x / m = x := mul_div_cancel_left₀ x hm
  rw [← hmx] at hu ⊢
  refine (measure_mono fun ω hω ↦ ?_).trans (h.measure_inter_exists_add_div_mul_sub_le_le hP hm ht
    ht0 hu hs)
  obtain ⟨hωs, n, hV, hn⟩ := hω
  refine ⟨hωs, n, ?_⟩
  rw [hmx, le_div_iff₀ hV] at hn
  have : (x - (x - ψ t / t) / V n ω * (V n ω - m)) * V n ω = m * x + ψ t / t * (V n ω - m) := by
    field_simp
    ring
  linarith

/-- **The line through a point for the normalised process** [HRMS20, Theorem 1(c)]. Under every
probability measure `P` of the null, let `m ≠ 0` and let `x` be a subgradient of `ψ` on `Λ` at a
positive parameter `t ∈ Λ`, so that `ψ t / t` is the slope transform `s x` for a CGF-like `ψ`.
Then the probability that, at some time with `V > 0`, `S / V ≥ x - (x - ψ t / t) / V (V - m)`
is at most `l₀ exp (-m ψ⋆ x)`. -/
theorem measure_exists_sub_div_mul_sub_le_div_le (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩)
    (hP : P ∈ 𝒩) [IsProbabilityMeasure P] (hm : m ≠ 0) (ht : t ∈ Λ) (ht0 : 0 < t)
    (hu : HasSubgradientWithinAt ψ (ContinuousLinearMap.toSpanSingleton ℝ x) Λ t) :
    P {ω | ∃ n, 0 < V n ω ∧ x - (x - ψ t / t) / V n ω * (V n ω - m) ≤ S n ω / V n ω} ≤
      l₀ * EReal.exp (-(m * LMLExplore.fenchelConjugateOn ψ Λ
        (ContinuousLinearMap.toSpanSingleton ℝ x))) := by
  simpa using h.measure_inter_exists_sub_div_mul_sub_le_div_le hP hm ht ht0 hu MeasurableSet.univ

/-! ### Lines through a point after the intrinsic time `m` -/

/-- **Crossing a line through a point after the intrinsic time `m`, with the conjugate bound**
[HRMS20, Theorem 1(d), second case], conditionally on `ℱ 0`. Let `m ≠ 0`, let `x / m` be a
subgradient of `ψ` on `Λ` at a positive parameter `t ∈ Λ`, and let the slope `b` be at least
`ψ t / t`, the slope transform `s (x / m)` for a CGF-like `ψ`. Then the probability that `s`
holds and `S` crosses the line `x + b (V - m)` at some time at which `V ≥ m` is at most
`l₀ exp (-m ψ⋆ (x / m)) P s`. -/
theorem measure_inter_exists_le_and_add_mul_sub_le_le_of_div_le
    (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩) (hP : P ∈ 𝒩) (hm : m ≠ 0) (ht : t ∈ Λ) (ht0 : 0 < t)
    (hu : HasSubgradientWithinAt ψ (ContinuousLinearMap.toSpanSingleton ℝ (x / m)) Λ t)
    (hb : ψ t / t ≤ b) (hs : MeasurableSet[ℱ 0] s) :
    P (s ∩ {ω | ∃ n, m ≤ V n ω ∧ x + b * (V n ω - m) ≤ S n ω}) ≤
      l₀ * EReal.exp (-(m * LMLExplore.fenchelConjugateOn ψ Λ
        (ContinuousLinearMap.toSpanSingleton ℝ (x / m)))) * P s := by
  rw [exp_neg_mul_fenchelConjugateOn ht hm hu]
  exact h.measure_inter_exists_le_and_add_mul_sub_le_le_of_mem hP ht ht0.le
    ((div_le_iff₀ ht0).1 hb) x m hs

/-- **Crossing a line through a point after the intrinsic time `m`, with the conjugate bound**
[HRMS20, Theorem 1(d), second case]. Under every probability measure `P` of the null, let
`m ≠ 0`, let `x / m` be a subgradient of `ψ` on `Λ` at a positive parameter `t ∈ Λ`, and let the
slope `b` be at least `ψ t / t`, the slope transform `s (x / m)` for a CGF-like `ψ`. Then the
probability that `S` crosses the line `x + b (V - m)` at some time at which `V ≥ m` is at most
`l₀ exp (-m ψ⋆ (x / m))`. -/
theorem measure_exists_le_and_add_mul_sub_le_le_of_div_le (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩)
    (hP : P ∈ 𝒩) [IsProbabilityMeasure P] (hm : m ≠ 0) (ht : t ∈ Λ) (ht0 : 0 < t)
    (hu : HasSubgradientWithinAt ψ (ContinuousLinearMap.toSpanSingleton ℝ (x / m)) Λ t)
    (hb : ψ t / t ≤ b) :
    P {ω | ∃ n, m ≤ V n ω ∧ x + b * (V n ω - m) ≤ S n ω} ≤
      l₀ * EReal.exp (-(m * LMLExplore.fenchelConjugateOn ψ Λ
        (ContinuousLinearMap.toSpanSingleton ℝ (x / m)))) := by
  simpa using
    h.measure_inter_exists_le_and_add_mul_sub_le_le_of_div_le hP hm ht ht0 hu hb MeasurableSet.univ

/-- **Crossing a line through a point after the intrinsic time `m`, with the decay bound**
[HRMS20, Theorem 1(d), first case], conditionally on `ℱ 0`. Let `1 ≤ l₀ < ∞`, let `V` be
nonnegative, and let `c ≤ b` be such that every positive parameter `t ∈ Λ` with `ψ t ≤ b t` also
has `ψ t ≤ c t`, such as `c = min b b_max` when `ψ t ≤ b_max t` for all positive `t ∈ Λ`. If
`c m ≤ x`, then the probability that `s` holds and `S` crosses the line `x + b (V - m)` at some
time at which `V ≥ m` is at most `l₀ exp (-(x - c m) D b) P s`, for every `ℱ 0`-measurable set `s`
of finite measure, with `D` the decay transform. -/
theorem measure_inter_exists_le_and_add_mul_sub_le_le (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩)
    (hP : P ∈ 𝒩) (hV : ∀ n, 0 ≤ᵐ[P] V n) (hl₀ : 1 ≤ l₀) (hl₀' : l₀ ≠ ∞) (hcb : c ≤ b)
    (hc : ∀ t ∈ Λ, 0 < t → ψ t ≤ b * t → ψ t ≤ c * t) (hx : c * m ≤ x)
    (hs : MeasurableSet[ℱ 0] s) (hPs : P s ≠ ∞) :
    P (s ∩ {ω | ∃ n, m ≤ V n ω ∧ x + b * (V n ω - m) ≤ S n ω}) ≤
      l₀ * EReal.exp (-(((x - c * m : ℝ) : EReal) * decayTransform ψ Λ b)) * P s := by
  -- after the intrinsic time `m`, the line of slope `b` lies above the line `(x - c m) + c V`
  rw [← decayTransform_eq_of_forall_le_mul hcb hc]
  refine (measure_mono fun ω hω ↦ ?_).trans
    (h.measure_inter_exists_add_mul_le_le hP hV hl₀ hl₀' (sub_nonneg.2 hx) c hs hPs)
  obtain ⟨hωs, n, hmV, hn⟩ := hω
  refine ⟨hωs, n, ?_⟩
  have := mul_le_mul_of_nonneg_right hcb (sub_nonneg.2 hmV)
  linarith

/-- **Crossing a line through a point after the intrinsic time `m`, with the decay bound**
[HRMS20, Theorem 1(d), first case]. Under every probability measure `P` of the null, let
`1 ≤ l₀ < ∞`, let `V` be nonnegative, and let `c ≤ b` be such that every positive parameter
`t ∈ Λ` with `ψ t ≤ b t` also has `ψ t ≤ c t`, such as `c = min b b_max` when `ψ t ≤ b_max t`
for all positive `t ∈ Λ`. If `c m ≤ x`, then the probability that `S` crosses the line
`x + b (V - m)` at some time at which `V ≥ m` is at most `l₀ exp (-(x - c m) D b)`, with `D` the
decay transform. -/
theorem measure_exists_le_and_add_mul_sub_le_le (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩)
    (hP : P ∈ 𝒩) [IsProbabilityMeasure P] (hV : ∀ n, 0 ≤ᵐ[P] V n) (hl₀ : 1 ≤ l₀)
    (hl₀' : l₀ ≠ ∞) (hcb : c ≤ b) (hc : ∀ t ∈ Λ, 0 < t → ψ t ≤ b * t → ψ t ≤ c * t)
    (hx : c * m ≤ x) :
    P {ω | ∃ n, m ≤ V n ω ∧ x + b * (V n ω - m) ≤ S n ω} ≤
      l₀ * EReal.exp (-(((x - c * m : ℝ) : EReal) * decayTransform ψ Λ b)) := by
  simpa using h.measure_inter_exists_le_and_add_mul_sub_le_le hP hV hl₀ hl₀' hcb hc hx
    MeasurableSet.univ (measure_ne_top P univ)

/-! ### The Freedman-style form -/

/-- **The Freedman-style form** [HRMS20, Theorem 1(b) and Figure 1], conditionally on `ℱ 0`. Let
`m ≠ 0` and let `x / m` be a subgradient of `ψ` on `Λ` at a positive parameter `t ∈ Λ` with
`ψ t ≥ 0`. Then the probability that `s` holds and `S` reaches `x` at some time at which `V ≤ m`
is at most `l₀ exp (-m ψ⋆ (x / m)) P s`. -/
theorem measure_inter_exists_le_and_le_le (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩) (hP : P ∈ 𝒩)
    (hm : m ≠ 0) (ht : t ∈ Λ) (ht0 : 0 < t)
    (hu : HasSubgradientWithinAt ψ (ContinuousLinearMap.toSpanSingleton ℝ (x / m)) Λ t)
    (hψ : 0 ≤ ψ t) (hs : MeasurableSet[ℱ 0] s) :
    P (s ∩ {ω | ∃ n, V n ω ≤ m ∧ x ≤ S n ω}) ≤
      l₀ * EReal.exp (-(m * LMLExplore.fenchelConjugateOn ψ Λ
        (ContinuousLinearMap.toSpanSingleton ℝ (x / m)))) * P s := by
  -- before the intrinsic time `m`, the line of (b) lies below `x`
  refine (measure_mono fun ω hω ↦ ?_).trans
    (h.measure_inter_exists_add_div_mul_sub_le_le hP hm ht ht0 hu hs)
  obtain ⟨hωs, n, hV, hn⟩ := hω
  refine ⟨hωs, n, ?_⟩
  have := mul_nonpos_of_nonneg_of_nonpos (div_nonneg hψ ht0.le) (sub_nonpos.2 hV)
  linarith

/-- **The Freedman-style form** [HRMS20, Theorem 1(b) and Figure 1]. Under every probability
measure `P` of the null, let `m ≠ 0` and let `x / m` be a subgradient of `ψ` on `Λ` at a positive
parameter `t ∈ Λ` with `ψ t ≥ 0`. Then the probability that `S` reaches `x` at some time at which
`V ≤ m` is at most `l₀ exp (-m ψ⋆ (x / m))`. -/
theorem measure_exists_le_and_le_le (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩) (hP : P ∈ 𝒩)
    [IsProbabilityMeasure P] (hm : m ≠ 0) (ht : t ∈ Λ) (ht0 : 0 < t)
    (hu : HasSubgradientWithinAt ψ (ContinuousLinearMap.toSpanSingleton ℝ (x / m)) Λ t)
    (hψ : 0 ≤ ψ t) :
    P {ω | ∃ n, V n ω ≤ m ∧ x ≤ S n ω} ≤
      l₀ * EReal.exp (-(m * LMLExplore.fenchelConjugateOn ψ Λ
        (ContinuousLinearMap.toSpanSingleton ℝ (x / m)))) := by
  simpa using h.measure_inter_exists_le_and_le_le hP hm ht ht0 hu hψ MeasurableSet.univ

end IsSubPsiProcess

/-! ### The sub-Gaussian case -/

/-- **The line through a point for the one-sided conditionally sub-Gaussian null**
[HRMS20, Theorem 1(b)]. Under every member of `oneSidedCondSubgaussianNull`, for `m, x > 0`, the
probability that the random walk `∑ k < n, ω k` ever crosses the line `x + x / (2 m) (n - m)`
through the point `(m, x)` is at most `exp (-x ^ 2 / (2 m))`, the Gaussian tail bound at the
time `m`. Here `ψ t = t ^ 2 / 2` on `[0, ∞)`, with `ψ⋆ u = u ^ 2 / 2` and slope transform
`s u = u / 2`. -/
theorem measure_exists_add_div_mul_sub_le_sum_le_of_mem_oneSidedCondSubgaussianNull
    {P : Measure (ℕ → ℝ)} (hP : P ∈ oneSidedCondSubgaussianNull) (hm : 0 < m) (hx : 0 < x) :
    P {ω | ∃ n : ℕ, x + x / (2 * m) * (n - m) ≤ ∑ k ∈ range n, ω k} ≤
      ENNReal.ofReal (exp (-(x ^ 2 / (2 * m)))) := by
  have := isProbabilityMeasure_of_mem_oneSidedCondSubgaussianNull hP
  have hsub := isSubPsiProcess_sum_condEVarNull (ψ := fun t ↦ t ^ 2 / 2) (Λ := Ici 0)
    (ℱ := Filtration.piLT) (X := fun k ω ↦ ω k)
    fun k ↦ Filtration.measurable_piLT_apply k.lt_succ_self
  rw [← oneSidedCondSubgaussianNull_eq_condEVarNull] at hsub
  have ht0 : 0 < x / m := div_pos hx hm
  -- the tangent of `t ^ 2 / 2` at `x / m` has slope `x / m`
  have hu : HasSubgradientWithinAt (fun t : ℝ ↦ t ^ 2 / 2)
      (ContinuousLinearMap.toSpanSingleton ℝ (x / m)) (Ici 0) (x / m) := by
    refine hasSubgradientWithinAt_iff_le.2 fun y _ ↦ ?_
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    nlinarith [sq_nonneg (y - x / m)]
  have h := hsub.measure_exists_add_div_mul_sub_le_le hP hm.ne' (Set.mem_Ici.2 ht0.le) ht0 hu
  rw [exp_neg_mul_fenchelConjugateOn (Set.mem_Ici.2 ht0.le) hm.ne' hu, one_mul] at h
  convert h using 5
  · field_simp
  · field_simp
    ring

/-! ### Freedman's inequality in Bennett's form -/

/-- **Freedman's inequality in Bennett's form** [Fre75, Theorem 1.6; HRMS20, Corollary 1(b)]. Let
`X n` be `ℱ (n + 1)`-measurable, with `X n ^ 2` integrable, `E[X n | ℱ n] ≤ 0` and `X n ≤ b`
almost surely, with `b > 0`. For `m, x > 0`, the probability that the partial sums
`∑ k < n, X k` reach `x` at some time at which the sum of the conditional second moments
`∑ k < n, E[X k ^ 2 | ℱ k]` is at most `m` is at most `exp (-(m / b²) h (b x / m))`, with Bennett's
function `h u = (1 + u) log (1 + u) - u`. This is the Freedman-style form of (b) for the
sub-Poisson `ψ t = (exp (t b) - 1 - t b) / b²`, whose conjugate is `ψ⋆ u = h (b u) / b²`, attained
at `t = log (1 + b u) / b`. -/
theorem measure_exists_sum_condExp_sq_le_and_le_sum_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hb : 0 < b) (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hX2 : ∀ n, Integrable (fun ω ↦ X n ω ^ 2) μ) (h_mean : ∀ n, μ[X n | ℱ n] ≤ᵐ[μ] 0)
    (h_bdd : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ b) (hm : 0 < m) (hx : 0 < x) :
    μ {ω | ∃ n, ∑ k ∈ range n, μ[fun ω ↦ X k ω ^ 2 | ℱ k] ω ≤ m ∧ x ≤ ∑ k ∈ range n, X k ω} ≤
      ENNReal.ofReal
        (exp (-(m / b ^ 2 * ((1 + b * x / m) * log (1 + b * x / m) - b * x / m)))) := by
  have hsub := isSubPsiProcess_sum_sum_condExp_sq hb hX hX2 h_mean h_bdd
  have hbx : 0 < b * (x / m) := mul_pos hb (div_pos hx hm)
  -- the parameter `t = log (1 + b x / m) / b`, at which `exp (t b) = 1 + b x / m`
  set t := log (1 + b * (x / m)) / b with ht_def
  have ht0 : 0 < t := div_pos (log_pos (by linarith)) hb
  have hexp : exp (t * b) = 1 + b * (x / m) := by
    rw [ht_def, div_mul_cancel₀ _ hb.ne', exp_log (by linarith)]
  -- `ψ` lies above its tangent of slope `x / m` at `t`, by `exp z ≥ 1 + z`
  have hu : HasSubgradientWithinAt (fun t ↦ (exp (t * b) - 1 - t * b) / b ^ 2)
      (ContinuousLinearMap.toSpanSingleton ℝ (x / m)) (Ici 0) t := by
    refine hasSubgradientWithinAt_iff_le.2 fun y _ ↦ ?_
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    have h₁ : exp (t * b) * (y * b - t * b + 1) ≤ exp (y * b) := by
      calc exp (t * b) * (y * b - t * b + 1) ≤ exp (t * b) * exp (y * b - t * b) :=
            mul_le_mul_of_nonneg_left (add_one_le_exp _) (exp_pos _).le
        _ = exp (y * b) := by rw [← exp_add]; ring_nf
    rw [hexp] at h₁ ⊢
    rw [div_add' _ _ _ (by positivity), div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  have hψ : 0 ≤ (exp (t * b) - 1 - t * b) / b ^ 2 := by
    have := add_one_le_exp (t * b)
    exact div_nonneg (by linarith) (sq_nonneg b)
  have h := hsub.measure_exists_le_and_le_le (mem_singleton μ) hm.ne' (Set.mem_Ici.2 ht0.le) ht0 hu
    hψ
  rw [exp_neg_mul_fenchelConjugateOn (Set.mem_Ici.2 ht0.le) hm.ne' hu, one_mul, hexp] at h
  refine h.trans_eq ?_
  rw [ht_def, mul_div_assoc]
  congr 3
  field_simp
  ring

end ProbabilityTheory
