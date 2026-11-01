/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Exp
public import LMLExplore.Probability.Martingale.Basic
public import LMLExplore.Probability.Martingale.Ville
public import LMLExplore.Probability.Moments.SubGaussian
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Exponential supermartingales of sub-Gaussian sums

Let `ℱ` be a filtration on a standard Borel space, `Y` a real process with `Y n`
`ℱ (n + 1)`-measurable and conditionally `c`-sub-Gaussian given `ℱ n` (a sub-Gaussian martingale
difference sequence), and `w` an adapted process of weights. For the weighted sums
`T n = ∑ k < n, w k * Y k`, with quadratic variation `A n = ∑ k < n, w k ^ 2`, the process
`exp (t * T n - c * t ^ 2 * A n / 2)` is a nonnegative supermartingale with initial value `1`, for
every `t : ℝ`. Ville's inequality turns it into concentration bounds that hold simultaneously for
all times.

Splitting the times into the blocks `[2 ^ j, 2 ^ (j + 1))` and applying the maximal inequality on
each block (the peeling device) bounds the probability that the sample mean
`μ̂_s = (∑ k < s, Y k) / s` ever falls below `-Δ - √(4 c / s * log⁺ (1 / (s δ)))`, by
`12 c δ / Δ ^ 2`. This is [LS, Lemma 9.3], which controls how far the index of an optimal arm
under the MOSS algorithm drops below its mean. It holds in particular for independent
`c`-sub-Gaussian variables, which are conditionally `c`-sub-Gaussian given the past.

## Main statements

* `LMLExplore.supermartingale_exp_sum_mul_of_hasCondSubgaussianMGF`: the exponential
  supermartingale.
* `LMLExplore.measure_exists_le_mul_sum_sub_of_hasCondSubgaussianMGF`: with probability at least
  `1 - exp (-x)`, `t * T n - c * t ^ 2 * A n / 2 < x` for all `n` simultaneously.
* `LMLExplore.measure_exists_le_sum_le_of_hasCondSubgaussianMGF`: the maximal inequality
  `P(∃ n ≤ N, ε ≤ ∑ k < n, Y k) ≤ exp (-ε ^ 2 / (2 N c))` for `ε ≥ 0`.
* `LMLExplore.measure_exists_sum_div_add_sqrt_add_le_zero_le_of_hasCondSubgaussianMGF`: the
  peeling bound
  `P(∃ s ≥ 1, μ̂_s + √(4 c / s * log⁺ (1 / (s δ))) + Δ ≤ 0) ≤ 12 c δ / Δ ^ 2` for `δ, Δ > 0`.
* `LMLExplore.measure_exists_sum_div_add_sqrt_add_le_zero_le_of_iIndepFun`: the same bound for
  independent `c`-sub-Gaussian variables, which is [LS, Lemma 9.3] with variance proxy `c`.

## Implementation notes

The proof of [LS, Lemma 9.3] bounds the probability of the block `j` by
`2 δ * 2 ^ j exp (-2 ^ j Δ ^ 2 / (4 c))`, as in the book. The book sums these terms by comparison
with an integral and obtains the constant `15`. Here the inequality
`y exp (-y) ≤ 3 (exp (-2 y / 3) - exp (-4 y / 3)) / 2` makes the sum telescope
(`Real.sum_range_two_pow_mul_exp_neg_le`), which gives the constant `12`. The book also assumes
`δ < 1`, which the proof does not use.

The version for independent variables is deduced from the conditional one on the product space
`ℕ → ℝ` with the law of the sequence, which is standard Borel, so that no assumption on the
underlying space is needed.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Theorem 9.2 and Lemma 9.3.
* `supermartingale_exp_sum_mul_of_hasCondSubgaussianMGF` is adapted from the formalization in the
  LMLPapers project
  (`LMLPapers/LeanMachineLearning/ForMathlib/Probability/Martingale/SubgaussianSum.lean`); the
  consequences of Ville's inequality are new here.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Filter
open scoped ENNReal NNReal Topology

namespace LMLExplore

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {μ : Measure Ω}
  {ℱ : Filtration ℕ mΩ} {Y w : ℕ → Ω → ℝ} {c : ℝ≥0}

/-- **Exponential supermartingale of a sub-Gaussian sum.** If `Y n` is `ℱ (n + 1)`-measurable and
conditionally `c`-sub-Gaussian given `ℱ n`, and the weights `w` are adapted, then for every
`t : ℝ`, `n ↦ exp (t * ∑ k < n, w k * Y k - c * t ^ 2 * (∑ k < n, w k ^ 2) / 2)` is a
supermartingale. -/
theorem supermartingale_exp_sum_mul_of_hasCondSubgaussianMGF [IsFiniteMeasure μ]
    (hY : ∀ n, Measurable[ℱ (n + 1)] (Y n))
    (hsubG : ∀ n, HasCondSubgaussianMGF (ℱ n) (ℱ.le n) (Y n) c μ) (hw : Adapted ℱ w) (t : ℝ) :
    Supermartingale (fun n ω ↦ exp (t * ∑ k ∈ range n, w k ω * Y k ω
      - c * t ^ 2 * (∑ k ∈ range n, w k ω ^ 2) / 2)) ℱ μ := by
  set U : ℕ → Ω → ℝ := fun n ω ↦ exp (t * ∑ k ∈ range n, w k ω * Y k ω
      - c * t ^ 2 * (∑ k ∈ range n, w k ω ^ 2) / 2) with hU_def
  have hU_adapted : Adapted ℱ U := by
    intro n
    have hT : Measurable[ℱ n] (fun ω ↦ ∑ k ∈ range n, w k ω * Y k ω) := by
      refine Finset.measurable_fun_sum _ fun k hk ↦ ?_
      have hk : k + 1 ≤ n := mem_range.1 hk
      exact (hw.measurable_le (by omega)).mul ((hY k).mono (ℱ.mono hk) le_rfl)
    have hA : Measurable[ℱ n] (fun ω ↦ ∑ k ∈ range n, w k ω ^ 2) :=
      Finset.measurable_fun_sum _ fun k hk ↦ (hw.measurable_le (mem_range.1 hk).le).pow_const 2
    exact ((hT.const_mul t).sub ((hA.const_mul (c * t ^ 2)).div_const 2)).exp
  refine supermartingale_of_setLIntegral_succ_le hU_adapted
    (fun n ↦ ae_of_all _ fun ω ↦ (exp_pos _).le) (by simp [hU_def]) fun n A hA ↦ ?_
  -- the `ℱ n`-measurable factor, with the parameter `s = t * w n`
  set g : Ω → ℝ≥0∞ := A.indicator fun ω ↦
    ENNReal.ofReal (U n ω * exp (-(c * (t * w n ω) ^ 2 / 2))) with hg_def
  have hs : Measurable[ℱ n] (fun ω ↦ t * w n ω) := (hw n).const_mul t
  have hg : Measurable[ℱ n] g :=
    ((hU_adapted n).mul ((((hs.pow_const 2).const_mul c).div_const 2).neg.exp)).ennreal_ofReal
      |>.indicator hA
  have h_succ : ∀ ω, A.indicator (fun ω ↦ ENNReal.ofReal (U (n + 1) ω)) ω
      = g ω * ENNReal.ofReal (exp ((t * w n ω) * Y n ω)) := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [hg_def, Set.indicator_of_mem hω]
      rw [← ENNReal.ofReal_mul (mul_nonneg (exp_pos _).le (exp_pos _).le)]
      congr 1
      simp only [hU_def, sum_range_succ, ← exp_add]
      congr 1
      ring
    · simp [hg_def, hω]
  have h_n : ∀ ω, g ω * ENNReal.ofReal (exp (c * (t * w n ω) ^ 2 / 2))
      = A.indicator (fun ω ↦ ENNReal.ofReal (U n ω)) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [hg_def, Set.indicator_of_mem hω]
      rw [← ENNReal.ofReal_mul (mul_nonneg (exp_pos _).le (exp_pos _).le), mul_assoc,
        ← exp_add]
      simp [hU_def]
    · simp [hg_def, hω]
  rw [← lintegral_indicator (ℱ.le n _ hA), ← lintegral_indicator (ℱ.le n _ hA)]
  simp_rw [h_succ, ← h_n]
  exact (hsubG n).lintegral_mul_exp_le ((hY n).mono (ℱ.le _) le_rfl) hs hg

/-- **Time-uniform bound for sub-Gaussian sums.** If `Y n` is `ℱ (n + 1)`-measurable and
conditionally `c`-sub-Gaussian given `ℱ n`, and the weights `w` are adapted, then for all
`t x : ℝ`, the probability that
`x ≤ t * ∑ k < n, w k * Y k - c * t ^ 2 * (∑ k < n, w k ^ 2) / 2` for some `n` is at most
`exp (-x)`. -/
theorem measure_exists_le_mul_sum_sub_of_hasCondSubgaussianMGF [IsProbabilityMeasure μ]
    (hY : ∀ n, Measurable[ℱ (n + 1)] (Y n))
    (hsubG : ∀ n, HasCondSubgaussianMGF (ℱ n) (ℱ.le n) (Y n) c μ) (hw : Adapted ℱ w)
    (t x : ℝ) :
    μ {ω | ∃ n, x ≤ t * ∑ k ∈ range n, w k ω * Y k ω
      - c * t ^ 2 * (∑ k ∈ range n, w k ω ^ 2) / 2} ≤ ENNReal.ofReal (exp (-x)) := by
  have h :=
    (supermartingale_exp_sum_mul_of_hasCondSubgaussianMGF hY hsubG hw t).measure_exists_le_le
      (fun n ↦ ae_of_all _ fun ω ↦ (exp_pos _).le) (exp_pos x)
  simpa [← exp_neg] using h

/-- **Maximal inequality for sub-Gaussian sums** ([LS, Theorem 9.2], for conditionally
sub-Gaussian increments): if `Y n` is `ℱ (n + 1)`-measurable and conditionally `c`-sub-Gaussian
given `ℱ n`, then for `ε ≥ 0` and every horizon `N`,
`P(∃ n ≤ N, ε ≤ ∑ k < n, Y k) ≤ exp (-ε ^ 2 / (2 N c))`. -/
theorem measure_exists_le_sum_le_of_hasCondSubgaussianMGF [IsProbabilityMeasure μ]
    (hY : ∀ n, Measurable[ℱ (n + 1)] (Y n))
    (hsubG : ∀ n, HasCondSubgaussianMGF (ℱ n) (ℱ.le n) (Y n) c μ) {ε : ℝ} (hε : 0 ≤ ε)
    (N : ℕ) :
    μ {ω | ∃ n ≤ N, ε ≤ ∑ k ∈ range n, Y k ω} ≤ ENNReal.ofReal (exp (-ε ^ 2 / (2 * N * c))) := by
  rcases (by positivity : (0 : ℝ) ≤ N * c).eq_or_lt with hNc | hNc
  · simpa [mul_assoc, ← hNc] using prob_le_one
  have hN : (N : ℝ) ≠ 0 := left_ne_zero_of_mul hNc.ne'
  have hc : (c : ℝ) ≠ 0 := right_ne_zero_of_mul hNc.ne'
  set t := ε / (N * c) with ht_def
  have ht : 0 ≤ t := div_nonneg hε hNc.le
  have key : t * ε - c * t ^ 2 * N / 2 = ε ^ 2 / (2 * N * c) := by
    rw [ht_def]
    field_simp
    ring
  have h := measure_exists_le_mul_sum_sub_of_hasCondSubgaussianMGF hY hsubG (w := fun _ _ ↦ 1)
    (fun _ ↦ measurable_const) t
    (ε ^ 2 / (2 * N * c))
  refine (measure_mono fun ω hω ↦ ?_).trans (h.trans_eq (by rw [neg_div]))
  obtain ⟨n, hn, hεn⟩ := hω
  refine ⟨n, ?_⟩
  simp only [one_mul, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
  have h1 : t * ε ≤ t * ∑ k ∈ range n, Y k ω := mul_le_mul_of_nonneg_left hεn ht
  have h2 : (c : ℝ) * t ^ 2 * n ≤ c * t ^ 2 * N :=
    mul_le_mul_of_nonneg_left (Nat.cast_le.2 hn) (by positivity)
  linarith

/-- On the event of [LS, Lemma 9.3] at the sample size `s`, the negated sum `-∑ k < s, Y k` is at
least the deviation level of the block `2 ^ j ≤ s < 2 ^ (j + 1)` of the peeling device. -/
private lemma le_neg_sum_of_sum_div_add_sqrt_add_le_zero {c δ Δ S : ℝ} (hc : 0 ≤ c)
    (hδ : 0 < δ) (hΔ : 0 ≤ Δ) {s j : ℕ} (hs : 0 < s) (hjs : 2 ^ j ≤ s) (hsj : s < 2 ^ (j + 1))
    (h : S / s + √(4 * c / s * log⁺ (1 / (s * δ))) + Δ ≤ 0) :
    2 ^ j * Δ + √(4 * c * 2 ^ j * log⁺ (1 / (2 ^ (j + 1) * δ))) ≤ -S := by
  have hs' : (0 : ℝ) < s := Nat.cast_pos.2 hs
  have hjs' : (2 : ℝ) ^ j ≤ s := mod_cast hjs
  have hsj' : (s : ℝ) ≤ 2 ^ (j + 1) := mod_cast hsj.le
  -- the deviation level is monotone in the sample size on the block
  have h_log : log⁺ (1 / (2 ^ (j + 1) * δ)) ≤ log⁺ (1 / (s * δ)) :=
    posLog_le_posLog (by linarith [one_div_nonneg.2 (by positivity : (0 : ℝ) ≤ 2 ^ (j + 1) * δ)])
      (one_div_le_one_div_of_le (by positivity) (by gcongr))
  have h_sqrt : √(4 * c * 2 ^ j * log⁺ (1 / (2 ^ (j + 1) * δ)))
      ≤ s * √(4 * c / s * log⁺ (1 / (s * δ))) := by
    have h_eq : s * √(4 * c / s * log⁺ (1 / (s * δ)))
        = √((s : ℝ) ^ 2 * (4 * c / s * log⁺ (1 / (s * δ)))) := by
      rw [sqrt_mul (sq_nonneg _), sqrt_sq hs'.le]
    rw [h_eq]
    refine sqrt_le_sqrt ?_
    calc 4 * c * 2 ^ j * log⁺ (1 / (2 ^ (j + 1) * δ))
    _ ≤ 4 * c * s * log⁺ (1 / (s * δ)) := by gcongr; exact posLog_nonneg
    _ = s ^ 2 * (4 * c / s * log⁺ (1 / (s * δ))) := by field_simp
  have h_mul : S + s * √(4 * c / s * log⁺ (1 / (s * δ))) + s * Δ ≤ 0 := by
    have := mul_nonpos_of_nonneg_of_nonpos hs'.le h
    rwa [mul_add, mul_add, mul_div_cancel₀ _ hs'.ne'] at this
  nlinarith [mul_le_mul_of_nonneg_right hjs' hΔ]

/-- The bound of the block `2 ^ j ≤ s < 2 ^ (j + 1)` in the peeling device: the maximal inequality
at the horizon `2 ^ (j + 1)` and the deviation level `ε j` of
`le_neg_sum_of_sum_div_add_sqrt_add_le_zero` give at most `2 δ * 2 ^ j exp (-2 ^ j Δ ^ 2 / (4 c))`.
-/
private lemma exp_neg_sq_div_le {c δ Δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hΔ : 0 ≤ Δ) (j : ℕ) :
    exp (-(2 ^ j * Δ + √(4 * c * 2 ^ j * log⁺ (1 / (2 ^ (j + 1) * δ)))) ^ 2
        / (2 * (2 ^ (j + 1) : ℕ) * c))
      ≤ 2 * δ * (2 ^ j * exp (-(2 ^ j * (Δ ^ 2 / (4 * c))))) := by
  set L := log⁺ (1 / (2 ^ (j + 1) * δ))
  have hL : 0 ≤ L := posLog_nonneg
  -- `(a + b) ^ 2 ≥ a ^ 2 + b ^ 2` for `a, b ≥ 0`
  have h_sq : (2 ^ j * Δ) ^ 2 + 4 * c * 2 ^ j * L ≤ (2 ^ j * Δ + √(4 * c * 2 ^ j * L)) ^ 2 := by
    have h_sqrt := sq_sqrt (by positivity : (0 : ℝ) ≤ 4 * c * 2 ^ j * L)
    nlinarith [sqrt_nonneg (4 * c * 2 ^ j * L), (by positivity : (0 : ℝ) ≤ 2 ^ j * Δ)]
  -- `exp (-log⁺ x) ≤ 1 / x` for `x > 0`
  have h_L : exp (-L) ≤ 2 ^ (j + 1) * δ := by
    calc exp (-L)
    _ ≤ exp (-log (1 / (2 ^ (j + 1) * δ))) := exp_le_exp.2 (neg_le_neg (le_max_right _ _))
    _ = 2 ^ (j + 1) * δ := by rw [one_div, log_inv, neg_neg, exp_log (by positivity)]
  calc exp (-(2 ^ j * Δ + √(4 * c * 2 ^ j * L)) ^ 2 / (2 * (2 ^ (j + 1) : ℕ) * c))
  _ ≤ exp (-L + -(2 ^ j * (Δ ^ 2 / (4 * c)))) := by
    refine exp_le_exp.2 ?_
    rw [neg_div, ← neg_add, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    push_cast
    have h_eq : (L + 2 ^ j * (Δ ^ 2 / (4 * c))) * (2 * 2 ^ (j + 1) * c)
        = (2 ^ j * Δ) ^ 2 + 4 * c * 2 ^ j * L := by
      field_simp
      ring
    linarith
  _ = exp (-L) * exp (-(2 ^ j * (Δ ^ 2 / (4 * c)))) := exp_add _ _
  _ ≤ 2 ^ (j + 1) * δ * exp (-(2 ^ j * (Δ ^ 2 / (4 * c)))) := by gcongr
  _ = 2 * δ * (2 ^ j * exp (-(2 ^ j * (Δ ^ 2 / (4 * c))))) := by ring

/-- **Peeling bound for sub-Gaussian sums** ([LS, Lemma 9.3], for conditionally sub-Gaussian
increments): if `Y n` is `ℱ (n + 1)`-measurable and conditionally `c`-sub-Gaussian given `ℱ n`,
then for `δ > 0` and `Δ > 0`, the probability that for some `s ≥ 1` the sample mean of
`Y 0, …, Y (s - 1)` satisfies `(∑ k < s, Y k) / s + √(4 c / s * log⁺ (1 / (s δ))) + Δ ≤ 0` is
at most `12 c δ / Δ ^ 2`. The book states the constant `15`, for `δ < 1`. -/
theorem measure_exists_sum_div_add_sqrt_add_le_zero_le_of_hasCondSubgaussianMGF
    [IsProbabilityMeasure μ] (hY : ∀ n, Measurable[ℱ (n + 1)] (Y n))
    (hsubG : ∀ n, HasCondSubgaussianMGF (ℱ n) (ℱ.le n) (Y n) c μ) {δ Δ : ℝ} (hδ : 0 < δ)
    (hΔ : 0 < Δ) :
    μ {ω | ∃ s : ℕ, 0 < s ∧
        (∑ k ∈ range s, Y k ω) / s + √(4 * c / s * log⁺ (1 / (s * δ))) + Δ ≤ 0}
      ≤ ENNReal.ofReal (12 * c * δ / Δ ^ 2) := by
  -- the lower deviations of `Y` are the upper deviations of `-Y`
  have hY' : ∀ n, Measurable[ℱ (n + 1)] (fun ω ↦ -Y n ω) := fun n ↦ (hY n).neg
  have hsubG' : ∀ n, HasCondSubgaussianMGF (ℱ n) (ℱ.le n) (fun ω ↦ -Y n ω) c μ :=
    fun n ↦ (hsubG n).neg
  have h_block {ω : Ω} {s : ℕ} (hs : 0 < s)
      (h : (∑ k ∈ range s, Y k ω) / s + √(4 * c / s * log⁺ (1 / (s * δ))) + Δ ≤ 0) :
      2 ^ Nat.log 2 s * Δ + √(4 * c * 2 ^ Nat.log 2 s * log⁺ (1 / (2 ^ (Nat.log 2 s + 1) * δ)))
        ≤ ∑ k ∈ range s, -Y k ω := by
    rw [sum_neg_distrib]
    exact le_neg_sum_of_sum_div_add_sqrt_add_le_zero c.2 hδ hΔ.le hs
      (Nat.pow_log_le_self 2 hs.ne') (Nat.lt_pow_succ_log_self (by norm_num) s) h
  rcases eq_or_ne c 0 with hc | hc
  · -- for `c = 0`, the time-uniform bound `exp (-t Δ)` holds for every `t ≥ 0`
    subst hc
    have h_le (t : ℕ) : μ {ω | ∃ s : ℕ, 0 < s ∧
        (∑ k ∈ range s, Y k ω) / s + √(4 * (0 : ℝ≥0) / s * log⁺ (1 / (s * δ))) + Δ ≤ 0}
          ≤ ENNReal.ofReal (exp (-(t * Δ))) := by
      have h_unif := measure_exists_le_mul_sum_sub_of_hasCondSubgaussianMGF hY' hsubG'
        (w := fun _ _ ↦ 1) (fun _ ↦ measurable_const) t (t * Δ)
      refine le_trans (measure_mono fun ω hω ↦ ?_) h_unif
      obtain ⟨s, hs, h⟩ := hω
      refine ⟨s, ?_⟩
      have hΔs : Δ ≤ ∑ k ∈ range s, -Y k ω := by
        have h1 := h_block hs h
        have h2 : Δ ≤ 2 ^ Nat.log 2 s * Δ := le_mul_of_one_le_left hΔ.le (one_le_pow₀ one_le_two)
        simp only [NNReal.coe_zero, mul_zero, zero_mul, sqrt_zero, add_zero] at h1
        linarith
      simpa using mul_le_mul_of_nonneg_left hΔs (Nat.cast_nonneg t)
    have h_tendsto : Tendsto (fun t : ℕ ↦ ENNReal.ofReal (exp (-(t * Δ)))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const hΔ))
    simpa using ge_of_tendsto' h_tendsto h_le
  -- for `c > 0`, peel the sample sizes into the blocks `2 ^ j ≤ s < 2 ^ (j + 1)`
  have hc : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  set ε : ℕ → ℝ := fun j ↦ 2 ^ j * Δ + √(4 * c * 2 ^ j * log⁺ (1 / (2 ^ (j + 1) * δ)))
  -- on the block `j`, the maximal inequality bounds the probability by
  -- `exp (-ε j ^ 2 / (2 ^ (j + 2) c)) ≤ 2 δ * 2 ^ j exp (-2 ^ j Δ ^ 2 / (4 c))`, and these sum to
  -- at most `12 c δ / Δ ^ 2`
  calc μ {ω | ∃ s : ℕ, 0 < s ∧
        (∑ k ∈ range s, Y k ω) / s + √(4 * c / s * log⁺ (1 / (s * δ))) + Δ ≤ 0}
  _ ≤ μ (⋃ j, {ω | ∃ n ≤ 2 ^ (j + 1), ε j ≤ ∑ k ∈ range n, -Y k ω}) := by
    refine measure_mono fun ω ⟨s, hs, h⟩ ↦ Set.mem_iUnion.2 ⟨Nat.log 2 s, s,
      (Nat.lt_pow_succ_log_self (by norm_num) s).le, h_block hs h⟩
  _ ≤ ∑' j, μ {ω | ∃ n ≤ 2 ^ (j + 1), ε j ≤ ∑ k ∈ range n, -Y k ω} := measure_iUnion_le _
  _ ≤ ∑' j, ENNReal.ofReal (2 * δ * (2 ^ j * exp (-(2 ^ j * (Δ ^ 2 / (4 * c)))))) :=
    ENNReal.tsum_le_tsum fun j ↦ (measure_exists_le_sum_le_of_hasCondSubgaussianMGF hY' hsubG'
      (by positivity) _).trans (ENNReal.ofReal_le_ofReal (exp_neg_sq_div_le hc hδ hΔ.le j))
  _ ≤ ENNReal.ofReal (12 * c * δ / Δ ^ 2) := by
    refine ENNReal.tsum_le_of_sum_range_le fun m ↦ ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ by positivity, ← mul_sum]
    refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left
      (sum_range_two_pow_mul_exp_neg_le (by positivity) m) (by positivity)).trans_eq ?_)
    field_simp
    ring

omit [StandardBorelSpace Ω] in
/-- **Peeling bound for sub-Gaussian sums** ([LS, Lemma 9.3]): if `X 0, X 1, …` are independent
and `c`-sub-Gaussian, then for `δ > 0` and `Δ > 0`, the probability that for some `s ≥ 1` the
sample mean of `X 0, …, X (s - 1)` satisfies
`(∑ k < s, X k) / s + √(4 c / s * log⁺ (1 / (s δ))) + Δ ≤ 0` is at most `12 c δ / Δ ^ 2`. The book
states the constant `15`, for `δ < 1`. -/
theorem measure_exists_sum_div_add_sqrt_add_le_zero_le_of_iIndepFun [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ) (hX : ∀ n, HasSubgaussianMGF (X n) c μ)
    {δ Δ : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ) :
    μ {ω | ∃ s : ℕ, 0 < s ∧
        (∑ k ∈ range s, X k ω) / s + √(4 * c / s * log⁺ (1 / (s * δ))) + Δ ≤ 0}
      ≤ ENNReal.ofReal (12 * c * δ / Δ ^ 2) := by
  -- transfer to the coordinates of the product space `ℕ → ℝ`, which is standard Borel
  have hX_meas : ∀ n, AEMeasurable (X n) μ := fun n ↦ (hX n).aemeasurable
  set P := Measure.infinitePi fun n ↦ μ.map (X n)
  -- the filtration generated by the coordinates of index `k < n`
  let ℱ' : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → ℝ)) :=
    { seq n := ⨆ k < n, MeasurableSpace.comap (fun x : ℕ → ℝ ↦ x k) inferInstance
      mono' _ _ hij := biSup_mono fun _ hk ↦ lt_of_lt_of_le hk hij
      le' _ := iSup₂_le fun k _ ↦ (measurable_pi_apply k).comap_le }
  have hY : ∀ n, Measurable[ℱ' (n + 1)] (fun x : ℕ → ℝ ↦ x n) := fun n ↦
    (comap_measurable _).mono (le_iSup₂ (f := fun k (_ : k < n + 1) ↦
      MeasurableSpace.comap (fun x : ℕ → ℝ ↦ x k) inferInstance) n n.lt_succ_self) le_rfl
  have h_iIndep : iIndep (fun k ↦ MeasurableSpace.comap (fun x : ℕ → ℝ ↦ x k) inferInstance) P :=
    (iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_infinitePi (X := fun _ ↦ id) fun _ ↦ measurable_id)
  have hsubG : ∀ n, HasCondSubgaussianMGF (ℱ' n) (ℱ'.le n) (fun x : ℕ → ℝ ↦ x n) c P := by
    intro n
    have h_sub : HasSubgaussianMGF (fun x : ℕ → ℝ ↦ x n) c P := by
      rw [← HasSubgaussianMGF.id_map_iff (measurable_pi_apply n).aemeasurable,
        Measure.infinitePi_map_eval]
      exact (HasSubgaussianMGF.id_map_iff (hX_meas n)).2 (hX n)
    have h_ind := indep_iSup_of_disjoint (fun k ↦ (measurable_pi_apply k).comap_le) h_iIndep
      (S := {n}) (T := Set.Iio n) (by simp)
    simp only [Set.mem_singleton_iff, iSup_iSup_eq_left, Set.mem_Iio] at h_ind
    exact h_sub.hasCondSubgaussianMGF_of_indep (measurable_pi_apply n) h_ind
  set E : Set (ℕ → ℝ) := {x | ∃ s : ℕ, 0 < s ∧
    (∑ k ∈ range s, x k) / s + √(4 * c / s * log⁺ (1 / (s * δ))) + Δ ≤ 0}
  have h_map := Measure.le_map_apply (aemeasurable_pi_iff.2 hX_meas) E
  rw [Set.preimage_ofPred_eq, h_indep.map_fun_eq_infinitePi_map₀' hX_meas] at h_map
  exact h_map.trans
    (measure_exists_sum_div_add_sqrt_add_le_zero_le_of_hasCondSubgaussianMGF hY hsubG hδ hΔ)

end LMLExplore
