/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Martingale.Basic
public import LMLExplore.Probability.Martingale.Ville
public import LMLExplore.Probability.Moments.SubGaussian

/-!
# Exponential supermartingales of sub-Gaussian sums

Let `ℱ` be a filtration on a standard Borel space, `Y` a real process with `Y n`
`ℱ (n + 1)`-measurable and conditionally `c`-sub-Gaussian given `ℱ n` (a sub-Gaussian martingale
difference sequence), and `w` an adapted process of weights. For the weighted sums
`T n = ∑ k < n, w k * Y k`, with quadratic variation `A n = ∑ k < n, w k ^ 2`, the process
`exp (t * T n - c * t ^ 2 * A n / 2)` is a nonnegative supermartingale with initial value `1`, for
every `t : ℝ`. Ville's inequality turns it into concentration bounds that hold simultaneously for
all times.

## Main statements

* `LMLExplore.supermartingale_exp_sum_mul_of_hasCondSubgaussianMGF`: the exponential
  supermartingale.
* `LMLExplore.measure_exists_le_mul_sum_sub_of_hasCondSubgaussianMGF`: with probability at least
  `1 - exp (-x)`, `t * T n - c * t ^ 2 * A n / 2 < x` for all `n` simultaneously.
* `LMLExplore.measure_exists_le_sum_le_of_hasCondSubgaussianMGF`: the maximal inequality
  `P(∃ n ≤ N, ε ≤ ∑ k < n, Y k) ≤ exp (-ε ^ 2 / (2 N c))` for `ε ≥ 0`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Theorem 9.2.
* `supermartingale_exp_sum_mul_of_hasCondSubgaussianMGF` is adapted from the formalization in the
  LMLPapers project
  (`LMLPapers/LeanMachineLearning/ForMathlib/Probability/Martingale/SubgaussianSum.lean`); the two
  consequences of Ville's inequality are new here.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real
open scoped ENNReal NNReal

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

end LMLExplore
