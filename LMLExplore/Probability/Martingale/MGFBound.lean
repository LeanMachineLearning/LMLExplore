/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Martingale.Basic
public import LMLExplore.Probability.Martingale.Ville
public import LMLExplore.Probability.Moments.MGF.Bound

/-!
# Exponential supermartingales under conditional bounds on the moment generating function

Let `ℱ` be a filtration on a standard Borel space and `X` a real process with `X n`
`ℱ (n + 1)`-measurable and with moment generating function conditionally bounded by `exp ψ` on a
set of parameters `Λ` given `ℱ n` (`LMLExplore.HasCondMGFBound`). For a process of weights `w`
adapted to `ℱ` (so that `w n` is known when `X n` is drawn) and a parameter `t` with `t * w n ∈ Λ`,
the process
`exp (t * ∑ k < n, w k * X k - ∑ k < n, ψ (t * w k))`
is a nonnegative supermartingale with initial value `1`, and Ville's inequality gives
`P(∃ n, x ≤ t * ∑ k < n, w k * X k - ∑ k < n, ψ (t * w k)) ≤ exp (-x)`.

With `ψ t = c t ^ 2 / 2` on `ℝ` this is the exponential supermartingale of conditionally
sub-Gaussian increments (`LMLExplore.supermartingale_exp_sum_mul_of_hasCondSubgaussianMGF`). With
weights in `{0, 1}`, for instance the indicators `𝟙{A k = a}` that an arm `a` is pulled, and
`ψ 0 = 0`, the exponent is `t S n - N n ψ t` for the sum `S n` of the selected variables and their
number `N n`: these are the time-uniform Chernoff bounds of the observations of one arm along a run
of any sampling rule, with `ψ` the cumulant generating function of a law dominating them.

## Main statements

* `LMLExplore.supermartingale_exp_mul_sum_sub_sum_of_hasCondMGFBound`: the exponential
  supermartingale.
* `LMLExplore.measure_exists_le_mul_sum_sub_sum_of_hasCondMGFBound`: its time-uniform bound
  `P(∃ n, x ≤ t * ∑ k < n, w k * X k - ∑ k < n, ψ (t * w k)) ≤ exp (-x)`.
* `LMLExplore.measure_exists_le_mul_sum_sub_sum_mul_of_hasCondMGFBound`: the bound for weights in
  `{0, 1}`, `P(∃ n, x ≤ t * ∑ k < n, w k * X k - (∑ k < n, w k) * ψ t) ≤ exp (-x)`.

## References

* S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, *Time-uniform Chernoff bounds via
  nonnegative supermartingales*, Probability Surveys 17 (2020), 257–317, Section 2 (the
  exponential process of a sub-`ψ` process is a supermartingale) and Lemma 1 (Ville's inequality).
* The proof of `supermartingale_exp_mul_sum_sub_sum_of_hasCondMGFBound` generalizes the
  sub-Gaussian case adapted from the formalization in the LMLPapers project
  (`LMLPapers/LeanMachineLearning/ForMathlib/Probability/Martingale/SubgaussianSum.lean`).
-/

public section

open MeasureTheory ProbabilityTheory Finset Real
open scoped ENNReal

namespace LMLExplore

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {μ : Measure Ω}
  {ℱ : Filtration ℕ mΩ} {X w : ℕ → Ω → ℝ} {ψ : ℝ → ℝ} {Λ : Set ℝ} {t : ℝ}

/-- **Exponential supermartingale.** If `X n` is `ℱ (n + 1)`-measurable with moment generating
function conditionally bounded by `exp ψ` on `Λ` given `ℱ n`, the weights `w` are adapted, and
`t * w n ∈ Λ` almost surely with `ψ (t * w n)` `ℱ n`-measurable, then
`n ↦ exp (t * ∑ k < n, w k * X k - ∑ k < n, ψ (t * w k))` is a supermartingale. -/
theorem supermartingale_exp_mul_sum_sub_sum_of_hasCondMGFBound [IsFiniteMeasure μ]
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) ψ Λ μ) (hw : Adapted ℱ w)
    (htw : ∀ n, ∀ᵐ ω ∂μ, t * w n ω ∈ Λ) (hψw : ∀ n, Measurable[ℱ n] fun ω ↦ ψ (t * w n ω)) :
    Supermartingale (fun n ω ↦ exp (t * ∑ k ∈ range n, w k ω * X k ω
      - ∑ k ∈ range n, ψ (t * w k ω))) ℱ μ := by
  -- the sum of the rounds `Z k = t * w k * X k - ψ (t * w k)`
  have h_eq : (fun n ω ↦ exp (t * ∑ k ∈ range n, w k ω * X k ω
      - ∑ k ∈ range n, ψ (t * w k ω))) = fun n ω ↦
      exp (∑ k ∈ range n, (t * w k ω * X k ω - ψ (t * w k ω))) := by
    ext n ω
    simp only [sum_sub_distrib, mul_sum, mul_assoc]
  rw [h_eq]
  refine supermartingale_exp_sum_of_lintegral_mul_exp_le (fun n ↦ ?_) fun n g hg ↦ ?_
  · have hw' : Measurable[ℱ (n + 1)] (w n) := hw.measurable_le (by omega)
    exact ((hw'.const_mul t).mul (hX n)).sub ((hψw n).mono (ℱ.mono (by omega)) le_rfl)
  -- `g * exp (Z n) = g * exp (-ψ (t * w n)) * exp (t * w n * X n)`
  have hs : Measurable[ℱ n] (fun ω ↦ t * w n ω) := (hw n).const_mul t
  set G : Ω → ℝ≥0∞ := fun ω ↦ g ω * ENNReal.ofReal (exp (-ψ (t * w n ω))) with hG_def
  have hG : Measurable[ℱ n] G := hg.mul (hψw n).neg.exp.ennreal_ofReal
  calc ∫⁻ ω, g ω * ENNReal.ofReal (exp (t * w n ω * X n ω - ψ (t * w n ω))) ∂μ
      = ∫⁻ ω, G ω * ENNReal.ofReal (exp (t * w n ω * X n ω)) ∂μ := by
        simp only [hG_def, mul_assoc, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add,
          neg_add_eq_sub]
    _ ≤ ∫⁻ ω, G ω * ENNReal.ofReal (exp (ψ (t * w n ω))) ∂μ :=
        (hψ n).lintegral_mul_exp_le ((hX n).mono (ℱ.le _) le_rfl) hs (htw n) hG
    _ = ∫⁻ ω, g ω ∂μ := by
        simp [hG_def, mul_assoc, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]

/-- **Time-uniform Chernoff bound.** Under the hypotheses of
`supermartingale_exp_mul_sum_sub_sum_of_hasCondMGFBound`, for every `x : ℝ`, the probability that
`x ≤ t * ∑ k < n, w k * X k - ∑ k < n, ψ (t * w k)` for some `n` is at most `exp (-x)`. -/
theorem measure_exists_le_mul_sum_sub_sum_of_hasCondMGFBound [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) ψ Λ μ) (hw : Adapted ℱ w)
    (htw : ∀ n, ∀ᵐ ω ∂μ, t * w n ω ∈ Λ) (hψw : ∀ n, Measurable[ℱ n] fun ω ↦ ψ (t * w n ω))
    (x : ℝ) :
    μ {ω | ∃ n, x ≤ t * ∑ k ∈ range n, w k ω * X k ω - ∑ k ∈ range n, ψ (t * w k ω)}
      ≤ ENNReal.ofReal (exp (-x)) := by
  have h := (supermartingale_exp_mul_sum_sub_sum_of_hasCondMGFBound hX hψ hw htw
    hψw).measure_exists_le_le (fun n ↦ ae_of_all _ fun ω ↦ (exp_pos _).le) (exp_pos x)
  simpa [← exp_neg] using h

/-- **Time-uniform Chernoff bound for selected variables.** If `X n` is `ℱ (n + 1)`-measurable
with moment generating function conditionally bounded by `exp ψ` on `Λ` given `ℱ n`, with
`ψ 0 = 0` and `0, t ∈ Λ`, and the weights `w` are adapted with values in `{0, 1}`, then for every
`x : ℝ`, the probability that `x ≤ t * ∑ k < n, w k * X k - (∑ k < n, w k) * ψ t` for some `n` is
at most `exp (-x)`. -/
theorem measure_exists_le_mul_sum_sub_sum_mul_of_hasCondMGFBound [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) ψ Λ μ) (hw : Adapted ℱ w)
    (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hψ0 : ψ 0 = 0) (h0 : 0 ∈ Λ) (ht : t ∈ Λ) (x : ℝ) :
    μ {ω | ∃ n, x ≤ t * ∑ k ∈ range n, w k ω * X k ω - (∑ k ∈ range n, w k ω) * ψ t}
      ≤ ENNReal.ofReal (exp (-x)) := by
  -- for weights in `{0, 1}`, `ψ (t * w k) = w k * ψ t`
  have hψw : ∀ n ω, ψ (t * w n ω) = w n ω * ψ t := fun n ω ↦ by
    rcases hw01 n ω with h | h <;> simp [h, hψ0]
  have h := measure_exists_le_mul_sum_sub_sum_of_hasCondMGFBound hX hψ hw (t := t)
    (fun n ↦ ae_of_all _ fun ω ↦ by rcases hw01 n ω with h | h <;> simp [h, h0, ht])
    (fun n ↦ by simp_rw [hψw]; exact (hw n).mul_const _) x
  simpa only [hψw, ← sum_mul] using h

end LMLExplore
