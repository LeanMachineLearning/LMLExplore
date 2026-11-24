/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Martingale.TestSupermartingale
public import LMLExplore.Probability.Martingale.Ville
public import LMLExplore.Probability.Moments.MGF.Bound

/-!
# Exponential supermartingales under conditional bounds on the moment generating function

Let `ℱ` be a filtration and `X` a real process with `X n` `ℱ (n + 1)`-measurable. For a process of
weights `w` adapted to `ℱ` (so that `w n` is known when `X n` is drawn), a parameter `t` and a
function `ψ`, the *bets* `exp (t * w n * X n - ψ (t * w n))` have a parameter `t * w n` chosen
from the past. On any measurable space, if under every member of a set of measures each bet is a
conditional e-variable given `ℱ n`, the process
`exp (t * ∑ k < n, w k * X k - ∑ k < n, ψ (t * w k))`
is an `ℝ≥0∞`-valued supermartingale under each of them: it is the wealth of the gambler who
reinvests everything in these bets. This is the set-integral form of the exponential
supermartingale of [HRMS20, §2.1], with no regularity of the conditional laws.

On a standard Borel space, a bound on the conditional moment generating function by `exp ψ` on a
set of parameters `Λ` given `ℱ n` (`LMLExplore.HasCondMGFBound`) makes every bet at an
`ℱ n`-measurable parameter with values in `Λ` a conditional e-variable. With `t * w n ∈ Λ`, the
process above is then a real nonnegative supermartingale with initial value `1`, and Ville's
inequality gives
`P(∃ n, x ≤ t * ∑ k < n, w k * X k - ∑ k < n, ψ (t * w k)) ≤ exp (-x)`.

With `ψ t = c t ^ 2 / 2` on `ℝ` this is the exponential supermartingale of conditionally
sub-Gaussian increments (`LMLExplore.supermartingale_exp_sum_mul_of_hasCondSubgaussianMGF`). With
weights in `{0, 1}`, for instance the indicators `𝟙{A k = a}` that an arm `a` is pulled, and
`ψ 0 = 0`, the exponent is `t S n - N n ψ t` for the sum `S n` of the selected variables and their
number `N n`: these are the time-uniform Chernoff bounds of the observations of one arm along a run
of any sampling rule, with `ψ` the cumulant generating function of a law dominating them.

## Main statements

* `LMLExplore.isENNSupermartingale_exp_mul_sum_sub_sum`: on any measurable space, the exponential
  process of bets that are conditional e-variables is an `ℝ≥0∞`-valued supermartingale.
* `LMLExplore.HasCondMGFBound.isCondEVar_exp_mul_sub`: a conditional bound on the moment
  generating function makes the bet `exp (s * X - ψ s)` at a known parameter `s` a conditional
  e-variable.
* `LMLExplore.supermartingale_exp_mul_sum_sub_sum_of_hasCondMGFBound`: the exponential
  supermartingale under a conditional bound on the moment generating function.
* `LMLExplore.measure_exists_le_mul_sum_sub_sum_of_hasCondMGFBound`: its time-uniform bound
  `P(∃ n, x ≤ t * ∑ k < n, w k * X k - ∑ k < n, ψ (t * w k)) ≤ exp (-x)`.
* `LMLExplore.measure_exists_le_mul_sum_sub_sum_mul_of_hasCondMGFBound`: the bound for weights in
  `{0, 1}`, `P(∃ n, x ≤ t * ∑ k < n, w k * X k - (∑ k < n, w k) * ψ t) ≤ exp (-x)`.

## References

* [HRMS20] S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, *Time-uniform Chernoff bounds via
  nonnegative supermartingales*, Probability Surveys 17 (2020), 257–317, Section 2 (the
  exponential process of a sub-`ψ` process is a supermartingale) and Lemma 1 (Ville's inequality).
* The exponential supermartingale under a conditional bound on the moment generating function
  generalizes the sub-Gaussian case adapted from the formalization in the LMLPapers project
  (`LMLPapers/LeanMachineLearning/ForMathlib/Probability/Martingale/SubgaussianSum.lean`).
-/

public section

open MeasureTheory ProbabilityTheory Finset Real
open scoped ENNReal

namespace LMLExplore

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ mΩ} {X w : ℕ → Ω → ℝ} {ψ : ℝ → ℝ} {Λ : Set ℝ} {t : ℝ}

/-- **Exponential supermartingale of conditional bets.** On any measurable space, let `X n` be
`ℱ (n + 1)`-measurable, the weights `w` adapted and `ψ (t * w n)` `ℱ n`-measurable. If, under
every member of a set of measures `𝒩`, each bet `exp (t * w n * X n - ψ (t * w n))` is a
conditional e-variable given `ℱ n`, then
`n ↦ exp (t * ∑ k < n, w k * X k - ∑ k < n, ψ (t * w k))` is an `ℝ≥0∞`-valued supermartingale under
every member of `𝒩`. -/
theorem isENNSupermartingale_exp_mul_sum_sub_sum {𝒩 : Set (Measure Ω)}
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n)) (hw : Adapted ℱ w)
    (hψw : ∀ n, Measurable[ℱ n] fun ω ↦ ψ (t * w n ω))
    (h : ∀ n, IsCondEVar
      (fun ω ↦ ENNReal.ofReal (exp (t * w n ω * X n ω - ψ (t * w n ω)))) (ℱ n) 𝒩) :
    IsENNSupermartingale (fun n ω ↦ ENNReal.ofReal (exp (t * ∑ k ∈ range n, w k ω * X k ω
      - ∑ k ∈ range n, ψ (t * w k ω)))) ℱ 𝒩 := by
  -- the process is the product of the bets of the rounds before `n`
  have h_eq : (fun n ω ↦ ENNReal.ofReal (exp (t * ∑ k ∈ range n, w k ω * X k ω
      - ∑ k ∈ range n, ψ (t * w k ω)))) = fun n ω ↦
      1 * ∏ k ∈ range n, ENNReal.ofReal (exp (t * w k ω * X k ω - ψ (t * w k ω))) := by
    ext n ω
    rw [one_mul, ← ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (exp_pos _).le, ← exp_sum,
      sum_sub_distrib]
    simp only [mul_sum, mul_assoc]
  rw [h_eq]
  refine isENNSupermartingale_mul_prod measurable_const (fun n ↦ ?_) h
  have hw' : Measurable[ℱ (n + 1)] (w n) := hw.measurable_le (by omega)
  exact (((hw'.const_mul t).mul (hX n)).sub
    ((hψw n).mono (ℱ.mono (by omega)) le_rfl)).exp.ennreal_ofReal

/-- **Conditional bounds on the moment generating function give conditional bets.** If `X` is
measurable with moment generating function conditionally bounded by `exp ψ` on `Λ` given `m`,
then for every `m`-measurable parameter `s` with values in `Λ` almost surely and `ψ ∘ s`
`m`-measurable, the bet `exp (s * X - ψ s)` is a conditional e-variable given `m`. -/
theorem HasCondMGFBound.isCondEVar_exp_mul_sub [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} {hm : m ≤ mΩ} {X : Ω → ℝ} (h : HasCondMGFBound m hm X ψ Λ μ)
    (hX : Measurable[mΩ] X) {s : Ω → ℝ} (hs : Measurable[m] s) (hsΛ : ∀ᵐ ω ∂μ, s ω ∈ Λ)
    (hψs : Measurable[m] fun ω ↦ ψ (s ω)) :
    IsCondEVar (fun ω ↦ ENNReal.ofReal (exp (s ω * X ω - ψ (s ω)))) m {μ} := by
  refine ⟨((hs.mono hm le_rfl).mul hX).sub (hψs.mono hm le_rfl) |>.exp.ennreal_ofReal, ?_⟩
  rintro _ rfl A hA
  -- with `g = 𝟙_A exp (-ψ ∘ s)`, the conditional bound reads `∫⁻ g exp (s X) ≤ ∫⁻ g exp (ψ ∘ s)`
  set g : Ω → ℝ≥0∞ := A.indicator fun ω ↦ ENNReal.ofReal (exp (-ψ (s ω)))
  have hl (ω : Ω) : A.indicator (fun ω ↦ ENNReal.ofReal (exp (s ω * X ω - ψ (s ω)))) ω =
      g ω * ENNReal.ofReal (exp (s ω * X ω)) := by
    by_cases hω : ω ∈ A <;>
      simp [g, hω, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add, sub_eq_neg_add]
  have hr (ω : Ω) : g ω * ENNReal.ofReal (exp (ψ (s ω))) = A.indicator 1 ω := by
    by_cases hω : ω ∈ A <;> simp [g, hω, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
  rw [← lintegral_indicator (hm _ hA)]
  simp_rw [hl]
  refine (h.lintegral_mul_exp_le hX hs hsΛ (g := g)
    (hψs.neg.exp.ennreal_ofReal.indicator hA)).trans_eq ?_
  simp_rw [hr]
  exact lintegral_indicator_one (hm _ hA)

/-- **Exponential supermartingale.** If `X n` is `ℱ (n + 1)`-measurable with moment generating
function conditionally bounded by `exp ψ` on `Λ` given `ℱ n`, the weights `w` are adapted, and
`t * w n ∈ Λ` almost surely with `ψ (t * w n)` `ℱ n`-measurable, then
`n ↦ exp (t * ∑ k < n, w k * X k - ∑ k < n, ψ (t * w k))` is a supermartingale. -/
theorem supermartingale_exp_mul_sum_sub_sum_of_hasCondMGFBound [StandardBorelSpace Ω]
    [IsFiniteMeasure μ] (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) ψ Λ μ) (hw : Adapted ℱ w)
    (htw : ∀ n, ∀ᵐ ω ∂μ, t * w n ω ∈ Λ) (hψw : ∀ n, Measurable[ℱ n] fun ω ↦ ψ (t * w n ω)) :
    Supermartingale (fun n ω ↦ exp (t * ∑ k ∈ range n, w k ω * X k ω
      - ∑ k ∈ range n, ψ (t * w k ω))) ℱ μ := by
  have h := (isENNSupermartingale_exp_mul_sum_sub_sum hX hw hψw fun n ↦
    (hψ n).isCondEVar_exp_mul_sub ((hX n).mono (ℱ.le _) le_rfl) ((hw n).const_mul t) (htw n)
      (hψw n)).supermartingale_toReal (Set.mem_singleton μ) (by simp)
  simpa only [ENNReal.toReal_ofReal (exp_pos _).le] using h

/-- **Time-uniform Chernoff bound.** Under the hypotheses of
`supermartingale_exp_mul_sum_sub_sum_of_hasCondMGFBound`, for every `x : ℝ`, the probability that
`x ≤ t * ∑ k < n, w k * X k - ∑ k < n, ψ (t * w k)` for some `n` is at most `exp (-x)`. -/
theorem measure_exists_le_mul_sum_sub_sum_of_hasCondMGFBound [StandardBorelSpace Ω]
    [IsProbabilityMeasure μ]
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
theorem measure_exists_le_mul_sum_sub_sum_mul_of_hasCondMGFBound [StandardBorelSpace Ω]
    [IsProbabilityMeasure μ]
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
