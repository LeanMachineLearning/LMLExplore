/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Algebra.BigOperators.Ring.Finset
public import LMLExplore.Analysis.SpecialFunctions.Exp
public import LMLExplore.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner
public import LMLExplore.Probability.Martingale.Basic
public import LMLExplore.Probability.Martingale.Ville

/-!
# Concentration of implicit-exploration estimates

Let `ℱ` be a filtration and, for every round `t` and every index `i` of a finite type `ι`, let
`X t i ≥ 0` be an integrable `ℱ (t + 1)`-measurable variable whose conditional expectation given
`ℱ t` is at most `y t i`, with `y t i` `ℱ t`-measurable. Let `w t i ≥ 0` and `l t i` be
`ℱ t`-measurable with `w t i * X t i ≤ 2 * l t i`, and assume that at each round at most one of
the products `w t i * X t i` is nonzero: `(w t i * X t i) * (w t j * X t j) = 0` for `i ≠ j`.
Then the process
`exp (∑ t < n, ∑ i, w t i * (X t i / (1 + l t i) - y t i))`
is a supermartingale, and with probability at least `1 - δ`, for all `n` simultaneously,
`∑ t < n, ∑ i, w t i * (X t i / (1 + l t i) - y t i) < log (1 / δ)` [LS, Lemma 12.2].

The discount `1 / (1 + l t i)` is what makes this a one-sided bound without any variance term:
`exp (x / (1 + l)) ≤ 1 + x` for `0 ≤ x ≤ 2 l` [LS, Lemma 12.5], and the vanishing of the products
turns `∏ i, (1 + w t i * X t i)` into `1 + ∑ i, w t i * X t i`, whose conditional expectation is at
most `1 + ∑ i, w t i * y t i ≤ exp (∑ i, w t i * y t i)`.

The bound applies to the estimates `X t i = 𝟙{A t = i} y t i / P t i` of losses `y t i ∈ [0, 1]`
of an adversarial bandit, where `A t` is drawn from the probability vector `P t`: the indicators of
distinct arms have vanishing products, and with `w t i = 2 γ` and `l t i = γ / P t i` the
summands are `2 γ (𝟙{A t = i} y t i / (P t i + γ) - y t i)`. This controls the deviations of the
cumulative loss estimates of Exp3-IX [LS, Lemma 12.3].

## Main statements

* `LMLExplore.lintegral_mul_exp_sum_mul_div_one_add_sub_le`: one round [LS, (12.10)], the
  conditional expectation of `exp (∑ i, w i * (X i / (1 + l i) - y i))` is at most `1`.
* `LMLExplore.supermartingale_exp_sum_sum_mul_div_one_add_sub`: the exponential supermartingale.
* `LMLExplore.measure_exists_le_sum_sum_mul_div_one_add_sub_le`: the time-uniform bound: for all
  `x : ℝ`, the probability that `x ≤ ∑ t < n, ∑ i, w t i * (X t i / (1 + l t i) - y t i)` for
  some `n` is at most `exp (-x)`.
* `LMLExplore.measure_log_one_div_le_sum_sum_mul_div_one_add_sub_le`: [LS, Lemma 12.2], the
  probability that the sum up to a fixed horizon is at least `log (1 / δ)` is at most `δ`.

## Implementation notes

[LS] allows weights `w t i` and variables `X t i` of any sign with `0 ≤ w t i * X t i`, and states
the negative correlation as `E[∏ i ∈ S, X t i | ℱ t] ≤ 0` for every `S` with at least two
elements. Its proof pulls the predictable weights out of `E[∏ i ∈ S, w t i * X t i | ℱ t]`, which
needs their products to be nonnegative. Here `w t i ≥ 0` and `X t i ≥ 0`, as for Exp3-IX, and for
the nonnegative variables `w t i * X t i` the negative correlation condition of the proof says
that their pairwise products vanish almost surely, which is the hypothesis. The conditional
expectations of [LS] are equalities, of which only the upper bounds are used, and the `y t i` may
be random. The bound holds for all horizons simultaneously, by Ville's inequality, where [LS]
applies Markov's inequality at a fixed horizon.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemmas 12.2, 12.3 and 12.5.
* G. Neu, *Explore no more: improved high-probability regret bounds for non-stochastic
  bandits*, NeurIPS 2015, Lemma 1.
-/

public section

open MeasureTheory Finset Real
open scoped ENNReal

namespace LMLExplore

variable {Ω ι : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Fintype ι]
  {ℱ : Filtration ℕ mΩ} {X w l y : ℕ → ι → Ω → ℝ}

/-- The sum `∑ i, w t i * (X t i / (1 + l t i) - y t i)` of round `t` is `ℱ (t + 1)`-measurable
when the `X t` are `ℱ (t + 1)`-measurable and the `w t`, `l t` and `y t` are `ℱ t`-measurable. -/
private lemma measurable_sum_mul_div_one_add_sub (hX : ∀ t i, Measurable[ℱ (t + 1)] (X t i))
    (hw : ∀ t i, Measurable[ℱ t] (w t i)) (hl : ∀ t i, Measurable[ℱ t] (l t i))
    (hy : ∀ t i, Measurable[ℱ t] (y t i)) (t : ℕ) :
    Measurable[ℱ (t + 1)] fun ω ↦ ∑ i, w t i ω * (X t i ω / (1 + l t i ω) - y t i ω) := by
  have hle : ℱ t ≤ ℱ (t + 1) := ℱ.mono (by omega)
  exact Finset.measurable_fun_sum _ fun i _ ↦ ((hw t i).mono hle le_rfl).mul (((hX t i).div
    (measurable_const.add ((hl t i).mono hle le_rfl))).sub ((hy t i).mono hle le_rfl))

/-- The one-round bound behind [LS, Lemma 12.2]: if `0 ≤ w i * X i ≤ 2 * l i` for all `i` and
the products `(w i * X i) * (w j * X j)` of distinct `i, j` vanish, then
`exp (∑ i, w i * X i / (1 + l i)) ≤ 1 + ∑ i, w i * X i`. -/
private lemma exp_sum_mul_div_one_add_le {w X l : ι → ℝ} (hwX : ∀ i, 0 ≤ w i * X i)
    (hwl : ∀ i, w i * X i ≤ 2 * l i) (hmul : ∀ i j, i ≠ j → w i * X i * (w j * X j) = 0) :
    exp (∑ i, w i * X i / (1 + l i)) ≤ 1 + ∑ i, w i * X i := by
  rw [exp_sum, ← prod_one_add_of_mul_eq_zero fun i _ j _ hij ↦ hmul i j hij]
  exact prod_le_prod₀ (fun i _ ↦ (exp_pos _).le)
    fun i _ ↦ exp_div_one_add_le_one_add (hwX i) (hwl i)

/-- For `a i ≥ 0` and `z i ≥ 0`,
`ofReal r * (1 + ∑ i, ofReal (a i) * ofReal (z i)) = ofReal (r * (1 + ∑ i, a i * z i))`. -/
private lemma ofReal_mul_one_add_sum_ofReal_mul {a z : ι → ℝ} (r : ℝ) (ha : ∀ i, 0 ≤ a i)
    (hz : ∀ i, 0 ≤ z i) :
    ENNReal.ofReal r * (1 + ∑ i, ENNReal.ofReal (a i) * ENNReal.ofReal (z i)) =
      ENNReal.ofReal (r * (1 + ∑ i, a i * z i)) := by
  have haz : ∀ i, 0 ≤ a i * z i := fun i ↦ mul_nonneg (ha i) (hz i)
  rw [← sum_congr rfl fun i _ ↦ ENNReal.ofReal_mul (ha i),
    ← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ haz i, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (sum_nonneg fun i _ ↦ haz i), ENNReal.ofReal_mul']
  exact add_nonneg zero_le_one (sum_nonneg fun i _ ↦ haz i)

/-- The expansion
`∫⁻ G * (1 + ∑ i, ofReal (a i) * ofReal (z i)) = ∫⁻ G + ∑ i, ∫⁻ G * ofReal (a i) * ofReal (z i)`
for measurable `G` and a.e.-measurable `G * ofReal (a i) * ofReal (z i)`. -/
private lemma lintegral_mul_one_add_sum {G : Ω → ℝ≥0∞} {a z : ι → Ω → ℝ} (hG : Measurable G)
    (haz : ∀ i, AEMeasurable (fun ω ↦ G ω * ENNReal.ofReal (a i ω) * ENNReal.ofReal (z i ω)) μ) :
    ∫⁻ ω, G ω * (1 + ∑ i, ENNReal.ofReal (a i ω) * ENNReal.ofReal (z i ω)) ∂μ =
      ∫⁻ ω, G ω ∂μ + ∑ i, ∫⁻ ω, G ω * ENNReal.ofReal (a i ω) * ENNReal.ofReal (z i ω) ∂μ := by
  simp only [mul_add, mul_one, mul_sum, ← mul_assoc]
  rw [lintegral_add_left hG, lintegral_finsetSum' _ fun i _ ↦ haz i]

/-- **One round of implicit exploration** [LS, (12.10)]. Let `m` be a sub-σ-algebra, `X i ≥ 0`
integrable with `μ[X i | m] ≤ y i`, `w i ≥ 0` and `y i` `m`-measurable, and `l i` arbitrary with
`w i * X i ≤ 2 * l i`. If the products `(w i * X i) * (w j * X j)` of distinct `i, j` vanish, then
the conditional expectation of `exp (∑ i, w i * (X i / (1 + l i) - y i))` given `m` is at most `1`:
for every `m`-measurable `g : Ω → ℝ≥0∞`,
`∫⁻ g * exp (∑ i, w i * (X i / (1 + l i) - y i)) ≤ ∫⁻ g`. -/
theorem lintegral_mul_exp_sum_mul_div_one_add_sub_le (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {X w l y : ι → Ω → ℝ} (hX_int : ∀ i, Integrable (X i) μ)
    (hX_nonneg : ∀ i, 0 ≤ᵐ[μ] X i) (hXy : ∀ i, μ[X i | m] ≤ᵐ[μ] y i)
    (hw : ∀ i, Measurable[m] (w i)) (hy : ∀ i, Measurable[m] (y i))
    (hw_nonneg : ∀ i, 0 ≤ᵐ[μ] w i) (hwl : ∀ i, ∀ᵐ ω ∂μ, w i ω * X i ω ≤ 2 * l i ω)
    (hmul : ∀ i j, i ≠ j → ∀ᵐ ω ∂μ, w i ω * X i ω * (w j ω * X j ω) = 0)
    {g : Ω → ℝ≥0∞} (hg : Measurable[m] g) :
    ∫⁻ ω, g ω * ENNReal.ofReal (exp (∑ i, w i ω * (X i ω / (1 + l i ω) - y i ω))) ∂μ ≤
      ∫⁻ ω, g ω ∂μ := by
  -- the `m`-measurable factor `g * exp (-∑ i, w i * y i)`
  set G : Ω → ℝ≥0∞ := fun ω ↦ g ω * ENNReal.ofReal (exp (-∑ i, w i ω * y i ω)) with hG_def
  have hG : Measurable[m] G :=
    hg.mul (Finset.measurable_fun_sum _ fun i _ ↦ (hw i).mul (hy i)).neg.exp.ennreal_ofReal
  have hGw : ∀ i, Measurable[m] fun ω ↦ G ω * ENNReal.ofReal (w i ω) :=
    fun i ↦ hG.mul (hw i).ennreal_ofReal
  have hGm : Measurable G := hG.mono hm le_rfl
  have hy_nonneg : ∀ i, 0 ≤ᵐ[μ] y i := fun i ↦ by
    filter_upwards [condExp_nonneg (m := m) (hX_nonneg i), hXy i] with ω h₁ h₂
    exact h₁.trans h₂
  have hall : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ w i ω ∧ 0 ≤ X i ω ∧ 0 ≤ y i ω ∧ w i ω * X i ω ≤ 2 * l i ω := by
    simp only [ae_all_iff]
    exact fun i ↦ (((hw_nonneg i).and (hX_nonneg i)).and ((hy_nonneg i).and (hwl i))).mono
      fun ω h ↦ ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  have hall_mul : ∀ᵐ ω ∂μ, ∀ i j, i ≠ j → w i ω * X i ω * (w j ω * X j ω) = 0 := by
    simp only [ae_all_iff]
    exact hmul
  -- `exp (∑ i, w i * (X i / (1 + l i) - y i)) ≤ exp (-∑ i, w i * y i) * (1 + ∑ i, w i * X i)`
  have h_le : ∀ᵐ ω ∂μ, g ω * ENNReal.ofReal (exp (∑ i, w i ω * (X i ω / (1 + l i ω) - y i ω))) ≤
      G ω * (1 + ∑ i, ENNReal.ofReal (w i ω) * ENNReal.ofReal (X i ω)) := by
    filter_upwards [hall, hall_mul] with ω hω hω_mul
    have hwX : ∀ i, 0 ≤ w i ω * X i ω := fun i ↦ mul_nonneg (hω i).1 (hω i).2.1
    rw [hG_def, mul_assoc,
      ofReal_mul_one_add_sum_ofReal_mul _ (fun i ↦ (hω i).1) fun i ↦ (hω i).2.1]
    gcongr
    simp only [mul_sub, sum_sub_distrib, mul_div_assoc', sub_eq_neg_add _ (∑ i, w i ω * y i ω),
      exp_add]
    exact mul_le_mul_of_nonneg_left
      (exp_sum_mul_div_one_add_le hwX (fun i ↦ (hω i).2.2.2) hω_mul) (exp_pos _).le
  -- `exp (-∑ i, w i * y i) * (1 + ∑ i, w i * y i) ≤ 1`
  have h_one : ∀ᵐ ω ∂μ, G ω * (1 + ∑ i, ENNReal.ofReal (w i ω) * ENNReal.ofReal (y i ω)) ≤ g ω := by
    filter_upwards [hall] with ω hω
    rw [hG_def, mul_assoc,
      ofReal_mul_one_add_sum_ofReal_mul _ (fun i ↦ (hω i).1) fun i ↦ (hω i).2.2.1]
    refine mul_le_of_le_one_right' (ENNReal.ofReal_le_one.2 ?_)
    rw [exp_neg, inv_mul_le_one₀ (exp_pos _)]
    linarith [add_one_le_exp (∑ i, w i ω * y i ω)]
  -- the conditional expectation of `w i * X i` given `m` is at most `w i * y i`
  calc ∫⁻ ω, g ω * ENNReal.ofReal (exp (∑ i, w i ω * (X i ω / (1 + l i ω) - y i ω))) ∂μ
      ≤ ∫⁻ ω, G ω * (1 + ∑ i, ENNReal.ofReal (w i ω) * ENNReal.ofReal (X i ω)) ∂μ :=
        lintegral_mono_ae h_le
    _ = ∫⁻ ω, G ω ∂μ + ∑ i, ∫⁻ ω, G ω * ENNReal.ofReal (w i ω) * ENNReal.ofReal (X i ω) ∂μ :=
        lintegral_mul_one_add_sum hGm fun i ↦
          ((hGw i).mono hm le_rfl).aemeasurable.mul (hX_int i).1.aemeasurable.ennreal_ofReal
    _ ≤ ∫⁻ ω, G ω ∂μ + ∑ i, ∫⁻ ω, G ω * ENNReal.ofReal (w i ω) * ENNReal.ofReal (y i ω) ∂μ :=
        add_le_add le_rfl <| sum_le_sum fun i _ ↦
          lintegral_mul_ofReal_le_of_condExp_le hm (hX_int i) (hX_nonneg i) (hXy i) (hGw i)
    _ = ∫⁻ ω, G ω * (1 + ∑ i, ENNReal.ofReal (w i ω) * ENNReal.ofReal (y i ω)) ∂μ :=
        (lintegral_mul_one_add_sum hGm fun i ↦
          (((hGw i).mono hm le_rfl).mul ((hy i).mono hm le_rfl).ennreal_ofReal).aemeasurable).symm
    _ ≤ ∫⁻ ω, g ω ∂μ := lintegral_mono_ae h_one

/-- **The exponential supermartingale of implicit exploration** [LS, proof of Lemma 12.2]. Let
`X t i ≥ 0` be integrable and `ℱ (t + 1)`-measurable with `μ[X t i | ℱ t] ≤ y t i`, and let
`w t i ≥ 0`, `l t i` and `y t i` be `ℱ t`-measurable with `w t i * X t i ≤ 2 * l t i`. If the
products `(w t i * X t i) * (w t j * X t j)` of distinct `i, j` vanish, then
`n ↦ exp (∑ t < n, ∑ i, w t i * (X t i / (1 + l t i) - y t i))` is a supermartingale. -/
theorem supermartingale_exp_sum_sum_mul_div_one_add_sub [IsFiniteMeasure μ]
    (hX : ∀ t i, Measurable[ℱ (t + 1)] (X t i)) (hX_int : ∀ t i, Integrable (X t i) μ)
    (hX_nonneg : ∀ t i, 0 ≤ᵐ[μ] X t i) (hXy : ∀ t i, μ[X t i | ℱ t] ≤ᵐ[μ] y t i)
    (hw : ∀ t i, Measurable[ℱ t] (w t i)) (hl : ∀ t i, Measurable[ℱ t] (l t i))
    (hy : ∀ t i, Measurable[ℱ t] (y t i)) (hw_nonneg : ∀ t i, 0 ≤ᵐ[μ] w t i)
    (hwl : ∀ t i, ∀ᵐ ω ∂μ, w t i ω * X t i ω ≤ 2 * l t i ω)
    (hmul : ∀ t i j, i ≠ j → ∀ᵐ ω ∂μ, w t i ω * X t i ω * (w t j ω * X t j ω) = 0) :
    Supermartingale
      (fun n ω ↦ exp (∑ t ∈ range n, ∑ i, w t i ω * (X t i ω / (1 + l t i ω) - y t i ω))) ℱ μ := by
  exact supermartingale_exp_sum_of_lintegral_mul_exp_le
    (measurable_sum_mul_div_one_add_sub hX hw hl hy) fun n _ hg ↦
    lintegral_mul_exp_sum_mul_div_one_add_sub_le (ℱ.le n) (hX_int n) (hX_nonneg n) (hXy n)
      (hw n) (hy n) (hw_nonneg n) (hwl n) (hmul n) hg

/-- **Time-uniform concentration of implicit-exploration estimates.** Under the hypotheses of
`supermartingale_exp_sum_sum_mul_div_one_add_sub`, for every `x : ℝ`, the probability that
`x ≤ ∑ t < n, ∑ i, w t i * (X t i / (1 + l t i) - y t i)` for some `n` is at most `exp (-x)`. -/
theorem measure_exists_le_sum_sum_mul_div_one_add_sub_le [IsProbabilityMeasure μ]
    (hX : ∀ t i, Measurable[ℱ (t + 1)] (X t i)) (hX_int : ∀ t i, Integrable (X t i) μ)
    (hX_nonneg : ∀ t i, 0 ≤ᵐ[μ] X t i) (hXy : ∀ t i, μ[X t i | ℱ t] ≤ᵐ[μ] y t i)
    (hw : ∀ t i, Measurable[ℱ t] (w t i)) (hl : ∀ t i, Measurable[ℱ t] (l t i))
    (hy : ∀ t i, Measurable[ℱ t] (y t i)) (hw_nonneg : ∀ t i, 0 ≤ᵐ[μ] w t i)
    (hwl : ∀ t i, ∀ᵐ ω ∂μ, w t i ω * X t i ω ≤ 2 * l t i ω)
    (hmul : ∀ t i j, i ≠ j → ∀ᵐ ω ∂μ, w t i ω * X t i ω * (w t j ω * X t j ω) = 0) (x : ℝ) :
    μ {ω | ∃ n, x ≤ ∑ t ∈ range n, ∑ i, w t i ω * (X t i ω / (1 + l t i ω) - y t i ω)} ≤
      ENNReal.ofReal (exp (-x)) := by
  have h := (supermartingale_exp_sum_sum_mul_div_one_add_sub hX hX_int hX_nonneg hXy hw hl hy
    hw_nonneg hwl hmul).measure_exists_le_le (fun n ↦ ae_of_all _ fun ω ↦ (exp_pos _).le)
    (exp_pos x)
  simpa [← exp_neg] using h

/-- **Concentration of implicit-exploration estimates** [LS, Lemma 12.2]. Let `X t i ≥ 0` be
integrable and `ℱ (t + 1)`-measurable with `μ[X t i | ℱ t] ≤ y t i`, and let `w t i ≥ 0`,
`l t i` and `y t i` be `ℱ t`-measurable with `w t i * X t i ≤ 2 * l t i`. If the products
`(w t i * X t i) * (w t j * X t j)` of distinct `i, j` vanish, then for `δ > 0` and every
horizon `n`, the probability that
`log (1 / δ) ≤ ∑ t < n, ∑ i, w t i * (X t i / (1 + l t i) - y t i)` is at most `δ`. -/
theorem measure_log_one_div_le_sum_sum_mul_div_one_add_sub_le [IsProbabilityMeasure μ]
    (hX : ∀ t i, Measurable[ℱ (t + 1)] (X t i)) (hX_int : ∀ t i, Integrable (X t i) μ)
    (hX_nonneg : ∀ t i, 0 ≤ᵐ[μ] X t i) (hXy : ∀ t i, μ[X t i | ℱ t] ≤ᵐ[μ] y t i)
    (hw : ∀ t i, Measurable[ℱ t] (w t i)) (hl : ∀ t i, Measurable[ℱ t] (l t i))
    (hy : ∀ t i, Measurable[ℱ t] (y t i)) (hw_nonneg : ∀ t i, 0 ≤ᵐ[μ] w t i)
    (hwl : ∀ t i, ∀ᵐ ω ∂μ, w t i ω * X t i ω ≤ 2 * l t i ω)
    (hmul : ∀ t i j, i ≠ j → ∀ᵐ ω ∂μ, w t i ω * X t i ω * (w t j ω * X t j ω) = 0)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    μ {ω | log (1 / δ) ≤ ∑ t ∈ range n, ∑ i, w t i ω * (X t i ω / (1 + l t i ω) - y t i ω)} ≤
      ENNReal.ofReal δ := by
  calc μ {ω | log (1 / δ) ≤ ∑ t ∈ range n, ∑ i, w t i ω * (X t i ω / (1 + l t i ω) - y t i ω)}
      ≤ μ {ω | ∃ n, log (1 / δ) ≤
          ∑ t ∈ range n, ∑ i, w t i ω * (X t i ω / (1 + l t i ω) - y t i ω)} :=
        measure_mono fun ω hω ↦ ⟨n, hω⟩
    _ ≤ ENNReal.ofReal (exp (-log (1 / δ))) :=
        measure_exists_le_sum_sum_mul_div_one_add_sub_le hX hX_int hX_nonneg hXy hw hl hy
          hw_nonneg hwl hmul _
    _ = ENNReal.ofReal δ := by rw [exp_neg, exp_log (one_div_pos.2 hδ), one_div, inv_inv]

end LMLExplore
