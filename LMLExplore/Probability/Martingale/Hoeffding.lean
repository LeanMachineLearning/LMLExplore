/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import LMLExplore.Probability.Moments.SubGaussian.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Chord
import TauCeti.MeasureTheory.Function.ConditionalExpectation
import TauCeti.Probability.Moments.Azuma

/-!
# Hoeffding's lemma and the Azuma–Hoeffding inequality around conditional means

Let `m` be a sub-σ-algebra and `X` a random variable with values in `[a, b]`. Given `m`, the
variable `X` keeps its range `[a, b]` and has mean `μ[X | m]`, so Hoeffding's lemma applies
conditionally to the centred variable `X - μ[X | m]`:
`E[exp (t (X - μ[X | m])) | m] ≤ exp ((b - a) ^ 2 t ^ 2 / 8)`.
The range of the centred variable, `[a - μ[X | m], b - μ[X | m]]`, is random but known given `m`,
and its width is `b - a`. A deterministic interval containing `X - μ[X | m]` is only
`[a - b, b - a]`, of width `2 (b - a)`, and using it (as in the deterministic-range Azuma lemmas)
loses a factor `4` in the variance proxy.

Summing along a filtration `ℱ`, a process `X k` that is `ℱ (k + 1)`-measurable with values in
`[a k, b k]` gives the Azuma–Hoeffding inequality
`P(ε ≤ ∑ k < n, (μ[X k | ℱ k] - X k)) ≤ exp (-2 ε ^ 2 / ∑ k < n, (b k - a k) ^ 2)`,
with no hypothesis on the conditional means. This is the form used by online-to-batch
conversions, where `X k` is the loss of the play of round `k` on a fresh datum and
`μ[X k | ℱ k]` is the risk of that play.

Tau Ceti's `TauCeti.Probability.hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero` and
`TauCeti.Probability.measureReal_sum_range_ge_le_of_mem_Icc_martingale_differences` are the cases
of conditionally centred variables with deterministic ranges. The proofs adapt theirs: the chord
bound for the exponential (`Real.exp_mul_le_add_mul`) and the Bernoulli case of Hoeffding's lemma
(`TauCeti.Probability.chord_le_exp`) bound the conditional exponential moment without regular
conditional distributions, so that only the conditional sub-Gaussian predicate of Mathlib needs a
standard Borel space.

## Main statements

* `LMLExplore.condExp_exp_mul_sub_condExp_le`: the conditional Hoeffding lemma,
  `μ[exp (t (X - μ[X | m])) | m] ≤ exp ((b - a) ^ 2 t ^ 2 / 8)` almost everywhere.
* `LMLExplore.hasCondSubgaussianMGF_of_mem_Icc`: `X - μ[X | m]` is conditionally
  `(‖b - a‖₊ / 2) ^ 2`-sub-Gaussian given `m`, the conditional form of Mathlib's
  `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`.
* `LMLExplore.hasSubgaussianMGF_sum_range_sub_condExp`: the sum
  `∑ k < n, (X k - μ[X k | ℱ k])` is sub-Gaussian with the sum of the Hoeffding variance proxies.
* `LMLExplore.measureReal_le_sum_condExp_sub_le`: the Azuma–Hoeffding inequality
  `P(ε ≤ ∑ k < n, (μ[X k | ℱ k] - X k)) ≤ exp (-2 ε ^ 2 / ∑ k < n, (b k - a k) ^ 2)`.

## References

* W. Hoeffding, *Probability inequalities for sums of bounded random variables*, Journal of the
  American Statistical Association 58 (1963), 13–30.
* K. Azuma, *Weighted sums of certain dependent random variables*, Tohoku Mathematical Journal 19
  (1967), 357–367.
* F. Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*,
  arXiv:1912.13213v10, Theorem 3.9.
-/

public section

open MeasureTheory ProbabilityTheory Real Finset
open scoped NNReal

namespace LMLExplore

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ} {a b : ℝ}

/-- The Hoeffding variance proxy of the interval `[a, b]`, as a real number. -/
private lemma coe_nnnorm_sub_div_two_sq :
    (((‖b - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = (b - a) ^ 2 / 4 := by
  push_cast
  rw [Real.norm_eq_abs, div_pow, sq_abs]
  norm_num

/-- A variable with values in `[a, b]`, centred at its conditional mean, has values in
`[a - b, b - a]` almost everywhere. -/
private lemma ae_sub_condExp_mem_Icc (hm : m ≤ mΩ) (hX : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    ∀ᵐ ω ∂μ, X ω - μ[X | m] ω ∈ Set.Icc (a - b) (b - a) := by
  filter_upwards [hbound, (convex_Icc a b).condExp_mem hm (Integrable.of_mem_Icc a b hX hbound)
    isClosed_Icc hbound] with ω h1 h2
  exact ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

/-- The exponential moments of a variable with values in `[a, b]`, centred at its conditional
mean, are finite. -/
private lemma integrable_exp_mul_sub_condExp (hm : m ≤ mΩ) (hX : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * (X ω - μ[X | m] ω))) μ :=
  integrable_exp_mul_of_mem_Icc
    (hX.sub (stronglyMeasurable_condExp.mono hm).measurable.aemeasurable)
    (ae_sub_condExp_mem_Icc hm hX hbound)

/-- Hoeffding's chord bound at a mean `M ∈ [a, b]`: for the chord `c₀ + c₁ y` of `y ↦ exp (t y)`
over `[a, b]`, `exp (-t M) (c₀ + c₁ M) ≤ exp ((b - a) ^ 2 t ^ 2 / 8)`. -/
private lemma exp_neg_mul_mul_chord_le (hab : a < b) {M : ℝ} (hM : M ∈ Set.Icc a b) (t : ℝ) :
    exp (-t * M) * ((b * exp (t * a) - a * exp (t * b)) / (b - a) +
      (exp (t * b) - exp (t * a)) / (b - a) * M) ≤ exp ((b - a) ^ 2 * t ^ 2 / 8) := by
  have hbM : b - M - (a - M) = b - a := by ring
  calc _ = ((b - M) * exp (t * (a - M)) - (a - M) * exp (t * (b - M))) / (b - M - (a - M)) := by
        rw [hbM, show t * (a - M) = t * a + -t * M by ring,
          show t * (b - M) = t * b + -t * M by ring, exp_add, exp_add]
        field_simp
        ring
    _ ≤ exp ((‖b - M - (a - M)‖₊ / 2) ^ 2 * t ^ 2 / 2) :=
        TauCeti.Probability.chord_le_exp (by linarith [hM.1]) (by linarith [hM.2]) (by linarith) t
    _ = exp ((b - a) ^ 2 * t ^ 2 / 8) := by
        have h := coe_nnnorm_sub_div_two_sq (a := a) (b := b)
        push_cast at h
        rw [hbM, coe_nnNorm, h]
        ring_nf

/-- **Conditional Hoeffding lemma, centred at the conditional mean.** If `X` has values in
`[a, b]` almost everywhere, then for every `t`,
`μ[exp (t (X - μ[X | m])) | m] ≤ exp ((b - a) ^ 2 t ^ 2 / 8)` almost everywhere.
No regular conditional distribution is needed. -/
theorem condExp_exp_mul_sub_condExp_le (hm : m ≤ mΩ) (hX : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (t : ℝ) :
    μ[fun ω ↦ exp (t * (X ω - μ[X | m] ω)) | m] ≤ᵐ[μ]
      fun _ ↦ exp ((b - a) ^ 2 * t ^ 2 / 8) := by
  have hXint : Integrable X μ := Integrable.of_mem_Icc a b hX hbound
  have hM := (convex_Icc a b).condExp_mem hm hXint isClosed_Icc hbound
  obtain ⟨ω₀, hω₀⟩ := hbound.exists
  rcases (hω₀.1.trans hω₀.2).eq_or_lt with hab | hab
  · -- A degenerate interval: `X = μ[X | m]` almost everywhere.
    have h0 : (fun ω ↦ exp (t * (X ω - μ[X | m] ω))) =ᵐ[μ] fun _ ↦ 1 := by
      filter_upwards [hbound, hM] with ω h1 h2
      rw [show X ω = μ[X | m] ω by subst hab; linarith [h1.1, h1.2, h2.1, h2.2]]
      simp
    refine (condExp_congr_ae h0).trans_le ?_
    rw [condExp_const hm]
    exact Filter.Eventually.of_forall fun _ ↦ by simp [hab]
  -- `exp (t (X - μ[X | m])) = exp (-t μ[X | m]) exp (t X)`, whose first factor is known given `m`.
  have hZm : StronglyMeasurable[m] fun ω ↦ exp (-t * μ[X | m] ω) :=
    continuous_exp.comp_stronglyMeasurable (stronglyMeasurable_condExp.const_mul (-t))
  have hW : Integrable (fun ω ↦ exp (t * X ω)) μ := integrable_exp_mul_of_mem_Icc hX hbound
  have hprod : (fun ω ↦ exp (t * (X ω - μ[X | m] ω))) =
      (fun ω ↦ exp (-t * μ[X | m] ω)) * fun ω ↦ exp (t * X ω) := by
    ext ω
    rw [Pi.mul_apply, ← exp_add]
    ring_nf
  have hpull := condExp_mul_of_stronglyMeasurable_left hZm
    (hprod ▸ integrable_exp_mul_sub_condExp hm hX hbound t) hW
  -- The chord bound for `exp (t X)`, and the linearity of the conditional expectation.
  set c₀ := (b * exp (t * a) - a * exp (t * b)) / (b - a)
  set c₁ := (exp (t * b) - exp (t * a)) / (b - a)
  have hchord := condExp_mono (m := m) hW ((integrable_const c₀).add (hXint.const_mul c₁))
    (hbound.mono fun ω hω ↦ exp_mul_le_add_mul hab hω t)
  have hlin := condExp_add (m := m) (integrable_const c₀) (hXint.const_mul c₁)
  have hsmul := condExp_smul (m := m) (μ := μ) c₁ X
  rw [condExp_const hm] at hlin
  rw [hprod]
  filter_upwards [hpull, hchord, hlin, hsmul, hM] with ω hp hc hl hs hMω
  have hs' : μ[fun ω ↦ c₁ * X ω | m] ω = c₁ * μ[X | m] ω := by
    simpa only [Pi.smul_def, Pi.smul_apply, smul_eq_mul] using hs
  rw [hp, Pi.mul_apply]
  refine (mul_le_mul_of_nonneg_left ?_ (exp_pos _).le).trans (exp_neg_mul_mul_chord_le hab hMω t)
  rw [← hs']
  exact hc.trans_eq hl

/-- **Conditional Hoeffding lemma.** A random variable `X` with values in `[a, b]` almost
everywhere, centred at its conditional mean given `m`, is conditionally
`(‖b - a‖₊ / 2) ^ 2`-sub-Gaussian given `m`. This is the conditional form of Mathlib's
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`. -/
theorem hasCondSubgaussianMGF_of_mem_Icc [StandardBorelSpace Ω] (hm : m ≤ mΩ)
    (hX : AEMeasurable X μ) (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    HasCondSubgaussianMGF m hm (fun ω ↦ X ω - μ[X | m] ω) ((‖b - a‖₊ / 2) ^ 2) μ :=
  HasCondSubgaussianMGF.of_ae_trim_condExp_le (integrable_exp_mul_sub_condExp hm hX hbound)
    fun q ↦ (StronglyMeasurable.ae_le_trim_iff hm stronglyMeasurable_condExp
      stronglyMeasurable_const).2 <| (condExp_exp_mul_sub_condExp_le hm hX hbound q).trans_eq <|
        .of_forall fun _ ↦ by rw [coe_nnnorm_sub_div_two_sq]; ring_nf

/-- A variable with values in `[a, b]`, centred at its conditional mean given `m`, adds its
Hoeffding variance proxy to a sub-Gaussian `m`-measurable random variable. -/
theorem hasSubgaussianMGF_add_sub_condExp {S : Ω → ℝ} {c : ℝ≥0} (hm : m ≤ mΩ)
    (hS : HasSubgaussianMGF S c μ) (hSm : AEStronglyMeasurable[m] S μ) (hX : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    HasSubgaussianMGF (fun ω ↦ S ω + (X ω - μ[X | m] ω)) (c + (‖b - a‖₊ / 2) ^ 2) μ := by
  have hD := ae_sub_condExp_mem_Icc hm hX hbound
  have hZ (t : ℝ) : AEStronglyMeasurable[m] (fun ω ↦ exp (t * S ω)) μ :=
    continuous_exp.comp_aestronglyMeasurable (hSm.const_mul t)
  have hZW (t : ℝ) :
      Integrable (fun ω ↦ exp (t * S ω) * exp (t * (X ω - μ[X | m] ω))) μ := by
    refine (hS.integrable_exp_mul t).mul_bdd (c := exp (|t| * (b - a)))
      (integrable_exp_mul_sub_condExp hm hX hbound t).aestronglyMeasurable ?_
    filter_upwards [hD] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_exp]
    calc t * (X ω - μ[X | m] ω) ≤ |t| * |X ω - μ[X | m] ω| := (le_abs_self _).trans_eq (abs_mul _ _)
      _ ≤ |t| * (b - a) := by
        gcongr
        exact abs_le.2 ⟨by linarith [hω.1], hω.2⟩
  refine ⟨fun t ↦ by simpa [mul_add, exp_add] using hZW t, fun t ↦ ?_⟩
  have hmul : mgf (fun ω ↦ S ω + (X ω - μ[X | m] ω)) μ t =
      ∫ ω, exp (t * S ω) * exp (t * (X ω - μ[X | m] ω)) ∂μ := by
    simp [mgf, mul_add, exp_add]
  rw [hmul]
  calc _ ≤ exp ((b - a) ^ 2 * t ^ 2 / 8) * ∫ ω, exp (t * S ω) ∂μ :=
        TauCeti.MeasureTheory.integral_mul_le_of_condExp_le hm (hZ t)
          (Filter.Eventually.of_forall fun ω ↦ (exp_pos _).le) (hS.integrable_exp_mul t)
          (integrable_exp_mul_sub_condExp hm hX hbound t) (hZW t)
          (condExp_exp_mul_sub_condExp_le hm hX hbound t)
    _ ≤ exp ((b - a) ^ 2 * t ^ 2 / 8) * exp (c * t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (hS.mgf_le t) (exp_pos _).le
    _ = _ := by rw [← exp_add, NNReal.coe_add, coe_nnnorm_sub_div_two_sq]; ring_nf

variable {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ} {a b : ℕ → ℝ}

/-- If `X k` is `ℱ (k + 1)`-measurable with values in `[a k, b k]` almost everywhere, then the sum
`∑ k < n, (X k - μ[X k | ℱ k])` of the variables centred at their conditional means is
sub-Gaussian with the sum of the Hoeffding variance proxies `(‖b k - a k‖₊ / 2) ^ 2`. -/
theorem hasSubgaussianMGF_sum_range_sub_condExp (hX : ∀ k, Measurable[ℱ (k + 1)] (X k))
    (n : ℕ) (hbound : ∀ k < n, ∀ᵐ ω ∂μ, X k ω ∈ Set.Icc (a k) (b k)) :
    HasSubgaussianMGF (fun ω ↦ ∑ k ∈ range n, (X k ω - μ[X k | ℱ k] ω))
      (∑ k ∈ range n, (‖b k - a k‖₊ / 2) ^ 2) μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hS := ih fun k hk ↦ hbound k (by lia)
    -- The partial sum up to round `n` is known at time `n`.
    have hSm : StronglyMeasurable[ℱ n] fun ω ↦ ∑ k ∈ range n, (X k ω - μ[X k | ℱ k] ω) :=
      Finset.stronglyMeasurable_fun_sum _ fun k hk ↦
        (((hX k).mono (ℱ.mono (by simpa using hk)) le_rfl).stronglyMeasurable).sub
          (stronglyMeasurable_condExp.mono (ℱ.mono (by simp at hk; lia)))
    simp_rw [sum_range_succ]
    exact hasSubgaussianMGF_add_sub_condExp (ℱ.le n) hS hSm.aestronglyMeasurable
      ((hX n).mono (ℱ.le (n + 1)) le_rfl).aemeasurable (hbound n (by lia))

/-- **Azuma–Hoeffding inequality around conditional means** [Ora, Theorem 3.9]. If `X k` is
`ℱ (k + 1)`-measurable with values in `[a k, b k]` almost everywhere, then for `ε ≥ 0`,
`P(ε ≤ ∑ k < n, (μ[X k | ℱ k] - X k)) ≤ exp (-2 ε ^ 2 / ∑ k < n, (b k - a k) ^ 2)`.
The conditional means are arbitrary. -/
theorem measureReal_le_sum_condExp_sub_le (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) (n : ℕ)
    (hbound : ∀ k < n, ∀ᵐ ω ∂μ, X k ω ∈ Set.Icc (a k) (b k)) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ k ∈ range n, (μ[X k | ℱ k] ω - X k ω)} ≤
      exp (-2 * ε ^ 2 / ∑ k ∈ range n, (b k - a k) ^ 2) := by
  have h := (hasSubgaussianMGF_sum_range_sub_condExp hX n hbound).neg.measure_ge_le hε
  have hset : {ω | ε ≤ ∑ k ∈ range n, (μ[X k | ℱ k] ω - X k ω)} =
      {ω | ε ≤ (-fun ω ↦ ∑ k ∈ range n, (X k ω - μ[X k | ℱ k] ω)) ω} := by
    ext ω
    simp [sum_sub_distrib]
  rw [hset]
  refine h.trans_eq ?_
  congr 1
  push_cast
  simp_rw [Real.norm_eq_abs, div_pow, sq_abs, ← sum_div]
  ring

end LMLExplore
