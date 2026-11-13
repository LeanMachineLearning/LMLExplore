/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Martingale.Basic
public import LMLExplore.Probability.Martingale.Ville
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# The Bernoulli maximal inequality

Let `X` be a process with values in `[0, 1]`, with `X i` measurable with respect to `ℱ (i + 1)`,
and let `P i = E[X i | ℱ i]`. The Bernoulli maximal inequality states that, with probability at
least `1 - δ`, the sum of the `X i` is at least half the sum of their conditional means minus
`log (1 / δ)`, simultaneously for all times:
`ℙ(∃ n, ∑_{i < n} X i < (1/2) ∑_{i < n} P i - log (1 / δ)) ≤ δ`.

When `X i` is the indicator that a state–action pair is visited in episode `i`, the sum of the
`X i` is its visit count and the sum of the `P i` its pseudo-count, the sum of the conditional
visit probabilities. The inequality says that counts are at least half the pseudo-counts up to a
logarithmic term, which is how the analyses of episodic exploration algorithms convert bounds in
pseudo-counts into bounds in counts.

Freedman's inequality in its fixed-`η` form
(`LMLExplore.measure_exists_mul_sum_condExp_sq_add_log_div_le_sum_le`), applied to `P i - X i`
with `η = 1 / 2`, gives the same bound with `2 log (1 / δ)` in place of `log (1 / δ)`. The sharper
constant comes from the one-step bound `E[exp (P / 2 - X) | m] ≤ 1`: by convexity of the
exponential, `exp (-X) ≤ 1 - (1 - e⁻¹) X` on `[0, 1]`, and `1 - (1 - e⁻¹) P ≤ exp (-P / 2)`
since `1 - e⁻¹ ≥ 1 / 2`. Then `exp (∑_{i < n} (P i / 2 - X i))` is a nonnegative supermartingale
started at `1`, and Ville's inequality bounds the probability that it ever reaches `1 / δ`.

## Main statements

* `LMLExplore.condExp_exp_condExp_div_two_sub_le_one`: the one-step bound
  `E[exp (E[X | m] / 2 - X) | m] ≤ 1` for `X` with values in `[0, 1]`.
* `LMLExplore.measure_exists_sum_lt_half_mul_sum_sub_le`: **the Bernoulli maximal inequality**.

## References

* [DLB17] C. Dann, T. Lattimore and E. Brunskill, *Unifying PAC and regret: uniform PAC bounds
  for episodic reinforcement learning*, Advances in Neural Information Processing Systems 30
  (2017), Lemma F.4.
* [EV26] A. Essakine and C. Vernade, *Tight sample complexity bounds for entropic best policy
  identification*, COLT 2026, arXiv:2605.13717, Lemma 20.
-/

public section

open MeasureTheory Finset Real
open scoped ENNReal

namespace LMLExplore

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- For `X` measurable with values in `[0, 1]` almost surely, `exp (E[X | m] / 2 - X)` is
integrable: it is bounded by `exp (1 / 2)`. -/
private theorem integrable_exp_condExp_div_two_sub [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable X) (hX01 : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc 0 1) :
    Integrable (fun ω ↦ exp (μ[X | m] ω / 2 - X ω)) μ := by
  have hXabs : ∀ᵐ ω ∂μ, |X ω| ≤ 1 := hX01.mono fun ω hω ↦ abs_le.2 ⟨by linarith [hω.1], hω.2⟩
  refine .of_bound
    (((stronglyMeasurable_condExp.mono hm).measurable.div_const 2).sub hX).exp.aestronglyMeasurable
    (exp (1 / 2)) ?_
  filter_upwards [hX01, ae_bdd_abs_condExp_of_ae_bdd_abs (m := m) hXabs] with ω hω hCω
  rw [norm_of_nonneg (exp_pos _).le, exp_le_exp]
  linarith [hω.1, (abs_le.1 hCω).2]

/-- **One-step bound of the Bernoulli maximal inequality.** If `X` is measurable with values in
`[0, 1]` almost surely, then `E[exp (E[X | m] / 2 - X) | m] ≤ 1` almost surely. -/
theorem condExp_exp_condExp_div_two_sub_le_one [IsFiniteMeasure μ] (hm : m ≤ mΩ) {X : Ω → ℝ}
    (hX : Measurable X) (hX01 : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc 0 1) :
    μ[fun ω ↦ exp (μ[X | m] ω / 2 - X ω) | m] ≤ᵐ[μ] 1 := by
  set C := μ[X | m]
  set k : ℝ := 1 - exp (-1)
  have hCm : StronglyMeasurable[m] C := stronglyMeasurable_condExp
  have hXabs : ∀ᵐ ω ∂μ, |X ω| ≤ 1 := hX01.mono fun ω hω ↦ abs_le.2 ⟨by linarith [hω.1], hω.2⟩
  have hXint : Integrable X μ := .of_bound hX.aestronglyMeasurable 1 hXabs
  have hC0 : 0 ≤ᵐ[μ] C := condExp_nonneg (hX01.mono fun _ hω ↦ hω.1)
  -- the exponential of `-X` lies below its chord on `[0, 1]`
  have hchord : (fun ω ↦ exp (-X ω)) ≤ᵐ[μ] fun ω ↦ 1 - k * X ω := hX01.mono fun ω hω ↦ by
    have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (-1)) (sub_nonneg.2 hω.2) hω.1
      (sub_add_cancel 1 (X ω))
    simp only [smul_eq_mul, mul_zero, zero_add, mul_neg, mul_one, exp_zero] at h
    linarith
  have hEint : Integrable (fun ω ↦ exp (-X ω)) μ :=
    .of_bound hX.neg.exp.aestronglyMeasurable 1 (hX01.mono fun ω hω ↦ by
      rw [norm_of_nonneg (exp_pos _).le, exp_le_one_iff]
      linarith [hω.1])
  have hLint : Integrable (fun ω ↦ 1 - k * X ω) μ := (integrable_const 1).sub (hXint.const_mul k)
  have hfun : (fun ω ↦ exp (C ω / 2 - X ω)) =
      (fun ω ↦ exp (C ω / 2)) * fun ω ↦ exp (-X ω) := by
    funext ω
    rw [Pi.mul_apply, ← exp_add, sub_eq_add_neg]
  -- `E[exp (C / 2) exp (-X) | m] = exp (C / 2) E[exp (-X) | m] ≤ exp (C / 2) (1 - k C)`
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := m)
    (hCm.measurable.div_const 2).exp.stronglyMeasurable
    (hfun ▸ integrable_exp_condExp_div_two_sub hm hX hX01) hEint
  have hmono := condExp_mono (m := m) hEint hLint hchord
  have hlin : μ[fun ω ↦ 1 - k * X ω | m] =ᵐ[μ] fun ω ↦ 1 - k * C ω := by
    have h : (fun ω ↦ 1 - k * X ω) = (fun _ ↦ (1 : ℝ)) - k • X := by ext; simp
    rw [h]
    filter_upwards [condExp_sub (integrable_const 1) (hXint.smul k) m,
      condExp_smul (m := m) k X] with ω h1 h2
    rw [h1, Pi.sub_apply, condExp_const hm, h2, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  filter_upwards [hpull, hmono, hlin, hC0] with ω hp hmo hl hCω
  rw [hp, Pi.mul_apply, Pi.one_apply]
  -- `1 - k C ≤ 1 - C / 2 ≤ exp (-C / 2)`, since `k ≥ 1 / 2` and `C ≥ 0`
  have hk : 1 / 2 ≤ k := by linarith [exp_neg_one_lt_half]
  have hC : 0 ≤ C ω := hCω
  have hbound : 1 - k * C ω ≤ exp (-(C ω / 2)) := by
    nlinarith [add_one_le_exp (-(C ω / 2))]
  calc exp (C ω / 2) * μ[fun ω ↦ exp (-X ω) | m] ω
      ≤ exp (C ω / 2) * (1 - k * C ω) :=
        mul_le_mul_of_nonneg_left (hmo.trans_eq hl) (exp_pos _).le
    _ ≤ exp (C ω / 2) * exp (-(C ω / 2)) := mul_le_mul_of_nonneg_left hbound (exp_pos _).le
    _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]

/-- **The Bernoulli maximal inequality** [DLB17, Lemma F.4], [EV26, Lemma 20]. Let `X i` be
`ℱ (i + 1)`-measurable with values in `[0, 1]` almost surely, and let `P i` be a version of its
conditional mean `E[X i | ℱ i]`. Then for every `δ > 0`, the probability that
`∑_{i < n} X i < (1/2) ∑_{i < n} P i - log (1 / δ)` for some `n` is at most `δ`. -/
theorem measure_exists_sum_lt_half_mul_sum_sub_le [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {X P : ℕ → Ω → ℝ} (hX : ∀ i, Measurable[ℱ (i + 1)] (X i))
    (hX01 : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 1) (hP : ∀ i, μ[X i | ℱ i] =ᵐ[μ] P i)
    {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | ∃ n, ∑ i ∈ range n, X i ω < 1 / 2 * ∑ i ∈ range n, P i ω - log (1 / δ)} ≤
      ENNReal.ofReal δ := by
  set C : ℕ → Ω → ℝ := fun i ↦ μ[X i | ℱ i]
  have hXm : ∀ i, Measurable (X i) := fun i ↦ (hX i).mono (ℱ.le (i + 1)) le_rfl
  -- `exp (∑_{i < n} (C i / 2 - X i))` is a nonnegative supermartingale started at `1`
  have hZm : ∀ i, Measurable[ℱ (i + 1)] fun ω ↦ C i ω / 2 - X i ω := fun i ↦
    ((stronglyMeasurable_condExp.mono (ℱ.mono i.le_succ)).measurable.div_const 2).sub (hX i)
  have hsuper := supermartingale_exp_sum_of_condExp_exp_le_one hZm
    (fun i ↦ integrable_exp_condExp_div_two_sub (ℱ.le i) (hXm i) (hX01 i)) fun i ↦
    condExp_exp_condExp_div_two_sub_le_one (ℱ.le i) (hXm i) (hX01 i)
  have hville := hsuper.measure_exists_le_le (fun _ ↦ ae_of_all _ fun _ ↦ (exp_pos _).le)
    (one_div_pos.2 hδ)
  simp only [range_zero, sum_empty, exp_zero, integral_const, probReal_univ, smul_eq_mul,
    one_mul, one_div_one_div] at hville
  -- off a null set, the versions `P i` agree with the conditional means `C i`
  have hPC : ∀ᵐ ω ∂μ, ∀ i, P i ω = C i ω := ae_all_iff.2 fun i ↦ (hP i).mono fun _ h ↦ h.symm
  refine (measure_mono_ae (hPC.mono fun ω hω h ↦ ?_)).trans hville
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  simp only [hω] at hn
  have hsum : ∑ i ∈ range n, (C i ω / 2 - X i ω) =
      1 / 2 * ∑ i ∈ range n, C i ω - ∑ i ∈ range n, X i ω := by
    rw [sum_sub_distrib, mul_sum]
    exact congrArg₂ _ (sum_congr rfl fun i _ ↦ by ring) rfl
  calc (1 : ℝ) / δ = exp (log (1 / δ)) := (exp_log (by positivity)).symm
    _ ≤ exp (∑ i ∈ range n, (C i ω / 2 - X i ω)) := exp_le_exp.2 (by rw [hsum]; linarith)

end LMLExplore
