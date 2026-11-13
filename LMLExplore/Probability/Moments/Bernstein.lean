/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Basic
import LMLExplore.Analysis.SpecialFunctions.Exp
import LMLExplore.Probability.Moments.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound
import TauCeti.MeasureTheory.Measure.Tail
import TauCeti.Probability.Moments.Basic

/-!
# Bennett's inequality and the high-probability form of Bernstein's inequality

Let `X i`, `i ∈ s`, be independent real random variables with finite second moments, nonpositive
means and `X i ≤ b` almost surely for some `b > 0`, and let `v ≥ ∑ i ∈ s, E (X i) ^ 2`. Write
`S = ∑ i ∈ s, X i`.

Bennett's bound `exp (t x) ≤ 1 + t x + ψ_b(t) x ^ 2` for `x ≤ b` and `t ≥ 0`, with
`ψ_b(t) = (exp (t b) - 1 - t b) / b ^ 2` (`Real.exp_mul_le_one_add_mul_add_mul_sq`), bounds the
moment-generating function of `S` at `t` by `exp (v ψ_b(t))`: the moment-generating function of
a centred Poisson variable with parameter `v / b ^ 2`, scaled by `b`. Optimising Chernoff's bound
at `t = log (1 + b ε / v) / b` gives **Bennett's inequality**
`P(ε ≤ S) ≤ exp (-(v / b ^ 2) h (b ε / v))` with `h u = (1 + u) log (1 + u) - u`. For large `ε`
it decays like `exp (-(ε / b) log (b ε / v))`, faster than the exponential decay of Bernstein's
inequality.

Since `ψ_b(t) ≤ t ^ 2 / (2 (1 - t b / 3))` for `t b < 3` (Tau Ceti's
`Real.exp_le_one_add_add_sq_div_of_le`), `S` is also sub-gamma with variance factor `v` and scale
`b / 3`. Chernoff's bound at an explicit `t` then inverts in closed form: for every `L`,
`P(√(2 v L) + b L / 3 ≤ S) ≤ exp (-L)`, so that with probability at least `1 - δ`,
`S < √(2 v log (1 / δ)) + b log (1 / δ) / 3`. This is the form of Bernstein's inequality in which
confidence bounds are stated [BLM13, Theorem 2.10]. It is also the high-probability form of
Bennett's bound, whose rate function `h` has no elementary inverse. With `|X i| ≤ b` and centred
summands, both tails combine into two-sided forms.

## Main statements

* `MeasureTheory.MemLp.mgf_le_exp_mul_exp_sub_one_sub_of_ae_le`: Bennett's bound on the
  moment-generating function, `E exp (t Y) ≤ exp (E Y ^ 2 ψ_b(t))`.
* `ProbabilityTheory.iIndepFun.mgf_sum_le_exp_mul_exp_sub_one_sub_of_ae_le`: the same for an
  independent sum, `E exp (t S) ≤ exp (v ψ_b(t))`.
* `ProbabilityTheory.iIndepFun.measureReal_sum_ge_le_exp_neg_mul_log_of_ae_le`: **Bennett's
  inequality**.
* `ProbabilityTheory.iIndepFun.measureReal_abs_sum_ge_le_two_mul_exp_neg_mul_log_of_abs_le`: its
  two-sided form.
* `ProbabilityTheory.iIndepFun.measureReal_sqrt_add_le_sum_le_of_ae_le` and
  `measureReal_sqrt_log_add_le_sum_le_of_ae_le`: **Bernstein's inequality** in high-probability
  form, `P(√(2 v L) + b L / 3 ≤ S) ≤ exp (-L)` and its version at confidence level `δ`.
* `ProbabilityTheory.iIndepFun.measureReal_sqrt_add_le_abs_sum_le_of_abs_le` and
  `measureReal_sqrt_log_add_le_abs_sum_le_of_abs_le`: their two-sided forms.

## Implementation notes

Bernstein's tail bound `P(ε ≤ S) ≤ exp (-ε ^ 2 / (2 (v + b ε / 3)))` for centred summands is Tau
Ceti's `ProbabilityTheory.iIndepFun.measureReal_sum_ge_le_of_ae_le`, and the statements here follow
its conventions: independent summands indexed by a `Finset`, almost-sure bounds, and the second
moments `E (X i) ^ 2` rather than variances. The one-sided bounds only need the means to be
nonpositive, and all bounds take any deterministic upper bound `v` on the sum of the second
moments.

## References

* [Ben62] G. Bennett, *Probability inequalities for the sum of independent random variables*,
  Journal of the American Statistical Association 57 (1962), 33–45.
* [BLM13] S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford
  University Press, 2013, Theorems 2.9 and 2.10.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → ℝ} {s : Finset ι}

namespace MeasureTheory.MemLp

/-- **Bennett's moment-generating-function bound** [BLM13, Theorem 2.9]. If `Y` has a finite
second moment, a nonpositive mean and `Y ≤ b` almost surely with `b > 0`, then for `t ≥ 0`,
`E exp (t Y) ≤ exp (E Y ^ 2 * ψ_b(t))` with `ψ_b(t) = (exp (t b) - 1 - t b) / b ^ 2`. -/
theorem mgf_le_exp_mul_exp_sub_one_sub_of_ae_le [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    {b t : ℝ} (hY : MemLp Y 2 μ) (hmean : μ[Y] ≤ 0) (hb : 0 < b) (hYb : ∀ᵐ ω ∂μ, Y ω ≤ b)
    (ht : 0 ≤ t) :
    mgf Y μ t ≤ exp ((∫ ω, Y ω ^ 2 ∂μ) * ((exp (t * b) - 1 - t * b) / b ^ 2)) := by
  have hYi : Integrable Y μ := hY.integrable one_le_two
  have hY2 : Integrable (fun ω ↦ Y ω ^ 2) μ := hY.integrable_sq
  set ψ := (exp (t * b) - 1 - t * b) / b ^ 2
  have hint₁ : Integrable (fun ω ↦ 1 + t * Y ω) μ := (integrable_const 1).add (hYi.const_mul t)
  have hint : Integrable (fun ω ↦ 1 + t * Y ω + ψ * Y ω ^ 2) μ := hint₁.add (hY2.const_mul ψ)
  calc mgf Y μ t ≤ ∫ ω, (1 + t * Y ω + ψ * Y ω ^ 2) ∂μ := by
        rw [mgf]
        refine integral_mono_ae (integrable_exp_mul_of_le t b ht hYi.aemeasurable hYb) hint ?_
        filter_upwards [hYb] with ω hω using exp_mul_le_one_add_mul_add_mul_sq hb ht hω
    _ = 1 + t * μ[Y] + ψ * ∫ ω, Y ω ^ 2 ∂μ := by
        rw [integral_add hint₁ (hY2.const_mul ψ),
          integral_add (integrable_const 1) (hYi.const_mul t), integral_const_mul,
          integral_const_mul]
        simp
    _ ≤ 1 + ψ * ∫ ω, Y ω ^ 2 ∂μ := by linarith [mul_nonpos_of_nonneg_of_nonpos ht hmean]
    _ ≤ exp (ψ * ∫ ω, Y ω ^ 2 ∂μ) := by linarith [add_one_le_exp (ψ * ∫ ω, Y ω ^ 2 ∂μ)]
    _ = exp ((∫ ω, Y ω ^ 2 ∂μ) * ψ) := by rw [mul_comm]

end MeasureTheory.MemLp

namespace ProbabilityTheory.iIndepFun

/-- **Bennett's moment-generating-function bound for independent sums** [BLM13, Theorem 2.9].
If the `X i`, `i ∈ s`, are independent with finite second moments, nonpositive means and
`X i ≤ b` almost surely with `b > 0`, and `∑ i ∈ s, E (X i) ^ 2 ≤ v`, then for `t ≥ 0` the
moment-generating function of `∑ i ∈ s, X i` at `t` is at most `exp (v * ψ_b(t))`, with
`ψ_b(t) = (exp (t b) - 1 - t b) / b ^ 2`. -/
theorem mgf_sum_le_exp_mul_exp_sub_one_sub_of_ae_le (h_indep : iIndepFun X μ) {b t v : ℝ}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hmean : ∀ i ∈ s, μ[X i] ≤ 0) (hb : 0 < b)
    (hXb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ≤ b) (hv : ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ ≤ v) (ht : 0 ≤ t) :
    mgf (fun ω ↦ ∑ i ∈ s, X i ω) μ t ≤ exp (v * ((exp (t * b) - 1 - t * b) / b ^ 2)) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  refine (h_indep.mgf_sum_le_exp_sum (fun i hi ↦ (hX i hi).aestronglyMeasurable.aemeasurable)
    fun i hi ↦ (hX i hi).mgf_le_exp_mul_exp_sub_one_sub_of_ae_le (hmean i hi) hb (hXb i hi)
      ht).trans ?_
  rw [← sum_mul]
  gcongr
  exact exp_sub_one_sub_id_div_sq_nonneg _ _

/-- Chernoff's bound for a sum bounded above: if `X i ≤ b` almost surely for `i ∈ s` and the
moment-generating function of `∑ i ∈ s, X i` at `t ≥ 0` is at most `exp K`, then
`P(ε ≤ ∑ i ∈ s, X i) ≤ exp (-t ε + K)`. -/
private lemma measureReal_sum_ge_le_exp_of_mgf_le [IsFiniteMeasure μ] {b t ε K : ℝ}
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) (hXb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ≤ b) (ht : 0 ≤ t)
    (hK : mgf (fun ω ↦ ∑ i ∈ s, X i ω) μ t ≤ exp K) :
    μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤ exp (-t * ε + K) := by
  refine measureReal_ge_le_exp_of_mgf_le ht
    (integrable_exp_mul_of_le t (#s * b) ht (Finset.aemeasurable_fun_sum s hX) ?_) hK
  filter_upwards [(Filter.eventually_all_finset s).2 hXb] with ω hω
  simpa using sum_le_card_nsmul s (fun i ↦ X i ω) b hω

/-- Two-sided form of a one-sided tail bound: if every independent family `Y` satisfying the
one-sided hypotheses (finite second moments, nonpositive means, `Y i ≤ b`, second moments summing
to at most `v`) has `P(ε ≤ ∑ i ∈ s, Y i) ≤ c`, then a centred family with `|X i| ≤ b` has
`P(ε ≤ |∑ i ∈ s, X i|) ≤ 2 c`, applying the bound to `X` and to `-X`. -/
private lemma measureReal_abs_sum_ge_le_two_mul (h_indep : iIndepFun X μ) {b v ε c : ℝ}
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) (hmean : ∀ i ∈ s, μ[X i] = 0)
    (hXb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ b) (hv : ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ ≤ v)
    (hbound : ∀ Y : ι → Ω → ℝ, iIndepFun Y μ → (∀ i ∈ s, MemLp (Y i) 2 μ) →
      (∀ i ∈ s, μ[Y i] ≤ 0) → (∀ i ∈ s, ∀ᵐ ω ∂μ, Y i ω ≤ b) →
      ∑ i ∈ s, ∫ ω, Y i ω ^ 2 ∂μ ≤ v → μ.real {ω | ε ≤ ∑ i ∈ s, Y i ω} ≤ c) :
    μ.real {ω | ε ≤ |∑ i ∈ s, X i ω|} ≤ 2 * c := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  have hL2 : ∀ i ∈ s, MemLp (X i) 2 μ := fun i hi ↦
    MemLp.of_bound (hX i hi).aestronglyMeasurable b (by simpa using hXb i hi)
  have hup := hbound X h_indep hL2 (fun i hi ↦ (hmean i hi).le)
    (fun i hi ↦ by filter_upwards [hXb i hi] with ω hω using (le_abs_self _).trans hω) hv
  -- The lower tail is the upper tail of the negated family.
  have hlow := hbound (fun i ω ↦ -X i ω) (h_indep.comp (fun _ ↦ Neg.neg) fun _ ↦ measurable_neg)
    (fun i hi ↦ (hL2 i hi).neg) (fun i hi ↦ by simp [integral_neg, hmean i hi])
    (fun i hi ↦ by filter_upwards [hXb i hi] with ω hω using (neg_le_abs _).trans hω)
    (by simpa using hv)
  simp only [sum_neg_distrib] at hlow
  exact TauCeti.measureReal_le_abs_le_add.trans (by linarith)

/-- **Bennett's inequality** [Ben62], [BLM13, Theorem 2.9]. Let the `X i`, `i ∈ s`, be
independent with finite second moments, nonpositive means and `X i ≤ b` almost surely with
`b > 0`, and let `∑ i ∈ s, E (X i) ^ 2 ≤ v`. Then for `ε ≥ 0`,
`P(ε ≤ ∑ i ∈ s, X i) ≤ exp (-(v / b ^ 2) h (b ε / v))` with `h u = (1 + u) log (1 + u) - u`.
For `v = 0` the right-hand side is `1`. -/
theorem measureReal_sum_ge_le_exp_neg_mul_log_of_ae_le (h_indep : iIndepFun X μ) {b v ε : ℝ}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hmean : ∀ i ∈ s, μ[X i] ≤ 0) (hb : 0 < b)
    (hXb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ≤ b) (hv : ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ ≤ v) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤
      exp (-(v / b ^ 2 * ((1 + b * ε / v) * log (1 + b * ε / v) - b * ε / v))) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  have hv0 : 0 ≤ v := (sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦ sq_nonneg _).trans hv
  rcases hv0.eq_or_lt with rfl | hv0
  · simp
  -- Chernoff's bound at `t = log (1 + u) / b`, where `exp (t b) = 1 + u` for `u = b ε / v`.
  set u := b * ε / v
  have hu : 0 ≤ u := by positivity
  set L := log (1 + u)
  have ht : 0 ≤ L / b := div_nonneg (log_nonneg (by linarith)) hb.le
  refine (measureReal_sum_ge_le_exp_of_mgf_le
    (fun i hi ↦ (hX i hi).aestronglyMeasurable.aemeasurable) hXb ht
    (h_indep.mgf_sum_le_exp_mul_exp_sub_one_sub_of_ae_le hX hmean hb hXb hv ht)).trans_eq ?_
  rw [div_mul_cancel₀ _ hb.ne', exp_log (by linarith)]
  congr 1
  simp only [u]
  field_simp
  ring

/-- **Bennett's inequality, two-sided form** [BLM13, Theorem 2.9]. Let the `X i`, `i ∈ s`, be
independent and almost-everywhere measurable with mean zero and `|X i| ≤ b` almost surely with
`b > 0`, and let `∑ i ∈ s, E (X i) ^ 2 ≤ v`. Then for `ε ≥ 0`,
`P(ε ≤ |∑ i ∈ s, X i|) ≤ 2 exp (-(v / b ^ 2) h (b ε / v))` with
`h u = (1 + u) log (1 + u) - u`. -/
theorem measureReal_abs_sum_ge_le_two_mul_exp_neg_mul_log_of_abs_le (h_indep : iIndepFun X μ)
    {b v ε : ℝ} (hX : ∀ i ∈ s, AEMeasurable (X i) μ) (hmean : ∀ i ∈ s, μ[X i] = 0)
    (hb : 0 < b) (hXb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (hv : ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ ≤ v) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ s, X i ω|} ≤
      2 * exp (-(v / b ^ 2 * ((1 + b * ε / v) * log (1 + b * ε / v) - b * ε / v))) :=
  measureReal_abs_sum_ge_le_two_mul h_indep hX hmean hXb hv fun _ hY hL2 hm hYb hYv ↦
    hY.measureReal_sum_ge_le_exp_neg_mul_log_of_ae_le hL2 hm hb hYb hYv hε

/-- **Bernstein's inequality, high-probability form** [BLM13, Theorem 2.10]. Let the `X i`,
`i ∈ s`, be independent with finite second moments, nonpositive means and `X i ≤ b` almost surely
with `b > 0`, and let `∑ i ∈ s, E (X i) ^ 2 ≤ v`. Then for every `L`,
`P(√(2 v L) + b L / 3 ≤ ∑ i ∈ s, X i) ≤ exp (-L)`. -/
theorem measureReal_sqrt_add_le_sum_le_of_ae_le (h_indep : iIndepFun X μ) {b v L : ℝ}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hmean : ∀ i ∈ s, μ[X i] ≤ 0) (hb : 0 < b)
    (hXb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ≤ b) (hv : ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ ≤ v) :
    μ.real {ω | √(2 * v * L) + b * L / 3 ≤ ∑ i ∈ s, X i ω} ≤ exp (-L) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  rcases le_or_gt L 0 with hL | hL
  · exact measureReal_le_one.trans (one_le_exp (neg_nonneg.2 hL))
  have hm0 : 0 ≤ ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ :=
    sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦ sq_nonneg _
  rcases (hm0.trans hv).eq_or_lt with rfl | hv0
  · -- Zero second moments: the sum vanishes almost surely, below the level `b L / 3 > 0`.
    have hzero := TauCeti.ae_sum_eq_zero_of_sum_integral_sq_eq_zero hX (le_antisymm hv hm0)
    have hnull : μ.real {ω | √(2 * 0 * L) + b * L / 3 ≤ ∑ i ∈ s, X i ω} = 0 := by
      rw [measureReal_eq_zero_iff]
      refine measure_mono_null (fun ω hω ↦ ?_) (ae_iff.1 hzero)
      simp only [Set.mem_ofPred_eq, mul_zero, zero_mul, sqrt_zero, zero_add] at hω ⊢
      have : 0 < b * L / 3 := by positivity
      linarith
    rw [hnull]
    positivity
  -- Chernoff's bound at `t = r / (v + b r / 3)` with `r = √(2 v L)`, where the sub-gamma bound
  -- `ψ_b(t) ≤ t ^ 2 / (2 (1 - t b / 3))` makes the exponent exactly `-L`.
  set r := √(2 * v * L)
  have hr : r ^ 2 = 2 * v * L := sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := sqrt_nonneg _
  have hD : 0 < v + b * r / 3 := by positivity
  set t := r / (v + b * r / 3)
  have ht : 0 ≤ t := by positivity
  have htb : t * b < 3 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
    nlinarith
  have h1 : 1 - t * b / 3 = v / (v + b * r / 3) := by
    simp only [t]
    field_simp
    ring
  have hmgf : mgf (fun ω ↦ ∑ i ∈ s, X i ω) μ t ≤ exp (v * t ^ 2 / (2 * (1 - t * b / 3))) := by
    refine (h_indep.mgf_sum_le_exp_mul_exp_sub_one_sub_of_ae_le hX hmean hb hXb hv ht).trans
      (exp_le_exp.2 ?_)
    calc v * ((exp (t * b) - 1 - t * b) / b ^ 2)
        ≤ v * ((t * b) ^ 2 / (2 * (1 - t * b / 3)) / b ^ 2) := by
          gcongr
          linarith [exp_le_one_add_add_sq_div_of_le le_rfl (by positivity) htb]
      _ = v * t ^ 2 / (2 * (1 - t * b / 3)) := by
          field_simp
  refine (measureReal_sum_ge_le_exp_of_mgf_le
    (fun i hi ↦ (hX i hi).aestronglyMeasurable.aemeasurable) hXb ht hmgf).trans_eq ?_
  rw [h1]
  congr 1
  simp only [t]
  field_simp
  linear_combination (-3 : ℝ) * hr

/-- **Bernstein's inequality at confidence level `δ`** [BLM13, Theorem 2.10]. Under the
hypotheses of `measureReal_sqrt_add_le_sum_le_of_ae_le`, for `δ > 0`, with probability at least
`1 - δ`, `∑ i ∈ s, X i < √(2 v log (1 / δ)) + b log (1 / δ) / 3`. -/
theorem measureReal_sqrt_log_add_le_sum_le_of_ae_le (h_indep : iIndepFun X μ) {b v δ : ℝ}
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hmean : ∀ i ∈ s, μ[X i] ≤ 0) (hb : 0 < b)
    (hXb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ≤ b) (hv : ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ ≤ v) (hδ : 0 < δ) :
    μ.real {ω | √(2 * v * log (1 / δ)) + b * log (1 / δ) / 3 ≤ ∑ i ∈ s, X i ω} ≤ δ := by
  have hexp : exp (-log (1 / δ)) = δ := by rw [one_div, log_inv, neg_neg, exp_log hδ]
  simpa only [hexp] using
    h_indep.measureReal_sqrt_add_le_sum_le_of_ae_le (L := log (1 / δ)) hX hmean hb hXb hv

/-- **Bernstein's inequality, two-sided high-probability form** [BLM13, Theorem 2.10]. Let the
`X i`, `i ∈ s`, be independent and almost-everywhere measurable with mean zero and `|X i| ≤ b`
almost surely with `b > 0`, and let `∑ i ∈ s, E (X i) ^ 2 ≤ v`. Then for every `L`,
`P(√(2 v L) + b L / 3 ≤ |∑ i ∈ s, X i|) ≤ 2 exp (-L)`. -/
theorem measureReal_sqrt_add_le_abs_sum_le_of_abs_le (h_indep : iIndepFun X μ) {b v L : ℝ}
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) (hmean : ∀ i ∈ s, μ[X i] = 0) (hb : 0 < b)
    (hXb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ b) (hv : ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ ≤ v) :
    μ.real {ω | √(2 * v * L) + b * L / 3 ≤ |∑ i ∈ s, X i ω|} ≤ 2 * exp (-L) :=
  measureReal_abs_sum_ge_le_two_mul h_indep hX hmean hXb hv fun _ hY hL2 hm hYb hYv ↦
    hY.measureReal_sqrt_add_le_sum_le_of_ae_le hL2 hm hb hYb hYv

/-- **Bernstein's inequality, two-sided, at confidence level `δ`** [BLM13, Theorem 2.10]. Under
the hypotheses of `measureReal_sqrt_add_le_abs_sum_le_of_abs_le`, for `δ > 0`, with probability
at least `1 - δ`, `|∑ i ∈ s, X i| < √(2 v log (2 / δ)) + b log (2 / δ) / 3`. -/
theorem measureReal_sqrt_log_add_le_abs_sum_le_of_abs_le (h_indep : iIndepFun X μ) {b v δ : ℝ}
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) (hmean : ∀ i ∈ s, μ[X i] = 0) (hb : 0 < b)
    (hXb : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ b) (hv : ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ ≤ v) (hδ : 0 < δ) :
    μ.real {ω | √(2 * v * log (2 / δ)) + b * log (2 / δ) / 3 ≤ |∑ i ∈ s, X i ω|} ≤ δ := by
  have hexp : 2 * exp (-log (2 / δ)) = δ := by
    rw [← log_inv, inv_div, exp_log (by positivity), mul_div_cancel₀ _ two_ne_zero]
  simpa only [hexp] using
    h_indep.measureReal_sqrt_add_le_abs_sum_le_of_abs_le (L := log (2 / δ)) hX hmean hb hXb hv

end ProbabilityTheory.iIndepFun
