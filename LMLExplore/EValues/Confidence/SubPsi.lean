/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Confidence.Sequence
public import LMLExplore.EValues.SubPsi

/-!
# Confidence sequences from sub-ψ processes

A family `(S θ, V θ)` of `1`-sub-ψ processes on `Λ` for the nulls `𝒩 θ` gives, for every
`t ∈ Λ`, the e-processes `exp (t S θ n - ψ t V θ n)` for `𝒩 θ`, hence the confidence sequence
`{θ | t S θ n - ψ t V θ n < log δ⁻¹}` at level `δ` [HRMS21, §3; WSR24, Theorem 1]. This file
specialises it to the mean of real observations `X k`, with `S m n = ∑ k < n, (X k - m)`. It
treats the general null of the sub-ψ bets and derives the four classical cases from it:

* **the null of the sub-ψ bets** for the centred observations `X k - m`, under which every bet
  `exp (t (X k - m) - ψ t)`, `t ∈ Λ`, is a conditional e-variable given the past: for `t > 0` the
  bound `∑ k < n, X k - (log δ⁻¹ + n ψ t) / t < n m` holds for all `n` at once except with
  probability at most `δ`, for `-t ∈ Λ` the reverse bound, and both together at level `δ` with
  `log (2 / δ)`;
* **sub-Gaussian** observations, `ψ t = c t ^ 2 / 2` on `ℝ`: for `c ≥ 0`, the laws with
  conditionally `c`-sub-Gaussian centred observations (Mathlib's `HasCondSubgaussianMGF`) are
  members, and the confidence sequence is `|∑ k < n, X k - n m| < log (2 / δ) / u + n c u / 2`;
* **Hoeffding**: observations in `[a, b]` with conditional mean `m` are conditionally
  `(b - a) ^ 2 / 4`-sub-Gaussian, which gives the confidence sequence
  `|∑ k < n, X k - n m| < log (2 / δ) / u + n (b - a) ^ 2 u / 8`;
* **Bernoulli**: observations in `[0, 1]` with conditional mean at most `q` have the moment
  generating function of the Bernoulli law of mean `q` as a bound at `t ≥ 0`, which gives the
  confidence sequence `{q | t ∑ k < n, X k - n log (1 - q + q exp t) < log δ⁻¹}` for the means, and
  symmetrically at `t ≤ 0` for observations with conditional mean at least `q`;
* **Freedman**: centred observations `X k - m ≤ b` with nonpositive conditional mean and with
  conditional second moment at most a predictable bound `v k` are sub-Poisson with the intrinsic
  time `∑ k < n, v k`, which gives the confidence sequence
  `∑ k < n, X k - (log δ⁻¹ + ψ_b t ∑ k < n, v k) / t < n m`, with
  `ψ_b t = (exp (t b) - 1 - t b) / b ^ 2`. For a constant bound `v k = σ²` this is Bennett's
  inequality, uniformly in time.

Each confidence sequence holds at every time simultaneously, so it may be read at any stopping
time (`ProbabilityTheory.isConfSeq_tfae`). The memberships of the classical laws in the nulls of
the sub-ψ bets, and Freedman's sub-ψ process with a predictable variance bound, are in
`LMLExplore.EValues.SubPsi`.

## Main statements

* `ProbabilityTheory.isConfSeq_of_isSubPsiProcess`,
  `ProbabilityTheory.isConfSeq_lt_log_of_isSubPsiProcess`: confidence sequences from families of
  sub-ψ processes.
* `ProbabilityTheory.isConfSeq_lt_log_condEVarNull`,
  `ProbabilityTheory.isConfSeq_sub_div_lt_mul_condEVarNull`,
  `ProbabilityTheory.isConfSeq_mul_lt_add_div_condEVarNull`,
  `ProbabilityTheory.isConfSeq_sub_div_lt_mul_and_mul_lt_add_div_condEVarNull`: the confidence
  sequences for the mean under the nulls of the sub-ψ bets.
* `ProbabilityTheory.isConfSeq_abs_sum_sub_mul_lt_condEVarNull`: the sub-Gaussian case.
* `ProbabilityTheory.isConfSeq_abs_sum_sub_mul_lt_of_mem_Icc`: the Hoeffding case.
* `ProbabilityTheory.isConfSeq_mul_sum_sub_mul_log_lt_log_of_condExp_le`,
  `ProbabilityTheory.isConfSeq_mul_sum_sub_mul_log_lt_log_of_le_condExp`: the Bernoulli case.
* `ProbabilityTheory.isConfSeq_sum_sub_div_lt_mul_of_condExp_sq_le`: the Freedman case.

## References

* [HRMS20] S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, *Time-uniform Chernoff bounds via
  nonnegative supermartingales*, Probab. Surveys 17 (2020), 257–317, arXiv:1808.03204, §2 and
  Fact 1.
* [HRMS21] S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, *Time-uniform, nonparametric,
  nonasymptotic confidence sequences*, Ann. Statist. 49 (2021), §3.
* [WSR24] I. Waudby-Smith and A. Ramdas, *Estimating means of bounded random variables by
  betting*, J. R. Stat. Soc. Ser. B 86 (2024), arXiv:2010.09686v7, Theorem 1.
* [Fre75] D. A. Freedman, *On tail probabilities for martingales*, Ann. Probab. 3 (1975), 100–118.
-/

public section

open MeasureTheory Set Finset Real
open scoped ENNReal unitInterval

namespace ProbabilityTheory

variable {Ω Θ : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
  {ψ : ℝ → ℝ} {Λ : Set ℝ} {t u δ : ℝ}

/-! ### Confidence sequences from sub-ψ processes -/

section SubPsiProcess

variable {S V : Θ → ℕ → Ω → ℝ} {φ : Θ → ℝ → ℝ} {𝒩 : Θ → Set (Measure Ω)}

/-- **Confidence sequences from sub-ψ processes** [HRMS21, §3]. For a family of `l₀`-sub-`φ θ`
processes `(S θ, V θ)` on `Λ` for nulls `𝒩 θ` of probability measures, with `S θ` and `V θ`
adapted, and for every `t ∈ Λ`, the parameters `θ` with
`l₀⁻¹ exp (t S θ n - φ θ t V θ n) < α⁻¹` form a confidence sequence at level `α`. -/
theorem isConfSeq_of_isSubPsiProcess {l₀ : ℝ≥0∞}
    (h : ∀ θ, IsSubPsiProcess (S θ) (V θ) (φ θ) Λ l₀ ℱ (𝒩 θ))
    (h𝒩 : ∀ θ, ∀ P ∈ 𝒩 θ, IsProbabilityMeasure P) (hS : ∀ θ n, Measurable[ℱ n] (S θ n))
    (hV : ∀ θ n, Measurable[ℱ n] (V θ n)) (ht : t ∈ Λ) (α : ℝ≥0∞) :
    IsConfSeq
      (fun n ω ↦ {θ | l₀⁻¹ * ENNReal.ofReal (exp (t * S θ n ω - φ θ t * V θ n ω)) < α⁻¹}) ℱ 𝒩
      α :=
  isConfSeq_of_isEProcess (fun θ ↦ (h θ).isEProcess (h𝒩 θ) (hS θ) (hV θ) ht) α

/-- **Confidence sequences from sub-ψ processes, logarithmic form** [HRMS21, §3]. For a family of
`1`-sub-`φ θ` processes `(S θ, V θ)` on `Λ` for nulls `𝒩 θ` of probability measures, with `S θ`
and `V θ` adapted, for every `t ∈ Λ` and every level `δ > 0`, the parameters `θ` with
`t S θ n - φ θ t V θ n < log δ⁻¹` form a confidence sequence at level `δ`. -/
theorem isConfSeq_lt_log_of_isSubPsiProcess
    (h : ∀ θ, IsSubPsiProcess (S θ) (V θ) (φ θ) Λ 1 ℱ (𝒩 θ))
    (h𝒩 : ∀ θ, ∀ P ∈ 𝒩 θ, IsProbabilityMeasure P) (hS : ∀ θ n, Measurable[ℱ n] (S θ n))
    (hV : ∀ θ n, Measurable[ℱ n] (V θ n)) (ht : t ∈ Λ) (hδ : 0 < δ) :
    IsConfSeq (fun n ω ↦ {θ | t * S θ n ω - φ θ t * V θ n ω < log δ⁻¹}) ℱ 𝒩
      (ENNReal.ofReal δ) := by
  -- `exp x < δ⁻¹` exactly when `x < log δ⁻¹`
  have key (x : ℝ) :
      (1 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (exp x) < (ENNReal.ofReal δ)⁻¹ ↔ x < log δ⁻¹ := by
    rw [inv_one, one_mul, ← ENNReal.ofReal_inv_of_pos hδ,
      ENNReal.ofReal_lt_ofReal_iff (inv_pos.2 hδ), lt_log_iff_exp_lt (inv_pos.2 hδ)]
  simpa only [key] using isConfSeq_of_isSubPsiProcess h h𝒩 hS hV ht (ENNReal.ofReal δ)

end SubPsiProcess

/-! ### The mean under the null of the sub-ψ bets -/

/-- The partial sums `∑ k < n, f k` are `ℱ n`-measurable when each `f k` is
`ℱ (k + 1)`-measurable. -/
private lemma measurable_sum_range_of_succ {f : ℕ → Ω → ℝ}
    (hf : ∀ k, Measurable[ℱ (k + 1)] (f k)) (n : ℕ) :
    Measurable[ℱ n] fun ω ↦ ∑ k ∈ range n, f k ω :=
  Finset.measurable_fun_sum _ fun k hk ↦ (hf k).mono (ℱ.mono (mem_range.1 hk)) le_rfl

/-- `∑ k < n, (x k - m) = ∑ k < n, x k - n m`. -/
private lemma sum_range_sub_const (x : ℕ → ℝ) (m : ℝ) (n : ℕ) :
    ∑ k ∈ range n, (x k - m) = ∑ k ∈ range n, x k - n * m := by
  rw [Finset.sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]

/-- **Confidence sequences for the mean under the nulls of the sub-ψ bets** [HRMS21, §3]. Let
each observation `X k` be `ℱ (k + 1)`-measurable, and for a candidate mean `m` let the null be the
laws under which every sub-ψ bet `exp (t (X k - m) - ψ t)`, `t ∈ Λ`, is a conditional e-variable
given the past. For every `t ∈ Λ` and every `δ > 0`, the means `m` with
`t (∑ k < n, X k - n m) - n ψ t < log δ⁻¹` form a confidence sequence at level `δ`. -/
theorem isConfSeq_lt_log_condEVarNull (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) (ht : t ∈ Λ)
    (hδ : 0 < δ) :
    IsConfSeq (fun n ω ↦ {m | t * (∑ k ∈ range n, X k ω - n * m) - n * ψ t < log δ⁻¹}) ℱ
      (fun m ↦ condEVarNull (subPsiBets ψ Λ) (fun k ω ↦ X k ω - m) ℱ) (ENNReal.ofReal δ) := by
  have h := isConfSeq_lt_log_of_isSubPsiProcess (φ := fun _ ↦ ψ) (Λ := Λ) (ℱ := ℱ)
    (S := fun m n ω ↦ ∑ k ∈ range n, (X k ω - m)) (V := fun _ n _ ↦ n)
    (fun m ↦ isSubPsiProcess_sum_condEVarNull fun k ↦ (hX k).sub_const m)
    (fun _ _ hP ↦ isProbabilityMeasure_of_mem_condEVarNull hP)
    (fun m ↦ measurable_sum_range_of_succ fun k ↦ (hX k).sub_const m)
    (fun _ _ ↦ measurable_const) ht hδ
  simpa only [sum_range_sub_const, mul_comm (ψ t)] using h

/-- **Lower confidence bounds for the mean under the nulls of the sub-ψ bets** [HRMS21, §3]. Let
each observation `X k` be `ℱ (k + 1)`-measurable. For a parameter `t > 0` of `Λ` and `δ > 0`, the
means `m` with `∑ k < n, X k - (log δ⁻¹ + n ψ t) / t < n m` form a confidence sequence at level `δ`
for the nulls of the sub-ψ bets on the centred observations `X k - m`. -/
theorem isConfSeq_sub_div_lt_mul_condEVarNull (hX : ∀ k, Measurable[ℱ (k + 1)] (X k))
    (ht : t ∈ Λ) (ht0 : 0 < t) (hδ : 0 < δ) :
    IsConfSeq (fun n ω ↦ {m | ∑ k ∈ range n, X k ω - (log δ⁻¹ + n * ψ t) / t < n * m}) ℱ
      (fun m ↦ condEVarNull (subPsiBets ψ Λ) (fun k ω ↦ X k ω - m) ℱ) (ENNReal.ofReal δ) := by
  convert isConfSeq_lt_log_condEVarNull hX ht hδ using 4 with n ω
  ext m
  rw [sub_lt_comm, lt_div_iff₀ ht0]
  constructor <;> intro h <;> linarith

/-- **Upper confidence bounds for the mean under the nulls of the sub-ψ bets** [HRMS21, §3]. Let
each observation `X k` be `ℱ (k + 1)`-measurable. For `u > 0` with `-u ∈ Λ` and `δ > 0`, the means
`m` with `n m < ∑ k < n, X k + (log δ⁻¹ + n ψ (-u)) / u` form a confidence sequence at level `δ`
for the nulls of the sub-ψ bets on the centred observations `X k - m`. -/
theorem isConfSeq_mul_lt_add_div_condEVarNull (hX : ∀ k, Measurable[ℱ (k + 1)] (X k))
    (hu : -u ∈ Λ) (hu0 : 0 < u) (hδ : 0 < δ) :
    IsConfSeq (fun n ω ↦ {m | n * m < ∑ k ∈ range n, X k ω + (log δ⁻¹ + n * ψ (-u)) / u}) ℱ
      (fun m ↦ condEVarNull (subPsiBets ψ Λ) (fun k ω ↦ X k ω - m) ℱ) (ENNReal.ofReal δ) := by
  convert isConfSeq_lt_log_condEVarNull hX hu hδ using 4 with n ω
  ext m
  rw [← sub_lt_iff_lt_add', lt_div_iff₀ hu0]
  constructor <;> intro h <;> linarith

/-- **Two-sided confidence sequences for the mean under the nulls of the sub-ψ bets**
[HRMS21, §3]. Let each observation `X k` be `ℱ (k + 1)`-measurable. For `u > 0` with `u ∈ Λ` and
`-u ∈ Λ` and for `δ > 0`, the means `m` with
`∑ k < n, X k - (log (2 / δ) + n ψ u) / u < n m < ∑ k < n, X k + (log (2 / δ) + n ψ (-u)) / u`
form a confidence sequence at level `δ` for the nulls of the sub-ψ bets on the centred
observations `X k - m`: it is the intersection of the two one-sided ones at level `δ / 2`. -/
theorem isConfSeq_sub_div_lt_mul_and_mul_lt_add_div_condEVarNull
    (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) (hu : u ∈ Λ) (hu' : -u ∈ Λ) (hu0 : 0 < u)
    (hδ : 0 < δ) :
    IsConfSeq (fun n ω ↦ {m | ∑ k ∈ range n, X k ω - (log (2 / δ) + n * ψ u) / u < n * m ∧
        n * m < ∑ k ∈ range n, X k ω + (log (2 / δ) + n * ψ (-u)) / u}) ℱ
      (fun m ↦ condEVarNull (subPsiBets ψ Λ) (fun k ω ↦ X k ω - m) ℱ) (ENNReal.ofReal δ) := by
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have h := (isConfSeq_sub_div_lt_mul_condEVarNull (ψ := ψ) hX hu hu0 hδ2).inter
    (isConfSeq_mul_lt_add_div_condEVarNull (ψ := ψ) hX hu' hu0 hδ2)
  rw [← ENNReal.ofReal_add hδ2.le hδ2.le, add_halves, inv_div] at h
  simpa only [inter_self, ← ofPred_and] using h

/-! ### Sub-Gaussian observations -/

section SubGaussian

/-- **Confidence sequences for the mean of sub-Gaussian observations** [HRMS21, §3]. Let each
observation `X k` be `ℱ (k + 1)`-measurable. For `u > 0` and `δ > 0`, the means `m` with
`|∑ k < n, X k - n m| < log (2 / δ) / u + n c u / 2` form a confidence sequence at level `δ` for
the nulls of the sub-Gaussian bets `exp (t (x - m) - c t ^ 2 / 2)`, `t ∈ ℝ`, on the observations.
For `c ≥ 0` and a standard Borel `Ω`, these nulls contain the laws with conditionally
`c`-sub-Gaussian centred observations
(`ProbabilityTheory.mem_condEVarNull_subPsiBets_of_hasCondSubgaussianMGF`). -/
theorem isConfSeq_abs_sum_sub_mul_lt_condEVarNull {c : ℝ} (hX : ∀ k, Measurable[ℱ (k + 1)] (X k))
    (hu0 : 0 < u) (hδ : 0 < δ) :
    IsConfSeq
      (fun n ω ↦ {m | |∑ k ∈ range n, X k ω - n * m| < log (2 / δ) / u + n * c * u / 2}) ℱ
      (fun m ↦ condEVarNull (subPsiBets (fun t ↦ c * t ^ 2 / 2) univ) (fun k ω ↦ X k ω - m) ℱ)
      (ENNReal.ofReal δ) := by
  convert isConfSeq_sub_div_lt_mul_and_mul_lt_add_div_condEVarNull hX (mem_univ u)
    (mem_univ (-u)) hu0 hδ using 4 with n ω
  ext m
  -- both widths are `log (2 / δ) / u + n c u / 2`
  have hw : (log (2 / δ) + n * (c * u ^ 2 / 2)) / u = log (2 / δ) / u + n * c * u / 2 := by
    field_simp
  rw [neg_sq, hw, abs_sub_lt_iff]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

end SubGaussian

/-! ### Hoeffding: bounded observations -/

section Hoeffding

variable {a b : ℝ}

/-- **Hoeffding confidence sequences for the mean of bounded observations** [HRMS21, §3]. Let each
observation `X k` be `ℱ (k + 1)`-measurable. For `u > 0` and `δ > 0`, the means `m` with
`|∑ k < n, X k - n m| < log (2 / δ) / u + n (b - a) ^ 2 u / 8` form a confidence sequence at level
`δ` for the nulls of the laws under which every observation has values in `[a, b]` and conditional
mean `m` given the past. -/
theorem isConfSeq_abs_sum_sub_mul_lt_of_mem_Icc [StandardBorelSpace Ω]
    (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) (hu0 : 0 < u) (hδ : 0 < δ) :
    IsConfSeq
      (fun n ω ↦ {m | |∑ k ∈ range n, X k ω - n * m| <
        log (2 / δ) / u + n * (b - a) ^ 2 * u / 8}) ℱ
      (fun m ↦ {P | IsProbabilityMeasure P ∧
        ∀ k, (∀ᵐ ω ∂P, X k ω ∈ Icc a b) ∧ P[X k | ℱ k] =ᵐ[P] fun _ ↦ m})
      (ENNReal.ofReal δ) := by
  have hX' (k : ℕ) : Measurable (X k) := (hX k).mono (ℱ.le _) le_rfl
  -- the sub-Gaussian confidence sequence with variance proxy `(b - a) ^ 2 / 4`
  have h := isConfSeq_abs_sum_sub_mul_lt_condEVarNull (c := (b - a) ^ 2 / 4) hX hu0 hδ
  have hψ : (fun t ↦ (b - a) ^ 2 / 4 * t ^ 2 / 2) = fun t ↦ (b - a) ^ 2 * t ^ 2 / 8 := by
    ext t
    ring
  have hw (n : ℕ) : (n : ℝ) * ((b - a) ^ 2 / 4) * u / 2 = n * (b - a) ^ 2 * u / 8 := by ring
  simp only [hψ, hw] at h
  exact h.anti_set fun m P ⟨hP, hPX⟩ ↦
    mem_condEVarNull_subPsiBets_of_mem_Icc hX' (fun k ↦ (hPX k).1) fun k ↦ (hPX k).2

end Hoeffding

/-! ### Bernoulli: observations in `[0, 1]` -/

section Bernoulli

/-- The confidence sequence of the Bernoulli bets for the parameters `q`, for any family of nulls
contained in the nulls of the Bernoulli bets on `Λ`. -/
private lemma isConfSeq_mul_sum_sub_mul_log_lt_log_of_subset {𝒩 : I → Set (Measure Ω)}
    (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) (ht : t ∈ Λ) (hδ : 0 < δ)
    (h𝒩 : ∀ q, 𝒩 q ⊆ condEVarNull (subPsiBets (fun t ↦ log (1 - q + q * exp t)) Λ) X ℱ) :
    IsConfSeq
      (fun n ω ↦ {q : I | t * ∑ k ∈ range n, X k ω - n * log (1 - q + q * exp t) < log δ⁻¹}) ℱ
      𝒩 (ENNReal.ofReal δ) := by
  have h := isConfSeq_lt_log_of_isSubPsiProcess (Λ := Λ) (ℱ := ℱ) (t := t)
    (φ := fun (q : I) t ↦ log (1 - q + q * exp t))
    (S := fun _ n ω ↦ ∑ k ∈ range n, X k ω) (V := fun _ n _ ↦ n)
    (fun q ↦ (isSubPsiProcess_sum_condEVarNull hX).anti_set (h𝒩 q))
    (fun q _ hP ↦ isProbabilityMeasure_of_mem_condEVarNull (h𝒩 q hP))
    (fun _ ↦ measurable_sum_range_of_succ hX) (fun _ _ ↦ measurable_const) ht hδ
  simpa only [mul_comm (log _)] using h

/-- **Bernoulli lower confidence bounds for the mean** [HRMS20, Fact 1; HRMS21, §3].
Let each observation `X k` be `ℱ (k + 1)`-measurable. For `t ≥ 0` and `δ > 0`, the parameters `q`
with `t ∑ k < n, X k - n log (1 - q + q exp t) < log δ⁻¹` form a confidence sequence at level `δ`
for the nulls of the laws under which every observation has values in `[0, 1]` and conditional
mean at most `q` given the past. -/
theorem isConfSeq_mul_sum_sub_mul_log_lt_log_of_condExp_le [StandardBorelSpace Ω]
    (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) (ht : 0 ≤ t) (hδ : 0 < δ) :
    IsConfSeq
      (fun n ω ↦ {q : I | t * ∑ k ∈ range n, X k ω - n * log (1 - q + q * exp t) < log δ⁻¹}) ℱ
      (fun q ↦ {P | IsProbabilityMeasure P ∧
        ∀ k, (∀ᵐ ω ∂P, X k ω ∈ Set.Icc 0 1) ∧ P[X k | ℱ k] ≤ᵐ[P] fun _ ↦ (q : ℝ)})
      (ENNReal.ofReal δ) :=
  isConfSeq_mul_sum_sub_mul_log_lt_log_of_subset hX (Set.mem_Ici.2 ht) hδ fun _ _ ⟨_, hPX⟩ ↦
    mem_condEVarNull_subPsiBets_log_of_condExp_le (fun k ↦ (hX k).mono (ℱ.le _) le_rfl)
      (fun k ↦ (hPX k).1) fun k ↦ (hPX k).2

/-- **Bernoulli upper confidence bounds for the mean** [HRMS20, Fact 1; HRMS21, §3].
Let each observation `X k` be `ℱ (k + 1)`-measurable. For `t ≤ 0` and `δ > 0`, the parameters `q`
with `t ∑ k < n, X k - n log (1 - q + q exp t) < log δ⁻¹` form a confidence sequence at level `δ`
for the nulls of the laws under which every observation has values in `[0, 1]` and conditional
mean at least `q` given the past. -/
theorem isConfSeq_mul_sum_sub_mul_log_lt_log_of_le_condExp [StandardBorelSpace Ω]
    (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) (ht : t ≤ 0) (hδ : 0 < δ) :
    IsConfSeq
      (fun n ω ↦ {q : I | t * ∑ k ∈ range n, X k ω - n * log (1 - q + q * exp t) < log δ⁻¹}) ℱ
      (fun q ↦ {P | IsProbabilityMeasure P ∧
        ∀ k, (∀ᵐ ω ∂P, X k ω ∈ Set.Icc 0 1) ∧ (fun _ ↦ (q : ℝ)) ≤ᵐ[P] P[X k | ℱ k]})
      (ENNReal.ofReal δ) :=
  isConfSeq_mul_sum_sub_mul_log_lt_log_of_subset hX (Set.mem_Iic.2 ht) hδ fun _ _ ⟨_, hPX⟩ ↦
    mem_condEVarNull_subPsiBets_log_of_le_condExp (fun k ↦ (hX k).mono (ℱ.le _) le_rfl)
      (fun k ↦ (hPX k).1) fun k ↦ (hPX k).2

end Bernoulli

/-! ### Freedman: observations bounded above with a predictable variance bound -/

section Freedman

variable {v : ℕ → Ω → ℝ} {b : ℝ}

/-- **Freedman confidence sequences for the mean** [Fre75; HRMS20, Fact 1(c); HRMS21, §3]. Let each
observation `X k` be `ℱ (k + 1)`-measurable and `v k` be `ℱ k`-measurable, and let `b > 0`. For
`t > 0` and `δ > 0`, the means `m` with
`∑ k < n, X k - (log δ⁻¹ + ψ_b t ∑ k < n, v k) / t < n m`, with
`ψ_b t = (exp (t b) - 1 - t b) / b ^ 2`, form a confidence sequence at level `δ` for the nulls of
the laws under which the centred observations `X k - m` have integrable squares, are at most `b`,
and have nonpositive conditional mean and conditional second moment at most `v k` given the past.
For a constant `v k = σ²` this is Bennett's inequality, uniformly in time. -/
theorem isConfSeq_sum_sub_div_lt_mul_of_condExp_sq_le (hX : ∀ k, Measurable[ℱ (k + 1)] (X k))
    (hv : ∀ k, Measurable[ℱ k] (v k)) (hb : 0 < b) (ht0 : 0 < t) (hδ : 0 < δ) :
    IsConfSeq (fun n ω ↦ {m | ∑ k ∈ range n, X k ω -
        (log δ⁻¹ + (exp (t * b) - 1 - t * b) / b ^ 2 * ∑ k ∈ range n, v k ω) / t < n * m}) ℱ
      (fun m ↦ {P | IsProbabilityMeasure P ∧ ∀ k, Integrable (fun ω ↦ (X k ω - m) ^ 2) P ∧
        (∀ᵐ ω ∂P, X k ω - m ≤ b) ∧ P[fun ω ↦ X k ω - m | ℱ k] ≤ᵐ[P] 0 ∧
        P[fun ω ↦ (X k ω - m) ^ 2 | ℱ k] ≤ᵐ[P] v k})
      (ENNReal.ofReal δ) := by
  have h := isConfSeq_lt_log_of_isSubPsiProcess
    (fun m ↦ isSubPsiProcess_sum_sub_sum_of_condExp_sq_le hX hv hb m) (fun _ _ hP ↦ hP.1)
    (fun m ↦ measurable_sum_range_of_succ fun k ↦ (hX k).sub_const m)
    (fun _ ↦ measurable_sum_range_of_succ fun k ↦ (hv k).mono (ℱ.mono k.le_succ) le_rfl)
    (Set.mem_Ici.2 ht0.le) hδ
  convert h using 4 with n ω
  ext m
  rw [sum_range_sub_const, sub_lt_comm, lt_div_iff₀ ht0]
  constructor <;> intro h <;> linarith

end Freedman

end ProbabilityTheory
