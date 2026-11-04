/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Distributions.ExponentialFamily.Mean

/-!
# The lower bound of Cramér's theorem for exponential families

Let `ρ` be a measure on a measurable space `𝓧` and `T : 𝓧 → ℝ` a statistic, with log-partition
function `ψ = cgf T ρ`, and let `ρ_η(μ)` be the member of mean `μ` of their exponential family.
For independent observations `Y i` with law `ρ_η(μ)` and a mean `x` of the family, the empirical
mean of the statistics `T (Y i)` is close to `x` with probability at least of the order of
`exp (-(n d(x, μ)))` for `n` observations, where `d(x, μ) = KL(ρ_η(x), ρ_η(μ))`. This is the lower
half of Cramér's theorem for exponential families: together with the Cramér–Chernoff upper bounds
of `LMLExplore.Probability.Distributions.ExponentialFamily.Chernoff`, it shows that `d(x, μ)` is
the exact exponential rate of the probability that the empirical mean is near `x`. In
identification, these bounds give the error exponents of algorithms that sample the arms with
fixed proportions.

The proof tilts the law of the sum `S = ∑ i ∈ s, T (Y i)` by `t = η(x) - η(μ)`
(`ProbabilityTheory.exp_mul_le_measureReal_abs_sub_deriv_cgf_le`). The cumulant generating
function of `S` is `u ↦ #s (ψ(η(μ) + u) - ψ(η(μ)))` near `t`, so that under the tilted measure
`S` has mean `#s x` and variance `#s Var(T)`, with the variance of `T` under `ρ_η(x)`, and the
exponent `t (#s x) - cgf S t` of the change of measure is `#s d(x, μ)`.

## Main statements

* `ProbabilityTheory.iIndepFun.exp_mul_le_measureReal_abs_sum_sub_le_of_hasLaw`: for `#s`
  independent observations with law `ρ_η(μ)`, a mean `x` of the family and `r > 0`,
  `exp (-(#s (d(x, μ) + |η(x) - η(μ)| r))) (1 - Var(T) / (#s r²)) ≤
  P(|∑ i ∈ s, T (Y i) - #s x| ≤ #s r)`.
* `ProbabilityTheory.iIndepFun.eventually_exp_le_measureReal_abs_sum_sub_le_of_hasLaw`:
  **Cramér's lower bound**: for a sequence of independent observations with law `ρ_η(μ)`, every
  `r > 0` and every `ε > 0`, eventually in `n`,
  `exp (-(n (d(x, μ) + ε))) ≤ P(|∑ i < n, T (Y i) - n x| ≤ n r)`.

## References

* A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed., Springer,
  1998, Section 2.2 (Cramér's theorem, and the change of measure in the proof of its lower bound).
-/

public section

open MeasureTheory Real Finset Filter

open scoped Topology ProbabilityTheory

namespace ProbabilityTheory

variable {Ω ι 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {P : Measure Ω}
  {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {μ x r : ℝ}

/-- **Lower bound on the probability that the empirical mean is near a mean of the family.** For
independent random variables `Y i`, `i ∈ s`, with law the member `ρ_η(μ)` of mean `μ` of the
exponential family of `ρ` and `T`, a mean `x` of the family and `r > 0`,
`exp (-(#s (d(x, μ) + |η(x) - η(μ)| r))) (1 - Var(T) / (#s r²))` is at most the probability that
`|∑ i ∈ s, T (Y i) - #s x| ≤ #s r`, where `d(x, μ) = KL(ρ_η(x), ρ_η(μ))` and `Var(T)` is the
variance of `T` under the member `ρ_η(x)` of mean `x`. -/
theorem iIndepFun.exp_mul_le_measureReal_abs_sum_sub_le_of_hasLaw {Y : ι → Ω → 𝓧} {s : Finset ι}
    (h_indep : iIndepFun Y P) (hY : ∀ i ∈ s, HasLaw (Y i) (ρ.expFamily T (ρ.natParam T μ)) P)
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) (hr : 0 < r) :
    exp (-(#s * (ρ.expFamilyDiv T x μ + |ρ.natParam T x - ρ.natParam T μ| * r))) *
        (1 - Var[T; ρ.expFamily T (ρ.natParam T x)] / (#s * r ^ 2)) ≤
      P.real {ω | |∑ i ∈ s, T (Y i ω) - #s * x| ≤ #s * r} := by
  have := h_indep.isProbabilityMeasure
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  set η := ρ.natParam T μ
  set t := ρ.natParam T x - η
  set I := integrableExpSet T ρ
  have hη : η ∈ interior I := Measure.natParam_mem_interior_integrableExpSet hμ
  have hηt : η + t = ρ.natParam T x := add_sub_cancel η _
  have hx' : η + t ∈ interior I := hηt ▸ Measure.natParam_mem_interior_integrableExpSet hx
  have hT : AEMeasurable T ρ := aemeasurable_of_mem_interior_integrableExpSet hη
  -- The open set of the parameters `u` with `η + u` in the interior of the natural parameters.
  set U := (η + ·) ⁻¹' interior I
  have hU : IsOpen U := isOpen_interior.preimage (continuous_const_add η)
  have hU_sub : U ⊆ integrableExpSet (fun ω ↦ ∑ i ∈ s, T (Y i ω)) P := fun u hu ↦
    h_indep.integrable_exp_mul_sum_of_hasLaw_expFamily hT hY (interior_subset hη)
      (interior_subset hu)
  have ht : t ∈ interior (integrableExpSet (fun ω ↦ ∑ i ∈ s, T (Y i ω)) P) :=
    interior_maximal hU_sub hU hx'
  -- Near `t`, the cumulant generating function of the sum is `u ↦ #s (ψ(η + u) - ψ(η))`.
  have h_cgf (u : ℝ) (hu : u ∈ U) : cgf (fun ω ↦ ∑ i ∈ s, T (Y i ω)) P u =
      #s * (cgf T ρ (η + u) - cgf T ρ η) :=
    h_indep.cgf_sum_of_hasLaw_expFamily hT hY (interior_subset hη) (interior_subset hu)
  have h_eq : cgf (fun ω ↦ ∑ i ∈ s, T (Y i ω)) P =ᶠ[𝓝 t]
      fun u ↦ #s * (cgf T ρ (η + u) - cgf T ρ η) :=
    eventually_of_mem (hU.mem_nhds hx') h_cgf
  have h_deriv : deriv (fun u ↦ #s * (cgf T ρ (η + u) - cgf T ρ η)) =
      fun u ↦ #s * deriv (cgf T ρ) (η + u) := by
    ext u
    simp only [deriv_const_mul_field', deriv_sub_const, deriv_comp_const_add]
  have h_mean : deriv (cgf (fun ω ↦ ∑ i ∈ s, T (Y i ω)) P) t = #s * x := by
    rw [h_eq.deriv_eq, h_deriv]
    beta_reduce
    rw [hηt, Measure.deriv_cgf_natParam hx]
  have h_var : iteratedDeriv 2 (cgf (fun ω ↦ ∑ i ∈ s, T (Y i ω)) P) t =
      #s * Var[T; ρ.expFamily T (ρ.natParam T x)] := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, h_eq.deriv.deriv_eq, h_deriv]
    simp only [deriv_const_mul_field', deriv_comp_const_add]
    rw [hηt, Measure.variance_expFamily (Measure.natParam_mem_interior_integrableExpSet hx),
      iteratedDeriv_succ, iteratedDeriv_one]
  have h_bound := exp_mul_le_measureReal_abs_sub_deriv_cgf_le ht
    (mul_pos (Nat.cast_pos.2 hs.card_pos) hr)
  rw [h_mean, h_var, h_cgf t (hx' : η + t ∈ interior I)] at h_bound
  convert h_bound using 3
  · rw [Measure.expFamilyDiv_def, hηt]
    ring
  · have : (#s : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hs.card_pos.ne'
    field_simp

/-- **Cramér's lower bound for exponential families.** For a sequence of independent random
variables `Y i` with law the member `ρ_η(μ)` of mean `μ` of the exponential family of `ρ` and `T`,
a mean `x` of the family, `r > 0` and `ε > 0`, eventually in `n`, the probability that
`|∑ i < n, T (Y i) - n x| ≤ n r` is at least `exp (-(n (d(x, μ) + ε)))`, where
`d(x, μ) = KL(ρ_η(x), ρ_η(μ))`. Equivalently,
`liminf (1 / n) log P(|∑ i < n, T (Y i) / n - x| ≤ r) ≥ -d(x, μ)`. -/
theorem iIndepFun.eventually_exp_le_measureReal_abs_sum_sub_le_of_hasLaw {Y : ℕ → Ω → 𝓧}
    (h_indep : iIndepFun Y P) (hY : ∀ i, HasLaw (Y i) (ρ.expFamily T (ρ.natParam T μ)) P)
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) (hr : 0 < r) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, exp (-(n * (ρ.expFamilyDiv T x μ + ε))) ≤
      P.real {ω | |∑ i ∈ range n, T (Y i ω) - n * x| ≤ n * r} := by
  set t := ρ.natParam T x - ρ.natParam T μ
  set V := Var[T; ρ.expFamily T (ρ.natParam T x)]
  -- A smaller radius `r'`, for which the cost `|t| r'` of the tilt is at most `ε / 2`.
  set r' := min r (ε / (2 * (|t| + 1)))
  have hr' : 0 < r' := lt_min hr (by positivity)
  have h_tr' : |t| * r' ≤ ε / 2 := by
    calc |t| * r' ≤ (|t| + 1) * (ε / (2 * (|t| + 1))) := by
          gcongr
          · linarith [abs_nonneg t]
          · exact min_le_right _ _
    _ = ε / 2 := by field_simp
  -- Eventually, `exp (-(n ε / 2)) ≤ 1 / 2 ≤ 1 - V / (n r'²)`.
  have h_exp : Tendsto (fun n : ℕ ↦ exp (-(n * (ε / 2)))) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)))
  have h_var : Tendsto (fun n : ℕ ↦ V / r' ^ 2 / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  filter_upwards [(tendsto_order.1 h_exp).2 (1 / 2) (by norm_num),
    (tendsto_order.1 h_var).2 (1 / 2) (by norm_num)] with n hn_exp hn_var
  have h_bound := h_indep.exp_mul_le_measureReal_abs_sum_sub_le_of_hasLaw (s := range n)
    (fun i _ ↦ hY i) hμ hx hr'
  rw [card_range] at h_bound
  have h_one_sub : 1 / 2 ≤ 1 - V / (n * r' ^ 2) := by
    rw [mul_comm, ← div_div]
    linarith
  calc exp (-(n * (ρ.expFamilyDiv T x μ + ε)))
  _ = exp (-(n * (ρ.expFamilyDiv T x μ + ε / 2))) * exp (-(n * (ε / 2))) := by
    rw [← exp_add]
    congr 1
    ring
  _ ≤ exp (-(n * (ρ.expFamilyDiv T x μ + |t| * r'))) * (1 - V / (n * r' ^ 2)) := by
    gcongr
    linarith
  _ ≤ P.real {ω | |∑ i ∈ range n, T (Y i ω) - n * x| ≤ n * r'} := h_bound
  _ ≤ P.real {ω | |∑ i ∈ range n, T (Y i ω) - n * x| ≤ n * r} := by
    have := h_indep.isProbabilityMeasure
    refine measureReal_mono fun ω hω ↦ ?_
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact hω.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) n.cast_nonneg)

end ProbabilityTheory
