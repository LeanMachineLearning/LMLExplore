/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Distributions.ExponentialFamily.Posterior.Basic
public import LMLExplore.Probability.Moments.MGF.Dominated

/-!
# Posterior odds against a mean below the truth

Let `ρ` be a measure on `𝓧` and `T : 𝓧 → ℝ` a statistic, with log-partition function
`ψ = cgf T ρ` and natural parameters `Θ`, the interior of `integrableExpSet T ρ`. After `s`
observations whose statistics sum to `S`, the posterior of the natural parameter for a prior `ν`
has density proportional to `exp (f(θ))` with respect to `ν` on `Θ`, where
`f(θ) = θ S - s ψ(θ)` (`Measure.expFamilyPosterior`). For a level `c`, the posterior odds
`P(ψ'(θ) ≤ c) / P(c < ψ'(θ))` are the ratio of the integrals of `exp (f(θ))` over the two sides of
the level.

This file bounds these odds when the observations come from a member `ρ_η` with mean `ψ'(η)`
above `c`, in expectation over the observations. In Thompson sampling, the inverse
`1 / G_s` of the probability `G_s` that the sampled mean of the optimal arm exceeds `c` is one
plus these odds, and [LS, Theorem 36.2] needs `E[∑_s (1 / G_s - 1)]` to be small.

* *Pointwise.* The exponent `f` is concave, so on an interval `[a, b]` of natural parameters it is
  at least `min (f(a), f(b))`, and the posterior mass of the means above `c` is at least
  `ν([a, b]) min (exp f(a), exp f(b))` when `c < ψ'(a)`. Hence the odds are at most
  `ν([a, b])⁻¹ ∫_{θ ∈ Θ, ψ'(θ) ≤ c} (exp (f(θ) - f(a)) + exp (f(θ) - f(b))) dν(θ)`.
* *In expectation.* For `θ ≤ e ≤ η`, the likelihood ratio `exp (f(θ) - f(e))` of `s` independent
  observations dominated on `Set.Iic 0` by `ρ_η` has expectation at most
  `exp (-s (η - e) (ψ'(e) - ψ'(θ + η - e)))`, by the Chernoff bound of the sum at `θ - e ≤ 0` and
  two tangent lines of `ψ`. For `θ ≤ η(c)` and `(η(c) + η) / 2 < e < η` the exponent is a negative
  multiple of `s`, uniformly in `θ`.

Together, the expected odds decay exponentially in `s` as soon as the prior mass `ν(ψ' ≤ c)` of
the low means is finite. This fails for the Jeffreys prior of exponential laws, which gives
infinite mass to every set of small means; there the expected odds are infinite.

## Main statements

* `MeasureTheory.Measure.inv_expFamilyPosterior_sub_one_le`: the pointwise bound on the posterior
  odds `(P(c < ψ'(θ)))⁻¹ - 1`.
* `ProbabilityTheory.iIndepFun.lintegral_exp_sub_le`: the bound on the expected likelihood ratio
  `E[exp (f(θ) - f(e))]` for observations dominated on `Set.Iic 0` by `ρ_η`.

## References

* [KKM13] N. Korda, E. Kaufmann and R. Munos, *Thompson sampling for 1-dimensional exponential
  family bandits*, NeurIPS 2013.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Theorem 36.2.
-/

public section

open MeasureTheory ProbabilityTheory Real Set LMLExplore

open scoped ENNReal

namespace MeasureTheory.Measure

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {ν : Measure ℝ}
  {s : ℕ} {S a b c : ℝ}

/-- **Posterior odds against a level of the mean.** Let `[a, b]` be an interval of natural
parameters of positive prior mass whose means exceed the level `c`. After `s` observations whose
statistics sum to `S`, if the posterior is proper, then the posterior odds
`(P(c < ψ'(θ)))⁻¹ - 1 = P(ψ'(θ) ≤ c) / P(c < ψ'(θ))` are at most
`ν([a, b])⁻¹ ∫_{θ ∈ Θ, ψ'(θ) ≤ c} (exp (f(θ) - f(a)) + exp (f(θ) - f(b))) dν(θ)`, with
`f(θ) = θ S - s ψ(θ)`. -/
theorem inv_expFamilyPosterior_sub_one_le (hΘ : Icc a b ⊆ interior (integrableExpSet T ρ))
    (hc : c < deriv (cgf T ρ) a) (hν : ν (Icc a b) ≠ 0) (h : ρ.expFamilyPosterior T ν s S ≠ 0) :
    (ρ.expFamilyPosterior T ν s S {θ | c < deriv (cgf T ρ) θ})⁻¹ - 1 ≤
      (ν (Icc a b))⁻¹ * ∫⁻ θ in interior (integrableExpSet T ρ) ∩ {θ | deriv (cgf T ρ) θ ≤ c},
        (ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ - (a * S - s * cgf T ρ a))) +
          ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ - (b * S - s * cgf T ρ b)))) ∂ν := by
  set Θ := interior (integrableExpSet T ρ)
  set E : ℝ → ℝ≥0∞ := fun θ ↦ ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ)) with hE
  set B := {θ | c < deriv (cgf T ρ) θ}
  set Lset := Θ ∩ {θ | deriv (cgf T ρ) θ ≤ c}
  have hB : MeasurableSet B := measurableSet_lt measurable_const (measurable_deriv _)
  set U := ∫⁻ θ in Θ ∩ B, E θ ∂ν
  set L := ∫⁻ θ in Lset, E θ ∂ν
  -- the normalizing constant splits along the level `c`
  have hZ : ∫⁻ θ in Θ, E θ ∂ν = U + L := by
    have hset : Θ \ B = Lset := by
      ext θ
      simp [B, Lset, not_lt]
    rw [← lintegral_inter_add_sdiff _ Θ hB, hset]
  rw [Ne, expFamilyPosterior_eq_zero_iff, not_or] at h
  obtain ⟨hZtop, hZ0⟩ := h
  -- on `[a, b]`, the exponent is at least its value at one of the endpoints
  have hmin (θ : ℝ) (hθ : θ ∈ Icc a b) : min (E a) (E b) ≤ E θ := by
    have ha := cgf_add_deriv_cgf_mul_sub_le_cgf (hΘ hθ)
      (interior_subset (hΘ ⟨le_rfl, hθ.1.trans hθ.2⟩))
    have hb := cgf_add_deriv_cgf_mul_sub_le_cgf (hΘ hθ)
      (interior_subset (hΘ ⟨hθ.1.trans hθ.2, le_rfl⟩))
    have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    rcases le_total (S - s * deriv (cgf T ρ) θ) 0 with hS | hS
    · refine min_le_of_right_le (ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_))
      nlinarith [mul_nonneg (sub_nonneg.2 hθ.2) (neg_nonneg.2 hS)]
    · refine min_le_of_left_le (ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_))
      nlinarith [mul_nonneg (sub_nonneg.2 hθ.1) hS]
  have hE0 (θ : ℝ) : E θ ≠ 0 := (ENNReal.ofReal_pos.2 (exp_pos _)).ne'
  have hm0 : min (E a) (E b) ≠ 0 := by
    rcases min_choice (E a) (E b) with h | h <;> rw [h] <;> exact hE0 _
  have hmtop : min (E a) (E b) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
  have hU : min (E a) (E b) * ν (Icc a b) ≤ U := by
    calc min (E a) (E b) * ν (Icc a b) = ∫⁻ _ in Icc a b, min (E a) (E b) ∂ν :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ θ in Icc a b, E θ ∂ν := setLIntegral_mono' measurableSet_Icc hmin
      _ ≤ U := lintegral_mono_set fun θ hθ ↦ ⟨hΘ hθ, hc.trans_le
          (monotoneOn_deriv_cgf (hΘ ⟨le_rfl, hθ.1.trans hθ.2⟩) (hΘ hθ) hθ.1)⟩
  have hU0 : U ≠ 0 := (lt_of_lt_of_le (ENNReal.mul_pos hm0 hν) hU).ne'
  have hUtop : U ≠ ∞ := ne_top_of_le_ne_top hZtop (hZ ▸ le_self_add)
  -- the odds are `L / U`
  have h_odds : (ρ.expFamilyPosterior T ν s S B)⁻¹ - 1 ≤ L * U⁻¹ := by
    rw [expFamilyPosterior_apply hB, ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hZtop))
      (Or.inl (ENNReal.inv_ne_top.2 hZ0)), inv_inv, hZ, add_mul,
      ENNReal.mul_inv_cancel hU0 hUtop, ENNReal.add_sub_cancel_left ENNReal.one_ne_top]
  -- and `1 / U ≤ (1 / E a + 1 / E b) / ν([a, b])`
  have h_inv : U⁻¹ ≤ ((E a)⁻¹ + (E b)⁻¹) * (ν (Icc a b))⁻¹ := by
    refine (ENNReal.inv_le_inv.2 hU).trans ?_
    rw [ENNReal.mul_inv (Or.inl hm0) (Or.inl hmtop)]
    gcongr
    rcases min_choice (E a) (E b) with h | h <;> rw [h]
    exacts [le_self_add, le_add_self]
  have h_int : ∫⁻ θ in Lset,
      (ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ - (a * S - s * cgf T ρ a))) +
        ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ - (b * S - s * cgf T ρ b)))) ∂ν =
      L * ((E a)⁻¹ + (E b)⁻¹) := by
    have hdiv (x y : ℝ) : ENNReal.ofReal (exp (x - y)) =
        ENNReal.ofReal (exp x) * (ENNReal.ofReal (exp y))⁻¹ := by
      rw [exp_sub, ENNReal.ofReal_div_of_pos (exp_pos _), div_eq_mul_inv]
    rw [← lintegral_mul_const' _ _ (by simp [hE0])]
    congr with θ
    rw [hdiv (θ * S - s * cgf T ρ θ), hdiv (θ * S - s * cgf T ρ θ), mul_add]
  rw [h_int]
  calc _ ≤ L * U⁻¹ := h_odds
    _ ≤ L * (((E a)⁻¹ + (E b)⁻¹) * (ν (Icc a b))⁻¹) := by gcongr
    _ = _ := by ring

end MeasureTheory.Measure

namespace ProbabilityTheory

variable {Ω ι 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {P : Measure Ω}
  {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {X : ι → Ω → ℝ} {s : Finset ι} {θ e η : ℝ}

/-- **Expected likelihood ratio of a smaller natural parameter.** Let `X i`, `i ∈ s`, be
independent and dominated on `Set.Iic 0` by the member `ρ_η` of natural parameter `η`, and let
`S = ∑ i ∈ s, X i`. For natural parameters `θ ≤ e ≤ η`, the likelihood ratio
`exp ((θ S - #s ψ(θ)) - (e S - #s ψ(e)))` of the members `ρ_θ` and `ρ_e` has expectation at most
`exp (-#s (η - e) (ψ'(e) - ψ'(θ + η - e)))`. -/
theorem iIndepFun.lintegral_exp_sub_le (h_indep : iIndepFun X P)
    (hX : ∀ i ∈ s, MGFDominatedOn (X i) P T (ρ.expFamily T η) (Iic 0))
    (hθ : θ ∈ interior (integrableExpSet T ρ)) (hη : η ∈ interior (integrableExpSet T ρ))
    (hθe : θ ≤ e) (heη : e ≤ η) :
    ∫⁻ ω, ENNReal.ofReal (exp (θ * ∑ i ∈ s, X i ω - s.card * cgf T ρ θ -
        (e * ∑ i ∈ s, X i ω - s.card * cgf T ρ e))) ∂P ≤
      ENNReal.ofReal (exp (-(s.card * ((η - e) *
        (deriv (cgf T ρ) e - deriv (cgf T ρ) (θ + η - e)))))) := by
  have := h_indep.isProbabilityMeasure
  set ψ := cgf T ρ
  set n : ℝ := (s.card : ℝ)
  have hΘ := (convex_integrableExpSet (X := T) (μ := ρ)).interior.ordConnected
  have he : e ∈ interior (integrableExpSet T ρ) := hΘ.out hθ hη ⟨hθe, heη⟩
  have hw : θ + η - e ∈ interior (integrableExpSet T ρ) :=
    hΘ.out hθ hη ⟨by linarith, by linarith⟩
  -- the Chernoff bound of the sum at `θ - e ≤ 0`
  have ht : θ - e ∈ Iic 0 := sub_nonpos.2 hθe
  have hY : Integrable (fun x ↦ exp ((θ - e) * T x)) (ρ.expFamily T η) := by
    rw [Measure.integrable_exp_mul_expFamily_iff (interior_subset hη),
      show η + (θ - e) = θ + η - e by ring]
    exact interior_subset hw
  have hint := h_indep.integrable_exp_mul_sum_of_mgfDominatedOn hX ht hY
  have hmgf := (h_indep.mgf_sum_le_pow_of_mgfDominatedOn hX ht hY).trans
    (pow_le_pow_left₀ mgf_nonneg Measure.mgf_expFamily_le_exp_cgf_sub s.card)
  rw [← exp_nat_mul, show η + (θ - e) = θ + η - e by ring] at hmgf
  -- two tangent lines of `ψ`, at `θ + η - e` and at `e`
  have h1 := Measure.cgf_add_deriv_cgf_mul_sub_le_cgf hw (interior_subset hθ)
  have h2 := Measure.cgf_add_deriv_cgf_mul_sub_le_cgf he (interior_subset hη)
  have h_exp : n * (ψ (θ + η - e) - ψ η) + -(n * (ψ θ - ψ e)) ≤
      -(n * ((η - e) * (deriv ψ e - deriv ψ (θ + η - e)))) := by
    have hn : 0 ≤ n := Nat.cast_nonneg _
    nlinarith
  calc ∫⁻ ω, ENNReal.ofReal (exp (θ * ∑ i ∈ s, X i ω - n * ψ θ - (e * ∑ i ∈ s, X i ω - n * ψ e)))
        ∂P
      = ∫⁻ ω, ENNReal.ofReal (exp ((θ - e) * ∑ i ∈ s, X i ω)) *
          ENNReal.ofReal (exp (-(n * (ψ θ - ψ e)))) ∂P := by
        congr with ω
        rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
        ring_nf
    _ = ENNReal.ofReal (mgf (fun ω ↦ ∑ i ∈ s, X i ω) P (θ - e)) *
          ENNReal.ofReal (exp (-(n * (ψ θ - ψ e)))) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mgf,
          ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ (exp_pos _).le)]
    _ ≤ ENNReal.ofReal (exp (n * (ψ (θ + η - e) - ψ η))) *
          ENNReal.ofReal (exp (-(n * (ψ θ - ψ e)))) := by
        gcongr
    _ ≤ _ := by
        rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
        exact ENNReal.ofReal_le_ofReal (exp_le_exp.2 h_exp)

end ProbabilityTheory
