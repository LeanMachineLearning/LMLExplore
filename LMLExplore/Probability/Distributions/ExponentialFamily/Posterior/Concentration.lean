/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Distributions.ExponentialFamily.Mean
public import LMLExplore.Probability.Distributions.ExponentialFamily.Posterior.Basic

/-!
# Concentration of the posteriors of an exponential family

Let `ρ` be a measure on `𝓧` and `T : 𝓧 → ℝ` a statistic which is not `ρ`-almost everywhere
constant, with log-partition function `ψ = cgf T ρ`, natural parameters `Θ` (the interior of
`integrableExpSet T ρ`), mean map `ψ'` and set of means `M`. After `s` observations whose
statistics sum to `S`, the posterior of the natural parameter for a prior `ν` is the probability
measure proportional to `exp (θ S - s ψ(θ)) ν(dθ)` on `Θ` (`Measure.expFamilyPosterior`). This
file proves that it concentrates around the natural parameter `θ₀ = η(μ₀)` of a mean `μ₀ ∈ M`
when the empirical mean `S / s` is close to `μ₀`: this is the posterior concentration theorem of
Thompson sampling for exponential families [KKM13, Theorem 4].

Relative to `θ₀`, the exponent is
`θ S - s ψ(θ) - (θ₀ S - s ψ(θ₀)) = -s K(θ₀, θ) + (θ - θ₀) (S - s μ₀)`, where
`K(θ₀, θ) = ψ(θ) - ψ(θ₀) - μ₀ (θ - θ₀)` is the Kullback–Leibler divergence from the member of
natural parameter `θ₀` to the member of natural parameter `θ` [KKM13, (14)–(15)]. Let
`|S - s μ₀| ≤ s δ`.

* *Denominator.* On an interval `[θ₀ - r, θ₀ + r] ⊆ Θ` on which `|ψ' - μ₀| ≤ D`, convexity of
  `ψ` gives `K(θ₀, θ) ≤ (θ - θ₀) (ψ'(θ) - μ₀)`, so the exponent is at least `-s r (δ + D)`, and the
  normalizing constant is at least `exp (-s r (δ + D)) ν([θ₀ - r, θ₀ + r])`. With `r = 1 / s`
  this costs only a constant factor, and for the Jeffreys prior `√ψ''(θ) dθ` the prior mass of the
  interval is of order `1 / s` [KKM13, (12)–(13)].
* *Numerator.* For a mean `m ≥ μ₀ + δ`, every natural parameter `θ` with `ψ'(θ) ≥ m` is at least
  `η(m)`, and the tangent line of `ψ` at `η(m)` gives
  `K(θ₀, θ) - δ (θ - θ₀) ≥ d(μ₀, m) - δ (η(m) - η(μ₀))`, with `d` the divergence of the family in
  the mean parametrization [KKM13, (11)]. All but `s₀` of the `s` observations contribute this
  exponent, and the remaining `s₀` give the normalizing constant of the posterior after `s₀`
  observations whose statistics sum to `s₀ (μ₀ + δ)`, which is finite for a proper posterior.

Together, the posterior of `{θ | m ≤ ψ'(θ)}` decays like
`exp (-s (d(μ₀, m) - δ (η(m) - η(μ₀))))`, times a factor `s` for the Jeffreys prior. The lower
tail `{θ | ψ'(θ) ≤ m}` for a mean `m ≤ μ₀ - δ` is symmetric. In Thompson sampling, the sampled
mean of an arm is `ψ'(θ)` for a natural parameter `θ` drawn from its posterior: the upper tail
bounds the probability that a suboptimal arm looks better than the best mean, and the lower tail
the probability that the best arm looks worse than a suboptimal mean, once their empirical means
are accurate.

The factor `1 - δ C₂` of [KKM13, Theorem 4], with `C₂ = (η(m) - η(μ₀)) / d(μ₀, m)`, appears here as
`d(μ₀, m) - δ (η(m) - η(μ₀)) = (1 - δ C₂) d(μ₀, m)`. Instead of the posterior after one
well-chosen observation, a probability measure in [KKM13], the bounds use the normalizing constant
of the posterior after `s₀` observations at the boundary `μ₀ ± δ` of the accuracy event; `s₀ = 0`
is a proper prior.

## Main statements

* `MeasureTheory.Measure.ofReal_exp_mul_measure_Icc_le_lintegral`: the lower bound on the
  normalizing constant relative to `θ₀`.
* `MeasureTheory.Measure.expFamilyPosterior_le_of_forall_sub_le`: the posterior of a set on which
  the exponent relative to `θ₀` is at most `A + θ S₀ - s₀ ψ(θ)` is at most
  `exp (s r (δ + D) + A) Z(s₀, S₀) / ν([θ₀ - r, θ₀ + r])`, with `Z(s₀, S₀)` the normalizing
  constant after `s₀` observations whose statistics sum to `S₀`.
* `MeasureTheory.Measure.expFamilyPosterior_setOf_le_deriv_cgf_le`,
  `MeasureTheory.Measure.expFamilyPosterior_setOf_deriv_cgf_le_le`: the bounds on the upper and
  lower tails of the posterior mean `ψ'(θ)`, for every prior.
* `MeasureTheory.Measure.exists_expFamilyPosterior_jeffreysPrior_setOf_le_deriv_cgf_le`,
  `MeasureTheory.Measure.exists_expFamilyPosterior_jeffreysPrior_setOf_deriv_cgf_le_le`:
  **posterior concentration** [KKM13, Theorem 4]: for the Jeffreys prior, there are `C` and `N`
  such that for `s ≥ N` and `|S - s μ₀| ≤ s δ`, the posterior of the upper tail is at most
  `C s exp (-s (d(μ₀, m) - δ (η(m) - η(μ₀))))`, and similarly for the lower tail.

## References

* [KKM13] N. Korda, E. Kaufmann and R. Munos, *Thompson sampling for 1-dimensional exponential
  family bandits*, NeurIPS 2013, Section 4.
-/

public section

open ProbabilityTheory Real Set Filter Topology

open scoped ENNReal

namespace MeasureTheory.Measure

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {ν : Measure ℝ}
  {s s₀ : ℕ} {S S₀ μ₀ m δ r D A : ℝ}

/-- **Lower bound on the normalizing constant.** Let `θ₀ = η(μ₀)` be the natural parameter of a
mean `μ₀`, and let `[θ₀ - r, θ₀ + r]` be an interval of natural parameters on which the mean map
stays within `D` of `μ₀`. After `s` observations whose statistics sum to `S` with
`|S - s μ₀| ≤ s δ`, the exponent relative to `θ₀` is at least `-s r (δ + D)` on that interval, so
the normalizing constant of the posterior relative to `θ₀` is at least
`exp (-s r (δ + D)) ν([θ₀ - r, θ₀ + r])` [KKM13, (12)]. -/
lemma ofReal_exp_mul_measure_Icc_le_lintegral (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T) (hr : 0 ≤ r)
    (hΘ : Icc (ρ.natParam T μ₀ - r) (ρ.natParam T μ₀ + r) ⊆ interior (integrableExpSet T ρ))
    (hD : ∀ θ ∈ Icc (ρ.natParam T μ₀ - r) (ρ.natParam T μ₀ + r),
      |deriv (cgf T ρ) θ - μ₀| ≤ D)
    (hS : |S - s * μ₀| ≤ s * δ) :
    ENNReal.ofReal (exp (-(s * r * (δ + D)))) *
        ν (Icc (ρ.natParam T μ₀ - r) (ρ.natParam T μ₀ + r)) ≤
      ∫⁻ θ in interior (integrableExpSet T ρ), ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ -
        (ρ.natParam T μ₀ * S - s * cgf T ρ (ρ.natParam T μ₀)))) ∂ν := by
  set θ₀ := ρ.natParam T μ₀
  have hθ₀ : θ₀ ∈ integrableExpSet T ρ :=
    interior_subset (natParam_mem_interior_integrableExpSet hμ₀)
  calc ENNReal.ofReal (exp (-(s * r * (δ + D)))) * ν (Icc (θ₀ - r) (θ₀ + r))
      = ∫⁻ _ in Icc (θ₀ - r) (θ₀ + r), ENNReal.ofReal (exp (-(s * r * (δ + D)))) ∂ν :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ θ in Icc (θ₀ - r) (θ₀ + r), ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ -
          (θ₀ * S - s * cgf T ρ θ₀))) ∂ν := by
        refine setLIntegral_mono' measurableSet_Icc fun θ hθ ↦
          ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_)
        -- the tangent line of `ψ` at `θ` lies below `ψ(θ₀)`
        have h_tan := toReal_klDiv_expFamily (hΘ hθ) hθ₀
        have h_abs : |θ - θ₀| ≤ r := abs_sub_le_iff.2 ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
        have h1 : |(θ - θ₀) * (S - s * μ₀)| ≤ r * (s * δ) := by
          rw [abs_mul]
          exact mul_le_mul h_abs hS (abs_nonneg _) hr
        have h2 : |(θ - θ₀) * (deriv (cgf T ρ) θ - μ₀)| ≤ r * D := by
          rw [abs_mul]
          exact mul_le_mul h_abs (hD θ hθ) (abs_nonneg _) hr
        have h3 : (s : ℝ) * (cgf T ρ θ - cgf T ρ θ₀) ≤ s * (deriv (cgf T ρ) θ * (θ - θ₀)) :=
          mul_le_mul_of_nonneg_left (by linarith [ENNReal.toReal_nonneg.trans_eq h_tan])
            (Nat.cast_nonneg s)
        have h4 : (s : ℝ) * ((θ - θ₀) * (deriv (cgf T ρ) θ - μ₀)) ≤ s * (r * D) :=
          mul_le_mul_of_nonneg_left (le_of_abs_le h2) (Nat.cast_nonneg s)
        linarith [neg_abs_le ((θ - θ₀) * (S - s * μ₀))]
    _ ≤ _ := lintegral_mono_set hΘ

/-- **Posterior bound through a pointwise bound on the exponent.** Let `θ₀ = η(μ₀)` be the natural
parameter of a mean `μ₀`, let `[θ₀ - r, θ₀ + r]` be an interval of natural parameters on which
the mean map stays within `D` of `μ₀`, and let `|S - s μ₀| ≤ s δ`. If on the natural parameters
of a measurable set `B` the exponent relative to `θ₀` is at most `A + θ S₀ - s₀ ψ(θ)`, then the
posterior of `B` after `s` observations whose statistics sum to `S` is at most
`exp (s r (δ + D) + A) Z(s₀, S₀) / ν([θ₀ - r, θ₀ + r])`, with
`Z(s₀, S₀) = ∫_Θ exp (θ S₀ - s₀ ψ(θ)) dν(θ)` the normalizing constant of the posterior after
`s₀` observations whose statistics sum to `S₀`. -/
theorem expFamilyPosterior_le_of_forall_sub_le (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T) (hr : 0 ≤ r)
    (hΘ : Icc (ρ.natParam T μ₀ - r) (ρ.natParam T μ₀ + r) ⊆ interior (integrableExpSet T ρ))
    (hD : ∀ θ ∈ Icc (ρ.natParam T μ₀ - r) (ρ.natParam T μ₀ + r),
      |deriv (cgf T ρ) θ - μ₀| ≤ D)
    (hS : |S - s * μ₀| ≤ s * δ) {B : Set ℝ} (hB : MeasurableSet B)
    (hA : ∀ θ ∈ interior (integrableExpSet T ρ) ∩ B,
      θ * S - s * cgf T ρ θ - (ρ.natParam T μ₀ * S - s * cgf T ρ (ρ.natParam T μ₀)) ≤
        A + (θ * S₀ - s₀ * cgf T ρ θ)) :
    ρ.expFamilyPosterior T ν s S B ≤
      ENNReal.ofReal (exp (s * r * (δ + D) + A)) *
          (∫⁻ θ in interior (integrableExpSet T ρ),
            ENNReal.ofReal (exp (θ * S₀ - s₀ * cgf T ρ θ)) ∂ν) /
        ν (Icc (ρ.natParam T μ₀ - r) (ρ.natParam T μ₀ + r)) := by
  set θ₀ := ρ.natParam T μ₀
  set Θ := interior (integrableExpSet T ρ)
  set L := s * r * (δ + D)
  have hL0 : ENNReal.ofReal (exp (-L)) ≠ 0 := (ENNReal.ofReal_pos.2 (exp_pos _)).ne'
  -- the numerator, bounded through the pointwise bound on the exponent
  have h_num : ∫⁻ θ in Θ ∩ B, ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ -
        (θ₀ * S - s * cgf T ρ θ₀))) ∂ν ≤
      ENNReal.ofReal (exp A) *
        ∫⁻ θ in Θ, ENNReal.ofReal (exp (θ * S₀ - s₀ * cgf T ρ θ)) ∂ν := by
    calc _ ≤ ∫⁻ θ in Θ ∩ B, ENNReal.ofReal (exp A) *
          ENNReal.ofReal (exp (θ * S₀ - s₀ * cgf T ρ θ)) ∂ν := by
          refine setLIntegral_mono' (isOpen_interior.measurableSet.inter hB) fun θ hθ ↦ ?_
          rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
          exact ENNReal.ofReal_le_ofReal (exp_le_exp.2 (hA θ hθ))
      _ = ENNReal.ofReal (exp A) * ∫⁻ θ in Θ ∩ B,
          ENNReal.ofReal (exp (θ * S₀ - s₀ * cgf T ρ θ)) ∂ν :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr; exact inter_subset_left
  have h_inv : (ENNReal.ofReal (exp (-L)))⁻¹ * ENNReal.ofReal (exp A) =
      ENNReal.ofReal (exp (L + A)) := by
    rw [← ENNReal.ofReal_inv_of_pos (exp_pos _), ← ENNReal.ofReal_mul (inv_pos.2 (exp_pos _)).le,
      ← exp_neg, neg_neg, ← exp_add]
  calc ρ.expFamilyPosterior T ν s S B
      = (∫⁻ θ in Θ, ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ -
            (θ₀ * S - s * cgf T ρ θ₀))) ∂ν)⁻¹ *
          ∫⁻ θ in Θ ∩ B, ENNReal.ofReal (exp (θ * S - s * cgf T ρ θ -
            (θ₀ * S - s * cgf T ρ θ₀))) ∂ν :=
        expFamilyPosterior_apply_sub_const _ hB
    _ ≤ (ENNReal.ofReal (exp (-L)) * ν (Icc (θ₀ - r) (θ₀ + r)))⁻¹ *
        (ENNReal.ofReal (exp A) *
          ∫⁻ θ in Θ, ENNReal.ofReal (exp (θ * S₀ - s₀ * cgf T ρ θ)) ∂ν) :=
        mul_le_mul' (ENNReal.inv_le_inv.2
          (ofReal_exp_mul_measure_Icc_le_lintegral hμ₀ hr hΘ hD hS)) h_num
    _ = _ := by
      rw [ENNReal.mul_inv (Or.inl hL0) (Or.inl ENNReal.ofReal_ne_top), ENNReal.div_eq_inv_mul,
        ← h_inv]
      ring

/-! ### The two tails of the posterior mean -/

/-- On the upper tail `{θ ∈ Θ | m ≤ ψ'(θ)}` of the mean map, for a mean `m ≥ μ₀ + δ` and a sum of
statistics `S ≤ s (μ₀ + δ)`, the exponent relative to `θ₀ = η(μ₀)` is at most
`-(s - s₀) β + (θ S₀ - s₀ ψ(θ)) - (θ₀ S₀ - s₀ ψ(θ₀))`, with `S₀ = s₀ (μ₀ + δ)` and
`β = d(μ₀, m) - δ (η(m) - η(μ₀))`. -/
private lemma sub_le_of_le_deriv_cgf (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T) (hm : m ∈ ρ.expFamilyMeans T) (hδ : 0 ≤ δ)
    (hδm : δ ≤ m - μ₀) (hs₀ : s₀ ≤ s) (hS : S ≤ s * (μ₀ + δ)) {θ : ℝ}
    (hθ : θ ∈ interior (integrableExpSet T ρ)) (hθm : m ≤ deriv (cgf T ρ) θ) :
    θ * S - s * cgf T ρ θ - (ρ.natParam T μ₀ * S - s * cgf T ρ (ρ.natParam T μ₀)) ≤
      -((s - s₀ : ℝ) * (ρ.expFamilyDiv T μ₀ m - δ * (ρ.natParam T m - ρ.natParam T μ₀))) -
          (ρ.natParam T μ₀ * (s₀ * (μ₀ + δ)) - s₀ * cgf T ρ (ρ.natParam T μ₀)) +
        (θ * (s₀ * (μ₀ + δ)) - s₀ * cgf T ρ θ) := by
  set θ₀ := ρ.natParam T μ₀
  set θm := ρ.natParam T m
  have hθm_le : θm ≤ θ :=
    natParam_deriv_cgf hT hθ ▸ monotoneOn_natParam hm (deriv_cgf_mem_expFamilyMeans hθ) hθm
  have hθ₀m : θ₀ ≤ θm := monotoneOn_natParam hμ₀ hm (by linarith)
  -- the tangent line of `ψ` at `η(m)`
  have h_tan := cgf_natParam_add_mul_sub_le_cgf hm (interior_subset hθ)
  have h_beta : ρ.expFamilyDiv T μ₀ m - δ * (θm - θ₀) ≤
      cgf T ρ θ - cgf T ρ θ₀ - (μ₀ + δ) * (θ - θ₀) := by
    rw [expFamilyDiv_def]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m - μ₀ - δ) (sub_nonneg.2 hθm_le)]
  have h1 : (θ - θ₀) * S ≤ (θ - θ₀) * (s * (μ₀ + δ)) :=
    mul_le_mul_of_nonneg_left hS (by linarith)
  have h2 := mul_le_mul_of_nonneg_left h_beta (sub_nonneg.2 (Nat.cast_le.2 hs₀) : (0 : ℝ) ≤ s - s₀)
  linarith

/-- On the lower tail `{θ ∈ Θ | ψ'(θ) ≤ m}` of the mean map, for a mean `m ≤ μ₀ - δ` and a sum of
statistics `S ≥ s (μ₀ - δ)`, the exponent relative to `θ₀ = η(μ₀)` is at most
`-(s - s₀) β + (θ S₀ - s₀ ψ(θ)) - (θ₀ S₀ - s₀ ψ(θ₀))`, with `S₀ = s₀ (μ₀ - δ)` and
`β = d(μ₀, m) - δ (η(μ₀) - η(m))`. -/
private lemma sub_le_of_deriv_cgf_le (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T) (hm : m ∈ ρ.expFamilyMeans T) (hδ : 0 ≤ δ)
    (hδm : δ ≤ μ₀ - m) (hs₀ : s₀ ≤ s) (hS : s * (μ₀ - δ) ≤ S) {θ : ℝ}
    (hθ : θ ∈ interior (integrableExpSet T ρ)) (hθm : deriv (cgf T ρ) θ ≤ m) :
    θ * S - s * cgf T ρ θ - (ρ.natParam T μ₀ * S - s * cgf T ρ (ρ.natParam T μ₀)) ≤
      -((s - s₀ : ℝ) * (ρ.expFamilyDiv T μ₀ m - δ * (ρ.natParam T μ₀ - ρ.natParam T m))) -
          (ρ.natParam T μ₀ * (s₀ * (μ₀ - δ)) - s₀ * cgf T ρ (ρ.natParam T μ₀)) +
        (θ * (s₀ * (μ₀ - δ)) - s₀ * cgf T ρ θ) := by
  set θ₀ := ρ.natParam T μ₀
  set θm := ρ.natParam T m
  have hθ_le : θ ≤ θm :=
    natParam_deriv_cgf hT hθ ▸ monotoneOn_natParam (deriv_cgf_mem_expFamilyMeans hθ) hm hθm
  have hθm₀ : θm ≤ θ₀ := monotoneOn_natParam hm hμ₀ (by linarith)
  -- the tangent line of `ψ` at `η(m)`
  have h_tan := cgf_natParam_add_mul_sub_le_cgf hm (interior_subset hθ)
  have h_beta : ρ.expFamilyDiv T μ₀ m - δ * (θ₀ - θm) ≤
      cgf T ρ θ - cgf T ρ θ₀ - (μ₀ - δ) * (θ - θ₀) := by
    rw [expFamilyDiv_def]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ μ₀ - δ - m) (sub_nonneg.2 hθ_le)]
  have h1 : (θ - θ₀) * S ≤ (θ - θ₀) * (s * (μ₀ - δ)) :=
    mul_le_mul_of_nonpos_left hS (by linarith)
  have h2 := mul_le_mul_of_nonneg_left h_beta (sub_nonneg.2 (Nat.cast_le.2 hs₀) : (0 : ℝ) ≤ s - s₀)
  linarith

/-- **Upper tail of the posterior mean.** Let `μ₀` and `m` be means of the family with
`0 ≤ δ ≤ m - μ₀`, let `[θ₀ - r, θ₀ + r]` around `θ₀ = η(μ₀)` be an interval of natural parameters
on which the mean map stays within `D` of `μ₀`, and let `s₀ ≤ s`. After `s` observations whose
statistics sum to `S` with `|S - s μ₀| ≤ s δ`, the posterior probability that the mean `ψ'(θ)` is
at least `m` is at most
`exp (s r (δ + D) - (s - s₀) β - (θ₀ S₀ - s₀ ψ(θ₀))) Z(s₀, S₀) / ν([θ₀ - r, θ₀ + r])`, with
`β = d(μ₀, m) - δ (η(m) - η(μ₀))`, `S₀ = s₀ (μ₀ + δ)` and
`Z(s₀, S₀) = ∫_Θ exp (θ S₀ - s₀ ψ(θ)) dν(θ)` [KKM13, Lemma 7 and (11)–(12)]. -/
theorem expFamilyPosterior_setOf_le_deriv_cgf_le (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T) (hm : m ∈ ρ.expFamilyMeans T) (hδ : 0 ≤ δ)
    (hδm : δ ≤ m - μ₀) (hs₀ : s₀ ≤ s) (hr : 0 ≤ r)
    (hΘ : Icc (ρ.natParam T μ₀ - r) (ρ.natParam T μ₀ + r) ⊆ interior (integrableExpSet T ρ))
    (hD : ∀ θ ∈ Icc (ρ.natParam T μ₀ - r) (ρ.natParam T μ₀ + r),
      |deriv (cgf T ρ) θ - μ₀| ≤ D)
    (hS : |S - s * μ₀| ≤ s * δ) :
    ρ.expFamilyPosterior T ν s S {θ | m ≤ deriv (cgf T ρ) θ} ≤
      ENNReal.ofReal (exp (s * r * (δ + D) -
          (s - s₀ : ℝ) * (ρ.expFamilyDiv T μ₀ m - δ * (ρ.natParam T m - ρ.natParam T μ₀)) -
          (ρ.natParam T μ₀ * (s₀ * (μ₀ + δ)) - s₀ * cgf T ρ (ρ.natParam T μ₀)))) *
          (∫⁻ θ in interior (integrableExpSet T ρ),
            ENNReal.ofReal (exp (θ * (s₀ * (μ₀ + δ)) - s₀ * cgf T ρ θ)) ∂ν) /
        ν (Icc (ρ.natParam T μ₀ - r) (ρ.natParam T μ₀ + r)) := by
  have hS' : S ≤ s * (μ₀ + δ) := by linarith [le_of_abs_le hS]
  convert expFamilyPosterior_le_of_forall_sub_le hμ₀ hr hΘ hD hS
    (B := {θ | m ≤ deriv (cgf T ρ) θ}) (measurableSet_le measurable_const (measurable_deriv _))
    (fun θ hθ ↦ sub_le_of_le_deriv_cgf hT hμ₀ hm hδ hδm hs₀ hS' hθ.1 hθ.2) using 4
  congr 1
  ring

/-- **Lower tail of the posterior mean.** Let `μ₀` and `m` be means of the family with
`0 ≤ δ ≤ μ₀ - m`, let `[θ₀ - r, θ₀ + r]` around `θ₀ = η(μ₀)` be an interval of natural parameters
on which the mean map stays within `D` of `μ₀`, and let `s₀ ≤ s`. After `s` observations whose
statistics sum to `S` with `|S - s μ₀| ≤ s δ`, the posterior probability that the mean `ψ'(θ)` is
at most `m` is at most
`exp (s r (δ + D) - (s - s₀) β - (θ₀ S₀ - s₀ ψ(θ₀))) Z(s₀, S₀) / ν([θ₀ - r, θ₀ + r])`, with
`β = d(μ₀, m) - δ (η(μ₀) - η(m))`, `S₀ = s₀ (μ₀ - δ)` and
`Z(s₀, S₀) = ∫_Θ exp (θ S₀ - s₀ ψ(θ)) dν(θ)`. -/
theorem expFamilyPosterior_setOf_deriv_cgf_le_le (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T) (hm : m ∈ ρ.expFamilyMeans T) (hδ : 0 ≤ δ)
    (hδm : δ ≤ μ₀ - m) (hs₀ : s₀ ≤ s) (hr : 0 ≤ r)
    (hΘ : Icc (ρ.natParam T μ₀ - r) (ρ.natParam T μ₀ + r) ⊆ interior (integrableExpSet T ρ))
    (hD : ∀ θ ∈ Icc (ρ.natParam T μ₀ - r) (ρ.natParam T μ₀ + r),
      |deriv (cgf T ρ) θ - μ₀| ≤ D)
    (hS : |S - s * μ₀| ≤ s * δ) :
    ρ.expFamilyPosterior T ν s S {θ | deriv (cgf T ρ) θ ≤ m} ≤
      ENNReal.ofReal (exp (s * r * (δ + D) -
          (s - s₀ : ℝ) * (ρ.expFamilyDiv T μ₀ m - δ * (ρ.natParam T μ₀ - ρ.natParam T m)) -
          (ρ.natParam T μ₀ * (s₀ * (μ₀ - δ)) - s₀ * cgf T ρ (ρ.natParam T μ₀)))) *
          (∫⁻ θ in interior (integrableExpSet T ρ),
            ENNReal.ofReal (exp (θ * (s₀ * (μ₀ - δ)) - s₀ * cgf T ρ θ)) ∂ν) /
        ν (Icc (ρ.natParam T μ₀ - r) (ρ.natParam T μ₀ + r)) := by
  have hS' : s * (μ₀ - δ) ≤ S := by linarith [neg_abs_le (S - s * μ₀)]
  convert expFamilyPosterior_le_of_forall_sub_le hμ₀ hr hΘ hD hS
    (B := {θ | deriv (cgf T ρ) θ ≤ m}) (measurableSet_le (measurable_deriv _) measurable_const)
    (fun θ hθ ↦ sub_le_of_deriv_cgf_le hT hμ₀ hm hδ hδm hs₀ hS' hθ.1 hθ.2) using 4
  congr 1
  ring

/-! ### Posterior concentration for the Jeffreys prior -/

/-- Around the natural parameter `θ₀ = η(μ₀)` of a mean `μ₀`, there is an interval
`[θ₀ - r₀, θ₀ + r₀]` of natural parameters on which the mean map stays within some `D` of `μ₀`
and `√ψ''` is at least some `c > 0`. -/
private lemma exists_Icc_natParam (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T) :
    ∃ r₀ > 0, ∃ c > 0, ∃ D,
      Icc (ρ.natParam T μ₀ - r₀) (ρ.natParam T μ₀ + r₀) ⊆ interior (integrableExpSet T ρ) ∧
      (∀ θ ∈ Icc (ρ.natParam T μ₀ - r₀) (ρ.natParam T μ₀ + r₀), |deriv (cgf T ρ) θ - μ₀| ≤ D) ∧
      ∀ θ ∈ Icc (ρ.natParam T μ₀ - r₀) (ρ.natParam T μ₀ + r₀),
        c ≤ √(iteratedDeriv 2 (cgf T ρ) θ) := by
  set θ₀ := ρ.natParam T μ₀
  have hθ₀ := natParam_mem_interior_integrableExpSet hμ₀
  have hpos := iteratedDeriv_two_cgf_pos hT hθ₀
  -- `ψ''` is continuous and positive at `θ₀`, and `Θ` is open
  have hcont : ContinuousAt (iteratedDeriv 2 (cgf T ρ)) θ₀ := by
    rw [iteratedDeriv_eq_iterate]
    exact ((analyticAt_cgf hθ₀).iterated_deriv 2).continuousAt
  have h_ev : ∀ᶠ θ in 𝓝 θ₀, θ ∈ interior (integrableExpSet T ρ) ∧
      iteratedDeriv 2 (cgf T ρ) θ₀ / 2 < iteratedDeriv 2 (cgf T ρ) θ :=
    (isOpen_interior.eventually_mem hθ₀).and <|
      continuousAt_const.eventually_lt hcont (half_lt_self hpos)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 h_ev
  have hIcc : Icc (θ₀ - ε / 2) (θ₀ + ε / 2) ⊆ Metric.ball θ₀ ε := fun θ hθ ↦ by
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [hθ.1, hθ.2]
  have hΘ : Icc (θ₀ - ε / 2) (θ₀ + ε / 2) ⊆ interior (integrableExpSet T ρ) :=
    fun θ hθ ↦ (hball θ (hIcc hθ)).1
  refine ⟨ε / 2, by positivity, √(iteratedDeriv 2 (cgf T ρ) θ₀ / 2), by positivity,
    deriv (cgf T ρ) (θ₀ + ε / 2) - deriv (cgf T ρ) (θ₀ - ε / 2), hΘ, fun θ hθ ↦ ?_,
    fun θ hθ ↦ Real.sqrt_le_sqrt (hball θ (hIcc hθ)).2.le⟩
  -- the mean map is monotone, and `ψ'(θ₀) = μ₀`
  have h_lo : θ₀ - ε / 2 ∈ Icc (θ₀ - ε / 2) (θ₀ + ε / 2) := ⟨le_rfl, by linarith⟩
  have h_hi : θ₀ + ε / 2 ∈ Icc (θ₀ - ε / 2) (θ₀ + ε / 2) := ⟨by linarith, le_rfl⟩
  have h₀ : θ₀ ∈ Icc (θ₀ - ε / 2) (θ₀ + ε / 2) := ⟨by linarith, by linarith⟩
  have h1 := monotoneOn_deriv_cgf (hΘ h_lo) (hΘ hθ) hθ.1
  have h2 := monotoneOn_deriv_cgf (hΘ hθ) (hΘ h_hi) hθ.2
  have h3 := monotoneOn_deriv_cgf (hΘ h_lo) (hΘ h₀) h₀.1
  have h4 := monotoneOn_deriv_cgf (hΘ h₀) (hΘ h_hi) h₀.2
  rw [deriv_cgf_natParam hμ₀] at h3 h4
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- From bounds of the form of `expFamilyPosterior_setOf_le_deriv_cgf_le` for every interval
`[θ₀ - r, θ₀ + r]` of natural parameters, the bound `C s exp (-s β)` for the Jeffreys prior,
with `r = 1 / s`. -/
private lemma exists_expFamilyPosterior_jeffreysPrior_le (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T) {B : Set ℝ} {β : ℝ} (s₀ : ℕ)
    (hZ : ∫⁻ θ in interior (integrableExpSet T ρ),
      ENNReal.ofReal (exp (θ * S₀ - s₀ * cgf T ρ θ)) ∂(ρ.jeffreysPrior T) ≠ ∞)
    (h : ∀ s : ℕ, s₀ ≤ s → ∀ S, |S - s * μ₀| ≤ s * δ → ∀ r D, 0 ≤ r →
      Icc (ρ.natParam T μ₀ - r) (ρ.natParam T μ₀ + r) ⊆ interior (integrableExpSet T ρ) →
      (∀ θ ∈ Icc (ρ.natParam T μ₀ - r) (ρ.natParam T μ₀ + r), |deriv (cgf T ρ) θ - μ₀| ≤ D) →
      ρ.expFamilyPosterior T (ρ.jeffreysPrior T) s S B ≤
        ENNReal.ofReal (exp (s * r * (δ + D) - (s - s₀ : ℝ) * β -
            (ρ.natParam T μ₀ * S₀ - s₀ * cgf T ρ (ρ.natParam T μ₀)))) *
            (∫⁻ θ in interior (integrableExpSet T ρ),
              ENNReal.ofReal (exp (θ * S₀ - s₀ * cgf T ρ θ)) ∂(ρ.jeffreysPrior T)) /
          ρ.jeffreysPrior T (Icc (ρ.natParam T μ₀ - r) (ρ.natParam T μ₀ + r))) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ s ≥ N, ∀ S, |S - s * μ₀| ≤ s * δ →
      ρ.expFamilyPosterior T (ρ.jeffreysPrior T) s S B ≤
        ENNReal.ofReal (C * s * exp (-(s * β))) := by
  set θ₀ := ρ.natParam T μ₀
  set Z := ∫⁻ θ in interior (integrableExpSet T ρ),
    ENNReal.ofReal (exp (θ * S₀ - s₀ * cgf T ρ θ)) ∂(ρ.jeffreysPrior T)
  obtain ⟨r₀, hr₀, c, hc, D, hΘ, hD, hψ⟩ := exists_Icc_natParam hT hμ₀
  set K := exp (δ + D + s₀ * β - (θ₀ * S₀ - s₀ * cgf T ρ θ₀))
  refine ⟨K * Z.toReal / (2 * c), max s₀ (max 1 ⌈r₀⁻¹⌉₊), fun s hs S hS ↦ ?_⟩
  have hs₀ : s₀ ≤ s := (le_max_left _ _).trans hs
  have hs1 : 1 ≤ s := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
  have hspos : (0 : ℝ) < s := Nat.cast_pos.2 hs1
  -- the interval of half-width `1 / s` lies in `[θ₀ - r₀, θ₀ + r₀]`
  have hr : (s : ℝ)⁻¹ ≤ r₀ := inv_le_of_inv_le₀ hr₀ ((Nat.le_ceil _).trans
    (Nat.cast_le.2 ((le_max_right _ _).trans ((le_max_right _ _).trans hs))))
  have hsub : Icc (θ₀ - (s : ℝ)⁻¹) (θ₀ + (s : ℝ)⁻¹) ⊆ Icc (θ₀ - r₀) (θ₀ + r₀) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hle := h s hs₀ S hS (s : ℝ)⁻¹ D (inv_nonneg.2 hspos.le)
    (hsub.trans hΘ) fun θ hθ ↦ hD θ (hsub hθ)
  have hmass := ofReal_mul_le_jeffreysPrior_Icc hc.le (hsub.trans hΘ) fun θ hθ ↦ hψ θ (hsub hθ)
  have hcs : 0 < c * (θ₀ + (s : ℝ)⁻¹ - (θ₀ - (s : ℝ)⁻¹)) := by
    have : 0 < (s : ℝ)⁻¹ := inv_pos.2 hspos
    nlinarith
  refine hle.trans ((ENNReal.div_le_div_left hmass _).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_toReal hZ, ← ENNReal.ofReal_mul (exp_pos _).le,
    ← ENNReal.ofReal_div_of_pos hcs]
  congr 1
  have hK : exp (s * (s : ℝ)⁻¹ * (δ + D) - (s - s₀ : ℝ) * β - (θ₀ * S₀ - s₀ * cgf T ρ θ₀)) =
      K * exp (-(s * β)) := by
    rw [← exp_add]
    congr 1
    field_simp
    ring
  rw [hK, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  field_simp
  ring

/-- **Posterior concentration, upper tail** [KKM13, Theorem 4]. Let `μ₀ < m` be means of the
family and `0 ≤ δ ≤ m - μ₀`, and let the posterior of the Jeffreys prior after `s₀` observations
whose statistics sum to `s₀ (μ₀ + δ)` have a finite normalizing constant (for example `s₀ = 0`
for a proper Jeffreys prior). There are constants `C` and `N` such that for every `s ≥ N` and
every sum of statistics `S` with `|S - s μ₀| ≤ s δ`, the posterior probability that the mean
`ψ'(θ)` is at least `m` is at most `C s exp (-s (d(μ₀, m) - δ (η(m) - η(μ₀))))`. -/
theorem exists_expFamilyPosterior_jeffreysPrior_setOf_le_deriv_cgf_le
    (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T)
    (hm : m ∈ ρ.expFamilyMeans T) (hδ : 0 ≤ δ) (hδm : δ ≤ m - μ₀) (s₀ : ℕ)
    (hZ : ∫⁻ θ in interior (integrableExpSet T ρ),
      ENNReal.ofReal (exp (θ * (s₀ * (μ₀ + δ)) - s₀ * cgf T ρ θ)) ∂(ρ.jeffreysPrior T) ≠ ∞) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ s ≥ N, ∀ S, |S - s * μ₀| ≤ s * δ →
      ρ.expFamilyPosterior T (ρ.jeffreysPrior T) s S {θ | m ≤ deriv (cgf T ρ) θ} ≤
        ENNReal.ofReal (C * s * exp (-(s *
          (ρ.expFamilyDiv T μ₀ m - δ * (ρ.natParam T m - ρ.natParam T μ₀))))) :=
  exists_expFamilyPosterior_jeffreysPrior_le hT hμ₀ s₀ hZ fun _ hs _ hS _ _ hr hΘ hD ↦
    expFamilyPosterior_setOf_le_deriv_cgf_le hT hμ₀ hm hδ hδm hs hr hΘ hD hS

/-- **Posterior concentration, lower tail** [KKM13, Section 3, Step 3]. Let `m < μ₀` be means of
the family and `0 ≤ δ ≤ μ₀ - m`, and let the posterior of the Jeffreys prior after `s₀`
observations whose statistics sum to `s₀ (μ₀ - δ)` have a finite normalizing constant. There are
constants `C` and `N` such that for every `s ≥ N` and every sum of statistics `S` with
`|S - s μ₀| ≤ s δ`, the posterior probability that the mean `ψ'(θ)` is at most `m` is at most
`C s exp (-s (d(μ₀, m) - δ (η(μ₀) - η(m))))`. -/
theorem exists_expFamilyPosterior_jeffreysPrior_setOf_deriv_cgf_le_le
    (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hμ₀ : μ₀ ∈ ρ.expFamilyMeans T)
    (hm : m ∈ ρ.expFamilyMeans T) (hδ : 0 ≤ δ) (hδm : δ ≤ μ₀ - m) (s₀ : ℕ)
    (hZ : ∫⁻ θ in interior (integrableExpSet T ρ),
      ENNReal.ofReal (exp (θ * (s₀ * (μ₀ - δ)) - s₀ * cgf T ρ θ)) ∂(ρ.jeffreysPrior T) ≠ ∞) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ s ≥ N, ∀ S, |S - s * μ₀| ≤ s * δ →
      ρ.expFamilyPosterior T (ρ.jeffreysPrior T) s S {θ | deriv (cgf T ρ) θ ≤ m} ≤
        ENNReal.ofReal (C * s * exp (-(s *
          (ρ.expFamilyDiv T μ₀ m - δ * (ρ.natParam T μ₀ - ρ.natParam T m))))) :=
  exists_expFamilyPosterior_jeffreysPrior_le hT hμ₀ s₀ hZ fun _ hs _ hS _ _ hr hΘ hD ↦
    expFamilyPosterior_setOf_deriv_cgf_le_le hT hμ₀ hm hδ hδm hs hr hΘ hD hS

end MeasureTheory.Measure
