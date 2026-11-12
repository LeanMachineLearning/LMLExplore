/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Distributions.ExponentialFamily.Mean
public import LMLExplore.Probability.Moments.RateFunction

/-!
# The rate function of the statistic of an exponential family

Let `ρ` be a measure on `𝓧` and `T : 𝓧 → ℝ` a statistic, with log-partition function
`ψ = cgf T ρ`. Under a member `ρ_η` of their exponential family, the cumulant generating function
of `T` is `t ↦ ψ(η + t) - ψ(η)`, so the Cramér rate function of `T` under `ρ_η` at a level `x`
is a supremum over the natural parameters `η + t`. At a mean `x` of the family the supremum is
attained at the natural parameter `η(x)` of `x`, and its value is the Kullback–Leibler divergence
`KL(ρ_η(x), ρ_η)`: the rate function of `T` under `ρ_η` at `x` is the divergence from the member
of mean `x` to `ρ_η`. In the mean parametrization, the rate function of `T` under the member of
mean `μ` is `d(x, μ)` at every mean `x`. This is the exponent of the Chernoff bounds for the
empirical means of the statistic, and it extends `d(·, μ)` to every real level.

We call this extension `dbar(x, μ)`, defined for every real level `x` and every mean `μ`. It is the
generalized likelihood ratio extension of `d` to empirical means outside the open interval of
means, for example the empirical means `0` and `1` of Bernoulli observations. Through the natural
parameters of `ρ`, `dbar(x, μ) = ψ*(x) - x η(μ) + ψ(η(μ))` with `ψ*` the convex conjugate of `ψ`, so
changing the mean `μ` shifts `dbar(x, ·)` by a real term: this is the three-point identity
`dbar(x, μ) = dbar(x, q) + d(q, μ) + (q - x) (η(μ) - η(q))` for means `q` and `μ`. With the
continuity of `dbar(·, μ)` on the closure of the means, where the convex function `dbar(·, μ)` is
monotone on each side of `μ`, it makes `dbar` continuous on (closure of the means) × (means).

## Main definitions

* `MeasureTheory.Measure.expFamilyRate ρ T x μ`: the extended divergence `dbar(x, μ)`, the rate
  function of `T` under the member of mean `μ` at the level `x`.

## Main statements

* `LMLExplore.rateFunction_expFamily`: the rate function of `T` under `ρ_η` at a mean `x` of the
  family is `KL(ρ_η(x), ρ_η)`.
* `LMLExplore.rateFunction_expFamily_natParam`: the rate function of `T` under the member of mean
  `μ` at a mean `x` is `d(x, μ)`.
* `LMLExplore.rateFunction_eq_ofReal_expFamilyDiv`: the rate function of `T` under a probability
  measure `ρ` itself, at a mean `x`, is the divergence `d(x, ψ'(0))` to the mean of `ρ`.
* `MeasureTheory.Measure.expFamilyRate_eq_ofReal_expFamilyDiv`: `dbar = d` on the means.
* `MeasureTheory.Measure.expFamilyRate_eq_iSup`: `dbar(x, μ)` as a supremum over the natural
  parameters of `ρ`.
* `MeasureTheory.Measure.expFamilyRate_three_point`: the three-point identity, and
  `MeasureTheory.Measure.expFamilyRate_eq_add_of_mul_nonneg` its form when the shift is
  nonnegative.
* `MeasureTheory.Measure.expFamilyRate_ne_top_iff`,
  `MeasureTheory.Measure.expFamilyRate_eq_ofReal_toReal_add`: `dbar(x, ·)` is finite at every mean
  or at none, and where finite it is a real shift of its value at any one mean.
* `MeasureTheory.Measure.continuousOn_expFamilyRate_right`: for every level `x`, `dbar(x, ·)` is
  continuous on the means.
* `MeasureTheory.Measure.monotoneOn_expFamilyRate_right`,
  `MeasureTheory.Measure.antitoneOn_expFamilyRate_right`: `dbar(x, ·)` is monotone on the means
  above `x` and antitone on the means below `x`.
* `MeasureTheory.Measure.monotoneOn_expFamilyRate_left`,
  `MeasureTheory.Measure.antitoneOn_expFamilyRate_left`,
  `MeasureTheory.Measure.lowerSemicontinuous_expFamilyRate_left`: `dbar(·, μ)` is monotone above
  the mean `μ`, antitone below it, and lower semicontinuous.
* `MeasureTheory.Measure.continuousOn_expFamilyRate_left`: `dbar(·, μ)` is continuous on the closure
  of the means.
* `MeasureTheory.Measure.continuousOn_expFamilyRate`: `dbar` is continuous on
  (closure of the means) × (means), as an `ℝ≥0∞`-valued function.
* `MeasureTheory.Measure.sq_div_le_expFamilyDiv_of_hasSubgaussianMGF`: if `T - μ` is
  `c`-sub-Gaussian under the member of mean `μ`, then `(x - μ)² / (2 c) ≤ d(x, μ)` at every mean
  `x`, since `d(·, μ)` is the rate function of `T` under that member. This complements
  `MeasureTheory.Measure.sq_div_le_expFamilyDiv`, which bounds the variances of the members between
  `x` and `μ` instead.

The last statement is adapted from the formalization Degenne2023Existence
(`github.com/RemyDegenne/Degenne2023Existence`, file
`Degenne2023Existence/ForLMLExplore/Probability/Distributions/ExponentialFamily/RateFunction.lean`,
commit `a4244176eae7d9dd79c5c082f361c3b3b2541c0f`, by Rémy Degenne, Apache 2.0).
-/

public section

open MeasureTheory Measure ProbabilityTheory InformationTheory Set

open scoped ENNReal

namespace LMLExplore

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {η x μ : ℝ}

/-- The rate function of the statistic `T` under the member `ρ_η` of its exponential family, at a
mean `x` of the family, is the Kullback–Leibler divergence `KL(ρ_η(x), ρ_η)` from the member of
mean `x`. -/
theorem rateFunction_expFamily (hη : η ∈ integrableExpSet T ρ) (hx : x ∈ ρ.expFamilyMeans T) :
    rateFunction T (ρ.expFamily T η) x =
      klDiv (ρ.expFamily T (ρ.natParam T x)) (ρ.expFamily T η) := by
  have hηx := natParam_mem_interior_integrableExpSet hx
  have hηx' := interior_subset hηx
  rw [klDiv_expFamily hηx hη, deriv_cgf_natParam hx]
  refine le_antisymm ((rateFunction_le_iff).2 fun t ht ↦ ?_) ?_
  · -- `ψ(η + t) ≥ ψ(η(x)) + x (η + t - η(x))`: the log-partition function lies above its tangent
    -- line at `η(x)`.
    rw [integrableExpSet_expFamily hη, mem_preimage] at ht
    rw [cgf_expFamily hη ht]
    exact ENNReal.ofReal_le_ofReal (by linarith [cgf_natParam_add_mul_sub_le_cgf hx ht])
  · -- The supremum is attained at the natural parameter `η(x)`.
    have ht : ρ.natParam T x - η ∈ integrableExpSet T (ρ.expFamily T η) := by
      rwa [integrableExpSet_expFamily hη, mem_preimage, add_sub_cancel]
    refine (le_of_eq ?_).trans (ofReal_le_rateFunction ht x)
    rw [cgf_expFamily hη (by rwa [add_sub_cancel]), add_sub_cancel]
    congr 1
    ring

/-- The rate function of the statistic `T` under the member of mean `μ` of its exponential family
is the divergence `d(x, μ)` at every mean `x` of the family. -/
theorem rateFunction_expFamily_natParam (hx : x ∈ ρ.expFamilyMeans T)
    (hμ : μ ∈ ρ.expFamilyMeans T) :
    rateFunction T (ρ.expFamily T (ρ.natParam T μ)) x = ENNReal.ofReal (ρ.expFamilyDiv T x μ) := by
  rw [rateFunction_expFamily (interior_subset (natParam_mem_interior_integrableExpSet hμ)) hx,
    klDiv_expFamily_natParam hx hμ]

/-- The rate function of the statistic `T` under a probability measure `ρ` whose cumulant
generating function is finite near `0`, with `T` not `ρ`-almost everywhere constant, is the
divergence `d(x, ψ'(0))` to the mean `ψ'(0)` of `T` under `ρ` at every mean `x` of the family,
since `ρ` is the member `ρ_0` of the family. -/
theorem rateFunction_eq_ofReal_expFamilyDiv [IsProbabilityMeasure ρ]
    (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (h0 : 0 ∈ interior (integrableExpSet T ρ))
    (hx : x ∈ ρ.expFamilyMeans T) :
    rateFunction T ρ x = ENNReal.ofReal (ρ.expFamilyDiv T x (deriv (cgf T ρ) 0)) := by
  have h := rateFunction_expFamily_natParam hx (deriv_cgf_mem_expFamilyMeans h0)
  rwa [natParam_deriv_cgf hT h0, expFamily_zero] at h

end LMLExplore

namespace MeasureTheory.Measure

open LMLExplore Filter

open scoped Topology

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {x μ q : ℝ}

/-! ### The divergence extended to every level -/

/-- The divergence `dbar(x, μ)` of the exponential family of `ρ` and `T`, extended to every real
level `x`: the Cramér rate function at `x` of the statistic `T` under the member
`ρ.expFamily T (ρ.natParam T μ)` of mean `μ`, valued in `ℝ≥0∞`. At a mean `x` of the family it is
the divergence `d(x, μ)` (`expFamilyRate_eq_ofReal_expFamilyDiv`); at the other levels it is the
generalized likelihood ratio extension of `d(·, μ)`, possibly infinite. The value is meaningful
for `μ ∈ ρ.expFamilyMeans T` only. -/
noncomputable def expFamilyRate (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (x μ : ℝ) : ℝ≥0∞ :=
  rateFunction T (ρ.expFamily T (ρ.natParam T μ)) x

lemma expFamilyRate_def (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (x μ : ℝ) :
    ρ.expFamilyRate T x μ = rateFunction T (ρ.expFamily T (ρ.natParam T μ)) x :=
  (rfl)

/-- At the means of the family, the extended divergence `dbar(x, μ)` is the divergence `d(x, μ)`. -/
theorem expFamilyRate_eq_ofReal_expFamilyDiv (hx : x ∈ ρ.expFamilyMeans T)
    (hμ : μ ∈ ρ.expFamilyMeans T) :
    ρ.expFamilyRate T x μ = ENNReal.ofReal (ρ.expFamilyDiv T x μ) := by
  rw [expFamilyRate_def, rateFunction_expFamily_natParam hx hμ]

/-- The extended divergence vanishes on the diagonal of the means. -/
@[simp]
lemma expFamilyRate_self (hμ : μ ∈ ρ.expFamilyMeans T) : ρ.expFamilyRate T μ μ = 0 := by
  rw [expFamilyRate_eq_ofReal_expFamilyDiv hμ hμ, expFamilyDiv_self, ENNReal.ofReal_zero]

/-- The extended divergence through the natural parameters of `ρ`: with `ψ = cgf T ρ` and
`η = η(μ)`, `dbar(x, μ) = sup_θ ((θ - η) x - ψ(θ) + ψ(η))` over `θ ∈ integrableExpSet T ρ`. -/
theorem expFamilyRate_eq_iSup (hμ : μ ∈ ρ.expFamilyMeans T) (x : ℝ) :
    ρ.expFamilyRate T x μ = ⨆ θ ∈ integrableExpSet T ρ,
      ENNReal.ofReal ((θ - ρ.natParam T μ) * x - cgf T ρ θ + cgf T ρ (ρ.natParam T μ)) := by
  have hη := interior_subset (natParam_mem_interior_integrableExpSet hμ)
  rw [expFamilyRate_def]
  refine le_antisymm (rateFunction_le_iff.2 fun t ht ↦ ?_) (iSup₂_le fun θ hθ ↦ ?_)
  · rw [integrableExpSet_expFamily hη, mem_preimage] at ht
    refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun θ (_ : θ ∈ integrableExpSet T ρ) ↦
      ENNReal.ofReal ((θ - ρ.natParam T μ) * x - cgf T ρ θ + cgf T ρ (ρ.natParam T μ)))
      (ρ.natParam T μ + t) ht)
    rw [cgf_expFamily hη ht]
    congr 1
    ring
  · have ht : θ - ρ.natParam T μ ∈ integrableExpSet T (ρ.expFamily T (ρ.natParam T μ)) := by
      rwa [integrableExpSet_expFamily hη, mem_preimage, add_sub_cancel]
    refine le_trans (le_of_eq ?_) (ofReal_le_rateFunction ht x)
    rw [cgf_expFamily hη (by rwa [add_sub_cancel]), add_sub_cancel]
    congr 1
    ring

/-- One half of the three-point identity `expFamilyRate_three_point`, written with
`c = ψ(η(μ)) - ψ(η(q)) - x (η(μ) - η(q))`. -/
private lemma expFamilyRate_add_ofReal_neg_le (hq : q ∈ ρ.expFamilyMeans T)
    (hμ : μ ∈ ρ.expFamilyMeans T) (x : ℝ) :
    ρ.expFamilyRate T x μ + ENNReal.ofReal (-(cgf T ρ (ρ.natParam T μ) -
        cgf T ρ (ρ.natParam T q) - x * (ρ.natParam T μ - ρ.natParam T q))) ≤
      ρ.expFamilyRate T x q + ENNReal.ofReal (cgf T ρ (ρ.natParam T μ) -
        cgf T ρ (ρ.natParam T q) - x * (ρ.natParam T μ - ρ.natParam T q)) := by
  -- Each term of `dbar(x, q)` is bounded by `dbar(x, q)`, and so is `-c`, the term at `θ = η(μ)`.
  have hle (θ : ℝ) (hθ : θ ∈ integrableExpSet T ρ) :
      ENNReal.ofReal ((θ - ρ.natParam T q) * x - cgf T ρ θ + cgf T ρ (ρ.natParam T q)) ≤
        ρ.expFamilyRate T x q := by
    rw [expFamilyRate_eq_iSup hq]
    exact le_iSup₂ (f := fun θ (_ : θ ∈ integrableExpSet T ρ) ↦
      ENNReal.ofReal ((θ - ρ.natParam T q) * x - cgf T ρ θ + cgf T ρ (ρ.natParam T q))) θ hθ
  have hwit : ENNReal.ofReal (-(cgf T ρ (ρ.natParam T μ) - cgf T ρ (ρ.natParam T q) -
      x * (ρ.natParam T μ - ρ.natParam T q))) ≤ ρ.expFamilyRate T x q := by
    refine le_trans (le_of_eq ?_)
      (hle _ (interior_subset (natParam_mem_interior_integrableExpSet hμ)))
    congr 1
    ring
  -- The terms of `dbar(x, μ)` are those of `dbar(x, q)` shifted by `c`.
  have hsplit (θ : ℝ) : (θ - ρ.natParam T μ) * x - cgf T ρ θ + cgf T ρ (ρ.natParam T μ) =
      ((θ - ρ.natParam T q) * x - cgf T ρ θ + cgf T ρ (ρ.natParam T q)) +
        (cgf T ρ (ρ.natParam T μ) - cgf T ρ (ρ.natParam T q) -
          x * (ρ.natParam T μ - ρ.natParam T q)) := by
    ring
  rw [expFamilyRate_eq_iSup hμ]
  rcases le_or_gt 0 (cgf T ρ (ρ.natParam T μ) - cgf T ρ (ρ.natParam T q) -
      x * (ρ.natParam T μ - ρ.natParam T q)) with hc | hc
  · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.2 hc), add_zero]
    refine iSup₂_le fun θ hθ ↦ ?_
    rw [hsplit]
    exact ENNReal.ofReal_add_le.trans (add_le_add_left (hle θ hθ) _)
  · rw [ENNReal.ofReal_of_nonpos hc.le, add_zero, ENNReal.iSup_add]
    refine iSup_le fun θ ↦ ?_
    by_cases hθ : θ ∈ integrableExpSet T ρ
    · rw [iSup_pos hθ, hsplit]
      rcases le_or_gt 0 (((θ - ρ.natParam T q) * x - cgf T ρ θ + cgf T ρ (ρ.natParam T q)) +
          (cgf T ρ (ρ.natParam T μ) - cgf T ρ (ρ.natParam T q) -
            x * (ρ.natParam T μ - ρ.natParam T q))) with h | h
      · rw [← ENNReal.ofReal_add h (neg_nonneg.2 hc.le), add_neg_cancel_right]
        exact hle θ hθ
      · rw [ENNReal.ofReal_of_nonpos h.le, zero_add]
        exact hwit
    · rw [iSup_neg hθ, bot_eq_zero, zero_add]
      exact hwit

/-- **Three-point identity** for the extended divergence: for every level `x` and means `q, μ`,
`dbar(x, μ) = dbar(x, q) + c` with `c = d(q, μ) + (q - x) (η(μ) - η(q))`, written in `ℝ≥0∞` as
`dbar(x, μ) + (-c)⁺ = dbar(x, q) + c⁺` since `c` may be negative. The term `c` is nonnegative
when `x` lies beyond `q` on the other side of `μ` (`expFamilyRate_eq_add_of_mul_nonneg`). -/
theorem expFamilyRate_three_point (hq : q ∈ ρ.expFamilyMeans T) (hμ : μ ∈ ρ.expFamilyMeans T)
    (x : ℝ) :
    ρ.expFamilyRate T x μ +
        ENNReal.ofReal (-(ρ.expFamilyDiv T q μ + (q - x) * (ρ.natParam T μ - ρ.natParam T q))) =
      ρ.expFamilyRate T x q +
        ENNReal.ofReal (ρ.expFamilyDiv T q μ + (q - x) * (ρ.natParam T μ - ρ.natParam T q)) := by
  have hc : ρ.expFamilyDiv T q μ + (q - x) * (ρ.natParam T μ - ρ.natParam T q) =
      cgf T ρ (ρ.natParam T μ) - cgf T ρ (ρ.natParam T q) -
        x * (ρ.natParam T μ - ρ.natParam T q) := by
    rw [expFamilyDiv_def]
    ring
  rw [hc]
  refine le_antisymm (expFamilyRate_add_ofReal_neg_le hq hμ x) ?_
  convert expFamilyRate_add_ofReal_neg_le hμ hq x using 3 <;> ring

/-- The three-point identity `dbar(x, μ) = dbar(x, q) + d(q, μ) + (q - x) (η(μ) - η(q))` when its
last term is nonnegative, for example when `x ≤ q ≤ μ` or `μ ≤ q ≤ x`. -/
theorem expFamilyRate_eq_add_of_mul_nonneg (hq : q ∈ ρ.expFamilyMeans T)
    (hμ : μ ∈ ρ.expFamilyMeans T) (h : 0 ≤ (q - x) * (ρ.natParam T μ - ρ.natParam T q)) :
    ρ.expFamilyRate T x μ = ρ.expFamilyRate T x q +
      ENNReal.ofReal (ρ.expFamilyDiv T q μ + (q - x) * (ρ.natParam T μ - ρ.natParam T q)) := by
  have h3 := expFamilyRate_three_point hq hμ x
  rwa [ENNReal.ofReal_of_nonpos (neg_nonpos.2 (add_nonneg (expFamilyDiv_nonneg hq hμ) h)),
    add_zero] at h3

/-- For a level `x`, the extended divergence `dbar(x, ·)` is finite at one mean exactly when it is
finite at every mean. -/
theorem expFamilyRate_ne_top_iff (hq : q ∈ ρ.expFamilyMeans T) (hμ : μ ∈ ρ.expFamilyMeans T)
    (x : ℝ) : ρ.expFamilyRate T x μ ≠ ∞ ↔ ρ.expFamilyRate T x q ≠ ∞ := by
  have h3 := expFamilyRate_three_point hq hμ x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' : ρ.expFamilyRate T x q + ENNReal.ofReal (ρ.expFamilyDiv T q μ +
        (q - x) * (ρ.natParam T μ - ρ.natParam T q)) ≠ ∞ := by
      rw [← h3]
      exact ENNReal.add_ne_top.2 ⟨h, ENNReal.ofReal_ne_top⟩
    exact (ENNReal.add_ne_top.1 h').1
  · have h' : ρ.expFamilyRate T x μ + ENNReal.ofReal (-(ρ.expFamilyDiv T q μ +
        (q - x) * (ρ.natParam T μ - ρ.natParam T q))) ≠ ∞ := by
      rw [h3]
      exact ENNReal.add_ne_top.2 ⟨h, ENNReal.ofReal_ne_top⟩
    exact (ENNReal.add_ne_top.1 h').1

/-- The three-point identity in real form: where `dbar(x, q)` is finite, for every mean `μ`,
`dbar(x, μ) = dbar(x, q) + d(q, μ) + (q - x) (η(μ) - η(q))`. Changing the mean shifts the finite
extended divergence by a real term that is continuous in `μ`. -/
theorem expFamilyRate_eq_ofReal_toReal_add (hq : q ∈ ρ.expFamilyMeans T)
    (hμ : μ ∈ ρ.expFamilyMeans T) (h : ρ.expFamilyRate T x q ≠ ∞) :
    ρ.expFamilyRate T x μ = ENNReal.ofReal ((ρ.expFamilyRate T x q).toReal +
      (ρ.expFamilyDiv T q μ + (q - x) * (ρ.natParam T μ - ρ.natParam T q))) := by
  have hμ' := (expFamilyRate_ne_top_iff hq hμ x).2 h
  have h3 := congrArg ENNReal.toReal (expFamilyRate_three_point hq hμ x)
  rw [ENNReal.toReal_add hμ' ENNReal.ofReal_ne_top, ENNReal.toReal_add h ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at h3
  rw [← ENNReal.ofReal_toReal hμ']
  congr 1
  linarith [max_zero_sub_max_neg_zero_eq_self
    (ρ.expFamilyDiv T q μ + (q - x) * (ρ.natParam T μ - ρ.natParam T q))]

/-- For every level `x`, the extended divergence `dbar(x, ·)` is continuous on the means, as an
`ℝ≥0∞`-valued function: it is infinite on all of them, or a real shift of its finite value at one
of them. Unlike `continuousOn_expFamilyRate`, the level `x` need not lie in the closure of the
means. -/
theorem continuousOn_expFamilyRate_right (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (x : ℝ) :
    ContinuousOn (ρ.expFamilyRate T x) (ρ.expFamilyMeans T) := by
  intro q hq
  by_cases h : ρ.expFamilyRate T x q = ∞
  · refine continuousWithinAt_const.congr (fun μ hμ ↦ ?_) h
    by_contra hμ'
    exact (expFamilyRate_ne_top_iff hq hμ x).1 hμ' h
  · have hc : ContinuousOn (fun μ ↦ ENNReal.ofReal ((ρ.expFamilyRate T x q).toReal +
        (ρ.expFamilyDiv T q μ + (q - x) * (ρ.natParam T μ - ρ.natParam T q))))
        (ρ.expFamilyMeans T) :=
      ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_const.add
        (((continuousOn_expFamilyDiv hT).comp (continuousOn_const.prodMk continuousOn_id)
          fun μ hμ ↦ ⟨hq, hμ⟩).add
        (continuousOn_const.mul ((continuousOn_natParam hT).sub continuousOn_const))))
    exact (hc q hq).congr (fun μ hμ ↦ expFamilyRate_eq_ofReal_toReal_add hq hμ h)
      (expFamilyRate_eq_ofReal_toReal_add hq hq h)

/-- The extended divergence `dbar(x, ·)` is monotone on the means above `x`. -/
theorem monotoneOn_expFamilyRate_right (x : ℝ) :
    MonotoneOn (ρ.expFamilyRate T x) (ρ.expFamilyMeans T ∩ Ici x) := by
  intro q hq μ hμ hqμ
  rw [expFamilyRate_eq_add_of_mul_nonneg hq.1 hμ.1 (mul_nonneg (sub_nonneg.2 hq.2)
    (sub_nonneg.2 (monotoneOn_natParam hq.1 hμ.1 hqμ)))]
  exact le_self_add

/-- The extended divergence `dbar(x, ·)` is antitone on the means below `x`. -/
theorem antitoneOn_expFamilyRate_right (x : ℝ) :
    AntitoneOn (ρ.expFamilyRate T x) (ρ.expFamilyMeans T ∩ Iic x) := by
  intro μ hμ q hq hμq
  rw [expFamilyRate_eq_add_of_mul_nonneg hq.1 hμ.1 (mul_nonneg_of_nonpos_of_nonpos
    (sub_nonpos.2 hq.2) (sub_nonpos.2 (monotoneOn_natParam hμ.1 hq.1 hμq)))]
  exact le_self_add

/-- For a mean `μ`, the extended divergence `dbar(·, μ)` is monotone on the levels above `μ`. -/
theorem monotoneOn_expFamilyRate_left (hμ : μ ∈ ρ.expFamilyMeans T) :
    MonotoneOn (ρ.expFamilyRate T · μ) (Ici μ) := by
  rcases eq_zero_or_neZero ρ with rfl | hρ
  · -- For the zero measure, the only mean is `0`, and `dbar(x, 0)` is `0` at `0` and `∞` elsewhere.
    obtain ⟨η, -, rfl⟩ := mem_expFamilyMeans_iff.1 hμ
    intro a ha b hb hab
    simp only [mem_Ici, cgf_zero_measure, Pi.zero_def, deriv_const] at ha
    simp_rw [expFamilyRate_def, expFamily_zero_measure, rateFunction_zero_measure]
    rcases eq_or_lt_of_le ha with rfl | ha₀
    · simp
    · simp [ha₀.ne', (ha₀.trans_le hab).ne']
  · have hη := natParam_mem_interior_integrableExpSet hμ
    have := isProbabilityMeasure_expFamily (interior_subset hη)
    simpa only [expFamilyRate_def, integral_expFamily_natParam hμ] using
      monotoneOn_rateFunction (integrable_expFamily hη)

/-- For a mean `μ`, the extended divergence `dbar(·, μ)` is antitone on the levels below `μ`. -/
theorem antitoneOn_expFamilyRate_left (hμ : μ ∈ ρ.expFamilyMeans T) :
    AntitoneOn (ρ.expFamilyRate T · μ) (Iic μ) := by
  rcases eq_zero_or_neZero ρ with rfl | hρ
  · -- For the zero measure, the only mean is `0`, and `dbar(x, 0)` is `0` at `0` and `∞` elsewhere.
    obtain ⟨η, -, rfl⟩ := mem_expFamilyMeans_iff.1 hμ
    intro a ha b hb hab
    simp only [mem_Iic, cgf_zero_measure, Pi.zero_def, deriv_const] at hb
    simp_rw [expFamilyRate_def, expFamily_zero_measure, rateFunction_zero_measure]
    rcases eq_or_lt_of_le hb with rfl | hb₀
    · simp
    · simp [hb₀.ne, (hab.trans_lt hb₀).ne]
  · have hη := natParam_mem_interior_integrableExpSet hμ
    have := isProbabilityMeasure_expFamily (interior_subset hη)
    simpa only [expFamilyRate_def, integral_expFamily_natParam hμ] using
      antitoneOn_rateFunction (integrable_expFamily hη)

/-- The extended divergence `dbar(·, μ)` is lower semicontinuous, as a rate function. -/
theorem lowerSemicontinuous_expFamilyRate_left (μ : ℝ) :
    LowerSemicontinuous (ρ.expFamilyRate T · μ) := by
  simpa only [expFamilyRate_def] using lowerSemicontinuous_rateFunction T _

/-! ### Continuity -/

/-- For a mean `μ`, the extended divergence `dbar(·, μ)` is continuous on the closure of the means,
as an `ℝ≥0∞`-valued function, including at the endpoints where it may be infinite. -/
theorem continuousOn_expFamilyRate_left (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : μ ∈ ρ.expFamilyMeans T) :
    ContinuousOn (fun x ↦ ρ.expFamilyRate T x μ) (closure (ρ.expFamilyMeans T)) := by
  intro x₀ hx₀
  -- On the open interval of means, `dbar(·, μ)` is `d(·, μ)`.
  by_cases hx₀M : x₀ ∈ ρ.expFamilyMeans T
  · have hM := expFamilyMeans_mem_nhds hT hx₀M
    have hd : ContinuousAt (fun x ↦ ENNReal.ofReal (ρ.expFamilyDiv T x μ)) x₀ :=
      ENNReal.continuous_ofReal.continuousAt.comp (((continuousOn_expFamilyDiv hT).comp
        (continuousOn_id.prodMk continuousOn_const) fun x hx ↦ ⟨hx, hμ⟩).continuousAt hM)
    refine (hd.congr ?_).continuousWithinAt
    filter_upwards [hM] with x hx using (expFamilyRate_eq_ofReal_expFamilyDiv hx hμ).symm
  -- At an endpoint `x₀`, `dbar(·, μ)` is lower semicontinuous, and bounded by its value at `x₀`
  -- between the mean `μ` and `x₀`, where it is monotone.
  rw [continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
  refine ⟨((lowerSemicontinuous_expFamilyRate_left μ).lowerSemicontinuousAt x₀)
    |>.lowerSemicontinuousWithinAt _, fun y hy ↦ ?_⟩
  -- Near the endpoint `x₀`, the closure of the means lies between `μ` and `x₀`.
  suffices h : ∀ᶠ x in 𝓝[closure (ρ.expFamilyMeans T)] x₀,
      ρ.expFamilyRate T x μ ≤ ρ.expFamilyRate T x₀ μ from
    h.mono fun x hx ↦ hx.trans_lt hy
  rcases lt_or_gt_of_ne (show μ ≠ x₀ from fun h ↦ hx₀M (h ▸ hμ)) with hlt | hlt
  · have hsub : closure (ρ.expFamilyMeans T) ⊆ Iic x₀ := closure_minimal (fun a ha ↦ not_lt.1
      fun hxa ↦ hx₀M (Icc_subset_expFamilyMeans hμ ha ⟨hlt.le, hxa.le⟩)) isClosed_Iic
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hlt)] with x hx hx'
    exact monotoneOn_expFamilyRate_left hμ (mem_Ioi.1 hx').le hlt.le (hsub hx)
  · have hsub : closure (ρ.expFamilyMeans T) ⊆ Ici x₀ := closure_minimal (fun a ha ↦ not_lt.1
      fun hax ↦ hx₀M (Icc_subset_expFamilyMeans ha hμ ⟨hax.le, hlt.le⟩)) isClosed_Ici
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hlt)] with x hx hx'
    exact antitoneOn_expFamilyRate_left hμ hlt.le (mem_Iio.1 hx').le (hsub hx)

/-- **Continuity of the extended divergence**: `(x, μ) ↦ dbar(x, μ)` is continuous on the pairs of a
level in the closure of the means and a mean, as an `ℝ≥0∞`-valued function. -/
theorem continuousOn_expFamilyRate (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) :
    ContinuousOn (fun p : ℝ × ℝ ↦ ρ.expFamilyRate T p.1 p.2)
      (closure (ρ.expFamilyMeans T) ×ˢ ρ.expFamilyMeans T) := by
  -- By the three-point identity, `dbar(x, μ)` is `dbar(x, μ₀)` shifted by a real term `c (x, μ)`,
  -- continuous in `(x, μ)` and zero at `(x₀, μ₀)`.
  rintro ⟨x₀, μ₀⟩ ⟨hx₀, hμ₀⟩
  set s := closure (ρ.expFamilyMeans T) ×ˢ ρ.expFamilyMeans T
  set c : ℝ × ℝ → ℝ := fun p ↦
    ρ.expFamilyDiv T μ₀ p.2 + (μ₀ - p.1) * (ρ.natParam T p.2 - ρ.natParam T μ₀)
  have hc : ContinuousWithinAt c s (x₀, μ₀) := by
    have hd := (continuousOn_expFamilyDiv hT).comp (continuousOn_const.prodMk continuousOn_snd)
      (s := s) fun p hp ↦ ⟨hμ₀, hp.2⟩
    have hη := (continuousOn_natParam hT).comp continuousOn_snd (s := s) fun p hp ↦ hp.2
    exact (hd.add ((continuousOn_const.sub continuousOn_fst).mul
      (hη.sub continuousOn_const))) (x₀, μ₀) ⟨hx₀, hμ₀⟩
  have hc0 : c (x₀, μ₀) = 0 := by simp [c]
  have hpos : Tendsto (fun p ↦ ENNReal.ofReal (c p)) (𝓝[s] (x₀, μ₀)) (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto _).comp hc
    rwa [hc0, ENNReal.ofReal_zero] at h
  have hneg : Tendsto (fun p ↦ ENNReal.ofReal (-c p)) (𝓝[s] (x₀, μ₀)) (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto _).comp hc.neg
    rwa [Pi.neg_apply, hc0, neg_zero, ENNReal.ofReal_zero] at h
  have hJ : ContinuousWithinAt (fun p : ℝ × ℝ ↦ ρ.expFamilyRate T p.1 μ₀) s (x₀, μ₀) :=
    (continuousOn_expFamilyRate_left hT hμ₀ x₀ hx₀).comp continuousWithinAt_fst
      fun p hp ↦ hp.1
  have h3 : ∀ p ∈ s, ρ.expFamilyRate T p.1 p.2 + ENNReal.ofReal (-c p) =
      ρ.expFamilyRate T p.1 μ₀ + ENNReal.ofReal (c p) := fun p hp ↦
    expFamilyRate_three_point hμ₀ hp.2 p.1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun p ↦
      ρ.expFamilyRate T p.1 μ₀ - ENNReal.ofReal (-c p))
    (h := fun p ↦ ρ.expFamilyRate T p.1 μ₀ + ENNReal.ofReal (c p)) ?_ ?_ ?_ ?_
  · simpa using ENNReal.Tendsto.sub hJ.tendsto hneg (Or.inr ENNReal.zero_ne_top)
  · simpa using hJ.tendsto.add hpos
  · filter_upwards [self_mem_nhdsWithin] with p hp
    rw [tsub_le_iff_right, h3 p hp]
    exact le_self_add
  · filter_upwards [self_mem_nhdsWithin] with p hp
    rw [← h3 p hp]
    exact le_self_add

/-! ### Sub-Gaussian members -/

/-- **Sub-Gaussian comparison.** If the statistic `T` is `c`-sub-Gaussian around its mean `μ` under
the member of mean `μ` of the exponential family, then `(x - μ)² / (2 c) ≤ d(x, μ)` for every mean
`x` of the family. -/
theorem sq_div_le_expFamilyDiv_of_hasSubgaussianMGF (hx : x ∈ ρ.expFamilyMeans T)
    (hμ : μ ∈ ρ.expFamilyMeans T) {c : NNReal}
    (h : HasSubgaussianMGF (fun ω ↦ T ω - μ) c (ρ.expFamily T (ρ.natParam T μ))) :
    (x - μ) ^ 2 / (2 * c) ≤ ρ.expFamilyDiv T x μ := by
  rcases eq_zero_or_neZero ρ with rfl | _
  · rw [expFamilyMeans_zero_measure, mem_singleton_iff] at hx hμ
    simp [hx, hμ, expFamilyDiv_self]
  have hη := natParam_mem_interior_integrableExpSet hμ
  have := isProbabilityMeasure_expFamily (ρ := ρ) (T := T) (interior_subset hη)
  have h_mean := integral_expFamily_natParam hμ
  have h' : HasSubgaussianMGF (fun ω ↦ T ω - ∫ y, T y ∂(ρ.expFamily T (ρ.natParam T μ))) c
      (ρ.expFamily T (ρ.natParam T μ)) := by
    rwa [h_mean]
  have h_le := h'.ofReal_sq_div_le_rateFunction x
  rw [h_mean, rateFunction_expFamily_natParam hx hμ] at h_le
  exact (ENNReal.ofReal_le_ofReal_iff (expFamilyDiv_nonneg hx hμ)).1 h_le

end MeasureTheory.Measure
