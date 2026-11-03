/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Distributions.ExponentialFamily.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The mean parametrization of an exponential family

Let `ρ` be a measure on a measurable space `𝓧` and `T : 𝓧 → ℝ` a statistic which is not
`ρ`-almost everywhere constant, with log-partition function `ψ = cgf T ρ`. The mean of `T` under
the member `ρ_η = ρ.expFamily T η` of their exponential family is `ψ'(η)`, and the mean map `ψ'` is
strictly increasing on the interior of the natural-parameter set `integrableExpSet T ρ`. Its image
is the open interval of the *means* of the family, and its inverse `μ ↦ η(μ)` parametrizes the
family by the means: `μ ↦ ρ_η(μ)` is the member under which `T` has mean `μ`. This is how the
family appears in the bandit literature, where a model is a vector of means.

In the mean parametrization, the Kullback–Leibler divergence between two members is
`d(μ, μ') = KL(ρ_η(μ), ρ_η(μ')) = ψ(η(μ')) - ψ(η(μ)) - μ (η(μ') - η(μ))`. It is nonnegative, zero
exactly on the diagonal, continuous on the pairs of means, strictly convex in its first argument
and, in each argument, strictly decreasing below the other argument and strictly increasing above
it. It is not convex in its second argument in general (exponential distributions are a
counterexample). If `T` has variance at most `v` under the members with mean between `μ` and `μ'`,
then `d(μ, μ') ≥ (μ - μ')² / (2 v)`, the divergence between Gaussian laws of variance `v`. For
weights `w i ≥ 0`, the weighted divergence `z ↦ ∑ i, w i d(μ i, z)` is minimal at the weighted mean
`m` of the `μ i`, by the compensation identity
`∑ i, w i d(μ i, z) = ∑ i, w i d(μ i, m) + (∑ i, w i) d(m, z)`. The
function `d` is the divergence of the transportation costs and of the
generalized likelihood ratio statistics of identification in bandits with arms in an exponential
family, for example in A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed
confidence*, COLT 2016.

## Main definitions

* `MeasureTheory.Measure.expFamilyMeans ρ T`: the set of means `ψ'(η)` of `T` under the members
  of the exponential family of `ρ` and `T` with natural parameter in the interior of
  `integrableExpSet T ρ`.
* `MeasureTheory.Measure.natParam ρ T μ`: the natural parameter `η(μ)` of the member of mean `μ`.
* `MeasureTheory.Measure.expFamilyDiv ρ T μ μ'`: the divergence
  `d(μ, μ') = ψ(η(μ')) - ψ(η(μ)) - μ (η(μ') - η(μ))`.
* `MeasureTheory.Measure.expFamilyPairCost ρ T μ₁ μ₂ w₁ w₂`: the cost
  `w₁ d(μ₁, m) + w₂ d(μ₂, m)` of moving two means to their weighted mean
  `m = (w₁ μ₁ + w₂ μ₂) / (w₁ + w₂)`.

## Main statements

* `MeasureTheory.Measure.isOpen_expFamilyMeans`,
  `MeasureTheory.Measure.convex_expFamilyMeans`: the means form an open interval.
* `MeasureTheory.Measure.integral_expFamily_natParam`: the member `ρ_η(μ)` has mean `μ`.
* `MeasureTheory.Measure.monotoneOn_natParam`: the natural parameter is monotone in the mean.
* `MeasureTheory.Measure.strictMonoOn_natParam`, `MeasureTheory.Measure.hasDerivAt_natParam`: the
  natural parameter is strictly increasing and differentiable in the mean, with derivative
  `1 / ψ''(η(μ))`.
* `MeasureTheory.Measure.klDiv_expFamily_natParam`: `KL(ρ_η(μ), ρ_η(μ')) = d(μ, μ')`.
* `MeasureTheory.Measure.expFamilyDiv_nonneg`,
  `MeasureTheory.Measure.expFamilyDiv_eq_zero_iff`: `d(μ, μ') ≥ 0`, with equality iff
  `μ = μ'`.
* `MeasureTheory.Measure.continuousOn_expFamilyDiv`: `d` is continuous on the pairs of means.
* `MeasureTheory.Measure.strictConvexOn_expFamilyDiv_left`: `d` is strictly convex in its first
  argument.
* `MeasureTheory.Measure.strictAntiOn_expFamilyDiv_left`,
  `MeasureTheory.Measure.strictMonoOn_expFamilyDiv_left`,
  `MeasureTheory.Measure.strictAntiOn_expFamilyDiv_right`,
  `MeasureTheory.Measure.strictMonoOn_expFamilyDiv_right`: in each argument, `d` is strictly
  decreasing below the other argument and strictly increasing above it.
* `MeasureTheory.Measure.exists_mem_Icc_expFamilyDiv_eq`: between two means `μ' ≤ μ` there is a
  mean `z` with `d(μ, z) = d(μ', z)`.
* `MeasureTheory.Measure.sq_div_le_expFamilyDiv`,
  `MeasureTheory.Measure.ofReal_sq_div_le_klDiv_expFamily_natParam`: the sub-Gaussian
  comparison `d(μ, μ') ≥ (μ - μ')² / (2 v)` when `T` has variance at most `v` under the members
  with mean strictly between `μ` and `μ'`.
* `MeasureTheory.Measure.sum_mul_expFamilyDiv_eq`: the compensation identity
  `∑ i, w i d(μ i, z) = ∑ i, w i d(μ i, m) + (∑ i, w i) d(m, z)` for the weighted mean `m`.
* `MeasureTheory.Measure.sum_mul_expFamilyDiv_le`: for nonnegative weights, the weighted mean
  minimizes the weighted divergence `z ↦ ∑ i, w i d(μ i, z)` over the means of the family.
* `MeasureTheory.Measure.div_mem_expFamilyMeans`: a weighted mean of two means of the family is a
  mean of the family.
* `MeasureTheory.Measure.mul_expFamilyDiv_add_mul_expFamilyDiv_le_of_mul_eq`: the two-point case
  of `sum_mul_expFamilyDiv_le`.
* `MeasureTheory.Measure.expFamilyPairCost_le_mul_expFamilyDiv_add_mul_expFamilyDiv`: for
  `μ₂ ≤ μ₁` and nonnegative weights, `w₁ d(μ₁, x) + w₂ d(μ₂, y)` at means `x ≤ y` is at least its
  value `expFamilyPairCost` at `x = y = m`, the weighted mean of `μ₁` and `μ₂`; when
  `w₁ + w₂ > 0`, this is the minimum over these pairs.
* `MeasureTheory.Measure.mul_expFamilyDiv_add_mul_expFamilyDiv_eq`: the two-point compensation
  identity `w₁ d(μ₁, z) + w₂ d(μ₂, z) = w₁ d(μ₁, m) + w₂ d(μ₂, m) + (w₁ + w₂) d(m, z)`.
* `MeasureTheory.Measure.strictMonoOn_expFamilyPairCost`: for distinct means and `w₁ > 0`, the
  cost `w₁ d(μ₁, m) + w₂ d(μ₂, m)` of moving them to their weighted mean `m` is strictly
  increasing in `w₂ ≥ 0`.
* `MeasureTheory.Measure.expFamilyPairCost_nonneg`, `MeasureTheory.Measure.expFamilyPairCost_pos`,
  `MeasureTheory.Measure.expFamilyPairCost_eq_zero`, `MeasureTheory.Measure.expFamilyPairCost_mul`:
  the cost of moving two means to their weighted mean is nonnegative, positive for distinct means
  and positive weights, zero when a weight vanishes, and homogeneous in the weights.
* `MeasureTheory.Measure.mul_eq_mul_of_expFamilyPairCost_midpoint_eq`: if that cost takes the
  same value at two pairs of weights and at their midpoint, then the two pairs are proportional.
* `MeasureTheory.Measure.continuousOn_expFamilyPairCost`: that cost is continuous in the means and
  the nonnegative weights.
-/

public section

open ProbabilityTheory InformationTheory Filter Set

open scoped Topology

namespace MeasureTheory.Measure

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {η μ μ' : ℝ}

/-! ### The set of means and the natural parameter of a mean -/

/-- The set of means of the exponential family of `ρ` and `T`: the means `ψ'(η)` of `T` under the
members `ρ.expFamily T η` with natural parameter `η` in the interior of `integrableExpSet T ρ`,
where `ψ = cgf T ρ`. It is an interval, open when `T` is not `ρ`-almost everywhere constant
(`convex_expFamilyMeans`, `isOpen_expFamilyMeans`), and empty if that interior is. -/
noncomputable def expFamilyMeans (ρ : Measure 𝓧) (T : 𝓧 → ℝ) : Set ℝ :=
  deriv (cgf T ρ) '' interior (integrableExpSet T ρ)

/-- The natural parameter `η(μ)` of the member of mean `μ` of the exponential family of `ρ` and
`T`: the inverse of the mean map `ψ' = deriv (cgf T ρ)` on the interior of
`integrableExpSet T ρ`. The member of mean `μ` is `ρ.expFamily T (ρ.natParam T μ)`. The value is
meaningful for `μ ∈ ρ.expFamilyMeans T` only. -/
noncomputable def natParam (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (μ : ℝ) : ℝ :=
  Function.invFunOn (deriv (cgf T ρ)) (interior (integrableExpSet T ρ)) μ

/-- The Kullback–Leibler divergence in the mean parametrization of the exponential family of `ρ`
and `T`: `d(μ, μ') = ψ(η(μ')) - ψ(η(μ)) - μ (η(μ') - η(μ))`, with `ψ = cgf T ρ` and `η(μ)` the
natural parameter of the mean `μ`. For means `μ, μ'` of the family it is
`KL(ρ_η(μ), ρ_η(μ'))` (`klDiv_expFamily_natParam`). -/
noncomputable def expFamilyDiv (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (μ μ' : ℝ) : ℝ :=
  cgf T ρ (ρ.natParam T μ') - cgf T ρ (ρ.natParam T μ) - μ * (ρ.natParam T μ' - ρ.natParam T μ)

lemma expFamilyMeans_def (ρ : Measure 𝓧) (T : 𝓧 → ℝ) :
    ρ.expFamilyMeans T = deriv (cgf T ρ) '' interior (integrableExpSet T ρ) := (rfl)

lemma natParam_def (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (μ : ℝ) :
    ρ.natParam T μ = Function.invFunOn (deriv (cgf T ρ)) (interior (integrableExpSet T ρ)) μ :=
  (rfl)

lemma expFamilyDiv_def (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (μ μ' : ℝ) :
    ρ.expFamilyDiv T μ μ' =
      cgf T ρ (ρ.natParam T μ') - cgf T ρ (ρ.natParam T μ) -
        μ * (ρ.natParam T μ' - ρ.natParam T μ) :=
  (rfl)

lemma mem_expFamilyMeans_iff :
    μ ∈ ρ.expFamilyMeans T ↔ ∃ η ∈ interior (integrableExpSet T ρ), deriv (cgf T ρ) η = μ :=
  Iff.rfl

lemma deriv_cgf_mem_expFamilyMeans (hη : η ∈ interior (integrableExpSet T ρ)) :
    deriv (cgf T ρ) η ∈ ρ.expFamilyMeans T :=
  mem_image_of_mem _ hη

lemma natParam_mem_interior_integrableExpSet (hμ : μ ∈ ρ.expFamilyMeans T) :
    ρ.natParam T μ ∈ interior (integrableExpSet T ρ) :=
  Function.invFunOn_mem hμ

/-- The mean map sends the natural parameter of a mean `μ` to `μ`. -/
@[simp]
lemma deriv_cgf_natParam (hμ : μ ∈ ρ.expFamilyMeans T) : deriv (cgf T ρ) (ρ.natParam T μ) = μ :=
  Function.invFunOn_eq hμ

/-- The statistic `T` has mean `μ` under the member `ρ_η(μ)` of the exponential family. -/
lemma integral_expFamily_natParam (hμ : μ ∈ ρ.expFamilyMeans T) :
    ∫ x, T x ∂(ρ.expFamily T (ρ.natParam T μ)) = μ := by
  rw [integral_expFamily (natParam_mem_interior_integrableExpSet hμ), deriv_cgf_natParam hμ]

/-- The means of an exponential family form a convex set. -/
lemma convex_expFamilyMeans : Convex ℝ (ρ.expFamilyMeans T) :=
  ((convex_integrableExpSet.interior.isPreconnected).image _
    analyticOnNhd_cgf.deriv.continuousOn).ordConnected.convex

/-- The interval between two means of an exponential family consists of means of the family. -/
lemma Icc_subset_expFamilyMeans (hμ' : μ' ∈ ρ.expFamilyMeans T) (hμ : μ ∈ ρ.expFamilyMeans T) :
    Icc μ' μ ⊆ ρ.expFamilyMeans T :=
  convex_expFamilyMeans.ordConnected.out hμ' hμ

/-- The natural parameter is monotone in the mean. It is strictly increasing when `T` is not
`ρ`-almost everywhere constant (`strictMonoOn_natParam`). -/
theorem monotoneOn_natParam : MonotoneOn (ρ.natParam T) (ρ.expFamilyMeans T) := by
  intro x hx y hy hxy
  by_contra! h
  have hyx := monotoneOn_deriv_cgf (natParam_mem_interior_integrableExpSet hy)
    (natParam_mem_interior_integrableExpSet hx) h.le
  rw [deriv_cgf_natParam hx, deriv_cgf_natParam hy] at hyx
  exact h.ne (congrArg (ρ.natParam T) (le_antisymm hyx hxy))

/-- The natural parameter of the mean `ψ'(η)` is `η`. -/
@[simp]
lemma natParam_deriv_cgf (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hη : η ∈ interior (integrableExpSet T ρ)) :
    ρ.natParam T (deriv (cgf T ρ) η) = η :=
  (strictMonoOn_deriv_cgf hT).injOn.leftInvOn_invFunOn hη

lemma image_natParam (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) :
    ρ.natParam T '' ρ.expFamilyMeans T = interior (integrableExpSet T ρ) := by
  refine MapsTo.image_subset (fun _ hμ ↦ natParam_mem_interior_integrableExpSet hμ) |>.antisymm
    fun η hη ↦ ?_
  exact ⟨_, deriv_cgf_mem_expFamilyMeans hη, natParam_deriv_cgf hT hη⟩

/-- The means of the exponential family of `ρ` and a statistic `T` which is not `ρ`-almost
everywhere constant form an open set. -/
theorem isOpen_expFamilyMeans (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) : IsOpen (ρ.expFamilyMeans T) := by
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨η, hη, rfl⟩
  rw [← (hasStrictDerivAt_deriv_cgf hη).map_nhds_eq (iteratedDeriv_two_cgf_pos hT hη).ne']
  exact image_mem_map (isOpen_interior.mem_nhds hη)

lemma expFamilyMeans_mem_nhds (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hμ : μ ∈ ρ.expFamilyMeans T) :
    ρ.expFamilyMeans T ∈ 𝓝 μ :=
  (isOpen_expFamilyMeans hT).mem_nhds hμ

/-- The natural parameter is strictly increasing in the mean. -/
theorem strictMonoOn_natParam (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) :
    StrictMonoOn (ρ.natParam T) (ρ.expFamilyMeans T) := fun x hx y hy hxy ↦ by
  rwa [← (strictMonoOn_deriv_cgf hT).lt_iff_lt (natParam_mem_interior_integrableExpSet hx)
    (natParam_mem_interior_integrableExpSet hy), deriv_cgf_natParam hx, deriv_cgf_natParam hy]

lemma continuousOn_natParam (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) :
    ContinuousOn (ρ.natParam T) (ρ.expFamilyMeans T) := fun μ hμ ↦ by
  refine ((strictMonoOn_natParam hT).continuousAt_of_image_mem_nhds
    (expFamilyMeans_mem_nhds hT hμ) ?_).continuousWithinAt
  rw [image_natParam hT]
  exact isOpen_interior.mem_nhds (natParam_mem_interior_integrableExpSet hμ)

/-- The natural parameter is differentiable in the mean, with derivative `1 / ψ''(η(μ))`, the
inverse of the variance of `T` under the member of mean `μ`. -/
theorem hasDerivAt_natParam (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hμ : μ ∈ ρ.expFamilyMeans T) :
    HasDerivAt (ρ.natParam T) (iteratedDeriv 2 (cgf T ρ) (ρ.natParam T μ))⁻¹ μ :=
  (hasStrictDerivAt_deriv_cgf (natParam_mem_interior_integrableExpSet hμ)).hasDerivAt
    |>.of_local_left_inverse
    ((continuousOn_natParam hT).continuousAt (expFamilyMeans_mem_nhds hT hμ))
    (iteratedDeriv_two_cgf_pos hT (natParam_mem_interior_integrableExpSet hμ)).ne'
    (eventually_of_mem (expFamilyMeans_mem_nhds hT hμ) fun _ ↦ deriv_cgf_natParam)

/-- The log-partition function at the natural parameter of the mean `x` has derivative
`μ / ψ''(η(μ))` in `x` at `μ`. -/
private lemma hasDerivAt_cgf_natParam (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : μ ∈ ρ.expFamilyMeans T) :
    HasDerivAt (fun x ↦ cgf T ρ (ρ.natParam T x))
      (μ * (iteratedDeriv 2 (cgf T ρ) (ρ.natParam T μ))⁻¹) μ := by
  have h :=
    (analyticOnNhd_cgf _ (natParam_mem_interior_integrableExpSet hμ)).differentiableAt.hasDerivAt
  rw [deriv_cgf_natParam hμ] at h
  exact h.comp μ (hasDerivAt_natParam hT hμ)

/-! ### The divergence in the mean parametrization -/

@[simp]
lemma expFamilyDiv_self (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (μ : ℝ) : ρ.expFamilyDiv T μ μ = 0 := by
  simp [expFamilyDiv_def]

/-- The Kullback–Leibler divergence between the members of means `μ` and `μ'` of an exponential
family, as a real number, is `d(μ, μ')`. -/
theorem toReal_klDiv_expFamily_natParam (hμ : μ ∈ ρ.expFamilyMeans T)
    (hμ' : μ' ∈ ρ.expFamilyMeans T) :
    (klDiv (ρ.expFamily T (ρ.natParam T μ)) (ρ.expFamily T (ρ.natParam T μ'))).toReal =
      ρ.expFamilyDiv T μ μ' := by
  rw [toReal_klDiv_expFamily (natParam_mem_interior_integrableExpSet hμ)
    (interior_subset (natParam_mem_interior_integrableExpSet hμ')), deriv_cgf_natParam hμ,
    expFamilyDiv_def]

/-- **Kullback–Leibler divergence in the mean parametrization.** The divergence between the
members of means `μ` and `μ'` of an exponential family is
`d(μ, μ') = ψ(η(μ')) - ψ(η(μ)) - μ (η(μ') - η(μ))`. -/
theorem klDiv_expFamily_natParam (hμ : μ ∈ ρ.expFamilyMeans T)
    (hμ' : μ' ∈ ρ.expFamilyMeans T) :
    klDiv (ρ.expFamily T (ρ.natParam T μ)) (ρ.expFamily T (ρ.natParam T μ')) =
      ENNReal.ofReal (ρ.expFamilyDiv T μ μ') := by
  rw [klDiv_expFamily (natParam_mem_interior_integrableExpSet hμ)
    (interior_subset (natParam_mem_interior_integrableExpSet hμ')),
    deriv_cgf_natParam hμ, expFamilyDiv_def]

lemma expFamilyDiv_nonneg (hμ : μ ∈ ρ.expFamilyMeans T) (hμ' : μ' ∈ ρ.expFamilyMeans T) :
    0 ≤ ρ.expFamilyDiv T μ μ' := by
  rw [← toReal_klDiv_expFamily_natParam hμ hμ']
  exact ENNReal.toReal_nonneg

/-- The divergence `d(μ, μ')` between two means of the family vanishes iff `μ = μ'`. -/
theorem expFamilyDiv_eq_zero_iff (hμ : μ ∈ ρ.expFamilyMeans T)
    (hμ' : μ' ∈ ρ.expFamilyMeans T) : ρ.expFamilyDiv T μ μ' = 0 ↔ μ = μ' := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ expFamilyDiv_self ρ T μ⟩
  have h_eq : ρ.expFamily T (ρ.natParam T μ) = ρ.expFamily T (ρ.natParam T μ') := by
    rw [← klDiv_eq_zero_iff, klDiv_expFamily_natParam hμ hμ', h, ENNReal.ofReal_zero]
  rw [← integral_expFamily_natParam hμ, ← integral_expFamily_natParam hμ', h_eq]

lemma expFamilyDiv_pos (hμ : μ ∈ ρ.expFamilyMeans T) (hμ' : μ' ∈ ρ.expFamilyMeans T)
    (h : μ ≠ μ') : 0 < ρ.expFamilyDiv T μ μ' :=
  (expFamilyDiv_nonneg hμ hμ').lt_of_ne' fun h0 ↦ h ((expFamilyDiv_eq_zero_iff hμ hμ').1 h0)

/-- The divergence `d(μ, μ')` is continuous on the pairs of means. -/
theorem continuousOn_expFamilyDiv (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) :
    ContinuousOn (fun p : ℝ × ℝ ↦ ρ.expFamilyDiv T p.1 p.2)
      (ρ.expFamilyMeans T ×ˢ ρ.expFamilyMeans T) := by
  have hη := continuousOn_natParam hT
  have hψ : ContinuousOn (fun x ↦ cgf T ρ (ρ.natParam T x)) (ρ.expFamilyMeans T) :=
    analyticOnNhd_cgf.continuousOn.comp hη fun _ hx ↦ natParam_mem_interior_integrableExpSet hx
  have h₁ : MapsTo Prod.fst (ρ.expFamilyMeans T ×ˢ ρ.expFamilyMeans T) (ρ.expFamilyMeans T) :=
    fun _ hp ↦ hp.1
  have h₂ : MapsTo Prod.snd (ρ.expFamilyMeans T ×ˢ ρ.expFamilyMeans T) (ρ.expFamilyMeans T) :=
    fun _ hp ↦ hp.2
  simp_rw [expFamilyDiv_def]
  exact ((hψ.comp continuousOn_snd h₂).sub (hψ.comp continuousOn_fst h₁)).sub
    (continuousOn_fst.mul ((hη.comp continuousOn_snd h₂).sub (hη.comp continuousOn_fst h₁)))

/-- The derivative of `x ↦ d(x, μ')` at a mean `μ` is `η(μ) - η(μ')`. -/
theorem hasDerivAt_expFamilyDiv_left (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hμ : μ ∈ ρ.expFamilyMeans T)
    (μ' : ℝ) :
    HasDerivAt (fun x ↦ ρ.expFamilyDiv T x μ') (ρ.natParam T μ - ρ.natParam T μ') μ := by
  have h := ((hasDerivAt_const μ (cgf T ρ (ρ.natParam T μ'))).sub
    (hasDerivAt_cgf_natParam hT hμ)).sub
    ((hasDerivAt_id' μ).mul
      ((hasDerivAt_const μ (ρ.natParam T μ')).sub (hasDerivAt_natParam hT hμ)))
  simp_rw [expFamilyDiv_def]
  convert h using 1
  simp only [Pi.sub_apply]
  ring

/-- The derivative of `y ↦ d(μ, y)` at a mean `μ'` is `(μ' - μ) / ψ''(η(μ'))`. -/
theorem hasDerivAt_expFamilyDiv_right (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (μ : ℝ)
    (hμ' : μ' ∈ ρ.expFamilyMeans T) :
    HasDerivAt (fun y ↦ ρ.expFamilyDiv T μ y)
      ((μ' - μ) / iteratedDeriv 2 (cgf T ρ) (ρ.natParam T μ')) μ' := by
  have h := ((hasDerivAt_cgf_natParam hT hμ').sub
    (hasDerivAt_const μ' (cgf T ρ (ρ.natParam T μ)))).sub
    (((hasDerivAt_natParam hT hμ').sub (hasDerivAt_const μ' (ρ.natParam T μ))).const_mul μ)
  simp_rw [expFamilyDiv_def]
  convert h using 1
  ring

/-- The divergence `d(μ, μ')` is strictly convex in its first argument `μ` on the means of the
family. -/
theorem strictConvexOn_expFamilyDiv_left (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (μ' : ℝ) :
    StrictConvexOn ℝ (ρ.expFamilyMeans T) fun x ↦ ρ.expFamilyDiv T x μ' := by
  refine StrictMonoOn.strictConvexOn_of_deriv convex_expFamilyMeans
    (fun x hx ↦ (hasDerivAt_expFamilyDiv_left hT hx μ').continuousAt.continuousWithinAt) ?_
  rw [(isOpen_expFamilyMeans hT).interior_eq]
  intro x hx y hy hxy
  rw [(hasDerivAt_expFamilyDiv_left hT hx μ').deriv,
    (hasDerivAt_expFamilyDiv_left hT hy μ').deriv]
  exact sub_lt_sub_right (strictMonoOn_natParam hT hx hy hxy) _

/-- The divergence `d(μ, μ')` is strictly decreasing in `μ` for `μ ≤ μ'`. -/
theorem strictAntiOn_expFamilyDiv_left (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ' : μ' ∈ ρ.expFamilyMeans T) :
    StrictAntiOn (fun x ↦ ρ.expFamilyDiv T x μ') (ρ.expFamilyMeans T ∩ Iic μ') := by
  refine strictAntiOn_of_deriv_neg (convex_expFamilyMeans.inter (convex_Iic μ'))
    (fun x hx ↦ (hasDerivAt_expFamilyDiv_left hT hx.1 μ').continuousAt.continuousWithinAt)
    fun x hx ↦ ?_
  rw [interior_inter, (isOpen_expFamilyMeans hT).interior_eq, interior_Iic] at hx
  rw [(hasDerivAt_expFamilyDiv_left hT hx.1 μ').deriv, sub_neg]
  exact strictMonoOn_natParam hT hx.1 hμ' hx.2

/-- The divergence `d(μ, μ')` is strictly increasing in `μ` for `μ' ≤ μ`. -/
theorem strictMonoOn_expFamilyDiv_left (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ' : μ' ∈ ρ.expFamilyMeans T) :
    StrictMonoOn (fun x ↦ ρ.expFamilyDiv T x μ') (ρ.expFamilyMeans T ∩ Ici μ') := by
  refine strictMonoOn_of_deriv_pos (convex_expFamilyMeans.inter (convex_Ici μ'))
    (fun x hx ↦ (hasDerivAt_expFamilyDiv_left hT hx.1 μ').continuousAt.continuousWithinAt)
    fun x hx ↦ ?_
  rw [interior_inter, (isOpen_expFamilyMeans hT).interior_eq, interior_Ici] at hx
  rw [(hasDerivAt_expFamilyDiv_left hT hx.1 μ').deriv, sub_pos]
  exact strictMonoOn_natParam hT hμ' hx.1 hx.2

/-- The divergence `d(μ, μ')` is strictly decreasing in `μ'` for `μ' ≤ μ`. -/
theorem strictAntiOn_expFamilyDiv_right (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (μ : ℝ) :
    StrictAntiOn (fun y ↦ ρ.expFamilyDiv T μ y) (ρ.expFamilyMeans T ∩ Iic μ) := by
  refine strictAntiOn_of_deriv_neg (convex_expFamilyMeans.inter (convex_Iic μ))
    (fun y hy ↦ (hasDerivAt_expFamilyDiv_right hT μ hy.1).continuousAt.continuousWithinAt)
    fun y hy ↦ ?_
  rw [interior_inter, (isOpen_expFamilyMeans hT).interior_eq, interior_Iic] at hy
  rw [(hasDerivAt_expFamilyDiv_right hT μ hy.1).deriv]
  exact div_neg_of_neg_of_pos (sub_neg.2 hy.2)
    (iteratedDeriv_two_cgf_pos hT (natParam_mem_interior_integrableExpSet hy.1))

/-- The divergence `d(μ, μ')` is strictly increasing in `μ'` for `μ ≤ μ'`. -/
theorem strictMonoOn_expFamilyDiv_right (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (μ : ℝ) :
    StrictMonoOn (fun y ↦ ρ.expFamilyDiv T μ y) (ρ.expFamilyMeans T ∩ Ici μ) := by
  refine strictMonoOn_of_deriv_pos (convex_expFamilyMeans.inter (convex_Ici μ))
    (fun y hy ↦ (hasDerivAt_expFamilyDiv_right hT μ hy.1).continuousAt.continuousWithinAt)
    fun y hy ↦ ?_
  rw [interior_inter, (isOpen_expFamilyMeans hT).interior_eq, interior_Ici] at hy
  rw [(hasDerivAt_expFamilyDiv_right hT μ hy.1).deriv]
  exact div_pos (sub_pos.2 hy.2)
    (iteratedDeriv_two_cgf_pos hT (natParam_mem_interior_integrableExpSet hy.1))

/-- Between two means `μ' ≤ μ` of the family there is a mean `z` at the same divergence from both,
`d(μ, z) = d(μ', z)`: the divergence `d(μ, ·) - d(μ', ·)` is continuous, nonnegative at `μ'` and
nonpositive at `μ`. -/
theorem exists_mem_Icc_expFamilyDiv_eq (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : μ ∈ ρ.expFamilyMeans T) (hμ' : μ' ∈ ρ.expFamilyMeans T) (h : μ' ≤ μ) :
    ∃ z ∈ Icc μ' μ, ρ.expFamilyDiv T μ z = ρ.expFamilyDiv T μ' z := by
  have h_sub := Icc_subset_expFamilyMeans hμ' hμ
  have h_cont (x : ℝ) (hx : x ∈ ρ.expFamilyMeans T) :
      ContinuousOn (fun z ↦ ρ.expFamilyDiv T x z) (Icc μ' μ) :=
    (continuousOn_expFamilyDiv hT).comp (continuousOn_const.prodMk continuousOn_id)
      fun z hz ↦ ⟨hx, h_sub hz⟩
  have h0 : (0 : ℝ) ∈ Icc (ρ.expFamilyDiv T μ μ - ρ.expFamilyDiv T μ' μ)
      (ρ.expFamilyDiv T μ μ' - ρ.expFamilyDiv T μ' μ') := by
    rw [expFamilyDiv_self, expFamilyDiv_self, zero_sub, sub_zero]
    exact ⟨neg_nonpos.2 (expFamilyDiv_nonneg hμ' hμ), expFamilyDiv_nonneg hμ hμ'⟩
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' h ((h_cont μ hμ).sub (h_cont μ' hμ')) h0
  exact ⟨z, hz, sub_eq_zero.1 hz0⟩

/-! ### Comparison with the Gaussian divergence -/

/-- The derivative of `x ↦ d(x, μ') - (x - μ')² / (2 v)` at a mean `μ` is
`η(μ) - η(μ') - (μ - μ') / v`. -/
private lemma hasDerivAt_expFamilyDiv_sub_sq_div (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : μ ∈ ρ.expFamilyMeans T) (v : ℝ) :
    HasDerivAt (fun x ↦ ρ.expFamilyDiv T x μ' - (x - μ') ^ 2 / (2 * v))
      (ρ.natParam T μ - ρ.natParam T μ' - (μ - μ') / v) μ := by
  convert (hasDerivAt_expFamilyDiv_left hT hμ μ').sub
    ((((hasDerivAt_id' μ).sub_const μ').pow 2).div_const (2 * v)) using 1
  field_simp
  ring

/-- The function `x ↦ η(x) - η(μ') - (x - μ') / v` is monotone on an interval `[a, b]` of means
when `T` has variance at most `v` under the members whose mean lies in `(a, b)`: its derivative is
`1 / ψ''(η(x)) - 1 / v`. -/
private lemma monotoneOn_natParam_sub_div (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) {a b v : ℝ}
    (hab : Icc a b ⊆ ρ.expFamilyMeans T)
    (hv : ∀ x ∈ Ioo a b, Var[T; ρ.expFamily T (ρ.natParam T x)] ≤ v) (μ' : ℝ) :
    MonotoneOn (fun x ↦ ρ.natParam T x - ρ.natParam T μ' - (x - μ') / v) (Icc a b) := by
  have h_deriv (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun x ↦ ρ.natParam T x - ρ.natParam T μ' - (x - μ') / v)
        ((iteratedDeriv 2 (cgf T ρ) (ρ.natParam T x))⁻¹ - 1 / v) x := by
    convert ((hasDerivAt_natParam hT (hab hx)).sub_const (ρ.natParam T μ')).sub
      (((hasDerivAt_id' x).sub_const μ').div_const v) using 1
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun x hx ↦ (h_deriv x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (h_deriv x (interior_subset hx)).hasDerivWithinAt) fun x hx ↦ ?_
  rw [interior_Icc] at hx
  have hη := natParam_mem_interior_integrableExpSet (hab (Ioo_subset_Icc_self hx))
  have h_le := hv x hx
  rw [variance_expFamily hη] at h_le
  rw [sub_nonneg, one_div]
  exact inv_anti₀ (iteratedDeriv_two_cgf_pos hT hη) h_le

/-- **Sub-Gaussian comparison.** If `T` has variance at most `v` under the members of the family
whose mean lies strictly between `μ` and `μ'`, then `d(μ, μ') ≥ (μ - μ')² / (2 v)`, the divergence
between the Gaussian laws of means `μ` and `μ'` and variance `v`. -/
theorem sq_div_le_expFamilyDiv (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hμ : μ ∈ ρ.expFamilyMeans T)
    (hμ' : μ' ∈ ρ.expFamilyMeans T) {v : ℝ}
    (hv : ∀ x ∈ uIoo μ μ', Var[T; ρ.expFamily T (ρ.natParam T x)] ≤ v) :
    (μ - μ') ^ 2 / (2 * v) ≤ ρ.expFamilyDiv T μ μ' := by
  rcases le_or_gt v 0 with hv0 | hv0
  · exact (div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)).trans
      (expFamilyDiv_nonneg hμ hμ')
  -- `F x = d(x, μ') - (x - μ')² / (2 v)` vanishes at `μ'`, and its derivative `g` is monotone
  -- with `g μ' = 0`, so `F` is monotone above `μ'` and antitone below `μ'`
  set F := fun x ↦ ρ.expFamilyDiv T x μ' - (x - μ') ^ 2 / (2 * v)
  have hF (x : ℝ) (hx : x ∈ ρ.expFamilyMeans T) :=
    hasDerivAt_expFamilyDiv_sub_sq_div (μ' := μ') hT hx v
  suffices F μ' ≤ F μ by simp [F] at this; linarith
  have h_means := convex_expFamilyMeans (ρ := ρ) (T := T) |>.ordConnected
  rcases le_total μ' μ with h | h
  · rw [uIoo_of_ge h] at hv
    have hg := monotoneOn_natParam_sub_div hT (h_means.out hμ' hμ) hv μ'
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc μ' μ)
      (fun x hx ↦ (hF x (h_means.out hμ' hμ hx)).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hF x (h_means.out hμ' hμ (interior_subset hx))).hasDerivWithinAt)
      (fun x hx ↦ ?_) (left_mem_Icc.2 h) (right_mem_Icc.2 h) h
    rw [interior_Icc] at hx
    simpa using hg (left_mem_Icc.2 h) (Ioo_subset_Icc_self hx) hx.1.le
  · rw [uIoo_of_le h] at hv
    have hg := monotoneOn_natParam_sub_div hT (h_means.out hμ hμ') hv μ'
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc μ μ')
      (fun x hx ↦ (hF x (h_means.out hμ hμ' hx)).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hF x (h_means.out hμ hμ' (interior_subset hx))).hasDerivWithinAt)
      (fun x hx ↦ ?_) (left_mem_Icc.2 h) (right_mem_Icc.2 h) h
    rw [interior_Icc] at hx
    simpa using hg (Ioo_subset_Icc_self hx) (right_mem_Icc.2 h) hx.2.le

/-- **Sub-Gaussian comparison** for the Kullback–Leibler divergence: if `T` has variance at most
`v` under the members of the family whose mean lies strictly between `μ` and `μ'`, then the
divergence between the members of means `μ` and `μ'` is at least `(μ - μ')² / (2 v)`. -/
theorem ofReal_sq_div_le_klDiv_expFamily_natParam (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hμ : μ ∈ ρ.expFamilyMeans T) (hμ' : μ' ∈ ρ.expFamilyMeans T) {v : ℝ}
    (hv : ∀ x ∈ uIoo μ μ', Var[T; ρ.expFamily T (ρ.natParam T x)] ≤ v) :
    ENNReal.ofReal ((μ - μ') ^ 2 / (2 * v)) ≤
      klDiv (ρ.expFamily T (ρ.natParam T μ)) (ρ.expFamily T (ρ.natParam T μ')) := by
  rw [klDiv_expFamily_natParam hμ hμ']
  exact ENNReal.ofReal_le_ofReal (sq_div_le_expFamilyDiv hT hμ hμ' hv)

/-! ### Weighted divergences and weighted means -/

/-- **Compensation identity.** If `m` is the mean of the `μ i`, `i ∈ s`, weighted by `w`, that is
`(∑ i ∈ s, w i) * m = ∑ i ∈ s, w i * μ i`, then for every `z` the weighted divergence
`∑ i ∈ s, w i d(μ i, z)` is the weighted divergence to `m` plus `(∑ i ∈ s, w i) d(m, z)`. -/
lemma sum_mul_expFamilyDiv_eq {ι : Type*} (s : Finset ι) (w μ : ι → ℝ) {m : ℝ}
    (hm : (∑ i ∈ s, w i) * m = ∑ i ∈ s, w i * μ i) (z : ℝ) :
    ∑ i ∈ s, w i * ρ.expFamilyDiv T (μ i) z =
      ∑ i ∈ s, w i * ρ.expFamilyDiv T (μ i) m + (∑ i ∈ s, w i) * ρ.expFamilyDiv T m z := by
  have h (i : ι) : w i * ρ.expFamilyDiv T (μ i) z = w i * ρ.expFamilyDiv T (μ i) m +
      w i * (cgf T ρ (ρ.natParam T z) - cgf T ρ (ρ.natParam T m)) -
        w i * μ i * (ρ.natParam T z - ρ.natParam T m) := by
    simp only [expFamilyDiv_def]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ h i, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← hm, expFamilyDiv_def]
  ring

/-- The weighted mean `m` of the `μ i`, `i ∈ s`, minimizes the weighted divergence
`z ↦ ∑ i ∈ s, w i d(μ i, z)` over the means of the family, for nonnegative weights. -/
theorem sum_mul_expFamilyDiv_le {ι : Type*} (s : Finset ι) {w μ : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) {m z : ℝ} (hm : (∑ i ∈ s, w i) * m = ∑ i ∈ s, w i * μ i)
    (hm_mem : m ∈ ρ.expFamilyMeans T) (hz : z ∈ ρ.expFamilyMeans T) :
    ∑ i ∈ s, w i * ρ.expFamilyDiv T (μ i) m ≤ ∑ i ∈ s, w i * ρ.expFamilyDiv T (μ i) z := by
  rw [sum_mul_expFamilyDiv_eq s w μ hm z]
  exact le_add_of_nonneg_right (mul_nonneg (Finset.sum_nonneg hw) (expFamilyDiv_nonneg hm_mem hz))

/-- The mean `(w₁ μ₁ + w₂ μ₂) / (w₁ + w₂)` of two means of the family, weighted by nonnegative
weights with `w₁ + w₂ > 0`, is a mean of the family. -/
lemma div_mem_expFamilyMeans {μ₁ μ₂ w₁ w₂ : ℝ} (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T)
    (hμ₂ : μ₂ ∈ ρ.expFamilyMeans T) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hW : 0 < w₁ + w₂) :
    (w₁ * μ₁ + w₂ * μ₂) / (w₁ + w₂) ∈ ρ.expFamilyMeans T := by
  convert convex_iff_div.mp convex_expFamilyMeans hμ₁ hμ₂ hw₁ hw₂ hW using 1
  simp only [smul_eq_mul]
  ring

/-- For two points with nonnegative weights `w₁, w₂`, a weighted mean `m` of `μ₁` and `μ₂`, that
is `(w₁ + w₂) m = w₁ μ₁ + w₂ μ₂`, minimizes `z ↦ w₁ d(μ₁, z) + w₂ d(μ₂, z)` over the means of the
family. -/
theorem mul_expFamilyDiv_add_mul_expFamilyDiv_le_of_mul_eq {μ₁ μ₂ w₁ w₂ m z : ℝ} (hw₁ : 0 ≤ w₁)
    (hw₂ : 0 ≤ w₂) (hm : (w₁ + w₂) * m = w₁ * μ₁ + w₂ * μ₂) (hm_mem : m ∈ ρ.expFamilyMeans T)
    (hz : z ∈ ρ.expFamilyMeans T) :
    w₁ * ρ.expFamilyDiv T μ₁ m + w₂ * ρ.expFamilyDiv T μ₂ m ≤
      w₁ * ρ.expFamilyDiv T μ₁ z + w₂ * ρ.expFamilyDiv T μ₂ z := by
  have h := sum_mul_expFamilyDiv_le (ρ := ρ) (T := T) Finset.univ (w := ![w₁, w₂])
    (μ := ![μ₁, μ₂]) (Fin.forall_fin_two.mpr ⟨fun _ ↦ hw₁, fun _ ↦ hw₂⟩)
    (by rw [Fin.sum_univ_two, Fin.sum_univ_two]; exact hm) hm_mem hz
  rwa [Fin.sum_univ_two, Fin.sum_univ_two] at h

/-- The cost `w₁ d(μ₁, m) + w₂ d(μ₂, m)` of moving two means `μ₁` and `μ₂` to their mean
`m = (w₁ μ₁ + w₂ μ₂) / (w₁ + w₂)` weighted by `w₁` and `w₂`. For nonnegative weights, it is the
minimum over the means `z` of `w₁ d(μ₁, z) + w₂ d(μ₂, z)`
(`mul_expFamilyDiv_add_mul_expFamilyDiv_le_of_mul_eq`); in best arm identification, it is the cost
of the alternatives in which the arm of mean `μ₂` beats the arm of mean `μ₁`. -/
noncomputable def expFamilyPairCost (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (μ₁ μ₂ w₁ w₂ : ℝ) : ℝ :=
  w₁ * ρ.expFamilyDiv T μ₁ ((w₁ * μ₁ + w₂ * μ₂) / (w₁ + w₂)) +
    w₂ * ρ.expFamilyDiv T μ₂ ((w₁ * μ₁ + w₂ * μ₂) / (w₁ + w₂))

lemma expFamilyPairCost_def (ρ : Measure 𝓧) (T : 𝓧 → ℝ) (μ₁ μ₂ w₁ w₂ : ℝ) :
    ρ.expFamilyPairCost T μ₁ μ₂ w₁ w₂ =
      w₁ * ρ.expFamilyDiv T μ₁ ((w₁ * μ₁ + w₂ * μ₂) / (w₁ + w₂)) +
        w₂ * ρ.expFamilyDiv T μ₂ ((w₁ * μ₁ + w₂ * μ₂) / (w₁ + w₂)) :=
  (rfl)

/-- For means `μ₂ ≤ μ₁` and nonnegative weights `w₁, w₂`, the weighted divergence
`w₁ d(μ₁, x) + w₂ d(μ₂, y)` at a pair of means `x ≤ y` is at least its value
`expFamilyPairCost ρ T μ₁ μ₂ w₁ w₂` at `x = y = m`, where `m = (w₁ μ₁ + w₂ μ₂) / (w₁ + w₂)` is the
mean of `μ₁` and `μ₂` weighted by `w₁` and `w₂`. When
`w₁ + w₂ > 0`, `m` is a mean of the family, so this value is the minimum over these pairs. -/
theorem expFamilyPairCost_le_mul_expFamilyDiv_add_mul_expFamilyDiv
    (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) {μ₁ μ₂ w₁ w₂ x y : ℝ} (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T)
    (hμ₂ : μ₂ ∈ ρ.expFamilyMeans T) (hμ₂₁ : μ₂ ≤ μ₁) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hx : x ∈ ρ.expFamilyMeans T) (hy : y ∈ ρ.expFamilyMeans T) (hxy : x ≤ y) :
    ρ.expFamilyPairCost T μ₁ μ₂ w₁ w₂ ≤
      w₁ * ρ.expFamilyDiv T μ₁ x + w₂ * ρ.expFamilyDiv T μ₂ y := by
  rw [expFamilyPairCost_def]
  set m := (w₁ * μ₁ + w₂ * μ₂) / (w₁ + w₂) with hm_def
  rcases (add_nonneg hw₁ hw₂).eq_or_lt with hW | hW
  · obtain ⟨rfl, rfl⟩ : w₁ = 0 ∧ w₂ = 0 := ⟨by linarith, by linarith⟩
    simp
  -- The weighted mean `m` lies between `μ₂` and `μ₁` and is a mean of the family.
  have hm₂ : μ₂ ≤ m := by rw [hm_def, le_div_iff₀ hW]; nlinarith
  have hm₁ : m ≤ μ₁ := by rw [hm_def, div_le_iff₀ hW]; nlinarith
  have hm_mem : m ∈ ρ.expFamilyMeans T := div_mem_expFamilyMeans hμ₁ hμ₂ hw₁ hw₂ hW
  -- It minimizes `z ↦ w₁ d(μ₁, z) + w₂ d(μ₂, z)`.
  have hm : (w₁ + w₂) * m = w₁ * μ₁ + w₂ * μ₂ := by rw [hm_def]; field_simp
  have h_min (z : ℝ) (hz : z ∈ ρ.expFamilyMeans T) :=
    mul_expFamilyDiv_add_mul_expFamilyDiv_le_of_mul_eq hw₁ hw₂ hm hm_mem hz
  -- Move `x` and `y` towards `m` without increasing their divergences: `d(μ₁, ·)` is antitone
  -- below `μ₁` and `d(μ₂, ·)` is monotone above `μ₂`.
  have h_anti := (strictAntiOn_expFamilyDiv_right hT μ₁).antitoneOn
  have h_mono := (strictMonoOn_expFamilyDiv_right hT μ₂).monotoneOn
  rcases le_total m x with hmx | hxm
  · refine (h_min x hx).trans (add_le_add_right (mul_le_mul_of_nonneg_left ?_ hw₂) _)
    exact h_mono ⟨hx, hm₂.trans hmx⟩ ⟨hy, (hm₂.trans hmx).trans hxy⟩ hxy
  rcases le_total y m with hym | hmy
  · refine (h_min y hy).trans (add_le_add_left (mul_le_mul_of_nonneg_left ?_ hw₁) _)
    exact h_anti ⟨hx, (hxy.trans hym).trans hm₁⟩ ⟨hy, hym.trans hm₁⟩ hxy
  exact add_le_add
    (mul_le_mul_of_nonneg_left (h_anti ⟨hx, hxm.trans hm₁⟩ ⟨hm_mem, hm₁⟩ hxm) hw₁)
    (mul_le_mul_of_nonneg_left (h_mono ⟨hm_mem, hm₂⟩ ⟨hy, hm₂.trans hmy⟩ hmy) hw₂)

lemma expFamilyPairCost_nonneg {μ₁ μ₂ w₁ w₂ : ℝ} (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T)
    (hμ₂ : μ₂ ∈ ρ.expFamilyMeans T) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) :
    0 ≤ ρ.expFamilyPairCost T μ₁ μ₂ w₁ w₂ := by
  rcases (add_nonneg hw₁ hw₂).eq_or_lt with hW | hW
  · obtain ⟨rfl, rfl⟩ : w₁ = 0 ∧ w₂ = 0 := ⟨by linarith, by linarith⟩
    simp [expFamilyPairCost_def]
  have hm := div_mem_expFamilyMeans hμ₁ hμ₂ hw₁ hw₂ hW
  exact add_nonneg (mul_nonneg hw₁ (expFamilyDiv_nonneg hμ₁ hm))
    (mul_nonneg hw₂ (expFamilyDiv_nonneg hμ₂ hm))

/-- The cost of moving two means to their weighted mean vanishes when one of the weights does. -/
lemma expFamilyPairCost_eq_zero {μ₁ μ₂ w₁ w₂ : ℝ} (h : w₁ = 0 ∨ w₂ = 0) :
    ρ.expFamilyPairCost T μ₁ μ₂ w₁ w₂ = 0 := by
  rcases h with rfl | rfl
  · rcases eq_or_ne w₂ 0 with rfl | h <;> simp [expFamilyPairCost_def, *, expFamilyDiv_self]
  · rcases eq_or_ne w₁ 0 with rfl | h <;> simp [expFamilyPairCost_def, *, expFamilyDiv_self]

/-- The cost of moving two distinct means to their mean weighted by positive weights is
positive. -/
lemma expFamilyPairCost_pos {μ₁ μ₂ w₁ w₂ : ℝ} (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T)
    (hμ₂ : μ₂ ∈ ρ.expFamilyMeans T) (hμ : μ₁ ≠ μ₂) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) :
    0 < ρ.expFamilyPairCost T μ₁ μ₂ w₁ w₂ := by
  have hW := add_pos hw₁ hw₂
  have hm := div_mem_expFamilyMeans hμ₁ hμ₂ hw₁.le hw₂.le hW
  -- The weighted mean differs from `μ₁`, since `w₁ μ₁ + w₂ μ₂ - (w₁ + w₂) μ₁ = w₂ (μ₂ - μ₁)`.
  have hne : μ₁ ≠ (w₁ * μ₁ + w₂ * μ₂) / (w₁ + w₂) := by
    rw [Ne, eq_div_iff hW.ne']
    intro h
    exact mul_ne_zero hw₂.ne' (sub_ne_zero.2 hμ.symm) (by linear_combination -h)
  exact add_pos_of_pos_of_nonneg (mul_pos hw₁ (expFamilyDiv_pos hμ₁ hm hne))
    (mul_nonneg hw₂.le (expFamilyDiv_nonneg hμ₂ hm))

/-- The cost of moving two means to their weighted mean is homogeneous in the weights. -/
lemma expFamilyPairCost_mul {μ₁ μ₂ w₁ w₂ t : ℝ} :
    ρ.expFamilyPairCost T μ₁ μ₂ (t * w₁) (t * w₂) = t * ρ.expFamilyPairCost T μ₁ μ₂ w₁ w₂ := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [expFamilyPairCost_def]
  have hm : (t * w₁ * μ₁ + t * w₂ * μ₂) / (t * w₁ + t * w₂) =
      (w₁ * μ₁ + w₂ * μ₂) / (w₁ + w₂) := by
    rw [← mul_div_mul_left (w₁ * μ₁ + w₂ * μ₂) (w₁ + w₂) ht]
    congr 1 <;> ring
  simp only [expFamilyPairCost_def, hm]
  ring

/-- **Compensation identity** for two means: `w₁ d(μ₁, z) + w₂ d(μ₂, z)` is the cost of moving
`μ₁` and `μ₂` to their weighted mean `m` plus `(w₁ + w₂) d(m, z)`. -/
lemma mul_expFamilyDiv_add_mul_expFamilyDiv_eq {μ₁ μ₂ w₁ w₂ : ℝ} (hW : w₁ + w₂ ≠ 0) (z : ℝ) :
    w₁ * ρ.expFamilyDiv T μ₁ z + w₂ * ρ.expFamilyDiv T μ₂ z =
      ρ.expFamilyPairCost T μ₁ μ₂ w₁ w₂ +
        (w₁ + w₂) * ρ.expFamilyDiv T ((w₁ * μ₁ + w₂ * μ₂) / (w₁ + w₂)) z := by
  have h := sum_mul_expFamilyDiv_eq (ρ := ρ) (T := T) Finset.univ ![w₁, w₂] ![μ₁, μ₂]
    (m := (w₁ * μ₁ + w₂ * μ₂) / (w₁ + w₂)) (by simp [Fin.sum_univ_two]; field_simp) z
  simpa [Fin.sum_univ_two, expFamilyPairCost_def] using h

/-- For two distinct means `μ₁ ≠ μ₂` of the family and a positive weight `w₁`, the cost of moving
`μ₁` and `μ₂` to their weighted mean is strictly increasing in the weight `w₂ ≥ 0` of `μ₂`. -/
theorem strictMonoOn_expFamilyPairCost {μ₁ μ₂ w₁ : ℝ} (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T)
    (hμ₂ : μ₂ ∈ ρ.expFamilyMeans T) (hμ : μ₁ ≠ μ₂) (hw₁ : 0 < w₁) :
    StrictMonoOn (ρ.expFamilyPairCost T μ₁ μ₂ w₁) (Ici 0) := by
  intro y hy y' hy' hyy'
  rw [mem_Ici] at hy hy'
  have hW : 0 < w₁ + y := by linarith
  have hW' : 0 < w₁ + y' := by linarith
  set m' := (w₁ * μ₁ + y' * μ₂) / (w₁ + y') with hm'_def
  have hm' : m' ∈ ρ.expFamilyMeans T := div_mem_expFamilyMeans hμ₁ hμ₂ hw₁.le hy' hW'
  -- The weighted mean `m'` differs from `μ₂`, since `w₁ μ₁ + y' μ₂ - (w₁ + y') μ₂ = w₁ (μ₁ - μ₂)`.
  have hne : μ₂ ≠ m' := by
    rw [hm'_def, Ne, eq_div_iff hW'.ne']
    intro h
    exact mul_ne_zero hw₁.ne' (sub_ne_zero.2 hμ) (by linear_combination -h)
  -- By the compensation identity, the cost at `y` is at most `w₁ d(μ₁, m') + y d(μ₂, m')`, which
  -- is smaller than the cost `w₁ d(μ₁, m') + y' d(μ₂, m')` at `y'`.
  have h := mul_expFamilyDiv_add_mul_expFamilyDiv_eq (ρ := ρ) (T := T) (μ₁ := μ₁) (μ₂ := μ₂)
    hW.ne' m'
  have h_nonneg := mul_nonneg hW.le
    (expFamilyDiv_nonneg (div_mem_expFamilyMeans hμ₁ hμ₂ hw₁.le hy hW) hm')
  have h_lt := mul_lt_mul_of_pos_right hyy' (expFamilyDiv_pos hμ₂ hm' hne)
  rw [expFamilyPairCost_def ρ T μ₁ μ₂ w₁ y']
  linarith

/-- If the cost of moving two distinct means to their weighted mean, at the midpoint of two pairs
of weights, equals its cost at both pairs, then the two pairs of weights are proportional. This
is a consequence of the strict concavity of the cost along the directions that change the ratio of
the weights. -/
lemma mul_eq_mul_of_expFamilyPairCost_midpoint_eq {μ₁ μ₂ x₁ y₁ x₂ y₂ : ℝ}
    (hμ₁ : μ₁ ∈ ρ.expFamilyMeans T) (hμ₂ : μ₂ ∈ ρ.expFamilyMeans T) (hμ : μ₁ ≠ μ₂)
    (hx₁ : 0 ≤ x₁) (hy₁ : 0 ≤ y₁) (hx₂ : 0 ≤ x₂) (hy₂ : 0 ≤ y₂) (h₁ : 0 < x₁ + y₁)
    (h₂ : 0 < x₂ + y₂)
    (he₁ : ρ.expFamilyPairCost T μ₁ μ₂ ((x₁ + x₂) / 2) ((y₁ + y₂) / 2) =
      ρ.expFamilyPairCost T μ₁ μ₂ x₁ y₁)
    (he₂ : ρ.expFamilyPairCost T μ₁ μ₂ ((x₁ + x₂) / 2) ((y₁ + y₂) / 2) =
      ρ.expFamilyPairCost T μ₁ μ₂ x₂ y₂) :
    x₁ * y₂ = x₂ * y₁ := by
  set x := (x₁ + x₂) / 2
  set y := (y₁ + y₂) / 2
  have h : 0 < x + y := by simp only [x, y]; linarith
  set m := (x * μ₁ + y * μ₂) / (x + y) with hm_def
  have hm : m ∈ ρ.expFamilyMeans T := div_mem_expFamilyMeans hμ₁ hμ₂ (by positivity)
    (by positivity) h
  have hm₁ := div_mem_expFamilyMeans hμ₁ hμ₂ hx₁ hy₁ h₁
  have hm₂ := div_mem_expFamilyMeans hμ₁ hμ₂ hx₂ hy₂ h₂
  -- By the compensation identity at `m`, the cost at the midpoint is the average of the costs at
  -- the two pairs plus nonnegative terms, which must vanish: the weighted means are all `m`.
  have e₁ := mul_expFamilyDiv_add_mul_expFamilyDiv_eq (ρ := ρ) (T := T) (μ₁ := μ₁) (μ₂ := μ₂)
    h₁.ne' m
  have e₂ := mul_expFamilyDiv_add_mul_expFamilyDiv_eq (ρ := ρ) (T := T) (μ₁ := μ₁) (μ₂ := μ₂)
    h₂.ne' m
  have e : ρ.expFamilyPairCost T μ₁ μ₂ x y =
      x * ρ.expFamilyDiv T μ₁ m + y * ρ.expFamilyDiv T μ₂ m :=
    expFamilyPairCost_def ρ T μ₁ μ₂ x y
  have hd₁ := mul_nonneg h₁.le (expFamilyDiv_nonneg hm₁ hm)
  have hd₂ := mul_nonneg h₂.le (expFamilyDiv_nonneg hm₂ hm)
  have k₁ : (x₁ + y₁) * ρ.expFamilyDiv T ((x₁ * μ₁ + y₁ * μ₂) / (x₁ + y₁)) m = 0 := by
    simp only [x, y] at e he₁ he₂
    linarith
  have k₂ : (x₂ + y₂) * ρ.expFamilyDiv T ((x₂ * μ₁ + y₂ * μ₂) / (x₂ + y₂)) m = 0 := by
    simp only [x, y] at e he₁ he₂
    linarith
  have hm₁m := (expFamilyDiv_eq_zero_iff hm₁ hm).1 ((mul_eq_zero.1 k₁).resolve_left h₁.ne')
  have hm₂m := (expFamilyDiv_eq_zero_iff hm₂ hm).1 ((mul_eq_zero.1 k₂).resolve_left h₂.ne')
  -- Equal weighted means of two distinct means have proportional weights.
  have h_eq := hm₁m.trans hm₂m.symm
  rw [div_eq_div_iff h₁.ne' h₂.ne'] at h_eq
  have : (x₁ * y₂ - x₂ * y₁) * (μ₁ - μ₂) = 0 := by linear_combination h_eq
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hμ))

/-- The cost `w₁ d(μ₁, m) + w₂ d(μ₂, m)` of moving two means to their weighted mean
`m = (w₁ μ₁ + w₂ μ₂) / (w₁ + w₂)`, the minimum over the means `z` of
`w₁ d(μ₁, z) + w₂ d(μ₂, z)`, is a continuous function of the means `(μ₁, μ₂)` of the family and of
the nonnegative weights `(w₁, w₂)`, including where both weights vanish and `m` is not defined. -/
theorem continuousOn_expFamilyPairCost (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) :
    ContinuousOn (fun p : (ℝ × ℝ) × (ℝ × ℝ) ↦ ρ.expFamilyPairCost T p.1.1 p.1.2 p.2.1 p.2.2)
      ((ρ.expFamilyMeans T ×ˢ ρ.expFamilyMeans T) ×ˢ (Ici 0 ×ˢ Ici 0)) := by
  simp only [expFamilyPairCost_def]
  set S := (ρ.expFamilyMeans T ×ˢ ρ.expFamilyMeans T) ×ˢ (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)) with hS
  set m : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p ↦ (p.2.1 * p.1.1 + p.2.2 * p.1.2) / (p.2.1 + p.2.2)
    with hm_def
  set G : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p ↦
    p.2.1 * ρ.expFamilyDiv T p.1.1 (m p) + p.2.2 * ρ.expFamilyDiv T p.1.2 (m p) with hG
  have hd := continuousOn_expFamilyDiv hT (ρ := ρ)
  -- On `S`, `0 ≤ G p ≤ w₁ d(μ₁, μ₂)`: the weighted mean minimizes `z ↦ w₁ d(μ₁, z) + w₂ d(μ₂, z)`,
  -- in particular `G p` is at most its value at `z = μ₂`.
  have h_bounds (p : (ℝ × ℝ) × (ℝ × ℝ)) (hp : p ∈ S) :
      0 ≤ G p ∧ G p ≤ p.2.1 * ρ.expFamilyDiv T p.1.1 p.1.2 := by
    obtain ⟨⟨hx₁, hx₂⟩, hv₁, hv₂⟩ := hp
    rw [mem_Ici] at hv₁ hv₂
    rcases (add_nonneg hv₁ hv₂).eq_or_lt with hV | hV
    · have h₁ : p.2.1 = 0 := by linarith
      have h₂ : p.2.2 = 0 := by linarith
      simp [hG, h₁, h₂]
    have hm := div_mem_expFamilyMeans hx₁ hx₂ hv₁ hv₂ hV
    refine ⟨add_nonneg (mul_nonneg hv₁ (expFamilyDiv_nonneg hx₁ hm))
      (mul_nonneg hv₂ (expFamilyDiv_nonneg hx₂ hm)), ?_⟩
    have h := mul_expFamilyDiv_add_mul_expFamilyDiv_le_of_mul_eq (μ₁ := p.1.1) (μ₂ := p.1.2)
      hv₁ hv₂ (by field_simp) hm hx₂
    rwa [expFamilyDiv_self, mul_zero, add_zero] at h
  rintro ⟨⟨μ₁, μ₂⟩, ⟨w₁, w₂⟩⟩ ⟨⟨hμ₁, hμ₂⟩, hw₁, hw₂⟩
  rw [mem_Ici] at hw₁ hw₂
  rcases (add_nonneg hw₁ hw₂).eq_or_lt with hW | hW
  · -- Both weights vanish: `G` is squeezed between `0` and `w₁ d(μ₁, μ₂)`, which tends to `0`.
    obtain ⟨rfl, rfl⟩ : w₁ = 0 ∧ w₂ = 0 := ⟨by linarith, by linarith⟩
    have h_upper : ContinuousWithinAt (fun p : (ℝ × ℝ) × (ℝ × ℝ) ↦
        p.2.1 * ρ.expFamilyDiv T p.1.1 p.1.2) S ((μ₁, μ₂), (0, 0)) :=
      continuousWithinAt_snd.fst.mul ((hd (μ₁, μ₂) ⟨hμ₁, hμ₂⟩).comp
        (x := ((μ₁, μ₂), (0, 0))) (f := Prod.fst) continuousWithinAt_fst fun p hp ↦ hp.1)
    have h0 : G ((μ₁, μ₂), (0, 0)) = 0 := by simp [hG]
    rw [ContinuousWithinAt, h0]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [ContinuousWithinAt, zero_mul] using h_upper)
      (eventually_nhdsWithin_of_forall fun p hp ↦ (h_bounds p hp).1)
      (eventually_nhdsWithin_of_forall fun p hp ↦ (h_bounds p hp).2)
  · -- A positive weight: the weighted mean is a continuous function with values in the means.
    have hm : ContinuousWithinAt m S ((μ₁, μ₂), (w₁, w₂)) :=
      ContinuousAt.continuousWithinAt (by fun_prop (disch := exact hW.ne'))
    have hm_mem : m ((μ₁, μ₂), (w₁, w₂)) ∈ ρ.expFamilyMeans T :=
      div_mem_expFamilyMeans hμ₁ hμ₂ hw₁ hw₂ hW
    have hd_at (x : ℝ) (hx : x ∈ ρ.expFamilyMeans T) :
        ContinuousAt (fun q : ℝ × ℝ ↦ ρ.expFamilyDiv T q.1 q.2) (x, m ((μ₁, μ₂), (w₁, w₂))) :=
      hd.continuousAt (prod_mem_nhds (expFamilyMeans_mem_nhds hT hx)
        (expFamilyMeans_mem_nhds hT hm_mem))
    exact (continuousWithinAt_snd.fst.mul ((hd_at μ₁ hμ₁).comp_continuousWithinAt
      (f := fun p ↦ (p.1.1, m p)) (continuousWithinAt_fst.fst.prodMk hm))).add
      (continuousWithinAt_snd.snd.mul ((hd_at μ₂ hμ₂).comp_continuousWithinAt
        (f := fun p ↦ (p.1.2, m p)) (continuousWithinAt_fst.snd.prodMk hm)))

end MeasureTheory.Measure
