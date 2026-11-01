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
then `d(μ, μ') ≥ (μ - μ')² / (2 v)`, the divergence between Gaussian laws of variance `v`. The
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
* `MeasureTheory.Measure.sq_div_le_expFamilyDiv`,
  `MeasureTheory.Measure.ofReal_sq_div_le_klDiv_expFamily_natParam`: the sub-Gaussian
  comparison `d(μ, μ') ≥ (μ - μ')² / (2 v)` when `T` has variance at most `v` under the members
  with mean strictly between `μ` and `μ'`.
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

end MeasureTheory.Measure
