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
# The mean parametrization of a natural exponential family

Let `ρ` be a probability measure on `ℝ` which is not a Dirac mass, with log-partition function
`ψ = cgf id ρ`. The mean of the member `ρ_η = ρ.natExpFamily η` of its natural exponential family
is `ψ'(η)`, and the mean map `ψ'` is strictly increasing on the interior of the natural-parameter
set `integrableExpSet id ρ`. Its image is the open interval of the *means* of the family, and its
inverse `μ ↦ η(μ)` parametrizes the family by the means: `μ ↦ ρ_η(μ)` is the member of mean `μ`.
This is how the family appears in the bandit literature, where a model is a vector of means.

In the mean parametrization, the Kullback–Leibler divergence between two members is
`d(μ, μ') = KL(ρ_η(μ), ρ_η(μ')) = ψ(η(μ')) - ψ(η(μ)) - μ (η(μ') - η(μ))`. It is nonnegative, zero
exactly on the diagonal, continuous on the pairs of means, strictly convex in its first argument
and, in each argument, strictly decreasing below the other argument and strictly increasing above
it. It is not convex in its second argument in general (exponential distributions are a
counterexample). The function `d` is the divergence of the transportation costs and of the
generalized likelihood ratio statistics of identification in bandits with arms in an exponential
family, for example in A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed
confidence*, COLT 2016.

## Main definitions

* `MeasureTheory.Measure.natExpFamilyMeans ρ`: the set of means `ψ'(η)` of the members of the
  natural exponential family of `ρ` with natural parameter in the interior of
  `integrableExpSet id ρ`.
* `MeasureTheory.Measure.natParam ρ μ`: the natural parameter `η(μ)` of the member of mean `μ`.
* `MeasureTheory.Measure.natExpFamilyDiv ρ μ μ'`: the divergence
  `d(μ, μ') = ψ(η(μ')) - ψ(η(μ)) - μ (η(μ') - η(μ))`.

## Main statements

* `MeasureTheory.Measure.isOpen_natExpFamilyMeans`,
  `MeasureTheory.Measure.convex_natExpFamilyMeans`: the means form an open interval.
* `MeasureTheory.Measure.integral_id_natExpFamily_natParam`: the member `ρ_η(μ)` has mean `μ`.
* `MeasureTheory.Measure.strictMonoOn_natParam`, `MeasureTheory.Measure.hasDerivAt_natParam`: the
  natural parameter is strictly increasing and differentiable in the mean, with derivative
  `1 / ψ''(η(μ))`.
* `MeasureTheory.Measure.klDiv_natExpFamily_natParam`: `KL(ρ_η(μ), ρ_η(μ')) = d(μ, μ')`.
* `MeasureTheory.Measure.natExpFamilyDiv_nonneg`,
  `MeasureTheory.Measure.natExpFamilyDiv_eq_zero_iff`: `d(μ, μ') ≥ 0`, with equality iff
  `μ = μ'`.
* `MeasureTheory.Measure.continuousOn_natExpFamilyDiv`: `d` is continuous on the pairs of means.
* `MeasureTheory.Measure.strictConvexOn_natExpFamilyDiv_left`: `d` is strictly convex in its first
  argument.
* `MeasureTheory.Measure.strictAntiOn_natExpFamilyDiv_left`,
  `MeasureTheory.Measure.strictMonoOn_natExpFamilyDiv_left`,
  `MeasureTheory.Measure.strictAntiOn_natExpFamilyDiv_right`,
  `MeasureTheory.Measure.strictMonoOn_natExpFamilyDiv_right`: in each argument, `d` is strictly
  decreasing below the other argument and strictly increasing above it.
-/

public section

open ProbabilityTheory InformationTheory Filter Set

open scoped Topology

namespace MeasureTheory.Measure

variable {ρ : Measure ℝ} {η μ μ' : ℝ}

/-! ### The set of means and the natural parameter of a mean -/

/-- The set of means of the natural exponential family of `ρ`: the means `ψ'(η)` of the members
`ρ.natExpFamily η` with natural parameter `η` in the interior of `integrableExpSet id ρ`, where
`ψ = cgf id ρ`. It is an open interval, empty if that interior is, when `ρ` is a probability
measure which is not a Dirac mass (`isOpen_natExpFamilyMeans`, `convex_natExpFamilyMeans`). -/
noncomputable def natExpFamilyMeans (ρ : Measure ℝ) : Set ℝ :=
  deriv (cgf id ρ) '' interior (integrableExpSet id ρ)

/-- The natural parameter `η(μ)` of the member of mean `μ` of the natural exponential family of
`ρ`: the inverse of the mean map `ψ' = deriv (cgf id ρ)` on the interior of
`integrableExpSet id ρ`. The member of mean `μ` is `ρ.natExpFamily (ρ.natParam μ)`. The value is
meaningful for `μ ∈ ρ.natExpFamilyMeans` only. -/
noncomputable def natParam (ρ : Measure ℝ) (μ : ℝ) : ℝ :=
  Function.invFunOn (deriv (cgf id ρ)) (interior (integrableExpSet id ρ)) μ

/-- The Kullback–Leibler divergence in the mean parametrization of the natural exponential family
of `ρ`: `d(μ, μ') = ψ(η(μ')) - ψ(η(μ)) - μ (η(μ') - η(μ))`, with `ψ = cgf id ρ` and `η(μ)` the
natural parameter of the mean `μ`. For means `μ, μ'` of the family it is
`KL(ρ_η(μ), ρ_η(μ'))` (`klDiv_natExpFamily_natParam`). -/
noncomputable def natExpFamilyDiv (ρ : Measure ℝ) (μ μ' : ℝ) : ℝ :=
  cgf id ρ (ρ.natParam μ') - cgf id ρ (ρ.natParam μ) - μ * (ρ.natParam μ' - ρ.natParam μ)

lemma natExpFamilyMeans_def (ρ : Measure ℝ) :
    ρ.natExpFamilyMeans = deriv (cgf id ρ) '' interior (integrableExpSet id ρ) := (rfl)

lemma natParam_def (ρ : Measure ℝ) (μ : ℝ) :
    ρ.natParam μ = Function.invFunOn (deriv (cgf id ρ)) (interior (integrableExpSet id ρ)) μ :=
  (rfl)

lemma natExpFamilyDiv_def (ρ : Measure ℝ) (μ μ' : ℝ) :
    ρ.natExpFamilyDiv μ μ' =
      cgf id ρ (ρ.natParam μ') - cgf id ρ (ρ.natParam μ) - μ * (ρ.natParam μ' - ρ.natParam μ) :=
  (rfl)

lemma mem_natExpFamilyMeans_iff :
    μ ∈ ρ.natExpFamilyMeans ↔ ∃ η ∈ interior (integrableExpSet id ρ), deriv (cgf id ρ) η = μ :=
  Iff.rfl

lemma deriv_cgf_mem_natExpFamilyMeans (hη : η ∈ interior (integrableExpSet id ρ)) :
    deriv (cgf id ρ) η ∈ ρ.natExpFamilyMeans :=
  mem_image_of_mem _ hη

lemma natParam_mem_interior_integrableExpSet (hμ : μ ∈ ρ.natExpFamilyMeans) :
    ρ.natParam μ ∈ interior (integrableExpSet id ρ) :=
  Function.invFunOn_mem hμ

/-- The mean map sends the natural parameter of a mean `μ` to `μ`. -/
@[simp]
lemma deriv_cgf_natParam (hμ : μ ∈ ρ.natExpFamilyMeans) : deriv (cgf id ρ) (ρ.natParam μ) = μ :=
  Function.invFunOn_eq hμ

/-- The member `ρ_η(μ)` of the natural exponential family has mean `μ`. -/
lemma integral_id_natExpFamily_natParam (hμ : μ ∈ ρ.natExpFamilyMeans) :
    ∫ x, x ∂(ρ.natExpFamily (ρ.natParam μ)) = μ := by
  rw [integral_id_natExpFamily (natParam_mem_interior_integrableExpSet hμ), deriv_cgf_natParam hμ]

/-- The means of a natural exponential family form a convex set. -/
lemma convex_natExpFamilyMeans : Convex ℝ ρ.natExpFamilyMeans :=
  ((convex_integrableExpSet.interior.isPreconnected).image _
    analyticOnNhd_cgf.deriv.continuousOn).ordConnected.convex

section Inverse

variable [IsProbabilityMeasure ρ]

/-- The natural parameter of the mean `ψ'(η)` is `η`. -/
@[simp]
lemma natParam_deriv_cgf (hρ : ∀ c, ρ ≠ dirac c) (hη : η ∈ interior (integrableExpSet id ρ)) :
    ρ.natParam (deriv (cgf id ρ) η) = η :=
  (strictMonoOn_deriv_cgf_id hρ).injOn.leftInvOn_invFunOn hη

lemma image_natParam (hρ : ∀ c, ρ ≠ dirac c) :
    ρ.natParam '' ρ.natExpFamilyMeans = interior (integrableExpSet id ρ) := by
  refine MapsTo.image_subset (fun _ hμ ↦ natParam_mem_interior_integrableExpSet hμ) |>.antisymm
    fun η hη ↦ ?_
  exact ⟨_, deriv_cgf_mem_natExpFamilyMeans hη, natParam_deriv_cgf hρ hη⟩

/-- The means of the natural exponential family of a probability measure which is not a Dirac
mass form an open set. -/
theorem isOpen_natExpFamilyMeans (hρ : ∀ c, ρ ≠ dirac c) : IsOpen ρ.natExpFamilyMeans := by
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨η, hη, rfl⟩
  rw [← (hasStrictDerivAt_deriv_cgf hη).map_nhds_eq (iteratedDeriv_two_cgf_id_pos hρ hη).ne']
  exact image_mem_map (isOpen_interior.mem_nhds hη)

lemma natExpFamilyMeans_mem_nhds (hρ : ∀ c, ρ ≠ dirac c) (hμ : μ ∈ ρ.natExpFamilyMeans) :
    ρ.natExpFamilyMeans ∈ 𝓝 μ :=
  (isOpen_natExpFamilyMeans hρ).mem_nhds hμ

/-- The natural parameter is strictly increasing in the mean. -/
theorem strictMonoOn_natParam (hρ : ∀ c, ρ ≠ dirac c) :
    StrictMonoOn ρ.natParam ρ.natExpFamilyMeans := fun x hx y hy hxy ↦ by
  rwa [← (strictMonoOn_deriv_cgf_id hρ).lt_iff_lt (natParam_mem_interior_integrableExpSet hx)
    (natParam_mem_interior_integrableExpSet hy), deriv_cgf_natParam hx, deriv_cgf_natParam hy]

lemma continuousOn_natParam (hρ : ∀ c, ρ ≠ dirac c) :
    ContinuousOn ρ.natParam ρ.natExpFamilyMeans := fun μ hμ ↦ by
  refine ((strictMonoOn_natParam hρ).continuousAt_of_image_mem_nhds
    (natExpFamilyMeans_mem_nhds hρ hμ) ?_).continuousWithinAt
  rw [image_natParam hρ]
  exact isOpen_interior.mem_nhds (natParam_mem_interior_integrableExpSet hμ)

/-- The natural parameter is differentiable in the mean, with derivative `1 / ψ''(η(μ))`, the
inverse of the variance of the member of mean `μ`. -/
theorem hasDerivAt_natParam (hρ : ∀ c, ρ ≠ dirac c) (hμ : μ ∈ ρ.natExpFamilyMeans) :
    HasDerivAt ρ.natParam (iteratedDeriv 2 (cgf id ρ) (ρ.natParam μ))⁻¹ μ :=
  (hasStrictDerivAt_deriv_cgf (natParam_mem_interior_integrableExpSet hμ)).hasDerivAt
    |>.of_local_left_inverse
    ((continuousOn_natParam hρ).continuousAt (natExpFamilyMeans_mem_nhds hρ hμ))
    (iteratedDeriv_two_cgf_id_pos hρ (natParam_mem_interior_integrableExpSet hμ)).ne'
    (eventually_of_mem (natExpFamilyMeans_mem_nhds hρ hμ) fun _ ↦ deriv_cgf_natParam)

/-- The log-partition function at the natural parameter of the mean `x` has derivative
`μ / ψ''(η(μ))` in `x` at `μ`. -/
private lemma hasDerivAt_cgf_natParam (hρ : ∀ c, ρ ≠ dirac c) (hμ : μ ∈ ρ.natExpFamilyMeans) :
    HasDerivAt (fun x ↦ cgf id ρ (ρ.natParam x))
      (μ * (iteratedDeriv 2 (cgf id ρ) (ρ.natParam μ))⁻¹) μ := by
  have h :=
    (analyticOnNhd_cgf _ (natParam_mem_interior_integrableExpSet hμ)).differentiableAt.hasDerivAt
  rw [deriv_cgf_natParam hμ] at h
  exact h.comp μ (hasDerivAt_natParam hρ hμ)

end Inverse

/-! ### The divergence in the mean parametrization -/

@[simp]
lemma natExpFamilyDiv_self (ρ : Measure ℝ) (μ : ℝ) : ρ.natExpFamilyDiv μ μ = 0 := by
  simp [natExpFamilyDiv_def]

/-- The Kullback–Leibler divergence between the members of means `μ` and `μ'` of a natural
exponential family, as a real number, is `d(μ, μ')`. -/
theorem toReal_klDiv_natExpFamily_natParam (hμ : μ ∈ ρ.natExpFamilyMeans)
    (hμ' : μ' ∈ ρ.natExpFamilyMeans) :
    (klDiv (ρ.natExpFamily (ρ.natParam μ)) (ρ.natExpFamily (ρ.natParam μ'))).toReal =
      ρ.natExpFamilyDiv μ μ' := by
  rw [toReal_klDiv_natExpFamily (natParam_mem_interior_integrableExpSet hμ)
    (interior_subset (natParam_mem_interior_integrableExpSet hμ')), deriv_cgf_natParam hμ,
    natExpFamilyDiv_def]

/-- **Kullback–Leibler divergence in the mean parametrization.** The divergence between the
members of means `μ` and `μ'` of a natural exponential family is
`d(μ, μ') = ψ(η(μ')) - ψ(η(μ)) - μ (η(μ') - η(μ))`. -/
theorem klDiv_natExpFamily_natParam (hμ : μ ∈ ρ.natExpFamilyMeans)
    (hμ' : μ' ∈ ρ.natExpFamilyMeans) :
    klDiv (ρ.natExpFamily (ρ.natParam μ)) (ρ.natExpFamily (ρ.natParam μ')) =
      ENNReal.ofReal (ρ.natExpFamilyDiv μ μ') := by
  rw [klDiv_natExpFamily (natParam_mem_interior_integrableExpSet hμ)
    (interior_subset (natParam_mem_interior_integrableExpSet hμ')),
    deriv_cgf_natParam hμ, natExpFamilyDiv_def]

lemma natExpFamilyDiv_nonneg (hμ : μ ∈ ρ.natExpFamilyMeans) (hμ' : μ' ∈ ρ.natExpFamilyMeans) :
    0 ≤ ρ.natExpFamilyDiv μ μ' := by
  rw [← toReal_klDiv_natExpFamily_natParam hμ hμ']
  exact ENNReal.toReal_nonneg

/-- The divergence `d(μ, μ')` between two means of the family vanishes iff `μ = μ'`. -/
theorem natExpFamilyDiv_eq_zero_iff (hμ : μ ∈ ρ.natExpFamilyMeans)
    (hμ' : μ' ∈ ρ.natExpFamilyMeans) : ρ.natExpFamilyDiv μ μ' = 0 ↔ μ = μ' := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ natExpFamilyDiv_self ρ μ⟩
  have h_eq : ρ.natExpFamily (ρ.natParam μ) = ρ.natExpFamily (ρ.natParam μ') := by
    rw [← klDiv_eq_zero_iff, klDiv_natExpFamily_natParam hμ hμ', h, ENNReal.ofReal_zero]
  rw [← integral_id_natExpFamily_natParam hμ, ← integral_id_natExpFamily_natParam hμ', h_eq]

lemma natExpFamilyDiv_pos (hμ : μ ∈ ρ.natExpFamilyMeans) (hμ' : μ' ∈ ρ.natExpFamilyMeans)
    (h : μ ≠ μ') : 0 < ρ.natExpFamilyDiv μ μ' :=
  (natExpFamilyDiv_nonneg hμ hμ').lt_of_ne' fun h0 ↦ h ((natExpFamilyDiv_eq_zero_iff hμ hμ').1 h0)

section Analytic

variable [IsProbabilityMeasure ρ]

/-- The divergence `d(μ, μ')` is continuous on the pairs of means. -/
theorem continuousOn_natExpFamilyDiv (hρ : ∀ c, ρ ≠ dirac c) :
    ContinuousOn (fun p : ℝ × ℝ ↦ ρ.natExpFamilyDiv p.1 p.2)
      (ρ.natExpFamilyMeans ×ˢ ρ.natExpFamilyMeans) := by
  have hη := continuousOn_natParam hρ
  have hψ : ContinuousOn (fun x ↦ cgf id ρ (ρ.natParam x)) ρ.natExpFamilyMeans :=
    analyticOnNhd_cgf.continuousOn.comp hη fun _ hx ↦ natParam_mem_interior_integrableExpSet hx
  have h₁ : MapsTo Prod.fst (ρ.natExpFamilyMeans ×ˢ ρ.natExpFamilyMeans) ρ.natExpFamilyMeans :=
    fun _ hp ↦ hp.1
  have h₂ : MapsTo Prod.snd (ρ.natExpFamilyMeans ×ˢ ρ.natExpFamilyMeans) ρ.natExpFamilyMeans :=
    fun _ hp ↦ hp.2
  simp_rw [natExpFamilyDiv_def]
  exact ((hψ.comp continuousOn_snd h₂).sub (hψ.comp continuousOn_fst h₁)).sub
    (continuousOn_fst.mul ((hη.comp continuousOn_snd h₂).sub (hη.comp continuousOn_fst h₁)))

/-- The derivative of `x ↦ d(x, μ')` at a mean `μ` is `η(μ) - η(μ')`. -/
theorem hasDerivAt_natExpFamilyDiv_left (hρ : ∀ c, ρ ≠ dirac c) (hμ : μ ∈ ρ.natExpFamilyMeans)
    (μ' : ℝ) :
    HasDerivAt (fun x ↦ ρ.natExpFamilyDiv x μ') (ρ.natParam μ - ρ.natParam μ') μ := by
  have h := ((hasDerivAt_const μ (cgf id ρ (ρ.natParam μ'))).sub
    (hasDerivAt_cgf_natParam hρ hμ)).sub
    ((hasDerivAt_id' μ).mul ((hasDerivAt_const μ (ρ.natParam μ')).sub (hasDerivAt_natParam hρ hμ)))
  simp_rw [natExpFamilyDiv_def]
  convert h using 1
  simp only [Pi.sub_apply]
  ring

/-- The derivative of `y ↦ d(μ, y)` at a mean `μ'` is `(μ' - μ) / ψ''(η(μ'))`. -/
theorem hasDerivAt_natExpFamilyDiv_right (hρ : ∀ c, ρ ≠ dirac c) (μ : ℝ)
    (hμ' : μ' ∈ ρ.natExpFamilyMeans) :
    HasDerivAt (fun y ↦ ρ.natExpFamilyDiv μ y)
      ((μ' - μ) / iteratedDeriv 2 (cgf id ρ) (ρ.natParam μ')) μ' := by
  have h := ((hasDerivAt_cgf_natParam hρ hμ').sub
    (hasDerivAt_const μ' (cgf id ρ (ρ.natParam μ)))).sub
    (((hasDerivAt_natParam hρ hμ').sub (hasDerivAt_const μ' (ρ.natParam μ))).const_mul μ)
  simp_rw [natExpFamilyDiv_def]
  convert h using 1
  ring

/-- The divergence `d(μ, μ')` is strictly convex in its first argument `μ` on the means of the
family. -/
theorem strictConvexOn_natExpFamilyDiv_left (hρ : ∀ c, ρ ≠ dirac c) (μ' : ℝ) :
    StrictConvexOn ℝ ρ.natExpFamilyMeans fun x ↦ ρ.natExpFamilyDiv x μ' := by
  refine StrictMonoOn.strictConvexOn_of_deriv convex_natExpFamilyMeans
    (fun x hx ↦ (hasDerivAt_natExpFamilyDiv_left hρ hx μ').continuousAt.continuousWithinAt) ?_
  rw [(isOpen_natExpFamilyMeans hρ).interior_eq]
  intro x hx y hy hxy
  rw [(hasDerivAt_natExpFamilyDiv_left hρ hx μ').deriv,
    (hasDerivAt_natExpFamilyDiv_left hρ hy μ').deriv]
  exact sub_lt_sub_right (strictMonoOn_natParam hρ hx hy hxy) _

/-- The divergence `d(μ, μ')` is strictly decreasing in `μ` for `μ ≤ μ'`. -/
theorem strictAntiOn_natExpFamilyDiv_left (hρ : ∀ c, ρ ≠ dirac c)
    (hμ' : μ' ∈ ρ.natExpFamilyMeans) :
    StrictAntiOn (fun x ↦ ρ.natExpFamilyDiv x μ') (ρ.natExpFamilyMeans ∩ Iic μ') := by
  refine strictAntiOn_of_deriv_neg (convex_natExpFamilyMeans.inter (convex_Iic μ'))
    (fun x hx ↦ (hasDerivAt_natExpFamilyDiv_left hρ hx.1 μ').continuousAt.continuousWithinAt)
    fun x hx ↦ ?_
  rw [interior_inter, (isOpen_natExpFamilyMeans hρ).interior_eq, interior_Iic] at hx
  rw [(hasDerivAt_natExpFamilyDiv_left hρ hx.1 μ').deriv, sub_neg]
  exact strictMonoOn_natParam hρ hx.1 hμ' hx.2

/-- The divergence `d(μ, μ')` is strictly increasing in `μ` for `μ' ≤ μ`. -/
theorem strictMonoOn_natExpFamilyDiv_left (hρ : ∀ c, ρ ≠ dirac c)
    (hμ' : μ' ∈ ρ.natExpFamilyMeans) :
    StrictMonoOn (fun x ↦ ρ.natExpFamilyDiv x μ') (ρ.natExpFamilyMeans ∩ Ici μ') := by
  refine strictMonoOn_of_deriv_pos (convex_natExpFamilyMeans.inter (convex_Ici μ'))
    (fun x hx ↦ (hasDerivAt_natExpFamilyDiv_left hρ hx.1 μ').continuousAt.continuousWithinAt)
    fun x hx ↦ ?_
  rw [interior_inter, (isOpen_natExpFamilyMeans hρ).interior_eq, interior_Ici] at hx
  rw [(hasDerivAt_natExpFamilyDiv_left hρ hx.1 μ').deriv, sub_pos]
  exact strictMonoOn_natParam hρ hμ' hx.1 hx.2

/-- The divergence `d(μ, μ')` is strictly decreasing in `μ'` for `μ' ≤ μ`. -/
theorem strictAntiOn_natExpFamilyDiv_right (hρ : ∀ c, ρ ≠ dirac c) (μ : ℝ) :
    StrictAntiOn (fun y ↦ ρ.natExpFamilyDiv μ y) (ρ.natExpFamilyMeans ∩ Iic μ) := by
  refine strictAntiOn_of_deriv_neg (convex_natExpFamilyMeans.inter (convex_Iic μ))
    (fun y hy ↦ (hasDerivAt_natExpFamilyDiv_right hρ μ hy.1).continuousAt.continuousWithinAt)
    fun y hy ↦ ?_
  rw [interior_inter, (isOpen_natExpFamilyMeans hρ).interior_eq, interior_Iic] at hy
  rw [(hasDerivAt_natExpFamilyDiv_right hρ μ hy.1).deriv]
  exact div_neg_of_neg_of_pos (sub_neg.2 hy.2)
    (iteratedDeriv_two_cgf_id_pos hρ (natParam_mem_interior_integrableExpSet hy.1))

/-- The divergence `d(μ, μ')` is strictly increasing in `μ'` for `μ ≤ μ'`. -/
theorem strictMonoOn_natExpFamilyDiv_right (hρ : ∀ c, ρ ≠ dirac c) (μ : ℝ) :
    StrictMonoOn (fun y ↦ ρ.natExpFamilyDiv μ y) (ρ.natExpFamilyMeans ∩ Ici μ) := by
  refine strictMonoOn_of_deriv_pos (convex_natExpFamilyMeans.inter (convex_Ici μ))
    (fun y hy ↦ (hasDerivAt_natExpFamilyDiv_right hρ μ hy.1).continuousAt.continuousWithinAt)
    fun y hy ↦ ?_
  rw [interior_inter, (isOpen_natExpFamilyMeans hρ).interior_eq, interior_Ici] at hy
  rw [(hasDerivAt_natExpFamilyDiv_right hρ μ hy.1).deriv]
  exact div_pos (sub_pos.2 hy.2)
    (iteratedDeriv_two_cgf_id_pos hρ (natParam_mem_interior_integrableExpSet hy.1))

end Analytic

end MeasureTheory.Measure
