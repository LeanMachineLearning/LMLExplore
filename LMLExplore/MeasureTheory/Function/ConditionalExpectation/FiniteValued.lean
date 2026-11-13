/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Notation

/-!
# Conditional expectations through a finite-valued random variable

Let `X : Ω → O` be a random variable with values in a finite type, whose conditional law given a
sub-σ-algebra `m` is `q o = P⟦X ⁻¹' {o} | m⟧`. For a family of random variables `g · o`, one for
each outcome `o`, that are `m`-measurable, the conditional expectation of `ω ↦ g ω (X ω)` given
`m` is the average `∑ o, q o • g · o` of the family under the conditional law of `X`. This is how
a randomized algorithm that, given the past, draws a finite outcome from a known law and then acts
on it, is analysed: its expected action, or the expected value of an estimate built from the
outcome, is a finite weighted sum.

## Main statements

* `LMLExplore.integrable_apply_of_measurableSet_preimage`: `ω ↦ g ω (X ω)` is integrable when
  each `g · o` is.
* `LMLExplore.aestronglyMeasurable_of_condExp_preimage_ae_eq`: the conditional law `q` of `X` is
  `m`-measurable.
* `LMLExplore.condExp_apply_ae_eq_sum_smul`: `P[fun ω ↦ g ω (X ω) | m] =ᵐ ∑ o, q o • g · o`.
* `LMLExplore.integral_apply_eq_integral_sum_smul`: the corresponding identity of expectations.
-/

public section

open MeasureTheory Finset
open scoped ProbabilityTheory

namespace LMLExplore

variable {Ω O F : Type*} [NormedAddCommGroup F] {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {X : Ω → O} {g : Ω → O → F} {q : O → Ω → ℝ}

/-- A function of a finite-valued `X` is the sum over the outcomes `o` of the indicators of
`{X = o}`. -/
lemma apply_eq_sum_indicator [Fintype O] (X : Ω → O) (g : Ω → O → F) (ω : Ω) :
    g ω (X ω) = ∑ o, (X ⁻¹' {o}).indicator (g · o) ω := by
  classical
  simp [Set.indicator_apply]

/-- If `X` takes finitely many values on measurable sets and each `g · o` is integrable, then
`ω ↦ g ω (X ω)` is integrable. -/
lemma integrable_apply_of_measurableSet_preimage [Finite O] (hX : ∀ o, MeasurableSet (X ⁻¹' {o}))
    (hg : ∀ o, Integrable (g · o) μ) : Integrable (fun ω ↦ g ω (X ω)) μ := by
  have := Fintype.ofFinite O
  simp_rw [apply_eq_sum_indicator X g]
  exact integrable_finsetSum _ fun o _ ↦ (hg o).indicator (hX o)

/-- The conditional law of a finite-valued `X` given `m` is `m`-measurable: if
`μ⟦X ⁻¹' {o} | m⟧ =ᵐ q o` for every outcome `o`, then `ω ↦ (q o ω)_o` is `m`-measurable as a
function with values in `O → ℝ`. -/
lemma aestronglyMeasurable_of_condExp_preimage_ae_eq [Finite O]
    (hq : ∀ o, μ⟦X ⁻¹' {o} | m⟧ =ᵐ[μ] q o) : AEStronglyMeasurable[m] (fun ω o ↦ q o ω) μ := by
  refine ⟨fun ω o ↦ (μ⟦X ⁻¹' {o} | m⟧) ω, ?_, ?_⟩
  · have h : Measurable[m] fun ω o ↦ (μ⟦X ⁻¹' {o} | m⟧) ω :=
      @measurable_pi_iff Ω O (fun _ ↦ ℝ) m _ _ |>.2 fun _ ↦
        (stronglyMeasurable_condExp (m := m) (μ := μ)).measurable
    exact h.stronglyMeasurable
  · filter_upwards [ae_all_iff.2 hq] with ω hω
    exact funext fun o ↦ (hω o).symm

variable [Fintype O] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Conditional expectation through a finite-valued random variable.** Let `X` take values in
a finite type, with conditional law `q o` of `{X = o}` given `m`. If each `g · o` is
`m`-measurable and integrable, then `μ[fun ω ↦ g ω (X ω) | m] =ᵐ ∑ o, q o • g · o`. -/
theorem condExp_apply_ae_eq_sum_smul [IsFiniteMeasure μ] (hX : ∀ o, MeasurableSet (X ⁻¹' {o}))
    (hq : ∀ o, μ⟦X ⁻¹' {o} | m⟧ =ᵐ[μ] q o) (hgm : ∀ o, AEStronglyMeasurable[m] (g · o) μ)
    (hg : ∀ o, Integrable (g · o) μ) :
    μ[fun ω ↦ g ω (X ω) | m] =ᵐ[μ] fun ω ↦ ∑ o, q o ω • g ω o := by
  -- each indicator `{X = o}.indicator (g · o)` is the product `{X = o}.indicator 1 • g · o`
  have h_ind (o : O) : (X ⁻¹' {o}).indicator (g · o) =
      (X ⁻¹' {o}).indicator (fun _ ↦ (1 : ℝ)) • (g · o) := by
    ext ω
    by_cases h : X ω = o <;> simp [h]
  have h_int1 (o : O) : Integrable ((X ⁻¹' {o}).indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const 1).indicator (hX o)
  have h_sum : (fun ω ↦ g ω (X ω)) = ∑ o, (X ⁻¹' {o}).indicator (g · o) := by
    ext ω
    simp [Finset.sum_apply, apply_eq_sum_indicator X g ω]
  rw [h_sum]
  refine (condExp_finsetSum (fun o _ ↦ (hg o).indicator (hX o)) m).trans ?_
  -- pull the `m`-measurable factor `g · o` out of each term
  have h_term (o : O) : μ[(X ⁻¹' {o}).indicator (g · o) | m] =ᵐ[μ] q o • (g · o) := by
    rw [h_ind]
    refine (condExp_smul_of_aestronglyMeasurable_right (h_int1 o) ?_ (hgm o)).trans ?_
    · rw [← h_ind]
      exact (hg o).indicator (hX o)
    · filter_upwards [hq o] with ω hω
      rw [Pi.smul_apply', Pi.smul_apply', hω]
  have h_all : ∀ᵐ ω ∂μ, ∀ o, μ[(X ⁻¹' {o}).indicator (g · o) | m] ω = q o ω • g ω o :=
    ae_all_iff.2 fun o ↦ (h_term o).mono fun ω hω ↦ by simpa using hω
  filter_upwards [h_all] with ω hω
  simp [Finset.sum_apply, hω]

/-- **Expectation through a finite-valued random variable.** Let `X` take values in a finite type,
with conditional law `q o` of `{X = o}` given a sub-σ-algebra `m`. If each `g · o` is
`m`-measurable and integrable, then `∫ g ω (X ω) = ∫ ∑ o, q o ω • g ω o`. -/
theorem integral_apply_eq_integral_sum_smul [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    (hX : ∀ o, MeasurableSet (X ⁻¹' {o})) (hq : ∀ o, μ⟦X ⁻¹' {o} | m⟧ =ᵐ[μ] q o)
    (hgm : ∀ o, AEStronglyMeasurable[m] (g · o) μ) (hg : ∀ o, Integrable (g · o) μ) :
    ∫ ω, g ω (X ω) ∂μ = ∫ ω, ∑ o, q o ω • g ω o ∂μ := by
  rw [← integral_condExp hm]
  exact integral_congr_ae (condExp_apply_ae_eq_sum_smul hX hq hgm hg)

end LMLExplore
