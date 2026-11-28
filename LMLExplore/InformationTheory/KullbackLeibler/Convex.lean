/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
import LMLExplore.MeasureTheory.Integral.BoundedMeasurable
import TauCeti.InformationTheory.KullbackLeibler.Variational
import TauCeti.MeasureTheory.Integral.Bind
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Convexity of the relative entropy in its second argument, for mixtures

For a finite measure `μ` and a mixture `π.bind κ` of finite measures `κ a` under a probability
measure `π`, the relative entropy from `μ` to the mixture is at most the average relative entropy
from `μ` to the components: `KL(μ ‖ ∫ κ a dπ(a)) ≤ ∫ KL(μ ‖ κ a) dπ(a)`. This is the integral form
of the convexity of `klDiv μ`; the form for two measures is the case `μ₁ = μ₂` of Tau Ceti's joint
convexity `TauCeti.klDiv_smul_add_smul_smul_add_smul_le`.

The proof uses Tau Ceti's variational formula with the mass correction,
`klDiv μ ν = sup_f (∫ f dμ - ∫ (exp f - 1) dν)` over the bounded measurable `f`
(`TauCeti.klDiv_eq_iSup_integral_sub_integral_exp_sub_one`): each objective is affine in `ν`,
so its value at the mixture is the average of its values at the components, each at most the
relative entropy to the component.

## Main statements

* `InformationTheory.klDiv_bind_le_lintegral`: `klDiv μ (π.bind κ) ≤ ∫⁻ a, klDiv μ (κ a) ∂π`.

## Implementation notes

The average is a lower integral, so `a ↦ klDiv μ (κ a)` need not be measurable, and `κ` need
only be almost everywhere measurable. The statement is adapted from the lemma of the same name in
`EValuesResearch/Results/Numeraire.lean` (commit `9eee1f2`) of the paper project
`RemyDegenne/evalues_research`, stated there for probability measures and proved through the
Donsker–Varadhan formula and Jensen's inequality, where it bounds the regret of the mixture
numeraires [EVR26, Note 14].

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents: Note 14, *Asymptotic log-optimality of the mixture numeraire*.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace InformationTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- **Convexity of the relative entropy in its second argument, for mixtures**: the relative
entropy from a finite measure `μ` to a mixture `π.bind κ` under a probability measure `π` is at
most the average relative entropy from `μ` to the components. The average is a lower integral:
`a ↦ klDiv μ (κ a)` need not be measurable. -/
theorem klDiv_bind_le_lintegral {μ : Measure β} [IsFiniteMeasure μ] {π : Measure α}
    [IsProbabilityMeasure π] {κ : α → Measure β} (hκ : AEMeasurable κ π)
    [IsFiniteMeasure (π.bind κ)] :
    klDiv μ (π.bind κ) ≤ ∫⁻ a, klDiv μ (κ a) ∂π := by
  rw [TauCeti.klDiv_eq_iSup_integral_sub_integral_exp_sub_one]
  refine iSup₂_le fun f hf ↦ iSup_le fun ⟨C, hC⟩ ↦ ?_
  -- the components are finite measures, almost surely
  have hfin : ∀ᵐ a ∂π, κ a .univ < ∞ := by
    refine ae_lt_top' ((Measure.measurable_coe .univ).comp_aemeasurable hκ) ?_
    rw [← Measure.bind_apply .univ hκ]
    exact measure_ne_top _ _
  -- `f`, `exp ∘ f` and `exp ∘ f - 1` are integrable for every finite measure
  have hfi (ρ : Measure β) [IsFiniteMeasure ρ] : Integrable f ρ :=
    LMLExplore.integrable_of_abs_le hf hC ρ
  have hefi (ρ : Measure β) [IsFiniteMeasure ρ] : Integrable (fun x ↦ Real.exp (f x)) ρ :=
    LMLExplore.integrable_exp_of_abs_le hf hC ρ
  have hgi (ρ : Measure β) [IsFiniteMeasure ρ] :
      Integrable (fun x ↦ Real.exp (f x) - 1) ρ :=
    (hefi ρ).sub (integrable_const 1)
  -- the component integrals of `exp ∘ f - 1` are integrable under `π`
  have hcomp : Integrable (fun a ↦ ∫ x, Real.exp (f x) - 1 ∂κ a) π := by
    have h := Measure.integrable_integral_bind hκ.measurable_mk
      (f := fun x ↦ Real.exp (f x) - 1)
      (by rw [← Measure.bind_congr_right hκ.ae_eq_mk]; exact hgi _)
    exact h.congr (hκ.ae_eq_mk.mono fun a ha ↦ by simp only [ha])
  calc ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, Real.exp (f x) - 1 ∂π.bind κ)
  _ = ENNReal.ofReal (∫ a, (∫ x, f x ∂μ - ∫ x, Real.exp (f x) - 1 ∂κ a) ∂π) := by
    rw [Measure.integral_bind hκ (hgi _), integral_sub (integrable_const _) hcomp,
      integral_const, probReal_univ, one_smul]
  _ ≤ ∫⁻ a, ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, Real.exp (f x) - 1 ∂κ a) ∂π :=
    TauCeti.MeasureTheory.ofReal_integral_le_lintegral_ofReal
  _ ≤ ∫⁻ a, klDiv μ (κ a) ∂π := by
    refine lintegral_mono_ae (hfin.mono fun a ha ↦ ?_)
    have : IsFiniteMeasure (κ a) := ⟨ha⟩
    exact TauCeti.ofReal_integral_sub_integral_exp_sub_one_le_klDiv (hfi μ) (hefi (κ a))

end InformationTheory
