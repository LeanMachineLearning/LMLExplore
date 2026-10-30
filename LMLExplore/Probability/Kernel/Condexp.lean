/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Condexp

/-!
# Freezing lemma for the conditional expectation kernel

If `Z` is measurable with respect to a sub-σ-algebra `m`, then integrating a function of `(Z, ω)`
amounts to integrating out `ω` against the conditional expectation kernel with `Z` frozen:
`∫⁻ ω, Φ (Z ω, ω) ∂μ = ∫⁻ ω, ∫⁻ ω', Φ (Z ω, ω') ∂(condExpKernel μ m ω) ∂μ`.

## Main statements

* `LMLExplore.lintegral_comp_condExpKernel`: the freezing lemma for nonnegative functions.

## References

* The proof is adapted from the formalization in the LMLPapers project
  (`LMLPapers/LeanMachineLearning/ForMathlib/Probability/Kernel/Condexp.lean`).
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LMLExplore

variable {Ω E : Type*} {m mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {mE : MeasurableSpace E}
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- **Freezing lemma for the conditional expectation kernel**: if `Z` is `m`-measurable, then for
every measurable `Φ ≥ 0`,
`∫⁻ ω, Φ (Z ω, ω) ∂μ = ∫⁻ ω, ∫⁻ ω', Φ (Z ω, ω') ∂(condExpKernel μ m ω) ∂μ`. -/
theorem lintegral_comp_condExpKernel (hm : m ≤ mΩ) {Z : Ω → E} (hZ : Measurable[m] Z)
    {Φ : E × Ω → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ ω, Φ (Z ω, ω) ∂μ = ∫⁻ ω, ∫⁻ ω', Φ (Z ω, ω') ∂(condExpKernel μ m ω) ∂μ := by
  have hG : Measurable[m.prod mΩ] (fun p : Ω × Ω ↦ Φ (Z p.1, p.2)) :=
    hΦ.comp ((hZ.comp measurable_fst).prodMk measurable_snd)
  have hdiag : Measurable[mΩ, m.prod mΩ] (Function.diag : Ω → Ω × Ω) :=
    (measurable_id'' hm).prodMk measurable_id
  calc ∫⁻ ω, Φ (Z ω, ω) ∂μ
      = ∫⁻ p, Φ (Z p.1, p.2) ∂(@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ) :=
        (@lintegral_map Ω (Ω × Ω) mΩ (m.prod mΩ) μ _ _ hG hdiag).symm
    _ = ∫⁻ p, Φ (Z p.1, p.2) ∂((μ.trim hm) ⊗ₘ condExpKernel μ m) := by
        rw [compProd_trim_condExpKernel]
    _ = ∫⁻ ω, ∫⁻ ω', Φ (Z ω, ω') ∂(condExpKernel μ m ω) ∂(μ.trim hm) :=
        Measure.lintegral_compProd hG
    _ = ∫⁻ ω, ∫⁻ ω', Φ (Z ω, ω') ∂(condExpKernel μ m ω) ∂μ :=
        lintegral_trim hm hG.lintegral_kernel_prod_right'

end LMLExplore
