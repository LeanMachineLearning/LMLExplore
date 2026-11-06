/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Kernel.Condexp

/-!
# The conditional expectation kernel: freezing and independence

If `Z` is measurable with respect to a sub-σ-algebra `m`, then integrating a function of `(Z, ω)`
amounts to integrating out `ω` against the conditional expectation kernel with `Z` frozen:
`∫⁻ ω, Φ (Z ω, ω) ∂μ = ∫⁻ ω, ∫⁻ ω', Φ (Z ω, ω') ∂(condExpKernel μ m ω) ∂μ`.

If a real random variable `X` is independent of `m`, then its conditional law given `m`, the image
of the conditional expectation kernel by `X`, is almost surely the law of `X`.

## Main statements

* `LMLExplore.lintegral_comp_condExpKernel`: the freezing lemma for nonnegative functions.
* `LMLExplore.ae_trim_map_condExpKernel_eq_of_indep`: for `X` independent of `m`,
  `(condExpKernel μ m ω).map X = μ.map X` for almost every `ω`.

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

/-- If `X` is independent of the σ-algebra `m`, then almost surely the conditional law of `X`
given `m` is the law of `X`. -/
lemma ae_trim_map_condExpKernel_eq_of_indep [IsProbabilityMeasure μ] {hm : m ≤ mΩ} {X : Ω → ℝ}
    (hX : Measurable X)
    (h_indep : Indep (MeasurableSpace.comap X inferInstance) m μ) :
    ∀ᵐ ω ∂(μ.trim hm), (condExpKernel μ m ω).map X = μ.map X := by
  -- the two laws agree on the half-lines `Iic q` with rational `q`
  have h_Iic (q : ℚ) : ∀ᵐ ω ∂(μ.trim hm),
      (condExpKernel μ m ω) (X ⁻¹' Set.Iic (q : ℝ)) = μ (X ⁻¹' Set.Iic (q : ℝ)) := by
    set s := X ⁻¹' Set.Iic (q : ℝ)
    have hs : MeasurableSet s := hX measurableSet_Iic
    have h_meas : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
        (s.indicator fun _ ↦ (1 : ℝ)) :=
      stronglyMeasurable_const.indicator ⟨Set.Iic (q : ℝ), measurableSet_Iic, rfl⟩
    have h_const : μ⟦s | m⟧ =ᵐ[μ.trim hm] fun _ ↦ μ[s.indicator fun _ ↦ (1 : ℝ)] :=
      StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm stronglyMeasurable_condExp
        stronglyMeasurable_const (condExp_indep_eq hX.comap_le hm h_meas h_indep)
    filter_upwards [condExpKernel_ae_eq_trim_condExp hm hs, h_const] with ω h_ker h_const
    have h_real : (condExpKernel μ m ω).real s = μ.real s := by
      rw [h_ker, h_const]
      exact integral_indicator_one hs
    rwa [measureReal_def, measureReal_def,
      ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)] at h_real
  rw [← ae_all_iff] at h_Iic
  filter_upwards [h_Iic] with ω hω
  refine ext_of_generate_finite _ Real.borel_eq_generateFrom_Iic_rat Real.isPiSystem_Iic_rat
    (fun s hs ↦ ?_) (by simp [Measure.map_apply hX MeasurableSet.univ])
  simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hs
  obtain ⟨q, rfl⟩ := hs
  rw [Measure.map_apply hX measurableSet_Iic, Measure.map_apply hX measurableSet_Iic, hω q]

end LMLExplore
