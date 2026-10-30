/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Martingale.Basic

/-!
# Mixtures of nonnegative supermartingales

A mixture `n ↦ ∫ l, f l n ∂π` of a measurable family of nonnegative supermartingales `f l` with
respect to a measure `π` on the parameter space is a supermartingale, as soon as
`l ↦ ∫ f l 0 ∂μ` is `π`-integrable (Tonelli's theorem). This is the *method of mixtures* step in
the proof of self-normalized concentration bounds [LS, Lemma 20.3], where the mixture over a
Gaussian law of the exponential supermartingales `exp (⟪x, S_t⟫ - ‖x‖²_{V_t} / 2)` is bounded
with Ville's inequality.

## Main statements

* `LMLExplore.supermartingale_integral_of_integrable`: the general statement, for an s-finite
  mixing measure `π` and `l ↦ ∫ f l 0 ∂μ` integrable.
* `LMLExplore.supermartingale_integral`: the case of a finite mixing measure and initial
  expectations bounded uniformly in `l`; it contains [LS, Lemma 20.3], where `π` is a probability
  measure and every `f l 0` has expectation at most `1`.

## Implementation notes

This file is adapted from `MeasureTheory.supermartingale_integral_of_integrable` and
`MeasureTheory.supermartingale_integral` in
`LeanMachineLearning/ForMathlib/Probability/Martingale/Mixture.lean` of the LMLPapers project
(https://github.com/LeanMachineLearning/LMLPapers). The almost sure convergence corollary proved
there is not included.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 20.3.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace LMLExplore

variable {Ω L : Type*} {mΩ : MeasurableSpace Ω} {mL : MeasurableSpace L} {μ : Measure Ω}
  {π : Measure L}

/-- The product σ-algebra `m₁ ⊗ m₂` is monotone in `m₂`. -/
private lemma prod_mono_right {α β : Type*} (m₁ : MeasurableSpace α)
    {m₂ m₂' : MeasurableSpace β} (h : m₂ ≤ m₂') : m₁.prod m₂ ≤ m₁.prod m₂' := by
  -- By definition, `m₁.prod m₂ = m₁.comap Prod.fst ⊔ m₂.comap Prod.snd`.
  unfold MeasurableSpace.prod
  exact sup_le_sup le_rfl (MeasurableSpace.comap_mono h)

/-- **Mixtures of supermartingales.** Let `(f l)_l` be a family of nonnegative supermartingales
such that `(l, ω) ↦ f l n ω` is `mL ⊗ ℱ n`-measurable for each `n`, and `π` an s-finite measure
on the parameter space such that `l ↦ ∫ ω, f l 0 ω ∂μ` is `π`-integrable. Then the mixture
`n ↦ ∫ l, f l n ∂π` is a supermartingale. -/
lemma supermartingale_integral_of_integrable [IsFiniteMeasure μ] [SFinite π]
    {ℱ : Filtration ℕ mΩ} {f : L → ℕ → Ω → ℝ} (hf : ∀ l, Supermartingale (f l) ℱ μ)
    (hf_nonneg : ∀ l n ω, 0 ≤ f l n ω)
    (hmeas : ∀ n, Measurable[mL.prod (ℱ n)] (fun p : L × Ω ↦ f p.1 n p.2))
    (hint : Integrable (fun l ↦ ∫ ω, f l 0 ω ∂μ) π) :
    Supermartingale (fun n ω ↦ ∫ l, f l n ω ∂π) ℱ μ := by
  set G : ℕ → Ω → ℝ≥0∞ := fun n ω ↦ ∫⁻ l, ENNReal.ofReal (f l n ω) ∂π with hG_def
  have hmeas' : ∀ n, Measurable (fun p : L × Ω ↦ f p.1 n p.2) := fun n ↦
    (hmeas n).mono (prod_mono_right mL (ℱ.le n)) le_rfl
  have hsec : ∀ n ω, Measurable (fun l ↦ f l n ω) := fun n ω ↦
    (hmeas' n).comp measurable_prodMk_right
  have hg_eq : ∀ n ω, ∫ l, f l n ω ∂π = (G n ω).toReal := fun n ω ↦
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun l ↦ hf_nonneg l n ω)
      (hsec n ω).aestronglyMeasurable
  have hGm : ∀ n, Measurable (G n) := fun n ↦ (hmeas' n).ennreal_ofReal.lintegral_prod_left'
  -- Tonelli
  have hswap : ∀ n s, MeasurableSet s →
      ∫⁻ ω in s, G n ω ∂μ = ∫⁻ l, ENNReal.ofReal (∫ ω in s, f l n ω ∂μ) ∂π := by
    intro n s hs
    rw [hG_def, lintegral_lintegral_swap]
    · refine lintegral_congr fun l ↦ ?_
      rw [ofReal_integral_eq_lintegral_ofReal ((hf l).integrable n).integrableOn
        (ae_of_all _ fun ω ↦ hf_nonneg l n ω)]
    · exact ((hmeas' n).comp measurable_swap).ennreal_ofReal.aemeasurable
  have key : ∀ i j, i ≤ j → ∀ s, MeasurableSet[ℱ i] s →
      ∫⁻ ω in s, G j ω ∂μ ≤ ∫⁻ ω in s, G i ω ∂μ := by
    intro i j hij s hs
    rw [hswap j s (ℱ.le i _ hs), hswap i s (ℱ.le i _ hs)]
    exact lintegral_mono fun l ↦ ENNReal.ofReal_le_ofReal ((hf l).setIntegral_le hij hs)
  have hfin : ∀ n, ∫⁻ ω, G n ω ∂μ < ∞ := by
    intro n
    refine lt_of_le_of_lt (by simpa using key 0 n (Nat.zero_le n) Set.univ MeasurableSet.univ) ?_
    rw [← setLIntegral_univ, hswap 0 Set.univ MeasurableSet.univ]
    simpa using (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun l ↦
      integral_nonneg (hf_nonneg l 0))).1 hint.hasFiniteIntegral
  have hG_lt : ∀ n, ∀ᵐ ω ∂μ, G n ω < ∞ := fun n ↦ ae_lt_top (hGm n) (hfin n).ne
  have hint' : ∀ n, Integrable (fun ω ↦ ∫ l, f l n ω ∂π) μ := fun n ↦ by
    simp_rw [hg_eq]
    exact integrable_toReal_of_lintegral_ne_top (hGm n).aemeasurable (hfin n).ne
  have hadapt : StronglyAdapted ℱ (fun n ω ↦ ∫ l, f l n ω ∂π) := fun n ↦ by
    -- The local instance `ℱ n` on `Ω` makes `integral_prod_left'` conclude
    -- `ℱ n`-strong measurability.
    let : MeasurableSpace Ω := ℱ n
    exact (hmeas n).stronglyMeasurable.integral_prod_left'
  refine supermartingale_of_setIntegral_succ_le hadapt hint' fun n s hs ↦ ?_
  simp_rw [hg_eq]
  rw [integral_toReal (hGm _).aemeasurable (ae_restrict_of_ae (hG_lt _)),
    integral_toReal (hGm _).aemeasurable (ae_restrict_of_ae (hG_lt _))]
  exact ENNReal.toReal_mono ((setLIntegral_le_lintegral _ _).trans_lt (hfin n)).ne
    (key n (n + 1) (Nat.le_succ n) s hs)

/-- **Mixtures of supermartingales**, for a finite mixing measure: if `(f l)_l` is a family of
nonnegative supermartingales such that `(l, ω) ↦ f l n ω` is `mL ⊗ ℱ n`-measurable for each `n`
and `∫ ω, f l 0 ω ∂μ ≤ C` for all `l`, then `n ↦ ∫ l, f l n ∂π` is a supermartingale. -/
lemma supermartingale_integral [IsFiniteMeasure μ] [IsFiniteMeasure π]
    {ℱ : Filtration ℕ mΩ} {f : L → ℕ → Ω → ℝ} (hf : ∀ l, Supermartingale (f l) ℱ μ)
    (hf_nonneg : ∀ l n ω, 0 ≤ f l n ω)
    (hmeas : ∀ n, Measurable[mL.prod (ℱ n)] (fun p : L × Ω ↦ f p.1 n p.2))
    (hbdd : ∃ C, ∀ l, ∫ ω, f l 0 ω ∂μ ≤ C) :
    Supermartingale (fun n ω ↦ ∫ l, f l n ω ∂π) ℱ μ := by
  obtain ⟨C, hC⟩ := hbdd
  refine supermartingale_integral_of_integrable hf hf_nonneg hmeas ?_
  have hm : Measurable (fun p : L × Ω ↦ f p.1 0 p.2) :=
    (hmeas 0).mono (prod_mono_right mL (ℱ.le 0)) le_rfl
  refine Integrable.of_bound (C := C)
    hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable (ae_of_all _ fun l ↦ ?_)
  rw [Real.norm_of_nonneg (integral_nonneg (hf_nonneg l 0))]
  exact hC l

end LMLExplore
