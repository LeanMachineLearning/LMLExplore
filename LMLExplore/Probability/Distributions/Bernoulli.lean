/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Distributions.Bernoulli
public import LMLExplore.Analysis.Convex.Integral
public import LMLExplore.Topology.UnitInterval
public import TauCeti.Probability.Distributions.Bernoulli.Measurability

/-!
# Bernoulli laws: symmetry, absolute continuity, boundedness, sub-Gaussianity and mixtures

Exchanging the two points of a Bernoulli law `Ber(x, y, p)` replaces `p` by `1 - p`, and for
`x ≠ y`, `Ber(x, y, p) ≪ Ber(x, y, q)` exactly when `p` puts no mass on a point that `q` ignores.
Being supported on two points, a Bernoulli law gives every real function exponential moments of all
orders, and tilting it by `exp ∘ f` gives the Bernoulli law on the same two points whose odds are
multiplied by `exp (f x - f y)`.

The real two-point law `Ber(x, y, p)` is supported on the interval between `x` and `y`, hence, by
Hoeffding's lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`), it is
`(|x - y| / 2) ^ 2`-sub-Gaussian around its mean `p x + (1 - p) y`. For `Ber((1 : ℝ), 0, p)` these
are the two noise assumptions (rewards in `[0, 1]` and `1 / 4`-sub-Gaussian rewards) under which
stochastic bandit algorithms are analysed.

Drawing a point `x` from a law `ρ` on `[0, 1]` and then an observation from the Bernoulli law
`Ber(1, 0, x)` of mean `x` gives an observation with the Bernoulli law of mean `∫ x ∂ρ`: the Markov
kernel `x ↦ Ber(1, 0, x)` thus sends each law on `[0, 1]` to the Bernoulli law of its mean, and the
data processing inequality uses it to compare laws on `[0, 1]` with Bernoulli laws of the same
means.

## Main definitions

* `LMLExplore.bernoulliKernel`: the Markov kernel `x ↦ Ber(1, 0, x)` on `ℝ`, the parameter being
  clamped to `[0, 1]`.

## Main statements

* `ProbabilityTheory.bernoulliMeasure_symm`: `Ber(x, y, 1 - p) = Ber(y, x, p)`.
* `ProbabilityTheory.bernoulliMeasure_absolutelyContinuous_iff`: for `x ≠ y`,
  `Ber(x, y, p) ≪ Ber(x, y, q)` if and only if `q = 0 → p = 0` and `q = 1 → p = 1`.
* `ProbabilityTheory.lintegral_bernoulliMeasure`: `∫⁻ f ∂Ber(x, y, p) = p f(x) + (1 - p) f(y)`.
* `ProbabilityTheory.integrableExpSet_bernoulliMeasure`: every real function has exponential
  moments of all orders under `Ber(x, y, p)`.
* `ProbabilityTheory.tilted_bernoulliMeasure`: tilting `Ber(x, y, p)` by `exp ∘ f` gives
  `Ber(x, y, p')` with `p' = p exp (f x) / (p exp (f x) + (1 - p) exp (f y))`.
* `LMLExplore.ae_mem_uIcc_bernoulliMeasure`: `Ber(x, y, p)`-almost every point lies in
  `Set.uIcc x y`.
* `LMLExplore.hasSubgaussianMGF_bernoulliMeasure`: `Ber(x, y, p)` is
  `(|x - y| / 2) ^ 2`-sub-Gaussian around `p x + (1 - p) y`.
* `LMLExplore.bernoulliKernel_comp`: for a law `ρ` on `[0, 1]`, the mixture
  `bernoulliKernel ∘ₘ ρ` of the Bernoulli laws `Ber(1, 0, x)` over `x ∼ ρ` is the Bernoulli law of
  mean `∫ x ∂ρ`.
-/

public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal ProbabilityTheory unitInterval

namespace ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] {x y : X} {p q : I}

/-- Exchanging the two points of a Bernoulli law replaces its parameter `p` by `1 - p`. -/
theorem bernoulliMeasure_symm (x y : X) (p : I) : Ber(x, y, σ p) = Ber(y, x, p) := by
  rw [bernoulliMeasure_def, bernoulliMeasure_def, unitInterval.symm_symm, add_comm]

/-- A Bernoulli law is absolutely continuous with respect to the Bernoulli law on the same two
points with parameter `q` whenever it puts no mass on a point that the second law ignores. -/
theorem bernoulliMeasure_absolutelyContinuous (h0 : q = 0 → p = 0) (h1 : q = 1 → p = 1) :
    Ber(x, y, p) ≪ Ber(x, y, q) := by
  classical
  refine Measure.AbsolutelyContinuous.mk fun s hs hνs ↦ ?_
  rw [bernoulliMeasure_apply q hs] at hνs
  rw [bernoulliMeasure_apply p hs]
  split_ifs at hνs ⊢ with hx hy hy
  · simp at hνs
  · rw [ENNReal.coe_eq_zero, unitInterval.toNNReal_eq_zero] at hνs ⊢
    exact h0 hνs
  · rw [ENNReal.coe_eq_zero, unitInterval.toNNReal_eq_zero, unitInterval.symm_eq_zero] at hνs ⊢
    exact h1 hνs
  · rfl

/-- Absolute continuity between two Bernoulli laws on two distinct points: `Ber(x, y, p)` is
absolutely continuous with respect to `Ber(x, y, q)` if and only if `p` vanishes when `q` does
and `p = 1` when `q = 1`. -/
theorem bernoulliMeasure_absolutelyContinuous_iff [MeasurableSingletonClass X] (hxy : x ≠ y) :
    Ber(x, y, p) ≪ Ber(x, y, q) ↔ (q = 0 → p = 0) ∧ (q = 1 → p = 1) := by
  refine ⟨fun h ↦ ⟨fun hq ↦ ?_, fun hq ↦ ?_⟩,
    fun h ↦ bernoulliMeasure_absolutelyContinuous h.1 h.2⟩
  · simpa [hxy.symm] using h (s := {x}) (by simp [hq, hxy.symm])
  · simpa [hxy, unitInterval.symm_eq_zero] using h (s := {y}) (by simp [hq, hxy])

/-- The lower Lebesgue integral of `f` against `Ber(x, y, p)` is `p f(x) + (1 - p) f(y)`. -/
lemma lintegral_bernoulliMeasure [MeasurableSingletonClass X] (x y : X) (p : I) (f : X → ℝ≥0∞) :
    ∫⁻ z, f z ∂Ber(x, y, p) = ENNReal.ofReal p * f x + ENNReal.ofReal (1 - p) * f y := by
  simp [bernoulliMeasure_def, ENNReal.smul_def, ENNReal.coe_nnreal_eq]

/-- Every real function has exponential moments of all orders under a Bernoulli law. -/
@[simp]
lemma integrableExpSet_bernoulliMeasure [MeasurableSingletonClass X] (x y : X) (p : I)
    (T : X → ℝ) : integrableExpSet T Ber(x, y, p) = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ integrable_bernoulliMeasure x y p _

/-- Tilting the Bernoulli law `Ber(x, y, p)` by `exp ∘ f` gives the Bernoulli law on the same two
points with parameter `p exp (f x) / (p exp (f x) + (1 - p) exp (f y))`. -/
theorem tilted_bernoulliMeasure [MeasurableSingletonClass X] (x y : X) (p : I) (f : X → ℝ) :
    Ber(x, y, p).tilted f =
      Ber(x, y, ⟨p * Real.exp (f x) / (p * Real.exp (f x) + (1 - p) * Real.exp (f y)),
        unitInterval.div_mem (by have := p.2.1; positivity)
          (by have := p.2.1; have := unitInterval.one_sub_nonneg p; positivity)
          (le_add_of_nonneg_right (by have := unitInterval.one_sub_nonneg p; positivity))⟩) := by
  -- the normalizing constant `∫ exp ∘ f` is positive, since `p` and `1 - p` are not both zero
  have hZ : 0 < p * Real.exp (f x) + (1 - p) * Real.exp (f y) := by
    rcases (unitInterval.nonneg p).lt_or_eq with hp | hp
    · have := unitInterval.one_sub_nonneg p
      positivity
    · simp [← hp, Real.exp_pos]
  -- both measures are combinations of the Dirac masses at `x` and `y`: compare the weights
  rw [Measure.tilted, integral_bernoulliMeasure]
  simp only [bernoulliMeasure_def, smul_eq_mul, withDensity_add_measure, ENNReal.smul_def,
    withDensity_smul_measure, dirac_withDensity, smul_smul]
  congr 2
  all_goals simp only [ENNReal.coe_nnreal_eq, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
  · rw [← ENNReal.ofReal_mul (unitInterval.nonneg p), mul_div_assoc]
  · rw [← ENNReal.ofReal_mul (unitInterval.one_sub_nonneg p)]
    congr 1
    field_simp
    ring

end ProbabilityTheory

namespace LMLExplore

/-- Almost every point of the real Bernoulli law `Ber(x, y, p)` lies between `x` and `y`. -/
lemma ae_mem_uIcc_bernoulliMeasure (x y : ℝ) (p : I) :
    ∀ᵐ z ∂Ber(x, y, p), z ∈ Set.uIcc x y := by
  rw [ae_iff]
  exact bernoulliMeasure_apply_of_notMem_of_notMem p measurableSet_uIcc.compl (by simp) (by simp)

/-- The real Bernoulli law `Ber(x, y, p)` is `(|x - y| / 2) ^ 2`-sub-Gaussian around its mean
`p x + (1 - p) y`. -/
lemma hasSubgaussianMGF_bernoulliMeasure (x y : ℝ) (p : I) :
    HasSubgaussianMGF (fun z ↦ z - (p * x + (1 - p) * y)) ((‖x - y‖₊ / 2) ^ 2) Ber(x, y, p) := by
  have h := hasSubgaussianMGF_of_mem_Icc aemeasurable_id (ae_mem_uIcc_bernoulliMeasure x y p)
  have hc : ‖x ⊔ y - x ⊓ y‖₊ = ‖x - y‖₊ := by
    ext
    simp [max_sub_min_eq_abs']
  simpa only [id_eq, integral_bernoulliMeasure, smul_eq_mul, hc] using h

/-- The Markov kernel `x ↦ Ber(1, 0, x)` on `ℝ`, sending `x` to the Bernoulli law of mean `x`. The
parameter is clamped to `[0, 1]` by `Set.projIcc`, so that the kernel is defined on all of `ℝ`. -/
noncomputable def bernoulliKernel : Kernel ℝ ℝ where
  toFun x := Ber((1 : ℝ), 0, Set.projIcc 0 1 zero_le_one x)
  measurable' :=
    (TauCeti.Probability.measurable_bernoulliMeasure _ _).comp continuous_projIcc.measurable

@[simp]
lemma bernoulliKernel_apply (x : ℝ) :
    bernoulliKernel x = Ber((1 : ℝ), 0, Set.projIcc 0 1 zero_le_one x) :=
  (rfl)

instance : IsMarkovKernel bernoulliKernel :=
  ⟨fun x ↦ by rw [bernoulliKernel_apply]; infer_instance⟩

/-- For a probability measure `ρ` on `ℝ` supported on `[0, 1]`, the mixture
`bernoulliKernel ∘ₘ ρ` of the Bernoulli laws `Ber(1, 0, x)` over `x ∼ ρ` is the Bernoulli law of
mean `∫ x ∂ρ`. -/
theorem bernoulliKernel_comp {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : ∀ᵐ x ∂ρ, x ∈ Set.Icc 0 1) :
    bernoulliKernel ∘ₘ ρ = Ber((1 : ℝ), 0, Set.projIcc 0 1 zero_le_one ρ[id]) := by
  set p : ℝ → I := Set.projIcc 0 1 zero_le_one
  have hp : Measurable p := continuous_projIcc.measurable
  have hpi : Integrable (fun x ↦ (p x : ℝ)) ρ :=
    Integrable.of_mem_Icc 0 1 (by fun_prop) (.of_forall fun x ↦ (p x).2)
  have hint : ∫ x, (p x : ℝ) ∂ρ = ρ[id] := by
    refine integral_congr_ae ?_
    filter_upwards [hρ] with x hx
    simp [p, Set.projIcc_of_mem _ hx]
  have hmem : ρ[id] ∈ Set.Icc (0 : ℝ) 1 := integral_id_mem_Icc_of_ae_mem_Icc hρ
  have hpm : p ρ[id] = ⟨ρ[id], hmem⟩ := Set.projIcc_of_mem _ hmem
  -- The masses that the mixture puts on `1` and on `0` are the means of `x` and of `1 - x`.
  have h₁ : ∫⁻ x, (unitInterval.toNNReal (p x) : ℝ≥0∞) ∂ρ =
      unitInterval.toNNReal (p ρ[id]) := by
    simp_rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal]
    rw [← ofReal_integral_eq_lintegral_ofReal hpi (.of_forall fun x ↦ (p x).2.1), hint, hpm]
  have h₂ : ∫⁻ x, (unitInterval.toNNReal (σ (p x)) : ℝ≥0∞) ∂ρ =
      unitInterval.toNNReal (σ (p ρ[id])) := by
    simp_rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
    rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.of_mem_Icc 0 1 (by fun_prop)
      (.of_forall fun x ↦ ⟨by simp [(p x).2.2], by simp [(p x).2.1]⟩))
      (.of_forall fun x ↦ by simp [(p x).2.2]), integral_sub (integrable_const 1) hpi, hint, hpm]
    simp
  ext s hs
  rw [Measure.bind_apply hs bernoulliKernel.aemeasurable]
  simp only [bernoulliKernel_apply, bernoulliMeasure_def, add_apply, smul_apply, ENNReal.smul_def,
    smul_eq_mul]
  rw [lintegral_add_left (by fun_prop), lintegral_mul_const _ (by fun_prop),
    lintegral_mul_const _ (by fun_prop), h₁, h₂]

end LMLExplore
