/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Moments.SubGaussian
public import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib
public import LMLExplore.Probability.Moments.MGF.Bound
import LMLExplore.Analysis.SpecialFunctions.Exp
import LMLExplore.MeasureTheory.Measure.Weighted
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Conditionally sub-Gaussian variables

A real random variable `X` is conditionally `c`-sub-Gaussian given a sub-σ-algebra `m` if
`E[exp (t X) | m] ≤ exp (c t² / 2)` for every `t`; it suffices to check it at rational `t`.

A `c`-sub-Gaussian variable independent of `m` is conditionally `c`-sub-Gaussian given `m`. This
lets the martingale bounds for conditionally sub-Gaussian increments apply to sums of independent
sub-Gaussian variables. More generally, if `Y` has conditional distribution `κ` given `X` and
`y ↦ y - g x` is `c`-sub-Gaussian under `κ x` for almost every value `x` of `X`, then the centered
variable `Y - g ∘ X` is conditionally `c`-sub-Gaussian given `X`. This is how the noise of a
feedback whose conditional law given the past is sub-Gaussian around a prediction enters the
martingale bounds.

## Main statements

* `ProbabilityTheory.HasSubgaussianMGF.integrable_of_sub_const`: if `X - a` is sub-Gaussian under
  a finite measure for a constant `a`, then `X` is integrable.
* `ProbabilityTheory.HasCondSubgaussianMGF.of_ae_trim_condExp_le`: if `exp (t * X)` is integrable
  for every `t` and `E[exp (q * X) | m] ≤ exp (c * q ^ 2 / 2)` for every rational `q`, then `X` is
  conditionally `c`-sub-Gaussian given `m`.
* `ProbabilityTheory.HasSubgaussianMGF.hasCondSubgaussianMGF_of_indep`: a `c`-sub-Gaussian
  variable independent of `m` is conditionally `c`-sub-Gaussian given `m`, the sub-Gaussian case
  of `LMLExplore.HasMGFBound.hasCondMGFBound_of_indep`.
* `ProbabilityTheory.HasCondDistrib.hasCondSubgaussianMGF_sub`: if `Y` has conditional
  distribution `κ` given `X` and almost every `κ x` is `c`-sub-Gaussian around `g x`, then
  `Y - g ∘ X` is conditionally `c`-sub-Gaussian given `X`.
* `ProbabilityTheory.HasSubgaussianMGF.integral_sq_le`: a `c`-sub-Gaussian variable under a
  probability measure has second moment at most `c`.
* `ProbabilityTheory.hasSubgaussianMGF_sum_smul_dirac`: a finitely supported law whose moment
  generating function is at most `exp (c t ^ 2 / 2)` is `c`-sub-Gaussian.
* `ProbabilityTheory.exists_hasSubgaussianMGF_measure_singleton_pos`: every point of `ℝ` is charged
  by a finitely supported `c`-sub-Gaussian probability law, for `c > 0`.

## References

* The conditional sub-Gaussian material is adapted from the formalization in the LMLPapers
  project (`LMLPapers/LeanMachineLearning/ForMathlib/Probability/Moments/SubGaussian.lean`).
* `HasSubgaussianMGF.integral_sq_le`, `hasSubgaussianMGF_sum_smul_dirac` and
  `exists_hasSubgaussianMGF_measure_singleton_pos` are adapted from the Lean proof in
  `EValuesResearch/Results/SubGaussianCompleteClass.lean` and
  `EValuesResearch/Results/SubGaussianCompleteClassAux.lean` (commit `dd4072f`) of the paper
  project `RemyDegenne/evalues_research`.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- If `X - a` is `c`-sub-Gaussian under a finite measure `μ` for a constant `a`, then `X` is
`μ`-integrable. -/
theorem HasSubgaussianMGF.integrable_of_sub_const [IsFiniteMeasure μ] {a : ℝ}
    (h : HasSubgaussianMGF (fun ω ↦ X ω - a) c μ) : Integrable X μ :=
  (h.integrable.add (integrable_const a)).congr
    (ae_of_all _ fun ω ↦ by simp only [Pi.add_apply, sub_add_cancel])

/-- **Conditional sub-Gaussianity from a conditional expectation bound.** If `exp (t * X)` is
integrable for every `t` and, for every rational `q`, `E[exp (q * X) | m] ≤ exp (c * q ^ 2 / 2)`
almost everywhere on `m`, then `X` is conditionally `c`-sub-Gaussian given `m`. This is the converse
of `HasCondSubgaussianMGF.ae_trim_condExp_le`. -/
theorem HasCondSubgaussianMGF.of_ae_trim_condExp_le [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {hm : m ≤ mΩ} (h_int : ∀ t, Integrable (fun ω ↦ Real.exp (t * X ω)) μ)
    (h_le : ∀ q : ℚ, μ[fun ω ↦ Real.exp (q * X ω) | m]
      ≤ᵐ[μ.trim hm] fun _ ↦ Real.exp (c * (q : ℝ) ^ 2 / 2)) :
    HasCondSubgaussianMGF m hm X c μ := by
  refine Kernel.HasSubgaussianMGF.of_rat (fun t ↦ ?_) (fun q ↦ ?_)
  · rw [condExpKernel_comp_trim]
    exact h_int t
  filter_upwards [condExp_ae_eq_trim_integral_condExpKernel hm (h_int q), h_le q]
    with ω h_kernel h_bound
  rw [mgf, ← h_kernel]
  exact h_bound

/-- **Independence gives conditional sub-Gaussianity.** If `X` is measurable, `c`-sub-Gaussian and
independent of the sub-σ-algebra `m`, then `X` is conditionally `c`-sub-Gaussian given `m`. -/
theorem HasSubgaussianMGF.hasCondSubgaussianMGF_of_indep [StandardBorelSpace Ω]
    [IsProbabilityMeasure μ] {hm : m ≤ mΩ} (h : HasSubgaussianMGF X c μ) (hX : Measurable X)
    (h_indep : Indep (MeasurableSpace.comap X inferInstance) m μ) :
    HasCondSubgaussianMGF m hm X c μ :=
  LMLExplore.hasCondMGFBound_iff_hasCondSubgaussianMGF.1
    ((LMLExplore.hasMGFBound_iff_hasSubgaussianMGF.2 h).hasCondMGFBound_of_indep hX h_indep)

/-- **Conditional sub-Gaussianity from a conditional distribution.** If `Y` has conditional
distribution `κ` given `X` and, for almost every value `x` of `X`, `y ↦ y - g x` is
`c`-sub-Gaussian under `κ x`, then `Y - g ∘ X` is conditionally `c`-sub-Gaussian given the
σ-algebra generated by `X`. -/
theorem HasCondDistrib.hasCondSubgaussianMGF_sub [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧} {Y : Ω → ℝ} {κ : Kernel 𝓧 ℝ}
    [IsFiniteKernel κ] (h : HasCondDistrib Y X κ μ) (hX : Measurable X) {g : 𝓧 → ℝ}
    (hg : Measurable g)
    (hκ : ∀ᵐ x ∂μ.map X, HasSubgaussianMGF (fun y ↦ y - g x) c (κ x)) :
    HasCondSubgaussianMGF (m𝓧.comap X) hX.comap_le (fun ω ↦ Y ω - g (X ω)) c μ := by
  have hm : m𝓧.comap X ≤ mΩ := hX.comap_le
  have hf (t : ℝ) : StronglyMeasurable fun p : 𝓧 × ℝ ↦ Real.exp (t * (p.2 - g p.1)) :=
    (by fun_prop : Measurable fun p : 𝓧 × ℝ ↦ Real.exp (t * (p.2 - g p.1))).stronglyMeasurable
  -- the conditional moment generating function, as a function of the value of `X`
  have hF (t : ℝ) : StronglyMeasurable[m𝓧.comap X]
      fun ω ↦ ∫ y, Real.exp (t * (y - g (X ω))) ∂κ (X ω) :=
    (hf t).integral_kernel_prod_right'.comp_measurable (comap_measurable X)
  have h_int (t : ℝ) : Integrable (fun ω ↦ Real.exp (t * (Y ω - g (X ω)))) μ := by
    have h_prod : Integrable (fun p : 𝓧 × ℝ ↦ Real.exp (t * (p.2 - g p.1))) (μ.map X ⊗ₘ κ) := by
      rw [Measure.integrable_compProd_iff (hf t).aestronglyMeasurable]
      refine ⟨?_, (integrable_const (Real.exp (c * t ^ 2 / 2))).mono'
        (hf t).norm.integral_kernel_prod_right'.aestronglyMeasurable ?_⟩
      · filter_upwards [hκ] with x hx using hx.integrable_exp_mul t
      · filter_upwards [hκ] with x hx
        have h_mgf := hx.mgf_le t
        rw [mgf] at h_mgf
        simpa only [Real.norm_eq_abs, Real.abs_exp,
          abs_of_nonneg (integral_nonneg fun _ ↦ (Real.exp_pos _).le)] using h_mgf
    rw [← h.map_eq] at h_prod
    exact h_prod.comp_aemeasurable h.aemeasurable
  refine HasCondSubgaussianMGF.of_ae_trim_condExp_le h_int fun q ↦ ?_
  have h_condExp : μ[fun ω ↦ Real.exp (q * (Y ω - g (X ω))) | m𝓧.comap X]
      =ᵐ[μ] fun ω ↦ ∫ y, Real.exp (q * (y - g (X ω))) ∂κ (X ω) := by
    refine (condExp_prod_ae_eq_integral_condDistrib hX h.aemeasurable_snd (hf q) (h_int q)).trans ?_
    filter_upwards [ae_of_ae_map hX.aemeasurable h.condDistrib_ae_eq] with ω hω
    rw [hω]
  have h_le : (fun ω ↦ ∫ y, Real.exp (q * (y - g (X ω))) ∂κ (X ω))
      ≤ᵐ[μ.trim hm] fun _ ↦ Real.exp (c * q ^ 2 / 2) := by
    rw [StronglyMeasurable.ae_le_trim_iff hm (hF q) stronglyMeasurable_const]
    filter_upwards [ae_of_ae_map hX.aemeasurable hκ] with ω hω
    have h_mgf := hω.mgf_le q
    rwa [mgf] at h_mgf
  exact (StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm stronglyMeasurable_condExp (hF q)
    h_condExp).trans_le h_le


/-- A `c`-sub-Gaussian variable under a probability measure has second moment at most `c`, since
`t ^ 2 ∫ X ^ 2 ≤ 2 (exp (c t ^ 2 / 2) - 1) ≤ c t ^ 2 exp (c t ^ 2 / 2)` for every real `t`. -/
theorem HasSubgaussianMGF.integral_sq_le [IsProbabilityMeasure μ] (h : HasSubgaussianMGF X c μ) :
    ∫ ω, X ω ^ 2 ∂μ ≤ c := by
  have hx2 : Integrable (fun ω ↦ X ω ^ 2) μ := (h.memLp 2).integrable_sq
  have he := h.integrable_exp_mul
  have hmgf (t : ℝ) : ∫ ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (c * t ^ 2 / 2) := by
    simpa [mgf] using h.mgf_le t
  have key : ∀ s : ℝ, 0 < s → ∫ ω, X ω ^ 2 ∂μ ≤ c * Real.exp (c * s ^ 2 / 2) := by
    intro s hs
    have hint : Integrable (fun ω ↦ Real.exp (s * X ω) + Real.exp ((-s) * X ω)) μ :=
      (he s).add (he (-s))
    have h1 : s ^ 2 * ∫ ω, X ω ^ 2 ∂μ ≤ 2 * Real.exp (c * s ^ 2 / 2) - 2 := by
      rw [← integral_const_mul]
      calc ∫ ω, s ^ 2 * X ω ^ 2 ∂μ
          ≤ ∫ ω, (Real.exp (s * X ω) + Real.exp ((-s) * X ω) - 2) ∂μ := by
            refine integral_mono (hx2.const_mul _) (hint.sub (integrable_const 2)) fun ω ↦ ?_
            have h' := Real.one_add_sq_div_two_le_cosh (s * X ω)
            rw [Real.cosh_eq] at h'
            simp only [neg_mul]
            nlinarith
        _ ≤ 2 * Real.exp (c * s ^ 2 / 2) - 2 := by
            rw [integral_sub hint (integrable_const 2), integral_add (he s) (he (-s))]
            have := hmgf s
            have := hmgf (-s)
            simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, neg_sq] at *
            linarith
    have h3 : Real.exp (c * s ^ 2 / 2) - 1 ≤ c * s ^ 2 / 2 * Real.exp (c * s ^ 2 / 2) := by
      nlinarith [Real.add_one_le_exp (-(c * s ^ 2 / 2)), Real.exp_pos (c * s ^ 2 / 2),
        show Real.exp (-(c * s ^ 2 / 2)) * Real.exp (c * s ^ 2 / 2) = 1 by
          rw [← Real.exp_add]; simp]
    have hs2 : 0 < s ^ 2 := by positivity
    refine le_of_mul_le_mul_left ?_ hs2
    nlinarith
  have hlim : Tendsto (fun s : ℝ ↦ c * Real.exp (c * s ^ 2 / 2)) (𝓝[>] 0) (𝓝 c) := by
    have : Continuous (fun s : ℝ ↦ c * Real.exp (c * s ^ 2 / 2)) := by fun_prop
    simpa using tendsto_nhdsWithin_of_tendsto_nhds (this.tendsto 0)
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun s hs ↦ key s hs)

/-- A finitely supported law `∑ k, w k • δ_{y k}` on `ℝ`, with nonnegative weights, whose moment
generating function is at most `exp (c t ^ 2 / 2)` at every `t` is `c`-sub-Gaussian. -/
theorem hasSubgaussianMGF_sum_smul_dirac {α : Type*} [Fintype α] {w : α → ℝ} (hw : ∀ k, 0 ≤ w k)
    (y : α → ℝ) (h : ∀ t, ∑ k, w k * Real.exp (t * y k) ≤ Real.exp (c * t ^ 2 / 2)) :
    HasSubgaussianMGF id c (∑ k, ENNReal.ofReal (w k) • Measure.dirac (y k)) where
  integrable_exp_mul t := integrable_finsetSum_measure.2 fun k _ ↦
    (integrable_dirac' (by fun_prop : Measurable fun x : ℝ ↦ Real.exp (t * id x)).stronglyMeasurable
      (by simp)).smul_measure ENNReal.ofReal_ne_top
  mgf_le t := by
    rw [mgf, LMLExplore.integral_sum_smul_dirac hw
      (by fun_prop : Measurable fun x : ℝ ↦ Real.exp (t * id x)).stronglyMeasurable]
    simpa using h t

/-- For `c > 0`, every point `y` of `ℝ` is charged by a finitely supported `c`-sub-Gaussian
probability law: the law of `y / n` times a sum of `n ≥ y ^ 2 / c` independent uniform signs. -/
theorem exists_hasSubgaussianMGF_measure_singleton_pos (hc : 0 < c) (y : ℝ) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ HasSubgaussianMGF id c μ ∧
      (∃ s : Finset ℝ, μ (↑s)ᶜ = 0) ∧ 0 < μ {y} := by
  have hc' : (0 : ℝ) < c := hc
  set n : ℕ := ⌈y ^ 2 / c⌉₊ + 1 with hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hny : y ^ 2 / n ≤ c := by
    rw [div_le_iff₀ hn0, mul_comm, ← div_le_iff₀ hc', hn]
    push_cast
    linarith [Nat.le_ceil (y ^ 2 / c)]
  set a : ℝ := y / n with ha
  set x : (Fin n → Bool) → ℝ := fun σ ↦ a * ∑ i, if σ i then (1 : ℝ) else -1 with hx
  have hw : ∀ σ : Fin n → Bool, 0 ≤ (2 ^ n : ℝ)⁻¹ := fun _ ↦ by positivity
  refine ⟨∑ σ, ENNReal.ofReal (2 ^ n : ℝ)⁻¹ • Measure.dirac (x σ),
    LMLExplore.isProbabilityMeasure_sum_smul_dirac hw ?_ x, hasSubgaussianMGF_sum_smul_dirac hw x
      fun t ↦ ?_, ⟨Finset.univ.image x, LMLExplore.sum_smul_dirac_compl_eq_zero fun σ ↦
        Finset.mem_image_of_mem _ (Finset.mem_univ σ)⟩, ?_⟩
  · simp [Finset.card_univ]
  · simp_rw [hx, ← mul_assoc]
    rw [Real.sum_inv_two_pow_mul_exp_mul_sum_sign]
    calc Real.cosh (t * a) ^ n ≤ Real.exp ((t * a) ^ 2 / 2) ^ n := by
          gcongr
          exact Real.cosh_le_exp_half_sq _
      _ = Real.exp (n * ((t * a) ^ 2 / 2)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (c * t ^ 2 / 2) := by
          gcongr
          have h1 : (n : ℝ) * ((t * a) ^ 2 / 2) = t ^ 2 / 2 * (y ^ 2 / n) := by
            rw [ha]; field_simp
          rw [h1]
          nlinarith [sq_nonneg t]
  · have hy : x (fun _ ↦ true) = y := by simp [hx, ha]
    calc (0 : ℝ≥0∞) < ENNReal.ofReal (2 ^ n : ℝ)⁻¹ * Measure.dirac (x fun _ ↦ true) {y} := by
          simp [hy]
      _ ≤ ∑ σ, ENNReal.ofReal (2 ^ n : ℝ)⁻¹ * Measure.dirac (x σ) {y} :=
          Finset.single_le_sum (f := fun σ ↦ ENNReal.ofReal (2 ^ n : ℝ)⁻¹ *
            Measure.dirac (x σ) {y}) (fun _ _ ↦ bot_le) (Finset.mem_univ _)
      _ = _ := by simp

end ProbabilityTheory
