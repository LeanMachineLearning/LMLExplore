/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.Task.GaussianLinear
public import LMLExplore.Identification.Task.Transductive.Basic

/-!
# The characteristic time of linear identification with Gaussian observations

In the transductive best-answer task (`LMLExplore.Identification.transductiveTask`) of a linear
model, the models are the vectors `θ` of a real inner product space `E`, the arm `a` has Gaussian
observations `𝒩(⟪φ a, θ⟫, v a)` of known variance `v a > 0`, and the correct answer of `θ` is the
answer `i` with the largest value `⟪z i, θ⟫` among finitely many distinct answers `z i ∈ E`.
Linear best arm identification is the case `z = φ`. For an allocation `w`, let
`V_w = ∑ a, (w a / v a) • φ a ⊗ φ a` be its design operator, and `‖y‖²_{V_w⁻¹}` the squared norm
`LMLExplore.invNormSq V_w y ∈ [0, ∞]`. Write `y_j = z i - z j` for the directions from the
answers `j ≠ i` to the best answer `i`, and `Δ_j = ⟪y_j, θ⟫ > 0` for the gaps. The closure of the
alternatives to `i` is the union of the half-spaces `{λ | ⟪y_j, λ⟫ ≤ 0}`, whose costs give the
characteristic time [FJJR19, Theorem 1]
`T*(θ)⁻¹ = sup_{w ∈ Δ_K} min_{j ≠ i} Δ_j² / (2 ‖y_j‖²_{V_w⁻¹})`, that is
`T*(θ) = inf_{w ∈ Δ_K} max_{j ≠ i} ‖y_j‖²_{V_w⁻¹} / (Δ_j² / 2)`. For a common variance `σ²`,
`T*(θ) = 2 σ² H_LB(θ)` with `H_LB(θ) = inf_w max_{j ≠ i} ‖y_j‖²_{V_w⁻¹} / Δ_j²` for the design
operator `V_w = ∑ a, w a • φ a ⊗ φ a`: `H_LB` is the complexity of linear best arm identification of
Soare, Lazaric and Munos [SLM14, (6)].

The characteristic time compares with the static allocations of [SLM14] as follows, for a lower
bound `Δ > 0` on the gaps `Δ_j`.
* Every allocation `w` gives `T*(θ) ≤ max_{j ≠ i} ‖y_j‖²_{V_w⁻¹} / (Δ² / 2)`. The
  *XY-allocation* [SLM14, (14)] minimizes `max_{j, k} ‖z j - z k‖²_{V_w⁻¹}`, so that
  `T*(θ) ≤ ρ_XY / (Δ² / 2)` for its value `ρ_XY = inf_w max_{j, k} ‖z j - z k‖²_{V_w⁻¹}`.
* For best arm identification and variances at most `σ²`, the *G-allocation* [SLM14, (12)], a
  Kiefer–Wolfowitz design of the features, has `‖φ a‖²_{V⁻¹} ≤ d` for every arm, where `d` is the
  dimension of the span of the features, hence `‖φ a - φ b‖²_{V_w⁻¹} ≤ 4 σ² d` and
  `T*(θ) ≤ 8 σ² d / Δ²` [SLM14, Lemma 2].
* Conversely, if `‖φ a‖² ≤ L v a` for every arm, then `V_w ≤ L • 1` for every allocation `w` of the
  simplex, so `‖y‖²_{V_w⁻¹} ≥ ‖y‖² / L` and `T*(θ) ≥ 2 ‖y_j‖² / (L Δ_j²)` for every `j ≠ i`
  [SLM14, Lemma 2]. ([SLM14, Lemma 2] prints this lower bound with the smallest gap `Δ_min` in
  place of the gap `Δ_j` of the direction `y_j`; the argument gives the gap of the direction.)

The unstructured case, `H(μ) ≤ T*(μ) ≤ 2 H(μ)` for Gaussian arms with a common variance
[SLM14, Lemma 2; GK16, Section 2.2], is
`LMLExplore.Identification.le_charTime_baiTask_gaussianBandit` and
`LMLExplore.Identification.charTime_baiTask_gaussianBandit_le`.

## Main statements

In the namespace `LMLExplore.Identification`, for finitely many distinct answers and the best
answer `i` of `θ`:

* `altCost_transductiveTask_gaussianReal`: `D(θ, w, ¬i) = min_{j ≠ i} Δ_j² / (2 ‖y_j‖²_{V_w⁻¹})`.
* `answerValue_transductiveTask_gaussianReal`:
  `D(θ, ¬i) = sup_{w ∈ Δ_K} min_{j ≠ i} Δ_j² / (2 ‖y_j‖²_{V_w⁻¹})` [FJJR19, Theorem 1].
* `charTime_transductiveTask_gaussianReal`:
  `T*(θ) = inf_{w ∈ Δ_K} max_{j ≠ i} ‖y_j‖²_{V_w⁻¹} / (Δ_j² / 2)`, and
  `charTime_transductiveTask_gaussianReal_const`: `T*(θ) = 2 σ² H_LB(θ)` for a common variance
  `σ²` [SLM14, (6)].
* `charTime_transductiveTask_gaussianReal_le_iSup_div`,
  `charTime_transductiveTask_gaussianReal_le_iInf_iSup_div`: the upper bounds by any allocation and
  by the value of the XY-allocation.
* `charTime_transductiveTask_gaussianReal_le_finrank`: `T*(θ) ≤ 8 σ² d / Δ²` for linear best arm
  identification, through the G-allocation [SLM14, Lemma 2].
* `ofReal_le_charTime_transductiveTask_gaussianReal`: `T*(θ) ≥ 2 ‖y_j‖² / (L Δ_j²)`
  [SLM14, Lemma 2].

## References

* [FJJR19] T. Fiez, L. Jain, K. Jamieson and L. Ratliff, *Sequential experimental design for
  transductive linear bandits*, NeurIPS 2019, Theorem 1.
* [SLM14] M. Soare, A. Lazaric and R. Munos, *Best-arm identification in linear bandits*,
  NeurIPS 2014, Sections 3–4 ((6), (12), (14) and Lemma 2).
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Section 2.2.
-/

public section

open MeasureTheory ProbabilityTheory Module InnerProductSpace

open scoped InnerProductSpace ENNReal NNReal

namespace LMLExplore.Identification

variable {α ι E : Type*} [Fintype α] {mα : MeasurableSpace α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {ν : E → Kernel α ℝ} [∀ θ, IsMarkovKernel (ν θ)] {z : ι → E}
  {φ : α → E} {v : α → ℝ≥0} {w : α → ℝ} {θ : E} {i : ι}

/-! ### The characteristic time -/

/-- **The cost of the alternatives in transductive identification with Gaussian observations**
[FJJR19, Theorem 1]. For finitely many distinct answers, Gaussian observations `𝒩(⟪φ a, θ⟫, v a)`
with `v a ≠ 0`, an allocation `w ≥ 0` and a best answer `i` of `θ`, the cost of the alternatives
to `i` is `D(θ, w, ¬i) = min_{j ≠ i} ⟪z i - z j, θ⟫² / (2 ‖z i - z j‖²_{V_w⁻¹})`, for the design
operator `V_w = ∑ a, (w a / v a) • φ a ⊗ φ a`. -/
theorem altCost_transductiveTask_gaussianReal [Finite ι] (hz : Function.Injective z)
    (hv : ∀ a, v a ≠ 0) (hν : ∀ θ a, ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ (v a)) (hw : 0 ≤ w)
    (hi : ∀ j, ⟪z j, θ⟫_ℝ ≤ ⟪z i, θ⟫_ℝ) :
    (transductiveTask ν z).altCost θ w i = ⨅ j : {j // j ≠ i},
      ENNReal.ofReal (⟪z i - z j, θ⟫_ℝ ^ 2 / 2) /
        invNormSq (∑ a, (w a / v a) • rankOne ℝ (φ a) (φ a) : E →L[ℝ] E) (z i - z j) := by
  have h_eq := closure_alt_transductiveTask ν z hz i
  have h := IdentTask.altCost_gaussianReal_inner (task := transductiveTask ν z) (φ := φ) (θ := θ)
    hv (fun θ a ↦ by rw [ν_baiTask]; exact hν θ a) hw
    (y := fun j : {j // j ≠ i} ↦ z i - z j) (c := fun _ ↦ 0) (h_eq ▸ subset_closure) h_eq.ge
    fun j ↦ by rw [inner_sub_left, sub_nonneg]; exact hi j
  simpa only [sub_zero] using h

/-- **The value of the transductive game with Gaussian observations** [FJJR19, Theorem 1]. For
finitely many distinct answers, Gaussian observations `𝒩(⟪φ a, θ⟫, v a)` with `v a ≠ 0` and a best
answer `i` of `θ`, the value of the answer `i` is
`D(θ, ¬i) = sup_{w ∈ Δ_K} min_{j ≠ i} ⟪z i - z j, θ⟫² / (2 ‖z i - z j‖²_{V_w⁻¹})`, for the design
operator `V_w = ∑ a, (w a / v a) • φ a ⊗ φ a`. -/
theorem answerValue_transductiveTask_gaussianReal [Finite ι] (hz : Function.Injective z)
    (hv : ∀ a, v a ≠ 0) (hν : ∀ θ a, ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ (v a))
    (hi : ∀ j, ⟪z j, θ⟫_ℝ ≤ ⟪z i, θ⟫_ℝ) :
    (transductiveTask ν z).answerValue θ i = ⨆ w ∈ simplex α, ⨅ j : {j // j ≠ i},
      ENNReal.ofReal (⟪z i - z j, θ⟫_ℝ ^ 2 / 2) /
        invNormSq (∑ a, (w a / v a) • rankOne ℝ (φ a) (φ a) : E →L[ℝ] E) (z i - z j) := by
  have h_eq := closure_alt_transductiveTask ν z hz i
  simpa only [sub_zero] using IdentTask.answerValue_gaussianReal_inner
    (task := transductiveTask ν z) (φ := φ) (θ := θ) hv (fun θ a ↦ by rw [ν_baiTask]; exact hν θ a)
    (y := fun j : {j // j ≠ i} ↦ z i - z j) (c := fun _ ↦ 0) (h_eq ▸ subset_closure) h_eq.ge
    fun j ↦ by rw [inner_sub_left, sub_nonneg]; exact hi j

/-- **The characteristic time of transductive identification with Gaussian observations**
[FJJR19, Theorem 1]. For finitely many distinct answers, Gaussian observations
`𝒩(⟪φ a, θ⟫, v a)` with `v a ≠ 0` and a model `θ` with unique best answer `i`,
`T*(θ) = inf_{w ∈ Δ_K} max_{j ≠ i} ‖z i - z j‖²_{V_w⁻¹} / (⟪z i - z j, θ⟫² / 2)`, for the design
operator `V_w = ∑ a, (w a / v a) • φ a ⊗ φ a`. -/
theorem charTime_transductiveTask_gaussianReal [Finite ι] (hz : Function.Injective z)
    (hv : ∀ a, v a ≠ 0) (hν : ∀ θ a, ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ (v a))
    (hi : ∀ j ≠ i, ⟪z j, θ⟫_ℝ < ⟪z i, θ⟫_ℝ) :
    (transductiveTask ν z).charTime θ = ⨅ w ∈ simplex α, ⨆ j : {j // j ≠ i},
      invNormSq (∑ a, (w a / v a) • rankOne ℝ (φ a) (φ a) : E →L[ℝ] E) (z i - z j) /
        ENNReal.ofReal (⟪z i - z j, θ⟫_ℝ ^ 2 / 2) := by
  have hi' : ∀ j, ⟪z j, θ⟫_ℝ ≤ ⟪z i, θ⟫_ℝ := fun j ↦ by
    rcases eq_or_ne j i with rfl | hj
    exacts [le_rfl, (hi j hj).le]
  rw [charTime_baiTask_eq_inv_answerValue _ _ hi,
    answerValue_transductiveTask_gaussianReal hz hv hν hi']
  simp_rw [ENNReal.inv_iSup, ENNReal.inv_iInf]
  refine iInf_congr fun w ↦ iInf_congr fun _ ↦ iSup_congr fun j ↦
    ENNReal.inv_div (.inr ENNReal.ofReal_ne_top) (.inr ?_)
  have hj : 0 < ⟪z i - z j, θ⟫_ℝ := by rw [inner_sub_left, sub_pos]; exact hi j j.2
  positivity

/-- **The characteristic time of transductive identification with a common variance**
[FJJR19, Theorem 1; SLM14, (6)]. For finitely many distinct answers, Gaussian observations
`𝒩(⟪φ a, θ⟫, σ²)` with `σ² ≠ 0` and a model `θ` with unique best answer `i`,
`T*(θ) = 2 σ² H_LB(θ)` with
`H_LB(θ) = inf_{w ∈ Δ_K} max_{j ≠ i} ‖z i - z j‖²_{V_w⁻¹} / ⟪z i - z j, θ⟫²`, for the design
operator `V_w = ∑ a, w a • φ a ⊗ φ a`. -/
theorem charTime_transductiveTask_gaussianReal_const [Finite ι] (hz : Function.Injective z)
    {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0) (hν : ∀ θ a, ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ σ2)
    (hi : ∀ j ≠ i, ⟪z j, θ⟫_ℝ < ⟪z i, θ⟫_ℝ) :
    (transductiveTask ν z).charTime θ = ENNReal.ofReal (2 * σ2) * ⨅ w ∈ simplex α,
      ⨆ j : {j // j ≠ i}, invNormSq (∑ a, w a • rankOne ℝ (φ a) (φ a) : E →L[ℝ] E) (z i - z j) /
        ENNReal.ofReal (⟪z i - z j, θ⟫_ℝ ^ 2) := by
  rw [charTime_transductiveTask_gaussianReal (v := fun _ ↦ σ2) hz (fun _ ↦ hσ2) hν hi,
    ENNReal.mul_iInf_of_ne (by simp [hσ2]) ENNReal.ofReal_ne_top]
  refine iInf_congr fun w ↦ ?_
  rw [ENNReal.mul_iInf_of_ne (by simp [hσ2]) ENNReal.ofReal_ne_top]
  refine iInf_congr fun _ ↦ ?_
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun j ↦ ?_
  have hj : 0 < ⟪z i - z j, θ⟫_ℝ := by rw [inner_sub_left, sub_pos]; exact hi j j.2
  -- `σ² / (Δ² / 2) = 2 σ² / Δ²`
  have hc : ENNReal.ofReal σ2 / ENNReal.ofReal (⟪z i - z j, θ⟫_ℝ ^ 2 / 2) =
      ENNReal.ofReal (2 * σ2) / ENNReal.ofReal (⟪z i - z j, θ⟫_ℝ ^ 2) := by
    rw [← ENNReal.ofReal_div_of_pos (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  rw [invNormSq_sum_div_smul_rankOne φ w hσ2, mul_comm, mul_div_assoc, hc, div_eq_mul_inv,
    div_eq_mul_inv]
  ring

/-! ### Comparison with the static allocations -/

/-- **The characteristic time is at most the cost of any allocation** [SLM14, Section 4]. For
finitely many distinct answers, Gaussian observations `𝒩(⟪φ a, θ⟫, v a)` with `v a ≠ 0`, an
allocation `w` of the simplex and a lower bound `Δ > 0` on the gaps `⟪z i - z j, θ⟫`, `j ≠ i`,
`T*(θ) ≤ max_{j ≠ i} ‖z i - z j‖²_{V_w⁻¹} / (Δ² / 2)`, for the design operator
`V_w = ∑ a, (w a / v a) • φ a ⊗ φ a`. -/
theorem charTime_transductiveTask_gaussianReal_le_iSup_div [Finite ι] (hz : Function.Injective z)
    (hv : ∀ a, v a ≠ 0) (hν : ∀ θ a, ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ (v a)) (hw : w ∈ simplex α)
    {Δ : ℝ} (hΔ : 0 < Δ) (hi : ∀ j ≠ i, Δ ≤ ⟪z i - z j, θ⟫_ℝ) :
    (transductiveTask ν z).charTime θ ≤
      (⨆ j : {j // j ≠ i},
        invNormSq (∑ a, (w a / v a) • rankOne ℝ (φ a) (φ a) : E →L[ℝ] E) (z i - z j)) /
        ENNReal.ofReal (Δ ^ 2 / 2) := by
  have hi' : ∀ j ≠ i, ⟪z j, θ⟫_ℝ < ⟪z i, θ⟫_ℝ := fun j hj ↦ by
    have := hΔ.trans_le (hi j hj)
    rwa [inner_sub_left, sub_pos] at this
  rw [charTime_transductiveTask_gaussianReal hz hv hν hi', ENNReal.iSup_div]
  refine (iInf₂_le w hw).trans (iSup_mono fun j ↦ ENNReal.div_le_div_left ?_ _)
  gcongr
  exact hi j j.2

/-- **The characteristic time is at most the value of the XY-allocation** [SLM14, (14)]. For
finitely many distinct answers, Gaussian observations `𝒩(⟪φ a, θ⟫, v a)` with `v a ≠ 0` and a lower
bound `Δ > 0` on the gaps `⟪z i - z j, θ⟫`, `j ≠ i`, `T*(θ) ≤ ρ_XY / (Δ² / 2)` for the value
`ρ_XY = inf_{w ∈ Δ_K} max_{j, k} ‖z j - z k‖²_{V_w⁻¹}` of the XY-allocation problem, with the
design operator `V_w = ∑ a, (w a / v a) • φ a ⊗ φ a`. -/
theorem charTime_transductiveTask_gaussianReal_le_iInf_iSup_div [Finite ι]
    (hz : Function.Injective z) (hv : ∀ a, v a ≠ 0)
    (hν : ∀ θ a, ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ (v a)) {Δ : ℝ} (hΔ : 0 < Δ)
    (hi : ∀ j ≠ i, Δ ≤ ⟪z i - z j, θ⟫_ℝ) :
    (transductiveTask ν z).charTime θ ≤
      (⨅ w ∈ simplex α, ⨆ (j : ι) (k : ι),
        invNormSq (∑ a, (w a / v a) • rankOne ℝ (φ a) (φ a) : E →L[ℝ] E) (z j - z k)) /
        ENNReal.ofReal (Δ ^ 2 / 2) := by
  have hΔ2 : ENNReal.ofReal (Δ ^ 2 / 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  rw [ENNReal.le_div_iff_mul_le (.inl hΔ2) (.inl ENNReal.ofReal_ne_top)]
  refine le_iInf₂ fun w hw ↦ ?_
  rw [← ENNReal.le_div_iff_mul_le (.inl hΔ2) (.inl ENNReal.ofReal_ne_top)]
  refine (charTime_transductiveTask_gaussianReal_le_iSup_div hz hv hν hw hΔ hi).trans ?_
  gcongr
  exact iSup_le fun j ↦ le_iSup₂_of_le (f := fun j k ↦ invNormSq
    (∑ a, (w a / v a) • rankOne ℝ (φ a) (φ a) : E →L[ℝ] E) (z j - z k)) i j le_rfl

/-- **The characteristic time of linear best arm identification through the G-allocation**
[SLM14, Lemma 2]. For distinct features `φ`, Gaussian observations `𝒩(⟪φ a, θ⟫, v a)` with
variances `0 < v a ≤ σ²` and a lower bound `Δ > 0` on the gaps `⟪φ a - φ b, θ⟫`, `b ≠ a`, of the
best arm `a`, `T*(θ) ≤ 8 σ² d / Δ²`, where `d` is the dimension of the span of the features. -/
theorem charTime_transductiveTask_gaussianReal_le_finrank [FiniteDimensional ℝ E]
    (hφ : Function.Injective φ) {a : α} {σ2 : ℝ≥0} (hv : ∀ a, v a ≠ 0) (hvσ : ∀ a, v a ≤ σ2)
    (hν : ∀ θ a, ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ (v a)) {Δ : ℝ} (hΔ : 0 < Δ)
    (ha : ∀ b ≠ a, Δ ≤ ⟪φ a - φ b, θ⟫_ℝ) :
    (transductiveTask ν φ).charTime θ ≤
      ENNReal.ofReal (8 * σ2 * finrank ℝ (Submodule.span ℝ (Set.range φ)) / Δ ^ 2) := by
  have : Nonempty α := ⟨a⟩
  obtain ⟨w, hw, hle⟩ := exists_mem_simplex_invNormSq_sub_le_finrank φ hv hvσ
  calc (transductiveTask ν φ).charTime θ
      ≤ (⨆ b : {b // b ≠ a},
          invNormSq (∑ c, (w c / v c) • rankOne ℝ (φ c) (φ c) : E →L[ℝ] E) (φ a - φ b)) /
          ENNReal.ofReal (Δ ^ 2 / 2) :=
        charTime_transductiveTask_gaussianReal_le_iSup_div hφ hv hν hw hΔ ha
    _ ≤ ENNReal.ofReal (4 * σ2 * finrank ℝ (Submodule.span ℝ (Set.range φ))) /
          ENNReal.ofReal (Δ ^ 2 / 2) := by
        gcongr
        exact iSup_le fun b ↦ hle a b
    _ = ENNReal.ofReal (8 * σ2 * finrank ℝ (Submodule.span ℝ (Set.range φ)) / Δ ^ 2) := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        field_simp
        ring

/-- **A lower bound on the characteristic time** [SLM14, Lemma 2]. For finitely many distinct
answers, Gaussian observations `𝒩(⟪φ a, θ⟫, v a)` with `v a ≠ 0` and features with
`‖φ a‖² ≤ L v a` for some `L > 0`, at a model `θ` with unique best answer `i`,
`T*(θ) ≥ 2 ‖z i - z j‖² / (L ⟪z i - z j, θ⟫²)` for every answer `j ≠ i`: every allocation has
`‖y‖²_{V_w⁻¹} ≥ ‖y‖² / L`. -/
theorem ofReal_le_charTime_transductiveTask_gaussianReal [Finite ι] (hz : Function.Injective z)
    (hv : ∀ a, v a ≠ 0) (hν : ∀ θ a, ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ (v a)) {L : ℝ} (hL : 0 < L)
    (hφL : ∀ a, ‖φ a‖ ^ 2 ≤ L * v a) (hi : ∀ j ≠ i, ⟪z j, θ⟫_ℝ < ⟪z i, θ⟫_ℝ) {j : ι}
    (hj : j ≠ i) :
    ENNReal.ofReal (2 * ‖z i - z j‖ ^ 2 / (L * ⟪z i - z j, θ⟫_ℝ ^ 2)) ≤
      (transductiveTask ν z).charTime θ := by
  have hΔ : 0 < ⟪z i - z j, θ⟫_ℝ := by rw [inner_sub_left, sub_pos]; exact hi j hj
  rw [charTime_transductiveTask_gaussianReal hz hv hν hi]
  refine le_iInf₂ fun w hw ↦ le_iSup_of_le ⟨j, hj⟩ ?_
  calc ENNReal.ofReal (2 * ‖z i - z j‖ ^ 2 / (L * ⟪z i - z j, θ⟫_ℝ ^ 2))
      = ENNReal.ofReal L⁻¹ * ENNReal.ofReal (‖z i - z j‖ ^ 2) /
          ENNReal.ofReal (⟪z i - z j, θ⟫_ℝ ^ 2 / 2) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hL.le), ← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        field_simp
    _ ≤ _ := by gcongr; exact ofReal_inv_mul_le_invNormSq_sum_div_smul_rankOne hv hw hL hφL _

end LMLExplore.Identification
