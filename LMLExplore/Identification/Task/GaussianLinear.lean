/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.InnerProductSpace.InvNormSq
public import LMLExplore.Analysis.InnerProductSpace.OptimalDesign
public import LMLExplore.Identification.Task.BestArm.Basic
public import LMLExplore.InformationTheory.KullbackLeibler.Gaussian

/-!
# Transportation costs of linear models with Gaussian observations

Let the models of an identification task be the vectors `θ` of a real inner product space `E`, and
let the arm `a` have Gaussian observations of mean `⟪φ a, θ⟫` and known variance `v a > 0`, for
features `φ : α → E`. The unstructured model with arm-dependent variances is
`E = EuclideanSpace ℝ α` with the basis vectors as features. For an allocation `w ≥ 0`, the
transportation cost is a squared seminorm,
`cost_θ(w, λ) = ∑ a, w a ⟪φ a, θ - λ⟫² / (2 v a) = ‖θ - λ‖²_{V_w} / 2`,
for the design operator `V_w = ∑ a, (w a / v a) • φ a ⊗ φ a`, a positive operator. The smallest
cost of a model of a half-space `{λ | ⟪y, λ⟫ ≤ c}` whose interior does not contain `θ` is therefore
`(⟪y, θ⟫ - c)² / (2 ‖y‖²_{V_w⁻¹})`, where
`‖y‖²_{V_w⁻¹} = sup_x (2 ⟪y, x⟫ - ⟪x, V_w x⟫) ∈ [0, ∞]` (`LMLExplore.invNormSq`). In finite
dimension it is `⟪y, V_w⁺ y⟫` for `y` in the range of `V_w` and `∞` otherwise, in which case the
cost is `0`. The cost of a union
of half-spaces is the infimum of the costs of the half-spaces [FJJR19, Theorem 1].

When the alternatives to an answer are, up to their closure, a union of half-spaces, this gives
the cost of the alternatives and the value of the pure exploration game of that answer. For best
arm identification in the unstructured model, the half-spaces are `{λ | λ a ≤ λ b}`, `b ≠ a`, and
the cost of the alternatives to the best arm `a` is
`D(μ, w, ¬a) = min_{b ≠ a} (μ a - μ b)² / (2 (v a / w a + v b / w b))`.

## Main statements

In the namespace `LMLExplore.Identification`:

* `IdentTask.cost_gaussianReal_inner`: the transportation cost is `‖θ - λ‖²_{V_w} / 2`, and
  `IdentTask.continuous_cost_gaussianReal_inner`: it is continuous in the alternative.
* `IdentTask.biInf_cost_gaussianReal_inner`: the smallest cost of a model of the half-space
  `{λ | ⟪y, λ⟫ ≤ c}`, `c ≤ ⟪y, θ⟫`, is `(⟪y, θ⟫ - c)² / (2 ‖y‖²_{V_w⁻¹})` [FJJR19, Theorem 1].
* `IdentTask.altCost_gaussianReal_inner`: if the alternatives to `i` lie between a union of
  half-spaces `{λ | ⟪y j, λ⟫ ≤ c j}` with `c j ≤ ⟪y j, θ⟫` and its closure, `D(θ, w, ¬i)` is the
  infimum of these values over the half-spaces, and `IdentTask.answerValue_gaussianReal_inner`:
  the value of the answer `i` is then
  `D(θ, ¬i) = sup_{w ∈ Δ_K} inf_j (⟪y j, θ⟫ - c j)² / (2 ‖y j‖²_{V_w⁻¹})`.
* `altCost_baiTask_gaussianReal`: for best arm identification with Gaussian arms of variances
  `v c` and a best arm `a`,
  `D(μ, w, ¬a) = min_{b ≠ a} w a w b (μ a - μ b)² / (2 (v a w b + v b w a))`.

## References

* [FJJR19] T. Fiez, L. Jain, K. Jamieson and L. Ratliff, *Sequential experimental design for
  transductive linear bandits*, NeurIPS 2019, Theorem 1 and its proof.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory InnerProductSpace Set

open scoped ENNReal NNReal InnerProductSpace

namespace LMLExplore.Identification

namespace IdentTask

variable {α ℐ E ι : Type*} [Fintype α] {mα : MeasurableSpace α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {task : IdentTask α E ℐ ℝ} {φ : α → E} {v : α → ℝ≥0} {w : α → ℝ}
  {θ : E} {i : ℐ}

/-- For a linear model with Gaussian observations, the arm `a` of `θ` having the law
`𝒩(⟪φ a, θ⟫, v a)` with `v a ≠ 0`, the transportation cost of an allocation `w ≥ 0` is
`cost_θ(w, θ') = ‖θ - θ'‖²_{V_w} / 2`, the quadratic form of the design operator
`V_w = ∑ a, (w a / v a) • φ a ⊗ φ a`. -/
lemma cost_gaussianReal_inner (hv : ∀ a, v a ≠ 0)
    (hν : ∀ θ a, task.ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ (v a)) (hw : 0 ≤ w) (θ θ' : E) :
    task.cost w θ θ' = ENNReal.ofReal
      (⟪θ - θ', (∑ a, (w a / v a) • rankOne ℝ (φ a) (φ a)) (θ - θ')⟫_ℝ / 2) := by
  rw [cost_def, inner_sum_smul_rankOne_apply_self, Finset.sum_div, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hva : (v a : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 (hv a)
    rw [hν, hν, klDiv_gaussianReal_gaussianReal_same_var (hv a), ← ENNReal.ofReal_mul (hw a),
      inner_sub_right]
    congr 1
    field_simp
  · exact fun a _ ↦ div_nonneg (mul_nonneg (div_nonneg (hw a) (v a).2) (sq_nonneg _)) zero_le_two

/-- For a linear model with Gaussian observations, the transportation cost of an allocation
`w ≥ 0` is continuous in the alternative. -/
lemma continuous_cost_gaussianReal_inner (hv : ∀ a, v a ≠ 0)
    (hν : ∀ θ a, task.ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ (v a)) (hw : 0 ≤ w) (θ : E) :
    Continuous (task.cost w θ) := by
  simp_rw [funext (cost_gaussianReal_inner hv hν hw θ)]
  exact ENNReal.continuous_ofReal.comp (by fun_prop)

/-- **The cost of a half-space** [FJJR19, Theorem 1]. For a linear model with Gaussian
observations and an allocation `w ≥ 0`, the smallest transportation cost from `θ` to a model of
the half-space `{θ' | ⟪y, θ'⟫ ≤ c}` with `c ≤ ⟪y, θ⟫` is `(⟪y, θ⟫ - c)² / (2 ‖y‖²_{V_w⁻¹})`, for
the design operator `V_w = ∑ a, (w a / v a) • φ a ⊗ φ a`. It is `0` when `‖y‖²_{V_w⁻¹} = ∞`, which
in finite dimension happens exactly when `y` is not in the range of `V_w`. -/
theorem biInf_cost_gaussianReal_inner (hv : ∀ a, v a ≠ 0)
    (hν : ∀ θ a, task.ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ (v a)) (hw : 0 ≤ w) {y : E} {c : ℝ}
    (hc : c ≤ ⟪y, θ⟫_ℝ) :
    ⨅ θ' ∈ {θ' | ⟪y, θ'⟫_ℝ ≤ c}, task.cost w θ θ' =
      ENNReal.ofReal ((⟪y, θ⟫_ℝ - c) ^ 2 / 2) /
        invNormSq (∑ a, (w a / v a) • rankOne ℝ (φ a) (φ a) : E →L[ℝ] E) y := by
  have hV : ∀ x, 0 ≤ ⟪x, (∑ a, (w a / v a) • rankOne ℝ (φ a) (φ a)) x⟫_ℝ :=
    (isPositive_sum_smul_rankOne Finset.univ φ fun a _ ↦
      div_nonneg (hw a) (v a).2).inner_nonneg_right
  have h := biInf_ofReal_inner_sub_apply_sub_eq_div_invNormSq
    (V := (∑ a, (w a / v a) • rankOne ℝ (φ a) (φ a) : E →L[ℝ] E)) hV hc
  have h2 : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
  simp_rw [cost_gaussianReal_inner hv hν hw, ENNReal.ofReal_div_of_pos two_pos,
    ENNReal.ofReal_ofNat, ← ENNReal.iInf_div_of_ne h2 ENNReal.ofNat_ne_top]
  rw [ContinuousLinearMap.coe_coe] at h
  rw [h, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.div_eq_inv_mul, mul_left_comm]

/-- **The cost of the alternatives as a union of half-spaces** [FJJR19, Theorem 1]. For a linear
model with Gaussian observations and an allocation `w ≥ 0`, if the alternatives to `i` lie between
a union of half-spaces `{θ' | ⟪y j, θ'⟫ ≤ c j}` with `c j ≤ ⟪y j, θ⟫` and its closure, the cost
of the alternatives to `i` is the smallest cost of a half-space,
`D(θ, w, ¬i) = inf_j (⟪y j, θ⟫ - c j)² / (2 ‖y j‖²_{V_w⁻¹})`. -/
theorem altCost_gaussianReal_inner (hv : ∀ a, v a ≠ 0)
    (hν : ∀ θ a, task.ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ (v a)) (hw : 0 ≤ w) {y : ι → E}
    {c : ι → ℝ} (h_alt : task.alt i ⊆ ⋃ j, {θ' | ⟪y j, θ'⟫_ℝ ≤ c j})
    (h_closure : ⋃ j, {θ' | ⟪y j, θ'⟫_ℝ ≤ c j} ⊆ closure (task.alt i))
    (hθ : ∀ j, c j ≤ ⟪y j, θ⟫_ℝ) :
    task.altCost θ w i = ⨅ j, ENNReal.ofReal ((⟪y j, θ⟫_ℝ - c j) ^ 2 / 2) /
      invNormSq (∑ a, (w a / v a) • rankOne ℝ (φ a) (φ a) : E →L[ℝ] E) (y j) := by
  rw [task.altCost_eq_biInf_of_subset_closure h_alt h_closure
    (continuous_cost_gaussianReal_inner hv hν hw θ).continuousOn, iInf_iUnion]
  exact iInf_congr fun j ↦ biInf_cost_gaussianReal_inner hv hν hw (hθ j)

/-- **The value of the game for alternatives forming a union of half-spaces** [FJJR19,
Theorem 1]. For a linear model with Gaussian observations, if the alternatives to `i` lie between
a union of half-spaces `{θ' | ⟪y j, θ'⟫ ≤ c j}` with `c j ≤ ⟪y j, θ⟫` and its closure, the value of
the answer `i` is
`D(θ, ¬i) = sup_{w ∈ Δ_K} inf_j (⟪y j, θ⟫ - c j)² / (2 ‖y j‖²_{V_w⁻¹})`. -/
theorem answerValue_gaussianReal_inner (hv : ∀ a, v a ≠ 0)
    (hν : ∀ θ a, task.ν θ a = gaussianReal ⟪φ a, θ⟫_ℝ (v a)) {y : ι → E} {c : ι → ℝ}
    (h_alt : task.alt i ⊆ ⋃ j, {θ' | ⟪y j, θ'⟫_ℝ ≤ c j})
    (h_closure : ⋃ j, {θ' | ⟪y j, θ'⟫_ℝ ≤ c j} ⊆ closure (task.alt i))
    (hθ : ∀ j, c j ≤ ⟪y j, θ⟫_ℝ) :
    task.answerValue θ i = ⨆ w ∈ simplex α, ⨅ j, ENNReal.ofReal ((⟪y j, θ⟫_ℝ - c j) ^ 2 / 2) /
      invNormSq (∑ a, (w a / v a) • rankOne ℝ (φ a) (φ a) : E →L[ℝ] E) (y j) := by
  rw [answerValue_def]
  exact iSup_congr fun w ↦ iSup_congr fun hw ↦ altCost_gaussianReal_inner hv hν
    (simplex_subset_nonneg hw) h_alt h_closure hθ

end IdentTask

/-! ### Best arm identification with arm-dependent variances -/

section BestArm

variable {α : Type*} [Fintype α] {mα : MeasurableSpace α} {v : α → ℝ≥0} {w : α → ℝ}

/-- In the unstructured model `EuclideanSpace ℝ α`, with the basis vectors `e c` as features, the
cost `(x² / 2) / ‖e a - e b‖²_{V_w⁻¹}` of the half-space `{λ | λ a ≤ λ b}`, at a model with
`μ a - μ b = x`, is `w a w b x² / (2 (v a w b + v b w a))`: for positive weights
`‖e a - e b‖²_{V_w⁻¹} = v a / w a + v b / w b`, and for `w a = 0` (or `w b = 0`) the vector `e a`
(or `e b`) of the kernel of `V_w` makes it `∞`. -/
private lemma ofReal_div_invNormSq_sub_basisFun (hv : ∀ c, v c ≠ 0) (hw : 0 ≤ w) {a b : α}
    (hab : b ≠ a) (x : ℝ) :
    ENNReal.ofReal (x ^ 2 / 2) / invNormSq (∑ c, (w c / v c) •
        rankOne ℝ (EuclideanSpace.basisFun α ℝ c) (EuclideanSpace.basisFun α ℝ c) :
          EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α)
        (EuclideanSpace.basisFun α ℝ a - EuclideanSpace.basisFun α ℝ b) =
      ENNReal.ofReal (w a * w b * x ^ 2 / (2 * (v a * w b + v b * w a))) := by
  classical
  set e := EuclideanSpace.basisFun α ℝ
  set V : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α := ∑ c, (w c / v c) • rankOne ℝ (e c) (e c)
  have hVe (c : α) : V (e c) = (w c / v c) • e c :=
    sum_smul_rankOne_apply_of_orthonormal e.orthonormal _ c
  have he (c d : α) : ⟪e c, e d⟫_ℝ = if c = d then 1 else 0 :=
    orthonormal_iff_ite.1 e.orthonormal c d
  have hw' : ∀ c, 0 ≤ w c := hw
  rcases (hw' a).eq_or_lt with hwa | hwa
  · rw [invNormSq_eq_top_of_apply_eq_zero (x := e a) (by simp [hVe, ← hwa])
      (by simp [inner_sub_left, he, hab])]
    simp [← hwa]
  rcases (hw' b).eq_or_lt with hwb | hwb
  · rw [invNormSq_eq_top_of_apply_eq_zero (x := e b) (by simp [hVe, ← hwb])
      (by simp [inner_sub_left, he, hab.symm])]
    simp [← hwb]
  have hva : (0 : ℝ) < v a := NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hv a))
  have hvb : (0 : ℝ) < v b := NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hv b))
  -- `V z = e a - e b` for `z = (v a / w a) e a - (v b / w b) e b`
  have h1 : v a / w a * (w a / v a) = 1 := by field_simp
  have h2 : v b / w b * (w b / v b) = 1 := by field_simp
  have hz : V ((v a / w a) • e a - (v b / w b) • e b) = e a - e b := by
    rw [map_sub, map_smul, map_smul, hVe, hVe, smul_smul, smul_smul, h1, h2, one_smul, one_smul]
  have hS : ⟪(v a / w a) • e a - (v b / w b) • e b, e a - e b⟫_ℝ = v a / w a + v b / w b := by
    simp [inner_sub_left, inner_sub_right, real_inner_smul_left, he, hab, hab.symm]
  have hV : (V : EuclideanSpace ℝ α →ₗ[ℝ] EuclideanSpace ℝ α).IsPositive :=
    (isPositive_sum_smul_rankOne Finset.univ e fun c _ ↦ div_nonneg (hw' c) (v c).2).toLinearMap
  have h := invNormSq_apply hV ((v a / w a) • e a - (v b / w b) • e b)
  rw [ContinuousLinearMap.coe_coe, hz, hS] at h
  rw [h, ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  field_simp

/-- **The cost of the alternatives in Gaussian best arm identification with arm-dependent
variances.** For Gaussian arms `𝒩(μ c, v c)` with variances `v c ≠ 0`, a best arm `a` of `μ` and
a nonnegative allocation `w`,
`D(μ, w, ¬a) = min_{b ≠ a} (μ a - μ b)² / (2 (v a / w a + v b / w b))`, written
`w a w b (μ a - μ b)² / (2 (v a w b + v b w a))` so that the value is `0` when `w a = 0` or
`w b = 0`. This is the cost of the union of the half-spaces `{λ | λ a ≤ λ b}`, `b ≠ a`, in the
unstructured model `EuclideanSpace ℝ α` with the basis vectors as features. For a common variance
`σ2` it is `altCost_baiTask_gaussianBandit`. -/
theorem altCost_baiTask_gaussianReal (hv : ∀ c, v c ≠ 0) {ν : (α → ℝ) → Kernel α ℝ}
    [∀ μ, IsMarkovKernel (ν μ)] (hν : ∀ μ c, ν μ c = gaussianReal (μ c) (v c)) {μ : α → ℝ}
    {a : α} (ha : ∀ b, μ b ≤ μ a) (hw : 0 ≤ w) :
    (baiTask ν id).altCost μ w a =
      ⨅ (b) (_ : b ≠ a),
        ENNReal.ofReal (w a * w b * (μ a - μ b) ^ 2 / (2 * (v a * w b + v b * w a))) := by
  -- Transfer to the unstructured model `EuclideanSpace ℝ α`, with the basis vectors as features.
  set h := PiLp.homeomorph 2 (fun _ : α ↦ ℝ)
  set e := EuclideanSpace.basisFun α ℝ
  -- `PiLp.homeomorph` is `WithLp.equiv`, whose application is `WithLp.ofLp`
  have hh (x : EuclideanSpace ℝ α) : h x = x.ofLp := rfl
  obtain ⟨θ, rfl⟩ := h.surjective μ
  rw [← (baiTask ν id).altCost_comap_of_alt_subset_range (f := h)
    (by rw [h.surjective.range_eq]; exact Set.subset_univ _)]
  have hν' : ∀ θ c, ((baiTask ν id).comap h).ν θ c = gaussianReal ⟪e c, θ⟫_ℝ (v c) := by
    intro θ c
    simp [hν, e, EuclideanSpace.basisFun_inner, hh]
  -- The closure of the alternatives is the union of the half-spaces `{λ | λ a ≤ λ b}`, `b ≠ a`.
  have hU : ⋃ b : {b // b ≠ a}, {θ' | ⟪e a - e b, θ'⟫_ℝ ≤ 0} =
      closure (((baiTask ν id).comap h).alt a) := by
    rw [IdentTask.alt_comap, ← h.preimage_closure, closure_alt_baiTask]
    ext θ'
    simp [e, hh, inner_sub_left, EuclideanSpace.basisFun_inner]
  rw [IdentTask.altCost_gaussianReal_inner hv hν' hw
    (hU ▸ subset_closure) hU.le (fun b ↦ ?_), iInf_subtype]
  · refine iInf_congr fun b ↦ iInf_congr fun hab ↦ ?_
    simp only [inner_sub_left, e, EuclideanSpace.basisFun_inner, sub_zero, hh]
    exact ofReal_div_invNormSq_sub_basisFun hv hw hab (θ a - θ b)
  · simp only [inner_sub_left, e, EuclideanSpace.basisFun_inner, sub_nonneg]
    simpa [hh] using ha b

end BestArm

end LMLExplore.Identification
