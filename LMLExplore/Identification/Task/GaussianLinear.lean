/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.InnerProductSpace.InvNormSq
public import LMLExplore.Analysis.InnerProductSpace.OptimalDesign
public import LMLExplore.Identification.Task.TransportationCost
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
the cost of the alternatives and the value of the pure exploration game of that answer. Best arm
identification with arm-dependent variances is the instance of
`LMLExplore/Identification/Task/BestArm/GaussianLinear.lean`.

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
  -- reorder the divisions by `2` and by `‖y‖²_{V_w⁻¹}`
  rw [h, ENNReal.div_right_comm]

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

end LMLExplore.Identification
