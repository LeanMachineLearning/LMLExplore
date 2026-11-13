/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.Task.BestArm.Basic
public import LMLExplore.Identification.Task.GaussianLinear

/-!
# Gaussian best arm identification with arm-dependent variances

For best arm identification with Gaussian arms `𝒩(μ c, v c)` of known, arm-dependent variances, the
unstructured model is the linear model on `EuclideanSpace ℝ α` with the basis vectors as features.
The closure of the alternatives to the best arm `a` is the union of the half-spaces
`{λ | λ a ≤ λ b}`, `b ≠ a`, so the cost of the alternatives is the smallest cost of these
half-spaces [FJJR19, Theorem 1]:
`D(μ, w, ¬a) = min_{b ≠ a} (μ a - μ b)² / (2 (v a / w a + v b / w b))`.

## Main statements

* `LMLExplore.Identification.altCost_baiTask_gaussianReal`: for best arm identification with
  Gaussian arms of variances `v c` and a best arm `a`,
  `D(μ, w, ¬a) = min_{b ≠ a} w a w b (μ a - μ b)² / (2 (v a w b + v b w a))`.

## References

* [FJJR19] T. Fiez, L. Jain, K. Jamieson and L. Ratliff, *Sequential experimental design for
  transductive linear bandits*, NeurIPS 2019, Theorem 1 and its proof.
-/

public section

open MeasureTheory ProbabilityTheory InnerProductSpace Set

open scoped ENNReal NNReal InnerProductSpace

namespace LMLExplore.Identification

variable {α : Type*} [Fintype α] {mα : MeasurableSpace α} {v : α → ℝ≥0} {w : α → ℝ}

/-- In the unstructured model `EuclideanSpace ℝ α`, with the basis vectors `e c` as features, the
cost `(x² / 2) / ‖e a - e b‖²_{V_w⁻¹}` of the half-space `{λ | λ a ≤ λ b}`, at a model with
`μ a - μ b = x`, is `w a w b x² / (2 (v a w b + v b w a))`: for positive weights
`‖e a - e b‖²_{V_w⁻¹} = v a / w a + v b / w b`, and for `w a = 0` (or `w b = 0`) it is `∞`. -/
private lemma ofReal_div_invNormSq_sub_basisFun (hv : ∀ c, v c ≠ 0) (hw : 0 ≤ w) {a b : α}
    (hab : b ≠ a) (x : ℝ) :
    ENNReal.ofReal (x ^ 2 / 2) / invNormSq (∑ c, (w c / v c) •
        rankOne ℝ (EuclideanSpace.basisFun α ℝ c) (EuclideanSpace.basisFun α ℝ c) :
          EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α)
        (EuclideanSpace.basisFun α ℝ a - EuclideanSpace.basisFun α ℝ b) =
      ENNReal.ofReal (w a * w b * x ^ 2 / (2 * (v a * w b + v b * w a))) := by
  set e := EuclideanSpace.basisFun α ℝ
  have hw' : ∀ c, 0 ≤ w c := hw
  rcases (hw' a).eq_or_lt with hwa | hwa
  · rw [invNormSq_sum_smul_rankOne_sub_eq_top_of_orthonormal e.orthonormal hab.symm
      (.inl (by simp [← hwa]))]
    simp [← hwa]
  rcases (hw' b).eq_or_lt with hwb | hwb
  · rw [invNormSq_sum_smul_rankOne_sub_eq_top_of_orthonormal e.orthonormal hab.symm
      (.inr (by simp [← hwb]))]
    simp [← hwb]
  have hva : (0 : ℝ) < v a := NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hv a))
  have hvb : (0 : ℝ) < v b := NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hv b))
  rw [invNormSq_sum_smul_rankOne_sub_of_orthonormal (w := fun c ↦ w c / v c) e.orthonormal
      (fun c ↦ div_nonneg (hw' c) (v c).2) hab.symm (div_pos hwa hva) (div_pos hwb hvb),
    ← ENNReal.ofReal_div_of_pos (by positivity)]
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
  have hh (x : EuclideanSpace ℝ α) : h x = x.ofLp := by
    rw [← Homeomorph.coe_toEquiv, PiLp.toEquiv_homeomorph, WithLp.equiv_apply]
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

end LMLExplore.Identification
