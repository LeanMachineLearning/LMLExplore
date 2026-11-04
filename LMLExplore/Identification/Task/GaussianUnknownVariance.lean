/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.Instances
public import LMLExplore.Identification.Task.TransportationCost

/-!
# Transportation costs of Gaussian arms with unknown variances

In the model of Gaussian arms with unknown variances, a model `θ : α → ℝ × ℝ≥0` gives each arm `a`
a mean `μ_a = (θ a).1` and a variance `σ²_a = (θ a).2`, and the arm `a` has law `𝒩(μ_a, σ²_a)`
(`LMLExplore.Bandits.gaussianMeanVarBandit θ`). The relative entropy between the arms `a` of two
models with positive variances is
`KL(𝒩(μ_a, σ²_a), 𝒩(μ'_a, σ'²_a)) = (log (σ'²_a / σ²_a) + (σ²_a + (μ_a - μ'_a)²) / σ'²_a - 1) / 2`,
so that the transportation cost `cost_θ(w, θ')` of an identification task on this model is the
weighted sum of these divergences.

The questions asked about this model (which arm has the largest mean, for best arm identification)
concern the means only, so the alternatives to an answer constrain the means of some arms and leave
their variances free. Minimizing the divergence over the variance of the alternative arm gives
`inf_{σ'²} KL(𝒩(μ_a, σ²_a), 𝒩(x, σ'²)) = log (1 + (μ_a - x)² / σ²_a) / 2`, attained at
`σ'² = σ²_a + (μ_a - x)²` (`LMLExplore.iInf_klDiv_gaussianReal_gaussianReal`). Hence the smallest
transportation cost to a model whose arms `c ∈ s` have the means `m c` is
`∑ c ∈ s, w c log (1 + (μ_c - m c)² / σ²_c) / 2`. For two arms `a` and `b` moved to a common mean
`x`, this is the cost `w a log (1 + (μ_a - x)² / σ²_a) / 2 + w b log (1 + (μ_b - x)² / σ²_b) / 2`
in the transportation costs `C(a, b; w)` of best arm identification with unknown variances
[JDK23, Lemma 3 and (1)].

## Main statements

* `LMLExplore.Identification.IdentTask.cost_gaussianMeanVarBandit`: the transportation cost between
  two models with positive variances.
* `LMLExplore.Identification.IdentTask.sum_ofReal_mul_log_le_cost_gaussianMeanVarBandit`: a model
  whose arms `c ∈ s` have the means `m c` is at transportation cost at least
  `∑ c ∈ s, w c log (1 + (μ_c - m c)² / σ²_c) / 2`.
* `LMLExplore.Identification.IdentTask.iInf_cost_gaussianMeanVarBandit`: this lower bound is the
  infimum of the transportation costs to the models with positive variances whose arms `c ∈ s` have
  the means `m c`.
* `LMLExplore.Identification.IdentTask.iInf_cost_gaussianMeanVarBandit_pair`: the cost of moving
  two arms `a ≠ b` to a common mean `x` [JDK23, (1)].

## References

* [JDK23] M. Jourdan, R. Degenne and E. Kaufmann, *Dealing with unknown variances in best-arm
  identification*, ALT 2023, Section 2.2 (Lemma 3 and the transportation costs (1)) and
  Appendix C.1 (proof of Lemma 11).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Real

open scoped ENNReal NNReal

namespace LMLExplore.Identification.IdentTask

variable {α ℐ : Type*} {mα : MeasurableSpace α} [MeasurableSingletonClass α] [Fintype α]
  {task : IdentTask α (α → ℝ × ℝ≥0) ℐ ℝ} {θ θ' : α → ℝ × ℝ≥0} {w : α → ℝ}

/-- For Gaussian arms with unknown variances, the transportation cost between two models with
positive variances is
`cost_θ(w, θ') = ∑ c, w c (log (σ'²_c / σ²_c) + (σ²_c + (μ_c - μ'_c)²) / σ'²_c - 1) / 2`. -/
lemma cost_gaussianMeanVarBandit (hνt : task.ν = Bandits.gaussianMeanVarBandit)
    (hw : 0 ≤ w) (hθ : ∀ c, (θ c).2 ≠ 0) (hθ' : ∀ c, (θ' c).2 ≠ 0) :
    task.cost w θ θ' = ∑ c, ENNReal.ofReal (w c * ((log ((θ' c).2 / (θ c).2) +
      ((θ c).2 + ((θ c).1 - (θ' c).1) ^ 2) / (θ' c).2 - 1) / 2)) := by
  rw [cost_def, hνt]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Bandits.gaussianMeanVarBandit_apply, Bandits.gaussianMeanVarBandit_apply,
    klDiv_gaussianReal_gaussianReal (hθ c) (hθ' c), ENNReal.ofReal_mul (hw c)]

/-- **Lower bound on the cost of moving the means of some arms.** For Gaussian arms with unknown
variances, if the arms `c ∈ s` of `θ` have positive variances and the arms `c ∈ s` of `θ'` have the
means `m c`, then `∑ c ∈ s, w c log (1 + (μ_c - m c)² / σ²_c) / 2 ≤ cost_θ(w, θ')`, whatever the
variances of `θ'`. -/
lemma sum_ofReal_mul_log_le_cost_gaussianMeanVarBandit
    (hνt : task.ν = Bandits.gaussianMeanVarBandit) (hw : 0 ≤ w) {s : Finset α} {m : α → ℝ}
    (hθ : ∀ c ∈ s, (θ c).2 ≠ 0) (hθ' : ∀ c ∈ s, (θ' c).1 = m c) :
    ∑ c ∈ s, ENNReal.ofReal (w c * (log (1 + ((θ c).1 - m c) ^ 2 / (θ c).2) / 2)) ≤
      task.cost w θ θ' := by
  rw [cost_def, hνt]
  refine (Finset.sum_le_sum fun c hc ↦ ?_).trans
    (Finset.sum_le_sum_of_subset (Finset.subset_univ s))
  rw [ENNReal.ofReal_mul (hw c), Bandits.gaussianMeanVarBandit_apply,
    Bandits.gaussianMeanVarBandit_apply, ← hθ' c hc]
  gcongr
  exact ofReal_log_one_add_div_le_klDiv_gaussianReal (hθ c hc) _

/-- The model that moves the arms `c ∈ s` of `θ` to the means `m c` with the variances
`σ²_c + (μ_c - m c)²` and leaves the other arms unchanged attains the lower bound
`sum_ofReal_mul_log_le_cost_gaussianMeanVarBandit`. -/
private lemma cost_gaussianMeanVarBandit_ite (hνt : task.ν = Bandits.gaussianMeanVarBandit)
    (hw : 0 ≤ w) (s : Finset α) [DecidablePred (· ∈ s)] (m : α → ℝ)
    (hθ : ∀ c ∈ s, (θ c).2 ≠ 0) :
    task.cost w θ (fun c ↦ if c ∈ s then (m c, (θ c).2 + (((θ c).1 - m c) ^ 2).toNNReal)
      else θ c) =
      ∑ c ∈ s, ENNReal.ofReal (w c * (log (1 + ((θ c).1 - m c) ^ 2 / (θ c).2) / 2)) := by
  rw [cost_def, hνt, ← Finset.sum_subset (Finset.subset_univ s) fun c _ hc ↦ by simp [hc]]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  simp only [Bandits.gaussianMeanVarBandit_apply, hc, ↓reduceIte]
  rw [klDiv_gaussianReal_gaussianReal_add_sq (hθ c hc), ENNReal.ofReal_mul (hw c)]

/-- **The cost of moving the means of some arms.** For Gaussian arms with unknown variances and a
model `θ` with positive variances, the smallest transportation cost to a model with positive
variances whose arms `c ∈ s` have the means `m c` is
`∑ c ∈ s, w c log (1 + (μ_c - m c)² / σ²_c) / 2`. It is attained by moving each arm `c ∈ s` to the
mean `m c` and the variance `σ²_c + (μ_c - m c)²`, and leaving the other arms unchanged. -/
theorem iInf_cost_gaussianMeanVarBandit (hνt : task.ν = Bandits.gaussianMeanVarBandit)
    (hw : 0 ≤ w) (s : Finset α) (m : α → ℝ) (hθ : ∀ c, (θ c).2 ≠ 0) :
    ⨅ (θ' : α → ℝ × ℝ≥0) (_ : (∀ c, (θ' c).2 ≠ 0) ∧ ∀ c ∈ s, (θ' c).1 = m c),
        task.cost w θ θ' =
      ∑ c ∈ s, ENNReal.ofReal (w c * (log (1 + ((θ c).1 - m c) ^ 2 / (θ c).2) / 2)) := by
  classical
  refine le_antisymm ((iInf₂_le _ ⟨fun c ↦ ?_, fun c hc ↦ by simp [hc]⟩).trans
    (cost_gaussianMeanVarBandit_ite hνt hw s m fun c _ ↦ hθ c).le)
    (le_iInf₂ fun θ' hθ' ↦
      sum_ofReal_mul_log_le_cost_gaussianMeanVarBandit hνt hw (fun c _ ↦ hθ c) hθ'.2)
  by_cases hc : c ∈ s <;> simp [hc, hθ c]

/-- **The cost of moving two arms to a common mean** [JDK23, (1)]. For Gaussian arms with unknown
variances, a model `θ` with positive variances, two arms `a ≠ b` and a mean `x`, the smallest
transportation cost to a model with positive variances in which both `a` and `b` have mean `x` is
`w a log (1 + (μ_a - x)² / σ²_a) / 2 + w b log (1 + (μ_b - x)² / σ²_b) / 2`. -/
theorem iInf_cost_gaussianMeanVarBandit_pair (hνt : task.ν = Bandits.gaussianMeanVarBandit)
    (hw : 0 ≤ w) (hθ : ∀ c, (θ c).2 ≠ 0) {a b : α} (hab : a ≠ b) (x : ℝ) :
    ⨅ (θ' : α → ℝ × ℝ≥0) (_ : (∀ c, (θ' c).2 ≠ 0) ∧ (θ' a).1 = x ∧ (θ' b).1 = x),
        task.cost w θ θ' =
      ENNReal.ofReal (w a * (log (1 + ((θ a).1 - x) ^ 2 / (θ a).2) / 2)) +
        ENNReal.ofReal (w b * (log (1 + ((θ b).1 - x) ^ 2 / (θ b).2) / 2)) := by
  classical
  have h := iInf_cost_gaussianMeanVarBandit hνt hw {a, b} (fun _ ↦ x) hθ
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] at h
  rwa [Finset.sum_pair hab] at h

end LMLExplore.Identification.IdentTask
