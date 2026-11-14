/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.Task.BestArm.Basic
import LMLExplore.Analysis.SpecialFunctions.Log.Basic

/-!
# Product models and the transportation costs `K⁻` and `K⁺`

A *product model* describes a bandit whose arms are parametrized independently: for a type `Θ₀`
of arm parameters and arm laws `κ : α → Θ₀ → Measure 𝓨`, a model is a vector `θ : α → Θ₀` of
parameters, and arm `a` of `θ` has law `κ a (θ a)` (`productBandit κ θ`). Each arm `a` comes with
a set `S a ⊆ Θ₀` of admissible parameters and a mean `m a : Θ₀ → ℝ`, so that the questions asked
about the model (which arm has the largest mean, ...) use the mean functional
`θ ↦ (m a (θ a))_a`. Examples are the vectors of means of exponential families (`Θ₀ = ℝ`,
`m a = id`), Gaussian arms with known variances, Gaussian arms with unknown variances
(`Θ₀ = ℝ × ℝ≥0`, `m a = Prod.fst`, `gaussianMeanVarBandit_eq_productBandit`) and Bernoulli arms.

The transportation cost `cost_θ(w, λ) = ∑ a, w a KL(κ_a(θ a), κ_a(λ a))` of a product model is a
sum of per-arm divergences (`IdentTask.cost_eq_sum_of_ν_eq_productBandit`), so the infimum of the
cost over the models in which some arm has mean below (or above) a level `u` reduces to a per-arm
quantity: the smallest divergence from the law of an arm to a law of mean at most (or at least) `u`,
`K⁻_a(x, u) = inf {KL(κ_a(x), κ_a(y)) | y ∈ S a, m a y ≤ u}` and
`K⁺_a(x, u) = inf {KL(κ_a(x), κ_a(y)) | y ∈ S a, u ≤ m a y}`
[AJG20; JDK23a, (1)]. In best arm identification, the cheapest models in which an arm `b` is at
least as good as the arm `a` move `a` down and `b` up to a common level `u`, at the cost
`inf_u (w a K⁻_a(θ a, u) + w b K⁺_b(θ b, u))`, the pairwise transportation cost `C(a, b; w)` of
[AJG20] and [JDK23a, (1)]. The same reduction gives the costs of top-`m` identification (pairs
`a ∈ s`, `b ∉ s`) and of thresholding (one arm on the wrong side of the threshold). For exponential
families in the mean parametrization, `K⁻(μ, u)` is the divergence `d(μ, u)` for means `u ≤ μ`;
for Gaussian arms with unknown variances it is `log (1 + (μ - u)² / σ²) / 2` [JDK23a, Lemma 3].

`LMLExplore.Bandits.dInf` is `K⁺` for the model of all real laws in a class, with a strict
inequality on the mean.

## Main definitions

* `LMLExplore.Identification.productBandit κ θ`: the bandit of the model `θ : α → Θ₀`, with arm
  `a` of law `κ a (θ a)`.
* `LMLExplore.Identification.kInfLower κ S m x u`, `LMLExplore.Identification.kInfUpper κ S m x u`:
  the smallest divergence from `κ x` to a law `κ y`, `y ∈ S`, with mean `m y ≤ u`
  (respectively `u ≤ m y`).

## Main statements

* `LMLExplore.Identification.antitone_kInfLower`, `LMLExplore.Identification.monotone_kInfUpper`:
  `K⁻(x, ·)` is antitone and `K⁺(x, ·)` monotone;
  `LMLExplore.Identification.kInfLower_eq_zero_of_le`,
  `LMLExplore.Identification.kInfUpper_eq_zero_of_le`: for `x ∈ S`, `K⁻(x, u) = 0` from `m x` on
  and `K⁺(x, u) = 0` up to `m x`.
* `LMLExplore.Identification.IdentTask.cost_eq_sum_of_ν_eq_productBandit`: the transportation cost
  of a task on a product model is the weighted sum of the per-arm divergences.
* `LMLExplore.Identification.IdentTask.iInf_cost_eq_ofReal_mul_kInfLower`,
  `LMLExplore.Identification.IdentTask.iInf_cost_eq_ofReal_mul_kInfUpper`: the smallest cost of a
  model of `∏ c, S c` in which arm `a` has mean at most (at least) `u` is `w a K⁻_a(θ a, u)`
  (`w a K⁺_a(θ a, u)`).
* `LMLExplore.Identification.IdentTask.iInf_cost_eq_iInf_kInfLower_add_kInfUpper`: the smallest
  cost of a model of `∏ c, S c` in which arm `b ≠ a` has mean at least that of `a` is
  `inf_u (w a K⁻_a(θ a, u) + w b K⁺_b(θ b, u))` [AJG20; JDK23a, (1)].
* `LMLExplore.Identification.IdentTask.continuousOn_biInf_cost_productBandit`,
  `LMLExplore.Identification.IdentTask.continuousOn_altCost_productBandit`: if the per-arm
  divergences are finite and continuous on `S a ×ˢ S a` with locally relatively compact sublevel
  sets, the cost of any set of alternatives in `∏ a, S a` is jointly continuous in the model and
  the allocation [DK19, Lemmas 25–27];
  `LMLExplore.Identification.IdentTask.continuousOn_gameValue_productBandit`,
  `LMLExplore.Identification.IdentTask.continuousOn_charTime_productBandit`: for finitely many
  answers and admissible models in `∏ a, S a`, `D(θ)` and `T*(θ)` are continuous on the admissible
  models [DK19, Lemmas 27, 29].
* `LMLExplore.Identification.iInf_cost_baiTask_productBandit`,
  `LMLExplore.Identification.iInf_cost_topMTask_productBandit`,
  `LMLExplore.Identification.iInf_cost_thresholdingTask_productBandit`: the infimum of the cost over
  the sets of models, defined by non-strict mean inequalities, that contain the alternatives of best
  arm identification, top-`m` identification and thresholding, as minima of `K⁻`/`K⁺` costs.
* `LMLExplore.Identification.le_altCost_baiTask_productBandit_restrict`,
  `LMLExplore.Identification.le_altCost_topMTask_productBandit_restrict`,
  `LMLExplore.Identification.le_altCost_thresholdingTask_productBandit_restrict`: these minima are
  lower bounds on the costs of the alternatives `D(θ, w, ¬i)`.
* `LMLExplore.Identification.altCost_baiTask_productBandit_restrict_eq`: for real parameters with
  open admissible sets and a continuous transportation cost, `D(θ, w, ¬a)` is
  `min_{b ≠ a} inf_u (w a K⁻_a(θ a, u) + w b K⁺_b(θ b, u))`.
* `LMLExplore.Identification.kInfLower_expFamily`, `LMLExplore.Identification.kInfUpper_expFamily`:
  for an exponential family in the mean parametrization, `K⁻(μ, u) = d(μ, u)` for means `u ≤ μ`
  and `K⁺(μ, u) = d(μ, u)` for means `μ ≤ u`.
* `LMLExplore.Identification.kInfLower_gaussianReal`,
  `LMLExplore.Identification.kInfUpper_gaussianReal`: for Gaussian laws with unknown variance,
  `K⁻((μ, σ²), u) = log (1 + (μ - u)² / σ²) / 2` for `u ≤ μ`, and the same value of `K⁺` for
  `μ ≤ u` [JDK23a, Lemma 3].
* `LMLExplore.Identification.exists_mem_nhds_forall_exists_isCompact_klDiv_gaussianReal`: for
  Gaussian laws with unknown means and variances, every parameter `(μ, σ²)` with `σ² ≠ 0` has a
  neighbourhood near which the sublevel sets of the divergence lie in compact sets of parameters of
  nonzero variance, the per-arm hypothesis of the joint continuity of the cost.
* `LMLExplore.Identification.IdentTask.continuousOn_biInf_cost_gaussianMeanVarBandit`,
  `LMLExplore.Identification.IdentTask.continuousOn_altCost_gaussianMeanVarBandit`: for Gaussian
  arms with unknown variances, the cost of every set of alternatives of nonzero variances, and
  `D(θ, w, ¬i)`, are jointly continuous in the model and the allocation [DK19, Lemmas 25–27];
  `LMLExplore.Identification.IdentTask.continuousOn_gameValue_gaussianMeanVarBandit`,
  `LMLExplore.Identification.IdentTask.continuousOn_charTime_gaussianMeanVarBandit`: for finitely
  many answers and admissible models of nonzero variances, `D(θ)` and `T*(θ)` are continuous on the
  admissible models [DK19, Lemmas 27, 29].

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, supplementary material, Appendix F, Lemmas 25–27.
* [FKV14] E. A. Feinberg, P. O. Kasyanov and M. Voorneveld, *Berge's maximum theorem for
  noncompact image sets*, J. Math. Anal. Appl. 413 (2014).
* [AJG20] S. Agrawal, S. Juneja and P. Glynn, *Optimal δ-correct best-arm selection for
  heavy-tailed distributions*, ALT 2020.
* [JDK23a] M. Jourdan, R. Degenne and E. Kaufmann, *Dealing with unknown variances in best-arm
  identification*, ALT 2023, Section 2 (the transportation costs (1) and Lemma 3).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Real Set

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α 𝓨 Θ₀ ℐ : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}

/-! ### The bandit of a product model -/

section ProductBandit

variable [Countable α] [MeasurableSingletonClass α]

/-- The bandit of the model `θ : α → Θ₀` of the product model with arm laws
`κ : α → Θ₀ → Measure 𝓨`: arm `a` has law `κ a (θ a)`, which depends on the parameter `θ a` of
that arm only. -/
noncomputable def productBandit (κ : α → Θ₀ → Measure 𝓨) (θ : α → Θ₀) : Kernel α 𝓨 :=
  Kernel.ofFunOfCountable fun a ↦ κ a (θ a)

@[simp]
lemma productBandit_apply (κ : α → Θ₀ → Measure 𝓨) (θ : α → Θ₀) (a : α) :
    productBandit κ θ a = κ a (θ a) := (rfl)

instance isMarkovKernel_productBandit (κ : α → Θ₀ → Measure 𝓨)
    [∀ a x, IsProbabilityMeasure (κ a x)] (θ : α → Θ₀) : IsMarkovKernel (productBandit κ θ) :=
  inferInstanceAs (IsMarkovKernel (Kernel.ofFunOfCountable _))

/-- The Gaussian bandit with common variance `σ2` is the product model of the Gaussian laws of
variance `σ2`, parametrized by their means. -/
lemma gaussianBandit_eq_productBandit (μ : α → ℝ) (σ2 : ℝ≥0) :
    Bandits.gaussianBandit μ σ2 = productBandit (fun _ x ↦ gaussianReal x σ2) μ := by
  ext1 a
  simp

/-- The Gaussian bandit with unknown means and variances is the product model of the Gaussian
laws, parametrized by their means and variances. -/
lemma gaussianMeanVarBandit_eq_productBandit (θ : α → ℝ × ℝ≥0) :
    Bandits.gaussianMeanVarBandit θ = productBandit (fun _ p ↦ gaussianReal p.1 p.2) θ := by
  ext1 a
  simp

/-- The Bernoulli bandit is the product model of the Bernoulli laws, parametrized by their
means. -/
lemma bernoulliBandit_eq_productBandit (p : α → unitInterval) :
    Bandits.bernoulliBandit p = productBandit (fun _ q ↦ Ber((1 : ℝ), 0, q)) p := by
  ext1 a
  simp

end ProductBandit

/-! ### The divergences to the laws of mean below or above a level -/

section KInf

variable {κ : Θ₀ → Measure 𝓨} {S : Set Θ₀} {m : Θ₀ → ℝ} {x y : Θ₀} {u : ℝ} {r : ℝ≥0∞}

/-- `K⁻(x, u)`: the smallest relative entropy from the law `κ x` to a law `κ y` with parameter
`y ∈ S` of mean `m y ≤ u` [AJG20; JDK23a, (1)]. It is `∞` if there is no such parameter. -/
noncomputable def kInfLower (κ : Θ₀ → Measure 𝓨) (S : Set Θ₀) (m : Θ₀ → ℝ) (x : Θ₀) (u : ℝ) :
    ℝ≥0∞ :=
  ⨅ y ∈ {y ∈ S | m y ≤ u}, klDiv (κ x) (κ y)

/-- `K⁺(x, u)`: the smallest relative entropy from the law `κ x` to a law `κ y` with parameter
`y ∈ S` of mean `u ≤ m y` [AJG20; JDK23a, (1)]. It is `∞` if there is no such parameter. -/
noncomputable def kInfUpper (κ : Θ₀ → Measure 𝓨) (S : Set Θ₀) (m : Θ₀ → ℝ) (x : Θ₀) (u : ℝ) :
    ℝ≥0∞ :=
  ⨅ y ∈ {y ∈ S | u ≤ m y}, klDiv (κ x) (κ y)

lemma kInfLower_def (κ : Θ₀ → Measure 𝓨) (S : Set Θ₀) (m : Θ₀ → ℝ) (x : Θ₀) (u : ℝ) :
    kInfLower κ S m x u = ⨅ y ∈ {y ∈ S | m y ≤ u}, klDiv (κ x) (κ y) := (rfl)

lemma kInfUpper_def (κ : Θ₀ → Measure 𝓨) (S : Set Θ₀) (m : Θ₀ → ℝ) (x : Θ₀) (u : ℝ) :
    kInfUpper κ S m x u = ⨅ y ∈ {y ∈ S | u ≤ m y}, klDiv (κ x) (κ y) := (rfl)

lemma kInfLower_le (hy : y ∈ S) (hyu : m y ≤ u) : kInfLower κ S m x u ≤ klDiv (κ x) (κ y) := by
  rw [kInfLower_def]
  exact iInf₂_le y ⟨hy, hyu⟩

lemma kInfUpper_le (hy : y ∈ S) (huy : u ≤ m y) : kInfUpper κ S m x u ≤ klDiv (κ x) (κ y) := by
  rw [kInfUpper_def]
  exact iInf₂_le y ⟨hy, huy⟩

lemma le_kInfLower_iff :
    r ≤ kInfLower κ S m x u ↔ ∀ y ∈ S, m y ≤ u → r ≤ klDiv (κ x) (κ y) := by
  simp [kInfLower_def]

lemma le_kInfUpper_iff :
    r ≤ kInfUpper κ S m x u ↔ ∀ y ∈ S, u ≤ m y → r ≤ klDiv (κ x) (κ y) := by
  simp [kInfUpper_def]

lemma kInfLower_lt_iff :
    kInfLower κ S m x u < r ↔ ∃ y ∈ S, m y ≤ u ∧ klDiv (κ x) (κ y) < r := by
  simp [kInfLower_def, iInf_lt_iff, and_assoc]

lemma kInfUpper_lt_iff :
    kInfUpper κ S m x u < r ↔ ∃ y ∈ S, u ≤ m y ∧ klDiv (κ x) (κ y) < r := by
  simp [kInfUpper_def, iInf_lt_iff, and_assoc]

/-- `K⁺` is `K⁻` for the opposite means at the opposite level:
`K⁺(x, u) = inf {KL(κ x, κ y) | y ∈ S, -m y ≤ -u}`. -/
lemma kInfUpper_eq_kInfLower_neg (κ : Θ₀ → Measure 𝓨) (S : Set Θ₀) (m : Θ₀ → ℝ) (x : Θ₀)
    (u : ℝ) : kInfUpper κ S m x u = kInfLower κ S (fun y ↦ -m y) x (-u) := by
  simp [kInfUpper_def, kInfLower_def]

/-- `K⁻(x, u)` is antitone in the level `u`: more laws have mean at most a larger level. -/
lemma antitone_kInfLower (κ : Θ₀ → Measure 𝓨) (S : Set Θ₀) (m : Θ₀ → ℝ) (x : Θ₀) :
    Antitone (kInfLower κ S m x) := fun _ _ huv ↦
  le_kInfLower_iff.2 fun _ hy hyu ↦ kInfLower_le hy (hyu.trans huv)

/-- `K⁺(x, u)` is monotone in the level `u`: fewer laws have mean at least a larger level. -/
lemma monotone_kInfUpper (κ : Θ₀ → Measure 𝓨) (S : Set Θ₀) (m : Θ₀ → ℝ) (x : Θ₀) :
    Monotone (kInfUpper κ S m x) := fun _ _ huv ↦
  le_kInfUpper_iff.2 fun _ hy hvy ↦ kInfUpper_le hy (huv.trans hvy)

/-- For an admissible parameter `x`, `K⁻(x, u) = 0` at every level `u ≥ m x`. -/
lemma kInfLower_eq_zero_of_le [SigmaFinite (κ x)] (hx : x ∈ S) (hxu : m x ≤ u) :
    kInfLower κ S m x u = 0 :=
  nonpos_iff_eq_zero.1 ((kInfLower_le hx hxu).trans (klDiv_self _).le)

/-- For an admissible parameter `x`, `K⁺(x, u) = 0` at every level `u ≤ m x`. -/
lemma kInfUpper_eq_zero_of_le [SigmaFinite (κ x)] (hx : x ∈ S) (hux : u ≤ m x) :
    kInfUpper κ S m x u = 0 :=
  nonpos_iff_eq_zero.1 ((kInfUpper_le hx hux).trans (klDiv_self _).le)

end KInf

/-! ### Transportation costs of product models -/

namespace IdentTask

variable {κ : α → Θ₀ → Measure 𝓨} {task : IdentTask α (α → Θ₀) ℐ 𝓨} {S : α → Set Θ₀}
  {m : α → Θ₀ → ℝ} {θ θ' : α → Θ₀} {w : α → ℝ} {a b : α} {u : ℝ}

/-- The arm laws of a task on a product model are probability measures, since its bandits are
Markov kernels. -/
private lemma isProbabilityMeasure_of_ν_eq_productBandit [Countable α]
    [MeasurableSingletonClass α] (hν : task.ν = productBandit κ) (a : α) (x : Θ₀) :
    IsProbabilityMeasure (κ a x) := by
  have h : IsMarkovKernel (productBandit κ fun _ ↦ x) := hν ▸ task.isMarkovKernel_ν _
  simpa using h.isProbabilityMeasure a

variable [Fintype α] [MeasurableSingletonClass α]

/-- The transportation cost of a task on a product model is the weighted sum of the divergences
between the laws of the arms: `cost_θ(w, θ') = ∑ c, w c KL(κ_c(θ c), κ_c(θ' c))`. -/
lemma cost_eq_sum_of_ν_eq_productBandit (hν : task.ν = productBandit κ) (w : α → ℝ)
    (θ θ' : α → Θ₀) :
    task.cost w θ θ' = ∑ c, ENNReal.ofReal (w c) * klDiv (κ c (θ c)) (κ c (θ' c)) := by
  simp [cost_def, hν]

/-- In a product model, the transportation cost to a model `θ'` that agrees with `θ` outside a
finite set `s` of arms is the weighted sum of the divergences of the arms of `s`. -/
lemma cost_eq_sum_of_forall_notMem_eq (hν : task.ν = productBandit κ) {s : Finset α}
    (h : ∀ c ∉ s, θ' c = θ c) :
    task.cost w θ θ' = ∑ c ∈ s, ENNReal.ofReal (w c) * klDiv (κ c (θ c)) (κ c (θ' c)) := by
  rw [cost_eq_sum_of_ν_eq_productBandit hν]
  refine (Finset.sum_subset (Finset.subset_univ s) fun c _ hc ↦ ?_).symm
  have := isProbabilityMeasure_of_ν_eq_productBandit hν c (θ c)
  rw [h c hc, klDiv_self, mul_zero]

/-- A model `θ'` whose arm `a` has an admissible parameter of mean at most `u` is at cost at least
`w a K⁻_a(θ a, u)` from `θ`. -/
lemma ofReal_mul_kInfLower_le_cost (hν : task.ν = productBandit κ) (hθ' : θ' a ∈ S a)
    (hu : m a (θ' a) ≤ u) :
    ENNReal.ofReal (w a) * kInfLower (κ a) (S a) (m a) (θ a) u ≤ task.cost w θ θ' := by
  rw [cost_eq_sum_of_ν_eq_productBandit hν]
  calc ENNReal.ofReal (w a) * kInfLower (κ a) (S a) (m a) (θ a) u
      ≤ ENNReal.ofReal (w a) * klDiv (κ a (θ a)) (κ a (θ' a)) := by
        gcongr
        exact kInfLower_le hθ' hu
    _ ≤ ∑ c, ENNReal.ofReal (w c) * klDiv (κ c (θ c)) (κ c (θ' c)) :=
        Finset.single_le_sum (f := fun c ↦ ENNReal.ofReal (w c) * klDiv (κ c (θ c)) (κ c (θ' c)))
          (fun _ _ ↦ zero_le) (Finset.mem_univ a)

/-- A model `θ'` whose arm `a` has an admissible parameter of mean at least `u` is at cost at least
`w a K⁺_a(θ a, u)` from `θ`. -/
lemma ofReal_mul_kInfUpper_le_cost (hν : task.ν = productBandit κ) (hθ' : θ' a ∈ S a)
    (hu : u ≤ m a (θ' a)) :
    ENNReal.ofReal (w a) * kInfUpper (κ a) (S a) (m a) (θ a) u ≤ task.cost w θ θ' := by
  simpa [kInfUpper_eq_kInfLower_neg] using
    ofReal_mul_kInfLower_le_cost (m := fun c y ↦ -m c y) (u := -u) (w := w) (θ := θ) hν hθ'
      (neg_le_neg hu)

/-- A model `θ'` in which the arms `a ≠ b` have admissible parameters with
`m a (θ' a) ≤ u ≤ m b (θ' b)` is at cost at least `w a K⁻_a(θ a, u) + w b K⁺_b(θ b, u)` from
`θ`. -/
lemma ofReal_mul_kInfLower_add_ofReal_mul_kInfUpper_le_cost (hν : task.ν = productBandit κ)
    (hab : a ≠ b) (hθ'a : θ' a ∈ S a) (hθ'b : θ' b ∈ S b) (hua : m a (θ' a) ≤ u)
    (hub : u ≤ m b (θ' b)) :
    ENNReal.ofReal (w a) * kInfLower (κ a) (S a) (m a) (θ a) u +
        ENNReal.ofReal (w b) * kInfUpper (κ b) (S b) (m b) (θ b) u ≤ task.cost w θ θ' := by
  classical
  rw [cost_eq_sum_of_ν_eq_productBandit hν]
  calc ENNReal.ofReal (w a) * kInfLower (κ a) (S a) (m a) (θ a) u +
        ENNReal.ofReal (w b) * kInfUpper (κ b) (S b) (m b) (θ b) u
      ≤ ENNReal.ofReal (w a) * klDiv (κ a (θ a)) (κ a (θ' a)) +
          ENNReal.ofReal (w b) * klDiv (κ b (θ b)) (κ b (θ' b)) := by
        gcongr
        exacts [kInfLower_le hθ'a hua, kInfUpper_le hθ'b hub]
    _ = ∑ c ∈ {a, b}, ENNReal.ofReal (w c) * klDiv (κ c (θ c)) (κ c (θ' c)) :=
        (Finset.sum_pair (f := fun c ↦ ENNReal.ofReal (w c) * klDiv (κ c (θ c)) (κ c (θ' c)))
          hab).symm
    _ ≤ ∑ c, ENNReal.ofReal (w c) * klDiv (κ c (θ c)) (κ c (θ' c)) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **The cost of moving one arm below a level.** In a product model, the smallest transportation
cost from an admissible model `θ` to an admissible model whose arm `a` has mean at most `u` is
`w a K⁻_a(θ a, u)`, for a positive weight `w a`. -/
theorem iInf_cost_eq_ofReal_mul_kInfLower (hν : task.ν = productBandit κ) (hθ : θ ∈ univ.pi S)
    (hw : 0 < w a) (u : ℝ) :
    ⨅ θ' ∈ univ.pi S, ⨅ (_ : m a (θ' a) ≤ u), task.cost w θ θ' =
      ENNReal.ofReal (w a) * kInfLower (κ a) (S a) (m a) (θ a) u := by
  classical
  refine le_antisymm ?_ (le_iInf₂ fun θ' hθ' ↦ le_iInf fun hu ↦
    ofReal_mul_kInfLower_le_cost hν (hθ' a (mem_univ a)) hu)
  rw [kInfLower_def]
  simp_rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hw).ne' ENNReal.ofReal_ne_top]
  refine le_iInf₂ fun y hy ↦ ?_
  -- Move the arm `a` of `θ` to the parameter `y`.
  have hθy : Function.update θ a y ∈ univ.pi S := mem_univ_pi.2 fun c ↦ by
    rcases eq_or_ne c a with rfl | hc
    · simpa using hy.1
    · simpa [hc] using hθ c (mem_univ c)
  refine (iInf₂_le _ hθy).trans (iInf_le_of_le (by simpa using hy.2) (le_of_eq ?_))
  rw [cost_eq_sum_of_forall_notMem_eq (s := {a}) hν fun c hc ↦
    Function.update_of_ne (by simpa using hc) _ _]
  simp

/-- **The cost of moving one arm above a level.** In a product model, the smallest transportation
cost from an admissible model `θ` to an admissible model whose arm `a` has mean at least `u` is
`w a K⁺_a(θ a, u)`, for a positive weight `w a`. -/
theorem iInf_cost_eq_ofReal_mul_kInfUpper (hν : task.ν = productBandit κ) (hθ : θ ∈ univ.pi S)
    (hw : 0 < w a) (u : ℝ) :
    ⨅ θ' ∈ univ.pi S, ⨅ (_ : u ≤ m a (θ' a)), task.cost w θ θ' =
      ENNReal.ofReal (w a) * kInfUpper (κ a) (S a) (m a) (θ a) u := by
  simpa [kInfUpper_eq_kInfLower_neg] using
    iInf_cost_eq_ofReal_mul_kInfLower (m := fun c y ↦ -m c y) hν hθ hw (-u)

/-- **The pairwise transportation cost of a product model** [AJG20; JDK23a, (1)]. In a product
model, the smallest transportation cost from an admissible model `θ` to an admissible model in
which the arm `b` has mean at least that of the arm `a ≠ b` is
`inf_u (w a K⁻_a(θ a, u) + w b K⁺_b(θ b, u))`, for positive weights `w a` and `w b`: the cheapest
such models move `a` down and `b` up to a common level `u`. -/
theorem iInf_cost_eq_iInf_kInfLower_add_kInfUpper (hν : task.ν = productBandit κ)
    (hθ : θ ∈ univ.pi S) (hab : a ≠ b) (ha : 0 < w a) (hb : 0 < w b) :
    ⨅ θ' ∈ univ.pi S, ⨅ (_ : m a (θ' a) ≤ m b (θ' b)), task.cost w θ θ' =
      ⨅ u, (ENNReal.ofReal (w a) * kInfLower (κ a) (S a) (m a) (θ a) u +
        ENNReal.ofReal (w b) * kInfUpper (κ b) (S b) (m b) (θ b) u) := by
  classical
  refine le_antisymm (le_iInf fun u ↦ ?_) (le_iInf₂ fun θ' hθ' ↦ le_iInf fun h ↦
    iInf_le_of_le (m a (θ' a)) (ofReal_mul_kInfLower_add_ofReal_mul_kInfUpper_le_cost hν hab
      (hθ' a (mem_univ a)) (hθ' b (mem_univ b)) le_rfl h))
  rw [kInfLower_def, kInfUpper_def]
  simp_rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 ha).ne' ENNReal.ofReal_ne_top,
    ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hb).ne' ENNReal.ofReal_ne_top]
  refine ENNReal.le_iInf₂_add_iInf₂ fun y hy y' hy' ↦ ?_
  -- Move the arm `a` of `θ` to the parameter `y` and the arm `b` to the parameter `y'`.
  set θ' := Function.update (Function.update θ a y) b y'
  have hθ'a : θ' a = y := by simp [θ', hab]
  have hθ'b : θ' b = y' := by simp [θ']
  have hθ' : θ' ∈ univ.pi S := mem_univ_pi.2 fun c ↦ by
    rcases eq_or_ne c a with rfl | hca
    · simpa [hθ'a] using hy.1
    rcases eq_or_ne c b with rfl | hcb
    · simpa [hθ'b] using hy'.1
    · simpa [θ', hca, hcb] using hθ c (mem_univ c)
  refine (iInf₂_le θ' hθ').trans (iInf_le_of_le (by rw [hθ'a, hθ'b]; exact hy.2.trans hy'.2)
    (le_of_eq ?_))
  rw [cost_eq_sum_of_forall_notMem_eq (s := {a, b}) hν fun c hc ↦ ?_, Finset.sum_pair hab,
    hθ'a, hθ'b]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  simp [θ', hc.1, hc.2]

/-! ### Continuity of the cost of the alternatives on product models -/

section Continuity

open Filter Topology

/-- **Continuity of the cost of a set of alternatives on a product model** [DK19, Lemmas 25–27;
FKV14], `continuousOn_biInf_cost_pi` for `productBandit κ`. If the per-arm divergences
`KL(κ_a(x), κ_a(y))` are finite and continuous on `S a ×ˢ S a`, and every `x ∈ S a` has a
neighbourhood `U` in `S a` such that for every finite `r`, the parameters `y ∈ S a` with
`KL(κ_a(x'), κ_a(y)) ≤ r` for some `x' ∈ U` lie in a compact subset of `S a`, then for every set
`A ⊆ ∏ a, S a` of models, the cost `(θ, w) ↦ inf_{θ' ∈ A} cost_θ(w, θ')` is continuous on
`(∏ a, S a) ×ˢ univ`. -/
theorem continuousOn_biInf_cost_productBandit [TopologicalSpace Θ₀]
    (hν : task.ν = productBandit κ)
    (hfin : ∀ a, ∀ x ∈ S a, ∀ y ∈ S a, klDiv (κ a x) (κ a y) ≠ ∞)
    (hcont : ∀ a, ContinuousOn (fun p : Θ₀ × Θ₀ ↦ klDiv (κ a p.1) (κ a p.2)) (S a ×ˢ S a))
    (hcomp : ∀ a, ∀ x ∈ S a, ∃ U ∈ 𝓝[S a] x, ∀ r : ℝ≥0∞, r ≠ ∞ →
      ∃ K ⊆ S a, IsCompact K ∧ ∀ x' ∈ U, ∀ y ∈ S a, klDiv (κ a x') (κ a y) ≤ r → y ∈ K)
    {A : Set (α → Θ₀)} (hA : A ⊆ univ.pi S) :
    ContinuousOn (fun p : (α → Θ₀) × (α → ℝ) ↦ ⨅ θ' ∈ A, task.cost p.2 p.1 θ')
      (univ.pi S ×ˢ univ) := by
  refine task.continuousOn_biInf_cost_pi (k := fun a x y ↦ (klDiv (κ a x) (κ a y)).toReal)
    (fun θ hθ θ' hθ' a ↦ ?_) (fun a ↦ ?_) (fun a x hx ↦ ?_) hA
  · simp only [hν, productBandit_apply]
    exact (ENNReal.ofReal_toReal (hfin a _ (hθ a (mem_univ a)) _ (hθ' a (mem_univ a)))).symm
  · exact ENNReal.continuousOn_toReal.comp (hcont a) fun p hp ↦ hfin a _ hp.1 _ hp.2
  · -- Shrink `U` into `S a`, where the divergences are finite.
    obtain ⟨U, hU, hUK⟩ := hcomp a x hx
    refine ⟨U ∩ S a, inter_mem hU self_mem_nhdsWithin, fun r ↦ ?_⟩
    obtain ⟨K, hKS, hK, hK_mem⟩ := hUK (ENNReal.ofReal r) ENNReal.ofReal_ne_top
    refine ⟨K, hKS, hK, fun x' hx' y hy hxy ↦ hK_mem x' hx'.1 y hy ?_⟩
    rw [← ENNReal.ofReal_toReal (hfin a x' hx'.2 y hy)]
    exact ENNReal.ofReal_le_ofReal hxy

/-- **Continuity of the cost of the alternatives on a product model** [DK19, Lemma 27]: under
the hypotheses of `continuousOn_biInf_cost_productBandit`, if the alternatives to `i` are models
of `∏ a, S a`, then `(θ, w) ↦ D(θ, w, ¬i)` is continuous on `(∏ a, S a) ×ˢ univ`. -/
theorem continuousOn_altCost_productBandit [TopologicalSpace Θ₀] {i : ℐ}
    (hν : task.ν = productBandit κ)
    (hfin : ∀ a, ∀ x ∈ S a, ∀ y ∈ S a, klDiv (κ a x) (κ a y) ≠ ∞)
    (hcont : ∀ a, ContinuousOn (fun p : Θ₀ × Θ₀ ↦ klDiv (κ a p.1) (κ a p.2)) (S a ×ˢ S a))
    (hcomp : ∀ a, ∀ x ∈ S a, ∃ U ∈ 𝓝[S a] x, ∀ r : ℝ≥0∞, r ≠ ∞ →
      ∃ K ⊆ S a, IsCompact K ∧ ∀ x' ∈ U, ∀ y ∈ S a, klDiv (κ a x') (κ a y) ≤ r → y ∈ K)
    (h_alt : task.alt i ⊆ univ.pi S) :
    ContinuousOn (fun p : (α → Θ₀) × (α → ℝ) ↦ task.altCost p.1 p.2 i) (univ.pi S ×ˢ univ) := by
  simp_rw [altCost_def]
  exact continuousOn_biInf_cost_productBandit hν hfin hcont hcomp h_alt

/-- **Continuity of the value of the game on a product model** [DK19, Lemmas 27, 29]. For
finitely many answers, under the hypotheses of `continuousOn_biInf_cost_productBandit`, if the
admissible models are models of `∏ a, S a`, then the value `θ ↦ D(θ)` of the game is continuous
on the admissible models. -/
theorem continuousOn_gameValue_productBandit [TopologicalSpace Θ₀] [Finite ℐ]
    (hν : task.ν = productBandit κ)
    (hfin : ∀ a, ∀ x ∈ S a, ∀ y ∈ S a, klDiv (κ a x) (κ a y) ≠ ∞)
    (hcont : ∀ a, ContinuousOn (fun p : Θ₀ × Θ₀ ↦ klDiv (κ a p.1) (κ a p.2)) (S a ×ˢ S a))
    (hcomp : ∀ a, ∀ x ∈ S a, ∃ U ∈ 𝓝[S a] x, ∀ r : ℝ≥0∞, r ≠ ∞ →
      ∃ K ⊆ S a, IsCompact K ∧ ∀ x' ∈ U, ∀ y ∈ S a, klDiv (κ a x') (κ a y) ≤ r → y ∈ K)
    (hM : task.M ⊆ univ.pi S) :
    ContinuousOn task.gameValue task.M := fun θ hθ ↦
  task.continuousWithinAt_gameValue subset_rfl hθ fun i w hw ↦
    ((continuousOn_altCost_productBandit hν hfin hcont hcomp
      ((task.alt_subset_M i).trans hM)).mono (prod_mono hM (subset_univ _))) (θ, w) ⟨hθ, hw⟩

/-- **Continuity of the characteristic time on a product model** [DK19, Lemmas 27, 29]: under
the hypotheses of `continuousOn_gameValue_productBandit`, the characteristic time `θ ↦ T*(θ)` is
continuous on the admissible models. -/
theorem continuousOn_charTime_productBandit [TopologicalSpace Θ₀] [Finite ℐ]
    (hν : task.ν = productBandit κ)
    (hfin : ∀ a, ∀ x ∈ S a, ∀ y ∈ S a, klDiv (κ a x) (κ a y) ≠ ∞)
    (hcont : ∀ a, ContinuousOn (fun p : Θ₀ × Θ₀ ↦ klDiv (κ a p.1) (κ a p.2)) (S a ×ˢ S a))
    (hcomp : ∀ a, ∀ x ∈ S a, ∃ U ∈ 𝓝[S a] x, ∀ r : ℝ≥0∞, r ≠ ∞ →
      ∃ K ⊆ S a, IsCompact K ∧ ∀ x' ∈ U, ∀ y ∈ S a, klDiv (κ a x') (κ a y) ≤ r → y ∈ K)
    (hM : task.M ⊆ univ.pi S) :
    ContinuousOn task.charTime task.M := fun θ hθ ↦
  task.continuousWithinAt_charTime subset_rfl hθ fun i w hw ↦
    ((continuousOn_altCost_productBandit hν hfin hcont hcomp
      ((task.alt_subset_M i).trans hM)).mono (prod_mono hM (subset_univ _))) (θ, w) ⟨hθ, hw⟩

end Continuity

end IdentTask

/-! ### The classical tasks on product models -/

section Classical

variable [Fintype α] [MeasurableSingletonClass α] {κ : α → Θ₀ → Measure 𝓨}
  [∀ a x, IsProbabilityMeasure (κ a x)] {S : α → Set Θ₀} {m : α → Θ₀ → ℝ} {θ : α → Θ₀}
  {w : α → ℝ}

/-- **The cost of the alternatives of best arm identification on a product model**
[AJG20; JDK23a, (1)]. For an admissible model `θ` and an allocation with positive entries, the
infimum of the transportation cost over the admissible models in which some arm `b ≠ a` is at least
as good as `a` is `min_{b ≠ a} inf_u (w a K⁻_a(θ a, u) + w b K⁺_b(θ b, u))`. This set of models
(defined by non-strict inequalities) contains the alternatives to `a`
(`le_altCost_baiTask_productBandit_restrict`). -/
theorem iInf_cost_baiTask_productBandit (hθ : θ ∈ univ.pi S) (hw : ∀ c, 0 < w c) (a : α) :
    ⨅ θ' ∈ {θ' | θ' ∈ univ.pi S ∧ ∃ b ≠ a, m a (θ' a) ≤ m b (θ' b)},
        (baiTask (productBandit κ) fun θ c ↦ m c (θ c)).cost w θ θ' =
      ⨅ (b) (_ : b ≠ a) (u : ℝ), (ENNReal.ofReal (w a) * kInfLower (κ a) (S a) (m a) (θ a) u +
        ENNReal.ofReal (w b) * kInfUpper (κ b) (S b) (m b) (θ b) u) := by
  have hν : (baiTask (productBandit κ) fun θ c ↦ m c (θ c)).ν = productBandit κ := by simp
  refine le_antisymm (le_iInf₂ fun b hb ↦ ?_) (le_iInf₂ fun θ' ⟨hθ', b, hb, h⟩ ↦
    (iInf₂_le b hb).trans (iInf_le_of_le (m a (θ' a))
      (IdentTask.ofReal_mul_kInfLower_add_ofReal_mul_kInfUpper_le_cost hν hb.symm
        (hθ' a (mem_univ a)) (hθ' b (mem_univ b)) le_rfl h)))
  rw [← IdentTask.iInf_cost_eq_iInf_kInfLower_add_kInfUpper hν hθ hb.symm (hw a) (hw b)]
  exact le_iInf₂ fun θ' hθ' ↦ le_iInf fun h ↦ iInf₂_le θ' ⟨hθ', b, hb, h⟩

/-- **The cost of the alternatives of top-`m` identification on a product model.** For an
admissible model `θ`, a set `s` of arms and an allocation with positive entries, the infimum of the
transportation cost over the admissible models in which some arm `b ∉ s` is at least as good as
some arm `a ∈ s` is `min_{a ∈ s, b ∉ s} inf_u (w a K⁻_a(θ a, u) + w b K⁺_b(θ b, u))`. This set
of models (defined by non-strict inequalities) contains the alternatives to `s`
(`le_altCost_topMTask_productBandit_restrict`). -/
theorem iInf_cost_topMTask_productBandit (hθ : θ ∈ univ.pi S) (hw : ∀ c, 0 < w c) (k : ℕ)
    (s : Finset α) :
    ⨅ θ' ∈ {θ' | θ' ∈ univ.pi S ∧ ∃ a ∈ s, ∃ b ∉ s, m a (θ' a) ≤ m b (θ' b)},
        (topMTask (productBandit κ) (fun θ c ↦ m c (θ c)) k).cost w θ θ' =
      ⨅ (a ∈ s) (b ∉ s) (u : ℝ), (ENNReal.ofReal (w a) *
        kInfLower (κ a) (S a) (m a) (θ a) u +
          ENNReal.ofReal (w b) * kInfUpper (κ b) (S b) (m b) (θ b) u) := by
  have hν : (topMTask (productBandit κ) (fun θ c ↦ m c (θ c)) k).ν = productBandit κ := by simp
  have hab {a b : α} (ha : a ∈ s) (hb : b ∉ s) : a ≠ b := fun h ↦ hb (h ▸ ha)
  refine le_antisymm (le_iInf₂ fun a ha ↦ le_iInf₂ fun b hb ↦ ?_)
    (le_iInf₂ fun θ' ⟨hθ', a, ha, b, hb, h⟩ ↦ (iInf₂_le a ha).trans ((iInf₂_le b hb).trans
      (iInf_le_of_le (m a (θ' a))
        (IdentTask.ofReal_mul_kInfLower_add_ofReal_mul_kInfUpper_le_cost hν (hab ha hb)
          (hθ' a (mem_univ a)) (hθ' b (mem_univ b)) le_rfl h))))
  rw [← IdentTask.iInf_cost_eq_iInf_kInfLower_add_kInfUpper hν hθ (hab ha hb) (hw a) (hw b)]
  exact le_iInf₂ fun θ' hθ' ↦ le_iInf fun h ↦ iInf₂_le θ' ⟨hθ', a, ha, b, hb, h⟩

/-- **The cost of the alternatives of thresholding on a product model.** For an admissible model
`θ`, a set `s` of arms and an allocation with positive entries, the infimum of the transportation
cost over the admissible models in which some arm of `s` has mean at most `γ` or some arm outside
`s` has mean at least `γ` is `min (min_{a ∈ s} w a K⁻_a(θ a, γ)) (min_{a ∉ s} w a K⁺_a(θ a, γ))`.
This set of models (defined by non-strict inequalities) contains the alternatives to `s`
(`le_altCost_thresholdingTask_productBandit_restrict`). -/
theorem iInf_cost_thresholdingTask_productBandit (hθ : θ ∈ univ.pi S) (hw : ∀ c, 0 < w c)
    (γ : ℝ) (s : Finset α) :
    ⨅ θ' ∈ {θ' | θ' ∈ univ.pi S ∧ ((∃ a ∈ s, m a (θ' a) ≤ γ) ∨ ∃ a ∉ s, γ ≤ m a (θ' a))},
        (thresholdingTask (productBandit κ) (fun θ c ↦ m c (θ c)) γ).cost w θ θ' =
      (⨅ a ∈ s, ENNReal.ofReal (w a) * kInfLower (κ a) (S a) (m a) (θ a) γ) ⊓
        ⨅ a ∉ s, ENNReal.ofReal (w a) * kInfUpper (κ a) (S a) (m a) (θ a) γ := by
  have hν : (thresholdingTask (productBandit κ) (fun θ c ↦ m c (θ c)) γ).ν = productBandit κ := by
    simp
  refine le_antisymm (le_inf (le_iInf₂ fun a ha ↦ ?_) (le_iInf₂ fun a ha ↦ ?_))
    (le_iInf₂ fun θ' ⟨hθ', h⟩ ↦ ?_)
  · rw [← IdentTask.iInf_cost_eq_ofReal_mul_kInfLower hν hθ (hw a)]
    exact le_iInf₂ fun θ' hθ' ↦ le_iInf fun h ↦ iInf₂_le θ' ⟨hθ', Or.inl ⟨a, ha, h⟩⟩
  · rw [← IdentTask.iInf_cost_eq_ofReal_mul_kInfUpper hν hθ (hw a)]
    exact le_iInf₂ fun θ' hθ' ↦ le_iInf fun h ↦ iInf₂_le θ' ⟨hθ', Or.inr ⟨a, ha, h⟩⟩
  · rcases h with ⟨a, ha, h⟩ | ⟨a, ha, h⟩
    · exact inf_le_left.trans ((iInf₂_le a ha).trans
        (IdentTask.ofReal_mul_kInfLower_le_cost hν (hθ' a (mem_univ a)) h))
    · exact inf_le_right.trans ((iInf₂_le a ha).trans
        (IdentTask.ofReal_mul_kInfUpper_le_cost hν (hθ' a (mem_univ a)) h))

/-- **A lower bound on the cost of the alternatives of best arm identification on a product
model.** For every allocation, `min_{b ≠ a} inf_u (w a K⁻_a(θ a, u) + w b K⁺_b(θ b, u))` is at
most `D(θ, w, ¬a)`, within the admissible models. -/
theorem le_altCost_baiTask_productBandit_restrict (θ : α → Θ₀) (w : α → ℝ) (a : α) :
    ⨅ (b) (_ : b ≠ a) (u : ℝ), (ENNReal.ofReal (w a) * kInfLower (κ a) (S a) (m a) (θ a) u +
        ENNReal.ofReal (w b) * kInfUpper (κ b) (S b) (m b) (θ b) u) ≤
      ((baiTask (productBandit κ) fun θ c ↦ m c (θ c)).restrict (univ.pi S)).altCost θ w a := by
  rw [IdentTask.altCost_def]
  refine le_iInf₂ fun θ' hθ' ↦ ?_
  simp only [IdentTask.alt_restrict, mem_inter_iff, IdentTask.mem_alt_iff] at hθ'
  obtain ⟨⟨-, hθ'a⟩, hθ'S⟩ := hθ'
  simp only [correct_baiTask, mem_ofPred_eq, not_forall, not_lt, exists_prop] at hθ'a
  obtain ⟨b, hb, h⟩ := hθ'a
  exact (iInf₂_le b hb).trans (iInf_le_of_le (m a (θ' a))
    (IdentTask.ofReal_mul_kInfLower_add_ofReal_mul_kInfUpper_le_cost (by simp) hb.symm
      (hθ'S a (mem_univ a)) (hθ'S b (mem_univ b)) le_rfl h))

/-- **A lower bound on the cost of the alternatives of top-`m` identification on a product
model.** For a set `s` of `k` arms and every allocation,
`min_{a ∈ s, b ∉ s} inf_u (w a K⁻_a(θ a, u) + w b K⁺_b(θ b, u))` is at most `D(θ, w, ¬s)`, within
the admissible models. -/
theorem le_altCost_topMTask_productBandit_restrict {k : ℕ} {s : Finset α} (hs : s.card = k)
    (θ : α → Θ₀) (w : α → ℝ) :
    ⨅ (a ∈ s) (b ∉ s) (u : ℝ), (ENNReal.ofReal (w a) * kInfLower (κ a) (S a) (m a) (θ a) u +
        ENNReal.ofReal (w b) * kInfUpper (κ b) (S b) (m b) (θ b) u) ≤
      ((topMTask (productBandit κ) (fun θ c ↦ m c (θ c)) k).restrict (univ.pi S)).altCost
        θ w s := by
  rw [IdentTask.altCost_def]
  refine le_iInf₂ fun θ' hθ' ↦ ?_
  simp only [IdentTask.alt_restrict, mem_inter_iff, IdentTask.mem_alt_iff] at hθ'
  obtain ⟨⟨-, hθ's⟩, hθ'S⟩ := hθ'
  simp only [correct_topMTask, mem_ofPred_eq, hs, true_and, not_forall, not_lt,
    exists_prop] at hθ's
  obtain ⟨a, ha, b, hb, h⟩ := hθ's
  exact (iInf₂_le a ha).trans ((iInf₂_le b hb).trans (iInf_le_of_le (m a (θ' a))
    (IdentTask.ofReal_mul_kInfLower_add_ofReal_mul_kInfUpper_le_cost (by simp)
      (fun h ↦ hb (h ▸ ha)) (hθ'S a (mem_univ a)) (hθ'S b (mem_univ b)) le_rfl h)))

/-- **A lower bound on the cost of the alternatives of thresholding on a product model.** For a
set `s` of arms and every allocation,
`min (min_{a ∈ s} w a K⁻_a(θ a, γ)) (min_{a ∉ s} w a K⁺_a(θ a, γ))` is at most `D(θ, w, ¬s)`,
within the admissible models. -/
theorem le_altCost_thresholdingTask_productBandit_restrict (γ : ℝ) (s : Finset α) (θ : α → Θ₀)
    (w : α → ℝ) :
    (⨅ a ∈ s, ENNReal.ofReal (w a) * kInfLower (κ a) (S a) (m a) (θ a) γ) ⊓
        (⨅ a ∉ s, ENNReal.ofReal (w a) * kInfUpper (κ a) (S a) (m a) (θ a) γ) ≤
      ((thresholdingTask (productBandit κ) (fun θ c ↦ m c (θ c)) γ).restrict
        (univ.pi S)).altCost θ w s := by
  rw [IdentTask.altCost_def]
  refine le_iInf₂ fun θ' hθ' ↦ ?_
  simp only [IdentTask.alt_restrict, mem_inter_iff, IdentTask.mem_alt_iff] at hθ'
  obtain ⟨⟨-, hθ's⟩, hθ'S⟩ := hθ'
  simp only [correct_thresholdingTask, mem_ofPred_eq, not_forall] at hθ's
  obtain ⟨a, ha⟩ := hθ's
  by_cases has : a ∈ s
  · exact inf_le_left.trans ((iInf₂_le a has).trans
      (IdentTask.ofReal_mul_kInfLower_le_cost (by simp) (hθ'S a (mem_univ a))
        (not_lt.1 fun h ↦ ha (iff_of_true has h))))
  · exact inf_le_right.trans ((iInf₂_le a has).trans
      (IdentTask.ofReal_mul_kInfUpper_le_cost (by simp) (hθ'S a (mem_univ a))
        (not_not.1 fun h ↦ ha (iff_of_false has h)).le))

end Classical

/-- **The cost of the alternatives of best arm identification on a product model with real
parameters.** Let the parameters be real, with open admissible sets `S c` and means
`m c = id`, let `θ` be admissible, `w` an allocation with positive entries and the transportation
cost from `θ` continuous on the admissible models in which some arm `b ≠ a` is at least as good as
`a`. Then `D(θ, w, ¬a) = min_{b ≠ a} inf_u (w a K⁻_a(θ a, u) + w b K⁺_b(θ b, u))`
[AJG20; JDK23a, (1)]. -/
theorem altCost_baiTask_productBandit_restrict_eq [Fintype α] [MeasurableSingletonClass α]
    {κ : α → ℝ → Measure 𝓨} [∀ a x, IsProbabilityMeasure (κ a x)] {S : α → Set ℝ}
    (hS : ∀ c, IsOpen (S c)) {θ w : α → ℝ} (hθ : θ ∈ univ.pi S) (hw : ∀ c, 0 < w c) {a : α}
    (hc : ContinuousOn ((baiTask (productBandit κ) id).cost w θ)
      ({θ' | ∃ b ≠ a, θ' a ≤ θ' b} ∩ univ.pi S)) :
    ((baiTask (productBandit κ) id).restrict (univ.pi S)).altCost θ w a =
      ⨅ (b) (_ : b ≠ a) (u : ℝ), (ENNReal.ofReal (w a) * kInfLower (κ a) (S a) id (θ a) u +
        ENNReal.ofReal (w b) * kInfUpper (κ b) (S b) id (θ b) u) := by
  rw [altCost_baiTask_restrict_eq_iInf _ (isOpen_set_pi finite_univ fun c _ ↦ hS c) hc]
  refine iInf_congr fun b ↦ iInf_congr fun hb ↦ ?_
  exact IdentTask.iInf_cost_eq_iInf_kInfLower_add_kInfUpper (m := fun _ ↦ id) (by simp) hθ
    hb.symm (hw a) (hw b)

/-! ### Instances -/

section ExpFamily

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {μ u : ℝ}

/-- For an exponential family in the mean parametrization, `K⁻(μ, u)` is the divergence `d(μ, u)`
for means `u ≤ μ` of the family: the closest member of mean at most `u` is the member of mean
`u`. -/
theorem kInfLower_expFamily (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hμ : μ ∈ ρ.expFamilyMeans T)
    (hu : u ∈ ρ.expFamilyMeans T) (huμ : u ≤ μ) :
    kInfLower (fun x ↦ ρ.expFamily T (ρ.natParam T x)) (ρ.expFamilyMeans T) id μ u =
      ENNReal.ofReal (ρ.expFamilyDiv T μ u) := by
  refine le_antisymm ((kInfLower_le hu le_rfl).trans_eq (Measure.klDiv_expFamily_natParam hμ hu))
    (le_kInfLower_iff.2 fun y hy hyu ↦ ?_)
  rw [Measure.klDiv_expFamily_natParam hμ hy]
  exact ENNReal.ofReal_le_ofReal (Measure.expFamilyDiv_le_expFamilyDiv_of_mem_uIcc hT hu hy
    (mem_uIcc.2 (Or.inr ⟨hyu, huμ⟩)))

/-- For an exponential family in the mean parametrization, `K⁺(μ, u)` is the divergence `d(μ, u)`
for means `μ ≤ u` of the family: the closest member of mean at least `u` is the member of mean
`u`. -/
theorem kInfUpper_expFamily (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) (hμ : μ ∈ ρ.expFamilyMeans T)
    (hu : u ∈ ρ.expFamilyMeans T) (hμu : μ ≤ u) :
    kInfUpper (fun x ↦ ρ.expFamily T (ρ.natParam T x)) (ρ.expFamilyMeans T) id μ u =
      ENNReal.ofReal (ρ.expFamilyDiv T μ u) := by
  refine le_antisymm ((kInfUpper_le hu le_rfl).trans_eq (Measure.klDiv_expFamily_natParam hμ hu))
    (le_kInfUpper_iff.2 fun y hy huy ↦ ?_)
  rw [Measure.klDiv_expFamily_natParam hμ hy]
  exact ENNReal.ofReal_le_ofReal (Measure.expFamilyDiv_le_expFamilyDiv_of_mem_uIcc hT hu hy
    (mem_uIcc.2 (Or.inl ⟨hμu, huy⟩)))

end ExpFamily

section Gaussian

open Topology

variable {μ u : ℝ} {v : ℝ≥0}

/-- **`K⁻` for Gaussian laws with unknown variance** [JDK23a, Lemma 3]. For the Gaussian laws
`𝒩(μ', σ'²)` with positive variances, parametrized by `(μ', σ'²)`, and a level `u ≤ μ`,
`K⁻((μ, σ²), u) = log (1 + (μ - u)² / σ²) / 2`. -/
theorem kInfLower_gaussianReal (hv : v ≠ 0) (huμ : u ≤ μ) :
    kInfLower (fun p : ℝ × ℝ≥0 ↦ gaussianReal p.1 p.2) {p | p.2 ≠ 0} Prod.fst (μ, v) u =
      ENNReal.ofReal (log (1 + (μ - u) ^ 2 / v) / 2) := by
  refine le_antisymm ((kInfLower_le (y := (u, v + ((μ - u) ^ 2).toNNReal)) (by simp [hv])
    le_rfl).trans_eq (klDiv_gaussianReal_gaussianReal_add_sq hv))
    (le_kInfLower_iff.2 fun y _ hyu ↦ ?_)
  refine le_trans ?_ (ofReal_log_one_add_div_le_klDiv_gaussianReal (μ₂ := y.1) hv y.2)
  have h : (μ - u) ^ 2 ≤ (μ - y.1) ^ 2 := pow_le_pow_left₀ (sub_nonneg.2 huμ) (by linarith) 2
  gcongr

/-- **`K⁺` for Gaussian laws with unknown variance** [JDK23a, Lemma 3]. For the Gaussian laws
`𝒩(μ', σ'²)` with positive variances, parametrized by `(μ', σ'²)`, and a level `μ ≤ u`,
`K⁺((μ, σ²), u) = log (1 + (μ - u)² / σ²) / 2`. -/
theorem kInfUpper_gaussianReal (hv : v ≠ 0) (hμu : μ ≤ u) :
    kInfUpper (fun p : ℝ × ℝ≥0 ↦ gaussianReal p.1 p.2) {p | p.2 ≠ 0} Prod.fst (μ, v) u =
      ENNReal.ofReal (log (1 + (μ - u) ^ 2 / v) / 2) := by
  refine le_antisymm ((kInfUpper_le (y := (u, v + ((μ - u) ^ 2).toNNReal)) (by simp [hv])
    le_rfl).trans_eq (klDiv_gaussianReal_gaussianReal_add_sq hv))
    (le_kInfUpper_iff.2 fun y _ huy ↦ ?_)
  refine le_trans ?_ (ofReal_log_one_add_div_le_klDiv_gaussianReal (μ₂ := y.1) hv y.2)
  have h : (μ - u) ^ 2 ≤ (μ - y.1) ^ 2 := by nlinarith
  gcongr

/-- If `D(𝒩(μ, v), 𝒩(μ', v')) ≤ R` for positive variances, then the variance ratio is bounded on
both sides and so is the distance between the means: `v / (4 R + 2) ≤ v' ≤ v exp (1 + 2 R)` and
`(μ - μ')² ≤ 2 R v'`. With `s = v / v'`, the divergence is
`(s - 1 - log s + (μ - μ')² / v') / 2`, and `s - 1 - log s` is at least `0`, `s / 2 - 1` and
`-1 - log s`. -/
private lemma le_and_le_and_sq_le_of_klDiv_le {μ μ' v v' R : ℝ} (hv : 0 < v) (hv' : 0 < v')
    (h : (log (v' / v) + (v + (μ - μ') ^ 2) / v' - 1) / 2 ≤ R) :
    v / (4 * R + 2) ≤ v' ∧ v' ≤ v * exp (1 + 2 * R) ∧ (μ - μ') ^ 2 ≤ 2 * R * v' := by
  have hs : 0 < v / v' := div_pos hv hv'
  have h_log : log (v' / v) = -log (v / v') := by rw [← log_inv, inv_div]
  have hq : 0 ≤ (μ - μ') ^ 2 / v' := div_nonneg (sq_nonneg _) hv'.le
  rw [h_log, add_div] at h
  have h₀ := log_le_sub_one_of_pos hs
  -- `log s ≤ s / e ≤ s / 2`
  have h₁ := log_le_rpow_div_exp_one_mul hs.le one_pos
  rw [rpow_one, mul_one] at h₁
  have he : v / v' / exp 1 ≤ v / v' / 2 :=
    div_le_div_of_nonneg_left hs.le two_pos (by linarith [add_one_lt_exp one_ne_zero])
  refine ⟨?_, ?_, ?_⟩
  · have h4 : 0 < 4 * R + 2 := by linarith
    have : v / v' ≤ 4 * R + 2 := by linarith
    rw [div_le_iff₀ hv'] at this
    rw [div_le_iff₀ h4]
    linarith
  · have : log (v' / v) ≤ 1 + 2 * R := by rw [h_log]; linarith
    rw [log_le_iff_le_exp (div_pos hv' hv), div_le_iff₀ hv] at this
    linarith
  · have : (μ - μ') ^ 2 / v' ≤ 2 * R := by linarith
    rwa [div_le_iff₀ hv'] at this

/-- **Locally relatively compact sublevel sets of the Gaussian divergence** with unknown means and
variances [DK19, Appendix F]. Every parameter `x = (μ, σ²)` with `σ² ≠ 0` has a neighbourhood `U`
such that, for every finite `r`, the parameters `y = (μ', σ'²)` with `σ'² ≠ 0` and
`KL(𝒩(x'), 𝒩(y)) ≤ r` for some `x' ∈ U` lie in a compact set of parameters of nonzero variance:
the divergence tends to infinity as `σ'² → 0`, as `σ'² → ∞`, and as `|μ'| → ∞` with a bounded
variance. This is the per-arm hypothesis of the joint continuity of the cost
(`IdentTask.continuousOn_biInf_cost_productBandit`) for the two-parameter Gaussian model. -/
theorem exists_mem_nhds_forall_exists_isCompact_klDiv_gaussianReal {x : ℝ × ℝ≥0} (hx : x.2 ≠ 0) :
    ∃ U ∈ 𝓝 x, ∀ r : ℝ≥0∞, r ≠ ∞ → ∃ K ⊆ {p : ℝ × ℝ≥0 | p.2 ≠ 0}, IsCompact K ∧
      ∀ x' ∈ U, ∀ y ∈ {p : ℝ × ℝ≥0 | p.2 ≠ 0},
        klDiv (gaussianReal x'.1 x'.2) (gaussianReal y.1 y.2) ≤ r → y ∈ K := by
  obtain ⟨μ₀, v₀⟩ := x
  have hv₀ : (0 : ℝ) < v₀ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hx)
  -- `U` is the set of parameters with mean within `1` of `μ₀` and variance in `(v₀ / 2, 2 v₀)`.
  refine ⟨(fun p : ℝ × ℝ≥0 ↦ (p.1, (p.2 : ℝ))) ⁻¹'
      (Ioo (μ₀ - 1) (μ₀ + 1) ×ˢ Ioo ((v₀ : ℝ) / 2) (2 * v₀)),
    ((isOpen_Ioo.prod isOpen_Ioo).preimage (by fun_prop)).mem_nhds
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, fun r hr ↦ ?_⟩
  set R := r.toReal
  have hR : 0 ≤ R := ENNReal.toReal_nonneg
  -- Bounds on the variance and the mean of the parameters at divergence at most `R`.
  set a := v₀ / 2 / (4 * R + 2)
  set b := 2 * v₀ * exp (1 + 2 * R)
  have ha : 0 < a := by positivity
  refine ⟨Icc (μ₀ - 1 - √(2 * R * b)) (μ₀ + 1 + √(2 * R * b)) ×ˢ Icc a.toNNReal b.toNNReal,
    fun p hp ↦ (lt_of_lt_of_le (Real.toNNReal_pos.2 ha) hp.2.1).ne',
    isCompact_Icc.prod isCompact_Icc, ?_⟩
  rintro ⟨μ, v⟩ ⟨⟨hμ₁, hμ₂⟩, ⟨hv₁, hv₂⟩⟩ ⟨μ', v'⟩ (hv' : v' ≠ 0) hle
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp only [NNReal.coe_zero] at hv₁
    linarith
  have hvpos : (0 : ℝ) < v := by linarith
  rw [klDiv_gaussianReal_gaussianReal hv0 hv', ENNReal.ofReal_le_iff_le_toReal hr] at hle
  obtain ⟨h₁, h₂, h₃⟩ := le_and_le_and_sq_le_of_klDiv_le hvpos
    (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv')) hle
  have h_lo : a ≤ v' := (div_le_div_of_nonneg_right hv₁.le (by linarith)).trans h₁
  have h_hi : (v' : ℝ) ≤ b := h₂.trans (mul_le_mul_of_nonneg_right hv₂.le (exp_pos _).le)
  have h_abs : |μ - μ'| ≤ √(2 * R * b) :=
    abs_le_sqrt (h₃.trans (mul_le_mul_of_nonneg_left h_hi (by positivity)))
  rw [abs_le] at h_abs
  exact ⟨⟨by linarith, by linarith⟩, Real.toNNReal_le_iff_le_coe.2 h_lo,
    (Real.le_toNNReal_iff_coe_le (by positivity)).2 h_hi⟩

end Gaussian

namespace IdentTask

variable [Fintype α] [MeasurableSingletonClass α] {task : IdentTask α (α → ℝ × ℝ≥0) ℐ ℝ} {i : ℐ}

open Topology in
/-- The per-arm sublevel-compactness hypothesis of `continuousOn_biInf_cost_productBandit` for
Gaussian laws on the parameters of nonzero variance, relative to that set of parameters. -/
private lemma exists_mem_nhdsWithin_forall_exists_isCompact_klDiv_gaussianReal :
    ∀ x ∈ {p : ℝ × ℝ≥0 | p.2 ≠ 0}, ∃ U ∈ 𝓝[{p : ℝ × ℝ≥0 | p.2 ≠ 0}] x,
      ∀ r : ℝ≥0∞, r ≠ ∞ → ∃ K ⊆ {p : ℝ × ℝ≥0 | p.2 ≠ 0}, IsCompact K ∧
        ∀ x' ∈ U, ∀ y ∈ {p : ℝ × ℝ≥0 | p.2 ≠ 0},
          klDiv (gaussianReal x'.1 x'.2) (gaussianReal y.1 y.2) ≤ r → y ∈ K := fun _ hx ↦
  let ⟨U, hU, hUK⟩ := exists_mem_nhds_forall_exists_isCompact_klDiv_gaussianReal hx
  ⟨U, mem_nhdsWithin_of_mem_nhds hU, hUK⟩

/-- **Continuity of the cost of a set of alternatives for Gaussian arms with unknown variances**
[DK19, Lemmas 25–27]. For a task on the models `θ : α → ℝ × ℝ≥0` of Gaussian arms with unknown
means and variances, and every set `A` of models of nonzero variances, compact or not, the cost
`(θ, w) ↦ inf_{θ' ∈ A} cost_θ(w, θ')` is continuous on the models of nonzero variances and all
allocations. -/
theorem continuousOn_biInf_cost_gaussianMeanVarBandit
    (hν : task.ν = Bandits.gaussianMeanVarBandit) {A : Set (α → ℝ × ℝ≥0)}
    (hA : A ⊆ univ.pi fun _ ↦ {p | p.2 ≠ 0}) :
    ContinuousOn (fun p : (α → ℝ × ℝ≥0) × (α → ℝ) ↦ ⨅ θ' ∈ A, task.cost p.2 p.1 θ')
      ((univ.pi fun _ ↦ {p : ℝ × ℝ≥0 | p.2 ≠ 0}) ×ˢ univ) :=
  continuousOn_biInf_cost_productBandit (hν.trans (funext gaussianMeanVarBandit_eq_productBandit))
    (fun _ _ hx _ hy ↦ klDiv_gaussianReal_gaussianReal_ne_top hx hy)
    (fun _ ↦ continuousOn_klDiv_gaussianReal)
    (fun _ ↦ exists_mem_nhdsWithin_forall_exists_isCompact_klDiv_gaussianReal) hA

/-- **Continuity of the cost of the alternatives for Gaussian arms with unknown variances**
[DK19, Lemma 27]: for a task on the models of Gaussian arms with unknown means and variances whose
alternatives to `i` have nonzero variances, `(θ, w) ↦ D(θ, w, ¬i)` is continuous on the models of
nonzero variances and all allocations. -/
theorem continuousOn_altCost_gaussianMeanVarBandit (hν : task.ν = Bandits.gaussianMeanVarBandit)
    (h_alt : task.alt i ⊆ univ.pi fun _ ↦ {p | p.2 ≠ 0}) :
    ContinuousOn (fun p : (α → ℝ × ℝ≥0) × (α → ℝ) ↦ task.altCost p.1 p.2 i)
      ((univ.pi fun _ ↦ {p : ℝ × ℝ≥0 | p.2 ≠ 0}) ×ˢ univ) := by
  simp_rw [altCost_def]
  exact continuousOn_biInf_cost_gaussianMeanVarBandit hν h_alt

/-- **Continuity of the value of the game for Gaussian arms with unknown variances**
[DK19, Lemmas 27, 29]: for a task with finitely many answers on the models of Gaussian arms with
unknown means and variances whose admissible models have nonzero variances, `θ ↦ D(θ)` is
continuous on the admissible models. -/
theorem continuousOn_gameValue_gaussianMeanVarBandit [Finite ℐ]
    (hν : task.ν = Bandits.gaussianMeanVarBandit) (hM : task.M ⊆ univ.pi fun _ ↦ {p | p.2 ≠ 0}) :
    ContinuousOn task.gameValue task.M :=
  continuousOn_gameValue_productBandit (hν.trans (funext gaussianMeanVarBandit_eq_productBandit))
    (fun _ _ hx _ hy ↦ klDiv_gaussianReal_gaussianReal_ne_top hx hy)
    (fun _ ↦ continuousOn_klDiv_gaussianReal)
    (fun _ ↦ exists_mem_nhdsWithin_forall_exists_isCompact_klDiv_gaussianReal) hM

/-- **Continuity of the characteristic time for Gaussian arms with unknown variances**
[DK19, Lemmas 27, 29]: under the hypotheses of `continuousOn_gameValue_gaussianMeanVarBandit`,
`θ ↦ T*(θ)` is continuous on the admissible models. -/
theorem continuousOn_charTime_gaussianMeanVarBandit [Finite ℐ]
    (hν : task.ν = Bandits.gaussianMeanVarBandit) (hM : task.M ⊆ univ.pi fun _ ↦ {p | p.2 ≠ 0}) :
    ContinuousOn task.charTime task.M :=
  continuousOn_charTime_productBandit (hν.trans (funext gaussianMeanVarBandit_eq_productBandit))
    (fun _ _ hx _ hy ↦ klDiv_gaussianReal_gaussianReal_ne_top hx hy)
    (fun _ ↦ continuousOn_klDiv_gaussianReal)
    (fun _ ↦ exists_mem_nhdsWithin_forall_exists_isCompact_klDiv_gaussianReal) hM

end IdentTask

end LMLExplore.Identification
