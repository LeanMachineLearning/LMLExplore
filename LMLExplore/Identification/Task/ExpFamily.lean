/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.Instances
public import LMLExplore.Identification.Task.TransportationCost
public import LMLExplore.Probability.Distributions.ExponentialFamily.Mean

/-!
# Transportation costs of arms in exponential families

Let the models of an identification task be vectors of means `μ : α → ℝ`, and let the arm `c`
belong to an exponential family `(ρ c, T c)` with divergence `d_c` in the mean parametrization, in
the sense that `KL(ν_c(μ), ν_c(μ')) = d_c(μ c, μ' c)` for all vectors of means `μ'` of the
families. Then the transportation cost from `μ` to such a `μ'` is
`cost_μ(w, μ') = ∑ c, w c d_c(μ c, μ' c)`. This file collects the consequences of this formula used
to compute the cost of the alternatives of tasks on vectors of means (best arm identification,
thresholding, minimum threshold): the cost of moving a single arm, and the bounds on the cost of
the alternatives obtained by moving one arm, or several arms along a path, to a mean `γ` or across
it.

## Main statements

* `LMLExplore.Identification.IdentTask.cost_eq_sum_ofReal_mul_expFamilyDiv`: on the vectors of
  means of the families, `cost_μ(w, μ') = ∑ c, w c d_c(μ c, μ' c)`.
* `LMLExplore.Identification.IdentTask.cost_update_eq_ofReal_mul_expFamilyDiv`: moving the mean of
  the arm `a` of `μ` to a mean `x` of its family costs `w a d_a(μ a, x)`.
* `LMLExplore.Identification.IdentTask.altCost_le_ofReal_mul_expFamilyDiv_of_eventually`: if
  moving the arm `a` to any mean `x` near `γ` (along a filter) gives an alternative to `i`, then
  `D(μ, w, ¬i) ≤ w a d_a(μ a, γ)`.
* `LMLExplore.Identification.IdentTask.altCost_le_sum_ofReal_mul_expFamilyDiv_of_tendsto`: if
  alternatives to `i` converge to a vector of means `μ'` of the families, then
  `D(μ, w, ¬i) ≤ ∑ c, w c d_c(μ c, μ' c)`.
* `LMLExplore.Identification.IdentTask.altCost_le_sum_ofReal_mul_expFamilyDiv_of_eventually`: if
  moving the arms along a continuous path `μx` gives alternatives to `i` near `γ` (along a
  filter), then `D(μ, w, ¬i) ≤ ∑ c, w c d_c(μ c, μx γ c)`.
* `LMLExplore.Identification.IdentTask.altCost_restrict_le_ofReal_mul_expFamilyDiv_of_tendsto`:
  if alternatives to `i` converge to the vector obtained from `μ` by moving the arm `a` to a mean
  `γ` of its family, then `D(μ, w, ¬i) ≤ w a d_a(μ a, γ)` within the vectors of means of the
  families.
* `LMLExplore.Identification.IdentTask.ofReal_mul_expFamilyDiv_le_cost`: if `γ` lies between
  `μ a` and `μ' a`, then `w a d_a(μ a, γ) ≤ cost_μ(w, μ')`.
* `LMLExplore.Identification.IdentTask.cost_gaussianBandit`: for Gaussian arms with a common
  variance `σ2`, `cost_μ(w, μ') = ∑ c, w c (μ c - μ' c)² / (2 σ2)`.
* `LMLExplore.Identification.IdentTask.cost_bernoulliBandit`: for Bernoulli arms,
  `cost_μ(w, μ') = ∑ c, w c d(μ c, μ' c)` with the binary relative entropy `d`.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Measure Set

open scoped ENNReal NNReal

namespace LMLExplore.Identification.IdentTask

variable {α 𝓨 ℐ : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} [Fintype α]
  {ρ : α → Measure 𝓨} {T : α → 𝓨 → ℝ} {γ : ℝ} {μ w : α → ℝ}
  {task : IdentTask α (α → ℝ) ℐ 𝓨} {i : ℐ} {ν : (α → ℝ) → Kernel α 𝓨}

/-- On the vectors of means of the families, the transportation cost from `μ` to `μ'` is
`∑ c, w c d_c(μ c, μ' c)` when the divergences between the arm laws are those of the families. -/
lemma cost_eq_sum_ofReal_mul_expFamilyDiv
    (hνt : task.ν = ν) (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hw : 0 ≤ w) {μ' : α → ℝ} (hμ' : ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) :
    task.cost w μ μ' = ∑ c, ENNReal.ofReal (w c * (ρ c).expFamilyDiv (T c) (μ c) (μ' c)) := by
  rw [cost_def, hνt]
  exact Finset.sum_congr rfl fun c _ ↦ by rw [hν μ' hμ' c, ENNReal.ofReal_mul (hw c)]

/-- Moving the mean of the arm `a` of `μ` to a mean `x` of its family costs `w a d_a(μ a, x)`. -/
lemma cost_update_eq_ofReal_mul_expFamilyDiv [DecidableEq α]
    (hνt : task.ν = ν) (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hw : 0 ≤ w) (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c)) (a : α) {x : ℝ}
    (hx : x ∈ (ρ a).expFamilyMeans (T a)) :
    task.cost w μ (Function.update μ a x) =
      ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) x) := by
  have hμx : ∀ c, Function.update μ a x c ∈ (ρ c).expFamilyMeans (T c) :=
    (Function.forall_update_iff μ fun c y ↦ y ∈ (ρ c).expFamilyMeans (T c)).2
      ⟨hx, fun c _ ↦ hμ c⟩
  rw [cost_eq_sum_ofReal_mul_expFamilyDiv hνt hν hw hμx,
    Finset.sum_eq_single a (fun c _ hc ↦ ?_) (by simp)]
  · simp
  · simp [Function.update_of_ne hc, expFamilyDiv_self]

/-- **Moving one arm close to a mean.** If the vectors obtained from `μ` by moving the mean of the
arm `a` to `x` are alternatives to `i` for all `x` near `γ` along a filter `l ≤ 𝓝 γ`, then
`D(μ, w, ¬i) ≤ w a d_a(μ a, γ)`. -/
lemma altCost_le_ofReal_mul_expFamilyDiv_of_eventually [DecidableEq α]
    (hνt : task.ν = ν) (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hw : 0 ≤ w) (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c)) (a : α)
    (hT : ∀ c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : γ ∈ (ρ a).expFamilyMeans (T a)) {l : Filter ℝ} [l.NeBot] (hl : l ≤ 𝓝 γ)
    (h_alt : ∀ᶠ x in l, Function.update μ a x ∈ task.alt i) :
    task.altCost μ w i ≤ ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) γ) := by
  have h_tendsto : Tendsto (fun x ↦ ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) x)) l
      (𝓝 (ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) γ))) :=
    (ENNReal.continuous_ofReal.continuousAt.comp (continuousAt_const.mul
      (hasDerivAt_expFamilyDiv_right hT (μ a) hγ).continuousAt)).tendsto.mono_left hl
  refine ge_of_tendsto h_tendsto ?_
  filter_upwards [h_alt, hl (expFamilyMeans_mem_nhds hT hγ)] with x hx hxm
  rw [← cost_update_eq_ofReal_mul_expFamilyDiv hνt hν hw hμ a hxm]
  exact task.altCost_le_cost hx w

/-- **Alternatives converging to a vector of means.** If the vectors `f x` are alternatives to `i`
eventually along a filter `l` and converge to a vector of means `μ'` of the families, then
`D(μ, w, ¬i) ≤ ∑ c, w c d_c(μ c, μ' c)`: the cost of the alternatives is at most the cost of every
vector of means of the families that is a limit of alternatives. -/
lemma altCost_le_sum_ofReal_mul_expFamilyDiv_of_tendsto
    (hνt : task.ν = ν) (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hw : 0 ≤ w) (hT : ∀ c x, ¬ T c =ᵐ[ρ c] fun _ ↦ x) {μ' : α → ℝ}
    (hμ' : ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → α → ℝ} (hf : Tendsto f l (𝓝 μ')) (h_alt : ∀ᶠ x in l, f x ∈ task.alt i) :
    task.altCost μ w i ≤ ∑ c, ENNReal.ofReal (w c * (ρ c).expFamilyDiv (T c) (μ c) (μ' c)) := by
  have hfc (c : α) : Tendsto (fun x ↦ f x c) l (𝓝 (μ' c)) :=
    ((continuous_apply c).tendsto μ').comp hf
  have h_tendsto : Tendsto
      (fun x ↦ ∑ c, ENNReal.ofReal (w c * (ρ c).expFamilyDiv (T c) (μ c) (f x c))) l
      (𝓝 (∑ c, ENNReal.ofReal (w c * (ρ c).expFamilyDiv (T c) (μ c) (μ' c)))) :=
    tendsto_finsetSum _ fun c _ ↦ (ENNReal.continuous_ofReal.continuousAt.comp
      (continuousAt_const.mul (hasDerivAt_expFamilyDiv_right (hT c) (μ c)
        (hμ' c)).continuousAt)).tendsto.comp (hfc c)
  refine ge_of_tendsto h_tendsto ?_
  have h_mem : ∀ᶠ x in l, ∀ c, f x c ∈ (ρ c).expFamilyMeans (T c) :=
    eventually_all.2 fun c ↦ hfc c (expFamilyMeans_mem_nhds (hT c) (hμ' c))
  filter_upwards [h_alt, h_mem] with x hx hxm
  rw [← cost_eq_sum_ofReal_mul_expFamilyDiv hνt hν hw hxm]
  exact task.altCost_le_cost hx w

/-- **Moving the arms along a path to a vector of means.** Let `μx : ℝ → α → ℝ` be a path of
vectors with coordinates continuous at `γ`, such that `μx γ` is a vector of means of the families.
If the vectors `μx x` of means of the families are alternatives to `i` for all `x` near `γ` along a
filter `l ≤ 𝓝 γ`, then `D(μ, w, ¬i) ≤ ∑ c, w c d_c(μ c, μx γ c)`. -/
lemma altCost_le_sum_ofReal_mul_expFamilyDiv_of_eventually
    (hνt : task.ν = ν) (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hw : 0 ≤ w) (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c) {μx : ℝ → α → ℝ} {l : Filter ℝ}
    [l.NeBot] (hl : l ≤ 𝓝 γ) (hcont : ∀ c, ContinuousAt (fun x ↦ μx x c) γ)
    (hmem : ∀ c, μx γ c ∈ (ρ c).expFamilyMeans (T c))
    (h_alt : ∀ᶠ x in l, (∀ c, μx x c ∈ (ρ c).expFamilyMeans (T c)) → μx x ∈ task.alt i) :
    task.altCost μ w i ≤
      ∑ c, ENNReal.ofReal (w c * (ρ c).expFamilyDiv (T c) (μ c) (μx γ c)) := by
  have h_mem : ∀ᶠ x in l, ∀ c, μx x c ∈ (ρ c).expFamilyMeans (T c) :=
    hl (eventually_all.2 fun c ↦
      (hcont c).eventually_mem (expFamilyMeans_mem_nhds (hT c) (hmem c)))
  exact altCost_le_sum_ofReal_mul_expFamilyDiv_of_tendsto hνt hν hw hT hmem
    ((tendsto_pi_nhds.2 hcont).mono_left hl) ((h_alt.and h_mem).mono fun _ hx ↦ hx.1 hx.2)

/-- **Alternatives converging to a vector with one arm moved.** If the vectors `f x` are
alternatives to `i` eventually along a filter `l` and converge to the vector `update μ a γ` obtained
from `μ` by moving the mean of the arm `a` to a mean `γ` of its family, then
`D(μ, w, ¬i) ≤ w a d_a(μ a, γ)`, even within the vectors of means of the families. This bound
implies the one for `task` itself (`altCost_le_altCost_restrict`). -/
lemma altCost_restrict_le_ofReal_mul_expFamilyDiv_of_tendsto [DecidableEq α]
    (hνt : task.ν = ν) (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hw : 0 ≤ w) (hT : ∀ c x, ¬ T c =ᵐ[ρ c] fun _ ↦ x)
    (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c)) (a : α) (hγ : γ ∈ (ρ a).expFamilyMeans (T a))
    {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → α → ℝ}
    (hf : Tendsto f l (𝓝 (Function.update μ a γ))) (h_alt : ∀ᶠ x in l, f x ∈ task.alt i) :
    (task.restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).altCost μ w i ≤
      ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) γ) := by
  have hμγ : ∀ c, Function.update μ a γ c ∈ (ρ c).expFamilyMeans (T c) :=
    (Function.forall_update_iff μ fun c y ↦ y ∈ (ρ c).expFamilyMeans (T c)).2
      ⟨hγ, fun c _ ↦ hμ c⟩
  have h_mem : ∀ᶠ x in l, ∀ c, f x c ∈ (ρ c).expFamilyMeans (T c) :=
    eventually_all.2 fun c ↦ ((continuous_apply c).tendsto _).comp hf
      (expFamilyMeans_mem_nhds (hT c) (hμγ c))
  rw [← cost_update_eq_ofReal_mul_expFamilyDiv hνt hν hw hμ a hγ,
    cost_eq_sum_ofReal_mul_expFamilyDiv hνt hν hw hμγ]
  refine altCost_le_sum_ofReal_mul_expFamilyDiv_of_tendsto (by rw [ν_restrict, hνt]) hν hw hT hμγ
    hf ?_
  filter_upwards [h_alt, h_mem] with x hx hxm
  rw [alt_restrict]
  exact ⟨hx, hxm⟩

/-- **A lower bound on the cost of a model in which one arm crossed a mean.** If `γ` lies between
`μ a` and `μ' a`, then `w a d_a(μ a, γ) ≤ cost_μ(w, μ')`. -/
lemma ofReal_mul_expFamilyDiv_le_cost
    (hνt : task.ν = ν) (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (hw : 0 ≤ w) {μ' : α → ℝ} (hμ' : ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) (a : α)
    (hT : ∀ c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hγ : γ ∈ (ρ a).expFamilyMeans (T a)) (h : γ ∈ uIcc (μ a) (μ' a)) :
    ENNReal.ofReal (w a * (ρ a).expFamilyDiv (T a) (μ a) γ) ≤ task.cost w μ μ' := by
  rw [cost_eq_sum_ofReal_mul_expFamilyDiv hνt hν hw hμ']
  refine le_trans ?_ (Finset.single_le_sum (f := fun c ↦
    ENNReal.ofReal (w c * (ρ c).expFamilyDiv (T c) (μ c) (μ' c))) (fun _ _ ↦ zero_le)
    (Finset.mem_univ a))
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (expFamilyDiv_le_expFamilyDiv_of_mem_uIcc hT hγ (hμ' a) h) (hw a))

/-- For Gaussian arms with a common variance `σ2 ≠ 0`, the transportation cost is a weighted
squared distance between the vectors of means: `cost_μ(w, μ') = ∑ c, w c (μ c - μ' c)² / (2 σ2)`. -/
lemma cost_gaussianBandit [MeasurableSingletonClass α] {σ2 : ℝ≥0}
    {task : IdentTask α (α → ℝ) ℐ ℝ} (hνt : task.ν = (Bandits.gaussianBandit · σ2))
    (hσ2 : σ2 ≠ 0) (hw : 0 ≤ w) (μ' : α → ℝ) :
    task.cost w μ μ' = ENNReal.ofReal (∑ c, w c * (μ c - μ' c) ^ 2 / (2 * σ2)) := by
  rw [cost_def, hνt, ENNReal.ofReal_sum_of_nonneg fun c _ ↦
    div_nonneg (mul_nonneg (hw c) (sq_nonneg _)) (by positivity)]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Bandits.klDiv_gaussianBandit _ _ hσ2, ← ENNReal.ofReal_mul (hw c), mul_div_assoc]

/-- For Bernoulli arms, the arm `c` of the vector of means `μ` having law `Ber(μ c)` (with `μ c`
clamped to `[0, 1]`), the transportation cost is a weighted sum of binary relative entropies:
`cost_μ(w, μ') = ∑ c, w c d(μ c, μ' c)`. -/
lemma cost_bernoulliBandit [MeasurableSingletonClass α] {task : IdentTask α (α → ℝ) ℐ ℝ}
    (hνt : task.ν = fun μ ↦ Bandits.bernoulliBandit fun c ↦ projIcc 0 1 zero_le_one (μ c))
    (μ' : α → ℝ) :
    task.cost w μ μ' = ∑ c, ENNReal.ofReal (w c) * klBer (μ c) (μ' c) := by
  rw [cost_def, hνt]
  simp only [Bandits.bernoulliBandit_apply, klDiv_bernoulliMeasure, klBer_projIcc]

end LMLExplore.Identification.IdentTask
