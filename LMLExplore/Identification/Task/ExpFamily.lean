/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.Instances
public import LMLExplore.Identification.Task.Continuity
public import LMLExplore.Identification.Task.TransportationCost
public import LMLExplore.Probability.Distributions.ExponentialFamily.Mean

/-!
# Transportation costs under per-arm divergences

Let the models of an identification task be vectors of means `μ : α → ℝ`, and let the arm `c`
have a real divergence `d_c` on an open set `S_c` of means, in the sense that
`KL(ν_c(μ), ν_c(μ')) = d_c(μ c, μ' c)` for all vectors of means `μ'` with `μ' c ∈ S_c`. Then the
transportation cost from `μ` to such a `μ'` is `cost_μ(w, μ') = ∑ c, w c d_c(μ c, μ' c)`. This file
collects the consequences of this formula used to compute the cost of the alternatives of tasks on
vectors of means (best arm identification, thresholding, minimum threshold, Any Low Arm, top-`m`
and ε-best arm identification): the cost of moving a single arm, and the bounds on the cost of the
alternatives obtained by moving one arm, or several arms along a path, to a mean `γ` or across it.

These bounds use only the following properties of the per-arm divergences, bundled in
`IsDivergenceOn d S`: `d` is continuous on `S ×ˢ S`, zero exactly on the diagonal, and monotone in
each argument on each side of the other. The divergences of exponential families in the mean
parametrization have them (`isDivergenceOn_expFamilyDiv`).

The analysis of asymptotically optimal algorithms needs the cost of the alternatives
`D(μ, w, ¬i)` to be jointly continuous in the model and the allocation. On vectors of means this
holds, for every task and every set of alternatives, compact or not, as soon as each per-arm
divergence `d_c` is a divergence on an interval which is unbounded on each side of every point,
that is, `d_c(x, y) → ∞` as `y` tends to either endpoint of `S_c`: near every vector of means, the
alternatives of bounded cost then have their coordinates in compact subsets of the intervals. This
is the non-compact setting of Feinberg, Kasyanov and Voorneveld (2014), used by Degenne and Koolen
(2019), and it is the setting of the exponential families of Gaussian, Bernoulli, Poisson, gamma
and exponential laws and of the Gaussian laws of known mean, whose divergences tend to infinity at
both endpoints of the means (`tendsto_expFamilyDiv_gaussianReal_atBot`,
`tendsto_expFamilyDiv_bernoulliMeasure_sigmoid_nhdsGT_zero`, ...).

## Main definitions

* `LMLExplore.Identification.IsDivergenceOn d S`: the function `d : ℝ → ℝ → ℝ` is a divergence on
  the open set `S`: continuous on `S ×ˢ S`, zero exactly on the diagonal of `S`, and, on `S`,
  monotone in each argument on each side of the other.

## Main statements

* `LMLExplore.Identification.isDivergenceOn_expFamilyDiv`: the divergence `d(μ, μ')` of an
  exponential family in the mean parametrization is a divergence on its means.
* `LMLExplore.Identification.IsDivergenceOn.exists_mem_nhds_forall_exists_isCompact`: a
  divergence on an interval that is unbounded on each side of every point has, near every point,
  sublevel sets contained in compact subsets of the interval.
* `LMLExplore.Identification.IdentTask.continuousOn_biInf_cost_of_isDivergenceOn`,
  `LMLExplore.Identification.IdentTask.continuousOn_altCost_of_isDivergenceOn`: for such per-arm
  divergences, the cost `(μ, w) ↦ inf_{μ' ∈ A} cost_μ(w, μ')` of every set `A` of vectors of means
  is jointly continuous, and so is `D(μ, w, ¬i)` [DK19, Lemmas 25–27];
  `LMLExplore.Identification.IdentTask.continuousOn_gameValue_of_isDivergenceOn`,
  `LMLExplore.Identification.IdentTask.continuousOn_charTime_of_isDivergenceOn`: for finitely many
  answers, `D(μ)` and `T*(μ)` are continuous on the admissible models.
* `LMLExplore.Identification.IdentTask.continuousOn_biInf_cost_expFamily`: the case of arms in
  exponential families in the mean parametrization whose divergence `d(x, y)` tends to infinity as
  `y` tends to either endpoint of the means.
* `LMLExplore.Identification.IdentTask.continuous_altCost_gaussianReal`,
  `LMLExplore.Identification.IdentTask.continuousOn_gameValue_gaussianReal`: for Gaussian arms with
  known arm-dependent variances, `D(μ, w, ¬i)` is continuous for every task, and so is `D(μ)` for
  finitely many answers.
* `LMLExplore.Identification.IdentTask.cost_eq_sum_ofReal_mul`: on the vectors of means in `S`,
  `cost_μ(w, μ') = ∑ c, w c d_c(μ c, μ' c)`.
* `LMLExplore.Identification.IdentTask.cost_eq_sum_ofReal_mul_left`: the cost with the free vector
  first, `cost_{μ'}(w, μ) = ∑ c, w c d_c(μ' c, μ c)`.
* `LMLExplore.Identification.IdentTask.cost_update_eq_ofReal_mul`: moving the mean of the arm `a`
  of `μ` to a mean `x ∈ S_a` costs `w a d_a(μ a, x)`.
* `LMLExplore.Identification.IdentTask.altCost_le_ofReal_mul_of_eventually`: if moving the arm `a`
  to any mean `x` near `γ` (along a filter) gives an alternative to `i`, then
  `D(μ, w, ¬i) ≤ w a d_a(μ a, γ)`.
* `LMLExplore.Identification.IdentTask.altCost_le_sum_ofReal_mul_of_tendsto`: if alternatives to
  `i` converge to a vector of means `μ'` in `S`, then `D(μ, w, ¬i) ≤ ∑ c, w c d_c(μ c, μ' c)`.
* `LMLExplore.Identification.IdentTask.altCost_le_sum_ofReal_mul_of_eventually`: if moving the arms
  along a continuous path `μx` gives alternatives to `i` near `γ` (along a filter), then
  `D(μ, w, ¬i) ≤ ∑ c, w c d_c(μ c, μx γ c)`.
* `LMLExplore.Identification.IdentTask.iInf_cost_le_ofReal_mul_left_of_eventually`,
  `LMLExplore.Identification.IdentTask.iInf_cost_le_sum_ofReal_mul_left_of_eventually`: the
  counterparts of the two `_of_eventually` bounds for the cost with the alternative first,
  `inf_{λ ∈ ¬i} cost_λ(w, μ) ≤ w a d_a(γ, μ a)` and `≤ ∑ c, w c d_c(μx γ c, μ c)`.
* `LMLExplore.Identification.IdentTask.altCost_restrict_le_ofReal_mul_of_tendsto`: if alternatives
  to `i` converge to the vector obtained from `μ` by moving the arm `a` to a mean `γ ∈ S_a`, then
  `D(μ, w, ¬i) ≤ w a d_a(μ a, γ)` within the vectors of means in `S`.
* `LMLExplore.Identification.IdentTask.ofReal_mul_le_cost`: if `γ` lies between `μ a` and `μ' a`,
  then `w a d_a(μ a, γ) ≤ cost_μ(w, μ')`.
* `LMLExplore.Identification.IdentTask.cost_gaussianReal`: for Gaussian arms with variances
  `v c ≠ 0`, `cost_μ(w, μ') = ∑ c, w c (μ c - μ' c)² / (2 v c)`, and
  `LMLExplore.Identification.IdentTask.cost_comm_gaussianReal`: this cost is symmetric in `μ` and
  `μ'`.
* `LMLExplore.Identification.IdentTask.cost_gaussianBandit`: its case of a common variance `σ2`.
* `LMLExplore.Identification.IdentTask.cost_bernoulliBandit`: for Bernoulli arms,
  `cost_μ(w, μ') = ∑ c, w c d(μ c, μ' c)` with the binary relative entropy `d`.
* `LMLExplore.Identification.IdentTask.continuousOn_cost_bernoulliBandit`: for Bernoulli arms,
  the cost is continuous on the vectors of means in `(0, 1)`.

The lemmas `cost_gaussianReal` and `cost_comm_gaussianReal` are adapted from the formalization
Degenne2023Existence (`github.com/RemyDegenne/Degenne2023Existence`, file
`ForLMLExplore/Identification/Task/ExpFamily.lean`, commit
`76f5b36f9219535e1049ef12f781fb5426a2b835`, by Rémy Degenne, Apache 2.0).

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, supplementary material, Appendix F, Lemmas 25–29.
* [FKV14] E. A. Feinberg, P. O. Kasyanov and M. Voorneveld, *Berge's maximum theorem for
  noncompact image sets*, J. Math. Anal. Appl. 413 (2014).
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Measure Set

open scoped ENNReal NNReal

namespace LMLExplore.Identification

/-- **A divergence on an open set of means.** The function `d : ℝ → ℝ → ℝ` is a divergence on
the open set `S ⊆ ℝ` if it is continuous on `S ×ˢ S`, vanishes exactly on the diagonal of `S`,
and, on `S`, `d x ·` is antitone below `x` and monotone above `x`, and `d · y` is antitone below
`y` and monotone above `y`. These are the properties of the per-arm divergences
`(x, y) ↦ KL(ν_a(x), ν_a(y))` that the bounds on transportation costs of this file use; the
divergences of exponential families in the mean parametrization have them
(`isDivergenceOn_expFamilyDiv`). -/
structure IsDivergenceOn (d : ℝ → ℝ → ℝ) (S : Set ℝ) : Prop where
  /-- The set of means is open. -/
  isOpen : IsOpen S
  /-- The divergence is continuous on the pairs of means. -/
  continuousOn : ContinuousOn (fun p : ℝ × ℝ ↦ d p.1 p.2) (S ×ˢ S)
  /-- The divergence between two means vanishes exactly when they are equal. -/
  eq_zero_iff ⦃x : ℝ⦄ (hx : x ∈ S) ⦃y : ℝ⦄ (hy : y ∈ S) : d x y = 0 ↔ x = y
  /-- The divergence from `x` is monotone in the second argument above `x`. -/
  monotoneOn_right ⦃x : ℝ⦄ (hx : x ∈ S) : MonotoneOn (d x) (S ∩ Ici x)
  /-- The divergence from `x` is antitone in the second argument below `x`. -/
  antitoneOn_right ⦃x : ℝ⦄ (hx : x ∈ S) : AntitoneOn (d x) (S ∩ Iic x)
  /-- The divergence to `y` is monotone in the first argument above `y`. -/
  monotoneOn_left ⦃y : ℝ⦄ (hy : y ∈ S) : MonotoneOn (d · y) (S ∩ Ici y)
  /-- The divergence to `y` is antitone in the first argument below `y`. -/
  antitoneOn_left ⦃y : ℝ⦄ (hy : y ∈ S) : AntitoneOn (d · y) (S ∩ Iic y)

namespace IsDivergenceOn

variable {d : ℝ → ℝ → ℝ} {S : Set ℝ} {x y γ : ℝ}

/-- A divergence on `S` vanishes on the diagonal of `S`. -/
lemma apply_self (h : IsDivergenceOn d S) (hx : x ∈ S) : d x x = 0 :=
  (h.eq_zero_iff hx hx).2 rfl

/-- A divergence on `S` is nonnegative on `S ×ˢ S`. -/
lemma nonneg (h : IsDivergenceOn d S) (hx : x ∈ S) (hy : y ∈ S) : 0 ≤ d x y := by
  rw [← h.apply_self hx]
  rcases le_total x y with hxy | hyx
  · exact h.monotoneOn_right hx ⟨hx, le_rfl⟩ ⟨hy, hxy⟩ hxy
  · exact h.antitoneOn_right hx ⟨hy, hyx⟩ ⟨hx, le_rfl⟩ hyx

/-- A divergence on `S` is positive off the diagonal of `S`. -/
lemma pos (h : IsDivergenceOn d S) (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : 0 < d x y :=
  (h.nonneg hx hy).lt_of_ne' fun h0 ↦ hxy ((h.eq_zero_iff hx hy).1 h0)

/-- A divergence on `S` is continuous in its second argument at the points of `S`. -/
lemma continuousAt_right (h : IsDivergenceOn d S) (hx : x ∈ S) (hy : y ∈ S) :
    ContinuousAt (d x) y :=
  (h.continuousOn.continuousAt ((h.isOpen.prod h.isOpen).mem_nhds ⟨hx, hy⟩)).comp
    (f := fun y ↦ (x, y)) (Continuous.prodMk_right x).continuousAt

/-- A divergence on `S` is continuous in its first argument at the points of `S`. -/
lemma continuousAt_left (h : IsDivergenceOn d S) (hx : x ∈ S) (hy : y ∈ S) :
    ContinuousAt (d · y) x :=
  (h.continuousOn.continuousAt ((h.isOpen.prod h.isOpen).mem_nhds ⟨hx, hy⟩)).comp
    (f := fun x ↦ (x, y)) (Continuous.prodMk_left y).continuousAt

/-- The divergence from `x` grows as the second argument moves away from `x`: for `γ` between `x`
and `y`, `d(x, γ) ≤ d(x, y)`. -/
lemma le_of_mem_uIcc (h : IsDivergenceOn d S) (hx : x ∈ S) (hγ : γ ∈ S) (hy : y ∈ S)
    (hγxy : γ ∈ uIcc x y) : d x γ ≤ d x y := by
  rcases le_total x y with hxy | hyx
  · rw [uIcc_of_le hxy] at hγxy
    exact h.monotoneOn_right hx ⟨hγ, hγxy.1⟩ ⟨hy, hxy⟩ hγxy.2
  · rw [uIcc_of_ge hyx] at hγxy
    exact h.antitoneOn_right hx ⟨hy, hyx⟩ ⟨hγ, hγxy.2⟩ hγxy.1

/-- The divergence to `y` grows as the first argument moves away from `y`: for `γ` between `y`
and `x`, `d(γ, y) ≤ d(x, y)`. -/
lemma le_left_of_mem_uIcc (h : IsDivergenceOn d S) (hx : x ∈ S) (hγ : γ ∈ S) (hy : y ∈ S)
    (hγxy : γ ∈ uIcc y x) : d γ y ≤ d x y := by
  rcases le_total y x with hyx | hxy
  · rw [uIcc_of_le hyx] at hγxy
    exact h.monotoneOn_left hy ⟨hγ, hγxy.1⟩ ⟨hx, hyx⟩ hγxy.2
  · rw [uIcc_of_ge hxy] at hγxy
    exact h.antitoneOn_left hy ⟨hx, hxy⟩ ⟨hγ, hγxy.2⟩ hγxy.1

/-- **Sublevel sets of a divergence near a point.** Let `d` be a divergence on an interval `S`
that is unbounded on each side of every point: for every `x ∈ S` and every `r`, some `y ∈ S` below
`x` and some `y ∈ S` above `x` have `d(x, y) > r`. By monotonicity, this means that `d(x, y) → ∞`
as `y` tends to either endpoint of `S`. Then every `x ∈ S` has a neighbourhood `U` such that, for
every `r`, the points `y ∈ S` with `d(x', y) ≤ r` for some `x' ∈ U` lie in a compact subset of
`S`. This is the per-arm hypothesis of the joint continuity of the cost of the alternatives on
product models (`IdentTask.continuousOn_biInf_cost_pi`). -/
theorem exists_mem_nhds_forall_exists_isCompact (h : IsDivergenceOn d S) (hS : S.OrdConnected)
    (h_lt : ∀ x ∈ S, ∀ r : ℝ, ∃ y ∈ S, y < x ∧ r < d x y)
    (h_gt : ∀ x ∈ S, ∀ r : ℝ, ∃ y ∈ S, x < y ∧ r < d x y) (hx : x ∈ S) :
    ∃ U ∈ 𝓝 x, ∀ r : ℝ, ∃ K ⊆ S, IsCompact K ∧ ∀ x' ∈ U, ∀ y ∈ S, d x' y ≤ r → y ∈ K := by
  -- Take `U = [b, c] ⊆ S`. A point `y < b` at divergence at most `r` from some `x' ∈ U` has
  -- `d(b, y) ≤ d(x', y) ≤ r`, so it lies above the point `y₁ < b` with `d(b, y₁) > r`;
  -- symmetrically above `c`.
  obtain ⟨b, c, hxbc, hU, hUS⟩ := exists_Icc_mem_subset_of_mem_nhds (h.isOpen.mem_nhds hx)
  have hb : b ∈ S := hUS (left_mem_Icc.2 (hxbc.1.trans hxbc.2))
  have hc : c ∈ S := hUS (right_mem_Icc.2 (hxbc.1.trans hxbc.2))
  refine ⟨Icc b c, hU, fun r ↦ ?_⟩
  obtain ⟨y₁, hy₁, hy₁b, hr₁⟩ := h_lt b hb r
  obtain ⟨y₂, hy₂, hcy₂, hr₂⟩ := h_gt c hc r
  refine ⟨Icc y₁ y₂, hS.out hy₁ hy₂, isCompact_Icc, fun x' hx' y hy hxy ↦ ⟨?_, ?_⟩⟩
  · by_contra! hyy₁
    have hyb : y ≤ b := (hyy₁.trans hy₁b).le
    have h₁ : d b y₁ ≤ d b y := h.antitoneOn_right hb ⟨hy, hyb⟩ ⟨hy₁, hy₁b.le⟩ hyy₁.le
    have h₂ : d b y ≤ d x' y := h.monotoneOn_left hy ⟨hb, hyb⟩ ⟨hUS hx', hyb.trans hx'.1⟩ hx'.1
    linarith
  · by_contra! hy₂y
    have hcy : c ≤ y := (hcy₂.trans hy₂y).le
    have h₁ : d c y₂ ≤ d c y := h.monotoneOn_right hc ⟨hy₂, hcy₂.le⟩ ⟨hy, hcy⟩ hy₂y.le
    have h₂ : d c y ≤ d x' y := h.antitoneOn_left hy ⟨hUS hx', hx'.2.trans hcy⟩ ⟨hc, hcy⟩ hx'.2
    linarith

end IsDivergenceOn

/-- The divergence `d(μ, μ')` of the exponential family of `ρ` and `T`, in the mean
parametrization, is a divergence on the means of the family. -/
theorem isDivergenceOn_expFamilyDiv {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧}
    {T : 𝓧 → ℝ} (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c) :
    IsDivergenceOn (ρ.expFamilyDiv T) (ρ.expFamilyMeans T) where
  isOpen := isOpen_expFamilyMeans hT
  continuousOn := continuousOn_expFamilyDiv hT
  eq_zero_iff _ hx _ hy := expFamilyDiv_eq_zero_iff hx hy
  monotoneOn_right x _ := (strictMonoOn_expFamilyDiv_right hT x).monotoneOn
  antitoneOn_right x _ := (strictAntiOn_expFamilyDiv_right hT x).antitoneOn
  monotoneOn_left _ hy := (strictMonoOn_expFamilyDiv_left hT hy).monotoneOn
  antitoneOn_left _ hy := (strictAntiOn_expFamilyDiv_left hT hy).antitoneOn

namespace IdentTask

variable {α 𝓨 ℐ : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨} [Fintype α]
  {S : α → Set ℝ} {d : α → ℝ → ℝ → ℝ} {γ : ℝ} {μ w : α → ℝ}
  {task : IdentTask α (α → ℝ) ℐ 𝓨} {i : ℐ} {ν : (α → ℝ) → Kernel α 𝓨}

/-- On the vectors of means in `S`, the transportation cost from `μ` to `μ'` is
`∑ c, w c d_c(μ c, μ' c)` when the divergences between the arm laws are the per-arm divergences
`d_c`. -/
lemma cost_eq_sum_ofReal_mul
    (hνt : task.ν = ν) (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hw : 0 ≤ w) {μ' : α → ℝ} (hμ' : ∀ c, μ' c ∈ S c) :
    task.cost w μ μ' = ∑ c, ENNReal.ofReal (w c * d c (μ c) (μ' c)) := by
  rw [cost_def, hνt]
  exact Finset.sum_congr rfl fun c _ ↦ by rw [hν μ' hμ' c, ENNReal.ofReal_mul (hw c)]

/-- On the vectors of means in `S`, the transportation cost from such a `μ'` to `μ` is
`∑ c, w c d_c(μ' c, μ c)` when the divergences from the arm laws of the vectors of means in `S`
to those of `μ` are the per-arm divergences `d_c`. This is the cost with the free vector first,
as in the static-proportions difficulty `IdentTask.staticDifficulty`. -/
lemma cost_eq_sum_ofReal_mul_left
    (hνt : task.ν = ν) (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ' c) (ν μ c) = ENNReal.ofReal (d c (μ' c) (μ c)))
    (hw : 0 ≤ w) {μ' : α → ℝ} (hμ' : ∀ c, μ' c ∈ S c) :
    task.cost w μ' μ = ∑ c, ENNReal.ofReal (w c * d c (μ' c) (μ c)) := by
  rw [cost_def, hνt]
  exact Finset.sum_congr rfl fun c _ ↦ by rw [hν μ' hμ' c, ENNReal.ofReal_mul (hw c)]

/-- Moving the mean of the arm `a` of a vector of means `μ` in `S` to a mean `x ∈ S_a` costs
`w a d_a(μ a, x)`, when each divergence `d_c` vanishes at `(μ c, μ c)`. -/
lemma cost_update_eq_ofReal_mul [DecidableEq α]
    (hνt : task.ν = ν) (hd : ∀ c, d c (μ c) (μ c) = 0)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hw : 0 ≤ w) (hμ : ∀ c, μ c ∈ S c) (a : α) {x : ℝ} (hx : x ∈ S a) :
    task.cost w μ (Function.update μ a x) = ENNReal.ofReal (w a * d a (μ a) x) := by
  have hμx : ∀ c, Function.update μ a x c ∈ S c :=
    (Function.forall_update_iff μ fun c y ↦ y ∈ S c).2 ⟨hx, fun c _ ↦ hμ c⟩
  rw [cost_eq_sum_ofReal_mul hνt hν hw hμx, Finset.sum_eq_single a (fun c _ hc ↦ ?_) (by simp)]
  · simp
  · simp [Function.update_of_ne hc, hd c]

/-- **Moving one arm close to a mean.** Let `μ` be a vector of means in `S`. If the vectors
obtained from `μ` by moving the mean of the arm `a` to `x` are alternatives to `i` for all `x` near
a mean `γ ∈ S_a` along a filter `l ≤ 𝓝 γ`, then `D(μ, w, ¬i) ≤ w a d_a(μ a, γ)`. -/
lemma altCost_le_ofReal_mul_of_eventually [DecidableEq α]
    (hνt : task.ν = ν) (hd : ∀ c, IsDivergenceOn (d c) (S c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hw : 0 ≤ w) (hμ : ∀ c, μ c ∈ S c) (a : α) (hγ : γ ∈ S a) {l : Filter ℝ} [l.NeBot]
    (hl : l ≤ 𝓝 γ) (h_alt : ∀ᶠ x in l, Function.update μ a x ∈ task.alt i) :
    task.altCost μ w i ≤ ENNReal.ofReal (w a * d a (μ a) γ) := by
  have h_tendsto : Tendsto (fun x ↦ ENNReal.ofReal (w a * d a (μ a) x)) l
      (𝓝 (ENNReal.ofReal (w a * d a (μ a) γ))) :=
    (ENNReal.continuous_ofReal.continuousAt.comp (continuousAt_const.mul
      ((hd a).continuousAt_right (hμ a) hγ))).tendsto.mono_left hl
  refine ge_of_tendsto h_tendsto ?_
  filter_upwards [h_alt, hl ((hd a).isOpen.mem_nhds hγ)] with x hx hxm
  rw [← cost_update_eq_ofReal_mul hνt (fun c ↦ (hd c).apply_self (hμ c)) hν hw hμ a hxm]
  exact task.altCost_le_cost hx w

/-- **Alternatives converging to a vector of means.** Let `μ` be a vector of means in `S`. If the
vectors `f x` are alternatives to `i` eventually along a filter `l` and converge to a vector of
means `μ'` in `S`, then `D(μ, w, ¬i) ≤ ∑ c, w c d_c(μ c, μ' c)`: the cost of the alternatives is at
most the cost of every vector of means in `S` that is a limit of alternatives. -/
lemma altCost_le_sum_ofReal_mul_of_tendsto
    (hνt : task.ν = ν) (hd : ∀ c, IsDivergenceOn (d c) (S c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hw : 0 ≤ w) (hμ : ∀ c, μ c ∈ S c) {μ' : α → ℝ} (hμ' : ∀ c, μ' c ∈ S c) {ι : Type*}
    {l : Filter ι} [l.NeBot] {f : ι → α → ℝ} (hf : Tendsto f l (𝓝 μ'))
    (h_alt : ∀ᶠ x in l, f x ∈ task.alt i) :
    task.altCost μ w i ≤ ∑ c, ENNReal.ofReal (w c * d c (μ c) (μ' c)) := by
  have hfc (c : α) : Tendsto (fun x ↦ f x c) l (𝓝 (μ' c)) :=
    ((continuous_apply c).tendsto μ').comp hf
  have h_tendsto : Tendsto (fun x ↦ ∑ c, ENNReal.ofReal (w c * d c (μ c) (f x c))) l
      (𝓝 (∑ c, ENNReal.ofReal (w c * d c (μ c) (μ' c)))) :=
    tendsto_finsetSum _ fun c _ ↦ (ENNReal.continuous_ofReal.continuousAt.comp
      (continuousAt_const.mul ((hd c).continuousAt_right (hμ c) (hμ' c)))).tendsto.comp (hfc c)
  refine ge_of_tendsto h_tendsto ?_
  have h_mem : ∀ᶠ x in l, ∀ c, f x c ∈ S c :=
    eventually_all.2 fun c ↦ hfc c ((hd c).isOpen.mem_nhds (hμ' c))
  filter_upwards [h_alt, h_mem] with x hx hxm
  rw [← cost_eq_sum_ofReal_mul hνt hν hw hxm]
  exact task.altCost_le_cost hx w

/-- **Moving the arms along a path to a vector of means.** Let `μ` be a vector of means in `S`, and
let `μx : ℝ → α → ℝ` be a path of vectors with coordinates continuous at `γ`, such that `μx γ` is a
vector of means in `S`. If the vectors `μx x` of means in `S` are alternatives to `i` for all `x`
near `γ` along a filter `l ≤ 𝓝 γ`, then `D(μ, w, ¬i) ≤ ∑ c, w c d_c(μ c, μx γ c)`. -/
lemma altCost_le_sum_ofReal_mul_of_eventually
    (hνt : task.ν = ν) (hd : ∀ c, IsDivergenceOn (d c) (S c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hw : 0 ≤ w) (hμ : ∀ c, μ c ∈ S c) {μx : ℝ → α → ℝ} {l : Filter ℝ} [l.NeBot]
    (hl : l ≤ 𝓝 γ) (hcont : ∀ c, ContinuousAt (fun x ↦ μx x c) γ) (hmem : ∀ c, μx γ c ∈ S c)
    (h_alt : ∀ᶠ x in l, (∀ c, μx x c ∈ S c) → μx x ∈ task.alt i) :
    task.altCost μ w i ≤ ∑ c, ENNReal.ofReal (w c * d c (μ c) (μx γ c)) := by
  have h_mem : ∀ᶠ x in l, ∀ c, μx x c ∈ S c :=
    hl (eventually_all.2 fun c ↦ (hcont c).eventually_mem ((hd c).isOpen.mem_nhds (hmem c)))
  exact altCost_le_sum_ofReal_mul_of_tendsto hνt hd hν hw hμ hmem
    ((tendsto_pi_nhds.2 hcont).mono_left hl) ((h_alt.and h_mem).mono fun _ hx ↦ hx.1 hx.2)

/-- **Moving one arm close to a mean, alternative first.** The counterpart of
`altCost_le_ofReal_mul_of_eventually` for the cost with the alternative first, as in the
static-proportions difficulty `IdentTask.staticDifficulty`: let `μ` be a vector of means in `S`.
If the vectors obtained from `μ` by moving the mean of the arm `a` to `x` are alternatives to `i`
for all `x` near a mean `γ ∈ S_a` along a filter `l ≤ 𝓝 γ`, then
`inf_{λ ∈ ¬i} cost_λ(w, μ) ≤ w a d_a(γ, μ a)`. -/
lemma iInf_cost_le_ofReal_mul_left_of_eventually [DecidableEq α]
    (hνt : task.ν = ν) (hd : ∀ c, IsDivergenceOn (d c) (S c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ' c) (ν μ c) = ENNReal.ofReal (d c (μ' c) (μ c)))
    (hw : 0 ≤ w) (hμ : ∀ c, μ c ∈ S c) (a : α) (hγ : γ ∈ S a) {l : Filter ℝ} [l.NeBot]
    (hl : l ≤ 𝓝 γ) (h_alt : ∀ᶠ x in l, Function.update μ a x ∈ task.alt i) :
    ⨅ μ' ∈ task.alt i, task.cost w μ' μ ≤ ENNReal.ofReal (w a * d a γ (μ a)) := by
  have h_tendsto : Tendsto (fun x ↦ ENNReal.ofReal (w a * d a x (μ a))) l
      (𝓝 (ENNReal.ofReal (w a * d a γ (μ a)))) :=
    (ENNReal.continuous_ofReal.continuousAt.comp (continuousAt_const.mul
      ((hd a).continuousAt_left hγ (hμ a)))).tendsto.mono_left hl
  refine ge_of_tendsto h_tendsto ?_
  filter_upwards [h_alt, hl ((hd a).isOpen.mem_nhds hγ)] with x hx hxm
  have hμx : ∀ c, Function.update μ a x c ∈ S c :=
    (Function.forall_update_iff μ fun c y ↦ y ∈ S c).2 ⟨hxm, fun c _ ↦ hμ c⟩
  refine (iInf₂_le _ hx).trans_eq ?_
  rw [cost_eq_sum_ofReal_mul_left hνt hν hw hμx,
    Finset.sum_eq_single a (fun c _ hc ↦ ?_) (by simp)]
  · simp
  · simp [Function.update_of_ne hc, (hd c).apply_self (hμ c)]

/-- **Moving the arms along a path to a vector of means, alternative first.** The counterpart of
`altCost_le_sum_ofReal_mul_of_eventually` for the cost with the alternative first, as in the
static-proportions difficulty `IdentTask.staticDifficulty`: let `μ` be a vector of means in `S`,
and let `μx : ℝ → α → ℝ` be a path of vectors with coordinates continuous at `γ`, such that `μx γ`
is a vector of means in `S`. If the vectors `μx x` of means in `S` are alternatives to `i` for all
`x` near `γ` along a filter `l ≤ 𝓝 γ`, then `inf_{λ ∈ ¬i} cost_λ(w, μ) ≤ ∑ c, w c d_c(μx γ c, μ c)`.
-/
lemma iInf_cost_le_sum_ofReal_mul_left_of_eventually
    (hνt : task.ν = ν) (hd : ∀ c, IsDivergenceOn (d c) (S c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ' c) (ν μ c) = ENNReal.ofReal (d c (μ' c) (μ c)))
    (hw : 0 ≤ w) (hμ : ∀ c, μ c ∈ S c) {μx : ℝ → α → ℝ} {l : Filter ℝ} [l.NeBot]
    (hl : l ≤ 𝓝 γ) (hcont : ∀ c, ContinuousAt (fun x ↦ μx x c) γ) (hmem : ∀ c, μx γ c ∈ S c)
    (h_alt : ∀ᶠ x in l, (∀ c, μx x c ∈ S c) → μx x ∈ task.alt i) :
    ⨅ μ' ∈ task.alt i, task.cost w μ' μ ≤ ∑ c, ENNReal.ofReal (w c * d c (μx γ c) (μ c)) := by
  have h_tendsto : Tendsto (fun x ↦ ∑ c, ENNReal.ofReal (w c * d c (μx x c) (μ c))) l
      (𝓝 (∑ c, ENNReal.ofReal (w c * d c (μx γ c) (μ c)))) :=
    (tendsto_finsetSum _ fun c _ ↦ (ENNReal.continuous_ofReal.continuousAt.comp
      (continuousAt_const.mul (ContinuousAt.comp (f := fun x ↦ μx x c)
        ((hd c).continuousAt_left (hmem c) (hμ c)) (hcont c)))).tendsto).mono_left hl
  refine ge_of_tendsto h_tendsto ?_
  have h_mem : ∀ᶠ x in l, ∀ c, μx x c ∈ S c :=
    hl (eventually_all.2 fun c ↦ (hcont c).eventually_mem ((hd c).isOpen.mem_nhds (hmem c)))
  filter_upwards [h_alt, h_mem] with x hx hxm
  exact (iInf₂_le _ (hx hxm)).trans_eq (cost_eq_sum_ofReal_mul_left hνt hν hw hxm)

/-- **Alternatives converging to a vector with one arm moved.** Let `μ` be a vector of means in
`S`. If the vectors `f x` are alternatives to `i` eventually along a filter `l` and converge to the
vector `update μ a γ` obtained from `μ` by moving the mean of the arm `a` to a mean `γ ∈ S_a`, then
`D(μ, w, ¬i) ≤ w a d_a(μ a, γ)`, even within the vectors of means in `S`. This bound implies the
one for `task` itself (`altCost_le_altCost_restrict`). -/
lemma altCost_restrict_le_ofReal_mul_of_tendsto [DecidableEq α]
    (hνt : task.ν = ν) (hd : ∀ c, IsDivergenceOn (d c) (S c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hw : 0 ≤ w) (hμ : ∀ c, μ c ∈ S c) (a : α) (hγ : γ ∈ S a)
    {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → α → ℝ}
    (hf : Tendsto f l (𝓝 (Function.update μ a γ))) (h_alt : ∀ᶠ x in l, f x ∈ task.alt i) :
    (task.restrict {μ' | ∀ c, μ' c ∈ S c}).altCost μ w i ≤ ENNReal.ofReal (w a * d a (μ a) γ) := by
  have hμγ : ∀ c, Function.update μ a γ c ∈ S c :=
    (Function.forall_update_iff μ fun c y ↦ y ∈ S c).2 ⟨hγ, fun c _ ↦ hμ c⟩
  have h_mem : ∀ᶠ x in l, ∀ c, f x c ∈ S c :=
    eventually_all.2 fun c ↦ ((continuous_apply c).tendsto _).comp hf
      ((hd c).isOpen.mem_nhds (hμγ c))
  rw [← cost_update_eq_ofReal_mul hνt (fun c ↦ (hd c).apply_self (hμ c)) hν hw hμ a hγ,
    cost_eq_sum_ofReal_mul hνt hν hw hμγ]
  refine altCost_le_sum_ofReal_mul_of_tendsto (by rw [ν_restrict, hνt]) hd hν hw hμ hμγ hf ?_
  filter_upwards [h_alt, h_mem] with x hx hxm
  rw [alt_restrict]
  exact ⟨hx, hxm⟩

/-- **A lower bound on the cost of a model in which one arm crossed a mean.** For a mean
`μ a ∈ S_a` and a vector of means `μ'` in `S`, if a mean `γ ∈ S_a` lies between `μ a` and `μ' a`,
then `w a d_a(μ a, γ) ≤ cost_μ(w, μ')`. -/
lemma ofReal_mul_le_cost
    (hνt : task.ν = ν)
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ S c) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hw : 0 ≤ w) {μ' : α → ℝ} (hμ' : ∀ c, μ' c ∈ S c) (a : α) (hd : IsDivergenceOn (d a) (S a))
    (hμ : μ a ∈ S a) (hγ : γ ∈ S a)
    (h : γ ∈ uIcc (μ a) (μ' a)) :
    ENNReal.ofReal (w a * d a (μ a) γ) ≤ task.cost w μ μ' := by
  rw [cost_eq_sum_ofReal_mul hνt hν hw hμ']
  refine le_trans ?_ (Finset.single_le_sum (f := fun c ↦
    ENNReal.ofReal (w c * d c (μ c) (μ' c))) (fun _ _ ↦ zero_le) (Finset.mem_univ a))
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (hd.le_of_mem_uIcc hμ hγ (hμ' a) h) (hw a))

/-- For Gaussian arms with variances `v c ≠ 0`, the transportation cost is a weighted squared
distance between the vectors of means: `cost_μ(w, μ') = ∑ c, w c (μ c - μ' c)² / (2 v c)`. -/
lemma cost_gaussianReal {v : α → ℝ≥0} {task : IdentTask α (α → ℝ) ℐ ℝ} (hv : ∀ c, v c ≠ 0)
    (hν : ∀ μ c, task.ν μ c = gaussianReal (μ c) (v c)) (hw : 0 ≤ w) (μ' : α → ℝ) :
    task.cost w μ μ' = ENNReal.ofReal (∑ c, w c * (μ c - μ' c) ^ 2 / (2 * v c)) := by
  rw [cost_def, ENNReal.ofReal_sum_of_nonneg fun c _ ↦
    div_nonneg (mul_nonneg (hw c) (sq_nonneg _)) (by positivity)]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [hν, hν, klDiv_gaussianReal_gaussianReal_same_var (hv c), ← ENNReal.ofReal_mul (hw c),
    mul_div_assoc]

/-- For Gaussian arms with variances `v c ≠ 0`, the transportation cost is symmetric in the two
vectors of means: `cost_μ(w, μ') = cost_{μ'}(w, μ)`. -/
lemma cost_comm_gaussianReal {v : α → ℝ≥0} {task : IdentTask α (α → ℝ) ℐ ℝ} (hv : ∀ c, v c ≠ 0)
    (hν : ∀ μ c, task.ν μ c = gaussianReal (μ c) (v c)) (w μ' : α → ℝ) :
    task.cost w μ μ' = task.cost w μ' μ := by
  simp_rw [cost_def, hν, klDiv_gaussianReal_gaussianReal_same_var (hv _), sub_sq_comm]

/-- For Gaussian arms with a common variance `σ2 ≠ 0`, the transportation cost is a weighted
squared distance between the vectors of means: `cost_μ(w, μ') = ∑ c, w c (μ c - μ' c)² / (2 σ2)`. -/
lemma cost_gaussianBandit [MeasurableSingletonClass α] {σ2 : ℝ≥0}
    {task : IdentTask α (α → ℝ) ℐ ℝ} (hνt : task.ν = (Bandits.gaussianBandit · σ2))
    (hσ2 : σ2 ≠ 0) (hw : 0 ≤ w) (μ' : α → ℝ) :
    task.cost w μ μ' = ENNReal.ofReal (∑ c, w c * (μ c - μ' c) ^ 2 / (2 * σ2)) :=
  cost_gaussianReal (v := fun _ ↦ σ2) (fun _ ↦ hσ2) (by simp [hνt]) hw μ'

/-- For Bernoulli arms, the arm `c` of the vector of means `μ` having law `Ber(μ c)` (with `μ c`
clamped to `[0, 1]`), the transportation cost is a weighted sum of binary relative entropies:
`cost_μ(w, μ') = ∑ c, w c d(μ c, μ' c)`. -/
lemma cost_bernoulliBandit [MeasurableSingletonClass α] {task : IdentTask α (α → ℝ) ℐ ℝ}
    (hνt : task.ν = fun μ ↦ Bandits.bernoulliBandit fun c ↦ projIcc 0 1 zero_le_one (μ c))
    (μ' : α → ℝ) :
    task.cost w μ μ' = ∑ c, ENNReal.ofReal (w c) * klBer (μ c) (μ' c) := by
  rw [cost_def, hνt]
  simp only [Bandits.bernoulliBandit_apply, klDiv_bernoulliMeasure one_ne_zero, klBer_projIcc]

/-- For Bernoulli arms, the transportation cost is continuous in the alternative vector of means on
the vectors of means in `(0, 1)`, where the binary relative entropy is continuous in its second
argument. -/
lemma continuousOn_cost_bernoulliBandit [MeasurableSingletonClass α]
    {task : IdentTask α (α → ℝ) ℐ ℝ}
    (hνt : task.ν = fun μ ↦ Bandits.bernoulliBandit fun c ↦ projIcc 0 1 zero_le_one (μ c)) :
    ContinuousOn (task.cost w μ) {μ' | ∀ c, μ' c ∈ Ioo 0 1} := by
  refine task.continuousOn_cost (fun c ↦ ?_) w
  refine (continuousOn_klBer.comp (s := {μ' : α → ℝ | ∀ c, μ' c ∈ Ioo 0 1})
    (continuousOn_const.prodMk (continuous_apply c).continuousOn)
    fun μ' hμ' ↦ ⟨Subtype.prop (projIcc 0 1 zero_le_one (μ c)), hμ' c⟩).congr fun μ' hμ' ↦ ?_
  simp [hνt, klDiv_bernoulliMeasure, projIcc_of_mem _ (Ioo_subset_Icc_self (hμ' c))]

/-! ### Continuity of the cost of the alternatives -/

section Continuity

omit [Fintype α] in
/-- The per-arm hypothesis of `continuousOn_biInf_cost_pi` for divergences on intervals that are
unbounded on each side of every point. -/
private lemma forall_exists_mem_nhdsWithin_isCompact (hd : ∀ c, IsDivergenceOn (d c) (S c))
    (hS : ∀ c, (S c).OrdConnected)
    (h_lt : ∀ c, ∀ x ∈ S c, ∀ r : ℝ, ∃ y ∈ S c, y < x ∧ r < d c x y)
    (h_gt : ∀ c, ∀ x ∈ S c, ∀ r : ℝ, ∃ y ∈ S c, x < y ∧ r < d c x y) :
    ∀ c, ∀ x ∈ S c, ∃ U ∈ 𝓝[S c] x, ∀ r : ℝ,
      ∃ K ⊆ S c, IsCompact K ∧ ∀ x' ∈ U, ∀ y ∈ S c, d c x' y ≤ r → y ∈ K := fun c _ hx ↦
  let ⟨U, hU, hUK⟩ := (hd c).exists_mem_nhds_forall_exists_isCompact (hS c) (h_lt c) (h_gt c) hx
  ⟨U, mem_nhdsWithin_of_mem_nhds hU, hUK⟩

/-- **Continuity of the cost of a set of alternatives under per-arm divergences**
[DK19, Lemmas 25–27; FKV14]. Let the divergences between the arm laws of the vectors of means in
`∏ c, S c` be per-arm divergences, `KL(ν_c(μ), ν_c(μ')) = d_c(μ c, μ' c)`, where each `d_c` is a
divergence on the interval `S c` which is unbounded on each side of every point, so that
`d_c(x, y) → ∞` as `y` tends to either endpoint of `S c`. Then for every set `A ⊆ ∏ c, S c` of
vectors of means, compact or not, the cost `(μ, w) ↦ inf_{μ' ∈ A} cost_μ(w, μ')` is continuous on
`(∏ c, S c) ×ˢ univ`. -/
theorem continuousOn_biInf_cost_of_isDivergenceOn
    (hν : ∀ μ ∈ univ.pi S, ∀ μ' ∈ univ.pi S, ∀ c,
      klDiv (task.ν μ c) (task.ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hd : ∀ c, IsDivergenceOn (d c) (S c)) (hS : ∀ c, (S c).OrdConnected)
    (h_lt : ∀ c, ∀ x ∈ S c, ∀ r : ℝ, ∃ y ∈ S c, y < x ∧ r < d c x y)
    (h_gt : ∀ c, ∀ x ∈ S c, ∀ r : ℝ, ∃ y ∈ S c, x < y ∧ r < d c x y)
    {A : Set (α → ℝ)} (hA : A ⊆ univ.pi S) :
    ContinuousOn (fun p : (α → ℝ) × (α → ℝ) ↦ ⨅ μ' ∈ A, task.cost p.2 p.1 μ')
      (univ.pi S ×ˢ univ) :=
  task.continuousOn_biInf_cost_pi hν (fun c ↦ (hd c).continuousOn)
    (forall_exists_mem_nhdsWithin_isCompact hd hS h_lt h_gt) hA

/-- **Continuity of the cost of the alternatives under per-arm divergences** [DK19, Lemma 27]:
under the hypotheses of `continuousOn_biInf_cost_of_isDivergenceOn`, if the alternatives to `i`
are vectors of means in `∏ c, S c`, then `(μ, w) ↦ D(μ, w, ¬i)` is continuous on
`(∏ c, S c) ×ˢ univ`. -/
theorem continuousOn_altCost_of_isDivergenceOn
    (hν : ∀ μ ∈ univ.pi S, ∀ μ' ∈ univ.pi S, ∀ c,
      klDiv (task.ν μ c) (task.ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hd : ∀ c, IsDivergenceOn (d c) (S c)) (hS : ∀ c, (S c).OrdConnected)
    (h_lt : ∀ c, ∀ x ∈ S c, ∀ r : ℝ, ∃ y ∈ S c, y < x ∧ r < d c x y)
    (h_gt : ∀ c, ∀ x ∈ S c, ∀ r : ℝ, ∃ y ∈ S c, x < y ∧ r < d c x y)
    (h_alt : task.alt i ⊆ univ.pi S) :
    ContinuousOn (fun p : (α → ℝ) × (α → ℝ) ↦ task.altCost p.1 p.2 i) (univ.pi S ×ˢ univ) :=
  task.continuousOn_altCost_pi hν (fun c ↦ (hd c).continuousOn)
    (forall_exists_mem_nhdsWithin_isCompact hd hS h_lt h_gt) h_alt

/-- **Continuity of the value of the game under per-arm divergences** [DK19, Lemmas 27, 29]: for
finitely many answers, under the hypotheses of `continuousOn_biInf_cost_of_isDivergenceOn`, if the
admissible models are vectors of means in `∏ c, S c`, then `μ ↦ D(μ)` is continuous on the
admissible models. -/
theorem continuousOn_gameValue_of_isDivergenceOn [Finite ℐ]
    (hν : ∀ μ ∈ univ.pi S, ∀ μ' ∈ univ.pi S, ∀ c,
      klDiv (task.ν μ c) (task.ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hd : ∀ c, IsDivergenceOn (d c) (S c)) (hS : ∀ c, (S c).OrdConnected)
    (h_lt : ∀ c, ∀ x ∈ S c, ∀ r : ℝ, ∃ y ∈ S c, y < x ∧ r < d c x y)
    (h_gt : ∀ c, ∀ x ∈ S c, ∀ r : ℝ, ∃ y ∈ S c, x < y ∧ r < d c x y)
    (hM : task.M ⊆ univ.pi S) :
    ContinuousOn task.gameValue task.M :=
  task.continuousOn_gameValue_pi hν (fun c ↦ (hd c).continuousOn)
    (forall_exists_mem_nhdsWithin_isCompact hd hS h_lt h_gt) hM

/-- **Continuity of the characteristic time under per-arm divergences** [DK19, Lemmas 27, 29]:
under the hypotheses of `continuousOn_gameValue_of_isDivergenceOn`, `μ ↦ T*(μ)` is continuous on
the admissible models. -/
theorem continuousOn_charTime_of_isDivergenceOn [Finite ℐ]
    (hν : ∀ μ ∈ univ.pi S, ∀ μ' ∈ univ.pi S, ∀ c,
      klDiv (task.ν μ c) (task.ν μ' c) = ENNReal.ofReal (d c (μ c) (μ' c)))
    (hd : ∀ c, IsDivergenceOn (d c) (S c)) (hS : ∀ c, (S c).OrdConnected)
    (h_lt : ∀ c, ∀ x ∈ S c, ∀ r : ℝ, ∃ y ∈ S c, y < x ∧ r < d c x y)
    (h_gt : ∀ c, ∀ x ∈ S c, ∀ r : ℝ, ∃ y ∈ S c, x < y ∧ r < d c x y)
    (hM : task.M ⊆ univ.pi S) :
    ContinuousOn task.charTime task.M :=
  task.continuousOn_charTime_pi hν (fun c ↦ (hd c).continuousOn)
    (forall_exists_mem_nhdsWithin_isCompact hd hS h_lt h_gt) hM

/-- **Continuity of the cost of a set of alternatives for arms in exponential families**
[DK19, Lemma 27, Appendix F]. Let the arm `c` be in the exponential family of `ρ c` and `T c` in the
mean parametrization, in the sense that `KL(ν_c(μ), ν_c(μ')) = d_c(μ c, μ' c)` for the divergence
`d_c` of that family and all vectors of means `μ`, `μ'` of the families (for example when
`ν μ c` is the member of mean `μ c`, by `klDiv_expFamily_natParam`). Suppose that each divergence
`d_c(x, y)` is unbounded as `y` moves away from `x` on either side within the means, that is,
tends to infinity as `y` tends to either endpoint of the means (`tendsto_expFamilyDiv_*` for the
Gaussian, Bernoulli, Poisson, gamma and exponential families). Then for every set `A` of vectors of
means of the families, the cost `(μ, w) ↦ inf_{μ' ∈ A} cost_μ(w, μ')` is continuous on the vectors
of means of the families and all allocations. -/
theorem continuousOn_biInf_cost_expFamily {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}
    {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} (hT : ∀ c, ∀ x, ¬ T c =ᵐ[ρ c] fun _ ↦ x)
    (hν : ∀ μ ∈ univ.pi fun c ↦ (ρ c).expFamilyMeans (T c),
      ∀ μ' ∈ univ.pi fun c ↦ (ρ c).expFamilyMeans (T c), ∀ c,
        klDiv (task.ν μ c) (task.ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (h_lt : ∀ c, ∀ x ∈ (ρ c).expFamilyMeans (T c), ∀ r : ℝ,
      ∃ y ∈ (ρ c).expFamilyMeans (T c), y < x ∧ r < (ρ c).expFamilyDiv (T c) x y)
    (h_gt : ∀ c, ∀ x ∈ (ρ c).expFamilyMeans (T c), ∀ r : ℝ,
      ∃ y ∈ (ρ c).expFamilyMeans (T c), x < y ∧ r < (ρ c).expFamilyDiv (T c) x y)
    {A : Set (α → ℝ)} (hA : A ⊆ univ.pi fun c ↦ (ρ c).expFamilyMeans (T c)) :
    ContinuousOn (fun p : (α → ℝ) × (α → ℝ) ↦ ⨅ μ' ∈ A, task.cost p.2 p.1 μ')
      ((univ.pi fun c ↦ (ρ c).expFamilyMeans (T c)) ×ˢ univ) :=
  continuousOn_biInf_cost_of_isDivergenceOn hν (fun c ↦ isDivergenceOn_expFamilyDiv (hT c))
    (fun _ ↦ convex_expFamilyMeans.ordConnected) h_lt h_gt hA

omit [Fintype α] in
/-- For Gaussian arms with variances `v c ≠ 0`, the divergences are those of the Gaussian
exponential families, which tend to infinity at `±∞`. -/
private lemma klDiv_eq_expFamilyDiv_and_exists_lt_gaussianReal {v : α → ℝ≥0}
    {task : IdentTask α (α → ℝ) ℐ ℝ} (hv : ∀ c, v c ≠ 0)
    (hν : ∀ μ c, task.ν μ c = gaussianReal (μ c) (v c)) :
    (∀ μ ∈ univ.pi fun c ↦ (gaussianReal 0 (v c)).expFamilyMeans id,
      ∀ μ' ∈ univ.pi fun c ↦ (gaussianReal 0 (v c)).expFamilyMeans id, ∀ c,
        klDiv (task.ν μ c) (task.ν μ' c) =
          ENNReal.ofReal ((gaussianReal 0 (v c)).expFamilyDiv id (μ c) (μ' c))) ∧
    (∀ c, ∀ x ∈ (gaussianReal 0 (v c)).expFamilyMeans id, ∀ r : ℝ,
      ∃ y ∈ (gaussianReal 0 (v c)).expFamilyMeans id, y < x ∧
        r < (gaussianReal 0 (v c)).expFamilyDiv id x y) ∧
    (∀ c, ∀ x ∈ (gaussianReal 0 (v c)).expFamilyMeans id, ∀ r : ℝ,
      ∃ y ∈ (gaussianReal 0 (v c)).expFamilyMeans id, x < y ∧
        r < (gaussianReal 0 (v c)).expFamilyDiv id x y) := by
  refine ⟨fun μ _ μ' _ c ↦ ?_, fun c x _ r ↦ ?_, fun c x _ r ↦ ?_⟩
  · rw [hν, hν, klDiv_gaussianReal_gaussianReal_same_var (hv c),
      expFamilyDiv_gaussianReal 0 (hv c)]
  · obtain ⟨y, hry, hyx⟩ := (((tendsto_expFamilyDiv_gaussianReal_atBot 0 (hv c)
      x).eventually_gt_atTop r).and (eventually_lt_atBot x)).exists
    exact ⟨y, mem_expFamilyMeans_gaussianReal 0 (hv c) y, hyx, hry⟩
  · obtain ⟨y, hry, hxy⟩ := (((tendsto_expFamilyDiv_gaussianReal_atTop 0 (hv c)
      x).eventually_gt_atTop r).and (eventually_gt_atTop x)).exists
    exact ⟨y, mem_expFamilyMeans_gaussianReal 0 (hv c) y, hxy, hry⟩

/-- **Continuity of the cost of the alternatives for Gaussian arms** [DK19, Lemma 27]: for
Gaussian arms with known variances `v c ≠ 0`, `(μ, w) ↦ D(μ, w, ¬i)` is continuous, for every task
on vectors of means and every answer `i`. -/
theorem continuous_altCost_gaussianReal {v : α → ℝ≥0} {task : IdentTask α (α → ℝ) ℐ ℝ}
    (hv : ∀ c, v c ≠ 0) (hν : ∀ μ c, task.ν μ c = gaussianReal (μ c) (v c)) (i : ℐ) :
    Continuous fun p : (α → ℝ) × (α → ℝ) ↦ task.altCost p.1 p.2 i := by
  obtain ⟨hν', h_lt, h_gt⟩ := klDiv_eq_expFamilyDiv_and_exists_lt_gaussianReal hv hν
  have h := continuousOn_altCost_of_isDivergenceOn (i := i) hν'
    (fun c ↦ isDivergenceOn_expFamilyDiv (not_ae_eq_const_gaussianReal 0 (hv c)))
    (fun _ ↦ convex_expFamilyMeans.ordConnected) h_lt h_gt (by simp [hv])
  simpa [hv, continuousOn_univ] using h

/-- **Continuity of the value of the game for Gaussian arms** [DK19, Lemmas 27, 29]: for Gaussian
arms with known variances `v c ≠ 0` and every task with finitely many answers on vectors of means,
`μ ↦ D(μ)` is continuous on the admissible models. -/
theorem continuousOn_gameValue_gaussianReal [Finite ℐ] {v : α → ℝ≥0}
    {task : IdentTask α (α → ℝ) ℐ ℝ} (hv : ∀ c, v c ≠ 0)
    (hν : ∀ μ c, task.ν μ c = gaussianReal (μ c) (v c)) :
    ContinuousOn task.gameValue task.M := by
  obtain ⟨hν', h_lt, h_gt⟩ := klDiv_eq_expFamilyDiv_and_exists_lt_gaussianReal hv hν
  exact continuousOn_gameValue_of_isDivergenceOn hν'
    (fun c ↦ isDivergenceOn_expFamilyDiv (not_ae_eq_const_gaussianReal 0 (hv c)))
    (fun _ ↦ convex_expFamilyMeans.ordConnected) h_lt h_gt (by simp [hv])

end Continuity

end IdentTask

end LMLExplore.Identification
