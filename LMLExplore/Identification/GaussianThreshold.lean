/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.AsymptoticOptimality
public import LMLExplore.Identification.StickyTrackAndStop
public import LMLExplore.Identification.Task.ExpFamily
public import LMLExplore.Identification.TrackAndStop

/-!
# `δ`-correct GLR thresholds for Gaussian arms and asymptotic optimality of Track-and-Stop

Let the arms of the models of an identification task be Gaussian with a common known variance
`σ2 ≠ 0`, the arm `a` of the vector of means `μ` having law `𝒩(μ a, σ2)`. After `n` rounds with
pull counts `N_a` and empirical means `μ̂_a`, the plug-in statistic of the empirical means, the
statistic of the GLR stopping rule of `Identification/TrackAndStop.lean`, against a model `λ` is
`∑ a, N_a KL(𝒩(μ̂_a, σ2), 𝒩(λ_a, σ2)) = ∑ a, N_a (μ̂_a - λ_a)² / (2 σ2)`. Gaussian arms are the
members of the exponential family of `𝒩(0, σ2)` with the identity statistic, whose means are all
the reals, so this statistic is the generalized likelihood ratio evidence of that family, and the
results of `Identification/ExpFamilyThreshold.lean` and `Identification/AsymptoticOptimality.lean`
apply; the theorems of this file are their Gaussian instances. Along a run of any sampling rule on
the model `μ`, this statistic at `λ = μ` exceeds `K log (2 n (n + 1)) + x` at some round `n` with
probability at most `f(x) = (x / K) ^ K exp (K - x)` for `x ≥ K`, where `K` is the number of arms.
Hence the GLRT with the thresholds `β_x(n) = K log (2 n (n + 1)) + x` stops with an incorrect
answer with probability at most `f(x)`, for every task and every sampling rule [LS, Lemma 33.7].

To reach the confidence level `δ`, Lattimore and Szepesvári take `x = f⁻¹(δ)`, and remark that
`f⁻¹(δ) = (1 + o(1)) log (1 / δ)` as `δ → 0`. This file uses instead the explicit level
`x_δ = log (1 / δ) + 2 K (1 + log (1 + log (1 / δ)))`, which satisfies `f(x_δ) ≤ δ` and
`x_δ - log (1 / δ) = o(log (1 / δ))`: the leading term `log (1 / δ)` is the one that the
asymptotic sample complexity of Track-and-Stop requires to match the lower bound
`𝔼[τ_δ] ≥ T*(μ) kl(δ, 1 - δ)`.

The thresholds of [LS] have `log (t (t + 1))` in place of `log (2 t (t + 1))`; the factor `2`
accounts for the two tails of the empirical mean of each arm.

The thresholds `β_x` (`LMLExplore.Identification.unionBoundThreshold`), the level `x_δ`
(`LMLExplore.Identification.unionBoundLevel`) and the facts `f(x_δ) ≤ δ` and
`x_δ - log (1 / δ) = o(log (1 / δ))` do not depend on the arms and live in
`Identification/GLR.lean`.

**Asymptotic optimality of Track-and-Stop** [GK16, Theorem 14]. When Track-and-Stop with the
thresholds `K log (2 n (n + 1)) + x_δ` tracks the optimal allocations of every admissible model, it
is `δ`-PAC for every `δ ∈ (0, 1]`, and together with the lower bound of
`Identification/LowerBound.lean`, `𝔼[τ_δ] / log (1 / δ)` tends to `T*(μ)` on every admissible
model `μ`. The same holds for Track-and-Stop with C-tracking, whose
targets may be any selection of the optimal allocations, even where these are not unique
[DK19, Theorem 7].

**Sticky Track-and-Stop** [DK19, Theorems 10–11]. Since
`KL(𝒩(x, σ2), 𝒩(y, σ2)) = (x - y)² / (2 σ2)`, the models whose arms are within a small relative
entropy of those of a model close to `μ` are close to `μ`, so that the confidence regions of
Sticky Track-and-Stop shrink to the true model. Let the task have finitely many answers, let the
radii of the confidence regions be at least `K log (2 n (n + 1)) + x_{(n + 1) ^ (-p)}` for some
`p > 2` and `o(√n)`, let the targets be allocations, those of the least oracle answer of the
admissible model `μ` being optimal allocations near `μ`, let the recommendation have a GLR
statistic at least that of the sticky answer, and let the costs be continuous at `μ`. Then, with
the thresholds `K log (2 n (n + 1)) + x_δ`, Sticky Track-and-Stop satisfies
`limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ T*(μ)`, even where `μ` has several oracle answers. When
these assumptions hold on every admissible model `θ`, and `T*(θ) < ∞` on every admissible model
`θ`, it is moreover `δ`-PAC for every `δ ∈ (0, 1]`.

## Main statements

* `IdentTask.plugInCost_gaussianBandit`: the plug-in statistic of the empirical means of
  Gaussian arms is `∑ a, N_a (μ̂_a - λ_a)² / (2 σ2)`.
* `IdentTask.measure_exists_unionBoundThreshold_lt_plugInCost_le`: along a run of any sampling rule
  on the model `μ`, the plug-in statistic of the empirical means at `μ` exceeds the threshold
  `β_x(n)` at some round with
  probability at most `f(x)`.
* `IdentTask.measureReal_histOutputMeasure_glrt_unionBoundThreshold_le`: [LS, Lemma 33.7] for
  every task with Gaussian arms and every sampling rule: the GLRT with the thresholds `β_x`
  stops with an answer that is not correct for `μ` with probability at most `f(x)`.
* `IdentTask.isDeltaPAC_glrt_unionBoundThreshold`: with the level `x_δ`, the GLRT is `δ`-PAC on
  the task as soon as it stops almost surely on every admissible model.
* `IdentTask.isDeltaPAC_trackAndStop_unionBoundThreshold`: the same for Track-and-Stop.
* `IdentTask.isDeltaPAC_trackAndStop_unionBoundThreshold_of_mem_optAlloc`: when Track-and-Stop
  with the thresholds `β_{x_δ}` tracks optimal allocations, it is `δ`-PAC for every `δ ∈ (0, 1]`.
* `IdentTask.tendsto_expectedStoppingTime_trackAndStop_unionBoundThreshold_div_log`:
  **asymptotic optimality**, `𝔼[τ_δ] / log (1 / δ) → T*(μ)` as `δ → 0`.
* `IdentTask.isDeltaPAC_cTrackAndStop_unionBoundThreshold_of_mem_optAlloc`,
  `IdentTask.tendsto_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_div_log`: the same for
  Track-and-Stop with C-tracking, whose targets may be any selection of the optimal allocations,
  even where these are not unique [DK19, Theorem 7].
* `IdentTask.eventually_expectedStoppingTime_stickyTrackAndStop_unionBoundThreshold_le`,
  `IdentTask.isDeltaPAC_stickyTrackAndStop_unionBoundThreshold`: under the assumptions above, the
  sample complexity of Sticky Track-and-Stop is at most `T*(μ) log (1 / δ)` asymptotically, and it
  is `δ`-PAC for every `δ ∈ (0, 1]` [DK19, Theorems 10–11].

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, Theorems 7, 10 and 11.
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Theorem 14.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 33.7.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Real
open scoped ENNReal NNReal

namespace LMLExplore.Identification.IdentTask

/-- For Gaussian arms with a common variance `σ2 ≠ 0`, the arm `a` of the model `θ` is dominated,
in moment generating function and on every parameter, by the member of mean `θ a` of the
exponential family of `𝒩(0, σ2)` with the identity statistic: both have the law `𝒩(θ a, σ2)`. -/
private lemma mgfDominatedOn_gaussianBandit {α ℐ : Type*} {mα : MeasurableSpace α} [Countable α]
    [MeasurableSingletonClass α] {task : IdentTask α (α → ℝ) ℐ ℝ} {σ2 : ℝ≥0}
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0) (θ : α → ℝ) (a : α) :
    MGFDominatedOn id (task.ν θ a) id
      ((gaussianReal 0 σ2).expFamily id ((gaussianReal 0 σ2).natParam id (θ a))) Set.univ := by
  rw [hνt, expFamily_natParam_gaussianReal 0 hσ2, Bandits.gaussianBandit_apply]
  exact (IdentDistrib.refl aemeasurable_id).mgfDominatedOn

/-- For Gaussian arms with a common variance `σ2 ≠ 0`, the relative entropy between the arms `a`
of two models is at most (in fact equal to) the extended divergence of the exponential family of
`𝒩(0, σ2)` with the identity statistic, whose means are all the reals. -/
private lemma klDiv_le_expFamilyRate_gaussianBandit {α ℐ : Type*} {mα : MeasurableSpace α}
    [Countable α] [MeasurableSingletonClass α] {task : IdentTask α (α → ℝ) ℐ ℝ} {σ2 : ℝ≥0}
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0) (θ μ' : α → ℝ) (a : α) :
    klDiv (task.ν μ' a) (task.ν θ a) ≤ (gaussianReal 0 σ2).expFamilyRate id (μ' a) (θ a) :=
  hνt ▸ (Bandits.klDiv_gaussianBandit_eq_expFamilyRate hσ2 μ' θ a).le

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {task : IdentTask α (α → ℝ) ℐ ℝ} {σ2 : ℝ≥0}

/-- For Gaussian arms with a common variance `σ2 ≠ 0`, the plug-in statistic of an estimator
`est` of the vector of means, for the history `h` of the first `n` rounds against the model `λ`, is
`∑ a, N_a (θ̂_a - λ_a)² / (2 σ2)`, with the pull counts `N_a` of `h` and the estimate
`θ̂ = est n h`. For the empirical means `est = empMean'`, it is
`∑ a, N_a (μ̂_a - λ_a)² / (2 σ2)`. -/
lemma plugInCost_gaussianBandit (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0)
    (est : (n : ℕ) → Hist Unit α ℝ n → α → ℝ) (n : ℕ) (h : Hist Unit α ℝ n) (θ' : α → ℝ) :
    task.plugInCost est n h θ' =
      ENNReal.ofReal (∑ a, pullCount' n h a * (est n h a - θ' a) ^ 2 / (2 * σ2)) := by
  rw [plugInCost_def, cost_gaussianBandit hνt hσ2 fun a ↦ by positivity]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {alg : Algorithm Unit α ℝ} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {μ : α → ℝ}
  {x δ : ℝ}

/-- **Deviation of the plug-in statistic of the empirical means of Gaussian arms**, along a run of
any sampling rule. For Gaussian arms with a common variance `σ2 ≠ 0` and a level `x ≥ K`, the
probability that at some round `n`, the plug-in statistic of the empirical means against the true
model `μ` exceeds the threshold
`K log (2 n (n + 1)) + x`, is at most `(x / K) ^ K exp (K - x)`. -/
theorem measure_exists_unionBoundThreshold_lt_plugInCost_le
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0)
    (hseq : IsAlgEnvSeq O A R alg (Environment.bandit (task.ν μ)) P)
    (hx : Fintype.card α ≤ x) :
    P {ω | ∃ n, unionBoundThreshold (Fintype.card α) x n <
        task.plugInCost empMean' n (history O A R n ω) μ} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) :=
  measure_exists_unionBoundThreshold_lt_plugInCost_le_of_klDiv_le (ρ := fun _ ↦ gaussianReal 0 σ2)
    (T := fun _ ↦ id) (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
    (mgfDominatedOn_gaussianBandit hνt hσ2 μ) (klDiv_le_expFamilyRate_gaussianBandit hνt hσ2 μ)
    hseq hx

variable {mℐ : MeasurableSpace ℐ} (rec : (n : ℕ) → Hist Unit α ℝ n → ℐ)
  (hrec : ∀ n, Measurable (rec n))

/-- **Error probability of the GLRT for Gaussian arms** [LS, Lemma 33.7], for every task and every
sampling rule. For Gaussian arms with a common variance `σ2 ≠ 0`, an admissible model `μ` and a
level `x ≥ K`, the GLRT with the plug-in statistic of the empirical means and the thresholds
`K log (2 n (n + 1)) + x` stops with an answer that is not correct for `μ` with probability at most
`(x / K) ^ K exp (K - x)`. -/
theorem measureReal_histOutputMeasure_glrt_unionBoundThreshold_le
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0)
    (hstop : ∀ n, MeasurableSet
      {h | unionBoundThreshold (Fintype.card α) x n <
        task.glr (task.plugInCost empMean') n h (rec n h)})
    (hμ : μ ∈ task.M) (hc : MeasurableSet (task.correct μ)) (hx : Fintype.card α ≤ x) :
    (histOutputMeasure
        (task.glrt (task.plugInCost empMean') alg
          (fun n _ ↦ unionBoundThreshold (Fintype.card α) x n) rec hrec hstop)
          (Environment.bandit (task.ν μ))).real
        {p | p.1 ∈ (task.glrt (task.plugInCost empMean') alg
          (fun n _ ↦ unionBoundThreshold (Fintype.card α) x n) rec hrec hstop).stopSet ∧
          p.2 ∉ task.correct μ} ≤
      (x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x) :=
  measureReal_histOutputMeasure_glrt_unionBoundThreshold_le_of_klDiv_le
    (ρ := fun _ ↦ gaussianReal 0 σ2) (T := fun _ ↦ id) rec hrec hstop hμ
    (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _) (mgfDominatedOn_gaussianBandit hνt hσ2 μ)
    (klDiv_le_expFamilyRate_gaussianBandit hνt hσ2 μ) hc hx

/-- **The GLRT for Gaussian arms is `δ`-PAC** [LS, Lemma 33.7], for every task and every sampling
rule. For Gaussian arms with a common variance `σ2 ≠ 0` and `δ ∈ (0, 1]`, the GLRT with the
plug-in statistic of the empirical means and the thresholds `K log (2 n (n + 1)) + x_δ` is
`δ`-PAC on the task, provided it stops almost surely on every admissible model. -/
theorem isDeltaPAC_glrt_unionBoundThreshold
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hstop : ∀ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
      (unionBoundLevel (Fintype.card α) δ) n < task.glr (task.plugInCost empMean') n h (rec n h)})
    (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (h_stops : ∀ θ ∈ task.M, StopsAS (task.glrt (task.plugInCost empMean') alg
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec hstop) (Environment.bandit (task.ν θ))) :
    task.IsDeltaPAC (task.glrt (task.plugInCost empMean') alg
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec hstop) δ :=
  isDeltaPAC_glrt_unionBoundThreshold_of_klDiv_le (ρ := fun _ ↦ gaussianReal 0 σ2)
    (T := fun _ ↦ id) rec hrec hδ hδ1 hstop (fun _ _ _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
    (fun θ _ ↦ mgfDominatedOn_gaussianBandit hνt hσ2 θ)
    (fun θ _ ↦ klDiv_le_expFamilyRate_gaussianBandit hνt hσ2 θ) hc h_stops

/-- **Track-and-Stop for Gaussian arms is `δ`-PAC** [LS, Lemma 33.7], whatever its target map and
its recommendation rule. For Gaussian arms with a common variance `σ2 ≠ 0` and `δ ∈ (0, 1]`,
Track-and-Stop with the empirical means as estimator and the thresholds `K log (2 n (n + 1)) + x_δ`
is `δ`-PAC on the task, provided it stops almost surely on every admissible model. -/
theorem isDeltaPAC_trackAndStop_unionBoundThreshold [Nonempty α]
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {w : (α → ℝ) → α → ℝ} (hw : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ w (empMean' n h))
    {rec : (α → ℝ) → ℐ} (hrec : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ rec (empMean' n h))
    (hstop : ∀ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
      (unionBoundLevel (Fintype.card α) δ) n <
        task.glr (task.plugInCost empMean') n h (rec (empMean' n h))})
    (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (h_stops : ∀ θ ∈ task.M, StopsAS (task.trackAndStop empMean' w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec hstop) (Environment.bandit (task.ν θ))) :
    task.IsDeltaPAC (task.trackAndStop empMean' w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec hstop) δ :=
  isDeltaPAC_trackAndStop_unionBoundThreshold_of_klDiv_le (ρ := fun _ ↦ gaussianReal 0 σ2)
    (T := fun _ ↦ id) hδ hδ1 hw hrec hstop (fun _ _ _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
    (fun θ _ ↦ mgfDominatedOn_gaussianBandit hνt hσ2 θ)
    (fun θ _ ↦ klDiv_le_expFamilyRate_gaussianBandit hνt hσ2 θ) hc h_stops

end LMLExplore.Identification.IdentTask

/-! ### Asymptotic optimality of Track-and-Stop -/

namespace LMLExplore.Identification.IdentTask

open Filter Topology

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {mℐ : MeasurableSpace ℐ} {task : IdentTask α (α → ℝ) ℐ ℝ}
  {σ2 : ℝ≥0} {w : (α → ℝ) → α → ℝ}
  {hw : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ w (empMean' n h)} {rec : (α → ℝ) → ℐ}
  {hrec : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ rec (empMean' n h)}
  {hstop : ∀ δ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
    (unionBoundLevel (Fintype.card α) δ) n <
      task.glr (task.plugInCost empMean') n h (rec (empMean' n h))}}
  {μ : α → ℝ} {i : ℐ}

/-- **Track-and-Stop for Gaussian arms is `δ`-PAC** for every `δ ∈ (0, 1]`, with the thresholds
`K log (2 n (n + 1)) + x_δ`, when it tracks optimal allocations: every admissible model `θ` has
the single correct answer `rec θ`, which is the recommendation near `θ`, and `T*(θ) < ∞`; the
target map `w` is continuous at `θ` with `w(θ)` an optimal allocation `w*(θ, ¬rec θ)`; and
`(μ', w') ↦ D(μ', w', ¬rec θ)` is lower semicontinuous at `(θ, w(θ))` on the allocations of the
simplex. -/
theorem isDeltaPAC_trackAndStop_unionBoundThreshold_of_mem_optAlloc [MeasurableSingletonClass ℐ]
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0)
    (hcorrect : ∀ θ ∈ task.M, task.correct θ = {rec θ})
    (hw_opt : ∀ θ ∈ task.M, w θ ∈ task.optAlloc θ (rec θ))
    (hw_cont : ∀ θ ∈ task.M, ContinuousAt w θ)
    (hrec_eq : ∀ θ ∈ task.M, ∀ᶠ θ' in 𝓝 θ, rec θ' = rec θ)
    (h_lsc : ∀ θ ∈ task.M, LowerSemicontinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 (rec θ)) (Set.univ ×ˢ simplex α) (θ, w θ))
    (h_charTime : ∀ θ ∈ task.M, task.charTime θ ≠ ∞) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    task.IsDeltaPAC (task.trackAndStop empMean' w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec (hstop δ)) δ :=
  isDeltaPAC_trackAndStop_unionBoundThreshold_of_mem_optAlloc_of_klDiv_le
    (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
    (fun _ _ _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
    (fun θ _ ↦ mgfDominatedOn_gaussianBandit hνt hσ2 θ)
    (fun θ _ ↦ klDiv_le_expFamilyRate_gaussianBandit hνt hσ2 θ) hcorrect hw_opt hw_cont hrec_eq
    h_lsc h_charTime hδ hδ1

/-- **Asymptotic optimality of Track-and-Stop for Gaussian arms** [GK16, Theorem 14]. Under the
assumptions of `IdentTask.isDeltaPAC_trackAndStop_unionBoundThreshold_of_mem_optAlloc`,
Track-and-Stop with the thresholds `K log (2 n (n + 1)) + x_δ`, which is `δ`-PAC for every
`δ ∈ (0, 1]` by that theorem, has on every admissible model `μ` a sample complexity asymptotically
equal to the characteristic time: `𝔼[τ_δ] / log (1 / δ) → T*(μ)` as `δ → 0`. By the lower bound
`IdentTask.eventually_mul_ofReal_log_le_expectedStoppingTime_of_finite`, no family of
`δ`-correct algorithms does better. -/
theorem tendsto_expectedStoppingTime_trackAndStop_unionBoundThreshold_div_log
    [MeasurableSingletonClass ℐ] (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0)
    (hcorrect : ∀ θ ∈ task.M, task.correct θ = {rec θ})
    (hw_opt : ∀ θ ∈ task.M, w θ ∈ task.optAlloc θ (rec θ))
    (hw_cont : ∀ θ ∈ task.M, ContinuousAt w θ)
    (hrec_eq : ∀ θ ∈ task.M, ∀ᶠ θ' in 𝓝 θ, rec θ' = rec θ)
    (h_lsc : ∀ θ ∈ task.M, LowerSemicontinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 (rec θ)) (Set.univ ×ˢ simplex α) (θ, w θ))
    (h_charTime : ∀ θ ∈ task.M, task.charTime θ ≠ ∞) (hμ : μ ∈ task.M) :
    Tendsto (fun δ ↦ expectedStoppingTime (task.trackAndStop empMean' w hw
        (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
        hrec (hstop δ)) (Environment.bandit (task.ν μ)) / ENNReal.ofReal (log (1 / δ)))
      (𝓝[>] 0) (𝓝 (task.charTime μ)) :=
  tendsto_expectedStoppingTime_trackAndStop_unionBoundThreshold_div_log_of_klDiv_le
    (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
    (fun _ _ _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
    (fun θ _ ↦ mgfDominatedOn_gaussianBandit hνt hσ2 θ)
    (fun θ _ ↦ klDiv_le_expFamilyRate_gaussianBandit hνt hσ2 θ) hcorrect hw_opt hw_cont hrec_eq
    h_lsc h_charTime hμ

end LMLExplore.Identification.IdentTask

/-! ### Asymptotic optimality of Track-and-Stop with C-tracking -/

namespace LMLExplore.Identification.IdentTask

open Filter Topology

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {mℐ : MeasurableSpace ℐ} {task : IdentTask α (α → ℝ) ℐ ℝ}
  {σ2 : ℝ≥0} {w : (α → ℝ) → α → ℝ}
  {hw : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ w (empMean' n h)} {rec : (α → ℝ) → ℐ}
  {hrec : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ rec (empMean' n h)}
  {hstop : ∀ δ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
    (unionBoundLevel (Fintype.card α) δ) n <
      task.glr (task.plugInCost empMean') n h (rec (empMean' n h))}}
  {μ : α → ℝ}

/-- **Track-and-Stop with C-tracking for Gaussian arms is `δ`-PAC** for every `δ ∈ (0, 1]`, with
the thresholds `K log (2 n (n + 1)) + x_δ`, when it tracks optimal allocations that need not be
unique: the targets `w` are allocations; every admissible model `θ` has the single correct answer
`rec θ`, which is the recommendation near `θ`, and `T*(θ) < ∞`; the targets near `θ` are optimal
allocations `w(θ') ∈ w*(θ', ¬rec θ)`; and `(μ', w') ↦ D(μ', w', ¬rec θ)` is continuous at every
point `(θ, v)` with `v` in the simplex, on the allocations of the simplex. -/
theorem isDeltaPAC_cTrackAndStop_unionBoundThreshold_of_mem_optAlloc [MeasurableSingletonClass ℐ]
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0)
    (hcorrect : ∀ θ ∈ task.M, task.correct θ = {rec θ}) (hw_mem : ∀ μ', w μ' ∈ simplex α)
    (hw_opt : ∀ θ ∈ task.M, ∀ᶠ θ' in 𝓝 θ, w θ' ∈ task.optAlloc θ' (rec θ))
    (hrec_eq : ∀ θ ∈ task.M, ∀ᶠ θ' in 𝓝 θ, rec θ' = rec θ)
    (h_cont : ∀ θ ∈ task.M, ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 (rec θ)) (Set.univ ×ˢ simplex α) (θ, v))
    (h_charTime : ∀ θ ∈ task.M, task.charTime θ ≠ ∞) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    task.IsDeltaPAC (task.cTrackAndStop empMean' w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec (hstop δ)) δ :=
  isDeltaPAC_cTrackAndStop_unionBoundThreshold_of_mem_optAlloc_of_klDiv_le
    (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
    (fun _ _ _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
    (fun θ _ ↦ mgfDominatedOn_gaussianBandit hνt hσ2 θ)
    (fun θ _ ↦ klDiv_le_expFamilyRate_gaussianBandit hνt hσ2 θ) hcorrect hw_mem hw_opt hrec_eq
    h_cont h_charTime hδ hδ1

/-- **Asymptotic optimality of Track-and-Stop with C-tracking for Gaussian arms**
[DK19, Theorem 7]. Under the assumptions of
`IdentTask.isDeltaPAC_cTrackAndStop_unionBoundThreshold_of_mem_optAlloc`, Track-and-Stop with
C-tracking and the thresholds `K log (2 n (n + 1)) + x_δ`, which is `δ`-PAC for every
`δ ∈ (0, 1]` by that theorem, has on every admissible model `μ` a sample complexity asymptotically
equal to the characteristic time: `𝔼[τ_δ] / log (1 / δ) → T*(μ)` as `δ → 0`, even where the
optimal allocations are not unique. By
the lower bound `IdentTask.eventually_mul_ofReal_log_le_expectedStoppingTime_of_finite`, no
family of `δ`-correct algorithms does better. -/
theorem tendsto_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_div_log
    [MeasurableSingletonClass ℐ] (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0)
    (hcorrect : ∀ θ ∈ task.M, task.correct θ = {rec θ}) (hw_mem : ∀ μ', w μ' ∈ simplex α)
    (hw_opt : ∀ θ ∈ task.M, ∀ᶠ θ' in 𝓝 θ, w θ' ∈ task.optAlloc θ' (rec θ))
    (hrec_eq : ∀ θ ∈ task.M, ∀ᶠ θ' in 𝓝 θ, rec θ' = rec θ)
    (h_cont : ∀ θ ∈ task.M, ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 (rec θ)) (Set.univ ×ˢ simplex α) (θ, v))
    (h_charTime : ∀ θ ∈ task.M, task.charTime θ ≠ ∞) (hμ : μ ∈ task.M) :
    Tendsto (fun δ ↦ expectedStoppingTime (task.cTrackAndStop empMean' w hw
        (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
        hrec (hstop δ)) (Environment.bandit (task.ν μ)) / ENNReal.ofReal (log (1 / δ)))
      (𝓝[>] 0) (𝓝 (task.charTime μ)) :=
  tendsto_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_div_log_of_klDiv_le
    (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
    (fun _ _ _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
    (fun θ _ ↦ mgfDominatedOn_gaussianBandit hνt hσ2 θ)
    (fun θ _ ↦ klDiv_le_expFamilyRate_gaussianBandit hνt hσ2 θ) hcorrect hw_mem hw_opt hrec_eq
    h_cont h_charTime hμ

end LMLExplore.Identification.IdentTask

/-! ### Sticky Track-and-Stop -/

namespace LMLExplore.Identification.IdentTask

open Filter Topology

/-- For Gaussian arms with a common variance `σ2 ≠ 0`, the models whose arms are within a small
relative entropy of those of a model close to `θ` are close to `θ`: for every neighbourhood `U` of
`θ` there are a neighbourhood `V` of `θ` and `ε > 0` such that every model whose arms are within
relative entropy `ε` of those of a model of `V` is in `U`, since
`KL(𝒩(x, σ2), 𝒩(y, σ2)) = (x - y)² / (2 σ2)`. -/
private lemma exists_mem_nhds_forall_klDiv_le_mem_gaussianBandit {α ℐ : Type*} [Finite α]
    {mα : MeasurableSpace α} [MeasurableSingletonClass α] {task : IdentTask α (α → ℝ) ℐ ℝ}
    {σ2 : ℝ≥0}
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0) (θ : α → ℝ) :
    ∀ U ∈ 𝓝 θ, ∃ V ∈ 𝓝 θ, ∃ ε : ℝ, 0 < ε ∧ ∀ μ' ∈ V, ∀ θ' ∈ task.M,
      (∀ a, klDiv (task.ν μ' a) (task.ν θ' a) ≤ ENNReal.ofReal ε) → θ' ∈ U := by
  intro U hU
  have := Fintype.ofFinite α
  obtain ⟨d, hd, hdU⟩ := Metric.mem_nhds_iff.1 hU
  have hσ : (0 : ℝ) < σ2 := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hσ2)
  refine ⟨Metric.ball θ (d / 2), Metric.ball_mem_nhds _ (by positivity), d ^ 2 / (8 * σ2),
    by positivity, fun μ' hμ' θ' _ hkl ↦ hdU ((dist_pi_lt_iff hd).2 fun a ↦ ?_)⟩
  -- `(μ' a - θ' a)² / (2 σ2) ≤ d² / (8 σ2)`, so `|μ' a - θ' a| ≤ d / 2`.
  have h := hkl a
  rw [hνt, Bandits.klDiv_gaussianBandit μ' θ' hσ2, ENNReal.ofReal_le_ofReal_iff (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)] at h
  have h_sq : (μ' a - θ' a) ^ 2 ≤ (d / 2) ^ 2 := by nlinarith
  have h_abs : |μ' a - θ' a| ≤ d / 2 := abs_le_of_sq_le_sq' h_sq (by positivity) |> abs_le.2
  have h_μ' : dist (μ' a) (θ a) < d / 2 := (dist_pi_lt_iff (by positivity)).1 hμ' a
  rw [Real.dist_eq] at h_μ' ⊢
  calc |θ' a - θ a| ≤ |μ' a - θ' a| + |μ' a - θ a| := by
        rw [abs_sub_comm (μ' a)]; exact abs_sub_le _ _ _
  _ < d / 2 + d / 2 := add_lt_add_of_le_of_lt h_abs h_μ'
  _ = d := add_halves d

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {mℐ : MeasurableSpace ℐ} [LinearOrder ℐ] [WellFoundedLT ℐ]
  [Nonempty ℐ] [Finite ℐ] {task : IdentTask α (α → ℝ) ℐ ℝ} {σ2 : ℝ≥0}
  {r : (n : ℕ) → Hist Unit α ℝ n → ℝ≥0∞} {p : ℝ} {w : ℐ → (α → ℝ) → α → ℝ}
  {hw : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦
    w (task.stickyAnswer (task.confidenceRegion empMean' r n h)) (empMean' n h)}
  {rec : (n : ℕ) → Hist Unit α ℝ n → ℐ} {hrec : ∀ n, Measurable (rec n)}
  {hstop : ∀ δ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
    (unionBoundLevel (Fintype.card α) δ) n < task.glr (task.plugInCost empMean') n h (rec n h)}}
  {μ : α → ℝ}

/-- **Sample complexity of Sticky Track-and-Stop for Gaussian arms** [DK19, Theorem 11]. For
Gaussian arms with a common variance `σ2 ≠ 0`, finitely many answers and confidence regions whose
radii are at least `K log (2 n (n + 1)) + x_{(n + 1) ^ (-p)}` for some `p > 2` and `o(√n)`
(`eventually_unionBoundThreshold_unionBoundLevel_le_mul_sqrt`), let the targets be
allocations, those of the least oracle answer of the admissible model `μ` being optimal allocations
near `μ`, let the recommendation have a GLR statistic at least that of the sticky answer, and let
the costs be continuous at `μ`. Then Sticky Track-and-Stop with the thresholds
`K log (2 n (n + 1)) + x_δ` satisfies `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every
`c > T*(μ)`, even when `μ` has several oracle answers. -/
theorem eventually_expectedStoppingTime_stickyTrackAndStop_unionBoundThreshold_le
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0) (hμM : μ ∈ task.M)
    (hp : 2 < p)
    (hr_ge : ∀ (n : ℕ) h, unionBoundThreshold (Fintype.card α)
      (unionBoundLevel (Fintype.card α) (((n : ℝ) + 1) ^ p)⁻¹) n ≤ r n h)
    (hr_le : ∀ ε > 0, ∀ᶠ n in atTop, ∀ h, r n h ≤ ENNReal.ofReal (ε * √(n : ℝ)))
    (hw_mem : ∀ i μ', w i μ' ∈ simplex α)
    (hw_opt : ∀ᶠ μ' in 𝓝 μ,
      w (task.stickyAnswer {μ}) μ' ∈ task.optAlloc μ' (task.stickyAnswer {μ}))
    (hrec_ge : ∀ n h, task.glr (task.plugInCost empMean') n h
      (task.stickyAnswer (task.confidenceRegion empMean' r n h)) ≤
        task.glr (task.plugInCost empMean') n h (rec n h))
    (h_cont : ∀ i, ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (μ, v))
    {c : ℝ≥0} (hc : task.charTime μ < c) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.stickyTrackAndStop empMean'
      (task.confidenceRegion empMean' r) w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec (hstop δ)) (Environment.bandit (task.ν μ)) ≤ c * ENNReal.ofReal (log (1 / δ)) :=
  eventually_expectedStoppingTime_stickyTrackAndStop_unionBoundThreshold_le_of_klDiv_le
    (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
    (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _) (mgfDominatedOn_gaussianBandit hνt hσ2 μ)
    (klDiv_le_expFamilyRate_gaussianBandit hνt hσ2 μ) hμM
    (exists_mem_nhds_forall_klDiv_le_mem_gaussianBandit hνt hσ2 μ) hp hr_ge hr_le hw_mem hw_opt
    hrec_ge h_cont hc

/-- **Sticky Track-and-Stop for Gaussian arms is `δ`-PAC** [DK19, Theorems 10–11] for every
`δ ∈ (0, 1]`, with the thresholds `K log (2 n (n + 1)) + x_δ`, on every task with finitely many
answers, under the assumptions of
`IdentTask.eventually_expectedStoppingTime_stickyTrackAndStop_unionBoundThreshold_le` on every
admissible model `θ`, with `T*(θ) < ∞`. -/
theorem isDeltaPAC_stickyTrackAndStop_unionBoundThreshold [MeasurableSingletonClass ℐ]
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0) (hp : 2 < p)
    (hr_ge : ∀ (n : ℕ) h, unionBoundThreshold (Fintype.card α)
      (unionBoundLevel (Fintype.card α) (((n : ℝ) + 1) ^ p)⁻¹) n ≤ r n h)
    (hr_le : ∀ ε > 0, ∀ᶠ n in atTop, ∀ h, r n h ≤ ENNReal.ofReal (ε * √(n : ℝ)))
    (hw_mem : ∀ i μ', w i μ' ∈ simplex α)
    (hw_opt : ∀ θ ∈ task.M, ∀ᶠ μ' in 𝓝 θ,
      w (task.stickyAnswer {θ}) μ' ∈ task.optAlloc μ' (task.stickyAnswer {θ}))
    (hrec_ge : ∀ n h, task.glr (task.plugInCost empMean') n h
      (task.stickyAnswer (task.confidenceRegion empMean' r n h)) ≤
        task.glr (task.plugInCost empMean') n h (rec n h))
    (h_cont : ∀ θ ∈ task.M, ∀ i, ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (θ, v))
    (h_charTime : ∀ θ ∈ task.M, task.charTime θ ≠ ∞) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    task.IsDeltaPAC (task.stickyTrackAndStop empMean' (task.confidenceRegion empMean' r) w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec (hstop δ)) δ :=
  isDeltaPAC_stickyTrackAndStop_unionBoundThreshold_of_klDiv_le
    (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
    (fun _ _ _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
    (fun θ _ ↦ mgfDominatedOn_gaussianBandit hνt hσ2 θ)
    (fun θ _ ↦ klDiv_le_expFamilyRate_gaussianBandit hνt hσ2 θ)
    (fun θ _ ↦ exists_mem_nhds_forall_klDiv_le_mem_gaussianBandit hνt hσ2 θ) hp hr_ge hr_le hw_mem
    hw_opt hrec_ge h_cont h_charTime hδ hδ1

end LMLExplore.Identification.IdentTask
