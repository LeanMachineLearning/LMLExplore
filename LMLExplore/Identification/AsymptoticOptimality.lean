/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.ExpFamilyThreshold
public import LMLExplore.Identification.MultipleAnswerLowerBound

/-!
# Asymptotic optimality of Track-and-Stop for arms dominated by exponential families

Let the models of an identification task be vectors of means `μ : α → ℝ` of arms with real
observations, and let the arm `a` be described by a nondegenerate exponential family `(ρ a, T a)`
on a measurable space `𝓧`, with extended divergence `dbar_a`
(`MeasureTheory.Measure.expFamilyRate`).
Suppose that on every admissible model `θ`
* the vector `θ` is a vector of means of the families;
* the rewards of each arm `a` are dominated on `Set.univ`, in moment generating function, by the
  member of mean `θ a` of `(ρ a, T a)`;
* the relative entropy from the arm `a` of any vector of means `μ'` to the arm `a` of `θ` is at most
  `dbar_a(μ' a, θ a)`.

The last condition holds with equality when the arms of the models are the members of the families
and `μ'` is a vector of means of the families, as for Gaussian arms of known variance, whose means
are all the reals. It also holds for Bernoulli arms indexed by real means, the arm `a` of `μ'` being
the Bernoulli law of mean `μ' a` projected on `[0, 1]`: the relative entropy is `klBer (μ' a) (θ a)`
for `μ' a ∈ [0, 1]`, the boundary empirical means `0` and `1` included, and `dbar` is infinite
elsewhere (`LMLExplore.Bandits.klDiv_bernoulliBandit_projIcc_le_expFamilyRate`).

Under the last condition, the plug-in statistic of the empirical means, the statistic of the
stopping rule of Track-and-Stop (`Identification/TrackAndStop.lean`), is at most the generalized
likelihood ratio evidence of `Identification/ExpFamilyThreshold.lean`. Hence Track-and-Stop with the
thresholds `K log (2 n (n + 1)) + x_δ` stops with an incorrect answer with probability at most `δ`,
whatever its target map and its recommendation rule [GK16, Proposition 12; LS, Lemma 33.7]. When it
tracks optimal allocations, `Identification/TrackAndStop.lean` shows that it stops almost surely and
that `𝔼[τ_δ] ≤ c log (1 / δ)` for small `δ`, for every `c > T*(μ)`. It is therefore `δ`-PAC for
every `δ ∈ (0, 1]`, and together with the lower bound of `Identification/LowerBound.lean`,
`𝔼[τ_δ] / log (1 / δ)` tends to `T*(μ)` on every admissible model `μ`: Track-and-Stop is
asymptotically optimal [GK16, Theorem 14]. The same holds for Track-and-Stop with C-tracking, whose
targets may be any selection of the optimal allocations, even where these are not unique
[DK19, Theorem 7].

The Gaussian instances are in `Identification/GaussianThreshold.lean`, and the Bernoulli instances
in `Identification/BernoulliThreshold.lean`.

## Main statements

* `IdentTask.isDeltaPAC_trackAndStop_unionBoundThreshold_of_klDiv_le`: Track-and-Stop with the
  thresholds `K log (2 n (n + 1)) + x_δ` is `δ`-PAC as soon as it stops almost surely on every
  admissible model, whatever its target map and its recommendation rule.
* `IdentTask.isDeltaPAC_trackAndStop_unionBoundThreshold_of_mem_optAlloc_of_klDiv_le`: when it
  tracks optimal allocations, it is `δ`-PAC for every `δ ∈ (0, 1]`.
* `IdentTask.tendsto_expectedStoppingTime_trackAndStop_unionBoundThreshold_div_log_of_klDiv_le`:
  **asymptotic optimality**, `𝔼[τ_δ] / log (1 / δ) → T*(μ)` as `δ → 0`.
* `IdentTask.isDeltaPAC_cTrackAndStop_unionBoundThreshold_of_mem_optAlloc_of_klDiv_le`,
  `IdentTask.tendsto_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_div_log_of_klDiv_le`:
  the same for Track-and-Stop with C-tracking.

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, Theorem 7.
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Proposition 12 and Theorem 14.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 33.7.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Real Filter Topology

open scoped ENNReal NNReal

namespace LMLExplore.Identification.IdentTask

variable {α ℐ 𝓧 : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {mℐ : MeasurableSpace ℐ} {task : IdentTask α (α → ℝ) ℐ ℝ}
  {m𝓧 : MeasurableSpace 𝓧} {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {δ : ℝ}

/-! ### Track-and-Stop -/

/-- **Track-and-Stop for arms dominated by exponential families is `δ`-PAC**
([GK16, Proposition 12], [LS, Lemma 33.7]), whatever its target map and its recommendation rule.
If on every admissible model `θ` the rewards of each arm `a` are dominated on `Set.univ`, in moment
generating function, by the member of mean `θ a` of the exponential family `(ρ a, T a)`, and the
relative entropy from the arms of any vector of means to those of `θ` is at most the extended
divergence of the families, then for `δ ∈ (0, 1]`, Track-and-Stop with the empirical means as
estimator and the thresholds `K log (2 n (n + 1)) + x_δ` is `δ`-PAC on the task, provided it stops
almost surely on every admissible model. -/
theorem isDeltaPAC_trackAndStop_unionBoundThreshold_of_klDiv_le (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {w : (α → ℝ) → α → ℝ} (hw : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ w (empMean' n h))
    {rec : (α → ℝ) → ℐ} (hrec : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ rec (empMean' n h))
    (hstop : ∀ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
      (unionBoundLevel (Fintype.card α) δ) n <
        task.glr (task.plugInCost empMean') n h (rec (empMean' n h))})
    (hμ : ∀ θ ∈ task.M, ∀ a, θ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ θ ∈ task.M, ∀ a, MGFDominatedOn id (task.ν θ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (θ a))) Set.univ)
    (hkl : ∀ θ ∈ task.M, ∀ (μ' : α → ℝ) a,
      klDiv (task.ν μ' a) (task.ν θ a) ≤ (ρ a).expFamilyRate (T a) (μ' a) (θ a))
    (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (h_stops : ∀ θ ∈ task.M, StopsAS (task.trackAndStop empMean' w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec hstop) (Environment.bandit (task.ν θ))) :
    task.IsDeltaPAC (task.trackAndStop empMean' w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec hstop) δ := by
  simp only [trackAndStop_def] at h_stops ⊢
  exact isDeltaPAC_glrt_unionBoundThreshold_of_klDiv_le _ _ hδ hδ1 hstop hμ hν hkl hc h_stops

variable {w : (α → ℝ) → α → ℝ} {hw : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ w (empMean' n h)}
  {rec : (α → ℝ) → ℐ} {hrec : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ rec (empMean' n h)}
  {hstop : ∀ δ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
    (unionBoundLevel (Fintype.card α) δ) n <
      task.glr (task.plugInCost empMean') n h (rec (empMean' n h))}}
  {μ : α → ℝ}

/-- **Track-and-Stop for arms dominated by exponential families is `δ`-PAC** for every
`δ ∈ (0, 1]`, with the thresholds `K log (2 n (n + 1)) + x_δ`, when it tracks optimal allocations.
Let the families be nondegenerate, and on every admissible model `θ` let the rewards of each arm
`a` be dominated on `Set.univ` by the member of mean `θ a` of `(ρ a, T a)`, and the relative entropy
from the arms of any vector of means to those of `θ` be at most the extended divergence of the
families. Let every admissible model `θ` have the single correct answer `rec θ`, which is the
recommendation near `θ`, and `T*(θ) < ∞`; let the target map `w` be continuous at `θ` with `w(θ)` an
optimal allocation `w*(θ, ¬rec θ)`; and let `(μ', w') ↦ D(μ', w', ¬rec θ)` be lower semicontinuous
at `(θ, w(θ))` on the allocations of the simplex. -/
theorem isDeltaPAC_trackAndStop_unionBoundThreshold_of_mem_optAlloc_of_klDiv_le
    [MeasurableSingletonClass ℐ] (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hμ : ∀ θ ∈ task.M, ∀ a, θ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ θ ∈ task.M, ∀ a, MGFDominatedOn id (task.ν θ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (θ a))) Set.univ)
    (hkl : ∀ θ ∈ task.M, ∀ (μ' : α → ℝ) a,
      klDiv (task.ν μ' a) (task.ν θ a) ≤ (ρ a).expFamilyRate (T a) (μ' a) (θ a))
    (hcorrect : ∀ θ ∈ task.M, task.correct θ = {rec θ})
    (hw_opt : ∀ θ ∈ task.M, w θ ∈ task.optAlloc θ (rec θ))
    (hw_cont : ∀ θ ∈ task.M, ContinuousAt w θ)
    (hrec_eq : ∀ θ ∈ task.M, ∀ᶠ θ' in 𝓝 θ, rec θ' = rec θ)
    (h_lsc : ∀ θ ∈ task.M, LowerSemicontinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 (rec θ)) (Set.univ ×ˢ simplex α) (θ, w θ))
    (h_charTime : ∀ θ ∈ task.M, task.charTime θ ≠ ∞) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    task.IsDeltaPAC (task.trackAndStop empMean' w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec (hstop δ)) δ :=
  isDeltaPAC_trackAndStop_unionBoundThreshold_of_klDiv_le hδ hδ1 hw hrec (hstop δ) hμ hν hkl
    (fun θ hθ ↦ hcorrect θ hθ ▸ measurableSet_singleton _) fun θ hθ ↦
    stopsAS_trackAndStop_unionBoundThreshold hT (hμ θ hθ) (hν θ hθ) (hcorrect θ hθ) (hw_opt θ hθ)
      (hw_cont θ hθ) (hrec_eq θ hθ) (h_lsc θ hθ) (h_charTime θ hθ) hδ hδ1

/-- **Asymptotic optimality of Track-and-Stop for arms dominated by exponential families**
[GK16, Theorem 14]. Under the assumptions of
`IdentTask.isDeltaPAC_trackAndStop_unionBoundThreshold_of_mem_optAlloc_of_klDiv_le`,
Track-and-Stop with the thresholds `K log (2 n (n + 1)) + x_δ`, which is `δ`-PAC for every
`δ ∈ (0, 1]` by that theorem, has on every admissible model `μ` a sample complexity asymptotically
equal to the characteristic time: `𝔼[τ_δ] / log (1 / δ) → T*(μ)` as `δ → 0`. By the lower bound
`IdentTask.eventually_mul_ofReal_log_le_expectedStoppingTime_of_finite`, no family of
`δ`-correct algorithms does better. -/
theorem tendsto_expectedStoppingTime_trackAndStop_unionBoundThreshold_div_log_of_klDiv_le
    [MeasurableSingletonClass ℐ] (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hμ : ∀ θ ∈ task.M, ∀ a, θ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ θ ∈ task.M, ∀ a, MGFDominatedOn id (task.ν θ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (θ a))) Set.univ)
    (hkl : ∀ θ ∈ task.M, ∀ (μ' : α → ℝ) a,
      klDiv (task.ν μ' a) (task.ν θ a) ≤ (ρ a).expFamilyRate (T a) (μ' a) (θ a))
    (hcorrect : ∀ θ ∈ task.M, task.correct θ = {rec θ})
    (hw_opt : ∀ θ ∈ task.M, w θ ∈ task.optAlloc θ (rec θ))
    (hw_cont : ∀ θ ∈ task.M, ContinuousAt w θ)
    (hrec_eq : ∀ θ ∈ task.M, ∀ᶠ θ' in 𝓝 θ, rec θ' = rec θ)
    (h_lsc : ∀ θ ∈ task.M, LowerSemicontinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 (rec θ)) (Set.univ ×ˢ simplex α) (θ, w θ))
    (h_charTime : ∀ θ ∈ task.M, task.charTime θ ≠ ∞) (hμM : μ ∈ task.M) :
    Tendsto (fun δ ↦ expectedStoppingTime (task.trackAndStop empMean' w hw
        (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
        hrec (hstop δ)) (Environment.bandit (task.ν μ)) / ENNReal.ofReal (log (1 / δ)))
      (𝓝[>] 0) (𝓝 (task.charTime μ)) := by
  refine tendsto_expectedStoppingTime_div_log_of_finite ?_ hμM
    (hcorrect μ hμM ▸ Set.finite_singleton _) fun c hc ↦ ?_
  · filter_upwards [Ioc_mem_nhdsGT one_pos] with δ hδ
    exact (isDeltaPAC_trackAndStop_unionBoundThreshold_of_mem_optAlloc_of_klDiv_le hT hμ hν hkl
      hcorrect hw_opt hw_cont hrec_eq h_lsc h_charTime hδ.1 hδ.2).isDeltaCorrect
  · exact eventually_expectedStoppingTime_trackAndStop_unionBoundThreshold_le hT (hμ μ hμM)
      (hν μ hμM) (hcorrect μ hμM) (hw_opt μ hμM) (hw_cont μ hμM) (hrec_eq μ hμM) (h_lsc μ hμM) hc

/-! ### Track-and-Stop with C-tracking -/

/-- **Track-and-Stop with C-tracking for arms dominated by exponential families is `δ`-PAC** for
every `δ ∈ (0, 1]`, with the thresholds `K log (2 n (n + 1)) + x_δ`, when it tracks optimal
allocations that need not be unique. Let the families be nondegenerate, and on every admissible
model `θ` let the rewards of each arm `a` be dominated on `Set.univ` by the member of mean `θ a` of
`(ρ a, T a)`, and the relative entropy from the arms of any vector of means to those of `θ` be at
most the extended divergence of the families. Let the targets `w` be allocations; let every
admissible model `θ` have the single correct answer `rec θ`, which is the recommendation near `θ`,
and `T*(θ) < ∞`; let the targets near `θ` be optimal allocations `w(θ') ∈ w*(θ', ¬rec θ)`; and let
`(μ', w') ↦ D(μ', w', ¬rec θ)` be continuous at every point `(θ, v)` with `v` in the simplex, on the
allocations of the simplex. -/
theorem isDeltaPAC_cTrackAndStop_unionBoundThreshold_of_mem_optAlloc_of_klDiv_le
    [MeasurableSingletonClass ℐ] (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hμ : ∀ θ ∈ task.M, ∀ a, θ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ θ ∈ task.M, ∀ a, MGFDominatedOn id (task.ν θ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (θ a))) Set.univ)
    (hkl : ∀ θ ∈ task.M, ∀ (μ' : α → ℝ) a,
      klDiv (task.ν μ' a) (task.ν θ a) ≤ (ρ a).expFamilyRate (T a) (μ' a) (θ a))
    (hcorrect : ∀ θ ∈ task.M, task.correct θ = {rec θ}) (hw_mem : ∀ μ', w μ' ∈ simplex α)
    (hw_opt : ∀ θ ∈ task.M, ∀ᶠ θ' in 𝓝 θ, w θ' ∈ task.optAlloc θ' (rec θ))
    (hrec_eq : ∀ θ ∈ task.M, ∀ᶠ θ' in 𝓝 θ, rec θ' = rec θ)
    (h_cont : ∀ θ ∈ task.M, ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 (rec θ)) (Set.univ ×ˢ simplex α) (θ, v))
    (h_charTime : ∀ θ ∈ task.M, task.charTime θ ≠ ∞) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    task.IsDeltaPAC (task.cTrackAndStop empMean' w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec (hstop δ)) δ := by
  have h_stops (θ : α → ℝ) (hθ : θ ∈ task.M) := stopsAS_cTrackAndStop_unionBoundThreshold
    (hw := hw) (hrec := hrec) (hstop := hstop) hT (hμ θ hθ) (hν θ hθ) (hcorrect θ hθ) hw_mem
    (hw_opt θ hθ) (hrec_eq θ hθ) (h_cont θ hθ) (h_charTime θ hθ) hδ hδ1
  simp only [cTrackAndStop_def] at h_stops ⊢
  exact isDeltaPAC_glrt_unionBoundThreshold_of_klDiv_le _ _ hδ hδ1 (hstop δ) hμ hν hkl
    (fun θ hθ ↦ hcorrect θ hθ ▸ measurableSet_singleton _) h_stops

/-- **Asymptotic optimality of Track-and-Stop with C-tracking for arms dominated by exponential
families** [DK19, Theorem 7]. Under the assumptions of
`IdentTask.isDeltaPAC_cTrackAndStop_unionBoundThreshold_of_mem_optAlloc_of_klDiv_le`,
Track-and-Stop with C-tracking and the thresholds `K log (2 n (n + 1)) + x_δ`, which is `δ`-PAC for
every `δ ∈ (0, 1]` by that theorem, has on every admissible model `μ` a sample complexity
asymptotically equal to the characteristic time: `𝔼[τ_δ] / log (1 / δ) → T*(μ)` as `δ → 0`, even
where the optimal allocations are not unique. By the lower bound
`IdentTask.eventually_mul_ofReal_log_le_expectedStoppingTime_of_finite`, no family of
`δ`-correct algorithms does better. -/
theorem tendsto_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_div_log_of_klDiv_le
    [MeasurableSingletonClass ℐ] (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hμ : ∀ θ ∈ task.M, ∀ a, θ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ θ ∈ task.M, ∀ a, MGFDominatedOn id (task.ν θ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (θ a))) Set.univ)
    (hkl : ∀ θ ∈ task.M, ∀ (μ' : α → ℝ) a,
      klDiv (task.ν μ' a) (task.ν θ a) ≤ (ρ a).expFamilyRate (T a) (μ' a) (θ a))
    (hcorrect : ∀ θ ∈ task.M, task.correct θ = {rec θ}) (hw_mem : ∀ μ', w μ' ∈ simplex α)
    (hw_opt : ∀ θ ∈ task.M, ∀ᶠ θ' in 𝓝 θ, w θ' ∈ task.optAlloc θ' (rec θ))
    (hrec_eq : ∀ θ ∈ task.M, ∀ᶠ θ' in 𝓝 θ, rec θ' = rec θ)
    (h_cont : ∀ θ ∈ task.M, ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 (rec θ)) (Set.univ ×ˢ simplex α) (θ, v))
    (h_charTime : ∀ θ ∈ task.M, task.charTime θ ≠ ∞) (hμM : μ ∈ task.M) :
    Tendsto (fun δ ↦ expectedStoppingTime (task.cTrackAndStop empMean' w hw
        (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
        hrec (hstop δ)) (Environment.bandit (task.ν μ)) / ENNReal.ofReal (log (1 / δ)))
      (𝓝[>] 0) (𝓝 (task.charTime μ)) := by
  refine tendsto_expectedStoppingTime_div_log_of_finite ?_ hμM
    (hcorrect μ hμM ▸ Set.finite_singleton _) fun c hc ↦ ?_
  · filter_upwards [Ioc_mem_nhdsGT one_pos] with δ hδ
    exact (isDeltaPAC_cTrackAndStop_unionBoundThreshold_of_mem_optAlloc_of_klDiv_le hT hμ hν hkl
      hcorrect hw_mem hw_opt hrec_eq h_cont h_charTime hδ.1 hδ.2).isDeltaCorrect
  · exact eventually_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_le hT (hμ μ hμM)
      (hν μ hμM) (hcorrect μ hμM) hw_mem (hw_opt μ hμM) (hrec_eq μ hμM) (h_cont μ hμM) hc

end LMLExplore.Identification.IdentTask
