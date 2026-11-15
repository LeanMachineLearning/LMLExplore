/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.GaussianThreshold
public import LMLExplore.Identification.Task.BestArm.Recommendation

/-!
# Track-and-Stop on best arm identification

The sample complexity theorems of Track-and-Stop (`Identification/TrackAndStop.lean`) and its
asymptotic optimality for Gaussian arms (`Identification/GaussianThreshold.lean`) hold for every
task, under hypotheses on the task at the true model `μ`: the target map `w` is continuous at `μ`,
the cost of the alternatives `(μ', w') ↦ D(μ', w', ¬i)` is lower semicontinuous (for D-tracking)
or continuous (for C-tracking) at `μ`, the recommendation is locally constant at `μ` and, for the
limit theorem, the characteristic time `T*(μ)` is finite. This file discharges all of them on best
arm identification [GK16, Theorem 14, Proposition 6], so that its statements assume none of them.

The models are vectors of means `μ : α → ℝ` of arms in one exponential family `(ρ, T)` with
divergence `d`, the task `(baiTask ν id).restrict {μ | ∀ c, μ c ∈ ρ.expFamilyMeans T}`, and the
admissible models are those with a unique best arm `a`.

* The recommendation `rec` of a best arm of every admissible model, typically the empirical best
  arm `rec(μ̂)`, is `a` near `μ`, since the models with unique best arm `a` form an open set
  (`eventually_eq_of_forall_mem_correct_baiTask_restrict`, in
  `Task/BestArm/Recommendation.lean`).
* Targets `w(μ') ∈ w*(μ', ¬a)` that are optimal allocations near `μ` are continuous at `μ`, since
  the optimal allocation is unique [GK16, Proposition 6]
  (`continuousAt_of_mem_optAlloc_baiTask_restrict`).
* The cost of the alternatives is continuous at `μ` in the model and the allocation, from its
  closed form [GK16, Lemma 3] (`continuousWithinAt_altCost_baiTask_restrict`).
* The value `D(μ, ¬a)` of the game is positive (`answerValue_baiTask_restrict_pos`), so that
  `T*(μ) = D(μ, ¬a)⁻¹` is finite.

With these, Track-and-Stop with D-tracking or with C-tracking, the empirical means as estimator and
thresholds `β δ n h ≤ log (r n / δ)` for `n ≥ n₀`, with `r n = O(n ^ p)`, satisfies
`limsup_{δ → 0} 𝔼_μ[τ_δ] / log (1 / δ) ≤ T*(μ)` at every admissible `μ`.

For Gaussian arms with a common variance `σ2 ≠ 0`, every vector of means is a vector of means of the
family of `𝒩(0, σ2)`, and the task is `baiTask (Bandits.gaussianBandit · σ2) id`. When the targets
are optimal allocations at every admissible model, Track-and-Stop with the thresholds
`K log (2 n (n + 1)) + x_δ` (`unionBoundThreshold`, `unionBoundLevel`) is `δ`-PAC for every
`δ ∈ (0, 1]` and `𝔼_μ[τ_δ] / log (1 / δ) → T*(μ)` at every admissible `μ`, with D-tracking
[GK16, Theorem 14] and with C-tracking [DK19, Theorem 7]. For two arms `a` and `b` with
`μ b < μ a`, the limit is `8 σ2 / (μ a - μ b)²` [KCG16, Section 3].

## Main statements

* `limsup_expectedStoppingTime_trackAndStop_baiTask_restrict_div_log_le`,
  `limsup_expectedStoppingTime_cTrackAndStop_baiTask_restrict_div_log_le`:
  for arms in an exponential family, `limsup_{δ → 0} 𝔼_μ[τ_δ] / log (1 / δ) ≤ T*(μ)` for
  Track-and-Stop with D-tracking [GK16, Theorem 14] and with C-tracking [DK19, Theorem 7].
* `isDeltaPAC_trackAndStop_baiTask_gaussianBandit`,
  `tendsto_expectedStoppingTime_trackAndStop_baiTask_gaussianBandit_div_log`:
  for Gaussian arms, Track-and-Stop with the union-bound thresholds is `δ`-PAC and
  `𝔼_μ[τ_δ] / log (1 / δ) → T*(μ)` [GK16, Theorem 14].
* `isDeltaPAC_cTrackAndStop_baiTask_gaussianBandit`,
  `tendsto_expectedStoppingTime_cTrackAndStop_baiTask_gaussianBandit_div_log`:
  the same for Track-and-Stop with C-tracking [DK19, Theorem 7].
* `tendsto_expectedStoppingTime_trackAndStop_baiTask_gaussianBandit_div_log_of_forall_eq_or_eq`:
  for two Gaussian arms `a`, `b` with `μ b < μ a`,
  `𝔼_μ[τ_δ] / log (1 / δ) → 8 σ2 / (μ a - μ b)²`.

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, Theorem 7.
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Lemma 3, Proposition 6 and Theorem 14.
* [KCG16] E. Kaufmann, O. Cappé and A. Garivier, *On the complexity of best-arm identification in
  multi-armed bandit models*, JMLR 17 (2016), Section 3.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Real Filter Topology
open scoped ENNReal NNReal

namespace LMLExplore.Identification

/-! ### Arms in an exponential family -/

section ExpFamily

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {ν : (α → ℝ) → Kernel α ℝ} [∀ μ, IsMarkovKernel (ν μ)]
  {ρ : Measure ℝ} {T : ℝ → ℝ} {μ : α → ℝ} {a : α} {w : (α → ℝ) → α → ℝ}
  {hw : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ w (empMean' n h)} {rec : (α → ℝ) → α}
  {hrec : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ rec (empMean' n h)}
  {β : ℝ → (n : ℕ) → Hist Unit α ℝ n → ℝ≥0∞}
  {hstop : ∀ δ n, MeasurableSet {h | β δ n h <
    ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).glr
      (((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).plugInCost empMean') n h
      (rec (empMean' n h))}}
  {r : ℕ → ℝ} {p : ℝ} {n₀ : ℕ}

/-- **Sample complexity of Track-and-Stop on best arm identification** [GK16, Theorem 14], with no
continuity hypothesis. Let the arms be in one nondegenerate exponential family `(ρ, T)` with
divergence `d`, in the sense that `KL(ν_c(μ), ν_c(μ')) = d(μ c, μ' c)` for all vectors of means
`μ`, `μ'` of the family, let `μ` be a vector of means of the family with unique best arm `a`, whose
arms have rewards dominated on `Set.univ` by the members of the family of means `μ c`. Let the
targets `w(μ')` be optimal allocations `w*(μ', ¬a)` near `μ`, and let the recommendation answer a
best arm of every admissible model. Then for thresholds `β δ n h ≤ log (r n / δ)` (for `n ≥ n₀`)
with `r n = O(n ^ p)`, Track-and-Stop with the empirical means as estimator satisfies
`limsup_{δ → 0} 𝔼_μ[τ_δ] / log (1 / δ) ≤ T*(μ)`. -/
theorem limsup_expectedStoppingTime_trackAndStop_baiTask_restrict_div_log_le
    (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ μ' : α → ℝ, (∀ c, μ c ∈ ρ.expFamilyMeans T) → (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T) (ha : ∀ b ≠ a, μ b < μ a)
    (hνμ : ∀ c, MGFDominatedOn id (ν μ c) T (ρ.expFamily T (ρ.natParam T (μ c))) Set.univ)
    (hw_opt : ∀ᶠ μ' in 𝓝 μ,
      w μ' ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ' a)
    (hrec_correct : ∀ μ' ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).M,
      rec μ' ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).correct μ')
    (hr : r =O[atTop] fun n ↦ (n : ℝ) ^ p)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ n ≥ n₀, ∀ h, β δ n h ≤ ENNReal.ofReal (log (r n / δ))) :
    limsup (fun δ ↦ expectedStoppingTime
        (((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).trackAndStop empMean' w
          hw (β δ) rec hrec (hstop δ)) (Environment.bandit (ν μ)) /
        ENNReal.ofReal (log (1 / δ))) (𝓝[>] 0) ≤
      ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).charTime μ := by
  set task := (baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}
  have hνt : task.ν = ν := by rw [IdentTask.ν_restrict, ν_baiTask]
  have hcorrect : task.correct μ = {a} := by
    rw [IdentTask.correct_restrict, correct_baiTask_eq_singleton_iff]
    exact ha
  refine limsup_expectedStoppingTime_div_log_le fun c hc ↦ ?_
  have h := task.eventually_expectedStoppingTime_trackAndStop_le_of_charTime_lt
    (mℐ := mα) (hw := hw) (hrec := hrec) (ρ := fun _ ↦ ρ) (T := fun _ ↦ T) (hstop := hstop)
    (fun _ ↦ hT) hμ (hνt ▸ hνμ) hcorrect
    hw_opt.self_of_nhds (continuousAt_of_mem_optAlloc_baiTask_restrict ν hT hν hμ ha hw_opt)
    (eventually_eq_of_forall_mem_correct_baiTask_restrict ν continuous_apply
      (Measure.setOf_forall_mem_expFamilyMeans_mem_nhds (fun _ ↦ hT) hμ) hrec_correct ha)
    (continuousWithinAt_altCost_baiTask_restrict ν hT hν hμ ha
      ((IdentTask.mem_optAlloc_iff _).1 hw_opt.self_of_nhds).1).lowerSemicontinuousWithinAt
    hc hr hβ
  simpa only [hνt] using h

/-- **Sample complexity of Track-and-Stop with C-tracking on best arm identification**
[DK19, Theorem 7], with no continuity hypothesis. Under the assumptions of
`limsup_expectedStoppingTime_trackAndStop_baiTask_restrict_div_log_le`, with targets that are
allocations everywhere, Track-and-Stop with C-tracking and the empirical means as estimator
satisfies `limsup_{δ → 0} 𝔼_μ[τ_δ] / log (1 / δ) ≤ T*(μ)`. -/
theorem limsup_expectedStoppingTime_cTrackAndStop_baiTask_restrict_div_log_le
    (hT : ∀ c, ¬ T =ᵐ[ρ] fun _ ↦ c)
    (hν : ∀ μ μ' : α → ℝ, (∀ c, μ c ∈ ρ.expFamilyMeans T) → (∀ c, μ' c ∈ ρ.expFamilyMeans T) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal (ρ.expFamilyDiv T (μ c) (μ' c)))
    (hμ : ∀ c, μ c ∈ ρ.expFamilyMeans T) (ha : ∀ b ≠ a, μ b < μ a)
    (hνμ : ∀ c, MGFDominatedOn id (ν μ c) T (ρ.expFamily T (ρ.natParam T (μ c))) Set.univ)
    (hw_mem : ∀ μ', w μ' ∈ simplex α)
    (hw_opt : ∀ᶠ μ' in 𝓝 μ,
      w μ' ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).optAlloc μ' a)
    (hrec_correct : ∀ μ' ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).M,
      rec μ' ∈ ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).correct μ')
    (hr : r =O[atTop] fun n ↦ (n : ℝ) ^ p)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ n ≥ n₀, ∀ h, β δ n h ≤ ENNReal.ofReal (log (r n / δ))) :
    limsup (fun δ ↦ expectedStoppingTime
        (((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).cTrackAndStop empMean' w
          hw (β δ) rec hrec (hstop δ)) (Environment.bandit (ν μ)) /
        ENNReal.ofReal (log (1 / δ))) (𝓝[>] 0) ≤
      ((baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}).charTime μ := by
  set task := (baiTask ν id).restrict {μ' | ∀ c, μ' c ∈ ρ.expFamilyMeans T}
  have hνt : task.ν = ν := by rw [IdentTask.ν_restrict, ν_baiTask]
  have hcorrect : task.correct μ = {a} := by
    rw [IdentTask.correct_restrict, correct_baiTask_eq_singleton_iff]
    exact ha
  refine limsup_expectedStoppingTime_div_log_le fun c hc ↦ ?_
  have h := task.eventually_expectedStoppingTime_cTrackAndStop_le_of_charTime_lt
    (mℐ := mα) (hw := hw) (hrec := hrec) (ρ := fun _ ↦ ρ) (T := fun _ ↦ T) (hstop := hstop)
    (fun _ ↦ hT) hμ (hνt ▸ hνμ) hcorrect
    hw_mem hw_opt (eventually_eq_of_forall_mem_correct_baiTask_restrict ν continuous_apply
      (Measure.setOf_forall_mem_expFamilyMeans_mem_nhds (fun _ ↦ hT) hμ) hrec_correct ha)
    (fun _ hv ↦ continuousWithinAt_altCost_baiTask_restrict ν hT hν hμ ha hv) hc hr hβ
  simpa only [hνt] using h

end ExpFamily

/-! ### Gaussian arms -/

section Gaussian

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {σ2 : ℝ≥0} {μ v : α → ℝ} {a : α} {w : (α → ℝ) → α → ℝ}
  {hw : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ w (empMean' n h)} {rec : (α → ℝ) → α}
  {hrec : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ rec (empMean' n h)}
  {hstop : ∀ δ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
    (unionBoundLevel (Fintype.card α) δ) n <
      (baiTask (Bandits.gaussianBandit · σ2) id).glr
        ((baiTask (Bandits.gaussianBandit · σ2) id).plugInCost empMean') n h (rec (empMean' n h))}}

omit [DecidableEq α] [Nonempty α] in
/-- For Gaussian arms with a common variance `σ2 ≠ 0` and a vector of means `μ` with unique best
arm `a`, `(μ', w') ↦ D(μ', w', ¬a)` is continuous within `univ ×ˢ simplex α` at `(μ, v)` for every
allocation `v`. -/
private lemma continuousWithinAt_altCost_baiTask_gaussianBandit (hσ2 : σ2 ≠ 0)
    (ha : ∀ b ≠ a, μ b < μ a) (hv : v ∈ simplex α) :
    ContinuousWithinAt (fun q : (α → ℝ) × (α → ℝ) ↦
        (baiTask (Bandits.gaussianBandit · σ2) id).altCost q.1 q.2 a)
      (Set.univ ×ˢ simplex α) (μ, v) := by
  have h := continuousWithinAt_altCost_baiTask_restrict (Bandits.gaussianBandit · σ2)
    (not_ae_eq_const_gaussianReal 0 hσ2)
    (fun μ μ' _ _ ↦ Bandits.klDiv_gaussianBandit_eq_ofReal_expFamilyDiv hσ2 μ μ')
    (fun c ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 (μ c)) ha hv
  simpa only [restrict_baiTask_gaussianBandit hσ2] using h

omit [DecidableEq α] [Nonempty α] in
/-- For Gaussian arms with a common variance `σ2 ≠ 0`, targets that are optimal allocations at
every admissible model are continuous at every admissible model, for a recommendation of the best
arm of every admissible model. -/
private lemma continuousAt_of_forall_mem_optAlloc_baiTask_gaussianBandit (hσ2 : σ2 ≠ 0)
    (hrec_correct : ∀ θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M,
      rec θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).correct θ)
    (hw_opt : ∀ θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M,
      w θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).optAlloc θ (rec θ))
    {θ : α → ℝ} (hθ : θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M) :
    ContinuousAt w θ := by
  have hf := eventually_mem_optAlloc_baiTask (mean := id) _ continuous_apply hrec_correct hw_opt hθ
  rw [← restrict_baiTask_gaussianBandit hσ2] at hf
  exact continuousAt_of_mem_optAlloc_baiTask_restrict _ (not_ae_eq_const_gaussianReal 0 hσ2)
    (fun μ μ' _ _ ↦ Bandits.klDiv_gaussianBandit_eq_ofReal_expFamilyDiv hσ2 μ μ')
    (fun c ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 (θ c))
    (by simpa using hrec_correct _ hθ) hf

omit [DecidableEq α] [Nonempty α] in
/-- For Gaussian arms with a common variance `σ2 ≠ 0`, a recommendation of the best arm of every
admissible model and targets that are optimal allocations at every admissible model,
`(μ', w') ↦ D(μ', w', ¬rec θ)` is lower semicontinuous within `univ ×ˢ simplex α` at `(θ, w θ)`
for every admissible model `θ`. -/
private lemma lowerSemicontinuousWithinAt_altCost_baiTask_gaussianBandit (hσ2 : σ2 ≠ 0)
    (hrec_correct : ∀ θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M,
      rec θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).correct θ)
    (hw_opt : ∀ θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M,
      w θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).optAlloc θ (rec θ))
    {θ : α → ℝ} (hθ : θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M) :
    LowerSemicontinuousWithinAt (fun q : (α → ℝ) × (α → ℝ) ↦
        (baiTask (Bandits.gaussianBandit · σ2) id).altCost q.1 q.2 (rec θ))
      (Set.univ ×ˢ simplex α) (θ, w θ) :=
  (continuousWithinAt_altCost_baiTask_gaussianBandit hσ2 (by simpa using hrec_correct _ hθ)
    ((IdentTask.mem_optAlloc_iff _).1 (hw_opt θ hθ)).1).lowerSemicontinuousWithinAt

/-- **Track-and-Stop for Gaussian best arm identification is `δ`-PAC** for every `δ ∈ (0, 1]`, with
the thresholds `K log (2 n (n + 1)) + x_δ`, the empirical means as estimator, targets that are
optimal allocations at every admissible model and a recommendation of the best arm of every
admissible model. -/
theorem isDeltaPAC_trackAndStop_baiTask_gaussianBandit (hσ2 : σ2 ≠ 0)
    (hrec_correct : ∀ θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M,
      rec θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).correct θ)
    (hw_opt : ∀ θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M,
      w θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).optAlloc θ (rec θ))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (baiTask (Bandits.gaussianBandit · σ2) id).IsDeltaPAC
      ((baiTask (Bandits.gaussianBandit · σ2) id).trackAndStop empMean' w hw
        (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n)
        rec hrec (hstop δ)) δ :=
  IdentTask.isDeltaPAC_trackAndStop_unionBoundThreshold_of_mem_optAlloc (ν_baiTask _ id) hσ2
    (fun _ hθ ↦ (isSingleAnswer_baiTask _ id).correct_eq_singleton_of_mem hθ (hrec_correct _ hθ))
    hw_opt
    (fun _ ↦ continuousAt_of_forall_mem_optAlloc_baiTask_gaussianBandit hσ2 hrec_correct hw_opt)
    (fun _ ↦ eventually_eq_of_forall_mem_correct_baiTask _ continuous_apply hrec_correct)
    (fun _ ↦ lowerSemicontinuousWithinAt_altCost_baiTask_gaussianBandit hσ2 hrec_correct hw_opt)
    (fun _ hθ ↦ charTime_baiTask_gaussianBandit_ne_top hσ2 (by simpa using hrec_correct _ hθ))
    hδ hδ1

/-- **Asymptotic optimality of Track-and-Stop for Gaussian best arm identification**
[GK16, Theorem 14]. Under the assumptions of `isDeltaPAC_trackAndStop_baiTask_gaussianBandit`,
Track-and-Stop with the thresholds `K log (2 n (n + 1)) + x_δ` has, at every vector of means `μ`
with a unique best arm, `𝔼_μ[τ_δ] / log (1 / δ) → T*(μ)` as `δ → 0`. -/
theorem tendsto_expectedStoppingTime_trackAndStop_baiTask_gaussianBandit_div_log (hσ2 : σ2 ≠ 0)
    (hrec_correct : ∀ θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M,
      rec θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).correct θ)
    (hw_opt : ∀ θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M,
      w θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).optAlloc θ (rec θ))
    (hμ : μ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M) :
    Tendsto (fun δ ↦ expectedStoppingTime
        ((baiTask (Bandits.gaussianBandit · σ2) id).trackAndStop empMean' w hw
          (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n)
          rec hrec (hstop δ)) (Environment.bandit (Bandits.gaussianBandit μ σ2)) /
        ENNReal.ofReal (log (1 / δ)))
      (𝓝[>] 0) (𝓝 ((baiTask (Bandits.gaussianBandit · σ2) id).charTime μ)) := by
  simpa only [ν_baiTask] using
    IdentTask.tendsto_expectedStoppingTime_trackAndStop_unionBoundThreshold_div_log (hw := hw)
    (hrec := hrec) (hstop := hstop) (ν_baiTask _ id) hσ2
    (fun _ hθ ↦ (isSingleAnswer_baiTask _ id).correct_eq_singleton_of_mem hθ (hrec_correct _ hθ))
    hw_opt
    (fun _ ↦ continuousAt_of_forall_mem_optAlloc_baiTask_gaussianBandit hσ2 hrec_correct hw_opt)
    (fun _ ↦ eventually_eq_of_forall_mem_correct_baiTask _ continuous_apply hrec_correct)
    (fun _ ↦ lowerSemicontinuousWithinAt_altCost_baiTask_gaussianBandit hσ2 hrec_correct hw_opt)
    (fun _ hθ ↦ charTime_baiTask_gaussianBandit_ne_top hσ2 (by simpa using hrec_correct _ hθ))
    hμ

/-- **Asymptotic optimality of Track-and-Stop for two Gaussian arms** [GK16, Theorem 14;
KCG16, Section 3]. For two Gaussian arms `a` and `b` with a common variance `σ2 ≠ 0` and
`μ b < μ a`, under the assumptions of `isDeltaPAC_trackAndStop_baiTask_gaussianBandit`,
Track-and-Stop with the thresholds `K log (2 n (n + 1)) + x_δ` has
`𝔼_μ[τ_δ] / log (1 / δ) → 8 σ2 / (μ a - μ b)²` as `δ → 0`. -/
theorem tendsto_expectedStoppingTime_trackAndStop_baiTask_gaussianBandit_div_log_of_forall_eq_or_eq
    {b : α} (hσ2 : σ2 ≠ 0) (hba : b ≠ a) (hα : ∀ c, c = a ∨ c = b) (hμ : μ b < μ a)
    (hrec_correct : ∀ θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M,
      rec θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).correct θ)
    (hw_opt : ∀ θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M,
      w θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).optAlloc θ (rec θ)) :
    Tendsto (fun δ ↦ expectedStoppingTime
        ((baiTask (Bandits.gaussianBandit · σ2) id).trackAndStop empMean' w hw
          (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n)
          rec hrec (hstop δ)) (Environment.bandit (Bandits.gaussianBandit μ σ2)) /
        ENNReal.ofReal (log (1 / δ)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (8 * σ2 / (μ a - μ b) ^ 2))) := by
  have ha : ∀ c ≠ a, μ c < μ a := fun c hc ↦ (hα c).resolve_left hc ▸ hμ
  rw [← charTime_baiTask_gaussianBandit_of_forall_eq_or_eq hσ2 hba hα hμ]
  exact tendsto_expectedStoppingTime_trackAndStop_baiTask_gaussianBandit_div_log hσ2 hrec_correct
    hw_opt (by rw [M_baiTask]; exact ⟨a, ha⟩)

/-- **Track-and-Stop with C-tracking for Gaussian best arm identification is `δ`-PAC** for every
`δ ∈ (0, 1]`, with the thresholds `K log (2 n (n + 1)) + x_δ`, the empirical means as estimator,
targets that are allocations everywhere and optimal allocations at every admissible model, and a
recommendation of the best arm of every admissible model. -/
theorem isDeltaPAC_cTrackAndStop_baiTask_gaussianBandit (hσ2 : σ2 ≠ 0)
    (hrec_correct : ∀ θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M,
      rec θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).correct θ)
    (hw_mem : ∀ μ', w μ' ∈ simplex α)
    (hw_opt : ∀ θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M,
      w θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).optAlloc θ (rec θ))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (baiTask (Bandits.gaussianBandit · σ2) id).IsDeltaPAC
      ((baiTask (Bandits.gaussianBandit · σ2) id).cTrackAndStop empMean' w hw
        (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n)
        rec hrec (hstop δ)) δ :=
  IdentTask.isDeltaPAC_cTrackAndStop_unionBoundThreshold_of_mem_optAlloc (ν_baiTask _ id) hσ2
    (fun _ hθ ↦ (isSingleAnswer_baiTask _ id).correct_eq_singleton_of_mem hθ (hrec_correct _ hθ))
    hw_mem
    (fun _ ↦ eventually_mem_optAlloc_baiTask _ continuous_apply hrec_correct hw_opt)
    (fun _ ↦ eventually_eq_of_forall_mem_correct_baiTask _ continuous_apply hrec_correct)
    (fun _ hθ _ hv ↦ continuousWithinAt_altCost_baiTask_gaussianBandit hσ2
      (by simpa using hrec_correct _ hθ) hv)
    (fun _ hθ ↦ charTime_baiTask_gaussianBandit_ne_top hσ2 (by simpa using hrec_correct _ hθ))
    hδ hδ1

/-- **Asymptotic optimality of Track-and-Stop with C-tracking for Gaussian best arm
identification** [DK19, Theorem 7]. Under the assumptions of
`isDeltaPAC_cTrackAndStop_baiTask_gaussianBandit`, Track-and-Stop with C-tracking and the
thresholds `K log (2 n (n + 1)) + x_δ` has, at every vector of means `μ` with a unique best arm,
`𝔼_μ[τ_δ] / log (1 / δ) → T*(μ)` as `δ → 0`. -/
theorem tendsto_expectedStoppingTime_cTrackAndStop_baiTask_gaussianBandit_div_log (hσ2 : σ2 ≠ 0)
    (hrec_correct : ∀ θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M,
      rec θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).correct θ)
    (hw_mem : ∀ μ', w μ' ∈ simplex α)
    (hw_opt : ∀ θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M,
      w θ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).optAlloc θ (rec θ))
    (hμ : μ ∈ (baiTask (Bandits.gaussianBandit · σ2) id).M) :
    Tendsto (fun δ ↦ expectedStoppingTime
        ((baiTask (Bandits.gaussianBandit · σ2) id).cTrackAndStop empMean' w hw
          (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n)
          rec hrec (hstop δ)) (Environment.bandit (Bandits.gaussianBandit μ σ2)) /
        ENNReal.ofReal (log (1 / δ)))
      (𝓝[>] 0) (𝓝 ((baiTask (Bandits.gaussianBandit · σ2) id).charTime μ)) := by
  simpa only [ν_baiTask] using
    IdentTask.tendsto_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_div_log (hw := hw)
    (hrec := hrec) (hstop := hstop) (ν_baiTask _ id) hσ2
    (fun _ hθ ↦ (isSingleAnswer_baiTask _ id).correct_eq_singleton_of_mem hθ (hrec_correct _ hθ))
    hw_mem
    (fun _ ↦ eventually_mem_optAlloc_baiTask _ continuous_apply hrec_correct hw_opt)
    (fun _ ↦ eventually_eq_of_forall_mem_correct_baiTask _ continuous_apply hrec_correct)
    (fun _ hθ _ hv ↦ continuousWithinAt_altCost_baiTask_gaussianBandit hσ2
      (by simpa using hrec_correct _ hθ) hv)
    (fun _ hθ ↦ charTime_baiTask_gaussianBandit_ne_top hσ2 (by simpa using hrec_correct _ hθ))
    hμ

end Gaussian

end LMLExplore.Identification
