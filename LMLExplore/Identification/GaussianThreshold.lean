/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.LowerBound
public import LMLExplore.Identification.Task.ExpFamily
public import LMLExplore.Identification.TrackAndStop
public import LMLExplore.SequentialLearning.SubGaussianDeviation

/-!
# `δ`-correct GLR thresholds for Gaussian arms and asymptotic optimality of Track-and-Stop

Let the arms of the models of an identification task be Gaussian with a common known variance
`σ2 ≠ 0`, the arm `a` of the vector of means `μ` having law `𝒩(μ a, σ2)`. After `n` rounds with
pull counts `N_a` and empirical means `μ̂_a`, the empirical cost of the GLR stopping rule of
`Identification/TrackAndStop.lean` against a model `λ` is
`∑ a, N_a KL(𝒩(μ̂_a, σ2), 𝒩(λ_a, σ2)) = ∑ a, N_a (μ̂_a - λ_a)² / (2 σ2)`. By the time-uniform
deviation inequality of `SequentialLearning/SubGaussianDeviation.lean`, along a run of any sampling
rule on the model `μ`, this statistic at `λ = μ` exceeds `K log (2 n (n + 1)) + x` at some round
`n` with probability at most `f(x) = (x / K) ^ K exp (K - x)` for `x ≥ K`, where `K` is the number
of arms. Hence the GLRT with the thresholds `β_x(n) = K log (2 n (n + 1)) + x` stops with an
incorrect answer with probability at most `f(x)`, for every task and every sampling rule
[LS, Lemma 33.7].

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

**Asymptotic optimality of Track-and-Stop** [GK16, Theorem 14]. For arms dominated by
exponential families, `Identification/TrackAndStop.lean` shows that Track-and-Stop with the
thresholds `K log (2 n (n + 1)) + x_δ` satisfies `𝔼[τ_δ] ≤ c log (1 / δ)` for small `δ`, for every
`c > T*(μ)`, and stops almost surely at every `δ ∈ (0, 1]`. Gaussian arms are the members of the
exponential family of `𝒩(0, σ2)` with the identity statistic. When Track-and-Stop tracks the
optimal allocations of every admissible model, it is thus `δ`-PAC for every `δ ∈ (0, 1]`, and
together with the lower bound of `Identification/LowerBound.lean`, `𝔼[τ_δ] / log (1 / δ)` tends to
`T*(μ)` on every admissible model `μ`. The same holds for Track-and-Stop with C-tracking, whose
targets may be any selection of the optimal allocations, even where these are not unique
[DK19, Theorem 7].

## Main statements

* `IdentTask.empCost_gaussianBandit`: the empirical cost of Gaussian arms is
  `∑ a, N_a (μ̂_a - λ_a)² / (2 σ2)`.
* `IdentTask.measure_exists_unionBoundThreshold_lt_empCost_le`: along a run of any sampling rule
  on the model `μ`, the empirical cost at `μ` exceeds the threshold `β_x(n)` at some round with
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

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, Theorem 7.
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Theorem 14.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 33.7.
-/

public section

open MeasureTheory ProbabilityTheory Learning Real
open scoped ENNReal NNReal

namespace LMLExplore.Identification.IdentTask

/-- For Gaussian arms with a common variance `σ2 ≠ 0`, the arm `a` of the model `θ` is dominated
above, in moment generating function, by the member of mean `θ a` of the exponential family of
`𝒩(0, σ2)` with the identity statistic: both have the law `𝒩(θ a, σ2)`. -/
private lemma mgfDominatedAbove_gaussianBandit {α ℐ : Type*} {mα : MeasurableSpace α} [Countable α]
    [MeasurableSingletonClass α] {task : IdentTask α (α → ℝ) ℐ ℝ} {σ2 : ℝ≥0}
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0) (θ : α → ℝ) (a : α) :
    MGFDominatedAbove id (task.ν θ a) id
      ((gaussianReal 0 σ2).expFamily id ((gaussianReal 0 σ2).natParam id (θ a))) := by
  rw [hνt, expFamily_natParam_gaussianReal 0 hσ2, Bandits.gaussianBandit_apply]
  exact (IdentDistrib.refl aemeasurable_id).mgfDominatedAbove

/-- For Gaussian arms with a common variance `σ2 ≠ 0`, the arm `a` of the model `θ` is dominated
below, in moment generating function, by the member of mean `θ a` of the exponential family of
`𝒩(0, σ2)` with the identity statistic: both have the law `𝒩(θ a, σ2)`. -/
private lemma mgfDominatedBelow_gaussianBandit {α ℐ : Type*} {mα : MeasurableSpace α} [Countable α]
    [MeasurableSingletonClass α] {task : IdentTask α (α → ℝ) ℐ ℝ} {σ2 : ℝ≥0}
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0) (θ : α → ℝ) (a : α) :
    MGFDominatedBelow id (task.ν θ a) id
      ((gaussianReal 0 σ2).expFamily id ((gaussianReal 0 σ2).natParam id (θ a))) := by
  rw [hνt, expFamily_natParam_gaussianReal 0 hσ2, Bandits.gaussianBandit_apply]
  exact (IdentDistrib.refl aemeasurable_id).mgfDominatedBelow

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {task : IdentTask α (α → ℝ) ℐ ℝ} {σ2 : ℝ≥0}

/-- For Gaussian arms with a common variance `σ2 ≠ 0`, the empirical cost of the history `h` of
the first `n` rounds against the model `λ` is `∑ a, N_a (μ̂_a - λ_a)² / (2 σ2)`, with the pull
counts `N_a` and the empirical means `μ̂_a` of `h`. -/
lemma empCost_gaussianBandit (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0)
    (n : ℕ) (h : Hist Unit α ℝ n) (θ' : α → ℝ) :
    task.empCost n h θ' =
      ENNReal.ofReal (∑ a, pullCount' n h a * (empMean' n h a - θ' a) ^ 2 / (2 * σ2)) := by
  rw [empCost_def, cost_gaussianBandit hνt hσ2 fun a ↦ by positivity]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {alg : Algorithm Unit α ℝ} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {μ : α → ℝ}
  {x δ : ℝ}

/-- **Deviation of the empirical cost of Gaussian arms**, along a run of any sampling rule. For
Gaussian arms with a common variance `σ2 ≠ 0` and a level `x ≥ K`, the probability that at some
round `n`, the empirical cost against the true model `μ` exceeds the threshold
`K log (2 n (n + 1)) + x`, is at most `(x / K) ^ K exp (K - x)`. -/
theorem measure_exists_unionBoundThreshold_lt_empCost_le
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0)
    (hseq : IsAlgEnvSeq O A R alg (Environment.bandit (task.ν μ)) P)
    (hx : Fintype.card α ≤ x) :
    P {ω | ∃ n, unionBoundThreshold (Fintype.card α) x n <
        task.empCost n (history O A R n ω) μ} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  simp only [hνt] at hseq
  refine (measure_mono ?_).trans
    (measure_exists_card_mul_log_add_le_sum_pullCount_mul_sq_div_le hseq
      (fun a ↦ Bandits.hasSubgaussianMGF_gaussianBandit μ σ2 a) hx)
  rintro ω ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [unionBoundThreshold_def, empCost_gaussianBandit hνt hσ2] at hn
  refine (ENNReal.ofReal_lt_ofReal_iff'.1 hn).1.le.trans_eq ?_
  simp only [Bandits.integral_id_gaussianBandit, pullCount_eq_pullCount' (O := O) (R' := R),
    empMean_eq_empMean' (O := O)]

variable {mℐ : MeasurableSpace ℐ} (rec : (n : ℕ) → Hist Unit α ℝ n → ℐ)
  (hrec : ∀ n, Measurable (rec n))

/-- **Error probability of the GLRT for Gaussian arms** [LS, Lemma 33.7], for every task and every
sampling rule. For Gaussian arms with a common variance `σ2 ≠ 0`, an admissible model `μ` and a
level `x ≥ K`, the GLRT with the empirical costs as statistic and the thresholds
`K log (2 n (n + 1)) + x` stops with an answer that is not correct for `μ` with probability at most
`(x / K) ^ K exp (K - x)`. -/
theorem measureReal_histOutputMeasure_glrt_unionBoundThreshold_le
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0)
    (hstop : ∀ n, MeasurableSet
      {h | unionBoundThreshold (Fintype.card α) x n < task.glr task.empCost n h (rec n h)})
    (hμ : μ ∈ task.M) (hc : MeasurableSet (task.correct μ)) (hx : Fintype.card α ≤ x) :
    (histOutputMeasure
        (task.glrt task.empCost alg (fun n _ ↦ unionBoundThreshold (Fintype.card α) x n) rec hrec
          hstop) (Environment.bandit (task.ν μ))).real
        {p | p.1 ∈ (task.glrt task.empCost alg (fun n _ ↦ unionBoundThreshold (Fintype.card α) x n)
          rec hrec hstop).stopSet ∧ p.2 ∉ task.correct μ} ≤
      (x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x) := by
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit (task.ν μ))
  refine (task.measureReal_histOutputMeasure_glrt_le task.empCost alg _ rec hrec hstop hseq hμ
    hc).trans ?_
  rw [measureReal_def]
  have hx0 : 0 ≤ x := (Nat.cast_nonneg _).trans hx
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (measure_exists_unionBoundThreshold_lt_empCost_le hνt hσ2 hseq hx)

/-- **The GLRT for Gaussian arms is `δ`-PAC** [LS, Lemma 33.7], for every task and every sampling
rule. For Gaussian arms with a common variance `σ2 ≠ 0` and `δ ∈ (0, 1]`, the GLRT with the
empirical costs as statistic and the thresholds `K log (2 n (n + 1)) + x_δ` is `δ`-PAC on the
task, provided it stops almost surely on every admissible model. -/
theorem isDeltaPAC_glrt_unionBoundThreshold
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hstop : ∀ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
      (unionBoundLevel (Fintype.card α) δ) n < task.glr task.empCost n h (rec n h)})
    (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (h_stops : ∀ θ ∈ task.M, StopsAS (task.glrt task.empCost alg
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec hstop) (Environment.bandit (task.ν θ))) :
    task.IsDeltaPAC (task.glrt task.empCost alg
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec hstop) δ := by
  refine task.isDeltaPAC_glrt task.empCost alg _ rec hrec hstop hc (fun θ hθ ↦ ?_) h_stops
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal hδ.le ((measure_exists_unionBoundThreshold_lt_empCost_le
    hνt hσ2 (IT.isAlgEnvSeq_trajMeasure alg _) (card_le_unionBoundLevel hδ hδ1)).trans ?_)
  exact ENNReal.ofReal_le_ofReal
    (div_pow_mul_exp_sub_unionBoundLevel_le hδ hδ1)

/-- **Track-and-Stop for Gaussian arms is `δ`-PAC** [LS, Lemma 33.7], whatever its target map and
its recommendation rule. For Gaussian arms with a common variance `σ2 ≠ 0` and `δ ∈ (0, 1]`,
Track-and-Stop with the thresholds `K log (2 n (n + 1)) + x_δ` is `δ`-PAC on the task, provided it
stops almost surely on every admissible model. -/
theorem isDeltaPAC_trackAndStop_unionBoundThreshold [Nonempty α]
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {w : (α → ℝ) → α → ℝ} (hw : Measurable w) {rec : (α → ℝ) → ℐ} (hrec : Measurable rec)
    (hstop : ∀ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
      (unionBoundLevel (Fintype.card α) δ) n <
        task.glr task.empCost n h (rec (empMean' n h))})
    (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (h_stops : ∀ θ ∈ task.M, StopsAS (task.trackAndStop w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec hstop) (Environment.bandit (task.ν θ))) :
    task.IsDeltaPAC (task.trackAndStop w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec hstop) δ := by
  simp only [trackAndStop_def] at h_stops ⊢
  exact isDeltaPAC_glrt_unionBoundThreshold _ _ hνt hσ2 hδ hδ1 hstop hc h_stops

end LMLExplore.Identification.IdentTask

/-! ### Asymptotic optimality of Track-and-Stop -/

namespace LMLExplore.Identification.IdentTask

open Filter Topology

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {mℐ : MeasurableSpace ℐ} {task : IdentTask α (α → ℝ) ℐ ℝ}
  {σ2 : ℝ≥0} {w : (α → ℝ) → α → ℝ} {hw : Measurable w} {rec : (α → ℝ) → ℐ}
  {hrec : Measurable rec}
  {hstop : ∀ δ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
    (unionBoundLevel (Fintype.card α) δ) n < task.glr task.empCost n h (rec (empMean' n h))}}
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
    task.IsDeltaPAC (task.trackAndStop w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec (hstop δ)) δ :=
  isDeltaPAC_trackAndStop_unionBoundThreshold hνt hσ2 hδ hδ1 hw hrec (hstop δ)
    (fun θ hθ ↦ hcorrect θ hθ ▸ measurableSet_singleton _) fun θ hθ ↦
    stopsAS_trackAndStop_unionBoundThreshold (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
      (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (mgfDominatedAbove_gaussianBandit hνt hσ2 θ) (mgfDominatedBelow_gaussianBandit hνt hσ2 θ)
      (hcorrect θ hθ) (hw_opt θ hθ) (hw_cont θ hθ) (hrec_eq θ hθ) (h_lsc θ hθ) (h_charTime θ hθ)
      hδ hδ1

/-- **Asymptotic optimality of Track-and-Stop for Gaussian arms** [GK16, Theorem 14]. Under the
assumptions of `IdentTask.isDeltaPAC_trackAndStop_unionBoundThreshold_of_mem_optAlloc`,
Track-and-Stop with the thresholds `K log (2 n (n + 1)) + x_δ`, which is `δ`-PAC for every
`δ ∈ (0, 1]` by that theorem, has on every admissible model `μ` a sample complexity asymptotically
equal to the characteristic time: `𝔼[τ_δ] / log (1 / δ) → T*(μ)` as `δ → 0`. By the lower bound
`IdentTask.eventually_mul_ofReal_log_le_expectedStoppingTime`, no family of `δ`-correct algorithms
does better. -/
theorem tendsto_expectedStoppingTime_trackAndStop_unionBoundThreshold_div_log
    [MeasurableSingletonClass ℐ] (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0)
    (hcorrect : ∀ θ ∈ task.M, task.correct θ = {rec θ})
    (hw_opt : ∀ θ ∈ task.M, w θ ∈ task.optAlloc θ (rec θ))
    (hw_cont : ∀ θ ∈ task.M, ContinuousAt w θ)
    (hrec_eq : ∀ θ ∈ task.M, ∀ᶠ θ' in 𝓝 θ, rec θ' = rec θ)
    (h_lsc : ∀ θ ∈ task.M, LowerSemicontinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 (rec θ)) (Set.univ ×ˢ simplex α) (θ, w θ))
    (h_charTime : ∀ θ ∈ task.M, task.charTime θ ≠ ∞) (hμ : μ ∈ task.M) :
    Tendsto (fun δ ↦ expectedStoppingTime (task.trackAndStop w hw
        (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
        hrec (hstop δ)) (Environment.bandit (task.ν μ)) / ENNReal.ofReal (log (1 / δ)))
      (𝓝[>] 0) (𝓝 (task.charTime μ)) := by
  refine tendsto_expectedStoppingTime_div_log ?_ hμ (hcorrect μ hμ) fun c hc ↦ ?_
  · filter_upwards [Ioc_mem_nhdsGT one_pos] with δ hδ
    exact (isDeltaPAC_trackAndStop_unionBoundThreshold_of_mem_optAlloc hνt hσ2 hcorrect hw_opt
      hw_cont hrec_eq h_lsc h_charTime hδ.1 hδ.2).isDeltaCorrect
  · exact eventually_expectedStoppingTime_trackAndStop_unionBoundThreshold_le
      (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2) (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (mgfDominatedAbove_gaussianBandit hνt hσ2 μ) (mgfDominatedBelow_gaussianBandit hνt hσ2 μ)
      (hcorrect μ hμ) (hw_opt μ hμ) (hw_cont μ hμ) (hrec_eq μ hμ) (h_lsc μ hμ) hc

end LMLExplore.Identification.IdentTask

/-! ### Asymptotic optimality of Track-and-Stop with C-tracking -/

namespace LMLExplore.Identification.IdentTask

open Filter Topology

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {mℐ : MeasurableSpace ℐ} {task : IdentTask α (α → ℝ) ℐ ℝ}
  {σ2 : ℝ≥0} {w : (α → ℝ) → α → ℝ} {hw : Measurable w} {rec : (α → ℝ) → ℐ}
  {hrec : Measurable rec}
  {hstop : ∀ δ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
    (unionBoundLevel (Fintype.card α) δ) n < task.glr task.empCost n h (rec (empMean' n h))}}
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
    task.IsDeltaPAC (task.cTrackAndStop w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec (hstop δ)) δ := by
  have h_stops (θ : α → ℝ) (hθ : θ ∈ task.M) := stopsAS_cTrackAndStop_unionBoundThreshold
    (hw := hw) (hrec := hrec) (hstop := hstop) (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
    (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _) (mgfDominatedAbove_gaussianBandit hνt hσ2 θ)
    (mgfDominatedBelow_gaussianBandit hνt hσ2 θ) (hcorrect θ hθ) hw_mem (hw_opt θ hθ)
    (hrec_eq θ hθ) (h_cont θ hθ) (h_charTime θ hθ) hδ hδ1
  simp only [cTrackAndStop_def] at h_stops ⊢
  exact isDeltaPAC_glrt_unionBoundThreshold _ _ hνt hσ2 hδ hδ1 (hstop δ)
    (fun θ hθ ↦ hcorrect θ hθ ▸ measurableSet_singleton _) h_stops

/-- **Asymptotic optimality of Track-and-Stop with C-tracking for Gaussian arms**
[DK19, Theorem 7]. Under the assumptions of
`IdentTask.isDeltaPAC_cTrackAndStop_unionBoundThreshold_of_mem_optAlloc`, Track-and-Stop with
C-tracking and the thresholds `K log (2 n (n + 1)) + x_δ`, which is `δ`-PAC for every
`δ ∈ (0, 1]` by that theorem, has on every admissible model `μ` a sample complexity asymptotically
equal to the characteristic time: `𝔼[τ_δ] / log (1 / δ) → T*(μ)` as `δ → 0`, even where the
optimal allocations are not unique. By
the lower bound `IdentTask.eventually_mul_ofReal_log_le_expectedStoppingTime`, no family of
`δ`-correct algorithms does better. -/
theorem tendsto_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_div_log
    [MeasurableSingletonClass ℐ] (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0)
    (hcorrect : ∀ θ ∈ task.M, task.correct θ = {rec θ}) (hw_mem : ∀ μ', w μ' ∈ simplex α)
    (hw_opt : ∀ θ ∈ task.M, ∀ᶠ θ' in 𝓝 θ, w θ' ∈ task.optAlloc θ' (rec θ))
    (hrec_eq : ∀ θ ∈ task.M, ∀ᶠ θ' in 𝓝 θ, rec θ' = rec θ)
    (h_cont : ∀ θ ∈ task.M, ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 (rec θ)) (Set.univ ×ˢ simplex α) (θ, v))
    (h_charTime : ∀ θ ∈ task.M, task.charTime θ ≠ ∞) (hμ : μ ∈ task.M) :
    Tendsto (fun δ ↦ expectedStoppingTime (task.cTrackAndStop w hw
        (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
        hrec (hstop δ)) (Environment.bandit (task.ν μ)) / ENNReal.ofReal (log (1 / δ)))
      (𝓝[>] 0) (𝓝 (task.charTime μ)) := by
  refine tendsto_expectedStoppingTime_div_log ?_ hμ (hcorrect μ hμ) fun c hc ↦ ?_
  · filter_upwards [Ioc_mem_nhdsGT one_pos] with δ hδ
    exact (isDeltaPAC_cTrackAndStop_unionBoundThreshold_of_mem_optAlloc hνt hσ2 hcorrect hw_mem
      hw_opt hrec_eq h_cont h_charTime hδ.1 hδ.2).isDeltaCorrect
  · exact eventually_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_le
      (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2) (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
      (mgfDominatedAbove_gaussianBandit hνt hσ2 μ) (mgfDominatedBelow_gaussianBandit hνt hσ2 μ)
      (hcorrect μ hμ) hw_mem (hw_opt μ hμ) (hrec_eq μ hμ) (h_cont μ hμ) hc

end LMLExplore.Identification.IdentTask
