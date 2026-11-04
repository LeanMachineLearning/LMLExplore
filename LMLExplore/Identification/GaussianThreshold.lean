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

**Asymptotic optimality of Track-and-Stop** [GK16, Theorem 14]. The sample complexity bound of
`Identification/TrackAndStop.lean` applies to thresholds `log (r n / δ)` with `r n` polynomial in
`n`, and gives `𝔼[τ_δ] ≤ c log (1 / δ)` for small `δ`, for every `c > T*(μ)`. The thresholds
`K log (2 n (n + 1)) + x_δ` are not of this form, since `x_δ - log (1 / δ)` is unbounded, but for
every `s > 1` they are at most `log ((2 n (n + 1)) ^ K / δ ^ s)` for small `δ`. The bound at the
confidence level `δ ^ s` therefore gives `𝔼[τ_δ] ≤ c' s log (1 / δ)` for every `c' > T*(μ)`, and
`c' s` is any constant above `T*(μ)`. A finite expected stopping time at small `δ` gives almost
sure stopping at every `δ ∈ (0, 1]`, since the thresholds decrease with `δ`. When Track-and-Stop
tracks the optimal allocations of every admissible model, it is thus `δ`-PAC for every `δ ∈ (0, 1]`,
and together with the lower bound of `Identification/LowerBound.lean`, `𝔼[τ_δ] / log (1 / δ)`
tends to `T*(μ)` on every admissible model `μ`.

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
* `IdentTask.eventually_expectedStoppingTime_trackAndStop_unionBoundThreshold_le`: Track-and-Stop
  with the thresholds `β_{x_δ}` satisfies `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for
  every `c > T*(μ)`.
* `IdentTask.stopsAS_trackAndStop_unionBoundThreshold`: it stops almost surely for every
  `δ ∈ (0, 1]`.
* `IdentTask.isDeltaPAC_trackAndStop_unionBoundThreshold_of_mem_optAlloc`: when it tracks optimal
  allocations, it is `δ`-PAC for every `δ ∈ (0, 1]`.
* `IdentTask.tendsto_expectedStoppingTime_trackAndStop_unionBoundThreshold_div_log`:
  **asymptotic optimality**, `𝔼[τ_δ] / log (1 / δ) → T*(μ)` as `δ → 0`.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Theorem 14.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 33.7.
-/

public section

open MeasureTheory ProbabilityTheory Learning Real
open scoped ENNReal NNReal

namespace LMLExplore.Identification.IdentTask

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
        (task.glrt task.empCost alg (unionBoundThreshold (Fintype.card α) x) rec hrec hstop)
        (Environment.bandit (task.ν μ))).real
        {p | p.1 ∈ (task.glrt task.empCost alg (unionBoundThreshold (Fintype.card α) x) rec hrec
          hstop).stopSet ∧ p.2 ∉ task.correct μ} ≤
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
      (unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ)) rec hrec hstop)
      (Environment.bandit (task.ν θ))) :
    task.IsDeltaPAC (task.glrt task.empCost alg
      (unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ)) rec hrec hstop)
      δ := by
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
      (unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ)) rec hrec hstop)
      (Environment.bandit (task.ν θ))) :
    task.IsDeltaPAC (task.trackAndStop w hw
      (unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ)) rec hrec hstop)
      δ := by
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

/-- **Sample complexity of Track-and-Stop for Gaussian arms with `δ`-correct thresholds**
[GK16, Theorem 14]. Let the arms be Gaussian with a common variance `σ2 ≠ 0`, let `i` be the single
correct answer of the model `μ`, let the target map `w` be continuous at `μ` with `w(μ)` an
optimal allocation `w*(μ, ¬i)`, let the recommendation be `i` near `μ`, and let
`(μ', w') ↦ D(μ', w', ¬i)` be lower semicontinuous at `(μ, w(μ))` on the allocations of the
simplex. Then Track-and-Stop with the thresholds `K log (2 n (n + 1)) + x_δ`, with which it stops
with an incorrect answer with probability at most `δ`
(`IdentTask.isDeltaPAC_trackAndStop_unionBoundThreshold`), satisfies
`𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every `c > T*(μ)`:
`limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ T*(μ)`. -/
theorem eventually_expectedStoppingTime_trackAndStop_unionBoundThreshold_le
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0)
    (hcorrect : task.correct μ = {i}) (hw_opt : w μ ∈ task.optAlloc μ i)
    (hw_cont : ContinuousAt w μ) (hrec_eq : ∀ᶠ μ' in 𝓝 μ, rec μ' = i)
    (h_lsc : LowerSemicontinuousWithinAt (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i)
      (Set.univ ×ˢ simplex α) (μ, w μ))
    {c : ℝ≥0} (hc : task.charTime μ < c) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.trackAndStop w hw
      (unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ)) rec hrec
      (hstop δ)) (Environment.bandit (task.ν μ)) ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  set K := Fintype.card α
  -- Choose `T*(μ) < c' < c` and the exponent `s = c / c' > 1`.
  obtain ⟨c', hc', hc'c⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hc
  have hc'c_real : (c' : ℝ) < c := mod_cast ENNReal.coe_lt_coe.1 hc'c
  have hc'0 : (0 : ℝ) < c' := mod_cast ENNReal.coe_pos.1 (zero_le.trans_lt hc')
  set s : ℝ := c / c'
  have hs : 1 < s := (one_lt_div hc'0).2 hc'c_real
  have hs0 : 0 < s := one_pos.trans hs
  have hr : (fun n : ℕ ↦ (2 * n * (n + 1) : ℝ) ^ K) =O[atTop]
      fun n ↦ (n : ℝ) ^ ((2 * K : ℕ) : ℝ) := by
    have h : (fun n : ℕ ↦ (2 * n * (n + 1) : ℝ)) =O[atTop] fun n ↦ (n : ℝ) ^ 2 := by
      refine Asymptotics.IsBigO.of_bound 4 ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1 : ℝ) ≤ n := mod_cast hn
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      nlinarith
    simpa only [rpow_natCast, pow_mul] using h.pow K
  -- The arm `a` of `μ` has the law of the member of mean `μ a` of the family of `𝒩(0, σ2)`.
  have hν (a : α) :
      task.ν μ a = (gaussianReal 0 σ2).expFamily id ((gaussianReal 0 σ2).natParam id (μ a)) := by
    rw [expFamily_natParam_gaussianReal 0 hσ2, hνt, Bandits.gaussianBandit_apply]
  -- At the confidence level `δ' = δ ^ s`, the thresholds of `δ` are at most `log (r n / δ')` with
  -- `r n = (2 n (n + 1)) ^ K`, so `𝔼[τ_δ] ≤ c' log (1 / δ') = c log (1 / δ)` for small `δ`.
  have h_sc := task.eventually_expectedStoppingTime_trackAndStop_le_of_charTime_lt (hw := hw)
    (hrec := hrec) (hstop := fun δ' ↦ hstop (δ' ^ s⁻¹)) (ρ := fun _ ↦ gaussianReal 0 σ2)
    (T := fun _ ↦ id) (fun _ ↦ not_ae_eq_const_gaussianReal 0 hσ2)
    (fun _ ↦ mem_expFamilyMeans_gaussianReal 0 hσ2 _)
    (fun a ↦ hν a ▸ (IdentDistrib.refl aemeasurable_id).mgfDominatedAbove)
    (fun a ↦ hν a ▸ (IdentDistrib.refl aemeasurable_id).mgfDominatedBelow)
    hcorrect hw_opt hw_cont hrec_eq h_lsc hc' hr (eventually_unionBoundThreshold_rpow_inv_le K hs)
  filter_upwards [(tendsto_rpow_nhdsGT_zero hs0).eventually h_sc, self_mem_nhdsWithin]
    with δ hδ hδ0
  have hδ0 : 0 < δ := Set.mem_Ioi.1 hδ0
  rw [rpow_rpow_inv hδ0.le hs0.ne'] at hδ
  have hc_eq : (c : ℝ≥0∞) = c' * ENNReal.ofReal s := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal (p := c'),
      ← ENNReal.ofReal_mul c'.coe_nonneg]
    congr 1
    simp only [s]
    field_simp
  refine hδ.trans_eq ?_
  rw [hc_eq, mul_assoc, ← ENNReal.ofReal_mul hs0.le, one_div, one_div, log_inv, log_inv,
    log_rpow hδ0, neg_mul_eq_mul_neg]

/-- **Track-and-Stop for Gaussian arms stops almost surely**, with the thresholds
`K log (2 n (n + 1)) + x_δ` of every confidence level `δ ∈ (0, 1]`, on a model `μ` with
`T*(μ) < ∞` that satisfies the assumptions of
`IdentTask.eventually_expectedStoppingTime_trackAndStop_unionBoundThreshold_le`. -/
theorem stopsAS_trackAndStop_unionBoundThreshold
    (hνt : task.ν = (Bandits.gaussianBandit · σ2)) (hσ2 : σ2 ≠ 0)
    (hcorrect : task.correct μ = {i}) (hw_opt : w μ ∈ task.optAlloc μ i)
    (hw_cont : ContinuousAt w μ) (hrec_eq : ∀ᶠ μ' in 𝓝 μ, rec μ' = i)
    (h_lsc : LowerSemicontinuousWithinAt (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i)
      (Set.univ ×ˢ simplex α) (μ, w μ))
    (h_charTime : task.charTime μ ≠ ∞) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    StopsAS (task.trackAndStop w hw
      (unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ)) rec hrec
      (hstop δ)) (Environment.bandit (task.ν μ)) := by
  -- Some confidence level `δ₀ ≤ δ` has a finite expected stopping time, and the thresholds of `δ`
  -- are below those of `δ₀`.
  have hc : task.charTime μ < (task.charTime μ).toNNReal + 1 := by
    rw [ENNReal.coe_toNNReal h_charTime]
    exact ENNReal.lt_add_right h_charTime one_ne_zero
  obtain ⟨δ₀, hδ₀, hδ₀δ⟩ := ((eventually_expectedStoppingTime_trackAndStop_unionBoundThreshold_le
    (hw := hw) (hrec := hrec) (hstop := hstop) hνt hσ2 hcorrect hw_opt hw_cont hrec_eq h_lsc
    hc).and
    (Ioc_mem_nhdsGT hδ)).exists
  refine StopsAS.of_expectedStoppingTime_ne_top (ne_top_of_le_ne_top
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hδ₀)
    (expectedStoppingTime_le_of_stopSet_subset (by simp only [alg_trackAndStop]) fun h hh ↦ ?_))
  rw [mem_stopSet_trackAndStop] at hh ⊢
  rw [unionBoundThreshold_def] at hh ⊢
  refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hh
  gcongr
  exact antitoneOn_unionBoundLevel _ ⟨hδ₀δ.1, hδ₀δ.2.trans hδ1⟩ ⟨hδ, hδ1⟩ hδ₀δ.2

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
      (unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ)) rec hrec
      (hstop δ)) δ :=
  isDeltaPAC_trackAndStop_unionBoundThreshold hνt hσ2 hδ hδ1 hw hrec (hstop δ)
    (fun θ hθ ↦ hcorrect θ hθ ▸ measurableSet_singleton _) fun θ hθ ↦
    stopsAS_trackAndStop_unionBoundThreshold hνt hσ2 (hcorrect θ hθ) (hw_opt θ hθ)
      (hw_cont θ hθ) (hrec_eq θ hθ) (h_lsc θ hθ) (h_charTime θ hθ) hδ hδ1

/-- **Asymptotic optimality of Track-and-Stop for Gaussian arms** [GK16, Theorem 14]. Under the
assumptions of `IdentTask.isDeltaPAC_trackAndStop_unionBoundThreshold_of_mem_optAlloc`,
Track-and-Stop with the thresholds `K log (2 n (n + 1)) + x_δ` is `δ`-PAC for every `δ ∈ (0, 1]`,
and on every admissible model `μ` its sample complexity is asymptotically the characteristic time:
`𝔼[τ_δ] / log (1 / δ) → T*(μ)` as `δ → 0`. By the lower bound
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
        (unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ)) rec hrec
        (hstop δ)) (Environment.bandit (task.ν μ)) / ENNReal.ofReal (log (1 / δ)))
      (𝓝[>] 0) (𝓝 (task.charTime μ)) := by
  have hA : ∀ᶠ δ in 𝓝[>] 0, task.IsDeltaCorrect (task.trackAndStop w hw
      (unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ)) rec hrec
      (hstop δ)) δ := by
    filter_upwards [Ioc_mem_nhdsGT one_pos] with δ hδ
    exact (isDeltaPAC_trackAndStop_unionBoundThreshold_of_mem_optAlloc hνt hσ2 hcorrect hw_opt
      hw_cont hrec_eq h_lsc h_charTime hδ.1 hδ.2).isDeltaCorrect
  have hL : ∀ᶠ δ in 𝓝[>] 0, 0 < log (1 / δ) := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ using log_pos (one_lt_one_div hδ.1 hδ.2)
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · -- Below `T*(μ)`: the lower bound for `δ`-correct algorithms.
    obtain ⟨c, hac, hc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    filter_upwards [eventually_mul_ofReal_log_le_expectedStoppingTime hA hμ (hcorrect μ hμ) hc,
      hL] with δ hδ hLδ
    exact hac.trans_le ((ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hLδ).ne')
      (Or.inl ENNReal.ofReal_ne_top)).2 hδ)
  · -- Above `T*(μ)`: the sample complexity of Track-and-Stop.
    obtain ⟨c, hc, hca⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    filter_upwards [eventually_expectedStoppingTime_trackAndStop_unionBoundThreshold_le hνt hσ2
      (hcorrect μ hμ) (hw_opt μ hμ) (hw_cont μ hμ) (hrec_eq μ hμ) (h_lsc μ hμ) hc] with δ hδ
    exact (ENNReal.div_le_of_le_mul hδ).trans_lt hca

end LMLExplore.Identification.IdentTask
