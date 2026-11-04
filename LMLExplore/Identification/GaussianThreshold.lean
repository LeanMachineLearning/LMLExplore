/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.ExpFamily
public import LMLExplore.Identification.TrackAndStop
public import LMLExplore.SequentialLearning.SubGaussianDeviation

/-!
# `δ`-correct GLR stopping thresholds for Gaussian arms

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

## Main definitions

* `LMLExplore.Identification.unionBoundThreshold K x n`: the threshold
  `K log (2 n (n + 1)) + x` after `n` rounds, for `K` arms and the level `x`.
* `LMLExplore.Identification.unionBoundLevel K δ`: the level
  `x_δ = log (1 / δ) + 2 K (1 + log (1 + log (1 / δ)))` of confidence `δ`.

## Main statements

* `LMLExplore.Identification.div_pow_mul_exp_sub_unionBoundLevel_le`: `f(x_δ) ≤ δ`.
* `LMLExplore.Identification.isLittleO_unionBoundLevel_sub_log`:
  `x_δ - log (1 / δ) = o(log (1 / δ))` as `δ → 0`.
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

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 33.7.
-/

public section

open MeasureTheory ProbabilityTheory Learning Filter Real Asymptotics
open scoped Topology ENNReal NNReal

namespace LMLExplore.Identification

/-! ### Thresholds and levels -/

/-- The GLR stopping threshold `K log (2 n (n + 1)) + x` after `n` rounds, for `K` arms and the
level `x` [LS, Lemma 33.7]. For Gaussian arms, the GLRT with these thresholds stops with an
incorrect answer with probability at most `(x / K) ^ K exp (K - x)`
(`IdentTask.measureReal_histOutputMeasure_glrt_unionBoundThreshold_le`). -/
noncomputable def unionBoundThreshold (K : ℕ) (x : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (K * log (2 * n * (n + 1)) + x)

lemma unionBoundThreshold_def (K : ℕ) (x : ℝ) (n : ℕ) :
    unionBoundThreshold K x n = ENNReal.ofReal (K * log (2 * n * (n + 1)) + x) := (rfl)

/-- The level `x_δ = log (1 / δ) + 2 K (1 + log (1 + log (1 / δ)))` of confidence `δ` for `K`
arms: an explicit upper bound on the inverse at `δ` of the decreasing map
`x ↦ (x / K) ^ K exp (K - x)` on `[K, ∞)` (`div_pow_mul_exp_sub_unionBoundLevel_le`), with
`x_δ = (1 + o(1)) log (1 / δ)` as `δ → 0` (`isLittleO_unionBoundLevel_sub_log`). -/
noncomputable def unionBoundLevel (K : ℕ) (δ : ℝ) : ℝ :=
  log (1 / δ) + 2 * K * (1 + log (1 + log (1 / δ)))

lemma unionBoundLevel_def (K : ℕ) (δ : ℝ) :
    unionBoundLevel K δ = log (1 / δ) + 2 * K * (1 + log (1 + log (1 / δ))) := (rfl)

variable {K : ℕ} {δ : ℝ}

/-- For `δ ∈ (0, 1]`, the level `x_δ` is at least `K`, as the deviation inequality of
`SequentialLearning/SubGaussianDeviation.lean` requires. -/
lemma card_le_unionBoundLevel (hδ : 0 < δ) (hδ1 : δ ≤ 1) : (K : ℝ) ≤ unionBoundLevel K δ := by
  have hL : 0 ≤ log (1 / δ) := log_nonneg (one_le_one_div hδ hδ1)
  have hlog : 0 ≤ log (1 + log (1 / δ)) := log_nonneg (by linarith)
  have hK : (0 : ℝ) ≤ K := K.cast_nonneg
  rw [unionBoundLevel_def]
  nlinarith

/-- **The level `x_δ` has confidence `δ`**: for `K ≠ 0` arms and `δ ∈ (0, 1]`,
`(x_δ / K) ^ K exp (K - x_δ) ≤ δ`. -/
theorem div_pow_mul_exp_sub_unionBoundLevel_le (hK : K ≠ 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (unionBoundLevel K δ / K) ^ K * exp (K - unionBoundLevel K δ) ≤ δ := by
  set L := log (1 / δ) with hL_def
  have hL : 0 ≤ L := log_nonneg (one_le_one_div hδ hδ1)
  have hK1 : (1 : ℝ) ≤ K := Nat.one_le_cast.2 (Nat.pos_of_ne_zero hK)
  have hK0 : (0 : ℝ) < K := zero_lt_one.trans_le hK1
  have hL1 : 0 < 1 + L := by linarith
  have hx0 : 0 ≤ unionBoundLevel K δ / K :=
    div_nonneg (hK0.le.trans (card_le_unionBoundLevel hδ hδ1)) hK0.le
  -- `x_δ / K ≤ e (1 + L)²`, with `L = log (1 / δ)`.
  have h_le : unionBoundLevel K δ / K ≤ exp (1 + 2 * log (1 + L)) := by
    have hlog : log (1 + L) ≤ L := by linarith [log_le_sub_one_of_pos hL1]
    have he : 2 ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
    have hLK : L / K ≤ L := div_le_self hL hK1
    rw [exp_add, show 2 * log (1 + L) = (2 : ℕ) * log (1 + L) by norm_num, exp_nat_mul,
      exp_log hL1, unionBoundLevel_def, ← hL_def, add_div,
      show (2 : ℝ) * K * (1 + log (1 + L)) / K = 2 * (1 + log (1 + L)) by field_simp]
    nlinarith
  calc (unionBoundLevel K δ / K) ^ K * exp (K - unionBoundLevel K δ)
  _ ≤ exp (1 + 2 * log (1 + L)) ^ K * exp (K - unionBoundLevel K δ) := by
    gcongr
  _ = exp (-L) := by
    rw [← exp_nat_mul, ← exp_add, unionBoundLevel_def, ← hL_def]
    ring_nf
  _ = δ := by rw [hL_def, one_div, log_inv, neg_neg, exp_log hδ]

/-- **The level `x_δ` is `(1 + o(1)) log (1 / δ)`** as `δ → 0`: `x_δ - log (1 / δ)` is
negligible compared to `log (1 / δ)`. -/
theorem isLittleO_unionBoundLevel_sub_log (K : ℕ) :
    (fun δ ↦ unionBoundLevel K δ - log (1 / δ)) =o[𝓝[>] 0] fun δ ↦ log (1 / δ) := by
  have hL : Tendsto (fun δ : ℝ ↦ log (1 / δ)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Function.comp_def] using tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  -- `2 K (1 + log (1 + L)) = o(L)` as `L → ∞`.
  have h_add : (fun L : ℝ ↦ 1 + L) =O[atTop] id :=
    (isLittleO_const_id_atTop (1 : ℝ)).isBigO.add (isBigO_refl _ _)
  have h_log : (fun L : ℝ ↦ log (1 + L)) =o[atTop] id :=
    (isLittleO_log_id_atTop.comp_tendsto (tendsto_atTop_add_const_left _ 1 tendsto_id)).trans_isBigO
      h_add
  have h : (fun L : ℝ ↦ 2 * K * (1 + log (1 + L))) =o[atTop] id :=
    ((isLittleO_const_id_atTop (1 : ℝ)).add h_log).const_mul_left _
  refine (h.comp_tendsto hL).congr_left fun δ ↦ ?_
  simp only [Function.comp_apply, unionBoundLevel_def]
  ring

end LMLExplore.Identification

/-! ### Gaussian arms -/

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
theorem isDeltaPAC_glrt_unionBoundThreshold [Nonempty α]
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
    (div_pow_mul_exp_sub_unionBoundLevel_le Fintype.card_ne_zero hδ hδ1)

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
