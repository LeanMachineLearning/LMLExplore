/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.TrackAndStop

/-!
# Almost sure sample complexity of the GLRT

The almost sure counterpart [GK16, Proposition 13] of the sample complexity bound in expectation
`IdentTask.eventually_expectedStoppingTime_glrt_le`. Consider the GLRTs with thresholds
`β δ T h ≤ log (1 / δ) + f T`, where `f T ≤ ε T` eventually for every `ε > 0`.

* **Pathwise.** Along one sequence of histories, if the GLR statistic of the recommended answer
  after `T` rounds is at least `κ T` for all large `T`, with `κ > 0`, then the GLRT stops for every
  `δ` at which the thresholds have this form, and its stopping time is at most `c log (1 / δ)` for
  all small `δ`, for every `c > 1 / κ`.
* **Linear growth of the plug-in statistic.** For the plug-in statistic of an estimator `θ̂`, the
  GLR statistic after `T` rounds is `T D(θ̂_T, N(T) / T, ¬i)`. If `θ̂_T → θ`, the proportions of
  pulls `N(T) / T` approach a compact set `W` of allocations, `(θ', w) ↦ D(θ', w, ¬i)` is lower
  semicontinuous at `(θ, w)` for every `w ∈ W`, and the recommendation is `i` near `θ`, then it is
  at least `κ T` for all large `T`, for every `κ < inf_{w ∈ W} D(θ, w, ¬i)`.
* **Almost surely.** If almost surely `θ̂_T → θ` and `N(T) / T` approaches `W`, then almost surely,
  for every `c > (inf_{w ∈ W} D(θ, w, ¬i))⁻¹`, the stopping time at the confidence level `δ` is at
  most `c log (1 / δ)` for all small `δ`, and the GLRT stops at every such `δ` if the infimum is
  positive. The thresholds `log (r T / δ)` with `r T = O(T ^ p)` of [GK16, Theorem 14] are a case.

The sampling rule is arbitrary: it enters only through the almost sure convergence of the
estimates and of the proportions of pulls. For the empirical means, the first follows from the
strong law of large numbers (`ae_tendsto_empMean_of_tendsto_pullCount`) as soon as every arm is
pulled infinitely often.

## Main statements

* `IdentTask.stoppingTime_glrt_ne_top_of_eventually_mul_le_glr`,
  `IdentTask.eventually_stoppingTime_glrt_le_of_eventually_mul_le_glr`: the pathwise statements.
* `IdentTask.eventually_mul_le_glr_plugInCost`: the linear growth of the plug-in statistic.
* `IdentTask.ae_eventually_stoppingTime_glrt_le`, `IdentTask.ae_stoppingTime_glrt_ne_top`:
  [GK16, Proposition 13] for any task, any estimator and any thresholds of the form above.
* `IdentTask.ae_eventually_stoppingTime_glrt_le_of_isBigO`: the same bound for thresholds at most
  `log (r T / δ)`, with `r T = O(T ^ p)`.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Proposition 13.
-/

public section

open MeasureTheory ProbabilityTheory Learning Filter Real Metric

open scoped Topology ENNReal NNReal

namespace LMLExplore.Identification.IdentTask

/-! ### Pathwise: from the linear growth of the GLR statistic to the stopping time -/

variable {α Θ ℐ 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  {mℐ : MeasurableSpace ℐ} (task : IdentTask α Θ ℐ 𝓨) (Z : (n : ℕ) → Hist Unit α 𝓨 n → Θ → ℝ≥0∞)
  (alg : Algorithm Unit α 𝓨) (rec : (n : ℕ) → Hist Unit α 𝓨 n → ℐ)
  (hrec : ∀ n, Measurable (rec n))
  {Ω : Type*} {O : ℕ → Ω → Unit} {X : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨} {ω : Ω} {κ c : ℝ≥0} {T₀ : ℕ}
  {f : ℕ → ℝ}

/-- **The GLRT stops** along a sequence of histories on which its statistic grows linearly. If the
GLR statistic of the recommended answer after `T` rounds is at least `κ T` for all large `T`, with
`κ > 0`, and the thresholds are `β T h ≤ L + f T` for all large `T`, where `f T ≤ ε T` eventually
for every `ε > 0`, then the stopping time of the GLRT is finite. -/
lemma stoppingTime_glrt_ne_top_of_eventually_mul_le_glr
    {β : (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞}
    (hstop : ∀ n, MeasurableSet {h | β n h < task.glr Z n h (rec n h)}) (hκ : 0 < κ)
    (hE : ∀ᶠ T in atTop,
      κ * T ≤ task.glr Z T (history O X Y T ω) (rec T (history O X Y T ω)))
    (hf : ∀ ε > 0, ∀ᶠ T in atTop, f T ≤ ε * T) {L : ℝ}
    (hβ : ∀ᶠ T in atTop, ∀ h, β T h ≤ ENNReal.ofReal (L + f T)) :
    (task.glrt Z alg β rec hrec hstop).stoppingTime O X Y ω ≠ ⊤ := by
  have hκ' : (0 : ℝ) < κ := hκ
  -- At a large round `T`, `f T ≤ κ T / 2` and `L < κ T / 2`, so the threshold is below `κ T`.
  obtain ⟨T, hET, hfT, hβT, hLT, hT0⟩ := (hE.and ((hf (κ / 2) (by positivity)).and (hβ.and
    (((tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (2 * L / κ)).and
    (eventually_gt_atTop 0))))).exists
  have hLT' : L < κ / 2 * T := by
    rw [div_lt_iff₀ hκ'] at hLT
    linarith
  refine ne_top_of_le_ne_top (WithTop.coe_ne_top (a := T)) (task.stoppingTime_glrt_le Z alg β rec
    hrec hstop ?_)
  calc β T (history O X Y T ω)
  _ ≤ ENNReal.ofReal (L + f T) := hβT _
  _ < ENNReal.ofReal (κ * T) := by
    refine (ENNReal.ofReal_lt_ofReal_iff (mul_pos hκ' (Nat.cast_pos.2 hT0))).2 ?_
    linarith
  _ = κ * T := by
    rw [ENNReal.ofReal_mul κ.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]
  _ ≤ _ := hET

/-- **The stopping time of the GLRT at small `δ`** along a sequence of histories on which its
statistic grows linearly (the deterministic step of [GK16, Proposition 13]). Consider the GLRTs with
thresholds `β δ T h ≤ log (1 / δ) + f T` for `T ≥ T₀`, where `f T ≤ ε T` eventually for every
`ε > 0`. If the GLR statistic of the recommended answer after `T` rounds is at least `κ T` for all
large `T`, then the stopping time at the confidence level `δ` is at most `c log (1 / δ)` for all
small enough `δ`, for every `c > 1 / κ`. -/
lemma eventually_stoppingTime_glrt_le_of_eventually_mul_le_glr
    {β : ℝ → (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞}
    (hstop : ∀ δ n, MeasurableSet {h | β δ n h < task.glr Z n h (rec n h)})
    (hE : ∀ᶠ T in atTop,
      κ * T ≤ task.glr Z T (history O X Y T ω) (rec T (history O X Y T ω)))
    (hκc : 1 < κ * c) (hf : ∀ ε > 0, ∀ᶠ T in atTop, f T ≤ ε * T)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ T ≥ T₀, ∀ h, β δ T h ≤ ENNReal.ofReal (log (1 / δ) + f T)) :
    ∀ᶠ δ in 𝓝[>] 0, ENat.toENNReal
        ((task.glrt Z alg (β δ) rec hrec (hstop δ)).stoppingTime O X Y ω) ≤
      c * ENNReal.ofReal (log (1 / δ)) := by
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 hE
  filter_upwards [hβ, eventually_exists_add_le_mul_and_forall_ofReal_add_lt_mul hκc hf
    (max T₀ T₁) ENNReal.zero_ne_top] with δ hβδ ⟨N, hN, hNc, hNlt⟩
  -- The stopping condition holds after `N ≤ c log (1 / δ)` rounds.
  have h_stop : (task.glrt Z alg (β δ) rec hrec (hstop δ)).stoppingTime O X Y ω ≤ N :=
    task.stoppingTime_glrt_le Z alg (β δ) rec hrec (hstop δ)
      (((hβδ N (le_of_max_le_left hN) _).trans_lt (hNlt N le_rfl)).trans_le
        (hT₁ N (le_of_max_le_right hN)))
  calc ENat.toENNReal ((task.glrt Z alg (β δ) rec hrec (hstop δ)).stoppingTime O X Y ω)
  _ ≤ ENat.toENNReal N := ENat.toENNReal_le.2 h_stop
  _ = N + 0 := by rw [ENat.toENNReal_coe, add_zero]
  _ ≤ c * ENNReal.ofReal (log (1 / δ)) := hNc

/-! ### The linear growth of the plug-in statistic -/

variable [Fintype α] [DecidableEq α] [TopologicalSpace Θ] (est : (n : ℕ) → Hist Unit α 𝓨 n → Θ)
  {θ : Θ} {i : ℐ} {W : Set (α → ℝ)}

/-- **Linear growth of the plug-in statistic** [GK16, proof of Proposition 13]. Along a sequence of
histories on which the estimates `θ̂_T` converge to `θ` and the proportions of pulls `N(T) / T`
approach a compact set `W` of allocations, let `(θ', w) ↦ D(θ', w, ¬i)` be lower semicontinuous at
`(θ, w)` on the allocations of the simplex for every `w ∈ W`, and let the recommendation be `i`
near `θ`. Then the GLR statistic of the recommendation after `T` rounds is at least `κ T` for all
large `T`, for every `κ < inf_{w ∈ W} D(θ, w, ¬i)`. -/
lemma eventually_mul_le_glr_plugInCost {rec : Θ → ℐ} (hW : IsCompact W)
    (h_lsc : ∀ w ∈ W, LowerSemicontinuousWithinAt
      (fun q : Θ × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (θ, w))
    (hκ : ∀ w ∈ W, (κ : ℝ≥0∞) < task.altCost θ w i) (hrec_eq : ∀ᶠ θ' in 𝓝 θ, rec θ' = i)
    (h_est : Tendsto (fun n ↦ est n (history O X Y n ω)) atTop (𝓝 θ))
    (h_prop : Tendsto (fun n a ↦ (pullCount X a n ω : ℝ) / n) atTop (𝓝ˢ W)) :
    ∀ᶠ T in atTop, κ * T ≤ task.glr (task.plugInCost est) T (history O X Y T ω)
      (rec (est T (history O X Y T ω))) := by
  -- Near `θ`, on the allocations of a thickening of `W`, the cost of the alternatives exceeds `κ`.
  obtain ⟨U, hU, η, hη, hUη⟩ := hW.exists_forall_mem_thickening_lt_of_lowerSemicontinuousWithinAt
    h_lsc hκ
  filter_upwards [h_est.eventually_mem (inter_mem hU hrec_eq),
    h_prop.eventually_mem (thickening_mem_nhdsSet W hη), eventually_ne_atTop 0] with T hT hTW hT0
  have h_eq : (fun a ↦ (pullCount' T (history O X Y T ω) a : ℝ) / T) =
      fun a ↦ (pullCount X a T ω : ℝ) / T := by
    simp_rw [pullCount_eq_pullCount' (O := O) (R' := Y)]
  rw [← h_eq] at hTW
  rw [hT.2, glr_plugInCost_eq_mul task est hT0, mul_comm]
  exact mul_le_mul_right (hUη _ hT.1 _ (pullCount'_div_mem_simplex _ hT0) hTW).le _

/-! ### Almost sure sample complexity -/

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} {rec : Θ → ℐ}
  {hrec : ∀ n, Measurable fun h : Hist Unit α 𝓨 n ↦ rec (est n h)}
  {β : ℝ → (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞}
  {hstop : ∀ δ n, MeasurableSet
    {h | β δ n h < task.glr (task.plugInCost est) n h (rec (est n h))}}

/-- **Almost sure sample complexity of the GLRT** [GK16, Proposition 13], for every task, every
estimator and every sampling rule. Let `W` be a compact set of allocations such that
`(θ', w) ↦ D(θ', w, ¬i)` is lower semicontinuous at `(θ, w)` on the allocations of the simplex for
every `w ∈ W`, and let the GLRT use the plug-in statistic of the estimator `θ̂` and recommend `i`
near `θ`, with thresholds `β δ T h ≤ log (1 / δ) + f T` for `T ≥ T₀` and small `δ`, where
`f T ≤ ε T` eventually for every `ε > 0`. If almost surely `θ̂_T → θ` and the proportions of pulls
`N(T) / T` approach `W`, then almost surely, for every `c > (inf_{w ∈ W} D(θ, w, ¬i))⁻¹`, the
stopping time at the confidence level `δ` is at most `c log (1 / δ)` for all small enough `δ`:
`limsup_{δ → 0} τ_δ / log (1 / δ) ≤ (inf_{w ∈ W} D(θ, w, ¬i))⁻¹`. -/
theorem ae_eventually_stoppingTime_glrt_le (hW : IsCompact W)
    (h_lsc : ∀ w ∈ W, LowerSemicontinuousWithinAt
      (fun q : Θ × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (θ, w))
    (hrec_eq : ∀ᶠ θ' in 𝓝 θ, rec θ' = i)
    (h_est : ∀ᵐ ω ∂P, Tendsto (fun n ↦ est n (history O X Y n ω)) atTop (𝓝 θ))
    (h_prop : ∀ᵐ ω ∂P, Tendsto (fun n a ↦ (pullCount X a n ω : ℝ) / n) atTop (𝓝ˢ W))
    (hf : ∀ ε > 0, ∀ᶠ T in atTop, f T ≤ ε * T)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ T ≥ T₀, ∀ h, β δ T h ≤ ENNReal.ofReal (log (1 / δ) + f T)) :
    ∀ᵐ ω ∂P, ∀ c : ℝ≥0, (⨅ w ∈ W, task.altCost θ w i)⁻¹ < c →
      ∀ᶠ δ in 𝓝[>] 0, ENat.toENNReal ((task.glrt (task.plugInCost est) alg (β δ)
          (fun n h ↦ rec (est n h)) hrec (hstop δ)).stoppingTime O X Y ω) ≤
        c * ENNReal.ofReal (log (1 / δ)) := by
  filter_upwards [h_est, h_prop] with ω h_est h_prop c hc
  -- A rate `κ` with `c⁻¹ < κ < D(θ, w, ¬i)` for all `w ∈ W`, at which the GLR statistic grows.
  obtain ⟨κ, hκ', hκc⟩ := ENNReal.exists_nnreal_lt_one_lt_mul_of_inv_lt hc
  exact task.eventually_stoppingTime_glrt_le_of_eventually_mul_le_glr (task.plugInCost est) alg
    _ hrec hstop (task.eventually_mul_le_glr_plugInCost est hW h_lsc
      (fun w hw ↦ hκ'.trans_le (iInf₂_le w hw)) hrec_eq h_est h_prop) hκc hf hβ

/-- **Almost sure sample complexity of the GLRT with thresholds `log (r T / δ)`**
[GK16, Proposition 13], for the thresholds of [GK16, Theorem 14], `r T = O(T ^ p)`. Under the
assumptions of `IdentTask.ae_eventually_stoppingTime_glrt_le` on the task, the estimator and the
proportions of pulls, with thresholds `β δ T h ≤ log (r T / δ)` for `T ≥ T₀` and small `δ`,
almost surely, for every `c > (inf_{w ∈ W} D(θ, w, ¬i))⁻¹`, the stopping time at the confidence
level `δ` is at most `c log (1 / δ)` for all small enough `δ`. -/
theorem ae_eventually_stoppingTime_glrt_le_of_isBigO (hW : IsCompact W)
    (h_lsc : ∀ w ∈ W, LowerSemicontinuousWithinAt
      (fun q : Θ × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (θ, w))
    (hrec_eq : ∀ᶠ θ' in 𝓝 θ, rec θ' = i)
    (h_est : ∀ᵐ ω ∂P, Tendsto (fun n ↦ est n (history O X Y n ω)) atTop (𝓝 θ))
    (h_prop : ∀ᵐ ω ∂P, Tendsto (fun n a ↦ (pullCount X a n ω : ℝ) / n) atTop (𝓝ˢ W))
    {r : ℕ → ℝ} {p : ℝ} (hr : r =O[atTop] fun T ↦ (T : ℝ) ^ p)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ T ≥ T₀, ∀ h, β δ T h ≤ ENNReal.ofReal (log (r T / δ))) :
    ∀ᵐ ω ∂P, ∀ c : ℝ≥0, (⨅ w ∈ W, task.altCost θ w i)⁻¹ < c →
      ∀ᶠ δ in 𝓝[>] 0, ENat.toENNReal ((task.glrt (task.plugInCost est) alg (β δ)
          (fun n h ↦ rec (est n h)) hrec (hstop δ)).stoppingTime O X Y ω) ≤
        c * ENNReal.ofReal (log (1 / δ)) := by
  refine task.ae_eventually_stoppingTime_glrt_le alg est hW h_lsc hrec_eq h_est h_prop
    (T₀ := T₀) (f := fun T ↦ log (r T)) (fun ε hε ↦ eventually_log_le_mul_of_isBigO hr hε) ?_
  filter_upwards [hβ, Ioo_mem_nhdsGT one_pos] with δ hβδ hδ T hT h
  exact (hβδ T hT h).trans
    (ENNReal.ofReal_le_ofReal (log_div_le_log_one_div_add_log _ hδ.1 hδ.2.le))

/-- **The GLRT stops almost surely** [GK16, Proposition 13], for every task, every estimator and
every sampling rule. Under the assumptions of `IdentTask.ae_eventually_stoppingTime_glrt_le` on the
task, the estimator and the proportions of pulls, with `inf_{w ∈ W} D(θ, w, ¬i) > 0` and thresholds
`β δ T h ≤ log (1 / δ) + f T` for `T ≥ T₀` and every `δ` in a set `s`, almost surely the GLRT stops
at every confidence level `δ ∈ s`. -/
theorem ae_stoppingTime_glrt_ne_top (hW : IsCompact W)
    (h_lsc : ∀ w ∈ W, LowerSemicontinuousWithinAt
      (fun q : Θ × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (θ, w))
    (hrec_eq : ∀ᶠ θ' in 𝓝 θ, rec θ' = i) (hpos : 0 < ⨅ w ∈ W, task.altCost θ w i)
    (h_est : ∀ᵐ ω ∂P, Tendsto (fun n ↦ est n (history O X Y n ω)) atTop (𝓝 θ))
    (h_prop : ∀ᵐ ω ∂P, Tendsto (fun n a ↦ (pullCount X a n ω : ℝ) / n) atTop (𝓝ˢ W))
    (hf : ∀ ε > 0, ∀ᶠ T in atTop, f T ≤ ε * T) {s : Set ℝ}
    (hβ : ∀ δ ∈ s, ∀ T ≥ T₀, ∀ h, β δ T h ≤ ENNReal.ofReal (log (1 / δ) + f T)) :
    ∀ᵐ ω ∂P, ∀ δ ∈ s, (task.glrt (task.plugInCost est) alg (β δ) (fun n h ↦ rec (est n h)) hrec
      (hstop δ)).stoppingTime O X Y ω ≠ ⊤ := by
  -- A positive rate `κ` below `D(θ, w, ¬i)` for all `w ∈ W`, at which the GLR statistic grows.
  obtain ⟨κ, hκ0, hκ'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
  filter_upwards [h_est, h_prop] with ω h_est h_prop δ hδ
  exact task.stoppingTime_glrt_ne_top_of_eventually_mul_le_glr (task.plugInCost est) alg _ hrec
    (hstop δ) (mod_cast hκ0) (task.eventually_mul_le_glr_plugInCost est hW h_lsc
      (fun w hw ↦ hκ'.trans_le (iInf₂_le w hw)) hrec_eq h_est h_prop) hf
    (eventually_atTop.2 ⟨T₀, fun T hT ↦ hβ δ hδ T hT⟩)

end LMLExplore.Identification.IdentTask
