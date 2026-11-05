/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.CTracking
public import LMLExplore.Identification.DTracking
public import LMLExplore.Identification.GLR
public import LMLExplore.Identification.Task.Continuity
public import LMLExplore.Analysis.Convex.Normed
public import LMLExplore.Topology.Order.Basic
public import LMLExplore.Topology.Semicontinuity.Compact

/-!
# Track-and-Stop

Track-and-Stop [GK16] is the fixed-confidence identification algorithm that samples the arms so
that their proportions of pulls follow an optimal allocation at the current estimate of the model,
and stops with the generalized likelihood ratio test. For an identification task with models `Θ`
and observations in `𝓨`, and an estimator `est` of the model, after `n` rounds with history `h`,
with pull counts `N_a` and estimated model `θ̂ = est n h`, it
* samples with the D-tracking rule of `Identification/DTracking.lean` or the C-tracking rule of
  `Identification/CTracking.lean`, whose target is `w(θ̂)` for a target map `w`, typically a
  selection of the optimal allocations `w*(θ̂, ¬i)`;
* recommends the answer `rec(θ̂)`, typically the correct answer of `θ̂`;
* stops when the GLR statistic of the plug-in statistic
  `GLR_n(h, ¬rec(θ̂)) = inf_{λ ∈ ¬rec(θ̂)} ∑ a, N_a KL(ν_a(θ̂), ν_a(λ))` exceeds a threshold
  `β n h`, which may depend on the history.

The GLR statistic is the transportation cost of the estimated model with the pull counts as
allocation, `GLR_n(h, ¬i) = D(θ̂, N, ¬i) = n D(θ̂, N / n, ¬i)`.

The sample complexity bounds below are stated for tasks whose models are vectors of means
`μ : α → ℝ` of arms with real observations, with the vector `μ̂` of empirical means as estimator.

**Sample complexity with D-tracking** [GK16, Theorem 14]. Let the true model `μ` have rewards
dominated by exponential families with means `μ a`, let the target map be continuous at `μ` and the
recommendation be `i` near `μ`. By the forced exploration of D-tracking, the empirical means stay
close to `μ` from round `t₀(T)` on, except on events whose probabilities have a finite sum over `T`
[GK16, Lemma 19]. On these events, the targets `w(μ̂)` stay close to `w(μ)` from round `t₀(T)` on,
so that the proportions of pulls `N(T) / T` are close to `w(μ)`, and the GLR statistic after `T`
rounds is `T D(μ̂(T), N(T) / T, ¬i) ≥ κ T` for any `κ < D(μ, w(μ), ¬i)`, provided
`(μ', w') ↦ D(μ', w', ¬i)` is lower semicontinuous at `(μ, w(μ))`. The generic reduction
`IdentTask.eventually_expectedStoppingTime_glrt_le_of_isBigO` then gives, for thresholds
`β δ n h ≤ log (r n / δ)` with `r n = O(n ^ p)`, the bound `𝔼[τ_δ] ≤ c log (1 / δ)` for all small
enough `δ`, for every `c > 1 / κ`, hence for every `c > D(μ, w(μ), ¬i)⁻¹`. When `w(μ)` is an
optimal allocation for the single correct answer `i` of `μ`, `D(μ, w(μ), ¬i) = T*(μ)⁻¹` and the
sample complexity of Track-and-Stop is at most the characteristic time:
`limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ T*(μ)`. This upper bound holds for all such thresholds,
including ones that are not `δ`-correct, such as `β = 0`.
Asymptotic optimality, that is, matching the lower bound `𝔼[τ_δ] ≥ T*(μ) kl(δ, 1 - δ)` of
`Identification/LowerBound.lean`, also needs the `δ`-correctness of the thresholds, which is not
proved here; for Gaussian arms it is in `Identification/GaussianThreshold.lean`.

**Sample complexity with C-tracking** [DK19, Lemma 6 and Theorem 7]. When the optimal
allocations `w*(μ, ¬i)` are not unique, a selection `w` of them is in general not continuous at
`μ`, and the proportions of pulls of D-tracking, which follow the current targets, need not
converge. The optimal allocations form a convex compact set, and they are upper hemicontinuous
when `(μ', w') ↦ D(μ', w', ¬i)` is continuous [DK19, Lemma 28], so that the targets `w(μ̂(s))`
eventually lie in every neighbourhood of `w*(μ, ¬i)`. C-tracking makes the pull counts follow the
cumulated targets up to `(K - 1) (1 + √T)` [GK16, Lemma 7], and averages of points close to a
convex set are close to it: the proportions of pulls `N(T) / T` approach `w*(μ, ¬i)`, which is
enough for the GLR statistic to grow like `T (T*(μ)⁻¹ - ε)`. Track-and-Stop with C-tracking
therefore has `limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ T*(μ)` whatever the selection of the
optimal allocations.

**Union-bound thresholds.** The thresholds `K log (2 n (n + 1)) + x_δ` of `Identification/GLR.lean`,
which are `δ`-correct for Gaussian arms, are not of the form `log (r n / δ)`, since
`x_δ - log (1 / δ)` is unbounded, but for every `s > 1` they are at most
`log ((2 n (n + 1)) ^ K / δ ^ s)` for small `δ`. The bound at the confidence level `δ ^ s`
therefore gives `𝔼[τ_δ] ≤ c' s log (1 / δ)` for every `c' > T*(μ)`, and `c' s` is any constant
above `T*(μ)`. A finite expected stopping time at small `δ` gives almost sure stopping at every
`δ ∈ (0, 1]`, since the thresholds decrease with `δ` (`IdentTask.stopsAS_glrt_unionBoundThreshold`).

## Main definitions

* `IdentTask.plugInCost task est n h λ`: the plug-in statistic `∑ a, N_a KL(ν_a(θ̂), ν_a(λ))` of
  the estimator `est` for the history `h` of the first `n` rounds against the model `λ`, the
  transportation cost from the estimated model `θ̂ = est n h` with the pull counts `N` as
  allocation.
* `IdentTask.trackAndStop task est w hw β rec hrec hstop`: Track-and-Stop with D-tracking of the
  targets `w(θ̂)`, recommendation `rec(θ̂)` and GLR stopping with the plug-in statistic of `est` and
  thresholds `β`.
* `IdentTask.cTrackAndStop task est w hw β rec hrec hstop`: Track-and-Stop with C-tracking of the
  targets `w(θ̂)`, recommendation `rec(θ̂)` and GLR stopping with the plug-in statistic of `est` and
  thresholds `β`.

## Main statements

* `IdentTask.glr_plugInCost`, `IdentTask.glr_plugInCost_eq_mul`: the GLR statistic of the plug-in
  statistic is `D(θ̂, N, ¬i) = n D(θ̂, N / n, ¬i)`.
* `IdentTask.eventually_expectedStoppingTime_trackAndStop_le`: [GK16, Theorem 14] for any target
  map continuous at `μ`: `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every
  `c > D(μ, w(μ), ¬i)⁻¹`.
* `IdentTask.eventually_expectedStoppingTime_trackAndStop_le_of_charTime_lt`: **sample complexity
  at the characteristic time** [GK16, Theorem 14]: if `w(μ)` is an optimal allocation for the
  single correct answer `i` of `μ`, then `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for
  every `c > T*(μ)`. The `δ`-correctness of the thresholds, which turns this upper bound into
  asymptotic optimality, is not established here; for Gaussian arms, see
  `IdentTask.tendsto_expectedStoppingTime_trackAndStop_unionBoundThreshold_div_log` in
  `Identification/GaussianThreshold.lean`.
* `IdentTask.eventually_expectedStoppingTime_trackAndStop_unionBoundThreshold_le`: the same bound
  for the union-bound thresholds `K log (2 n (n + 1)) + x_δ` of `Identification/GLR.lean`.
* `IdentTask.stopsAS_trackAndStop_unionBoundThreshold`: with these thresholds, Track-and-Stop
  stops almost surely for every `δ ∈ (0, 1]`.
* `IdentTask.eventually_expectedStoppingTime_cTrackAndStop_le`: [DK19, Theorem 7] for targets that
  converge to a convex compact set `C`: `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for
  every `c > (inf_{v ∈ C} D(μ, v, ¬i))⁻¹`.
* `IdentTask.eventually_expectedStoppingTime_cTrackAndStop_le_of_charTime_lt`: **sample complexity
  of Track-and-Stop with C-tracking at the characteristic time** [DK19, Theorem 7]: if the targets
  are optimal allocations near `μ` and `(μ', w') ↦ D(μ', w', ¬i)` is continuous within
  `univ ×ˢ simplex` at every `(μ, v)` with `v` in the simplex, then `𝔼[τ_δ] ≤ c log (1 / δ)` for
  all small enough `δ`, for every `c > T*(μ)`.
* `IdentTask.eventually_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_le`,
  `IdentTask.stopsAS_cTrackAndStop_unionBoundThreshold`: the same bound for the union-bound
  thresholds, with which Track-and-Stop with C-tracking stops almost surely for every
  `δ ∈ (0, 1]`.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Section 3 and Theorem 14.
* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, Lemma 6 and Theorem 7.
-/

public section

open MeasureTheory ProbabilityTheory Learning Filter Real
open scoped Topology ENNReal NNReal

namespace LMLExplore.Identification.IdentTask

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  {m𝓨 : MeasurableSpace 𝓨} (task : IdentTask α Θ ℐ 𝓨) (est : (n : ℕ) → Hist Unit α 𝓨 n → Θ)
  {n : ℕ} {h : Hist Unit α 𝓨 n} {i : ℐ}

/-! ### The plug-in GLR statistic -/

/-- The *plug-in statistic* of the estimator `est`: the statistic `∑ a, N_a KL(ν_a(θ̂), ν_a(λ))` of
the history `h` of the first `n` rounds against the model `λ`, with `N_a` the number of pulls of
the arm `a` in `h` and `θ̂ = est n h` the estimate of the model from `h`. It is the transportation
cost from the estimated model `θ̂` to `λ` with the pull counts as allocation. When the arm laws of
the models are the members of exponential families with divergence `d`, indexed by their means,
the estimate is the vector `μ̂` of empirical means, and `μ̂` and `λ` are vectors of means of the
families, it is `∑ a, N_a d(μ̂_a, λ_a)`, the log-likelihood ratio of the maximum-likelihood model
against `λ`. -/
noncomputable def plugInCost (n : ℕ) (h : Hist Unit α 𝓨 n) (θ' : Θ) : ℝ≥0∞ :=
  task.cost (fun a ↦ (pullCount' n h a : ℝ)) (est n h) θ'

lemma plugInCost_def (n : ℕ) (h : Hist Unit α 𝓨 n) (θ' : Θ) :
    task.plugInCost est n h θ' = task.cost (fun a ↦ (pullCount' n h a : ℝ)) (est n h) θ' :=
  (rfl)

/-- The GLR statistic of the plug-in statistic is the cost `D(θ̂, N, ¬i)` of the alternatives to
`i` from the estimated model `θ̂ = est n h` with the pull counts `N` as allocation. -/
lemma glr_plugInCost :
    task.glr (task.plugInCost est) n h i =
      task.altCost (est n h) (fun a ↦ (pullCount' n h a : ℝ)) i :=
  task.glr_eq_altCost fun _ _ ↦ task.plugInCost_def est n h _

/-- After `n ≠ 0` rounds, the GLR statistic of the plug-in statistic is `n D(θ̂, N / n, ¬i)`, with
the estimated model `θ̂ = est n h` and the proportions of pulls `N / n` as allocation. -/
lemma glr_plugInCost_eq_mul (hn : n ≠ 0) :
    task.glr (task.plugInCost est) n h i =
      n * task.altCost (est n h) (fun a ↦ (pullCount' n h a : ℝ) / n) i := by
  have hn' : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h_smul :
      (fun a ↦ (pullCount' n h a : ℝ)) = (n : ℝ≥0) • fun a ↦ (pullCount' n h a : ℝ) / n := by
    ext a
    simp [NNReal.smul_def, field]
  rw [glr_plugInCost, h_smul, task.altCost_smul hn', ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_natCast]

/-! ### Track-and-Stop -/

variable [Nonempty α] [MeasurableSingletonClass α] {mℐ : MeasurableSpace ℐ}

/-- **Track-and-Stop** with D-tracking [GK16, Section 3], for any task and any estimator `est` of
the model: the GLRT of the task with the plug-in statistic `IdentTask.plugInCost est`, thresholds
`β`, the recommendation `rec(θ̂)` and the D-tracking sampling rule with targets `w(θ̂)`, where
`θ̂ = est n h` is the estimate of the model from the history `h` of the first `n` rounds. After `n`
rounds with history `h`, it stops if `β n h < GLR_n(h, ¬rec(θ̂))` and then answers `rec(θ̂)`. The
target map `w` is typically a selection of the optimal allocations `w*(θ̂, ¬rec(θ̂))`, and `rec(θ̂)`
a correct answer of `θ̂`. -/
noncomputable def trackAndStop (w : Θ → α → ℝ)
    (hw : ∀ n, Measurable fun h : Hist Unit α 𝓨 n ↦ w (est n h))
    (β : (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞) (rec : Θ → ℐ)
    (hrec : ∀ n, Measurable fun h : Hist Unit α 𝓨 n ↦ rec (est n h))
    (hstop : ∀ n, MeasurableSet {h | β n h < task.glr (task.plugInCost est) n h (rec (est n h))}) :
    IdentAlg Unit α 𝓨 ℐ :=
  task.glrt (task.plugInCost est) (dTracking (fun n h ↦ w (est n h)) hw) β
    (fun n h ↦ rec (est n h)) hrec hstop

variable {w : Θ → α → ℝ} {hw : ∀ n, Measurable fun h : Hist Unit α 𝓨 n ↦ w (est n h)}
  {β : (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞} {rec : Θ → ℐ}
  {hrec : ∀ n, Measurable fun h : Hist Unit α 𝓨 n ↦ rec (est n h)}
  {hstop : ∀ n, MeasurableSet {h | β n h < task.glr (task.plugInCost est) n h (rec (est n h))}}

lemma trackAndStop_def : task.trackAndStop est w hw β rec hrec hstop =
    task.glrt (task.plugInCost est) (dTracking (fun n h ↦ w (est n h)) hw) β
      (fun n h ↦ rec (est n h)) hrec hstop := (rfl)

/-- The sampling rule of Track-and-Stop is D-tracking of the targets `w(θ̂)`. -/
@[simp]
lemma alg_trackAndStop :
    (task.trackAndStop est w hw β rec hrec hstop).alg = dTracking (fun n h ↦ w (est n h)) hw := by
  rw [trackAndStop_def, alg_glrt]

/-- Track-and-Stop stops after the history `h` of the first `n` rounds iff the GLR statistic of
the recommendation `rec(θ̂)` exceeds the threshold `β n h`. -/
@[simp]
lemma mem_stopSet_trackAndStop {h : Σ n, Hist Unit α 𝓨 n} :
    h ∈ (task.trackAndStop est w hw β rec hrec hstop).stopSet ↔
      β h.1 h.2 < task.glr (task.plugInCost est) h.1 h.2 (rec (est h.1 h.2)) := by
  rw [trackAndStop_def, mem_stopSet_glrt]

/-- Track-and-Stop answers the recommendation `rec(θ̂)` of the estimated model. -/
@[simp]
lemma output_trackAndStop (h : Σ n, Hist Unit α 𝓨 n) :
    (task.trackAndStop est w hw β rec hrec hstop).output h =
      Measure.dirac (rec (est h.1 h.2)) := by
  rw [trackAndStop_def, output_glrt]

/-- **Track-and-Stop with C-tracking** [GK16, Section 3; DK19, Theorem 7], for any task and any
estimator `est` of the model: the GLRT of the task with the plug-in statistic
`IdentTask.plugInCost est`, thresholds `β`, the recommendation `rec(θ̂)` and the C-tracking
sampling rule with targets `w(θ̂)`, where `θ̂ = est n h` is the estimate of the model from the
history `h` of the first `n` rounds. After `n` rounds with history `h`, it stops if
`β n h < GLR_n(h, ¬rec(θ̂))` and then answers `rec(θ̂)`. Unlike D-tracking
(`IdentTask.trackAndStop`), C-tracking follows the averages of the past targets, so that the target
map `w` may be any selection of the optimal allocations `w*(θ̂, ¬rec(θ̂))`, even when these are not
unique. -/
noncomputable def cTrackAndStop (w : Θ → α → ℝ)
    (hw : ∀ n, Measurable fun h : Hist Unit α 𝓨 n ↦ w (est n h))
    (β : (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞) (rec : Θ → ℐ)
    (hrec : ∀ n, Measurable fun h : Hist Unit α 𝓨 n ↦ rec (est n h))
    (hstop : ∀ n, MeasurableSet {h | β n h < task.glr (task.plugInCost est) n h (rec (est n h))}) :
    IdentAlg Unit α 𝓨 ℐ :=
  task.glrt (task.plugInCost est) (cTracking (fun n h ↦ w (est n h)) hw) β
    (fun n h ↦ rec (est n h)) hrec hstop

lemma cTrackAndStop_def : task.cTrackAndStop est w hw β rec hrec hstop =
    task.glrt (task.plugInCost est) (cTracking (fun n h ↦ w (est n h)) hw) β
      (fun n h ↦ rec (est n h)) hrec hstop := (rfl)

/-- The sampling rule of Track-and-Stop with C-tracking is C-tracking of the targets `w(θ̂)`. -/
@[simp]
lemma alg_cTrackAndStop :
    (task.cTrackAndStop est w hw β rec hrec hstop).alg = cTracking (fun n h ↦ w (est n h)) hw := by
  rw [cTrackAndStop_def, alg_glrt]

/-- Track-and-Stop with C-tracking stops after the history `h` of the first `n` rounds iff the
GLR statistic of the recommendation `rec(θ̂)` exceeds the threshold `β n h`. -/
@[simp]
lemma mem_stopSet_cTrackAndStop {h : Σ n, Hist Unit α 𝓨 n} :
    h ∈ (task.cTrackAndStop est w hw β rec hrec hstop).stopSet ↔
      β h.1 h.2 < task.glr (task.plugInCost est) h.1 h.2 (rec (est h.1 h.2)) := by
  rw [cTrackAndStop_def, mem_stopSet_glrt]

/-- Track-and-Stop with C-tracking answers the recommendation `rec(θ̂)` of the estimated model. -/
@[simp]
lemma output_cTrackAndStop (h : Σ n, Hist Unit α 𝓨 n) :
    (task.cTrackAndStop est w hw β rec hrec hstop).output h =
      Measure.dirac (rec (est h.1 h.2)) := by
  rw [cTrackAndStop_def, output_glrt]

end LMLExplore.Identification.IdentTask

/-! ### Sample complexity -/

namespace LMLExplore.Identification.IdentTask

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {mℐ : MeasurableSpace ℐ} (task : IdentTask α (α → ℝ) ℐ ℝ)
  {i : ℐ} {w : (α → ℝ) → α → ℝ} {hw : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ w (empMean' n h)}
  {rec : (α → ℝ) → ℐ} {hrec : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ rec (empMean' n h)}
/-- The forced exploration rounds `t₀(T) = ⌈log⁴ T⌉` after which the empirical means are required
to be close to the model in the analysis of Track-and-Stop. -/
private noncomputable def roundsAfter (T : ℕ) : ℕ := ⌈log T ^ 4⌉₊

/-- `√t₀(T) ≥ log² T` grows faster than `log T`, as the concentration of the empirical means
under D-tracking requires. -/
private lemma tendsto_sqrt_roundsAfter_div_log :
    Tendsto (fun T : ℕ ↦ √(roundsAfter T : ℝ) / log T) atTop atTop := by
  have hlog : Tendsto (fun T : ℕ ↦ log T) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [hlog.eventually_gt_atTop 0] with T hT
  rw [le_div_iff₀ hT, ← sq, ← sqrt_sq (sq_nonneg (log T)), ← pow_mul]
  exact sqrt_le_sqrt (Nat.le_ceil _)

/-- `t₀(T) ≤ c T` for all large `T`, for every `c > 0`. -/
private lemma eventually_roundsAfter_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ T : ℕ in atTop, (roundsAfter T : ℝ) ≤ c * T := by
  have h_lim : Tendsto (fun T : ℕ ↦ log T ^ 4 / T + 1 / T) atTop (𝓝 0) := by
    have h := (tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa using h.add (tendsto_const_div_atTop_nhds_zero_nat 1)
  filter_upwards [h_lim.eventually_le_const hc, eventually_gt_atTop 0] with T hT hT0
  have hT' : (0 : ℝ) < T := Nat.cast_pos.2 hT0
  rw [← add_div, div_le_iff₀ hT'] at hT
  exact (Nat.ceil_lt_add_one (by positivity)).le.trans hT

/-- `t₀(T) → ∞`. -/
private lemma tendsto_roundsAfter : Tendsto (fun T : ℕ ↦ (roundsAfter T : ℝ)) atTop atTop :=
  tendsto_atTop_mono (fun _ ↦ Nat.le_ceil _)
    ((tendsto_pow_atTop (by norm_num)).comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ}
  {β : ℝ → (n : ℕ) → Hist Unit α ℝ n → ℝ≥0∞}
  {hstop : ∀ δ n, MeasurableSet
    {h | β δ n h < task.glr (task.plugInCost empMean') n h (rec (empMean' n h))}}
  {r : ℕ → ℝ} {p : ℝ} {n₀ : ℕ}

/-- If `D⁻¹ < c`, then some rate `κ` satisfies `κ < D` and `1 < κ c`: the rate at which the proofs
of the sample complexity bounds of Track-and-Stop make the GLR statistic grow. -/
private lemma exists_lt_one_lt_mul_of_inv_lt {D : ℝ≥0∞} {c : ℝ≥0} (hc : D⁻¹ < c) :
    ∃ κ : ℝ≥0, (κ : ℝ≥0∞) < D ∧ 1 < κ * c := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact not_lt_zero (ENNReal.coe_zero ▸ hc)
  rw [ENNReal.inv_lt_iff_inv_lt, ← ENNReal.coe_inv hc0] at hc
  obtain ⟨κ, hcκ, hκ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hc
  refine ⟨κ, hκ, ?_⟩
  rw [← inv_mul_cancel₀ hc0]
  exact mul_lt_mul_of_pos_right (ENNReal.coe_lt_coe.1 hcκ) (pos_iff_ne_zero.2 hc0)

omit [MeasurableSingletonClass α] in
/-- The deterministic step of the analysis of Track-and-Stop [GK16, proof of Theorem 14]. Along a
sequence of arms following the D-tracking rule with targets `w(μ̂(k))`, suppose that from round `t₀`
on, the empirical means `μ̂(k)` lie in a set `U` on which the cost of the alternatives to `i`
exceeds `κ` at every allocation of the simplex `η`-close to `w(μ)`, the targets `w(μ̂(k))` are
`ε`-close to `w(μ)` with `3 K ε ≤ η`, and the recommendation is `i`. If `t₀ ≥ 1 / (4 ε²)`,
`t₀ ≤ T`, `t₀ ≤ 3 ε T` and `1 ≤ ε T`, then the GLR statistic of the recommendation after `T`
rounds is at least `κ T`. -/
private lemma mul_le_glr_plugInCost {Ω : Type*} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
    {Y : ℕ → Ω → ℝ} {ω : Ω} {U : Set (α → ℝ)} {ε η : ℝ} {κ : ℝ≥0} {t₀ T : ℕ}
    (hw_mem : w μ ∈ simplex α) (hε : 0 < ε) (hεη : 3 * Fintype.card α * ε ≤ η)
    (hU : ∀ μ' ∈ U, ∀ w' ∈ simplex α, dist w' (w μ) < η → (κ : ℝ≥0∞) < task.altCost μ' w' i)
    (hmeans : ∀ k ≥ t₀, empMean' k (history O A Y k ω) ∈ U ∧
      dist (w (empMean' k (history O A Y k ω))) (w μ) < ε ∧
      rec (empMean' k (history O A Y k ω)) = i)
    (hforced : ∀ (k : ℕ) a, (pullCount A a k ω : ℝ) < √(k : ℝ) - Fintype.card α / 2 →
      pullCount A (A k ω) k ω ≤ pullCount A a k ω)
    (htrack : ∀ k : ℕ, (∀ a, √(k : ℝ) - Fintype.card α / 2 ≤ pullCount A a k ω) → ∀ a,
      k * w (empMean' k (history O A Y k ω)) a - pullCount A a k ω ≤
        k * w (empMean' k (history O A Y k ω)) (A k ω) - pullCount A (A k ω) k ω)
    (ht₀ : 1 / (4 * ε ^ 2) ≤ t₀) (hT : t₀ ≤ T) (ht₀T : (t₀ : ℝ) ≤ 3 * ε * T) (hεT : 1 ≤ ε * T) :
    κ * T ≤ task.glr (task.plugInCost empMean') T (history O A Y T ω)
      (rec (empMean' T (history O A Y T ω))) := by
  have hT0 : T ≠ 0 := by
    rintro rfl
    simp only [CharP.cast_eq_zero, mul_zero] at hεT
    linarith
  have hw_close : ∀ k ≥ t₀, ∀ a, |w (empMean' k (history O A Y k ω)) a - w μ a| ≤ ε :=
    fun k hk a ↦ (Real.dist_eq _ _ ▸ (dist_pi_lt_iff hε).1 (hmeans k hk).2.1 a).le
  -- The exploration threshold `√k - K / 2` is below `2 ε k` from round `t₀` on.
  have hg (k : ℕ) (hk : t₀ ≤ k) : √(k : ℝ) - Fintype.card α / 2 ≤ 2 * ε * k := by
    have hk' : 1 / (4 * ε ^ 2) ≤ (k : ℝ) := ht₀.trans (Nat.cast_le.2 hk)
    rw [div_le_iff₀ (by positivity)] at hk'
    have hsq : √(k : ℝ) ≤ 2 * ε * k := by
      rw [sqrt_le_left (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    linarith [show (0 : ℝ) ≤ Fintype.card α / 2 by positivity]
  -- The proportions of pulls `q = N(T) / T` are an allocation `η`-close to `w(μ)`.
  set q : α → ℝ := fun a ↦ (pullCount' T (history O A Y T ω) a : ℝ) / T
  have hq : q ∈ simplex α := by
    refine mem_simplex_iff.2 ⟨fun a ↦ by positivity, ?_⟩
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_pullCount', div_self (Nat.cast_ne_zero.2 hT0)]
  have hq_dist : dist q (w μ) < η := by
    refine (dist_pi_lt_iff (hε.trans_le (le_mul_of_one_le_left hε.le ?_) |>.trans_le hεη)).2
      fun a ↦ ?_
    · have : (1 : ℝ) ≤ Fintype.card α := Nat.one_le_cast.2 Fintype.card_pos
      linarith
    have h := abs_pullCount_div_sub_le (mem_simplex_iff.1 hw_mem).1 (mem_simplex_iff.1 hw_mem).2
      (fun k _ ↦ hforced k) (fun k _ ↦ htrack k) hw_close hg hT ht₀T hεT a
    rw [Real.dist_eq]
    simp only [q, ← pullCount_eq_pullCount']
    linarith
  obtain ⟨hU', -, hrec'⟩ := hmeans T hT
  rw [hrec', glr_plugInCost_eq_mul task empMean' hT0, mul_comm]
  exact mul_le_mul_right (hU _ hU' q hq hq_dist).le _

/-- **Sample complexity of Track-and-Stop** [GK16, Theorem 14]. Let the rewards of each arm `a` of
the model `μ` be dominated above and below by the member of mean `μ a` of a nondegenerate
exponential family `(ρ a, T a)`. Let the target map `w` be continuous at `μ` with `w(μ)` a
probability vector, let the recommendation be `i` near `μ`, and let `(μ', w') ↦ D(μ', w', ¬i)` be
lower semicontinuous at `(μ, w(μ))` on the allocations of the simplex. Then for thresholds
`β δ n h ≤ log (r n / δ)` (for `n ≥ n₀`) with `r n = O(n ^ p)`, Track-and-Stop with the empirical
means as estimator satisfies `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every
`c > D(μ, w(μ), ¬i)⁻¹`. The constant does not depend on `p`, unlike in [GK16, Theorem 14], whose
bound for `r(t) = O(t ^ α)` has a factor `α ∈ [1, e / 2]`. -/
theorem eventually_expectedStoppingTime_trackAndStop_le (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν_above : ∀ a, MGFDominatedAbove id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hν_below : ∀ a, MGFDominatedBelow id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hw_mem : w μ ∈ simplex α) (hw_cont : ContinuousAt w μ) (hrec_eq : ∀ᶠ μ' in 𝓝 μ, rec μ' = i)
    (h_lsc : LowerSemicontinuousWithinAt (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i)
      (Set.univ ×ˢ simplex α) (μ, w μ))
    {c : ℝ≥0} (hc : (task.altCost μ (w μ) i)⁻¹ < c)
    (hr : r =O[atTop] fun n ↦ (n : ℝ) ^ p)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ n ≥ n₀, ∀ h, β δ n h ≤ ENNReal.ofReal (log (r n / δ))) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.trackAndStop empMean' w hw (β δ) rec hrec (hstop δ))
      (Environment.bandit (task.ν μ)) ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  -- A rate `κ` with `c⁻¹ < κ < D(μ, w(μ), ¬i)`, at which the GLR statistic grows.
  obtain ⟨κ, hκ, hκc⟩ := exists_lt_one_lt_mul_of_inv_lt hc
  set alg := dTracking (fun n h ↦ w (empMean' n h)) hw
  set P := trajMeasure alg (Environment.bandit (task.ν μ))
  have hseq : IsAlgEnvSeq IT.obs IT.action IT.feedback alg (Environment.bandit (task.ν μ)) P :=
    IT.isAlgEnvSeq_trajMeasure alg _
  set K : ℝ := (Fintype.card α : ℝ)
  -- Near `(μ, w(μ))` on the simplex, the cost of the alternatives exceeds `κ`.
  obtain ⟨U, hU, η, hη, hUη⟩ :=
    (isCompact_singleton (x := w μ)).exists_forall_mem_thickening_lt_of_lowerSemicontinuousWithinAt
      (f := fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i) (c := (κ : ℝ≥0∞))
      (fun v hv ↦ (Set.mem_singleton_iff.1 hv) ▸ h_lsc)
      (fun v hv ↦ (Set.mem_singleton_iff.1 hv) ▸ hκ)
  -- Near `μ`, the targets are `ε`-close to `w(μ)`, the recommendation is `i` and the vectors are
  -- vectors of means of the families.
  set ε := η / (3 * K)
  have hε : 0 < ε := by positivity
  set W := {μ' | μ' ∈ U ∧ dist (w μ') (w μ) < ε ∧ rec μ' = i ∧
    ∀ a, μ' a ∈ (ρ a).expFamilyMeans (T a)}
  have hW : W ∈ 𝓝 μ := by
    filter_upwards [hU, hw_cont (Metric.ball_mem_nhds _ hε), hrec_eq, eventually_all.2 fun a ↦
      (continuous_apply a).continuousAt.preimage_mem_nhds
        (Measure.expFamilyMeans_mem_nhds (hT a) (hμ a))] with μ' h1 h2 h3 h4
    exact ⟨h1, Metric.mem_ball.1 h2, h3, h4⟩
  obtain ⟨l, u, hlμ, hμu, h_box⟩ := exists_pi_Icc_subset_of_mem_nhds hW
  have hlu : l ≤ u := fun a ↦ ((hlμ a).trans (hμu a)).le
  have hlW := h_box (Set.left_mem_Icc.2 hlu)
  have huW := h_box (Set.right_mem_Icc.2 hlu)
  -- The good events: the empirical means stay in the box `∏ (l a, u a)` from round `t₀(T)` on,
  -- and the run follows the D-tracking rule.
  set E : ℕ → Set _ := fun T ↦ {ω |
    (∀ t ≥ roundsAfter T, ∀ a, empMean IT.action IT.feedback a t ω ∈ Set.Ioo (l a) (u a)) ∧
    (∀ (k : ℕ) a, (pullCount IT.action a k ω : ℝ) < √(k : ℝ) - K / 2 →
      pullCount IT.action (IT.action k ω) k ω ≤ pullCount IT.action a k ω) ∧
    (∀ k : ℕ, (∀ a, √(k : ℝ) - K / 2 ≤ pullCount IT.action a k ω) → ∀ a,
      k * w (empMean' k (history IT.obs IT.action IT.feedback k ω)) a -
          pullCount IT.action a k ω ≤
        k * w (empMean' k (history IT.obs IT.action IT.feedback k ω)) (IT.action k ω) -
          pullCount IT.action (IT.action k ω) k ω)}
  have hE_sum : ∑' T, P (E T)ᶜ ≠ ∞ := by
    refine ne_top_of_le_ne_top (DTracking.tsum_measure_exists_ge_empMean_notMem_Ioo_ne_top hseq
      hν_above hν_below hμ (fun a ↦ hlW.2.2.2 a) (fun a ↦ huW.2.2.2 a) hlμ hμu
      tendsto_sqrt_roundsAfter_div_log)
      (tsum_le_tsum fun T ↦ measure_mono_ae ?_)
    filter_upwards [DTracking.pullCount_action_le_of_lt hseq,
      DTracking.mul_sub_pullCount_le_of_forall_le hseq] with ω h_forced h_track hωE
    by_contra h_box
    push Not at h_box
    exact hωE ⟨h_box, h_forced, h_track⟩
  -- From some round on, on the good event of round `T`, the GLR statistic is at least `κ T`.
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1
    ((eventually_roundsAfter_le (by positivity : 0 < 3 * ε)).and
    ((eventually_roundsAfter_le one_pos).and
    ((tendsto_roundsAfter.eventually_ge_atTop (1 / (4 * ε ^ 2))).and
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 / ε)))))
  have hE (T : ℕ) (hT : max n₀ T₁ ≤ T) (ω) (hω : ω ∈ E T) :
      κ * T ≤ task.glr (task.plugInCost empMean') T (history IT.obs IT.action IT.feedback T ω)
        (rec (empMean' T (history IT.obs IT.action IT.feedback T ω))) := by
    obtain ⟨hω_box, hω_forced, hω_track⟩ := hω
    obtain ⟨h3ε, hT_le, ht₀, hεT⟩ := hT₁ T (le_of_max_le_right hT)
    refine task.mul_le_glr_plugInCost (η := η) hw_mem hε
      (le_of_eq (by simp only [ε, K]; field_simp)) (fun μ' hμ' w' hw' hd ↦
        hUη μ' hμ' w' hw' (by rwa [Metric.thickening_singleton, Metric.mem_ball]))
      (fun k hk ↦ ?_) hω_forced hω_track ht₀ (by exact_mod_cast hT_le.trans_eq (one_mul _)) h3ε
      (by rwa [div_le_iff₀' hε] at hεT)
    -- The empirical means at the rounds `k ≥ t₀(T)` are in `W`.
    have hk_box (b : α) :
        empMean' k (history IT.obs IT.action IT.feedback k ω) b ∈ Set.Ioo (l b) (u b) := by
      rw [← empMean_eq_empMean']
      exact hω_box k hk b
    exact (h_box ⟨fun b ↦ (hk_box b).1.le, fun b ↦ (hk_box b).2.le⟩).imp_right
      fun h ↦ ⟨h.1, h.2.1⟩
  have h := task.eventually_expectedStoppingTime_glrt_le_of_isBigO (task.plugInCost empMean') alg
    (fun n h ↦ rec (empMean' n h)) hrec hstop hseq
    hE_sum hκc hE hr (T₀ := max n₀ T₁)
    (by filter_upwards [hβ] with δ hδ n hn h using hδ n (le_of_max_le_left hn) h)
  simpa only [trackAndStop_def] using h

/-- **Sample complexity of Track-and-Stop at the characteristic time** [GK16, Theorem 14], the
upper bound `𝔼[τ_δ] ≤ c log (1 / δ)` with `c > T*(μ)`. Let the rewards of each arm `a`
of the model `μ` be dominated above and below by the member of mean `μ a` of a nondegenerate
exponential family `(ρ a, T a)`, let `i` be the single correct answer of `μ`, let the target map
`w` be continuous at `μ` with `w(μ)` an optimal allocation `w*(μ, ¬i)`, let the recommendation be
`i` near `μ`, and let `(μ', w') ↦ D(μ', w', ¬i)` be lower semicontinuous at `(μ, w(μ))` on the
allocations of the simplex. Then for thresholds `β δ n h ≤ log (r n / δ)` (for `n ≥ n₀`) with
`r n = O(n ^ p)`, Track-and-Stop with the empirical means as estimator satisfies
`𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every `c > T*(μ)`:
`limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ T*(μ)`. This is asymptotic optimality
only for `δ`-correct thresholds, whose correctness is not proved here. For Gaussian arms, the
union-bound thresholds `K log (2 n (n + 1)) + x_δ` are `δ`-correct, and asymptotic optimality is
`IdentTask.tendsto_expectedStoppingTime_trackAndStop_unionBoundThreshold_div_log` in
`Identification/GaussianThreshold.lean`. -/
theorem eventually_expectedStoppingTime_trackAndStop_le_of_charTime_lt
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν_above : ∀ a, MGFDominatedAbove id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hν_below : ∀ a, MGFDominatedBelow id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hcorrect : task.correct μ = {i}) (hw_opt : w μ ∈ task.optAlloc μ i)
    (hw_cont : ContinuousAt w μ) (hrec_eq : ∀ᶠ μ' in 𝓝 μ, rec μ' = i)
    (h_lsc : LowerSemicontinuousWithinAt (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i)
      (Set.univ ×ˢ simplex α) (μ, w μ))
    {c : ℝ≥0} (hc : task.charTime μ < c) (hr : r =O[atTop] fun n ↦ (n : ℝ) ^ p)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ n ≥ n₀, ∀ h, β δ n h ≤ ENNReal.ofReal (log (r n / δ))) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.trackAndStop empMean' w hw (β δ) rec hrec (hstop δ))
      (Environment.bandit (task.ν μ)) ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  -- At an optimal allocation, `D(μ, w(μ), ¬i)⁻¹ = D(μ, ¬i)⁻¹ = T*(μ)`.
  rw [task.charTime_eq_inv_answerValue hcorrect, ← (task.mem_optAlloc_iff.1 hw_opt).2] at hc
  exact task.eventually_expectedStoppingTime_trackAndStop_le hT hμ hν_above hν_below
    (task.mem_optAlloc_iff.1 hw_opt).1 hw_cont hrec_eq h_lsc hc hr hβ

end LMLExplore.Identification.IdentTask

/-! ### Union-bound thresholds -/

namespace LMLExplore.Identification.IdentTask

open Filter Topology

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {mℐ : MeasurableSpace ℐ} {task : IdentTask α (α → ℝ) ℐ ℝ}
  {w : (α → ℝ) → α → ℝ}
  {hw : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ w (empMean' n h)} {rec : (α → ℝ) → ℐ}
  {hrec : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ rec (empMean' n h)}
  {hstop : ∀ δ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
    (unionBoundLevel (Fintype.card α) δ) n <
      task.glr (task.plugInCost empMean') n h (rec (empMean' n h))}}
  {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ}
  {i : ℐ}

/-- **Sample complexity of Track-and-Stop with the union-bound thresholds** [GK16, Theorem 14].
Under the assumptions of `IdentTask.eventually_expectedStoppingTime_trackAndStop_le_of_charTime_lt`
on the model `μ`, Track-and-Stop with the thresholds `K log (2 n (n + 1)) + x_δ` satisfies
`𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every `c > T*(μ)`:
`limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ T*(μ)`. For Gaussian arms, these thresholds are
`δ`-correct (`IdentTask.isDeltaPAC_trackAndStop_unionBoundThreshold`). -/
theorem eventually_expectedStoppingTime_trackAndStop_unionBoundThreshold_le
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν_above : ∀ a, MGFDominatedAbove id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hν_below : ∀ a, MGFDominatedBelow id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hcorrect : task.correct μ = {i}) (hw_opt : w μ ∈ task.optAlloc μ i)
    (hw_cont : ContinuousAt w μ) (hrec_eq : ∀ᶠ μ' in 𝓝 μ, rec μ' = i)
    (h_lsc : LowerSemicontinuousWithinAt (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i)
      (Set.univ ×ˢ simplex α) (μ, w μ))
    {c : ℝ≥0} (hc : task.charTime μ < c) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.trackAndStop empMean' w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n)
      rec hrec (hstop δ)) (Environment.bandit (task.ν μ)) ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  refine eventually_le_mul_ofReal_log_of_rpow_inv (fun c' hc' s hs ↦ ?_) hc
  -- At the confidence level `δ ^ (1 / s)`, the thresholds are at most `log (r n / δ)` with
  -- `r n = (2 n (n + 1)) ^ K`.
  exact task.eventually_expectedStoppingTime_trackAndStop_le_of_charTime_lt (hw := hw)
    (hrec := hrec) (hstop := fun δ' ↦ hstop (δ' ^ s⁻¹)) hT hμ hν_above hν_below hcorrect hw_opt
    hw_cont hrec_eq h_lsc hc' (isBigO_two_mul_mul_add_one_pow _)
    ((eventually_unionBoundThreshold_rpow_inv_le _ hs).mono fun _ h n hn _ ↦ h n hn)

/-- **Track-and-Stop with the union-bound thresholds stops almost surely**, with the thresholds
`K log (2 n (n + 1)) + x_δ` of every confidence level `δ ∈ (0, 1]`, on a model `μ` with
`T*(μ) < ∞` that satisfies the assumptions of
`IdentTask.eventually_expectedStoppingTime_trackAndStop_unionBoundThreshold_le`. -/
theorem stopsAS_trackAndStop_unionBoundThreshold
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν_above : ∀ a, MGFDominatedAbove id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hν_below : ∀ a, MGFDominatedBelow id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hcorrect : task.correct μ = {i}) (hw_opt : w μ ∈ task.optAlloc μ i)
    (hw_cont : ContinuousAt w μ) (hrec_eq : ∀ᶠ μ' in 𝓝 μ, rec μ' = i)
    (h_lsc : LowerSemicontinuousWithinAt (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i)
      (Set.univ ×ˢ simplex α) (μ, w μ))
    (h_charTime : task.charTime μ ≠ ∞) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    StopsAS (task.trackAndStop empMean' w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n)
      rec hrec (hstop δ)) (Environment.bandit (task.ν μ)) := by
  have hc : task.charTime μ < (task.charTime μ).toNNReal + 1 := by
    rw [ENNReal.coe_toNNReal h_charTime]
    exact ENNReal.lt_add_right h_charTime one_ne_zero
  have h := eventually_expectedStoppingTime_trackAndStop_unionBoundThreshold_le (hw := hw)
    (hrec := hrec) (hstop := hstop) hT hμ hν_above hν_below hcorrect hw_opt hw_cont hrec_eq h_lsc hc
  simp only [trackAndStop_def] at h ⊢
  exact stopsAS_glrt_unionBoundThreshold (h.mono fun _ hδ' ↦ ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hδ').frequently hδ hδ1

end LMLExplore.Identification.IdentTask

/-! ### Track-and-Stop with C-tracking -/

namespace LMLExplore.Identification.IdentTask

open Filter Topology Metric Finset

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {mℐ : MeasurableSpace ℐ} (task : IdentTask α (α → ℝ) ℐ ℝ)
  {i : ℐ}

variable {w : (α → ℝ) → α → ℝ} {hw : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ w (empMean' n h)}
  {rec : (α → ℝ) → ℐ} {hrec : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ rec (empMean' n h)}

omit [MeasurableSingletonClass α] in
/-- The deterministic step of the analysis of Track-and-Stop with C-tracking [DK19, Lemma 6 and
proof of Theorem 7]. Along a sequence of arms whose pull counts follow the cumulated targets
`w(μ̂(s))` up to `(K - 1) (1 + √T)` after `T` rounds, suppose that from round `t₀` on, the
empirical means `μ̂(k)` lie in a set `U` on which the cost of the alternatives to `i` exceeds `κ`
at every allocation of the simplex `η`-close to the convex set `C`, the targets `w(μ̂(k))` are
`ε`-close to `C` and the recommendation is `i`. Since averages of points close to `C` are close
to `C` (`Convex.exists_mem_norm_sum_sub_smul_le`), the proportions of pulls after `T` rounds are
close to `C`: if the elements of `C` have norm at most `B` and
`(K - 1) (1 + √T) + (1 + B) t₀ + ε T < η T`, then the GLR statistic of the recommendation after
`T` rounds is at least `κ T`. -/
private lemma mul_le_glr_plugInCost_of_mem_thickening {Ω : Type*} {O : ℕ → Ω → Unit}
    {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ} {ω : Ω} {C U : Set (α → ℝ)} {B ε η : ℝ} {κ : ℝ≥0}
    {t₀ T : ℕ} (hw_mem : ∀ μ', w μ' ∈ simplex α) (hC : Convex ℝ C) (hCB : ∀ v ∈ C, ‖v‖ ≤ B)
    (hU : ∀ μ' ∈ U, ∀ w' ∈ simplex α, w' ∈ thickening η C → (κ : ℝ≥0∞) < task.altCost μ' w' i)
    (hmeans : ∀ k ≥ t₀, empMean' k (history O A Y k ω) ∈ U ∧
      w (empMean' k (history O A Y k ω)) ∈ thickening ε C ∧
      rec (empMean' k (history O A Y k ω)) = i)
    (htrack : ∀ a, |(pullCount A a T ω : ℝ) -
      ∑ s ∈ range T, w (empMean' s (history O A Y s ω)) a| ≤ (Fintype.card α - 1) * (1 + √(T : ℝ)))
    (hT : t₀ ≤ T) (hT0 : T ≠ 0)
    (hTη : (Fintype.card α - 1) * (1 + √(T : ℝ)) + (1 + B) * t₀ + ε * T < η * T) :
    κ * T ≤ task.glr (task.plugInCost empMean') T (history O A Y T ω)
      (rec (empMean' T (history O A Y T ω))) := by
  set v : ℕ → α → ℝ := fun s ↦ w (empMean' s (history O A Y s ω))
  have hT' : (0 : ℝ) < T := Nat.cast_pos.2 (Nat.pos_of_ne_zero hT0)
  obtain ⟨hU', hεC, hrec'⟩ := hmeans T hT
  obtain ⟨c₀, hc₀, hdc₀⟩ := mem_thickening_iff.1 hεC
  have hε : 0 < ε := dist_nonneg.trans_lt hdc₀
  -- The targets are allocations, of norm at most `1`.
  have hv (s : ℕ) : ‖v s‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a ↦ ?_
    have hv := mem_simplex_iff.1 (hw_mem (empMean' s (history O A Y s ω)))
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith [hv.1 a],
      (simplex_subset_Icc (hw_mem (empMean' s (history O A Y s ω)))).2 a⟩
  -- The average of the targets is close to a point `cbar` of the convex set `C`.
  obtain ⟨cbar, hcbar, h_avg⟩ := hC.exists_mem_norm_sum_sub_smul_le ⟨c₀, hc₀⟩ hT
    (fun s _ ↦ hv s) hCB fun s hs _ ↦ (hmeans s hs).2.1
  have h_sum (a : α) : |∑ s ∈ range T, v s a - T * cbar a| ≤ (1 + B) * t₀ + ε * (T - t₀) := by
    have h := (norm_le_pi_norm (∑ s ∈ range T, v s - (T : ℝ) • cbar) a).trans h_avg
    simpa only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
      using h
  -- The proportions of pulls `q = N(T) / T` are an allocation `η`-close to `cbar`.
  set q : α → ℝ := fun a ↦ (pullCount' T (history O A Y T ω) a : ℝ) / T
  have hq : q ∈ simplex α := by
    refine mem_simplex_iff.2 ⟨fun a ↦ by positivity, ?_⟩
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_pullCount', div_self hT'.ne']
  have hq_dist (a : α) : |q a - cbar a| < η := by
    have h_eq : q a - cbar a = ((pullCount A a T ω - ∑ s ∈ range T, v s a) +
        (∑ s ∈ range T, v s a - T * cbar a)) / T := by
      simp only [q, ← pullCount_eq_pullCount']
      field_simp
      ring
    rw [h_eq, abs_div, abs_of_pos hT', div_lt_iff₀ hT']
    linarith [abs_add_le (pullCount A a T ω - ∑ s ∈ range T, v s a)
      (∑ s ∈ range T, v s a - T * cbar a), htrack a, h_sum a,
      mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) t₀)]
  have hη : 0 < η := (abs_nonneg _).trans_lt (hq_dist (Classical.arbitrary α))
  rw [hrec', glr_plugInCost_eq_mul task empMean' hT0, mul_comm]
  refine mul_le_mul_right (hU _ hU' q hq (mem_thickening_iff.2 ⟨cbar, hcbar, ?_⟩)).le _
  exact (dist_pi_lt_iff hη).2 fun a ↦ Real.dist_eq _ _ ▸ hq_dist a

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ}
  {β : ℝ → (n : ℕ) → Hist Unit α ℝ n → ℝ≥0∞}
  {hstop : ∀ δ n, MeasurableSet
    {h | β δ n h < task.glr (task.plugInCost empMean') n h (rec (empMean' n h))}}
  {r : ℕ → ℝ} {p : ℝ} {n₀ : ℕ}

/-- **Sample complexity of Track-and-Stop with C-tracking** [DK19, Lemma 6 and Theorem 7]. Let the
rewards of each arm `a` of the model `μ` be dominated above and below by the member of mean `μ a`
of a nondegenerate exponential family `(ρ a, T a)`. Let the targets `w` be allocations that
converge at `μ` to a convex compact set `C` (they eventually lie in every neighbourhood of `C`),
let the recommendation be `i` near `μ`, and let `(μ', w') ↦ D(μ', w', ¬i)` be lower
semicontinuous at every point of `{μ} × C` on the allocations of the simplex. Then for thresholds
`β δ n h ≤ log (r n / δ)` (for `n ≥ n₀`) with `r n = O(n ^ p)`, Track-and-Stop with C-tracking and
the empirical means as estimator satisfies `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for
every `c > (inf_{v ∈ C} D(μ, v, ¬i))⁻¹`. -/
theorem eventually_expectedStoppingTime_cTrackAndStop_le (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν_above : ∀ a, MGFDominatedAbove id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hν_below : ∀ a, MGFDominatedBelow id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hw_mem : ∀ μ', w μ' ∈ simplex α) {C : Set (α → ℝ)} (hC_conv : Convex ℝ C)
    (hC_compact : IsCompact C) (hw_tendsto : Tendsto w (𝓝 μ) (𝓝ˢ C))
    (hrec_eq : ∀ᶠ μ' in 𝓝 μ, rec μ' = i)
    (h_lsc : ∀ v ∈ C, LowerSemicontinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (μ, v))
    {c : ℝ≥0} (hc : (⨅ v ∈ C, task.altCost μ v i)⁻¹ < c)
    (hr : r =O[atTop] fun n ↦ (n : ℝ) ^ p)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ n ≥ n₀, ∀ h, β δ n h ≤ ENNReal.ofReal (log (r n / δ))) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.cTrackAndStop empMean' w hw (β δ) rec hrec (hstop δ))
      (Environment.bandit (task.ν μ)) ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  -- A rate `κ` with `c⁻¹ < κ < D(μ, v, ¬i)` for all `v ∈ C`, at which the GLR statistic grows.
  obtain ⟨κ, hκ', hκc⟩ := exists_lt_one_lt_mul_of_inv_lt hc
  have hκ : ∀ v ∈ C, (κ : ℝ≥0∞) < task.altCost μ v i := fun v hv ↦ hκ'.trans_le (iInf₂_le v hv)
  set alg := cTracking (fun n h ↦ w (empMean' n h)) hw
  set P := trajMeasure alg (Environment.bandit (task.ν μ))
  have hseq : IsAlgEnvSeq IT.obs IT.action IT.feedback alg (Environment.bandit (task.ν μ)) P :=
    IT.isAlgEnvSeq_trajMeasure alg _
  set K : ℝ := (Fintype.card α : ℝ)
  have hK : 0 < K := Nat.cast_pos.2 Fintype.card_pos
  have hw0 (n : ℕ) (h : Hist Unit α ℝ n) (a : α) : 0 ≤ w (empMean' n h) a :=
    (mem_simplex_iff.1 (hw_mem _)).1 a
  have hw1 (n : ℕ) (h : Hist Unit α ℝ n) : ∑ a, w (empMean' n h) a = 1 :=
    (mem_simplex_iff.1 (hw_mem _)).2
  -- Uniformly near `{μ} × C` on the simplex, the cost of the alternatives exceeds `κ`, by
  -- compactness of `C`.
  obtain ⟨U, hU, η, hη, hUη⟩ :=
    hC_compact.exists_forall_mem_thickening_lt_of_lowerSemicontinuousWithinAt h_lsc hκ
  obtain ⟨B, hB, hCB⟩ := hC_compact.isBounded.exists_pos_norm_le
  -- Near `μ`, the targets are `ε`-close to `C`, the recommendation is `i` and the vectors are
  -- vectors of means of the families.
  set ε := η / 4
  have hε : 0 < ε := by positivity
  set W := {μ' | μ' ∈ U ∧ w μ' ∈ thickening ε C ∧ rec μ' = i ∧
    ∀ a, μ' a ∈ (ρ a).expFamilyMeans (T a)}
  have hW : W ∈ 𝓝 μ := by
    filter_upwards [hU, hw_tendsto (thickening_mem_nhdsSet C hε), hrec_eq, eventually_all.2 fun a ↦
      (continuous_apply a).continuousAt.preimage_mem_nhds
        (Measure.expFamilyMeans_mem_nhds (hT a) (hμ a))] with μ' h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨l, u, hlμ, hμu, h_box⟩ := exists_pi_Icc_subset_of_mem_nhds hW
  have hlu : l ≤ u := fun a ↦ ((hlμ a).trans (hμu a)).le
  have hlW := h_box (Set.left_mem_Icc.2 hlu)
  have huW := h_box (Set.right_mem_Icc.2 hlu)
  -- The good events: the empirical means stay in the box `∏ (l a, u a)` from round `t₀(T)` on,
  -- and the pull counts follow the cumulated targets.
  set E : ℕ → Set _ := fun T ↦ {ω |
    (∀ t ≥ roundsAfter T, ∀ a, empMean IT.action IT.feedback a t ω ∈ Set.Ioo (l a) (u a)) ∧
    ∀ (n : ℕ) a, |(pullCount IT.action a n ω : ℝ) -
      ∑ s ∈ range n, w (empMean' s (history IT.obs IT.action IT.feedback s ω)) a| ≤
        (K - 1) * (1 + √(n : ℝ))}
  have hE_sum : ∑' T, P (E T)ᶜ ≠ ∞ := by
    refine ne_top_of_le_ne_top (CTracking.tsum_measure_exists_ge_empMean_notMem_Ioo_ne_top hw0 hw1
      hseq hν_above hν_below hμ (fun a ↦ hlW.2.2.2 a) (fun a ↦ huW.2.2.2 a) hlμ hμu
      tendsto_sqrt_roundsAfter_div_log)
      (tsum_le_tsum fun T ↦ measure_mono_ae ?_)
    filter_upwards [CTracking.abs_pullCount_sub_sum_le_mul_one_add_sqrt hw0 hw1 hseq]
      with ω h_track hωE
    by_contra h_box
    push Not at h_box
    exact hωE ⟨h_box, h_track⟩
  -- The tracking error `(K - 1) (1 + √T)` is `o(T)`.
  have h_sqrt : Tendsto (fun T : ℕ ↦ (1 + √(T : ℝ)) / T) atTop (𝓝 0) :=
    tendsto_one_add_sqrt_div_atTop.comp tendsto_natCast_atTop_atTop
  -- From some round on, on the good event of round `T`, the GLR statistic is at least `κ T`.
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1
    ((eventually_roundsAfter_le (by positivity : 0 < η / (4 * (1 + B)))).and
    ((eventually_roundsAfter_le one_pos).and
    ((h_sqrt.eventually_le_const (by positivity : 0 < η / (4 * K))).and
    (eventually_gt_atTop 0))))
  have hE (T : ℕ) (hT : max n₀ T₁ ≤ T) (ω) (hω : ω ∈ E T) :
      κ * T ≤ task.glr (task.plugInCost empMean') T (history IT.obs IT.action IT.feedback T ω)
        (rec (empMean' T (history IT.obs IT.action IT.feedback T ω))) := by
    obtain ⟨hω_box, hω_track⟩ := hω
    obtain ⟨h_t₀, hT_le, h_sqrt_le, hT0⟩ := hT₁ T (le_of_max_le_right hT)
    have hT' : (0 : ℝ) < T := Nat.cast_pos.2 hT0
    refine task.mul_le_glr_plugInCost_of_mem_thickening (ε := ε) hw_mem hC_conv hCB hUη
      (fun k hk ↦ ?_) (hω_track T) (by exact_mod_cast hT_le.trans_eq (one_mul _)) hT0.ne' ?_
    · -- The empirical means at the rounds `k ≥ t₀(T)` are in `W`.
      have hk_box (b : α) :
          empMean' k (history IT.obs IT.action IT.feedback k ω) b ∈ Set.Ioo (l b) (u b) := by
        rw [← empMean_eq_empMean']
        exact hω_box k hk b
      exact (h_box ⟨fun b ↦ (hk_box b).1.le, fun b ↦ (hk_box b).2.le⟩).imp_right
        fun h ↦ ⟨h.1, h.2.1⟩
    · -- `(K - 1) (1 + √T) + (1 + B) t₀(T) + ε T ≤ 3 η T / 4 < η T`.
      rw [div_le_iff₀ hT'] at h_sqrt_le
      have h1 : (K - 1) * (1 + √(T : ℝ)) ≤ η / 4 * T := by
        have : (K - 1) * (1 + √(T : ℝ)) ≤ K * (1 + √(T : ℝ)) := by gcongr; linarith
        refine this.trans ?_
        calc K * (1 + √(T : ℝ)) ≤ K * (η / (4 * K) * T) := by gcongr
        _ = η / 4 * T := by field_simp
      have h2 : (1 + B) * roundsAfter T ≤ η / 4 * T := by
        calc (1 + B) * roundsAfter T ≤ (1 + B) * (η / (4 * (1 + B)) * T) := by gcongr
        _ = η / 4 * T := by field_simp
      have h3 : 0 < η * T := mul_pos hη hT'
      simp only [ε]
      linarith
  have h := task.eventually_expectedStoppingTime_glrt_le_of_isBigO (task.plugInCost empMean') alg
    (fun n h ↦ rec (empMean' n h)) hrec hstop hseq
    hE_sum hκc hE hr (T₀ := max n₀ T₁)
    (by filter_upwards [hβ] with δ hδ n hn h using hδ n (le_of_max_le_left hn) h)
  simpa only [cTrackAndStop_def] using h

/-- **Sample complexity of Track-and-Stop with C-tracking at the characteristic time**
[DK19, Theorem 7], the upper bound `𝔼[τ_δ] ≤ c log (1 / δ)` with `c > T*(μ)`, even when the
optimal allocations are not unique. Let the rewards of each arm `a` of the model `μ` be dominated
above and below by the member of mean `μ a` of a nondegenerate exponential family `(ρ a, T a)`,
let `i` be the single correct answer of `μ`, let `(μ', w') ↦ D(μ', w', ¬i)` be continuous at
every point `(μ, v)` with `v` in the simplex, on the allocations of the simplex, let the targets
`w` be allocations, and optimal allocations `w(μ') ∈ w*(μ', ¬i)` near `μ`, and let the
recommendation be `i` near `μ`. Then for thresholds `β δ n h ≤ log (r n / δ)` (for `n ≥ n₀`) with
`r n = O(n ^ p)`, Track-and-Stop with C-tracking and the empirical means as estimator satisfies
`𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every `c > T*(μ)`. Unlike D-tracking
(`IdentTask.eventually_expectedStoppingTime_trackAndStop_le_of_charTime_lt`), this does not need
`w` to be continuous at `μ`. -/
theorem eventually_expectedStoppingTime_cTrackAndStop_le_of_charTime_lt
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν_above : ∀ a, MGFDominatedAbove id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hν_below : ∀ a, MGFDominatedBelow id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hcorrect : task.correct μ = {i}) (hw_mem : ∀ μ', w μ' ∈ simplex α)
    (hw_opt : ∀ᶠ μ' in 𝓝 μ, w μ' ∈ task.optAlloc μ' i) (hrec_eq : ∀ᶠ μ' in 𝓝 μ, rec μ' = i)
    (h_cont : ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (μ, v))
    {c : ℝ≥0} (hc : task.charTime μ < c) (hr : r =O[atTop] fun n ↦ (n : ℝ) ^ p)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ n ≥ n₀, ∀ h, β δ n h ≤ ENNReal.ofReal (log (r n / δ))) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.cTrackAndStop empMean' w hw (β δ) rec hrec (hstop δ))
      (Environment.bandit (task.ν μ)) ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  -- On the optimal allocations, `D(μ, v, ¬i) = D(μ, ¬i) = T*(μ)⁻¹`.
  rw [task.charTime_eq_inv_answerValue hcorrect] at hc
  have hc' : (⨅ v ∈ task.optAlloc μ i, task.altCost μ v i)⁻¹ < c :=
    (ENNReal.inv_le_inv.2 (le_iInf₂ fun v hv ↦ (task.mem_optAlloc_iff.1 hv).2.ge)).trans_lt hc
  -- The optimal allocations form a compact set, to which the targets converge.
  have h_usc : UpperSemicontinuousOn (task.altCost μ · i) (simplex α) := fun v hv ↦
    ((h_cont v hv).comp (Continuous.prodMk_right μ).continuousWithinAt
      fun _ hv' ↦ ⟨Set.mem_univ _, hv'⟩).upperSemicontinuousWithinAt
  have h_uhc := task.upperHemicontinuousWithinAt_optAlloc (s := Set.univ) h_cont
  rw [upperHemicontinuousWithinAt_iff, nhdsWithin_univ] at h_uhc
  have hw_tendsto : Tendsto w (𝓝 μ) (𝓝ˢ (task.optAlloc μ i)) := fun t ht ↦ by
    rw [Filter.mem_map]
    filter_upwards [h_uhc t ht, hw_opt] with μ' h1 h2 using subset_of_mem_nhdsSet h1 h2
  exact task.eventually_expectedStoppingTime_cTrackAndStop_le hT hμ hν_above hν_below hw_mem
    (task.convex_optAlloc μ i) (task.isCompact_optAlloc h_usc) hw_tendsto hrec_eq
    (fun v hv ↦ (h_cont v (task.mem_optAlloc_iff.1 hv).1).lowerSemicontinuousWithinAt)
    hc' hr hβ

end LMLExplore.Identification.IdentTask

/-! ### Union-bound thresholds for Track-and-Stop with C-tracking -/

namespace LMLExplore.Identification.IdentTask

open Filter Topology

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {mℐ : MeasurableSpace ℐ} {task : IdentTask α (α → ℝ) ℐ ℝ}
  {w : (α → ℝ) → α → ℝ}
  {hw : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ w (empMean' n h)} {rec : (α → ℝ) → ℐ}
  {hrec : ∀ n, Measurable fun h : Hist Unit α ℝ n ↦ rec (empMean' n h)}
  {hstop : ∀ δ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
    (unionBoundLevel (Fintype.card α) δ) n <
      task.glr (task.plugInCost empMean') n h (rec (empMean' n h))}}
  {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ}
  {i : ℐ}

/-- **Sample complexity of Track-and-Stop with C-tracking with the union-bound thresholds**
[DK19, Theorem 7]. Under the assumptions of
`IdentTask.eventually_expectedStoppingTime_cTrackAndStop_le_of_charTime_lt` on the model `μ`,
Track-and-Stop with C-tracking and the thresholds `K log (2 n (n + 1)) + x_δ` satisfies
`𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every `c > T*(μ)`:
`limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ T*(μ)`. -/
theorem eventually_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_le
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν_above : ∀ a, MGFDominatedAbove id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hν_below : ∀ a, MGFDominatedBelow id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hcorrect : task.correct μ = {i}) (hw_mem : ∀ μ', w μ' ∈ simplex α)
    (hw_opt : ∀ᶠ μ' in 𝓝 μ, w μ' ∈ task.optAlloc μ' i) (hrec_eq : ∀ᶠ μ' in 𝓝 μ, rec μ' = i)
    (h_cont : ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (μ, v))
    {c : ℝ≥0} (hc : task.charTime μ < c) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.cTrackAndStop empMean' w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n)
      rec hrec (hstop δ)) (Environment.bandit (task.ν μ)) ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  refine eventually_le_mul_ofReal_log_of_rpow_inv (fun c' hc' s hs ↦ ?_) hc
  -- At the confidence level `δ ^ (1 / s)`, the thresholds are at most `log (r n / δ)` with
  -- `r n = (2 n (n + 1)) ^ K`.
  exact task.eventually_expectedStoppingTime_cTrackAndStop_le_of_charTime_lt (hw := hw)
    (hrec := hrec) (hstop := fun δ' ↦ hstop (δ' ^ s⁻¹)) hT hμ hν_above hν_below hcorrect hw_mem
    hw_opt hrec_eq h_cont hc' (isBigO_two_mul_mul_add_one_pow _)
    ((eventually_unionBoundThreshold_rpow_inv_le _ hs).mono fun _ h n hn _ ↦ h n hn)

/-- **Track-and-Stop with C-tracking and the union-bound thresholds stops almost surely**, with
the thresholds `K log (2 n (n + 1)) + x_δ` of every confidence level `δ ∈ (0, 1]`, on a model `μ`
with `T*(μ) < ∞` that satisfies the assumptions of
`IdentTask.eventually_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_le`. -/
theorem stopsAS_cTrackAndStop_unionBoundThreshold
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν_above : ∀ a, MGFDominatedAbove id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hν_below : ∀ a, MGFDominatedBelow id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hcorrect : task.correct μ = {i}) (hw_mem : ∀ μ', w μ' ∈ simplex α)
    (hw_opt : ∀ᶠ μ' in 𝓝 μ, w μ' ∈ task.optAlloc μ' i) (hrec_eq : ∀ᶠ μ' in 𝓝 μ, rec μ' = i)
    (h_cont : ∀ v ∈ simplex α, ContinuousWithinAt
      (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (μ, v))
    (h_charTime : task.charTime μ ≠ ∞) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    StopsAS (task.cTrackAndStop empMean' w hw
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n)
      rec hrec (hstop δ)) (Environment.bandit (task.ν μ)) := by
  have hc : task.charTime μ < (task.charTime μ).toNNReal + 1 := by
    rw [ENNReal.coe_toNNReal h_charTime]
    exact ENNReal.lt_add_right h_charTime one_ne_zero
  have h := eventually_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_le (hw := hw)
    (hrec := hrec) (hstop := hstop) hT hμ hν_above hν_below hcorrect hw_mem hw_opt hrec_eq h_cont hc
  simp only [cTrackAndStop_def] at h ⊢
  exact stopsAS_glrt_unionBoundThreshold (h.mono fun _ hδ' ↦ ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hδ').frequently hδ hδ1

end LMLExplore.Identification.IdentTask
