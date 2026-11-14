/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.CTracking
public import LMLExplore.Identification.DTracking
public import LMLExplore.Identification.GLR
public import LMLExplore.Identification.Task.Continuity
public import LMLExplore.Analysis.Convex.Normed
public import LMLExplore.Basic.ENNReal.Inv
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

**Sample complexity of the plug-in GLRT** [GK16, proof of Theorem 14]. The GLR statistic after
`T` rounds is `T D(θ̂_T, N(T) / T, ¬i)`. If `(θ', w) ↦ D(θ', w, ¬i)` is lower semicontinuous at
`(θ, w)` for every `w` in a compact set `W` of allocations, it is at least `κ T` for any
`κ < inf_{w ∈ W} D(θ, w, ¬i)` as soon as `θ̂_T` is close to `θ` and `N(T) / T` is close to `W`.
If, for all neighbourhoods of `θ` and of `W`, the estimates and the proportions of pulls are in
them on events whose complements have probabilities with a finite sum over `T`, the reduction
`IdentTask.eventually_expectedStoppingTime_glrt_le` of `Identification/GLR.lean` gives
`𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every
`c > (inf_{w ∈ W} D(θ, w, ¬i))⁻¹`. This holds for every task, every estimator and every sampling
rule, which enters only through the convergence of its allocations on these events.

**Sample complexity with D-tracking** [GK16, Theorem 14]. Let the true model `μ` have rewards
dominated by exponential families with means `μ a`, let the target map be continuous at `μ` and the
recommendation be `i` near `μ`. By the forced exploration of D-tracking, the empirical means stay
close to `μ` from round `t₀(T)` on, except on events whose probabilities have a finite sum over `T`
[GK16, Lemma 19]. On these events, the targets `w(μ̂)` stay close to `w(μ)` from round `t₀(T)` on,
so that the proportions of pulls `N(T) / T` are close to `w(μ)`. The reduction above with
`W = {w(μ)}` then gives, for thresholds `β δ n h ≤ log (r n / δ)` with `r n = O(n ^ p)`, the bound
`𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every `c > D(μ, w(μ), ¬i)⁻¹`, provided
`(μ', w') ↦ D(μ', w', ¬i)` is lower semicontinuous at `(μ, w(μ))`. When `w(μ)` is an
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
convex set are close to it: on the good events of forced exploration, the proportions of pulls
`N(T) / T` approach `w*(μ, ¬i)`. The reduction above with `W = w*(μ, ¬i)` then gives
`limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ T*(μ)` for Track-and-Stop with C-tracking, whatever the
selection of the optimal allocations. The two analyses share the step from forced exploration to
the good events, and differ only in how the proportions of pulls follow the targets.

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
* `IdentTask.exists_mem_nhds_mul_le_glr_plugInCost`: the GLR statistic of the plug-in statistic
  after `n` rounds is at least `κ n` when the estimate is close to `θ` and the proportions of pulls
  are close to `W`, for every `κ` below `D(θ, w, ¬i)` at all `w ∈ W`.
* `IdentTask.eventually_expectedStoppingTime_glrt_plugInCost_le`: **asymptotic sample complexity
  of the plug-in GLRT** [GK16, proof of Theorem 14], for every task, estimator and sampling rule
  whose allocations converge to `W` on good events: `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough
  `δ`, for every `c > (inf_{w ∈ W} D(θ, w, ¬i))⁻¹`, for thresholds at most `log (1 / δ) + f T`
  with `f T = o(T)`.
* `IdentTask.eventually_expectedStoppingTime_glrt_plugInCost_le_of_isBigO`: the same bound for
  thresholds at most `log (r T / δ)`, with `r T = O(T ^ p)`.
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
  converge to a convex compact set `C`, the reduction with `W = C`: `𝔼[τ_δ] ≤ c log (1 / δ)` for
  all small enough `δ`, for every `c > (inf_{v ∈ C} D(μ, v, ¬i))⁻¹`.
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

/-! ### Sample complexity of the plug-in GLRT -/

section SampleComplexity

open Metric

variable [TopologicalSpace Θ] {θ : Θ} {W : Set (α → ℝ)} {κ : ℝ≥0} {rec : Θ → ℐ}

/-- **Linear growth of the plug-in statistic near a model** [GK16, proof of Theorem 14]. Let `W`
be a compact set of allocations such that `(θ', w) ↦ D(θ', w, ¬i)` is lower semicontinuous at
`(θ, w)` on the allocations of the simplex for every `w ∈ W`, let `κ < D(θ, w, ¬i)` for every
`w ∈ W`, and let the recommendation be `i` near `θ`. Then there are a neighbourhood `U` of `θ` and
a neighbourhood `V` of `W` such that, after `n ≠ 0` rounds with history `h`, if the estimate
`θ̂ = est n h` is in `U` and the proportions of pulls `N / n` are in `V`, then the GLR statistic of
the recommendation `rec(θ̂)` is at least `κ n`. -/
lemma exists_mem_nhds_mul_le_glr_plugInCost (hW : IsCompact W)
    (h_lsc : ∀ w ∈ W, LowerSemicontinuousWithinAt
      (fun q : Θ × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (θ, w))
    (hκ : ∀ w ∈ W, (κ : ℝ≥0∞) < task.altCost θ w i) (hrec_eq : ∀ᶠ θ' in 𝓝 θ, rec θ' = i) :
    ∃ U ∈ 𝓝 θ, ∃ V ∈ 𝓝ˢ W, ∀ n ≠ 0, ∀ h : Hist Unit α 𝓨 n, est n h ∈ U →
      (fun a ↦ (pullCount' n h a : ℝ) / n) ∈ V →
        κ * n ≤ task.glr (task.plugInCost est) n h (rec (est n h)) := by
  -- Near `θ`, on the allocations of a thickening of `W`, the cost of the alternatives exceeds `κ`.
  obtain ⟨U, hU, η, hη, hUη⟩ := hW.exists_forall_mem_thickening_lt_of_lowerSemicontinuousWithinAt
    h_lsc hκ
  refine ⟨U ∩ {θ' | rec θ' = i}, inter_mem hU hrec_eq, thickening η W,
    thickening_mem_nhdsSet W hη, fun n hn h hθ hV ↦ ?_⟩
  rw [hθ.2, glr_plugInCost_eq_mul task est hn, mul_comm]
  exact mul_le_mul_right (hUη _ hθ.1 _ (pullCount'_div_mem_simplex _ hn) hV).le _

variable {mℐ : MeasurableSpace ℐ} (alg : Algorithm Unit α 𝓨)
  {hrec : ∀ n, Measurable fun h : Hist Unit α 𝓨 n ↦ rec (est n h)}
  {β : ℝ → (n : ℕ) → Hist Unit α 𝓨 n → ℝ≥0∞}
  {hstop : ∀ δ n, MeasurableSet
    {h | β δ n h < task.glr (task.plugInCost est) n h (rec (est n h))}}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨} {env : Environment Unit α 𝓨} {T₀ : ℕ}

/-- **Asymptotic sample complexity of the plug-in GLRT** [GK16, proof of Theorem 14], for every
task, every topological space of models, every estimator and every sampling rule. Let `W` be a
compact set of allocations such that `(θ', w) ↦ D(θ', w, ¬i)` is lower semicontinuous at `(θ, w)`
on the allocations of the simplex for every `w ∈ W`, and let the GLRT use the plug-in statistic of
the estimator `θ̂` and recommend `i` near `θ`, with thresholds `β δ T h ≤ log (1 / δ) + f T` for
every history `h`, `T ≥ T₀` and small `δ`, where `f T ≤ ε T` eventually for every `ε > 0`.
Suppose that the allocations converge on good events: along an algorithm-environment sequence of
the sampling rule in `env`, for all neighbourhoods `U` of `θ` and `V` of `W`, there are events
`E T` with `∑ T, P((E T)ᶜ) < ∞` on which, for all large `T`, the estimate `θ̂_T` is in `U` and the
proportions of pulls `N(T) / T` are in `V`. Then `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough
`δ`, for every `c > (inf_{w ∈ W} D(θ, w, ¬i))⁻¹`:
`limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ (inf_{w ∈ W} D(θ, w, ¬i))⁻¹`. -/
theorem eventually_expectedStoppingTime_glrt_plugInCost_le (hseq : IsAlgEnvSeq O X Y alg env P)
    (hW : IsCompact W)
    (h_lsc : ∀ w ∈ W, LowerSemicontinuousWithinAt
      (fun q : Θ × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (θ, w))
    (hrec_eq : ∀ᶠ θ' in 𝓝 θ, rec θ' = i)
    (h_conv : ∀ U ∈ 𝓝 θ, ∀ V ∈ 𝓝ˢ W, ∃ E : ℕ → Set Ω, ∑' T, P (E T)ᶜ ≠ ∞ ∧
      ∀ᶠ T in atTop, ∀ ω ∈ E T, est T (history O X Y T ω) ∈ U ∧
        (fun a ↦ (pullCount X a T ω : ℝ) / T) ∈ V)
    {c : ℝ≥0} (hc : (⨅ w ∈ W, task.altCost θ w i)⁻¹ < c)
    {f : ℕ → ℝ} (hf : ∀ ε > 0, ∀ᶠ T in atTop, f T ≤ ε * T)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ T ≥ T₀, ∀ h, β δ T h ≤ ENNReal.ofReal (log (1 / δ) + f T)) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.glrt (task.plugInCost est) alg (β δ)
      (fun n h ↦ rec (est n h)) hrec (hstop δ)) env ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  -- A rate `κ` with `c⁻¹ < κ < D(θ, w, ¬i)` for all `w ∈ W`, at which the GLR statistic grows on
  -- the good events of the neighbourhoods of `exists_mem_nhds_mul_le_glr_plugInCost`.
  obtain ⟨κ, hκ, hκc⟩ := ENNReal.exists_nnreal_lt_one_lt_mul_of_inv_lt hc
  obtain ⟨U, hU, V, hV, hUV⟩ := task.exists_mem_nhds_mul_le_glr_plugInCost est hW h_lsc
    (fun w hw ↦ hκ.trans_le (iInf₂_le w hw)) hrec_eq
  obtain ⟨E, hE_sum, hE⟩ := h_conv U hU V hV
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (hE.and (eventually_ne_atTop 0))
  refine task.eventually_expectedStoppingTime_glrt_le (task.plugInCost est) alg _ hrec hstop hseq
    hE_sum hκc (T₀ := max T₀ T₁) (fun T hT ω hω ↦ ?_) hf
    (by filter_upwards [hβ] with δ hδ T hT h using hδ T (le_of_max_le_left hT) h)
  obtain ⟨hTE, hT0⟩ := hT₁ T (le_of_max_le_right hT)
  obtain ⟨hθ, hN⟩ := hTE ω hω
  refine hUV T hT0 _ hθ ?_
  simpa only [pullCount_eq_pullCount' (O := O) (R' := Y)] using hN

/-- **Asymptotic sample complexity of the plug-in GLRT with thresholds `log (r T / δ)`**, for the
thresholds of [GK16, Theorem 14], `r T = O(T ^ p)`. Under the assumptions of
`IdentTask.eventually_expectedStoppingTime_glrt_plugInCost_le` on the task, the estimator and the
convergence of the allocations on good events, with thresholds `β δ T h ≤ log (r T / δ)` for every
history `h`, `T ≥ T₀` and small `δ`, `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every
`c > (inf_{w ∈ W} D(θ, w, ¬i))⁻¹`. -/
theorem eventually_expectedStoppingTime_glrt_plugInCost_le_of_isBigO
    (hseq : IsAlgEnvSeq O X Y alg env P) (hW : IsCompact W)
    (h_lsc : ∀ w ∈ W, LowerSemicontinuousWithinAt
      (fun q : Θ × (α → ℝ) ↦ task.altCost q.1 q.2 i) (Set.univ ×ˢ simplex α) (θ, w))
    (hrec_eq : ∀ᶠ θ' in 𝓝 θ, rec θ' = i)
    (h_conv : ∀ U ∈ 𝓝 θ, ∀ V ∈ 𝓝ˢ W, ∃ E : ℕ → Set Ω, ∑' T, P (E T)ᶜ ≠ ∞ ∧
      ∀ᶠ T in atTop, ∀ ω ∈ E T, est T (history O X Y T ω) ∈ U ∧
        (fun a ↦ (pullCount X a T ω : ℝ) / T) ∈ V)
    {c : ℝ≥0} (hc : (⨅ w ∈ W, task.altCost θ w i)⁻¹ < c)
    {r : ℕ → ℝ} {p : ℝ} (hr : r =O[atTop] fun T ↦ (T : ℝ) ^ p)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ T ≥ T₀, ∀ h, β δ T h ≤ ENNReal.ofReal (log (r T / δ))) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.glrt (task.plugInCost est) alg (β δ)
      (fun n h ↦ rec (est n h)) hrec (hstop δ)) env ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  refine task.eventually_expectedStoppingTime_glrt_plugInCost_le est alg hseq hW h_lsc hrec_eq
    h_conv hc (T₀ := T₀) (f := fun T ↦ log (r T))
    (fun ε hε ↦ eventually_log_le_mul_of_isBigO hr hε) ?_
  filter_upwards [hβ, Ioo_mem_nhdsGT one_pos] with δ hβδ hδ T hT h
  exact (hβδ T hT h).trans
    (ENNReal.ofReal_le_ofReal (log_div_le_log_one_div_add_log _ hδ.1 hδ.2.le))

end SampleComplexity

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

omit [Fintype α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The argument over the rounds shared by the analyses of Track-and-Stop with D-tracking and with
C-tracking [GK16, proof of Theorem 14]. Let `μ` be a vector of means of the nondegenerate
exponential families `(ρ a, T a)`, and let the sampling rule explore enough: for all vectors of
means `l < μ < u` of the families, the probabilities that the empirical mean of some arm `a` is
outside `(l a, u a)` at some round `t ≥ t₀ T` have a finite sum over `T` (forced exploration,
[GK16, Lemma 19]). Then for every neighbourhood `W` of `μ` and every property `G` of the runs that
holds almost surely, there are events `E T` with `∑ T, P((E T)ᶜ) < ∞` on which `G` holds and the
empirical means are in `W` at every round `k ≥ t₀ T`. -/
private lemma exists_tsum_measure_compl_ne_top_forall_ge_empMean'_mem [Finite α] {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
    {Y : ℕ → Ω → ℝ} {t₀ : ℕ → ℕ} (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (h_forced : ∀ l u : α → ℝ, (∀ a, l a ∈ (ρ a).expFamilyMeans (T a)) →
      (∀ a, u a ∈ (ρ a).expFamilyMeans (T a)) → (∀ a, l a < μ a) → (∀ a, μ a < u a) →
        ∑' T, P {ω | ∃ t ≥ t₀ T, ∃ a, empMean A Y a t ω ∉ Set.Ioo (l a) (u a)} ≠ ∞)
    {G : Ω → Prop} (hG : ∀ᵐ ω ∂P, G ω) {W : Set (α → ℝ)} (hW : W ∈ 𝓝 μ) :
    ∃ E : ℕ → Set Ω, ∑' T, P (E T)ᶜ ≠ ∞ ∧
      ∀ T, ∀ ω ∈ E T, G ω ∧ ∀ k ≥ t₀ T, empMean' k (history O A Y k ω) ∈ W := by
  -- A box `∏ [l a, u a]` around `μ` of vectors of means of the families, inside `W`.
  have hW' : W ∩ {μ' | ∀ a, μ' a ∈ (ρ a).expFamilyMeans (T a)} ∈ 𝓝 μ :=
    inter_mem hW (eventually_all.2 fun a ↦ (continuous_apply a).continuousAt.preimage_mem_nhds
      (Measure.expFamilyMeans_mem_nhds (hT a) (hμ a)))
  obtain ⟨l, u, hlμ, hμu, h_box⟩ := exists_pi_Icc_subset_of_mem_nhds hW'
  have hlu : l ≤ u := fun a ↦ ((hlμ a).trans (hμu a)).le
  -- The good events: `G` holds and the empirical means stay in the box from round `t₀ T` on.
  refine ⟨fun T ↦ {ω | G ω ∧ ∀ t ≥ t₀ T, ∀ a, empMean A Y a t ω ∈ Set.Ioo (l a) (u a)}, ?_, ?_⟩
  · refine ne_top_of_le_ne_top (h_forced l u (h_box (Set.left_mem_Icc.2 hlu)).2
      (h_box (Set.right_mem_Icc.2 hlu)).2 hlμ hμu) (tsum_le_tsum fun T ↦ measure_mono_ae ?_)
    filter_upwards [hG] with ω hGω hωE
    by_contra h_mem
    push Not at h_mem
    exact hωE ⟨hGω, h_mem⟩
  · rintro T ω ⟨hGω, hω⟩
    refine ⟨hGω, fun k hk ↦ (h_box ⟨fun b ↦ ?_, fun b ↦ ?_⟩).1⟩ <;> rw [← empMean_eq_empMean']
    exacts [(hω k hk b).1.le, (hω k hk b).2.le]

omit [MeasurableSingletonClass α] in
/-- The deterministic step of the analysis of Track-and-Stop [GK16, proof of Theorem 14]. Along a
sequence of arms following the D-tracking rule with targets `v k`, suppose that from round `t₀` on,
the targets are `ε`-close to the probability vector `l`. If `t₀ ≥ 1 / (4 ε²)`, `t₀ ≤ T`,
`t₀ ≤ 3 ε T` and `1 ≤ ε T`, then the proportions of pulls after `T` rounds are `3 K ε`-close
to `l`. -/
private lemma dist_pullCount_div_lt {Ω : Type*} {A : ℕ → Ω → α} {ω : Ω} {v : ℕ → α → ℝ}
    {l : α → ℝ} {ε η : ℝ} {t₀ T : ℕ} (hl : l ∈ simplex α) (hε : 0 < ε)
    (hεη : 3 * Fintype.card α * ε ≤ η) (hv : ∀ k ≥ t₀, dist (v k) l < ε)
    (hforced : ∀ (k : ℕ) a, (pullCount A a k ω : ℝ) < √(k : ℝ) - Fintype.card α / 2 →
      pullCount A (A k ω) k ω ≤ pullCount A a k ω)
    (htrack : ∀ k : ℕ, (∀ a, √(k : ℝ) - Fintype.card α / 2 ≤ pullCount A a k ω) → ∀ a,
      k * v k a - pullCount A a k ω ≤ k * v k (A k ω) - pullCount A (A k ω) k ω)
    (ht₀ : 1 / (4 * ε ^ 2) ≤ t₀) (hT : t₀ ≤ T) (ht₀T : (t₀ : ℝ) ≤ 3 * ε * T) (hεT : 1 ≤ ε * T) :
    dist (fun a ↦ (pullCount A a T ω : ℝ) / T) l < η := by
  have hv_close : ∀ k ≥ t₀, ∀ a, |v k a - l a| ≤ ε :=
    fun k hk a ↦ (Real.dist_eq _ _ ▸ (dist_pi_lt_iff hε).1 (hv k hk) a).le
  -- The exploration threshold `√k - K / 2` is below `2 ε k` from round `t₀` on.
  have hg (k : ℕ) (hk : t₀ ≤ k) : √(k : ℝ) - Fintype.card α / 2 ≤ 2 * ε * k := by
    have hk' : 1 / (4 * ε ^ 2) ≤ (k : ℝ) := ht₀.trans (Nat.cast_le.2 hk)
    rw [div_le_iff₀ (by positivity)] at hk'
    have hsq : √(k : ℝ) ≤ 2 * ε * k := by
      rw [sqrt_le_left (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    linarith [show (0 : ℝ) ≤ Fintype.card α / 2 by positivity]
  refine (dist_pi_lt_iff (hε.trans_le (le_mul_of_one_le_left hε.le ?_) |>.trans_le hεη)).2
    fun a ↦ ?_
  · have : (1 : ℝ) ≤ Fintype.card α := Nat.one_le_cast.2 Fintype.card_pos
    linarith
  have h := abs_pullCount_div_sub_le (mem_simplex_iff.1 hl).1 (mem_simplex_iff.1 hl).2
    (fun k _ ↦ hforced k) (fun k _ ↦ htrack k) hv_close hg hT ht₀T hεT a
  rw [Real.dist_eq]
  linarith

/-- **Sample complexity of Track-and-Stop** [GK16, Theorem 14]. Let the rewards of each arm `a` of
the model `μ` be dominated on `Set.univ` by the member of mean `μ a` of a nondegenerate
exponential family `(ρ a, T a)`. Let the target map `w` be continuous at `μ` with `w(μ)` a
probability vector, let the recommendation be `i` near `μ`, and let `(μ', w') ↦ D(μ', w', ¬i)` be
lower semicontinuous at `(μ, w(μ))` on the allocations of the simplex. Then for thresholds
`β δ n h ≤ log (r n / δ)` (for `n ≥ n₀`) with `r n = O(n ^ p)`, Track-and-Stop with the empirical
means as estimator satisfies `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every
`c > D(μ, w(μ), ¬i)⁻¹`. The constant does not depend on `p`, unlike in [GK16, Theorem 14], whose
bound for `r(t) = O(t ^ α)` has a factor `α ∈ [1, e / 2]`. -/
theorem eventually_expectedStoppingTime_trackAndStop_le (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hw_mem : w μ ∈ simplex α) (hw_cont : ContinuousAt w μ) (hrec_eq : ∀ᶠ μ' in 𝓝 μ, rec μ' = i)
    (h_lsc : LowerSemicontinuousWithinAt (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i)
      (Set.univ ×ˢ simplex α) (μ, w μ))
    {c : ℝ≥0} (hc : (task.altCost μ (w μ) i)⁻¹ < c)
    (hr : r =O[atTop] fun n ↦ (n : ℝ) ^ p)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ n ≥ n₀, ∀ h, β δ n h ≤ ENNReal.ofReal (log (r n / δ))) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.trackAndStop empMean' w hw (β δ) rec hrec (hstop δ))
      (Environment.bandit (task.ν μ)) ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  set alg := dTracking (fun n h ↦ w (empMean' n h)) hw
  set P := trajMeasure alg (Environment.bandit (task.ν μ))
  have hseq : IsAlgEnvSeq IT.obs IT.action IT.feedback alg (Environment.bandit (task.ν μ)) P :=
    IT.isAlgEnvSeq_trajMeasure alg _
  set K : ℝ := (Fintype.card α : ℝ)
  -- The reduction with `W = {w(μ)}`: it remains to show that the allocations converge on good
  -- events.
  have h := task.eventually_expectedStoppingTime_glrt_plugInCost_le_of_isBigO empMean' alg hseq
    (isCompact_singleton (x := w μ)) (fun v hv ↦ (Set.mem_singleton_iff.1 hv) ▸ h_lsc) hrec_eq
    ?_ (by rwa [iInf_singleton]) hr hβ (hrec := hrec) (hstop := hstop)
  · simpa only [trackAndStop_def] using h
  intro U hU V hV
  obtain ⟨η, hη, hηV⟩ := Metric.mem_nhds_iff.1 (nhdsSet_singleton (x := w μ) ▸ hV)
  set ε := η / (3 * K)
  have hε : 0 < ε := by positivity
  -- The good events: from round `t₀(T)` on, the empirical means are in `U` with targets `ε`-close
  -- to `w(μ)`, and the run follows the D-tracking rule.
  obtain ⟨E, hE_sum, hE⟩ := exists_tsum_measure_compl_ne_top_forall_ge_empMean'_mem
    (O := IT.obs) hT hμ (fun l u hl hu hlμ hμu ↦
      DTracking.tsum_measure_exists_ge_empMean_notMem_Ioo_ne_top hseq hν hμ hl hu hlμ hμu
        tendsto_sqrt_roundsAfter_div_log)
    ((DTracking.pullCount_action_le_of_lt hseq).and
      (DTracking.mul_sub_pullCount_le_of_forall_le hseq))
    (inter_mem hU (hw_cont (Metric.ball_mem_nhds _ hε)))
  refine ⟨E, hE_sum, ?_⟩
  -- For all large `T`, on the good event of round `T`, the empirical means after `T` rounds are
  -- in `U` and the proportions of pulls are `η`-close to `w(μ)`.
  filter_upwards [eventually_roundsAfter_le (by positivity : 0 < 3 * ε),
    eventually_roundsAfter_le one_pos,
    tendsto_roundsAfter.eventually_ge_atTop (1 / (4 * ε ^ 2)),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 / ε)]
    with T h3ε hT_le ht₀ hεT ω hω
  obtain ⟨⟨hω_forced, hω_track⟩, hω_W⟩ := hE T ω hω
  have hT_le' : roundsAfter T ≤ T := by exact_mod_cast hT_le.trans_eq (one_mul _)
  refine ⟨(hω_W T hT_le').1, hηV (Metric.mem_ball.2 ?_)⟩
  exact dist_pullCount_div_lt hw_mem hε (le_of_eq (by simp only [ε, K]; field_simp))
    (fun k hk ↦ (hω_W k hk).2) hω_forced hω_track ht₀ hT_le' h3ε
    (by rwa [div_le_iff₀' hε] at hεT)

/-- **Sample complexity of Track-and-Stop at the characteristic time** [GK16, Theorem 14], the
upper bound `𝔼[τ_δ] ≤ c log (1 / δ)` with `c > T*(μ)`. Let the rewards of each arm `a`
of the model `μ` be dominated on `Set.univ` by the member of mean `μ a` of a nondegenerate
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
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
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
  exact task.eventually_expectedStoppingTime_trackAndStop_le hT hμ hν
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
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
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
    (hrec := hrec) (hstop := fun δ' ↦ hstop (δ' ^ s⁻¹)) hT hμ hν hcorrect hw_opt
    hw_cont hrec_eq h_lsc hc' (isBigO_two_mul_mul_add_one_pow _)
    ((eventually_unionBoundThreshold_rpow_inv_le _ hs).mono fun _ h n hn _ ↦ h n hn)

/-- **Track-and-Stop with the union-bound thresholds stops almost surely**, with the thresholds
`K log (2 n (n + 1)) + x_δ` of every confidence level `δ ∈ (0, 1]`, on a model `μ` with
`T*(μ) < ∞` that satisfies the assumptions of
`IdentTask.eventually_expectedStoppingTime_trackAndStop_unionBoundThreshold_le`. -/
theorem stopsAS_trackAndStop_unionBoundThreshold
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
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
    (hrec := hrec) (hstop := hstop) hT hμ hν hcorrect hw_opt hw_cont hrec_eq h_lsc hc
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
proof of Theorem 7]. Along a sequence of arms whose pull counts follow the cumulated targets `v s`
up to `e` after `T` rounds, suppose that the targets are allocations, `ε`-close to the convex set
`C` from round `t₀` on. Since averages of points close to `C` are close to `C`
(`Convex.exists_mem_norm_sum_sub_smul_le`), if the elements of `C` have norm at most `B` and
`e + (1 + B) t₀ + ε T < η T`, then the proportions of pulls after `T` rounds are `η`-close to
`C`. -/
private lemma pullCount_div_mem_thickening {Ω : Type*} {A : ℕ → Ω → α} {ω : Ω}
    {v : ℕ → α → ℝ} {C : Set (α → ℝ)} {B e ε η : ℝ} {t₀ T : ℕ} (hv_mem : ∀ s, v s ∈ simplex α)
    (hC : Convex ℝ C) (hCB : ∀ c ∈ C, ‖c‖ ≤ B) (hv : ∀ k ≥ t₀, v k ∈ thickening ε C)
    (htrack : ∀ a, |(pullCount A a T ω : ℝ) - ∑ s ∈ range T, v s a| ≤ e) (hT : t₀ ≤ T)
    (hTη : e + (1 + B) * t₀ + ε * T < η * T) :
    (fun a ↦ (pullCount A a T ω : ℝ) / T) ∈ thickening η C := by
  obtain ⟨c₀, hc₀, hdc₀⟩ := mem_thickening_iff.1 (hv T hT)
  have hε : 0 < ε := dist_nonneg.trans_lt hdc₀
  have he : 0 ≤ e := (abs_nonneg _).trans (htrack (Classical.arbitrary α))
  -- At `T = 0` the condition `e < 0` on the tracking error fails.
  have hT' : (0 : ℝ) < T := by
    obtain rfl | hT0 := eq_or_ne T 0
    · obtain rfl := Nat.le_zero.1 hT
      norm_num at hTη
      linarith
    · exact Nat.cast_pos.2 (Nat.pos_of_ne_zero hT0)
  -- The targets are allocations, of norm at most `1`.
  have hv1 (s : ℕ) : ‖v s‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a ↦ ?_
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(mem_simplex_iff.1 (hv_mem s)).1 a], (simplex_subset_Icc (hv_mem s)).2 a⟩
  -- The average of the targets is close to a point `cbar` of the convex set `C`.
  obtain ⟨cbar, hcbar, h_avg⟩ := hC.exists_mem_norm_sum_sub_smul_le ⟨c₀, hc₀⟩ hT
    (fun s _ ↦ hv1 s) hCB fun s hs _ ↦ hv s hs
  have h_sum (a : α) : |∑ s ∈ range T, v s a - T * cbar a| ≤ (1 + B) * t₀ + ε * (T - t₀) := by
    have h := (norm_le_pi_norm (∑ s ∈ range T, v s - (T : ℝ) • cbar) a).trans h_avg
    simpa only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
      using h
  -- The proportions of pulls are `η`-close to `cbar`.
  have hq_dist (a : α) : |(pullCount A a T ω : ℝ) / T - cbar a| < η := by
    have h_eq : (pullCount A a T ω : ℝ) / T - cbar a = ((pullCount A a T ω - ∑ s ∈ range T, v s a)
        + (∑ s ∈ range T, v s a - T * cbar a)) / T := by
      field_simp
      ring
    rw [h_eq, abs_div, abs_of_pos hT', div_lt_iff₀ hT']
    linarith [abs_add_le (pullCount A a T ω - ∑ s ∈ range T, v s a)
      (∑ s ∈ range T, v s a - T * cbar a), htrack a, h_sum a,
      mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) t₀)]
  have hη : 0 < η := (abs_nonneg _).trans_lt (hq_dist (Classical.arbitrary α))
  exact mem_thickening_iff.2
    ⟨cbar, hcbar, (dist_pi_lt_iff hη).2 fun a ↦ Real.dist_eq _ _ ▸ hq_dist a⟩

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ}
  {β : ℝ → (n : ℕ) → Hist Unit α ℝ n → ℝ≥0∞}
  {hstop : ∀ δ n, MeasurableSet
    {h | β δ n h < task.glr (task.plugInCost empMean') n h (rec (empMean' n h))}}
  {r : ℕ → ℝ} {p : ℝ} {n₀ : ℕ}

/-- **Sample complexity of Track-and-Stop with C-tracking** [DK19, Lemma 6 and Theorem 7]. Let the
rewards of each arm `a` of the model `μ` be dominated on `Set.univ` by the member of mean `μ a`
of a nondegenerate exponential family `(ρ a, T a)`. Let the targets `w` be allocations that
converge at `μ` to a convex compact set `C` (they eventually lie in every neighbourhood of `C`),
let the recommendation be `i` near `μ`, and let `(μ', w') ↦ D(μ', w', ¬i)` be lower
semicontinuous at every point of `{μ} × C` on the allocations of the simplex. Then for thresholds
`β δ n h ≤ log (r n / δ)` (for `n ≥ n₀`) with `r n = O(n ^ p)`, Track-and-Stop with C-tracking and
the empirical means as estimator satisfies `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for
every `c > (inf_{v ∈ C} D(μ, v, ¬i))⁻¹`. -/
theorem eventually_expectedStoppingTime_cTrackAndStop_le (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
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
  -- The reduction with `W = C`: it remains to show that the allocations converge to `C` on good
  -- events.
  have h := task.eventually_expectedStoppingTime_glrt_plugInCost_le_of_isBigO empMean' alg hseq
    hC_compact h_lsc hrec_eq ?_ hc hr hβ (hrec := hrec) (hstop := hstop)
  · simpa only [cTrackAndStop_def] using h
  intro U hU V hV
  obtain ⟨η, hη, hηV⟩ := (hasBasis_nhdsSet_thickening hC_compact).mem_iff.1 hV
  obtain ⟨B, hB, hCB⟩ := hC_compact.isBounded.exists_pos_norm_le
  set ε := η / 4
  have hε : 0 < ε := by positivity
  -- The good events: from round `t₀(T)` on, the empirical means are in `U` with targets
  -- `ε`-close to `C`, and the pull counts follow the cumulated targets.
  obtain ⟨E, hE_sum, hE⟩ := exists_tsum_measure_compl_ne_top_forall_ge_empMean'_mem
    (O := IT.obs) hT hμ (fun l u hl hu hlμ hμu ↦
      CTracking.tsum_measure_exists_ge_empMean_notMem_Ioo_ne_top hw0 hw1 hseq hν hμ hl hu hlμ hμu
        tendsto_sqrt_roundsAfter_div_log)
    (CTracking.abs_pullCount_sub_sum_le_mul_one_add_sqrt hw0 hw1 hseq)
    (inter_mem hU (hw_tendsto (thickening_mem_nhdsSet C hε)))
  refine ⟨E, hE_sum, ?_⟩
  -- The tracking error `(K - 1) (1 + √T)` is `o(T)`.
  have h_sqrt : Tendsto (fun T : ℕ ↦ (1 + √(T : ℝ)) / T) atTop (𝓝 0) :=
    tendsto_one_add_sqrt_div_atTop.comp tendsto_natCast_atTop_atTop
  -- For all large `T`, on the good event of round `T`, the empirical means after `T` rounds are
  -- in `U` and the proportions of pulls are `η`-close to `C`.
  filter_upwards [eventually_roundsAfter_le (by positivity : 0 < η / (4 * (1 + B))),
    eventually_roundsAfter_le one_pos,
    h_sqrt.eventually_le_const (by positivity : 0 < η / (4 * K)), eventually_gt_atTop 0]
    with T h_t₀ hT_le h_sqrt_le hT0 ω hω
  obtain ⟨hω_track, hω_W⟩ := hE T ω hω
  have hT_le' : roundsAfter T ≤ T := by exact_mod_cast hT_le.trans_eq (one_mul _)
  have hT' : (0 : ℝ) < T := Nat.cast_pos.2 hT0
  refine ⟨(hω_W T hT_le').1, hηV (pullCount_div_mem_thickening (fun _ ↦ hw_mem _) hC_conv hCB
    (fun k hk ↦ (hω_W k hk).2) (hω_track T) hT_le' ?_)⟩
  -- `(K - 1) (1 + √T) + (1 + B) t₀(T) + ε T ≤ 3 η T / 4 < η T`.
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

/-- **Sample complexity of Track-and-Stop with C-tracking at the characteristic time**
[DK19, Theorem 7], the upper bound `𝔼[τ_δ] ≤ c log (1 / δ)` with `c > T*(μ)`, even when the
optimal allocations are not unique. Let the rewards of each arm `a` of the model `μ` be dominated
on `Set.univ` by the member of mean `μ a` of a nondegenerate exponential family `(ρ a, T a)`,
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
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
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
  exact task.eventually_expectedStoppingTime_cTrackAndStop_le hT hμ hν hw_mem
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
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
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
    (hrec := hrec) (hstop := fun δ' ↦ hstop (δ' ^ s⁻¹)) hT hμ hν hcorrect hw_mem
    hw_opt hrec_eq h_cont hc' (isBigO_two_mul_mul_add_one_pow _)
    ((eventually_unionBoundThreshold_rpow_inv_le _ hs).mono fun _ h n hn _ ↦ h n hn)

/-- **Track-and-Stop with C-tracking and the union-bound thresholds stops almost surely**, with
the thresholds `K log (2 n (n + 1)) + x_δ` of every confidence level `δ ∈ (0, 1]`, on a model `μ`
with `T*(μ) < ∞` that satisfies the assumptions of
`IdentTask.eventually_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_le`. -/
theorem stopsAS_cTrackAndStop_unionBoundThreshold
    (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
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
    (hrec := hrec) (hstop := hstop) hT hμ hν hcorrect hw_mem hw_opt hrec_eq h_cont hc
  simp only [cTrackAndStop_def] at h ⊢
  exact stopsAS_glrt_unionBoundThreshold (h.mono fun _ hδ' ↦ ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hδ').frequently hδ hδ1

end LMLExplore.Identification.IdentTask
