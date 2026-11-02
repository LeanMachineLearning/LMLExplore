/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.DTracking
public import LMLExplore.Identification.GLR

/-!
# Track-and-Stop with D-tracking

Track-and-Stop [GK16] is the fixed-confidence identification algorithm that samples the arms so
that their proportions of pulls follow an optimal allocation at the current estimate of the model,
and stops with the generalized likelihood ratio test. For an identification task whose models are
vectors of means `μ : α → ℝ` (the arms have real observations), after `n` rounds with history `h`,
with pull counts `N_a` and empirical means `μ̂ = μ̂(h)`, it
* samples with the D-tracking rule of `Identification/DTracking.lean`, whose target is
  `w(μ̂)` for a target map `w`, typically a selection of the optimal allocations `w*(μ̂, ¬i)`;
* recommends the answer `rec(μ̂)`, typically the correct answer of `μ̂`;
* stops when the GLR statistic
  `GLR_n(h, ¬rec(μ̂)) = inf_{λ ∈ ¬rec(μ̂)} ∑ a, N_a KL(ν_a(μ̂), ν_a(λ))` exceeds a threshold `β n`.

The GLR statistic is the transportation cost of the empirical model with the pull counts as
allocation, `GLR_n(h, ¬i) = D(μ̂, N, ¬i) = n D(μ̂, N / n, ¬i)`.

**Sample complexity** [GK16, Theorem 14]. Let the true model `μ` have rewards dominated by
exponential families with means `μ a`, let the target map be continuous at `μ` and the
recommendation be `i` near `μ`. By the forced exploration of D-tracking, the empirical means stay
close to `μ` from round `t₀(T)` on, except on events whose probabilities have a finite sum over `T`
[GK16, Lemma 19]. On these events, the targets `w(μ̂)` stay close to `w(μ)` from round `t₀(T)` on,
so that the proportions of pulls `N(T) / T` are close to `w(μ)`, and the GLR statistic after `T`
rounds is `T D(μ̂(T), N(T) / T, ¬i) ≥ κ T` for any `κ < D(μ, w(μ), ¬i)`, provided
`(μ', w') ↦ D(μ', w', ¬i)` is lower semicontinuous at `(μ, w(μ))`. The generic reduction
`IdentTask.eventually_expectedStoppingTime_glrt_le_of_isBigO` then gives, for thresholds
`β δ n ≤ log (r n / δ)` with `r n = O(n ^ p)`, the bound `𝔼[τ_δ] ≤ c log (1 / δ)` for all small
enough `δ`, for every `c > 1 / κ`. When `w(μ)` is an optimal allocation for the single correct
answer `i` of `μ`, `D(μ, w(μ), ¬i) = T*(μ)⁻¹` and the sample complexity of Track-and-Stop is at
most the characteristic time: `limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ T*(μ)`. This upper bound
holds for all such thresholds, including ones that are not `δ`-correct, such as `β = 0`.
Asymptotic optimality, that is, matching the lower bound `𝔼[τ_δ] ≥ T*(μ) kl(δ, 1 - δ)` of
`Identification/LowerBound.lean`, also needs the `δ`-correctness of the thresholds, which is not
proved here.

## Main definitions

* `IdentTask.empCost task n h λ`: the statistic `∑ a, N_a KL(ν_a(μ̂), ν_a(λ))` of the history `h`
  of the first `n` rounds against the model `λ`, the transportation cost from the empirical model
  `μ̂` with the pull counts `N` as allocation.
* `IdentTask.trackAndStop task w hw β rec hrec hstop`: Track-and-Stop with D-tracking of the
  targets `w(μ̂)`, recommendation `rec(μ̂)` and GLR stopping with thresholds `β`.

## Main statements

* `IdentTask.glr_empCost`, `IdentTask.glr_empCost_eq_mul`: the GLR statistic of the empirical
  costs is `D(μ̂, N, ¬i) = n D(μ̂, N / n, ¬i)`.
* `IdentTask.eventually_expectedStoppingTime_trackAndStop_le`: [GK16, Theorem 14] with the rate
  `κ < D(μ, w(μ), ¬i)`: `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every `c > 1 / κ`.
* `IdentTask.eventually_expectedStoppingTime_trackAndStop_le_of_charTime_lt`: **sample complexity
  at the characteristic time** [GK16, Theorem 14]: if `w(μ)` is an optimal allocation for the
  single correct answer `i` of `μ`, then `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for
  every `c > T*(μ)`. The `δ`-correctness of the thresholds, which turns this upper bound into
  asymptotic optimality, is not established here.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Section 3 and Theorem 14.
-/

public section

open MeasureTheory ProbabilityTheory Learning Filter Real
open scoped Topology ENNReal NNReal

namespace LMLExplore.Identification.IdentTask

variable {α ℐ : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  (task : IdentTask α (α → ℝ) ℐ ℝ) {n : ℕ} {h : Hist Unit α ℝ n} {i : ℐ}

/-! ### The GLR statistic of the empirical model -/

/-- The statistic `∑ a, N_a KL(ν_a(μ̂), ν_a(λ))` of the history `h` of the first `n` rounds against
the model `λ`, with `N_a` the number of pulls of the arm `a` and `μ̂` the vector of empirical means
of `h`: the transportation cost from the empirical model `μ̂` to `λ` with the pull counts as
allocation. When the arm laws of the models are the members of exponential families with
divergence `d`, indexed by their means, and `μ̂` and `λ` are vectors of means of the families, it
is `∑ a, N_a d(μ̂_a, λ_a)`, the log-likelihood ratio of the maximum-likelihood model against `λ`. -/
noncomputable def empCost (n : ℕ) (h : Hist Unit α ℝ n) (θ' : α → ℝ) : ℝ≥0∞ :=
  task.cost (fun a ↦ (pullCount' n h a : ℝ)) (empMean' n h) θ'

lemma empCost_def (n : ℕ) (h : Hist Unit α ℝ n) (θ' : α → ℝ) :
    task.empCost n h θ' = task.cost (fun a ↦ (pullCount' n h a : ℝ)) (empMean' n h) θ' := (rfl)

/-- The GLR statistic of the empirical costs is the cost `D(μ̂, N, ¬i)` of the alternatives to `i`
from the empirical model `μ̂` with the pull counts `N` as allocation. -/
lemma glr_empCost :
    task.glr task.empCost n h i = task.altCost (empMean' n h) (fun a ↦ (pullCount' n h a : ℝ)) i :=
  task.glr_eq_altCost fun _ _ ↦ task.empCost_def n h _

/-- After `n ≠ 0` rounds, the GLR statistic of the empirical costs is `n D(μ̂, N / n, ¬i)`, with the
proportions of pulls `N / n` as allocation. -/
lemma glr_empCost_eq_mul (hn : n ≠ 0) :
    task.glr task.empCost n h i =
      n * task.altCost (empMean' n h) (fun a ↦ (pullCount' n h a : ℝ) / n) i := by
  have hn' : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h_smul :
      (fun a ↦ (pullCount' n h a : ℝ)) = (n : ℝ≥0) • fun a ↦ (pullCount' n h a : ℝ) / n := by
    ext a
    simp [NNReal.smul_def, field]
  rw [glr_empCost, h_smul, task.altCost_smul hn', ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_natCast]

/-! ### Track-and-Stop -/

variable [Nonempty α] [MeasurableSingletonClass α] {mℐ : MeasurableSpace ℐ}

/-- **Track-and-Stop** with D-tracking [GK16, Section 3]: the GLRT of the task with the empirical
costs `IdentTask.empCost` as statistic, thresholds `β`, the recommendation `rec(μ̂)` and the
D-tracking sampling rule with targets `w(μ̂)`, where `μ̂` is the vector of empirical means of the
history. After `n` rounds with history `h`, it stops if `β n < GLR_n(h, ¬rec(μ̂))` and then answers
`rec(μ̂)`. The target map `w` is typically a selection of the optimal allocations
`w*(μ̂, ¬rec(μ̂))`, and `rec(μ̂)` a correct answer of `μ̂`. -/
noncomputable def trackAndStop (w : (α → ℝ) → α → ℝ) (hw : Measurable w) (β : ℕ → ℝ≥0∞)
    (rec : (α → ℝ) → ℐ) (hrec : Measurable rec)
    (hstop : ∀ n, MeasurableSet {h | β n < task.glr task.empCost n h (rec (empMean' n h))}) :
    IdentAlg Unit α ℝ ℐ :=
  task.glrt task.empCost
    (dTracking (fun n h ↦ w (empMean' n h)) fun n ↦ hw.comp (by fun_prop)) β
    (fun n h ↦ rec (empMean' n h)) (fun n ↦ hrec.comp (by fun_prop)) hstop

variable {w : (α → ℝ) → α → ℝ} {hw : Measurable w} {β : ℕ → ℝ≥0∞} {rec : (α → ℝ) → ℐ}
  {hrec : Measurable rec}
  {hstop : ∀ n, MeasurableSet {h | β n < task.glr task.empCost n h (rec (empMean' n h))}}

lemma trackAndStop_def : task.trackAndStop w hw β rec hrec hstop = task.glrt task.empCost
    (dTracking (fun n h ↦ w (empMean' n h)) fun n ↦ hw.comp (by fun_prop)) β
    (fun n h ↦ rec (empMean' n h)) (fun n ↦ hrec.comp (by fun_prop)) hstop := (rfl)

/-- The sampling rule of Track-and-Stop is D-tracking of the targets `w(μ̂)`. -/
@[simp]
lemma alg_trackAndStop : (task.trackAndStop w hw β rec hrec hstop).alg =
    dTracking (fun n h ↦ w (empMean' n h)) fun n ↦ hw.comp (by fun_prop) := by
  rw [trackAndStop_def, alg_glrt]

/-- Track-and-Stop stops after the history `h` of the first `n` rounds iff the GLR statistic of
the recommendation `rec(μ̂)` exceeds the threshold `β n`. -/
@[simp]
lemma mem_stopSet_trackAndStop {h : Σ n, Hist Unit α ℝ n} :
    h ∈ (task.trackAndStop w hw β rec hrec hstop).stopSet ↔
      β h.1 < task.glr task.empCost h.1 h.2 (rec (empMean' h.1 h.2)) := by
  rw [trackAndStop_def, mem_stopSet_glrt]

/-- Track-and-Stop answers the recommendation `rec(μ̂)` of the empirical means. -/
@[simp]
lemma output_trackAndStop (h : Σ n, Hist Unit α ℝ n) :
    (task.trackAndStop w hw β rec hrec hstop).output h =
      Measure.dirac (rec (empMean' h.1 h.2)) := by
  rw [trackAndStop_def, output_glrt]

/-! ### Sample complexity -/

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
  {β : ℝ → ℕ → ℝ≥0∞}
  {hstop : ∀ δ n, MeasurableSet {h | β δ n < task.glr task.empCost n h (rec (empMean' n h))}}
  {r : ℕ → ℝ} {p : ℝ} {n₀ : ℕ}

omit [MeasurableSingletonClass α] in
/-- The deterministic step of the analysis of Track-and-Stop [GK16, proof of Theorem 14]. Along a
sequence of arms following the D-tracking rule with targets `w(μ̂(k))`, suppose that from round `t₀`
on, the empirical means `μ̂(k)` lie in a set `U` on which the cost of the alternatives to `i`
exceeds `κ` at every allocation of the simplex `η`-close to `w(μ)`, the targets `w(μ̂(k))` are
`ε`-close to `w(μ)` with `3 K ε ≤ η`, and the recommendation is `i`. If `t₀ ≥ 1 / (4 ε²)`,
`t₀ ≤ T`, `t₀ ≤ 3 ε T` and `1 ≤ ε T`, then the GLR statistic of the recommendation after `T`
rounds is at least `κ T`. -/
private lemma mul_le_glr_empCost {Ω : Type*} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
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
    κ * T ≤ task.glr task.empCost T (history O A Y T ω) (rec (empMean' T (history O A Y T ω))) := by
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
  rw [hrec', glr_empCost_eq_mul task hT0, mul_comm]
  exact mul_le_mul_right (hU _ hU' q hq hq_dist).le _

/-- **Sample complexity of Track-and-Stop** [GK16, Theorem 14], with the rate
`κ < D(μ, w(μ), ¬i)`. Let the rewards of each arm `a` of the model `μ` be dominated above and below
by the member of mean `μ a` of a nondegenerate exponential family `(ρ a, T a)`. Let the target map
`w` be continuous at `μ` with `w(μ)` a probability vector, let the recommendation be `i` near `μ`,
and let `(μ', w') ↦ D(μ', w', ¬i)` be lower semicontinuous at `(μ, w(μ))` on the allocations of the
simplex. Then for thresholds `β δ n ≤ log (r n / δ)` (for `n ≥ n₀`) with `r n = O(n ^ p)`,
Track-and-Stop satisfies `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every `c` with
`1 < κ c`. -/
theorem eventually_expectedStoppingTime_trackAndStop_le (hT : ∀ a c, ¬ T a =ᵐ[ρ a] fun _ ↦ c)
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν_above : ∀ a, MGFDominatedAbove id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hν_below : ∀ a, MGFDominatedBelow id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hw_mem : w μ ∈ simplex α) (hw_cont : ContinuousAt w μ) (hrec_eq : ∀ᶠ μ' in 𝓝 μ, rec μ' = i)
    (h_lsc : LowerSemicontinuousWithinAt (fun q : (α → ℝ) × (α → ℝ) ↦ task.altCost q.1 q.2 i)
      (Set.univ ×ˢ simplex α) (μ, w μ))
    {κ c : ℝ≥0} (hκ : κ < task.altCost μ (w μ) i) (hκc : 1 < κ * c)
    (hr : r =O[atTop] fun n ↦ (n : ℝ) ^ p)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ n ≥ n₀, β δ n ≤ ENNReal.ofReal (log (r n / δ))) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.trackAndStop w hw (β δ) rec hrec (hstop δ))
      (stationaryEnv (task.ν μ)) ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  set alg := dTracking (fun n h ↦ w (empMean' n h)) fun n ↦ hw.comp (by fun_prop)
  set P := trajMeasure alg (stationaryEnv (task.ν μ))
  have hseq : IsAlgEnvSeq IT.obs IT.action IT.feedback alg (stationaryEnv (task.ν μ)) P :=
    IT.isAlgEnvSeq_trajMeasure alg _
  set K : ℝ := (Fintype.card α : ℝ)
  -- Near `(μ, w(μ))` on the simplex, the cost of the alternatives exceeds `κ`.
  obtain ⟨U, hU, η, hη, hUη⟩ : ∃ U ∈ 𝓝 μ, ∃ η > 0, ∀ μ' ∈ U, ∀ w' ∈ simplex α,
      dist w' (w μ) < η → (κ : ℝ≥0∞) < task.altCost μ' w' i := by
    have h := h_lsc κ hκ
    rw [nhdsWithin_prod_eq, nhdsWithin_univ] at h
    obtain ⟨pa, hpa, pb, hpb, hp⟩ := eventually_prod_iff.1 h
    obtain ⟨η, hη, hηb⟩ := Metric.mem_nhdsWithin_iff.1 hpb
    exact ⟨{x | pa x}, hpa, η, hη, fun μ' hμ' w' hw' hd ↦ hp hμ' (hηb ⟨Metric.mem_ball.2 hd, hw'⟩)⟩
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
  obtain ⟨R, hR, hRW⟩ := Metric.mem_nhds_iff.1 hW
  have h_ball (μ' : α → ℝ) (hμ' : ∀ b, |μ' b - μ b| < R) : μ' ∈ W :=
    hRW <| (Metric.mem_ball.trans (dist_pi_lt_iff hR)).2 fun b ↦ Real.dist_eq _ _ ▸ hμ' b
  set l : α → ℝ := fun a ↦ μ a - R / 2
  set u : α → ℝ := fun a ↦ μ a + R / 2
  have hl a : l a ∈ (ρ a).expFamilyMeans (T a) :=
    (h_ball l fun b ↦ abs_sub_lt_iff.2 ⟨by simp only [l]; linarith,
      by simp only [l]; linarith⟩).2.2.2 a
  have hu a : u a ∈ (ρ a).expFamilyMeans (T a) :=
    (h_ball u fun b ↦ abs_sub_lt_iff.2 ⟨by simp only [u]; linarith,
      by simp only [u]; linarith⟩).2.2.2 a
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
      hν_above hν_below hμ hl hu (fun a ↦ by simp only [l]; linarith)
      (fun a ↦ by simp only [u]; linarith) tendsto_sqrt_roundsAfter_div_log)
      (ENNReal.tsum_le_tsum fun T ↦ measure_mono_ae ?_)
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
      κ * T ≤ task.glr task.empCost T (history IT.obs IT.action IT.feedback T ω)
        (rec (empMean' T (history IT.obs IT.action IT.feedback T ω))) := by
    obtain ⟨hω_box, hω_forced, hω_track⟩ := hω
    obtain ⟨h3ε, hT_le, ht₀, hεT⟩ := hT₁ T (le_of_max_le_right hT)
    refine task.mul_le_glr_empCost hw_mem hε (le_of_eq (by simp only [ε, K]; field_simp)) hUη
      (fun k hk ↦ ?_) hω_forced hω_track ht₀ (by exact_mod_cast hT_le.trans_eq (one_mul _)) h3ε
      (by rwa [div_le_iff₀' hε] at hεT)
    -- The empirical means at the rounds `k ≥ t₀(T)` are in `W`.
    refine (h_ball _ fun b ↦ ?_).imp_right fun h ↦ ⟨h.1, h.2.1⟩
    rw [← empMean_eq_empMean']
    obtain ⟨h1, h2⟩ := hω_box k hk b
    simp only [l, u] at h1 h2
    exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have h := task.eventually_expectedStoppingTime_glrt_le_of_isBigO task.empCost alg
    (fun n h ↦ rec (empMean' n h)) (fun n ↦ hrec.comp (by fun_prop)) hstop hseq
    hE_sum hκc hE hr (T₀ := max n₀ T₁)
    (by filter_upwards [hβ] with δ hδ n hn using hδ n (le_of_max_le_left hn))
  simpa only [trackAndStop_def] using h

/-- **Sample complexity of Track-and-Stop at the characteristic time** [GK16, Theorem 14], the
upper bound `𝔼[τ_δ] ≤ c log (1 / δ)` with `c > T*(μ)`. Let the rewards of each arm `a`
of the model `μ` be dominated above and below by the member of mean `μ a` of a nondegenerate
exponential family `(ρ a, T a)`, let `i` be the single correct answer of `μ`, let the target map
`w` be continuous at `μ` with `w(μ)` an optimal allocation `w*(μ, ¬i)`, let the recommendation be
`i` near `μ`, and let `(μ', w') ↦ D(μ', w', ¬i)` be lower semicontinuous at `(μ, w(μ))` on the
allocations of the simplex. Then for thresholds `β δ n ≤ log (r n / δ)` (for `n ≥ n₀`) with
`r n = O(n ^ p)`, Track-and-Stop satisfies `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for
every `c > T*(μ)`: `limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ T*(μ)`. This is asymptotic optimality
only for `δ`-correct thresholds, whose correctness is not proved here. -/
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
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ n ≥ n₀, β δ n ≤ ENNReal.ofReal (log (r n / δ))) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.trackAndStop w hw (β δ) rec hrec (hstop δ))
      (stationaryEnv (task.ν μ)) ≤ c * ENNReal.ofReal (log (1 / δ)) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact not_lt_zero (ENNReal.coe_zero ▸ hc)
  -- Choose a rate `κ` with `c⁻¹ < κ < D(μ, w(μ), ¬i) = T*(μ)⁻¹`.
  rw [task.charTime_eq_inv_answerValue hcorrect, ENNReal.inv_lt_iff_inv_lt,
    ← (task.mem_optAlloc_iff.1 hw_opt).2, ← ENNReal.coe_inv hc0] at hc
  obtain ⟨κ, hcκ, hκ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hc
  have hκc : 1 < κ * c := by
    rw [← inv_mul_cancel₀ hc0]
    exact mul_lt_mul_of_pos_right (ENNReal.coe_lt_coe.1 hcκ) (pos_iff_ne_zero.2 hc0)
  exact task.eventually_expectedStoppingTime_trackAndStop_le hT hμ hν_above hν_below
    (task.mem_optAlloc_iff.1 hw_opt).1 hw_cont hrec_eq h_lsc hκ hκc hr hβ

end LMLExplore.Identification.IdentTask
