/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Log.Basic
public import LMLExplore.Bandits.IndexAlgorithm
public import LMLExplore.Identification.ForcedExploration
public import LMLExplore.Identification.Tracking

/-!
# The C-tracking sampling rule

The C-tracking rule of Garivier and Kaufmann (2016) follows a sequence of target allocations
computed from the data, typically the optimal allocations `w*(μ̂(t))` at the empirical means in
Track-and-Stop, through their cumulated sums. To force the exploration of every arm, each target
`w(s)` is first mixed with the uniform allocation into the target `w^{ε_s}(s)`, which gives at
least `ε_s = 1 / (2 √(K² + s))` to every arm (`cTrackingTarget`, `cTrackingRate`). With `N_a(t)`
the number of pulls of arm `a` in the first `t` rounds and `K` the number of arms, at round `t` it
plays an arm maximizing `∑_{s ≤ t} w^{ε_s}_a(s) - N_a(t)`, where `w(s)` is the target computed
from the history of the first `s` rounds.

Unlike D-tracking (`LMLExplore/Identification/DTracking.lean`), whose proportions of pulls follow
the current target, the proportions of pulls of C-tracking follow the average of the past targets.
This is what the analysis of Track-and-Stop needs when the optimal allocations are not unique
[DK19, Lemma 6 and Theorem 7]: the averages of targets chosen in a convex set of optimal
allocations stay close to that set, while the targets themselves may oscillate.

This file defines the rule as a deterministic algorithm (an index policy of LML) for any measurable
target rule, and proves that the hypothesis of the deterministic tracking lemmas of
`Identification/Tracking.lean` holds almost surely along every run. Consequently, along every run
whose targets are allocations [GK16, Lemma 7]: after `n` rounds, every arm has at least
`√(n + K²) - 2 K + 1` pulls, and `|N_a(n) - ∑_{s < n} w_a(s)| ≤ (K - 1) (1 + √n)`; the proportions
of pulls get close to the averages of the targets, and converge to the limit of the targets
whenever the targets converge.

## Main definitions

* `LMLExplore.Identification.cTrackingIndex w n h`: the index of the C-tracking rule after `n`
  rounds with history `h`, for the target rule `w`.
* `LMLExplore.Identification.cTracking w hw`: the C-tracking sampling rule with targets `w`, the
  deterministic algorithm that plays an arm of maximal `cTrackingIndex`.

## Main statements

In the namespace `LMLExplore.Identification.CTracking`, along every run of `cTracking w hw`:

* `sum_sub_pullCount_le`: almost surely, the arm played at round `k` maximizes the cumulated
  targets minus the pull counts.
* `abs_pullCount_sub_sum_le_mul_one_add_sqrt`, `sqrt_add_sub_le_pullCount`: the guarantees of
  C-tracking [GK16, Lemma 7].
* `tendsto_pullCount_atTop`: almost surely, every arm is pulled infinitely often.
* `tendsto_pullCount_div_sub_inv_mul_sum`, `tendsto_pullCount_div`: almost surely, the
  proportions of pulls get close to the averages of the targets, and converge to the limit of the
  targets whenever the targets converge.
* `tsum_measure_exists_ge_empMean_notMem_Ioo_ne_top`: under the forced exploration of C-tracking,
  the empirical means of exponential-family arms stay close to the means after `t₀ T` rounds,
  except on events whose probabilities have a finite sum over `T` [GK16, Lemma 19].

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Section 3.1 and Lemmas 7 and 19.
* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, Lemma 6 and Theorem 7.
-/

public section

open MeasureTheory ProbabilityTheory Learning Filter Finset
open scoped Topology ENNReal

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} [Fintype α] [DecidableEq α] {m𝓨 : MeasurableSpace 𝓨}
  {w : (n : ℕ) → Hist Unit α 𝓨 n → α → ℝ} {n : ℕ} {h : Hist Unit α 𝓨 n} {a : α}

/-! ### The index and the algorithm -/

/-- The index of the C-tracking rule with target rule `w`, after `n` rounds with history `h`: the
cumulated targets `∑_{s ≤ n} w^{ε_s}_a(s)` minus the pull count `N_a` of `h`, where `w(s)` is the
target `w s` of the prefix of length `s` of `h` (for `s = n`, of `h` itself) and `w^{ε_s}(s)` its
mixture `cTrackingTarget ε_s (w(s))` with the uniform allocation, `ε_s = cTrackingRate K s`
(`cumulatedTargets` of the mixed targets). -/
noncomputable def cTrackingIndex (w : (n : ℕ) → Hist Unit α 𝓨 n → α → ℝ) (n : ℕ)
    (h : Hist Unit α 𝓨 n) (a : α) : ℝ :=
  cumulatedTargets (fun s h ↦ cTrackingTarget (cTrackingRate (Fintype.card α) s) (w s h)) n h a -
    pullCount' n h a

/-- The index of C-tracking, unfolded. -/
lemma cTrackingIndex_def (w : (n : ℕ) → Hist Unit α 𝓨 n → α → ℝ) (n : ℕ) (h : Hist Unit α 𝓨 n)
    (a : α) :
    cTrackingIndex w n h a =
      cumulatedTargets (fun s h ↦ cTrackingTarget (cTrackingRate (Fintype.card α) s) (w s h)) n h
        a - pullCount' n h a :=
  (rfl)

/-- Along a sequence of rounds, the index of C-tracking at the history of the first `k` rounds is
`∑_{s ≤ k} w^{ε_s}_a(s) - N_a(k)`, with `w(s)` the target of the history of the first `s`
rounds. -/
lemma cTrackingIndex_history {Ω : Type*} (O : ℕ → Ω → Unit) (A : ℕ → Ω → α) (Y : ℕ → Ω → 𝓨)
    (k : ℕ) (ω : Ω) (a : α) :
    cTrackingIndex w k (history O A Y k ω) a =
      ∑ s ∈ range (k + 1), cTrackingTarget (cTrackingRate (Fintype.card α) s)
        (w s (history O A Y s ω)) a - pullCount A a k ω := by
  rw [cTrackingIndex_def, ← pullCount_eq_pullCount', cumulatedTargets_history]

variable [MeasurableSpace α]

/-- The index of C-tracking is a measurable function of the history if the target rule is. -/
@[fun_prop]
lemma measurable_cTrackingIndex [MeasurableSingletonClass α] (hw : ∀ n, Measurable (w n)) :
    Measurable (cTrackingIndex w n) := by
  have hN (b : α) : Measurable fun h : Hist Unit α 𝓨 n ↦ (pullCount' n h b : ℝ) :=
    measurable_from_top.comp (measurable_pullCount' n b)
  refine Measurable.of_eval fun a ↦ ?_
  simp_rw [cTrackingIndex_def]
  refine Measurable.sub ((measurable_pi_apply a).comp (measurable_cumulatedTargets fun s ↦ ?_))
    (hN a)
  refine Measurable.of_eval fun b ↦ ?_
  simp_rw [cTrackingTarget_apply]
  exact (((measurable_pi_apply b).comp (hw s)).const_mul _).add_const _

/-- The index of C-tracking, as an `EReal`-valued index of the history and the observation, is
measurable. -/
lemma measurable_coe_cTrackingIndex [MeasurableSingletonClass α] (hw : ∀ n, Measurable (w n)) :
    Measurable fun (x : Hist Unit α 𝓨 n × Unit) a ↦ (cTrackingIndex w n x.1 a : EReal) :=
  Measurable.of_eval fun a ↦ measurable_coe_real_ereal.comp
    ((measurable_pi_apply a).comp ((measurable_cTrackingIndex hw).comp measurable_fst))

variable [Nonempty α] [MeasurableSingletonClass α]

/-- The **C-tracking** sampling rule with target rule `w` [GK16, Section 3.1]: the deterministic
algorithm that plays, after `n` rounds with history `h`, an arm of maximal `cTrackingIndex w n h`
(ties broken by LML's `argmax`), that is an arm maximizing `∑_{s ≤ n} w^{ε_s}_a(s) - N_a`. -/
noncomputable def cTracking (w : (n : ℕ) → Hist Unit α 𝓨 n → α → ℝ)
    (hw : ∀ n, Measurable (w n)) : Algorithm Unit α 𝓨 :=
  Bandits.indexAlgorithm (fun n x a ↦ (cTrackingIndex w n x.1 a : EReal))
    fun _ ↦ measurable_coe_cTrackingIndex hw

variable {hw : ∀ n, Measurable (w n)}

/-- C-tracking is the index policy whose index is `cTrackingIndex`. -/
lemma cTracking_eq_indexAlgorithm :
    cTracking w hw = Bandits.indexAlgorithm (fun n x a ↦ (cTrackingIndex w n x.1 a : EReal))
      (fun _ ↦ measurable_coe_cTrackingIndex hw) :=
  (rfl)

instance : (cTracking w hw).IsDeterministic := by
  rw [cTracking_eq_indexAlgorithm]
  infer_instance

/-! ### Run lemmas -/

namespace CTracking

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {env : Environment Unit α 𝓨} {P : Measure Ω}
  [IsFiniteMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨}

/-- **Tracking step of C-tracking.** Almost surely, the arm played at every round `k` maximizes
`∑_{s ≤ k} w^{ε_s}_a(s) - N_a(k)`, with `w(s)` the target of the history of the first `s`
rounds. -/
lemma sum_sub_pullCount_le (h : IsAlgEnvSeq O A Y (cTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ k a,
      ∑ s ∈ range (k + 1), cTrackingTarget (cTrackingRate (Fintype.card α) s)
          (w s (history O A Y s ω)) a - pullCount A a k ω ≤
        ∑ s ∈ range (k + 1), cTrackingTarget (cTrackingRate (Fintype.card α) s)
          (w s (history O A Y s ω)) (A k ω) - pullCount A (A k ω) k ω := by
  rw [cTracking_eq_indexAlgorithm] at h
  filter_upwards [Bandits.IndexAlgorithm.index_le_index_action h] with ω hω k a
  rw [← cTrackingIndex_history, ← cTrackingIndex_history]
  exact EReal.coe_le_coe_iff.1 (hω k a)

variable (hw0 : ∀ n h a, 0 ≤ w n h a) (hw1 : ∀ n h, ∑ a, w n h a = 1)
include hw0 hw1

/-- **Tracking of C-tracking** [GK16, Lemma 7]. If the targets are allocations, then almost
surely, after every number `n` of rounds, `|N_a(n) - ∑_{s < n} w_a(s)| ≤ (K - 1) (1 + √n)` for
every arm `a`, with `w(s)` the target of the history of the first `s` rounds. -/
theorem abs_pullCount_sub_sum_le_mul_one_add_sqrt (h : IsAlgEnvSeq O A Y (cTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) a, |(pullCount A a n ω : ℝ) - ∑ s ∈ range n, w s (history O A Y s ω) a| ≤
      (Fintype.card α - 1) * (1 + √(n : ℝ)) := by
  filter_upwards [sum_sub_pullCount_le h] with ω hω n a
  exact abs_pullCount_sub_sum_le_mul_one_add_sqrt_of_cTracking (fun k ↦ hw0 k _)
    (fun k ↦ hw1 k _) hω n a

/-- **Forced exploration of C-tracking** [GK16, Lemma 7]. If the targets are allocations, then
almost surely, after every number `n` of rounds, every arm `a` satisfies
`√(n + K²) - 2 K + 1 ≤ N_a(n)`. -/
theorem sqrt_add_sub_le_pullCount (h : IsAlgEnvSeq O A Y (cTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) a,
      √((n : ℝ) + Fintype.card α ^ 2) - 2 * Fintype.card α + 1 ≤ pullCount A a n ω := by
  filter_upwards [sum_sub_pullCount_le h] with ω hω n a
  exact sqrt_add_sub_le_pullCount_of_cTracking (fun k ↦ hw0 k _) (fun k ↦ hw1 k _) hω n a

/-- If the targets are allocations, then almost surely, C-tracking pulls every arm infinitely
often. -/
theorem tendsto_pullCount_atTop (h : IsAlgEnvSeq O A Y (cTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ pullCount A a n ω) atTop atTop := by
  filter_upwards [sqrt_add_sub_le_pullCount hw0 hw1 h] with ω hω a
  refine tendsto_natCast_atTop_iff (R := ℝ).1 (tendsto_atTop_mono (fun n ↦ hω n a) ?_)
  refine tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ ?_)
  exact Real.tendsto_sqrt_atTop.comp
    (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)

/-- **Proportions of pulls of C-tracking.** If the targets are allocations, then almost surely,
for every arm `a`, the difference between the proportion of pulls `N_a(n) / n` and the average
`n⁻¹ ∑_{s < n} w_a(s)` of the targets tends to `0`, with `w(s)` the target of the history of
the first `s` rounds. -/
theorem tendsto_pullCount_div_sub_inv_mul_sum (h : IsAlgEnvSeq O A Y (cTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n : ℕ ↦ (pullCount A a n ω : ℝ) / n -
      (n : ℝ)⁻¹ * ∑ s ∈ range n, w s (history O A Y s ω) a) atTop (𝓝 0) := by
  filter_upwards [sum_sub_pullCount_le h] with ω hω a
  exact tendsto_pullCount_div_sub_inv_mul_sum_of_cTracking (fun k ↦ hw0 k _) (fun k ↦ hw1 k _) hω a

/-- **Convergence of the proportions of pulls of C-tracking.** If the targets are allocations,
then almost surely, for every `l : α → ℝ`, if the targets `w_a(k)` of the histories of the run
converge to `l a` for every arm `a`, then the proportions of pulls `N_a(n) / n` converge to
`l a`. -/
theorem tendsto_pullCount_div (h : IsAlgEnvSeq O A Y (cTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ l : α → ℝ, (∀ a, Tendsto (fun k ↦ w k (history O A Y k ω) a) atTop (𝓝 (l a))) →
      ∀ a, Tendsto (fun n ↦ (pullCount A a n ω : ℝ) / n) atTop (𝓝 (l a)) := by
  filter_upwards [sum_sub_pullCount_le h] with ω hω l hl a
  exact tendsto_pullCount_div_of_cTracking (fun k ↦ hw0 k _) (fun k ↦ hw1 k _) hω (hl a)

end CTracking

/-! ### Concentration of the empirical means -/

namespace CTracking

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}
  {ν : Kernel α ℝ} [IsMarkovKernel ν] {w : (n : ℕ) → Hist Unit α ℝ n → α → ℝ}
  {hw : ∀ n, Measurable (w n)} {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ l u : α → ℝ}

/-- **Concentration of the empirical means under C-tracking** [GK16, Lemma 19], in the form used
in the proof of [GK16, Theorem 14]. In a run of C-tracking against the stochastic bandit
`Environment.bandit ν`, with targets that are allocations, let the rewards of each arm `a` be
dominated on `Set.univ` by the member of mean `μ a` of the exponential family of `ρ a` and `T a`,
and let `l a < μ a < u a` be means of the family. If the rounds `t₀ T` satisfy
`√(t₀ T) / log T → ∞`, then the probabilities that the empirical mean of some arm `a` is outside
`(l a, u a)` at some round `t ≥ t₀ T` have a finite sum over `T`. -/
theorem tsum_measure_exists_ge_empMean_notMem_Ioo_ne_top (hw0 : ∀ n h a, 0 ≤ w n h a)
    (hw1 : ∀ n h, ∑ a, w n h a = 1)
    (h : IsAlgEnvSeq O A R (cTracking w hw) (Environment.bandit ν) P)
    (hν : ∀ a, MGFDominatedOn id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a)) (hl : ∀ a, l a ∈ (ρ a).expFamilyMeans (T a))
    (hu : ∀ a, u a ∈ (ρ a).expFamilyMeans (T a)) (hlμ : ∀ a, l a < μ a) (hμu : ∀ a, μ a < u a)
    {t₀ : ℕ → ℕ} (ht₀ : Tendsto (fun T : ℕ ↦ √(t₀ T : ℝ) / Real.log T) atTop atTop) :
    ∑' T, P {ω | ∃ t ≥ t₀ T, ∃ a, empMean A R a t ω ∉ Set.Ioo (l a) (u a)} ≠ ∞ := by
  have h_forced (T : ℕ) :
      ∀ᵐ ω ∂P, ∀ a, ⌈√(t₀ T : ℝ) - 2 * Fintype.card α⌉₊ ≤ pullCount A a (t₀ T) ω := by
    filter_upwards [sqrt_add_sub_le_pullCount hw0 hw1 h] with ω hω a
    refine Nat.ceil_le.2 ?_
    have h_sqrt : √(t₀ T : ℝ) ≤ √((t₀ T : ℝ) + Fintype.card α ^ 2) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
    linarith [hω (t₀ T) a]
  -- Forced exploration is sufficient exploration on the sure event.
  simpa only [Set.univ_inter] using Identification.tsum_measure_exists_ge_empMean_notMem_Ioo_ne_top
    h hν hμ hl hu hlμ hμu (G := fun _ ↦ Set.univ)
    (fun T ↦ (h_forced T).mono fun _ hω _ ↦ hω) (Real.tendsto_natCeil_sub_div_log _ ht₀)

end CTracking

end LMLExplore.Identification
