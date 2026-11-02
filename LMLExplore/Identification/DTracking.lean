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
# The D-tracking sampling rule

The D-tracking rule of Garivier and Kaufmann (2016) follows a sequence of target allocations
computed from the data, typically the optimal allocations `w*(μ̂(t))` at the empirical means in
Track-and-Stop, while forcing the exploration of the arms that are pulled too rarely. With
`N_a(t)` the number of pulls of arm `a` in the first `t` rounds and `K` the number of arms, at
round `t` it plays
* an arm with the fewest pulls, if some arm `a` is in deficit: `N_a(t) < √t - K / 2`;
* otherwise an arm maximizing `t w_a(t) - N_a(t)`, the arm that lags the most behind the target
  `w(t)` computed from the history of the first `t` rounds.

In [GK16] the forced arm is one with the fewest pulls among the arms in deficit; an arm with the
fewest pulls overall is in deficit as soon as some arm is, so both rules play the same set of arms.

This file defines the rule as a deterministic algorithm (an index policy of LML) for any measurable
target rule, and proves that the hypotheses of the deterministic tracking lemmas of
`Identification/Tracking.lean` hold almost surely along every run. Consequently, along every run:
every arm has more than `√t - K / 2 - 1` pulls after `t` rounds [GK16, Lemma 8], the proportions of
pulls converge to the limit of the targets whenever the targets converge [GK16, Lemma 8], and, for
rewards dominated by exponential families, the empirical means concentrate after forced
exploration with summable failure probabilities [GK16, Lemma 19], as the proof of the asymptotic
optimality of Track-and-Stop [GK16, Theorem 14] requires.

## Main definitions

* `LMLExplore.Identification.dTrackingIndex w n h`: the index of the D-tracking rule after `n`
  rounds with history `h`, for the target rule `w`.
* `LMLExplore.Identification.dTracking w hw`: the D-tracking sampling rule with targets `w`, the
  deterministic algorithm that plays an arm of maximal `dTrackingIndex`.

## Main statements

In the namespace `LMLExplore.Identification.DTracking`, along every run of `dTracking w hw`:

* `pullCount_action_le_of_lt`, `mul_sub_pullCount_le_of_forall_le`: almost surely, the arm played
  at round `k` is forced when some arm is in deficit, and tracks the target `w k` otherwise.
* `sqrt_sub_sub_one_lt_pullCount`: forced exploration [GK16, Lemma 8]: almost surely,
  `√n - K / 2 - 1 < N_a(n)` for every arm `a` and every `n`.
* `tendsto_pullCount_atTop`: almost surely, every arm is pulled infinitely often.
* `tendsto_pullCount_div`: [GK16, Lemma 8]: almost surely, whenever the targets converge to a
  probability vector `l`, the proportions of pulls `N_a(n) / n` converge to `l a`.
* `tsum_measure_exists_ge_empMean_notMem_Ioo_ne_top`: [GK16, Lemma 19] for D-tracking: for
  rewards dominated by exponential families and rounds `t₀ T` with `√(t₀ T) / log T → ∞`, the
  probabilities that some empirical mean leaves a neighbourhood of its mean at some round
  `t ≥ t₀ T` have a finite sum over `T`.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Section 3.1, Lemmas 8 and 19, and the proof of Theorem 14.
-/

public section

open MeasureTheory ProbabilityTheory Learning Filter Real
open scoped Topology ENNReal

namespace LMLExplore.Identification

variable {α 𝓨 : Type*} [Fintype α] [DecidableEq α] {m𝓨 : MeasurableSpace 𝓨}
  {w : (n : ℕ) → Hist Unit α 𝓨 n → α → ℝ} {n : ℕ} {h : Hist Unit α 𝓨 n} {a : α}

/-! ### The index and the algorithm -/

/-- The index of the D-tracking rule with target rule `w`, after `n` rounds with history `h`.
If some arm `b` is in deficit, `N_b < √n - K / 2` with `N` the pull counts of `h` and `K` the
number of arms, the index of `a` is `-N_a`, maximal for the arms with the fewest pulls.
Otherwise it is `n w_a - N_a`, maximal for the arms that lag the most behind the target `w n h`. -/
noncomputable def dTrackingIndex (w : (n : ℕ) → Hist Unit α 𝓨 n → α → ℝ) (n : ℕ)
    (h : Hist Unit α 𝓨 n) (a : α) : ℝ :=
  if ∃ b, (pullCount' n h b : ℝ) < √(n : ℝ) - Fintype.card α / 2 then -(pullCount' n h a : ℝ)
  else n * w n h a - pullCount' n h a

/-- If some arm is in deficit, the index of `a` is `-N_a`. -/
lemma dTrackingIndex_of_exists
    (hb : ∃ b, (pullCount' n h b : ℝ) < √(n : ℝ) - Fintype.card α / 2) :
    dTrackingIndex w n h a = -(pullCount' n h a : ℝ) := by
  rw [dTrackingIndex, ite_eq_left hb]

/-- If no arm is in deficit, the index of `a` is `n w_a - N_a`. -/
lemma dTrackingIndex_of_forall (hb : ∀ b, √(n : ℝ) - Fintype.card α / 2 ≤ pullCount' n h b) :
    dTrackingIndex w n h a = n * w n h a - pullCount' n h a := by
  have hb' : ¬∃ b, (pullCount' n h b : ℝ) < √(n : ℝ) - Fintype.card α / 2 := by
    simpa using hb
  rw [dTrackingIndex, ite_eq_right hb']

variable [MeasurableSpace α]

/-- The index of D-tracking is a measurable function of the history if the target rule is. -/
@[fun_prop]
lemma measurable_dTrackingIndex [MeasurableSingletonClass α] (hw : Measurable (w n)) :
    Measurable (dTrackingIndex w n) := by
  have hN (b : α) : Measurable fun h : Hist Unit α 𝓨 n ↦ (pullCount' n h b : ℝ) :=
    measurable_from_top.comp (measurable_pullCount' n b)
  refine Measurable.of_eval fun a ↦ Measurable.ite ?_ (hN a).neg
    (((measurable_pi_apply a).comp hw).const_mul _ |>.sub (hN a))
  rw [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun b ↦ measurableSet_lt (hN b) measurable_const

/-- The index of D-tracking, as an `EReal`-valued index of the history and the observation, is
measurable. -/
lemma measurable_coe_dTrackingIndex [MeasurableSingletonClass α] (hw : Measurable (w n)) :
    Measurable fun (x : Hist Unit α 𝓨 n × Unit) a ↦ (dTrackingIndex w n x.1 a : EReal) :=
  Measurable.of_eval fun a ↦ measurable_coe_real_ereal.comp
    ((measurable_pi_apply a).comp ((measurable_dTrackingIndex hw).comp measurable_fst))

variable [Nonempty α] [MeasurableSingletonClass α]

/-- The **D-tracking** sampling rule with target rule `w` [GK16, Section 3.1]: the deterministic
algorithm that plays, after `n` rounds with history `h`, an arm of maximal `dTrackingIndex w n h`
(ties broken by LML's `argmax`). It plays an arm with the fewest pulls if some arm `a` has
`N_a < √n - K / 2`, and otherwise an arm maximizing `n w_a - N_a`, for the target `w n h`. -/
noncomputable def dTracking (w : (n : ℕ) → Hist Unit α 𝓨 n → α → ℝ)
    (hw : ∀ n, Measurable (w n)) : Algorithm Unit α 𝓨 :=
  Bandits.indexAlgorithm (fun n x a ↦ (dTrackingIndex w n x.1 a : EReal))
    fun n ↦ measurable_coe_dTrackingIndex (hw n)

variable {hw : ∀ n, Measurable (w n)}

/-- D-tracking is the index policy whose index is `dTrackingIndex`. -/
lemma dTracking_eq_indexAlgorithm :
    dTracking w hw = Bandits.indexAlgorithm (fun n x a ↦ (dTrackingIndex w n x.1 a : EReal))
      (fun n ↦ measurable_coe_dTrackingIndex (hw n)) :=
  (rfl)

instance : IsDeterministicAlg (dTracking w hw) := by
  rw [dTracking_eq_indexAlgorithm]
  infer_instance

/-! ### Run lemmas -/

namespace DTracking

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {env : Environment Unit α 𝓨} {P : Measure Ω}
  [IsFiniteMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨}

/-- The run lemma of D-tracking: almost surely, the arm played at every round `k` has maximal
index for the history of the first `k` rounds. -/
lemma index_le_index_action (h : IsAlgEnvSeq O A Y (dTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ k b, dTrackingIndex w k (history O A Y k ω) b ≤
      dTrackingIndex w k (history O A Y k ω) (A k ω) := by
  rw [dTracking_eq_indexAlgorithm] at h
  filter_upwards [Bandits.IndexAlgorithm.index_le_index_action h] with ω hω k b
  exact EReal.coe_le_coe_iff.1 (hω k b)

/-- **Forced exploration step of D-tracking.** Almost surely, at every round `k`, if an arm `a` is
in deficit, `N_a(k) < √k - K / 2`, then the arm played at round `k` has been pulled at most as
often as `a`. -/
lemma pullCount_action_le_of_lt (h : IsAlgEnvSeq O A Y (dTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) a, (pullCount A a k ω : ℝ) < √(k : ℝ) - Fintype.card α / 2 →
      pullCount A (A k ω) k ω ≤ pullCount A a k ω := by
  filter_upwards [index_le_index_action h] with ω hω k a ha
  have hN (b : α) : pullCount' k (history O A Y k ω) b = pullCount A b k ω :=
    pullCount_eq_pullCount'.symm
  have hex : ∃ b, (pullCount' k (history O A Y k ω) b : ℝ) < √(k : ℝ) - Fintype.card α / 2 :=
    ⟨a, by rwa [hN]⟩
  have := hω k a
  rw [dTrackingIndex_of_exists hex, dTrackingIndex_of_exists hex, hN, hN, neg_le_neg_iff] at this
  exact_mod_cast this

/-- **Tracking step of D-tracking.** Almost surely, at every round `k`, if no arm is in deficit,
`√k - K / 2 ≤ N_a(k)` for every arm `a`, then the arm played at round `k` maximizes
`k w_a - N_a(k)` for the target `w k` of the history of the first `k` rounds. -/
lemma mul_sub_pullCount_le_of_forall_le (h : IsAlgEnvSeq O A Y (dTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, (∀ a, √(k : ℝ) - Fintype.card α / 2 ≤ pullCount A a k ω) → ∀ a,
      k * w k (history O A Y k ω) a - pullCount A a k ω ≤
        k * w k (history O A Y k ω) (A k ω) - pullCount A (A k ω) k ω := by
  filter_upwards [index_le_index_action h] with ω hω k hk a
  have hN (b : α) : pullCount' k (history O A Y k ω) b = pullCount A b k ω :=
    pullCount_eq_pullCount'.symm
  have hall (b : α) : √(k : ℝ) - Fintype.card α / 2 ≤ pullCount' k (history O A Y k ω) b := by
    rw [hN]
    exact hk b
  have := hω k a
  rwa [dTrackingIndex_of_forall hall, dTrackingIndex_of_forall hall, hN, hN] at this

/-- **Forced exploration of D-tracking** [GK16, Lemma 8]. Almost surely, after every number `n`
of rounds, every arm `a` satisfies `√n - K / 2 - 1 < N_a(n)`. -/
theorem sqrt_sub_sub_one_lt_pullCount (h : IsAlgEnvSeq O A Y (dTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) a, √(n : ℝ) - Fintype.card α / 2 - 1 < pullCount A a n ω := by
  filter_upwards [pullCount_action_le_of_lt h] with ω hω n a
  exact Identification.sqrt_sub_sub_one_lt_pullCount hω n a

/-- Almost surely, D-tracking pulls every arm infinitely often. -/
theorem tendsto_pullCount_atTop (h : IsAlgEnvSeq O A Y (dTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ a, Tendsto (fun n ↦ pullCount A a n ω) atTop atTop := by
  filter_upwards [sqrt_sub_sub_one_lt_pullCount h] with ω hω a
  refine tendsto_natCast_atTop_iff (R := ℝ).1 (tendsto_atTop_mono (fun n ↦ (hω n a).le) ?_)
  exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _
    (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))

/-- **Convergence of the proportions of pulls of D-tracking** [GK16, Lemma 8]. Almost surely, for
every probability vector `l`, if the targets `w k` of the histories of the run converge to `l`,
then the proportions of pulls `N_a(n) / n` converge to `l a` for every arm `a`. -/
theorem tendsto_pullCount_div (h : IsAlgEnvSeq O A Y (dTracking w hw) env P) :
    ∀ᵐ ω ∂P, ∀ l : α → ℝ, (∀ a, 0 ≤ l a) → ∑ a, l a = 1 →
      (∀ a, Tendsto (fun k ↦ w k (history O A Y k ω) a) atTop (𝓝 (l a))) →
      ∀ a, Tendsto (fun n ↦ (pullCount A a n ω : ℝ) / n) atTop (𝓝 (l a)) := by
  filter_upwards [pullCount_action_le_of_lt h, mul_sub_pullCount_le_of_forall_le h]
    with ω hforced htrack l hl0 hl1 hw' a
  exact tendsto_pullCount_div_of_sqrt_sub hl0 hl1 (Eventually.of_forall hforced)
    (Eventually.of_forall htrack) hw' a

/-! ### Concentration of the empirical means -/

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ν : Kernel α ℝ} [IsMarkovKernel ν]
  {R : ℕ → Ω → ℝ} {w : (n : ℕ) → Hist Unit α ℝ n → α → ℝ} {hw : ∀ n, Measurable (w n)}
  {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ l u : α → ℝ}

/-- **Concentration of the empirical means under D-tracking** [GK16, Lemma 19], in the form used
in the proof of [GK16, Theorem 14]. In a run of D-tracking against the stochastic bandit
`stationaryEnv ν`, let the rewards of each arm `a` be dominated above and below by the member of
mean `μ a` of the exponential family of `ρ a` and `T a`, and let `l a < μ a < u a` be means of the
family. If the rounds `t₀ T` satisfy `√(t₀ T) / log T → ∞` (for instance `t₀ T = ⌈T ^ (1 / 4)⌉₊`
as in [GK16]), then the probabilities that the empirical mean of some arm `a` is outside
`(l a, u a)` at some round `t ≥ t₀ T` have a finite sum over `T`. -/
theorem tsum_measure_exists_ge_empMean_notMem_Ioo_ne_top [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A R (dTracking w hw) (stationaryEnv ν) P)
    (hν_above : ∀ a, MGFDominatedAbove id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hν_below : ∀ a, MGFDominatedBelow id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a)) (hl : ∀ a, l a ∈ (ρ a).expFamilyMeans (T a))
    (hu : ∀ a, u a ∈ (ρ a).expFamilyMeans (T a)) (hlμ : ∀ a, l a < μ a) (hμu : ∀ a, μ a < u a)
    {t₀ : ℕ → ℕ} (ht₀ : Tendsto (fun T : ℕ ↦ √(t₀ T : ℝ) / log T) atTop atTop) :
    ∑' T, P {ω | ∃ t ≥ t₀ T, ∃ a, empMean A R a t ω ∉ Set.Ioo (l a) (u a)} ≠ ∞ := by
  refine Identification.tsum_measure_exists_ge_empMean_notMem_Ioo_ne_top h hν_above hν_below hμ
    hl hu hlμ hμu
    (m := fun T ↦ ⌈√(t₀ T : ℝ) - (Fintype.card α / 2 + 1)⌉₊) (fun T ↦ ?_)
    (Real.tendsto_natCeil_sub_div_log _ ht₀)
  filter_upwards [sqrt_sub_sub_one_lt_pullCount h] with ω hω a
  refine Nat.ceil_le.2 ?_
  linarith [hω (t₀ T) a]

end DTracking

end LMLExplore.Identification
