/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.ProductMeasure
import LMLExplore.Logic.Function.DependsOn
import LMLExplore.Probability.Process.StoppedValue

/-!
# Restarting at a stopping time of an i.i.d. sequence

The observations are the coordinates of `ℕ → 𝓧`. A random time `σ : (ℕ → 𝓧) → ℕ`, counted in
observations, is a stopping time when it is determined by the observations before it,
`DependsOnBefore σ σ`, and a function `f` is known at time `σ` when it is determined by the
observations before `σ`, `DependsOnBefore σ f`.

Under an i.i.d. law the observations after a stopping time `σ` are independent of what is known at
time `σ`, and they are again i.i.d. with the same law: on the event `{σ ≤ N}`, the expectation of
`f * g σ ∘ (shift 𝓧)^[σ]` splits along the values of `σ` into products of expectations
(`ProbabilityTheory.DependsOnBefore.lintegral_indicator_mul_comp_shift_iterate`). This is the
strong Markov property of an i.i.d. sequence at a stopping time, on the event that it is at most
`N`.

Restarting a round of duration `σ` and payoff `V` on the fresh observations each time it ends gives
the restart times `restartTime σ j`, the number of observations used by the first `j` rounds, and
the products `restartPayoff σ V j` of the payoffs of the first `j` rounds. The restart times are
stopping times, and the payoffs of the first `j` rounds are known at time `restartTime σ j`.

## Main definitions

* `ProbabilityTheory.DependsOnBefore σ f`: `f` is determined by the first `σ` observations
  (`ProbabilityTheory.dependsOnBefore_iff`).
* `ProbabilityTheory.restartTime σ j`: the number of observations used by the first `j` rounds of
  duration `σ`, each restarted on the fresh observations at the end of the previous one.
* `ProbabilityTheory.restartPayoff σ V j`: the product of the payoffs `V` of these `j` rounds.

## Main statements

* `ProbabilityTheory.isStoppingTime_piLT_iff_dependsOnBefore`: the stopping times of the
  filtration `Filtration.piLT` of the observations are the measurable random times determined by
  the observations before them.
* `ProbabilityTheory.DependsOnBefore.lintegral_indicator_mul_comp_shift_iterate`,
  `ProbabilityTheory.DependsOnBefore.integral_indicator_comp_shift_iterate`: the strong Markov
  property of an i.i.d. sequence at a stopping time `σ`, on the event `{σ ≤ N}`.
* `ProbabilityTheory.dependsOnBefore_restartTime`,
  `ProbabilityTheory.dependsOnBefore_restartPayoff`: the restart times are stopping times, and
  the payoffs of the first `j` rounds are known at the end of these rounds.

## Implementation notes

The definitions and the restart lemmas are adapted from
`EValuesResearch/Results/BipolarRateAux.lean` (commit `dd4072f`) in the paper project
`RemyDegenne/evalues_research`, where they are used to prove the Wald inequality at the bipolar
rate of [EVR26, Note 01] (`ProbabilityTheory.integral_truncLog_le_bipolarRate_mul`).

## References

* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 01,
  `results/01-bipolar-rate.md`.
-/

public section

open MeasureTheory
open TauCeti.Probability (shift measurable_shift_iterate)
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-! ### Functions determined by the observations before a random time -/

/-- `f` is determined by the first `σ` observations: if `σ ω ≤ u` and `ω'` agrees with `ω` on the
first `u` observations, then `f ω' = f ω`. For `f = σ`, this says that `σ` is a stopping time
counted in observations. -/
def DependsOnBefore {β : Type*} (σ : (ℕ → 𝓧) → ℕ) (f : (ℕ → 𝓧) → β) : Prop :=
  ∀ ⦃u : ℕ⦄ ⦃ω ω' : ℕ → 𝓧⦄, (∀ i < u, ω i = ω' i) → σ ω ≤ u → f ω' = f ω

/-- The defining property of `DependsOnBefore`. -/
lemma dependsOnBefore_iff {β : Type*} {σ : (ℕ → 𝓧) → ℕ} {f : (ℕ → 𝓧) → β} :
    DependsOnBefore σ f ↔
      ∀ ⦃u : ℕ⦄ ⦃ω ω' : ℕ → 𝓧⦄, (∀ i < u, ω i = ω' i) → σ ω ≤ u → f ω' = f ω :=
  Iff.rfl

namespace DependsOnBefore

variable {σ : (ℕ → 𝓧) → ℕ} {β : Type*} {f : (ℕ → 𝓧) → β}

/-- For a stopping time `σ`, whether `σ = t` is determined by the first `t` observations. -/
lemma eq_iff_of_eqOn (hσ : DependsOnBefore σ σ) {t : ℕ} {ω ω' : ℕ → 𝓧}
    (h : ∀ i < t, ω i = ω' i) : σ ω' = t ↔ σ ω = t :=
  ⟨fun h' ↦ (hσ (fun i hi ↦ (h i hi).symm) h'.le).trans h', fun h' ↦ (hσ h h'.le).trans h'⟩

/-- For a stopping time `σ`, whether `σ ≤ N` is determined by the first `N` observations. -/
lemma le_iff_of_eqOn (hσ : DependsOnBefore σ σ) {N : ℕ} {ω ω' : ℕ → 𝓧}
    (h : ∀ i < N, ω i = ω' i) : σ ω' ≤ N ↔ σ ω ≤ N :=
  ⟨fun h' ↦ hσ (fun i hi ↦ (h i hi).symm) h' ▸ h', fun h' ↦ (hσ h h').symm ▸ h'⟩

/-- On the event `{σ = t}`, a function known at the stopping time `σ` is a function of the first
`t` observations. -/
lemma dependsOn_indicator_eq [Zero β] (hσ : DependsOnBefore σ σ) (hf : DependsOnBefore σ f)
    (t : ℕ) : DependsOn ({ω | σ ω = t}.indicator f) (Set.Iio t) :=
  dependsOn_indicator_of_eqOn (fun _ _ h ↦ hσ.eq_iff_of_eqOn h) fun _ _ h hω ↦ hf h hω.le

/-- On the event `{σ ≤ N}`, a function known at the stopping time `σ` is a function of the first
`N` observations. -/
lemma dependsOn_indicator_le [Zero β] (hσ : DependsOnBefore σ σ) (hf : DependsOnBefore σ f)
    (N : ℕ) : DependsOn ({ω | σ ω ≤ N}.indicator f) (Set.Iio N) :=
  dependsOn_indicator_of_eqOn (fun _ _ h ↦ hσ.le_iff_of_eqOn h) fun _ _ h hω ↦ hf h hω

end DependsOnBefore

/-- **Stopping times counted in observations.** A random time `σ` with values in `ℕ` is a stopping
time of the filtration `Filtration.piLT` of the observations, whose time `n` has seen the first
`n` observations, exactly when it is measurable and determined by the observations before it. -/
theorem isStoppingTime_piLT_iff_dependsOnBefore {σ : (ℕ → 𝓧) → ℕ} :
    IsStoppingTime (Filtration.piLT (X := fun _ : ℕ ↦ 𝓧)) (fun ω ↦ (σ ω : WithTop ℕ)) ↔
      Measurable σ ∧ DependsOnBefore σ σ := by
  refine ⟨fun hσ ↦ ⟨hσ.measurable'.untopA, fun u ω ω' h hu ↦ ?_⟩,
    fun ⟨hσm, hσ⟩ n ↦ ?_⟩
  · exact WithTop.coe_injective (hσ.eq_of_forall_lt rfl fun i hi ↦ h i (by omega))
  · have hm : Measurable fun ω ↦ σ ω ≤ n :=
      measurable_mem.2 (hσm (MeasurableSet.of_discrete (s := {m : ℕ | m ≤ n})))
    have hmn := Filtration.measurable_piLT_of_dependsOn hm
      fun ω ω' h ↦ propext (hσ.le_iff_of_eqOn fun i hi ↦ (h i hi).symm)
    convert (@measurable_mem _ {ω | σ ω ≤ n} (Filtration.piLT (X := fun _ : ℕ ↦ 𝓧) n)).1 hmn
      using 1
    ext ω
    simp

/-! ### The strong Markov property at a stopping time -/

/-- Summing the indicators of the events `{T = t}`, `t ≤ N`, gives the indicator of `{T ≤ N}`. -/
private lemma sum_indicator_eq_indicator_le {Ω M : Type*} [AddCommMonoid M] (T : Ω → ℕ)
    (f : Ω → M) (N : ℕ) (ω : Ω) :
    ∑ t ∈ Finset.range (N + 1), {ω | T ω = t}.indicator f ω = {ω | T ω ≤ N}.indicator f ω := by
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Finset.sum_ite_eq, Finset.mem_range,
    Nat.lt_succ_iff]

/-- On the event `{T = t}`, a function `G t` of the time `t` is the function `G (T ·)` of the
random time: `𝟙{T = t} f * G t = 𝟙{T = t} (f * G T)`. -/
private lemma indicator_eq_mul_apply {Ω M : Type*} [MulZeroClass M] (T : Ω → ℕ) (t : ℕ)
    (f : Ω → M) (G : ℕ → Ω → M) (ω : Ω) :
    {ω | T ω = t}.indicator f ω * G t ω =
      {ω | T ω = t}.indicator (fun ω' ↦ f ω' * G (T ω') ω') ω := by
  by_cases h : T ω = t
  · rw [Set.indicator_of_mem (s := {x | T x = t}) h, Set.indicator_of_mem (s := {x | T x = t}) h,
      h]
  · rw [Set.indicator_of_notMem (s := {x | T x = t}) h,
      Set.indicator_of_notMem (s := {x | T x = t}) h, zero_mul]

namespace DependsOnBefore

variable {σ : (ℕ → 𝓧) → ℕ}

/-- **The strong Markov property of an i.i.d. sequence at a stopping time.** Under an i.i.d. law,
on the event that the stopping time `σ` is at most `N`, a function `f` known at time `σ` and a
function `g σ` of the observations after time `σ` have the expectation of their product given by
the sum over the values `t ≤ N` of `σ` of the product of the expectations of `f` on `{σ = t}` and
of `g t`: the observations after time `σ` are independent of what is known at time `σ`, and they
are again i.i.d. with the same law. -/
theorem lintegral_indicator_mul_comp_shift_iterate (hσ : DependsOnBefore σ σ)
    (hσm : Measurable σ) {f : (ℕ → 𝓧) → ℝ≥0∞} (hf : DependsOnBefore σ f) (hfm : Measurable f)
    {g : ℕ → (ℕ → 𝓧) → ℝ≥0∞} (hg : ∀ t, Measurable (g t)) (P : Measure 𝓧)
    [IsProbabilityMeasure P] (N : ℕ) :
    ∫⁻ ω, {ω | σ ω ≤ N}.indicator (fun ω ↦ f ω * g (σ ω) ((shift 𝓧)^[σ ω] ω)) ω
        ∂Measure.infinitePi (fun _ : ℕ ↦ P) =
      ∑ t ∈ Finset.range (N + 1),
        (∫⁻ ω, {ω | σ ω = t}.indicator f ω ∂Measure.infinitePi (fun _ : ℕ ↦ P)) *
          ∫⁻ ω, g t ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) := by
  have hft (t : ℕ) : Measurable ({ω | σ ω = t}.indicator f) :=
    hfm.indicator (hσm (measurableSet_singleton t))
  have hsum (ω : ℕ → 𝓧) :
      {ω | σ ω ≤ N}.indicator (fun ω ↦ f ω * g (σ ω) ((shift 𝓧)^[σ ω] ω)) ω =
        ∑ t ∈ Finset.range (N + 1), {ω | σ ω = t}.indicator f ω * g t ((shift 𝓧)^[t] ω) := by
    rw [← sum_indicator_eq_indicator_le]
    exact Finset.sum_congr rfl fun t _ ↦
      (indicator_eq_mul_apply σ t f (fun s ω ↦ g s ((shift 𝓧)^[s] ω)) ω).symm
  simp_rw [hsum]
  refine (lintegral_finsetSum _ fun t _ ↦
    (hft t).mul ((hg t).comp (measurable_shift_iterate t))).trans ?_
  exact Finset.sum_congr rfl fun t _ ↦
    lintegral_mul_comp_shift_iterate P (hft t) (hσ.dependsOn_indicator_eq hf t) (hg t)

/-- **The strong Markov property of an i.i.d. sequence at a stopping time**, for a real
integrable function `g`. Under an i.i.d. law, on the event that the stopping time `σ` is at most
`N`, the function `g` of the observations after time `σ` has expectation the probability of
`{σ ≤ N}` times the expectation of `g`. -/
theorem integral_indicator_comp_shift_iterate (hσ : DependsOnBefore σ σ) (hσm : Measurable σ)
    (P : Measure 𝓧) [IsProbabilityMeasure P] {g : (ℕ → 𝓧) → ℝ} (hg : Measurable g)
    (hgi : Integrable g (Measure.infinitePi fun _ : ℕ ↦ P)) (N : ℕ) :
    ∫ ω, {ω | σ ω ≤ N}.indicator (fun ω ↦ g ((shift 𝓧)^[σ ω] ω)) ω
        ∂Measure.infinitePi (fun _ : ℕ ↦ P) =
      (Measure.infinitePi (fun _ : ℕ ↦ P)).real {ω | σ ω ≤ N} *
        ∫ ω, g ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ P)
  have hs (t : ℕ) : MeasurableSet {ω | σ ω = t} := hσm (measurableSet_singleton t)
  have hf (t : ℕ) : Measurable ({ω | σ ω = t}.indicator (1 : (ℕ → 𝓧) → ℝ)) :=
    measurable_one.indicator (hs t)
  have hfg (t : ℕ) : Integrable (fun ω ↦
      {ω | σ ω = t}.indicator (1 : (ℕ → 𝓧) → ℝ) ω * g ((shift 𝓧)^[t] ω)) μ := by
    have h := ((measurePreserving_shift_iterate P t).integrable_comp_of_integrable hgi).indicator
      (hs t)
    refine h.congr (ae_of_all _ fun ω ↦ ?_)
    by_cases hω : σ ω = t <;> simp [Set.indicator, hω]
  have hsum (ω : ℕ → 𝓧) : {ω | σ ω ≤ N}.indicator (fun ω ↦ g ((shift 𝓧)^[σ ω] ω)) ω =
      ∑ t ∈ Finset.range (N + 1),
        {ω | σ ω = t}.indicator (1 : (ℕ → 𝓧) → ℝ) ω * g ((shift 𝓧)^[t] ω) := by
    rw [← sum_indicator_eq_indicator_le]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [indicator_eq_mul_apply σ t 1 (fun s ω ↦ g ((shift 𝓧)^[s] ω))]
    simp only [Pi.one_apply, one_mul]
  simp_rw [hsum]
  rw [integral_finsetSum _ fun t _ ↦ hfg t]
  calc ∑ t ∈ Finset.range (N + 1), ∫ ω,
        {ω | σ ω = t}.indicator (1 : (ℕ → 𝓧) → ℝ) ω * g ((shift 𝓧)^[t] ω) ∂μ
  _ = ∑ t ∈ Finset.range (N + 1),
        (∫ ω, {ω | σ ω = t}.indicator (1 : (ℕ → 𝓧) → ℝ) ω ∂μ) * ∫ ω, g ω ∂μ :=
    Finset.sum_congr rfl fun t _ ↦ integral_mul_comp_shift_iterate P (hf t)
      (hσ.dependsOn_indicator_eq (fun _ _ _ _ _ ↦ rfl) t) hg
  _ = μ.real {ω | σ ω ≤ N} * ∫ ω, g ω ∂μ := by
    rw [← Finset.sum_mul, ← integral_finsetSum (f := fun t ω ↦
      {ω | σ ω = t}.indicator (1 : (ℕ → 𝓧) → ℝ) ω) _ fun t _ ↦
        (integrable_const (1 : ℝ)).indicator (hs t)]
    simp_rw [sum_indicator_eq_indicator_le]
    rw [integral_indicator_one (s := {ω | σ ω ≤ N}) (hσm measurableSet_Iic)]

end DependsOnBefore

/-! ### Restarting a round on the fresh observations

A round is a pair of a duration `σ : (ℕ → 𝓧) → ℕ`, the number of observations that it uses, and a
payoff `V : (ℕ → 𝓧) → ℝ≥0∞`. Restarting the round on the fresh observations at its end gives the
restart times `restartTime σ j` and the products `restartPayoff σ V j` of the payoffs of the first
`j` rounds. -/

section Restart

variable (σ : (ℕ → 𝓧) → ℕ) (V : (ℕ → 𝓧) → ℝ≥0∞)

/-- The number of observations used by the first `j` rounds, when a round that uses `σ ω`
observations is restarted on the fresh observations at its end. -/
def restartTime : ℕ → (ℕ → 𝓧) → ℕ
  | 0 => fun _ ↦ 0
  | j + 1 => fun ω ↦ restartTime j ω + σ ((shift 𝓧)^[restartTime j ω] ω)

/-- The product of the payoffs `V` of the first `j` restarted rounds. -/
noncomputable def restartPayoff : ℕ → (ℕ → 𝓧) → ℝ≥0∞
  | 0 => fun _ ↦ 1
  | j + 1 => fun ω ↦ restartPayoff j ω * V ((shift 𝓧)^[restartTime σ j ω] ω)

/-- No round uses no observation. -/
@[simp]
lemma restartTime_zero (ω : ℕ → 𝓧) : restartTime σ 0 ω = 0 :=
  (rfl)

/-- The round after the first `j` ones is played on the observations after them. -/
lemma restartTime_succ (j : ℕ) (ω : ℕ → 𝓧) :
    restartTime σ (j + 1) ω = restartTime σ j ω + σ ((shift 𝓧)^[restartTime σ j ω] ω) :=
  (rfl)

/-- The payoff of no round is `1`. -/
@[simp]
lemma restartPayoff_zero (ω : ℕ → 𝓧) : restartPayoff σ V 0 ω = 1 :=
  (rfl)

/-- The payoff of `j + 1` rounds is that of the first `j` times that of the next one. -/
lemma restartPayoff_succ (j : ℕ) (ω : ℕ → 𝓧) :
    restartPayoff σ V (j + 1) ω =
      restartPayoff σ V j ω * V ((shift 𝓧)^[restartTime σ j ω] ω) :=
  (rfl)

/-- The restart times are nondecreasing in the number of rounds. -/
lemma monotone_restartTime (ω : ℕ → 𝓧) : Monotone fun j ↦ restartTime σ j ω :=
  monotone_nat_of_le_succ fun _ ↦ Nat.le_add_right _ _

/-- The first `j` rounds use the sum of their durations. -/
lemma restartTime_eq_sum (j : ℕ) (ω : ℕ → 𝓧) :
    restartTime σ j ω = ∑ i ∈ Finset.range j, σ ((shift 𝓧)^[restartTime σ i ω] ω) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Finset.sum_range_succ, ← ih, restartTime_succ]

/-- The payoff of the first `j` rounds is the product of their payoffs. -/
lemma restartPayoff_eq_prod (j : ℕ) (ω : ℕ → 𝓧) :
    restartPayoff σ V j ω = ∏ i ∈ Finset.range j, V ((shift 𝓧)^[restartTime σ i ω] ω) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Finset.prod_range_succ, ← ih, restartPayoff_succ]

variable {σ V}

/-- If every round uses at least one observation, `j` rounds use at least `j` observations. -/
lemma le_restartTime (hσ1 : ∀ ω, 1 ≤ σ ω) (j : ℕ) (ω : ℕ → 𝓧) : j ≤ restartTime σ j ω := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact Nat.add_le_add ih (hσ1 _)

/-- The restart times are measurable. -/
lemma measurable_restartTime (hσm : Measurable σ) (j : ℕ) : Measurable (restartTime σ j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    exact ih.add (measurable_apply_of_countable (fun t ↦ hσm.comp (measurable_shift_iterate t)) ih)

/-- The products of the payoffs of the restarted rounds are measurable. -/
lemma measurable_restartPayoff (hσm : Measurable σ) (hVm : Measurable V) (j : ℕ) :
    Measurable (restartPayoff σ V j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih => exact ih.mul (measurable_apply_of_countable
      (fun t ↦ hVm.comp (measurable_shift_iterate t)) (measurable_restartTime hσm j))

/-- **The restart times are stopping times.** If the duration `σ` of a round is a stopping time,
the number of observations used by the first `j` restarted rounds is a stopping time. -/
lemma dependsOnBefore_restartTime (hσ : DependsOnBefore σ σ) (j : ℕ) :
    DependsOnBefore (restartTime σ j) (restartTime σ j) := by
  intro t ω ω' h hj
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [restartTime_succ] at hj
    rw [restartTime_succ, restartTime_succ, ih (by omega),
      hσ (shift_iterate_eqOn h (restartTime σ j ω)) (by omega)]

/-- **The payoffs of the restarted rounds are known at their end.** If the duration `σ` of a round
is a stopping time and its payoff `V` is known at time `σ`, the payoff of the first `j` restarted
rounds is known at the time `restartTime σ j` that they end. -/
lemma dependsOnBefore_restartPayoff (hσ : DependsOnBefore σ σ) (hV : DependsOnBefore σ V)
    (j : ℕ) : DependsOnBefore (restartTime σ j) (restartPayoff σ V j) := by
  intro t ω ω' h hj
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [restartTime_succ] at hj
    rw [restartPayoff_succ, restartPayoff_succ, dependsOnBefore_restartTime hσ j h (by omega),
      ih (by omega), hV (shift_iterate_eqOn h (restartTime σ j ω)) (by omega)]

end Restart

end ProbabilityTheory
