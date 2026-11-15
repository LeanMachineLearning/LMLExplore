/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import LMLExplore.EValues.EProcess
public import Mathlib.Probability.ProductMeasure
import LMLExplore.EValues.BipolarRate.EProcess
import LMLExplore.Probability.Process.Stopping
import LMLExplore.Probability.Process.StoppedValue
import Mathlib.Probability.Independence.Integration
import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner
import TauCeti.Probability.Process.PathLaw.Shift

/-!
# Expected stopping times are governed by the bipolar rate

Let `S₁` be a set of probability measures on `𝓧` (the null) and `Q₁` a probability measure on `𝓧`
(the alternative). The observations are the coordinates of `ℕ → 𝓧`, with the i.i.d. laws
`Measure.infinitePi fun _ ↦ P`, `P ∈ S₁`, and the filtration `Filtration.piLE`, so that `τ + 1`
observations have been made at a time `τ`. Write `d = bipolarRate Q₁ S₁` and `Q` for the i.i.d. law
of `Q₁`.

The **Wald inequality** at the bipolar rate: for every e-process `E` for the i.i.d. null and every
stopping time `τ` with values in `ℕ`, `𝔼_Q[log E_τ] ≤ 𝔼_Q[τ + 1] * d`, in `EReal`, with
Statlib's extended integral on the left. Nothing is assumed of `S₁` beyond its members being
probability measures, and nothing of `Q₁`. The expectation of `τ` may be infinite, with
`∞ * 0 = 0`: if `d = 0`, the e-process has a nonpositive expected logarithm at every stopping
time.

Its case `E n = α⁻¹ * 𝟙{τ ≤ n}` (mixed with a constant, so that its logarithm is finite) is the
**lower bound on expected stopping times**: a sequential test of level `α`, that is, a stopping
time `τ` with values in `WithTop ℕ` such that `P^ℕ (τ < ∞) ≤ α` for every `P ∈ S₁`, makes at least
`log (1/α) / d` observations in expectation under `Q`. If `d = 0`, every test of a level `α < 1`
has an infinite expected number of observations. Since `d` is at most the smallest relative
entropy `KL_inf(Q₁, S₁)` from `Q₁` to the null (`ProbabilityTheory.bipolarRate_le_iInf_klDiv`),
this contains the lower bound with `KL_inf(Q₁, S₁)` in place of `d`, the form of the bounds of
[ARR26]; the bipolar rate can be smaller [RR26, Proposition 5.4].

## Main statements

* `ProbabilityTheory.IsEProcess.eintegral_log_stoppedValue_le_mul_bipolarRate`: the Wald
  inequality `𝔼_Q[log E_τ] ≤ 𝔼_Q[τ + 1] * d`.
* `ProbabilityTheory.toENNReal_log_inv_div_bipolarRate_le_lintegral`: a sequential test of level
  `α` has `log (1/α) / d ≤ 𝔼_Q[τ + 1]`.

## Implementation notes

The proof restarts the round, the e-process stopped at `τ`, on the fresh observations each time
it ends, and bets on the number of completed rounds with a geometric mixture. Within the first
`N` observations, the mixture over the rounds completed so far of the products of their payoffs
is an `N`-sample e-variable: under the i.i.d. law of a member of the null, the first `t`
observations are independent of the later ones. Its expected logarithm under `Q` is at most
`maxLogGrowth Q₁ S₁ N ≤ N * d`. A Wald argument shows that the rounds that start within the first
`N` observations use at least `N + 1` observations, hence that `(N + 1) / 𝔼_Q[τ + 1]` of them
start in expectation; letting `N → ∞` bounds the expected truncated logarithm of the payoff of a
round by `𝔼_Q[τ + 1] * d`. The payoff is first mixed with a constant `ε`, so that its logarithm
is bounded below, and the stopping time is first bounded by `k`; the truncation, `ε` and `k` are
removed at the end. The proof uses neither the law of large numbers nor the strong Markov
property: only the independence of the first `t` observations from the later ones, summed over
the values `t` of the restart times.

## References

* [ARR26] S. Agrawal, A. Ram and A. Ramdas, *On stopping times of power-one sequential tests:
  tight lower and upper bounds*, arXiv:2504.19952v2.
* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1.
-/

public section

open MeasureTheory Filter
open TauCeti.Probability (shift shift_iterate_apply shift_iterate_eq_reindex
  measurable_shift_iterate)
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}

/-! ### The observations after the first ones -/

/-- The shift by `t` observations preserves the i.i.d. law. -/
private lemma measurePreserving_shift_iterate (P : Measure 𝓧) [IsProbabilityMeasure P] (t : ℕ) :
    MeasurePreserving ((shift 𝓧)^[t]) (Measure.infinitePi fun _ : ℕ ↦ P)
      (Measure.infinitePi fun _ : ℕ ↦ P) := by
  refine ⟨measurable_shift_iterate t, ?_⟩
  rw [shift_iterate_eq_reindex]
  exact Measure.map_infinitePi_infinitePi_of_inj (add_left_injective t)

/-- Under an i.i.d. law, the first `t` observations are independent of the observations after
them. -/
private lemma indepFun_initSeg_shift_iterate (P : Measure 𝓧) [IsProbabilityMeasure P] (t : ℕ) :
    IndepFun (initSeg t) ((shift 𝓧)^[t]) (Measure.infinitePi fun _ : ℕ ↦ P) := by
  have h := (iIndepFun_infinitePi (P := fun _ : ℕ ↦ P) (X := fun _ x ↦ x)
    (fun _ ↦ measurable_id)).indepFun_set (Set.Iio t) (Set.Ici t)
    (Set.disjoint_left.2 fun i (hi : i < t) (hi' : t ≤ i) ↦ (not_lt.2 hi') hi)
    (fun i ↦ measurable_pi_apply i)
  rw [shift_iterate_eq_reindex, initSeg_def]
  exact h.comp (φ := fun (y : Set.Iio t → 𝓧) (i : Fin t) ↦ y ⟨i, i.2⟩)
    (ψ := fun (y : Set.Ici t → 𝓧) (i : ℕ) ↦ y ⟨i + t, Nat.le_add_left t i⟩)
    (by fun_prop) (by fun_prop)

/-- Under an i.i.d. law, a function of the first `t` observations is independent of a function of
the observations after them. -/
private lemma lintegral_mul_comp_shift_iterate (P : Measure 𝓧) [IsProbabilityMeasure P]
    {f g : (ℕ → 𝓧) → ℝ≥0∞} {t : ℕ} (hf : Measurable f) (hft : DependsOn f (Set.Iio t))
    (hg : Measurable g) :
    ∫⁻ ω, f ω * g ((shift 𝓧)^[t] ω) ∂Measure.infinitePi (fun _ : ℕ ↦ P) =
      (∫⁻ ω, f ω ∂Measure.infinitePi (fun _ : ℕ ↦ P)) *
        ∫⁻ ω, g ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) := by
  have := nonempty_of_isProbabilityMeasure P
  obtain ⟨F, hF, rfl⟩ := exists_measurable_eq_comp_initSeg hf hft
  rw [← (measurePreserving_shift_iterate P t).lintegral_comp hg]
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hF.comp (measurable_initSeg t))
    (hg.comp (measurable_shift_iterate t)) ((indepFun_initSeg_shift_iterate P t).comp hF hg)

/-- Under an i.i.d. law, a real function of the first `t` observations is independent of a real
function of the observations after them. -/
private lemma integral_mul_comp_shift_iterate (P : Measure 𝓧) [IsProbabilityMeasure P]
    {f g : (ℕ → 𝓧) → ℝ} {t : ℕ} (hf : Measurable f) (hft : DependsOn f (Set.Iio t))
    (hg : Measurable g) :
    ∫ ω, f ω * g ((shift 𝓧)^[t] ω) ∂Measure.infinitePi (fun _ : ℕ ↦ P) =
      (∫ ω, f ω ∂Measure.infinitePi (fun _ : ℕ ↦ P)) *
        ∫ ω, g ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) := by
  have := nonempty_of_isProbabilityMeasure P
  obtain ⟨F, hF, rfl⟩ := exists_measurable_eq_comp_initSeg hf hft
  have hmap : ∫ ω, g ((shift 𝓧)^[t] ω) ∂Measure.infinitePi (fun _ : ℕ ↦ P) =
      ∫ ω, g ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) := by
    rw [← integral_map (measurable_shift_iterate t).aemeasurable
      (by rw [(measurePreserving_shift_iterate P t).map_eq]; exact hg.aestronglyMeasurable),
      (measurePreserving_shift_iterate P t).map_eq]
  rw [← hmap]
  exact ((indepFun_initSeg_shift_iterate P t).comp hF hg).integral_fun_mul_eq_mul_integral
    (hF.comp (measurable_initSeg t)).aestronglyMeasurable
    (hg.comp (measurable_shift_iterate t)).aestronglyMeasurable

/-! ### Stopping times of the observations -/

section StoppingTime

variable {τ : (ℕ → 𝓧) → ℕ}

/-- A stopping time of the observations with values in `ℕ` is measurable. -/
private lemma measurable_of_isStoppingTime_nat
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) fun ω ↦ (τ ω : WithTop ℕ)) :
    Measurable τ := by
  convert (measurable_of_countable (WithTop.untopD 0)).comp hτ.measurable' using 1
  exact funext fun ω ↦ (WithTop.untopD_coe 0 (τ ω)).symm

/-- A stopping time of the observations with values in `ℕ` is determined by the observations up
to it. -/
private lemma eq_of_isStoppingTime_of_forall_le
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) fun ω ↦ (τ ω : WithTop ℕ))
    {ω ω' : ℕ → 𝓧} (h : ∀ i ≤ τ ω, ω i = ω' i) : τ ω' = τ ω := by
  have hm : MeasurableSet[Filtration.piLE (τ ω)] {ω' | τ ω' = τ ω} := by
    simpa using hτ.measurableSet_eq (τ ω)
  have hd : DependsOn ({ω' | τ ω' = τ ω}.indicator fun _ ↦ (1 : ℕ)) (Set.Iic (τ ω)) :=
    (measurable_const.indicator hm).dependsOn_of_piLE
  have h1 := hd fun i hi ↦ h i hi
  by_contra hne
  simp [Set.indicator, hne] at h1

/-- The minimum of a stopping time with values in `ℕ` and a constant is a stopping time. -/
private lemma isStoppingTime_min_nat
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) fun ω ↦ (τ ω : WithTop ℕ))
    (k : ℕ) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      fun ω ↦ ((min (τ ω) k : ℕ) : WithTop ℕ) := by
  have h : (fun ω ↦ ((min (τ ω) k : ℕ) : WithTop ℕ)) = fun ω ↦ min (τ ω : WithTop ℕ) k :=
    funext fun ω ↦ WithTop.coe_min _ _
  rw [h]
  exact hτ.min_natCast k

end StoppingTime

/-! ### Restarting a round on the fresh observations

A round is a pair of a duration `σ : (ℕ → 𝓧) → ℕ`, the number of observations that it uses, and a
payoff `V : (ℕ → 𝓧) → ℝ≥0∞`, both determined by the observations of the round. Restarting the
round on the fresh observations at its end gives the restart times `restartTime σ j` and the
products `restartPayoff σ V j` of the payoffs of the first `j` rounds. -/

/-- `f` is determined by the first `σ` observations: if `σ ω ≤ u` and `ω'` agrees with `ω` on the
first `u` observations, then `f ω' = f ω`. For `f = σ`, this says that `σ` is a stopping time
counted in observations. -/
private def DependsOnBefore {β : Type*} (σ : (ℕ → 𝓧) → ℕ) (f : (ℕ → 𝓧) → β) : Prop :=
  ∀ ⦃u : ℕ⦄ ⦃ω ω' : ℕ → 𝓧⦄, (∀ i < u, ω i = ω' i) → σ ω ≤ u → f ω' = f ω

section Restart

variable (σ : (ℕ → 𝓧) → ℕ) (V : (ℕ → 𝓧) → ℝ≥0∞)

/-- The number of observations used by the first `j` rounds, when a round that uses `σ ω`
observations is restarted on the fresh observations at its end. -/
private def restartTime : ℕ → (ℕ → 𝓧) → ℕ
  | 0 => fun _ ↦ 0
  | j + 1 => fun ω ↦ restartTime j ω + σ ((shift 𝓧)^[restartTime j ω] ω)

/-- The product of the payoffs `V` of the first `j` restarted rounds. -/
private noncomputable def restartPayoff : ℕ → (ℕ → 𝓧) → ℝ≥0∞
  | 0 => fun _ ↦ 1
  | j + 1 => fun ω ↦ restartPayoff j ω * V ((shift 𝓧)^[restartTime σ j ω] ω)

/-- The round after the first `j` ones is played on the observations after them. -/
private lemma restartTime_succ (j : ℕ) (ω : ℕ → 𝓧) :
    restartTime σ (j + 1) ω = restartTime σ j ω + σ ((shift 𝓧)^[restartTime σ j ω] ω) :=
  rfl

/-- The payoff of `j + 1` rounds is that of the first `j` times that of the next one. -/
private lemma restartPayoff_succ (j : ℕ) (ω : ℕ → 𝓧) :
    restartPayoff σ V (j + 1) ω =
      restartPayoff σ V j ω * V ((shift 𝓧)^[restartTime σ j ω] ω) :=
  rfl

/-- The restart times are nondecreasing in the number of rounds. -/
private lemma monotone_restartTime (ω : ℕ → 𝓧) : Monotone fun j ↦ restartTime σ j ω :=
  monotone_nat_of_le_succ fun _ ↦ Nat.le_add_right _ _

/-- If every round uses at least one observation, `j` rounds use at least `j` observations. -/
private lemma le_restartTime (hσ1 : ∀ ω, 1 ≤ σ ω) (j : ℕ) (ω : ℕ → 𝓧) :
    j ≤ restartTime σ j ω := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact Nat.add_le_add ih (hσ1 _)

/-- The first `j` rounds use the sum of their durations. -/
private lemma restartTime_eq_sum (j : ℕ) (ω : ℕ → 𝓧) :
    restartTime σ j ω = ∑ i ∈ Finset.range j, σ ((shift 𝓧)^[restartTime σ i ω] ω) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Finset.sum_range_succ, ← ih, restartTime_succ]

/-- The payoff of the first `j` rounds is the product of their payoffs. -/
private lemma restartPayoff_eq_prod (j : ℕ) (ω : ℕ → 𝓧) :
    restartPayoff σ V j ω = ∏ i ∈ Finset.range j, V ((shift 𝓧)^[restartTime σ i ω] ω) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Finset.prod_range_succ, ← ih, restartPayoff_succ]

variable {σ V}

/-- A measurable function of the observations after a measurable random number of them is
measurable. -/
private lemma measurable_comp_shift_iterate {β : Type*} [MeasurableSpace β]
    {h : (ℕ → 𝓧) → β} (hh : Measurable h) {T : (ℕ → 𝓧) → ℕ} (hT : Measurable T) :
    Measurable fun ω ↦ h ((shift 𝓧)^[T ω] ω) :=
  measurable_apply_of_countable (u := fun t ω ↦ h ((shift 𝓧)^[t] ω))
    (fun t ↦ hh.comp (measurable_shift_iterate t)) hT

/-- The restart times are measurable. -/
private lemma measurable_restartTime (hσm : Measurable σ) (j : ℕ) :
    Measurable (restartTime σ j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih => exact ih.add (measurable_comp_shift_iterate hσm ih)

/-- The products of the payoffs of the restarted rounds are measurable. -/
private lemma measurable_restartPayoff (hσm : Measurable σ) (hVm : Measurable V) (j : ℕ) :
    Measurable (restartPayoff σ V j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih => exact ih.mul (measurable_comp_shift_iterate hVm (measurable_restartTime hσm j))

/-- The first `j` rounds are determined by the observations that they use. -/
private lemma restartTime_eq_of_eqOn (hσ : DependsOnBefore σ σ) (j : ℕ) {t : ℕ}
    {ω ω' : ℕ → 𝓧} (h : ∀ i < t, ω i = ω' i) (hj : restartTime σ j ω ≤ t) :
    restartTime σ j ω' = restartTime σ j ω := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [restartTime_succ] at hj
    have h1 := ih (by omega)
    have hshift : ∀ i < t - restartTime σ j ω,
        (shift 𝓧)^[restartTime σ j ω] ω i = (shift 𝓧)^[restartTime σ j ω] ω' i := fun i hi ↦ by
      simp only [shift_iterate_apply]
      exact h _ (by omega)
    rw [restartTime_succ, restartTime_succ, h1, hσ hshift (by omega)]

/-- The payoffs of the first `j` rounds are determined by the observations that they use. -/
private lemma restartPayoff_eq_of_eqOn (hσ : DependsOnBefore σ σ) (hV : DependsOnBefore σ V)
    (j : ℕ) {t : ℕ} {ω ω' : ℕ → 𝓧} (h : ∀ i < t, ω i = ω' i) (hj : restartTime σ j ω ≤ t) :
    restartPayoff σ V j ω' = restartPayoff σ V j ω := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [restartTime_succ] at hj
    have h1 := restartTime_eq_of_eqOn hσ j h (by omega)
    have h2 := ih (by omega)
    have hshift : ∀ i < t - restartTime σ j ω,
        (shift 𝓧)^[restartTime σ j ω] ω i = (shift 𝓧)^[restartTime σ j ω] ω' i := fun i hi ↦ by
      simp only [shift_iterate_apply]
      exact h _ (by omega)
    rw [restartPayoff_succ, restartPayoff_succ, h1, h2, hV hshift (by omega)]

/-- Whether the first `j` rounds use exactly `t` observations is determined by the first `t`
observations. -/
private lemma restartTime_eq_iff_of_eqOn (hσ : DependsOnBefore σ σ) (j t : ℕ) {ω ω' : ℕ → 𝓧}
    (h : ∀ i < t, ω i = ω' i) : restartTime σ j ω' = t ↔ restartTime σ j ω = t :=
  ⟨fun h' ↦ (restartTime_eq_of_eqOn hσ j (fun i hi ↦ (h i hi).symm) h'.le).trans h',
    fun h' ↦ (restartTime_eq_of_eqOn hσ j h h'.le).trans h'⟩

/-- Whether the first `j` rounds use at most `N` observations is determined by the first `N`
observations. -/
private lemma restartTime_le_iff_of_eqOn (hσ : DependsOnBefore σ σ) (j N : ℕ) {ω ω' : ℕ → 𝓧}
    (h : ∀ i < N, ω i = ω' i) : restartTime σ j ω' ≤ N ↔ restartTime σ j ω ≤ N :=
  ⟨fun h' ↦ (restartTime_eq_of_eqOn hσ j (fun i hi ↦ (h i hi).symm) h') ▸ h',
    fun h' ↦ (restartTime_eq_of_eqOn hσ j h h').symm ▸ h'⟩

/-- On the event that the first `j` rounds use `t` observations, their payoff is a function of
the first `t` observations. -/
private lemma dependsOn_indicator_restartTime_eq (hσ : DependsOnBefore σ σ)
    (hV : DependsOnBefore σ V) (j t : ℕ) :
    DependsOn ({ω | restartTime σ j ω = t}.indicator (restartPayoff σ V j)) (Set.Iio t) := by
  intro ω ω' h
  have h' : ∀ i < t, ω i = ω' i := fun i hi ↦ h i hi
  by_cases hω : restartTime σ j ω = t
  · have hω' := (restartTime_eq_iff_of_eqOn hσ j t h').2 hω
    simp only [Set.indicator, Set.mem_ofPred_eq, hω, hω', ite_true]
    exact (restartPayoff_eq_of_eqOn hσ hV j h' hω.le).symm
  · have hω' : ¬ restartTime σ j ω' = t := mt (restartTime_eq_iff_of_eqOn hσ j t h').1 hω
    simp [Set.indicator, hω, hω']

/-- The indicator of the event that the first `i` rounds use `t` observations is a function of
the first `t` observations. -/
private lemma dependsOn_indicator_one_restartTime_eq (hσ : DependsOnBefore σ σ) (i t : ℕ) :
    DependsOn ({ω | restartTime σ i ω = t}.indicator (1 : (ℕ → 𝓧) → ℝ)) (Set.Iio t) := by
  intro ω ω' h
  have h' := restartTime_eq_iff_of_eqOn hσ i t (ω := ω) (ω' := ω') fun i hi ↦ h i hi
  by_cases hω : restartTime σ i ω = t
  · simp [Set.indicator, hω, h'.2 hω]
  · simp [Set.indicator, hω, mt h'.1 hω]

/-- On the event that the first `j` rounds use at most `N` observations, their payoff is a
function of the first `N` observations. -/
private lemma dependsOn_indicator_restartTime_le (hσ : DependsOnBefore σ σ)
    (hV : DependsOnBefore σ V) (j N : ℕ) :
    DependsOn ({ω | restartTime σ j ω ≤ N}.indicator (restartPayoff σ V j)) (Set.Iio N) := by
  intro ω ω' h
  have h' : ∀ i < N, ω i = ω' i := fun i hi ↦ h i hi
  by_cases hω : restartTime σ j ω ≤ N
  · have hω' := (restartTime_le_iff_of_eqOn hσ j N h').2 hω
    simp only [Set.indicator, Set.mem_ofPred_eq, hω, hω', ite_true]
    exact (restartPayoff_eq_of_eqOn hσ hV j h' hω).symm
  · have hω' : ¬ restartTime σ j ω' ≤ N := mt (restartTime_le_iff_of_eqOn hσ j N h').1 hω
    simp [Set.indicator, hω, hω']

/-- Summing the indicators of the events `{T = t}`, `t ≤ N`, gives the indicator of `{T ≤ N}`. -/
private lemma sum_indicator_eq_indicator_le {Ω M : Type*} [AddCommMonoid M] (T : Ω → ℕ)
    (f : Ω → M) (N : ℕ) (ω : Ω) :
    ∑ t ∈ Finset.range (N + 1), {ω | T ω = t}.indicator f ω = {ω | T ω ≤ N}.indicator f ω := by
  by_cases h : T ω ≤ N
  · rw [Finset.sum_eq_single (T ω), Set.indicator_of_mem (s := {ω | T ω ≤ N}) h,
      Set.indicator_of_mem (s := {x | T x = T ω}) rfl]
    · exact fun t _ ht ↦ Set.indicator_of_notMem (Ne.symm ht) _
    · exact fun hT ↦ absurd (Finset.mem_range.2 (Nat.lt_succ_of_le h)) hT
  · rw [Set.indicator_of_notMem h]
    refine Finset.sum_eq_zero fun t ht ↦ Set.indicator_of_notMem ?_ _
    rw [Finset.mem_range] at ht
    exact fun h' ↦ h (by rw [Set.mem_ofPred_eq] at h'; omega)

/-- The event that the first `j` rounds use at most `N` observations is measurable. -/
private lemma measurableSet_restartTime_le (hσm : Measurable σ) (j N : ℕ) :
    MeasurableSet {ω | restartTime σ j ω ≤ N} :=
  measurable_restartTime hσm j measurableSet_Iic

/-- The event that the first `j` rounds use exactly `t` observations is measurable. -/
private lemma measurableSet_restartTime_eq (hσm : Measurable σ) (j t : ℕ) :
    MeasurableSet {ω | restartTime σ j ω = t} :=
  measurable_restartTime hσm j (measurableSet_singleton t)

/-- The payoff of `j + 1` rounds within `N` observations, decomposed along the number `t` of
observations used by the first `j` rounds. -/
private lemma indicator_restartTime_succ_le (j N : ℕ) (ω : ℕ → 𝓧) :
    {ω | restartTime σ (j + 1) ω ≤ N}.indicator (restartPayoff σ V (j + 1)) ω =
      ∑ t ∈ Finset.range (N + 1),
        {ω | restartTime σ j ω = t}.indicator (restartPayoff σ V j) ω *
          {ω | σ ω ≤ N - t}.indicator V ((shift 𝓧)^[t] ω) := by
  have hterm (t : ℕ) : {ω | restartTime σ j ω = t}.indicator (restartPayoff σ V j) ω *
      {ω | σ ω ≤ N - t}.indicator V ((shift 𝓧)^[t] ω) =
        {ω | restartTime σ j ω = t}.indicator (fun ω' ↦ restartPayoff σ V j ω' *
          {x | σ x ≤ N - restartTime σ j ω'}.indicator V
            ((shift 𝓧)^[restartTime σ j ω'] ω')) ω := by
    by_cases h : restartTime σ j ω = t
    · rw [Set.indicator_of_mem (s := {x | restartTime σ j x = t}) h,
        Set.indicator_of_mem (s := {x | restartTime σ j x = t}) h, h]
    · rw [Set.indicator_of_notMem (s := {x | restartTime σ j x = t}) h,
        Set.indicator_of_notMem (s := {x | restartTime σ j x = t}) h, zero_mul]
  rw [Finset.sum_congr rfl fun t _ ↦ hterm t, sum_indicator_eq_indicator_le]
  simp only [Set.indicator, Set.mem_ofPred_eq, restartTime_succ, restartPayoff_succ]
  by_cases h1 : restartTime σ j ω ≤ N
  · by_cases h2 : σ ((shift 𝓧)^[restartTime σ j ω] ω) ≤ N - restartTime σ j ω
    · have h3 : restartTime σ j ω + σ ((shift 𝓧)^[restartTime σ j ω] ω) ≤ N := by omega
      simp only [h1, h2, h3, ↓reduceIte]
    · have h3 : ¬ restartTime σ j ω + σ ((shift 𝓧)^[restartTime σ j ω] ω) ≤ N := by omega
      simp only [h1, h2, h3, ↓reduceIte, mul_zero]
  · have h3 : ¬ restartTime σ j ω + σ ((shift 𝓧)^[restartTime σ j ω] ω) ≤ N := by omega
    simp only [h1, h3, ↓reduceIte]

/-- If the payoff of a round has expectation at most `1` on each event `{σ ≤ n}` under an i.i.d.
law, so has the product of the payoffs of `j` restarted rounds on each event that they use at most
`N` observations. -/
private lemma lintegral_indicator_restartPayoff_le_one (hσ : DependsOnBefore σ σ)
    (hV : DependsOnBefore σ V) (hσm : Measurable σ) (hVm : Measurable V)
    (P : Measure 𝓧) [IsProbabilityMeasure P]
    (h_null : ∀ n : ℕ,
      ∫⁻ ω, {ω | σ ω ≤ n}.indicator V ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1)
    (j N : ℕ) :
    ∫⁻ ω, {ω | restartTime σ j ω ≤ N}.indicator (restartPayoff σ V j) ω
      ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1 := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ P)
  induction j generalizing N with
  | zero =>
    calc ∫⁻ ω, {ω | restartTime σ 0 ω ≤ N}.indicator (restartPayoff σ V 0) ω ∂μ
    _ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun ω ↦ Set.indicator_le (fun _ _ ↦ le_rfl) ω
    _ = 1 := by simp
  | succ j ih =>
    have hf (t : ℕ) :
        Measurable ({ω | restartTime σ j ω = t}.indicator (restartPayoff σ V j)) :=
      (measurable_restartPayoff hσm hVm j).indicator
        (measurableSet_restartTime_eq hσm j t)
    have hg (t : ℕ) : Measurable ({ω | σ ω ≤ N - t}.indicator V) :=
      hVm.indicator (hσm measurableSet_Iic)
    calc ∫⁻ ω, {ω | restartTime σ (j + 1) ω ≤ N}.indicator (restartPayoff σ V (j + 1)) ω ∂μ
    _ = ∑ t ∈ Finset.range (N + 1),
          ∫⁻ ω, {ω | restartTime σ j ω = t}.indicator (restartPayoff σ V j) ω *
            {ω | σ ω ≤ N - t}.indicator V ((shift 𝓧)^[t] ω) ∂μ := by
      simp_rw [indicator_restartTime_succ_le]
      exact lintegral_finsetSum _ fun t _ ↦
        (hf t).mul ((hg t).comp (measurable_shift_iterate t))
    _ = ∑ t ∈ Finset.range (N + 1),
          (∫⁻ ω, {ω | restartTime σ j ω = t}.indicator (restartPayoff σ V j) ω ∂μ) *
            ∫⁻ ω, {ω | σ ω ≤ N - t}.indicator V ω ∂μ :=
      Finset.sum_congr rfl fun t _ ↦ lintegral_mul_comp_shift_iterate P (hf t)
        (dependsOn_indicator_restartTime_eq hσ hV j t) (hg t)
    _ ≤ ∑ t ∈ Finset.range (N + 1),
          ∫⁻ ω, {ω | restartTime σ j ω = t}.indicator (restartPayoff σ V j) ω ∂μ :=
      Finset.sum_le_sum fun t _ ↦ mul_le_of_le_one_right' (h_null _)
    _ = ∫⁻ ω, {ω | restartTime σ j ω ≤ N}.indicator (restartPayoff σ V j) ω ∂μ := by
      rw [← lintegral_finsetSum _ fun t _ ↦ hf t]
      exact lintegral_congr fun ω ↦ sum_indicator_eq_indicator_le _ _ N ω
    _ ≤ 1 := ih N

variable (σ V) in
/-- The geometric mixture, with weights `(1 - r) r ^ j`, of the products of the payoffs of the
first `j` rounds on the event that they use at most `N` observations. -/
private noncomputable def restartMixture (r : ℝ) (N : ℕ) (ω : ℕ → 𝓧) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal ((1 - r) * r ^ j) *
    {ω | restartTime σ j ω ≤ N}.indicator (restartPayoff σ V j) ω

/-- The mixture of restarted rounds is measurable. -/
private lemma measurable_restartMixture (hσm : Measurable σ) (hVm : Measurable V) (r : ℝ)
    (N : ℕ) : Measurable (restartMixture σ V r N) :=
  Finset.measurable_fun_sum _ fun j _ ↦ measurable_const.mul
    ((measurable_restartPayoff hσm hVm j).indicator
      (measurableSet_restartTime_le hσm j N))

/-- The mixture of the rounds completed within the first `N` observations is a function of the
first `N` observations. -/
private lemma dependsOn_restartMixture (hσ : DependsOnBefore σ σ) (hV : DependsOnBefore σ V)
    (r : ℝ) (N : ℕ) : DependsOn (restartMixture σ V r N) (Set.Iio N) := fun ω ω' h ↦
  Finset.sum_congr rfl fun j _ ↦ by rw [dependsOn_indicator_restartTime_le hσ hV j N h]

/-- The mixture of restarted rounds has expectation at most `1` under an i.i.d. law for which the
payoff of a round has expectation at most `1` on each event `{σ ≤ n}`. -/
private lemma lintegral_restartMixture_le_one (hσ : DependsOnBefore σ σ)
    (hV : DependsOnBefore σ V) (hσm : Measurable σ) (hVm : Measurable V) (P : Measure 𝓧)
    [IsProbabilityMeasure P]
    (h_null : ∀ n : ℕ,
      ∫⁻ ω, {ω | σ ω ≤ n}.indicator V ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (N : ℕ) :
    ∫⁻ ω, restartMixture σ V r N ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1 := by
  have hm (j : ℕ) :
      Measurable ({ω | restartTime σ j ω ≤ N}.indicator (restartPayoff σ V j)) :=
    (measurable_restartPayoff hσm hVm j).indicator
      (measurableSet_restartTime_le hσm j N)
  simp only [restartMixture]
  rw [lintegral_finsetSum _ fun j _ ↦ (hm j).const_mul _]
  calc ∑ j ∈ Finset.range (N + 1), ∫⁻ ω, ENNReal.ofReal ((1 - r) * r ^ j) *
        {ω | restartTime σ j ω ≤ N}.indicator (restartPayoff σ V j) ω
          ∂Measure.infinitePi (fun _ : ℕ ↦ P)
  _ = ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal ((1 - r) * r ^ j) *
        ∫⁻ ω, {ω | restartTime σ j ω ≤ N}.indicator (restartPayoff σ V j) ω
          ∂Measure.infinitePi (fun _ : ℕ ↦ P) :=
    Finset.sum_congr rfl fun j _ ↦ lintegral_const_mul _ (hm j)
  _ ≤ ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal ((1 - r) * r ^ j) :=
    Finset.sum_le_sum fun j _ ↦ mul_le_of_le_one_right'
      (lintegral_indicator_restartPayoff_le_one hσ hV hσm hVm P h_null j N)
  _ = ENNReal.ofReal (1 - r ^ (N + 1)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ mul_nonneg (by linarith) (pow_nonneg hr0 j),
      ← Finset.mul_sum, mul_neg_geom_sum]
  _ ≤ 1 := ENNReal.ofReal_le_one.2 (by have := pow_nonneg hr0 (N + 1); linarith)

variable (σ) in
/-- The number of rounds completed within the first `N` observations. -/
private def numRounds (N : ℕ) (ω : ℕ → 𝓧) : ℕ :=
  Nat.findGreatest (fun j ↦ restartTime σ j ω ≤ N) N

/-- At most `N` rounds are completed within `N` observations. -/
private lemma numRounds_le (N : ℕ) (ω : ℕ → 𝓧) : numRounds σ N ω ≤ N := Nat.findGreatest_le N

/-- The completed rounds use at most `N` observations. -/
private lemma restartTime_numRounds_le (N : ℕ) (ω : ℕ → 𝓧) :
    restartTime σ (numRounds σ N ω) ω ≤ N :=
  Nat.findGreatest_spec (P := fun j ↦ restartTime σ j ω ≤ N) (Nat.zero_le N) (Nat.zero_le N)

/-- For `i ≤ N`, the first `i` rounds use at most `N` observations if and only if they are among
the completed rounds. -/
private lemma restartTime_le_iff_le_numRounds {N i : ℕ} (hi : i ≤ N) (ω : ℕ → 𝓧) :
    restartTime σ i ω ≤ N ↔ i ≤ numRounds σ N ω :=
  ⟨fun h ↦ Nat.le_findGreatest hi h,
    fun h ↦ (monotone_restartTime σ ω h).trans (restartTime_numRounds_le N ω)⟩

/-- If every round uses at least one observation, the round after the completed ones ends after
the first `N` observations. -/
private lemma lt_restartTime_numRounds_succ (hσ1 : ∀ ω, 1 ≤ σ ω) (N : ℕ) (ω : ℕ → 𝓧) :
    N < restartTime σ (numRounds σ N ω + 1) ω := by
  by_cases hJ : numRounds σ N ω + 1 ≤ N
  · exact not_le.1 (Nat.findGreatest_is_greatest (P := fun j ↦ restartTime σ j ω ≤ N)
      (Nat.lt_succ_self _) hJ)
  · have hJN : numRounds σ N ω = N := le_antisymm (numRounds_le N ω) (by omega)
    rw [hJN]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (le_restartTime σ hσ1 (N + 1) ω)

/-- **Wald's argument, pointwise.** The durations of the rounds that start within the first `N`
observations add up to more than `N`. -/
private lemma add_one_le_sum_indicator (hσ1 : ∀ ω, 1 ≤ σ ω) (N : ℕ) (ω : ℕ → 𝓧) :
    (N + 1 : ℝ) ≤ ∑ i ∈ Finset.range (N + 1), {ω | restartTime σ i ω ≤ N}.indicator
      (fun ω ↦ (σ ((shift 𝓧)^[restartTime σ i ω] ω) : ℝ)) ω := by
  set J := numRounds σ N ω
  have hJN : J ≤ N := numRounds_le N ω
  have hJ : N + 1 ≤ restartTime σ (J + 1) ω := lt_restartTime_numRounds_succ hσ1 N ω
  calc (N + 1 : ℝ) ≤ (restartTime σ (J + 1) ω : ℝ) := by exact_mod_cast hJ
  _ = ∑ i ∈ Finset.range (J + 1), (σ ((shift 𝓧)^[restartTime σ i ω] ω) : ℝ) := by
    rw [restartTime_eq_sum, Nat.cast_sum]
  _ = ∑ i ∈ Finset.range (J + 1), {ω | restartTime σ i ω ≤ N}.indicator
      (fun ω ↦ (σ ((shift 𝓧)^[restartTime σ i ω] ω) : ℝ)) ω := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Set.indicator_of_mem]
    exact (restartTime_le_iff_le_numRounds ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans
      hJN) ω).2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 (Nat.succ_le_succ hJN))
    fun i _ _ ↦ Set.indicator_nonneg (fun _ _ ↦ Nat.cast_nonneg _) _

/-- **Wald's argument, in expectation.** Under an i.i.d. law, the observations after the first
`i` rounds are independent of the event that these rounds use at most `N` observations. -/
private lemma integral_indicator_comp_shift_restartTime (hσ : DependsOnBefore σ σ)
    (hσm : Measurable σ) (P : Measure 𝓧) [IsProbabilityMeasure P] {g : (ℕ → 𝓧) → ℝ}
    (hg : Measurable g) {C : ℝ} (hgC : ∀ ω, |g ω| ≤ C) (i N : ℕ) :
    ∫ ω, {ω | restartTime σ i ω ≤ N}.indicator
        (fun ω ↦ g ((shift 𝓧)^[restartTime σ i ω] ω)) ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) =
      (Measure.infinitePi (fun _ : ℕ ↦ P)).real {ω | restartTime σ i ω ≤ N} *
        ∫ ω, g ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ P)
  have hf (t : ℕ) : Measurable ({ω | restartTime σ i ω = t}.indicator (1 : (ℕ → 𝓧) → ℝ)) :=
    measurable_one.indicator (measurableSet_restartTime_eq hσm i t)
  have hfi (t : ℕ) : Integrable ({ω | restartTime σ i ω = t}.indicator (1 : (ℕ → 𝓧) → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_restartTime_eq hσm i t)
  have hfg (t : ℕ) : Integrable (fun ω ↦
      {ω | restartTime σ i ω = t}.indicator (1 : (ℕ → 𝓧) → ℝ) ω * g ((shift 𝓧)^[t] ω)) μ := by
    refine Integrable.of_bound
      ((hf t).mul (hg.comp (measurable_shift_iterate t))).aestronglyMeasurable C
      (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |{ω | restartTime σ i ω = t}.indicator (1 : (ℕ → 𝓧) → ℝ) ω| * |g ((shift 𝓧)^[t] ω)|
    _ ≤ 1 * C := by
      refine mul_le_mul ?_ (hgC _) (abs_nonneg _) zero_le_one
      by_cases h : restartTime σ i ω = t <;> simp [Set.indicator, h]
    _ = C := one_mul C
  have hsum (ω : ℕ → 𝓧) : {ω | restartTime σ i ω ≤ N}.indicator
      (fun ω ↦ g ((shift 𝓧)^[restartTime σ i ω] ω)) ω =
        ∑ t ∈ Finset.range (N + 1),
          {ω | restartTime σ i ω = t}.indicator (1 : (ℕ → 𝓧) → ℝ) ω * g ((shift 𝓧)^[t] ω) := by
    rw [← sum_indicator_eq_indicator_le]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    by_cases h : restartTime σ i ω = t
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, one_mul, h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  simp_rw [hsum]
  rw [integral_finsetSum _ fun t _ ↦ hfg t]
  calc ∑ t ∈ Finset.range (N + 1), ∫ ω,
        {ω | restartTime σ i ω = t}.indicator (1 : (ℕ → 𝓧) → ℝ) ω * g ((shift 𝓧)^[t] ω) ∂μ
  _ = ∑ t ∈ Finset.range (N + 1),
        (∫ ω, {ω | restartTime σ i ω = t}.indicator (1 : (ℕ → 𝓧) → ℝ) ω ∂μ) * ∫ ω, g ω ∂μ :=
    Finset.sum_congr rfl fun t _ ↦ integral_mul_comp_shift_iterate P (hf t)
      (dependsOn_indicator_one_restartTime_eq hσ i t) hg
  _ = μ.real {ω | restartTime σ i ω ≤ N} * ∫ ω, g ω ∂μ := by
    rw [← Finset.sum_mul, ← integral_finsetSum _ fun t _ ↦ hfi t]
    simp_rw [sum_indicator_eq_indicator_le]
    rw [integral_indicator_one (measurableSet_restartTime_le hσm i N)]

end Restart

/-! ### The truncated logarithm -/

/-- The logarithm truncated above at `c`, as a real number. -/
private noncomputable def truncLog (c : ℝ) (x : ℝ≥0∞) : ℝ := (min (ENNReal.log x) c).toReal

/-- The truncated logarithm is measurable. -/
private lemma measurable_truncLog (c : ℝ) : Measurable (truncLog c) :=
  measurable_ereal_toReal.comp (ENNReal.measurable_log.min measurable_const)

/-- The truncated logarithm of a positive finite number. -/
private lemma truncLog_of_ne {c : ℝ} {x : ℝ≥0∞} (h0 : x ≠ 0) (htop : x ≠ ∞) :
    truncLog c x = min (Real.log x.toReal) c := by
  rw [truncLog, ENNReal.log_pos_real h0 htop, ← EReal.coe_strictMono.monotone.map_min,
    EReal.toReal_coe]

/-- The truncated logarithm of `∞` is the truncation level. -/
private lemma truncLog_top (c : ℝ) : truncLog c ∞ = c := by simp [truncLog]

/-- The truncated logarithm is at most the truncation level. -/
private lemma truncLog_le {c : ℝ} {x : ℝ≥0∞} (h0 : x ≠ 0) : truncLog c x ≤ c := by
  by_cases htop : x = ∞
  · rw [htop, truncLog_top]
  · rw [truncLog_of_ne h0 htop]
    exact min_le_right _ _

/-- The truncated logarithm of `x ≥ δ` is at least `log δ`, if `log δ ≤ c`. -/
private lemma log_le_truncLog {c δ : ℝ} (hδ : 0 < δ) {x : ℝ≥0∞} (hx : ENNReal.ofReal δ ≤ x)
    (hc : Real.log δ ≤ c) : Real.log δ ≤ truncLog c x := by
  have h0 : x ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hδ) hx).ne'
  by_cases htop : x = ∞
  · rw [htop, truncLog_top]
    exact hc
  · rw [truncLog_of_ne h0 htop]
    exact le_min (Real.log_le_log hδ ((ENNReal.ofReal_le_iff_le_toReal htop).1 hx)) hc

/-- The truncated logarithm of `x ≥ δ` is bounded in absolute value, if `log δ ≤ c`. -/
private lemma abs_truncLog_le {c δ : ℝ} (hδ : 0 < δ) {x : ℝ≥0∞} (hx : ENNReal.ofReal δ ≤ x)
    (hc : Real.log δ ≤ c) : |truncLog c x| ≤ max |Real.log δ| |c| :=
  abs_le_max_abs_abs (log_le_truncLog hδ hx hc)
    (truncLog_le (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hδ) hx).ne')

/-- The exponential of the truncated logarithm of `x` is at most `x`. -/
private lemma ofReal_exp_truncLog_le {c : ℝ} {x : ℝ≥0∞} (h0 : x ≠ 0) :
    ENNReal.ofReal (Real.exp (truncLog c x)) ≤ x := by
  by_cases htop : x = ∞
  · rw [htop]
    exact le_top
  · rw [truncLog_of_ne h0 htop]
    calc ENNReal.ofReal (Real.exp (min (Real.log x.toReal) c))
    _ ≤ ENNReal.ofReal (Real.exp (Real.log x.toReal)) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (min_le_left _ _))
    _ = x := by
      rw [Real.exp_log (ENNReal.toReal_pos h0 htop), ENNReal.ofReal_toReal htop]

/-- Mixing a payoff with a constant: `min (log x) c ≤ truncLog c ((1 - ε) x + ε) - log (1 - ε)`. -/
private lemma min_log_le_truncLog_sub {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (c : ℝ) (x : ℝ≥0∞) :
    min (ENNReal.log x) c ≤
      ((truncLog c (ENNReal.ofReal (1 - ε) * x + ENNReal.ofReal ε) - Real.log (1 - ε) : ℝ) :
        EReal) := by
  have hlog : Real.log (1 - ε) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  by_cases h0 : x = 0
  · simp [h0]
  by_cases htop : x = ∞
  · have : ENNReal.ofReal (1 - ε) * x + ENNReal.ofReal ε = ∞ := by
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by linarith)).ne', top_add]
    rw [this, truncLog_top]
    exact (min_le_right _ _).trans (EReal.coe_le_coe_iff.2 (by linarith))
  have hε' : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.2 hε0).ne'
  have hV0 : ENNReal.ofReal (1 - ε) * x + ENNReal.ofReal ε ≠ 0 := by simp [hε']
  have hVtop : ENNReal.ofReal (1 - ε) * x + ENNReal.ofReal ε ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop, ENNReal.ofReal_ne_top⟩
  have hVreal : (ENNReal.ofReal (1 - ε) * x + ENNReal.ofReal ε).toReal =
      (1 - ε) * x.toReal + ε := by
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop) ENNReal.ofReal_ne_top,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hε0.le]
  rw [truncLog_of_ne hV0 hVtop, hVreal, ENNReal.log_pos_real h0 htop,
    ← EReal.coe_strictMono.monotone.map_min, EReal.coe_le_coe_iff]
  have hx : 0 < x.toReal := ENNReal.toReal_pos h0 htop
  have hL : Real.log (1 - ε) + Real.log x.toReal ≤ Real.log ((1 - ε) * x.toReal + ε) := by
    rw [← Real.log_mul (by linarith) hx.ne']
    exact Real.log_le_log (mul_pos (by linarith) hx) (by linarith)
  rw [← min_sub_sub_right]
  exact le_min ((min_le_left _ _).trans (by linarith)) ((min_le_right _ _).trans (by linarith))

/-! ### The Wald inequality for a round -/

section Wald

variable {σ : (ℕ → 𝓧) → ℕ} {V : (ℕ → 𝓧) → ℝ≥0∞}

/-- The logarithm of the mixture of restarted rounds is at least the logarithm of the weight of
the completed rounds plus their truncated log-payoffs, hence at least the sum of the truncated
log-payoffs of the rounds that start within the first `N` observations, up to `c` for the last
one and to the logarithm of the weights. -/
private lemma log_restartMixture_ge {δ : ℝ} (hδ : 0 < δ) (hVδ : ∀ ω, ENNReal.ofReal δ ≤ V ω)
    (c : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) (ω : ℕ → 𝓧) :
    ((Real.log (1 - r) + N * Real.log r - c + ∑ i ∈ Finset.range (N + 1),
        {ω | restartTime σ i ω ≤ N}.indicator
          (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω : ℝ) : EReal) ≤
      ENNReal.log (restartMixture σ V r N ω) := by
  set J := numRounds σ N ω
  set Y : ℕ → ℝ := fun i ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))
  have hV0 (ω : ℕ → 𝓧) : V ω ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hδ) (hVδ ω)).ne'
  have hJN : J ≤ N := numRounds_le N ω
  have hr' : 0 < 1 - r := by linarith
  -- the mixture is at least its term of index `J`
  have h1 : ENNReal.ofReal ((1 - r) * r ^ J * Real.exp (∑ i ∈ Finset.range J, Y i)) ≤
      restartMixture σ V r N ω := by
    calc ENNReal.ofReal ((1 - r) * r ^ J * Real.exp (∑ i ∈ Finset.range J, Y i))
    _ = ENNReal.ofReal ((1 - r) * r ^ J) *
          ∏ i ∈ Finset.range J, ENNReal.ofReal (Real.exp (Y i)) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hr'.le (pow_nonneg hr0.le J)), Real.exp_sum,
        ENNReal.ofReal_prod_of_nonneg fun i _ ↦ (Real.exp_pos _).le]
    _ ≤ ENNReal.ofReal ((1 - r) * r ^ J) * restartPayoff σ V J ω := by
      rw [restartPayoff_eq_prod]
      gcongr with i hi
      exact ofReal_exp_truncLog_le (hV0 _)
    _ = ENNReal.ofReal ((1 - r) * r ^ J) *
          {ω | restartTime σ J ω ≤ N}.indicator (restartPayoff σ V J) ω := by
      rw [Set.indicator_of_mem (restartTime_numRounds_le N ω)]
    _ ≤ restartMixture σ V r N ω :=
      Finset.single_le_sum (f := fun j ↦ ENNReal.ofReal ((1 - r) * r ^ j) *
        {ω | restartTime σ j ω ≤ N}.indicator (restartPayoff σ V j) ω)
        (fun _ _ ↦ bot_le) (Finset.mem_range.2 (Nat.lt_succ_of_le hJN))
  -- the logarithm of this term
  have hpos : 0 < (1 - r) * r ^ J * Real.exp (∑ i ∈ Finset.range J, Y i) := by
    have := pow_pos hr0 J
    have := Real.exp_pos (∑ i ∈ Finset.range J, Y i)
    positivity
  have h2 : Real.log ((1 - r) * r ^ J * Real.exp (∑ i ∈ Finset.range J, Y i)) =
      Real.log (1 - r) + J * Real.log r + ∑ i ∈ Finset.range J, Y i := by
    rw [Real.log_mul (mul_pos hr' (pow_pos hr0 J)).ne' (Real.exp_pos _).ne',
      Real.log_mul hr'.ne' (pow_pos hr0 J).ne', Real.log_pow, Real.log_exp]
  -- the sum over the rounds that start within the first `N` observations
  have h3 : ∑ i ∈ Finset.range (N + 1), {ω | restartTime σ i ω ≤ N}.indicator
      (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω =
        ∑ i ∈ Finset.range (J + 1), Y i := by
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_succ hJN))
      (fun i hi hiJ ↦ ?_) |>.symm.trans (Finset.sum_congr rfl fun i hi ↦ ?_) |>.symm
    · rw [Set.indicator_of_notMem]
      rw [Set.mem_ofPred_eq, restartTime_le_iff_le_numRounds
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
      exact fun h ↦ hiJ (Finset.mem_range.2 (Nat.lt_succ_of_le h))
    · rw [Set.indicator_of_mem]
      exact (restartTime_le_iff_le_numRounds
        ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hJN) ω).2
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  have h4 : Y J ≤ c := truncLog_le (hV0 _)
  have h5 : (N : ℝ) * Real.log r ≤ J * Real.log r :=
    mul_le_mul_of_nonpos_right (by exact_mod_cast hJN) (Real.log_nonpos hr0.le hr1.le)
  calc ((Real.log (1 - r) + N * Real.log r - c + ∑ i ∈ Finset.range (N + 1),
        {ω | restartTime σ i ω ≤ N}.indicator
          (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω : ℝ) : EReal)
  _ ≤ ((Real.log ((1 - r) * r ^ J * Real.exp (∑ i ∈ Finset.range J, Y i)) : ℝ) : EReal) := by
    rw [h2, h3, Finset.sum_range_succ]
    exact EReal.coe_le_coe_iff.2 (by linarith)
  _ = ENNReal.log (ENNReal.ofReal ((1 - r) * r ^ J * Real.exp (∑ i ∈ Finset.range J, Y i))) :=
    (ENNReal.log_ofReal_of_pos hpos).symm
  _ ≤ ENNReal.log (restartMixture σ V r N ω) := ENNReal.log_le_log h1

/-- The limit argument of the Wald inequality: if for every `r ∈ (0, 1)` and `N ≥ 1` some
`s ≥ (N + 1) / m` satisfies `log (1 - r) + N log r - c + A s ≤ N d`, then `A ≤ d m`. -/
private lemma le_mul_of_forall_restart {A c d m : ℝ} (hm : 0 < m) (hd : 0 ≤ d)
    (h : ∀ r : ℝ, 0 < r → r < 1 → ∀ N : ℕ, 1 ≤ N → ∃ s : ℝ,
      (N + 1 : ℝ) ≤ m * s ∧ Real.log (1 - r) + N * Real.log r - c + A * s ≤ N * d) :
    A ≤ d * m := by
  by_contra hlt
  rw [not_le] at hlt
  have hA : 0 < A := lt_of_le_of_lt (mul_nonneg hd hm.le) hlt
  set ε := A / m - d with hε
  have hε0 : 0 < ε := by
    rw [hε, sub_pos, lt_div_iff₀ hm]
    linarith
  set r := Real.exp (-(ε / 2)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hlogr : Real.log r = -(ε / 2) := Real.log_exp _
  obtain ⟨N, hN⟩ := exists_nat_gt ((c - Real.log (1 - r)) * 2 / ε)
  obtain ⟨s, hs1, hs2⟩ := h r hr0 hr1 (N + 1) (by omega)
  have hAs : A * (((N + 1 : ℕ) : ℝ) + 1) / m ≤ A * s := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hm).2 (by linarith [mul_comm m s])) hA.le
  have key : A * (((N + 1 : ℕ) : ℝ) + 1) / m = (((N + 1 : ℕ) : ℝ) + 1) * (d + ε) := by
    rw [hε]
    field_simp
    ring
  rw [key] at hAs
  rw [hlogr] at hs2
  have hN' : (c - Real.log (1 - r)) * 2 < N * ε := (div_lt_iff₀ hε0).1 hN
  push_cast at hs2 hAs
  nlinarith

/-- **The Wald inequality for a round.** Let `σ ≥ 1` be the bounded duration and `V ≥ δ > 0` the
payoff of a round, both determined by the observations of the round. If the payoff has
expectation at most `1` on each event `{σ ≤ n}` under the i.i.d. laws of the members of `S₁`,
then under the i.i.d. law of `Q₁` the expected logarithm of the payoff, truncated above at `c`, is
at most the bipolar rate times the expected duration. -/
private lemma integral_truncLog_le_bipolarRate_mul (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hσ : DependsOnBefore σ σ)
    (hV : DependsOnBefore σ V) (hσm : Measurable σ) (hVm : Measurable V) (hσ1 : ∀ ω, 1 ≤ σ ω)
    {K : ℕ} (hσK : ∀ ω, σ ω ≤ K)
    (h_null : ∀ P ∈ S₁, ∀ n : ℕ,
      ∫⁻ ω, {ω | σ ω ≤ n}.indicator V ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hVδ : ∀ ω, ENNReal.ofReal δ ≤ V ω) {c : ℝ} (hc : Real.log δ ≤ c)
    (hd : bipolarRate Q₁ S₁ ≠ ⊤) :
    ∫ ω, truncLog c (V ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤
      (bipolarRate Q₁ S₁).toReal * ∫ ω, (σ ω : ℝ) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  set m := ∫ ω, (σ ω : ℝ) ∂μ
  set A := ∫ ω, truncLog c (V ω) ∂μ
  have hd0 := bipolarRate_nonneg Q₁ S₁
  have hσm' : Measurable fun ω ↦ (σ ω : ℝ) := measurable_from_top.comp hσm
  have hσC (ω : ℕ → 𝓧) : |(σ ω : ℝ)| ≤ K := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hσK ω
  have hm1 : 1 ≤ m := by
    calc (1 : ℝ) = ∫ _, (1 : ℝ) ∂μ := by simp
    _ ≤ m := integral_mono (integrable_const _)
      (Integrable.of_bound hσm'.aestronglyMeasurable K (ae_of_all _ fun ω ↦ hσC ω))
      fun ω ↦ by exact_mod_cast hσ1 ω
  -- the truncated log-payoffs are bounded
  set C := max |Real.log δ| |c|
  have hYm : Measurable fun ω ↦ truncLog c (V ω) := (measurable_truncLog c).comp hVm
  have hT (i : ℕ) : Measurable (restartTime σ i) := measurable_restartTime hσm i
  refine le_mul_of_forall_restart (c := c) (by linarith) (EReal.toReal_nonneg hd0)
    fun r hr0 hr1 N hN ↦ ?_
  have hfm (i : ℕ) : Measurable fun ω ↦ {ω | restartTime σ i ω ≤ N}.indicator
      (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω :=
    (measurable_comp_shift_iterate hYm (hT i)).indicator (hT i measurableSet_Iic)
  have hfC (i : ℕ) (ω : ℕ → 𝓧) : |{ω | restartTime σ i ω ≤ N}.indicator
      (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω| ≤ C := by
    by_cases h : restartTime σ i ω ≤ N
    · rw [Set.indicator_of_mem h]
      exact abs_truncLog_le hδ (hVδ _) hc
    · rw [Set.indicator_of_notMem h, abs_zero]
      exact (abs_nonneg _).trans (le_max_left _ _)
  have hfi (i : ℕ) : Integrable (fun ω ↦ {ω | restartTime σ i ω ≤ N}.indicator
      (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω) μ :=
    Integrable.of_bound (hfm i).aestronglyMeasurable C
      (ae_of_all _ fun ω ↦ (Real.norm_eq_abs _).trans_le (hfC i ω))
  refine ⟨∑ i ∈ Finset.range (N + 1), μ.real {ω | restartTime σ i ω ≤ N}, ?_, ?_⟩
  · -- Wald's argument
    have hgm (i : ℕ) : Measurable fun ω ↦ {ω | restartTime σ i ω ≤ N}.indicator
        (fun ω ↦ (σ ((shift 𝓧)^[restartTime σ i ω] ω) : ℝ)) ω :=
      (measurable_comp_shift_iterate hσm' (hT i)).indicator (hT i measurableSet_Iic)
    have hgi (i : ℕ) : Integrable (fun ω ↦ {ω | restartTime σ i ω ≤ N}.indicator
        (fun ω ↦ (σ ((shift 𝓧)^[restartTime σ i ω] ω) : ℝ)) ω) μ := by
      refine Integrable.of_bound (hgm i).aestronglyMeasurable K (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs]
      by_cases h : restartTime σ i ω ≤ N
      · rw [Set.indicator_of_mem h]
        exact hσC _
      · rw [Set.indicator_of_notMem h, abs_zero]
        exact Nat.cast_nonneg _
    calc (N + 1 : ℝ) = ∫ _, (N + 1 : ℝ) ∂μ := by simp
    _ ≤ ∫ ω, ∑ i ∈ Finset.range (N + 1), {ω | restartTime σ i ω ≤ N}.indicator
          (fun ω ↦ (σ ((shift 𝓧)^[restartTime σ i ω] ω) : ℝ)) ω ∂μ :=
      integral_mono (integrable_const _) (integrable_finsetSum _ fun i _ ↦ hgi i)
        fun ω ↦ add_one_le_sum_indicator hσ1 N ω
    _ = ∑ i ∈ Finset.range (N + 1), μ.real {ω | restartTime σ i ω ≤ N} * m := by
      rw [integral_finsetSum _ fun i _ ↦ hgi i]
      exact Finset.sum_congr rfl fun i _ ↦
        integral_indicator_comp_shift_restartTime hσ hσm Q₁ hσm' hσC i N
    _ = m * ∑ i ∈ Finset.range (N + 1), μ.real {ω | restartTime σ i ω ≤ N} := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  · -- the logarithmic bound
    set B := Real.log (1 - r) + N * Real.log r - c
    have hsum : Integrable (fun ω ↦ ∑ i ∈ Finset.range (N + 1),
        {ω | restartTime σ i ω ≤ N}.indicator
          (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω) μ :=
      integrable_finsetSum _ fun i _ ↦ hfi i
    have hint : Integrable (fun ω ↦ B + ∑ i ∈ Finset.range (N + 1),
        {ω | restartTime σ i ω ≤ N}.indicator
          (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω) μ :=
      (integrable_const B).add hsum
    have hval : ∫ ω, B + ∑ i ∈ Finset.range (N + 1), {ω | restartTime σ i ω ≤ N}.indicator
          (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω ∂μ =
        B + A * ∑ i ∈ Finset.range (N + 1), μ.real {ω | restartTime σ i ω ≤ N} := by
      rw [integral_add (integrable_const B) hsum, integral_finsetSum _ fun i _ ↦ hfi i,
        Finset.mul_sum]
      simp only [integral_const, probReal_univ, one_smul]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ (integral_indicator_comp_shift_restartTime hσ hσm Q₁
        hYm (fun ω ↦ abs_truncLog_le hδ (hVδ ω) hc) i N).trans (mul_comm _ _)
    have hle : ((B + A * ∑ i ∈ Finset.range (N + 1), μ.real {ω | restartTime σ i ω ≤ N} : ℝ) :
        EReal) ≤ (N : EReal) * bipolarRate Q₁ S₁ := by
      rw [← hval, ← eintegral_eq_integral hint]
      calc ∫ᵉ ω, ((B + ∑ i ∈ Finset.range (N + 1), {ω | restartTime σ i ω ≤ N}.indicator
            (fun ω ↦ truncLog c (V ((shift 𝓧)^[restartTime σ i ω] ω))) ω : ℝ) : EReal) ∂μ
      _ ≤ ∫ᵉ ω, ENNReal.log (restartMixture σ V r N ω) ∂μ :=
        eintegral_mono fun ω ↦ log_restartMixture_ge hδ hVδ c hr0 hr1 N ω
      _ ≤ maxLogGrowth Q₁ S₁ N :=
        eintegral_log_le_maxLogGrowth_of_dependsOn Q₁ hS₁ (measurable_restartMixture hσm hVm r N)
          (dependsOn_restartMixture hσ hV r N) fun P hP ↦ by
            have := hS₁ P hP
            exact lintegral_restartMixture_le_one hσ hV hσm hVm P (h_null P hP) hr0.le hr1.le N
      _ ≤ N * bipolarRate Q₁ S₁ := maxLogGrowth_le_mul_bipolarRate Q₁ S₁ (by omega)
    rw [← EReal.coe_toReal hd (ne_bot_of_le_ne_bot EReal.zero_ne_bot hd0), ← EReal.coe_natCast,
      ← EReal.coe_mul, EReal.coe_le_coe_iff] at hle
    exact hle

end Wald

/-! ### Extended integrals -/

/-- **Monotone convergence for truncations.** If the extended integrals of the truncations
`min f k`, `k ∈ ℕ`, are at most `D`, so is the extended integral of `f`. -/
private lemma eintegral_le_of_forall_min_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → EReal} (hf : Measurable f) {D : EReal}
    (h : ∀ k : ℕ, ∫ᵉ x, min (f x) k ∂μ ≤ D) : ∫ᵉ x, f x ∂μ ≤ D := by
  have hmono : Monotone EReal.toENNReal := fun _ _ h ↦ EReal.toENNReal_le_toENNReal h
  have hpos (k : ℕ) (x : Ω) : (min (f x) k).toENNReal = min (f x).toENNReal k := by
    rw [hmono.map_min, show ((k : EReal)) = ((k : ℝ≥0∞) : EReal) by simp, EReal.toENNReal_coe]
  have hneg (k : ℕ) (x : Ω) : (-min (f x) k).toENNReal = (-f x).toENNReal := by
    by_cases hk : f x ≤ k
    · rw [min_eq_left hk]
    · rw [not_le] at hk
      have hk0 : (0 : EReal) ≤ k := by exact_mod_cast Nat.zero_le k
      rw [min_eq_right hk.le, EReal.toENNReal_of_nonpos (by simp),
        EReal.toENNReal_of_nonpos (by simpa using hk0.trans hk.le)]
  have h' (k : ℕ) : ((∫⁻ x, min (f x).toENNReal k ∂μ : ℝ≥0∞) : EReal) -
      ((∫⁻ x, (-f x).toENNReal ∂μ : ℝ≥0∞) : EReal) ≤ D := by
    have := h k
    simp only [eintegral, hpos, hneg] at this
    exact this
  have hm (k : ℕ) : Measurable fun x ↦ min (f x).toENNReal (k : ℝ≥0∞) :=
    (measurable_ereal_toENNReal.comp hf).min measurable_const
  have hmono' : Monotone fun (k : ℕ) x ↦ min (f x).toENNReal (k : ℝ≥0∞) :=
    fun k k' hkk' x ↦ min_le_min_left _ (by exact_mod_cast hkk')
  have hsup : ∫⁻ x, (f x).toENNReal ∂μ = ⨆ k : ℕ, ∫⁻ x, min (f x).toENNReal k ∂μ := by
    rw [← lintegral_iSup hm hmono']
    refine lintegral_congr fun x ↦ le_antisymm ?_ (iSup_le fun k ↦ min_le_left _ _)
    by_cases hx : (f x).toENNReal = ∞
    · simp [hx, ENNReal.iSup_natCast]
    · obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hx
      exact le_iSup_of_le k (min_eq_left hk.le).ge
  rw [eintegral, hsup]
  set b := ∫⁻ x, (-f x).toENNReal ∂μ
  by_cases hb : b = ∞
  · rw [hb, EReal.coe_ennreal_top, EReal.sub_top]
    exact bot_le
  have hb' : (b : EReal) ≠ ⊤ := by simpa using hb
  have hb'' : (b : EReal) ≠ ⊥ := by simp
  rw [EReal.sub_le_iff_le_add (.inl hb'') (.inl hb')]
  have hk (k : ℕ) : ((∫⁻ x, min (f x).toENNReal k ∂μ : ℝ≥0∞) : EReal) ≤ D + b :=
    (EReal.sub_le_iff_le_add (.inl hb'') (.inl hb')).1 (h' k)
  have hD : 0 ≤ D + b := (EReal.coe_ennreal_nonneg _).trans (hk 0)
  rw [← EReal.coe_toENNReal hD] at hk ⊢
  exact EReal.coe_ennreal_le_coe_ennreal_iff.2
    (iSup_le fun k ↦ EReal.coe_ennreal_le_coe_ennreal_iff.1 (hk k))

/-- A bound `x ≤ D + η` for every `η > 0` gives `x ≤ D`. -/
private lemma le_coe_of_forall_pos_le_coe_add {x : EReal} {D : ℝ}
    (h : ∀ η : ℝ, 0 < η → x ≤ ↑(D + η)) : x ≤ D := by
  refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ ?_
  obtain ⟨r, hDr, hra⟩ := EReal.lt_iff_exists_real_btwn.1 ha
  calc x ≤ ↑(D + (r - D)) := h _ (by exact_mod_cast sub_pos.2 (EReal.coe_lt_coe_iff.1 hDr))
  _ = r := by rw [add_sub_cancel]
  _ ≤ a := hra.le

/-! ### The Wald inequality for e-processes -/

section EProcess

variable {E : ℕ → (ℕ → 𝓧) → ℝ≥0∞} {τ : (ℕ → 𝓧) → ℕ}

/-- The Wald inequality for the payoff `(1 - ε) E_τ + ε`, truncated above at `c`: apply the Wald
inequality for a round to the e-process stopped at `min τ k`, and let `k` tend to infinity. The
bound `D` is that of the Wald inequality for the stopping times `min τ k`. -/
private lemma integral_truncLog_stoppedValue_le (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hE : IsEProcess E (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁))
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) fun ω ↦ (τ ω : WithTop ℕ))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {c : ℝ} (hc : Real.log ε ≤ c)
    (hd : bipolarRate Q₁ S₁ ≠ ⊤) {D : ℝ}
    (hD : ∀ k : ℕ, (bipolarRate Q₁ S₁).toReal *
      ∫ ω, ((min (τ ω) k + 1 : ℕ) : ℝ) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤ D) :
    ∫ ω, truncLog c (ENNReal.ofReal (1 - ε) * E (τ ω) ω + ENNReal.ofReal ε)
      ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤ D := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  set V : ℕ → (ℕ → 𝓧) → ℝ≥0∞ := fun k ω ↦
    ENNReal.ofReal (1 - ε) * E (min (τ ω) k) ω + ENNReal.ofReal ε
  have hτk (k : ℕ) := isStoppingTime_min_nat hτ k
  have hVm (k : ℕ) : Measurable (V k) :=
    (measurable_const.mul (hE.measurable_stoppedValue (hτk k))).add measurable_const
  have hVε (k : ℕ) (ω : ℕ → 𝓧) : ENNReal.ofReal ε ≤ V k ω := le_add_self
  -- the Wald inequality for the round stopped at `min τ k`
  have hk (k : ℕ) : ∫ ω, truncLog c (V k ω) ∂μ ≤ D := by
    refine (integral_truncLog_le_bipolarRate_mul (σ := fun ω ↦ min (τ ω) k + 1) Q₁ hS₁ ?_ ?_
      ((measurable_of_isStoppingTime_nat (hτk k)).add_const 1) (hVm k) (fun _ ↦ le_add_self)
      (K := k + 1) (fun ω ↦ by simp) ?_ hε0 (hVε k) hc hd).trans ?_
    · intro u ω ω' h hle
      simp only at hle ⊢
      rw [eq_of_isStoppingTime_of_forall_le (hτk k) fun i hi ↦ h i (by omega)]
    · intro u ω ω' h hle
      simp only at hle
      have h' : ∀ i ≤ min (τ ω) k, ω i = ω' i := fun i hi ↦ h i (by omega)
      simp only [V, eq_of_isStoppingTime_of_forall_le (hτk k) h',
        ((hE.adapted (min (τ ω) k)).dependsOn_of_piLE fun i hi ↦ h' i hi).symm]
    · intro P hP n
      have := hS₁ P hP
      have hPS : Measure.infinitePi (fun _ : ℕ ↦ P) ∈
          (fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁ := ⟨P, hP, rfl⟩
      calc ∫⁻ ω, {ω | min (τ ω) k + 1 ≤ n}.indicator (V k) ω ∂Measure.infinitePi (fun _ ↦ P)
      _ ≤ ∫⁻ ω, ENNReal.ofReal (1 - ε) * E (min (min (τ ω) k) (n - 1)) ω + ENNReal.ofReal ε
          ∂Measure.infinitePi (fun _ ↦ P) := by
        refine lintegral_mono fun ω ↦ ?_
        by_cases hω : min (τ ω) k + 1 ≤ n
        · rw [Set.indicator_of_mem hω, min_eq_left (by omega : min (τ ω) k ≤ n - 1)]
        · rw [Set.indicator_of_notMem hω]
          exact bot_le
      _ = ENNReal.ofReal (1 - ε) * ∫⁻ ω, E (min (min (τ ω) k) (n - 1)) ω
          ∂Measure.infinitePi (fun _ ↦ P) + ENNReal.ofReal ε := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul _
          (hE.measurable_stoppedValue (isStoppingTime_min_nat (hτk k) (n - 1))), lintegral_const,
          measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (1 - ε) * 1 + ENNReal.ofReal ε := by
        gcongr
        exact hE.lintegral_le_one (isStoppingTime_min_nat (hτk k) (n - 1)) hPS
      _ = 1 := by
        rw [mul_one, ← ENNReal.ofReal_add (by linarith) hε0.le, sub_add_cancel,
          ENNReal.ofReal_one]
    · exact hD k
  -- let `k` tend to infinity
  refine le_of_tendsto' (tendsto_integral_of_dominated_convergence (fun _ ↦ max |Real.log ε| |c|)
    (fun k ↦ ((measurable_truncLog c).comp (hVm k)).aestronglyMeasurable) (integrable_const _)
    (fun k ↦ ae_of_all _ fun ω ↦ (Real.norm_eq_abs _).trans_le
      (abs_truncLog_le hε0 (hVε k ω) hc)) (ae_of_all _ fun ω ↦ ?_)) hk
  exact tendsto_atTop_of_eventually_const (i₀ := τ ω) fun k hk ↦ by simp [V, min_eq_left hk]

/-- The Wald inequality when the bipolar rate is finite and either it is `0` or the expected
number of observations is finite: the expected logarithm of `E_τ` is at most the real number
`d * 𝔼[τ + 1]`. -/
private lemma eintegral_log_stoppedValue_le_toReal_mul (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hE : IsEProcess E (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁))
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) fun ω ↦ (τ ω : WithTop ℕ))
    (hd : bipolarRate Q₁ S₁ ≠ ⊤)
    (hdm : bipolarRate Q₁ S₁ = 0 ∨
      ∫⁻ ω, (τ ω : ℝ≥0∞) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≠ ∞) :
    ∫ᵉ ω, ENNReal.log (E (τ ω) ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤
      (((bipolarRate Q₁ S₁).toReal *
        (∫⁻ ω, (τ ω : ℝ≥0∞) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)).toReal : ℝ) : EReal) := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  set m := ∫⁻ ω, (τ ω : ℝ≥0∞) + 1 ∂μ
  set D := (bipolarRate Q₁ S₁).toReal * m.toReal
  have hτm := measurable_of_isStoppingTime_nat hτ
  have hEτm : Measurable fun ω ↦ E (τ ω) ω := hE.measurable_stoppedValue hτ
  have hD (k : ℕ) : (bipolarRate Q₁ S₁).toReal * ∫ ω, ((min (τ ω) k + 1 : ℕ) : ℝ) ∂μ ≤ D := by
    rcases hdm with hd0 | hm
    · simp [D, hd0]
    refine mul_le_mul_of_nonneg_left ?_ (EReal.toReal_nonneg (bipolarRate_nonneg Q₁ S₁))
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ Nat.cast_nonneg _)
      ((measurable_from_top.comp ((hτm.min measurable_const).add_const 1)).aestronglyMeasurable)]
    refine ENNReal.toReal_mono hm (lintegral_mono fun ω ↦ ?_)
    rw [ENNReal.ofReal_natCast]
    push_cast
    gcongr
    exact_mod_cast min_le_left _ _
  have step (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (k : ℕ) :
      ∫ᵉ ω, min (ENNReal.log (E (τ ω) ω)) k ∂μ ≤ ((D - Real.log (1 - ε) : ℝ) : EReal) := by
    set W : (ℕ → 𝓧) → ℝ≥0∞ := fun ω ↦ ENNReal.ofReal (1 - ε) * E (τ ω) ω + ENNReal.ofReal ε
    have hc : Real.log ε ≤ k := (Real.log_neg hε0 hε1).le.trans (Nat.cast_nonneg k)
    have hYi : Integrable (fun ω ↦ truncLog k (W ω)) μ :=
      Integrable.of_bound ((measurable_truncLog _).comp
        ((measurable_const.mul hEτm).add measurable_const)).aestronglyMeasurable
        (max |Real.log ε| |(k : ℝ)|) (ae_of_all _ fun ω ↦ (Real.norm_eq_abs _).trans_le
          (abs_truncLog_le hε0 le_add_self hc))
    calc ∫ᵉ ω, min (ENNReal.log (E (τ ω) ω)) k ∂μ
    _ ≤ ∫ᵉ ω, ((truncLog k (W ω) - Real.log (1 - ε) : ℝ) : EReal) ∂μ :=
      eintegral_mono fun ω ↦ by simpa using min_log_le_truncLog_sub hε0 hε1 k (E (τ ω) ω)
    _ = ((∫ ω, truncLog k (W ω) ∂μ - Real.log (1 - ε) : ℝ) : EReal) := by
      have hYi' : Integrable (fun ω ↦ truncLog k (W ω) - Real.log (1 - ε)) μ :=
        hYi.sub (integrable_const _)
      rw [eintegral_eq_integral hYi',
        integral_sub hYi (integrable_const _), integral_const, probReal_univ, one_smul]
    _ ≤ ((D - Real.log (1 - ε) : ℝ) : EReal) := EReal.coe_le_coe_iff.2 (by
      linarith [integral_truncLog_stoppedValue_le Q₁ hS₁ hE hτ hε0 hε1 hc hd hD])
  refine eintegral_le_of_forall_min_le (ENNReal.measurable_log.comp hEτm) fun k ↦ ?_
  refine le_coe_of_forall_pos_le_coe_add fun η hη ↦ ?_
  have hexp : Real.exp (-η) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h := step (1 - Real.exp (-η)) (by linarith) (by linarith [Real.exp_pos (-η)]) k
  rwa [sub_sub_cancel, Real.log_exp, sub_neg_eq_add] at h

end EProcess

/-- **The Wald inequality at the bipolar rate.** For an e-process `E` for the i.i.d. laws of the
members of `S₁` and a stopping time `τ` with values in `ℕ`, the expected logarithm of `E` at `τ`
under the i.i.d. law of `Q₁` is at most the expected number `τ + 1` of observations times the
bipolar rate. The expected number of observations may be infinite, with `∞ * 0 = 0`: if the
bipolar rate is `0`, the expected logarithm is nonpositive at every stopping time. The expected
logarithm is Statlib's extended integral, which is `⊥` when the positive and negative parts of
the logarithm have infinite integrals. `Q₁` need not be a probability measure: otherwise its
i.i.d. law is `0` and both sides are `0`. -/
theorem IsEProcess.eintegral_log_stoppedValue_le_mul_bipolarRate (Q₁ : Measure 𝓧)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {E : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hE : IsEProcess E (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁))
    {τ : (ℕ → 𝓧) → ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) fun ω ↦ (τ ω : WithTop ℕ)) :
    ∫ᵉ ω, ENNReal.log (E (τ ω) ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤
      ((∫⁻ ω, (τ ω : ℝ≥0∞) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) : ℝ≥0∞) : EReal) *
        bipolarRate Q₁ S₁ := by
  by_cases hQ : IsProbabilityMeasure Q₁
  swap
  · simp [Measure.infinitePi, hQ]
  set m := ∫⁻ ω, (τ ω : ℝ≥0∞) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  have hm0 : (0 : EReal) < m := by
    have : (1 : ℝ≥0∞) ≤ m :=
      calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by simp
      _ ≤ m := lintegral_mono fun ω ↦ le_add_self
    exact EReal.coe_ennreal_pos.2 (zero_lt_one.trans_le this)
  by_cases hdtop : bipolarRate Q₁ S₁ = ⊤
  · rw [hdtop, EReal.mul_top_of_pos hm0]
    exact le_top
  rcases (bipolarRate_nonneg Q₁ S₁).eq_or_lt with hd | hd
  · rw [← hd, mul_zero]
    simpa [← hd] using eintegral_log_stoppedValue_le_toReal_mul Q₁ hS₁ hE hτ hdtop (.inl hd.symm)
  by_cases hm : m = ∞
  · rw [hm, EReal.coe_ennreal_top, EReal.top_mul_of_pos hd]
    exact le_top
  refine (eintegral_log_stoppedValue_le_toReal_mul Q₁ hS₁ hE hτ hdtop (.inr hm)).trans_eq ?_
  rw [EReal.coe_mul, EReal.coe_toReal hdtop (ne_bot_of_gt hd), EReal.coe_ennreal_toReal hm,
    mul_comm]

/-! ### Expected stopping times of sequential tests -/

section Test

variable {τ : (ℕ → 𝓧) → WithTop ℕ}

/-- The lower bound for a level `a > 0` and a finite expected number of observations, up to a term
`- log (1 - ε)`: the Wald inequality for the e-process `ε + (1 - ε) a⁻¹ 𝟙{τ ≤ n}` at the
stopping times `min τ k`, as `k → ∞`. -/
private lemma neg_log_le_toReal_mul_sub (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) τ) {a : ℝ} (ha0 : 0 < a)
    (h_level : ∀ P ∈ S₁, Measure.infinitePi (fun _ : ℕ ↦ P) {ω | τ ω ≠ ⊤} ≤ ENNReal.ofReal a)
    (hd : bipolarRate Q₁ S₁ ≠ ⊤)
    (hm : ∫⁻ ω, ENat.toENNReal (τ ω) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≠ ∞)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    -Real.log a ≤ (bipolarRate Q₁ S₁).toReal *
      (∫⁻ ω, ENat.toENNReal (τ ω) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)).toReal -
        Real.log (1 - ε) := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  set m := ∫⁻ ω, ENat.toENNReal (τ ω) + 1 ∂μ
  set D := (bipolarRate Q₁ S₁).toReal * m.toReal
  have hd0 := bipolarRate_nonneg Q₁ S₁
  have hτm := hτ.measurable_enat
  have hτle (k : ℕ) : MeasurableSet {ω | τ ω ≤ k} :=
    Filtration.le _ k _ (hτ.measurableSet_le_natCast k)
  have hτtop : MeasurableSet {ω | τ ω ≠ ⊤} := (hτm (measurableSet_singleton ⊤)).compl
  -- `τ` is almost surely finite under the i.i.d. law of `Q₁`
  have hae : ∀ᵐ ω ∂μ, τ ω ≠ ⊤ := by
    filter_upwards [ae_lt_top (f := fun ω ↦ ENat.toENNReal (τ ω) + 1)
      ((measurable_from_top.comp hτm).add_const 1) hm] with ω hω
    exact ENat.toENNReal_ne_top.1 (ne_top_of_lt (lt_of_le_of_lt le_self_add hω))
  -- the stopping times `min τ k`, with values in `ℕ`
  set τk : ℕ → (ℕ → 𝓧) → ℕ := fun k ω ↦ ENat.toNat (min (τ ω) k)
  have hτk_coe (k : ℕ) (ω : ℕ → 𝓧) : ((τk k ω : ℕ) : WithTop ℕ) = min (τ ω) k :=
    ENat.natCast_toNat (ne_top_of_le_ne_top (WithTop.natCast_ne_top k) (min_le_right _ _))
  have hτk (k : ℕ) : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      fun ω ↦ (τk k ω : WithTop ℕ) := by
    rw [show (fun ω ↦ (τk k ω : WithTop ℕ)) = fun ω ↦ min (τ ω) k from funext (hτk_coe k)]
    exact hτ.min_natCast k
  have hmk (k : ℕ) : ∫⁻ ω, (τk k ω : ℝ≥0∞) + 1 ∂μ ≤ m := lintegral_mono fun ω ↦ by
    gcongr
    have h : ((τk k ω : ℕ) : ℕ∞) ≤ τ ω := (hτk_coe k ω).trans_le (min_le_left _ _)
    exact_mod_cast ENat.toENNReal_le.2 h
  -- the e-process `ε + (1 - ε) a⁻¹ 𝟙{τ ≤ n}`
  have hb0 : 0 < (1 - ε) / a := div_pos (by linarith) ha0
  set b := ENNReal.ofReal ((1 - ε) / a)
  set L := Real.log (ε + (1 - ε) / a)
  set E : ℕ → (ℕ → 𝓧) → ℝ≥0∞ := fun n ω ↦
    ENNReal.ofReal ε + {ω | τ ω ≤ n}.indicator (fun _ ↦ b) ω
  have hE : IsEProcess E (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁) := by
    refine IsEProcess.of_lintegral_le_one ?_ (fun n ↦
      (measurable_const.indicator (hτ.measurableSet_le_natCast n)).const_add _)
      fun σ _ _ hP ↦ ?_
    · rintro _ ⟨P, hP, rfl⟩
      have := hS₁ P hP
      infer_instance
    obtain ⟨P, hP, rfl⟩ := hP
    have := hS₁ P hP
    calc ∫⁻ ω, E (σ ω) ω ∂Measure.infinitePi (fun _ ↦ P)
    _ ≤ ∫⁻ ω, ENNReal.ofReal ε + {ω | τ ω ≠ ⊤}.indicator (fun _ ↦ b) ω
        ∂Measure.infinitePi (fun _ ↦ P) :=
      lintegral_mono fun ω ↦ add_le_add le_rfl (Set.indicator_le_indicator_of_subset
        (s := {x | τ x ≤ σ ω}) (t := {x | τ x ≠ ⊤})
        (fun x hx ↦ ne_top_of_le_ne_top (WithTop.natCast_ne_top _) hx) (fun _ ↦ bot_le) ω)
    _ = ENNReal.ofReal ε + b * Measure.infinitePi (fun _ ↦ P) {ω | τ ω ≠ ⊤} := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_indicator_const hτtop]
    _ ≤ ENNReal.ofReal ε + b * ENNReal.ofReal a := by
      gcongr
      exact h_level P hP
    _ = 1 := by
      rw [← ENNReal.ofReal_mul hb0.le, div_mul_cancel₀ _ ha0.ne',
        ← ENNReal.ofReal_add hε0.le (by linarith), add_sub_cancel, ENNReal.ofReal_one]
  -- its logarithm at `min τ k`
  set g : ℕ → (ℕ → 𝓧) → ℝ := fun k ω ↦ if τ ω ≤ k then L else Real.log ε
  have hgm (k : ℕ) : Measurable (g k) := Measurable.ite (hτle k) measurable_const measurable_const
  have hgC (k : ℕ) (ω : ℕ → 𝓧) : ‖g k ω‖ ≤ max |L| |Real.log ε| := by
    rw [Real.norm_eq_abs]
    by_cases h : τ ω ≤ k
    · simp only [g, h, ↓reduceIte, le_max_left]
    · simp only [g, h, ↓reduceIte, le_max_right]
  have hlog (k : ℕ) (ω : ℕ → 𝓧) : ENNReal.log (E (τk k ω) ω) = (g k ω : EReal) := by
    have hmem : ω ∈ {x | τ x ≤ (τk k ω : WithTop ℕ)} ↔ τ ω ≤ k := by
      rw [Set.mem_ofPred_eq, hτk_coe]
      exact ⟨fun h ↦ h.trans (min_le_right _ _), fun h ↦ le_min le_rfl h⟩
    by_cases hω : τ ω ≤ k
    · simp only [E, g, Set.indicator_of_mem (hmem.2 hω), hω, ↓reduceIte]
      rw [← ENNReal.ofReal_add hε0.le hb0.le, ENNReal.log_ofReal_of_pos (by linarith)]
    · simp only [E, g, Set.indicator_of_notMem (mt hmem.1 hω), hω, ↓reduceIte, add_zero]
      rw [ENNReal.log_ofReal_of_pos hε0]
  have hk (k : ℕ) : ∫ ω, g k ω ∂μ ≤ D := by
    have hg : Integrable (g k) μ :=
      Integrable.of_bound (hgm k).aestronglyMeasurable _ (ae_of_all _ (hgC k))
    have h := hE.eintegral_log_stoppedValue_le_mul_bipolarRate Q₁ hS₁ (hτk k)
    have hmk' : ∫⁻ ω, (τk k ω : ℝ≥0∞) + 1 ∂μ ≠ ∞ := ne_top_of_le_ne_top hm (hmk k)
    rw [eintegral_congr (hlog k), eintegral_eq_integral hg, ← EReal.coe_ennreal_toReal hmk',
      ← EReal.coe_toReal hd (ne_bot_of_le_ne_bot EReal.zero_ne_bot hd0), ← EReal.coe_mul,
      EReal.coe_le_coe_iff] at h
    calc ∫ ω, g k ω ∂μ ≤ _ := h
    _ ≤ m.toReal * (bipolarRate Q₁ S₁).toReal :=
      mul_le_mul_of_nonneg_right (ENNReal.toReal_mono hm (hmk k)) (EReal.toReal_nonneg hd0)
    _ = D := mul_comm _ _
  -- let `k` tend to infinity
  have hL : L ≤ D := by
    have h := le_of_tendsto' (tendsto_integral_of_dominated_convergence (f := fun _ ↦ L) _
      (fun k ↦ (hgm k).aestronglyMeasurable) (integrable_const _) (fun k ↦ ae_of_all _ (hgC k))
      (hae.mono fun ω hω ↦ ?_)) hk
    · simpa using h
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hω
    refine tendsto_atTop_of_eventually_const (i₀ := n) fun k hk ↦ ?_
    have : τ ω ≤ k := by
      rw [← hn]
      exact WithTop.coe_le_coe.2 hk
    simp only [g, this, ↓reduceIte]
  have h1 : Real.log (1 - ε) - Real.log a ≤ L := by
    rw [← Real.log_div (by linarith) ha0.ne']
    exact Real.log_le_log hb0 (by linarith)
  linarith

/-- **The lower bound on expected stopping times.** A sequential test of level `α` for the i.i.d.
laws of the members of `S₁`, that is, a stopping time `τ` with `P^ℕ (τ < ∞) ≤ α` for every
`P ∈ S₁`, makes at least `log (1/α) / d` observations in expectation under the i.i.d. law of
`Q₁`, where `d` is the bipolar rate of `Q₁` against `S₁`: `log (1/α) / d ≤ 𝔼[τ + 1]`. The left
side is in `ℝ≥0∞`, with `log (1/α)` replaced by `0` for `α ≥ 1`: if `d = 0` and `α < 1`, the
expected number of observations is infinite, if `d = ∞` the bound is `0`, and if `α = 0` and
`d < ∞` the expected number of observations is infinite. Since the bipolar rate is at most the
smallest relative entropy from `Q₁` to `S₁` (`bipolarRate_le_iInf_klDiv`), this contains the
lower bound `log (1/α) / KL_inf(Q₁, S₁)` [ARR26]. -/
theorem toENNReal_log_inv_div_bipolarRate_le_lintegral (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) τ) {α : ℝ≥0∞}
    (h_level : ∀ P ∈ S₁, Measure.infinitePi (fun _ : ℕ ↦ P) {ω | τ ω ≠ ⊤} ≤ α) :
    (ENNReal.log α⁻¹).toENNReal / (bipolarRate Q₁ S₁).toENNReal ≤
      ∫⁻ ω, ENat.toENNReal (τ ω) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by
  set m := ∫⁻ ω, ENat.toENNReal (τ ω) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  by_cases hm : m = ∞
  · rw [hm]
    exact le_top
  by_cases hd : bipolarRate Q₁ S₁ = ⊤
  · simp [hd]
  by_cases hα1 : 1 ≤ α
  · rw [EReal.toENNReal_of_nonpos (ENNReal.log_le_zero_iff.2 (ENNReal.inv_le_one.2 hα1)),
      ENNReal.zero_div]
    exact bot_le
  have hD0 : 0 ≤ (bipolarRate Q₁ S₁).toReal * m.toReal :=
    mul_nonneg (EReal.toReal_nonneg (bipolarRate_nonneg Q₁ S₁)) ENNReal.toReal_nonneg
  -- the bound up to `- log (1 - ε)`, for every `ε ∈ (0, 1)`, gives the bound
  have key {a : ℝ} (ha0 : 0 < a)
      (h_level' : ∀ P ∈ S₁, Measure.infinitePi (fun _ : ℕ ↦ P) {ω | τ ω ≠ ⊤} ≤
        ENNReal.ofReal a) :
      -Real.log a ≤ (bipolarRate Q₁ S₁).toReal * m.toReal := by
    refine le_of_forall_pos_le_add fun η hη ↦ ?_
    have hexp : Real.exp (-η) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    have h := neg_log_le_toReal_mul_sub Q₁ hS₁ hτ ha0 h_level' hd hm
      (ε := 1 - Real.exp (-η)) (by linarith) (by linarith [Real.exp_pos (-η)])
    rwa [sub_sub_cancel, Real.log_exp, sub_neg_eq_add] at h
  rcases eq_or_ne α 0 with rfl | hα0
  · -- a test of level `0` with a finite expected number of observations would have level
    -- `exp (- (d 𝔼[τ + 1] + 1))`
    have h := key (Real.exp_pos (-((bipolarRate Q₁ S₁).toReal * m.toReal + 1)))
      fun P hP ↦ (h_level P hP).trans bot_le
    rw [Real.log_exp, neg_neg] at h
    linarith
  have hαtop : α ≠ ⊤ := ne_top_of_lt (not_le.1 hα1)
  have h := key (ENNReal.toReal_pos hα0 hαtop)
    fun P hP ↦ (h_level P hP).trans_eq (ENNReal.ofReal_toReal hαtop).symm
  rw [ENNReal.log_inv, ENNReal.log_pos_real hα0 hαtop, ← EReal.coe_neg,
    EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  refine ENNReal.div_le_of_le_mul ?_
  rw [EReal.toENNReal_of_ne_top hd, ← ENNReal.ofReal_toReal hm,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal (by linarith [mul_comm m.toReal (bipolarRate Q₁ S₁).toReal])

end Test

end ProbabilityTheory
