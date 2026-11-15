/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Process.Stopping
import LMLExplore.Algebra.Order.Floor.Semifield
import LMLExplore.MeasureTheory.Integral.Lebesgue.Markov
import LMLExplore.Probability.Martingale.SampleMean
import LMLExplore.Probability.Martingale.Upcrossing
import LMLExplore.Probability.Process.HittingTime
import LMLExplore.Probability.ProductMeasure
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Process.HittingTime
import Statlib.ForMathlib.Probability.Process.Filtration
import Statlib.ForMathlib.Probability.ProductMeasure
import TauCeti.Probability.Exchangeability.PathSpace.Law.Basic

/-!
# A composite strong law of large numbers

For a set `𝒫` of laws of a sequence of observations, the inverse capital outer measure of a set
`A` of sequences is the infimum of `sup_{P ∈ 𝒫} P (τ < ∞)` over the stopping times `τ` that are
finite on `A` [RLKR23]. It is zero exactly when, for every `α > 0`, some stopping time is finite
on `A` and finite with probability at most `α` under every member of `𝒫`, and exactly when some
e-process for `𝒫` tends to infinity on `A` [RLKR23, Theorem 3.1]. A composite strong law of large
numbers says that the set of the sequences whose sample means do not converge has inverse capital
outer measure zero for a null of i.i.d. laws.

This file proves it for the i.i.d. laws on `ℕ → ℝ` whose marginal ranges over a set of integrable
laws `P` with centred first absolute moments `∫ |x - m_P| dP ≤ c` for one constant `c`, where
`m_P` is the mean of `P`, in the stopping-time form, for the canonical filtration
`Filtration.piLE`, following [EVR26, Note 16, Theorem 1]. The centred uniform integrability under
which [RLKR23, §4.2] proves a composite strong law implies this hypothesis.

## Main statements

* `ProbabilityTheory.exists_isStoppingTime_lt_top_of_not_tendsto_mean`: the composite strong law.

## Implementation notes

Write `Aₖ` for the mean of the first `k` observations. The stopping time stops at the first time
`n` at which, for some interval `[a, b]` with rational endpoints, the sample means
`A₁, …, Aₙ₊₁` have completed `K (a, b)` upcrossings of `[a, b]`, or
at which `Aₙ₊₁` is at distance at least `2 L` from the first observation. A sequence on which it
never stops has bounded sample means that cross each such interval finitely often, so its sample
means converge (Mathlib's `MeasureTheory.tendsto_of_upcrossings_lt_top`). The probability of
stopping under each member of the null is bounded by the upcrossing and maximal inequalities
`ProbabilityTheory.mul_lintegral_upcrossings_sampleMean_le` and
`ProbabilityTheory.mul_measure_exists_le_abs_sampleMean_sub_le`, which involve the law only through
its centred first absolute moment. The thresholds `K (a, b)` come from summable positive weights
on the rational pairs (`ENNReal.exists_pos_sum_of_countable`).

The proof is adapted from `EValuesResearch/Results/CompositeSLLN.lean` (commit `7695891`) in the
paper project `RemyDegenne/evalues_research`, which proves [EVR26, Note 16, Theorem 1]; its
reverse-martingale helpers are replaced here by Tau Ceti's reverse filtration and time reversal.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026.
* [RLKR23] J. Ruf, M. Larsson, W. M. Koolen and A. Ramdas, *A composite generalization of Ville's
  martingale theorem using e-processes*, Electron. J. Probab. 28 (2023), arXiv:2203.04485v3.
-/

public section

open MeasureTheory Filter TauCeti.Probability
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

/-- A sequence whose sample means stay at distance less than `L` from the first observation and
make fewer than `K q` upcrossings of every interval with rational endpoints `q` has convergent
sample means. -/
private lemma exists_tendsto_of_upcrossingsBefore_lt {ω : ℕ → ℝ} {L : ℝ} {K : ℚ × ℚ → ℕ}
    (hL : ∀ n : ℕ, |sampleMean n ω - ω 0| < L)
    (hK : ∀ q : ℚ × ℚ, (q.1 : ℝ) < q.2 → ∀ n, upcrossingsBefore q.1 q.2 sampleMean n ω < K q) :
    ∃ l, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, ω i) / n) atTop (𝓝 l) := by
  have hlim : liminf (fun n ↦ (‖sampleMean n ω‖₊ : ℝ≥0∞)) atTop < ⊤ := by
    refine (liminf_le_of_frequently_le' (x := ((‖ω 0‖₊ + L.toNNReal : ℝ≥0) : ℝ≥0∞))
      (Eventually.of_forall fun n ↦ ?_).frequently).trans_lt ENNReal.coe_lt_top
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    push_cast [Real.norm_eq_abs, Real.coe_toNNReal']
    have h1 := abs_sub_abs_le_abs_sub (sampleMean n ω) (ω 0)
    have h2 := hL n
    have h3 := le_max_left L 0
    linarith
  obtain ⟨l, hl⟩ := tendsto_of_upcrossings_lt_top (f := sampleMean) (ω := ω) hlim fun a b hab ↦
    upcrossings_lt_top_iff.2 ⟨K (a, b), fun N ↦ (hK (a, b) (by exact_mod_cast hab) N).le⟩
  refine ⟨l, (tendsto_add_atTop_iff_nat 1).1 ?_⟩
  simpa [sampleMean_def] using hl

/-- The events at which the stopping time of the composite strong law stops: at time `n`, the
sample means of the coordinates `0, …, k`, `k ≤ n`, have completed `K q` upcrossings of some
interval `[q.1, q.2]` with rational endpoints, or the sample mean of the coordinates `0, …, n` is
at distance at least `2 L` from the first observation. -/
private def stopEvent (L : ℝ≥0) (K : ℚ × ℚ → ℕ) (n : ℕ) : Set (ℕ → ℝ) :=
  {ω | (∃ q : ℚ × ℚ, (q.1 : ℝ) < q.2 ∧ K q ≤ upcrossingsBefore q.1 q.2 sampleMean n ω) ∨
    2 * (L : ℝ) ≤ |sampleMean n ω - ω 0|}

/-- The stopping time of the composite strong law: the first time at which `stopEvent L K`
occurs. -/
private noncomputable def stopTime (L : ℝ≥0) (K : ℚ × ℚ → ℕ) : (ℕ → ℝ) → WithTop ℕ :=
  hittingAfter (fun n ↦ (stopEvent L K n).indicator fun _ ↦ (1 : ℝ)) {1} 0

/-- The stopping time stops exactly when some event `stopEvent L K n` occurs. -/
private lemma stopTime_lt_top_iff {L : ℝ≥0} {K : ℚ × ℚ → ℕ} {ω : ℕ → ℝ} :
    stopTime L K ω < ⊤ ↔ ∃ n, ω ∈ stopEvent L K n := by
  simp [stopTime, hittingAfter_indicator_lt_top_iff]

/-- The event `stopEvent L K n` is determined by the first `n + 1` observations. -/
private lemma measurableSet_stopEvent (L : ℝ≥0) (K : ℚ × ℚ → ℕ) (n : ℕ) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ ↦ ℝ) n] (stopEvent L K n) := by
  simp only [stopEvent, Set.ofPred_or]
  refine MeasurableSet.union ?_ ?_
  · have : {ω | ∃ q : ℚ × ℚ, (q.1 : ℝ) < q.2 ∧ K q ≤ upcrossingsBefore q.1 q.2 sampleMean n ω} =
        ⋃ q : ℚ × ℚ, {ω | (q.1 : ℝ) < q.2 ∧ K q ≤ upcrossingsBefore q.1 q.2 sampleMean n ω} := by
      ext
      simp
    rw [this]
    refine MeasurableSet.iUnion fun q ↦ ?_
    by_cases hq : (q.1 : ℝ) < q.2
    · simp only [hq, true_and]
      exact stronglyAdapted_piLE_sampleMean.adapted_upcrossingsBefore hq n
        (measurableSet_Ici (a := K q))
    · simp [hq]
  · refine (continuous_abs.measurable.comp ?_) (measurableSet_Ici (a := 2 * (L : ℝ)))
    exact (measurable_piLE_sampleMean n).sub (Filtration.measurable_piLE_apply (Nat.zero_le n))

/-- The time `stopTime L K` is a stopping time of the canonical filtration. -/
private lemma isStoppingTime_stopTime (L : ℝ≥0) (K : ℚ × ℚ → ℕ) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ ℝ)) (stopTime L K) :=
  Adapted.isStoppingTime_hittingAfter
    (fun n ↦ measurable_const.indicator (measurableSet_stopEvent L K n))
    (measurableSet_singleton 1)

/-- A sequence on which the stopping time never stops has convergent sample means. -/
private lemma stopTime_lt_top_of_not_tendsto {L : ℝ≥0} {K : ℚ × ℚ → ℕ} {ω : ℕ → ℝ}
    (hω : ¬ ∃ l : ℝ, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, ω i) / n) atTop (𝓝 l)) :
    stopTime L K ω < ⊤ := by
  rw [stopTime_lt_top_iff]
  by_contra h
  simp only [stopEvent, Set.mem_ofPred_eq, not_exists, not_or, not_and, not_le] at h
  exact hω (exists_tendsto_of_upcrossingsBefore_lt (L := 2 * L) (K := K) (fun n ↦ (h n).2)
    fun q hq n ↦ (h n).1 q hq)

/-- **The stopping probability under one law.** Let `μ` be an exchangeable probability measure on
`ℕ → ℝ` whose first coordinate is integrable, with centred first absolute moment at most `C`. If
`C ≤ (q.2 - q.1) K q ε q` for every rational interval `q` and `C ≤ L η`, then the stopping time
`stopTime L K` stops with probability at most `∑' q, ε q + η`. -/
private lemma measure_stopTime_lt_top_le {μ : Measure (ℕ → ℝ)} [IsProbabilityMeasure μ]
    (hμ : ExchangeableLaw μ) (hint : Integrable (fun ω ↦ ω 0) μ) {C : ℝ≥0}
    (hC : ENNReal.ofReal (∫ ω, |ω 0 - ∫ ω', ω' 0 ∂μ| ∂μ) ≤ C) {L η : ℝ≥0} (hL : L ≠ 0)
    (hLη : C ≤ L * η) {K : ℚ × ℚ → ℕ} (hK0 : ∀ q, K q ≠ 0) {ε : ℚ × ℚ → ℝ≥0}
    (hK : ∀ q : ℚ × ℚ, (q.1 : ℝ) < q.2 → (C : ℝ) ≤ ((q.2 : ℝ) - q.1) * K q * ε q) :
    μ {ω | stopTime L K ω < ⊤} ≤ ∑' q, (ε q : ℝ≥0∞) + η := by
  set m := ∫ ω, ω 0 ∂μ
  -- stopping means many upcrossings of some interval, or a sample mean far from `m`
  have hsub : {ω | stopTime L K ω < ⊤} ⊆
      (⋃ q : ℚ × ℚ, {ω | (q.1 : ℝ) < q.2 ∧ (K q : ℝ≥0∞) ≤ upcrossings q.1 q.2 sampleMean ω}) ∪
        {ω | ∃ n, (L : ℝ) ≤ |sampleMean n ω - m|} := by
    intro ω hω
    rw [Set.mem_ofPred_eq, stopTime_lt_top_iff] at hω
    obtain ⟨n, hn⟩ := hω
    rcases hn with ⟨q, hq, hKq⟩ | hfar
    · refine Or.inl (Set.mem_iUnion.2 ⟨q, hq, ?_⟩)
      exact (Nat.cast_le.2 hKq).trans
        (le_iSup (fun N ↦ (upcrossingsBefore q.1 q.2 sampleMean N ω : ℝ≥0∞)) n)
    · -- by the triangle inequality, `A_n` or `X₀` is at distance at least `L` from `m`
      refine Or.inr ?_
      rcases le_or_gt (L : ℝ) |sampleMean n ω - m| with h | h
      · exact ⟨n, h⟩
      · refine ⟨0, ?_⟩
        rw [sampleMean_zero]
        have := abs_sub_le (sampleMean n ω) m (ω 0)
        rw [abs_sub_comm m] at this
        linarith
  -- many upcrossings of `[q.1, q.2]` have probability at most `ε q`
  have hq (q : ℚ × ℚ) :
      μ {ω | (q.1 : ℝ) < q.2 ∧ (K q : ℝ≥0∞) ≤ upcrossings q.1 q.2 sampleMean ω} ≤ ε q := by
    by_cases hq : (q.1 : ℝ) < q.2
    swap
    · simp [hq]
    simp only [hq, true_and]
    refine measure_natCast_le_le_of_mul_lintegral_le
      (stronglyAdapted_piLE_sampleMean.measurable_upcrossings hq).aemeasurable hq (hK0 q)
      ((mul_lintegral_upcrossings_sampleMean_le hμ hint q.1 q.2).trans hC) (hK q hq)
  -- a sample mean at distance at least `L` from `m` has probability at most `η`
  have hfar : μ {ω | ∃ n, (L : ℝ) ≤ |sampleMean n ω - m|} ≤ η := by
    rw [← ENNReal.mul_le_mul_iff_right (ENNReal.coe_ne_zero.2 hL) ENNReal.coe_ne_top]
    exact (mul_measure_exists_le_abs_sampleMean_sub_le hμ hint m L).trans
      (hC.trans (by exact_mod_cast hLη))
  calc μ {ω | stopTime L K ω < ⊤}
      ≤ ∑' q : ℚ × ℚ, μ {ω | (q.1 : ℝ) < q.2 ∧ (K q : ℝ≥0∞) ≤ upcrossings q.1 q.2 sampleMean ω} +
          μ {ω | ∃ n, (L : ℝ) ≤ |sampleMean n ω - m|} :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add_left (measure_iUnion_le _) _))
    _ ≤ ∑' q, (ε q : ℝ≥0∞) + η := add_le_add (tsum_le_tsum hq) hfar

/-- **A composite strong law of large numbers.** Let `S` be a set of integrable laws on `ℝ` whose
centred first absolute moments `∫ |x - m_P| dP` are at most `c`, where `m_P` is the mean of `P`.
For every `α > 0`, some stopping time of the canonical filtration of `ℕ → ℝ` is finite on every
sequence whose sample means do not converge in `ℝ`, and finite with probability at most `α` under
i.i.d. sampling from each member of `S` [EVR26, Note 16, Theorem 1]. The set of these sequences
has thus inverse capital outer measure zero [RLKR23]. (For a member that is not a probability
measure, `Measure.infinitePi` is zero.) -/
theorem exists_isStoppingTime_lt_top_of_not_tendsto_mean {S : Set (Measure ℝ)}
    (hS : ∀ P ∈ S, Integrable id P) {c : ℝ} (hc : ∀ P ∈ S, ∫ x, |x - ∫ y, y ∂P| ∂P ≤ c)
    {α : ℝ≥0∞} (hα : 0 < α) :
    ∃ τ : (ℕ → ℝ) → WithTop ℕ, IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ ℝ)) τ ∧
      (∀ P ∈ S, Measure.infinitePi (fun _ : ℕ ↦ P) {ω | τ ω < ⊤} ≤ α) ∧
      ∀ ω : ℕ → ℝ, (¬ ∃ l : ℝ,
        Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, ω i) / n) atTop (𝓝 l)) → τ ω < ⊤ := by
  -- the constants: a level `δ ≤ α`, weights `ε` on the rational pairs, a bound `C` for the
  -- centred moments, a distance `L` and the upcrossing thresholds `K`
  obtain ⟨δ, hδ0, hδα⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hα
  have hδ0' : (0 : ℝ≥0) < δ := by exact_mod_cast hδ0
  obtain ⟨ε, hε0, hεsum⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.coe_ne_zero.2 (half_pos hδ0').ne') (ℚ × ℚ)
  set C : ℝ≥0 := c.toNNReal + 1 with hC
  have hcC : c ≤ C := by
    rw [hC, NNReal.coe_add, NNReal.coe_one]
    linarith [Real.le_coe_toNNReal c]
  have hC0 : 0 < C := add_pos_of_nonneg_of_pos zero_le one_pos
  set L : ℝ≥0 := 2 * C / δ with hL
  set K : ℚ × ℚ → ℕ := fun q ↦ ⌈(C : ℝ) / (((q.2 : ℝ) - q.1) * ε q)⌉₊ + 1 with hK
  have hKC (q : ℚ × ℚ) (hq : (q.1 : ℝ) < q.2) : (C : ℝ) ≤ ((q.2 : ℝ) - q.1) * K q * ε q := by
    have hd : 0 < ((q.2 : ℝ) - q.1) * ε q := mul_pos (sub_pos.2 hq) (hε0 q)
    calc (C : ℝ) ≤ ((q.2 : ℝ) - q.1) * ε q * ⌈(C : ℝ) / (((q.2 : ℝ) - q.1) * ε q)⌉₊ :=
          Nat.le_mul_ceil_div hd
      _ ≤ ((q.2 : ℝ) - q.1) * ε q * K q := by gcongr; simp [hK]
      _ = ((q.2 : ℝ) - q.1) * K q * ε q := by ring
  refine ⟨stopTime L K, isStoppingTime_stopTime L K, fun P hPS ↦ ?_,
    fun ω hω ↦ stopTime_lt_top_of_not_tendsto hω⟩
  by_cases hP₁ : IsProbabilityMeasure P
  swap
  · -- the product of copies of `P` is zero
    simp [Measure.infinitePi_eq_zero_of_not_isProbabilityMeasure (μ := fun _ : ℕ ↦ P)
      fun h ↦ hP₁ (h 0)]
  set μ := Measure.infinitePi fun _ : ℕ ↦ P
  set m := ∫ y, y ∂P
  -- the i.i.d. law is exchangeable, and its first coordinate is integrable of law `P`
  have hμ : ExchangeableLaw μ := exchangeableLaw_infinitePi_const ⟨P, hP₁⟩
  have hint : Integrable (fun ω ↦ ω 0) μ :=
    ((measurePreserving_eval_infinitePi (fun _ : ℕ ↦ P) 0).integrable_comp
      (hS P hPS).aestronglyMeasurable).2 (hS P hPS)
  have hm : ∫ ω, ω 0 ∂μ = m := integral_comp_eval_infinitePi (μ := fun _ : ℕ ↦ P) (i := 0)
    (f := fun x ↦ x) aestronglyMeasurable_id
  have hc₀ : ENNReal.ofReal (∫ ω, |ω 0 - ∫ ω', ω' 0 ∂μ| ∂μ) ≤ C := by
    have h : ∫ ω, |ω 0 - m| ∂μ = ∫ x, |x - m| ∂P :=
      integral_comp_eval_infinitePi (μ := fun _ : ℕ ↦ P) (i := 0) (f := fun x ↦ |x - m|)
        (by fun_prop)
    refine ENNReal.ofReal_le_of_le_toReal ?_
    rw [ENNReal.coe_toReal, hm, h]
    exact (hc P hPS).trans hcC
  have hL0 : L ≠ 0 := by
    rw [hL]
    positivity
  calc μ {ω | stopTime L K ω < ⊤} ≤ ∑' q, (ε q : ℝ≥0∞) + ((δ / 2 : ℝ≥0) : ℝ≥0∞) :=
        measure_stopTime_lt_top_le hμ hint hc₀ hL0
          (show L * (δ / 2) = C by rw [hL]; field_simp).ge (fun q ↦ by simp [hK]) hKC
    _ ≤ ((δ / 2 : ℝ≥0) : ℝ≥0∞) + ((δ / 2 : ℝ≥0) : ℝ≥0∞) := by gcongr
    _ = δ := by rw [← ENNReal.coe_add, add_halves]
    _ ≤ α := hδα.le

end ProbabilityTheory
