/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Process.Stopping
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
`ProbabilityTheory.mul_lintegral_upcrossings_sum_div_le` and
`ProbabilityTheory.mul_measure_exists_le_abs_sum_div_sub_le`, which involve the law only through
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

/-- The sample mean of the first `n + 1` coordinates is measurable at time `n` for the canonical
filtration. -/
private lemma measurable_piLE_sum_div (n : ℕ) :
    Measurable[Filtration.piLE (X := fun _ : ℕ ↦ ℝ) n]
      fun ω : ℕ → ℝ ↦ (∑ i ∈ Finset.range (n + 1), ω i) / (n + 1) := by
  refine Measurable.div_const (Finset.measurable_sum _ fun i hi ↦ ?_) _
  exact Filtration.measurable_piLE_apply (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

/-- A sequence whose sample means stay at distance less than `L` from the first observation and
make fewer than `K q` upcrossings of every interval with rational endpoints `q` has convergent
sample means. -/
private lemma exists_tendsto_of_upcrossingsBefore_lt {ω : ℕ → ℝ} {L : ℝ} {K : ℚ × ℚ → ℕ}
    (hL : ∀ n : ℕ, |(∑ i ∈ Finset.range (n + 1), ω i) / (n + 1) - ω 0| < L)
    (hK : ∀ q : ℚ × ℚ, (q.1 : ℝ) < q.2 → ∀ n, upcrossingsBefore q.1 q.2
      (fun n ω ↦ (∑ i ∈ Finset.range (n + 1), ω i) / (n + 1)) n ω < K q) :
    ∃ l, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, ω i) / n) atTop (𝓝 l) := by
  set Y : ℕ → (ℕ → ℝ) → ℝ := fun n ω ↦ (∑ i ∈ Finset.range (n + 1), ω i) / (n + 1)
  have hlim : liminf (fun n ↦ (‖Y n ω‖₊ : ℝ≥0∞)) atTop < ⊤ := by
    refine (liminf_le_of_frequently_le' (x := ((‖ω 0‖₊ + L.toNNReal : ℝ≥0) : ℝ≥0∞))
      (Eventually.of_forall fun n ↦ ?_).frequently).trans_lt ENNReal.coe_lt_top
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    push_cast [Real.norm_eq_abs, Real.coe_toNNReal']
    have h1 := abs_sub_abs_le_abs_sub (Y n ω) (ω 0)
    have h2 := hL n
    have h3 := le_max_left L 0
    linarith
  obtain ⟨l, hl⟩ := tendsto_of_upcrossings_lt_top (f := Y) (ω := ω) hlim fun a b hab ↦
    upcrossings_lt_top_iff.2 ⟨K (a, b), fun N ↦ (hK (a, b) (by exact_mod_cast hab) N).le⟩
  refine ⟨l, (tendsto_add_atTop_iff_nat 1).1 ?_⟩
  simpa [Y] using hl

/-- If `y` is at distance at least `2 L` from `y₀`, then `y` or `y₀` is at distance at least `L`
from `m`, by the triangle inequality. -/
private lemma le_abs_sub_or_le_abs_sub_of_two_mul_le {y y₀ m L : ℝ} (h : 2 * L ≤ |y - y₀|) :
    L ≤ |y - m| ∨ L ≤ |y₀ - m| := by
  by_contra! h'
  have := abs_sub_le y m y₀
  rw [abs_sub_comm m] at this
  linarith [h'.1, h'.2]

/-- **Markov's inequality for a count.** If `(b - a) ∫⁻ U ≤ C` and `C ≤ (b - a) K ε`, with `a < b`
and `K ≠ 0`, then `U` is at least `K` with probability at most `ε`. -/
private lemma measure_natCast_le_le_of_mul_lintegral_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {U : Ω → ℝ≥0∞} (hU : AEMeasurable U μ) {a b : ℝ} (hab : a < b) {K : ℕ}
    (hK : K ≠ 0) {C ε : ℝ≥0} (hUC : ENNReal.ofReal (b - a) * ∫⁻ ω, U ω ∂μ ≤ C)
    (hC : (C : ℝ) ≤ (b - a) * K * ε) :
    μ {ω | (K : ℝ≥0∞) ≤ U ω} ≤ ε := by
  set x := ENNReal.ofReal (b - a) * K
  have hx0 : x ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne' (Nat.cast_ne_zero.2 hK)
  have hxtop : x ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)
  rw [← ENNReal.mul_le_mul_iff_right hx0 hxtop]
  calc x * μ {ω | (K : ℝ≥0∞) ≤ U ω}
      = ENNReal.ofReal (b - a) * (K * μ {ω | (K : ℝ≥0∞) ≤ U ω}) := mul_assoc _ _ _
    _ ≤ ENNReal.ofReal (b - a) * ∫⁻ ω, U ω ∂μ := by
        gcongr
        exact mul_meas_ge_le_lintegral₀ hU _
    _ ≤ C := hUC
    _ = ENNReal.ofReal C := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal ((b - a) * K * ε) := ENNReal.ofReal_le_ofReal hC
    _ = x * ε := by
        rw [ENNReal.ofReal_mul (mul_nonneg (sub_nonneg.2 hab.le) (Nat.cast_nonneg _)),
          ENNReal.ofReal_mul (sub_nonneg.2 hab.le), ENNReal.ofReal_natCast,
          ENNReal.ofReal_coe_nnreal]

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
  set Y : ℕ → (ℕ → ℝ) → ℝ := fun n ω ↦ (∑ i ∈ Finset.range (n + 1), ω i) / (n + 1) with hY
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
  -- the events at which the stopping time stops
  set E : ℕ → Set (ℕ → ℝ) := fun n ↦ {ω | (∃ q : ℚ × ℚ, (q.1 : ℝ) < q.2 ∧
      K q ≤ upcrossingsBefore q.1 q.2 Y n ω) ∨ 2 * (L : ℝ) ≤ |Y n ω - Y 0 ω|} with hE
  have hYadapted : StronglyAdapted (Filtration.piLE (X := fun _ : ℕ ↦ ℝ)) Y :=
    fun n ↦ (measurable_piLE_sum_div n).stronglyMeasurable
  have hEmeas (n : ℕ) : MeasurableSet[Filtration.piLE (X := fun _ : ℕ ↦ ℝ) n] (E n) := by
    simp only [hE, Set.ofPred_or]
    refine MeasurableSet.union ?_ ?_
    · have : {ω | ∃ q : ℚ × ℚ, (q.1 : ℝ) < q.2 ∧ K q ≤ upcrossingsBefore q.1 q.2 Y n ω} =
          ⋃ q : ℚ × ℚ, {ω | (q.1 : ℝ) < q.2 ∧ K q ≤ upcrossingsBefore q.1 q.2 Y n ω} := by
        ext
        simp
      rw [this]
      refine MeasurableSet.iUnion fun q ↦ ?_
      by_cases hq : (q.1 : ℝ) < q.2
      · simp only [hq, true_and]
        exact hYadapted.adapted_upcrossingsBefore hq n (measurableSet_Ici (a := K q))
      · simp [hq]
    · refine (continuous_abs.measurable.comp ?_) (measurableSet_Ici (a := 2 * (L : ℝ)))
      exact (measurable_piLE_sum_div n).sub
        ((measurable_piLE_sum_div 0).mono (Filtration.mono _ (Nat.zero_le n)) le_rfl)
  refine ⟨hittingAfter (fun n ↦ (E n).indicator fun _ ↦ (1 : ℝ)) {1} 0,
    Adapted.isStoppingTime_hittingAfter (fun n ↦ measurable_const.indicator (hEmeas n))
      (measurableSet_singleton 1), fun P hPS ↦ ?_, fun ω hω ↦ ?_⟩
  · by_cases hP₁ : IsProbabilityMeasure P
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
    have hc₀ : ENNReal.ofReal (∫ ω, |ω 0 - m| ∂μ) ≤ C := by
      have h : ∫ ω, |ω 0 - m| ∂μ = ∫ x, |x - m| ∂P :=
        integral_comp_eval_infinitePi (μ := fun _ : ℕ ↦ P) (i := 0) (f := fun x ↦ |x - m|)
          (by fun_prop)
      refine ENNReal.ofReal_le_of_le_toReal ?_
      rw [ENNReal.coe_toReal, h]
      exact (hc P hPS).trans hcC
    -- stopping means many upcrossings of some interval, or a sample mean far from `m`
    have hsub : {ω | hittingAfter (fun n ↦ (E n).indicator fun _ ↦ (1 : ℝ)) {1} 0 ω < ⊤} ⊆
        (⋃ q : ℚ × ℚ, {ω | (q.1 : ℝ) < q.2 ∧ (K q : ℝ≥0∞) ≤ upcrossings q.1 q.2 Y ω}) ∪
          {ω | ∃ n, (L : ℝ) ≤ |Y n ω - m|} := by
      intro ω hω
      rw [Set.mem_ofPred_eq, hittingAfter_indicator_lt_top_iff] at hω
      obtain ⟨n, -, hn⟩ := hω
      rcases hn with ⟨q, hq, hKq⟩ | hfar
      · refine Or.inl (Set.mem_iUnion.2 ⟨q, hq, ?_⟩)
        exact (Nat.cast_le.2 hKq).trans
          (le_iSup (fun N ↦ (upcrossingsBefore q.1 q.2 Y N ω : ℝ≥0∞)) n)
      · rcases le_abs_sub_or_le_abs_sub_of_two_mul_le (m := m) hfar with h | h
        exacts [Or.inr ⟨n, h⟩, Or.inr ⟨0, h⟩]
    -- many upcrossings of `[q.1, q.2]` have probability at most `ε q`
    have hq (q : ℚ × ℚ) :
        μ {ω | (q.1 : ℝ) < q.2 ∧ (K q : ℝ≥0∞) ≤ upcrossings q.1 q.2 Y ω} ≤ ε q := by
      by_cases hq : (q.1 : ℝ) < q.2
      swap
      · simp [hq]
      simp only [hq, true_and]
      refine measure_natCast_le_le_of_mul_lintegral_le (C := C)
        (hYadapted.measurable_upcrossings hq).aemeasurable hq (by simp [hK]) ?_ ?_
      · calc ENNReal.ofReal ((q.2 : ℝ) - q.1) * ∫⁻ ω, upcrossings q.1 q.2 Y ω ∂μ
            ≤ ENNReal.ofReal (∫ ω, |ω 0 - m| ∂μ) := by
              simpa only [hm] using mul_lintegral_upcrossings_sum_div_le hμ hint q.1 q.2
          _ ≤ C := hc₀
      · have hd : 0 < ((q.2 : ℝ) - q.1) * ε q := mul_pos (sub_pos.2 hq) (hε0 q)
        have hceil := Nat.le_ceil ((C : ℝ) / (((q.2 : ℝ) - q.1) * ε q))
        have hKq : (C : ℝ) / (((q.2 : ℝ) - q.1) * ε q) ≤ K q := by
          simp only [hK, Nat.cast_add, Nat.cast_one]
          linarith
        calc (C : ℝ) ≤ K q * (((q.2 : ℝ) - q.1) * ε q) := (div_le_iff₀ hd).1 hKq
          _ = ((q.2 : ℝ) - q.1) * K q * ε q := by ring
    -- a sample mean at distance at least `L` from `m` has probability at most `δ / 2`
    have hfar : μ {ω | ∃ n, (L : ℝ) ≤ |Y n ω - m|} ≤ ((δ / 2 : ℝ≥0) : ℝ≥0∞) := by
      have hL0 : (L : ℝ≥0∞) ≠ 0 := by
        rw [ENNReal.coe_ne_zero, hL]
        positivity
      rw [← ENNReal.mul_le_mul_iff_right hL0 ENNReal.coe_ne_top]
      refine (mul_measure_exists_le_abs_sum_div_sub_le hμ hint m L).trans (hc₀.trans_eq ?_)
      rw [← ENNReal.coe_mul, show L * (δ / 2) = C by rw [hL]; field_simp]
    calc μ {ω | hittingAfter (fun n ↦ (E n).indicator fun _ ↦ (1 : ℝ)) {1} 0 ω < ⊤}
        ≤ ∑' q : ℚ × ℚ, μ {ω | (q.1 : ℝ) < q.2 ∧ (K q : ℝ≥0∞) ≤ upcrossings q.1 q.2 Y ω} +
            μ {ω | ∃ n, (L : ℝ) ≤ |Y n ω - m|} :=
          (measure_mono hsub).trans ((measure_union_le _ _).trans
            (add_le_add_left (measure_iUnion_le _) _))
      _ ≤ ∑' q, (ε q : ℝ≥0∞) + ((δ / 2 : ℝ≥0) : ℝ≥0∞) := add_le_add (tsum_le_tsum hq) hfar
      _ ≤ ((δ / 2 : ℝ≥0) : ℝ≥0∞) + ((δ / 2 : ℝ≥0) : ℝ≥0∞) := by gcongr
      _ = δ := by rw [← ENNReal.coe_add, add_halves]
      _ ≤ α := hδα.le
  · -- a sequence on which the stopping time is infinite has convergent sample means
    rw [hittingAfter_indicator_lt_top_iff]
    by_contra h
    simp only [hE, Set.mem_ofPred_eq, zero_le, true_and, not_exists, not_or, not_and,
      not_le] at h
    refine hω (exists_tendsto_of_upcrossingsBefore_lt (L := 2 * L) (K := K) (fun n ↦ ?_)
      fun q hq n ↦ (h n).1 q hq)
    simpa [Y] using (h n).2

end ProbabilityTheory
