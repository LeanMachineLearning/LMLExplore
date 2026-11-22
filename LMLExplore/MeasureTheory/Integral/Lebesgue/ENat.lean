/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import TauCeti.MeasureTheory.Integral.Lebesgue.Encard

/-!
# Lebesgue integral of an `ℕ∞`-valued function

The expectation of a random variable `f` with values in `ℕ∞`, such as a random time, is the sum of
its tail probabilities: `∫⁻ f ∂μ = ∑ n, μ {n < f}` (the discrete layer cake formula). Tau Ceti
proves it for measurable `f` (`MeasureTheory.lintegral_enat_eq_tsum`); here it is extended to
a.e.-measurable `f`. As a consequence, a random time that is at most `T` on an event `E T` for
every `T ≥ T₀` has expectation at most `T₀ + ∑_{T ≥ T₀} μ (E T)ᶜ` under a probability measure.
This is the form in which upper bounds on the expected stopping time of sequential algorithms are
proved: the events `E T` are good events of the first `T` rounds on which the algorithm must have
stopped.

## Main statements

* `MeasureTheory.lintegral_toENNReal_eq_tsum_measure_lt`: `∫⁻ f ∂μ = ∑' n, μ {n < f}` for
  a.e.-measurable `f`.
* `MeasureTheory.lintegral_toENNReal_le_add_tsum_measure_compl`: if `f ≤ T` on `E T` for every
  `T ≥ T₀`, then `∫⁻ f ∂μ ≤ T₀ + ∑' T, μ (E (T + T₀))ᶜ`.
* `MeasureTheory.lintegral_toENNReal_eq_top_of_measure_ne_zero`: a function with values in `ℕ∞`
  that is infinite on a set of positive measure has infinite integral.
* `MeasureTheory.lintegral_toENNReal_add_one`: the expectation of `τ + 1` is that of `τ` plus `1`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → ℕ∞}

/-- **Tail-sum formula** (discrete layer cake formula): the integral of an a.e.-measurable
function with values in `ℕ∞` is the sum of the measures of the sets where it exceeds each natural
number. This extends Tau Ceti's `lintegral_enat_eq_tsum`, which asks for measurable superlevel
sets. -/
lemma lintegral_toENNReal_eq_tsum_measure_lt (hf : AEMeasurable f μ) :
    ∫⁻ ω, (f ω : ℝ≥0∞) ∂μ = ∑' n : ℕ, μ {ω | (n : ℕ∞) < f ω} := by
  rw [lintegral_congr_ae (hf.ae_eq_mk.mono fun ω hω ↦ by rw [hω]),
    lintegral_enat_eq_tsum μ fun n ↦ hf.measurable_mk (.of_discrete (s := Set.Ioi (n : ℕ∞)))]
  exact tsum_congr fun n ↦ measure_congr (hf.ae_eq_mk.preimage (Set.Ioi (n : ℕ∞))).symm

/-- If a function with values in `ℕ∞` is at most `T` on a set `E T` for every `T ≥ T₀`, then its
integral under a probability measure is at most `T₀ + ∑_{T ≥ T₀} μ (E T)ᶜ`. For a random time,
`E T` is an event on which it is at most `T`. -/
lemma lintegral_toENNReal_le_add_tsum_measure_compl [IsZeroOrProbabilityMeasure μ]
    (hf : AEMeasurable f μ) {E : ℕ → Set Ω} {T₀ : ℕ} (hE : ∀ T ≥ T₀, ∀ ω ∈ E T, f ω ≤ T) :
    ∫⁻ ω, (f ω : ℝ≥0∞) ∂μ ≤ T₀ + ∑' T, μ (E (T + T₀))ᶜ := by
  rw [lintegral_toENNReal_eq_tsum_measure_lt hf,
    ← Summable.sum_add_tsum_nat_add' (k := T₀) CompleteLattice.summable]
  gcongr with T
  · -- The first `T₀` tail probabilities are at most `1`.
    calc ∑ n ∈ Finset.range T₀, μ {ω | (n : ℕ∞) < f ω}
    _ ≤ ∑ n ∈ Finset.range T₀, 1 := Finset.sum_le_sum fun _ _ ↦ prob_le_one
    _ = T₀ := by simp
  · -- From `T₀` on, `f` exceeds `T` only outside `E T`.
    exact fun ω hω hωE ↦ (hE (T + T₀) (Nat.le_add_left _ _) ω hωE).not_gt hω

/-- An a.e.-measurable function with values in `ℕ∞` that is infinite on a set of positive measure,
such as a random time that is infinite with positive probability, has infinite integral. -/
lemma lintegral_toENNReal_eq_top_of_measure_ne_zero (hf : AEMeasurable f μ)
    (h : μ {ω | f ω = ⊤} ≠ 0) : ∫⁻ ω, (f ω : ℝ≥0∞) ∂μ = ∞ :=
  lintegral_eq_top_of_measure_eq_top_ne_zero ((measurable_of_countable _).comp_aemeasurable hf)
    (by simpa using h)

/-- The expectation of the successor `τ + 1` of a random time with values in `WithTop ℕ` is the
expectation of `τ` plus `1`. On such terms, which are not `ℕ∞`-typed up to reducible
transparency, `simp` does not apply `ENat.toENNReal_add`. -/
lemma lintegral_toENNReal_add_one (τ : Ω → WithTop ℕ) :
    ∫⁻ ω, ENat.toENNReal (τ ω + 1 : WithTop ℕ) ∂μ = ∫⁻ ω, ENat.toENNReal (τ ω) + 1 ∂μ :=
  lintegral_congr fun ω ↦ (ENat.toENNReal_add (τ ω) 1).trans (by rw [ENat.toENNReal_one])

end MeasureTheory
