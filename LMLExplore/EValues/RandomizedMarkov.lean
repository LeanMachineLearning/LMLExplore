/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.PVariable
public import LMLExplore.Probability.Independence.Basic

/-!
# The randomized Markov inequality

Markov's inequality for e-variables rejects the null at level `α` when `α⁻¹ ≤ E`
(`ProbabilityTheory.IsEVar.measure_inv_le_le`). Randomizing the threshold makes the test
uniformly more powerful at no cost in validity: with `U` uniform on `[0, 1]` and independent of
`E`, rejecting when `U ≤ α * E` still has level `α`: the threshold `1` of the test `1 ≤ α * E`
is lowered to the random threshold `U`. The exact statement is the identity
`P {U ≤ α * Y} = ∫⁻ min (α * Y) 1 ∂P ≤ α * ∫⁻ Y ∂P` for any `ℝ≥0∞`-valued `Y` independent of `U`,
the uniformly randomized Markov inequality [RM26, Theorem 1.2; RW, Theorem 2.9].

The proof freezes `Y` (`ProbabilityTheory.IndepFun.measure_prodMk_mem_eq_lintegral`): the event
`{U ≤ Z}`, for `Z` independent of `U`, has probability `∫⁻ ω, P {U ≤ Z ω} ∂P`, and the
distribution function of `U` is `t ↦ min t 1`. The same argument with a p-variable `p` in place
of `U` gives the inequality `P {p ≤ Z} ≤ ∫⁻ min Z 1 ∂P`, since a p-variable has
`P {p ≤ t} ≤ min t 1`; for an exact p-variable it is an equality. In particular, for a
p-variable `p` and an e-variable `E` independent under every member of the null, `p / E` is a
p-variable, and so is `U / E` for `U` uniform on `[0, 1]` [RW, Corollary 2.10]: the e-to-p
calibration `E ↦ E⁻¹` (`ProbabilityTheory.IsEVar.isPVar_inv`) can be sharpened by an independent
p-variable.

As everywhere in `LMLExplore.EValues`, the null is an arbitrary set of measures, and values are
in `ℝ≥0∞`, with `p / 0 = ∞` for `p ≠ 0` and `p / ∞ = 0`.

## Main statements

* `ProbabilityTheory.IsPVar.measure_le_le_lintegral_min`,
  `ProbabilityTheory.IsExactPVar.measure_le_eq_lintegral_min`: for `Z` independent of a
  p-variable `p`, `P {p ≤ Z} ≤ ∫⁻ min Z 1 ∂P`, with equality when `p` is exact.
* `ProbabilityTheory.measure_ofReal_le_mul_eq_lintegral_min`: for `U` uniform on `[0, 1]` and
  independent of `Y`, `P {U ≤ α * Y} = ∫⁻ min (α * Y) 1 ∂P` [RW, Theorem 2.9].
* `ProbabilityTheory.IsPVar.measure_le_mul_le_mul_lintegral`: **the randomized Markov
  inequality**, `P {p ≤ α * Y} ≤ α * ∫⁻ Y ∂P` for `Y` independent of a p-variable `p`, in
  particular of a uniform variable [RM26, Theorem 1.2].
* `ProbabilityTheory.IsEVar.measure_le_mul_le`: the randomized e-test `{p ≤ α * E}` has level `α`.
* `ProbabilityTheory.IsEVar.isPVar_div`, `ProbabilityTheory.IsEVar.isPVar_ofReal_div`: `p / E`
  and `U / E` are p-variables [RW, Corollary 2.10].

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6: Theorem 2.9 and Corollary 2.10.
* [RM26] A. Ramdas and T. Manole, *Randomized and exchangeable improvements of Markov's,
  Chebyshev's and Chernoff's inequalities*, Statist. Sci. 41 (2026),
  arXiv:2304.02611v3: Theorem 1.2.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S : Set (Measure Ω)} {P : Measure Ω}
  {p E Y Z : Ω → ℝ≥0∞}

/-- The event `{p ≤ Z}` of independent `ℝ≥0∞`-valued variables, by freezing `Z`. -/
private theorem measure_le_eq_lintegral_of_indepFun [IsFiniteMeasure P] (hp : Measurable p)
    (hZ : Measurable Z) (hpZ : IndepFun p Z P) :
    P {ω | p ω ≤ Z ω} = ∫⁻ ω, P {ω' | p ω' ≤ Z ω} ∂P :=
  hpZ.measure_prodMk_mem_eq_lintegral hp.aemeasurable hZ.aemeasurable (s := {x | x.1 ≤ x.2})
    (measurableSet_le measurable_fst measurable_snd)

/-- A p-variable `p` is at most an independent threshold `Z` with probability at most
`∫⁻ min Z 1 ∂P`: the randomized test that rejects when `p ≤ Z` has the size of the
`[0, 1]`-valued test `min Z 1`. -/
theorem IsPVar.measure_le_le_lintegral_min (hp : IsPVar p S) (hP : P ∈ S)
    [IsProbabilityMeasure P] (hZ : Measurable Z) (hpZ : IndepFun p Z P) :
    P {ω | p ω ≤ Z ω} ≤ ∫⁻ ω, min (Z ω) 1 ∂P := by
  rw [measure_le_eq_lintegral_of_indepFun hp.measurable hZ hpZ]
  exact lintegral_mono fun ω ↦ le_min (hp.measure_le_le P hP _) prob_le_one

/-- An exact p-variable `p` is below an independent threshold `Z` with probability exactly
`∫⁻ min Z 1 ∂P`. -/
theorem IsExactPVar.measure_le_eq_lintegral_min (hp : IsExactPVar p S) (hP : P ∈ S)
    [IsProbabilityMeasure P] (hZ : Measurable Z) (hpZ : IndepFun p Z P) :
    P {ω | p ω ≤ Z ω} = ∫⁻ ω, min (Z ω) 1 ∂P := by
  simp_rw [measure_le_eq_lintegral_of_indepFun hp.measurable hZ hpZ, hp.measure_le_eq_min hP]

/-- **The randomized Markov identity** [RW, Theorem 2.9]: for `U` uniform on `[0, 1]` and
independent of a measurable `Y : Ω → ℝ≥0∞`, the randomized test that rejects when `U ≤ α * Y` has
rejection probability `∫⁻ min (α * Y) 1 ∂P`, the expectation of the `[0, 1]`-valued test
`min (α * Y) 1`. -/
theorem measure_ofReal_le_mul_eq_lintegral_min (hY : Measurable Y) {U : Ω → ℝ} (hU : Measurable U)
    (hU_law : P.map U = volume.restrict (Icc 0 1)) (hUY : IndepFun U Y P) (α : ℝ≥0∞) :
    P {ω | ENNReal.ofReal (U ω) ≤ α * Y ω} = ∫⁻ ω, min (α * Y ω) 1 ∂P := by
  have := isProbabilityMeasure_of_map_eq_volume_restrict_Icc hU.aemeasurable hU_law
  refine (isExactPVar_ofReal_of_map_eq (S := {P}) hU fun Q hQ ↦ ?_).measure_le_eq_lintegral_min
    (mem_singleton P) (hY.const_mul α)
    (hUY.comp ENNReal.measurable_ofReal (measurable_const_mul α))
  rwa [mem_singleton_iff.1 hQ]

/-- **The randomized Markov inequality** [RW, Theorem 2.9; RM26, Theorem 1.2]: for a p-variable
`p` and an independent measurable `Y : Ω → ℝ≥0∞`, `P {p ≤ α * Y} ≤ α * ∫⁻ Y ∂P`. For `p` uniform
on `[0, 1]` (`ProbabilityTheory.isExactPVar_ofReal_of_map_eq`), this is the uniformly randomized
Markov inequality `P {U ≤ α * Y} ≤ α * ∫⁻ Y ∂P`, whose event contains that of Markov's inequality
`P {1 ≤ α * Y} ≤ α * ∫⁻ Y ∂P` as soon as `U ≤ 1`. -/
theorem IsPVar.measure_le_mul_le_mul_lintegral (hp : IsPVar p S) (hP : P ∈ S)
    [IsProbabilityMeasure P] (hY : Measurable Y) (hpY : IndepFun p Y P) (α : ℝ≥0∞) :
    P {ω | p ω ≤ α * Y ω} ≤ α * ∫⁻ ω, Y ω ∂P :=
  calc P {ω | p ω ≤ α * Y ω}
  _ ≤ ∫⁻ ω, min (α * Y ω) 1 ∂P :=
    hp.measure_le_le_lintegral_min hP (hY.const_mul α)
      (hpY.comp measurable_id (measurable_const_mul α))
  _ ≤ ∫⁻ ω, α * Y ω ∂P := lintegral_mono fun _ ↦ min_le_left _ _
  _ = α * ∫⁻ ω, Y ω ∂P := lintegral_const_mul α hY

/-- **The randomized e-test** [RW, Theorem 2.9]: for an e-variable `E` and a p-variable `p`
independent of `E` under a probability measure `P` of the null, rejecting when `p ≤ α * E` has
level `α`. For `p` uniform on `[0, 1]`, this lowers the rejection threshold of the test
`1 ≤ α * E` of Markov's inequality (`ProbabilityTheory.IsEVar.measure_inv_le_le`) to `U`. -/
theorem IsEVar.measure_le_mul_le (hE : IsEVar E S) (hp : IsPVar p S) (hP : P ∈ S)
    [IsProbabilityMeasure P] (hpE : IndepFun p E P) (α : ℝ≥0∞) :
    P {ω | p ω ≤ α * E ω} ≤ α :=
  (hp.measure_le_le_lintegral_min hP (hE.measurable.const_mul α)
    (hpE.comp measurable_id (measurable_const_mul α))).trans (hE.lintegral_min_mul_le hP α)

/-- **Randomized e-to-p calibration** [RW, Corollary 2.10]: for a null of probability measures,
an e-variable `E` and a p-variable `p` that are independent under every member of the null,
`p / E` is a p-variable. -/
theorem IsEVar.isPVar_div (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hE : IsEVar E S)
    (hp : IsPVar p S) (hpE : ∀ P ∈ S, IndepFun p E P) :
    IsPVar (fun ω ↦ p ω / E ω) S where
  measurable := hp.measurable.div hE.measurable
  measure_le_le P hP α := by
    have := hS P hP
    rcases eq_or_ne α ∞ with rfl | hα
    · exact le_top
    -- off the `P`-null set where `E` is infinite, `p / E ≤ α` means `p ≤ α * E`
    have h_top : P {ω | E ω = ∞} = 0 := by
      simpa [lt_top_iff_ne_top] using ae_iff.1 (hE.ae_lt_top hP)
    calc P {ω | p ω / E ω ≤ α}
    _ ≤ P ({ω | p ω ≤ α * E ω} ∪ {ω | E ω = ∞}) := by
      refine measure_mono fun ω (hω : p ω / E ω ≤ α) ↦ ?_
      rcases eq_or_ne (E ω) ∞ with hω_top | hω_top
      · exact Or.inr hω_top
      exact Or.inl ((ENNReal.div_le_iff_le_mul (.inr hα) (.inl hω_top)).1 hω)
    _ ≤ P {ω | p ω ≤ α * E ω} + P {ω | E ω = ∞} := measure_union_le _ _
    _ ≤ α := by
      rw [h_top, add_zero]
      exact hE.measure_le_mul_le hp hP (hpE P hP) α

/-- **Randomized e-to-p calibration with a uniform variable** [RW, Corollary 2.10]: for an
e-variable `E` and a variable `U` uniform on `[0, 1]` and independent of `E` under every member of
the null, `U / E` is a p-variable. -/
theorem IsEVar.isPVar_ofReal_div (hE : IsEVar E S) {U : Ω → ℝ} (hU : Measurable U)
    (hU_law : ∀ P ∈ S, P.map U = volume.restrict (Icc 0 1)) (hUE : ∀ P ∈ S, IndepFun U E P) :
    IsPVar (fun ω ↦ ENNReal.ofReal (U ω) / E ω) S :=
  hE.isPVar_div (fun P hP ↦ isProbabilityMeasure_of_map_eq_volume_restrict_Icc hU.aemeasurable
      (hU_law P hP))
    (isExactPVar_ofReal_of_map_eq hU hU_law).toIsPVar
    fun P hP ↦ (hUE P hP).comp ENNReal.measurable_ofReal measurable_id

end ProbabilityTheory
