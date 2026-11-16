/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
public import LMLExplore.SequentialLearning.DivergenceDecomposition

/-!
# Change of measure at a fixed horizon for two stationary bandits

Run one algorithm for `M` rounds against two stationary environments with reward kernels `κ`
and `κ'`. If an event of the history of the first `M` rounds has probability at least `1 - δ`
under `κ` and at most `δ` under `κ'`, then the expected transportation cost
`∑ a, E_κ[N_a(M)] KL(κ a ‖ κ' a)` is at least `log (1 / (2.4 δ))`. This follows from the
divergence decomposition `Learning.IsAlgEnvSeq.klDiv_map_history_eq_sum_pullCount`, the data
processing inequality `LMLExplore.klBer_measureReal_le_klDiv` and the bound
`LMLExplore.mul_ofReal_log_le_of_mul_klBer_le` of `d(δ, 1 - δ)`. Its two-point form applies to an
estimate computed from the history that is `ε`-accurate with probability `1 - δ` under both
kernels, for two targets more than `2 ε` apart.

The version at the stopping time of an identification algorithm is
`LMLExplore.Identification.klBer_measureReal_histOutputMeasure_le`.

## Main statements

* `Learning.IsAlgEnvSeq.ofReal_log_le_sum_lintegral_pullCount_mul_klDiv`: the change of measure
  for an event of the history.
* `Learning.IsAlgEnvSeq.ofReal_log_le_sum_lintegral_pullCount_mul_klDiv_of_two_mul_lt`: the
  two-point form, for an estimate and two targets more than `2 ε` apart.

## References

* E. Kaufmann, O. Cappé and A. Garivier, *On the complexity of best-arm identification in
  multi-armed bandit models*, JMLR 17 (2016), Lemma 1.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory LMLExplore

open scoped ENNReal

namespace Learning

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  [Fintype 𝓐] [DecidableEq 𝓐] [MeasurableSingletonClass 𝓐] [MeasurableSpace.CountablyGenerated 𝓨]
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {O' : ℕ → Ω' → Unit} {A' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}
  {alg : Algorithm Unit 𝓐 𝓨} {κ κ' : Kernel 𝓐 𝓨} [IsMarkovKernel κ] [IsMarkovKernel κ'] {M : ℕ}
  {δ : ℝ}

/-- **Change of measure at a fixed horizon** [KCG16, Lemma 1]. Let a measurable set `E` of
histories of the first `M` rounds have probability at least `1 - δ` when the algorithm runs
against the stationary environment with reward kernel `κ`, and at most `δ` against `κ'`. Then
`log (1 / (2.4 δ)) ≤ ∑ a, E_κ[N_a(M)] KL(κ a ‖ κ' a)`, where `N_a(M)` is the number of rounds
before `M` at which `a` was played. -/
theorem IsAlgEnvSeq.ofReal_log_le_sum_lintegral_pullCount_mul_klDiv
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit κ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (Environment.bandit κ') P')
    {E : Set (Hist Unit 𝓐 𝓨 M)} (hE : MeasurableSet E)
    (hP : 1 - δ ≤ P.real (history O A Y M ⁻¹' E)) (hP' : P'.real (history O' A' Y' M ⁻¹' E) ≤ δ) :
    ENNReal.ofReal (Real.log (1 / (2.4 * δ))) ≤
      ∑ a, (∫⁻ ω, (pullCount A a M ω : ℝ≥0∞) ∂P) * klDiv (κ a) (κ' a) := by
  rw [← h.klDiv_map_history_eq_sum_pullCount h' M, ← one_mul (ENNReal.ofReal _)]
  refine mul_ofReal_log_le_of_mul_klBer_le le_rfl fun _ ↦ ?_
  -- The data processing inequality for the indicator of `E`.
  refine (one_mul _).trans_le (le_trans ?_ (klBer_measureReal_le_klDiv hE))
  rw [map_measureReal_apply (h.measurable_history M) hE,
    map_measureReal_apply (h'.measurable_history M) hE]
  calc klBer δ (1 - δ) = klBer (1 - δ) δ := by rw [← klBer_one_sub_one_sub, sub_sub_cancel]
    _ ≤ _ := klBer_le_klBer hP' (by linarith) hP

/-- **Two-point change of measure at a fixed horizon.** Let `est` be a measurable estimate
computed from the history of the first `M` rounds, and `Q`, `Q'` two targets more than `2 ε`
apart. If `est` is within `ε` of `Q` with probability at least `1 - δ` when the algorithm runs
against the stationary environment with reward kernel `κ`, and within `ε` of `Q'` with
probability at least `1 - δ` against `κ'`, then
`log (1 / (2.4 δ)) ≤ ∑ a, E_κ[N_a(M)] KL(κ a ‖ κ' a)`. -/
theorem IsAlgEnvSeq.ofReal_log_le_sum_lintegral_pullCount_mul_klDiv_of_two_mul_lt
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit κ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (Environment.bandit κ') P')
    {est : Hist Unit 𝓐 𝓨 M → ℝ} (hest : Measurable est) {Q Q' ε : ℝ} (hgap : 2 * ε < |Q' - Q|)
    (hP : 1 - δ ≤ P.real {ω | |est (history O A Y M ω) - Q| ≤ ε})
    (hP' : 1 - δ ≤ P'.real {ω | |est (history O' A' Y' M ω) - Q'| ≤ ε}) :
    ENNReal.ofReal (Real.log (1 / (2.4 * δ))) ≤
      ∑ a, (∫⁻ ω, (pullCount A a M ω : ℝ≥0∞) ∂P) * klDiv (κ a) (κ' a) := by
  have hmeas (c : ℝ) : MeasurableSet {hh : Hist Unit 𝓐 𝓨 M | |est hh - c| ≤ ε} :=
    measurableSet_le ((hest.sub_const c).abs) measurable_const
  refine h.ofReal_log_le_sum_lintegral_pullCount_mul_klDiv h' (hmeas Q) hP ?_
  -- The estimate cannot be within `ε` of both `Q` and `Q'`.
  have hsub : history O' A' Y' M ⁻¹' {hh | |est hh - Q| ≤ ε} ⊆
      {ω | |est (history O' A' Y' M ω) - Q'| ≤ ε}ᶜ := fun ω hE hE' ↦ by
    have h1 : |est (history O' A' Y' M ω) - Q| ≤ ε := hE
    have h2 : |est (history O' A' Y' M ω) - Q'| ≤ ε := hE'
    have := abs_sub_le Q' (est (history O' A' Y' M ω)) Q
    rw [abs_sub_comm] at h2
    linarith
  calc _ ≤ _ := measureReal_mono hsub
    _ = 1 - P'.real {ω | |est (history O' A' Y' M ω) - Q'| ≤ ε} :=
        probReal_compl_eq_one_sub (h'.measurable_history M (hmeas Q'))
    _ ≤ δ := by linarith

end Learning
