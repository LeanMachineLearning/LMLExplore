/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.ChangeOfMeasure
public import LMLExplore.Identification.SampleComplexity
public import LMLExplore.Identification.Task.TransportationCost

/-!
# Lower bound on the sample complexity of `δ`-correct algorithms

Let `A` be a `δ`-correct algorithm for an identification task, with `δ ≤ 1 / 2`, and let `θ` be an
admissible model with a single correct answer `i`. On `θ`, the algorithm stops and answers `i`
with probability at least `1 - δ`; on every alternative `λ ∈ ¬i`, with probability at most `δ`.
The transportation lemma turns this difference of behaviour into the inequality
`kl(δ, 1 - δ) ≤ ∑ a, E_θ[N_a(τ)] KL(ν_a(θ), ν_a(λ))`, where `N_a(τ)` is the number of pulls of the
arm `a` before the stopping time `τ`. Writing `E_θ[N_a(τ)] = E_θ[τ] w_a` with the expected
proportions of pulls `w`, an allocation, and taking the infimum over the alternatives gives
`kl(δ, 1 - δ) ≤ E_θ[τ] D(θ, w, ¬i) ≤ E_θ[τ] D(θ)`, that is, the lower bound
`E_θ[τ] ≥ T*(θ) kl(δ, 1 - δ)` of Garivier and Kaufmann (2016) on the sample complexity.

The binary relative entropy `kl(δ, 1 - δ)` is `LMLExplore.klBer δ (1 - δ)`; it is equivalent to
`log (1 / δ)` as `δ → 0`, so that `T*(θ) log (1 / δ)` lower-bounds `E_θ[τ]` asymptotically. That
`T*(θ)` is the optimal constant in front of `log (1 / δ)`, attained by the Track-and-Stop algorithm,
is a result of [GK16] that is not proved here.

## Main statements

* `LMLExplore.Identification.expectedPullProportion_mem_simplex`: if `0 < E[τ] < ∞`, the expected
  proportions of pulls `E[N_a(τ)] / E[τ]` form an allocation.
* `IdentTask.IsDeltaCorrect.klBer_le_sum_lintegral_pullCount_mul_klDiv`: the change of measure
  `kl(δ, 1 - δ) ≤ ∑ a, E_θ[N_a(τ)] KL(ν_a(θ), ν_a(λ))` for every alternative `λ` to the answer of
  `θ`.
* `IdentTask.IsDeltaCorrect.klBer_le_expectedStoppingTime_mul_altCost`: the allocation form
  `kl(δ, 1 - δ) ≤ E_θ[τ] D(θ, w, ¬i)`, with `w` the expected proportions of pulls.
* `IdentTask.IsDeltaCorrect.charTime_mul_le_expectedStoppingTime`: the lower bound
  `T*(θ) kl(δ, 1 - δ) ≤ E_θ[τ]`.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Theorem 1.
* [KCG16] E. Kaufmann, O. Cappé and A. Garivier, *On the complexity of best-arm identification in
  multi-armed bandit models*, JMLR 17 (2016), Lemma 1.
* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Theorem 33.5.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Learning

open scoped ENNReal

namespace LMLExplore.Identification

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {m𝓨 : MeasurableSpace 𝓨}

/-- If `0 < E[τ] < ∞`, the expected proportions of pulls `E[N_a(τ)] / E[τ]` form an allocation. -/
lemma expectedPullProportion_mem_simplex {𝓞 𝓓 : Type*} {m𝓞 : MeasurableSpace 𝓞}
    {m𝓓 : MeasurableSpace 𝓓} {A : IdentAlg 𝓞 α 𝓨 𝓓} {env : Environment 𝓞 α 𝓨}
    (h0 : expectedStoppingTime A env ≠ 0) (h : expectedStoppingTime A env ≠ ∞) :
    expectedPullProportion A env ∈ simplex α :=
  mem_simplex_iff.2 ⟨expectedPullProportion_nonneg A env, sum_expectedPullProportion h0 h⟩

namespace IdentTask

variable [MeasurableSpace.CountablyGenerated 𝓨] {mℐ : MeasurableSpace ℐ}
  [MeasurableSingletonClass ℐ] {task : IdentTask α Θ ℐ 𝓨} {A : IdentAlg Unit α 𝓨 ℐ} {δ : ℝ}
  {θ θ' : Θ} {i : ℐ}

/-- **Change of measure for `δ`-correct algorithms** [KCG16, Lemma 1]. Let `A` be `δ`-correct with
`δ ≤ 1 / 2`, let `i` be the only correct answer of the admissible model `θ`, and suppose that `A`
stops almost surely on `θ`. Then for every alternative `θ'` to `i`,
`kl(δ, 1 - δ) ≤ ∑ a, E_θ[N_a(τ)] KL(ν_a(θ), ν_a(θ'))`, where `N_a(τ)` is the number of pulls of the
arm `a` before the stopping time `τ`. -/
theorem IsDeltaCorrect.klBer_le_sum_lintegral_pullCount_mul_klDiv (hA : task.IsDeltaCorrect A δ)
    (hδ : δ ≤ 1 / 2) (hθ : θ ∈ task.M) (hi : task.correct θ = {i}) (hθ' : θ' ∈ task.alt i)
    (hstop : StopsAS A (stationaryEnv (task.ν θ))) :
    klBer δ (1 - δ) ≤
      ∑ a, (∫⁻ ω, (pullCount IT.action a (A.stoppingTime IT.obs IT.action IT.feedback ω).toNat
        ω : ℝ≥0∞) ∂(trajMeasure A.alg (stationaryEnv (task.ν θ)))) *
          klDiv (task.ν θ a) (task.ν θ' a) := by
  refine le_trans ?_
    (klBer_measureReal_histOutputMeasure_le A _ _ hstop (A.measurableSet_mem_stopSet_and_eq i))
  -- The event "stop and answer `i`" has probability at least `1 - δ` under `θ` and at most `δ`
  -- under `θ'`.
  have h_le := hA.measureReal_histOutputMeasure_le hθ'
  calc klBer δ (1 - δ) = klBer (1 - δ) δ := by rw [← klBer_one_sub_one_sub, sub_sub_cancel]
    _ ≤ _ := klBer_le_klBer h_le (by linarith)
        (hA.one_sub_le_measureReal_histOutputMeasure hθ hi)

/-- **Lower bound in allocation form** [GK16, proof of Theorem 1]. Let `A` be `δ`-correct with
`δ ≤ 1 / 2` and let `i` be the only correct answer of the admissible model `θ`. If
`0 < E_θ[τ] < ∞`, then the expected proportions of pulls `w = E_θ[N(τ)] / E_θ[τ]` satisfy
`kl(δ, 1 - δ) ≤ E_θ[τ] D(θ, w, ¬i)`. -/
theorem IsDeltaCorrect.klBer_le_expectedStoppingTime_mul_altCost (hA : task.IsDeltaCorrect A δ)
    (hδ : δ ≤ 1 / 2) (hθ : θ ∈ task.M) (hi : task.correct θ = {i})
    (h0 : expectedStoppingTime A (stationaryEnv (task.ν θ)) ≠ 0)
    (h : expectedStoppingTime A (stationaryEnv (task.ν θ)) ≠ ∞) :
    klBer δ (1 - δ) ≤ expectedStoppingTime A (stationaryEnv (task.ν θ)) *
      task.altCost θ (expectedPullProportion A (stationaryEnv (task.ν θ))) i := by
  simp_rw [altCost_def, ENNReal.mul_iInf_of_ne h0 h]
  refine le_iInf₂ fun θ' hθ' ↦ (hA.klBer_le_sum_lintegral_pullCount_mul_klDiv hδ hθ hi hθ'
    (.of_expectedStoppingTime_ne_top h)).trans_eq ?_
  simp_rw [cost_def, Finset.mul_sum, ← mul_assoc,
    expectedStoppingTime_mul_ofReal_expectedPullProportion h]

omit [DecidableEq α] in
/-- **Lower bound on the sample complexity** [GK16, Theorem 1; LS, Theorem 33.5]. Let `A` be
`δ`-correct with `δ ≤ 1 / 2` and let `θ` be an admissible model with a single correct answer.
Then `T*(θ) kl(δ, 1 - δ) ≤ E_θ[τ]`. -/
theorem IsDeltaCorrect.charTime_mul_le_expectedStoppingTime [Nonempty α]
    (hA : task.IsDeltaCorrect A δ) (hδ : δ ≤ 1 / 2) (hθ : θ ∈ task.M)
    (hi : task.correct θ = {i}) :
    task.charTime θ * klBer δ (1 - δ) ≤ expectedStoppingTime A (stationaryEnv (task.ν θ)) := by
  classical
  rcases eq_or_ne (expectedStoppingTime A (stationaryEnv (task.ν θ))) ∞ with h | h
  · exact h ▸ le_top
  -- If `i` has no alternative, then `D(θ) = ∞` and `T*(θ) = 0`.
  rcases (task.alt i).eq_empty_or_nonempty with h_alt | ⟨θ', hθ'⟩
  · simp [charTime_eq_inv_answerValue _ hi, answerValue_eq_top_of_alt_eq_empty _ h_alt]
  rcases eq_or_ne (expectedStoppingTime A (stationaryEnv (task.ν θ))) 0 with h0 | h0
  · -- If `E_θ[τ] = 0`, then all the expected numbers of pulls vanish, hence so does `kl(δ, 1 - δ)`.
    have h_kl := hA.klBer_le_sum_lintegral_pullCount_mul_klDiv hδ hθ hi hθ'
      (.of_expectedStoppingTime_ne_top h)
    simp_rw [← expectedStoppingTime_mul_ofReal_expectedPullProportion h, h0, zero_mul,
      Finset.sum_const_zero, nonpos_iff_eq_zero] at h_kl
    simp [h_kl]
  rw [charTime_def, mul_comm, ← div_eq_mul_inv]
  refine ENNReal.div_le_of_le_mul ((hA.klBer_le_expectedStoppingTime_mul_altCost hδ hθ hi h0
    h).trans ?_)
  gcongr
  exact (task.altCost_le_answerValue (expectedPullProportion_mem_simplex h0 h)).trans
    (task.answerValue_le_gameValue (hi ▸ Set.mem_singleton i))

end IdentTask

end LMLExplore.Identification
