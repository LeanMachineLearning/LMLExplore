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
`log (1 / δ)` as `δ → 0`, and at least `log (1 / (2.4 δ))` for every `δ`, so that
`E_θ[τ] ≥ T*(θ) log (1 / (2.4 δ))`. For a family of `δ`-correct algorithms, this gives
`liminf_{δ → 0} E_θ[τ_δ] / log (1 / δ) ≥ T*(θ)`. That `T*(θ)` is the optimal constant in front
of `log (1 / δ)`, attained by the Track-and-Stop algorithm [GK16, Theorem 14], is proved for
Gaussian arms when Track-and-Stop tracks continuous optimal allocations with D-tracking, and when
it tracks any selection of the optimal allocations, even where these are not unique, with
C-tracking [DK19, Theorem 7]
(`IdentTask.tendsto_expectedStoppingTime_trackAndStop_unionBoundThreshold_div_log` and
`IdentTask.tendsto_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_div_log` in
`Identification/GaussianThreshold.lean`).

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
* `IdentTask.IsDeltaCorrect.charTime_mul_ofReal_log_le_expectedStoppingTime`: the lower bound
  `T*(θ) log (1 / (c δ)) ≤ E_θ[τ]` for `c ≥ 2.4`; for `c = 4` it is the form of
  [LS, Theorem 33.5].
* `IdentTask.eventually_mul_ofReal_log_le_expectedStoppingTime`: the asymptotic lower bound
  `c log (1 / δ) ≤ E_θ[τ_δ]` for all small enough `δ`, for every `c < T*(θ)`, for a family of
  `δ`-correct algorithms.
* `IdentTask.tendsto_expectedStoppingTime_div_log`: a family of `δ`-correct algorithms with
  `E_θ[τ_δ] ≤ c log (1 / δ)` for small `δ`, for every `c > T*(θ)`, has
  `E_θ[τ_δ] / log (1 / δ) → T*(θ)`.

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, Theorem 7.
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Theorems 1 and 14.
* [KCG16] E. Kaufmann, O. Cappé and A. Garivier, *On the complexity of best-arm identification in
  multi-armed bandit models*, JMLR 17 (2016), Lemma 1.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Theorem 33.5.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Learning

open scoped ENNReal NNReal

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
    (hstop : StopsAS A (Environment.bandit (task.ν θ))) :
    klBer δ (1 - δ) ≤
      ∑ a, (∫⁻ ω, (pullCount IT.action a
        (ENat.toNat (A.stoppingTime IT.obs IT.action IT.feedback ω))
        ω : ℝ≥0∞) ∂(trajMeasure A.alg (Environment.bandit (task.ν θ)))) *
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
    (h0 : expectedStoppingTime A (Environment.bandit (task.ν θ)) ≠ 0)
    (h : expectedStoppingTime A (Environment.bandit (task.ν θ)) ≠ ∞) :
    klBer δ (1 - δ) ≤ expectedStoppingTime A (Environment.bandit (task.ν θ)) *
      task.altCost θ (expectedPullProportion A (Environment.bandit (task.ν θ))) i := by
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
    task.charTime θ * klBer δ (1 - δ) ≤ expectedStoppingTime A (Environment.bandit (task.ν θ)) := by
  classical
  rcases eq_or_ne (expectedStoppingTime A (Environment.bandit (task.ν θ))) ∞ with h | h
  · exact h ▸ le_top
  -- If `i` has no alternative, then `D(θ) = ∞` and `T*(θ) = 0`.
  rcases (task.alt i).eq_empty_or_nonempty with h_alt | ⟨θ', hθ'⟩
  · simp [charTime_eq_inv_answerValue _ hi, answerValue_eq_top_of_alt_eq_empty _ h_alt]
  rcases eq_or_ne (expectedStoppingTime A (Environment.bandit (task.ν θ))) 0 with h0 | h0
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

omit [DecidableEq α] in
/-- **Lower bound on the sample complexity in logarithmic form** [KCG16; LS, Theorem 33.5]. Let `A`
be `δ`-correct and let `θ` be an admissible model with a single correct answer. Then for every
`c ≥ 2.4`, `T*(θ) log (1 / (c δ)) ≤ E_θ[τ]`. The constant `c = 2.4` is that of Kaufmann, Cappé and
Garivier, and `c = 4` gives the Bretagnolle–Huber form `E_θ[τ] ≥ T*(θ) log (1 / (4 δ))`. No upper
bound on `δ` is needed: for `δ > 1 / 2` the logarithm is negative. -/
theorem IsDeltaCorrect.charTime_mul_ofReal_log_le_expectedStoppingTime [Nonempty α]
    (hA : task.IsDeltaCorrect A δ) {c : ℝ} (hc : 2.4 ≤ c) (hθ : θ ∈ task.M)
    (hi : task.correct θ = {i}) :
    task.charTime θ * ENNReal.ofReal (Real.log (1 / (c * δ))) ≤
      expectedStoppingTime A (Environment.bandit (task.ν θ)) := by
  rcases le_or_gt δ (1 / 2) with hδ | hδ
  · exact (mul_le_mul_right (ofReal_log_one_div_le_klBer hc δ) _).trans
      (hA.charTime_mul_le_expectedStoppingTime hδ hθ hi)
  have h_neg : Real.log (1 / (c * δ)) ≤ 0 :=
    Real.log_nonpos (by positivity) ((div_le_one (by positivity)).2 (by nlinarith))
  rw [ENNReal.ofReal_of_nonpos h_neg, mul_zero]
  exact zero_le

open Filter Topology in
omit [DecidableEq α] in
/-- **Asymptotic lower bound on the sample complexity** [GK16, Theorem 1], in eventual form. Let
`A δ` be `δ`-correct for all small enough `δ` and let `θ` be an admissible model with a single
correct answer. Then for every `c < T*(θ)`, `c log (1 / δ) ≤ E_θ[τ_δ]` for all small enough `δ`:
`liminf_{δ → 0} E_θ[τ_δ] / log (1 / δ) ≥ T*(θ)`. -/
theorem eventually_mul_ofReal_log_le_expectedStoppingTime [Nonempty α]
    {A : ℝ → IdentAlg Unit α 𝓨 ℐ} (hA : ∀ᶠ δ in 𝓝[>] 0, task.IsDeltaCorrect (A δ) δ)
    (hθ : θ ∈ task.M) (hi : task.correct θ = {i}) {c : ℝ≥0} (hc : c < task.charTime θ) :
    ∀ᶠ δ in 𝓝[>] 0, c * ENNReal.ofReal (Real.log (1 / δ)) ≤
      expectedStoppingTime (A δ) (Environment.bandit (task.ν θ)) := by
  -- Choose `c < c' < T*(θ)`: then `c log (1 / δ) ≤ c' log (1 / (2.4 δ))` for small `δ`.
  obtain ⟨c', hcc', hc'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hc
  have hcc'_real : (c : ℝ) < c' := mod_cast ENNReal.coe_lt_coe.1 hcc'
  have hL : Tendsto (fun δ : ℝ ↦ Real.log (1 / δ)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Function.comp_def] using
      Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  filter_upwards [hA, self_mem_nhdsWithin,
    hL.eventually_ge_atTop (c' * Real.log 2.4 / (c' - c))] with δ hAδ hδ hLδ
  have h_log : Real.log (1 / (2.4 * δ)) = Real.log (1 / δ) - Real.log 2.4 := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv,
      Real.log_mul (by norm_num) (Set.mem_Ioi.1 hδ).ne']
    ring
  have h_le : (c : ℝ) * Real.log (1 / δ) ≤ c' * Real.log (1 / (2.4 * δ)) := by
    rw [div_le_iff₀ (sub_pos.2 hcc'_real)] at hLδ
    rw [h_log]
    nlinarith
  calc (c : ℝ≥0∞) * ENNReal.ofReal (Real.log (1 / δ))
  _ = ENNReal.ofReal (c * Real.log (1 / δ)) := by
    rw [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  _ ≤ ENNReal.ofReal (c' * Real.log (1 / (2.4 * δ))) := ENNReal.ofReal_le_ofReal h_le
  _ = c' * ENNReal.ofReal (Real.log (1 / (2.4 * δ))) := by
    rw [ENNReal.ofReal_mul c'.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  _ ≤ task.charTime θ * ENNReal.ofReal (Real.log (1 / (2.4 * δ))) := by gcongr
  _ ≤ _ := hAδ.charTime_mul_ofReal_log_le_expectedStoppingTime le_rfl hθ hi

open Filter Topology in
omit [DecidableEq α] in
/-- **Asymptotic optimality from a matching upper bound.** Let `A δ` be `δ`-correct for all small
enough `δ` and let `θ` be an admissible model with a single correct answer. If for every
`c > T*(θ)`, `E_θ[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, then
`E_θ[τ_δ] / log (1 / δ) → T*(θ)` as `δ → 0`: by the lower bound
`eventually_mul_ofReal_log_le_expectedStoppingTime`, the family `A` has the optimal sample
complexity. -/
theorem tendsto_expectedStoppingTime_div_log [Nonempty α] {A : ℝ → IdentAlg Unit α 𝓨 ℐ}
    (hA : ∀ᶠ δ in 𝓝[>] 0, task.IsDeltaCorrect (A δ) δ) (hθ : θ ∈ task.M)
    (hi : task.correct θ = {i})
    (h_upper : ∀ c : ℝ≥0, task.charTime θ < c → ∀ᶠ δ in 𝓝[>] 0,
      expectedStoppingTime (A δ) (Environment.bandit (task.ν θ)) ≤
        c * ENNReal.ofReal (Real.log (1 / δ))) :
    Tendsto (fun δ ↦ expectedStoppingTime (A δ) (Environment.bandit (task.ν θ)) /
      ENNReal.ofReal (Real.log (1 / δ))) (𝓝[>] 0) (𝓝 (task.charTime θ)) := by
  have hL : ∀ᶠ δ in 𝓝[>] 0, 0 < Real.log (1 / δ) := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
    exact Real.log_pos (one_lt_one_div hδ.1 hδ.2)
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · -- Below `T*(θ)`: the lower bound for `δ`-correct algorithms.
    obtain ⟨c, hac, hc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    filter_upwards [eventually_mul_ofReal_log_le_expectedStoppingTime hA hθ hi hc, hL]
      with δ hδ hLδ
    exact hac.trans_le ((ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hLδ).ne')
      (Or.inl ENNReal.ofReal_ne_top)).2 hδ)
  · -- Above `T*(θ)`: the upper bound.
    obtain ⟨c, hc, hca⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    filter_upwards [h_upper c hc] with δ hδ
    exact (ENNReal.div_le_of_le_mul hδ).trans_lt hca

end IdentTask

end LMLExplore.Identification
