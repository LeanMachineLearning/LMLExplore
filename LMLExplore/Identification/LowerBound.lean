/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.ChangeOfMeasure
public import LMLExplore.Identification.SampleComplexity
public import LMLExplore.Identification.Task.DesignRate
public import LMLExplore.Identification.Task.TransportationCost
import LMLExplore.EValues.BipolarRate.Design.Algorithm
import LMLExplore.EValues.TestBet
import LMLExplore.Probability.HasLaw

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

That lower bound is derived here from a sharper one, with the rate of the designs `D*` in place of
`1 / T*(θ)` [EVR26, Note 41, Corollary 2]. Given the history at the stopping time, the probability
that the algorithm stops and answers `i` is a test of level `δ` for the alternatives to `i`, of
power at least `1 - δ` at `θ`, and the bet on it (`ProbabilityTheory.testBet`) is an e-variable at
the stopping time whose expected logarithm at `θ` is at least `kl(1 - δ, δ) = kl(δ, 1 - δ)`. The
Wald inequality with a design bounds that expected logarithm by `D* E_θ[τ]`, so
`E_θ[τ] ≥ kl(δ, 1 - δ) / D*`, and `D* ≤ D(θ, ¬i) ≤ 1 / T*(θ)`
(`IdentTask.designRate_le_inv_charTime`). The change of measure above bounds the expected number
of pulls of each arm (`kl(δ, 1 - δ) ≤ ∑ a, E_θ[N_a(τ)] KL(ν_a(θ), ν_a(λ))`, and
`kl(δ, 1 - δ) ≤ E_θ[N_a(τ)] x` when `D(θ, w, ¬i) ≤ w_a x` for every nonnegative `w`), which the
bound `D* E_θ[τ]` on the expected stopping time does not give.

The binary relative entropy `kl(δ, 1 - δ)` is `LMLExplore.klBer δ (1 - δ)`; it is equivalent to
`log (1 / δ)` as `δ → 0`, and at least `log (1 / (2.4 δ))` for every `δ`, so that
`E_θ[τ] ≥ T*(θ) log (1 / (2.4 δ))`. For a family of `δ`-correct algorithms, this gives
`liminf_{δ → 0} E_θ[τ_δ] / log (1 / δ) ≥ T*(θ)`. That `T*(θ)` is the optimal constant in front
of `log (1 / δ)`, attained by the Track-and-Stop algorithm [GK16, Theorem 14], is proved for
arms dominated by exponential families whose relative entropies are at most the extended
divergences of the families, when Track-and-Stop tracks continuous optimal allocations
with D-tracking, and when it tracks any selection of the optimal allocations, even where these are
not unique, with C-tracking [DK19, Theorem 7]
(`IdentTask.tendsto_expectedStoppingTime_trackAndStop_unionBoundThreshold_div_log_of_klDiv_le` and
`IdentTask.tendsto_expectedStoppingTime_cTrackAndStop_unionBoundThreshold_div_log_of_klDiv_le` in
`Identification/AsymptoticOptimality.lean`, with Gaussian and Bernoulli instances in
`Identification/GaussianThreshold.lean` and `Identification/BernoulliThreshold.lean`).

## Main statements

* `LMLExplore.Identification.expectedPullProportion_mem_simplex`: if `0 < E[τ] < ∞`, the expected
  proportions of pulls `E[N_a(τ)] / E[τ]` form an allocation.
* `IdentTask.IsDeltaCorrect.klBer_le_sum_lintegral_pullCount_mul_klDiv`: the change of measure
  `kl(δ, 1 - δ) ≤ ∑ a, E_θ[N_a(τ)] KL(ν_a(θ), ν_a(λ))` for every alternative `λ` to the answer of
  `θ`.
* `IdentTask.IsDeltaCorrect.klBer_le_expectedStoppingTime_mul_altCost`: the allocation form
  `kl(δ, 1 - δ) ≤ E_θ[τ] D(θ, w, ¬i)`, with `w` the expected proportions of pulls.
* `IdentTask.IsDeltaCorrect.klBer_le_altCost`: the unnormalized form
  `kl(δ, 1 - δ) ≤ D(θ, n, ¬i)`, with `n` the expected numbers of pulls, for `E_θ[τ] < ∞`.
* `IdentTask.IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_of_altCost_le`: if
  `D(θ, w, ¬i) ≤ w a x` for all nonnegative allocations, then `kl(δ, 1 - δ) ≤ E_θ[N_a(τ)] x`.
* `IdentTask.IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_of_altCost_le_restrict`: the same
  bound for an algorithm that is only `δ`-correct on the models of a set `S`.
* `IdentTask.IsDeltaCorrect.klBer_le_designRate_mul_expectedStoppingTime`: the lower bound
  `kl(δ, 1 - δ) ≤ D* E_θ[τ]` with the rate of the designs `D*` against the alternatives.
* `IdentTask.IsDeltaCorrect.charTime_mul_le_expectedStoppingTime`: the lower bound
  `T*(θ) kl(δ, 1 - δ) ≤ E_θ[τ]`.
* `IdentTask.IsDeltaCorrect.charTime_mul_ofReal_log_le_expectedStoppingTime`: the lower bound
  `T*(θ) log (1 / (c δ)) ≤ E_θ[τ]` for `c ≥ 2.4`; for `c = 4` it is the form of
  [LS, Theorem 33.5].
* `IdentTask.eventually_mul_ofReal_log_le_expectedStoppingTime`: the asymptotic lower bound
  `c log (1 / δ) ≤ E_θ[τ_δ]` for all small enough `δ`, for every `c < T*(θ)`, for a family of
  `δ`-correct algorithms.
* `LMLExplore.Identification.limsup_expectedStoppingTime_div_log_le`: if
  `E[τ_δ] ≤ c log (1 / δ)` for small `δ`, for every `c > x`, then
  `limsup_{δ → 0} E[τ_δ] / log (1 / δ) ≤ x`.
* `LMLExplore.Identification.tendsto_expectedStoppingTime_div_log_of_forall_eventually`: if
  `c log (1 / δ) ≤ E[τ_δ]` for small `δ` for every `c < x`, and `E[τ_δ] ≤ c log (1 / δ)` for
  small `δ` for every `c > x`, then `E[τ_δ] / log (1 / δ) → x`.
* `IdentTask.tendsto_expectedStoppingTime_div_log`: a family of `δ`-correct algorithms with
  `E_θ[τ_δ] ≤ c log (1 / δ)` for small `δ`, for every `c > T*(θ)`, has
  `E_θ[τ_δ] / log (1 / δ) → T*(θ)`.

## References

* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 41,
  `results/41-several-arms-bipolar-rate.md`, Section 3.
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

open Filter Topology in
omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] in
/-- **Upper bound on the asymptotic sample complexity.** If, for every `c > x`, the algorithms
`A δ` satisfy `E[τ_δ] ≤ c log (1 / δ)` in the environment `env` for all small enough `δ`, then
`limsup_{δ → 0} E[τ_δ] / log (1 / δ) ≤ x`. -/
theorem limsup_expectedStoppingTime_div_log_le {𝓞 𝓓 : Type*} {m𝓞 : MeasurableSpace 𝓞}
    {m𝓓 : MeasurableSpace 𝓓} {A : ℝ → IdentAlg 𝓞 α 𝓨 𝓓} {env : Environment 𝓞 α 𝓨} {x : ℝ≥0∞}
    (h_upper : ∀ c : ℝ≥0, x < c → ∀ᶠ δ in 𝓝[>] 0,
      expectedStoppingTime (A δ) env ≤ c * ENNReal.ofReal (Real.log (1 / δ))) :
    limsup (fun δ ↦ expectedStoppingTime (A δ) env / ENNReal.ofReal (Real.log (1 / δ)))
      (𝓝[>] 0) ≤ x := by
  refine (limsup_le_iff' (by isBoundedDefault) (by isBoundedDefault)).2 fun y hy ↦ ?_
  obtain ⟨c, hxc, hcy⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hy
  filter_upwards [h_upper c hxc] with δ hδ
  exact (ENNReal.div_le_of_le_mul hδ).trans hcy.le

open Filter Topology in
omit [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] in
/-- **Asymptotic sample complexity from matching bounds.** If, for every `c < x`,
`c log (1 / δ) ≤ E[τ_δ]` for all small enough `δ`, and, for every `c > x`,
`E[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, then `E[τ_δ] / log (1 / δ) → x` as
`δ → 0`. -/
theorem tendsto_expectedStoppingTime_div_log_of_forall_eventually {𝓞 𝓓 : Type*}
    {m𝓞 : MeasurableSpace 𝓞} {m𝓓 : MeasurableSpace 𝓓} {A : ℝ → IdentAlg 𝓞 α 𝓨 𝓓}
    {env : Environment 𝓞 α 𝓨} {x : ℝ≥0∞}
    (h_lower : ∀ c : ℝ≥0, (c : ℝ≥0∞) < x → ∀ᶠ δ in 𝓝[>] 0,
      c * ENNReal.ofReal (Real.log (1 / δ)) ≤ expectedStoppingTime (A δ) env)
    (h_upper : ∀ c : ℝ≥0, x < c → ∀ᶠ δ in 𝓝[>] 0,
      expectedStoppingTime (A δ) env ≤ c * ENNReal.ofReal (Real.log (1 / δ))) :
    Tendsto (fun δ ↦ expectedStoppingTime (A δ) env / ENNReal.ofReal (Real.log (1 / δ)))
      (𝓝[>] 0) (𝓝 x) := by
  have hL : ∀ᶠ δ in 𝓝[>] 0, 0 < Real.log (1 / δ) := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
    exact Real.log_pos (one_lt_one_div hδ.1 hδ.2)
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · -- Below `x`: the lower bound.
    obtain ⟨c, hac, hc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
    filter_upwards [h_lower c hc, hL] with δ hδ hLδ
    exact hac.trans_le ((ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hLδ).ne')
      (Or.inl ENNReal.ofReal_ne_top)).2 hδ)
  · -- Above `x`: the upper bound.
    exact eventually_lt_of_limsup_lt ((limsup_expectedStoppingTime_div_log_le h_upper).trans_lt ha)

namespace IdentTask

variable {mℐ : MeasurableSpace ℐ}
  [MeasurableSingletonClass ℐ] {task : IdentTask α Θ ℐ 𝓨} {A : IdentAlg Unit α 𝓨 ℐ} {δ : ℝ}
  {θ θ' : Θ} {i : ℐ}

/-- **Change of measure for `δ`-correct algorithms** [KCG16, Lemma 1]. Let `A` be `δ`-correct with
`δ ≤ 1 / 2`, let `i` be the only correct answer of the admissible model `θ`, and suppose that `A`
stops almost surely on `θ`. Then for every alternative `θ'` to `i`,
`kl(δ, 1 - δ) ≤ ∑ a, E_θ[N_a(τ)] KL(ν_a(θ), ν_a(θ'))`, where `N_a(τ)` is the number of pulls of the
arm `a` before the stopping time `τ`. -/
theorem IsDeltaCorrect.klBer_le_sum_lintegral_pullCount_mul_klDiv
    [MeasurableSpace.CountablyGenerated 𝓨] (hA : task.IsDeltaCorrect A δ)
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
theorem IsDeltaCorrect.klBer_le_expectedStoppingTime_mul_altCost
    [MeasurableSpace.CountablyGenerated 𝓨] (hA : task.IsDeltaCorrect A δ)
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

/-- **Change of measure against all the alternatives.** Let `A` be `δ`-correct with `δ ≤ 1 / 2`,
let `i` be the only correct answer of the admissible model `θ`, and suppose that `E_θ[τ] < ∞`.
Then `kl(δ, 1 - δ) ≤ D(θ, n, ¬i)`, where the allocation `n` is the vector of the expected numbers
of pulls `n a = E_θ[N_a(τ)]`, not normalized. Every upper bound on the cost of the alternatives
in terms of a single arm, `D(θ, w, ¬i) ≤ w a c`, thus gives the lower bound
`kl(δ, 1 - δ) ≤ E_θ[N_a(τ)] c` on the expected number of pulls of that arm. -/
theorem IsDeltaCorrect.klBer_le_altCost
    [MeasurableSpace.CountablyGenerated 𝓨] (hA : task.IsDeltaCorrect A δ) (hδ : δ ≤ 1 / 2)
    (hθ : θ ∈ task.M) (hi : task.correct θ = {i})
    (h : expectedStoppingTime A (Environment.bandit (task.ν θ)) ≠ ∞) :
    klBer δ (1 - δ) ≤ task.altCost θ (fun a ↦ (∫⁻ ω, (pullCount IT.action a
        (ENat.toNat (A.stoppingTime IT.obs IT.action IT.feedback ω)) ω : ℝ≥0∞)
          ∂(trajMeasure A.alg (Environment.bandit (task.ν θ)))).toReal) i := by
  rw [altCost_def]
  refine le_iInf₂ fun θ' hθ' ↦ (hA.klBer_le_sum_lintegral_pullCount_mul_klDiv hδ hθ hi hθ'
    (.of_expectedStoppingTime_ne_top h)).trans_eq ?_
  simp_rw [cost_def, ENNReal.ofReal_toReal
    ((lintegral_pullCount_le_expectedStoppingTime _).trans_lt h.lt_top).ne]

/-- **Lower bound on the number of pulls of an arm.** Let `A` be `δ`-correct with `δ ≤ 1 / 2`, let
`i` be the only correct answer of the admissible model `θ`, and suppose that `E_θ[τ] < ∞`. If
`D(θ, w, ¬i) ≤ w a x` for every nonnegative allocation `w`, then
`kl(δ, 1 - δ) ≤ E_θ[N_a(τ)] x`. -/
theorem IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_of_altCost_le
    [MeasurableSpace.CountablyGenerated 𝓨]
    (hA : task.IsDeltaCorrect A δ) (hδ : δ ≤ 1 / 2) (hθ : θ ∈ task.M) (hi : task.correct θ = {i})
    (h : expectedStoppingTime A (Environment.bandit (task.ν θ)) ≠ ∞) {a : α} {x : ℝ}
    (h_alt : ∀ w : α → ℝ, 0 ≤ w → task.altCost θ w i ≤ ENNReal.ofReal (w a * x)) :
    klBer δ (1 - δ) ≤ (∫⁻ ω, (pullCount IT.action a
        (ENat.toNat (A.stoppingTime IT.obs IT.action IT.feedback ω)) ω : ℝ≥0∞)
          ∂(trajMeasure A.alg (Environment.bandit (task.ν θ)))) * ENNReal.ofReal x := by
  refine (hA.klBer_le_altCost hδ hθ hi h).trans
    ((h_alt _ fun _ ↦ ENNReal.toReal_nonneg).trans_eq ?_)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal
    ((lintegral_pullCount_le_expectedStoppingTime a).trans_lt h.lt_top).ne]

/-- `IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_of_altCost_le` for an algorithm that is only
`δ`-correct on the models of a set `S`: if `θ ∈ S` is an admissible model of `task` with the single
correct answer `i` and `D(θ, w, ¬i) ≤ w a x` for every nonnegative allocation `w`, the cost being
taken over the alternatives in `S`, then `kl(δ, 1 - δ) ≤ E_θ[N_a(τ)] x`. -/
theorem IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_of_altCost_le_restrict
    [MeasurableSpace.CountablyGenerated 𝓨] {S : Set Θ}
    (hA : (task.restrict S).IsDeltaCorrect A δ) (hδ : δ ≤ 1 / 2) (hθ : θ ∈ task.M) (hθS : θ ∈ S)
    (hi : task.correct θ = {i}) (h : expectedStoppingTime A (Environment.bandit (task.ν θ)) ≠ ∞)
    {a : α} {x : ℝ}
    (h_alt : ∀ w : α → ℝ, 0 ≤ w → (task.restrict S).altCost θ w i ≤ ENNReal.ofReal (w a * x)) :
    klBer δ (1 - δ) ≤ (∫⁻ ω, (pullCount IT.action a
        (ENat.toNat (A.stoppingTime IT.obs IT.action IT.feedback ω)) ω : ℝ≥0∞)
          ∂(trajMeasure A.alg (Environment.bandit (task.ν θ)))) * ENNReal.ofReal x := by
  simpa using hA.klBer_le_lintegral_pullCount_mul_of_altCost_le hδ
    (by rw [M_restrict]; exact ⟨hθ, hθS⟩) (by rwa [correct_restrict]) (by simpa using h) h_alt

omit [DecidableEq α] in
/-- `IsDeltaCorrect.klBer_le_designRate_mul_expectedStoppingTime` for `0 < δ`. -/
private lemma IsDeltaCorrect.klBer_le_designRate_mul_expectedStoppingTime_of_pos
    (hA : task.IsDeltaCorrect A δ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hθ : θ ∈ task.M)
    (hi : task.correct θ = {i}) (h_alt : (task.alt i).Nonempty)
    (hstop : StopsAS A (Environment.bandit (task.ν θ))) :
    (klBer δ (1 - δ) : EReal) ≤
      designRate (fun a ↦ task.ν θ a) ((fun θ' a ↦ task.ν θ' a) '' task.alt i) *
        (expectedStoppingTime A (Environment.bandit (task.ν θ)) : EReal) := by
  classical
  have hseq := IT.isAlgEnvSeq_trajMeasure A.alg (Environment.bandit (task.ν θ))
  -- the probability `φ h` that `A` stops and answers `i` given the stopped history `h` is a test
  -- of level `δ` against the alternatives to `i`, of power at least `1 - δ` at `θ`
  set φ : (Σ n : ℕ, Hist Unit α 𝓨 n) → ℝ≥0∞ := A.stopSet.indicator fun h ↦ A.output h {i}
  have hφm : Measurable φ :=
    (A.output.measurable_coe (measurableSet_singleton i)).indicator A.measurableSet_stopSet
  have hφ1 (h : Σ n : ℕ, Hist Unit α 𝓨 n) : φ h ≤ 1 :=
    Set.indicator_apply_le' (fun _ ↦ prob_le_one) fun _ ↦ zero_le_one
  have hφθ : ENNReal.ofReal (1 - δ) ≤
      ∫⁻ h, φ h ∂stoppedHistMeasure A.alg (Environment.bandit (task.ν θ)) A.stopSet := by
    rw [lintegral_indicator_output_eq_histOutputMeasure]
    exact ENNReal.ofReal_le_of_le_toReal (hA.one_sub_le_measureReal_histOutputMeasure hθ hi)
  -- the bet on that test is an e-variable at the stopping time against the alternatives
  set G := testBet δ (1 - δ) φ
  have hGm : Measurable G := hφm.testBet
  have hGalt : ∀ (ν : Kernel α 𝓨) [IsMarkovKernel ν], ν ∈ task.ν '' task.alt i →
      ∫⁻ h in A.stopSet, G h ∂stoppedHistMeasure A.alg (Environment.bandit ν) A.stopSet ≤ 1 := by
    rintro _ _ ⟨θ', hθ', rfl⟩
    refine (setLIntegral_le_lintegral _ _).trans (lintegral_testBet_le_one hφm hφ1
      ⟨hδ0, by linarith⟩ (by linarith) (by linarith) prob_le_one ?_)
    rw [lintegral_indicator_output_eq_histOutputMeasure]
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hδ0.le).2
      (hA.measureReal_histOutputMeasure_le hθ')
  have hτ : ∀ᵐ ω ∂trajMeasure A.alg (Environment.bandit (task.ν θ)),
      hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) A.stopSet 0 ω ≠ ⊤ :=
    (stopsAS_iff_ae_stoppingTime_ne_top hseq).1 hstop
  have hlog : AEMeasurable (fun h ↦ ENNReal.log (G h))
      (stoppedHistMeasure A.alg (Environment.bandit (task.ν θ)) A.stopSet) :=
    (ENNReal.measurable_log.comp hGm).aemeasurable
  -- `kl(δ, 1 - δ) = kl(1 - δ, δ) ≤ 𝔼_θ[log G] ≤ D* 𝔼_θ[τ]`
  calc (klBer δ (1 - δ) : EReal) = klBer (1 - δ) δ := by
        rw [← klBer_one_sub_one_sub, sub_sub_cancel]
  _ ≤ ∫ᵉ h, ENNReal.log (G h)
      ∂stoppedHistMeasure A.alg (Environment.bandit (task.ν θ)) A.stopSet :=
    klBer_le_eintegral_log_testBet hφm hφ1 hδ0 (by linarith) (by linarith) hφθ
  _ = ∫ᵉ ω, ENNReal.log (G (stoppedValue (sigmaHistory IT.obs IT.action IT.feedback)
        (hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) A.stopSet 0) ω))
          ∂trajMeasure A.alg (Environment.bandit (task.ν θ)) :=
    ((hseq.hasLaw_stoppedValue_sigmaHistory A.measurableSet_stopSet).eintegral_comp hlog).symm
  _ ≤ _ := hseq.eintegral_log_le_designRate_mul_lintegral (Λ := task.ν '' task.alt i)
      (by rintro _ ⟨θ', -, rfl⟩; infer_instance) (h_alt.image _) A.measurableSet_stopSet hGm
      hGalt hτ
  _ = _ := by rw [Set.image_image, expectedStoppingTime_def, IdentAlg.stoppingTime_def]

omit [DecidableEq α] in
/-- **Lower bound on the sample complexity with the rate of the designs** [EVR26, Note 41,
Corollary 2]. Let `A` be `δ`-correct with `δ ≤ 1 / 2`, let `i` be the only correct answer of the
admissible model `θ`, and suppose that `i` has an alternative and that `A` stops almost surely on
`θ`. Then `kl(δ, 1 - δ) ≤ D* E_θ[τ]`, where `D*` is the rate of the designs of the laws of the arms
at `θ` against those at the alternatives to `i`: `E_θ[τ] ≥ kl(δ, 1 - δ) / D*`.

This is the Wald inequality with a design
(`Learning.IsAlgEnvSeq.eintegral_log_le_designRate_mul_lintegral`) for the bet on the event that
`A` stops and answers `i`, randomized by the output rule. The product is in `EReal`; since
`D* ≤ 1 / T*(θ)` (`IdentTask.designRate_le_inv_charTime`), it implies the bound
`T*(θ) kl(δ, 1 - δ) ≤ E_θ[τ]` of `IsDeltaCorrect.charTime_mul_le_expectedStoppingTime`. -/
theorem IsDeltaCorrect.klBer_le_designRate_mul_expectedStoppingTime
    (hA : task.IsDeltaCorrect A δ) (hδ : δ ≤ 1 / 2) (hθ : θ ∈ task.M)
    (hi : task.correct θ = {i}) (h_alt : (task.alt i).Nonempty)
    (hstop : StopsAS A (Environment.bandit (task.ν θ))) :
    (klBer δ (1 - δ) : EReal) ≤
      designRate (fun a ↦ task.ν θ a) ((fun θ' a ↦ task.ν θ' a) '' task.alt i) *
        (expectedStoppingTime A (Environment.bandit (task.ν θ)) : EReal) := by
  rcases lt_or_ge 0 δ with hδ0 | hδ0
  · exact hA.klBer_le_designRate_mul_expectedStoppingTime_of_pos hδ0 hδ hθ hi h_alt hstop
  -- for `δ ≤ 0`, `A` is `ε`-correct for every `ε > 0`, and `kl(ε, 1 - ε)` is unbounded as
  -- `ε → 0`, so that the right-hand side is `⊤`
  rw [klBer_one_sub_right_eq_top fun h ↦ hδ0.not_gt h.1]
  refine ((EReal.eq_top_iff_forall_lt _).2 fun y ↦ ?_).ge
  obtain ⟨ε, hy, hε⟩ := ((tendsto_klBer_one_sub_right_nhdsGT_zero.eventually
    (eventually_gt_nhds (ENNReal.ofReal_lt_top (r := y)))).and
    (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2))).exists
  calc (y : EReal) ≤ (ENNReal.ofReal y : EReal) := by
        rw [EReal.coe_ennreal_ofReal]
        exact EReal.coe_le_coe_iff.2 (le_max_left _ _)
  _ < (klBer ε (1 - ε) : EReal) := EReal.coe_ennreal_lt_coe_ennreal_iff.2 hy
  _ ≤ _ := hA.mono (hδ0.trans hε.1.le) |>.klBer_le_designRate_mul_expectedStoppingTime_of_pos hε.1
    hε.2 hθ hi h_alt hstop

omit [DecidableEq α] in
/-- **Lower bound on the sample complexity** [GK16, Theorem 1; LS, Theorem 33.5]. Let `A` be
`δ`-correct with `δ ≤ 1 / 2` and let `θ` be an admissible model with a single correct answer.
Then `T*(θ) kl(δ, 1 - δ) ≤ E_θ[τ]`. It follows from
`IsDeltaCorrect.klBer_le_designRate_mul_expectedStoppingTime`, `E_θ[τ] ≥ kl(δ, 1 - δ) / D*`, and
`D* ≤ 1 / T*(θ)`. -/
theorem IsDeltaCorrect.charTime_mul_le_expectedStoppingTime [Nonempty α]
    (hA : task.IsDeltaCorrect A δ) (hδ : δ ≤ 1 / 2) (hθ : θ ∈ task.M)
    (hi : task.correct θ = {i}) :
    task.charTime θ * klBer δ (1 - δ) ≤ expectedStoppingTime A (Environment.bandit (task.ν θ)) := by
  set E := expectedStoppingTime A (Environment.bandit (task.ν θ))
  -- If `E_θ[τ] = ∞` there is nothing to prove; otherwise `A` stops almost surely on `θ`.
  rcases eq_or_ne E ∞ with h | h
  · exact h ▸ le_top
  -- If `i` has no alternative, then `D(θ) = ∞` and `T*(θ) = 0`.
  rcases (task.alt i).eq_empty_or_nonempty with h_alt | h_alt
  · simp [charTime_eq_inv_answerValue _ hi, answerValue_eq_top_of_alt_eq_empty _ h_alt]
  -- `kl(δ, 1 - δ) ≤ D* E_θ[τ] ≤ E_θ[τ] / T*(θ)`
  have h_le : klBer δ (1 - δ) ≤ (task.charTime θ)⁻¹ * E := by
    rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_ennreal_mul]
    exact (hA.klBer_le_designRate_mul_expectedStoppingTime hδ hθ hi h_alt
      (.of_expectedStoppingTime_ne_top h)).trans (mul_le_mul_of_nonneg_right
        (task.designRate_le_inv_charTime (hi ▸ Set.mem_singleton i)) (EReal.coe_ennreal_nonneg _))
  calc task.charTime θ * klBer δ (1 - δ) ≤ task.charTime θ * ((task.charTime θ)⁻¹ * E) := by
        gcongr
  _ ≤ E := by
    rw [← mul_assoc]
    exact mul_le_of_le_one_left' (ENNReal.mul_inv_le_one _)

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
      expectedStoppingTime A (Environment.bandit (task.ν θ)) :=
  mul_ofReal_log_le_of_mul_klBer_le hc fun hδ ↦ hA.charTime_mul_le_expectedStoppingTime hδ hθ hi

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
      ENNReal.ofReal (Real.log (1 / δ))) (𝓝[>] 0) (𝓝 (task.charTime θ)) :=
  tendsto_expectedStoppingTime_div_log_of_forall_eventually
    (fun _ hc ↦ eventually_mul_ofReal_log_le_expectedStoppingTime hA hθ hi hc) h_upper

end IdentTask

end LMLExplore.Identification
