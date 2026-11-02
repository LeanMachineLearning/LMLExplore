/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.SampleComplexity
public import LMLExplore.Identification.Task.TransportationCost
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Generalized likelihood ratio stopping rules

A fixed-confidence identification algorithm for a task stops when the data rule out every
alternative to some answer. Let `Z n h λ ∈ [0, ∞]` measure how much the history `h` of the first
`n` rounds speaks against the model `λ`: in the parametric setting of Chernoff (1959) and
Garivier and Kaufmann (2016), `Z n h λ` is the log-likelihood ratio of the maximum-likelihood
model against `λ`, which for arms in exponential families is `∑ a, N_a d(μ̂_a, λ_a)` with the pull
counts `N_a`, the empirical means `μ̂_a` and the divergence `d` of the family. The
*generalized likelihood ratio statistic* of the answer `i` is the smallest such evidence against an
alternative to `i`,
`GLR_n(h, ¬i) = inf_{λ ∈ ¬i} Z n h λ`.
The GLRT (Chernoff's stopping rule) runs any sampling rule, recommends an answer `rec n h` after
each round and stops as soon as `GLR_n(h, ¬rec n h)` exceeds a threshold `β n`.

Whatever the sampling rule and the recommendation rule, if the GLRT stops with an answer `i` that
is not correct for the true model `θ`, then `θ` is an alternative to `i`, so that
`β n < GLR_n(h, ¬i) ≤ Z n h θ`: the evidence against the true model exceeds the threshold. The
probability of stopping with an incorrect answer is therefore at most the probability of the
deviation event `∃ n, β n < Z n hₙ θ` of the true model, which time-uniform concentration
inequalities bound by `δ` for suitable thresholds. Together with almost sure stopping, this makes
the GLRT `δ`-PAC on every task.

The sample complexity of the GLRT reduces to the growth of the GLR statistic along the run. If on
an event `E T` the statistic after `T` rounds exceeds the threshold, then `τ ≤ T` on `E T`, and
`𝔼[τ] ≤ T₀ + ∑_{T ≥ T₀} P((E T)ᶜ)`. If the statistic grows linearly, at least `κ T` on `E T`, and
the thresholds are `log (1 / δ) + o(T)`, then the threshold is crossed on `E T` as soon as
`T ≥ log (1 / δ) / η` for any `η < κ`, hence `𝔼[τ_δ] ≤ c log (1 / δ)` for small `δ` and every
`c > 1 / κ` when `∑ T, P((E T)ᶜ) < ∞`. Each sampling rule then only has to prove the linear growth
of the statistic, typically from the convergence of its empirical proportions of pulls to an
optimal allocation, with `κ` close to the inverse of the characteristic time.

## Main definitions

* `IdentTask.glr task Z n h i`: the generalized likelihood ratio statistic
  `inf_{λ ∈ ¬i} Z n h λ` of the answer `i` after `n` rounds with history `h`.
* `IdentTask.glrt task Z alg β rec hrec hstop`: the identification algorithm with sampling rule
  `alg` that stops after `n` rounds with history `h` if `β n < task.glr Z n h (rec n h)` and then
  answers `rec n h`.

## Main statements

* `IdentTask.glr_eq_altCost`: when the statistic is the transportation cost `cost_θ₀(w, ·)` of a
  model `θ₀` and an allocation `w`, the GLR statistic is the cost `D(θ₀, w, ¬i)` of the
  alternatives.
* `IdentTask.stoppingTime_glrt_le`: the GLRT has stopped after `n` rounds if its stopping
  condition holds after `n` rounds.
* `IdentTask.measureReal_histOutputMeasure_glrt_le`: for every sampling rule and every model `θ`,
  the probability that the GLRT stops with an answer that is not correct for `θ` is at most the
  probability of the deviation event `∃ n, β n < Z n hₙ θ`.
* `IdentTask.measureReal_stoppingTime_ne_top_and_notMem_le_of_isRun_glrt`: the same bound along
  every run of the GLRT.
* `IdentTask.isDeltaPAC_glrt`: if the deviation event has probability at most `δ` on every
  admissible model and the GLRT stops almost surely, then it is `δ`-PAC on the task.
* `IdentTask.expectedStoppingTime_glrt_le_add_tsum`: if the stopping condition holds after `T`
  rounds on an event `E T` for every `T ≥ T₀`, then `𝔼[τ] ≤ T₀ + ∑_{T ≥ T₀} P((E T)ᶜ)`.
* `IdentTask.eventually_expectedStoppingTime_glrt_le`: if the GLR statistic of the recommended
  answer is at least `κ T` after `T` rounds on events `E T` with `∑ T, P((E T)ᶜ) < ∞`, and the
  thresholds are at most `log (1 / δ) + f T` with `f T = o(T)` from above, then
  `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every `c > 1 / κ`.
* `IdentTask.eventually_expectedStoppingTime_glrt_le_of_isBigO`: the same conclusion for
  thresholds at most `log (r T / δ)` with `r T = O(T ^ p)`.

## References

* [C59] H. Chernoff, *Sequential design of experiments*, Ann. Math. Statist. 30 (1959).
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Proposition 12 and the proof of Theorem 14.
* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, Theorem 10.
* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019, Theorem 1 and Lemma 1.
-/

public section

open MeasureTheory ProbabilityTheory Learning

open scoped ENNReal

namespace LMLExplore.Identification.IdentTask

variable {α Θ ℐ 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  (task : IdentTask α Θ ℐ 𝓨) {Z Z' : (n : ℕ) → Hist Unit α 𝓨 n → Θ → ℝ≥0∞} {n : ℕ}
  {h : Hist Unit α 𝓨 n} {θ : Θ} {i j : ℐ}

/-! ### The generalized likelihood ratio statistic -/

/-- The *generalized likelihood ratio statistic* `GLR_n(h, ¬i) = inf_{λ ∈ ¬i} Z n h λ` of the
answer `i` after `n` rounds with history `h`, for the statistic `Z`: the smallest evidence
`Z n h λ` against an alternative `λ` to `i`. It is `∞` if `i` has no alternative.

For the log-likelihood ratio `Z n h λ` of the maximum-likelihood model against `λ`, this is the
generalized likelihood ratio of the composite hypothesis `¬i`. -/
noncomputable def glr (Z : (n : ℕ) → Hist Unit α 𝓨 n → Θ → ℝ≥0∞) (n : ℕ) (h : Hist Unit α 𝓨 n)
    (i : ℐ) : ℝ≥0∞ :=
  ⨅ θ' ∈ task.alt i, Z n h θ'

lemma glr_def (Z : (n : ℕ) → Hist Unit α 𝓨 n → Θ → ℝ≥0∞) (n : ℕ) (h : Hist Unit α 𝓨 n)
    (i : ℐ) : task.glr Z n h i = ⨅ θ' ∈ task.alt i, Z n h θ' := (rfl)

lemma le_glr_iff {c : ℝ≥0∞} : c ≤ task.glr Z n h i ↔ ∀ θ' ∈ task.alt i, c ≤ Z n h θ' :=
  le_iInf₂_iff

lemma glr_le (hθ : θ ∈ task.alt i) : task.glr Z n h i ≤ Z n h θ :=
  iInf₂_le θ hθ

/-- The GLR statistic of an answer that is not correct for an admissible model `θ` is at most the
evidence against `θ`. -/
lemma glr_le_of_notMem_correct (hθ : θ ∈ task.M) (hi : i ∉ task.correct θ) :
    task.glr Z n h i ≤ Z n h θ :=
  task.glr_le ((task.mem_alt_iff).2 ⟨hθ, hi⟩)

lemma glr_mono (hZ : ∀ θ' ∈ task.alt i, Z n h θ' ≤ Z' n h θ') :
    task.glr Z n h i ≤ task.glr Z' n h i :=
  iInf₂_mono hZ

/-- The GLR statistic is antitone in the set of alternatives. -/
lemma glr_le_glr_of_alt_subset (hij : task.alt i ⊆ task.alt j) :
    task.glr Z n h j ≤ task.glr Z n h i :=
  biInf_mono hij

/-- The GLR statistic of an answer without alternatives is `∞`. -/
lemma glr_eq_top_of_alt_eq_empty (hi : task.alt i = ∅) : task.glr Z n h i = ∞ := by
  simp [glr_def, hi]

/-- The GLR statistic of the restriction of a task to `S` is the infimum over the alternatives in
`S`. -/
lemma glr_restrict (S : Set Θ) :
    (task.restrict S).glr Z n h i = ⨅ θ' ∈ task.alt i ∩ S, Z n h θ' := by
  rw [glr_def, alt_restrict]

/-- When the statistic is the transportation cost `cost_θ₀(w, ·)` from a model `θ₀` with the
allocation `w`, the GLR statistic is the cost `D(θ₀, w, ¬i)` of the alternatives to `i`. For arms
in exponential families whose vector of empirical means `μ̂` is a model, this applies with
`θ₀ = μ̂` and `w` the pull counts `N(h)`, and gives `GLR_n(h, ¬i) = D(μ̂, N(h), ¬i)`. -/
lemma glr_eq_altCost [Fintype α] {w : α → ℝ} {θ₀ : Θ}
    (hZ : ∀ θ' ∈ task.alt i, Z n h θ' = task.cost w θ₀ θ') :
    task.glr Z n h i = task.altCost θ₀ w i := by
  rw [glr_def, altCost_def]
  exact iInf_congr fun θ' ↦ iInf_congr fun hθ' ↦ hZ θ' hθ'

/-! ### The GLRT -/

variable (Z) {mℐ : MeasurableSpace ℐ} (alg : Algorithm Unit α 𝓨) (β : ℕ → ℝ≥0∞)
  (rec : (n : ℕ) → Hist Unit α 𝓨 n → ℐ) (hrec : ∀ n, Measurable (rec n))
  (hstop : ∀ n, MeasurableSet {h | β n < task.glr Z n h (rec n h)})

/-- The *GLRT* with sampling rule `alg`, statistic `Z`, thresholds `β` and recommendation rule
`rec` (Chernoff's stopping rule): after `n` rounds with history `h`, it stops if the GLR statistic
of the recommended answer `rec n h` exceeds the threshold `β n`, and then answers `rec n h`. -/
noncomputable def glrt : IdentAlg Unit α 𝓨 ℐ :=
  ofStop alg (fun n h ↦ β n < task.glr Z n h (rec n h)) hstop
    fun n ↦ Kernel.deterministic (rec n) (hrec n)

lemma glrt_def : task.glrt Z alg β rec hrec hstop = ofStop alg
    (fun n h ↦ β n < task.glr Z n h (rec n h)) hstop
    (fun n ↦ Kernel.deterministic (rec n) (hrec n)) := (rfl)

@[simp]
lemma alg_glrt : (task.glrt Z alg β rec hrec hstop).alg = alg := by
  rw [glrt_def, alg_ofStop]

@[simp]
lemma mem_stopSet_glrt {h : Σ n, Hist Unit α 𝓨 n} :
    h ∈ (task.glrt Z alg β rec hrec hstop).stopSet ↔ β h.1 < task.glr Z h.1 h.2 (rec h.1 h.2) := by
  rw [glrt_def, mem_stopSet_ofStop]

@[simp]
lemma output_glrt (h : Σ n, Hist Unit α 𝓨 n) :
    (task.glrt Z alg β rec hrec hstop).output h = Measure.dirac (rec h.1 h.2) := by
  rw [glrt_def, output_ofStop, Kernel.sigma_apply, Kernel.deterministic_apply]

/-- The output rule of the GLRT is the deterministic kernel of the recommendation rule. -/
lemma output_glrt_eq_deterministic :
    (task.glrt Z alg β rec hrec hstop).output = Kernel.deterministic (fun h ↦ rec h.1 h.2)
      (measurable_sigma_of_measurable_comp_mk hrec) := by
  ext h : 1
  rw [output_glrt, Kernel.deterministic_apply]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨}

/-- The GLRT has stopped after `n` rounds if its stopping condition holds after `n` rounds. -/
lemma stoppingTime_glrt_le {ω : Ω}
    (hn : β n < task.glr Z n (history O X Y n ω) (rec n (history O X Y n ω))) :
    (task.glrt Z alg β rec hrec hstop).stoppingTime O X Y ω ≤ n :=
  IdentAlg.stoppingTime_le_of_mem_stopSet ((task.mem_stopSet_glrt Z alg β rec hrec hstop).2 hn)

/-! ### Error probability of the GLRT -/

/-- **Error probability of the GLRT**, for every sampling rule (the reduction in the proof of
[GK16, Proposition 12]). For every model `θ`, the probability that the GLRT stops with an answer
that is not correct for `θ` is at most the probability of the deviation event
`∃ n, β n < Z n hₙ θ` of `θ`, along any algorithm-environment sequence of the sampling rule. Only
the probabilities in `env = stationaryEnv (task.ν θ)` matter for correctness; the inclusion of
the events holds in every environment. -/
theorem measureReal_histOutputMeasure_glrt_le {env : Environment Unit α 𝓨}
    (hseq : IsAlgEnvSeq O X Y alg env P) (hθ : θ ∈ task.M)
    (hc : MeasurableSet (task.correct θ)) :
    (histOutputMeasure (task.glrt Z alg β rec hrec hstop) env).real
        {p | p.1 ∈ (task.glrt Z alg β rec hrec hstop).stopSet ∧ p.2 ∉ task.correct θ} ≤
      P.real {ω | ∃ n, β n < Z n (history O X Y n ω) θ} := by
  set A := task.glrt Z alg β rec hrec hstop
  have hg : Measurable fun h : Σ n, Hist Unit α 𝓨 n ↦ (h, rec h.1 h.2) :=
    measurable_id.prodMk (measurable_sigma_of_measurable_comp_mk hrec)
  have hS := A.measurableSet_mem_stopSet_and_notMem hc
  have h_law : HasLaw (A.stoppedHist O X Y) (stoppedHistMeasure A.alg env A.stopSet) P :=
    (task.alg_glrt Z alg β rec hrec hstop ▸ hseq).hasLaw_stoppedValue_sigmaHistory
      A.measurableSet_stopSet
  rw [histOutputMeasure_def, output_glrt_eq_deterministic, Measure.compProd_deterministic,
    map_measureReal_apply hg hS, ← h_law.map_eq,
    map_measureReal_apply_of_aemeasurable h_law.aemeasurable (hg hS)]
  -- The stopped history is the history of the first `n` rounds, for `n` the stopping time.
  refine measureReal_mono fun ω ⟨hω_stop, hω_wrong⟩ ↦ ?_
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (IdentAlg.stoppedHist_mem_stopSet_iff.1 hω_stop)
  rw [IdentAlg.stoppedHist_eq_of_stoppingTime_eq hn.symm] at hω_stop hω_wrong
  rw [mem_stopSet_glrt] at hω_stop
  exact ⟨n, hω_stop.trans_le (task.glr_le_of_notMem_correct hθ hω_wrong)⟩

/-- **Error probability of the GLRT along a run**, for every sampling rule. Along every run of the
GLRT, the probability that it stops with an answer that is not correct for the model `θ` is at
most the probability of the deviation event `∃ n, β n < Z n hₙ θ` of `θ`. -/
theorem measureReal_stoppingTime_ne_top_and_notMem_le_of_isRun_glrt {env : Environment Unit α 𝓨}
    {out : Ω → ℐ} (hrun : (task.glrt Z alg β rec hrec hstop).IsRun env O X Y out P)
    (hθ : θ ∈ task.M) (hc : MeasurableSet (task.correct θ)) :
    P.real {ω | (task.glrt Z alg β rec hrec hstop).stoppingTime O X Y ω ≠ ⊤ ∧
        out ω ∉ task.correct θ} ≤
      P.real {ω | ∃ n, β n < Z n (history O X Y n ω) θ} := by
  have h_eq := hrun.hasLaw_stoppedHist_output.measureReal_eq
    ((task.glrt Z alg β rec hrec hstop).measurableSet_mem_stopSet_and_notMem hc)
  simp only [IdentAlg.stoppedHist_mem_stopSet_iff] at h_eq
  rw [h_eq]
  exact task.measureReal_histOutputMeasure_glrt_le Z alg β rec hrec hstop
    (task.alg_glrt Z alg β rec hrec hstop ▸ hrun.isAlgEnvSeq) hθ hc

/-- **The GLRT is `δ`-PAC**, for every sampling rule and every task ([GK16, Proposition 12],
[DKM19, Theorem 1], [DK19, Theorem 10]): if on every admissible model `θ` the deviation event
`∃ n, β n < Z n hₙ θ` has probability at most `δ` and the GLRT stops almost surely, then it is
`δ`-PAC on the task. -/
theorem isDeltaPAC_glrt {δ : ℝ} (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (hdev : ∀ θ ∈ task.M, (trajMeasure alg (stationaryEnv (task.ν θ))).real
      {ω | ∃ n, β n < Z n (history IT.obs IT.action IT.feedback n ω) θ} ≤ δ)
    (h_stops : ∀ θ ∈ task.M,
      StopsAS (task.glrt Z alg β rec hrec hstop) (stationaryEnv (task.ν θ))) :
    task.IsDeltaPAC (task.glrt Z alg β rec hrec hstop) δ := by
  set A := task.glrt Z alg β rec hrec hstop
  have h_correct : task.IsDeltaCorrect A δ := by
    refine isDeltaCorrect_iff.2 fun θ hθ ↦ ?_
    set μ := histOutputMeasure A (stationaryEnv (task.ν θ))
    -- Since the GLRT stops almost surely, not stopping does not contribute to the error.
    have h_ae : ∀ᵐ p ∂μ, p.1 ∈ A.stopSet := ae_of_ae_map measurable_fst.aemeasurable <| by
      rw [← Measure.fst, fst_histOutputMeasure]
      exact stopsAS_iff.1 (h_stops θ hθ)
    calc μ.real {p | p.1 ∉ A.stopSet ∨ p.2 ∉ task.correct θ}
    _ = μ.real {p | p.1 ∈ A.stopSet ∧ p.2 ∉ task.correct θ} :=
      measureReal_congr <| Filter.eventuallyEqSet_iff.2 <| h_ae.mono fun p hp ↦ by simp [hp]
    _ ≤ δ := (task.measureReal_histOutputMeasure_glrt_le Z alg β rec hrec hstop
      (IT.isAlgEnvSeq_trajMeasure alg _) hθ (hc θ hθ)).trans (hdev θ hθ)
  exact isDeltaPAC_iff_isDeltaPAC.2 <| Identification.isDeltaPAC_iff.2
    ⟨h_correct.isPAC hc, fun θ ↦ h_stops θ θ.2⟩

/-! ### Sample complexity of the GLRT -/

/-- **Sample complexity of the GLRT from good events** [DKM19, Lemma 1], for every sampling rule.
If, along an algorithm-environment sequence of the sampling rule in `env`, the stopping condition
of the GLRT holds after `T` rounds on an event `E T` for every `T ≥ T₀`, then
`𝔼[τ] ≤ T₀ + ∑_{T ≥ T₀} P((E T)ᶜ)`. -/
theorem expectedStoppingTime_glrt_le_add_tsum {env : Environment Unit α 𝓨}
    (hseq : IsAlgEnvSeq O X Y alg env P) {E : ℕ → Set Ω} {T₀ : ℕ}
    (hE : ∀ T ≥ T₀, ∀ ω ∈ E T,
      β T < task.glr Z T (history O X Y T ω) (rec T (history O X Y T ω))) :
    expectedStoppingTime (task.glrt Z alg β rec hrec hstop) env ≤ T₀ + ∑' T, P (E (T + T₀))ᶜ :=
  expectedStoppingTime_le_add_tsum_measure_compl (by rwa [alg_glrt])
    fun T hT ω hω ↦ task.stoppingTime_glrt_le Z alg β rec hrec hstop (hE T hT ω hω)

end LMLExplore.Identification.IdentTask

/-! ### Asymptotic sample complexity of the GLRT -/

namespace LMLExplore.Identification.IdentTask

open Filter Topology Real

open scoped NNReal

variable {α Θ ℐ 𝓨 : Type*} {mα : MeasurableSpace α} {m𝓨 : MeasurableSpace 𝓨}
  {mℐ : MeasurableSpace ℐ} (task : IdentTask α Θ ℐ 𝓨) (Z : (n : ℕ) → Hist Unit α 𝓨 n → Θ → ℝ≥0∞)
  (alg : Algorithm Unit α 𝓨) {β : ℝ → ℕ → ℝ≥0∞} (rec : (n : ℕ) → Hist Unit α 𝓨 n → ℐ)
  (hrec : ∀ n, Measurable (rec n))
  (hstop : ∀ δ n, MeasurableSet {h | β δ n < task.glr Z n h (rec n h)})
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → α} {Y : ℕ → Ω → 𝓨} {env : Environment Unit α 𝓨}
  {E : ℕ → Set Ω} {κ c : ℝ≥0} {T₀ : ℕ}

/-- **Asymptotic sample complexity of the GLRT** (the reduction in the proof of
[GK16, Theorem 14]), for every sampling rule. Consider the GLRTs with thresholds
`β δ T ≤ log (1 / δ) + f T`, where `f T ≤ ε T` eventually for every `ε > 0`. Suppose that, along an
algorithm-environment sequence of the sampling rule in `env`, the GLR statistic of the recommended
answer after `T` rounds is at least `κ T` on an event `E T`, for every `T ≥ T₀`, and that
`∑ T, P((E T)ᶜ) < ∞`. Then `𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every `c > 1 / κ`,
that is, `limsup_{δ → 0} 𝔼[τ_δ] / log (1 / δ) ≤ 1 / κ`.

For an asymptotically optimal sampling rule, `κ` is any rate below the inverse `T*(θ)⁻¹` of the
characteristic time. -/
theorem eventually_expectedStoppingTime_glrt_le (hseq : IsAlgEnvSeq O X Y alg env P)
    (hE_sum : ∑' T, P (E T)ᶜ ≠ ∞) (hκc : 1 < κ * c)
    (hE : ∀ T ≥ T₀, ∀ ω ∈ E T,
      κ * T ≤ task.glr Z T (history O X Y T ω) (rec T (history O X Y T ω)))
    {f : ℕ → ℝ} (hf : ∀ ε > 0, ∀ᶠ T in atTop, f T ≤ ε * T)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ T ≥ T₀, β δ T ≤ ENNReal.ofReal (log (1 / δ) + f T)) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.glrt Z alg (β δ) rec hrec (hstop δ)) env ≤
      c * ENNReal.ofReal (log (1 / δ)) := by
  have hκc' : 1 < (κ : ℝ) * c := mod_cast hκc
  have hc : 0 < (c : ℝ) := pos_of_mul_pos_right (one_pos.trans hκc') κ.coe_nonneg
  -- Choose `η` with `1 / c < η < κ`: if `log (1 / δ) ≤ η T`, the threshold is below `κ T`.
  obtain ⟨η, hcη, hηκ⟩ : ∃ η, (c : ℝ)⁻¹ < η ∧ η < κ :=
    exists_between ((inv_lt_iff_one_lt_mul₀' hc).2 (by linarith))
  have hη : 0 < η := (inv_pos.2 hc).trans hcη
  have hκ : 0 < (κ : ℝ) := hη.trans hηκ
  have hηc : 0 < (c : ℝ) - η⁻¹ := sub_pos.2 (inv_lt_of_inv_lt₀ hc hcη)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (hf ((κ - η) / 2) (by linarith))
  set S := (∑' T, P (E T)ᶜ).toReal
  set M := max (max T₀ T₁) 1
  have hL : Tendsto (fun δ : ℝ ↦ log (1 / δ)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Function.comp_def] using tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  filter_upwards [hβ, hL.eventually_ge_atTop ((M + 1 + S) / (c - η⁻¹))] with δ hβδ hLδ
  set L := log (1 / δ)
  have hL0 : 0 ≤ L := (by positivity : 0 ≤ (M + 1 + S) / (c - η⁻¹)).trans hLδ
  -- From `N = max M ⌈L / η⌉` rounds on, the stopping condition holds on `E T`.
  set N := max M ⌈L / η⌉₊
  have h_stop : ∀ T ≥ N, ∀ ω ∈ E T,
      β δ T < task.glr Z T (history O X Y T ω) (rec T (history O X Y T ω)) := by
    intro T hT ω hω
    have hT₀ : T₀ ≤ T := by omega
    have hT1 : (1 : ℝ) ≤ T := mod_cast (show 1 ≤ T by omega)
    have hLT : L ≤ η * T := by
      rw [← div_le_iff₀' hη]
      exact (Nat.le_ceil _).trans (mod_cast (le_max_right _ _).trans hT)
    have hfT := hT₁ T (by omega)
    calc β δ T
    _ ≤ ENNReal.ofReal (L + f T) := hβδ T hT₀
    _ < ENNReal.ofReal (κ * T) := by
      refine (ENNReal.ofReal_lt_ofReal_iff (mul_pos hκ (by linarith))).2 ?_
      nlinarith
    _ = κ * T := by
      rw [ENNReal.ofReal_mul κ.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]
    _ ≤ _ := hE T hT₀ ω hω
  -- Hence `𝔼[τ_δ] ≤ N + ∑ T, P((E T)ᶜ) ≤ M + L / η + 1 + S ≤ c L`.
  calc expectedStoppingTime (task.glrt Z alg (β δ) rec hrec (hstop δ)) env
  _ ≤ N + ∑' T, P (E (T + N))ᶜ :=
    task.expectedStoppingTime_glrt_le_add_tsum Z alg (β δ) rec hrec (hstop δ) hseq h_stop
  _ ≤ N + ∑' T, P (E T)ᶜ := add_le_add_right
    (ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective N) fun T ↦ P (E T)ᶜ) _
  _ = ENNReal.ofReal (N + S) := by
    rw [ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg, ENNReal.ofReal_natCast,
      ENNReal.ofReal_toReal hE_sum]
  _ ≤ ENNReal.ofReal (c * L) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hceil : (⌈L / η⌉₊ : ℝ) ≤ L / η + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hN : (N : ℝ) ≤ M + (L / η + 1) := by
      rw [Nat.cast_max]
      have hM : (0 : ℝ) ≤ M := M.cast_nonneg
      exact max_le (by linarith [div_nonneg hL0 hη.le]) (by linarith)
    rw [div_le_iff₀ hηc] at hLδ
    have : L / η = η⁻¹ * L := by ring
    nlinarith
  _ = c * ENNReal.ofReal L := by rw [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/-- **Asymptotic sample complexity of the GLRT with thresholds `log (r T / δ)`**, for every
sampling rule and the thresholds of [GK16, Theorem 14], `r T = O(T ^ p)`. Suppose that, along an
algorithm-environment sequence of the sampling rule in `env`, the GLR statistic of the recommended
answer after `T` rounds is at least `κ T` on an event `E T`, for every `T ≥ T₀`, and that
`∑ T, P((E T)ᶜ) < ∞`. Then for thresholds `β δ T ≤ log (r T / δ)` with `r T = O(T ^ p)`,
`𝔼[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`, for every `c > 1 / κ`. -/
theorem eventually_expectedStoppingTime_glrt_le_of_isBigO (hseq : IsAlgEnvSeq O X Y alg env P)
    (hE_sum : ∑' T, P (E T)ᶜ ≠ ∞) (hκc : 1 < κ * c)
    (hE : ∀ T ≥ T₀, ∀ ω ∈ E T,
      κ * T ≤ task.glr Z T (history O X Y T ω) (rec T (history O X Y T ω)))
    {r : ℕ → ℝ} {p : ℝ} (hr : r =O[atTop] fun T ↦ (T : ℝ) ^ p)
    (hβ : ∀ᶠ δ in 𝓝[>] 0, ∀ T ≥ T₀, β δ T ≤ ENNReal.ofReal (log (r T / δ))) :
    ∀ᶠ δ in 𝓝[>] 0, expectedStoppingTime (task.glrt Z alg (β δ) rec hrec (hstop δ)) env ≤
      c * ENNReal.ofReal (log (1 / δ)) := by
  refine task.eventually_expectedStoppingTime_glrt_le Z alg rec hrec hstop hseq hE_sum hκc hE
    (f := fun T ↦ log (r T)) (fun ε hε ↦ ?_) ?_
  · -- `log (r T) ≤ log C + p log T = o(T)`.
    obtain ⟨C, hC, hrC⟩ := hr.exists_pos
    have hg : (fun T : ℕ ↦ log C + p * log T) =o[atTop] fun T : ℕ ↦ (T : ℝ) :=
      ((Asymptotics.isLittleO_const_id_atTop (log C)).add
        (isLittleO_log_id_atTop.const_mul_left p)).comp_tendsto tendsto_natCast_atTop_atTop
    filter_upwards [hrC.bound, hg.bound hε, eventually_gt_atTop 0] with T hrT hgT hT
    rcases eq_or_ne (r T) 0 with h | h
    · simp only [h, log_zero]
      positivity
    have hT' : (0 : ℝ) < T := Nat.cast_pos.2 hT
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (rpow_nonneg hT'.le p)] at hrT
    rw [Real.norm_of_nonneg hT'.le] at hgT
    calc log (r T)
    _ = log |r T| := (log_abs _).symm
    _ ≤ log (C * T ^ p) := log_le_log (abs_pos.2 h) hrT
    _ = log C + p * log T := by rw [log_mul hC.ne' (rpow_pos_of_pos hT' p).ne', log_rpow hT']
    _ ≤ ε * T := (le_abs_self _).trans hgT
  · -- `log (r T / δ) ≤ log (1 / δ) + log (r T)` for `δ ∈ (0, 1)`.
    filter_upwards [hβ, Ioo_mem_nhdsGT one_pos] with δ hβδ hδ T hT
    refine (hβδ T hT).trans (ENNReal.ofReal_le_ofReal ?_)
    rcases eq_or_ne (r T) 0 with h | h
    · simp only [h, zero_div, log_zero, add_zero]
      exact log_nonneg (one_le_one_div hδ.1 hδ.2.le)
    · rw [log_div h hδ.1.ne', one_div, log_inv]
      linarith

end LMLExplore.Identification.IdentTask
