/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Task.TransportationCost

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

## References

* [C59] H. Chernoff, *Sequential design of experiments*, Ann. Math. Statist. 30 (1959).
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Proposition 12.
* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, Theorem 10.
* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019, Theorem 1.
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
  have hS : MeasurableSet {p : (Σ n, Hist Unit α 𝓨 n) × ℐ | p.1 ∈ A.stopSet ∧
      p.2 ∉ task.correct θ} :=
    (measurable_fst A.measurableSet_stopSet).inter (measurable_snd hc.compl)
  have h_law : HasLaw (A.stoppedHist O X Y) (stoppedHistMeasure A.alg env A.stopSet) P :=
    (task.alg_glrt Z alg β rec hrec hstop ▸ hseq).hasLaw_stoppedValue_sigmaHistory
      A.measurableSet_stopSet
  rw [histOutputMeasure_def, output_glrt_eq_deterministic, Measure.compProd_deterministic,
    map_measureReal_apply hg hS, ← h_law.map_eq,
    map_measureReal_apply_of_aemeasurable h_law.aemeasurable (hg hS)]
  -- The stopped history is the history of the first `k` rounds, for `k` the stopping time.
  refine measureReal_mono fun ω ⟨hω_stop, hω_wrong⟩ ↦ ?_
  simp only [IdentAlg.stoppedHist_def, stoppedValue, sigmaHistory_apply, A,
    mem_stopSet_glrt] at hω_stop hω_wrong
  exact ⟨_, hω_stop.trans_le (task.glr_le_of_notMem_correct hθ hω_wrong)⟩

/-- **Error probability of the GLRT along a run**, for every sampling rule. Along every run of the
GLRT, the probability that it stops with an answer that is not correct for the model `θ` is at
most the probability of the deviation event `∃ n, β n < Z n hₙ θ` of `θ`. -/
theorem measureReal_stoppingTime_ne_top_and_notMem_le_of_isRun_glrt {env : Environment Unit α 𝓨}
    {out : Ω → ℐ} (hrun : (task.glrt Z alg β rec hrec hstop).IsRun env O X Y out P)
    (hθ : θ ∈ task.M) (hc : MeasurableSet (task.correct θ)) :
    P.real {ω | (task.glrt Z alg β rec hrec hstop).stoppingTime O X Y ω ≠ ⊤ ∧
        out ω ∉ task.correct θ} ≤
      P.real {ω | ∃ n, β n < Z n (history O X Y n ω) θ} := by
  have hS : MeasurableSet {p : (Σ n, Hist Unit α 𝓨 n) × ℐ |
      p.1 ∈ (task.glrt Z alg β rec hrec hstop).stopSet ∧ p.2 ∉ task.correct θ} :=
    (measurable_fst (task.glrt Z alg β rec hrec hstop).measurableSet_stopSet).inter
      (measurable_snd hc.compl)
  have h_eq := hrun.hasLaw_stoppedHist_output.measureReal_eq hS
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

end LMLExplore.Identification.IdentTask
