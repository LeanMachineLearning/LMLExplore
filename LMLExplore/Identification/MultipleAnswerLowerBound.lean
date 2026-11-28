/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.LowerBound
public import LMLExplore.Identification.Task.Minimax
public import LMLExplore.SequentialLearning.HistoryDensity
public import LMLExplore.SequentialLearning.WeakLaw

/-!
# The lower bound of identification with several correct answers

Let `θ` be an admissible model of an identification task with finitely many correct answers. For
every family of `δ`-correct algorithms `A δ`,
`liminf_{δ → 0} E_θ[τ_δ] / log (1 / δ) ≥ T*(θ)`, where
`T*(θ)⁻¹ = max_{i ∈ i*(θ)} D(θ, ¬i)` [DK19, Theorem 1]. When `θ` has a single correct answer this
is the lower bound of Garivier and Kaufmann
(`IdentTask.IsDeltaCorrect.charTime_mul_ofReal_log_le_expectedStoppingTime` in
`Identification/LowerBound.lean`), which follows from the transportation lemma: the algorithm
answers `i` with probability at least `1 - δ` at `θ` and at most `δ` at every alternative to `i`.
With several correct answers the algorithm may split its probability among them, and a bound on
the expected stopping time from the divergence of the laws of the stopped history loses a factor
of the number of answers. Degenne and Koolen replace it by a bound in probability: the algorithm
cannot stop before `T = (1 - η) T*(θ) log (1 / δ)` with any answer `i`, except with a probability
tending to `0`.

The alternatives to a correct answer `i` are combined into a mixture. By the minimax theorem
(`IdentTask.exists_forall_sum_klDiv_lt_of_answerValue_lt`), for every `d > D(θ, ¬i)` there is a
finitely supported distribution `q` on the alternatives to `i` with
`E_{λ ∼ q}[KL(ν_a(θ), ν_a(λ))] < d` for every arm `a`. Whatever the arms it pulls, the weighted
log-likelihood ratio `Λ_n = ∑_{t < n} E_{λ ∼ q}[log (dν_{A_t}(θ) / dν_{A_t}(λ))(Y_t)]` then grows at
most like `d n`, up to deviations which are `o(n)` uniformly over the algorithms by the weak law of
large numbers along bandit runs
(`LMLExplore.eventually_measure_exists_le_mul_lt_sum_sub_integral_le`).
The change of measure towards the mixture
(`Learning.setLIntegral_stoppedHistMeasure_bandit_le`) bounds the probability that the algorithm
stops by `T` with the answer `i` by `e^γ δ + P_θ(∃ n ≤ T, Λ_n > γ)`: the first term is the error
of the algorithm on the alternatives, which do not have `i` as a correct answer. For
`γ = (d + ε) T` and `T ≈ c log (1 / δ)` with `c (d + ε) < 1`, both terms tend to `0`. Summing
over the correct answers, `A δ` stops by `T` with probability tending to `0`, and
`E_θ[τ_δ] ≥ T (1 - P_θ(τ_δ ≤ T))`.

Degenne and Koolen assume sub-Gaussian arms, under which the log-likelihood ratios of exponential
families concentrate by the Hoeffding–Azuma inequality. Here the arm laws are arbitrary: the weak
law only needs the integrability of the log-likelihood ratios, which follows from the finiteness of
the relative entropies to the alternatives in the support of `q`.

## Main statements

* `IdentTask.IsDeltaCorrect.histOutputMeasure_le_add`: for a `δ`-correct algorithm and a finitely
  supported distribution `q` on the alternatives to `i`, the probability of stopping by `T` with the
  answer `i` is at most `e^γ δ` plus the probability that the weighted log-likelihood ratio exceeds
  `γ` before `T` [DK19, Proposition 18, Lemma 19].
* `IdentTask.IsDeltaCorrect.histOutputMeasure_le_add_sum`: the probability of stopping by `T` is at
  most `δ` plus the sum of these probabilities over the correct answers.
* `IdentTask.eventually_mul_ofReal_log_le_expectedStoppingTime_of_finite`: **the lower bound with
  several correct answers** [DK19, Theorem 1]: for every `c < T*(θ)`, `c log (1 / δ) ≤ E_θ[τ_δ]`
  for all small enough `δ`.
* `IdentTask.tendsto_expectedStoppingTime_div_log_of_finite`: asymptotic optimality from a matching
  upper bound, for models with finitely many correct answers.

## References

* [DK19] R. Degenne and W. M. Koolen, *Pure exploration with multiple correct answers*,
  NeurIPS 2019, Theorem 1, and supplementary material, Appendix C, Proposition 18 and Lemma 19.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Finset Filter Topology Convexity

open scoped ENNReal NNReal

namespace LMLExplore.Identification

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] {mα : MeasurableSpace α} [MeasurableSingletonClass α]
  {m𝓨 : MeasurableSpace 𝓨} {mℐ : MeasurableSpace ℐ}

namespace IdentTask

variable [MeasurableSingletonClass ℐ] {task : IdentTask α Θ ℐ 𝓨} {A : IdentAlg Unit α 𝓨 ℐ}
  {θ : Θ} {i : ℐ} {δ : ℝ}

omit [Fintype α] [MeasurableSingletonClass α] in
/-- The probability that `A` stops after at most `T` rounds with the answer `i` is the integral,
under the law of the stopped history, of the probability of `i` under the output rule, on the
stopped histories of at most `T` rounds of the stopping rule. -/
private lemma histOutputMeasure_stop_le_eq (env : Environment Unit α 𝓨) (T : ℕ) :
    histOutputMeasure A env {p | p.1 ∈ A.stopSet ∧ p.1.1 ≤ T ∧ p.2 = i} =
      ∫⁻ x in A.stopSet, {x : Σ n : ℕ, Hist Unit α 𝓨 n | x.1 ≤ T}.indicator
        (fun x ↦ A.output x {i}) x ∂stoppedHistMeasure A.alg env A.stopSet := by
  have hL : MeasurableSet {x : Σ n : ℕ, Hist Unit α 𝓨 n | x.1 ≤ T} := measurableSet_sigma_fst_le T
  have h_prod : {p : (Σ n : ℕ, Hist Unit α 𝓨 n) × ℐ | p.1 ∈ A.stopSet ∧ p.1.1 ≤ T ∧ p.2 = i} =
      (A.stopSet ∩ {x | x.1 ≤ T}) ×ˢ {i} := by
    ext p
    simp [and_assoc]
  rw [h_prod, histOutputMeasure_def, Measure.compProd_apply_prod
    (A.measurableSet_stopSet.inter hL) (measurableSet_singleton i), lintegral_indicator hL,
    Measure.restrict_restrict hL, Set.inter_comm]

omit [Fintype α] [MeasurableSingletonClass α] [MeasurableSingletonClass ℐ] in
/-- Along the canonical run, the event that the stopped history has at most `T` rounds and a
weighted sum `Λ` of a function `g` of its rounds above `γ` is the event that for some `n ≤ T` the
algorithm stops after `n` rounds with `∑_{t < n} g(A_t, Y_t) > γ`. -/
private lemma stoppedHistMeasure_le_measure_exists (env : Environment Unit α 𝓨) {g : α → 𝓨 → ℝ}
    (hg : Measurable (Function.uncurry g)) (T : ℕ) (γ : ℝ) :
    stoppedHistMeasure A.alg env A.stopSet (A.stopSet ∩ {x | γ < ∑ t, g (x.2 t).action
      (x.2 t).feedback} ∩ {x | x.1 ≤ T}) ≤
      trajMeasure A.alg env
        {ω | ∃ n ≤ T, γ < ∑ t ∈ range n, g (IT.action t ω) (IT.feedback t ω)} := by
  have hseq := IT.isAlgEnvSeq_trajMeasure A.alg env
  have hΛ : Measurable fun x : Σ n : ℕ, Hist Unit α 𝓨 n ↦ ∑ t, g (x.2 t).action (x.2 t).feedback :=
    measurable_sigma_sum_round hg
  have hB : MeasurableSet (A.stopSet ∩ {x : Σ n : ℕ, Hist Unit α 𝓨 n |
      γ < ∑ t, g (x.2 t).action (x.2 t).feedback} ∩ {x | x.1 ≤ T}) :=
    (A.measurableSet_stopSet.inter (measurableSet_lt measurable_const hΛ)).inter
      (measurableSet_sigma_fst_le T)
  rw [← (hseq.hasLaw_stoppedValue_sigmaHistory A.measurableSet_stopSet).map_eq,
    ← IdentAlg.stoppingTime_def, ← IdentAlg.stoppedHist_def,
    Measure.map_apply (A.measurable_stoppedHist hseq.measurable_obs hseq.measurable_action
      hseq.measurable_feedback) hB]
  refine measure_mono fun ω ⟨⟨hS, hγ⟩, hT⟩ ↦ ?_
  -- the algorithm stops after `n = τ ω` rounds, and the stopped history is the `n`-round history
  have hne := IdentAlg.stoppedHist_mem_stopSet_iff.1 hS
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
  have hF : A.stoppedHist IT.obs IT.action IT.feedback ω =
      ⟨n, history IT.obs IT.action IT.feedback n ω⟩ :=
    IdentAlg.stoppedHist_eq_of_stoppingTime_eq hn.symm
  simp only [Set.mem_ofPred_eq] at hγ hT
  rw [hF] at hγ hT
  refine ⟨n, hT, ?_⟩
  rw [← Fin.sum_univ_eq_sum_range (fun t ↦ g (IT.action t ω) (IT.feedback t ω))]
  simpa [history_apply] using hγ

omit [Fintype α] in
/-- **The probability of stopping early with a correct answer** [DK19, Proposition 18,
Lemma 19]. Let `A` be `δ`-correct and let `q` be a finitely supported distribution on the
alternatives to the answer `i`, with `ν_a(θ) ≪ ν_a(λ)` for every `λ` in its support. For every
horizon `T` and every `γ`, the probability that `A` stops at `θ` after at most `T` rounds with the
answer `i` is at most `e^γ δ` plus the probability that the weighted log-likelihood ratio
`∑_{t < n} E_{λ ∼ q}[log (dν_{A_t}(θ) / dν_{A_t}(λ))(Y_t)]` exceeds `γ` for some `n ≤ T`. -/
theorem IsDeltaCorrect.histOutputMeasure_le_add [Countable α] (hA : task.IsDeltaCorrect A δ)
    {q : StdSimplex ℝ Θ} (hq : ↑q.weights.support ⊆ task.alt i)
    (hac : ∀ θ' ∈ q.weights.support, ∀ a, task.ν θ a ≪ task.ν θ' a) (T : ℕ) (γ : ℝ) :
    histOutputMeasure A (Environment.bandit (task.ν θ))
        {p | p.1 ∈ A.stopSet ∧ p.1.1 ≤ T ∧ p.2 = i} ≤
      ENNReal.ofReal (Real.exp γ) * ENNReal.ofReal δ +
        trajMeasure A.alg (Environment.bandit (task.ν θ)) {ω | ∃ n ≤ T, γ < ∑ t ∈ range n,
          ∑ θ' ∈ q.weights.support, q.weights θ' *
            llr (task.ν θ (IT.action t ω)) (task.ν θ' (IT.action t ω)) (IT.feedback t ω)} := by
  set L := {x : Σ n : ℕ, Hist Unit α 𝓨 n | x.1 ≤ T} with hL_def
  have hL : MeasurableSet L := measurableSet_sigma_fst_le T
  set φ := L.indicator fun x ↦ A.output x {i} with hφ_def
  have hφ : Measurable φ :=
    (A.output.measurable_coe (measurableSet_singleton i)).indicator hL
  -- the weighted log-likelihood ratio of one observation
  set g : α → 𝓨 → ℝ := fun a y ↦ ∑ θ' ∈ q.weights.support, q.weights θ' *
    llr (task.ν θ a) (task.ν θ' a) y with hg
  have hgm : Measurable (Function.uncurry g) :=
    measurable_sum_mul_llr (task.ν θ) task.ν q.weights.support q.weights
  have hw1 : ∑ θ' ∈ q.weights.support, q.weights θ' = 1 := q.total
  rw [histOutputMeasure_stop_le_eq]
  refine (Learning.setLIntegral_stoppedHistMeasure_bandit_le (fun θ' _ ↦ q.nonneg θ') hw1
    (fun θ' ↦ task.ν θ') hac A.measurableSet_stopSet hφ γ).trans (add_le_add ?_ ?_)
  · -- at the alternatives, the algorithm stops with the answer `i` with probability at most `δ`
    gcongr
    calc ∑ θ' ∈ q.weights.support, ENNReal.ofReal (q.weights θ') *
          ∫⁻ x in A.stopSet, φ x ∂stoppedHistMeasure A.alg (Environment.bandit (task.ν θ'))
            A.stopSet
    _ ≤ ∑ θ' ∈ q.weights.support, ENNReal.ofReal (q.weights θ') * ENNReal.ofReal δ := by
        refine Finset.sum_le_sum fun θ' hθ' ↦ ?_
        gcongr
        have h_alt := hq hθ'
        rw [hφ_def, ← histOutputMeasure_stop_le_eq]
        have h_le := hA.measureReal_histOutputMeasure_le h_alt
        refine (measure_mono (s := {p : (Σ n : ℕ, Hist Unit α 𝓨 n) × ℐ |
          p.1 ∈ A.stopSet ∧ p.1.1 ≤ T ∧ p.2 = i}) (t := {p | p.1 ∈ A.stopSet ∧ p.2 = i})
          fun p hp ↦ ⟨hp.1, hp.2.2⟩).trans ?_
        exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
          (measureReal_nonneg.trans h_le)).2 h_le
    _ = ENNReal.ofReal δ := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun θ' _ ↦ q.nonneg θ', hw1,
          ENNReal.ofReal_one, one_mul]
  · -- the remaining event is the deviation of the log-likelihood ratio before `T`
    calc ∫⁻ x in A.stopSet ∩ {x | γ < ∑ t, ∑ θ' ∈ q.weights.support, q.weights θ' *
          llr (task.ν θ (x.2 t).action) (task.ν θ' (x.2 t).action) (x.2 t).feedback}, φ x
          ∂stoppedHistMeasure A.alg (Environment.bandit (task.ν θ)) A.stopSet
    _ ≤ ∫⁻ x in A.stopSet ∩ {x | γ < ∑ t, g (x.2 t).action (x.2 t).feedback}, L.indicator 1 x
          ∂stoppedHistMeasure A.alg (Environment.bandit (task.ν θ)) A.stopSet :=
        lintegral_mono fun x ↦ Set.indicator_le_indicator prob_le_one
    _ = stoppedHistMeasure A.alg (Environment.bandit (task.ν θ)) A.stopSet
          (A.stopSet ∩ {x | γ < ∑ t, g (x.2 t).action (x.2 t).feedback} ∩ L) := by
        rw [lintegral_indicator_one hL, Measure.restrict_apply hL, Set.inter_comm L]
    _ ≤ _ := stoppedHistMeasure_le_measure_exists _ hgm T γ

omit [Fintype α] [MeasurableSingletonClass α] [MeasurableSingletonClass ℐ] in
/-- **The probability of stopping early.** Let `A` be `δ`-correct and let the admissible model `θ`
have finitely many correct answers. The probability that `A` stops at `θ` after at most `T` rounds
is at most `δ` plus the sum over the correct answers `i` of the probability that it stops after at
most `T` rounds with the answer `i`. -/
theorem IsDeltaCorrect.histOutputMeasure_le_add_sum (hA : task.IsDeltaCorrect A δ)
    (hθ : θ ∈ task.M) (hfin : (task.correct θ).Finite) (T : ℕ) :
    histOutputMeasure A (Environment.bandit (task.ν θ)) {p | p.1 ∈ A.stopSet ∧ p.1.1 ≤ T} ≤
      ENNReal.ofReal δ + ∑ i ∈ hfin.toFinset, histOutputMeasure A
        (Environment.bandit (task.ν θ)) {p | p.1 ∈ A.stopSet ∧ p.1.1 ≤ T ∧ p.2 = i} := by
  have h_bad := isDeltaCorrect_iff.1 hA θ hθ
  have h_sub : {p : (Σ n : ℕ, Hist Unit α 𝓨 n) × ℐ | p.1 ∈ A.stopSet ∧ p.1.1 ≤ T} ⊆
      {p | p.1 ∉ A.stopSet ∨ p.2 ∉ task.correct θ} ∪
        ⋃ i ∈ hfin.toFinset, {p | p.1 ∈ A.stopSet ∧ p.1.1 ≤ T ∧ p.2 = i} := by
    rintro p ⟨hS, hT⟩
    by_cases hc : p.2 ∈ task.correct θ
    · exact Or.inr (Set.mem_biUnion (hfin.mem_toFinset.2 hc) ⟨hS, hT, rfl⟩)
    · exact Or.inl (Or.inr hc)
  refine (measure_mono h_sub).trans ((measure_union_le _ _).trans (add_le_add ?_
    (measure_biUnion_finset_le _ _)))
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
    (measureReal_nonneg.trans h_bad)).2 h_bad

omit [Fintype α] [MeasurableSingletonClass α] [MeasurableSingletonClass ℐ] in
/-- If a finitely supported distribution `q` of models has `E_{λ ∼ q}[KL(ν_a(θ), ν_a(λ))] < d` on
the arm `a`, every model of its support is at finite divergence from `θ` on the arm `a`. -/
private lemma klDiv_ne_top_of_sum_lt {q : StdSimplex ℝ Θ} {a : α} {d : ℝ≥0}
    (hqd : ∑ θ' ∈ q.weights.support, ENNReal.ofReal (q.weights θ') *
      klDiv (task.ν θ a) (task.ν θ' a) < d) {θ' : Θ} (hθ' : θ' ∈ q.weights.support) :
    klDiv (task.ν θ a) (task.ν θ' a) ≠ ∞ := by
  have hpos : 0 < q.weights θ' := (q.nonneg θ').lt_of_ne' (Finsupp.mem_support_iff.1 hθ')
  have h_le := (Finset.single_le_sum (f := fun θ' ↦ ENNReal.ofReal (q.weights θ') *
    klDiv (task.ν θ a) (task.ν θ' a)) (fun _ _ ↦ bot_le) hθ').trans_lt hqd
  intro h_top
  rw [h_top, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne'] at h_le
  exact (not_top_lt h_le).elim

omit [Fintype α] [MeasurableSingletonClass α] [MeasurableSingletonClass ℐ] in
/-- If a finitely supported distribution `q` of models has `E_{λ ∼ q}[KL(ν_a(θ), ν_a(λ))] < d` on
the arm `a`, the mean under `ν_a(θ)` of the weighted log-likelihood ratio
`y ↦ E_{λ ∼ q}[log (dν_a(θ) / dν_a(λ))(y)]` is at most `d`. -/
private lemma integral_sum_mul_llr_le_of_sum_lt {q : StdSimplex ℝ Θ} {a : α} {d : ℝ≥0}
    (hqd : ∑ θ' ∈ q.weights.support, ENNReal.ofReal (q.weights θ') *
      klDiv (task.ν θ a) (task.ν θ' a) < d) :
    ∫ y, ∑ θ' ∈ q.weights.support, q.weights θ' * llr (task.ν θ a) (task.ν θ' a) y
      ∂task.ν θ a ≤ d := by
  have hkl (θ' : Θ) (hθ' : θ' ∈ q.weights.support) := klDiv_ne_top_of_sum_lt hqd hθ'
  rw [integral_finsetSum _ fun θ' hθ' ↦ ((klDiv_ne_top_iff.1 (hkl θ' hθ')).2).const_mul _]
  -- the means of the log-likelihood ratios are the relative entropies
  have h_eq : ∑ θ' ∈ q.weights.support, ∫ y, q.weights θ' * llr (task.ν θ a) (task.ν θ' a) y
      ∂task.ν θ a = (∑ θ' ∈ q.weights.support, ENNReal.ofReal (q.weights θ') *
        klDiv (task.ν θ a) (task.ν θ' a)).toReal := by
    rw [ENNReal.toReal_sum fun θ' hθ' ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hkl θ' hθ')]
    refine Finset.sum_congr rfl fun θ' hθ' ↦ ?_
    rw [integral_const_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (q.nonneg θ'),
      toReal_klDiv_of_measure_eq (klDiv_ne_top_iff.1 (hkl θ' hθ')).1 (by simp)]
  rw [h_eq]
  exact ENNReal.toReal_le_coe_of_le_coe hqd.le

/-- At a correct answer `i` of `θ` and for `d > D(θ)`, the probability that the `δ`-correct
algorithm `A δ` stops after at most `⌈c log (1 / δ)⌉` rounds with the answer `i` tends to `0` as
`δ → 0`, whenever `c d < 1`. -/
private lemma eventually_histOutputMeasure_le_of_mem_correct [Nonempty α]
    {A : ℝ → IdentAlg Unit α 𝓨 ℐ} (hi : i ∈ task.correct θ) {d : ℝ≥0}
    (hd : task.gameValue θ < d) {c ε η : ℝ} (hc : 0 < c) (hε : 0 < ε) (hη : 0 < η)
    (hcd : c * (d + ε) < 1) :
    ∀ᶠ δ in 𝓝[>] 0, task.IsDeltaCorrect (A δ) δ →
      histOutputMeasure (A δ) (Environment.bandit (task.ν θ))
        {p | p.1 ∈ (A δ).stopSet ∧ p.1.1 ≤ ⌈c * Real.log (1 / δ)⌉₊ ∧ p.2 = i} ≤
          ENNReal.ofReal η := by
  -- a mixture `q` of alternatives to `i` at which every arm has divergence less than `d`
  rw [gameValue_def] at hd
  obtain ⟨q, hq, hqd⟩ := task.exists_forall_sum_klDiv_lt_of_answerValue_lt
    ((le_iSup₂ (f := fun i (_ : i ∈ task.correct θ) ↦ task.answerValue θ i) i hi).trans_lt hd)
  simp only [Finsupp.sum] at hqd
  have hac (θ' : Θ) (hθ' : θ' ∈ q.weights.support) (a : α) : task.ν θ a ≪ task.ν θ' a :=
    (klDiv_ne_top_iff.1 (klDiv_ne_top_of_sum_lt (hqd a) hθ')).1
  -- the weighted log-likelihood ratio of an observation, and its means
  set z : α → 𝓨 → ℝ := fun a y ↦ ∑ θ' ∈ q.weights.support, q.weights θ' *
    llr (task.ν θ a) (task.ν θ' a) y with hz
  have hzm : Measurable (Function.uncurry z) :=
    measurable_sum_mul_llr (task.ν θ) task.ν q.weights.support q.weights
  have hzint (a : α) : Integrable (z a) (task.ν θ a) :=
    integrable_finsetSum _ fun θ' hθ' ↦
      ((klDiv_ne_top_iff.1 (klDiv_ne_top_of_sum_lt (hqd a) hθ')).2).const_mul _
  have hzd (a : α) : ∫ y, z a y ∂task.ν θ a ≤ d := integral_sum_mul_llr_le_of_sum_lt (hqd a)
  -- the horizon `T δ = ⌈c log (1 / δ)⌉` tends to `∞`
  have hL : Tendsto (fun δ : ℝ ↦ Real.log (1 / δ)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Function.comp_def] using
      Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hT : Tendsto (fun δ : ℝ ↦ ⌈c * Real.log (1 / δ)⌉₊) (𝓝[>] 0) atTop :=
    tendsto_nat_ceil_atTop.comp (hL.const_mul_atTop hc)
  -- `e^{(d + ε) T δ} δ ≤ e^{d + ε} δ^{1 - c (d + ε)}` tends to `0`
  have h_exp : Tendsto (fun δ : ℝ ↦ Real.exp (d + ε) *
      Real.exp (-((1 - c * (d + ε)) * Real.log (1 / δ)))) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (hL.const_mul_atTop (by linarith)))).const_mul (Real.exp (d + ε))
  filter_upwards [hT.eventually (eventually_measure_exists_le_mul_lt_sum_sub_integral_le hzm hzint
    hε (half_pos hη)), h_exp.eventually (gt_mem_nhds (half_pos hη)),
    Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with δ hwl hδe hδ hAδ
  set T := ⌈c * Real.log (1 / δ)⌉₊ with hT_def
  have hLδ : 0 < Real.log (1 / δ) := Real.log_pos (one_lt_one_div hδ.1 hδ.2)
  have hTle : (T : ℝ) ≤ c * Real.log (1 / δ) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  refine (hAδ.histOutputMeasure_le_add hq hac T ((d + ε) * T)).trans ?_
  rw [show η = η / 2 + η / 2 by ring, ENNReal.ofReal_add (half_pos hη).le (half_pos hη).le]
  refine add_le_add ?_ ?_
  · -- the error at the alternatives, inflated by `e^γ`
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal (le_trans ?_ hδe.le)
    have hδ_eq : δ = Real.exp (-Real.log (1 / δ)) := by
      rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ.1]
    calc Real.exp ((d + ε) * T) * δ = Real.exp ((d + ε) * T - Real.log (1 / δ)) := by
          conv_lhs => rw [hδ_eq]
          rw [← Real.exp_add, sub_eq_add_neg]
    _ ≤ Real.exp ((d + ε) * (c * Real.log (1 / δ) + 1) - Real.log (1 / δ)) := by
          gcongr
    _ = _ := by
          rw [← Real.exp_add]
          congr 1
          ring
  · -- the deviation of the log-likelihood ratio, controlled by the weak law
    refine le_trans (measure_mono ?_)
      (hwl (IT.isAlgEnvSeq_trajMeasure (A δ).alg (Environment.bandit (task.ν θ))))
    rintro ω ⟨n, hnT, hn⟩
    refine ⟨n, hnT, ?_⟩
    have hm : ∑ t ∈ range n, ∫ y, z (IT.action t ω) y ∂task.ν θ (IT.action t ω) ≤ d * T :=
      calc _ ≤ ∑ t ∈ range n, (d : ℝ) := Finset.sum_le_sum fun t _ ↦ hzd _
      _ = d * n := by rw [sum_const, card_range, nsmul_eq_mul, mul_comm]
      _ ≤ d * T := by gcongr
    rw [Finset.sum_sub_distrib]
    simp only [hz] at hm ⊢
    linarith

omit [MeasurableSingletonClass α] [MeasurableSingletonClass ℐ] in
/-- For `0 < c < T*(θ)`, there are `d > D(θ)` and `ε > 0` with `c (d + ε) < 1`. -/
private lemma exists_gameValue_lt_and_mul_add_lt_one {c : ℝ≥0} (hc : c < task.charTime θ)
    (hc0 : (0 : ℝ) < c) :
    ∃ d : ℝ≥0, task.gameValue θ < d ∧ ∃ ε : ℝ, 0 < ε ∧ (c : ℝ) * (d + ε) < 1 := by
  have hgame : task.gameValue θ < (c : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.lt_inv_iff_lt_inv, ← charTime_def]
    exact hc
  obtain ⟨d, hd, hdc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hgame
  have hcd : (c : ℝ) * d < 1 := by
    rw [← ENNReal.coe_inv (by exact_mod_cast hc0.ne'), ENNReal.coe_lt_coe] at hdc
    have : (d : ℝ) < (c : ℝ)⁻¹ := by exact_mod_cast hdc
    calc (c : ℝ) * d < c * (c : ℝ)⁻¹ := mul_lt_mul_of_pos_left this hc0
    _ = 1 := mul_inv_cancel₀ hc0.ne'
  refine ⟨d, hd, (1 - c * d) / (2 * c), div_pos (by linarith) (by positivity), ?_⟩
  rw [mul_add, mul_div_assoc', mul_comm (2 : ℝ), ← div_div, mul_div_cancel_left₀ _ hc0.ne']
  linarith

/-- **The lower bound with several correct answers** [DK19, Theorem 1]. Let `A δ` be `δ`-correct
for all small enough `δ`, and let `θ` be an admissible model with finitely many correct answers.
Then for every `c < T*(θ)`, `c log (1 / δ) ≤ E_θ[τ_δ]` for all small enough `δ`:
`liminf_{δ → 0} E_θ[τ_δ] / log (1 / δ) ≥ T*(θ)`, where `T*(θ)⁻¹ = max_{i ∈ i*(θ)} D(θ, ¬i)`. The
arms may have any laws on any measurable space. -/
theorem eventually_mul_ofReal_log_le_expectedStoppingTime_of_finite [Nonempty α]
    {A : ℝ → IdentAlg Unit α 𝓨 ℐ} (hA : ∀ᶠ δ in 𝓝[>] 0, task.IsDeltaCorrect (A δ) δ)
    (hθ : θ ∈ task.M) (hfin : (task.correct θ).Finite) {c : ℝ≥0} (hc : c < task.charTime θ) :
    ∀ᶠ δ in 𝓝[>] 0, c * ENNReal.ofReal (Real.log (1 / δ)) ≤
      expectedStoppingTime (A δ) (Environment.bandit (task.ν θ)) := by
  -- choose `c < c' < T*(θ)`, then `D(θ) < d` with `c' d < 1`, and `ε > 0` with `c' (d + ε) < 1`
  obtain ⟨c', hcc', hc'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hc
  have hcc'_real : (c : ℝ) < c' := mod_cast ENNReal.coe_lt_coe.1 hcc'
  have hc'0 : (0 : ℝ) < c' := c.coe_nonneg.trans_lt hcc'_real
  obtain ⟨d, hd, ε, hε, hc'dε⟩ := exists_gameValue_lt_and_mul_add_lt_one hc' hc'0
  -- the target probability of stopping early: `1 - c / c'`
  set κ : ℝ := 1 - c / c' with hκ
  have hκ0 : 0 < κ := by
    rw [hκ, sub_pos, div_lt_one hc'0]
    exact hcc'_real
  set N := hfin.toFinset.card
  set η : ℝ := κ / (2 * (N + 1)) with hη
  have hη0 : 0 < η := by positivity
  have h_ans : ∀ i ∈ hfin.toFinset, ∀ᶠ δ in 𝓝[>] 0, task.IsDeltaCorrect (A δ) δ →
      histOutputMeasure (A δ) (Environment.bandit (task.ν θ))
        {p | p.1 ∈ (A δ).stopSet ∧ p.1.1 ≤ ⌈(c' : ℝ) * Real.log (1 / δ)⌉₊ ∧ p.2 = i} ≤
          ENNReal.ofReal η := fun i hi ↦
    eventually_histOutputMeasure_le_of_mem_correct (hfin.mem_toFinset.1 hi) hd hc'0 hε hη0 hc'dε
  filter_upwards [(Filter.eventually_all_finset _).2 h_ans, hA,
    Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 (κ / 2) by positivity)] with δ hδi hAδ hδ
  set T := ⌈(c' : ℝ) * Real.log (1 / δ)⌉₊ with hT_def
  have hLδ : 0 < Real.log (1 / δ) :=
    Real.log_pos (one_lt_one_div hδ.1 (hδ.2.trans_le (min_le_left _ _)))
  -- the algorithm stops by `T` with probability at most `δ + N η ≤ κ`
  have h_stop : histOutputMeasure (A δ) (Environment.bandit (task.ν θ))
      {p | p.1 ∈ (A δ).stopSet ∧ p.1.1 ≤ T} ≤ ENNReal.ofReal κ := by
    refine (hAδ.histOutputMeasure_le_add_sum hθ hfin T).trans ?_
    calc ENNReal.ofReal δ + ∑ i ∈ hfin.toFinset, histOutputMeasure (A δ)
          (Environment.bandit (task.ν θ)) {p | p.1 ∈ (A δ).stopSet ∧ p.1.1 ≤ T ∧ p.2 = i}
    _ ≤ ENNReal.ofReal δ + ∑ i ∈ hfin.toFinset, ENNReal.ofReal η := by
        gcongr with i hi
        exact hδi i hi hAδ
    _ = ENNReal.ofReal (δ + N * η) := by
        rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add hδ.1.le (by positivity)]
    _ ≤ ENNReal.ofReal κ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hNη : N * η ≤ κ / 2 := by
          rw [hη, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith [hδ.2.trans_le (min_le_right _ _)]
  -- hence `E_θ[τ_δ] ≥ (T + 1) (1 - κ) ≥ c' log (1 / δ) · c / c'`
  calc (c : ℝ≥0∞) * ENNReal.ofReal (Real.log (1 / δ))
  _ = ENNReal.ofReal ((c' : ℝ) * Real.log (1 / δ)) * ENNReal.ofReal (c / c') := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul c.coe_nonneg]
      congr 1
      field_simp
  _ ≤ ((T : ℝ≥0∞) + 1) * (1 - ENNReal.ofReal κ) := by
      gcongr
      · rw [← ENNReal.ofReal_natCast]
        exact (ENNReal.ofReal_le_ofReal (Nat.le_ceil _)).trans le_self_add
      · rw [hκ, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
  _ ≤ ((T : ℝ≥0∞) + 1) * (1 - histOutputMeasure (A δ) (Environment.bandit (task.ν θ))
        {p | p.1 ∈ (A δ).stopSet ∧ p.1.1 ≤ T}) := by
      gcongr
  _ ≤ _ := mul_one_sub_le_expectedStoppingTime _ _ T

/-- **Asymptotic optimality from a matching upper bound, with several correct answers.** Let
`A δ` be `δ`-correct for all small enough `δ` and let `θ` be an admissible model with finitely many
correct answers. If for every `c > T*(θ)`, `E_θ[τ_δ] ≤ c log (1 / δ)` for all small enough `δ`,
then `E_θ[τ_δ] / log (1 / δ) → T*(θ)` as `δ → 0`: by the lower bound
`eventually_mul_ofReal_log_le_expectedStoppingTime_of_finite`, the family `A` has the optimal sample
complexity. -/
theorem tendsto_expectedStoppingTime_div_log_of_finite [Nonempty α]
    {A : ℝ → IdentAlg Unit α 𝓨 ℐ} (hA : ∀ᶠ δ in 𝓝[>] 0, task.IsDeltaCorrect (A δ) δ)
    (hθ : θ ∈ task.M) (hfin : (task.correct θ).Finite)
    (h_upper : ∀ c : ℝ≥0, task.charTime θ < c → ∀ᶠ δ in 𝓝[>] 0,
      expectedStoppingTime (A δ) (Environment.bandit (task.ν θ)) ≤
        c * ENNReal.ofReal (Real.log (1 / δ))) :
    Tendsto (fun δ ↦ expectedStoppingTime (A δ) (Environment.bandit (task.ν θ)) /
      ENNReal.ofReal (Real.log (1 / δ))) (𝓝[>] 0) (𝓝 (task.charTime θ)) :=
  tendsto_expectedStoppingTime_div_log_of_forall_eventually
    (fun _ hc ↦ eventually_mul_ofReal_log_le_expectedStoppingTime_of_finite hA hθ hfin hc) h_upper

end IdentTask

end LMLExplore.Identification
