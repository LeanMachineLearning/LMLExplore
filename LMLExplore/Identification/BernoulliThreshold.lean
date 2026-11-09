/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.SequentialLearning.BernoulliDeviation
public import LMLExplore.Identification.Correctness
public import LMLExplore.Identification.TrackAndStop
public import LMLExplore.Identification.Task.BestArm

/-!
# The informational threshold of the GLRT for Bernoulli arms

For best arm identification with Bernoulli arms, on the vectors of means in `(0, 1)`, the GLRT
with the plug-in statistic of the empirical means and thresholds at least
`log (2 n (K - 1) / δ)` stops with an arm that is not the best with probability at most `δ`,
whatever the sampling rule and the recommendation rule [GK16, Theorem 10]. These grow like
`log n + log (K / δ)`. For arms dominated by exponential families,
`Identification/ExpFamilyThreshold.lean` gives the pairwise threshold
`2 log (2 n (n + 1)) + x_{δ / (K - 1)}`, of order `4 log n + log (K / δ)`, and the all-arm
threshold `K log (2 n (n + 1)) + x`, of order `2 K log n + log (1 / δ)`.

The GLRT errs only if, at some round `n`, the GLR statistic of a wrong arm `i` exceeds the
threshold. That statistic is at most the evidence `N_i d(μ̂_i, μ_i) + N_a d(μ̂_a, μ_a)` of the pair
formed by `i` and the best arm `a` against the true means, since `μ_i < μ_a` and the other arms
can be moved as close as wanted to their empirical means at no cost. The pairwise deviation
inequality of the Krichevsky–Trofimov mixture
(`LMLExplore.measure_exists_log_two_mul_mul_lt_klBer_le`) bounds the probability of that event by
`δ / (K - 1)`, and a union bound over the `K - 1` wrong arms concludes.

## Main statements

* `LMLExplore.Identification.glr_plugInCost_baiTask_bernoulliBandit_le`: the GLR statistic of the
  arm `i` is at most the evidence of the pair `(i, j)` against every `(λ_i, λ_j)` with
  `λ_i ≤ λ_j`.
* `LMLExplore.Identification.measureReal_histOutputMeasure_glrt_baiTask_bernoulliBandit_le`: the
  informational threshold [GK16, Theorem 10]: the GLRT errs with probability at most `δ`.
* `LMLExplore.Identification.isDeltaPAC_glrt_baiTask_bernoulliBandit`: the GLRT is `δ`-PAC as soon
  as it stops almost surely.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2.
* This file is adapted from `Identification/KTThreshold.lean` of the formalization in
  RemyDegenne/Garivier2016Optimal (commit 53ac67e4, directory `ForLMLExplore/`).
-/

public section

open MeasureTheory ProbabilityTheory Learning Real Finset

open scoped ENNReal

namespace LMLExplore.Identification

variable {α : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α]

/-- After `n` rounds, `∑ c, N_c t ≤ ε` for `t = min 1 (ε / (n + 1))`. -/
private lemma sum_pullCount'_mul_ofReal_min_le (n : ℕ) (h : Hist Unit α ℝ n) (ε : NNReal) :
    ∑ c, (pullCount' n h c : ℝ≥0∞) * ENNReal.ofReal (min 1 (ε / (n + 1))) ≤ ε := by
  rw [← sum_mul, ← Nat.cast_sum, sum_pullCount', ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have hn : (0 : ℝ) < n + 1 := by positivity
  calc (n : ℝ) * min 1 (ε / (n + 1)) ≤ n * (ε / (n + 1)) := by gcongr; exact min_le_right _ _
    _ ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ hn]
      nlinarith [ε.coe_nonneg]

/-- **The GLR statistic of best arm identification with Bernoulli arms is at most a pairwise
evidence.** For Bernoulli arms on the vectors of means in `(0, 1)`, the GLR statistic of the
plug-in statistic of the empirical means for the arm `i`, after `n` rounds with history `h`, is at
most `N_i d(μ̂_i, λ_i) + N_j d(μ̂_j, λ_j)` for every arm `j ≠ i` and all `λ_i ≤ λ_j` in `(0, 1)`:
`i` is not the best arm of the models with these means on `i` and `j`, and the other arms can be
moved as close as wanted to their empirical means. -/
lemma glr_plugInCost_baiTask_bernoulliBandit_le {i j : α} (hij : i ≠ j) {qi qj : ℝ}
    (hqi : qi ∈ Set.Ioo 0 1) (hqj : qj ∈ Set.Ioo 0 1) (hq : qi ≤ qj) (n : ℕ)
    (h : Hist Unit α ℝ n) :
    ((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a)) id
        ).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).glr
        (((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
          id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).plugInCost empMean') n h i ≤
      (pullCount' n h i : ℝ≥0∞) * klBer (empMean' n h i) qi +
        (pullCount' n h j : ℝ≥0∞) * klBer (empMean' n h j) qj := by
  set S : Set (α → ℝ) := {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1} with hS_def
  set ν : (α → ℝ) → Kernel α ℝ :=
    fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a) with hν
  set w : α → ℝ := fun a ↦ (pullCount' n h a : ℝ) with hw
  set emp := empMean' n h with hemp
  -- the cost from the empirical means, in terms of the binary relative entropy
  have hcost : ∀ μ', (baiTask ν id).cost w emp μ' =
      ∑ c, (pullCount' n h c : ℝ≥0∞) * klBer (emp c) (μ' c) := fun μ' ↦ by
    rw [IdentTask.cost_bernoulliBandit (ν_baiTask ν id)]
    simp only [hw, ENNReal.ofReal_natCast]
  have hS : IsOpen S := by
    simp only [hS_def, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun a ↦ isOpen_Ioo.preimage (continuous_apply a)
  -- the cost is continuous on `S`, where the binary relative entropy is continuous in its second
  -- argument
  have hc : ContinuousOn ((baiTask ν id).cost w emp) S := by
    refine (baiTask ν id).continuousOn_cost (fun c ↦ ?_) w
    refine (continuousOn_klBer.comp (s := S)
      (continuousOn_const.prodMk (continuous_apply c).continuousOn)
      fun μ' hμ' ↦ ⟨Subtype.prop (Set.projIcc 0 1 zero_le_one (emp c)), hμ' c⟩).congr
      fun μ' hμ' ↦ ?_
    rw [ν_baiTask, hν, Bandits.bernoulliBandit_apply, Bandits.bernoulliBandit_apply,
      klDiv_bernoulliMeasure, Set.projIcc_of_mem _ (Set.Ioo_subset_Icc_self (hμ' c)),
      Function.comp_apply, Function.uncurry_apply_pair]
  rw [IdentTask.glr_plugInCost, altCost_baiTask_restrict_eq_iInf _ hS
    (hc.mono Set.inter_subset_right)]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  -- the alternative: `λ_i`, `λ_j`, and the other arms moved to `(1 - t) μ̂ + t / 2`
  set t : ℝ := min 1 (ε / (n + 1)) with ht_def
  have ht : t ∈ Set.Ioc 0 1 := ⟨lt_min one_pos (by positivity), min_le_left _ _⟩
  set p : α → ℝ := fun c ↦ (Set.projIcc 0 1 zero_le_one (emp c) : ℝ) with hp_def
  have hp : ∀ c, p c ∈ Set.Icc 0 1 := fun c ↦ Subtype.prop _
  set lam : α → ℝ :=
    Function.update (Function.update (fun c ↦ (1 - t) * p c + t / 2) i qi) j qj with hlam
  have hlam_i : lam i = qi := by simp [hlam, hij]
  have hlam_j : lam j = qj := by simp [hlam]
  have hlam_c : ∀ c, c ≠ i → c ≠ j → lam c = (1 - t) * p c + t / 2 := by
    intro c hci hcj
    simp [hlam, hci, hcj]
  have hlamS : lam ∈ S := by
    intro c
    by_cases hcj : c = j
    · rw [hcj, hlam_j]
      exact hqj
    by_cases hci : c = i
    · rw [hci, hlam_i]
      exact hqi
    rw [hlam_c c hci hcj]
    exact one_sub_mul_add_div_two_mem_Ioo (hp c) ht
  calc ⨅ (b) (_ : b ≠ i) (μ' ∈ S) (_ : μ' i ≤ μ' b), (baiTask ν id).cost w emp μ'
      ≤ (baiTask ν id).cost w emp lam :=
        iInf_le_of_le j (iInf_le_of_le hij.symm (iInf_le_of_le lam (iInf_le_of_le hlamS
          (iInf_le _ (by rw [hlam_i, hlam_j]; exact hq)))))
    _ = ∑ c, (pullCount' n h c : ℝ≥0∞) * klBer (emp c) (lam c) := hcost lam
    _ = (pullCount' n h i : ℝ≥0∞) * klBer (emp i) qi +
        ((pullCount' n h j : ℝ≥0∞) * klBer (emp j) qj +
          ∑ c ∈ (univ.erase i).erase j, (pullCount' n h c : ℝ≥0∞) * klBer (emp c) (lam c)) := by
        rw [← add_sum_erase _ _ (mem_univ i),
          ← add_sum_erase _ _ (mem_erase.2 ⟨hij.symm, mem_univ j⟩), hlam_i, hlam_j]
    _ ≤ (pullCount' n h i : ℝ≥0∞) * klBer (emp i) qi +
        ((pullCount' n h j : ℝ≥0∞) * klBer (emp j) qj +
          ∑ c, (pullCount' n h c : ℝ≥0∞) * ENNReal.ofReal t) := by
        gcongr
        refine (sum_le_sum fun c hc ↦ ?_).trans
          (sum_le_sum_of_subset ((erase_subset _ _).trans (erase_subset _ _)))
        obtain ⟨hcj, hc'⟩ := mem_erase.1 hc
        obtain ⟨hci, -⟩ := mem_erase.1 hc'
        gcongr
        rw [hlam_c c hci hcj, ← klBer_projIcc (emp c), Set.projIcc_of_mem zero_le_one
          (x := (1 - t) * p c + t / 2) (Set.Ioo_subset_Icc_self (one_sub_mul_add_div_two_mem_Ioo
            (hp c) ht))]
        exact klBer_one_sub_mul_add_div_two_le (hp c) ht
    _ ≤ (pullCount' n h i : ℝ≥0∞) * klBer (emp i) qi +
        (pullCount' n h j : ℝ≥0∞) * klBer (emp j) qj + ε := by
        rw [← add_assoc]
        gcongr
        exact sum_pullCount'_mul_ofReal_min_le n h ε

/-- **The informational threshold for Bernoulli arms** [GK16, Theorem 10]. For best arm
identification with Bernoulli arms on the vectors of means in `(0, 1)` and every `δ > 0`, whatever
the sampling rule `alg` and the recommendation rule `rec`, the GLRT with the plug-in statistic of
the empirical means and thresholds `β` at least `log (2 n (K - 1) / δ)` stops with an arm that is
not the best with probability at most `δ`, on every vector of means of the task. -/
theorem measureReal_histOutputMeasure_glrt_baiTask_bernoulliBandit_le
    {δ : ℝ} (hδ : 0 < δ) (alg : Algorithm Unit α ℝ) (β : (n : ℕ) → Hist Unit α ℝ n → ℝ≥0∞)
    (hβ : ∀ (n : ℕ) h, ENNReal.ofReal (log (2 * n * (Fintype.card α - 1) / δ)) ≤ β n h)
    (rec : (n : ℕ) → Hist Unit α ℝ n → α) (hrec : ∀ n, Measurable (rec n))
    (hstop : ∀ n, MeasurableSet {h : Hist Unit α ℝ n | β n h <
      ((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a)) id
        ).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).glr
        (((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
          id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).plugInCost empMean') n h (rec n h)})
    {μ : α → ℝ}
    (hμ : μ ∈ ((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
      id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).M) :
    (histOutputMeasure
        (((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a)) id
          ).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).glrt
          (((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
            id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).plugInCost empMean') alg β rec hrec
          hstop)
        (Environment.bandit
          (Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a)))).real
      {q | q.1 ∈ (((baiTask
            (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a)) id
          ).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).glrt
          (((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
            id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).plugInCost empMean') alg β rec hrec
          hstop).stopSet ∧
        q.2 ∉ ((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
          id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).correct μ} ≤ δ := by
  simp only [IdentTask.M_restrict, M_baiTask, id_eq, Set.mem_inter_iff, Set.mem_ofPred_eq] at hμ
  obtain ⟨⟨a, ha⟩, hμS⟩ := hμ
  set task : IdentTask α (α → ℝ) α ℝ :=
    (baiTask (fun μ : α → ℝ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
      id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1} with htask
  set p : α → unitInterval := fun a ↦ Set.projIcc 0 1 zero_le_one (μ a) with hp_def
  have hpμ : ∀ c, (p c : ℝ) = μ c := fun c ↦ by
    simp [hp_def, Set.projIcc_of_mem _ (Set.Ioo_subset_Icc_self (hμS c))]
  have hp : ∀ c, (p c : ℝ) ∈ Set.Ioo 0 1 := fun c ↦ (hpμ c) ▸ hμS c
  have hcorr : task.correct μ = {a} := by
    rw [htask, IdentTask.correct_restrict]
    exact (correct_baiTask_eq_singleton_iff _ id).2 ha
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit (Bandits.bernoulliBandit p))
  rw [IdentTask.glrt_def, hcorr]
  refine (measureReal_histOutputMeasure_ofStop_deterministic_le hseq
    (measurableSet_singleton a)).trans ?_
  set x : ℝ := (Fintype.card α - 1) / δ with hx_def
  set E : α → Set _ := fun i ↦ {ω | ∃ n : ℕ, ENNReal.ofReal (log (2 * n * x)) <
      (pullCount IT.action i n ω : ℝ≥0∞) * klBer (empMean IT.action IT.feedback i n ω) (p i) +
        (pullCount IT.action a n ω : ℝ≥0∞) * klBer (empMean IT.action IT.feedback a n ω) (p a)}
    with hE
  have hsub : {ω | ∃ n, β n (history IT.obs IT.action IT.feedback n ω) <
        task.glr (task.plugInCost empMean') n (history IT.obs IT.action IT.feedback n ω)
          (rec n (history IT.obs IT.action IT.feedback n ω)) ∧
        rec n (history IT.obs IT.action IT.feedback n ω) ∉ ({a} : Set α)} ⊆
      ⋃ i ∈ univ.erase a, E i := by
    rintro ω ⟨n, hn_stop, hn_wrong⟩
    set i := rec n (history IT.obs IT.action IT.feedback n ω)
    have hia : i ≠ a := hn_wrong
    refine Set.mem_biUnion (mem_erase.2 ⟨hia, mem_univ i⟩) ⟨n, ?_⟩
    have hglr := glr_plugInCost_baiTask_bernoulliBandit_le hia (hμS i) (hμS a) (ha i hia).le n
      (history IT.obs IT.action IT.feedback n ω)
    rw [← pullCount_eq_pullCount', ← pullCount_eq_pullCount', ← empMean_eq_empMean',
      ← empMean_eq_empMean'] at hglr
    rw [hpμ, hpμ]
    refine lt_of_le_of_lt ?_ (hn_stop.trans_le hglr)
    refine le_trans (le_of_eq ?_) (hβ n _)
    rw [hx_def, mul_div_assoc]
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  rcases (univ.erase a).eq_empty_or_nonempty with he | ⟨i₀, hi₀⟩
  · simp [he, hδ.le]
  -- at least two arms, so `x > 0`
  have hK : 1 < Fintype.card α := by
    rw [← card_univ, ← card_erase_add_one (mem_univ a)]
    have := card_pos.2 ⟨i₀, hi₀⟩
    omega
  have hK' : (1 : ℝ) < Fintype.card α := by exact_mod_cast hK
  have hx : 0 < x := div_pos (by linarith) hδ
  calc ∑ i ∈ univ.erase a, (trajMeasure alg _).real (E i)
      ≤ ∑ i ∈ univ.erase a, 1 / x := by
        refine sum_le_sum fun i hi ↦ ?_
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal (by positivity)
          (measure_exists_log_two_mul_mul_lt_klBer_le hseq (mem_erase.1 hi).1 (hp i) (hp a) hx)
    _ = δ := by
        rw [sum_const, card_erase_of_mem (mem_univ a), card_univ, nsmul_eq_mul,
          Nat.cast_sub hK.le, Nat.cast_one, hx_def]
        field_simp

/-- **The GLRT for Bernoulli arms is `δ`-PAC** [GK16, Theorem 10]. For best arm identification
with Bernoulli arms on the vectors of means in `(0, 1)` and every `δ > 0`, whatever the sampling
rule `alg` and the recommendation rule `rec`, the GLRT with the plug-in statistic of the empirical
means and thresholds `β` at least `log (2 n (K - 1) / δ)` is `δ`-PAC, provided it stops almost
surely on every vector of means of the task. -/
theorem isDeltaPAC_glrt_baiTask_bernoulliBandit
    {δ : ℝ} (hδ : 0 < δ) (alg : Algorithm Unit α ℝ) (β : (n : ℕ) → Hist Unit α ℝ n → ℝ≥0∞)
    (hβ : ∀ (n : ℕ) h, ENNReal.ofReal (log (2 * n * (Fintype.card α - 1) / δ)) ≤ β n h)
    (rec : (n : ℕ) → Hist Unit α ℝ n → α) (hrec : ∀ n, Measurable (rec n))
    (hstop : ∀ n, MeasurableSet {h : Hist Unit α ℝ n | β n h <
      ((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a)) id
        ).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).glr
        (((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
          id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).plugInCost empMean') n h (rec n h)})
    (h_stops : ∀ μ ∈ ((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦
        Set.projIcc 0 1 zero_le_one (μ a)) id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).M,
      StopsAS (((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
          id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).glrt
          (((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
            id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).plugInCost empMean') alg β rec hrec
          hstop)
        (Environment.bandit (Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a)))) :
    ((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a)) id
        ).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).IsDeltaPAC
      (((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a)) id
          ).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).glrt
        (((baiTask (fun μ ↦ Bandits.bernoulliBandit fun a ↦ Set.projIcc 0 1 zero_le_one (μ a))
          id).restrict {μ' | ∀ a, μ' a ∈ Set.Ioo 0 1}).plugInCost empMean') alg β rec hrec
        hstop) δ :=
  IdentTask.isDeltaPAC_of_measureReal_mem_stopSet_and_notMem_le
    (fun _ _ ↦ (Set.toFinite _).measurableSet)
    (fun _ hμ ↦ by
      simpa only [IdentTask.ν_restrict, ν_baiTask] using
        measureReal_histOutputMeasure_glrt_baiTask_bernoulliBandit_le hδ alg β hβ rec hrec hstop hμ)
    fun _ hμ ↦ by simpa only [IdentTask.ν_restrict, ν_baiTask] using h_stops _ hμ

end LMLExplore.Identification
