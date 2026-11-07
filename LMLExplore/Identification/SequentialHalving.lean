/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.MedianElimination

/-!
# Sequential halving

Sequential halving [KKS13] is the fixed-budget algorithm for best arm identification that splits
a budget of `T` rounds evenly between `⌈log₂ K⌉` phases, `K` being the number of arms. Phase `j`
pulls each of the `n_j = ⌈K / 2 ^ j⌉` arms that survive the first `j` phases
`⌊T / (n_j ⌈log₂ K⌉)⌋` times, then eliminates the half of them with the smallest empirical means,
computed from the samples of phase `j` only. The arm that survives the `⌈log₂ K⌉` phases is
recommended. These are the phases of median elimination, with other numbers of pulls: sequential
halving is `medianElimination` with the numbers of pulls `SequentialHalving.pullSchedule K T`, and
it takes at most `T` rounds.

Let `a'` be the unique best arm, and let a phase start from a set `S` of `n` arms containing `a'`.
If `a'` is eliminated, then each of the `n - ⌊n / 2⌋` survivors has an empirical mean at least that
of `a'`, and at least `n - ⌊n / 2⌋ - ⌊n / 4⌋` of them lie in the set `S'` of the
`n - 1 - ⌊n / 4⌋` arms of `S` with the smallest means. By Markov's inequality on the number of arms
of `S'` whose empirical mean is at least that of `a'`, this has probability at most three times
the largest probability that the empirical mean of an arm of `S'` is at least that of `a'`. The
arms of `S'` have at least `⌊n / 4⌋ + 2` arms with gaps at most theirs, so their squared gaps are
at least `(⌊n / 4⌋ + 2) / H₂`, with the complexity `H₂ = max_i i Δ_(i)⁻²` of
`LMLExplore.Identification.Complexity`. For `σ2`-sub-Gaussian arms, a union bound over the phases
gives `P(error) ≤ ∑ j, 3 exp(-t j (⌊n_j / 4⌋ + 2) / (4 σ2 H₂))` for any numbers of pulls `t`. With
the numbers of pulls of sequential halving, this is at most
`3 ⌈log₂ K⌉ exp(-(T - K ⌈log₂ K⌉) / (16 σ2 ⌈log₂ K⌉ H₂))`, where `K ⌈log₂ K⌉` accounts for the
rounding down of the numbers of pulls.

## Main definitions

In the namespace `LMLExplore.Identification`:

* `SequentialHalving.pullSchedule K T`: the numbers of pulls of sequential halving with `K` arms
  and budget `T`.
* `sequentialHalving T`: sequential halving with budget `T`, as a fixed-budget identification
  algorithm.

## Main statements

In the namespace `LMLExplore.Identification`:

* `SequentialHalving.phaseEnd_pullSchedule_le`, `expectedStoppingTime_sequentialHalving_le`:
  sequential halving with budget `T` stops after at most `T` rounds.
* `SequentialHalving.measureReal_output_ne_le`: [KKS13, Theorem 4.1] for `σ2`-sub-Gaussian arms,
  `P(error) ≤ 3 ⌈log₂ K⌉ exp(-(T - K ⌈log₂ K⌉) / (16 σ2 ⌈log₂ K⌉ H₂))`, and
  `SequentialHalving.measureReal_output_ne_le_of_mem_Icc`, its form
  `P(error) ≤ 3 ⌈log₂ K⌉ exp(-(T - K ⌈log₂ K⌉) / (4 ⌈log₂ K⌉ H₂))` for rewards in `[0, 1]`.
* `SequentialHalving.measureReal_outputMeasure_compl_correct_le`,
  `SequentialHalving.measureReal_outputMeasure_compl_correct_le_of_unitIntervalLaws`: the same
  bounds on the probability of error of best arm identification (`baiTask lawBandit lawMean`), on
  every bandit with `σ2`-sub-Gaussian arms, respectively with laws on `[0, 1]`.

## Implementation notes

[KKS13] compares the empirical means of an arm and of the best arm by Hoeffding's inequality for
their difference, which has range `2` for rewards in `[0, 1]`, and obtains the constant `8` in the
exponent `T / (8 H₂ log₂ K)`. Here the difference of two independent sums of `σ2`-sub-Gaussian
rewards is `2 σ2`-sub-Gaussian, which gives the constant `16 σ2` of [LS, Theorem 33.10] for
`σ2 = 1`, and the constant `4` for rewards in `[0, 1]`, which are `1 / 4`-sub-Gaussian. The
numbers of pulls are rounded down so that the budget is never exceeded, and the bounds hold for
every budget `T`; for `T ≥ 2 K ⌈log₂ K⌉` they imply the bound
`3 ⌈log₂ K⌉ exp(-T / (8 ⌈log₂ K⌉ H₂))` of [KKS13].

The analysis of one phase and the bound `∑ j, 3 exp(-t j (⌊n_j / 4⌋ + 2) / (4 σ2 H₂))` for any
numbers of pulls `t` hold for median elimination in general, and are proved in
`LMLExplore.Identification.MedianElimination` (`MedianElimination.measure_notMem_halve_le`,
`MedianElimination.measureReal_output_ne_le_sum`). This file specializes them to the numbers of
pulls of sequential halving.

## References

* [KKS13] Z. Karnin, T. Koren and O. Somekh, *Almost optimal exploration in multi-armed bandits*,
  ICML 2013, Section 4 (Algorithm 2, Lemmas 4.2–4.3, Theorem 4.1).
* [LS] T. Lattimore and C. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Theorem 33.10.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real
open scoped ENNReal NNReal

namespace LMLExplore.Identification

open MedianElimination

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {out : Ω → α} {ν : Kernel α ℝ}
  [IsMarkovKernel ν]

/-! ### The numbers of pulls of sequential halving -/

namespace SequentialHalving

/-- The numbers of pulls of sequential halving [KKS13] with `K` arms and budget `T`: in phase `j`,
each of the `armsCount K j = ⌈K / 2 ^ j⌉` surviving arms is pulled `⌊T / (⌈K / 2 ^ j⌉ ⌈log₂ K⌉)⌋`
times, so that each of the `⌈log₂ K⌉` phases takes at most `T / ⌈log₂ K⌉` rounds. -/
def pullSchedule (K T j : ℕ) : ℕ := T / (armsCount K j * numPhases K)

lemma pullSchedule_def (K T j : ℕ) : pullSchedule K T j = T / (armsCount K j * numPhases K) :=
  (rfl)

/-- Each phase of sequential halving takes at most `⌊T / ⌈log₂ K⌉⌋` rounds. -/
lemma armsCount_mul_pullSchedule_le (K T j : ℕ) :
    armsCount K j * pullSchedule K T j ≤ T / numPhases K := by
  rcases Nat.eq_zero_or_pos (numPhases K) with hL | hL
  · simp [pullSchedule_def, hL]
  rw [Nat.le_div_iff_mul_le hL]
  calc armsCount K j * pullSchedule K T j * numPhases K
  _ = T / (armsCount K j * numPhases K) * (armsCount K j * numPhases K) := by
    rw [pullSchedule_def]
    ring
  _ ≤ T := Nat.div_mul_le_self _ _

/-- **Budget of sequential halving** [KKS13]: with `K` arms and budget `T`, the `⌈log₂ K⌉` phases
of sequential halving take at most `T` rounds. -/
theorem phaseEnd_pullSchedule_le (K T : ℕ) : phaseEnd K (pullSchedule K T) (numPhases K) ≤ T := by
  rw [phaseEnd_eq_sum]
  calc ∑ j ∈ range (numPhases K), armsCount K j * pullSchedule K T j
  _ ≤ ∑ _j ∈ range (numPhases K), T / numPhases K :=
    sum_le_sum fun j _ ↦ armsCount_mul_pullSchedule_le K T j
  _ ≤ T := by
    rw [sum_const, card_range, smul_eq_mul]
    exact Nat.mul_div_le T _

/-- With the numbers of pulls `t_j` of sequential halving, the term of phase `j < ⌈log₂ K⌉` in the
error bound `MedianElimination.measureReal_output_ne_le_sum` satisfies
`exp(-t_j (⌊n_j / 4⌋ + 2) / (4 σ2 H)) ≤ exp(-(T - K ⌈log₂ K⌉) / (16 σ2 ⌈log₂ K⌉ H))`, where `n_j` is
the number of arms of phase `j`. -/
lemma exp_neg_pullSchedule_le {K T j : ℕ} (hK : 0 < K) (hj : j < numPhases K) (σ2 H : ℝ)
    (hσH : 0 ≤ σ2 * H) :
    exp (-(pullSchedule K T j * (armsCount K j / 4 + 2 : ℕ)) / (4 * σ2 * H)) ≤
      exp (-((T : ℝ) - K * numPhases K) / (16 * σ2 * numPhases K * H)) := by
  set n := armsCount K j
  set L := numPhases K
  have hL : 0 < L := by omega
  have hn : 0 < n := armsCount_pos hK j
  -- Phase `j` pulls each of its `n` arms more than `T / (n L) - 1` times, and
  -- `4 (⌊n / 4⌋ + 2) ≥ n`.
  -- `T < (t + 1) n L` for the number of pulls `t` of phase `j`.
  have h_lt := Nat.lt_div_mul_add (a := T) (Nat.mul_pos hn hL)
  rw [← pullSchedule_def] at h_lt
  have h_nat : T ≤ 4 * L * (pullSchedule K T j * (n / 4 + 2)) + K * L := by
    have := armsCount_le K j
    have h4 : n ≤ 4 * (n / 4 + 2) := by omega
    calc T ≤ pullSchedule K T j * (n * L) + n * L := h_lt.le
    _ ≤ pullSchedule K T j * (4 * (n / 4 + 2) * L) + K * L := by gcongr
    _ = 4 * L * (pullSchedule K T j * (n / 4 + 2)) + K * L := by ring
  have h_real : ((T : ℝ) - K * L) / (4 * L) ≤ pullSchedule K T j * (n / 4 + 2 : ℕ) := by
    rw [div_le_iff₀ (by positivity), sub_le_iff_le_add]
    calc (T : ℝ) ≤ (4 * L * (pullSchedule K T j * (n / 4 + 2)) + K * L : ℕ) := by
          exact_mod_cast h_nat
    _ = _ := by push_cast; ring
  refine exp_le_exp.2 ?_
  rw [show -((T : ℝ) - K * L) / (16 * σ2 * L * H) = -(((T : ℝ) - K * L) / (4 * L)) / (4 * σ2 * H)
    by field_simp; ring]
  gcongr
  linarith

end SequentialHalving

open SequentialHalving

/-- **Sequential halving** [KKS13] with budget `T`, as a fixed-budget identification algorithm.
With `K` arms, it proceeds in `⌈log₂ K⌉` phases: phase `j` pulls each of the `n_j = ⌈K / 2 ^ j⌉`
arms that survive the first `j` phases `⌊T / (n_j ⌈log₂ K⌉)⌋` times, in a round robin, then keeps
the half of them (rounded up) with the largest empirical means computed from the samples of
phase `j` only. The arm that survives the `⌈log₂ K⌉` phases is recommended. It is median
elimination with the numbers of pulls `pullSchedule K T`, and it takes at most `T` rounds. -/
noncomputable def sequentialHalving (T : ℕ) : IdentAlg Unit α ℝ α :=
  medianElimination (pullSchedule (Fintype.card α) T)

lemma sequentialHalving_def (T : ℕ) :
    sequentialHalving (α := α) T = medianElimination (pullSchedule (Fintype.card α) T) :=
  (rfl)

variable {T : ℕ}

@[simp]
lemma alg_sequentialHalving :
    (sequentialHalving (α := α) T).alg = samplingRule (pullSchedule (Fintype.card α) T) := by
  rw [sequentialHalving_def, alg_medianElimination]

lemma isFixedBudget_sequentialHalving :
    IsFixedBudget (sequentialHalving (α := α) T)
      (phaseEnd (Fintype.card α) (pullSchedule (Fintype.card α) T) (numPhases (Fintype.card α))) :=
  isFixedBudget_medianElimination

/-- **Sample complexity of sequential halving**: with budget `T`, sequential halving stops after
at most `T` rounds in expectation, in every environment: it is a fixed-budget algorithm with at most
this budget. -/
theorem expectedStoppingTime_sequentialHalving_le (env : Environment Unit α ℝ) :
    expectedStoppingTime (sequentialHalving (α := α) T) env ≤ T := by
  rw [isFixedBudget_sequentialHalving.expectedStoppingTime_eq]
  exact_mod_cast phaseEnd_pullSchedule_le _ T

/-- **Sequential halving** [KKS13, Theorem 4.1; LS, Theorem 33.10]. For `σ2`-sub-Gaussian arms with
a unique best arm `a'` and any budget `T`, sequential halving fails to recommend `a'` with
probability at most `3 ⌈log₂ K⌉ exp(-(T - K ⌈log₂ K⌉) / (16 σ2 ⌈log₂ K⌉ H₂))`, with the complexity
`H₂ = max_i i Δ_(i)⁻²`. -/
theorem SequentialHalving.measureReal_output_ne_le {σ2 : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {a' : α}
    (ha' : ∀ b ≠ a', (ν b)[id] < (ν a')[id])
    (h : (sequentialHalving T).IsRun (Environment.bandit ν) O A R out P) :
    P.real {ω | out ω ≠ a'} ≤ 3 * numPhases (Fintype.card α) *
      exp (-((T : ℝ) - Fintype.card α * numPhases (Fintype.card α)) /
        (16 * σ2 * numPhases (Fintype.card α) * complexityTwo ν)) := by
  rw [sequentialHalving_def] at h
  refine (MedianElimination.measureReal_output_ne_le_sum hν ha' h).trans ?_
  have hσH : 0 ≤ (σ2 : ℝ) * complexityTwo ν := mul_nonneg σ2.2 (complexityTwo_nonneg ν)
  calc ∑ j ∈ range (numPhases (Fintype.card α)), 3 * exp (-(pullSchedule (Fintype.card α) T j *
        (armsCount (Fintype.card α) j / 4 + 2 : ℕ)) / (4 * σ2 * complexityTwo ν))
  _ ≤ ∑ _j ∈ range (numPhases (Fintype.card α)), 3 * exp (-((T : ℝ) -
        Fintype.card α * numPhases (Fintype.card α)) /
        (16 * σ2 * numPhases (Fintype.card α) * complexityTwo ν)) :=
    sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_left
      (exp_neg_pullSchedule_le (T := T) Fintype.card_pos (mem_range.1 hj) _ _ hσH) (by norm_num)
  _ = _ := by
    rw [sum_const, card_range, nsmul_eq_mul]
    ring

/-- **Sequential halving for rewards in `[0, 1]`** [KKS13, Theorem 4.1]: with a unique best arm
`a'` and any budget `T`, sequential halving fails to recommend `a'` with probability at most
`3 ⌈log₂ K⌉ exp(-(T - K ⌈log₂ K⌉) / (4 ⌈log₂ K⌉ H₂))`. For `T ≥ 2 K ⌈log₂ K⌉`, this implies the
bound `3 ⌈log₂ K⌉ exp(-T / (8 ⌈log₂ K⌉ H₂))` of [KKS13]. -/
theorem SequentialHalving.measureReal_output_ne_le_of_mem_Icc
    (hν : ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc (0 : ℝ) 1) {a' : α}
    (ha' : ∀ b ≠ a', (ν b)[id] < (ν a')[id])
    (h : (sequentialHalving T).IsRun (Environment.bandit ν) O A R out P) :
    P.real {ω | out ω ≠ a'} ≤ 3 * numPhases (Fintype.card α) *
      exp (-((T : ℝ) - Fintype.card α * numPhases (Fintype.card α)) /
        (4 * numPhases (Fintype.card α) * complexityTwo ν)) := by
  have h_sub (a : α) : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) (1 / 4) (ν a) :=
    hasSubgaussianMGF_of_mem_Icc_zero_one aemeasurable_id (hν a)
  refine (measureReal_output_ne_le h_sub ha' h).trans_eq ?_
  norm_num

/-- **Sequential halving on the bandits with σ²-sub-Gaussian arms** [KKS13, Theorem 4.1;
LS, Theorem 33.10]. On every bandit `θ` whose arms are `σ2`-sub-Gaussian and which has a unique
best arm, the probability that sequential halving with budget `T` does not output the best arm is
at most `3 ⌈log₂ K⌉ exp(-(T - K ⌈log₂ K⌉) / (16 σ2 ⌈log₂ K⌉ H₂))`. -/
theorem SequentialHalving.measureReal_outputMeasure_compl_correct_le {σ2 : ℝ≥0}
    {θ : α → ProbabilityMeasure ℝ} (hθ : θ ∈ ((baiTask (lawBandit (α := α)) lawMean).restrict
      (Set.univ.pi fun _ ↦ subgaussianLaws σ2)).M) :
    ((sequentialHalving T).outputMeasure (Environment.bandit (lawBandit θ))).real
        ((baiTask lawBandit lawMean).correct θ)ᶜ ≤ 3 * numPhases (Fintype.card α) *
      exp (-((T : ℝ) - Fintype.card α * numPhases (Fintype.card α)) /
        (16 * σ2 * numPhases (Fintype.card α) * complexityTwo (lawBandit θ))) := by
  rw [IdentTask.M_restrict, M_baiTask] at hθ
  obtain ⟨⟨a, ha⟩, hθ⟩ := hθ
  have hν (b : α) : HasSubgaussianMGF (fun x ↦ x - (lawBandit θ b)[id]) σ2 (lawBandit θ b) := by
    simpa using hθ b (Set.mem_univ b)
  have hrun := isRun_runMeasure (sequentialHalving (α := α) T) (Environment.bandit (lawBandit θ))
  rw [(correct_baiTask_eq_singleton_iff _ _).2 ha, Set.compl_def,
    ← hrun.hasLaw_output.measureReal_eq MeasurableSet.of_discrete]
  simp only [lawMean_eq_integral_lawBandit] at ha
  simpa only [Set.mem_singleton_iff] using measureReal_output_ne_le hν ha hrun

/-- **Sequential halving on the bandits with laws on `[0, 1]`** [KKS13, Theorem 4.1]. On every
bandit `θ` whose arms have laws on `[0, 1]` and which has a unique best arm, the probability that
sequential halving with budget `T` does not output the best arm is at most
`3 ⌈log₂ K⌉ exp(-(T - K ⌈log₂ K⌉) / (4 ⌈log₂ K⌉ H₂))`. -/
theorem SequentialHalving.measureReal_outputMeasure_compl_correct_le_of_unitIntervalLaws
    {θ : α → ProbabilityMeasure ℝ} (hθ : θ ∈ ((baiTask (lawBandit (α := α)) lawMean).restrict
      (Set.univ.pi fun _ ↦ unitIntervalLaws)).M) :
    ((sequentialHalving T).outputMeasure (Environment.bandit (lawBandit θ))).real
        ((baiTask lawBandit lawMean).correct θ)ᶜ ≤ 3 * numPhases (Fintype.card α) *
      exp (-((T : ℝ) - Fintype.card α * numPhases (Fintype.card α)) /
        (4 * numPhases (Fintype.card α) * complexityTwo (lawBandit θ))) := by
  rw [IdentTask.M_restrict] at hθ
  refine (measureReal_outputMeasure_compl_correct_le (σ2 := 1 / 4) ?_).trans_eq (by norm_num)
  rw [IdentTask.M_restrict]
  exact ⟨hθ.1, Set.pi_mono (fun _ _ ↦ unitIntervalLaws_subset_subgaussianLaws) hθ.2⟩

end LMLExplore.Identification
