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

* `MedianElimination.measure_notMem_halve_le`: an arm `a` is removed by the halving of a set `S`
  with probability at most `3 η`, if each arm of a set of `#S - 1 - ⌊#S / 4⌋` other arms has a
  value at least that of `a` with probability at most `η` [KKS13, proof of Lemma 4.3].
* `MedianElimination.measureReal_output_ne_le_sum`: along every run of median elimination with any
  numbers of pulls `t` and `σ2`-sub-Gaussian arms with a unique best arm, the output is not the
  best arm with probability at most `∑ j, 3 exp(-t j (⌊n_j / 4⌋ + 2) / (4 σ2 H₂))`.
* `SequentialHalving.phaseEnd_pullSchedule_le`, `expectedStoppingTime_sequentialHalving_le`:
  sequential halving with budget `T` stops after at most `T` rounds.
* `SequentialHalving.measureReal_output_ne_le`: [KKS13, Theorem 4.1] for `σ2`-sub-Gaussian arms,
  `P(error) ≤ 3 ⌈log₂ K⌉ exp(-(T - K ⌈log₂ K⌉) / (16 σ2 ⌈log₂ K⌉ H₂))`, and
  `SequentialHalving.measureReal_output_ne_le_of_mem_Icc`, its form
  `P(error) ≤ 3 ⌈log₂ K⌉ exp(-(T - K ⌈log₂ K⌉) / (4 ⌈log₂ K⌉ H₂))` for rewards in `[0, 1]`.

## Implementation notes

[KKS13] compares the empirical means of an arm and of the best arm by Hoeffding's inequality for
their difference, which has range `2` for rewards in `[0, 1]`, and obtains the constant `8` in the
exponent `T / (8 H₂ log₂ K)`. Here the difference of two independent sums of `σ2`-sub-Gaussian
rewards is `2 σ2`-sub-Gaussian, which gives the constant `16 σ2` of [LS, Theorem 33.10] for
`σ2 = 1`, and the constant `4` for rewards in `[0, 1]`, which are `1 / 4`-sub-Gaussian. The
numbers of pulls are rounded down so that the budget is never exceeded, and the bounds hold for
every budget `T`; for `T ≥ 2 K ⌈log₂ K⌉` they imply the bound
`3 ⌈log₂ K⌉ exp(-T / (8 ⌈log₂ K⌉ H₂))` of [KKS13].

The probabilities are computed in the reward stream, through the transfer from the runs of median
elimination `MedianElimination.measure_survivors_runStats_mem_eq` and the independence of the
phases `MedianElimination.measure_streamStats_mem_survivors_le`.

## References

* [KKS13] Z. Karnin, T. Koren and O. Somekh, *Almost optimal exploration in multi-armed bandits*,
  ICML 2013, Section 4 (Algorithm 2, Lemmas 4.2–4.3, Theorem 4.1).
* [LS] T. Lattimore and C. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Theorem 33.10.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real
open scoped ENNReal NNReal

namespace LMLExplore.Identification.MedianElimination

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-! ### One phase -/

/-- **One phase of sequential halving** [KKS13, proof of Lemma 4.3]. Let `a ∈ S` and let `S'` be
a set of `#S - 1 - ⌊#S / 4⌋` arms of `S` other than `a`, each of whose values `Y b` is at least
`Y a` with probability at most `η`. Then `a` is removed by the halving of `S` by the values `Y` with
probability at most `3 η`. -/
lemma measure_notMem_halve_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Y : Ω → α → ℝ} (hY : ∀ a, Measurable fun ω ↦ Y ω a) {S S' : Finset α} {a : α} (ha : a ∈ S)
    (hS' : S' ⊆ S.erase a) (hcard : #S' + #S / 4 + 1 = #S) {η : ℝ≥0∞}
    (h : ∀ b ∈ S', P {ω | Y ω a ≤ Y ω b} ≤ η) :
    P {ω | a ∉ halve S (Y ω)} ≤ 3 * η := by
  set m := #S - #S / 2 - #S / 4 with hm
  have hm0 : m ≠ 0 := by have := card_pos.2 ⟨a, ha⟩; omega
  -- The number of arms of `S'` whose value is at least that of `a`.
  set N : Ω → ℝ≥0∞ := fun ω ↦ ∑ b ∈ S', {ω | Y ω a ≤ Y ω b}.indicator 1 ω with hN
  have h_meas (b : α) : MeasurableSet {ω | Y ω a ≤ Y ω b} := measurableSet_le (hY a) (hY b)
  have h_sub : {ω | a ∉ halve S (Y ω)} ⊆ {ω | (m : ℝ≥0∞) ≤ N ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    -- Every survivor has a value at least that of `a`, and at most `⌊#S / 4⌋` survivors are
    -- outside `S'`.
    have h_le (b : α) (hb : b ∈ halve S (Y ω)) : Y ω a ≤ Y ω b := le_of_notMem_halve ha hω hb
    have h_halve : #(halve S (Y ω)) ≤ #{b ∈ S' | Y ω a ≤ Y ω b} + #(S.erase a \ S') := by
      refine (card_le_card fun b hb ↦ ?_).trans (card_union_le _ _)
      by_cases hbS' : b ∈ S'
      · exact mem_union_left _ (mem_filter.2 ⟨hbS', h_le b hb⟩)
      · exact mem_union_right _ (mem_sdiff.2
          ⟨mem_erase.2 ⟨fun hba ↦ hω (hba ▸ hb), halve_subset _ _ hb⟩, hbS'⟩)
    rw [card_halve, card_sdiff_of_subset hS', card_erase_of_mem ha] at h_halve
    calc (m : ℝ≥0∞) ≤ #{b ∈ S' | Y ω a ≤ Y ω b} := by exact_mod_cast (by omega)
    _ = N ω := by
      simp only [hN, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
      rw [sum_boole]
  -- Markov's inequality for the number of arms of `S'` whose value is at least that of `a`.
  have h_int : ∫⁻ ω, N ω ∂P ≤ #S' * η := by
    rw [lintegral_finsetSum _ fun b _ ↦ (measurable_one.indicator (h_meas b))]
    simp_rw [lintegral_indicator_one (h_meas _)]
    calc ∑ b ∈ S', P {ω | Y ω a ≤ Y ω b} ≤ ∑ _b ∈ S', η := sum_le_sum h
    _ = #S' * η := by simp
  have h_markov := (mul_meas_ge_le_lintegral₀ (μ := P) (Finset.measurable_sum _ fun b _ ↦
    measurable_one.indicator (h_meas b)).aemeasurable (m : ℝ≥0∞)).trans h_int
  have hS3 : (#S' : ℝ≥0∞) * η ≤ m * (3 * η) := by
    rw [← mul_assoc]
    gcongr
    norm_cast
    omega
  exact (measure_mono h_sub).trans
    ((ENNReal.mul_le_mul_iff_right (by exact_mod_cast hm0) (by simp)).1 (h_markov.trans hS3))

/-! ### Comparison of two arms in the reward stream -/

section Stream

variable [MeasurableSpace α] [MeasurableSingletonClass α]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Comparison of two arms** [KKS13, Lemma 4.2]. For `σ2`-sub-Gaussian arms `a ≠ b` with
`μ b ≤ μ a`, the statistic of `a` in phase `j` of the reward stream is at most that of `b` with
probability at most `exp(-t j (μ a - μ b)² / (4 σ2))`. -/
lemma measure_streamStats_le_streamStats_le {ν : Kernel α ℝ} [IsMarkovKernel ν] {σ2 : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (t : ℕ → ℕ) (j : ℕ)
    {a b : α} (hab : a ≠ b) (h_le : (ν b)[id] ≤ (ν a)[id]) :
    Bandits.streamMeasure ν {z | streamStats t z j a ≤ streamStats t z j b} ≤
      ENNReal.ofReal (exp (-(t j * ((ν a)[id] - (ν b)[id]) ^ 2) / (4 * σ2))) := by
  set P := Bandits.streamMeasure ν
  set I := Ico (∑ i ∈ range j, t i) (∑ i ∈ range (j + 1), t i)
  have hI : #I = t j := by simp [I, sum_range_succ]
  -- The centered statistic of an arm, as a function of its row of the stream.
  set g : α → (ℕ → ℝ) → ℝ := fun c w ↦ ∑ k ∈ I, (w k - (ν c)[id])
  have hg (c : α) : Measurable (g c) := Finset.measurable_sum _ fun k _ ↦ by fun_prop
  have h_sub (c : α) : HasSubgaussianMGF (fun z ↦ g c fun k ↦ z k c) (t j * σ2) P := by
    have h := HasSubgaussianMGF.sum_of_iIndepFun (c := fun _ ↦ σ2) (s := I)
      ((Bandits.iIndepFun_eval_streamMeasure'' ν c).comp (fun _ x ↦ x - (ν c)[id]) (by fun_prop))
      (fun k _ ↦ (hν c).congr_identDistrib
        ((Bandits.identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _))
    simpa [hI, g] using h
  have h_indep : IndepFun (fun z ↦ g b fun k ↦ z k b) (fun z ↦ g a fun k ↦ z k a) P :=
    (Bandits.indepFun_eval_streamMeasure' ν hab.symm).comp (hg b) (hg a)
  have h_eq : {z : ℕ → α → ℝ | streamStats t z j a ≤ streamStats t z j b} =
      {z | t j * ((ν a)[id] - (ν b)[id]) ≤ (g b fun k ↦ z k b) - g a fun k ↦ z k a} := by
    ext z
    simp only [Set.mem_ofPred_eq, streamStats_def, g, sum_sub_distrib, sum_const, nsmul_eq_mul]
    rw [hI]
    constructor <;> intro h <;> linarith
  rw [h_eq, ← ofReal_measureReal]
  gcongr
  refine (((h_sub b).sub_of_indepFun (h_sub a) h_indep).measure_ge_le
    (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 h_le))).trans_eq ?_
  push_cast
  rcases eq_or_ne (t j : ℝ) 0 with ht | ht
  · simp [ht]
  rcases eq_or_ne (σ2 : ℝ) 0 with hσ | hσ
  · simp [hσ]
  congr 1
  field_simp
  ring

/-! ### Correctness on the reward stream -/

/-- **Sequential halving on the reward stream** [KKS13, Lemma 4.3, Theorem 4.1]. For
`σ2`-sub-Gaussian arms with a unique best arm `a'` and any numbers of pulls `t`, the arm that
survives the `⌈log₂ K⌉` phases of the reward stream is not `a'` with probability at most
`∑ j, 3 exp(-t j (⌊n_j / 4⌋ + 2) / (4 σ2 H₂))`, where `n_j` is the number of arms of phase `j`. -/
theorem measure_roundRobinOn_survivors_streamStats_ne_le {ν : Kernel α ℝ} [IsMarkovKernel ν]
    {σ2 : ℝ≥0} (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (t : ℕ → ℕ)
    {a' : α} (ha' : ∀ b ≠ a', (ν b)[id] < (ν a')[id]) :
    Bandits.streamMeasure ν
        {z | roundRobinOn (survivors (streamStats t z) (numPhases (Fintype.card α))) 0 ≠ a'} ≤
      ∑ j ∈ range (numPhases (Fintype.card α)), 3 * ENNReal.ofReal (exp
        (-(t j * (armsCount (Fintype.card α) j / 4 + 2 : ℕ)) / (4 * σ2 * complexityTwo ν))) := by
  set K := Fintype.card α
  set L := numPhases K
  set P := Bandits.streamMeasure ν
  -- Phase `j` fails from the set `S` if `a' ∈ S` is removed by the halving.
  set Bad : Finset α → Set (α → ℝ) := fun S ↦ {y | a' ∈ S ∧ a' ∉ halve S y}
  have hBad (S : Finset α) : MeasurableSet (Bad S) :=
    (MeasurableSet.const (a' ∈ S)).inter
      (measurable_halve S (MeasurableSet.of_discrete (s := {T : Finset α | a' ∉ T})))
  have h_ne : ∀ z, roundRobinOn (survivors (streamStats t z) L) 0 ≠ a' →
      ∃ j ∈ range L, streamStats t z j ∈ Bad (survivors (streamStats t z) j) := by
    intro z hz
    by_contra h
    simp only [mem_range, not_exists, not_and, Set.mem_ofPred_eq, Bad, not_not] at h
    -- If no phase fails, `a'` survives every phase, hence is the only survivor of the last one.
    have h_mem (j : ℕ) (hj : j ≤ L) : a' ∈ survivors (streamStats t z) j := by
      induction j with
      | zero => rw [survivors_zero]; exact mem_univ a'
      | succ j ih =>
        rw [survivors_succ]
        exact h j (by omega) (ih (by omega))
    exact hz (card_le_one.1 (card_survivors_numPhases _).le _
      (roundRobinOn_mem (survivors_nonempty _ _) 0) _ (h_mem L le_rfl))
  refine (measure_mono fun z hz ↦ ?_).trans
    ((measure_biUnion_finset_le (range L)
      fun j ↦ {z | streamStats t z j ∈ Bad (survivors (streamStats t z) j)}).trans
        (sum_le_sum fun j _ ↦ ?_))
  · obtain ⟨j, hj, hz⟩ := h_ne z hz
    exact Set.mem_iUnion₂.2 ⟨j, hj, hz⟩
  refine measure_streamStats_mem_survivors_le ν t j hBad fun S hS ↦ ?_
  by_cases ha'S : a' ∉ S
  · simp [Bad, ha'S]
  rw [not_not] at ha'S
  -- The set `S'` of the `n - 1 - ⌊n / 4⌋` arms of `S` other than `a'` with the largest gaps.
  obtain ⟨S', hS'_sub, hS'_card, hS'_top⟩ := Finset.exists_subset_card_eq_forall_le
    (Bandits.gap ν) (s := S.erase a') (j := #S - 1 - #S / 4)
    (by rw [card_erase_of_mem ha'S]; omega)
  have hS_pos : 0 < #S := card_pos.2 ⟨a', ha'S⟩
  have h_gap_eq (c : α) : Bandits.gap ν c = (ν a')[id] - (ν c)[id] := by
    rw [Bandits.gap_eq_bestArm_sub, Bandits.bestArm_eq_of_forall_lt ha']
  simp only [Bad, ha'S, true_and]
  refine measure_notMem_halve_le (fun a ↦ measurable_streamStats_apply t j a) ha'S hS'_sub
    (by omega) fun b hb ↦ ?_
  have hba' : b ≠ a' := (mem_erase.1 (hS'_sub hb)).1
  have hΔ : 0 < Bandits.gap ν b := Bandits.gap_pos_of_forall_lt ha' hba'
  -- The arms of `S` outside `S'`, and `b`, have gaps at most that of `b`.
  have h_gap : ((armsCount K j / 4 + 2 : ℕ) : ℝ) / complexityTwo ν ≤ Bandits.gap ν b ^ 2 := by
    have hC : ∀ c ∈ insert b (S \ S'), Bandits.gap ν c ≤ Bandits.gap ν b := by
      intro c hc
      rcases mem_insert.1 hc with rfl | hc
      · exact le_rfl
      rcases eq_or_ne c a' with hca | hca
      · rw [hca, h_gap_eq a', sub_self]
        exact hΔ.le
      · exact hS'_top b hb c (mem_sdiff.2 ⟨mem_erase.2 ⟨hca, (mem_sdiff.1 hc).1⟩,
          (mem_sdiff.1 hc).2⟩)
    have h_card : armsCount K j / 4 + 2 ≤ #(insert b (S \ S')) := by
      have hS'S : S' ⊆ S := hS'_sub.trans (erase_subset _ _)
      rw [card_insert_of_notMem fun h ↦ (mem_sdiff.1 h).2 hb, card_sdiff_of_subset hS'S, ← hS]
      omega
    refine le_trans ?_ (card_div_complexityTwo_le_gap_sq hΔ hC)
    gcongr
    exact complexityTwo_nonneg ν
  refine (measure_streamStats_le_streamStats_le hν t j hba'.symm (ha' b hba').le).trans
    (ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_))
  rw [← h_gap_eq, show -(t j * ((armsCount K j / 4 + 2 : ℕ) : ℝ)) / (4 * σ2 * complexityTwo ν) =
    -(t j * (((armsCount K j / 4 + 2 : ℕ) : ℝ) / complexityTwo ν)) / (4 * σ2) by ring]
  exact div_le_div_of_nonneg_right (neg_le_neg (mul_le_mul_of_nonneg_left h_gap
    (Nat.cast_nonneg _))) (by positivity)

end Stream

end LMLExplore.Identification.MedianElimination

namespace LMLExplore.Identification

open MedianElimination

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {out : Ω → α} {ν : Kernel α ℝ}
  [IsMarkovKernel ν]

/-- **Correctness of the halving of median elimination for best arm identification**, for any
numbers of pulls [KKS13, Lemma 4.3, Theorem 4.1]. Let the arms be `σ2`-sub-Gaussian with a unique
best arm `a'`. Along every run of median elimination in which each surviving arm is pulled `t j`
times during phase `j`, the output is not `a'` with probability at most
`∑ j, 3 exp(-t j (⌊n_j / 4⌋ + 2) / (4 σ2 H₂))`, the sum ranging over the `⌈log₂ K⌉` phases, where
`n_j` is the number of arms of phase `j`. -/
theorem MedianElimination.measureReal_output_ne_le_sum {t : ℕ → ℕ} {σ2 : ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {a' : α}
    (ha' : ∀ b ≠ a', (ν b)[id] < (ν a')[id])
    (h : (medianElimination t).IsRun (Environment.bandit ν) O A R out P) :
    P.real {ω | out ω ≠ a'} ≤ ∑ j ∈ range (numPhases (Fintype.card α)),
      3 * exp (-(t j * (armsCount (Fintype.card α) j / 4 + 2 : ℕ)) /
        (4 * σ2 * complexityTwo ν)) := by
  set L := numPhases (Fintype.card α)
  have h_alg : IsAlgEnvSeq O A R (samplingRule t) (Environment.bandit ν) P := by
    simpa using h.isAlgEnvSeq
  set B : Set (Finset α) := {S | roundRobinOn S 0 ≠ a'}
  calc P.real {ω | out ω ≠ a'}
  _ = P.real {ω | survivors (runStats t A R ω) L ∈ B} := by
    refine measureReal_congr ?_
    filter_upwards [output_ae_eq h] with ω hω
    simp [B, hω, L]
  _ = (Bandits.streamMeasure ν).real {z | survivors (streamStats t z) L ∈ B} := by
    rw [measureReal_def, measureReal_def, measure_survivors_runStats_mem_eq h_alg B]
  _ ≤ (∑ j ∈ range L, 3 * ENNReal.ofReal (exp (-(t j * (armsCount (Fintype.card α) j / 4 + 2 : ℕ))
      / (4 * σ2 * complexityTwo ν)))).toReal :=
    ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun _ _ ↦ ENNReal.mul_ne_top (by simp)
      ENNReal.ofReal_ne_top) (measure_roundRobinOn_survivors_streamStats_ne_le hν t ha')
  _ = ∑ j ∈ range L, 3 * exp (-(t j * (armsCount (Fintype.card α) j / 4 + 2 : ℕ)) /
      (4 * σ2 * complexityTwo ν)) := by
    rw [ENNReal.toReal_sum fun _ _ ↦ by finiteness]
    simp [ENNReal.toReal_ofReal (exp_pos _).le]

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

/-- With the numbers of pulls of sequential halving, the exponent of phase `j < ⌈log₂ K⌉` in the
error bound `MedianElimination.measureReal_output_ne_le_sum` is at least
`(T - K ⌈log₂ K⌉) / (16 σ2 ⌈log₂ K⌉ H₂)`: phase `j` pulls each of its `n_j` arms more than
`T / (n_j ⌈log₂ K⌉) - 1` times, and `4 (⌊n_j / 4⌋ + 2) ≥ n_j`. -/
lemma exp_neg_pullSchedule_le {K T j : ℕ} (hK : 0 < K) (hj : j < numPhases K) (σ2 H : ℝ)
    (hσH : 0 ≤ σ2 * H) :
    exp (-(pullSchedule K T j * (armsCount K j / 4 + 2 : ℕ)) / (4 * σ2 * H)) ≤
      exp (-((T : ℝ) - K * numPhases K) / (16 * σ2 * numPhases K * H)) := by
  set n := armsCount K j
  set L := numPhases K
  have hL : 0 < L := by omega
  have hn : 0 < n := armsCount_pos hK j
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
  exact div_le_div_of_nonneg_right (neg_le_neg h_real) (by linarith)

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
  have hσ : (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 = 1 / 4 := by
    ext
    norm_num
  have h_sub (a : α) : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) (1 / 4) (ν a) :=
    hσ ▸ hasSubgaussianMGF_of_mem_Icc aemeasurable_id (hν a)
  refine (measureReal_output_ne_le h_sub ha' h).trans_eq ?_
  norm_num

end LMLExplore.Identification
