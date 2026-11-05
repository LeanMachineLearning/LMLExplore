/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.SumRewards
public import LMLExplore.Bandits.PerturbedLeader
public import LMLExplore.SequentialLearning.FiniteActions
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian Thompson sampling

Gaussian Thompson sampling with variance proxy `σ²` and a flat prior [LS, Theorem 36.3] is the
follow-the-perturbed-leader policy of [LS, Algorithm 24] whose perturbation of an arm `a` that has
been pulled `T_a > 0` times with empirical mean `μ̂_a` has law `𝒩(μ̂_a, σ² / T_a)`, and whose
perturbation of an arm that has not been pulled yet is `⊤`. The perturbations take values in
`EReal`, as the indices of index policies do: the policy pulls every arm once before comparing
Gaussian samples, and "pull each arm once" is the behaviour of the policy itself rather than a
separate initialization phase.

It is the limit of Thompson sampling with independent Gaussian priors on the means when the prior
variances tend to infinity. It differs from LML's `Bandits.tsAlgorithm`, which samples from the
posterior of a prior over environments.

[LS] writes the variance `1 / t` of the update; the intended variance after `s` samples of the arm
is `1 / s`, here `σ² / s`.

## Main definitions

* `LMLExplore.Bandits.gaussianTSStackLaw σ2 s y`: the law of the perturbation of an arm that has
  been pulled `s` times with sum of rewards `y`: `δ_⊤` if `s = 0`, `𝒩(y / s, σ² / s)` otherwise.
* `LMLExplore.Bandits.gaussianTSLaw σ2 n h a`: the law of the perturbation of arm `a` after the
  history `h` of length `n`: `δ_⊤` if `a` has not been pulled, `𝒩(μ̂_a, σ² / T_a)` otherwise.
* `LMLExplore.Bandits.gaussianTS σ2`: Gaussian Thompson sampling, the follow-the-perturbed-leader
  algorithm `perturbedLeaderAlgorithm` with perturbation laws `gaussianTSLaw σ2`.

## Main statements

* `gaussianTSLaw_history`: along a sequence of rounds, the perturbation law in terms of LML's
  `pullCount` and `empMean`.
* `GaussianTS.pullCount_action_eq_zero`: along a run, while some arm has not been pulled, the arm
  played has not been pulled before.
* `GaussianTS.pullCount_card_eq_one`: Gaussian Thompson sampling pulls every arm exactly once
  during the first `Fintype.card α` rounds.
* `GaussianTS.lintegral_pullCount_le`: [LS, Theorem 36.2] for Gaussian Thompson sampling, the
  bound on the expected number of pulls of an arm in terms of the perturbation laws of the
  reward-stack model.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 36.2.
-/

public section

open MeasureTheory ProbabilityTheory Learning Bandits

open scoped NNReal ENNReal

namespace LMLExplore.Bandits

section Law

variable {α : Type*} [DecidableEq α] {σ2 : ℝ≥0} {n : ℕ} {h : Hist Unit α ℝ n} {a : α}
  {s : ℕ} {y : ℝ}

/-- The law of the perturbation of an arm in Gaussian Thompson sampling, as a function of its
number of pulls `s` and its sum of rewards `y`: the Dirac mass at `⊤` if `s = 0`, and otherwise the
Gaussian law `𝒩(y / s, σ² / s)` on `EReal`. This is the perturbation law of the reward-stack model,
in which the sum of rewards after `s` pulls is the sum of the first `s` rewards of the stack. -/
noncomputable def gaussianTSStackLaw (σ2 : ℝ≥0) (s : ℕ) (y : ℝ) : Measure EReal :=
  if s = 0 then Measure.dirac ⊤ else (gaussianReal (y / s) (σ2 / s)).map ((↑) : ℝ → EReal)

/-- The defining equation of `gaussianTSStackLaw`. -/
lemma gaussianTSStackLaw_def (σ2 : ℝ≥0) (s : ℕ) (y : ℝ) :
    gaussianTSStackLaw σ2 s y =
      if s = 0 then Measure.dirac ⊤ else (gaussianReal (y / s) (σ2 / s)).map ((↑) : ℝ → EReal) :=
  (rfl)

/-- The perturbation of an arm that has not been pulled is `⊤`. -/
@[simp]
lemma gaussianTSStackLaw_zero (σ2 : ℝ≥0) (y : ℝ) : gaussianTSStackLaw σ2 0 y = Measure.dirac ⊤ := by
  simp [gaussianTSStackLaw_def]

/-- The perturbation of an arm that has been pulled `s ≠ 0` times with sum of rewards `y` has the
Gaussian law `𝒩(y / s, σ² / s)`. -/
@[simp]
lemma gaussianTSStackLaw_of_ne_zero (hs : s ≠ 0) :
    gaussianTSStackLaw σ2 s y = (gaussianReal (y / s) (σ2 / s)).map ((↑) : ℝ → EReal) := by
  simp [gaussianTSStackLaw_def, hs]

instance : IsProbabilityMeasure (gaussianTSStackLaw σ2 s y) := by
  rw [gaussianTSStackLaw_def]
  split_ifs <;> infer_instance

@[fun_prop]
lemma measurable_gaussianTSStackLaw (σ2 : ℝ≥0) (s : ℕ) :
    Measurable fun y : ℝ ↦ gaussianTSStackLaw σ2 s y := by
  by_cases hs : s = 0
  · simp [hs]
  · simp only [gaussianTSStackLaw_of_ne_zero hs]
    exact (Measure.measurable_map _ (by fun_prop)).comp
      (measurable_gaussianReal.comp ((measurable_id.div_const _).prodMk measurable_const))

/-- The law of the perturbation of arm `a` in Gaussian Thompson sampling at Lean round `n`, for the
history `h` of the first `n` rounds: the Dirac mass at `⊤` if the arm `a` has not been pulled, and
otherwise the Gaussian law `𝒩(μ̂_a, σ² / T_a)` on `EReal`, where `T_a` is the number of pulls of
`a` and `μ̂_a` its empirical mean. -/
noncomputable def gaussianTSLaw (σ2 : ℝ≥0) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) :
    Measure EReal :=
  gaussianTSStackLaw σ2 (pullCount' n h a) (sumRewards' n h a)

/-- The defining equation of `gaussianTSLaw`: the law `gaussianTSStackLaw` at the number of pulls
and the sum of rewards of the arm. -/
lemma gaussianTSLaw_def (σ2 : ℝ≥0) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) :
    gaussianTSLaw σ2 n h a = gaussianTSStackLaw σ2 (pullCount' n h a) (sumRewards' n h a) :=
  (rfl)

/-- The perturbation of an arm that has not been pulled is `⊤`. -/
@[simp]
lemma gaussianTSLaw_of_pullCount'_eq_zero (h0 : pullCount' n h a = 0) :
    gaussianTSLaw σ2 n h a = Measure.dirac ⊤ := by
  simp [gaussianTSLaw_def, h0]

/-- The perturbation of an arm that has been pulled has the Gaussian law `𝒩(μ̂_a, σ² / T_a)`. -/
lemma gaussianTSLaw_of_pullCount'_ne_zero (h0 : pullCount' n h a ≠ 0) :
    gaussianTSLaw σ2 n h a =
      (gaussianReal (empMean' n h a) (σ2 / pullCount' n h a)).map ((↑) : ℝ → EReal) := by
  simp [gaussianTSLaw_def, h0, empMean']

instance : IsProbabilityMeasure (gaussianTSLaw σ2 n h a) := by
  rw [gaussianTSLaw_def]
  infer_instance

/-- The perturbation of an arm that has been pulled is almost surely finite. -/
lemma gaussianTSLaw_Ici_top_eq_zero (h0 : pullCount' n h a ≠ 0) :
    gaussianTSLaw σ2 n h a (Set.Ici ⊤) = 0 := by
  have h_empty : ((↑) : ℝ → EReal) ⁻¹' Set.Ici ⊤ = ∅ := by ext; simp
  rw [gaussianTSLaw_of_pullCount'_ne_zero h0,
    Measure.map_apply (by fun_prop) measurableSet_Ici, h_empty, measure_empty]

/-- The perturbation of an arm that has not been pulled is `⊤`, almost surely not below `⊤`. -/
lemma gaussianTSLaw_Iio_top_eq_zero (h0 : pullCount' n h a = 0) :
    gaussianTSLaw σ2 n h a (Set.Iio ⊤) = 0 := by
  simp [h0]

@[fun_prop]
lemma measurable_gaussianTSLaw [MeasurableSpace α] [MeasurableSingletonClass α] (σ2 : ℝ≥0)
    (n : ℕ) (a : α) : Measurable fun h : Hist Unit α ℝ n ↦ gaussianTSLaw σ2 n h a :=
  (measurable_from_prod_countable_right (f := fun q : ℕ × ℝ ↦ gaussianTSStackLaw σ2 q.1 q.2)
    (measurable_gaussianTSStackLaw σ2)).comp
    ((measurable_pullCount' n a).prodMk (measurable_sumRewards' n a))

/-- Along a sequence of rounds `(O, A, R)`, the perturbation law of an arm at round `n` is the
Dirac mass at `⊤` if the arm has not been pulled before `n`, and otherwise `𝒩(μ̂_a, σ² / T_a)` for
the number of pulls `T_a = pullCount A a n ω` and the empirical mean `μ̂_a = empMean A R a n ω`. -/
lemma gaussianTSLaw_history {Ω : Type*} (O : ℕ → Ω → Unit) (A : ℕ → Ω → α) (R : ℕ → Ω → ℝ)
    (σ2 : ℝ≥0) (n : ℕ) (ω : Ω) (a : α) :
    gaussianTSLaw σ2 n (history O A R n ω) a = if pullCount A a n ω = 0 then Measure.dirac ⊤ else
      (gaussianReal (empMean A R a n ω) (σ2 / pullCount A a n ω)).map ((↑) : ℝ → EReal) := by
  rw [gaussianTSLaw_def, gaussianTSStackLaw_def, ← pullCount_eq_pullCount',
    ← sumRewards_eq_sumRewards', empMean]

end Law

section Algorithm

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- Gaussian Thompson sampling with variance proxy `σ²` and a flat prior [LS, Theorem 36.3]: the
follow-the-perturbed-leader algorithm that samples, at round `n`, independent perturbations of laws
`gaussianTSLaw σ2 n h a` and plays an arm of maximal perturbation, ties being broken by LML's
`argmax`. -/
noncomputable def gaussianTS (σ2 : ℝ≥0) : Algorithm Unit α ℝ :=
  perturbedLeaderAlgorithm (fun n x a ↦ gaussianTSLaw σ2 n x.1 a)
    (fun n a ↦ (measurable_gaussianTSLaw σ2 n a).comp measurable_fst) fun _ _ _ ↦ inferInstance

/-- Gaussian Thompson sampling is the follow-the-perturbed-leader algorithm with perturbation laws
`gaussianTSLaw σ2`. -/
lemma gaussianTS_def (σ2 : ℝ≥0) :
    gaussianTS (α := α) σ2 =
      perturbedLeaderAlgorithm (fun n x a ↦ gaussianTSLaw σ2 n x.1 a)
        (fun n a ↦ (measurable_gaussianTSLaw σ2 n a).comp measurable_fst)
        fun _ _ _ ↦ inferInstance :=
  (rfl)

namespace GaussianTS

variable {σ2 : ℝ≥0} {Ω : Type*} {mΩ : MeasurableSpace Ω} {env : Environment Unit α ℝ}
  {P : Measure Ω} [IsFiniteMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- Along a run of Gaussian Thompson sampling, while some arm has not been pulled yet, the arm
played has not been pulled before. -/
lemma pullCount_action_eq_zero (h : IsAlgEnvSeq O A R (gaussianTS σ2) env P) :
    ∀ᵐ ω ∂P, ∀ n, (∃ b, pullCount A b n ω = 0) → pullCount A (A n ω) n ω = 0 := by
  -- arms that have not been pulled have perturbation `⊤` and the others almost surely have a
  -- finite perturbation
  rw [ae_all_iff]
  intro n
  rw [gaussianTS_def] at h
  have hpc (b : α) : Measurable fun x : Hist Unit α ℝ n × Unit ↦ pullCount' n x.1 b :=
    (measurable_pullCount' n b).comp measurable_fst
  -- the set of pasts at which `a` has been pulled while some arm has not
  let s (a : α) : Set (Hist Unit α ℝ n × Unit) :=
    {x | pullCount' n x.1 a = 0}ᶜ ∩ ⋃ b, {x | pullCount' n x.1 b = 0}
  have hs (a : α) : MeasurableSet (s a) :=
    ((hpc a) (measurableSet_singleton 0)).compl.inter
      (MeasurableSet.iUnion fun b ↦ (hpc b) (measurableSet_singleton 0))
  have hnull (a : α) :
      P ((fun ω ↦ (history O A R n ω, O n ω)) ⁻¹' s a ∩ A n ⁻¹' {a}) = 0 := by
    refine PerturbedLeader.measure_preimage_inter_action_eq_zero h n (hs a) a fun x hx ↦ ?_
    obtain ⟨hxa, hxb⟩ := hx
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hxb
    exact ⟨b, ⊤, gaussianTSLaw_Ici_top_eq_zero hxa,
      gaussianTSLaw_Iio_top_eq_zero hb⟩
  have hsub : {ω | ¬((∃ b, pullCount A b n ω = 0) → pullCount A (A n ω) n ω = 0)} ⊆
      ⋃ a, (fun ω ↦ (history O A R n ω, O n ω)) ⁻¹' s a ∩ A n ⁻¹' {a} := by
    intro ω hω
    simp only [Classical.not_imp, Set.mem_ofPred_eq] at hω
    obtain ⟨⟨b, hb⟩, hne⟩ := hω
    rw [pullCount_eq_pullCount' (O := O) (R' := R)] at hb hne
    exact Set.mem_iUnion.2 ⟨A n ω, ⟨hne, Set.mem_iUnion.2 ⟨b, hb⟩⟩, rfl⟩
  rw [ae_iff]
  exact measure_mono_null hsub (measure_iUnion_null hnull)

/-- Gaussian Thompson sampling pulls every arm exactly once during the first `Fintype.card α`
rounds. -/
lemma pullCount_card_eq_one (h : IsAlgEnvSeq O A R (gaussianTS σ2) env P) :
    ∀ᵐ ω ∂P, ∀ a, pullCount A a (Fintype.card α) ω = 1 := by
  filter_upwards [pullCount_action_eq_zero h] with ω hω a
  exact pullCount_card_eq_one_of_forall_pullCount_action_eq_zero
    (fun n hn ↦ hω n (exists_pullCount_eq_zero_of_lt_card hn)) a

omit [IsFiniteMeasure P] in
/-- **[LS, Theorem 36.2] for Gaussian Thompson sampling.** In a run of Gaussian Thompson sampling
against the stochastic bandit `Environment.bandit ν`, for arms `i ≠ j`, a level `c` and a horizon
`n`, `E[T_i(n)] ≤ 1 + E[∑_{s < n} (G_{j s}⁻¹ - 1)] + ∑_{s < n} P(G_{i s} > 1 / n)`, where in the
reward-stack model `streamMeasure ν`, `G_{a s}` is the probability that the perturbation of arm `a`
after `s` pulls exceeds `c`: the probability that a sample of `𝒩(μ̂_{a s}, σ² / s)` exceeds `c`,
for the mean `μ̂_{a s}` of the first `s` rewards of `a`, and `G_{a 0} = 1` if `c < ⊤`. -/
theorem lintegral_pullCount_le [IsProbabilityMeasure P] {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (h : IsAlgEnvSeq O A R (gaussianTS σ2) (Environment.bandit ν) P) {i j : α} (hij : i ≠ j)
    (c : EReal) (n : ℕ) :
    ∫⁻ ω, (pullCount A i n ω : ℝ≥0∞) ∂P ≤
      1 + ∑ s ∈ Finset.range n, ∫⁻ x,
          (gaussianTSStackLaw σ2 s (∑ k ∈ Finset.range s, x k j) (Set.Ioi c))⁻¹ - 1
            ∂(streamMeasure ν) +
        ∑ s ∈ Finset.range n, streamMeasure ν {x | (n : ℝ≥0∞)⁻¹ <
          gaussianTSStackLaw σ2 s (∑ k ∈ Finset.range s, x k i) (Set.Ioi c)} :=
  -- the perturbation law of an arm is a function of its number of pulls and its sum of rewards
  PerturbedLeader.lintegral_pullCount_le h (fun _ ↦ gaussianTSStackLaw σ2)
    (fun _ ↦ measurable_gaussianTSStackLaw σ2) (fun t x a ↦ gaussianTSLaw_def σ2 t x.1 a) hij c n

end GaussianTS

end Algorithm

end LMLExplore.Bandits
