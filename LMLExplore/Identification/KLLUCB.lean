/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.Concentration
public import LMLExplore.Identification.LUCB

/-!
# The stopping rule of KL-LUCB

KL-LUCB [KK13] is the instance of the LUCB algorithm (`lucb`) of top-`m` identification with
tolerance `ε` whose confidence bounds are the confidence levels of the binary relative entropy
`d`, for rewards in `[0, 1]`. After `n` rounds, an arm `a` with `N_a` pulls and empirical mean
`μ̂_a` has, for an exploration rate `β`,
* the upper confidence bound `u_a = max {q ∈ [μ̂_a, 1] | N_a d(μ̂_a, q) ≤ β(N_a, n)}`, the upper
  confidence level `U(μ̂_a, β(N_a, n) / N_a)` (`klUpper`),
* the lower confidence bound `l_a = min {q ∈ [0, μ̂_a] | N_a d(μ̂_a, q) ≤ β(N_a, n)}`, the lower
  confidence level `L(μ̂_a, β(N_a, n) / N_a)` (`klLower`).

By Pinsker's inequality these intervals are contained in the Hoeffding intervals of LUCB with the
same exploration level [KK13, (6)], and the Chernoff bound in relative-entropy form shows that they
have the same coverage: after `u` pulls, `u_a < μ_a` and `μ_a < l_a` each have probability at most
`exp (-β)`. A union bound over the rounds `n` and the numbers of pulls `u ≤ n` then bounds the
probability that some arm violates one of its bounds at some round, whatever the sampling rule,
and LUCB is correct outside this event (`measureReal_histOutputMeasure_lucb_le_card_mul`). If
`∑_n ∑_{u = 1}^n exp (-β(u, n)) ≤ δ / K`, KL-LUCB stops with a wrong answer with probability at
most `δ`, for every sampling rule. This is the union-bound condition of [KTAS12, Theorem 1] for
the relative-entropy confidence bounds, and the union-bound proof of correctness mentioned in
[KK13, Appendix A]. [KK13, Theorem 1] obtains the smaller exploration rate
`log (k₁ K t^α / δ) + log log (k₁ K t^α / δ)` from the self-normalized deviation inequality of
Garivier and Cappé, which is not used here.

## Main definitions

In the namespace `LMLExplore.Identification`:

* `LUCB.klLowerBound β`, `LUCB.klUpperBound β`: the confidence bounds `L(μ̂_a, β(N_a, n) / N_a)`
  and `U(μ̂_a, β(N_a, n) / N_a)` of KL-LUCB with exploration rate `β`.
* `kllucb alg β ε m`: KL-LUCB with sampling rule `alg`, exploration rate `β`, tolerance `ε` and
  `m` arms to select.

## Main statements

* `measureReal_histOutputMeasure_kllucb_le`: for rewards in `[0, 1]` and every sampling rule, if
  `∑_n ∑_{u = 1}^n exp (-β(u, n)) ≤ δ / K`, KL-LUCB stops with an answer that is not a correct
  answer of top-`m` identification with tolerance `ε` with probability at most `δ`.
* `measureReal_stoppingTime_ne_top_and_notMem_le_of_isRun_kllucb`: the same bound along every
  run.
* `isDeltaPAC_kllucb`: KL-LUCB is `δ`-PAC on top-`m` identification with tolerance `ε`, on every
  set of models with rewards in `[0, 1]` on which it stops almost surely.

## Implementation notes

As for LUCB, the rounds are numbered from `0` and the exploration rate `β u n` is used after `n`
rounds, with `u` the number of pulls of the arm. An arm that has not been pulled has the bounds
`L(0, 0) = U(0, 0) = 0`, which play no role: the stopping rule of LUCB only stops once every arm
has been pulled.

## References

* [KK13] E. Kaufmann and S. Kalyanakrishnan, *Information complexity in bandit subset selection*,
  COLT 2013, Section 3 ((4), (5) and Algorithm 2), Theorem 1 and Appendix A (Lemmas 3 and 4).
* [KTAS12] S. Kalyanakrishnan, A. Tewari, P. Auer and P. Stone, *PAC subset selection in
  stochastic multi-armed bandits*, ICML 2012, Theorem 1.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real

open scoped ENNReal

namespace LMLExplore.Identification

variable {α : Type*}

/-! ### Confidence bounds from the binary relative entropy -/

namespace LUCB

section Bounds

variable [DecidableEq α]

/-- The lower confidence bound `L(μ̂_a, β(N_a, n) / N_a) = min {q ∈ [0, μ̂_a] | N_a d(μ̂_a, q) ≤
β(N_a, n)}` of KL-LUCB with exploration rate `β` [KK13, (5)], after `n` rounds with history `h`,
where `N_a` and `μ̂_a` are the number of pulls and the empirical mean of the arm `a`. -/
noncomputable def klLowerBound (β : ℕ → ℕ → ℝ) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) : ℝ :=
  klLower (empMean' n h a) (ENNReal.ofReal (β (pullCount' n h a) n / pullCount' n h a))

lemma klLowerBound_def (β : ℕ → ℕ → ℝ) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) :
    klLowerBound β n h a =
      klLower (empMean' n h a) (ENNReal.ofReal (β (pullCount' n h a) n / pullCount' n h a)) :=
  (rfl)

/-- The upper confidence bound `U(μ̂_a, β(N_a, n) / N_a) = max {q ∈ [μ̂_a, 1] | N_a d(μ̂_a, q) ≤
β(N_a, n)}` of KL-LUCB with exploration rate `β` [KK13, (4)], after `n` rounds with history `h`,
where `N_a` and `μ̂_a` are the number of pulls and the empirical mean of the arm `a`. -/
noncomputable def klUpperBound (β : ℕ → ℕ → ℝ) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) : ℝ :=
  klUpper (empMean' n h a) (ENNReal.ofReal (β (pullCount' n h a) n / pullCount' n h a))

lemma klUpperBound_def (β : ℕ → ℕ → ℝ) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) :
    klUpperBound β n h a =
      klUpper (empMean' n h a) (ENNReal.ofReal (β (pullCount' n h a) n / pullCount' n h a)) :=
  (rfl)

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The exploration level `β(N_a, n) / N_a` of an arm is a measurable function of the history. -/
private lemma measurable_ofReal_div_pullCount' (β : ℕ → ℕ → ℝ) (n : ℕ) (a : α) :
    Measurable fun h : Hist Unit α ℝ n ↦
      ENNReal.ofReal (β (pullCount' n h a) n / pullCount' n h a) :=
  ENNReal.measurable_ofReal.comp
    (measurable_of_countable (fun u : ℕ ↦ β u n / u) |>.comp (measurable_pullCount' n a))

lemma measurable_klLowerBound (β : ℕ → ℕ → ℝ) (n : ℕ) (a : α) :
    Measurable fun h : Hist Unit α ℝ n ↦ klLowerBound β n h a :=
  (measurable_empMean' n a).klLower (measurable_ofReal_div_pullCount' β n a)

lemma measurable_klUpperBound (β : ℕ → ℕ → ℝ) (n : ℕ) (a : α) :
    Measurable fun h : Hist Unit α ℝ n ↦ klUpperBound β n h a :=
  (measurable_empMean' n a).klUpper (measurable_ofReal_div_pullCount' β n a)

end Bounds

end LUCB

/-! ### KL-LUCB -/

variable [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

section Algorithm

variable (alg : Algorithm Unit α ℝ)

/-- **KL-LUCB with exploration rate `β`** [KK13, Section 3], with sampling rule `alg`, tolerance `ε`
and `m` arms to select: LUCB with the confidence bounds `L(μ̂_a, β(N_a, n) / N_a)` and
`U(μ̂_a, β(N_a, n) / N_a)` after `n` rounds, where `N_a` and `μ̂_a` are the number of pulls and the
empirical mean of the arm `a`, and `L` and `U` are the confidence levels of the binary relative
entropy. -/
noncomputable def kllucb (β : ℕ → ℕ → ℝ) (ε : ℝ) (m : ℕ) : IdentAlg Unit α ℝ (Finset α) :=
  lucb alg (LUCB.klLowerBound β) (LUCB.klUpperBound β) (LUCB.measurable_klLowerBound β)
    (LUCB.measurable_klUpperBound β) ε m

lemma kllucb_def (β : ℕ → ℕ → ℝ) (ε : ℝ) (m : ℕ) :
    kllucb alg β ε m = lucb alg (LUCB.klLowerBound β) (LUCB.klUpperBound β)
      (LUCB.measurable_klLowerBound β) (LUCB.measurable_klUpperBound β) ε m := (rfl)

end Algorithm

/-! ### Correctness of the stopping rule -/

variable {ν : (α → ℝ) → Kernel α ℝ} [∀ μ, IsMarkovKernel (ν μ)] {ν₀ : Kernel α ℝ}
  [IsMarkovKernel ν₀] {alg : Algorithm Unit α ℝ} {β : ℕ → ℕ → ℝ} {ε δ : ℝ} {m : ℕ}

/-- **Error probability of KL-LUCB for rewards in `[0, 1]`**, for every sampling rule
[KK13, Theorem 1 and Lemma 4, with a union bound over the numbers of pulls]. Let the rewards of the
arms of `ν₀` be in `[0, 1]`, with means `μ`, let `ε ≥ 0` and `m ≤ K`, and let the exploration rate
`β` satisfy `∑_n ∑_{u = 1}^n exp (-β(u, n)) ≤ δ / K`. Then the probability that KL-LUCB stops with
an answer that is not a correct answer of top-`m` identification with tolerance `ε` for `μ` is at
most `δ`. -/
theorem measureReal_histOutputMeasure_kllucb_le
    (hν : ∀ a, ∀ᵐ x ∂(ν₀ a), x ∈ Set.Icc (0 : ℝ) 1)
    (hsum : Summable fun n ↦ ∑ u ∈ Icc 1 n, exp (-β u n))
    (hδ : ∑' n, ∑ u ∈ Icc 1 n, exp (-β u n) ≤ δ / Fintype.card α)
    (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α) :
    (histOutputMeasure (kllucb alg β ε m) (Environment.bandit ν₀)).real
        {p | p.1 ∈ (kllucb alg β ε m).stopSet ∧
          p.2 ∉ (epsTopMTask ν m ε).correct fun a ↦ (ν₀ a)[id]} ≤ δ := by
  rw [kllucb_def]
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν₀)
  have hP : IsProbabilityMeasure (trajMeasure alg (Environment.bandit ν₀)) :=
    inferInstanceAs (IsProbabilityMeasure (trajMeasure alg (Environment.bandit ν₀)))
  refine (measureReal_histOutputMeasure_lucb_le_card_mul hseq hε hm
    (S := ∑' n, ∑ u ∈ Icc 1 n, exp (-β u n)) (fun a ↦ ?_) (fun a ↦ ?_)).trans ?_
  · refine le_trans (measureReal_mono fun ω hω ↦ ?_)
      (Bandits.measureReal_exists_klUpper_lt_le_tsum hseq a (hν a) hsum)
    obtain ⟨n, hn, h⟩ := hω
    rw [LUCB.klUpperBound_def, ← empMean_eq_empMean', ← pullCount_eq_pullCount'] at h
    exact ⟨n, hn, h⟩
  · refine le_trans (measureReal_mono fun ω hω ↦ ?_)
      (Bandits.measureReal_exists_lt_klLower_le_tsum hseq a (hν a) hsum)
    obtain ⟨n, hn, h⟩ := hω
    rw [LUCB.klLowerBound_def, ← empMean_eq_empMean', ← pullCount_eq_pullCount'] at h
    exact ⟨n, hn, h⟩
  · have hK : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
    rwa [← le_div_iff₀' hK]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}

/-- **Error probability of KL-LUCB along a run**, for rewards in `[0, 1]` and every sampling rule.
Under the assumptions of `measureReal_histOutputMeasure_kllucb_le`, along every run of KL-LUCB,
the probability that it stops with an answer that is not a correct answer of top-`m`
identification with tolerance `ε` for the means `μ` is at most `δ`. -/
theorem measureReal_stoppingTime_ne_top_and_notMem_le_of_isRun_kllucb {out : Ω → Finset α}
    (hrun : (kllucb alg β ε m).IsRun (Environment.bandit ν₀) O X Y out P)
    (hν : ∀ a, ∀ᵐ x ∂(ν₀ a), x ∈ Set.Icc (0 : ℝ) 1)
    (hsum : Summable fun n ↦ ∑ u ∈ Icc 1 n, exp (-β u n))
    (hδ : ∑' n, ∑ u ∈ Icc 1 n, exp (-β u n) ≤ δ / Fintype.card α)
    (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α) :
    P.real {ω | (kllucb alg β ε m).stoppingTime O X Y ω ≠ ⊤ ∧
        out ω ∉ (epsTopMTask ν m ε).correct fun a ↦ (ν₀ a)[id]} ≤ δ := by
  rw [hrun.measureReal_stoppingTime_ne_top_and_notMem_eq (Set.to_countable _).measurableSet]
  exact measureReal_histOutputMeasure_kllucb_le hν hsum hδ hε hm

/-- **KL-LUCB is `δ`-PAC** for top-`m` identification with tolerance `ε`, for every sampling rule
[KK13, Theorem 1, with a union bound over the numbers of pulls]. Let `S` be a set of models whose
arms have rewards in `[0, 1]` and means given by the model, let `ε ≥ 0` and `m ≤ K`, and let the
exploration rate `β` satisfy `∑_n ∑_{u = 1}^n exp (-β(u, n)) ≤ δ / K`. If KL-LUCB stops almost
surely on every model of `S`, then it is `δ`-PAC on the task restricted to `S`. For Bernoulli
arms, `S` is the set of mean vectors in `[0, 1]`. -/
theorem isDeltaPAC_kllucb {S : Set (α → ℝ)} (hmean : ∀ μ ∈ S, ∀ a, (ν μ a)[id] = μ a)
    (hν : ∀ μ ∈ S, ∀ a, ∀ᵐ x ∂(ν μ a), x ∈ Set.Icc (0 : ℝ) 1)
    (hsum : Summable fun n ↦ ∑ u ∈ Icc 1 n, exp (-β u n))
    (hδ : ∑' n, ∑ u ∈ Icc 1 n, exp (-β u n) ≤ δ / Fintype.card α)
    (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α)
    (h_stops : ∀ μ ∈ S, StopsAS (kllucb alg β ε m) (Environment.bandit (ν μ))) :
    ((epsTopMTask ν m ε).restrict S).IsDeltaPAC (kllucb alg β ε m) δ := by
  have hS (μ : α → ℝ) (hμ : μ ∈ ((epsTopMTask ν m ε).restrict S).M) : μ ∈ S := by
    rw [IdentTask.M_restrict] at hμ
    exact hμ.2
  refine IdentTask.isDeltaPAC_of_measureReal_mem_stopSet_and_notMem_le
    (fun μ _ ↦ (Set.to_countable _).measurableSet) (fun μ hμ ↦ ?_)
    fun μ hμ ↦ by simpa only [IdentTask.ν_restrict, ν_epsTopMTask] using h_stops μ (hS μ hμ)
  simp only [IdentTask.ν_restrict, IdentTask.correct_restrict, ν_epsTopMTask]
  have h := measureReal_histOutputMeasure_kllucb_le (alg := alg) (ν := ν) (hν μ (hS μ hμ)) hsum
    hδ hε hm
  rwa [funext (hmean μ (hS μ hμ))] at h

end LMLExplore.Identification
