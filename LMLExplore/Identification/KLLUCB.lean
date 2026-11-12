/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.Concentration
public import LMLExplore.Identification.LUCB
import LMLExplore.Analysis.PSeries

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

By Pinsker's inequality these intervals are contained in the Hoeffding intervals
`[μ̂_a - √(β(N_a, n) / (2 N_a)), μ̂_a + √(β(N_a, n) / (2 N_a))]` [KK13, (6)]
(`LMLExplore.max_le_klLower`, `LMLExplore.klUpper_le_min`), and the Chernoff bound in
relative-entropy form shows that they have the same coverage: after `u` pulls, `u_a < μ_a` and
`μ_a < l_a` each have probability at most `exp (-β)`. A union bound over
the rounds `n` and the numbers of pulls `u ≤ n` then bounds the probability that some arm violates
one of its bounds at some round, whatever the sampling rule, and LUCB is correct outside this
event (`measureReal_histOutputMeasure_lucb_le_card_mul`). If
`∑_n ∑_{u = 1}^n exp (-β(u, n)) ≤ δ / K`, KL-LUCB stops with a wrong answer with probability at
most `δ`, for every sampling rule. This is the union-bound condition of [KTAS12, Theorem 1] for
the relative-entropy confidence bounds, and the union-bound proof of correctness mentioned in
[KK13, Appendix A].

[KK13, Theorem 1] obtains the smaller exploration rate
`log (k₁ K n ^ p / δ) + log log (k₁ K n ^ p / δ)`, which depends on the round `n` only, from the
self-normalized deviation inequality of Garivier and Cappé [GC11, Theorem 10]: at round `n`, the
probability that an arm violates one of its bounds at level `x` is at most
`e (x log n + 1) exp (-x)` whatever its number of pulls [KK13, Lemma 4, (13)]
(`LMLExplore.Bandits.measureReal_pullCount_ne_zero_and_klUpper_lt_le`), so a union bound over the
rounds and the arms suffices when `∑_{n ≥ 1} e (b n log n + 1) exp (-b n) ≤ δ / K`. For
`p > 1`, `k₁ ≥ 2 e + 1 + e / (p - 1) + (e + 1) / (p - 1) ^ 2` and `δ ∈ (0, 1]`, the rate
`b n = log (k₁ K n ^ p / δ) + log log (k₁ K n ^ p / δ)` has `exp (-b n) = δ / (k₁ K n ^ p L_n)` with
`L_n = log (k₁ K n ^ p / δ) ≥ 1`, and `log L_n ≤ L_n / e`, so the sum is at most
`δ / (k₁ K) ((e + 1) ∑ log n / n ^ p + e ∑ 1 / n ^ p)`, which the bounds
`∑ log n / n ^ p ≤ 1 + 1 / (p - 1) ^ 2` and `∑ 1 / n ^ p ≤ 1 + 1 / (p - 1)` of
`LMLExplore/Analysis/PSeries.lean` bound by `δ / K`.

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
* `isDeltaPAC_kllucb`: KL-LUCB is `δ`-PAC on top-`m` identification with tolerance `ε`
  (`epsTopMTask lawBandit lawMean m ε`) restricted to every set of bandits with laws on `[0, 1]` on
  which it stops almost surely.
* `measureReal_histOutputMeasure_kllucb_le_of_tsum_mul_log_le`: for an exploration rate `b n > 0`
  depending on the round `n` only, with `∑_{n ≥ 1} e (b n log n + 1) exp (-b n) ≤ δ / K`, KL-LUCB
  stops with a wrong answer with probability at most `δ`, for every sampling rule.
* `measureReal_stoppingTime_ne_top_and_notMem_le_of_isRun_kllucb_of_tsum_mul_log_le`,
  `isDeltaPAC_kllucb_of_tsum_mul_log_le`: the same bound along every run, and KL-LUCB with such an
  exploration rate is `δ`-PAC.
* `measureReal_histOutputMeasure_kllucb_log_add_log_log_le`,
  `measureReal_stoppingTime_ne_top_and_notMem_le_of_isRun_kllucb_log_add_log_log`,
  `isDeltaPAC_kllucb_log_add_log_log`: [KK13, Theorem 1] for KL-LUCB, the same three statements as
  above for the exploration rate `log (k₁ K n ^ p / δ) + log log (k₁ K n ^ p / δ)`, with `p > 1`
  and `k₁ ≥ 2 e + 1 + e / (p - 1) + (e + 1) / (p - 1) ^ 2`.

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
* [GC11] A. Garivier and O. Cappé, *The KL-UCB algorithm for bounded stochastic bandits and
  beyond*, COLT 2011, Theorem 10.
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
[KTAS12, Theorem 1] for the confidence bounds of [KK13, (4), (5)]; this is the union-bound proof
mentioned in [KK13, Appendix A]. Let the rewards of the arms of `ν₀` be in `[0, 1]`, with means
`μ`, let `ε ≥ 0` and `m ≤ K`, and let the exploration rate `β` satisfy
`∑_n ∑_{u = 1}^n exp (-β(u, n)) ≤ δ / K`. Then the probability that KL-LUCB stops with an answer
that is not a correct answer of top-`m` identification with tolerance `ε` for `μ` is at most
`δ`. -/
theorem measureReal_histOutputMeasure_kllucb_le
    (hν : ∀ a, ∀ᵐ x ∂(ν₀ a), x ∈ Set.Icc (0 : ℝ) 1)
    (hsum : Summable fun n ↦ ∑ u ∈ Icc 1 n, exp (-β u n))
    (hδ : ∑' n, ∑ u ∈ Icc 1 n, exp (-β u n) ≤ δ / Fintype.card α)
    (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α) :
    (histOutputMeasure (kllucb alg β ε m) (Environment.bandit ν₀)).real
        {p | p.1 ∈ (kllucb alg β ε m).stopSet ∧
          p.2 ∉ (epsTopMTask ν id m ε).correct fun a ↦ (ν₀ a)[id]} ≤ δ := by
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
        out ω ∉ (epsTopMTask ν id m ε).correct fun a ↦ (ν₀ a)[id]} ≤ δ := by
  rw [hrun.measureReal_stoppingTime_ne_top_and_notMem_eq (Set.to_countable _).measurableSet]
  exact measureReal_histOutputMeasure_kllucb_le hν hsum hδ hε hm

/-- **KL-LUCB is `δ`-PAC as soon as its error probability is at most `δ`**. Let `S` be a set of
bandits whose arms have laws on `[0, 1]`. If, for every bandit with rewards in `[0, 1]`, KL-LUCB
stops with an answer that is not a correct answer of top-`m` identification with tolerance `ε`
with probability at most `δ`, and if it stops almost surely on every bandit of `S`, then it is
`δ`-PAC on the task restricted to `S`. -/
private lemma isDeltaPAC_kllucb_of_measureReal_le {S : Set (α → ProbabilityMeasure ℝ)}
    (hS : S ⊆ Set.univ.pi fun _ ↦ unitIntervalLaws)
    (h_err : ∀ (ν₀ : Kernel α ℝ) [IsMarkovKernel ν₀],
      (∀ a, ∀ᵐ x ∂(ν₀ a), x ∈ Set.Icc (0 : ℝ) 1) →
      (histOutputMeasure (kllucb alg β ε m) (Environment.bandit ν₀)).real
        {p | p.1 ∈ (kllucb alg β ε m).stopSet ∧
          p.2 ∉ (epsTopMTask (fun _ ↦ ν₀) id m ε).correct fun a ↦ (ν₀ a)[id]} ≤ δ)
    (h_stops : ∀ θ ∈ S, StopsAS (kllucb alg β ε m) (Environment.bandit (lawBandit θ))) :
    ((epsTopMTask (lawBandit (α := α)) lawMean m ε).restrict S).IsDeltaPAC
      (kllucb alg β ε m) δ := by
  have hS' (θ : α → ProbabilityMeasure ℝ)
      (hθ : θ ∈ ((epsTopMTask (lawBandit (α := α)) lawMean m ε).restrict S).M) : θ ∈ S := by
    rw [IdentTask.M_restrict] at hθ
    exact hθ.2
  refine IdentTask.isDeltaPAC_of_measureReal_mem_stopSet_and_notMem_le
    (fun θ _ ↦ (Set.to_countable _).measurableSet) (fun θ hθ ↦ ?_)
    fun θ hθ ↦ by simpa only [IdentTask.ν_restrict, ν_epsTopMTask] using h_stops θ (hS' θ hθ)
  simpa only [IdentTask.ν_restrict, IdentTask.correct_restrict, ν_epsTopMTask, correct_epsTopMTask,
    id, lawMean_eq_integral_lawBandit] using h_err _ (mem_pi_unitIntervalLaws_iff.1 (hS (hS' θ hθ)))

/-- **KL-LUCB is `δ`-PAC** for top-`m` identification with tolerance `ε`, for every sampling rule
[KTAS12, Theorem 1] for the confidence bounds of [KK13, (4), (5)]; this is the union-bound proof
mentioned in [KK13, Appendix A]. Let `S` be a set of bandits whose arms have laws on `[0, 1]`, let
`ε ≥ 0` and `m ≤ K`, and let the exploration rate `β` satisfy
`∑_n ∑_{u = 1}^n exp (-β(u, n)) ≤ δ / K`. If KL-LUCB stops almost surely on every bandit of `S`,
then it is `δ`-PAC on the task restricted to `S`. -/
theorem isDeltaPAC_kllucb {S : Set (α → ProbabilityMeasure ℝ)}
    (hS : S ⊆ Set.univ.pi fun _ ↦ unitIntervalLaws)
    (hsum : Summable fun n ↦ ∑ u ∈ Icc 1 n, exp (-β u n))
    (hδ : ∑' n, ∑ u ∈ Icc 1 n, exp (-β u n) ≤ δ / Fintype.card α)
    (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α)
    (h_stops : ∀ θ ∈ S, StopsAS (kllucb alg β ε m) (Environment.bandit (lawBandit θ))) :
    ((epsTopMTask (lawBandit (α := α)) lawMean m ε).restrict S).IsDeltaPAC
      (kllucb alg β ε m) δ :=
  isDeltaPAC_kllucb_of_measureReal_le hS
    (fun _ _ hν ↦ measureReal_histOutputMeasure_kllucb_le hν hsum hδ hε hm) h_stops

/-! ### The exploration rate of [KK13, Theorem 1] -/

/-- **Error probability of KL-LUCB with an exploration rate depending on the round**, for rewards
in `[0, 1]` and every sampling rule [KK13, Lemmas 3 and 4]. Let the rewards of the arms of `ν₀` be
in `[0, 1]`, with means `μ`, let `ε ≥ 0` and `m ≤ K`, and let the exploration rate `b n > 0` after
`n ≥ 1` rounds satisfy `∑_{n ≥ 1} e (b n log n + 1) exp (-b n) ≤ δ / K`. Then the probability that
KL-LUCB stops with an answer that is not a correct answer of top-`m` identification with tolerance
`ε` for `μ` is at most `δ`. -/
theorem measureReal_histOutputMeasure_kllucb_le_of_tsum_mul_log_le {b : ℕ → ℝ}
    (hν : ∀ a, ∀ᵐ x ∂(ν₀ a), x ∈ Set.Icc (0 : ℝ) 1) (hb : ∀ n, 0 < b (n + 1))
    (hsum : Summable fun n : ℕ ↦ exp 1 * (b (n + 1) * log (n + 1 : ℕ) + 1) * exp (-b (n + 1)))
    (hδ : ∑' n : ℕ, exp 1 * (b (n + 1) * log (n + 1 : ℕ) + 1) * exp (-b (n + 1)) ≤
      δ / Fintype.card α)
    (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α) :
    (histOutputMeasure (kllucb alg (fun _ n ↦ b n) ε m) (Environment.bandit ν₀)).real
        {p | p.1 ∈ (kllucb alg (fun _ n ↦ b n) ε m).stopSet ∧
          p.2 ∉ (epsTopMTask ν id m ε).correct fun a ↦ (ν₀ a)[id]} ≤ δ := by
  rw [kllucb_def]
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit ν₀)
  have hP : IsProbabilityMeasure (trajMeasure alg (Environment.bandit ν₀)) :=
    inferInstanceAs (IsProbabilityMeasure (trajMeasure alg (Environment.bandit ν₀)))
  set g : ℕ → ℝ := fun n ↦ exp 1 * (b (n + 1) * log (n + 1 : ℕ) + 1) * exp (-b (n + 1))
  have hg0 (n : ℕ) : 0 ≤ g n := by
    have := log_natCast_nonneg (n + 1)
    have := hb n
    positivity
  -- a union bound over the rounds `n ≥ 1`, at which the arm may have been pulled, of the events
  -- `Q n N_a μ̂_a` on the number of pulls `N_a` and the empirical mean `μ̂_a` of the arm `a`
  have h_union (a : α) (Q : ℕ → ℕ → ℝ → Prop)
      (hQ : ∀ n, (trajMeasure alg (Environment.bandit ν₀)).real
        {ω | pullCount IT.action a (n + 1) ω ≠ 0 ∧ Q (n + 1) (pullCount IT.action a (n + 1) ω)
          (empMean IT.action IT.feedback a (n + 1) ω)} ≤ g n) :
      (trajMeasure alg (Environment.bandit ν₀)).real
        {ω | ∃ n, pullCount IT.action a n ω ≠ 0 ∧
          Q n (pullCount' n (history IT.obs IT.action IT.feedback n ω) a)
            (empMean' n (history IT.obs IT.action IT.feedback n ω) a)} ≤ ∑' n, g n := by
    have h_sub : {ω : ℕ → Unit × α × ℝ | ∃ n, pullCount IT.action a n ω ≠ 0 ∧
          Q n (pullCount' n (history IT.obs IT.action IT.feedback n ω) a)
            (empMean' n (history IT.obs IT.action IT.feedback n ω) a)} ⊆
        ⋃ n, {ω | pullCount IT.action a (n + 1) ω ≠ 0 ∧ Q (n + 1)
          (pullCount IT.action a (n + 1) ω) (empMean IT.action IT.feedback a (n + 1) ω)} := by
      rintro ω ⟨n, hn, h⟩
      rcases n with _ | n
      · simp only [pullCount_zero] at hn
        exact absurd rfl hn
      · rw [← empMean_eq_empMean', ← pullCount_eq_pullCount'] at h
        exact Set.mem_iUnion.2 ⟨n, hn, h⟩
    refine ENNReal.toReal_le_of_le_ofReal (tsum_nonneg hg0) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg hg0 hsum]
    refine (measure_mono h_sub).trans ((measure_iUnion_le _).trans (tsum_le_tsum fun n ↦ ?_))
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hQ n)
  refine (measureReal_histOutputMeasure_lucb_le_card_mul hseq hε hm (S := ∑' n, g n)
    (fun a ↦ ?_) (fun a ↦ ?_)).trans ?_
  · simp only [LUCB.klUpperBound_def]
    exact h_union a (fun n N y ↦ klUpper y (ENNReal.ofReal (b n / N)) < (ν₀ a)[id]) fun n ↦
      Bandits.measureReal_pullCount_ne_zero_and_klUpper_lt_le hseq a (hν a) (hb n) (n + 1)
  · simp only [LUCB.klLowerBound_def]
    exact h_union a (fun n N y ↦ (ν₀ a)[id] < klLower y (ENNReal.ofReal (b n / N))) fun n ↦
      Bandits.measureReal_pullCount_ne_zero_and_lt_klLower_le hseq a (hν a) (hb n) (n + 1)
  · have hK : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
    rwa [← le_div_iff₀' hK]

/-- **Error probability of KL-LUCB with an exploration rate depending on the round along a run**,
for rewards in `[0, 1]` and every sampling rule. Under the assumptions of
`measureReal_histOutputMeasure_kllucb_le_of_tsum_mul_log_le`, along every run of KL-LUCB with the
exploration rate `b n` after `n` rounds, the probability that it stops with an answer that is not
a correct answer of top-`m` identification with tolerance `ε` for the means `μ` is at most `δ`. -/
theorem measureReal_stoppingTime_ne_top_and_notMem_le_of_isRun_kllucb_of_tsum_mul_log_le
    {b : ℕ → ℝ} {out : Ω → Finset α}
    (hrun : (kllucb alg (fun _ n ↦ b n) ε m).IsRun (Environment.bandit ν₀) O X Y out P)
    (hν : ∀ a, ∀ᵐ x ∂(ν₀ a), x ∈ Set.Icc (0 : ℝ) 1) (hb : ∀ n, 0 < b (n + 1))
    (hsum : Summable fun n : ℕ ↦ exp 1 * (b (n + 1) * log (n + 1 : ℕ) + 1) * exp (-b (n + 1)))
    (hδ : ∑' n : ℕ, exp 1 * (b (n + 1) * log (n + 1 : ℕ) + 1) * exp (-b (n + 1)) ≤
      δ / Fintype.card α)
    (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α) :
    P.real {ω | (kllucb alg (fun _ n ↦ b n) ε m).stoppingTime O X Y ω ≠ ⊤ ∧
        out ω ∉ (epsTopMTask ν id m ε).correct fun a ↦ (ν₀ a)[id]} ≤ δ := by
  rw [hrun.measureReal_stoppingTime_ne_top_and_notMem_eq (Set.to_countable _).measurableSet]
  exact measureReal_histOutputMeasure_kllucb_le_of_tsum_mul_log_le hν hb hsum hδ hε hm

/-- **KL-LUCB with an exploration rate depending on the round is `δ`-PAC** for top-`m`
identification with tolerance `ε`, for every sampling rule [KK13, Lemmas 3 and 4]. Let `S` be a
set of bandits whose arms have laws on `[0, 1]`, let `ε ≥ 0` and `m ≤ K`, and let the exploration
rate `b n > 0` after `n ≥ 1` rounds satisfy `∑_{n ≥ 1} e (b n log n + 1) exp (-b n) ≤ δ / K`. If
KL-LUCB with the exploration rate `b` stops almost surely on every bandit of `S`, then it is
`δ`-PAC on the task restricted to `S`. -/
theorem isDeltaPAC_kllucb_of_tsum_mul_log_le {b : ℕ → ℝ} {S : Set (α → ProbabilityMeasure ℝ)}
    (hS : S ⊆ Set.univ.pi fun _ ↦ unitIntervalLaws) (hb : ∀ n, 0 < b (n + 1))
    (hsum : Summable fun n : ℕ ↦ exp 1 * (b (n + 1) * log (n + 1 : ℕ) + 1) * exp (-b (n + 1)))
    (hδ : ∑' n : ℕ, exp 1 * (b (n + 1) * log (n + 1 : ℕ) + 1) * exp (-b (n + 1)) ≤
      δ / Fintype.card α)
    (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α)
    (h_stops : ∀ θ ∈ S,
      StopsAS (kllucb alg (fun _ n ↦ b n) ε m) (Environment.bandit (lawBandit θ))) :
    ((epsTopMTask (lawBandit (α := α)) lawMean m ε).restrict S).IsDeltaPAC
      (kllucb alg (fun _ n ↦ b n) ε m) δ :=
  isDeltaPAC_kllucb_of_measureReal_le hS
    (fun _ _ hν ↦ measureReal_histOutputMeasure_kllucb_le_of_tsum_mul_log_le hν hb hsum hδ hε hm)
    h_stops

/-- For `p ≥ 0`, `k₁ ≥ e`, `K ≥ 1`, `δ ∈ (0, 1]` and `n ≥ 1`, `log (k₁ K n ^ p / δ) ≥ 1`. -/
private lemma one_le_log_mul_rpow_div {k₁ p δ : ℝ} {K : ℕ} (hp : 0 ≤ p) (hk : exp 1 ≤ k₁)
    (hK : 1 ≤ K) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ log (k₁ * K * n ^ p / δ) := by
  have hk0 : 0 ≤ k₁ := (exp_pos 1).le.trans hk
  have hK0 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hnp : 1 ≤ (n : ℝ) ^ p := one_le_rpow (by exact_mod_cast hn) hp
  have hy : exp 1 ≤ k₁ * K * n ^ p / δ := by
    rw [le_div_iff₀ hδ]
    calc exp 1 * δ
    _ ≤ k₁ * 1 := by gcongr
    _ ≤ k₁ * (K * n ^ p) := by
      gcongr
      nlinarith
    _ = k₁ * K * n ^ p := by ring
  rwa [le_log_iff_exp_le ((exp_pos 1).trans_le hy)]

/-- One term of the union bound of [KK13, Theorem 1]: for `p ≥ 0`, `k₁ ≥ e`, `K ≥ 1`,
`δ ∈ (0, 1]` and `n ≥ 1`, the exploration rate `b = log y + log log y`, `y = k₁ K n ^ p / δ`, has
`e (b log n + 1) exp (-b) ≤ δ / (k₁ K) ((e + 1) log n / n ^ p + e / n ^ p)`, since
`exp (-b) = 1 / (y log y)` and `log log y ≤ log y / e`. -/
private lemma exp_one_mul_log_add_log_log_mul_log_add_one_mul_exp_le {k₁ p δ : ℝ} {K : ℕ}
    (hp : 0 ≤ p) (hk : exp 1 ≤ k₁) (hK : 1 ≤ K) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    exp 1 * ((log (k₁ * K * n ^ p / δ) + log (log (k₁ * K * n ^ p / δ))) * log n + 1) *
        exp (-(log (k₁ * K * n ^ p / δ) + log (log (k₁ * K * n ^ p / δ)))) ≤
      δ / (k₁ * K) * ((exp 1 + 1) * (log n / n ^ p) + exp 1 * (1 / n ^ p)) := by
  have hk0 : 0 < k₁ := (exp_pos 1).trans_le hk
  have hK0 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hnp : 1 ≤ (n : ℝ) ^ p := one_le_rpow (by exact_mod_cast hn) hp
  set y := k₁ * K * n ^ p / δ with hy_def
  have hy0 : 0 < y := by positivity
  set L := log y with hL_def
  have hL : 1 ≤ L := one_le_log_mul_rpow_div hp hk hK hδ hδ1 hn
  have hL0 : 0 < L := by linarith
  -- `e log L ≤ L`, since `log L / L = log L * exp (-log L) ≤ exp (-1)`
  have hlogL : exp 1 * log L ≤ L := by
    have h := mul_exp_neg_le_exp_neg_one (log L)
    rw [exp_neg, exp_log hL0, exp_neg, ← div_eq_mul_inv, div_le_iff₀ hL0, inv_mul_eq_div,
      le_div_iff₀ (exp_pos 1)] at h
    linarith
  have hlogL0 : 0 ≤ log L := log_nonneg hL
  have hlogn : 0 ≤ log n := log_natCast_nonneg n
  have h_exp : exp (-(L + log L)) = (y * L)⁻¹ := by
    rw [exp_neg, exp_add, exp_log hy0, exp_log hL0]
  rw [h_exp]
  have h_key : exp 1 * ((L + log L) * log n + 1) ≤ L * ((exp 1 + 1) * log n + exp 1) := by
    nlinarith [mul_le_mul_of_nonneg_right hlogL hlogn, exp_pos 1]
  have hnp0 : 0 < (n : ℝ) ^ p := by linarith
  calc exp 1 * ((L + log L) * log n + 1) * (y * L)⁻¹
  _ = δ / (k₁ * K * n ^ p) * (exp 1 * ((L + log L) * log n + 1) / L) := by
    rw [hy_def]
    field_simp
  _ ≤ δ / (k₁ * K * n ^ p) * ((exp 1 + 1) * log n + exp 1) := by
    gcongr
    rwa [div_le_iff₀ hL0, mul_comm _ L]
  _ = δ / (k₁ * K) * ((exp 1 + 1) * (log n / n ^ p) + exp 1 * (1 / n ^ p)) := by
    field_simp

/-- The union bound of [KK13, Theorem 1]: for `p > 1`,
`k₁ ≥ 2 e + 1 + e / (p - 1) + (e + 1) / (p - 1) ^ 2`, `K ≥ 1` and `δ ∈ (0, 1]`, the exploration
rate `b n = log (k₁ K n ^ p / δ) + log log (k₁ K n ^ p / δ)` has
`∑_{n ≥ 1} e (b n log n + 1) exp (-b n) ≤ δ / K`, the series being summable. -/
private lemma summable_and_tsum_exp_one_mul_log_add_log_log_le {k₁ p δ : ℝ} {K : ℕ} (hp : 1 < p)
    (hk : 2 * exp 1 + 1 + exp 1 / (p - 1) + (exp 1 + 1) / (p - 1) ^ 2 ≤ k₁) (hK : 1 ≤ K)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {b : ℕ → ℝ}
    (hb : ∀ n, b n = log (k₁ * K * n ^ p / δ) + log (log (k₁ * K * n ^ p / δ))) :
    (∀ n, 0 < b (n + 1)) ∧
      (Summable fun n : ℕ ↦ exp 1 * (b (n + 1) * log (n + 1 : ℕ) + 1) * exp (-b (n + 1))) ∧
      ∑' n : ℕ, exp 1 * (b (n + 1) * log (n + 1 : ℕ) + 1) * exp (-b (n + 1)) ≤ δ / K := by
  have hp1 : 0 < p - 1 := by linarith
  have he := exp_pos 1
  have hk1 : exp 1 ≤ k₁ := by
    have : 0 ≤ exp 1 / (p - 1) + (exp 1 + 1) / (p - 1) ^ 2 := by positivity
    linarith
  have hk0 : 0 < k₁ := he.trans_le hk1
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  -- the dominating series `δ / (k₁ K) ((e + 1) log n / n ^ p + e / n ^ p)`
  set h : ℕ → ℝ := fun n ↦ δ / (k₁ * K) * ((exp 1 + 1) * (log n / n ^ p) + exp 1 * (1 / n ^ p))
  have hh : Summable h := (((Real.summable_log_div_nat_rpow hp).mul_left _).add
    ((Real.summable_one_div_nat_rpow.2 hp).mul_left _)).mul_left _
  have h_le (n : ℕ) : exp 1 * (b (n + 1) * log (n + 1 : ℕ) + 1) * exp (-b (n + 1)) ≤ h (n + 1) :=
    hb (n + 1) ▸
      exp_one_mul_log_add_log_log_mul_log_add_one_mul_exp_le (by linarith) hk1 hK hδ hδ1 (by omega)
  -- `b (n + 1) = L + log L` with `L ≥ 1`
  have hb1 (n : ℕ) : 1 ≤ b (n + 1) := by
    have hL := one_le_log_mul_rpow_div (p := p) (by linarith) hk1 hK hδ hδ1 (by omega : 1 ≤ n + 1)
    rw [hb]
    linarith [log_nonneg hL]
  have h_nonneg (n : ℕ) : 0 ≤ exp 1 * (b (n + 1) * log (n + 1 : ℕ) + 1) * exp (-b (n + 1)) := by
    have := log_natCast_nonneg (n + 1)
    have := hb1 n
    positivity
  have h_summable := ((summable_nat_add_iff 1).2 hh).of_nonneg_of_le h_nonneg h_le
  refine ⟨fun n ↦ zero_lt_one.trans_le (hb1 n), h_summable, ?_⟩
  -- the term of index `0` of the dominating series vanishes
  have h0 : h 0 = 0 := by simp [h, zero_rpow (by linarith : p ≠ 0)]
  calc ∑' n : ℕ, exp 1 * (b (n + 1) * log (n + 1 : ℕ) + 1) * exp (-b (n + 1))
  _ ≤ ∑' n : ℕ, h (n + 1) := h_summable.tsum_le_tsum h_le ((summable_nat_add_iff 1).2 hh)
  _ = ∑' n : ℕ, h n := by rw [hh.tsum_eq_zero_add, h0, zero_add]
  _ = δ / (k₁ * K) * ((exp 1 + 1) * ∑' n : ℕ, log n / (n : ℝ) ^ p +
      exp 1 * ∑' n : ℕ, 1 / (n : ℝ) ^ p) := by
    simp only [h]
    rw [tsum_mul_left, Summable.tsum_add ((Real.summable_log_div_nat_rpow hp).mul_left _)
      ((Real.summable_one_div_nat_rpow.2 hp).mul_left _), tsum_mul_left, tsum_mul_left]
  _ ≤ δ / (k₁ * K) * ((exp 1 + 1) * (1 + 1 / (p - 1) ^ 2) + exp 1 * (1 + 1 / (p - 1))) := by
    gcongr
    · exact Real.tsum_log_div_nat_rpow_le hp
    · exact Real.tsum_one_div_nat_rpow_le hp
  _ ≤ δ / (k₁ * K) * k₁ := by
    gcongr
    calc (exp 1 + 1) * (1 + 1 / (p - 1) ^ 2) + exp 1 * (1 + 1 / (p - 1))
    _ = 2 * exp 1 + 1 + exp 1 / (p - 1) + (exp 1 + 1) / (p - 1) ^ 2 := by ring
    _ ≤ k₁ := hk
  _ = δ / K := by
    field_simp

/-- **Error probability of KL-LUCB with the exploration rate of [KK13, Theorem 1]**, for rewards
in `[0, 1]` and every sampling rule. Let the rewards of the arms of `ν₀` be in `[0, 1]`, with
means `μ`, let `ε ≥ 0` and `m ≤ K`, `δ ∈ (0, 1]`, `p > 1` and
`k₁ ≥ 2 e + 1 + e / (p - 1) + (e + 1) / (p - 1) ^ 2`. Then KL-LUCB with the exploration rate
`log (k₁ K n ^ p / δ) + log log (k₁ K n ^ p / δ)` after `n` rounds stops with an answer that is not
a correct answer of top-`m` identification with tolerance `ε` for `μ` with probability at most
`δ`. -/
theorem measureReal_histOutputMeasure_kllucb_log_add_log_log_le {k₁ p : ℝ}
    (hν : ∀ a, ∀ᵐ x ∂(ν₀ a), x ∈ Set.Icc (0 : ℝ) 1) (hp : 1 < p)
    (hk : 2 * exp 1 + 1 + exp 1 / (p - 1) + (exp 1 + 1) / (p - 1) ^ 2 ≤ k₁) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α) :
    (histOutputMeasure (kllucb alg (fun _ n ↦ log (k₁ * Fintype.card α * n ^ p / δ) +
          log (log (k₁ * Fintype.card α * n ^ p / δ))) ε m) (Environment.bandit ν₀)).real
        {q | q.1 ∈ (kllucb alg (fun _ n ↦ log (k₁ * Fintype.card α * n ^ p / δ) +
            log (log (k₁ * Fintype.card α * n ^ p / δ))) ε m).stopSet ∧
          q.2 ∉ (epsTopMTask ν id m ε).correct fun a ↦ (ν₀ a)[id]} ≤ δ := by
  obtain ⟨hb, hsum, htsum⟩ := summable_and_tsum_exp_one_mul_log_add_log_log_le hp hk
    Fintype.card_pos hδ hδ1 (K := Fintype.card α) (b := fun n ↦
      log (k₁ * Fintype.card α * n ^ p / δ) + log (log (k₁ * Fintype.card α * n ^ p / δ)))
    fun n ↦ rfl
  exact measureReal_histOutputMeasure_kllucb_le_of_tsum_mul_log_le hν hb hsum htsum hε hm

/-- **Error probability of KL-LUCB with the exploration rate of [KK13, Theorem 1] along a run**,
for rewards in `[0, 1]` and every sampling rule. Under the assumptions of
`measureReal_histOutputMeasure_kllucb_log_add_log_log_le`, along every run of KL-LUCB with the
exploration rate `log (k₁ K n ^ p / δ) + log log (k₁ K n ^ p / δ)`, the probability that it stops
with an answer that is not a correct answer of top-`m` identification with tolerance `ε` for the
means `μ` is at most `δ`. -/
theorem measureReal_stoppingTime_ne_top_and_notMem_le_of_isRun_kllucb_log_add_log_log
    {k₁ p : ℝ} {out : Ω → Finset α}
    (hrun : (kllucb alg (fun _ n ↦ log (k₁ * Fintype.card α * n ^ p / δ) +
      log (log (k₁ * Fintype.card α * n ^ p / δ))) ε m).IsRun (Environment.bandit ν₀) O X Y out P)
    (hν : ∀ a, ∀ᵐ x ∂(ν₀ a), x ∈ Set.Icc (0 : ℝ) 1) (hp : 1 < p)
    (hk : 2 * exp 1 + 1 + exp 1 / (p - 1) + (exp 1 + 1) / (p - 1) ^ 2 ≤ k₁) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α) :
    P.real {ω | (kllucb alg (fun _ n ↦ log (k₁ * Fintype.card α * n ^ p / δ) +
          log (log (k₁ * Fintype.card α * n ^ p / δ))) ε m).stoppingTime O X Y ω ≠ ⊤ ∧
        out ω ∉ (epsTopMTask ν id m ε).correct fun a ↦ (ν₀ a)[id]} ≤ δ := by
  obtain ⟨hb, hsum, htsum⟩ := summable_and_tsum_exp_one_mul_log_add_log_log_le hp hk
    Fintype.card_pos hδ hδ1 (K := Fintype.card α) (b := fun n ↦
      log (k₁ * Fintype.card α * n ^ p / δ) + log (log (k₁ * Fintype.card α * n ^ p / δ)))
    fun n ↦ rfl
  exact measureReal_stoppingTime_ne_top_and_notMem_le_of_isRun_kllucb_of_tsum_mul_log_le hrun hν
    hb hsum htsum hε hm

/-- **KL-LUCB with the exploration rate of [KK13, Theorem 1] is `δ`-PAC** for top-`m`
identification with tolerance `ε`, for every sampling rule. Let `S` be a set of bandits whose arms
have laws on `[0, 1]`, let `ε ≥ 0` and `m ≤ K`, `δ ∈ (0, 1]`, `p > 1` and
`k₁ ≥ 2 e + 1 + e / (p - 1) + (e + 1) / (p - 1) ^ 2`. If KL-LUCB with the exploration rate
`log (k₁ K n ^ p / δ) + log log (k₁ K n ^ p / δ)` stops almost surely on every bandit of `S`, then
it is `δ`-PAC on the task restricted to `S`. -/
theorem isDeltaPAC_kllucb_log_add_log_log {k₁ p : ℝ} {S : Set (α → ProbabilityMeasure ℝ)}
    (hS : S ⊆ Set.univ.pi fun _ ↦ unitIntervalLaws) (hp : 1 < p)
    (hk : 2 * exp 1 + 1 + exp 1 / (p - 1) + (exp 1 + 1) / (p - 1) ^ 2 ≤ k₁) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) (hm : m ≤ Fintype.card α)
    (h_stops : ∀ θ ∈ S, StopsAS (kllucb alg (fun _ n ↦ log (k₁ * Fintype.card α * n ^ p / δ) +
      log (log (k₁ * Fintype.card α * n ^ p / δ))) ε m) (Environment.bandit (lawBandit θ))) :
    ((epsTopMTask (lawBandit (α := α)) lawMean m ε).restrict S).IsDeltaPAC
      (kllucb alg (fun _ n ↦ log (k₁ * Fintype.card α * n ^ p / δ) +
        log (log (k₁ * Fintype.card α * n ^ p / δ))) ε m) δ := by
  obtain ⟨hb, hsum, htsum⟩ := summable_and_tsum_exp_one_mul_log_add_log_log_le hp hk
    Fintype.card_pos hδ hδ1 (K := Fintype.card α) (b := fun n ↦
      log (k₁ * Fintype.card α * n ^ p / δ) + log (log (k₁ * Fintype.card α * n ^ p / δ)))
    fun n ↦ rfl
  exact isDeltaPAC_kllucb_of_tsum_mul_log_le hS hb hsum htsum hε hm h_stops

end LMLExplore.Identification
