/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.Online.Bandit.Regret
public import LeanMachineLearning.SequentialLearning.SumRewards
public import LMLExplore.Analysis.SpecialFunctions.Log.Basic
public import LMLExplore.Bandits.AsymptoticallyOptimalUCB
public import LMLExplore.Bandits.Concentration
public import LMLExplore.Bandits.IndexAlgorithm
public import LMLExplore.Bandits.Regret
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
public import LMLExplore.Probability.Distributions.ExponentialFamily.Bernoulli
public import LMLExplore.Probability.Distributions.ExponentialFamily.Gaussian
public import LMLExplore.SequentialLearning.Algorithm

/-!
# KL-UCB

The KL-UCB algorithm [LS, Algorithm 8; GC11, Section 4; CGMMS13] for exponential families of real
rewards is the index policy whose index at book round `t`, for an arm `a` pulled `T_a > 0` times
with empirical mean `μ̂_a`, is the upper confidence level `U_{ρ_a}(μ̂_a, log f(t) / T_a)` of the
exponential family `ρ_a` of arm `a` with the identity statistic (`Measure.expFamilyUpper`): the
supremum in `EReal` of `μ̂_a` and of the means `q ≥ μ̂_a` of the family with extended divergence
`dbar(μ̂_a, q) ≤ log f(t) / T_a`, where `f(t) = 1 + t log² t`. Each arm has its own family. An
arm that has not been pulled yet has index `⊤`, so that the policy pulls every arm once before
comparing finite indices. It is stated for any finite type of arms and does not depend on an
enumeration of the arms.

Two instances are classical. With the Bernoulli family on every arm, the index at an empirical
mean in `[0, 1]` is the upper confidence level `U(μ̂_a, log f(t) / T_a)` of the binary relative
entropy, the largest `q ∈ [μ̂_a, 1]` with `d(μ̂_a, q) ≤ log f(t) / T_a`: this is KL-UCB for
rewards in `[0, 1]` of [LS, Algorithm 8], defined here as that instance. With the Gaussian family
of variance `σ²` on every arm, the index is `μ̂_a + √(2 σ² log f(t) / T_a)`: this is the
asymptotically optimal UCB algorithm `ucbF σ2` of [LS, Algorithm 6].

Book round `t` is Lean round `n = t - 1`, at which the history has length `n`: the index of
Lean round `n` uses `log f(n + 1)`.

## Main definitions

* `LMLExplore.Bandits.klucbFamIndex ρ n h a`: the index of arm `a` after the history `h` of length
  `n`, for the families `ρ`.
* `LMLExplore.Bandits.klucbFam ρ`: the KL-UCB algorithm for the families `ρ`, the index policy
  `indexAlgorithm` with index `klucbFamIndex ρ`.
* `LMLExplore.Bandits.klucbIndex n h a`: the index of [LS, Algorithm 8] for rewards in `[0, 1]`.
* `LMLExplore.Bandits.klucb`: the KL-UCB algorithm for rewards in `[0, 1]`, the KL-UCB algorithm
  for the Bernoulli family on every arm.

## Main statements

* `klucbFamIndex_eq_top_iff`: when the confidence levels of the families are finite at finite
  budgets, the index is `⊤` exactly on the arms not pulled yet.
* `klucbFamIndex_history`: along a sequence of rounds, the index in terms of LML's `pullCount` and
  `empMean`.
* `klucbFamIndex_bernoulliMeasure_sigmoid`: at empirical means in `[0, 1]`, the index for the
  Bernoulli family is `klucbIndex`.
* `klucbFam_gaussianReal`: the KL-UCB algorithm for the Gaussian family of variance `σ2` is
  `ucbF σ2`.
* `KLUCBFam.pullCount_card_eq_one`, `KLUCB.pullCount_card_eq_one`: KL-UCB pulls every arm exactly
  once during the first `Fintype.card α` rounds.
* `KLUCBFam.integral_pullCount_le_sum_add_sum`: the decomposition of the expected number of pulls
  of an arm `a`: for every arm `b` and every mean `c` of the family of `a`, `E[T_a(n)]` is at most
  the sum over the rounds `t < n` of the probabilities that the index of `b` is at most `c`, plus
  the sum over `t < n` of the probabilities that `a` is played at round `t` while either it has
  not been pulled yet (`T_a = 0`), or its empirical mean `μ̂_a` is at least `c`, or
  `dbar(μ̂_a, c) ≤ log f(n) / T_a` for the exploration level `log f(n)` of the horizon.
* `KLUCB.integral_pullCount_le_sum_add_sum`: the same decomposition for rewards in `[0, 1]` in the
  proof of [LS, Theorem 10.6], with `klUpper` and `d = klBer` and a threshold `c ∈ (0, 1)`.
* `KLUCBFam.integral_pullCount_le`: for arms dominated by their families, the bound
  `1 + log f(n) / d_{ρ a}(μ_a + ε₁, μ_b - ε₂) + 1 / d_{ρ a}(μ_a + ε₁, μ_a) +
  3 / (2 d_{ρ b}(μ_b - ε₂, μ_b))` on the expected number of pulls of an arm `a`, for an arm `b`
  with a larger mean (typically an optimal arm).
* `klucbFam_regret_le`: the resulting finite-time bound on the expected regret of KL-UCB for
  exponential families.
* `KLUCBFam.integral_pullCount_eventually_le`, `klucbFam_regret_eventually_le`: for arms
  dominated by their families, `limsup_n E[T_a(n)] / log n ≤ 1 / d_{ρ a}(μ_a, μ*)` and
  `limsup_n E[R_n] / log n ≤ ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)` when `μ*` is a mean of the
  family of every arm with positive gap.
* `klucbFam_gaussianReal_regret_eventually_le`: for `σ2_a`-sub-Gaussian rewards and the Gaussian
  families of variances `σ2_a`, `limsup_n E[R_n] / log n ≤ ∑_{a : Δ_a > 0} 2 σ2_a / Δ_a`.
* `KLUCB.integral_pullCount_le`: for rewards in `[0, 1]`, the bound
  `log f(n) / d(μ_a + ε₁, μ* - ε₂) + 1 / (2 ε₁²) + 2 / ε₂²` on the expected number of pulls of an
  arm `a` with gap `Δ_a`, for all `ε₁, ε₂ > 0` with `ε₁ + ε₂ < Δ_a`.
* `klucb_regret_le`: [LS, Theorem 10.6], the finite-time bound on the expected regret.
* `KLUCB.integral_pullCount_eventually_le`: for rewards in `[0, 1]`, an arm `a` with positive gap
  and every `c > 1 / d(μ_a, μ*)`, eventually `E[T_a(n)] ≤ c log n`, that is,
  `limsup_n E[T_a(n)] / log n ≤ 1 / d(μ_a, μ*)`.
* `klucb_regret_eventually_le`: the asymptotic part of [LS, Theorem 10.6]: for every
  `c > ∑_{a : Δ_a > 0} Δ_a / d(μ_a, μ*)`, eventually `E[R_n] ≤ c log n`, that is,
  `limsup_n E[R_n] / log n ≤ ∑_{a : Δ_a > 0} Δ_a / d(μ_a, μ*)`.

* `klucb_regret_eventually_le_of_integral_bestArm_eq_one`: when the largest mean is `1`, the
  expected regret is `o(log n)`.

In the asymptotic statements for rewards in `[0, 1]` (`KLUCB.integral_pullCount_eventually_le`,
`klucb_regret_eventually_le`), `1 / d(μ_a, μ*)` and `Δ_a / d(μ_a, μ*)` are computed from the real
number `(klBer μ_a μ*).toReal`, which is `0` when `d(μ_a, μ*) = ∞`, so that both quantities are
then `0`. For an arm with positive gap, `d(μ_a, μ*) = ∞` happens exactly when `μ* = 1`: such an
arm is pulled `o(log n)` times in expectation.

## Implementation notes

An arm `a` is dominated by its family if its mean `μ_a` is a mean of `ρ a` and its law is
dominated in moment generating function (`MGFDominatedOn`) by the member of mean `μ_a` of `ρ a`.
The bounds for exponential families use only the half of that domination which each arm needs:
on `Set.Ici 0` (overestimation) for the arm whose pulls are counted, and on `Set.Iic 0`
(underestimation) for the better arm `b`. They bound the two sums of
`KLUCBFam.integral_pullCount_le_sum_add_sum` at the threshold `μ_b - ε₂` by the generalizations of
[LS, Lemmas 10.7 and 10.8] (`sum_measureReal_pullCount_ne_zero_and_expFamilyUpper_le_le` and
`sum_measureReal_action_eq_and_pullCount_eq_zero_or_le_empMean_or_expFamilyRate_le_le`). The
asymptotic bound chooses `ε₁ = ε₂ = ε` small by continuity of the divergence on the pairs of means
(`Measure.continuousOn_expFamilyDiv`); the family of `b` must not be degenerate so that its
interval of means is open and contains `μ_b - ε`.

The decomposition for rewards in `[0, 1]` is that of the Bernoulli family: almost surely, every
empirical mean lies in `[0, 1]`, where the confidence level and the extended divergence of the
Bernoulli family are `klUpper` and `klBer` (`expFamilyUpper_bernoulliMeasure_sigmoid`,
`expFamilyRate_bernoulliMeasure_sigmoid`). The empirical means `0` and `1` lie outside the open
interval of means of the family, and [LS, Lemmas 10.7 and 10.8] for rewards in `[0, 1]` cover
them, so the regret bounds below are proved through `klUpper` and `klBer`.

The proof of [LS, Theorem 10.6] bounds the two sums of `KLUCB.integral_pullCount_le_sum_add_sum`,
for an optimal arm `b` and the threshold `μ* - ε₂`. The first sum, the underestimation of `b`, is
at most `3 / (4 ε₂²)` by `sum_measureReal_pullCount_ne_zero_and_klUpper_le_le` ([LS, Lemma 10.7]).
The second sum, the overestimation of `a`, is at most `1 + log f(n) / d(μ_a + ε₁, μ* - ε₂) +
1 / (2 ε₁²)` by `sum_measureReal_action_eq_and_pullCount_eq_zero_or_le_empMean_or_klBer_le_le`
([LS, Lemma 10.8]), where the `1` accounts for the first pull of `a`. Since `ε₂ < Δ_a ≤ 1`,
`1 + 3 / (4 ε₂²) ≤ 2 / ε₂²`.

For the asymptotic bound, `ε₁ = ε₂ = ε` is chosen small enough that
`1 / d(μ_a + ε, μ* - ε) < c`. This uses the lower semicontinuity of `d`
(`lowerSemicontinuous_klBer`), which also covers the case `d(μ_a, μ*) = ∞`. The bound of
`KLUCB.integral_pullCount_le` divided by `log n` then tends to `1 / d(μ_a + ε, μ* - ε)`, since
`log f(n) / log n → 1` (`Real.tendsto_log_one_add_mul_log_sq_div_log_atTop`). The book leaves
this limit to its Exercise 10.2.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 10.
* [GC11] A. Garivier and O. Cappé, *The KL-UCB algorithm for bounded stochastic bandits and
  beyond*, COLT 2011.
* [CGMMS13] O. Cappé, A. Garivier, O.-A. Maillard, R. Munos and G. Stoltz, *Kullback–Leibler
  upper confidence bounds for optimal sequential allocation*, Ann. Statist. 41(3), 2013.
-/

public section

open MeasureTheory InformationTheory ProbabilityTheory Finset Filter Topology Real Learning Bandits

open scoped ENNReal NNReal

namespace LMLExplore.Bandits

section FamilyIndex

variable {α : Type*} [DecidableEq α] {ρ : α → Measure ℝ} {n : ℕ} {h : Hist Unit α ℝ n} {a : α}

/-- The index of the KL-UCB algorithm for the exponential families `ρ a` of real rewards (with the
identity statistic) [GC11, Section 4; CGMMS13], at Lean round `n` (book round `n + 1`), for the
history `h` of the first `n` rounds: `⊤` if the arm `a` has not been pulled, and otherwise the
upper confidence level `U_{ρ a}(μ̂_a, log f(n + 1) / T_a)` of the family of `a`
(`Measure.expFamilyUpper`) with `f(t) = 1 + t log² t`, where `T_a` is the number of pulls of `a`
and `μ̂_a` its empirical mean. -/
noncomputable def klucbFamIndex (ρ : α → Measure ℝ) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) :
    EReal :=
  if pullCount' n h a = 0 then ⊤ else
    (ρ a).expFamilyUpper id (empMean' n h a)
      (ENNReal.ofReal (log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount' n h a))

/-- The defining equation of `klucbFamIndex`. -/
lemma klucbFamIndex_def (ρ : α → Measure ℝ) (n : ℕ) (h : Hist Unit α ℝ n) (a : α) :
    klucbFamIndex ρ n h a = if pullCount' n h a = 0 then ⊤ else
      (ρ a).expFamilyUpper id (empMean' n h a)
        (ENNReal.ofReal (log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount' n h a)) :=
  (rfl)

/-- An arm that has not been pulled has index `⊤`. -/
@[simp]
lemma klucbFamIndex_of_pullCount'_eq_zero (h0 : pullCount' n h a = 0) :
    klucbFamIndex ρ n h a = ⊤ := by
  simp [klucbFamIndex_def, h0]

/-- The index of an arm that has been pulled is `U_{ρ a}(μ̂_a, log f(n + 1) / T_a)`. -/
lemma klucbFamIndex_of_pullCount'_ne_zero (h0 : pullCount' n h a ≠ 0) :
    klucbFamIndex ρ n h a =
      (ρ a).expFamilyUpper id (empMean' n h a)
        (ENNReal.ofReal (log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount' n h a)) := by
  simp [klucbFamIndex_def, h0]

/-- If the upper confidence levels of the families are finite at finite budgets, then the index of
an arm is `⊤` if and only if the arm has not been pulled yet. -/
lemma klucbFamIndex_eq_top_iff
    (hρ : ∀ a x c, c ≠ ⊤ → (ρ a).expFamilyUpper id x c ≠ ⊤) :
    klucbFamIndex ρ n h a = ⊤ ↔ pullCount' n h a = 0 := by
  by_cases h0 : pullCount' n h a = 0
  · simp [h0]
  · simpa [klucbFamIndex_of_pullCount'_ne_zero h0, h0] using hρ _ _ _ ENNReal.ofReal_ne_top

@[fun_prop]
lemma measurable_klucbFamIndex [MeasurableSpace α] [MeasurableSingletonClass α]
    (ρ : α → Measure ℝ) (n : ℕ) : Measurable (klucbFamIndex ρ n) := by
  refine Measurable.of_eval fun a ↦ ?_
  simp_rw [klucbFamIndex_def]
  refine Measurable.ite ?_ measurable_const (by fun_prop)
  exact (measurableSet_singleton 0).preimage (measurable_pullCount' n a)

/-- Along a sequence of rounds `(O, A, R)`, the index of an arm at round `n` is `⊤` if the arm has
not been pulled before `n`, and otherwise `U_{ρ a}(μ̂_a, log f(n + 1) / T_a)` for the number of
pulls `T_a = pullCount A a n ω` and the empirical mean `μ̂_a = empMean A R a n ω`. -/
lemma klucbFamIndex_history {Ω : Type*} (O : ℕ → Ω → Unit) (A : ℕ → Ω → α) (R : ℕ → Ω → ℝ)
    (ρ : α → Measure ℝ) (n : ℕ) (ω : Ω) (a : α) :
    klucbFamIndex ρ n (history O A R n ω) a = if pullCount A a n ω = 0 then ⊤ else
      (ρ a).expFamilyUpper id (empMean A R a n ω)
        (ENNReal.ofReal (log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount A a n ω)) := by
  rw [klucbFamIndex_def, ← pullCount_eq_pullCount', ← empMean_eq_empMean']

end FamilyIndex

section Index

variable {α : Type*} [DecidableEq α] {n : ℕ} {h : Hist Unit α ℝ n} {a : α}

/-- The index of the KL-UCB algorithm [LS, Algorithm 8] at Lean round `n` (book round `n + 1`),
for the history `h` of the first `n` rounds: `⊤` if the arm `a` has not been pulled, and otherwise
the upper confidence level `U(μ̂_a, log f(n + 1) / T_a)` with `f(t) = 1 + t log² t`, where `T_a` is
the number of pulls of `a` and `μ̂_a` its empirical mean. -/
noncomputable def klucbIndex (n : ℕ) (h : Hist Unit α ℝ n) (a : α) : EReal :=
  if pullCount' n h a = 0 then ⊤ else
    ((klUpper (empMean' n h a)
      (ENNReal.ofReal (log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount' n h a)) : ℝ) : EReal)

/-- The defining equation of `klucbIndex`. -/
lemma klucbIndex_def (n : ℕ) (h : Hist Unit α ℝ n) (a : α) :
    klucbIndex n h a = if pullCount' n h a = 0 then ⊤ else
      ((klUpper (empMean' n h a)
        (ENNReal.ofReal (log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount' n h a)) : ℝ) : EReal) :=
  (rfl)

/-- An arm that has not been pulled has index `⊤`. -/
@[simp]
lemma klucbIndex_of_pullCount'_eq_zero (h0 : pullCount' n h a = 0) : klucbIndex n h a = ⊤ := by
  simp [klucbIndex_def, h0]

/-- The index of an arm that has been pulled is `U(μ̂_a, log f(n + 1) / T_a)`. -/
lemma klucbIndex_of_pullCount'_ne_zero (h0 : pullCount' n h a ≠ 0) :
    klucbIndex n h a =
      ((klUpper (empMean' n h a)
        (ENNReal.ofReal (log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount' n h a)) : ℝ) :
          EReal) := by
  simp [klucbIndex_def, h0]

/-- At an empirical mean in `[0, 1]`, the KL-UCB index of the Bernoulli family on every arm is the
index `U(μ̂_a, log f(n + 1) / T_a)` of [LS, Algorithm 8]. The Bernoulli family is generated by any
of its members `Ber((1 : ℝ), 0, sigmoid η₀)`. -/
theorem klucbFamIndex_bernoulliMeasure_sigmoid (η₀ : ℝ) (hμ : empMean' n h a ∈ Set.Icc 0 1) :
    klucbFamIndex (fun _ ↦ Ber((1 : ℝ), 0, unitInterval.sigmoid η₀)) n h a = klucbIndex n h a := by
  by_cases h0 : pullCount' n h a = 0
  · simp [h0]
  · rw [klucbFamIndex_of_pullCount'_ne_zero h0, klucbIndex_of_pullCount'_ne_zero h0,
      expFamilyUpper_bernoulliMeasure_sigmoid η₀ hμ]

end Index

section Algorithm

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- The KL-UCB algorithm for the exponential families `ρ a` of real rewards [LS, Algorithm 8;
GC11, Section 4; CGMMS13]: the index policy with index `klucbFamIndex ρ`, which plays at round `n`
an arm of maximal index, ties being broken by LML's `argmax`. Each arm `a` has its own family, the
exponential family of `ρ a` with the identity statistic. -/
noncomputable def klucbFam (ρ : α → Measure ℝ) : Algorithm Unit α ℝ :=
  indexAlgorithm (fun n x ↦ klucbFamIndex ρ n x.1)
    fun n ↦ (measurable_klucbFamIndex ρ n).comp measurable_fst

/-- The KL-UCB algorithm for the families `ρ` is the index policy with index `klucbFamIndex ρ`. -/
lemma klucbFam_def (ρ : α → Measure ℝ) :
    klucbFam ρ =
      indexAlgorithm (fun n x ↦ klucbFamIndex ρ n x.1)
        fun n ↦ (measurable_klucbFamIndex ρ n).comp measurable_fst :=
  (rfl)

/-- The asymptotically optimal UCB algorithm `ucbF σ2` [LS, Algorithm 6] is the KL-UCB algorithm
for the Gaussian family of variance `σ2 ≠ 0` on every arm, generated by any of its members
`𝒩(m, σ2)`. -/
theorem klucbFam_gaussianReal (m : ℝ) {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0) :
    klucbFam (fun _ : α ↦ gaussianReal m σ2) = ucbF σ2 := by
  have h_index (n : ℕ) (h : Hist Unit α ℝ n) (a : α) :
      klucbFamIndex (fun _ ↦ gaussianReal m σ2) n h a = ucbFIndex σ2 n h a := by
    by_cases h0 : pullCount' n h a = 0
    · simp [h0]
    have hL : 0 ≤ log (1 + (n + 1) * log (n + 1) ^ 2) / pullCount' n h a :=
      div_nonneg (log_nonneg (by nlinarith [sq_nonneg (log (n + 1))])) (Nat.cast_nonneg _)
    rw [klucbFamIndex_of_pullCount'_ne_zero h0, ucbFIndex_of_pullCount'_ne_zero h0,
      expFamilyUpper_ofReal_gaussianReal m hσ2 _ hL, mul_div_assoc]
  rw [klucbFam_def, ucbF_def]
  congr 1
  exact funext fun n ↦ funext fun x ↦ funext (h_index n x.1)

/-- The KL-UCB algorithm [LS, Algorithm 8] for rewards in `[0, 1]`: the KL-UCB algorithm for the
Bernoulli family on every arm, generated by the fair coin `Ber((1 : ℝ), 0, sigmoid 0)`. At
empirical means in `[0, 1]`, its index is the index `klucbIndex` of [LS, Algorithm 8]
(`klucbFamIndex_bernoulliMeasure_sigmoid`). -/
noncomputable def klucb : Algorithm Unit α ℝ :=
  klucbFam fun _ ↦ Ber((1 : ℝ), 0, unitInterval.sigmoid 0)

/-- The KL-UCB algorithm for rewards in `[0, 1]` is the KL-UCB algorithm for the Bernoulli
family. -/
lemma klucb_def : klucb (α := α) = klucbFam fun _ ↦ Ber((1 : ℝ), 0, unitInterval.sigmoid 0) :=
  (rfl)

namespace KLUCBFam

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {env : Environment Unit α ℝ} {ρ : α → Measure ℝ}
  {P : Measure Ω} [IsFiniteMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- If the upper confidence levels of the families are finite at finite budgets, the KL-UCB
algorithm pulls every arm exactly once during the first `Fintype.card α` rounds. -/
lemma pullCount_card_eq_one (h : IsAlgEnvSeq O A R (klucbFam ρ) env P)
    (hρ : ∀ a x c, c ≠ ⊤ → (ρ a).expFamilyUpper id x c ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ a, pullCount A a (Fintype.card α) ω = 1 := by
  rw [klucbFam_def] at h
  exact IndexAlgorithm.pullCount_card_eq_one h fun _ _ _ ↦ klucbFamIndex_eq_top_iff hρ

/-- The decomposition of the expected number of pulls of an arm `a` by the KL-UCB algorithm for
the families `ρ`, as in the proofs of [LS, Theorem 10.6; GC11; CGMMS13]. For every arm `b`
(typically an optimal arm) and every mean `c` of the family of `a` (typically `μ* - ε`),
`E[T_a(n)]` is at most the sum over the rounds `t < n` of the probabilities that `b` has been
pulled with index `U_{ρ b}(μ̂_b, log f(t + 1) / T_b)` at most `c`, plus the sum over `t < n` of the
probabilities that `a` is played at round `t` while either it has not been pulled yet, or
`c ≤ μ̂_a`, or `dbar_{ρ a}(μ̂_a, c) ≤ log f(n) / T_a`. The exploration level `log f(t + 1)` of
round `t` is bounded by that of the horizon `n` in the second sum, so that the event only depends
on `T_a` and `μ̂_a`. -/
theorem integral_pullCount_le_sum_add_sum (h : IsAlgEnvSeq O A R (klucbFam ρ) env P) (a b : α)
    {c : ℝ} (hc : c ∈ (ρ a).expFamilyMeans id) (n : ℕ) :
    ∫ ω, (pullCount A a n ω : ℝ) ∂P ≤
      ∑ t ∈ range n, P.real {ω | pullCount A b t ω ≠ 0 ∧
        (ρ b).expFamilyUpper id (empMean A R b t ω)
          (ENNReal.ofReal (log (1 + (t + 1) * log (t + 1) ^ 2) / pullCount A b t ω)) ≤ c} +
      ∑ t ∈ range n, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨ c ≤ empMean A R a t ω ∨
        (ρ a).expFamilyRate id (empMean A R a t ω) c ≤
          ENNReal.ofReal (log (1 + n * log n ^ 2) / pullCount A a t ω))} := by
  rw [klucbFam_def] at h
  refine (IndexAlgorithm.integral_pullCount_le_sum_add_sum h a b c n).trans
    (add_le_add (sum_le_sum fun t _ ↦ le_of_eq ?_) (sum_le_sum fun t ht ↦ measureReal_mono ?_))
  · simp only [klucbFamIndex_history, apply_ite (· ≤ (c : EReal)), top_le_iff, EReal.coe_ne_top,
      ite_false_left, ne_eq]
  · -- The exploration level `log f(t + 1)` of round `t < n` is at most `log f(n)`.
    have htn : t + 1 ≤ n := mem_range.mp ht
    have hlog : log (1 + (t + 1) * log (t + 1) ^ 2) ≤ log (1 + n * log n ^ 2) :=
      monotoneOn_log_one_add_mul_log_sq (by simp) (Nat.one_le_cast.2 (by omega))
        (by exact_mod_cast htn)
    intro ω hω
    simp only [Set.mem_ofPred_eq, klucbFamIndex_history] at hω ⊢
    refine ⟨hω.1, ?_⟩
    split_ifs at hω with h0
    · exact Or.inl h0
    · refine Or.inr (Measure.le_or_expFamilyRate_le_of_lt_expFamilyUpper hc (hω.2.trans_le ?_))
      exact Measure.monotone_expFamilyUpper _ _ _ (ENNReal.ofReal_le_ofReal (by gcongr))

end KLUCBFam

namespace KLUCB

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {env : Environment Unit α ℝ}
  {P : Measure Ω} [IsFiniteMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- The KL-UCB algorithm pulls every arm exactly once during the first `Fintype.card α`
rounds. -/
lemma pullCount_card_eq_one (h : IsAlgEnvSeq O A R klucb env P) :
    ∀ᵐ ω ∂P, ∀ a, pullCount A a (Fintype.card α) ω = 1 := by
  rw [klucb_def] at h
  refine KLUCBFam.pullCount_card_eq_one h fun _ _ _ _ ↦
    Measure.expFamilyUpper_ne_top_of_bddAbove ?_
  rw [expFamilyMeans_bernoulliMeasure_sigmoid]
  exact bddAbove_Ioo

/-- The decomposition of the expected number of pulls of an arm `a` by the KL-UCB algorithm for
rewards in `[0, 1]`, in the proof of [LS, Theorem 10.6]. For every arm `b` (typically an optimal
arm) and every threshold `c ∈ (0, 1)` (typically `μ* - ε`), `E[T_a(n)]` is at most the sum over
the rounds `t < n` of the probabilities that `b` has been pulled with index
`U(μ̂_b, log f(t + 1) / T_b)` at most `c`, plus the sum over `t < n` of the probabilities that `a`
is played at round `t` while either it has not been pulled yet, or `c ≤ μ̂_a`, or
`d(μ̂_a, c) ≤ log f(n) / T_a`. This is `KLUCBFam.integral_pullCount_le_sum_add_sum` for the
Bernoulli family, whose confidence levels and divergences are `klUpper` and `klBer` at the
empirical means, which lie in `[0, 1]`. -/
theorem integral_pullCount_le_sum_add_sum (h : IsAlgEnvSeq O A R klucb env P)
    (hR : ∀ᵐ ω ∂P, ∀ t, R t ω ∈ Set.Icc 0 1) (a b : α) {c : ℝ} (hc : c ∈ Set.Ioo 0 1)
    (n : ℕ) :
    ∫ ω, (pullCount A a n ω : ℝ) ∂P ≤
      ∑ t ∈ range n, P.real {ω | pullCount A b t ω ≠ 0 ∧
        klUpper (empMean A R b t ω)
          (ENNReal.ofReal (log (1 + (t + 1) * log (t + 1) ^ 2) / pullCount A b t ω)) ≤ c} +
      ∑ t ∈ range n, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨ c ≤ empMean A R a t ω ∨
        klBer (empMean A R a t ω) c ≤
          ENNReal.ofReal (log (1 + n * log n ^ 2) / pullCount A a t ω))} := by
  rw [klucb_def] at h
  have hc' : c ∈ Ber((1 : ℝ), 0, unitInterval.sigmoid 0).expFamilyMeans id := by
    rwa [expFamilyMeans_bernoulliMeasure_sigmoid]
  -- Almost surely, every empirical mean lies in `[0, 1]`.
  have hμ : ∀ᵐ ω ∂P, ∀ b t, empMean A R b t ω ∈ Set.Icc 0 1 := by
    filter_upwards [hR] with ω hω b t
    by_cases h0 : pullCount A b t ω = 0
    · simp [empMean, h0]
    · exact empMean_mem_Icc (fun s _ ↦ hω s) h0
  refine (KLUCBFam.integral_pullCount_le_sum_add_sum h a b hc' n).trans_eq
    (congrArg₂ (· + ·) (sum_congr rfl fun t _ ↦ measureReal_congr ?_)
      (sum_congr rfl fun t _ ↦ measureReal_congr ?_))
  · filter_upwards [hμ] with ω hω
    simp only [expFamilyUpper_bernoulliMeasure_sigmoid 0 (hω b t), EReal.coe_le_coe_iff]
  · filter_upwards [hμ] with ω hω
    simp only [expFamilyRate_bernoulliMeasure_sigmoid 0 (hω a t) hc]

end KLUCB

end Algorithm

section Regret

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {ν : Kernel α ℝ} [IsMarkovKernel ν]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- **[LS, Theorem 10.6], number of pulls.** For rewards in `[0, 1]`, the KL-UCB algorithm pulls
an arm `a` with gap `Δ_a` at most
`log f(n) / d(μ_a + ε₁, μ* - ε₂) + 1 / (2 ε₁²) + 2 / ε₂²` times in expectation during the first
`n` rounds, for all `ε₁, ε₂ > 0` with `ε₁ + ε₂ < Δ_a`, where `μ_a` is the mean of `a`, `μ*` the
largest mean and `f(n) = 1 + n log² n`. -/
theorem KLUCB.integral_pullCount_le (h : IsAlgEnvSeq O A R klucb (Environment.bandit ν) P)
    (hν : ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1) (a : α) {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (hε : ε₁ + ε₂ < gap ν a) (n : ℕ) :
    P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤
      log (1 + n * log n ^ 2) / klBerReal ((ν a)[id] + ε₁) ((ν (bestArm ν))[id] - ε₂) +
        1 / (2 * ε₁ ^ 2) + 2 / ε₂ ^ 2 := by
  set μs := (ν (bestArm ν))[id] with hμs
  set L := log (1 + n * log n ^ 2) with hL
  have hL0 : 0 ≤ L := log_nonneg (by linarith [(by positivity : (0 : ℝ) ≤ n * log n ^ 2)])
  have hgap : gap ν a = μs - (ν a)[id] := gap_eq_bestArm_sub
  -- the means lie in `[0, 1]`, so that `ε₂ < Δ_a ≤ 1`
  have hμ (b : α) : (ν b)[id] ∈ Set.Icc 0 1 := integral_id_mem_Icc_of_ae_mem_Icc (hν b)
  have hμs1 : μs ≤ 1 := (hμ (bestArm ν)).2
  have hε₂1 : ε₂ < 1 := by linarith [(hμ a).1]
  calc P[fun ω ↦ (pullCount A a n ω : ℝ)]
  _ ≤ ∑ t ∈ range n, P.real {ω | pullCount A (bestArm ν) t ω ≠ 0 ∧
        klUpper (empMean A R (bestArm ν) t ω)
          (ENNReal.ofReal (log (1 + (t + 1) * log (t + 1) ^ 2) / pullCount A (bestArm ν) t ω)) ≤
            μs - ε₂} +
      ∑ t ∈ range n, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨
        μs - ε₂ ≤ empMean A R a t ω ∨
          klBer (empMean A R a t ω) (μs - ε₂) ≤ ENNReal.ofReal (L / pullCount A a t ω))} :=
    KLUCB.integral_pullCount_le_sum_add_sum h (h.ae_forall_feedback_mem_bandit measurableSet_Icc hν)
      a (bestArm ν) ⟨by linarith [(hμ a).1], by linarith⟩ n
  _ ≤ 3 / (4 * ε₂ ^ 2) + (1 + L / klBerReal ((ν a)[id] + ε₁) (μs - ε₂) + 1 / (2 * ε₁ ^ 2)) :=
    add_le_add (sum_measureReal_pullCount_ne_zero_and_klUpper_le_le h (bestArm ν) (hν _) hε₂ n)
      (sum_measureReal_action_eq_and_pullCount_eq_zero_or_le_empMean_or_klBer_le_le h a (hν a)
        hε₁ (by linarith) (by linarith) hL0 n)
  _ ≤ L / klBerReal ((ν a)[id] + ε₁) (μs - ε₂) + 1 / (2 * ε₁ ^ 2) + 2 / ε₂ ^ 2 := by
    -- `1 + 3 / (4 ε₂²) ≤ 2 / ε₂²` since `ε₂ < 1`
    have h1 : 1 ≤ 5 / (4 * ε₂ ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h2 : 3 / (4 * ε₂ ^ 2) + 5 / (4 * ε₂ ^ 2) = 2 / ε₂ ^ 2 := by
      field_simp
      ring
    linarith

/-- **[LS, Theorem 10.6]** For rewards in `[0, 1]`, the expected regret of the KL-UCB algorithm at
horizon `n` is at most the sum over the arms `a` with positive gap `Δ_a` of
`inf_{ε₁, ε₂ > 0, ε₁ + ε₂ < Δ_a} Δ_a (log f(n) / d(μ_a + ε₁, μ* - ε₂) + 1 / (2 ε₁²) + 2 / ε₂²)`,
where `μ_a` is the mean of `a`, `μ*` the largest mean and `f(n) = 1 + n log² n`. -/
theorem klucb_regret_le
    (h : IsAlgEnvSeq O A R klucb (Environment.bandit ν) P) (hν : ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    (n : ℕ) :
    P[regret ν A n] ≤ ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
      ⨅ ε₁ : Set.Ioo 0 (gap ν a), ⨅ ε₂ : Set.Ioo 0 (gap ν a - ε₁),
        gap ν a * (log (1 + n * log n ^ 2) /
          klBerReal ((ν a)[id] + ε₁) ((ν (bestArm ν))[id] - ε₂) +
            1 / (2 * (ε₁ : ℝ) ^ 2) + 2 / (ε₂ : ℝ) ^ 2) := by
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount h.measurable_action,
    ← sum_filter_of_ne fun a _ ha ↦ gap_nonneg.lt_of_ne' (left_ne_zero_of_mul ha)]
  refine sum_le_sum fun a ha ↦ ?_
  have : Nonempty (Set.Ioo 0 (gap ν a)) := (Set.nonempty_Ioo.mpr (mem_filter.mp ha).2).to_subtype
  refine le_ciInf fun ε₁ ↦ ?_
  have : Nonempty (Set.Ioo 0 (gap ν a - ε₁)) :=
    (Set.nonempty_Ioo.mpr (sub_pos.mpr ε₁.2.2)).to_subtype
  exact le_ciInf fun ε₂ ↦ mul_le_mul_of_nonneg_left
    (KLUCB.integral_pullCount_le h hν a ε₁.2.1 ε₂.2.1 (by linarith [ε₂.2.2]) n) gap_nonneg

/-- **Asymptotic number of pulls of KL-UCB.** For rewards in `[0, 1]`, an arm `a` with positive gap
and every `c > 1 / d(μ_a, μ*)`, where `μ_a` is the mean of `a` and `μ*` the largest mean, the
expected number of pulls of `a` by the KL-UCB algorithm during the first `n` rounds is eventually
at most `c log n`; that is, `limsup_n E[T_a(n)] / log n ≤ 1 / d(μ_a, μ*)`. Here `1 / d(μ_a, μ*)` is
`(klBer μ_a μ*).toReal⁻¹`, which is `0` when `d(μ_a, μ*) = ∞`. -/
theorem KLUCB.integral_pullCount_eventually_le
    (h : IsAlgEnvSeq O A R klucb (Environment.bandit ν) P)
    (hν : ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1) (a : α) (ha : 0 < gap ν a) {c : ℝ}
    (hc : (klBer (ν a)[id] (ν (bestArm ν))[id]).toReal⁻¹ < c) :
    ∀ᶠ n : ℕ in atTop, P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤ c * log n := by
  set μa := (ν a)[id]
  set μs := (ν (bestArm ν))[id]
  have hgap : gap ν a = μs - μa := gap_eq_bestArm_sub
  -- the means lie in `[0, 1]`
  have hμ (b : α) : (ν b)[id] ∈ Set.Icc 0 1 := integral_id_mem_Icc_of_ae_mem_Icc (hν b)
  have hc0 : 0 < c := (inv_nonneg.mpr ENNReal.toReal_nonneg).trans_lt hc
  -- `c⁻¹ < d(μ_a, μ*)`, also when `d(μ_a, μ*) = ∞`
  have hlt : ENNReal.ofReal c⁻¹ < klBer μa μs := by
    by_cases htop : klBer μa μs = ∞
    · simp [htop]
    have hpos : 0 < (klBer μa μs).toReal := ENNReal.toReal_pos
      (fun h0 ↦ by linarith [(klBer_eq_zero_iff (hμ a) (hμ _)).mp h0]) htop
    exact (ENNReal.ofReal_lt_iff_lt_toReal (inv_nonneg.mpr hc0.le) htop).mpr
      (inv_lt_of_inv_lt₀ hpos hc)
  -- Choose `ε ∈ (0, Δ_a / 2)` with `c⁻¹ < d(μ_a + ε, μ* - ε)`, by lower semicontinuity of `d`.
  have h_tendsto : Tendsto (fun ε : ℝ ↦ (μa + ε, μs - ε)) (𝓝[>] 0) (𝓝 (μa, μs)) := by
    have : Continuous fun ε : ℝ ↦ (μa + ε, μs - ε) := by fun_prop
    simpa using (this.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hεd, hε, hεa⟩ := (h_tendsto.eventually (lowerSemicontinuous_klBer (μa, μs) _ hlt)).and
    (Ioo_mem_nhdsGT (half_pos ha)) |>.exists
  simp only [Function.uncurry_apply_pair] at hεd
  set D := klBerReal (μa + ε) (μs - ε)
  have hp : μa + ε ∈ Set.Icc 0 1 := ⟨by linarith [(hμ a).1], by linarith [(hμ (bestArm ν)).2]⟩
  have hq : μs - ε ∈ Set.Ioo 0 1 := ⟨by linarith [(hμ a).1], by linarith [(hμ (bestArm ν)).2]⟩
  rw [klBer_eq_ofReal_klBerReal hp (Set.Ioo_subset_Icc_self hq) (klBer_ne_top hq), gt_iff_lt,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (inv_nonneg.mpr hc0.le)] at hεd
  have hDc : D⁻¹ < c := inv_lt_of_inv_lt₀ hc0 hεd
  -- The bound of `KLUCB.integral_pullCount_le` divided by `log n` tends to `D⁻¹`.
  set K := 1 / (2 * ε ^ 2) + 2 / ε ^ 2
  set L : ℕ → ℝ := fun n ↦ log (1 + n * log n ^ 2)
  have h_bound : Tendsto (fun n : ℕ ↦ (L n / D + K) / log n) atTop (𝓝 D⁻¹) :=
    tendsto_div_add_div_log
      (tendsto_log_one_add_mul_log_sq_div_log_atTop.comp tendsto_natCast_atTop_atTop) D K
  filter_upwards [eventually_lt_mul_log_of_tendsto_div_log h_bound hDc] with n hn
  refine (KLUCB.integral_pullCount_le h hν a hε hε (by linarith) n).trans ?_
  simp only [K, L] at hn
  linarith

/-- **[LS, Theorem 10.6], asymptotic part.** For rewards in `[0, 1]` and every
`c > ∑_{a : Δ_a > 0} Δ_a / d(μ_a, μ*)`, where `μ_a` is the mean of `a` and `μ*` the largest mean,
the expected regret of the KL-UCB algorithm at horizon `n` is eventually at most `c log n`; that
is, `limsup_n E[R_n] / log n ≤ ∑_{a : Δ_a > 0} Δ_a / d(μ_a, μ*)`. Here `Δ_a / d(μ_a, μ*)` is
`Δ_a / (klBer μ_a μ*).toReal`, which is `0` when `d(μ_a, μ*) = ∞`. -/
theorem klucb_regret_eventually_le [StandardBorelSpace α]
    (h : IsAlgEnvSeq O A R klucb (Environment.bandit ν) P) (hν : ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    {c : ℝ} (hc : ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
      gap ν a / (klBer (ν a)[id] (ν (bestArm ν))[id]).toReal < c) :
    ∀ᶠ n : ℕ in atTop, P[regret ν A n] ≤ c * log n :=
  integral_regret_eventually_le_of_forall_integral_pullCount_eventually_le
    h.measurable_action (.of_forall fun n ↦ log_natCast_nonneg n)
    (fun a ↦ (klBer (ν a)[id] (ν (bestArm ν))[id]).toReal⁻¹)
    (fun a ha _ hc ↦ KLUCB.integral_pullCount_eventually_le h hν a ha hc)
    (by simpa only [div_eq_mul_inv] using hc)

/-- For rewards in `[0, 1]` whose largest mean is `1`, the expected regret of the KL-UCB algorithm
is `o(log n)`: for every `c > 0`, eventually `E[R_n] ≤ c log n`. Indeed `d(μ_a, 1) = ∞` for every
arm `a` with positive gap, so that the constant of `klucb_regret_eventually_le` vanishes. -/
theorem klucb_regret_eventually_le_of_integral_bestArm_eq_one [StandardBorelSpace α]
    (h : IsAlgEnvSeq O A R klucb (Environment.bandit ν) P) (hν : ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    (h1 : (ν (bestArm ν))[id] = 1) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, P[regret ν A n] ≤ c * log n := by
  refine klucb_regret_eventually_le h hν (lt_of_eq_of_lt (sum_eq_zero fun a ha ↦ ?_) hc)
  have hμ : (ν a)[id] ∈ Set.Icc 0 1 := integral_id_mem_Icc_of_ae_mem_Icc (hν a)
  have hlt : (ν a)[id] < 1 := by
    have := (mem_filter.mp ha).2
    rw [gap_eq_bestArm_sub, h1] at this
    linarith
  rw [h1, (klBer_eq_top_iff hμ (by simp)).mpr (Or.inr ⟨rfl, hlt.ne⟩), ENNReal.toReal_top,
    div_zero]

end Regret

section FamilyRegret

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {ν : Kernel α ℝ} [IsMarkovKernel ν] {ρ : α → Measure ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- **Number of pulls of KL-UCB for exponential families** [GC11, Section 4;
CGMMS13]. Let `a` and `b` be two arms with means `μ_a < μ_b`, each lying in the interval of means
of its own family, the law of `a` being dominated on `Set.Ici 0` by the member of mean `μ_a` of the
family `ρ a` and the law of `b` dominated on `Set.Iic 0` by the member of mean `μ_b` of `ρ b`. For
`ε₁, ε₂ > 0` with `μ_a + ε₁ < μ_b - ε₂`, `μ_a + ε₁` and `μ_b - ε₂` means of `ρ a` and `μ_b - ε₂` a
mean of `ρ b`, the KL-UCB algorithm for the families `ρ` pulls `a` at most
`1 + log f(n) / d_{ρ a}(μ_a + ε₁, μ_b - ε₂) + 1 / d_{ρ a}(μ_a + ε₁, μ_a) +
3 / (2 d_{ρ b}(μ_b - ε₂, μ_b))` times in expectation during the first `n` rounds, where
`f(n) = 1 + n log² n`. The arm `b` is typically an optimal arm. -/
theorem KLUCBFam.integral_pullCount_le
    (h : IsAlgEnvSeq O A R (klucbFam ρ) (Environment.bandit ν) P) {a b : α}
    (ha : (ν a)[id] ∈ (ρ a).expFamilyMeans id)
    (hνa : MGFDominatedOn id (ν a) id ((ρ a).expFamily id ((ρ a).natParam id (ν a)[id]))
      (Set.Ici 0))
    (hb : (ν b)[id] ∈ (ρ b).expFamilyMeans id)
    (hνb : MGFDominatedOn id (ν b) id ((ρ b).expFamily id ((ρ b).natParam id (ν b)[id]))
      (Set.Iic 0))
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hε : (ν a)[id] + ε₁ < (ν b)[id] - ε₂)
    (ha₁ : (ν a)[id] + ε₁ ∈ (ρ a).expFamilyMeans id)
    (ha₂ : (ν b)[id] - ε₂ ∈ (ρ a).expFamilyMeans id)
    (hb₂ : (ν b)[id] - ε₂ ∈ (ρ b).expFamilyMeans id) (n : ℕ) :
    P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤
      1 + log (1 + n * log n ^ 2) / (ρ a).expFamilyDiv id ((ν a)[id] + ε₁) ((ν b)[id] - ε₂) +
        1 / (ρ a).expFamilyDiv id ((ν a)[id] + ε₁) (ν a)[id] +
          3 / (2 * (ρ b).expFamilyDiv id ((ν b)[id] - ε₂) (ν b)[id]) := by
  have hL0 : 0 ≤ log (1 + n * log n ^ 2) :=
    log_nonneg (by linarith [(by positivity : (0 : ℝ) ≤ n * log n ^ 2)])
  -- the underestimation of `b` and the overestimation of `a` in the decomposition of
  -- `KLUCBFam.integral_pullCount_le_sum_add_sum` at the threshold `μ_b - ε₂`
  refine (KLUCBFam.integral_pullCount_le_sum_add_sum h a b ha₂ n).trans ?_
  refine (add_le_add
    (sum_measureReal_pullCount_ne_zero_and_expFamilyUpper_le_le h b hνb hb hε₂ hb₂ n)
    (sum_measureReal_action_eq_and_pullCount_eq_zero_or_le_empMean_or_expFamilyRate_le_le h a
      hνa ha hε₁ hε ha₁ ha₂ hL0 n)).trans_eq ?_
  ring

/-- **Regret of KL-UCB for exponential families** [GC11, Section 4; CGMMS13]. Let the
mean `μ_a` of every arm `a` with positive gap lie in the interval of means of its family `ρ a`
and its law be dominated on `Set.Ici 0` by the member of mean `μ_a` of `ρ a`, and let the mean `μ*`
of the optimal arm `a*` be a mean of `ρ a*` and its law be dominated on `Set.Iic 0` by the member
of mean `μ*` of `ρ a*`. For every arm `a` with
positive gap `Δ_a`, let `ε₁ a, ε₂ a > 0` with `ε₁ a + ε₂ a < Δ_a`, `μ_a + ε₁ a` and `μ* - ε₂ a`
means of `ρ a` and `μ* - ε₂ a` a mean of `ρ a*`. Then the expected regret of the KL-UCB algorithm
for the families `ρ` at horizon `n` is at most the sum over the arms `a` with positive gap of
`Δ_a (1 + log f(n) / d_{ρ a}(μ_a + ε₁ a, μ* - ε₂ a) + 1 / d_{ρ a}(μ_a + ε₁ a, μ_a) +
3 / (2 d_{ρ a*}(μ* - ε₂ a, μ*)))`, where `f(n) = 1 + n log² n`. -/
theorem klucbFam_regret_le
    (h : IsAlgEnvSeq O A R (klucbFam ρ) (Environment.bandit ν) P)
    (hμ : ∀ a, 0 < gap ν a → (ν a)[id] ∈ (ρ a).expFamilyMeans id)
    (hs : (ν (bestArm ν))[id] ∈ (ρ (bestArm ν)).expFamilyMeans id)
    (hν : ∀ a, 0 < gap ν a →
      MGFDominatedOn id (ν a) id ((ρ a).expFamily id ((ρ a).natParam id (ν a)[id])) (Set.Ici 0))
    (hνs : MGFDominatedOn id (ν (bestArm ν)) id ((ρ (bestArm ν)).expFamily id
      ((ρ (bestArm ν)).natParam id (ν (bestArm ν))[id])) (Set.Iic 0))
    {ε₁ ε₂ : α → ℝ} (hε₁ : ∀ a, 0 < gap ν a → 0 < ε₁ a) (hε₂ : ∀ a, 0 < gap ν a → 0 < ε₂ a)
    (hε : ∀ a, 0 < gap ν a → ε₁ a + ε₂ a < gap ν a)
    (ha₁ : ∀ a, 0 < gap ν a → (ν a)[id] + ε₁ a ∈ (ρ a).expFamilyMeans id)
    (ha₂ : ∀ a, 0 < gap ν a → (ν (bestArm ν))[id] - ε₂ a ∈ (ρ a).expFamilyMeans id)
    (hs₂ : ∀ a, 0 < gap ν a → (ν (bestArm ν))[id] - ε₂ a ∈ (ρ (bestArm ν)).expFamilyMeans id)
    (n : ℕ) :
    P[regret ν A n] ≤ ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a), gap ν a *
      (1 + log (1 + n * log n ^ 2) /
          (ρ a).expFamilyDiv id ((ν a)[id] + ε₁ a) ((ν (bestArm ν))[id] - ε₂ a) +
        1 / (ρ a).expFamilyDiv id ((ν a)[id] + ε₁ a) (ν a)[id] +
          3 / (2 * (ρ (bestArm ν)).expFamilyDiv id ((ν (bestArm ν))[id] - ε₂ a)
            (ν (bestArm ν))[id])) := by
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount h.measurable_action,
    ← sum_filter_of_ne fun a _ ha ↦ gap_nonneg.lt_of_ne' (left_ne_zero_of_mul ha)]
  refine sum_le_sum fun a ha ↦ mul_le_mul_of_nonneg_left ?_ gap_nonneg
  have hga := (mem_filter.mp ha).2
  have hgap : gap ν a = (ν (bestArm ν))[id] - (ν a)[id] := gap_eq_bestArm_sub
  exact KLUCBFam.integral_pullCount_le h (hμ a hga) (hν a hga) hs hνs (hε₁ a hga) (hε₂ a hga)
    (by linarith [hε a hga]) (ha₁ a hga) (ha₂ a hga) (hs₂ a hga) n

/-- **Asymptotic number of pulls of KL-UCB for exponential families** [GC11, Section 4;
CGMMS13]. Let `a` and `b` be two arms with means `μ_a < μ_b` and families `ρ a`, `ρ b`, with
`μ_a` and `μ_b` means of `ρ a`, `μ_b` a mean of `ρ b`, and the statistic of `ρ b` not almost
everywhere constant. If the law of `a` is dominated on `Set.Ici 0` by the member of mean `μ_a` of
`ρ a` and the law of `b` is dominated on `Set.Iic 0` by the member of mean `μ_b` of `ρ b`, then
for every `c > 1 / d_{ρ a}(μ_a, μ_b)`, the expected number of pulls of `a` by the KL-UCB algorithm
for the families `ρ` during the first `n` rounds is eventually at most `c log n`; that is,
`limsup_n E[T_a(n)] / log n ≤ 1 / d_{ρ a}(μ_a, μ_b)`. The arm `b` is typically an optimal arm. -/
theorem KLUCBFam.integral_pullCount_eventually_le
    (h : IsAlgEnvSeq O A R (klucbFam ρ) (Environment.bandit ν) P) {a b : α}
    (ha : (ν a)[id] ∈ (ρ a).expFamilyMeans id)
    (hνa : MGFDominatedOn id (ν a) id ((ρ a).expFamily id ((ρ a).natParam id (ν a)[id]))
      (Set.Ici 0))
    (hb : (ν b)[id] ∈ (ρ b).expFamilyMeans id)
    (hνb : MGFDominatedOn id (ν b) id ((ρ b).expFamily id ((ρ b).natParam id (ν b)[id]))
      (Set.Iic 0))
    (hρb : ∀ c, ¬ id =ᵐ[ρ b] fun _ ↦ c) (hab : (ν a)[id] < (ν b)[id])
    (hba : (ν b)[id] ∈ (ρ a).expFamilyMeans id) {c : ℝ}
    (hc : ((ρ a).expFamilyDiv id (ν a)[id] (ν b)[id])⁻¹ < c) :
    ∀ᶠ n : ℕ in atTop, P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤ c * log n := by
  set μa := (ν a)[id]
  set μb := (ν b)[id]
  have hρa := Measure.not_ae_eq_const_of_mem_expFamilyMeans ha hba hab.ne
  have hMa := Measure.isOpen_expFamilyMeans hρa
  have hMb := Measure.isOpen_expFamilyMeans hρb
  have hd0 : 0 < (ρ a).expFamilyDiv id μa μb := Measure.expFamilyDiv_pos ha hba hab.ne
  -- Choose `ε ∈ (0, (μ_b - μ_a) / 2)` small enough that `μ_a + ε` and `μ_b - ε` are means of
  -- `ρ a`, `μ_b - ε` is a mean of `ρ b` and `1 / d_{ρ a}(μ_a + ε, μ_b - ε) < c`, by continuity of
  -- the divergence on the pairs of means.
  have h_tendsto : Tendsto (fun ε : ℝ ↦ (μa + ε, μb - ε)) (𝓝[>] 0) (𝓝 (μa, μb)) := by
    have : Continuous fun ε : ℝ ↦ (μa + ε, μb - ε) := by fun_prop
    simpa using (this.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have h_div : Tendsto (fun ε : ℝ ↦ ((ρ a).expFamilyDiv id (μa + ε) (μb - ε))⁻¹) (𝓝[>] 0)
      (𝓝 ((ρ a).expFamilyDiv id μa μb)⁻¹) :=
    ((((Measure.continuousOn_expFamilyDiv hρa).continuousAt
      ((hMa.prod hMa).mem_nhds ⟨ha, hba⟩)).tendsto.comp h_tendsto).inv₀ hd0.ne')
  obtain ⟨ε, ⟨⟨hεa, hεab⟩, -, hεb⟩, hεd, hε, hε2⟩ :=
    ((h_tendsto.eventually ((hMa.prod hMa).mem_nhds ⟨ha, hba⟩)).and
      (h_tendsto.eventually ((hMa.prod hMb).mem_nhds ⟨ha, hb⟩))).and
    ((h_div.eventually_lt_const hc).and
      (Ioo_mem_nhdsGT (half_pos (sub_pos.mpr hab)))) |>.exists
  -- The bound of `KLUCBFam.integral_pullCount_le` divided by `log n` tends to
  -- `1 / d_{ρ a}(μ_a + ε, μ_b - ε)`.
  set D := (ρ a).expFamilyDiv id (μa + ε) (μb - ε)
  set K := 1 + 1 / (ρ a).expFamilyDiv id (μa + ε) μa +
    3 / (2 * (ρ b).expFamilyDiv id (μb - ε) μb)
  set L : ℕ → ℝ := fun n ↦ log (1 + n * log n ^ 2)
  have h_bound : Tendsto (fun n : ℕ ↦ (L n / D + K) / log n) atTop (𝓝 D⁻¹) :=
    tendsto_div_add_div_log
      (tendsto_log_one_add_mul_log_sq_div_log_atTop.comp tendsto_natCast_atTop_atTop) D K
  filter_upwards [eventually_lt_mul_log_of_tendsto_div_log h_bound hεd] with n hn
  refine (KLUCBFam.integral_pullCount_le h ha hνa hb hνb hε hε (by linarith) hεa hεab hεb
    n).trans ?_
  simp only [K, L] at hn
  linarith

/-- **Asymptotic regret of KL-UCB for exponential families** [GC11, Section 4;
CGMMS13]. Let the mean `μ_a` of every arm `a` with positive gap lie in the interval of means of
its family `ρ a` and its law be dominated on `Set.Ici 0` by the member of mean `μ_a` of `ρ a`, and
let the mean `μ*` of the optimal arm `a*` be a mean of `ρ a*` and its law be dominated on
`Set.Iic 0` by the member of mean `μ*` of `ρ a*`, whose statistic is not almost everywhere
constant. If the largest mean `μ*` is a mean of the family of
every arm with positive gap, then for every `c > ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)`, the
expected regret of the KL-UCB algorithm for the families `ρ` at horizon `n` is eventually at most
`c log n`; that is, `limsup_n E[R_n] / log n ≤ ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)`. -/
theorem klucbFam_regret_eventually_le [StandardBorelSpace α]
    (h : IsAlgEnvSeq O A R (klucbFam ρ) (Environment.bandit ν) P)
    (hμ : ∀ a, 0 < gap ν a → (ν a)[id] ∈ (ρ a).expFamilyMeans id)
    (hs : (ν (bestArm ν))[id] ∈ (ρ (bestArm ν)).expFamilyMeans id)
    (hν : ∀ a, 0 < gap ν a →
      MGFDominatedOn id (ν a) id ((ρ a).expFamily id ((ρ a).natParam id (ν a)[id])) (Set.Ici 0))
    (hνs : MGFDominatedOn id (ν (bestArm ν)) id ((ρ (bestArm ν)).expFamily id
      ((ρ (bestArm ν)).natParam id (ν (bestArm ν))[id])) (Set.Iic 0))
    (hρs : ∀ c, ¬ id =ᵐ[ρ (bestArm ν)] fun _ ↦ c)
    (hμs : ∀ a, 0 < gap ν a → (ν (bestArm ν))[id] ∈ (ρ a).expFamilyMeans id) {c : ℝ}
    (hc : ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
      gap ν a / (ρ a).expFamilyDiv id (ν a)[id] (ν (bestArm ν))[id] < c) :
    ∀ᶠ n : ℕ in atTop, P[regret ν A n] ≤ c * log n :=
  integral_regret_eventually_le_of_forall_integral_pullCount_eventually_le
    h.measurable_action (.of_forall fun n ↦ log_natCast_nonneg n)
    (fun a ↦ ((ρ a).expFamilyDiv id (ν a)[id] (ν (bestArm ν))[id])⁻¹)
    (fun a ha _ hc ↦ KLUCBFam.integral_pullCount_eventually_le h (hμ a ha) (hν a ha) hs hνs hρs
      (by linarith [gap_eq_bestArm_sub (ν := ν) (a := a)]) (hμs a ha) hc)
    (by simpa only [div_eq_mul_inv] using hc)

omit [DecidableEq α] [MeasurableSingletonClass α] [IsMarkovKernel ν] in
/-- For the Gaussian families of variances `σ2 a ≠ 0`, the constant
`∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)` is `∑_{a : Δ_a > 0} 2 σ2_a / Δ_a`, since
`d(μ_a, μ*) = Δ_a² / (2 σ2_a)`. -/
lemma sum_gap_div_expFamilyDiv_gaussianReal (m : α → ℝ) {σ2 : α → ℝ≥0} (hσ2 : ∀ a, σ2 a ≠ 0) :
    ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
      gap ν a / (gaussianReal (m a) (σ2 a)).expFamilyDiv id (ν a)[id] (ν (bestArm ν))[id] =
    ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a), 2 * σ2 a / gap ν a := by
  refine sum_congr rfl fun a ha ↦ ?_
  have hga := (mem_filter.mp ha).2
  have hσ2a : (σ2 a : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 (hσ2 a)
  rw [expFamilyDiv_gaussianReal _ (hσ2 a), ← neg_sub, neg_sq, ← gap_eq_bestArm_sub]
  field_simp

/-- **Asymptotic regret of KL-UCB for Gaussian families with known variances.** Let the rewards
of every arm `a` be `σ2 a`-sub-Gaussian with `σ2 a ≠ 0`. For every
`c > ∑_{a : Δ_a > 0} 2 σ2_a / Δ_a`, the expected regret at horizon `n` of the KL-UCB algorithm for
the Gaussian families of variances `σ2 a`, generated by any members `𝒩(m a, σ2 a)`, is eventually
at most `c log n`; that is, `limsup_n E[R_n] / log n ≤ ∑_{a : Δ_a > 0} 2 σ2_a / Δ_a`. For a
common variance `σ2`, that algorithm is `ucbF σ2` (`klucbFam_gaussianReal`). -/
theorem klucbFam_gaussianReal_regret_eventually_le [StandardBorelSpace α] (m : α → ℝ)
    {σ2 : α → ℝ≥0}
    (h : IsAlgEnvSeq O A R (klucbFam fun a ↦ gaussianReal (m a) (σ2 a)) (Environment.bandit ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) (σ2 a) (ν a)) (hσ2 : ∀ a, σ2 a ≠ 0)
    {c : ℝ} (hc : ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a), 2 * σ2 a / gap ν a < c) :
    ∀ᶠ n : ℕ in atTop, P[regret ν A n] ≤ c * log n := by
  -- every arm is dominated on `ℝ` by the member `𝒩(μ_a, σ2 a)` of its family
  have hdom (a : α) : MGFDominatedOn id (ν a) id ((gaussianReal (m a) (σ2 a)).expFamily id
      ((gaussianReal (m a) (σ2 a)).natParam id (ν a)[id])) Set.univ := by
    rw [expFamily_natParam_gaussianReal (m a) (hσ2 a)]
    exact (hν a).mgfDominatedOn_gaussianReal
  refine klucbFam_regret_eventually_le h (fun a _ ↦ mem_expFamilyMeans_gaussianReal _ (hσ2 a) _)
    (mem_expFamilyMeans_gaussianReal _ (hσ2 _) _) (fun a _ ↦ (hdom a).mono (Set.subset_univ _))
    ((hdom _).mono (Set.subset_univ _))
    (not_ae_eq_const_gaussianReal _ (hσ2 _))
    (fun a _ ↦ mem_expFamilyMeans_gaussianReal _ (hσ2 a) _) ?_
  exact (sum_gap_div_expFamilyDiv_gaussianReal m hσ2).trans_lt hc

end FamilyRegret

end LMLExplore.Bandits
