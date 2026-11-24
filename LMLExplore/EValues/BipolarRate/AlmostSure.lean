/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.EProcess
public import LMLExplore.EValues.EProcess.LevelStoppingTime
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.Analysis.SpecificLimits.Basic
import LMLExplore.EValues.Null.PrefixBet

/-!
# E-processes for an i.i.d. null grow at most at the bipolar rate, almost surely

Let `S₁` be a set of probability measures on `𝓧` (the null) and `Q₁` a law on `𝓧` (the
alternative). The observations are the coordinates of `ℕ → 𝓧`, with the i.i.d. laws
`Measure.infinitePi fun _ ↦ P`. For every sequence of `n`-sample e-variables `M n` for the
i.i.d. null, almost surely under the i.i.d. law of `Q₁`, `M n` evaluated at the first `n`
observations has `limsup (1/n) log (M n) ≤ bipolarRate Q₁ S₁` [EVR26, Note 01]. In particular an
e-process for the i.i.d. null grows almost surely at most at the bipolar rate per observation. The
members of `S₁` are probability measures, and nothing else is assumed on `S₁` or `Q₁`: no
domination, convexity or compactness. Since the bipolar rate is at most the smallest relative
entropy from `Q₁` to the null (`ProbabilityTheory.bipolarRate_le_klInf`), the bound by that
relative entropy follows [WSJ26, Proposition 2.2, for portfolio nulls].

The bound in expectation, `ProbabilityTheory.IsEProcess.eintegral_log_div_le_bipolarRate`
[RR26, Lemma 3.3], holds for each time `n ≠ 0` separately; the almost sure bound is about the
whole trajectory.

Its consequence for sequential tests is the almost sure form of the lower bound on stopping times
[ARR26, Theorem 3.1], with the bipolar rate `d` in place of `KL_inf(Q₁, S₁) ≥ d`: if `τ k` is a
sequential test of level `exp (-k)` for the i.i.d. null, for every `k`, then almost surely
`liminf_k τ k / k ≥ 1 / d`, with no relation between the tests at different levels; and nested
tests `τ α`, with `τ α ≤ τ α'` for `α' ≤ α`, have `liminf_{α → 0} τ α / log (1/α) ≥ 1 / d`. The
lower bound in expectation is `ProbabilityTheory.toENNReal_log_inv_div_bipolarRate_le_lintegral`.

## Main definitions

* `ProbabilityTheory.coverWeight`: the weight `1 / (k (k + 1))` of a block of `k` observations in
  a mixture over block lengths; the weights of `1, 2, …` add up to at most `1`
  (`ProbabilityTheory.sum_coverWeight_le_one`,
  `ProbabilityTheory.tsum_ofReal_coverWeight_succ_le_one`).

## Main statements

* `ProbabilityTheory.ae_limsup_log_div_le_bipolarRate_of_adapted`: the bound for e-variables `F n`
  of the i.i.d. null that are functions of the first `n` observations, that is, adapted to the
  filtration `Filtration.piLT` of the observations.
* `ProbabilityTheory.ae_limsup_log_div_le_bipolarRate`: the bound for `n`-sample e-variables
  evaluated at the first `n` observations.
* `ProbabilityTheory.IsEProcess.ae_limsup_log_div_le_bipolarRate`: the bound for e-processes in the
  filtration `Filtration.piLT` of the observations, per observation seen.
* `ProbabilityTheory.ae_inv_toENNReal_bipolarRate_le_liminf_div`: tests `τ k` of level `exp (-k)`
  have `liminf_k τ k / k ≥ 1 / d` almost surely, and
  `ProbabilityTheory.ae_inv_toENNReal_klInf_le_liminf_div` the same with `KL_inf(Q₁, S₁)`
  [ARR26, Theorem 3.1].
* `ProbabilityTheory.ae_inv_toENNReal_bipolarRate_le_liminf_div_log`: nested tests `τ α` of
  level `α` have `liminf_{α → 0} τ α / log (1/α) ≥ 1 / d` almost surely.

## Implementation notes

Write `d` for the bipolar rate, assume it finite, and let `L > d`. The proof has two steps.

* **Covering.** If, almost surely, `G n ≥ exp (n L')` for infinitely many `n`, where the `G n` are
  functions of the first `n` observations with expectation at most one under the null, then
  `L' ≤ d`. The covering mixture of `N` observations bets half on skipping the first observation
  and half on a block of the first `k` observations, with weight `1 / (k (k + 1))` and the bet
  `G k`, and then continues on the remaining observations. It is a function of the first `N`
  observations with expectation at most one under the null, so its expected logarithm is at most
  `N d`. Parsing the observations greedily, taking a block where some `G k`, `k₀ ≤ k ≤ K`, exceeds
  `exp (k L')` and skipping one observation elsewhere, bounds its logarithm from below by about
  `N (L' - ε)` minus `log 2` times the number of blocks and skips. The skips are at most `K` plus
  the number of positions where the shifted sequence is not good, whose mean is `N` times the
  probability that no `G k` with `k₀ ≤ k ≤ K` exceeds `exp (k L')`, by stationarity; this
  probability tends to `0` as `K → ∞`.
* **Zero-one law.** If `M n ≥ exp (n L)` infinitely often with positive probability, the mixture
  over `s` of `M (n - s)` on the observations after the first `s`, with weights `2⁻¹ ^ (s + 1)`,
  exceeds `exp (n L')` infinitely often, for `d < L' < L`, on an event that contains its preimage
  under the shift. The Bernoulli shift is ergodic (Tau Ceti's
  `MeasureTheory.Measure.ergodic_shift_infinitePi_const`), so this event has probability one, and
  the covering step gives `L' ≤ d`, a contradiction.

For the tests, let `c d < 1` and `ε > 0` small. The mixture
`∑ k, (1 - exp (-ε)) exp (-ε k) exp k 𝟙{τ k ≤ n}` of the bets on the tests is a function of the
first `n` observations with expectation at most one under the null. If `τ k < c k` for infinitely
many `k`, it exceeds `exp ((1 - ε) k)` at the times `⌈c k⌉`, a rate `(1 - ε) / c > d`, which the
almost sure bound excludes. [ARR26] bound instead the probability of `{τ k ≤ c k}` by a change of
measure to a member of the null close to `Q₁` in relative entropy, which gives the bound with
`KL_inf(Q₁, S₁)` only. As in [ARR26, proof of Theorem 3.1], the bounds for the rationals `c` are
intersected, and the nested form follows by comparing `α` with the grid points `exp (-m)`.

The growth bound and its proof are adapted from `EValuesResearch/Results/BipolarRate.lean`
(commit `decbae4`) in the paper project `RemyDegenne/evalues_research` (same author), which
formalizes [EVR26, Note 01], rewritten on the API of LMLExplore.

## References

* [ARR26] S. Agrawal, A. Ram and A. Ramdas, *On stopping times of power-one sequential tests:
  tight lower and upper bounds*, arXiv:2504.19952v2.
* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1.
* [WSJ26] I. Waudby-Smith, R. Sandoval and M. I. Jordan, *Instance-log-optimality of
  portfolio-based e-processes and their sequential hypothesis tests*, arXiv:2504.02818v2.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory Filter
open TauCeti.Probability (shift measurable_shift_iterate)
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-! ### The covering mixture -/

/-- The weight `1 / (k (k + 1))` of a block of `k` observations in the covering mixture. These
weights add up to at most `1`, and their logarithms are `o(k)`. -/
noncomputable def coverWeight (k : ℕ) : ℝ := 1 / ((k : ℝ) * (k + 1))

/-- The definition of the weights of the covering mixture. -/
lemma coverWeight_def (k : ℕ) : coverWeight k = 1 / ((k : ℝ) * (k + 1)) := (rfl)

/-- The weights of the covering mixture are nonnegative. -/
lemma coverWeight_nonneg (k : ℕ) : 0 ≤ coverWeight k := by
  unfold coverWeight
  positivity

/-- The weights of the blocks of lengths `1, …, n` add up to at most `1`. -/
lemma sum_coverWeight_le_one (n : ℕ) :
    ∑ j ∈ Finset.range n, coverWeight (j + 1) ≤ 1 := by
  have h (n : ℕ) : ∑ j ∈ Finset.range n, coverWeight (j + 1) = 1 - 1 / ((n : ℝ) + 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, coverWeight]
      push_cast
      field_simp
      ring
  rw [h]
  have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- The weights of the covering mixture of nonempty blocks are positive. -/
lemma coverWeight_pos {k : ℕ} (hk : 0 < k) : 0 < coverWeight k := by
  rw [coverWeight_def]
  exact one_div_pos.2 (mul_pos (Nat.cast_pos.2 hk) (by positivity))

/-- The weights of the blocks of all lengths `1, 2, …` add up to at most `1`. -/
lemma tsum_ofReal_coverWeight_succ_le_one :
    ∑' k : ℕ, ENNReal.ofReal (coverWeight (k + 1)) ≤ 1 := by
  refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ coverWeight_nonneg _]
  exact ENNReal.ofReal_le_one.2 (sum_coverWeight_le_one n)

/-- The logarithm of the inverse weight of a block is at most `ε` times its length, for long
blocks. -/
private lemma exists_log_inv_coverWeight_le {ε : ℝ} (hε : 0 < ε) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → Real.log ((k : ℝ) * (k + 1)) ≤ ε * k := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1
    (Real.isLittleO_log_id_atTop.bound (c := ε / 4) (by positivity))
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge (max x₀ 1)
  refine ⟨k₀, by exact_mod_cast (le_max_right _ _).trans hk₀, fun k hk ↦ ?_⟩
  have hk' : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := (le_max_right _ _).trans (hk₀.trans hk')
  have hb := hx₀ ((k : ℝ) + 1) (by linarith [le_max_left x₀ 1])
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)), id,
    abs_of_nonneg (by linarith)] at hb
  calc Real.log ((k : ℝ) * (k + 1))
  _ ≤ Real.log (((k : ℝ) + 1) ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
  _ = 2 * Real.log ((k : ℝ) + 1) := by rw [Real.log_pow]; push_cast; ring
  _ ≤ ε * k := by nlinarith

variable {M : ℕ → (ℕ → 𝓧) → ℝ≥0∞}

variable (M) in
/-- The covering mixture of `N` observations: bet half on skipping the first observation and half
on a block of the first `k` observations, `1 ≤ k ≤ N`, with weight `coverWeight k` and the bet
`M k`; then continue on the remaining observations. -/
private noncomputable def coverMixture (N : ℕ) (ω : ℕ → 𝓧) : ℝ≥0∞ :=
  match N with
  | 0 => 1
  | N + 1 => 2⁻¹ * coverMixture N (shift 𝓧 ω) + 2⁻¹ * ∑ j ∈ Finset.range (N + 1),
      ENNReal.ofReal (coverWeight (j + 1)) * M (j + 1) ω *
        coverMixture (N - j) ((shift 𝓧)^[j + 1] ω)
termination_by N
decreasing_by all_goals omega

/-- The covering mixture of no observation is `1`. -/
private lemma coverMixture_zero (ω : ℕ → 𝓧) : coverMixture M 0 ω = 1 := by rw [coverMixture]

/-- The recursive description of the covering mixture. -/
private lemma coverMixture_succ (N : ℕ) (ω : ℕ → 𝓧) :
    coverMixture M (N + 1) ω = 2⁻¹ * coverMixture M N (shift 𝓧 ω) +
      2⁻¹ * ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (coverWeight (j + 1)) * M (j + 1) ω *
        coverMixture M (N - j) ((shift 𝓧)^[j + 1] ω) := by
  rw [coverMixture]

/-- The covering mixture of `N` observations is a function of the first `N` observations. -/
private lemma dependsOn_coverMixture (hM : ∀ n, DependsOn (M n) (Set.Iio n)) (N : ℕ) :
    DependsOn (coverMixture M N) (Set.Iio N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro ω ω' h
    rcases N with _ | N
    · simp only [coverMixture_zero]
    rw [coverMixture_succ, coverMixture_succ,
      ih N N.lt_succ_self (x := shift 𝓧 ω) (y := shift 𝓧 ω') fun i (hi : i < N) ↦ by
        simpa using h (i + 1) (show i + 1 < N + 1 by omega)]
    congr 2
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj : j < N + 1 := Finset.mem_range.1 hj
    simp_rw [mul_assoc]
    exact congrArg _ (dependsOn_mul_comp_shift_iterate (hM (j + 1)) (ih (N - j) (by omega))
      fun i (hi : i < j + 1 + (N - j)) ↦ h i (show i < N + 1 by omega))

/-- The covering mixture is an e-variable for the i.i.d. null when the bets `M k` are e-variables
for it that are functions of the first `k` observations: it is a mixture of skips and of
concatenations of bets. -/
private lemma isEVar_coverMixture {S : Set (Measure 𝓧)} (hM : ∀ n, IsEVar (M n) (iidNull S))
    (hMd : ∀ n, DependsOn (M n) (Set.Iio n)) (N : ℕ) :
    IsEVar (coverMixture M N) (iidNull S) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases N with _ | N
    · rw [funext coverMixture_zero]
      exact isEVar_fun_one (measure_univ_le_one_of_mem_iidNull S)
    have hblocks := isEVar_finsetSum_mul (Finset.range (N + 1))
      (w := fun j ↦ ENNReal.ofReal (coverWeight (j + 1)))
      (fun j hj ↦ (hM (j + 1)).mul_comp_shift_iterate (hMd (j + 1))
        (ih (N - j) (by rw [Finset.mem_range] at hj; omega)))
      (by
        rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ coverWeight_nonneg _]
        exact ENNReal.ofReal_le_one.2 (sum_coverWeight_le_one (N + 1)))
    have h : IsEVar (_ • _ + _ • _) (iidNull S) := convex_isEVar (iidNull S)
      ((ih N N.lt_succ_self).comp_shift_iterate 1) hblocks zero_le zero_le
      ENNReal.inv_two_add_inv_two
    convert h using 1
    funext ω
    simp [coverMixture_succ, mul_assoc]

/-- The covering mixture of `N` observations is at least `2⁻¹ ^ N`. -/
private lemma pow_le_coverMixture (N : ℕ) (ω : ℕ → 𝓧) : 2⁻¹ ^ N ≤ coverMixture M N ω := by
  induction N generalizing ω with
  | zero => simp [coverMixture_zero]
  | succ N ih =>
    rw [coverMixture_succ, pow_succ']
    calc 2⁻¹ * 2⁻¹ ^ N ≤ 2⁻¹ * coverMixture M N (shift 𝓧 ω) := by gcongr; exact ih _
    _ ≤ _ := le_self_add

/-! ### The covering argument -/

variable (M) in
/-- The good event of the covering argument: some bet `M k`, `k₀ ≤ k ≤ K`, is at least
`exp (k L)`. -/
private def goodSet (L : ℝ) (k₀ K : ℕ) : Set (ℕ → 𝓧) :=
  {ω | ∃ k, k₀ ≤ k ∧ k ≤ K ∧ ENNReal.ofReal (Real.exp (k * L)) ≤ M k ω}

/-- The good event is measurable. -/
private lemma measurableSet_goodSet (hM : ∀ n, Measurable (M n)) (L : ℝ) (k₀ K : ℕ) :
    MeasurableSet (goodSet M L k₀ K) := by
  have : goodSet M L k₀ K =
      ⋃ k ∈ Finset.Icc k₀ K, {ω | ENNReal.ofReal (Real.exp (k * L)) ≤ M k ω} := by
    ext ω
    simp [goodSet, and_assoc]
  rw [this]
  exact Finset.measurableSet_biUnion _ fun k _ ↦ measurableSet_le measurable_const (hM k)

/-- The number of positions `s < N` at which the shifted sequence is not in `G`. -/
private noncomputable def badCount (G : Set (ℕ → 𝓧)) (N : ℕ) (ω : ℕ → 𝓧) : ℝ :=
  ∑ s ∈ Finset.range N, Gᶜ.indicator 1 ((shift 𝓧)^[s] ω)

/-- The number of bad positions is nonnegative. -/
private lemma badCount_nonneg (G : Set (ℕ → 𝓧)) (N : ℕ) (ω : ℕ → 𝓧) : 0 ≤ badCount G N ω :=
  Finset.sum_nonneg fun _ _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _

/-- There are at most `N` bad positions among the first `N`. -/
private lemma badCount_le (G : Set (ℕ → 𝓧)) (N : ℕ) (ω : ℕ → 𝓧) : badCount G N ω ≤ N := by
  calc badCount G N ω ≤ ∑ _s ∈ Finset.range N, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ ↦ Set.indicator_le_self' (fun _ _ ↦ zero_le_one) _
  _ = N := by simp

/-- The bad positions among the first `N + 1` are the first one, if it is bad, and the bad
positions of the shifted sequence among the first `N`. -/
private lemma badCount_succ (G : Set (ℕ → 𝓧)) (N : ℕ) (ω : ℕ → 𝓧) :
    badCount G (N + 1) ω = Gᶜ.indicator 1 ω + badCount G N (shift 𝓧 ω) := by
  rw [badCount, Finset.sum_range_succ', badCount, add_comm, Function.iterate_zero_apply]
  simp only [Function.iterate_succ_apply]

/-- The shifted sequence has fewer bad positions. -/
private lemma badCount_shift_le (G : Set (ℕ → 𝓧)) {k N : ℕ} (hk : k ≤ N) (ω : ℕ → 𝓧) :
    badCount G (N - k) ((shift 𝓧)^[k] ω) ≤ badCount G N ω := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, badCount, badCount, Finset.sum_range_add,
    Finset.sum_congr rfl fun x _ ↦ by rw [← Function.iterate_add_apply, Nat.add_comm]]
  exact le_add_of_nonneg_left (badCount_nonneg G k ω)

/-- The number of bad positions is measurable. -/
private lemma measurable_badCount {G : Set (ℕ → 𝓧)} (hG : MeasurableSet G) (N : ℕ) :
    Measurable (badCount G N) :=
  Finset.measurable_fun_sum _ fun s _ ↦
    (measurable_one.indicator hG.compl).comp (measurable_shift_iterate s)

/-- The expected number of bad positions is `N` times the probability of the bad event, by
stationarity. -/
private lemma integral_badCount (Q : Measure 𝓧) [IsProbabilityMeasure Q] {G : Set (ℕ → 𝓧)}
    (hG : MeasurableSet G) (N : ℕ) :
    ∫ ω, badCount G N ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q) =
      N * (Measure.infinitePi (fun _ : ℕ ↦ Q)).real Gᶜ := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q)
  have hm (s : ℕ) : Measurable fun ω ↦ Gᶜ.indicator (1 : (ℕ → 𝓧) → ℝ) ((shift 𝓧)^[s] ω) :=
    (measurable_one.indicator hG.compl).comp (measurable_shift_iterate s)
  have hi (s : ℕ) : Integrable (fun ω ↦ Gᶜ.indicator (1 : (ℕ → 𝓧) → ℝ) ((shift 𝓧)^[s] ω)) μ :=
    .of_bound (hm s).aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ by
      by_cases h : (shift 𝓧)^[s] ω ∈ G <;> simp [Set.indicator, h])
  have he (s : ℕ) : ∫ ω, Gᶜ.indicator (1 : (ℕ → 𝓧) → ℝ) ((shift 𝓧)^[s] ω) ∂μ = μ.real Gᶜ := by
    rw [← integral_map (measurable_shift_iterate s).aemeasurable
      (measurable_one.indicator hG.compl).aestronglyMeasurable,
      (measurePreserving_shift_iterate Q s).map_eq, integral_indicator_one hG.compl]
  simp only [badCount]
  rw [integral_finsetSum _ fun s _ ↦ hi s, Finset.sum_congr rfl fun s _ ↦ he s]
  simp

/-- The exponent of the pointwise covering bound at a good position: taking a block of length
`k ≥ k₀`, of weight `exp (-w)` with `w ≤ ε k`, and of bet at least `exp (k L)`, with a factor
`exp (-l)` for the choice of a block, loses no more than the bound allows. -/
private lemma cover_exponent_le_of_good {L ε k k₀ K n C C' w l : ℝ} (hεL : ε ≤ L) (hl : 0 < l)
    (hk₀ : 0 < k₀) (hkk₀ : k₀ ≤ k) (hw : w ≤ ε * k) (hC : C' ≤ C) :
    (L - ε) * (n + k - K - C) - ((n + k) / k₀ + K + C) * l ≤
      -l + -w + k * L + ((L - ε) * (n - K - C') - (n / k₀ + K + C') * l) := by
  have hq : 1 ≤ k / k₀ := by rwa [le_div_iff₀ hk₀, one_mul]
  have hsplit : (n + k) / k₀ = n / k₀ + k / k₀ := add_div _ _ _
  rw [hsplit]
  nlinarith [mul_nonneg (sub_nonneg.2 hεL) (sub_nonneg.2 hC), mul_nonneg hl.le (sub_nonneg.2 hq),
    mul_nonneg hl.le (sub_nonneg.2 hC)]

/-- The exponent of the pointwise covering bound at a bad position: skipping one observation, with
a factor `exp (-l)`, loses no more than the bound allows. -/
private lemma cover_exponent_le_of_bad {L ε k₀ K n C l : ℝ} (hl : 0 < l) (hk₀ : 0 < k₀) :
    (L - ε) * (n + 1 - K - (1 + C)) - ((n + 1) / k₀ + K + (1 + C)) * l ≤
      -l + ((L - ε) * (n - K - C) - (n / k₀ + K + C) * l) := by
  have h : (n + 1) / k₀ = n / k₀ + 1 / k₀ := add_div _ _ _
  have h1k : 0 ≤ 1 / k₀ := by positivity
  rw [h]
  nlinarith [mul_nonneg hl.le h1k]

/-- **The covering argument, pointwise.** Parse the observations greedily: at a good position,
take the block of a bet `M k ≥ exp (k L)`, `k₀ ≤ k ≤ K`; elsewhere skip one observation. Each
block of length `k` multiplies the covering mixture by at least `exp (k (L - ε)) / 2`, each skip
by `1 / 2`, and at most `N / k₀` blocks and `badCount + K` skips occur. -/
private lemma ofReal_exp_le_coverMixture {L ε : ℝ} (hεL : ε ≤ L) {k₀ K : ℕ} (hk₀ : 1 ≤ k₀)
    (hw : ∀ k : ℕ, k₀ ≤ k → Real.log ((k : ℝ) * (k + 1)) ≤ ε * k) (N : ℕ) (ω : ℕ → 𝓧) :
    ENNReal.ofReal (Real.exp ((L - ε) * (N - K - badCount (goodSet M L k₀ K) N ω) -
      (N / k₀ + K + badCount (goodSet M L k₀ K) N ω) * Real.log 2)) ≤ coverMixture M N ω := by
  set G := goodSet M L k₀ K
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hk₀' : (0 : ℝ) < k₀ := by exact_mod_cast hk₀
  have hexp2 : Real.exp (-Real.log 2) = 2⁻¹ := by rw [Real.exp_neg, Real.exp_log two_pos]
  induction N using Nat.strong_induction_on generalizing ω with
  | _ N ih =>
  have hC := badCount_nonneg G N ω
  by_cases hNK : N ≤ K
  · -- too few observations: the bound is below `2⁻¹ ^ N`
    refine le_trans ?_ (pow_le_coverMixture N ω)
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos two_pos,
      ← ENNReal.ofReal_pow (by norm_num), ← hexp2, ← Real.exp_natCast_mul]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have hN : (N : ℝ) ≤ K := by exact_mod_cast hNK
    have h1 : (L - ε) * (N - K - badCount G N ω) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have h2 : (0 : ℝ) ≤ N / k₀ := by positivity
    nlinarith
  rw [not_le] at hNK
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  by_cases hω : ω ∈ G
  · -- a good position: take the block of a bet `M k ≥ exp (k L)`
    obtain ⟨k, hk₀k, hkK, hkM⟩ := hω
    have hk1 : 0 < k := hk₀.trans hk₀k
    have hkN : k ≤ N' + 1 := hkK.trans hNK.le
    have hIH := ih (N' + 1 - k) (by omega) ((shift 𝓧)^[k] ω)
    set C := badCount G (N' + 1) ω
    set C' := badCount G (N' + 1 - k) ((shift 𝓧)^[k] ω)
    set B := (L - ε) * ((N' + 1 - k : ℕ) - K - C') -
      ((N' + 1 - k : ℕ) / k₀ + K + C') * Real.log 2
    have hreal : Real.exp ((L - ε) * ((N' + 1 : ℕ) - K - C) -
        ((N' + 1 : ℕ) / k₀ + K + C) * Real.log 2) ≤
        2⁻¹ * (coverWeight k * (Real.exp (k * L) * Real.exp B)) := by
      have hR : 2⁻¹ * (coverWeight k * (Real.exp (k * L) * Real.exp B)) =
          Real.exp (-Real.log 2 + -Real.log ((k : ℝ) * (k + 1)) + k * L + B) := by
        have e2 : Real.exp (-Real.log ((k : ℝ) * (k + 1))) = coverWeight k := by
          rw [Real.exp_neg, Real.exp_log (by positivity), coverWeight, one_div]
        rw [Real.exp_add, Real.exp_add, Real.exp_add, hexp2, e2]
        ring
      have hcast : ((N' + 1 : ℕ) : ℝ) = ((N' + 1 - k : ℕ) : ℝ) + k := by
        rw [Nat.cast_sub hkN]
        ring
      rw [hR, hcast]
      exact Real.exp_le_exp.2 (cover_exponent_le_of_good hεL hlog2 hk₀'
        (by exact_mod_cast hk₀k) (hw k hk₀k) (badCount_shift_le G hkN ω))
    calc ENNReal.ofReal (Real.exp ((L - ε) * ((N' + 1 : ℕ) - K - C) -
          ((N' + 1 : ℕ) / k₀ + K + C) * Real.log 2))
    _ ≤ ENNReal.ofReal (2⁻¹ * (coverWeight k * (Real.exp (k * L) * Real.exp B))) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = 2⁻¹ * (ENNReal.ofReal (coverWeight k) * (ENNReal.ofReal (Real.exp (k * L)) *
          ENNReal.ofReal (Real.exp B))) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (coverWeight_nonneg k),
        ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_inv_of_pos two_pos,
        ENNReal.ofReal_ofNat]
    _ ≤ 2⁻¹ * (ENNReal.ofReal (coverWeight k) *
          (M k ω * coverMixture M (N' + 1 - k) ((shift 𝓧)^[k] ω))) := by
      gcongr
    _ ≤ 2⁻¹ * ∑ j ∈ Finset.range (N' + 1), ENNReal.ofReal (coverWeight (j + 1)) *
          M (j + 1) ω * coverMixture M (N' - j) ((shift 𝓧)^[j + 1] ω) := by
      gcongr
      have h := Finset.single_le_sum (f := fun j ↦ ENNReal.ofReal (coverWeight (j + 1)) *
          M (j + 1) ω * coverMixture M (N' - j) ((shift 𝓧)^[j + 1] ω)) (fun _ _ ↦ bot_le)
        (Finset.mem_range.2 (show k - 1 < N' + 1 by omega))
      have e1 : k - 1 + 1 = k := by omega
      have e2 : N' - (k - 1) = N' + 1 - k := by omega
      simp only [e1, e2] at h
      rw [← mul_assoc]
      exact h
    _ ≤ coverMixture M (N' + 1) ω := by
      rw [coverMixture_succ]
      exact le_add_self
  · -- a bad position: skip one observation
    have hIH := ih N' N'.lt_succ_self (shift 𝓧 ω)
    have hCsucc := badCount_succ G N' ω
    rw [Set.indicator_of_mem (show ω ∈ Gᶜ from hω), Pi.one_apply] at hCsucc
    set C'' := badCount G N' (shift 𝓧 ω)
    have hreal : Real.exp ((L - ε) * ((N' + 1 : ℕ) - K - badCount G (N' + 1) ω) -
        ((N' + 1 : ℕ) / k₀ + K + badCount G (N' + 1) ω) * Real.log 2) ≤
        2⁻¹ * Real.exp ((L - ε) * (N' - K - C'') - (N' / k₀ + K + C'') * Real.log 2) := by
      rw [← hexp2, ← Real.exp_add, hCsucc, Nat.cast_succ]
      exact Real.exp_le_exp.2 (cover_exponent_le_of_bad hlog2 hk₀')
    calc ENNReal.ofReal (Real.exp ((L - ε) * ((N' + 1 : ℕ) - K - badCount G (N' + 1) ω) -
          ((N' + 1 : ℕ) / k₀ + K + badCount G (N' + 1) ω) * Real.log 2))
    _ ≤ ENNReal.ofReal (2⁻¹ * Real.exp ((L - ε) * (N' - K - C'') -
          (N' / k₀ + K + C'') * Real.log 2)) := ENNReal.ofReal_le_ofReal hreal
    _ = 2⁻¹ * ENNReal.ofReal (Real.exp ((L - ε) * (N' - K - C'') -
          (N' / k₀ + K + C'') * Real.log 2)) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos two_pos,
        ENNReal.ofReal_ofNat]
    _ ≤ 2⁻¹ * coverMixture M N' (shift 𝓧 ω) := by gcongr
    _ ≤ coverMixture M (N' + 1) ω := by
      rw [coverMixture_succ]
      exact le_self_add

/-- **The covering argument, for fixed `N`.** Integrating the pointwise bound
`ofReal_exp_le_coverMixture`, where the expected number of bad positions is `N q` with `q` the
probability of the bad event, gives a lower bound on the expected logarithm of the covering
mixture, which is at most `N` times the bipolar rate. -/
private lemma cover_le_mul_toReal_bipolarRate (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    {S : Set (Measure 𝓧)} (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hM : ∀ n, IsEVar (M n) (iidNull S)) (hMd : ∀ n, DependsOn (M n) (Set.Iio n))
    (hd : bipolarRate Q S ≠ ⊤) {L ε : ℝ} (hεL : ε ≤ L) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hw : ∀ k : ℕ, k₀ ≤ k → Real.log ((k : ℝ) * (k + 1)) ≤ ε * k) (K : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    (L - ε) * (N - K - N * (Measure.infinitePi fun _ : ℕ ↦ Q).real (goodSet M L k₀ K)ᶜ) -
      (N / k₀ + K + N * (Measure.infinitePi fun _ : ℕ ↦ Q).real (goodSet M L k₀ K)ᶜ) *
        Real.log 2 ≤ N * (bipolarRate Q S).toReal := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q)
  set G := goodSet M L k₀ K
  have hG := measurableSet_goodSet (fun n ↦ (hM n).measurable) L k₀ K
  have hbi : Integrable (badCount G N) μ :=
    .of_bound (measurable_badCount hG N).aestronglyMeasurable N (ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (badCount_nonneg G N ω)]
      exact badCount_le G N ω)
  have hA : Integrable (fun ω ↦ (L - ε) * (N - K - badCount G N ω)) μ :=
    ((integrable_const _).sub hbi).const_mul _
  have hB : Integrable (fun ω ↦ (N / k₀ + K + badCount G N ω) * Real.log 2) μ :=
    ((integrable_const _).add hbi).mul_const _
  have hAB : Integrable (fun ω ↦ (L - ε) * (N - K - badCount G N ω) -
      (N / k₀ + K + badCount G N ω) * Real.log 2) μ := hA.sub hB
  have hval : ∫ ω, ((L - ε) * (N - K - badCount G N ω) -
      (N / k₀ + K + badCount G N ω) * Real.log 2) ∂μ =
      (L - ε) * (N - K - N * μ.real Gᶜ) - (N / k₀ + K + N * μ.real Gᶜ) * Real.log 2 := by
    rw [integral_sub hA hB, integral_const_mul, integral_mul_const,
      integral_sub (integrable_const _) hbi, integral_add (integrable_const _) hbi,
      integral_badCount Q hG N]
    simp only [integral_const, probReal_univ, one_smul, μ, G]
  have hle : (((L - ε) * (N - K - N * μ.real Gᶜ) - (N / k₀ + K + N * μ.real Gᶜ) * Real.log 2 :
      ℝ) : EReal) ≤ N * bipolarRate Q S := by
    rw [← hval, ← eintegral_eq_integral hAB]
    calc ∫ᵉ ω, (((L - ε) * (N - K - badCount G N ω) -
          (N / k₀ + K + badCount G N ω) * Real.log 2 : ℝ) : EReal) ∂μ
    _ ≤ ∫ᵉ ω, ENNReal.log (coverMixture M N ω) ∂μ := eintegral_mono fun ω ↦ by
      rw [← ENNReal.log_ofReal_exp ((L - ε) * (N - K - badCount G N ω) -
        (N / k₀ + K + badCount G N ω) * Real.log 2)]
      exact ENNReal.log_le_log (ofReal_exp_le_coverMixture hεL hk₀ hw N ω)
    _ ≤ maxLogGrowth Q S N :=
      IsEVar.eintegral_log_le_maxLogGrowth Q hS
        (isEVar_coverMixture hM hMd N)
        (Filtration.measurable_piLT_of_dependsOn (isEVar_coverMixture hM hMd N).measurable
          (dependsOn_coverMixture hMd N))
    _ ≤ N * bipolarRate Q S := maxLogGrowth_le_mul_bipolarRate Q S (by omega)
  rwa [← coe_toReal_bipolarRate (fun P hP ↦ (hS P hP).measure_univ.le) hd, ← EReal.coe_natCast,
    ← EReal.coe_mul, EReal.coe_le_coe_iff] at hle

/-- **The covering argument, for fixed `K`.** Letting `N → ∞` in
`cover_le_mul_toReal_bipolarRate`. -/
private lemma sub_le_toReal_bipolarRate_of_goodSet (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    {S : Set (Measure 𝓧)} (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hM : ∀ n, IsEVar (M n) (iidNull S)) (hMd : ∀ n, DependsOn (M n) (Set.Iio n))
    (hd : bipolarRate Q S ≠ ⊤) {L ε : ℝ} (hεL : ε ≤ L) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hw : ∀ k : ℕ, k₀ ≤ k → Real.log ((k : ℝ) * (k + 1)) ≤ ε * k) (K : ℕ) :
    (L - ε) - Real.log 2 / k₀ -
      (L - ε + Real.log 2) * (Measure.infinitePi fun _ : ℕ ↦ Q).real (goodSet M L k₀ K)ᶜ ≤
        (bipolarRate Q S).toReal := by
  -- `N a - b ≤ N d` for every `N ≥ 1`, with `b = K (L - ε + log 2)`, so `a ≤ d`
  set a := (L - ε) - Real.log 2 / k₀ -
    (L - ε + Real.log 2) * (Measure.infinitePi fun _ : ℕ ↦ Q).real (goodSet M L k₀ K)ᶜ
  set b := K * (L - ε + Real.log 2)
  set d := (bipolarRate Q S).toReal
  have h (N : ℕ) (hN : 1 ≤ N) : N * a - b ≤ N * d := by
    refine le_of_eq_of_le ?_ (cover_le_mul_toReal_bipolarRate Q hS hM hMd hd hεL hk₀ hw K hN)
    ring
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨N, hN⟩ := exists_nat_gt (b / (a - d))
  have h1 := h (N + 1) (by omega)
  rw [div_lt_iff₀ (by linarith)] at hN
  push_cast at h1
  nlinarith

/-- As `K → ∞`, the probability that no bet `M k`, `k₀ ≤ k ≤ K`, exceeds `exp (k L)` tends to `0`
when, almost surely, `M n ≥ exp (n L)` for infinitely many `n`. -/
private lemma tendsto_measureReal_compl_goodSet {μ : Measure (ℕ → 𝓧)} [IsFiniteMeasure μ]
    (hMm : ∀ n, Measurable (M n)) {L : ℝ}
    (hL : ∀ᵐ ω ∂μ, ∃ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (n * L)) ≤ M n ω) (k₀ : ℕ) :
    Tendsto (fun K : ℕ ↦ μ.real (goodSet M L k₀ K)ᶜ) atTop (nhds 0) := by
  have hanti : Antitone fun K : ℕ ↦ (goodSet M L k₀ K)ᶜ := fun K K' hKK' ω hω hω' ↦ by
    obtain ⟨k, hk₀k, hkK, hkM⟩ := hω'
    exact hω ⟨k, hk₀k, hkK.trans hKK', hkM⟩
  have hinter : μ (⋂ K : ℕ, (goodSet M L k₀ K)ᶜ) = 0 := by
    refine measure_mono_null (fun ω hω ↦ ?_) (ae_iff.1 hL)
    simp only [Set.mem_iInter, Set.mem_compl_iff] at hω
    intro hfreq
    obtain ⟨k, hk, hkM⟩ := (frequently_atTop.1 hfreq) k₀
    exact hω k ⟨k, hk, le_rfl, hkM⟩
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun K ↦ (measurableSet_goodSet hMm L k₀ K).compl.nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hinter] at h
  simpa [Function.comp_def, measureReal_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

/-- **The covering argument, for fixed `ε` and `k₀`.** Letting `K → ∞` in
`sub_le_toReal_bipolarRate_of_goodSet`. -/
private lemma sub_log_two_div_le_toReal_bipolarRate (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    {S : Set (Measure 𝓧)} (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hM : ∀ n, IsEVar (M n) (iidNull S)) (hMd : ∀ n, DependsOn (M n) (Set.Iio n))
    (hd : bipolarRate Q S ≠ ⊤) {L : ℝ}
    (hL : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q),
      ∃ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (n * L)) ≤ M n ω) {ε : ℝ} (hεL : ε ≤ L)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hw : ∀ k : ℕ, k₀ ≤ k → Real.log ((k : ℝ) * (k + 1)) ≤ ε * k) :
    (L - ε) - Real.log 2 / k₀ ≤ (bipolarRate Q S).toReal := by
  have hlim : Tendsto (fun K : ℕ ↦ (L - ε) - Real.log 2 / k₀ - (L - ε + Real.log 2) *
      (Measure.infinitePi fun _ : ℕ ↦ Q).real (goodSet M L k₀ K)ᶜ) atTop
      (nhds ((L - ε) - Real.log 2 / k₀ - (L - ε + Real.log 2) * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul
      (tendsto_measureReal_compl_goodSet (fun n ↦ (hM n).measurable) hL k₀))
  rw [mul_zero, sub_zero] at hlim
  exact le_of_tendsto' hlim
    (sub_le_toReal_bipolarRate_of_goodSet Q hS hM hMd hd hεL hk₀ hw)

/-- **The covering argument.** Let `M n` be functions of the first `n` observations with
expectation at most `1` under the i.i.d. laws of the members of `S`. If, almost surely under the
i.i.d. law of `Q`, `M n ≥ exp (n L)` for infinitely many `n`, then `L` is at most the bipolar rate:
the covering mixture of `N` observations has expected logarithm at least about
`N ((L - ε) (1 - q) - (1 / k₀ + q) log 2)`, where `q` is the probability that no bet `M k`,
`k₀ ≤ k ≤ K`, exceeds `exp (k L)`, and at most `N` times the bipolar rate. -/
private lemma coe_le_bipolarRate_of_ae_frequently (Q : Measure 𝓧) [IsProbabilityMeasure Q]
    {S : Set (Measure 𝓧)} (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hM : ∀ n, IsEVar (M n) (iidNull S)) (hMd : ∀ n, DependsOn (M n) (Set.Iio n)) {L : ℝ}
    (hL : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q),
      ∃ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (n * L)) ≤ M n ω) :
    (L : EReal) ≤ bipolarRate Q S := by
  by_cases hd : bipolarRate Q S = ⊤
  · rw [hd]
    exact le_top
  rw [← coe_toReal_bipolarRate (fun P hP ↦ (hS P hP).measure_univ.le) hd, EReal.coe_le_coe_iff]
  by_cases hL0 : L ≤ 0
  · exact hL0.trans
      (EReal.toReal_nonneg (bipolarRate_nonneg Q fun P hP ↦ (hS P hP).measure_univ.le))
  rw [not_le] at hL0
  -- let `ε → 0` and `k₀ → ∞`
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  set ε := min (η / 2) L
  have hε : 0 < ε := lt_min (by linarith) hL0
  obtain ⟨k₀, hk₀, hw⟩ := exists_log_inv_coverWeight_le hε
  obtain ⟨k₁, hk₁⟩ := exists_nat_gt (Real.log 2 / (η / 2))
  have hk : 1 ≤ max k₀ k₁ := hk₀.trans (le_max_left _ _)
  have h := sub_log_two_div_le_toReal_bipolarRate Q hS hM hMd hd hL (min_le_right _ _) hk
    fun k hk' ↦ hw k ((le_max_left _ _).trans hk')
  have hk₁' : (k₁ : ℝ) ≤ max k₀ k₁ := by exact_mod_cast le_max_right k₀ k₁
  have hpos : (0 : ℝ) < max k₀ k₁ := by exact_mod_cast hk
  have hdiv : Real.log 2 / (max k₀ k₁ : ℕ) ≤ η / 2 := by
    rw [div_le_iff₀ hpos]
    rw [div_lt_iff₀ (by linarith)] at hk₁
    push_cast at hpos hk₁' ⊢
    nlinarith
  have hεη : ε ≤ η / 2 := min_le_left _ _
  linarith

/-! ### The mixture over shifts -/

variable (M) in
/-- The mixture over `s < n` of the functions `M (n - s)` of the observations after the first
`s`, with weights `2⁻¹ ^ (s + 1)`. -/
private noncomputable def shiftMixture (n : ℕ) (ω : ℕ → 𝓧) : ℝ≥0∞ :=
  ∑ s ∈ Finset.range n, 2⁻¹ ^ (s + 1) * M (n - s) ((shift 𝓧)^[s] ω)

/-- The shift mixture of functions of the first observations is a function of the first `n`
observations. -/
private lemma dependsOn_shiftMixture (hM : ∀ n, DependsOn (M n) (Set.Iio n)) (n : ℕ) :
    DependsOn (shiftMixture M n) (Set.Iio n) := by
  intro ω ω' h
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hs : s < n := Finset.mem_range.1 hs
  rw [show M (n - s) ((shift 𝓧)^[s] ω) = M (n - s) ((shift 𝓧)^[s] ω') from
    dependsOn_comp_shift_iterate (hM (n - s)) s fun i (hi : i < s + (n - s)) ↦
      h i (show i < n by omega)]

/-- The shift mixture of e-variables for the i.i.d. null is an e-variable for it: a mixture of
bets read after skipping observations. -/
private lemma isEVar_shiftMixture {S : Set (Measure 𝓧)} (hM : ∀ n, IsEVar (M n) (iidNull S))
    (n : ℕ) : IsEVar (shiftMixture M n) (iidNull S) := by
  unfold shiftMixture
  refine isEVar_finsetSum_mul _ (fun s _ ↦ (hM (n - s)).comp_shift_iterate s) ?_
  calc ∑ s ∈ Finset.range n, (2⁻¹ : ℝ≥0∞) ^ (s + 1)
  _ ≤ ∑' s, (2⁻¹ : ℝ≥0∞) ^ (s + 1) := sum_le_tsum _
  _ = 1 := ENNReal.tsum_geometric_two_add_one

/-- If `M m ≥ exp (m L)` for infinitely many `m` along the shifted sequence, then the shift
mixture exceeds `exp (n L')` for infinitely many `n`, for every `L' < L`. -/
private lemma frequently_le_shiftMixture {L L' : ℝ} (hLL' : L' < L) {s : ℕ} {ω : ℕ → 𝓧}
    (h : ∃ᶠ m : ℕ in atTop, ENNReal.ofReal (Real.exp (m * L)) ≤ M m ((shift 𝓧)^[s] ω)) :
    ∃ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (n * L')) ≤ shiftMixture M n ω := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt ((s * L' + (s + 1) * Real.log 2) / (L - L'))
  rw [frequently_atTop] at h ⊢
  intro a
  obtain ⟨m, hm, hmL⟩ := h (max a m₀ + 1)
  refine ⟨m + s, by omega, ?_⟩
  have hm1 : (m₀ : ℝ) < m := by exact_mod_cast (by omega : m₀ < m)
  have hreal : Real.exp (((m + s : ℕ) : ℝ) * L') ≤ 2⁻¹ ^ (s + 1) * Real.exp (m * L) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 2⁻¹ ^ (s + 1)), ← Real.exp_add, Real.log_pow,
      Real.log_inv]
    refine Real.exp_le_exp.2 ?_
    rw [div_lt_iff₀ (by linarith)] at hm₀
    push_cast
    nlinarith
  calc ENNReal.ofReal (Real.exp (((m + s : ℕ) : ℝ) * L'))
  _ ≤ ENNReal.ofReal (2⁻¹ ^ (s + 1) * Real.exp (m * L)) := ENNReal.ofReal_le_ofReal hreal
  _ = 2⁻¹ ^ (s + 1) * ENNReal.ofReal (Real.exp (m * L)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  _ ≤ 2⁻¹ ^ (s + 1) * M m ((shift 𝓧)^[s] ω) := by gcongr
  _ = 2⁻¹ ^ (s + 1) * M (m + s - s) ((shift 𝓧)^[s] ω) := by rw [Nat.add_sub_cancel]
  _ ≤ shiftMixture M (m + s) ω :=
    Finset.single_le_sum (f := fun s' ↦ 2⁻¹ ^ (s' + 1) * M (m + s - s') ((shift 𝓧)^[s'] ω))
      (fun _ _ ↦ bot_le) (Finset.mem_range.2 (by omega))

/-! ### The almost sure growth bound -/

variable {Q₁ : Measure 𝓧} {S₁ : Set (Measure 𝓧)}

/-- **No function of the first observations grows faster than the bipolar rate, almost surely.**
Let `F n` be e-variables for the i.i.d. laws of the members of `S₁` such that `F n` is a function
of the first `n` observations: `F` is adapted to the filtration `Filtration.piLT` of the
observations. Almost surely under the i.i.d. law of `Q₁`,
`limsup (1/n) log (F n) ≤ bipolarRate Q₁ S₁` [EVR26, Note 01]. -/
theorem ae_limsup_log_div_le_bipolarRate_of_adapted (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {F : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hF : Adapted (Filtration.piLT (X := fun _ : ℕ ↦ 𝓧)) F)
    (hFe : ∀ n, IsEVar (F n) (iidNull S₁)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      limsup (fun n : ℕ ↦ ENNReal.log (F n ω) / (n : EReal)) atTop ≤ bipolarRate Q₁ S₁ := by
  have hFm : ∀ n, Measurable (F n) := fun n ↦ (hFe n).measurable
  have hFn : ∀ n, DependsOn (F n) (Set.Iio n) := fun n ↦ (hF n).dependsOn_of_piLT
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  by_cases hd : bipolarRate Q₁ S₁ = ⊤
  · simp [hd]
  set d := (bipolarRate Q₁ S₁).toReal
  have hdeq : (d : EReal) = bipolarRate Q₁ S₁ :=
    coe_toReal_bipolarRate (fun P hP ↦ (hS₁ P hP).measure_univ.le) hd
  -- for `L > d`, almost surely `F n < exp (n L)` eventually
  have key (L : ℝ) (hL : d < L) :
      ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, F n ω < ENNReal.ofReal (Real.exp (n * L)) := by
    set B := {ω | ∃ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (n * L)) ≤ F n ω}
    have hBm : MeasurableSet B := by
      have : B = ⋂ N : ℕ, ⋃ n ≥ N, {ω | ENNReal.ofReal (Real.exp (n * L)) ≤ F n ω} := by
        ext ω
        simp [B, frequently_atTop]
      rw [this]
      exact .iInter fun N ↦ .iUnion fun n ↦ .iUnion fun _ ↦
        measurableSet_le measurable_const (hFm n)
    have hB : μ B = 0 → ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
        F n ω < ENNReal.ofReal (Real.exp (n * L)) := fun h0 ↦
      ae_iff.2 (measure_mono_null (fun ω hω ↦ by
        simp only [Set.mem_ofPred_eq, not_eventually, not_lt] at hω
        exact hω) h0)
    -- the event that some shifted sequence is in `B` has probability `0` or `1`
    set U := ⋃ s, (shift 𝓧)^[s] ⁻¹' B
    have hUm : MeasurableSet U := .iUnion fun s ↦ measurable_shift_iterate s hBm
    have hBU : B ⊆ U := fun ω hω ↦ Set.mem_iUnion.2 ⟨0, hω⟩
    have hUshift : shift 𝓧 ⁻¹' U ⊆ U := fun ω hω ↦ by
      obtain ⟨s, hs⟩ := Set.mem_iUnion.1 hω
      exact Set.mem_iUnion.2 ⟨s + 1, by rwa [Set.mem_preimage, Function.iterate_succ_apply]⟩
    rcases (Measure.ergodic_shift_infinitePi_const Q₁).ae_empty_or_univ_of_preimage_ae_le
      hUm.nullMeasurableSet (ae_of_all _ fun ω (hω : ω ∈ shift 𝓧 ⁻¹' U) ↦ hUshift hω)
      with hU | hU
    · exact hB (measure_mono_null hBU (ae_eq_empty.1 hU))
    -- if it has probability `1`, the shift mixture grows at a rate above `d`
    have hUae : ∀ᵐ ω ∂μ, ω ∈ U := by
      rw [ae_iff]
      exact ae_eq_univ.1 hU
    have hae : ∀ᵐ ω ∂μ, ∃ᶠ n : ℕ in atTop,
        ENNReal.ofReal (Real.exp (n * ((d + L) / 2))) ≤ shiftMixture F n ω := by
      filter_upwards [hUae] with ω hω
      obtain ⟨s, hs⟩ := Set.mem_iUnion.1 hω
      exact frequently_le_shiftMixture (by linarith) hs
    have h := coe_le_bipolarRate_of_ae_frequently Q₁ hS₁ (isEVar_shiftMixture hFe)
      (dependsOn_shiftMixture hFn) hae
    rw [← hdeq, EReal.coe_le_coe_iff] at h
    linarith
  have key' : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ᶠ n in atTop,
      F n ω < ENNReal.ofReal (Real.exp (n * (d + 1 / ((k : ℝ) + 1)))) :=
    ae_all_iff.2 fun k ↦ key _ (lt_add_of_pos_right _ (by positivity))
  filter_upwards [key'] with ω hω
  refine le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_
  induction c using EReal.rec with
  | bot => exact absurd hc not_lt_bot
  | top => exact le_top
  | coe c =>
    rw [← hdeq, EReal.coe_lt_coe_iff] at hc
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
    refine limsup_le_of_le (by isBoundedDefault) (((hω k).and (eventually_ge_atTop 1)).mono
      fun n hn ↦ ?_)
    obtain ⟨hn, hn1⟩ := hn
    rw [EReal.div_le_iff_le_mul (by exact_mod_cast hn1) (EReal.natCast_ne_top n)]
    calc ENNReal.log (F n ω)
    _ ≤ ENNReal.log (ENNReal.ofReal (Real.exp (n * (d + 1 / ((k : ℝ) + 1))))) :=
      ENNReal.log_le_log hn.le
    _ = ((n * (d + 1 / ((k : ℝ) + 1)) : ℝ) : EReal) := by
      rw [ENNReal.log_ofReal_exp]
    _ ≤ n * c := by
      rw [← EReal.coe_natCast, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)

/-- **No sequence of `n`-sample e-variables grows faster than the bipolar rate, almost surely.**
For every sequence of `n`-sample e-variables `M n` for the i.i.d. laws of the members of `S₁`,
almost surely under the i.i.d. law of `Q₁`, `M n` evaluated at the first `n` observations has
`limsup (1/n) log (M n) ≤ bipolarRate Q₁ S₁` [EVR26, Note 01]. -/
theorem ae_limsup_log_div_le_bipolarRate (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {M : (n : ℕ) → (Fin n → 𝓧) → ℝ≥0∞}
    (hM : ∀ n, IsEVar (M n) (sampleNull S₁ n)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      limsup (fun n : ℕ ↦ ENNReal.log (M n (initSeg n ω)) / (n : EReal)) atTop ≤
        bipolarRate Q₁ S₁ :=
  ae_limsup_log_div_le_bipolarRate_of_adapted Q₁ hS₁ (F := fun n ω ↦ M n (initSeg n ω))
    (fun n ↦ (hM n).measurable.comp (Filtration.measurable_piLT_initSeg le_rfl))
    fun n ↦ (isEVar_mapNull_iff (measurable_initSeg n) (hM n).measurable).1
      (mapNull_initSeg_iidNull hS₁ n ▸ hM n)

/-- **No e-process for an i.i.d. null grows faster than the bipolar rate, almost surely.** For an
e-process `E` for the i.i.d. laws of the members of `S₁`, in the filtration `Filtration.piLT` of the
observations, almost surely under the i.i.d. law of `Q₁`, the logarithm of `E n` divided by the
number `n` of observations it has seen has `limsup` at most `bipolarRate Q₁ S₁`. -/
theorem IsEProcess.ae_limsup_log_div_le_bipolarRate (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {E : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hE : IsEProcess E (Filtration.piLT (X := fun _ : ℕ ↦ 𝓧)) (iidNull S₁)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      limsup (fun n : ℕ ↦ ENNReal.log (E n ω) / (n : EReal)) atTop ≤ bipolarRate Q₁ S₁ :=
  ae_limsup_log_div_le_bipolarRate_of_adapted Q₁ hS₁ hE.adapted hE.isEVar

/-! ### Sequential tests of small levels stop late, almost surely -/

section Test

variable {τ : ℕ → (ℕ → 𝓧) → WithTop ℕ}

/-- The mixture over `k` of the bets `exp k * 𝟙{τ k ≤ n}` on the tests `τ k`, with the
geometric weights `(1 - exp (-ε)) * exp (-ε) ^ k`. -/
private noncomputable def levelMixture (τ : ℕ → (ℕ → 𝓧) → WithTop ℕ) (ε : ℝ) (n : ℕ)
    (ω : ℕ → 𝓧) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal ((1 - Real.exp (-ε)) * Real.exp (-ε) ^ k * Real.exp k) *
    {ω | τ k ω ≤ n}.indicator 1 ω

/-- The mixture is adapted to the filtration of the observations when the `τ k` are stopping
times of it. -/
private lemma adapted_levelMixture (hτ : ∀ k, IsStoppingTime Filtration.piLT (τ k)) (ε : ℝ) :
    Adapted (Filtration.piLT (X := fun _ : ℕ ↦ 𝓧)) (levelMixture τ ε) := fun n ↦
  @Measurable.tsum _ _ _ (Filtration.piLT n) _ _ _ _ _ _ _ _ _ _ _ _ fun k ↦
    (measurable_const.indicator (hτ k n)).const_mul _

/-- The weights of the mixture add up to `1`. -/
private lemma tsum_ofReal_weight {ε : ℝ} (hε : 0 < ε) :
    ∑' k : ℕ, ENNReal.ofReal ((1 - Real.exp (-ε)) * Real.exp (-ε) ^ k) = 1 := by
  have h0 : 0 ≤ Real.exp (-ε) := (Real.exp_pos _).le
  have h1 : Real.exp (-ε) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hpos : 0 < 1 - Real.exp (-ε) := sub_pos.2 h1
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ mul_nonneg hpos.le (pow_nonneg h0 k))
    ((summable_geometric_of_lt_one h0 h1).mul_left _), tsum_mul_left,
    tsum_geometric_of_lt_one h0 h1, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one]

/-- The mixture of the bets on tests `τ k` of level `exp (-k)` is an e-variable for the i.i.d.
null. -/
private lemma isEVar_levelMixture
    (hτ : ∀ k, IsLevelStoppingTime (τ k) Filtration.piLT (iidNull S₁)
      (ENNReal.ofReal (Real.exp (-k)))) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    IsEVar (levelMixture τ ε n) (iidNull S₁) := by
  refine ⟨(adapted_levelMixture (fun k ↦ (hτ k).isStoppingTime) ε n).mono
    (Filtration.le _ n) le_rfl, fun μ hμ ↦ ?_⟩
  have hm : ∀ k, MeasurableSet {ω | τ k ω ≤ n} := fun k ↦
    Filtration.le _ n _ ((hτ k).isStoppingTime n)
  unfold levelMixture
  rw [lintegral_tsum (f := fun (k : ℕ) ω ↦ ENNReal.ofReal ((1 - Real.exp (-ε)) * Real.exp (-ε) ^ k *
    Real.exp k) * {ω | τ k ω ≤ n}.indicator 1 ω) fun k ↦
    ((measurable_const.indicator (hm k)).const_mul _).aemeasurable, ← tsum_ofReal_weight hε]
  refine tsum_le_tsum fun k ↦ ?_
  rw [lintegral_const_mul _ (measurable_one.indicator (hm k)), lintegral_indicator_one (hm k)]
  calc ENNReal.ofReal ((1 - Real.exp (-ε)) * Real.exp (-ε) ^ k * Real.exp k) *
      μ {ω | τ k ω ≤ n}
  _ ≤ ENNReal.ofReal ((1 - Real.exp (-ε)) * Real.exp (-ε) ^ k * Real.exp k) *
      ENNReal.ofReal (Real.exp (-k)) := by
    gcongr
    exact (measure_mono (Set.ofPred_subset_ofPred.2 fun ω (hω : τ k ω ≤ n) ↦
      hω.trans_lt (WithTop.coe_lt_top n))).trans
      ((hτ k).measure_lt_top_le μ hμ)
  _ = ENNReal.ofReal ((1 - Real.exp (-ε)) * Real.exp (-ε) ^ k) := by
    have hε' : 0 ≤ 1 - Real.exp (-ε) := sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith))
    rw [← ENNReal.ofReal_mul (by positivity), mul_assoc _ (Real.exp k), ← Real.exp_add,
      add_neg_cancel, Real.exp_zero, mul_one]

/-- For every `c > 0` with `c d < 1`, where `d` is the bipolar rate, tests `τ k` of level
`exp (-k)` make at least `c k` observations for all large `k`, almost surely under the i.i.d. law
of `Q₁`. -/
private lemma ae_eventually_ofReal_mul_le (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hτ : ∀ k, IsLevelStoppingTime (τ k) Filtration.piLT (iidNull S₁)
      (ENNReal.ofReal (Real.exp (-k)))) {c D : ℝ} (hc : 0 < c) (hD0 : 0 ≤ D)
    (hD : bipolarRate Q₁ S₁ = D) (hcD : c * D < 1) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      ∀ᶠ k : ℕ in atTop, ENNReal.ofReal (c * k) ≤ ENat.toENNReal (τ k ω) := by
  -- a rate `L > D` with `c L < 1`, and the weights `exp (-ε k)` with `c L = 1 - 2 ε`
  set L := (D + 1 / c) / 2 with hL
  have hcL : c * L = (c * D + 1) / 2 := by
    rw [hL]
    field_simp
  have hDL : D < L := by
    have : D < 1 / c := by
      rw [lt_div_iff₀ hc]
      linarith
    linarith
  set ε := (1 - c * L) / 2 with hε
  have hε0 : 0 < ε := by linarith
  have hpos : 0 < 1 - Real.exp (-ε) := sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))
  filter_upwards [ae_limsup_log_div_le_bipolarRate_of_adapted Q₁ hS₁
    (adapted_levelMixture (fun k ↦ (hτ k).isStoppingTime) ε) (isEVar_levelMixture hτ hε0)]
    with ω hω
  rw [hD] at hω
  -- the mixture eventually stays below `exp (n L)`
  have hlt : ∀ᶠ n : ℕ in atTop, levelMixture τ ε n ω < ENNReal.ofReal (Real.exp (n * L)) := by
    filter_upwards [eventually_lt_of_limsup_lt (hω.trans_lt (EReal.coe_lt_coe_iff.2 hDL)),
      eventually_ge_atTop 1] with n hn hn1
    rw [EReal.div_lt_iff (by exact_mod_cast hn1) (EReal.natCast_ne_top n), mul_comm,
      ← EReal.coe_natCast, ← EReal.coe_mul] at hn
    rwa [← ENNReal.log_lt_log_iff, ENNReal.log_ofReal_exp]
  -- a test `τ k` that stops before `c k` makes the mixture at time `⌈c k⌉` exceed `exp (⌈c k⌉ L)`
  by_contra h
  rw [not_eventually] at h
  obtain ⟨K, hK⟩ := exists_nat_gt ((L - Real.log (1 - Real.exp (-ε))) / ε)
  have htend : Tendsto (fun k : ℕ ↦ ⌈c * k⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  obtain ⟨k, hk, hkK, hkn⟩ :=
    (h.and_eventually ((eventually_ge_atTop K).and (htend.eventually hlt))).exists
  rw [not_le] at hk
  have hτn : τ k ω ≤ (⌈c * k⌉₊ : WithTop ℕ) := by
    refine ENat.toENNReal_le.1
      (hk.le.trans ((ENNReal.ofReal_le_ofReal (Nat.le_ceil _)).trans_eq ?_))
    rw [ENNReal.ofReal_natCast]
    exact (ENat.toENNReal_coe _).symm
  have hge : ENNReal.ofReal ((1 - Real.exp (-ε)) * Real.exp (-ε) ^ k * Real.exp k) ≤
      levelMixture τ ε ⌈c * k⌉₊ ω := by
    refine le_of_eq_of_le ?_ (le_tsum _ k)
    rw [Set.indicator_of_mem hτn, Pi.one_apply, mul_one]
  have hreal : Real.exp (⌈c * k⌉₊ * L) ≤
      (1 - Real.exp (-ε)) * Real.exp (-ε) ^ k * Real.exp k := by
    rw [← Real.exp_natCast_mul, ← Real.exp_log hpos, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hceil : (⌈c * k⌉₊ : ℝ) < c * k + 1 := Nat.ceil_lt_add_one (by positivity)
    have hkK' : (K : ℝ) ≤ k := by exact_mod_cast hkK
    rw [div_lt_iff₀ hε0] at hK
    nlinarith
  exact absurd ((ENNReal.ofReal_le_ofReal hreal).trans hge) (not_le.2 hkn)

/-- Almost surely, for every `r < 1 / d`, where `d` is the bipolar rate, tests `τ k` of level
`exp (-k)` make at least `r k` observations for all large `k`. -/
private lemma ae_forall_lt_eventually_mul_le (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hτ : ∀ k, IsLevelStoppingTime (τ k) Filtration.piLT (iidNull S₁)
      (ENNReal.ofReal (Real.exp (-k)))) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ r < (bipolarRate Q₁ S₁).toENNReal⁻¹,
      ∀ᶠ k : ℕ in atTop, r * k ≤ ENat.toENNReal (τ k ω) := by
  by_cases hd : bipolarRate Q₁ S₁ = ⊤
  · simp [hd]
  have hS₁' : ∀ P ∈ S₁, P Set.univ ≤ 1 := fun P hP ↦ (hS₁ P hP).measure_univ.le
  set D := (bipolarRate Q₁ S₁).toReal
  have hD0 : 0 ≤ D := EReal.toReal_nonneg (bipolarRate_nonneg Q₁ hS₁')
  -- the bound for every rational `q > 0` with `q D < 1`
  have hrat : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ q : ℚ, 0 < (q : ℝ) →
      (q : ℝ) * D < 1 → ∀ᶠ k : ℕ in atTop, ENNReal.ofReal (q * k) ≤ ENat.toENNReal (τ k ω) := by
    refine ae_all_iff.2 fun q ↦ ?_
    by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) * D < 1
    · filter_upwards [ae_eventually_ofReal_mul_le Q₁ hS₁ hτ hq.1 hD0
        (coe_toReal_bipolarRate hS₁' hd).symm hq.2] with ω hω _ _
      exact hω
    · exact ae_of_all _ fun ω h1 h2 ↦ absurd ⟨h1, h2⟩ hq
  filter_upwards [hrat] with ω hω r hr
  rw [EReal.toENNReal_of_ne_top hd] at hr
  -- a rational `q` with `r < q < 1 / D`
  obtain ⟨q, -, hrq, hqD⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hr
  have hq : 0 < (q : ℝ) := by simpa using pos_of_gt hrq
  have hqD' := ENNReal.mul_lt_of_lt_div (a := ENNReal.ofReal q) (b := 1) (by rwa [one_div])
  rw [← ENNReal.ofReal_mul hq.le, ENNReal.ofReal_lt_one] at hqD'
  filter_upwards [hω q hq hqD'] with k hk
  rw [ENNReal.ofReal_mul hq.le, ENNReal.ofReal_natCast] at hk
  exact (mul_le_mul_left hrq.le _).trans hk

/-- **Tests of small levels stop late, almost surely.** Let `τ k` be a sequential test of level
`exp (-k)` for the i.i.d. laws of the members of `S₁`, for every `k`: a stopping time of the
filtration `Filtration.piLT` with `P^ℕ (τ k < ∞) ≤ exp (-k)` for every `P ∈ S₁`. Almost surely
under the i.i.d. law of `Q₁`, `liminf_k τ k / k ≥ 1 / d`, where `d` is the bipolar rate of `Q₁`
against `S₁`. The tests at different levels need not be related. If `d = 0`, the tests make, almost
surely, more than `c k` observations for all large `k`, for every `c`. [ARR26, Theorem 3.1] states
the bound with `KL_inf(Q₁, S₁)`, which is at least `d`
(`ProbabilityTheory.ae_inv_toENNReal_klInf_le_liminf_div`). -/
theorem ae_inv_toENNReal_bipolarRate_le_liminf_div (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hτ : ∀ k : ℕ, IsLevelStoppingTime (τ k) Filtration.piLT (iidNull S₁)
      (ENNReal.ofReal (Real.exp (-k)))) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      (bipolarRate Q₁ S₁).toENNReal⁻¹ ≤ liminf (fun k : ℕ ↦ ENat.toENNReal (τ k ω) / k) atTop := by
  filter_upwards [ae_forall_lt_eventually_mul_le Q₁ hS₁ hτ] with ω hω
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hω r hr, eventually_ge_atTop 1] with k hk hk1
  rwa [ENNReal.le_div_iff_mul_le (.inl (by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hk1)))
    (.inl (ENNReal.natCast_ne_top k))]

/-- **Tests of small levels stop late, almost surely**, with the smallest relative entropy
`KL_inf(Q₁, S₁)` from `Q₁` to the null: `liminf_k τ k / k ≥ 1 / KL_inf(Q₁, S₁)` for sequential tests
`τ k` of level `exp (-k)` [ARR26, Theorem 3.1]. The bipolar rate is at most `KL_inf(Q₁, S₁)`
(`bipolarRate_le_klInf`), so `ae_inv_toENNReal_bipolarRate_le_liminf_div` is stronger. -/
theorem ae_inv_toENNReal_klInf_le_liminf_div (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hτ : ∀ k : ℕ, IsLevelStoppingTime (τ k) Filtration.piLT (iidNull S₁)
      (ENNReal.ofReal (Real.exp (-k)))) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      (klInf Q₁ S₁).toENNReal⁻¹ ≤ liminf (fun k : ℕ ↦ ENat.toENNReal (τ k ω) / k) atTop := by
  filter_upwards [ae_inv_toENNReal_bipolarRate_le_liminf_div Q₁ hS₁ hτ] with ω hω
  exact (ENNReal.inv_le_inv.2 (EReal.toENNReal_le_toENNReal (bipolarRate_le_klInf Q₁ hS₁))).trans hω

/-- A level `α < exp (-N)` lies below a grid point `exp (-m)` with `N ≤ m` and
`log (1/α) < m + 1`. -/
private lemma exists_le_ofReal_exp_neg {α : ℝ≥0∞} {N : ℕ} (hα0 : 0 < α)
    (hαN : α < ENNReal.ofReal (Real.exp (-N))) :
    ∃ m : ℕ, N ≤ m ∧ α ≤ ENNReal.ofReal (Real.exp (-m)) ∧
      ∃ b : ℝ, 0 < b ∧ b < m + 1 ∧ (ENNReal.log α⁻¹).toENNReal = ENNReal.ofReal b := by
  have hα1 : α < 1 := hαN.trans_le (ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2
    (neg_nonpos.2 (Nat.cast_nonneg _))))
  have hlog_top : ENNReal.log α⁻¹ ≠ ⊤ := by simpa using hα0.ne'
  have hlog_bot : ENNReal.log α⁻¹ ≠ ⊥ := by simpa using hα1.ne_top
  set b := (ENNReal.log α⁻¹).toReal
  have hb : ENNReal.log α = ((-b : ℝ) : EReal) := by
    rw [EReal.coe_neg, EReal.coe_toReal hlog_top hlog_bot, ENNReal.log_inv, neg_neg]
  have hb0 : 0 < b := by
    rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal hlog_top hlog_bot, EReal.coe_zero,
      ENNReal.zero_lt_log_iff]
    exact ENNReal.one_lt_inv.2 hα1
  refine ⟨⌊b⌋₊, Nat.le_floor ?_, ?_, b, hb0, Nat.lt_floor_add_one b,
    EReal.toENNReal_of_ne_top hlog_top⟩
  · have h := ENNReal.log_lt_log hαN
    rw [hb, ENNReal.log_ofReal_exp, EReal.coe_lt_coe_iff] at h
    linarith
  · rw [← ENNReal.log_le_log_iff, hb, ENNReal.log_ofReal_exp, EReal.coe_le_coe_iff,
      neg_le_neg_iff]
    exact Nat.floor_le hb0.le

/-- **Nested tests of small levels stop late, almost surely.** Let `τ α` be a sequential test of
level `α` for the i.i.d. laws of the members of `S₁`, in the filtration `Filtration.piLT`, for
every `α ∈ (0, a)`, and let the tests be nested: `τ α ≤ τ α'` for `α' ≤ α` in `(0, a)`. Almost
surely under the i.i.d. law of `Q₁`, `liminf_{α → 0} τ α / log (1/α) ≥ 1 / d`, where `d` is the
bipolar rate of `Q₁` against `S₁`. [ARR26, Theorem 3.1] states the bound with `KL_inf(Q₁, S₁)`,
which is at least `d`, and `a = 1/2`. -/
theorem ae_inv_toENNReal_bipolarRate_le_liminf_div_log (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {τ : ℝ≥0∞ → (ℕ → 𝓧) → WithTop ℕ} {a : ℝ≥0∞}
    (ha : 0 < a) (hτ : ∀ α ∈ Set.Ioo 0 a, IsLevelStoppingTime (τ α) Filtration.piLT (iidNull S₁) α)
    (hτa : ∀ ω, AntitoneOn (τ · ω) (Set.Ioo 0 a)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), (bipolarRate Q₁ S₁).toENNReal⁻¹ ≤
      liminf (fun α ↦ ENat.toENNReal (τ α ω) / (ENNReal.log α⁻¹).toENNReal) (𝓝[>] 0) := by
  -- the tests on the grid `exp (-(k + k₀))`, inside `(0, a)`
  set g : ℕ → ℝ≥0∞ := fun k ↦ ENNReal.ofReal (Real.exp (-k))
  have hg0 (k : ℕ) : 0 < g k := ENNReal.ofReal_pos.2 (Real.exp_pos _)
  have hg (k j : ℕ) (h : k ≤ j) : g j ≤ g k :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by simpa using h))
  have hlog (k : ℕ) : ENNReal.log (g k) = ((-k : ℝ) : EReal) := ENNReal.log_ofReal_exp _
  have hgtend : Tendsto g atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop))
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (hgtend.eventually (eventually_lt_nhds ha))
  have hσ (k : ℕ) : IsLevelStoppingTime (τ (g (k + k₀))) Filtration.piLT (iidNull S₁) (g k) :=
    (hτ _ ⟨hg0 _, hk₀ _ (by omega)⟩).mono (hg _ _ (by omega))
  filter_upwards [ae_forall_lt_eventually_mul_le Q₁ hS₁ hσ] with ω hω
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ le_liminf_of_le (by isBoundedDefault) ?_
  -- a rate `s` with `r < s < 1 / d`, and the grid index `J` after which it applies
  obtain ⟨s, hrs, hsd⟩ := exists_between hr
  have hs_top : s ≠ ⊤ := (hsd.trans_le le_top).ne
  have hrs' : r.toReal < s.toReal := ENNReal.toReal_strict_mono hs_top hrs
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hω s hsd)
  obtain ⟨J', hJ'⟩ := exists_nat_gt (r.toReal * (k₀ + 1) / (s.toReal - r.toReal))
  rw [div_lt_iff₀ (sub_pos.2 hrs')] at hJ'
  -- for `α < exp (-(max J J' + k₀))`, the test `τ α` stops after the test of the grid point
  -- `exp (-m) ≥ α`, with `log (1/α) < m + 1`
  filter_upwards [Ioo_mem_nhdsGT (hg0 (max J J' + k₀))] with α ⟨hα0, hαN⟩
  obtain ⟨m, hNm, hαm, b, hb0, hbm, hB⟩ := exists_le_ofReal_exp_neg hα0 hαN
  have hτα : s * (m - k₀ : ℕ) ≤ ENat.toENNReal (τ α ω) := by
    refine (hJ (m - k₀) (by omega)).trans (ENat.toENNReal_le.2 ?_)
    rw [Nat.sub_add_cancel (by omega)]
    exact hτa ω ⟨hα0, hαm.trans_lt (hk₀ m (by omega))⟩ ⟨hg0 m, hk₀ m (by omega)⟩ hαm
  rw [hB, ENNReal.le_div_iff_mul_le (.inl (ENNReal.ofReal_pos.2 hb0).ne')
    (.inl ENNReal.ofReal_ne_top)]
  refine le_trans ?_ hτα
  rw [← ENNReal.ofReal_toReal (hrs.trans_le le_top).ne, ← ENNReal.ofReal_toReal hs_top,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  have hmk : ((m - k₀ : ℕ) : ℝ) = m - k₀ := Nat.cast_sub (by omega)
  have hJ'm : (J' : ℝ) ≤ m - k₀ := by
    rw [← hmk]
    exact_mod_cast (by omega : J' ≤ m - k₀)
  rw [hmk]
  nlinarith [ENNReal.toReal_nonneg (a := r)]

end Test

end ProbabilityTheory
