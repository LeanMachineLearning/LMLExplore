/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.CountableCover
public import LMLExplore.EValues.BipolarRate.Design.Algorithm
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
import LMLExplore.Data.ENat.Basic
import LMLExplore.EValues.BipolarRate.Design.Growth
import LMLExplore.EValues.TestBet
import LMLExplore.Probability.HasLaw
import LMLExplore.SequentialLearning.StoppedHistory
import TauCeti.Data.EReal.Operations

/-!
# Lower bounds on the pulls of an informative arm, with the bipolar rate

A bandit `κ` with finitely many arms, observations in any measurable space `𝓧`, and a set `Λ` of
alternative bandits which differ from `κ` at one arm `a` only: the arm `a` is the only informative
one. In the model of [EVR26, Note 47], `a` is the worse arm under `κ` and the better arm under
every `ν ∈ Λ`, so that an algorithm with small regret at `ν` pulls the other arms rarely, and must
pull `a` often enough at `κ` to tell `κ` from `Λ`. The constants of these lower bounds are rates
of evidence against the laws `𝒫 = {ν a | ν ∈ Λ}` of the arm `a` under the alternatives:

* for algorithms with `E_ν[n - N_a(n)] = o(n ^ p)` uniformly over `ν ∈ Λ`, for every `p > 0`,
  `liminf_n E_κ[N_a(n)] / log n ≥ 1 / d`, with `d = bipolarRate (κ a) 𝒫` the bipolar rate;
* for algorithms with `E_ν[n - N_a(n)] = o(n ^ p)` at each `ν ∈ Λ`, for every `p > 0`,
  `liminf_n E_κ[N_a(n)] / log n ≥ 1 / d_σ`, with `d_σ = sigmaBipolarRate (κ a) 𝒫` the rate along
  countable covers of `𝒫`.

These hold on every observation space, while the bound `1 / klInf` of Lai and Robbins and of
Burnetas and Katehakis needs more structure: `d ≤ d_σ ≤ klInf`, and both inequalities can be
strict [EVR26, Notes 44 and 47].

Asymptotic statements are in eventual form, as in `Bandits/LaiRobbins.lean`:
`liminf_n u_n / log n ≥ 1 / d` is `∀ c, c * d < 1 → ∀ᶠ n in atTop, c log n ≤ u_n`, with the
product in `EReal`.

## Main statements

* `LMLExplore.Bandits.klBer_le_integral_pullCount_mul_bipolarRate`: for an event `E` of the
  histories of `n` rounds, with probability at most `δ` under every alternative and at least `q`
  under `κ`, `kl(q, δ) ≤ E_κ[N_a(n)] d`.
* `LMLExplore.Bandits.klBer_le_integral_pullCount_mul_bipolarRate_of_integral_le`: if the
  algorithm pulls the other arms at most `δ n / 2` times in expectation under every alternative
  and `a` at most `η n / 2` times under `κ`, then `kl(1 - η, δ) ≤ E_κ[N_a(n)] d`.
* `LMLExplore.Bandits.eventually_mul_log_le_integral_pullCount_of_forall_le_rpow`: if
  `E_ν[n - N_a(n)] ≤ C n ^ p` for `p < 1`, for every `ν ∈ Λ` and every large `n`, then
  `liminf_n E_κ[N_a(n)] / log n ≥ (1 - p) / d`.
* `LMLExplore.Bandits.eventually_mul_log_le_integral_pullCount_of_bipolarRate`: [EVR26, Note 47,
  Theorem 1.1], the bound `1 / d` for algorithms consistent uniformly over the alternatives.
* `LMLExplore.Bandits.eventually_mul_log_le_integral_pullCount_of_sigmaBipolarRate`: [EVR26,
  Note 47, Theorem 1.2], the bound `1 / d_σ` for algorithms consistent at each alternative.

## Implementation notes

The bet at the horizon `n` is on the event `{2 N_a(n) ≤ n}`: it has probability at most
`δ_n = 2 C n ^ (p - 1)` under every alternative at which `E_ν[n - N_a(n)] ≤ C n ^ p`, by Markov's
inequality, and probability close to `1` under `κ` unless `E_κ[N_a(n)]` is of order `n`. The Wald
inequality with a design (`Learning.IsAlgEnvSeq.eintegral_log_le_designGrowth`) at the stopping time
`τ = n`, with the growth of the designs bounded through the single informative arm
(`ProbabilityTheory.designGrowth_le_mul_bipolarRate_of_forall_ne`), bounds the expected logarithm
`kl(1 - η, δ_n) ≈ (1 - p) log n` of the bet by `E_κ[N_a(n)] d`.

## References

* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 47,
  `results/47-regret-constants-one-sided-models.md`, Theorem 1 and its proof, through Note 41,
  `results/41-several-arms-bipolar-rate.md`, Theorem 1, Proposition 7 and Section 7.
-/

public section

open MeasureTheory ProbabilityTheory Filter Real Learning
open scoped ENNReal

namespace LMLExplore.Bandits

variable {α 𝓧 : Type*} [MeasurableSpace α] {m𝓧 : MeasurableSpace 𝓧} {alg : Algorithm Unit α 𝓧}
  {Λ : Set (Kernel α 𝓧)} {a : α}

/-- The law of the history of `n` rounds, read on the stopped histories: the event `E` of
histories of `n` rounds has, under the law of the history stopped after `n` rounds, the
probability that the history of the first `n` rounds lies in `E`. -/
private lemma stoppedHistMeasure_setOf_fst_eq_image_sigmaMk (env : Environment Unit α 𝓧)
    {n : ℕ} {E : Set (Hist Unit α 𝓧 n)} (hE : MeasurableSet E) :
    stoppedHistMeasure alg env {x | x.1 = n} (Sigma.mk n '' E) =
      trajMeasure alg env (history IT.obs IT.action IT.feedback n ⁻¹' E) := by
  rw [stoppedHistMeasure_setOf_fst_eq, Measure.map_apply
    (measurable_sigmaHistory IT.measurable_obs IT.measurable_action IT.measurable_feedback n)
    ((measurableEmbedding_sigmaMk n).measurableSet_image.2 hE)]
  congr 1
  ext ω
  simp [sigmaHistory_apply]

/-- The laws of the arm `a` under bandits of `Λ` have mass at most one. -/
private lemma measure_univ_le_one_of_mem_image (hΛ : ∀ ν ∈ Λ, IsMarkovKernel ν) :
    ∀ P ∈ (fun ν : Kernel α 𝓧 ↦ ν a) '' Λ, P Set.univ ≤ 1 := by
  rintro _ ⟨ν, hν, rfl⟩
  have := hΛ ν hν
  exact prob_le_one

variable [DecidableEq α]

/-- A bound with a nonpositive constant holds at every horizon. -/
private lemma eventually_mul_log_le_integral_pullCount_of_nonpos {c : ℝ} (hc : c ≤ 0)
    (env : Environment Unit α 𝓧) :
    ∀ᶠ n : ℕ in atTop, c * log n ≤ ∫ ω, (pullCount IT.action a n ω : ℝ) ∂trajMeasure alg env :=
  .of_forall fun n ↦ (mul_nonpos_of_nonpos_of_nonneg hc (log_natCast_nonneg n)).trans
    (integral_nonneg fun _ ↦ Nat.cast_nonneg _)

/-- If `E_ν[n - N_a(n)] ≤ n ^ p` for every `n ≥ N`, with `p > 0`, then
`E_ν[n - N_a(n)] ≤ (N + 1) n ^ p` for every `n`, since `E_ν[n - N_a(n)] ≤ n`. -/
private lemma integral_sub_pullCount_le_mul_rpow [MeasurableSingletonClass α]
    {P : Measure (ℕ → Round Unit α 𝓧)} [IsProbabilityMeasure P] {p : ℝ} (hp : 0 < p) {N : ℕ}
    (hN : ∀ n ≥ N, ∫ ω, ((n : ℝ) - pullCount IT.action a n ω) ∂P ≤ (n : ℝ) ^ p) (n : ℕ) :
    ∫ ω, ((n : ℝ) - pullCount IT.action a n ω) ∂P ≤ ((N + 1 : ℕ) : ℝ) * (n : ℝ) ^ p := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [zero_rpow hp.ne']
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ p := one_le_rpow (by exact_mod_cast hn) hp.le
  rcases le_or_gt N n with hNn | hNn
  · exact (hN n hNn).trans (le_mul_of_one_le_left (by positivity) (by simp))
  -- for `n < N`, `E_ν[n - N_a(n)] ≤ n ≤ N + 1 ≤ (N + 1) n ^ p`
  have hle : ∫ ω, ((n : ℝ) - pullCount IT.action a n ω) ∂P ≤ n :=
    (integral_mono ((integrable_const _).sub (integrable_pullCount IT.measurable_action a n))
      (integrable_const _) fun ω ↦ sub_le_self _ (Nat.cast_nonneg _)).trans_eq (by simp)
  refine hle.trans ((le_mul_of_one_le_right (by positivity) hn1).trans' ?_)
  exact_mod_cast (hNn.trans (Nat.lt_succ_self N)).le

variable [Finite α] [StandardBorelSpace α] {κ : Kernel α 𝓧} [IsMarkovKernel κ]

/-- **Change of measure with the bipolar rate, at a fixed horizon.** Let the bandits of a
nonempty set `Λ` differ from `κ` at the arm `a` only, and let `E` be an event of the histories of
`n` rounds, of probability at most `δ` under every `ν ∈ Λ` and at least `q` under `κ`, with
`0 < δ ≤ q < 1`. Then `kl(q, δ) ≤ E_κ[N_a(n)] d`, with `d` the bipolar rate of `κ a` against the
laws `ν a` of the arm `a` under the alternatives. The product is in `EReal`.

For one alternative `ν`, `d = klDiv (κ a) (ν a)` and this is the classical bound of the
data-processing inequality and of the divergence decomposition. -/
theorem klBer_le_integral_pullCount_mul_bipolarRate (hΛ : ∀ ν ∈ Λ, IsMarkovKernel ν)
    (hne : Λ.Nonempty) (hΛa : ∀ ν ∈ Λ, ∀ b ≠ a, ν b = κ b) {n : ℕ}
    {E : Set (Hist Unit α 𝓧 n)} (hE : MeasurableSet E) {δ q : ℝ} (hδ : 0 < δ) (hδq : δ ≤ q)
    (hq : q < 1)
    (hEΛ : ∀ ν ∈ Λ, ∀ [IsMarkovKernel ν], trajMeasure alg (Environment.bandit ν)
      (history IT.obs IT.action IT.feedback n ⁻¹' E) ≤ ENNReal.ofReal δ)
    (hEκ : ENNReal.ofReal q ≤ trajMeasure alg (Environment.bandit κ)
      (history IT.obs IT.action IT.feedback n ⁻¹' E)) :
    (klBer q δ : EReal) ≤ ((∫ ω, (pullCount IT.action a n ω : ℝ)
      ∂trajMeasure alg (Environment.bandit κ) : ℝ) : EReal) *
        bipolarRate (κ a) ((fun ν ↦ ν a) '' Λ) := by
  have := Fintype.ofFinite α
  set S : Set (Σ m, Hist Unit α 𝓧 m) := {x | x.1 = n}
  have hS : MeasurableSet S := measurable_sigma_fst (measurableSet_singleton n)
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit κ)
  -- the test `φ`, the indicator of `E` on the histories of `n` rounds, and the bet `G` on it
  have hEm : MeasurableSet (Sigma.mk n '' E) :=
    (measurableEmbedding_sigmaMk n).measurableSet_image.2 hE
  set φ : (Σ m, Hist Unit α 𝓧 m) → ℝ≥0∞ := (Sigma.mk n '' E).indicator 1
  have hφm : Measurable φ := measurable_one.indicator hEm
  have hφ1 (x : Σ m, Hist Unit α 𝓧 m) : φ x ≤ 1 :=
    Set.indicator_apply_le' (fun _ ↦ le_rfl) fun _ ↦ zero_le_one
  have hφ (env : Environment Unit α 𝓧) : ∫⁻ x, φ x ∂stoppedHistMeasure alg env S =
      trajMeasure alg env (history IT.obs IT.action IT.feedback n ⁻¹' E) := by
    rw [lintegral_indicator_one hEm, stoppedHistMeasure_setOf_fst_eq_image_sigmaMk env hE]
  set G := testBet δ q φ
  have hGm : Measurable G := hφm.testBet
  -- `G` is an e-variable at the time `n` against the alternatives
  have hGΛ : ∀ (ν : Kernel α 𝓧) [IsMarkovKernel ν], ν ∈ Λ →
      ∫⁻ x in S, G x ∂stoppedHistMeasure alg (Environment.bandit ν) S ≤ 1 := fun ν _ hν ↦
    (setLIntegral_le_lintegral _ _).trans (lintegral_testBet_le_one hφm hφ1
      ⟨hδ, hδq.trans_lt hq⟩ hδq hq.le prob_le_one ((hφ _).trans_le (hEΛ ν hν)))
  have hτ : ∫⁻ ω, ENat.toENNReal (hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0 ω)
      ∂trajMeasure alg (Environment.bandit κ) ≠ ⊤ := by
    simp only [S, hittingAfter_sigmaHistory_setOf_fst_eq, lintegral_const, measure_univ,
      mul_one]
    exact ENat.toENNReal_ne_top.2 WithTop.coe_ne_top
  have hlog : AEMeasurable (fun x ↦ ENNReal.log (G x))
      (stoppedHistMeasure alg (Environment.bandit κ) S) :=
    (ENNReal.measurable_log.comp hGm).aemeasurable
  -- `kl(q, δ) ≤ 𝔼_κ[log G] ≤ G'(𝔼_κ[N n]) ≤ 𝔼_κ[N_a n] d`
  calc (klBer q δ : EReal)
      ≤ ∫ᵉ x, ENNReal.log (G x) ∂stoppedHistMeasure alg (Environment.bandit κ) S :=
        klBer_le_eintegral_log_testBet hφm hφ1 hδ hδq hq ((hφ _).symm ▸ hEκ)
    _ = ∫ᵉ ω, ENNReal.log (G (stoppedValue (sigmaHistory IT.obs IT.action IT.feedback)
          (hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0) ω))
            ∂trajMeasure alg (Environment.bandit κ) :=
        ((hseq.hasLaw_stoppedValue_sigmaHistory hS).eintegral_comp hlog).symm
    _ ≤ designGrowth (fun b ↦ κ b) ((fun (ν : Kernel α 𝓧) b ↦ ν b) '' Λ) fun b ↦
          (∫⁻ ω, (pullCount IT.action b
            (hittingAfter (sigmaHistory IT.obs IT.action IT.feedback) S 0 ω).untopA ω : ℝ≥0∞)
              ∂trajMeasure alg (Environment.bandit κ)).toNNReal :=
        hseq.eintegral_log_le_designGrowth hΛ hS hGm hGΛ hτ
    _ ≤ _ := (designGrowth_le_mul_bipolarRate_of_forall_ne
          (by rintro _ ⟨ν, hν, rfl⟩; have := hΛ ν hν; exact prob_le_one) (hne.image _)
          (by rintro _ ⟨ν, hν, rfl⟩ b hb; exact hΛa ν hν b hb) _).trans_eq ?_
  -- the expected number of pulls of `a`, as a Lebesgue and as a Bochner integral
  rw [Set.image_image]
  congr 3
  simp only [S, hittingAfter_sigmaHistory_setOf_fst_eq, WithTop.untopA_natCast,
    ENNReal.coe_toNNReal_eq_toReal]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ Nat.cast_nonneg _)
    (measurable_from_nat.comp (measurable_pullCount IT.measurable_action a n)).aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_natCast]

/-- **The bet on the pulls of the informative arm, at a fixed horizon** [EVR26, Note 41, proof of
Proposition 7]. Let the bandits of a nonempty set `Λ` differ from `κ` at the arm `a` only. If, at
the horizon `n ≥ 1`, the algorithm pulls the arms other than `a` at most `δ n / 2` times in
expectation under every `ν ∈ Λ`, and `a` at most `η n / 2` times under `κ`, with `0 < δ` and
`0 < η ≤ 1 - δ`, then `kl(1 - η, δ) ≤ E_κ[N_a(n)] d`, with `d` the bipolar rate of `κ a` against
the laws `ν a` of the arm `a` under the alternatives. The product is in `EReal`. -/
theorem klBer_le_integral_pullCount_mul_bipolarRate_of_integral_le
    (hΛ : ∀ ν ∈ Λ, IsMarkovKernel ν) (hne : Λ.Nonempty) (hΛa : ∀ ν ∈ Λ, ∀ b ≠ a, ν b = κ b)
    {n : ℕ} (hn : 0 < n) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hδη : δ ≤ 1 - η)
    (hΛn : ∀ ν ∈ Λ, ∀ [IsMarkovKernel ν], ∫ ω, ((n : ℝ) - pullCount IT.action a n ω)
      ∂trajMeasure alg (Environment.bandit ν) ≤ δ * n / 2)
    (hκn : ∫ ω, (pullCount IT.action a n ω : ℝ) ∂trajMeasure alg (Environment.bandit κ) ≤
      η * n / 2) :
    (klBer (1 - η) δ : EReal) ≤ ((∫ ω, (pullCount IT.action a n ω : ℝ)
      ∂trajMeasure alg (Environment.bandit κ) : ℝ) : EReal) *
        bipolarRate (κ a) ((fun ν ↦ ν a) '' Λ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- the event `E = {2 N_a(n) ≤ n}` of the histories of `n` rounds
  set E : Set (Hist Unit α 𝓧 n) := {h | 2 * pullCount' n h a ≤ n}
  have hE : MeasurableSet E := ((measurable_pullCount' n a).const_mul 2) measurableSet_Iic
  have hpre : history IT.obs IT.action IT.feedback n ⁻¹' E =
      {ω | 2 * pullCount IT.action a n ω ≤ n} := by
    ext ω
    simp only [Set.mem_preimage, E, Set.mem_ofPred_eq]
    rw [pullCount_eq_pullCount' (O := IT.obs) (R' := IT.feedback)]
  have hpm : MeasurableSet {ω : ℕ → Round Unit α 𝓧 | 2 * pullCount IT.action a n ω ≤ n} :=
    ((measurable_pullCount IT.measurable_action a n).const_mul 2) measurableSet_Iic
  refine klBer_le_integral_pullCount_mul_bipolarRate hΛ hne hΛa hE hδ hδη (by linarith)
    (fun ν hν _ ↦ ?_) ?_
  · -- under the alternatives, `E` has probability at most `δ`, by Markov's inequality
    have hsub : {ω : ℕ → Round Unit α 𝓧 | 2 * pullCount IT.action a n ω ≤ n} ⊆
        {ω | (n : ℝ) / 2 ≤ (n : ℝ) - pullCount IT.action a n ω} := fun ω hω ↦ by
      rw [Set.mem_ofPred_eq] at hω ⊢
      have : ((2 * pullCount IT.action a n ω : ℕ) : ℝ) ≤ n := Nat.cast_le.2 hω
      push_cast at this
      linarith
    have hM := mul_meas_ge_le_integral_of_nonneg (μ := trajMeasure alg (Environment.bandit ν))
      (ae_of_all _ fun ω ↦ sub_nonneg.2 (Nat.cast_le.2 (pullCount_le a n ω)))
      ((integrable_const _).sub (integrable_pullCount IT.measurable_action a n)) ((n : ℝ) / 2)
    rw [hpre, ← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ((measureReal_mono hsub).trans
      (le_of_mul_le_mul_left ?_ (half_pos hn0)))
    linarith [hΛn ν hν]
  · -- under `κ`, `E` has probability at least `1 - η`, by Markov's inequality
    have hsub : {ω : ℕ → Round Unit α 𝓧 | 2 * pullCount IT.action a n ω ≤ n}ᶜ ⊆
        {ω | (n : ℝ) / 2 ≤ (pullCount IT.action a n ω : ℝ)} := fun ω hω ↦ by
      rw [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
      rw [Set.mem_ofPred_eq]
      have : (n : ℝ) < ((2 * pullCount IT.action a n ω : ℕ) : ℝ) := Nat.cast_lt.2 hω
      push_cast at this
      linarith
    have hM := mul_meas_ge_le_integral_of_nonneg (μ := trajMeasure alg (Environment.bandit κ))
      (ae_of_all _ fun ω ↦ Nat.cast_nonneg _) (integrable_pullCount IT.measurable_action a n)
      ((n : ℝ) / 2)
    have h1 : (trajMeasure alg (Environment.bandit κ)).real
        {ω | (n : ℝ) / 2 ≤ (pullCount IT.action a n ω : ℝ)} ≤ η :=
      le_of_mul_le_mul_left (by linarith) (half_pos hn0)
    have hc := (measureReal_mono hsub).trans h1
    rw [probReal_compl_eq_one_sub hpm] at hc
    rw [hpre, ← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ### Asymptotic lower bounds -/

/-- **The lower bound on the pulls of the informative arm, with the bipolar rate**
[EVR26, Note 47, proof of Theorem 1, (1)]. Let the bandits of `Λ` differ from `κ` at the arm `a`
only, and suppose that, for some `p < 1` and `C`, the algorithm pulls the other arms at most
`C n ^ p` times in expectation under every `ν ∈ Λ`, for every large horizon `n`:
`E_ν[n - N_a(n)] ≤ C n ^ p`. Then `liminf_n E_κ[N_a(n)] / log n ≥ (1 - p) / d`, with `d` the
bipolar rate of `κ a` against the laws `ν a` of the arm `a` under the alternatives: for every
real `c` with `c d < 1 - p`, eventually `c log n ≤ E_κ[N_a(n)]`. -/
theorem eventually_mul_log_le_integral_pullCount_of_forall_le_rpow
    (hΛ : ∀ ν ∈ Λ, IsMarkovKernel ν) (hΛa : ∀ ν ∈ Λ, ∀ b ≠ a, ν b = κ b) {p C : ℝ} (hp : p < 1)
    (hC : ∀ᶠ n : ℕ in atTop, ∀ ν ∈ Λ, ∀ [IsMarkovKernel ν],
      ∫ ω, ((n : ℝ) - pullCount IT.action a n ω) ∂trajMeasure alg (Environment.bandit ν) ≤
        C * (n : ℝ) ^ p)
    {c : ℝ} (hc : (c : EReal) * bipolarRate (κ a) ((fun ν ↦ ν a) '' Λ) < ((1 - p : ℝ) : EReal)) :
    ∀ᶠ n : ℕ in atTop, c * log n ≤
      ∫ ω, (pullCount IT.action a n ω : ℝ) ∂trajMeasure alg (Environment.bandit κ) := by
  rcases le_or_gt c 0 with hc0 | hc0
  · exact eventually_mul_log_le_integral_pullCount_of_nonpos hc0 _
  -- the rate is a real `r ≥ 0` with `c r < 1 - p`, so that `Λ` is nonempty
  have hΛ1 := measure_univ_le_one_of_mem_image (a := a) hΛ
  set r := (bipolarRate (κ a) ((fun ν ↦ ν a) '' Λ)).toReal
  have hdr := coe_toReal_bipolarRate hΛ1 (EReal.ne_top_of_coe_mul_ne_top hc0 (ne_top_of_lt hc))
  have hr : 0 ≤ r := EReal.toReal_nonneg (bipolarRate_nonneg _ hΛ1)
  have hcr : c * r < 1 - p := by
    rw [← hdr, ← EReal.coe_mul] at hc
    exact_mod_cast hc
  have hne : Λ.Nonempty := Set.ne_empty_iff_nonempty.1 fun h ↦ by simp [h] at hdr
  -- a margin `η` with `c r + ε ≤ (1 - η) (1 - p)`, and a positive constant `C' ≥ C`
  set ε := (1 - p - c * r) / 2 with hε_def
  have hε : 0 < ε := by linarith
  set η := min (1 / 2) (ε / (1 - p))
  have hη0 : 0 < η := lt_min (by norm_num) (div_pos hε (by linarith))
  have hη2 : η ≤ 1 / 2 := min_le_left _ _
  have hηp : η * (1 - p) ≤ ε := (le_div_iff₀ (by linarith)).1 (min_le_right _ _)
  set C' := max C 1
  have hC' : 0 < C' := lt_max_of_lt_right one_pos
  -- the horizons `n` at which the bound is proved
  have h1 : ∀ᶠ n : ℕ in atTop, 2 * C' * (n : ℝ) ^ (p - 1) ≤ η := by
    have h := ((tendsto_rpow_neg_atTop (by linarith : 0 < 1 - p)).comp
      tendsto_natCast_atTop_atTop).const_mul (2 * C')
    simp only [mul_zero, neg_sub] at h
    exact ((tendsto_order.1 h).2 η hη0).mono fun n hn ↦ hn.le
  have h2 : ∀ᶠ n : ℕ in atTop, 2 * c * (log n / n) ≤ η := by
    have h := (isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul (2 * c)
    simp only [mul_zero] at h
    exact ((tendsto_order.1 h).2 η hη0).mono fun n hn ↦ hn.le
  have h3 : ∀ᶠ n : ℕ in atTop, (1 - η) * log (2 * C') + log 2 < ε * log n :=
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hε).eventually_gt_atTop _
  filter_upwards [hC, h1, h2, h3, eventually_ge_atTop 1] with n hCn h1n h2n h3n hn
  by_contra! hlt
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set δ := 2 * C' * (n : ℝ) ^ (p - 1) with hδ_def
  have hδ : 0 < δ := by positivity
  have hδ1 : δ < 1 := by linarith
  -- the other arms are pulled at most `δ n / 2` times under the alternatives, and `a` at most
  -- `η n / 2` times under `κ`, so that `kl(1 - η, δ) ≤ E_κ[N_a(n)] r`
  have hΛn : ∀ ν ∈ Λ, ∀ [IsMarkovKernel ν], ∫ ω, ((n : ℝ) - pullCount IT.action a n ω)
      ∂trajMeasure alg (Environment.bandit ν) ≤ δ * n / 2 := by
    intro ν hν _
    rw [hδ_def, rpow_sub_one hn0.ne', show 2 * C' * ((n : ℝ) ^ p / n) * n / 2 = C' * n ^ p by
      field_simp]
    exact (hCn ν hν).trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (rpow_nonneg hn0.le p))
  have hκn : ∫ ω, (pullCount IT.action a n ω : ℝ) ∂trajMeasure alg (Environment.bandit κ) ≤
      η * n / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hn0] at h2n
    rw [le_div_iff₀ two_pos]
    linarith
  have hkl := klBer_le_integral_pullCount_mul_bipolarRate_of_integral_le hΛ hne hΛa hn hδ hη0
    (by linarith) hΛn hκn
  rw [← hdr, ← EReal.coe_mul, klBer_eq_ofReal_klBerReal ⟨by linarith, by linarith⟩
    ⟨hδ.le, hδ1.le⟩ (klBer_ne_top ⟨hδ, hδ1⟩), EReal.coe_ennreal_ofReal,
    EReal.coe_le_coe_iff] at hkl
  have hent := mul_neg_log_le_klBerReal_add_log_two (p := 1 - η) ⟨by linarith, by linarith⟩
    ⟨hδ, hδ1⟩
  -- `log δ = log (2 C') - (1 - p) log n`, against the choice of `n`
  rw [log_mul (by positivity) (by positivity), log_rpow hn0] at hent
  have hL := log_natCast_nonneg n
  have hXr := mul_le_mul_of_nonneg_right hlt.le hr
  have hηL := mul_le_mul_of_nonneg_right hηp hL
  have hεL : ε * log n = (1 - p - c * r) / 2 * log n := by rw [hε_def]
  linarith [(le_max_left _ _).trans hkl]

/-- **The lower bound `1 / d` for algorithms consistent uniformly over the alternatives**
[EVR26, Note 47, Theorem 1.1]. Let the bandits of `Λ` differ from `κ` at the arm `a` only, and
suppose that the algorithm pulls the other arms `o(n ^ p)` times in expectation, uniformly over
`ν ∈ Λ`, for every `p > 0`: for every `p > 0`, eventually `E_ν[n - N_a(n)] ≤ n ^ p` for all
`ν ∈ Λ`. Then `liminf_n E_κ[N_a(n)] / log n ≥ 1 / d`, with `d` the bipolar rate of `κ a` against
the laws `ν a` of the arm `a` under the alternatives: for every real `c` with `c d < 1`,
eventually `c log n ≤ E_κ[N_a(n)]`. No hypothesis at `κ` is needed. -/
theorem eventually_mul_log_le_integral_pullCount_of_bipolarRate
    (hΛ : ∀ ν ∈ Λ, IsMarkovKernel ν) (hΛa : ∀ ν ∈ Λ, ∀ b ≠ a, ν b = κ b)
    (halg : ∀ p : ℝ, 0 < p → ∀ᶠ n : ℕ in atTop, ∀ ν ∈ Λ, ∀ [IsMarkovKernel ν],
      ∫ ω, ((n : ℝ) - pullCount IT.action a n ω) ∂trajMeasure alg (Environment.bandit ν) ≤
        (n : ℝ) ^ p)
    {c : ℝ} (hc : (c : EReal) * bipolarRate (κ a) ((fun ν ↦ ν a) '' Λ) < 1) :
    ∀ᶠ n : ℕ in atTop, c * log n ≤
      ∫ ω, (pullCount IT.action a n ω : ℝ) ∂trajMeasure alg (Environment.bandit κ) := by
  rcases le_or_gt c 0 with hc0 | hc0
  · exact eventually_mul_log_le_integral_pullCount_of_nonpos hc0 _
  have hΛ1 := measure_univ_le_one_of_mem_image (a := a) hΛ
  set r := (bipolarRate (κ a) ((fun ν ↦ ν a) '' Λ)).toReal
  have hdr := coe_toReal_bipolarRate hΛ1 (EReal.ne_top_of_coe_mul_ne_top hc0 (ne_top_of_lt hc))
  have hr : 0 ≤ r := EReal.toReal_nonneg (bipolarRate_nonneg _ hΛ1)
  have hcr : c * r < 1 := by
    rw [← hdr, ← EReal.coe_mul] at hc
    exact_mod_cast hc
  -- the exponent `p = (1 - c r) / 2 ∈ (0, 1)`, with `c r < 1 - p`
  refine eventually_mul_log_le_integral_pullCount_of_forall_le_rpow hΛ hΛa (p := (1 - c * r) / 2)
    (C := 1) (by linarith [mul_nonneg hc0.le hr]) ((halg _ (by linarith)).mono fun n hn ν hν _ ↦
      (hn ν hν).trans_eq (one_mul _).symm) ?_
  rw [← hdr, ← EReal.coe_mul, EReal.coe_lt_coe_iff]
  linarith

/-- **The lower bound `1 / d_σ` for algorithms consistent at each alternative**
[EVR26, Note 47, Theorem 1.2]. Let the bandits of `Λ` differ from `κ` at the arm `a` only, and
suppose that, at each `ν ∈ Λ`, the algorithm pulls the other arms `o(n ^ p)` times in expectation,
for every `p > 0`: for every `ν ∈ Λ` and every `p > 0`, eventually `E_ν[n - N_a(n)] ≤ n ^ p`. Then
`liminf_n E_κ[N_a(n)] / log n ≥ 1 / d_σ`, with `d_σ` the bipolar rate along countable covers of
`κ a` against the laws `ν a` of the arm `a` under the alternatives
(`ProbabilityTheory.sigmaBipolarRate`): for every real `c` with `c d_σ < 1`, eventually
`c log n ≤ E_κ[N_a(n)]`. Since `d ≤ d_σ`, the constant is smaller than that of uniformly
consistent algorithms, `eventually_mul_log_le_integral_pullCount_of_bipolarRate`. -/
theorem eventually_mul_log_le_integral_pullCount_of_sigmaBipolarRate
    (hΛ : ∀ ν ∈ Λ, IsMarkovKernel ν) (hΛa : ∀ ν ∈ Λ, ∀ b ≠ a, ν b = κ b)
    (halg : ∀ ν ∈ Λ, ∀ [IsMarkovKernel ν], ∀ p : ℝ, 0 < p → ∀ᶠ n : ℕ in atTop,
      ∫ ω, ((n : ℝ) - pullCount IT.action a n ω) ∂trajMeasure alg (Environment.bandit ν) ≤
        (n : ℝ) ^ p)
    {c : ℝ} (hc : (c : EReal) * sigmaBipolarRate (κ a) ((fun ν ↦ ν a) '' Λ) < 1) :
    ∀ᶠ n : ℕ in atTop, c * log n ≤
      ∫ ω, (pullCount IT.action a n ω : ℝ) ∂trajMeasure alg (Environment.bandit κ) := by
  rcases le_or_gt c 0 with hc0 | hc0
  · exact eventually_mul_log_le_integral_pullCount_of_nonpos hc0 _
  have hds0 : 0 ≤ sigmaBipolarRate (κ a) ((fun ν ↦ ν a) '' Λ) :=
    (bipolarRate_nonneg _ (measure_univ_le_one_of_mem_image hΛ)).trans
      (bipolarRate_le_sigmaBipolarRate _ _)
  set s := (sigmaBipolarRate (κ a) ((fun ν ↦ ν a) '' Λ)).toReal
  have hds : (s : EReal) = sigmaBipolarRate (κ a) ((fun ν ↦ ν a) '' Λ) :=
    EReal.coe_toReal (EReal.ne_top_of_coe_mul_ne_top hc0 (ne_top_of_lt hc))
      (ne_bot_of_le_ne_bot EReal.zero_ne_bot hds0)
  have hs : 0 ≤ s := EReal.toReal_nonneg hds0
  have hcs : c * s < 1 := by
    rw [← hds, ← EReal.coe_mul] at hc
    exact_mod_cast hc
  -- a real `t > s` with `c t < 1`, and the exponent `p = (1 - c t) / 2 ∈ (0, 1)`
  set t := s + (1 - c * s) / (2 * c) with ht
  have hst : s < t := lt_add_of_pos_right s (div_pos (by linarith) (by positivity))
  have hct : c * t = (1 + c * s) / 2 := by
    rw [ht]
    field_simp
    ring
  set p := (1 - c * t) / 2 with hp_def
  have hp0 : 0 < p := by
    rw [hp_def]
    linarith
  have hp1 : p < 1 := by
    rw [hp_def]
    linarith [mul_nonneg hc0.le hs]
  -- the alternatives at which `E_ν[n - N_a(n)] ≤ m n ^ p` for every `n` cover `Λ`
  set Λ' : ℕ → Set (Kernel α 𝓧) := fun m ↦ {ν ∈ Λ | ∀ [IsMarkovKernel ν], ∀ n : ℕ,
    ∫ ω, ((n : ℝ) - pullCount IT.action a n ω) ∂trajMeasure alg (Environment.bandit ν) ≤
      m * (n : ℝ) ^ p}
  have hcover : (fun ν ↦ ν a) '' Λ ⊆ ⋃ m, (fun ν ↦ ν a) '' Λ' m := by
    rintro _ ⟨ν, hν, rfl⟩
    have := hΛ ν hν
    obtain ⟨N, hN⟩ := eventually_atTop.1 (halg ν hν p hp0)
    exact Set.mem_iUnion.2 ⟨N + 1, ν, ⟨hν, fun n ↦ integral_sub_pullCount_le_mul_rpow hp0 hN n⟩,
      rfl⟩
  -- some piece has a bipolar rate below `t`, and the bound with the bipolar rate holds on it
  obtain ⟨m, hm⟩ := iInf_lt_iff.1 ((iInf_bipolarRate_le_sigmaBipolarRate hcover).trans_lt
    (hds.symm ▸ EReal.coe_lt_coe_iff.2 hst))
  refine eventually_mul_log_le_integral_pullCount_of_forall_le_rpow (Λ := Λ' m)
    (fun ν hν ↦ hΛ ν hν.1) (fun ν hν ↦ hΛa ν hν.1) (p := p) (C := m) hp1
    (.of_forall fun n ν hν _ ↦ hν.2 n) ?_
  calc (c : EReal) * bipolarRate (κ a) ((fun ν ↦ ν a) '' Λ' m) ≤ (c : EReal) * t :=
        mul_le_mul_of_nonneg_left hm.le (EReal.coe_nonneg.2 hc0.le)
    _ < ((1 - p : ℝ) : EReal) := by
        rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, hp_def]
        linarith

end LMLExplore.Bandits
