/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Correctness
public import LMLExplore.SequentialLearning.DivergenceDecomposition
public import LMLExplore.SequentialLearning.Wald

/-!
# Sample complexity of identification algorithms and Wald's identities

The *sample complexity* of an identification algorithm `A` in an environment `env` is the expected
number of rounds it plays, `𝔼[τ]`, where `τ` is its stopping time. Since the stopping time is a
measurable function of the trajectory, whose law `trajMeasure A.alg env` is determined by the
sampling rule and the environment, it is the same along every algorithm-environment sequence of
the sampling rule.

For finitely many actions, *Wald's identities* express the expectation of a sum over the rounds
before a random time `τ` through the expected numbers of pulls `N_a(τ)` of the actions:
`𝔼[τ] = ∑ a, 𝔼[N_a(τ)]` when `τ` is almost surely finite
(`LMLExplore.lintegral_toENNReal_eq_sum_lintegral_pullCount`), and
`𝔼[∑_{t < τ} f(A_t)] = ∑ a, 𝔼[N_a(τ)] f(a)` for `f ≥ 0` (`LMLExplore.sum_lintegral_pullCount_mul`).
Both hold for any measurable random time and are in
`LMLExplore/SequentialLearning/DivergenceDecomposition.lean`. For the rewards `Y_t` of a stationary
environment `ν` with integrable reward distributions of means `μ_a`, and a stopping time `τ` with
`𝔼[τ] < ∞`, Wald's identity `𝔼[∑_{t < τ} Y_t] = ∑ a, 𝔼[N_a(τ)] μ_a`
(`Learning.IsAlgEnvSeq.integral_sum_feedback_eq_sum_integral_pullCount_mul`) is in
`LMLExplore/SequentialLearning/Wald.lean`. This file applies these identities at the stopping
time of an identification algorithm.

## Main definitions

* `LMLExplore.Identification.expectedStoppingTime A env`: the expected number of rounds `𝔼[τ]`
  played by `A` in `env`, an `ℝ≥0∞`-valued lower integral under `trajMeasure A.alg env`.
* `LMLExplore.Identification.expectedPullProportion A env a`: the expected proportion
  `𝔼[N_a(τ)] / 𝔼[τ]` of the rounds at which the action `a` is played.

## Main statements

* `Learning.IdentAlg.lintegral_stoppingTime_eq_expectedStoppingTime`: the expected stopping time
  along any algorithm-environment sequence of the sampling rule is `expectedStoppingTime A env`.
* `LMLExplore.Identification.StopsAS.of_expectedStoppingTime_ne_top`: an algorithm with
  `𝔼[τ] < ∞` stops almost surely.
* `Learning.IdentAlg.lintegral_stoppingTime_eq_sum_lintegral_pullCount`,
  `LMLExplore.Identification.expectedStoppingTime_eq_sum_lintegral_pullCount`: Wald's identity
  `𝔼[τ] = ∑ a, 𝔼[N_a(τ)]` at the stopping time `τ` of an identification algorithm that stops
  almost surely, along any algorithm-environment sequence and on the canonical space.
* `Learning.IdentAlg.integral_sum_feedback_eq_sum_integral_pullCount_mul`: Wald's identity for the
  rewards, `𝔼[∑_{t < τ} Y_t] = ∑ a, 𝔼[N_a(τ)] μ_a`, at the stopping time `τ` of an identification
  algorithm with `𝔼[τ] < ∞` in a stationary environment with integrable reward distributions.
* `LMLExplore.Identification.expectedStoppingTime_mul_ofReal_expectedPullProportion`,
  `LMLExplore.Identification.sum_expectedPullProportion`: if `𝔼[τ] < ∞`, then
  `𝔼[τ] (𝔼[N_a(τ)] / 𝔼[τ]) = 𝔼[N_a(τ)]`, and if moreover `𝔼[τ] ≠ 0`, the expected proportions of
  pulls sum to `1`.

## References

* E. Kaufmann, O. Cappé and A. Garivier, *On the complexity of best-arm identification in
  multi-armed bandit models*, JMLR 17 (2016).
* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Chapter 33.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset

open scoped ENNReal

variable {𝓞 𝓐 𝓨 𝓓 Ω : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓓 : MeasurableSpace 𝓓} {mΩ : MeasurableSpace Ω}
  {A : IdentAlg 𝓞 𝓐 𝓨 𝓓} {env : Environment 𝓞 𝓐 𝓨}
  {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {P : Measure Ω}

/-! ### The expected stopping time -/

namespace LMLExplore.Identification

/-- The expected number of rounds `𝔼[τ]` played by the identification algorithm `A` in the
environment `env`: the lower integral of its stopping time under `trajMeasure A.alg env`. -/
noncomputable def expectedStoppingTime (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (env : Environment 𝓞 𝓐 𝓨) :
    ℝ≥0∞ :=
  ∫⁻ ω, (A.stoppingTime IT.obs IT.action IT.feedback ω : ℝ≥0∞) ∂(trajMeasure A.alg env)

/-- The defining formula of `expectedStoppingTime`. -/
lemma expectedStoppingTime_def (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (env : Environment 𝓞 𝓐 𝓨) :
    expectedStoppingTime A env =
      ∫⁻ ω, (A.stoppingTime IT.obs IT.action IT.feedback ω : ℝ≥0∞) ∂(trajMeasure A.alg env) :=
  (rfl)

/-- An identification algorithm with a finite expected stopping time in `env` stops almost surely
in `env`. -/
lemma StopsAS.of_expectedStoppingTime_ne_top (h : expectedStoppingTime A env ≠ ∞) :
    StopsAS A env := by
  rw [stopsAS_iff_ae_stoppingTime_ne_top (IT.isAlgEnvSeq_trajMeasure A.alg env)]
  filter_upwards [ae_lt_top (Measurable.of_discrete.comp (A.measurable_stoppingTime
    IT.measurable_obs IT.measurable_action IT.measurable_feedback)) h] with ω hω
  simpa using hω.ne

end LMLExplore.Identification

namespace Learning.IdentAlg

open LMLExplore.Identification

/-- The expected stopping time of `A` along any algorithm-environment sequence of its sampling
rule in `env` is `expectedStoppingTime A env`. -/
lemma lintegral_stoppingTime_eq_expectedStoppingTime [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O X Y A.alg env P) :
    ∫⁻ ω, (A.stoppingTime O X Y ω : ℝ≥0∞) ∂P = expectedStoppingTime A env :=
  h.hasLaw_trajectory.lintegral_comp
    (f := fun ω ↦ (A.stoppingTime IT.obs IT.action IT.feedback ω : ℝ≥0∞))
    (Measurable.of_discrete.comp (A.measurable_stoppingTime IT.measurable_obs
      IT.measurable_action IT.measurable_feedback)).aemeasurable

end Learning.IdentAlg

/-! ### Wald's identities -/

namespace Learning.IdentAlg

open LMLExplore.Identification

variable [Fintype 𝓐] [DecidableEq 𝓐] [MeasurableSingletonClass 𝓐]

/-- **Wald's identity at the stopping time.** If `A` stops almost surely in `env`, then along any
algorithm-environment sequence of its sampling rule, `𝔼[τ] = ∑ a, 𝔼[N_a(τ)]`, where `N_a(τ)` is
the number of pulls of the action `a` before the stopping time `τ`. -/
lemma lintegral_stoppingTime_eq_sum_lintegral_pullCount [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O X Y A.alg env P) (hA : StopsAS A env) :
    ∫⁻ ω, (A.stoppingTime O X Y ω : ℝ≥0∞) ∂P =
      ∑ a, ∫⁻ ω, (pullCount X a (A.stoppingTime O X Y ω).toNat ω : ℝ≥0∞) ∂P :=
  LMLExplore.lintegral_toENNReal_eq_sum_lintegral_pullCount h.measurable_action
    (A.measurable_stoppingTime h.measurable_obs h.measurable_action h.measurable_feedback)
    (hA.ae_stoppingTime_ne_top h)

end Learning.IdentAlg

namespace LMLExplore.Identification

variable [Fintype 𝓐] [DecidableEq 𝓐] [MeasurableSingletonClass 𝓐]

/-- **Wald's identity for the expected stopping time.** If `A` stops almost surely in `env`, then
`expectedStoppingTime A env = ∑ a, 𝔼[N_a(τ)]`, the expectations being under the canonical law
`trajMeasure A.alg env` of the trajectory. -/
lemma expectedStoppingTime_eq_sum_lintegral_pullCount (hA : StopsAS A env) :
    expectedStoppingTime A env =
      ∑ a, ∫⁻ ω, (pullCount IT.action a
        (A.stoppingTime IT.obs IT.action IT.feedback ω).toNat ω : ℝ≥0∞) ∂(trajMeasure A.alg env) :=
  IdentAlg.lintegral_stoppingTime_eq_sum_lintegral_pullCount
    (IT.isAlgEnvSeq_trajMeasure A.alg env) hA

/-! ### The expected proportions of pulls -/

omit [Fintype 𝓐] [MeasurableSingletonClass 𝓐] in
variable (A env) in
/-- The expected proportion `𝔼[N_a(τ)] / 𝔼[τ]` of the rounds played by `A` in `env` at which the
action `a` is played, where `N_a(τ)` is the number of pulls of `a` before the stopping time `τ`.
It is `0` when `𝔼[τ]` is `0` or `∞`. -/
noncomputable def expectedPullProportion (a : 𝓐) : ℝ :=
  ((∫⁻ ω, (pullCount IT.action a (A.stoppingTime IT.obs IT.action IT.feedback ω).toNat ω : ℝ≥0∞)
    ∂(trajMeasure A.alg env)) / expectedStoppingTime A env).toReal

omit [Fintype 𝓐] [MeasurableSingletonClass 𝓐] in
variable (A env) in
/-- The defining formula of `expectedPullProportion`. -/
lemma expectedPullProportion_def (a : 𝓐) :
    expectedPullProportion A env a =
      ((∫⁻ ω, (pullCount IT.action a (A.stoppingTime IT.obs IT.action IT.feedback ω).toNat ω :
        ℝ≥0∞) ∂(trajMeasure A.alg env)) / expectedStoppingTime A env).toReal :=
  (rfl)

omit [Fintype 𝓐] [MeasurableSingletonClass 𝓐] in
variable (A env) in
lemma expectedPullProportion_nonneg (a : 𝓐) : 0 ≤ expectedPullProportion A env a :=
  ENNReal.toReal_nonneg

omit [Fintype 𝓐] [MeasurableSingletonClass 𝓐] in
/-- If `𝔼[τ] = 0`, the expected proportions of pulls vanish. -/
lemma expectedPullProportion_eq_zero_of_expectedStoppingTime_eq_zero
    (h : expectedStoppingTime A env = 0) (a : 𝓐) : expectedPullProportion A env a = 0 := by
  simp [expectedPullProportion_def, h]

omit [Fintype 𝓐] [MeasurableSingletonClass 𝓐] in
/-- If `𝔼[τ] = ∞`, the expected proportions of pulls vanish. -/
lemma expectedPullProportion_eq_zero_of_expectedStoppingTime_eq_top
    (h : expectedStoppingTime A env = ∞) (a : 𝓐) : expectedPullProportion A env a = 0 := by
  rw [expectedPullProportion_def, h, ENNReal.div_top, ENNReal.toReal_zero]

omit [Fintype 𝓐] in
/-- If `𝔼[τ] < ∞`, the expected proportions of pulls recover the expected numbers of pulls:
`𝔼[τ] * (𝔼[N_a(τ)] / 𝔼[τ]) = 𝔼[N_a(τ)]`. -/
lemma expectedStoppingTime_mul_ofReal_expectedPullProportion [Finite 𝓐]
    (h : expectedStoppingTime A env ≠ ∞) (a : 𝓐) :
    expectedStoppingTime A env * ENNReal.ofReal (expectedPullProportion A env a) =
      ∫⁻ ω, (pullCount IT.action a (A.stoppingTime IT.obs IT.action IT.feedback ω).toNat ω : ℝ≥0∞)
        ∂(trajMeasure A.alg env) := by
  have := Fintype.ofFinite 𝓐
  -- By Wald's identity, `𝔼[N_a(τ)] ≤ 𝔼[τ]`.
  have hle : ∫⁻ ω, (pullCount IT.action a (A.stoppingTime IT.obs IT.action IT.feedback ω).toNat ω :
      ℝ≥0∞) ∂(trajMeasure A.alg env) ≤ expectedStoppingTime A env := by
    rw [expectedStoppingTime_eq_sum_lintegral_pullCount (StopsAS.of_expectedStoppingTime_ne_top h)]
    apply Finset.single_le_sum_of_canonicallyOrdered (Finset.mem_univ a)
  rcases eq_or_ne (expectedStoppingTime A env) 0 with h0 | h0
  · rw [h0, zero_mul]
    exact (nonpos_iff_eq_zero.1 (h0 ▸ hle)).symm
  rw [expectedPullProportion_def, ENNReal.ofReal_toReal (ENNReal.div_ne_top (hle.trans_lt
    h.lt_top).ne h0), ENNReal.mul_div_cancel h0 h]

/-- If `0 < 𝔼[τ] < ∞`, the expected proportions of pulls sum to `1`. -/
lemma sum_expectedPullProportion (h0 : expectedStoppingTime A env ≠ 0)
    (h : expectedStoppingTime A env ≠ ∞) : ∑ a, expectedPullProportion A env a = 1 := by
  rw [← ENNReal.ofReal_eq_one, ← ENNReal.mul_eq_left h0 h,
    ENNReal.ofReal_sum_of_nonneg fun a _ ↦ expectedPullProportion_nonneg A env a, Finset.mul_sum]
  simp_rw [expectedStoppingTime_mul_ofReal_expectedPullProportion h]
  exact (expectedStoppingTime_eq_sum_lintegral_pullCount
    (StopsAS.of_expectedStoppingTime_ne_top h)).symm

end LMLExplore.Identification

/-! ### Wald's identity for the rewards -/

namespace Learning.IdentAlg

open LMLExplore.Identification

variable [Fintype 𝓐] [DecidableEq 𝓐] [MeasurableSingletonClass 𝓐]

/-- **Wald's identity for the rewards at the stopping time.** If `A` has finite expected stopping
time `𝔼[τ] < ∞` in a stationary environment `ν` with integrable reward distributions, then along
any algorithm-environment sequence of its sampling rule, the expected sum of the rewards collected
before stopping is `∑ a, 𝔼[N_a(τ)] μ_a`, where `N_a(τ)` is the number of pulls of the action `a`
before `τ` and `μ_a` is the mean of `ν a`. -/
lemma integral_sum_feedback_eq_sum_integral_pullCount_mul [IsProbabilityMeasure P]
    {A : IdentAlg Unit 𝓐 ℝ 𝓓} {ν : Kernel 𝓐 ℝ} [IsMarkovKernel ν] {O : ℕ → Ω → Unit}
    {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} (h : IsAlgEnvSeq O X Y A.alg (stationaryEnv ν) P)
    (hA : expectedStoppingTime A (stationaryEnv ν) ≠ ∞) (hν : ∀ a, Integrable id (ν a)) :
    ∫ ω, ∑ t ∈ range (A.stoppingTime O X Y ω).toNat, Y t ω ∂P =
      ∑ a, (∫ ω, (pullCount X a (A.stoppingTime O X Y ω).toNat ω : ℝ) ∂P) * ∫ y, y ∂(ν a) :=
  h.integral_sum_feedback_eq_sum_integral_pullCount_mul
    (A.isStoppingTime_filtrationAction_stoppingTime h)
    (by rwa [A.lintegral_stoppingTime_eq_expectedStoppingTime h]) hν

end Learning.IdentAlg
