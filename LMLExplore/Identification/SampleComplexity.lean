/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Correctness
public import LMLExplore.SequentialLearning.DivergenceDecomposition

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
`LMLExplore/SequentialLearning/DivergenceDecomposition.lean`; this file applies the first one at
the stopping time of an identification algorithm.

## Main definitions

* `LMLExplore.Identification.expectedStoppingTime A env`: the expected number of rounds `𝔼[τ]`
  played by `A` in `env`, an `ℝ≥0∞`-valued lower integral under `trajMeasure A.alg env`.

## Main statements

* `Learning.IdentAlg.lintegral_stoppingTime_eq_expectedStoppingTime`: the expected stopping time
  along any algorithm-environment sequence of the sampling rule is `expectedStoppingTime A env`.
* `Learning.IdentAlg.lintegral_stoppingTime_eq_sum_lintegral_pullCount`,
  `LMLExplore.Identification.expectedStoppingTime_eq_sum_lintegral_pullCount`: Wald's identity
  `𝔼[τ] = ∑ a, 𝔼[N_a(τ)]` at the stopping time `τ` of an identification algorithm that stops
  almost surely, along any algorithm-environment sequence and on the canonical space.

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

end LMLExplore.Identification
