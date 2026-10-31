/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.Correctness
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
public import LMLExplore.SequentialLearning.DivergenceDecomposition

/-!
# Change of measure at the stopping time of an identification algorithm

The lower bounds of fixed-confidence identification compare the behaviour of one identification
algorithm on two bandit models through the relative entropy between the laws of what it observes
before stopping and of what it outputs. For an algorithm `A` that stops almost surely on the
stationary bandit with reward kernel `κ`, the *divergence decomposition at the stopping time*
bounds this relative entropy by the expected transportation cost
`∑ a, E_κ[N_a(τ)] KL(κ a ‖ κ' a)`, where `N_a(τ)` is the number of pulls of the arm `a` before
the stopping time `τ`. The output kernel is common to the two models, so it does not increase the
divergence. By the data processing inequality, the same expected cost bounds the binary relative
entropy `d(P_κ(E), P_κ'(E))` of the probabilities of every event `E` of the stopped history and the
output: this *transportation lemma* turns a difference of behaviour of the algorithm on the two
models into a number of samples.

## Main statements

* `LMLExplore.Identification.klDiv_histOutputMeasure_le`: the relative entropy between the joint
  laws of the stopped history and the output under `κ` and `κ'` is at most
  `∑ a, E_κ[N_a(τ)] KL(κ a ‖ κ' a)`.
* `LMLExplore.Identification.klBer_measureReal_histOutputMeasure_le`: the transportation lemma
  `d(P_κ(E), P_κ'(E)) ≤ ∑ a, E_κ[N_a(τ)] KL(κ a ‖ κ' a)` for every measurable event `E` of the
  stopped history and the output.

The bound for the stopped history alone, for any stopping rule, is
`Learning.klDiv_stoppedHistMeasure_le`.

## References

* E. Kaufmann, O. Cappé and A. Garivier, *On the complexity of best-arm identification in
  multi-armed bandit models*, JMLR 17 (2016), Lemma 1.
* A. Garivier, P. Ménard and G. Stoltz, *Explore first, exploit next: the true shape of regret in
  bandit problems*, Math. Oper. Res. 44 (2019), for the proof of the transportation lemma by data
  processing.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Learning

open scoped ENNReal

namespace LMLExplore.Identification

variable {𝓐 𝓨 𝓓 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {m𝓓 : MeasurableSpace 𝓓} [Fintype 𝓐] [DecidableEq 𝓐] [MeasurableSingletonClass 𝓐]
  [MeasurableSpace.CountablyGenerated 𝓨]

/-- **Divergence decomposition at the stopping time** of an identification algorithm. If `A` stops
almost surely on the stationary bandit with reward kernel `κ`, then the relative entropy between
the joint laws of its stopped history and its output on the bandits `κ` and `κ'` is at most
`∑ a, E_κ[N_a(τ)] KL(κ a ‖ κ' a)`, where `N_a(τ)` is the number of pulls of `a` before the stopping
time `τ`. -/
theorem klDiv_histOutputMeasure_le (A : IdentAlg Unit 𝓐 𝓨 𝓓) (κ κ' : Kernel 𝓐 𝓨)
    [IsMarkovKernel κ] [IsMarkovKernel κ'] (hA : StopsAS A (stationaryEnv κ)) :
    klDiv (histOutputMeasure A (stationaryEnv κ)) (histOutputMeasure A (stationaryEnv κ')) ≤
      ∑ a, (∫⁻ ω, (pullCount IT.action a (A.stoppingTime IT.obs IT.action IT.feedback ω).toNat
        ω : ℝ≥0∞) ∂(trajMeasure A.alg (stationaryEnv κ))) * klDiv (κ a) (κ' a) := by
  rw [histOutputMeasure_def, histOutputMeasure_def, klDiv_compProd_left,
    IdentAlg.stoppingTime_def]
  exact klDiv_stoppedHistMeasure_le A.measurableSet_stopSet
    (hA.ae_stoppingTime_ne_top (IT.isAlgEnvSeq_trajMeasure A.alg (stationaryEnv κ)))

/-- **Transportation lemma** [KCG16, Lemma 1]. If `A` stops almost surely on the stationary bandit
with reward kernel `κ`, then for every measurable event `E` of the stopped history and the output,
the binary relative entropy of the probabilities of `E` on the bandits `κ` and `κ'` is at most
`∑ a, E_κ[N_a(τ)] KL(κ a ‖ κ' a)`, where `N_a(τ)` is the number of pulls of `a` before the stopping
time `τ`. No absolute continuity is assumed: the inequality holds in `ℝ≥0∞`. -/
theorem klBer_measureReal_histOutputMeasure_le (A : IdentAlg Unit 𝓐 𝓨 𝓓) (κ κ' : Kernel 𝓐 𝓨)
    [IsMarkovKernel κ] [IsMarkovKernel κ'] (hA : StopsAS A (stationaryEnv κ))
    {E : Set ((Σ n : ℕ, Hist Unit 𝓐 𝓨 n) × 𝓓)} (hE : MeasurableSet E) :
    klBer ((histOutputMeasure A (stationaryEnv κ)).real E)
        ((histOutputMeasure A (stationaryEnv κ')).real E) ≤
      ∑ a, (∫⁻ ω, (pullCount IT.action a (A.stoppingTime IT.obs IT.action IT.feedback ω).toNat
        ω : ℝ≥0∞) ∂(trajMeasure A.alg (stationaryEnv κ))) * klDiv (κ a) (κ' a) :=
  (klBer_measureReal_le_klDiv hE).trans (klDiv_histOutputMeasure_le A κ κ' hA)

end LMLExplore.Identification
