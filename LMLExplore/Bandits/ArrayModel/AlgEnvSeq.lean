/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.Online.Bandit.ArrayProbSpace
import LMLExplore.SequentialLearning.Algorithm
import LMLExplore.SequentialLearning.FiniteActions

/-!
# The array model is a run of the algorithm for observations in any measurable space

LML's array model (`Bandits.ArrayModel`) realizes a run of an algorithm against the stochastic
bandit `Environment.bandit ν` on the space `ProbSpace 𝓐 𝓡` of a sequence of uniform variables and
a table `ω.2 : ℕ → 𝓐 → 𝓡` of observations: the observation of the round in which the source `a`
is chosen for the `m`-th time is the entry `ω.2 m a`, so that the observations of each source are
read in order from one row of an i.i.d. table. Statements about the observations of each source,
such as the concentration of their empirical means, are proved in this model and transferred to
every algorithm–environment sequence through the uniqueness of the law of the run
(`Learning.isAlgEnvSeq_unique`).

LML proves that the array model is such a sequence (`Bandits.ArrayModel.isAlgEnvSeq_arrayMeasure`)
for a standard Borel nonempty space of observations `𝓡`. Here it is proved for observations in any
measurable space, with the same assumptions on the sources: countably many, in a nonempty
standard Borel space (which the uniform randomization of the algorithm needs).

## Main statements

* `LMLExplore.Bandits.ArrayModel.hasCondDistrib_reward_hist_action`: under
  `ArrayModel.arrayMeasure ν`, the conditional law of the observation of round `n` given the
  history and the source chosen at round `n` is `ν` of that source.
* `LMLExplore.Bandits.ArrayModel.isAlgEnvSeq_bandit`: under `ArrayModel.arrayMeasure ν`, the
  actions and observations of the array model are a run of the algorithm against
  `Environment.bandit ν`.

## Implementation notes

LML obtains the conditional law of the observation from Mathlib's `condDistrib`, which needs a
standard Borel space of observations. Here it is computed on rectangles instead. On the event
`E a m` that the source `a` is chosen at round `n` for the `m`-th time, the observation is
`ω.2 m a`. That event, the history and the source of round `n` are unchanged when the entry
`ω.2 m a` is removed from the table (LML's `ArrayModel.truncRow a m`), which is independent of
`ω.2 m a` (`ArrayModel.indepFun_snd_apply_truncRow`). So on `E a m` the observation is independent
of the history and the source, with law `ν a`; the events `E a m` partition the space.
-/

public section

open MeasureTheory ProbabilityTheory Learning Bandits.ArrayModel Function

namespace LMLExplore.Bandits.ArrayModel

variable {𝓐 𝓡 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓡 : MeasurableSpace 𝓡} [DecidableEq 𝓐]
  [Countable 𝓐] [Nonempty 𝓐] [StandardBorelSpace 𝓐] (alg : Algorithm Unit 𝓐 𝓡) (ν : Kernel 𝓐 𝓡)
  [IsMarkovKernel ν]

omit [Countable 𝓐] in
/-- Removing the entry `ω.2 m a` from the table changes neither the event that the source `a` is
chosen at round `n` for the `m`-th time, nor, on that event, the history and the source of
round `n`. -/
private lemma truncRow_preimage_inter (n : ℕ) (a : 𝓐) (m : ℕ)
    (s : Set (Hist Unit 𝓐 𝓡 n × 𝓐)) :
    truncRow a m ⁻¹' ({ω | action alg n ω = a ∧ pullCount (action alg) a n ω = m} ∩
        (fun ω ↦ (hist alg ω n, action alg n ω)) ⁻¹' s) =
      {ω | action alg n ω = a ∧ pullCount (action alg) a n ω = m} ∩
        (fun ω ↦ (hist alg ω n, action alg n ω)) ⁻¹' s := by
  ext ω
  have hω2_ne (i : ℕ) (b : 𝓐) (hb : b ≠ a) : ω.2 i b = (truncRow a m ω).2 i b := by
    simp [truncRow, hb]
  have hω2_eq (i : ℕ) (hi : i < m) : ω.2 i a = (truncRow a m ω).2 i a := by
    simp [truncRow, hi]
  have hE := action_eq_and_pullCount_eq_congr alg a m n (ω := ω) (ω' := truncRow a m ω)
    (fun _ ↦ rfl) hω2_ne fun i hi ↦ hω2_eq i hi
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [← hE]
  refine and_congr_right fun h ↦ ?_
  -- on the event, the rows read before round `n` are those of `truncRow a m ω`
  have h_hist : hist alg ω n = hist alg (truncRow a m ω) n := by
    refine hist_congr alg n (fun _ _ ↦ rfl) fun i b hi ↦ ?_
    rcases eq_or_ne b a with rfl | hb
    · exact hω2_eq i (h.2 ▸ hi)
    · exact hω2_ne i b hb
  rw [← h_hist, (hE.1 h).1, h.1]

/-- **The conditional law of the observation in the array model**, for observations in any
measurable space: under `ArrayModel.arrayMeasure ν`, the conditional law of the observation of
round `n` given the history of the first `n` rounds and the source chosen at round `n` is `ν` of
that source. LML's `Bandits.ArrayModel.hasCondDistrib_reward'` states it for a standard Borel
nonempty space of observations. -/
theorem hasCondDistrib_reward_hist_action (n : ℕ) :
    HasCondDistrib (reward alg n) (fun ω ↦ (hist alg ω n, action alg n ω))
      (ν.prodMkLeft _) (arrayMeasure ν) := by
  set P := arrayMeasure ν
  set Φ : ProbSpace 𝓐 𝓡 → Hist Unit 𝓐 𝓡 n × 𝓐 := fun ω ↦ (hist alg ω n, action alg n ω)
  have hΦ : Measurable Φ := (measurable_hist alg n).prodMk (measurable_action alg n)
  refine ⟨(hΦ.prodMk (measurable_reward alg n)).aemeasurable,
    Measure.ext_prod fun {s t} hs ht ↦ ?_⟩
  rw [Measure.map_apply (hΦ.prodMk (measurable_reward alg n)) (hs.prod ht), Set.mk_preimage_prod,
    Measure.compProd_apply_prod hs ht, setLIntegral_map hs (Kernel.measurable_coe _ ht) hΦ]
  simp only [Kernel.prodMkLeft_apply]
  -- the events `E p` that the source `p.1` is chosen at round `n` for the `p.2`-th time
  -- partition the space
  set E : 𝓐 × ℕ → Set (ProbSpace 𝓐 𝓡) :=
    fun p ↦ {ω | action alg n ω = p.1 ∧ pullCount (action alg) p.1 n ω = p.2}
  have hE (p : 𝓐 × ℕ) : MeasurableSet (E p) :=
    measurableSet_action_eq_and_pullCount_eq (measurable_action alg) n p.1 p.2
  rw [measure_eq_tsum_action_eq_and_pullCount_eq (measurable_action alg) n
      ((hΦ hs).inter (measurable_reward alg n ht)),
    setLIntegral_eq_tsum_action_eq_and_pullCount_eq (measurable_action alg) n (hΦ hs)]
  refine tsum_congr fun ⟨a, m⟩ ↦ ?_
  -- on `E (a, m)`, the observation is the entry `ω.2 m a`, independent of `truncRow a m`
  have h_reward : E (a, m) ∩ (Φ ⁻¹' s ∩ reward alg n ⁻¹' t) =
      (fun ω ↦ ω.2 m a) ⁻¹' t ∩ truncRow a m ⁻¹' (E (a, m) ∩ Φ ⁻¹' s) := by
    have hr (ω : ProbSpace 𝓐 𝓡) (hω : ω ∈ E (a, m)) : reward alg n ω = ω.2 m a := by
      simp only [reward_eq, hω.1, hω.2]
    rw [truncRow_preimage_inter]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hω, hs, ht⟩
      exact ⟨hr ω hω ▸ ht, hω, hs⟩
    · rintro ⟨ht, hω, hs⟩
      exact ⟨hω, hs, (hr ω hω).symm ▸ ht⟩
  rw [h_reward, (indepFun_snd_apply_truncRow ν a m).measure_inter_preimage_eq_mul _ _ ht
      ((hE _).inter (hΦ hs)),
    truncRow_preimage_inter, ← Measure.map_apply (by fun_prop) ht, map_snd_apply_arrayMeasure,
    setLIntegral_congr_fun ((hE _).inter (hΦ hs)) fun ω hω ↦ by simp only [Φ]; rw [hω.1.1],
    setLIntegral_const]

/-- **The array model is a run of the algorithm**, for observations in any measurable space: under
`ArrayModel.arrayMeasure ν`, the actions and observations of the array model are an
algorithm–environment sequence for `alg` and the stochastic bandit `Environment.bandit ν`. LML's
`Bandits.ArrayModel.isAlgEnvSeq_arrayMeasure` states it for a standard Borel nonempty space of
observations. -/
theorem isAlgEnvSeq_bandit :
    IsAlgEnvSeq (noObs _) (action alg) (reward alg) alg (Environment.bandit ν)
      (arrayMeasure ν) :=
  isAlgEnvSeq_bandit_of_hasCondDistrib (measurable_action alg) (measurable_reward alg)
    (hasCondDistrib_action alg ν) fun n ↦ by
      simpa only [hist_eq_history] using hasCondDistrib_reward_hist_action alg ν n

end LMLExplore.Bandits.ArrayModel
