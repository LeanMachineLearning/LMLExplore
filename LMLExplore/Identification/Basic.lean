/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Kernel.Sigma
public import LeanMachineLearning.SequentialLearning.IdentificationAlg
public import LMLExplore.SequentialLearning.Algorithm

/-!
# Identification algorithms: per-length rules, stopping times, canonical runs

Complements to LML's identification algorithms `Learning.IdentAlg`
(`LeanMachineLearning/SequentialLearning/IdentificationAlg.lean`), whose stopping rule is a
measurable set `A.stopSet` of histories of variable length and whose output rule is a single
Markov kernel `A.output` on histories of variable length.

## Main definitions

* `LMLExplore.Identification.ofStop alg stop hstop output`: the identification algorithm with
  sampling rule `alg` that stops after `n` rounds if the history `h` of these rounds satisfies
  `stop n h`, and whose output after `n` rounds with history `h` has law `output n h` (stopping
  and output rules given per history length).
* `LMLExplore.Identification.outputAt A n`: the output rule of `A` on the histories of `n` rounds.
* `LMLExplore.Identification.runMeasure A env`: the law of the (trajectory, output) pair of the
  canonical run of `A` in the environment `env`, on `(ℕ → Round 𝓞 𝓐 𝓨) × 𝓓`.

## Main statements

* `Learning.IdentAlg.stoppingTime_eq_top_iff`, `Learning.IdentAlg.stoppingTime_eq_coe_iff`,
  `Learning.IdentAlg.stoppingTime_le_of_mem_stopSet`: the stopping time in terms of the stopping
  rule.
* `Learning.IdentAlg.stoppedHist_mem_stopSet_iff`: the history at the stopping time belongs to the
  stopping rule iff the stopping time is finite.
* `Learning.IdentAlg.stoppedHist_eq_of_stoppingTime_eq`: the history at a finite stopping time.
* `Learning.IdentAlg.measurable_stoppingTime`, `Learning.IdentAlg.measurable_stoppedHist`.
* `Learning.IdentAlg.IsRun.comp_hasLaw`: runs are transported along a measurable map `g : Ω → Ω'`
  carrying `P` to `P'`.
* `Learning.IdentAlg.outputMeasure_apply_eq_lintegral`: the probability of an event of the output
  is the expectation, along any algorithm-environment sequence of the sampling rule, of its
  probability under the output rule applied to the stopped history.
* `LMLExplore.Identification.isRun_runMeasure`: every identification algorithm has a run in every
  environment, the canonical run on `runMeasure`, on which the trajectory has law
  `trajMeasure A.alg env` and the output is drawn from the output rule applied to the history at
  the stopping time.

Adapted from the LMLPapers project (same author).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning

variable {𝓞 𝓐 𝓨 𝓓 Ω : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓓 : MeasurableSpace 𝓓} {mΩ : MeasurableSpace Ω}

namespace LMLExplore.Identification

/-! ### Construction from per-length rules -/

section OfStop

variable (alg : Algorithm 𝓞 𝓐 𝓨) (stop : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n → Prop)
  (hstop : ∀ n, MeasurableSet {h | stop n h}) (output : (n : ℕ) → Kernel (Hist 𝓞 𝓐 𝓨 n) 𝓓)
  [∀ n, IsMarkovKernel (output n)]

/-- The identification algorithm with sampling rule `alg` that stops after `n` rounds if the
history `h` of these rounds satisfies `stop n h`, and whose output after `n` rounds with history
`h` has law `output n h`. -/
noncomputable def ofStop : IdentAlg 𝓞 𝓐 𝓨 𝓓 where
  alg := alg
  stopSet := {h | stop h.1 h.2}
  measurableSet_stopSet := measurableSet_sigma_iff.2 hstop
  output := Kernel.sigma output

@[simp]
lemma alg_ofStop : (ofStop alg stop hstop output).alg = alg := rfl

lemma stopSet_ofStop : (ofStop alg stop hstop output).stopSet = {h | stop h.1 h.2} := rfl

@[simp]
lemma mem_stopSet_ofStop {h : Σ n, Hist 𝓞 𝓐 𝓨 n} :
    h ∈ (ofStop alg stop hstop output).stopSet ↔ stop h.1 h.2 := Iff.rfl

@[simp]
lemma output_ofStop : (ofStop alg stop hstop output).output = Kernel.sigma output := rfl

lemma output_ofStop_mk {n : ℕ} (h : Hist 𝓞 𝓐 𝓨 n) :
    (ofStop alg stop hstop output).output ⟨n, h⟩ = output n h := rfl

end OfStop

/-! ### The output rule on the histories of a given length -/

/-- The output rule of `A` on the histories of `n` rounds: the law of the output of `A` when it
stops after `n` rounds, as a function of the history of these rounds. -/
noncomputable def outputAt (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (n : ℕ) : Kernel (Hist 𝓞 𝓐 𝓨 n) 𝓓 :=
  A.output.comap (Sigma.mk n) (measurable_sigma_mk n)

@[simp]
lemma outputAt_apply (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) {n : ℕ} (h : Hist 𝓞 𝓐 𝓨 n) :
    outputAt A n h = A.output ⟨n, h⟩ := rfl

instance (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (n : ℕ) : IsMarkovKernel (outputAt A n) := by
  unfold outputAt
  infer_instance

@[simp]
lemma outputAt_ofStop (alg : Algorithm 𝓞 𝓐 𝓨) (stop : (n : ℕ) → Hist 𝓞 𝓐 𝓨 n → Prop)
    (hstop : ∀ n, MeasurableSet {h | stop n h}) (output : (n : ℕ) → Kernel (Hist 𝓞 𝓐 𝓨 n) 𝓓)
    [∀ n, IsMarkovKernel (output n)] (n : ℕ) :
    outputAt (ofStop alg stop hstop output) n = output n :=
  Kernel.comap_sigma_mk output n

end LMLExplore.Identification

namespace Learning.IdentAlg

variable {A : IdentAlg 𝓞 𝓐 𝓨 𝓓} {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {ω : Ω}
  {n : ℕ}

/-! ### The stopping time and the stopped history -/

/-- The stopping time is infinite iff the stopping rule never holds. -/
lemma stoppingTime_eq_top_iff :
    A.stoppingTime O X Y ω = ⊤ ↔
      ∀ n, (⟨n, history O X Y n ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∉ A.stopSet := by
  rw [stoppingTime_def]
  exact hittingAfter_eq_top_iff.trans (by simp [sigmaHistory_apply])

/-- The stopping time is `n` iff the stopping rule holds after `n` rounds and not before. -/
lemma stoppingTime_eq_coe_iff :
    A.stoppingTime O X Y ω = n ↔
      (⟨n, history O X Y n ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∈ A.stopSet ∧
        ∀ j < n, (⟨j, history O X Y j ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∉ A.stopSet := by
  rw [stoppingTime_def]
  exact hittingAfter_eq_coe_iff.trans (by simp [sigmaHistory_apply])

/-- If the stopping rule holds after `n` rounds, the stopping time is at most `n`. -/
lemma stoppingTime_le_of_mem_stopSet
    (h : (⟨n, history O X Y n ω⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∈ A.stopSet) :
    A.stoppingTime O X Y ω ≤ n :=
  hittingAfter_le_of_mem (Nat.zero_le n) h

lemma fst_stoppedHist : (A.stoppedHist O X Y ω).1 = (A.stoppingTime O X Y ω).untopA := rfl

/-- The history at a finite stopping time `n` is the history of the first `n` rounds. -/
lemma stoppedHist_eq_of_stoppingTime_eq (h : A.stoppingTime O X Y ω = n) :
    A.stoppedHist O X Y ω = ⟨n, history O X Y n ω⟩ := by
  simp only [stoppedHist_def, stoppedValue, h, sigmaHistory_apply]
  rfl

/-- The history at the stopping time belongs to the stopping rule iff the stopping time is
finite. -/
lemma stoppedHist_mem_stopSet_iff :
    A.stoppedHist O X Y ω ∈ A.stopSet ↔ A.stoppingTime O X Y ω ≠ ⊤ := by
  refine ⟨fun h htop ↦ ?_, stoppedHist_mem_stopSet_of_ne_top⟩
  simp only [stoppedHist_def, stoppedValue, htop, sigmaHistory_apply] at h
  exact stoppingTime_eq_top_iff.1 htop _ h

section Measurability

variable (A)
variable (hO : ∀ n, Measurable (O n)) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
include hO hX hY

@[fun_prop]
lemma measurable_stoppingTime : Measurable (A.stoppingTime O X Y) :=
  measurable_to_countable' fun x ↦ measurable_hittingAfter_sigmaHistory hO hX hY
    A.measurableSet_stopSet (measurableSet_singleton (α := WithTop ℕ) x)

@[fun_prop]
lemma measurable_stoppedHist : Measurable (A.stoppedHist O X Y) :=
  measurable_stoppedValue_sigmaHistory hO hX hY
    (measurable_hittingAfter_sigmaHistory hO hX hY A.measurableSet_stopSet)

end Measurability

/-! ### Transport of runs and law of the output -/

/-- A run of an identification algorithm is transported along a measurable map `g` carrying `P`
to `P'`. -/
lemma IsRun.comp_hasLaw {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
    [IsFiniteMeasure P] {P' : Measure Ω'} [IsFiniteMeasure P'] {g : Ω → Ω'}
    {env : Environment 𝓞 𝓐 𝓨} {O : ℕ → Ω' → 𝓞} {X : ℕ → Ω' → 𝓐} {Y : ℕ → Ω' → 𝓨}
    {out : Ω' → 𝓓} (h : A.IsRun env O X Y out P') (hg : HasLaw g P' P) (hgm : Measurable g) :
    A.IsRun env (fun n ↦ O n ∘ g) (fun n ↦ X n ∘ g) (fun n ↦ Y n ∘ g) (out ∘ g) P where
  isAlgEnvSeq := h.isAlgEnvSeq.comp_hasLaw hg hgm
  hasCondDistrib_output := h.hasCondDistrib_output.comp_hasLaw hg

/-- The probability that the output of `A` in `env` belongs to `s` is the expectation, along any
algorithm-environment sequence of the sampling rule `A.alg` in `env`, of the probability of `s`
under the output rule applied to the stopped history. -/
lemma outputMeasure_apply_eq_lintegral {env : Environment 𝓞 𝓐 𝓨} {P : Measure Ω}
    [IsProbabilityMeasure P] (h : IsAlgEnvSeq O X Y A.alg env P) {s : Set 𝓓}
    (hs : MeasurableSet s) :
    A.outputMeasure env s = ∫⁻ ω, A.output (A.stoppedHist O X Y ω) s ∂P := by
  rw [IdentAlg.outputMeasure, Measure.bind_apply hs A.output.measurable.aemeasurable,
    ← (h.hasLaw_stoppedValue_sigmaHistory A.measurableSet_stopSet).map_eq]
  exact lintegral_map (A.output.measurable_coe hs)
    (A.measurable_stoppedHist h.measurable_obs h.measurable_action h.measurable_feedback)

end Learning.IdentAlg

namespace LMLExplore.Identification

/-! ### The canonical run -/

section RunMeasure

variable (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (env : Environment 𝓞 𝓐 𝓨)

/-- The canonical probability space of a run of `A` in the environment `env`, on the space
`(ℕ → Round 𝓞 𝓐 𝓨) × 𝓓` of (trajectory, output) pairs: the trajectory has the law
`trajMeasure A.alg env` of the Ionescu-Tulcea construction and, given the trajectory, the output
is drawn from the output rule applied to the history at the stopping time. -/
noncomputable def runMeasure : Measure ((ℕ → Round 𝓞 𝓐 𝓨) × 𝓓) :=
  trajMeasure A.alg env ⊗ₘ A.output.comap (A.stoppedHist IT.obs IT.action IT.feedback)
    (A.measurable_stoppedHist IT.measurable_obs IT.measurable_action IT.measurable_feedback)
deriving IsProbabilityMeasure

/-- **Existence of runs**: every identification algorithm has a run in every environment, the
canonical run on `runMeasure`. -/
lemma isRun_runMeasure :
    A.IsRun env (fun n ω ↦ IT.obs n ω.1) (fun n ω ↦ IT.action n ω.1)
      (fun n ω ↦ IT.feedback n ω.1) Prod.snd (runMeasure A env) where
  isAlgEnvSeq := (IT.isAlgEnvSeq_trajMeasure A.alg env).comp_hasLaw
    ⟨measurable_fst.aemeasurable, Measure.fst_compProd _ _⟩ measurable_fst
  hasCondDistrib_output :=
    hasCondDistrib_snd_compProd_comap (trajMeasure A.alg env) A.output
      (A.measurable_stoppedHist IT.measurable_obs IT.measurable_action IT.measurable_feedback)
      fun _ ↦ inferInstance

/-- The trajectory of the canonical run has law `trajMeasure A.alg env`. -/
@[simp]
lemma fst_runMeasure : (runMeasure A env).fst = trajMeasure A.alg env :=
  Measure.fst_compProd _ _

/-- The output of the canonical run has law `A.outputMeasure env`. -/
@[simp]
lemma snd_runMeasure : (runMeasure A env).snd = A.outputMeasure env :=
  (isRun_runMeasure A env).hasLaw_output.map_eq

end RunMeasure

end LMLExplore.Identification
