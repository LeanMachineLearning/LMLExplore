/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.SampleComplexity
public import LMLExplore.SequentialLearning.Algorithms.OfSeq

/-!
# Fixed-budget and fixed-design identification algorithms

A *fixed-budget* identification algorithm with budget `T` stops after exactly `T` rounds; a
*fixed-confidence* algorithm stops adaptively. A *fixed-design* (static, non-adaptive) sampling
rule plays a fixed sequence of actions, whatever the observations and feedbacks.

## Main definitions

* `LMLExplore.Identification.IsFixedBudget A T`: the stopping rule of `A` is "stop after exactly
  `T` rounds".
* `LMLExplore.Identification.fixedBudget alg T ρ`: the fixed-budget identification algorithm with
  sampling rule `alg`, budget `T` and output kernel `ρ` on the histories of `T` rounds.
* `LMLExplore.Identification.IsFixedDesign alg`: the sampling rule `alg` plays a fixed sequence of
  actions, that is, it is `Algorithm.ofSeq x` for some `x`.

## Main statements

* `LMLExplore.Identification.IsFixedBudget.stoppingTime_eq`,
  `LMLExplore.Identification.IsFixedBudget.stoppedHist_eq`: the stopping time of a fixed-budget
  algorithm is its budget, and the stopped history is the history of the first `T` rounds.
* `LMLExplore.Identification.IsFixedBudget.stoppedHistMeasure_eq`,
  `LMLExplore.Identification.IsFixedBudget.outputMeasure_eq`: the laws of the stopped history and
  of the output; the latter is the output rule on the histories of `T` rounds composed with the
  law of the history of the first `T` rounds.
* `LMLExplore.Identification.IsFixedBudget.stopsAS`,
  `LMLExplore.Identification.IsFixedBudget.expectedStoppingTime_eq`: a fixed-budget algorithm with
  budget `T` stops almost surely, and its expected stopping time is `T`.
* `Learning.IdentAlg.IsRun.hasCondDistrib_output_history`: in a run of a fixed-budget algorithm,
  the output has conditional law `outputAt A T` given the history of the first `T` rounds.
* `LMLExplore.Identification.IsFixedBudget.hasLaw_output_of_isAlgEnvSeqUntil`,
  `Learning.IdentAlg.IsPAC.measureReal_bad_of_isAlgEnvSeqUntil`: an output drawn from
  `outputAt A T` after `T` rounds of the sampling rule of `A` (in a possibly longer interaction)
  has the law of the output of `A`, hence the PAC guarantees of `A` apply to it.

Adapted from the LMLPapers project (same author).
-/

public section

open MeasureTheory ProbabilityTheory Learning

variable {𝓞 𝓐 𝓨 𝓓 Ω : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {m𝓓 : MeasurableSpace 𝓓} {mΩ : MeasurableSpace Ω}
  {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {P : Measure Ω}

namespace LMLExplore.Identification

/-! ### Fixed budget -/

/-- The identification algorithm `A` is *fixed-budget* with budget `T`: it stops after exactly
`T` rounds. -/
def IsFixedBudget (A : IdentAlg 𝓞 𝓐 𝓨 𝓓) (T : ℕ) : Prop := A.stopSet = {h | h.1 = T}

section IsFixedBudget

variable {A : IdentAlg 𝓞 𝓐 𝓨 𝓓} {T : ℕ}

/-- The defining property of `IsFixedBudget`. -/
lemma isFixedBudget_iff : IsFixedBudget A T ↔ A.stopSet = {h | h.1 = T} := Iff.rfl

lemma IsFixedBudget.mem_stopSet_iff (hA : IsFixedBudget A T) {h : Σ n, Hist 𝓞 𝓐 𝓨 n} :
    h ∈ A.stopSet ↔ h.1 = T := by
  rw [isFixedBudget_iff.1 hA, Set.mem_ofPred_eq]

/-- The stopping time of a fixed-budget algorithm with budget `T` is `T`. -/
lemma IsFixedBudget.stoppingTime_eq (hA : IsFixedBudget A T) (ω : Ω) :
    A.stoppingTime O X Y ω = T := by
  rw [IdentAlg.stoppingTime_eq_coe_iff, hA.mem_stopSet_iff]
  exact ⟨rfl, fun j hj h ↦ hj.ne (hA.mem_stopSet_iff.1 h)⟩

/-- The stopping time of a fixed-budget algorithm is finite. -/
lemma IsFixedBudget.stoppingTime_ne_top (hA : IsFixedBudget A T) (ω : Ω) :
    A.stoppingTime O X Y ω ≠ ⊤ := by
  rw [hA.stoppingTime_eq]
  exact ENat.natCast_ne_top T

/-- The history at the stopping time of a fixed-budget algorithm with budget `T` is the history
of the first `T` rounds. -/
lemma IsFixedBudget.stoppedHist_eq (hA : IsFixedBudget A T) (ω : Ω) :
    A.stoppedHist O X Y ω = ⟨T, history O X Y T ω⟩ :=
  IdentAlg.stoppedHist_eq_of_stoppingTime_eq (hA.stoppingTime_eq ω)

/-- The law of the history at the stopping time of a fixed-budget algorithm with budget `T` is
the law of the history of the first `T` rounds. -/
lemma IsFixedBudget.stoppedHistMeasure_eq (hA : IsFixedBudget A T) (env : Environment 𝓞 𝓐 𝓨) :
    stoppedHistMeasure A.alg env A.stopSet
      = (trajMeasure A.alg env).map (sigmaHistory IT.obs IT.action IT.feedback T) := by
  rw [stoppedHistMeasure]
  congr 1
  funext traj
  exact hA.stoppedHist_eq (O := IT.obs) (X := IT.action) (Y := IT.feedback) traj

/-- The law of the output of a fixed-budget algorithm with budget `T`: the output rule on the
histories of `T` rounds applied to the law of the history of the first `T` rounds. -/
lemma IsFixedBudget.outputMeasure_eq (hA : IsFixedBudget A T) (env : Environment 𝓞 𝓐 𝓨) :
    A.outputMeasure env = outputAt A T ∘ₘ (trajMeasure A.alg env).map (IT.hist T) := by
  -- On the canonical space, the history `history IT.obs IT.action IT.feedback T` of the first
  -- `T` rounds is `IT.hist T` (`IT.history_obs_action_feedback`).
  have h_hist : sigmaHistory IT.obs IT.action IT.feedback T = Sigma.mk T ∘ IT.hist T :=
    funext fun _ ↦ by
      rw [sigmaHistory_apply, IT.history_obs_action_feedback (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨),
        Function.comp_apply]
  rw [IdentAlg.outputMeasure, hA.stoppedHistMeasure_eq, h_hist,
    ← Measure.map_map (measurable_sigma_mk T) (IT.measurable_hist T),
    ← Measure.deterministic_comp_eq_map (measurable_sigma_mk T), Measure.comp_assoc,
    Kernel.comp_deterministic_eq_comap, outputAt_eq_comap]

/-- The law of the output of a fixed-budget algorithm with budget `0` is the output rule applied
to the empty history. -/
lemma outputMeasure_eq_of_isFixedBudget_zero (hA : IsFixedBudget A 0)
    (env : Environment 𝓞 𝓐 𝓨) :
    A.outputMeasure env = A.output ⟨0, default⟩ := by
  rw [hA.outputMeasure_eq, IT.hist_zero, Measure.map_const, measure_univ, one_smul,
    Measure.dirac_bind (Kernel.measurable _), outputAt_apply]

/-- A fixed-budget algorithm stops almost surely. -/
lemma IsFixedBudget.stopsAS (hA : IsFixedBudget A T) (env : Environment 𝓞 𝓐 𝓨) :
    StopsAS A env := by
  rw [stopsAS_iff, hA.stoppedHistMeasure_eq]
  exact (ae_map_iff (measurable_sigmaHistory IT.measurable_obs IT.measurable_action
    IT.measurable_feedback T).aemeasurable A.measurableSet_stopSet).2
    (.of_forall fun _ ↦ hA.mem_stopSet_iff.2 rfl)

/-- The expected stopping time of a fixed-budget algorithm with budget `T` is `T`. -/
lemma IsFixedBudget.expectedStoppingTime_eq (hA : IsFixedBudget A T)
    (env : Environment 𝓞 𝓐 𝓨) : expectedStoppingTime A env = T := by
  simp [expectedStoppingTime_def, hA.stoppingTime_eq]

/-- If `A` has budget `T`, `(O, X, Y)` is an algorithm-environment sequence for the sampling rule
of `A` until time `T` (the interaction may go on after time `T` with another algorithm) and `out`
has conditional law `outputAt A T` given the history of the first `T` rounds, then `out` has the
law of the output of `A`. -/
lemma IsFixedBudget.hasLaw_output_of_isAlgEnvSeqUntil [IsProbabilityMeasure P] {out : Ω → 𝓓}
    {env : Environment 𝓞 𝓐 𝓨} (hA : IsFixedBudget A T) (h : IsAlgEnvSeqUntil O X Y A.alg env P T)
    (hout : HasCondDistrib out (history O X Y T) (outputAt A T) P) :
    HasLaw out (A.outputMeasure env) P := by
  have h_comp := hout.hasLaw_comp
  rwa [h.map_history, ← hA.outputMeasure_eq] at h_comp

end IsFixedBudget

end LMLExplore.Identification

/-! ### Runs of fixed-budget algorithms -/

namespace Learning.IdentAlg

open LMLExplore.Identification

variable {A : IdentAlg 𝓞 𝓐 𝓨 𝓓} {T : ℕ} {out : Ω → 𝓓}

/-- **In a run of a fixed-budget algorithm with budget `T`, the output has conditional law
`outputAt A T` given the history of the first `T` rounds.** -/
lemma IsRun.hasCondDistrib_output_history [IsFiniteMeasure P] {env : Environment 𝓞 𝓐 𝓨}
    (hA : IsFixedBudget A T) (h : A.IsRun env O X Y out P) :
    HasCondDistrib out (history O X Y T) (outputAt A T) P := by
  have h1 := h.hasCondDistrib_output
  rw [show A.stoppedHist O X Y = Sigma.mk T ∘ history O X Y T from funext hA.stoppedHist_eq] at h1
  rw [outputAt_eq_comap]
  exact h1.of_measurableEmbedding_comp_right (measurableEmbedding_sigma_mk T)

/-- For a fixed-budget algorithm whose output rule on the histories of `T` rounds is the
deterministic map `g`, the output of a run is almost surely `g` of the history of the first `T`
rounds. -/
lemma IsRun.output_ae_eq_of_outputAt_eq_deterministic [MeasurableEq 𝓓] [IsFiniteMeasure P]
    {env : Environment 𝓞 𝓐 𝓨} (hA : IsFixedBudget A T) (h : A.IsRun env O X Y out P)
    {g : Hist 𝓞 𝓐 𝓨 T → 𝓓} (hg : Measurable g) (hout : outputAt A T = Kernel.deterministic g hg) :
    out =ᵐ[P] fun ω ↦ g (history O X Y T ω) := by
  have h1 := h.hasCondDistrib_output_history hA
  rw [hout] at h1
  exact ae_eq_of_hasCondDistrib_deterministic hg h1.aemeasurable_fst h1.aemeasurable_snd h1

/-- **Transfer of a PAC guarantee to a partial run.** If `A` is PAC at level `δ` with budget `T`,
`(O, X, Y)` is an algorithm-environment sequence for the sampling rule of `A` until time `T` in
`env θ` and `out` has conditional law `outputAt A T` given the history of the first `T` rounds,
then `out` is `bad θ` with probability at most `δ`. -/
lemma IsPAC.measureReal_bad_of_isAlgEnvSeqUntil [IsProbabilityMeasure P] {Θ : Type*}
    {env : Θ → Environment 𝓞 𝓐 𝓨} {bad : Θ → 𝓓 → Prop} {δ : ℝ} {θ : Θ}
    (hpac : A.IsPAC env bad δ) (hA : IsFixedBudget A T) (hbad : MeasurableSet {d | bad θ d})
    (h : IsAlgEnvSeqUntil O X Y A.alg (env θ) P T)
    (hout : HasCondDistrib out (history O X Y T) (outputAt A T) P) :
    P.real {ω | bad θ (out ω)} ≤ δ := by
  rw [(hA.hasLaw_output_of_isAlgEnvSeqUntil h hout).measureReal_eq hbad]
  exact hpac θ

end Learning.IdentAlg

namespace LMLExplore.Identification

/-! ### The fixed-budget constructor -/

/-- The output rule of `fixedBudget alg T ρ` after `n` rounds: `ρ` if `n = T`, and an arbitrary
constant otherwise (never used). -/
private noncomputable def fixedBudgetOutput [Nonempty 𝓓] (T : ℕ)
    (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓓) (n : ℕ) : Kernel (Hist 𝓞 𝓐 𝓨 n) 𝓓 :=
  if h : n = T then ρ.comap (fun x i ↦ x (Fin.cast h.symm i)) (by fun_prop)
  else Kernel.const _ (Measure.dirac (Classical.arbitrary 𝓓))

private instance [Nonempty 𝓓] (T : ℕ) (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓓) [IsMarkovKernel ρ] (n : ℕ) :
    IsMarkovKernel (fixedBudgetOutput T ρ n) := by
  unfold fixedBudgetOutput
  split <;> infer_instance

@[simp]
private lemma fixedBudgetOutput_self [Nonempty 𝓓] (T : ℕ) (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓓) :
    fixedBudgetOutput T ρ T = ρ := by
  ext h : 1
  simp [fixedBudgetOutput]

/-- The fixed-budget identification algorithm with sampling rule `alg`, budget `T` and output
kernel `ρ` on the histories of `T` rounds. -/
noncomputable def fixedBudget [Nonempty 𝓓] (alg : Algorithm 𝓞 𝓐 𝓨) (T : ℕ)
    (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓓) [IsMarkovKernel ρ] : IdentAlg 𝓞 𝓐 𝓨 𝓓 :=
  ofStop alg (fun n _ ↦ n = T) (fun n ↦ by by_cases h : n = T <;> simp [h])
    (fixedBudgetOutput T ρ)

section FixedBudget

variable [Nonempty 𝓓] (alg : Algorithm 𝓞 𝓐 𝓨) (T : ℕ) (ρ : Kernel (Hist 𝓞 𝓐 𝓨 T) 𝓓)
  [IsMarkovKernel ρ]

@[simp]
lemma alg_fixedBudget : (fixedBudget alg T ρ).alg = alg := by
  rw [fixedBudget, alg_ofStop]

lemma isFixedBudget_fixedBudget : IsFixedBudget (fixedBudget alg T ρ) T := by
  rw [isFixedBudget_iff, fixedBudget, stopSet_ofStop]

/-- The output rule of `fixedBudget alg T ρ` after `T` rounds is `ρ`. -/
@[simp]
lemma output_fixedBudget_mk (h : Hist 𝓞 𝓐 𝓨 T) :
    (fixedBudget alg T ρ).output ⟨T, h⟩ = ρ h := by
  rw [fixedBudget, output_ofStop_mk, fixedBudgetOutput_self]

/-- The output rule of `fixedBudget alg T ρ` on the histories of `T` rounds is `ρ`. -/
@[simp]
lemma outputAt_fixedBudget : outputAt (fixedBudget alg T ρ) T = ρ := by
  rw [fixedBudget, outputAt_ofStop, fixedBudgetOutput_self]

end FixedBudget

/-! ### Fixed design -/

/-- The sampling rule `alg` is a *fixed-design* (static, non-adaptive) sampling rule: it plays a
fixed sequence of actions, whatever the observations and feedbacks. -/
def IsFixedDesign (alg : Algorithm 𝓞 𝓐 𝓨) : Prop := ∃ x : ℕ → 𝓐, alg = Algorithm.ofSeq x

/-- The defining property of `IsFixedDesign`. -/
lemma isFixedDesign_iff {alg : Algorithm 𝓞 𝓐 𝓨} :
    IsFixedDesign alg ↔ ∃ x : ℕ → 𝓐, alg = Algorithm.ofSeq x := Iff.rfl

lemma isFixedDesign_ofSeq (x : ℕ → 𝓐) : IsFixedDesign (Algorithm.ofSeq x : Algorithm 𝓞 𝓐 𝓨) :=
  ⟨x, rfl⟩

end LMLExplore.Identification
