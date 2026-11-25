/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Design.Round
public import LeanMachineLearning.Online.Bandit.ArrayProbSpace
public import LeanMachineLearning.SequentialLearning.StoppedHistory
import LMLExplore.Data.ENat.Basic
import LMLExplore.MeasureTheory.Integral.EReal
import LMLExplore.Probability.HasLaw
import LMLExplore.Probability.Process.StoppedValue
import LMLExplore.SequentialLearning.StoppedHistory

/-!
# The Wald inequality with a design, for an algorithm and a stopping time

An algorithm `alg : Learning.Algorithm Unit α 𝓧` chooses at each round which of finitely many
sources `a : α` to observe, and the instance `ν : α → Measure 𝓧` gives the law of the observations
of each source. A stopping time `τ` of the history and a variable `Y` known at that time form an
*e-variable at `τ`* for a set `Λ` of instances if `∫⁻ Y * 𝟙{τ < ⊤} ∂P_λ ≤ 1` for every `λ ∈ Λ`,
with `P_λ` the law of the run against `λ`.

The Wald inequality with a design [EVR26, Note 41]: if `τ` is almost surely finite under the
instance `μ`, then `𝔼_μ[log Y] ≤ D* * 𝔼_μ[τ]`, with `D* = designRate μ Λ` the rate of the
designs, the best expected logarithm per observation of an e-variable for the designs that observe
each source a fixed number of times. Adaptive sampling does not beat the best fixed design. For one
source, `D*` is the bipolar rate (`ProbabilityTheory.designRate_unique`), the rate of the Wald
inequality for e-processes,
`ProbabilityTheory.IsEProcess.eintegral_log_stoppedValue_le_mul_bipolarRate`.

## Main definitions

* `Bandits.ArrayModel.IsStoppedVar alg τ f`: in the array model of LML, `τ` and `f` are
  determined, on the event `{τ = t}`, by the seeds `ω.1 0, …, ω.1 t` and the history of the
  first `t` rounds of `alg`.
* `Bandits.ArrayModel.stoppedShape alg τ k`: the seeds and the observations of each source that
  the run of `alg` reads by the time `min τ k`.

## Main statements

* `Bandits.ArrayModel.eintegral_log_le_designRate_mul_lintegral`: the Wald inequality with a
  design in the array model, for a stopping time that may use the seeds.
* `Bandits.ArrayModel.isStoppedVar_hittingAfter`: the hitting time of a stopping rule and the
  history at that time form a stopped variable.
* `Learning.IsAlgEnvSeq.eintegral_log_le_designRate_mul_lintegral`: the Wald inequality with a
  design for any algorithm–environment sequence of a bandit, at the hitting time of a stopping
  rule, for an e-variable that is a function of the stopped history.

## Implementation notes

In the array model (`Bandits.ArrayModel`), a point is a pair of seeds `ω.1 t`, from which the
algorithm draws its actions, and of a table `ω.2 i a` of observations, the observation number `i`
of the source `a`; its law `ArrayModel.arrayMeasure ν` is `ProbabilityTheory.arrayLaw` for the
uniform law of the seeds. The run stopped at `min τ k`, with payoff `(1 - ε) Y 𝟙{τ ≤ k} + ε`, is a
bounded round of the table, for which `ProbabilityTheory.integral_truncLog_le_designRate_mul`
gives the bound; letting `k → ∞` and then `ε → 0` gives the inequality. Any
algorithm–environment sequence transfers to the array model, since the law of the stopped history
is `Learning.stoppedHistMeasure` for both (`Learning.IsAlgEnvSeq.hasLaw_stoppedValue_sigmaHistory`).
LML builds the array model, which draws the actions of the algorithm from uniform seeds, for
standard Borel spaces of sources and of observations, hence these hypotheses in the transfer.

The proofs are adapted from the draft `notes/lean-wip/SeveralArms.lean` of the paper project
`RemyDegenne/evalues_research`, which formalizes [EVR26, Note 41].

## References

* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 41,
  `results/41-several-arms-bipolar-rate.md`, Theorem 1.
-/

public section

open MeasureTheory ProbabilityTheory Learning
open ENNReal (truncLog)
open scoped ENNReal

namespace Bandits.ArrayModel

variable {α 𝓧 β : Type*} [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [StandardBorelSpace α] {m𝓧 : MeasurableSpace 𝓧} {alg : Algorithm Unit α 𝓧}
  {τ : ProbSpace α 𝓧 → WithTop ℕ} {Y : ProbSpace α 𝓧 → ℝ≥0∞}

/-! ### Stopping times and stopped variables in the array model -/

/-- In the array model, `τ` and `f` are determined, on the event `{τ = t}`, by the seeds
`ω.1 0, …, ω.1 t` and the history of the first `t` rounds of the algorithm `alg`: the time `τ`
is a stopping time for the information of the algorithm, its seeds and the observations it has
read, and `f` is known at that time. The hitting time of a stopping rule and the history at that
time are an instance (`Bandits.ArrayModel.isStoppedVar_hittingAfter`). -/
def IsStoppedVar (alg : Algorithm Unit α 𝓧) (τ : ProbSpace α 𝓧 → WithTop ℕ)
    (f : ProbSpace α 𝓧 → β) : Prop :=
  ∀ (ω ω' : ProbSpace α 𝓧) (t : ℕ), τ ω = t → (∀ i ≤ t, ω.1 i = ω'.1 i) →
    hist alg ω t = hist alg ω' t → τ ω' = t ∧ f ω' = f ω

lemma isStoppedVar_iff {f : ProbSpace α 𝓧 → β} :
    IsStoppedVar alg τ f ↔ ∀ (ω ω' : ProbSpace α 𝓧) (t : ℕ), τ ω = t →
      (∀ i ≤ t, ω.1 i = ω'.1 i) → hist alg ω t = hist alg ω' t → τ ω' = t ∧ f ω' = f ω :=
  Iff.rfl

/-- A function of a stopped variable is a stopped variable. -/
lemma IsStoppedVar.comp {γ : Type*} {f : ProbSpace α 𝓧 → β} (h : IsStoppedVar alg τ f)
    (g : β → γ) : IsStoppedVar alg τ fun ω ↦ g (f ω) := by
  refine isStoppedVar_iff.2 fun ω ω' t hτ hseed hhist ↦ ?_
  obtain ⟨hτ', hf⟩ := (isStoppedVar_iff.1 h) ω ω' t hτ hseed hhist
  exact ⟨hτ', by rw [hf]⟩

/-- The shape of the run of `alg` stopped at the time `min τ k`: the seeds
`ω.1 0, …, ω.1 (min τ k)` and, for each source, the observations read by that time. -/
noncomputable def stoppedShape (alg : Algorithm Unit α 𝓧) (τ : ProbSpace α 𝓧 → WithTop ℕ) (k : ℕ)
    (ω : ProbSpace α 𝓧) : ℕ × (α → ℕ) :=
  ((min (τ ω) k).untopA + 1, fun a ↦ pullCount (action alg) a (min (τ ω) k).untopA ω)

lemma stoppedShape_def (alg : Algorithm Unit α 𝓧) (τ : ProbSpace α 𝓧 → WithTop ℕ) (k : ℕ)
    (ω : ProbSpace α 𝓧) :
    stoppedShape alg τ k ω =
      ((min (τ ω) k).untopA + 1, fun a ↦ pullCount (action alg) a (min (τ ω) k).untopA ω) :=
  (rfl)

/-- The run stopped at `min τ k` reads at most `k` observations of each source. -/
lemma stoppedShape_snd_le (alg : Algorithm Unit α 𝓧) (τ : ProbSpace α 𝓧 → WithTop ℕ) (k : ℕ)
    (ω : ProbSpace α 𝓧) (a : α) : (stoppedShape alg τ k ω).2 a ≤ k :=
  (pullCount_le a _ ω).trans (WithTop.untopA_le (min_le_right _ _))

/-- The run stopped at `min τ k` reads `min τ k` observations. -/
lemma sum_stoppedShape_snd [Fintype α] (alg : Algorithm Unit α 𝓧) (τ : ProbSpace α 𝓧 → WithTop ℕ)
    (k : ℕ) (ω : ProbSpace α 𝓧) : ∑ a, (stoppedShape alg τ k ω).2 a = (min (τ ω) k).untopA :=
  sum_pullCount

lemma measurable_stoppedShape [Countable α] (alg : Algorithm Unit α 𝓧) (hτ : Measurable τ) (k : ℕ) :
    Measurable (stoppedShape alg τ k) := by
  have ht : Measurable fun ω ↦ (min (τ ω) k).untopA :=
    (hτ.min measurable_const).untopA
  refine (ht.add measurable_const).prodMk (measurable_pi_iff.2 fun a ↦ ?_)
  exact measurable_apply_of_countable
    (fun t ↦ measurable_pullCount (measurable_action alg) a t) ht

/-- Two points with the same entries below the shape of the run stopped at `min τ k` have the
same time `min τ k`, the same histories up to that time, and the same stopped variable if
`τ ≤ k`. -/
private lemma IsStoppedVar.eq_of_agreeBelow {f : ProbSpace α 𝓧 → β}
    (h : IsStoppedVar alg τ f) {k : ℕ} {ω ω' : ProbSpace α 𝓧}
    (hag : AgreeBelow (stoppedShape alg τ k ω) ω ω') :
    (min (τ ω') k).untopA = (min (τ ω) k).untopA ∧ (τ ω' ≤ k ↔ τ ω ≤ k) ∧
      (τ ω ≤ k → f ω' = f ω) ∧
      hist alg ω' (min (τ ω) k).untopA = hist alg ω (min (τ ω) k).untopA := by
  rw [agreeBelow_iff] at hag
  set t := (min (τ ω) k).untopA with ht
  have hcoe : (t : WithTop ℕ) = min (τ ω) k :=
    WithTop.natCast_untopA (WithTop.ne_top_of_le_natCast (min_le_right _ _))
  have htk : t ≤ k := WithTop.untopA_le (min_le_right _ _)
  have hseed (i : ℕ) (hi : i ≤ t) : ω.1 i = ω'.1 i :=
    hag.1 i (by simp only [stoppedShape_def]; omega)
  have hhist (j : ℕ) (hj : j ≤ t) : hist alg ω j = hist alg ω' j :=
    hist_congr alg j (fun i hi ↦ hseed i (by omega))
      fun i a hi ↦ hag.2 a i (hi.trans_le (pullCount_mono a hj ω))
  by_cases hle : τ ω ≤ k
  · have hτ : τ ω = t := by rw [hcoe, min_eq_left hle]
    obtain ⟨hτ', hf⟩ := (isStoppedVar_iff.1 h) ω ω' t hτ hseed (hhist t le_rfl)
    refine ⟨?_, by rw [hτ', hτ], fun _ ↦ hf, (hhist t le_rfl).symm⟩
    rw [hτ', min_eq_left (by exact_mod_cast htk), WithTop.untopA_natCast]
  · have hkt : t = k := by
      rw [ht, min_eq_right (not_le.1 hle).le, WithTop.untopA_natCast]
    have hle' : ¬ τ ω' ≤ k := by
      intro hle'
      obtain ⟨t', ht'⟩ := WithTop.exists_eq_natCast_of_ne_top (WithTop.ne_top_of_le_natCast hle')
      have ht'k : t' ≤ k := by rw [ht'] at hle'; exact_mod_cast hle'
      obtain ⟨hτ, -⟩ := (isStoppedVar_iff.1 h) ω' ω t' ht'
        (fun i hi ↦ (hseed i (by omega)).symm) (hhist t' (by omega)).symm
      exact hle (by rw [hτ]; exact_mod_cast ht'k)
    refine ⟨?_, by simp [hle, hle'], fun h' ↦ absurd h' hle, (hhist t le_rfl).symm⟩
    rw [min_eq_right (not_le.1 hle').le, hkt, WithTop.untopA_natCast]

/-- The shape of the run stopped at `min τ k` is determined by the entries below itself. -/
lemma IsStoppedVar.dependsOnBelow_stoppedShape {f : ProbSpace α 𝓧 → β}
    (h : IsStoppedVar alg τ f) (k : ℕ) :
    DependsOnBelow (stoppedShape alg τ k) (stoppedShape alg τ k) := by
  refine dependsOnBelow_iff.2 fun ω ω' hag ↦ ?_
  obtain ⟨ht, -, -, hhist⟩ := h.eq_of_agreeBelow hag
  simp only [stoppedShape_def, ht, Prod.mk.injEq, true_and]
  funext a
  rw [pullCount_action_eq, pullCount_action_eq, hhist]

/-- The stopped variable, on the event `{τ ≤ k}`, is determined by the entries below the shape of
the run stopped at `min τ k`. -/
lemma IsStoppedVar.dependsOnBelow_indicator [Zero β] {f : ProbSpace α 𝓧 → β}
    (h : IsStoppedVar alg τ f) (k : ℕ) :
    DependsOnBelow (stoppedShape alg τ k) ({ω | τ ω ≤ k}.indicator f) := by
  refine dependsOnBelow_iff.2 fun ω ω' hag ↦ ?_
  obtain ⟨-, hiff, hf, -⟩ := h.eq_of_agreeBelow hag
  by_cases hle : τ ω ≤ k
  · rw [Set.indicator_of_mem (s := {ω | τ ω ≤ k}) hle,
      Set.indicator_of_mem (s := {ω | τ ω ≤ k}) (hiff.2 hle), hf hle]
  · rw [Set.indicator_of_notMem (s := {ω | τ ω ≤ k}) hle,
      Set.indicator_of_notMem (s := {ω | τ ω ≤ k}) (mt hiff.1 hle)]

/-! ### The Wald inequality with a design in the array model -/

omit [DecidableEq α] [Nonempty α] [StandardBorelSpace α] in
/-- The array measure of LML is the law of the uniform seeds and of the table. -/
lemma arrayMeasure_eq_arrayLaw (ν : Kernel α 𝓧) :
    arrayMeasure ν = arrayLaw volume fun a ↦ ν a := by
  rw [arrayLaw_def, arrayMeasure, streamMeasure]

/-- The Wald inequality for the run stopped at `min τ k`, with payoff
`(1 - ε) Y 𝟙{τ ≤ k} + ε`. -/
private lemma integral_truncLog_mix_le [Fintype α] (μ : α → Measure 𝓧)
    [∀ a, IsProbabilityMeasure (μ a)] {Λ : Set (α → Measure 𝓧)}
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a)) (hΛne : Λ.Nonempty)
    (hτ : Measurable τ) (hY : Measurable Y) (hτY : IsStoppedVar alg τ Y)
    (hYΛ : ∀ ν ∈ Λ, ∫⁻ ω in {ω | τ ω ≠ ⊤}, Y ω ∂arrayLaw volume ν ≤ 1) (k : ℕ) (c : ℝ)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ((∫ ω, truncLog c (ENNReal.ofReal (1 - ε) * {ω | τ ω ≤ k}.indicator Y ω +
      ENNReal.ofReal ε) ∂arrayLaw volume μ : ℝ) : EReal) ≤
      designRate μ Λ * ((∫⁻ ω, ENat.toENNReal (τ ω) ∂arrayLaw volume μ : ℝ≥0∞) : EReal) := by
  have hτle : MeasurableSet {ω | τ ω ≤ k} := measurableSet_le hτ measurable_const
  have hτtop : MeasurableSet {ω | τ ω ≠ ⊤} := (measurableSet_singleton ⊤).compl.preimage hτ
  set V : ProbSpace α 𝓧 → ℝ≥0∞ := fun ω ↦
    ENNReal.ofReal (1 - ε) * {ω | τ ω ≤ k}.indicator Y ω + ENNReal.ofReal ε
  have hVm : Measurable V := (measurable_const.mul (hY.indicator hτle)).add measurable_const
  have hV : DependsOnBelow (stoppedShape alg τ k) V := dependsOnBelow_iff.2 fun ω ω' hag ↦ by
    simp only [V, (hτY.dependsOnBelow_indicator k).eq_of_agreeBelow hag]
  have h_null (ν : α → Measure 𝓧) (hν : ν ∈ Λ) : ∫⁻ ω, V ω ∂arrayLaw volume ν ≤ 1 := by
    have := hΛ ν hν
    calc ∫⁻ ω, V ω ∂arrayLaw volume ν
    _ = ENNReal.ofReal (1 - ε) * ∫⁻ ω, {ω | τ ω ≤ k}.indicator Y ω ∂arrayLaw volume ν +
          ENNReal.ofReal ε := by
      rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ (hY.indicator hτle),
        lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (1 - ε) * 1 + ENNReal.ofReal ε := by
      gcongr
      refine le_trans ?_ (hYΛ ν hν)
      rw [← lintegral_indicator hτtop]
      exact lintegral_mono fun ω ↦ Set.indicator_le_indicator_of_subset
        (fun ω hω ↦ WithTop.ne_top_of_le_natCast hω) (fun _ ↦ bot_le) ω
    _ = 1 := by
      rw [mul_one, ← ENNReal.ofReal_add (by linarith) hε0.le, sub_add_cancel, ENNReal.ofReal_one]
  refine (integral_truncLog_le_designRate_mul volume μ hΛ hΛne (measurable_stoppedShape alg hτ k)
    (hτY.dependsOnBelow_stoppedShape k) hVm hV (stoppedShape_snd_le alg τ k) h_null hε0
    (fun ω ↦ le_add_self) c).trans (mul_le_mul_of_nonneg_left ?_ (designRate_nonneg μ Λ))
  -- the expected number of observations of the stopped run is at most `𝔼_μ[τ]`
  have hsum (ω : ProbSpace α 𝓧) :
      ∑ a, ((stoppedShape alg τ k ω).2 a : ℝ) = ((min (τ ω) k).untopA : ℝ) := by
    rw [← Nat.cast_sum, sum_stoppedShape_snd]
  have htm : Measurable fun ω ↦ ((min (τ ω) k).untopA : ℝ) :=
    measurable_from_nat.comp (hτ.min measurable_const).untopA
  have hfin : ∫⁻ ω, ((min (τ ω) k).untopA : ℝ≥0∞) ∂arrayLaw volume μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.natCast_ne_top k) ?_
    calc ∫⁻ ω, ((min (τ ω) k).untopA : ℝ≥0∞) ∂arrayLaw volume μ
    _ ≤ ∫⁻ _, (k : ℝ≥0∞) ∂arrayLaw volume μ :=
      lintegral_mono fun ω ↦ by exact_mod_cast WithTop.untopA_le (min_le_right (τ ω) k)
    _ = k := by simp
  simp_rw [hsum]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ Nat.cast_nonneg _)
    htm.aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_natCast]
  rw [EReal.coe_ennreal_toReal hfin, EReal.coe_ennreal_le_coe_ennreal_iff]
  refine lintegral_mono fun ω ↦ ?_
  rw [← ENat.toENNReal_coe]
  exact ENat.toENNReal_le.2 ((WithTop.natCast_untopA (WithTop.ne_top_of_le_natCast
    (min_le_right _ _))).trans_le (min_le_left _ _))

/-- **The Wald inequality with a design** [EVR26, Note 41, Theorem 1], in the array model. Let
`alg` be an algorithm on finitely many sources, `κ` an instance and `Λ` a nonempty set of
instances. Let `τ` be a stopping time of the run and `Y` a variable known at that time
(`IsStoppedVar alg τ Y`) which is an e-variable at `τ` for `Λ`: `𝔼_ν[Y 𝟙{τ < ⊤}] ≤ 1` for every
`ν ∈ Λ`. If `τ` is almost surely finite under `κ`, then `𝔼_κ[log Y] ≤ D* * 𝔼_κ[τ]`, where
`D* = designRate κ Λ` is the rate of the designs.

The expected logarithm is Statlib's extended integral, which is `⊥` when the positive and negative
parts of the logarithm have infinite integrals. The expectation of `τ` may be infinite, and the
product is in `EReal`, with `0 * ⊤ = 0`: if `D* = 0`, the expected logarithm is nonpositive. -/
theorem eintegral_log_le_designRate_mul_lintegral [Fintype α] (κ : Kernel α 𝓧) [IsMarkovKernel κ]
    {Λ : Set (Kernel α 𝓧)} (hΛ : ∀ ν ∈ Λ, IsMarkovKernel ν) (hΛne : Λ.Nonempty)
    (hτ : Measurable τ) (hY : Measurable Y) (hτY : IsStoppedVar alg τ Y)
    (hYΛ : ∀ ν ∈ Λ, ∫⁻ ω in {ω | τ ω ≠ ⊤}, Y ω ∂arrayMeasure ν ≤ 1)
    (hτκ : ∀ᵐ ω ∂arrayMeasure κ, τ ω ≠ ⊤) :
    ∫ᵉ ω, ENNReal.log (Y ω) ∂arrayMeasure κ ≤
      designRate (fun a ↦ κ a) ((fun (ν : Kernel α 𝓧) a ↦ ν a) '' Λ) *
        ((∫⁻ ω, ENat.toENNReal (τ ω) ∂arrayMeasure κ : ℝ≥0∞) : EReal) := by
  simp only [arrayMeasure_eq_arrayLaw] at hYΛ hτκ ⊢
  set μ : α → Measure 𝓧 := fun a ↦ κ a
  set Λ' : Set (α → Measure 𝓧) := (fun (ν : Kernel α 𝓧) a ↦ ν a) '' Λ
  have hΛ' : ∀ ν ∈ Λ', ∀ a, IsProbabilityMeasure (ν a) := by
    rintro _ ⟨ν, hν, rfl⟩ a
    have := hΛ ν hν
    infer_instance
  have hYΛ' : ∀ ν ∈ Λ', ∫⁻ ω in {ω | τ ω ≠ ⊤}, Y ω ∂arrayLaw volume ν ≤ 1 := by
    rintro _ ⟨ν, hν, rfl⟩
    exact hYΛ ν hν
  set B : EReal := designRate μ Λ' *
    ((∫⁻ ω, ENat.toENNReal (τ ω) ∂arrayLaw volume μ : ℝ≥0∞) : EReal)
  have h_round := fun k c ε (hε0 : 0 < ε) (hε1 : ε < 1) ↦
    integral_truncLog_mix_le μ hΛ' (hΛne.image _) hτ hY hτY hYΛ' k c hε0 hε1
  rcases eq_or_ne B ⊤ with hBtop | hBtop
  · rw [hBtop]
    exact le_top
  have hb : ((B.toReal : ℝ) : EReal) = B :=
    EReal.coe_toReal hBtop (ne_bot_of_le_ne_bot EReal.zero_ne_bot
      (mul_nonneg (designRate_nonneg μ Λ') (EReal.coe_ennreal_nonneg _)))
  -- let `k` tend to infinity, by dominated convergence
  have h_lim (c : ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
      ∫ ω, truncLog c (ENNReal.ofReal (1 - ε) * Y ω + ENNReal.ofReal ε) ∂arrayLaw volume μ ≤
        B.toReal := by
    rw [← EReal.coe_le_coe_iff, hb]
    refine le_of_tendsto' (EReal.tendsto_coe.2 (tendsto_integral_of_dominated_convergence
      (fun _ ↦ max |Real.log ε| |c|) (fun k ↦ ?_) (integrable_const _) (fun k ↦ ?_) ?_))
      fun k ↦ h_round k c ε hε0 hε1
    · exact ((ENNReal.measurable_truncLog c).comp ((measurable_const.mul
        (hY.indicator (measurableSet_le hτ measurable_const))).add
          measurable_const)).aestronglyMeasurable
    · exact ae_of_all _ fun ω ↦ (Real.norm_eq_abs _).trans_le
        (ENNReal.abs_truncLog_le hε0 le_add_self)
    · filter_upwards [hτκ] with ω hω
      refine tendsto_atTop_of_eventually_const (i₀ := (τ ω).untopA) fun k hk ↦ ?_
      have hle : τ ω ≤ k := by
        rw [← WithTop.natCast_untopA hω]
        exact_mod_cast hk
      rw [Set.indicator_of_mem (s := {ω | τ ω ≤ k}) hle]
  -- remove the truncation of the logarithm and the mixing constant
  refine eintegral_le_of_forall_min_le (ENNReal.measurable_log.comp hY) fun k ↦ ?_
  rw [← hb]
  refine EReal.le_of_forall_le_sub_log_one_sub fun ε hε0 hε1 ↦ ?_
  have hYi : Integrable (fun ω ↦ truncLog k (ENNReal.ofReal (1 - ε) * Y ω + ENNReal.ofReal ε))
      (arrayLaw volume μ) :=
    ENNReal.integrable_truncLog_comp hε0 ((measurable_const.mul hY).add measurable_const)
      fun _ ↦ le_add_self
  exact (eintegral_min_log_le_integral_truncLog_sub hε0 hε1 k hYi).trans
    (EReal.coe_le_coe_iff.2 (by linarith [h_lim k hε0 hε1]))

/-! ### Stopping rules -/

/-- In the array model, the hitting time of a stopping rule `S`, the first time at which the
history belongs to `S`, and the history at that time form a stopped variable of the algorithm. -/
lemma isStoppedVar_hittingAfter (alg : Algorithm Unit α 𝓧) (S : Set (Σ n, Hist Unit α 𝓧 n)) :
    IsStoppedVar alg
      (hittingAfter (sigmaHistory (noObs (ProbSpace α 𝓧)) (action alg) (reward alg)) S 0)
      (stoppedValue (sigmaHistory (noObs (ProbSpace α 𝓧)) (action alg) (reward alg))
        (hittingAfter (sigmaHistory (noObs (ProbSpace α 𝓧)) (action alg) (reward alg)) S 0)) := by
  refine isStoppedVar_iff.2 fun ω ω' t hτ _ hhist ↦ ?_
  set u := sigmaHistory (noObs (ProbSpace α 𝓧)) (action alg) (reward alg)
  -- the histories of `ω` and `ω'` agree up to time `t`
  have hu (j : ℕ) (hj : j ≤ t) : u j ω' = u j ω := by
    simp only [u, sigmaHistory_apply]
    rw [history_eq_comp_history hj]
    simp only [Function.comp_apply, ← hist_eq_history, hhist]
  have hτ' : hittingAfter u S 0 ω' = t := by
    have h := hτ
    rw [Nat.cast_withTop, hittingAfter_eq_coe_iff] at h ⊢
    exact ⟨h.1, by rw [hu t le_rfl]; exact h.2.1,
      fun j hj ↦ by rw [hu j hj.2.le]; exact h.2.2 j hj⟩
  refine ⟨hτ', ?_⟩
  simp only [stoppedValue, hτ, hτ', WithTop.untopA_natCast]
  exact hu t le_rfl

end Bandits.ArrayModel

/-! ### Algorithm–environment sequences -/

namespace Learning

variable {α 𝓧 Ω : Type*} {mα : MeasurableSpace α} {m𝓧 : MeasurableSpace 𝓧}
  {mΩ : MeasurableSpace Ω} {alg : Algorithm Unit α 𝓧} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
  {R : ℕ → Ω → 𝓧} {P : Measure Ω} {S : Set (Σ n, Hist Unit α 𝓧 n)}

/-- **The Wald inequality with a design** [EVR26, Note 41, Theorem 1], for an algorithm and the
hitting time `τ` of a stopping rule. Let `alg` be an algorithm on finitely many sources, run
against the instance `κ` (`IsAlgEnvSeq O A R alg (Environment.bandit κ) P`), and let `Λ` be a
nonempty set of instances. Let `S` be a stopping rule, a set of histories, with hitting time `τ`,
and `G` a function of the stopped history which is an e-variable at `τ` for `Λ`: under the law
`stoppedHistMeasure alg (Environment.bandit ν) S` of the stopped history against `ν ∈ Λ`, the
expectation of `G` on `S` (where the run stops) is at most `1`. If `τ` is almost surely finite,
then `𝔼[log G] ≤ D* * 𝔼[τ]`, where `D* = designRate κ Λ` is the rate of the designs.

The expected logarithm is Statlib's extended integral, and the product is in `EReal`, with
`0 * ⊤ = 0`. -/
theorem IsAlgEnvSeq.eintegral_log_le_designRate_mul_lintegral [Fintype α] [StandardBorelSpace α]
    [StandardBorelSpace 𝓧] [IsProbabilityMeasure P] {κ : Kernel α 𝓧} [IsMarkovKernel κ]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit κ) P) {Λ : Set (Kernel α 𝓧)}
    (hΛ : ∀ ν ∈ Λ, IsMarkovKernel ν) (hΛne : Λ.Nonempty) (hS : MeasurableSet S)
    {G : (Σ n, Hist Unit α 𝓧 n) → ℝ≥0∞} (hG : Measurable G)
    (hGΛ : ∀ (ν : Kernel α 𝓧) [IsMarkovKernel ν], ν ∈ Λ →
      ∫⁻ x in S, G x ∂stoppedHistMeasure alg (Environment.bandit ν) S ≤ 1)
    (hτ : ∀ᵐ ω ∂P, hittingAfter (sigmaHistory O A R) S 0 ω ≠ ⊤) :
    ∫ᵉ ω, ENNReal.log (G (stoppedValue (sigmaHistory O A R)
        (hittingAfter (sigmaHistory O A R) S 0) ω)) ∂P ≤
      designRate (fun a ↦ κ a) ((fun (ν : Kernel α 𝓧) a ↦ ν a) '' Λ) *
        ((∫⁻ ω, ENat.toENNReal (hittingAfter (sigmaHistory O A R) S 0 ω) ∂P : ℝ≥0∞) :
          EReal) := by
  classical
  have : Nonempty α := nonempty_of_isProbabilityMeasure (alg.policyZero ())
  have : Nonempty 𝓧 := nonempty_of_isProbabilityMeasure (κ (Classical.arbitrary α))
  -- transfer to the array model, where the stopped history has the same law
  have h' := Bandits.ArrayModel.isAlgEnvSeq_arrayMeasure alg κ
  have hτ' := (h'.ae_hittingAfter_ne_top_iff hS).2 ((h.ae_hittingAfter_ne_top_iff hS).1 hτ)
  have hlog : AEMeasurable (fun x ↦ ENNReal.log (G x))
      (stoppedHistMeasure alg (Environment.bandit κ) S) :=
    (ENNReal.measurable_log.comp hG).aemeasurable
  have hτm := measurable_hittingAfter_sigmaHistory h'.measurable_obs h'.measurable_action
    h'.measurable_feedback hS
  rw [(h.hasLaw_stoppedValue_sigmaHistory hS).eintegral_comp hlog,
    h.lintegral_toENNReal_hittingAfter hS hτ,
    ← (h'.hasLaw_stoppedValue_sigmaHistory hS).eintegral_comp hlog,
    ← h'.lintegral_toENNReal_hittingAfter hS hτ']
  refine Bandits.ArrayModel.eintegral_log_le_designRate_mul_lintegral κ hΛ hΛne hτm
    (hG.comp (measurable_stoppedValue_sigmaHistory h'.measurable_obs h'.measurable_action
      h'.measurable_feedback hτm))
    ((Bandits.ArrayModel.isStoppedVar_hittingAfter alg S).comp G) (fun ν hν ↦ ?_) hτ'
  have := hΛ ν hν
  exact ((Bandits.ArrayModel.isAlgEnvSeq_arrayMeasure alg
    ν).setLIntegral_comp_stoppedValue_sigmaHistory hS hG).trans_le (hGΛ ν hν)

end Learning
