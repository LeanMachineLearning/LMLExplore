/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.ArrayModel.Stopping
public import LMLExplore.EValues.BipolarRate.Design.Round
import LMLExplore.Bandits.ArrayModel.AlgEnvSeq
import LMLExplore.Data.ENat.Basic
import LMLExplore.EValues.EVariable
import LMLExplore.MeasureTheory.Integral.EReal
import LMLExplore.Probability.HasLaw
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

If `τ` has a finite mean, the sharp form holds: `𝔼_μ[log Y] ≤ G (𝔼_μ[N τ])`, with `N τ` the
vector of the numbers of observations of each source by the time `τ` and
`G = designGrowth μ Λ` the growth of the designs proportional to a vector. It is sharper since
`G x ≤ D* * ∑ a, x a`, and it depends on how often each source is observed, not only on the total
number of observations.

## Main statements

* `Bandits.ArrayModel.eintegral_log_le_designRate_mul_lintegral`,
  `Bandits.ArrayModel.eintegral_log_le_designGrowth`: the Wald inequality with a design in the
  array model, with the rate and with the growth of the designs, for a stopping time that may use
  the seeds (`Bandits.ArrayModel.IsStoppedVar`).
* `Learning.IsAlgEnvSeq.eintegral_log_le_designRate_mul_lintegral`,
  `Learning.IsAlgEnvSeq.eintegral_log_le_designGrowth`: the Wald inequality with a design, with
  the rate and with the growth of the designs, for any algorithm–environment sequence of a bandit,
  at the hitting time of a stopping rule, for an e-variable that is a function of the stopped
  history.

## Implementation notes

In the array model (`Bandits.ArrayModel`), a point is a pair of seeds `ω.1 t`, from which the
algorithm draws its actions, and of a table `ω.2 i a` of observations, the observation number `i`
of the source `a`; its law `ArrayModel.arrayMeasure ν` is `ProbabilityTheory.arrayLaw` for the
uniform law of the seeds. The run stopped at `min τ k`, with payoff `(1 - ε) Y 𝟙{τ ≤ k} + ε`, is a
bounded round of the table (`Bandits.ArrayModel.stoppedShape`), for which
`ProbabilityTheory.integral_truncLog_le_designGrowth` gives the bound with the growth of the
designs at the expected numbers of observations by the time `min τ k`. These are at most those by
the time `τ`, and the growth is monotone; with the rate of the designs, they add up to at most
`𝔼_μ[τ]`. Letting `k → ∞` and then `ε → 0` gives the inequalities. Any algorithm–environment
sequence transfers to the array model, since the law of the stopped history, which determines the
expected hitting time and the expected numbers of pulls before it
(`Learning.IsAlgEnvSeq.lintegral_pullCount_hittingAfter`), is `Learning.stoppedHistMeasure` for
both (`Learning.IsAlgEnvSeq.hasLaw_stoppedValue_sigmaHistory`), and the array model is such a
sequence for observations in any measurable space
(`LMLExplore.Bandits.ArrayModel.isAlgEnvSeq_bandit`). The
array model draws the actions of the algorithm from uniform seeds, which needs a standard Borel
space of sources, hence this hypothesis in the transfer; a finite space of sources in which
singletons are measurable is standard Borel.

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

variable {α 𝓧 : Type*} [DecidableEq α] [Nonempty α] {mα : MeasurableSpace α}
  [StandardBorelSpace α] {m𝓧 : MeasurableSpace 𝓧} {alg : Algorithm Unit α 𝓧}
  {τ : ProbSpace α 𝓧 → WithTop ℕ} {Y : ProbSpace α 𝓧 → ℝ≥0∞}

/-! ### The Wald inequality with a design in the array model -/

/-- The Wald inequality for the run stopped at `min τ k`, with payoff
`(1 - ε) Y 𝟙{τ ≤ k} + ε`, with the growth of the designs proportional to the expected numbers of
observations of each source by the time `min τ k`. -/
private lemma integral_truncLog_mix_le_designGrowth [Fintype α] (μ : α → Measure 𝓧)
    [∀ a, IsProbabilityMeasure (μ a)] {Λ : Set (α → Measure 𝓧)}
    (hΛ : ∀ ν ∈ Λ, ∀ a, IsProbabilityMeasure (ν a))
    (hτ : Measurable τ) (hY : Measurable Y) (hτY : IsStoppedVar alg τ Y)
    (hYΛ : ∀ ν ∈ Λ, ∫⁻ ω in {ω | τ ω ≠ ⊤}, Y ω ∂arrayLaw volume ν ≤ 1) (k : ℕ) (c : ℝ)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ((∫ ω, truncLog c (ENNReal.ofReal (1 - ε) * {ω | τ ω ≤ k}.indicator Y ω +
      ENNReal.ofReal ε) ∂arrayLaw volume μ : ℝ) : EReal) ≤
      designGrowth μ Λ fun a ↦ (∫⁻ ω, (pullCount (action alg) a (min (τ ω) k).untopA ω : ℝ≥0∞)
        ∂arrayLaw volume μ).toNNReal := by
  have hτle : MeasurableSet {ω | τ ω ≤ k} := measurableSet_le hτ measurable_const
  have hτtop : MeasurableSet {ω | τ ω ≠ ⊤} := (measurableSet_singleton ⊤).compl.preimage hτ
  set V : ProbSpace α 𝓧 → ℝ≥0∞ := fun ω ↦
    ENNReal.ofReal (1 - ε) * {ω | τ ω ≤ k}.indicator Y ω + ENNReal.ofReal ε
  have hVm : Measurable V := (measurable_const.mul (hY.indicator hτle)).add measurable_const
  have hV : DependsOnBelow (stoppedShape alg τ k) V := dependsOnBelow_iff.2 fun ω ω' hag ↦ by
    simp only [V, (hτY.dependsOnBelow_indicator k).eq_of_agreeBelow hag]
  -- `Y 𝟙{τ ≤ k}` is an e-variable, and so is its mixture `V` with the constant `1`
  have hE : IsEVar ({ω | τ ω ≤ k}.indicator Y) ((fun ν ↦ arrayLaw volume ν) '' Λ) := by
    refine isEVar_iff_lintegral_le_one.2 ⟨hY.indicator hτle, ?_⟩
    rintro _ ⟨ν, hν, rfl⟩
    refine le_trans ?_ (hYΛ ν hν)
    rw [← lintegral_indicator hτtop]
    exact lintegral_mono fun ω ↦ Set.indicator_le_indicator_of_subset
      (fun ω hω ↦ WithTop.ne_top_of_le_natCast hω) (fun _ ↦ bot_le) ω
  have hVE := hE.ofReal_one_sub_mul_add_ofReal
    (by rintro _ ⟨ν, hν, rfl⟩; have := hΛ ν hν; exact prob_le_one) hε0.le hε1.le
  have h_null (ν : α → Measure 𝓧) (hν : ν ∈ Λ) : ∫⁻ ω, V ω ∂arrayLaw volume ν ≤ 1 :=
    hVE.lintegral_le_one ⟨ν, hν, rfl⟩
  refine (integral_truncLog_le_designGrowth volume μ hΛ (measurable_stoppedShape alg hτ k)
    (hτY.dependsOnBelow_stoppedShape k) hVm hV (stoppedShape_snd_le alg τ k) h_null hε0
    (fun ω ↦ le_add_self) c).trans_eq ?_
  -- the expected numbers of observations, as Bochner and as Lebesgue integrals
  congr 1
  funext a
  have hm : Measurable fun ω ↦ ((stoppedShape alg τ k ω).2 a : ℝ) :=
    measurable_from_nat.comp ((measurable_pi_apply a).comp (measurable_stoppedShape alg hτ k).snd)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ Nat.cast_nonneg _)
    hm.aestronglyMeasurable, ENNReal.toNNReal_toReal_eq]
  simp_rw [ENNReal.ofReal_natCast, stoppedShape_def]

omit [DecidableEq α] [Nonempty α] in
/-- From the bounds for the runs stopped at the times `min τ k` to the bound at `τ`: if `τ` is
almost surely finite and the truncated logarithms of the payoffs `(1 - ε) Y 𝟙{τ ≤ k} + ε` have
expectations at most `B` for every `k`, then the expected logarithm of `Y` is at most `B`. -/
private lemma eintegral_log_le_of_forall_integral_truncLog_mix_le (μ : α → Measure 𝓧)
    [∀ a, IsProbabilityMeasure (μ a)] (hτ : Measurable τ) (hY : Measurable Y)
    (hτμ : ∀ᵐ ω ∂arrayLaw volume μ, τ ω ≠ ⊤) {B : EReal} (hB : 0 ≤ B)
    (h : ∀ (k : ℕ) (c ε : ℝ), 0 < ε → ε < 1 →
      ((∫ ω, truncLog c (ENNReal.ofReal (1 - ε) * {ω | τ ω ≤ k}.indicator Y ω +
        ENNReal.ofReal ε) ∂arrayLaw volume μ : ℝ) : EReal) ≤ B) :
    ∫ᵉ ω, ENNReal.log (Y ω) ∂arrayLaw volume μ ≤ B := by
  rcases eq_or_ne B ⊤ with hBtop | hBtop
  · rw [hBtop]
    exact le_top
  have hb : ((B.toReal : ℝ) : EReal) = B :=
    EReal.coe_toReal hBtop (ne_bot_of_le_ne_bot EReal.zero_ne_bot hB)
  -- remove the truncation of the logarithm and the mixing constant
  rw [← hb]
  refine eintegral_log_le_of_forall_integral_truncLog_le hY fun c ε hε0 hε1 ↦ ?_
  -- let `k` tend to infinity, by dominated convergence
  refine integral_truncLog_le_of_eventually_eq (V := fun k ω ↦
    ENNReal.ofReal (1 - ε) * {ω | τ ω ≤ k}.indicator Y ω + ENNReal.ofReal ε) hε0
    (fun k ↦ (measurable_const.mul (hY.indicator (measurableSet_le hτ measurable_const))).add
      measurable_const) (fun _ _ ↦ le_add_self) ?_
    fun k ↦ EReal.coe_le_coe_iff.1 ((h k c ε hε0 hε1).trans_eq hb.symm)
  filter_upwards [hτμ] with ω hω
  filter_upwards [Filter.eventually_ge_atTop (τ ω).untopA] with k hk
  have hle : τ ω ≤ k := by
    rw [← WithTop.natCast_untopA hω]
    exact_mod_cast hk
  rw [Set.indicator_of_mem (s := {ω | τ ω ≤ k}) hle]

/-- **The Wald inequality with a design** [EVR26, Note 41, Theorem 1], in the array model. Let
`alg` be an algorithm on finitely many sources, `κ` an instance and `Λ` a nonempty set of
instances. Let `τ` be a stopping time of the run and `Y` a variable known at that time
(`IsStoppedVar alg τ Y`) which is an e-variable at `τ` for `Λ`: `𝔼_ν[Y 𝟙{τ < ⊤}] ≤ 1` for every
`ν ∈ Λ`. If `τ` is almost surely finite under `κ`, then `𝔼_κ[log Y] ≤ D* * 𝔼_κ[τ]`, where
`D* = designRate κ Λ` is the rate of the designs.

The expected logarithm is Statlib's extended integral, which is `⊥` when the positive and negative
parts of the logarithm have infinite integrals. The expectation of `τ` may be infinite, and the
product is in `EReal`, with `0 * ⊤ = 0`: if `D* = 0`, the expected logarithm is nonpositive. When
`τ` has a finite mean, `Bandits.ArrayModel.eintegral_log_le_designGrowth` is the sharper bound by
the growth of the designs proportional to the expected numbers of observations of each source. -/
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
  refine eintegral_log_le_of_forall_integral_truncLog_mix_le μ hτ hY hτκ
    (mul_nonneg (designRate_nonneg μ Λ') (EReal.coe_ennreal_nonneg _)) fun k c ε hε0 hε1 ↦ ?_
  refine (integral_truncLog_mix_le_designGrowth μ hΛ' hτ hY hτY hYΛ' k c hε0 hε1).trans
    ((designGrowth_le_designRate_mul (hΛne.image _) _).trans
      (mul_le_mul_of_nonneg_left ?_ (designRate_nonneg μ Λ')))
  -- the expected number `𝔼_μ[min τ k]` of observations of the stopped run is at most `𝔼_μ[τ]`
  set N : α → ProbSpace α 𝓧 → ℝ≥0∞ := fun a ω ↦
    (pullCount (action alg) a (min (τ ω) k).untopA ω : ℝ≥0∞)
  have hN (a : α) : Measurable (N a) := by
    have hm := (measurable_pi_apply a).comp (measurable_stoppedShape alg hτ k).snd
    simp only [stoppedShape_def] at hm
    exact measurable_from_nat.comp hm
  have hsum : ∫⁻ ω, ∑ a, N a ω ∂arrayLaw volume μ ≤
      ∫⁻ ω, ENat.toENNReal (τ ω) ∂arrayLaw volume μ := by
    refine lintegral_mono fun ω ↦ ?_
    simp only [N]
    rw [← Nat.cast_sum, sum_pullCount, ← ENat.toENNReal_coe]
    exact ENat.toENNReal_le.2 ((WithTop.natCast_untopA (WithTop.ne_top_of_le_natCast
      (min_le_right _ _))).trans_le (min_le_left _ _))
  have hfin (a : α) : ∫⁻ ω, N a ω ∂arrayLaw volume μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.natCast_ne_top k) ((lintegral_mono fun ω ↦ ?_).trans_eq
      (lintegral_const (k : ℝ≥0∞)) |>.trans_eq (by simp))
    simp only [N]
    exact_mod_cast (pullCount_le a _ ω).trans (WithTop.untopA_le (min_le_right (τ ω) k))
  rw [lintegral_finsetSum _ fun a _ ↦ hN a] at hsum
  simp only [ENNReal.coe_toNNReal_eq_toReal]
  rw [← ENNReal.toReal_sum fun a _ ↦ hfin a,
    EReal.coe_ennreal_toReal (ENNReal.sum_ne_top.2 fun a _ ↦ hfin a)]
  exact EReal.coe_ennreal_le_coe_ennreal_iff.2 hsum

/-- **The Wald inequality with a design, with the growth of the designs** [EVR26, Note 41,
Theorem 1], in the array model. Let `alg` be an algorithm on finitely many sources, `κ` an
instance and `Λ` a set of instances. Let `τ` be a stopping time of the run and `Y` a variable known
at that time (`IsStoppedVar alg τ Y`) which is an e-variable at `τ` for `Λ`:
`𝔼_ν[Y 𝟙{τ < ⊤}] ≤ 1` for every `ν ∈ Λ`. If `τ` has a finite mean under `κ`, then
`𝔼_κ[log Y] ≤ G (𝔼_κ[N τ])`, where `N τ` is the vector of the numbers of observations of each
source by the time `τ` and `G = designGrowth κ Λ` is the growth of the designs proportional to a
vector. Since `G x ≤ D* * ∑ a, x a` (`ProbabilityTheory.designGrowth_le_designRate_mul`), this is
sharper than `Bandits.ArrayModel.eintegral_log_le_designRate_mul_lintegral`, whose hypothesis is
only that `τ` is almost surely finite. -/
theorem eintegral_log_le_designGrowth [Fintype α] (κ : Kernel α 𝓧) [IsMarkovKernel κ]
    {Λ : Set (Kernel α 𝓧)} (hΛ : ∀ ν ∈ Λ, IsMarkovKernel ν)
    (hτ : Measurable τ) (hY : Measurable Y) (hτY : IsStoppedVar alg τ Y)
    (hYΛ : ∀ ν ∈ Λ, ∫⁻ ω in {ω | τ ω ≠ ⊤}, Y ω ∂arrayMeasure ν ≤ 1)
    (hτκ : ∫⁻ ω, ENat.toENNReal (τ ω) ∂arrayMeasure κ ≠ ⊤) :
    ∫ᵉ ω, ENNReal.log (Y ω) ∂arrayMeasure κ ≤
      designGrowth (fun a ↦ κ a) ((fun (ν : Kernel α 𝓧) a ↦ ν a) '' Λ) fun a ↦
        (∫⁻ ω, (pullCount (action alg) a (τ ω).untopA ω : ℝ≥0∞) ∂arrayMeasure κ).toNNReal := by
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
  -- a time of finite mean is almost surely finite
  have hτμ : ∀ᵐ ω ∂arrayLaw volume μ, τ ω ≠ ⊤ := by
    filter_upwards [ae_lt_top' ((measurable_of_countable _).comp hτ).aemeasurable hτκ] with ω hω
    exact ENat.toENNReal_ne_top.1 hω.ne
  refine eintegral_log_le_of_forall_integral_truncLog_mix_le μ hτ hY hτμ
    (designGrowth_nonneg μ (fun ν hν a ↦ (hΛ' ν hν a).measure_univ.le) _)
    fun k c ε hε0 hε1 ↦ ?_
  refine (integral_truncLog_mix_le_designGrowth μ hΛ' hτ hY hτY hYΛ' k c hε0 hε1).trans
    (designGrowth_mono hΛ' fun a ↦ ?_)
  -- the run stopped at `min τ k` observes each source at most as often as the run stopped at `τ`
  refine ENNReal.toNNReal_mono (ne_top_of_le_ne_top hτκ (lintegral_mono fun ω ↦ ?_))
    (lintegral_mono_ae ?_)
  · rcases eq_or_ne (τ ω) ⊤ with hω | hω
    · rw [hω]
      exact le_top.trans_eq ENat.toENNReal_top.symm
    obtain ⟨t, ht⟩ := WithTop.exists_eq_natCast_of_ne_top hω
    rw [ht, WithTop.untopA_natCast, ← ENat.toENNReal_coe]
    exact ENat.toENNReal_le.2 (Nat.cast_le.2 (pullCount_le a t ω))
  · filter_upwards [hτμ] with ω hω
    exact_mod_cast pullCount_mono a (WithTop.untopA_mono hω (min_le_left _ _)) ω

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
`0 * ⊤ = 0`. When `τ` has a finite mean, `Learning.IsAlgEnvSeq.eintegral_log_le_designGrowth` is
the sharper bound by the growth of the designs proportional to the expected numbers of pulls of
each source. -/
theorem IsAlgEnvSeq.eintegral_log_le_designRate_mul_lintegral [Fintype α] [StandardBorelSpace α]
    [IsProbabilityMeasure P] {κ : Kernel α 𝓧} [IsMarkovKernel κ]
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
  -- transfer to the array model, where the stopped history has the same law
  have h' := LMLExplore.Bandits.ArrayModel.isAlgEnvSeq_bandit alg κ
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
  exact ((LMLExplore.Bandits.ArrayModel.isAlgEnvSeq_bandit alg
    ν).setLIntegral_comp_stoppedValue_sigmaHistory hS hG).trans_le (hGΛ ν hν)

/-- **The Wald inequality with a design, with the growth of the designs** [EVR26, Note 41,
Theorem 1], for an algorithm and the hitting time `τ` of a stopping rule. Let `alg` be an
algorithm on finitely many sources, run against the instance `κ`
(`IsAlgEnvSeq O A R alg (Environment.bandit κ) P`), and let `Λ` be a set of instances. Let `S` be
a stopping rule, a set of histories, with hitting time `τ`, and `G` a function of the stopped
history which is an e-variable at `τ` for `Λ`: under the law
`stoppedHistMeasure alg (Environment.bandit ν) S` of the stopped history against `ν ∈ Λ`, the
expectation of `G` on `S` (where the run stops) is at most `1`. If `τ` has a finite mean, then
`𝔼[log G] ≤ G' (𝔼[N τ])`, where `N τ` is the vector of the numbers of pulls of each source
before `τ` and `G' = designGrowth κ Λ` is the growth of the designs proportional to a vector.
Since `G' x ≤ D* * ∑ a, x a` (`ProbabilityTheory.designGrowth_le_designRate_mul`), this is
sharper than `Learning.IsAlgEnvSeq.eintegral_log_le_designRate_mul_lintegral`, whose hypothesis is
only that `τ` is almost surely finite. -/
theorem IsAlgEnvSeq.eintegral_log_le_designGrowth [Fintype α] [DecidableEq α]
    [StandardBorelSpace α] [IsProbabilityMeasure P] {κ : Kernel α 𝓧} [IsMarkovKernel κ]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit κ) P) {Λ : Set (Kernel α 𝓧)}
    (hΛ : ∀ ν ∈ Λ, IsMarkovKernel ν) (hS : MeasurableSet S)
    {G : (Σ n, Hist Unit α 𝓧 n) → ℝ≥0∞} (hG : Measurable G)
    (hGΛ : ∀ (ν : Kernel α 𝓧) [IsMarkovKernel ν], ν ∈ Λ →
      ∫⁻ x in S, G x ∂stoppedHistMeasure alg (Environment.bandit ν) S ≤ 1)
    (hτ : ∫⁻ ω, ENat.toENNReal (hittingAfter (sigmaHistory O A R) S 0 ω) ∂P ≠ ⊤) :
    ∫ᵉ ω, ENNReal.log (G (stoppedValue (sigmaHistory O A R)
        (hittingAfter (sigmaHistory O A R) S 0) ω)) ∂P ≤
      designGrowth (fun a ↦ κ a) ((fun (ν : Kernel α 𝓧) a ↦ ν a) '' Λ) fun a ↦
        (∫⁻ ω, (pullCount A a (hittingAfter (sigmaHistory O A R) S 0 ω).untopA ω : ℝ≥0∞)
          ∂P).toNNReal := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure (alg.policyZero ())
  -- transfer to the array model, where the stopped history has the same law
  have h' := LMLExplore.Bandits.ArrayModel.isAlgEnvSeq_bandit alg κ
  have hτm := measurable_hittingAfter_sigmaHistory h.measurable_obs h.measurable_action
    h.measurable_feedback hS
  have hτm' := measurable_hittingAfter_sigmaHistory h'.measurable_obs h'.measurable_action
    h'.measurable_feedback hS
  -- a time of finite mean is almost surely finite
  have hτae : ∀ᵐ ω ∂P, hittingAfter (sigmaHistory O A R) S 0 ω ≠ ⊤ := by
    filter_upwards [ae_lt_top' ((measurable_of_countable _).comp hτm).aemeasurable hτ] with ω hω
    exact ENat.toENNReal_ne_top.1 hω.ne
  have hτae' := (h'.ae_hittingAfter_ne_top_iff hS).2 ((h.ae_hittingAfter_ne_top_iff hS).1 hτae)
  have hlog : AEMeasurable (fun x ↦ ENNReal.log (G x))
      (stoppedHistMeasure alg (Environment.bandit κ) S) :=
    (ENNReal.measurable_log.comp hG).aemeasurable
  rw [h.lintegral_toENNReal_hittingAfter hS hτae,
    ← h'.lintegral_toENNReal_hittingAfter hS hτae'] at hτ
  rw [(h.hasLaw_stoppedValue_sigmaHistory hS).eintegral_comp hlog,
    ← (h'.hasLaw_stoppedValue_sigmaHistory hS).eintegral_comp hlog]
  simp only [h.lintegral_pullCount_hittingAfter hS, ← h'.lintegral_pullCount_hittingAfter hS]
  refine Bandits.ArrayModel.eintegral_log_le_designGrowth κ hΛ hτm'
    (hG.comp (measurable_stoppedValue_sigmaHistory h'.measurable_obs h'.measurable_action
      h'.measurable_feedback hτm'))
    ((Bandits.ArrayModel.isStoppedVar_hittingAfter alg S).comp G) (fun ν hν ↦ ?_) hτ
  have := hΛ ν hν
  exact ((LMLExplore.Bandits.ArrayModel.isAlgEnvSeq_bandit alg
    ν).setLIntegral_comp_stoppedValue_sigmaHistory hS hG).trans_le (hGΛ ν hν)

end Learning
