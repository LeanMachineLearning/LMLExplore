/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import LMLExplore.EValues.EProcess.Basic
public import Mathlib.Probability.ProductMeasure
import LMLExplore.EValues.BipolarRate.Round
import LMLExplore.MeasureTheory.Integral.EReal
import LMLExplore.Probability.ProductMeasure
import LMLExplore.Probability.Process.Stopping
import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner

/-!
# Expected stopping times are governed by the bipolar rate

Let `S₁` be a set of probability measures on `𝓧` (the null) and `Q₁` a probability measure on `𝓧`
(the alternative). The observations are the coordinates of `ℕ → 𝓧`, with the i.i.d. laws
`Measure.infinitePi fun _ ↦ P`, `P ∈ S₁`, and the filtration `Filtration.piLE`, so that `τ + 1`
observations have been made at a time `τ`. Write `d = bipolarRate Q₁ S₁` and `Q` for the i.i.d. law
of `Q₁`.

The **Wald inequality** at the bipolar rate [EVR26, Note 01]: for every e-process `E` for the
i.i.d. null and every stopping time `τ` with values in `ℕ`, `𝔼_Q[log E_τ] ≤ 𝔼_Q[τ + 1] * d`, in
`EReal`, with Statlib's extended integral on the left. Nothing is assumed of `S₁` beyond its
members being probability measures, and nothing of `Q₁`. The expectation of `τ` may be infinite,
with `∞ * 0 = 0`: if `d = 0`, the e-process has a nonpositive expected logarithm at every stopping
time.

Its case `E n = α⁻¹ * 𝟙{τ ≤ n}` (mixed with a constant, so that its logarithm is finite) is the
**lower bound on expected stopping times** [EVR26, Note 01]: a sequential test of level `α`, that
is, a stopping time `τ` with values in `WithTop ℕ` such that `P^ℕ (τ < ∞) ≤ α` for every
`P ∈ S₁`, makes at least `log (1/α) / d` observations in expectation under `Q`. If `d = 0`,
every test of a level `α < 1` has an infinite expected number of observations. Since `d` is at
most the smallest relative entropy `KL_inf(Q₁, S₁)` from `Q₁` to the null
(`ProbabilityTheory.bipolarRate_le_iInf_klDiv`), this contains the lower bound with
`KL_inf(Q₁, S₁)` in place of `d`, the form of the bounds of [ARR26]; the bipolar rate can be
smaller [RR26, Proposition 5.4].

## Main statements

* `ProbabilityTheory.IsEProcess.eintegral_log_stoppedValue_le_mul_bipolarRate`: the Wald
  inequality `𝔼_Q[log E_τ] ≤ 𝔼_Q[τ + 1] * d`.
* `ProbabilityTheory.toENNReal_log_inv_div_bipolarRate_le_lintegral`: a sequential test of level
  `α` has `log (1/α) / d ≤ 𝔼_Q[τ + 1]`.

## Implementation notes

The round of the Wald inequality for a round
(`ProbabilityTheory.integral_truncLog_le_bipolarRate_mul`, in
`LMLExplore.EValues.BipolarRate.Round`) is the e-process stopped at `min τ k`, mixed with a
constant `ε` so that its logarithm is bounded below: `(1 - ε) E_{min τ k} + ε`. The bound for it
holds for the logarithm truncated above at a level `c`; then `k → ∞` (dominated convergence), the
truncation level `c → ∞` (monotone convergence for the extended integral,
`MeasureTheory.eintegral_le_of_forall_min_le`) and `ε → 0`. The lower bound on expected stopping
times applies the Wald inequality to the e-process `ε + (1 - ε) α⁻¹ 𝟙{τ ≤ n}` at the stopping times
`min τ k`.

The proofs are adapted from `EValuesResearch/Results/BipolarRate.lean` and
`EValuesResearch/Results/BipolarRateAux.lean` (commit `dd4072f`) in the paper project
`RemyDegenne/evalues_research`, which formalizes [EVR26, Note 01]. They are specialized here to
stopping times with values in `ℕ`.

## References

* [ARR26] S. Agrawal, A. Ram and A. Ramdas, *On stopping times of power-one sequential tests:
  tight lower and upper bounds*, arXiv:2504.19952v2.
* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1.
* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 01,
  `results/01-bipolar-rate.md`.
-/

public section

open MeasureTheory Filter
open ENNReal (truncLog)
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}

/-! ### Removing the mixing constant -/

/-- The mixing constant `ε` of `(1 - ε) x + ε` costs `- log (1 - ε)`, which tends to `0` with `ε`:
a bound `x ≤ D - log (1 - ε)` for every `ε ∈ (0, 1)` gives `x ≤ D`. -/
private lemma le_of_forall_le_sub_log_one_sub {x : EReal} {D : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → x ≤ ((D - Real.log (1 - ε) : ℝ) : EReal)) : x ≤ D := by
  refine EReal.le_of_forall_lt_iff_le.1 fun z hz ↦ ?_
  have hη : 0 < z - D := sub_pos.2 (EReal.coe_lt_coe_iff.1 hz)
  have hexp : Real.exp (-(z - D)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h' := h (1 - Real.exp (-(z - D))) (by linarith) (by linarith [Real.exp_pos (-(z - D))])
  rwa [sub_sub_cancel, Real.log_exp, sub_neg_eq_add, add_sub_cancel] at h'

/-! ### The Wald inequality for e-processes -/

section EProcess

variable {E : ℕ → (ℕ → 𝓧) → ℝ≥0∞} {τ : (ℕ → 𝓧) → ℕ}

/-- The stopped e-process mixed with a constant, `(1 - ε) E_τ + ε`, has expectation at most `1`
on each event `{τ + 1 ≤ n}` under the i.i.d. law of a member of the null. -/
private lemma lintegral_indicator_mix_stoppedValue_le_one (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hE : IsEProcess E (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁))
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) fun ω ↦ (τ ω : WithTop ℕ))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {P : Measure 𝓧} (hP : P ∈ S₁) (n : ℕ) :
    ∫⁻ ω, {ω | τ ω + 1 ≤ n}.indicator
        (fun ω ↦ ENNReal.ofReal (1 - ε) * E (τ ω) ω + ENNReal.ofReal ε) ω
      ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1 := by
  have := hS₁ P hP
  have hPS : Measure.infinitePi (fun _ : ℕ ↦ P) ∈
      (fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁ := ⟨P, hP, rfl⟩
  calc ∫⁻ ω, {ω | τ ω + 1 ≤ n}.indicator
        (fun ω ↦ ENNReal.ofReal (1 - ε) * E (τ ω) ω + ENNReal.ofReal ε) ω
      ∂Measure.infinitePi (fun _ ↦ P)
  _ ≤ ∫⁻ ω, ENNReal.ofReal (1 - ε) * E (min (τ ω) (n - 1)) ω + ENNReal.ofReal ε
      ∂Measure.infinitePi (fun _ ↦ P) := by
    refine lintegral_mono fun ω ↦ ?_
    by_cases hω : τ ω + 1 ≤ n
    · rw [Set.indicator_of_mem hω, min_eq_left (by omega : τ ω ≤ n - 1)]
    · rw [Set.indicator_of_notMem hω]
      exact bot_le
  _ = ENNReal.ofReal (1 - ε) * ∫⁻ ω, E (min (τ ω) (n - 1)) ω
      ∂Measure.infinitePi (fun _ ↦ P) + ENNReal.ofReal ε := by
    rw [lintegral_add_right _ measurable_const, lintegral_const_mul _
      (hE.measurable_stoppedValue (hτ.natCast_min (n - 1))), lintegral_const,
      measure_univ, mul_one]
  _ ≤ ENNReal.ofReal (1 - ε) * 1 + ENNReal.ofReal ε := by
    gcongr
    exact hE.lintegral_le_one (hτ.natCast_min (n - 1)) hPS
  _ = 1 := by
    rw [mul_one, ← ENNReal.ofReal_add (by linarith) hε0.le, sub_add_cancel, ENNReal.ofReal_one]

/-- The Wald inequality for the payoff `(1 - ε) E_τ + ε`, truncated above at `c`: apply the Wald
inequality for a round to the e-process stopped at `min τ k`, and let `k` tend to infinity. The
bound `D` is that of the Wald inequality for the stopping times `min τ k`. -/
private lemma integral_truncLog_stoppedValue_le (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hE : IsEProcess E (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁))
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) fun ω ↦ (τ ω : WithTop ℕ))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {c : ℝ}
    (hd : bipolarRate Q₁ S₁ ≠ ⊤) {D : ℝ}
    (hD : ∀ k : ℕ, (bipolarRate Q₁ S₁).toReal *
      ∫ ω, ((min (τ ω) k + 1 : ℕ) : ℝ) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤ D) :
    ∫ ω, truncLog c (ENNReal.ofReal (1 - ε) * E (τ ω) ω + ENNReal.ofReal ε)
      ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤ D := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  set V : ℕ → (ℕ → 𝓧) → ℝ≥0∞ := fun k ω ↦
    ENNReal.ofReal (1 - ε) * E (min (τ ω) k) ω + ENNReal.ofReal ε
  have hτk (k : ℕ) := hτ.natCast_min k
  have hVm (k : ℕ) : Measurable (V k) :=
    (measurable_const.mul (hE.measurable_stoppedValue (hτk k))).add measurable_const
  have hVε (k : ℕ) (ω : ℕ → 𝓧) : ENNReal.ofReal ε ≤ V k ω := le_add_self
  -- the Wald inequality for the round stopped at `min τ k`
  have hk (k : ℕ) : ∫ ω, truncLog c (V k ω) ∂μ ≤ D := by
    refine (integral_truncLog_le_bipolarRate_mul (σ := fun ω ↦ min (τ ω) k + 1) Q₁ hS₁ ?_ ?_
      (((hτk k).measurable_nat).add_const 1) (hVm k) (fun _ ↦ le_add_self)
      (K := k + 1) (fun ω ↦ by simp) ?_ hε0 (hVε k) hd).trans ?_
    · refine dependsOnBefore_iff.2 fun u ω ω' h hle ↦ ?_
      rw [(hτk k).eq_of_forall_le fun i hi ↦ h i (by omega)]
    · refine dependsOnBefore_iff.2 fun u ω ω' h hle ↦ ?_
      have h' : ∀ i ≤ min (τ ω) k, ω i = ω' i := fun i hi ↦ h i (by omega)
      simp only [V, (hτk k).eq_of_forall_le h',
        ((hE.adapted (min (τ ω) k)).dependsOn_of_piLE fun i hi ↦ h' i hi).symm]
    · exact fun P hP n ↦ lintegral_indicator_mix_stoppedValue_le_one hS₁ hE (hτk k) hε0 hε1 hP n
    · exact hD k
  -- let `k` tend to infinity
  refine le_of_tendsto' (tendsto_integral_of_dominated_convergence (fun _ ↦ max |Real.log ε| |c|)
    (fun k ↦ ((ENNReal.measurable_truncLog c).comp (hVm k)).aestronglyMeasurable)
    (integrable_const _)
    (fun k ↦ ae_of_all _ fun ω ↦ (Real.norm_eq_abs _).trans_le
      (ENNReal.abs_truncLog_le hε0 (hVε k ω))) (ae_of_all _ fun ω ↦ ?_)) hk
  exact tendsto_atTop_of_eventually_const (i₀ := τ ω) fun k hk ↦ by simp [V, min_eq_left hk]

/-- The Wald inequality when the bipolar rate is finite and either it is `0` or the expected
number of observations is finite: the expected logarithm of `E_τ` is at most the real number
`d * 𝔼[τ + 1]`. -/
private lemma eintegral_log_stoppedValue_le_toReal_mul (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hE : IsEProcess E (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁))
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) fun ω ↦ (τ ω : WithTop ℕ))
    (hd : bipolarRate Q₁ S₁ ≠ ⊤)
    (hdm : bipolarRate Q₁ S₁ = 0 ∨
      ∫⁻ ω, (τ ω : ℝ≥0∞) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≠ ∞) :
    ∫ᵉ ω, ENNReal.log (E (τ ω) ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤
      (((bipolarRate Q₁ S₁).toReal *
        (∫⁻ ω, (τ ω : ℝ≥0∞) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)).toReal : ℝ) : EReal) := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  set m := ∫⁻ ω, (τ ω : ℝ≥0∞) + 1 ∂μ
  set D := (bipolarRate Q₁ S₁).toReal * m.toReal
  have hτm := hτ.measurable_nat
  have hEτm : Measurable fun ω ↦ E (τ ω) ω := hE.measurable_stoppedValue hτ
  have hD (k : ℕ) : (bipolarRate Q₁ S₁).toReal * ∫ ω, ((min (τ ω) k + 1 : ℕ) : ℝ) ∂μ ≤ D := by
    rcases hdm with hd0 | hm
    · simp [D, hd0]
    refine mul_le_mul_of_nonneg_left ?_ (EReal.toReal_nonneg (bipolarRate_nonneg Q₁ S₁))
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ Nat.cast_nonneg _)
      ((measurable_from_top.comp ((hτm.min measurable_const).add_const 1)).aestronglyMeasurable)]
    refine ENNReal.toReal_mono hm (lintegral_mono fun ω ↦ ?_)
    rw [ENNReal.ofReal_natCast]
    push_cast
    gcongr
    exact_mod_cast min_le_left _ _
  have step (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (k : ℕ) :
      ∫ᵉ ω, min (ENNReal.log (E (τ ω) ω)) k ∂μ ≤ ((D - Real.log (1 - ε) : ℝ) : EReal) := by
    set W : (ℕ → 𝓧) → ℝ≥0∞ := fun ω ↦ ENNReal.ofReal (1 - ε) * E (τ ω) ω + ENNReal.ofReal ε
    have hYi : Integrable (fun ω ↦ truncLog k (W ω)) μ :=
      ENNReal.integrable_truncLog_comp hε0 ((measurable_const.mul hEτm).add measurable_const)
        (fun _ ↦ le_add_self)
    calc ∫ᵉ ω, min (ENNReal.log (E (τ ω) ω)) k ∂μ
    _ ≤ ∫ᵉ ω, ((truncLog k (W ω) - Real.log (1 - ε) : ℝ) : EReal) ∂μ :=
      eintegral_mono fun ω ↦ by simpa using ENNReal.min_log_le_truncLog_sub hε0 hε1 k (E (τ ω) ω)
    _ = ((∫ ω, truncLog k (W ω) ∂μ - Real.log (1 - ε) : ℝ) : EReal) := by
      have hYi' : Integrable (fun ω ↦ truncLog k (W ω) - Real.log (1 - ε)) μ :=
        hYi.sub (integrable_const _)
      rw [eintegral_eq_integral hYi',
        integral_sub hYi (integrable_const _), integral_const, probReal_univ, one_smul]
    _ ≤ ((D - Real.log (1 - ε) : ℝ) : EReal) := EReal.coe_le_coe_iff.2 (by
      linarith [integral_truncLog_stoppedValue_le Q₁ hS₁ hE hτ hε0 hε1 (c := k) hd hD])
  exact eintegral_le_of_forall_min_le (ENNReal.measurable_log.comp hEτm) fun k ↦
    le_of_forall_le_sub_log_one_sub fun ε hε0 hε1 ↦ step ε hε0 hε1 k

end EProcess

/-- **The Wald inequality at the bipolar rate.** For an e-process `E` for the i.i.d. laws of the
members of `S₁` and a stopping time `τ` with values in `ℕ`, the expected logarithm of `E` at `τ`
under the i.i.d. law of `Q₁` is at most the expected number `τ + 1` of observations times the
bipolar rate. The expected number of observations may be infinite, with `∞ * 0 = 0`: if the
bipolar rate is `0`, the expected logarithm is nonpositive at every stopping time. The expected
logarithm is Statlib's extended integral, which is `⊥` when the positive and negative parts of
the logarithm have infinite integrals. `Q₁` need not be a probability measure: otherwise its
i.i.d. law is `0` and both sides are `0`. [EVR26, Note 01] -/
theorem IsEProcess.eintegral_log_stoppedValue_le_mul_bipolarRate (Q₁ : Measure 𝓧)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {E : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hE : IsEProcess E (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁))
    {τ : (ℕ → 𝓧) → ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) fun ω ↦ (τ ω : WithTop ℕ)) :
    ∫ᵉ ω, ENNReal.log (E (τ ω) ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤
      ((∫⁻ ω, (τ ω : ℝ≥0∞) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) : ℝ≥0∞) : EReal) *
        bipolarRate Q₁ S₁ := by
  by_cases hQ : IsProbabilityMeasure Q₁
  swap
  · simp [Measure.infinitePi_eq_zero_of_not_isProbabilityMeasure (μ := fun _ : ℕ ↦ Q₁) (i := 0) hQ]
  set m := ∫⁻ ω, (τ ω : ℝ≥0∞) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  have hm0 : (0 : EReal) < m := by
    have : (1 : ℝ≥0∞) ≤ m :=
      calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by simp
      _ ≤ m := lintegral_mono fun ω ↦ le_add_self
    exact EReal.coe_ennreal_pos.2 (zero_lt_one.trans_le this)
  by_cases hdtop : bipolarRate Q₁ S₁ = ⊤
  · rw [hdtop, EReal.mul_top_of_pos hm0]
    exact le_top
  rcases (bipolarRate_nonneg Q₁ S₁).eq_or_lt with hd | hd
  · rw [← hd, mul_zero]
    simpa [← hd] using eintegral_log_stoppedValue_le_toReal_mul Q₁ hS₁ hE hτ hdtop (.inl hd.symm)
  by_cases hm : m = ∞
  · rw [hm, EReal.coe_ennreal_top, EReal.top_mul_of_pos hd]
    exact le_top
  refine (eintegral_log_stoppedValue_le_toReal_mul Q₁ hS₁ hE hτ hdtop (.inr hm)).trans_eq ?_
  rw [EReal.coe_mul, coe_toReal_bipolarRate hdtop, EReal.coe_ennreal_toReal hm,
    mul_comm]

/-! ### Expected stopping times of sequential tests -/

section Test

variable {τ : (ℕ → 𝓧) → WithTop ℕ}

/-- A sequential test `τ` of level `a > 0` gives the e-process `ε + (1 - ε) a⁻¹ 𝟙{τ ≤ n}` for the
i.i.d. null, for every `ε ∈ (0, 1)`. -/
private lemma isEProcess_add_indicator_le (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) τ) {a ε : ℝ} (ha0 : 0 < a)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (h_level : ∀ P ∈ S₁, Measure.infinitePi (fun _ : ℕ ↦ P) {ω | τ ω ≠ ⊤} ≤ ENNReal.ofReal a) :
    IsEProcess (fun n ω ↦ ENNReal.ofReal ε + {ω | τ ω ≤ n}.indicator
        (fun _ ↦ ENNReal.ofReal ((1 - ε) / a)) ω) (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁) := by
  have hb0 : 0 < (1 - ε) / a := div_pos (by linarith) ha0
  set b := ENNReal.ofReal ((1 - ε) / a)
  have hτtop : MeasurableSet {ω | τ ω ≠ ⊤} :=
    (hτ.measurable_enat (measurableSet_singleton ⊤)).compl
  refine IsEProcess.of_lintegral_le_one ?_ (fun n ↦
    (measurable_const.indicator (hτ.measurableSet_le_natCast n)).const_add _)
    fun σ _ _ hP ↦ ?_
  · rintro _ ⟨P, hP, rfl⟩
    have := hS₁ P hP
    infer_instance
  obtain ⟨P, hP, rfl⟩ := hP
  have := hS₁ P hP
  calc ∫⁻ ω, ENNReal.ofReal ε + {x | τ x ≤ σ ω}.indicator (fun _ ↦ b) ω
      ∂Measure.infinitePi (fun _ ↦ P)
  _ ≤ ∫⁻ ω, ENNReal.ofReal ε + {ω | τ ω ≠ ⊤}.indicator (fun _ ↦ b) ω
      ∂Measure.infinitePi (fun _ ↦ P) :=
    lintegral_mono fun ω ↦ add_le_add le_rfl (Set.indicator_le_indicator_of_subset
      (s := {x | τ x ≤ σ ω}) (t := {x | τ x ≠ ⊤})
      (fun x hx ↦ ne_top_of_le_ne_top (WithTop.natCast_ne_top _) hx) (fun _ ↦ bot_le) ω)
  _ = ENNReal.ofReal ε + b * Measure.infinitePi (fun _ ↦ P) {ω | τ ω ≠ ⊤} := by
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_indicator_const hτtop]
  _ ≤ ENNReal.ofReal ε + b * ENNReal.ofReal a := by
    gcongr
    exact h_level P hP
  _ = 1 := by
    rw [← ENNReal.ofReal_mul hb0.le, div_mul_cancel₀ _ ha0.ne',
      ← ENNReal.ofReal_add hε0.le (by linarith), add_sub_cancel, ENNReal.ofReal_one]

/-- The lower bound for a level `a > 0` and a finite expected number of observations, up to a term
`- log (1 - ε)`: the Wald inequality for the e-process `ε + (1 - ε) a⁻¹ 𝟙{τ ≤ n}` at the
stopping times `min τ k`, as `k → ∞`. -/
private lemma neg_log_le_toReal_mul_sub (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) τ) {a : ℝ} (ha0 : 0 < a)
    (h_level : ∀ P ∈ S₁, Measure.infinitePi (fun _ : ℕ ↦ P) {ω | τ ω ≠ ⊤} ≤ ENNReal.ofReal a)
    (hd : bipolarRate Q₁ S₁ ≠ ⊤)
    (hm : ∫⁻ ω, ENat.toENNReal (τ ω) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≠ ∞)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    -Real.log a ≤ (bipolarRate Q₁ S₁).toReal *
      (∫⁻ ω, ENat.toENNReal (τ ω) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)).toReal -
        Real.log (1 - ε) := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  set m := ∫⁻ ω, ENat.toENNReal (τ ω) + 1 ∂μ
  set D := (bipolarRate Q₁ S₁).toReal * m.toReal
  have hd0 := bipolarRate_nonneg Q₁ S₁
  have hτm := hτ.measurable_enat
  have hτle (k : ℕ) : MeasurableSet {ω | τ ω ≤ k} :=
    Filtration.le _ k _ (hτ.measurableSet_le_natCast k)
  -- `τ` is almost surely finite under the i.i.d. law of `Q₁`
  have hae : ∀ᵐ ω ∂μ, τ ω ≠ ⊤ := by
    filter_upwards [ae_lt_top (f := fun ω ↦ ENat.toENNReal (τ ω) + 1)
      ((measurable_from_top.comp hτm).add_const 1) hm] with ω hω
    exact ENat.toENNReal_ne_top.1 (ne_top_of_lt (lt_of_le_of_lt le_self_add hω))
  -- the stopping times `min τ k`, with values in `ℕ`
  set τk : ℕ → (ℕ → 𝓧) → ℕ := fun k ω ↦ ENat.toNat (min (τ ω) k)
  have hτk_coe (k : ℕ) (ω : ℕ → 𝓧) : ((τk k ω : ℕ) : WithTop ℕ) = min (τ ω) k :=
    ENat.natCast_toNat_min (τ ω) k
  have hτk (k : ℕ) : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      fun ω ↦ (τk k ω : WithTop ℕ) :=
    hτ.toNat_min k
  have hmk (k : ℕ) : ∫⁻ ω, (τk k ω : ℝ≥0∞) + 1 ∂μ ≤ m := lintegral_mono fun ω ↦ by
    gcongr
    have h : ((τk k ω : ℕ) : ℕ∞) ≤ τ ω := (hτk_coe k ω).trans_le (min_le_left _ _)
    exact_mod_cast ENat.toENNReal_le.2 h
  -- the e-process `ε + (1 - ε) a⁻¹ 𝟙{τ ≤ n}`
  have hb0 : 0 < (1 - ε) / a := div_pos (by linarith) ha0
  set b := ENNReal.ofReal ((1 - ε) / a)
  set L := Real.log (ε + (1 - ε) / a)
  set E : ℕ → (ℕ → 𝓧) → ℝ≥0∞ := fun n ω ↦
    ENNReal.ofReal ε + {ω | τ ω ≤ n}.indicator (fun _ ↦ b) ω
  have hE : IsEProcess E (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁) :=
    isEProcess_add_indicator_le hS₁ hτ ha0 hε0 hε1 h_level
  -- its logarithm at `min τ k`
  set g : ℕ → (ℕ → 𝓧) → ℝ := fun k ω ↦ if τ ω ≤ k then L else Real.log ε
  have hgm (k : ℕ) : Measurable (g k) := Measurable.ite (hτle k) measurable_const measurable_const
  have hgC (k : ℕ) (ω : ℕ → 𝓧) : ‖g k ω‖ ≤ max |L| |Real.log ε| := by
    rw [Real.norm_eq_abs]
    by_cases h : τ ω ≤ k
    · simp only [g, h, ↓reduceIte, le_max_left]
    · simp only [g, h, ↓reduceIte, le_max_right]
  have hlog (k : ℕ) (ω : ℕ → 𝓧) : ENNReal.log (E (τk k ω) ω) = (g k ω : EReal) := by
    have hmem : ω ∈ {x | τ x ≤ (τk k ω : WithTop ℕ)} ↔ τ ω ≤ k := by
      rw [Set.mem_ofPred_eq, hτk_coe]
      exact ⟨fun h ↦ h.trans (min_le_right _ _), fun h ↦ le_min le_rfl h⟩
    by_cases hω : τ ω ≤ k
    · simp only [E, g, Set.indicator_of_mem (hmem.2 hω), hω, ↓reduceIte]
      rw [← ENNReal.ofReal_add hε0.le hb0.le, ENNReal.log_ofReal_of_pos (by linarith)]
    · simp only [E, g, Set.indicator_of_notMem (mt hmem.1 hω), hω, ↓reduceIte, add_zero]
      rw [ENNReal.log_ofReal_of_pos hε0]
  have hk (k : ℕ) : ∫ ω, g k ω ∂μ ≤ D := by
    have hg : Integrable (g k) μ :=
      Integrable.of_bound (hgm k).aestronglyMeasurable _ (ae_of_all _ (hgC k))
    have h := hE.eintegral_log_stoppedValue_le_mul_bipolarRate Q₁ hS₁ (hτk k)
    have hmk' : ∫⁻ ω, (τk k ω : ℝ≥0∞) + 1 ∂μ ≠ ∞ := ne_top_of_le_ne_top hm (hmk k)
    rw [eintegral_congr (hlog k), eintegral_eq_integral hg, ← EReal.coe_ennreal_toReal hmk',
      ← coe_toReal_bipolarRate hd, ← EReal.coe_mul, EReal.coe_le_coe_iff] at h
    calc ∫ ω, g k ω ∂μ ≤ _ := h
    _ ≤ m.toReal * (bipolarRate Q₁ S₁).toReal :=
      mul_le_mul_of_nonneg_right (ENNReal.toReal_mono hm (hmk k)) (EReal.toReal_nonneg hd0)
    _ = D := mul_comm _ _
  -- let `k` tend to infinity
  have hL : L ≤ D := by
    have h := le_of_tendsto' (tendsto_integral_of_dominated_convergence (f := fun _ ↦ L) _
      (fun k ↦ (hgm k).aestronglyMeasurable) (integrable_const _) (fun k ↦ ae_of_all _ (hgC k))
      (hae.mono fun ω hω ↦ ?_)) hk
    · simpa using h
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hω
    refine tendsto_atTop_of_eventually_const (i₀ := n) fun k hk ↦ ?_
    have : τ ω ≤ k := by
      rw [← hn]
      exact WithTop.coe_le_coe.2 hk
    simp only [g, this, ↓reduceIte]
  have h1 : Real.log (1 - ε) - Real.log a ≤ L := by
    rw [← Real.log_div (by linarith) ha0.ne']
    exact Real.log_le_log hb0 (by linarith)
  linarith

/-- **The lower bound on expected stopping times.** A sequential test of level `α` for the i.i.d.
laws of the members of `S₁`, that is, a stopping time `τ` with `P^ℕ (τ < ∞) ≤ α` for every
`P ∈ S₁`, makes at least `log (1/α) / d` observations in expectation under the i.i.d. law of
`Q₁`, where `d` is the bipolar rate of `Q₁` against `S₁`: `log (1/α) / d ≤ 𝔼[τ + 1]`
[EVR26, Note 01]. The left
side is in `ℝ≥0∞`, with `log (1/α)` replaced by `0` for `α ≥ 1`: if `d = 0` and `α < 1`, the
expected number of observations is infinite, if `d = ∞` the bound is `0`, and if `α = 0` and
`d < ∞` the expected number of observations is infinite. Since the bipolar rate is at most the
smallest relative entropy from `Q₁` to `S₁` (`bipolarRate_le_iInf_klDiv`), this contains the
lower bound `log (1/α) / KL_inf(Q₁, S₁)` [ARR26]. -/
theorem toENNReal_log_inv_div_bipolarRate_le_lintegral (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) τ) {α : ℝ≥0∞}
    (h_level : ∀ P ∈ S₁, Measure.infinitePi (fun _ : ℕ ↦ P) {ω | τ ω ≠ ⊤} ≤ α) :
    (ENNReal.log α⁻¹).toENNReal / (bipolarRate Q₁ S₁).toENNReal ≤
      ∫⁻ ω, ENat.toENNReal (τ ω) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by
  set m := ∫⁻ ω, ENat.toENNReal (τ ω) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  by_cases hm : m = ∞
  · rw [hm]
    exact le_top
  by_cases hd : bipolarRate Q₁ S₁ = ⊤
  · simp [hd]
  by_cases hα1 : 1 ≤ α
  · rw [EReal.toENNReal_of_nonpos (ENNReal.log_le_zero_iff.2 (ENNReal.inv_le_one.2 hα1)),
      ENNReal.zero_div]
    exact bot_le
  -- the bound up to `- log (1 - ε)`, for every `ε ∈ (0, 1)`, gives the bound
  have key {a : ℝ} (ha0 : 0 < a)
      (h_level' : ∀ P ∈ S₁, Measure.infinitePi (fun _ : ℕ ↦ P) {ω | τ ω ≠ ⊤} ≤
        ENNReal.ofReal a) :
      -Real.log a ≤ (bipolarRate Q₁ S₁).toReal * m.toReal :=
    EReal.coe_le_coe_iff.1 <| le_of_forall_le_sub_log_one_sub fun ε hε0 hε1 ↦
      EReal.coe_le_coe_iff.2 (neg_log_le_toReal_mul_sub Q₁ hS₁ hτ ha0 h_level' hd hm hε0 hε1)
  rcases eq_or_ne α 0 with rfl | hα0
  · -- a test of level `0` with a finite expected number of observations would have level
    -- `exp (- (d 𝔼[τ + 1] + 1))`
    have h := key (Real.exp_pos (-((bipolarRate Q₁ S₁).toReal * m.toReal + 1)))
      fun P hP ↦ (h_level P hP).trans bot_le
    rw [Real.log_exp, neg_neg] at h
    linarith
  have hαtop : α ≠ ⊤ := ne_top_of_lt (not_le.1 hα1)
  have h := key (ENNReal.toReal_pos hα0 hαtop)
    fun P hP ↦ (h_level P hP).trans_eq (ENNReal.ofReal_toReal hαtop).symm
  rw [ENNReal.log_inv, ENNReal.log_pos_real hα0 hαtop, ← EReal.coe_neg,
    EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  refine ENNReal.div_le_of_le_mul ?_
  rw [EReal.toENNReal_of_ne_top hd, ← ENNReal.ofReal_toReal hm,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal (by linarith [mul_comm m.toReal (bipolarRate Q₁ S₁).toReal])

end Test

end ProbabilityTheory
