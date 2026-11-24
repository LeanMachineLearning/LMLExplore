/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import LMLExplore.EValues.EProcess.LevelStoppingTime
public import Mathlib.Probability.ProductMeasure
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.Data.ENat.Basic
import LMLExplore.EValues.BipolarRate.AlmostSure
import LMLExplore.EValues.BipolarRate.Round
import LMLExplore.EValues.EProcess.Closure
import LMLExplore.MeasureTheory.Integral.EReal
import LMLExplore.Probability.Process.Stopping
import LMLExplore.Probability.ProductMeasure
import Statlib.ForMathlib.MeasureTheory.Integral.EReal.Bochner

/-!
# Expected stopping times are governed by the bipolar rate

Let `S₁` be a set of probability measures on `𝓧` (the null) and `Q₁` a probability measure on `𝓧`
(the alternative). The observations are the coordinates of `ℕ → 𝓧`, with the i.i.d. laws
`Measure.infinitePi fun _ ↦ P`, `P ∈ S₁`, and the filtration `Filtration.piLT`, so that `τ`
observations have been made at a time `τ`. Write `d = bipolarRate Q₁ S₁` and `Q` for the i.i.d. law
of `Q₁`.

The **Wald inequality** at the bipolar rate [EVR26, Note 01]: for every e-process `E` for the
i.i.d. null and every stopping time `τ` that is finite everywhere, `𝔼_Q[log E_τ] ≤ 𝔼_Q[τ] * d`, in
`EReal`, with Statlib's extended integral on the left. Nothing is assumed of `S₁` beyond its
members being probability measures and its being nonempty, and nothing of `Q₁`. The expectation of
`τ` may be infinite, with `∞ * 0 = 0`: if `d = 0`, the e-process has a nonpositive expected
logarithm at every stopping time.

Its case `E n = α⁻¹ * 𝟙{τ ≤ n}` (mixed with a constant, so that its logarithm is finite) is the
**lower bound on expected stopping times** [EVR26, Note 01]: a sequential test of level `α`, that
is, a stopping time `τ` with values in `WithTop ℕ` such that `P^ℕ (τ < ∞) ≤ α` for every
`P ∈ S₁` (`ProbabilityTheory.IsLevelStoppingTime`, for the null of these i.i.d. laws), makes at
least `log (1/α) / d` observations in expectation under `Q`. If `d = 0`, every test of a level
`α < 1` has an infinite expected number of observations. Since `d` is at
most the smallest relative entropy `KL_inf(Q₁, S₁)` from `Q₁` to the null
(`ProbabilityTheory.bipolarRate_le_klInf`), this contains the lower bound with
`KL_inf(Q₁, S₁)` in place of `d`, the form of the bounds of [ARR26]; the bipolar rate can be
smaller [RR26, Proposition 5.4].

The **almost sure lower bound on stopping times** [ARR26, Theorem 3.1], with the bipolar rate `d`
in place of `KL_inf(Q₁, S₁) ≥ d`: if `τ k` is a sequential test of level `exp (-k)` for the
i.i.d. null, for every `k`, then almost surely under `Q`, `liminf_k τ k / k ≥ 1 / d`, with no
relation between the tests at different levels; and nested tests `τ α`, with `τ α ≤ τ α'` for
`α' ≤ α`, have `liminf_{α → 0} τ α / log (1/α) ≥ 1 / d`.

## Main statements

* `ProbabilityTheory.IsEProcess.eintegral_log_stoppedValue_le_mul_bipolarRate`: the Wald
  inequality `𝔼_Q[log E_τ] ≤ 𝔼_Q[τ] * d`.
* `ProbabilityTheory.toENNReal_log_inv_div_bipolarRate_le_lintegral`: a sequential test of level
  `α` has `log (1/α) / d ≤ 𝔼_Q[τ]`.
* `ProbabilityTheory.ae_inv_toENNReal_bipolarRate_le_liminf_div`: tests `τ k` of level `exp (-k)`
  have `liminf_k τ k / k ≥ 1 / d` almost surely, and
  `ProbabilityTheory.ae_inv_toENNReal_klInf_le_liminf_div` the same with `KL_inf(Q₁, S₁)`
  [ARR26, Theorem 3.1].
* `ProbabilityTheory.ae_inv_toENNReal_bipolarRate_le_liminf_div_log`: nested tests `τ α` of
  level `α` have `liminf_{α → 0} τ α / log (1/α) ≥ 1 / d` almost surely.

## Implementation notes

Both bounds are first proved for the filtration `Filtration.piLE`, where `τ + 1` observations have
been made at a time `τ`, and transported to `Filtration.piLT` by the shift: a stopping time of
`piLT` is `0` everywhere or `σ + 1` for a stopping time `σ` of `piLE`
(`MeasureTheory.IsStoppingTime.eq_zero_or_exists_eq_add_one`), and `fun n ↦ E (n + 1)` is an
e-process for `piLE` (`ProbabilityTheory.IsEProcess.shift`). At the time `0` nothing has been
observed, so `E 0` is a constant, at most `1` under a member of the null.

The round of the Wald inequality for a round
(`ProbabilityTheory.integral_truncLog_le_bipolarRate_mul`, in
`LMLExplore.EValues.BipolarRate.Round`) is the e-process stopped at `min τ k`, mixed with a
constant `ε` so that its logarithm is bounded below: `(1 - ε) E_{min τ k} + ε`. The bound for it
holds for the logarithm truncated above at a level `c`; then `k → ∞` (dominated convergence), the
truncation level `c → ∞` (monotone convergence for the extended integral,
`MeasureTheory.eintegral_le_of_forall_min_le`) and `ε → 0`. The lower bound on expected stopping
times applies the Wald inequality to the e-process `ε + (1 - ε) α⁻¹ 𝟙{τ ≤ n}` at the stopping times
`min τ k`.

For the almost sure bound, let `c d < 1` and `ε > 0` small. The mixture
`∑ k, (1 - exp (-ε)) exp (-ε k) exp k 𝟙{τ k ≤ n}` of the e-processes of the tests
(`ProbabilityTheory.isEProcess_tsum_mul`) is an e-process. If `τ k < c k` for infinitely many `k`,
it exceeds `exp ((1 - ε) k)` at the times `⌈c k⌉`, a rate `(1 - ε) / c > d`, which the almost sure
growth bound `ProbabilityTheory.IsEProcess.ae_limsup_log_div_le_bipolarRate` excludes. [ARR26]
bound instead the probability of `{τ k ≤ c k}` by a change of measure to a member of the null close
to `Q₁` in relative entropy, which gives the bound with `KL_inf(Q₁, S₁)` only. As in
[ARR26, proof of Theorem 3.1], the bounds for the rationals `c` are intersected, and the nested
form follows by comparing `α` with the grid points `exp (-m)`.

The proofs of the bounds in expectation are adapted from
`EValuesResearch/Results/BipolarRate.lean` and `EValuesResearch/Results/BipolarRateAux.lean`
(commit `dd4072f`) in the paper project `RemyDegenne/evalues_research`, which formalizes
[EVR26, Note 01]. They are specialized here to stopping times that are finite everywhere.

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
      (iidNull S₁))
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) fun ω ↦ (τ ω : WithTop ℕ))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {P : Measure 𝓧} (hP : P ∈ S₁) (n : ℕ) :
    ∫⁻ ω, {ω | τ ω + 1 ≤ n}.indicator
        (fun ω ↦ ENNReal.ofReal (1 - ε) * E (τ ω) ω + ENNReal.ofReal ε) ω
      ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1 := by
  have := hS₁ P hP
  have hPS : Measure.infinitePi (fun _ : ℕ ↦ P) ∈ iidNull S₁ := infinitePi_mem_iidNull hP
  have hτn : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      fun ω ↦ ((min (τ ω) (n - 1) : ℕ) : WithTop ℕ) := by
    simp_rw [Nat.mono_cast.map_min]
    exact hτ.min_natCast (n - 1)
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
      (by simpa using hE.measurable_stoppedValue hτn), lintegral_const, measure_univ, mul_one]
  _ ≤ ENNReal.ofReal (1 - ε) * 1 + ENNReal.ofReal ε := by
    gcongr
    simpa using hE.lintegral_le_one hτn (fun _ ↦ WithTop.natCast_ne_top _) hPS
  _ = 1 := by
    rw [mul_one, ← ENNReal.ofReal_add (by linarith) hε0.le, sub_add_cancel, ENNReal.ofReal_one]

/-- The Wald inequality for the payoff `(1 - ε) E_τ + ε`, truncated above at `c`: apply the Wald
inequality for a round to the e-process stopped at `min τ k`, and let `k` tend to infinity. The
bound `D` is that of the Wald inequality for the stopping times `min τ k`. -/
private lemma integral_truncLog_stoppedValue_le (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hE : IsEProcess E (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      (iidNull S₁))
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
  have hτk (k : ℕ) : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      fun ω ↦ ((min (τ ω) k : ℕ) : WithTop ℕ) := by
    simp_rw [Nat.mono_cast.map_min]
    exact hτ.min_natCast k
  have hτm : Measurable τ := by simpa using hτ.measurable'.untopA
  -- `min τ k` is determined by the coordinates up to it
  have heq (k : ℕ) {ω ω' : ℕ → 𝓧} (h : ∀ i ≤ min (τ ω) k, ω i = ω' i) :
      min (τ ω') k = min (τ ω) k :=
    Nat.cast_injective ((hτk k).eq_of_forall_le rfl h)
  have hVm (k : ℕ) : Measurable (V k) :=
    (measurable_const.mul (by simpa using hE.measurable_stoppedValue (hτk k))).add
      measurable_const
  have hVε (k : ℕ) (ω : ℕ → 𝓧) : ENNReal.ofReal ε ≤ V k ω := le_add_self
  -- the Wald inequality for the round stopped at `min τ k`
  have hk (k : ℕ) : ∫ ω, truncLog c (V k ω) ∂μ ≤ D := by
    refine (integral_truncLog_le_bipolarRate_mul (σ := fun ω ↦ min (τ ω) k + 1) Q₁ hS₁ ?_ ?_
      ((hτm.min measurable_const).add_const 1) (hVm k) (fun _ ↦ le_add_self)
      (K := k + 1) (fun ω ↦ by simp) ?_ hε0 (hVε k) hd).trans ?_
    · refine dependsOnBefore_iff.2 fun u ω ω' h hle ↦ ?_
      rw [heq k fun i hi ↦ h i (by omega)]
    · refine dependsOnBefore_iff.2 fun u ω ω' h hle ↦ ?_
      have h' : ∀ i ≤ min (τ ω) k, ω i = ω' i := fun i hi ↦ h i (by omega)
      simp only [V, heq k h',
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
      (iidNull S₁))
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
  have hτm : Measurable τ := by simpa using hτ.measurable'.untopA
  have hEτm : Measurable fun ω ↦ E (τ ω) ω := by simpa using hE.measurable_stoppedValue hτ
  have hD (k : ℕ) : (bipolarRate Q₁ S₁).toReal * ∫ ω, ((min (τ ω) k + 1 : ℕ) : ℝ) ∂μ ≤ D := by
    rcases hdm with hd0 | hm
    · simp [D, hd0]
    refine mul_le_mul_of_nonneg_left ?_
      (EReal.toReal_nonneg (bipolarRate_nonneg Q₁ fun P hP ↦ (hS₁ P hP).measure_univ.le))
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
    exact (eintegral_min_log_le_integral_truncLog_sub hε0 hε1 k hYi).trans
      (EReal.coe_le_coe_iff.2 (by
        linarith [integral_truncLog_stoppedValue_le Q₁ hS₁ hE hτ hε0 hε1 (c := k) hd hD]))
  exact eintegral_le_of_forall_min_le (ENNReal.measurable_log.comp hEτm) fun k ↦
    le_of_forall_le_sub_log_one_sub fun ε hε0 hε1 ↦ step ε hε0 hε1 k

end EProcess

/-- The Wald inequality for the filtration `Filtration.piLE`, where `τ + 1` observations have been
made at a time `τ`: `𝔼_Q[log E_τ] ≤ 𝔼_Q[τ + 1] * d`. -/
private theorem IsEProcess.eintegral_log_stoppedValue_le_mul_bipolarRate_piLE (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {E : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hE : IsEProcess E (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      (iidNull S₁))
    {τ : (ℕ → 𝓧) → WithTop ℕ}
    (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) τ) (hτ_top : ∀ ω, τ ω ≠ ⊤) :
    ∫ᵉ ω, ENNReal.log (stoppedValue E τ ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤
      ((∫⁻ ω, ENat.toENNReal (τ ω) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) : ℝ≥0∞) : EReal) *
        bipolarRate Q₁ S₁ := by
  -- `τ` is finite, so it is the cast of a time with values in `ℕ`
  obtain ⟨τ, rfl⟩ := WithTop.exists_eq_natCast_of_forall_ne_top hτ_top
  have h_cast : ∫⁻ ω, ENat.toENNReal (τ ω : WithTop ℕ) + 1 ∂Measure.infinitePi (fun _ ↦ Q₁) =
      ∫⁻ ω, (τ ω : ℝ≥0∞) + 1 ∂Measure.infinitePi (fun _ ↦ Q₁) :=
    lintegral_congr fun ω ↦ congrArg (· + 1) (ENat.toENNReal_coe (τ ω))
  rw [stoppedValue_natCast, h_cast]
  set m := ∫⁻ ω, (τ ω : ℝ≥0∞) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  have hm0 : (0 : EReal) < m := by
    have : (1 : ℝ≥0∞) ≤ m :=
      calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by simp
      _ ≤ m := lintegral_mono fun ω ↦ le_add_self
    exact EReal.coe_ennreal_pos.2 (zero_lt_one.trans_le this)
  by_cases hdtop : bipolarRate Q₁ S₁ = ⊤
  · rw [hdtop, EReal.mul_top_of_pos hm0]
    exact le_top
  rcases (bipolarRate_nonneg Q₁ (fun P hP ↦ (hS₁ P hP).measure_univ.le)).eq_or_lt with hd | hd
  · rw [← hd, mul_zero]
    simpa [← hd] using eintegral_log_stoppedValue_le_toReal_mul Q₁ hS₁ hE hτ hdtop (.inl hd.symm)
  by_cases hm : m = ∞
  · rw [hm, EReal.coe_ennreal_top, EReal.top_mul_of_pos hd]
    exact le_top
  refine (eintegral_log_stoppedValue_le_toReal_mul Q₁ hS₁ hE hτ hdtop (.inr hm)).trans_eq ?_
  rw [EReal.coe_mul, coe_toReal_bipolarRate (fun P hP ↦ (hS₁ P hP).measure_univ.le) hdtop,
    EReal.coe_ennreal_toReal hm, mul_comm]

/-- **The Wald inequality at the bipolar rate.** For an e-process `E` for the i.i.d. laws of the
members of a nonempty null `S₁` and the filtration `Filtration.piLT`, and a stopping time `τ` that
is finite everywhere, the expected logarithm of `E` at `τ` under the i.i.d. law of `Q₁` is at most
the expected number `τ` of observations times the bipolar rate. The expected number of
observations may be infinite, with `∞ * 0 = 0`: if the bipolar rate is `0`, the expected logarithm
is nonpositive at every stopping time. The expected logarithm is Statlib's extended integral,
which is `⊥` when the positive and negative parts of the logarithm have infinite integrals. The
null must be nonempty: for the empty null every process is an e-process, and at `τ = 0` the right
side is `0`. [EVR26, Note 01] -/
theorem IsEProcess.eintegral_log_stoppedValue_le_mul_bipolarRate (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hS₁ne : S₁.Nonempty) {E : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hE : IsEProcess E Filtration.piLT (iidNull S₁)) {τ : (ℕ → 𝓧) → WithTop ℕ}
    (hτ : IsStoppingTime Filtration.piLT τ) (hτ_top : ∀ ω, τ ω ≠ ⊤) :
    ∫ᵉ ω, ENNReal.log (stoppedValue E τ ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤
      ((∫⁻ ω, ENat.toENNReal (τ ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) : ℝ≥0∞) : EReal) *
        bipolarRate Q₁ S₁ := by
  rcases hτ.eq_zero_or_exists_eq_add_one Filtration.piLT_zero Filtration.piLT_add_one with
    rfl | ⟨σ, hσ, rfl⟩
  · -- nothing has been observed at time `0`: `E 0` is a constant, at most `1`
    obtain ⟨P, hP⟩ := hS₁ne
    have := hS₁ P hP
    have hE₀ : Measurable[⊥] (E 0) := Filtration.piLT_zero (X := fun _ : ℕ ↦ 𝓧) ▸ hE.adapted 0
    obtain ⟨c, hc⟩ := eq_const_of_measurable_bot hE₀
    have hc1 : c ≤ 1 := by
      simpa [hc] using (hE.isEVar 0).lintegral_le_one (infinitePi_mem_iidNull hP)
    have h0 : ∫⁻ ω, ENat.toENNReal ((0 : (ℕ → 𝓧) → WithTop ℕ) ω)
        ∂Measure.infinitePi (fun _ ↦ Q₁) = 0 :=
      (lintegral_congr fun _ ↦ ENat.toENNReal_zero).trans lintegral_zero
    rw [stoppedValue_zero, hc, h0, EReal.coe_ennreal_zero, zero_mul]
    exact (eintegral_mono fun _ ↦ ENNReal.log_le_zero_iff.2 hc1).trans_eq (eintegral_zero _)
  · -- `τ = σ + 1` for a stopping time `σ` of `Filtration.piLE`
    have hσ_top (ω : ℕ → 𝓧) : σ ω ≠ ⊤ := fun h' ↦ hτ_top ω (by simp [h'])
    simp_rw [← stoppedValue_add_one E hσ_top, ENat.toENNReal_add_one]
    exact (hE.shift Filtration.piLT_add_one).eintegral_log_stoppedValue_le_mul_bipolarRate_piLE
      Q₁ hS₁ hσ hσ_top

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
      (iidNull S₁) := by
  have hb0 : 0 < (1 - ε) / a := div_pos (by linarith) ha0
  set b := ENNReal.ofReal ((1 - ε) / a)
  have hτtop : MeasurableSet {ω | τ ω ≠ ⊤} :=
    (hτ.measurable_enat (measurableSet_singleton ⊤)).compl
  refine IsEProcess.of_lintegral_le_one (fun n ↦
    (measurable_const.indicator (hτ.measurableSet_le_natCast n)).const_add _)
    fun σ _ _ _ μ hμ ↦ ?_
  obtain ⟨P, hP, rfl⟩ := mem_iidNull.1 hμ
  have := hS₁ P hP
  calc ∫⁻ ω, ENNReal.ofReal ε + {x | τ x ≤ ((σ ω).untopA : WithTop ℕ)}.indicator (fun _ ↦ b) ω
      ∂Measure.infinitePi (fun _ ↦ P)
  _ ≤ ∫⁻ ω, ENNReal.ofReal ε + {ω | τ ω ≠ ⊤}.indicator (fun _ ↦ b) ω
      ∂Measure.infinitePi (fun _ ↦ P) :=
    lintegral_mono fun ω ↦ add_le_add le_rfl (Set.indicator_le_indicator_of_subset
      (s := {x | τ x ≤ ((σ ω).untopA : WithTop ℕ)}) (t := {x | τ x ≠ ⊤})
      (fun x hx ↦ WithTop.ne_top_of_le_natCast hx) (fun _ ↦ bot_le) ω)
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
  have hd0 := bipolarRate_nonneg Q₁ (fun P hP ↦ (hS₁ P hP).measure_univ.le)
  have hτm := hτ.measurable_enat
  have hτle (k : ℕ) : MeasurableSet {ω | τ ω ≤ k} :=
    Filtration.le _ k _ (hτ.measurableSet_le_natCast k)
  -- `τ` is almost surely finite under the i.i.d. law of `Q₁`
  have hae : ∀ᵐ ω ∂μ, τ ω ≠ ⊤ := by
    filter_upwards [ae_lt_top (f := fun ω ↦ ENat.toENNReal (τ ω) + 1)
      ((measurable_from_top.comp hτm).add_const 1) hm] with ω hω
    exact ENat.toENNReal_ne_top.1 (ne_top_of_lt (lt_of_le_of_lt le_self_add hω))
  -- the stopping times `min τ k`, which are finite
  have hτk_top (k : ℕ) (ω : ℕ → 𝓧) : min (τ ω) k ≠ ⊤ :=
    WithTop.ne_top_of_le_natCast (min_le_right _ _)
  have hτk_coe (k : ℕ) (ω : ℕ → 𝓧) : (((min (τ ω) k).untopA : ℕ) : WithTop ℕ) = min (τ ω) k :=
    WithTop.natCast_untopA (hτk_top k ω)
  have hmk (k : ℕ) : ∫⁻ ω, ENat.toENNReal (min (τ ω) k : WithTop ℕ) + 1 ∂μ ≤ m :=
    lintegral_mono fun ω ↦ by
    gcongr
    exact ENat.toENNReal_le.2 (min_le_left _ _)
  -- the e-process `ε + (1 - ε) a⁻¹ 𝟙{τ ≤ n}`
  have hb0 : 0 < (1 - ε) / a := div_pos (by linarith) ha0
  set b := ENNReal.ofReal ((1 - ε) / a)
  set L := Real.log (ε + (1 - ε) / a)
  set E : ℕ → (ℕ → 𝓧) → ℝ≥0∞ := fun n ω ↦
    ENNReal.ofReal ε + {ω | τ ω ≤ n}.indicator (fun _ ↦ b) ω
  have hE : IsEProcess E (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      (iidNull S₁) :=
    isEProcess_add_indicator_le hS₁ hτ ha0 hε0 hε1 h_level
  -- its logarithm at `min τ k`
  set g : ℕ → (ℕ → 𝓧) → ℝ := fun k ω ↦ if τ ω ≤ k then L else Real.log ε
  have hgm (k : ℕ) : Measurable (g k) := Measurable.ite (hτle k) measurable_const measurable_const
  have hgC (k : ℕ) (ω : ℕ → 𝓧) : ‖g k ω‖ ≤ max |L| |Real.log ε| := by
    rw [Real.norm_eq_abs]
    by_cases h : τ ω ≤ k
    · simp only [g, h, ↓reduceIte, le_max_left]
    · simp only [g, h, ↓reduceIte, le_max_right]
  have hlog (k : ℕ) (ω : ℕ → 𝓧) :
      ENNReal.log (stoppedValue E (fun ω ↦ min (τ ω) k) ω) = (g k ω : EReal) := by
    have hmem : ω ∈ {x | τ x ≤ ((min (τ ω) k).untopA : WithTop ℕ)} ↔ τ ω ≤ k := by
      rw [Set.mem_ofPred_eq, hτk_coe]
      exact ⟨fun h ↦ h.trans (min_le_right _ _), fun h ↦ le_min le_rfl h⟩
    rw [stoppedValue_of_eq_natCast (τ := fun ω ↦ min (τ ω) k) (hτk_coe k ω).symm]
    by_cases hω : τ ω ≤ k
    · simp only [E, g, Set.indicator_of_mem (hmem.2 hω), hω, ↓reduceIte]
      rw [← ENNReal.ofReal_add hε0.le hb0.le, ENNReal.log_ofReal_of_pos (by linarith)]
    · simp only [E, g, Set.indicator_of_notMem (mt hmem.1 hω), hω, ↓reduceIte, add_zero]
      rw [ENNReal.log_ofReal_of_pos hε0]
  have hk (k : ℕ) : ∫ ω, g k ω ∂μ ≤ D := by
    have hg : Integrable (g k) μ :=
      Integrable.of_bound (hgm k).aestronglyMeasurable _ (ae_of_all _ (hgC k))
    have h := hE.eintegral_log_stoppedValue_le_mul_bipolarRate_piLE Q₁ hS₁ (hτ.min_natCast k)
      (hτk_top k)
    have hmk' : ∫⁻ ω, ENat.toENNReal (min (τ ω) k : WithTop ℕ) + 1
        ∂Measure.infinitePi (fun _ ↦ Q₁) ≠ ∞ :=
      ne_top_of_le_ne_top hm (hmk k)
    rw [eintegral_congr (hlog k), eintegral_eq_integral hg, ← EReal.coe_ennreal_toReal hmk',
      ← coe_toReal_bipolarRate (fun P hP ↦ (hS₁ P hP).measure_univ.le) hd, ← EReal.coe_mul,
      EReal.coe_le_coe_iff] at h
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

/-- The lower bound on expected stopping times for the filtration `Filtration.piLE`, where `τ + 1`
observations have been made at a time `τ`: `log (1/α) / d ≤ 𝔼[τ + 1]`. -/
private theorem toENNReal_log_inv_div_bipolarRate_le_lintegral_piLE (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {α : ℝ≥0∞}
    (hτ : IsLevelStoppingTime τ (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      (iidNull S₁) α) :
    (ENNReal.log α⁻¹).toENNReal / (bipolarRate Q₁ S₁).toENNReal ≤
      ∫⁻ ω, ENat.toENNReal (τ ω) + 1 ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by
  have h_level (P : Measure 𝓧) (hP : P ∈ S₁) :
      Measure.infinitePi (fun _ : ℕ ↦ P) {ω | τ ω ≠ ⊤} ≤ α := by
    simpa only [lt_top_iff_ne_top] using hτ.measure_lt_top_le _ (infinitePi_mem_iidNull hP)
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
      EReal.coe_le_coe_iff.2 (neg_log_le_toReal_mul_sub Q₁ hS₁ hτ.isStoppingTime ha0 h_level' hd hm
        hε0 hε1)
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

/-- **The lower bound on expected stopping times.** A sequential test of level `α` for the i.i.d.
laws of the members of `S₁` and the filtration `Filtration.piLT`, that is, a stopping time `τ`
with `P^ℕ (τ < ∞) ≤ α` for every `P ∈ S₁`, makes at least `log (1/α) / d` observations in
expectation under the i.i.d. law of `Q₁`, where `d` is the bipolar rate of `Q₁` against `S₁`:
`log (1/α) / d ≤ 𝔼[τ]` [EVR26, Note 01]. The left side is in `ℝ≥0∞`, with `log (1/α)` replaced by
`0` for `α ≥ 1`: if `d = 0` and `α < 1`, the expected number of observations is infinite, if
`d = ∞` the bound is `0`, and if `α = 0` and `d < ∞` the expected number of observations is
infinite. Since the bipolar rate is at most the smallest relative entropy from `Q₁` to `S₁`
(`bipolarRate_le_klInf`), this contains the lower bound `log (1/α) / KL_inf(Q₁, S₁)` [ARR26]. -/
theorem toENNReal_log_inv_div_bipolarRate_le_lintegral (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {α : ℝ≥0∞}
    (hτ : IsLevelStoppingTime τ Filtration.piLT (iidNull S₁) α) :
    (ENNReal.log α⁻¹).toENNReal / (bipolarRate Q₁ S₁).toENNReal ≤
      ∫⁻ ω, ENat.toENNReal (τ ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by
  rcases hτ.isStoppingTime.eq_zero_or_exists_eq_add_one Filtration.piLT_zero
    Filtration.piLT_add_one with rfl | ⟨σ, -, rfl⟩
  · -- the test that stops at once has level `1`, unless the null is empty and `d = ∞`
    refine le_of_eq_of_le ?_ zero_le
    rcases S₁.eq_empty_or_nonempty with rfl | ⟨P, hP⟩
    · simp
    have := hS₁ P hP
    have hα : 1 ≤ α := by
      simpa using hτ.measure_lt_top_le _ (infinitePi_mem_iidNull hP)
    rw [EReal.toENNReal_of_nonpos (ENNReal.log_le_zero_iff.2 (ENNReal.inv_le_one.2 hα)),
      ENNReal.zero_div]
  · -- `τ = σ + 1` for a sequential test `σ` of the same level for `Filtration.piLE`
    simp_rw [ENat.toENNReal_add_one]
    exact toENNReal_log_inv_div_bipolarRate_le_lintegral_piLE Q₁ hS₁
      ((isLevelStoppingTime_add_one_iff Filtration.piLT_add_one).1 hτ)

end Test

/-! ### Sequential tests of small levels stop late, almost surely -/

section TestAlmostSure

variable {τ : ℕ → (ℕ → 𝓧) → WithTop ℕ}

/-- The geometric weights `(1 - exp (-ε)) * exp (-ε) ^ k` add up to `1`. -/
private lemma tsum_ofReal_weight {ε : ℝ} (hε : 0 < ε) :
    ∑' k : ℕ, ENNReal.ofReal ((1 - Real.exp (-ε)) * Real.exp (-ε) ^ k) = 1 := by
  have h0 : 0 ≤ Real.exp (-ε) := (Real.exp_pos _).le
  have h1 : Real.exp (-ε) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hpos : 0 < 1 - Real.exp (-ε) := sub_pos.2 h1
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ mul_nonneg hpos.le (pow_nonneg h0 k))
    ((summable_geometric_of_lt_one h0 h1).mul_left _), tsum_mul_left,
    tsum_geometric_of_lt_one h0 h1, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one]

/-- For every `c > 0` with `c d < 1`, where `d` is the bipolar rate, tests `τ k` of level
`exp (-k)` make at least `c k` observations for all large `k`, almost surely under the i.i.d. law
of `Q₁`. -/
private lemma ae_eventually_ofReal_mul_le (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hτ : ∀ k, IsLevelStoppingTime (τ k) Filtration.piLT (iidNull S₁)
      (ENNReal.ofReal (Real.exp (-k)))) {c D : ℝ} (hc : 0 < c) (hD0 : 0 ≤ D)
    (hD : bipolarRate Q₁ S₁ = D) (hcD : c * D < 1) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      ∀ᶠ k : ℕ in atTop, ENNReal.ofReal (c * k) ≤ ENat.toENNReal (τ k ω) := by
  -- a rate `L > D` with `c L < 1`, and the weights `exp (-ε k)` with `c L = 1 - 2 ε`
  set L := (D + 1 / c) / 2 with hL
  have hcL : c * L = (c * D + 1) / 2 := by
    rw [hL]
    field_simp
  have hDL : D < L := by
    have : D < 1 / c := by
      rw [lt_div_iff₀ hc]
      linarith
    linarith
  set ε := (1 - c * L) / 2 with hε
  have hε0 : 0 < ε := by linarith
  have hpos : 0 < 1 - Real.exp (-ε) := sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))
  -- the mixture over `k` of the e-processes `exp k * 𝟙{τ k ≤ n}` of the tests
  set w : ℕ → ℝ≥0∞ := fun k ↦ ENNReal.ofReal ((1 - Real.exp (-ε)) * Real.exp (-ε) ^ k)
  set E : ℕ → (ℕ → 𝓧) → ℝ≥0∞ := fun n ω ↦
    ∑' k, w k * ((ENNReal.ofReal (Real.exp (-k)))⁻¹ * {ω | τ k ω ≤ n}.indicator 1 ω)
  have hE : IsEProcess E Filtration.piLT (iidNull S₁) :=
    isEProcess_tsum_mul (fun k ↦ (hτ k).isEProcess_inv_mul_indicator) (tsum_ofReal_weight hε0).le
  filter_upwards [hE.ae_limsup_log_div_le_bipolarRate Q₁ hS₁] with ω hω
  rw [hD] at hω
  -- the mixture eventually stays below `exp (n L)`
  have hlt : ∀ᶠ n : ℕ in atTop, E n ω < ENNReal.ofReal (Real.exp (n * L)) := by
    filter_upwards [eventually_lt_of_limsup_lt (hω.trans_lt (EReal.coe_lt_coe_iff.2 hDL)),
      eventually_ge_atTop 1] with n hn hn1
    rw [EReal.div_lt_iff (by exact_mod_cast hn1) (EReal.natCast_ne_top n), mul_comm,
      ← EReal.coe_natCast, ← EReal.coe_mul] at hn
    rwa [← ENNReal.log_lt_log_iff, ENNReal.log_ofReal_exp]
  -- a test `τ k` that stops before `c k` makes the mixture at time `⌈c k⌉` exceed `exp (⌈c k⌉ L)`
  by_contra h
  rw [not_eventually] at h
  obtain ⟨K, hK⟩ := exists_nat_gt ((L - Real.log (1 - Real.exp (-ε))) / ε)
  have htend : Tendsto (fun k : ℕ ↦ ⌈c * k⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  obtain ⟨k, hk, hkK, hkn⟩ :=
    (h.and_eventually ((eventually_ge_atTop K).and (htend.eventually hlt))).exists
  rw [not_le] at hk
  have hτn : τ k ω ≤ (⌈c * k⌉₊ : WithTop ℕ) := by
    refine ENat.toENNReal_le.1
      (hk.le.trans ((ENNReal.ofReal_le_ofReal (Nat.le_ceil _)).trans_eq ?_))
    rw [ENNReal.ofReal_natCast]
    exact (ENat.toENNReal_coe _).symm
  have hge : ENNReal.ofReal ((1 - Real.exp (-ε)) * Real.exp (-ε) ^ k * Real.exp k) ≤
      E ⌈c * k⌉₊ ω := by
    refine le_of_eq_of_le ?_ (le_tsum _ k)
    have hinv : (ENNReal.ofReal (Real.exp (-k)))⁻¹ = ENNReal.ofReal (Real.exp k) := by
      rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_neg]
    rw [Set.indicator_of_mem hτn, Pi.one_apply, mul_one, hinv,
      ← ENNReal.ofReal_mul (by positivity)]
  have hreal : Real.exp (⌈c * k⌉₊ * L) ≤
      (1 - Real.exp (-ε)) * Real.exp (-ε) ^ k * Real.exp k := by
    rw [← Real.exp_natCast_mul, ← Real.exp_log hpos, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hceil : (⌈c * k⌉₊ : ℝ) < c * k + 1 := Nat.ceil_lt_add_one (by positivity)
    have hkK' : (K : ℝ) ≤ k := by exact_mod_cast hkK
    rw [div_lt_iff₀ hε0] at hK
    nlinarith
  exact absurd ((ENNReal.ofReal_le_ofReal hreal).trans hge) (not_le.2 hkn)

/-- Almost surely, for every `r < 1 / d`, where `d` is the bipolar rate, tests `τ k` of level
`exp (-k)` make at least `r k` observations for all large `k`. -/
private lemma ae_forall_lt_eventually_mul_le (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hτ : ∀ k, IsLevelStoppingTime (τ k) Filtration.piLT (iidNull S₁)
      (ENNReal.ofReal (Real.exp (-k)))) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ r < (bipolarRate Q₁ S₁).toENNReal⁻¹,
      ∀ᶠ k : ℕ in atTop, r * k ≤ ENat.toENNReal (τ k ω) := by
  by_cases hd : bipolarRate Q₁ S₁ = ⊤
  · simp [hd]
  have hS₁' : ∀ P ∈ S₁, P Set.univ ≤ 1 := fun P hP ↦ (hS₁ P hP).measure_univ.le
  set D := (bipolarRate Q₁ S₁).toReal
  have hD0 : 0 ≤ D := EReal.toReal_nonneg (bipolarRate_nonneg Q₁ hS₁')
  -- the bound for every rational `q > 0` with `q D < 1`
  have hrat : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ q : ℚ, 0 < (q : ℝ) →
      (q : ℝ) * D < 1 → ∀ᶠ k : ℕ in atTop, ENNReal.ofReal (q * k) ≤ ENat.toENNReal (τ k ω) := by
    refine ae_all_iff.2 fun q ↦ ?_
    by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) * D < 1
    · filter_upwards [ae_eventually_ofReal_mul_le Q₁ hS₁ hτ hq.1 hD0
        (coe_toReal_bipolarRate hS₁' hd).symm hq.2] with ω hω _ _
      exact hω
    · exact ae_of_all _ fun ω h1 h2 ↦ absurd ⟨h1, h2⟩ hq
  filter_upwards [hrat] with ω hω r hr
  rw [EReal.toENNReal_of_ne_top hd] at hr
  -- a rational `q` with `r < q < 1 / D`
  obtain ⟨q, -, hrq, hqD⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hr
  have hq : 0 < (q : ℝ) := by simpa using pos_of_gt hrq
  have hqD' := ENNReal.mul_lt_of_lt_div (a := ENNReal.ofReal q) (b := 1) (by rwa [one_div])
  rw [← ENNReal.ofReal_mul hq.le, ENNReal.ofReal_lt_one] at hqD'
  filter_upwards [hω q hq hqD'] with k hk
  rw [ENNReal.ofReal_mul hq.le, ENNReal.ofReal_natCast] at hk
  exact (mul_le_mul_left hrq.le _).trans hk

/-- **Tests of small levels stop late, almost surely.** Let `τ k` be a sequential test of level
`exp (-k)` for the i.i.d. laws of the members of `S₁`, for every `k`: a stopping time of the
filtration `Filtration.piLT` with `P^ℕ (τ k < ∞) ≤ exp (-k)` for every `P ∈ S₁`. Almost surely
under the i.i.d. law of `Q₁`, `liminf_k τ k / k ≥ 1 / d`, where `d` is the bipolar rate of `Q₁`
against `S₁`. The tests at different levels need not be related. If `d = 0`, the tests make, almost
surely, more than `c k` observations for all large `k`, for every `c`. [ARR26, Theorem 3.1] states
the bound with `KL_inf(Q₁, S₁)`, which is at least `d`
(`ProbabilityTheory.ae_inv_toENNReal_klInf_le_liminf_div`). -/
theorem ae_inv_toENNReal_bipolarRate_le_liminf_div (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hτ : ∀ k : ℕ, IsLevelStoppingTime (τ k) Filtration.piLT (iidNull S₁)
      (ENNReal.ofReal (Real.exp (-k)))) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      (bipolarRate Q₁ S₁).toENNReal⁻¹ ≤ liminf (fun k : ℕ ↦ ENat.toENNReal (τ k ω) / k) atTop := by
  filter_upwards [ae_forall_lt_eventually_mul_le Q₁ hS₁ hτ] with ω hω
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hω r hr, eventually_ge_atTop 1] with k hk hk1
  rwa [ENNReal.le_div_iff_mul_le (.inl (by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hk1)))
    (.inl (ENNReal.natCast_ne_top k))]

/-- **Tests of small levels stop late, almost surely**, with the smallest relative entropy
`KL_inf(Q₁, S₁)` from `Q₁` to the null: `liminf_k τ k / k ≥ 1 / KL_inf(Q₁, S₁)` for sequential tests
`τ k` of level `exp (-k)` [ARR26, Theorem 3.1]. The bipolar rate is at most `KL_inf(Q₁, S₁)`
(`bipolarRate_le_klInf`), so `ae_inv_toENNReal_bipolarRate_le_liminf_div` is stronger. -/
theorem ae_inv_toENNReal_klInf_le_liminf_div (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hτ : ∀ k : ℕ, IsLevelStoppingTime (τ k) Filtration.piLT (iidNull S₁)
      (ENNReal.ofReal (Real.exp (-k)))) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      (klInf Q₁ S₁).toENNReal⁻¹ ≤ liminf (fun k : ℕ ↦ ENat.toENNReal (τ k ω) / k) atTop := by
  filter_upwards [ae_inv_toENNReal_bipolarRate_le_liminf_div Q₁ hS₁ hτ] with ω hω
  exact (ENNReal.inv_le_inv.2 (EReal.toENNReal_le_toENNReal (bipolarRate_le_klInf Q₁ hS₁))).trans hω

/-- A level `α < exp (-N)` lies below a grid point `exp (-m)` with `N ≤ m` and
`log (1/α) < m + 1`. -/
private lemma exists_le_ofReal_exp_neg {α : ℝ≥0∞} {N : ℕ} (hα0 : 0 < α)
    (hαN : α < ENNReal.ofReal (Real.exp (-N))) :
    ∃ m : ℕ, N ≤ m ∧ α ≤ ENNReal.ofReal (Real.exp (-m)) ∧
      ∃ b : ℝ, 0 < b ∧ b < m + 1 ∧ (ENNReal.log α⁻¹).toENNReal = ENNReal.ofReal b := by
  have hα1 : α < 1 := hαN.trans_le (ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2
    (neg_nonpos.2 (Nat.cast_nonneg _))))
  have hlog_top : ENNReal.log α⁻¹ ≠ ⊤ := by simpa using hα0.ne'
  have hlog_bot : ENNReal.log α⁻¹ ≠ ⊥ := by simpa using hα1.ne_top
  set b := (ENNReal.log α⁻¹).toReal
  have hb : ENNReal.log α = ((-b : ℝ) : EReal) := by
    rw [EReal.coe_neg, EReal.coe_toReal hlog_top hlog_bot, ENNReal.log_inv, neg_neg]
  have hb0 : 0 < b := by
    rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal hlog_top hlog_bot, EReal.coe_zero,
      ENNReal.zero_lt_log_iff]
    exact ENNReal.one_lt_inv.2 hα1
  refine ⟨⌊b⌋₊, Nat.le_floor ?_, ?_, b, hb0, Nat.lt_floor_add_one b,
    EReal.toENNReal_of_ne_top hlog_top⟩
  · have h := ENNReal.log_lt_log hαN
    rw [hb, ENNReal.log_ofReal_exp, EReal.coe_lt_coe_iff] at h
    linarith
  · rw [← ENNReal.log_le_log_iff, hb, ENNReal.log_ofReal_exp, EReal.coe_le_coe_iff,
      neg_le_neg_iff]
    exact Nat.floor_le hb0.le

/-- **Nested tests of small levels stop late, almost surely.** Let `τ α` be a sequential test of
level `α` for the i.i.d. laws of the members of `S₁`, in the filtration `Filtration.piLT`, for
every `α ∈ (0, a)`, and let the tests be nested: `τ α ≤ τ α'` for `α' ≤ α` in `(0, a)`. Almost
surely under the i.i.d. law of `Q₁`, `liminf_{α → 0} τ α / log (1/α) ≥ 1 / d`, where `d` is the
bipolar rate of `Q₁` against `S₁`. [ARR26, Theorem 3.1] states the bound with `KL_inf(Q₁, S₁)`,
which is at least `d`, and `a = 1/2`. -/
theorem ae_inv_toENNReal_bipolarRate_le_liminf_div_log (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {τ : ℝ≥0∞ → (ℕ → 𝓧) → WithTop ℕ} {a : ℝ≥0∞}
    (ha : 0 < a) (hτ : ∀ α ∈ Set.Ioo 0 a, IsLevelStoppingTime (τ α) Filtration.piLT (iidNull S₁) α)
    (hτa : ∀ ω, AntitoneOn (τ · ω) (Set.Ioo 0 a)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), (bipolarRate Q₁ S₁).toENNReal⁻¹ ≤
      liminf (fun α ↦ ENat.toENNReal (τ α ω) / (ENNReal.log α⁻¹).toENNReal) (𝓝[>] 0) := by
  -- the tests on the grid `exp (-(k + k₀))`, inside `(0, a)`
  set g : ℕ → ℝ≥0∞ := fun k ↦ ENNReal.ofReal (Real.exp (-k))
  have hg0 (k : ℕ) : 0 < g k := ENNReal.ofReal_pos.2 (Real.exp_pos _)
  have hg (k j : ℕ) (h : k ≤ j) : g j ≤ g k :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by simpa using h))
  have hlog (k : ℕ) : ENNReal.log (g k) = ((-k : ℝ) : EReal) := ENNReal.log_ofReal_exp _
  have hgtend : Tendsto g atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop))
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (hgtend.eventually (eventually_lt_nhds ha))
  have hσ (k : ℕ) : IsLevelStoppingTime (τ (g (k + k₀))) Filtration.piLT (iidNull S₁) (g k) :=
    (hτ _ ⟨hg0 _, hk₀ _ (by omega)⟩).mono (hg _ _ (by omega))
  filter_upwards [ae_forall_lt_eventually_mul_le Q₁ hS₁ hσ] with ω hω
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ le_liminf_of_le (by isBoundedDefault) ?_
  -- a rate `s` with `r < s < 1 / d`, and the grid index `J` after which it applies
  obtain ⟨s, hrs, hsd⟩ := exists_between hr
  have hs_top : s ≠ ⊤ := (hsd.trans_le le_top).ne
  have hrs' : r.toReal < s.toReal := ENNReal.toReal_strict_mono hs_top hrs
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hω s hsd)
  obtain ⟨J', hJ'⟩ := exists_nat_gt (r.toReal * (k₀ + 1) / (s.toReal - r.toReal))
  rw [div_lt_iff₀ (sub_pos.2 hrs')] at hJ'
  -- for `α < exp (-(max J J' + k₀))`, the test `τ α` stops after the test of the grid point
  -- `exp (-m) ≥ α`, with `log (1/α) < m + 1`
  filter_upwards [Ioo_mem_nhdsGT (hg0 (max J J' + k₀))] with α ⟨hα0, hαN⟩
  obtain ⟨m, hNm, hαm, b, hb0, hbm, hB⟩ := exists_le_ofReal_exp_neg hα0 hαN
  have hτα : s * (m - k₀ : ℕ) ≤ ENat.toENNReal (τ α ω) := by
    refine (hJ (m - k₀) (by omega)).trans (ENat.toENNReal_le.2 ?_)
    rw [Nat.sub_add_cancel (by omega)]
    exact hτa ω ⟨hα0, hαm.trans_lt (hk₀ m (by omega))⟩ ⟨hg0 m, hk₀ m (by omega)⟩ hαm
  rw [hB, ENNReal.le_div_iff_mul_le (.inl (ENNReal.ofReal_pos.2 hb0).ne')
    (.inl ENNReal.ofReal_ne_top)]
  -- the bound in `ℝ`, with `log (1/α) = b < m + 1` and `m - k₀ ≥ J'`
  have hmk : ((m - k₀ : ℕ) : ℝ) = m - k₀ := Nat.cast_sub (by omega)
  have hJ'm : (J' : ℝ) ≤ m - k₀ := by
    rw [← hmk]
    exact_mod_cast (by omega : J' ≤ m - k₀)
  have hreal : r.toReal * b ≤ s.toReal * ((m - k₀ : ℕ) : ℝ) := by
    rw [hmk]
    nlinarith [ENNReal.toReal_nonneg (a := r)]
  refine le_trans ?_ hτα
  calc r * ENNReal.ofReal b = ENNReal.ofReal (r.toReal * b) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (hrs.trans_le le_top).ne]
  _ ≤ ENNReal.ofReal (s.toReal * ((m - k₀ : ℕ) : ℝ)) := ENNReal.ofReal_le_ofReal hreal
  _ = s * (m - k₀ : ℕ) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hs_top,
          ENNReal.ofReal_natCast]

end TestAlmostSure

end ProbabilityTheory
