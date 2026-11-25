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
import LMLExplore.Bandits.ArrayModel.Basic
import LMLExplore.EValues.BipolarRate.AlmostSure
import LMLExplore.EValues.BipolarRate.Design.Algorithm
import LMLExplore.EValues.EProcess.Closure
import LMLExplore.Probability.HasLaw
import LMLExplore.Probability.Process.Filtration

/-!
# Expected stopping times are governed by the bipolar rate

Let `S₁` be a set of probability measures on `𝓧` (the null) and `Q₁` a probability measure on `𝓧`
(the alternative). The observations are the coordinates of `ℕ → 𝓧`, with the i.i.d. laws
`Measure.infinitePi fun _ ↦ P`, `P ∈ S₁`, and the filtration `Filtration.piLT`, so that `τ`
observations have been made at a time `τ`. Write `d = bipolarRate Q₁ S₁` and `Q` for the i.i.d. law
of `Q₁`.

The **Wald inequality** at the bipolar rate [EVR26, Note 01]: for every stopping time `τ` that is
almost surely finite under `Q` and every variable `Y` known at `τ` with `𝔼_P[Y 𝟙{τ < ∞}] ≤ 1` under
the i.i.d. law of every member of the null, `𝔼_Q[log Y] ≤ 𝔼_Q[τ] * d`, in `EReal`, with Statlib's
extended integral on the left. In particular `𝔼_Q[log E_τ] ≤ 𝔼_Q[τ] * d` for every e-process `E`
for the i.i.d. null. Nothing is assumed of `S₁` beyond its members being probability measures and
its being nonempty, and nothing of `Q₁`. The expectation of `τ` may be infinite, with `∞ * 0 = 0`:
if `d = 0`, the e-process has a nonpositive expected logarithm at every stopping time.

Its case `Y = 1/α` is the **lower bound on expected stopping times** [EVR26, Note 01]: a sequential
test of level `α`, that is, a stopping time `τ` with values in `WithTop ℕ` such that
`P^ℕ (τ < ∞) ≤ α` for every `P ∈ S₁` (`ProbabilityTheory.IsLevelStoppingTime`, for the null of
these i.i.d. laws), makes at least `log (1/α) / d` observations in expectation under `Q`. If
`d = 0`, every test of a level `α < 1` has an infinite expected number of observations. Since `d`
is at most the smallest relative entropy `KL_inf(Q₁, S₁)` from `Q₁` to the null
(`ProbabilityTheory.bipolarRate_le_klInf`), this contains the lower bound with
`KL_inf(Q₁, S₁)` in place of `d`, the form of the bounds of [ARR26]; the bipolar rate can be
smaller [RR26, Proposition 5.4].

The **almost sure lower bound on stopping times** [ARR26, Theorem 3.1], with the bipolar rate `d`
in place of `KL_inf(Q₁, S₁) ≥ d`: if `τ k` is a sequential test of level `exp (-k)` for the
i.i.d. null, for every `k`, then almost surely under `Q`, `liminf_k τ k / k ≥ 1 / d`, with no
relation between the tests at different levels; and nested tests `τ α`, with `τ α ≤ τ α'` for
`α' ≤ α`, have `liminf_{α → 0} τ α / log (1/α) ≥ 1 / d`.

## Main statements

* `ProbabilityTheory.eintegral_log_le_lintegral_mul_bipolarRate`: the Wald inequality
  `𝔼_Q[log Y] ≤ 𝔼_Q[τ] * d` for a variable `Y` known at `τ`.
* `ProbabilityTheory.IsEProcess.eintegral_log_stoppedValue_le_mul_bipolarRate`: the Wald
  inequality `𝔼_Q[log E_τ] ≤ 𝔼_Q[τ] * d` for an e-process.
* `ProbabilityTheory.toENNReal_log_inv_div_bipolarRate_le_lintegral`: a sequential test of level
  `α` has `log (1/α) / d ≤ 𝔼_Q[τ]`.
* `ProbabilityTheory.ae_inv_toENNReal_bipolarRate_le_liminf_div`: tests `τ k` of level `exp (-k)`
  have `liminf_k τ k / k ≥ 1 / d` almost surely, and
  `ProbabilityTheory.ae_inv_toENNReal_klInf_le_liminf_div` the same with `KL_inf(Q₁, S₁)`
  [ARR26, Theorem 3.1].
* `ProbabilityTheory.ae_inv_toENNReal_bipolarRate_le_liminf_div_log`: nested tests `τ α` of
  level `α` have `liminf_{α → 0} τ α / log (1/α) ≥ 1 / d` almost surely.

## Implementation notes

The Wald inequality is the case of one source of the Wald inequality with a design
(`Bandits.ArrayModel.eintegral_log_le_designRate_mul_lintegral`), whose rate of designs is then
the bipolar rate (`ProbabilityTheory.designRate_unique`). The transport goes from the filtration
of the observations to that of the run: in LML's array model with the single source `Unit`, the
run of an algorithm reads the observations `ω.2 i ()` in order (`Bandits.ArrayModel.reward_unique`),
so a stopping time of `Filtration.piLT` and a variable known at it, composed with these
observations, are a stopping time of the run and a variable known at it
(`Bandits.ArrayModel.IsStoppedVar`), and the observations have the i.i.d. law under the array
measure of every instance (`Bandits.ArrayModel.hasLaw_row_arrayMeasure`).

For an e-process, `Y = E_τ` is known at `τ`, and it has expectation at most `1` on `{τ < ∞}` by
the validity of e-processes with the `liminf` convention
(`ProbabilityTheory.IsEProcess.isEVar_stoppedValue_liminf`). For a sequential test of level `α`,
`Y` is the constant `1/α`, whose expectation on `{τ < ∞}` is `P^ℕ (τ < ∞) / α ≤ 1`; when
`𝔼_Q[τ] < ∞`, the test stops almost surely under `Q`.

For the almost sure bound, let `c d < 1` and `ε > 0` small. The mixture
`∑ k, (1 - exp (-ε)) exp (-ε k) exp k 𝟙{τ k ≤ n}` of the e-processes of the tests
(`ProbabilityTheory.isEProcess_tsum_mul`) is an e-process. If `τ k < c k` for infinitely many `k`,
it exceeds `exp ((1 - ε) k)` at the times `⌈c k⌉`, a rate `(1 - ε) / c > d`, which the almost sure
growth bound `ProbabilityTheory.IsEProcess.ae_limsup_log_div_le_bipolarRate` excludes. [ARR26]
bound instead the probability of `{τ k ≤ c k}` by a change of measure to a member of the null close
to `Q₁` in relative entropy, which gives the bound with `KL_inf(Q₁, S₁)` only. As in
[ARR26, proof of Theorem 3.1], the bounds for the rationals `c` are intersected, and the nested
form follows by comparing `α` with the grid points `exp (-m)`.

## References

* [ARR26] S. Agrawal, A. Ram and A. Ramdas, *On stopping times of power-one sequential tests:
  tight lower and upper bounds*, arXiv:2504.19952v2.
* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1.
* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 01,
  `results/01-bipolar-rate.md`.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}

/-- An algorithm on the single source `Unit`: every round observes it. -/
private noncomputable def oneSourceAlg : Learning.Algorithm Unit Unit 𝓧 :=
  ⟨fun _ ↦ Kernel.const _ (Measure.dirac ())⟩

/-- In the array model with one source, the observations of the source are i.i.d. -/
private lemma hasLaw_oneSource (P : Measure 𝓧) [IsProbabilityMeasure P] :
    HasLaw (fun ω : Bandits.ArrayModel.ProbSpace Unit 𝓧 ↦ fun i ↦ ω.2 i ())
      (Measure.infinitePi fun _ : ℕ ↦ P)
      (Bandits.ArrayModel.arrayMeasure (Kernel.const Unit P)) := by
  simpa only [Kernel.const_apply] using
    Bandits.ArrayModel.hasLaw_row_arrayMeasure (Kernel.const Unit P) ()

/-! ### The Wald inequality at the bipolar rate -/

/-- **The Wald inequality at the bipolar rate**, for a variable known at a stopping time. Let `τ`
be a stopping time of `Filtration.piLT`, almost surely finite under the i.i.d. law of `Q₁`, and
`Y` a variable known at `τ` which is an e-variable at `τ` for the i.i.d. laws of the members of a
nonempty null `S₁`: `𝔼_P[Y 𝟙{τ < ∞}] ≤ 1` for every `P ∈ S₁`. Then the expected logarithm of `Y`
under the i.i.d. law of `Q₁` is at most the expected number `τ` of observations times the bipolar
rate [EVR26, Note 01]. This is the case of one source of the Wald inequality with a design
(`Bandits.ArrayModel.eintegral_log_le_designRate_mul_lintegral`).

The expected logarithm is Statlib's extended integral, which is `⊥` when the positive and negative
parts of the logarithm have infinite integrals. The expected number of observations may be
infinite, with `∞ * 0 = 0`. The null must be nonempty: for the empty null every variable is an
e-variable, and at `τ = 0` the right side is `0`. -/
theorem eintegral_log_le_lintegral_mul_bipolarRate (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hS₁ne : S₁.Nonempty)
    {τ : (ℕ → 𝓧) → WithTop ℕ} (hτ : IsStoppingTime Filtration.piLT τ)
    {Y : (ℕ → 𝓧) → ℝ≥0∞} (hY : Measurable[hτ.measurableSpace] Y)
    (hYS : ∀ P ∈ S₁, ∫⁻ ω in {ω | τ ω ≠ ⊤}, Y ω ∂Measure.infinitePi (fun _ : ℕ ↦ P) ≤ 1)
    (hτQ : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), τ ω ≠ ⊤) :
    ∫ᵉ ω, ENNReal.log (Y ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤
      ((∫⁻ ω, ENat.toENNReal (τ ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) : ℝ≥0∞) : EReal) *
        bipolarRate Q₁ S₁ := by
  have hYm : Measurable Y := hY.mono hτ.measurableSpace_le le_rfl
  have hτm : Measurable τ := hτ.measurable'
  -- composed with the observations of the source in the array model with one source, they are
  -- a stopping time of the run and a variable known at it
  set obs : Bandits.ArrayModel.ProbSpace Unit 𝓧 → ℕ → 𝓧 := fun ω i ↦ ω.2 i ()
  have hlaw := hasLaw_oneSource Q₁
  have hobs : Measurable obs := by fun_prop
  have hstop : Bandits.ArrayModel.IsStoppedVar (oneSourceAlg (m𝓧 := m𝓧))
      (fun ω ↦ τ (obs ω)) (fun ω ↦ Y (obs ω)) := by
    refine Bandits.ArrayModel.isStoppedVar_iff.2 fun ω ω' t ht _ hhist ↦ ?_
    -- `τ` and `Y` are determined, on the event `{τ = t}`, by the observations before `t`
    have hobs_eq : ∀ i < t, obs ω i = obs ω' i := fun i hi ↦ by
      have h := congrFun hhist ⟨i, hi⟩
      rw [Bandits.ArrayModel.hist_eq, Bandits.ArrayModel.hist_eq] at h
      simp only [Prod.mk.injEq, true_and] at h
      rwa [Bandits.ArrayModel.reward_unique, Bandits.ArrayModel.reward_unique] at h
    exact ⟨hτ.eq_of_forall_lt ht hobs_eq, hY.eq_of_forall_lt_of_isStoppingTime hτ ht hobs_eq⟩
  have h := Bandits.ArrayModel.eintegral_log_le_designRate_mul_lintegral
    (alg := oneSourceAlg (m𝓧 := m𝓧)) (Kernel.const Unit Q₁) (Λ := Kernel.const Unit '' S₁)
    (by rintro _ ⟨P, hP, rfl⟩; have := hS₁ P hP; infer_instance) (hS₁ne.image _)
    (hτm.comp hobs) (hYm.comp hobs) hstop ?_ ?_
  · -- the rate of the designs with one source is the bipolar rate
    simp only [Function.comp_apply] at h
    rw [hlaw.eintegral_comp (f := fun x ↦ ENNReal.log (Y x))
        (ENNReal.measurable_log.comp hYm).aemeasurable,
      hlaw.lintegral_comp (f := fun x ↦ ENat.toENNReal (τ x))
        (measurable_from_top.comp hτ.measurable_enat).aemeasurable,
      designRate_unique _ ?_] at h
    · refine h.trans_eq ?_
      rw [mul_comm]
      congr 1
      simp [Set.image_image]
    · rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩ a
      have := hS₁ P hP
      simp
  · -- `Y` is an e-variable at `τ` in the array model
    rintro _ ⟨P, hP, rfl⟩
    have := hS₁ P hP
    have hs : MeasurableSet {ω | τ ω ≠ ⊤} := (measurableSet_singleton ⊤).compl.preimage hτm
    have h1 := hYS P hP
    rw [← (hasLaw_oneSource P).map_eq, setLIntegral_map hs hYm hobs] at h1
    exact h1
  · rw [← hlaw.map_eq] at hτQ
    exact ae_of_ae_map hobs.aemeasurable hτQ

/-- **The Wald inequality at the bipolar rate** for e-processes. For an e-process `E` for the
i.i.d. laws of the members of a nonempty null `S₁` and the filtration `Filtration.piLT`, and a
stopping time `τ` that is almost surely finite under the i.i.d. law of `Q₁`, the expected logarithm
of `E` at `τ` under that law is at most the expected number `τ` of observations times the bipolar
rate. The expected number of observations may be infinite, with `∞ * 0 = 0`: if the bipolar rate
is `0`, the expected logarithm is nonpositive at every stopping time. The expected logarithm is
Statlib's extended integral, which is `⊥` when the positive and negative parts of the logarithm
have infinite integrals. The null must be nonempty: for the empty null every process is an
e-process, and at `τ = 0` the right side is `0`. [EVR26, Note 01] -/
theorem IsEProcess.eintegral_log_stoppedValue_le_mul_bipolarRate (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hS₁ne : S₁.Nonempty) {E : ℕ → (ℕ → 𝓧) → ℝ≥0∞}
    (hE : IsEProcess E Filtration.piLT (iidNull S₁)) {τ : (ℕ → 𝓧) → WithTop ℕ}
    (hτ : IsStoppingTime Filtration.piLT τ)
    (hτ_top : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), τ ω ≠ ⊤) :
    ∫ᵉ ω, ENNReal.log (stoppedValue E τ ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤
      ((∫⁻ ω, ENat.toENNReal (τ ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) : ℝ≥0∞) : EReal) *
        bipolarRate Q₁ S₁ := by
  refine eintegral_log_le_lintegral_mul_bipolarRate Q₁ hS₁ hS₁ne hτ
    (hE.adapted.measurable_stoppedValue hτ) (fun P hP ↦ ?_) hτ_top
  -- on `{τ < ∞}`, `E_τ` is the e-variable of `E` at `τ` with the `liminf` convention
  have hs : MeasurableSet {ω | τ ω ≠ ⊤} :=
    (measurableSet_singleton ⊤).compl.preimage hτ.measurable'
  calc ∫⁻ ω in {ω | τ ω ≠ ⊤}, stoppedValue E τ ω ∂Measure.infinitePi (fun _ ↦ P)
  _ = ∫⁻ ω in {ω | τ ω ≠ ⊤}, (if τ ω = ⊤ then liminf (fun n ↦ E n ω) atTop
        else stoppedValue E τ ω) ∂Measure.infinitePi (fun _ ↦ P) :=
    setLIntegral_congr_fun hs fun ω hω ↦ by simp [show τ ω ≠ ⊤ from hω]
  _ ≤ ∫⁻ ω, (if τ ω = ⊤ then liminf (fun n ↦ E n ω) atTop
        else stoppedValue E τ ω) ∂Measure.infinitePi (fun _ ↦ P) :=
    setLIntegral_le_lintegral _ _
  _ ≤ 1 := (hE.isEVar_stoppedValue_liminf hτ).lintegral_le_one (infinitePi_mem_iidNull hP)

/-! ### Expected stopping times of sequential tests -/

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
    {τ : (ℕ → 𝓧) → WithTop ℕ} (hτ : IsLevelStoppingTime τ Filtration.piLT (iidNull S₁) α) :
    (ENNReal.log α⁻¹).toENNReal / (bipolarRate Q₁ S₁).toENNReal ≤
      ∫⁻ ω, ENat.toENNReal (τ ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by
  set m := ∫⁻ ω, ENat.toENNReal (τ ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  rcases S₁.eq_empty_or_nonempty with rfl | hS₁ne
  · simp [bipolarRate_empty]
  by_cases hm : m = ∞
  · rw [hm]
    exact le_top
  -- a test with a finite expected number of observations stops almost surely
  have hτQ : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), τ ω ≠ ⊤ := by
    filter_upwards [ae_lt_top (measurable_from_top.comp hτ.isStoppingTime.measurable_enat) hm]
      with ω hω
    exact ENat.toENNReal_ne_top.1 hω.ne
  -- the Wald inequality for the constant `1/α`
  have h := eintegral_log_le_lintegral_mul_bipolarRate Q₁ hS₁ hS₁ne hτ.isStoppingTime
    (Y := fun _ ↦ α⁻¹) measurable_const (fun P hP ↦ ?_) hτQ
  · rw [eintegral_const, measure_univ, EReal.coe_ennreal_one, mul_one] at h
    refine ENNReal.div_le_of_le_mul ?_
    calc (ENNReal.log α⁻¹).toENNReal ≤ ((m : EReal) * bipolarRate Q₁ S₁).toENNReal :=
      EReal.toENNReal_le_toENNReal h
    _ = m * (bipolarRate Q₁ S₁).toENNReal := by
      rw [EReal.toENNReal_mul (EReal.coe_ennreal_nonneg _), EReal.toENNReal_coe]
  · have := hS₁ P hP
    have hP' := hτ.measure_lt_top_le _ (infinitePi_mem_iidNull hP)
    simp_rw [lt_top_iff_ne_top] at hP'
    rw [setLIntegral_const]
    calc α⁻¹ * Measure.infinitePi (fun _ ↦ P) {ω | τ ω ≠ ⊤} ≤ α⁻¹ * α := by gcongr
    _ ≤ 1 := ENNReal.inv_mul_le_one α

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
