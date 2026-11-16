/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.EValues.BipolarRate.AlmostSure
import LMLExplore.EValues.BipolarRate.Numeraire
import LMLExplore.Probability.ProductMeasure

/-!
# A Stein lemma for composite nulls, with the bipolar rate as exponent

A non-randomized test of a null `S`, a set of measures on `Ω`, rejects on a measurable set `C`; its
size is the worst-case null probability `⨆ P ∈ S, P C`, and its power against a law `Q` is `Q C`.
The smallest size of a test of power at least `β` is `minTestSize Q S β`.

Let `S₁` be a set of probability measures on `𝓧` (the null) and `Q₁` a probability measure on `𝓧`
(the alternative). With `n` observations, the null is the set of the `n`-fold products `P ^ n` of
the members of `S₁` and the alternative is `Q₁ ^ n`, so that the smallest size of a test of power
at least `β` is
$\alpha^*_n(\beta)=\inf\{\sup_{P\in S_1}P^{\otimes n}(C):\ Q_1^{\otimes n}(C)\ge\beta\}$.
For every `β ∈ (0, 1)`, `-(1/n) log α*_n(β)` tends to the bipolar rate `d = bipolarRate Q₁ S₁`,
the optimal growth rate of the evidence against the i.i.d. null [RR26], also when it is infinite
[EVR26, Note 01]: the exponent does not depend on `β`, a strong converse. Nothing is assumed on
`S₁` besides that its members are probability measures: no domination, convexity or compactness.
For a simple null `{P₁}`, the bipolar rate is `klDiv Q₁ P₁`
(`ProbabilityTheory.bipolarRate_singleton`), and this is the Chernoff–Stein lemma with its strong
converse.

* **Achievability**, for `β < 1`. For a real `r < d`, the event where the numeraire of the
  `n`-sample null exceeds `exp (n r)` has probability at most `exp (- n r)` under every member of
  the null, by Markov's inequality (`ProbabilityTheory.IsEVar.measure_inv_le_le`). Almost surely
  under the i.i.d. law of `Q₁`, the numeraires grow at the rate `d`
  (`ProbabilityTheory.ae_tendsto_log_numeraire_div_bipolarRate`), so that the first `n`
  observations are eventually in that event, whose probability under `Q₁ ^ n` therefore tends to
  `1`.
* **Strong converse**, for `0 < β`. For a real `r > d`, let `C n` be a test of `n` observations of
  power at least `β` and size at most `exp (- n r)` when there is one, and `∅` otherwise. The bets
  `exp (n r) 𝟙_{C n}` are `n`-sample e-variables, so almost surely they eventually stay below
  `exp (n r)` (`ProbabilityTheory.ae_limsup_log_div_le_bipolarRate`): almost surely the first `n`
  observations are eventually outside `C n`, whose probability under `Q₁ ^ n` therefore tends to
  `0`. Eventually it is below `β`, so that eventually no test of power at least `β` has size at
  most `exp (- n r)`.

The members of the null must be probability measures, and not only finite measures: for a real
`c > 0`, replacing the simple null `{P}` by `{c • P}` multiplies the size of every test of `n`
observations by `c ^ n`, while it changes neither the `n`-sample e-variables nor the bipolar rate.
The alternative must be a probability measure as well: for `Q₁ = 0`, `β > 0` and `n ≥ 1`, no test
has power `β`, so that `α*_n(β) = ∞` and the quotient is `⊥`.

## Main definitions

* `ProbabilityTheory.minTestSize Q S β`: the infimum of `⨆ P ∈ S, P C` over the measurable sets `C`
  with `β ≤ Q C`.

## Main statements

* `ProbabilityTheory.bipolarRate_le_liminf_neg_log_minTestSize_div`: achievability,
  `d ≤ liminf -(1/n) log α*_n(β)` for `β < 1`.
* `ProbabilityTheory.limsup_neg_log_minTestSize_div_le_bipolarRate`: the strong converse,
  `limsup -(1/n) log α*_n(β) ≤ d` for `0 < β`.
* `ProbabilityTheory.tendsto_neg_log_minTestSize_div_bipolarRate`: **the Stein lemma for
  composite nulls**, `-(1/n) log α*_n(β) → d` for `β ∈ (0, 1)` [EVR26, Note 01].
* `ProbabilityTheory.tendsto_neg_log_minTestSize_div_klDiv`: the Chernoff–Stein lemma, with its
  strong converse, for a simple null `{P₁}`: the limit is `klDiv Q₁ P₁`.

## Implementation notes

The statements and proofs are adapted from `EValuesResearch/Results/Numeraire.lean`
(commit `dd4072f`) in the paper project `RemyDegenne/evalues_research`, which formalizes
[EVR26, Note 01], rewritten on the API of LMLExplore. The probabilities of the events under
`Q₁ ^ n` are those of their preimages under the initial segments of the i.i.d. sequence
(`MeasureTheory.measurePreserving_initSeg`), and their limits come from
`MeasureTheory.tendsto_measure_pi_one_of_ae_eventually_mem` and
`MeasureTheory.tendsto_measure_pi_zero_of_ae_eventually_notMem`.

## References

* [RR26] A. Ram and A. Ramdas, *The optimal betting wealth growth rate*, arXiv:2604.25280v1.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory Filter InformationTheory
open scoped ENNReal Topology

namespace ProbabilityTheory

/-! ### The smallest size of a test of given power -/

section MinTestSize

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {S T : Set (Measure Ω)}
  {β β' : ℝ≥0∞} {C : Set Ω}

/-- The smallest size of a non-randomized test of the null `S` with power at least `β` against
`Q`: the infimum, over the measurable sets `C` with `β ≤ Q C`, of the worst-case null probability
`⨆ P ∈ S, P C` of `C`. It is `∞` when no measurable set has measure at least `β` under `Q`. -/
noncomputable def minTestSize (Q : Measure Ω) (S : Set (Measure Ω)) (β : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (C : Set Ω) (_ : MeasurableSet C) (_ : β ≤ Q C), ⨆ P ∈ S, P C

/-- The smallest size of a test, unfolded. -/
lemma minTestSize_def (Q : Measure Ω) (S : Set (Measure Ω)) (β : ℝ≥0∞) :
    minTestSize Q S β = ⨅ (C : Set Ω) (_ : MeasurableSet C) (_ : β ≤ Q C), ⨆ P ∈ S, P C :=
  (rfl)

/-- The smallest size is at most the size of every test of power at least `β`. -/
lemma minTestSize_le (hC : MeasurableSet C) (hβ : β ≤ Q C) : minTestSize Q S β ≤ ⨆ P ∈ S, P C :=
  iInf₂_le_of_le C hC (iInf_le _ hβ)

/-- A lower bound on the smallest size is a lower bound on the size of every test of power at
least `β`. -/
lemma le_minTestSize_iff {c : ℝ≥0∞} :
    c ≤ minTestSize Q S β ↔ ∀ C, MeasurableSet C → β ≤ Q C → c ≤ ⨆ P ∈ S, P C := by
  simp only [minTestSize, le_iInf_iff]

/-- The smallest size of a test is monotone in the null and in the power. -/
@[gcongr]
lemma minTestSize_mono (hST : S ⊆ T) (hβ : β ≤ β') : minTestSize Q S β ≤ minTestSize Q T β' :=
  le_minTestSize_iff.2 fun _ hC hβC ↦ (minTestSize_le hC (hβ.trans hβC)).trans (biSup_mono hST)

/-- For a simple null `{P}`, the smallest size of a test of power at least `β` is the smallest
probability under `P` of a measurable set of measure at least `β` under `Q`. -/
lemma minTestSize_singleton (Q P : Measure Ω) (β : ℝ≥0∞) :
    minTestSize Q {P} β = ⨅ (C : Set Ω) (_ : MeasurableSet C) (_ : β ≤ Q C), P C := by
  simp only [minTestSize, iSup_singleton]

end MinTestSize

/-! ### The Stein lemma -/

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)} {β : ℝ≥0∞}

/-- For `n ≥ 1`, a size `x` at most `exp (- n r)` has `r ≤ -(1/n) log x`. -/
private lemma le_neg_log_div_of_le_ofReal_exp {x : ℝ≥0∞} {n : ℕ} {r : ℝ} (hn : 1 ≤ n)
    (h : x ≤ ENNReal.ofReal (Real.exp (-(n * r)))) :
    (r : EReal) ≤ -ENNReal.log x / (n : EReal) := by
  have hlog := ENNReal.log_le_log h
  rw [ENNReal.log_ofReal_exp, EReal.coe_neg] at hlog
  rw [EReal.le_div_iff_mul_le (by exact_mod_cast hn) (EReal.natCast_ne_top n), mul_comm,
    ← EReal.coe_natCast, ← EReal.coe_mul]
  exact EReal.le_neg_of_le_neg hlog

/-- For `n ≥ 1`, a size `x` at least `exp (- n r)` has `-(1/n) log x ≤ r`. -/
private lemma neg_log_div_le_of_ofReal_exp_le {x : ℝ≥0∞} {n : ℕ} {r : ℝ} (hn : 1 ≤ n)
    (h : ENNReal.ofReal (Real.exp (-(n * r))) ≤ x) : -ENNReal.log x / (n : EReal) ≤ r := by
  have hlog := ENNReal.log_le_log h
  rw [ENNReal.log_ofReal_exp, EReal.coe_neg] at hlog
  rw [EReal.div_le_iff_le_mul (by exact_mod_cast hn) (EReal.natCast_ne_top n),
    ← EReal.coe_natCast, ← EReal.coe_mul]
  exact EReal.neg_le_of_neg_le hlog

/-- For a real `r` below the bipolar rate and `β < 1`, eventually some test of `n` observations of
power at least `β` has size at most `exp (- n r)`: the event where the numeraire of the `n`-sample
null exceeds `exp (n r)`. -/
private lemma eventually_minTestSize_le (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hβ : β < 1) {r : ℝ}
    (hr : (r : EReal) < bipolarRate Q₁ S₁) :
    ∀ᶠ n : ℕ in atTop, minTestSize (Measure.pi fun _ : Fin n ↦ Q₁)
      ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) β ≤ ENNReal.ofReal (Real.exp (-(n * r))) := by
  set E : (n : ℕ) → (Fin n → 𝓧) → ℝ≥0∞ := fun n ↦ numeraire (Measure.pi fun _ : Fin n ↦ Q₁)
    ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁)
  set C : (n : ℕ) → Set (Fin n → 𝓧) := fun n ↦
    {x | (ENNReal.ofReal (Real.exp (-(n * r))))⁻¹ ≤ E n x}
  have hCm (n : ℕ) : MeasurableSet (C n) :=
    measurableSet_le measurable_const (measurable_numeraire _ _)
  -- Markov's inequality under the null
  have hnull (n : ℕ) : ⨆ μ ∈ (fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁, μ (C n) ≤
      ENNReal.ofReal (Real.exp (-(n * r))) := by
    refine iSup₂_le ?_
    rintro _ ⟨P, hP, rfl⟩
    have := hS₁ P hP
    exact (isEVar_numeraire _ _).measure_inv_le_le
      (Set.mem_image_of_mem (fun P ↦ Measure.pi fun _ : Fin n ↦ P) hP) _
  -- almost surely, the first `n` observations are eventually in `C n`
  have hae : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
      initSeg n ω ∈ C n := by
    filter_upwards [ae_tendsto_log_numeraire_div_bipolarRate Q₁ hS₁] with ω hω
    filter_upwards [hω.eventually (lt_mem_nhds hr), eventually_ge_atTop 1] with n hn hn1
    simp only [C, Set.mem_ofPred_eq]
    rw [EReal.lt_div_iff (by exact_mod_cast hn1) (EReal.natCast_ne_top n)] at hn
    rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_neg,
      ← ENNReal.log_le_log_iff, ENNReal.log_ofReal_exp, EReal.coe_mul, EReal.coe_natCast,
      mul_comm]
    exact hn.le
  filter_upwards [(tendsto_order.1 (tendsto_measure_pi_one_of_ae_eventually_mem Q₁ hCm hae)).1 β
    hβ] with n hn
  exact (minTestSize_le (hCm n) hn.le).trans (hnull n)

/-- For a real `r` above the bipolar rate and `0 < β`, eventually every test of `n` observations
of power at least `β` has size at least `exp (- n r)`. Otherwise the bets `exp (n r) 𝟙_C` on the
tests `C` of smaller size would reach `exp (n r)` infinitely often with positive probability. -/
private lemma eventually_le_minTestSize (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hβ : 0 < β) {r : ℝ}
    (hr : bipolarRate Q₁ S₁ < r) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (-(n * r))) ≤
      minTestSize (Measure.pi fun _ : Fin n ↦ Q₁)
        ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) β := by
  classical
  -- a test of power at least `β` and size at most `exp (- n r)` if there is one, `∅` otherwise
  set p : (n : ℕ) → Set (Fin n → 𝓧) → Prop := fun n C ↦ MeasurableSet C ∧
    β ≤ Measure.pi (fun _ : Fin n ↦ Q₁) C ∧
    ⨆ μ ∈ (fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁, μ C ≤ ENNReal.ofReal (Real.exp (-(n * r)))
  set C : (n : ℕ) → Set (Fin n → 𝓧) := fun n ↦ if h : ∃ C, p n C then h.choose else ∅
  have hC (n : ℕ) : MeasurableSet (C n) ∧
      ⨆ μ ∈ (fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁, μ (C n) ≤
        ENNReal.ofReal (Real.exp (-(n * r))) := by
    by_cases h : ∃ C, p n C
    · simp only [C, h, dite_true]
      exact ⟨h.choose_spec.1, h.choose_spec.2.2⟩
    · simp [C, h]
  have hCQ (n : ℕ) (h : ∃ C, p n C) : β ≤ Measure.pi (fun _ : Fin n ↦ Q₁) (C n) := by
    simp only [C, h, dite_true]
    exact h.choose_spec.2.1
  -- the bets `exp (n r) 𝟙_{C n}` are `n`-sample e-variables
  set M : (n : ℕ) → (Fin n → 𝓧) → ℝ≥0∞ := fun n ↦
    (C n).indicator fun _ ↦ ENNReal.ofReal (Real.exp (n * r))
  have hM (n : ℕ) : IsEVar (M n) ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) := by
    refine IsEVar.of_lintegral_le_one ?_ (measurable_const.indicator (hC n).1) fun μ hμ ↦ ?_
    · rintro _ ⟨P, hP, rfl⟩
      have := hS₁ P hP
      infer_instance
    · rw [lintegral_indicator_const (hC n).1]
      calc ENNReal.ofReal (Real.exp (n * r)) * μ (C n)
      _ ≤ ENNReal.ofReal (Real.exp (n * r)) * ENNReal.ofReal (Real.exp (-(n * r))) := by
        gcongr
        exact (le_biSup (fun μ : Measure (Fin n → 𝓧) ↦ μ (C n)) hμ).trans (hC n).2
      _ = 1 := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, ENNReal.ofReal_one]
  -- almost surely, the first `n` observations are eventually outside `C n`
  have hae : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ᶠ n : ℕ in atTop,
      initSeg n ω ∉ C n := by
    filter_upwards [ae_limsup_log_div_le_bipolarRate Q₁ hS₁ hM] with ω hω
    filter_upwards [eventually_lt_of_limsup_lt (hω.trans_lt hr), eventually_ge_atTop 1]
      with n hn hn1
    intro hmem
    rw [show M n (initSeg n ω) = ENNReal.ofReal (Real.exp (n * r)) from
        Set.indicator_of_mem hmem _, ENNReal.log_ofReal_exp,
      EReal.div_lt_iff (by exact_mod_cast hn1) (EReal.natCast_ne_top n), ← EReal.coe_natCast,
      ← EReal.coe_mul, EReal.coe_lt_coe_iff, mul_comm] at hn
    exact lt_irrefl _ hn
  filter_upwards [(tendsto_order.1 (tendsto_measure_pi_zero_of_ae_eventually_notMem Q₁
    (fun n ↦ (hC n).1) hae)).2 β hβ] with n hn
  refine le_minTestSize_iff.2 fun D hD hβD ↦ le_of_not_gt fun hlt ↦ ?_
  exact (hn.trans_le (hCQ n ⟨D, hD, hβD, hlt.le⟩)).false

/-- **Achievability in the Stein lemma for composite nulls.** For `β < 1`, the smallest size
`α*_n(β)` of a test of `n` observations of the i.i.d. null `S₁` with power at least `β` against
`Q₁ ^ n` has `liminf -(1/n) log α*_n(β)` at least the bipolar rate [EVR26, Note 01]. -/
theorem bipolarRate_le_liminf_neg_log_minTestSize_div (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hβ : β < 1) :
    bipolarRate Q₁ S₁ ≤ liminf (fun n : ℕ ↦ -ENNReal.log (minTestSize
      (Measure.pi fun _ : Fin n ↦ Q₁) ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) β) /
        (n : EReal)) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun a ha ↦ ?_
  obtain ⟨r, har, hrd⟩ := EReal.lt_iff_exists_real_btwn.1 ha
  refine har.le.trans (le_liminf_of_le (by isBoundedDefault) ?_)
  filter_upwards [eventually_minTestSize_le Q₁ hS₁ hβ hrd, eventually_ge_atTop 1] with n hn hn1
  exact le_neg_log_div_of_le_ofReal_exp hn1 hn

/-- **The strong converse of the Stein lemma for composite nulls.** For `0 < β`, the smallest
size `α*_n(β)` of a test of `n` observations of the i.i.d. null `S₁` with power at least `β`
against `Q₁ ^ n` has `limsup -(1/n) log α*_n(β)` at most the bipolar rate [EVR26, Note 01]: no
power `β > 0`, however small, gives a better exponent. -/
theorem limsup_neg_log_minTestSize_div_le_bipolarRate (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hβ : 0 < β) :
    limsup (fun n : ℕ ↦ -ENNReal.log (minTestSize (Measure.pi fun _ : Fin n ↦ Q₁)
      ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) β) / (n : EReal)) atTop ≤
        bipolarRate Q₁ S₁ := by
  refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ ?_
  obtain ⟨r, hdr, hra⟩ := EReal.lt_iff_exists_real_btwn.1 ha
  refine (limsup_le_of_le (by isBoundedDefault) ?_).trans hra.le
  filter_upwards [eventually_le_minTestSize Q₁ hS₁ hβ hdr, eventually_ge_atTop 1] with n hn hn1
  exact neg_log_div_le_of_ofReal_exp_le hn1 hn

/-- **A Stein lemma for composite nulls, with strong converse.** For `β ∈ (0, 1)`, the smallest
size `α*_n(β)` of a test of `n` observations of the i.i.d. null `S₁` with power at least `β`
against `Q₁ ^ n` has `-(1/n) log α*_n(β)` tending to the bipolar rate, also when it is infinite
[EVR26, Note 01]. The exponent does not depend on `β`. -/
theorem tendsto_neg_log_minTestSize_div_bipolarRate (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n : ℕ ↦ -ENNReal.log (minTestSize (Measure.pi fun _ : Fin n ↦ Q₁)
      ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' S₁) β) / (n : EReal)) atTop
        (𝓝 (bipolarRate Q₁ S₁)) :=
  tendsto_of_le_liminf_of_limsup_le (bipolarRate_le_liminf_neg_log_minTestSize_div Q₁ hS₁ hβ1)
    (limsup_neg_log_minTestSize_div_le_bipolarRate Q₁ hS₁ hβ0)

/-- **The Chernoff–Stein lemma, with strong converse.** For a simple null `{P₁}` and
`β ∈ (0, 1)`, the smallest probability under `P₁ ^ n` of a measurable set of `n` observations with
probability at least `β` under `Q₁ ^ n`, `α*_n(β)`, has `-(1/n) log α*_n(β)` tending to
`klDiv Q₁ P₁`, the bipolar rate of a simple null. -/
theorem tendsto_neg_log_minTestSize_div_klDiv (Q₁ P₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure P₁] (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n : ℕ ↦ -ENNReal.log (minTestSize (Measure.pi fun _ : Fin n ↦ Q₁)
      {Measure.pi fun _ : Fin n ↦ P₁} β) / (n : EReal)) atTop (𝓝 (klDiv Q₁ P₁ : EReal)) := by
  have h := tendsto_neg_log_minTestSize_div_bipolarRate Q₁ (S₁ := {P₁})
    (fun P hP ↦ by rw [Set.mem_singleton_iff.1 hP]; infer_instance) hβ0 hβ1
  simpa only [Set.image_singleton, bipolarRate_singleton] using h

end ProbabilityTheory
