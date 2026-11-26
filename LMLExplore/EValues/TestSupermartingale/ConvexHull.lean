/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.LevelStoppingTime
public import LMLExplore.EValues.KLInf
public import LMLExplore.EValues.Null.Basic
public import LMLExplore.EValues.TestSupermartingale.SequentialNull
public import Mathlib.Probability.Process.HittingTime
import LMLExplore.EValues.EffectiveSet.Basic
import LMLExplore.EValues.EProcess.ProductNumeraire
import LMLExplore.EValues.TestSupermartingale.Betting
import LMLExplore.MeasureTheory.Integral.Lebesgue.Countable
import LMLExplore.MeasureTheory.Measure.Typeclasses.Probability
import LMLExplore.Probability.Independence.Wald
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Probability.Independence.InfinitePi

/-!
# Test supermartingales see the effective null, and their tests are slow

Let `S₁` be a set of probability measures on `𝓧`, each of which charges every point of `𝓧`, and
let `M` be a test supermartingale for the i.i.d. null `iidNull S₁`, in the filtration
`Filtration.piLT` of the past observations. Every past has positive probability under every
member of the null, so `M` satisfies the one-step condition
`∫⁻ y, M (n + 1) (update ω n y) ∂P ≤ M n ω` at every past `ω` and for every `P ∈ S₁`
(`ProbabilityTheory.IsENNSupermartingale.lintegral_update_le_of_infinitePi`). A bound on integrals
that holds on `S₁` holds on its effective null `effectiveSet S₁`, the measures under which every
e-variable for `S₁` has mean at most `1` (`ProbabilityTheory.lintegral_le_of_mem_effectiveSet`).
So `M` satisfies the one-step condition for the members of the effective null, and it is a test
supermartingale for the sequential null of the probability measures of the effective null: the
laws under which every observation, given the past, has a law in it. The effective null contains
the mixtures of members of `S₁` and is closed under limits: on a countable alphabet, it contains
the probability measures whose masses `Q₁ {x}` are pointwise limits of those of mixtures of
members of `S₁`, by Fatou's lemma for sums. In particular `M` is a test supermartingale for the
i.i.d. null of the convex hull of `S₁` and for the i.i.d. law of every such limit, and the test
that rejects when `M` reaches `α⁻¹` has level `α` there: it has no power inside the closed convex
hull of the null [EVR26, Note 32, Statement 1].

Without the hypothesis that every member charges every point, this fails: for the null of the two
point masses on `Bool`, some test martingale tends to `∞` almost surely under fair coins, a mixture
of them (`ProbabilityTheory.exists_isTestMartingale_dirac_tendsto_top`).

The expected number of observations of these tests is governed by the largest expected logarithm
`a₁ = maxEPower Q₁ S₁` of an e-variable of one observation, rather than by the bipolar rate. Every
level-`α` sequential test `τ` for the independent null `indepNull S₁` (the laws of independent
observations with laws in `S₁`) has `log (1/α) ≤ a₁ 𝔼[τ]` under the i.i.d. law of a probability
measure `Q₁`. The ratio of the e-process `α⁻¹ 𝟙{τ ≤ n}` to the product of the numeraires
`X* = numeraire Q₁ S₁` of the observations has mean at most `1` at every bounded stopping time
(`ProbabilityTheory.lintegral_div_prod_le_one`), so
`𝔼[𝟙{τ < ∞} α⁻¹ / ∏ j < τ, X* (ω j)] ≤ 1`. Pathwise,
`log (1/α) + ∑ j < τ, log⁻ X* (ω j) + 1 ≤ ∑ j < τ, log⁺ X* (ω j) + α⁻¹ / ∏ j < τ, X* (ω j)`,
which is `t + 1 ≤ exp t`, and Wald's identity in `ℝ≥0∞`
(`ProbabilityTheory.iIndepFun.lintegral_tsum_indicator_lt_eq_mul`) integrates the sums, whose
means are `𝔼[τ]` times those of `log⁺ X*` and `log⁻ X*`, of difference `a₁`. Since the test
supermartingales of a null whose members charge every point are test supermartingales for its
sequential null, which contains its independent null, their tests need at least
`log (1/α) / a₁` observations in expectation [EVR26, Note 32, Statement 1]. For a null that is not
convex, the bipolar rate `d` can be much larger than `a₁`, and the tests of other e-processes need
only `log (1/α) / d` observations to first order
(`ProbabilityTheory.exists_isLevelStoppingTime_limsup_lintegral_div_log_le`).

## Main statements

* `ProbabilityTheory.isTestSupermartingale_sequentialNull_effectiveSet_of_iidNull`: a test
  supermartingale for the i.i.d. null of laws that charge every point is a test supermartingale
  for the sequential null of the probability measures of its effective null.
* `ProbabilityTheory.isTestSupermartingale_iidNull_convexHull`,
  `ProbabilityTheory.isTestSupermartingale_infinitePi_of_tendsto` [EVR26, Note 32, Statement 1]:
  it is a test supermartingale for the i.i.d. null of the convex hull, and, on a countable
  alphabet, for the i.i.d. law of every pointwise limit of mixtures of members of the null.
* `ProbabilityTheory.measure_hittingAfter_lt_top_le_of_tendsto` [EVR26, Note 32, Statement 1]: its
  test of level `α` rejects with probability at most `α` under these laws.
* `ProbabilityTheory.toENNReal_log_inv_div_maxEPower_le_lintegral_of_indepNull`: a sequential test
  of level `α` for the independent null makes at least `log (1/α) / a₁` observations in
  expectation.
* `ProbabilityTheory.toENNReal_log_inv_div_maxEPower_le_lintegral_hittingAfter`
  [EVR26, Note 32, Statement 1]: so does the test of a test supermartingale for the i.i.d. null of
  laws that charge every point.

## Implementation notes

The statements and proofs are adapted from `EValuesResearch/Results/ConvexPieces.lean` (commit
`83205cb`) in the paper project `RemyDegenne/evalues_research`, rewritten on the API of
LMLExplore: the closure of the null is reached through its effective null, and the bound on
expected stopping times is stated for every sequential test of the independent null.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}
  {M : ℕ → (ℕ → 𝓧) → ℝ≥0∞}

/-! ### The tests of the independent null -/

/-- **A pathwise form of `t + 1 ≤ exp t`.** For nonzero `x j` and `c ≥ 0`,
`c + ∑ j, log⁻ (x j) + 1 ≤ ∑ j, log⁺ (x j) + exp c / ∏ j, x j`, with the positive and negative
parts of the logarithms kept apart so that the inequality lives in `ℝ≥0∞`. -/
private lemma ofReal_add_sum_add_one_le_sum_add_div_prod {s : Finset ℕ} {x : ℕ → ℝ≥0∞}
    (hx0 : ∀ j ∈ s, x j ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    ENNReal.ofReal c + ∑ j ∈ s, (-ENNReal.log (x j)).toENNReal + 1 ≤
      ∑ j ∈ s, (ENNReal.log (x j)).toENNReal + ENNReal.ofReal (Real.exp c) / ∏ j ∈ s, x j := by
  by_cases htop : ∃ j ∈ s, x j = ⊤
  · obtain ⟨j, hj, hjt⟩ := htop
    have hsum : ∑ j ∈ s, (ENNReal.log (x j)).toENNReal = ⊤ :=
      ENNReal.sum_eq_top.2 ⟨j, hj, by simp [hjt]⟩
    simp [hsum]
  simp only [not_exists, not_and] at htop
  set l : ℕ → ℝ := fun j ↦ Real.log (x j).toReal with hl
  have hlog : ∀ j ∈ s, ENNReal.log (x j) = (l j : EReal) := fun j hj ↦
    ENNReal.log_pos_real (hx0 j hj) (htop j hj)
  have hofmax (r : ℝ) : ENNReal.ofReal r = ENNReal.ofReal (max r 0) := by
    rcases le_total r 0 with h | h
    · simp [ENNReal.ofReal_of_nonpos h, max_eq_right h]
    · simp [max_eq_left h]
  have h1 : ∑ j ∈ s, (ENNReal.log (x j)).toENNReal =
      ENNReal.ofReal (∑ j ∈ s, max (l j) 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ ↦ le_max_right _ _]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [hlog j hj, EReal.real_coe_toENNReal, hofmax]
  have h2 : ∑ j ∈ s, (-ENNReal.log (x j)).toENNReal =
      ENNReal.ofReal (∑ j ∈ s, max (-l j) 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ ↦ le_max_right _ _]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [hlog j hj, ← EReal.coe_neg, EReal.real_coe_toENNReal, hofmax]
  have h3 : ∏ j ∈ s, x j = ENNReal.ofReal (Real.exp (∑ j ∈ s, l j)) := by
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun j _ ↦ (Real.exp_pos _).le]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [hl, Real.exp_log (ENNReal.toReal_pos (hx0 j hj) (htop j hj)),
      ENNReal.ofReal_toReal (htop j hj)]
  have hL : ∑ j ∈ s, l j = ∑ j ∈ s, max (l j) 0 - ∑ j ∈ s, max (-l j) 0 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ (max_zero_sub_max_neg_zero_eq_self _).symm
  have hA : 0 ≤ ∑ j ∈ s, max (l j) 0 := Finset.sum_nonneg fun j _ ↦ le_max_right _ _
  have hB : 0 ≤ ∑ j ∈ s, max (-l j) 0 := Finset.sum_nonneg fun j _ ↦ le_max_right _ _
  rw [h1, h2, h3, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_add hc hB,
    ← ENNReal.ofReal_add (by positivity) zero_le_one,
    ← ENNReal.ofReal_add hA (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have := Real.add_one_le_exp (c - ∑ j ∈ s, l j)
  rw [hL] at this ⊢
  linarith

/-- **Sequential tests of the independent null need `log (1/α) / a₁` observations.** Let `S₁` be
a set of probability measures and `Q₁` a probability measure on `𝓧`. Every sequential test `τ` of
level `α` for the independent null `indepNull S₁`, in the filtration `Filtration.piLT` of the past
observations, makes at least `log (1/α) / a₁` observations in expectation under the i.i.d. law of
`Q₁`, where `a₁ = maxEPower Q₁ S₁` is the largest expected logarithm under `Q₁` of an e-variable
for `S₁`. The left side is in `ℝ≥0∞`, with `log (1/α)` replaced by `0` for `α ≥ 1`; if `a₁ = 0`
and `α < 1`, the expected number of observations is infinite. -/
theorem toENNReal_log_inv_div_maxEPower_le_lintegral_of_indepNull (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    {τ : (ℕ → 𝓧) → WithTop ℕ} {α : ℝ≥0∞}
    (hτ : IsLevelStoppingTime τ Filtration.piLT (indepNull S₁) α) :
    (ENNReal.log α⁻¹).toENNReal / (maxEPower Q₁ S₁).toENNReal ≤
      ∫⁻ ω, ENat.toENNReal (τ ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by
  set Q := Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  set T := ∫⁻ ω, ENat.toENNReal (τ ω) ∂Q with hT_def
  -- the trivial cases
  rcases eq_or_ne T ⊤ with hT | hT
  · rw [hT]; exact le_top
  rcases le_or_gt 1 α with hα1 | hα1
  · have : (ENNReal.log α⁻¹).toENNReal = 0 :=
      EReal.toENNReal_eq_zero_iff.2 (ENNReal.log_le_zero_iff.2 (ENNReal.inv_le_one.2 hα1))
    rw [this, ENNReal.zero_div]; exact zero_le
  rcases eq_or_ne (maxEPower Q₁ S₁) ⊤ with ha | ha
  · rw [ha, EReal.toENNReal_top, ENNReal.div_top]; exact zero_le
  -- the null is nonempty; the numeraire `X` of `S₁` against `Q₁`
  have hS_ne : S₁.Nonempty := by
    rw [← Set.ne_empty_iff_nonempty]; rintro rfl; exact ha maxEPower_empty
  have hS₁le : ∀ P ∈ S₁, P univ ≤ 1 := fun P hP ↦ (hS₁ P hP).measure_univ.le
  set X := numeraire Q₁ S₁
  have hX : IsNumeraire X S₁ Q₁ := isNumeraire_numeraire Q₁ hS₁le
  have hXm : Measurable X := measurable_numeraire Q₁ S₁
  -- the positive and negative parts of the expected logarithm of the numeraire
  set mp := ∫⁻ x, (ENNReal.log (X x)).toENNReal ∂Q₁
  set mm := ∫⁻ x, (-ENNReal.log (X x)).toENNReal ∂Q₁
  have hmm_le : mm ≤ 1 := by
    refine (lintegral_mono fun x ↦ ?_).trans (hX.lintegral_div_le_one (isEVar_fun_one hS₁le))
    rw [← ENNReal.log_inv, one_div]
    refine (EReal.toENNReal_le_toENNReal (ENNReal.log_le_sub_one _)).trans ?_
    rw [← EReal.coe_ennreal_one, EReal.coe_ennreal_sub_toENNReal]
    exact tsub_le_self
  have hmm_top : mm ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hmm_le
  have ha_eq : maxEPower Q₁ S₁ = (mp : EReal) - mm := by
    rw [maxEPower_eq_eintegral_numeraire hS₁le]; rfl
  have hmp_top : mp ≠ ⊤ := by
    rintro h
    rw [ha_eq, h, ← EReal.coe_ennreal_toReal hmm_top] at ha
    exact ha (EReal.top_sub_coe _)
  have hXtop : ∀ᵐ x ∂Q₁, X x ≠ ⊤ := by
    filter_upwards [ae_lt_top' hXm.ennreal_log.ereal_toENNReal.aemeasurable hmp_top] with x hx h
    simp [h] at hx
  -- the key bound: `∫ 𝟙{τ < ∞} α⁻¹ / ∏ i < τ, X (ω i) ≤ 1`, from the e-process `α⁻¹ 𝟙{τ ≤ n}`
  have hE := hτ.isEProcess_inv_mul_indicator
  have hτs := hτ.isStoppingTime
  set f : ℕ → (ℕ → 𝓧) → ℝ≥0∞ := fun k ↦
    {ω | τ ω = k}.indicator fun ω ↦ α⁻¹ / ∏ i ∈ Finset.range k, X (ω i) with hf
  have hτk (k : ℕ) : MeasurableSet {ω | τ ω = k} :=
    Filtration.le _ k _ (by simpa using hτs.measurableSet_eq k)
  have hf_meas (k : ℕ) : Measurable (f k) :=
    (measurable_const.div (Finset.measurable_prod _ fun i _ ↦
      hXm.comp (measurable_pi_apply i))).indicator (hτk k)
  have hkey : ∫⁻ ω, ∑' k, f k ω ∂Q ≤ 1 := by
    rw [lintegral_tsum fun k ↦ (hf_meas k).aemeasurable, ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N ↦ ?_
    rw [← lintegral_finsetSum _ fun k _ ↦ hf_meas k]
    refine (lintegral_mono fun ω ↦ ?_).trans (lintegral_div_prod_le_one (S₁ := fun _ ↦ S₁)
      (Q₁ := fun _ ↦ Q₁) (X := fun _ ↦ X) (fun _ ↦ hS₁) (fun _ ↦ hS_ne) (fun _ ↦ hX)
      (fun _ hP ↦ infinitePi_mem_indepNull hP) hE (hτs.min_const N)
      fun ω ↦ ((min_le_right _ _).trans_lt (WithTop.coe_lt_top N)).ne)
    by_cases hk : ∃ k < N, τ ω = k
    · obtain ⟨k, hkN, hτk⟩ := hk
      rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.2 hkN) fun j _ hjk ↦ by
        simp [f, hτk, Ne.symm hjk]]
      have hkN' : min (k : WithTop ℕ) (WithTop.some N) = WithTop.some k := by
        rw [Nat.cast_withTop]; exact min_eq_left (WithTop.coe_le_coe.2 hkN.le)
      simp only [stoppedValue, f, Set.indicator_of_mem (show ω ∈ {ω | τ ω = k} from hτk), hτk]
      rw [hkN']
      simp [hτk]
    · push Not at hk
      rw [Finset.sum_eq_zero fun j hj ↦ by simp [f, hk j (Finset.mem_range.1 hj)]]
      exact zero_le
  -- almost surely, the test stops and the numeraires of the observations are positive and finite
  have hτm : Measurable fun ω ↦ ENat.toENNReal (τ ω) :=
    (measurable_of_countable _).comp hτs.measurable'
  have hτ_ae : ∀ᵐ ω ∂Q, τ ω ≠ ⊤ := by
    filter_upwards [ae_lt_top hτm hT] with ω hω h
    exact hω.ne (by rw [h]; exact ENat.toENNReal_top)
  have hX0 : ∀ᵐ ω ∂Q, ∀ i, X (ω i) ≠ 0 :=
    Measure.ae_forall_apply_infinitePi _ fun _ ↦ hX.ae_ne_zero hS₁le
  have hXt : ∀ᵐ ω ∂Q, ∀ i, X (ω i) ≠ ⊤ :=
    Measure.ae_forall_apply_infinitePi _ fun _ ↦ hXtop
  -- the level is positive: at level `0`, the key bound forbids the test to stop
  have hα0 : α ≠ 0 := by
    rintro rfl
    have htop : ∀ᵐ ω ∂Q, ∑' k, f k ω = ⊤ := by
      filter_upwards [hτ_ae, hXt] with ω hτω hXω
      obtain ⟨k, hk2⟩ := ENat.ne_top_iff_exists.mp hτω
      have hk : τ ω = (k : WithTop ℕ) := hk2.symm
      rw [tsum_eq_single k fun j hj ↦ by simp [f, hk, Ne.symm hj]]
      simp only [f, Set.indicator_of_mem (show ω ∈ {ω | τ ω = k} from hk), ENNReal.inv_zero]
      exact ENNReal.top_div_of_ne_top (ENNReal.prod_ne_top fun i _ ↦ hXω i)
    rw [lintegral_congr_ae htop, lintegral_const, measure_univ, mul_one] at hkey
    exact absurd hkey (by simp)
  -- the level `log (1/α)` as a real number
  set c := Real.log (α⁻¹).toReal with hc_def
  have hαinv0 : α⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (hα1.trans ENNReal.one_lt_top).ne
  have hαinvt : α⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hα0
  have hc0 : 0 ≤ c := Real.log_nonneg (by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hαinvt (ENNReal.one_le_inv.2 hα1.le))
  have hexp : ENNReal.ofReal (Real.exp c) = α⁻¹ := by
    rw [hc_def, Real.exp_log (ENNReal.toReal_pos hαinv0 hαinvt), ENNReal.ofReal_toReal hαinvt]
  have hlogc : (ENNReal.log α⁻¹).toENNReal = ENNReal.ofReal c := by
    rw [ENNReal.log_pos_real hαinv0 hαinvt, EReal.real_coe_toENNReal]
  -- Wald's identity for the coordinates
  have hind : iIndepFun (fun j (ω : ℕ → 𝓧) ↦ ω j) Q :=
    iIndepFun_infinitePi (P := fun _ ↦ Q₁) (X := fun _ ↦ id) fun _ ↦ measurable_id
  have hτ' : IsStoppingTime (Filtration.naturalLT (fun j (ω : ℕ → 𝓧) ↦ ω j)
      measurable_pi_apply) τ := by
    rw [← Filtration.piLT_eq_naturalLT]; exact hτs
  have hWald {g : 𝓧 → ℝ≥0∞} (hg : Measurable g) :
      ∫⁻ ω, ∑' j : ℕ, {ω | (j : ℕ∞) < τ ω}.indicator (fun ω ↦ g (ω j)) ω ∂Q =
        (∫⁻ x, g x ∂Q₁) * T :=
    hind.lintegral_tsum_indicator_lt_eq_mul measurable_pi_apply hτ' hg fun j ↦
      (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ Q₁) j).lintegral_comp hg
  set gp : 𝓧 → ℝ≥0∞ := fun x ↦ (ENNReal.log (X x)).toENNReal
  set gm : 𝓧 → ℝ≥0∞ := fun x ↦ (-ENNReal.log (X x)).toENNReal
  have hgp : Measurable gp := hXm.ennreal_log.ereal_toENNReal
  have hgm : Measurable gm := hXm.ennreal_log.neg.ereal_toENNReal
  have hsum_meas {g : 𝓧 → ℝ≥0∞} (hg : Measurable g) :
      Measurable fun ω ↦ ∑' j : ℕ, {ω | (j : ℕ∞) < τ ω}.indicator (fun ω ↦ g (ω j)) ω :=
    Measurable.tsum fun j ↦ (hg.comp (measurable_pi_apply j)).indicator
      (hτs.measurable' measurableSet_Ioi)
  -- the pathwise bound `log (1/α) + ∑ j < τ, log⁻ X + 1 ≤ ∑ j < τ, log⁺ X + α⁻¹ / ∏ j < τ, X`
  have hpt : ∀ᵐ ω ∂Q, ENNReal.ofReal c +
      ∑' j : ℕ, {ω | (j : ℕ∞) < τ ω}.indicator (fun ω ↦ gm (ω j)) ω + 1 ≤
      ∑' j : ℕ, {ω | (j : ℕ∞) < τ ω}.indicator (fun ω ↦ gp (ω j)) ω + ∑' k, f k ω := by
    filter_upwards [hτ_ae, hX0] with ω hτω hXω
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hτω
    have hsum (g : 𝓧 → ℝ≥0∞) :
        ∑' j : ℕ, {ω | (j : ℕ∞) < τ ω}.indicator (fun ω ↦ g (ω j)) ω =
          ∑ j ∈ Finset.range k, g (ω j) := by
      rw [tsum_eq_sum (s := Finset.range k) fun j hj ↦ ?_]
      · refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [Set.indicator_of_mem]
        simp [← hk, Finset.mem_range.1 hj]
      · rw [Set.indicator_of_notMem]
        simpa [← hk] using hj
    have hf_sum : ∑' j, f j ω = α⁻¹ / ∏ i ∈ Finset.range k, X (ω i) := by
      have hk1 : τ ω = (k : WithTop ℕ) := hk.symm
      rw [tsum_eq_single k fun j hj ↦ by simp [f, hk1, Ne.symm hj]]
      simp [f, hk1]
    rw [hsum, hsum, hf_sum, ← hexp]
    exact ofReal_add_sum_add_one_le_sum_add_div_prod (fun j _ ↦ hXω j) hc0
  -- integrate, with Wald's identity and the key bound
  have hint := lintegral_mono_ae hpt
  rw [lintegral_add_right _ measurable_const, lintegral_add_left measurable_const,
    lintegral_const, measure_univ, mul_one, hWald hgm, lintegral_const, measure_univ, mul_one,
    lintegral_add_left (hsum_meas hgp), hWald hgp] at hint
  have h1 : ENNReal.ofReal c + mm * T ≤ mp * T :=
    (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 (hint.trans (by gcongr))
  have h2 : ENNReal.ofReal c ≤ (mp - mm) * T := by
    rw [ENNReal.sub_mul fun _ _ ↦ hT]
    exact ENNReal.le_sub_of_add_le_left (ENNReal.mul_ne_top hmm_top hT) (by rwa [add_comm])
  rw [hlogc, ha_eq, EReal.coe_ennreal_sub_toENNReal]
  exact ENNReal.div_le_of_le_mul (by rwa [mul_comm])

/-! ### Test supermartingales of a null of laws that charge every point -/

variable [MeasurableSingletonClass 𝓧]

/-- The one-step condition of a test supermartingale of the i.i.d. null of laws that charge every
point, at every past, for every member of the effective null. -/
private lemma lintegral_update_le_of_mem_effectiveSet (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hpos : ∀ P ∈ S₁, ∀ x, P {x} ≠ 0) (hM : IsENNSupermartingale M Filtration.piLT (iidNull S₁))
    (n : ℕ) (ω : ℕ → 𝓧) {μ : Measure 𝓧} (hμ : μ ∈ effectiveSet S₁) :
    ∫⁻ y, M (n + 1) (Function.update ω n y) ∂μ ≤ M n ω := by
  refine lintegral_le_of_mem_effectiveSet hμ
    (((hM.adapted (n + 1)).mono (Filtration.le _ _) le_rfl).comp (measurable_update ω))
    fun P hP ↦ ?_
  have := hS₁ P hP
  exact (hM.anti_set (singleton_subset_iff.2
    (infinitePi_mem_iidNull hP))).lintegral_update_le_of_infinitePi fun i _ ↦ hpos P hP (ω i)

/-- **Test supermartingales see the effective null.** Let `S₁` be a set of probability measures
on `𝓧`, each of which charges every point. A test supermartingale for the i.i.d. null of `S₁`, in
the filtration `Filtration.piLT` of the past observations, is a test supermartingale for the
sequential null of the probability measures of the effective null of `S₁`: the laws under which
every observation, given the past, has a law under which every e-variable for `S₁` has mean at
most `1`. -/
theorem isTestSupermartingale_sequentialNull_effectiveSet_of_iidNull
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hpos : ∀ P ∈ S₁, ∀ x, P {x} ≠ 0)
    (hM : IsTestSupermartingale M Filtration.piLT (iidNull S₁)) :
    IsTestSupermartingale M Filtration.piLT (sequentialNull
      (fun _ _ ↦ effectiveSet S₁ ∩ {P | IsProbabilityMeasure P}) (fun k ω ↦ ω k)
      Filtration.piLT) := by
  refine ⟨isENNSupermartingale_sequentialNull_of_lintegral_update_le hM.adapted
    fun n ω ν hν ↦ lintegral_update_le_of_mem_effectiveSet hS₁ hpos hM.toIsENNSupermartingale n
      ω hν.1, fun P hP ↦ ?_⟩
  -- the initial value is a constant `c`, and `c ≤ 1` on the null, hence on its effective null
  have := isProbabilityMeasure_of_mem_sequentialNull hP
  obtain ⟨κ, -, hκS⟩ := exists_hasCondLaw_of_mem_sequentialNull hP 0
  obtain ⟨ω₀, hω₀, hω₀P⟩ := hκS.exists
  have : IsProbabilityMeasure (κ ω₀) := hω₀P
  have hconst : ∀ ω, M 0 ω = M 0 ω₀ := fun ω ↦ (hM.adapted 0).apply_eq_of_piLT_zero ω ω₀
  have h1 := lintegral_le_of_mem_effectiveSet hω₀ (measurable_const (a := M 0 ω₀))
    fun Q hQ ↦ by
      have := hS₁ Q hQ
      simpa [hconst] using hM.lintegral_zero_le _ (infinitePi_mem_iidNull hQ)
  simpa [hconst] using h1

/-- **Test supermartingales see the convex hull of the null** [EVR26, Note 32, Statement 1].
Let `S₁` be a set of probability measures on `𝓧`, each of which charges every point. A test
supermartingale for the i.i.d. null of `S₁`, in the filtration `Filtration.piLT` of the past
observations, is a test supermartingale for the i.i.d. null of the convex hull of `S₁`. -/
theorem isTestSupermartingale_iidNull_convexHull (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (hpos : ∀ P ∈ S₁, ∀ x, P {x} ≠ 0)
    (hM : IsTestSupermartingale M Filtration.piLT (iidNull S₁)) :
    IsTestSupermartingale M Filtration.piLT (iidNull (convexHull ℝ≥0∞ S₁)) :=
  (isTestSupermartingale_sequentialNull_effectiveSet_of_iidNull hS₁ hpos hM).anti_set
    ((iidNull_mono (subset_inter convexHull_subset_effectiveSet
      (convexHull_min (fun P hP ↦ hS₁ P hP) convex_setOfPred_isProbabilityMeasure))).trans
    (iidNull_subset_sequentialNull fun _ hP ↦ hP.2))

/-- **Test supermartingales see the closed convex hull of the null**
[EVR26, Note 32, Statement 1]. Let `S₁` be a set of probability measures on a countable alphabet
`𝓧`, each of which charges every point. A test supermartingale for the i.i.d. null of `S₁`, in the
filtration `Filtration.piLT` of the past observations, is a test supermartingale for the i.i.d.
law of every probability measure `Q₁` whose masses `Q₁ {x}` are the limits, along a filter, of
those of mixtures of members of `S₁`: for the closure of the convex hull of `S₁` in the topology of
pointwise convergence of the masses. -/
theorem isTestSupermartingale_infinitePi_of_tendsto [Countable 𝓧]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hpos : ∀ P ∈ S₁, ∀ x, P {x} ≠ 0)
    (hM : IsTestSupermartingale M Filtration.piLT (iidNull S₁))
    {ι : Type*} {l : Filter ι} [l.NeBot] {R : ι → Measure 𝓧}
    (hR : ∀ᶠ i in l, R i ∈ convexHull ℝ≥0∞ S₁) (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hQ₁ : ∀ x, Tendsto (fun i ↦ R i {x}) l (𝓝 (Q₁ {x}))) :
    IsTestSupermartingale M Filtration.piLT {Measure.infinitePi fun _ : ℕ ↦ Q₁} := by
  -- `Q₁` is in the effective null, by Fatou's lemma for sums
  have hQ : Q₁ ∈ effectiveSet S₁ := by
    refine mem_effectiveSet_of_measure_le_liminf (hR.mono fun i hi ↦
      convexHull_subset_effectiveSet hi) fun s hs ↦ ?_
    simpa [lintegral_indicator_one hs] using
      lintegral_le_liminf_of_tendsto_measure_singleton hQ₁ (s.indicator 1)
  exact (isTestSupermartingale_sequentialNull_effectiveSet_of_iidNull hS₁ hpos hM).anti_set
    (singleton_subset_iff.2 (infinitePi_mem_sequentialNull fun _ ↦ .of_forall fun _ ↦
      (show Q₁ ∈ effectiveSet S₁ ∩ {P | IsProbabilityMeasure P} from ⟨hQ, inferInstance⟩)))

/-- **The tests of the test supermartingales of a null have no power inside its closed convex
hull** [EVR26, Note 32, Statement 1]. Under the hypotheses of
`isTestSupermartingale_infinitePi_of_tendsto`, the test that rejects the first time `M` reaches
`α⁻¹` rejects with probability at most `α` under the i.i.d. law of every probability measure
`Q₁` whose masses are limits of those of mixtures of members of the null. -/
theorem measure_hittingAfter_lt_top_le_of_tendsto [Countable 𝓧]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hpos : ∀ P ∈ S₁, ∀ x, P {x} ≠ 0)
    (hM : IsTestSupermartingale M Filtration.piLT (iidNull S₁))
    {ι : Type*} {l : Filter ι} [l.NeBot] {R : ι → Measure 𝓧}
    (hR : ∀ᶠ i in l, R i ∈ convexHull ℝ≥0∞ S₁) (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hQ₁ : ∀ x, Tendsto (fun i ↦ R i {x}) l (𝓝 (Q₁ {x}))) (α : ℝ≥0∞) :
    Measure.infinitePi (fun _ : ℕ ↦ Q₁) {ω | hittingAfter M (Ici α⁻¹) 0 ω < ⊤} ≤ α :=
  ((isTestSupermartingale_infinitePi_of_tendsto hS₁ hpos hM hR Q₁ hQ₁).isEProcess
    (by rintro _ rfl; infer_instance)).isLevelStoppingTime_hittingAfter α |>.measure_lt_top_le _ rfl

/-- **The tests of the test supermartingales of a null make at least `log (1/α) / a₁`
observations** [EVR26, Note 32, Statement 1]. Let `S₁` be a set of probability measures on `𝓧`,
each of which charges every point, `M` a test supermartingale for the i.i.d. null of `S₁` in the
filtration `Filtration.piLT` of the past observations, and `Q₁` a probability measure. The test
that rejects the first time `M` reaches `α⁻¹` makes at least `log (1/α) / a₁` observations in
expectation under the i.i.d. law of `Q₁`, where `a₁ = maxEPower Q₁ S₁` is the largest expected
logarithm of an e-variable of one observation (`maxLogGrowth Q₁ S₁ 1`, by
`ProbabilityTheory.maxLogGrowth_one`). The left side is in `ℝ≥0∞`, with `log (1/α)` replaced by
`0` for `α ≥ 1`. -/
theorem toENNReal_log_inv_div_maxEPower_le_lintegral_hittingAfter
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hpos : ∀ P ∈ S₁, ∀ x, P {x} ≠ 0)
    (hM : IsTestSupermartingale M Filtration.piLT (iidNull S₁))
    (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁] (α : ℝ≥0∞) :
    (ENNReal.log α⁻¹).toENNReal / (maxEPower Q₁ S₁).toENNReal ≤
      ∫⁻ ω, ENat.toENNReal (hittingAfter M (Ici α⁻¹) 0 ω)
        ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by
  -- `M` is a test supermartingale for the independent null, hence an e-process
  have hM' : IsTestSupermartingale M Filtration.piLT (indepNull S₁) :=
    (isTestSupermartingale_sequentialNull_effectiveSet_of_iidNull hS₁ hpos hM).anti_set
      ((indepNull_mono (subset_inter subset_effectiveSet fun P hP ↦ hS₁ P hP)).trans
        (indepNull_subset_sequentialNull fun _ hP ↦ hP.2))
  exact toENNReal_log_inv_div_maxEPower_le_lintegral_of_indepNull Q₁ hS₁
    ((hM'.isEProcess fun P hP ↦ have := isProbabilityMeasure_of_mem_indepNull hS₁ P hP;
      inferInstance).isLevelStoppingTime_hittingAfter α)

end ProbabilityTheory
