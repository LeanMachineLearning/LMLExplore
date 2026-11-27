/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.ConstraintNull.Basic
public import LMLExplore.EValues.EProcess.Basic
public import LMLExplore.EValues.Null.Basic
public import LMLExplore.Probability.Process.Filtration
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Probability.ProductMeasure
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.EIntegral
import LMLExplore.Algebra.Order.Field.Basic
import LMLExplore.EValues.Betting.FollowTheLeader.Basic
import LMLExplore.EValues.BipolarRate.AlmostSure
import LMLExplore.EValues.ConstraintNull.KLInf
import LMLExplore.EValues.TestSupermartingale.SequentialNull
import LMLExplore.Probability.ProductMeasure

/-!
# Follow-the-leader betting with a cap, and its log-optimality

A bettor observes i.i.d. e-values `E 0, E 1, …` with law `Q` on `[0, ∞)` and bets at round `k` the
fraction `l k` of its wealth on `E k`, so that the wealth after `n` rounds is
`∏ k < n, (1 + l k * (E k - 1))`. The follow-the-leader bettor with cap `γ` bets at round `n + 1`
a fraction that maximizes over `[0, γ]` the wealth that a constant fraction would have produced on
`E 0, …, E n`. `LMLExplore.EValues.Betting.FollowTheLeader.Basic` treats the uncapped bettor
`γ = 1`. Write `ℓ γ = ⨆ c ∈ [0, γ], 𝔼_Q log (1 + c (E - 1))` for the best growth rate of a constant
fraction in `[0, γ]`, which may be `+∞`. The answers below to [WSJ26, Remark 2.3] are those of
[EVR26, Note 07].

* With a cap `γ < 1`, almost surely, `(1/n) log` of the wealth tends to `ℓ γ`, for all
  follow-the-leader fractions and whatever `Q`: a factor is at least `1 - γ > 0`, so an atom of `Q`
  at `0` does no harm, unlike in the uncapped case.
* For `γ ≤ 1`, no bettor whose fractions in `[0, γ]` depend on the past e-values only does better:
  almost surely, `limsup (1/n) log` of its wealth is at most `ℓ γ`.
* No e-process for the i.i.d. null of the laws on `[0, ∞)` of mean at most one, which is the
  constraint null `constraintNull {fun e ↦ e - 1}`, grows faster than `ℓ 1` [WSJ26,
  Proposition 2.2]. So when `Q {0} = 0` and `log (1 + E)` has a finite mean, the uncapped
  follow-the-leader bettor has `liminf (1/n) (log (W n) - log (W' n)) ≥ 0` almost surely, for every
  such e-process `W'`.

## Main statements

* `ProbabilityTheory.ae_tendsto_log_prod_followTheLeader_capped_div`: for `γ < 1`, `(1/n) log` of
  the wealth of follow-the-leader with cap `γ` tends to `ℓ γ` almost surely.
* `ProbabilityTheory.ae_limsup_log_prod_div_le_iSup_eintegral_log`: for `γ ≤ 1`, a bettor with
  predictable fractions in `[0, γ]` has `limsup (1/n) log` of its wealth at most `ℓ γ`.
* `ProbabilityTheory.IsEProcess.ae_limsup_log_div_le_iSup_eintegral_log`: an e-process for the
  i.i.d. null of the laws of mean at most one has `limsup (1/n) log` at most `ℓ 1`.
* `ProbabilityTheory.ae_liminf_log_prod_followTheLeader_sub_log_div_nonneg`: if `Q {0} = 0` and
  `log (1 + E)` is integrable, uncapped follow-the-leader does at least as well as every such
  e-process.

## Implementation notes

The cap reduces to the uncapped case through the affine map `e ↦ e' = 1 - γ + γ e`: for
`γ ∈ (0, 1]`, the bet `1 + c (e - 1)` with `c ∈ [0, γ]` is the bet `1 + (c / γ) (e' - 1)`, with
`c / γ ∈ [0, 1]`, and `e' ≥ 1 - γ` has no atom at `0` when `γ < 1`. The capped growth is then
`ProbabilityTheory.ae_tendsto_log_prod_followTheLeader_div` for the law of `e'`, and the bound for
predictable bettors with fractions in `[0, γ]` is the one for fractions in `[0, 1]` on the
e-values `e'`. For fractions in `[0, 1]`, the wealth is a test supermartingale for the i.i.d. null
(`ProbabilityTheory.isTestSupermartingale_prod_sequentialNull`), so that its growth is at most the
bipolar rate (`ProbabilityTheory.IsEProcess.ae_limsup_log_div_le_bipolarRate`), at most the
smallest relative entropy to the null, which is at most `ℓ 1` by the dual formula
`ProbabilityTheory.klInf_constraintNull_eq_iSup_eintegral_log`: a bet `1 + π (e - 1)` on the
constraint has `π ≤ 1`, since the point mass at `0` belongs to the null. When `log (1 + E)` has an
infinite mean, `ℓ 1 = ∞` and there is nothing to prove.

The statements and proofs are adapted from `EValuesResearch/Results/FollowTheLeaderCapped.lean`
(commit `83205cb`) in the paper project `RemyDegenne/evalues_research`, which formalizes
[EVR26, Note 07], rewritten on the API of LMLExplore.

## References

* [WSJ26] I. Waudby-Smith, R. Sandoval and M. I. Jordan, *Instance-log-optimality of
  portfolio-based e-processes and their sequential hypothesis tests*, arXiv:2504.02818v2.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

/-! ### The laws of mean at most one and the best rate of a constant fraction -/

/-- The bet `1 + c (e - 1)` with `c ∈ [0, 1]` is an e-variable for the laws on `ℝ≥0` of mean at
most one. -/
private lemma isEVar_ofReal_one_add_mul_sub_one {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    IsEVar (fun e : ℝ≥0 ↦ ENNReal.ofReal (1 + c * ((e : ℝ) - 1)))
      (constraintNull {fun e : ℝ≥0 ↦ (e : ℝ) - 1}) := by
  have h := isEVar_ofReal_one_add_of_mem_constraintBets
    (g := fun _ : Unit ↦ fun e : ℝ≥0 ↦ (e : ℝ) - 1) (fun _ ↦ by fun_prop)
    (toNNReal_mem_constraintBets (Y := univ) (fun _ _ ↦ by simp) (fun _ ↦ hc.1)
      fun e _ ↦ by
        simp only [Finset.univ_unique, Finset.sum_singleton]
        nlinarith [mul_nonneg hc.1 e.coe_nonneg, hc.2])
  simpa [Real.coe_toNNReal _ hc.1] using h

/-- The smallest relative entropy from `Q` to the laws of mean at most one is at most the best
growth rate of a constant fraction in `[0, 1]`, by the dual formula
`klInf_constraintNull_eq_iSup_eintegral_log`: a bet `1 + π (e - 1)` on the constraint has
`π ≤ 1`, since the point mass at `0` belongs to the null. -/
private lemma klInf_le_iSup_eintegral_log (Q : Measure ℝ≥0) [IsProbabilityMeasure Q]
    (hlog : Integrable (fun e : ℝ≥0 ↦ Real.log (1 + e)) Q) :
    klInf Q (constraintNull {fun e : ℝ≥0 ↦ (e : ℝ) - 1}) ≤
      ⨆ c ∈ Icc (0 : ℝ) 1, ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * ((e : ℝ) - 1))) ∂Q := by
  have hg : ({fun e : ℝ≥0 ↦ (e : ℝ) - 1} : Set (ℝ≥0 → ℝ)) =
      range fun _ : Unit ↦ fun e : ℝ≥0 ↦ (e : ℝ) - 1 := range_const.symm
  have hpos : Integrable (fun e : ℝ≥0 ↦ Real.posLog ((e : ℝ) - 1)) Q := by
    refine hlog.mono' (by fun_prop) (ae_of_all _ fun e ↦ ?_)
    rw [Real.norm_of_nonneg Real.posLog_nonneg]
    exact (Real.posLog_le_posLog (by linarith [e.coe_nonneg]) (by linarith)).trans
      (Real.posLog_le_log_one_add e.coe_nonneg)
  rw [hg, klInf_constraintNull_eq_iSup_eintegral_log (fun _ ↦ by fun_prop) Q fun _ ↦ hpos]
  refine iSup₂_le fun π hπ ↦ ?_
  -- the point mass at `0` belongs to the null, so that `π () ≤ 1`
  have hδ : Measure.dirac (0 : ℝ≥0) ∈
      constraintNull (range fun _ : Unit ↦ fun e : ℝ≥0 ↦ (e : ℝ) - 1) :=
    (dirac_mem_constraintNull_iff (by rintro _ ⟨_, rfl⟩; fun_prop)).2
      (by rintro _ ⟨_, rfl⟩; simp)
  have h0 := mem_constraintBets_iff.1 hπ _ hδ
  rw [ae_dirac_eq, eventually_pure] at h0
  have hπ1 : (π () : ℝ) ≤ 1 := by simpa using h0
  refine le_iSup₂_of_le (π () : ℝ) ⟨(π ()).coe_nonneg, hπ1⟩ (le_of_eq ?_)
  simp

/-- When `log (1 + E)` has an infinite mean, the best growth rate of a constant fraction in
`[0, 1]` is infinite, already for the fraction `1 / 2`
(`eintegral_log_ofReal_one_half_eq_top`). -/
private lemma iSup_eintegral_log_eq_top (Q : Measure ℝ≥0) [IsProbabilityMeasure Q]
    (hlog : ¬ Integrable (fun e : ℝ≥0 ↦ Real.log (1 + e)) Q) :
    ⨆ c ∈ Icc (0 : ℝ) 1, ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * ((e : ℝ) - 1))) ∂Q = ⊤ :=
  eq_top_iff.2 (le_iSup₂_of_le (1 / 2 : ℝ) ⟨by norm_num, by norm_num⟩
    (eintegral_log_ofReal_one_half_eq_top hlog).ge)

/-- **No e-process for the laws of mean at most one grows faster than the best constant
fraction**, the case of one e-value of [WSJ26, Proposition 2.2]. Let `Q` be a probability measure
on `ℝ≥0` and `W` an e-process, in the filtration `Filtration.piLT` of the observations, for the
i.i.d. null of the laws on `ℝ≥0` of mean at most one (`constraintNull {fun e ↦ e - 1}`). Almost
surely under `Q^ℕ`, `(1/n) log (W n)` has `limsup` at most the best growth rate
`⨆ c ∈ [0, 1], 𝔼_Q log (1 + c * (E - 1))` of a constant fraction. Nothing is assumed on `Q`: when
`log (1 + E)` has an infinite mean, that rate is `+∞`. -/
theorem IsEProcess.ae_limsup_log_div_le_iSup_eintegral_log (Q : Measure ℝ≥0)
    [IsProbabilityMeasure Q] {W : ℕ → (ℕ → ℝ≥0) → ℝ≥0∞}
    (hW : IsEProcess W (Filtration.piLT (X := fun _ : ℕ ↦ ℝ≥0))
      (iidNull (constraintNull {fun e : ℝ≥0 ↦ (e : ℝ) - 1}))) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q),
      limsup (fun n : ℕ ↦ ENNReal.log (W n ω) / (n : EReal)) atTop ≤
        ⨆ c ∈ Icc (0 : ℝ) 1, ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * ((e : ℝ) - 1))) ∂Q := by
  by_cases hlog : Integrable (fun e : ℝ≥0 ↦ Real.log (1 + e)) Q
  · have hS (P : Measure ℝ≥0) (hP : P ∈ constraintNull {fun e : ℝ≥0 ↦ (e : ℝ) - 1}) :
        IsProbabilityMeasure P :=
      isProbabilityMeasure_of_mem_constraintNull hP
    filter_upwards [hW.ae_limsup_log_div_le_bipolarRate Q hS] with ω hω
    exact hω.trans ((bipolarRate_le_klInf Q hS).trans (klInf_le_iSup_eintegral_log Q hlog))
  · rw [iSup_eintegral_log_eq_top Q hlog]
    exact ae_of_all _ fun _ ↦ le_top

/-- For predictable fractions in `[0, 1]`, the logarithm of the wealth grows at most at the best
rate of a constant fraction in `[0, 1]`: the wealth is a test supermartingale for the i.i.d. null
of the laws of mean at most one. -/
private lemma ae_limsup_log_prod_div_le_iSup_eintegral_log_one (Q : Measure ℝ≥0)
    [IsProbabilityMeasure Q] {l : ℕ → (ℕ → ℝ≥0) → ℝ}
    (hl : Adapted (Filtration.piLT (X := fun _ : ℕ ↦ ℝ≥0)) l)
    (hl1 : ∀ n ω, l n ω ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q),
      limsup (fun n : ℕ ↦
          ENNReal.log (∏ k ∈ Finset.range n, ENNReal.ofReal (1 + l k ω * ((ω k : ℝ) - 1))) / n)
        atTop ≤ ⨆ c ∈ Icc (0 : ℝ) 1,
          ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * ((e : ℝ) - 1))) ∂Q := by
  set S := constraintNull {fun e : ℝ≥0 ↦ (e : ℝ) - 1}
  have hS (P : Measure ℝ≥0) (hP : P ∈ S) : IsProbabilityMeasure P :=
    isProbabilityMeasure_of_mem_constraintNull hP
  have hM := isTestSupermartingale_prod_sequentialNull (S₁ := fun _ _ ↦ S)
    (r := fun k (ω : ℕ → ℝ≥0) (e : ℝ≥0) ↦ ENNReal.ofReal (1 + l k ω * ((e : ℝ) - 1)))
    (fun k ↦ Filtration.measurable_piLT_apply (Nat.lt_succ_self k))
    (fun k ↦ (((hl k).comp measurable_fst).mul ((measurable_coe_nnreal_real.comp
      measurable_snd).sub_const 1)).const_add 1 |>.ennreal_ofReal)
    fun k ω ↦ isEVar_ofReal_one_add_mul_sub_one (hl1 k ω)
  have hW := (hM.isEProcess fun P hP ↦
    have := isProbabilityMeasure_of_mem_sequentialNull hP; inferInstance).anti_set
      (iidNull_subset_sequentialNull hS)
  exact hW.ae_limsup_log_div_le_iSup_eintegral_log Q

/-! ### A capped bet on an e-value is an uncapped bet on an affine image -/

/-- The affine map `e ↦ 1 - γ + γ e` on `[0, ∞)`. For `γ ∈ (0, 1]`, the bet `1 + c (e - 1)` with
`c ∈ [0, γ]` is the bet `1 + (c / γ) (e' - 1)` on `e' = 1 - γ + γ e`, with `c / γ ∈ [0, 1]`. -/
private noncomputable def capMap (γ : ℝ) (e : ℝ≥0) : ℝ≥0 := Real.toNNReal (1 - γ + γ * e)

/-- For `γ ∈ [0, 1]`, the affine image `1 - γ + γ e` is nonnegative, so that `capMap` is the
affine map itself. -/
private lemma coe_capMap {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1) (e : ℝ≥0) :
    (capMap γ e : ℝ) = 1 - γ + γ * e :=
  Real.coe_toNNReal _ (by nlinarith [mul_nonneg hγ.1 e.coe_nonneg, hγ.2])

/-- The affine map `capMap γ` is measurable. -/
@[fun_prop]
private lemma measurable_capMap (γ : ℝ) : Measurable (capMap γ) := by
  unfold capMap
  fun_prop

/-- A bet on the affine image is a bet on the e-value, with the fraction multiplied by `γ`. -/
private lemma one_add_mul_capMap {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1) (c : ℝ) (e : ℝ≥0) :
    1 + c * ((capMap γ e : ℝ) - 1) = 1 + c * γ * ((e : ℝ) - 1) := by
  rw [coe_capMap hγ]
  ring

/-- A bet on the affine image with the fraction divided by `γ` is the bet on the e-value. -/
private lemma one_add_div_mul_capMap {γ : ℝ} (hγ : γ ∈ Ioc (0 : ℝ) 1) (c : ℝ) (e : ℝ≥0) :
    1 + c / γ * ((capMap γ e : ℝ) - 1) = 1 + c * ((e : ℝ) - 1) := by
  rw [one_add_mul_capMap ⟨hγ.1.le, hγ.2⟩, div_mul_cancel₀ c hγ.1.ne']

/-- The best rate of a constant fraction in `[0, 1]` on the affine image is the best rate of a
constant fraction in `[0, γ]` on the e-value. -/
private lemma iSup_eintegral_map_capMap {γ : ℝ} (hγ : γ ∈ Ioc (0 : ℝ) 1) (Q : Measure ℝ≥0) :
    ⨆ c ∈ Icc (0 : ℝ) 1, ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * ((e : ℝ) - 1)))
        ∂Q.map (capMap γ) =
      ⨆ c ∈ Icc (0 : ℝ) γ, ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * ((e : ℝ) - 1))) ∂Q := by
  have hmap (c : ℝ) : ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * ((e : ℝ) - 1)))
      ∂Q.map (capMap γ) =
        ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * γ * ((e : ℝ) - 1))) ∂Q := by
    rw [eintegral_map (by fun_prop) (measurable_capMap γ)]
    exact eintegral_congr fun e ↦ by rw [one_add_mul_capMap ⟨hγ.1.le, hγ.2⟩]
  simp_rw [hmap]
  refine le_antisymm (iSup₂_le fun c hc ↦ ?_) (iSup₂_le fun c hc ↦ ?_)
  · exact le_iSup₂_of_le (c * γ) (mul_mem_Icc_zero hγ.1.le hc) le_rfl
  · refine le_iSup₂_of_le (c / γ) (unitInterval.div_mem hc.1 hγ.1.le hc.2) (le_of_eq ?_)
    rw [div_mul_cancel₀ c hγ.1.ne']

/-! ### Main results -/

/-- **Follow-the-leader betting with a cap grows at the best capped constant rate**
[EVR26, Note 07]. Let `Q` be a probability measure on `ℝ≥0` and `γ < 1`. Almost surely under
`Q^ℕ`, for all fractions `l n ∈ [0, γ]` such that `l (n + 1)` maximizes over `[0, γ]` the wealth
`∏ k ≤ n, (1 + c * (ω k - 1))` of a constant fraction `c`, the logarithm of the wealth
`∏ k < n, (1 + l k * (ω k - 1))` divided by `n` tends to the best growth rate
`⨆ c ∈ [0, γ], 𝔼_Q log (1 + c * (E - 1))` of a constant fraction in `[0, γ]`, which may be `+∞`.
Nothing is assumed on `Q`, which may charge `0`: a factor is at least `1 - γ > 0`. -/
theorem ae_tendsto_log_prod_followTheLeader_capped_div (Q : Measure ℝ≥0) [IsProbabilityMeasure Q]
    {γ : ℝ} (hγ : γ < 1) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q), ∀ l : ℕ → ℝ, (∀ n, l n ∈ Icc (0 : ℝ) γ) →
      (∀ n, IsMaxOn (fun c : ℝ ↦
        ∏ k ∈ Finset.range (n + 1), ENNReal.ofReal (1 + c * ((ω k : ℝ) - 1))) (Icc 0 γ)
          (l (n + 1))) →
      Tendsto (fun n : ℕ ↦
          ENNReal.log (∏ k ∈ Finset.range n, ENNReal.ofReal (1 + l k * ((ω k : ℝ) - 1))) / n)
        atTop (𝓝 (⨆ c ∈ Icc (0 : ℝ) γ,
          ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * ((e : ℝ) - 1))) ∂Q)) := by
  rcases lt_trichotomy γ 0 with hγ0 | rfl | hγ0
  · -- no fraction lies in the empty interval
    exact ae_of_all _ fun ω l hl ↦ absurd ((hl 0).1.trans (hl 0).2) (not_le.2 hγ0)
  · -- the fractions are `0`, and the wealth is `1`
    refine ae_of_all _ fun ω l hl _ ↦ ?_
    have hl0 (n : ℕ) : l n = 0 := le_antisymm (hl n).2 (hl n).1
    simp [hl0]
  -- the capped bettor is the uncapped bettor on the affine images, which do not vanish
  have hγ' : γ ∈ Icc (0 : ℝ) 1 := ⟨hγ0.le, hγ.le⟩
  have hQ0 : Q.map (capMap γ) {0} = 0 := by
    rw [Measure.map_apply (measurable_capMap γ) (measurableSet_singleton 0)]
    convert measure_empty (μ := Q)
    refine eq_empty_of_forall_notMem fun e he ↦ ?_
    have h := coe_capMap hγ' e
    rw [Set.mem_preimage, Set.mem_singleton_iff] at he
    rw [he, NNReal.coe_zero] at h
    nlinarith [mul_nonneg hγ0.le e.coe_nonneg]
  filter_upwards [Measure.ae_of_ae_infinitePi_map (fun _ : ℕ ↦ Q) (fun _ ↦ measurable_capMap γ)
    (ae_tendsto_log_prod_followTheLeader_div _ hQ0)] with ω hω l hl hmax
  have hmax' (n : ℕ) : IsMaxOn (fun c : ℝ ↦ ∏ k ∈ Finset.range (n + 1),
      ENNReal.ofReal (1 + c * ((capMap γ (ω k) : ℝ) - 1))) (Icc 0 1) (l (n + 1) / γ) := by
    refine isMaxOn_iff.2 fun c hc ↦ ?_
    have h := isMaxOn_iff.1 (hmax n) (c * γ) (mul_mem_Icc_zero hγ0.le hc)
    simpa only [one_add_mul_capMap hγ', div_mul_cancel₀ _ hγ0.ne'] using h
  have hlim := hω (fun n ↦ l n / γ) (fun n ↦ unitInterval.div_mem (hl n).1 hγ0.le (hl n).2) hmax'
  simp_rw [one_add_div_mul_capMap ⟨hγ0, hγ.le⟩] at hlim
  rwa [iSup_eintegral_map_capMap ⟨hγ0, hγ.le⟩] at hlim

/-- **No predictable bettor with fractions in `[0, γ]` grows faster than the best constant
fraction in `[0, γ]`** [EVR26, Note 07]. Let `Q` be a probability measure on `ℝ≥0`, `γ ≤ 1`, and
`l n` fractions in `[0, γ]` that depend only on the first `n` e-values (adapted to
`Filtration.piLT`). Almost surely under `Q^ℕ`, the logarithm of the wealth
`∏ k < n, (1 + l k * (ω k - 1))` divided by `n` has `limsup` at most the best growth rate
`⨆ c ∈ [0, γ], 𝔼_Q log (1 + c * (E - 1))` of a constant fraction in `[0, γ]`. With
`ae_tendsto_log_prod_followTheLeader_capped_div` for `γ < 1`, and with
`ae_tendsto_log_prod_followTheLeader_div` for `γ = 1` and `Q {0} = 0`, follow-the-leader is almost
surely log-optimal among these bettors. Nothing is assumed on `Q`. -/
theorem ae_limsup_log_prod_div_le_iSup_eintegral_log (Q : Measure ℝ≥0) [IsProbabilityMeasure Q]
    {γ : ℝ} (hγ : γ ≤ 1) {l : ℕ → (ℕ → ℝ≥0) → ℝ}
    (hl : Adapted (Filtration.piLT (X := fun _ : ℕ ↦ ℝ≥0)) l)
    (hlγ : ∀ n ω, l n ω ∈ Icc (0 : ℝ) γ) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q),
      limsup (fun n : ℕ ↦
          ENNReal.log (∏ k ∈ Finset.range n, ENNReal.ofReal (1 + l k ω * ((ω k : ℝ) - 1))) / n)
        atTop ≤ ⨆ c ∈ Icc (0 : ℝ) γ,
          ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * ((e : ℝ) - 1))) ∂Q := by
  rcases lt_trichotomy γ 0 with hγ0 | rfl | hγ0
  · -- no fraction lies in the empty interval
    exact absurd ((hlγ 0 fun _ ↦ 0).1.trans (hlγ 0 fun _ ↦ 0).2) (not_le.2 hγ0)
  · -- the fractions are `0`, and the wealth is `1`
    have hl0 (n : ℕ) (ω : ℕ → ℝ≥0) : l n ω = 0 := le_antisymm (hlγ n ω).2 (hlγ n ω).1
    exact ae_of_all _ fun ω ↦ by norm_num [hl0]
  -- on the affine images, the bettor bets the fractions `l / γ ∈ [0, 1]`
  have hγ' : γ ∈ Icc (0 : ℝ) 1 := ⟨hγ0.le, hγ⟩
  obtain ⟨uncap, humeas, huncap⟩ :
      ∃ u : ℝ≥0 → ℝ≥0, Measurable u ∧ ∀ e, u (capMap γ e) = e := by
    refine ⟨fun e' ↦ Real.toNNReal (((e' : ℝ) - (1 - γ)) / γ), by fun_prop, fun e ↦ ?_⟩
    ext
    dsimp only
    rw [coe_capMap hγ', show 1 - γ + γ * (e : ℝ) - (1 - γ) = γ * e by ring,
      mul_div_cancel_left₀ _ hγ0.ne', Real.coe_toNNReal _ e.coe_nonneg]
  set l' : ℕ → (ℕ → ℝ≥0) → ℝ := fun n ω' ↦ l n (fun j ↦ uncap (ω' j)) / γ
  have hl' : Adapted (Filtration.piLT (X := fun _ : ℕ ↦ ℝ≥0)) l' := fun n ↦ by
    refine Filtration.measurable_piLT_of_dependsOn ?_ fun ω ω' h ↦ ?_
    · exact (((hl n).mono (Filtration.le _ n) le_rfl).comp
        (Measurable.of_eval fun j ↦ humeas.comp (measurable_pi_apply j))).div_const γ
    · simp only [l']
      congr 1
      exact (hl n).dependsOn_of_piLT fun j hj ↦ by simp [h j hj]
  filter_upwards [Measure.ae_of_ae_infinitePi_map (fun _ : ℕ ↦ Q) (fun _ ↦ measurable_capMap γ)
    (ae_limsup_log_prod_div_le_iSup_eintegral_log_one _ hl' fun n ω' ↦
      unitInterval.div_mem (hlγ _ _).1 hγ0.le (hlγ _ _).2)] with ω hω
  have hfac (k : ℕ) : 1 + l' k (fun j ↦ capMap γ (ω j)) * ((capMap γ (ω k) : ℝ) - 1) =
      1 + l k ω * ((ω k : ℝ) - 1) := by
    simp only [l', huncap]
    exact one_add_div_mul_capMap ⟨hγ0, hγ⟩ _ _
  simp_rw [hfac, iSup_eintegral_map_capMap ⟨hγ0, hγ⟩] at hω
  exact hω

/-- **Without a cap and without an atom at `0`, no e-process grows faster than
follow-the-leader** [EVR26, Note 07], which answers [WSJ26, Remark 2.3]. Let `Q` be a probability
measure on `ℝ≥0` with `Q {0} = 0` and `log (1 + E)` integrable, and `W` an e-process, in the
filtration `Filtration.piLT` of the observations, for the i.i.d. null of the laws on `ℝ≥0` of mean
at most one (`constraintNull {fun e ↦ e - 1}`). Almost surely under `Q^ℕ`, for all fractions
`l n ∈ [0, 1]` such that `l (n + 1)` maximizes over `[0, 1]` the wealth
`∏ k ≤ n, (1 + c * (ω k - 1))` of a constant fraction `c`, the difference between the logarithms
of the wealth `∏ k < n, (1 + l k * (ω k - 1))` and of `W n`, divided by `n`, has a nonnegative
`liminf`. -/
theorem ae_liminf_log_prod_followTheLeader_sub_log_div_nonneg (Q : Measure ℝ≥0)
    [IsProbabilityMeasure Q] (hQ0 : Q {0} = 0)
    (hlog : Integrable (fun e : ℝ≥0 ↦ Real.log (1 + e)) Q) {W : ℕ → (ℕ → ℝ≥0) → ℝ≥0∞}
    (hW : IsEProcess W (Filtration.piLT (X := fun _ : ℕ ↦ ℝ≥0))
      (iidNull (constraintNull {fun e : ℝ≥0 ↦ (e : ℝ) - 1}))) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q), ∀ l : ℕ → ℝ, (∀ n, l n ∈ Icc (0 : ℝ) 1) →
      (∀ n, IsMaxOn (fun c : ℝ ↦
        ∏ k ∈ Finset.range (n + 1), ENNReal.ofReal (1 + c * ((ω k : ℝ) - 1))) (Icc 0 1)
          (l (n + 1))) →
      0 ≤ liminf (fun n : ℕ ↦
          (ENNReal.log (∏ k ∈ Finset.range n, ENNReal.ofReal (1 + l k * ((ω k : ℝ) - 1))) -
            ENNReal.log (W n ω)) / n) atTop := by
  set ℓ := ⨆ c ∈ Icc (0 : ℝ) 1, ∫ᵉ e, ENNReal.log (ENNReal.ofReal (1 + c * ((e : ℝ) - 1))) ∂Q
  -- the best rate is finite: it is nonnegative, and at most the mean of `log (1 + E)`
  have hℓ0 : 0 ≤ ℓ := le_iSup₂_of_le (0 : ℝ) ⟨le_rfl, zero_le_one⟩ (by simp)
  have hℓtop : ℓ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (EReal.coe_ne_top (∫ e, Real.log (1 + e) ∂Q))
      (iSup₂_le fun c hc ↦ ?_)
    rw [← eintegral_eq_integral hlog]
    exact eintegral_mono fun e ↦ log_ofReal_one_add_mul_le hc e
  filter_upwards [ae_tendsto_log_prod_followTheLeader_div Q hQ0,
    hW.ae_limsup_log_div_le_iSup_eintegral_log Q] with ω hFTL hω l hl hmax
  -- the difference is the follow-the-leader rate minus the rate of `W`
  set a : ℕ → EReal := fun n ↦
    ENNReal.log (∏ k ∈ Finset.range n, ENNReal.ofReal (1 + l k * ((ω k : ℝ) - 1))) / n
  set b : ℕ → EReal := fun n ↦ ENNReal.log (W n ω) / n
  have hab : (fun n : ℕ ↦
      (ENNReal.log (∏ k ∈ Finset.range n, ENNReal.ofReal (1 + l k * ((ω k : ℝ) - 1))) -
        ENNReal.log (W n ω)) / n) = a + -b := by
    funext n
    simp only [a, b, Pi.add_apply, Pi.neg_apply, div_eq_mul_inv, ← sub_eq_add_neg]
    exact EReal.sub_mul_of_nonneg_of_ne_top (EReal.inv_nonneg_of_nonneg (by positivity))
      (EReal.inv_lt_top _).ne
  rw [hab]
  refine le_trans ?_ EReal.le_liminf_add
  rw [(hFTL l hl hmax).liminf_eq, EReal.liminf_neg,
    ← EReal.sub_self hℓtop (ne_bot_of_le_ne_bot EReal.zero_ne_bot hℓ0), sub_eq_add_neg]
  gcongr
  exact EReal.neg_le_neg_iff.2 hω

end ProbabilityTheory
