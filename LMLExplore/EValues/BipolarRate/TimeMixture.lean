/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.AlmostSure
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
import LMLExplore.Analysis.SpecialFunctions.Log.Basic
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.Analysis.SpecificLimits.Basic
import LMLExplore.Data.EReal.Inv
import LMLExplore.EValues.BipolarRate.MixtureNumeraire
import LMLExplore.EValues.EProcess.Closure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# One e-process from a prior: the time mixture of the mixture numeraires

Let `S₁` be a set of measures on `𝓧` (the null). The observations are the coordinates of
`ℕ → 𝓧`, with the filtration `Filtration.piLT`, so that time `n` has seen `n` observations. A
sequence `G n` of e-variables for the `n`-sample nulls `sampleNull S₁ n` need not be an e-process:
the numeraires of the `n`-sample nulls are not one in general
(`ProbabilityTheory.not_isEProcess_numeraires_bernoulli`). The time mixture of [RW, Section 7.9]
turns such a sequence into one:
`M n = ∑ j ∈ [1, n], G j (X_1, …, X_j) / (j (j + 1))`. It is the time mixture of
`ProbabilityTheory.isEProcess_sum_mul`, with the weights `coverWeight j = 1 / (j (j + 1))`, which
add up to `1`. So `M` is nondecreasing, its supremum over time is an e-variable for the i.i.d.
null, and `M` is an e-process valid at every random time, possibly infinite and not a stopping
time. No hypothesis on `S₁` is needed.

The weights cost little growth: `log (M n) ≥ log (G n) - log (n (n + 1))`, and
`log (n (n + 1)) = o(n)`, so `liminf (1/n) log (M n) ≥ liminf (1/n) log (G n)`. Since `M` is an
e-process, `limsup (1/n) log (M n)` is at most the bipolar rate `bipolarRate Q₁ S₁` almost surely
under the i.i.d. law of every `Q₁`
(`ProbabilityTheory.IsEProcess.ae_limsup_log_div_le_bipolarRate`).
Hence `M` attains the bipolar rate wherever `G` does. With `G n` the numeraires of the `n`-sample
nulls under the mixtures `∫ Q' ^ n ν(dQ')` of a prior `ν` on the alternatives, which attain the
rate at every `Q₁` in the Kullback–Leibler support of `ν` [EVR26, Note 14]
(`ProbabilityTheory.ae_tendsto_log_numeraire_bind_div_bipolarRate`), `M` is one e-process that
attains the rate at every such `Q₁`, on any measurable space. For a countable class `{Q j}` and the
prior `∑ j, 2^{-(j+1)} δ_{Q j}`, every `Q j` is in the support: one e-process attains the rate on
the class, with no countable generation of `𝓧` and no dominating measure, which
`ProbabilityTheory.exists_isEProcess_ae_tendsto_log_div_bipolarRate` assumes for its classes.

## Main definitions

* `ProbabilityTheory.timeMixture G`: the time mixture of a sequence `G n` of functions of `n`
  observations.

## Main statements

* `ProbabilityTheory.timeMixture_eq_sum_Icc`, `ProbabilityTheory.monotone_timeMixture`: the time
  mixture is `∑ j ∈ [1, n], G j / (j (j + 1))`, and is nondecreasing.
* `ProbabilityTheory.iSup_timeMixture`: the supremum over time of the time mixture is the full
  series `∑' j, coverWeight j * G j`.
* `ProbabilityTheory.isEVar_iSup_timeMixture`, `ProbabilityTheory.isEProcess_timeMixture`,
  `ProbabilityTheory.isEVar_stoppedValueLimsup_timeMixture`: the time mixture of e-variables of
  the `n`-sample nulls is an e-process for the i.i.d. null, its supremum is an e-variable, and so is
  its value at every measurable random time.
* `ProbabilityTheory.liminf_log_div_le_liminf_log_timeMixture_div`: the time mixture grows at least
  as fast as its bets.
* `ProbabilityTheory.ae_tendsto_log_timeMixture_div_bipolarRate`: the time mixture of e-variables
  that grow at least at the bipolar rate grows at the bipolar rate.
* `ProbabilityTheory.ae_tendsto_log_timeMixture_numeraire_bind_div_bipolarRate`: the time mixture
  of the numeraires against a prior attains the rate on its Kullback–Leibler support.
* `ProbabilityTheory.ae_tendsto_log_timeMixture_numeraire_sum_dirac_div_bipolarRate`: for a
  countable class of alternatives.

## Implementation notes

`timeMixture G n ω` is defined as `∑ j ∈ Finset.Iic n, ENNReal.ofReal (coverWeight j) * G j ω'`,
with `ω'` the first `j` observations, the form of `ProbabilityTheory.isEProcess_sum_mul`; the term
`j = 0` vanishes, since `coverWeight 0 = 0`. The statements and proofs are adapted from
`EValuesResearch/Results/TimeMixture.lean` (commit `83205cb`) in the paper project
`RemyDegenne/evalues_research`, rewritten on the API of LMLExplore.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, Section 7.9.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory Filter InformationTheory
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}
  {G : (n : ℕ) → (Fin n → 𝓧) → ℝ≥0∞}

/-! ### The time mixture -/

variable (G) in
/-- The **time mixture** of a sequence `G j` of functions of `j` observations [RW, Section 7.9]:
at time `n`, the sum over `j ≤ n` of `G j` at the first `j` observations, with the weight
`coverWeight j = 1 / (j (j + 1))`, which is `0` for `j = 0`. It is the process of
`ProbabilityTheory.isEProcess_sum_mul`; `ProbabilityTheory.timeMixture_eq_sum_Icc` writes it as
`∑ j ∈ [1, n], G j / (j (j + 1))`. -/
noncomputable def timeMixture (n : ℕ) (ω : ℕ → 𝓧) : ℝ≥0∞ :=
  ∑ j ∈ Finset.Iic n, ENNReal.ofReal (coverWeight j) * G j (initSeg j ω)

variable (G) in
/-- The definition of the time mixture. -/
lemma timeMixture_def (n : ℕ) (ω : ℕ → 𝓧) :
    timeMixture G n ω = ∑ j ∈ Finset.Iic n, ENNReal.ofReal (coverWeight j) * G j (initSeg j ω) :=
  (rfl)

variable (G) in
/-- The time mixture at time `n` is `∑ j ∈ [1, n], G j / (j (j + 1))`, with `G j` at the first `j`
observations. -/
theorem timeMixture_eq_sum_Icc (n : ℕ) (ω : ℕ → 𝓧) :
    timeMixture G n ω = ∑ j ∈ Finset.Icc 1 n, G j (initSeg j ω) / ((j : ℝ≥0∞) * (j + 1)) := by
  rw [timeMixture_def]
  refine (Finset.sum_subset (fun j hj ↦ Finset.mem_Iic.2 (Finset.mem_Icc.1 hj).2)
    fun j hj hj' ↦ ?_).symm.trans (Finset.sum_congr rfl fun j hj ↦ ?_)
  · have : j = 0 := by
      by_contra h
      exact hj' (Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 h, Finset.mem_Iic.1 hj⟩)
    simp [this]
  · rw [ofReal_coverWeight (Nat.one_le_iff_ne_zero.1 (Finset.mem_Icc.1 hj).1), div_eq_mul_inv,
      mul_comm]

variable (G) in
/-- The time mixture is nondecreasing in time. -/
theorem monotone_timeMixture : Monotone (timeMixture G) := fun _ _ hmn _ ↦
  Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.2 hmn)

variable (G) in
/-- At every time `n`, the time mixture is at least the bet `G n` at the first `n` observations,
with its weight `coverWeight n`. -/
theorem ofReal_coverWeight_mul_le_timeMixture (n : ℕ) (ω : ℕ → 𝓧) :
    ENNReal.ofReal (coverWeight n) * G n (initSeg n ω) ≤ timeMixture G n ω :=
  Finset.single_le_sum (f := fun j ↦ ENNReal.ofReal (coverWeight j) * G j (initSeg j ω))
    (fun _ _ ↦ zero_le) (Finset.mem_Iic.2 le_rfl)

/-- The time mixture of measurable functions is adapted to the filtration `Filtration.piLT` of the
observations: at time `n`, it is a function of the first `n` observations. -/
theorem adapted_timeMixture (hG : ∀ n, Measurable (G n)) :
    Adapted (Filtration.piLT (X := fun _ : ℕ ↦ 𝓧)) (timeMixture G) := fun _ ↦
  Finset.measurable_sum _ fun j hj ↦
    ((hG j).comp (Filtration.measurable_piLT_initSeg (Finset.mem_Iic.1 hj))).const_mul _

/-! ### Validity -/

variable (G) in
/-- The supremum over time of the time mixture is the full series
`∑' j, coverWeight j * G j (X_1, …, X_j)`. -/
theorem iSup_timeMixture (ω : ℕ → 𝓧) :
    ⨆ n, timeMixture G n ω = ∑' j, ENNReal.ofReal (coverWeight j) * G j (initSeg j ω) :=
  (tsum_eq_iSup_sum' Finset.Iic fun t ↦
    ⟨t.sup id, fun _ hx ↦ Finset.mem_Iic.2 (Finset.le_sup (f := id) hx)⟩).symm

/-- **The supremum of the time mixture of e-variables is an e-variable.** If each `G n` is an
e-variable for the `n`-sample null of `S₁`, the supremum over time of the time mixture is an
e-variable for the i.i.d. null: its mean under every member is at most
`∑ j ≥ 1, 1 / (j (j + 1)) = 1`. No hypothesis on `S₁` is needed. -/
theorem isEVar_iSup_timeMixture (hG : ∀ n, IsEVar (G n) (sampleNull S₁ n)) :
    IsEVar (fun ω ↦ ⨆ n, timeMixture G n ω) (iidNull S₁) := by
  simp_rw [iSup_timeMixture]
  exact isEVar_tsum_mul (fun j ↦ (hG j).comp_initSeg) tsum_ofReal_coverWeight_le_one

/-- **The time mixture of e-variables is an e-process** [RW, Section 7.9]. If each `G n` is an
e-variable for the `n`-sample null of `S₁`, the time mixture is an e-process for the i.i.d. null,
in the filtration `Filtration.piLT` of the observations, for any `S₁`. It is the time mixture of
`ProbabilityTheory.isEProcess_sum_mul`, with the weights `coverWeight j`. -/
theorem isEProcess_timeMixture (hG : ∀ n, IsEVar (G n) (sampleNull S₁ n)) :
    IsEProcess (timeMixture G) (Filtration.piLT (X := fun _ : ℕ ↦ 𝓧)) (iidNull S₁) :=
  isEProcess_sum_mul (fun j ↦ (hG j).measurable.comp (Filtration.measurable_piLT_initSeg le_rfl))
    (fun j ↦ (hG j).comp_initSeg) tsum_ofReal_coverWeight_le_one

/-- **The time mixture is valid at every random time.** If each `G n` is an e-variable for the
`n`-sample null of `S₁`, then for every measurable random time `τ` with values in `WithTop ℕ`, not
necessarily a stopping time, the value `stoppedValueLimsup (timeMixture G) τ` of the time mixture
at `τ`, its limit where `τ` is infinite, is an e-variable for the i.i.d. null. -/
theorem isEVar_stoppedValueLimsup_timeMixture (hG : ∀ n, IsEVar (G n) (sampleNull S₁ n))
    {τ : (ℕ → 𝓧) → WithTop ℕ} (hτ : Measurable τ) :
    IsEVar (stoppedValueLimsup (timeMixture G) τ) (iidNull S₁) :=
  (isEVar_iSup_timeMixture hG).mono
    (measurable_stoppedValueLimsup (isEProcess_timeMixture hG).measurable hτ)
    fun _ ↦ stoppedValueLimsup_le_iSup

/-! ### Growth -/

variable (G) in
/-- At every time `n ≠ 0`, the logarithm of `G n` at the first `n` observations exceeds that of
the time mixture by at most `log (n (n + 1))`. -/
theorem log_le_log_timeMixture_add {n : ℕ} (hn : n ≠ 0) (ω : ℕ → 𝓧) :
    ENNReal.log (G n (initSeg n ω)) ≤
      ENNReal.log (timeMixture G n ω) + ((Real.log ((n : ℝ) * (n + 1)) : ℝ) : EReal) := by
  have hpos : (0 : ℝ) < n * (n + 1) := by
    have : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    positivity
  have h1 : (n : ℝ≥0∞) * (n + 1) * ENNReal.ofReal (coverWeight n) = 1 := by
    rw [ofReal_coverWeight hn]
    exact ENNReal.mul_inv_cancel (by simp [hn]) (by finiteness)
  refine ENNReal.log_le_log_add_of_div_le ?_
  have hcast : ENNReal.ofReal ((n : ℝ) * (n + 1)) = (n : ℝ≥0∞) * (n + 1) := by norm_cast
  rw [Real.exp_log hpos, hcast]
  refine ENNReal.div_le_of_le_mul ?_
  calc G n (initSeg n ω)
  _ = (n : ℝ≥0∞) * (n + 1) * (ENNReal.ofReal (coverWeight n) * G n (initSeg n ω)) := by
    rw [← mul_assoc, h1, one_mul]
  _ ≤ (n : ℝ≥0∞) * (n + 1) * timeMixture G n ω := by
    gcongr
    exact ofReal_coverWeight_mul_le_timeMixture G n ω

variable (G) in
/-- **The time mixture grows at least as fast as its bets.** For every sequence `ω` of
observations, `liminf (1/n) log` of the time mixture is at least that of `G n` at the first `n`
observations: the weights `1 / (n (n + 1))` cost `log (n (n + 1)) = o(n)`. -/
theorem liminf_log_div_le_liminf_log_timeMixture_div (ω : ℕ → 𝓧) :
    liminf (fun n : ℕ ↦ ENNReal.log (G n (initSeg n ω)) / (n : EReal)) atTop ≤
      liminf (fun n : ℕ ↦ ENNReal.log (timeMixture G n ω) / (n : EReal)) atTop := by
  -- `n (n + 1) = O(n ^ 2)`, so `log (n (n + 1)) ≤ n δ` eventually, for every `δ > 0`
  have hO : (fun n : ℕ ↦ (n : ℝ) * (n + 1)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (2 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.rpow_two, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    nlinarith
  refine le_of_forall_lt_imp_le_of_dense fun a ha ↦ ?_
  obtain ⟨c, hac, hc⟩ := EReal.lt_iff_exists_real_btwn.1 ha
  obtain ⟨b, hab, hbc⟩ := EReal.lt_iff_exists_real_btwn.1 hac
  rw [EReal.coe_lt_coe_iff] at hbc
  refine hab.le.trans (le_liminf_of_le (by isBoundedDefault) ?_)
  filter_upwards [eventually_lt_of_lt_liminf hc (by isBoundedDefault),
    Real.eventually_log_le_mul_of_isBigO hO (sub_pos.2 hbc), eventually_gt_atTop 0]
    with n hn hlog hn0
  rw [EReal.coe_lt_div_natCast_iff hn0] at hn
  rw [EReal.coe_le_div_natCast_iff hn0]
  -- `n c < log (G n) ≤ log (M n) + log (n (n + 1)) ≤ log (M n) + (c - b) n`
  have h := (hn.trans_le (log_le_log_timeMixture_add G hn0.ne' ω)).trans_le
    (add_le_add le_rfl (EReal.coe_le_coe_iff.2 hlog))
  generalize ENNReal.log (timeMixture G n ω) = y at h ⊢
  induction y using EReal.rec with
  | bot => simp at h
  | top => exact le_top
  | coe y =>
    rw [← EReal.coe_add, EReal.coe_lt_coe_iff] at h
    exact EReal.coe_le_coe_iff.2 (by nlinarith)

/-- **The time mixture keeps the bipolar rate of its bets.** Let `G n` be e-variables for the
`n`-sample nulls of a set `S₁` of probability measures such that, almost surely under the i.i.d.
law of `Q₁`, `liminf (1/n) log (G n)` at the first `n` observations is at least the bipolar rate
`bipolarRate Q₁ S₁`. Then almost surely `(1/n) log (M n)` of the time mixture tends to the bipolar
rate, also when it is infinite: the lower bound holds since the time mixture grows at least as
fast as its bets, and the upper bound since it is an e-process
(`ProbabilityTheory.IsEProcess.ae_limsup_log_div_le_bipolarRate`). -/
theorem ae_tendsto_log_timeMixture_div_bipolarRate (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hG : ∀ n, IsEVar (G n) (sampleNull S₁ n))
    (hG_rate : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), bipolarRate Q₁ S₁ ≤
      liminf (fun n : ℕ ↦ ENNReal.log (G n (initSeg n ω)) / (n : EReal)) atTop) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      Tendsto (fun n : ℕ ↦ ENNReal.log (timeMixture G n ω) / (n : EReal)) atTop
        (𝓝 (bipolarRate Q₁ S₁)) := by
  filter_upwards [(isEProcess_timeMixture hG).ae_limsup_log_div_le_bipolarRate Q₁ hS₁, hG_rate]
    with ω hsup hinf
  exact tendsto_of_le_liminf_of_limsup_le
    (hinf.trans (liminf_log_div_le_liminf_log_timeMixture_div G ω)) hsup

/-! ### One e-process from a prior -/

/-- **The time mixture of the numeraires against a prior attains the bipolar rate on its
Kullback–Leibler support.** Let `ν` be a finite measure on the measures on `𝓧` that charges only
probability measures and every Kullback–Leibler neighbourhood `{Q' | klDiv Q₁ Q' ≤ ε}`, `ε > 0`,
of `Q₁`, and `M` the time mixture of the numeraires of the `n`-sample nulls under the mixtures
`∫ Q' ^ n ν(dQ')`. Almost surely under the i.i.d. law of `Q₁`, `(1/n) log (M n)` tends to
`bipolarRate Q₁ S₁`, also when it is infinite. `M` is an e-process for the i.i.d. null
(`ProbabilityTheory.isEProcess_timeMixture`), while the numeraires need not be one; it does not
depend on `Q₁`. The numeraires attain the rate by [EVR26, Note 14]
(`ProbabilityTheory.ae_tendsto_log_numeraire_bind_div_bipolarRate`). No assumption is made on
`𝓧`. -/
theorem ae_tendsto_log_timeMixture_numeraire_bind_div_bipolarRate (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    (ν : Measure (Measure 𝓧)) [IsFiniteMeasure ν] (hν : ∀ᵐ Q' ∂ν, IsProbabilityMeasure Q')
    (hν_supp : ∀ ε : ℝ≥0∞, 0 < ε → ν {Q' | klDiv Q₁ Q' ≤ ε} ≠ 0) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      Tendsto (fun n : ℕ ↦ ENNReal.log (timeMixture
          (fun n ↦ numeraire (ν.bind fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q') (sampleNull S₁ n))
          n ω) / (n : EReal)) atTop (𝓝 (bipolarRate Q₁ S₁)) := by
  refine ae_tendsto_log_timeMixture_div_bipolarRate Q₁ hS₁ (fun n ↦ isEVar_numeraire _
    (measure_univ_le_one_of_mem_sampleNull (fun P hP ↦ (hS₁ P hP).measure_univ.le) n)) ?_
  filter_upwards [ae_tendsto_log_numeraire_bind_div_bipolarRate Q₁ hS₁ ν hν hν_supp] with ω hω
  exact hω.liminf_eq.ge

/-- **One e-process at the bipolar rate for a countable class of alternatives, on any measurable
space.** Let `Q j` be probability measures on `𝓧` and `ν = ∑ j, 2^{-(j+1)} δ_{Q j}`. The time
mixture `M` of the numeraires of the `n`-sample nulls under the mixtures `∫ Q' ^ n ν(dQ')` is an
e-process for the i.i.d. null (`ProbabilityTheory.isEProcess_timeMixture`) such that, for every
`j`, almost surely under the i.i.d. law of `Q j`, `(1/n) log (M n)` tends to
`bipolarRate (Q j) S₁`. No countable generation of `𝓧` and no dominating measure are needed, unlike
in `ProbabilityTheory.exists_isEProcess_ae_tendsto_log_div_bipolarRate`. -/
theorem ae_tendsto_log_timeMixture_numeraire_sum_dirac_div_bipolarRate
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (Q : ℕ → Measure 𝓧)
    [∀ j, IsProbabilityMeasure (Q j)] (j : ℕ) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q j),
      Tendsto (fun n : ℕ ↦ ENNReal.log (timeMixture
          (fun n ↦ numeraire
            ((Measure.sum fun i : ℕ ↦ (2⁻¹ : ℝ≥0∞) ^ (i + 1) • Measure.dirac (Q i)).bind
              fun Q' ↦ Measure.pi fun _ : Fin n ↦ Q') (sampleNull S₁ n))
          n ω) / (n : EReal)) atTop (𝓝 (bipolarRate (Q j) S₁)) := by
  set ν : Measure (Measure 𝓧) := Measure.sum fun i : ℕ ↦ (2⁻¹ : ℝ≥0∞) ^ (i + 1) • .dirac (Q i)
  -- the prior has mass one
  have : IsProbabilityMeasure ν := ⟨by
    simp [ν, Measure.sum_apply _ MeasurableSet.univ, ENNReal.tsum_geometric_two_add_one]⟩
  -- it charges only probability measures
  have hν : ∀ᵐ Q' ∂ν, IsProbabilityMeasure Q' := by
    rw [Measure.ae_sum_eq, eventually_iSup]
    exact fun i ↦ Measure.ae_smul_measure ((ae_dirac_iff
      ProbabilityMeasure.measurableSet_isProbabilityMeasure).2 inferInstance) _
  -- it charges every set that contains `Q j`, as an outer measure
  have hsupp (ε : ℝ≥0∞) (_ : 0 < ε) : ν {Q' | klDiv (Q j) Q' ≤ ε} ≠ 0 := by
    refine (lt_of_lt_of_le
      (ENNReal.pow_pos (ENNReal.inv_pos.2 (ENNReal.ofNat_ne_top (n := 2))) (j + 1)) ?_).ne'
    calc (2⁻¹ : ℝ≥0∞) ^ (j + 1)
    _ = ((2⁻¹ : ℝ≥0∞) ^ (j + 1) • Measure.dirac (Q j)) {Q' | klDiv (Q j) Q' ≤ ε} := by
      rw [smul_apply, Measure.dirac_apply_of_mem (by simp), smul_eq_mul, mul_one]
    _ ≤ ν {Q' | klDiv (Q j) Q' ≤ ε} :=
      Measure.le_sum (fun i : ℕ ↦ (2⁻¹ : ℝ≥0∞) ^ (i + 1) • Measure.dirac (Q i)) j _
  exact ae_tendsto_log_timeMixture_numeraire_bind_div_bipolarRate (Q j) hS₁ ν hν hsupp

end ProbabilityTheory
