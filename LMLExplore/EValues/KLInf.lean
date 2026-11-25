/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Null.Basic
public import Statlib.EValues.Product
public import Statlib.EValues.RIPr
import LMLExplore.EValues.DPI
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Statlib.ForMathlib.InformationTheory.KullbackLeibler.EIntegral
import TauCeti.Data.EReal.Operations

/-!
# The smallest relative entropy to a null and the largest e-power

For a measure `Q` and a null `S : Set (Measure Ω)`, this file defines the two sides of Statlib's
duality between e-variables and relative entropies:

* `klInf Q S := ⨅ P ∈ S, klIntegral Q P`, the smallest relative entropy from `Q` to the null;
* `maxEPower Q S := maxUtility Q S logUtility`, the largest expected logarithm under `Q` of an
  e-variable for `S`.

Both are `EReal`-valued. The divergence is Statlib's `klIntegral Q P = ∫ log (dQ/dP) dQ`, not
Mathlib's `klDiv`. The two agree for measures of equal mass. On measures of different masses,
`klDiv Q P = klIntegral Q P + P univ - Q univ`, and only `klIntegral` is the divergence that the
duality produces. An effective null has sub-probability members, so the duality needs it there.
For `S = {c • Q}` with `0 < c < 1`, the largest e-power is `-log c`, while `klDiv Q (c • Q)` is
`-log c + c - 1`, which is smaller (`coe_klDiv_smul_right_self_lt_maxEPower`). So the weak duality
`maxEPower Q S ≤ klInf Q S` fails when `klDiv` replaces `klIntegral`.

Both definitions are prototyped in `notes/book/Suggested.lean` of the paper project
`RemyDegenne/evalues_research` (commit `88fb487`), where `klInf` is `ℝ≥0∞`-valued and uses `klDiv`.

## Main definitions

* `ProbabilityTheory.klInf Q S`: the smallest relative entropy `klIntegral Q P` over `P ∈ S`.
* `ProbabilityTheory.maxEPower Q S`: the largest expected logarithm of an e-variable for `S`
  under `Q`.

## Main statements

* `ProbabilityTheory.coe_klDiv_eq_klIntegral_add_sub`: for finite measures,
  `klDiv μ ν = klIntegral μ ν + ν univ - μ univ`, with no absolute continuity or integrability
  hypothesis (both sides are then `⊤`).
* `ProbabilityTheory.klIntegral_nonneg`, `ProbabilityTheory.klInf_nonneg` and
  `ProbabilityTheory.maxEPower_nonneg`: nonnegativity when the members of the null have mass at
  most that of `Q` (at most one, for `maxEPower`).
* `ProbabilityTheory.klIntegral_map_le`: data processing for `klIntegral` along a measurable map.
* `ProbabilityTheory.klInf_eq_iInf_klDiv`: for a null whose members have the mass of `Q`, `klInf`
  is the smallest `klDiv`.
* `ProbabilityTheory.maxEPower_effectiveSet`: a null and its effective null have the same largest
  e-power.
* `ProbabilityTheory.maxEPower_eq_klInf_effectiveSet`: Statlib's duality,
  `maxEPower Q S = klInf Q (effectiveSet S)`, and `ProbabilityTheory.maxEPower_le_klInf`.
* `ProbabilityTheory.maxEPower_singleton`: the simple null, `maxEPower Q {P} = klIntegral Q P` for
  `P` of mass at most one, and `ProbabilityTheory.maxEPower_singleton_eq_klDiv`, its value
  `klDiv Q P` for a probability measure `P`.
* `ProbabilityTheory.maxEPower_singleton_le_add_eintegral_log_inv`: if `ν.withDensity c ≤ m` for
  a measurable `c ≤ 1`, positive under `Q`, and the expected value of `log c⁻¹` under `Q` is
  finite, then the largest e-power of `{m}` exceeds that of `{ν}` by at most that expected value.
* `ProbabilityTheory.maxEPower_eq_eintegral_numeraire`: the numeraire attains the largest e-power.
* `ProbabilityTheory.maxEPower_prod_eq_add`: additivity of `maxEPower` on products of nulls.
* `ProbabilityTheory.maxEPower_map_le`, `MeasurableEmbedding.maxEPower_map_eq` and
  `MeasurableEquiv.maxEPower_map_eq`: data processing for `maxEPower` along a measurable map, with
  equality along a measurable embedding or a measurable equivalence.
* `ProbabilityTheory.coe_klDiv_smul_right_self_lt_maxEPower`: `klDiv` cannot replace `klIntegral` in
  the duality.

## References

* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, §6.
-/

public section

open MeasureTheory InformationTheory Set

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ ν P Q : Measure Ω} {S T : Set (Measure Ω)}

/-! ### The divergence `klIntegral` -/

section KLIntegral

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- For finite measures with `μ ≪ ν`, `klIntegral μ ν` is the extended integral of the
log-likelihood ratio, also when that ratio is not integrable (both sides are then `⊤`). The proof
follows that of Statlib's `coe_klDiv_eq_eintegral_llr`. -/
theorem klIntegral_eq_eintegral_llr (h_ac : μ ≪ ν) :
    klIntegral μ ν = ∫ᵉ x, llr μ ν x ∂μ := by
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [klIntegral_of_ac_of_integrable h_ac h_int, eintegral_eq_integral h_int]
  rw [klIntegral_of_not_integrable h_int, eq_comm]
  by_contra h_ne_top
  -- the negative part of `llr μ ν` has finite integral, hence its positive part does not
  refine h_int ?_
  simpa using (integrable_toReal_iff_eintegral_ne_bot_and_ne_top
    (f := fun x ↦ (llr μ ν x : EReal)) (by fun_prop) (ae_of_all _ fun _ ↦ EReal.coe_ne_bot _)
    (ae_of_all _ fun _ ↦ EReal.coe_ne_top _)).mpr ⟨eintegral_llr_ne_bot h_ac, h_ne_top⟩

/-- `klIntegral` is Mathlib's `klDiv` corrected by the masses:
`klDiv μ ν = klIntegral μ ν + ν univ - μ univ`. No absolute continuity or integrability is needed:
when one fails, both sides are `⊤`. -/
theorem coe_klDiv_eq_klIntegral_add_sub :
    (klDiv μ ν : EReal) = klIntegral μ ν + ν.real univ - μ.real univ := by
  by_cases h_ac : μ ≪ ν
  · rw [coe_klDiv_eq_eintegral_llr h_ac, klIntegral_eq_eintegral_llr h_ac]
  rw [klDiv_of_not_ac h_ac, klIntegral_of_not_ac h_ac, EReal.coe_ennreal_top, EReal.top_add_coe,
    EReal.top_sub_coe]

/-- `klIntegral` is Mathlib's `klDiv` corrected by the masses:
`klIntegral μ ν = klDiv μ ν + μ univ - ν univ`. -/
theorem klIntegral_eq_klDiv_add_sub :
    klIntegral μ ν = klDiv μ ν + μ.real univ - ν.real univ := by
  by_cases h : μ ≪ ν ∧ Integrable (llr μ ν) μ
  · rw [klIntegral_of_ac_of_integrable h.1 h.2, klDiv_of_ac_of_integrable h.1 h.2,
      EReal.coe_ennreal_ofReal, max_eq_left (integral_llr_add_sub_measure_univ_nonneg h.1 h.2)]
    norm_cast
    ring
  have h_top : klIntegral μ ν = ⊤ := by
    by_cases h_ac : μ ≪ ν
    · exact klIntegral_of_not_integrable fun h_int ↦ h ⟨h_ac, h_int⟩
    · exact klIntegral_of_not_ac h_ac
  rw [h_top, klDiv_eq_top_iff.2 fun h₁ h₂ ↦ h ⟨h₁, h₂⟩, EReal.coe_ennreal_top, EReal.top_add_coe,
    EReal.top_sub_coe]

/-- `klIntegral μ ν` is at least the difference of the masses `μ univ - ν univ`, by the
nonnegativity of `klDiv`. -/
theorem measureReal_univ_sub_le_klIntegral :
    ((μ.real univ - ν.real univ : ℝ) : EReal) ≤ klIntegral μ ν := by
  rw [klIntegral_eq_klDiv_add_sub, EReal.coe_sub]
  exact EReal.sub_le_sub (le_add_of_nonneg_left (EReal.coe_ennreal_nonneg _)) le_rfl

/-- `klIntegral μ ν` is nonnegative when `ν` has mass at most that of `μ`, in particular for a
probability measure `μ` and a measure `ν` of mass at most one. -/
theorem klIntegral_nonneg (h : ν univ ≤ μ univ) : 0 ≤ klIntegral μ ν := by
  refine le_trans ?_ measureReal_univ_sub_le_klIntegral
  rw [EReal.coe_nonneg, sub_nonneg]
  exact ENNReal.toReal_mono (measure_ne_top μ univ) h

/-- **Data processing** for `klIntegral` along a measurable map. -/
theorem klIntegral_map_le {g : Ω → Ω'} (hg : Measurable g) :
    klIntegral (μ.map g) (ν.map g) ≤ klIntegral μ ν := by
  have hreal (ρ : Measure Ω) : (ρ.map g).real univ = ρ.real univ := by
    simp [map_measureReal_apply hg .univ]
  rw [klIntegral_eq_klDiv_add_sub, klIntegral_eq_klDiv_add_sub, hreal, hreal]
  exact EReal.sub_le_sub (add_le_add_left (EReal.coe_ennreal_le_coe_ennreal_iff.2
    (klDiv_map_le μ ν hg)) _) le_rfl

end KLIntegral

/-! ### The smallest relative entropy to a null -/

/-- The smallest relative entropy from `Q` to the null `S`, `⨅ P ∈ S, klIntegral Q P`, written
$\mathrm{KL}_{\inf}(Q, S)$. It is valued in `EReal`: Statlib's `klIntegral` may be negative on
measures of mass larger than that of `Q`. -/
noncomputable def klInf (Q : Measure Ω) (S : Set (Measure Ω)) : EReal :=
  ⨅ P ∈ S, klIntegral Q P

theorem klInf_def : klInf Q S = ⨅ P ∈ S, klIntegral Q P := (rfl)

theorem klInf_le_klIntegral (hP : P ∈ S) : klInf Q S ≤ klIntegral Q P :=
  iInf₂_le P hP

theorem le_klInf_iff {c : EReal} : c ≤ klInf Q S ↔ ∀ P ∈ S, c ≤ klIntegral Q P :=
  le_iInf₂_iff

/-- `klInf` is antitone in the null. -/
@[gcongr]
theorem klInf_anti (hST : S ⊆ T) : klInf Q T ≤ klInf Q S :=
  biInf_mono hST

@[simp]
theorem klInf_empty : klInf Q ∅ = ⊤ := by
  simp [klInf_def]

@[simp]
theorem klInf_singleton : klInf Q {P} = klIntegral Q P := by
  simp [klInf_def]

theorem klInf_union : klInf Q (S ∪ T) = min (klInf Q S) (klInf Q T) :=
  iInf_union

/-- For a null whose members have the mass of `Q`, in particular for probability measures, `klInf`
is the smallest relative entropy `klDiv`. -/
theorem klInf_eq_iInf_klDiv [IsFiniteMeasure Q] (hS : ∀ P ∈ S, P univ = Q univ) :
    klInf Q S = ⨅ P ∈ S, (klDiv Q P : EReal) := by
  refine iInf_congr fun P ↦ iInf_congr fun hP ↦ ?_
  have : IsFiniteMeasure P := ⟨(hS P hP).trans_lt (measure_lt_top Q univ)⟩
  exact klIntegral_eq_klDiv (hS P hP).symm

/-- For a null whose members have the mass of `Q`, `klInf` is the coercion to `EReal` of the
smallest relative entropy `klDiv`, an infimum in `ℝ≥0∞`. -/
theorem klInf_eq_coe_iInf_klDiv [IsFiniteMeasure Q] (hS : ∀ P ∈ S, P univ = Q univ) :
    klInf Q S = ((⨅ P ∈ S, klDiv Q P : ℝ≥0∞) : EReal) := by
  simp only [klInf_eq_iInf_klDiv hS, EReal.coe_ennreal_iInf]

/-- `klInf Q S` is nonnegative when every member of `S` has mass at most that of `Q`, in
particular for a probability measure `Q` and a null of measures of mass at most one. -/
theorem klInf_nonneg [IsFiniteMeasure Q] (hS : ∀ P ∈ S, P univ ≤ Q univ) : 0 ≤ klInf Q S :=
  le_klInf_iff.2 fun P hP ↦
    have : IsFiniteMeasure P := ⟨(hS P hP).trans_lt (measure_lt_top Q univ)⟩
    klIntegral_nonneg (hS P hP)

/-! ### The largest e-power -/

/-- The largest e-power of the null `S` under `Q`: the largest expected logarithm
`∫ᵉ ω, log (X ω) ∂Q` of an e-variable `X` for `S`, Statlib's `maxUtility Q S logUtility`. -/
noncomputable def maxEPower (Q : Measure Ω) (S : Set (Measure Ω)) : EReal :=
  maxUtility Q S logUtility

theorem maxEPower_def : maxEPower Q S = maxUtility Q S logUtility := (rfl)

/-- The expected logarithm of an e-variable is at most the largest e-power. -/
theorem IsEVar.eintegral_log_le_maxEPower {X : Ω → ℝ≥0∞}
    (hX : IsEVar X S) (Q : Measure Ω) : ∫ᵉ ω, ENNReal.log (X ω) ∂Q ≤ maxEPower Q S := by
  simpa [maxEPower_def, logUtility_apply] using hX.eintegral_le_maxUtility Q logUtility

theorem maxEPower_le_iff {c : EReal} :
    maxEPower Q S ≤ c ↔ ∀ X, IsEVar X S → ∫ᵉ ω, ENNReal.log (X ω) ∂Q ≤ c := by
  simp only [maxEPower_def, maxUtility_eq_sSup, sSup_le_iff, mem_ofPred_eq, Function.comp_apply,
    logUtility_apply]
  exact ⟨fun h X hX ↦ h _ ⟨X, hX, rfl⟩, fun h _ ⟨X, hX, hb⟩ ↦ hb ▸ h X hX⟩

/-- The largest e-power exceeds `c` exactly when some e-variable has expected logarithm above
`c`. -/
theorem lt_maxEPower_iff {c : EReal} :
    c < maxEPower Q S ↔ ∃ X, IsEVar X S ∧ c < ∫ᵉ ω, ENNReal.log (X ω) ∂Q := by
  simpa using (maxEPower_le_iff (Q := Q) (S := S) (c := c)).not

/-- The numeraire of a null of measures of mass at most one attains the largest e-power under a
finite measure. This is Statlib's `maxUtility_eq_eintegral_numeraire`. -/
theorem maxEPower_eq_eintegral_numeraire [IsFiniteMeasure Q] (hS : ∀ P ∈ S, P univ ≤ 1) :
    maxEPower Q S = ∫ᵉ ω, ENNReal.log (numeraire Q S ω) ∂Q :=
  maxUtility_eq_eintegral_numeraire Q hS

/-- The empty null has infinite largest e-power under a nonzero measure: every measurable function,
`∞` included, is an e-variable for it. -/
@[simp]
theorem maxEPower_empty [NeZero Q] : maxEPower Q ∅ = ⊤ := by
  rw [maxEPower_def, maxUtility_empty, logUtility_apply, ENNReal.log_top]
  exact EReal.top_mul_of_pos (by simpa using NeZero.ne (Q univ))

/-- The largest e-power under the zero measure vanishes. This is `maxUtility_zero_measure`. -/
@[simp]
theorem maxEPower_zero_measure (S : Set (Measure Ω)) : maxEPower 0 S = 0 :=
  maxUtility_zero_measure S logUtility

/-- `maxEPower` is antitone in the null. -/
@[gcongr]
theorem maxEPower_anti (hST : S ⊆ T) : maxEPower Q T ≤ maxEPower Q S :=
  maxUtility_anti hST

/-- The largest e-power is nonnegative for a null of measures of mass at most one, for which the
constant `1` is an e-variable. -/
theorem maxEPower_nonneg (Q : Measure Ω) (hS : ∀ P ∈ S, P univ ≤ 1) : 0 ≤ maxEPower Q S :=
  maxUtility_nonneg Q hS

/-- A null and its effective null have the same e-variables, hence the same largest e-power. -/
@[simp]
theorem maxEPower_effectiveSet (Q : Measure Ω) (S : Set (Measure Ω)) :
    maxEPower Q (effectiveSet S) = maxEPower Q S := by
  simp only [maxEPower_def, maxUtility_eq_sSup, isEVar_effectiveSet_iff]

/-- **Duality** [LRR25]: the largest e-power of `S` is the smallest relative entropy to its
effective null. This is Statlib's `maxUtility_eq_iInf_klIntegral_effectiveSet`. -/
theorem maxEPower_eq_klInf_effectiveSet [IsProbabilityMeasure Q] (hS : ∀ P ∈ S, P univ ≤ 1) :
    maxEPower Q S = klInf Q (effectiveSet S) :=
  maxUtility_eq_iInf_klIntegral_effectiveSet hS

/-- **Weak duality**: the largest e-power of `S` is at most the smallest relative entropy to `S`. -/
theorem maxEPower_le_klInf [IsProbabilityMeasure Q] (hS : ∀ P ∈ S, P univ ≤ 1) :
    maxEPower Q S ≤ klInf Q S :=
  (maxEPower_eq_klInf_effectiveSet hS).trans_le (klInf_anti subset_effectiveSet)

/-- **The simple null**: the largest e-power of `{P}` is `klIntegral Q P`, for a measure `P` of
mass at most one. If `Q ≪ P`, the likelihood ratio `dQ/dP` is an e-variable that attains it;
otherwise an e-variable equal to `∞` on a `P`-null set charged by `Q` has infinite expected
logarithm. Statlib's `maxUtility_singleton_eq_klDiv` is the case of a probability measure `P`, and
the proof follows its proof. -/
theorem maxEPower_singleton [IsProbabilityMeasure Q] (hP : P univ ≤ 1) :
    maxEPower Q {P} = klIntegral Q P := by
  refine le_antisymm ((maxEPower_le_klInf (by simpa using hP)).trans_eq klInf_singleton) ?_
  have : IsFiniteMeasure P := ⟨hP.trans_lt ENNReal.one_lt_top⟩
  by_cases h_ac : Q ≪ P
  · have hX : IsEVar (Q.rnDeriv P) {P} := ⟨by fun_prop, fun μ hμ ↦ by
      obtain rfl : μ = P := hμ
      exact Measure.lintegral_rnDeriv_le.trans_eq measure_univ⟩
    refine le_of_eq_of_le ?_ (hX.eintegral_log_le_maxEPower Q)
    rw [klIntegral_eq_eintegral_llr h_ac]
    refine eintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_pos h_ac, h_ac.ae_le (Measure.rnDeriv_lt_top Q P)]
      with x h_pos h_lt_top
    rw [ENNReal.log_pos_real h_pos.ne' h_lt_top.ne, llr]
  -- an e-variable equal to `∞` on a `P`-null set charged by `Q`, and to `1` elsewhere
  obtain ⟨s, hs, hPs, hQs⟩ : ∃ s, MeasurableSet s ∧ P s = 0 ∧ Q s ≠ 0 := by
    by_contra! h
    exact h_ac (Measure.AbsolutelyContinuous.mk fun s hs hPs ↦ h s hs hPs)
  classical
  have hX : IsEVar (fun x ↦ if x ∈ s then ∞ else 1) {P} :=
    ⟨Measurable.ite hs measurable_const measurable_const, fun μ hμ ↦ by
      obtain rfl : μ = P := hμ
      rw [lintegral_congr_ae (g := fun _ ↦ 1)]
      · simpa using hP
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hPs] with x hx
      simp [hx]⟩
  rw [klIntegral_of_not_ac h_ac]
  refine le_of_eq_of_le ?_ (hX.eintegral_log_le_maxEPower Q)
  rw [eintegral_eq_lintegral_of_nonneg fun x ↦ by by_cases hx : x ∈ s <;> simp [hx],
    lintegral_congr (g := s.indicator fun _ ↦ ∞) fun x ↦ by by_cases hx : x ∈ s <;> simp [hx],
    lintegral_indicator_const hs]
  simp [ENNReal.top_mul hQs]

/-- **The simple null**, for probability measures: the largest e-power of `{P}` is the relative
entropy `klDiv Q P`. This is Statlib's `maxUtility_singleton_eq_klDiv`. -/
@[simp]
theorem maxEPower_singleton_eq_klDiv (Q P : Measure Ω) [IsProbabilityMeasure Q]
    [IsProbabilityMeasure P] : maxEPower Q {P} = klDiv Q P :=
  maxUtility_singleton_eq_klDiv Q P

/-- **Transfer of e-variables along a domination.** Let `c ≤ 1` be measurable, `Q`-almost
everywhere positive, with `ν.withDensity c ≤ m`. For every e-variable `E` for `{m}`, `c * E` is an
e-variable for `{ν}`; so, provided the expected value of `log c⁻¹` under `Q` is finite, the
largest e-power of `{m}` under `Q` exceeds that of `{ν}` by at most that expected value. -/
theorem maxEPower_singleton_le_add_eintegral_log_inv {m : Measure Ω} {c : Ω → ℝ≥0∞}
    (hc : Measurable c) (hc_le : ∀ ω, c ω ≤ 1) (hc_ne : ∀ᵐ ω ∂Q, c ω ≠ 0)
    (hle : ν.withDensity c ≤ m) (h_top : ∫ᵉ ω, ENNReal.log (c ω)⁻¹ ∂Q ≠ ⊤) :
    maxEPower Q {m} ≤ maxEPower Q {ν} + ∫ᵉ ω, ENNReal.log (c ω)⁻¹ ∂Q := by
  have hlog_nonneg (ω : Ω) : 0 ≤ ENNReal.log (c ω)⁻¹ :=
    ENNReal.zero_le_log_iff.2 (ENNReal.one_le_inv.2 (hc_le ω))
  refine maxEPower_le_iff.2 fun E hE ↦ ?_
  have hE_meas := hE.measurable
  -- `c * E` is an e-variable for `ν`
  have hcE : IsEVar (c * E) {ν} := by
    refine ⟨hc.mul hE_meas, fun ν' hν' ↦ ?_⟩
    rw [mem_singleton_iff] at hν'
    subst hν'
    rw [← lintegral_withDensity_eq_lintegral_mul _ hc hE_meas]
    exact (lintegral_mono' hle le_rfl).trans (hE.lintegral_le_one (mem_singleton m))
  -- `log E = log (c * E) + log c⁻¹` where `c` is positive
  have h_eq : ∀ᵐ ω ∂Q, ENNReal.log (E ω) =
      ENNReal.log ((c * E) ω) + ENNReal.log (c ω)⁻¹ := by
    filter_upwards [hc_ne] with ω hω
    rw [← ENNReal.log_mul_add, Pi.mul_apply, mul_comm (c ω), mul_assoc,
      ENNReal.mul_inv_cancel hω ((hc_le ω).trans_lt ENNReal.one_lt_top).ne, mul_one]
  calc ∫ᵉ ω, ENNReal.log (E ω) ∂Q
      = ∫ᵉ ω, ENNReal.log ((c * E) ω) + ENNReal.log (c ω)⁻¹ ∂Q := eintegral_congr_ae h_eq
    _ = ∫ᵉ ω, ENNReal.log ((c * E) ω) ∂Q + ∫ᵉ ω, ENNReal.log (c ω)⁻¹ ∂Q :=
        eintegral_add (by fun_prop) (by fun_prop) (eintegrable_of_nonneg hlog_nonneg)
          (.inr h_top) (.inr (EReal.ne_bot_of_nonneg (eintegral_nonneg hlog_nonneg)))
    _ ≤ maxEPower Q {ν} + ∫ᵉ ω, ENNReal.log (c ω)⁻¹ ∂Q :=
        add_le_add_left (hcE.eintegral_log_le_maxEPower Q) _

/-- **Additivity on products of nulls**: the largest e-power of the products of the members of
two nulls, under a product of probability measures, is the sum of the largest e-powers. This is
Statlib's `maxUtility_prod_eq_add`. -/
theorem maxEPower_prod_eq_add {Q₁ : Measure Ω} {Q₂ : Measure Ω'} [IsProbabilityMeasure Q₁]
    [IsProbabilityMeasure Q₂] {S₁ : Set (Measure Ω)} {S₂ : Set (Measure Ω')}
    (hS₁ : ∀ P ∈ S₁, P univ ≤ 1) (hS₂ : ∀ P ∈ S₂, P univ ≤ 1) :
    maxEPower (Q₁.prod Q₂) (image2 Measure.prod S₁ S₂) = maxEPower Q₁ S₁ + maxEPower Q₂ S₂ :=
  maxUtility_prod_eq_add Q₁ Q₂ hS₁ hS₂

/-- **Data processing** along a measurable map: pushing the measure and the null forward along `φ`
does not increase the largest e-power. This is Statlib's `maxUtility_map_le`. -/
theorem maxEPower_map_le (Q : Measure Ω) {φ : Ω → Ω'} (hφ : Measurable φ) :
    maxEPower (Q.map φ) (mapNull φ S) ≤ maxEPower Q S :=
  mapNull_def φ S ▸ maxUtility_map_le Q hφ

/-- Pushing the measure and the null forward along a measurable embedding preserves the largest
e-power. This is Statlib's `MeasurableEmbedding.maxUtility_map_eq`. -/
theorem _root_.MeasurableEmbedding.maxEPower_map_eq [Nonempty Ω] {φ : Ω → Ω'}
    (hφ : MeasurableEmbedding φ) (Q : Measure Ω) (S : Set (Measure Ω)) :
    maxEPower (Q.map φ) (mapNull φ S) = maxEPower Q S :=
  mapNull_def φ S ▸ MeasurableEmbedding.maxUtility_map_eq φ hφ Q S

/-- Pushing the measure and the null forward along a measurable equivalence preserves the largest
e-power. Unlike `MeasurableEmbedding.maxEPower_map_eq`, no point of `Ω` is needed: the inverse
carries the e-variables back. -/
theorem _root_.MeasurableEquiv.maxEPower_map_eq (e : Ω ≃ᵐ Ω') (Q : Measure Ω)
    (S : Set (Measure Ω)) :
    maxEPower (Q.map e) (mapNull e S) = maxEPower Q S := by
  refine le_antisymm (maxEPower_map_le Q e.measurable) ?_
  have h := maxEPower_map_le (Q.map e) (S := mapNull e S) e.symm.measurable
  rwa [Measure.map_map e.symm.measurable e.measurable, mapNull_mapNull e.symm.measurable
    e.measurable, e.symm_comp_self, Measure.map_id, mapNull_id] at h

/-! ### `klDiv` cannot replace `klIntegral` -/

/-- The divergence from `Q` to a multiple `c • Q` of itself: `klIntegral Q (c • Q)` is
`-log c * Q univ`. -/
theorem klIntegral_smul_right_self [IsFiniteMeasure Q] {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    klIntegral Q (c • Q) = ((-Real.log c.toReal * Q.real univ : ℝ) : EReal) := by
  have h_ac : Q ≪ c • Q := Measure.absolutelyContinuous_smul hc0
  have h_eq : llr Q (c • Q) =ᵐ[Q] fun _ ↦ -Real.log c.toReal := by
    filter_upwards [llr_smul_right Measure.AbsolutelyContinuous.rfl c hc0 hc, llr_self Q]
      with x hx hx0
    rw [hx, hx0, Pi.zero_apply, zero_sub]
  have h_int : Integrable (llr Q (c • Q)) Q := (integrable_congr h_eq).2 (integrable_const _)
  rw [klIntegral_of_ac_of_integrable h_ac h_int, integral_congr_ae h_eq, integral_const,
    smul_eq_mul, mul_comm]

/-- With `klDiv` in place of `klIntegral`, weak duality fails on measures of mass less than one:
for a probability measure `Q` and `0 < c < 1`, `klDiv Q (c • Q) = -log c + c - 1` is smaller than
the largest e-power `-log c` of the simple null `{c • Q}`. For `Q` a Dirac mass and `c = 1 / 2`,
these are `log 2 - 1 / 2` and `log 2`. -/
theorem coe_klDiv_smul_right_self_lt_maxEPower [IsProbabilityMeasure Q] {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc1 : c < 1) : (klDiv Q (c • Q) : EReal) < maxEPower Q {c • Q} := by
  have hc : c ≠ ∞ := hc1.ne_top
  have hcQ : (c • Q) univ = c := by simp
  have : IsFiniteMeasure (c • Q) := ⟨by simpa [hcQ] using hc.lt_top⟩
  rw [maxEPower_singleton (hcQ.trans_le hc1.le), coe_klDiv_eq_klIntegral_add_sub,
    klIntegral_smul_right_self hc0 hc]
  simp only [measureReal_def, hcQ, measure_univ, ENNReal.toReal_one, mul_one]
  have : c.toReal < 1 := by simpa using (ENNReal.toReal_lt_toReal hc ENNReal.one_ne_top).2 hc1
  norm_cast
  linarith

end ProbabilityTheory
