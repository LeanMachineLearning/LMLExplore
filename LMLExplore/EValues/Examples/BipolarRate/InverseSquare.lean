/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Probability.Distributions.Geometric
import LMLExplore.InformationTheory.KullbackLeibler.Variational
import LMLExplore.MeasureTheory.Function.SimpleFunc
import LMLExplore.MeasureTheory.Integral.BoundedMeasurable
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ZetaValues

/-!
# The block criterion for `d = klInf` needs a finite smallest relative entropy

For a null `S` of probability measures with `klInf Q S < ∞`, the bipolar rate `d` equals
`klInf Q S` exactly when, for every `η > 0`, some `n ≥ 1` and some basic neighbourhood of `Q ^ n`
for the topology of the integrals of the bounded measurable functions contain only laws at
relative entropy at least `n (klInf Q S - η)` from every `P ^ n`, `P ∈ S`
(`ProbabilityTheory.bipolarRate_eq_klInf_iff_forall_exists`) [EVR26, Note 15]. The finiteness is
needed. For the simple null `{P}` with `KL(Q ‖ P) = ∞`, `d = klInf Q {P} = ∞`; but if `P` charges
every point, every basic neighbourhood of every `Q ^ n` contains a law carried by a finite set,
which is at finite relative entropy from `P ^ n`, so the condition of the criterion fails.

An instance is the law `Q {j} = 6 / (π² (j + 1)²)` on `ℕ` against the geometric law
`P {j} = 2 ^ (-(j + 1))` (Mathlib's `geometricMeasure` with success probability `1 / 2`): the
logarithm of the likelihood ratio grows linearly in `j` while `Q` has an infinite mean, so that
`KL(Q ‖ P) = ∞`.

## Main statements

* `ProbabilityTheory.exists_klDiv_ne_top_forall_abs_integral_sub_le`: if a measure `ν` charges
  every point, every basic neighbourhood of a probability measure `μ` contains a
  probability measure at finite relative entropy from `ν`.
* `ProbabilityTheory.exists_klDiv_pi_ne_top_forall_abs_integral_sub_le`: if `P` charges every
  point, every basic neighbourhood of every `Q ^ n` contains a probability measure at finite
  relative entropy from `P ^ n`.
* `ProbabilityTheory.not_bipolarRate_eq_klInf_iff_of_klDiv_eq_top`: if moreover `KL(Q ‖ P) = ∞`,
  the equivalence of `ProbabilityTheory.bipolarRate_eq_klInf_iff_forall_exists` fails for the null
  `{P}`.
* `ProbabilityTheory.klDiv_inverseSquare_geometricMeasure_eq_top`: the law
  `Q {j} = 6 / (π² (j + 1)²)` is at infinite relative entropy from the geometric law
  `P {j} = 2 ^ (-(j + 1))` on `ℕ`.

## Implementation notes

The law carried by a finite set is the image of `μ` by a measurable map with finite range along
which the statistics of the neighbourhood move by less than its tolerance
(`MeasureTheory.exists_measurable_finite_range_forall_abs_integral_map_sub_le`); it is at finite
relative entropy from `ν`, which charges each of its finitely many points. The relative entropy
`KL(Q ‖ P) = ∞` is proved by the Donsker–Varadhan inequality for the logarithm of the likelihood
ratio on the points of `[199, J)` (`InformationTheory.ofReal_sum_mul_log_sub_log_two_le_klDiv`),
where the terms `q_j log (q_j / p_j)` are at least
`1 / (5 (j + 1))`, and by the divergence of the harmonic series.

The statements and proofs are adapted from `EValuesResearch/Results/Envelopes.lean` (commit
`83205cb`) in the paper project `RemyDegenne/evalues_research`, rewritten on the API of
LMLExplore. The source states the instance only, for a law `Q` defined by its density with
respect to the counting measure, and obtains the laws of finite support by conditioning `Q ^ n`
on large boxes.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory InformationTheory Filter Real
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-! ### Basic neighbourhoods contain laws at finite relative entropy -/

/-- **Every basic neighbourhood of `μ` contains a law at finite relative entropy from `ν`** when
the measure `ν` charges every point: for a probability measure `μ`, finitely many
bounded measurable real functions `g i` and `ε > 0`, some probability measure `R` has
`|∫ g i ∂R - ∫ g i ∂μ| ≤ ε` for every `i` and `klDiv R ν ≠ ∞`. -/
theorem exists_klDiv_ne_top_forall_abs_integral_sub_le
    (μ ν : Measure 𝓧) [IsProbabilityMeasure μ] (hν : ∀ x, ν {x} ≠ 0)
    {ι : Type*} [Finite ι] {g : ι → 𝓧 → ℝ} (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i, ∃ C, ∀ x, |g i x| ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : Measure 𝓧, IsProbabilityMeasure R ∧ (∀ i, |∫ x, g i x ∂R - ∫ x, g i x ∂μ| ≤ ε) ∧
      klDiv R ν ≠ ∞ := by
  -- the image of `μ` by a map with finite range along which the `g i` move by less than `ε`
  obtain ⟨s, hs, hsf, hsg⟩ :=
    exists_measurable_finite_range_forall_abs_integral_map_sub_le hg hgb hε μ
  refine ⟨μ.map s, inferInstance, fun i ↦ (hsg i).trans_eq (by rw [probReal_univ, mul_one]), ?_⟩
  -- `ν` charges every point, and the image of `μ` is carried by the finite range of `s`
  refine klDiv_ne_top (Measure.AbsolutelyContinuous.mk fun A _ hA ↦ ?_) ?_
  · rw [Set.eq_empty_of_forall_notMem fun x hx ↦
      hν x (measure_mono_null (Set.singleton_subset_iff.2 hx) hA), measure_empty]
  · refine (integrable_map_measure (measurable_llr _ _).aestronglyMeasurable
      hs.aemeasurable).2 ?_
    refine .of_bound ((measurable_llr _ _).comp hs).aestronglyMeasurable
      (∑ y ∈ hsf.toFinset, |llr (μ.map s) ν y|) (.of_forall fun x ↦ ?_)
    rw [Function.comp_apply, Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun y ↦ |llr (μ.map s) ν y|) (fun _ _ ↦ abs_nonneg _)
      (hsf.mem_toFinset.2 ⟨x, rfl⟩)

/-- **Every basic neighbourhood of `Q ^ n` contains a law at finite relative entropy from
`P ^ n`** when `P` is a σ-finite measure that charges every point [EVR26, Note 15]: for a
probability measure `Q`, finitely many bounded measurable real functions `g i` on `𝓧 ^ n` and
`ε > 0`, some probability measure `R` has `|∫ g i ∂R - ∫ g i ∂(Q ^ n)| ≤ ε` for every `i` and
`klDiv R (P ^ n) ≠ ∞`. -/
theorem exists_klDiv_pi_ne_top_forall_abs_integral_sub_le
    (Q P : Measure 𝓧) [IsProbabilityMeasure Q] [SigmaFinite P] (hP : ∀ x, P {x} ≠ 0) (n : ℕ)
    {k : ℕ} {g : Fin k → (Fin n → 𝓧) → ℝ} (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i, ∃ C, ∀ x, |g i x| ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : Measure (Fin n → 𝓧), IsProbabilityMeasure R ∧
      (∀ i, |∫ x, g i x ∂R - ∫ x, g i x ∂(Measure.pi fun _ : Fin n ↦ Q)| ≤ ε) ∧
      klDiv R (Measure.pi fun _ : Fin n ↦ P) ≠ ∞ :=
  exists_klDiv_ne_top_forall_abs_integral_sub_le _ _ (fun x ↦ by
    rw [Measure.pi_singleton]
    exact Finset.prod_ne_zero_iff.2 fun i _ ↦ hP (x i)) hg hgb hε

/-- **The block criterion fails at an infinite relative entropy** [EVR26, Note 15]. For a
probability measure `P` that charges every point and a probability measure `Q` with
`KL(Q ‖ P) = ∞`, the bipolar rate of `Q` against `{P}` and the smallest relative entropy are both
infinite, while no basic neighbourhood of any `Q ^ n` contains only laws at infinite relative
entropy from `P ^ n`: the equivalence of `ProbabilityTheory.bipolarRate_eq_klInf_iff_forall_exists`
needs its assumption `klInf Q S ≠ ⊤`. -/
theorem not_bipolarRate_eq_klInf_iff_of_klDiv_eq_top
    (Q P : Measure 𝓧) [IsProbabilityMeasure Q] [IsProbabilityMeasure P] (hP : ∀ x, P {x} ≠ 0)
    (hQP : klDiv Q P = ∞) :
    ¬ (bipolarRate Q {P} = klInf Q {P} ↔ ∀ η : ℝ, 0 < η →
      ∃ (n k : ℕ) (g : Fin k → (Fin n → 𝓧) → ℝ) (ε : ℝ), n ≠ 0 ∧ 0 < ε ∧
        (∀ i, Measurable (g i)) ∧ (∀ i, ∃ C, ∀ x, |g i x| ≤ C) ∧
        ∀ R : Measure (Fin n → 𝓧), IsProbabilityMeasure R →
          (∀ i, |∫ x, g i x ∂R - ∫ x, g i x ∂(Measure.pi fun _ : Fin n ↦ Q)| ≤ ε) →
          ∀ P' ∈ ({P} : Set (Measure 𝓧)), (n : EReal) * (klInf Q {P} - η) ≤
            ((klDiv R (Measure.pi fun _ : Fin n ↦ P') : ℝ≥0∞) : EReal)) := by
  have hkl : klInf Q {P} = ⊤ := by
    rw [klInf_singleton, klIntegral_eq_klDiv (by simp), hQP, EReal.coe_ennreal_top]
  rw [bipolarRate_singleton, hQP, EReal.coe_ennreal_top, hkl]
  intro h
  obtain ⟨n, k, g, ε, hn, hε, hg, hgb, hR⟩ := h.1 rfl 1 one_pos
  obtain ⟨R, hR1, hRg, hRP⟩ := exists_klDiv_pi_ne_top_forall_abs_integral_sub_le Q P hP n hg hgb hε
  have h1 := hR R hR1 hRg P rfl
  rw [EReal.top_sub_coe, EReal.mul_top_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn),
    top_le_iff, EReal.coe_ennreal_eq_top_iff] at h1
  exact hRP h1

/-! ### The inverse-square law against the geometric law -/

/-- The masses `6 / (π² (j + 1)²)` of the inverse-square law on `ℕ` sum to one. -/
private lemma hasSum_inverseSquare :
    HasSum (fun j : ℕ ↦ 6 / (π ^ 2 * ((j : ℝ) + 1) ^ 2)) 1 := by
  have h := (hasSum_nat_add_iff' (f := fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) 1).2 hasSum_zeta_two
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h
  have hπ : π ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  convert h.mul_left (6 / π ^ 2) using 1
  · ext j
    field_simp
  · field_simp

/-- From `j = 199` on, the term `q_j log (q_j / p_j)` of the inverse-square law
`q_j = 6 / (π² (j + 1)²)` against the geometric law `p_j = 2 ^ (-(j + 1))` is at least
`1 / (5 (j + 1))`. -/
private lemma inv_five_mul_inv_le_inverseSquare_mul_log (j : ℕ) (hj : 199 ≤ j) :
    (1 / 5) * (1 / ((j : ℝ) + 1)) ≤ 6 / (π ^ 2 * ((j : ℝ) + 1) ^ 2) *
      Real.log (6 / (π ^ 2 * ((j : ℝ) + 1) ^ 2) / (2⁻¹ : ℝ) ^ (j + 1)) := by
  set x : ℝ := (j : ℝ) + 1 with hx_def
  have hx : 200 ≤ x := by rw [hx_def]; exact_mod_cast (show 200 ≤ j + 1 by omega)
  have hxpos : 0 < x := by linarith
  have hlog2 := Real.log_two_gt_d9
  have hπ := Real.pi_lt_d2
  have hπpos := Real.pi_pos
  have hlogπ : Real.log π ≤ π - 1 := Real.log_le_sub_one_of_pos hπpos
  have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hlogx : Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div hxpos.le (by norm_num)
  set r := x ^ (1 / 2 : ℝ) with hr
  have hr2 : r ^ 2 = x := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; norm_num
  have hr0 : 0 ≤ r := Real.rpow_nonneg hxpos.le _
  have hr14 : 14 ≤ r := by nlinarith
  -- the logarithm of the likelihood ratio is at least `x / 3`
  have hjx : ((j + 1 : ℕ) : ℝ) = x := by rw [hx_def]; push_cast; ring
  have hqpos : 0 < 6 / (π ^ 2 * x ^ 2) := by positivity
  have hppos : 0 < (2⁻¹ : ℝ) ^ (j + 1) := by positivity
  have hlogq : Real.log (6 / (π ^ 2 * x ^ 2)) = Real.log 6 - 2 * Real.log π - 2 * Real.log x := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlogp : Real.log ((2⁻¹ : ℝ) ^ (j + 1)) = -(x * Real.log 2) := by
    rw [Real.log_pow, Real.log_inv, hjx]
    ring
  have hL : x / 3 ≤ Real.log (6 / (π ^ 2 * x ^ 2) / (2⁻¹ : ℝ) ^ (j + 1)) := by
    rw [Real.log_div hqpos.ne' hppos.ne', hlogq, hlogp]
    nlinarith
  have hπ2 : π ^ 2 ≤ 10 := by nlinarith
  calc (1 / 5) * (1 / x) = 2 / (10 * x) := by field_simp; ring
  _ ≤ 2 / (π ^ 2 * x) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  _ = 6 / (π ^ 2 * x ^ 2) * (x / 3) := by field_simp; ring
  _ ≤ 6 / (π ^ 2 * x ^ 2) * Real.log (6 / (π ^ 2 * x ^ 2) / (2⁻¹ : ℝ) ^ (j + 1)) :=
    mul_le_mul_of_nonneg_left hL hqpos.le

/-- **The inverse-square law is at infinite relative entropy from the geometric law.** The law
`Q {j} = 6 / (π² (j + 1)²)` on `ℕ` has `KL(Q ‖ P) = ∞` for the geometric law
`P {j} = 2 ^ (-(j + 1))` [EVR26, Note 15]. With
`ProbabilityTheory.not_bipolarRate_eq_klInf_iff_of_klDiv_eq_top`, the bipolar rate of `Q` against
`{P}` and the smallest relative entropy are both infinite, while every basic neighbourhood of
every `Q ^ n` contains a law at finite relative entropy from `P ^ n`. -/
theorem klDiv_inverseSquare_geometricMeasure_eq_top :
    klDiv (Measure.sum fun j : ℕ ↦
        ENNReal.ofReal (6 / (π ^ 2 * ((j : ℝ) + 1) ^ 2)) • Measure.dirac j)
      (geometricMeasure ⟨2⁻¹, by norm_num, by norm_num⟩) = ∞ := by
  set Q := Measure.sum fun j : ℕ ↦
    ENNReal.ofReal (6 / (π ^ 2 * ((j : ℝ) + 1) ^ 2)) • Measure.dirac j with hQ_def
  set P := geometricMeasure (⟨2⁻¹, by norm_num, by norm_num⟩ : unitInterval) with hP_def
  have : IsProbabilityMeasure Q :=
    hasSum_inverseSquare.isProbabilityMeasure_sum_dirac fun j ↦ by positivity
  have hq (j : ℕ) : Q.real {j} = 6 / (π ^ 2 * ((j : ℝ) + 1) ^ 2) := by
    rw [measureReal_def, hQ_def, Measure.sum_smul_dirac_singleton,
      ENNReal.toReal_ofReal (by positivity)]
  have hp (j : ℕ) : P.real {j} = (2⁻¹ : ℝ) ^ (j + 1) := by
    rw [hP_def, geometricMeasure_real_singleton fun h ↦ by simpa using congrArg Subtype.val h]
    norm_num
    ring
  -- the harmonic series diverges
  refine ENNReal.eq_top_of_forall_nnreal_le fun T ↦ ?_
  have hH := Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨J, hJ⟩ := (hH.eventually (eventually_ge_atTop
    (5 * ((T : ℝ) + Real.log 2) + ∑ i ∈ Finset.range 199, 1 / ((i : ℝ) + 1)))).and
      (eventually_ge_atTop 199) |>.exists
  refine le_trans ?_ (ofReal_sum_mul_log_sub_log_two_le_klDiv Q P (Finset.Ico 199 J)
    (fun j _ ↦ by rw [hq]; positivity) (fun j _ ↦ by rw [hp]; positivity))
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsum : (1 / 5) * ∑ j ∈ Finset.Ico 199 J, 1 / ((j : ℝ) + 1) ≤
      ∑ j ∈ Finset.Ico 199 J, Q.real {j} * Real.log (Q.real {j} / P.real {j}) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj ↦ ?_
    rw [hq, hp]
    exact inv_five_mul_inv_le_inverseSquare_mul_log j (Finset.mem_Ico.1 hj).1
  rw [Finset.sum_Ico_eq_sub _ hJ.2] at hsum
  linarith [hJ.1]

end ProbabilityTheory
