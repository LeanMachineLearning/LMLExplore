/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import LMLExplore.EValues.LevelAttained
public import LMLExplore.EValues.Null.Basic
public import LMLExplore.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Probability.ProductMeasure
public import Statlib.EValues.NumeraireExistence
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.Data.EReal.Inv
import LMLExplore.EValues.BipolarRate.AlmostSure
import LMLExplore.EValues.BipolarRate.Numeraire.Basic
import LMLExplore.Probability.ProductMeasure

/-!
# Bahadur slopes: p-variables decrease at most at the bipolar rate

Let `S₁` be a set of probability measures on `𝓧` (the null) and `Q₁` a law on `𝓧` (the
alternative). The observations are the coordinates of `ℕ → 𝓧`, with the i.i.d. laws
`Measure.infinitePi fun _ ↦ P`, and `d = bipolarRate Q₁ S₁`. For p-variables `p n` of the
`n`-sample nulls `sampleNull S₁ n`, almost surely under the i.i.d. law of `Q₁`,
`limsup (1/n) log (1 / p n) ≤ d`, with `p n` evaluated at the first `n` observations
[EVR26, Note 42, Theorem 11]. The bound is attained: the inverses `p* n = (X* n)⁻¹` of the
numeraires `X* n` of the `n`-sample nulls under `Q₁ ^ n` are p-variables, and
`log (1 / p* n) = log (X* n)`, so that `(1/n) log (1 / p* n)` tends to `d` almost surely
(`ProbabilityTheory.ae_tendsto_log_numeraire_div_bipolarRate`).

Bahadur's exact slope at `Q₁` of a sequence of statistics `T n` of `n` observations is the almost
sure limit, when it exists, of `(2/n) log (1 / L n)`, with `L n` the level attained by `T n`
against the `n`-sample null (`ProbabilityTheory.levelAttained`) [Bah67]. The levels attained are
p-variables, so no exact slope exceeds `2 d`; the level attained by an e-variable is at most its
inverse, so the numeraires have the exact slope `2 d`. The best exact slope at `Q₁` is therefore
`2 d`, for every null of probability measures and every probability measure `Q₁`, with no other
assumption on either. Since the bipolar rate is at most the smallest relative entropy from `Q₁`
to the null (`ProbabilityTheory.bipolarRate_le_klInf`), every exact slope is also at most
`2 * klInf Q₁ S₁`.

## Main statements

* `ProbabilityTheory.ae_limsup_log_inv_div_le_bipolarRate`: p-variables of the `n`-sample nulls
  decrease almost surely at most at the bipolar rate.
* `ProbabilityTheory.isPVar_inv_numeraire`: the inverses of the numeraires of the `n`-sample nulls
  are p-variables.
* `ProbabilityTheory.ae_limsup_two_mul_log_inv_levelAttained_div_le`: no exact slope exceeds twice
  the bipolar rate.
* `ProbabilityTheory.ae_tendsto_two_mul_log_inv_levelAttained_numeraire_div`: the exact slope of
  the numeraires is twice the bipolar rate.
* `ProbabilityTheory.isGreatest_exactSlope`: twice the bipolar rate is the largest exact slope.

## Implementation notes

For a rational `r` with `d < r`, the function `exp (n r) * 𝟙{p n ≤ exp (-(n r))}` is a test of
level `exp (-(n r))` divided by its level, an `n`-sample e-variable. By
`ProbabilityTheory.ae_limsup_log_div_le_bipolarRate`, almost surely it is below `exp (n r)` for all
large `n`, that is, `exp (-(n r)) < p n`. Intersecting these events over the rationals gives the
bound.

The statements and proofs are adapted from the last section of
`EValuesResearch/Results/FiniteAlphabetRate.lean` and from
`EValuesResearch/Results/BahadurSlope.lean` (commit `83205cb`) in the paper project
`RemyDegenne/evalues_research`, which formalize [EVR26, Note 42, Theorem 11], rewritten on the API
of LMLExplore; the bound for p-variables is proved here through tests rather than through power
calibrators.

## References

* [Bah67] R. R. Bahadur, *Rates of convergence of estimates and test statistics*, Ann. Math.
  Statist. 38 (1967), 303–324.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 49 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 β : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}

/-- **No sequence of p-variables decreases faster than the bipolar rate, almost surely.** For
p-variables `p n` of the `n`-sample nulls of a set `S₁` of probability measures, almost surely
under the i.i.d. law of `Q₁`, `p n` evaluated at the first `n` observations has
`limsup (1/n) log (1 / p n) ≤ bipolarRate Q₁ S₁` [EVR26, Note 42, Theorem 11]. No hypothesis on
`Q₁` is needed: when it is not a probability measure, its i.i.d. law is zero. -/
theorem ae_limsup_log_inv_div_le_bipolarRate (Q₁ : Measure 𝓧)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {p : (n : ℕ) → (Fin n → 𝓧) → ℝ≥0∞}
    (hp : ∀ n, IsPVar (p n) (sampleNull S₁ n)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      limsup (fun n : ℕ ↦ ENNReal.log (p n (initSeg n ω))⁻¹ / (n : EReal)) atTop ≤
        bipolarRate Q₁ S₁ := by
  by_cases hQ₁ : IsProbabilityMeasure Q₁
  swap
  · simp [Measure.infinitePi_eq_zero_of_not_isProbabilityMeasure (μ := fun _ : ℕ ↦ Q₁) (i := 0)
      hQ₁]
  -- for a rational `r`, the tests `𝟙{p n ≤ exp (-(n r))}` divided by their levels are e-variables
  have h_ae : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁), ∀ r : ℚ,
      limsup (fun n : ℕ ↦ ENNReal.log
        ({x | p n x ≤ ENNReal.ofReal (Real.exp (-(n * r)))}.indicator 1 (initSeg n ω) /
          ENNReal.ofReal (Real.exp (-(n * r)))) / (n : EReal)) atTop ≤ bipolarRate Q₁ S₁ :=
    ae_all_iff.2 fun r ↦ ae_limsup_log_div_le_bipolarRate Q₁ hS₁
      (M := fun n x ↦ {x | p n x ≤ ENNReal.ofReal (Real.exp (-(n * r)))}.indicator 1 x /
        ENNReal.ofReal (Real.exp (-(n * r))))
      fun n ↦ ((hp n).isTest_indicator _).isEVar_div
  filter_upwards [h_ae] with ω hω
  refine le_of_forall_gt_imp_ge_of_dense fun y hy ↦ ?_
  obtain ⟨r, hr, hry⟩ := EReal.lt_iff_exists_rat_btwn.1 hy
  refine (limsup_le_of_le (h := ?_)).trans hry.le
  filter_upwards [eventually_lt_of_limsup_lt ((hω r).trans_lt hr), eventually_gt_atTop 0]
    with n hn hn0
  rw [ENNReal.log_inv]
  refine ENNReal.neg_log_div_le_of_ofReal_exp_le hn0 (not_le.1 fun hpn ↦ hn.not_ge ?_).le
  -- where `p n ≤ exp (-(n r))`, the e-variable is `exp (n r)`
  rw [EReal.coe_le_div_natCast_iff hn0, Set.indicator_of_mem hpn, Pi.one_apply, one_div,
    ENNReal.log_inv, ENNReal.log_ofReal_exp, EReal.coe_neg, neg_neg]

/-- The inverse of the numeraire of the `n`-sample null under `Q₁ ^ n` is a p-variable for the
`n`-sample null, for a null `S₁` of measures of mass at most one
[EVR26, Note 42, Theorem 11]. -/
theorem isPVar_inv_numeraire (Q₁ : Measure 𝓧) (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) (n : ℕ) :
    IsPVar (fun x ↦ (numeraire (Measure.pi fun _ : Fin n ↦ Q₁) (sampleNull S₁ n) x)⁻¹)
      (sampleNull S₁ n) :=
  (isEVar_numeraire _ (measure_univ_le_one_of_mem_sampleNull hS₁ n)).isPVar_inv

/-- **No exact slope exceeds twice the bipolar rate.** For measurable statistics `T n` of `n`
observations, with values in a linear order whose topology is order-closed and hereditarily
Lindelöf (for instance `ℝ` or `ℝ≥0∞`), and `L n` the level attained by `T n` against the
`n`-sample null of a set `S₁` of probability measures, almost surely under the i.i.d. law of `Q₁`,
`limsup (2/n) log (1 / L n) ≤ 2 * bipolarRate Q₁ S₁`, where `T n` is evaluated at the first `n`
observations [EVR26, Note 42, Theorem 11]. -/
theorem ae_limsup_two_mul_log_inv_levelAttained_div_le [LinearOrder β] [TopologicalSpace β]
    [OrderClosedTopology β] [HereditarilyLindelofSpace β] [MeasurableSpace β]
    [OpensMeasurableSpace β] (Q₁ : Measure 𝓧) (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    {T : (n : ℕ) → (Fin n → 𝓧) → β} (hT : ∀ n, Measurable (T n)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      limsup (fun n : ℕ ↦ 2 * ENNReal.log
          (levelAttained (T n) (sampleNull S₁ n) (initSeg n ω))⁻¹ / (n : EReal)) atTop ≤
        2 * bipolarRate Q₁ S₁ := by
  filter_upwards [ae_limsup_log_inv_div_le_bipolarRate Q₁ hS₁
    fun n ↦ isPVar_levelAttained (hT n) _] with ω hω
  simp_rw [mul_div_assoc]
  rw [EReal.limsup_const_mul_of_nonneg_of_ne_top zero_le_two
    (by exact_mod_cast EReal.natCast_ne_top 2)]
  exact mul_le_mul_of_nonneg_left hω zero_le_two

/-- **The numeraires have twice the bipolar rate as exact slope.** For `L n` the level attained by
the numeraire of the `n`-sample null of a set `S₁` of probability measures under `Q₁ ^ n`, almost
surely under the i.i.d. law of `Q₁`, `(2/n) log (1 / L n)` tends to `2 * bipolarRate Q₁ S₁`, also
when the bipolar rate is infinite [EVR26, Note 42, Theorem 11]. No hypothesis on `Q₁` is needed:
when it is not a probability measure, its i.i.d. law is zero. -/
theorem ae_tendsto_two_mul_log_inv_levelAttained_numeraire_div (Q₁ : Measure 𝓧)
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
      Tendsto (fun n : ℕ ↦ 2 * ENNReal.log
          (levelAttained (numeraire (Measure.pi fun _ : Fin n ↦ Q₁) (sampleNull S₁ n))
            (sampleNull S₁ n) (initSeg n ω))⁻¹ / (n : EReal)) atTop
        (𝓝 (2 * bipolarRate Q₁ S₁)) := by
  by_cases hQ₁ : IsProbabilityMeasure Q₁
  swap
  · simp [Measure.infinitePi_eq_zero_of_not_isProbabilityMeasure (μ := fun _ : ℕ ↦ Q₁) (i := 0)
      hQ₁]
  have hX (n : ℕ) : IsEVar (numeraire (Measure.pi fun _ : Fin n ↦ Q₁) (sampleNull S₁ n))
      (sampleNull S₁ n) := isEVar_numeraire _
    (measure_univ_le_one_of_mem_sampleNull (fun P hP ↦ (hS₁ P hP).measure_univ.le) n)
  filter_upwards [ae_limsup_log_inv_div_le_bipolarRate Q₁ hS₁
      fun n ↦ isPVar_levelAttained (hX n).measurable _,
    ae_tendsto_log_numeraire_div_bipolarRate Q₁ hS₁] with ω hup hlow
  -- the level attained by the numeraire is at most its inverse
  have hlim : Tendsto (fun n : ℕ ↦ ENNReal.log
      (levelAttained (numeraire (Measure.pi fun _ : Fin n ↦ Q₁) (sampleNull S₁ n))
        (sampleNull S₁ n) (initSeg n ω))⁻¹ / (n : EReal)) atTop (𝓝 (bipolarRate Q₁ S₁)) := by
    refine tendsto_of_le_liminf_of_limsup_le ?_ hup
    rw [← hlow.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall fun n ↦
      EReal.div_le_div_right_of_nonneg (Nat.cast_nonneg' n) (ENNReal.log_le_log
        (ENNReal.le_inv_iff_le_inv.1 ((hX n).levelAttained_le_inv _))))
  simpa only [mul_div_assoc] using
    EReal.Tendsto.const_mul hlim (Or.inl (by exact_mod_cast EReal.natCast_ne_bot 2))
      (Or.inl (by exact_mod_cast EReal.natCast_ne_top 2))

/-- **The best exact slope in Bahadur's sense is twice the bipolar rate.** Among the almost sure
limits `c` of `(2/n) log (1 / L n)` under the i.i.d. law of a probability measure `Q₁`, for
measurable statistics `T n` of `n` observations with values in `[0, ∞]` and `L n` the level
attained by `T n` against the `n`-sample null of a set `S₁` of probability measures, the largest
is `2 * bipolarRate Q₁ S₁`, attained by the numeraires [EVR26, Note 42, Theorem 11]. A statistic
with values in another linear order that embeds in `[0, ∞]`, such as `ℝ`, has the levels attained
of its composition with the embedding (`ProbabilityTheory.levelAttained_comp`). -/
theorem isGreatest_exactSlope (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) :
    IsGreatest {c : EReal | ∃ T : (n : ℕ) → (Fin n → 𝓧) → ℝ≥0∞, (∀ n, Measurable (T n)) ∧
        ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁),
          Tendsto (fun n : ℕ ↦ 2 * ENNReal.log
            (levelAttained (T n) (sampleNull S₁ n) (initSeg n ω))⁻¹ / (n : EReal)) atTop (𝓝 c)}
      (2 * bipolarRate Q₁ S₁) := by
  refine ⟨⟨fun n ↦ numeraire (Measure.pi fun _ : Fin n ↦ Q₁) (sampleNull S₁ n),
    fun n ↦ (isEVar_numeraire _ (measure_univ_le_one_of_mem_sampleNull
      (fun P hP ↦ (hS₁ P hP).measure_univ.le) n)).measurable,
    ae_tendsto_two_mul_log_inv_levelAttained_numeraire_div Q₁ hS₁⟩, ?_⟩
  rintro c ⟨T, hT, hc⟩
  obtain ⟨ω, hω, hω'⟩ := (hc.and (ae_limsup_two_mul_log_inv_levelAttained_div_le Q₁ hS₁ hT)).exists
  rw [← hω.limsup_eq]
  exact hω'

end ProbabilityTheory
