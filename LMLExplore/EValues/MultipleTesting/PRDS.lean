/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.MultipleTesting.EBH
import LMLExplore.EValues.MultipleTesting.Simes
import LMLExplore.Topology.Instances.ENNReal.Lemmas

/-!
# Positive regression dependence and the lemma of Blanchard and Roquain

P-values `p : ι → Ω → ℝ≥0∞` are positively regression dependent on a set `N` of hypotheses
(`ProbabilityTheory.IsPRDS`) when, for every `i ∈ N` and every measurable upper set `D` of vectors
of p-values, the conditional probability `P (p ∈ D ∣ p i ≤ s)` is nondecreasing in `s` [Goe26,
(11)]. This is the weak form of the condition of [BY01], conditioning on `p i ≤ s` rather than on
`p i = s`. The sets `D` are upper sets, as in [BY01; BR08], so that `{x | f x ≤ t}` qualifies for
every coordinatewise nonincreasing `f`; [Goe26, (11)] in v2 writes "decreasing sets" instead, a
degenerate condition: taking `D = {x | x i ≤ s}`, it forces each `p i`, `i ∈ N`, to be almost
surely constant under a probability measure (hence at least `1` for a p-variable), so that the
lemma of Blanchard and Roquain holds trivially under it, and it is not the condition of [BY01;
BR08]. P-values that are all nondecreasing functions of one statistic are PRDS on every set of
hypotheses (`ProbabilityTheory.isPRDS_of_monotone`), and PRDS passes to subsets of hypotheses
(`ProbabilityTheory.IsPRDS.mono`).

Under PRDS, a p-variable `p i` with `i ∈ N` earns an e-value against every coordinatewise
nonincreasing threshold `f`: `𝔼[𝟙{p i ≤ f p} / f p] ≤ 1`, the lemma of Blanchard and Roquain
[BR08; Goe26, Theorem 5] (`ProbabilityTheory.IsPRDS.lintegral_indicator_le_inv_le_one`). Its
two-variable form (`ProbabilityTheory.IsPVar.lintegral_indicator_le_inv_le_one`) asks of a
p-variable `U` and a variable `V` only that `P (V ≤ t ∣ U ≤ s)` be nondecreasing in `s`.

Two consequences follow. Averaging these e-values over a set `S` of hypotheses, against thresholds
`a #S p` that depend on the size of `S`, gives the threshold statistics
(`ProbabilityTheory.thresholdECollection`), which form an e-collection when the thresholds are
measurable and nonincreasing (`ProbabilityTheory.isECollection_thresholdECollection`) [Goe26,
Theorem 8, for any such thresholds], whose e-closure controls the false discovery rate by the
e-Closure Principle; this is the construction of closed BH, which picks particular thresholds.
And the Benjamini–Hochberg procedure, e-BH applied to `p⁻¹`, has false discovery rate at most
`α * #N / K` when the p-values are PRDS on the true nulls `N` [BY01, Theorem 1.2]
(`ProbabilityTheory.IsPRDS.lintegral_fdp_eBH_inv_le`), the case of the threshold `α * #R / K`,
with `R` the rejection set, that the condition of [Goe26, Remark 9] isolates.

## Main definitions

* `ProbabilityTheory.IsPRDS p P N`: the p-values `p` are PRDS on the hypotheses `N` under `P`.
* `ProbabilityTheory.thresholdECollection p a`: the threshold statistics of the thresholds `a`,
  the candidate e-collection of [Goe26, (9)].

## Main statements

* `ProbabilityTheory.IsPVar.lintegral_indicator_le_inv_le_one`: the lemma of Blanchard and
  Roquain for a p-variable `U` and a variable `V` that depends positively on it.
* `ProbabilityTheory.isPRDS_of_monotone`: nondecreasing functions of one statistic are PRDS.
* `ProbabilityTheory.IsPRDS.lintegral_indicator_le_inv_le_one`: the lemma of Blanchard and
  Roquain [Goe26, Theorem 5].
* `ProbabilityTheory.IsPRDS.sum_lintegral_indicator_le_inv_le_card`: summed over the hypotheses
  of `N`, these e-values have expectations summing to at most `#N`.
* `ProbabilityTheory.isECollection_thresholdECollection`: under PRDS, the threshold statistics of
  measurable nonincreasing thresholds form an e-collection [Goe26, Theorem 8].
* `ProbabilityTheory.IsPRDS.lintegral_fdp_eBH_inv_le`: the false discovery rate of BH under PRDS
  is at most `α * #N / K` [BY01, Theorem 1.2].

## Implementation notes

The lemma of Blanchard and Roquain is proved for every distribution of `V`, with no
discretization: on the geometric grid `ρ ^ j`, `j : ℤ`, for `ρ > 1`, the expectation is at most
`ρ` times the sum of the increments of the nondecreasing ratios
`P (V ≤ ρ ^ j, U ≤ ρ ^ j) / P (U ≤ ρ ^ j)`, which telescopes to at most `ρ`; then `ρ` decreases
to `1`.

## References

* [BR08] G. Blanchard and É. Roquain, *Two simple sufficient conditions for FDR control*,
  Electron. J. Stat. 2 (2008).
* [BY01] Y. Benjamini and D. Yekutieli, *The control of the false discovery rate in multiple
  testing under dependency*, Ann. Statist. 29 (2001).
* [Goe26] J. Goeman, *A uniform improvement of the Benjamini–Hochberg procedure via e-Closure*,
  arXiv:2606.01854v2.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {U V : Ω → ℝ≥0∞}

section TwoVariables

/-- The conditional probability `P (V ≤ t ∣ U ≤ t)`, as the ratio
`P (V ≤ t, U ≤ t) / P (U ≤ t)`, which is `0` when `P (U ≤ t) = 0`. -/
private noncomputable def condRatio (P : Measure Ω) (U V : Ω → ℝ≥0∞) (t : ℝ≥0∞) : ℝ≥0∞ :=
  P ({ω | V ω ≤ t} ∩ {ω | U ω ≤ t}) / P {ω | U ω ≤ t}

variable {a b : ℝ≥0∞}

private lemma condRatio_le_one : condRatio P U V a ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono Set.inter_subset_right)

/-- The ratio at `b` recovers the joint probability. -/
private lemma condRatio_mul (hb : P {ω | U ω ≤ b} ≠ ∞) :
    condRatio P U V b * P {ω | U ω ≤ b} = P ({ω | V ω ≤ b} ∩ {ω | U ω ≤ b}) := by
  by_cases h0 : P {ω | U ω ≤ b} = 0
  · rw [h0, mul_zero, eq_comm, ← nonpos_iff_eq_zero, ← h0]
    exact measure_mono Set.inter_subset_right
  · exact ENNReal.div_mul_cancel h0 hb

/-- The weak positive dependence of `V` on `U`, at the level `a` and the times `a ≤ b`, bounds
`P (V ≤ a, U ≤ b)` below by the ratio at `a` times `P (U ≤ b)`. -/
private lemma condRatio_mul_le (ha : P {ω | U ω ≤ a} ≠ ∞)
    (hUV : P ({ω | V ω ≤ a} ∩ {ω | U ω ≤ a}) * P {ω | U ω ≤ b} ≤
      P ({ω | V ω ≤ a} ∩ {ω | U ω ≤ b}) * P {ω | U ω ≤ a}) :
    condRatio P U V a * P {ω | U ω ≤ b} ≤ P ({ω | V ω ≤ a} ∩ {ω | U ω ≤ b}) := by
  by_cases h0 : P {ω | U ω ≤ a} = 0
  · have : P ({ω | V ω ≤ a} ∩ {ω | U ω ≤ a}) = 0 :=
      le_antisymm (h0 ▸ measure_mono Set.inter_subset_right) zero_le
    simp [condRatio, this]
  · rw [condRatio, div_eq_mul_inv, mul_right_comm]
    calc P ({ω | V ω ≤ a} ∩ {ω | U ω ≤ a}) * P {ω | U ω ≤ b} * (P {ω | U ω ≤ a})⁻¹
        ≤ P ({ω | V ω ≤ a} ∩ {ω | U ω ≤ b}) * P {ω | U ω ≤ a} * (P {ω | U ω ≤ a})⁻¹ := by
          gcongr
      _ = P ({ω | V ω ≤ a} ∩ {ω | U ω ≤ b}) := by
          rw [mul_assoc, ENNReal.mul_inv_cancel h0 ha, mul_one]

/-- The ratio is nondecreasing under the weak positive dependence of `V` on `U`. -/
private lemma condRatio_le_condRatio (ha : P {ω | U ω ≤ a} ≠ ∞) (hb : P {ω | U ω ≤ b} ≠ ∞)
    (hab : a ≤ b)
    (hUV : P ({ω | V ω ≤ a} ∩ {ω | U ω ≤ a}) * P {ω | U ω ≤ b} ≤
      P ({ω | V ω ≤ a} ∩ {ω | U ω ≤ b}) * P {ω | U ω ≤ a}) :
    condRatio P U V a ≤ condRatio P U V b := by
  by_cases h0 : P {ω | U ω ≤ b} = 0
  · have : P ({ω | V ω ≤ a} ∩ {ω | U ω ≤ a}) = 0 := le_antisymm
      ((measure_mono Set.inter_subset_right).trans (h0 ▸ measure_mono fun ω (h : U ω ≤ a) ↦
        h.trans hab)) zero_le
    simp [condRatio, this]
  · refine (ENNReal.mul_le_mul_iff_left h0 hb).1 ?_
    rw [condRatio_mul hb]
    exact (condRatio_mul_le ha hUV).trans
      (measure_mono (Set.inter_subset_inter_left _ fun ω (h : V ω ≤ a) ↦ h.trans hab))

/-- The probability that `V` lies in `(a, b]` and `U` below `b` is at most the increment of the
ratio between `a` and `b`, times `P (U ≤ b)`. -/
private lemma measure_diff_inter_le (hU : Measurable U) (hV : Measurable V)
    (ha : P {ω | U ω ≤ a} ≠ ∞) (hb : P {ω | U ω ≤ b} ≠ ∞) (hab : a ≤ b)
    (hUV : P ({ω | V ω ≤ a} ∩ {ω | U ω ≤ a}) * P {ω | U ω ≤ b} ≤
      P ({ω | V ω ≤ a} ∩ {ω | U ω ≤ b}) * P {ω | U ω ≤ a}) :
    P (({ω | V ω ≤ b} \ {ω | V ω ≤ a}) ∩ {ω | U ω ≤ b}) ≤
      (condRatio P U V b - condRatio P U V a) * P {ω | U ω ≤ b} := by
  have hsub : {ω | V ω ≤ a} ∩ {ω | U ω ≤ b} ⊆ {ω | V ω ≤ b} ∩ {ω | U ω ≤ b} :=
    Set.inter_subset_inter_left _ fun ω (h : V ω ≤ a) ↦ h.trans hab
  have hm : MeasurableSet ({ω | V ω ≤ a} ∩ {ω | U ω ≤ b}) :=
    (measurableSet_le hV measurable_const).inter (measurableSet_le hU measurable_const)
  rw [Set.inter_sdiff_distrib_right, measure_sdiff hsub hm.nullMeasurableSet
    (ne_top_of_le_ne_top hb (measure_mono Set.inter_subset_right)), ENNReal.sub_mul fun _ _ ↦ hb,
    condRatio_mul hb]
  exact tsub_le_tsub_left (condRatio_mul_le ha hUV) _

/-- On the geometric grid of ratio `ρ`, the event where `V` lies in `(ρ ^ j, ρ ^ (j + 1)]` and `U`
below `ρ ^ (j + 1)`, weighted by `1 / ρ ^ j`, has mass at most `ρ` times the increment of the
ratio between `ρ ^ j` and `ρ ^ (j + 1)`, when `U` is a p-variable. -/
private lemma inv_zpow_mul_measure_le (hU : IsPVar U {P}) (hV : Measurable V) {ρ : ℝ≥0∞}
    (hρ : 1 < ρ) (hρ' : ρ ≠ ∞) (j : ℤ)
    (hUV : P ({ω | V ω ≤ ρ ^ j} ∩ {ω | U ω ≤ ρ ^ j}) * P {ω | U ω ≤ ρ ^ (j + 1)} ≤
      P ({ω | V ω ≤ ρ ^ j} ∩ {ω | U ω ≤ ρ ^ (j + 1)}) * P {ω | U ω ≤ ρ ^ j}) :
    (ρ ^ j)⁻¹ * P (({ω | V ω ≤ ρ ^ (j + 1)} \ {ω | V ω ≤ ρ ^ j}) ∩ {ω | U ω ≤ ρ ^ (j + 1)}) ≤
      (condRatio P U V (ρ ^ (j + 1)) - condRatio P U V (ρ ^ j)) * ρ := by
  have hρ0 : ρ ≠ 0 := (zero_lt_one.trans hρ).ne'
  have hwtop (k : ℤ) : ρ ^ k ≠ ∞ := ENNReal.zpow_ne_top hρ0 hρ' k
  have hq (k : ℤ) : P {ω | U ω ≤ ρ ^ k} ≠ ∞ :=
    ne_top_of_le_ne_top (hwtop k) (hU.measure_le_le P rfl _)
  calc (ρ ^ j)⁻¹ * P (({ω | V ω ≤ ρ ^ (j + 1)} \ {ω | V ω ≤ ρ ^ j}) ∩ {ω | U ω ≤ ρ ^ (j + 1)})
      ≤ (ρ ^ j)⁻¹ * ((condRatio P U V (ρ ^ (j + 1)) - condRatio P U V (ρ ^ j)) * ρ ^ (j + 1)) := by
        gcongr
        exact (measure_diff_inter_le hU.measurable hV (hq j) (hq (j + 1))
          (ENNReal.zpow_le_of_le hρ.le (by omega)) hUV).trans
          (by gcongr; exact hU.measure_le_le P rfl _)
    _ = (condRatio P U V (ρ ^ (j + 1)) - condRatio P U V (ρ ^ j)) * ρ * ((ρ ^ j)⁻¹ * ρ ^ j) := by
        rw [ENNReal.zpow_add hρ0 hρ', zpow_one]
        ring
    _ = (condRatio P U V (ρ ^ (j + 1)) - condRatio P U V (ρ ^ j)) * ρ := by
        rw [ENNReal.inv_mul_cancel (ENNReal.zpow_pos hρ0 hρ' j).ne' (hwtop j), mul_one]

/-- Where `U ≠ 0`, the e-value `𝟙{U ≤ V} / V` is at most the sum over `j : ℤ` of `1 / ρ ^ j` on
the events where `V` lies in `(ρ ^ j, ρ ^ (j + 1)]` and `U` below `ρ ^ (j + 1)`. -/
private lemma indicator_le_inv_le_tsum {ρ : ℝ≥0∞} (hρ : 1 < ρ) {ω : Ω} (hω : U ω ≠ 0) :
    {ω | U ω ≤ V ω}.indicator (fun ω ↦ (V ω)⁻¹) ω ≤ ∑' j : ℤ,
      (({ω | V ω ≤ ρ ^ (j + 1)} \ {ω | V ω ≤ ρ ^ j}) ∩ {ω | U ω ≤ ρ ^ (j + 1)}).indicator
        (fun _ ↦ (ρ ^ j)⁻¹) ω := by
  by_cases h : U ω ≤ V ω
  swap
  · simp [h]
  rcases eq_or_ne (V ω) ∞ with hVt | hVt
  · simp [hVt]
  obtain ⟨j, hj1, hj2⟩ :=
    ENNReal.exists_mem_Ioc_zpow ((pos_iff_ne_zero.2 hω).trans_le h).ne' hVt hρ
  refine le_trans ?_ (le_tsum _ j)
  rw [Set.indicator_of_mem (s := {ω | U ω ≤ V ω}) h, Set.indicator_of_mem
    (s := ({ω | V ω ≤ ρ ^ (j + 1)} \ {ω | V ω ≤ ρ ^ j}) ∩ {ω | U ω ≤ ρ ^ (j + 1)})
    ⟨⟨hj2, not_le.2 hj1⟩, h.trans hj2⟩]
  exact ENNReal.inv_le_inv.2 hj1.le

/-- **The lemma of Blanchard and Roquain** for two variables [BR08], the form of [Goe26,
Theorem 5] for a single variable `V` in place of `f p`: if `U` is a p-variable for `P` and `V`
depends positively on `U`, in the sense that `P (V ≤ t ∣ U ≤ s)` is nondecreasing in `s` for
every `t`, then `𝔼[𝟙{U ≤ V} / V] ≤ 1`. The variable `V` may take the values `0` and `∞`, with
`1 / 0 = ∞` and `1 / ∞ = 0`. -/
theorem IsPVar.lintegral_indicator_le_inv_le_one (hU : IsPVar U {P}) (hV : Measurable V)
    (hUV : ∀ t ⦃s s'⦄, s ≤ s' → P ({ω | V ω ≤ t} ∩ {ω | U ω ≤ s}) * P {ω | U ω ≤ s'} ≤
      P ({ω | V ω ≤ t} ∩ {ω | U ω ≤ s'}) * P {ω | U ω ≤ s}) :
    ∫⁻ ω, {ω | U ω ≤ V ω}.indicator (fun ω ↦ (V ω)⁻¹) ω ∂P ≤ 1 := by
  -- It suffices to prove the bound `ρ` for every `1 < ρ < ∞`.
  suffices h : ∀ ρ : ℝ≥0∞, 1 < ρ → ρ ≠ ∞ →
      ∫⁻ ω, {ω | U ω ≤ V ω}.indicator (fun ω ↦ (V ω)⁻¹) ω ∂P ≤ ρ by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ h _ ?_ (by finiteness)
    exact ENNReal.lt_add_right ENNReal.one_ne_top (by simpa using hε.ne')
  intro ρ hρ hρ'
  have hρ0 : ρ ≠ 0 := (zero_lt_one.trans hρ).ne'
  have hwtop (j : ℤ) : ρ ^ j ≠ ∞ := ENNReal.zpow_ne_top hρ0 hρ' j
  have hq (j : ℤ) : P {ω | U ω ≤ ρ ^ j} ≠ ∞ :=
    ne_top_of_le_ne_top (hwtop j) (hU.measure_le_le P rfl _)
  have hstep (j : ℤ) : ρ ^ j ≤ ρ ^ (j + 1) := ENNReal.zpow_le_of_le hρ.le (by omega)
  -- On the grid of the powers `ρ ^ j`, the ratios `c j` are nondecreasing and at most `1`.
  set c : ℤ → ℝ≥0∞ := fun j ↦ condRatio P U V (ρ ^ j)
  have hc : Monotone c := monotone_int_of_le_succ fun j ↦
    condRatio_le_condRatio (hq j) (hq (j + 1)) (hstep j) (hUV _ (hstep j))
  -- The events where `V` lies in `(ρ ^ j, ρ ^ (j + 1)]` and `U` below `ρ ^ (j + 1)`.
  set A : ℤ → Set Ω := fun j ↦
    ({ω | V ω ≤ ρ ^ (j + 1)} \ {ω | V ω ≤ ρ ^ j}) ∩ {ω | U ω ≤ ρ ^ (j + 1)}
  have hA (j : ℤ) : MeasurableSet (A j) :=
    ((measurableSet_le hV measurable_const).diff (measurableSet_le hV measurable_const)).inter
      (measurableSet_le hU.measurable measurable_const)
  -- Almost surely `U ≠ 0`, and then `𝟙{U ≤ V} / V ≤ ∑ j, 𝟙_{A j} / ρ ^ j`.
  have hU0 : ∀ᵐ ω ∂P, U ω ≠ 0 := by
    have : P {ω | U ω ≤ 0} = 0 := le_antisymm (hU.measure_le_le P rfl 0) zero_le
    rw [ae_iff]
    simpa using this
  have hpt : ∀ᵐ ω ∂P, {ω | U ω ≤ V ω}.indicator (fun ω ↦ (V ω)⁻¹) ω ≤
      ∑' j, (A j).indicator (fun _ ↦ (ρ ^ j)⁻¹) ω := by
    filter_upwards [hU0] with ω hω using indicator_le_inv_le_tsum hρ hω
  calc ∫⁻ ω, {ω | U ω ≤ V ω}.indicator (fun ω ↦ (V ω)⁻¹) ω ∂P
      ≤ ∫⁻ ω, ∑' j, (A j).indicator (fun _ ↦ (ρ ^ j)⁻¹) ω ∂P := lintegral_mono_ae hpt
    _ = ∑' j, (ρ ^ j)⁻¹ * P (A j) := by
        rw [lintegral_tsum fun j ↦ (aemeasurable_const.indicator (hA j))]
        exact tsum_congr fun j ↦ lintegral_indicator_const (hA j) _
    _ ≤ ∑' j, (c (j + 1) - c j) * ρ := tsum_le_tsum fun j ↦
        inv_zpow_mul_measure_le hU hV hρ hρ' j (hUV _ (hstep j))
    _ = (∑' j, (c (j + 1) - c j)) * ρ := ENNReal.tsum_mul_right
    _ ≤ 1 * ρ := by
        gcongr
        exact (ENNReal.tsum_sub_le_iSup hc).trans (iSup_le fun j ↦ condRatio_le_one)
    _ = ρ := one_mul ρ

end TwoVariables

section PRDS

variable {p : ι → Ω → ℝ≥0∞} {N : Set ι} {i : ι}

/-- **Positive regression dependence on a subset** (PRDS), in its weak form [Goe26, (11)]: for
every `i ∈ N` and every measurable upper set `D` of vectors of p-values, the conditional
probability `P (p ∈ D ∣ p i ≤ s)` is nondecreasing in `s`. It is stated without division, as
`P (p ∈ D, p i ≤ s) * P (p i ≤ t) ≤ P (p ∈ D, p i ≤ t) * P (p i ≤ s)` for `s ≤ t`. The sets `D`
are upper sets, as in [BY01; BR08]; [Goe26, (11)] in v2 writes "decreasing sets", a degenerate
condition that forces each `p i`, `i ∈ N`, to be almost surely constant under a probability
measure (hence at least `1` for a p-variable), and is not the condition of [BY01; BR08]. -/
def IsPRDS (p : ι → Ω → ℝ≥0∞) (P : Measure Ω) (N : Set ι) : Prop :=
  ∀ i ∈ N, ∀ D : Set (ι → ℝ≥0∞), MeasurableSet D → IsUpperSet D → ∀ ⦃s t : ℝ≥0∞⦄, s ≤ t →
    P ({ω | (p · ω) ∈ D} ∩ {ω | p i ω ≤ s}) * P {ω | p i ω ≤ t} ≤
      P ({ω | (p · ω) ∈ D} ∩ {ω | p i ω ≤ t}) * P {ω | p i ω ≤ s}

theorem isPRDS_iff : IsPRDS p P N ↔
    ∀ i ∈ N, ∀ D : Set (ι → ℝ≥0∞), MeasurableSet D → IsUpperSet D → ∀ ⦃s t : ℝ≥0∞⦄, s ≤ t →
      P ({ω | (p · ω) ∈ D} ∩ {ω | p i ω ≤ s}) * P {ω | p i ω ≤ t} ≤
        P ({ω | (p · ω) ∈ D} ∩ {ω | p i ω ≤ t}) * P {ω | p i ω ≤ s} :=
  Iff.rfl

/-- PRDS on a set of hypotheses passes to its subsets. -/
theorem IsPRDS.mono {N' : Set ι} (h : IsPRDS p P N) (hN : N' ⊆ N) : IsPRDS p P N' :=
  fun i hi ↦ h i (hN hi)

/-- Every family of p-values is PRDS on the empty set of hypotheses. -/
@[simp]
theorem isPRDS_empty : IsPRDS p P ∅ :=
  fun _ hi ↦ absurd hi (Set.notMem_empty _)

/-- **Nondecreasing functions of one statistic are PRDS**: p-values `p j = g j ∘ X` that are all
nondecreasing functions of one statistic `X` with values in a linear order are PRDS on every set
`N` of hypotheses whose p-values are measurable, under every measure. -/
theorem isPRDS_of_monotone {α : Type*} [LinearOrder α] {X : Ω → α} {g : ι → α → ℝ≥0∞}
    (hg : ∀ j, Monotone (g j)) (hm : ∀ i ∈ N, Measurable fun ω ↦ g i (X ω)) :
    IsPRDS (fun j ω ↦ g j (X ω)) P N := by
  intro i hi D _ hD s t hst
  set A := {ω | (fun j ↦ g j (X ω)) ∈ D}
  set Bs := {ω | g i (X ω) ≤ s}
  set Bt := {ω | g i (X ω) ≤ t}
  by_cases hA : (A ∩ Bs).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.1 hA]
    simp
  -- Above a point of `A ∩ Bs`, the points of `Bt \ Bs` are in the upper set `A`.
  obtain ⟨ω₀, hω₀A, hω₀B⟩ := hA
  have hsub : Bt \ Bs ⊆ A := by
    rintro ω ⟨-, hωs⟩
    have hlt : X ω₀ < X ω := lt_of_not_ge fun h ↦ hωs ((hg i h).trans hω₀B)
    exact hD (fun j ↦ hg j hlt.le) hω₀A
  have hBs : MeasurableSet Bs := measurableSet_le (hm i hi) measurable_const
  have hBt : P Bt ≤ P Bs + P (Bt \ Bs) := by
    rw [add_comm]
    exact (measure_mono (Set.subset_sdiff_union Bt Bs)).trans (measure_union_le _ _)
  have hABt : P (A ∩ Bs) + P (Bt \ Bs) ≤ P (A ∩ Bt) := by
    rw [← measure_union (Set.disjoint_sdiff_right.mono_left Set.inter_subset_right)
      ((measurableSet_le (hm i hi) measurable_const).diff hBs)]
    exact measure_mono (Set.union_subset (Set.inter_subset_inter_right _ fun ω h ↦ h.trans hst)
      (Set.subset_inter hsub Set.sdiff_subset))
  calc P (A ∩ Bs) * P Bt ≤ P (A ∩ Bs) * (P Bs + P (Bt \ Bs)) := by gcongr
    _ ≤ P (A ∩ Bs) * P Bs + P Bs * P (Bt \ Bs) := by
        rw [mul_add]
        have : P (A ∩ Bs) ≤ P Bs := measure_mono Set.inter_subset_right
        gcongr
    _ = (P (A ∩ Bs) + P (Bt \ Bs)) * P Bs := by ring
    _ ≤ P (A ∩ Bt) * P Bs := by gcongr

/-- **The lemma of Blanchard and Roquain** [Goe26, Theorem 5]: if the p-values `p` are PRDS on a
set `N` containing `i`, and `p i` is a p-variable for `P`, then for every measurable coordinatewise
nonincreasing threshold `f`, `𝔼[𝟙{p i ≤ f p} / f p] ≤ 1`. -/
theorem IsPRDS.lintegral_indicator_le_inv_le_one (h : IsPRDS p P N) (hi : i ∈ N)
    (hpi : IsPVar (p i) {P}) (hp : ∀ j, Measurable (p j)) {f : (ι → ℝ≥0∞) → ℝ≥0∞}
    (hf : Antitone f) (hfm : Measurable f) :
    ∫⁻ ω, {ω | p i ω ≤ f (p · ω)}.indicator (fun ω ↦ (f (p · ω))⁻¹) ω ∂P ≤ 1 :=
  hpi.lintegral_indicator_le_inv_le_one (hfm.comp (measurable_pi_iff.2 hp)) fun t _ _ hss' ↦
    h i hi {x | f x ≤ t} (measurableSet_le hfm measurable_const)
      (fun _ _ hxy hx ↦ (hf hxy).trans hx) hss'

/-- **The e-values of Blanchard and Roquain sum to at most the number of hypotheses**: if the
p-values `p` are PRDS on a finite set `S` of hypotheses whose p-values are p-variables for `P`,
then for every measurable coordinatewise nonincreasing threshold `f`,
`∑ i ∈ S, 𝔼[𝟙{p i ≤ f p} / f p] ≤ #S`. -/
theorem IsPRDS.sum_lintegral_indicator_le_inv_le_card {S : Finset ι} (h : IsPRDS p P S)
    (hpS : ∀ i ∈ S, IsPVar (p i) {P}) (hp : ∀ j, Measurable (p j)) {f : (ι → ℝ≥0∞) → ℝ≥0∞}
    (hf : Antitone f) (hfm : Measurable f) :
    ∑ i ∈ S, ∫⁻ ω, {ω | p i ω ≤ f (p · ω)}.indicator (fun ω ↦ (f (p · ω))⁻¹) ω ∂P ≤ #S :=
  (sum_le_card_nsmul _ _ 1 fun i hi ↦
    h.lintegral_indicator_le_inv_le_one (Finset.mem_coe.2 hi) (hpS i hi) hp hf hfm).trans_eq
    (by simp)

end PRDS

/-- The e-value `𝟙{p i ≤ f p} / f p` of a p-value against a threshold is measurable. -/
private lemma measurable_indicator_le_inv {p : ι → Ω → ℝ≥0∞} (hp : ∀ j, Measurable (p j))
    {f : (ι → ℝ≥0∞) → ℝ≥0∞} (hf : Measurable f) (i : ι) :
    Measurable fun ω ↦ {ω | p i ω ≤ f (p · ω)}.indicator (fun ω ↦ (f (p · ω))⁻¹) ω :=
  (hf.comp (measurable_pi_iff.2 hp)).inv.indicator
    (measurableSet_le (hp i) (hf.comp (measurable_pi_iff.2 hp)))

section ECollection

variable {p : ι → Ω → ℝ≥0∞} {a : ℕ → (ι → ℝ≥0∞) → ℝ≥0∞}

/-- The **threshold statistics** of the thresholds `a`, the candidate e-collection of the form of
[Goe26, (9)]: for a set `S` of hypotheses, the average over `i ∈ S` of the statistics
`𝟙{p i ≤ a #S p} / a #S p` of the p-values against the threshold `a #S p`, which depends on the
size of `S` and on all the p-values, with `1 / 0 = ∞`. The statistic of the empty set is `0`.
They form an e-collection under the hypotheses of
`ProbabilityTheory.isECollection_thresholdECollection`. -/
noncomputable def thresholdECollection (p : ι → Ω → ℝ≥0∞) (a : ℕ → (ι → ℝ≥0∞) → ℝ≥0∞)
    (S : Finset ι) (ω : Ω) : ℝ≥0∞ :=
  (#S : ℝ≥0∞)⁻¹ * ∑ i ∈ S, {ω | p i ω ≤ a #S (p · ω)}.indicator (fun ω ↦ (a #S (p · ω))⁻¹) ω

theorem thresholdECollection_def (p : ι → Ω → ℝ≥0∞) (a : ℕ → (ι → ℝ≥0∞) → ℝ≥0∞)
    (S : Finset ι) (ω : Ω) : thresholdECollection p a S ω =
      (#S : ℝ≥0∞)⁻¹ * ∑ i ∈ S,
        {ω | p i ω ≤ a #S (p · ω)}.indicator (fun ω ↦ (a #S (p · ω))⁻¹) ω :=
  (rfl)

@[simp]
theorem thresholdECollection_empty (p : ι → Ω → ℝ≥0∞) (a : ℕ → (ι → ℝ≥0∞) → ℝ≥0∞) :
    thresholdECollection p a ∅ = 0 := by
  ext ω
  simp [thresholdECollection_def]

theorem measurable_thresholdECollection (hp : ∀ j, Measurable (p j))
    (ha : ∀ s, Measurable (a s)) (S : Finset ι) : Measurable (thresholdECollection p a S) :=
  measurable_const.mul (Finset.measurable_sum _ fun i _ ↦ measurable_indicator_le_inv hp (ha _) i)

/-- **The threshold statistics of nonincreasing thresholds form an e-collection under PRDS**
[Goe26, Theorem 8]: if each `p i` is a p-variable for `H i`, the p-values are PRDS on the true
nulls under every probability measure, and each threshold `a s` is measurable, and coordinatewise
nonincreasing for the sizes `s` of sets of hypotheses, then `thresholdECollection p a` is an
e-collection. -/
theorem isECollection_thresholdECollection [Fintype ι] {H : ι → Set (Measure Ω)}
    (hp : ∀ i, IsPVar (p i) (H i)) (ha : ∀ s ≤ Fintype.card ι, Antitone (a s))
    (ham : ∀ s, Measurable (a s))
    (hPRDS : ∀ (P : Measure Ω) [IsProbabilityMeasure P], IsPRDS p P (trueNulls H P)) :
    IsECollection (thresholdECollection p a) H where
  measurable := measurable_thresholdECollection (fun j ↦ (hp j).measurable) ham
  apply_empty := thresholdECollection_empty p a
  lintegral_le_one P _ := by
    set N := trueNulls H P
    have hg := measurable_indicator_le_inv (fun j ↦ (hp j).measurable) (ham #N)
    calc ∫⁻ ω, thresholdECollection p a N ω ∂P
        = (#N : ℝ≥0∞)⁻¹ * ∑ i ∈ N, ∫⁻ ω,
            {ω | p i ω ≤ a #N (p · ω)}.indicator (fun ω ↦ (a #N (p · ω))⁻¹) ω ∂P := by
          simp_rw [thresholdECollection_def]
          rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ ↦ hg i),
            lintegral_finsetSum _ fun i _ ↦ hg i]
      _ ≤ (#N : ℝ≥0∞)⁻¹ * #N := by
          gcongr
          exact (hPRDS P).sum_lintegral_indicator_le_inv_le_card
            (fun i hi ↦ (hp i).anti_set (Set.singleton_subset_iff.2 (mem_trueNulls.1 hi)))
            (fun j ↦ (hp j).measurable) (ha _ (card_le_univ N)) (ham _)
      _ ≤ 1 := ENNReal.inv_mul_le_one _

end ECollection

section BH

variable [Fintype ι] {p : ι → Ω → ℝ≥0∞} {N : Finset ι} {α : ℝ≥0∞}

/-- The threshold `α * #R / K` of BH at the p-values `x`, with `R` the BH rejection set and `K` the
number of hypotheses. It is coordinatewise nonincreasing. -/
private noncomputable def bhThreshold (α : ℝ≥0∞) (x : ι → ℝ≥0∞) : ℝ≥0∞ :=
  α * #(eBH (fun i ↦ (x i)⁻¹) α) / Fintype.card ι

private lemma antitone_bhThreshold (α : ℝ≥0∞) : Antitone (bhThreshold (ι := ι) α) :=
  fun x y hxy ↦ by
    have : eBH (fun i ↦ (y i)⁻¹) α ⊆ eBH (fun i ↦ (x i)⁻¹) α :=
      eBH_mono le_rfl fun i ↦ ENNReal.inv_le_inv.2 (hxy i)
    simp only [bhThreshold]
    gcongr

private lemma measurable_bhThreshold (α : ℝ≥0∞) : Measurable (bhThreshold (ι := ι) α) :=
  (measurable_const.mul ((measurable_card_eBH α).comp
    (measurable_pi_iff.2 fun i ↦ (measurable_pi_apply i).inv))).div_const _

/-- BH is self-consistent for the e-values `𝟙{p i ≤ f p} / f p` of the p-values against the BH
threshold `f`: each rejected p-value is at most `f p`, and `α * #R / f p = K`. -/
private lemma isSelfConsistent_indicator_bhThreshold (hα₀ : α ≠ 0) (hα : α ≠ ∞)
    (x : ι → ℝ≥0∞) :
    IsSelfConsistent (fun i ↦ {y : ι → ℝ≥0∞ | y i ≤ bhThreshold α y}.indicator
      (fun y ↦ (bhThreshold α y)⁻¹) x) α (eBH (fun i ↦ (x i)⁻¹) α) := by
  refine isSelfConsistent_iff.2 fun i hiR ↦ ?_
  have : Nonempty ι := ⟨i⟩
  have hK0 : (Fintype.card ι : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hR0 : α * #(eBH (fun i ↦ (x i)⁻¹) α) ≠ 0 :=
    mul_ne_zero hα₀ (Nat.cast_ne_zero.2 (card_ne_zero_of_mem hiR))
  have hle : x i ≤ bhThreshold α x := by
    rw [bhThreshold, ENNReal.le_div_iff_mul_le (Or.inl hK0) (Or.inl (ENNReal.natCast_ne_top _)),
      mul_comm]
    exact isSelfConsistent_eBH.card_mul_le hiR
  -- The rejected e-value is `K / (α * #R)`, exactly the self-consistency threshold.
  rw [Set.indicator_of_mem (s := {y : ι → ℝ≥0∞ | y i ≤ bhThreshold α y}) hle, bhThreshold,
    ENNReal.inv_div (Or.inl (ENNReal.natCast_ne_top _)) (Or.inr hR0),
    ENNReal.mul_div_cancel hR0 (ENNReal.mul_ne_top hα (ENNReal.natCast_ne_top _))]

variable [DecidableEq ι]

/-- **The Benjamini–Hochberg procedure under PRDS** [BY01, Theorem 1.2; Goe26, Remark 9]: if the
p-values are PRDS on a set `N` of hypotheses whose p-values are p-variables for `P`, then the
false discovery rate of BH at level `α`, e-BH applied to `p⁻¹`, is at most `α * #N / K`, with `K`
the number of hypotheses. -/
theorem IsPRDS.lintegral_fdp_eBH_inv_le (h : IsPRDS p P N) (hpN : ∀ i ∈ N, IsPVar (p i) {P})
    (hp : ∀ j, Measurable (p j)) (α : ℝ≥0∞) :
    ∫⁻ ω, fdp N (eBH (fun i ↦ (p i ω)⁻¹) α) ∂P ≤ α * #N / Fintype.card ι := by
  rcases N.eq_empty_or_nonempty with rfl | hN
  · simp
  rcases eq_or_ne α 0 with rfl | hα₀
  · simp [eBH_zero]
  rcases eq_or_ne α ∞ with rfl | hα
  · have : (#N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hN.card_pos.ne'
    simp [ENNReal.top_mul this, ENNReal.top_div]
  refine (lintegral_fdp_le_of_isSelfConsistent
    (fun i ↦ (measurable_indicator_le_inv hp (measurable_bhThreshold α) i).aemeasurable)
    (fun ω ↦ isSelfConsistent_indicator_bhThreshold hα₀ hα (p · ω)) N).trans ?_
  gcongr
  exact h.sum_lintegral_indicator_le_inv_le_card hpN hp (antitone_bhThreshold α)
    (measurable_bhThreshold α)

end BH

end ProbabilityTheory
