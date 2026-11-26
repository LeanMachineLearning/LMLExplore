/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Process.HittingTime
import LMLExplore.Basic.ENNReal.BigOperators
import LMLExplore.MeasureTheory.Integral.Bochner.Basic
import LMLExplore.MeasureTheory.Integral.Lebesgue.ENat
import LMLExplore.Probability.Independence.Wald
import LMLExplore.Probability.Process.Filtration
import LMLExplore.Probability.Process.Stopping
import LMLExplore.Topology.Algebra.InfiniteSum.NatInt

/-!
# The expected first passage time of a random walk with positive drift

Let `X 0, X 1, …` be independent, identically distributed real increments with mean
`D = 𝔼[X 0] ∈ (0, ∞]`, meaning that the negative part `X⁻` has a finite mean and the positive part
`X⁺` a larger one, possibly infinite: `D = 𝔼[X⁺] - 𝔼[X⁻]` in `ℝ≥0∞`. The partial sums
`∑ j < k, X j` first reach a level `b` after `N b` steps, the hitting time `hittingAfter` of
`[b, ∞)`. The **elementary renewal theorem for first passage times** [Gut09, Chapter 3] states
`𝔼[N b] / b → 1 / D` as `b → ∞`, with `1 / ∞ = 0`: for integrable increments,
`𝔼[N b] ~ b / D`. Tau Ceti's elementary renewal theorem
(`MeasureTheory.Measure.tendsto_renewalFunction_div`) is the case of nonnegative increments; here
the increments may take both signs, and the walk may go down before it goes up.

The two bounds come from Wald's argument.
* **Lower bound.** Wald's identity in `ℝ≥0∞`, for a stopping time `τ` of the filtration of the past
  increments and a measurable `g ≥ 0`, gives `𝔼[∑ j < τ, g (X j)] = 𝔼[g (X 0)] 𝔼[τ]`, with no
  integrability hypothesis (`ProbabilityTheory.iIndepFun.lintegral_tsum_indicator_lt_eq_mul`).
  Applied to `X⁺` and `X⁻` at `τ = N b`, where the walk is at least `b`,
  it gives `b ≤ D 𝔼[N b]`.
* **Upper bound.** Truncating the increments at a level `c` does not let the walk reach `b` earlier,
  and the truncated increments, bounded above by `c`, reach `b` after at most `(b + c) / D_c` steps
  in expectation, where `D_c = 𝔼[min (X 0) c]`
  (`ProbabilityTheory.iIndepFun.lintegral_hittingAfter_sum_le_of_le_integral_min`). The means `D_c`
  tend to `D` as `c → ∞` (`MeasureTheory.tendsto_ofReal_integral_min`).

## Main statements

* `ProbabilityTheory.iIndepFun.ofReal_le_mul_lintegral_hittingAfter_sum`: Wald's lower bound
  `b ≤ D 𝔼[N b]`.
* `ProbabilityTheory.iIndepFun.lintegral_hittingAfter_sum_lt_top`: `𝔼[N b] < ∞` under a positive
  drift.
* `ProbabilityTheory.iIndepFun.tendsto_lintegral_hittingAfter_sum_div`: the elementary renewal
  theorem `𝔼[N b] / b → 1 / D` for first passage times, in `ℝ≥0∞`, with an infinite mean allowed.
* `ProbabilityTheory.iIndepFun.isEquivalent_toReal_lintegral_hittingAfter_sum`: `𝔼[N b] ~ b / D` for
  integrable increments with mean `D > 0`.

## References

* [Gut09] A. Gut, *Stopped Random Walks: Limit Theorems and Applications*, 2nd edition, Springer,
  2009, Chapter 3.
-/

public section

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- **Wald's lower bound on the expected first passage time.** Let `X j` be independent real
random variables whose positive parts have the common mean `p` and whose negative parts have the
common mean `q < p`, so that the drift is `p - q > 0`. The first time `N b` at which the partial
sums `∑ j < k, X j` reach `b` satisfies `b ≤ (p - q) 𝔼[N b]`. -/
theorem iIndepFun.ofReal_le_mul_lintegral_hittingAfter_sum (hX : iIndepFun X μ)
    (hXm : ∀ j, Measurable (X j)) {p q : ℝ≥0∞}
    (hp : ∀ j, ∫⁻ ω, ENNReal.ofReal (X j ω) ∂μ = p)
    (hq : ∀ j, ∫⁻ ω, ENNReal.ofReal (-X j ω) ∂μ = q) (hqp : q < p) (b : ℝ) :
    ENNReal.ofReal b ≤ (p - q) * ∫⁻ ω, ENat.toENNReal
        (hittingAfter (fun k ω ↦ ∑ j ∈ Finset.range k, X j ω) (Set.Ici b) 0 ω) ∂μ := by
  have := hX.isProbabilityMeasure
  set S : ℕ → Ω → ℝ := fun k ω ↦ ∑ j ∈ Finset.range k, X j ω
  set N : Ω → ℕ∞ := hittingAfter S (Set.Ici b) 0
  have hN : IsStoppingTime (Filtration.naturalLT X hXm) N := by
    refine Adapted.isStoppingTime_hittingAfter (fun k ↦ ?_) measurableSet_Ici
    exact (Finset.measurable_sum (m := Filtration.naturalLT X hXm k) _ fun i hi ↦
      Filtration.measurable_naturalLT hXm (Finset.mem_range.1 hi))
  rcases le_or_gt b 0 with hb | hb
  · simp [ENNReal.ofReal_of_nonpos hb]
  -- if `𝔼[N b] = ∞` there is nothing to prove; otherwise `N b` is almost surely finite
  by_cases htop : ∫⁻ ω, (N ω : ℝ≥0∞) ∂μ = ∞
  · rw [htop, ENNReal.mul_top (tsub_pos_iff_lt.2 hqp).ne']
    exact le_top
  have hfin : ∀ᵐ ω ∂μ, N ω ≠ ⊤ :=
    ae_ne_top_of_lintegral_toENNReal_ne_top hN.measurable_enat.aemeasurable htop
  set F : (ℝ → ℝ≥0∞) → Ω → ℝ≥0∞ := fun f ω ↦
    ∑' j : ℕ, {ω | (j : ℕ∞) < N ω}.indicator (fun ω ↦ f (X j ω)) ω
  have hF (f : ℝ → ℝ≥0∞) (ω : Ω) (n : ℕ) (hn : N ω = n) :
      F f ω = ∑ j ∈ Finset.range n, f (X j ω) := by
    simpa only [F, Set.indicator, Set.mem_ofPred_eq, hn, ENat.toNat_natCast] using
      LMLExplore.tsum_indicator_natCast_lt_eq_sum_range (n := N ω) (by simp [hn])
        fun j ↦ f (X j ω)
  -- on the event that the walk reaches `b`, its positive steps exceed `b` plus its negative steps
  have hpt : ∀ᵐ ω ∂μ, ENNReal.ofReal b + F (fun x ↦ ENNReal.ofReal (-x)) ω ≤
      F ENNReal.ofReal ω := by
    filter_upwards [hfin] with ω hω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hω
    have hSn : b ≤ ∑ j ∈ Finset.range n, X j ω := by
      have := hittingAfter_mem_set_of_ne_top hω
      simp only [N, ← hn] at this
      simpa using this
    rw [hF (fun x ↦ ENNReal.ofReal (-x)) ω n hn.symm, hF ENNReal.ofReal ω n hn.symm,
      ← ENNReal.ofReal_sum_add_sum_ofReal_neg (hb.le.trans hSn)]
    gcongr
  -- Wald's identity for the positive and the negative parts of the steps
  have hwald (f : ℝ → ℝ≥0∞) (hf : Measurable f) {m : ℝ≥0∞}
      (hm : ∀ j, ∫⁻ ω, f (X j ω) ∂μ = m) :
      ∫⁻ ω, F f ω ∂μ = m * ∫⁻ ω, (N ω : ℝ≥0∞) ∂μ :=
    hX.lintegral_tsum_indicator_lt_eq_mul hXm hN hf hm
  have hsum : ENNReal.ofReal b + q * ∫⁻ ω, (N ω : ℝ≥0∞) ∂μ ≤
      p * ∫⁻ ω, (N ω : ℝ≥0∞) ∂μ := by
    rw [← hwald _ ENNReal.measurable_ofReal hp,
      ← hwald _ (ENNReal.measurable_ofReal.comp measurable_neg) hq]
    calc ENNReal.ofReal b + ∫⁻ ω, F (fun x ↦ ENNReal.ofReal (-x)) ω ∂μ
    _ = ∫⁻ ω, ENNReal.ofReal b + F (fun x ↦ ENNReal.ofReal (-x)) ω ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ ω, F ENNReal.ofReal ω ∂μ := lintegral_mono_ae hpt
  rw [ENNReal.sub_mul fun _ _ ↦ htop]
  exact ENNReal.le_sub_of_add_le_right (ENNReal.mul_ne_top hqp.ne_top htop) hsum

/-- Under a positive drift, the first passage time has a finite mean: if `X j` are independent,
identically distributed real random variables whose negative part has a mean smaller than that of
their positive part, the first time the partial sums reach `b` has a finite expectation. -/
theorem iIndepFun.lintegral_hittingAfter_sum_lt_top (hX : iIndepFun X μ)
    (hXm : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hqp : ∫⁻ ω, ENNReal.ofReal (-X 0 ω) ∂μ < ∫⁻ ω, ENNReal.ofReal (X 0 ω) ∂μ) (b : ℝ) :
    ∫⁻ ω, ENat.toENNReal
      (hittingAfter (fun k ω ↦ ∑ j ∈ Finset.range k, X j ω) (Set.Ici b) 0 ω) ∂μ < ∞ := by
  have := hX.isProbabilityMeasure
  obtain ⟨n, hn⟩ := ((tendsto_order.1 (tendsto_ofReal_integral_min (hXm 0).aemeasurable)).1 0
    (tsub_pos_iff_lt.2 hqp)).exists
  refine (hX.lintegral_hittingAfter_sum_le_of_le_integral_min hXm (ENNReal.ofReal_pos.1 hn)
    (fun j ↦ ((hident j).comp (measurable_id.min measurable_const)).integral_eq.ge) b).trans_lt
    ENNReal.ofReal_lt_top

/-- **The elementary renewal theorem for first passage times.** Let `X j` be independent,
identically distributed real random variables whose negative part has a mean `q` smaller than the
mean `p` of their positive part, which may be infinite: the drift `D = p - q` lies in `(0, ∞]`.
The first time `N b` at which the partial sums `∑ j < k, X j` reach `b` satisfies
`𝔼[N b] / b → 1 / D` as `b → ∞`, with `1 / ∞ = 0` [Gut09, Chapter 3]. -/
theorem iIndepFun.tendsto_lintegral_hittingAfter_sum_div (hX : iIndepFun X μ)
    (hXm : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hqp : ∫⁻ ω, ENNReal.ofReal (-X 0 ω) ∂μ < ∫⁻ ω, ENNReal.ofReal (X 0 ω) ∂μ) :
    Tendsto (fun b : ℝ ↦ (∫⁻ ω, ENat.toENNReal
        (hittingAfter (fun k ω ↦ ∑ j ∈ Finset.range k, X j ω) (Set.Ici b) 0 ω) ∂μ) /
          ENNReal.ofReal b) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (X 0 ω) ∂μ - ∫⁻ ω, ENNReal.ofReal (-X 0 ω) ∂μ)⁻¹) := by
  have := hX.isProbabilityMeasure
  set p := ∫⁻ ω, ENNReal.ofReal (X 0 ω) ∂μ
  set q := ∫⁻ ω, ENNReal.ofReal (-X 0 ω) ∂μ
  set T : ℝ → ℝ≥0∞ := fun b ↦ ∫⁻ ω, ENat.toENNReal
    (hittingAfter (fun k ω ↦ ∑ j ∈ Finset.range k, X j ω) (Set.Ici b) 0 ω) ∂μ
  have hp (j : ℕ) : ∫⁻ ω, ENNReal.ofReal (X j ω) ∂μ = p :=
    ((hident j).comp ENNReal.measurable_ofReal).lintegral_eq
  have hq (j : ℕ) : ∫⁻ ω, ENNReal.ofReal (-X j ω) ∂μ = q :=
    ((hident j).comp (ENNReal.measurable_ofReal.comp measurable_neg)).lintegral_eq
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · -- the lower bound `1 / D ≤ 𝔼[N b] / b`, from Wald's identity
    filter_upwards [eventually_gt_atTop 0] with b hb
    refine ha.trans_le ((ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hb).ne')
      (Or.inl ENNReal.ofReal_ne_top)).2 ?_)
    rw [mul_comm, ← div_eq_mul_inv]
    refine ENNReal.div_le_of_le_mul ?_
    rw [mul_comm]
    exact hX.ofReal_le_mul_lintegral_hittingAfter_sum hXm hp hq hqp b
  · -- the upper bound, from Wald's bound for the increments truncated at a large level `n`, whose
    -- mean `D` exceeds `a⁻¹`
    obtain ⟨n, hDn⟩ := ((tendsto_order.1 (tendsto_ofReal_integral_min (hXm 0).aemeasurable)).1
      a⁻¹ (ENNReal.inv_lt_iff_inv_lt.1 ha)).exists
    set D : ℝ := ∫ ω, min (X 0 ω) n ∂μ
    have hDpos : 0 < D := ENNReal.ofReal_pos.1 (zero_le.trans_lt hDn)
    have hlim : Tendsto (fun b : ℝ ↦ ENNReal.ofReal ((1 + n / b) / D)) atTop
        (𝓝 (ENNReal.ofReal D⁻¹)) := by
      have h : Tendsto (fun b : ℝ ↦ (1 + n / b) / D) atTop (𝓝 ((1 + 0) / D)) :=
        ((tendsto_const_nhds.div_atTop tendsto_id).const_add 1).div_const _
      rw [add_zero, one_div] at h
      exact ENNReal.tendsto_ofReal h
    have hlt : ENNReal.ofReal D⁻¹ < a := by
      rw [ENNReal.ofReal_inv_of_pos hDpos]
      exact ENNReal.inv_lt_iff_inv_lt.1 hDn
    filter_upwards [(tendsto_order.1 hlim).2 a hlt, eventually_gt_atTop 0] with b hb hb0
    refine lt_of_le_of_lt ?_ hb
    calc T b / ENNReal.ofReal b
    _ ≤ ENNReal.ofReal ((b + n) / D) / ENNReal.ofReal b := by
      gcongr
      exact hX.lintegral_hittingAfter_sum_le_of_le_integral_min hXm hDpos
        (fun j ↦ ((hident j).comp (measurable_id.min measurable_const)).integral_eq.ge) b
    _ = ENNReal.ofReal ((1 + n / b) / D) := by
      rw [← ENNReal.ofReal_div_of_pos hb0]
      congr 1
      field_simp

/-- **The elementary renewal theorem for first passage times**, for integrable increments: if
`X j` are independent, identically distributed and integrable real random variables with mean
`D > 0`, the first time `N b` at which the partial sums `∑ j < k, X j` reach `b` has
`𝔼[N b] ~ b / D` as `b → ∞` [Gut09, Chapter 3]. The expectation is finite
(`ProbabilityTheory.iIndepFun.lintegral_hittingAfter_sum_lt_top`), so that `toReal` loses
nothing. -/
theorem iIndepFun.isEquivalent_toReal_lintegral_hittingAfter_sum (hX : iIndepFun X μ)
    (hXm : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hint : Integrable (X 0) μ) (hpos : 0 < ∫ ω, X 0 ω ∂μ) :
    (fun b : ℝ ↦ (∫⁻ ω, ENat.toENNReal
        (hittingAfter (fun k ω ↦ ∑ j ∈ Finset.range k, X j ω) (Set.Ici b) 0 ω) ∂μ).toReal)
      ~[atTop] fun b ↦ b / ∫ ω, X 0 ω ∂μ := by
  have := hX.isProbabilityMeasure
  set D := ∫ ω, X 0 ω ∂μ
  -- the drift `𝔼[X⁺] - 𝔼[X⁻]` in `ℝ≥0∞` is the mean `D`
  have hq : ∫⁻ ω, ENNReal.ofReal (-X 0 ω) ∂μ ≠ ∞ := hint.neg.lintegral_lt_top.ne
  have hp : ∫⁻ ω, ENNReal.ofReal (X 0 ω) ∂μ ≠ ∞ := hint.lintegral_lt_top.ne
  have hmean : ENNReal.ofReal D =
      ∫⁻ ω, ENNReal.ofReal (X 0 ω) ∂μ - ∫⁻ ω, ENNReal.ofReal (-X 0 ω) ∂μ := by
    simp only [D]
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint,
      ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hp,
      ENNReal.ofReal_toReal hq]
  have hqp : ∫⁻ ω, ENNReal.ofReal (-X 0 ω) ∂μ < ∫⁻ ω, ENNReal.ofReal (X 0 ω) ∂μ :=
    tsub_pos_iff_lt.1 (hmean ▸ ENNReal.ofReal_pos.2 hpos)
  have h := hX.tendsto_lintegral_hittingAfter_sum_div hXm hident hqp
  rw [← hmean, ← ENNReal.ofReal_inv_of_pos hpos] at h
  have hreal := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp h
  rw [ENNReal.toReal_ofReal (inv_nonneg.2 hpos.le)] at hreal
  refine isEquivalent_of_tendsto_one ?_
  have h1 := hreal.mul_const D
  rw [inv_mul_cancel₀ hpos.ne'] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  rw [Function.comp_apply, ENNReal.toReal_div, ENNReal.toReal_ofReal hb.le, Pi.div_apply]
  field_simp

end ProbabilityTheory
