/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Defs
public import TauCeti.Probability.LargeDeviations.Basic
public import LMLExplore.Data.EReal.Basic
public import LMLExplore.Data.EReal.Inv
public import LMLExplore.Topology.Semicontinuity.ENNReal

/-!
# Large deviation principles

Tau Ceti's `TauCeti.Probability.HasLDP l ε μ I` is the large deviation principle of a family of
measures `μ i` along a filter `l`, with speed `ε` and rate function `I : X → [0, ∞]`: `I` is lower
semicontinuous, `-inf_G I ≤ liminf ε i log μ i G` for every open set `G` and
`limsup ε i log μ i F ≤ -inf_F I` for every closed set `F`. A sequence of measures `P n` satisfies
the principle with speed `1 / n` when `HasLDP atTop (fun n ↦ (n : ℝ≥0)⁻¹) P I`. The rate function
is *good* (`TauCeti.Probability.IsGoodRateFunction`) if its sublevel sets `{x | I x ≤ c}`, `c`
finite, are compact. The logarithms are `EReal`-valued, `log 0 = ⊥`.

This file adds to Tau Ceti's definitions. The bounds extend to every set `s`, through its interior
and its closure, `-inf_{x ∈ int s} I(x) ≤ liminf ε i log μ i s` and
`limsup ε i log μ i s ≤ -inf_{x ∈ cl s} I(x)`: this is the definition of A. Dembo and
O. Zeitouni, where the measure of a set that is not measurable is its outer measure.

At the speed `1 / n`, the bounds are usually proved from exponential bounds on the probabilities:
an upper bound `P n s ≤ C exp (-(n r))` for every `r < c` gives
`limsup_n (1 / n) log P n s ≤ -c`, and a lower bound `C exp (-(n r)) ≤ P n s` for every `r > c`
gives `-c ≤ liminf_n (1 / n) log P n s`. The lower bound of the principle reduces to the
neighbourhoods of single points.

## Main statements

* `LMLExplore.limsup_inv_mul_log_le_neg_of_le_mul_exp`: exponential upper bounds at every rate
  `r < c` give `limsup_n (1 / n) log u n ≤ -c`.
* `LMLExplore.neg_le_liminf_inv_mul_log_of_mul_exp_le`: exponential lower bounds at every rate
  `r > c` give `-c ≤ liminf_n (1 / n) log u n`.
* `TauCeti.Probability.HasLDP.of_isClosed_of_mem_nhds`: the large deviation principle from the
  upper bound on the closed sets and the lower bound on the neighbourhoods of each point.
* `TauCeti.Probability.HasLDP.neg_iInf_interior_le_liminf`,
  `TauCeti.Probability.HasLDP.limsup_le_neg_iInf_closure`: the bounds of the principle for every
  set, through its interior and its closure.
* `TauCeti.Probability.HasLDP.eventually_measure_le_exp`,
  `TauCeti.Probability.HasLDP.eventually_exp_le_measure`: the converse at the speed `1 / n`,
  exponential bounds on closed sets and on neighbourhoods of points, from the principle.
* `TauCeti.Probability.HasLDP.exists_eventually_measure_norm_ge_le_exp`: exponential tightness on a
  normed group, from a principle at the speed `1 / n` with a good rate function.
* `TauCeti.Probability.HasLDP.comp_of_tendsto_div`: a change of time. If `P n` satisfies the
  principle at the speed `1 / n` with rate `I` and `m n / n → w > 0`, then `P (m n)` satisfies it
  at the speed `1 / n` with rate `w I`: `m n` samples taken at the time `n` deviate at the rate
  `w I` per unit of time.
* `LMLExplore.isGoodRateFunction_sum_mul`: positive weighted sums of good rate functions on the
  coordinates of a finite product are good.
* `TauCeti.Probability.IsGoodRateFunction.ofReal_mul`: a positive multiple of a good rate function
  is good.

## References

* [DZ98] A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed.,
  Springer, 1998, Section 1.2.

The exponential-bound criteria are adapted from the formalization
Degenne2023Existence (`github.com/RemyDegenne/Degenne2023Existence`, file
`Degenne2023Existence/ForLMLExplore/Probability/LargeDeviations/Basic.lean`, commit
`5afa57772d415c17cfd89de287fb004ca51d8fb3`, by Rémy Degenne, Apache 2.0) of R. Degenne, *On the
existence of a complexity in fixed budget bandit identification*, COLT 2023.
-/

public section

open MeasureTheory Filter Topology
open TauCeti.Probability (HasLDP IsGoodRateFunction)

open scoped ENNReal NNReal

namespace LMLExplore

/-! ### Exponential bounds -/

/-- The logarithm of `exp (-(n r))` is `-r n`, as an extended real. -/
private lemma log_ofReal_exp (n : ℕ) (r : ℝ) :
    ENNReal.log (ENNReal.ofReal (Real.exp (-(n * r)))) = ((-r : ℝ) : EReal) * n := by
  rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp, ← EReal.coe_natCast,
    ← EReal.coe_mul, neg_mul, mul_comm]

/-- `log C / n - r` tends to `-r`, as an extended real. -/
private lemma tendsto_coe_div_sub (C r : ℝ) :
    Tendsto (fun n : ℕ ↦ ((C / n - r : ℝ) : EReal)) atTop (𝓝 (-(r : EReal))) := by
  rw [← EReal.coe_neg]
  refine EReal.tendsto_coe.2 ?_
  simpa using (tendsto_const_div_atTop_nhds_zero_nat C).sub_const r

/-- The logarithm of `C exp (-(n r))`, divided by `n`, is `log C / n - r`, for a finite `C > 0`. -/
private lemma log_mul_exp_div {C : ℝ≥0∞} (hC0 : C ≠ 0) (hC : C ≠ ⊤) {n : ℕ} (hn : 1 ≤ n)
    (r : ℝ) :
    ENNReal.log (C * ENNReal.ofReal (Real.exp (-(n * r)))) / n =
      ((Real.log C.toReal / n - r : ℝ) : EReal) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [ENNReal.log_mul_add, ← ENNReal.ofReal_toReal hC,
    ENNReal.log_ofReal_of_pos (ENNReal.toReal_pos hC0 hC), log_ofReal_exp, ENNReal.toReal_ofReal
    ENNReal.toReal_nonneg, ← EReal.coe_natCast, ← EReal.coe_mul, ← EReal.coe_add,
    ← EReal.coe_div]
  congr 1
  field_simp
  ring

/-- **Exponential upper bounds give the upper bound of a large deviation principle.** If for every
real `r < c` there is a finite `C` with `u n ≤ C exp (-(n r))` eventually, then
`limsup_n (1 / n) log u n ≤ -c`. -/
lemma limsup_inv_mul_log_le_neg_of_le_mul_exp {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ r : ℝ, (r : EReal) < c → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ᶠ n : ℕ in atTop, u n ≤ C * ENNReal.ofReal (Real.exp (-(n * r)))) :
    limsup (fun n : ℕ ↦ (((n⁻¹ : ℝ≥0) : ℝ) : EReal) * ENNReal.log (u n)) atTop ≤
      -(c : EReal) := by
  simp_rw [EReal.coe_nnreal_inv_natCast_mul]
  rw [EReal.le_neg]
  refine EReal.ge_of_forall_gt_iff_ge.1 fun r hr ↦ ?_
  rw [EReal.le_neg]
  obtain ⟨C, hC, hu⟩ := h r hr
  have hC0 : max C 1 ≠ 0 := (zero_lt_one.trans_le (le_max_right C 1)).ne'
  have hCtop : max C 1 ≠ ⊤ := max_ne_top hC ENNReal.one_ne_top
  rw [← (tendsto_coe_div_sub (Real.log (max C 1).toReal) r).limsup_eq]
  refine limsup_le_limsup ?_
  filter_upwards [hu, eventually_ge_atTop 1] with n hn hn1
  rw [← log_mul_exp_div hC0 hCtop hn1]
  refine EReal.div_le_div_right_of_nonneg (by exact_mod_cast n.cast_nonneg) ?_
  exact ENNReal.log_monotone (hn.trans (by gcongr; exact le_max_left _ _))

/-- **Exponential lower bounds give the lower bound of a large deviation principle.** If for every
real `r > c` there is a nonzero `C` with `C exp (-(n r)) ≤ u n` eventually, then
`-c ≤ liminf_n (1 / n) log u n`. -/
lemma neg_le_liminf_inv_mul_log_of_mul_exp_le {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ r : ℝ, (c : EReal) < r → ∃ C : ℝ≥0∞, C ≠ 0 ∧
      ∀ᶠ n : ℕ in atTop, C * ENNReal.ofReal (Real.exp (-(n * r))) ≤ u n) :
    -(c : EReal) ≤ liminf (fun n : ℕ ↦ (((n⁻¹ : ℝ≥0) : ℝ) : EReal) * ENNReal.log (u n)) atTop := by
  simp_rw [EReal.coe_nnreal_inv_natCast_mul]
  rw [EReal.neg_le]
  refine EReal.le_of_forall_lt_iff_le.1 fun r hr ↦ ?_
  rw [EReal.neg_le]
  obtain ⟨C, hC, hu⟩ := h r hr
  have hC0 : min C 1 ≠ 0 := by simp [hC]
  have hCtop : min C 1 ≠ ⊤ := ((min_le_right C 1).trans_lt ENNReal.one_lt_top).ne
  rw [← (tendsto_coe_div_sub (Real.log (min C 1).toReal) r).liminf_eq]
  refine liminf_le_liminf ?_
  filter_upwards [hu, eventually_ge_atTop 1] with n hn hn1
  rw [← log_mul_exp_div hC0 hCtop hn1]
  refine EReal.div_le_div_right_of_nonneg (by exact_mod_cast n.cast_nonneg) ?_
  refine ENNReal.log_monotone (le_trans ?_ hn)
  gcongr
  exact min_le_left _ _

/-! ### Exponential bounds from the bounds of a large deviation principle -/

/-- **Exponential upper bounds from the upper bound of a large deviation principle.** If
`limsup_n (1 / n) log u n ≤ -c`, then `u n ≤ exp (-(n r))` eventually, for every real `r < c`. -/
lemma eventually_le_exp_of_limsup_inv_mul_log_le {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : limsup (fun n : ℕ ↦ (((n⁻¹ : ℝ≥0) : ℝ) : EReal) * ENNReal.log (u n)) atTop ≤
      -(c : EReal)) {r : ℝ} (hr : (r : EReal) < c) :
    ∀ᶠ n : ℕ in atTop, u n ≤ ENNReal.ofReal (Real.exp (-(n * r))) := by
  simp_rw [EReal.coe_nnreal_inv_natCast_mul] at h
  have h' : limsup (fun n : ℕ ↦ ENNReal.log (u n) / n) atTop < ((-r : ℝ) : EReal) := by
    rw [EReal.coe_neg]
    exact h.trans_lt (EReal.neg_lt_neg_iff.2 hr)
  filter_upwards [eventually_lt_of_limsup_lt h', eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : EReal) < n := by exact_mod_cast hn1
  rw [EReal.div_lt_iff hn0 (EReal.natCast_ne_top n), ← log_ofReal_exp,
    ENNReal.log_strictMono.lt_iff_lt] at hn
  exact hn.le

/-- **Exponential lower bounds from the lower bound of a large deviation principle.** If
`-c ≤ liminf_n (1 / n) log u n`, then `exp (-(n r)) ≤ u n` eventually, for every real `r > c`. -/
lemma eventually_exp_le_of_neg_le_liminf_inv_mul_log {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : -(c : EReal) ≤
      liminf (fun n : ℕ ↦ (((n⁻¹ : ℝ≥0) : ℝ) : EReal) * ENNReal.log (u n)) atTop) {r : ℝ}
    (hr : (c : EReal) < r) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (-(n * r))) ≤ u n := by
  simp_rw [EReal.coe_nnreal_inv_natCast_mul] at h
  have h' : ((-r : ℝ) : EReal) < liminf (fun n : ℕ ↦ ENNReal.log (u n) / n) atTop := by
    rw [EReal.coe_neg]
    exact (EReal.neg_lt_neg_iff.2 hr).trans_le h
  filter_upwards [eventually_lt_of_lt_liminf h', eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : EReal) < n := by exact_mod_cast hn1
  rw [EReal.lt_div_iff hn0 (EReal.natCast_ne_top n), ← log_ofReal_exp,
    ENNReal.log_strictMono.lt_iff_lt] at hn
  exact hn.le

end LMLExplore

namespace TauCeti.Probability.HasLDP

variable {ι X : Type*} [TopologicalSpace X] {mX : MeasurableSpace X} {l : Filter ι}
  {ε : ι → ℝ≥0} {μ : ι → Measure X} {I : X → ℝ≥0∞}

/-! ### Reduction to closed sets and to neighbourhoods of points -/

/-- **The large deviation principle from the bounds on closed sets and neighbourhoods.** If `I` is
lower semicontinuous, `limsup ε i log μ i s ≤ -inf_s I` for every closed set `s`, and
`-I(x) ≤ liminf ε i log μ i s` for every neighbourhood `s` of every point `x`, then the measures
`μ i` satisfy the large deviation principle with speed `ε` and rate function `I`. -/
theorem of_isClosed_of_mem_nhds (hI : LowerSemicontinuous I)
    (h_upper : ∀ s, IsClosed s →
      limsup (fun i ↦ ((ε i : ℝ) : EReal) * ENNReal.log (μ i s)) l ≤
        -(((⨅ x ∈ s, I x : ℝ≥0∞)) : EReal))
    (h_lower : ∀ x, ∀ s ∈ 𝓝 x,
      -(I x : EReal) ≤ liminf (fun i ↦ ((ε i : ℝ) : EReal) * ENNReal.log (μ i s)) l) :
    HasLDP l ε μ I where
  lowerSemicontinuous := hI
  lower_bound s hs := by
    rw [EReal.neg_le]
    set L := liminf (fun i ↦ ((ε i : ℝ) : EReal) * ENNReal.log (μ i s)) l
    rcases le_or_gt (-L) 0 with hL | hL
    · exact hL.trans (EReal.coe_ennreal_nonneg _)
    rw [← EReal.coe_toENNReal hL.le, EReal.coe_ennreal_le_coe_ennreal_iff]
    refine le_iInf₂ fun x hx ↦ ?_
    rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_toENNReal hL.le, EReal.neg_le]
    exact h_lower x s (hs.mem_nhds hx)
  upper_bound := h_upper

omit [TopologicalSpace X] in
/-- The speed `ε` multiplies the logarithms of the measures monotonically: `ε i log μ i s` is
monotone in `s`. -/
private lemma mul_log_measure_mono (ε : ι → ℝ≥0) (μ : ι → Measure X) (i : ι) {s t : Set X}
    (hst : s ⊆ t) :
    ((ε i : ℝ) : EReal) * ENNReal.log (μ i s) ≤ ((ε i : ℝ) : EReal) * ENNReal.log (μ i t) :=
  mul_le_mul_of_nonneg_left (ENNReal.log_monotone (measure_mono hst))
    (EReal.coe_nonneg.2 (ε i).coe_nonneg)

/-- **The lower bound of a large deviation principle for every set**, through its interior:
`-inf_{x ∈ int s} I(x) ≤ liminf ε i log μ i s`. -/
theorem neg_iInf_interior_le_liminf (h : HasLDP l ε μ I) (s : Set X) :
    -(((⨅ x ∈ interior s, I x : ℝ≥0∞)) : EReal) ≤
      liminf (fun i ↦ ((ε i : ℝ) : EReal) * ENNReal.log (μ i s)) l := by
  refine (h.lower_bound _ isOpen_interior).trans (liminf_le_liminf ?_)
  exact Eventually.of_forall fun i ↦ mul_log_measure_mono ε μ i interior_subset

/-- **The upper bound of a large deviation principle for every set**, through its closure:
`limsup ε i log μ i s ≤ -inf_{x ∈ cl s} I(x)`. -/
theorem limsup_le_neg_iInf_closure (h : HasLDP l ε μ I) (s : Set X) :
    limsup (fun i ↦ ((ε i : ℝ) : EReal) * ENNReal.log (μ i s)) l ≤
      -(((⨅ x ∈ closure s, I x : ℝ≥0∞)) : EReal) := by
  refine le_trans (limsup_le_limsup ?_) (h.upper_bound _ isClosed_closure)
  exact Eventually.of_forall fun i ↦ mul_log_measure_mono ε μ i subset_closure

/-! ### Exponential bounds from a principle at the speed `1 / n` -/

/-- Under a large deviation principle at the speed `1 / n`, the measure of a closed set `s` is
eventually at most `exp (-(n r))`, for every real `r` below the infimum of the rate function on
`s`. -/
theorem eventually_measure_le_exp {P : ℕ → Measure X}
    (h : HasLDP atTop (fun n : ℕ ↦ (n : ℝ≥0)⁻¹) P I) {s : Set X} (hs : IsClosed s) {r : ℝ}
    (hr : (r : EReal) < ⨅ x ∈ s, I x) :
    ∀ᶠ n : ℕ in atTop, P n s ≤ ENNReal.ofReal (Real.exp (-(n * r))) :=
  LMLExplore.eventually_le_exp_of_limsup_inv_mul_log_le (h.upper_bound s hs) hr

/-- Under a large deviation principle at the speed `1 / n`, the measure of a neighbourhood `s` of
`x` is eventually at least `exp (-(n r))`, for every real `r > I x`. -/
theorem eventually_exp_le_measure {P : ℕ → Measure X}
    (h : HasLDP atTop (fun n : ℕ ↦ (n : ℝ≥0)⁻¹) P I) {x : X} {s : Set X} (hs : s ∈ 𝓝 x) {r : ℝ}
    (hr : (I x : EReal) < r) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (-(n * r))) ≤ P n s := by
  refine LMLExplore.eventually_exp_le_of_neg_le_liminf_inv_mul_log
    ((EReal.neg_le_neg_iff.2 ?_).trans (h.neg_iInf_interior_le_liminf s)) hr
  exact EReal.coe_ennreal_le_coe_ennreal_iff.2 (iInf₂_le x (mem_interior_iff_mem_nhds.2 hs))

/-- **Exponential tightness.** Under a large deviation principle at the speed `1 / n` with a good
rate function on a normed group, for every real `r` there is a radius `M` such that the measure of
`{x | M ≤ ‖x‖}` is eventually at most `exp (-(n r))`. -/
theorem exists_eventually_measure_norm_ge_le_exp {E : Type*} [SeminormedAddCommGroup E]
    {mE : MeasurableSpace E} {P : ℕ → Measure E} {I : E → ℝ≥0∞}
    (h : HasLDP atTop (fun n : ℕ ↦ (n : ℝ≥0)⁻¹) P I) (hI : IsGoodRateFunction I) (r : ℝ) :
    ∃ M : ℝ, ∀ᶠ n : ℕ in atTop, P n {x | M ≤ ‖x‖} ≤ ENNReal.ofReal (Real.exp (-(n * r))) := by
  set c : ℝ≥0 := (max r 0 + 1).toNNReal with hc_def
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).1
    (hI.isCompact_sublevel c ENNReal.coe_ne_top).isBounded
  refine ⟨C + 1, h.eventually_measure_le_exp (isClosed_le continuous_const continuous_norm) ?_⟩
  have hc : (((c : ℝ≥0∞)) : EReal) = ((max r 0 + 1 : ℝ) : EReal) := by
    rw [hc_def, ENNReal.ofNNReal_toNNReal, EReal.coe_ennreal_ofReal,
      max_eq_left (by linarith [le_max_right r 0])]
  refine lt_of_lt_of_le (b := ((c : ℝ≥0∞) : EReal)) ?_ (EReal.coe_ennreal_le_coe_ennreal_iff.2
    (le_iInf₂ fun x hx ↦ ?_))
  · rw [hc, EReal.coe_lt_coe_iff]
    linarith [le_max_left r 0]
  · by_contra hlt
    have hx' := hC (show x ∈ {x | I x ≤ c} from (not_le.1 hlt).le)
    rw [Metric.mem_closedBall, dist_zero_right] at hx'
    simp only [Set.mem_ofPred_eq] at hx
    linarith

/-! ### A change of time -/

/-- **A change of time in a large deviation principle at the speed `1 / n`.** If the measures
`P n` satisfy the large deviation principle with speed `1 / n` and rate function `I`, and the
indices `m n` grow linearly, `m n / n → w` with `w > 0`, then the measures `P (m n)` satisfy the
large deviation principle with speed `1 / n` and rate function `w I`. For `P n` the law of a
statistic of `n` samples, the measures `P (m n)` are the laws of the statistic of a proportion
`w` of `n` samples. -/
theorem comp_of_tendsto_div {P : ℕ → Measure X}
    (h : HasLDP atTop (fun n : ℕ ↦ (n : ℝ≥0)⁻¹) P I) {m : ℕ → ℕ} {w : ℝ} (hw : 0 < w)
    (hm : Tendsto (fun n ↦ (m n : ℝ) / n) atTop (𝓝 w)) :
    HasLDP atTop (fun n : ℕ ↦ (n : ℝ≥0)⁻¹) (fun n ↦ P (m n))
      (fun x ↦ ENNReal.ofReal w * I x) := by
  have hm_top : Tendsto m atTop atTop := by
    refine tendsto_natCast_atTop_iff.1 <|
      (hm.pos_mul_atTop hw tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp
  -- For every real `r'`, `m n r'` is eventually above `n r` if `r < w r'`, and below it if
  -- `w r' < r`.
  have h_lt {r r' : ℝ} (hr : r < w * r') : ∀ᶠ n : ℕ in atTop, n * r ≤ m n * r' := by
    filter_upwards [(hm.mul_const r').eventually (eventually_gt_nhds hr),
      eventually_gt_atTop 0] with n hn hn0
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by exact_mod_cast hn0)] at hn
    linarith
  have h_gt {r r' : ℝ} (hr : w * r' < r) : ∀ᶠ n : ℕ in atTop, m n * r' ≤ n * r := by
    filter_upwards [(hm.mul_const r').eventually (eventually_lt_nhds hr),
      eventually_gt_atTop 0] with n hn hn0
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by exact_mod_cast hn0)] at hn
    linarith
  have hw0 : ENNReal.ofReal w ≠ 0 := (ENNReal.ofReal_pos.2 hw).ne'
  refine .of_isClosed_of_mem_nhds ?_ (fun F hF ↦ ?_) (fun x s hs ↦ ?_)
  · exact h.lowerSemicontinuous.ennreal_const_mul ENNReal.ofReal_ne_top
  · refine LMLExplore.limsup_inv_mul_log_le_neg_of_le_mul_exp fun r hr ↦
      ⟨1, ENNReal.one_ne_top, ?_⟩
    simp_rw [← ENNReal.mul_iInf_of_ne hw0 ENNReal.ofReal_ne_top] at hr
    obtain ⟨r', hr₁, hr₂⟩ := EReal.lt_iff_exists_real_btwn.1
      ((EReal.coe_lt_coe_ennreal_ofReal_mul_iff hw).1 hr)
    filter_upwards [hm_top.eventually (h.eventually_measure_le_exp hF hr₂),
      h_lt ((div_lt_iff₀' hw).1 (EReal.coe_lt_coe_iff.1 hr₁))] with n hn hn'
    rw [one_mul]
    exact hn.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith)))
  · refine LMLExplore.neg_le_liminf_inv_mul_log_of_mul_exp_le fun r hr ↦
      ⟨1, one_ne_zero, ?_⟩
    obtain ⟨r', hr₁, hr₂⟩ := EReal.lt_iff_exists_real_btwn.1
      ((EReal.coe_ennreal_ofReal_mul_lt_coe_iff hw).1 hr)
    filter_upwards [hm_top.eventually (h.eventually_exp_le_measure hs hr₁),
      h_gt ((lt_div_iff₀' hw).1 (EReal.coe_lt_coe_iff.1 hr₂))] with n hn hn'
    rw [one_mul]
    exact (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))).trans hn

end TauCeti.Probability.HasLDP

namespace LMLExplore

/-- **Weighted sums of good rate functions are good.** For good rate functions `I a` on spaces
`X a`, indexed by a finite type, and positive weights `w a`, the function
`x ↦ ∑ a, w a I a (x a)` on the product is a good rate function. -/
lemma isGoodRateFunction_sum_mul {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ a, TopologicalSpace (X a)] {I : ∀ a, X a → ℝ≥0∞} (hI : ∀ a, IsGoodRateFunction (I a))
    {w : ι → ℝ} (hw : ∀ a, 0 < w a) :
    IsGoodRateFunction fun x : (∀ a, X a) ↦ ∑ a, ENNReal.ofReal (w a) * I a (x a) := by
  have h_lsc : LowerSemicontinuous fun x : (∀ a, X a) ↦ ∑ a, ENNReal.ofReal (w a) * I a (x a) :=
    lowerSemicontinuous_sum fun a _ ↦
      ((hI a).lowerSemicontinuous.comp (continuous_apply a)).ennreal_const_mul ENNReal.ofReal_ne_top
  refine ⟨h_lsc, fun c hc ↦ ?_⟩
  lift c to ℝ≥0 using hc
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun a ↦
      (hI a).isCompact_sublevel ((c / (w a).toNNReal : ℝ≥0) : ℝ≥0∞) ENNReal.coe_ne_top)
    (h_lsc.isClosed_preimage _) fun x hx a _ ↦ ?_
  have hw0 : (w a).toNNReal ≠ 0 := by simpa using hw a
  have h_le : ENNReal.ofReal (w a) * I a (x a) ≤ c :=
    (Finset.single_le_sum (f := fun a ↦ ENNReal.ofReal (w a) * I a (x a))
      (fun _ _ ↦ zero_le) (Finset.mem_univ a)).trans hx
  simp only [Set.mem_ofPred_eq, ENNReal.coe_div hw0]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hw0)) (Or.inl ENNReal.coe_ne_top),
    mul_comm]
  exact h_le

end LMLExplore

namespace TauCeti.Probability.IsGoodRateFunction

/-- **Positive multiples of good rate functions are good.** For a good rate function `I` and
`w > 0`, the function `x ↦ w I x` is a good rate function. -/
lemma ofReal_mul {X : Type*} [TopologicalSpace X] {I : X → ℝ≥0∞} (hI : IsGoodRateFunction I)
    {w : ℝ} (hw : 0 < w) : IsGoodRateFunction fun x ↦ ENNReal.ofReal w * I x := by
  have hw0 : ENNReal.ofReal w ≠ 0 := (ENNReal.ofReal_pos.2 hw).ne'
  refine ⟨hI.lowerSemicontinuous.ennreal_const_mul ENNReal.ofReal_ne_top,
    fun c hc ↦ ?_⟩
  convert hI.isCompact_sublevel (c / ENNReal.ofReal w) (ENNReal.div_ne_top hc hw0) using 2
  ext x
  rw [ENNReal.le_div_iff_mul_le (Or.inl hw0) (Or.inl ENNReal.ofReal_ne_top), mul_comm]

end TauCeti.Probability.IsGoodRateFunction
