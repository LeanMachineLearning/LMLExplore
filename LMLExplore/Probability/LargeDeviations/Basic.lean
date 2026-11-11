/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.EReal.Inv
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Defs

/-!
# Large deviation principles

A sequence of measures `P n` on a topological space `X` satisfies the *large deviation principle*
(LDP) with speed `n` and rate function `I : X → [0, ∞]` if `I` is lower semicontinuous and, for
every set `s`,
`-inf_{x ∈ int s} I(x) ≤ liminf_n (1 / n) log P n s` and
`limsup_n (1 / n) log P n s ≤ -inf_{x ∈ cl s} I(x)`.
The rate function is *good* if its sublevel sets `{x | I x ≤ c}` are compact. The logarithms are
`EReal`-valued, `log 0 = ⊥`.

This is the definition of A. Dembo and O. Zeitouni, with the bounds stated for every set: the
measure of a set that is not measurable is its outer measure. When open sets are measurable
(`OpensMeasurableSpace X`, for example for the Borel σ-algebra), the bounds for every set follow
from the bounds for the measurable ones by monotonicity, since interiors are open and closures are
closed.

The bounds are usually proved from exponential bounds on the probabilities: an upper bound
`P n s ≤ C exp (-(n r))` for every `r < c` gives `limsup_n (1 / n) log P n s ≤ -c`, and a lower
bound `C exp (-(n r)) ≤ P n s` for every `r > c` gives `-c ≤ liminf_n (1 / n) log P n s`. The
lower bound of the principle reduces to the neighbourhoods of single points, and the upper bound
to the closed sets.

## Main definitions

* `LMLExplore.IsGoodRateFunction I`: `I` is lower semicontinuous with compact sublevel sets.
* `LMLExplore.IsLDP P I`: the sequence of measures `P` satisfies the large deviation principle with
  speed `n` and rate function `I`.

## Main statements

* `LMLExplore.limsup_log_div_le_neg_of_le_mul_exp`: exponential upper bounds at every rate `r < c`
  give `limsup_n (1 / n) log u n ≤ -c`.
* `LMLExplore.neg_le_liminf_log_div_of_mul_exp_le`: exponential lower bounds at every rate `r > c`
  give `-c ≤ liminf_n (1 / n) log u n`.
* `LMLExplore.IsLDP.of_isClosed_of_mem_nhds`: the large deviation principle from the upper bound on
  the closed sets and the lower bound on the neighbourhoods of each point.
* `LMLExplore.IsLDP.eventually_measure_le_exp`, `LMLExplore.IsLDP.eventually_exp_le_measure`: the
  converse, exponential bounds on closed sets and on neighbourhoods of points, from the principle.
* `LMLExplore.IsLDP.exists_eventually_measure_norm_ge_le_exp`: exponential tightness on a normed
  group, from a principle with a good rate function.
* `LMLExplore.isGoodRateFunction_sum_mul`: positive weighted sums of good rate functions on the
  coordinates of a finite product are good.

## References

* [DZ98] A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed.,
  Springer, 1998, Section 1.2.

The definitions and the exponential-bound criteria are adapted from the formalization
Degenne2023Existence (`github.com/RemyDegenne/Degenne2023Existence`, file
`Degenne2023Existence/ForLMLExplore/Probability/LargeDeviations/Basic.lean`, commit
`5afa57772d415c17cfd89de287fb004ca51d8fb3`, by Rémy Degenne, Apache 2.0) of R. Degenne, *On the
existence of a complexity in fixed budget bandit identification*, COLT 2023.
-/

public section

open MeasureTheory Filter Topology

open scoped ENNReal NNReal

namespace LMLExplore

variable {X : Type*} [TopologicalSpace X] {mX : MeasurableSpace X}

/-- The function `I : X → [0, ∞]` is a *good rate function*: it is lower semicontinuous and its
sublevel sets `{x | I x ≤ c}`, `c` finite, are compact [DZ98, Section 1.2]. -/
structure IsGoodRateFunction (I : X → ℝ≥0∞) : Prop where
  /-- A good rate function is lower semicontinuous. -/
  lowerSemicontinuous : LowerSemicontinuous I
  /-- The sublevel sets of a good rate function at the finite levels are compact. -/
  isCompact_setOf_le (c : ℝ≥0) : IsCompact {x | I x ≤ c}

/-- The sequence of measures `P n` satisfies the *large deviation principle* with speed `n` and
rate function `I` [DZ98, Section 1.2]: `I` is lower semicontinuous and, for every set `s`,
`-inf_{x ∈ int s} I(x) ≤ liminf_n (1 / n) log P n s` and
`limsup_n (1 / n) log P n s ≤ -inf_{x ∈ cl s} I(x)`. -/
structure IsLDP (P : ℕ → Measure X) (I : X → ℝ≥0∞) : Prop where
  /-- The rate function is lower semicontinuous. -/
  lowerSemicontinuous : LowerSemicontinuous I
  /-- The lower bound, through the interior. -/
  neg_iInf_interior_le_liminf (s : Set X) :
    -(((⨅ x ∈ interior s, I x : ℝ≥0∞)) : EReal) ≤
      liminf (fun n : ℕ ↦ ENNReal.log (P n s) / n) atTop
  /-- The upper bound, through the closure. -/
  limsup_le_neg_iInf_closure (s : Set X) :
    limsup (fun n : ℕ ↦ ENNReal.log (P n s) / n) atTop ≤
      -(((⨅ x ∈ closure s, I x : ℝ≥0∞)) : EReal)

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
lemma limsup_log_div_le_neg_of_le_mul_exp {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ r : ℝ, (r : EReal) < c → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ᶠ n : ℕ in atTop, u n ≤ C * ENNReal.ofReal (Real.exp (-(n * r)))) :
    limsup (fun n : ℕ ↦ ENNReal.log (u n) / n) atTop ≤ -(c : EReal) := by
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
lemma neg_le_liminf_log_div_of_mul_exp_le {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ r : ℝ, (c : EReal) < r → ∃ C : ℝ≥0∞, C ≠ 0 ∧
      ∀ᶠ n : ℕ in atTop, C * ENNReal.ofReal (Real.exp (-(n * r))) ≤ u n) :
    -(c : EReal) ≤ liminf (fun n : ℕ ↦ ENNReal.log (u n) / n) atTop := by
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

/-! ### Reduction to closed sets and to neighbourhoods of points -/

/-- **The large deviation principle from the bounds on closed sets and neighbourhoods.** If `I` is
lower semicontinuous, `limsup_n (1 / n) log P n s ≤ -inf_s I` for every closed set `s`, and
`-I(x) ≤ liminf_n (1 / n) log P n s` for every neighbourhood `s` of every point `x`, then the
measures `P n` satisfy the large deviation principle with rate function `I`. -/
lemma IsLDP.of_isClosed_of_mem_nhds {P : ℕ → Measure X} {I : X → ℝ≥0∞}
    (hI : LowerSemicontinuous I)
    (h_upper : ∀ s, IsClosed s →
      limsup (fun n : ℕ ↦ ENNReal.log (P n s) / n) atTop ≤ -(((⨅ x ∈ s, I x : ℝ≥0∞)) : EReal))
    (h_lower : ∀ x, ∀ s ∈ 𝓝 x,
      -(I x : EReal) ≤ liminf (fun n : ℕ ↦ ENNReal.log (P n s) / n) atTop) :
    IsLDP P I where
  lowerSemicontinuous := hI
  neg_iInf_interior_le_liminf s := by
    have h_mono (n : ℕ) :
        ENNReal.log (P n (interior s)) / n ≤ ENNReal.log (P n s) / n :=
      EReal.div_le_div_right_of_nonneg (by exact_mod_cast n.cast_nonneg)
        (ENNReal.log_monotone (measure_mono interior_subset))
    refine le_trans ?_ (liminf_le_liminf (Eventually.of_forall h_mono))
    rw [EReal.neg_le]
    set L := liminf (fun n : ℕ ↦ ENNReal.log (P n (interior s)) / n) atTop
    rcases le_or_gt (-L) 0 with hL | hL
    · exact hL.trans (EReal.coe_ennreal_nonneg _)
    rw [← EReal.coe_toENNReal hL.le, EReal.coe_ennreal_le_coe_ennreal_iff]
    refine le_iInf₂ fun x hx ↦ ?_
    rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_toENNReal hL.le, EReal.neg_le]
    exact h_lower x _ (isOpen_interior.mem_nhds hx)
  limsup_le_neg_iInf_closure s := by
    have h_mono (n : ℕ) :
        ENNReal.log (P n s) / n ≤ ENNReal.log (P n (closure s)) / n :=
      EReal.div_le_div_right_of_nonneg (by exact_mod_cast n.cast_nonneg)
        (ENNReal.log_monotone (measure_mono subset_closure))
    exact (limsup_le_limsup (Eventually.of_forall h_mono)).trans (h_upper _ isClosed_closure)

/-! ### Exponential bounds from the bounds of a large deviation principle -/

/-- **Exponential upper bounds from the upper bound of a large deviation principle.** If
`limsup_n (1 / n) log u n ≤ -c`, then `u n ≤ exp (-(n r))` eventually, for every real `r < c`. -/
lemma eventually_le_exp_of_limsup_log_div_le {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : limsup (fun n : ℕ ↦ ENNReal.log (u n) / n) atTop ≤ -(c : EReal)) {r : ℝ}
    (hr : (r : EReal) < c) :
    ∀ᶠ n : ℕ in atTop, u n ≤ ENNReal.ofReal (Real.exp (-(n * r))) := by
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
lemma eventually_exp_le_of_neg_le_liminf_log_div {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : -(c : EReal) ≤ liminf (fun n : ℕ ↦ ENNReal.log (u n) / n) atTop) {r : ℝ}
    (hr : (c : EReal) < r) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (-(n * r))) ≤ u n := by
  have h' : ((-r : ℝ) : EReal) < liminf (fun n : ℕ ↦ ENNReal.log (u n) / n) atTop := by
    rw [EReal.coe_neg]
    exact (EReal.neg_lt_neg_iff.2 hr).trans_le h
  filter_upwards [eventually_lt_of_lt_liminf h', eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : EReal) < n := by exact_mod_cast hn1
  rw [EReal.lt_div_iff hn0 (EReal.natCast_ne_top n), ← log_ofReal_exp,
    ENNReal.log_strictMono.lt_iff_lt] at hn
  exact hn.le

/-- Under a large deviation principle, the measure of a closed set `s` is eventually at most
`exp (-(n r))`, for every real `r` below the infimum of the rate function on `s`. -/
lemma IsLDP.eventually_measure_le_exp {P : ℕ → Measure X} {I : X → ℝ≥0∞} (h : IsLDP P I)
    {s : Set X} (hs : IsClosed s) {r : ℝ} (hr : (r : EReal) < ⨅ x ∈ s, I x) :
    ∀ᶠ n : ℕ in atTop, P n s ≤ ENNReal.ofReal (Real.exp (-(n * r))) :=
  eventually_le_exp_of_limsup_log_div_le
    ((h.limsup_le_neg_iInf_closure s).trans_eq (by rw [hs.closure_eq])) hr

/-- Under a large deviation principle, the measure of a neighbourhood `s` of `x` is eventually at
least `exp (-(n r))`, for every real `r > I x`. -/
lemma IsLDP.eventually_exp_le_measure {P : ℕ → Measure X} {I : X → ℝ≥0∞} (h : IsLDP P I)
    {x : X} {s : Set X} (hs : s ∈ 𝓝 x) {r : ℝ} (hr : (I x : EReal) < r) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (-(n * r))) ≤ P n s := by
  refine eventually_exp_le_of_neg_le_liminf_log_div ((EReal.neg_le_neg_iff.2 ?_).trans
    (h.neg_iInf_interior_le_liminf s)) hr
  exact EReal.coe_ennreal_le_coe_ennreal_iff.2 (iInf₂_le x (mem_interior_iff_mem_nhds.2 hs))

/-- **Exponential tightness.** Under a large deviation principle with a good rate function on a
normed group, for every real `r` there is a radius `M` such that the measure of
`{x | M ≤ ‖x‖}` is eventually at most `exp (-(n r))`. -/
lemma IsLDP.exists_eventually_measure_norm_ge_le_exp {E : Type*} [SeminormedAddCommGroup E]
    {mE : MeasurableSpace E} {P : ℕ → Measure E} {I : E → ℝ≥0∞} (h : IsLDP P I)
    (hI : IsGoodRateFunction I) (r : ℝ) :
    ∃ M : ℝ, ∀ᶠ n : ℕ in atTop, P n {x | M ≤ ‖x‖} ≤ ENNReal.ofReal (Real.exp (-(n * r))) := by
  set c : ℝ≥0 := (max r 0 + 1).toNNReal with hc_def
  obtain ⟨C, hC⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : E)).1 (hI.isCompact_setOf_le c).isBounded
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

/-- **Weighted sums of good rate functions are good.** For good rate functions `I a` on spaces
`X a`, indexed by a finite type, and positive weights `w a`, the function
`x ↦ ∑ a, w a I a (x a)` on the product is a good rate function. -/
lemma isGoodRateFunction_sum_mul {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ a, TopologicalSpace (X a)] {I : ∀ a, X a → ℝ≥0∞} (hI : ∀ a, IsGoodRateFunction (I a))
    {w : ι → ℝ} (hw : ∀ a, 0 < w a) :
    IsGoodRateFunction fun x : (∀ a, X a) ↦ ∑ a, ENNReal.ofReal (w a) * I a (x a) := by
  have h_lsc : LowerSemicontinuous fun x : (∀ a, X a) ↦ ∑ a, ENNReal.ofReal (w a) * I a (x a) :=
    lowerSemicontinuous_sum fun a _ ↦
      (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous
        ((hI a).lowerSemicontinuous.comp (continuous_apply a)) fun _ _ h ↦ by dsimp only; gcongr
  refine ⟨h_lsc, fun c ↦ ?_⟩
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun a ↦ (hI a).isCompact_setOf_le (c / (w a).toNNReal))
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
