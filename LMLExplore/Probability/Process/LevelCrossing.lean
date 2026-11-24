/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Statlib.ForMathlib.MeasureTheory.Integral.EReal.EIntegral
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.Data.EReal.Basic
import LMLExplore.Data.EReal.Inv
import LMLExplore.Data.ENat.Basic
import LMLExplore.Probability.Independence.FirstPassage
import LMLExplore.Probability.Process.HittingTime
import LMLExplore.Probability.Process.Stopping
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# The time for a growing process to reach a level

Let `E : ℕ → Ω → ℝ≥0∞` be a process, for instance an e-process, and let `τ α` be the first time
`E` reaches `α⁻¹`, the sequential test of level `α` obtained by thresholding an e-process
(`ProbabilityTheory.IsEProcess.isLevelStoppingTime_hittingAfter`). If the logarithm of `E` grows
at least linearly at a rate `L`, the test stops after about `log (1/α) / L` observations
[ARR26, Theorem 4.1]:

* **Pathwise.** If `c n ≤ log (E n ω)` for every `n ≥ n₀`, with `c > 0`, then
  `τ α ω ≤ n₀ + ⌈log (1/α) / c⌉`.
* **Almost surely.** If `L ≤ liminf (1/n) log (E n ω)`, then
  `limsup_{α → 0} τ α ω / log (1/α) ≤ 1 / L`.
* **In expectation.** If, for every rate `0 < c < L`, the first index `N ω` after which
  `c n ≤ log (E n ω)` has a finite mean under a probability measure `Q` (the integrable convergence
  of [ARR26]), then `limsup_{α → 0} 𝔼_Q[τ α] / log (1/α) ≤ 1 / L`.

Nothing is assumed of `E`: the bounds are statements about the time a sequence takes to reach a
level, and they hold for every process and every filtration. For an e-process of a null `S`
growing at the rate `L = KL_inf(Q, S)` under an alternative `Q`, the bound in expectation matches
the lower bound `log (1/α) / KL_inf(Q, S)` of [ARR26, Theorem 3.1] on the expected number of
observations of every sequential test of level `α` (for i.i.d. nulls,
`ProbabilityTheory.toENNReal_log_inv_div_bipolarRate_le_lintegral` contains it), so that
thresholding such an e-process is first-order optimal as `α → 0`. Without the integrability of the
index `N`, the expected stopping times may be infinite [ARR26, Section 4].

**Products of i.i.d. factors.** For a product `∏ k < n, X k` of independent, identically
distributed factors whose logarithm has a positive mean `D = 𝔼[log (X 0)]`, possibly infinite,
the first time `τ α` at which the product reaches `α⁻¹` satisfies `𝔼[τ α] / log (1/α) → 1 / D`.
The logarithm of the product is the random walk of the increments `log (X k)`, and `τ α` is its
first passage time above `log (1/α)`, so this is the elementary renewal theorem for first passage
times (`ProbabilityTheory.iIndepFun.tendsto_lintegral_hittingAfter_sum_div`), which needs no
moment beyond the finiteness of the mean of the negative part of `log (X 0)`. Where a factor is
infinite with positive probability, `D = ∞`, and the product is infinite from the first infinite
factor on, a time of finite mean.

The rate `L` is an extended real, and `1 / L` is `L.toENNReal⁻¹`: it is `0` for `L = ⊤` and `⊤`
for `L ≤ 0`. The level `log (1/α)` is `(ENNReal.log α⁻¹).toENNReal`, as in
`ProbabilityTheory.toENNReal_log_inv_div_bipolarRate_le_lintegral`.

## Main statements

* `ProbabilityTheory.hittingAfter_Ici_inv_le_add_ceil`: the pathwise bound
  `τ α ω ≤ n₀ + ⌈log (1/α) / c⌉`.
* `ProbabilityTheory.limsup_toENNReal_hittingAfter_div_log_le`: almost surely, or rather on every
  path where `L ≤ liminf (1/n) log (E n ω)`, `limsup_{α → 0} τ α ω / log (1/α) ≤ 1 / L`.
* `ProbabilityTheory.limsup_lintegral_hittingAfter_div_log_le`: under the integrable convergence,
  `limsup_{α → 0} 𝔼_Q[τ α] / log (1/α) ≤ 1 / L`.
* `ProbabilityTheory.iIndepFun.tendsto_lintegral_hittingAfter_prod_div_log`: for a product of
  i.i.d. factors, `𝔼[τ α] / log (1/α) → 1 / 𝔼[log (X 0)]`.

## References

* [ARR26] S. Agrawal, A. Ram and A. Ramdas, *On stopping times of power-one sequential tests:
  tight lower and upper bounds*, arXiv:2504.19952v2, Theorem 4.1.
* [Gut09] A. Gut, *Stopped Random Walks: Limit Theorems and Applications*, 2nd edition, Springer,
  2009, Chapter 3.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {E : ℕ → Ω → ℝ≥0∞}

/-- **The pathwise bound on the time to reach a level** [ARR26, proof of Theorem 4.1]. If the
logarithm of `E n ω` is at least `c n` for every `n ≥ n₀`, with `c > 0`, then `E` reaches `α⁻¹`,
for `α ≠ 0`, at the latest at the time `n₀ + ⌈log (1/α) / c⌉`. -/
theorem hittingAfter_Ici_inv_le_add_ceil {c : ℝ} (hc : 0 < c) {ω : Ω} {n₀ : ℕ}
    (h : ∀ k ≥ n₀, ((c * k : ℝ) : EReal) ≤ ENNReal.log (E k ω)) {α : ℝ≥0∞} (hα : α ≠ 0) :
    hittingAfter E (Set.Ici α⁻¹) 0 ω ≤ (n₀ + ⌈(ENNReal.log α⁻¹).toReal / c⌉₊ : ℕ) := by
  refine hittingAfter_le_of_mem (Nat.zero_le _) ?_
  rw [Set.mem_Ici, ← ENNReal.log_le_log_iff]
  refine le_trans ?_ (h _ (Nat.le_add_right _ _))
  refine (EReal.le_coe_toReal (by simpa using hα)).trans (EReal.coe_le_coe_iff.2 ?_)
  calc (ENNReal.log α⁻¹).toReal
  _ ≤ c * ⌈(ENNReal.log α⁻¹).toReal / c⌉₊ := by
    rw [← div_le_iff₀' hc]
    exact Nat.le_ceil _
  _ ≤ c * ((n₀ + ⌈(ENNReal.log α⁻¹).toReal / c⌉₊ : ℕ) : ℝ) := by
    gcongr
    exact Nat.le_add_left _ _

/-- The pathwise bound in `ℝ≥0∞`: `τ α ω ≤ n₀ + 1 + log (1/α) / c`. -/
private lemma toENNReal_hittingAfter_le_add_mul {c : ℝ} (hc : 0 < c) {ω : Ω} {n₀ : ℕ}
    (h : ∀ k ≥ n₀, ((c * k : ℝ) : EReal) ≤ ENNReal.log (E k ω)) {α : ℝ≥0∞} (hα : α ≠ 0) :
    ENat.toENNReal (hittingAfter E (Set.Ici α⁻¹) 0 ω) ≤
      (n₀ + 1 : ℝ≥0∞) + (ENNReal.log α⁻¹).toENNReal * ENNReal.ofReal c⁻¹ := by
  -- `hittingAfter` takes values in `WithTop ℕ`, so the cast of the bound goes through `ℕ∞`
  refine le_trans (b := ((n₀ + ⌈(ENNReal.log α⁻¹).toReal / c⌉₊ : ℕ) : ℝ≥0∞)) ?_ ?_
  · rw [← ENat.toENNReal_coe]
    exact ENat.toENNReal_le.2 (hittingAfter_Ici_inv_le_add_ceil hc h hα)
  rw [Nat.cast_add, add_assoc]
  gcongr
  set b := (ENNReal.log α⁻¹).toReal
  have hB : (ENNReal.log α⁻¹).toENNReal = ENNReal.ofReal b :=
    EReal.toENNReal_of_ne_top (by simpa using hα)
  rcases le_or_gt b 0 with hb | hb
  · simp [Nat.ceil_eq_zero.2 (div_nonpos_of_nonpos_of_nonneg hb hc.le)]
  rw [hB, ← ENNReal.ofReal_mul hb.le, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one
    (by positivity), ← ENNReal.ofReal_natCast, add_comm]
  exact ENNReal.ofReal_le_ofReal (Nat.ceil_lt_add_one (by positivity)).le

/-- **Tests thresholding a growing process stop early, pathwise** [ARR26, Theorem 4.1]. If the
logarithm of `E n ω` grows at least at the rate `L`, in the sense that
`L ≤ liminf (1/n) log (E n ω)`, then the first time `τ α ω` at which `E` reaches `α⁻¹` satisfies
`limsup_{α → 0} τ α ω / log (1/α) ≤ 1 / L`. The rate may be `⊤`, where the bound is `0`; for
`L ≤ 0` the bound is `⊤`. Applied on an almost sure event, this is the almost sure form of
[ARR26, Theorem 4.1]. -/
theorem limsup_toENNReal_hittingAfter_div_log_le {L : EReal} {ω : Ω}
    (h : L ≤ liminf (fun n : ℕ ↦ ENNReal.log (E n ω) / (n : EReal)) atTop) :
    limsup (fun α ↦ ENat.toENNReal (hittingAfter E (Set.Ici α⁻¹) 0 ω) /
      (ENNReal.log α⁻¹).toENNReal) (𝓝[>] 0) ≤ L.toENNReal⁻¹ := by
  refine EReal.le_inv_toENNReal_iff.2 fun c hc hcL ↦ ?_
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 ((eventually_lt_of_lt_liminf (hcL.trans_le h)).and
    (eventually_gt_atTop 0))
  refine ENNReal.limsup_div_toENNReal_log_inv_le (K := n₀ + 1) (by simp) fun α hα _ ↦
    toENNReal_hittingAfter_le_add_mul hc (fun k hk ↦ ?_) hα.ne'
  obtain ⟨hlt, hk0⟩ := hn₀ k hk
  rw [mul_comm]
  exact ((EReal.coe_lt_div_natCast_iff hk0).1 hlt).le

/-- **Tests thresholding a growing process stop early, in expectation** [ARR26, Theorem 4.1]. Let
`Q` be a probability measure and `L` a rate such that, for every real `0 < c < L`, there is an
index `N ω` of finite mean under `Q` after which `c n ≤ log (E n ω)` almost surely (the
integrable convergence of [ARR26]). Then the first time `τ α` at which `E` reaches `α⁻¹`
satisfies `limsup_{α → 0} 𝔼_Q[τ α] / log (1/α) ≤ 1 / L`. The rate may be `⊤`, where the bound
is `0`. For an e-process growing at the rate `KL_inf(Q, S)` of the smallest relative entropy from
`Q` to the null, this attains the lower bound on the expected number of observations of a
sequential test of level `α`. -/
theorem limsup_lintegral_hittingAfter_div_log_le {Q : Measure Ω} [IsProbabilityMeasure Q]
    {L : EReal} (h : ∀ c : ℝ, 0 < c → (c : EReal) < L → ∃ N : Ω → ℕ,
      ∫⁻ ω, (N ω : ℝ≥0∞) ∂Q ≠ ∞ ∧
        ∀ᵐ ω ∂Q, ∀ k ≥ N ω, ((c * k : ℝ) : EReal) ≤ ENNReal.log (E k ω)) :
    limsup (fun α ↦ (∫⁻ ω, ENat.toENNReal (hittingAfter E (Set.Ici α⁻¹) 0 ω) ∂Q) /
      (ENNReal.log α⁻¹).toENNReal) (𝓝[>] 0) ≤ L.toENNReal⁻¹ := by
  refine EReal.le_inv_toENNReal_iff.2 fun c hc hcL ↦ ?_
  obtain ⟨N, hN, hNE⟩ := h c hc hcL
  refine ENNReal.limsup_div_toENNReal_log_inv_le (K := ∫⁻ ω, (N ω : ℝ≥0∞) ∂Q + 1)
    (by simpa using hN) fun α hα _ ↦ ?_
  calc ∫⁻ ω, ENat.toENNReal (hittingAfter E (Set.Ici α⁻¹) 0 ω) ∂Q
  _ ≤ ∫⁻ ω, (N ω : ℝ≥0∞) + (1 + (ENNReal.log α⁻¹).toENNReal * ENNReal.ofReal c⁻¹) ∂Q := by
    refine lintegral_mono_ae (hNE.mono fun ω hω ↦ ?_)
    rw [← add_assoc]
    exact toENNReal_hittingAfter_le_add_mul hc hω hα.ne'
  _ = ∫⁻ ω, (N ω : ℝ≥0∞) ∂Q + 1 + (ENNReal.log α⁻¹).toENNReal * ENNReal.ofReal c⁻¹ := by
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
      add_assoc]

/-! ### Products of independent, identically distributed factors -/

section IID

variable {μ : Measure Ω} {X : ℕ → Ω → ℝ≥0∞}

/-- The product of i.i.d. factors that are almost surely positive and finite reaches `α⁻¹` after
`log (1/α) / D` steps in expectation to first order, with `D = 𝔼[(log X)⁺] - 𝔼[(log X)⁻]`: its
logarithm is a random walk, and this is the elementary renewal theorem for first passage
times. -/
private lemma iIndepFun.tendsto_lintegral_hittingAfter_prod_div_log_of_ae_ne_top
    (hX : iIndepFun X μ) (hXm : ∀ j, Measurable (X j))
    (hident : ∀ j, IdentDistrib (X j) (X 0) μ μ) (hX0 : ∀ᵐ ω ∂μ, ∀ j, X j ω ≠ 0)
    (hXtop : ∀ᵐ ω ∂μ, ∀ j, X j ω ≠ ∞)
    (hqp : ∫⁻ ω, (-ENNReal.log (X 0 ω)).toENNReal ∂μ < ∫⁻ ω, (ENNReal.log (X 0 ω)).toENNReal ∂μ) :
    Tendsto (fun α ↦ (∫⁻ ω, ENat.toENNReal (hittingAfter
        (fun n ω ↦ ∏ k ∈ Finset.range n, X k ω) (Set.Ici α⁻¹) 0 ω) ∂μ) /
        (ENNReal.log α⁻¹).toENNReal) (𝓝[>] 0)
      (𝓝 (∫⁻ ω, (ENNReal.log (X 0 ω)).toENNReal ∂μ -
        ∫⁻ ω, (-ENNReal.log (X 0 ω)).toENNReal ∂μ)⁻¹) := by
  -- the increments `log (X j)` of the random walk, in `ℝ`
  set g : ℝ≥0∞ → ℝ := fun x ↦ (ENNReal.log x).toReal
  have hgm : Measurable g := ENNReal.measurable_log.ereal_toReal
  have hY : iIndepFun (fun j ω ↦ g (X j ω)) μ := hX.comp (fun _ ↦ g) fun _ ↦ hgm
  have hp : ∫⁻ ω, ENNReal.ofReal (g (X 0 ω)) ∂μ = ∫⁻ ω, (ENNReal.log (X 0 ω)).toENNReal ∂μ :=
    lintegral_congr_ae (hXtop.mono fun ω hω ↦
      (EReal.toENNReal_of_ne_top (by simpa using hω 0)).symm)
  have hq : ∫⁻ ω, ENNReal.ofReal (-g (X 0 ω)) ∂μ =
      ∫⁻ ω, (-ENNReal.log (X 0 ω)).toENNReal ∂μ := by
    refine lintegral_congr_ae (hX0.mono fun ω hω ↦ ?_)
    have hω' : -ENNReal.log (X 0 ω) ≠ ⊤ := by simpa using hω 0
    simp only [g]
    rw [EReal.toENNReal_of_ne_top hω', EReal.toReal_neg_eq]
  have hlim := (hY.tendsto_lintegral_hittingAfter_sum_div (fun j ↦ hgm.comp (hXm j))
    (fun j ↦ (hident j).comp hgm) (hq.trans_lt (hqp.trans_eq hp.symm))).comp
    ENNReal.tendsto_toReal_log_inv_nhdsGT_zero
  rw [hp, hq] at hlim
  refine hlim.congr' ?_
  -- for `α ∈ (0, 1)`, the product reaches `α⁻¹` when the walk reaches `log (1/α)`
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with α ⟨hα0, hα1⟩
  rw [Function.comp_apply, EReal.toENNReal_of_ne_top (by simpa using hα0.ne')]
  congr 1
  refine lintegral_congr_ae ((hX0.and hXtop).mono fun ω hω ↦ ?_)
  refine congrArg ENat.toENNReal (hittingAfter_apply_congr fun k _ ↦ ?_)
  rw [Set.mem_Ici, Set.mem_Ici, ENNReal.le_prod_iff_toReal_log_le_sum
    (fun j _ ↦ ⟨hω.1 j, hω.2 j⟩) (ENNReal.inv_ne_zero.2 hα1.ne_top) (ENNReal.inv_ne_top.2 hα0.ne')]

/-- The product of i.i.d. almost surely nonzero factors that are infinite with positive
probability reaches every level after a number of steps of finite mean, the first time a factor
is infinite, so that `𝔼[τ α] / log (1/α) → 0`. -/
private lemma iIndepFun.tendsto_lintegral_hittingAfter_prod_div_log_of_measure_ne_zero
    (hX : iIndepFun X μ) (hXm : ∀ j, Measurable (X j))
    (hident : ∀ j, IdentDistrib (X j) (X 0) μ μ) (hX0 : ∀ᵐ ω ∂μ, ∀ j, X j ω ≠ 0)
    (htop : μ {ω | X 0 ω = ∞} ≠ 0) :
    Tendsto (fun α ↦ (∫⁻ ω, ENat.toENNReal (hittingAfter
        (fun n ω ↦ ∏ k ∈ Finset.range n, X k ω) (Set.Ici α⁻¹) 0 ω) ∂μ) /
        (ENNReal.log α⁻¹).toENNReal) (𝓝[>] 0) (𝓝 0) := by
  have := hX.isProbabilityMeasure
  -- the walk `Z` of the indicators of the infinite factors, of positive drift
  set z : ℝ≥0∞ → ℝ := ({∞} : Set ℝ≥0∞).indicator 1
  have hzm : Measurable z := measurable_const.indicator (measurableSet_singleton ∞)
  have hz0 (x : ℝ≥0∞) : 0 ≤ z x := Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x
  have hZm (j : ℕ) : Measurable fun ω ↦ z (X j ω) := hzm.comp (hXm j)
  have hZpos : ∫⁻ ω, ENNReal.ofReal (-z (X 0 ω)) ∂μ < ∫⁻ ω, ENNReal.ofReal (z (X 0 ω)) ∂μ := by
    have h1 : ∫⁻ ω, ENNReal.ofReal (-z (X 0 ω)) ∂μ = 0 :=
      (lintegral_congr fun ω ↦ ENNReal.ofReal_of_nonpos (neg_nonpos.2 (hz0 _))).trans
        lintegral_zero
    have h2 : ∫⁻ ω, ENNReal.ofReal (z (X 0 ω)) ∂μ = μ {ω | X 0 ω = ∞} := by
      rw [← lintegral_indicator_one (measurableSet_eq_fun (hXm 0) measurable_const)]
      refine lintegral_congr fun ω ↦ ?_
      by_cases hω : X 0 ω = ∞ <;> simp [z, hω]
    rw [h1, h2]
    exact pos_iff_ne_zero.2 htop
  -- its first passage time `G` above `1` has a finite mean, so it is finite almost surely
  set G := hittingAfter (fun k ω ↦ ∑ j ∈ Finset.range k, z (X j ω)) (Set.Ici (1 : ℝ)) 0
  have hGint : ∫⁻ ω, ENat.toENNReal (G ω) ∂μ ≠ ∞ :=
    ((hX.comp (fun _ ↦ z) fun _ ↦ hzm).lintegral_hittingAfter_sum_lt_top hZm
      (fun j ↦ (hident j).comp hzm) hZpos 1).ne
  have hGm : Measurable fun ω ↦ ENat.toENNReal (G ω) := measurable_from_top.comp
    (Adapted.isStoppingTime_hittingAfter (f := Filtration.const ℕ _ le_rfl)
      (fun k ↦ Finset.measurable_sum _ fun j _ ↦ hZm j) measurableSet_Ici).measurable_enat
  have hGfin : ∀ᵐ ω ∂μ, G ω ≠ ⊤ := by
    filter_upwards [ae_lt_top hGm hGint] with ω hω hG
    exact hω.ne (by rw [hG]; exact ENat.toENNReal_top)
  -- from the time `G` on, the product is infinite, at every rate
  have hlim := limsup_lintegral_hittingAfter_div_log_le
    (E := fun n ω ↦ ∏ k ∈ Finset.range n, X k ω) (Q := μ) (L := ⊤)
    fun c _ _ ↦ ⟨fun ω ↦ (G ω).untopA, ne_top_of_le_ne_top hGint (lintegral_mono fun ω ↦ ?_), ?_⟩
  · rw [EReal.toENNReal_top, ENNReal.inv_top] at hlim
    exact tendsto_of_le_liminf_of_limsup_le bot_le hlim
  · by_cases hG : G ω = ⊤
    · exact le_top.trans_eq (by rw [hG]; exact ENat.toENNReal_top.symm)
    obtain ⟨n, hn⟩ := WithTop.exists_eq_natCast_of_ne_top hG
    dsimp only
    rw [hn, WithTop.untopA_natCast]
    exact (ENat.toENNReal_coe n).ge
  · filter_upwards [hGfin, hX0] with ω hG hω0 k hk
    -- some factor before `G ω` is infinite, and the others are nonzero
    have hmem : (1 : ℝ) ≤ ∑ j ∈ Finset.range (G ω).untopA, z (X j ω) :=
      hittingAfter_mem_set_of_ne_top hG
    obtain ⟨j, hj, hzj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (one_pos.trans_le hmem).ne'
    have hXj : X j ω = ∞ := Set.mem_singleton_iff.1 (Set.mem_of_indicator_ne_zero hzj)
    have hjk : j ∈ Finset.range k := Finset.mem_range.2 ((Finset.mem_range.1 hj).trans_le hk)
    rw [← Finset.mul_prod_erase _ _ hjk, hXj,
      ENNReal.top_mul (Finset.prod_ne_zero_iff.2 fun i _ ↦ hω0 i), ENNReal.log_top]
    exact le_top

/-- **The expected time for a product of i.i.d. factors to reach a level** [ARR26, Theorem 4.1].
Let `X j` be independent, identically distributed random variables with values in `ℝ≥0∞`, whose
logarithm has a positive mean `D = 𝔼[log (X 0)]`, in `(0, ∞]`, as Statlib's extended integral.
The first time `τ α` at which the product `∏ k < n, X k` reaches `α⁻¹` satisfies
`𝔼[τ α] / log (1/α) → 1 / D` as `α → 0`, with `1 / ∞ = 0`. No moment is assumed beyond the
finiteness of the mean of the negative part of `log (X 0)`, which `D > 0` contains. When the
factors are the values `e (ω k)` of an e-variable `e` for a null at i.i.d. observations, the
products form an e-process for the i.i.d. null (`ProbabilityTheory.IsEVar.isEProcess_prod_piLT`)
and `τ α` is a sequential test of level `α`. -/
theorem iIndepFun.tendsto_lintegral_hittingAfter_prod_div_log (hX : iIndepFun X μ)
    (hXm : ∀ j, Measurable (X j)) (hident : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hpos : 0 < ∫ᵉ ω, ENNReal.log (X 0 ω) ∂μ) :
    Tendsto (fun α ↦ (∫⁻ ω, ENat.toENNReal (hittingAfter
        (fun n ω ↦ ∏ k ∈ Finset.range n, X k ω) (Set.Ici α⁻¹) 0 ω) ∂μ) /
        (ENNReal.log α⁻¹).toENNReal) (𝓝[>] 0)
      (𝓝 (∫ᵉ ω, ENNReal.log (X 0 ω) ∂μ).toENNReal⁻¹) := by
  -- the mean of the logarithm is the difference of the means of its positive and negative parts
  set p := ∫⁻ ω, (ENNReal.log (X 0 ω)).toENNReal ∂μ
  set q := ∫⁻ ω, (-ENNReal.log (X 0 ω)).toENNReal ∂μ
  have hD : ∫ᵉ ω, ENNReal.log (X 0 ω) ∂μ = (p : EReal) - q := by rw [eintegral]
  have hqp : q < p := by
    by_contra h
    push Not at h
    exact hpos.not_ge (hD ▸ EReal.sub_nonpos.2 (EReal.coe_ennreal_le_coe_ennreal_iff.2 h))
  rw [hD, EReal.coe_ennreal_sub_toENNReal]
  -- the factors are almost surely nonzero, since the negative part of `log (X 0)` has a finite mean
  have hlogm : Measurable fun ω ↦ (-ENNReal.log (X 0 ω)).toENNReal :=
    ((hXm 0).ennreal_log.neg).ereal_toENNReal
  have hX0 : ∀ᵐ ω ∂μ, ∀ j, X j ω ≠ 0 := by
    refine ae_all_iff.2 fun j ↦ (hident j).symm.ae_snd (measurableSet_singleton 0).compl ?_
    filter_upwards [ae_lt_top hlogm (hqp.trans_le le_top).ne] with ω hω (h0 : X 0 ω = 0)
    simp [h0] at hω
  by_cases htop : μ {ω | X 0 ω = ∞} = 0
  · refine hX.tendsto_lintegral_hittingAfter_prod_div_log_of_ae_ne_top hXm hident hX0
      (ae_all_iff.2 fun j ↦ (hident j).symm.ae_snd (measurableSet_singleton ∞).compl ?_) hqp
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 htop] with ω hω
    simpa using hω
  · -- the logarithm has an infinite positive part, and the limit is `0`
    have hp : p = ⊤ := by
      refine eq_top_iff.2 ?_
      calc ⊤ = ∫⁻ ω, {ω | X 0 ω = ∞}.indicator (fun _ ↦ ⊤) ω ∂μ := by
            rw [lintegral_indicator_const (measurableSet_eq_fun (hXm 0) measurable_const),
              ENNReal.top_mul htop]
      _ ≤ p := lintegral_mono fun ω ↦ by
            by_cases hω : X 0 ω = ∞ <;> simp [hω]
    rw [hp, ENNReal.top_sub (hqp.trans_eq hp).ne, ENNReal.inv_top]
    exact hX.tendsto_lintegral_hittingAfter_prod_div_log_of_measure_ne_zero hXm hident hX0 htop

end IID

end ProbabilityTheory
