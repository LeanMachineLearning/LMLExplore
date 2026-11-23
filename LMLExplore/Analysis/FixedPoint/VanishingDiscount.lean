/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.FixedPoint.SpanSeminorm
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Vanishing discount for topical maps

Let `E` be an ordered real normed space whose norm is the order-unit norm of `e` (`ι → ℝ` with `ι`
finite and `e = 1`, through `LMLExplore.orderUnitNorm_one_eq_norm`, or the bounded measurable
functions `LMLExplore.boundedMeasurable 𝓢`), and let `T : E → E` be topical. For a discount
`γ < 1`, the map `x ↦ T (γ • x)` is a `γ`-contraction; let `v γ` be a fixed point,
`v γ = T (γ • v γ)`. When `T` is the undiscounted Bellman operator of an MDP, `v γ` is the optimal
`γ`-discounted value.

The *vanishing discount* approach [Koh80], [LS, Theorem 38.2] obtains an additive eigenvector
`T h = h + g • e` (the average-reward optimality equation, with gain `g` and bias `h`) as a limit
of the discounted fixed points as `γ ↑ 1`:

* If the oscillations `osc_e (v γ)` are bounded by `B`, and `E` is proper (for instance finite
  dimensional), then there are `g` and `h` with `T h = h + g • e` and `osc_e h ≤ B`
  (`LMLExplore.IsTopical.exists_map_eq_add_smul_of_orderUnitOsc_le`). The renormalised fixed
  points `v γ - c_γ • e` are bounded, and so are `(1 - γ) • c_γ`; a limit point along `γ ↑ 1`
  gives `h` and `g`.
* Conversely, any additive eigenvector controls the discounted fixed points, without compactness:
  `‖v γ - (g / (1 - γ)) • e‖ ≤ osc_e h` (`LMLExplore.IsTopical.norm_sub_smul_le_orderUnitOsc`),
  hence `osc_e (v γ) ≤ 2 * osc_e h` and `(1 - γ) • v γ → g • e` as `γ ↑ 1`
  (`LMLExplore.IsTopical.tendsto_one_sub_smul`). The first bound is the abstract form of
  [WJLSJ20, Lemma 2], `‖v*_γ - ρ* / (1 - γ)‖ ≤ sp (h*)`.

So, for proper `E`, an additive eigenvector exists exactly when the oscillations of the discounted
fixed points are bounded (`LMLExplore.IsTopical.exists_map_eq_add_smul_iff_bddAbove`). Finally, the
value iteration `T^[n] x` grows like `n * g`:
`‖T^[n] x - (n * g) • e‖ ≤ ‖x - h‖ + ‖h‖` (`LMLExplore.IsTopical.norm_iterate_sub_smul_le`).

## Main statements

* `LMLExplore.IsTopical.one_sub_mul_norm_le`: `(1 - γ) * ‖v γ‖ ≤ ‖T 0‖`.
* `LMLExplore.IsTopical.norm_sub_sub_smul_le`: `‖v γ - h - (g / (1 - γ)) • e‖ ≤ ‖h‖` when
  `T h = h + g • e`.
* `LMLExplore.IsTopical.norm_sub_smul_le_orderUnitOsc`: `‖v γ - (g / (1 - γ)) • e‖ ≤ osc_e h`.
* `LMLExplore.IsTopical.orderUnitOsc_le_two_mul_orderUnitOsc`: `osc_e (v γ) ≤ 2 * osc_e h`.
* `LMLExplore.IsTopical.tendsto_one_sub_smul`: `(1 - γ) • v γ → g • e` as `γ ↑ 1`.
* `LMLExplore.IsTopical.norm_iterate_sub_smul_le`: `‖T^[n] x - (n * g) • e‖ ≤ ‖x - h‖ + ‖h‖`.
* `LMLExplore.IsTopical.exists_map_eq_add_smul_of_orderUnitOsc_le`: existence of an additive
  eigenvector with `osc_e h ≤ B` from the bound `osc_e (v γ) ≤ B`.
* `LMLExplore.IsTopical.exists_map_eq_add_smul_iff_bddAbove`: an additive eigenvector exists iff
  the oscillations of the discounted fixed points are bounded.

## References

* [E. Kohlberg, *Invariant half-lines of nonexpansive piecewise-linear transformations*,
  1980][Koh80]
* [T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, 2020][LS], Theorem 38.2
* [C.-Y. Wei, M. Jafarnia-Jahromi, H. Luo, H. Sharma and R. Jain, *Model-free reinforcement
  learning in infinite-horizon average-reward Markov decision processes*, 2020][WJLSJ20], Lemma 2
-/

public section

open Filter Function Set Submodule Topology
open scoped NNReal

namespace LMLExplore

namespace IsTopical

variable {E : Type*} [NormedAddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [NormedSpace ℝ E] {e : E} {T : E → E}

/-! ### Bounds from an additive eigenvector -/

/-- The iterates of a topical map grow linearly at the rate of an additive eigenvector:
if `T h = h + g • e`, then `‖T^[n] x - (n * g) • e‖ ≤ ‖x - h‖ + ‖h‖`. -/
theorem norm_iterate_sub_smul_le (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : IsTopical e T)
    {h : E} {g : ℝ} (hh : T h = h + g • e) (n : ℕ) (x : E) :
    ‖T^[n] x - ((n : ℝ) * g) • e‖ ≤ ‖x - h‖ + ‖h‖ := by
  calc ‖T^[n] x - ((n : ℝ) * g) • e‖ = ‖(T^[n] x - T^[n] h) + h‖ := by
        rw [hT.iterate_eq_add_smul hh]
        congr 1
        abel
    _ ≤ ‖T^[n] x - T^[n] h‖ + ‖h‖ := norm_add_le _ _
    _ ≤ ‖x - h‖ + ‖h‖ := by
        gcongr
        simpa [dist_eq_norm] using ((hT.iterate n).lipschitzWith hnorm).dist_le_mul x h

omit [IsOrderedAddMonoid E] in
/-- Writing a fixed point of `x ↦ T (γ • x)` as `v = m + c • e`, the fixed-point equation reads
`T (γ • m) = m + ((1 - γ) * c) • e`. -/
private lemma map_smul_eq_add_smul (hT : IsTopical e T) {γ c : ℝ} {v m : E}
    (hv : v = T (γ • v)) (hvm : v = m + c • e) : T (γ • m) = m + ((1 - γ) * c) • e := by
  rw [hvm, smul_add, smul_smul, hT.map_add_smul] at hv
  rw [eq_sub_of_add_eq hv.symm]
  module

variable [PosSMulMono ℝ E] {γ : ℝ≥0} {v h : E} {g : ℝ}

/-- A fixed point of the discounted topical map `x ↦ T (γ • x)` satisfies
`(1 - γ) * ‖v‖ ≤ ‖T 0‖`. -/
theorem one_sub_mul_norm_le (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : IsTopical e T)
    (hv : v = T ((γ : ℝ) • v)) : (1 - (γ : ℝ)) * ‖v‖ ≤ ‖T 0‖ := by
  -- `x ↦ T (γ • x)` is `γ`-Lipschitz and maps `0` to `T 0`.
  have hlip := (hT.isBlackwell_comp_smul γ).lipschitzWith hnorm
  have := hlip.dist_le_mul v 0
  simp only [dist_eq_norm, smul_zero, sub_zero, ← hv] at this
  have := norm_le_norm_sub_add v (T 0)
  nlinarith

/-- Writing a fixed point of `x ↦ T (γ • x)`, `γ ≤ 1`, as `v = m + c • e`, the rescaled constant
satisfies `|(1 - γ) * c| * ‖e‖ ≤ ‖T 0‖ + ‖m‖`. -/
private lemma abs_one_sub_mul_mul_norm_le (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : IsTopical e T) (hγ : γ ≤ 1) (hv : v = T ((γ : ℝ) • v)) {m : E} {c : ℝ}
    (hvm : v = m + c • e) : |(1 - (γ : ℝ)) * c| * ‖e‖ ≤ ‖T 0‖ + ‖m‖ := by
  have h1 : 0 ≤ 1 - (γ : ℝ) := sub_nonneg.2 (mod_cast hγ)
  have hv0 := hT.one_sub_mul_norm_le hnorm hv
  have hae : ((1 - (γ : ℝ)) * c) • e = (1 - (γ : ℝ)) • v - (1 - (γ : ℝ)) • m := by
    rw [hvm]
    module
  rw [← Real.norm_eq_abs, ← norm_smul, hae]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg h1]
  have : (1 - (γ : ℝ)) * ‖m‖ ≤ ‖m‖ :=
    mul_le_of_le_one_left (norm_nonneg _) (by linarith [γ.coe_nonneg])
  linarith

/-- **Comparison with an additive eigenvector.** If `T h = h + g • e` and `v = T (γ • v)` with
`γ < 1`, then `‖v - h - (g / (1 - γ)) • e‖ ≤ ‖h‖`: up to the error `‖h‖`, the discounted fixed
point is `h + (g / (1 - γ)) • e`. -/
theorem norm_sub_sub_smul_le (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : IsTopical e T)
    (hγ : γ < 1) (hv : v = T ((γ : ℝ) • v)) (hh : T h = h + g • e) :
    ‖v - h - (g / (1 - γ)) • e‖ ≤ ‖h‖ := by
  have h1 : (0 : ℝ) < 1 - γ := sub_pos.2 (mod_cast hγ)
  set u := h + (g / (1 - γ)) • e with hu_def
  -- The discounted map moves `u` by `T (γ • h) - T h` only.
  have hu : T ((γ : ℝ) • u) = u + (T ((γ : ℝ) • h) - T h) := by
    have hc : (γ : ℝ) * (g / (1 - γ)) = g / (1 - γ) - g := by
      field_simp
      ring
    rw [hu_def, smul_add, smul_smul, hT.map_add_smul, hh, hc, sub_smul]
    abel
  have hγh : ‖(γ : ℝ) • h - h‖ = (1 - γ) * ‖h‖ := by
    rw [show (γ : ℝ) • h - h = -((1 - (γ : ℝ)) • h) by module, norm_neg, norm_smul,
      Real.norm_of_nonneg h1.le]
  have hSu : dist u (T ((γ : ℝ) • u)) ≤ (1 - γ) * ‖h‖ := by
    rw [hu, dist_eq_norm, sub_add_cancel_left, norm_neg, ← hγh]
    simpa [dist_eq_norm] using (hT.lipschitzWith hnorm).dist_le_mul ((γ : ℝ) • h) h
  -- `v` is the fixed point of the `γ`-contraction `x ↦ T (γ • x)`.
  have hc : ContractingWith γ fun x ↦ T ((γ : ℝ) • x) :=
    ⟨hγ, (hT.isBlackwell_comp_smul γ).lipschitzWith hnorm⟩
  rw [sub_sub, ← dist_eq_norm, dist_comm]
  calc dist u v ≤ dist u (T ((γ : ℝ) • u)) / (1 - γ) := hc.dist_le_of_fixedPoint u hv.symm
    _ ≤ (1 - γ) * ‖h‖ / (1 - γ) := by gcongr
    _ = ‖h‖ := mul_div_cancel_left₀ _ h1.ne'

/-- **The discounted fixed points are `g / (1 - γ)` up to the oscillation of the bias**
[WJLSJ20, Lemma 2]: if `T h = h + g • e` and `v = T (γ • v)` with `γ < 1`, then
`‖v - (g / (1 - γ)) • e‖ ≤ osc_e h`. -/
theorem norm_sub_smul_le_orderUnitOsc (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : IsTopical e T) (hγ : γ < 1) (hv : v = T ((γ : ℝ) • v)) (hh : T h = h + g • e) :
    ‖v - (g / (1 - γ)) • e‖ ≤ orderUnitOsc e h := by
  -- Every `h + c • e` is an additive eigenvector with the same gain `g`.
  have hc (c : ℝ) : ‖v - (g / (1 - γ)) • e‖ ≤ 2 * ‖h + c • e‖ := by
    have hh' : T (h + c • e) = (h + c • e) + g • e := by
      rw [hT.map_add_smul, hh]
      abel
    have := hT.norm_sub_sub_smul_le hnorm hγ hv hh'
    calc ‖v - (g / (1 - γ)) • e‖ = ‖(v - (h + c • e) - (g / (1 - γ)) • e) + (h + c • e)‖ := by
          congr 1
          abel
      _ ≤ ‖v - (h + c • e) - (g / (1 - γ)) • e‖ + ‖h + c • e‖ := norm_add_le _ _
      _ ≤ 2 * ‖h + c • e‖ := by linarith
  -- The infimum of `‖h + c • e‖` over `c` is the quotient norm `osc_e h / 2`.
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨m, c, hmc, hm⟩ := exists_eq_add_smul_and_norm_lt hnorm h (half_pos hε)
  have := hc (-c)
  rw [show h + (-c) • e = m by rw [hmc]; module] at this
  linarith

/-- If `T h = h + g • e`, the discounted fixed points have oscillation at most `2 * osc_e h`. -/
theorem orderUnitOsc_le_two_mul_orderUnitOsc (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : IsTopical e T) (hγ : γ < 1) (hv : v = T ((γ : ℝ) • v)) (hh : T h = h + g • e) :
    orderUnitOsc e v ≤ 2 * orderUnitOsc e h := by
  have he := isOrderUnit_of_forall_orderUnitNorm_eq_norm hnorm
  calc orderUnitOsc e v = orderUnitOsc e (v - (g / (1 - γ)) • e) := by
        rw [sub_eq_add_neg, ← neg_smul, orderUnitOsc_add_smul]
    _ ≤ 2 * orderUnitNorm e (v - (g / (1 - γ)) • e) := orderUnitOsc_le_two_mul_orderUnitNorm he _
    _ ≤ 2 * orderUnitOsc e h := by
        rw [hnorm]
        gcongr
        exact hT.norm_sub_smul_le_orderUnitOsc hnorm hγ hv hh

/-- **The gain is the limit of the normalised discounted fixed points**: if `T h = h + g • e`
and `v γ = T (γ • v γ)` for every `γ < 1`, then `(1 - γ) • v γ → g • e` as `γ ↑ 1`. -/
theorem tendsto_one_sub_smul (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : IsTopical e T)
    {v : ℝ≥0 → E} (hv : ∀ γ < 1, v γ = T ((γ : ℝ) • v γ)) (hh : T h = h + g • e) :
    Tendsto (fun γ : ℝ≥0 ↦ (1 - (γ : ℝ)) • v γ) (𝓝[<] 1) (𝓝 (g • e)) := by
  have hbound : ∀ᶠ γ : ℝ≥0 in 𝓝[<] 1,
      ‖(1 - (γ : ℝ)) • v γ - g • e‖ ≤ (1 - (γ : ℝ)) * orderUnitOsc e h := by
    filter_upwards [self_mem_nhdsWithin] with γ (hγ : γ < 1)
    have h1 : (0 : ℝ) < 1 - γ := sub_pos.2 (mod_cast hγ)
    calc ‖(1 - (γ : ℝ)) • v γ - g • e‖ = ‖(1 - (γ : ℝ)) • (v γ - (g / (1 - γ)) • e)‖ := by
          rw [smul_sub, smul_smul, mul_div_cancel₀ _ h1.ne']
      _ = (1 - γ) * ‖v γ - (g / (1 - γ)) • e‖ := by rw [norm_smul, Real.norm_of_nonneg h1.le]
      _ ≤ (1 - γ) * orderUnitOsc e h := by
          gcongr
          exact hT.norm_sub_smul_le_orderUnitOsc hnorm hγ (hv γ hγ) hh
  have hlim : Tendsto (fun γ : ℝ≥0 ↦ (1 - (γ : ℝ)) * orderUnitOsc e h) (𝓝[<] 1) (𝓝 0) := by
    have := ((continuous_const.sub NNReal.continuous_coe).mul continuous_const).tendsto
      (f := fun γ : ℝ≥0 ↦ (1 - (γ : ℝ)) * orderUnitOsc e h) 1
    simpa using this.mono_left nhdsWithin_le_nhds
  exact tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' hbound hlim)

/-! ### Existence of an additive eigenvector -/

/-- **Vanishing discount** [Koh80], [LS, Theorem 38.2]: let `T` be a topical map of a proper
ordered normed space whose norm is the order-unit norm of `e`, and let `v γ = T (γ • v γ)` for
every `γ < 1`. If the oscillations `osc_e (v γ)` are bounded by `B`, then there are `g : ℝ` and
`h : E` with `T h = h + g • e` and `osc_e h ≤ B`. -/
theorem exists_map_eq_add_smul_of_orderUnitOsc_le [ProperSpace E]
    (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : IsTopical e T) {v : ℝ≥0 → E}
    (hv : ∀ γ < 1, v γ = T ((γ : ℝ) • v γ)) {B : ℝ} (hB : ∀ γ < 1, orderUnitOsc e (v γ) ≤ B) :
    ∃ (g : ℝ) (h : E), T h = h + g • e ∧ orderUnitOsc e h ≤ B := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨0, v 0, Subsingleton.elim _ _, hB 0 zero_lt_one⟩
  have he0 : 0 < ‖e‖ :=
    norm_pos_iff.2 (isOrderUnit_of_forall_orderUnitNorm_eq_norm hnorm).ne_zero
  -- Discounts `γ k` increasing to `1`.
  obtain ⟨γ, -, hγ1, hγ⟩ := exists_seq_strictMono_tendsto' (zero_lt_one : (0 : ℝ≥0) < 1)
  -- Write `v (γ k) = m k + c k • e` with `‖m k‖ < osc_e (v (γ k)) / 2 + 1 ≤ B / 2 + 1`.
  choose m c hvm hm using fun k ↦ exists_eq_add_smul_and_norm_lt hnorm (v (γ k)) one_pos
  have hm' (k : ℕ) : ‖m k‖ ≤ B / 2 + 1 := by linarith [hm k, hB _ (hγ1 k).2]
  -- The rescaled constants `a k = (1 - γ k) * c k` are bounded.
  set a : ℕ → ℝ := fun k ↦ (1 - (γ k : ℝ)) * c k with ha
  have hab (k : ℕ) : |a k| ≤ (‖T 0‖ + (B / 2 + 1)) / ‖e‖ := by
    rw [le_div_iff₀ he0]
    linarith [abs_one_sub_mul_mul_norm_le hnorm hT (hγ1 k).2.le (hv _ (hγ1 k).2) (hvm k), hm' k]
  -- A limit point `(h, g)` of `(m k, a k)`.
  obtain ⟨⟨h, g⟩, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (x := fun k ↦ (m k, a k))
    (Metric.isBounded_closedBall (x := 0)
      (r := max (B / 2 + 1) ((‖T 0‖ + (B / 2 + 1)) / ‖e‖)))
    fun k ↦ by
      rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs]
      exact max_le_max (hm' k) (hab k)
  have hmφ : Tendsto (m ∘ φ) atTop (𝓝 h) := (continuous_fst.tendsto _).comp hlim
  have haφ : Tendsto (a ∘ φ) atTop (𝓝 g) := (continuous_snd.tendsto _).comp hlim
  have hγφ : Tendsto (fun k ↦ (γ (φ k) : ℝ)) atTop (𝓝 1) :=
    (NNReal.tendsto_coe.2 hγ).comp hφ.tendsto_atTop
  refine ⟨g, h, ?_, ?_⟩
  · -- The fixed-point equation `T (γ k • m k) = m k + a k • e` passes to the limit along `φ`.
    have heq (k : ℕ) : T ((γ k : ℝ) • m k) = m k + a k • e :=
      map_smul_eq_add_smul hT (hv _ (hγ1 k).2) (hvm k)
    have hl : Tendsto (fun k ↦ m (φ k) + a (φ k) • e) atTop (𝓝 (h + g • e)) :=
      hmφ.add (haφ.smul_const e)
    have hr : Tendsto (fun k ↦ T ((γ (φ k) : ℝ) • m (φ k))) atTop (𝓝 (T h)) := by
      have : Tendsto (fun k ↦ (γ (φ k) : ℝ) • m (φ k)) atTop (𝓝 h) := by
        simpa using hγφ.smul hmφ
      exact ((hT.lipschitzWith hnorm).continuous.tendsto h).comp this
    exact tendsto_nhds_unique hr (by simpa only [heq] using hl)
  · -- The bound `osc_e (m k) = osc_e (v (γ k)) ≤ B` passes to the limit.
    refine le_of_tendsto' (((continuous_orderUnitOsc hnorm).tendsto h).comp hmφ) fun k ↦ ?_
    rw [comp_apply, comp_apply, ← orderUnitOsc_add_smul e _ (c (φ k)), ← hvm]
    exact hB _ (hγ1 _).2

/-- **Existence of an additive eigenvector by vanishing discount**: for a topical map of a proper
ordered normed space whose norm is the order-unit norm of `e`, and fixed points
`v γ = T (γ • v γ)` for every `γ < 1`, there are `g` and `h` with `T h = h + g • e` if and only if
the oscillations `osc_e (v γ)`, `γ < 1`, are bounded. -/
theorem exists_map_eq_add_smul_iff_bddAbove [ProperSpace E]
    (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : IsTopical e T) {v : ℝ≥0 → E}
    (hv : ∀ γ < 1, v γ = T ((γ : ℝ) • v γ)) :
    (∃ (g : ℝ) (h : E), T h = h + g • e) ↔
      BddAbove (range fun γ : Iio (1 : ℝ≥0) ↦ orderUnitOsc e (v γ)) := by
  constructor
  · rintro ⟨g, h, hh⟩
    refine ⟨2 * orderUnitOsc e h, ?_⟩
    rintro _ ⟨γ, rfl⟩
    exact hT.orderUnitOsc_le_two_mul_orderUnitOsc hnorm γ.property (hv γ γ.property) hh
  · rintro ⟨B, hB⟩
    obtain ⟨g, h, hh, -⟩ := hT.exists_map_eq_add_smul_of_orderUnitOsc_le hnorm hv
      fun γ hγ ↦ hB ⟨⟨γ, hγ⟩, rfl⟩
    exact ⟨g, h, hh⟩

end IsTopical

end LMLExplore
