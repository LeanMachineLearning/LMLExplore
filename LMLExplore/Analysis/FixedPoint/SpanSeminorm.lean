/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.FixedPoint.OrderUnit
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# The span seminorm, additive eigenvectors and relative value iteration

Let `E` be an ordered real Banach space with an order unit `e` whose order-unit norm is the norm
(`ι → ℝ` with `ι` finite and `e = 1`, or the bounded measurable functions
`LMLExplore.boundedMeasurable 𝓢`). The oscillation `osc x = LMLExplore.orderUnitOsc e x`, the
*span* `sup x - inf x` when `e = 1`, is a seminorm vanishing on the multiples of `e`. On the
quotient `E ⧸ ℝ ∙ e` by these multiples, Mathlib's quotient norm is `osc / 2`
(`LMLExplore.norm_mk_span_singleton`): the quotient is a Banach space for half the span.

A topical map `T` (monotone, with `T (x + c • e) = T x + c • e`) descends to this quotient
(`LMLExplore.IsTopical.quotientMap`), where it is nonexpansive since `T` is nonexpansive for the
oscillation. Suppose that some iterate contracts the span:
`osc (T^[J] x - T^[J] y) ≤ α * osc (x - y)` with `α < 1`. Then `T^[J]` is a contraction of the
quotient, whose fixed point is fixed by `T`: there are `g : ℝ` and `h : E` with
`T h = h + g • e` (`LMLExplore.IsTopical.exists_map_eq_add_smul`). This is the *average-reward
optimality equation* when `T` is the undiscounted Bellman operator of an MDP: `g` is the optimal
gain and `h` a bias (relative value) [P, §8.5]. The pair is unique up to adding a multiple
of `e` to `h` (`LMLExplore.IsTopical.eq_add_smul_of_map_eq_add_smul`,
`LMLExplore.IsTopical.eq_of_map_eq_add_smul`).

*Relative value iteration* [P, §8.5] computes such a pair. Fix a normalisation `N : E → ℝ` that
is monotone with `N (x + c • e) = N x + c`, such as the evaluation at a reference state `s₀`, and
iterate `x (n + 1) = T (x n) - N (T (x n)) • e` (`LMLExplore.relativeValueIteration`). It is value
iteration `T^[n] x₀`, renormalised to `N (x n) = 0`
(`LMLExplore.relativeValueIteration_succ_eq_iterate`). If `T h = h + g • e` with `N h = 0`, then
for every `n`
* `‖x (n + 1) - h‖ ≤ α ^ ((n + 1) / J) * osc (x₀ - h)`, and
* `‖T (x n) - x n - g • e‖ ≤ α ^ (n / J) * osc (x₀ - h)`.

So the iterates converge geometrically to the bias normalised by `N`, and `T (x n) - x n` to the
gain.

## Main definitions

* `LMLExplore.IsTopical.quotientMap`: the map induced by a topical map on `E ⧸ ℝ ∙ e`.
* `LMLExplore.relativeValueIteration e T N x₀`: the iterates of relative value iteration.

## Main statements

* `LMLExplore.norm_mk_span_singleton`: the quotient norm of `E ⧸ ℝ ∙ e` is `osc / 2`.
* `LMLExplore.IsTopical.lipschitzWith_quotientMap`: a topical map is nonexpansive on the quotient.
* `LMLExplore.IsTopical.lipschitzWith_quotientMap_iterate`: if `T^[J]` contracts the span at rate
  `α`, it is `α`-Lipschitz on the quotient.
* `LMLExplore.IsTopical.orderUnitOsc_iterate_sub_le`: then
  `osc (T^[n] x - T^[n] y) ≤ α ^ (n / J) * osc (x - y)`.
* `LMLExplore.IsTopical.exists_map_eq_add_smul`: existence of `g` and `h` with `T h = h + g • e`,
  and `LMLExplore.IsTopical.eq_add_smul_of_map_eq_add_smul` their uniqueness.
* `LMLExplore.norm_relativeValueIteration_succ_sub_le` and
  `LMLExplore.norm_map_relativeValueIteration_sub_sub_le`: the convergence of relative value
  iteration to `h` and of its increments to `g`.

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], Theorem 6.6.2, §8.5
-/

public section

open Function Set Submodule

namespace LMLExplore

variable {E : Type*}

/-! ### Topical maps, the oscillation and the order-unit norm -/

section Order

variable [AddCommGroup E] [PartialOrder E] [Module ℝ E] {e : E} {T : E → E}

/-- If `T h = h + g • e`, then the iterates of a topical map `T` are `T^[n] h = h + (n * g) • e`. -/
theorem IsTopical.iterate_eq_add_smul (hT : IsTopical e T) {h : E} {g : ℝ}
    (hh : T h = h + g • e) (n : ℕ) : T^[n] h = h + ((n : ℝ) * g) • e := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih, hT.map_add_smul, hh, add_assoc, ← add_smul]
    push_cast
    ring_nf

namespace IsTopical

/-- A topical map `T` descends to the quotient `E ⧸ ℝ ∙ e` by the multiples of `e`:
`[x] ↦ [T x]`. -/
noncomputable def quotientMap (hT : IsTopical e T) : E ⧸ ℝ ∙ e → E ⧸ ℝ ∙ e :=
  Quotient.map' T fun x y hxy ↦ by
    rw [Submodule.quotientRel_def] at hxy ⊢
    obtain ⟨c, hc⟩ := mem_span_singleton.1 hxy
    rw [eq_add_of_sub_eq' hc.symm, hT.map_add_smul, add_sub_cancel_left]
    exact smul_mem _ c (mem_span_singleton_self e)

@[simp]
lemma quotientMap_mk (hT : IsTopical e T) (x : E) :
    hT.quotientMap (Submodule.Quotient.mk x) = Submodule.Quotient.mk (T x) :=
  (rfl)

lemma quotientMap_iterate_mk (hT : IsTopical e T) (n : ℕ) (x : E) :
    hT.quotientMap^[n] (Submodule.Quotient.mk x) = Submodule.Quotient.mk (T^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', ih, quotientMap_mk, iterate_succ_apply']

end IsTopical

variable [IsOrderedAddMonoid E]

/-- A topical map changes a difference by at most its oscillation:
`‖(T x - T y) - (x - y)‖_e ≤ osc_e (x - y)`. -/
theorem IsTopical.orderUnitNorm_sub_sub_le (hT : IsTopical e T) (he : IsOrderUnit e) (x y : E) :
    orderUnitNorm e (T x - T y - (x - y)) ≤ orderUnitOsc e (x - y) := by
  refine le_orderUnitOsc he fun d hd a h ↦ orderUnitNorm_le hd ⟨?_, ?_⟩
  -- Both `T x - T y` and `x - y` lie in `[a • e, (a + d) • e]`.
  · rw [neg_le_sub_iff_le_add, ← sub_le_iff_le_add]
    calc x - y - d • e ≤ (a + d) • e - d • e := sub_le_sub_right h.2 _
      _ = a • e := by rw [add_smul, add_sub_cancel_right]
      _ ≤ T x - T y := (hT.sub_mem_Icc_smul h).1
  · rw [sub_le_iff_le_add]
    calc T x - T y ≤ (a + d) • e := (hT.sub_mem_Icc_smul h).2
      _ = d • e + a • e := by rw [add_smul, add_comm]
      _ ≤ d • e + (x - y) := add_le_add_right h.1 _

/-- If a monotone normalisation `N` with `N (x + c • e) = N x + c` takes the same value at `x` and
`y`, then the order-unit norm of `x - y` is at most its oscillation. -/
theorem orderUnitNorm_sub_le_orderUnitOsc_of_eq [PosSMulMono ℝ E] {N : E → ℝ} (hN : Monotone N)
    (hN_add : ∀ x (c : ℝ), N (x + c • e) = N x + c) (he : IsOrderUnit e) {x y : E}
    (hxy : N x = N y) : orderUnitNorm e (x - y) ≤ orderUnitOsc e (x - y) := by
  have hmono {b c : ℝ} (hbc : b ≤ c) : b • e ≤ c • e :=
    sub_nonneg.1 (by rw [← sub_smul]; exact smul_nonneg (sub_nonneg.2 hbc) he.nonneg)
  refine le_orderUnitOsc he fun d hd a h ↦ orderUnitNorm_le hd ?_
  -- Applying `N` to `y + a • e ≤ x ≤ y + (a + d) • e` gives `a ≤ 0 ≤ a + d`.
  have ha : a ≤ 0 := by
    have := hN (le_sub_iff_add_le'.1 h.1)
    rw [hN_add, hxy] at this
    linarith
  have had : 0 ≤ a + d := by
    have := hN (sub_le_iff_le_add'.1 h.2)
    rw [hN_add, hxy] at this
    linarith
  refine ⟨h.1.trans' ?_, h.2.trans (hmono (by linarith))⟩
  rw [← neg_smul]
  exact hmono (by linarith)

variable {α : NNReal} {J : ℕ}

/-- If `T` is topical and its iterate `T^[J]` contracts the oscillation at rate `α`, then
`osc (T^[n] x - T^[n] y) ≤ α ^ (n / J) * osc (x - y)` for every `n`. -/
theorem IsTopical.orderUnitOsc_iterate_sub_le (hT : IsTopical e T) (he : IsOrderUnit e)
    (hJ : ∀ x y, orderUnitOsc e (T^[J] x - T^[J] y) ≤ α * orderUnitOsc e (x - y)) (n : ℕ)
    (x y : E) : orderUnitOsc e (T^[n] x - T^[n] y) ≤ α ^ (n / J) * orderUnitOsc e (x - y) := by
  -- The iterates `T^[J * k]` contract at rate `α ^ k`.
  have hk (k : ℕ) (x y : E) :
      orderUnitOsc e (T^[J * k] x - T^[J * k] y) ≤ α ^ k * orderUnitOsc e (x - y) := by
    induction k generalizing x y with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, iterate_add_apply, iterate_add_apply, pow_succ, mul_assoc]
      exact (ih _ _).trans (mul_le_mul_of_nonneg_left (hJ x y) (by positivity))
  -- The remaining `n % J` steps do not increase the oscillation.
  calc orderUnitOsc e (T^[n] x - T^[n] y)
      = orderUnitOsc e (T^[n % J] (T^[J * (n / J)] x) - T^[n % J] (T^[J * (n / J)] y)) := by
        rw [← iterate_add_apply, ← iterate_add_apply, Nat.mod_add_div]
    _ ≤ orderUnitOsc e (T^[J * (n / J)] x - T^[J * (n / J)] y) :=
        (hT.iterate _).orderUnitOsc_sub_le he _ _
    _ ≤ α ^ (n / J) * orderUnitOsc e (x - y) := hk _ x y

end Order

/-! ### The quotient by the multiples of the order unit -/

section Quotient

variable [NormedAddCommGroup E] [PartialOrder E] [NormedSpace ℝ E] {e : E} {T : E → E}

variable [IsOrderedAddMonoid E]

/-- When the order-unit norm of `e` is the norm, the quotient norm of `E ⧸ ℝ ∙ e` is half the
oscillation: `‖[x]‖ = osc_e x / 2`. For `e = 1` on bounded functions, this is the distance
`(sup x - inf x) / 2` from `x` to the constants. -/
theorem norm_mk_span_singleton (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ ℝ ∙ e)‖ = orderUnitOsc e x / 2 := by
  have he := isOrderUnit_of_forall_orderUnitNorm_eq_norm hnorm
  have hmk (m : E) (c : ℝ) :
      (Submodule.Quotient.mk (m + c • e) : E ⧸ ℝ ∙ e) = Submodule.Quotient.mk m := by
    rw [Submodule.Quotient.eq, add_sub_cancel_left]
    exact smul_mem _ c (mem_span_singleton_self e)
  refine le_antisymm (le_of_forall_gt fun r hr ↦ ?_) (not_lt.1 fun hlt ↦ ?_)
  · -- `x` lies in some `[a • e, (a + d) • e]` with `d < 2 * r`; recentre it at `(a + d / 2) • e`.
    obtain ⟨d, hd, hdr, a, hx⟩ :=
      exists_mem_Icc_smul_of_orderUnitOsc_lt (he.exists_mem_Icc_smul x) (by linarith : _ < 2 * r)
    have hx' : x + (-(a + d / 2)) • e ∈ Icc (-((d / 2) • e)) ((d / 2) • e) := by
      have h₁ : -((d / 2) • e) = a • e + (-(a + d / 2)) • e := by
        rw [← add_smul, ← neg_smul]; congr 1; ring
      have h₂ : (d / 2) • e = (a + d) • e + (-(a + d / 2)) • e := by
        rw [← add_smul]; congr 1; ring
      rw [h₁, h₂]
      exact ⟨add_le_add_left hx.1 _, add_le_add_left hx.2 _⟩
    calc ‖(Submodule.Quotient.mk x : E ⧸ ℝ ∙ e)‖
        = ‖(Submodule.Quotient.mk (x + (-(a + d / 2)) • e) : E ⧸ ℝ ∙ e)‖ := by rw [hmk]
      _ ≤ ‖x + (-(a + d / 2)) • e‖ := Submodule.Quotient.norm_mk_le _ _
      _ ≤ d / 2 := (hnorm _).symm.trans_le (orderUnitNorm_le (by positivity) hx')
      _ < r := by linarith
  · -- A representative `m = x - c • e` of norm below `osc_e x / 2` would have `osc_e m < osc_e x`.
    obtain ⟨m, hm, hm'⟩ := Submodule.Quotient.norm_mk_lt (Submodule.Quotient.mk x : E ⧸ ℝ ∙ e)
      (sub_pos.2 hlt)
    obtain ⟨c, hc⟩ := mem_span_singleton.1 ((Submodule.Quotient.eq _).1 hm.symm)
    have := orderUnitOsc_le_two_mul_orderUnitNorm he m
    rw [hnorm, ← orderUnitOsc_add_smul e m c, hc, add_sub_cancel] at this
    linarith

namespace IsTopical

/-- If `T^[J]` contracts the oscillation at rate `α`, then it is `α`-Lipschitz on the quotient
`E ⧸ ℝ ∙ e`. For `α < 1` it is a contraction there. -/
theorem lipschitzWith_quotientMap_iterate (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : IsTopical e T) {α : NNReal} {J : ℕ}
    (hJ : ∀ x y, orderUnitOsc e (T^[J] x - T^[J] y) ≤ α * orderUnitOsc e (x - y)) :
    LipschitzWith α hT.quotientMap^[J] := by
  refine LipschitzWith.of_dist_le_mul fun p q ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ p
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp only [dist_eq_norm, quotientMap_iterate_mk, ← Submodule.Quotient.mk_sub,
    norm_mk_span_singleton hnorm, mul_div_assoc']
  gcongr
  exact hJ x y

/-- A topical map is nonexpansive on the quotient `E ⧸ ℝ ∙ e`, when the order-unit norm of `e` is
the norm. -/
theorem lipschitzWith_quotientMap (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : IsTopical e T) :
    LipschitzWith 1 hT.quotientMap := by
  simpa using hT.lipschitzWith_quotientMap_iterate hnorm (J := 1) fun x y ↦ by
    simpa using hT.orderUnitOsc_sub_le (isOrderUnit_of_forall_orderUnitNorm_eq_norm hnorm) x y

variable {α : NNReal} {J : ℕ}

/-- If `T^[J]` contracts the oscillation at rate `α < 1`, then it is a contraction of the quotient
`E ⧸ ℝ ∙ e`, for the normed group structure given by the closedness of `ℝ ∙ e`. -/
private lemma contractingWith_quotientMap_iterate (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : IsTopical e T) (hα : α < 1)
    (hJ : ∀ x y, orderUnitOsc e (T^[J] x - T^[J] y) ≤ α * orderUnitOsc e (x - y)) :
    letI : IsClosed ((ℝ ∙ e : Submodule ℝ E) : Set E) := (ℝ ∙ e).isClosed_of_finiteDimensional
    ContractingWith α hT.quotientMap^[J] :=
  ⟨hα, hT.lipschitzWith_quotientMap_iterate hnorm hJ⟩

/-- **Existence of an additive eigenvector** [P, Theorem 6.6.2, §8.5]: if a topical map `T` of an
ordered Banach space, whose norm is the order-unit norm of `e`, has an iterate `T^[J]` that
contracts the oscillation at rate `α < 1`, then there are `g : ℝ` and `h : E` with
`T h = h + g • e`. For an undiscounted Bellman operator, this is the average-reward optimality
equation with gain `g` and bias `h`. -/
theorem exists_map_eq_add_smul [CompleteSpace E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : IsTopical e T) (hα : α < 1)
    (hJ : ∀ x y, orderUnitOsc e (T^[J] x - T^[J] y) ≤ α * orderUnitOsc e (x - y)) :
    ∃ (g : ℝ) (h : E), T h = h + g • e := by
  have : IsClosed ((ℝ ∙ e : Submodule ℝ E) : Set E) := (ℝ ∙ e).isClosed_of_finiteDimensional
  have hc := hT.contractingWith_quotientMap_iterate hnorm hα hJ
  -- The fixed point of the contraction `T^[J]` of the quotient is fixed by `T`.
  obtain ⟨h, hh⟩ := Submodule.Quotient.mk_surjective _ (hc.fixedPoint _)
  have hfix := hc.isFixedPt_fixedPoint_iterate
  rw [← hh, IsFixedPt, quotientMap_mk, Submodule.Quotient.eq] at hfix
  obtain ⟨g, hg⟩ := mem_span_singleton.1 hfix
  exact ⟨g, h, eq_add_of_sub_eq' hg.symm⟩

/-- **Uniqueness of the bias up to constants**: under the contraction hypothesis of
`exists_map_eq_add_smul`, if `T h = h + g • e` and `T h' = h' + g' • e`, then `h'` differs from
`h` by a multiple of `e`. -/
theorem eq_add_smul_of_map_eq_add_smul (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : IsTopical e T) (hα : α < 1)
    (hJ : ∀ x y, orderUnitOsc e (T^[J] x - T^[J] y) ≤ α * orderUnitOsc e (x - y)) {g g' : ℝ}
    {h h' : E} (hh : T h = h + g • e) (hh' : T h' = h' + g' • e) : ∃ c : ℝ, h' = h + c • e := by
  have : IsClosed ((ℝ ∙ e : Submodule ℝ E) : Set E) := (ℝ ∙ e).isClosed_of_finiteDimensional
  have hc := hT.contractingWith_quotientMap_iterate hnorm hα hJ
  -- `[h]` and `[h']` are fixed points of `T` on the quotient, hence of its contraction `T^[J]`.
  have hfix {k : E} {b : ℝ} (hk : T k = k + b • e) :
      IsFixedPt hT.quotientMap^[J] (Submodule.Quotient.mk k) := by
    refine IsFixedPt.iterate ?_ J
    rw [IsFixedPt, quotientMap_mk, hk, Submodule.Quotient.eq, add_sub_cancel_left]
    exact smul_mem _ b (mem_span_singleton_self e)
  have := hc.fixedPoint_unique' (hfix hh') (hfix hh)
  obtain ⟨c, hc⟩ := mem_span_singleton.1 ((Submodule.Quotient.eq _).1 this)
  exact ⟨c, eq_add_of_sub_eq' hc.symm⟩

/-- **Uniqueness of the gain**: under the contraction hypothesis of `exists_map_eq_add_smul`, in a
nontrivial space, if `T h = h + g • e` and `T h' = h' + g' • e`, then `g' = g`. -/
theorem eq_of_map_eq_add_smul [Nontrivial E] (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : IsTopical e T) (hα : α < 1)
    (hJ : ∀ x y, orderUnitOsc e (T^[J] x - T^[J] y) ≤ α * orderUnitOsc e (x - y)) {g g' : ℝ}
    {h h' : E} (hh : T h = h + g • e) (hh' : T h' = h' + g' • e) : g' = g := by
  -- The order unit is nonzero, since every element lies in `[-c • e, c • e]`.
  have he : e ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    obtain ⟨c, -, hx₁, hx₂⟩ :=
      isOrderUnit_def.1 (isOrderUnit_of_forall_orderUnitNorm_eq_norm hnorm) x
    exact hx (le_antisymm (by simpa using hx₂) (by simpa using hx₁))
  obtain ⟨c, rfl⟩ := hT.eq_add_smul_of_map_eq_add_smul hnorm hα hJ hh hh'
  rw [hT.map_add_smul, hh, add_right_comm, add_assoc, add_assoc, ← add_smul, ← add_smul,
    add_right_inj] at hh'
  have := smul_left_injective ℝ he hh'
  linarith

end IsTopical

end Quotient

/-! ### Relative value iteration -/

section RelativeValueIteration

section Defs

variable [AddCommGroup E] [Module ℝ E] {e : E} {T : E → E} {N : E → ℝ} {x₀ : E}

variable (e T N x₀) in
/-- **Relative value iteration** [P, §8.5] for a map `T`, a normalisation `N : E → ℝ` and a unit
`e`, started at `x₀`: `x 0 = x₀` and `x (n + 1) = T (x n) - N (T (x n)) • e`. On functions of the
states, with `e = 1` and `N` the evaluation at a reference state `s₀`, each step applies `T` and
subtracts the resulting value at `s₀`. -/
noncomputable def relativeValueIteration : ℕ → E
  | 0 => x₀
  | n + 1 => T (relativeValueIteration n) - N (T (relativeValueIteration n)) • e

@[simp]
lemma relativeValueIteration_zero : relativeValueIteration e T N x₀ 0 = x₀ := by
  rw [relativeValueIteration]

lemma relativeValueIteration_succ (n : ℕ) :
    relativeValueIteration e T N x₀ (n + 1) =
      T (relativeValueIteration e T N x₀ n) - N (T (relativeValueIteration e T N x₀ n)) • e := by
  rw [relativeValueIteration]

/-- The iterates of relative value iteration are normalised: `N (x (n + 1)) = 0`, when
`N (x + c • e) = N x + c`. -/
lemma apply_relativeValueIteration_succ_eq_zero (hN_add : ∀ x (c : ℝ), N (x + c • e) = N x + c)
    (n : ℕ) : N (relativeValueIteration e T N x₀ (n + 1)) = 0 := by
  rw [relativeValueIteration_succ, sub_eq_add_neg, ← neg_smul, hN_add, add_neg_cancel]

variable [PartialOrder E]

/-- For a topical map, relative value iteration is value iteration renormalised:
`x (n + 1) = T^[n + 1] x₀ - N (T^[n + 1] x₀) • e`. -/
theorem relativeValueIteration_succ_eq_iterate (hT : IsTopical e T)
    (hN_add : ∀ x (c : ℝ), N (x + c • e) = N x + c) (n : ℕ) :
    relativeValueIteration e T N x₀ (n + 1) = T^[n + 1] x₀ - N (T^[n + 1] x₀) • e := by
  induction n with
  | zero => rw [relativeValueIteration_succ, relativeValueIteration_zero, iterate_one]
  | succ n ih =>
    rw [relativeValueIteration_succ, ih, hT.map_sub_smul, sub_eq_add_neg (T _), ← neg_smul,
      hN_add, iterate_succ_apply' T (n + 1), neg_smul, ← sub_eq_add_neg, sub_sub, ← add_smul]
    congr 2
    ring

/-- For a topical map, the iterates of relative value iteration differ from those of value
iteration by multiples of `e`. -/
theorem exists_relativeValueIteration_eq_iterate_add_smul (hT : IsTopical e T)
    (hN_add : ∀ x (c : ℝ), N (x + c • e) = N x + c) (n : ℕ) :
    ∃ c : ℝ, relativeValueIteration e T N x₀ n = T^[n] x₀ + c • e := by
  cases n with
  | zero => exact ⟨0, by simp⟩
  | succ n =>
    exact ⟨-N (T^[n + 1] x₀), by
      rw [relativeValueIteration_succ_eq_iterate hT hN_add, neg_smul, sub_eq_add_neg]⟩

end Defs

variable [NormedAddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [NormedSpace ℝ E]
  {e : E} {T : E → E} {N : E → ℝ} {x₀ h : E} {g : ℝ} {α : NNReal} {J : ℕ}

/-- If `T^[J]` contracts the oscillation at rate `α` and `T h = h + g • e`, the iterates of relative
value iteration satisfy `osc (x n - h) ≤ α ^ (n / J) * osc (x₀ - h)`. -/
theorem orderUnitOsc_relativeValueIteration_sub_le (hT : IsTopical e T) (he : IsOrderUnit e)
    (hN_add : ∀ x (c : ℝ), N (x + c • e) = N x + c)
    (hJ : ∀ x y, orderUnitOsc e (T^[J] x - T^[J] y) ≤ α * orderUnitOsc e (x - y))
    (hh : T h = h + g • e) (n : ℕ) :
    orderUnitOsc e (relativeValueIteration e T N x₀ n - h) ≤
      α ^ (n / J) * orderUnitOsc e (x₀ - h) := by
  obtain ⟨c, hc⟩ := exists_relativeValueIteration_eq_iterate_add_smul (x₀ := x₀) hT hN_add n
  -- Up to multiples of `e`, `x n - h` is `T^[n] x₀ - T^[n] h`.
  have hsub : relativeValueIteration e T N x₀ n - h =
      (T^[n] x₀ - T^[n] h) + (c + (n : ℝ) * g) • e := by
    rw [hc, hT.iterate_eq_add_smul hh n, add_smul]
    abel
  rw [hsub, orderUnitOsc_add_smul]
  exact hT.orderUnitOsc_iterate_sub_le he hJ n x₀ h

/-- **Convergence of relative value iteration** [P, §8.5]: let `T` be a topical map whose
iterate `T^[J]` contracts the oscillation at rate `α`, in an ordered normed space whose norm is the
order-unit norm of `e`. Let `N` be a monotone normalisation with `N (x + c • e) = N x + c`, and let
`T h = h + g • e` with `N h = 0`. Then the iterates of relative value iteration satisfy
`‖x (n + 1) - h‖ ≤ α ^ ((n + 1) / J) * osc (x₀ - h)`. -/
theorem norm_relativeValueIteration_succ_sub_le [PosSMulMono ℝ E]
    (hnorm : ∀ x, orderUnitNorm e x = ‖x‖) (hT : IsTopical e T) (hN : Monotone N)
    (hN_add : ∀ x (c : ℝ), N (x + c • e) = N x + c)
    (hJ : ∀ x y, orderUnitOsc e (T^[J] x - T^[J] y) ≤ α * orderUnitOsc e (x - y))
    (hh : T h = h + g • e) (hNh : N h = 0) (n : ℕ) :
    ‖relativeValueIteration e T N x₀ (n + 1) - h‖ ≤
      α ^ ((n + 1) / J) * orderUnitOsc e (x₀ - h) := by
  have he := isOrderUnit_of_forall_orderUnitNorm_eq_norm hnorm
  rw [← hnorm]
  refine (orderUnitNorm_sub_le_orderUnitOsc_of_eq hN hN_add he ?_).trans
    (orderUnitOsc_relativeValueIteration_sub_le hT he hN_add hJ hh (n + 1))
  rw [apply_relativeValueIteration_succ_eq_zero hN_add, hNh]

/-- **Convergence of the increments of relative value iteration** [P, §8.5]: under the
hypotheses of `norm_relativeValueIteration_succ_sub_le`, without monotonicity of `N` or `N h = 0`,
`‖T (x n) - x n - g • e‖ ≤ α ^ (n / J) * osc (x₀ - h)` for every `n`. So `T (x n) - x n` converges
to the gain `g • e`. -/
theorem norm_map_relativeValueIteration_sub_sub_le (hnorm : ∀ x, orderUnitNorm e x = ‖x‖)
    (hT : IsTopical e T) (hN_add : ∀ x (c : ℝ), N (x + c • e) = N x + c)
    (hJ : ∀ x y, orderUnitOsc e (T^[J] x - T^[J] y) ≤ α * orderUnitOsc e (x - y))
    (hh : T h = h + g • e) (n : ℕ) :
    ‖T (relativeValueIteration e T N x₀ n) - relativeValueIteration e T N x₀ n - g • e‖ ≤
      α ^ (n / J) * orderUnitOsc e (x₀ - h) := by
  have he := isOrderUnit_of_forall_orderUnitNorm_eq_norm hnorm
  set x := relativeValueIteration e T N x₀ n
  -- `T x - x - g • e = (T x - T h) - (x - h)`, which `T` keeps within the oscillation of `x - h`.
  have hx : T x - x - g • e = T x - T h - (x - h) := by
    rw [hh]
    abel
  rw [← hnorm, hx]
  exact (hT.orderUnitNorm_sub_sub_le he x h).trans
    (orderUnitOsc_relativeValueIteration_sub_le hT he hN_add hJ hh n)

end RelativeValueIteration

end LMLExplore
