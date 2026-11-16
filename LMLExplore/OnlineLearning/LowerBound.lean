/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Normed.Module.RademacherSum
public import LMLExplore.OnlineLearning.Learner.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The lower bound of bounded online linear optimization

In online linear optimization on a real normed space `E`, a learner plays `x t ∈ E` and then
suffers the loss `y t (x t)` of a linear loss `y t : E →L[ℝ] ℝ` of dual norm at most `L`. Whatever
the learner, an adversary can force, against one of any two comparators `v` and `w`, the regret
`L / 2 * ‖v - w‖ * 𝔼 |∑ t < n, ε t|`, where the `ε t` are independent Rademacher signs, and hence
the regret `L / 2 * ‖v - w‖ * √(n / 3)` [Ora, Theorem 5.1, Problem 5.2]. Online subgradient
descent on a set of diameter `D` has regret at most of order `L D √n`, so this is optimal up to a
constant factor.

The proof is the probabilistic method. Let `z` be a functional of norm at most `1` with
`z (v - w) = ‖v - w‖` (Hahn–Banach), and let the adversary play `y t = L ε t z` with random signs
`ε t`. The play `x t` depends only on the signs of the rounds `s < t`, so the expected loss
`𝔼 ∑ t, L ε t z (x t)` of every learner vanishes (`expect_sum_units_apply_mul_eq_zero`), while the
better of the comparators `v` and `w` has expected loss
`-𝔼 max (L S z v, L S z w) ≤ -L / 2 * ‖v - w‖ * 𝔼 |S|`, with `S = ∑ t, ε t`, as
`max a b = (a + b) / 2 + |a - b| / 2`. Some sequence of signs does at least as well as the average.

The signs are averaged uniformly over the sign cube `Fin n → ℤˣ`. The bound holds for every learner
of `OnlineLearner`, and for the expected regret of a randomized learner, a family of learners
`A ω` indexed by its internal randomness `ω`, independent of the signs [Ora, Remark 5.3]. No
constraint set is needed: the learner may play anywhere in `E`, and the comparators are `v` and
`w`. With `w = -u`, the bound is the regret `L * ‖u‖ * 𝔼 |∑ t < n, ε t|` against `u` or `-u` of
unconstrained online linear optimization [Ora, Problem 5.1].

## Main statements

* `OnlineLearner.exists_mul_expect_abs_sum_le_regret_run`: the lower bound, for a deterministic
  learner.
* `OnlineLearner.exists_mul_sqrt_le_regret_run`: its form `L / 2 * ‖v - w‖ * √(n / 3)`.
* `exists_mul_expect_abs_sum_le_integral_regret_run`,
  `exists_mul_sqrt_le_integral_regret_run`: the lower bound for the expected regret of a
  randomized learner.
* `OnlineLearner.exists_mul_norm_mul_expect_abs_sum_le_regret_run`: the unconstrained form,
  against `u` or `-u`.
* `OnlineLearner.HasRegretBound.div_two_mul_norm_sub_mul_sqrt_le`: a regret guarantee `R n` for
  linear losses of dual norm at most `L` against comparators `v` and `w` is at least
  `L / 2 * ‖v - w‖ * √(n / 3)`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Finset MeasureTheory
open scoped BigOperators

namespace LMLExplore.OnlineLearning

variable {C E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Signs

variable {L : ℝ} {z : E →L[ℝ] ℝ} {n : ℕ}

/-- The linear losses `L ε t z` of the rounds `t < n` for the signs `ε`, and `0` after. -/
private noncomputable def signedLosses (L : ℝ) (z : E →L[ℝ] ℝ) (ε : Fin n → ℤˣ) (t : ℕ) :
    E →L[ℝ] ℝ :=
  if h : t < n then (L * ((ε ⟨t, h⟩ : ℤ) : ℝ)) • z else 0

private lemma norm_signedLosses_le (hL : 0 ≤ L) (hz : ‖z‖ ≤ 1) (ε : Fin n → ℤˣ) (t : ℕ) :
    ‖signedLosses L z ε t‖ ≤ L := by
  unfold signedLosses
  split_ifs with h
  · have hε : |((ε ⟨t, h⟩ : ℤ) : ℝ)| = 1 := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.natAbs_of_isUnit (ε _).isUnit]
      simp
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hL, hε, mul_one]
    exact mul_le_of_le_one_right hL hz
  · simpa using hL

/-- The losses of the rounds `s < t` depend only on the signs of these rounds. -/
private lemma signedLosses_congr {ε ε' : Fin n → ℤˣ} {t : Fin n} (h : ∀ j < t, ε j = ε' j)
    {s : ℕ} (hs : s < t) : signedLosses L z ε s = signedLosses L z ε' s := by
  unfold signedLosses
  split_ifs with hsn
  · rw [h ⟨s, hsn⟩ (Fin.lt_def.mpr hs)]
  · rfl

/-- The regret for the signed losses. -/
private lemma regret_signedLosses (ε : Fin n → ℤˣ) (x : ℕ → E) (u : E) :
    regret (fun t ↦ signedLosses L z ε t) x u n =
      L * ∑ t : Fin n, ((ε t : ℤ) : ℝ) * (z (x t) - z u) := by
  rw [regret_eq_sum_apply_sub, ← Fin.sum_univ_eq_sum_range, mul_sum]
  refine sum_congr rfl fun t _ ↦ ?_
  simp only [signedLosses, t.isLt, dite_true, Fin.eta]
  simp only [FunLike.coe_smul, Pi.smul_apply, map_sub, smul_eq_mul]
  ring

/-- The probabilistic method of the lower bound: if the (expected) regret `R ε u` of a learner
for the signed losses of the signs `ε` is `L * ∑ t, ε t * (a ε t - z u)` with `a` predictable,
then some signs force the regret `L / 2 * ‖v - w‖ * 𝔼 |∑ t, ε t|` against `v` or `w`. -/
private lemma exists_mul_expect_abs_sum_le {v w : E} (hz : z (v - w) = ‖v - w‖)
    {a : (Fin n → ℤˣ) → Fin n → ℝ}
    (ha : ∀ (ε ε' : Fin n → ℤˣ) (t : Fin n), (∀ s < t, ε s = ε' s) → a ε t = a ε' t)
    {R : (Fin n → ℤˣ) → E → ℝ}
    (hR : ∀ ε u, R ε u = L * ∑ t, ((ε t : ℤ) : ℝ) * (a ε t - z u)) :
    ∃ ε, ∃ u ∈ ({v, w} : Set E),
      L / 2 * ‖v - w‖ * 𝔼 ε : Fin n → ℤˣ, |∑ t, ((ε t : ℤ) : ℝ)| ≤ R ε u := by
  have hzvw : ‖v - w‖ = z v - z w := by rw [← hz, map_sub]
  have hS : 𝔼 ε : Fin n → ℤˣ, ∑ t, ((ε t : ℤ) : ℝ) = 0 := by
    rw [expect_sum_comm]
    exact sum_eq_zero fun t _ ↦ expect_units_apply t
  -- pointwise, the better comparator gains at least
  -- `L * ∑ t, ε t * a ε t - L (z v + z w) / 2 * S + L / 2 * ‖v - w‖ * |S|`, with `S = ∑ t, ε t`
  have key (ε : Fin n → ℤˣ) : L * ∑ t, ((ε t : ℤ) : ℝ) * a ε t -
      L * (z v + z w) / 2 * ∑ t, ((ε t : ℤ) : ℝ) +
        L / 2 * ‖v - w‖ * |∑ t, ((ε t : ℤ) : ℝ)| ≤ max (R ε v) (R ε w) := by
    have hRu (u : E) : R ε u = L * ∑ t, ((ε t : ℤ) : ℝ) * a ε t -
        L * z u * ∑ t, ((ε t : ℤ) : ℝ) := by
      simp only [hR, mul_sub, sum_sub_distrib, mul_sum]
      congr 1
      exact sum_congr rfl fun t _ ↦ by ring
    rw [hRu, hRu, hzvw]
    rcases le_total 0 (∑ t, ((ε t : ℤ) : ℝ)) with h | h
    · rw [abs_of_nonneg h]
      exact le_max_of_le_right (le_of_eq (by ring))
    · rw [abs_of_nonpos h]
      exact le_max_of_le_left (le_of_eq (by ring))
  have hmean : L / 2 * ‖v - w‖ * 𝔼 ε : Fin n → ℤˣ, |∑ t, ((ε t : ℤ) : ℝ)| ≤
      𝔼 ε : Fin n → ℤˣ, max (R ε v) (R ε w) := by
    refine le_trans (le_of_eq ?_) (expect_le_expect fun ε _ ↦ key ε)
    rw [expect_add_distrib, expect_sub_distrib, ← mul_expect, ← mul_expect, ← mul_expect,
      expect_sum_units_apply_mul_eq_zero ha, hS]
    ring
  obtain ⟨ε, -, hε⟩ := exists_le_of_le_expect univ_nonempty hmean
  rcases le_total (R ε v) (R ε w) with h | h
  · exact ⟨ε, w, by simp, hε.trans (max_eq_right h).le⟩
  · exact ⟨ε, v, by simp, hε.trans (max_eq_left h).le⟩

end Signs

omit [NormedSpace ℝ E] in
/-- `√(n / 3) ≤ 𝔼 |∑ t < n, ε t|`, scaled by `L / 2 * ‖v - w‖`. -/
private lemma mul_sqrt_le_mul_expect_abs_sum {L : ℝ} (hL : 0 ≤ L) (v w : E) (n : ℕ) :
    L / 2 * ‖v - w‖ * √((n : ℝ) / 3) ≤
      L / 2 * ‖v - w‖ * 𝔼 ε : Fin n → ℤˣ, |∑ t, ((ε t : ℤ) : ℝ)| := by
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  simpa using sqrt_card_div_three_le_expect_abs_sum_units (univ : Finset (Fin n))

namespace OnlineLearner

/-- **The lower bound of bounded online linear optimization** [Ora, Theorem 5.1, Problem 5.2].
For every learner `A` for linear losses on a real normed space, all contexts `c`, all `v` and `w`
and every horizon `n`, there are linear losses of dual norm at most `L` and a comparator
`u ∈ {v, w}` against which the regret of `A` after `n` rounds is at least
`L / 2 * ‖v - w‖ * 𝔼 |∑ t < n, ε t|`, for independent Rademacher signs `ε t`. -/
theorem exists_mul_expect_abs_sum_le_regret_run (A : OnlineLearner C (E →L[ℝ] ℝ) E) (c : ℕ → C)
    (v w : E) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    ∃ y : ℕ → E →L[ℝ] ℝ, (∀ t, ‖y t‖ ≤ L) ∧ ∃ u ∈ ({v, w} : Set E),
      L / 2 * ‖v - w‖ * 𝔼 ε : Fin n → ℤˣ, |∑ t, ((ε t : ℤ) : ℝ)| ≤
        regret (fun t ↦ y t) (A.run c y) u n := by
  obtain ⟨z, hz1, hz⟩ := exists_dual_vector'' ℝ (v - w)
  obtain ⟨ε, u, hu, h⟩ := exists_mul_expect_abs_sum_le (L := L) (n := n) hz
    (a := fun ε t ↦ z (A.run c (signedLosses L z ε) t))
    (fun ε ε' t h ↦ by rw [A.run_congr_feedback c fun s hs ↦ signedLosses_congr h hs])
    (R := fun ε u ↦ regret (fun t ↦ signedLosses L z ε t) (A.run c (signedLosses L z ε)) u n)
    fun ε u ↦ regret_signedLosses ε _ u
  exact ⟨signedLosses L z ε, norm_signedLosses_le hL hz1 ε, u, hu, h⟩

/-- **The lower bound of bounded online linear optimization**, with Khintchine's inequality: for
every learner `A` for linear losses, there are linear losses of dual norm at most `L` and a
comparator `u ∈ {v, w}` against which the regret of `A` after `n` rounds is at least
`L / 2 * ‖v - w‖ * √(n / 3)` [Ora, Theorem 5.1, with the constant `1 / √3` of
`sqrt_card_div_three_le_expect_abs_sum_units` in place of Szarek's `1 / √2`]. -/
theorem exists_mul_sqrt_le_regret_run (A : OnlineLearner C (E →L[ℝ] ℝ) E) (c : ℕ → C)
    (v w : E) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    ∃ y : ℕ → E →L[ℝ] ℝ, (∀ t, ‖y t‖ ≤ L) ∧ ∃ u ∈ ({v, w} : Set E),
      L / 2 * ‖v - w‖ * √((n : ℝ) / 3) ≤ regret (fun t ↦ y t) (A.run c y) u n := by
  obtain ⟨y, hy, u, hu, h⟩ := A.exists_mul_expect_abs_sum_le_regret_run c v w hL n
  exact ⟨y, hy, u, hu, (mul_sqrt_le_mul_expect_abs_sum hL v w n).trans h⟩

/-- **The lower bound of unconstrained online linear optimization** [Ora, Problem 5.1]. For every
learner `A` for linear losses and every `u`, there are linear losses of dual norm at most `L`
against which the regret of `A` after `n` rounds against `u` or `-u` is at least
`L * ‖u‖ * 𝔼 |∑ t < n, ε t|`. -/
theorem exists_mul_norm_mul_expect_abs_sum_le_regret_run (A : OnlineLearner C (E →L[ℝ] ℝ) E)
    (c : ℕ → C) (u : E) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    ∃ y : ℕ → E →L[ℝ] ℝ, (∀ t, ‖y t‖ ≤ L) ∧ ∃ u' ∈ ({u, -u} : Set E),
      L * ‖u‖ * 𝔼 ε : Fin n → ℤˣ, |∑ t, ((ε t : ℤ) : ℝ)| ≤
        regret (fun t ↦ y t) (A.run c y) u' n := by
  have h2 : L / 2 * ‖u - -u‖ = L * ‖u‖ := by
    rw [sub_neg_eq_add, ← two_smul ℝ u, norm_smul, Real.norm_two]
    ring
  simpa only [h2] using A.exists_mul_expect_abs_sum_le_regret_run c u (-u) hL n

/-- **No regret guarantee beats the lower bound.** If the learner `A` has the regret bound `R n`
after `n` rounds for all linear losses of dual norm at most `L`, against comparators in a set
containing `v` and `w`, then `L / 2 * ‖v - w‖ * √(n / 3) ≤ R n` [Ora, Theorem 5.1]. -/
theorem HasRegretBound.div_two_mul_norm_sub_mul_sqrt_le [Nonempty C]
    {A : OnlineLearner C (E →L[ℝ] ℝ) E} {L : ℝ} {U : Set E} {R : ℕ → ℝ}
    (hA : A.HasRegretBound (fun y x ↦ y x) (fun _ y ↦ ‖y‖ ≤ L) U fun n _ _ _ ↦ R n)
    {v w : E} (hv : v ∈ U) (hw : w ∈ U) (hL : 0 ≤ L) (n : ℕ) :
    L / 2 * ‖v - w‖ * √((n : ℝ) / 3) ≤ R n := by
  obtain ⟨c₀⟩ := ‹Nonempty C›
  obtain ⟨y, hy, u, hu, h⟩ := A.exists_mul_sqrt_le_regret_run (fun _ ↦ c₀) v w hL n
  have huU : u ∈ U := by
    rcases hu with rfl | rfl
    exacts [hv, hw]
  exact h.trans (hA.regret_le (fun t _ ↦ hy t) huU)

end OnlineLearner

section Randomized

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The lower bound of bounded online linear optimization for randomized learners**
[Ora, Theorem 5.1, Remark 5.3]. For a randomized learner, a family of learners `A ω` indexed by
its internal randomness `ω ∼ P`, whose plays are integrable, there are linear losses of dual norm
at most `L` and a comparator `u ∈ {v, w}` against which the expected regret after `n` rounds is at
least `L / 2 * ‖v - w‖ * 𝔼 |∑ t < n, ε t|`, for Rademacher signs `ε t`. The losses do not depend
on `ω`: the internal randomness is independent of the signs. -/
theorem exists_mul_expect_abs_sum_le_integral_regret_run (A : Ω → OnlineLearner C (E →L[ℝ] ℝ) E)
    (c : ℕ → C) (hA : ∀ (y : ℕ → E →L[ℝ] ℝ) (t : ℕ), Integrable (fun ω ↦ (A ω).run c y t) P)
    (v w : E) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    ∃ y : ℕ → E →L[ℝ] ℝ, (∀ t, ‖y t‖ ≤ L) ∧ ∃ u ∈ ({v, w} : Set E),
      L / 2 * ‖v - w‖ * 𝔼 ε : Fin n → ℤˣ, |∑ t, ((ε t : ℤ) : ℝ)| ≤
        ∫ ω, regret (fun t ↦ y t) ((A ω).run c y) u n ∂P := by
  obtain ⟨z, hz1, hz⟩ := exists_dual_vector'' ℝ (v - w)
  obtain ⟨ε, u, hu, h⟩ := exists_mul_expect_abs_sum_le (L := L) (n := n) hz
    (a := fun ε t ↦ ∫ ω, z ((A ω).run c (signedLosses L z ε) t) ∂P)
    (fun ε ε' t h ↦ integral_congr_ae (ae_of_all _ fun ω ↦ by
      dsimp only
      rw [(A ω).run_congr_feedback c fun s hs ↦ signedLosses_congr h hs]))
    (R := fun ε u ↦ ∫ ω, regret (fun t ↦ signedLosses L z ε t)
      ((A ω).run c (signedLosses L z ε)) u n ∂P)
    fun ε u ↦ by
      have hint (t : Fin n) : Integrable (fun ω ↦ ((ε t : ℤ) : ℝ) *
          (z ((A ω).run c (signedLosses L z ε) t) - z u)) P :=
        ((z.integrable_comp (hA _ t)).sub (integrable_const _)).const_mul _
      simp_rw [regret_signedLosses, integral_const_mul, integral_finsetSum _ fun t _ ↦ hint t,
        integral_const_mul,
        integral_sub (z.integrable_comp (hA _ _)) (integrable_const _), integral_const,
        probReal_univ, one_smul]
  exact ⟨signedLosses L z ε, norm_signedLosses_le hL hz1 ε, u, hu, h⟩

/-- **The lower bound of bounded online linear optimization for randomized learners**, with
Khintchine's inequality: the expected regret of a randomized learner after `n` rounds is at least
`L / 2 * ‖v - w‖ * √(n / 3)` against `v` or `w`, for some linear losses of dual norm at most `L`
[Ora, Theorem 5.1, Remark 5.3]. -/
theorem exists_mul_sqrt_le_integral_regret_run (A : Ω → OnlineLearner C (E →L[ℝ] ℝ) E)
    (c : ℕ → C) (hA : ∀ (y : ℕ → E →L[ℝ] ℝ) (t : ℕ), Integrable (fun ω ↦ (A ω).run c y t) P)
    (v w : E) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    ∃ y : ℕ → E →L[ℝ] ℝ, (∀ t, ‖y t‖ ≤ L) ∧ ∃ u ∈ ({v, w} : Set E),
      L / 2 * ‖v - w‖ * √((n : ℝ) / 3) ≤ ∫ ω, regret (fun t ↦ y t) ((A ω).run c y) u n ∂P := by
  obtain ⟨y, hy, u, hu, h⟩ := exists_mul_expect_abs_sum_le_integral_regret_run A c hA v w hL n
  exact ⟨y, hy, u, hu, (mul_sqrt_le_mul_expect_abs_sum hL v w n).trans h⟩

end Randomized

end LMLExplore.OnlineLearning
