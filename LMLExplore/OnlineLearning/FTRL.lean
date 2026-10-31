/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.Order.Compact
public import TauCeti.Analysis.Convex.Strong

/-!
# Follow the regularized leader

Online linear optimization on a set `K` of a real inner product space `E`: at each round `t`, the
learner plays `a t ∈ K`, then the loss vector `y t` is revealed and the learner suffers the loss
`⟪a t, y t⟫`. The regret against `u ∈ K` after `n` rounds is `∑ t < n, ⟪a t - u, y t⟫`. All
statements hold for every sequence of losses, in particular for losses chosen adaptively from the
past plays.

Follow the regularized leader (FTRL) with regularizers `ψ t` plays at round `t` a minimizer over
`K` of the cumulative loss plus the regularizer, `b ↦ ⟪b, ∑ s < t, y s⟫ + ψ t b`. With a
potential `F` and a learning rate `η > 0`, it plays a minimizer of `η ∑ s < t, ⟪b, y s⟫ + F b`
[LS, (28.3)].

## Main statements

* `sum_inner_sub_le_ftrl`: the **FTRL lemma** [Ora, Lemma 7.1], for regularizers that may change
  over the rounds: the regret is at most `ψ n u - ψ 0 (a 0)` plus the sum of the stability terms
  `⟪a t, y t⟫ - (m (t + 1) - m t)`, where `m t` is the value of the objective of round `t` at its
  play.
* `ftrl_regret_le`: [LS, Theorem 28.5]. For a convex `K` and a potential `F` with a derivative
  `F' t` within `K` at each play, the regret is at most
  `(F u - F (a 0)) / η + ∑ t < n, ⟪a t - a (t + 1), y t⟫ - (∑ t < n, D_F(a (t + 1), a t)) / η`,
  with `D_F` the Bregman divergence. The potential need not be convex.
* `ftrl_regret_le_of_strongConvexOn`: [LS, Corollary 28.8] when each norm there is `√m` times the
  norm of `E`, that is, for an `m`-strongly convex potential: the regret is at most
  `(F u - F (a 0)) / η + η / (2 m) ∑ t < n, ‖y t‖ ^ 2`.
* `exists_ftrl`: on a nonempty compact set, FTRL with a potential continuous on that set has
  plays.
* `ftrl_regret_le_sqrt_of_closedBall`: [LS, Proposition 28.6] for FTRL. On the closed unit ball,
  with the potential `‖b‖ ^ 2 / 2` and the learning rate `1 / √n`, the regret after `n` rounds
  against every point of the ball is at most `√n` for losses of norm at most `1`.

## Implementation notes

The FTRL lemma and its telescoping proof are adapted from the LMLPapers project (same author),
where they are stated for gains on the probability simplex; here they hold for losses on any set.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
* [Ora] F. Orabona, *A Modern Introduction to Online Learning*, arXiv:1912.13213, 2019.
-/

public section

open Finset Metric
open scoped RealInnerProductSpace

namespace LMLExplore.OnlineLearning

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E} {n : ℕ} {u : E}

/-- **FTRL lemma** [Ora, Lemma 7.1]. Let the play `a n` of round `n` minimize over `K` the
objective `b ↦ ⟪b, ∑ s < n, y s⟫ + ψ n b`. For every `u ∈ K`, the regret against `u` after `n`
rounds is at most `ψ n u - ψ 0 (a 0)` plus the sum over the rounds of the stability terms
`⟪a t, y t⟫ - (m (t + 1) - m t)`, where `m t = ⟪a t, ∑ s < t, y s⟫ + ψ t (a t)` is the value of
the objective of round `t` at its play. -/
theorem sum_inner_sub_le_ftrl (ψ : ℕ → E → ℝ) (y a : ℕ → E)
    (ha : IsMinOn (fun b ↦ ⟪b, ∑ s ∈ range n, y s⟫ + ψ n b) K (a n)) (hu : u ∈ K) :
    ∑ t ∈ range n, ⟪a t - u, y t⟫ ≤ ψ n u - ψ 0 (a 0) + ∑ t ∈ range n, (⟪a t, y t⟫ -
      ((⟪a (t + 1), ∑ s ∈ range (t + 1), y s⟫ + ψ (t + 1) (a (t + 1))) -
        (⟪a t, ∑ s ∈ range t, y s⟫ + ψ t (a t)))) := by
  -- the values of the objectives at the plays telescope, and `a n` beats `u` at round `n`
  have h_tele := sum_range_sub (fun t ↦ ⟪a t, ∑ s ∈ range t, y s⟫ + ψ t (a t)) n
  have h_min : ⟪a n, ∑ s ∈ range n, y s⟫ + ψ n (a n) ≤ ⟪u, ∑ s ∈ range n, y s⟫ + ψ n u := ha hu
  simp only [range_zero, sum_empty, inner_zero_right, zero_add] at h_tele
  rw [sum_sub_distrib, h_tele]
  simp only [inner_sub_left, sum_sub_distrib, ← inner_sum]
  linarith

/-- Let `a` minimize over `K` the FTRL objective `c ↦ η ⟪c, L⟫ + F c`, where `F` has derivative
`F'` within `K` at `a`. If the segment from `a` to `b` lies in `K`, then the objective increases
from `a` to `b` by at least the Bregman divergence `D_F(b, a)`. -/
lemma bregDiv_le_sub_of_isMinOn {F : E → ℝ} {F' : E →L[ℝ] ℝ} {η : ℝ} {L a b : E}
    (h_seg : segment ℝ a b ⊆ K) (ha : IsMinOn (fun c ↦ η * ⟪c, L⟫ + F c) K a)
    (hF' : HasFDerivWithinAt F F' K a) :
    bregDiv F b a F' ≤ η * ⟪b, L⟫ + F b - (η * ⟪a, L⟫ + F a) := by
  -- the objective has derivative `η ⟪·, L⟫ + F'` within `K` at `a`, nonnegative towards `b`
  let ℓ : E →L[ℝ] ℝ := η • innerSL ℝ L
  have hℓ (c : E) : ℓ c = η * ⟪c, L⟫ := by simp [ℓ, real_inner_comm]
  have h_deriv : HasFDerivWithinAt (fun c ↦ η * ⟪c, L⟫ + F c) (ℓ + F') K a := by
    convert ℓ.hasFDerivWithinAt.add hF' using 1
    ext c
    simp [hℓ]
  have h_seg' : segment ℝ a (a + (b - a)) ⊆ K := by rwa [add_sub_cancel]
  have h_nonneg := ha.isLocalMinOn.hasFDerivWithinAt_nonneg h_deriv
    (mem_posTangentConeAt_of_segment_subset h_seg')
  simp only [add_apply, hℓ, inner_sub_left, mul_sub] at h_nonneg
  simp only [bregDiv]
  linarith

/-- **Regret of follow the regularized leader** [LS, Theorem 28.5]. Let `K` be convex and
`η > 0`. Let each play `a t`, for `t ≤ n`, lie in `K` and minimize
`b ↦ η ∑ s < t, ⟪b, y s⟫ + F b` over `K`, where the potential `F` has derivative `F' t` within `K`
at `a t` for `t < n`. Then for every `u ∈ K`, with `D_F` the Bregman divergence,
`∑ t < n, ⟪a t - u, y t⟫ ≤ (F u - F (a 0)) / η + ∑ t < n, ⟪a t - a (t + 1), y t⟫
  - (∑ t < n, D_F(a (t + 1), a t)) / η`.
[LS] assumes the potential convex; the proof only uses the derivatives at the plays. -/
theorem ftrl_regret_le {F : E → ℝ} (hK : Convex ℝ K) {η : ℝ} (hη : 0 < η) (y a : ℕ → E)
    (ha_mem : ∀ t ≤ n, a t ∈ K)
    (ha : ∀ t ≤ n, IsMinOn (fun b ↦ η * ∑ s ∈ range t, ⟪b, y s⟫ + F b) K (a t))
    (F' : ℕ → E →L[ℝ] ℝ) (hF' : ∀ t < n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, ⟪a t - u, y t⟫ ≤ (F u - F (a 0)) / η +
      ∑ t ∈ range n, ⟪a t - a (t + 1), y t⟫ -
        (∑ t ∈ range n, bregDiv F (a (t + 1)) (a t) (F' t)) / η := by
  -- FTRL with potential `F` and learning rate `η` is FTRL with the regularizers `F / η`
  have h_obj (t : ℕ) (b : E) :
      ⟪b, ∑ s ∈ range t, y s⟫ + F b / η = (η * ⟪b, ∑ s ∈ range t, y s⟫ + F b) / η := by
    field_simp
  have ha' (t : ℕ) (ht : t ≤ n) :
      IsMinOn (fun b ↦ η * ⟪b, ∑ s ∈ range t, y s⟫ + F b) K (a t) := by
    simpa only [inner_sum] using ha t ht
  have h_ftrl := sum_inner_sub_le_ftrl (fun _ b ↦ F b / η) y a (n := n) (K := K) (fun b hb ↦ by
    simp only [Set.mem_ofPred_eq, h_obj]
    exact div_le_div_of_nonneg_right (ha' n le_rfl hb) hη.le) hu
  -- each stability term is at most `⟪a t - a (t + 1), y t⟫ - D_F(a (t + 1), a t) / η`
  have h_stab (t : ℕ) (ht : t ∈ range n) :
      ⟪a t, y t⟫ - ((⟪a (t + 1), ∑ s ∈ range (t + 1), y s⟫ + F (a (t + 1)) / η) -
        (⟪a t, ∑ s ∈ range t, y s⟫ + F (a t) / η)) ≤
      ⟪a t - a (t + 1), y t⟫ - bregDiv F (a (t + 1)) (a t) (F' t) / η := by
    have ht' := mem_range.mp ht
    have h_breg := bregDiv_le_sub_of_isMinOn (hK.segment_subset (ha_mem t ht'.le)
      (ha_mem (t + 1) ht')) (ha' t ht'.le) (hF' t ht')
    rw [sum_range_succ, inner_add_right, inner_sub_left]
    have : bregDiv F (a (t + 1)) (a t) (F' t) / η ≤
        ⟪a (t + 1), ∑ s ∈ range t, y s⟫ - ⟪a t, ∑ s ∈ range t, y s⟫ +
          F (a (t + 1)) / η - F (a t) / η := by
      refine (div_le_div_of_nonneg_right h_breg hη.le).trans_eq ?_
      field_simp
      ring
    linarith
  calc ∑ t ∈ range n, ⟪a t - u, y t⟫
  _ ≤ F u / η - F (a 0) / η + ∑ t ∈ range n, (⟪a t, y t⟫ -
      ((⟪a (t + 1), ∑ s ∈ range (t + 1), y s⟫ + F (a (t + 1)) / η) -
        (⟪a t, ∑ s ∈ range t, y s⟫ + F (a t) / η))) := h_ftrl
  _ ≤ F u / η - F (a 0) / η + ∑ t ∈ range n,
      (⟪a t - a (t + 1), y t⟫ - bregDiv F (a (t + 1)) (a t) (F' t) / η) := by
    exact (add_le_add_iff_left _).mpr (sum_le_sum h_stab)
  _ = (F u - F (a 0)) / η + ∑ t ∈ range n, ⟪a t - a (t + 1), y t⟫ -
      (∑ t ∈ range n, bregDiv F (a (t + 1)) (a t) (F' t)) / η := by
    rw [sum_sub_distrib, sum_div, sub_div]
    ring

/-- **Regret of FTRL with a strongly convex potential.** Under the assumptions of
`ftrl_regret_le`, if the potential `F` is `m`-strongly convex on `K` with `m > 0`, then for every
`u ∈ K`,
`∑ t < n, ⟪a t - u, y t⟫ ≤ (F u - F (a 0)) / η + η / (2 m) ∑ t < n, ‖y t‖ ^ 2`.
This is [LS, Corollary 28.8] when each norm there is `√m` times the norm of `E`, with
`F u - F (a 0)` in place of the diameter of `K` for `F`. -/
theorem ftrl_regret_le_of_strongConvexOn {F : E → ℝ} {m : ℝ} (hF : StrongConvexOn K m F)
    (hm : 0 < m) {η : ℝ} (hη : 0 < η) (y a : ℕ → E) (ha_mem : ∀ t ≤ n, a t ∈ K)
    (ha : ∀ t ≤ n, IsMinOn (fun b ↦ η * ∑ s ∈ range t, ⟪b, y s⟫ + F b) K (a t))
    (F' : ℕ → E →L[ℝ] ℝ) (hF' : ∀ t < n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, ⟪a t - u, y t⟫ ≤
      (F u - F (a 0)) / η + η / (2 * m) * ∑ t ∈ range n, ‖y t‖ ^ 2 := by
  refine (ftrl_regret_le hF.1 hη y a ha_mem ha F' hF' hu).trans ?_
  rw [add_sub_assoc, add_le_add_iff_left, sum_div, ← sum_sub_distrib, mul_sum]
  refine sum_le_sum fun t ht ↦ ?_
  have ht' := mem_range.mp ht
  -- the Bregman divergence of `F` is at least `m / 2` times the squared distance
  have h_breg : m / 2 * ‖a (t + 1) - a t‖ ^ 2 ≤ bregDiv F (a (t + 1)) (a t) (F' t) := by
    have := hF.add_add_le_of_hasFDerivWithinAt (ha_mem t ht'.le) (ha_mem (t + 1) ht') (hF' t ht')
    simp only [bregDiv]
    linarith
  have h_inner : ⟪a t - a (t + 1), y t⟫ ≤ ‖a (t + 1) - a t‖ * ‖y t‖ := by
    rw [norm_sub_rev]
    exact real_inner_le_norm _ _
  -- `x z - m x² / (2 η) ≤ η z² / (2 m)`, a square completion
  set x := ‖a (t + 1) - a t‖
  set z := ‖y t‖
  have h_sq : η / (2 * m) * z ^ 2 - (x * z - m / 2 * x ^ 2 / η) =
      (m * x - η * z) ^ 2 / (2 * m * η) := by
    field_simp
    ring
  have h_nonneg : 0 ≤ (m * x - η * z) ^ 2 / (2 * m * η) := by positivity
  have h_div : -(bregDiv F (a (t + 1)) (a t) (F' t) / η) ≤ -(m / 2 * x ^ 2 / η) :=
    neg_le_neg (div_le_div_of_nonneg_right h_breg hη.le)
  linarith

/-- **Existence of FTRL plays.** On a nonempty compact set `K`, with a potential `F` continuous
on `K`, there is a sequence of plays `a t ∈ K` such that each `a t` minimizes
`b ↦ η ∑ s < t, ⟪b, y s⟫ + F b` over `K`. -/
theorem exists_ftrl {F : E → ℝ} (hK : IsCompact K) (hK_ne : K.Nonempty) (hF : ContinuousOn F K)
    (η : ℝ) (y : ℕ → E) :
    ∃ a : ℕ → E, ∀ t, a t ∈ K ∧ IsMinOn (fun b ↦ η * ∑ s ∈ range t, ⟪b, y s⟫ + F b) K (a t) := by
  have h_cont (t : ℕ) : ContinuousOn (fun b ↦ η * ∑ s ∈ range t, ⟪b, y s⟫ + F b) K :=
    (by fun_prop : Continuous fun b ↦ η * ∑ s ∈ range t, ⟪b, y s⟫).continuousOn.add hF
  choose a ha using fun t ↦ hK.exists_isMinOn hK_ne (h_cont t)
  exact ⟨a, ha⟩

/-- **FTRL on the unit ball** [LS, Proposition 28.6], which [LS] states for mirror descent and
notes for FTRL. Let each play `a t`, for `t ≤ n`, lie in the closed unit ball and minimize
`b ↦ (√n)⁻¹ ∑ s < t, ⟪b, y s⟫ + ‖b‖ ^ 2 / 2` over it: this is FTRL with the potential
`‖b‖ ^ 2 / 2` and the learning rate `1 / √n`. If the losses have norm at most `1`, then the regret
after `n` rounds against every point of the ball is at most `√n`. -/
theorem ftrl_regret_le_sqrt_of_closedBall (y a : ℕ → E) (hy : ∀ t < n, ‖y t‖ ≤ 1)
    (ha_mem : ∀ t ≤ n, a t ∈ closedBall (0 : E) 1)
    (ha : ∀ t ≤ n, IsMinOn (fun b ↦ (√n)⁻¹ * ∑ s ∈ range t, ⟪b, y s⟫ + ‖b‖ ^ 2 / 2)
      (closedBall 0 1) (a t))
    (hu : u ∈ closedBall (0 : E) 1) :
    ∑ t ∈ range n, ⟪a t - u, y t⟫ ≤ √n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hsqrt : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  -- `‖·‖ ^ 2 / 2` is `1`-strongly convex, with derivative `⟪b, ·⟫` at `b`
  have hF : StrongConvexOn (closedBall (0 : E) 1) 1 fun b ↦ ‖b‖ ^ 2 / 2 := by
    refine strongConvexOn_iff_convex.mpr ?_
    convert convexOn_const (0 : ℝ) (convex_closedBall (0 : E) 1) using 2 with b
    ring
  have hF' (t : ℕ) : HasFDerivWithinAt (fun b ↦ ‖b‖ ^ 2 / 2)
      ((2 : ℝ)⁻¹ • (2 • innerSL ℝ (a t))) (closedBall 0 1) (a t) := by
    simpa only [div_eq_mul_inv, mul_comm _ (2 : ℝ)⁻¹] using
      ((hasStrictFDerivAt_norm_sq (a t)).hasFDerivAt.const_mul (2 : ℝ)⁻¹).hasFDerivWithinAt
  have h := ftrl_regret_le_of_strongConvexOn hF one_pos (inv_pos.mpr hsqrt) y a ha_mem ha _
    (fun t _ ↦ hF' t) hu
  -- the penalty is at most `√n / 2` and the stability terms add up to at most `√n / 2`
  have hu' : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.mp hu
  have h_pen : (‖u‖ ^ 2 / 2 - ‖a 0‖ ^ 2 / 2) / (√n)⁻¹ ≤ √n / 2 := by
    rw [div_inv_eq_mul]
    have : ‖u‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg u) hu'
    nlinarith [sq_nonneg ‖a 0‖]
  have h_sum : ∑ t ∈ range n, ‖y t‖ ^ 2 ≤ n := by
    calc ∑ t ∈ range n, ‖y t‖ ^ 2
    _ ≤ ∑ t ∈ range n, (1 : ℝ) :=
      sum_le_sum fun t ht ↦ pow_le_one₀ (norm_nonneg _) (hy t (mem_range.mp ht))
    _ = n := by simp
  have h_stab : (√n)⁻¹ / (2 * 1) * ∑ t ∈ range n, ‖y t‖ ^ 2 ≤ √n / 2 := by
    calc (√n)⁻¹ / (2 * 1) * ∑ t ∈ range n, ‖y t‖ ^ 2
    _ ≤ (√n)⁻¹ / (2 * 1) * n := by gcongr
    _ = √n / 2 := by
      field_simp
      rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  linarith

end LMLExplore.OnlineLearning
