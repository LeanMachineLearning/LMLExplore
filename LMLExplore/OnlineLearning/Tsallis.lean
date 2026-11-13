/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Tsallis
public import LMLExplore.OnlineLearning.LocalNorm

/-!
# Follow the regularized leader and mirror descent with the ½-Tsallis potential

Follow the regularized leader on the probability simplex of a finite set `α`, with the ½-Tsallis
potential `F p = -∑ a, √(p a)` and the learning rates `1 / c t`, plays at round `t` the Tsallis
weights `p t = tsallisWeights (c t) (∑ s < t, ℓ s)`, the minimizer of
`p ↦ ⟨∑ s < t, ℓ s, p⟩ - c t ∑ a, √(p a)` over the simplex (`LMLExplore.tsallisWeights`). This
file bounds its regret with local norms [ZS21], [Ora, Section 9.3].

The bound follows from the local-norm regret bound of FTRL through the unconstrained step
(`ftrl_regret_le_of_localNorm_of_antitone`), on the nonnegative orthant, where `F` is convex,
and the positive orthant, where it is twice differentiable with second derivative
`F'' z (v, w) = ∑ a, v a * w a / (4 z a √(z a))`. The unconstrained step `x` from the weights
`p` for the loss `ℓ` and the rate `1 / c` solves `1 / √(x a) = 1 / √(p a) + 2 ℓ a / c`. If every
coordinate of the loss is at least `-c / 4`, this is at least `1 / (2 √(p a))`, so `x` lies in
the positive orthant with `x a ≤ 4 p a`, and the Cauchy–Schwarz inequality bounds the squared dual
local norm of `ℓ` at every point of the segment `[p, x]` by `32 ∑ a, p a √(p a) ℓ a ^ 2`. The
losses may be negative: the analysis of Tsallis-INF uses losses shifted by the loss of the played
arm, which do not change the weights (`tsallisWeights_add_const`) and are at least `-1`.

Mirror descent on the simplex with the same potential and the learning rate `1 / c` moves from
the weights `p` to the Tsallis weights of `ℓ + c / (2 √p)` (`tsallisMDStep`), the loss minus `c`
times the derivative of the potential at `p`. From the Tsallis weights of `L` it reaches the
Tsallis weights of `L + ℓ`, so with a constant learning rate and the uniform first weights its
iterates are the plays of follow the regularized leader. For nonnegative losses, the
unconstrained step decreases every coordinate, which bounds the squared dual local norm along the
segment by `4 ∑ a, p a √(p a) ℓ a ^ 2`; this sharper constant gives the regret bound of mirror
descent with the ½-Tsallis potential for bandits [Ora, Section 9.1.2, Theorem 9.2].

## Main definitions

* `tsallisMDStep c p ℓ`: the mirror descent step with the ½-Tsallis potential from the weights
  `p`, for the loss `ℓ` and the learning rate `1 / c`.

## Main statements

* `tsallisWeights_regret_le_of_monotone`: for coefficients `c t > 0` nondecreasing in `t` and
  losses with `ℓ t a ≥ -c t / 4`, against every point `u` of the simplex,
  `∑ t < n, (⟨p t, ℓ t⟩ - ⟨u, ℓ t⟩)
    ≤ c (n - 1) (√k - ∑ a, √(u a)) + ∑ t < n, 16 / c t * ∑ a, p t a √(p t a) ℓ t a ^ 2`,
  with `k` the cardinality of `α`.
* `isMirrorDescentStep_iff_eq_tsallisMDStep`: for `c > 0`, the mirror descent steps on the simplex
  with the potential `-∑ a, √(p a)` and the learning rate `1 / c` from `p` for the loss `ℓ` are
  exactly `tsallisMDStep c p ℓ`.
* `tsallisMDStep_tsallisWeights`, `eq_tsallisWeights_of_eq_tsallisMDStep`: the mirror descent
  step from the Tsallis weights of `L` is the Tsallis weights of `L + ℓ`, and mirror descent with a
  constant learning rate from the uniform weights plays `tsallisWeights c (∑ s < t, ℓ s)`.
* `tsallisMirrorDescent_regret_le`: for `c > 0` and nonnegative losses, mirror descent with the
  learning rate `1 / c` from the uniform weights satisfies, against every point `u` of the simplex,
  `∑ t < n, (⟨p t, ℓ t⟩ - ⟨u, ℓ t⟩)
    ≤ c (√k - ∑ a, √(u a)) + ∑ t < n, 2 / c * ∑ a, p t a √(p t a) ℓ t a ^ 2`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
* [ZS21] J. Zimmert and Y. Seldin, *Tsallis-INF: an optimal algorithm for stochastic and
  adversarial bandits*, JMLR 22 (2021).
-/

public section

open Finset Real

namespace LMLExplore.OnlineLearning

variable {α : Type*} [Fintype α]

section Loss

/-- The linear functional `v ↦ ∑ a, ℓ a * v a` of a loss vector `ℓ`. -/
private noncomputable def lossCLM (ℓ : α → ℝ) : (α → ℝ) →L[ℝ] ℝ :=
  ∑ a, ℓ a • ContinuousLinearMap.proj a

private lemma lossCLM_apply (ℓ v : α → ℝ) : lossCLM ℓ v = ∑ a, ℓ a * v a := by
  simp [lossCLM]

end Loss

section Step

variable {c : ℝ} {ℓ p : α → ℝ}

/-- The unconstrained step from the weights `p` for the loss `ℓ` and the rate `1 / c`: the point
`x` with `1 / √(x a) = 1 / √(p a) + 2 ℓ a / c`. -/
private noncomputable def tsallisStep (c : ℝ) (ℓ p : α → ℝ) : α → ℝ :=
  fun a ↦ ((√(p a))⁻¹ + 2 * ℓ a / c)⁻¹ ^ 2

omit [Fintype α] in
/-- For `0 < p a ≤ 1` and `ℓ a ≥ -c / 4`, `1 / √(p a) + 2 ℓ a / c ≥ 1 / (2 √(p a))`. -/
private lemma inv_two_mul_sqrt_le (hc : 0 < c) {a : α} (hp : 0 < p a) (hp1 : p a ≤ 1)
    (hℓ : -(c / 4) ≤ ℓ a) : (2 * √(p a))⁻¹ ≤ (√(p a))⁻¹ + 2 * ℓ a / c := by
  have hs : 0 < √(p a) := sqrt_pos.2 hp
  have hs1 : √(p a) ≤ 1 := sqrt_le_one.2 hp1
  have h2 : -(1 / 2) ≤ 2 * ℓ a / c := by
    rw [le_div_iff₀ hc]
    linarith
  have h3 : 1 / 2 ≤ (2 * √(p a))⁻¹ := by
    rw [one_div]
    exact inv_anti₀ (by positivity) (by linarith)
  have h4 : (√(p a))⁻¹ = 2 * (2 * √(p a))⁻¹ := by field_simp
  linarith

omit [Fintype α] in
/-- For `0 < p a ≤ 1` and `ℓ a ≥ -c / 4`, `1 / √(p a) + 2 ℓ a / c` is positive. -/
private lemma inv_sqrt_add_two_mul_div_pos (hc : 0 < c) {a : α} (hp : 0 < p a) (hp1 : p a ≤ 1)
    (hℓ : -(c / 4) ≤ ℓ a) : 0 < (√(p a))⁻¹ + 2 * ℓ a / c := by
  have hs : 0 < √(p a) := sqrt_pos.2 hp
  have h0 : 0 < (2 * √(p a))⁻¹ := by positivity
  exact h0.trans_le (inv_two_mul_sqrt_le hc hp hp1 hℓ)

omit [Fintype α] in
/-- For weights in `(0, 1]` and a loss with `ℓ a ≥ -c / 4`, the unconstrained step has positive
coordinates, with `x a ≤ 4 p a`. -/
private lemma tsallisStep_pos_le (hc : 0 < c) (hp : ∀ a, 0 < p a) (hp1 : ∀ a, p a ≤ 1)
    (hℓ : ∀ a, -(c / 4) ≤ ℓ a) (a : α) :
    0 < tsallisStep c ℓ p a ∧ tsallisStep c ℓ p a ≤ 4 * p a := by
  have h := inv_two_mul_sqrt_le hc (hp a) (hp1 a) (hℓ a)
  have hs : 0 < √(p a) := sqrt_pos.2 (hp a)
  have hpos := inv_sqrt_add_two_mul_div_pos hc (hp a) (hp1 a) (hℓ a)
  refine ⟨pow_pos (inv_pos.2 hpos) 2, ?_⟩
  calc tsallisStep c ℓ p a = ((√(p a))⁻¹ + 2 * ℓ a / c)⁻¹ ^ 2 := rfl
  _ ≤ ((2 * √(p a))⁻¹)⁻¹ ^ 2 := by
      gcongr
  _ = 4 * p a := by rw [inv_inv, mul_pow, sq_sqrt (hp a).le]; norm_num

/-- The unconstrained step solves `F' x = F' p - c⁻¹ ℓ` for the ½-Tsallis potential `F`. -/
private lemma tsallisDeriv_tsallisStep (hc : 0 < c) (hp : ∀ a, 0 < p a) (hp1 : ∀ a, p a ≤ 1)
    (hℓ : ∀ a, -(c / 4) ≤ ℓ a) :
    tsallisDeriv (tsallisStep c ℓ p) = tsallisDeriv p - c⁻¹ • lossCLM ℓ := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [sub_apply, smul_apply, tsallisDeriv_apply,
    lossCLM_apply, smul_eq_mul, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun a _ ↦ ?_
  have hpos := inv_sqrt_add_two_mul_div_pos hc (hp a) (hp1 a) (hℓ a)
  have hs : 0 < √(p a) := sqrt_pos.2 (hp a)
  rw [tsallisStep, sqrt_sq (inv_pos.2 hpos).le, mul_inv, inv_inv]
  field_simp
  ring

/-- **The local norm along a segment from the weights.** For positive weights `p`, `r ≥ 1`, a
point `x` with `0 < x a ≤ r p a`, and `z ∈ [p, x]`,
`ℓ (x - p) ^ 2 ≤ 4 r √r ∑ a, p a √(p a) ℓ a ^ 2 * F'' z (x - p, x - p)`. -/
private lemma sq_lossCLM_le_of_le_mul {r : ℝ} (hr : 1 ≤ r) (hp : ∀ a, 0 < p a) {x : α → ℝ}
    (hx : ∀ a, 0 < x a) (hxr : ∀ a, x a ≤ r * p a) {z : α → ℝ} (hz : z ∈ segment ℝ p x) :
    lossCLM ℓ (x - p) ^ 2 ≤
      (4 * r * √r * ∑ a, p a * √(p a) * ℓ a ^ 2) * tsallisDeriv2 z (x - p) (x - p) := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  set z := s • p + t • x
  -- every coordinate of `z` is in `(0, r p a]`
  have hz_pos (a : α) : 0 < z a := by
    simp only [z, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hs.lt_or_eq with hs | rfl
    · nlinarith [hp a, hx a]
    · simp only [zero_add] at hst
      simp [hst, hx a]
  have hzr (a : α) : z a ≤ r * p a := by
    have hpr : p a ≤ r * p a := le_mul_of_one_le_left (hp a).le hr
    calc z a = s * p a + t * x a := by simp [z]
    _ ≤ s * (r * p a) + t * (r * p a) := by gcongr; exact hxr a
    _ = r * p a := by rw [← add_mul, hst, one_mul]
  have hw (a : α) : 0 < 4 * z a * √(z a) :=
    mul_pos (mul_pos four_pos (hz_pos a)) (sqrt_pos.2 (hz_pos a))
  have hg (a : α) : 0 ≤ (4 * z a * √(z a))⁻¹ * (x - p) a * (x - p) a := by
    rw [mul_assoc]
    exact mul_nonneg (inv_nonneg.2 (hw a).le) (mul_self_nonneg _)
  -- the Cauchy–Schwarz inequality with the weights `4 z a √(z a)`
  have h_cs := sum_sq_le_sum_mul_sum_of_sq_le_mul univ (r := fun a ↦ ℓ a * (x - p) a)
    (f := fun a ↦ 4 * z a * √(z a) * ℓ a ^ 2)
    (g := fun a ↦ (4 * z a * √(z a))⁻¹ * (x - p) a * (x - p) a)
    (fun a _ ↦ mul_nonneg (hw a).le (sq_nonneg _)) (fun a _ ↦ hg a)
    (fun a _ ↦ le_of_eq (by
      have h1 := (hz_pos a).ne'
      have h2 := (sqrt_pos.2 (hz_pos a)).ne'
      field_simp))
  rw [lossCLM_apply, tsallisDeriv2_apply]
  refine h_cs.trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun a _ ↦ hg a))
  rw [mul_sum]
  refine sum_le_sum fun a _ ↦ ?_
  -- `4 z a √(z a) ≤ 4 r √r p a √(p a)`
  have h1 : z a * √(z a) ≤ r * √r * (p a * √(p a)) := by
    have h2 : √(z a) ≤ √r * √(p a) := by
      rw [← sqrt_mul (by linarith)]
      exact sqrt_le_sqrt (hzr a)
    calc z a * √(z a) ≤ (r * p a) * (√r * √(p a)) :=
          mul_le_mul (hzr a) h2 (sqrt_nonneg _) (by nlinarith [hp a])
    _ = r * √r * (p a * √(p a)) := by ring
  calc 4 * z a * √(z a) * ℓ a ^ 2 = 4 * (z a * √(z a)) * ℓ a ^ 2 := by ring
  _ ≤ 4 * (r * √r * (p a * √(p a))) * ℓ a ^ 2 := by gcongr
  _ = 4 * r * √r * (p a * √(p a) * ℓ a ^ 2) := by ring

/-- **The local norm along the segment to the unconstrained step.** For weights `p` in `(0, 1]`, a
point `x` with `0 < x a ≤ 4 p a`, and `z ∈ [p, x]`,
`ℓ (x - p) ^ 2 ≤ 32 ∑ a, p a √(p a) ℓ a ^ 2 * F'' z (x - p, x - p)`. -/
private lemma sq_lossCLM_le (hp : ∀ a, 0 < p a) {x : α → ℝ} (hx : ∀ a, 0 < x a)
    (hx4 : ∀ a, x a ≤ 4 * p a) {z : α → ℝ} (hz : z ∈ segment ℝ p x) :
    lossCLM ℓ (x - p) ^ 2 ≤
      (32 * ∑ a, p a * √(p a) * ℓ a ^ 2) * tsallisDeriv2 z (x - p) (x - p) := by
  have h32 : (4 : ℝ) * 4 * √4 = 32 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq zero_le_two]
    norm_num
  simpa only [h32] using sq_lossCLM_le_of_le_mul (by norm_num) hp hx hx4 hz

end Step

/-- **Regret of FTRL with the ½-Tsallis potential** with local norms [ZS21],
[Ora, Section 9.3]. Let the coefficients `c t > 0` be nondecreasing, and let the losses satisfy
`ℓ t a ≥ -c t / 4` at the rounds `t < n`. Then the Tsallis weights
`p t = tsallisWeights (c t) (∑ s < t, ℓ s)` satisfy, against every point `u` of the simplex,
`∑ t < n, (⟨p t, ℓ t⟩ - ⟨u, ℓ t⟩)
  ≤ c (n - 1) (√k - ∑ a, √(u a)) + ∑ t < n, 16 / c t * ∑ a, p t a √(p t a) ℓ t a ^ 2`,
with `k` the cardinality of `α` and `⟨p, ℓ⟩ = ∑ a, p a * ℓ a`. The weights are the plays of FTRL
on the simplex with the potential `-∑ a, √(p a)` and the learning rates `1 / c t`. -/
theorem tsallisWeights_regret_le_of_monotone {c : ℕ → ℝ} (hc : ∀ t, 0 < c t)
    (hc_mono : Monotone c)
    {ℓ : ℕ → α → ℝ} {n : ℕ} (hℓ : ∀ t < n, ∀ a, -(c t / 4) ≤ ℓ t a) {u : α → ℝ}
    (hu : u ∈ simplex α) :
    ∑ t ∈ range n, (∑ a, tsallisWeights (c t) (∑ s ∈ range t, ℓ s) a * ℓ t a -
        ∑ a, u a * ℓ t a) ≤
      c (n - 1) * (√(Fintype.card α) - ∑ a, √(u a)) +
        ∑ t ∈ range n, 16 / c t * ∑ a, tsallisWeights (c t) (∑ s ∈ range t, ℓ s) a *
          √(tsallisWeights (c t) (∑ s ∈ range t, ℓ s) a) * ℓ t a ^ 2 := by
  have := nonempty_of_mem_simplex hu
  set p : ℕ → α → ℝ := fun t ↦ tsallisWeights (c t) (∑ s ∈ range t, ℓ s) with hp_def
  have hp_pos (t : ℕ) (a : α) : 0 < p t a := tsallisWeights_pos (hc t).ne' _ a
  have hp_mem (t : ℕ) : p t ∈ simplex α := tsallisWeights_mem_simplex (hc t).ne' _
  have hp_le_one (t : ℕ) (a : α) : p t a ≤ 1 := (simplex_subset_Icc (hp_mem t)).2 a
  set U : Set (α → ℝ) := Set.univ.pi fun _ ↦ Set.Ioi 0
  have hUD : U ⊆ Set.Ici 0 := fun z hz a ↦ (Set.mem_univ_pi.1 hz a).le
  -- the plays are the plays of FTRL with the potential `-∑ a, √(p a)` and the rates `1 / c t`
  have h_play (t : ℕ) : IsFTRLPlay (simplex α) (fun q ↦ -∑ a, √(q a)) (c t)⁻¹
      (fun s ↦ lossCLM (ℓ s)) t (p t) := by
    refine ⟨hp_mem t, isMinOn_iff.2 fun b hb ↦ ?_⟩
    have h := isMinOn_iff.1 (isMinOn_tsallisWeights (hc t) (∑ s ∈ range t, ℓ s)) b hb
    have h_obj (q : α → ℝ) : (c t)⁻¹ * ∑ s ∈ range t, lossCLM (ℓ s) q + -∑ a, √(q a) =
        (c t)⁻¹ * ((∑ s ∈ range t, ℓ s) ⬝ᵥ q - c t * ∑ a, √(q a)) := by
      simp only [lossCLM_apply, dotProduct, Finset.sum_apply, sum_mul]
      rw [sum_comm]
      have := (hc t).ne'
      field_simp
      ring
    rw [h_obj, h_obj]
    exact mul_le_mul_of_nonneg_left h (inv_pos.2 (hc t)).le
  have h := ftrl_regret_le_of_localNorm_of_antitone convexOn_neg_sum_sqrt (convex_simplex α)
    (simplex_subset_nonneg (α := α)) (convex_pi fun _ _ ↦ convex_Ioi 0) hUD
    (fun z hz ↦ (hasFDerivAt_neg_sum_sqrt (Set.mem_univ_pi.1 hz)).hasFDerivWithinAt)
    (fun z hz ↦ (hasFDerivAt_tsallisDeriv (Set.mem_univ_pi.1 hz)).hasFDerivWithinAt)
    (η := fun t ↦ (c t)⁻¹) (fun t ↦ inv_pos.2 (hc t))
    (fun s t hst ↦ inv_anti₀ (hc s) (hc_mono hst)) (fun s ↦ lossCLM (ℓ s)) p
    (fun t ↦ tsallisStep (c t) (ℓ t) (p t)) (h_play 0) (fun t _ ↦ h_play t)
    (fun t _ ↦ Set.mem_univ_pi.2 (hp_pos t))
    (fun t ht ↦ Set.mem_univ_pi.2 fun a ↦
      (tsallisStep_pos_le (hc t) (hp_pos t) (hp_le_one t) (hℓ t ht) a).1)
    (fun t ht ↦ tsallisDeriv_tsallisStep (hc t) (hp_pos t) (hp_le_one t) (hℓ t ht))
    (fun t ↦ 32 * ∑ a, p t a * √(p t a) * ℓ t a ^ 2)
    (fun t _ ↦ mul_nonneg (by norm_num) (sum_nonneg fun a _ ↦ by
      have := hp_pos t a; positivity))
    (fun t ht z hz ↦ sq_lossCLM_le (hp_pos t)
      (fun a ↦ (tsallisStep_pos_le (hc t) (hp_pos t) (hp_le_one t) (hℓ t ht) a).1)
      (fun a ↦ (tsallisStep_pos_le (hc t) (hp_pos t) (hp_le_one t) (hℓ t ht) a).2) hz) hu
  -- the first play is uniform, where the potential is `-√k`
  have hp0 : p 0 = fun _ ↦ (Fintype.card α : ℝ)⁻¹ := by
    simp only [hp_def, range_zero, sum_empty]
    exact tsallisWeights_const (hc 0).ne' 0
  have hk : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have h_F0 : -∑ a, √(p 0 a) = -√(Fintype.card α) := by
    rw [hp0, sum_const, card_univ, nsmul_eq_mul, sqrt_inv]
    congr 1
    field_simp
    rw [sq_sqrt hk.le]
  convert h using 1
  · refine sum_congr rfl fun t _ ↦ ?_
    rw [map_sub, lossCLM_apply, lossCLM_apply]
    simp only [hp_def, mul_comm]
  · rw [h_F0, div_inv_eq_mul]
    congr 1
    · ring
    · refine sum_congr rfl fun t _ ↦ ?_
      field_simp
      ring

section MirrorDescent

variable {c : ℝ}

/-- The **mirror descent step with the ½-Tsallis potential** from the weights `p`, for the loss
`ℓ` and the learning rate `1 / c`: the Tsallis weights with coefficient `c` of the vector
`a ↦ ℓ a + c / (2 √(p a))`, which is `ℓ` minus `c` times the derivative of the potential
`-∑ a, √(p a)` at `p`. For `c > 0` it is the unique mirror descent step on the simplex
(`isMirrorDescentStep_iff_eq_tsallisMDStep`). -/
noncomputable def tsallisMDStep (c : ℝ) (p ℓ : α → ℝ) : α → ℝ :=
  tsallisWeights c fun a ↦ ℓ a + c / (2 * √(p a))

lemma tsallisMDStep_def (c : ℝ) (p ℓ : α → ℝ) :
    tsallisMDStep c p ℓ = tsallisWeights c (fun a ↦ ℓ a + c / (2 * √(p a))) := (rfl)

variable [Nonempty α]

lemma tsallisMDStep_pos (hc : c ≠ 0) (p ℓ : α → ℝ) (a : α) : 0 < tsallisMDStep c p ℓ a :=
  tsallisWeights_pos hc _ a

lemma tsallisMDStep_mem_simplex (hc : c ≠ 0) (p ℓ : α → ℝ) : tsallisMDStep c p ℓ ∈ simplex α :=
  tsallisWeights_mem_simplex hc _

/-- For `c ≠ 0`, the mirror descent step is a measurable function of the weights and the loss. -/
@[fun_prop]
lemma measurable_tsallisMDStep (hc : c ≠ 0) :
    Measurable fun x : (α → ℝ) × (α → ℝ) ↦ tsallisMDStep c x.1 x.2 := by
  simp_rw [tsallisMDStep_def]
  have := measurable_tsallisWeights (α := α) hc
  fun_prop

omit [Nonempty α] in
/-- The objective `b ↦ c⁻¹ ℓ b + D_F(b, p)` of a mirror descent step with the ½-Tsallis potential
`F` is `c⁻¹` times the objective `b ↦ L ⬝ᵥ b - c ∑ a, √(b a)` of the Tsallis weights of
`L = ℓ + c / (2 √p)`, up to an additive constant. -/
private lemma mul_lossCLM_add_bregDiv_eq (hc : c ≠ 0) (p ℓ b : α → ℝ) :
    c⁻¹ * lossCLM ℓ b + bregDiv (fun q ↦ -∑ a, √(q a)) b p (tsallisDeriv p) =
      c⁻¹ * ((fun a ↦ ℓ a + c / (2 * √(p a))) ⬝ᵥ b - c * ∑ a, √(b a)) +
        ∑ a, (√(p a) - (2 * √(p a))⁻¹ * p a) := by
  simp only [bregDiv, lossCLM_apply, tsallisDeriv_apply, dotProduct, map_sub, mul_sum,
    ← sum_neg_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun a _ ↦ ?_
  have : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  rw [div_eq_mul_inv]
  linear_combination (√(b a) - b a * (2 * √(p a))⁻¹) * this

/-- **Mirror descent with the ½-Tsallis potential** [Ora, Section 9.1.2]. For `c > 0`, a point
`q` is a mirror descent step on the simplex from `p`, with the potential `-∑ a, √(p a)`, its
derivative `tsallisDeriv p` at `p`, the learning rate `1 / c` and the loss `ℓ`, if and only if
`q = tsallisMDStep c p ℓ`. The weights `p` need not be positive nor lie in the simplex. -/
theorem isMirrorDescentStep_iff_eq_tsallisMDStep (hc : 0 < c) (p ℓ : α → ℝ) {q : α → ℝ} :
    IsMirrorDescentStep (simplex α) (fun q ↦ -∑ a, √(q a)) c⁻¹
        (∑ a, ℓ a • ContinuousLinearMap.proj a) p (tsallisDeriv p) q ↔
      q = tsallisMDStep c p ℓ := by
  have h_iff (q : α → ℝ) :
      IsMinOn (fun b ↦ c⁻¹ * lossCLM ℓ b + bregDiv (fun q ↦ -∑ a, √(q a)) b p (tsallisDeriv p))
        (simplex α) q ↔
      IsMinOn (fun b ↦ (fun a ↦ ℓ a + c / (2 * √(p a))) ⬝ᵥ b - c * ∑ a, √(b a)) (simplex α) q := by
    simp only [isMinOn_iff, mul_lossCLM_add_bregDiv_eq hc.ne', add_le_add_iff_right]
    exact forall₂_congr fun b _ ↦ mul_le_mul_iff_of_pos_left (inv_pos.2 hc)
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨h ▸ tsallisMDStep_mem_simplex hc.ne' p ℓ, ?_⟩⟩
  · exact (isMinOn_iff_eq_tsallisWeights hc h.mem).1 ((h_iff q).1 h.isMinOn)
  · exact (h_iff q).2 (h ▸ isMinOn_tsallisWeights hc _)

/-- **Mirror descent from the Tsallis weights is follow the regularized leader.** For `c > 0`, the
mirror descent step from the Tsallis weights of `L`, for the loss `ℓ` and the learning rate
`1 / c`, is the Tsallis weights of `L + ℓ`. -/
theorem tsallisMDStep_tsallisWeights (hc : 0 < c) (L ℓ : α → ℝ) :
    tsallisMDStep c (tsallisWeights c L) ℓ = tsallisWeights c (L + ℓ) := by
  -- by the first-order condition, the shifted loss is `L + ℓ` minus the normalizer of `L`
  have h (a : α) : ℓ a + c / (2 * √(tsallisWeights c L a)) =
      (L + ℓ) a + -tsallisNormalizer c L := by
    have := sub_div_two_mul_sqrt_tsallisWeights hc L a
    rw [Pi.add_apply]
    linarith
  rw [tsallisMDStep_def, funext h, tsallisWeights_add_const hc.ne']

/-- **Mirror descent with the ½-Tsallis potential and a constant learning rate is follow the
regularized leader.** For `c > 0`, if `p 0` is uniform and `p (t + 1)` is the mirror descent step
from `p t` for the loss `ℓ t` and the learning rate `1 / c`, at the rounds `t < n`, then
`p t = tsallisWeights c (∑ s < t, ℓ s)` for `t ≤ n`. -/
theorem eq_tsallisWeights_of_eq_tsallisMDStep (hc : 0 < c) {ℓ p : ℕ → α → ℝ} {n : ℕ}
    (hp0 : p 0 = fun _ ↦ (Fintype.card α : ℝ)⁻¹)
    (hp : ∀ t < n, p (t + 1) = tsallisMDStep c (p t) (ℓ t)) :
    ∀ t ≤ n, p t = tsallisWeights c (∑ s ∈ range t, ℓ s)
  | 0, _ => by rw [hp0, range_zero, sum_empty, ← tsallisWeights_const hc.ne' 0]; rfl
  | t + 1, ht => by
    rw [hp t ht, eq_tsallisWeights_of_eq_tsallisMDStep hc hp0 hp t (Nat.le_of_succ_le ht),
      tsallisMDStep_tsallisWeights hc, sum_range_succ]

omit [Fintype α] [Nonempty α] in
/-- For a nonnegative loss, the unconstrained step from positive weights `p` decreases every
coordinate. -/
private lemma tsallisStep_le (hc : 0 < c) {ℓ p : α → ℝ} (hp : ∀ a, 0 < p a) (hℓ : ∀ a, 0 ≤ ℓ a)
    (a : α) : tsallisStep c ℓ p a ≤ p a := by
  have hs : 0 < √(p a) := sqrt_pos.2 (hp a)
  have hℓa := hℓ a
  have h : (√(p a))⁻¹ ≤ (√(p a))⁻¹ + 2 * ℓ a / c := le_add_of_nonneg_right (by positivity)
  calc tsallisStep c ℓ p a = ((√(p a))⁻¹ + 2 * ℓ a / c)⁻¹ ^ 2 := rfl
  _ ≤ ((√(p a))⁻¹)⁻¹ ^ 2 := by gcongr
  _ = p a := by rw [inv_inv, sq_sqrt (hp a).le]

/-- **Stability of a mirror descent step with the ½-Tsallis potential** for a nonnegative loss.
For `c > 0`, positive weights `p ≤ 1` and a nonnegative loss `ℓ`, the stability term
`⟨ℓ, p - q⟩ - c D_ψ(q, p)` of the step `q = tsallisMDStep c p ℓ`, with `ψ q = -∑ a, √(q a)`, is at
most `2 / c * ∑ a, p a √(p a) ℓ a ^ 2`. The unconstrained step decreases every coordinate, so the
local norm at the intermediate point is bounded at `p`, which gives the constant `2 / c`. -/
private lemma stab_tsallisMDStep_le (hc : 0 < c) {p ℓ : α → ℝ} (hp : ∀ a, 0 < p a)
    (hp1 : ∀ a, p a ≤ 1) (hℓ : ∀ a, 0 ≤ ℓ a) :
    lossCLM ℓ (p - tsallisMDStep c p ℓ) -
        bregDiv (fun q ↦ -∑ a, √(q a)) (tsallisMDStep c p ℓ) p (tsallisDeriv p) / c⁻¹ ≤
      2 / c * ∑ a, p a * √(p a) * ℓ a ^ 2 := by
  set U : Set (α → ℝ) := Set.univ.pi fun _ ↦ Set.Ioi 0
  have hUD : U ⊆ Set.Ici 0 := fun z hz a ↦ (Set.mem_univ_pi.1 hz a).le
  have hF' (z : α → ℝ) (hz : z ∈ U) :=
    (hasFDerivAt_neg_sum_sqrt (Set.mem_univ_pi.1 hz)).hasFDerivWithinAt (s := Set.Ici 0)
  have hℓ' (a : α) : -(c / 4) ≤ ℓ a := (neg_nonpos.2 (by positivity)).trans (hℓ a)
  have hx (a : α) := (tsallisStep_pos_le hc hp hp1 hℓ' a).1
  obtain ⟨z, hz, h⟩ := exists_mem_segment_apply_sub_sub_bregDiv_div_le_of_hasFDerivWithinAt
    convexOn_neg_sum_sqrt (convex_pi fun _ _ ↦ convex_Ioi 0) hUD hF'
    (fun z hz ↦ (hasFDerivAt_tsallisDeriv (Set.mem_univ_pi.1 hz)).hasFDerivWithinAt)
    (inv_pos.2 hc) (lossCLM ℓ) (Set.mem_univ_pi.2 hp) (Set.mem_univ_pi.2 hx)
    (tsallisDeriv_tsallisStep hc hp hp1 hℓ')
  have h_norm := sq_lossCLM_le_of_le_mul (ℓ := ℓ) le_rfl hp hx
    (fun a ↦ (tsallisStep_le hc hp hℓ a).trans_eq (one_mul _).symm) hz
  rw [sqrt_one, mul_one, mul_one] at h_norm
  refine (h _ (mul_nonneg (by norm_num) (sum_nonneg fun a _ ↦ by
    have := hp a
    positivity)) h_norm _
    (simplex_subset_nonneg (tsallisMDStep_mem_simplex hc.ne' _ _))).trans_eq ?_
  field_simp
  ring

/-- **Regret of mirror descent with the ½-Tsallis potential and a constant learning rate**, with
local norms [Ora, Section 9.1.2]. Let `c > 0` and let the losses be nonnegative at the rounds
`t < n`. Let `p 0` be uniform and let `p (t + 1)` be the mirror descent step on the simplex from
`p t` with the potential `-∑ a, √(p a)`, the learning rate `1 / c` and the loss `ℓ t`
(`isMirrorDescentStep_iff_eq_tsallisMDStep`), at the rounds `t < n`. Then against every point `u`
of the simplex,
`∑ t < n, (⟨p t, ℓ t⟩ - ⟨u, ℓ t⟩)
  ≤ c (√k - ∑ a, √(u a)) + ∑ t < n, 2 / c * ∑ a, p t a √(p t a) ℓ t a ^ 2`,
with `k` the cardinality of `α` and `⟨p, ℓ⟩ = ∑ a, p a * ℓ a`. -/
theorem tsallisMirrorDescent_regret_le (hc : 0 < c) {ℓ p : ℕ → α → ℝ} {n : ℕ}
    (hℓ : ∀ t < n, ∀ a, 0 ≤ ℓ t a) (hp0 : p 0 = fun _ ↦ (Fintype.card α : ℝ)⁻¹)
    (hp : ∀ t < n, p (t + 1) = tsallisMDStep c (p t) (ℓ t)) {u : α → ℝ} (hu : u ∈ simplex α) :
    ∑ t ∈ range n, (∑ a, p t a * ℓ t a - ∑ a, u a * ℓ t a) ≤
      c * (√(Fintype.card α) - ∑ a, √(u a)) +
        ∑ t ∈ range n, 2 / c * ∑ a, p t a * √(p t a) * ℓ t a ^ 2 := by
  have hk : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hp_pos (t : ℕ) (ht : t ≤ n) (a : α) : 0 < p t a := by
    rcases t with _ | t
    · rw [hp0]
      positivity
    · rw [hp t ht]
      exact tsallisMDStep_pos hc.ne' _ _ a
  have hp_le_one (t : ℕ) (ht : t ≤ n) (a : α) : p t a ≤ 1 := by
    rcases t with _ | t
    · rw [hp0]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos)
    · rw [hp t ht]
      exact (simplex_subset_Icc (tsallisMDStep_mem_simplex hc.ne' _ _)).2 a
  -- the uniform weights minimize the potential over the simplex
  have h_min : IsMinOn (fun q : α → ℝ ↦ -∑ a, √(q a)) (simplex α) (p 0) := by
    have h := isMinOn_tsallisWeights one_pos (fun _ : α ↦ (0 : ℝ))
    rw [tsallisWeights_const one_ne_zero, ← hp0] at h
    simpa [dotProduct] using h
  have h_md := mirrorDescent_regret_le (convexOn_neg_sum_sqrt.subset simplex_subset_nonneg
      (convex_simplex α)) (inv_pos.2 hc) (fun t ↦ lossCLM (ℓ t)) p (fun t ↦ tsallisDeriv (p t))
      h_min (hp0 ▸ uniform_mem_simplex α) (fun t ht ↦ (isMirrorDescentStep_iff_eq_tsallisMDStep hc
        (p t) (ℓ t)).2 (hp t ht))
      (fun t ht ↦ (hasFDerivAt_neg_sum_sqrt (hp_pos t ht)).hasFDerivWithinAt) hu
  -- the potential at the uniform weights is `-√k`
  have h_F0 : -∑ a, √(p 0 a) = -√(Fintype.card α) := by
    rw [hp0, sum_const, card_univ, nsmul_eq_mul, sqrt_inv]
    congr 1
    field_simp
    rw [sq_sqrt hk.le]
  rw [h_F0, div_inv_eq_mul, sum_div, add_sub_assoc, ← sum_sub_distrib] at h_md
  calc ∑ t ∈ range n, (∑ a, p t a * ℓ t a - ∑ a, u a * ℓ t a)
      = ∑ t ∈ range n, lossCLM (ℓ t) (p t - u) := by
        refine sum_congr rfl fun t _ ↦ ?_
        simp only [map_sub, lossCLM_apply, mul_comm]
    _ ≤ (-∑ a, √(u a) - -√(Fintype.card α)) * c + ∑ t ∈ range n,
        (lossCLM (ℓ t) (p t - p (t + 1)) -
          bregDiv (fun q ↦ -∑ a, √(q a)) (p (t + 1)) (p t) (tsallisDeriv (p t)) / c⁻¹) := h_md
    _ ≤ (-∑ a, √(u a) - -√(Fintype.card α)) * c +
        ∑ t ∈ range n, 2 / c * ∑ a, p t a * √(p t a) * ℓ t a ^ 2 := by
        gcongr with t ht
        have ht := mem_range.1 ht
        rw [hp t ht]
        exact stab_tsallisMDStep_le hc (hp_pos t ht.le) (hp_le_one t ht.le) (hℓ t ht)
    _ = _ := by ring

end MirrorDescent

end LMLExplore.OnlineLearning
