/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Convex.Tsallis
public import LMLExplore.OnlineLearning.LocalNorm

/-!
# Follow the regularized leader with the ½-Tsallis potential

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

## Main statements

* `tsallisWeights_regret_succ_le_sum_sub_mul`: for positive coefficients `c t` and losses with
  `ℓ t a ≥ -c t / 4`, against every point `u` of the simplex,
  `∑ t < n + 1, (⟨p t, ℓ t⟩ - ⟨u, ℓ t⟩) ≤ c 0 (∑ a, √(p 0 a) - ∑ a, √(u a))
    + ∑ t < n, (c (t + 1) - c t) (∑ a, √(p (t + 1) a) - ∑ a, √(u a))
    + ∑ t < n + 1, 16 / c t * ∑ a, p t a √(p t a) ℓ t a ^ 2`:
  the penalty of each change of coefficient is measured at the weights of its round.
* `tsallisWeights_regret_le_of_monotone`: for coefficients `c t > 0` nondecreasing in `t` and
  losses with `ℓ t a ≥ -c t / 4`, against every point `u` of the simplex,
  `∑ t < n, (⟨p t, ℓ t⟩ - ⟨u, ℓ t⟩)
    ≤ c (n - 1) (√k - ∑ a, √(u a)) + ∑ t < n, 16 / c t * ∑ a, p t a √(p t a) ℓ t a ^ 2`,
  with `k` the cardinality of `α`.

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

/-- **The local norm along the segment to the unconstrained step.** For weights `p` in `(0, 1]`, a
point `x` with `0 < x a ≤ 4 p a`, and `z ∈ [p, x]`,
`ℓ (x - p) ^ 2 ≤ 32 ∑ a, p a √(p a) ℓ a ^ 2 * F'' z (x - p, x - p)`. -/
private lemma sq_lossCLM_le (hp : ∀ a, 0 < p a) {x : α → ℝ} (hx : ∀ a, 0 < x a)
    (hx4 : ∀ a, x a ≤ 4 * p a) {z : α → ℝ} (hz : z ∈ segment ℝ p x) :
    lossCLM ℓ (x - p) ^ 2 ≤
      (32 * ∑ a, p a * √(p a) * ℓ a ^ 2) * tsallisDeriv2 z (x - p) (x - p) := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  set z := s • p + t • x
  -- every coordinate of `z` is in `(0, 4 p a]`
  have hz_pos (a : α) : 0 < z a := by
    simp only [z, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases hs.lt_or_eq with hs | rfl
    · nlinarith [hp a, hx a]
    · simp only [zero_add] at hst
      simp [hst, hx a]
  have hz4 (a : α) : z a ≤ 4 * p a := by
    simp only [z, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hp a, hx4 a]
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
  -- `4 z a √(z a) ≤ 32 p a √(p a)`
  have h1 : √(z a) ≤ 2 * √(p a) :=
    (sqrt_le_left (by positivity)).2 (by nlinarith [sq_sqrt (hp a).le, hz4 a])
  have h2 : 4 * z a * √(z a) ≤ 32 * (p a * √(p a)) := by
    have := sqrt_nonneg (z a)
    nlinarith [hz_pos a, hz4 a, hp a]
  calc 4 * z a * √(z a) * ℓ a ^ 2 ≤ 32 * (p a * √(p a)) * ℓ a ^ 2 := by gcongr
  _ = 32 * (p a * √(p a) * ℓ a ^ 2) := by ring

end Step

/-- The Tsallis weights `tsallisWeights c (∑ s < t, ℓ s)` are the plays of FTRL on the simplex
at round `t`, with the potential `-∑ a, √(p a)`, the learning rate `1 / c` and the losses `ℓ`. -/
private lemma isFTRLPlay_tsallisWeights [Nonempty α] {c : ℝ} (hc : 0 < c) (ℓ : ℕ → α → ℝ)
    (t : ℕ) :
    IsFTRLPlay (simplex α) (fun q ↦ -∑ a, √(q a)) c⁻¹ (fun s ↦ lossCLM (ℓ s)) t
      (tsallisWeights c (∑ s ∈ range t, ℓ s)) := by
  refine ⟨tsallisWeights_mem_simplex hc.ne' _, isMinOn_iff.2 fun b hb ↦ ?_⟩
  have h := isMinOn_iff.1 (isMinOn_tsallisWeights hc (∑ s ∈ range t, ℓ s)) b hb
  have h_obj (q : α → ℝ) : c⁻¹ * ∑ s ∈ range t, lossCLM (ℓ s) q + -∑ a, √(q a) =
      c⁻¹ * ((∑ s ∈ range t, ℓ s) ⬝ᵥ q - c * ∑ a, √(q a)) := by
    simp only [lossCLM_apply, dotProduct, Finset.sum_apply, sum_mul]
    rw [sum_comm]
    have := hc.ne'
    field_simp
    ring
  rw [h_obj, h_obj]
  exact mul_le_mul_of_nonneg_left h (inv_pos.2 hc).le

/-- **Regret of FTRL with the ½-Tsallis potential, with the penalties of the changes of
coefficient** [ZS21], [Ora, Section 9.3]. Let the coefficients `c t` be positive, and let the
losses satisfy `ℓ t a ≥ -c t / 4` at the rounds `t ≤ n`. Then the Tsallis weights
`p t = tsallisWeights (c t) (∑ s < t, ℓ s)` satisfy, against every point `u` of the simplex,
`∑ t < n + 1, (⟨p t, ℓ t⟩ - ⟨u, ℓ t⟩) ≤ c 0 (∑ a, √(p 0 a) - ∑ a, √(u a))
  + ∑ t < n, (c (t + 1) - c t) (∑ a, √(p (t + 1) a) - ∑ a, √(u a))
  + ∑ t < n + 1, 16 / c t * ∑ a, p t a √(p t a) ℓ t a ^ 2`,
with `⟨p, ℓ⟩ = ∑ a, p a * ℓ a`. The first weights `p 0` are uniform. The coefficients need not be
monotone; the penalty of each round is measured at its weights, which is what bounds the regret of
Tsallis-INF in stochastic environments, where the weights of the suboptimal arms vanish. -/
theorem tsallisWeights_regret_succ_le_sum_sub_mul {c : ℕ → ℝ} (hc : ∀ t, 0 < c t)
    {ℓ : ℕ → α → ℝ} {n : ℕ} (hℓ : ∀ t ≤ n, ∀ a, -(c t / 4) ≤ ℓ t a) {u : α → ℝ}
    (hu : u ∈ simplex α) :
    ∑ t ∈ range (n + 1), (∑ a, tsallisWeights (c t) (∑ s ∈ range t, ℓ s) a * ℓ t a -
        ∑ a, u a * ℓ t a) ≤
      c 0 * (∑ a, √(tsallisWeights (c 0) (0 : α → ℝ) a) - ∑ a, √(u a)) +
      ∑ t ∈ range n, (c (t + 1) - c t) *
        (∑ a, √(tsallisWeights (c (t + 1)) (∑ s ∈ range (t + 1), ℓ s) a) - ∑ a, √(u a)) +
      ∑ t ∈ range (n + 1), 16 / c t * ∑ a, tsallisWeights (c t) (∑ s ∈ range t, ℓ s) a *
        √(tsallisWeights (c t) (∑ s ∈ range t, ℓ s) a) * ℓ t a ^ 2 := by
  have := nonempty_of_mem_simplex hu
  set p : ℕ → α → ℝ := fun t ↦ tsallisWeights (c t) (∑ s ∈ range t, ℓ s) with hp_def
  have hp_pos (t : ℕ) (a : α) : 0 < p t a := tsallisWeights_pos (hc t).ne' _ a
  have hp_le_one (t : ℕ) (a : α) : p t a ≤ 1 :=
    (simplex_subset_Icc (tsallisWeights_mem_simplex (hc t).ne' _)).2 a
  set U : Set (α → ℝ) := Set.univ.pi fun _ ↦ Set.Ioi 0
  have hUD : U ⊆ Set.Ici 0 := fun z hz a ↦ (Set.mem_univ_pi.1 hz a).le
  have h := ftrl_regret_succ_le_sum_inv_sub_inv_of_localNorm convexOn_neg_sum_sqrt
    (convex_simplex α) (simplex_subset_nonneg (α := α)) (convex_pi fun _ _ ↦ convex_Ioi 0) hUD
    (fun z hz ↦ (hasFDerivAt_neg_sum_sqrt (Set.mem_univ_pi.1 hz)).hasFDerivWithinAt)
    (fun z hz ↦ (hasFDerivAt_tsallisDeriv (Set.mem_univ_pi.1 hz)).hasFDerivWithinAt)
    (η := fun t ↦ (c t)⁻¹) (fun t ↦ inv_pos.2 (hc t)) (fun s ↦ lossCLM (ℓ s)) p
    (fun t ↦ tsallisStep (c t) (ℓ t) (p t)) (fun t _ ↦ isFTRLPlay_tsallisWeights (hc t) ℓ t)
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
  have hp0 : p 0 = tsallisWeights (c 0) 0 := by simp [hp_def]
  convert h using 1
  · refine sum_congr rfl fun t _ ↦ ?_
    rw [map_sub, lossCLM_apply, lossCLM_apply]
    simp only [hp_def, mul_comm]
  · rw [hp0, div_inv_eq_mul]
    simp only [inv_inv]
    congr 1
    · congr 1
      · ring
      · exact sum_congr rfl fun t _ ↦ by ring
    · refine sum_congr rfl fun t _ ↦ ?_
      have := (hc t).ne'
      field_simp
      ring

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
  have h_u : 0 ≤ √(Fintype.card α) - ∑ a, √(u a) := sub_nonneg.2 (sum_sqrt_le_sqrt_card hu)
  rcases n with _ | n
  · simpa using mul_nonneg (hc 0).le h_u
  refine (tsallisWeights_regret_succ_le_sum_sub_mul hc
    (fun t ht ↦ hℓ t (Nat.lt_succ_of_le ht)) hu).trans (add_le_add ?_ le_rfl)
  -- every sum of square roots of weights is at most `√k`, and the penalties telescope
  have h_sqrt (L : α → ℝ) (t : ℕ) : ∑ a, √(tsallisWeights (c t) L a) ≤ √(Fintype.card α) :=
    sum_sqrt_le_sqrt_card (tsallisWeights_mem_simplex (hc t).ne' L)
  have h_pen : ∑ t ∈ range n, (c (t + 1) - c t) *
      (∑ a, √(tsallisWeights (c (t + 1)) (∑ s ∈ range (t + 1), ℓ s) a) - ∑ a, √(u a)) ≤
      (c n - c 0) * (√(Fintype.card α) - ∑ a, √(u a)) := by
    rw [← sum_range_sub c, sum_mul]
    refine sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 (hc_mono t.le_succ))
    linarith [h_sqrt (∑ s ∈ range (t + 1), ℓ s) (t + 1)]
  have h0 := mul_le_mul_of_nonneg_left (sub_le_sub_right (h_sqrt 0 0) (∑ a, √(u a))) (hc 0).le
  rw [Nat.add_sub_cancel]
  linarith

end LMLExplore.OnlineLearning
