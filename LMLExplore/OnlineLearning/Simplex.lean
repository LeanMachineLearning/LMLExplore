/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Convex.NegEntropy
public import LMLExplore.Analysis.Normed.Lp.PiLp
public import LMLExplore.OnlineLearning.ExponentialWeights
public import LMLExplore.OnlineLearning.FTRL

/-!
# Online linear optimization on the probability simplex

Follow the regularized leader on the probability simplex of a finite set `α`, with the unnormalized
negative entropy `negEntropy` as potential and learning rate `η`, is the exponential weights
algorithm [LS, Example 28.3, (28.5)]: at round `t` it plays `softmax (-(η • ∑ s < t, ŷ s))`,
where `ŷ s a` is the loss of the vertex `a` at round `s`.

The space of plays is `PiLp 1 (fun _ : α ↦ ℝ)`, whose `ℓ¹` norm makes the negative entropy
`1`-strongly convex on the simplex (Pinsker's inequality); the losses are in its dual, normed by
the sup norm. The regret bound of FTRL with a strongly convex potential then gives, against every
point of the simplex, `R_n ≤ log k / η + η / 2 ∑ t < n, ‖y t‖ ^ 2` with `k` the cardinality of
`α`, and `R_n ≤ √(2 n log k)` for losses of dual norm at most `1` and the learning rate
`η = √(2 log k / n)` [LS, Proposition 28.7], which [LS] states for mirror descent and losses in
`[0, 1]`.

## Main statements

* `negEntropy_sub_sum_mul_eq`: on the simplex, `negEntropy b - ∑ c, b c * v c` is the relative
  entropy of `b` with respect to `softmax v`, up to an additive constant.
* `isFTRLPlay_negEntropy_iff`: the plays of FTRL on the simplex with the negative entropy are the
  exponential weights of the cumulative losses of the vertices.
* `ftrl_regret_le_of_negEntropy`: the regret bound `log k / η + η / 2 ∑ t < n, ‖y t‖ ^ 2`.
* `ftrl_regret_le_sqrt_of_negEntropy`: [LS, Proposition 28.7] for FTRL, `R_n ≤ √(2 n log k)`.
* `softmax_regret_le_sqrt`: the same bound for exponential weights stated on `α → ℝ`, for losses
  in `[-1, 1]`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open Finset Real WithLp

namespace LMLExplore.OnlineLearning

variable {α : Type*} [Fintype α]

/-- On the simplex, `negEntropy b - ∑ c, b c * v c` is, up to the constant
`log (∑ c, exp (v c)) + 1`, the relative entropy `∑ c, b c * log (b c / softmax v c)` of `b` with
respect to the exponential weights of `v`. -/
theorem negEntropy_sub_sum_mul_eq (v : α → ℝ) {b : α → ℝ} (hb : b ∈ simplex α) :
    negEntropy b - ∑ c, b c * v c =
      ∑ c, b c * log (b c / softmax v c) - log (∑ c, exp (v c)) - 1 := by
  have := nonempty_of_mem_simplex hb
  have hZ : 0 < ∑ c, exp (v c) := sum_pos (fun c _ ↦ exp_pos (v c)) univ_nonempty
  have h_pt (c : α) : b c * log (b c / softmax v c) =
      b c * log (b c) - b c * v c + b c * log (∑ c, exp (v c)) := by
    rcases eq_or_ne (b c) 0 with h0 | h0
    · simp [h0]
    rw [log_div h0 (softmax_pos v c).ne', softmax_apply, log_div (exp_pos _).ne' hZ.ne', log_exp]
    ring
  simp_rw [h_pt, sum_add_distrib, sum_sub_distrib, ← sum_mul, (mem_simplex_iff.1 hb).2, one_mul,
    negEntropy_of_mem_simplex hb]
  ring

/-- **FTRL with the negative entropy is exponential weights** [LS, Example 28.3, (28.5)]. On the
simplex, a play of FTRL at round `t` with the unnormalized negative entropy as potential, learning
rate `η` and losses `y` is exactly the softmax of `-η` times the cumulative losses of the
vertices. -/
theorem isFTRLPlay_negEntropy_iff [Nonempty α] [DecidableEq α] {η : ℝ}
    {y : ℕ → PiLp 1 (fun _ : α ↦ ℝ) →L[ℝ] ℝ} {t : ℕ} {x : PiLp 1 fun _ : α ↦ ℝ} :
    IsFTRLPlay (ofLp ⁻¹' simplex α) (fun x ↦ negEntropy (ofLp x)) η y t x ↔
      ofLp x = softmax (-(η • ∑ s ∈ range t, fun c ↦ y s (PiLp.single 1 c 1))) := by
  set v := -(η • ∑ s ∈ range t, fun c ↦ y s (PiLp.single 1 c 1))
  set p := softmax v
  -- the objective at `b` in the simplex is the relative entropy of `b` with respect to `p`,
  -- up to a constant
  have h_obj (b : PiLp 1 fun _ : α ↦ ℝ) (hb : ofLp b ∈ simplex α) :
      η * ∑ s ∈ range t, y s b + negEntropy (ofLp b) =
        ∑ c, b c * log (b c / p c) - log (∑ c, exp (v c)) - 1 := by
    rw [← negEntropy_sub_sum_mul_eq v hb]
    simp_rw [PiLp.apply_eq_sum_smul_apply_single 1 (y _) b, v, Pi.neg_apply, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul]
    simp only [mul_neg, sum_neg_distrib, sub_neg_eq_add, mul_sum]
    rw [add_comm, sum_comm]
    simp_rw [mul_left_comm]
  have hp : p ∈ simplex α := softmax_mem_simplex v
  have hp0 (c : α) : p c ≠ 0 := (softmax_pos v c).ne'
  constructor
  · intro hx
    -- the objective at `x` is at most its value at `p`, so the relative entropy vanishes
    have h_le := isMinOn_iff.1 hx.isMinOn (toLp 1 p) (by simpa using hp)
    rw [h_obj x hx.mem, h_obj _ (by simpa using hp), ofLp_toLp] at h_le
    have hxp (c : α) : p c = 0 → x c = 0 := fun h ↦ absurd h (hp0 c)
    have h_gibbs := sum_mul_log_div_nonneg (mem_simplex_iff.1 hx.mem).1 (mem_simplex_iff.1 hp).1
      hxp ((mem_simplex_iff.1 hp).2.trans (mem_simplex_iff.1 hx.mem).2.symm).le
    simp only [log_div_self, mul_zero, sum_const_zero] at h_le
    exact (sum_mul_log_div_eq_zero_iff hx.mem hp hxp).1 (by linarith)
  · intro hx
    have hx_mem : ofLp x ∈ simplex α := hx ▸ hp
    refine ⟨hx_mem, isMinOn_iff.2 fun b hb ↦ ?_⟩
    rw [h_obj x hx_mem, h_obj b hb, hx]
    have h_gibbs := sum_mul_log_div_nonneg (mem_simplex_iff.1 hb).1 (mem_simplex_iff.1 hp).1
      (fun c h ↦ absurd h (hp0 c)) ((mem_simplex_iff.1 hp).2.trans (mem_simplex_iff.1 hb).2.symm).le
    simp only [log_div_self, mul_zero, sum_const_zero]
    linarith

/-- **Regret of FTRL with the negative entropy on the simplex.** Let each `a t`, for `t ≤ n`, be
a play of FTRL on the simplex of `PiLp 1 (fun _ : α ↦ ℝ)` with the unnormalized negative entropy
as potential, learning rate `η > 0` and losses `y`. Then the regret against every point `u` of
the simplex is at most `log k / η + η / 2 ∑ t < n, ‖y t‖ ^ 2`, with `k` the cardinality of `α`
and `‖y t‖` the operator norm, the sup norm of the losses of the vertices. -/
theorem ftrl_regret_le_of_negEntropy {n : ℕ} {η : ℝ} (hη : 0 < η)
    (y : ℕ → PiLp 1 (fun _ : α ↦ ℝ) →L[ℝ] ℝ) (a : ℕ → PiLp 1 fun _ : α ↦ ℝ)
    (ha : ∀ t ≤ n, IsFTRLPlay (ofLp ⁻¹' simplex α) (fun x ↦ negEntropy (ofLp x)) η y t (a t))
    {u : PiLp 1 fun _ : α ↦ ℝ} (hu : ofLp u ∈ simplex α) :
    ∑ t ∈ range n, y t (a t - u) ≤
      log (Fintype.card α) / η + η / 2 * ∑ t ∈ range n, ‖y t‖ ^ 2 := by
  classical
  have := nonempty_of_mem_simplex hu
  -- the plays are exponential weights, whose coordinates are positive
  have h_ne (t : ℕ) (ht : t ≤ n) (c : α) : a t c ≠ 0 := by
    rw [isFTRLPlay_negEntropy_iff.1 (ha t ht)]
    exact (softmax_pos _ c).ne'
  have h := ftrl_regret_le_of_strongConvexOn strongConvexOn_negEntropy one_pos hη y a ha _
    (fun t ht ↦ (hasFDerivAt_negEntropy (h_ne t ht.le)).hasFDerivWithinAt) hu
  -- the range of the negative entropy on the simplex is at most `log k`
  have h_range : (negEntropy (ofLp u) - negEntropy (ofLp (a 0))) / η ≤
      log (Fintype.card α) / η := by
    refine div_le_div_of_nonneg_right ?_ hη.le
    linarith [negEntropy_le_neg_one hu,
      neg_log_card_sub_one_le_negEntropy (ha 0 (Nat.zero_le n)).mem]
  rw [mul_one] at h
  linarith

/-- **Regret of FTRL with the negative entropy on the simplex** [LS, Proposition 28.7]. For
losses `y t` of operator norm at most `1` (the sup norm of the losses of the vertices) and the
learning rate `η = √(2 log k / n)`, with `k` the cardinality of `α`, the regret of FTRL on the
simplex with the unnormalized negative entropy as potential, against every point of the simplex,
is at most `√(2 n log k)`. -/
theorem ftrl_regret_le_sqrt_of_negEntropy {n : ℕ}
    (y : ℕ → PiLp 1 (fun _ : α ↦ ℝ) →L[ℝ] ℝ) (hy : ∀ t < n, ‖y t‖ ≤ 1)
    (a : ℕ → PiLp 1 fun _ : α ↦ ℝ)
    (ha : ∀ t ≤ n, IsFTRLPlay (ofLp ⁻¹' simplex α) (fun x ↦ negEntropy (ofLp x))
      √(2 * log (Fintype.card α) / n) y t (a t))
    {u : PiLp 1 fun _ : α ↦ ℝ} (hu : ofLp u ∈ simplex α) :
    ∑ t ∈ range n, y t (a t - u) ≤ √(2 * n * log (Fintype.card α)) := by
  have := nonempty_of_mem_simplex hu
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases (Nat.one_le_iff_ne_zero.2 Fintype.card_ne_zero : 1 ≤ Fintype.card α).eq_or_lt with
    hk | hk
  · -- with a single coordinate, the simplex is a single point
    have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.1 hk.symm.le
    have h_zero (t : ℕ) (ht : t ∈ range n) : y t (a t - u) = 0 := by
      have : a t = u := ofLp_injective 1 <| by
        rw [eq_one_of_mem_simplex (ha t (mem_range.1 ht).le).mem, eq_one_of_mem_simplex hu]
      rw [this, sub_self, map_zero]
    rw [sum_eq_zero h_zero]
    exact sqrt_nonneg _
  set L := log (Fintype.card α)
  have hL : 0 < L := log_pos (by exact_mod_cast hk)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set η := √(2 * L / n)
  have hη : 0 < η := sqrt_pos.2 (by positivity)
  have hη2 : η ^ 2 = 2 * L / n := sq_sqrt (by positivity)
  have h := ftrl_regret_le_of_negEntropy hη y a ha hu
  have h_sum : ∑ t ∈ range n, ‖y t‖ ^ 2 ≤ n := by
    calc ∑ t ∈ range n, ‖y t‖ ^ 2
    _ ≤ ∑ t ∈ range n, (1 : ℝ) :=
      sum_le_sum fun t ht ↦ pow_le_one₀ (norm_nonneg _) (hy t (mem_range.1 ht))
    _ = n := by simp
  -- with this learning rate, both terms of the bound are `η n / 2 = √(n L / 2)`
  have h_pen : L / η = η * n / 2 := by
    rw [div_eq_iff hη.ne', show η * n / 2 * η = η ^ 2 * n / 2 by ring, hη2]
    field_simp
  have h_sqrt : √(2 * n * L) = η * n := by
    rw [← sqrt_sq (by positivity : 0 ≤ η * n), mul_pow, hη2]
    congr 1
    field_simp
  rw [h_sqrt]
  nlinarith

/-- **Regret of exponential weights** for losses in `[-1, 1]` [LS, Proposition 28.7]. For losses
`ℓ t : α → ℝ` with `|ℓ t b| ≤ 1` at the rounds `t < n` and the learning rate
`η = √(2 log k / n)`, with `k` the cardinality of `α`, the exponential weights
`p t = softmax (-(η • ∑ s < t, ℓ s))` satisfy, against every point `u` of the simplex,
`∑ t < n, (⟨p t, ℓ t⟩ - ⟨u, ℓ t⟩) ≤ √(2 n log k)`, with `⟨p, ℓ⟩ = ∑ b, p b * ℓ b`. -/
theorem softmax_regret_le_sqrt {n : ℕ} {ℓ : ℕ → α → ℝ}
    (hℓ : ∀ t < n, ∀ b, |ℓ t b| ≤ 1) {u : α → ℝ} (hu : u ∈ simplex α) :
    ∑ t ∈ range n, (∑ b, softmax (-(√(2 * log (Fintype.card α) / n) • ∑ s ∈ range t, ℓ s)) b *
        ℓ t b - ∑ b, u b * ℓ t b) ≤ √(2 * n * log (Fintype.card α)) := by
  classical
  have := nonempty_of_mem_simplex hu
  -- the losses as linear functionals on `PiLp 1 (fun _ : α ↦ ℝ)`
  set y : ℕ → PiLp 1 (fun _ : α ↦ ℝ) →L[ℝ] ℝ :=
    fun t ↦ ∑ b, ℓ t b • PiLp.proj (𝕜 := ℝ) 1 (fun _ : α ↦ ℝ) b
  have hy_apply (t : ℕ) (x : PiLp 1 fun _ : α ↦ ℝ) : y t x = ∑ b, ℓ t b * x b := by
    simp [y]
  have hy_single (t : ℕ) : (fun c ↦ y t (PiLp.single 1 c 1)) = ℓ t :=
    funext fun c ↦ by simp [y, PiLp.single_apply]
  have hy (t : ℕ) (ht : t < n) : ‖y t‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
    rw [hy_apply, one_mul, PiLp.norm_eq_of_L1, Real.norm_eq_abs]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ ↦ ?_)
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (hℓ t ht b)
  -- the exponential weights are the plays of FTRL with the negative entropy
  set η := √(2 * log (Fintype.card α) / n)
  have ha (t : ℕ) : IsFTRLPlay (ofLp ⁻¹' simplex α) (fun x ↦ negEntropy (ofLp x)) η y t
      (toLp 1 (softmax (-(η • ∑ s ∈ range t, ℓ s)))) := by
    rw [isFTRLPlay_negEntropy_iff, ofLp_toLp]
    simp_rw [hy_single]
  have h := ftrl_regret_le_sqrt_of_negEntropy y hy _ (fun t _ ↦ ha t) (u := toLp 1 u)
    (by simpa using hu)
  refine (le_of_eq (sum_congr rfl fun t _ ↦ ?_)).trans h
  rw [hy_apply, ← sum_sub_distrib]
  refine sum_congr rfl fun b _ ↦ ?_
  rw [PiLp.sub_apply, PiLp.toLp_apply, PiLp.toLp_apply]
  ring

end LMLExplore.OnlineLearning
