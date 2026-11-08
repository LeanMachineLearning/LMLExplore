/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Convex.NegEntropy
public import LMLExplore.Analysis.Normed.Lp.PiLp
public import LMLExplore.Analysis.Real.Sqrt
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

For nonnegative losses, the stability terms of exponential weights are bounded by local norms
[Ora, Section 7.5; BCB12, proof of Theorem 3.1]. At a probability vector `p` with positive
coordinates, the stability term `q ↦ ⟨p - q, y⟩ - D(q, p) / η`, with `D` the relative entropy
(the Bregman divergence of the negative entropy on the simplex), has maximum
`⟨p, y⟩ + log (∑ a, p a * exp (-(η * y a))) / η` over the simplex, by the Gibbs variational
principle. Since `log x ≤ x - 1` and `exp (-x) ≤ 1 - x + x ^ 2 / 2` for `x ≥ 0`, it is at most
`η / 2 * ⟨p, y ^ 2⟩`. With FTRL for nonincreasing learning rates `η t`, the weights
`p t = softmax (-(η t • ∑ s < t, y s))` then satisfy, against every point `u` of the simplex,
`∑ t < n, (⟨p t, y t⟩ - ⟨u, y t⟩) ≤ log k / η (n - 1) + ∑ t < n, η t / 2 * ⟨p t, (y t) ^ 2⟩`.
Its case of a constant learning rate and a vertex `u` is the bound `softmax_regret_le` used by
Exp3, Exp3-IX and Exp4. For losses that may be negative but satisfy `η t * y t a ≥ -1`, such as
the loss estimates of adversarial linear bandits, `exp (-x) ≤ 1 - x + x ^ 2` for `x ≥ -1` gives the
same bound with `η t * ⟨p t, (y t) ^ 2⟩` in place of `η t / 2 * ⟨p t, (y t) ^ 2⟩`
[LS, proof of Theorem 27.1].

## Main statements

* `negEntropy_sub_sum_mul_eq`: on the simplex, `negEntropy b - ∑ c, b c * v c` is the relative
  entropy of `b` with respect to `softmax v`, up to an additive constant.
* `isFTRLPlay_negEntropy_iff`: the plays of FTRL on the simplex with the negative entropy are the
  exponential weights of the cumulative losses of the vertices.
* `ftrl_regret_le_of_negEntropy`: the regret bound `log k / η + η / 2 ∑ t < n, ‖y t‖ ^ 2`.
* `ftrl_regret_le_sqrt_of_negEntropy`: [LS, Proposition 28.7] for FTRL, `R_n ≤ √(2 n log k)`.
* `softmax_regret_le_sqrt`: the same bound for exponential weights stated on `α → ℝ`, for losses
  in `[-1, 1]`.
* `isGreatest_sum_sub_mul_sub_sum_mul_log_div_div`: the maximum over the simplex of the stability
  term of exponential weights at `p`.
* `sum_sub_mul_sub_sum_mul_log_div_div_le`: the stability term is at most
  `(∑ a, p a * (exp (-(η * y a)) - 1 + η * y a)) / η`.
* `sum_sub_mul_sub_sum_mul_log_div_div_le_mul_sum_mul_sq`: for a nonnegative loss `y`, the
  stability term is at most `η / 2 * ∑ a, p a * y a ^ 2`.
* `softmax_regret_le_sum_exp_of_antitone`: the regret bound of exponential weights with
  nonincreasing learning rates through the stability terms
  `(∑ a, p a * (exp (-(η * y a)) - 1 + η * y a)) / η`, for every loss.
* `softmax_regret_le_of_antitone`: the local-norm regret bound of exponential weights with
  nonincreasing learning rates, for nonnegative losses.
* `softmax_regret_le`: its case of a constant learning rate, against every coordinate.
* `softmax_regret_le_of_antitone_of_neg_one_le`, `softmax_regret_le_of_neg_one_le`: the local-norm
  bound `∑ t < n, η t * ⟨p t, (y t) ^ 2⟩` for losses with `η t * y t a ≥ -1`, which may be
  negative.

## References

* [BCB12] S. Bubeck and N. Cesa-Bianchi, *Regret analysis of stochastic and nonstochastic
  multi-armed bandit problems*, Foundations and Trends in Machine Learning 5(1), 2012.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
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
  -- the relative entropy with respect to the Gibbs vector of `v` under the constant `1`
  have h := sum_mul_log_div_mul_exp_div_eq (p := fun _ ↦ 1) (v := v) (mem_simplex_iff.1 hb).2
    (fun _ h ↦ absurd h one_ne_zero)
    (by simpa using (sum_pos (fun c _ ↦ exp_pos (v c)) univ_nonempty).ne')
  simp only [one_mul, div_one] at h
  simp_rw [softmax_apply, h, negEntropy_of_mem_simplex hb]
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
  -- with this learning rate, both terms of the bound are `η n / 2`, which sum to `√(2 n L)`
  have h_tune := div_sqrt_add_sqrt_mul_div_two L hn'.le
  set η := √(2 * L / n)
  have hη : 0 < η := sqrt_pos.2 (by positivity)
  have h := ftrl_regret_le_of_negEntropy hη y a ha hu
  have h_sum : ∑ t ∈ range n, ‖y t‖ ^ 2 ≤ n := by
    calc ∑ t ∈ range n, ‖y t‖ ^ 2
    _ ≤ ∑ t ∈ range n, (1 : ℝ) :=
      sum_le_sum fun t ht ↦ pow_le_one₀ (norm_nonneg _) (hy t (mem_range.1 ht))
    _ = n := by simp
  rw [← h_tune]
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

/-! ### Local norms and nonincreasing learning rates -/

/-- The stability term `∑ a, (p a - q a) * y a - D(q, p) / η` of exponential weights, with
`D(q, p) = ∑ a, q a * log (q a / p a)`, written through the objective of the Gibbs variational
principle for the vector `-(η • y)`. -/
private lemma sum_sub_mul_sub_sum_mul_log_div_div_eq (p q y : α → ℝ) {η : ℝ} (hη : η ≠ 0) :
    ∑ a, (p a - q a) * y a - (∑ a, q a * log (q a / p a)) / η =
      ∑ a, p a * y a + (∑ a, q a * -(η * y a) - ∑ a, q a * log (q a / p a)) / η := by
  have h1 : ∑ a, (p a - q a) * y a = ∑ a, p a * y a - ∑ a, q a * y a := by
    simp_rw [sub_mul, sum_sub_distrib]
  have h2 : ∑ a, q a * -(η * y a) = -(η * ∑ a, q a * y a) := by
    rw [mul_sum, ← sum_neg_distrib]
    exact sum_congr rfl fun a _ ↦ by ring
  rw [h1, h2]
  field_simp
  ring

/-- **The stability term of exponential weights** [Ora, Section 7.5]. For a probability vector `p`
with positive coordinates, a loss `y` and a learning rate `η > 0`, the stability term of FTRL with
the negative entropy at `p`, `q ↦ ∑ a, (p a - q a) * y a - D(q, p) / η` with
`D(q, p) = ∑ a, q a * log (q a / p a)` the relative entropy, has maximum
`∑ a, p a * y a + log (∑ a, p a * exp (-(η * y a))) / η` over the simplex. This is the Gibbs
variational principle for the vector `-(η • y)`. -/
theorem isGreatest_sum_sub_mul_sub_sum_mul_log_div_div {p : α → ℝ} (hp : p ∈ simplex α)
    (hp0 : ∀ a, 0 < p a) (y : α → ℝ) {η : ℝ} (hη : 0 < η) :
    IsGreatest ((fun q ↦ ∑ a, (p a - q a) * y a - (∑ a, q a * log (q a / p a)) / η) '' simplex α)
      (∑ a, p a * y a + log (∑ a, p a * exp (-(η * y a))) / η) := by
  obtain ⟨⟨q, hq, hq_eq⟩, h_le⟩ :=
    isGreatest_sum_mul_sub_sum_mul_log_div hp hp0 fun a ↦ -(η * y a)
  refine ⟨⟨q, hq, ?_⟩, ?_⟩
  · simp only at hq_eq ⊢
    rw [sum_sub_mul_sub_sum_mul_log_div_div_eq p q y hη.ne', hq_eq]
  · rintro _ ⟨q', hq', rfl⟩
    simp only
    rw [sum_sub_mul_sub_sum_mul_log_div_div_eq p q' y hη.ne']
    exact add_le_add le_rfl (div_le_div_of_nonneg_right (h_le ⟨q', hq', rfl⟩) hη.le)

/-- **Stability of exponential weights.** For probability vectors `p` and `q` with `q a = 0`
whenever `p a = 0`, a loss `y` and a learning rate `η > 0`, the stability term
`∑ a, (p a - q a) * y a - D(q, p) / η`, with `D(q, p) = ∑ a, q a * log (q a / p a)`, is at most
`(∑ a, p a * (exp (-(η * y a)) - 1 + η * y a)) / η` [Ora, Section 7.5; BCB12, proof of
Theorem 3.1]. For a nonnegative loss, this is at most `η / 2 * ∑ a, p a * y a ^ 2`
(`sum_sub_mul_sub_sum_mul_log_div_div_le_mul_sum_mul_sq`). -/
theorem sum_sub_mul_sub_sum_mul_log_div_div_le {p q : α → ℝ} (hp : p ∈ simplex α)
    (hq : q ∈ simplex α) (hqp : ∀ a, p a = 0 → q a = 0) (y : α → ℝ) {η : ℝ} (hη : 0 < η) :
    ∑ a, (p a - q a) * y a - (∑ a, q a * log (q a / p a)) / η ≤
      (∑ a, p a * (exp (-(η * y a)) - 1 + η * y a)) / η := by
  have hp1 := (mem_simplex_iff.1 hp).2
  have hZ : 0 < ∑ a, p a * exp (-(η * y a)) :=
    sum_mul_pos_of_mem_simplex hp fun a ↦ exp_pos (-(η * y a))
  -- the Gibbs variational principle and `log Z ≤ Z - 1`
  have h_gibbs := sum_mul_sub_sum_mul_log_div_le_log_sum_mul_exp hp hq hqp fun a ↦ -(η * y a)
  have h_log := log_le_sub_one_of_pos hZ
  have h_expand : ∑ a, p a * (exp (-(η * y a)) - 1 + η * y a) =
      ∑ a, p a * exp (-(η * y a)) - 1 + η * ∑ a, p a * y a := by
    simp_rw [mul_add, mul_sub, mul_one, sum_add_distrib, sum_sub_distrib, hp1, mul_sum]
    congr 1
    exact sum_congr rfl fun a _ ↦ by ring
  rw [sum_sub_mul_sub_sum_mul_log_div_div_eq p q y hη.ne', h_expand, add_div,
    mul_div_cancel_left₀ _ hη.ne', add_comm (∑ a, p a * y a)]
  exact add_le_add (div_le_div_of_nonneg_right (h_gibbs.trans h_log) hη.le) le_rfl

/-- **Local-norm stability of exponential weights** [Ora, Section 7.5; BCB12, proof of
Theorem 3.1]. For probability vectors `p` and `q` with `q a = 0` whenever `p a = 0`, a nonnegative
loss `y` and a learning rate `η > 0`, the stability term
`∑ a, (p a - q a) * y a - D(q, p) / η`, with `D(q, p) = ∑ a, q a * log (q a / p a)`, is at most
`η / 2 * ∑ a, p a * y a ^ 2`. -/
theorem sum_sub_mul_sub_sum_mul_log_div_div_le_mul_sum_mul_sq {p q : α → ℝ} (hp : p ∈ simplex α)
    (hq : q ∈ simplex α) (hqp : ∀ a, p a = 0 → q a = 0) {y : α → ℝ} (hy : ∀ a, 0 ≤ y a) {η : ℝ}
    (hη : 0 < η) :
    ∑ a, (p a - q a) * y a - (∑ a, q a * log (q a / p a)) / η ≤
      η / 2 * ∑ a, p a * y a ^ 2 := by
  have h_sq := sum_mul_exp_neg_sub_one_add_le (mem_simplex_iff.1 hp).1 hy hη.le
  have h_div : (η ^ 2 / 2 * ∑ a, p a * y a ^ 2) / η = η / 2 * ∑ a, p a * y a ^ 2 := by
    field_simp [hη.ne']
  calc _ ≤ _ := sum_sub_mul_sub_sum_mul_log_div_div_le hp hq hqp y hη
  _ ≤ (η ^ 2 / 2 * ∑ a, p a * y a ^ 2) / η := div_le_div_of_nonneg_right h_sq hη.le
  _ = _ := h_div

/-- **Regret of exponential weights with nonincreasing learning rates**, through the exponential
stability terms [Ora, Section 7.5; BCB12, proof of Theorem 3.1]. For losses `y t` and nonincreasing
learning rates `η t > 0`, the weights `p t = softmax (-(η t • ∑ s < t, y s))` satisfy, against
every point `u` of the simplex,
`∑ t < n, (⟨p t, y t⟩ - ⟨u, y t⟩) ≤ log k / η (n - 1)
  + ∑ t < n, (∑ b, p t b * (exp (-(η t * y t b)) - 1 + η t * y t b)) / η t`,
with `k` the cardinality of `α` and `⟨p, y⟩ = ∑ b, p b * y b`. The weights are the plays of FTRL
on the simplex with the negative entropy and the rates `η t`. No sign condition on the losses is
needed; the local-norm bounds `softmax_regret_le_of_antitone` (nonnegative losses) and
`softmax_regret_le_of_antitone_of_neg_one_le` (losses with `η t * y t b ≥ -1`) bound the
stability terms. -/
theorem softmax_regret_le_sum_exp_of_antitone {η : ℕ → ℝ} (hη : ∀ t, 0 < η t)
    (hη_anti : Antitone η) (y : ℕ → α → ℝ) (n : ℕ) {u : α → ℝ} (hu : u ∈ simplex α) :
    ∑ t ∈ range n, (∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b - ∑ b, u b * y t b) ≤
      log (Fintype.card α) / η (n - 1) +
        ∑ t ∈ range n, (∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b *
          (exp (-(η t * y t b)) - 1 + η t * y t b)) / η t := by
  classical
  have := nonempty_of_mem_simplex hu
  have h_log : 0 ≤ log (Fintype.card α) := log_natCast_nonneg _
  set p : ℕ → α → ℝ := fun t ↦ softmax (-(η t • ∑ s ∈ range t, y s)) with hp_def
  have hp_mem (t : ℕ) : p t ∈ simplex α := softmax_mem_simplex _
  have hp_pos (t : ℕ) (c : α) : 0 < p t c := softmax_pos _ c
  -- the stability terms `(∑ b, p t b * (exp (-(η t * y t b)) - 1 + η t * y t b)) / η t`
  set B : ℕ → ℝ := fun t ↦ (∑ b, p t b * (exp (-(η t * y t b)) - 1 + η t * y t b)) / η t
    with hB_def
  rcases n with _ | m
  · simpa using div_nonneg h_log (hη 0).le
  -- the losses as linear functionals on `PiLp 1 (fun _ : α ↦ ℝ)`
  set Y : ℕ → PiLp 1 (fun _ : α ↦ ℝ) →L[ℝ] ℝ :=
    fun t ↦ ∑ b, y t b • PiLp.proj (𝕜 := ℝ) 1 (fun _ : α ↦ ℝ) b
  have hY_apply (t : ℕ) (x : PiLp 1 fun _ : α ↦ ℝ) : Y t x = ∑ b, y t b * x b := by
    simp [Y]
  have hY_single (t : ℕ) : (fun c ↦ Y t (PiLp.single 1 c 1)) = y t :=
    funext fun c ↦ by simp [Y, PiLp.single_apply]
  -- the exponential weights are the plays of FTRL with the negative entropy
  set a : ℕ → PiLp 1 (fun _ : α ↦ ℝ) := fun t ↦ toLp 1 (p t)
  have ha (t : ℕ) :
      IsFTRLPlay (ofLp ⁻¹' simplex α) (fun x ↦ negEntropy (ofLp x)) (η t) Y t (a t) := by
    rw [isFTRLPlay_negEntropy_iff, ofLp_toLp]
    simp_rw [hY_single, hp_def]
  have hF' (t : ℕ) : HasFDerivWithinAt (fun x : PiLp 1 (fun _ : α ↦ ℝ) ↦ negEntropy (ofLp x))
      (∑ c, log (a t c) • PiLp.proj (𝕜 := ℝ) 1 (fun _ : α ↦ ℝ) c) (ofLp ⁻¹' simplex α) (a t) :=
    (hasFDerivAt_negEntropy fun c ↦ (hp_pos t c).ne').hasFDerivWithinAt
  have h := ftrl_regret_succ_le_of_antitone (n := m) strongConvexOn_negEntropy.1 hη hη_anti Y a
    (fun t _ ↦ ha t) _ (fun t _ ↦ hF' t) (u := toLp 1 u) (by simpa using hu)
  -- each stability term is at most `B t`
  have h_stab (t : ℕ) (q : PiLp 1 fun _ : α ↦ ℝ) (hq : ofLp q ∈ simplex α) :
      Y t (a t - q) - bregDiv (fun x : PiLp 1 (fun _ : α ↦ ℝ) ↦ negEntropy (ofLp x)) q (a t)
          (∑ c, log (a t c) • PiLp.proj (𝕜 := ℝ) 1 (fun _ : α ↦ ℝ) c) / η t ≤ B t := by
    rw [bregDiv_negEntropy hq (by simpa [a] using hp_mem t)
      fun c hc ↦ absurd hc (hp_pos t c).ne', hY_apply]
    have h_eq : ∑ b, y t b * (a t - q) b = ∑ b, (p t b - ofLp q b) * y t b :=
      sum_congr rfl fun b _ ↦ by simp [a, mul_comm]
    simp only [a] at h_eq ⊢
    rw [h_eq]
    exact sum_sub_mul_sub_sum_mul_log_div_div_le (hp_mem t) hq
      (fun c hc ↦ absurd hc (hp_pos t c).ne') (y t) (hη t)
  -- the range of the negative entropy on the simplex is at most `log k`
  have h_range : (negEntropy (ofLp (toLp 1 u)) - negEntropy (ofLp (a 0))) / η m ≤
      log (Fintype.card α) / η m := by
    refine div_le_div_of_nonneg_right ?_ (hη m).le
    rw [ofLp_toLp]
    linarith [negEntropy_le_neg_one hu, neg_log_card_sub_one_le_negEntropy (hp_mem 0)]
  have h_sum : ∑ t ∈ range m, (Y t (a t - a (t + 1)) -
      bregDiv (fun x : PiLp 1 (fun _ : α ↦ ℝ) ↦ negEntropy (ofLp x)) (a (t + 1)) (a t)
        (∑ c, log (a t c) • PiLp.proj (𝕜 := ℝ) 1 (fun _ : α ↦ ℝ) c) / η t) ≤
      ∑ t ∈ range m, B t :=
    sum_le_sum fun t _ ↦ h_stab t _ (by simpa [a] using hp_mem (t + 1))
  have h_last := h_stab m (toLp 1 u) (by simpa using hu)
  have h_lhs : ∑ t ∈ range (m + 1), Y t (a t - toLp 1 u) =
      ∑ t ∈ range (m + 1), (∑ b, p t b * y t b - ∑ b, u b * y t b) :=
    sum_congr rfl fun t _ ↦ by
      rw [hY_apply, ← sum_sub_distrib]
      exact sum_congr rfl fun b _ ↦ by simp [a]; ring
  have h_goal : ∑ t ∈ range (m + 1), (∑ b, p t b * y t b - ∑ b, u b * y t b) ≤
      log (Fintype.card α) / η m + ∑ t ∈ range (m + 1), B t := by
    rw [← h_lhs, sum_range_succ B m]
    linarith
  rw [Nat.add_sub_cancel]
  simpa only [hp_def, hB_def] using h_goal

/-- **Regret of exponential weights with nonincreasing learning rates** [Ora, Section 7.5;
BCB12, proof of Theorem 3.1]. For losses `y t` that are nonnegative at the rounds `t < n` and
nonincreasing learning rates `η t > 0`, the weights `p t = softmax (-(η t • ∑ s < t, y s))`
satisfy, against every point `u` of the simplex,
`∑ t < n, (⟨p t, y t⟩ - ⟨u, y t⟩) ≤ log k / η (n - 1) + ∑ t < n, η t / 2 * ⟨p t, (y t) ^ 2⟩`,
with `k` the cardinality of `α` and `⟨p, y⟩ = ∑ b, p b * y b`. The weights are the plays of FTRL
on the simplex with the negative entropy and the rates `η t`. -/
theorem softmax_regret_le_of_antitone {η : ℕ → ℝ} (hη : ∀ t, 0 < η t) (hη_anti : Antitone η)
    {y : ℕ → α → ℝ} {n : ℕ} (hy : ∀ t < n, ∀ b, 0 ≤ y t b) {u : α → ℝ} (hu : u ∈ simplex α) :
    ∑ t ∈ range n, (∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b - ∑ b, u b * y t b) ≤
      log (Fintype.card α) / η (n - 1) +
        ∑ t ∈ range n, η t / 2 * ∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b ^ 2 := by
  refine (softmax_regret_le_sum_exp_of_antitone hη hη_anti y n hu).trans
    (add_le_add le_rfl (sum_le_sum fun t ht ↦ ?_))
  rw [div_le_iff₀ (hη t)]
  calc _ ≤ η t ^ 2 / 2 * ∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b ^ 2 :=
        sum_mul_exp_neg_sub_one_add_le (softmax_nonneg _) (hy t (mem_range.1 ht)) (hη t).le
    _ = _ := by ring

/-- **Regret of exponential weights with nonincreasing learning rates, for losses bounded
below** [LS, proof of Theorem 27.1]. For losses `y t` with
`η t * y t b ≥ -1` at the rounds `t < n` and nonincreasing learning rates `η t > 0`, the weights
`p t = softmax (-(η t • ∑ s < t, y s))` satisfy, against every point `u` of the simplex,
`∑ t < n, (⟨p t, y t⟩ - ⟨u, y t⟩) ≤ log k / η (n - 1) + ∑ t < n, η t * ⟨p t, (y t) ^ 2⟩`,
with `k` the cardinality of `α` and `⟨p, y⟩ = ∑ b, p b * y b`. The losses may be negative, as
the loss estimates of adversarial linear bandits are. -/
theorem softmax_regret_le_of_antitone_of_neg_one_le {η : ℕ → ℝ} (hη : ∀ t, 0 < η t)
    (hη_anti : Antitone η) {y : ℕ → α → ℝ} {n : ℕ} (hy : ∀ t < n, ∀ b, -1 ≤ η t * y t b)
    {u : α → ℝ} (hu : u ∈ simplex α) :
    ∑ t ∈ range n, (∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b - ∑ b, u b * y t b) ≤
      log (Fintype.card α) / η (n - 1) +
        ∑ t ∈ range n, η t * ∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b ^ 2 := by
  refine (softmax_regret_le_sum_exp_of_antitone hη hη_anti y n hu).trans
    (add_le_add le_rfl (sum_le_sum fun t ht ↦ ?_))
  rw [div_le_iff₀ (hη t)]
  calc _ ≤ η t ^ 2 * ∑ b, softmax (-(η t • ∑ s ∈ range t, y s)) b * y t b ^ 2 :=
        sum_mul_exp_neg_sub_one_add_le_of_neg_one_le (softmax_nonneg _) (hy t (mem_range.1 ht))
    _ = _ := by ring

/-- **Regret of exponential weights** with local norms. For losses `y t` that are nonnegative at
the rounds `t < n` and a learning rate `η > 0`, the weights `p t = softmax (-(η • ∑ s < t, y s))`
satisfy, against every coordinate `a`,
`∑ t < n, (⟨p t, y t⟩ - y t a) ≤ log k / η + η / 2 * ∑ t < n, ⟨p t, (y t) ^ 2⟩`,
with `k` the cardinality of `α`. This is the case of a constant learning rate and a vertex of the
simplex in `softmax_regret_le_of_antitone`. -/
theorem softmax_regret_le {η : ℝ} (hη : 0 < η) {y : ℕ → α → ℝ} {n : ℕ}
    (hy : ∀ t < n, ∀ b, 0 ≤ y t b) (a : α) :
    ∑ t ∈ range n, (∑ b, softmax (-(η • ∑ s ∈ range t, y s)) b * y t b - y t a) ≤
      log (Fintype.card α) / η +
        η / 2 * ∑ t ∈ range n, ∑ b, softmax (-(η • ∑ s ∈ range t, y s)) b * y t b ^ 2 := by
  classical
  have h := softmax_regret_le_of_antitone (η := fun _ ↦ η) (fun _ ↦ hη) antitone_const hy
    (single_mem_simplex a)
  simpa [Pi.single_apply, mul_sum] using h

/-- **Regret of exponential weights for losses bounded below** [LS, proof of Theorem 27.1]. For
losses `y t` with `η * y t b ≥ -1` at the rounds `t < n` and a learning rate `η > 0`, the weights
`p t = softmax (-(η • ∑ s < t, y s))` satisfy, against every coordinate `a`,
`∑ t < n, (⟨p t, y t⟩ - y t a) ≤ log k / η + η * ∑ t < n, ⟨p t, (y t) ^ 2⟩`,
with `k` the cardinality of `α`. This is the case of a constant learning rate and a vertex of the
simplex in `softmax_regret_le_of_antitone_of_neg_one_le`. -/
theorem softmax_regret_le_of_neg_one_le {η : ℝ} (hη : 0 < η) {y : ℕ → α → ℝ} {n : ℕ}
    (hy : ∀ t < n, ∀ b, -1 ≤ η * y t b) (a : α) :
    ∑ t ∈ range n, (∑ b, softmax (-(η • ∑ s ∈ range t, y s)) b * y t b - y t a) ≤
      log (Fintype.card α) / η +
        η * ∑ t ∈ range n, ∑ b, softmax (-(η • ∑ s ∈ range t, y s)) b * y t b ^ 2 := by
  classical
  have h := softmax_regret_le_of_antitone_of_neg_one_le (η := fun _ ↦ η) (fun _ ↦ hη)
    antitone_const hy (single_mem_simplex a)
  simpa [Pi.single_apply, mul_sum] using h

end LMLExplore.OnlineLearning
