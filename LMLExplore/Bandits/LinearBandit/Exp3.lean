/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.OptimalDesign
public import LMLExplore.MeasureTheory.Constructions.BorelSpace.RingInverse
public import LMLExplore.MeasureTheory.Function.ConditionalExpectation.FiniteValued
public import LMLExplore.OnlineLearning.Simplex

/-!
# Exp3 with exploration for adversarial linear bandits

In an adversarial linear bandit with finitely many arms, each arm `a` of a finite type `α` has a
feature `φ a` in a finite-dimensional real inner product space `E` of dimension `d`. At round `t`
an adaptive adversary chooses a loss vector `y t ∈ E`, the learner plays an arm `A t` and only
observes the loss `⟪φ (A t), y t⟫` of its arm. Exp3 for linear bandits [LS, Algorithm 15] plays
exponential weights mixed with an exploration distribution `π` on the arms. With learning rate
`η > 0` and exploration rate `γ ∈ (0, 1]`, it draws the arm of round `t` from
`P t = (1 - γ) softmax (-(η • S t)) + γ π`, where `S t = ∑ s < t, Ŷ s` is the sum of the past loss
estimates and `Ŷ s` is the least-squares estimate
`Ŷ s a = ⟪φ a, V(P s)⁻¹ φ (A s)⟫ ⟪φ (A s), y s⟫`, with `V(p) = ∑ b, p b • φ b ⊗ φ b` the design
operator of the weights `p` (the design operator `designOperator (w.map φ)` of the image design,
by `designOperator_map`). The estimate only uses the observed loss.

Given the past, the estimate is unbiased, `∑ c, P c * Ŷ(c) a = ⟪φ a, y⟫`
(`sum_mul_linearExp3Estimate`), and its second moment under the weights is at most
`∑ a, P a ⟪φ a, V(P)⁻¹ φ a⟫ = d` (`sum_mul_linearExp3Estimate_sq_le`,
`sum_mul_inner_ringInverse_sum_smul_rankOne`). The exploration makes `V(P) ≥ γ V(π)` in the
Loewner order, so that for an exploration distribution with invertible `V(π)` and
`⟪φ b, V(π)⁻¹ φ b⟫ ≤ g` for every arm, the estimates are bounded by `g / γ`
(`abs_linearExp3Estimate_le`). For `η g ≤ γ`, the local-norm bound of exponential weights for
losses with `η Ŷ ≥ -1` (`softmax_regret_le_of_neg_one_le`) applies pathwise, and taking
expectations gives [LS, Theorem 27.1]: against every arm `b`,
`E[∑ t < n, (⟪φ (A t), y t⟫ - ⟪φ b, y t⟫)] ≤ log k / η + η d n + 2 γ n`,
with `k` the number of arms. With `γ = η g` and `η = √(log k / ((2 g + d) n))` the regret is at
most `2 √((2 g + d) n log k)`, and with an exploration distribution given by the Kiefer–Wolfowitz
theorem, which has `g = d` when the features span `E`, at most `2 √(3 d n log k)`.

As in `LMLExplore.Bandits.UnitBallFTRL`, the interaction is described round by round relative to
σ-algebras `m t`, the information available before the arm of round `t` is drawn: the loss
vector `y t` is `m t`-measurable (an adaptive adversary), and the arm `A t` has conditional law
`P t` given `m t`. Losses fixed in advance by an oblivious adversary are the constant ones.

## Main definitions

* `linearExp3Estimate φ p c ℓ`: the loss estimate of the arms for the weights `p`, the played arm
  `c` and its observed loss `ℓ`.
* `linearExp3Weights π η γ S`: the weights `(1 - γ) softmax (-(η • S)) + γ π` of the arms for the
  cumulative estimate `S`.
* `linearExp3Sum φ π η γ A ℓ t`: the cumulative estimate after the arms `A s` and the observed
  losses `ℓ s` of the rounds `s < t`.

## Main statements

* `sum_mul_linearExp3Estimate`: the estimate is unbiased.
* `sum_mul_linearExp3Estimate_sq_le`: its second moment is at most `⟪φ a, V(p)⁻¹ φ a⟫`.
* `abs_linearExp3Estimate_le`: the estimates are bounded by `g / γ`.
* `linearExp3_sum_sub_le`: the pathwise local-norm regret bound of the exponential weights on the
  estimated losses.
* `linearExp3_integral_regret_le`: [LS, Theorem 27.1] for arbitrary rates: the expected regret
  against every arm is at most `log k / η + η d n + 2 γ n`.
* `linearExp3_integral_regret_le_two_mul_sqrt`: [LS, Theorem 27.1] with the tuned rates, the
  expected regret is at most `2 √((2 g + d) n log k)`.
* `linearExp3_integral_regret_le_two_mul_sqrt_three`: with an exploration distribution with
  `g = d`, which `LMLExplore.exists_mem_simplex_inner_ringInverse_le_finrank` (the Kiefer–Wolfowitz
  theorem) provides when the features span `E`, the expected regret is at most `2 √(3 d n log k)`.
* `integral_sum_mul_linearExp3Estimate`, `integral_sum_mul_linearExp3Estimate_sq_le`,
  `linearExp3_integral_inner_sub_le`: unbiasedness, second moment and regret of a round, in
  expectation.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapter 27.
-/

public section

open MeasureTheory Finset ContinuousLinearMap InnerProductSpace Module LMLExplore.OnlineLearning
open scoped InnerProductSpace ProbabilityTheory

namespace LMLExplore.Bandits

variable {α E : Type*} [Fintype α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Defs

variable (φ : α → E)

/-- The loss estimate of Exp3 for linear bandits [LS, Chapter 27], for the weights `p` of the arms,
the played arm `c` and its observed loss `ℓ`: the estimate of the loss of arm `a` is
`⟪φ a, V(p)⁻¹ φ c⟫ * ℓ`, with `V(p) = ∑ b, p b • φ b ⊗ φ b` the design operator of the weights.
It is the evaluation at the features of the least-squares estimate `V(p)⁻¹ φ c ℓ` of the loss
vector. -/
noncomputable def linearExp3Estimate (p : α → ℝ) (c : α) (ℓ : ℝ) : α → ℝ :=
  fun a ↦ ⟪φ a, Ring.inverse (∑ b, p b • rankOne ℝ (φ b) (φ b)) (φ c)⟫_ℝ * ℓ

lemma linearExp3Estimate_apply (p : α → ℝ) (c : α) (ℓ : ℝ) (a : α) :
    linearExp3Estimate φ p c ℓ a =
      ⟪φ a, Ring.inverse (∑ b, p b • rankOne ℝ (φ b) (φ b)) (φ c)⟫_ℝ * ℓ := (rfl)

/-- The weights of the arms of Exp3 for linear bandits [LS, Algorithm 15] with exploration
distribution `π`, learning rate `η` and exploration rate `γ`, for the cumulative loss estimate
`S`: the exponential weights `softmax (-(η • S))` mixed with `π`,
`(1 - γ) softmax (-(η • S)) + γ π`. -/
noncomputable def linearExp3Weights (π : α → ℝ) (η γ : ℝ) (S : α → ℝ) : α → ℝ :=
  fun a ↦ (1 - γ) * softmax (-(η • S)) a + γ * π a

lemma linearExp3Weights_apply (π : α → ℝ) (η γ : ℝ) (S : α → ℝ) (a : α) :
    linearExp3Weights π η γ S a = (1 - γ) * softmax (-(η • S)) a + γ * π a := (rfl)

/-- The cumulative loss estimate of Exp3 for linear bandits after the rounds `s < t`, for the
played arms `A s` and their observed losses `ℓ s`: the sum of the estimates
`linearExp3Estimate φ (P s) (A s) (ℓ s)`, where `P s = linearExp3Weights π η γ (S s)` are the
weights of round `s`, computed from the cumulative estimate `S s` of the previous rounds. -/
noncomputable def linearExp3Sum (π : α → ℝ) (η γ : ℝ) (A : ℕ → α) (ℓ : ℕ → ℝ) : ℕ → α → ℝ
  | 0 => 0
  | t + 1 => linearExp3Sum π η γ A ℓ t +
      linearExp3Estimate φ (linearExp3Weights π η γ (linearExp3Sum π η γ A ℓ t)) (A t) (ℓ t)

@[simp]
lemma linearExp3Sum_zero (π : α → ℝ) (η γ : ℝ) (A : ℕ → α) (ℓ : ℕ → ℝ) :
    linearExp3Sum φ π η γ A ℓ 0 = 0 := (rfl)

lemma linearExp3Sum_succ (π : α → ℝ) (η γ : ℝ) (A : ℕ → α) (ℓ : ℕ → ℝ) (t : ℕ) :
    linearExp3Sum φ π η γ A ℓ (t + 1) = linearExp3Sum φ π η γ A ℓ t +
      linearExp3Estimate φ (linearExp3Weights π η γ (linearExp3Sum φ π η γ A ℓ t)) (A t) (ℓ t) :=
  (rfl)

/-- The cumulative estimate is the sum of the estimates of the past rounds. -/
lemma linearExp3Sum_eq_sum (π : α → ℝ) (η γ : ℝ) (A : ℕ → α) (ℓ : ℕ → ℝ) (t : ℕ) :
    linearExp3Sum φ π η γ A ℓ t = ∑ s ∈ range t,
      linearExp3Estimate φ (linearExp3Weights π η γ (linearExp3Sum φ π η γ A ℓ s)) (A s) (ℓ s) := by
  induction t with
  | zero => simp
  | succ t ih => rw [linearExp3Sum_succ, sum_range_succ, ← ih]

end Defs

section Weights

variable {π : α → ℝ} {η γ : ℝ}

/-- For an exploration distribution `π` in the simplex and `0 ≤ γ ≤ 1`, the weights are in the
simplex. -/
lemma linearExp3Weights_mem_simplex [Nonempty α] (hπ : π ∈ simplex α) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (S : α → ℝ) : linearExp3Weights π η γ S ∈ simplex α := by
  refine mem_simplex_iff.2 ⟨fun a ↦ ?_, ?_⟩
  · rw [linearExp3Weights_apply]
    have := softmax_nonneg (-(η • S)) a
    have := (mem_simplex_iff.1 hπ).1 a
    have : 0 ≤ 1 - γ := sub_nonneg.2 hγ1
    positivity
  · simp_rw [linearExp3Weights_apply, sum_add_distrib, ← mul_sum, sum_softmax,
      (mem_simplex_iff.1 hπ).2]
    ring

/-- The weights put mass at least `γ * π a` on each arm `a`, for `γ ≤ 1`. -/
lemma mul_le_linearExp3Weights (hγ1 : γ ≤ 1) (S : α → ℝ) (a : α) :
    γ * π a ≤ linearExp3Weights π η γ S a := by
  rw [linearExp3Weights_apply]
  have := mul_nonneg (sub_nonneg.2 hγ1) (softmax_nonneg (-(η • S)) a)
  linarith

end Weights

section Estimate

variable {φ : α → E} {p π : α → ℝ} {g γ : ℝ}

/-- **The loss estimate is unbiased** [LS, Chapter 27]: if `V(p)` is invertible, then for every
loss vector `y`, `∑ c, p c * Ŷ(c) a = ⟪φ a, y⟫`, where `Ŷ(c)` is the estimate for the played
arm `c` and its observed loss `⟪φ c, y⟫`. -/
theorem sum_mul_linearExp3Estimate (hu : IsUnit (∑ b, p b • rankOne ℝ (φ b) (φ b))) (y : E)
    (a : α) : ∑ c, p c * linearExp3Estimate φ p c ⟪φ c, y⟫_ℝ a = ⟪φ a, y⟫_ℝ := by
  set V := ∑ b, p b • rankOne ℝ (φ b) (φ b)
  have hV : V y = ∑ c, (p c * ⟪φ c, y⟫_ℝ) • φ c := by
    simp [V, sum_apply, rankOne_apply, smul_smul]
  calc ∑ c, p c * linearExp3Estimate φ p c ⟪φ c, y⟫_ℝ a
      = ⟪φ a, Ring.inverse V (∑ c, (p c * ⟪φ c, y⟫_ℝ) • φ c)⟫_ℝ := by
        simp only [linearExp3Estimate_apply, map_sum, map_smul, inner_sum, real_inner_smul_right]
        exact sum_congr rfl fun c _ ↦ by ring
    _ = ⟪φ a, y⟫_ℝ := by rw [← hV, ringInverse_apply_apply hu]

/-- **The second moment of the loss estimate** [LS, Chapter 27]: for nonnegative weights `p` and
a loss vector `y` with `|⟪φ c, y⟫| ≤ 1` for every arm `c`,
`∑ c, p c * Ŷ(c) a ^ 2 ≤ ⟪φ a, V(p)⁻¹ φ a⟫`. -/
theorem sum_mul_linearExp3Estimate_sq_le (hp : ∀ b, 0 ≤ p b) {y : E}
    (hy : ∀ c, |⟪φ c, y⟫_ℝ| ≤ 1) (a : α) :
    ∑ c, p c * linearExp3Estimate φ p c ⟪φ c, y⟫_ℝ a ^ 2 ≤
      ⟪φ a, Ring.inverse (∑ b, p b • rankOne ℝ (φ b) (φ b)) (φ a)⟫_ℝ := by
  set V := ∑ b, p b • rankOne ℝ (φ b) (φ b)
  have hVp : V.IsPositive := isPositive_sum_smul_rankOne φ hp
  set u := Ring.inverse V (φ a)
  -- `∑ c, p c * ⟪φ a, V⁻¹ φ c⟫ ^ 2 = ⟪u, V u⟫` with `u = V⁻¹ φ a`
  have h_quad : ∑ c, p c * ⟪φ a, Ring.inverse V (φ c)⟫_ℝ ^ 2 = ⟪u, V u⟫_ℝ := by
    have hsymm (c : α) : ⟪φ a, Ring.inverse V (φ c)⟫_ℝ = ⟪φ c, u⟫_ℝ := by
      rw [← hVp.ringInverse.inner_left_eq_inner_right, real_inner_comm]
    simp only [hsymm, V, sum_apply, smul_apply, rankOne_apply, inner_sum, real_inner_smul_right]
    exact sum_congr rfl fun c _ ↦ by rw [real_inner_comm u (φ c)]; ring
  have h_le : ⟪u, V u⟫_ℝ ≤ ⟪φ a, u⟫_ℝ := by
    by_cases hu : IsUnit V
    · rw [apply_ringInverse_apply hu, real_inner_comm]
    · simp [u, Ring.inverse_non_unit V hu]
  calc ∑ c, p c * linearExp3Estimate φ p c ⟪φ c, y⟫_ℝ a ^ 2
      ≤ ∑ c, p c * ⟪φ a, Ring.inverse V (φ c)⟫_ℝ ^ 2 := by
        refine sum_le_sum fun c _ ↦ mul_le_mul_of_nonneg_left ?_ (hp c)
        rw [linearExp3Estimate_apply, mul_pow]
        refine mul_le_of_le_one_right (sq_nonneg _) ?_
        rw [← sq_abs]
        exact pow_le_one₀ (abs_nonneg _) (hy c)
    _ ≤ ⟪φ a, u⟫_ℝ := h_quad.trans_le h_le

/-- **The loss estimates are bounded** [LS, proof of Theorem 27.1]. If `V(π)` is invertible with
`⟪φ b, V(π)⁻¹ φ b⟫ ≤ g` for every arm, `γ > 0` and `γ * π b ≤ p b` for every arm, then for an
observed loss `|ℓ| ≤ 1` the estimates satisfy `|Ŷ(c) a| ≤ g / γ`. -/
theorem abs_linearExp3Estimate_le (hπ0 : ∀ b, 0 ≤ π b)
    (hπu : IsUnit (∑ b, π b • rankOne ℝ (φ b) (φ b)))
    (hg : ∀ b, ⟪φ b, Ring.inverse (∑ b, π b • rankOne ℝ (φ b) (φ b)) (φ b)⟫_ℝ ≤ g)
    (hγ : 0 < γ) (hpπ : ∀ b, γ * π b ≤ p b) {ℓ : ℝ} (hℓ : |ℓ| ≤ 1) (c a : α) :
    |linearExp3Estimate φ p c ℓ a| ≤ g / γ := by
  set V := ∑ b, p b • rankOne ℝ (φ b) (φ b)
  have hπp := isPositive_sum_smul_rankOne φ hπ0
  have hVp : V.IsPositive :=
    isPositive_sum_smul_rankOne φ fun b ↦ (mul_nonneg hγ.le (hπ0 b)).trans (hpπ b)
  -- `⟪x, V(p)⁻¹ x⟫ ≤ ⟪x, V(π)⁻¹ x⟫ / γ ≤ g / γ` at the features, since `γ V(π) ≤ V(p)`
  have h_feat (b : α) : ⟪φ b, Ring.inverse V (φ b)⟫_ℝ ≤ g / γ := by
    rw [le_div_iff₀ hγ, mul_comm]
    exact (hπp.mul_inner_ringInverse_le_of_smul_le hπu hγ (smul_sum_smul_rankOne_le hpπ)
      (φ b)).trans (hg b)
  have hgγ : 0 ≤ g / γ := (hVp.ringInverse.inner_nonneg_right (φ a)).trans (h_feat a)
  -- the Cauchy–Schwarz inequality for the positive operator `V(p)⁻¹`
  have h_cs : |⟪φ a, Ring.inverse V (φ c)⟫_ℝ| ≤ g / γ := by
    refine abs_le_of_sq_le_sq ((hVp.ringInverse.sq_inner_apply_le (φ a) (φ c)).trans ?_) hgγ
    rw [sq]
    exact mul_le_mul (h_feat a) (h_feat c) (hVp.ringInverse.inner_nonneg_right _) hgγ
  rw [linearExp3Estimate_apply, abs_mul]
  calc |⟪φ a, Ring.inverse V (φ c)⟫_ℝ| * |ℓ| ≤ g / γ * 1 :=
        mul_le_mul h_cs hℓ (abs_nonneg _) hgγ
    _ = g / γ := mul_one _

end Estimate

section Pathwise

variable {φ : α → E} {π : α → ℝ} {g η γ : ℝ}

/-- **Pathwise regret of the exponential weights of Exp3 for linear bandits**
[LS, proof of Theorem 27.1]. Let `V(π)` be invertible with `⟪φ b, V(π)⁻¹ φ b⟫ ≤ g` for every
arm, and let `η > 0`, `0 < γ ≤ 1` and `η g ≤ γ`. For arms `A s` and observed losses `ℓ s` with
`|ℓ s| ≤ 1` at the rounds `s < n`, with `S t` the cumulative estimate, `Q t = softmax (-(η • S t))`
the exponential weights and `Ŷ t` the estimates of round `t`, against every arm `c`,
`∑ t < n, (⟨Q t, Ŷ t⟩ - Ŷ t c) ≤ log k / η + η ∑ t < n, ⟨Q t, (Ŷ t) ^ 2⟩`. The estimates may be
negative; the condition `η g ≤ γ` makes `η Ŷ t ≥ -1`. -/
theorem linearExp3_sum_sub_le (hπ0 : ∀ b, 0 ≤ π b)
    (hπu : IsUnit (∑ b, π b • rankOne ℝ (φ b) (φ b)))
    (hg : ∀ b, ⟪φ b, Ring.inverse (∑ b, π b • rankOne ℝ (φ b) (φ b)) (φ b)⟫_ℝ ≤ g)
    (hη : 0 < η) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hηγ : η * g ≤ γ) {A : ℕ → α} {ℓ : ℕ → ℝ} {n : ℕ}
    (hℓ : ∀ t < n, |ℓ t| ≤ 1) (c : α) :
    ∑ t ∈ range n,
      (∑ b, softmax (-(η • linearExp3Sum φ π η γ A ℓ t)) b *
          linearExp3Estimate φ (linearExp3Weights π η γ (linearExp3Sum φ π η γ A ℓ t)) (A t)
            (ℓ t) b -
        linearExp3Estimate φ (linearExp3Weights π η γ (linearExp3Sum φ π η γ A ℓ t)) (A t)
          (ℓ t) c) ≤
      Real.log (Fintype.card α) / η + η * ∑ t ∈ range n,
        ∑ b, softmax (-(η • linearExp3Sum φ π η γ A ℓ t)) b *
          linearExp3Estimate φ (linearExp3Weights π η γ (linearExp3Sum φ π η γ A ℓ t)) (A t)
            (ℓ t) b ^ 2 := by
  set Y : ℕ → α → ℝ := fun t ↦
    linearExp3Estimate φ (linearExp3Weights π η γ (linearExp3Sum φ π η γ A ℓ t)) (A t) (ℓ t)
  have hS (t : ℕ) : linearExp3Sum φ π η γ A ℓ t = ∑ s ∈ range t, Y s :=
    linearExp3Sum_eq_sum φ π η γ A ℓ t
  -- `η Ŷ ≥ -η g / γ ≥ -1`
  have hY (t : ℕ) (ht : t < n) (b : α) : -1 ≤ η * Y t b := by
    have h : |Y t b| ≤ g / γ := abs_linearExp3Estimate_le hπ0 hπu hg hγ
      (mul_le_linearExp3Weights (η := η) hγ1 _) (hℓ t ht) (A t) b
    have h1 : η * (g / γ) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one hγ]
      exact hηγ
    have h2 := mul_le_mul_of_nonneg_left (neg_abs_le (Y t b)) hη.le
    nlinarith [mul_le_mul_of_nonneg_left h hη.le]
  have h := softmax_regret_le_of_neg_one_le hη hY c
  simp only [← hS] at h
  exact h

end Pathwise

section Round

variable [FiniteDimensional ℝ E] {φ : α → E} {π : α → ℝ} {g η γ : ℝ}
  {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]
  {X : Ω → α} {S : Ω → α → ℝ} {y : Ω → E}

omit [IsProbabilityMeasure P] in
/-- The weights of a round are `m`-measurable when the played arm has them as conditional law
given `m`. -/
private lemma aestronglyMeasurable_weights
    (hXW : ∀ c, P⟦X ⁻¹' {c} | m⟧ =ᵐ[P] fun ω ↦ linearExp3Weights π η γ (S ω) c) :
    AEStronglyMeasurable[m] (fun ω ↦ linearExp3Weights π η γ (S ω)) P := by
  refine ⟨fun ω c ↦ (P⟦X ⁻¹' {c} | m⟧) ω, ?_, ?_⟩
  · have h : Measurable[m] fun ω c ↦ (P⟦X ⁻¹' {c} | m⟧) ω :=
      @measurable_pi_iff Ω α (fun _ ↦ ℝ) m _ _ |>.2 fun c ↦
        (stronglyMeasurable_condExp (m := m) (μ := P)).measurable
    exact h.stronglyMeasurable
  · filter_upwards [ae_all_iff.2 hXW] with ω hω
    exact funext fun c ↦ (hω c).symm

omit [IsProbabilityMeasure P] in
/-- The estimate of the loss of each arm, for each played arm, is `m`-measurable when the weights
and the loss vector are. -/
private lemma aestronglyMeasurable_linearExp3Estimate {p : Ω → α → ℝ}
    (hp : AEStronglyMeasurable[m] p P) (hy : AEStronglyMeasurable[m] y P) (c a : α) :
    AEStronglyMeasurable[m] (fun ω ↦ linearExp3Estimate φ (p ω) c ⟪φ c, y ω⟫_ℝ a) P := by
  -- `p ↦ ⟪φ a, V(p)⁻¹ φ c⟫` is measurable, as `V` is continuous and `Ring.inverse` measurable
  have hV : Continuous fun q : α → ℝ ↦ ∑ b, q b • rankOne ℝ (φ b) (φ b) := by fun_prop
  set F : (α → ℝ) → ℝ := fun q ↦
    ⟪φ a, Ring.inverse (∑ b, q b • rankOne ℝ (φ b) (φ b)) (φ c)⟫_ℝ with hF_def
  have hF : Measurable F :=
    (continuous_const.inner (continuous_id.clm_apply continuous_const)).measurable.comp
      (measurable_ringInverse.comp hV.measurable)
  obtain ⟨q, hq, hpq⟩ := hp
  have hFp : AEStronglyMeasurable[m] (fun ω ↦ F (p ω)) P :=
    ⟨F ∘ q, (hF.comp hq.measurable).stronglyMeasurable, hpq.fun_comp F⟩
  exact hFp.mul ((continuous_const.inner continuous_id).comp_aestronglyMeasurable hy)

variable (hπ : π ∈ simplex α) (hπu : IsUnit (∑ b, π b • rankOne ℝ (φ b) (φ b)))
  (hg : ∀ b, ⟪φ b, Ring.inverse (∑ b, π b • rankOne ℝ (φ b) (φ b)) (φ b)⟫_ℝ ≤ g)
  (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hm : m ≤ mΩ) (hX : ∀ c, MeasurableSet (X ⁻¹' {c}))
  (hXW : ∀ c, P⟦X ⁻¹' {c} | m⟧ =ᵐ[P] fun ω ↦ linearExp3Weights π η γ (S ω) c)
  (hy : AEStronglyMeasurable[m] y P) (hy1 : ∀ᵐ ω ∂P, ∀ c, |⟪φ c, y ω⟫_ℝ| ≤ 1)

include hπ hπu hg hγ hγ1 hy1 in
omit [FiniteDimensional ℝ E] [IsProbabilityMeasure P] in
/-- The estimates of a round are almost surely bounded by `g / γ`, for every played arm. -/
private lemma ae_abs_linearExp3Estimate_le : ∀ᵐ ω ∂P, ∀ c b,
    |linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) c ⟪φ c, y ω⟫_ℝ b| ≤ g / γ := by
  filter_upwards [hy1] with ω hω c b
  exact abs_linearExp3Estimate_le (mem_simplex_iff.1 hπ).1 hπu hg hγ
    (mul_le_linearExp3Weights hγ1 _) (hω c) c b

include hπ hπu hg hγ hγ1 hm hXW hy hy1 in
omit [IsProbabilityMeasure P] in
/-- For an `m`-measurable weight `r` bounded by `C`, the weighted power `r * Ŷ(c) b ^ k` of the
estimate of the loss of arm `b`, for the played arm `c`, is `m`-measurable and integrable. -/
private lemma integrable_mul_linearExp3Estimate_pow [IsFiniteMeasure P] {r : Ω → ℝ}
    (hr : AEStronglyMeasurable[m] r P) {C : ℝ} (hrC : ∀ ω, |r ω| ≤ C) (k : ℕ) (c b : α) :
    AEStronglyMeasurable[m] (fun ω ↦
        r ω * linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) c ⟪φ c, y ω⟫_ℝ b ^ k) P ∧
      Integrable (fun ω ↦
        r ω * linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) c ⟪φ c, y ω⟫_ℝ b ^ k) P := by
  have hmeas := hr.mul ((aestronglyMeasurable_linearExp3Estimate (φ := φ)
    (aestronglyMeasurable_weights hXW) hy c b).pow k)
  refine ⟨hmeas, .of_bound (hmeas.mono hm) (C * (g / γ) ^ k) ?_⟩
  filter_upwards [ae_abs_linearExp3Estimate_le hπ hπu hg hγ hγ1 hy1] with ω hω
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul (hrC ω) (pow_le_pow_left₀ (abs_nonneg _) (hω c b) k) (by positivity)
    ((abs_nonneg _).trans (hrC ω))

include hπ hπu hg hγ hγ1 hm hX hXW hy hy1 in
omit [IsProbabilityMeasure P] in
/-- For an `m`-measurable weight `r` bounded by `C`, the weighted power `r * Ŷ b ^ k` of the
estimate for the arm `X` played in the round is integrable. -/
private lemma integrable_mul_linearExp3Estimate_apply_pow [IsFiniteMeasure P] {r : Ω → ℝ}
    (hr : AEStronglyMeasurable[m] r P) {C : ℝ} (hrC : ∀ ω, |r ω| ≤ C) (k : ℕ) (b : α) :
    Integrable (fun ω ↦ r ω *
      linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ b ^ k) P :=
  integrable_apply_of_measurableSet_preimage (g := fun ω c ↦ r ω *
    linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) c ⟪φ c, y ω⟫_ℝ b ^ k) hX
    fun c ↦ (integrable_mul_linearExp3Estimate_pow hπ hπu hg hγ hγ1 hm hXW hy hy1 hr hrC k c b).2

include hπ hγ hγ1 in
omit [FiniteDimensional ℝ E] in
/-- The weights are bounded by `1`. -/
private lemma abs_linearExp3Weights_le_one (ω : Ω) (b : α) :
    |linearExp3Weights π η γ (S ω) b| ≤ 1 := by
  have := nonempty_of_mem_simplex hπ
  have h := linearExp3Weights_mem_simplex (η := η) hπ hγ.le hγ1 (S ω)
  rw [abs_of_nonneg ((mem_simplex_iff.1 h).1 b)]
  exact (simplex_subset_Icc h).2 b

omit [IsProbabilityMeasure P] in
/-- The weights of a round are `m`-measurable, coordinatewise. -/
private lemma aestronglyMeasurable_linearExp3Weights_apply
    (hXW : ∀ c, P⟦X ⁻¹' {c} | m⟧ =ᵐ[P] fun ω ↦ linearExp3Weights π η γ (S ω) c) (b : α) :
    AEStronglyMeasurable[m] (fun ω ↦ linearExp3Weights π η γ (S ω) b) P :=
  (continuous_apply b).comp_aestronglyMeasurable (aestronglyMeasurable_weights hXW)

include hπ hπu hg hγ hγ1 hm hX hXW hy hy1 in
/-- **Unbiasedness of the estimates in expectation** [LS, Chapter 27]. In a round in which the
arm `X` has conditional law `P = linearExp3Weights π η γ S` given `m` and the loss vector `y` is
`m`-measurable, for `m`-measurable bounded weights `r`,
`E[∑ b, r b * Ŷ b] = E[∑ b, r b * ⟪φ b, y⟫]`, where `Ŷ` is the estimate for the played arm `X`
and its observed loss `⟪φ X, y⟫`. -/
theorem integral_sum_mul_linearExp3Estimate {r : Ω → α → ℝ}
    (hr : ∀ b, AEStronglyMeasurable[m] (fun ω ↦ r ω b) P) {C : ℝ} (hrC : ∀ ω b, |r ω b| ≤ C) :
    ∫ ω, ∑ b, r ω b *
        linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ b ∂P =
      ∫ ω, ∑ b, r ω b * ⟪φ b, y ω⟫_ℝ ∂P := by
  have h_int (b c : α) := integrable_mul_linearExp3Estimate_pow hπ hπu hg hγ hγ1 hm hXW hy hy1
    (hr b) (fun ω ↦ hrC ω b) 1 c b
  simp only [pow_one] at h_int
  have h_int_X (b : α) := integrable_mul_linearExp3Estimate_apply_pow hπ hπu hg hγ hγ1 hm hX hXW
    hy hy1 (hr b) (fun ω ↦ hrC ω b) 1 b
  simp only [pow_one] at h_int_X
  have h_int_y (b : α) : Integrable (fun ω ↦ r ω b * ⟪φ b, y ω⟫_ℝ) P := by
    refine .of_bound (((hr b).mul ((continuous_const.inner continuous_id).comp_aestronglyMeasurable
      hy)).mono hm) (C * 1) ?_
    filter_upwards [hy1] with ω hω
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hrC ω b) (hω b) (abs_nonneg _) ((abs_nonneg _).trans (hrC ω b))
  -- each term `r b * Ŷ b` has the mean of its average over the played arm, `r b * ⟪φ b, y⟫`
  have h_term (b : α) : ∫ ω, r ω b *
      linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ b ∂P =
      ∫ ω, r ω b * ⟪φ b, y ω⟫_ℝ ∂P := by
    rw [integral_apply_eq_integral_sum_smul (g := fun ω c ↦ r ω b *
      linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) c ⟪φ c, y ω⟫_ℝ b) hm hX hXW
      (fun c ↦ (h_int b c).1) (fun c ↦ (h_int b c).2)]
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    have hu := isUnit_sum_smul_rankOne_of_mul_le (mem_simplex_iff.1 hπ).1 hπu hγ
      (mul_le_linearExp3Weights (η := η) (S := S ω) hγ1)
    dsimp only
    rw [← sum_mul_linearExp3Estimate hu (y ω) b, mul_sum]
    exact sum_congr rfl fun c _ ↦ by rw [smul_eq_mul]; ring
  rw [integral_finsetSum _ fun b _ ↦ h_int_X b, integral_finsetSum _ fun b _ ↦ h_int_y b]
  exact sum_congr rfl fun b _ ↦ h_term b

include hπ hπu hg hγ hγ1 hm hX hXW hy hy1 in
/-- **The expected second moment of the estimates** [LS, proof of Theorem 27.1]. In a round as
in `integral_sum_mul_linearExp3Estimate`, on a space of dimension `d`,
`E[∑ b, P b * Ŷ b ^ 2] ≤ d`, where `P = linearExp3Weights π η γ S` are the weights of the round. -/
theorem integral_sum_mul_linearExp3Estimate_sq_le :
    ∫ ω, ∑ b, linearExp3Weights π η γ (S ω) b *
        linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ b ^ 2 ∂P ≤
      finrank ℝ E := by
  have hWb := aestronglyMeasurable_linearExp3Weights_apply hXW
  have hW1 := abs_linearExp3Weights_le_one hπ hγ hγ1 (η := η) (S := S)
  have h_int (b c : α) := integrable_mul_linearExp3Estimate_pow hπ hπu hg hγ hγ1 hm hXW hy hy1
    (hWb b) (fun ω ↦ hW1 ω b) 2 c b
  have h_int_X (b : α) := integrable_mul_linearExp3Estimate_apply_pow hπ hπu hg hγ hγ1 hm hX hXW
    hy hy1 (hWb b) (fun ω ↦ hW1 ω b) 2 b
  -- the averages over the played arm
  set avg : α → Ω → ℝ := fun b ω ↦ ∑ c, linearExp3Weights π η γ (S ω) c •
    (linearExp3Weights π η γ (S ω) b *
      linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) c ⟪φ c, y ω⟫_ℝ b ^ 2) with havg
  have h_avg_int (b : α) : Integrable (avg b) P := by
    refine integrable_finsetSum _ fun c _ ↦ ?_
    simp only [smul_eq_mul]
    exact (h_int b c).2.bdd_mul ((hWb c).mono hm) (ae_of_all _ fun ω ↦ hW1 ω c)
  have h_term (b : α) : ∫ ω, linearExp3Weights π η γ (S ω) b *
      linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ b ^ 2 ∂P =
      ∫ ω, avg b ω ∂P :=
    integral_apply_eq_integral_sum_smul (g := fun ω c ↦ linearExp3Weights π η γ (S ω) b *
      linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) c ⟪φ c, y ω⟫_ℝ b ^ 2) hm hX hXW
      (fun c ↦ (h_int b c).1) (fun c ↦ (h_int b c).2)
  -- pointwise, `∑ b, avg b ≤ ∑ b, P b ⟪φ b, V(P)⁻¹ φ b⟫ = d`
  have h_le : ∀ᵐ ω ∂P, ∑ b, avg b ω ≤ finrank ℝ E := by
    filter_upwards [hy1] with ω hω
    have := nonempty_of_mem_simplex hπ
    have hu := isUnit_sum_smul_rankOne_of_mul_le (mem_simplex_iff.1 hπ).1 hπu hγ
      (mul_le_linearExp3Weights (η := η) (S := S ω) hγ1)
    set p := linearExp3Weights π η γ (S ω)
    have hp0 : ∀ b, 0 ≤ p b :=
      (mem_simplex_iff.1 (linearExp3Weights_mem_simplex hπ hγ.le hγ1 (S ω))).1
    calc ∑ b, avg b ω = ∑ b, p b * ∑ c, p c * linearExp3Estimate φ p c ⟪φ c, y ω⟫_ℝ b ^ 2 := by
          simp only [havg, smul_eq_mul, mul_sum]
          exact sum_congr rfl fun b _ ↦ sum_congr rfl fun c _ ↦ by ring
      _ ≤ ∑ b, p b * ⟪φ b, Ring.inverse (∑ b, p b • rankOne ℝ (φ b) (φ b)) (φ b)⟫_ℝ :=
          sum_le_sum fun b _ ↦ mul_le_mul_of_nonneg_left
            (sum_mul_linearExp3Estimate_sq_le hp0 hω b) (hp0 b)
      _ = finrank ℝ E := sum_mul_inner_ringInverse_sum_smul_rankOne hu
  rw [integral_finsetSum _ fun b _ ↦ h_int_X b]
  simp_rw [h_term]
  rw [← integral_finsetSum _ fun b _ ↦ h_avg_int b]
  calc ∫ ω, ∑ b, avg b ω ∂P ≤ ∫ _ω, (finrank ℝ E : ℝ) ∂P :=
        integral_mono_ae (integrable_finsetSum _ fun b _ ↦ h_avg_int b) (integrable_const _) h_le
    _ = finrank ℝ E := by simp

include hπ hπu hg hγ hγ1 hm hX hXW hy hy1 in
/-- **The expected regret of a round** [LS, proof of Theorem 27.1]. In a round as in
`integral_sum_mul_linearExp3Estimate`, against every arm `b`, the expected regret
`E[⟪φ X, y⟫ - ⟪φ b, y⟫]` is at most the expected regret of the exponential weights
`Q = softmax (-(η • S))` on the estimated losses, scaled by `1 - γ`, plus the cost `2 γ` of the
exploration: `E[(1 - γ) (⟨Q, Ŷ⟩ - Ŷ b)] + 2 γ`. Both sides are integrable. -/
theorem linearExp3_integral_inner_sub_le (b : α) :
    Integrable (fun ω ↦ (1 - γ) * (∑ c, softmax (-(η • S ω)) c *
      linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ c -
        linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ b)) P ∧
    ∫ ω, (⟪φ (X ω), y ω⟫_ℝ - ⟪φ b, y ω⟫_ℝ) ∂P ≤
      ∫ ω, (1 - γ) * (∑ c, softmax (-(η • S ω)) c *
        linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ c -
          linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ b) ∂P +
        2 * γ := by
  classical
  have := nonempty_of_mem_simplex hπ
  have hπ0 := (mem_simplex_iff.1 hπ).1
  have hWb := aestronglyMeasurable_linearExp3Weights_apply hXW
  have hW1 := abs_linearExp3Weights_le_one hπ hγ hγ1 (η := η) (S := S)
  -- the weights `r = (1 - γ) (Q - δ_b) = P - γ π - (1 - γ) δ_b` are `m`-measurable and bounded
  set r : Ω → α → ℝ := fun ω c ↦
    linearExp3Weights π η γ (S ω) c - γ * π c - (1 - γ) * if c = b then 1 else 0 with hr_def
  have hr (c : α) : AEStronglyMeasurable[m] (fun ω ↦ r ω c) P :=
    ((hWb c).sub aestronglyMeasurable_const).sub aestronglyMeasurable_const
  have hπ1 (c : α) : π c ≤ 1 := (simplex_subset_Icc hπ).2 c
  have hrC (ω : Ω) (c : α) : |r ω c| ≤ 3 := by
    have h1 := abs_le.1 (hW1 ω c)
    have h2 : 0 ≤ γ * π c := mul_nonneg hγ.le (hπ0 c)
    have h3 : γ * π c ≤ 1 := by nlinarith [hπ0 c, hπ1 c]
    have h4 : 0 ≤ (1 - γ) * (if c = b then (1 : ℝ) else 0) :=
      mul_nonneg (sub_nonneg.2 hγ1) (by split_ifs <;> norm_num)
    have h5 : (1 - γ) * (if c = b then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> linarith
    rw [abs_le]
    constructor <;> linarith
  have h_eq (ω : Ω) : (1 - γ) * (∑ c, softmax (-(η • S ω)) c *
      linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ c -
        linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ b) =
      ∑ c, r ω c *
        linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ c := by
    have hr_eq (c : α) :
        r ω c = (1 - γ) * (softmax (-(η • S ω)) c - if c = b then 1 else 0) := by
      simp only [hr_def, linearExp3Weights_apply]
      ring
    simp_rw [hr_eq, mul_assoc, ← mul_sum, sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul,
      sum_ite_eq', mem_univ, ite_true]
  have h_int_r : Integrable (fun ω ↦ ∑ c, r ω c *
      linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ c) P :=
    integrable_finsetSum _ fun c _ ↦ by
      simpa using integrable_mul_linearExp3Estimate_apply_pow hπ hπu hg hγ hγ1 hm hX hXW hy hy1
        (hr c) (fun ω ↦ hrC ω c) 1 c
  refine ⟨by simpa only [h_eq] using h_int_r, ?_⟩
  -- the expected regret of the played arm is the expectation of its average under the weights
  have hℓ (c : α) : AEStronglyMeasurable[m] (fun ω ↦ ⟪φ c, y ω⟫_ℝ) P :=
    (continuous_const.inner continuous_id).comp_aestronglyMeasurable hy
  have hℓb (c : α) : Integrable (fun ω ↦ ⟪φ c, y ω⟫_ℝ - ⟪φ b, y ω⟫_ℝ) P := by
    refine .of_bound (((hℓ c).sub (hℓ b)).mono hm) 2 ?_
    filter_upwards [hy1] with ω hω
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith [hω c, hω b])
  rw [integral_apply_eq_integral_sum_smul (g := fun ω c ↦ ⟪φ c, y ω⟫_ℝ - ⟪φ b, y ω⟫_ℝ) hm hX hXW
    (fun c ↦ (hℓ c).sub (hℓ b)) hℓb]
  simp_rw [h_eq]
  rw [integral_sum_mul_linearExp3Estimate hπ hπu hg hγ hγ1 hm hX hXW hy hy1 hr hrC]
  have h_int_rℓ : Integrable (fun ω ↦ ∑ c, r ω c * ⟪φ c, y ω⟫_ℝ) P := by
    refine integrable_finsetSum _ fun c _ ↦ .of_bound (((hr c).mul (hℓ c)).mono hm) (3 * 1) ?_
    filter_upwards [hy1] with ω hω
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hrC ω c) (hω c) (abs_nonneg _) (by norm_num)
  have hW_sum (ω : Ω) : ∑ c, linearExp3Weights π η γ (S ω) c = 1 :=
    (mem_simplex_iff.1 (linearExp3Weights_mem_simplex hπ hγ.le hγ1 (S ω))).2
  calc ∫ ω, ∑ c, linearExp3Weights π η γ (S ω) c • (⟪φ c, y ω⟫_ℝ - ⟪φ b, y ω⟫_ℝ) ∂P
      ≤ ∫ ω, (∑ c, r ω c * ⟪φ c, y ω⟫_ℝ + 2 * γ) ∂P := by
        refine integral_mono_ae (integrable_finsetSum _ fun c _ ↦ ?_)
          (h_int_rℓ.add (integrable_const _)) ?_
        · exact (hℓb c).bdd_mul ((hWb c).mono hm) (ae_of_all _ fun ω ↦ hW1 ω c)
        -- pointwise, the difference is `γ (⟨π, ℓ⟩ - ℓ b) ≤ 2 γ`
        filter_upwards [hy1] with ω hω
        have hπℓ : ∑ c, π c * ⟪φ c, y ω⟫_ℝ ≤ 1 :=
          (sum_le_sum fun c _ ↦ mul_le_of_le_one_right (hπ0 c) (le_of_abs_le (hω c))).trans_eq
            (mem_simplex_iff.1 hπ).2
        have h1 : ∑ c, linearExp3Weights π η γ (S ω) c • (⟪φ c, y ω⟫_ℝ - ⟪φ b, y ω⟫_ℝ) =
            ∑ c, linearExp3Weights π η γ (S ω) c * ⟪φ c, y ω⟫_ℝ - ⟪φ b, y ω⟫_ℝ := by
          simp_rw [smul_eq_mul, mul_sub, sum_sub_distrib, ← sum_mul, hW_sum, one_mul]
        have h2 : ∑ c, r ω c * ⟪φ c, y ω⟫_ℝ =
            ∑ c, linearExp3Weights π η γ (S ω) c * ⟪φ c, y ω⟫_ℝ -
              γ * ∑ c, π c * ⟪φ c, y ω⟫_ℝ - (1 - γ) * ⟪φ b, y ω⟫_ℝ := by
          simp_rw [hr_def, sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum, ite_mul, one_mul,
            zero_mul, sum_ite_eq', mem_univ, ite_true]
        rw [h1, h2]
        nlinarith [(abs_le.1 (hω b)).1]
    _ = ∫ ω, ∑ c, r ω c * ⟪φ c, y ω⟫_ℝ ∂P + 2 * γ := by
        rw [integral_add h_int_rℓ (integrable_const _)]
        simp

include hπ hπu hg hγ hγ1 hm hX hXW hy hy1 in
/-- In a round as in `integral_sum_mul_linearExp3Estimate`, the second moment of the estimates
under the exponential weights `Q = softmax (-(η • S))`, scaled by `1 - γ`, is integrable with
expectation at most `d`: `(1 - γ) Q ≤ P`. -/
private lemma integral_one_sub_mul_sum_softmax_mul_linearExp3Estimate_sq_le :
    Integrable (fun ω ↦ (1 - γ) * ∑ c, softmax (-(η • S ω)) c *
      linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ c ^ 2) P ∧
    ∫ ω, (1 - γ) * ∑ c, softmax (-(η • S ω)) c *
      linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ c ^ 2 ∂P ≤
      finrank ℝ E := by
  have hπ0 := (mem_simplex_iff.1 hπ).1
  have hWb := aestronglyMeasurable_linearExp3Weights_apply hXW
  have hW1 := abs_linearExp3Weights_le_one hπ hγ hγ1 (η := η) (S := S)
  -- `(1 - γ) Q c = P c - γ π c`
  have h_eq (ω : Ω) : (1 - γ) * ∑ c, softmax (-(η • S ω)) c *
      linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ c ^ 2 =
      ∑ c, (linearExp3Weights π η γ (S ω) c - γ * π c) *
        linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ c ^ 2 := by
    rw [mul_sum]
    exact sum_congr rfl fun c _ ↦ by rw [linearExp3Weights_apply]; ring
  have hπ1 (c : α) : π c ≤ 1 := (simplex_subset_Icc hπ).2 c
  have hrC (ω : Ω) (c : α) : |linearExp3Weights π η γ (S ω) c - γ * π c| ≤ 2 := by
    have h1 := abs_le.1 (hW1 ω c)
    have h2 : 0 ≤ γ * π c := mul_nonneg hγ.le (hπ0 c)
    have h3 : γ * π c ≤ 1 := by nlinarith [hπ0 c, hπ1 c]
    rw [abs_le]
    constructor <;> linarith
  have h_int : Integrable (fun ω ↦ ∑ c, (linearExp3Weights π η γ (S ω) c - γ * π c) *
      linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ c ^ 2) P :=
    integrable_finsetSum _ fun c _ ↦ integrable_mul_linearExp3Estimate_apply_pow hπ hπu hg hγ
      hγ1 hm hX hXW hy hy1 ((hWb c).sub aestronglyMeasurable_const) (fun ω ↦ hrC ω c) 2 c
  have h_int_W : Integrable (fun ω ↦ ∑ c, linearExp3Weights π η γ (S ω) c *
      linearExp3Estimate φ (linearExp3Weights π η γ (S ω)) (X ω) ⟪φ (X ω), y ω⟫_ℝ c ^ 2) P :=
    integrable_finsetSum _ fun c _ ↦ integrable_mul_linearExp3Estimate_apply_pow hπ hπu hg hγ
      hγ1 hm hX hXW hy hy1 (hWb c) (fun ω ↦ hW1 ω c) 2 c
  simp_rw [h_eq]
  refine ⟨h_int, (integral_mono h_int h_int_W fun ω ↦ sum_le_sum fun c _ ↦ ?_).trans
    (integral_sum_mul_linearExp3Estimate_sq_le hπ hπu hg hγ hγ1 hm hX hXW hy hy1)⟩
  exact mul_le_mul_of_nonneg_right (sub_le_self _ (mul_nonneg hγ.le (hπ0 c))) (sq_nonneg _)

end Round

section Regret

variable [FiniteDimensional ℝ E] {φ : α → E} {π : α → ℝ} {g η γ : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {m : ℕ → MeasurableSpace Ω} {A : ℕ → Ω → α} {y : ℕ → Ω → E} {n : ℕ}

/-- **Regret of Exp3 for adversarial linear bandits** [LS, Theorem 27.1], for arbitrary rates.
Let `π` be an exploration distribution on the arms with invertible design operator
`V(π) = ∑ b, π b • φ b ⊗ φ b` and `⟪φ b, V(π)⁻¹ φ b⟫ ≤ g` for every arm `b`, and let `η > 0` and
`0 < γ ≤ 1` with `η g ≤ γ`. For each round `t < n`, let the loss vector `y t`, with
`|⟪φ c, y t⟫| ≤ 1` for every arm `c`, be `m t`-measurable, and let the arm `A t` have conditional
law given `m t` the weights `linearExp3Weights π η γ (S t)` of Exp3 for linear bandits, where
`S t` is the cumulative estimate computed from the past arms and their observed losses
`⟪φ (A s), y s⟫`. Then against every arm `b`, on a space of dimension `d` and with `k` arms,
`E[∑ t < n, (⟪φ (A t), y t⟫ - ⟪φ b, y t⟫)] ≤ log k / η + η d n + 2 γ n`. -/
theorem linearExp3_integral_regret_le (hπ : π ∈ simplex α)
    (hπu : IsUnit (∑ b, π b • rankOne ℝ (φ b) (φ b)))
    (hg : ∀ b, ⟪φ b, Ring.inverse (∑ b, π b • rankOne ℝ (φ b) (φ b)) (φ b)⟫_ℝ ≤ g)
    (hη : 0 < η) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hηγ : η * g ≤ γ)
    (hm : ∀ t < n, m t ≤ mΩ) (hA : ∀ t < n, ∀ c, MeasurableSet (A t ⁻¹' {c}))
    (hAW : ∀ t < n, ∀ c, P⟦A t ⁻¹' {c} | m t⟧ =ᵐ[P] fun ω ↦ linearExp3Weights π η γ
      (linearExp3Sum φ π η γ (A · ω) (fun s ↦ ⟪φ (A s ω), y s ω⟫_ℝ) t) c)
    (hy : ∀ t < n, AEStronglyMeasurable[m t] (y t) P)
    (hy1 : ∀ t < n, ∀ᵐ ω ∂P, ∀ c, |⟪φ c, y t ω⟫_ℝ| ≤ 1) (b : α) :
    ∫ ω, ∑ t ∈ range n, (⟪φ (A t ω), y t ω⟫_ℝ - ⟪φ b, y t ω⟫_ℝ) ∂P ≤
      Real.log (Fintype.card α) / η + η * finrank ℝ E * n + 2 * γ * n := by
  have hπ0 := (mem_simplex_iff.1 hπ).1
  set S : ℕ → Ω → α → ℝ := fun t ω ↦
    linearExp3Sum φ π η γ (A · ω) (fun s ↦ ⟪φ (A s ω), y s ω⟫_ℝ) t
  set Y : ℕ → Ω → α → ℝ := fun t ω ↦
    linearExp3Estimate φ (linearExp3Weights π η γ (S t ω)) (A t ω) ⟪φ (A t ω), y t ω⟫_ℝ
  set Q : ℕ → Ω → α → ℝ := fun t ω ↦ softmax (-(η • S t ω))
  -- the regret of each round and the second moments of its estimates
  have h_round (t : ℕ) (ht : t < n) := linearExp3_integral_inner_sub_le (S := S t) hπ hπu hg hγ
    hγ1 (hm t ht) (hA t ht) (hAW t ht) (hy t ht) (hy1 t ht) b
  have h_sq (t : ℕ) (ht : t < n) :=
    integral_one_sub_mul_sum_softmax_mul_linearExp3Estimate_sq_le (S := S t) hπ hπu hg hγ hγ1
      (hm t ht) (hA t ht) (hAW t ht) (hy t ht) (hy1 t ht)
  have h_int_ℓ (t : ℕ) (ht : t < n) :
      Integrable (fun ω ↦ ⟪φ (A t ω), y t ω⟫_ℝ - ⟪φ b, y t ω⟫_ℝ) P := by
    have hℓ (c : α) : AEStronglyMeasurable (fun ω ↦ ⟪φ c, y t ω⟫_ℝ) P :=
      ((continuous_const.inner continuous_id).comp_aestronglyMeasurable (hy t ht)).mono (hm t ht)
    refine integrable_apply_of_measurableSet_preimage (g := fun ω c ↦
      ⟪φ c, y t ω⟫_ℝ - ⟪φ b, y t ω⟫_ℝ) (hA t ht) fun c ↦ .of_bound ((hℓ c).sub (hℓ b)) 2 ?_
    filter_upwards [hy1 t ht] with ω hω
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith [hω c, hω b])
  -- the pathwise bound of the exponential weights on the estimated losses
  have h_path : ∀ᵐ ω ∂P, ∑ t ∈ range n, (1 - γ) * (∑ c, Q t ω c * Y t ω c - Y t ω b) ≤
      (1 - γ) * (Real.log (Fintype.card α) / η) +
        η * ∑ t ∈ range n, (1 - γ) * ∑ c, Q t ω c * Y t ω c ^ 2 := by
    have hy1' : ∀ᵐ ω ∂P, ∀ t < n, ∀ c, |⟪φ c, y t ω⟫_ℝ| ≤ 1 :=
      ae_all_iff.2 fun t ↦ if ht : t < n then (hy1 t ht).mono fun _ h _ ↦ h
        else ae_of_all _ fun _ h ↦ absurd h ht
    filter_upwards [hy1'] with ω hω
    have h := linearExp3_sum_sub_le hπ0 hπu hg hη hγ hγ1 hηγ (A := (A · ω))
      (ℓ := fun s ↦ ⟪φ (A s ω), y s ω⟫_ℝ) (n := n) (fun t ht ↦ hω t ht (A t ω)) b
    rw [← mul_sum, ← mul_sum, mul_left_comm η]
    have h1γ : 0 ≤ 1 - γ := sub_nonneg.2 hγ1
    calc (1 - γ) * ∑ t ∈ range n, (∑ c, Q t ω c * Y t ω c - Y t ω b)
        ≤ (1 - γ) * (Real.log (Fintype.card α) / η +
            η * ∑ t ∈ range n, ∑ c, Q t ω c * Y t ω c ^ 2) :=
          mul_le_mul_of_nonneg_left h h1γ
      _ = _ := by ring
  have h_int_sq_t (t : ℕ) (ht : t < n) :
      Integrable (fun ω ↦ (1 - γ) * ∑ c, Q t ω c * Y t ω c ^ 2) P := (h_sq t ht).1
  have h_int_reg_t (t : ℕ) (ht : t < n) :
      Integrable (fun ω ↦ (1 - γ) * (∑ c, Q t ω c * Y t ω c - Y t ω b)) P := (h_round t ht).1
  have h_int_sq : Integrable (fun ω ↦ ∑ t ∈ range n,
      (1 - γ) * ∑ c, Q t ω c * Y t ω c ^ 2) P :=
    integrable_finsetSum _ fun t ht ↦ h_int_sq_t t (mem_range.1 ht)
  have h_int_bd : Integrable (fun ω ↦ (1 - γ) * (Real.log (Fintype.card α) / η) +
      η * ∑ t ∈ range n, (1 - γ) * ∑ c, Q t ω c * Y t ω c ^ 2) P :=
    (integrable_const _).add (h_int_sq.const_mul η)
  have h_log : 0 ≤ Real.log (Fintype.card α) / η := div_nonneg (Real.log_natCast_nonneg _) hη.le
  calc ∫ ω, ∑ t ∈ range n, (⟪φ (A t ω), y t ω⟫_ℝ - ⟪φ b, y t ω⟫_ℝ) ∂P
      = ∑ t ∈ range n, ∫ ω, (⟪φ (A t ω), y t ω⟫_ℝ - ⟪φ b, y t ω⟫_ℝ) ∂P :=
        integral_finsetSum _ fun t ht ↦ h_int_ℓ t (mem_range.1 ht)
    _ ≤ ∑ t ∈ range n,
          (∫ ω, (1 - γ) * (∑ c, Q t ω c * Y t ω c - Y t ω b) ∂P + 2 * γ) :=
        sum_le_sum fun t ht ↦ (h_round t (mem_range.1 ht)).2
    _ = ∫ ω, ∑ t ∈ range n, (1 - γ) * (∑ c, Q t ω c * Y t ω c - Y t ω b) ∂P + 2 * γ * n := by
        rw [sum_add_distrib, ← integral_finsetSum _ fun t ht ↦ h_int_reg_t t (mem_range.1 ht),
          sum_const, card_range, nsmul_eq_mul]
        ring
    _ ≤ ∫ ω, ((1 - γ) * (Real.log (Fintype.card α) / η) +
          η * ∑ t ∈ range n, (1 - γ) * ∑ c, Q t ω c * Y t ω c ^ 2) ∂P + 2 * γ * n :=
        add_le_add_left (integral_mono_ae (integrable_finsetSum _ fun t ht ↦
          h_int_reg_t t (mem_range.1 ht)) h_int_bd h_path) _
    _ = (1 - γ) * (Real.log (Fintype.card α) / η) + η * ∑ t ∈ range n,
          ∫ ω, (1 - γ) * ∑ c, Q t ω c * Y t ω c ^ 2 ∂P + 2 * γ * n := by
        rw [integral_add (integrable_const _) (h_int_sq.const_mul η), integral_const_mul η,
          integral_finsetSum _ fun t ht ↦ h_int_sq_t t (mem_range.1 ht)]
        simp
    _ ≤ 1 * (Real.log (Fintype.card α) / η) + η * ∑ _t ∈ range n, (finrank ℝ E : ℝ) +
          2 * γ * n := by
        gcongr ?_ + η * ?_ + _
        · nlinarith
        · exact sum_le_sum fun t ht ↦ (h_sq t (mem_range.1 ht)).2
    _ = Real.log (Fintype.card α) / η + η * finrank ℝ E * n + 2 * γ * n := by
        rw [sum_const, card_range, nsmul_eq_mul]
        ring

/-- **Regret of Exp3 for adversarial linear bandits with tuned rates** [LS, Theorem 27.1]. Under
the hypotheses of `linearExp3_integral_regret_le` on a nontrivial space of dimension `d`, with
`k ≥ 2` arms, `n ≥ 1` rounds, the exploration rate `γ = η g` and the learning rate
`η = √(log k / ((2 g + d) n))`, the expected regret against every arm is at most
`2 √((2 g + d) n log k)`. The weights are only defined for `γ ≤ 1`, which holds for `n` large
enough. -/
theorem linearExp3_integral_regret_le_two_mul_sqrt [Nontrivial E] (hπ : π ∈ simplex α)
    (hπu : IsUnit (∑ b, π b • rankOne ℝ (φ b) (φ b)))
    (hg : ∀ b, ⟪φ b, Ring.inverse (∑ b, π b • rankOne ℝ (φ b) (φ b)) (φ b)⟫_ℝ ≤ g)
    (hk : 1 < Fintype.card α) (hn : 0 < n)
    (hη : η = √(Real.log (Fintype.card α) / ((2 * g + finrank ℝ E) * n))) (hγ : γ = η * g)
    (hγ1 : γ ≤ 1) (hm : ∀ t < n, m t ≤ mΩ) (hA : ∀ t < n, ∀ c, MeasurableSet (A t ⁻¹' {c}))
    (hAW : ∀ t < n, ∀ c, P⟦A t ⁻¹' {c} | m t⟧ =ᵐ[P] fun ω ↦ linearExp3Weights π η γ
      (linearExp3Sum φ π η γ (A · ω) (fun s ↦ ⟪φ (A s ω), y s ω⟫_ℝ) t) c)
    (hy : ∀ t < n, AEStronglyMeasurable[m t] (y t) P)
    (hy1 : ∀ t < n, ∀ᵐ ω ∂P, ∀ c, |⟪φ c, y t ω⟫_ℝ| ≤ 1) (b : α) :
    ∫ ω, ∑ t ∈ range n, (⟪φ (A t ω), y t ω⟫_ℝ - ⟪φ b, y t ω⟫_ℝ) ∂P ≤
      2 * √((2 * g + finrank ℝ E) * n * Real.log (Fintype.card α)) := by
  set d : ℝ := (finrank ℝ E : ℝ) with hd_def
  set L := Real.log (Fintype.card α) with hL_def
  -- `g ≥ d ≥ 1`, since `∑ b, π b ⟪φ b, V(π)⁻¹ φ b⟫ = d`
  have hd1 : 1 ≤ d := Nat.one_le_cast.2 finrank_pos
  have hdg : d ≤ g := by
    rw [hd_def, ← sum_mul_inner_ringInverse_sum_smul_rankOne hπu]
    calc ∑ b, π b * ⟪φ b, Ring.inverse (∑ b, π b • rankOne ℝ (φ b) (φ b)) (φ b)⟫_ℝ
        ≤ ∑ b, π b * g := sum_le_sum fun b _ ↦
          mul_le_mul_of_nonneg_left (hg b) ((mem_simplex_iff.1 hπ).1 b)
      _ = g := by rw [← sum_mul, (mem_simplex_iff.1 hπ).2, one_mul]
  have hK : 0 < 2 * g + d := by linarith
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hL : 0 < L := Real.log_pos (Nat.one_lt_cast.2 hk)
  have hη0 : 0 < η := by rw [hη]; positivity
  -- the learning rate satisfies `L = η ^ 2 (2 g + d) n`
  have hη_sq : L = η ^ 2 * ((2 * g + d) * n) := by
    rw [hη, Real.sq_sqrt (by positivity)]
    field_simp
  refine (linearExp3_integral_regret_le hπ hπu hg hη0 (by rw [hγ]; nlinarith) hγ1
    (by rw [hγ]) hm hA hAW hy hy1 b).trans_eq ?_
  have h_sqrt : √((2 * g + d) * n * L) = η * ((2 * g + d) * n) := by
    rw [hη_sq, show (2 * g + d) * n * (η ^ 2 * ((2 * g + d) * n)) = (η * ((2 * g + d) * n)) ^ 2
      by ring, Real.sqrt_sq (by positivity)]
  rw [h_sqrt, hγ, ← hL_def, hη_sq]
  field_simp
  ring

/-- **Regret of Exp3 for adversarial linear bandits with the Kiefer–Wolfowitz exploration**
[LS, Theorem 27.1]. If the exploration distribution `π` has `⟪φ b, V(π)⁻¹ φ b⟫ ≤ d` for every
arm, on a nontrivial space of dimension `d` (such a distribution exists when the features span
`E`, by `exists_mem_simplex_inner_ringInverse_le_finrank`), then with `k ≥ 2` arms, `n ≥ 1` rounds,
`γ = η d` and `η = √(log k / (3 d n))`, the expected regret against every arm is at most
`2 √(3 d n log k)`. -/
theorem linearExp3_integral_regret_le_two_mul_sqrt_three [Nontrivial E] (hπ : π ∈ simplex α)
    (hπu : IsUnit (∑ b, π b • rankOne ℝ (φ b) (φ b)))
    (hg : ∀ b, ⟪φ b, Ring.inverse (∑ b, π b • rankOne ℝ (φ b) (φ b)) (φ b)⟫_ℝ ≤ finrank ℝ E)
    (hk : 1 < Fintype.card α) (hn : 0 < n)
    (hη : η = √(Real.log (Fintype.card α) / (3 * finrank ℝ E * n)))
    (hγ : γ = η * finrank ℝ E) (hγ1 : γ ≤ 1) (hm : ∀ t < n, m t ≤ mΩ)
    (hA : ∀ t < n, ∀ c, MeasurableSet (A t ⁻¹' {c}))
    (hAW : ∀ t < n, ∀ c, P⟦A t ⁻¹' {c} | m t⟧ =ᵐ[P] fun ω ↦ linearExp3Weights π η γ
      (linearExp3Sum φ π η γ (A · ω) (fun s ↦ ⟪φ (A s ω), y s ω⟫_ℝ) t) c)
    (hy : ∀ t < n, AEStronglyMeasurable[m t] (y t) P)
    (hy1 : ∀ t < n, ∀ᵐ ω ∂P, ∀ c, |⟪φ c, y t ω⟫_ℝ| ≤ 1) (b : α) :
    ∫ ω, ∑ t ∈ range n, (⟪φ (A t ω), y t ω⟫_ℝ - ⟪φ b, y t ω⟫_ℝ) ∂P ≤
      2 * √(3 * finrank ℝ E * n * Real.log (Fintype.card α)) := by
  have h3 : (3 : ℝ) * finrank ℝ E = 2 * finrank ℝ E + finrank ℝ E := by ring
  rw [h3] at hη ⊢
  exact linearExp3_integral_regret_le_two_mul_sqrt hπ hπu hg hk hn hη hγ hγ1 hm hA hAW hy hy1 b

end Regret

end LMLExplore.Bandits
