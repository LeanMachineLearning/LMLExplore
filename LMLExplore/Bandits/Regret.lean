/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import LMLExplore.SequentialLearning.FiniteActions
public import LeanMachineLearning.Online.Bandit.Regret

/-!
# Bounds on the gaps and the expected regret

Facts about LML's `gap` and `regret` of a bandit `ν : Kernel α ℝ` that hold for any sequence of
actions `A : ℕ → Ω → α`.

The first part gives lower bounds on the gaps and on the expected regret in terms of the expected
numbers of pulls.

The second part turns gap-dependent regret bounds into gap-free ones. The analysis of an algorithm
for stochastic bandits with finitely many arms typically bounds the expected number of pulls of
each suboptimal arm `a` by `C / Δ_a ^ 2 + B`, where `Δ_a = gap ν a`. The resulting regret bound
`∑ a, (C / Δ_a + B Δ_a)` blows up when some gap is small. This is turned into the gap-free bound
`2 √(C k n) + B ∑ a, Δ_a` at horizon `n`, with `k` the number of arms, by splitting the arms
according to whether their gap is below a threshold `δ`, as in the proof of [LS, Theorem 7.2].

The third part turns asymptotic bounds on the expected numbers of pulls into an asymptotic bound
on the expected regret. Asymptotic bounds are stated in eventual form: `limsup_n u_n / f(n) ≤ C` is
`∀ c > C, ∀ᶠ n in atTop, u_n ≤ c f(n)`. If `limsup_n E[T_a(n)] / f(n) ≤ C_a` for every arm `a` with
positive gap, then `limsup_n E[R_n] / f(n) ≤ ∑_{a : Δ_a > 0} Δ_a C_a`. With `f(n) = log n`, this is
how the asymptotic regret bounds of [LS, Theorems 8.1 and 10.6] follow from the bounds on the
numbers of pulls. Symmetrically, asymptotic lower bounds `liminf_n E[T_a(n)] / f(n) ≥ C_a`, with
constants in `ℝ≥0∞`, give `liminf_n E[R_n] / f(n) ≥ ∑_{a : Δ_a > 0} Δ_a C_a`, as in the Lai–Robbins
lower bound [LS, Theorem 16.2].

## Main statements

* `LMLExplore.Bandits.sub_le_gap`: the gap of an arm is at least its difference of mean with any
  other arm.
* `LMLExplore.Bandits.mul_sub_integral_pullCount_le_integral_regret`: if every arm other than `a₁`
  has gap at least `Δ`, the expected regret is at least `Δ (n - E[T_{a₁}(n)])`.
* `LMLExplore.Bandits.mul_integral_pullCount_le_integral_regret`: if the arm `a₁` has gap at least
  `Δ`, the expected regret is at least `Δ E[T_{a₁}(n)]`.
* `integral_regret_le_mul_add_div_add_of_forall_integral_pullCount_le`: the bound
  `δ n + k C / δ + B ∑ a, Δ_a` for every threshold `δ > 0`.
* `integral_regret_le_two_mul_sqrt_add_of_forall_integral_pullCount_le`: the bound
  `2 √(C k n) + B ∑ a, Δ_a`, for the optimal threshold `δ = √(C k / n)`.
* `integral_regret_eventually_le_of_forall_integral_pullCount_eventually_le`: eventual bounds
  `E[T_a(n)] ≤ c f(n)` for every `c > C_a` give the eventual bound `E[R_n] ≤ c f(n)` for every
  `c > ∑_{a : Δ_a > 0} Δ_a C_a`.
* `eventually_le_integral_regret_of_forall_eventually_le_integral_pullCount`: eventual bounds
  `c f(n) ≤ E[T_a(n)]` for every `c < C_a` give the eventual bound `c f(n) ≤ E[R_n]` for every
  `c < ∑_{a : Δ_a > 0} Δ_a C_a`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Finset Filter Learning Bandits

open scoped ENNReal

namespace LMLExplore.Bandits

section LowerBound

variable {α : Type*} [MeasurableSpace α]

/-- The gap of an arm is at least its difference of mean with any other arm. -/
theorem sub_le_gap [Finite α] (ν : Kernel α ℝ) (a j : α) :
    (ν j)[id] - (ν a)[id] ≤ gap ν a := by
  rw [gap]
  exact sub_le_sub_right (le_ciSup (f := fun i ↦ (ν i)[id]) (Set.finite_range _).bddAbove j) _

variable [StandardBorelSpace α] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {A : ℕ → Ω → α} {ν : Kernel α ℝ}

/-- If every arm other than `a₁` has gap at least `Δ`, the expected regret is at least
`Δ (n - E[T_{a₁}(n)])`. -/
theorem mul_sub_integral_pullCount_le_integral_regret [Finite α] [DecidableEq α]
    (hA : ∀ t, Measurable (A t)) {a₁ : α} {Δ : ℝ} (hΔ : ∀ a ≠ a₁, Δ ≤ gap ν a) (n : ℕ) :
    Δ * (n - ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P) ≤ ∫ ω, regret ν A n ω ∂P := by
  have := Fintype.ofFinite α
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount hA]
  have hnn (a : α) : 0 ≤ ∫ ω, (pullCount A a n ω : ℝ) ∂P :=
    integral_nonneg fun _ ↦ Nat.cast_nonneg _
  calc Δ * (n - ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P)
      = ∑ a ∈ univ.erase a₁, Δ * ∫ ω, (pullCount A a n ω : ℝ) ∂P := by
        rw [← mul_sum, ← sum_integral_pullCount (P := P) hA n, ← add_sum_erase _ _ (mem_univ a₁)]
        ring
    _ ≤ ∑ a ∈ univ.erase a₁, gap ν a * ∫ ω, (pullCount A a n ω : ℝ) ∂P :=
        sum_le_sum fun a ha ↦ mul_le_mul_of_nonneg_right (hΔ a (ne_of_mem_erase ha)) (hnn a)
    _ ≤ ∑ a, gap ν a * ∫ ω, (pullCount A a n ω : ℝ) ∂P :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
          fun a _ _ ↦ mul_nonneg gap_nonneg (hnn a)

/-- If the arm `a₁` has gap at least `Δ`, the expected regret is at least `Δ E[T_{a₁}(n)]`. -/
theorem mul_integral_pullCount_le_integral_regret [Finite α] [DecidableEq α]
    (hA : ∀ t, Measurable (A t)) {a₁ : α} {Δ : ℝ} (hΔ : Δ ≤ gap ν a₁) (n : ℕ) :
    Δ * ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P ≤ ∫ ω, regret ν A n ω ∂P := by
  have := Fintype.ofFinite α
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount hA]
  have hnn (a : α) : 0 ≤ ∫ ω, (pullCount A a n ω : ℝ) ∂P :=
    integral_nonneg fun _ ↦ Nat.cast_nonneg _
  calc Δ * ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P
      ≤ gap ν a₁ * ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P := mul_le_mul_of_nonneg_right hΔ (hnn a₁)
    _ ≤ ∑ a, gap ν a * ∫ ω, (pullCount A a n ω : ℝ) ∂P :=
        single_le_sum (f := fun a ↦ gap ν a * ∫ ω, (pullCount A a n ω : ℝ) ∂P)
          (fun a _ ↦ mul_nonneg gap_nonneg (hnn a)) (mem_univ a₁)

end LowerBound

section GapFree

variable {α Ω : Type*} [DecidableEq α] [Fintype α] [MeasurableSpace α] [StandardBorelSpace α]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ν : Kernel α ℝ} {A : ℕ → Ω → α} {n : ℕ} {B C : ℝ}

/-- If every arm `a` with positive gap `Δ_a` is pulled at most `C / Δ_a ^ 2 + B` times in
expectation during the first `n` rounds, then for every threshold `δ > 0` the expected regret at
horizon `n` is at most `δ n + k C / δ + B ∑ a, Δ_a`, where `k` is the number of arms. -/
theorem integral_regret_le_mul_add_div_add_of_forall_integral_pullCount_le
    (hA : ∀ t, Measurable (A t)) (hC : 0 ≤ C) (hB : 0 ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (h_le : ∀ a, 0 < gap ν a → P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤ C / gap ν a ^ 2 + B) :
    P[regret ν A n] ≤ δ * n + Fintype.card α * C / δ + B * ∑ a, gap ν a := by
  -- Each arm contributes at most `δ` per pull if its gap is at most `δ`, and at most
  -- `C / Δ_a + B Δ_a ≤ C / δ + B Δ_a` otherwise.
  have h_arm a : gap ν a * P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤
      δ * P[fun ω ↦ (pullCount A a n ω : ℝ)] + C / δ + B * gap ν a := by
    have h_nonneg : 0 ≤ P[fun ω ↦ (pullCount A a n ω : ℝ)] := integral_nonneg fun _ ↦ by simp
    have h_gap : 0 ≤ gap ν a := gap_nonneg
    rcases le_or_gt (gap ν a) δ with h_gap_le | h_lt
    · have : 0 ≤ C / δ + B * gap ν a := by positivity
      nlinarith
    · have h_gap_pos : 0 < gap ν a := hδ.trans h_lt
      calc gap ν a * P[fun ω ↦ (pullCount A a n ω : ℝ)]
      _ ≤ gap ν a * (C / gap ν a ^ 2 + B) := by gcongr; exact h_le a h_gap_pos
      _ = C / gap ν a + B * gap ν a := by field_simp
      _ ≤ C / δ + B * gap ν a := by gcongr
      _ ≤ δ * P[fun ω ↦ (pullCount A a n ω : ℝ)] + C / δ + B * gap ν a := by
        have : 0 ≤ δ * P[fun ω ↦ (pullCount A a n ω : ℝ)] := by positivity
        linarith
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount hA]
  refine (sum_le_sum fun a _ ↦ h_arm a).trans_eq ?_
  simp only [sum_add_distrib, ← mul_sum, sum_integral_pullCount hA n, sum_const, card_univ,
    nsmul_eq_mul]
  ring

/-- **Gap-free regret bound** [LS, Theorem 7.2]. If every arm `a` with positive gap `Δ_a` is
pulled at most `C / Δ_a ^ 2 + B` times in expectation during the first `n` rounds, then the
expected regret at horizon `n` is at most `2 √(C k n) + B ∑ a, Δ_a`, where `k` is the number of
arms. -/
theorem integral_regret_le_two_mul_sqrt_add_of_forall_integral_pullCount_le
    (hA : ∀ t, Measurable (A t)) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (h_le : ∀ a, 0 < gap ν a → P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤ C / gap ν a ^ 2 + B) :
    P[regret ν A n] ≤ 2 * √(C * Fintype.card α * n) + B * ∑ a, gap ν a := by
  have h_bound {δ : ℝ} (hδ : 0 < δ) :=
    integral_regret_le_mul_add_div_add_of_forall_integral_pullCount_le hA hC hB hδ h_le
  have h_gap_sum : 0 ≤ B * ∑ a, gap ν a := mul_nonneg hB (sum_nonneg fun _ _ ↦ gap_nonneg)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [regret_eq_sum_gap, h_gap_sum]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases (mul_nonneg hC (Nat.cast_nonneg (Fintype.card α))).eq_or_lt' with hCk | hCk
  · -- If `C k = 0`, the bound `δ n + B ∑ a, Δ_a` holds for every `δ > 0`.
    rw [hCk, zero_mul, Real.sqrt_zero, mul_zero, zero_add]
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    refine (h_bound (div_pos hε hn')).trans_eq ?_
    rw [mul_comm (Fintype.card α : ℝ), hCk]
    field_simp
    ring
  · -- Otherwise, the threshold `δ = s / n` with `s = √(C k n)` gives `δ n = k C / δ = s`.
    set s := √(C * Fintype.card α * n) with hs_def
    have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos hCk hn')
    have hs_sq : s ^ 2 = C * Fintype.card α * n := Real.sq_sqrt (mul_pos hCk hn').le
    refine (h_bound (div_pos hs hn')).trans_eq ?_
    field_simp
    linear_combination -hs_sq

end GapFree

section Asymptotic

variable {α Ω : Type*} [DecidableEq α] [Fintype α] [MeasurableSpace α] [StandardBorelSpace α]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ν : Kernel α ℝ} {A : ℕ → Ω → α}

/-- **Asymptotic regret from asymptotic numbers of pulls.** Let `f` be eventually nonnegative. If
for every arm `a` with positive gap and every `c > C_a`, eventually `E[T_a(n)] ≤ c f(n)`, then for
every `c > ∑_{a : Δ_a > 0} Δ_a C_a`, eventually `E[R_n] ≤ c f(n)`: in `limsup` form,
`limsup_n E[T_a(n)] / f(n) ≤ C_a` for each such arm gives
`limsup_n E[R_n] / f(n) ≤ ∑_{a : Δ_a > 0} Δ_a C_a`. -/
theorem integral_regret_eventually_le_of_forall_integral_pullCount_eventually_le
    (hA : ∀ t, Measurable (A t)) {f : ℕ → ℝ} (hf : ∀ᶠ n in atTop, 0 ≤ f n) (C : α → ℝ)
    (h_le : ∀ a, 0 < gap ν a → ∀ c > C a,
      ∀ᶠ n in atTop, P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤ c * f n)
    {c : ℝ} (hc : ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a), gap ν a * C a < c) :
    ∀ᶠ n in atTop, P[regret ν A n] ≤ c * f n := by
  set S := univ.filter (fun a ↦ 0 < gap ν a)
  -- Each arm of `S` gets the slack `δ / Δ_a` on its constant, where `#S δ ≤ c - ∑ a ∈ S, Δ_a C_a`.
  set δ := (c - ∑ a ∈ S, gap ν a * C a) / (#S + 1) with hδ_def
  have hδ : 0 < δ := div_pos (sub_pos.mpr hc) (by positivity)
  have hδS : #S * δ ≤ c - ∑ a ∈ S, gap ν a * C a := by
    rw [hδ_def, mul_div_assoc']
    exact div_le_of_le_mul₀ (by positivity) (sub_pos.mpr hc).le (by nlinarith)
  have h_arms : ∀ᶠ n in atTop, ∀ a ∈ S,
      P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤ (C a + δ / gap ν a) * f n :=
    (eventually_all_finset S).mpr fun a ha ↦ h_le a (mem_filter.mp ha).2 _
      (lt_add_of_pos_right _ (div_pos hδ (mem_filter.mp ha).2))
  filter_upwards [h_arms, hf] with n h_arms hfn
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount hA,
    ← sum_filter_of_ne fun a _ ha ↦ gap_nonneg.lt_of_ne' (left_ne_zero_of_mul ha)]
  calc ∑ a ∈ S, gap ν a * P[fun ω ↦ (pullCount A a n ω : ℝ)]
  _ ≤ ∑ a ∈ S, gap ν a * ((C a + δ / gap ν a) * f n) :=
    sum_le_sum fun a ha ↦ mul_le_mul_of_nonneg_left (h_arms a ha) gap_nonneg
  _ = ∑ a ∈ S, (gap ν a * C a + δ) * f n :=
    sum_congr rfl fun a ha ↦ by field_simp [(mem_filter.mp ha).2.ne']
  _ = (∑ a ∈ S, gap ν a * C a + #S * δ) * f n := by simp [← sum_mul, sum_add_distrib]
  _ ≤ c * f n := mul_le_mul_of_nonneg_right (by linarith) hfn

/-- **Asymptotic lower bound on the regret from the numbers of pulls.** Let `f` be eventually
nonnegative and `C : α → ℝ≥0∞`. If for every arm `a` with positive gap and every real `c` with
`c < C_a`, eventually `c f(n) ≤ E[T_a(n)]`, then for every real `c < ∑_{a : Δ_a > 0} Δ_a C_a`,
eventually `c f(n) ≤ E[R_n]`: in `liminf` form, `liminf_n E[T_a(n)] / f(n) ≥ C_a` for each such
arm gives `liminf_n E[R_n] / f(n) ≥ ∑_{a : Δ_a > 0} Δ_a C_a`. The constants are in `ℝ≥0∞`, which
allows the infinite constants of the Lai–Robbins lower bound [LS, Theorem 16.2]. -/
theorem eventually_le_integral_regret_of_forall_eventually_le_integral_pullCount
    (hA : ∀ t, Measurable (A t)) {f : ℕ → ℝ} (hf : ∀ᶠ n in atTop, 0 ≤ f n) (C : α → ℝ≥0∞)
    (h_le : ∀ a, 0 < gap ν a → ∀ c : ℝ, ENNReal.ofReal c < C a →
      ∀ᶠ n in atTop, c * f n ≤ P[fun ω ↦ (pullCount A a n ω : ℝ)])
    {c : ℝ} (hc : ENNReal.ofReal c <
      ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a), ENNReal.ofReal (gap ν a) * C a) :
    ∀ᶠ n in atTop, c * f n ≤ P[regret ν A n] := by
  set S := univ.filter (fun a ↦ 0 < gap ν a)
  -- The bound for an arm of `S` holds trivially for a nonpositive constant.
  have h_le' : ∀ a ∈ S, ∀ c : ℝ, (c ≤ 0 ∨ ENNReal.ofReal c < C a) →
      ∀ᶠ n in atTop, c * f n ≤ P[fun ω ↦ (pullCount A a n ω : ℝ)] := by
    rintro a ha c (hc | hc)
    · filter_upwards [hf] with n hfn
      exact (mul_nonpos_of_nonpos_of_nonneg hc hfn).trans
        (integral_nonneg fun _ ↦ Nat.cast_nonneg _)
    · exact h_le a (mem_filter.mp ha).2 c hc
  -- It suffices to write `c ≤ ∑_{a ∈ S} Δ_a c_a` with constants `c_a` to which `h_le'` applies.
  suffices h_split : ∃ c' : α → ℝ, (∀ a ∈ S, c' a ≤ 0 ∨ ENNReal.ofReal (c' a) < C a) ∧
      c ≤ ∑ a ∈ S, gap ν a * c' a by
    obtain ⟨c', hc'C, hc'⟩ := h_split
    have h_arms := (eventually_all_finset S).mpr fun a ha ↦ h_le' a ha (c' a) (hc'C a ha)
    filter_upwards [h_arms, hf] with n h_arms hfn
    rw [integral_regret_eq_sum_gap_mul_integral_pullCount hA]
    calc c * f n
    _ ≤ (∑ a ∈ S, gap ν a * c' a) * f n := mul_le_mul_of_nonneg_right hc' hfn
    _ = ∑ a ∈ S, gap ν a * (c' a * f n) := by simp_rw [sum_mul, mul_assoc]
    _ ≤ ∑ a ∈ S, gap ν a * P[fun ω ↦ (pullCount A a n ω : ℝ)] :=
      sum_le_sum fun a ha ↦ mul_le_mul_of_nonneg_left (h_arms a ha) gap_nonneg
    _ ≤ ∑ a, gap ν a * P[fun ω ↦ (pullCount A a n ω : ℝ)] :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun a _ _ ↦
        mul_nonneg gap_nonneg (integral_nonneg fun _ ↦ Nat.cast_nonneg _)
  rcases le_or_gt c 0 with hc0 | hc0
  · exact ⟨0, fun _ _ ↦ Or.inl le_rfl, by simpa using hc0⟩
  by_cases hC : ∃ a ∈ S, C a = ∞
  · -- An arm with an infinite constant carries all of `c`.
    obtain ⟨a₀, ha₀, hCa₀⟩ := hC
    have hgap : 0 < gap ν a₀ := (mem_filter.mp ha₀).2
    refine ⟨Pi.single a₀ (c / gap ν a₀), fun a _ ↦ ?_, ?_⟩
    · rcases eq_or_ne a a₀ with rfl | ha
      · exact Or.inr (by simp [hCa₀])
      · exact Or.inl (by simp [ha])
    · rw [sum_eq_single_of_mem a₀ ha₀ fun b _ hb ↦ by simp [hb], Pi.single_eq_same,
        mul_div_cancel₀ _ hgap.ne']
  · -- Otherwise, every constant is scaled by `c / s < 1`, where `s = ∑_{a ∈ S} Δ_a C_a`.
    push Not at hC
    set s := ∑ a ∈ S, gap ν a * (C a).toReal with hs_def
    have hsum : ∑ a ∈ S, ENNReal.ofReal (gap ν a) * C a = ENNReal.ofReal s := by
      rw [hs_def,
        ENNReal.ofReal_sum_of_nonneg fun a _ ↦ mul_nonneg gap_nonneg ENNReal.toReal_nonneg]
      refine sum_congr rfl fun a ha ↦ ?_
      rw [ENNReal.ofReal_mul gap_nonneg, ENNReal.ofReal_toReal (hC a ha)]
    rw [hsum, ENNReal.ofReal_lt_ofReal_iff'] at hc
    refine ⟨fun a ↦ c / s * (C a).toReal, fun a ha ↦ ?_, ?_⟩
    · rcases eq_or_ne (C a) 0 with h0 | h0
      · exact Or.inl (by simp [h0])
      · have hpos := ENNReal.toReal_pos h0 (hC a ha)
        have hcs : c / s < 1 := (div_lt_one hc.2).mpr hc.1
        refine Or.inr ?_
        rw [← ENNReal.ofReal_toReal (hC a ha), ENNReal.ofReal_lt_ofReal_iff hpos]
        nlinarith
    · simp_rw [mul_left_comm _ (c / s), ← mul_sum, ← hs_def, div_mul_cancel₀ _ hc.2.ne', le_rfl]

end Asymptotic

end LMLExplore.Bandits
