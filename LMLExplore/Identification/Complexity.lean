/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.Regret
public import LMLExplore.NumberTheory.Harmonic.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The complexities `H₁` and `H₂` of best arm identification

The fixed-budget guarantees of [ABM10] for best arm identification are stated in terms of the
gaps `Δ_b` of the arms of a bandit `ν` through the complexity `H₂ = max_i i Δ_(i)⁻²`, where
`Δ_(1) ≤ ⋯ ≤ Δ_(K)` are the gaps sorted increasingly, and through the constant
`log‾ K = 1 / 2 + ∑_{i = 2}^K 1 / i`. When the best arm is unique, the complexity
`H₁ = ∑_i Δ_(i)⁻²` of [ABM10] is the sum of the inverse squared gaps, with the gap `Δ_(1) = 0` of
the best arm replaced by `Δ_(2)`; `complexityOne` extends it to every bandit, and agrees with the
[ABM10] quantity only when the best arm is unique. The two complexities are equivalent up to a
logarithmic factor [ABM10]: `H₂ ≤ H₁` when the best arm is unique, and
`H₁ ≤ log‾ K H₂ ≤ log (2 K) H₂` for every bandit, so that bounds stated with `H₂`, such as the
probability of error of successive rejects, can be read in terms of the more familiar `H₁` at the
price of a factor `log (2 K)`. For Gaussian arms, `2 σ2 H₁` is the complexity `H(μ)` of [GK16]
that bounds the characteristic time of best arm identification
(`LMLExplore/Identification/Task/BestArm.lean`).

## Main definitions

In the namespace `LMLExplore.Identification`:

* `complexityTwo ν`: the complexity `H₂` of best arm identification, written without sorting the
  gaps: the largest `r_b / Δ_b²` over the arms `b`, with `r_b` the number of arms whose gap is at
  most `Δ_b`.
* `logBar K`: the constant `log‾ K = 1 / 2 + ∑_{i = 2}^K 1 / i`.
* `complexityOne ν`: the complexity `H₁` of best arm identification, written without sorting the
  gaps: `∑_b Δ_b⁻² + max_b Δ_b⁻²`, with the inverse of a zero gap equal to `0`. It is the [ABM10]
  quantity when the best arm is unique.

## Main statements

* `le_complexityTwo`, `complexityTwo_le`: `H₂` is the least upper bound of the `r_b / Δ_b²`.
* `complexityTwo_nonneg`, `complexityTwo_pos`: `H₂ ≥ 0`, and `H₂ > 0` when some gap is positive.
* `sub_card_div_complexityTwo_le_gap_sq`: an arm of a set `B` of arms with the largest gaps among
  the arms other than the unique best arm has `Δ_b² ≥ (K + 1 - #B) / H₂`.
* `logBar_eq_sum`, `one_half_le_logBar`: `log‾ K` as a sum, and `log‾ K ≥ 1 / 2`.
* `logBar_mono`, `logBar_le_log_two_mul`: `log‾` is monotone, and `log‾ K ≤ log (2 K)`.
* `complexityOne_eq_of_forall_lt`: if `a` is the unique best arm, then
  `H₁ = ∑_{b ≠ a} Δ_b⁻² + (min_{b ≠ a} Δ_b)⁻²`.
* `complexityTwo_le_complexityOne`: `H₂ ≤ H₁` when the best arm is unique.
* `complexityOne_le_logBar_mul`, `complexityOne_le_logBar_two_mul`,
  `complexityOne_le_log_two_mul_mul`: `H₁ ≤ log‾ K H₂`, hence `H₁ ≤ log‾ (2 K) H₂` and
  `H₁ ≤ log (2 K) H₂`.

## References

* [ABM10] J.-Y. Audibert, S. Bubeck and R. Munos, *Best arm identification in multi-armed
  bandits*, COLT 2010.
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Section 2.2.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning

namespace LMLExplore.Identification

/-! ### The constant `log‾ K` -/

/-- The constant `log‾ K = 1 / 2 + ∑_{i = 2}^K 1 / i` of [ABM10], written with the harmonic number
`H_K = ∑_{i = 1}^K 1 / i` as `H_K - 1 / 2`. -/
noncomputable def logBar (K : ℕ) : ℝ := harmonic K - 1 / 2

lemma logBar_def (K : ℕ) : logBar K = harmonic K - 1 / 2 := (rfl)

lemma logBar_eq_sum {K : ℕ} (hK : K ≠ 0) :
    logBar K = ∑ j ∈ range (K - 1), ((K - j : ℝ))⁻¹ + 1 / 2 := by
  rw [sum_range_inv_sub_eq_harmonic_sub_one hK, logBar]
  ring

lemma one_half_le_logBar {K : ℕ} (hK : K ≠ 0) : 1 / 2 ≤ logBar K := by
  rw [logBar_eq_sum hK, le_add_iff_nonneg_left]
  refine sum_nonneg fun j hj ↦ inv_nonneg.2 (sub_nonneg.2 ?_)
  exact_mod_cast (mem_range.1 hj).le.trans (Nat.sub_le K 1)

/-- `log‾` is monotone. -/
lemma logBar_mono : Monotone logBar := fun m n hmn ↦ by
  rw [logBar, logBar]
  gcongr
  exact_mod_cast harmonic_mono hmn

/-- `log‾ K ≤ log (2 K)`, from `H_K ≤ 1 + log K` and `1 / 2 ≤ log 2`. -/
lemma logBar_le_log_two_mul {K : ℕ} (hK : K ≠ 0) : logBar K ≤ Real.log (2 * K) := by
  rw [logBar, Real.log_mul two_ne_zero (by exact_mod_cast hK)]
  have h_log_two : 1 - 2⁻¹ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos two_pos
  linarith [harmonic_le_one_add_log K]

/-! ### The complexity `H₂` -/

variable {α : Type*} [MeasurableSpace α] [Fintype α] {ν : Kernel α ℝ}

/-- The complexity `H₂` of best arm identification [ABM10]: the largest `r_b / Δ_b²` over the
arms `b`, where `Δ_b` is the gap of `b` and `r_b` is the number of arms whose gap is at most `Δ_b`.
The term of an arm of gap zero is `0`. When the best arm is unique and `Δ_(1) ≤ ⋯ ≤ Δ_(K)` are the
gaps sorted increasingly, with the gap `0` of the best arm replaced by the smallest gap of the
other arms, this is `max_i i Δ_(i)⁻²`: within a block of equal gaps, `i Δ_(i)⁻²` is largest at
the last index of the block, which is `r_b` for the arms `b` of the block. -/
noncomputable def complexityTwo (ν : Kernel α ℝ) : ℝ :=
  ⨆ b, (#{c | Bandits.gap ν c ≤ Bandits.gap ν b} : ℝ) / Bandits.gap ν b ^ 2

lemma complexityTwo_def (ν : Kernel α ℝ) :
    complexityTwo ν = ⨆ b, (#{c | Bandits.gap ν c ≤ Bandits.gap ν b} : ℝ) / Bandits.gap ν b ^ 2 :=
  (rfl)

lemma le_complexityTwo (ν : Kernel α ℝ) (b : α) :
    (#{c | Bandits.gap ν c ≤ Bandits.gap ν b} : ℝ) / Bandits.gap ν b ^ 2 ≤ complexityTwo ν :=
  le_ciSup (Set.finite_range fun b ↦
    (#{c | Bandits.gap ν c ≤ Bandits.gap ν b} : ℝ) / Bandits.gap ν b ^ 2).bddAbove b

lemma complexityTwo_le [Nonempty α] {x : ℝ}
    (h : ∀ b, (#{c | Bandits.gap ν c ≤ Bandits.gap ν b} : ℝ) / Bandits.gap ν b ^ 2 ≤ x) :
    complexityTwo ν ≤ x :=
  ciSup_le h

lemma complexityTwo_nonneg (ν : Kernel α ℝ) : 0 ≤ complexityTwo ν :=
  Real.iSup_nonneg fun _ ↦ by positivity

/-- `H₂` is positive as soon as some arm has a positive gap. -/
lemma complexityTwo_pos {b : α} (hb : 0 < Bandits.gap ν b) : 0 < complexityTwo ν :=
  (div_pos (by exact_mod_cast card_pos.2 ⟨b, by simp⟩) (pow_pos hb 2)).trans_le
    (le_complexityTwo ν b)

/-- If `B` is a set of arms other than the unique best arm `a'` whose gaps are at least those of
the other arms `c ≠ a'`, and `b ∈ B`, then `Δ_b² ≥ (K + 1 - #B) / H₂`: the `K + 1 - #B` arms
outside `B`, together with `b`, have gaps at most `Δ_b`. -/
lemma sub_card_div_complexityTwo_le_gap_sq [DecidableEq α] {a' : α}
    (ha' : ∀ b ≠ a', (ν b)[id] < (ν a')[id]) {B : Finset α} (hB : B ⊆ univ.erase a')
    (h_top : ∀ b ∈ B, ∀ c ∈ univ.erase a' \ B, Bandits.gap ν c ≤ Bandits.gap ν b)
    {b : α} (hb : b ∈ B) :
    ((Fintype.card α : ℝ) + 1 - #B) / complexityTwo ν ≤ Bandits.gap ν b ^ 2 := by
  have : Nonempty α := ⟨a'⟩
  have hΔ : 0 < Bandits.gap ν b := Bandits.gap_pos_of_forall_lt ha' (mem_erase.1 (hB hb)).1
  -- The arms outside `B`, and `b`, have gaps at most that of `b`.
  have h_rank : #(B.erase b)ᶜ ≤ #{c | Bandits.gap ν c ≤ Bandits.gap ν b} := by
    refine card_le_card fun c hc ↦ ?_
    rw [mem_compl, mem_erase, not_and_or, not_not] at hc
    rw [mem_filter_univ]
    rcases hc with rfl | hc
    · exact le_rfl
    rcases eq_or_ne c a' with rfl | hca
    · rw [← Bandits.bestArm_eq_of_forall_lt ha', Bandits.gap_bestArm]
      exact Bandits.gap_nonneg
    · exact h_top b hb c (mem_sdiff.2 ⟨mem_erase.2 ⟨hca, mem_univ c⟩, hc⟩)
  rw [card_compl, card_erase_of_mem hb] at h_rank
  have h_rank' : (Fintype.card α : ℝ) + 1 - #B ≤ #{c | Bandits.gap ν c ≤ Bandits.gap ν b} := by
    have hBK : #B ≤ Fintype.card α := card_le_univ B
    have hB1 : 1 ≤ #B := card_pos.2 ⟨b, hb⟩
    calc (Fintype.card α : ℝ) + 1 - #B = (Fintype.card α - (#B - 1) : ℕ) := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub hB1]
          ring
      _ ≤ _ := by exact_mod_cast h_rank
  have hH := le_complexityTwo ν b
  rw [div_le_iff₀ (pow_pos hΔ 2)] at hH
  rw [div_le_iff₀ (complexityTwo_pos hΔ)]
  nlinarith

/-! ### The complexity `H₁` -/

/-- The complexity `H₁` of best arm identification [ABM10]: `∑_b Δ_b⁻² + max_b Δ_b⁻²`, where `Δ_b`
is the gap of the arm `b` and the inverse of a zero gap is `0`. When the best arm `a` is unique,
this is `∑_{b ≠ a} Δ_b⁻² + (min_{b ≠ a} Δ_b)⁻²` (`complexityOne_eq_of_forall_lt`): the sum
`∑_i Δ_(i)⁻²` of [ABM10] over the gaps `Δ_(1) ≤ ⋯ ≤ Δ_(K)` sorted increasingly, with the gap `0` of
the best arm replaced by the smallest gap `Δ_(2)` of the other arms. -/
noncomputable def complexityOne (ν : Kernel α ℝ) : ℝ :=
  ∑ b, (Bandits.gap ν b ^ 2)⁻¹ + ⨆ b, (Bandits.gap ν b ^ 2)⁻¹

lemma complexityOne_def (ν : Kernel α ℝ) :
    complexityOne ν = ∑ b, (Bandits.gap ν b ^ 2)⁻¹ + ⨆ b, (Bandits.gap ν b ^ 2)⁻¹ :=
  (rfl)

lemma complexityOne_nonneg (ν : Kernel α ℝ) : 0 ≤ complexityOne ν :=
  add_nonneg (sum_nonneg fun _ _ ↦ by positivity) (Real.iSup_nonneg fun _ ↦ by positivity)

/-- If `a` is the unique best arm and there are other arms, then
`H₁ = ∑_{b ≠ a} Δ_b⁻² + (min_{b ≠ a} Δ_b)⁻²`. -/
lemma complexityOne_eq_of_forall_lt [DecidableEq α] {a : α}
    (ha : ∀ b ≠ a, (ν b)[id] < (ν a)[id]) (h : (univ.erase a).Nonempty) :
    complexityOne ν = ∑ b ∈ univ.erase a, (Bandits.gap ν b ^ 2)⁻¹ +
      ((univ.erase a).inf' h (Bandits.gap ν) ^ 2)⁻¹ := by
  have : Nonempty α := ⟨a⟩
  have hga : Bandits.gap ν a = 0 := by
    rw [← Bandits.bestArm_eq_of_forall_lt ha, Bandits.gap_bestArm]
  have h_inf_pos : 0 < (univ.erase a).inf' h (Bandits.gap ν) :=
    (lt_inf'_iff h).2 fun b hb ↦ Bandits.gap_pos_of_forall_lt ha (mem_erase.1 hb).1
  rw [complexityOne, sum_erase _ (by simp [hga])]
  congr 1
  refine le_antisymm (ciSup_le fun b ↦ ?_) ?_
  · rcases eq_or_ne b a with rfl | hb
    · rw [hga, sq, mul_zero, inv_zero]
      positivity
    · exact inv_anti₀ (by positivity)
        (pow_le_pow_left₀ h_inf_pos.le (inf'_le _ (mem_erase.2 ⟨hb, mem_univ b⟩)) 2)
  · obtain ⟨b, -, hb⟩ := exists_mem_eq_inf' h (Bandits.gap ν)
    rw [hb]
    exact le_ciSup (Set.finite_range fun b ↦ (Bandits.gap ν b ^ 2)⁻¹).bddAbove b

/-- `H₂ ≤ H₁` when the best arm `a` is unique [ABM10]. The uniqueness cannot be dropped: with gaps
`0, 0, 1`, `H₂ = 3` while `H₁ = 2`. -/
lemma complexityTwo_le_complexityOne {a : α} (ha : ∀ b ≠ a, (ν b)[id] < (ν a)[id]) :
    complexityTwo ν ≤ complexityOne ν := by
  classical
  have : Nonempty α := ⟨a⟩
  refine complexityTwo_le fun b ↦ ?_
  rcases eq_or_ne b a with rfl | hb
  · rw [← Bandits.bestArm_eq_of_forall_lt ha, Bandits.gap_bestArm]
    simpa using complexityOne_nonneg ν
  set Δ := Bandits.gap ν b
  set S : Finset α := {c | Bandits.gap ν c ≤ Δ}
  have hΔ : 0 < Δ := Bandits.gap_pos_of_forall_lt ha hb
  have haS : a ∈ S := by
    rw [mem_filter_univ, ← Bandits.bestArm_eq_of_forall_lt ha, Bandits.gap_bestArm]
    exact hΔ.le
  -- Every arm of `S` other than `a` has a positive gap at most `Δ`.
  have h_le (c : α) (hc : c ∈ S.erase a) : (Δ ^ 2)⁻¹ ≤ (Bandits.gap ν c ^ 2)⁻¹ := by
    obtain ⟨hca, hcS⟩ := mem_erase.1 hc
    exact inv_anti₀ (pow_pos (Bandits.gap_pos_of_forall_lt ha hca) 2)
      (pow_le_pow_left₀ Bandits.gap_nonneg ((mem_filter_univ c).1 hcS) 2)
  calc (#S : ℝ) / Δ ^ 2 = #(S.erase a) • (Δ ^ 2)⁻¹ + (Δ ^ 2)⁻¹ := by
        rw [← card_erase_add_one haS, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ∑ c ∈ S.erase a, (Bandits.gap ν c ^ 2)⁻¹ + ⨆ c, (Bandits.gap ν c ^ 2)⁻¹ := by
        gcongr
        · exact card_nsmul_le_sum _ _ _ h_le
        · exact le_ciSup (Set.finite_range fun c ↦ (Bandits.gap ν c ^ 2)⁻¹).bddAbove b
    _ ≤ complexityOne ν := by
        rw [complexityOne]
        gcongr ?_ + _
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ by positivity

/-- The inverse squared gap of an arm is at most `H₂ / r_b`, with `r_b` the number of arms whose
gap is at most that of `b`. -/
private lemma inv_gap_sq_le_complexityTwo_div (ν : Kernel α ℝ) (b : α) :
    (Bandits.gap ν b ^ 2)⁻¹ ≤
      complexityTwo ν / #{c | Bandits.gap ν c ≤ Bandits.gap ν b} := by
  have hr : (0 : ℝ) < #{c | Bandits.gap ν c ≤ Bandits.gap ν b} :=
    mod_cast card_pos.2 ⟨b, by simp⟩
  rw [le_div_iff₀ hr, ← div_eq_inv_mul]
  exact le_complexityTwo ν b

/-- The sum part of `H₁` is at most `(H_K - 1) H₂`: by the bound `Δ_b⁻² ≤ H₂ / r_b`, it is at most
`H₂` times the sum of the inverse ranks `1 / r_b` of the arms of positive gap, and the arms of gap
zero, which share the rank `r_b`, have inverse ranks summing to `1`. -/
private lemma sum_inv_gap_sq_le [Nonempty α] (ν : Kernel α ℝ) :
    ∑ b, (Bandits.gap ν b ^ 2)⁻¹ ≤ (harmonic (Fintype.card α) - 1) * complexityTwo ν := by
  set r : α → ℝ := fun b ↦ #{c | Bandits.gap ν c ≤ Bandits.gap ν b}
  set Z : Finset α := {b | ¬ 0 < Bandits.gap ν b}
  -- The arms of gap zero have rank `#Z`, so their inverse ranks sum to `1`.
  have hZ : Z.Nonempty := ⟨Bandits.bestArm ν, by simp [Z, Bandits.gap_bestArm]⟩
  have h_zero : ∑ b ∈ Z, (r b)⁻¹ = 1 := by
    have h_rank (b : α) (hb : b ∈ Z) : r b = #Z := by
      have hb0 : Bandits.gap ν b = 0 :=
        le_antisymm (not_lt.1 ((mem_filter_univ b).1 hb)) Bandits.gap_nonneg
      simp only [r, Z, hb0, not_lt]
    rw [sum_congr rfl fun b hb ↦ by rw [h_rank b hb], sum_const, nsmul_eq_mul,
      mul_inv_cancel₀ (by exact_mod_cast hZ.card_pos.ne')]
  have h_rank_sum : ∑ b with 0 < Bandits.gap ν b, (r b)⁻¹ + 1 ≤ harmonic (Fintype.card α) := by
    rw [← h_zero, sum_filter_add_sum_filter_not]
    exact sum_inv_card_filter_le_le_harmonic univ (Bandits.gap ν)
  calc ∑ b, (Bandits.gap ν b ^ 2)⁻¹ = ∑ b with 0 < Bandits.gap ν b, (Bandits.gap ν b ^ 2)⁻¹ := by
        refine (sum_filter_of_ne fun b _ hb ↦ ?_).symm
        exact Bandits.gap_nonneg.lt_of_ne fun h ↦ hb (by simp [← h])
    _ ≤ ∑ b with 0 < Bandits.gap ν b, complexityTwo ν * (r b)⁻¹ :=
        sum_le_sum fun b _ ↦ (inv_gap_sq_le_complexityTwo_div ν b).trans_eq (div_eq_mul_inv _ _)
    _ ≤ (harmonic (Fintype.card α) - 1) * complexityTwo ν := by
        rw [← mul_sum, mul_comm]
        gcongr
        · exact complexityTwo_nonneg ν
        · linarith

/-- The maximum part of `H₁` is at most `H₂ / 2`: an arm of positive gap has rank at least `2`,
since the best arm has a smaller gap. -/
private lemma iSup_inv_gap_sq_le [Nonempty α] (ν : Kernel α ℝ) :
    ⨆ b, (Bandits.gap ν b ^ 2)⁻¹ ≤ complexityTwo ν / 2 := by
  classical
  refine ciSup_le fun b ↦ ?_
  rcases (Bandits.gap_nonneg (ν := ν) (a := b)).eq_or_lt' with hb | hb
  · rw [hb]
    simpa using div_nonneg (complexityTwo_nonneg ν) zero_le_two
  refine (inv_gap_sq_le_complexityTwo_div ν b).trans
    (div_le_div_of_nonneg_left (complexityTwo_nonneg ν) two_pos ?_)
  -- The arm `b` and the best arm, of gap `0`, both have gaps at most `Δ_b`.
  have h_ne : Bandits.bestArm ν ≠ b := fun h ↦ hb.ne' (h ▸ Bandits.gap_bestArm)
  have h_two : 1 < #{c | Bandits.gap ν c ≤ Bandits.gap ν b} :=
    one_lt_card.2 ⟨Bandits.bestArm ν, by simpa [Bandits.gap_bestArm] using hb.le, b, by simp, h_ne⟩
  exact_mod_cast h_two

/-- `H₁ ≤ log‾ K H₂` [ABM10], for every bandit with `K ≥ 1` arms, even when several arms are
best. -/
lemma complexityOne_le_logBar_mul [Nonempty α] (ν : Kernel α ℝ) :
    complexityOne ν ≤ logBar (Fintype.card α) * complexityTwo ν := by
  rw [complexityOne, logBar]
  linarith [sum_inv_gap_sq_le ν, iSup_inv_gap_sq_le ν]

/-- `H₁ ≤ log‾ (2 K) H₂`, a weakening of `complexityOne_le_logBar_mul`. -/
lemma complexityOne_le_logBar_two_mul [Nonempty α] (ν : Kernel α ℝ) :
    complexityOne ν ≤ logBar (2 * Fintype.card α) * complexityTwo ν :=
  (complexityOne_le_logBar_mul ν).trans (mul_le_mul_of_nonneg_right
    (logBar_mono (Nat.le_mul_of_pos_left _ two_pos)) (complexityTwo_nonneg ν))

/-- `H₁ ≤ log (2 K) H₂` [ABM10], from `H₁ ≤ log‾ K H₂` and `log‾ K ≤ log (2 K)`. -/
lemma complexityOne_le_log_two_mul_mul [Nonempty α] (ν : Kernel α ℝ) :
    complexityOne ν ≤ Real.log (2 * Fintype.card α) * complexityTwo ν :=
  (complexityOne_le_logBar_mul ν).trans (mul_le_mul_of_nonneg_right
    (logBar_le_log_two_mul Fintype.card_ne_zero) (complexityTwo_nonneg ν))

end LMLExplore.Identification
