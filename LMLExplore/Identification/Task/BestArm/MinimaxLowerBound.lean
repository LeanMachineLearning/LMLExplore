/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.Regret
public import LMLExplore.Identification.MinimaxLowerBound
public import LMLExplore.Identification.Task.RealLaws
import LMLExplore.Identification.Task.BestArm.DifficultyRatio
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ZetaValues

/-!
# The minimax lower bound of fixed-budget best arm identification

For best arm identification with `K ≥ 2` arms with laws on `[0, 1]`, every algorithm with budget
`T` errs, on some Bernoulli bandit `θ` with a unique best arm and complexity
`H(θ) = ∑_b Δ_b⁻² ≤ 11 K²`, with probability at least
`exp(-400 T / (log K · H(θ))) / 6` [CL16, Theorem 1]; the proof gives
`exp(-(1600 / 9) T / (log K · H(θ))) / 4`. Here `Δ_b` is the gap of the arm `b` and the sum runs
over the arms other than the best arm, whose gap is `0`.

Hence no algorithm has probability of error at most `exp(-c T / H)` on every bandit with laws on
`[0, 1]`, for all large budgets `T`, with a constant `c > 1600 / (9 log K)`: unlike the
fixed-confidence setting, where `H log (1 / δ)` samples suffice up to a constant factor, the
fixed-budget setting loses a factor `log K` in the exponent when the complexity is unknown [CL16].
Successive rejects, whose probability of error is at most
`(K (K - 1) / 2) exp(-(T - K) / (log‾ K · H₂))`
(`SuccessiveRejects.measureReal_outputMeasure_compl_correct_le_of_unitIntervalLaws`), with
`H₂ ≤ H₁ ≤ 2 H` (`complexityTwo_le_complexityOne`), loses a factor of order `log K` only.

The bandits are those of [CL16, Section 4.2], with the gaps `2 e b / (5 K)` in place of the gaps
`(e b + 1) / (4 K)` of [CL16, proof of Theorem 1], for a numbering `e b ∈ {0, …, K - 1}` of the
arms. At the bandit `μ`, the arm `b` has the law `Ber(1 / 2 - d b)` with `d b = 2 e b / (5 K)`, so
that the arm `a₀` of number `0` is the best arm. For every other arm `j`, the bandit `λ j` moves
the arm `j` to `Ber(1 / 2 + d j)`, which makes it the best arm, with gaps `d j + d b`. With
`m = e j`, `H(λ j) ≤ (25 K² / 4) (2 / m)` and
`KL(Ber(1 / 2 - d j), Ber(1 / 2 + d j)) ≤ (400 / 9) (d j)²`, so that
`h = ∑_{j ≠ a₀} 1 / (H(λ j) KL_j) ≥ (9 / 800) ∑_{m = 1}^{K - 1} 1 / m ≥ (9 / 800) log K`, and the
minimax lower bound of [CL16, Theorem 2]
(`LMLExplore.Identification.IsFixedBudget.exists_exp_neg_div_four_le_measureReal`) applies. All
the complexities are at most `(25 K² / 4) (π² / 6) ≤ 11 K²`.

## Main statements

* `LMLExplore.Identification.exists_exp_neg_div_four_le_measureReal_unitIntervalLaws`: some
  Bernoulli bandit `θ` with a unique best arm and `H(θ) ≤ 11 K²` has probability of error at least
  `exp(-(1600 / 9) T / (log K · H(θ))) / 4`.
* `LMLExplore.Identification.exists_exp_neg_div_six_le_measureReal_unitIntervalLaws`: the same with
  the bound `exp(-400 T / (log K · H(θ))) / 6` of [CL16, Theorem 1].

## Implementation notes

The gaps `(e b + 1) / (4 K)` of [CL16] give the same bounds with other constants. The gaps
`2 e b / (5 K)` vanish at the best arm of `μ`, so that a single formula describes the bandit `μ`,
and keep the means in `(1 / 10, 9 / 10)`, where the relative entropy of the Bernoulli laws is at
most a constant times the squared difference of their means.

## References

* [CL16] A. Carpentier and A. Locatelli, *Tight (lower) bounds for the fixed budget best arm
  identification bandit problem*, COLT 2016.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Real Finset

open scoped ENNReal unitInterval

namespace LMLExplore.Identification

variable {α : Type*} [Fintype α] {mα : MeasurableSpace α} [MeasurableSingletonClass α]

/-! ### Auxiliary bounds -/

/-- `∑_{i < n} 1 / i² ≤ π² / 6`, the term `i = 0` being `0`. -/
private lemma sum_range_inv_sq_le (n : ℕ) : ∑ i ∈ range n, ((i : ℝ) ^ 2)⁻¹ ≤ π ^ 2 / 6 :=
  sum_le_hasSum (range n) (fun _ _ ↦ by positivity) (by simpa [one_div] using hasSum_zeta_two)

/-- `(5 K / 2)² (π² / 6) ≤ 11 K²`. -/
private lemma five_mul_div_two_sq_mul_le (K : ℝ) : (5 * K / 2) ^ 2 * (π ^ 2 / 6) ≤ 11 * K ^ 2 := by
  have hπ : π ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  nlinarith [sq_nonneg K]

/-- For `0 ≤ d < 2 / 5`, `KL(Ber(1 / 2 - d), Ber(1 / 2 + d)) ≤ (400 / 9) d²`, from the bound by the
`χ²`-divergence `(2 d)² / (1 / 4 - d²)`. -/
private lemma klBer_one_half_sub_one_half_add_le {d : ℝ} (h0 : 0 ≤ d) (h1 : d < 2 / 5) :
    klBer (1 / 2 - d) (1 / 2 + d) ≤ ENNReal.ofReal (400 / 9 * d ^ 2) := by
  refine (klBer_le_ofReal_sq_sub_div ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hd2 : d ^ 2 ≤ 4 / 25 := by nlinarith
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith [mul_nonneg (sq_nonneg d) (by linarith : (0 : ℝ) ≤ 4 / 25 - d ^ 2)]

omit [Fintype α] in
/-- In a Bernoulli bandit whose arm `a` has the largest success probability, the gap of the arm
`b` is the difference of their success probabilities. -/
private lemma gap_bernoulliBandit [Finite α] {p : α → I} {a : α} (ha : ∀ b ≠ a, (p b : ℝ) < p a)
    (b : α) : Bandits.gap (Bandits.bernoulliBandit p) b = p a - p b := by
  have := Fintype.ofFinite α
  have : Nonempty α := ⟨a⟩
  rw [Bandits.gap_eq_bestArm_sub, Bandits.bestArm_eq_of_forall_lt (by simpa using ha)]
  simp

/-! ### Bernoulli models -/

/-- The model of the Bernoulli bandit with success probabilities `p`. -/
private noncomputable def bernoulliModel (p : α → I) : α → ProbabilityMeasure ℝ :=
  (exists_lawBandit_eq (Bandits.bernoulliBandit p)).choose

private lemma lawBandit_bernoulliModel (p : α → I) :
    lawBandit (bernoulliModel p) = Bandits.bernoulliBandit p :=
  (exists_lawBandit_eq (Bandits.bernoulliBandit p)).choose_spec

private lemma lawMean_bernoulliModel (p : α → I) (b : α) : lawMean (bernoulliModel p) b = p b := by
  rw [lawMean_eq_integral_lawBandit, lawBandit_bernoulliModel,
    Bandits.integral_id_bernoulliBandit]

/-- A Bernoulli model whose arm `a` has the largest success probability is a model of best arm
identification with laws on `[0, 1]`, with best arm `a`. -/
private lemma mem_M_bernoulliModel {p : α → I} {a : α} (ha : ∀ b ≠ a, (p b : ℝ) < p a) :
    bernoulliModel p ∈ ((baiTask (lawBandit (α := α)) lawMean).restrict
      (Set.univ.pi fun _ ↦ unitIntervalLaws)).M := by
  rw [IdentTask.M_restrict]
  refine ⟨?_, mem_pi_unitIntervalLaws_iff.2 fun b ↦ ?_⟩
  · rw [M_baiTask]
    exact ⟨a, fun b hb ↦ by rw [lawMean_bernoulliModel, lawMean_bernoulliModel]; exact ha b hb⟩
  · rw [lawBandit_bernoulliModel]
    exact Bandits.ae_mem_Icc_bernoulliBandit p b

private lemma correct_bernoulliModel {p : α → I} {a : α} (ha : ∀ b ≠ a, (p b : ℝ) < p a) :
    (baiTask (lawBandit (α := α)) lawMean).correct (bernoulliModel p) = {a} :=
  (correct_baiTask_eq_singleton_iff _ _).2 fun b hb ↦ by
    rw [lawMean_bernoulliModel, lawMean_bernoulliModel]
    exact ha b hb

/-- The complexity `∑_b Δ_b⁻²` of a Bernoulli model whose arm `a` has the largest success
probability. -/
private lemma sum_inv_sq_gap_bernoulliModel {p : α → I} {a : α}
    (ha : ∀ b ≠ a, (p b : ℝ) < p a) :
    ∑ b, (Bandits.gap (lawBandit (bernoulliModel p)) b ^ 2)⁻¹ = ∑ b, (((p a : ℝ) - p b) ^ 2)⁻¹ := by
  simp_rw [lawBandit_bernoulliModel, gap_bernoulliBandit ha]

/-! ### The bandits of [CL16] -/

section Family

variable (e : α ≃ Fin (Fintype.card α))

/-- The gap `d b = 2 e b / (5 K)` of the arm `b` in the bandits of [CL16], for a numbering `e` of
the arms. -/
private noncomputable def clGap (b : α) : ℝ := 2 / (5 * Fintype.card α) * (e b : ℕ)

variable {e}

private lemma clGap_nonneg (b : α) : 0 ≤ clGap e b := by
  unfold clGap
  positivity

private lemma clGap_lt (b : α) : clGap e b < 2 / 5 := by
  have hK : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos_iff.2 ⟨b⟩
  have heK : ((e b : ℕ) : ℝ) < Fintype.card α := by exact_mod_cast (e b).isLt
  unfold clGap
  rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

private lemma clGap_eq_zero {a₀ : α} (ha₀ : (e a₀ : ℕ) = 0) : clGap e a₀ = 0 := by
  simp [clGap, ha₀]

private lemma one_le_numbering {a₀ b : α} (ha₀ : (e a₀ : ℕ) = 0) (hb : b ≠ a₀) :
    1 ≤ (e b : ℕ) :=
  Nat.one_le_iff_ne_zero.2 fun h ↦ hb (e.injective (Fin.ext (h.trans ha₀.symm)))

private lemma clGap_pos {a₀ b : α} (ha₀ : (e a₀ : ℕ) = 0) (hb : b ≠ a₀) : 0 < clGap e b := by
  have hK : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos_iff.2 ⟨b⟩
  have : (0 : ℝ) < (e b : ℕ) := by exact_mod_cast one_le_numbering ha₀ hb
  unfold clGap
  positivity

private lemma inv_sq_clGap (b : α) :
    (clGap e b ^ 2)⁻¹ = (5 * Fintype.card α / 2) ^ 2 * ((((e b : ℕ) : ℝ)) ^ 2)⁻¹ := by
  rw [clGap, mul_pow, mul_inv]
  congr 1
  rw [← inv_pow, inv_div]

variable (e)

/-- The success probabilities `1 / 2 - d b` of the bandit `μ` of [CL16]. -/
private noncomputable def clBase (b : α) : I :=
  ⟨1 / 2 - clGap e b, by constructor <;> linarith [clGap_nonneg (e := e) b, clGap_lt (e := e) b]⟩

/-- The success probabilities of the bandit `λ j` of [CL16]: the arm `j` of `μ` moved to
`1 / 2 + d j`. -/
private noncomputable def clAlt [DecidableEq α] (j : α) : α → I :=
  Function.update (clBase e) j
    ⟨1 / 2 + clGap e j, by constructor <;> linarith [clGap_nonneg (e := e) j, clGap_lt (e := e) j]⟩

variable {e}

private lemma coe_clBase (b : α) : (clBase e b : ℝ) = 1 / 2 - clGap e b := rfl

private lemma coe_clAlt_self [DecidableEq α] (j : α) : (clAlt e j j : ℝ) = 1 / 2 + clGap e j := by
  simp [clAlt]

private lemma clAlt_of_ne [DecidableEq α] {j b : α} (hb : b ≠ j) : clAlt e j b = clBase e b := by
  simp [clAlt, hb]

private lemma clBase_lt {a₀ : α} (ha₀ : (e a₀ : ℕ) = 0) {b : α} (hb : b ≠ a₀) :
    (clBase e b : ℝ) < clBase e a₀ := by
  rw [coe_clBase, coe_clBase, clGap_eq_zero ha₀]
  linarith [clGap_pos ha₀ hb]

private lemma clAlt_lt [DecidableEq α] {a₀ : α} (ha₀ : (e a₀ : ℕ) = 0) {j b : α} (hj : j ≠ a₀)
    (hb : b ≠ j) : (clAlt e j b : ℝ) < clAlt e j j := by
  rw [clAlt_of_ne hb, coe_clAlt_self, coe_clBase]
  linarith [clGap_pos ha₀ hj, clGap_nonneg (e := e) b]

/-- The complexity of `μ` is `(5 K / 2)² ∑_b 1 / (e b)²`, at most `11 K²`. -/
private lemma sum_inv_sq_gap_clBase_le {a₀ : α} (ha₀ : (e a₀ : ℕ) = 0) :
    ∑ b, (Bandits.gap (lawBandit (bernoulliModel (clBase e))) b ^ 2)⁻¹ ≤
      11 * Fintype.card α ^ 2 := by
  rw [sum_inv_sq_gap_bernoulliModel (p := clBase e) (a := a₀) fun b hb ↦ clBase_lt ha₀ hb]
  simp_rw [coe_clBase, clGap_eq_zero ha₀, sub_zero, sub_sub_cancel, inv_sq_clGap, ← mul_sum]
  refine le_trans ?_ (five_mul_div_two_sq_mul_le _)
  gcongr
  have : ∑ b, ((((e b : ℕ) : ℝ)) ^ 2)⁻¹ = ∑ i ∈ range (Fintype.card α), ((i : ℝ) ^ 2)⁻¹ := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Fintype.sum_equiv e _ _ fun _ ↦ rfl
  rw [this]
  exact sum_range_inv_sq_le _

/-- The complexity of `λ j` is at most `(5 K / 2)² ∑_b 1 / (e j + e b)²`. -/
private lemma sum_inv_sq_gap_clAlt_le [DecidableEq α] {a₀ : α} (ha₀ : (e a₀ : ℕ) = 0) {j : α}
    (hj : j ≠ a₀) :
    ∑ b, (Bandits.gap (lawBandit (bernoulliModel (clAlt e j))) b ^ 2)⁻¹ ≤
      (5 * Fintype.card α / 2) ^ 2 * ∑ b, ((((e j : ℕ) : ℝ) + (e b : ℕ)) ^ 2)⁻¹ := by
  rw [sum_inv_sq_gap_bernoulliModel (p := clAlt e j) (a := j) fun b hb ↦ clAlt_lt ha₀ hj hb,
    mul_sum]
  refine sum_le_sum fun b _ ↦ ?_
  rcases eq_or_ne b j with rfl | hb
  · rw [sub_self, sq, mul_zero, inv_zero]
    positivity
  refine le_of_eq ?_
  rw [clAlt_of_ne hb, coe_clAlt_self, coe_clBase, clGap, clGap,
    show 1 / 2 + 2 / (5 * (Fintype.card α : ℝ)) * (e j : ℕ) -
      (1 / 2 - 2 / (5 * Fintype.card α) * (e b : ℕ)) =
        2 / (5 * Fintype.card α) * ((e j : ℕ) + (e b : ℕ)) by ring,
    mul_pow, mul_inv]
  congr 1
  rw [← inv_pow, inv_div]

/-- The complexity of `λ j` times the bound `(400 / 9) (d j)²` on its divergence from `μ` is at
most `(800 / 9) e j`. -/
private lemma sum_inv_sq_gap_clAlt_mul_le [DecidableEq α] {a₀ : α} (ha₀ : (e a₀ : ℕ) = 0) {j : α}
    (hj : j ≠ a₀) :
    (∑ b, (Bandits.gap (lawBandit (bernoulliModel (clAlt e j))) b ^ 2)⁻¹) *
      (400 / 9 * clGap e j ^ 2) ≤ 800 / 9 * ((e j : ℕ) : ℝ) := by
  have hm : (1 : ℝ) ≤ (e j : ℕ) := by exact_mod_cast one_le_numbering ha₀ hj
  have hK0 : (Fintype.card α : ℝ) ≠ 0 := by
    have : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos_iff.2 ⟨j⟩
    positivity
  calc (∑ b, (Bandits.gap (lawBandit (bernoulliModel (clAlt e j))) b ^ 2)⁻¹) *
        (400 / 9 * clGap e j ^ 2)
      ≤ (5 * Fintype.card α / 2) ^ 2 * (2 / ((e j : ℕ) : ℝ)) * (400 / 9 * clGap e j ^ 2) := by
        gcongr
        exact (sum_inv_sq_gap_clAlt_le ha₀ hj).trans (mul_le_mul_of_nonneg_left
          (sum_inv_sq_add_numbering_le e (one_le_numbering ha₀ hj)) (by positivity))
    _ = 800 / 9 * ((e j : ℕ) : ℝ) := by
        simp only [clGap]
        field_simp
        ring

/-- The complexity of `λ j` is at most `11 K²`. -/
private lemma sum_inv_sq_gap_clAlt_le_mul_sq [DecidableEq α] {a₀ : α} (ha₀ : (e a₀ : ℕ) = 0)
    {j : α} (hj : j ≠ a₀) :
    ∑ b, (Bandits.gap (lawBandit (bernoulliModel (clAlt e j))) b ^ 2)⁻¹ ≤
      11 * Fintype.card α ^ 2 := by
  refine (sum_inv_sq_gap_clAlt_le ha₀ hj).trans (le_trans ?_ (five_mul_div_two_sq_mul_le _))
  gcongr
  have hj1 : (1 : ℝ) ≤ (e j : ℕ) := by exact_mod_cast one_le_numbering ha₀ hj
  calc ∑ b, ((((e j : ℕ) : ℝ) + (e b : ℕ)) ^ 2)⁻¹
      ≤ ∑ b, ((((e b : ℕ) : ℝ) + 1) ^ 2)⁻¹ :=
        sum_le_sum fun b _ ↦ inv_anti₀ (by positivity)
          (pow_le_pow_left₀ (by positivity) (by linarith) 2)
    _ = ∑ i ∈ range (Fintype.card α), (((i : ℝ) + 1) ^ 2)⁻¹ := by
        rw [← Fin.sum_univ_eq_sum_range (fun i ↦ (((i : ℝ) + 1) ^ 2)⁻¹)]
        exact Fintype.sum_equiv e _ _ fun _ ↦ rfl
    _ = ∑ i ∈ range (Fintype.card α + 1), ((i : ℝ) ^ 2)⁻¹ := by
        rw [sum_range_succ']
        simp
    _ ≤ π ^ 2 / 6 := sum_range_inv_sq_le _

/-- The complexity of a model whose arm `a` has the largest success probability is positive when
there is another arm. -/
private lemma sum_inv_sq_gap_bernoulliModel_pos {p : α → I} {a b : α}
    (ha : ∀ b ≠ a, (p b : ℝ) < p a) (hb : b ≠ a) :
    0 < ∑ c, (Bandits.gap (lawBandit (bernoulliModel p)) c ^ 2)⁻¹ := by
  rw [sum_inv_sq_gap_bernoulliModel ha]
  refine lt_of_lt_of_le ?_ (single_le_sum (fun c _ ↦ by positivity) (mem_univ b))
  have := sub_pos.2 (ha b hb)
  positivity

end Family

/-! ### The minimax lower bound -/

/-- **Minimax lower bound of fixed-budget best arm identification** [CL16, Theorem 1]. Let `α`
have `K ≥ 2` arms. For every algorithm `A` with budget `T`, some Bernoulli bandit `θ` with a unique
best arm, whose complexity `H(θ) = ∑_b Δ_b⁻²` is at most `11 K²`, satisfies
`exp(-(1600 / 9) T / (log K · H(θ))) / 4 ≤ P_θ(error)`. -/
theorem exists_exp_neg_div_four_le_measureReal_unitIntervalLaws (hK : 2 ≤ Fintype.card α)
    {A : IdentAlg Unit α ℝ α} {T : ℕ} (hA : IsFixedBudget A T) :
    ∃ θ ∈ ((baiTask (lawBandit (α := α)) lawMean).restrict
        (Set.univ.pi fun _ ↦ unitIntervalLaws)).M,
      ∑ b, (Bandits.gap (lawBandit θ) b ^ 2)⁻¹ ≤ 11 * Fintype.card α ^ 2 ∧
      exp (-(1600 / 9 * T / (Real.log (Fintype.card α) *
          ∑ b, (Bandits.gap (lawBandit θ) b ^ 2)⁻¹))) / 4 ≤
        (A.outputMeasure (Environment.bandit (lawBandit θ))).real
          ((baiTask lawBandit lawMean).correct θ)ᶜ := by
  classical
  have hlogK : 0 < Real.log (Fintype.card α) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Fintype.card α))
  -- The arms are numbered `e b = 0, …, K - 1`, and `a₀` has number `0`.
  set e := Fintype.equivFin α
  set a₀ := e.symm ⟨0, by omega⟩
  have ha₀ : (e a₀ : ℕ) = 0 := by simp [a₀]
  set s := univ.erase a₀
  have hs : s.Nonempty := by
    obtain ⟨b, hb⟩ : ∃ b, b ≠ a₀ := by
      by_contra! h
      have : Fintype.card α ≤ 1 := Fintype.card_le_one_iff.2 fun x y ↦ (h x).trans (h y).symm
      omega
    exact ⟨b, mem_erase.2 ⟨hb, mem_univ b⟩⟩
  obtain ⟨b₁, hb₁⟩ := hs
  have hb₁a : b₁ ≠ a₀ := ne_of_mem_erase hb₁
  set lam : α → α → ProbabilityMeasure ℝ := fun j ↦ bernoulliModel (clAlt e j)
  set H : (α → ProbabilityMeasure ℝ) → ℝ := fun θ ↦ ∑ b, (Bandits.gap (lawBandit θ) b ^ 2)⁻¹
  have hHl_pos (j : α) (hj : j ≠ a₀) : 0 < H (lam j) :=
    sum_inv_sq_gap_bernoulliModel_pos (p := clAlt e j) (a := j)
      (fun _ hb ↦ clAlt_lt ha₀ hj hb) hj.symm
  set k : α → ℝ := fun j ↦ 400 / 9 * clGap e j ^ 2
  -- The minimax lower bound at `μ` with the alternatives `λ j`, `j ≠ a₀`.
  obtain ⟨θ, hθ, hbound⟩ := IsFixedBudget.exists_exp_neg_div_four_le_measureReal
    (task := baiTask (lawBandit (α := α)) lawMean) hA ⟨b₁, hb₁⟩ (lam := lam)
    (fun j hj ↦ by
      rw [correct_bernoulliModel (p := clBase e) (a := a₀) fun _ hb ↦ clBase_lt ha₀ hb,
        correct_bernoulliModel (p := clAlt e j) (a := j)
          fun _ hb ↦ clAlt_lt ha₀ (ne_of_mem_erase hj) hb]
      exact Set.disjoint_singleton.2 (ne_of_mem_erase hj).symm)
    (fun j _ b hb ↦ by
      simp only [ν_baiTask, lam]
      rw [lawBandit_bernoulliModel, lawBandit_bernoulliModel, Bandits.bernoulliBandit_apply,
        Bandits.bernoulliBandit_apply, clAlt_of_ne hb])
    (H := H) (sum_nonneg fun _ _ ↦ by positivity) (fun j hj ↦ hHl_pos j (ne_of_mem_erase hj))
    (k := k) (fun j hj ↦ by have := clGap_pos ha₀ (ne_of_mem_erase hj); positivity)
    (fun j _ ↦ by
      simp only [ν_baiTask, lam]
      rw [lawBandit_bernoulliModel, lawBandit_bernoulliModel, Bandits.bernoulliBandit_apply,
        Bandits.bernoulliBandit_apply, klDiv_bernoulliMeasure one_ne_zero, coe_clBase,
        coe_clAlt_self]
      exact klBer_one_half_sub_one_half_add_le (clGap_nonneg j) (clGap_lt j))
  -- `h = ∑_{j ≠ a₀} 1 / (H(λ j) k j) ≥ (9 / 800) log K`, since `H(λ j) k j ≤ (800 / 9) e j`.
  have hh : 9 / 800 * Real.log (Fintype.card α) ≤ ∑ j ∈ s, (H (lam j) * k j)⁻¹ := by
    calc 9 / 800 * Real.log (Fintype.card α) ≤ ∑ j ∈ s, (800 / 9 * ((e j : ℕ) : ℝ))⁻¹ := by
          simp_rw [mul_inv, ← mul_sum, inv_div]
          gcongr
          exact log_card_le_sum_inv_numbering e ha₀
      _ ≤ ∑ j ∈ s, (H (lam j) * k j)⁻¹ := by
          refine sum_le_sum fun j hj ↦ ?_
          have hj' := ne_of_mem_erase hj
          have hk_pos : 0 < k j := by have := clGap_pos ha₀ hj'; positivity
          exact inv_anti₀ (mul_pos (hHl_pos j hj') hk_pos) (sum_inv_sq_gap_clAlt_mul_le ha₀ hj')
  -- Every model of the family is admissible, with a positive complexity at most `11 K²`.
  have hfam : θ ∈ ((baiTask (lawBandit (α := α)) lawMean).restrict
      (Set.univ.pi fun _ ↦ unitIntervalLaws)).M ∧ 0 < H θ ∧ H θ ≤ 11 * Fintype.card α ^ 2 := by
    rcases hθ with rfl | ⟨j, hj, rfl⟩
    · exact ⟨mem_M_bernoulliModel (p := clBase e) (a := a₀) fun _ hb ↦ clBase_lt ha₀ hb,
        sum_inv_sq_gap_bernoulliModel_pos (p := clBase e) (a := a₀)
          (fun _ hb ↦ clBase_lt ha₀ hb) hb₁a,
        sum_inv_sq_gap_clBase_le ha₀⟩
    · have hj' := ne_of_mem_erase hj
      exact ⟨mem_M_bernoulliModel (p := clAlt e j) (a := j) fun _ hb ↦ clAlt_lt ha₀ hj' hb,
        hHl_pos j hj',
        sum_inv_sq_gap_clAlt_le_mul_sq ha₀ hj'⟩
  obtain ⟨hθM, hHθ, hHθ_le⟩ := hfam
  simp only [ν_baiTask] at hbound
  -- `2 T / (H(θ) h) ≤ (1600 / 9) T / (log K · H(θ))`.
  have key : 2 * (T : ℝ) / (H θ * ∑ j ∈ s, (H (lam j) * k j)⁻¹) ≤
      1600 / 9 * T / (Real.log (Fintype.card α) * H θ) :=
    calc 2 * (T : ℝ) / (H θ * ∑ j ∈ s, (H (lam j) * k j)⁻¹)
        ≤ 2 * T / (H θ * (9 / 800 * Real.log (Fintype.card α))) := by gcongr
      _ = 1600 / 9 * T / (Real.log (Fintype.card α) * H θ) := by
          field_simp
          ring
  exact ⟨θ, hθM, hHθ_le, le_trans (div_le_div_of_nonneg_right
    (Real.exp_le_exp.2 (neg_le_neg key)) (by norm_num)) hbound⟩

/-- **Minimax lower bound of fixed-budget best arm identification, with the constants of [CL16]**
[CL16, Theorem 1]. Let `α` have `K ≥ 2` arms. For every algorithm `A` with budget `T`, some
Bernoulli bandit `θ` with a unique best arm, whose complexity `H(θ) = ∑_b Δ_b⁻²` is at most
`11 K²`, satisfies `exp(-400 T / (log K · H(θ))) / 6 ≤ P_θ(error)`. -/
theorem exists_exp_neg_div_six_le_measureReal_unitIntervalLaws (hK : 2 ≤ Fintype.card α)
    {A : IdentAlg Unit α ℝ α} {T : ℕ} (hA : IsFixedBudget A T) :
    ∃ θ ∈ ((baiTask (lawBandit (α := α)) lawMean).restrict
        (Set.univ.pi fun _ ↦ unitIntervalLaws)).M,
      ∑ b, (Bandits.gap (lawBandit θ) b ^ 2)⁻¹ ≤ 11 * Fintype.card α ^ 2 ∧
      exp (-(400 * T / (Real.log (Fintype.card α) *
          ∑ b, (Bandits.gap (lawBandit θ) b ^ 2)⁻¹))) / 6 ≤
        (A.outputMeasure (Environment.bandit (lawBandit θ))).real
          ((baiTask lawBandit lawMean).correct θ)ᶜ := by
  obtain ⟨θ, hθ, hH, hbound⟩ := exists_exp_neg_div_four_le_measureReal_unitIntervalLaws hK hA
  refine ⟨θ, hθ, hH, le_trans ?_ hbound⟩
  have hX : 0 ≤ Real.log (Fintype.card α) * ∑ b, (Bandits.gap (lawBandit θ) b ^ 2)⁻¹ :=
    mul_nonneg (Real.log_natCast_nonneg _) (sum_nonneg fun _ _ ↦ by positivity)
  calc exp (-(400 * T / (Real.log (Fintype.card α) *
          ∑ b, (Bandits.gap (lawBandit θ) b ^ 2)⁻¹))) / 6
      ≤ exp (-(1600 / 9 * T / (Real.log (Fintype.card α) *
          ∑ b, (Bandits.gap (lawBandit θ) b ^ 2)⁻¹))) / 6 := by
        gcongr
        norm_num
    _ ≤ _ := by gcongr; norm_num

end LMLExplore.Identification
