/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.SubgradientDescent
import LMLExplore.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# A lower bound for online subgradient descent with decreasing rates on unbounded sets

With nonincreasing learning rates, the regret bound of online subgradient descent keeps the term
`D ^ 2 / (2 η (n - 1))`, where `D` bounds the distance of the plays to the comparator. On a bounded
set `D` is the diameter, and the rates `η t ∝ 1 / √(t + 1)` give a regret of order `√n`. On an
unbounded set no such `D` exists, and this file shows that the limitation is real [Ora, Theorem
5.4]: for `0 < α < 1`, unprojected online subgradient descent on `ℝ` from `0` with the rates
`η t = (t + 1) ^ (-α)` has regret at least `φ(α) / 2 * n ^ (2 - α)` against `0`, a power of `n`
above `n`, where `φ(α) = 1 / (2 - α) + (2 ^ (α - 1) - 1) / (1 - α)` and `n ≥ 2 / ((1 - α) φ(α))`.

The losses are linear, `x ↦ g t * x`, hence convex and `1`-Lipschitz: `g t = -1` on the first
`⌈n / 2⌉ = (n + 1) / 2` rounds, which push the plays to `∑_{i < t} (i + 1) ^ (-α)`, of order
`t ^ (1 - α)`, and `g t = 1` afterwards, which make the learner lose on each round of the second
half about as much as it moved in the first.

## Main statements

* `LMLExplore.OnlineLearning.mul_rpow_sub_rpow_div_le_regret`: for `0 ≤ α < 1` and every horizon
  `n`, the regret of the plays of unprojected online subgradient descent on these losses against
  `0` is at least `φ(α) * n ^ (2 - α) - n ^ (1 - α) / (1 - α)`.
* `LMLExplore.OnlineLearning.div_two_mul_rpow_le_regret`: [Ora, Theorem 5.4] for `0 < α < 1` and
  `n ≥ 2 / ((1 - α) φ(α))`, it is at least `φ(α) / 2 * n ^ (2 - α)`.
* `OnlineLearner.exists_div_two_mul_rpow_le_regret_run_onlineSubgradientDescent`:
  the same bound for the online subgradient descent learner on `ℝ`, on some linear losses of
  slopes in `[-1, 1]`.
* `LMLExplore.OnlineLearning.one_div_two_sub_add_two_rpow_sub_one_div_pos`: `φ(α) > 0` for
  `0 < α < 1`, so the bound grows like `n ^ (2 - α)`.
* `LMLExplore.OnlineLearning.tendsto_one_div_two_sub_add_two_rpow_sub_one_div`: `φ(α) → 1 - log 2`
  as `α → 1`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Finset Filter Topology Real

namespace LMLExplore.OnlineLearning

variable {α : ℝ} {n : ℕ}

/-- The constant `φ(α) = 1 / (2 - α) + (2 ^ (α - 1) - 1) / (1 - α)` of the lower bound for online
subgradient descent with the rates `(t + 1) ^ (-α)` is positive for `0 < α < 1`. -/
theorem one_div_two_sub_add_two_rpow_sub_one_div_pos (hα0 : 0 < α) (hα1 : α < 1) :
    0 < 1 / (2 - α) + ((2 : ℝ) ^ (α - 1) - 1) / (1 - α) := by
  -- Bernoulli's inequality for the exponent `1 - α ∈ (0, 1)`: `2 ^ (1 - α) < 2 - α`
  have hB := rpow_one_add_lt_one_add_mul_self (s := 1) (by norm_num) one_ne_zero
    (p := 1 - α) (by linarith) (by linarith)
  norm_num at hB
  have hu : 0 < (2 : ℝ) ^ (1 - α) := by positivity
  have h2 : (2 : ℝ) ^ (α - 1) = ((2 : ℝ) ^ (1 - α))⁻¹ := by
    rw [← rpow_neg zero_le_two, neg_sub]
  have h1 : 0 < 1 - α := by linarith
  have h2' : 0 < 2 - α := by linarith
  rw [h2, show 1 / (2 - α) + (((2 : ℝ) ^ (1 - α))⁻¹ - 1) / (1 - α) =
    ((2 - α) - (2 : ℝ) ^ (1 - α)) / ((2 - α) * (1 - α) * (2 : ℝ) ^ (1 - α)) by
      field_simp; ring]
  exact div_pos (by linarith) (by positivity)

/-- The constant `φ(α) = 1 / (2 - α) + (2 ^ (α - 1) - 1) / (1 - α)` of the lower bound for online
subgradient descent with the rates `(t + 1) ^ (-α)` tends to `1 - log 2` as `α → 1`. -/
theorem tendsto_one_div_two_sub_add_two_rpow_sub_one_div :
    Tendsto (fun α : ℝ ↦ 1 / (2 - α) + ((2 : ℝ) ^ (α - 1) - 1) / (1 - α)) (𝓝[<] 1)
      (𝓝 (1 - log 2)) := by
  -- `(2 ^ (α - 1) - 1) / (1 - α)` is minus the slope at `1` of `α ↦ 2 ^ (α - 1)`, whose
  -- derivative there is `log 2`
  have hd : HasDerivAt (fun α : ℝ ↦ (2 : ℝ) ^ (α - 1)) (log 2) 1 := by
    simpa using ((hasStrictDerivAt_const_rpow two_pos (1 - 1)).hasDerivAt).comp_sub_const 1 1
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).neg.mono_left
    (nhdsWithin_mono (1 : ℝ) fun x (hx : x ∈ Set.Iio (1 : ℝ)) ↦
      Set.mem_compl_singleton_iff.mpr (ne_of_lt hx))
  have h1 : Tendsto (fun α : ℝ ↦ 1 / (2 - α)) (𝓝[<] 1) (𝓝 1) := by
    have h : Tendsto (fun α : ℝ ↦ 1 / (2 - α)) (𝓝 1) (𝓝 (1 / (2 - 1))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.sub tendsto_id) (by norm_num)
    convert h.mono_left nhdsWithin_le_nhds using 2
    norm_num
  convert h1.add hs using 2 with α
  · rw [slope_def_field, sub_self, rpow_zero, show (1 : ℝ) - α = -(α - 1) by ring, div_neg]

/-- The regret of the losses `x ↦ g t * x` that switch from `g t = -1` to `g t = 1` at round `m`,
against `0`, of the plays `x t = -∑_{i < t} η i * g i` of unprojected online subgradient descent
from `0` with the rates `η`. -/
private lemma sum_mul_neg_sum_eq (η g : ℕ → ℝ) {m : ℕ} (hg : ∀ t, g t = if t < m then -1 else 1)
    {n : ℕ} (hmn : m ≤ n) :
    ∑ t ∈ range n, g t * -∑ i ∈ range t, η i * g i =
      ∑ i ∈ range n, ((i : ℝ) + 1) * η i - n * ∑ i ∈ Ico m n, η i +
        (n - 2 * m) * ∑ i ∈ range m, η i := by
  -- the plays are `x t = ∑_{i < t} η i` for `t ≤ m`, and `x t = 2 x m - x t` afterwards
  have hneg : ∀ t ≤ m, ∑ i ∈ range t, η i * g i = -∑ i ∈ range t, η i := fun t ht ↦ by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun i hi ↦ by simp [hg, show i < m by simp at hi; omega]
  have hpos : ∀ k, ∑ i ∈ Ico m k, η i * g i = ∑ i ∈ Ico m k, η i := fun k ↦
    sum_congr rfl fun i hi ↦ by simp [hg, show ¬i < m by simp at hi; omega]
  induction n, hmn using Nat.le_induction with
  | base =>
    have hS : ∀ k ≤ m, ∑ t ∈ range k, g t * -∑ i ∈ range t, η i * g i =
        ∑ i ∈ range k, ((i : ℝ) + 1) * η i - k * ∑ i ∈ range k, η i := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        rw [sum_range_succ, ih (by omega), hneg k (by omega)]
        simp only [hg k, show k < m by omega, ite_true]
        simp only [sum_range_succ]
        push_cast
        ring
    rw [hS m le_rfl, Ico_self, sum_empty]
    ring
  | succ n hmn ih =>
    rw [sum_range_succ, ih, ← sum_range_add_sum_Ico (fun i ↦ η i * g i) hmn, hneg m le_rfl, hpos,
      sum_range_succ, sum_Ico_succ_top hmn]
    simp only [hg n, show ¬n < m by omega, ite_false]
    push_cast
    ring

/-- **The regret of unprojected online subgradient descent with the rates `(t + 1) ^ (-α)`.**
Let `0 ≤ α < 1`, and let the slopes `g t` be `-1` on the first `(n + 1) / 2` rounds and `1`
afterwards. The plays `x` of online subgradient descent on `ℝ` from `x 0 = 0` with the rates
`(t + 1) ^ (-α)` and the losses `x ↦ g t * x` have a regret against `0` after `n` rounds of at least
`φ(α) * n ^ (2 - α) - n ^ (1 - α) / (1 - α)`, with
`φ(α) = 1 / (2 - α) + (2 ^ (α - 1) - 1) / (1 - α)`. -/
theorem mul_rpow_sub_rpow_div_le_regret (hα0 : 0 ≤ α) (hα1 : α < 1) {x g : ℕ → ℝ}
    (hg : ∀ t, g t = if t < (n + 1) / 2 then -1 else 1) (hx0 : x 0 = 0)
    (hx : ∀ t, x (t + 1) = x t - ((t : ℝ) + 1) ^ (-α) * g t) :
    (1 / (2 - α) + ((2 : ℝ) ^ (α - 1) - 1) / (1 - α)) * n ^ (2 - α) -
        (n : ℝ) ^ (1 - α) / (1 - α) ≤ regret (fun t b ↦ g t * b) x 0 n := by
  set m := (n + 1) / 2
  set η : ℕ → ℝ := fun i ↦ ((i : ℝ) + 1) ^ (-α) with hη
  have hs : 0 < 1 - α := by linarith
  -- the plays are `x t = -∑_{i < t} η i * g i`, so that the regret has a closed form
  have hxt : ∀ t, x t = -∑ i ∈ range t, η i * g i := by
    intro t
    induction t with
    | zero => simp [hx0]
    | succ t ih => rw [hx, ih, sum_range_succ]; ring
  have hR : regret (fun t b ↦ g t * b) x 0 n =
      ∑ i ∈ range n, ((i : ℝ) + 1) ^ (1 - α) - n * ∑ i ∈ Ico m n, η i +
        (n - 2 * m) * ∑ i ∈ range m, η i := by
    simp only [regret_def, mul_zero, sub_zero, hxt]
    rw [sum_mul_neg_sum_eq η g hg (by omega)]
    congr 2
    refine sum_congr rfl fun i _ ↦ ?_
    rw [hη, show (1 - α) = 1 + -α by ring, rpow_add (by positivity), rpow_one]
  -- the three sums, compared with integrals of powers
  have hA : (n : ℝ) ^ (2 - α) / (2 - α) ≤ ∑ i ∈ range n, ((i : ℝ) + 1) ^ (1 - α) := by
    have h := sub_div_le_sum_Ico_add_one_rpow (r := 1 - α) hs.le (Nat.zero_le n)
    rwa [show 1 - α + 1 = 2 - α by ring, Nat.cast_zero, zero_rpow (by linarith), sub_zero,
      ← range_eq_Ico] at h
  have hB : ∑ i ∈ Ico m n, η i ≤ ((n : ℝ) ^ (1 - α) - (m : ℝ) ^ (1 - α)) / (1 - α) := by
    have h := sum_Ico_add_one_rpow_le (r := -α) (by linarith) (by linarith) (m := m) (n := n)
      (by omega)
    rwa [show -α + 1 = 1 - α by ring] at h
  have hC : ∑ i ∈ range m, η i ≤ (m : ℝ) ^ (1 - α) / (1 - α) := by
    have h := sum_Ico_add_one_rpow_le (r := -α) (by linarith) (by linarith) (Nat.zero_le m)
    rwa [show -α + 1 = 1 - α by ring, Nat.cast_zero, zero_rpow hs.ne', sub_zero,
      ← range_eq_Ico] at h
  have hC0 : 0 ≤ ∑ i ∈ range m, η i := sum_nonneg fun i _ ↦ by positivity
  -- `n / 2 ≤ m ≤ n` and `2 m ≤ n + 1`
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast (show m ≤ n by omega)
  have hnm : (n : ℝ) ≤ 2 * m := by exact_mod_cast (show n ≤ 2 * m by omega)
  have hnm' : 2 * (m : ℝ) ≤ n + 1 := by exact_mod_cast (show 2 * m ≤ n + 1 by omega)
  set a := (n : ℝ) ^ (1 - α)
  set b := (m : ℝ) ^ (1 - α)
  have hab : b ≤ a := rpow_le_rpow (Nat.cast_nonneg m) hmn hs.le
  have hba : a * (2 : ℝ) ^ (α - 1) ≤ b := by
    have h := rpow_le_rpow (by positivity) (show (n : ℝ) / 2 ≤ m by linarith) hs.le
    rwa [div_rpow (Nat.cast_nonneg n) zero_le_two, div_eq_mul_inv, ← rpow_neg zero_le_two,
      neg_sub] at h
  have ha : 0 ≤ a := by positivity
  have hn2 : (n : ℝ) ^ (2 - α) = n * a := by
    rw [show 2 - α = 1 - α + 1 by ring, rpow_add_one' (Nat.cast_nonneg n) (by linarith), mul_comm]
  rw [hR, hn2]
  rw [hn2] at hA
  calc (1 / (2 - α) + ((2 : ℝ) ^ (α - 1) - 1) / (1 - α)) * (n * a) - a / (1 - α)
      ≤ n * a / (2 - α) - n * ((a - b) / (1 - α)) - b / (1 - α) := by
        -- `m ≥ n / 2` gives `b ≥ 2 ^ (α - 1) a`, and `m ≤ n` gives `b ≤ a`
        have h : n * a / (2 - α) - n * ((a - b) / (1 - α)) - b / (1 - α) -
            ((1 / (2 - α) + ((2 : ℝ) ^ (α - 1) - 1) / (1 - α)) * (n * a) - a / (1 - α)) =
              (n * b - n * (a * (2 : ℝ) ^ (α - 1)) + (a - b)) / (1 - α) := by
          field_simp
          ring
        have h' := mul_le_mul_of_nonneg_left hba (Nat.cast_nonneg n)
        exact sub_nonneg.mp (h ▸ div_nonneg (by linarith) hs.le)
    _ ≤ ∑ i ∈ range n, ((i : ℝ) + 1) ^ (1 - α) - n * ∑ i ∈ Ico m n, η i +
        (n - 2 * m) * ∑ i ∈ range m, η i := by
        -- `-1 ≤ n - 2 m ≤ 0`, so the last term is at least `-∑_{i < m} η i`
        have h1 := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg n)
        have h2 : 0 ≤ ((n : ℝ) - 2 * m + 1) * ∑ i ∈ range m, η i :=
          mul_nonneg (by linarith) hC0
        nlinarith

/-- **The lower bound for online subgradient descent with the rates `(t + 1) ^ (-α)` on unbounded
sets** [Ora, Theorem 5.4]. Let `0 < α < 1`, `φ(α) = 1 / (2 - α) + (2 ^ (α - 1) - 1) / (1 - α)` and
`n ≥ 2 / ((1 - α) φ(α))`, and let the slopes `g t` be `-1` on the first `(n + 1) / 2` rounds and
`1` afterwards. The plays `x` of online subgradient descent on `ℝ` from `x 0 = 0` with the rates
`(t + 1) ^ (-α)` and the losses `x ↦ g t * x` have a regret against `0` after `n` rounds of at least
`φ(α) / 2 * n ^ (2 - α)`. -/
theorem div_two_mul_rpow_le_regret (hα0 : 0 < α) (hα1 : α < 1)
    (hn : 2 / ((1 - α) * (1 / (2 - α) + ((2 : ℝ) ^ (α - 1) - 1) / (1 - α))) ≤ n) {x g : ℕ → ℝ}
    (hg : ∀ t, g t = if t < (n + 1) / 2 then -1 else 1) (hx0 : x 0 = 0)
    (hx : ∀ t, x (t + 1) = x t - ((t : ℝ) + 1) ^ (-α) * g t) :
    (1 / (2 - α) + ((2 : ℝ) ^ (α - 1) - 1) / (1 - α)) / 2 * n ^ (2 - α) ≤
      regret (fun t b ↦ g t * b) x 0 n := by
  have hφ := one_div_two_sub_add_two_rpow_sub_one_div_pos hα0 hα1
  refine le_trans ?_ (mul_rpow_sub_rpow_div_le_regret hα0.le hα1 hg hx0 hx)
  generalize 1 / (2 - α) + ((2 : ℝ) ^ (α - 1) - 1) / (1 - α) = φ at hφ hn ⊢
  have hs : 0 < 1 - α := by linarith
  -- the second-order term `n ^ (1 - α) / (1 - α)` is at most half the first, since
  -- `2 ≤ (1 - α) φ(α) n`
  have h2 : 2 ≤ n * ((1 - α) * φ) := (div_le_iff₀ (by positivity)).mp hn
  have ha : 0 ≤ (n : ℝ) ^ (1 - α) := by positivity
  rw [show 2 - α = 1 - α + 1 by ring, rpow_add_one' (Nat.cast_nonneg n) (by linarith)]
  have h3 : (n : ℝ) ^ (1 - α) / (1 - α) ≤ φ / 2 * ((n : ℝ) ^ (1 - α) * n) := by
    rw [div_le_iff₀ hs]
    nlinarith [mul_le_mul_of_nonneg_left h2 ha]
  linarith

namespace OnlineLearner

variable {C : Type*}

/-- **The lower bound for the online subgradient descent learner with the rates `(t + 1) ^ (-α)`
on `ℝ`** [Ora, Theorem 5.4]. Let `0 < α < 1`, `φ(α) = 1 / (2 - α) + (2 ^ (α - 1) - 1) / (1 - α)`
and `n ≥ 2 / ((1 - α) φ(α))`. There are slopes `g t ∈ [-1, 1]`, hence convex and `1`-Lipschitz
linear losses `x ↦ g t * x`, on which the unprojected online subgradient descent learner on `ℝ`
from `0` with the rates `(t + 1) ^ (-α)` has a regret against `0` after `n` rounds of at least
`φ(α) / 2 * n ^ (2 - α)`, whatever the contexts. -/
theorem exists_div_two_mul_rpow_le_regret_run_onlineSubgradientDescent (hα0 : 0 < α)
    (hα1 : α < 1)
    (hn : 2 / ((1 - α) * (1 / (2 - α) + ((2 : ℝ) ^ (α - 1) - 1) / (1 - α))) ≤ n) :
    ∃ g : ℕ → ℝ, (∀ t, |g t| ≤ 1) ∧ ∀ c : ℕ → C,
      (1 / (2 - α) + ((2 : ℝ) ^ (α - 1) - 1) / (1 - α)) / 2 * n ^ (2 - α) ≤
        regret (fun t b ↦ g t * b)
          ((onlineSubgradientDescent Set.univ (fun t ↦ ((t : ℝ) + 1) ^ (-α)) 0).run c g) 0 n := by
  refine ⟨fun t ↦ if t < (n + 1) / 2 then -1 else 1, fun t ↦ by dsimp only; split_ifs <;> simp,
    fun c ↦ ?_⟩
  exact div_two_mul_rpow_le_regret hα0 hα1 hn (fun t ↦ rfl) (run_onlineSubgradientDescent_zero c _)
    fun t ↦ by rw [run_onlineSubgradientDescent_univ_succ, smul_eq_mul]

end OnlineLearner

end LMLExplore.OnlineLearning
