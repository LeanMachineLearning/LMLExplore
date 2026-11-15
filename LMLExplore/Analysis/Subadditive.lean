/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Fekete's lemma for superadditive sequences of extended reals

Mathlib's `Subadditive.tendsto_lim` is Fekete's lemma for a subadditive sequence `u : ℕ → ℝ`
with `u n / n` bounded below. This file proves it for a superadditive sequence of extended reals,
`u m + u n ≤ u (m + n)`, that takes the value `⊥` at no `n ≠ 0`, with no boundedness assumption:
`u n / n` tends to its supremum over `n ≥ 1`, which may be `⊤`.

## Main statements

* `EReal.tendsto_div_iSup_of_superadditive`: Fekete's lemma for superadditive sequences of
  extended reals.

## Implementation notes

The supremum `d` bounds `u n / n` for `n ≥ 1`. Conversely, for `m ≥ 1` and `n = q m + s` with
`q ≥ 1` and `s < m`, superadditivity gives `u n ≥ q u m + s u 1`. If `u m` is finite, so is `u 1`,
and this lower bound is `n u m / m` up to a constant, so that `u n / n` is eventually above any
`L < u m / m`. If `u m = ⊤`, then `u n = ⊤` for every `n ≥ m`.
-/

public section

open Filter Topology

namespace EReal

variable {u : ℕ → EReal}

/-- Superadditivity iterated: `(q + 1) • u m + s • u 1 ≤ u ((q + 1) * m + s)`. -/
private lemma nsmul_add_nsmul_le_of_superadditive (h : ∀ m n, u m + u n ≤ u (m + n))
    (m q s : ℕ) : (q + 1) • u m + s • u 1 ≤ u ((q + 1) * m + s) := by
  have h_mul (m q : ℕ) : (q + 1) • u m ≤ u ((q + 1) * m) := by
    induction q with
    | zero => simp
    | succ q ih =>
      calc (q + 1 + 1) • u m = (q + 1) • u m + u m := succ_nsmul _ _
      _ ≤ u ((q + 1) * m) + u m := by gcongr
      _ ≤ u ((q + 1) * m + m) := h _ _
      _ = u ((q + 1 + 1) * m) := by congr 1; ring
  cases s with
  | zero => simpa using h_mul m q
  | succ s =>
    calc (q + 1) • u m + (s + 1) • u 1 ≤ u ((q + 1) * m) + u ((s + 1) * 1) :=
        add_le_add (h_mul m q) (h_mul 1 s)
    _ ≤ u ((q + 1) * m + (s + 1)) := by rw [mul_one]; exact h _ _

/-- A value `⊤` of a superadditive sequence that takes the value `⊥` at no `n ≠ 0` carries
forward: if `u j = ⊤` and `j ≤ n`, then `u n = ⊤`. -/
private lemma eq_top_of_superadditive (hu : ∀ n ≠ 0, u n ≠ ⊥)
    (h : ∀ m n, u m + u n ≤ u (m + n)) {j n : ℕ} (hjt : u j = ⊤) (hjn : j ≤ n) : u n = ⊤ := by
  rcases hjn.eq_or_lt with rfl | hjn
  · exact hjt
  refine eq_top_iff.2 ?_
  calc ⊤ = u j + u (n - j) := by rw [hjt, top_add_of_ne_bot (hu _ (by omega))]
  _ ≤ u (j + (n - j)) := h _ _
  _ = u n := by rw [Nat.add_sub_cancel' hjn.le]

/-- The real inequality behind Fekete's lemma: if `n = (q + 1) m + s` with `s ≤ m`, then
`(r / m - C / n) n ≤ (q + 1) r + s a` for `C = m |a - r / m|`. -/
private lemma _root_.Real.fekete_bound {m n q s : ℕ} {r a : ℝ} (hm : (0 : ℝ) < m)
    (hn : (0 : ℝ) < n) (hn_eq : (q + 1) * m + s = n) (hs : s ≤ m) :
    (r / m - m * |a - r / m| / n) * n ≤ (q + 1) * r + s * a := by
  have hn_real : (n : ℝ) = (q + 1) * m + s := by exact_mod_cast hn_eq.symm
  have hs_real : (s : ℝ) ≤ m := by exact_mod_cast hs
  have h_eq : (r / m - m * |a - r / m| / n) * n = (q + 1) * r + s * (r / m) - m * |a - r / m| := by
    rw [sub_mul, div_mul_cancel₀ _ hn.ne', hn_real]
    field_simp
  rw [h_eq]
  nlinarith [mul_le_mul_of_nonneg_right hs_real (abs_nonneg (a - r / m)),
    mul_le_mul_of_nonneg_left (neg_abs_le (a - r / m)) (Nat.cast_nonneg (α := ℝ) s)]

/-- **Fekete's lemma** for superadditive sequences of extended reals: if
`u m + u n ≤ u (m + n)` for all `m, n` and `u n ≠ ⊥` for `n ≠ 0`, then `u n / n` tends to the
supremum of `u n / n` over `n ≥ 1`. The limit may be `⊤`. -/
theorem tendsto_div_iSup_of_superadditive (hu : ∀ n ≠ 0, u n ≠ ⊥)
    (h : ∀ m n, u m + u n ≤ u (m + n)) :
    Tendsto (fun n : ℕ ↦ u n / n) atTop (𝓝 (⨆ n : ℕ, u (n + 1) / ((n + 1 : ℕ) : EReal))) := by
  have h_pos {n : ℕ} (hn : n ≠ 0) : (0 : EReal) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine tendsto_order.2 ⟨fun L hL ↦ ?_, fun L hL ↦ ?_⟩
  swap
  · filter_upwards [eventually_ne_atTop 0] with n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact (le_iSup (fun k : ℕ ↦ u (k + 1) / ((k + 1 : ℕ) : EReal)) k).trans_lt hL
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hL
  -- the case `u (k + 1) = ⊤`: `u n / n = ⊤` for `n ≥ k + 1`
  by_cases hkt : u (k + 1) = ⊤
  · filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    rw [eq_top_of_superadditive hu h hkt hn,
      top_div_of_pos_ne_top (h_pos (by omega)) (natCast_ne_top n)]
    exact hk.trans_le le_top
  -- otherwise `u (k + 1)` and `u 1` are real
  have h1t : u 1 ≠ ⊤ := fun h1 ↦ hkt (eq_top_of_superadditive hu h h1 (by omega))
  obtain ⟨r, hr⟩ : ∃ r : ℝ, u (k + 1) = r := ⟨_, (EReal.coe_toReal hkt (hu _ k.succ_ne_zero)).symm⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, u 1 = a := ⟨_, (EReal.coe_toReal h1t (hu _ one_ne_zero)).symm⟩
  set m : ℕ := k + 1
  have hm0 : (0 : ℝ) < m := by positivity
  obtain ⟨x, hLx, hx⟩ := lt_iff_exists_real_btwn.1 hk
  rw [hr] at hx
  have hx : x < r / m := EReal.coe_lt_coe_iff.1 (hx.trans_eq (EReal.coe_div r m).symm)
  -- the real lower bound `r / m - C / n` of `u n / n` tends to `r / m > x`
  have h_lim : Tendsto (fun n : ℕ ↦ r / m - m * |a - r / m| / n) atTop (𝓝 (r / m)) := by
    simpa using (tendsto_const_nhds (x := r / m)).sub
      (_root_.tendsto_const_div_atTop_nhds_zero_nat (m * |a - r / m|))
  filter_upwards [eventually_ge_atTop m, h_lim.eventually (lt_mem_nhds hx)] with n hnm hxn
  have hn0 : n ≠ 0 := by omega
  refine hLx.trans (lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hxn) ?_)
  rw [le_div_iff_mul_le (h_pos hn0) (natCast_ne_top n)]
  -- write `n = (q + 1) * m + s` with `s < m`
  obtain ⟨q, hq⟩ : ∃ q, n / m = q + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.div_pos hnm (by omega)).ne'
  have hn_eq : (q + 1) * m + n % m = n := by rw [← hq, Nat.div_add_mod']
  have key := nsmul_add_nsmul_le_of_superadditive h m q (n % m)
  rw [hn_eq, hr, ha] at key
  refine le_trans ?_ key
  have := Real.fekete_bound (r := r) (a := a) hm0 (by exact_mod_cast Nat.pos_of_ne_zero hn0)
    hn_eq (Nat.mod_lt _ (by omega)).le
  simp only [nsmul_eq_mul]
  exact_mod_cast this

end EReal
