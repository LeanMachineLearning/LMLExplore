/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Ville's inequality

For a nonnegative supermartingale `f` indexed by `ℕ` and `c > 0`, Ville's inequality bounds the
probability that `f` ever reaches the level `c`: `μ {ω | ∃ n, c ≤ f n ω} ≤ μ[f 0] / c`. Applied to
exponential supermartingales such as `exp (λ S n - λ ^ 2 σ ^ 2 n / 2)`, it gives concentration
bounds that hold simultaneously for all times (confidence sequences), as used for self-normalized
bounds and the confidence sets of optimistic bandit algorithms.

The finite-horizon form is the supermartingale counterpart of Doob's maximal inequality
`MeasureTheory.maximal_ineq`, which Mathlib states for submartingales: for a nonnegative
supermartingale the bound is in terms of `μ[f 0]` instead of an integral of `f n`. Ville's
inequality is its limit as the horizon tends to infinity.

## Main results

* `MeasureTheory.Supermartingale.maximal_ineq`: for a nonnegative supermartingale `f`,
  `ε * μ {ω | ε ≤ max_{k ≤ n} f k ω} ≤ μ[f 0]`.
* `MeasureTheory.Supermartingale.measure_exists_le_le`: **Ville's inequality**, for `0 < c`,
  `μ {ω | ∃ n, c ≤ f n ω} ≤ μ[f 0] / c`.

## References

* J. Ville, *Étude critique de la notion de collectif*, Gauthier-Villars, 1939.
* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Theorem 3.9.
-/

public section

open Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace MeasureTheory.Supermartingale

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  [SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → ℝ}

/-- **Maximal inequality for nonnegative supermartingales**: if `f` is an almost everywhere
nonnegative supermartingale, then for all `ε : ℝ≥0` and every horizon `n`,
`ε * μ {ε ≤ max_{k ≤ n} f k} ≤ μ[f 0]`. This is the supermartingale counterpart of Doob's
maximal inequality `MeasureTheory.maximal_ineq`. -/
theorem maximal_ineq (hf : Supermartingale f 𝒢 μ) (hnonneg : ∀ n, 0 ≤ᵐ[μ] f n) (ε : ℝ≥0)
    (n : ℕ) :
    ε * μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ f k ω} ≤
      ENNReal.ofReal (μ[f 0]) := by
  -- `τ` is the first time in `[0, n]` at which `f` reaches `ε`, and `n` if there is none.
  set τ : Ω → WithTop ℕ := fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)
  have hτ : IsStoppingTime 𝒢 τ :=
    hf.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hτ_le (ω : Ω) : τ ω ≤ n := WithTop.coe_le_coe.2 (hittingBtwn_le ω)
  have hint : Integrable (stoppedValue f τ) μ := integrable_stoppedValue ℕ hτ hf.integrable hτ_le
  -- Optional stopping, applied to the submartingale `-f` and the stopping times `0 ≤ τ`.
  have hstop : μ[stoppedValue f τ] ≤ μ[f 0] := by
    have h := hf.neg.expected_stoppedValue_mono (isStoppingTime_const 𝒢 0) hτ
      (fun _ ↦ WithTop.coe_le_coe.2 (Nat.zero_le _)) hτ_le
    have hneg : stoppedValue (-f) τ = -stoppedValue f τ := by ext; simp [stoppedValue]
    rwa [stoppedValue_const, hneg, Pi.neg_apply, integral_neg', integral_neg', neg_le_neg_iff] at h
  have hnonneg_stop : 0 ≤ᵐ[μ] stoppedValue f τ := by
    filter_upwards [ae_all_iff.2 hnonneg] with ω hω using hω _
  calc ε * μ {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ f k ω}
      ≤ ε * μ {ω | (ε : ℝ≥0∞) ≤ ENNReal.ofReal (stoppedValue f τ ω)} := by
        -- On the event, `f` reaches `ε` before time `n`, hence at time `τ`.
        refine mul_le_mul_right (measure_mono fun ω hω ↦ ?_) _
        rw [Set.mem_ofPred_eq, le_sup'_iff] at hω
        obtain ⟨k, hk, hεk⟩ := hω
        have h : stoppedValue f τ ω ∈ {y : ℝ | ε ≤ y} :=
          stoppedValue_hittingBtwn_mem ⟨k, ⟨Nat.zero_le k, Nat.lt_succ_iff.1 (mem_range.1 hk)⟩, hεk⟩
        simpa using ENNReal.ofReal_le_ofReal h
    _ ≤ ∫⁻ ω, ENNReal.ofReal (stoppedValue f τ ω) ∂μ :=
        mul_meas_ge_le_lintegral₀ hint.aemeasurable.ennreal_ofReal _
    _ = ENNReal.ofReal (μ[stoppedValue f τ]) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnonneg_stop).symm
    _ ≤ ENNReal.ofReal (μ[f 0]) := ENNReal.ofReal_le_ofReal hstop

/-- **Ville's inequality**: if `f` is an almost everywhere nonnegative supermartingale, then for
`0 < c` the probability that `f` ever reaches `c` is at most `μ[f 0] / c`. -/
theorem measure_exists_le_le (hf : Supermartingale f 𝒢 μ) (hnonneg : ∀ n, 0 ≤ᵐ[μ] f n) {c : ℝ}
    (hc : 0 < c) :
    μ {ω | ∃ n, c ≤ f n ω} ≤ ENNReal.ofReal (μ[f 0] / c) := by
  lift c to ℝ≥0 using hc.le
  -- The event is the increasing union of the events `c ≤ max_{k ≤ n} f k`.
  have hset : {ω | ∃ n, (c : ℝ) ≤ f n ω} =
      ⋃ n, {ω | (c : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ f k ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, le_sup'_iff, mem_range]
    exact ⟨fun ⟨n, h⟩ ↦ ⟨n, n, Nat.lt_succ_self n, h⟩, fun ⟨_, k, _, h⟩ ↦ ⟨k, h⟩⟩
  have hmono : Monotone fun n ↦
      {ω | (c : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k ↦ f k ω} :=
    fun m n hmn ω (hω : (c : ℝ) ≤ _) ↦ hω.trans
      (sup'_mono _ (range_subset_range.2 (Nat.succ_le_succ hmn)) nonempty_range_add_one)
  rw [hset, hmono.measure_iUnion]
  refine iSup_le fun n ↦ ?_
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  rw [ENNReal.ofReal_div_of_pos hc, ENNReal.ofReal_coe_nnreal,
    ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl ENNReal.coe_ne_top), mul_comm]
  exact hf.maximal_ineq hnonneg c n

end MeasureTheory.Supermartingale
