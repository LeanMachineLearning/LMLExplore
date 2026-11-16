/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.DifficultyRatio

/-!
# Minimax lower bounds on the probability of error at a fixed budget

An algorithm with budget `T` that is correct with probability at least `1 / 2` on a model `μ` errs
with probability at least `exp(-2 ∑ a, E_μ[N_a(T)] KL(ν_a(μ), ν_a(λ))) / 4` on every model `λ`
without a common correct answer with `μ`: by the data processing inequality for the event that the
output is correct for `μ`, `(1 - P_μ(error)) log (1 / P_λ(error)) ≤ ∑ a, E_μ[N_a(T)] KL + log 2`
(`LMLExplore.Identification.IdentTask.one_sub_errorProb_mul_neg_log_errorProb_le`). Unlike the
Bretagnolle–Huber bound on `P_μ(error) + P_λ(error)`
(`LMLExplore.Identification.IsFixedBudget.exp_neg_sum_lintegral_pullCount_mul_klDiv_div_two_le`),
this lower bound is on the probability of error at `λ` alone.

Let the models `λ j`, for the arms `j` of a nonempty set `s`, differ from `μ` on the arm `j` only.
The expected numbers of pulls `E_μ[N_j(T)]` sum to at most `T`, so for all positive weights `u j`
some arm `j ∈ s` has `E_μ[N_j(T)] ≤ T u j / ∑_{i ∈ s} u i`. With `u j = 1 / (H(λ j) k j)`, for a
difficulty function `H` and upper bounds `k j` on the divergences `KL(ν_j(μ), ν_j(λ j))`, the
probability of error at `λ j` is at least `exp(-2 T / (H(λ j) h)) / 4` with
`h = ∑_{j ∈ s} 1 / (H(λ j) k j)`. Hence one of the models `μ` and `λ j`, `j ∈ s`, has probability
of error at least `exp(-2 T / (H h)) / 4`, with `H` its difficulty: the algorithm cannot adapt to
the difficulties of all these models at once. This is the argument of [CL16, Theorem 2], where the
models are Bernoulli bandits and `H` is the complexity `∑_b Δ_b⁻²` of best arm identification; the
bandits of [CL16] are in `LMLExplore/Identification/Task/BestArm/MinimaxLowerBound.lean`. It is the
non-asymptotic counterpart of the lower bound from alternatives along the coordinates
[D23, Corollary 4] (`LMLExplore.Identification.IdentTask.sum_inv_le_iSup_asymptoticRatio`).

## Main statements

* `LMLExplore.Identification.IsFixedBudget.exp_neg_two_mul_div_four_le_measureReal`: if
  `P_μ(error) ≤ 1 / 2`, then `P_λ(error) ≥ exp(-2 x) / 4` for every
  `x ≥ ∑ a, E_μ[N_a(T)] KL(ν_a(μ), ν_a(λ))`.
* `LMLExplore.Identification.IsFixedBudget.exists_exp_neg_div_four_le_measureReal`: one of the
  models `μ` and `λ j`, `j ∈ s`, has probability of error at least `exp(-2 T / (H h)) / 4`
  [CL16, Theorem 2].

## Implementation notes

[CL16] bounds `P_λ(error)` below by a change of measure restricted to an event on which the
empirical log-likelihood ratios concentrate, which costs a term `2 √(T log (6 T K))` in the
exponent and the factor `1 / 6`. The data processing inequality gives the exponent `2 x` and the
factor `1 / 4` with no condition on `T`.

## References

* [CL16] A. Carpentier and A. Locatelli, *Tight (lower) bounds for the fixed budget best arm
  identification bandit problem*, COLT 2016.
* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023.
-/

public section

open MeasureTheory InformationTheory Learning Real

open scoped ENNReal

namespace LMLExplore.Identification.IsFixedBudget

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {m𝓨 : MeasurableSpace 𝓨} [MeasurableSpace.CountablyGenerated 𝓨]
  {mℐ : MeasurableSpace ℐ} {task : IdentTask α Θ ℐ 𝓨} {A : IdentAlg Unit α 𝓨 ℐ} {T : ℕ}

/-- **Lower bound on the probability of error at an alternative.** Let `A` be a fixed-budget
algorithm with budget `T`, and `θ`, `θ'` two models without a common correct answer. If `A` errs
with probability at most `1 / 2` on `θ`, then it errs with probability at least `exp(-2 x) / 4` on
`θ'`, for every `x ≥ 0` with `∑ a, E_θ[N_a(T)] KL(ν_a(θ), ν_a(θ')) ≤ x`, where `N_a(T)` is the
number of pulls of the arm `a` in the first `T` rounds. -/
theorem exp_neg_two_mul_div_four_le_measureReal (hA : IsFixedBudget A T) {θ θ' : Θ}
    (hdisj : Disjoint (task.correct θ) (task.correct θ'))
    (herr : (A.outputMeasure (Environment.bandit (task.ν θ))).real (task.correct θ)ᶜ ≤ 1 / 2)
    {x : ℝ} (hx₀ : 0 ≤ x)
    (hx : ∑ a, (∫⁻ ω, (pullCount IT.action a T ω : ℝ≥0∞)
      ∂(trajMeasure A.alg (Environment.bandit (task.ν θ)))) * klDiv (task.ν θ a) (task.ν θ' a) ≤
        ENNReal.ofReal x) :
    exp (-(2 * x)) / 4 ≤
      (A.outputMeasure (Environment.bandit (task.ν θ'))).real (task.correct θ')ᶜ := by
  have h := task.one_sub_errorProb_mul_neg_log_errorProb_le (𝒜 := fun _ ↦ A) hA hdisj
  simp only [IdentTask.errorProb_def] at h
  rw [measureReal_def] at herr ⊢
  set e := A.outputMeasure (Environment.bandit (task.ν θ)) (task.correct θ)ᶜ
  set e' := A.outputMeasure (Environment.bandit (task.ν θ')) (task.correct θ')ᶜ
  set L := (-ENNReal.log e').toENNReal
  -- Since `1 - P_θ(error) ≥ 1 / 2`, `log (1 / P_θ'(error)) ≤ 2 (x + log 2)`.
  have he : e ≤ 2⁻¹ :=
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by norm_num)).1
      (herr.trans_eq (by norm_num))
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hL : L ≤ ENNReal.ofReal (2 * (x + Real.log 2)) := by
    have h1 : 2⁻¹ * L ≤ ENNReal.ofReal (x + Real.log 2) := by
      rw [ENNReal.ofReal_add hx₀ hlog2]
      calc 2⁻¹ * L ≤ (1 - e) * L := by
            gcongr
            calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
              _ ≤ 1 - e := tsub_le_tsub_left he 1
        _ ≤ _ := h.trans (add_le_add_left hx _)
    calc L = 2 * (2⁻¹ * L) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      _ ≤ 2 * ENNReal.ofReal (x + Real.log 2) := by gcongr
      _ = ENNReal.ofReal (2 * (x + Real.log 2)) := by
          rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
  -- The probability of error at `θ'` is positive, since `log (1 / P_θ'(error))` is finite.
  have he'0 : e' ≠ 0 := by
    rintro he'
    have := hL.trans_lt ENNReal.ofReal_lt_top
    simp [L, he'] at this
  have he'_top : e' ≠ ∞ := measure_ne_top _ _
  have hq : 0 < e'.toReal := ENNReal.toReal_pos he'0 he'_top
  rw [show L = ENNReal.ofReal (-Real.log e'.toReal) by
    simp only [L, ENNReal.log_pos_real he'0 he'_top, ← EReal.coe_neg, EReal.real_coe_toENNReal],
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hL
  -- Hence `P_θ'(error) ≥ exp(-2 x - 2 log 2) = exp(-2 x) / 4`.
  have h4 : exp (2 * Real.log 2) = 4 := by
    rw [mul_comm, Real.exp_mul, Real.exp_log two_pos]
    norm_num
  calc exp (-(2 * x)) / 4 = exp (-(2 * (x + Real.log 2))) := by
        rw [← h4, ← Real.exp_sub]
        ring_nf
    _ ≤ exp (Real.log e'.toReal) := Real.exp_le_exp.2 (by linarith)
    _ = e'.toReal := Real.exp_log hq

omit [Fintype α] [DecidableEq α] in
/-- **Minimax lower bound on the probability of error at a fixed budget** [CL16, Theorem 2]. Let
`A` be a fixed-budget algorithm with budget `T`, `μ` a model, `s` a nonempty set of arms and, for
every arm `j ∈ s`, `λ j` a model without a common correct answer with `μ` whose arms other than
`j` have the same laws as those of `μ`. Let `H` be a difficulty function, nonnegative at `μ` and
positive at the models `λ j`, and `k j > 0` an upper bound on `KL(ν_j(μ), ν_j(λ j))` for
`j ∈ s`. Then one of the models `θ` among `μ` and the `λ j`, `j ∈ s`, satisfies
`exp(-2 T / (H(θ) h)) / 4 ≤ P_θ(error)`, with `h = ∑_{j ∈ s} 1 / (H(λ j) k j)`.

[CL16] proves `exp(-60 T / (H(θ) h*) - 2 √(T log (6 T K))) / 6` for Bernoulli arms with means in
`[1 / 4, 3 / 4]`, where `h* = ∑_{j ∈ s} 1 / (Δ_j² H(λ j))`. With the paper's bound
`KL(ν_j(μ), ν_j(λ j)) ≤ 10 Δ_j²`, that is `k j = 10 Δ_j²`, this theorem gives `h = h* / 10` and the
bound `exp(-20 T / (H(θ) h*)) / 4`. -/
theorem exists_exp_neg_div_four_le_measureReal [Finite α] (hA : IsFixedBudget A T) {μ : Θ}
    {s : Finset α} (hs : s.Nonempty) {lam : α → Θ}
    (hdisj : ∀ j ∈ s, Disjoint (task.correct μ) (task.correct (lam j)))
    (hν : ∀ j ∈ s, ∀ b ≠ j, task.ν (lam j) b = task.ν μ b) {H : Θ → ℝ} (hHμ : 0 ≤ H μ)
    (hH : ∀ j ∈ s, 0 < H (lam j)) {k : α → ℝ} (hk₀ : ∀ j ∈ s, 0 < k j)
    (hk : ∀ j ∈ s, klDiv (task.ν μ j) (task.ν (lam j) j) ≤ ENNReal.ofReal (k j)) :
    ∃ θ ∈ insert μ (lam '' s), exp (-(2 * T / (H θ * ∑ j ∈ s, (H (lam j) * k j)⁻¹))) / 4 ≤
      (A.outputMeasure (Environment.bandit (task.ν θ))).real (task.correct θ)ᶜ := by
  classical
  have := Fintype.ofFinite α
  set h := ∑ j ∈ s, (H (lam j) * k j)⁻¹
  have hu (j : α) (hj : j ∈ s) : 0 < (H (lam j) * k j)⁻¹ :=
    inv_pos.2 (mul_pos (hH j hj) (hk₀ j hj))
  have hh : 0 < h := Finset.sum_pos hu hs
  by_cases herr : (A.outputMeasure (Environment.bandit (task.ν μ))).real (task.correct μ)ᶜ ≤ 1 / 2
  swap
  · -- If `A` errs with probability more than `1 / 2` on `μ`, then `μ` satisfies the bound.
    refine ⟨μ, Set.mem_insert _ _, ?_⟩
    have : exp (-(2 * T / (H μ * h))) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ 2 * (T : ℝ) / (H μ * h) := by positivity
      linarith)
    linarith
  -- Otherwise, some arm `j ∈ s` has `E_μ[N_j(T)] ≤ T u j / h` with `u j = 1 / (H(λ j) k j)`.
  have hsum : ∑ j ∈ s, ∫⁻ ω, (pullCount IT.action j T ω : ℝ≥0∞)
      ∂(trajMeasure A.alg (Environment.bandit (task.ν μ))) ≤
      ∑ j ∈ s, ENNReal.ofReal (T * (H (lam j) * k j)⁻¹ / h) := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun j hj ↦ by have := hu j hj; positivity,
      ← Finset.sum_div, ← Finset.mul_sum, mul_div_cancel_right₀ _ hh.ne', ENNReal.ofReal_natCast]
    calc ∑ j ∈ s, ∫⁻ ω, (pullCount IT.action j T ω : ℝ≥0∞)
          ∂(trajMeasure A.alg (Environment.bandit (task.ν μ)))
        ≤ ∑ j, ∫⁻ ω, (pullCount IT.action j T ω : ℝ≥0∞)
          ∂(trajMeasure A.alg (Environment.bandit (task.ν μ))) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ s)
      _ = T := by
          have := expectedStoppingTime_eq_sum_lintegral_pullCount
            (hA.stopsAS (Environment.bandit (task.ν μ)))
          simp only [hA.toNat_stoppingTime, hA.expectedStoppingTime_eq] at this
          exact this.symm
  obtain ⟨j, hj, hNj⟩ := ENNReal.exists_le_of_sum_le hs hsum
  refine ⟨lam j, Set.mem_insert_of_mem _ (Set.mem_image_of_mem _ hj), ?_⟩
  -- The divergence term is `E_μ[N_j(T)] KL(ν_j(μ), ν_j(λ j)) ≤ (T / (H(λ j) h))`.
  have hx₀ : 0 ≤ (T : ℝ) / (H (lam j) * h) := by have := hH j hj; positivity
  have hx : ∑ a, (∫⁻ ω, (pullCount IT.action a T ω : ℝ≥0∞)
      ∂(trajMeasure A.alg (Environment.bandit (task.ν μ)))) *
        klDiv (task.ν μ a) (task.ν (lam j) a) ≤ ENNReal.ofReal (T / (H (lam j) * h)) := by
    rw [Finset.sum_eq_single j (fun a _ ha ↦ by rw [hν j hj a ha, klDiv_self, mul_zero])
      (by simp)]
    calc (∫⁻ ω, (pullCount IT.action j T ω : ℝ≥0∞)
          ∂(trajMeasure A.alg (Environment.bandit (task.ν μ)))) *
            klDiv (task.ν μ j) (task.ν (lam j) j)
        ≤ ENNReal.ofReal (T * (H (lam j) * k j)⁻¹ / h) * ENNReal.ofReal (k j) :=
          mul_le_mul' hNj (hk j hj)
      _ = ENNReal.ofReal (T / (H (lam j) * h)) := by
          rw [← ENNReal.ofReal_mul (by have := hu j hj; positivity)]
          congr 1
          have := (hk₀ j hj).ne'
          have := (hH j hj).ne'
          field_simp
  calc exp (-(2 * T / (H (lam j) * h))) / 4 = exp (-(2 * (T / (H (lam j) * h)))) / 4 := by
        ring_nf
    _ ≤ _ := exp_neg_two_mul_div_four_le_measureReal hA (hdisj j hj) herr hx₀ hx

end LMLExplore.Identification.IsFixedBudget
