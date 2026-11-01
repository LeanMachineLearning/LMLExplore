/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.FixedBudget
public import LMLExplore.Identification.LowerBound
public import LMLExplore.InformationTheory.KullbackLeibler.BretagnolleHuber

/-!
# Lower bounds on the probability of error of identification algorithms

The probability of error of an identification algorithm `A` on the model `θ` of a task is the mass
`P_θ(error)` that the law `A.outputMeasure` of its output on `θ` gives to the answers that are not
correct for `θ`. Two models `θ` and `θ'` without a common correct answer cannot both be answered
correctly with high probability by an algorithm that collects little information to tell them
apart. The Bretagnolle–Huber inequality, applied to the laws of the output and combined with the
divergence decomposition at the stopping time, makes this quantitative:
`P_θ(error) + P_θ'(error) ≥ exp(-∑ a, E_θ[N_a(τ)] KL(ν_a(θ), ν_a(θ'))) / 2`, where `N_a(τ)` is the
number of pulls of the arm `a` before the stopping time `τ`. This is the basic lower bound of
fixed-budget identification, where `τ` is the budget `T`.

Writing `E_θ[N_a(τ)] = E_θ[τ] w_a` with the expected proportions of pulls `w`, an allocation, the
exponent is `E_θ[τ]` times the transportation cost `cost_θ(w, θ')`. Hence for every finite family
`Λ` of models without a common correct answer with `θ`, some `θ' ∈ Λ` satisfies
`max (P_θ(error), P_θ'(error)) ≥ exp(-E_θ[τ] sup_{w ∈ Δ_K} min_{θ' ∈ Λ} cost_θ(w, θ')) / 4`, a bound
that no longer depends on the algorithm except through `E_θ[τ]`. For a fixed-budget algorithm with
budget `T` and a single alternative `θ'`, this gives
`max (P_θ(error), P_θ'(error)) ≥ exp(-T max_a KL(ν_a(θ), ν_a(θ'))) / 4`.

## Main statements

* `IdentTask.exp_neg_sum_lintegral_pullCount_mul_klDiv_div_two_le`: the bound
  `P_θ(error) + P_θ'(error) ≥ exp(-∑ a, E_θ[N_a(τ)] KL(ν_a(θ), ν_a(θ'))) / 2` for an algorithm that
  stops almost surely on `θ`.
* `IdentTask.exists_exp_neg_mul_div_four_le_max`: the bound for a finite family of models, with
  the exponent `E_θ[τ] sup_{w ∈ Δ_K} min_{θ' ∈ Λ} cost_θ(w, θ')`.
* `LMLExplore.Identification.IsFixedBudget.exp_neg_sum_lintegral_pullCount_mul_klDiv_div_two_le`:
  the bound `P_θ(error) + P_θ'(error) ≥ exp(-∑ a, E_θ[N_a(T)] KL(ν_a(θ), ν_a(θ'))) / 2` for a
  fixed-budget algorithm with budget `T`.
* `LMLExplore.Identification.IsFixedBudget.exp_neg_mul_iSup_klDiv_div_four_le_max`: the bound
  `max (P_θ(error), P_θ'(error)) ≥ exp(-T max_a KL(ν_a(θ), ν_a(θ'))) / 4` for a fixed-budget
  algorithm with budget `T`.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Theorem 14.2.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Real

open scoped ENNReal

namespace LMLExplore.Identification

variable {α Θ ℐ 𝓨 : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {m𝓨 : MeasurableSpace 𝓨} [MeasurableSpace.CountablyGenerated 𝓨]
  {mℐ : MeasurableSpace ℐ} {task : IdentTask α Θ ℐ 𝓨} {A : IdentAlg Unit α 𝓨 ℐ} {θ θ' : Θ}

namespace IdentTask

/-- **Bretagnolle–Huber lower bound on the probability of error.** Let `A` stop almost surely on
the model `θ`, and let `θ'` be a model without a common correct answer with `θ`. If
`∑ a, E_θ[N_a(τ)] KL(ν_a(θ), ν_a(θ'))` is finite, where `N_a(τ)` is the number of pulls of the
arm `a` before the stopping time `τ`, then the probabilities of error of `A` on `θ` and `θ'` satisfy
`exp(-∑ a, E_θ[N_a(τ)] KL(ν_a(θ), ν_a(θ'))) / 2 ≤ P_θ(error) + P_θ'(error)`. -/
theorem exp_neg_sum_lintegral_pullCount_mul_klDiv_div_two_le
    (hstop : StopsAS A (stationaryEnv (task.ν θ)))
    (hdisj : Disjoint (task.correct θ) (task.correct θ')) (hc : MeasurableSet (task.correct θ))
    (h : ∑ a, (∫⁻ ω, (pullCount IT.action a (A.stoppingTime IT.obs IT.action IT.feedback ω).toNat
      ω : ℝ≥0∞) ∂(trajMeasure A.alg (stationaryEnv (task.ν θ)))) *
        klDiv (task.ν θ a) (task.ν θ' a) ≠ ∞) :
    exp (-(∑ a, (∫⁻ ω, (pullCount IT.action a
        (A.stoppingTime IT.obs IT.action IT.feedback ω).toNat ω : ℝ≥0∞)
          ∂(trajMeasure A.alg (stationaryEnv (task.ν θ)))) *
            klDiv (task.ν θ a) (task.ν θ' a)).toReal) / 2 ≤
      (A.outputMeasure (stationaryEnv (task.ν θ))).real (task.correct θ)ᶜ +
        (A.outputMeasure (stationaryEnv (task.ν θ'))).real (task.correct θ')ᶜ := by
  have h_kl := klDiv_outputMeasure_le A (task.ν θ) (task.ν θ') hstop
  -- Bretagnolle–Huber for the event "the answer is not correct for `θ`", whose complement is
  -- contained in the event "the answer is not correct for `θ'`".
  have h_bh := exp_neg_klDiv_div_two_le hc.compl (h_kl.trans_lt h.lt_top).ne
  rw [compl_compl] at h_bh
  refine le_trans ?_ (h_bh.trans (add_le_add_right
    (measureReal_mono hdisj.subset_compl_right (measure_ne_top _ _)) _))
  -- `gcongr` reduces the goal to `h_kl`, the finiteness side goal being `h`.
  gcongr

omit [DecidableEq α] in
/-- **Lower bound on the probability of error over a finite family of models** [D23]. Let `A` have
finite expected stopping time `E_θ[τ]` on the model `θ`, and let `Λ` be a nonempty finite family
of models, none of which has a common correct answer with `θ`. If the value
`D = sup_{w ∈ Δ_K} min_{θ' ∈ Λ} cost_θ(w, θ')` is finite, then some `θ' ∈ Λ` satisfies
`exp(-E_θ[τ] D) / 4 ≤ max (P_θ(error), P_θ'(error))`. For a fixed-budget algorithm with budget `T`,
`E_θ[τ] = T` (`IsFixedBudget.expectedStoppingTime_eq`). -/
theorem exists_exp_neg_mul_div_four_le_max {Λ : Finset Θ} (hΛ : Λ.Nonempty)
    (hdisj : ∀ θ' ∈ Λ, Disjoint (task.correct θ) (task.correct θ'))
    (hc : MeasurableSet (task.correct θ))
    (h : expectedStoppingTime A (stationaryEnv (task.ν θ)) ≠ ∞)
    (hD : ⨆ w ∈ simplex α, ⨅ θ' ∈ Λ, task.cost w θ θ' ≠ ∞) :
    ∃ θ' ∈ Λ, exp (-(expectedStoppingTime A (stationaryEnv (task.ν θ)) *
        ⨆ w ∈ simplex α, ⨅ θ' ∈ Λ, task.cost w θ θ').toReal) / 4 ≤
      max ((A.outputMeasure (stationaryEnv (task.ν θ))).real (task.correct θ)ᶜ)
        ((A.outputMeasure (stationaryEnv (task.ν θ'))).real (task.correct θ')ᶜ) := by
  classical
  have hstop : StopsAS A (stationaryEnv (task.ν θ)) := .of_expectedStoppingTime_ne_top h
  -- It suffices to find `θ' ∈ Λ` with `∑ a, E_θ[N_a(τ)] KL(ν_a(θ), ν_a(θ')) ≤ E_θ[τ] D`.
  suffices ∃ θ' ∈ Λ, ∑ a, (∫⁻ ω, (pullCount IT.action a
      (A.stoppingTime IT.obs IT.action IT.feedback ω).toNat ω : ℝ≥0∞)
        ∂(trajMeasure A.alg (stationaryEnv (task.ν θ)))) *
          klDiv (task.ν θ a) (task.ν θ' a) ≤ expectedStoppingTime A (stationaryEnv (task.ν θ)) *
            ⨆ w ∈ simplex α, ⨅ θ' ∈ Λ, task.cost w θ θ' by
    obtain ⟨θ', hθ', h_le⟩ := this
    have hED := ENNReal.mul_ne_top h hD
    have h_bh := exp_neg_sum_lintegral_pullCount_mul_klDiv_div_two_le hstop (hdisj θ' hθ') hc
      (h_le.trans_lt hED.lt_top).ne
    refine ⟨θ', hθ', ?_⟩
    have h_exp := exp_le_exp.2 (neg_le_neg (ENNReal.toReal_mono hED h_le))
    generalize (A.outputMeasure (stationaryEnv (task.ν θ))).real (task.correct θ)ᶜ = x
      at h_bh ⊢
    generalize (A.outputMeasure (stationaryEnv (task.ν θ'))).real (task.correct θ')ᶜ = y
      at h_bh ⊢
    linarith [le_max_left x y, le_max_right x y]
  rcases eq_or_ne (expectedStoppingTime A (stationaryEnv (task.ν θ))) 0 with h0 | h0
  · -- If `E_θ[τ] = 0`, every expected number of pulls vanishes.
    obtain ⟨θ', hθ'⟩ := hΛ
    refine ⟨θ', hθ', le_of_eq_of_le (Finset.sum_eq_zero fun a _ ↦ ?_) zero_le⟩
    rw [← expectedStoppingTime_mul_ofReal_expectedPullProportion h a, h0, zero_mul, zero_mul]
  -- Otherwise, the expected proportions of pulls `w` form an allocation, and the exponent is
  -- `E_θ[τ] cost_θ(w, θ')`; choose `θ' ∈ Λ` minimizing `cost_θ(w, ·)`.
  have hw := expectedPullProportion_mem_simplex h0 h
  obtain ⟨θ', hθ', hmin⟩ :=
    Λ.exists_min_image (task.cost (expectedPullProportion A (stationaryEnv (task.ν θ))) θ) hΛ
  refine ⟨θ', hθ', ?_⟩
  have h_sum : ∑ a, (∫⁻ ω, (pullCount IT.action a
      (A.stoppingTime IT.obs IT.action IT.feedback ω).toNat ω : ℝ≥0∞)
        ∂(trajMeasure A.alg (stationaryEnv (task.ν θ)))) *
          klDiv (task.ν θ a) (task.ν θ' a) = expectedStoppingTime A (stationaryEnv (task.ν θ)) *
            task.cost (expectedPullProportion A (stationaryEnv (task.ν θ))) θ θ' := by
    simp_rw [cost_def, Finset.mul_sum, ← mul_assoc,
      expectedStoppingTime_mul_ofReal_expectedPullProportion h]
  rw [h_sum]
  -- `cost_θ(w, θ') = min_{θ'' ∈ Λ} cost_θ(w, θ'') ≤ D`.
  gcongr
  exact le_iSup₂_of_le _ hw (le_iInf₂ hmin)

end IdentTask

/-! ### Fixed-budget algorithms -/

namespace IsFixedBudget

variable {T : ℕ}

/-- **Bretagnolle–Huber lower bound on the probability of error of a fixed-budget algorithm.** Let
`A` be a fixed-budget algorithm with budget `T`, and let `θ` and `θ'` be two models without a
common correct answer. If `∑ a, E_θ[N_a(T)] KL(ν_a(θ), ν_a(θ'))` is finite, where `N_a(T)` is the
number of pulls of the arm `a` in the first `T` rounds, then the probabilities of error of `A` on
`θ` and `θ'` satisfy `exp(-∑ a, E_θ[N_a(T)] KL(ν_a(θ), ν_a(θ'))) / 2 ≤ P_θ(error) + P_θ'(error)`. -/
theorem exp_neg_sum_lintegral_pullCount_mul_klDiv_div_two_le (hA : IsFixedBudget A T)
    (hdisj : Disjoint (task.correct θ) (task.correct θ')) (hc : MeasurableSet (task.correct θ))
    (h : ∑ a, (∫⁻ ω, (pullCount IT.action a T ω : ℝ≥0∞)
      ∂(trajMeasure A.alg (stationaryEnv (task.ν θ)))) * klDiv (task.ν θ a) (task.ν θ' a) ≠ ∞) :
    exp (-(∑ a, (∫⁻ ω, (pullCount IT.action a T ω : ℝ≥0∞)
        ∂(trajMeasure A.alg (stationaryEnv (task.ν θ)))) *
          klDiv (task.ν θ a) (task.ν θ' a)).toReal) / 2 ≤
      (A.outputMeasure (stationaryEnv (task.ν θ))).real (task.correct θ)ᶜ +
        (A.outputMeasure (stationaryEnv (task.ν θ'))).real (task.correct θ')ᶜ := by
  have hτ : ∀ ω, (A.stoppingTime IT.obs IT.action IT.feedback ω).toNat = T := fun ω ↦ by
    rw [hA.stoppingTime_eq, ENat.toNat_natCast]
  simpa only [hτ] using IdentTask.exp_neg_sum_lintegral_pullCount_mul_klDiv_div_two_le
    (hA.stopsAS _) hdisj hc (by simpa only [hτ] using h)

omit [Fintype α] [DecidableEq α] in
/-- **Fixed-budget lower bound for two models.** Let `A` be a fixed-budget algorithm with budget
`T`, and let `θ` and `θ'` be two models without a common correct answer, with arm laws at finite
divergences `KL(ν_a(θ), ν_a(θ'))`. Then one of the two models has probability of error at least
`exp(-T max_a KL(ν_a(θ), ν_a(θ'))) / 4`. -/
theorem exp_neg_mul_iSup_klDiv_div_four_le_max [Finite α] (hA : IsFixedBudget A T)
    (hdisj : Disjoint (task.correct θ) (task.correct θ')) (hc : MeasurableSet (task.correct θ))
    (h : ∀ a, klDiv (task.ν θ a) (task.ν θ' a) ≠ ∞) :
    exp (-(T * ⨆ a, klDiv (task.ν θ a) (task.ν θ' a)).toReal) / 4 ≤
      max ((A.outputMeasure (stationaryEnv (task.ν θ))).real (task.correct θ)ᶜ)
        ((A.outputMeasure (stationaryEnv (task.ν θ'))).real (task.correct θ')ᶜ) := by
  have := Fintype.ofFinite α
  have h_sup : ⨆ a, klDiv (task.ν θ a) (task.ν θ' a) ≠ ∞ := iSup_ne_top h
  -- The value `sup_{w ∈ Δ_K} cost_θ(w, θ')` of the family `{θ'}` is at most `max_a KL`.
  have hD : ⨆ w ∈ simplex α, ⨅ θ'' ∈ ({θ'} : Finset Θ), task.cost w θ θ'' ≤
      ⨆ a, klDiv (task.ν θ a) (task.ν θ' a) := by
    simp only [Finset.iInf_singleton]
    exact iSup₂_le fun w hw ↦ task.cost_le_iSup_klDiv hw θ θ'
  obtain ⟨θ'', hθ'', h_le⟩ := IdentTask.exists_exp_neg_mul_div_four_le_max
    (Finset.singleton_nonempty θ') (fun _ h ↦ Finset.mem_singleton.1 h ▸ hdisj) hc
    (hA.expectedStoppingTime_eq _ ▸ ENNReal.natCast_ne_top T) (hD.trans_lt h_sup.lt_top).ne
  rw [Finset.mem_singleton.1 hθ'', hA.expectedStoppingTime_eq] at h_le
  refine le_trans ?_ h_le
  -- `gcongr` closes the main goal with `hD`, leaving the finiteness of `T max_a KL`.
  gcongr
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top T) h_sup

end IsFixedBudget

end LMLExplore.Identification
