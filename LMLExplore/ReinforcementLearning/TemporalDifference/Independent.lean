/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.ReinforcementLearning.TemporalDifference.MeanPath
public import LMLExplore.ReinforcementLearning.TemporalDifference.TDUpdate
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib
import LeanMachineLearning.ForMathlib.Probability.Independence.Basic
import LMLExplore.MeasureTheory.Function.L2Space
import LMLExplore.Probability.HasCondDistrib
import Mathlib.MeasureTheory.Integral.Prod
import LMLExplore.Probability.Process.Filtration
import LMLExplore.ReinforcementLearning.LearningRate

/-!
# TD(0) with independent observations

TD(0) with linear features `φ : 𝓢 → E` updates its parameter along one observed transition at a
time, `θ (t + 1) = θ t + α t d (θ t) (O t)`, where
`d θ (s, s') = (R (s, s') + γ ⟪φ s', θ⟫ - ⟪φ s, θ⟫) φ s` is the TD(0) direction of a transition
`(s, s')` with reward `R (s, s')` (`LMLExplore.ReinforcementLearning.tdUpdate`, with its
per-step moments in `LMLExplore.ReinforcementLearning.TemporalDifference.TDUpdate`). In the
i.i.d. observation model of [BRS18, §7], the transitions are drawn from `ν ⊗ₘ P`: the state from
an invariant law `ν` of the Markov kernel `P`, and the next state from `P`. The mean of `d θ` is
then the mean-path TD update `g θ` for the mean reward `s ↦ ∫ R (s, s') d(P s)`, so TD(0) is a
stochastic approximation of the mean-path TD of
`LMLExplore.ReinforcementLearning.TemporalDifference.MeanPath`, with noise of variance
`σ² = 𝔼 ‖d θ*‖²` at the zero `θ*` of `g`. This file proves the three finite-time bounds of
[BRS18, Theorem 2], which mirror those of stochastic gradient descent.

The theorems assume only what their proofs use: each observation `O t` has law `ν ⊗ₘ P` and is
independent of the current iterate `θ t`, whose initial value may be random with
`𝔼 ‖θ 0‖² < ∞`. This holds for a deterministic `θ 0` and mutually independent observations
(`LMLExplore.ReinforcementLearning.indepFun_iterate_of_iIndepFun`). An expectation at the random
iterate `θ t` is computed by freezing `θ t`, which is independent of `O t`, and integrating over
the transition at the fixed parameter.

## Main statements

* `LMLExplore.ReinforcementLearning.integral_norm_sub_sq_succ_le`: one step of TD(0) in
  expectation [BRS18, (16)],
  `𝔼 ‖θ* - θ (t + 1)‖² ≤ 𝔼 ‖θ* - θ t‖² - α t (2 (1 - γ) - 8 α t) 𝔼 ‖⟪φ, θ* - θ t⟫‖²_ν + 2 α t² σ²`.
* `LMLExplore.ReinforcementLearning.mul_sum_mul_integral_integral_sq_inner_sub_le`: its sum over
  `t < T`, for steps `0 ≤ α t ≤ (1 - γ) / 8`.
* `LMLExplore.ReinforcementLearning.integral_integral_sq_inner_sub_average_le`: for
  `T ≥ 64 / (1 - γ)²` and the step `1 / √T`, the average `θ_avg` of the first `T` iterates has
  `𝔼 ‖⟪φ, θ* - θ_avg⟫‖²_ν ≤ (𝔼 ‖θ* - θ 0‖² + 2 σ²) / (√T (1 - γ))` [BRS18, Theorem 2 (a)].
* `LMLExplore.ReinforcementLearning.integral_norm_sub_sq_le_exp_mul_add`: if
  `ω ‖θ‖² ≤ ‖⟪φ, θ⟫‖²_ν` with `ω > 0`, a constant step `a ≤ ω (1 - γ) / 8` gives
  `𝔼 ‖θ* - θ T‖² ≤ exp (-a (1 - γ) ω T) 𝔼 ‖θ* - θ 0‖² + 2 a σ² / ((1 - γ) ω)`
  [BRS18, Theorem 2 (b)].
* `LMLExplore.ReinforcementLearning.integral_norm_sub_sq_le_max_div`: under the same condition,
  the steps `β / (λ + t)` with `β = 2 / ((1 - γ) ω)` and `λ = 16 / ((1 - γ)² ω)` give
  `𝔼 ‖θ* - θ T‖² ≤ κ / (λ + T)` with
  `κ = max (8 σ² / ((1 - γ)² ω²)) (16 𝔼 ‖θ* - θ 0‖² / ((1 - γ)² ω))` [BRS18, Theorem 2 (c)].
* `LMLExplore.ReinforcementLearning.indepFun_iterate_of_iIndepFun`: from a deterministic `θ 0`, with
  mutually independent observations, `θ t` is independent of `O t`.

## References

* [J. Bhandari, D. Russo and R. Singal, *A finite time analysis of temporal difference learning
  with linear function approximation*, 2018][BRS18], §7
* [L. Bottou, F. E. Curtis and J. Nocedal, *Optimization methods for large-scale machine
  learning*, 2018][BCN18]
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal InnerProductSpace

namespace LMLExplore.ReinforcementLearning

variable {𝓢 E : Type*} {m𝓢 : MeasurableSpace 𝓢} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {φ : 𝓢 → E} {R : 𝓢 × 𝓢 → ℝ} {γ : ℝ≥0}

/-! ### TD(0) with independent observations -/

section Independent

variable [Finite 𝓢] [MeasurableSingletonClass 𝓢] {ν : Measure 𝓢} [IsProbabilityMeasure ν]
  {P : Kernel 𝓢 𝓢} [IsMarkovKernel P] [MeasurableSpace E] [BorelSpace E]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {θ : ℕ → Ω → E} {O : ℕ → Ω → 𝓢 × 𝓢} {α : ℕ → ℝ} {θ' : E}

omit [IsProbabilityMeasure ν] in
/-- The squared distance `θ ↦ ‖⟪φ, θ' - θ⟫‖²_ν` of the values is measurable. -/
private lemma measurable_integral_sq_inner_sub :
    Measurable fun x : E ↦ ∫ s, ⟪φ s, θ' - x⟫_ℝ ^ 2 ∂ν :=
  (StronglyMeasurable.integral_prod_right' (f := fun p : E × 𝓢 ↦ ⟪φ p.2, θ' - p.1⟫_ℝ ^ 2)
    (measurable_from_prod_countable_left fun s ↦
      (Continuous.measurable (by fun_prop))
      ).stronglyMeasurable).measurable

/-- **The iterates of TD(0) have second moments**: along `θ (t + 1) = θ t + α t d (θ t) (O t)`
with `AEMeasurable` observations, from an initial parameter with `𝔼 ‖θ 0‖² < ∞`, every iterate
is a.e.-measurable with `𝔼 ‖θ t‖² < ∞`. -/
private lemma aemeasurable_and_memLp_norm (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hθ : ∀ t x, θ (t + 1) x = θ t x + α t • tdUpdate φ R γ (θ t x) (O t x))
    (hθ₀ : AEMeasurable (θ 0) μ) (hθ₀' : MemLp (fun x ↦ ‖θ 0 x‖) 2 μ)
    (hO : ∀ t, AEMeasurable (O t) μ) (t : ℕ) :
    AEMeasurable (θ t) μ ∧ MemLp (fun x ↦ ‖θ t x‖) 2 μ := by
  obtain ⟨C, hC⟩ := Finite.exists_le fun o ↦ |R o|
  induction t with
  | zero => exact ⟨hθ₀, hθ₀'⟩
  | succ t ih =>
    have hfun : θ (t + 1) = fun x ↦ θ t x + α t • tdUpdate φ R γ (θ t x) (O t x) := funext (hθ t)
    have hm : AEMeasurable (θ (t + 1)) μ := by
      rw [hfun]
      exact (measurable_add_smul_tdUpdate (φ := φ) (R := R) (γ := γ) (α t)).comp_aemeasurable
        (ih.1.prodMk (hO t))
    refine ⟨hm, ?_⟩
    -- `‖θ (t + 1)‖ ≤ ‖θ t‖ + |α t| (C + (1 + γ) ‖θ t‖)`
    refine (((ih.2.const_mul (1 + |α t| * (1 + γ))).add (memLp_const (|α t| * C))).of_le
      hm.norm.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_))
    have hd := (norm_tdUpdate_le (R := R) (γ := γ) hφ (θ t x) (O t x)).trans
      (add_le_add_left (hC (O t x)) _)
    have hnn : 0 ≤ (1 + |α t| * (1 + γ)) * ‖θ t x‖ + |α t| * C :=
      add_nonneg (mul_nonneg (by positivity) (norm_nonneg _))
        (mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans (hC (O t x))))
    rw [Real.norm_of_nonneg (norm_nonneg _), Pi.add_apply, Real.norm_of_nonneg hnn, hθ]
    calc ‖θ t x + α t • tdUpdate φ R γ (θ t x) (O t x)‖
        ≤ ‖θ t x‖ + |α t| * ‖tdUpdate φ R γ (θ t x) (O t x)‖ := by
          grw [norm_add_le, norm_smul, Real.norm_eq_abs]
      _ ≤ ‖θ t x‖ + |α t| * ((1 + γ) * ‖θ t x‖ + C) := by
          grw [hd]
          rw [add_comm C]
      _ = (1 + |α t| * (1 + γ)) * ‖θ t x‖ + |α t| * C := by ring

omit [IsProbabilityMeasure μ] in
/-- **Independent observations are independent of the current iterate**: along
`θ (t + 1) = θ t + α t d (θ t) (O t)` from a deterministic `θ 0`, with mutually independent
measurable observations `O t`, the iterate `θ t` is independent of the observation `O t`. With
observations of law `ν ⊗ₘ P`, this is the i.i.d. observation model of [BRS18, §7]. -/
theorem indepFun_iterate_of_iIndepFun
    (hθ : ∀ t x, θ (t + 1) x = θ t x + α t • tdUpdate φ R γ (θ t x) (O t x)) {θ₀ : E}
    (hθ₀ : ∀ x, θ 0 x = θ₀) (hO : ∀ t, Measurable (O t)) (hind : iIndepFun O μ) (t : ℕ) :
    IndepFun (θ t) (O t) μ := by
  have h := measurable_tdUpdate_iterate (ℱ := Filtration.naturalLT O hO) hθ
    (funext hθ₀ ▸ measurable_const) (fun t ↦ Filtration.measurable_naturalLT hO t.lt_succ_self) t
  rw [Filtration.naturalLT_apply] at h
  -- `j ∈ Set.Iio t` is `j < t` by definition
  exact (hind.indepFun_of_measurable_iSup_comap hO (S := Set.Iio t) (lt_irrefl t) h).symm

/-- `𝔼 ‖⟪φ, θ' - θ t⟫‖²_ν < ∞` for an a.e.-measurable `θ t` with `𝔼 ‖θ t‖² < ∞`. -/
private lemma integrable_integral_sq_inner_sub (hφ : ∀ s, ‖φ s‖ ≤ 1) {X : Ω → E}
    (hX : AEMeasurable X μ) (hX' : MemLp (fun x ↦ ‖X x‖) 2 μ) :
    Integrable (fun x ↦ ∫ s, ⟪φ s, θ' - X x⟫_ℝ ^ 2 ∂ν) μ :=
  (integrable_norm_const_sub_sq hX hX' θ').mono'
    (measurable_integral_sq_inner_sub.comp_aemeasurable hX).aestronglyMeasurable
    (ae_of_all _ fun x ↦ by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)]
      exact integral_sq_inner_le_norm_sq hφ _)

/-- **One step of TD(0) with independent observations** [BRS18, (16)]: let `ν` be invariant,
`γ ≤ 1`, `‖φ s‖ ≤ 1` and `θ*` a zero of the mean-path TD update. Let the iterates follow
`θ (t + 1) = θ t + α t d (θ t) (O t)` from an a.e.-measurable `θ 0` with `𝔼 ‖θ 0‖² < ∞`, where
each observation `O t` has law `ν ⊗ₘ P` and is independent of the current iterate `θ t`. Then a
step of size `α t ≥ 0` satisfies
`𝔼 ‖θ* - θ (t + 1)‖² ≤ 𝔼 ‖θ* - θ t‖² - α t (2 (1 - γ) - 8 α t) 𝔼 ‖⟪φ, θ* - θ t⟫‖²_ν + 2 α t² σ²`,
with `σ² = 𝔼 ‖d θ*‖²` for a transition `(s, s') ∼ ν ⊗ₘ P`. -/
theorem integral_norm_sub_sq_succ_le [CompleteSpace E] (hP : P.Invariant ν)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hγ : γ ≤ 1)
    (hθ' : meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ θ' = 0)
    (hθ : ∀ t x, θ (t + 1) x = θ t x + α t • tdUpdate φ R γ (θ t x) (O t x))
    (hθ₀ : AEMeasurable (θ 0) μ) (hθ₀' : MemLp (fun x ↦ ‖θ 0 x‖) 2 μ)
    (hind : ∀ t, IndepFun (θ t) (O t) μ) (hO : ∀ t, HasLaw (O t) (ν ⊗ₘ P) μ) {t : ℕ}
    (hα : 0 ≤ α t) :
    ∫ x, ‖θ' - θ (t + 1) x‖ ^ 2 ∂μ ≤ ∫ x, ‖θ' - θ t x‖ ^ 2 ∂μ -
      α t * (2 * (1 - γ) - 8 * α t) * ∫ x, ∫ s, ⟪φ s, θ' - θ t x⟫_ℝ ^ 2 ∂ν ∂μ +
        2 * α t ^ 2 * ∫ o, ‖tdUpdate φ R γ θ' o‖ ^ 2 ∂(ν ⊗ₘ P) := by
  have hmom := aemeasurable_and_memLp_norm hφ hθ hθ₀ hθ₀' (fun t ↦ (hO t).aemeasurable)
  obtain ⟨hX, hX'⟩ := hmom t
  have hcd := (hind t).hasCondDistrib_const hX (hO t)
  set g : E × (𝓢 × 𝓢) → ℝ := fun p ↦ ‖θ' - (p.1 + α t • tdUpdate φ R γ p.1 p.2)‖ ^ 2 with hg
  have hgm : Measurable g :=
    (((measurable_add_smul_tdUpdate (α t)).const_sub θ').norm).pow_const 2
  have hint : Integrable (fun x ↦ g (θ t x, O t x)) μ := by
    simpa only [hg, ← hθ] using
      integrable_norm_const_sub_sq (hmom (t + 1)).1 (hmom (t + 1)).2 θ'
  -- freezing the iterate, which is independent of the observation
  obtain ⟨hGint, hGeq⟩ := hcd.integrable_and_integral_comp_prodMk_eq_of_ae_integral_eq
    (g := g) (G := fun y ↦ ∫ o, g (y, o) ∂(ν ⊗ₘ P)) hgm.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Kernel.const_apply]) hint
  have hN := integrable_norm_const_sub_sq hX hX' θ'
  have hD := integrable_integral_sq_inner_sub (ν := ν) (θ' := θ') hφ hX hX'
  have hA : Integrable (fun x ↦ ‖θ' - θ t x‖ ^ 2 -
      α t * (2 * (1 - γ) - 8 * α t) * ∫ s, ⟪φ s, θ' - θ t x⟫_ℝ ^ 2 ∂ν) μ :=
    hN.sub (hD.const_mul _)
  calc ∫ x, ‖θ' - θ (t + 1) x‖ ^ 2 ∂μ = ∫ x, g (θ t x, O t x) ∂μ := by simp only [hg, hθ]
    _ = ∫ x, ∫ o, g (θ t x, o) ∂(ν ⊗ₘ P) ∂μ := hGeq
    _ ≤ ∫ x, (‖θ' - θ t x‖ ^ 2 -
          α t * (2 * (1 - γ) - 8 * α t) * ∫ s, ⟪φ s, θ' - θ t x⟫_ℝ ^ 2 ∂ν +
            2 * α t ^ 2 * ∫ o, ‖tdUpdate φ R γ θ' o‖ ^ 2 ∂(ν ⊗ₘ P)) ∂μ :=
        integral_mono hGint (hA.add (integrable_const _)) fun x ↦
            integral_norm_sub_add_smul_tdUpdate_sq_le hP hφ hγ hθ' (θ t x) hα
    _ = _ := by
        rw [integral_add hA (integrable_const _),
          integral_sub hN (hD.const_mul _),
          integral_const_mul, integral_const, probReal_univ, one_smul]

/-- [BRS18, (17)]: a step of size `0 ≤ α t ≤ (1 - γ) / 8` satisfies
`𝔼 ‖θ* - θ (t + 1)‖² + α t (1 - γ) 𝔼 ‖⟪φ, θ* - θ t⟫‖²_ν ≤ 𝔼 ‖θ* - θ t‖² + 2 α t² σ²`. -/
private lemma integral_norm_sub_sq_succ_add_le [CompleteSpace E] (hP : P.Invariant ν)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hγ : γ ≤ 1)
    (hθ' : meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ θ' = 0)
    (hθ : ∀ t x, θ (t + 1) x = θ t x + α t • tdUpdate φ R γ (θ t x) (O t x))
    (hθ₀ : AEMeasurable (θ 0) μ) (hθ₀' : MemLp (fun x ↦ ‖θ 0 x‖) 2 μ)
    (hind : ∀ t, IndepFun (θ t) (O t) μ) (hO : ∀ t, HasLaw (O t) (ν ⊗ₘ P) μ) {t : ℕ}
    (hα : 0 ≤ α t) (hα' : α t ≤ (1 - γ) / 8) :
    ∫ x, ‖θ' - θ (t + 1) x‖ ^ 2 ∂μ +
        α t * (1 - γ) * ∫ x, ∫ s, ⟪φ s, θ' - θ t x⟫_ℝ ^ 2 ∂ν ∂μ ≤
      ∫ x, ‖θ' - θ t x‖ ^ 2 ∂μ + 2 * α t ^ 2 * ∫ o, ‖tdUpdate φ R γ θ' o‖ ^ 2 ∂(ν ⊗ₘ P) := by
  have h := integral_norm_sub_sq_succ_le hP hφ hγ hθ' hθ hθ₀ hθ₀' hind hO hα
  have hy : 0 ≤ ∫ x, ∫ s, ⟪φ s, θ' - θ t x⟫_ℝ ^ 2 ∂ν ∂μ :=
    integral_nonneg fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  nlinarith [mul_nonneg (mul_nonneg hα (by linarith : (0 : ℝ) ≤ 1 - γ - 8 * α t)) hy]

/-- [BRS18, (18)]: if moreover `ω ‖θ‖² ≤ ‖⟪φ, θ⟫‖²_ν` for every `θ`, a step of size
`0 ≤ α t ≤ (1 - γ) / 8` satisfies
`𝔼 ‖θ* - θ (t + 1)‖² ≤ (1 - α t (1 - γ) ω) 𝔼 ‖θ* - θ t‖² + 2 α t² σ²`. -/
private lemma integral_norm_sub_sq_succ_le_mul_add [CompleteSpace E] (hP : P.Invariant ν)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hγ : γ ≤ 1)
    (hθ' : meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ θ' = 0)
    (hθ : ∀ t x, θ (t + 1) x = θ t x + α t • tdUpdate φ R γ (θ t x) (O t x))
    (hθ₀ : AEMeasurable (θ 0) μ) (hθ₀' : MemLp (fun x ↦ ‖θ 0 x‖) 2 μ)
    (hind : ∀ t, IndepFun (θ t) (O t) μ) (hO : ∀ t, HasLaw (O t) (ν ⊗ₘ P) μ) {ω : ℝ}
    (hω : ∀ θ, ω * ‖θ‖ ^ 2 ≤ ∫ s, ⟪φ s, θ⟫_ℝ ^ 2 ∂ν) {t : ℕ} (hα : 0 ≤ α t)
    (hα' : α t ≤ (1 - γ) / 8) :
    ∫ x, ‖θ' - θ (t + 1) x‖ ^ 2 ∂μ ≤ (1 - α t * (1 - γ) * ω) * ∫ x, ‖θ' - θ t x‖ ^ 2 ∂μ +
      2 * α t ^ 2 * ∫ o, ‖tdUpdate φ R γ θ' o‖ ^ 2 ∂(ν ⊗ₘ P) := by
  have h := integral_norm_sub_sq_succ_add_le hP hφ hγ hθ' hθ hθ₀ hθ₀' hind hO hα hα'
  obtain ⟨hX, hX'⟩ := aemeasurable_and_memLp_norm hφ hθ hθ₀ hθ₀' (fun t ↦ (hO t).aemeasurable) t
  have hy : ω * ∫ x, ‖θ' - θ t x‖ ^ 2 ∂μ ≤ ∫ x, ∫ s, ⟪φ s, θ' - θ t x⟫_ℝ ^ 2 ∂ν ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono ((integrable_norm_const_sub_sq hX hX' θ').const_mul ω)
      (integrable_integral_sq_inner_sub hφ hX hX') fun x ↦ hω _
  have hγ₁ : (0 : ℝ) ≤ 1 - γ := by linarith [γ.coe_nonneg]
  nlinarith [mul_le_mul_of_nonneg_left hy (mul_nonneg hα hγ₁)]

omit [MeasurableSpace E] [BorelSpace E] in
/-- If `ω ‖θ‖² ≤ ‖⟪φ, θ⟫‖²_ν ≤ ‖θ‖²` for every `θ` with `ω > 1`, then `E` is trivial. -/
private lemma eq_zero_of_one_lt (hφ : ∀ s, ‖φ s‖ ≤ 1) {ω : ℝ}
    (hω : ∀ θ, ω * ‖θ‖ ^ 2 ≤ ∫ s, ⟪φ s, θ⟫_ℝ ^ 2 ∂ν) (h1 : 1 < ω) (v : E) : v = 0 := by
  have h := (hω v).trans (integral_sq_inner_le_norm_sq hφ v)
  have hv : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hv (sq_nonneg _)))

omit [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure μ] in
/-- If `ω ‖θ‖² ≤ ‖⟪φ, θ⟫‖²_ν ≤ ‖θ‖²` for every `θ` with `ω > 1`, every random parameter is at
distance `0` from `θ'`. -/
private lemma integral_norm_sub_sq_eq_zero_of_one_lt (hφ : ∀ s, ‖φ s‖ ≤ 1) {ω : ℝ}
    (hω : ∀ θ, ω * ‖θ‖ ^ 2 ≤ ∫ s, ⟪φ s, θ⟫_ℝ ^ 2 ∂ν) (h1 : 1 < ω) (X : Ω → E) :
    ∫ x, ‖θ' - X x‖ ^ 2 ∂μ = 0 := by
  simp [eq_zero_of_one_lt hφ hω h1 (θ' - _)]

/-- The step `1 / √T` is at most `c / 8` when `T ≥ 64 / c²`. -/
private lemma one_div_sqrt_le {c T : ℝ} (hc : 0 < c) (hT : 64 / c ^ 2 ≤ T) : 1 / √T ≤ c / 8 := by
  have hT' : 0 < T := (by positivity : (0 : ℝ) < 64 / c ^ 2).trans_le hT
  have h8 : 8 ≤ c * √T := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [mul_pow, Real.sq_sqrt hT'.le]
    rw [div_le_iff₀ (by positivity)] at hT
    linarith
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 hT') (by norm_num)]
  linarith

/-- **The weighted sum of the value errors of TD(0) with independent observations**: under the
hypotheses of `integral_norm_sub_sq_succ_le`, steps `0 ≤ α t ≤ (1 - γ) / 8` for `t < T` give
`(1 - γ) ∑_{t < T} α t 𝔼 ‖⟪φ, θ* - θ t⟫‖²_ν ≤ 𝔼 ‖θ* - θ 0‖² - 𝔼 ‖θ* - θ T‖² + 2 σ² ∑_{t < T} α t²`,
with `σ² = 𝔼 ‖d θ*‖²` for a transition `(s, s') ∼ ν ⊗ₘ P`. -/
theorem mul_sum_mul_integral_integral_sq_inner_sub_le [CompleteSpace E] (hP : P.Invariant ν)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hγ : γ ≤ 1)
    (hθ' : meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ θ' = 0)
    (hθ : ∀ t x, θ (t + 1) x = θ t x + α t • tdUpdate φ R γ (θ t x) (O t x))
    (hθ₀ : AEMeasurable (θ 0) μ) (hθ₀' : MemLp (fun x ↦ ‖θ 0 x‖) 2 μ)
    (hind : ∀ t, IndepFun (θ t) (O t) μ) (hO : ∀ t, HasLaw (O t) (ν ⊗ₘ P) μ) {T : ℕ}
    (hα : ∀ t < T, 0 ≤ α t) (hα' : ∀ t < T, α t ≤ (1 - γ) / 8) :
    (1 - γ) * ∑ t ∈ range T, α t * ∫ x, ∫ s, ⟪φ s, θ' - θ t x⟫_ℝ ^ 2 ∂ν ∂μ ≤
      ∫ x, ‖θ' - θ 0 x‖ ^ 2 ∂μ - ∫ x, ‖θ' - θ T x‖ ^ 2 ∂μ +
        2 * (∫ o, ‖tdUpdate φ R γ θ' o‖ ^ 2 ∂(ν ⊗ₘ P)) * ∑ t ∈ range T, α t ^ 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h := integral_norm_sub_sq_succ_add_le hP hφ hγ hθ' hθ hθ₀ hθ₀' hind hO
      (hα T T.lt_succ_self) (hα' T T.lt_succ_self)
    have ih := ih (fun t ht ↦ hα t (ht.trans T.lt_succ_self))
      (fun t ht ↦ hα' t (ht.trans T.lt_succ_self))
    rw [sum_range_succ, sum_range_succ]
    nlinarith

/-- **The `1 / √T` rate of TD(0) with averaging** [BRS18, Theorem 2 (a)]: let `ν` be invariant,
`γ < 1`, `‖φ s‖ ≤ 1` and `θ*` a zero of the mean-path TD update. Let the iterates follow
`θ (t + 1) = θ t + α t d (θ t) (O t)` from an a.e.-measurable `θ 0` with `𝔼 ‖θ 0‖² < ∞`, where
each observation `O t` has law `ν ⊗ₘ P` and is independent of the current iterate `θ t`. For
`T ≥ 64 / (1 - γ)²` and the constant step `α t = 1 / √T` for `t < T`, the average
`θ_avg = T⁻¹ ∑_{t < T} θ t` satisfies
`𝔼 ‖⟪φ, θ* - θ_avg⟫‖²_ν ≤ (𝔼 ‖θ* - θ 0‖² + 2 σ²) / (√T (1 - γ))`, with `σ² = 𝔼 ‖d θ*‖²` for a
transition `(s, s') ∼ ν ⊗ₘ P`. -/
theorem integral_integral_sq_inner_sub_average_le [CompleteSpace E] (hP : P.Invariant ν)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hγ : γ < 1)
    (hθ' : meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ θ' = 0)
    (hθ : ∀ t x, θ (t + 1) x = θ t x + α t • tdUpdate φ R γ (θ t x) (O t x))
    (hθ₀ : AEMeasurable (θ 0) μ) (hθ₀' : MemLp (fun x ↦ ‖θ 0 x‖) 2 μ)
    (hind : ∀ t, IndepFun (θ t) (O t) μ) (hO : ∀ t, HasLaw (O t) (ν ⊗ₘ P) μ) {T : ℕ}
    (hT : 64 / (1 - (γ : ℝ)) ^ 2 ≤ T) (hα : ∀ t < T, α t = 1 / √T) :
    ∫ x, ∫ s, ⟪φ s, θ' - (T : ℝ)⁻¹ • ∑ t ∈ range T, θ t x⟫_ℝ ^ 2 ∂ν ∂μ ≤
      (∫ x, ‖θ' - θ 0 x‖ ^ 2 ∂μ + 2 * ∫ o, ‖tdUpdate φ R γ θ' o‖ ^ 2 ∂(ν ⊗ₘ P)) /
        (√T * (1 - γ)) := by
  set σ2 := ∫ o, ‖tdUpdate φ R γ θ' o‖ ^ 2 ∂(ν ⊗ₘ P) with hσ2
  have hγ' : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hT' : (0 : ℝ) < T := (by positivity : (0 : ℝ) < 64 / (1 - γ) ^ 2).trans_le hT
  have hTn : 0 < T := by exact_mod_cast hT'
  have ha' := one_div_sqrt_le hγ' hT
  set a := 1 / √T with ha
  have hsT : 0 < √T := Real.sqrt_pos.2 hT'
  have hsT2 : √T ^ 2 = T := Real.sq_sqrt hT'.le
  have hsum := mul_sum_mul_integral_integral_sq_inner_sub_le hP hφ hγ.le hθ' hθ hθ₀ hθ₀' hind
    hO (T := T) (fun t ht ↦ by rw [hα t ht]; positivity) (fun t ht ↦ by rw [hα t ht]; exact ha')
  have hmom := aemeasurable_and_memLp_norm hφ hθ hθ₀ hθ₀' (fun t ↦ (hO t).aemeasurable)
  have hD : ∀ t, Integrable (fun x ↦ ∫ s, ⟪φ s, θ' - θ t x⟫_ℝ ^ 2 ∂ν) μ := fun t ↦
    integrable_integral_sq_inner_sub hφ (hmom t).1 (hmom t).2
  -- Jensen's inequality for the average, pointwise
  have hJ : ∫ x, ∫ s, ⟪φ s, θ' - (T : ℝ)⁻¹ • ∑ t ∈ range T, θ t x⟫_ℝ ^ 2 ∂ν ∂μ ≤
      (T : ℝ)⁻¹ * ∑ t ∈ range T, ∫ x, ∫ s, ⟪φ s, θ' - θ t x⟫_ℝ ^ 2 ∂ν ∂μ := by
    rw [← integral_finsetSum _ fun t _ ↦ hD t, ← integral_const_mul]
    exact integral_mono_of_nonneg (ae_of_all _ fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _)
      ((integrable_finsetSum _ fun t _ ↦ hD t).const_mul _)
      (ae_of_all _ fun x ↦ integral_sq_inner_sub_smul_sum_le (fun t ↦ θ t x) hTn)
  have hxT : 0 ≤ ∫ x, ‖θ' - θ T x‖ ^ 2 ∂μ := integral_nonneg fun _ ↦ sq_nonneg _
  refine hJ.trans ?_
  set S := ∑ t ∈ range T, ∫ x, ∫ s, ⟪φ s, θ' - θ t x⟫_ℝ ^ 2 ∂ν ∂μ
  have hsA : ∑ t ∈ range T, α t * ∫ x, ∫ s, ⟪φ s, θ' - θ t x⟫_ℝ ^ 2 ∂ν ∂μ = a * S := by
    rw [mul_sum]
    exact sum_congr rfl fun t ht ↦ by rw [hα t (mem_range.1 ht)]
  have hsB : ∑ t ∈ range T, α t ^ 2 = 1 := by
    rw [sum_congr rfl fun t ht ↦ by rw [hα t (mem_range.1 ht)], sum_const, card_range,
      nsmul_eq_mul, ha, div_pow, one_pow, hsT2]
    field_simp
  rw [hsA, hsB, ← hσ2] at hsum
  have hS : (1 - γ) * S ≤ √T * (∫ x, ‖θ' - θ 0 x‖ ^ 2 ∂μ + 2 * σ2) :=
    calc (1 - γ) * S = √T * ((1 - γ) * (a * S)) := by rw [ha]; field_simp
      _ ≤ √T * (∫ x, ‖θ' - θ 0 x‖ ^ 2 ∂μ - ∫ x, ‖θ' - θ T x‖ ^ 2 ∂μ + 2 * σ2 * 1) :=
        mul_le_mul_of_nonneg_left hsum hsT.le
      _ ≤ √T * (∫ x, ‖θ' - θ 0 x‖ ^ 2 ∂μ + 2 * σ2) :=
        mul_le_mul_of_nonneg_left (by linarith) hsT.le
  rw [inv_mul_eq_div, div_le_div_iff₀ hT' (by positivity)]
  linear_combination √T * hS + (∫ x, ‖θ' - θ 0 x‖ ^ 2 ∂μ + 2 * σ2) * hsT2

/-- **The linear rate of TD(0) with a constant step** [BRS18, Theorem 2 (b)]: let `ν` be invariant,
`γ < 1`, `‖φ s‖ ≤ 1` and `θ*` a zero of the mean-path TD update. Let the iterates follow
`θ (t + 1) = θ t + α t d (θ t) (O t)` from an a.e.-measurable `θ 0` with `𝔼 ‖θ 0‖² < ∞`, where
each observation `O t` has law `ν ⊗ₘ P` and is independent of the current iterate `θ t`. If
moreover `ω ‖θ‖² ≤ ‖⟪φ, θ⟫‖²_ν` for every `θ`, with `ω > 0`, then a constant step
`0 ≤ α t = a ≤ ω (1 - γ) / 8` for `t < T` gives
`𝔼 ‖θ* - θ T‖² ≤ exp (-a (1 - γ) ω T) 𝔼 ‖θ* - θ 0‖² + 2 a σ² / ((1 - γ) ω)`, with
`σ² = 𝔼 ‖d θ*‖²` for a transition `(s, s') ∼ ν ⊗ₘ P`. -/
theorem integral_norm_sub_sq_le_exp_mul_add [CompleteSpace E] (hP : P.Invariant ν)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hγ : γ < 1)
    (hθ' : meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ θ' = 0)
    (hθ : ∀ t x, θ (t + 1) x = θ t x + α t • tdUpdate φ R γ (θ t x) (O t x))
    (hθ₀ : AEMeasurable (θ 0) μ) (hθ₀' : MemLp (fun x ↦ ‖θ 0 x‖) 2 μ)
    (hind : ∀ t, IndepFun (θ t) (O t) μ) (hO : ∀ t, HasLaw (O t) (ν ⊗ₘ P) μ) {ω : ℝ}
    (hω₀ : 0 < ω) (hω : ∀ θ, ω * ‖θ‖ ^ 2 ≤ ∫ s, ⟪φ s, θ⟫_ℝ ^ 2 ∂ν) {T : ℕ} {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ ω * (1 - γ) / 8) (hα : ∀ t < T, α t = a) :
    ∫ x, ‖θ' - θ T x‖ ^ 2 ∂μ ≤ Real.exp (-(a * (1 - γ) * ω * T)) * ∫ x, ‖θ' - θ 0 x‖ ^ 2 ∂μ +
      2 * a * (∫ o, ‖tdUpdate φ R γ θ' o‖ ^ 2 ∂(ν ⊗ₘ P)) / ((1 - γ) * ω) := by
  set σ2 := ∫ o, ‖tdUpdate φ R γ θ' o‖ ^ 2 ∂(ν ⊗ₘ P) with hσ2
  have hγ' : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hσ0 : 0 ≤ σ2 := integral_nonneg fun _ ↦ sq_nonneg _
  have hx0 : 0 ≤ ∫ x, ‖θ' - θ 0 x‖ ^ 2 ∂μ := integral_nonneg fun _ ↦ sq_nonneg _
  set b := 2 * a * σ2 / ((1 - γ) * ω) with hb
  have hb0 : 0 ≤ b := by positivity
  rcases le_or_gt ω 1 with hω1 | hω1
  swap
  · -- if `ω > 1`, then `E` is trivial
    rw [integral_norm_sub_sq_eq_zero_of_one_lt hφ hω hω1]
    positivity
  set q := 1 - a * (1 - γ) * ω with hq
  have ha1 : a ≤ (1 - γ) / 8 :=
    ha'.trans (div_le_div_of_nonneg_right (mul_le_of_le_one_left hγ'.le hω1) (by norm_num))
  have hq0 : 0 ≤ q := by
    have h1 : a * (1 - γ) * ω ≤ a * 1 * 1 := by
      gcongr
      linarith [γ.coe_nonneg]
    rw [hq]
    linarith [γ.coe_nonneg]
  have hqb : q * b + 2 * a ^ 2 * σ2 = b := by
    rw [hq, hb]
    field_simp
    ring
  -- `𝔼 ‖θ* - θ n‖² ≤ q ^ n 𝔼 ‖θ* - θ 0‖² + b`, by induction
  have key : ∀ n ≤ T, ∫ x, ‖θ' - θ n x‖ ^ 2 ∂μ ≤ q ^ n * ∫ x, ‖θ' - θ 0 x‖ ^ 2 ∂μ + b := by
    intro n
    induction n with
    | zero => intro; simp [hb0]
    | succ n ih =>
      intro hn
      have hαn := hα n (by omega)
      have h := integral_norm_sub_sq_succ_le_mul_add hP hφ hγ.le hθ' hθ hθ₀ hθ₀' hind hO hω
        (t := n) (hαn ▸ ha) (hαn ▸ ha1)
      rw [hαn, ← hq] at h
      calc ∫ x, ‖θ' - θ (n + 1) x‖ ^ 2 ∂μ
          ≤ q * (q ^ n * ∫ x, ‖θ' - θ 0 x‖ ^ 2 ∂μ + b) + 2 * a ^ 2 * σ2 :=
            h.trans (by gcongr; exact ih (by omega))
        _ = q ^ (n + 1) * ∫ x, ‖θ' - θ 0 x‖ ^ 2 ∂μ + b := by linear_combination hqb
  -- `q ^ T ≤ exp (-a (1 - γ) ω T)`
  have hqT : q ^ T ≤ Real.exp (-(a * (1 - γ) * ω * T)) := by
    calc q ^ T ≤ Real.exp (-(a * (1 - γ) * ω)) ^ T :=
          pow_le_pow_left₀ hq0 (by linarith [Real.add_one_le_exp (-(a * (1 - γ) * ω))]) T
      _ = Real.exp (-(a * (1 - γ) * ω * T)) := by rw [← Real.exp_nat_mul]; ring_nf
  exact (key T le_rfl).trans (by gcongr)

/-- **The `1 / T` rate of TD(0) with decaying steps** [BRS18, Theorem 2 (c)]: let `ν` be invariant,
`γ < 1`, `‖φ s‖ ≤ 1` and `θ*` a zero of the mean-path TD update. Let the iterates follow
`θ (t + 1) = θ t + α t d (θ t) (O t)` from an a.e.-measurable `θ 0` with `𝔼 ‖θ 0‖² < ∞`, where
each observation `O t` has law `ν ⊗ₘ P` and is independent of the current iterate `θ t`. If
moreover `ω ‖θ‖² ≤ ‖⟪φ, θ⟫‖²_ν` for every `θ`, with `ω > 0`, then the steps
`α t = β / (λ + t)` for `t < T`, with `β = 2 / ((1 - γ) ω)` and `λ = 16 / ((1 - γ)² ω)`, give
`𝔼 ‖θ* - θ T‖² ≤ κ / (λ + T)` with
`κ = max (8 σ² / ((1 - γ)² ω²)) (16 𝔼 ‖θ* - θ 0‖² / ((1 - γ)² ω))`, where `σ² = 𝔼 ‖d θ*‖²` for
a transition `(s, s') ∼ ν ⊗ₘ P`. The induction step is
`LMLExplore.le_div_add_one_of_le_one_sub_two_div_mul_add`. -/
theorem integral_norm_sub_sq_le_max_div [CompleteSpace E] (hP : P.Invariant ν)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hγ : γ < 1)
    (hθ' : meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ θ' = 0)
    (hθ : ∀ t x, θ (t + 1) x = θ t x + α t • tdUpdate φ R γ (θ t x) (O t x))
    (hθ₀ : AEMeasurable (θ 0) μ) (hθ₀' : MemLp (fun x ↦ ‖θ 0 x‖) 2 μ)
    (hind : ∀ t, IndepFun (θ t) (O t) μ) (hO : ∀ t, HasLaw (O t) (ν ⊗ₘ P) μ) {ω : ℝ}
    (hω₀ : 0 < ω) (hω : ∀ θ, ω * ‖θ‖ ^ 2 ≤ ∫ s, ⟪φ s, θ⟫_ℝ ^ 2 ∂ν) {T : ℕ}
    (hα : ∀ t < T, α t = 2 / ((1 - γ) * ω) / (16 / ((1 - γ) ^ 2 * ω) + t)) :
    ∫ x, ‖θ' - θ T x‖ ^ 2 ∂μ ≤
      max (8 * (∫ o, ‖tdUpdate φ R γ θ' o‖ ^ 2 ∂(ν ⊗ₘ P)) / ((1 - γ) ^ 2 * ω ^ 2))
          (16 * (∫ x, ‖θ' - θ 0 x‖ ^ 2 ∂μ) / ((1 - γ) ^ 2 * ω)) /
        (16 / ((1 - γ) ^ 2 * ω) + T) := by
  set σ2 := ∫ o, ‖tdUpdate φ R γ θ' o‖ ^ 2 ∂(ν ⊗ₘ P) with hσ2
  set x0 := ∫ x, ‖θ' - θ 0 x‖ ^ 2 ∂μ with hx0
  have hγ' : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hσ0 : 0 ≤ σ2 := integral_nonneg fun _ ↦ sq_nonneg _
  have hx00 : 0 ≤ x0 := integral_nonneg fun _ ↦ sq_nonneg _
  set κ := max (8 * σ2 / ((1 - γ) ^ 2 * ω ^ 2)) (16 * x0 / ((1 - γ) ^ 2 * ω)) with hκ
  set l := 16 / ((1 - γ) ^ 2 * ω) with hl
  have hκ0 : 0 ≤ κ := le_max_of_le_right (by positivity)
  have hl0 : 0 < l := by positivity
  rcases le_or_gt ω 1 with hω1 | hω1
  swap
  · -- if `ω > 1`, then `E` is trivial
    rw [integral_norm_sub_sq_eq_zero_of_one_lt hφ hω hω1]
    positivity
  have hγ1 : (1 - (γ : ℝ)) ^ 2 * ω ≤ 1 := by
    have : (1 - (γ : ℝ)) ^ 2 ≤ 1 := by nlinarith [γ.coe_nonneg]
    nlinarith
  have hl16 : 16 ≤ l := by rw [hl, le_div_iff₀ (by positivity)]; linarith
  -- `𝔼 ‖θ* - θ n‖² ≤ κ / (λ + n)`, by induction
  have key : ∀ n ≤ T, ∫ x, ‖θ' - θ n x‖ ^ 2 ∂μ ≤ κ / (l + n) := by
    intro n
    induction n with
    | zero =>
      intro
      rw [Nat.cast_zero, add_zero, le_div_iff₀ hl0, mul_comm]
      exact le_max_of_le_right (by rw [hl, div_mul_eq_mul_div])
    | succ n ih =>
      intro hn
      set u : ℝ := l + n with hu
      have hu16 : 16 ≤ u := by rw [hu]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      have hu0 : 0 < u := by linarith
      have hαn : α n = 2 / ((1 - γ) * ω) / u := hα n (by omega)
      have hα0 : 0 ≤ α n := by rw [hαn]; positivity
      -- the step is at most `(1 - γ) / 8`
      have hα1 : α n ≤ (1 - γ) / 8 :=
        calc α n ≤ 2 / ((1 - γ) * ω) / l := by
              rw [hαn]
              exact div_le_div_of_nonneg_left (by positivity) hl0
                (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
          _ = (1 - γ) / 8 := by rw [hl]; field_simp; ring
      have h := integral_norm_sub_sq_succ_le_mul_add hP hφ hγ.le hθ' hθ hθ₀ hθ₀' hind hO hω
        (t := n) hα0 hα1
      have hq : 1 - α n * (1 - γ) * ω = 1 - 2 / u := by rw [hαn]; field_simp
      have hc : 2 * α n ^ 2 * σ2 = 8 * σ2 / ((1 - γ) ^ 2 * ω ^ 2) / u ^ 2 := by
        rw [hαn]; field_simp; ring
      rw [hq, hc] at h
      rw [Nat.cast_succ, ← add_assoc, ← hu]
      exact le_div_add_one_of_le_one_sub_two_div_mul_add (by linarith) (le_max_left _ _) hκ0
        (ih (by omega)) h
  exact key T le_rfl

end Independent

end LMLExplore.ReinforcementLearning
