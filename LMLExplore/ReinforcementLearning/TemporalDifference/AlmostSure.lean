/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Process.Filtration
public import LMLExplore.Probability.StochasticApproximation.RobbinsMonro
public import LMLExplore.ReinforcementLearning.TemporalDifference.TDUpdate
public import Mathlib.Probability.HasLaw
import LMLExplore.MeasureTheory.Function.L2Space
import TauCeti.Probability.Independence.CondExp

/-!
# Almost-sure convergence of TD(0) with independent observations

TD(0) with linear features `φ : 𝓢 → E` updates its parameter along one observed transition at a
time, `θ (t + 1) = θ t + α t d (θ t) (O t)`, where
`d θ (s, s') = (R (s, s') + γ ⟪φ s', θ⟫ - ⟪φ s, θ⟫) φ s` is the TD(0) direction
(`LMLExplore.ReinforcementLearning.tdUpdate`). When each transition `O t` is drawn from `ν ⊗ₘ P`,
for an invariant law `ν` of the Markov kernel `P`, independently of the past, the mean of `d θ` is
the mean-path TD update `g θ`, and TD(0) is the Robbins–Monro recursion
`θ (t + 1) = θ t - α t (h (θ t) + ξ (t + 1))` for the vector field `h = -g` and the martingale
difference noise `ξ (t + 1) = g (θ t) - d (θ t) (O t)`.

If `γ < 1` and the features are linearly independent in the quantitative sense
`ω ‖θ‖² ≤ ‖⟪φ, θ⟫‖²_ν` with `ω > 0`, the field `-g` points towards the zero `θ*` of `g`:
`⟪θ* - θ, g θ⟫ ≥ (1 - γ) ω ‖θ* - θ‖²` [TVR97], [BRS18, Lemma 3]. With features `‖φ s‖ ≤ 1` and
a finite state space, `g` grows at most linearly and the noise is bounded by an affine function of
`‖θ - θ*‖`. The Robbins–Monro theorem
`LMLExplore.ae_tendsto_of_not_summable_of_summable_sq` then shows that, for deterministic steps
with `∑ α t = ∞` and `∑ α t² < ∞`, the iterates converge to `θ*` almost surely [Zha25].

## Main statements

* `LMLExplore.ReinforcementLearning.ae_tendsto_of_indep`: TD(0) converges almost surely to the
  zero `θ*` of `g`, when each observation has law `ν ⊗ₘ P` and is independent of the past
  `ℱ t` of a filtration to which the iterates are adapted.
* `LMLExplore.ReinforcementLearning.ae_tendsto_of_iIndepFun`: the same, from a deterministic
  `θ 0`, for mutually independent observations of law `ν ⊗ₘ P`.

## References

* [J. N. Tsitsiklis and B. Van Roy, *An analysis of temporal-difference learning with function
  approximation*, 1997][TVR97]
* [J. Bhandari, D. Russo and R. Singal, *A finite time analysis of temporal difference learning
  with linear function approximation*, 2018][BRS18]
* [S. Zhang, *Towards formalizing reinforcement learning theory: a Robbins–Siegmund approach*,
  arXiv:2511.03618, 2025][Zha25]
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace LMLExplore.ReinforcementLearning

variable {𝓢 E : Type*} {m𝓢 : MeasurableSpace 𝓢} [Finite 𝓢] [MeasurableSingletonClass 𝓢]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ν : Measure 𝓢} [IsProbabilityMeasure ν] {P : Kernel 𝓢 𝓢} [IsMarkovKernel P]
  {φ : 𝓢 → E} {R : 𝓢 × 𝓢 → ℝ} {γ : ℝ≥0} {θ' : E}

/-- With features `‖φ s‖ ≤ 1` and `γ ≤ 1`, the mean-path TD update grows at most linearly
around its zero `θ*`: `‖g θ‖ ≤ 2 ‖θ* - θ‖`. -/
private lemma norm_meanTDUpdate_le_two_mul (hP : P.Invariant ν) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hγ : γ ≤ 1) {r : 𝓢 → ℝ} (hθ' : meanTDUpdate ν φ P r γ θ' = 0) (θ : E) :
    ‖meanTDUpdate ν φ P r γ θ‖ ≤ 2 * ‖θ' - θ‖ := by
  have hγ₁ : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ
  have hsq : √(∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν) ≤ ‖θ' - θ‖ :=
    (Real.sqrt_le_sqrt (integral_sq_inner_le_norm_sq hφ _)).trans_eq
      (Real.sqrt_sq (norm_nonneg _))
  calc ‖meanTDUpdate ν φ P r γ θ‖ ≤ (1 + γ) * √(∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν) :=
        norm_meanTDUpdate_le hP hφ hθ' θ
    _ ≤ 2 * ‖θ' - θ‖ := by gcongr; linarith

/-- With features `‖φ s‖ ≤ 1` and `γ ≤ 1`, the noise `g θ - d θ o` of TD(0) is bounded by an
affine function of `‖θ - θ*‖`, uniformly in the transition `o`. -/
private lemma exists_norm_meanTDUpdate_sub_tdUpdate_le (hP : P.Invariant ν)
    (hφ : ∀ s, ‖φ s‖ ≤ 1) (hγ : γ ≤ 1)
    (hθ' : meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ θ' = 0) :
    ∃ K : ℝ, ∀ θ o, ‖meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ θ -
      tdUpdate φ R γ θ o‖ ≤ K + 4 * ‖θ - θ'‖ := by
  obtain ⟨C, hC⟩ := Finite.exists_le fun o ↦ |R o|
  refine ⟨C + 2 * ‖θ'‖, fun θ o ↦ ?_⟩
  have hγ₁ : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ
  have hg := norm_meanTDUpdate_le_two_mul hP hφ hγ hθ' θ
  have hd := norm_tdUpdate_le (R := R) (γ := γ) hφ θ o
  have hθ : ‖θ‖ ≤ ‖θ'‖ + ‖θ - θ'‖ := norm_le_norm_add_norm_sub' θ θ'
  rw [norm_sub_rev θ' θ] at hg
  calc _ ≤ ‖meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ θ‖ +
        ‖tdUpdate φ R γ θ o‖ := norm_sub_le _ _
    _ ≤ C + 2 * ‖θ'‖ + 4 * ‖θ - θ'‖ := by
        nlinarith [hC o, norm_nonneg θ, norm_nonneg θ', norm_nonneg (θ - θ'), γ.coe_nonneg]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The squared bound of the noise, in `ℝ≥0∞`: if `‖a‖ ≤ K + 4 ‖b‖`, then
`‖a‖ₑ² ≤ 2 K² + 32 ‖b‖ₑ²`. -/
private lemma enorm_sq_le_of_norm_le {a b : E} {K : ℝ} (h : ‖a‖ ≤ K + 4 * ‖b‖) :
    ‖a‖ₑ ^ 2 ≤ ((2 * K ^ 2).toNNReal : ℝ≥0∞) + ((32 : ℝ≥0) : ℝ≥0∞) * ‖b‖ₑ ^ 2 := by
  rw [eNorm_eq_nnNorm, eNorm_eq_nnNorm]
  norm_cast
  rw [← NNReal.coe_le_coe]
  push_cast
  rw [Real.coe_toNNReal _ (by positivity)]
  have ha := norm_nonneg a
  nlinarith [sq_nonneg (K - 4 * ‖b‖), mul_self_le_mul_self ha h]

variable [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ} {θ : ℕ → Ω → E} {O : ℕ → Ω → 𝓢 × 𝓢} {α : ℕ → ℝ≥0}

omit [Finite 𝓢] [IsProbabilityMeasure ν] [IsMarkovKernel P] [SecondCountableTopology E]
  [CompleteSpace E] [IsProbabilityMeasure μ] in
/-- Along `θ (t + 1) = θ t + α t d (θ t) (O t)`, the iterates are adapted to a filtration `ℱ`
for which `θ 0` is `ℱ 0`-measurable and each observation `O t` is `ℱ (t + 1)`-measurable. -/
private lemma measurable_iterate [Countable 𝓢]
    (hθ : ∀ t x, θ (t + 1) x = θ t x + α t • tdUpdate φ R γ (θ t x) (O t x))
    (hθ₀ : Measurable[ℱ 0] (θ 0)) (hO : ∀ t, Measurable[ℱ (t + 1)] (O t)) (t : ℕ) :
    Measurable[ℱ t] (θ t) := by
  induction t with
  | zero => exact hθ₀
  | succ t ih =>
    have hfun : θ (t + 1) = fun x ↦ θ t x + (α t : ℝ) • tdUpdate φ R γ (θ t x) (O t x) :=
      funext fun x ↦ by rw [hθ, NNReal.smul_def]
    rw [hfun]
    exact (measurable_add_smul_tdUpdate (α t : ℝ)).comp
      ((ih.mono (ℱ.mono t.le_succ) le_rfl).prodMk (hO t))

omit [SecondCountableTopology E] in
/-- The noise `(θ, o) ↦ g θ - d θ o` of TD(0), as a function of the parameter and the
transition, is measurable. -/
private lemma measurable_meanTDUpdate_sub_tdUpdate {r : 𝓢 → ℝ} :
    Measurable fun p : E × (𝓢 × 𝓢) ↦ meanTDUpdate ν φ P r γ p.1 - tdUpdate φ R γ p.1 p.2 :=
  measurable_from_prod_countable_left fun o ↦
    (continuous_meanTDUpdate.sub (continuous_tdUpdate o)).measurable

/-- **The noise of TD(0) is a martingale difference**: if `θ t` is `ℱ t`-measurable and the
observation `O t` has law `ν ⊗ₘ P` and is independent of `ℱ t`, then
`𝔼[g (θ t) - d (θ t) (O t) | ℱ t] = 0`. -/
private lemma condExp_meanTDUpdate_sub_tdUpdate_ae_eq_zero {t : ℕ}
    (hθt : Measurable[ℱ t] (θ t)) (hO : Measurable (O t))
    (hind : Indep (MeasurableSpace.comap (O t) inferInstance) (ℱ t) μ)
    (hlaw : HasLaw (O t) (ν ⊗ₘ P) μ) :
    μ[fun x ↦ meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ (θ t x) -
      tdUpdate φ R γ (θ t x) (O t x) | ℱ t] =ᵐ[μ] 0 := by
  set g := meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ
  by_cases hint : Integrable (fun x ↦ g (θ t x) - tdUpdate φ R γ (θ t x) (O t x)) μ
  swap
  · rw [condExp_of_not_integrable hint]
  -- freeze the known iterate and integrate the independent observation out
  refine (TauCeti.Probability.condExp_comp_prodMk_ae_eq_integral_of_indep (ℱ.le t) hθt hO hind
    measurable_meanTDUpdate_sub_tdUpdate.stronglyMeasurable hint).trans (ae_of_all _ fun x ↦ ?_)
  simp only [hlaw.map_eq]
  rw [integral_sub (integrable_const _) Integrable.of_finite, integral_tdUpdate, integral_const,
    probReal_univ, one_smul, sub_self, Pi.zero_apply]

/-- **Almost-sure convergence of TD(0) with independent observations**: let `ν` be invariant for
`P`, `γ < 1`, `‖φ s‖ ≤ 1`, `ω ‖θ‖² ≤ ‖⟪φ, θ⟫‖²_ν` with `ω > 0`, and `θ*` a zero of the
mean-path TD update. Let the iterates follow `θ (t + 1) = θ t + α t d (θ t) (O t)` from an
`ℱ 0`-measurable `θ 0` with `𝔼 ‖θ 0‖² < ∞`, where each observation `O t` is
`ℱ (t + 1)`-measurable, has law `ν ⊗ₘ P` and is independent of `ℱ t`. If the deterministic
steps satisfy `∑ α t = ∞` and `∑ α t² < ∞`, then `θ t → θ*` almost surely. -/
theorem ae_tendsto_of_indep (hP : P.Invariant ν) (hφ : ∀ s, ‖φ s‖ ≤ 1) (hγ : γ < 1) {ω : ℝ}
    (hω₀ : 0 < ω) (hω : ∀ θ, ω * ‖θ‖ ^ 2 ≤ ∫ s, ⟪φ s, θ⟫_ℝ ^ 2 ∂ν)
    (hθ' : meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ θ' = 0)
    (hθ : ∀ t x, θ (t + 1) x = θ t x + α t • tdUpdate φ R γ (θ t x) (O t x))
    (hθ₀ : Measurable[ℱ 0] (θ 0)) (hθ₀' : MemLp (fun x ↦ ‖θ 0 x‖) 2 μ)
    (hO : ∀ t, Measurable[ℱ (t + 1)] (O t))
    (hind : ∀ t, Indep (MeasurableSpace.comap (O t) inferInstance) (ℱ t) μ)
    (hlaw : ∀ t, HasLaw (O t) (ν ⊗ₘ P) μ) (hα : ¬ Summable α)
    (hα2 : Summable fun t ↦ α t ^ 2) :
    ∀ᵐ x ∂μ, Tendsto (fun t ↦ θ t x) atTop (𝓝 θ') := by
  set g := meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ with hg
  have hγ₁ : (γ : ℝ) < 1 := by exact_mod_cast hγ
  have hθm := measurable_iterate hθ hθ₀ hO
  have hO' (t : ℕ) : Measurable (O t) := (hO t).mono (ℱ.le _) le_rfl
  obtain ⟨K, hK⟩ := exists_norm_meanTDUpdate_sub_tdUpdate_le hP hφ hγ.le hθ'
  -- TD(0) is the Robbins–Monro recursion for `h = -g`, with noise `ξ (t + 1) = g (θ t) - d (θ t)`
  refine LMLExplore.ae_tendsto_of_not_summable_of_summable_sq (h := fun y ↦ -g y) (C := 2)
    (ξ := fun n x ↦ g (θ (n - 1) x) - tdUpdate φ R γ (θ (n - 1) x) (O (n - 1) x))
    (A := (2 * K ^ 2).toNNReal) (B := 32) (fun n x ↦ ?_) hθ₀ ?_
    continuous_meanTDUpdate.neg.measurable (fun y ↦ ?_) ?_ (fun n ↦ ?_) (fun n ↦ ?_)
    (fun n ↦ ?_) hα hα2
  · -- the recursion
    rw [Nat.add_sub_cancel, hθ, smul_add, smul_neg, smul_sub]
    abel
  · -- the initial square-integrability
    simpa only [norm_sub_rev] using
      integrable_norm_const_sub_sq (hθ₀.mono (ℱ.le 0) le_rfl).aemeasurable hθ₀' θ'
  · -- linear growth of the field
    rw [norm_neg, NNReal.coe_ofNat, norm_sub_rev]
    have := norm_meanTDUpdate_le_two_mul hP hφ hγ.le hθ' y
    nlinarith [norm_nonneg (y - θ')]
  · -- the field points towards `θ*` on annuli
    rintro ε ⟨hε₀, -⟩
    refine ⟨(1 - γ) * ω * ε ^ 2, by have := sub_pos.2 hγ₁; positivity, fun y hy _ ↦ ?_⟩
    have h₁ := one_sub_mul_integral_sq_le_inner_meanTDUpdate hP hθ' y
    rw [← hg] at h₁
    have h₂ := mul_le_mul_of_nonneg_left (hω (θ' - y)) (sub_pos.2 hγ₁).le
    have h₃ : ε ^ 2 ≤ ‖θ' - y‖ ^ 2 := by
      rw [norm_sub_rev]
      exact pow_le_pow_left₀ hε₀.le hy 2
    have h₄ := mul_le_mul_of_nonneg_left h₃ (mul_pos (sub_pos.2 hγ₁) hω₀).le
    rw [inner_neg_right, ← inner_neg_left, neg_sub]
    linarith
  · -- the noise is adapted
    simp only [Nat.add_sub_cancel]
    exact measurable_meanTDUpdate_sub_tdUpdate.comp
        (((hθm n).mono (ℱ.mono n.le_succ) le_rfl).prodMk (hO n))
  · -- the noise is a martingale difference
    simpa only [Nat.add_sub_cancel] using
      condExp_meanTDUpdate_sub_tdUpdate_ae_eq_zero (hθm n) (hO' n) (hind n) (hlaw n)
  · -- the conditional second moment of the noise is bounded by its pointwise bound
    simp only [Nat.add_sub_cancel]
    have hb : Measurable[ℱ n] fun x ↦
        ((2 * K ^ 2).toNNReal : ℝ≥0∞) + ((32 : ℝ≥0) : ℝ≥0∞) * ‖θ n x - θ'‖ₑ ^ 2 :=
      (measurable_const.add (measurable_const.mul
        ((measurable_id.sub_const θ').eNorm.pow_const 2))).comp (hθm n)
    have h := condLExp_mono (mΩ := ℱ n) (P := μ) (ae_of_all _ fun x ↦
      enorm_sq_le_of_norm_le (hK (θ n x) (O n x)))
    rwa [condLExp_eq_self (ℱ.le n) μ hb] at h

/-- **Almost-sure convergence of TD(0) with i.i.d. observations**: let `ν` be invariant for `P`,
`γ < 1`, `‖φ s‖ ≤ 1`, `ω ‖θ‖² ≤ ‖⟪φ, θ⟫‖²_ν` with `ω > 0`, and `θ*` a zero of the mean-path TD
update. Along `θ (t + 1) = θ t + α t d (θ t) (O t)` from a deterministic `θ 0`, with mutually
independent observations of law `ν ⊗ₘ P` and deterministic steps with `∑ α t = ∞` and
`∑ α t² < ∞`, `θ t → θ*` almost surely. -/
theorem ae_tendsto_of_iIndepFun (hP : P.Invariant ν) (hφ : ∀ s, ‖φ s‖ ≤ 1) (hγ : γ < 1)
    {ω : ℝ} (hω₀ : 0 < ω) (hω : ∀ θ, ω * ‖θ‖ ^ 2 ≤ ∫ s, ⟪φ s, θ⟫_ℝ ^ 2 ∂ν)
    (hθ' : meanTDUpdate ν φ P (fun s ↦ ∫ s', R (s, s') ∂(P s)) γ θ' = 0)
    (hθ : ∀ t x, θ (t + 1) x = θ t x + α t • tdUpdate φ R γ (θ t x) (O t x)) {θ₀ : E}
    (hθ₀ : ∀ x, θ 0 x = θ₀) (hO : ∀ t, Measurable (O t)) (hind : iIndepFun O μ)
    (hlaw : ∀ t, HasLaw (O t) (ν ⊗ₘ P) μ) (hα : ¬ Summable α)
    (hα2 : Summable fun t ↦ α t ^ 2) :
    ∀ᵐ x ∂μ, Tendsto (fun t ↦ θ t x) atTop (𝓝 θ') := by
  have h0 : θ 0 = fun _ ↦ θ₀ := funext hθ₀
  refine ae_tendsto_of_indep (ℱ := Filtration.naturalLT O hO) hP hφ hγ hω₀ hω hθ' hθ
    (h0 ▸ measurable_const) (h0 ▸ memLp_const ‖θ₀‖)
    (fun t ↦ Filtration.measurable_naturalLT hO t.lt_succ_self)
    (Filtration.indep_naturalLT hO hind) hlaw hα hα2

end LMLExplore.ReinforcementLearning
