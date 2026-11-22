/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.Basic
public import LMLExplore.EValues.SubGaussian.SequentialCompleteClass
public import LMLExplore.EValues.TestSupermartingale.SequentialNull
public import LMLExplore.Probability.Martingale.ExactVille
public import LMLExplore.Probability.Martingale.Freedman
public import LMLExplore.Probability.Moments.MGF.Bound
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Sub-ψ processes and the line-crossing inequality

Let `ψ : ℝ → ℝ` and a set of parameters `Λ ⊆ ℝ`. A pair of real processes `(S, V)` is
*`l₀`-sub-ψ* on `Λ` [HRMS20, Definition 1] when, for every `t ∈ Λ`, the exponential process
`exp (t S n - ψ t V n)` is dominated at all times by a nonnegative supermartingale `L` with
`L 0 ≤ l₀`. Here `S` is a sum of increments, `V` an *intrinsic time* that measures their
accumulated variance, and `ψ` plays the role of a cumulant generating function. The definition is
stated for a null `𝒩`, under each of its members, with `ℝ≥0∞`-valued supermartingales
(`ProbabilityTheory.IsENNSupermartingale`) and no integrability condition.

The basic instance is a null of conditional bets. For observations `X k`, the exponentials
`x ↦ exp (t x - ψ t)`, `t ∈ Λ` (`ProbabilityTheory.subPsiBets ψ Λ`), are the bets of the laws whose
cumulant generating function is at most `ψ` on `Λ`, and under every member of the null
`condEVarNull (subPsiBets ψ Λ) X ℱ` of laws under which each of them, at the next observation, is
a conditional e-variable given the past, the process `exp (t ∑ k < n, X k - n ψ t)` is a test
supermartingale. So the partial sums, with the intrinsic time `n`, are `1`-sub-ψ for that null.
The laws with a conditional bound on the moment generating function (LMLExplore's
`HasCondMGFBound`) are members of it, and the one-sided conditionally `1`-sub-Gaussian null is the
case `ψ t = t ^ 2 / 2`, `Λ = [0, ∞)`. Freedman's exponential supermartingale makes the partial sums
of increments bounded above by `b` sub-Poisson, `ψ t = (exp (t b) - 1 - t b) / b ^ 2`, with the
sum of the conditional second moments as intrinsic time.

Ville's inequality applied to the supermartingales `L` gives the bounds of [HRMS20, Theorem 1(a)],
conditionally on `ℱ 0`: for a nonnegative intrinsic time, the probability that `S` ever crosses
the line `a + b V` is at most `l₀ exp (-a t)` for every `t ∈ Λ`, `t ≥ 0`, with `ψ t ≤ b t`, hence at
most `l₀ exp (-a D b)`, with the *decay transform*
`D b = sup {t ∈ Λ | 0 < t, ψ t ≤ b t}` (`ProbabilityTheory.decayTransform`), in `ℝ≥0∞`, `0` for
the empty set. For the sub-Gaussian `ψ`, `D b = 2 b`, which gives the classical bound
`exp (-2 a b)` on the probability that a conditionally sub-Gaussian random walk ever crosses the
line `a + b n`.

## Main definitions

* `ProbabilityTheory.subPsiBets ψ Λ`: the exponentials `x ↦ exp (t x - ψ t)`, `t ∈ Λ`.
* `ProbabilityTheory.IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩`: `(S, V)` is an `l₀`-sub-ψ process on `Λ`
  for the filtration `ℱ` under every member of `𝒩`.
* `ProbabilityTheory.decayTransform ψ Λ b`: the decay transform.

## Main statements

* `ProbabilityTheory.isTestSupermartingale_exp_sum_condEVarNull`: the exponential process
  `exp (t ∑ k < n, X k - n ψ t)` is a test supermartingale for the null of the sub-ψ bets.
* `ProbabilityTheory.mem_condEVarNull_subPsiBets_of_hasCondMGFBound`: a law with conditional
  moment generating functions bounded by `exp ψ` on `Λ` belongs to that null.
* `ProbabilityTheory.oneSidedCondSubgaussianNull_eq_condEVarNull`: the one-sided conditionally
  `1`-sub-Gaussian null is the null of the sub-Gaussian bets.
* `ProbabilityTheory.isSubPsiProcess_sum_condEVarNull`,
  `ProbabilityTheory.isSubPsiProcess_sum_sum_condExp_sq`: the partial sums are sub-ψ for the null
  of the sub-ψ bets, and sub-Poisson with Freedman's intrinsic time.
* `ProbabilityTheory.IsSubPsiProcess.isEProcess`: `l₀⁻¹ exp (t S - ψ t V)` is an e-process.
* `ProbabilityTheory.IsSubPsiProcess.measure_inter_exists_le_mul_sub_mul_le`: Ville's inequality
  for the exponential process, conditionally on `ℱ 0`.
* `ProbabilityTheory.IsSubPsiProcess.measure_inter_exists_add_mul_le_le`,
  `ProbabilityTheory.IsSubPsiProcess.measure_exists_add_mul_le_le`: **the line-crossing
  inequality** [HRMS20, Theorem 1(a)], `P(∃ n, a + b V n ≤ S n) ≤ l₀ exp (-a D b)`.
* `ProbabilityTheory.measure_exists_add_mul_le_sum_le_of_mem_oneSidedCondSubgaussianNull`: the
  line-crossing inequality `exp (-2 a b)` for the one-sided conditionally sub-Gaussian null.

## Implementation notes

[HRMS20] also asks `S 0 = V 0 = 0`, `V ≥ 0`, `l₀ ≥ 1` and the adaptedness of `S` and `V`. The
definition here carries only the domination, and each statement assumes what it uses: the
line-crossing inequalities a nonnegative intrinsic time, their form with the decay transform
`1 ≤ l₀ < ∞`, and the e-processes adapted processes.

## References

* [HRMS20] S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, *Time-uniform Chernoff bounds via
  nonnegative supermartingales*, Probab. Surveys 17 (2020), 257–317, arXiv:1808.03204.
* [Fre75] D. A. Freedman, *On tail probabilities for martingales*, Ann. Probab. 3 (1975), 100–118.
-/

public section

open MeasureTheory Set Finset Real
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {𝒩 𝒩' : Set (Measure Ω)}
  {P : Measure Ω} {S V X : ℕ → Ω → ℝ} {ψ : ℝ → ℝ} {Λ Λ' : Set ℝ} {l₀ l₁ : ℝ≥0∞} {t a b : ℝ}
  {s : Set Ω}

/-! ### The sub-ψ bets -/

/-- The **sub-ψ bets** on the line, for a function `ψ` and a set `Λ` of parameters: the
exponentials `x ↦ exp (t x - ψ t)` for `t ∈ Λ`. A law has all of them as e-variables exactly when
its moment generating function is at most `exp ψ` on `Λ`. -/
noncomputable def subPsiBets (ψ : ℝ → ℝ) (Λ : Set ℝ) : Set (ℝ → ℝ≥0∞) :=
  (fun t x ↦ ENNReal.ofReal (exp (t * x - ψ t))) '' Λ

/-- Membership in the sub-ψ bets. -/
theorem mem_subPsiBets_iff {e : ℝ → ℝ≥0∞} :
    e ∈ subPsiBets ψ Λ ↔ ∃ t ∈ Λ, (fun x ↦ ENNReal.ofReal (exp (t * x - ψ t))) = e :=
  Iff.rfl

/-- The exponential of a parameter of `Λ` is a sub-ψ bet. -/
theorem exp_mem_subPsiBets (ht : t ∈ Λ) :
    (fun x ↦ ENNReal.ofReal (exp (t * x - ψ t))) ∈ subPsiBets ψ Λ :=
  ⟨t, ht, rfl⟩

/-- The sub-ψ bets grow with the set of parameters. -/
@[gcongr]
theorem subPsiBets_mono (h : Λ ⊆ Λ') : subPsiBets ψ Λ ⊆ subPsiBets ψ Λ' :=
  image_mono h

/-- **The exponential supermartingale of the sub-ψ null** [HRMS20, §2.1]. If each observation
`X k` is `ℱ (k + 1)`-measurable, then for every `t ∈ Λ` the process
`exp (t ∑ k < n, X k - n ψ t)` is a test supermartingale for the null of the laws under which
every sub-ψ bet at the next observation is a conditional e-variable given the past. -/
theorem isTestSupermartingale_exp_sum_condEVarNull (hX : ∀ k, Measurable[ℱ (k + 1)] (X k))
    (ht : t ∈ Λ) :
    IsTestSupermartingale
      (fun n ω ↦ ENNReal.ofReal (exp (t * ∑ k ∈ range n, X k ω - n * ψ t))) ℱ
      (condEVarNull (subPsiBets ψ Λ) X ℱ) := by
  have h := isTestSupermartingale_prod_condEVarNull
    (e := fun _ x ↦ ENNReal.ofReal (exp (t * x - ψ t))) hX (fun _ ↦ exp_mem_subPsiBets ht)
    fun _ ↦ by fun_prop
  convert h using 3 with n ω
  rw [← ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (exp_pos _).le, ← exp_sum, sum_sub_distrib,
    mul_sum, sum_const, card_range, nsmul_eq_mul]

/-- **Conditional bounds on the moment generating function give members of the sub-ψ null.** A
probability measure under which every observation `X k` has, given `ℱ k`, a moment generating
function bounded by `exp ψ` on `Λ` belongs to the null of the sub-ψ bets. -/
theorem mem_condEVarNull_subPsiBets_of_hasCondMGFBound [StandardBorelSpace Ω]
    [IsProbabilityMeasure P] (hX : ∀ k, Measurable (X k))
    (hψ : ∀ k, LMLExplore.HasCondMGFBound (ℱ k) (ℱ.le k) (X k) ψ Λ P) :
    P ∈ condEVarNull (subPsiBets ψ Λ) X ℱ := by
  refine mem_condEVarNull_iff.2 ⟨inferInstance, fun k e he ↦ ?_⟩
  obtain ⟨t, ht, rfl⟩ := he
  refine ⟨by fun_prop, ?_⟩
  rintro Q rfl s hs
  -- with `g = 𝟙_s exp (-ψ t)`, the conditional bound reads `∫⁻ g exp (t X k) ≤ ∫⁻ g exp (ψ t)`
  set g : Ω → ℝ≥0∞ := s.indicator fun _ ↦ ENNReal.ofReal (exp (-ψ t))
  have h := (hψ k).lintegral_mul_exp_le (hX k) (s := fun _ ↦ t) measurable_const
    (ae_of_all _ fun _ ↦ ht) (g := g) (measurable_const.indicator hs)
  have hl : ∀ ω, s.indicator (fun ω ↦ ENNReal.ofReal (exp (t * X k ω - ψ t))) ω =
      g ω * ENNReal.ofReal (exp (t * X k ω)) := fun ω ↦ by
    by_cases hω : ω ∈ s <;>
      simp [g, hω, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add, sub_eq_neg_add]
  have hr : ∀ ω, g ω * ENNReal.ofReal (exp (ψ t)) = s.indicator 1 ω := fun ω ↦ by
    by_cases hω : ω ∈ s <;> simp [g, hω, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
  rw [← lintegral_indicator (ℱ.le k _ hs)]
  simp_rw [hl]
  refine h.trans_eq ?_
  simp_rw [hr]
  exact lintegral_indicator_one (ℱ.le k _ hs)

/-- **The one-sided conditionally sub-Gaussian null is a null of conditional bets**: it is the
null of the sub-Gaussian bets `x ↦ exp (t x - t ^ 2 / 2)`, `t ≥ 0`, for the coordinates of
`ℕ → ℝ` and the filtration `Filtration.piLT` of the strict past. -/
theorem oneSidedCondSubgaussianNull_eq_condEVarNull :
    oneSidedCondSubgaussianNull =
      condEVarNull (subPsiBets (fun t ↦ t ^ 2 / 2) (Ici 0)) (fun k ω ↦ ω k) Filtration.piLT := by
  ext P
  rw [mem_oneSidedCondSubgaussianNull_iff, mem_condEVarNull_iff]
  refine and_congr_right fun _ ↦ ⟨fun h k e he ↦ ?_, fun h k l hl s hs ↦ ?_⟩
  · obtain ⟨l, hl, rfl⟩ := he
    exact ⟨by fun_prop, fun Q hQ s hs ↦ (mem_singleton_iff.1 hQ) ▸ h k l hl s hs⟩
  · exact (h k _ (exp_mem_subPsiBets (mem_Ici.2 hl))).setLIntegral_le P (mem_singleton P) s hs

/-! ### Sub-ψ processes -/

/-- `(S, V)` is an **`l₀`-sub-ψ process** on the parameters `Λ`, for the filtration `ℱ`, under
every member of the null `𝒩` [HRMS20, Definition 1]: for every `P ∈ 𝒩` and every `t ∈ Λ`, some
`ℝ≥0∞`-valued supermartingale `L` for `P` has `L 0 ≤ l₀` almost surely and dominates
`exp (t S n - ψ t V n)` almost surely at every time `n`. The supermartingale may depend on the
member of the null. -/
def IsSubPsiProcess (S V : ℕ → Ω → ℝ) (ψ : ℝ → ℝ) (Λ : Set ℝ) (l₀ : ℝ≥0∞)
    (ℱ : Filtration ℕ mΩ) (𝒩 : Set (Measure Ω)) : Prop :=
  ∀ P ∈ 𝒩, ∀ t ∈ Λ, ∃ L : ℕ → Ω → ℝ≥0∞, IsENNSupermartingale L ℱ {P} ∧
    (∀ᵐ ω ∂P, L 0 ω ≤ l₀) ∧ ∀ n, (fun ω ↦ ENNReal.ofReal (exp (t * S n ω - ψ t * V n ω))) ≤ᵐ[P] L n

/-- The defining property of a sub-ψ process. -/
theorem isSubPsiProcess_iff :
    IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩 ↔ ∀ P ∈ 𝒩, ∀ t ∈ Λ, ∃ L : ℕ → Ω → ℝ≥0∞,
      IsENNSupermartingale L ℱ {P} ∧ (∀ᵐ ω ∂P, L 0 ω ≤ l₀) ∧
        ∀ n, (fun ω ↦ ENNReal.ofReal (exp (t * S n ω - ψ t * V n ω))) ≤ᵐ[P] L n :=
  Iff.rfl

/-- A process is sub-ψ under every member of a null exactly when it is sub-ψ under each of them. -/
theorem isSubPsiProcess_iff_forall_singleton :
    IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩 ↔ ∀ P ∈ 𝒩, IsSubPsiProcess S V ψ Λ l₀ ℱ {P} :=
  ⟨fun h P hP _ hQ ↦ (mem_singleton_iff.1 hQ) ▸ h P hP, fun h P hP ↦ h P hP P (mem_singleton P)⟩

namespace IsSubPsiProcess

/-- A sub-ψ process under every member of `𝒩'` is one under every member of a subset of `𝒩'`. -/
theorem anti_set (h𝒩 : 𝒩 ⊆ 𝒩') (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩') :
    IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩 :=
  fun P hP ↦ h P (h𝒩 hP)

/-- A sub-ψ process on `Λ` is sub-ψ on every subset of `Λ`. -/
theorem mono_param (hΛ : Λ' ⊆ Λ) (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩) :
    IsSubPsiProcess S V ψ Λ' l₀ ℱ 𝒩 :=
  fun P hP t ht ↦ h P hP t (hΛ ht)

/-- An `l₀`-sub-ψ process is `l₁`-sub-ψ for every `l₁ ≥ l₀`. -/
theorem mono_initial (hl : l₀ ≤ l₁) (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩) :
    IsSubPsiProcess S V ψ Λ l₁ ℱ 𝒩 := fun P hP t ht ↦ by
  obtain ⟨L, hL, hL0, hdom⟩ := h P hP t ht
  exact ⟨L, hL, hL0.mono fun _ hω ↦ hω.trans hl, hdom⟩

/-- **Sub-ψ processes give e-processes.** For a null of probability measures and adapted `S` and
`V`, the exponential process `l₀⁻¹ exp (t S n - ψ t V n)` of an `l₀`-sub-ψ process is an e-process
for every `t ∈ Λ`: under each member it is dominated by the test supermartingale `l₀⁻¹ L`. -/
theorem isEProcess (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩)
    (h𝒩 : ∀ P ∈ 𝒩, IsProbabilityMeasure P) (hS : ∀ n, Measurable[ℱ n] (S n))
    (hV : ∀ n, Measurable[ℱ n] (V n)) (ht : t ∈ Λ) :
    IsEProcess (fun n ω ↦ l₀⁻¹ * ENNReal.ofReal (exp (t * S n ω - ψ t * V n ω))) ℱ 𝒩 := by
  refine (isEProcess_iff_forall_exists_isTestSupermartingale h𝒩 fun n ↦ ?_).2 fun P hP ↦ ?_
  · exact measurable_const.mul (((hS n).const_mul t).sub ((hV n).const_mul _)).exp.ennreal_ofReal
  obtain ⟨L, hL, hL0, hdom⟩ := h P hP t ht
  have := h𝒩 P hP
  refine ⟨fun n ω ↦ l₀⁻¹ * L n ω, ⟨hL.const_mul l₀⁻¹, fun Q hQ ↦ ?_⟩,
    fun n ↦ (hdom n).mono fun ω hω ↦ mul_le_mul_right hω _⟩
  rw [mem_singleton_iff.1 hQ, lintegral_const_mul _ (hL.measurable 0)]
  calc l₀⁻¹ * ∫⁻ ω, L 0 ω ∂P ≤ l₀⁻¹ * ∫⁻ _, l₀ ∂P := mul_le_mul_right (lintegral_mono_ae hL0) _
    _ ≤ 1 := by simp

/-- **Ville's inequality for a sub-ψ process** [HRMS20, §2.3], conditionally on `ℱ 0`: for every
`t ∈ Λ`, every real `c` and every `ℱ 0`-measurable set `s`, the probability that `s` holds and
`c ≤ t S n - ψ t V n` at some time `n` is at most `l₀ exp (-c) P s`. -/
theorem measure_inter_exists_le_mul_sub_mul_le (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩)
    (hP : P ∈ 𝒩) (ht : t ∈ Λ) (c : ℝ) (hs : MeasurableSet[ℱ 0] s) :
    P (s ∩ {ω | ∃ n, c ≤ t * S n ω - ψ t * V n ω}) ≤ l₀ * ENNReal.ofReal (exp (-c)) * P s := by
  obtain ⟨L, hL, hL0, hdom⟩ := h P hP t ht
  have hC0 : ENNReal.ofReal (exp c) ≠ 0 := (ENNReal.ofReal_pos.2 (exp_pos c)).ne'
  calc P (s ∩ {ω | ∃ n, c ≤ t * S n ω - ψ t * V n ω})
      ≤ P (s ∩ {ω | ∃ n ≥ 0, ENNReal.ofReal (exp c) ≤ L n ω}) := by
        refine measure_mono_ae ?_
        filter_upwards [ae_all_iff.2 hdom] with ω hω hmem
        obtain ⟨hωs, n, hn⟩ := hmem
        exact ⟨hωs, n, Nat.zero_le n, (ENNReal.ofReal_le_ofReal (exp_le_exp.2 hn)).trans (hω n)⟩
    _ ≤ (∫⁻ ω in s, min (L 0 ω) (ENNReal.ofReal (exp c)) ∂P) / ENNReal.ofReal (exp c) :=
        hL.measure_inter_exists_le_le (mem_singleton P) hC0 ENNReal.ofReal_ne_top hs
    _ ≤ (∫⁻ _ in s, l₀ ∂P) / ENNReal.ofReal (exp c) := by
        gcongr ?_ / _
        exact lintegral_mono_ae ((ae_restrict_of_ae hL0).mono fun ω hω ↦ (min_le_left _ _).trans hω)
    _ = l₀ * ENNReal.ofReal (exp (-c)) * P s := by
        rw [setLIntegral_const, div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (exp_pos c), ← exp_neg,
          mul_right_comm]

/-- **The line-crossing inequality at one parameter** [HRMS20, proof of Theorem 1(a)],
conditionally on `ℱ 0`. For a nonnegative intrinsic time `V` and a parameter `t ≥ 0` of `Λ` with
`ψ t ≤ b t`, the probability that `s` holds and `S` crosses the line `a + b V` at some time is at
most `l₀ exp (-a t) P s`. -/
theorem measure_inter_exists_add_mul_le_le_of_mem (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩)
    (hP : P ∈ 𝒩) (hV : ∀ n, 0 ≤ᵐ[P] V n) (ht : t ∈ Λ) (ht0 : 0 ≤ t) (hψ : ψ t ≤ b * t) (a : ℝ)
    (hs : MeasurableSet[ℱ 0] s) :
    P (s ∩ {ω | ∃ n, a + b * V n ω ≤ S n ω}) ≤ l₀ * ENNReal.ofReal (exp (-(a * t))) * P s := by
  refine (measure_mono_ae ?_).trans (h.measure_inter_exists_le_mul_sub_mul_le hP ht (a * t) hs)
  filter_upwards [ae_all_iff.2 hV] with ω hω hmem
  obtain ⟨hωs, n, hn⟩ := hmem
  refine ⟨hωs, n, ?_⟩
  -- `t S n ≥ t (a + b V n) = a t + (b t) V n ≥ a t + ψ t V n`
  have h₁ := mul_le_mul_of_nonneg_left hn ht0
  have h₂ := mul_le_mul_of_nonneg_right hψ (hω n)
  nlinarith

end IsSubPsiProcess

/-! ### The decay transform and the line-crossing inequality -/

/-- The **decay transform** of `ψ` on `Λ` [HRMS20, §2.2]: `D b = sup {t ∈ Λ | 0 < t, ψ t ≤ b t}`,
valued in `ℝ≥0∞`, with `D b = 0` when no such `t` exists. It is the rate of exponential decay, in
the intercept `a`, of the probability that a sub-ψ process crosses the line `a + b V`. -/
noncomputable def decayTransform (ψ : ℝ → ℝ) (Λ : Set ℝ) (b : ℝ) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' {t | t ∈ Λ ∧ 0 < t ∧ ψ t ≤ b * t})

theorem decayTransform_def (ψ : ℝ → ℝ) (Λ : Set ℝ) (b : ℝ) :
    decayTransform ψ Λ b = sSup (ENNReal.ofReal '' {t | t ∈ Λ ∧ 0 < t ∧ ψ t ≤ b * t}) :=
  (rfl)

/-- Every positive parameter of `Λ` with `ψ t ≤ b t` is at most the decay transform at `b`. -/
theorem ofReal_le_decayTransform (ht : t ∈ Λ) (ht0 : 0 < t) (hψ : ψ t ≤ b * t) :
    ENNReal.ofReal t ≤ decayTransform ψ Λ b :=
  le_sSup ⟨t, ⟨ht, ht0, hψ⟩, rfl⟩

/-- The decay transform at `b` is at most `x` exactly when every positive parameter `t ∈ Λ` with
`ψ t ≤ b t` is. -/
theorem decayTransform_le_iff {x : ℝ≥0∞} :
    decayTransform ψ Λ b ≤ x ↔ ∀ t ∈ Λ, 0 < t → ψ t ≤ b * t → ENNReal.ofReal t ≤ x := by
  simp only [decayTransform_def, sSup_le_iff, forall_mem_image, mem_ofPred_eq, and_imp]

/-- The decay transform is monotone in the slope. -/
theorem monotone_decayTransform : Monotone (decayTransform ψ Λ) := fun _ _ hbb' ↦
  decayTransform_le_iff.2 fun _ ht ht0 hψ ↦
    ofReal_le_decayTransform ht ht0 (hψ.trans (mul_le_mul_of_nonneg_right hbb' ht0.le))

/-- The decay transform grows with the set of parameters. -/
theorem decayTransform_mono (hΛ : Λ ⊆ Λ') : decayTransform ψ Λ b ≤ decayTransform ψ Λ' b :=
  decayTransform_le_iff.2 fun _ ht ht0 hψ ↦ ofReal_le_decayTransform (hΛ ht) ht0 hψ

/-- The decay transform of the sub-Gaussian `ψ t = t ^ 2 / 2` on `[0, ∞)` is `2 b`. -/
theorem decayTransform_sq_div_two (b : ℝ) :
    decayTransform (fun t ↦ t ^ 2 / 2) (Ici 0) b = ENNReal.ofReal (2 * b) := by
  refine le_antisymm (decayTransform_le_iff.2 fun t _ ht0 hψ ↦ ENNReal.ofReal_le_ofReal ?_) ?_
  · nlinarith
  · rcases le_or_gt b 0 with hb | hb
    · simp [ENNReal.ofReal_of_nonpos (by linarith : 2 * b ≤ 0)]
    · exact ofReal_le_decayTransform (mem_Ici.2 (by linarith)) (by linarith) (by nlinarith)

namespace IsSubPsiProcess

/-- **The line-crossing inequality** [HRMS20, Theorem 1(a)], conditionally on `ℱ 0`. For an
`l₀`-sub-ψ process with `1 ≤ l₀ < ∞` and a nonnegative intrinsic time `V`, every intercept
`a ≥ 0`, every slope `b` and every `ℱ 0`-measurable set `s` of finite measure, the probability that
`s` holds and `S` crosses the line `a + b V` at some time is at most `l₀ exp (-a D b) P s`, with
`D` the decay transform and `exp (-∞) = 0`. -/
theorem measure_inter_exists_add_mul_le_le (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩) (hP : P ∈ 𝒩)
    (hV : ∀ n, 0 ≤ᵐ[P] V n) (hl₀ : 1 ≤ l₀) (hl₀' : l₀ ≠ ∞) (ha : 0 ≤ a) (b : ℝ)
    (hs : MeasurableSet[ℱ 0] s) (hPs : P s ≠ ∞) :
    P (s ∩ {ω | ∃ n, a + b * V n ω ≤ S n ω}) ≤
      l₀ * EReal.exp (-(a * decayTransform ψ Λ b)) * P s := by
  set A := {t | t ∈ Λ ∧ 0 < t ∧ ψ t ≤ b * t}
  rcases A.eq_empty_or_nonempty with hA | hA
  · -- no parameter qualifies: `D b = 0` and the bound is `l₀ P s ≥ P s`
    have hD : decayTransform ψ Λ b = 0 := by
      rw [decayTransform_def, show {t | t ∈ Λ ∧ 0 < t ∧ ψ t ≤ b * t} = A from rfl, hA,
        image_empty]
      simp
    rw [hD, EReal.coe_ennreal_zero, mul_zero, neg_zero, EReal.exp_zero, mul_one]
    exact (measure_mono Set.inter_subset_left).trans (le_mul_of_one_le_left zero_le hl₀)
  -- `g x = l₀ exp (-a x) P s` is antitone and continuous on `ℝ≥0∞`, so it maps the supremum
  -- `D b` to the infimum of the bounds `l₀ exp (-a t) P s` at the parameters `t`
  set g : ℝ≥0∞ → ℝ≥0∞ := fun x ↦ l₀ * EReal.exp (-((ENNReal.ofReal a * x : ℝ≥0∞) : EReal)) * P s
  have hg_anti : Antitone g := fun x y hxy ↦ by
    have : ((ENNReal.ofReal a * x : ℝ≥0∞) : EReal) ≤ ((ENNReal.ofReal a * y : ℝ≥0∞) : EReal) :=
      EReal.coe_ennreal_le_coe_ennreal_iff.2 (mul_le_mul_right hxy _)
    exact mul_le_mul_left (mul_le_mul_right (EReal.exp_monotone (EReal.neg_le_neg_iff.2 this)) _)
      _
  have hg_cont : Continuous g :=
    (ENNReal.continuous_mul_const hPs).comp ((ENNReal.continuous_const_mul hl₀').comp
      (EReal.expHomeomorph.continuous.comp (continuous_neg.comp (continuous_coe_ennreal_ereal.comp
        (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top)))))
  have hgD : l₀ * EReal.exp (-(a * decayTransform ψ Λ b)) * P s = g (decayTransform ψ Λ b) := by
    simp only [g, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left ha]
  rw [hgD, decayTransform_def,
    hg_anti.map_csSup_of_continuousAt hg_cont.continuousAt (hA.image _) (OrderTop.bddAbove _)]
  refine le_csInf ((hA.image _).image _) ?_
  rintro _ ⟨_, ⟨t, ⟨htΛ, ht0, hψ⟩, rfl⟩, rfl⟩
  refine (h.measure_inter_exists_add_mul_le_le_of_mem hP hV htΛ ht0.le hψ a hs).trans_eq ?_
  simp only [g, ← ENNReal.ofReal_mul ha, EReal.coe_ennreal_ofReal,
    max_eq_left (mul_nonneg ha ht0.le), ← EReal.coe_neg, EReal.exp_coe]

/-- **The line-crossing inequality** [HRMS20, Theorem 1(a)]. Under every probability measure `P`
of the null, for an `l₀`-sub-ψ process with `1 ≤ l₀ < ∞` and a nonnegative intrinsic time `V`,
every intercept `a ≥ 0` and every slope `b`, the probability that `S` ever crosses the line
`a + b V` is at most `l₀ exp (-a D b)`, with `D` the decay transform and `exp (-∞) = 0`. -/
theorem measure_exists_add_mul_le_le (h : IsSubPsiProcess S V ψ Λ l₀ ℱ 𝒩) (hP : P ∈ 𝒩)
    [IsProbabilityMeasure P] (hV : ∀ n, 0 ≤ᵐ[P] V n) (hl₀ : 1 ≤ l₀) (hl₀' : l₀ ≠ ∞) (ha : 0 ≤ a)
    (b : ℝ) :
    P {ω | ∃ n, a + b * V n ω ≤ S n ω} ≤ l₀ * EReal.exp (-(a * decayTransform ψ Λ b)) := by
  simpa using h.measure_inter_exists_add_mul_le_le hP hV hl₀ hl₀' ha b MeasurableSet.univ
    (measure_ne_top P univ)

end IsSubPsiProcess

/-! ### Instances -/

/-- **The partial sums are sub-ψ for the null of the sub-ψ bets.** If each observation `X k` is
`ℱ (k + 1)`-measurable, then the partial sums `∑ k < n, X k`, with the intrinsic time `n`, are a
`1`-sub-ψ process on `Λ` under every member of the null of the sub-ψ bets: the exponential
process is itself a test supermartingale. -/
theorem isSubPsiProcess_sum_condEVarNull (hX : ∀ k, Measurable[ℱ (k + 1)] (X k)) :
    IsSubPsiProcess (fun n ω ↦ ∑ k ∈ range n, X k ω) (fun n _ ↦ n) ψ Λ 1 ℱ
      (condEVarNull (subPsiBets ψ Λ) X ℱ) := fun P hP t ht ↦
  ⟨_, ((isTestSupermartingale_exp_sum_condEVarNull hX ht).anti_set
      (singleton_subset_iff.2 hP)).toIsENNSupermartingale,
    ae_of_all _ fun _ ↦ by simp, fun n ↦ ae_of_all _ fun _ ↦ by simp [mul_comm]⟩

/-- **Freedman's sums are sub-Poisson** [Fre75; HRMS20, Fact 1(c)]. Let `X n` be
`ℱ (n + 1)`-measurable, with `X n ^ 2` integrable, `E[X n | ℱ n] ≤ 0` and `X n ≤ b` almost surely,
with `b > 0`: supermartingale differences bounded above. The partial sums `∑ k < n, X k`, with
the intrinsic time `∑ k < n, E[X k ^ 2 | ℱ k]`, are a `1`-sub-ψ process on `[0, ∞)` for
`ψ t = (exp (t b) - 1 - t b) / b ^ 2`. -/
theorem isSubPsiProcess_sum_sum_condExp_sq {μ : Measure Ω} [IsFiniteMeasure μ] (hb : 0 < b)
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n)) (hX2 : ∀ n, Integrable (fun ω ↦ X n ω ^ 2) μ)
    (h_mean : ∀ n, μ[X n | ℱ n] ≤ᵐ[μ] 0) (h_bdd : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ b) :
    IsSubPsiProcess (fun n ω ↦ ∑ k ∈ range n, X k ω)
      (fun n ω ↦ ∑ k ∈ range n, μ[fun ω ↦ X k ω ^ 2 | ℱ k] ω)
      (fun t ↦ (exp (t * b) - 1 - t * b) / b ^ 2) (Ici 0) 1 ℱ {μ} := by
  rintro _ rfl t ht
  exact ⟨_, (LMLExplore.supermartingale_exp_mul_sum_sub_mul_sum_condExp_sq hb (mem_Ici.1 ht) le_rfl
      hX hX2 h_mean h_bdd).isENNSupermartingale_ofReal fun n ↦ ae_of_all _ fun _ ↦ (exp_pos _).le,
    ae_of_all _ fun _ ↦ by simp, fun n ↦ ae_of_all _ fun _ ↦ le_rfl⟩

/-- **The line-crossing inequality for the one-sided conditionally sub-Gaussian null**
[HRMS20, Theorem 1(a)]. Under every member of `oneSidedCondSubgaussianNull`, for an intercept
`a ≥ 0` and every slope `b`, the probability that the random walk `∑ k < n, ω k` ever crosses the
line `a + b n` is at most `exp (-2 a b)`. -/
theorem measure_exists_add_mul_le_sum_le_of_mem_oneSidedCondSubgaussianNull
    {P : Measure (ℕ → ℝ)} (hP : P ∈ oneSidedCondSubgaussianNull) (ha : 0 ≤ a) (b : ℝ) :
    P {ω | ∃ n : ℕ, a + b * n ≤ ∑ k ∈ range n, ω k} ≤ ENNReal.ofReal (exp (-(2 * a * b))) := by
  have := isProbabilityMeasure_of_mem_oneSidedCondSubgaussianNull hP
  rcases lt_or_ge b 0 with hb | hb
  · -- for a negative slope the bound is at least `1`
    exact prob_le_one.trans (ENNReal.one_le_ofReal.2 (one_le_exp (by nlinarith)))
  have hsub := isSubPsiProcess_sum_condEVarNull (ψ := fun t ↦ t ^ 2 / 2) (Λ := Ici 0)
    (ℱ := Filtration.piLT) (X := fun k ω ↦ ω k)
    fun k ↦ Filtration.measurable_piLT_apply k.lt_succ_self
  rw [← oneSidedCondSubgaussianNull_eq_condEVarNull] at hsub
  have h := hsub.measure_exists_add_mul_le_le hP (fun n ↦ ae_of_all _ fun _ ↦ Nat.cast_nonneg n)
    le_rfl ENNReal.one_ne_top ha b
  rw [decayTransform_sq_div_two, EReal.coe_ennreal_ofReal, max_eq_left (by linarith), one_mul,
    ← EReal.coe_mul, ← EReal.coe_neg, EReal.exp_coe] at h
  convert h using 3
  ring

end ProbabilityTheory
