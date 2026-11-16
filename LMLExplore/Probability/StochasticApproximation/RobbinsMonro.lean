/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Martingale.RobbinsSiegmund
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.PSeries

/-!
# The Robbins–Monro theorem

Let `h : E → E` be a vector field on a separable real Hilbert space `E` with a root `z`, towards
which it points uniformly on annuli: `⟪y - z, h y⟫` is bounded below by a positive constant on
each annulus `ε ≤ ‖y - z‖ ≤ ε⁻¹`. The Robbins–Monro recursion
`x (n + 1) = x n - α n • (h (x n) + ξ (n + 1))`
looks for `z` from noisy evaluations of `h`. The noise `ξ (n + 1)` is a martingale difference for
a filtration `ℱ`, with conditional second moment `E[‖ξ (n + 1)‖² | ℱ n] ≤ A + B ‖x n - z‖²`. If
`h` is measurable and grows at most linearly, `‖h y‖ ≤ C (1 + ‖y - z‖)`, if `x 0` is
square-integrable, and if the deterministic step sizes satisfy `∑ α n = ∞` and `∑ α n ^ 2 < ∞`,
then `x n` converges to `z` almost surely [RM51], [KY03, Chapter 5].

This is the basic convergence theorem of stochastic approximation: temporal-difference learning
with linear features, for instance, is a Robbins–Monro recursion for the root of the expected
temporal-difference update. For `h y = y - z` and the steps `1 / (n + 1)`, the recursion computes
running means, and the theorem is a strong law of large numbers for martingale differences with
bounded conditional second moments.

## Main statements

* `LMLExplore.ae_tendsto_of_not_summable_of_summable_sq`: the Robbins–Monro theorem.
* `LMLExplore.strong_law_ae_of_condExp_eq`: the running means of random variables with conditional
  mean `z` and bounded conditional second moments converge to `z` almost surely.

## Implementation notes

The step sizes and the constants `A`, `B`, `C` take values in `ℝ≥0`. The conditional second
moment of the noise is the conditional expectation `condLExp` of `‖ξ (n + 1)‖ₑ ^ 2`, which is
meaningful without integrability. Together with the integrability of `‖x 0 - z‖ ^ 2`, it makes
every iterate square-integrable, so that the conditional expectation of the cross term
`⟪x n - z, ξ (n + 1)⟫` vanishes. No finite dimension is needed: the space is complete and second
countable, as every finite-dimensional one is.

The theorem follows from the Robbins–Siegmund theorem
`LMLExplore.ae_exists_tendsto_and_summable_of_condLExp_add_le`, applied to the squared distance
`V n = ‖x n - z‖²`. Expanding the square and taking conditional expectations gives
`E[V (n + 1) | ℱ n] + 2 α n ⟪x n - z, h (x n)⟫ ≤ (1 + a n) V n + b n`, with
`a n = α n ^ 2 (4 C² + 2 B)` and `b n = α n ^ 2 (4 C² + 2 A)`. Hence, almost surely, `V n`
converges and `∑ α n ⟪x n - z, h (x n)⟫ < ∞`. Since `∑ α n = ∞`, a positive limit of `V n`
would keep `x n` in an annulus around `z`, on which the inner products are bounded below, and
make this sum infinite.

## References

* [RM51] H. Robbins and S. Monro, *A stochastic approximation method*, Ann. Math. Statist. 22
  (1951), 400–407.
* [KY03] H. J. Kushner and G. G. Yin, *Stochastic Approximation and Recursive Algorithms and
  Applications*, 2nd ed., Springer (2003).
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {h : E → E} {z : E} {C : ℝ≥0}

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℕ mΩ}
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  {x ξ : ℕ → Ω → E} {α : ℕ → ℝ≥0} {A B : ℝ≥0}

namespace RobbinsMonro

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- One step of the recursion, with `u = x n - z`, `v = h (x n)` and `w = ξ (n + 1)`: the new
squared distance plus the drift term is at most the old squared distance plus the cross term and the
squared step. -/
private lemma norm_sub_smul_sq_add_le (u v w : E) (a : ℝ) :
    ‖u - a • (v + w)‖ ^ 2 + 2 * a * ⟪u, v⟫
      ≤ ‖u‖ ^ 2 + -(2 * a) * ⟪u, w⟫ + 2 * a ^ 2 * ‖v‖ ^ 2 + 2 * a ^ 2 * ‖w‖ ^ 2 := by
  have hvw : ‖v + w‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
    have := norm_add_le v w
    nlinarith [norm_nonneg (v + w), norm_nonneg v, norm_nonneg w, sq_nonneg (‖v‖ - ‖w‖)]
  rw [norm_sub_sq_real, inner_smul_right, inner_add_right, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs]
  nlinarith [sq_nonneg a]

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- The linear growth bound, squared. -/
private lemma norm_sq_le (hh_le : ∀ y, ‖h y‖ ≤ C * (1 + ‖y - z‖)) (y : E) :
    ‖h y‖ ^ 2 ≤ 2 * C ^ 2 * (1 + ‖y - z‖ ^ 2) := by
  have h1 := hh_le y
  have h0 : 0 ≤ C * (1 + ‖y - z‖) := (norm_nonneg _).trans h1
  nlinarith [norm_nonneg (h y), sq_nonneg (‖y - z‖ - 1), pow_le_pow_left₀ (norm_nonneg _) h1 2]

/-- Every interval `[s, t]` with `0 < s` and `0 < t` lies in an annulus `[ε, ε⁻¹]` with
`0 < ε < 1`. -/
private lemma exists_annulus {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ∃ ε ∈ Set.Ioo (0 : ℝ) 1, ε ≤ s ∧ t ≤ ε⁻¹ := by
  have hε : 0 < min (min s t⁻¹) (1 / 2) := lt_min (lt_min hs (inv_pos.2 ht)) one_half_pos
  refine ⟨_, ⟨hε, (min_le_right _ _).trans_lt one_half_lt_one⟩,
    (min_le_left _ _).trans (min_le_left _ _), ?_⟩
  rw [le_inv_comm₀ ht hε]
  exact (min_le_left _ _).trans (min_le_right _ _)

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- A field pointing towards `z` uniformly on annuli points towards `z` everywhere. -/
private lemma inner_nonneg
    (hh_inner : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∃ c > 0, ∀ y, ε ≤ ‖y - z‖ → ‖y - z‖ ≤ ε⁻¹ →
      c ≤ ⟪y - z, h y⟫) (y : E) :
    0 ≤ ⟪y - z, h y⟫ := by
  rcases eq_or_ne y z with rfl | hy
  · simp
  have hr : 0 < ‖y - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  obtain ⟨ε, hε, hεs, hεt⟩ := exists_annulus hr hr
  obtain ⟨c, hc, hcy⟩ := hh_inner ε hε
  exact hc.le.trans (hcy y hεs hεt)

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- The drift term `2 a ⟪y - z, h y⟫` of a step is nonnegative. -/
private lemma drift_nonneg
    (hh_inner : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∃ c > 0, ∀ y, ε ≤ ‖y - z‖ → ‖y - z‖ ≤ ε⁻¹ →
      c ≤ ⟪y - z, h y⟫) (a : ℝ≥0) (y : E) :
    0 ≤ 2 * (a : ℝ) * ⟪y - z, h y⟫ :=
  mul_nonneg (by positivity) (inner_nonneg hh_inner y)

/-- The iterates are adapted. -/
private lemma measurable_iterate
    (hx : ∀ n ω, x (n + 1) ω = x n ω - α n • (h (x n ω) + ξ (n + 1) ω))
    (hx0 : Measurable[ℱ 0] (x 0)) (hh : Measurable h)
    (hξ : ∀ n, Measurable[ℱ (n + 1)] (ξ (n + 1))) (n : ℕ) :
    Measurable[ℱ n] (x n) := by
  induction n with
  | zero => exact hx0
  | succ n ih =>
    have ih' : Measurable[ℱ (n + 1)] (x n) := ih.mono (ℱ.mono n.le_succ) le_rfl
    rw [funext (hx n)]
    exact ih'.sub (((hh.comp ih').add (hξ n)).const_smul _)

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- The noise has a finite second moment when the current iterate does. -/
private lemma lintegral_enorm_noise_sq_lt_top [IsFiniteMeasure P]
    (hξ_var : ∀ n, P⁻[fun ω ↦ ‖ξ (n + 1) ω‖ₑ ^ 2 | ℱ n] ≤ᵐ[P] fun ω ↦ A + B * ‖x n ω - z‖ₑ ^ 2)
    {n : ℕ} (hxn : Integrable (fun ω ↦ ‖x n ω - z‖ ^ 2) P) :
    ∫⁻ ω, ‖ξ (n + 1) ω‖ₑ ^ 2 ∂P < ∞ := by
  have hfin := hasFiniteIntegral_iff_eNorm.1 hxn.2
  simp only [eNorm_pow, eNorm_norm] at hfin
  calc ∫⁻ ω, ‖ξ (n + 1) ω‖ₑ ^ 2 ∂P
      = ∫⁻ ω, P⁻[fun ω ↦ ‖ξ (n + 1) ω‖ₑ ^ 2 | ℱ n] ω ∂P := (lintegral_condLExp (ℱ.le n) _ _).symm
    _ ≤ ∫⁻ ω, (A + B * ‖x n ω - z‖ₑ ^ 2) ∂P := lintegral_mono_ae (hξ_var n)
    _ < ∞ := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      exact ENNReal.add_lt_top.2 ⟨by simp [ENNReal.mul_lt_top_iff, measure_lt_top],
        ENNReal.mul_lt_top ENNReal.coe_lt_top hfin⟩

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
/-- The noise is square-integrable when the current iterate is. -/
private lemma integrable_norm_noise_sq [IsFiniteMeasure P]
    (hξ : ∀ n, Measurable[ℱ (n + 1)] (ξ (n + 1)))
    (hξ_var : ∀ n, P⁻[fun ω ↦ ‖ξ (n + 1) ω‖ₑ ^ 2 | ℱ n] ≤ᵐ[P] fun ω ↦ A + B * ‖x n ω - z‖ₑ ^ 2)
    {n : ℕ} (hxn : Integrable (fun ω ↦ ‖x n ω - z‖ ^ 2) P) :
    Integrable (fun ω ↦ ‖ξ (n + 1) ω‖ ^ 2) P := by
  refine ⟨((hξ n).mono (ℱ.le _) le_rfl).norm.pow_const 2 |>.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_eNorm]
  simpa only [eNorm_pow, eNorm_norm] using lintegral_enorm_noise_sq_lt_top hξ_var hxn

/-- The noise is integrable, and so is the cross term `⟪x n - z, ξ (n + 1)⟫`, whose conditional
expectation given `ℱ n` vanishes. -/
private lemma condExp_inner_noise [IsFiniteMeasure P] [CompleteSpace E]
    (hxm : ∀ n, Measurable[ℱ n] (x n)) (hξ : ∀ n, Measurable[ℱ (n + 1)] (ξ (n + 1)))
    (hξ_mean : ∀ n, P[ξ (n + 1) | ℱ n] =ᵐ[P] 0)
    (hξ_var : ∀ n, P⁻[fun ω ↦ ‖ξ (n + 1) ω‖ₑ ^ 2 | ℱ n] ≤ᵐ[P] fun ω ↦ A + B * ‖x n ω - z‖ₑ ^ 2)
    {n : ℕ} (hxn : Integrable (fun ω ↦ ‖x n ω - z‖ ^ 2) P) :
    Integrable (fun ω ↦ ⟪x n ω - z, ξ (n + 1) ω⟫) P ∧
      P[fun ω ↦ ⟪x n ω - z, ξ (n + 1) ω⟫ | ℱ n] =ᵐ[P] 0 := by
  have hξn : Measurable (ξ (n + 1)) := (hξ n).mono (ℱ.le _) le_rfl
  have hξ2 := integrable_norm_noise_sq hξ hξ_var hxn
  have hξ1 : Integrable (ξ (n + 1)) P :=
    ((memLp_two_iff_integrable_sq_norm hξn.aestronglyMeasurable).2 hξ2).integrable one_le_two
  have hG : Integrable (fun ω ↦ ⟪x n ω - z, ξ (n + 1) ω⟫) P := by
    refine (hxn.add hξ2).mono'
      ((((hxm n).mono (ℱ.le n) le_rfl).sub_const z).inner hξn).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ ?_)
    have := abs_real_inner_le_norm (x n ω - z) (ξ (n + 1) ω)
    simp only [Pi.add_apply, Real.norm_eq_abs]
    nlinarith [sq_nonneg (‖x n ω - z‖ - ‖ξ (n + 1) ω‖), norm_nonneg (x n ω - z),
      norm_nonneg (ξ (n + 1) ω)]
  refine ⟨hG, ?_⟩
  have := condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) (m := ℱ n) (μ := P)
    ((hxm n).sub_const z).stronglyMeasurable hG hξ1
  filter_upwards [this, hξ_mean n] with ω h1 h2
  refine h1.trans ?_
  simp [h2]

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
/-- The conditional second moment of the noise, in real form. -/
private lemma condExp_norm_noise_sq_le [IsFiniteMeasure P]
    (hξ : ∀ n, Measurable[ℱ (n + 1)] (ξ (n + 1)))
    (hξ_var : ∀ n, P⁻[fun ω ↦ ‖ξ (n + 1) ω‖ₑ ^ 2 | ℱ n] ≤ᵐ[P] fun ω ↦ A + B * ‖x n ω - z‖ₑ ^ 2)
    {n : ℕ} (hxn : Integrable (fun ω ↦ ‖x n ω - z‖ ^ 2) P) :
    P[fun ω ↦ ‖ξ (n + 1) ω‖ ^ 2 | ℱ n] ≤ᵐ[P] fun ω ↦ A + B * ‖x n ω - z‖ ^ 2 := by
  have hξn : Measurable (ξ (n + 1)) := (hξ n).mono (ℱ.le _) le_rfl
  filter_upwards [toReal_condLExp (ℱ n) (by fun_prop)
    (lintegral_enorm_noise_sq_lt_top hξ_var hxn).ne, hξ_var n] with ω e1 e2
  have e3 : (fun ω ↦ ‖ξ (n + 1) ω‖ ^ 2) = fun ω ↦ (‖ξ (n + 1) ω‖ₑ ^ 2).toReal := by
    funext ω
    simp [ENNReal.toReal_pow]
  rw [e3, ← e1]
  refine (ENNReal.toReal_mono (by finiteness) e2).trans_eq ?_
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp [ENNReal.toReal_pow]

/-- The conditional step of the recursion, in real form: the new squared distance plus the drift
term is integrable, and its conditional expectation is at most
`(1 + α n ^ 2 (4 C² + 2 B)) ‖x n - z‖² + α n ^ 2 (4 C² + 2 A)`. -/
private lemma condExp_step_le [IsFiniteMeasure P] [CompleteSpace E]
    (hx : ∀ n ω, x (n + 1) ω = x n ω - α n • (h (x n ω) + ξ (n + 1) ω))
    (hxm : ∀ n, Measurable[ℱ n] (x n)) (hh : Measurable h) (hh_le : ∀ y, ‖h y‖ ≤ C * (1 + ‖y - z‖))
    (hh_inner : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∃ c > 0, ∀ y, ε ≤ ‖y - z‖ → ‖y - z‖ ≤ ε⁻¹ →
      c ≤ ⟪y - z, h y⟫)
    (hξ : ∀ n, Measurable[ℱ (n + 1)] (ξ (n + 1))) (hξ_mean : ∀ n, P[ξ (n + 1) | ℱ n] =ᵐ[P] 0)
    (hξ_var : ∀ n, P⁻[fun ω ↦ ‖ξ (n + 1) ω‖ₑ ^ 2 | ℱ n] ≤ᵐ[P] fun ω ↦ A + B * ‖x n ω - z‖ₑ ^ 2)
    {n : ℕ} (hxn : Integrable (fun ω ↦ ‖x n ω - z‖ ^ 2) P) :
    Integrable (fun ω ↦ ‖x (n + 1) ω - z‖ ^ 2 + 2 * α n * ⟪x n ω - z, h (x n ω)⟫) P ∧
    P[fun ω ↦ ‖x (n + 1) ω - z‖ ^ 2 + 2 * α n * ⟪x n ω - z, h (x n ω)⟫ | ℱ n] ≤ᵐ[P]
      fun ω ↦ (1 + α n ^ 2 * (4 * C ^ 2 + 2 * B)) * ‖x n ω - z‖ ^ 2
        + α n ^ 2 * (4 * C ^ 2 + 2 * A) := by
  have hm := ℱ.le n
  have hxn' : Measurable (x n) := (hxm n).mono hm le_rfl
  have hξ2 := integrable_norm_noise_sq hξ hξ_var hxn
  have hh2 : Integrable (fun ω ↦ ‖h (x n ω)‖ ^ 2) P := by
    refine (((integrable_const 1).add hxn).const_mul (2 * C ^ 2 : ℝ)).mono'
      ((hh.comp hxn').norm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact norm_sq_le hh_le _
  obtain ⟨hG, hGc⟩ := condExp_inner_noise hxm hξ hξ_mean hξ_var hxn
  set G := fun ω ↦ ⟪x n ω - z, ξ (n + 1) ω⟫
  -- the bound `Z` and its conditional expectation
  set W := fun ω ↦ ‖x n ω - z‖ ^ 2 + 2 * (α n : ℝ) ^ 2 * ‖h (x n ω)‖ ^ 2
  set N := fun ω ↦ ‖ξ (n + 1) ω‖ ^ 2
  set Z := W + (-(2 * α n : ℝ)) • G + (2 * (α n : ℝ) ^ 2) • N
  have hW : Integrable W P := hxn.add (hh2.const_mul _)
  have hWm : StronglyMeasurable[ℱ n] W := by
    have h1 : Measurable[ℱ n] fun ω ↦ ‖x n ω - z‖ ^ 2 :=
      (measurable_norm.pow_const 2).comp ((hxm n).sub_const z)
    have h2 : Measurable[ℱ n] fun ω ↦ ‖h (x n ω)‖ ^ 2 :=
      (measurable_norm.pow_const 2).comp (hh.comp (hxm n))
    exact (h1.add (h2.const_mul _)).stronglyMeasurable
  have hZ : Integrable Z P := (hW.add (hG.smul _)).add (hξ2.smul _)
  have hZc : P[Z | ℱ n] =ᵐ[P] fun ω ↦ W ω + 2 * (α n : ℝ) ^ 2 * P[N | ℱ n] ω := by
    filter_upwards [condExp_add (hW.add (hG.smul (-(2 * α n : ℝ))))
        (hξ2.smul (2 * (α n : ℝ) ^ 2)) (ℱ n),
      condExp_add hW (hG.smul (-(2 * α n : ℝ))) (ℱ n),
      condExp_smul (μ := P) (-(2 * α n : ℝ)) G (ℱ n),
      condExp_smul (μ := P) (2 * (α n : ℝ) ^ 2) N (ℱ n), hGc] with ω e1 e2 e3 e4 e5
    simp only [Z, e1, Pi.add_apply, e2, condExp_of_stronglyMeasurable hm hWm hW, e3, e4,
      Pi.smul_apply, e5, Pi.zero_apply, smul_eq_mul]
    ring
  have hNc := condExp_norm_noise_sq_le hξ hξ_var hxn
  -- the pointwise bound on the step
  have hle : ∀ ω, ‖x (n + 1) ω - z‖ ^ 2 + 2 * α n * ⟪x n ω - z, h (x n ω)⟫ ≤ Z ω := by
    intro ω
    have := norm_sub_smul_sq_add_le (x n ω - z) (h (x n ω)) (ξ (n + 1) ω) (α n)
    have hx' : x (n + 1) ω - z = x n ω - z - (α n : ℝ) • (h (x n ω) + ξ (n + 1) ω) := by
      rw [hx n ω, NNReal.smul_def]
      abel
    simp only [Z, W, G, N, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx']
    linarith
  have hR0 : ∀ ω, 0 ≤ ‖x (n + 1) ω - z‖ ^ 2 + 2 * α n * ⟪x n ω - z, h (x n ω)⟫ := fun ω ↦
    add_nonneg (sq_nonneg _) (drift_nonneg hh_inner _ _)
  have hR : Integrable (fun ω ↦ ‖x (n + 1) ω - z‖ ^ 2 + 2 * α n * ⟪x n ω - z, h (x n ω)⟫) P :=
    hZ.mono' ((((hxm (n + 1)).mono (ℱ.le _) le_rfl).sub_const z).norm.pow_const 2 |>.add
      (((hxn'.sub_const z).inner (hh.comp hxn')).const_mul _)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by rw [Real.norm_of_nonneg (hR0 ω)]; exact hle ω)
  refine ⟨hR, ?_⟩
  filter_upwards [condExp_mono hR hZ (ae_of_all _ hle), hZc, hNc] with ω e1 e2 e3
  have hh2ω := norm_sq_le hh_le (x n ω)
  have hα2 : 0 ≤ (α n : ℝ) ^ 2 := sq_nonneg _
  refine e1.trans (e2.trans_le ?_)
  simp only [W]
  nlinarith [mul_le_mul_of_nonneg_left e3 hα2, mul_le_mul_of_nonneg_left hh2ω hα2]

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- If the squared distances `‖u n - z‖²` converge and the drift terms `2 α n ⟪u n - z, h (u n)⟫`
are summable while `α` is not, then `u n` converges to `z`. -/
private lemma tendsto_of_tendsto_norm_sq (hα : ¬ Summable α)
    (hh_inner : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∃ c > 0, ∀ y, ε ≤ ‖y - z‖ → ‖y - z‖ ≤ ε⁻¹ →
      c ≤ ⟪y - z, h y⟫)
    {u : ℕ → E} {l : ℝ≥0} (hV : Tendsto (fun n ↦ ‖u n - z‖₊ ^ 2) atTop (𝓝 l))
    (hc : Summable fun n ↦ 2 * α n * (⟪u n - z, h (u n)⟫).toNNReal) :
    Tendsto u atTop (𝓝 z) := by
  have hr : Tendsto (fun n ↦ ‖u n - z‖) atTop (𝓝 (NNReal.sqrt l : ℝ)) := by
    have := (NNReal.continuous_coe.tendsto _).comp ((NNReal.continuous_sqrt.tendsto l).comp hV)
    simpa [Function.comp_def] using this
  rcases eq_or_ne l 0 with rfl | hl
  · simpa [tendsto_iff_norm_sub_tendsto_zero] using hr
  -- a positive limit keeps `u n` in an annulus, where the drift is bounded below
  set r : ℝ := (NNReal.sqrt l : ℝ)
  have hr0 : 0 < r := NNReal.coe_pos.2 (NNReal.sqrt_pos.2 (pos_iff_ne_zero.2 hl))
  obtain ⟨ε, hε, hεs, hεt⟩ := exists_annulus (s := r / 2) (t := 2 * r) (by positivity)
    (by positivity)
  obtain ⟨c, hc0, hcy⟩ := hh_inner ε hε
  have hev : ∀ᶠ n in atTop, ‖u n - z‖ ∈ Set.Ioo (r / 2) (2 * r) :=
    hr (Ioo_mem_nhds (by linarith) (by linarith))
  refine absurd ?_ hα
  refine NNReal.summable_coe.1 <| Summable.of_norm_bounded_eventually_nat
    ((NNReal.summable_coe.2 hc).mul_left (2 * c)⁻¹) (hev.mono fun n hn ↦ ?_)
  have hcn : c ≤ ⟪u n - z, h (u n)⟫ := hcy _ (hεs.trans hn.1.le) (hn.2.le.trans hεt)
  rw [Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  push_cast
  rw [Real.coe_toNNReal _ (hc0.le.trans hcn), ← mul_assoc, ← mul_assoc]
  calc (α n : ℝ) = (2 * c)⁻¹ * 2 * α n * c := by field_simp
    _ ≤ (2 * c)⁻¹ * 2 * α n * ⟪u n - z, h (u n)⟫ := by gcongr

/-- The conditional step of the recursion, in the form of the Robbins–Siegmund theorem. -/
private lemma condLExp_step_le [IsFiniteMeasure P] [CompleteSpace E]
    (hx : ∀ n ω, x (n + 1) ω = x n ω - α n • (h (x n ω) + ξ (n + 1) ω))
    (hxm : ∀ n, Measurable[ℱ n] (x n)) (hh : Measurable h) (hh_le : ∀ y, ‖h y‖ ≤ C * (1 + ‖y - z‖))
    (hh_inner : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∃ c > 0, ∀ y, ε ≤ ‖y - z‖ → ‖y - z‖ ≤ ε⁻¹ →
      c ≤ ⟪y - z, h y⟫)
    (hξ : ∀ n, Measurable[ℱ (n + 1)] (ξ (n + 1))) (hξ_mean : ∀ n, P[ξ (n + 1) | ℱ n] =ᵐ[P] 0)
    (hξ_var : ∀ n, P⁻[fun ω ↦ ‖ξ (n + 1) ω‖ₑ ^ 2 | ℱ n] ≤ᵐ[P] fun ω ↦ A + B * ‖x n ω - z‖ₑ ^ 2)
    {n : ℕ} (hxn : Integrable (fun ω ↦ ‖x n ω - z‖ ^ 2) P) :
    P⁻[fun ω ↦ ((‖x (n + 1) ω - z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) | ℱ n]
        + (fun ω ↦ ((2 * α n * (⟪x n ω - z, h (x n ω)⟫).toNNReal : ℝ≥0) : ℝ≥0∞))
      ≤ᵐ[P] fun ω ↦ (((1 + α n ^ 2 * (4 * C ^ 2 + 2 * B)) * ‖x n ω - z‖₊ ^ 2
        + α n ^ 2 * (4 * C ^ 2 + 2 * A) : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨hR, hRc⟩ := condExp_step_le hx hxm hh hh_le hh_inner hξ hξ_mean hξ_var hxn
  set Y := fun ω ↦ ((2 * α n * (⟪x n ω - z, h (x n ω)⟫).toNNReal : ℝ≥0) : ℝ≥0∞)
  have hY : Measurable[ℱ n] Y :=
    measurable_coe_nnreal_ennreal.comp
      ((((hxm n).sub_const z).inner (hh.comp (hxm n))).real_toNNReal.const_mul _)
  have hsum : (fun ω ↦ ((‖x (n + 1) ω - z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)) + Y
      = fun ω ↦ ENNReal.ofReal (‖x (n + 1) ω - z‖ ^ 2 + 2 * α n * ⟪x n ω - z, h (x n ω)⟫) := by
    funext ω
    rw [Pi.add_apply, ← ENNReal.coe_add, ← ENNReal.ofReal_coe_nnreal]
    push_cast
    rw [Real.coe_toNNReal _ (inner_nonneg hh_inner _)]
  have hR0 : 0 ≤ᵐ[P] fun ω ↦ ‖x (n + 1) ω - z‖ ^ 2 + 2 * α n * ⟪x n ω - z, h (x n ω)⟫ :=
    ae_of_all _ fun ω ↦ add_nonneg (sq_nonneg _) (drift_nonneg hh_inner _ _)
  filter_upwards [condLExp_add_right (fun ω ↦ ((‖x (n + 1) ω - z‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞))
      (hY.mono (ℱ.le n) le_rfl).aemeasurable (mΩ := ℱ n) (P := P),
    condLExp_ofReal (ℱ n) hR hR0, hRc] with ω e1 e2 e3
  rw [condLExp_eq_self (ℱ.le n) P hY, hsum, e2] at e1
  rw [← e1, ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal (e3.trans_eq ?_)
  push_cast
  ring

end RobbinsMonro

open RobbinsMonro in
/-- **The Robbins–Monro theorem** [RM51], [KY03, Chapter 5]. Let `h : E → E` be a measurable
vector field on a separable real Hilbert space, with linear growth `‖h y‖ ≤ C (1 + ‖y - z‖)` and
pointing towards `z` uniformly on annuli: on each annulus `ε ≤ ‖y - z‖ ≤ ε⁻¹` with `0 < ε < 1`,
`⟪y - z, h y⟫` is bounded below by a positive constant. Let the iterates follow
`x (n + 1) = x n - α n • (h (x n) + ξ (n + 1))`, with `x 0` measurable for `ℱ 0` and
`‖x 0 - z‖ ^ 2` integrable, and with a martingale-difference noise: `ξ (n + 1)` is measurable for
`ℱ (n + 1)`, `E[ξ (n + 1) | ℱ n] = 0` and `E[‖ξ (n + 1)‖² | ℱ n] ≤ A + B ‖x n - z‖²`, the latter
in the sense of `condLExp`. If the deterministic step sizes satisfy `∑ α n = ∞` and
`∑ α n ^ 2 < ∞`, then `x n` converges to `z` almost surely. -/
theorem ae_tendsto_of_not_summable_of_summable_sq [IsFiniteMeasure P] [CompleteSpace E]
    (hx : ∀ n ω, x (n + 1) ω = x n ω - α n • (h (x n ω) + ξ (n + 1) ω))
    (hx0 : Measurable[ℱ 0] (x 0)) (hx0_int : Integrable (fun ω ↦ ‖x 0 ω - z‖ ^ 2) P)
    (hh : Measurable h) (hh_le : ∀ y, ‖h y‖ ≤ C * (1 + ‖y - z‖))
    (hh_inner : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∃ c > 0, ∀ y, ε ≤ ‖y - z‖ → ‖y - z‖ ≤ ε⁻¹ →
      c ≤ ⟪y - z, h y⟫)
    (hξ : ∀ n, Measurable[ℱ (n + 1)] (ξ (n + 1))) (hξ_mean : ∀ n, P[ξ (n + 1) | ℱ n] =ᵐ[P] 0)
    (hξ_var : ∀ n, P⁻[fun ω ↦ ‖ξ (n + 1) ω‖ₑ ^ 2 | ℱ n] ≤ᵐ[P] fun ω ↦ A + B * ‖x n ω - z‖ₑ ^ 2)
    (hα : ¬ Summable α) (hα2 : Summable fun n ↦ α n ^ 2) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ x n ω) atTop (𝓝 z) := by
  have hxm := measurable_iterate hx hx0 hh hξ
  -- every iterate is square-integrable
  have hint : ∀ n, Integrable (fun ω ↦ ‖x n ω - z‖ ^ 2) P := by
    intro n
    induction n with
    | zero => exact hx0_int
    | succ n ih =>
      refine (condExp_step_le hx hxm hh hh_le hh_inner hξ hξ_mean hξ_var ih).1.mono'
        ((measurable_norm.pow_const 2).comp
          (((hxm (n + 1)).mono (ℱ.le _) le_rfl).sub_const z)).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact le_add_of_nonneg_right (drift_nonneg hh_inner _ _)
  have hRS := ae_exists_tendsto_and_summable_of_condLExp_add_le (P := P) (ℱ := ℱ)
    (V := fun n ω ↦ ‖x n ω - z‖₊ ^ 2) (a := fun n _ ↦ α n ^ 2 * (4 * C ^ 2 + 2 * B))
    (b := fun n _ ↦ α n ^ 2 * (4 * C ^ 2 + 2 * A))
    (c := fun n ω ↦ 2 * α n * (⟪x n ω - z, h (x n ω)⟫).toNNReal)
    (fun n ↦ (measurable_nnNorm.pow_const 2).comp ((hxm n).sub_const z))
    (adapted_const' ℱ _) (adapted_const' ℱ _)
    (fun n ↦ (((hxm n).sub_const z).inner (hh.comp (hxm n))).real_toNNReal.const_mul _)
    (fun n ↦ condLExp_step_le hx hxm hh hh_le hh_inner hξ hξ_mean hξ_var (hint n))
  filter_upwards [hRS] with ω hω
  obtain ⟨⟨l, hl⟩, hc⟩ := hω (hα2.mul_right _) (hα2.mul_right _)
  exact tendsto_of_tendsto_norm_sq hα hh_inner hl hc

open RobbinsMonro in
/-- **The strong law of large numbers for martingale differences**, as the Robbins–Monro
recursion for the mean. If `Y (n + 1)` has conditional mean `z` given `ℱ n`, and the conditional
expectation of `‖Y (n + 1) - z‖ ^ 2` given `ℱ n` is at most `A`, then the running means
`(Y 1 + ⋯ + Y n) / n` converge to `z` almost surely. The variables need be neither independent
nor identically distributed, unlike in Mathlib's `ProbabilityTheory.strong_law_ae`. -/
theorem strong_law_ae_of_condExp_eq [IsFiniteMeasure P] [CompleteSpace E] {Y : ℕ → Ω → E}
    (hY : ∀ n, Measurable[ℱ (n + 1)] (Y (n + 1)))
    (hY_mean : ∀ n, P[Y (n + 1) | ℱ n] =ᵐ[P] fun _ ↦ z)
    (hY_var : ∀ n, P⁻[fun ω ↦ ‖Y (n + 1) ω - z‖ₑ ^ 2 | ℱ n] ≤ᵐ[P] fun _ ↦ A) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Y (k + 1) ω) atTop (𝓝 z) := by
  -- the noise `z - Y (n + 1)`, with conditional second moment at most `A + 0 * ‖x n - z‖ ^ 2`
  have hξ (n : ℕ) : Measurable[ℱ (n + 1)] fun ω ↦ z - Y (n + 1) ω := (hY n).const_sub z
  have hξ_var (x : ℕ → Ω → E) (n : ℕ) :
      P⁻[fun ω ↦ ‖z - Y (n + 1) ω‖ₑ ^ 2 | ℱ n]
        ≤ᵐ[P] fun ω ↦ A + (0 : ℝ≥0) * ‖x n ω - z‖ₑ ^ 2 := by
    simpa [eNorm_sub_rev z] using hY_var n
  have hint (n : ℕ) : Integrable (Y (n + 1)) P := by
    have h2 := integrable_norm_noise_sq (z := z) (ξ := fun n ω ↦ z - Y n ω) hξ
      (hξ_var fun _ _ ↦ z) (n := n) (by simp)
    have hm : Measurable (Y (n + 1)) := (hY n).mono (ℱ.le _) le_rfl
    have h1 := ((memLp_two_iff_integrable_sq_norm (hm.const_sub z).aestronglyMeasurable).2
      h2).integrable one_le_two
    refine ((integrable_const z).sub h1).congr (ae_of_all _ fun ω ↦ ?_)
    simp
  refine ae_tendsto_of_not_summable_of_summable_sq
    (x := fun (n : ℕ) ω ↦ (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Y (k + 1) ω) (ξ := fun n ω ↦ z - Y n ω)
    (h := fun y ↦ y - z) (α := fun n ↦ ((n : ℝ≥0) + 1)⁻¹) (C := 1) (B := 0) (ℱ := ℱ)
    (fun n ω ↦ ?_) (by simp [measurable_const]) (by simp) (by fun_prop) (fun y ↦ by simp)
    (fun ε hε ↦ ⟨ε ^ 2, by positivity [hε.1], fun y h1 _ ↦ ?_⟩) hξ
    (fun n ↦ ?_) (hξ_var _) ?_ ?_
  · -- the running means follow the recursion with steps `1 / (n + 1)`
    rw [Finset.sum_range_succ, NNReal.smul_def, sub_add_sub_cancel]
    push_cast
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    match_scalars <;> field_simp
    ring
  · rw [real_inner_self_eq_norm_sq]
    exact pow_le_pow_left₀ hε.1.le h1 2
  · refine (condExp_sub (integrable_const z) (hint n) _).trans ?_
    filter_upwards [hY_mean n] with ω hω
    simp [condExp_const (ℱ.le n), hω]
  · rw [← NNReal.summable_coe]
    push_cast
    exact fun hs ↦ Real.not_summable_natCast_inv
      ((summable_nat_add_iff (f := fun n : ℕ ↦ (n : ℝ)⁻¹) 1).1 (by exact_mod_cast hs))
  · rw [← NNReal.summable_coe]
    push_cast
    have := (summable_nat_add_iff (f := fun n : ℕ ↦ ((n : ℝ)⁻¹) ^ 2) 1).2 (by simp)
    exact_mod_cast this

end LMLExplore
