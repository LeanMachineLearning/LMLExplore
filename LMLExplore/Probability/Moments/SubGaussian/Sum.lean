/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.SubGaussian
public import LMLExplore.Probability.Distributions.Gaussian.Tail
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Deviations of sums of independent sub-Gaussian variables with a `√s` margin

Let `X₀, X₁, …` be independent and σ²-sub-Gaussian (in particular centered), and write
`S_s = X₀ + ⋯ + X_{s-1}`. This file bounds the probabilities of the deviations of `S_s` beyond
`s ε` plus a margin `√(2 σ² c s)` of the order of the standard deviation of `S_s`. Divided by `s`,
these are the events that the empirical mean plus the confidence width `√(2 σ² c / s)` exceeds `ε`,
or falls below `-ε`.

The upper deviations have a bounded expected count over all sample sizes [LS, Lemma 8.2]:
`∑ s < n, P(s ε ≤ S_s + √(2 σ² c s)) ≤ 1 + 2 σ² / ε² (c + √(π c) + 1)` for `ε > 0` and `c ≥ 0`,
uniformly in `n`. For `s = 0` the event is the sure event. The lower deviations satisfy, for each
`s ≥ 1`, `P(S_s ≤ -(s ε + √(2 σ² L s))) ≤ exp (-L) exp (-s ε² / (2 σ²))`, by Hoeffding's
inequality.

These are the two concentration facts of the analysis of the optimistic index policies of
[LS, Chapters 7 and 8]: the index of a suboptimal arm rarely overestimates a threshold above its
mean, and the index of an optimal arm rarely underestimates its mean.

## Main statements

* `LMLExplore.sum_measureReal_mul_le_sum_add_sqrt_le`: [LS, Lemma 8.2] for independent
  σ²-sub-Gaussian random variables, with variance proxy `σ²` (the book has `σ² = 1`).
* `LMLExplore.measureReal_sum_le_neg_mul_add_sqrt_le`: the lower deviation
  `S_s ≤ -(s ε + √(2 σ² L s))` has probability at most `exp (-L) exp (-s ε² / (2 σ²))`.

## Implementation notes

For [LS, Lemma 8.2], each probability is bounded by Hoeffding's inequality
(`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`) by `g s`, where
`g t = exp (-(max 0 (√t ε - √(2 σ² c)))² / (2 σ²))` is antitone. The sum is then compared with the
integral of `g`, which the substitution `t = ((x + √(2 σ² c)) / ε)²` turns into Gaussian
integrals (`integral_gaussian_Ioi` and `integral_Ioi_sub_mul_gaussianPDFReal`), as in the proof of
[LS, Lemma 8.2]. The case `σ² = 0` follows from the case `σ² > 0`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemma 8.2.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Set

open scoped NNReal

namespace LMLExplore


variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ} {σ2 : ℝ≥0}
  {ε c : ℝ}

/-- The bound `exp (-(max 0 (√t ε - √(2 σ² c)))² / (2 σ²))` on the probability of the event of
sample size `t` in [LS, Lemma 8.2]. -/
private noncomputable def tailBound (σ2 : ℝ≥0) (ε c t : ℝ) : ℝ :=
  exp (-max 0 (√t * ε - √(2 * σ2 * c)) ^ 2 / (2 * σ2))

private lemma tailBound_le_one (σ2 : ℝ≥0) (ε c t : ℝ) : tailBound σ2 ε c t ≤ 1 := by
  rw [tailBound, exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

private lemma antitone_tailBound (σ2 : ℝ≥0) (hε : 0 ≤ ε) (c : ℝ) : Antitone (tailBound σ2 ε c) := by
  intro x y hxy
  simp only [tailBound]
  gcongr

/-- One term of [LS, Lemma 8.2], by Hoeffding's inequality. -/
private lemma measureReal_mul_le_sum_add_sqrt_le_tailBound (h_indep : iIndepFun X P)
    (hX : ∀ i, HasSubgaussianMGF (X i) σ2 P) (ε c : ℝ) (s : ℕ) :
    P.real {ω | s * ε ≤ ∑ i ∈ range s, X i ω + √(2 * σ2 * c * s)} ≤ tailBound σ2 ε c s := by
  have := h_indep.isProbabilityMeasure
  rw [tailBound]
  rcases le_or_gt (√s * ε - √(2 * σ2 * c)) 0 with hδ | hδ
  · rw [max_eq_left hδ]
    exact measureReal_le_one.trans_eq (by simp)
  rw [max_eq_right hδ.le]
  -- `s ≠ 0` is used by the final `field_simp` to cancel `s`
  have hs : (s : ℝ) ≠ 0 := by
    rintro hs0
    simp [hs0] at hδ
    exact hδ.not_ge (by positivity)
  have h_set : {ω | s * ε ≤ ∑ i ∈ range s, X i ω + √(2 * σ2 * c * s)} =
      {ω | √s * (√s * ε - √(2 * σ2 * c)) ≤ ∑ i ∈ range s, X i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [sqrt_mul' _ (Nat.cast_nonneg s), mul_sub, ← mul_assoc, mul_self_sqrt (Nat.cast_nonneg s)]
    constructor <;> intro h <;> linarith
  rw [h_set]
  refine (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h_indep (fun i _ ↦ hX i)
    (by positivity)).trans_eq ?_
  simp only [sum_const, card_range, nsmul_eq_mul, mul_pow, sq_sqrt (Nat.cast_nonneg s)]
  push_cast
  congr 1
  field_simp

/-- The Gaussian integral `∫ x in Ioi 0, (x + √(2 σ² c)) exp (-x² / (2 σ²)) = σ² (1 + √(π c))`,
which `tailBound` becomes after a change of variables. -/
private lemma integrableOn_Ioi_add_mul_exp_and_integral_eq (hσ2 : σ2 ≠ 0) (hc : 0 ≤ c) :
    IntegrableOn (fun x ↦ (x + √(2 * σ2 * c)) * exp (-(1 / (2 * σ2)) * x ^ 2)) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), (x + √(2 * σ2 * c)) * exp (-(1 / (2 * σ2)) * x ^ 2) =
        σ2 * (1 + √(π * c)) := by
  have hσ2' : (0 : ℝ) < σ2 := by positivity
  have hβ : (0 : ℝ) < 1 / (2 * σ2) := by positivity
  have h_int_x := (integrable_mul_exp_neg_mul_sq hβ).integrableOn (s := Ioi 0)
  have h_int_one := ((integrable_exp_neg_mul_sq hβ).const_mul √(2 * σ2 * c)).integrableOn
    (s := Ioi 0)
  simp_rw [add_mul]
  refine ⟨h_int_x.add h_int_one, ?_⟩
  rw [integral_add h_int_x h_int_one, integral_const_mul, integral_gaussian_Ioi]
  have h_x : ∫ x in Ioi (0 : ℝ), x * exp (-(1 / (2 * σ2)) * x ^ 2) = σ2 := by
    have h := integral_Ioi_sub_mul_gaussianPDFReal 0 σ2 0
    simp_rw [gaussianPDFReal_def, sub_zero, mul_left_comm _ (√(2 * π * σ2))⁻¹,
      integral_const_mul, show ∀ x : ℝ, -x ^ 2 / (2 * σ2) = -(1 / (2 * σ2)) * x ^ 2 from
        fun x ↦ by ring, zero_pow two_ne_zero, mul_zero, exp_zero, mul_one] at h
    exact mul_left_cancel₀ (by positivity) h
  have h_sqrt : √(2 * σ2 * c) * √(π / (1 / (2 * σ2))) = 2 * σ2 * √(π * c) := by
    rw [← sqrt_mul (by positivity),
      show 2 * σ2 * c * (π / (1 / (2 * σ2))) = (2 * σ2) ^ 2 * (π * c) by field_simp,
      sqrt_mul (sq_nonneg _), sqrt_sq (by positivity)]
  rw [h_x, mul_div_assoc', h_sqrt]
  ring

/-- The substitution `t = ((x + √(2 σ² c)) / ε)²` maps `(0, ∞)` onto `((√(2 σ² c) / ε)², ∞)` and
turns `tailBound σ2 ε c t dt` into `2 / ε² (x + √(2 σ² c)) exp (-x² / (2 σ²)) dx`. -/
private lemma integrableOn_Ioi_tailBound_and_integral_eq (hσ2 : σ2 ≠ 0) (hε : 0 < ε)
    (hc : 0 ≤ c) :
    IntegrableOn (tailBound σ2 ε c) (Ioi ((√(2 * σ2 * c) / ε) ^ 2)) ∧
      ∫ t in Ioi ((√(2 * σ2 * c) / ε) ^ 2), tailBound σ2 ε c t =
        2 * σ2 / ε ^ 2 * (1 + √(π * c)) := by
  have hε0 : ε ≠ 0 := hε.ne'
  set b := √(2 * σ2 * c) with hb_def
  have hb : 0 ≤ b := sqrt_nonneg _
  set f : ℝ → ℝ := fun x ↦ ((x + b) / ε) ^ 2 with hf_def
  set f' : ℝ → ℝ := fun x ↦ 2 * (x + b) / ε ^ 2 with hf'_def
  have hf' : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt f (f' x) (Ioi 0) x := by
    intro x _
    refine (((hasDerivAt_id x).add_const b).div_const ε).pow 2 |>.hasDerivWithinAt.congr_deriv ?_
    norm_num [hf'_def]
    field_simp
  have hf_mono : StrictMonoOn f (Ici 0) := by
    intro x hx y _ hxy
    have hx' : 0 ≤ (x + b) / ε := div_nonneg (add_nonneg hx hb) hε.le
    exact pow_lt_pow_left₀ (div_lt_div_of_pos_right (by linarith) hε) hx' two_ne_zero
  have hf_inj : InjOn f (Ioi 0) := (hf_mono.mono Ioi_subset_Ici_self).injOn
  have hf_image : f '' Ioi 0 = Ioi ((b / ε) ^ 2) := by
    ext t
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [hf_def] using hf_mono le_rfl hx.le hx
    · intro ht
      have hsqrt : b / ε < √t := by
        rw [← sqrt_sq (div_nonneg hb hε.le)]
        exact sqrt_lt_sqrt (sq_nonneg _) ht
      refine ⟨√t * ε - b, ?_, ?_⟩
      · rw [div_lt_iff₀ hε] at hsqrt
        linarith
      · simp only [hf_def, sub_add_cancel, mul_div_assoc, div_self hε0, mul_one]
        exact sq_sqrt ((sq_nonneg _).trans ht.le)
  have h_eqOn : EqOn (fun x ↦ |f' x| • tailBound σ2 ε c (f x))
      (fun x ↦ 2 / ε ^ 2 * ((x + b) * exp (-(1 / (2 * σ2)) * x ^ 2))) (Ioi 0) := by
    intro x hx
    have hx : 0 < x := hx
    have hsqrt : √(f x) = (x + b) / ε := sqrt_sq (div_nonneg (by linarith) hε.le)
    have hmax : max 0 (√(f x) * ε - b) = x := by
      rw [hsqrt, div_mul_cancel₀ _ hε0, add_sub_cancel_right, max_eq_right hx.le]
    simp only [smul_eq_mul, tailBound, ← hb_def, hmax, hf'_def]
    rw [abs_of_nonneg (by positivity)]
    ring_nf
  obtain ⟨h_int, h_eq⟩ := integrableOn_Ioi_add_mul_exp_and_integral_eq hσ2 hc
  rw [← hf_image, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hf' hf_inj,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hf' hf_inj,
    setIntegral_congr_fun measurableSet_Ioi h_eqOn, integral_const_mul, h_eq]
  refine ⟨IntegrableOn.congr_fun (h_int.const_mul _) h_eqOn.symm measurableSet_Ioi, ?_⟩
  ring

/-- `tailBound` is integrable on `(0, ∞)`, with integral at most
`2 σ² / ε² (c + √(π c) + 1)`: it is at most `1` on `(0, (√(2 σ² c) / ε)²]`. -/
private lemma integrableOn_tailBound_and_integral_le (hσ2 : σ2 ≠ 0) (hε : 0 < ε) (hc : 0 ≤ c) :
    IntegrableOn (tailBound σ2 ε c) (Ioi 0) ∧
      ∫ t in Ioi 0, tailBound σ2 ε c t ≤ 2 * σ2 / ε ^ 2 * (c + √(π * c) + 1) := by
  set u := (√(2 * σ2 * c) / ε) ^ 2 with hu_def
  have hu : 0 ≤ u := sq_nonneg _
  obtain ⟨h_int_Ioi, h_Ioi⟩ := integrableOn_Ioi_tailBound_and_integral_eq hσ2 hε hc
  have h_int_Ioc : IntegrableOn (tailBound σ2 ε c) (Ioc 0 u) :=
    ((antitone_tailBound σ2 hε.le c).antitoneOn _).integrableOn_isCompact isCompact_Icc |>.mono_set
      Ioc_subset_Icc_self
  have h_union : Ioc 0 u ∪ Ioi u = (Ioi 0 : Set ℝ) := Ioc_union_Ioi_eq_Ioi hu
  refine ⟨h_union ▸ h_int_Ioc.union h_int_Ioi, ?_⟩
  rw [← h_union, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h_int_Ioc h_int_Ioi,
    h_Ioi]
  have h_Ioc : ∫ t in Ioc 0 u, tailBound σ2 ε c t ≤ u := by
    refine (setIntegral_mono_on h_int_Ioc (integrableOn_const (by simp)) measurableSet_Ioc
      fun t _ ↦ tailBound_le_one σ2 ε c t).trans_eq ?_
    simp [hu]
  have hu_eq : u = 2 * σ2 / ε ^ 2 * c := by
    rw [hu_def, div_pow, sq_sqrt (by positivity)]
    ring
  linarith [show 2 * σ2 / ε ^ 2 * (c + √(π * c) + 1) = u + 2 * σ2 / ε ^ 2 * (1 + √(π * c)) by
    rw [hu_eq]; ring]

/-- Comparison of the sum of `tailBound` at `0, …, n - 1` with its integral: since `tailBound` is
antitone and at most `1`, the sum is at most `1 + ∫ t in Ioi 0, tailBound σ2 ε c t`. -/
private lemma sum_tailBound_le (hσ2 : σ2 ≠ 0) (hε : 0 < ε) (hc : 0 ≤ c) (n : ℕ) :
    ∑ s ∈ range n, tailBound σ2 ε c s ≤ 1 + ∫ t in Ioi 0, tailBound σ2 ε c t := by
  have hint := (integrableOn_tailBound_and_integral_le hσ2 hε hc).1
  have h_nonneg : 0 ≤ ∫ t in Ioi 0, tailBound σ2 ε c t :=
    setIntegral_nonneg measurableSet_Ioi fun t _ ↦ (exp_pos _).le
  cases n with
  | zero =>
    simp only [range_zero, sum_empty]
    linarith
  | succ m =>
    rw [sum_range_succ']
    have h_sum := ((antitone_tailBound σ2 hε.le c).antitoneOn (Icc 0 (0 + m))).sum_le_integral
    simp only [zero_add] at h_sum
    rw [intervalIntegral.integral_of_le (Nat.cast_nonneg m)] at h_sum
    have h_mono : ∫ t in Ioc 0 (m : ℝ), tailBound σ2 ε c t ≤ ∫ t in Ioi 0, tailBound σ2 ε c t :=
      setIntegral_mono_set hint (ae_of_all _ fun t ↦ (exp_pos _).le)
        Ioc_subset_Ioi_self.eventuallyLE
    have h_zero := tailBound_le_one σ2 ε c 0
    push_cast at h_sum ⊢
    linarith

/-- [LS, Lemma 8.2] for `σ² ≠ 0`. -/
private lemma sum_measureReal_mul_le_sum_add_sqrt_le_of_ne_zero (h_indep : iIndepFun X P)
    (hX : ∀ i, HasSubgaussianMGF (X i) σ2 P) (hσ2 : σ2 ≠ 0) (hε : 0 < ε) (hc : 0 ≤ c) (n : ℕ) :
    ∑ s ∈ range n, P.real {ω | s * ε ≤ ∑ i ∈ range s, X i ω + √(2 * σ2 * c * s)} ≤
      1 + 2 * σ2 / ε ^ 2 * (c + √(π * c) + 1) :=
  calc ∑ s ∈ range n, P.real {ω | s * ε ≤ ∑ i ∈ range s, X i ω + √(2 * σ2 * c * s)}
  _ ≤ ∑ s ∈ range n, tailBound σ2 ε c s :=
    sum_le_sum fun s _ ↦ measureReal_mul_le_sum_add_sqrt_le_tailBound h_indep hX ε c s
  _ ≤ 1 + ∫ t in Ioi 0, tailBound σ2 ε c t := sum_tailBound_le hσ2 hε hc n
  _ ≤ 1 + 2 * σ2 / ε ^ 2 * (c + √(π * c) + 1) := by
    gcongr
    exact (integrableOn_tailBound_and_integral_le hσ2 hε hc).2

/-- **[LS, Lemma 8.2]** For independent σ²-sub-Gaussian random variables `X₀, X₁, …`, `ε > 0` and
`c ≥ 0`, the expected number of sample sizes `s < n` at which the index
`(X₀ + ⋯ + X_{s-1}) / s + √(2 σ² c / s)` is at least `ε` is at most
`1 + 2 σ² / ε² (c + √(π c) + 1)`, uniformly in `n`. The event is stated multiplied by `s`; for
`s = 0` it is the sure event. -/
theorem sum_measureReal_mul_le_sum_add_sqrt_le (h_indep : iIndepFun X P)
    (hX : ∀ i, HasSubgaussianMGF (X i) σ2 P) (hε : 0 < ε) (hc : 0 ≤ c) (n : ℕ) :
    ∑ s ∈ range n, P.real {ω | s * ε ≤ ∑ i ∈ range s, X i ω + √(2 * σ2 * c * s)} ≤
      1 + 2 * σ2 / ε ^ 2 * (c + √(π * c) + 1) := by
  rcases eq_or_ne σ2 0 with rfl | hσ2
  swap
  · exact sum_measureReal_mul_le_sum_add_sqrt_le_of_ne_zero h_indep hX hσ2 hε hc n
  -- for `σ² = 0`, the variables are `δ`-sub-Gaussian for every `δ > 0`, and the events grow in `δ`
  have := h_indep.isProbabilityMeasure
  have hK : 0 < c + √(π * c) + 1 := by positivity
  simp only [NNReal.coe_zero, mul_zero, zero_mul, sqrt_zero, add_zero, zero_div]
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  let σ' : ℝ≥0 := ⟨δ * ε ^ 2 / (2 * (c + √(π * c) + 1)), by positivity⟩
  have hσ'_coe : (σ' : ℝ) = δ * ε ^ 2 / (2 * (c + √(π * c) + 1)) := NNReal.coe_mk _ _
  have hσ'_ne : σ' ≠ 0 := by
    rw [ne_eq, ← NNReal.coe_eq_zero, hσ'_coe]
    positivity
  have hX' : ∀ i, HasSubgaussianMGF (X i) σ' P := fun i ↦
    ⟨(hX i).integrable_exp_mul, fun t ↦ ((hX i).mgf_le t).trans (by gcongr; simp)⟩
  calc ∑ s ∈ range n, P.real {ω | s * ε ≤ ∑ i ∈ range s, X i ω}
  _ ≤ ∑ s ∈ range n, P.real {ω | s * ε ≤ ∑ i ∈ range s, X i ω + √(2 * σ' * c * s)} := by
    refine sum_le_sum fun s _ ↦ measureReal_mono fun ω (h : _ ≤ _) ↦ ?_
    exact h.trans (le_add_of_nonneg_right (sqrt_nonneg _))
  _ ≤ 1 + 2 * σ' / ε ^ 2 * (c + √(π * c) + 1) :=
    sum_measureReal_mul_le_sum_add_sqrt_le_of_ne_zero h_indep hX' hσ'_ne hε hc n
  _ = 1 + δ := by
    rw [hσ'_coe]
    field_simp

/-- **Hoeffding's inequality for the index of [LS, Algorithm 6], lower tail.** For independent
σ²-sub-Gaussian random variables `X₀, X₁, …` with `σ² ≠ 0`, `L ≥ 0`, `ε ≥ 0` and `s ≠ 0`, the
probability that `X₀ + ⋯ + X_{s-1} ≤ -(s ε + √(2 σ² L s))` is at most
`exp (-L) exp (-s ε² / (2 σ²))`. Divided by `s`, the event says that the index
`(X₀ + ⋯ + X_{s-1}) / s + √(2 σ² L / s)` is at most `-ε`. -/
theorem measureReal_sum_le_neg_mul_add_sqrt_le (h_indep : iIndepFun X P)
    (hX : ∀ i, HasSubgaussianMGF (X i) σ2 P) (hσ2 : σ2 ≠ 0) {L : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    {s : ℕ} (hs : s ≠ 0) :
    P.real {ω | ∑ i ∈ range s, X i ω ≤ -(s * ε + √(2 * σ2 * L * s))} ≤
      exp (-L) * exp (-(ε ^ 2 / (2 * σ2) * s)) := by
  have hs' : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)
  have hσ2' : (0 : ℝ) < σ2 := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hσ2)
  set δ := s * ε + √(2 * σ2 * L * s) with hδ
  have h_sq : (ε ^ 2 / (2 * σ2) * s + L) * (2 * s * σ2) ≤ δ ^ 2 := by
    have h1 : √(2 * σ2 * L * s) ^ 2 = 2 * σ2 * L * s := sq_sqrt (by positivity)
    have h2 : 0 ≤ s * ε * √(2 * σ2 * L * s) := by positivity
    have h3 : (ε ^ 2 / (2 * σ2) * s + L) * (2 * s * σ2) = (s * ε) ^ 2 + 2 * σ2 * L * s := by
      field_simp
    rw [h3, hδ]
    nlinarith
  refine (HasSubgaussianMGF.measure_sum_range_le_le_of_iIndepFun h_indep (fun i _ ↦ hX i)
    (by positivity)).trans ?_
  rw [← exp_add]
  gcongr
  have : ε ^ 2 / (2 * σ2) * s + L ≤ δ ^ 2 / (2 * s * σ2) := by
    rw [le_div_iff₀ (by positivity)]
    exact h_sq
  rw [neg_div]
  linarith

end LMLExplore
