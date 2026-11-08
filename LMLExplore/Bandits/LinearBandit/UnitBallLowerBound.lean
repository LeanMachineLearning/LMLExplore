/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Algebra.Order.BigOperators.SignFlip
public import LMLExplore.Bandits.LinearBandit.DivergenceDecomposition
public import LMLExplore.MeasureTheory.Function.SpecialFunctions.Inner
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

/-!
# The minimax lower bound for linear bandits on the unit ball

In a linear bandit with a fixed action set and Gaussian noise of variance `σ²`, the reward of an
action with feature `x ∈ E` has law `𝒩(⟪θ, x⟫, σ²)` for an unknown parameter `θ`. When the
features lie in the unit ball of `E`, of dimension `d`, and contain the points `s / √d` for the
sign patterns `s ∈ {±1}^d` of an orthonormal basis, every algorithm has, for some parameter `θ`
with `‖θ‖² = σ² d² / (4 n)`, an expected regret at least `e^{-1/2} d √(σ² n) / 16` after `n`
rounds. This is [LS, Theorem 24.2], whose bound is `d √n / (16 √3)` for variance `1`, a parameter
with `‖θ‖² = d² / (48 n)` and `d ≤ 2 n`; the constant here is larger (`e^{-1/2} > 1 / √3`) and no
relation between `d` and `n` is needed.

The parameters are the `θ` with coordinates `±Δ` in the basis, and the regret of a round is at
least `Δ / (2 √d)` times the number of coordinates `i` at which the feature played does not have
the sign of `⟪b i, θ⟫`. Flipping the sign of the `i`-th coordinate of `θ` changes the law of the
history of the first `n` rounds by the relative entropy `2 Δ² E[∑_{t < n} ⟪b i, X_t⟫²] / σ²`
(the divergence decomposition of `LMLExplore.Bandits.LinearBandit.DivergenceDecomposition`), and
these relative entropies add up over `i` to at most `2 Δ² n / σ²`, since the features `X_t`
played lie in the unit ball. The Bretagnolle–Huber inequality for each pair of parameters, the
convexity of `exp` across the coordinates and the averaging over the `2^d` sign patterns
(`Fintype.exists_div_two_le_sum`) then give a parameter with regret at least
`Δ √d n exp(-2 Δ² n / (σ² d)) / 8`, and `Δ² = σ² d / (4 n)` maximizes this bound. Distributing the
relative entropies across the coordinates in this way replaces the stopping times of [LS], which
cap the information gathered on each coordinate.

## Main statements

* `LMLExplore.Bandits.exists_le_integral_linearRegret_gaussianLinearEnv_of_norm_le_one`: the lower
  bound `Δ √d n exp(-2 Δ² n / (σ² d)) / 8` for every `Δ ≥ 0`, for features in the unit ball that
  contain the points `s / √d`.
* `LMLExplore.Bandits.exists_le_integral_linearRegret_gaussianLinearEnv_closedBall`: the lower
  bound `e^{-1/2} d √(σ² n) / 16` with the unit ball of a finite-dimensional inner product space as
  the action set [LS, Theorem 24.2].

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Theorem 24.2.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset Real Learning Module
open scoped ENNReal NNReal InnerProductSpace

namespace LMLExplore.Bandits

variable {ι 𝓐 E : Type*} [MeasurableSpace 𝓐] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {φ : 𝓐 → E} {σ2 : ℝ≥0}

section UnitBall

variable [Fintype ι] {b : OrthonormalBasis ι ℝ E} {θ : E} {Δ : ℝ} {s : ι → ℝ}

omit [MeasurableSpace 𝓐] in
/-- For signs `s i` and a feature in the unit ball, the number of coordinates `i` at which the
feature does not have the sign `s i` is at most `2 d - 2 √d ∑ i, s i ⟪b i, φ a⟫`. -/
private lemma sum_indicator_le (hs : ∀ i, |s i| = 1) {a : 𝓐} (ha : ‖φ a‖ ≤ 1) :
    ∑ i, {x : 𝓐 | s i * ⟪b i, φ x⟫_ℝ ≤ 0}.indicator (1 : 𝓐 → ℝ) a ≤
      2 * Fintype.card ι - 2 * √(Fintype.card ι) * ∑ i, s i * ⟪b i, φ a⟫_ℝ := by
  set d : ℝ := (Fintype.card ι : ℝ)
  have hd : √d ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg _)
  have hterm (i : ι) : {x : 𝓐 | s i * ⟪b i, φ x⟫_ℝ ≤ 0}.indicator (1 : 𝓐 → ℝ) a ≤
      (1 - √d * (s i * ⟪b i, φ a⟫_ℝ)) ^ 2 := by
    by_cases h : s i * ⟪b i, φ a⟫_ℝ ≤ 0
    · rw [Set.indicator_of_mem (by exact h), Pi.one_apply]
      have : 1 ≤ 1 - √d * (s i * ⟪b i, φ a⟫_ℝ) := by
        nlinarith [Real.sqrt_nonneg d]
      nlinarith
    · rw [Set.indicator_of_notMem (by exact h)]
      positivity
  have hsq (i : ι) : (s i * ⟪b i, φ a⟫_ℝ) ^ 2 = ⟪b i, φ a⟫_ℝ ^ 2 := by
    rw [mul_pow, ← sq_abs (s i), hs, one_pow, one_mul]
  have hnorm : d * ∑ i, ⟪b i, φ a⟫_ℝ ^ 2 ≤ d := by
    rw [b.sum_sq_inner_right]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (pow_le_one₀ (norm_nonneg _) ha)
  calc ∑ i, {x : 𝓐 | s i * ⟪b i, φ x⟫_ℝ ≤ 0}.indicator (1 : 𝓐 → ℝ) a
      ≤ ∑ i, (1 - √d * (s i * ⟪b i, φ a⟫_ℝ)) ^ 2 := sum_le_sum fun i _ ↦ hterm i
    _ = ∑ i, (1 - 2 * √d * (s i * ⟪b i, φ a⟫_ℝ) + d * ⟪b i, φ a⟫_ℝ ^ 2) :=
        sum_congr rfl fun i _ ↦ by
          linear_combination (s i * ⟪b i, φ a⟫_ℝ) ^ 2 * hd + d * hsq i
    _ = d - 2 * √d * ∑ i, s i * ⟪b i, φ a⟫_ℝ + d * ∑ i, ⟪b i, φ a⟫_ℝ ^ 2 := by
        rw [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one,
          ← mul_sum, ← mul_sum]
    _ ≤ 2 * d - 2 * √d * ∑ i, s i * ⟪b i, φ a⟫_ℝ := by linarith

omit [MeasurableSpace 𝓐] in
/-- The gap of an action against a parameter with coordinates `Δ * s i`, for signs `s i` and
features in the unit ball that contain the point `s / √d`, is at least `Δ / (2 √d)` times the
number of coordinates `i` at which the feature of the action does not have the sign `s i`. -/
private lemma mul_sum_indicator_le_mul_iSup_inner_sub_inner (hΔ : 0 ≤ Δ) (hs : ∀ i, |s i| = 1)
    (hθ : ∀ i, ⟪b i, θ⟫_ℝ = Δ * s i) (hball : ∀ a, ‖φ a‖ ≤ 1) {a₀ : 𝓐}
    (ha₀ : ∀ i, ⟪b i, φ a₀⟫_ℝ = s i / √(Fintype.card ι)) (a : 𝓐) :
    Δ * ∑ i, {x : 𝓐 | s i * ⟪b i, φ x⟫_ℝ ≤ 0}.indicator 1 a ≤
      2 * √(Fintype.card ι) * ((⨆ x, ⟪θ, φ x⟫_ℝ) - ⟪θ, φ a⟫_ℝ) := by
  set d : ℝ := (Fintype.card ι : ℝ)
  have hd : √d ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg _)
  have hinner (y : E) : ⟪θ, y⟫_ℝ = Δ * ∑ i, s i * ⟪b i, y⟫_ℝ := by
    rw [← b.sum_inner_mul_inner θ y, mul_sum]
    exact sum_congr rfl fun i _ ↦ by rw [real_inner_comm, hθ, mul_assoc]
  have hbdd : BddAbove (Set.range fun x ↦ ⟪θ, φ x⟫_ℝ) :=
    ⟨‖θ‖, by
      rintro _ ⟨x, rfl⟩
      exact (real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hball x))⟩
  -- the point `s / √d` has mean reward `Δ √d`
  have hvert : ∑ i, s i * ⟪b i, φ a₀⟫_ℝ = √d := by
    have h1 (i : ι) : s i * ⟪b i, φ a₀⟫_ℝ = 1 / √d := by
      rw [ha₀, mul_div_assoc', ← sq, ← sq_abs, hs, one_pow]
    rw [sum_congr rfl fun i _ ↦ h1 i, sum_const, card_univ, nsmul_eq_mul, mul_one_div,
      Real.div_sqrt]
  have hsup : Δ * √d ≤ ⨆ x, ⟪θ, φ x⟫_ℝ := by
    refine le_of_eq_of_le ?_ (le_ciSup hbdd a₀)
    rw [hinner, hvert]
  calc Δ * ∑ i, {x : 𝓐 | s i * ⟪b i, φ x⟫_ℝ ≤ 0}.indicator 1 a
      ≤ Δ * (2 * d - 2 * √d * ∑ i, s i * ⟪b i, φ a⟫_ℝ) :=
        mul_le_mul_of_nonneg_left (sum_indicator_le hs (hball a)) hΔ
    _ = 2 * √d * (Δ * √d - ⟪θ, φ a⟫_ℝ) := by
        rw [hinner]
        linear_combination (-2 * Δ) * hd
    _ ≤ 2 * √d * ((⨆ x, ⟪θ, φ x⟫_ℝ) - ⟪θ, φ a⟫_ℝ) := by gcongr

omit [MeasurableSpace 𝓐] in
/-- The expected regret of a run with features in the unit ball is nonnegative. -/
private lemma integral_linearRegret_nonneg {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (hball : ∀ a, ‖φ a‖ ≤ 1) (θ : E) (O : ℕ → Ω → Unit) (A : ℕ → Ω → 𝓐) (n : ℕ) :
    0 ≤ ∫ ω, linearRegret (fun _ ↦ φ) θ O A n ω ∂P :=
  integral_nonneg fun _ ↦ linearRegret_nonneg fun _ ↦ ⟨‖θ‖, by
    rintro _ ⟨x, rfl⟩
    exact (real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hball x))⟩

variable [MeasurableSpace E] [OpensMeasurableSpace E]

/-- The squared coordinates of the features played are integrable, for features in the unit ball. -/
private lemma integrable_inner_sq {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {A : ℕ → Ω → 𝓐} (hA : ∀ t, Measurable (A t)) (hφ : Measurable φ)
    (hball : ∀ a, ‖φ a‖ ≤ 1) (b : OrthonormalBasis ι ℝ E) (i : ι) (t : ℕ) :
    Integrable (fun ω ↦ ⟪b i, φ (A t ω)⟫_ℝ ^ 2) P := by
  refine Integrable.of_bound
    (((hφ.const_inner' (b i)).comp (hA t)).pow_const 2).aestronglyMeasurable 1
    (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_pow, sq_le_one_iff_abs_le_one, abs_abs]
  calc |⟪b i, φ (A t ω)⟫_ℝ| ≤ ‖b i‖ * ‖φ (A t ω)‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 := by rw [b.norm_eq_one, one_mul]; exact hball _

/-- The expected regret of a run against a parameter with coordinates `Δ * s i`, for signs `s i`
and features in the unit ball that contain the point `s / √d`, is at least `Δ / (2 √d)` times the
expected number of pairs of a round and a coordinate `i` at which the feature of the action played
does not have the sign `s i`. -/
private lemma mul_sum_sum_measureReal_le_mul_integral_linearRegret {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → 𝓐}
    (hA : ∀ t, Measurable (A t)) (hφ : Measurable φ) (hΔ : 0 ≤ Δ) (hs : ∀ i, |s i| = 1)
    (hθ : ∀ i, ⟪b i, θ⟫_ℝ = Δ * s i) (hball : ∀ a, ‖φ a‖ ≤ 1)
    (hvert : ∃ a, ∀ i, ⟪b i, φ a⟫_ℝ = s i / √(Fintype.card ι)) (O : ℕ → Ω → Unit) (n : ℕ) :
    Δ * ∑ i, ∑ t ∈ range n, P.real (A t ⁻¹' {x | s i * ⟪b i, φ x⟫_ℝ ≤ 0}) ≤
      2 * √(Fintype.card ι) * ∫ ω, linearRegret (fun _ ↦ φ) θ O A n ω ∂P := by
  obtain ⟨a₀, ha₀⟩ := hvert
  have hS (i : ι) : MeasurableSet {x : 𝓐 | s i * ⟪b i, φ x⟫_ℝ ≤ 0} :=
    measurableSet_le ((hφ.const_inner' (b i)).const_mul (s i)) measurable_const
  have hind (i : ι) (t : ℕ) :
      Integrable ((A t ⁻¹' {x | s i * ⟪b i, φ x⟫_ℝ ≤ 0}).indicator (1 : Ω → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator (hA t (hS i))
  have hreg : Integrable (fun ω ↦ linearRegret (fun _ ↦ φ) θ O A n ω) P := by
    simp_rw [linearRegret_def]
    refine integrable_finsetSum _ fun t _ ↦ (integrable_const _).sub ?_
    refine Integrable.of_bound ((hφ.const_inner' θ).comp (hA t)).aestronglyMeasurable ‖θ‖
      (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hball _))
  calc Δ * ∑ i, ∑ t ∈ range n, P.real (A t ⁻¹' {x | s i * ⟪b i, φ x⟫_ℝ ≤ 0})
      = ∫ ω, Δ * ∑ i, ∑ t ∈ range n,
          (A t ⁻¹' {x | s i * ⟪b i, φ x⟫_ℝ ≤ 0}).indicator 1 ω ∂P := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun t _ ↦
          hind i t]
        simp_rw [integral_finsetSum _ fun t _ ↦ hind _ t, integral_indicator_one (hA _ (hS _))]
    _ ≤ ∫ ω, 2 * √(Fintype.card ι) * linearRegret (fun _ ↦ φ) θ O A n ω ∂P := by
        refine integral_mono (((integrable_finsetSum _ fun i _ ↦
          integrable_finsetSum _ fun t _ ↦ hind i t)).const_mul Δ) (hreg.const_mul _)
          fun ω ↦ ?_
        rw [linearRegret_def, sum_comm, mul_sum, mul_sum]
        refine sum_le_sum fun t _ ↦ ?_
        simpa [Set.indicator_apply] using
          mul_sum_indicator_le_mul_iSup_inner_sub_inner hΔ hs hθ hball ha₀ (A t ω)
    _ = 2 * √(Fintype.card ι) * ∫ ω, linearRegret (fun _ ↦ φ) θ O A n ω ∂P :=
        integral_const_mul _ _

/-- **Flipping one sign.** Let `θ` and `θ'` have coordinates `Δ * s j` and `Δ * s' j` in the basis
`b`, for signs that agree except at `i`, where `s' i = -s i`. For features in the unit ball, the
expected numbers of rounds `t < n` at which the `i`-th coordinate of the feature played does not
have the sign `s i` in a run against `θ`, and the sign `s' i` in a run against `θ'`, add up to at
least `n exp(-2 Δ² q / σ²) / 2`, where `q = E[∑_{t < n} ⟪b i, φ (A t)⟫²]` in the run against
`θ`. -/
private lemma mul_exp_div_two_le_sum_add_sum {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
    {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ}
    {O' : ℕ → Ω' → Unit} {A' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → ℝ} {alg : Algorithm Unit 𝓐 ℝ}
    {θ' : E} {s' : ι → ℝ} {hθm : Measurable fun p : Unit × 𝓐 ↦ ⟪θ, φ p.2⟫_ℝ}
    {hθm' : Measurable fun p : Unit × 𝓐 ↦ ⟪θ', φ p.2⟫_ℝ}
    (h : IsAlgEnvSeq O A Y alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ σ2 hθm) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ' σ2 hθm')
      P')
    (hσ2 : σ2 ≠ 0) (hφ : Measurable φ) (hball : ∀ a, ‖φ a‖ ≤ 1) {i : ι} (hs : |s i| = 1)
    (hθ : ∀ j, ⟪b j, θ⟫_ℝ = Δ * s j) (hθ' : ∀ j, ⟪b j, θ'⟫_ℝ = Δ * s' j)
    (hs'i : s' i = -s i) (hs' : ∀ j ≠ i, s' j = s j) (n : ℕ) :
    n * exp (-(2 * Δ ^ 2 * (∑ t ∈ range n, ∫ ω, ⟪b i, φ (A t ω)⟫_ℝ ^ 2 ∂P) / σ2)) / 2 ≤
      ∑ t ∈ range n, P.real (A t ⁻¹' {x | s i * ⟪b i, φ x⟫_ℝ ≤ 0}) +
        ∑ t ∈ range n, P'.real (A' t ⁻¹' {x | s' i * ⟪b i, φ x⟫_ℝ ≤ 0}) := by
  -- `θ - θ'` is `2 Δ s i b i`, so `⟪θ - θ', x⟫² = 4 Δ² ⟪b i, x⟫²`
  have hdiff (y : E) : ⟪θ - θ', y⟫_ℝ ^ 2 = 4 * Δ ^ 2 * ⟪b i, y⟫_ℝ ^ 2 := by
    have heq : ⟪θ - θ', y⟫_ℝ = 2 * Δ * s i * ⟪b i, y⟫_ℝ := by
      rw [← b.sum_inner_mul_inner, Fintype.sum_eq_single i fun j hj ↦ by
        rw [real_inner_comm, inner_sub_right, hθ, hθ', hs' j hj, sub_self, zero_mul],
        real_inner_comm, inner_sub_right, hθ, hθ', hs'i]
      ring
    have hsq : s i ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
    rw [heq, mul_pow, mul_pow, mul_pow, hsq]
    ring
  have hint (t : ℕ) : Integrable (fun ω ↦ ⟪θ - θ', φ (A t ω)⟫_ℝ ^ 2) P := by
    simp_rw [hdiff]
    exact (integrable_inner_sq h.measurable_action hφ hball b i t).const_mul _
  have hsum : (∑ t ∈ range n, ∫ ω, ⟪θ - θ', φ (A t ω)⟫_ℝ ^ 2 ∂P) / (2 * σ2) =
      2 * Δ ^ 2 * (∑ t ∈ range n, ∫ ω, ⟪b i, φ (A t ω)⟫_ℝ ^ 2 ∂P) / σ2 := by
    simp_rw [hdiff, integral_const_mul, ← mul_sum]
    have : (σ2 : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hσ2
    field_simp
    ring
  have hbh := h.mul_exp_neg_sum_integral_div_two_le_sum_gaussianLinearEnv h' hσ2 hint n
    (S := {x | s i * ⟪b i, φ x⟫_ℝ ≤ 0})
    (measurableSet_le ((hφ.const_inner' (b i)).const_mul (s i)) measurable_const)
  rw [hsum] at hbh
  -- an action on the wrong side for `θ'` is one on the right side for `θ`
  have hsub : {x : 𝓐 | s i * ⟪b i, φ x⟫_ℝ ≤ 0}ᶜ ⊆ {x | s' i * ⟪b i, φ x⟫_ℝ ≤ 0} := fun x hx ↦ by
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx ⊢
    rw [hs'i, neg_mul]
    exact neg_nonpos.2 hx.le
  refine hbh.trans (add_le_add le_rfl (sum_le_sum fun t _ ↦ ?_))
  exact measureReal_mono (Set.preimage_mono hsub)

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- **Convexity across the coordinates.** If the `q i` add up to at most `n`, then
`∑ i, n exp(-c q i) / 2 ≥ d n exp(-c n / d) / 2` for `c ≥ 0`, with `d` the cardinality of `ι`. -/
private lemma card_mul_le_sum_mul_exp_neg (q : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) {n : ℕ}
    (hq : ∑ i, q i ≤ n) :
    Fintype.card ι * (n * exp (-(c * n / Fintype.card ι)) / 2) ≤
      ∑ i, n * exp (-(c * q i)) / 2 := by
  have h := Real.card_mul_exp_sum_div_card_le_sum_exp univ fun i ↦ -(c * q i)
  rw [card_univ, sum_neg_distrib, ← mul_sum, neg_div] at h
  have hle : exp (-(c * n / Fintype.card ι)) ≤ exp (-((c * ∑ i, q i) / Fintype.card ι)) := by
    rw [exp_le_exp, neg_le_neg_iff]
    gcongr
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _) |>.trans h)
    (Nat.cast_nonneg n)
  rw [← sum_div, ← mul_sum]
  linarith

/-- **Minimax lower bound for linear bandits with features in the unit ball** [LS, Theorem 24.2].
Let `b` be an orthonormal basis of `E` indexed by a finite type of size `d`, and let the features
`φ a` of the actions lie in the unit ball and contain the points `s / √d` (with coordinates
`⟪b i, φ a⟫ = s i / √d`) for the sign patterns `s ∈ {±1}^d`. For Gaussian noise of variance
`σ2 ≠ 0`, a horizon `n` and `Δ ≥ 0`, every algorithm has, for some parameter `θ` whose
coordinates `⟪b i, θ⟫` are `±Δ`, an expected regret against the Gaussian linear environment of
parameter `θ` at least `Δ √d n exp(-2 Δ² n / (σ² d)) / 8`. The bound holds for every proof `hθ`
of the measurability that `gaussianLinearEnv` takes, one of which is given by `hφ`. -/
theorem exists_le_integral_linearRegret_gaussianLinearEnv_of_norm_le_one
    (alg : Algorithm Unit 𝓐 ℝ) (b : OrthonormalBasis ι ℝ E) (hφ : Measurable φ)
    (hball : ∀ a, ‖φ a‖ ≤ 1)
    (hvert : ∀ s : ι → ℝ, (∀ i, |s i| = 1) → ∃ a, ∀ i, ⟪b i, φ a⟫_ℝ = s i / √(Fintype.card ι))
    (hσ2 : σ2 ≠ 0) (n : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    ∃ θ : E, (∀ i, |⟪b i, θ⟫_ℝ| = Δ) ∧
      ∀ hθ : Measurable fun p : Unit × 𝓐 ↦ ⟪θ, φ p.2⟫_ℝ,
        Δ * √(Fintype.card ι) * n * exp (-(2 * Δ ^ 2 * n / (σ2 * Fintype.card ι))) / 8 ≤
          ∫ ω, linearRegret (fun _ ↦ φ) θ IT.obs IT.action n ω
            ∂(trajMeasure alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ σ2 hθ)) := by
  classical
  set d : ℝ := (Fintype.card ι : ℝ) with hd_def
  -- the parameters `θ ε` with coordinates `±Δ`, for the sign patterns `ε : ι → Bool`
  let sg : (ι → Bool) → ι → ℝ := fun ε i ↦ if ε i then 1 else -1
  have hsg (ε : ι → Bool) (i : ι) : |sg ε i| = 1 := by by_cases h : ε i <;> simp [sg, h]
  let θ : (ι → Bool) → E := fun ε ↦ ∑ i, (Δ * sg ε i) • b i
  have hθ (ε : ι → Bool) (i : ι) : ⟪b i, θ ε⟫_ℝ = Δ * sg ε i :=
    b.orthonormal.inner_right_fintype _ i
  have habs (ε : ι → Bool) (i : ι) : |⟪b i, θ ε⟫_ℝ| = Δ := by
    rw [hθ, abs_mul, abs_of_nonneg hΔ, hsg, mul_one]
  have hθm (ε : ι → Bool) : Measurable fun p : Unit × 𝓐 ↦ ⟪θ ε, φ p.2⟫_ℝ :=
    (hφ.const_inner' (θ ε)).comp measurable_snd
  let P : (ι → Bool) → Measure (ℕ → Unit × 𝓐 × ℝ) := fun ε ↦
    trajMeasure alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) (θ ε) σ2 (hθm ε))
  have hrun (ε : ι → Bool) := IT.isAlgEnvSeq_trajMeasure alg
    (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) (θ ε) σ2 (hθm ε))
  -- `f ε i`: the expected number of rounds at which the `i`-th coordinate has the wrong sign
  let f : (ι → Bool) → ι → ℝ := fun ε i ↦ ∑ t ∈ range n,
    (P ε).real (IT.action t ⁻¹' {x | sg ε i * ⟪b i, φ x⟫_ℝ ≤ 0})
  -- `q ε i`: the expected information gathered on the `i`-th coordinate
  let q : (ι → Bool) → ι → ℝ := fun ε i ↦ ∑ t ∈ range n,
    ∫ ω, ⟪b i, φ (IT.action t ω)⟫_ℝ ^ 2 ∂(P ε)
  have hR (ε : ι → Bool) : Δ * ∑ i, f ε i ≤ 2 * √d * ∫ ω, linearRegret (fun _ ↦ φ) (θ ε) IT.obs
      IT.action n ω ∂(P ε) :=
    mul_sum_sum_measureReal_le_mul_integral_linearRegret (hrun ε).measurable_action hφ hΔ
      (hsg ε) (hθ ε) hball (hvert _ (hsg ε)) _ n
  -- the features played lie in the unit ball, so the information adds up to at most `n`
  have hq (ε : ι → Bool) : ∑ i, q ε i ≤ n := by
    have hint := integrable_inner_sq (P := P ε) (hrun ε).measurable_action hφ hball b
    calc ∑ i, q ε i = ∑ t ∈ range n, ∫ ω, ∑ i, ⟪b i, φ (IT.action t ω)⟫_ℝ ^ 2 ∂(P ε) := by
          rw [sum_comm]
          exact sum_congr rfl fun t _ ↦ (integral_finsetSum _ fun i _ ↦ hint i t).symm
      _ ≤ ∑ _t ∈ range n, (1 : ℝ) := by
          refine sum_le_sum fun t _ ↦ ?_
          refine (integral_mono (integrable_finsetSum _ fun i _ ↦ hint i t)
            (integrable_const 1) fun ω ↦ ?_).trans (by simp)
          rw [b.sum_sq_inner_right]
          exact pow_le_one₀ (norm_nonneg _) (hball _)
      _ = n := by simp
  -- flipping the sign of the coordinate `i` changes the law of the history by `2 Δ² q ε i / σ²`
  have hpair (ε : ι → Bool) (i : ι) : n * exp (-(2 * Δ ^ 2 / σ2 * q ε i)) / 2 ≤
      f ε i + f (Function.update ε i (!ε i)) i := by
    have := mul_exp_div_two_le_sum_add_sum (hrun ε) (hrun _) hσ2 hφ hball (hsg ε i) (hθ ε)
      (hθ _) (s' := sg (Function.update ε i (!ε i))) (i := i) ?_ (fun j hj ↦ ?_) n
    · refine le_of_eq_of_le ?_ this
      congr 3
      ring
    · by_cases h : ε i <;> simp [sg, h]
    · simp [sg, Function.update_of_ne hj]
  -- averaging over the sign patterns
  obtain ⟨ε, hε⟩ := Fintype.exists_div_two_le_sum f _ hpair fun ε ↦
    card_mul_le_sum_mul_exp_neg (q ε) (by positivity) (hq ε)
  refine ⟨θ ε, habs ε, fun _ ↦ ?_⟩
  have hd2 : √d * √d = d := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hexp : exp (-(2 * Δ ^ 2 / σ2 * n / d)) = exp (-(2 * Δ ^ 2 * n / (σ2 * d))) := by
    congr 2
    ring
  rcases (Real.sqrt_nonneg d).eq_or_lt with hd0 | hd0
  · rw [← hd0, mul_zero, zero_mul, zero_mul, zero_div]
    exact integral_linearRegret_nonneg hball _ _ _ n
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < 2 * √d)
  calc 2 * √d * (Δ * √d * n * exp (-(2 * Δ ^ 2 * n / (σ2 * d))) / 8)
      = Δ * (d * (n * exp (-(2 * Δ ^ 2 / σ2 * n / d)) / 2) / 2) := by
        rw [hexp]
        linear_combination (Δ * n * exp (-(2 * Δ ^ 2 * n / (σ2 * d))) / 4) * hd2
    _ ≤ Δ * ∑ i, f ε i := by gcongr
    _ ≤ _ := hR ε

/-- **Minimax lower bound for linear bandits on the unit ball** [LS, Theorem 24.2], with the unit
ball of a finite-dimensional inner product space `E` of dimension `d` as the action set: for
Gaussian noise of variance `σ2` and a horizon `n`, every algorithm has, for some parameter `θ` with
`‖θ‖² = σ² d² / (4 n)`, an expected regret at least `e^{-1/2} d √(σ² n) / 16`. -/
theorem exists_le_integral_linearRegret_gaussianLinearEnv_closedBall [FiniteDimensional ℝ E]
    (alg : Algorithm Unit (Metric.closedBall (0 : E) 1) ℝ) (σ2 : ℝ≥0) (n : ℕ) :
    ∃ θ : E, ‖θ‖ ^ 2 = σ2 * finrank ℝ E ^ 2 / (4 * n) ∧
      ∀ hθ : Measurable fun p : Unit × Metric.closedBall (0 : E) 1 ↦ ⟪θ, (p.2 : E)⟫_ℝ,
        exp (-(1 / 2)) / 16 * finrank ℝ E * √(σ2 * n) ≤
          ∫ ω, linearRegret (fun _ ↦ Subtype.val) θ IT.obs IT.action n ω
            ∂(trajMeasure alg
              (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ Subtype.val) θ σ2 hθ)) := by
  have hball (x : Metric.closedBall (0 : E) 1) : ‖(x : E)‖ ≤ 1 := by
    have := x.2
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  set d : ℝ := (finrank ℝ E : ℝ) with hd_def
  -- the degenerate cases, where the bound is `0` and `θ = 0`
  by_cases h0 : σ2 = 0 ∨ n = 0 ∨ finrank ℝ E = 0
  · refine ⟨0, ?_, fun _ ↦ ?_⟩
    · rcases h0 with h0 | h0 | h0 <;> simp [h0, hd_def]
    · refine le_of_eq_of_le ?_ (integral_linearRegret_nonneg hball _ _ _ n)
      rcases h0 with h0 | h0 | h0 <;> simp [h0, hd_def]
  simp only [not_or] at h0
  obtain ⟨hσ2, hn, hd⟩ := h0
  have hσ2' : (0 : ℝ) < σ2 := by positivity
  have hn' : (0 : ℝ) < n := by positivity
  have hd' : (0 : ℝ) < d := by positivity
  let b := stdOrthonormalBasis ℝ E
  have hcard : (Fintype.card (Fin (finrank ℝ E)) : ℝ) = d := by simp [hd_def]
  -- the points `s / √d` of the unit ball
  have hvert (s : Fin (finrank ℝ E) → ℝ) (hs : ∀ i, |s i| = 1) :
      ∃ x : Metric.closedBall (0 : E) 1,
        ∀ i, ⟪b i, (x : E)⟫_ℝ = s i / √(Fintype.card (Fin (finrank ℝ E))) := by
    let v : E := ∑ i, (s i / √(Fintype.card (Fin (finrank ℝ E)))) • b i
    have hv (i : Fin (finrank ℝ E)) :
        ⟪b i, v⟫_ℝ = s i / √(Fintype.card (Fin (finrank ℝ E))) :=
      b.orthonormal.inner_right_fintype _ i
    have hnorm : ‖v‖ ^ 2 = 1 := by
      rw [← b.sum_sq_inner_right]
      have hs2 (i : Fin (finrank ℝ E)) : s i ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
      simp_rw [hv, div_pow, hs2, Real.sq_sqrt (Nat.cast_nonneg _),
        sum_const, card_univ, nsmul_eq_mul]
      rw [hcard]
      field_simp
    refine ⟨⟨v, ?_⟩, hv⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg v]
  set Δ : ℝ := √(σ2 / n) * √d / 2 with hΔ
  have hΔsq : Δ ^ 2 = σ2 * d / (4 * n) := by
    rw [hΔ, div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hd'.le]
    field_simp
    norm_num
  obtain ⟨θ, hθ, hR⟩ := exists_le_integral_linearRegret_gaussianLinearEnv_of_norm_le_one alg b
    measurable_subtype_coe hball hvert hσ2 n Δ (by positivity)
  refine ⟨θ, ?_, fun hθm ↦ le_of_eq_of_le ?_ (hR hθm)⟩
  · have hθ2 (i : Fin (finrank ℝ E)) : ⟪b i, θ⟫_ℝ ^ 2 = Δ ^ 2 := by rw [← sq_abs, hθ]
    rw [← b.sum_sq_inner_right]
    simp_rw [hθ2, sum_const, card_univ, nsmul_eq_mul, hcard, hΔsq]
    field_simp
  · rw [hcard, hΔsq]
    have hexp : 2 * (σ2 * d / (4 * n)) * n / (σ2 * d) = 1 / 2 := by
      field_simp
      ring
    have hsq : √(σ2 / n) * n = √(σ2 * n) := by
      rw [show (σ2 : ℝ) * n = σ2 / n * n ^ 2 by field_simp, Real.sqrt_mul (by positivity),
        Real.sqrt_sq hn'.le]
    have hd2 : √d * √d = d := Real.mul_self_sqrt hd'.le
    rw [hexp, hΔ, ← hsq]
    linear_combination (-(√(σ2 / n) * n * exp (-(1 / 2)) / 16)) * hd2

end UnitBall

end LMLExplore.Bandits
