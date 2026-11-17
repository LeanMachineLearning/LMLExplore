/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Algebra.Order.BigOperators.SignFlip
public import LMLExplore.Bandits.LinearBandit.DivergenceDecomposition
public import LMLExplore.Bandits.LinearBandit.SignedParameter
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

/-!
# The minimax lower bound for linear bandits on the unit ball

In a linear bandit with a fixed action set and Gaussian noise of variance `σ²`, the reward of an
action with feature `x ∈ E` has law `𝒩(⟪θ, x⟫, σ²)` for an unknown parameter `θ`. When the
features lie in the unit ball of `E`, of dimension `d`, and contain the points `s / √d` for the
sign patterns `s ∈ {±1}^d` of an orthonormal basis, every algorithm has, for some parameter `θ`
with `‖θ‖² = σ² d² / (48 n)`, an expected regret at least `d √(σ² n) / (16 √3)` after `n` rounds
[LS, Theorem 24.2]. More generally, for every `κ ≥ 0` some parameter with
`‖θ‖² = κ² σ² d² / n` gives an expected regret at least `κ (1 - κ) d √(σ² n) / 2`; [LS] is the
case `κ = 1 / (4 √3)`, and `κ = 1 / 2` gives the bound `d √(σ² n) / 8`. No relation between `d`
and `n` is needed, where [LS] assumes `d ≤ 2 n`.

The parameters are the `θ` with coordinates `±Δ` in the basis, and the point `s / √d` is the best
action against the parameter of signs `s`. Since the features lie in the unit ball, the regret of
a round is at least `Δ √d / 2` times the squared distance `∑ i, (⟪b i, x⟫ - s i / √d)²` from the
feature `x` played to that point, as in [LS]. Flipping the sign of the `i`-th coordinate of `θ`
replaces the `i`-th term `(⟪b i, x⟫ - s i / √d)²` by `(⟪b i, x⟫ + s i / √d)²`, and the two terms
add up to at least `2 / d` whatever `x` is. The flip changes the law of the history of the first
`n` rounds by the relative entropy `2 Δ² E[∑_{t < n} ⟪b i, X_t⟫²] / σ²` (the divergence
decomposition of `LMLExplore.Bandits.LinearBandit.DivergenceDecomposition`), and these relative
entropies add up over `i` to at most `2 Δ² n / σ²`, since the features `X_t` played lie in the
unit ball. Pinsker's inequality for the two runs (`LMLExplore.SequentialLearning.Pinsker`), the
concavity of the square root across the coordinates and the averaging over the `2^d` sign
patterns (`Fintype.exists_div_two_le_sum`) then give a parameter with regret at least
`Δ √d n (1 - Δ √(n / (σ² d))) / 2`. Distributing the relative entropies across the coordinates in
this way replaces the stopping times of [LS], which cap the information gathered on each
coordinate.

## Main statements

* `LMLExplore.Bandits.exists_mul_one_sub_le_integral_linearRegret_gaussianLinearEnv_of_norm_le_one`:
  the lower bound `Δ √d n (1 - Δ √(n / (σ² d))) / 2` for every `Δ ≥ 0`, for features in the unit
  ball that contain the points `s / √d`.
* `LMLExplore.Bandits.exists_mul_le_integral_linearRegret_gaussianLinearEnv_closedBall`: the lower
  bound `κ (1 - κ) d √(σ² n) / 2` with the unit ball of a finite-dimensional inner product space as
  the action set, for a parameter with `‖θ‖² = κ² σ² d² / n`.
* `LMLExplore.Bandits.exists_le_integral_linearRegret_gaussianLinearEnv_closedBall`:
  [LS, Theorem 24.2], the lower bound `d √(σ² n) / (16 √3)` for a parameter with
  `‖θ‖² = σ² d² / (48 n)`.

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
/-- The expected reward `⟪θ, φ a⟫` of an action with a feature in the unit ball is at most `‖θ‖` in
absolute value. -/
private lemma abs_inner_le_norm_of_norm_le_one (hball : ∀ a, ‖φ a‖ ≤ 1) (θ : E) (a : 𝓐) :
    |⟪θ, φ a⟫_ℝ| ≤ ‖θ‖ :=
  (abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hball a))

omit [MeasurableSpace 𝓐] in
/-- The expected rewards of actions with features in the unit ball are bounded above. -/
private lemma bddAbove_range_inner_of_norm_le_one (hball : ∀ a, ‖φ a‖ ≤ 1) (θ : E) :
    BddAbove (Set.range fun a ↦ ⟪θ, φ a⟫_ℝ) :=
  ⟨‖θ‖, by
    rintro _ ⟨a, rfl⟩
    exact (le_abs_self _).trans (abs_inner_le_norm_of_norm_le_one hball θ a)⟩

/-- For signs `s i` and an orthonormal basis `b` indexed by a nonempty finite type of size `d`, the
point `∑ i, (s i / √d) • b i` has norm `1`. -/
private lemma norm_sum_div_sqrt_card_smul [Nonempty ι] (b : OrthonormalBasis ι ℝ E)
    (hs : ∀ i, |s i| = 1) : ‖∑ i, (s i / √(Fintype.card ι)) • b i‖ = 1 := by
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hs2 (i : ι) : s i ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_
  rw [← b.sum_sq_inner_right]
  simp_rw [b.orthonormal.inner_right_fintype, div_pow, hs2, Real.sq_sqrt hd.le, sum_const,
    card_univ, nsmul_eq_mul]
  field_simp

omit [MeasurableSpace 𝓐] in
/-- Against a parameter with coordinates `Δ * s i` in the basis `b`, for signs `s i` and features
in the unit ball that contain the point `s / √d`, the best expected reward is at least `Δ √d`. -/
private lemma mul_sqrt_card_le_iSup_inner (hs : ∀ i, |s i| = 1) (hθ : ∀ i, ⟪b i, θ⟫_ℝ = Δ * s i)
    (hball : ∀ a, ‖φ a‖ ≤ 1) {a₀ : 𝓐} (ha₀ : ∀ i, ⟪b i, φ a₀⟫_ℝ = s i / √(Fintype.card ι)) :
    Δ * √(Fintype.card ι) ≤ ⨆ x, ⟪θ, φ x⟫_ℝ := by
  set d : ℝ := (Fintype.card ι : ℝ)
  have hvert : ∑ i, s i * ⟪b i, φ a₀⟫_ℝ = √d := by
    have h1 (i : ι) : s i * ⟪b i, φ a₀⟫_ℝ = 1 / √d := by
      rw [ha₀, mul_div_assoc', ← sq, ← sq_abs, hs, one_pow]
    rw [sum_congr rfl fun i _ ↦ h1 i, sum_const, card_univ, nsmul_eq_mul, mul_one_div,
      Real.div_sqrt]
  refine le_of_eq_of_le ?_ (le_ciSup (bddAbove_range_inner_of_norm_le_one hball θ) a₀)
  simp_rw [inner_eq_sum_of_inner_basis hθ, mul_assoc, ← mul_sum, hvert]

omit [MeasurableSpace 𝓐] in
/-- The gap of an action against a parameter with coordinates `Δ * s i`, for signs `s i` and
features in the unit ball that contain the point `s / √d`, is at least `Δ √d / 2` times the
squared distance `∑ i, (⟪b i, φ a⟫ - s i / √d)²` from the feature of the action to that point. -/
private lemma mul_sum_sq_sub_le_mul_iSup_inner_sub_inner (hΔ : 0 ≤ Δ) (hs : ∀ i, |s i| = 1)
    (hθ : ∀ i, ⟪b i, θ⟫_ℝ = Δ * s i) (hball : ∀ a, ‖φ a‖ ≤ 1) {a₀ : 𝓐}
    (ha₀ : ∀ i, ⟪b i, φ a₀⟫_ℝ = s i / √(Fintype.card ι)) (a : 𝓐) :
    Δ * √(Fintype.card ι) * ∑ i, (⟪b i, φ a⟫_ℝ - s i / √(Fintype.card ι)) ^ 2 ≤
      2 * ((⨆ x, ⟪θ, φ x⟫_ℝ) - ⟪θ, φ a⟫_ℝ) := by
  set d : ℝ := (Fintype.card ι : ℝ)
  have hsup := mul_sqrt_card_le_iSup_inner hs hθ hball ha₀
  have hinner : ⟪θ, φ a⟫_ℝ = Δ * ∑ i, s i * ⟪b i, φ a⟫_ℝ := by
    simp_rw [inner_eq_sum_of_inner_basis hθ, mul_sum, mul_assoc]
  have hnorm : ∑ i, ⟪b i, φ a⟫_ℝ ^ 2 ≤ 1 := by
    rw [b.sum_sq_inner_right]
    exact pow_le_one₀ (norm_nonneg _) (hball a)
  rcases (Real.sqrt_nonneg d).eq_or_lt with hd0 | hd0
  · rw [← hd0, mul_zero, zero_mul]
    linarith [le_ciSup (bddAbove_range_inner_of_norm_le_one hball θ) a]
  -- `√d (x - s / √d)² = √d x² - 2 s x + 1 / √d`, as `s² = 1`
  have hterm (i : ι) : √d * (⟪b i, φ a⟫_ℝ - s i / √d) ^ 2 =
      √d * ⟪b i, φ a⟫_ℝ ^ 2 - 2 * (s i * ⟪b i, φ a⟫_ℝ) + 1 / √d := by
    have hy : √d * (s i / √d) = s i := mul_div_cancel₀ _ hd0.ne'
    have hsq : s i ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
    linear_combination (-2 * ⟪b i, φ a⟫_ℝ + s i / √d) * hy + (1 / √d) * hsq
  have hsum : √d * ∑ i, (⟪b i, φ a⟫_ℝ - s i / √d) ^ 2 =
      √d * ∑ i, ⟪b i, φ a⟫_ℝ ^ 2 - 2 * ∑ i, s i * ⟪b i, φ a⟫_ℝ + √d := by
    rw [mul_sum, sum_congr rfl fun i _ ↦ hterm i, sum_add_distrib, sum_sub_distrib, ← mul_sum,
      ← mul_sum, sum_const, card_univ, nsmul_eq_mul, mul_one_div, Real.div_sqrt]
  calc Δ * √d * ∑ i, (⟪b i, φ a⟫_ℝ - s i / √d) ^ 2
      = Δ * (√d * ∑ i, ⟪b i, φ a⟫_ℝ ^ 2 - 2 * ∑ i, s i * ⟪b i, φ a⟫_ℝ + √d) := by
        rw [mul_assoc, hsum]
    _ ≤ Δ * (2 * √d - 2 * ∑ i, s i * ⟪b i, φ a⟫_ℝ) := by
        gcongr
        nlinarith
    _ = 2 * (Δ * √d - ⟪θ, φ a⟫_ℝ) := by
        rw [hinner]
        ring
    _ ≤ 2 * ((⨆ x, ⟪θ, φ x⟫_ℝ) - ⟪θ, φ a⟫_ℝ) := by gcongr

variable [MeasurableSpace E] [OpensMeasurableSpace E]

/-- The squared distances `(⟪b i, φ (A t)⟫ - y)²` of the coordinates of the features played to a
real `y` are integrable, for features in the unit ball. -/
private lemma integrable_inner_sub_sq {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {A : ℕ → Ω → 𝓐} (hA : ∀ t, Measurable (A t)) (hφ : Measurable φ)
    (hball : ∀ a, ‖φ a‖ ≤ 1) (b : OrthonormalBasis ι ℝ E) (i : ι) (y : ℝ) (t : ℕ) :
    Integrable (fun ω ↦ (⟪b i, φ (A t ω)⟫_ℝ - y) ^ 2) P := by
  refine Integrable.of_bound
    ((((hφ.const_inner' (b i)).comp (hA t)).sub_const y).pow_const 2).aestronglyMeasurable
    ((1 + |y|) ^ 2) (ae_of_all _ fun ω ↦ ?_)
  have hx : |⟪b i, φ (A t ω)⟫_ℝ| ≤ 1 :=
    calc |⟪b i, φ (A t ω)⟫_ℝ| ≤ ‖b i‖ * ‖φ (A t ω)‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 := by rw [b.norm_eq_one, one_mul]; exact hball _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  obtain ⟨hx1, hx2⟩ := abs_le.1 hx
  exact sq_le_sq' (by linarith [le_abs_self y]) (by linarith [neg_abs_le y])

/-- The squared coordinates of the features played are integrable, for features in the unit ball. -/
private lemma integrable_inner_sq {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {A : ℕ → Ω → 𝓐} (hA : ∀ t, Measurable (A t)) (hφ : Measurable φ)
    (hball : ∀ a, ‖φ a‖ ≤ 1) (b : OrthonormalBasis ι ℝ E) (i : ι) (t : ℕ) :
    Integrable (fun ω ↦ ⟪b i, φ (A t ω)⟫_ℝ ^ 2) P := by
  simpa using integrable_inner_sub_sq hA hφ hball b i 0 t

/-- **The regret bounds the squared distances.** For features in the unit ball and a parameter with
coordinates `Δ * s i`, for signs `s i` and features that contain the point `s / √d`, the expected
regret after `n` rounds is at least `Δ √d / 2` times the expected sum over the rounds `t < n` of
the squared distances `∑ i, (⟪b i, φ (A t)⟫ - s i / √d)²`. -/
private lemma mul_sum_sum_integral_le_mul_integral_linearRegret {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {A : ℕ → Ω → 𝓐}
    (hA : ∀ t, Measurable (A t)) (hφ : Measurable φ) (hball : ∀ a, ‖φ a‖ ≤ 1) (hΔ : 0 ≤ Δ)
    (hs : ∀ i, |s i| = 1) (hθ : ∀ i, ⟪b i, θ⟫_ℝ = Δ * s i) {a₀ : 𝓐}
    (ha₀ : ∀ i, ⟪b i, φ a₀⟫_ℝ = s i / √(Fintype.card ι)) (O : ℕ → Ω → Unit) (n : ℕ) :
    Δ * √(Fintype.card ι) * ∑ i, ∑ t ∈ range n,
        ∫ ω, (⟪b i, φ (A t ω)⟫_ℝ - s i / √(Fintype.card ι)) ^ 2 ∂P ≤
      2 * ∫ ω, linearRegret (fun _ ↦ φ) θ O A n ω ∂P := by
  have hint := integrable_inner_sub_sq (P := P) hA hφ hball b
  have hreg : Integrable (fun ω ↦ linearRegret (fun _ ↦ φ) θ O A n ω) P :=
    integrable_linearRegret (fun _ ↦ measurable_of_subsingleton_codomain _) hA
      ((hφ.const_inner' θ).comp measurable_snd) measurable_const
      fun _ ↦ abs_inner_le_norm_of_norm_le_one hball θ
  calc Δ * √(Fintype.card ι) * ∑ i, ∑ t ∈ range n,
        ∫ ω, (⟪b i, φ (A t ω)⟫_ℝ - s i / √(Fintype.card ι)) ^ 2 ∂P
      = ∫ ω, ∑ t ∈ range n, Δ * √(Fintype.card ι) *
          ∑ i, (⟪b i, φ (A t ω)⟫_ℝ - s i / √(Fintype.card ι)) ^ 2 ∂P := by
        rw [integral_finsetSum _ fun t _ ↦
          (integrable_finsetSum _ fun i _ ↦ hint i _ t).const_mul _, sum_comm, mul_sum]
        refine sum_congr rfl fun t _ ↦ ?_
        rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hint i _ t]
    _ ≤ ∫ ω, 2 * linearRegret (fun _ ↦ φ) θ O A n ω ∂P := by
        refine integral_mono (integrable_finsetSum _ fun t _ ↦
          (integrable_finsetSum _ fun i _ ↦ hint i _ t).const_mul _) (hreg.const_mul 2)
          fun ω ↦ ?_
        rw [linearRegret_def, mul_sum]
        exact sum_le_sum fun t _ ↦
          mul_sum_sq_sub_le_mul_iSup_inner_sub_inner hΔ hs hθ hball ha₀ _
    _ = 2 * ∫ ω, linearRegret (fun _ ↦ φ) θ O A n ω ∂P := integral_const_mul _ _

/-- **Flipping one sign.** Let `θ` and `θ'` have coordinates `Δ * s j` and `Δ * s' j` in the basis
`b`, for `Δ ≥ 0` and signs that agree except at `i`, where `s' i = -s i`. For features in the unit
ball, the expected squared distances `∑_{t < n} (⟪b i, φ (A t)⟫ - s i / √d)²` in a run against
`θ` and `∑_{t < n} (⟪b i, φ (A' t)⟫ - s' i / √d)²` in a run against `θ'` add up to at least
`2 n (1 - Δ √(q / σ²)) / d`, where `q = E[∑_{t < n} ⟪b i, φ (A t)⟫²]` in the run against `θ`. -/
private lemma two_mul_one_sub_div_le_sum_add_sum {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
    {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ}
    {O' : ℕ → Ω' → Unit} {A' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → ℝ} {alg : Algorithm Unit 𝓐 ℝ}
    {θ' : E} {s' : ι → ℝ} {hθm : Measurable fun p : Unit × 𝓐 ↦ ⟪θ, φ p.2⟫_ℝ}
    {hθm' : Measurable fun p : Unit × 𝓐 ↦ ⟪θ', φ p.2⟫_ℝ}
    (h : IsAlgEnvSeq O A Y alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ σ2 hθm) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ' σ2 hθm')
      P')
    (hσ2 : σ2 ≠ 0) (hφ : Measurable φ) (hball : ∀ a, ‖φ a‖ ≤ 1) (hΔ : 0 ≤ Δ) {i : ι}
    (hs : |s i| = 1) (hθ : ∀ j, ⟪b j, θ⟫_ℝ = Δ * s j) (hθ' : ∀ j, ⟪b j, θ'⟫_ℝ = Δ * s' j)
    (hs'i : s' i = -s i) (hs' : ∀ j ≠ i, s' j = s j) (n : ℕ) :
    2 * n * (1 - Δ * √((∑ t ∈ range n, ∫ ω, ⟪b i, φ (A t ω)⟫_ℝ ^ 2 ∂P) / σ2)) /
        Fintype.card ι ≤
      ∑ t ∈ range n, ∫ ω, (⟪b i, φ (A t ω)⟫_ℝ - s i / √(Fintype.card ι)) ^ 2 ∂P +
        ∑ t ∈ range n, ∫ ω, (⟪b i, φ (A' t ω)⟫_ℝ - s' i / √(Fintype.card ι)) ^ 2 ∂P' := by
  set d : ℝ := (Fintype.card ι : ℝ)
  set q := ∑ t ∈ range n, ∫ ω, ⟪b i, φ (A t ω)⟫_ℝ ^ 2 ∂P with hq
  have hsq : s i ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
  -- `θ - θ'` is `2 Δ s i b i`, so `⟪θ - θ', x⟫² = 4 Δ² ⟪b i, x⟫²`
  have hdiff (y : E) : ⟪θ - θ', y⟫_ℝ ^ 2 = 4 * Δ ^ 2 * ⟪b i, y⟫_ℝ ^ 2 := by
    rw [inner_sub_eq_of_inner_basis hθ hθ' hs'i hs' y, mul_pow, mul_pow, mul_pow, hsq]
    ring
  have hint (t : ℕ) : Integrable (fun ω ↦ ⟪θ - θ', φ (A t ω)⟫_ℝ ^ 2) P := by
    simp_rw [hdiff]
    exact (integrable_inner_sq h.measurable_action hφ hball b i t).const_mul _
  have hmeas (y : ℝ) : Measurable fun a ↦ (⟪b i, φ a⟫_ℝ - y) ^ 2 :=
    ((hφ.const_inner' (b i)).sub_const y).pow_const 2
  -- the two squared distances add up to `2 ⟪b i, x⟫² + 2 / d ≥ 2 / d`
  have hp := h.mul_one_sub_sqrt_le_sum_gaussianLinearEnv h' hσ2 hint n
    (f := fun a ↦ (⟪b i, φ a⟫_ℝ - s i / √d) ^ 2) (g := fun a ↦ (⟪b i, φ a⟫_ℝ - s' i / √d) ^ 2)
    (hmeas _) (hmeas _)
    (integrable_inner_sub_sq h.measurable_action hφ hball b i _)
    (integrable_inner_sub_sq h'.measurable_action hφ hball b i _) (fun _ ↦ sq_nonneg _)
    (fun _ ↦ sq_nonneg _) (c := 2 / d) (by positivity) fun a ↦ by
      have hy : (s i / √d) ^ 2 = 1 / d := by rw [div_pow, hsq, Real.sq_sqrt (Nat.cast_nonneg _)]
      have hfg : (⟪b i, φ a⟫_ℝ - s i / √d) ^ 2 + (⟪b i, φ a⟫_ℝ - -s i / √d) ^ 2 =
          2 * ⟪b i, φ a⟫_ℝ ^ 2 + 2 * (s i / √d) ^ 2 := by ring
      rw [hs'i, hfg, hy, mul_one_div]
      linarith [sq_nonneg ⟪b i, φ a⟫_ℝ]
  refine le_of_eq_of_le ?_ hp
  -- the relative entropy is `2 Δ² q / σ²`
  have hS : ∑ t ∈ range n, ∫ ω, ⟪θ - θ', φ (A t ω)⟫_ℝ ^ 2 ∂P = 4 * Δ ^ 2 * q := by
    simp_rw [hdiff, integral_const_mul, ← mul_sum, hq]
  have hσ : (σ2 : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hσ2
  rw [hS, show 4 * Δ ^ 2 * q / (4 * σ2) = Δ ^ 2 * (q / σ2) by field_simp,
    Real.sqrt_mul (sq_nonneg Δ), Real.sqrt_sq hΔ]
  ring

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- **Concavity across the coordinates.** If the nonnegative `q i` add up to at most `n`, then
`∑ i, 2 n (1 - Δ √(q i / σ²)) / d ≥ 2 n (1 - Δ √(n / (σ² d)))` for `Δ ≥ 0`, with `d` the
cardinality of the nonempty finite type `ι`. -/
private lemma two_mul_one_sub_le_sum [Nonempty ι] (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) {n : ℕ}
    (hq : ∑ i, q i ≤ n) (hΔ : 0 ≤ Δ) (σ2 : ℝ≥0) :
    2 * n * (1 - Δ * √(n / (σ2 * Fintype.card ι))) ≤
      ∑ i, 2 * n * (1 - Δ * √(q i / σ2)) / Fintype.card ι := by
  set d : ℝ := (Fintype.card ι : ℝ)
  have hd : 0 < d := Nat.cast_pos.2 Fintype.card_pos
  -- Cauchy–Schwarz: `∑ i, √(q i / σ²) ≤ √d √(n / σ²)`
  have hcs : ∑ i, √(q i / σ2) ≤ √d * √(n / σ2) := by
    have h := Real.sum_sqrt_mul_sqrt_le univ (f := fun _ ↦ (1 : ℝ)) (g := fun i ↦ q i / σ2)
      (fun _ ↦ zero_le_one) fun i ↦ div_nonneg (hq0 i) NNReal.zero_le_coe
    simp only [Real.sqrt_one, one_mul, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
    rw [← sum_div]
    exact div_le_div_of_nonneg_right hq NNReal.zero_le_coe
  have hkey : d * √(n / (σ2 * d)) = √d * √(n / σ2) := by
    have hsd : √d ≠ 0 := (Real.sqrt_pos.2 hd).ne'
    rw [← div_div, Real.sqrt_div' _ hd.le]
    calc d * (√(n / σ2) / √d) = √d * √d * (√(n / σ2) / √d) := by rw [Real.mul_self_sqrt hd.le]
      _ = √d * √(n / σ2) := by field_simp
  rw [← sum_div, le_div_iff₀ hd]
  simp only [mul_sub, mul_one, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
  have h2nΔ : 0 ≤ 2 * n * Δ := by positivity
  have := mul_le_mul_of_nonneg_left hcs h2nΔ
  nlinarith

/-- **Minimax lower bound for linear bandits with features in the unit ball**, after
[LS, Theorem 24.2]. Let `b` be an orthonormal basis of `E` indexed by a finite type of size `d`,
and let the features `φ a` of the actions lie in the unit ball and contain the points `s / √d`
(with coordinates `⟪b i, φ a⟫ = s i / √d`) for the sign patterns `s ∈ {±1}^d`. For Gaussian
noise of variance `σ2 ≠ 0`, a horizon `n` and `Δ ≥ 0`, every algorithm has, for some parameter `θ`
whose coordinates `⟪b i, θ⟫` are `±Δ`, an expected regret against the Gaussian linear environment
of parameter `θ` at least `Δ √d n (1 - Δ √(n / (σ² d))) / 2`. The bound holds for every proof
`hθ` of the measurability that `gaussianLinearEnv` takes, one of which is given by `hφ`. -/
theorem exists_mul_one_sub_le_integral_linearRegret_gaussianLinearEnv_of_norm_le_one
    (alg : Algorithm Unit 𝓐 ℝ) (b : OrthonormalBasis ι ℝ E) (hφ : Measurable φ)
    (hball : ∀ a, ‖φ a‖ ≤ 1)
    (hvert : ∀ s : ι → ℝ, (∀ i, |s i| = 1) → ∃ a, ∀ i, ⟪b i, φ a⟫_ℝ = s i / √(Fintype.card ι))
    (hσ2 : σ2 ≠ 0) (n : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    ∃ θ : E, (∀ i, |⟪b i, θ⟫_ℝ| = Δ) ∧
      ∀ hθ : Measurable fun p : Unit × 𝓐 ↦ ⟪θ, φ p.2⟫_ℝ,
        Δ * √(Fintype.card ι) * n * (1 - Δ * √(n / (σ2 * Fintype.card ι))) / 2 ≤
          ∫ ω, linearRegret (fun _ ↦ φ) θ IT.obs IT.action n ω
            ∂(trajMeasure alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ σ2 hθ)) := by
  classical
  -- without coordinates, the bound is `0`
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨0, fun i ↦ isEmptyElim i, fun _ ↦ ?_⟩
    rw [Fintype.card_eq_zero, Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_mul, zero_mul,
      zero_div]
    exact integral_linearRegret_nonneg fun _ ↦ bddAbove_range_inner_of_norm_le_one hball _
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
  -- `g ε i`: the expected squared distance of the `i`-th coordinate to `sg ε i / √d`
  let g : (ι → Bool) → ι → ℝ := fun ε i ↦ ∑ t ∈ range n,
    ∫ ω, (⟪b i, φ (IT.action t ω)⟫_ℝ - sg ε i / √d) ^ 2 ∂(P ε)
  -- `q ε i`: the expected information gathered on the `i`-th coordinate
  let q : (ι → Bool) → ι → ℝ := fun ε i ↦ ∑ t ∈ range n,
    ∫ ω, ⟪b i, φ (IT.action t ω)⟫_ℝ ^ 2 ∂(P ε)
  have hR (ε : ι → Bool) : Δ * √d * ∑ i, g ε i ≤
      2 * ∫ ω, linearRegret (fun _ ↦ φ) (θ ε) IT.obs IT.action n ω ∂(P ε) :=
    have ⟨_, ha₀⟩ := hvert _ (hsg ε)
    mul_sum_sum_integral_le_mul_integral_linearRegret (hrun ε).measurable_action hφ hball hΔ
      (hsg ε) (hθ ε) ha₀ _ n
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
  have hq0 (ε : ι → Bool) (i : ι) : 0 ≤ q ε i :=
    sum_nonneg fun t _ ↦ integral_nonneg fun ω ↦ sq_nonneg _
  -- flipping the sign of the coordinate `i` changes the law of the history by `2 Δ² q ε i / σ²`
  have hpair (ε : ι → Bool) (i : ι) : 2 * n * (1 - Δ * √(q ε i / σ2)) / d ≤
      g ε i + g (Function.update ε i (!ε i)) i := by
    refine two_mul_one_sub_div_le_sum_add_sum (hrun ε) (hrun _) hσ2 hφ hball hΔ (hsg ε i) (hθ ε)
      (hθ _) (s' := sg (Function.update ε i (!ε i))) (i := i) ?_ (fun j hj ↦ ?_) n
    · by_cases h : ε i <;> simp [sg, h]
    · simp [sg, Function.update_of_ne hj]
  -- averaging over the sign patterns
  obtain ⟨ε, hε⟩ := Fintype.exists_div_two_le_sum g _ hpair fun ε ↦
    two_mul_one_sub_le_sum (q ε) (hq0 ε) (hq ε) hΔ σ2
  refine ⟨θ ε, habs ε, fun _ ↦ ?_⟩
  rw [← hd_def] at hε
  have := mul_le_mul_of_nonneg_left hε (by positivity : 0 ≤ Δ * √d)
  calc Δ * √d * n * (1 - Δ * √(n / (σ2 * d))) / 2
      ≤ (Δ * √d * ∑ i, g ε i) / 2 := by linarith
    _ ≤ (2 * ∫ ω, linearRegret (fun _ ↦ φ) (θ ε) IT.obs IT.action n ω ∂(P ε)) / 2 := by
        exact div_le_div_of_nonneg_right (hR ε) zero_le_two
    _ = ∫ ω, linearRegret (fun _ ↦ φ) (θ ε) IT.obs IT.action n ω ∂(P ε) := by ring

/-- **Minimax lower bound for linear bandits on the unit ball**, with the unit ball of a
finite-dimensional inner product space `E` of dimension `d` as the action set and a parameter of
norm `κ √(σ² / n) d` (after [LS, Theorem 24.2]): for Gaussian noise of variance `σ2`, a horizon
`n` and `κ ≥ 0`, every algorithm has, for some parameter `θ` with `‖θ‖² = κ² σ² d² / n`, an
expected regret at least `κ (1 - κ) d √(σ² n) / 2`. The choice `κ = 1 / 2` gives the largest bound,
`d √(σ² n) / 8`, and `κ = 1 / (4 √3)` gives [LS, Theorem 24.2]
(`exists_le_integral_linearRegret_gaussianLinearEnv_closedBall`). -/
theorem exists_mul_le_integral_linearRegret_gaussianLinearEnv_closedBall [FiniteDimensional ℝ E]
    (alg : Algorithm Unit (Metric.closedBall (0 : E) 1) ℝ) (σ2 : ℝ≥0) (n : ℕ) {κ : ℝ}
    (hκ : 0 ≤ κ) :
    ∃ θ : E, ‖θ‖ ^ 2 = κ ^ 2 * σ2 * finrank ℝ E ^ 2 / n ∧
      ∀ hθ : Measurable fun p : Unit × Metric.closedBall (0 : E) 1 ↦ ⟪θ, (p.2 : E)⟫_ℝ,
        κ * (1 - κ) / 2 * finrank ℝ E * √(σ2 * n) ≤
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
    · refine le_of_eq_of_le ?_
        (integral_linearRegret_nonneg fun _ ↦ bddAbove_range_inner_of_norm_le_one hball _)
      rcases h0 with h0 | h0 | h0 <;> simp [h0, hd_def]
  simp only [not_or] at h0
  obtain ⟨hσ2, hn, hd⟩ := h0
  have hσ2' : (0 : ℝ) < σ2 := by positivity
  have hn' : (0 : ℝ) < n := by positivity
  have hd' : (0 : ℝ) < d := by positivity
  let b := stdOrthonormalBasis ℝ E
  have hcard : (Fintype.card (Fin (finrank ℝ E)) : ℝ) = d := by simp [hd_def]
  -- the points `s / √d` of the unit ball
  have : Nonempty (Fin (finrank ℝ E)) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
  have hvert (s : Fin (finrank ℝ E) → ℝ) (hs : ∀ i, |s i| = 1) :
      ∃ x : Metric.closedBall (0 : E) 1,
        ∀ i, ⟪b i, (x : E)⟫_ℝ = s i / √(Fintype.card (Fin (finrank ℝ E))) :=
    ⟨⟨_, mem_closedBall_zero_iff.2 (norm_sum_div_sqrt_card_smul b hs).le⟩,
      b.orthonormal.inner_right_fintype _⟩
  set Δ : ℝ := κ * √(σ2 / n) * √d with hΔ
  have hΔsq : Δ ^ 2 = κ ^ 2 * σ2 * d / n := by
    rw [hΔ, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hd'.le]
    ring
  obtain ⟨θ, hθ, hR⟩ := exists_mul_one_sub_le_integral_linearRegret_gaussianLinearEnv_of_norm_le_one
    alg b measurable_subtype_coe hball hvert hσ2 n Δ (by positivity)
  refine ⟨θ, ?_, fun hθm ↦ le_of_eq_of_le ?_ (hR hθm)⟩
  · have hθ2 (i : Fin (finrank ℝ E)) : ⟪b i, θ⟫_ℝ ^ 2 = Δ ^ 2 := by rw [← sq_abs, hθ]
    rw [← b.sum_sq_inner_right]
    simp_rw [hθ2, sum_const, card_univ, nsmul_eq_mul, hcard, hΔsq]
    ring
  · rw [hcard]
    -- `Δ √(n / (σ² d)) = κ` and `√(σ² / n) n = √(σ² n)`
    have hκΔ : Δ * √(n / (σ2 * d)) = κ := by
      rw [hΔ, mul_assoc, mul_assoc, ← Real.sqrt_mul (by positivity),
        ← Real.sqrt_mul (by positivity)]
      rw [show (σ2 : ℝ) / n * (d * (n / (σ2 * d))) = 1 by field_simp, Real.sqrt_one, mul_one]
    have hsq : √(σ2 / n) * n = √(σ2 * n) := by
      rw [show (σ2 : ℝ) * n = σ2 / n * n ^ 2 by field_simp, Real.sqrt_mul (by positivity),
        Real.sqrt_sq hn'.le]
    have hd2 : √d * √d = d := Real.mul_self_sqrt hd'.le
    rw [hκΔ, hΔ, ← hsq]
    linear_combination (-(κ * (1 - κ) * √(σ2 / n) * n / 2)) * hd2

/-- **Minimax lower bound for linear bandits on the unit ball** [LS, Theorem 24.2], with the unit
ball of a finite-dimensional inner product space `E` of dimension `d` as the action set: for
Gaussian noise of variance `σ2` and a horizon `n`, every algorithm has, for some parameter `θ` with
`‖θ‖² = σ² d² / (48 n)`, an expected regret at least `d √(σ² n) / (16 √3)`. [LS] states this for
`σ² = 1` and assumes `d ≤ 2 n`, which is not needed here. -/
theorem exists_le_integral_linearRegret_gaussianLinearEnv_closedBall [FiniteDimensional ℝ E]
    (alg : Algorithm Unit (Metric.closedBall (0 : E) 1) ℝ) (σ2 : ℝ≥0) (n : ℕ) :
    ∃ θ : E, ‖θ‖ ^ 2 = σ2 * finrank ℝ E ^ 2 / (48 * n) ∧
      ∀ hθ : Measurable fun p : Unit × Metric.closedBall (0 : E) 1 ↦ ⟪θ, (p.2 : E)⟫_ℝ,
        finrank ℝ E * √(σ2 * n) / (16 * √3) ≤
          ∫ ω, linearRegret (fun _ ↦ Subtype.val) θ IT.obs IT.action n ω
            ∂(trajMeasure alg
              (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ Subtype.val) θ σ2 hθ)) := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h3pos : 0 < √3 := by positivity
  obtain ⟨θ, hθ, hR⟩ := exists_mul_le_integral_linearRegret_gaussianLinearEnv_closedBall alg σ2 n
    (κ := 1 / (4 * √3)) (by positivity)
  refine ⟨θ, hθ.trans ?_, fun hθm ↦ (hR hθm).trans' ?_⟩
  · rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  -- `κ (1 - κ) / 2 ≥ 1 / (16 √3)` for `κ = 1 / (4 √3) ≤ 1 / 2`
  have hκ : 1 / (16 * √3) ≤ 1 / (4 * √3) * (1 - 1 / (4 * √3)) / 2 := by
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hpos : 0 ≤ (finrank ℝ E : ℝ) * √(σ2 * n) := by positivity
  calc (finrank ℝ E : ℝ) * √(σ2 * n) / (16 * √3)
      = 1 / (16 * √3) * (finrank ℝ E * √(σ2 * n)) := by ring
    _ ≤ 1 / (4 * √3) * (1 - 1 / (4 * √3)) / 2 * (finrank ℝ E * √(σ2 * n)) := by gcongr
    _ = _ := by ring

end UnitBall

end LMLExplore.Bandits
