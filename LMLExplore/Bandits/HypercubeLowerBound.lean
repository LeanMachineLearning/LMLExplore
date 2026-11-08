/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.LinearBandit
public import LMLExplore.InformationTheory.KullbackLeibler.Gaussian
public import LMLExplore.SequentialLearning.BretagnolleHuber
public import LMLExplore.SequentialLearning.Environments.Stationary
public import LeanMachineLearning.SequentialLearning.DivergenceDecomposition
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

/-!
# The minimax lower bound for linear bandits on the hypercube

In a linear bandit with a fixed action set and Gaussian noise of variance `σ²`, the reward of an
action with feature `x ∈ E` has law `𝒩(⟪θ, x⟫, σ²)` for an unknown parameter `θ`. When the features
lie in the hypercube `{x : ∀ i, |⟪b i, x⟫| ≤ 1}` of an orthonormal basis `b` of `E`, indexed by a
finite type of size `d`, and contain its `2^d` vertices, every algorithm has, for some parameter
`θ` with coordinates `⟪b i, θ⟫ = ±√(σ² / n)`, an expected regret at least
`e^{-2} d √(σ² n) / 4` after `n` rounds. This is [LS, Theorem 24.1], whose action set is the
hypercube `[-1, 1]^d` itself, with variance `1` and the constant `e^{-2} / 8`.

The proof compares, for each coordinate `i`, the parameters `θ` and `θ'` that differ only in the
sign of their `i`-th coordinate. In a round in which the `i`-th coordinate of the feature played
does not have the sign of `⟪b i, θ⟫`, the algorithm loses at least `√(σ² / n)` against `θ`; and
an action loses in this way against `θ` or against `θ'`. The relative entropy between the laws of
the histories of the first `n` rounds against `θ` and `θ'` is
`∑_{t < n} E[⟪θ - θ', X_t⟫²] / (2σ²) ≤ 2`, so by the Bretagnolle–Huber inequality, summed over
the rounds, the expected numbers of such rounds against `θ` and against `θ'` add up to at least
`n e^{-2} / 2`. Averaging over the `2^d` sign patterns gives a parameter for which the expected
numbers of such rounds, summed over the coordinates, are at least `d n e^{-2} / 4`. Applying the
Bretagnolle–Huber inequality round by round, instead of to the event that a coordinate has the
wrong sign in at least half of the rounds, gives twice the constant of [LS].

## Main statements

* `Learning.IsAlgEnvSeq.klDiv_map_history_gaussianLinearEnv`: the divergence decomposition for a
  linear bandit with a fixed action set and Gaussian noise: the relative entropy between the laws
  of the histories of the first `n` rounds against the parameters `θ` and `θ'` is
  `∑_{t < n} E[⟪θ - θ', X_t⟫² / (2σ²)]`, for the features `X_t` of the actions played.
* `Learning.IsAlgEnvSeq.klDiv_map_history_gaussianLinearEnv_le`: it is at most `n δ / (2σ²)` when
  `⟪θ - θ', x⟫² ≤ δ` for every feature `x`.
* `Learning.IsAlgEnvSeq.mul_exp_neg_div_two_le_sum_gaussianLinearEnv`: the Bretagnolle–Huber
  inequality, summed over the rounds, for two such parameters.
* `LMLExplore.Bandits.exists_le_integral_linearRegret_gaussianLinearEnv`: the lower bound for
  features between the vertices and the hypercube of an orthonormal basis.
* `LMLExplore.Bandits.exists_le_integral_linearRegret_gaussianLinearEnv_cube`: the lower bound
  with the hypercube `[-1, 1]^ι` of `EuclideanSpace ℝ ι` as the action set [LS, Theorem 24.1].

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Theorem 24.1.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset Real Learning
open scoped ENNReal NNReal InnerProductSpace

namespace LMLExplore.Bandits

variable {ι 𝓐 E : Type*} [MeasurableSpace 𝓐] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {φ : 𝓐 → E} {σ2 : ℝ≥0}

section Divergence

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ}
  {O' : ℕ → Ω' → Unit} {A' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → ℝ} {alg : Algorithm Unit 𝓐 ℝ}
  {θ θ' : E} {hθ : Measurable fun p : Unit × 𝓐 ↦ ⟪θ, φ p.2⟫_ℝ}
  {hθ' : Measurable fun p : Unit × 𝓐 ↦ ⟪θ', φ p.2⟫_ℝ}

/-- **Divergence decomposition for linear bandits with Gaussian noise.** Run an algorithm against
the Gaussian linear environments with a fixed action set, features `φ`, variance `σ2 ≠ 0` and
parameters `θ` and `θ'`. The relative entropy between the laws of the histories of the first `n`
rounds is `∑_{t < n} E[⟪θ - θ', φ (A t)⟫² / (2σ²)]`, the expectation being under the run against
`θ`. -/
theorem _root_.Learning.IsAlgEnvSeq.klDiv_map_history_gaussianLinearEnv
    (h : IsAlgEnvSeq O A Y alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ σ2 hθ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ' σ2 hθ')
      P')
    (hσ2 : σ2 ≠ 0) (n : ℕ) :
    klDiv (P.map (history O A Y n)) (P'.map (history O' A' Y' n)) =
      ∑ t ∈ range n, ∫⁻ ω, ENNReal.ofReal (⟪θ - θ', φ (A t ω)⟫_ℝ ^ 2 / (2 * σ2)) ∂P := by
  rw [gaussianLinearEnv_def, Environment.stationary_dirac_unit_eq_bandit] at h h'
  rw [h.klDiv_map_history_bandit h']
  refine sum_congr rfl fun t _ ↦ lintegral_congr fun ω ↦ ?_
  rw [Kernel.comap_apply, Kernel.comap_apply, gaussianLinearKernel_apply,
    gaussianLinearKernel_apply, klDiv_gaussianReal_gaussianReal_same_var hσ2, inner_sub_left]

/-- If `⟪θ - θ', x⟫² ≤ δ` for every feature `x`, the relative entropy between the laws of the
histories of the first `n` rounds of an algorithm against the Gaussian linear environments with
parameters `θ` and `θ'` and variance `σ2 ≠ 0` is at most `n δ / (2σ²)`. -/
theorem _root_.Learning.IsAlgEnvSeq.klDiv_map_history_gaussianLinearEnv_le
    (h : IsAlgEnvSeq O A Y alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ σ2 hθ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ' σ2 hθ')
      P')
    (hσ2 : σ2 ≠ 0) {δ : ℝ} (hδ : ∀ a, ⟪θ - θ', φ a⟫_ℝ ^ 2 ≤ δ) (n : ℕ) :
    klDiv (P.map (history O A Y n)) (P'.map (history O' A' Y' n)) ≤
      ENNReal.ofReal (n * δ / (2 * σ2)) := by
  rw [h.klDiv_map_history_gaussianLinearEnv h' hσ2]
  calc ∑ t ∈ range n, ∫⁻ ω, ENNReal.ofReal (⟪θ - θ', φ (A t ω)⟫_ℝ ^ 2 / (2 * σ2)) ∂P
      ≤ ∑ t ∈ range n, ENNReal.ofReal (δ / (2 * σ2)) := by
        refine sum_le_sum fun t _ ↦ ?_
        calc ∫⁻ ω, ENNReal.ofReal (⟪θ - θ', φ (A t ω)⟫_ℝ ^ 2 / (2 * σ2)) ∂P
            ≤ ∫⁻ _, ENNReal.ofReal (δ / (2 * σ2)) ∂P :=
              lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal (by gcongr; exact hδ _)
          _ = ENNReal.ofReal (δ / (2 * σ2)) := by simp
    _ = ENNReal.ofReal (n * δ / (2 * σ2)) := by
        rw [sum_const, card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg n), mul_div_assoc]

/-- **Bretagnolle–Huber inequality for linear bandits with Gaussian noise.** If `⟪θ - θ', x⟫² ≤ δ`
for every feature `x`, then for a measurable set `S` of actions, the expected number of rounds
`t < n` with `A t ∈ S` in the run against `θ` plus the expected number of rounds `t < n` with
`A' t ∉ S` in the run against `θ'` is at least `n exp (-n δ / (2σ²)) / 2`. -/
theorem _root_.Learning.IsAlgEnvSeq.mul_exp_neg_div_two_le_sum_gaussianLinearEnv
    (h : IsAlgEnvSeq O A Y alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ σ2 hθ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ' σ2 hθ')
      P')
    (hσ2 : σ2 ≠ 0) {δ : ℝ} (hδ : ∀ a, ⟪θ - θ', φ a⟫_ℝ ^ 2 ≤ δ) (n : ℕ) {S : Set 𝓐}
    (hS : MeasurableSet S) :
    n * exp (-(n * δ / (2 * σ2))) / 2 ≤
      ∑ t ∈ range n, P.real (A t ⁻¹' S) + ∑ t ∈ range n, P'.real (A' t ⁻¹' Sᶜ) := by
  have hkl := h.klDiv_map_history_gaussianLinearEnv_le h' hσ2 hδ n
  have hbh := mul_exp_neg_klDiv_map_history_div_two_le_sum (h.measurable_history n)
    (h'.measurable_history n) hS (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl)
  obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure P
  have hδ0 : 0 ≤ δ := (sq_nonneg _).trans (hδ (A 0 ω))
  refine le_trans (le_of_eq_of_le (mul_div_assoc _ _ _) ?_) hbh
  gcongr
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hkl

end Divergence

section Hypercube

variable [Fintype ι] {b : OrthonormalBasis ι ℝ E} {θ : E} {Δ : ℝ} {s : ι → ℝ}

/-- The inner product with a parameter whose coordinates in the basis `b` are `Δ * s i`. -/
private lemma inner_eq_sum_of_inner_basis (hθ : ∀ i, ⟪b i, θ⟫_ℝ = Δ * s i) (x : E) :
    ⟪θ, x⟫_ℝ = ∑ i, Δ * s i * ⟪b i, x⟫_ℝ := by
  rw [← b.sum_inner_mul_inner θ x]
  exact sum_congr rfl fun i _ ↦ by rw [real_inner_comm (b i) θ, hθ]

private lemma abs_inner_le_of_inner_basis (hΔ : 0 ≤ Δ) (hs : ∀ i, |s i| = 1)
    (hθ : ∀ i, ⟪b i, θ⟫_ℝ = Δ * s i) {x : E} (hx : ∀ i, |⟪b i, x⟫_ℝ| ≤ 1) :
    |⟪θ, x⟫_ℝ| ≤ Δ * Fintype.card ι := by
  rw [inner_eq_sum_of_inner_basis hθ]
  calc |∑ i, Δ * s i * ⟪b i, x⟫_ℝ| ≤ ∑ i, |Δ * s i * ⟪b i, x⟫_ℝ| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : ι, Δ := sum_le_sum fun i _ ↦ by
        rw [abs_mul, abs_mul, abs_of_nonneg hΔ, hs i, mul_one]
        exact mul_le_of_le_one_right hΔ (hx i)
    _ = Δ * Fintype.card ι := by rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

omit [MeasurableSpace 𝓐] in
/-- The gap of an action against a parameter with coordinates `Δ * s i`, for signs `s i` and
features in the hypercube that contains the vertex `s`, is at least `Δ` times the number of
coordinates `i` at which the feature of the action does not have the sign `s i`. -/
private lemma mul_sum_indicator_le_iSup_inner_sub_inner (hΔ : 0 ≤ Δ) (hs : ∀ i, |s i| = 1)
    (hθ : ∀ i, ⟪b i, θ⟫_ℝ = Δ * s i) (hcube : ∀ a i, |⟪b i, φ a⟫_ℝ| ≤ 1) {a₀ : 𝓐}
    (ha₀ : ∀ i, ⟪b i, φ a₀⟫_ℝ = s i) (a : 𝓐) :
    Δ * ∑ i, {x : 𝓐 | s i * ⟪b i, φ x⟫_ℝ ≤ 0}.indicator 1 a ≤
      (⨆ x, ⟪θ, φ x⟫_ℝ) - ⟪θ, φ a⟫_ℝ := by
  have hbdd : BddAbove (Set.range fun x ↦ ⟪θ, φ x⟫_ℝ) :=
    ⟨Δ * Fintype.card ι, by
      rintro _ ⟨x, rfl⟩
      exact (le_abs_self _).trans (abs_inner_le_of_inner_basis hΔ hs hθ (hcube x))⟩
  have hvert : ⟪θ, φ a₀⟫_ℝ = Δ * Fintype.card ι := by
    have h1 (i : ι) : Δ * s i * ⟪b i, φ a₀⟫_ℝ = Δ := by
      rw [ha₀, mul_assoc, ← abs_mul_abs_self, hs, mul_one, mul_one]
    rw [inner_eq_sum_of_inner_basis hθ, sum_congr rfl fun i _ ↦ h1 i, sum_const, card_univ,
      nsmul_eq_mul, mul_comm]
  have hsup := le_of_eq_of_le hvert.symm (le_ciSup hbdd a₀)
  have hterm (i : ι) :
      {x : 𝓐 | s i * ⟪b i, φ x⟫_ℝ ≤ 0}.indicator (1 : 𝓐 → ℝ) a ≤ 1 - s i * ⟪b i, φ a⟫_ℝ := by
    by_cases ha : s i * ⟪b i, φ a⟫_ℝ ≤ 0
    · rw [Set.indicator_of_mem (by exact ha), Pi.one_apply]
      linarith
    · rw [Set.indicator_of_notMem (by exact ha), sub_nonneg]
      calc s i * ⟪b i, φ a⟫_ℝ ≤ |s i * ⟪b i, φ a⟫_ℝ| := le_abs_self _
        _ ≤ 1 := by rw [abs_mul, hs i, one_mul]; exact hcube a i
  calc Δ * ∑ i, {x : 𝓐 | s i * ⟪b i, φ x⟫_ℝ ≤ 0}.indicator 1 a
      ≤ ∑ i, Δ * (1 - s i * ⟪b i, φ a⟫_ℝ) := by
        rw [mul_sum]
        exact sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hterm i) hΔ
    _ = Δ * Fintype.card ι - ⟪θ, φ a⟫_ℝ := by
        rw [inner_eq_sum_of_inner_basis hθ]
        simp_rw [mul_sub, mul_one, sum_sub_distrib, mul_assoc]
        rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]
    _ ≤ (⨆ x, ⟪θ, φ x⟫_ℝ) - ⟪θ, φ a⟫_ℝ := by linarith

variable [MeasurableSpace E] [OpensMeasurableSpace E]

/-- The expected regret of a run against a parameter with coordinates `Δ * s i`, for signs `s i`
and features in the hypercube that contains the vertex `s`, is at least `Δ` times the expected
number of pairs of a round and a coordinate `i` at which the feature of the action played does not
have the sign `s i`. -/
private lemma mul_sum_sum_measureReal_le_integral_linearRegret {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → 𝓐} (hA : ∀ t, Measurable (A t))
    (hφ : Measurable φ) (hΔ : 0 ≤ Δ) (hs : ∀ i, |s i| = 1) (hθ : ∀ i, ⟪b i, θ⟫_ℝ = Δ * s i)
    (hcube : ∀ a i, |⟪b i, φ a⟫_ℝ| ≤ 1) (hvert : ∃ a, ∀ i, ⟪b i, φ a⟫_ℝ = s i)
    (O : ℕ → Ω → Unit) (n : ℕ) :
    Δ * ∑ i, ∑ t ∈ range n, P.real (A t ⁻¹' {x | s i * ⟪b i, φ x⟫_ℝ ≤ 0}) ≤
      ∫ ω, linearRegret (fun _ ↦ φ) θ O A n ω ∂P := by
  obtain ⟨a₀, ha₀⟩ := hvert
  have hinner (v : E) : Measurable fun a ↦ ⟪v, φ a⟫_ℝ :=
    (continuous_const.inner continuous_id).measurable.comp hφ
  have hS (i : ι) : MeasurableSet {x | s i * ⟪b i, φ x⟫_ℝ ≤ 0} :=
    measurableSet_le ((hinner (b i)).const_mul (s i)) measurable_const
  have hind (i : ι) (t : ℕ) :
      Integrable ((A t ⁻¹' {x | s i * ⟪b i, φ x⟫_ℝ ≤ 0}).indicator (1 : Ω → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator (hA t (hS i))
  have hreg : Integrable (fun ω ↦ linearRegret (fun _ ↦ φ) θ O A n ω) P := by
    simp_rw [linearRegret_def]
    refine integrable_finsetSum _ fun t _ ↦ (integrable_const _).sub ?_
    refine Integrable.of_bound ((hinner θ).comp (hA t)).aestronglyMeasurable (Δ * Fintype.card ι)
      (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs]
    exact abs_inner_le_of_inner_basis hΔ hs hθ (hcube _)
  calc Δ * ∑ i, ∑ t ∈ range n, P.real (A t ⁻¹' {x | s i * ⟪b i, φ x⟫_ℝ ≤ 0})
      = ∫ ω, Δ * ∑ i, ∑ t ∈ range n,
          (A t ⁻¹' {x | s i * ⟪b i, φ x⟫_ℝ ≤ 0}).indicator 1 ω ∂P := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun t _ ↦
          hind i t]
        simp_rw [integral_finsetSum _ fun t _ ↦ hind _ t, integral_indicator_one (hA _ (hS _))]
    _ ≤ ∫ ω, linearRegret (fun _ ↦ φ) θ O A n ω ∂P := by
        refine integral_mono (((integrable_finsetSum _ fun i _ ↦
          integrable_finsetSum _ fun t _ ↦ hind i t)).const_mul Δ) hreg fun ω ↦ ?_
        rw [linearRegret_def, sum_comm, mul_sum]
        refine sum_le_sum fun t _ ↦ ?_
        simpa [Set.indicator_apply] using
          mul_sum_indicator_le_iSup_inner_sub_inner hΔ hs hθ hcube ha₀ (A t ω)

/-- **Averaging over the sign patterns.** If `c ≤ g ε i + g ε' i` whenever `ε'` is `ε` with the
`i`-th sign flipped, then some sign pattern `ε` has `d c / 2 ≤ ∑ i, g ε i`. -/
private lemma exists_card_mul_div_two_le_sum [DecidableEq ι]
    (g : (ι → Bool) → ι → ℝ) {c : ℝ}
    (hg : ∀ ε i, c ≤ g ε i + g (Function.update ε i (!ε i)) i) :
    ∃ ε, Fintype.card ι * c / 2 ≤ ∑ i, g ε i := by
  have hinv (i : ι) : Function.Involutive fun ε : ι → Bool ↦ Function.update ε i (!ε i) :=
    fun ε ↦ by
      simp only [Function.update_self, Bool.not_not, Function.update_idem, Function.update_eq_self]
  have hflip (i : ι) : ∑ ε, g (Function.update ε i (!ε i)) i = ∑ ε, g ε i :=
    Fintype.sum_bijective _ (hinv i).bijective _ _ fun _ ↦ rfl
  have hi (i : ι) : (Fintype.card (ι → Bool) : ℝ) * c / 2 ≤ ∑ ε, g ε i := by
    have := sum_le_sum fun ε (_ : ε ∈ univ) ↦ hg ε i
    rw [sum_add_distrib, hflip, sum_const, card_univ, nsmul_eq_mul] at this
    linarith
  have hsum : ∑ _ : ι → Bool, (Fintype.card ι : ℝ) * c / 2 ≤ ∑ ε, ∑ i, g ε i := by
    rw [sum_comm]
    calc ∑ _ : ι → Bool, (Fintype.card ι : ℝ) * c / 2
        = ∑ _ : ι, (Fintype.card (ι → Bool) : ℝ) * c / 2 := by
          simp only [sum_const, card_univ, nsmul_eq_mul]
          ring
      _ ≤ ∑ i, ∑ ε, g ε i := sum_le_sum fun i _ ↦ hi i
  obtain ⟨ε, -, hε⟩ := exists_le_of_sum_le univ_nonempty hsum
  exact ⟨ε, hε⟩

/-- **Flipping one sign.** Let `θ` and `θ'` have coordinates `Δ * s j` and `Δ * s' j` in the basis
`b`, for signs that agree except at `i`, where `s' i = -s i`, and let `n Δ² ≤ σ²`. For features in
the hypercube, the expected numbers of rounds `t < n` at which the `i`-th coordinate of the feature
played does not have the sign `s i` in a run against `θ`, and the sign `s' i` in a run against
`θ'`, add up to at least `n e^{-2} / 2`. -/
private lemma mul_exp_neg_two_div_two_le_sum_add_sum {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
    {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ}
    {O' : ℕ → Ω' → Unit} {A' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → ℝ} {alg : Algorithm Unit 𝓐 ℝ}
    {θ' : E} {s' : ι → ℝ} {hθm : Measurable fun p : Unit × 𝓐 ↦ ⟪θ, φ p.2⟫_ℝ}
    {hθm' : Measurable fun p : Unit × 𝓐 ↦ ⟪θ', φ p.2⟫_ℝ}
    (h : IsAlgEnvSeq O A Y alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ σ2 hθm) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ' σ2 hθm')
      P')
    (hσ2 : σ2 ≠ 0) (hφ : Measurable φ) (hcube : ∀ a i, |⟪b i, φ a⟫_ℝ| ≤ 1) {i : ι}
    (hs : |s i| = 1) (hθ : ∀ j, ⟪b j, θ⟫_ℝ = Δ * s j) (hθ' : ∀ j, ⟪b j, θ'⟫_ℝ = Δ * s' j)
    (hs'i : s' i = -s i) (hs' : ∀ j ≠ i, s' j = s j) {n : ℕ} (hn : n * Δ ^ 2 ≤ σ2) :
    n * exp (-2) / 2 ≤ ∑ t ∈ range n, P.real (A t ⁻¹' {x | s i * ⟪b i, φ x⟫_ℝ ≤ 0}) +
      ∑ t ∈ range n, P'.real (A' t ⁻¹' {x | s' i * ⟪b i, φ x⟫_ℝ ≤ 0}) := by
  -- `θ - θ'` is `2 Δ s i b i`, so `⟪θ - θ', x⟫² ≤ 4 Δ²` on the hypercube
  have hdiff (a : 𝓐) : ⟪θ - θ', φ a⟫_ℝ ^ 2 ≤ 4 * Δ ^ 2 := by
    have heq : ⟪θ - θ', φ a⟫_ℝ = 2 * Δ * s i * ⟪b i, φ a⟫_ℝ := by
      rw [inner_sub_left, inner_eq_sum_of_inner_basis hθ, inner_eq_sum_of_inner_basis hθ',
        ← sum_sub_distrib, Fintype.sum_eq_single i fun j hj ↦ by rw [hs' j hj, sub_self], hs'i]
      ring
    have hsq : s i ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
    have hc : ⟪b i, φ a⟫_ℝ ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (hcube a i)
    rw [heq, mul_pow, mul_pow, mul_pow, hsq, mul_one]
    nlinarith [sq_nonneg Δ]
  have hnΔ : n * (4 * Δ ^ 2) / (2 * σ2) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hS : MeasurableSet {x | s i * ⟪b i, φ x⟫_ℝ ≤ 0} :=
    measurableSet_le (((continuous_const.inner continuous_id).measurable.comp hφ).const_mul (s i))
      measurable_const
  have hbh := h.mul_exp_neg_div_two_le_sum_gaussianLinearEnv h' hσ2 hdiff n hS
  -- an action on the wrong side for `θ'` is one on the right side for `θ`
  have hsub : {x | s i * ⟪b i, φ x⟫_ℝ ≤ 0}ᶜ ⊆ {x | s' i * ⟪b i, φ x⟫_ℝ ≤ 0} := fun x hx ↦ by
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx ⊢
    rw [hs'i, neg_mul]
    exact neg_nonpos.2 hx.le
  calc (n : ℝ) * exp (-2) / 2 ≤ n * exp (-(n * (4 * Δ ^ 2) / (2 * σ2))) / 2 := by gcongr
    _ ≤ _ := hbh
    _ ≤ _ := by
      refine add_le_add le_rfl (sum_le_sum fun t _ ↦ ?_)
      exact measureReal_mono (Set.preimage_mono hsub)

/-- **Minimax lower bound for linear bandits on the hypercube** [LS, Theorem 24.1]. Let `b` be an
orthonormal basis of `E` indexed by a finite type of size `d`, and let the features `φ a` of the
actions lie in the hypercube `{x : ∀ i, |⟪b i, x⟫| ≤ 1}` and contain its vertices. For Gaussian
noise of variance `σ2` and a horizon `n`, every algorithm has, for some parameter `θ` whose
coordinates `⟪b i, θ⟫` are `±√(σ² / n)`, an expected regret against the Gaussian linear
environment of parameter `θ` at least `e^{-2} d √(σ² n) / 4` (twice the constant of [LS]). The
bound holds for every proof `hθ` of the measurability that `gaussianLinearEnv` takes, one of which
is given by `hφ`. -/
theorem exists_le_integral_linearRegret_gaussianLinearEnv (alg : Algorithm Unit 𝓐 ℝ)
    (b : OrthonormalBasis ι ℝ E) (hφ : Measurable φ) (hcube : ∀ a i, |⟪b i, φ a⟫_ℝ| ≤ 1)
    (hvert : ∀ s : ι → ℝ, (∀ i, |s i| = 1) → ∃ a, ∀ i, ⟪b i, φ a⟫_ℝ = s i) (σ2 : ℝ≥0) (n : ℕ) :
    ∃ θ : E, (∀ i, |⟪b i, θ⟫_ℝ| = √(σ2 / n)) ∧
      ∀ hθ : Measurable fun p : Unit × 𝓐 ↦ ⟪θ, φ p.2⟫_ℝ,
        exp (-2) / 4 * Fintype.card ι * √(σ2 * n) ≤
          ∫ ω, linearRegret (fun _ ↦ φ) θ IT.obs IT.action n ω
            ∂(trajMeasure alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ σ2 hθ)) := by
  classical
  set Δ := √(σ2 / n) with hΔ
  have hΔ0 : 0 ≤ Δ := Real.sqrt_nonneg _
  -- the parameters `θ ε` with coordinates `±Δ`, for the sign patterns `ε : ι → Bool`
  let sg : (ι → Bool) → ι → ℝ := fun ε i ↦ if ε i then 1 else -1
  have hsg (ε : ι → Bool) (i : ι) : |sg ε i| = 1 := by by_cases h : ε i <;> simp [sg, h]
  let θ : (ι → Bool) → E := fun ε ↦ ∑ i, (Δ * sg ε i) • b i
  have hθ (ε : ι → Bool) (i : ι) : ⟪b i, θ ε⟫_ℝ = Δ * sg ε i :=
    b.orthonormal.inner_right_fintype _ i
  have habs (ε : ι → Bool) (i : ι) : |⟪b i, θ ε⟫_ℝ| = Δ := by
    rw [hθ, abs_mul, abs_of_nonneg hΔ0, hsg, mul_one]
  have hθm (ε : ι → Bool) : Measurable fun p : Unit × 𝓐 ↦ ⟪θ ε, φ p.2⟫_ℝ :=
    (continuous_const.inner continuous_id).measurable.comp (hφ.comp measurable_snd)
  have hrun (ε : ι → Bool) := IT.isAlgEnvSeq_trajMeasure alg
    (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) (θ ε) σ2 (hθm ε))
  -- `f ε i`: the expected number of rounds at which the `i`-th coordinate has the wrong sign
  let f : (ι → Bool) → ι → ℝ := fun ε i ↦ ∑ t ∈ range n,
    (trajMeasure alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) (θ ε) σ2 (hθm ε))).real
      (IT.action t ⁻¹' {x | sg ε i * ⟪b i, φ x⟫_ℝ ≤ 0})
  have hR (ε : ι → Bool) : Δ * ∑ i, f ε i ≤ ∫ ω, linearRegret (fun _ ↦ φ) (θ ε) IT.obs
      IT.action n ω
        ∂(trajMeasure alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) (θ ε) σ2 (hθm ε))) :=
    mul_sum_sum_measureReal_le_integral_linearRegret (hrun ε).measurable_action hφ hΔ0 (hsg ε)
      (hθ ε) hcube (hvert _ (hsg ε)) _ n
  -- the degenerate case `σ² = 0`, where the bound is `0`
  rcases eq_or_ne σ2 0 with rfl | hσ2
  · refine ⟨θ fun _ ↦ true, habs _, fun _ ↦ ?_⟩
    refine le_of_eq_of_le (by simp) ((mul_nonneg hΔ0 (sum_nonneg fun i _ ↦
      sum_nonneg fun t _ ↦ measureReal_nonneg)).trans (hR _))
  -- flipping the sign of the coordinate `i` changes the law of the history by at most `2`
  have hpair (ε : ι → Bool) (i : ι) :
      n * exp (-2) / 2 ≤ f ε i + f (Function.update ε i (!ε i)) i := by
    have hn : (n : ℝ) * Δ ^ 2 ≤ σ2 := by
      rw [hΔ, Real.sq_sqrt (by positivity)]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact le_of_eq (by field_simp)
    refine mul_exp_neg_two_div_two_le_sum_add_sum (hrun ε) (hrun _) hσ2 hφ hcube (hsg ε i) (hθ ε)
      (hθ _) ?_ (fun j hj ↦ ?_) hn
    · by_cases h : ε i <;> simp [sg, h]
    · simp [sg, Function.update_of_ne hj]
  -- averaging over the sign patterns
  obtain ⟨ε, hε⟩ := exists_card_mul_div_two_le_sum f hpair
  refine ⟨θ ε, habs ε, fun _ ↦ ?_⟩
  have hΔn : Δ * n = √(σ2 * n) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [hΔ, show (σ2 : ℝ) * n = σ2 / n * n ^ 2 by field_simp,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg n)]
  calc exp (-2) / 4 * Fintype.card ι * √(σ2 * n)
      = Δ * (Fintype.card ι * (n * exp (-2) / 2) / 2) := by rw [← hΔn]; ring
    _ ≤ Δ * ∑ i, f ε i := by gcongr
    _ ≤ _ := hR ε

/-- **Minimax lower bound for linear bandits on the hypercube** [LS, Theorem 24.1], with the
hypercube `[-1, 1]^ι` of `EuclideanSpace ℝ ι` as the action set: for Gaussian noise of variance
`σ2` and a horizon `n`, every algorithm has, for some parameter `θ ∈ {±√(σ² / n)}^ι`, an expected
regret at least `e^{-2} d √(σ² n) / 4`, with `d` the cardinality of `ι`. -/
theorem exists_le_integral_linearRegret_gaussianLinearEnv_cube
    (alg : Algorithm Unit {x : EuclideanSpace ℝ ι // ∀ i, |x i| ≤ 1} ℝ) (σ2 : ℝ≥0) (n : ℕ) :
    ∃ θ : EuclideanSpace ℝ ι, (∀ i, |θ i| = √(σ2 / n)) ∧
      ∀ hθ : Measurable fun p : Unit × {x : EuclideanSpace ℝ ι // ∀ i, |x i| ≤ 1} ↦
          ⟪θ, (p.2 : EuclideanSpace ℝ ι)⟫_ℝ,
        exp (-2) / 4 * Fintype.card ι * √(σ2 * n) ≤
          ∫ ω, linearRegret (fun _ ↦ Subtype.val) θ IT.obs IT.action n ω
            ∂(trajMeasure alg
              (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ Subtype.val) θ σ2 hθ)) := by
  obtain ⟨θ, hθ, hR⟩ := exists_le_integral_linearRegret_gaussianLinearEnv alg
    (EuclideanSpace.basisFun ι ℝ) measurable_subtype_coe
    (fun x i ↦ by rw [EuclideanSpace.basisFun_inner]; exact x.2 i)
    (fun s hs ↦ ⟨⟨WithLp.toLp 2 s, fun i ↦ (hs i).le⟩, fun i ↦ by
      rw [EuclideanSpace.basisFun_inner]⟩) σ2 n
  exact ⟨θ, fun i ↦ by rw [← hθ i, EuclideanSpace.basisFun_inner], hR⟩

end Hypercube

end LMLExplore.Bandits
