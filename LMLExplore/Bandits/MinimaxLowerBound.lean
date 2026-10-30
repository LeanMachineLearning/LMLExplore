/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.Instances
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
public import LMLExplore.InformationTheory.KullbackLeibler.Gaussian
public import LMLExplore.Probability.Kernel.Basic
public import LMLExplore.SequentialLearning.BretagnolleHuber
public import LMLExplore.SequentialLearning.DivergenceDecomposition
public import LeanMachineLearning.Online.Bandit.Regret
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace

/-!
# The minimax lower bound for stochastic bandits

Let `(κ x)_{x ∈ [b, b + h]}` be a family of reward laws with means `x` and relative entropies
`D(κ x, κ y) ≤ (x - y)² / (2σ²)`. For `k ≥ 2` arms and a horizon `n ≥ σ² (k - 1) / h²`, every
algorithm has, on some bandit `(κ (μ a))_a` with `μ ∈ [b, b + h]^k`, an expected regret at least
`√(σ² (k - 1) n) / 16` ([LS, Theorem 15.2] has the constant `1 / 27`).

The proof compares two bandits. In the first, an arm `a₁` has mean `b + Δ` and the others `b`;
some other arm `i` is played at most `n / (k - 1)` times in expectation. In the second, arm `i`
has mean `b + 2Δ`. The divergence decomposition bounds the relative entropy between the laws of
the histories by `E[T_i(n)] (2Δ)² / (2σ²) ≤ 1 / 2`, and the Bretagnolle–Huber inequality, summed
over the rounds, shows that the two expected regrets add up to at least `Δ n e^{-1/2} / 2`.

## Main statements

* `LMLExplore.Bandits.integral_pullCount_eq_sum`: `E[T_a(n)] = ∑_{t < n} P(A t = a)`.
* `LMLExplore.Bandits.le_integral_regret_add_integral_regret`: the two-bandit inequality.
* `LMLExplore.Bandits.exists_le_integral_regret_of_klDiv_le`: the minimax lower bound for a family
  of reward laws.
* `LMLExplore.Bandits.exists_sqrt_le_integral_regret_gaussianBandit`: Gaussian bandits with means
  in `[0, 1]` and variance `σ²` ([LS, Theorem 15.2] for `σ² = 1`).
* `LMLExplore.Bandits.exists_sqrt_le_integral_regret_bernoulliBandit`: Bernoulli bandits with
  means in `[1 / 4, 3 / 4]`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Theorem 15.2.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset Real Learning Bandits
open scoped ENNReal NNReal unitInterval

namespace LMLExplore.Bandits

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

section Runs

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {A : ℕ → Ω → α} {A' : ℕ → Ω' → α} {ν ν' : Kernel α ℝ}

/-- The expected number of pulls of `a` before `n` is `∑_{t < n} P(A t = a)`. -/
theorem integral_pullCount_eq_sum [DecidableEq α] (hA : ∀ t, Measurable (A t)) (a : α) (n : ℕ) :
    ∫ ω, (pullCount A a n ω : ℝ) ∂P = ∑ t ∈ range n, P.real (A t ⁻¹' {a}) := by
  have hs (t : ℕ) : MeasurableSet (A t ⁻¹' {a}) := hA t (measurableSet_singleton a)
  have h (ω : Ω) : (pullCount A a n ω : ℝ) =
      ∑ t ∈ range n, (A t ⁻¹' {a}).indicator (fun _ ↦ (1 : ℝ)) ω := by
    rw [pullCount_eq_sum]
    push_cast
    refine sum_congr rfl fun t _ ↦ ?_
    by_cases hω : A t ω = a <;> simp [hω]
  simp_rw [h]
  rw [integral_finsetSum _ fun t _ ↦ (integrable_const (1 : ℝ)).indicator (hs t)]
  exact sum_congr rfl fun t _ ↦ by rw [integral_indicator_const _ (hs t), smul_eq_mul, mul_one]

/-- The expected numbers of pulls of the arms before `n` add up to `n`. -/
private lemma sum_integral_pullCount [Fintype α] [DecidableEq α] (hA : ∀ t, Measurable (A t))
    (n : ℕ) : ∑ a, ∫ ω, (pullCount A a n ω : ℝ) ∂P = n := by
  rw [← integral_finsetSum _ fun a _ ↦ integrable_pullCount hA a n]
  simp [← Nat.cast_sum, sum_pullCount]

variable [StandardBorelSpace α]

/-- If every arm other than `a₁` has gap at least `Δ`, the expected regret is at least
`Δ (n - E[T_{a₁}(n)])`. -/
theorem mul_sub_integral_pullCount_le_integral_regret [Finite α] [DecidableEq α]
    (hA : ∀ t, Measurable (A t)) {a₁ : α} {Δ : ℝ} (hΔ : ∀ a ≠ a₁, Δ ≤ gap ν a) (n : ℕ) :
    Δ * (n - ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P) ≤ ∫ ω, regret ν A n ω ∂P := by
  have := Fintype.ofFinite α
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount hA]
  have hnn (a : α) : 0 ≤ ∫ ω, (pullCount A a n ω : ℝ) ∂P :=
    integral_nonneg fun _ ↦ Nat.cast_nonneg _
  calc Δ * (n - ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P)
      = ∑ a ∈ univ.erase a₁, Δ * ∫ ω, (pullCount A a n ω : ℝ) ∂P := by
        rw [← mul_sum, ← sum_integral_pullCount (P := P) hA n, ← add_sum_erase _ _ (mem_univ a₁)]
        ring
    _ ≤ ∑ a ∈ univ.erase a₁, gap ν a * ∫ ω, (pullCount A a n ω : ℝ) ∂P :=
        sum_le_sum fun a ha ↦ mul_le_mul_of_nonneg_right (hΔ a (ne_of_mem_erase ha)) (hnn a)
    _ ≤ ∑ a, gap ν a * ∫ ω, (pullCount A a n ω : ℝ) ∂P :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
          fun a _ _ ↦ mul_nonneg gap_nonneg (hnn a)

omit [MeasurableSingletonClass α] in
/-- If the arm `a₁` has gap at least `Δ`, the expected regret is at least `Δ E[T_{a₁}(n)]`. -/
theorem mul_integral_pullCount_le_integral_regret [Finite α] [DecidableEq α]
    (hA : ∀ t, Measurable (A t)) {a₁ : α} {Δ : ℝ} (hΔ : Δ ≤ gap ν a₁) (n : ℕ) :
    Δ * ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P ≤ ∫ ω, regret ν A n ω ∂P := by
  have := Fintype.ofFinite α
  rw [integral_regret_eq_sum_gap_mul_integral_pullCount hA]
  have hnn (a : α) : 0 ≤ ∫ ω, (pullCount A a n ω : ℝ) ∂P :=
    integral_nonneg fun _ ↦ Nat.cast_nonneg _
  calc Δ * ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P
      ≤ gap ν a₁ * ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P := mul_le_mul_of_nonneg_right hΔ (hnn a₁)
    _ ≤ ∑ a, gap ν a * ∫ ω, (pullCount A a n ω : ℝ) ∂P :=
        single_le_sum (f := fun a ↦ gap ν a * ∫ ω, (pullCount A a n ω : ℝ) ∂P)
          (fun a _ ↦ mul_nonneg gap_nonneg (hnn a)) (mem_univ a₁)

/-- **Two-bandit inequality.** Run an algorithm against two stationary bandits `ν` and `ν'`. If
in `ν` every arm other than `a₁` has gap at least `Δ ≥ 0`, and in `ν'` the arm `a₁` has gap at
least `Δ`, then the two expected regrets add up to at least `Δ n exp (-D) / 2`, where `D` is the
relative entropy between the laws of the histories of the first `n` rounds. -/
theorem le_integral_regret_add_integral_regret [Finite α] {alg : Algorithm Unit α ℝ}
    [IsMarkovKernel ν] [IsMarkovKernel ν'] {O : ℕ → Ω → Unit} {R : ℕ → Ω → ℝ}
    {O' : ℕ → Ω' → Unit} {R' : ℕ → Ω' → ℝ} (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P)
    (h' : IsAlgEnvSeq O' A' R' alg (stationaryEnv ν') P') {a₁ : α} {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hΔ : ∀ a ≠ a₁, Δ ≤ gap ν a) (hΔ' : Δ ≤ gap ν' a₁) (n : ℕ)
    (hkl : klDiv (P.map (history O A R n)) (P'.map (history O' A' R' n)) ≠ ∞) :
    Δ * n * exp (-(klDiv (P.map (history O A R n)) (P'.map (history O' A' R' n))).toReal) / 2 ≤
      ∫ ω, regret ν A n ω ∂P + ∫ ω, regret ν' A' n ω ∂P' := by
  classical
  have hbh := mul_exp_neg_klDiv_map_history_div_two_le_sum (h.measurable_history n)
    (h'.measurable_history n) (measurableSet_singleton a₁).compl hkl
  have h1 : ∑ t ∈ range n, P.real (A t ⁻¹' {a₁}ᶜ) = n - ∫ ω, (pullCount A a₁ n ω : ℝ) ∂P := by
    rw [integral_pullCount_eq_sum h.measurable_action]
    simp_rw [Set.preimage_compl,
      probReal_compl_eq_one_sub (h.measurable_action _ (measurableSet_singleton a₁))]
    simp
  have h2 : ∑ t ∈ range n, P'.real (A' t ⁻¹' {a₁}ᶜᶜ) = ∫ ω, (pullCount A' a₁ n ω : ℝ) ∂P' := by
    rw [compl_compl, integral_pullCount_eq_sum h'.measurable_action]
  rw [h1, h2] at hbh
  have hR := mul_sub_integral_pullCount_le_integral_regret (P := P) h.measurable_action hΔ n
  have hR' := mul_integral_pullCount_le_integral_regret (P := P') h'.measurable_action hΔ' n
  nlinarith [mul_le_mul_of_nonneg_left hbh hΔ0]

end Runs

omit [MeasurableSingletonClass α] in
/-- The gap of an arm is at least its difference of mean with any other arm. -/
private lemma sub_le_gap [Finite α] (ν : Kernel α ℝ) (a j : α) :
    (ν j)[id] - (ν a)[id] ≤ gap ν a := by
  rw [gap]
  exact sub_le_sub_right (le_ciSup (f := fun i ↦ (ν i)[id]) (Set.finite_range _).bddAbove j) _

variable [StandardBorelSpace α]

/-- **Minimax lower bound** for a family of reward laws [LS, Theorem 15.2]: let `κ x` have mean
`x` for `x ∈ [b, b + h]`, with `D(κ x, κ y) ≤ (x - y)² / (2σ²)` there. For `k ≥ 2` arms and
`σ² (k - 1) ≤ h² n`, every algorithm has, on some bandit with arm laws `κ (μ a)` and
`μ ∈ [b, b + h]^k`, an expected regret at least `√(σ² (k - 1) n) / 16`. -/
theorem exists_le_integral_regret_of_klDiv_le [Fintype α] (alg : Algorithm Unit α ℝ)
    (κ : ℝ → Measure ℝ) [∀ x, IsProbabilityMeasure (κ x)] {b h : ℝ} (hh : 0 ≤ h) {σ2 : ℝ≥0}
    (hmean : ∀ x ∈ Set.Icc b (b + h), (κ x)[id] = x)
    (hkl : ∀ x ∈ Set.Icc b (b + h), ∀ y ∈ Set.Icc b (b + h),
      klDiv (κ x) (κ y) ≤ ENNReal.ofReal ((x - y) ^ 2 / (2 * σ2)))
    (n : ℕ) (hk : 2 ≤ Fintype.card α) (hn : σ2 * (Fintype.card α - 1 : ℝ) ≤ h ^ 2 * n) :
    ∃ μ : α → ℝ, (∀ a, μ a ∈ Set.Icc b (b + h)) ∧
      √(σ2 * (Fintype.card α - 1) * n) / 16 ≤
        ∫ ω, regret (Kernel.ofFunOfCountable fun a ↦ κ (μ a)) IT.action n ω
          ∂(trajMeasure alg (stationaryEnv (Kernel.ofFunOfCountable fun a ↦ κ (μ a)))) := by
  classical
  set k := Fintype.card α with hk_def
  have hk1 : (1 : ℝ) ≤ k - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  -- the degenerate cases `σ² = 0` and `n = 0`, where the bound is `0`
  rcases (by positivity : (0 : ℝ) ≤ σ2 * (k - 1) * n).eq_or_lt with h0 | hpos
  · refine ⟨fun _ ↦ b, fun _ ↦ ⟨le_rfl, le_add_of_nonneg_right hh⟩, ?_⟩
    rw [← h0, Real.sqrt_zero, zero_div]
    exact integral_nonneg fun _ ↦ regret_nonneg
  have hn0 : (0 : ℝ) < n := by
    rcases (Nat.cast_nonneg n : (0 : ℝ) ≤ n).eq_or_lt with h | h
    · rw [← h, mul_zero] at hpos
      exact absurd hpos (lt_irrefl _)
    · exact h
  -- the gap `Δ`, with `Δ n = √(σ² (k - 1) n) / 2` and `2Δ ≤ h`
  set Δ := √(σ2 * (k - 1) * n) / (2 * n) with hΔ_def
  have hΔ0 : 0 < Δ := div_pos (Real.sqrt_pos.2 hpos) (by positivity)
  have hΔn : Δ * n = √(σ2 * (k - 1) * n) / 2 := by
    rw [hΔ_def]
    field_simp
  have hΔsq : Δ ^ 2 = σ2 * (k - 1) / (4 * n) := by
    rw [hΔ_def, div_pow, Real.sq_sqrt hpos.le]
    field_simp
    ring
  have hΔh : 2 * Δ ≤ h := by
    have : √(σ2 * (k - 1) * n) ≤ h * n := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ h * n)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    rw [hΔ_def, mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith
  -- the first bandit: arm `a₁` has mean `b + Δ`, the others `b`
  obtain ⟨a₁⟩ : Nonempty α := Fintype.card_pos_iff.1 (by omega)
  set μ₀ : α → ℝ := fun a ↦ if a = a₁ then b + Δ else b with hμ₀
  have hμ₀_mem (a : α) : μ₀ a ∈ Set.Icc b (b + h) := by
    simp only [hμ₀]
    split_ifs <;> constructor <;> linarith
  set ν₀ : Kernel α ℝ := Kernel.ofFunOfCountable fun a ↦ κ (μ₀ a) with hν₀
  have hmean₀ (a : α) : (ν₀ a)[id] = μ₀ a := hmean _ (hμ₀_mem a)
  set P₀ := trajMeasure alg (stationaryEnv ν₀)
  have hrun₀ := IT.isAlgEnvSeq_trajMeasure alg (stationaryEnv ν₀)
  set R₀ := ∫ ω, regret ν₀ IT.action n ω ∂P₀ with hR₀
  -- an arm `i ≠ a₁` played at most `n / (k - 1)` times in expectation
  obtain ⟨i, hi, hTi⟩ : ∃ i ∈ univ.erase a₁,
      ∫ ω, (pullCount IT.action i n ω : ℝ) ∂P₀ ≤ n / (k - 1) := by
    have hne : (univ.erase a₁).Nonempty := by
      rw [← card_pos, card_erase_of_mem (mem_univ _), card_univ, ← hk_def]
      omega
    refine exists_le_of_sum_le hne ?_
    have hconst : ∑ _a ∈ univ.erase a₁, (n : ℝ) / (k - 1) = n := by
      rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, ← hk_def, nsmul_eq_mul,
        Nat.cast_pred (by omega)]
      field_simp
    rw [hconst, ← sum_integral_pullCount (P := P₀) hrun₀.measurable_action n]
    exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
      fun a _ _ ↦ integral_nonneg fun _ ↦ Nat.cast_nonneg _
  have hia : i ≠ a₁ := ne_of_mem_erase hi
  -- the second bandit: arm `i` has mean `b + 2Δ`
  set μ₁ : α → ℝ := Function.update μ₀ i (b + 2 * Δ) with hμ₁
  have hμ₁_mem (a : α) : μ₁ a ∈ Set.Icc b (b + h) := by
    rcases eq_or_ne a i with rfl | ha
    · simp only [hμ₁, Function.update_self]
      constructor <;> linarith
    · simpa [hμ₁, Function.update_of_ne ha] using hμ₀_mem a
  set ν₁ : Kernel α ℝ := Kernel.ofFunOfCountable fun a ↦ κ (μ₁ a) with hν₁
  have hmean₁ (a : α) : (ν₁ a)[id] = μ₁ a := hmean _ (hμ₁_mem a)
  set P₁ := trajMeasure alg (stationaryEnv ν₁)
  have hrun₁ := IT.isAlgEnvSeq_trajMeasure alg (stationaryEnv ν₁)
  set R₁ := ∫ ω, regret ν₁ IT.action n ω ∂P₁ with hR₁
  -- the relative entropy between the laws of the histories is at most `1 / 2`
  have hD : klDiv (P₀.map (history IT.obs IT.action IT.feedback n))
      (P₁.map (history IT.obs IT.action IT.feedback n)) ≤ ENNReal.ofReal (1 / 2) := by
    rw [hrun₀.klDiv_map_history_eq_sum_pullCount hrun₁ n, sum_eq_single i]
    · have hk' : klDiv (ν₀ i) (ν₁ i) ≤ ENNReal.ofReal ((2 * Δ) ^ 2 / (2 * σ2)) := by
        have := hkl _ (hμ₀_mem i) _ (hμ₁_mem i)
        rwa [show μ₀ i - μ₁ i = -(2 * Δ) by simp [hμ₀, hμ₁, hia], neg_sq] at this
      have hT : ∫⁻ ω, (pullCount IT.action i n ω : ℝ≥0∞) ∂P₀ ≤ ENNReal.ofReal (n / (k - 1)) := by
        calc ∫⁻ ω, (pullCount IT.action i n ω : ℝ≥0∞) ∂P₀
            = ENNReal.ofReal (∫ ω, (pullCount IT.action i n ω : ℝ) ∂P₀) := by
              rw [ofReal_integral_eq_lintegral_ofReal
                (integrable_pullCount hrun₀.measurable_action i n)
                (ae_of_all _ fun _ ↦ Nat.cast_nonneg _)]
              simp
          _ ≤ ENNReal.ofReal (n / (k - 1)) := ENNReal.ofReal_le_ofReal hTi
      calc (∫⁻ ω, (pullCount IT.action i n ω : ℝ≥0∞) ∂P₀) * klDiv (ν₀ i) (ν₁ i)
          ≤ ENNReal.ofReal (n / (k - 1)) * ENNReal.ofReal ((2 * Δ) ^ 2 / (2 * σ2)) :=
            mul_le_mul' hT hk'
        _ = ENNReal.ofReal (n / (k - 1) * ((2 * Δ) ^ 2 / (2 * σ2))) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ = ENNReal.ofReal (1 / 2) := by
            congr 1
            have hσ : (σ2 : ℝ) ≠ 0 := by
              rintro hσ
              rw [hσ, zero_mul, zero_mul] at hpos
              exact lt_irrefl _ hpos
            rw [mul_pow, hΔsq]
            field_simp
            ring
    · intro a _ ha
      have : ν₁ a = ν₀ a := by
        change κ (μ₁ a) = κ (μ₀ a)
        rw [hμ₁, Function.update_of_ne ha]
      rw [this, klDiv_self, mul_zero]
    · exact fun h ↦ absurd (mem_univ i) h
  have hDfin := (hD.trans_lt ENNReal.ofReal_lt_top).ne
  have hDle := ENNReal.toReal_le_of_le_ofReal (by norm_num) hD
  -- the gaps
  have hgap₀ : ∀ a ≠ a₁, Δ ≤ gap ν₀ a := fun a ha ↦ by
    have := sub_le_gap ν₀ a a₁
    rw [hmean₀, hmean₀] at this
    have e : μ₀ a₁ - μ₀ a = Δ := by simp [hμ₀, ha]
    linarith
  have hgap₁ : Δ ≤ gap ν₁ a₁ := by
    have := sub_le_gap ν₁ a₁ i
    rw [hmean₁, hmean₁] at this
    have e1 : μ₁ i = b + 2 * Δ := by simp [hμ₁]
    have e2 : μ₁ a₁ = b + Δ := by simp [hμ₁, hμ₀, hia.symm]
    linarith
  -- the two regrets add up to at least `√(σ² (k - 1) n) / 8`
  have htwo := le_integral_regret_add_integral_regret hrun₀ hrun₁ hΔ0.le hgap₀ hgap₁ n hDfin
  have hexp : (1 : ℝ) / 2 ≤ exp (-(klDiv (P₀.map (history IT.obs IT.action IT.feedback n))
      (P₁.map (history IT.obs IT.action IT.feedback n))).toReal) := by
    have := add_one_le_exp (-(1 / 2 : ℝ))
    exact (by linarith : (1 : ℝ) / 2 ≤ exp (-(1 / 2))).trans (exp_le_exp.2 (by linarith))
  have hsum : √(σ2 * (k - 1) * n) / 8 ≤ R₀ + R₁ := by
    calc √(σ2 * (k - 1) * n) / 8 = Δ * n * (1 / 2) / 2 := by rw [hΔn]; ring
      _ ≤ _ := by gcongr
      _ ≤ R₀ + R₁ := htwo
  rcases le_total R₁ R₀ with hle | hle
  · exact ⟨μ₀, hμ₀_mem, (by linarith : √(σ2 * (k - 1) * n) / 16 ≤ R₀)⟩
  · exact ⟨μ₁, hμ₁_mem, (by linarith : √(σ2 * (k - 1) * n) / 16 ≤ R₁)⟩

/-- **Minimax lower bound for Gaussian bandits** ([LS, Theorem 15.2] for `σ² = 1`, with the
constant `1 / 16` instead of `1 / 27`): for `k ≥ 2` arms and `σ² (k - 1) ≤ n`, every algorithm
has, on some Gaussian bandit with means in `[0, 1]` and variance `σ²`, an expected regret at least
`√(σ² (k - 1) n) / 16`. -/
theorem exists_sqrt_le_integral_regret_gaussianBandit [Fintype α] (alg : Algorithm Unit α ℝ)
    (σ2 : ℝ≥0) (n : ℕ) (hk : 2 ≤ Fintype.card α) (hn : σ2 * (Fintype.card α - 1 : ℝ) ≤ n) :
    ∃ μ : α → ℝ, (∀ a, μ a ∈ Set.Icc 0 1) ∧
      √(σ2 * (Fintype.card α - 1) * n) / 16 ≤
        ∫ ω, regret (gaussianBandit μ σ2) IT.action n ω
          ∂(trajMeasure alg (stationaryEnv (gaussianBandit μ σ2))) := by
  rcases eq_or_ne σ2 0 with rfl | hσ
  · exact ⟨fun _ ↦ 0, fun _ ↦ ⟨le_rfl, zero_le_one⟩,
      by simpa using integral_nonneg fun _ ↦ regret_nonneg⟩
  obtain ⟨μ, hμ, hR⟩ := exists_le_integral_regret_of_klDiv_le alg (fun x ↦ gaussianReal x σ2)
    (b := 0) zero_le_one (σ2 := σ2) (fun x _ ↦ by simp)
    (fun x _ y _ ↦ (klDiv_gaussianReal_gaussianReal_same_var hσ).le) n hk (by simpa using hn)
  have hν : gaussianBandit μ σ2 = Kernel.ofFunOfCountable fun a ↦ gaussianReal (μ a) σ2 :=
    Kernel.ext fun a ↦ by rw [gaussianBandit_apply]; rfl
  refine ⟨μ, fun a ↦ by simpa using hμ a, ?_⟩
  simp only [hν]
  exact hR

/-- **Minimax lower bound for Bernoulli bandits**: for `k ≥ 2` arms and `3 (k - 1) ≤ 8 n`, every
algorithm has, on some Bernoulli bandit with means in `[1 / 4, 3 / 4]`, an expected regret at
least `√(3 (k - 1) n / 32) / 16`. On `[1 / 4, 3 / 4]`, `d(p, q) ≤ (p - q)² / (q (1 - q))`
is at most `(p - q)² / (2 σ²)` with `σ² = 3 / 32`. -/
theorem exists_sqrt_le_integral_regret_bernoulliBandit [Fintype α] (alg : Algorithm Unit α ℝ)
    (n : ℕ) (hk : 2 ≤ Fintype.card α) (hn : 3 * (Fintype.card α - 1 : ℝ) ≤ 8 * n) :
    ∃ p : α → I, (∀ a, (p a : ℝ) ∈ Set.Icc (1 / 4) (3 / 4)) ∧
      √(3 / 32 * (Fintype.card α - 1) * n) / 16 ≤
        ∫ ω, regret (bernoulliBandit p) IT.action n ω
          ∂(trajMeasure alg (stationaryEnv (bernoulliBandit p))) := by
  set κ : ℝ → Measure ℝ := fun x ↦ Ber((1 : ℝ), 0, Set.projIcc 0 1 zero_le_one x) with hκ
  have hI (x : ℝ) (hx : x ∈ Set.Icc (1 / 4 : ℝ) (1 / 4 + 1 / 2)) : x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmean : ∀ x ∈ Set.Icc (1 / 4 : ℝ) (1 / 4 + 1 / 2), (κ x)[id] = x := fun x hx ↦ by
    simp [hκ, Set.projIcc_of_mem _ (hI x hx)]
  have hkl : ∀ x ∈ Set.Icc (1 / 4 : ℝ) (1 / 4 + 1 / 2), ∀ y ∈ Set.Icc (1 / 4 : ℝ) (1 / 4 + 1 / 2),
      klDiv (κ x) (κ y) ≤ ENNReal.ofReal ((x - y) ^ 2 / (2 * ((3 / 32 : ℝ≥0) : ℝ))) := by
    intro x hx y hy
    have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    calc klDiv (κ x) (κ y) = klBer x y := (klBer_def x y).symm
      _ ≤ ENNReal.ofReal ((x - y) ^ 2 / (y * (1 - y))) := klBer_le_ofReal_sq_sub_div (hI x hx) hy'
      _ ≤ ENNReal.ofReal ((x - y) ^ 2 / (2 * ((3 / 32 : ℝ≥0) : ℝ))) := by
        refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) ?_)
        push_cast
        nlinarith [mul_nonneg (sub_nonneg.2 hy.1) (sub_nonneg.2 hy.2)]
  obtain ⟨μ, hμ, hR⟩ := exists_le_integral_regret_of_klDiv_le alg κ (b := 1 / 4) (h := 1 / 2)
    (by norm_num) (σ2 := 3 / 32) hmean hkl n hk (by push_cast; linarith)
  set p : α → I := fun a ↦ Set.projIcc 0 1 zero_le_one (μ a) with hp
  have hpμ (a : α) : (p a : ℝ) = μ a := by simp [hp, Set.projIcc_of_mem _ (hI _ (hμ a))]
  have hν : bernoulliBandit p = Kernel.ofFunOfCountable fun a ↦ κ (μ a) :=
    Kernel.ext fun a ↦ by rw [bernoulliBandit_apply]; rfl
  refine ⟨p, fun a ↦ ?_, ?_⟩
  · rw [hpμ]
    exact ⟨(hμ a).1, by linarith [(hμ a).2]⟩
  · simp only [hν]
    push_cast at hR
    exact hR

end LMLExplore.Bandits
