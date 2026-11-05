/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.LowerBound
public import LMLExplore.Identification.Task.EpsBestArm

/-!
# Lower bound on the sample complexity of `ε`-best arm identification

An algorithm for `ε`-best arm identification is `δ`-correct if on every model it stops and outputs
an `ε`-good arm, an arm `a` with `μ b ≤ μ a + ε` for every arm `b`, with probability at least
`1 - δ`. Mannor and Tsitsiklis [MT04, Theorem 1] prove that such an algorithm needs, on some
Bernoulli model with `K` arms, at least `c₁ K ε⁻² log (c₂ / δ)` samples in expectation, for
constants `c₁, c₂ > 0` and all small enough `ε` and `δ`.

We prove this bound with the change of measure of Kaufmann, Cappé and Garivier
[KCG16, Lemma 1], for arms in any exponential families. Let the arm `c` belong to an exponential
family `(ρ c, T c)` with divergence `d_c` in the mean parametrization, and let `μ` be a vector of
means of the families with a single `ε`-good arm `a`, that is `μ b + ε < μ a` for every arm `b ≠ a`.
The arm `a` stops being `ε`-good when the mean of another arm `b` is moved above `μ a + ε`, or when
the mean of `a` is moved below `μ b₀ - ε` for an arm `b₀ ≠ a`
(`LMLExplore/Identification/Task/EpsBestArm.lean`). The change of measure then bounds the expected
number of pulls of every arm from below, and Wald's identity `E_μ[τ] = ∑ a, E_μ[N_a(τ)]` gives
`(∑_{b ≠ a} d_b(μ b, μ a + ε)⁻¹ + d_a(μ a, μ b₀ - ε)⁻¹) kl(δ, 1 - δ) ≤ E_μ[τ]`.
The best choice of `b₀` is an arm with the second largest mean.

For Bernoulli arms and the model in which the arm `a` has mean `1 / 2 + ε` and every other arm has
mean `1 / 2 - ε`, with `0 < ε ≤ 1 / 8`, each of these `K` divergences is at most `48 ε²`, which
gives `E_μ[τ] ≥ K / (48 ε²) kl(δ, 1 - δ) ≥ K / (48 ε²) log (1 / (2.4 δ))`, the bound of
[MT04, Theorem 1] with the explicit constants `c₁ = 1 / 48` and `c₂ = 1 / 2.4`.

The algorithm is only required to be `δ`-correct on the vectors of means of the families
(`IdentTask.restrict`), for Bernoulli arms on the means in `(0, 1)`, so that the bounds apply to
algorithms designed for a given family.

## Main statements

In the namespace `LMLExplore.Identification.IdentTask`:

* `IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_epsBaiTask_add`: for `b ≠ a`,
  `kl(δ, 1 - δ) ≤ E_μ[N_b(τ)] d_b(μ b, μ a + ε)`.
* `IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_epsBaiTask_sub`: for `b ≠ a`,
  `kl(δ, 1 - δ) ≤ E_μ[N_a(τ)] d_a(μ a, μ b - ε)`.
* `IsDeltaCorrect.mul_klBer_le_expectedStoppingTime_epsBaiTask`: the lower bound on the sample
  complexity in terms of `kl(δ, 1 - δ)`.
* `IsDeltaCorrect.mul_ofReal_log_le_expectedStoppingTime_epsBaiTask`: the lower bound in terms of
  `log (1 / (c δ))` for `c ≥ 2.4`.
* `IsDeltaCorrect.ofReal_card_div_mul_klBer_le_expectedStoppingTime_epsBaiTask_bernoulliBandit`
  and its logarithmic form
  `IsDeltaCorrect.ofReal_card_div_mul_ofReal_log_le_expectedStoppingTime_epsBaiTask_bernoulliBandit`
  : the lower bound `K / (48 ε²) log (1 / (c δ)) ≤ E_μ[τ]` for Bernoulli arms [MT04, Theorem 1].

## References

* [KCG16] E. Kaufmann, O. Cappé and A. Garivier, *On the complexity of best-arm identification in
  multi-armed bandit models*, JMLR 17 (2016), Lemma 1.
* [MT04] S. Mannor and J. N. Tsitsiklis, *The sample complexity of exploration in the multi-armed
  bandit problem*, JMLR 5 (2004), Theorem 1.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Set

open scoped ENNReal unitInterval

namespace LMLExplore.Identification.IdentTask

variable {α 𝓨 : Type*} [Fintype α] [DecidableEq α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {m𝓨 : MeasurableSpace 𝓨} [MeasurableSpace.CountablyGenerated 𝓨]
  {ρ : α → Measure 𝓨} {T : α → 𝓨 → ℝ} {ν : (α → ℝ) → Kernel α 𝓨} [∀ μ, IsMarkovKernel (ν μ)]
  {μ : α → ℝ} {ε : ℝ} {a b : α} {A : IdentAlg Unit α 𝓨 α} {δ : ℝ}

/-- `IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_of_altCost_le` for `ε`-best arm
identification on the vectors of means of the families: if `A` is `δ`-correct with `δ ≤ 1 / 2`,
`a` is the only `ε`-good arm of `μ` and `E_μ[τ] < ∞`, then `kl(δ, 1 - δ) ≤ E_μ[N_c(τ)] x` for every
arm `c` and every `x` such that `D(μ, w, ¬a) ≤ w c x` for all nonnegative allocations `w`. -/
private lemma IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_of_altCost_le_epsBaiTask
    (hA : ((epsBaiTask ν ε).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).IsDeltaCorrect
      A δ) (hδ : δ ≤ 1 / 2) (hε : 0 ≤ ε) (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c))
    (ha : ∀ b ≠ a, μ b + ε < μ a) (h : expectedStoppingTime A (Environment.bandit (ν μ)) ≠ ∞)
    {c : α} {x : ℝ} (h_alt : ∀ w : α → ℝ, 0 ≤ w →
      ((epsBaiTask ν ε).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).altCost μ w a ≤
        ENNReal.ofReal (w c * x)) :
    klBer δ (1 - δ) ≤ (∫⁻ ω, (pullCount IT.action c
        (ENat.toNat (A.stoppingTime IT.obs IT.action IT.feedback ω)) ω : ℝ≥0∞)
          ∂(trajMeasure A.alg (Environment.bandit (ν μ)))) * ENNReal.ofReal x := by
  simpa using hA.klBer_le_lintegral_pullCount_mul_of_altCost_le_restrict hδ (by simp) hμ
    ((correct_epsBaiTask_eq_singleton_iff ν hε).2 ha) (by simpa using h) h_alt

omit [Fintype α] in
/-- **Lower bound on the number of pulls of an arm that is not `ε`-good** [MT04; KCG16, Lemma 1].
Let the arm `c` belong to an exponential family `(ρ c, T c)` with divergence `d_c`, let `μ` be a
vector of means of the families whose only `ε`-good arm is `a`, with `ε ≥ 0`, and let `A` be
`δ`-correct for `ε`-best arm identification on the vectors of means of the families, with
`δ ≤ 1 / 2` and `E_μ[τ] < ∞`. For `b ≠ a` such that `μ a + ε` is a mean of the family of `b`,
`kl(δ, 1 - δ) ≤ E_μ[N_b(τ)] d_b(μ b, μ a + ε)`. -/
theorem IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_epsBaiTask_add [Finite α]
    (hA : ((epsBaiTask ν ε).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).IsDeltaCorrect
      A δ) (hδ : δ ≤ 1 / 2) (hε : 0 ≤ ε) (hT : ∀ c x, ¬ T c =ᵐ[ρ c] fun _ ↦ x)
    (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b + ε < μ a) (hba : b ≠ a) (hb : μ a + ε ∈ (ρ b).expFamilyMeans (T b))
    (h : expectedStoppingTime A (Environment.bandit (ν μ)) ≠ ∞) :
    klBer δ (1 - δ) ≤ (∫⁻ ω, (pullCount IT.action b
        (ENat.toNat (A.stoppingTime IT.obs IT.action IT.feedback ω)) ω : ℝ≥0∞)
          ∂(trajMeasure A.alg (Environment.bandit (ν μ)))) *
        ENNReal.ofReal ((ρ b).expFamilyDiv (T b) (μ b) (μ a + ε)) := by
  have := Fintype.ofFinite α
  exact hA.klBer_le_lintegral_pullCount_mul_of_altCost_le_epsBaiTask hδ hε hμ ha h fun _ hw ↦
    altCost_epsBaiTask_restrict_le_ofReal_mul_expFamilyDiv_add ν hT hμ hν hba hb hw

omit [Fintype α] in
/-- **Lower bound on the number of pulls of the `ε`-good arm** [MT04; KCG16, Lemma 1]. Let the arm
`c` belong to an exponential family `(ρ c, T c)` with divergence `d_c`, let `μ` be a vector of
means of the families whose only `ε`-good arm is `a`, with `ε ≥ 0`, and let `A` be `δ`-correct for
`ε`-best arm identification on the vectors of means of the families, with `δ ≤ 1 / 2` and
`E_μ[τ] < ∞`. For `b ≠ a` such that `μ b - ε` is a mean of the family of `a`,
`kl(δ, 1 - δ) ≤ E_μ[N_a(τ)] d_a(μ a, μ b - ε)`. -/
theorem IsDeltaCorrect.klBer_le_lintegral_pullCount_mul_epsBaiTask_sub [Finite α]
    (hA : ((epsBaiTask ν ε).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).IsDeltaCorrect
      A δ) (hδ : δ ≤ 1 / 2) (hε : 0 ≤ ε) (hT : ∀ c x, ¬ T c =ᵐ[ρ c] fun _ ↦ x)
    (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b + ε < μ a) (hba : b ≠ a) (hb : μ b - ε ∈ (ρ a).expFamilyMeans (T a))
    (h : expectedStoppingTime A (Environment.bandit (ν μ)) ≠ ∞) :
    klBer δ (1 - δ) ≤ (∫⁻ ω, (pullCount IT.action a
        (ENat.toNat (A.stoppingTime IT.obs IT.action IT.feedback ω)) ω : ℝ≥0∞)
          ∂(trajMeasure A.alg (Environment.bandit (ν μ)))) *
        ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (μ b - ε)) := by
  have := Fintype.ofFinite α
  exact hA.klBer_le_lintegral_pullCount_mul_of_altCost_le_epsBaiTask hδ hε hμ ha h fun _ hw ↦
    altCost_epsBaiTask_restrict_le_ofReal_mul_expFamilyDiv_sub ν hT hμ hν hba hb hw

/-- **Lower bound on the sample complexity of `ε`-best arm identification** [MT04, Theorem 1;
KCG16, Lemma 1]. Let the arm `c` belong to an exponential family `(ρ c, T c)` with divergence
`d_c`, let `μ` be a vector of means of the families whose only `ε`-good arm is `a`, with `ε ≥ 0`,
and let `b₀ ≠ a`. Suppose that `μ a + ε` is a mean of the families of the arms `b ≠ a` and
`μ b₀ - ε` of the family of `a`. If `A` is `δ`-correct for `ε`-best arm identification on the
vectors of means of the families, with `δ ≤ 1 / 2`, then
`(∑_{b ≠ a} d_b(μ b, μ a + ε)⁻¹ + d_a(μ a, μ b₀ - ε)⁻¹) kl(δ, 1 - δ) ≤ E_μ[τ]`. -/
theorem IsDeltaCorrect.mul_klBer_le_expectedStoppingTime_epsBaiTask {b₀ : α}
    (hA : ((epsBaiTask ν ε).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).IsDeltaCorrect
      A δ) (hδ : δ ≤ 1 / 2) (hε : 0 ≤ ε) (hT : ∀ c x, ¬ T c =ᵐ[ρ c] fun _ ↦ x)
    (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b + ε < μ a) (hb₀ : b₀ ≠ a)
    (hab : ∀ b ≠ a, μ a + ε ∈ (ρ b).expFamilyMeans (T b))
    (hb₀a : μ b₀ - ε ∈ (ρ a).expFamilyMeans (T a)) :
    (∑ b ∈ Finset.univ.erase a,
          (ENNReal.ofReal ((ρ b).expFamilyDiv (T b) (μ b) (μ a + ε)))⁻¹ +
        (ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (μ b₀ - ε)))⁻¹) * klBer δ (1 - δ) ≤
      expectedStoppingTime A (Environment.bandit (ν μ)) := by
  rcases eq_or_ne (expectedStoppingTime A (Environment.bandit (ν μ))) ∞ with h | h
  · simp [h]
  -- Divide the lower bound on the number of pulls of each arm by its divergence, then sum over
  -- the arms with Wald's identity.
  rw [expectedStoppingTime_eq_sum_lintegral_pullCount (.of_expectedStoppingTime_ne_top h),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ a), add_mul, Finset.sum_mul]
  simp_rw [← ENNReal.div_eq_inv_mul]
  exact add_le_add (Finset.sum_le_sum fun b hb ↦ ENNReal.div_le_of_le_mul <|
      hA.klBer_le_lintegral_pullCount_mul_epsBaiTask_add hδ hε hT hμ hν ha
        (Finset.ne_of_mem_erase hb) (hab b (Finset.ne_of_mem_erase hb)) h)
    (ENNReal.div_le_of_le_mul <|
      hA.klBer_le_lintegral_pullCount_mul_epsBaiTask_sub hδ hε hT hμ hν ha hb₀ hb₀a h)

/-- **Lower bound on the sample complexity of `ε`-best arm identification in logarithmic form**
[MT04, Theorem 1; KCG16, Lemma 1]. Under the assumptions of
`mul_klBer_le_expectedStoppingTime_epsBaiTask` (except `δ ≤ 1 / 2`), for every `c ≥ 2.4`,
`(∑_{b ≠ a} d_b(μ b, μ a + ε)⁻¹ + d_a(μ a, μ b₀ - ε)⁻¹) log (1 / (c δ)) ≤ E_μ[τ]`. -/
theorem IsDeltaCorrect.mul_ofReal_log_le_expectedStoppingTime_epsBaiTask {b₀ : α}
    (hA : ((epsBaiTask ν ε).restrict {μ' | ∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)}).IsDeltaCorrect
      A δ) {c : ℝ} (hc : 2.4 ≤ c) (hε : 0 ≤ ε) (hT : ∀ c x, ¬ T c =ᵐ[ρ c] fun _ ↦ x)
    (hμ : ∀ c, μ c ∈ (ρ c).expFamilyMeans (T c))
    (hν : ∀ μ' : α → ℝ, (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (ν μ c) (ν μ' c) = ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    (ha : ∀ b ≠ a, μ b + ε < μ a) (hb₀ : b₀ ≠ a)
    (hab : ∀ b ≠ a, μ a + ε ∈ (ρ b).expFamilyMeans (T b))
    (hb₀a : μ b₀ - ε ∈ (ρ a).expFamilyMeans (T a)) :
    (∑ b ∈ Finset.univ.erase a,
          (ENNReal.ofReal ((ρ b).expFamilyDiv (T b) (μ b) (μ a + ε)))⁻¹ +
        (ENNReal.ofReal ((ρ a).expFamilyDiv (T a) (μ a) (μ b₀ - ε)))⁻¹) *
        ENNReal.ofReal (Real.log (1 / (c * δ))) ≤
      expectedStoppingTime A (Environment.bandit (ν μ)) :=
  mul_ofReal_log_le_of_mul_klBer_le hc fun hδ ↦
    hA.mul_klBer_le_expectedStoppingTime_epsBaiTask hδ hε hT hμ hν ha hb₀ hab hb₀a

/-! ### Bernoulli arms -/

/-- The binary relative entropy between Bernoulli laws of means `p` and `q` with `|p - q| ≤ 3 ε`
and `|q - 1 / 2| ≤ 2 ε`, for `ε ≤ 1 / 8`, is at most `48 ε²`, through the bound by the
`χ²`-divergence `(p - q)² / (q (1 - q))`. -/
private lemma klBerReal_le_forty_eight_mul_sq {p q : ℝ} (hp : p ∈ Icc 0 1) (hε : ε ≤ 1 / 8)
    (hpq : (p - q) ^ 2 ≤ (3 * ε) ^ 2) (hq : (q - 1 / 2) ^ 2 ≤ (2 * ε) ^ 2) (hε0 : 0 ≤ ε) :
    klBerReal p q ≤ 48 * ε ^ 2 := by
  have hq_pos : 3 / 16 ≤ q * (1 - q) := by nlinarith
  have hq' : q ∈ Ioo 0 1 := ⟨by nlinarith, by nlinarith⟩
  refine (klBerReal_le_sq_sub_div hp hq').trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- If the `K - 1` terms `f b`, `b ≠ a`, and the term `y` are all at least `1 / x`, then their sum
is at least `K / x`. -/
private lemma ofReal_card_div_le_sum_erase_add (a : α) {x : ℝ} (hx : 0 < x)
    {f : α → ℝ≥0∞} {y : ℝ≥0∞} (hf : ∀ b ∈ Finset.univ.erase a, (ENNReal.ofReal x)⁻¹ ≤ f b)
    (hy : (ENNReal.ofReal x)⁻¹ ≤ y) :
    ENNReal.ofReal (Fintype.card α / x) ≤ ∑ b ∈ Finset.univ.erase a, f b + y := by
  have h_card : ((Fintype.card α - 1 : ℕ) : ℝ≥0∞) + 1 = Fintype.card α := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel (Fintype.card_pos_iff.2 ⟨a⟩)]
  have h_sum : ((Fintype.card α - 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal x)⁻¹ ≤
      ∑ b ∈ Finset.univ.erase a, f b := by
    rw [← Finset.card_univ, ← Finset.card_erase_of_mem (Finset.mem_univ a), ← nsmul_eq_mul,
      ← Finset.sum_const]
    exact Finset.sum_le_sum hf
  calc ENNReal.ofReal (Fintype.card α / x)
      = ((Fintype.card α - 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal x)⁻¹ + (ENNReal.ofReal x)⁻¹ := by
        rw [ENNReal.ofReal_div_of_pos hx, ENNReal.ofReal_natCast, div_eq_mul_inv, ← h_card,
          add_mul, one_mul]
    _ ≤ _ := add_le_add h_sum hy

/-- **Lower bound on the sample complexity of `ε`-best arm identification for Bernoulli arms**
[MT04, Theorem 1]. Let `A` be `δ`-correct for `ε`-best arm identification on the Bernoulli bandits
with means in `(0, 1)`, with `δ ≤ 1 / 2` and `0 < ε ≤ 1 / 8`, and let `a` be an arm, among `K ≥ 2`
arms. On the Bernoulli bandit in which `a` has mean `1 / 2 + ε` and every other arm has mean
`1 / 2 - ε`, `K / (48 ε²) kl(δ, 1 - δ) ≤ E[τ]`. -/
theorem IsDeltaCorrect.ofReal_card_div_mul_klBer_le_expectedStoppingTime_epsBaiTask_bernoulliBandit
    [Nontrivial α] {A : IdentAlg Unit α ℝ α}
    (hA : ((epsBaiTask (fun μ ↦ Bandits.bernoulliBandit fun c ↦ projIcc 0 1 zero_le_one (μ c))
      ε).restrict {μ | ∀ c, μ c ∈ Ioo 0 1}).IsDeltaCorrect A δ)
    (hδ : δ ≤ 1 / 2) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (a : α) :
    ENNReal.ofReal (Fintype.card α / (48 * ε ^ 2)) * klBer δ (1 - δ) ≤
      expectedStoppingTime A (Environment.bandit (Bandits.bernoulliBandit fun c ↦
        projIcc 0 1 zero_le_one (if c = a then 1 / 2 + ε else 1 / 2 - ε))) := by
  set μ : α → ℝ := fun c ↦ if c = a then 1 / 2 + ε else 1 / 2 - ε with hμ_def
  have hμ : ∀ c, μ c ∈ Ioo 0 1 := fun c ↦ by
    simp only [hμ_def]
    split_ifs <;> constructor <;> linarith
  -- The Bernoulli laws of means in `(0, 1)` form the exponential family of `Ber(1 / 2)`.
  have hρ : Ber((1 : ℝ), 0, unitInterval.sigmoid 0).expFamilyMeans id = Ioo 0 1 :=
    expFamilyMeans_bernoulliMeasure_sigmoid 0
  have hT : ∀ (_ : α) x, ¬ id =ᵐ[Ber((1 : ℝ), 0, unitInterval.sigmoid 0)] fun _ ↦ x :=
    fun _ ↦ not_ae_eq_const_bernoulliMeasure (by
      rw [unitInterval.coe_sigmoid]
      exact ⟨Real.sigmoid_pos 0, Real.sigmoid_lt_one 0⟩)
  have hmem {x : ℝ} (hx : x ∈ Ioo 0 1) :
      x ∈ Ber((1 : ℝ), 0, unitInterval.sigmoid 0).expFamilyMeans id := hρ ▸ hx
  obtain ⟨b₀, hb₀⟩ := exists_ne a
  refine le_trans ?_ (IsDeltaCorrect.mul_klBer_le_expectedStoppingTime_epsBaiTask (a := a)
    (ρ := fun _ ↦ Ber((1 : ℝ), 0, unitInterval.sigmoid 0)) (T := fun _ ↦ id)
    (by simpa only [hρ] using hA) hδ hε.le hT (fun c ↦ hmem (hμ c))
    (fun μ' hμ' c ↦
      Bandits.klDiv_bernoulliBandit_projIcc_eq_ofReal_expFamilyDiv 0 (hμ c) (hρ ▸ hμ' c))
    (fun b hb ↦ by simp [hμ_def, hb]; linarith) hb₀
    (fun b _ ↦ hmem (by simp only [hμ_def]; constructor <;> simp <;> linarith))
    (hmem (by simp only [hμ_def]; constructor <;> simp [hb₀] <;> linarith)))
  gcongr
  -- Each of the `K` divergences is at most `48 ε²`.
  have h_inv {p q : ℝ} (hp : p ∈ Ioo 0 1) (hq : q ∈ Ioo 0 1) (hpq : (p - q) ^ 2 ≤ (3 * ε) ^ 2)
      (hq2 : (q - 1 / 2) ^ 2 ≤ (2 * ε) ^ 2) :
      (ENNReal.ofReal (48 * ε ^ 2))⁻¹ ≤
        (ENNReal.ofReal (Ber((1 : ℝ), 0, unitInterval.sigmoid 0).expFamilyDiv id p q))⁻¹ := by
    rw [expFamilyDiv_bernoulliMeasure_sigmoid 0 hp hq]
    exact ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal
      (klBerReal_le_forty_eight_mul_sq (Ioo_subset_Icc_self hp) hε' hpq hq2 hε.le))
  refine ofReal_card_div_le_sum_erase_add a (by positivity) (fun b hb ↦ h_inv (hμ b) ?_ ?_ ?_)
    (h_inv (hμ a) ?_ ?_ ?_)
  · simp only [hμ_def]
    constructor <;> simp <;> linarith
  · simp [hμ_def, Finset.ne_of_mem_erase hb]
    nlinarith
  · simp [hμ_def]
    nlinarith
  · simp only [hμ_def]
    constructor <;> simp [hb₀] <;> linarith
  · simp [hμ_def, hb₀]
    nlinarith
  · simp [hμ_def, hb₀]
    nlinarith

/-- **Lower bound on the sample complexity of `ε`-best arm identification for Bernoulli arms in
logarithmic form** [MT04, Theorem 1]. Let `A` be `δ`-correct for `ε`-best arm identification on
the Bernoulli bandits with means in `(0, 1)`, with `0 < ε ≤ 1 / 8`, and let `a` be an arm, among
`K ≥ 2` arms. On the Bernoulli bandit in which `a` has mean `1 / 2 + ε` and every other arm has
mean `1 / 2 - ε`, `K / (48 ε²) log (1 / (c δ)) ≤ E[τ]` for every `c ≥ 2.4`: the bound
`c₁ K ε⁻² log (c₂ / δ)` of Mannor and Tsitsiklis with `c₁ = 1 / 48` and `c₂ = 1 / 2.4`. -/
theorem
    IsDeltaCorrect.ofReal_card_div_mul_ofReal_log_le_expectedStoppingTime_epsBaiTask_bernoulliBandit
    [Nontrivial α] {A : IdentAlg Unit α ℝ α}
    (hA : ((epsBaiTask (fun μ ↦ Bandits.bernoulliBandit fun c ↦ projIcc 0 1 zero_le_one (μ c))
      ε).restrict {μ | ∀ c, μ c ∈ Ioo 0 1}).IsDeltaCorrect A δ)
    {c : ℝ} (hc : 2.4 ≤ c) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (a : α) :
    ENNReal.ofReal (Fintype.card α / (48 * ε ^ 2)) * ENNReal.ofReal (Real.log (1 / (c * δ))) ≤
      expectedStoppingTime A (Environment.bandit (Bandits.bernoulliBandit fun c ↦
        projIcc 0 1 zero_le_one (if c = a then 1 / 2 + ε else 1 / 2 - ε))) :=
  mul_ofReal_log_le_of_mul_klBer_le hc fun hδ ↦
    hA.ofReal_card_div_mul_klBer_le_expectedStoppingTime_epsBaiTask_bernoulliBandit hδ hε hε' a

end LMLExplore.Identification.IdentTask
