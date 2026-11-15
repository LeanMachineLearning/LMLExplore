/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProductMeasure
public import Statlib.EValues.Numeraire
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Topology.Order.IntermediateValue
import Statlib.ForMathlib.Probability.Process.Filtration

/-!
# The numeraires of the sample sizes, as a process

Let `S₁` be a set of laws on `𝓧`, the null, and `Q₁` a law on `𝓧`, the alternative. For every
number `n + 1` of observations, the numeraire of the `(n + 1)`-sample null
`{P ^ (n + 1) | P ∈ S₁}` under `Q₁ ^ (n + 1)` is the log-optimal `(n + 1)`-sample e-variable
(Statlib's `ProbabilityTheory.IsNumeraire`). Evaluated at the first `n + 1` coordinates of a
sequence `ω : ℕ → 𝓧`, these numeraires form a process adapted to `Filtration.piLE`, whose time `n`
has seen the observations `ω 0, …, ω n`. Ramdas, Grünwald, Vovk and Shafer ask when this process
is an e-process for the i.i.d. null [RGVS23, §8.2.4]. It is not in general:

* For the null `{Ber(1/5), Ber(4/5)}` on `Bool` and the alternative `Ber(1/2)`, the numeraire of
  `n` observations is the likelihood ratio of `Ber(1/2) ^ n` against the equal mixture of
  `Ber(1/5) ^ n` and `Ber(4/5) ^ n`. The stopping time that stops after the first observation
  when it is `false` and after the second one otherwise gives the process the mean
  `367 / 340 > 1` under the i.i.d. law of `Ber(1/5)`. Half of the process is an e-process: half
  the numeraire is at most the likelihood ratio against each of the two null laws.
* For a null `{P₁, P₂}` on a finite space, with `Q₁`, `P₁` and `P₂` charging every point, the
  process is an e-process exactly when `∫⁻ x, P₂ {x} / P₁ {x} ∂Q₁ ≤ 1` or
  `∫⁻ x, P₁ {x} / P₂ {x} ∂Q₁ ≤ 1`. These are also exactly the cases in which the numeraires are
  products `∏ i, e (x i)` of copies of one function `e`, and products of copies of an e-variable
  form a test supermartingale.

A numeraire is unique only almost surely under `Q₁ ^ (n + 1)`, and when `Q₁` does not charge
every point whether the process is an e-process can depend on the version. The statements take
any family `X n` of numeraires, for instance Statlib's chosen version `numeraire`
(`isNumeraire_numeraire`). Under their hypotheses `Q₁ ^ (n + 1)` charges every point, so that all
versions agree everywhere.

## Main statements

* `ProbabilityTheory.lintegral_numeraires_bernoulli_stop_eq`: for every family of numeraires of
  the null `{Ber(1/5), Ber(4/5)}` under `Ber(1/2)`, the mean `367 / 340` at the stopping time
  above, under the i.i.d. law of `Ber(1/5)`.
* `ProbabilityTheory.not_isEProcess_numeraires_bernoulli`: these numeraires do not form an
  e-process.
* `ProbabilityTheory.isEProcess_half_numeraires_bernoulli`: half of them do.
* `ProbabilityTheory.isEProcess_numeraires_pair_iff`: for a null `{P₁, P₂}` on a finite space,
  with `Q₁`, `P₁` and `P₂` charging every point, the numeraires form an e-process exactly when
  `∫⁻ x, P₂ {x} / P₁ {x} ∂Q₁ ≤ 1` or `∫⁻ x, P₁ {x} / P₂ {x} ∂Q₁ ≤ 1`.
* `ProbabilityTheory.exists_prod_eq_numeraires_pair_iff`: under the same hypotheses, the
  numeraires are products of copies of one function exactly under the same condition.

## Implementation notes

For the null `{P₁, P₂}`, a likelihood ratio of `Q₁ ^ n` against a mixture
`w P₁ ^ n + (1 - w) P₂ ^ n` that has expectation at most `1` under `P₁ ^ n` and `P₂ ^ n` is the
numeraire. If `∫⁻ x, P₂ {x} / P₁ {x} ∂Q₁ ≤ 1`, the weight `w = 1` works for every `n`, and the
numeraires are the products of copies of the likelihood ratio of `Q₁` against `P₁`. If both
expectations exceed `1`, the intermediate value theorem, applied to the difference of the two
null expectations of the likelihood ratio, gives a weight `0 < w < 1` for which both are `1`.
The e-process property at the stopping times that stop after `k + 1` observations on one sample
and after `k + 2` otherwise, with `k + 2` the number of points of the space, then forces the
weights for `k + 1` and `k + 2` observations to give the same mixture of the first `k + 1`
observations, and a rational function whose numerator has degree at most `k + 1` to vanish at
`k + 2` distinct points, a contradiction.

## References

* [RGVS23] A. Ramdas, P. Grünwald, V. Vovk and G. Shafer, *Game-theoretic statistics and safe
  anytime-valid inference*, Statist. Sci. 38 (2023), arXiv:2210.01948, §8.2.4.
-/

public section

open MeasureTheory unitInterval
open scoped ENNReal

namespace ProbabilityTheory

/-! ### I.i.d. sequences -/

section IID

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- The first `n` coordinates of an i.i.d. sequence have the product law. -/
private lemma measurePreserving_fin (P : Measure 𝓧) [IsProbabilityMeasure P] (n : ℕ) :
    MeasurePreserving (fun (ω : ℕ → 𝓧) (i : Fin n) ↦ ω i) (Measure.infinitePi fun _ ↦ P)
      (Measure.pi fun _ : Fin n ↦ P) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← Measure.infinitePi_eq_pi]
  exact Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective

/-- For `k ≤ n + 1`, the first `k` coordinates are measurable at time `n` of
`Filtration.piLE`. -/
private lemma measurable_piLE_fin {k n : ℕ} (hk : k ≤ n + 1) :
    Measurable[Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) n] fun (ω : ℕ → 𝓧) (i : Fin k) ↦ ω i :=
  @Measurable.of_eval _ _ _ (Filtration.piLE n) _ _ fun i ↦
    Filtration.measurable_piLE_apply (by have := i.2; omega)

/-- The process of the values of functions `X n` of the first `n + 1` coordinates is adapted to
`Filtration.piLE`. -/
private lemma adapted_comp_fin {X : (n : ℕ) → (Fin (n + 1) → 𝓧) → ℝ≥0∞}
    (hX : ∀ n, Measurable (X n)) :
    Adapted (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧)) fun n ω ↦ X n fun i ↦ ω i :=
  fun n ↦ (hX n).comp (measurable_piLE_fin le_rfl)

/-- Under an i.i.d. law, the coordinate `n + 1` is independent of the first `n + 1`
coordinates. -/
private lemma indep_piLE_comap_eval_succ (μ : Measure 𝓧) [IsProbabilityMeasure μ] (n : ℕ) :
    Indep (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) n) (m𝓧.comap fun ω : ℕ → 𝓧 ↦ ω (n + 1))
      (Measure.infinitePi fun _ ↦ μ) := by
  have h := (iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ ↦ id)
    fun _ ↦ measurable_id).indepFun_finset (Finset.Iic n) {n + 1} (by simp)
    fun i ↦ measurable_pi_apply i
  have h' : (fun ω : ℕ → 𝓧 ↦ Preorder.frestrictLe n ω)
      ⟂ᵢ[Measure.infinitePi fun _ ↦ μ] fun ω ↦ ω (n + 1) := by
    exact h.comp measurable_id (measurable_pi_apply ⟨n + 1, by simp⟩)
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (IndepFun_iff_Indep _ _ _).mp h'

/-- For an event `s` determined by the first `n + 1` coordinates of an i.i.d. sequence,
`∫⁻ ω in s, f (ω (n + 1)) ∂μ^ℕ = μ^ℕ s * ∫⁻ f ∂μ`. -/
private lemma setLIntegral_comp_eval_succ (μ : Measure 𝓧) [IsProbabilityMeasure μ]
    {f : 𝓧 → ℝ≥0∞} (hf : Measurable f) (n : ℕ) {s : Set (ℕ → 𝓧)}
    (hs : MeasurableSet[Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) n] s) :
    ∫⁻ ω in s, f (ω (n + 1)) ∂(Measure.infinitePi fun _ ↦ μ) =
      (Measure.infinitePi fun _ ↦ μ) s * ∫⁻ x, f x ∂μ := by
  have hs' : MeasurableSet s := Filtration.le _ n _ hs
  have h1 : Measurable[Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) n]
      (s.indicator (1 : (ℕ → 𝓧) → ℝ≥0∞)) :=
    Measurable.indicator (m := Filtration.piLE (X := fun _ : ℕ ↦ 𝓧) n) measurable_const hs
  calc ∫⁻ ω in s, f (ω (n + 1)) ∂(Measure.infinitePi fun _ ↦ μ)
      = ∫⁻ ω, s.indicator 1 ω * f (ω (n + 1)) ∂(Measure.infinitePi fun _ ↦ μ) := by
        rw [← lintegral_indicator hs']
        congr 1 with ω
        by_cases h : ω ∈ s <;> simp [h]
    _ = (∫⁻ ω, s.indicator 1 ω ∂(Measure.infinitePi fun _ ↦ μ)) *
          ∫⁻ ω, f (ω (n + 1)) ∂(Measure.infinitePi fun _ ↦ μ) :=
        lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
          (Filtration.le _ n) (measurable_pi_apply (n + 1)).comap_le
          (indep_piLE_comap_eval_succ μ n) h1 (hf.comp (comap_measurable _))
    _ = (Measure.infinitePi fun _ ↦ μ) s * ∫⁻ x, f x ∂μ := by
        rw [lintegral_indicator_one hs',
          (measurePreserving_eval_infinitePi (fun _ ↦ μ) (n + 1)).lintegral_comp hf]

/-- **Products of copies of an e-variable.** If each `X n` is the product `∏ i, e (x i)` of
copies of an e-variable `e` for a null `S₁` of probability measures, the process
`fun n ω ↦ X n fun i ↦ ω i` is a test supermartingale for the i.i.d. null and `Filtration.piLE`,
hence an e-process. -/
private lemma isEProcess_of_eq_prod {S₁ : Set (Measure 𝓧)}
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {e : 𝓧 → ℝ≥0∞} (he : IsEVar e S₁)
    {X : (n : ℕ) → (Fin (n + 1) → 𝓧) → ℝ≥0∞} (hXe : ∀ n x, X n x = ∏ i, e (x i)) :
    IsEProcess (fun n ω ↦ X n fun i ↦ ω i) (Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
      ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁) := by
  set T := (fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' S₁
  have hT : ∀ P ∈ T, IsProbabilityMeasure P := by
    rintro _ ⟨P, hP, rfl⟩
    have := hS₁ P hP
    infer_instance
  have h0 : ∀ P ∈ T, ∫⁻ ω, e (ω 0) ∂P ≤ 1 := by
    rintro _ ⟨P, hP, rfl⟩
    have := hS₁ P hP
    rw [(measurePreserving_eval_infinitePi (fun _ ↦ P) 0).lintegral_comp he.measurable]
    exact he.lintegral_le_one hP
  have hF : ∀ k, IsCondEVar (fun ω : ℕ → 𝓧 ↦ e (ω (k + 1))) (Filtration.piLE k) T := by
    refine fun k ↦ ⟨he.measurable.comp (measurable_pi_apply _), ?_⟩
    rintro _ ⟨P, hP, rfl⟩ s hs
    have := hS₁ P hP
    rw [setLIntegral_comp_eval_succ P he.measurable k hs]
    exact mul_le_of_le_one_right' (he.lintegral_le_one hP)
  have hM := isTestSupermartingale_mul_prod (ℱ := Filtration.piLE (X := fun _ : ℕ ↦ 𝓧))
    (he.measurable.comp (Filtration.measurable_piLE_apply le_rfl)) h0
    (fun k ↦ he.measurable.comp (Filtration.measurable_piLE_apply le_rfl)) hF
  convert hM.isEProcess hT using 3 with n ω
  rw [hXe, Fin.prod_univ_eq_prod_range (fun i ↦ e (ω i)), Finset.prod_range_succ', mul_comm]
  rfl

end IID

/-! ### Numeraires on a countable space -/

/-- On a countable space where `Q` charges every point, two numeraires agree everywhere. -/
private lemma eq_of_isNumeraire {β : Type*} [MeasurableSpace β] [Countable β]
    {S : Set (Measure β)} {Q : Measure β} {X Y : β → ℝ≥0∞} (hX : IsNumeraire X S Q)
    (hY : IsNumeraire Y S Q) (hQ : ∀ x, Q {x} ≠ 0) : X = Y :=
  funext fun x ↦ ae_iff_of_countable.1 (hX.ae_unique hY) x (hQ x)

/-! ### Masses and mixtures on a finite space -/

section Finite

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
  {Q P₁ P₂ : Measure α} [IsProbabilityMeasure Q] [IsProbabilityMeasure P₁]
  [IsProbabilityMeasure P₂]

/-- The mass of a point under the `n`-fold product of `μ`, as a real number. -/
private noncomputable def piMass (μ : Measure α) {n : ℕ} (x : Fin n → α) : ℝ :=
  ∏ i, μ.real {x i}

omit [MeasurableSingletonClass α] [Fintype α] in
/-- A finite measure that charges every point gives positive real masses. -/
private lemma measureReal_singleton_pos {μ : Measure α} [IsFiniteMeasure μ]
    (hμ : ∀ x, μ {x} ≠ 0) (x : α) : 0 < μ.real {x} :=
  ENNReal.toReal_pos (hμ x) (measure_ne_top _ _)

omit [MeasurableSingletonClass α] [Fintype α] in
/-- The masses of a product of a finite measure that charges every point are positive. -/
private lemma piMass_pos {μ : Measure α} [IsFiniteMeasure μ] (hμ : ∀ x, μ {x} ≠ 0) {n : ℕ}
    (x : Fin n → α) : 0 < piMass μ x :=
  Finset.prod_pos fun _ _ ↦ measureReal_singleton_pos hμ _

omit [MeasurableSingletonClass α] [Fintype α] in
/-- The masses of a product of a measure are nonnegative. -/
private lemma piMass_nonneg (μ : Measure α) {n : ℕ} (x : Fin n → α) : 0 ≤ piMass μ x :=
  Finset.prod_nonneg fun _ _ ↦ measureReal_nonneg

omit [MeasurableSingletonClass α] [Fintype α] in
/-- The mass of a point under the product of a finite measure. -/
private lemma pi_singleton_eq_ofReal_piMass (μ : Measure α) [IsFiniteMeasure μ] {n : ℕ}
    (x : Fin n → α) : (Measure.pi fun _ : Fin n ↦ μ) {x} = ENNReal.ofReal (piMass μ x) := by
  rw [Measure.pi_singleton, piMass, ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ measureReal_nonneg]
  simp

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- A sum over the samples of size `n` of a product is a power. -/
private lemma sum_prod_eq_pow (f : α → ℝ) (n : ℕ) :
    ∑ x : Fin n → α, ∏ i, f (x i) = (∑ y, f y) ^ n := by
  classical
  rw [← Fintype.prod_sum (fun _ : Fin n ↦ f), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The real masses of a probability measure sum to `1`. -/
private lemma sum_measureReal_singleton_eq_one (μ : Measure α) [IsProbabilityMeasure μ] :
    ∑ y, μ.real {y} = 1 := by
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

/-- The masses of the product of a probability measure sum to `1`. -/
private lemma sum_piMass_eq_one (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) :
    ∑ x : Fin n → α, piMass μ x = 1 := by
  rw [show (fun x : Fin n → α ↦ piMass μ x) = fun x ↦ ∏ i, μ.real {x i} from rfl,
    sum_prod_eq_pow (fun y ↦ μ.real {y}), sum_measureReal_singleton_eq_one, one_pow]

/-- The expectation `E_Q[p₂ / p₁]`, as a real number. -/
private lemma lintegral_div_eq_ofReal (hP₁ : ∀ x, P₁ {x} ≠ 0) :
    ∫⁻ x, P₂ {x} / P₁ {x} ∂Q =
      ENNReal.ofReal (∑ y, P₂.real {y} * (Q.real {y} / P₁.real {y})) := by
  rw [lintegral_fintype, ENNReal.ofReal_sum_of_nonneg fun y _ ↦ by positivity]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [← ofReal_measureReal (μ := P₂), ← ofReal_measureReal (μ := P₁),
    ← ofReal_measureReal (μ := Q), ← ENNReal.ofReal_div_of_pos
      (measureReal_singleton_pos hP₁ y), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

omit [MeasurableSingletonClass α] [IsProbabilityMeasure Q] [IsProbabilityMeasure P₁]
  [IsProbabilityMeasure P₂] in
/-- The sum over the samples of size `n` of `p₂ⁿ qⁿ / p₁ⁿ` is the `n`-th power of
`E_Q[p₂ / p₁]`. -/
private lemma sum_piMass_mul_div (n : ℕ) :
    ∑ x : Fin n → α, piMass P₂ x * (piMass Q x / piMass P₁ x) =
      (∑ y, P₂.real {y} * (Q.real {y} / P₁.real {y})) ^ n := by
  rw [← sum_prod_eq_pow]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [piMass, piMass, piMass, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]

omit [MeasurableSingletonClass α] [Fintype α] in
/-- A product of ratios of masses, as a real number. -/
private lemma prod_div_eq_ofReal (hP₁ : ∀ x, P₁ {x} ≠ 0) {n : ℕ} (x : Fin n → α) :
    ∏ i, Q {x i} / P₁ {x i} = ENNReal.ofReal (piMass Q x / piMass P₁ x) := by
  rw [piMass, piMass, ← Finset.prod_div_distrib,
    ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ by positivity]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [ENNReal.ofReal_div_of_pos (measureReal_singleton_pos hP₁ _), ofReal_measureReal,
    ofReal_measureReal]

omit [MeasurableSingletonClass α] [Fintype α] in
/-- The mass of a sample extended by one observation. -/
private lemma piMass_snoc (μ : Measure α) {k : ℕ} (x : Fin (k + 1) → α) (y : α) :
    piMass μ (Fin.snoc (α := fun _ ↦ α) x y) = piMass μ x * μ.real {y} := by
  rw [piMass, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rfl

/-! ### Likelihood ratios against mixtures -/

/-- **The likelihood ratio against a mixture.** On a finite space, if the likelihood ratio of
`Q` against the mixture `w P₁ + (1 - w) P₂` has expectation at most `1` under `P₁` and `P₂`, it is
the numeraire for `{P₁, P₂}`: the expectation under `Q` of the ratio of an e-variable `Y` to it
is the expectation of `Y` under the mixture. The masses are given as real functions. -/
private lemma isNumeraire_ofReal_div_mix {β : Type*} [MeasurableSpace β]
    [MeasurableSingletonClass β] [Fintype β] {Q P₁ P₂ : Measure β} [IsProbabilityMeasure Q]
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {q a b : β → ℝ} (hq : ∀ x, 0 < q x)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (hQ : ∀ x, Q {x} = ENNReal.ofReal (q x))
    (hP₁ : ∀ x, P₁ {x} = ENNReal.ofReal (a x)) (hP₂ : ∀ x, P₂ {x} = ENNReal.ofReal (b x))
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hm : ∀ x, 0 < w * a x + (1 - w) * b x)
    (hE₁ : ∑ x, a x * (q x / (w * a x + (1 - w) * b x)) ≤ 1)
    (hE₂ : ∑ x, b x * (q x / (w * a x + (1 - w) * b x)) ≤ 1) :
    IsNumeraire (fun x ↦ ENNReal.ofReal (q x / (w * a x + (1 - w) * b x))) {P₁, P₂} Q := by
  set m : β → ℝ := fun x ↦ w * a x + (1 - w) * b x with hm_def
  have hS : ∀ μ ∈ ({P₁, P₂} : Set (Measure β)), IsProbabilityMeasure μ := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro μ (rfl | rfl) <;> infer_instance
  have hint : ∀ (c : β → ℝ), (∀ x, 0 ≤ c x) → ∀ (μ : Measure β),
      (∀ x, μ {x} = ENNReal.ofReal (c x)) →
      ∫⁻ x, ENNReal.ofReal (q x / m x) ∂μ = ENNReal.ofReal (∑ x, c x * (q x / m x)) := by
    intro c hc μ hμ
    rw [lintegral_fintype, ENNReal.ofReal_sum_of_nonneg fun x _ ↦
      mul_nonneg (hc x) (div_nonneg (hq x).le (hm x).le)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [hμ, ← ENNReal.ofReal_mul (div_nonneg (hq x).le (hm x).le), mul_comm]
  have hW : IsEVar (fun x ↦ ENNReal.ofReal (q x / m x)) {P₁, P₂} := by
    refine IsEVar.of_lintegral_le_one hS Measurable.of_discrete ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro μ (rfl | rfl)
    · rw [hint a ha _ hP₁]
      exact ENNReal.ofReal_le_one.2 hE₁
    · rw [hint b hb _ hP₂]
      exact ENNReal.ofReal_le_one.2 hE₂
  rw [isNumeraire_iff]
  refine ⟨hW, fun Y hY ↦ ?_⟩
  have hsupp : (fun x ↦ ENNReal.ofReal (q x / m x)).fsupport = Set.univ := by
    ext x
    simp only [Function.fsupport, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨ENNReal.ofReal_ne_top, (ENNReal.ofReal_pos.2 (div_pos (hq x) (hm x))).ne'⟩
  have hY₁ : ∫⁻ x, Y x ∂P₁ ≤ 1 := hY.lintegral_le_one (by simp)
  have hY₂ : ∫⁻ x, Y x ∂P₂ ≤ 1 := hY.lintegral_le_one (by simp)
  rw [hsupp, measure_univ, lintegral_fintype]
  calc ∑ x, Y x / ENNReal.ofReal (q x / m x) * Q {x}
      = ∑ x, (ENNReal.ofReal w * (Y x * P₁ {x}) + ENNReal.ofReal (1 - w) * (Y x * P₂ {x})) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        have hq0 : ENNReal.ofReal (q x) ≠ 0 := (ENNReal.ofReal_pos.2 (hq x)).ne'
        rw [hQ, ENNReal.ofReal_div_of_pos (hm x), div_eq_mul_inv (Y x),
          ENNReal.inv_div (Or.inr ENNReal.ofReal_ne_top) (Or.inr hq0), mul_assoc,
          ENNReal.div_mul_cancel hq0 ENNReal.ofReal_ne_top, hP₁, hP₂,
          ENNReal.ofReal_add (mul_nonneg hw0 (ha x)) (mul_nonneg (by linarith) (hb x)),
          ENNReal.ofReal_mul hw0, ENNReal.ofReal_mul (by linarith)]
        ring
    _ = ENNReal.ofReal w * ∫⁻ x, Y x ∂P₁ + ENNReal.ofReal (1 - w) * ∫⁻ x, Y x ∂P₂ := by
        rw [lintegral_fintype, lintegral_fintype, Finset.sum_add_distrib, Finset.mul_sum,
          Finset.mul_sum]
    _ ≤ ENNReal.ofReal w * 1 + ENNReal.ofReal (1 - w) * 1 := by gcongr
    _ = 1 := by
        rw [mul_one, mul_one, ← ENNReal.ofReal_add hw0 (by linarith), add_sub_cancel,
          ENNReal.ofReal_one]

/-- A numeraire of `n` observations for the i.i.d. null `{P₁, P₂}` is the likelihood ratio of
`Q ^ n` against the mixture `w P₁ ^ n + (1 - w) P₂ ^ n` as soon as this ratio has expectation at
most `1` under `P₁ ^ n` and `P₂ ^ n`. -/
private lemma eq_ofReal_div_mix (hQ : ∀ x, Q {x} ≠ 0) {n : ℕ} {X : (Fin n → α) → ℝ≥0∞}
    (hX : IsNumeraire X ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' {P₁, P₂})
      (Measure.pi fun _ ↦ Q)) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hm : ∀ x : Fin n → α, 0 < w * piMass P₁ x + (1 - w) * piMass P₂ x)
    (hE₁ : ∑ x : Fin n → α,
      piMass P₁ x * (piMass Q x / (w * piMass P₁ x + (1 - w) * piMass P₂ x)) ≤ 1)
    (hE₂ : ∑ x : Fin n → α,
      piMass P₂ x * (piMass Q x / (w * piMass P₁ x + (1 - w) * piMass P₂ x)) ≤ 1)
    (x : Fin n → α) :
    X x = ENNReal.ofReal (piMass Q x / (w * piMass P₁ x + (1 - w) * piMass P₂ x)) := by
  have hN := isNumeraire_ofReal_div_mix (Q := Measure.pi fun _ : Fin n ↦ Q)
    (P₁ := Measure.pi fun _ : Fin n ↦ P₁) (P₂ := Measure.pi fun _ : Fin n ↦ P₂)
    (piMass_pos hQ) (piMass_nonneg P₁) (piMass_nonneg P₂) (pi_singleton_eq_ofReal_piMass Q)
    (pi_singleton_eq_ofReal_piMass P₁) (pi_singleton_eq_ofReal_piMass P₂) hw0 hw1 hm hE₁ hE₂
  rw [Set.image_pair] at hX
  refine congrFun (eq_of_isNumeraire hX hN fun y ↦ ?_) x
  rw [pi_singleton_eq_ofReal_piMass]
  exact (ENNReal.ofReal_pos.2 (piMass_pos hQ y)).ne'

omit [Fintype α] [IsProbabilityMeasure P₂] in
/-- The likelihood ratio of `Q` against a law `P₁` that charges every point has expectation `1`
under `P₁`. -/
private lemma lintegral_div_eq_one [Finite α] (hP₁ : ∀ x, P₁ {x} ≠ 0) :
    ∫⁻ x, Q {x} / P₁ {x} ∂P₁ = 1 := by
  have := Fintype.ofFinite α
  rw [lintegral_fintype, Finset.sum_congr rfl fun y _ ↦
    ENNReal.div_mul_cancel (hP₁ y) (measure_ne_top _ _), sum_measure_singleton, Finset.coe_univ,
    measure_univ]

omit [Fintype α] [IsProbabilityMeasure P₂] in
/-- The likelihood ratio of `Q` against a law `P₁` that charges every point is an e-variable for
`{P₁}`. -/
private lemma isEVar_div_singleton [Finite α] (hP₁ : ∀ x, P₁ {x} ≠ 0) :
    IsEVar (fun x ↦ Q {x} / P₁ {x}) {P₁} :=
  IsEVar.of_lintegral_le_one (by simpa) Measurable.of_discrete fun _ h ↦ by
    rw [Set.mem_singleton_iff.1 h]
    exact (lintegral_div_eq_one hP₁).le

/-- **The projection weight `1`.** If `E_Q[p₂ / p₁] ≤ 1`, a numeraire of `n` observations for the
i.i.d. null `{P₁, P₂}` is the likelihood ratio of `Q ^ n` against `P₁ ^ n`. -/
private lemma eq_ofReal_div_of_le (hQ : ∀ x, Q {x} ≠ 0) (hP₁ : ∀ x, P₁ {x} ≠ 0)
    (hρ : ∑ y, P₂.real {y} * (Q.real {y} / P₁.real {y}) ≤ 1) {n : ℕ}
    {X : (Fin n → α) → ℝ≥0∞}
    (hX : IsNumeraire X ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' {P₁, P₂})
      (Measure.pi fun _ ↦ Q)) (x : Fin n → α) :
    X x = ENNReal.ofReal (piMass Q x / piMass P₁ x) := by
  have h1 : ∀ y : Fin n → α, (1 : ℝ) * piMass P₁ y + (1 - 1) * piMass P₂ y = piMass P₁ y :=
    fun y ↦ by ring
  have h := eq_ofReal_div_mix hQ hX zero_le_one le_rfl
    (fun y ↦ by rw [h1]; exact piMass_pos hP₁ y) ?_ ?_ x
  · rwa [h1] at h
  · simp_rw [h1]
    rw [Finset.sum_congr rfl fun y _ ↦ mul_div_cancel₀ _ (piMass_pos hP₁ y).ne',
      sum_piMass_eq_one]
  · simp_rw [h1]
    rw [sum_piMass_mul_div]
    exact pow_le_one₀ (Finset.sum_nonneg fun y _ ↦ by positivity) hρ

omit [Fintype α] in
/-- If `E_Q[p₂ / p₁] ≤ 1`, the likelihood ratio of `Q` against `P₁` is an e-variable for
`{P₁, P₂}`, and the numeraires of `{P₁, P₂}` are the products of its copies. -/
private lemma isEVar_div_and_eq_prod_of_le [Finite α] (hQ : ∀ x, Q {x} ≠ 0) (hP₁ : ∀ x, P₁ {x} ≠ 0)
    (h : ∫⁻ x, P₂ {x} / P₁ {x} ∂Q ≤ 1) {X : (n : ℕ) → (Fin (n + 1) → α) → ℝ≥0∞}
    (hX : ∀ n, IsNumeraire (X n) ((fun P ↦ Measure.pi fun _ : Fin (n + 1) ↦ P) '' {P₁, P₂})
      (Measure.pi fun _ ↦ Q)) :
    IsEVar (fun y ↦ Q {y} / P₁ {y}) {P₁, P₂} ∧ ∀ n x, X n x = ∏ i, Q {x i} / P₁ {x i} := by
  have := Fintype.ofFinite α
  refine ⟨?_, fun n x ↦ ?_⟩
  · refine IsEVar.of_lintegral_le_one (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro μ (rfl | rfl) <;> infer_instance) Measurable.of_discrete ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro μ (rfl | rfl)
    · exact (lintegral_div_eq_one hP₁).le
    · refine le_trans (le_of_eq ?_) h
      rw [lintegral_fintype, lintegral_fintype]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ac_rfl
  · rw [lintegral_div_eq_ofReal hP₁, ENNReal.ofReal_le_one] at h
    rw [eq_ofReal_div_of_le hQ hP₁ h (hX n) x, prod_div_eq_ofReal hP₁]

omit [MeasurableSingletonClass α] [Fintype α] [IsProbabilityMeasure P₂] in
/-- `w` times the likelihood ratio of `Q ^ n` against the mixture `w P₁ ^ n + (1 - w) P₂ ^ n` is
at most the likelihood ratio of `Q ^ n` against `P₁ ^ n`, the product of copies of the likelihood
ratio of `Q` against `P₁`. -/
private lemma mul_ofReal_div_mix_le (hP₁ : ∀ x, P₁ {x} ≠ 0) {n : ℕ} {w : ℝ} (hw0 : 0 < w)
    (hw1 : w ≤ 1) (x : Fin n → α) :
    ENNReal.ofReal w *
        ENNReal.ofReal (piMass Q x / (w * piMass P₁ x + (1 - w) * piMass P₂ x)) ≤
      ∏ i, Q {x i} / P₁ {x i} := by
  have hA := piMass_pos hP₁ x
  rw [prod_div_eq_ofReal hP₁, ← ENNReal.ofReal_mul hw0.le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hB := piMass_nonneg P₂ x
  have hq := piMass_nonneg Q x
  have hmix : 0 < w * piMass P₁ x + (1 - w) * piMass P₂ x :=
    add_pos_of_pos_of_nonneg (mul_pos hw0 hA) (mul_nonneg (by linarith) hB)
  rw [mul_div_assoc', div_le_div_iff₀ hmix hA]
  nlinarith [mul_nonneg (mul_nonneg hq (sub_nonneg.2 hw1)) hB]

/-! ### The interior projection weight -/

/-- **The interior projection weight.** If `E_Q[p₂ / p₁] > 1` and `E_Q[p₁ / p₂] > 1`, for `n ≥ 1`
observations there is a weight `0 < w < 1` for which the likelihood ratio of `Q ^ n` against
`w P₁ ^ n + (1 - w) P₂ ^ n` has expectation `1` under `P₁ ^ n` and under `P₂ ^ n`: the difference
of the two expectations is continuous in `w`, negative at `w = 1` and positive at `w = 0`. -/
private lemma exists_weight_interior (hP₁ : ∀ x, P₁ {x} ≠ 0) (hP₂ : ∀ x, P₂ {x} ≠ 0)
    (h₁ : 1 < ∑ y, P₂.real {y} * (Q.real {y} / P₁.real {y}))
    (h₂ : 1 < ∑ y, P₁.real {y} * (Q.real {y} / P₂.real {y})) {n : ℕ} (hn : n ≠ 0) :
    ∃ w : ℝ, 0 < w ∧ w < 1 ∧
      ∑ x : Fin n → α,
        piMass P₁ x * (piMass Q x / (w * piMass P₁ x + (1 - w) * piMass P₂ x)) = 1 ∧
      ∑ x : Fin n → α,
        piMass P₂ x * (piMass Q x / (w * piMass P₁ x + (1 - w) * piMass P₂ x)) = 1 := by
  have hmix : ∀ w ∈ Set.Icc (0 : ℝ) 1, ∀ x : Fin n → α,
      0 < w * piMass P₁ x + (1 - w) * piMass P₂ x := by
    rintro w ⟨h0, h1⟩ x
    rcases eq_or_lt_of_le h0 with rfl | h0'
    · simpa using piMass_pos hP₂ x
    · exact add_pos_of_pos_of_nonneg (mul_pos h0' (piMass_pos hP₁ x))
        (mul_nonneg (by linarith) (piMass_nonneg P₂ x))
  set g : ℝ → ℝ := fun w ↦ ∑ x : Fin n → α, (piMass P₁ x - piMass P₂ x) *
    (piMass Q x / (w * piMass P₁ x + (1 - w) * piMass P₂ x)) with hg
  have hcont : ContinuousOn g (Set.Icc 0 1) :=
    continuousOn_finsetSum _ fun x _ ↦ continuousOn_const.mul
      (continuousOn_const.div (by fun_prop) fun w hw ↦ (hmix w hw x).ne')
  have hg1 : g 1 = 1 - (∑ y, P₂.real {y} * (Q.real {y} / P₁.real {y})) ^ n := by
    simp only [hg, one_mul, sub_self, add_zero, sub_mul, Finset.sum_sub_distrib]
    rw [← sum_piMass_mul_div, Finset.sum_congr rfl fun x _ ↦
      mul_div_cancel₀ _ (piMass_pos hP₁ x).ne', sum_piMass_eq_one]
  have hg0 : g 0 = (∑ y, P₁.real {y} * (Q.real {y} / P₂.real {y})) ^ n - 1 := by
    simp only [hg, zero_mul, sub_zero, one_mul, zero_add, sub_mul, Finset.sum_sub_distrib]
    rw [← sum_piMass_mul_div, Finset.sum_congr rfl fun x _ ↦
      mul_div_cancel₀ _ (piMass_pos hP₂ x).ne', sum_piMass_eq_one]
  have hg1' : g 1 < 0 := by rw [hg1]; linarith [one_lt_pow₀ h₁ hn]
  have hg0' : 0 < g 0 := by rw [hg0]; linarith [one_lt_pow₀ h₂ hn]
  obtain ⟨w, ⟨hw0, hw1⟩, hgw⟩ :=
    intermediate_value_Icc' zero_le_one hcont ⟨hg1'.le, hg0'.le⟩
  have hw0' : 0 < w := lt_of_le_of_ne hw0 fun h ↦ by rw [← h] at hgw; linarith
  have hw1' : w < 1 := lt_of_le_of_ne hw1 fun h ↦ by rw [h] at hgw; linarith
  set E₁ := ∑ x : Fin n → α,
    piMass P₁ x * (piMass Q x / (w * piMass P₁ x + (1 - w) * piMass P₂ x))
  set E₂ := ∑ x : Fin n → α,
    piMass P₂ x * (piMass Q x / (w * piMass P₁ x + (1 - w) * piMass P₂ x))
  have hdiff : E₁ - E₂ = 0 := by
    rw [← hgw, hg]
    simp only [E₁, E₂, ← Finset.sum_sub_distrib, sub_mul]
  have hmean : w * E₁ + (1 - w) * E₂ = 1 := by
    simp only [E₁, E₂, Finset.mul_sum, ← Finset.sum_add_distrib]
    conv_rhs => rw [← sum_piMass_eq_one Q n]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have := hmix w ⟨hw0, hw1⟩ x
    field_simp
  exact ⟨w, hw0', hw1', by linear_combination hmean + (1 - w) * hdiff,
    by linear_combination hmean - w * hdiff⟩

/-! ### Stopping times with two values -/

omit [Fintype α] in
/-- A random time that is a function, at least `k`, of the first `k + 1` observations is a
stopping time of the data filtration. -/
private lemma isStoppingTime_comp_fin [Finite α] {k : ℕ} (T : (Fin (k + 1) → α) → ℕ)
    (hT : ∀ x, k ≤ T x) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ α))
      (fun ω ↦ (T fun i ↦ ω i : WithTop ℕ)) := by
  intro i
  by_cases hi : k ≤ i
  · exact measurable_piLE_fin (by omega) (MeasurableSet.of_discrete :
      MeasurableSet {x : Fin (k + 1) → α | (T x : WithTop ℕ) ≤ i})
  · change MeasurableSet[Filtration.piLE i]
      {ω : ℕ → α | (T (fun j ↦ ω j) : WithTop ℕ) ≤ i}
    have h : {ω : ℕ → α | (T (fun j ↦ ω j) : WithTop ℕ) ≤ i} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, Nat.cast_le, not_le]
      exact lt_of_lt_of_le (by omega) (hT _)
    rw [h]
    exact @MeasurableSet.empty _ (Filtration.piLE i)

/-- **The stopping time with two values.** Let `E` be a process whose values at times `k` and
`k + 1` are functions `F₁` and `F₂` of the first `k + 1` and `k + 2` observations, with
`E_P[F₂] = 1` under the i.i.d. law of a law `P` that charges every point. If stopping at `k` when
the first `k + 1` observations are `x₀`, and at `k + 1` otherwise, gives `E` an expectation at
most `1`, then `F₁ x₀` is at most the conditional expectation of `F₂` given `x₀`. -/
private lemma le_sum_of_lintegral_stop_le_one [DecidableEq α] {P : Measure α}
    [IsProbabilityMeasure P] (hP : ∀ x, P {x} ≠ 0) {E : ℕ → (ℕ → α) → ℝ≥0∞} {k : ℕ}
    {F₁ : (Fin (k + 1) → α) → ℝ≥0∞} {F₂ : (Fin (k + 2) → α) → ℝ≥0∞}
    (h₁ : ∀ ω, E k ω = F₁ fun i ↦ ω i) (h₂ : ∀ ω, E (k + 1) ω = F₂ fun i ↦ ω i)
    (hF₂ : ∫⁻ z, F₂ z ∂(Measure.pi fun _ : Fin (k + 2) ↦ P) = 1) (x₀ : Fin (k + 1) → α)
    (hτ : ∫⁻ ω, E (if (fun i : Fin (k + 1) ↦ ω i) = x₀ then k else k + 1) ω
      ∂(Measure.infinitePi fun _ : ℕ ↦ P) ≤ 1) :
    F₁ x₀ ≤ ∑ y, F₂ (Fin.snoc x₀ y) * P {y} := by
  set G : (Fin (k + 2) → α) → ℝ≥0∞ := fun z ↦
    if Fin.init z = x₀ then F₁ (Fin.init z) else F₂ z with hG
  have hEG : ∀ ω, E (if (fun i : Fin (k + 1) ↦ ω i) = x₀ then k else k + 1) ω =
      G fun i ↦ ω i := by
    intro ω
    have hinit : Fin.init (fun i : Fin (k + 2) ↦ ω i) = fun i : Fin (k + 1) ↦ ω i := rfl
    simp only [hG, hinit]
    split_ifs
    exacts [h₁ ω, h₂ ω]
  have hsplit : ∀ f : (Fin (k + 2) → α) → ℝ≥0∞,
      ∫⁻ z, f z ∂(Measure.pi fun _ : Fin (k + 2) ↦ P) =
        ∑ x : Fin (k + 1) → α,
          (Measure.pi fun _ : Fin (k + 1) ↦ P) {x} * ∑ y, f (Fin.snoc x y) * P {y} := by
    intro f
    rw [lintegral_fintype, ← (Fin.snocEquiv (fun _ ↦ α)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [Fin.snocEquiv_apply, Measure.pi_singleton, Measure.pi_singleton, Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring
  have hx₀ : (Measure.pi fun _ : Fin (k + 1) ↦ P) {x₀} ≠ 0 := by
    rw [Measure.pi_singleton]
    exact Finset.prod_ne_zero_iff.2 fun i _ ↦ hP _
  rw [lintegral_congr hEG, (measurePreserving_fin P (k + 2)).lintegral_comp
    Measurable.of_discrete, hsplit] at hτ
  rw [hsplit] at hF₂
  set c : (Fin (k + 1) → α) → ℝ≥0∞ := fun x ↦ ∑ y, F₂ (Fin.snoc x y) * P {y} with hc
  have hsum : ∀ x, ∑ y, G (Fin.snoc x y) * P {y} = if x = x₀ then F₁ x else c x := by
    intro x
    simp only [hG, Fin.init_snoc]
    split_ifs
    · rw [← Finset.mul_sum, sum_measure_singleton, Finset.coe_univ, measure_univ, mul_one]
    · rfl
  simp only [hsum] at hτ
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x₀), ite_eq_left rfl,
    Finset.sum_congr rfl fun x hx ↦ by rw [ite_eq_right (Finset.ne_of_mem_erase hx)]] at hτ
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x₀)] at hF₂
  set R := ∑ x ∈ Finset.univ.erase x₀, (Measure.pi fun _ : Fin (k + 1) ↦ P) {x} * c x
  have hR : R ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hF₂ ▸ le_add_self)
  rw [← hF₂, ENNReal.add_le_add_iff_right hR,
    ENNReal.mul_le_mul_iff_right hx₀ (measure_ne_top _ _)] at hτ
  exact hτ

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **The algebra of the two-valued stopping time.** For the likelihood ratios against mixtures
with weights `w` (for `k + 1` observations) and `w'` (for `k + 2` observations), at a sample
with masses `A` under `P₁ ^ (k + 1)` and `B` under `P₂ ^ (k + 1)`: if the first ratio is at most
the conditional expectation of the second under both null laws, then the mixture of `A` and `B`
with weight `w'` is at most that with weight `w`, and in case of equality the two conditional
expectations of the second ratio coincide. -/
private lemma mixture_le_and_sum_eq_zero {A B C D w' : ℝ} {p₁ p₂ q : α → ℝ} (hA : 0 < A)
    (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) (hw0 : 0 < w') (hw1 : w' < 1)
    (hp₁ : ∀ y, 0 < p₁ y) (hp₂ : ∀ y, 0 < p₂ y) (hq : ∑ y, q y = 1)
    (h₁ : C / D ≤ ∑ y, C * q y / (w' * (A * p₁ y) + (1 - w') * (B * p₂ y)) * p₁ y)
    (h₂ : C / D ≤ ∑ y, C * q y / (w' * (A * p₁ y) + (1 - w') * (B * p₂ y)) * p₂ y) :
    w' * A + (1 - w') * B ≤ D ∧ (w' * A + (1 - w') * B = D →
      ∑ y, (p₁ y - p₂ y) * q y / (w' * (A * p₁ y) + (1 - w') * (B * p₂ y)) = 0) := by
  have hden : ∀ y, 0 < w' * (A * p₁ y) + (1 - w') * (B * p₂ y) := fun y ↦
    add_pos (mul_pos hw0 (mul_pos hA (hp₁ y))) (mul_pos (by linarith) (mul_pos hB (hp₂ y)))
  set G₁ := ∑ y, q y / (w' * (A * p₁ y) + (1 - w') * (B * p₂ y)) * p₁ y
  set G₂ := ∑ y, q y / (w' * (A * p₁ y) + (1 - w') * (B * p₂ y)) * p₂ y
  have hfac : ∀ p : α → ℝ, ∑ y, C * q y / (w' * (A * p₁ y) + (1 - w') * (B * p₂ y)) * p y =
      C * ∑ y, q y / (w' * (A * p₁ y) + (1 - w') * (B * p₂ y)) * p y := fun p ↦ by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ ↦ by ring
  rw [hfac, div_le_iff₀ hD, mul_comm C, mul_assoc] at h₁ h₂
  have hG₁ : 1 ≤ D * G₁ := le_of_mul_le_mul_right (by linarith) hC
  have hG₂ : 1 ≤ D * G₂ := le_of_mul_le_mul_right (by linarith) hC
  have hid : w' * A * G₁ + (1 - w') * B * G₂ = 1 := by
    simp only [G₁, G₂, Finset.mul_sum, ← Finset.sum_add_distrib]
    conv_rhs => rw [← hq]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    calc w' * A * (q y / (w' * (A * p₁ y) + (1 - w') * (B * p₂ y)) * p₁ y) +
          (1 - w') * B * (q y / (w' * (A * p₁ y) + (1 - w') * (B * p₂ y)) * p₂ y)
        = q y / (w' * (A * p₁ y) + (1 - w') * (B * p₂ y)) *
            (w' * (A * p₁ y) + (1 - w') * (B * p₂ y)) := by ring
      _ = q y := div_mul_cancel₀ _ (hden y).ne'
  have hle : w' * A + (1 - w') * B ≤ D := by
    have h1 : w' * A ≤ w' * A * (D * G₁) := le_mul_of_one_le_right (by positivity) hG₁
    have h2 : (1 - w') * B ≤ (1 - w') * B * (D * G₂) :=
      le_mul_of_one_le_right (mul_nonneg (by linarith) hB.le) hG₂
    nlinarith
  refine ⟨hle, fun heq ↦ ?_⟩
  have h0 : w' * A * (D * G₁ - 1) + (1 - w') * B * (D * G₂ - 1) = 0 := by
    linear_combination D * hid - heq
  have hn1 : 0 ≤ w' * A * (D * G₁ - 1) := mul_nonneg (by positivity) (by linarith)
  have hn2 : 0 ≤ (1 - w') * B * (D * G₂ - 1) :=
    mul_nonneg (mul_nonneg (by linarith) hB.le) (by linarith)
  have h12 := (add_eq_zero_iff_of_nonneg hn1 hn2).1 h0
  have hG₁' : D * G₁ = 1 := by
    have hpos : w' * A ≠ 0 := (mul_pos hw0 hA).ne'
    linarith [(mul_eq_zero.1 h12.1).resolve_left hpos]
  have hG₂' : D * G₂ = 1 := by
    have hpos : (1 - w') * B ≠ 0 := (mul_pos (by linarith) hB).ne'
    linarith [(mul_eq_zero.1 h12.2).resolve_left hpos]
  have hG : G₁ = G₂ := mul_left_cancel₀ hD.ne' (hG₁'.trans hG₂'.symm)
  calc ∑ y, (p₁ y - p₂ y) * q y / (w' * (A * p₁ y) + (1 - w') * (B * p₂ y)) = G₁ - G₂ := by
        simp only [G₁, G₂, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun y _ ↦ by ring
    _ = 0 := by rw [hG, sub_self]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **A rational function with few zeros.** If `s ↦ ∑ y, c y / (p₁ y + s p₂ y)`, with positive
`p₁`, `p₂`, vanishes at as many distinct nonnegative points as the space has elements, it
vanishes at `0`: multiplied by `∏ y, (p₁ y + s p₂ y)`, it is a polynomial of degree less than the
number of elements of the space. -/
private lemma sum_div_eq_zero_of_injective {p₁ p₂ c : α → ℝ} (hp₁ : ∀ y, 0 < p₁ y)
    (hp₂ : ∀ y, 0 < p₂ y) {ι : Type*} [Fintype ι] (hι : Fintype.card α ≤ Fintype.card ι)
    {s : ι → ℝ} (hs : Function.Injective s) (hs0 : ∀ j, 0 ≤ s j)
    (h : ∀ j, ∑ y, c y / (p₁ y + s j * p₂ y) = 0) :
    ∑ y, c y / p₁ y = 0 := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card α) with hα | hα
  · rw [Fintype.card_eq_zero_iff] at hα
    simp
  set N : Polynomial ℝ := ∑ y, Polynomial.C (c y) *
    ∏ y' ∈ Finset.univ.erase y, (Polynomial.C (p₂ y') * Polynomial.X + Polynomial.C (p₁ y'))
  have heval : ∀ t : ℝ, 0 ≤ t →
      (∑ y, c y / (p₁ y + t * p₂ y)) * ∏ y, (p₁ y + t * p₂ y) = N.eval t := by
    intro t ht
    simp only [N, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    have hy : 0 < p₁ y + t * p₂ y := add_pos_of_pos_of_nonneg (hp₁ y) (by positivity [hp₂ y])
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ y), ← mul_assoc, div_mul_cancel₀ _ hy.ne']
    exact congrArg _ (Finset.prod_congr rfl fun y' _ ↦ by ring)
  have hdeg : N.natDegree < Fintype.card ι := by
    have hle : N.natDegree ≤ Fintype.card α - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun y _ ↦ ?_
      refine (Polynomial.natDegree_C_mul_le _ _).trans
        ((Polynomial.natDegree_prod_le _ _).trans ?_)
      refine (Finset.sum_le_sum fun y' _ ↦ Polynomial.natDegree_linear_le).trans ?_
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ y), Finset.card_univ,
        smul_eq_mul, mul_one]
    omega
  have hN : N = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero N hs
    (fun j ↦ by rw [← heval _ (hs0 j), h j, zero_mul]) hdeg
  have h0 := heval 0 le_rfl
  rw [hN, Polynomial.eval_zero] at h0
  simp only [zero_mul, add_zero] at h0
  exact (mul_eq_zero.1 h0).resolve_right (Finset.prod_pos fun y _ ↦ hp₁ y).ne'

/-! ### The numeraires fail at a stopping time with two values -/

/-- **The numeraires fail at a stopping time with two values.** On a finite space, for laws `P₁`,
`P₂` and an alternative `Q` that charge every point, if `E_Q[p₂ / p₁] > 1` and
`E_Q[p₁ / p₂] > 1`, the numeraires are not an e-process: the e-process property fails at a
stopping time that stops after `|α| - 1` observations on one sample and after `|α|` otherwise. -/
private lemma not_isEProcess_of_one_lt (hQ : ∀ x, Q {x} ≠ 0) (hP₁ : ∀ x, P₁ {x} ≠ 0)
    (hP₂ : ∀ x, P₂ {x} ≠ 0) (h₁ : 1 < ∑ y, P₂.real {y} * (Q.real {y} / P₁.real {y}))
    (h₂ : 1 < ∑ y, P₁.real {y} * (Q.real {y} / P₂.real {y}))
    {X : (n : ℕ) → (Fin (n + 1) → α) → ℝ≥0∞}
    (hX : ∀ n, IsNumeraire (X n) ((fun P ↦ Measure.pi fun _ : Fin (n + 1) ↦ P) '' {P₁, P₂})
      (Measure.pi fun _ ↦ Q)) :
    ¬ IsEProcess (fun n ω ↦ X n fun i ↦ ω i) (Filtration.piLE (X := fun _ : ℕ ↦ α))
      ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' {P₁, P₂}) := by
  classical
  intro hE
  set r : α → ℝ := fun y ↦ P₂.real {y} / P₁.real {y} with hr
  -- two points with different likelihood ratios
  obtain ⟨y₁, y₂, hy⟩ : ∃ y₁ y₂, r y₁ < r y₂ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y₀⟩ := nonempty_of_isProbabilityMeasure Q
    have hP₂r : ∀ y, P₂.real {y} = r y₀ * P₁.real {y} := fun y ↦ by
      have h := le_antisymm (hcon y₀ y) (hcon y y₀)
      simp only [hr] at h
      rwa [div_eq_iff (measureReal_singleton_pos hP₁ y).ne'] at h
    have hr₀ : r y₀ = 1 := by
      have h := sum_measureReal_singleton_eq_one P₂
      rw [Finset.sum_congr rfl fun y _ ↦ hP₂r y, ← Finset.mul_sum,
        sum_measureReal_singleton_eq_one, mul_one] at h
      exact h
    have h1 : ∑ y, P₂.real {y} * (Q.real {y} / P₁.real {y}) = 1 := by
      rw [← sum_measureReal_singleton_eq_one Q]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [hP₂r y, hr₀, one_mul, mul_div_cancel₀ _ (measureReal_singleton_pos hP₁ y).ne']
    linarith
  have hy₁₂ : y₁ ≠ y₂ := fun h ↦ lt_irrefl _ (h ▸ hy)
  have hcard : 1 < Fintype.card α := Fintype.one_lt_card_iff.2 ⟨y₁, y₂, hy₁₂⟩
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card α = k + 2 := ⟨Fintype.card α - 2, by omega⟩
  -- the interior weights for `k + 1` and `k + 2` observations
  obtain ⟨w, hw0, hw1, hE₁, hE₂⟩ := exists_weight_interior hP₁ hP₂ h₁ h₂ (n := k + 1) (by omega)
  obtain ⟨w', hw0', hw1', hE₁', hE₂'⟩ :=
    exists_weight_interior hP₁ hP₂ h₁ h₂ (n := k + 2) (by omega)
  have hmix : ∀ {n : ℕ} {v : ℝ}, 0 < v → v < 1 → ∀ x : Fin n → α,
      0 < v * piMass P₁ x + (1 - v) * piMass P₂ x := fun hv0 hv1 x ↦
    add_pos (mul_pos hv0 (piMass_pos hP₁ x)) (mul_pos (by linarith) (piMass_pos hP₂ x))
  have hN₁ := eq_ofReal_div_mix hQ (hX k) hw0.le hw1.le (hmix hw0 hw1) hE₁.le hE₂.le
  have hN₂ := eq_ofReal_div_mix hQ (hX (k + 1)) hw0'.le hw1'.le (hmix hw0' hw1') hE₁'.le hE₂'.le
  have hden : ∀ (x₀ : Fin (k + 1) → α) (y : α), 0 ≤ w' * (piMass P₁ x₀ * P₁.real {y}) +
      (1 - w') * (piMass P₂ x₀ * P₂.real {y}) := fun x₀ y ↦ by
    rw [← piMass_snoc, ← piMass_snoc]
    exact (hmix hw0' hw1' _).le
  -- the e-process property at the stopping times with values in `{k, k + 1}`
  have key : ∀ (P : Measure α) [IsProbabilityMeasure P], P ∈ ({P₁, P₂} : Set (Measure α)) →
      (∀ y, P {y} ≠ 0) →
      ∑ z : Fin (k + 2) → α,
        piMass P z * (piMass Q z / (w' * piMass P₁ z + (1 - w') * piMass P₂ z)) = 1 →
      ∀ x₀ : Fin (k + 1) → α,
        piMass Q x₀ / (w * piMass P₁ x₀ + (1 - w) * piMass P₂ x₀) ≤
          ∑ y, piMass Q x₀ * Q.real {y} / (w' * (piMass P₁ x₀ * P₁.real {y}) +
            (1 - w') * (piMass P₂ x₀ * P₂.real {y})) * P.real {y} := by
    intro P _ hPS hP hEP x₀
    have hτ := isStoppingTime_comp_fin (fun x ↦ if x = x₀ then k else k + 1)
      fun x ↦ by split_ifs <;> omega
    have hle := hE.lintegral_le_one hτ ⟨P, hPS, rfl⟩
    have hF₂ : ∫⁻ z, X (k + 1) z ∂(Measure.pi fun _ : Fin (k + 2) ↦ P) = 1 := by
      rw [lintegral_fintype, ← ENNReal.ofReal_one, ← hEP,
        ENNReal.ofReal_sum_of_nonneg fun z _ ↦ mul_nonneg (piMass_nonneg _ _)
          (div_nonneg (piMass_nonneg _ _) (hmix hw0' hw1' z).le)]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [hN₂, pi_singleton_eq_ofReal_piMass,
        ← ENNReal.ofReal_mul (div_nonneg (piMass_nonneg _ _) (hmix hw0' hw1' z).le), mul_comm]
    have h := le_sum_of_lintegral_stop_le_one hP (E := fun n ω ↦ X n fun i ↦ ω i)
      (fun _ ↦ rfl) (fun _ ↦ rfl) hF₂ x₀ hle
    have hy : ∀ y, X (k + 1) (Fin.snoc x₀ y) * P {y} =
        ENNReal.ofReal (piMass Q x₀ * Q.real {y} / (w' * (piMass P₁ x₀ * P₁.real {y}) +
          (1 - w') * (piMass P₂ x₀ * P₂.real {y})) * P.real {y}) := fun y ↦ by
      rw [hN₂, piMass_snoc, piMass_snoc, piMass_snoc, ← ofReal_measureReal (μ := P),
        ← ENNReal.ofReal_mul]
      exact div_nonneg (mul_nonneg (piMass_nonneg _ _) measureReal_nonneg) (hden x₀ y)
    have hnn : ∀ y, 0 ≤ piMass Q x₀ * Q.real {y} / (w' * (piMass P₁ x₀ * P₁.real {y}) +
        (1 - w') * (piMass P₂ x₀ * P₂.real {y})) * P.real {y} := fun y ↦
      mul_nonneg (div_nonneg (mul_nonneg (piMass_nonneg _ _) measureReal_nonneg) (hden x₀ y))
        measureReal_nonneg
    rwa [hN₁, Finset.sum_congr rfl fun y _ ↦ hy y,
      ← ENNReal.ofReal_sum_of_nonneg fun y _ ↦ hnn y,
      ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun y _ ↦ hnn y)] at h
  have hstep := fun x₀ ↦ mixture_le_and_sum_eq_zero (piMass_pos hP₁ x₀) (piMass_pos hP₂ x₀)
    (piMass_pos hQ x₀) (hmix hw0 hw1 x₀) hw0' hw1' (measureReal_singleton_pos hP₁)
    (measureReal_singleton_pos hP₂) (sum_measureReal_singleton_eq_one Q)
    (key P₁ (by simp) hP₁ hE₁' x₀) (key P₂ (by simp) hP₂ hE₂' x₀)
  -- the mixtures with weights `w` and `w'` coincide
  have heq : ∀ x₀ : Fin (k + 1) → α, w' * piMass P₁ x₀ + (1 - w') * piMass P₂ x₀ =
      w * piMass P₁ x₀ + (1 - w) * piMass P₂ x₀ := by
    have hsum : ∑ x₀ : Fin (k + 1) → α, ((w * piMass P₁ x₀ + (1 - w) * piMass P₂ x₀) -
        (w' * piMass P₁ x₀ + (1 - w') * piMass P₂ x₀)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        sum_piMass_eq_one, sum_piMass_eq_one]
      ring
    intro x₀
    have := (Finset.sum_eq_zero_iff_of_nonneg fun x _ ↦ sub_nonneg.2 (hstep x).1).1 hsum x₀
      (Finset.mem_univ _)
    linarith
  -- the rational function vanishes at `|α|` distinct points
  have hr₁ : 0 < r y₁ :=
    div_pos (measureReal_singleton_pos hP₂ _) (measureReal_singleton_pos hP₁ _)
  have hr₂ : 0 < r y₂ :=
    div_pos (measureReal_singleton_pos hP₂ _) (measureReal_singleton_pos hP₁ _)
  set x : Fin (k + 2) → Fin (k + 1) → α := fun j i ↦ if (i : ℕ) < j then y₁ else y₂ with hx
  have hratio : ∀ j : Fin (k + 2),
      piMass P₂ (x j) / piMass P₁ (x j) = r y₂ ^ (k + 1) * (r y₁ / r y₂) ^ (j : ℕ) := by
    intro j
    have hj := j.2
    have hfac : ∀ i : Fin (k + 1), P₂.real {x j i} / P₁.real {x j i} =
        if (i : ℕ) < j then r y₁ else r y₂ := fun i ↦ by
      simp only [hx]
      split_ifs <;> rfl
    rw [piMass, piMass, ← Finset.prod_div_distrib, Finset.prod_congr rfl fun i _ ↦ hfac i,
      Fin.prod_univ_eq_prod_range (fun i ↦ if i < (j : ℕ) then r y₁ else r y₂),
      Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have hc₁ : ((Finset.range (k + 1)).filter (· < (j : ℕ))).card = j := by
      rw [Finset.range_eq_Ico, Finset.Ico_filter_lt]
      simp [show (j : ℕ) ≤ k + 1 by omega]
    have hc₂ : ((Finset.range (k + 1)).filter (fun i ↦ ¬ i < (j : ℕ))).card = k + 1 - j := by
      simp only [not_lt]
      rw [Finset.range_eq_Ico, Finset.Ico_filter_le]
      simp
    rw [hc₁, hc₂, div_pow (r y₁) (r y₂),
      show r y₂ ^ (k + 1) = r y₂ ^ (k + 1 - j) * r y₂ ^ (j : ℕ) by
      rw [← pow_add]
      congr 1
      omega, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (pow_ne_zero _ hr₂.ne'),
      mul_comm]
  set s : Fin (k + 2) → ℝ := fun j ↦ (1 - w') * piMass P₂ (x j) / (w' * piMass P₁ (x j))
    with hs
  have hs' : ∀ j, s j = (1 - w') / w' * (r y₂ ^ (k + 1) * (r y₁ / r y₂) ^ (j : ℕ)) := fun j ↦ by
    rw [hs, ← hratio j]
    field_simp
  have hinj : Function.Injective s := by
    intro j j' hjj
    rw [hs', hs'] at hjj
    have hK : (1 - w') / w' * r y₂ ^ (k + 1) ≠ 0 := by
      have : 0 < 1 - w' := by linarith
      positivity
    have h' : (1 - w') / w' * r y₂ ^ (k + 1) * (r y₁ / r y₂) ^ (j : ℕ) =
        (1 - w') / w' * r y₂ ^ (k + 1) * (r y₁ / r y₂) ^ (j' : ℕ) := by
      rw [mul_assoc, mul_assoc]
      exact hjj
    exact Fin.ext (pow_right_injective₀ (div_pos hr₁ hr₂)
      (ne_of_lt ((div_lt_one hr₂).2 hy)) (mul_left_cancel₀ hK h'))
  have hs0 : ∀ j, 0 ≤ s j := fun j ↦ div_nonneg
    (mul_nonneg (by linarith) (piMass_nonneg _ _)) (mul_nonneg hw0'.le (piMass_nonneg _ _))
  have hroot : ∀ j, ∑ y, (P₁.real {y} - P₂.real {y}) * Q.real {y} /
      (P₁.real {y} + s j * P₂.real {y}) = 0 := by
    intro j
    have h0 := (hstep (x j)).2 (heq (x j))
    have hA := piMass_pos hP₁ (x j)
    have hwA : w' * piMass P₁ (x j) ≠ 0 := (mul_pos hw0' hA).ne'
    have hden' : ∀ y, w' * (piMass P₁ (x j) * P₁.real {y}) +
        (1 - w') * (piMass P₂ (x j) * P₂.real {y}) =
        w' * piMass P₁ (x j) * (P₁.real {y} + s j * P₂.real {y}) := fun y ↦ by
      simp only [hs]
      field_simp
    calc ∑ y, (P₁.real {y} - P₂.real {y}) * Q.real {y} / (P₁.real {y} + s j * P₂.real {y})
        = w' * piMass P₁ (x j) * ∑ y, (P₁.real {y} - P₂.real {y}) * Q.real {y} /
            (w' * (piMass P₁ (x j) * P₁.real {y}) +
              (1 - w') * (piMass P₂ (x j) * P₂.real {y})) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          rw [hden' y, mul_div_assoc', mul_div_mul_left _ _ hwA]
      _ = 0 := by rw [h0, mul_zero]
  have hzero := sum_div_eq_zero_of_injective (measureReal_singleton_pos hP₁)
    (measureReal_singleton_pos hP₂) (by rw [hk, Fintype.card_fin]) hinj hs0 hroot
  have h1 : ∑ y, (P₁.real {y} - P₂.real {y}) * Q.real {y} / P₁.real {y} =
      1 - ∑ y, P₂.real {y} * (Q.real {y} / P₁.real {y}) := by
    rw [← sum_measureReal_singleton_eq_one Q, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    have := measureReal_singleton_pos hP₁ y
    field_simp
  linarith

end Finite

/-! ### Two-point nulls on a finite space -/

section TwoPoint

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
  {Q₁ P₁ P₂ : Measure α} [IsProbabilityMeasure Q₁] [IsProbabilityMeasure P₁]
  [IsProbabilityMeasure P₂] {X : (n : ℕ) → (Fin (n + 1) → α) → ℝ≥0∞}

/-- **Two-point nulls on a finite space.** This answers the question of [RGVS23, §8.2.4] for
nulls of two laws on a finite space. Let `P₁`, `P₂` and the alternative `Q₁` charge every point,
and let `X n` be a numeraire of `n + 1` observations for the i.i.d. null `{P₁, P₂}` under
`Q₁ ^ (n + 1)` for every `n`, for instance Statlib's `numeraire`. The process of the numeraires at
the first observations, `fun n ω ↦ X n fun i ↦ ω i`, is an e-process for the i.i.d. null and
`Filtration.piLE` exactly when `E_{Q₁}[p₂ / p₁] ≤ 1` or `E_{Q₁}[p₁ / p₂] ≤ 1`. When both
expectations exceed `1`, the proof finds the failure at a stopping time that stops after
`|α| - 1` observations on one sample and after `|α|` otherwise. -/
theorem isEProcess_numeraires_pair_iff (hQ₁ : ∀ x, Q₁ {x} ≠ 0) (hP₁ : ∀ x, P₁ {x} ≠ 0)
    (hP₂ : ∀ x, P₂ {x} ≠ 0)
    (hX : ∀ n, IsNumeraire (X n) ((fun P ↦ Measure.pi fun _ : Fin (n + 1) ↦ P) '' {P₁, P₂})
      (Measure.pi fun _ ↦ Q₁)) :
    IsEProcess (fun n ω ↦ X n fun i ↦ ω i) (Filtration.piLE (X := fun _ : ℕ ↦ α))
        ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) '' {P₁, P₂}) ↔
      ∫⁻ x, P₂ {x} / P₁ {x} ∂Q₁ ≤ 1 ∨ ∫⁻ x, P₁ {x} / P₂ {x} ∂Q₁ ≤ 1 := by
  have := Fintype.ofFinite α
  have hS : ∀ P ∈ ({P₁, P₂} : Set (Measure α)), IsProbabilityMeasure P := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro P (rfl | rfl) <;> infer_instance
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hcon
    push Not at hcon
    rw [lintegral_div_eq_ofReal hP₁, ENNReal.one_lt_ofReal] at hcon
    rw [lintegral_div_eq_ofReal hP₂, ENNReal.one_lt_ofReal] at hcon
    exact not_isEProcess_of_one_lt hQ₁ hP₁ hP₂ hcon.1 hcon.2 hX h
  · rcases h with h | h
    · obtain ⟨he, hXe⟩ := isEVar_div_and_eq_prod_of_le hQ₁ hP₁ h hX
      exact isEProcess_of_eq_prod hS he hXe
    · simp_rw [Set.pair_comm P₁ P₂] at hX hS ⊢
      obtain ⟨he, hXe⟩ := isEVar_div_and_eq_prod_of_le hQ₁ hP₂ h hX
      exact isEProcess_of_eq_prod hS he hXe

/-- **The numeraires of a two-point null are products exactly when they form an e-process.** On a
finite space, let `P₁`, `P₂` and the alternative `Q₁` charge every point, and let `X n` be a
numeraire of `n + 1` observations for the i.i.d. null `{P₁, P₂}` under `Q₁ ^ (n + 1)` for every
`n`. The numeraires are products `X n x = ∏ i, e (x i)` of copies of one function `e` exactly
when `E_{Q₁}[p₂ / p₁] ≤ 1` or `E_{Q₁}[p₁ / p₂] ≤ 1`. When the condition holds, the likelihood
ratio of `Q₁` against `P₁`, or against `P₂`, is such a function. -/
theorem exists_prod_eq_numeraires_pair_iff (hQ₁ : ∀ x, Q₁ {x} ≠ 0) (hP₁ : ∀ x, P₁ {x} ≠ 0)
    (hP₂ : ∀ x, P₂ {x} ≠ 0)
    (hX : ∀ n, IsNumeraire (X n) ((fun P ↦ Measure.pi fun _ : Fin (n + 1) ↦ P) '' {P₁, P₂})
      (Measure.pi fun _ ↦ Q₁)) :
    (∃ e : α → ℝ≥0∞, ∀ n (x : Fin (n + 1) → α), X n x = ∏ i, e (x i)) ↔
      ∫⁻ x, P₂ {x} / P₁ {x} ∂Q₁ ≤ 1 ∨ ∫⁻ x, P₁ {x} / P₂ {x} ∂Q₁ ≤ 1 := by
  have := Fintype.ofFinite α
  refine ⟨fun ⟨e, hXe⟩ ↦ ?_, fun h ↦ ?_⟩
  · have hS : ∀ P ∈ ({P₁, P₂} : Set (Measure α)), IsProbabilityMeasure P := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro P (rfl | rfl) <;> infer_instance
    -- `e` is an e-variable: it is the numeraire of one observation
    have he : IsEVar e {P₁, P₂} := by
      refine IsEVar.of_lintegral_le_one hS Measurable.of_discrete fun P hP ↦ ?_
      have := hS P hP
      have h0 := ((hX 0).isEVar).lintegral_le_one (Set.mem_image_of_mem _ hP)
      rwa [lintegral_congr fun x ↦ (hXe 0 x).trans (Fin.prod_univ_one _),
        (measurePreserving_eval (fun _ : Fin 1 ↦ P) 0).lintegral_comp
          Measurable.of_discrete] at h0
    exact (isEProcess_numeraires_pair_iff hQ₁ hP₁ hP₂ hX).1 (isEProcess_of_eq_prod hS he hXe)
  · rcases h with h | h
    · exact ⟨fun y ↦ Q₁ {y} / P₁ {y}, (isEVar_div_and_eq_prod_of_le hQ₁ hP₁ h hX).2⟩
    · simp_rw [Set.pair_comm P₁ P₂] at hX
      exact ⟨fun y ↦ Q₁ {y} / P₂ {y}, (isEVar_div_and_eq_prod_of_le hQ₁ hP₂ h hX).2⟩

end TwoPoint

/-! ### The Bernoulli counterexample -/

section Bernoulli

variable {Q P₁ P₂ : Measure Bool} [IsProbabilityMeasure Q] [IsProbabilityMeasure P₁]
  [IsProbabilityMeasure P₂] {X : (n : ℕ) → (Fin (n + 1) → Bool) → ℝ≥0∞}

/-- The real masses of a Bernoulli law on `Bool`. -/
private lemma measureReal_bernoulli_singleton (p : I) (b : Bool) :
    Ber(true, false, p).real {b} = if b then (p : ℝ) else 1 - p := by
  cases b
  · exact bernoulliMeasure_real_apply_of_notMem_of_mem p (measurableSet_singleton _) (by simp)
      (by simp)
  · exact bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton _) (by simp)
      (by simp)

/-- The real masses of `Ber(1/2)`, `Ber(1/5)` and `Ber(4/5)`. -/
private lemma measureReal_bernoulli_counterexample :
    (∀ b, Ber(true, false, ⟨1 / 2, by norm_num⟩).real {b} = 1 / 2) ∧
    (∀ b, Ber(true, false, ⟨1 / 5, by norm_num⟩).real {b} =
      if b then 1 / 5 else 4 / 5) ∧
    ∀ b, Ber(true, false, ⟨4 / 5, by norm_num⟩).real {b} =
      if b then 4 / 5 else 1 / 5 := by
  refine ⟨fun b ↦ ?_, fun b ↦ ?_, fun b ↦ ?_⟩ <;>
    cases b <;> simp only [measureReal_bernoulli_singleton] <;> norm_num

/-- A point of positive real mass has nonzero mass. -/
private lemma measure_singleton_ne_zero_of_pos {μ : Measure Bool} {b : Bool}
    (h : 0 < μ.real {b}) : μ {b} ≠ 0 :=
  fun h0 ↦ by simp [measureReal_def, h0] at h

/-- **Symmetric pairs.** If a bijection `φ` fixes `q` and exchanges `a` and `b`, the ratio of `q`
to the equal mixture of `a` and `b` has the same sum against `a` and against `b`, and these sums
are `1` when `q` sums to `1`. -/
private lemma sum_mul_div_mix_half_eq_one {β : Type*} [Fintype β] {q a b : β → ℝ}
    (hm : ∀ x, 0 < 2⁻¹ * a x + (1 - 2⁻¹) * b x) (hq : ∑ x, q x = 1) (φ : β ≃ β)
    (hqφ : ∀ x, q (φ x) = q x) (haφ : ∀ x, a (φ x) = b x) (hbφ : ∀ x, b (φ x) = a x) :
    ∑ x, a x * (q x / (2⁻¹ * a x + (1 - 2⁻¹) * b x)) = 1 ∧
      ∑ x, b x * (q x / (2⁻¹ * a x + (1 - 2⁻¹) * b x)) = 1 := by
  have h2 : (1 - 2⁻¹ : ℝ) = 2⁻¹ := by norm_num
  simp only [h2] at hm ⊢
  have hmφ : ∀ x, 2⁻¹ * a (φ x) + 2⁻¹ * b (φ x) = 2⁻¹ * a x + 2⁻¹ * b x :=
    fun x ↦ by rw [haφ, hbφ, add_comm]
  have h12 : ∑ x, a x * (q x / (2⁻¹ * a x + 2⁻¹ * b x)) =
      ∑ x, b x * (q x / (2⁻¹ * a x + 2⁻¹ * b x)) := by
    rw [← φ.sum_comp]
    exact Finset.sum_congr rfl fun x _ ↦ by rw [hmφ, haφ, hqφ]
  have hsum : ∑ x, a x * (q x / (2⁻¹ * a x + 2⁻¹ * b x)) +
      ∑ x, b x * (q x / (2⁻¹ * a x + 2⁻¹ * b x)) = 2 := by
    calc _ = ∑ x, 2 * q x := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          have hne : a x + b x ≠ 0 := fun h ↦ by linarith [hm x]
          field_simp
      _ = 2 := by rw [← Finset.mul_sum, hq, mul_one]
  constructor <;> linarith

/-- For the null `{Ber(1/5), Ber(4/5)}` and the alternative `Ber(1/2)` (given by their masses), a
numeraire of `n` observations is the likelihood ratio of `Ber(1/2) ^ n` against the equal mixture
of `Ber(1/5) ^ n` and `Ber(4/5) ^ n`: the negation of every observation fixes `Ber(1/2) ^ n` and
exchanges the two null products, so that the ratio has expectation `1` under both. -/
private lemma eq_ofReal_div_mix_half (hQ : ∀ b, Q.real {b} = 1 / 2)
    (hP₁ : ∀ b, P₁.real {b} = if b then 1 / 5 else 4 / 5)
    (hP₂ : ∀ b, P₂.real {b} = if b then 4 / 5 else 1 / 5) {n : ℕ}
    {Y : (Fin n → Bool) → ℝ≥0∞}
    (hY : IsNumeraire Y ((fun P ↦ Measure.pi fun _ : Fin n ↦ P) '' {P₁, P₂})
      (Measure.pi fun _ ↦ Q)) (x : Fin n → Bool) :
    Y x = ENNReal.ofReal (piMass Q x / (2⁻¹ * piMass P₁ x + (1 - 2⁻¹) * piMass P₂ x)) := by
  have hQ0 : ∀ b, Q {b} ≠ 0 := fun b ↦ measure_singleton_ne_zero_of_pos (by rw [hQ]; norm_num)
  have hP₁0 : ∀ b, P₁ {b} ≠ 0 := fun b ↦ measure_singleton_ne_zero_of_pos (by
    rw [hP₁]; split_ifs <;> norm_num)
  set φ : Equiv.Perm (Fin n → Bool) :=
    Function.Involutive.toPerm (fun x i ↦ !x i) fun x ↦ funext fun i ↦ Bool.not_not _
  have hφ : ∀ μ ν : Measure Bool, (∀ b, μ.real {!b} = ν.real {b}) →
      ∀ x, piMass μ (φ x) = piMass ν x :=
    fun μ ν h x ↦ Finset.prod_congr rfl fun i _ ↦ h (x i)
  have hm : ∀ x : Fin n → Bool, 0 < 2⁻¹ * piMass P₁ x + (1 - 2⁻¹) * piMass P₂ x := fun x ↦ by
    have := piMass_pos hP₁0 x
    have := piMass_nonneg P₂ x
    norm_num
    positivity
  obtain ⟨hE₁, hE₂⟩ := sum_mul_div_mix_half_eq_one hm (sum_piMass_eq_one Q n) φ
    (hφ Q Q fun b ↦ by rw [hQ, hQ]) (hφ P₁ P₂ fun b ↦ by cases b <;> simp [hP₁, hP₂])
    (hφ P₂ P₁ fun b ↦ by cases b <;> simp [hP₁, hP₂])
  exact eq_ofReal_div_mix (fun b ↦ hQ0 b) hY (by norm_num) (by norm_num) hm hE₁.le hE₂.le x

/-- The numeraires of one and two observations of the counterexample: `1`, and `25 / 34` or
`25 / 16` according as the two observations are equal or not. -/
private lemma numeraire_bernoulli_zero_one (hQ : ∀ b, Q.real {b} = 1 / 2)
    (hP₁ : ∀ b, P₁.real {b} = if b then 1 / 5 else 4 / 5)
    (hP₂ : ∀ b, P₂.real {b} = if b then 4 / 5 else 1 / 5)
    (hX : ∀ n, IsNumeraire (X n) ((fun P ↦ Measure.pi fun _ : Fin (n + 1) ↦ P) '' {P₁, P₂})
      (Measure.pi fun _ ↦ Q)) (ω : ℕ → Bool) :
    X 0 (fun i ↦ ω i) = 1 ∧
      X 1 (fun i ↦ ω i) = ENNReal.ofReal (if ω 0 = ω 1 then 25 / 34 else 25 / 16) := by
  refine ⟨?_, ?_⟩
  · rw [eq_ofReal_div_mix_half hQ hP₁ hP₂ (hX 0)]
    simp only [piMass, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, hQ, hP₁, hP₂,
      Fin.val_zero]
    rcases Bool.eq_false_or_eq_true (ω 0) with h | h <;> simp only [h] <;> norm_num
  · rw [eq_ofReal_div_mix_half hQ hP₁ hP₂ (hX 1)]
    simp only [piMass, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, hQ, hP₁, hP₂]
    simp only [Fin.val_zero, Fin.succ_zero_eq_one, Fin.val_one]
    rcases Bool.eq_false_or_eq_true (ω 0) with h0 | h0 <;>
      rcases Bool.eq_false_or_eq_true (ω 1) with h1 | h1 <;> simp only [h0, h1] <;> norm_num

/-- **The numeraires of the counterexample at the stopping time.** For the null
`{Ber(1/5), Ber(4/5)}` on `Bool` and the alternative `Ber(1/2)`, let `X n` be a numeraire of
`n + 1` observations for every `n`, for instance Statlib's `numeraire`. The stopping time that
stops after the first observation when it is `false` and after the second one otherwise (with
`Filtration.piLE`, stopping after one observation is stopping at time `0`) gives the numeraires
the mean `367 / 340 > 1` under the i.i.d. law of `Ber(1/5)`. -/
theorem lintegral_numeraires_bernoulli_stop_eq
    {X : (n : ℕ) → (Fin (n + 1) → Bool) → ℝ≥0∞}
    (hX : ∀ n, IsNumeraire (X n)
      ((fun P ↦ Measure.pi fun _ : Fin (n + 1) ↦ P) ''
        {Ber(true, false, ⟨1 / 5, by norm_num⟩), Ber(true, false, ⟨4 / 5, by norm_num⟩)})
      (Measure.pi fun _ ↦ Ber(true, false, ⟨1 / 2, by norm_num⟩))) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ ↦ Bool))
        (fun ω ↦ ((if ω 0 then 1 else 0 : ℕ) : WithTop ℕ)) ∧
      ∫⁻ ω, X (if ω 0 then 1 else 0) (fun i ↦ ω i)
          ∂Measure.infinitePi (fun _ : ℕ ↦ Ber(true, false, ⟨1 / 5, by norm_num⟩)) =
        367 / 340 := by
  obtain ⟨hQ, hP₁, hP₂⟩ := measureReal_bernoulli_counterexample
  refine ⟨isStoppingTime_comp_fin (k := 0) (fun x : Fin 1 → Bool ↦ if x 0 then 1 else 0)
    fun _ ↦ Nat.zero_le _, ?_⟩
  set g : (Fin 2 → Bool) → ℝ := fun y ↦ if y 0 then (if y 0 = y 1 then 25 / 34 else 25 / 16)
    else 1 with hg
  have hg0 : ∀ y, 0 ≤ g y := fun y ↦ by simp only [hg]; split_ifs <;> norm_num
  set G : (Fin 2 → Bool) → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (g y) with hG
  have hval : ∀ ω : ℕ → Bool, X (if ω 0 then 1 else 0) (fun i ↦ ω i) = G fun i ↦ ω i := by
    intro ω
    obtain ⟨h0, h1⟩ := numeraire_bernoulli_zero_one hQ hP₁ hP₂ hX ω
    cases hω : ω 0
    · change X 0 (fun i ↦ ω i) = _
      rw [h0]
      simp [hG, hg, hω]
    · change X 1 (fun i ↦ ω i) = _
      rw [h1]
      simp [hG, hg, hω]
  rw [lintegral_congr hval, (measurePreserving_fin _ 2).lintegral_comp Measurable.of_discrete,
    lintegral_fintype, Finset.sum_congr rfl fun y _ ↦ by
      rw [hG, pi_singleton_eq_ofReal_piMass, ← ENNReal.ofReal_mul (hg0 y)],
    ← ENNReal.ofReal_sum_of_nonneg fun y _ ↦ mul_nonneg (hg0 y) (piMass_nonneg _ _),
    ← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    Fintype.sum_bool, Fintype.sum_bool]
  simp only [hg, piMass, Fin.prod_univ_two, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, hP₁]
  rw [show (367 / 340 : ℝ≥0∞) = ENNReal.ofReal (367 / 340) by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
  norm_num

/-- **The numeraires need not form an e-process**, which answers the question of
[RGVS23, §8.2.4] in the negative. For the i.i.d. null `{Ber(1/5), Ber(4/5)}` on `Bool` and the
alternative `Ber(1/2)`, the numeraires of `n + 1` observations, evaluated at the first `n + 1`
observations, do not form an e-process for `Filtration.piLE`, whatever numeraires `X n` are
chosen. -/
theorem not_isEProcess_numeraires_bernoulli {X : (n : ℕ) → (Fin (n + 1) → Bool) → ℝ≥0∞}
    (hX : ∀ n, IsNumeraire (X n)
      ((fun P ↦ Measure.pi fun _ : Fin (n + 1) ↦ P) ''
        {Ber(true, false, ⟨1 / 5, by norm_num⟩), Ber(true, false, ⟨4 / 5, by norm_num⟩)})
      (Measure.pi fun _ ↦ Ber(true, false, ⟨1 / 2, by norm_num⟩))) :
    ¬ IsEProcess (fun n ω ↦ X n fun i ↦ ω i) (Filtration.piLE (X := fun _ : ℕ ↦ Bool))
      ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) ''
        {Ber(true, false, ⟨1 / 5, by norm_num⟩), Ber(true, false, ⟨4 / 5, by norm_num⟩)}) := by
  intro h
  obtain ⟨hτ, hint⟩ := lintegral_numeraires_bernoulli_stop_eq hX
  have hle : ∫⁻ ω, X (if ω 0 then 1 else 0) (fun i ↦ ω i)
      ∂Measure.infinitePi (fun _ : ℕ ↦ Ber(true, false, ⟨1 / 5, by norm_num⟩)) ≤ 1 :=
    h.lintegral_le_one hτ ⟨_, Set.mem_insert _ _, rfl⟩
  rw [hint, ENNReal.div_le_iff (by norm_num) (by norm_num)] at hle
  norm_num at hle

/-- **Half of the numeraires form an e-process.** For the i.i.d. null `{Ber(1/5), Ber(4/5)}` on
`Bool` and the alternative `Ber(1/2)`, half of the numeraires of `n + 1` observations, evaluated
at the first `n + 1` observations, form an e-process for `Filtration.piLE`, whatever numeraires
`X n` are chosen: half the likelihood ratio against the equal mixture of the two null products is
at most the likelihood ratio against each of them, a test supermartingale under that law. -/
theorem isEProcess_half_numeraires_bernoulli {X : (n : ℕ) → (Fin (n + 1) → Bool) → ℝ≥0∞}
    (hX : ∀ n, IsNumeraire (X n)
      ((fun P ↦ Measure.pi fun _ : Fin (n + 1) ↦ P) ''
        {Ber(true, false, ⟨1 / 5, by norm_num⟩), Ber(true, false, ⟨4 / 5, by norm_num⟩)})
      (Measure.pi fun _ ↦ Ber(true, false, ⟨1 / 2, by norm_num⟩))) :
    IsEProcess (fun n ω ↦ 2⁻¹ * X n fun i ↦ ω i) (Filtration.piLE (X := fun _ : ℕ ↦ Bool))
      ((fun P ↦ Measure.infinitePi fun _ : ℕ ↦ P) ''
        {Ber(true, false, ⟨1 / 5, by norm_num⟩), Ber(true, false, ⟨4 / 5, by norm_num⟩)}) := by
  obtain ⟨hQ, hP₁, hP₂⟩ := measureReal_bernoulli_counterexample
  have hadapt : Adapted (Filtration.piLE (X := fun _ : ℕ ↦ Bool))
      fun n ω ↦ 2⁻¹ * X n fun i ↦ ω i :=
    fun n ↦ (adapted_comp_fin (fun n ↦ (hX n).measurable) n).const_mul _
  have hhalf : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  -- half of the numeraire is at most the likelihood ratio against each null law
  have key : ∀ (P : Measure Bool) [IsProbabilityMeasure P], (∀ b, P {b} ≠ 0) →
      (∀ n x, 2⁻¹ * X n x ≤ ∏ i, Ber(true, false, ⟨1 / 2, by norm_num⟩) {x i} /
        P {x i}) →
      IsEProcess (fun n ω ↦ 2⁻¹ * X n fun i ↦ ω i) (Filtration.piLE (X := fun _ : ℕ ↦ Bool))
        {Measure.infinitePi fun _ : ℕ ↦ P} := by
    intro P _ hP hle
    have hE := isEProcess_of_eq_prod (by simpa) (isEVar_div_singleton hP)
      (X := fun n x ↦ ∏ i, Ber(true, false, ⟨1 / 2, by norm_num⟩) {x i} / P {x i})
      fun _ _ ↦ rfl
    rw [Set.image_singleton] at hE
    exact hE.mono (by simp only [Set.mem_singleton_iff, forall_eq]; infer_instance) hadapt
      fun n ω ↦ hle n _
  rw [isEProcess_iff_forall_singleton]
  refine ⟨hadapt, ?_⟩
  rintro _ ⟨P, hP, rfl⟩
  have hP₁0 : ∀ b, Ber(true, false, ⟨1 / 5, by norm_num⟩) {b} ≠ 0 := fun b ↦
    measure_singleton_ne_zero_of_pos (by rw [hP₁]; split_ifs <;> norm_num)
  have hP₂0 : ∀ b, Ber(true, false, ⟨4 / 5, by norm_num⟩) {b} ≠ 0 := fun b ↦
    measure_singleton_ne_zero_of_pos (by rw [hP₂]; split_ifs <;> norm_num)
  rcases hP with rfl | rfl
  · refine key _ hP₁0 fun n x ↦ ?_
    rw [eq_ofReal_div_mix_half hQ hP₁ hP₂ (hX n), hhalf]
    exact mul_ofReal_div_mix_le hP₁0 (by norm_num) (by norm_num) x
  · refine key _ hP₂0 fun n x ↦ ?_
    rw [eq_ofReal_div_mix_half hQ hP₁ hP₂ (hX n), hhalf,
      show 2⁻¹ * piMass Ber(true, false, ⟨1 / 5, by norm_num⟩) x +
          (1 - 2⁻¹) * piMass Ber(true, false, ⟨4 / 5, by norm_num⟩) x =
        2⁻¹ * piMass Ber(true, false, ⟨4 / 5, by norm_num⟩) x +
          (1 - 2⁻¹) * piMass Ber(true, false, ⟨1 / 5, by norm_num⟩) x by ring]
    exact mul_ofReal_div_mix_le hP₂0 (by norm_num) (by norm_num) x

end Bernoulli

end ProbabilityTheory
