/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Numeraire.Sequential
public import Mathlib.Probability.Distributions.Bernoulli
import LMLExplore.Probability.Distributions.Bernoulli
import Mathlib.Logic.Equiv.Fin.Basic
import all LMLExplore.EValues.Numeraire.Sequential

/-!
# The numeraires of the sample sizes need not form an e-process: a Bernoulli counterexample

Ramdas, Grünwald, Vovk and Shafer ask whether the numeraires of the `(n + 1)`-sample nulls,
evaluated at the first `n + 1` observations, form an e-process for the i.i.d. null
[RGVS23, §8.2.4] (see `LMLExplore.EValues.Numeraire.Sequential`). They need not. For the null
`{Ber(1/5), Ber(4/5)}` on `Bool` and the alternative `Ber(1/2)`, the numeraire of `n` observations
is the likelihood ratio of `Ber(1/2) ^ n` against the equal mixture of `Ber(1/5) ^ n` and
`Ber(4/5) ^ n`: the negation of every observation fixes `Ber(1/2) ^ n` and exchanges the two null
products. The numeraires of one and two observations are `1`, and `25 / 34` or `25 / 16`
according as the two observations are equal or not. The stopping time that stops after the first
observation when it is `false` and after the second one otherwise gives the process the mean
`367 / 340 > 1` under the i.i.d. law of `Ber(1/5)`. Half of the process is an e-process: half the
numeraire is at most the likelihood ratio against each of the two null laws, whose products form
a test supermartingale under that law.

This is Theorem (1) of the research note [EVR26, Note 23]. The statements and proofs are adapted
from its formalization in `EValuesResearch/Results/SequentialNumeraire.lean` (commit `dd4072f`)
in the paper project `RemyDegenne/evalues_research`. The masses of products and the likelihood
ratios against mixtures are the private helpers of `LMLExplore.EValues.Numeraire.Sequential`,
imported with `import all`.

## Main statements

* `ProbabilityTheory.lintegral_numeraires_bernoulli_stop_eq`: for every family of numeraires of
  the null `{Ber(1/5), Ber(4/5)}` under `Ber(1/2)`, the mean `367 / 340` at the stopping time
  above, under the i.i.d. law of `Ber(1/5)`.
* `ProbabilityTheory.not_isEProcess_numeraires_bernoulli`: these numeraires do not form an
  e-process.
* `ProbabilityTheory.isEProcess_half_numeraires_bernoulli`: half of them do.

## References

* [RGVS23] A. Ramdas, P. Grünwald, V. Vovk and G. Shafer, *Game-theoretic statistics and safe
  anytime-valid inference*, Statist. Sci. 38 (2023), arXiv:2210.01948, §8.2.4.
* [EVR26] the research notes of the paper project `RemyDegenne/evalues_research`: Note 23,
  `results/23-per-sample-numeraires-not-eprocess.md`.
-/

public section

open MeasureTheory unitInterval
open scoped ENNReal

namespace ProbabilityTheory

section Bernoulli

variable {Q P₁ P₂ : Measure Bool} [IsProbabilityMeasure Q] [IsProbabilityMeasure P₁]
  [IsProbabilityMeasure P₂] {X : (n : ℕ) → (Fin (n + 1) → Bool) → ℝ≥0∞}

/-- The real masses of `Ber(1/2)`, `Ber(1/5)` and `Ber(4/5)`. -/
private lemma measureReal_bernoulli_counterexample :
    (∀ b, Ber(true, false, ⟨1 / 2, by norm_num⟩).real {b} = 1 / 2) ∧
    (∀ b, Ber(true, false, ⟨1 / 5, by norm_num⟩).real {b} =
      if b then 1 / 5 else 4 / 5) ∧
    ∀ b, Ber(true, false, ⟨4 / 5, by norm_num⟩).real {b} =
      if b then 4 / 5 else 1 / 5 := by
  refine ⟨fun b ↦ ?_, fun b ↦ ?_, fun b ↦ ?_⟩ <;>
    cases b <;> simp only [bernoulliMeasure_true_false_real_singleton] <;> norm_num

/-- A point of positive real mass has nonzero mass. -/
private lemma measure_singleton_ne_zero_of_pos {μ : Measure Bool} {b : Bool}
    (h : 0 < μ.real {b}) : μ {b} ≠ 0 :=
  fun h0 ↦ by simp [measureReal_def, h0] at h

/-- The integral of a nonnegative function of the first two observations of an i.i.d. sequence on
`Bool`, as a sum over the four samples. -/
private lemma lintegral_ofReal_comp_fin_two (P : Measure Bool) [IsProbabilityMeasure P]
    {g : (Fin 2 → Bool) → ℝ} (hg : ∀ y, 0 ≤ g y) :
    ∫⁻ ω : ℕ → Bool, ENNReal.ofReal (g fun i ↦ ω i) ∂(Measure.infinitePi fun _ ↦ P) =
      ENNReal.ofReal (∑ b₀, ∑ b₁, g ![b₀, b₁] * (P.real {b₀} * P.real {b₁})) := by
  have hnn : ∀ b₀ b₁, 0 ≤ g ![b₀, b₁] * (P.real {b₀} * P.real {b₁}) := fun _ _ ↦
    mul_nonneg (hg _) (mul_nonneg measureReal_nonneg measureReal_nonneg)
  rw [lintegral_comp_initSeg_infinitePi P (f := fun y ↦ ENNReal.ofReal (g y))
    Measurable.of_discrete, lintegral_fintype, ← (finTwoArrowEquiv Bool).symm.sum_comp,
    Fintype.sum_prod_type,
    ENNReal.ofReal_sum_of_nonneg fun b₀ _ ↦ Finset.sum_nonneg fun b₁ _ ↦ hnn b₀ b₁]
  refine Finset.sum_congr rfl fun b₀ _ ↦ ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun b₁ _ ↦ hnn b₀ b₁]
  refine Finset.sum_congr rfl fun b₁ _ ↦ ?_
  rw [pi_singleton_eq_ofReal_piMass, ← ENNReal.ofReal_mul (hg _)]
  simp [piMass, Fin.prod_univ_two]

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
the mean `367 / 340 > 1` under the i.i.d. law of `Ber(1/5)` [EVR26, Note 23, Theorem (1)]. -/
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
  have hτ := Filtration.isStoppingTime_piLE_comp_initSeg (𝓧 := Bool) (k := 0)
    (T := fun x ↦ if x 0 then 1 else 0) Measurable.of_discrete fun _ ↦ Nat.zero_le _
  simp only [initSeg_def] at hτ
  refine ⟨hτ, ?_⟩
  set g : (Fin 2 → Bool) → ℝ := fun y ↦ if y 0 then (if y 0 = y 1 then 25 / 34 else 25 / 16)
    else 1 with hg
  have hg0 : ∀ y, 0 ≤ g y := fun y ↦ by simp only [hg]; split_ifs <;> norm_num
  have hval : ∀ ω : ℕ → Bool,
      X (if ω 0 then 1 else 0) (fun i ↦ ω i) = ENNReal.ofReal (g fun i ↦ ω i) := by
    intro ω
    obtain ⟨h0, h1⟩ := numeraire_bernoulli_zero_one hQ hP₁ hP₂ hX ω
    -- the number of observations is an index of the family `X`, so it is generalized first
    generalize hn : (if ω 0 then 1 else 0) = n
    cases hω : ω 0 <;> simp only [hω, Bool.false_eq_true, ↓reduceIte] at hn <;> subst hn
    · rw [h0]
      simp [hg, hω]
    · rw [h1]
      simp [hg, hω]
  rw [lintegral_congr hval, lintegral_ofReal_comp_fin_two _ hg0,
    show (367 / 340 : ℝ≥0∞) = ENNReal.ofReal (367 / 340) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
  congr 1
  simp only [hg, Fintype.sum_bool, hP₁]
  norm_num

/-- **The numeraires need not form an e-process**, which answers the question of
[RGVS23, §8.2.4] in the negative. For the i.i.d. null `{Ber(1/5), Ber(4/5)}` on `Bool` and the
alternative `Ber(1/2)`, the numeraires of `n + 1` observations, evaluated at the first `n + 1`
observations, do not form an e-process for `Filtration.piLE`, whatever numeraires `X n` are
chosen [EVR26, Note 23, Theorem (1)]. -/
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
`X n` are chosen [EVR26, Note 23, Theorem (1)]. -/
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
    fun n ↦ by
      simpa only [initSeg_def] using
        (Filtration.adapted_piLE_comp_initSeg (fun n ↦ (hX n).measurable) n).const_mul 2⁻¹
  have hhalf : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  -- half of the numeraire is at most the likelihood ratio against each null law
  have key : ∀ (P : Measure Bool) [IsProbabilityMeasure P], (∀ b, P {b} ≠ 0) →
      (∀ n x, 2⁻¹ * X n x ≤ ∏ i, Ber(true, false, ⟨1 / 2, by norm_num⟩) {x i} /
        P {x i}) →
      IsEProcess (fun n ω ↦ 2⁻¹ * X n fun i ↦ ω i) (Filtration.piLE (X := fun _ : ℕ ↦ Bool))
        {Measure.infinitePi fun _ : ℕ ↦ P} := by
    intro P _ hP hle
    have hE := (isEVar_div_singleton (Q := Ber(true, false, ⟨1 / 2, by norm_num⟩)) hP
      ).isEProcess_prod_piLE (by simpa)
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
