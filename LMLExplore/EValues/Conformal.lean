/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Exchangeable
public import LMLExplore.Probability.Exchangeability.Family
import LMLExplore.Algebra.BigOperators.Perm

/-!
# Conformal e-prediction

Given a training set `z₁, …, zₙ` of labelled observations `zᵢ = (xᵢ, yᵢ)` and a new object `x`, a
conformal e-predictor outputs, for every potential label `y` of `x`, an e-value that measures how
strange the completed sequence `z₁, …, zₙ, (x, y)` makes the test observation `(x, y)`. When the
training data and the test observation are exchangeable, the e-value of the true label is an
e-variable [Vov25, Proposition 2]: large e-values exclude labels, and the true label is excluded
at level `α⁻¹` with probability at most `α`.

The observations live in any measurable space `𝓩`, and a sample is indexed by a finite type: the
sample `Option ι → 𝓩` consists of the training points `some i` and the test point `none`.
* A **nonnegative nonconformity measure** (`ProbabilityTheory.IsNonconformityMeasure`) is a
  measurable `A : (ι → 𝓩) → ι → ℝ≥0∞`, assigning a score to every point of a sample, that is
  equivariant: permuting the sample permutes the scores. It is a **nonconformity e-measure**
  (`ProbabilityTheory.IsNonconformityEMeasure`) when moreover the scores have average at most `1`
  [Vov25, Section 2]. Vovk's scores are finite; here they are in `ℝ≥0∞`. Vovk defines these maps
  on samples of every length at once; every statement uses one length, so here they are defined on
  samples indexed by one finite type.
* Every nonnegative nonconformity measure becomes a nonconformity e-measure through the
  **normalization** `ProbabilityTheory.normalizeScores`, which divides the scores by their
  average, with the scores all `1` when they are all `0` [Vov25, Section 2]. When the scores are
  finite, the normalized scores have average exactly `1`: the nonconformity e-measure is
  admissible.
* The **conformal e-predictor** `ProbabilityTheory.conformalEPredictor A z x y` is the score of the
  test observation `(x, y)` in the sample completed by it [Vov25, Section 2].
* The **split conformal e-predictor** `ProbabilityTheory.splitConformalEPredictor N s t c x y`
  scores the calibration points `c` and the test observation `(x, y)` against the training set
  proper `t` with a split nonconformity measure `s`, and normalizes these summaries with a
  nonconformity e-measure `N` on the summary space, Vovk's normalizing transformation
  [Vov25, Section 5].
* The **cross-conformal e-predictor** `ProbabilityTheory.crossConformalEPredictor` splits the
  training set into folds by a map `fold`, computes for each fold the split conformal e-predictor
  with the fold as calibration set and the other folds as training set proper, and takes a
  weighted mean of these e-values [Vov25, Section 6]. Vovk's cross-conformal e-predictor is the
  arithmetic mean, and the weights proportional to the sizes of the folds are its variant.

The validity statements are derived from the description of the e-variables for exchangeability
at a fixed sample size (`ProbabilityTheory.isEVar_exchangeableLaws_iff`, in
`LMLExplore.EValues.Exchangeable`): the sum of the scores of one point over all the orderings of a
sample is `(K - 1)!` times the sum of the scores of the sample, for `K` its size. They are stated
for random samples with Tau Ceti's `ExchangeableFamily`, under every probability measure for which
the sample is exchangeable.

## Main definitions

* `ProbabilityTheory.IsNonconformityMeasure`, `ProbabilityTheory.IsNonconformityEMeasure`.
* `ProbabilityTheory.normalizeScores`: the normalization of a vector of scores.
* `ProbabilityTheory.conformalEPredictor`, `ProbabilityTheory.splitConformalEPredictor`,
  `ProbabilityTheory.crossConformalEPredictor`.

## Main statements

* `ProbabilityTheory.IsNonconformityEMeasure.isEVar`,
  `ProbabilityTheory.IsNonconformityMeasure.isExactEVar`: the score of any point of a sample is an
  e-variable for the exchangeable laws, and an exact one when the scores have average `1`.
* `ProbabilityTheory.IsNonconformityMeasure.isNonconformityEMeasure_normalizeScores`: the
  normalization of a nonnegative nonconformity measure is a nonconformity e-measure, and
  `ProbabilityTheory.sum_normalizeScores_of_ne_top` gives its admissibility for finite scores.
* `ProbabilityTheory.isEVar_normalizeScores`, `ProbabilityTheory.isExactEVar_normalizeScores_coe`,
  `ProbabilityTheory.isEVar_normalizeScores_comp`,
  `ProbabilityTheory.isExactEVar_normalizeScores_coe_comp`: **the soft-rank e-value** [BB24,
  Theorem 1]: for exchangeable nonnegative scores `S₁, …, S_K`, the ratio `S_i / ((∑ⱼ Sⱼ) / K)` is
  an e-variable, with expectation one when the scores are finite.
* `ProbabilityTheory.IsNonconformityEMeasure.isEVar_conformalEPredictor`,
  `ProbabilityTheory.IsNonconformityMeasure.isExactEVar_conformalEPredictor`: **validity of
  conformal e-predictors** [Vov25, Proposition 2].
* `ProbabilityTheory.IsNonconformityEMeasure.isEVar_splitConformalEPredictor`,
  `ProbabilityTheory.IsNonconformityEMeasure.isEVar_splitConformalEPredictor_inl_inr`: **validity of
  split conformal e-predictors** [Vov25, Proposition 10], when the calibration points and the test
  observation are exchangeable given the training set proper, and in particular when the whole
  sample is exchangeable; the exact versions are
  `ProbabilityTheory.IsNonconformityMeasure.isExactEVar_splitConformalEPredictor(_sumElim)`.
* `ProbabilityTheory.isEVar_crossConformalEPredictor`,
  `ProbabilityTheory.isExactEVar_crossConformalEPredictor`: **validity of cross-conformal
  e-predictors** [Vov25, Proposition 11], for weights of sum at most `1`, and with expectation one
  for admissible normalizing transformations and weights of sum `1`.

## References

* [Vov25] V. Vovk, *Conformal e-prediction*, Pattern Recognition 166 (2025),
  arXiv:2001.05989v5: Sections 2, 5 and 6, Propositions 2, 10 and 11.
* [BB24] A. A. Balinsky and A. D. Balinsky, *Enhancing conformal prediction using e-test
  statistics*, arXiv:2403.19082: Theorem 1.
-/

public section

open MeasureTheory TauCeti.Probability
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {ι κ Ω 𝓩 𝓢 𝓣 : Type*} [MeasurableSpace 𝓩] {mΩ : MeasurableSpace Ω}

/-! ### Nonconformity measures and nonconformity e-measures -/

section Definitions

variable [MeasurableSpace 𝓢]

/-- A **nonnegative nonconformity measure** on samples `ι → 𝓩` [Vov25, Section 2]: a measurable map
`A` assigning to every point `i` of a sample `z` a score `A z i ∈ [0, ∞]`, that is equivariant:
the scores of a permuted sample are the permuted scores. -/
structure IsNonconformityMeasure (A : (ι → 𝓩) → ι → ℝ≥0∞) : Prop where
  measurable : Measurable A
  comp_perm (σ : Equiv.Perm ι) (z : ι → 𝓩) : A (fun i ↦ z (σ i)) = fun i ↦ A z (σ i)

/-- A **nonconformity e-measure** on samples `ι → 𝓩` [Vov25, Section 2]: a nonnegative
nonconformity measure whose scores have average at most `1` on every sample. -/
structure IsNonconformityEMeasure [Fintype ι] (A : (ι → 𝓩) → ι → ℝ≥0∞) : Prop
    extends IsNonconformityMeasure A where
  sum_le (z : ι → 𝓩) : ∑ i, A z i ≤ Fintype.card ι

variable {A : (ι → 𝓩) → ι → ℝ≥0∞}

/-- The score of one point is a measurable function of the sample. -/
theorem IsNonconformityMeasure.measurable_apply (hA : IsNonconformityMeasure A) (i : ι) :
    Measurable fun z ↦ A z i :=
  (measurable_pi_apply i).comp hA.measurable

/-- The identity of `ι → ℝ≥0∞`, which scores every point by its value, is a nonnegative
nonconformity measure. -/
theorem isNonconformityMeasure_id : IsNonconformityMeasure (id : (ι → ℝ≥0∞) → ι → ℝ≥0∞) :=
  ⟨measurable_id, fun _ _ ↦ rfl⟩

/-- Scoring the images of the points under a measurable map `g` by a nonnegative nonconformity
measure on the space of the images gives a nonnegative nonconformity measure. -/
theorem IsNonconformityMeasure.comp {N : (ι → 𝓢) → ι → ℝ≥0∞} (hN : IsNonconformityMeasure N)
    {g : 𝓩 → 𝓢} (hg : Measurable g) : IsNonconformityMeasure fun z : ι → 𝓩 ↦ N fun i ↦ g (z i) :=
  ⟨hN.measurable.comp (Measurable.of_eval fun i ↦ hg.comp (measurable_pi_apply i)),
    fun σ z ↦ hN.comp_perm σ fun i ↦ g (z i)⟩

/-- Scoring the images of the points under a measurable map `g` by a nonconformity e-measure on
the space of the images gives a nonconformity e-measure. -/
theorem IsNonconformityEMeasure.comp [Fintype ι] {N : (ι → 𝓢) → ι → ℝ≥0∞}
    (hN : IsNonconformityEMeasure N) {g : 𝓩 → 𝓢} (hg : Measurable g) :
    IsNonconformityEMeasure fun z : ι → 𝓩 ↦ N fun i ↦ g (z i) :=
  ⟨hN.toIsNonconformityMeasure.comp hg, fun z ↦ hN.sum_le fun i ↦ g (z i)⟩

end Definitions

/-! ### Normalization -/

section Normalize

variable [Fintype ι] {a : ι → ℝ≥0∞}

/-- The **normalization** of a vector of scores `a` [Vov25, Section 2]: the scores divided by their
average, `K * a i / ∑ j, a j` for `K` the number of scores, and the constant `1` when all the
scores are `0`. -/
noncomputable def normalizeScores (a : ι → ℝ≥0∞) (i : ι) : ℝ≥0∞ :=
  if ∑ j, a j = 0 then 1 else Fintype.card ι * a i / ∑ j, a j

/-- The value of the normalized scores. -/
theorem normalizeScores_apply (a : ι → ℝ≥0∞) (i : ι) :
    normalizeScores a i = if ∑ j, a j = 0 then 1 else Fintype.card ι * a i / ∑ j, a j :=
  (rfl)

/-- The normalization of scores that are all `0` is the constant `1`. -/
@[simp]
theorem normalizeScores_of_sum_eq_zero (h : ∑ j, a j = 0) (i : ι) : normalizeScores a i = 1 := by
  simp [normalizeScores_apply, h]

/-- The normalization of scores with a nonzero sum divides them by their average. -/
theorem normalizeScores_of_sum_ne_zero (h : ∑ j, a j ≠ 0) (i : ι) :
    normalizeScores a i = Fintype.card ι * a i / ∑ j, a j := by
  simp [normalizeScores_apply, h]

/-- The sum of the normalized scores of a vector with nonzero sum is `K * (∑ a) / ∑ a`. -/
private lemma sum_normalizeScores_of_sum_ne_zero (h : ∑ j, a j ≠ 0) :
    ∑ i, normalizeScores a i = Fintype.card ι * (∑ j, a j) / ∑ j, a j := by
  simp_rw [normalizeScores_of_sum_ne_zero h, div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum]

/-- The normalized scores have average at most `1`. -/
theorem sum_normalizeScores_le (a : ι → ℝ≥0∞) : ∑ i, normalizeScores a i ≤ Fintype.card ι := by
  by_cases h : ∑ j, a j = 0
  · simp [h]
  · rw [sum_normalizeScores_of_sum_ne_zero h]
    exact ENNReal.div_le_of_le_mul le_rfl

/-- The normalized scores of finite scores have average `1`. -/
theorem sum_normalizeScores_of_ne_top (ha : ∀ i, a i ≠ ∞) :
    ∑ i, normalizeScores a i = Fintype.card ι := by
  by_cases h : ∑ j, a j = 0
  · simp [h]
  · rw [sum_normalizeScores_of_sum_ne_zero h,
      ENNReal.mul_div_cancel_right h (ENNReal.sum_ne_top.2 fun i _ ↦ ha i)]

/-- Normalization commutes with the permutations of the scores. -/
theorem normalizeScores_comp_perm (σ : Equiv.Perm ι) (a : ι → ℝ≥0∞) :
    normalizeScores (fun i ↦ a (σ i)) = fun i ↦ normalizeScores a (σ i) := by
  ext i
  simp_rw [normalizeScores_apply, Equiv.sum_comp σ a]

/-- The normalization is measurable. -/
theorem measurable_normalizeScores :
    Measurable (normalizeScores : (ι → ℝ≥0∞) → ι → ℝ≥0∞) := by
  refine Measurable.of_eval fun i ↦ ?_
  simp_rw [normalizeScores_apply]
  have hsum : Measurable fun a : ι → ℝ≥0∞ ↦ ∑ j, a j := by fun_prop
  exact Measurable.ite (measurableSet_eq_fun hsum measurable_const) measurable_const
    (((measurable_pi_apply i).const_mul _).div hsum)

variable {A : (ι → 𝓩) → ι → ℝ≥0∞}

/-- **Normalization** [Vov25, Section 2]: the normalization of a nonnegative nonconformity measure
is a nonconformity e-measure. It is admissible, its scores having average `1`, when the scores of
`A` are finite (`ProbabilityTheory.sum_normalizeScores_of_ne_top`). -/
theorem IsNonconformityMeasure.isNonconformityEMeasure_normalizeScores
    (hA : IsNonconformityMeasure A) : IsNonconformityEMeasure fun z ↦ normalizeScores (A z) :=
  ⟨⟨measurable_normalizeScores.comp hA.measurable, fun σ z ↦ by
    rw [hA.comp_perm, normalizeScores_comp_perm]⟩, fun z ↦ sum_normalizeScores_le (A z)⟩

end Normalize

/-! ### Validity for exchangeable samples -/

section Validity

variable [Fintype ι] {A : (ι → 𝓩) → ι → ℝ≥0∞}

/-- **The scores of one point over the orderings of a sample**: `K` times the sum, over the
permutations `σ`, of the score of `i` in the permuted sample is the number of permutations times
the sum of the scores of the sample, for `K` the size of the sample. -/
theorem IsNonconformityMeasure.card_mul_sum_perm [DecidableEq ι] (hA : IsNonconformityMeasure A)
    (z : ι → 𝓩) (i : ι) :
    Fintype.card ι * ∑ σ : Equiv.Perm ι, A (fun j ↦ z (σ j)) i =
      Fintype.card (Equiv.Perm ι) * ∑ j, A z j := by
  simp_rw [hA.comp_perm]
  simpa [nsmul_eq_mul] using Equiv.Perm.card_nsmul_sum_apply (A z) i

/-- **Validity of nonconformity e-measures**: the score of any point of a sample under a
nonconformity e-measure is an e-variable for the exchangeable probability laws of the sample. -/
theorem IsNonconformityEMeasure.isEVar (hA : IsNonconformityEMeasure A) (i : ι) :
    IsEVar (fun z ↦ A z i) (exchangeableLaws ∩ {μ : Measure (ι → 𝓩) | IsProbabilityMeasure μ}) := by
  classical
  refine isEVar_exchangeableLaws_iff.2 ⟨hA.measurable_apply i, fun z ↦ ?_⟩
  have : Nonempty ι := ⟨i⟩
  have hK : (Fintype.card ι : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine (ENNReal.mul_le_mul_iff_right hK (ENNReal.natCast_ne_top _)).1 ?_
  rw [hA.card_mul_sum_perm, mul_comm (Fintype.card ι : ℝ≥0∞)]
  gcongr
  exact hA.sum_le z

/-- **Validity of admissible nonconformity e-measures**: when the scores of a nonnegative
nonconformity measure have average `1` on every sample, the score of any point is an exact
e-variable for the exchangeable probability laws of the sample. -/
theorem IsNonconformityMeasure.isExactEVar (hA : IsNonconformityMeasure A)
    (hsum : ∀ z, ∑ j, A z j = Fintype.card ι) (i : ι) :
    IsExactEVar (fun z ↦ A z i)
      (exchangeableLaws ∩ {μ : Measure (ι → 𝓩) | IsProbabilityMeasure μ}) := by
  classical
  refine isExactEVar_exchangeableLaws_iff.2 ⟨hA.measurable_apply i, fun z ↦ ?_⟩
  have : Nonempty ι := ⟨i⟩
  have hK : (Fintype.card ι : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine (ENNReal.mul_right_inj hK (ENNReal.natCast_ne_top _)).1 ?_
  rw [hA.card_mul_sum_perm, hsum, mul_comm]

/-- **The soft-rank e-value** [BB24, Theorem 1]: for scores in `[0, ∞]`, the normalized score
`K * s i / ∑ j, s j` of any coordinate, with the value `1` when all the scores are `0`, is an
e-variable for the exchangeable probability laws of the scores. -/
theorem isEVar_normalizeScores (i : ι) :
    IsEVar (fun s : ι → ℝ≥0∞ ↦ normalizeScores s i)
      (exchangeableLaws ∩ {μ : Measure (ι → ℝ≥0∞) | IsProbabilityMeasure μ}) :=
  isNonconformityMeasure_id.isNonconformityEMeasure_normalizeScores.isEVar i

/-- **The soft-rank e-value is exact for finite scores** [BB24, Theorem 1]: for scores in
`[0, ∞)`, the normalized score `K * s i / ∑ j, s j` of any coordinate, with the value `1` when all
the scores are `0`, is an exact e-variable for the exchangeable probability laws of the scores. -/
theorem isExactEVar_normalizeScores_coe (i : ι) :
    IsExactEVar (fun s : ι → ℝ≥0 ↦ normalizeScores (fun j ↦ (s j : ℝ≥0∞)) i)
      (exchangeableLaws ∩ {μ : Measure (ι → ℝ≥0) | IsProbabilityMeasure μ}) :=
  have hA := (isNonconformityMeasure_id.comp measurable_coe_nnreal_ennreal)
    |>.isNonconformityEMeasure_normalizeScores
  hA.toIsNonconformityMeasure.isExactEVar
    (fun _ ↦ sum_normalizeScores_of_ne_top fun _ ↦ ENNReal.coe_ne_top) i

/-- **The soft-rank e-value of exchangeable scores** [BB24, Theorem 1]: for an exchangeable family
`S` of random scores in `[0, ∞]` indexed by a finite type, the normalized score
`K * S i / ∑ j, S j` is an e-variable for the probability measures under which `S` is
exchangeable. -/
theorem isEVar_normalizeScores_comp {S : ι → Ω → ℝ≥0∞} (hS : ∀ j, Measurable (S j)) (i : ι) :
    IsEVar (fun ω ↦ normalizeScores (fun j ↦ S j ω) i)
      {P | IsProbabilityMeasure P ∧ ExchangeableFamily P S} :=
  (isEVar_normalizeScores i).comp_exchangeableFamily hS

/-- **The soft-rank e-value of exchangeable finite scores has expectation one** [BB24, Theorem 1]:
for an exchangeable family `S` of random scores in `[0, ∞)` indexed by a finite type, the
normalized score `K * S i / ∑ j, S j` is an exact e-variable for the probability measures under
which `S` is exchangeable. -/
theorem isExactEVar_normalizeScores_coe_comp {S : ι → Ω → ℝ≥0} (hS : ∀ j, Measurable (S j))
    (i : ι) :
    IsExactEVar (fun ω ↦ normalizeScores (fun j ↦ (S j ω : ℝ≥0∞)) i)
      {P | IsProbabilityMeasure P ∧ ExchangeableFamily P S} :=
  (isExactEVar_normalizeScores_coe i).comp_exchangeableFamily hS

end Validity

/-! ### Conformal e-predictors -/

section ConformalEPredictor

variable {𝓧 𝓨 : Type*}

/-- The **conformal e-predictor** of a nonnegative nonconformity measure `A` on samples
`Option ι → 𝓧 × 𝓨` [Vov25, Section 2]: for training observations `z : ι → 𝓧 × 𝓨`, a test object `x`
and a potential label `y`, the score of the test observation `(x, y)` in the sample made of the
training observations, at the indices `some i`, and of `(x, y)`, at the index `none`. Large values
exclude the label `y`. -/
noncomputable def conformalEPredictor (A : (Option ι → 𝓧 × 𝓨) → Option ι → ℝ≥0∞)
    (z : ι → 𝓧 × 𝓨) (x : 𝓧) (y : 𝓨) : ℝ≥0∞ :=
  A (fun j ↦ j.elim (x, y) z) none

/-- The value of the conformal e-predictor. -/
theorem conformalEPredictor_apply (A : (Option ι → 𝓧 × 𝓨) → Option ι → ℝ≥0∞)
    (z : ι → 𝓧 × 𝓨) (x : 𝓧) (y : 𝓨) :
    conformalEPredictor A z x y = A (fun j ↦ j.elim (x, y) z) none :=
  (rfl)

/-- The conformal e-predictor at the observed test observation `w none` of a sample `w` is the
score of the test observation in `w`. -/
theorem conformalEPredictor_some_none (A : (Option ι → 𝓧 × 𝓨) → Option ι → ℝ≥0∞)
    (w : Option ι → 𝓧 × 𝓨) :
    conformalEPredictor A (fun i ↦ w (some i)) (w none).1 (w none).2 = A w none := by
  rw [conformalEPredictor_apply]
  congr
  ext j : 1
  cases j <;> simp

variable [MeasurableSpace 𝓧] [MeasurableSpace 𝓨] [Fintype ι]
  {A : (Option ι → 𝓧 × 𝓨) → Option ι → ℝ≥0∞} {W : Option ι → Ω → 𝓧 × 𝓨}

/-- **Validity of conformal e-predictors** [Vov25, Proposition 2]: for a nonconformity e-measure,
a random sample `W` of training observations `W (some i)` and of a test observation `W none`, the
conformal e-predictor at the true label of the test object is an e-variable for the probability
measures under which the sample is exchangeable. -/
theorem IsNonconformityEMeasure.isEVar_conformalEPredictor (hA : IsNonconformityEMeasure A)
    (hW : ∀ j, Measurable (W j)) :
    IsEVar (fun ω ↦ conformalEPredictor A (fun i ↦ W (some i) ω) (W none ω).1 (W none ω).2)
      {P | IsProbabilityMeasure P ∧ ExchangeableFamily P W} := by
  have h := (hA.isEVar none).comp_exchangeableFamily hW
  simp_rw [← conformalEPredictor_some_none] at h
  exact h

/-- **Validity of admissible conformal e-predictors** [Vov25, Proposition 2]: when the scores of a
nonnegative nonconformity measure have average `1` on every sample, the conformal e-predictor at
the true label of the test object of an exchangeable random sample has expectation one. -/
theorem IsNonconformityMeasure.isExactEVar_conformalEPredictor (hA : IsNonconformityMeasure A)
    (hsum : ∀ w, ∑ j, A w j = Fintype.card (Option ι)) (hW : ∀ j, Measurable (W j)) :
    IsExactEVar (fun ω ↦ conformalEPredictor A (fun i ↦ W (some i) ω) (W none ω).1 (W none ω).2)
      {P | IsProbabilityMeasure P ∧ ExchangeableFamily P W} := by
  have h := (hA.isExactEVar hsum none).comp_exchangeableFamily hW
  simp_rw [← conformalEPredictor_some_none] at h
  exact h

end ConformalEPredictor

/-! ### Split conformal e-predictors -/

section SplitConformalEPredictor

variable {𝓧 𝓨 : Type*}

/-- The **split conformal e-predictor** [Vov25, Section 5]. A split nonconformity measure
`s : 𝓣 → 𝓧 × 𝓨 → 𝓢` summarizes how an observation conforms to a training set proper `t : 𝓣`, and
a normalizing transformation `N`, a nonconformity e-measure on samples `Option ι → 𝓢` of summaries,
turns the summaries of the calibration observations `c : ι → 𝓧 × 𝓨`, at the indices `some i`, and
of the test observation `(x, y)`, at the index `none`, into scores. The e-value of the label `y` is
the score of the test observation. -/
noncomputable def splitConformalEPredictor (N : (Option ι → 𝓢) → Option ι → ℝ≥0∞)
    (s : 𝓣 → 𝓧 × 𝓨 → 𝓢) (t : 𝓣) (c : ι → 𝓧 × 𝓨) (x : 𝓧) (y : 𝓨) : ℝ≥0∞ :=
  N (fun j ↦ j.elim (s t (x, y)) fun i ↦ s t (c i)) none

/-- The value of the split conformal e-predictor. -/
theorem splitConformalEPredictor_apply (N : (Option ι → 𝓢) → Option ι → ℝ≥0∞)
    (s : 𝓣 → 𝓧 × 𝓨 → 𝓢) (t : 𝓣) (c : ι → 𝓧 × 𝓨) (x : 𝓧) (y : 𝓨) :
    splitConformalEPredictor N s t c x y =
      N (fun j ↦ j.elim (s t (x, y)) fun i ↦ s t (c i)) none :=
  (rfl)

/-- The split conformal e-predictor at the observed test observation `w none` of a sample `w` of
calibration and test observations is the score, under the normalizing transformation, of the test
summary among the summaries of `w` against the training set proper. -/
theorem splitConformalEPredictor_some_none (N : (Option ι → 𝓢) → Option ι → ℝ≥0∞)
    (s : 𝓣 → 𝓧 × 𝓨 → 𝓢) (t : 𝓣) (w : Option ι → 𝓧 × 𝓨) :
    splitConformalEPredictor N s t (fun i ↦ w (some i)) (w none).1 (w none).2 =
      N (fun j ↦ s t (w j)) none := by
  rw [splitConformalEPredictor_apply]
  congr
  ext j : 1
  cases j <;> simp

/-- The split conformal e-predictor at the true label, as a function of the pairs made of the
training set proper and of each calibration or test observation, is the score of the test point
under a nonconformity measure on these pairs. -/
private lemma splitConformalEPredictor_eq_comp (N : (Option ι → 𝓢) → Option ι → ℝ≥0∞)
    (s : 𝓣 → 𝓧 × 𝓨 → 𝓢) (T : Ω → 𝓣) (W : Option ι → Ω → 𝓧 × 𝓨) :
    (fun ω ↦ splitConformalEPredictor N s (T ω) (fun i ↦ W (some i) ω) (W none ω).1 (W none ω).2) =
      fun ω ↦ (fun v : Option ι → 𝓣 × (𝓧 × 𝓨) ↦ N (fun j ↦ s (v j).1 (v j).2) none)
        fun j ↦ (T ω, W j ω) := by
  ext ω
  exact splitConformalEPredictor_some_none N s (T ω) fun j ↦ W j ω

variable [MeasurableSpace 𝓧] [MeasurableSpace 𝓨] [MeasurableSpace 𝓢] [MeasurableSpace 𝓣]
  [Fintype ι] {N : (Option ι → 𝓢) → Option ι → ℝ≥0∞} {s : 𝓣 → 𝓧 × 𝓨 → 𝓢} {T : Ω → 𝓣}
  {W : Option ι → Ω → 𝓧 × 𝓨}

/-- **Validity of split conformal e-predictors, given the training set proper** [Vov25,
Proposition 10]: for a normalizing transformation `N`, a measurable split nonconformity measure
`s`, a random training set proper `T` and random calibration and test observations `W`, the split
conformal e-predictor at the true label of the test object is an e-variable for the probability
measures under which the pairs `(T, W j)` are exchangeable, that is, under which the calibration
and test observations are exchangeable given the training set proper. -/
theorem IsNonconformityEMeasure.isEVar_splitConformalEPredictor (hN : IsNonconformityEMeasure N)
    (hs : Measurable (Function.uncurry s)) (hT : Measurable T) (hW : ∀ j, Measurable (W j)) :
    IsEVar
      (fun ω ↦ splitConformalEPredictor N s (T ω) (fun i ↦ W (some i) ω) (W none ω).1 (W none ω).2)
      {P | IsProbabilityMeasure P ∧ ExchangeableFamily P fun j ω ↦ (T ω, W j ω)} := by
  rw [splitConformalEPredictor_eq_comp]
  exact ((hN.comp hs).isEVar none).comp_exchangeableFamily fun j ↦ hT.prodMk (hW j)

/-- **Validity of admissible split conformal e-predictors, given the training set proper**
[Vov25, Proposition 10]: when the normalizing transformation is admissible, its scores having
average `1` on every sample, the split conformal e-predictor at the true label has expectation one
under every probability measure under which the pairs `(T, W j)` are exchangeable. -/
theorem IsNonconformityMeasure.isExactEVar_splitConformalEPredictor (hN : IsNonconformityMeasure N)
    (hsum : ∀ v, ∑ j, N v j = Fintype.card (Option ι)) (hs : Measurable (Function.uncurry s))
    (hT : Measurable T) (hW : ∀ j, Measurable (W j)) :
    IsExactEVar
      (fun ω ↦ splitConformalEPredictor N s (T ω) (fun i ↦ W (some i) ω) (W none ω).1 (W none ω).2)
      {P | IsProbabilityMeasure P ∧ ExchangeableFamily P fun j ω ↦ (T ω, W j ω)} := by
  rw [splitConformalEPredictor_eq_comp]
  exact ((hN.comp hs).isExactEVar (fun _ ↦ hsum _) none).comp_exchangeableFamily
    fun j ↦ hT.prodMk (hW j)

variable [Countable κ] {s : (κ → 𝓧 × 𝓨) → 𝓧 × 𝓨 → 𝓢} {Z : κ ⊕ Option ι → Ω → 𝓧 × 𝓨}

/-- **Validity of split conformal e-predictors** [Vov25, Proposition 10]: for a random sample `Z`
made of a training set proper, at the indices `inl k`, of calibration observations, at the indices
`inr (some i)`, and of a test observation, at the index `inr none`, the split conformal
e-predictor at the true label of the test object is an e-variable for the probability measures
under which the whole sample is exchangeable. -/
theorem IsNonconformityEMeasure.isEVar_splitConformalEPredictor_inl_inr
    (hN : IsNonconformityEMeasure N) (hs : Measurable (Function.uncurry s))
    (hZ : ∀ j, Measurable (Z j)) :
    IsEVar
      (fun ω ↦ splitConformalEPredictor N s (fun k ↦ Z (.inl k) ω)
        (fun i ↦ Z (.inr (some i)) ω) (Z (.inr none) ω).1 (Z (.inr none) ω).2)
      {P | IsProbabilityMeasure P ∧ ExchangeableFamily P Z} := by
  refine IsEVar.anti_set (fun P hP ↦ ?_) (hN.isEVar_splitConformalEPredictor hs
    (Measurable.of_eval fun k ↦ hZ (.inl k)) fun j ↦ hZ (.inr j))
  have := hP.1
  exact ⟨hP.1, hP.2.prodMk_inl_inr hZ⟩

/-- **Validity of admissible split conformal e-predictors** [Vov25, Proposition 10]: when the
normalizing transformation is admissible, the split conformal e-predictor at the true label of the
test object of an exchangeable random sample has expectation one. -/
theorem IsNonconformityMeasure.isExactEVar_splitConformalEPredictor_inl_inr
    (hN : IsNonconformityMeasure N) (hsum : ∀ v, ∑ j, N v j = Fintype.card (Option ι))
    (hs : Measurable (Function.uncurry s)) (hZ : ∀ j, Measurable (Z j)) :
    IsExactEVar
      (fun ω ↦ splitConformalEPredictor N s (fun k ↦ Z (.inl k) ω)
        (fun i ↦ Z (.inr (some i)) ω) (Z (.inr none) ω).1 (Z (.inr none) ω).2)
      {P | IsProbabilityMeasure P ∧ ExchangeableFamily P Z} := by
  refine IsExactEVar.anti_set (fun P hP ↦ ?_) (hN.isExactEVar_splitConformalEPredictor hsum hs
    (Measurable.of_eval fun k ↦ hZ (.inl k)) fun j ↦ hZ (.inr j))
  have := hP.1
  exact ⟨hP.1, hP.2.prodMk_inl_inr hZ⟩

end SplitConformalEPredictor

/-! ### Cross-conformal e-predictors -/

section CrossConformalEPredictor

variable {𝓧 𝓨 F : Type*}

/-- The indices of a sample of training and test observations, arranged as the training set
proper of the fold `f` followed by the calibration and test indices of that fold. -/
private def foldEmbedding (fold : κ → F) (f : F) :
    {i // fold i ≠ f} ⊕ Option {i // fold i = f} → Option κ :=
  Sum.elim (fun i ↦ some i.1) (Option.map Subtype.val)

private lemma injective_foldEmbedding (fold : κ → F) (f : F) :
    Function.Injective (foldEmbedding fold f) := by
  refine ((Option.some_injective _).comp Subtype.val_injective).sumElim
    (Option.map_injective Subtype.val_injective) fun i j h ↦ ?_
  cases j with
  | none => simp at h
  | some j =>
    simp only [Function.comp_apply, Option.map_some, Option.some_inj] at h
    exact i.2 (h ▸ j.2)

variable [Fintype F]

/-- The **cross-conformal e-predictor** [Vov25, Section 6]. The training observations
`z : κ → 𝓧 × 𝓨` are split into folds by `fold : κ → F`. For each fold `f`, the split conformal
e-predictor with the normalizing transformation `N f` and the split nonconformity measure `s f`
uses the fold as calibration set and the other folds as training set proper; the cross-conformal
e-predictor is the mean of these e-values with the weights `w`. Vovk's cross-conformal
e-predictor has the weights `1 / #F`, and its variant the weights proportional to the sizes of the
folds. -/
noncomputable def crossConformalEPredictor (fold : κ → F) (w : F → ℝ≥0∞)
    (N : ∀ f, (Option {i // fold i = f} → 𝓢) → Option {i // fold i = f} → ℝ≥0∞)
    (s : ∀ f, ({i // fold i ≠ f} → 𝓧 × 𝓨) → 𝓧 × 𝓨 → 𝓢) (z : κ → 𝓧 × 𝓨) (x : 𝓧) (y : 𝓨) :
    ℝ≥0∞ :=
  ∑ f, w f * splitConformalEPredictor (N f) (s f) (fun i ↦ z i) (fun i ↦ z i) x y

/-- The value of the cross-conformal e-predictor. -/
theorem crossConformalEPredictor_apply (fold : κ → F) (w : F → ℝ≥0∞)
    (N : ∀ f, (Option {i // fold i = f} → 𝓢) → Option {i // fold i = f} → ℝ≥0∞)
    (s : ∀ f, ({i // fold i ≠ f} → 𝓧 × 𝓨) → 𝓧 × 𝓨 → 𝓢) (z : κ → 𝓧 × 𝓨) (x : 𝓧) (y : 𝓨) :
    crossConformalEPredictor fold w N s z x y =
      ∑ f, w f * splitConformalEPredictor (N f) (s f) (fun i ↦ z i) (fun i ↦ z i) x y :=
  (rfl)

variable [MeasurableSpace 𝓧] [MeasurableSpace 𝓨] [MeasurableSpace 𝓢] [Fintype κ] [DecidableEq F]
  {fold : κ → F}
  {N : ∀ f, (Option {i // fold i = f} → 𝓢) → Option {i // fold i = f} → ℝ≥0∞}
  {s : ∀ f, ({i // fold i ≠ f} → 𝓧 × 𝓨) → 𝓧 × 𝓨 → 𝓢} {W : Option κ → Ω → 𝓧 × 𝓨}

omit [Fintype F] [Fintype κ] [DecidableEq F] in
/-- In an exchangeable sample of training and test observations, the calibration and test
observations of a fold, each paired with the training set proper of that fold, are
exchangeable. -/
private lemma exchangeableFamily_fold [Countable κ] {P : Measure Ω} [IsFiniteMeasure P]
    (hP : ExchangeableFamily P W) (hW : ∀ j, Measurable (W j)) (f : F) :
    ExchangeableFamily P fun (j : Option {i // fold i = f}) ω ↦
      ((fun i : {i // fold i ≠ f} ↦ W (some i.1) ω), W (j.map Subtype.val) ω) :=
  (hP.comp_injective (injective_foldEmbedding fold f)).prodMk_inl_inr fun _ ↦ hW _

omit [Fintype F] in
/-- The split conformal e-predictor of a fold, at the true label of the test object, is an
e-variable for the probability measures under which the sample is exchangeable. -/
private lemma isEVar_splitConformalEPredictor_fold (f : F) (hN : IsNonconformityEMeasure (N f))
    (hs : Measurable (Function.uncurry (s f))) (hW : ∀ j, Measurable (W j)) :
    IsEVar (fun ω ↦ splitConformalEPredictor (N f) (s f) (fun i ↦ W (some i.1) ω)
        (fun i ↦ W (some i.1) ω) (W none ω).1 (W none ω).2)
      {P | IsProbabilityMeasure P ∧ ExchangeableFamily P W} := by
  refine IsEVar.anti_set (fun P hP ↦ ?_)
    (hN.isEVar_splitConformalEPredictor (W := fun j ↦ W (j.map Subtype.val)) hs
      (Measurable.of_eval fun _ ↦ hW _) fun _ ↦ hW _)
  have := hP.1
  exact ⟨hP.1, exchangeableFamily_fold hP.2 hW f⟩

omit [Fintype F] in
/-- The split conformal e-predictor of a fold with an admissible normalizing transformation, at the
true label of the test object, is an exact e-variable for the probability measures under which the
sample is exchangeable. -/
private lemma isExactEVar_splitConformalEPredictor_fold (f : F)
    (hN : IsNonconformityMeasure (N f))
    (hsum : ∀ v, ∑ j, N f v j = Fintype.card (Option {i // fold i = f}))
    (hs : Measurable (Function.uncurry (s f))) (hW : ∀ j, Measurable (W j)) :
    IsExactEVar (fun ω ↦ splitConformalEPredictor (N f) (s f) (fun i ↦ W (some i.1) ω)
        (fun i ↦ W (some i.1) ω) (W none ω).1 (W none ω).2)
      {P | IsProbabilityMeasure P ∧ ExchangeableFamily P W} := by
  refine IsExactEVar.anti_set (fun P hP ↦ ?_)
    (hN.isExactEVar_splitConformalEPredictor (W := fun j ↦ W (j.map Subtype.val)) hsum hs
      (Measurable.of_eval fun _ ↦ hW _) fun _ ↦ hW _)
  have := hP.1
  exact ⟨hP.1, exchangeableFamily_fold hP.2 hW f⟩

/-- **Validity of cross-conformal e-predictors** [Vov25, Proposition 11]: for normalizing
transformations `N f`, measurable split nonconformity measures `s f` and weights of sum at most
`1`, the cross-conformal e-predictor at the true label of the test object `W none` is an
e-variable for the probability measures under which the sample `W` of training observations
`W (some i)` and of the test observation is exchangeable. -/
theorem isEVar_crossConformalEPredictor (hN : ∀ f, IsNonconformityEMeasure (N f))
    (hs : ∀ f, Measurable (Function.uncurry (s f))) {w : F → ℝ≥0∞} (hw : ∑ f, w f ≤ 1)
    (hW : ∀ j, Measurable (W j)) :
    IsEVar
      (fun ω ↦ crossConformalEPredictor fold w N s (fun i ↦ W (some i) ω) (W none ω).1
        (W none ω).2)
      {P | IsProbabilityMeasure P ∧ ExchangeableFamily P W} := by
  simp_rw [crossConformalEPredictor_apply]
  exact isEVar_finsetSum_mul _
    (fun f _ ↦ isEVar_splitConformalEPredictor_fold f (hN f) (hs f) hW) hw

/-- **Validity of admissible cross-conformal e-predictors** [Vov25, Proposition 11]: when every
normalizing transformation is admissible, its scores having average `1` on every sample, and the
weights have sum `1`, the cross-conformal e-predictor at the true label of the test object of an
exchangeable random sample has expectation one. -/
theorem isExactEVar_crossConformalEPredictor (hN : ∀ f, IsNonconformityMeasure (N f))
    (hsum : ∀ f v, ∑ j, N f v j = Fintype.card (Option {i // fold i = f}))
    (hs : ∀ f, Measurable (Function.uncurry (s f))) {w : F → ℝ≥0∞} (hw : ∑ f, w f = 1)
    (hW : ∀ j, Measurable (W j)) :
    IsExactEVar
      (fun ω ↦ crossConformalEPredictor fold w N s (fun i ↦ W (some i) ω) (W none ω).1
        (W none ω).2)
      {P | IsProbabilityMeasure P ∧ ExchangeableFamily P W} := by
  simp_rw [crossConformalEPredictor_apply]
  exact isExactEVar_finsetSum_mul _
    (fun f _ ↦ isExactEVar_splitConformalEPredictor_fold f (hN f) (hsum f) (hs f) hW) hw

end CrossConformalEPredictor

end ProbabilityTheory
