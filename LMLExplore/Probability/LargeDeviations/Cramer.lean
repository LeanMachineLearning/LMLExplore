/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.LargeDeviations.Basic
public import LMLExplore.Probability.Distributions.ExponentialFamily.Cramer
public import LMLExplore.Probability.Distributions.ExponentialFamily.RateFunction
public import LMLExplore.Probability.LargeDeviations.Chernoff

/-!
# Cramér's theorem on `ℝ`

Let `ν` be a probability measure on `ℝ` with Cramér rate function
`I(x) = sup_t (t x - log E_ν[exp (t X)])` (`LMLExplore.rateFunction id ν`). The laws of the
empirical means `(∑ i < n, X i) / n` of `n` independent samples of `ν` satisfy the large deviation
principle with speed `n` and rate function `I` as soon as `ν` has a mean, and `I` is a good rate
function when the cumulant generating function of `ν` is finite on a neighbourhood of `0`:
this is Cramér's theorem [DZ98, Theorem 2.2.3]. The same holds for the empirical means of a
sequence of independent identically distributed real random variables, and for the empirical
means of the statistic `T` of the samples of a member of an exponential family, with the extended
divergence `Measure.expFamilyRate` of the family as rate function [D23, Lemma 11]. These are the
principles of a single arm that the large deviations of the empirical means of a bandit under
static allocations combine across arms.

The upper bound on a closed set `F` comes from the Cramér–Chernoff bounds of
`LMLExplore.Probability.LargeDeviations.Chernoff` on the two half-lines bounded by the points of
`F` nearest to the mean, at which the rate function is at least its infimum on `F`.

The lower bound holds for every probability measure, at every level `x`. If `ν` gives no mass to
one side of `x`, then `I(x) = -log ν{x}` and the empirical mean is `x` with probability at least
`ν{x}^n`. Otherwise the proof truncates `ν` to an interval `[-M, M]`, as in [DZ98]: the
normalized truncation `ν_M` has every exponential moment and charges both sides of `x`, so `x` is
a mean of its exponential family, and the exponential tilting of
`LMLExplore.Probability.Distributions.ExponentialFamily.Cramer` bounds the probability that the
empirical mean of `ν_M` is near `x` by `exp (-(n (I_M(x) + ε)))`. The rates of the truncations
converge to `I(x)`: the functions `t ↦ ∫_{[-M, M]} exp (t (y - x)) dν(y)` increase to
`t ↦ ∫ exp (t (y - x)) dν(y)`, whose infimum is `exp (-I(x))`, and they are continuous and
coercive, so a nested compact sets argument shows that their infima converge.

## Main statements

* `LMLExplore.limsup_log_measure_le_neg_iInf_rateFunction`: the upper bound of Cramér's theorem on
  closed sets, for `ν` with a mean.
* `LMLExplore.neg_rateFunction_le_liminf_log_measure`: the lower bound of Cramér's theorem on the
  neighbourhoods of every level, for every probability measure `ν`.
* `LMLExplore.isLDP_cramer`: **Cramér's theorem**, the large deviation principle of the empirical
  means of independent samples of a law on `ℝ` with a mean.
* `LMLExplore.isGoodRateFunction_rateFunction`: the rate function is good when the cumulant
  generating function is finite near `0`.
* `LMLExplore.isLDP_cramer_of_iIndepFun`: Cramér's theorem for a sequence of independent
  identically distributed integrable real random variables.
* `MeasureTheory.Measure.isLDP_cramer_expFamily`: Cramér's theorem for the statistic of the
  samples of a member of a one-parameter exponential family on any measurable space, with the
  extended divergence `Measure.expFamilyRate` as rate function, and
  `MeasureTheory.Measure.isGoodRateFunction_expFamilyRate_left`: that rate function is good.

## References

* [DZ98] A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed.,
  Springer, 1998, Theorem 2.2.3 and Lemma 2.2.5.
* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468, Lemma 11.
-/

public section

open MeasureTheory ProbabilityTheory Filter Real Set Finset Topology

open scoped ENNReal NNReal

namespace LMLExplore

variable {ν : Measure ℝ} {x : ℝ}

/-! ### The empirical mean of the coordinates -/

private lemma measurable_mean (n : ℕ) : Measurable fun y : Fin n → ℝ ↦ (∑ i, y i) / n := by
  fun_prop

private lemma iIndepFun_eval [IsProbabilityMeasure ν] (n : ℕ) :
    iIndepFun (fun (i : Fin n) (y : Fin n → ℝ) ↦ y i) (Measure.pi fun _ ↦ ν) :=
  iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id

private lemma identDistrib_eval [IsProbabilityMeasure ν] {n : ℕ} (i : Fin n) :
    IdentDistrib (fun y : Fin n → ℝ ↦ y i) id (Measure.pi fun _ ↦ ν) ν :=
  (measurePreserving_eval (fun _ ↦ ν) i).hasLaw.identDistrib HasLaw.id

/-! ### The upper bound -/

/-- The Cramér–Chernoff bound on the upper tail of the sum of `n` independent samples of `ν`. -/
private lemma measure_sum_ge_le [IsProbabilityMeasure ν] (hν : Integrable id ν) (n : ℕ) {r : ℝ}
    (hx : ∫ y, y ∂ν ≤ x) (hr : ENNReal.ofReal r ≤ rateFunction id ν x) :
    (Measure.pi fun _ : Fin n ↦ ν) {y | n * x ≤ ∑ i, y i} ≤ ENNReal.ofReal (exp (-(n * r))) := by
  have h := (iIndepFun_eval (ν := ν) n).measureReal_sum_ge_le_exp_of_le_rateFunction
    (s := univ) (fun i _ ↦ (identDistrib_eval i).mgfDominatedOn) hν hx hr
  rw [card_univ, Fintype.card_fin] at h
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h

/-- The Cramér–Chernoff bound on the lower tail of the sum of `n` independent samples of `ν`. -/
private lemma measure_sum_le_le [IsProbabilityMeasure ν] (hν : Integrable id ν) (n : ℕ) {r : ℝ}
    (hx : x ≤ ∫ y, y ∂ν) (hr : ENNReal.ofReal r ≤ rateFunction id ν x) :
    (Measure.pi fun _ : Fin n ↦ ν) {y | ∑ i, y i ≤ n * x} ≤ ENNReal.ofReal (exp (-(n * r))) := by
  have h := (iIndepFun_eval (ν := ν) n).measureReal_sum_le_le_exp_of_le_rateFunction
    (s := univ) (fun i _ ↦ (identDistrib_eval i).mgfDominatedOn) hν hx hr
  rw [card_univ, Fintype.card_fin] at h
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h

/-- For a closed set `F` with `I ≥ r` on `F`, the empirical mean of `n ≥ 1` samples lies in the
part of `F` above the mean with probability at most `exp (-(n r))`. -/
private lemma measure_mean_mem_inter_Ici_le [IsProbabilityMeasure ν] (hν : Integrable id ν)
    {F : Set ℝ} (hF : IsClosed F) {r : ℝ} (hr : ∀ y ∈ F, ENNReal.ofReal r ≤ rateFunction id ν y)
    {n : ℕ} (hn : 1 ≤ n) :
    (Measure.pi fun _ : Fin n ↦ ν) ((fun y : Fin n → ℝ ↦ (∑ i, y i) / n) ⁻¹'
      (F ∩ Ici (∫ y, y ∂ν))) ≤ ENNReal.ofReal (exp (-(n * r))) := by
  set m := ∫ y, y ∂ν
  rcases (F ∩ Ici m).eq_empty_or_nonempty with h | h
  · simp [h]
  have hB : BddBelow (F ∩ Ici m) := ⟨m, fun _ hy ↦ hy.2⟩
  have hmem := (hF.inter isClosed_Ici).csInf_mem h hB
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine (measure_mono fun y hy ↦ ?_).trans
    (measure_sum_ge_le hν n hmem.2 (hr _ hmem.1))
  rw [mem_ofPred_eq, ← le_div_iff₀' hn']
  exact csInf_le hB hy

/-- For a closed set `F` with `I ≥ r` on `F`, the empirical mean of `n ≥ 1` samples lies in the
part of `F` below the mean with probability at most `exp (-(n r))`. -/
private lemma measure_mean_mem_inter_Iic_le [IsProbabilityMeasure ν] (hν : Integrable id ν)
    {F : Set ℝ} (hF : IsClosed F) {r : ℝ} (hr : ∀ y ∈ F, ENNReal.ofReal r ≤ rateFunction id ν y)
    {n : ℕ} (hn : 1 ≤ n) :
    (Measure.pi fun _ : Fin n ↦ ν) ((fun y : Fin n → ℝ ↦ (∑ i, y i) / n) ⁻¹'
      (F ∩ Iic (∫ y, y ∂ν))) ≤ ENNReal.ofReal (exp (-(n * r))) := by
  set m := ∫ y, y ∂ν
  rcases (F ∩ Iic m).eq_empty_or_nonempty with h | h
  · simp [h]
  have hB : BddAbove (F ∩ Iic m) := ⟨m, fun _ hy ↦ hy.2⟩
  have hmem := (hF.inter isClosed_Iic).csSup_mem h hB
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine (measure_mono fun y hy ↦ ?_).trans
    (measure_sum_le_le hν n hmem.2 (hr _ hmem.1))
  rw [mem_ofPred_eq, ← div_le_iff₀' hn']
  exact le_csSup hB hy

/-- **The upper bound of Cramér's theorem.** For a probability measure `ν` on `ℝ` with a mean and
a closed set `F`, the laws `P n` of the empirical means of `n` independent samples of `ν` satisfy
`limsup_n (1 / n) log P n F ≤ -inf_F I`, with `I` the Cramér rate function of `ν`
[DZ98, Theorem 2.2.3]. -/
lemma limsup_log_measure_le_neg_iInf_rateFunction [IsProbabilityMeasure ν]
    (hν : Integrable id ν) {F : Set ℝ} (hF : IsClosed F) :
    limsup (fun n : ℕ ↦ ENNReal.log (((Measure.pi fun _ : Fin n ↦ ν).map
        fun y : Fin n → ℝ ↦ (∑ i, y i) / (n : ℝ)) F) / n) atTop ≤
      -(((⨅ x ∈ F, rateFunction id ν x : ℝ≥0∞)) : EReal) := by
  refine limsup_log_div_le_neg_of_le_mul_exp fun r hr ↦ ⟨2, ENNReal.ofNat_ne_top, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Measure.map_apply (measurable_mean n) hF.measurableSet]
  rcases le_or_gt r 0 with hr0 | hr0
  · -- For `r ≤ 0`, the bound is at least `1`.
    refine prob_le_one.trans ?_
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (exp (-(n * r))) :=
      ENNReal.one_le_ofReal.2 (one_le_exp (by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]))
    calc (1 : ℝ≥0∞) ≤ 2 * 1 := by norm_num
    _ ≤ 2 * ENNReal.ofReal (exp (-(n * r))) := by gcongr
  -- For `r > 0`, the rate function is at least `r` on `F`.
  have hrF : ∀ y ∈ F, ENNReal.ofReal r ≤ rateFunction id ν y := by
    intro y hy
    have hr' : ENNReal.ofReal r < ⨅ x ∈ F, rateFunction id ν x := by
      rwa [← EReal.coe_ennreal_lt_coe_ennreal_iff, EReal.coe_ennreal_ofReal,
        max_eq_left hr0.le]
    exact hr'.le.trans (iInf₂_le y hy)
  calc (Measure.pi fun _ : Fin n ↦ ν) ((fun y : Fin n → ℝ ↦ (∑ i, y i) / n) ⁻¹' F)
  _ ≤ (Measure.pi fun _ : Fin n ↦ ν) ((fun y : Fin n → ℝ ↦ (∑ i, y i) / n) ⁻¹'
        (F ∩ Ici (∫ y, y ∂ν))) + (Measure.pi fun _ : Fin n ↦ ν)
        ((fun y : Fin n → ℝ ↦ (∑ i, y i) / n) ⁻¹' (F ∩ Iic (∫ y, y ∂ν))) := by
    refine (measure_mono fun y hy ↦ ?_).trans (measure_union_le _ _)
    rcases le_total (∫ y, y ∂ν) ((∑ i, y i) / n) with h | h
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr ⟨hy, h⟩
  _ ≤ ENNReal.ofReal (exp (-(n * r))) + ENNReal.ofReal (exp (-(n * r))) :=
    add_le_add (measure_mean_mem_inter_Ici_le hν hF hrF hn)
      (measure_mean_mem_inter_Iic_le hν hF hrF hn)
  _ = 2 * ENNReal.ofReal (exp (-(n * r))) := (two_mul _).symm

/-! ### The lower bound at an atom -/

/-- The empirical mean of `n ≥ 1` samples is `x` with probability at least `ν{x}^n`. -/
private lemma pow_le_measure_mean_eq [IsProbabilityMeasure ν] {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    ν {x} ^ n ≤ (Measure.pi fun _ : Fin n ↦ ν)
      ((fun y : Fin n → ℝ ↦ (∑ i, y i) / (n : ℝ)) ⁻¹' {x}) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  calc ν {x} ^ n = (Measure.pi fun _ : Fin n ↦ ν) (Set.univ.pi fun _ ↦ {x}) := by
        rw [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  _ ≤ _ := by
    refine measure_mono fun y hy ↦ ?_
    have hy' : ∀ i, y i = x := fun i ↦ hy i (Set.mem_univ i)
    simp [hy', Finset.sum_const, Finset.card_univ, hn']

/-- If `ν{x} > 0` and `I(x) = -log ν{x}`, then for every `r > I(x)` and every set `U ∋ x`, the
empirical mean of `n` samples lies in `U` with probability at least `exp (-(n r))`, eventually. -/
private lemma eventually_ofReal_exp_le_of_atom [IsProbabilityMeasure ν] (hx0 : ν {x} ≠ 0)
    (hI : rateFunction id ν x = ENNReal.ofReal (-log (ν.real {ω | id ω = x}))) {U : Set ℝ}
    (hU : x ∈ U) {r : ℝ} (hr : (rateFunction id ν x : EReal) < r) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (exp (-(n * r))) ≤
      ((Measure.pi fun _ : Fin n ↦ ν).map fun y : Fin n → ℝ ↦ (∑ i, y i) / (n : ℝ)) U := by
  have h_set : {ω : ℝ | id ω = x} = {x} := by ext; simp
  rw [h_set] at hI
  set p := ν.real {x}
  have hp : 0 < p := ENNReal.toReal_pos hx0 (measure_ne_top _ _)
  have hp1 : p ≤ 1 := measureReal_le_one
  have hlog : -log p < r := by
    rw [hI, EReal.coe_ennreal_ofReal, max_eq_left (neg_nonneg.2 (log_nonpos hp.le hp1))] at hr
    exact_mod_cast hr
  filter_upwards [eventually_ge_atTop 1] with n hn
  calc ENNReal.ofReal (exp (-(n * r)))
  _ ≤ ENNReal.ofReal (p ^ n) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← exp_log hp, ← exp_nat_mul]
    exact exp_le_exp.2 (by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  _ = ν {x} ^ n := by rw [ENNReal.ofReal_pow hp.le, ofReal_measureReal]
  _ ≤ (Measure.pi fun _ : Fin n ↦ ν) ((fun y : Fin n → ℝ ↦ (∑ i, y i) / (n : ℝ)) ⁻¹' {x}) :=
    pow_le_measure_mean_eq hn x
  _ ≤ (Measure.pi fun _ : Fin n ↦ ν) ((fun y : Fin n → ℝ ↦ (∑ i, y i) / (n : ℝ)) ⁻¹' U) :=
    measure_mono (preimage_mono (singleton_subset_iff.2 hU))
  _ ≤ _ := Measure.le_map_apply (measurable_mean n).aemeasurable U

/-! ### The lower bound by exponential tilting -/

/-- A set of positive measure below `x` contains a set of positive measure within `[-k, k]` and at
distance `1 / (k + 1)` from `x`. -/
private lemma exists_measure_Icc_inter_Iic_ne_zero (hlt : ν (Iio x) ≠ 0) :
    ∃ k : ℕ, ν (Icc (-(k : ℝ)) k ∩ Iic (x - 1 / (k + 1))) ≠ 0 := by
  by_contra! h
  refine hlt (measure_mono_null (fun y (hy : y < x) ↦ ?_) (measure_iUnion_null h))
  obtain ⟨k₁, hk₁⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
  obtain ⟨k₂, hk₂⟩ := exists_nat_ge |y|
  refine mem_iUnion.2 ⟨max k₁ k₂, ⟨?_, ?_⟩, ?_⟩
  · have : (k₂ : ℝ) ≤ max k₁ k₂ := by exact_mod_cast le_max_right k₁ k₂
    linarith [neg_abs_le y]
  · have : (k₂ : ℝ) ≤ max k₁ k₂ := by exact_mod_cast le_max_right k₁ k₂
    linarith [le_abs_self y]
  · have : (k₁ : ℝ) ≤ max k₁ k₂ := by exact_mod_cast le_max_left k₁ k₂
    have h1 : 1 / ((max k₁ k₂ : ℕ) + 1 : ℝ) ≤ 1 / (k₁ + 1) := by
      gcongr
    rw [Set.mem_Iic]
    linarith

/-- A set of positive measure above `x` contains a set of positive measure within `[-k, k]` and at
distance `1 / (k + 1)` from `x`. -/
private lemma exists_measure_Icc_inter_Ici_ne_zero (hgt : ν (Ioi x) ≠ 0) :
    ∃ k : ℕ, ν (Icc (-(k : ℝ)) k ∩ Ici (x + 1 / (k + 1))) ≠ 0 := by
  by_contra! h
  refine hgt (measure_mono_null (fun y (hy : x < y) ↦ ?_) (measure_iUnion_null h))
  obtain ⟨k₁, hk₁⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
  obtain ⟨k₂, hk₂⟩ := exists_nat_ge |y|
  refine mem_iUnion.2 ⟨max k₁ k₂, ⟨?_, ?_⟩, ?_⟩
  · have : (k₂ : ℝ) ≤ max k₁ k₂ := by exact_mod_cast le_max_right k₁ k₂
    linarith [neg_abs_le y]
  · have : (k₂ : ℝ) ≤ max k₁ k₂ := by exact_mod_cast le_max_right k₁ k₂
    linarith [le_abs_self y]
  · have : (k₁ : ℝ) ≤ max k₁ k₂ := by exact_mod_cast le_max_left k₁ k₂
    have h1 : 1 / ((max k₁ k₂ : ℕ) + 1 : ℝ) ≤ 1 / (k₁ + 1) := by
      gcongr
    rw [Set.mem_Ici]
    linarith

/-- The sets of `exists_measure_Icc_inter_Iic_ne_zero` grow with `k`. -/
private lemma Icc_inter_Iic_subset {k k' : ℕ} (hk : k ≤ k') :
    Icc (-(k : ℝ)) k ∩ Iic (x - 1 / (k + 1)) ⊆ Icc (-(k' : ℝ)) k' ∩ Iic (x - 1 / (k' + 1)) := by
  have hk' : (k : ℝ) ≤ k' := by exact_mod_cast hk
  have h1 : 1 / ((k' : ℝ) + 1) ≤ 1 / (k + 1) := by gcongr
  rintro y ⟨⟨hy₁, hy₂⟩, hy₃⟩
  exact ⟨⟨by linarith, by linarith⟩, by rw [Set.mem_Iic] at hy₃ ⊢; linarith⟩

/-- The sets of `exists_measure_Icc_inter_Ici_ne_zero` grow with `k`. -/
private lemma Icc_inter_Ici_subset {k k' : ℕ} (hk : k ≤ k') :
    Icc (-(k : ℝ)) k ∩ Ici (x + 1 / (k + 1)) ⊆ Icc (-(k' : ℝ)) k' ∩ Ici (x + 1 / (k' + 1)) := by
  have hk' : (k : ℝ) ≤ k' := by exact_mod_cast hk
  have h1 : 1 / ((k' : ℝ) + 1) ≤ 1 / (k + 1) := by gcongr
  rintro y ⟨⟨hy₁, hy₂⟩, hy₃⟩
  exact ⟨⟨by linarith, by linarith⟩, by rw [Set.mem_Ici] at hy₃ ⊢; linarith⟩

/-- A positive radius `a` and a bound `M` such that `ν` charges `[-M, M] ∩ (-∞, x - a]` and
`[-M, M] ∩ [x + a, ∞)`, for `ν` charging both sides of `x`. -/
private lemma exists_measure_Icc_inter_ne_zero (hlt : ν (Iio x) ≠ 0) (hgt : ν (Ioi x) ≠ 0) :
    ∃ M : ℕ, ν (Icc (-(M : ℝ)) M ∩ Iic (x - 1 / (M + 1))) ≠ 0 ∧
      ν (Icc (-(M : ℝ)) M ∩ Ici (x + 1 / (M + 1))) ≠ 0 := by
  obtain ⟨k₁, hk₁⟩ := exists_measure_Icc_inter_Iic_ne_zero hlt
  obtain ⟨k₂, hk₂⟩ := exists_measure_Icc_inter_Ici_ne_zero hgt
  exact ⟨max k₁ k₂, fun h ↦ hk₁ (measure_mono_null (Icc_inter_Iic_subset (le_max_left _ _)) h),
    fun h ↦ hk₂ (measure_mono_null (Icc_inter_Ici_subset (le_max_right _ _)) h)⟩

/-- For a finite measure `ν` charging `[x + a, ∞)` and `(-∞, x - a]` with `a > 0`, the function
`t ↦ cgf id ν t - t x` tends to `∞` at `±∞`, when every exponential moment is finite. -/
private lemma tendsto_cgf_sub_mul_cocompact [IsFiniteMeasure ν]
    (h_int : ∀ t, Integrable (fun y ↦ exp (t * y)) ν) {a : ℝ} (ha : 0 < a)
    (hga : ν (Ici (x + a)) ≠ 0) (hla : ν (Iic (x - a)) ≠ 0) :
    Tendsto (fun t ↦ cgf id ν t - t * x) (cocompact ℝ) atTop := by
  have hqp : 0 < ν.real (Ici (x + a)) := ENNReal.toReal_pos hga (measure_ne_top _ _)
  have hqm : 0 < ν.real (Iic (x - a)) := ENNReal.toReal_pos hla (measure_ne_top _ _)
  rw [cocompact_eq_atBot_atTop, tendsto_sup]
  constructor
  · -- For `t ≤ 0`, `cgf t ≥ log ν(Iic (x - a)) + t (x - a)`.
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (log (ν.real (Iic (x - a))))
      (tendsto_neg_atBot_atTop.atTop_mul_const ha))
    filter_upwards [eventually_le_atBot 0] with t ht
    have h := measure_le_le_exp_mul_mgf (X := id) (μ := ν) (x - a) ht (h_int t)
    have h' : ν.real (Iic (x - a)) * exp (t * (x - a)) ≤ mgf id ν t := by
      have := mul_le_mul_of_nonneg_right h (exp_pos (t * (x - a))).le
      rwa [mul_comm (exp _), mul_assoc, ← exp_add, neg_mul, neg_add_cancel, exp_zero,
        mul_one] at this
    have hlog := log_le_log (by positivity) h'
    rw [log_mul hqm.ne' (exp_pos _).ne', log_exp] at hlog
    simp only [cgf]
    nlinarith
  · -- For `t ≥ 0`, `cgf t ≥ log ν(Ici (x + a)) + t (x + a)`.
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (log (ν.real (Ici (x + a))))
      (tendsto_id.atTop_mul_const ha))
    filter_upwards [eventually_ge_atTop 0] with t ht
    have h := measure_ge_le_exp_mul_mgf (X := id) (μ := ν) (x + a) ht (h_int t)
    have h' : ν.real (Ici (x + a)) * exp (t * (x + a)) ≤ mgf id ν t := by
      have := mul_le_mul_of_nonneg_right h (exp_pos (t * (x + a))).le
      rwa [mul_comm (exp _), mul_assoc, ← exp_add, neg_mul, neg_add_cancel, exp_zero,
        mul_one] at this
    have hlog := log_le_log (by positivity) h'
    rw [log_mul hqp.ne' (exp_pos _).ne', log_exp] at hlog
    simp only [cgf, id]
    nlinarith

/-- A probability measure with every exponential moment that charges both sides of `x` has an
exponential tilt of mean `x`: `x = Λ'(t)` for some `t`, with `Λ = cgf id ν`. -/
private lemma exists_deriv_cgf_eq [IsProbabilityMeasure ν]
    (h_int : ∀ t, Integrable (fun y ↦ exp (t * y)) ν) (hlt : ν (Iio x) ≠ 0)
    (hgt : ν (Ioi x) ≠ 0) :
    ∃ t, deriv (cgf id ν) t = x := by
  obtain ⟨M, hM₁, hM₂⟩ := exists_measure_Icc_inter_ne_zero hlt hgt
  have ha : (0 : ℝ) < 1 / (M + 1) := by positivity
  have hS : interior (integrableExpSet id ν) = Set.univ := by
    rw [show integrableExpSet id ν = Set.univ from Set.eq_univ_of_forall h_int, interior_univ]
  have h_cont : Continuous fun t ↦ cgf id ν t - t * x := by
    refine ((continuous_mgf h_int).log fun t ↦ (mgf_pos (h_int t)).ne').sub ?_
    fun_prop
  obtain ⟨t, ht⟩ := h_cont.exists_forall_le (tendsto_cgf_sub_mul_cocompact h_int ha
    (fun h ↦ hM₂ (measure_mono_null inter_subset_right h))
    (fun h ↦ hM₁ (measure_mono_null inter_subset_right h)))
  refine ⟨t, ?_⟩
  have hd : HasDerivAt (fun t ↦ cgf id ν t - t * x) (deriv (cgf id ν) t - x) t := by
    have hd := (analyticAt_cgf (hS ▸ mem_univ t)).differentiableAt.hasDerivAt
    exact hd.sub (hasDerivAt_mul_const x)
  have hmin : IsLocalMin (fun t ↦ cgf id ν t - t * x) t := Eventually.of_forall ht
  have := hmin.hasDerivAt_eq_zero hd
  linarith

/-- **Lower bound by exponential tilting**, for a probability measure `ν` with every exponential
moment that charges both sides of `x`: `I(x)` is finite and, for every `δ, ε > 0`, eventually the
sum of `n` samples is within `n δ` of `n x` with probability at least `exp (-(n (I(x) + ε)))`. -/
private lemma eventually_exp_le_measure_abs_sum_sub_le [IsProbabilityMeasure ν]
    (h_int : ∀ t, Integrable (fun y ↦ exp (t * y)) ν) (hlt : ν (Iio x) ≠ 0)
    (hgt : ν (Ioi x) ≠ 0) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    rateFunction id ν x ≠ ⊤ ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (exp (-(n * ((rateFunction id ν x).toReal + ε)))) ≤
        (Measure.pi fun _ : Fin n ↦ ν) {y | |∑ i, y i - n * x| ≤ n * δ} := by
  have hS : interior (integrableExpSet id ν) = Set.univ := by
    rw [show integrableExpSet id ν = Set.univ from Set.eq_univ_of_forall h_int, interior_univ]
  have hT : ∀ c, ¬ (id =ᵐ[ν] fun _ ↦ c) := by
    intro c hc
    rcases le_or_gt x c with hxc | hcx
    · exact hlt (measure_mono_null (fun y (hy : y < x) ↦ (hy.trans_le hxc).ne) (ae_iff.1 hc))
    · exact hgt (measure_mono_null (fun y (hy : x < y) ↦ (hcx.trans hy).ne') (ae_iff.1 hc))
  obtain ⟨t, ht⟩ := exists_deriv_cgf_eq h_int hlt hgt
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet id ν) := hS ▸ mem_univ 0
  have hx : x ∈ ν.expFamilyMeans id :=
    Measure.mem_expFamilyMeans_iff.2 ⟨t, hS ▸ mem_univ t, ht⟩
  have hμ₀ : deriv (cgf id ν) 0 ∈ ν.expFamilyMeans id := Measure.deriv_cgf_mem_expFamilyMeans h0
  have hmember : ν.expFamily id (ν.natParam id (deriv (cgf id ν) 0)) = ν := by
    rw [Measure.natParam_deriv_cgf hT h0, Measure.expFamily_zero]
  have hrate : rateFunction id ν x =
      ENNReal.ofReal (ν.expFamilyDiv id x (deriv (cgf id ν) 0)) := by
    have := rateFunction_expFamily_natParam hx hμ₀
    rwa [hmember] at this
  have hdiv := Measure.expFamilyDiv_nonneg hx hμ₀
  refine ⟨by rw [hrate]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [hrate, ENNReal.toReal_ofReal hdiv]
  set d := ν.expFamilyDiv id x (deriv (cgf id ν) 0)
  set η := ν.natParam id x - ν.natParam id (deriv (cgf id ν) 0)
  set V := Var[id; ν.expFamily id (ν.natParam id x)]
  -- A smaller radius `r'`, for which the cost `|η| r'` of the tilt is at most `ε / 2`.
  set r' := min δ (ε / (2 * (|η| + 1)))
  have hr' : 0 < r' := lt_min hδ (by positivity)
  have h_tr' : |η| * r' ≤ ε / 2 := by
    calc |η| * r' ≤ (|η| + 1) * (ε / (2 * (|η| + 1))) := by
          gcongr
          · linarith [abs_nonneg η]
          · exact min_le_right _ _
    _ = ε / 2 := by field_simp
  have h_exp : Tendsto (fun n : ℕ ↦ exp (-(n * (ε / 2)))) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)))
  have h_var : Tendsto (fun n : ℕ ↦ V / r' ^ 2 / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  filter_upwards [(tendsto_order.1 h_exp).2 (1 / 2) (by norm_num),
    (tendsto_order.1 h_var).2 (1 / 2) (by norm_num)] with n hn_exp hn_var
  have hY : ∀ i ∈ (univ : Finset (Fin n)), HasLaw (fun y : Fin n → ℝ ↦ y i)
      (ν.expFamily id (ν.natParam id (deriv (cgf id ν) 0))) (Measure.pi fun _ ↦ ν) :=
    fun i _ ↦ by
      rw [hmember]
      exact (measurePreserving_eval (fun _ ↦ ν) i).hasLaw
  have h_bound := (iIndepFun_eval (ν := ν) n).exp_mul_le_measureReal_abs_sum_sub_le_of_hasLaw
    hY hμ₀ hx hr'
  simp only [card_univ, Fintype.card_fin, id] at h_bound
  have h_one_sub : 1 / 2 ≤ 1 - V / (n * r' ^ 2) := by
    rw [mul_comm, ← div_div]
    linarith
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  calc exp (-(n * (d + ε)))
  _ = exp (-(n * (d + ε / 2))) * exp (-(n * (ε / 2))) := by
    rw [← exp_add]
    congr 1
    ring
  _ ≤ exp (-(n * (d + |η| * r'))) * (1 - V / (n * r' ^ 2)) := by
    gcongr
    linarith
  _ ≤ (Measure.pi fun _ : Fin n ↦ ν).real {y | |∑ i, y i - n * x| ≤ n * r'} := h_bound
  _ ≤ (Measure.pi fun _ : Fin n ↦ ν).real {y | |∑ i, y i - n * x| ≤ n * δ} := by
    refine measureReal_mono fun y hy ↦ ?_
    simp only [mem_ofPred_eq] at hy ⊢
    exact hy.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) n.cast_nonneg)

/-! ### Truncation -/

/-- The function `t ↦ ∫_{[-M, M]} exp (t (y - x)) dν(y)` is continuous. -/
private lemma continuous_setIntegral_exp [IsFiniteMeasure ν] (M : ℝ) :
    Continuous fun t ↦ ∫ y in Icc (-M) M, exp (t * (y - x)) ∂ν := by
  have h_int (t : ℝ) : Integrable (fun y ↦ exp (t * y)) (ν.restrict (Icc (-M) M)) :=
    (continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.integrableOn_compact
      isCompact_Icc
  have h_eq : (fun t ↦ ∫ y in Icc (-M) M, exp (t * (y - x)) ∂ν) =
      fun t ↦ exp (-(t * x)) * mgf id (ν.restrict (Icc (-M) M)) t := by
    ext t
    rw [mgf, ← integral_const_mul]
    congr 1
    ext y
    rw [← exp_add]
    congr 1
    simp only [id]
    ring
  rw [h_eq]
  exact (continuous_exp.comp (continuous_id.mul continuous_const).neg).mul (continuous_mgf h_int)

/-- `∫_{[-M, M]} exp (t (y - x)) dν(y)` is at least `exp (t a) ν([-M₀, M₀] ∩ [x + a, ∞))` for
`t ≥ 0` and `M ≥ M₀`. -/
private lemma exp_mul_le_setIntegral_exp_of_nonneg [IsFiniteMeasure ν] {M₀ M a t : ℝ}
    (hM : M₀ ≤ M) (ht : 0 ≤ t) :
    exp (t * a) * ν.real (Icc (-M₀) M₀ ∩ Ici (x + a)) ≤
      ∫ y in Icc (-M) M, exp (t * (y - x)) ∂ν := by
  have h_int : IntegrableOn (fun y ↦ exp (t * (y - x))) (Icc (-M) M) ν := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    fun_prop
  have h_sub : Icc (-M₀) M₀ ∩ Ici (x + a) ⊆ Icc (-M) M :=
    fun y hy ↦ ⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩
  calc exp (t * a) * ν.real (Icc (-M₀) M₀ ∩ Ici (x + a))
  _ = ∫ _ in Icc (-M₀) M₀ ∩ Ici (x + a), exp (t * a) ∂ν := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]
  _ ≤ ∫ y in Icc (-M₀) M₀ ∩ Ici (x + a), exp (t * (y - x)) ∂ν := by
    refine setIntegral_mono_on (integrableOn_const (measure_ne_top _ _))
      (h_int.mono_set h_sub) (measurableSet_Icc.inter measurableSet_Ici) fun y hy ↦ ?_
    exact exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [Set.mem_Ici.1 hy.2]) ht)
  _ ≤ ∫ y in Icc (-M) M, exp (t * (y - x)) ∂ν :=
    setIntegral_mono_set h_int (Eventually.of_forall fun _ ↦ (exp_pos _).le)
      (Eventually.of_forall h_sub)

/-- `∫_{[-M, M]} exp (t (y - x)) dν(y)` is at least `exp (-(t a)) ν([-M₀, M₀] ∩ (-∞, x - a])` for
`t ≤ 0` and `M ≥ M₀`. -/
private lemma exp_mul_le_setIntegral_exp_of_nonpos [IsFiniteMeasure ν] {M₀ M a t : ℝ}
    (hM : M₀ ≤ M) (ht : t ≤ 0) :
    exp (-(t * a)) * ν.real (Icc (-M₀) M₀ ∩ Iic (x - a)) ≤
      ∫ y in Icc (-M) M, exp (t * (y - x)) ∂ν := by
  have h_int : IntegrableOn (fun y ↦ exp (t * (y - x))) (Icc (-M) M) ν := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    fun_prop
  have h_sub : Icc (-M₀) M₀ ∩ Iic (x - a) ⊆ Icc (-M) M :=
    fun y hy ↦ ⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩
  calc exp (-(t * a)) * ν.real (Icc (-M₀) M₀ ∩ Iic (x - a))
  _ = ∫ _ in Icc (-M₀) M₀ ∩ Iic (x - a), exp (-(t * a)) ∂ν := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]
  _ ≤ ∫ y in Icc (-M₀) M₀ ∩ Iic (x - a), exp (t * (y - x)) ∂ν := by
    refine setIntegral_mono_on (integrableOn_const (measure_ne_top _ _))
      (h_int.mono_set h_sub) (measurableSet_Icc.inter measurableSet_Iic) fun y hy ↦ ?_
    exact exp_le_exp.2 (by nlinarith [Set.mem_Iic.1 hy.2])
  _ ≤ ∫ y in Icc (-M) M, exp (t * (y - x)) ∂ν :=
    setIntegral_mono_set h_int (Eventually.of_forall fun _ ↦ (exp_pos _).le)
      (Eventually.of_forall h_sub)

/-- `∫ exp (t (y - x)) dν(y) ≥ exp (-I(x))` for every `t`, as an `ℝ≥0∞`-valued integral. -/
private lemma ofReal_exp_le_lintegral_exp [IsProbabilityMeasure ν]
    (hI : rateFunction id ν x ≠ ⊤) (t : ℝ) :
    ENNReal.ofReal (exp (-(rateFunction id ν x).toReal)) ≤
      ∫⁻ y, ENNReal.ofReal (exp (t * (y - x))) ∂ν := by
  by_cases ht : Integrable (fun y ↦ exp (t * y)) ν
  · have h_eq : ∫ y, exp (t * (y - x)) ∂ν = exp (cgf id ν t - t * x) := by
      rw [exp_sub, exp_cgf (X := id) ht, mgf, div_eq_mul_inv, ← exp_neg, ← integral_mul_const]
      congr 1
      ext y
      rw [← exp_add]
      congr 1
      simp only [id]
      ring
    have h_int : Integrable (fun y ↦ exp (t * (y - x))) ν := by
      refine (ht.mul_const (exp (-(t * x)))).congr (Eventually.of_forall fun y ↦ ?_)
      dsimp only
      rw [← exp_add]
      congr 1
      ring
    rw [← ofReal_integral_eq_lintegral_ofReal h_int
      (Eventually.of_forall fun _ ↦ (exp_pos _).le), h_eq]
    refine ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_)
    have h := (ENNReal.ofReal_le_iff_le_toReal hI).1 (ofReal_le_rateFunction (X := id) ht x)
    linarith
  · have h_top : ∫⁻ y, ENNReal.ofReal (exp (t * (y - x))) ∂ν = ⊤ := by
      by_contra h
      refine ht ?_
      have h_int : Integrable (fun y ↦ exp (t * (y - x))) ν :=
        ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal
          (Eventually.of_forall fun _ ↦ (exp_pos _).le)).2 (lt_top_iff_ne_top.2 h)⟩
      refine (h_int.mul_const (exp (t * x))).congr (Eventually.of_forall fun y ↦ ?_)
      dsimp only
      rw [← exp_add]
      congr 1
      ring
    rw [h_top]
    exact le_top

/-- **Convergence of the truncated rates.** For a level `x` of finite rate, with `ν` charging both
sides of `x`, and `ε > 0`, there is `M` such that `ν` charges both sides of `x` within `[-M, M]`
and `∫_{[-M, M]} exp (t (y - x)) dν(y) ≥ exp (-(I(x) + ε))` for every `t`. -/
private lemma exists_le_setIntegral_exp [IsProbabilityMeasure ν] (hI : rateFunction id ν x ≠ ⊤)
    (hlt : ν (Iio x) ≠ 0) (hgt : ν (Ioi x) ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ν (Icc (-(M : ℝ)) M ∩ Iio x) ≠ 0 ∧ ν (Icc (-(M : ℝ)) M ∩ Ioi x) ≠ 0 ∧
      ∀ t, exp (-((rateFunction id ν x).toReal + ε)) ≤
        ∫ y in Icc (-(M : ℝ)) M, exp (t * (y - x)) ∂ν := by
  set I := (rateFunction id ν x).toReal
  set c := exp (-(I + ε))
  obtain ⟨M₀, hM₁, hM₂⟩ := exists_measure_Icc_inter_ne_zero hlt hgt
  set a : ℝ := 1 / (M₀ + 1)
  have ha : 0 < a := by positivity
  set q := min (ν.real (Icc (-(M₀ : ℝ)) M₀ ∩ Iic (x - a)))
    (ν.real (Icc (-(M₀ : ℝ)) M₀ ∩ Ici (x + a)))
  have hq : 0 < q := lt_min (ENNReal.toReal_pos hM₁ (measure_ne_top _ _))
    (ENNReal.toReal_pos hM₂ (measure_ne_top _ _))
  -- The sets of positive measure on both sides of `x`, for every `M ≥ M₀`.
  have h_sides (M : ℕ) (hM : M₀ ≤ M) :
      ν (Icc (-(M : ℝ)) M ∩ Iio x) ≠ 0 ∧ ν (Icc (-(M : ℝ)) M ∩ Ioi x) ≠ 0 := by
    have hM' : (M₀ : ℝ) ≤ M := by exact_mod_cast hM
    refine ⟨fun h ↦ hM₁ (measure_mono_null (fun y hy ↦ ?_) h),
      fun h ↦ hM₂ (measure_mono_null (fun y hy ↦ ?_) h)⟩
    · exact ⟨⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩,
        Set.mem_Iio.2 (by linarith [Set.mem_Iic.1 hy.2])⟩
    · exact ⟨⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩,
        by rw [Set.mem_Ioi]; linarith [Set.mem_Ici.1 hy.2]⟩
  -- Coercivity: outside `[-A, A]`, the truncated integrals exceed `c` for every `M ≥ M₀`.
  obtain ⟨A, hA⟩ := ((tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const ha)).eventually_ge_atTop
    (c / q)).exists_forall_of_atTop
  set A' := max A 0
  have h_coercive (M : ℕ) (hM : M₀ ≤ M) (t : ℝ)
      (ht : ∫ y in Icc (-(M : ℝ)) M, exp (t * (y - x)) ∂ν < c) : t ∈ Icc (-A') A' := by
    have hM' : (M₀ : ℝ) ≤ M := by exact_mod_cast hM
    by_contra ht'
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht'
    rcases ht' with ht' | ht'
    · have h1 := hA (-t) (by linarith [le_max_left A 0])
      simp only [Function.comp_apply, id, neg_mul] at h1
      have h2 := exp_mul_le_setIntegral_exp_of_nonpos (ν := ν) (x := x) (a := a) hM'
        (show t ≤ 0 by linarith [le_max_right A 0])
      have h3 : c ≤ exp (-(t * a)) * q := (div_le_iff₀ hq).1 h1
      have h4 : exp (-(t * a)) * q ≤ exp (-(t * a)) *
          ν.real (Icc (-(M₀ : ℝ)) M₀ ∩ Iic (x - a)) := by
        gcongr
        exact min_le_left _ _
      linarith
    · have h1 := hA t (by linarith [le_max_left A 0])
      simp only [Function.comp_apply, id] at h1
      have h2 := exp_mul_le_setIntegral_exp_of_nonneg (ν := ν) (x := x) (a := a) hM'
        (show 0 ≤ t by linarith [le_max_right A 0])
      have h3 : c ≤ exp (t * a) * q := (div_le_iff₀ hq).1 h1
      have h4 : exp (t * a) * q ≤ exp (t * a) * ν.real (Icc (-(M₀ : ℝ)) M₀ ∩ Ici (x + a)) := by
        gcongr
        exact min_le_right _ _
      linarith
  -- The truncated integrals increase with `M`.
  have h_int (M : ℝ) (t : ℝ) : IntegrableOn (fun y ↦ exp (t * (y - x))) (Icc (-M) M) ν := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    fun_prop
  have h_Icc_mono : Monotone fun k : ℕ ↦ Icc (-((M₀ + k : ℕ) : ℝ)) (M₀ + k : ℕ) := by
    intro k k' hk
    have : ((M₀ + k : ℕ) : ℝ) ≤ (M₀ + k' : ℕ) := by exact_mod_cast Nat.add_le_add_left hk M₀
    exact Icc_subset_Icc (neg_le_neg this) this
  by_contra! h
  -- The nested compact sets of the parameters at which the truncated integral is at most `c`.
  set K : ℕ → Set ℝ := fun k ↦ Icc (-A') A' ∩
    {t | ∫ y in Icc (-((M₀ + k : ℕ) : ℝ)) (M₀ + k : ℕ), exp (t * (y - x)) ∂ν ≤ c}
  have hK_closed (k : ℕ) : IsClosed (K k) :=
    isClosed_Icc.inter (isClosed_le (continuous_setIntegral_exp _) continuous_const)
  have hK_ne (k : ℕ) : (K k).Nonempty := by
    obtain ⟨t, ht⟩ := h (M₀ + k) (h_sides _ le_self_add).1 (h_sides _ le_self_add).2
    exact ⟨t, h_coercive _ le_self_add t ht, ht.le⟩
  have hK_anti (k : ℕ) : K (k + 1) ⊆ K k := fun t ht ↦ ⟨ht.1, le_trans
    (setIntegral_mono_set (h_int _ t) (Eventually.of_forall fun _ ↦ (exp_pos _).le)
      (Eventually.of_forall (h_Icc_mono (Nat.le_succ k)))) ht.2⟩
  obtain ⟨t₀, ht₀⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hK_anti
    hK_ne (isCompact_Icc.of_isClosed_subset (hK_closed 0) inter_subset_left) hK_closed
  -- By monotone convergence, `∫ exp (t₀ (y - x)) dν(y) ≤ c < exp (-I(x))`, a contradiction.
  set f : ℝ → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (exp (t₀ * (y - x)))
  have hG (k : ℕ) : (ν.withDensity f) (Icc (-((M₀ + k : ℕ) : ℝ)) (M₀ + k : ℕ)) ≤
      ENNReal.ofReal c := by
    rw [withDensity_apply _ measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal (h_int _ t₀)
      (Eventually.of_forall fun _ ↦ (exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (mem_iInter.1 ht₀ k).2
  have h_union : ⋃ k : ℕ, Icc (-((M₀ + k : ℕ) : ℝ)) (M₀ + k : ℕ) = Set.univ := by
    refine eq_univ_of_forall fun y ↦ mem_iUnion.2 ?_
    obtain ⟨k, hk⟩ := exists_nat_ge |y|
    have : (k : ℝ) ≤ (M₀ + k : ℕ) := by exact_mod_cast Nat.le_add_left k M₀
    exact ⟨k, by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  have h_tend := tendsto_measure_iUnion_atTop (μ := ν.withDensity f) h_Icc_mono
  rw [h_union, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h_tend
  have h_le : ∫⁻ y, f y ∂ν ≤ ENNReal.ofReal c := le_of_tendsto' h_tend hG
  have h_lt : ENNReal.ofReal c < ENNReal.ofReal (exp (-I)) :=
    (ENNReal.ofReal_lt_ofReal_iff (exp_pos _)).2 (exp_lt_exp.2 (by linarith))
  exact (h_lt.trans_le ((ofReal_exp_le_lintegral_exp hI t₀).trans h_le)).false

/-- **The lower bound by truncation**, at a level `x` of finite rate with `ν` charging both sides
of `x`: for `δ > 0` and `r > I(x)`, eventually the sum of `n` samples of `ν` is within `n δ` of
`n x` with probability at least `exp (-(n r))`. The normalized truncation
`ν_M = ν([-M, M])⁻¹ ν|_{[-M, M]}` satisfies the bound of
`eventually_exp_le_measure_abs_sum_sub_le`, and `ν^n ≥ ν([-M, M])^n ν_M^n`. -/
private lemma eventually_ofReal_exp_le_of_truncation [IsProbabilityMeasure ν]
    (hI : rateFunction id ν x ≠ ⊤) (hlt : ν (Iio x) ≠ 0) (hgt : ν (Ioi x) ≠ 0) {δ r : ℝ}
    (hδ : 0 < δ) (hr : (rateFunction id ν x).toReal < r) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (exp (-(n * r))) ≤
      (Measure.pi fun _ : Fin n ↦ ν) {y | |∑ i, y i - n * x| ≤ n * δ} := by
  set I := (rateFunction id ν x).toReal
  set ε := (r - I) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  obtain ⟨M, hM₁, hM₂, hM⟩ := exists_le_setIntegral_exp hI hlt hgt hε
  set B := Icc (-(M : ℝ)) M
  have hB0 : ν B ≠ 0 := fun h ↦ hM₁ (measure_mono_null inter_subset_left h)
  have hBtop : ν B ≠ ⊤ := measure_ne_top _ _
  set p := ν.real B
  have hp : 0 < p := ENNReal.toReal_pos hB0 hBtop
  set ν' := (ν B)⁻¹ • ν.restrict B
  have hν'_apply (s : Set ℝ) (hs : MeasurableSet s) : ν' s = (ν B)⁻¹ * ν (s ∩ B) := by
    simp [ν', Measure.restrict_apply hs]
  have : IsProbabilityMeasure ν' := ⟨by
    rw [hν'_apply _ MeasurableSet.univ, univ_inter, ENNReal.inv_mul_cancel hB0 hBtop]⟩
  have h_int' (t : ℝ) : Integrable (fun y ↦ exp (t * y)) ν' :=
    ((continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.integrableOn_compact
      isCompact_Icc).smul_measure (ENNReal.inv_ne_top.2 hB0)
  have hlt' : ν' (Iio x) ≠ 0 := by
    rw [hν'_apply _ measurableSet_Iio, inter_comm]
    exact mul_ne_zero (ENNReal.inv_ne_zero.2 hBtop) hM₁
  have hgt' : ν' (Ioi x) ≠ 0 := by
    rw [hν'_apply _ measurableSet_Ioi, inter_comm]
    exact mul_ne_zero (ENNReal.inv_ne_zero.2 hBtop) hM₂
  -- The rate function of the truncation at `x` is at most `log p + I(x) + ε`.
  have h_rate : (rateFunction id ν' x).toReal ≤ log p + I + ε := by
    have h_nonneg : 0 ≤ log p + I + ε := by
      have h0 := hM 0
      simp only [zero_mul, exp_zero, setIntegral_const, smul_eq_mul, mul_one] at h0
      have := log_le_log (exp_pos _) h0
      rw [log_exp] at this
      linarith
    refine ENNReal.toReal_le_of_le_ofReal h_nonneg
      (rateFunction_le_iff.2 fun t _ ↦ ENNReal.ofReal_le_ofReal ?_)
    have hG := hM t
    have hGpos : 0 < ∫ y in B, exp (t * (y - x)) ∂ν := (exp_pos _).trans_le hG
    have h_mgf : mgf id ν' t = p⁻¹ * (exp (t * x) * ∫ y in B, exp (t * (y - x)) ∂ν) := by
      have h_eq : (fun y ↦ exp (t * id y)) = fun y ↦ exp (t * x) * exp (t * (y - x)) := by
        ext y
        rw [← exp_add]
        congr 1
        simp only [id]
        ring
      rw [mgf, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv, h_eq, integral_const_mul,
        ← measureReal_def]
    have hlog := log_le_log (exp_pos _) hG
    rw [log_exp] at hlog
    rw [cgf, h_mgf, log_mul (inv_pos.2 hp).ne' (by positivity), log_mul (exp_pos _).ne'
      hGpos.ne', log_inv, log_exp]
    linarith
  obtain ⟨-, h_ev⟩ := eventually_exp_le_measure_abs_sum_sub_le h_int' hlt' hgt' hδ hε
  filter_upwards [h_ev] with n hn
  set A := {y : Fin n → ℝ | |∑ i, y i - n * x| ≤ n * δ}
  -- `ν^n ≥ ν(B)^n ν'^n`, since `ν|_B = ν(B) ν'`.
  have h_restrict : Measure.pi (fun _ : Fin n ↦ ν.restrict B) =
      ν B ^ n • Measure.pi (fun _ : Fin n ↦ ν') := by
    refine Measure.pi_eq fun s hs ↦ ?_
    have hpow : ν B ^ n = ∏ _i : Fin n, ν B := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [smul_apply, Measure.pi_pi, smul_eq_mul, hpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [hν'_apply _ (hs i), Measure.restrict_apply (hs i), ← mul_assoc,
      ENNReal.mul_inv_cancel hB0 hBtop, one_mul]
  have h_pi : ν B ^ n * (Measure.pi fun _ : Fin n ↦ ν') A ≤ (Measure.pi fun _ : Fin n ↦ ν) A := by
    calc ν B ^ n * (Measure.pi fun _ : Fin n ↦ ν') A
    _ = ((Measure.pi fun _ : Fin n ↦ ν).restrict (Set.univ.pi fun _ ↦ B)) A := by
      rw [Measure.restrict_pi_pi, h_restrict, smul_apply, smul_eq_mul]
    _ ≤ (Measure.pi fun _ : Fin n ↦ ν) A := Measure.restrict_apply_le _ _
  refine le_trans ?_ h_pi
  calc ENNReal.ofReal (exp (-(n * r)))
  _ ≤ ENNReal.ofReal (p ^ n) *
      ENNReal.ofReal (exp (-(n * ((rateFunction id ν' x).toReal + ε)))) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← exp_log hp, ← exp_nat_mul, ← exp_add]
    refine exp_le_exp.2 ?_
    have hr2 : r = I + 2 * ε := by simp only [ε]; ring
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  _ ≤ ν B ^ n * (Measure.pi fun _ : Fin n ↦ ν') A := by
    rw [ENNReal.ofReal_pow hp.le, ofReal_measureReal]
    gcongr

/-- The event that the sum of `n ≥ 1` samples is within `n δ` of `n x` is the event that their
empirical mean is within `δ` of `x`. -/
private lemma setOf_abs_sum_sub_le_subset {n : ℕ} (hn : 1 ≤ n) (x δ : ℝ) :
    {y : Fin n → ℝ | |∑ i, y i - n * x| ≤ n * δ} ⊆
      (fun y : Fin n → ℝ ↦ (∑ i, y i) / (n : ℝ)) ⁻¹' Metric.closedBall x δ := by
  intro y hy
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq]
  rw [show (∑ i, y i) / n - x = (∑ i, y i - n * x) / n by field_simp, abs_div, abs_of_pos hn',
    div_le_iff₀ hn']
  simpa [mul_comm] using hy

/-- **The lower bound of Cramér's theorem.** For every probability measure `ν` on `ℝ`, every level
`x` and every neighbourhood `U` of `x`, the laws `P n` of the empirical means of `n` independent
samples of `ν` satisfy `-I(x) ≤ liminf_n (1 / n) log P n U`, with `I` the Cramér rate function of
`ν` [DZ98, Theorem 2.2.3]. -/
lemma neg_rateFunction_le_liminf_log_measure [IsProbabilityMeasure ν] {U : Set ℝ}
    (hU : U ∈ 𝓝 x) :
    -(rateFunction id ν x : EReal) ≤ liminf (fun n : ℕ ↦ ENNReal.log
      (((Measure.pi fun _ : Fin n ↦ ν).map fun y : Fin n → ℝ ↦ (∑ i, y i) / (n : ℝ)) U) / n)
      atTop := by
  by_cases hI : rateFunction id ν x = ⊤
  · simp [hI]
  refine neg_le_liminf_log_div_of_mul_exp_le fun r hr ↦ ⟨1, one_ne_zero, ?_⟩
  simp only [one_mul]
  by_cases hgt : ν (Ioi x) = 0
  · -- `ν` gives no mass above `x`.
    have h : ∀ᵐ y ∂ν, id y ≤ x := by
      rw [ae_iff]
      convert hgt using 2
      ext
      simp
    have hx0 : ν {x} ≠ 0 := fun h0 ↦
      hI (rateFunction_eq_top_of_ae_le aemeasurable_id h (by simpa using h0))
    exact eventually_ofReal_exp_le_of_atom hx0
      (rateFunction_eq_ofReal_neg_log_measureReal_of_ae_le aemeasurable_id h (by simpa using hx0))
      (mem_of_mem_nhds hU) hr
  by_cases hlt : ν (Iio x) = 0
  · -- `ν` gives no mass below `x`.
    have h : ∀ᵐ y ∂ν, x ≤ id y := by
      rw [ae_iff]
      convert hlt using 2
      ext
      simp
    have hx0 : ν {x} ≠ 0 := fun h0 ↦
      hI (rateFunction_eq_top_of_ae_ge aemeasurable_id h (by simpa using h0))
    exact eventually_ofReal_exp_le_of_atom hx0
      (rateFunction_eq_ofReal_neg_log_measureReal_of_ae_ge aemeasurable_id h (by simpa using hx0))
      (mem_of_mem_nhds hU) hr
  -- `ν` charges both sides of `x`: truncation and tilting.
  obtain ⟨δ, hδ, hδU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hU
  have hr' : (rateFunction id ν x).toReal < r := by
    rw [← EReal.coe_lt_coe_iff, EReal.coe_ennreal_toReal hI]
    exact hr
  filter_upwards [eventually_ofReal_exp_le_of_truncation hI hlt hgt hδ hr',
    eventually_ge_atTop 1] with n hn hn1
  refine hn.trans ((measure_mono ((setOf_abs_sum_sub_le_subset hn1 x δ).trans
    (preimage_mono hδU))).trans (Measure.le_map_apply (measurable_mean n).aemeasurable U))

/-! ### Cramér's theorem -/

/-- **Cramér's theorem** [DZ98, Theorem 2.2.3]. For a probability measure `ν` on `ℝ` with a mean,
the laws of the empirical means `(∑ i < n, X i) / n` of `n` independent samples of `ν` satisfy the
large deviation principle with speed `n` and the Cramér rate function
`I(x) = sup_t (t x - log E_ν[exp (t X)])` of `ν`. -/
theorem isLDP_cramer [IsProbabilityMeasure ν] (hν : Integrable id ν) :
    IsLDP (fun n ↦ (Measure.pi fun _ : Fin n ↦ ν).map fun y : Fin n → ℝ ↦ (∑ i, y i) / (n : ℝ))
      (rateFunction id ν) :=
  .of_isClosed_of_mem_nhds (lowerSemicontinuous_rateFunction id ν)
    (fun _ hF ↦ limsup_log_measure_le_neg_iInf_rateFunction hν hF)
    (fun _ _ hU ↦ neg_rateFunction_le_liminf_log_measure hU)

/-! ### Goodness of the rate function -/

/-- **The Cramér rate function is a good rate function** when the cumulant generating function is
finite on a neighbourhood of `0` [DZ98, Lemma 2.2.5]. -/
lemma isGoodRateFunction_rateFunction {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : Ω → ℝ}
    {P : Measure Ω} (h : 0 ∈ interior (integrableExpSet X P)) :
    IsGoodRateFunction (rateFunction X P) := by
  refine ⟨lowerSemicontinuous_rateFunction X P, fun c ↦ ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 h)
  have hε2 : 0 < ε / 2 := by positivity
  have ht : ε / 2 ∈ integrableExpSet X P := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hε2]
    linarith
  have ht' : -(ε / 2) ∈ integrableExpSet X P := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right, norm_neg, Real.norm_eq_abs, abs_of_pos hε2]
    linarith
  refine (isCompact_Icc (a := -((c + cgf X P (-(ε / 2))) / (ε / 2)))
    (b := (c + cgf X P (ε / 2)) / (ε / 2))).of_isClosed_subset
    ((lowerSemicontinuous_rateFunction X P).isClosed_preimage _) fun x hx ↦ ?_
  have h₁ := (ofReal_le_rateFunction ht x).trans hx
  have h₂ := (ofReal_le_rateFunction ht' x).trans hx
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff c.coe_nonneg] at h₁ h₂
  constructor
  · rw [neg_le, le_div_iff₀ hε2]
    linarith
  · rw [le_div_iff₀ hε2]
    linarith

/-! ### Statistics of samples and independent sequences -/

/-- The law of the empirical mean of a statistic `X` of `n` independent samples of `P` is the law
of the empirical mean of `n` independent samples of the law of `X`. -/
private lemma map_pi_sum_comp_div {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : AEMeasurable X P) (n : ℕ) :
    (Measure.pi fun _ : Fin n ↦ P).map (fun y : Fin n → Ω ↦ (∑ i, X (y i)) / (n : ℝ)) =
      (Measure.pi fun _ : Fin n ↦ P.map X).map fun y : Fin n → ℝ ↦ (∑ i, y i) / (n : ℝ) := by
  have := (Measure.isProbabilityMeasure_map_iff hX).2 ‹_›
  have hf : AEMeasurable (fun (y : Fin n → Ω) (i : Fin n) ↦ X (y i)) (Measure.pi fun _ ↦ P) :=
    .of_eval fun i ↦ hX.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ i)
  rw [← Measure.pi_map_pi fun _ ↦ hX,
    AEMeasurable.map_map_of_aemeasurable (measurable_mean n).aemeasurable hf]
  rfl

/-- **Cramér's theorem for independent identically distributed random variables**
[DZ98, Theorem 2.2.3]. For independent real random variables `X i`, `i : ℕ`, distributed as `X 0`,
with `X 0` integrable, the laws of the empirical means `(∑ i < n, X i) / n` satisfy the large
deviation principle with speed `n` and the Cramér rate function of `X 0`. -/
theorem isLDP_cramer_of_iIndepFun {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hint : Integrable (X 0) P)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    IsLDP (fun n ↦ P.map fun ω ↦ (∑ i ∈ range n, X i ω) / (n : ℝ)) (rateFunction (X 0) P) := by
  have hX0 : HasLaw (X 0) (P.map (X 0)) P := ⟨hint.aemeasurable, rfl⟩
  have := hX0.isProbabilityMeasure_iff.1 ‹_›
  have h_law (n : ℕ) : P.map (fun ω ↦ (∑ i ∈ range n, X i ω) / (n : ℝ)) =
      (Measure.pi fun _ : Fin n ↦ P.map (X 0)).map fun y : Fin n → ℝ ↦ (∑ i, y i) / (n : ℝ) := by
    have h_pi : HasLaw (fun ω (i : Fin n) ↦ X i ω) (Measure.pi fun _ ↦ P.map (X 0)) P :=
      (hindep.precomp Fin.val_injective).hasLaw_pi fun i ↦ (hident i).symm.hasLaw hX0
    rw [← h_pi.map_eq, AEMeasurable.map_map_of_aemeasurable (measurable_mean n).aemeasurable
      h_pi.aemeasurable]
    congr 1
    ext ω
    simp [Fin.sum_univ_eq_sum_range (fun i ↦ X i ω) n]
  simp_rw [h_law]
  rw [(hX0.identDistrib HasLaw.id).rateFunction_eq]
  exact isLDP_cramer ((integrable_map_measure aestronglyMeasurable_id hint.aemeasurable).2 hint)

end LMLExplore

/-! ### Exponential families -/

namespace MeasureTheory.Measure

open LMLExplore

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {μ : ℝ}

/-- **Cramér's theorem for exponential families.** For a nonzero measure `ρ` on a measurable
space `𝓧`, a statistic `T` and a mean `μ` of the exponential family of `ρ` and `T`, the laws of
the empirical means `(∑ i < n, T (Y i)) / n` of the statistic of `n` independent samples `Y i` of
the member of mean `μ` satisfy the large deviation principle with speed `n` and rate function
the extended divergence `x ↦ dbar(x, μ)` (`Measure.expFamilyRate`), which is the divergence
`d(x, μ)` at the means `x` of the family [D23, Lemma 11]. -/
theorem isLDP_cramer_expFamily [NeZero ρ] (hμ : μ ∈ ρ.expFamilyMeans T) :
    IsLDP (fun n ↦ (Measure.pi fun _ : Fin n ↦ ρ.expFamily T (ρ.natParam T μ)).map
      fun y : Fin n → 𝓧 ↦ (∑ i, T (y i)) / (n : ℝ)) (fun x ↦ ρ.expFamilyRate T x μ) := by
  have hη := natParam_mem_interior_integrableExpSet hμ
  have := isProbabilityMeasure_expFamily (interior_subset hη)
  have hT := integrable_expFamily hη
  have hlaw : HasLaw T ((ρ.expFamily T (ρ.natParam T μ)).map T) (ρ.expFamily T (ρ.natParam T μ)) :=
    ⟨hT.aemeasurable, rfl⟩
  simp_rw [map_pi_sum_comp_div hT.aemeasurable, expFamilyRate_def,
    (hlaw.identDistrib HasLaw.id).rateFunction_eq]
  exact isLDP_cramer ((integrable_map_measure aestronglyMeasurable_id hT.aemeasurable).2 hT)

/-- **The extended divergence of an exponential family is a good rate function** in its first
argument: for a mean `μ` of the exponential family of `ρ` and `T`, the function
`x ↦ dbar(x, μ)` (`Measure.expFamilyRate`) has compact sublevel sets. -/
theorem isGoodRateFunction_expFamilyRate_left (hμ : μ ∈ ρ.expFamilyMeans T) :
    IsGoodRateFunction fun x ↦ ρ.expFamilyRate T x μ := by
  simp_rw [expFamilyRate_def]
  exact isGoodRateFunction_rateFunction
    (zero_mem_interior_integrableExpSet_expFamily (natParam_mem_interior_integrableExpSet hμ))

end MeasureTheory.Measure
