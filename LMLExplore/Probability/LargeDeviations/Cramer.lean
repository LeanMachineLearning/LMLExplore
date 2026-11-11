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
public import LMLExplore.MeasureTheory.Constructions.Pi

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

The upper bound on a closed set `F` comes from the two-sided Cramér–Chernoff bound of
`LMLExplore.Probability.LargeDeviations.Chernoff`: the empirical mean lies in `F` only if the rate
function at the empirical mean is at least its infimum on `F`.

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

The proofs are adapted from the formalization Degenne2023Existence
(`github.com/RemyDegenne/Degenne2023Existence`, file
`Degenne2023Existence/ForLMLExplore/Probability/LargeDeviations/Cramer.lean`, commit
`5afa57772d415c17cfd89de287fb004ca51d8fb3`, by Rémy Degenne, Apache 2.0) of [D23]; the
i.i.d.-sequence form and the generalization of the exponential-family form to any statistic are
new.
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

/-- **The upper bound of Cramér's theorem.** For a probability measure `ν` on `ℝ` with a mean and
a closed set `F`, the laws `P n` of the empirical means of `n` independent samples of `ν` satisfy
`limsup_n (1 / n) log P n F ≤ -inf_F I`, with `I` the Cramér rate function of `ν`
[DZ98, Theorem 2.2.3]. -/
lemma limsup_log_measure_le_neg_iInf_rateFunction [IsProbabilityMeasure ν]
    (hν : Integrable id ν) {F : Set ℝ} (hF : IsClosed F) :
    limsup (fun n : ℕ ↦ ENNReal.log (((Measure.pi fun _ : Fin n ↦ ν).map
        fun y : Fin n → ℝ ↦ (∑ i, y i) / (n : ℝ)) F) / n) atTop ≤
      -(((⨅ x ∈ F, rateFunction id ν x : ℝ≥0∞)) : EReal) := by
  refine limsup_log_div_le_neg_of_le_mul_exp fun r hr ↦
    ⟨2, ENNReal.ofNat_ne_top, Eventually.of_forall fun n ↦ ?_⟩
  -- The rate function is at least `r` on `F`, and the empirical mean has rate at least `r` with
  -- probability at most `2 exp (-(n r))` by the two-sided Cramér–Chernoff bound.
  have hrF : ENNReal.ofReal r ≤ ⨅ x ∈ F, rateFunction id ν x := by
    rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_ennreal_ofReal]
    exact max_le hr.le (EReal.coe_ennreal_nonneg _)
  have h := (iIndepFun_eval (ν := ν) n).measureReal_le_card_mul_rateFunction_le_two_mul_exp
    (s := univ) (fun i _ ↦ (identDistrib_eval i).mgfDominatedOn) hν (n * r)
  rw [card_univ, Fintype.card_fin] at h
  rw [Measure.map_apply (measurable_mean n) hF.measurableSet, ← ofReal_measureReal,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two]
  refine ENNReal.ofReal_le_ofReal ((measureReal_mono fun y hy ↦ ?_).trans h)
  rw [mem_ofPred_eq, ENNReal.ofReal_mul n.cast_nonneg, ENNReal.ofReal_natCast]
  exact mul_le_mul_right (hrF.trans (iInf₂_le ((∑ i, y i) / n) hy)) _

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

/-- **Lower bound by exponential tilting**, for a probability measure `ν` with every exponential
moment that charges both sides of `x`: `I(x)` is finite and, for every `δ, ε > 0`, eventually the
sum of `n` samples is within `n δ` of `n x` with probability at least `exp (-(n (I(x) + ε)))`. -/
private lemma eventually_exp_le_measure_abs_sum_sub_le [IsProbabilityMeasure ν]
    (h_int : ∀ t, Integrable (fun y ↦ exp (t * y)) ν) (hlt : ν (Iio x) ≠ 0)
    (hgt : ν (Ioi x) ≠ 0) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    rateFunction id ν x ≠ ⊤ ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (exp (-(n * ((rateFunction id ν x).toReal + ε)))) ≤
        (Measure.pi fun _ : Fin n ↦ ν) {y | |∑ i, y i - n * x| ≤ n * δ} := by
  -- `x` is a mean of the exponential family of `ν`, whose member of mean `m = ψ'(0)` is `ν`, and
  -- `I(x) = d(x, m)`.
  have hS : interior (integrableExpSet id ν) = Set.univ := by
    rw [show integrableExpSet id ν = Set.univ from Set.eq_univ_of_forall h_int, interior_univ]
  have hT : ∀ c, ¬ (id =ᵐ[ν] fun _ ↦ c) := by
    intro c hc
    rcases le_or_gt x c with hxc | hcx
    · exact hlt (measure_mono_null (fun y (hy : y < x) ↦ (hy.trans_le hxc).ne) (ae_iff.1 hc))
    · exact hgt (measure_mono_null (fun y (hy : x < y) ↦ (hcx.trans hy).ne') (ae_iff.1 hc))
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet id ν) := hS ▸ mem_univ 0
  have hx := Measure.mem_expFamilyMeans_id_of_measure_Iio_ne_zero_of_measure_Ioi_ne_zero h_int
    hlt hgt
  have hμ₀ : deriv (cgf id ν) 0 ∈ ν.expFamilyMeans id := Measure.deriv_cgf_mem_expFamilyMeans h0
  have hrate := rateFunction_eq_ofReal_expFamilyDiv hT h0 hx
  refine ⟨by rw [hrate]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [hrate, ENNReal.toReal_ofReal (Measure.expFamilyDiv_nonneg hx hμ₀)]
  -- The tilting estimate at a radius `r' ≤ δ` with tilt cost `|η| r' ≤ ε / 2` bounds the
  -- probability below by `exp (-(n (d + ε / 2))) (1 - V / (n r'²))`, and eventually
  -- `exp (-(n ε / 2)) ≤ 1 / 2 ≤ 1 - V / (n r'²)`.
  set d := ν.expFamilyDiv id x (deriv (cgf id ν) 0)
  set η := ν.natParam id x - ν.natParam id (deriv (cgf id ν) 0)
  set V := Var[id; ν.expFamily id (ν.natParam id x)]
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
      rw [Measure.natParam_deriv_cgf hT h0, Measure.expFamily_zero]
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

/-- The intervals `[-k, k]` grow with `k`. -/
private lemma Icc_neg_natCast_subset {k k' : ℕ} (hk : k ≤ k') :
    Icc (-(k : ℝ)) k ⊆ Icc (-(k' : ℝ)) k' :=
  Icc_subset_Icc (neg_le_neg (Nat.cast_le.2 hk)) (Nat.cast_le.2 hk)

/-- A set of positive measure contains a set of positive measure within `[-k, k]`, for some `k`. -/
private lemma exists_measure_Icc_inter_ne_zero {s : Set ℝ} (hs : ν s ≠ 0) :
    ∃ k : ℕ, ν (Icc (-(k : ℝ)) k ∩ s) ≠ 0 := by
  by_contra! h
  refine hs (measure_mono_null (fun y hy ↦ ?_) (measure_iUnion_null h))
  obtain ⟨k, hk⟩ := exists_nat_ge |y|
  exact mem_iUnion.2 ⟨k, abs_le.1 hk, hy⟩

/-- A bound on the integrals of `f` over the intervals `[-k, k]` bounds the integral of `f`, by
monotone convergence. -/
private lemma lintegral_le_of_forall_setLIntegral_Icc_le {f : ℝ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ k : ℕ, ∫⁻ y in Icc (-(k : ℝ)) k, f y ∂ν ≤ c) : ∫⁻ y, f y ∂ν ≤ c := by
  have h_union : ⋃ k : ℕ, Icc (-(k : ℝ)) k = Set.univ :=
    eq_univ_of_forall fun y ↦ mem_iUnion.2 ((exists_nat_ge |y|).imp fun _ ↦ abs_le.1)
  have h_tend := tendsto_measure_iUnion_atTop (μ := ν.withDensity f)
    fun _ _ hk ↦ Icc_neg_natCast_subset hk
  rw [h_union, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h_tend
  exact le_of_tendsto' h_tend fun k ↦ (withDensity_apply _ measurableSet_Icc).trans_le (h k)

/-- `exp (t (y - x)) = exp (-(t x)) exp (t y)`. -/
private lemma exp_mul_sub (t x y : ℝ) : exp (t * (y - x)) = exp (-(t * x)) * exp (t * y) := by
  rw [← exp_add]
  congr 1
  ring

/-- `∫ exp (t (y - x)) dμ(y) = exp (-(t x)) mgf id μ t`. -/
private lemma integral_exp_mul_sub (μ : Measure ℝ) (t : ℝ) :
    ∫ y, exp (t * (y - x)) ∂μ = exp (-(t * x)) * mgf id μ t := by
  simp_rw [exp_mul_sub t x, integral_const_mul]
  rfl

/-- `∫ exp (t (y - x)) dμ(y) = exp (cgf id μ t - t x)` when `exp (t y)` is integrable. -/
private lemma integral_exp_mul_sub_eq_exp {μ : Measure ℝ} [NeZero μ] {t : ℝ}
    (ht : Integrable (fun y ↦ exp (t * y)) μ) :
    ∫ y, exp (t * (y - x)) ∂μ = exp (cgf id μ t - t * x) := by
  rw [integral_exp_mul_sub, ← exp_cgf (X := id) ht, ← exp_add, neg_add_eq_sub]

/-- `y ↦ exp (t (y - x))` is integrable exactly when `y ↦ exp (t y)` is. -/
private lemma integrable_exp_mul_sub_iff {μ : Measure ℝ} {t : ℝ} :
    Integrable (fun y ↦ exp (t * (y - x))) μ ↔ Integrable (fun y ↦ exp (t * y)) μ := by
  simp_rw [exp_mul_sub t x]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.2 (exp_pos _).ne') _

/-- The function `y ↦ exp (t y)` is integrable on every interval `[a, b]`. -/
private lemma integrableOn_exp_mul_Icc [IsFiniteMeasure ν] (t a b : ℝ) :
    IntegrableOn (fun y ↦ exp (t * y)) (Icc a b) ν :=
  (continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.integrableOn_compact
    isCompact_Icc

/-- The function `t ↦ ∫_{[-M, M]} exp (t (y - x)) dν(y)` is continuous. -/
private lemma continuous_setIntegral_exp [IsFiniteMeasure ν] (M : ℝ) :
    Continuous fun t ↦ ∫ y in Icc (-M) M, exp (t * (y - x)) ∂ν := by
  simp_rw [integral_exp_mul_sub]
  exact (continuous_exp.comp (continuous_id.mul continuous_const).neg).mul
    (continuous_mgf fun t ↦ integrableOn_exp_mul_Icc t _ _)

/-- **Coercivity of the truncated integrals.** If `ν` charges both sides of `x` within
`[-M₀, M₀]`, then for every `c` there is a compact set `K` such that
`c ≤ ∫_{[-M, M]} exp (t (y - x)) dν(y)` for every `t ∉ K` and every `M ≥ M₀`. -/
private lemma exists_isCompact_forall_le_setIntegral_exp [IsFiniteMeasure ν] {M₀ : ℝ}
    (hlt : ν (Icc (-M₀) M₀ ∩ Iio x) ≠ 0) (hgt : ν (Icc (-M₀) M₀ ∩ Ioi x) ≠ 0) (c : ℝ) :
    ∃ K, IsCompact K ∧ ∀ M, M₀ ≤ M → ∀ t ∉ K, c ≤ ∫ y in Icc (-M) M, exp (t * (y - x)) ∂ν := by
  have hlt' : ν.restrict (Icc (-M₀) M₀) (Iio x) ≠ 0 := by
    rwa [Measure.restrict_apply measurableSet_Iio, inter_comm]
  have hgt' : ν.restrict (Icc (-M₀) M₀) (Ioi x) ≠ 0 := by
    rwa [Measure.restrict_apply measurableSet_Ioi, inter_comm]
  have : NeZero (ν.restrict (Icc (-M₀) M₀)) := ⟨fun h ↦ hlt' (by simp [h])⟩
  have h_int (t : ℝ) := integrableOn_exp_mul_Icc (ν := ν) t (-M₀) M₀
  have h_tend : Tendsto (fun t ↦ ∫ y in Icc (-M₀) M₀, exp (t * (y - x)) ∂ν) (cocompact ℝ) atTop :=
    (tendsto_exp_atTop.comp (Measure.tendsto_cgf_id_sub_mul_cocompact h_int hlt' hgt')).congr
      fun t ↦ (integral_exp_mul_sub_eq_exp (h_int t)).symm
  obtain ⟨K, hK, hKc⟩ := mem_cocompact.1 (h_tend.eventually_ge_atTop c)
  refine ⟨K, hK, fun M hM t ht ↦ le_trans (hKc ht) ?_⟩
  exact setIntegral_mono_set (integrable_exp_mul_sub_iff.2 (integrableOn_exp_mul_Icc t _ _))
    (Eventually.of_forall fun _ ↦ (exp_pos _).le)
    (Eventually.of_forall (Icc_subset_Icc (neg_le_neg hM) hM))

/-- `∫ exp (t (y - x)) dν(y) ≥ exp (-I(x))` for every `t`, as an `ℝ≥0∞`-valued integral. -/
private lemma ofReal_exp_le_lintegral_exp [IsProbabilityMeasure ν]
    (hI : rateFunction id ν x ≠ ⊤) (t : ℝ) :
    ENNReal.ofReal (exp (-(rateFunction id ν x).toReal)) ≤
      ∫⁻ y, ENNReal.ofReal (exp (t * (y - x))) ∂ν := by
  have h_nonneg : 0 ≤ᵐ[ν] fun y ↦ exp (t * (y - x)) := ae_of_all _ fun _ ↦ (exp_pos _).le
  by_cases ht : Integrable (fun y ↦ exp (t * y)) ν
  · rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_sub_iff.2 ht) h_nonneg,
      integral_exp_mul_sub_eq_exp ht]
    refine ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_)
    have h := (ENNReal.ofReal_le_iff_le_toReal hI).1 (ofReal_le_rateFunction (X := id) ht x)
    linarith
  · -- Otherwise the integral is infinite.
    have h_top : ∫⁻ y, ENNReal.ofReal (exp (t * (y - x))) ∂ν = ⊤ := by
      by_contra h
      exact ht (integrable_exp_mul_sub_iff.1
        ((lintegral_ofReal_ne_top_iff_integrable (by fun_prop) h_nonneg).1 h))
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
  set c := exp (-((rateFunction id ν x).toReal + ε))
  -- `ν` charges both sides of `x` within `[-M, M]` for every `M ≥ M₀`.
  obtain ⟨k₁, hk₁⟩ := exists_measure_Icc_inter_ne_zero hlt
  obtain ⟨k₂, hk₂⟩ := exists_measure_Icc_inter_ne_zero hgt
  set M₀ := max k₁ k₂
  have h_sides (M : ℕ) (hM : M₀ ≤ M) :
      ν (Icc (-(M : ℝ)) M ∩ Iio x) ≠ 0 ∧ ν (Icc (-(M : ℝ)) M ∩ Ioi x) ≠ 0 :=
    ⟨fun h ↦ hk₁ (measure_mono_null (inter_subset_inter_left _
        (Icc_neg_natCast_subset ((le_max_left _ _).trans hM))) h),
      fun h ↦ hk₂ (measure_mono_null (inter_subset_inter_left _
        (Icc_neg_natCast_subset ((le_max_right _ _).trans hM))) h)⟩
  obtain ⟨K, hK, hKc⟩ :=
    exists_isCompact_forall_le_setIntegral_exp (h_sides M₀ le_rfl).1 (h_sides M₀ le_rfl).2 c
  by_contra! h
  -- The nested compact sets of the parameters at which the truncated integral is at most `c`.
  set S : ℕ → Set ℝ := fun k ↦ K ∩
    {t | ∫ y in Icc (-((M₀ + k : ℕ) : ℝ)) (M₀ + k : ℕ), exp (t * (y - x)) ∂ν ≤ c}
  have hS_closed (k : ℕ) : IsClosed (S k) :=
    hK.isClosed.inter (isClosed_le (continuous_setIntegral_exp _) continuous_const)
  have hS_ne (k : ℕ) : (S k).Nonempty := by
    obtain ⟨t, ht⟩ := h (M₀ + k) (h_sides _ le_self_add).1 (h_sides _ le_self_add).2
    exact ⟨t, not_not.1 fun htK ↦ (hKc _ (by exact_mod_cast le_self_add) t htK).not_gt ht, ht.le⟩
  have hS_anti (k : ℕ) : S (k + 1) ⊆ S k := fun t ht ↦ ⟨ht.1, le_trans
    (setIntegral_mono_set (integrable_exp_mul_sub_iff.2 (integrableOn_exp_mul_Icc t _ _))
      (Eventually.of_forall fun _ ↦ (exp_pos _).le)
      (Eventually.of_forall (Icc_neg_natCast_subset (by omega)))) ht.2⟩
  obtain ⟨t₀, ht₀⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hS_anti
    hS_ne (hK.of_isClosed_subset (hS_closed 0) inter_subset_left) hS_closed
  -- By monotone convergence, `∫ exp (t₀ (y - x)) dν(y) ≤ c < exp (-I(x))`, a contradiction.
  have h_le : ∫⁻ y, ENNReal.ofReal (exp (t₀ * (y - x))) ∂ν ≤ ENNReal.ofReal c := by
    refine lintegral_le_of_forall_setLIntegral_Icc_le fun k ↦
      (lintegral_mono_set (Icc_neg_natCast_subset (Nat.le_add_left k M₀))).trans ?_
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_exp_mul_sub_iff.2 (integrableOn_exp_mul_Icc t₀ _ _))
      (Eventually.of_forall fun _ ↦ (exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (mem_iInter.1 ht₀ k).2
  have h_lt : ENNReal.ofReal c < ENNReal.ofReal (exp (-(rateFunction id ν x).toReal)) :=
    (ENNReal.ofReal_lt_ofReal_iff (exp_pos _)).2 (exp_lt_exp.2 (by linarith))
  exact (h_lt.trans_le ((ofReal_exp_le_lintegral_exp hI t₀).trans h_le)).false

/-- The rate function at `x` of the normalized truncation `ν[|B]` is at most `log ν(B) + c`, when
the truncated integrals `∫_B exp (t (y - x)) dν(y)` are at least `exp (-c)`. -/
private lemma toReal_rateFunction_cond_le [IsFiniteMeasure ν] {B : Set ℝ} (hB0 : ν B ≠ 0)
    (h_int : ∀ t, IntegrableOn (fun y ↦ exp (t * y)) B ν) {c : ℝ}
    (hB : ∀ t, exp (-c) ≤ ∫ y in B, exp (t * (y - x)) ∂ν) :
    (rateFunction id ν[|B] x).toReal ≤ log (ν.real B) + c := by
  have hp : 0 < ν.real B := ENNReal.toReal_pos hB0 (measure_ne_top _ _)
  have : NeZero (ν.restrict B) := ⟨by rwa [Ne, Measure.restrict_eq_zero]⟩
  have h_nonneg : 0 ≤ log (ν.real B) + c := by
    have h := hB 0
    simp only [zero_mul, exp_zero, setIntegral_const, smul_eq_mul, mul_one] at h
    linarith [(le_log_iff_exp_le hp).2 h]
  refine ENNReal.toReal_le_of_le_ofReal h_nonneg
    (rateFunction_le_iff.2 fun t _ ↦ ENNReal.ofReal_le_ofReal ?_)
  -- `cgf id ν[|B] t = cgf id ν|_B t - log ν(B)` and `cgf id ν|_B t - t x ≥ -c`.
  have h_cgf : cgf id ν[|B] t = cgf id (ν.restrict B) t - log (ν.real B) := by
    rw [cgf, cgf, ProbabilityTheory.cond, mgf_smul_measure, ENNReal.toReal_inv, ← measureReal_def,
      log_mul (inv_pos.2 hp).ne' (mgf_pos' (X := id) (NeZero.ne _) (h_int t)).ne', log_inv]
    ring
  have h := (le_log_iff_exp_le ((exp_pos _).trans_le (hB t))).2 (hB t)
  rw [integral_exp_mul_sub_eq_exp (h_int t), log_exp] at h
  rw [h_cgf]
  linarith

/-- Restricting the factors of a product measure to `B`: `ν(B)^n ν[|B]^n(A) ≤ ν^n(A)`. -/
private lemma pow_mul_pi_cond_le [IsFiniteMeasure ν] {B : Set ℝ} (hB0 : ν B ≠ 0) (n : ℕ)
    (A : Set (Fin n → ℝ)) :
    ν B ^ n * (Measure.pi fun _ : Fin n ↦ ν[|B]) A ≤ (Measure.pi fun _ : Fin n ↦ ν) A := by
  have h_restrict : Measure.pi (fun _ : Fin n ↦ ν.restrict B) =
      ν B ^ n • Measure.pi (fun _ : Fin n ↦ ν[|B]) := by
    refine Measure.pi_eq fun s hs ↦ ?_
    have hpow : ν B ^ n = ∏ _i : Fin n, ν B := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [smul_apply, Measure.pi_pi, smul_eq_mul, hpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [cond_apply' (hs i), Measure.restrict_apply (hs i), ← mul_assoc,
      ENNReal.mul_inv_cancel hB0 (measure_ne_top _ _), one_mul, inter_comm]
  calc ν B ^ n * (Measure.pi fun _ : Fin n ↦ ν[|B]) A
  _ = ((Measure.pi fun _ : Fin n ↦ ν).restrict (Set.univ.pi fun _ ↦ B)) A := by
    rw [Measure.restrict_pi_pi, h_restrict, smul_apply, smul_eq_mul]
  _ ≤ (Measure.pi fun _ : Fin n ↦ ν) A := Measure.restrict_apply_le _ _

/-- **The lower bound by truncation**, at a level `x` of finite rate with `ν` charging both sides
of `x`: for `δ > 0` and `r > I(x)`, eventually the sum of `n` samples of `ν` is within `n δ` of
`n x` with probability at least `exp (-(n r))`. The normalized truncation `ν[|[-M, M]]` satisfies
the bound of `eventually_exp_le_measure_abs_sum_sub_le`, and `ν^n ≥ ν([-M, M])^n ν[|[-M, M]]^n`. -/
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
  set p := ν.real B
  have hp : 0 < p := ENNReal.toReal_pos hB0 (measure_ne_top _ _)
  have := cond_isProbabilityMeasure (μ := ν) hB0
  have h_int' (t : ℝ) : Integrable (fun y ↦ exp (t * y)) ν[|B] :=
    (integrableOn_exp_mul_Icc t _ _).smul_measure (ENNReal.inv_ne_top.2 hB0)
  have hlt' : ν[|B] (Iio x) ≠ 0 := by
    rw [cond_apply' measurableSet_Iio]
    exact mul_ne_zero (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) hM₁
  have hgt' : ν[|B] (Ioi x) ≠ 0 := by
    rw [cond_apply' measurableSet_Ioi]
    exact mul_ne_zero (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) hM₂
  have h_rate := toReal_rateFunction_cond_le hB0 (fun t ↦ integrableOn_exp_mul_Icc t _ _) hM
  obtain ⟨-, h_ev⟩ := eventually_exp_le_measure_abs_sum_sub_le h_int' hlt' hgt' hδ hε
  filter_upwards [h_ev] with n hn
  refine le_trans ?_ (pow_mul_pi_cond_le hB0 n _)
  calc ENNReal.ofReal (exp (-(n * r)))
  _ ≤ ENNReal.ofReal (p ^ n) *
      ENNReal.ofReal (exp (-(n * ((rateFunction id ν[|B] x).toReal + ε)))) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← exp_log hp, ← exp_nat_mul, ← exp_add]
    refine exp_le_exp.2 ?_
    have hr2 : r = I + 2 * ε := by simp only [ε]; ring
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  _ ≤ ν B ^ n * (Measure.pi fun _ : Fin n ↦ ν[|B]) {y | |∑ i, y i - n * x| ≤ n * δ} := by
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
  have := hlaw.isProbabilityMeasure_iff.1 ‹_›
  have h_law (n : ℕ) : (Measure.pi fun _ : Fin n ↦ ρ.expFamily T (ρ.natParam T μ)).map
      (fun y : Fin n → 𝓧 ↦ (∑ i, T (y i)) / (n : ℝ)) =
        (Measure.pi fun _ : Fin n ↦ (ρ.expFamily T (ρ.natParam T μ)).map T).map
          fun y : Fin n → ℝ ↦ (∑ i, y i) / (n : ℝ) :=
    map_pi_comp_eq_map_pi_map (X := fun _ ↦ T) (fun _ ↦ hT.aemeasurable)
      (measurable_mean n).aemeasurable
  simp_rw [h_law, expFamilyRate_def,
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
