/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.Constructions.Pi
public import LMLExplore.Probability.LargeDeviations.Cramer

/-!
# Large deviations of independent coordinates

Let `P a n`, for `a` in a finite type `ι`, be laws on proper normed groups `X a` that satisfy
large deviation principles with speed `1 / n` and good rate functions `I a`. The product measures
`Measure.pi fun a ↦ P a n`, the laws of independent coordinates of laws `P a n`, satisfy the
large deviation principle with speed `1 / n` and rate function `x ↦ ∑ a, I a (x a)`
[DZ98, Exercise 4.2.7, for two factors]. With a change of time, if the coordinate `a` is observed
through `P a (m a n)` with `m a n / n → w a > 0`, the rate function is
`x ↦ ∑ a, w a I a (x a)`.

For a bandit whose arm `a` has the law `ν a` on `ℝ`, sampled with fixed proportions `w`, the
vector of the empirical means of `m a n` independent samples of each arm `a` has independent
coordinates, so with Cramér's theorem for each arm
(`LMLExplore.Probability.LargeDeviations.Cramer`) it satisfies the large deviation principle with
rate function `x ↦ ∑ a, w a I_a(x a)`, where `I_a` is the Cramér rate function of `ν a`. These
are the large deviations of the empirical means under static allocations, which give the error
exponent of the static-proportions algorithms of fixed-budget identification [GJ04;
D23, Theorem 12]. For arms in exponential families, `I_a(x) = dbar_a(x, μ_a)` is the extended
divergence of the family of arm `a` (`MeasureTheory.Measure.expFamilyRate`).

The lower bound of the product principle comes from boxes: a neighbourhood of `x` contains a
product of neighbourhoods of the coordinates `x a`, whose product measure is the product of their
measures. The upper bound on a closed set `F` comes from a compact box: by exponential tightness,
the coordinates leave a compact set `K a` with probability at most `exp (-(n r))`; the compact set
`F ∩ ∏ a, K a` is covered by finitely many boxes of closed neighbourhoods on which the sum of the
rates is above `r`.

## Main statements

* `LMLExplore.hasLDP_pi`: the large deviation principle of the product measures, with
  rate function `x ↦ ∑ a, I a (x a)`.
* `LMLExplore.hasLDP_pi_comp_of_tendsto_div`: the large deviation principle of the
  product measures `Measure.pi fun a ↦ P a (m a n)` with `m a n / n → w a > 0`, with rate function
  `x ↦ ∑ a, w a I a (x a)`.
* `LMLExplore.hasLDP_pi_cramer`: the vector of the empirical means of `m a n` independent samples
  of laws `ν a` on `ℝ` with cumulant generating functions finite near `0` satisfies the large
  deviation principle with rate function `x ↦ ∑ a, w a I_a(x a)`.
* `LMLExplore.hasLDP_pi_cramer_expFamily`: the same for the statistics of the samples of members
  of exponential families, with the extended divergences `dbar_a(x a, μ a)` of the families.

## References

* [DZ98] A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*, 2nd ed.,
  Springer, 1998, Theorem 2.2.3 and Exercise 4.2.7.
* [GJ04] P. Glynn and S. Juneja, *A large deviations perspective on ordinal optimization*,
  Winter Simulation Conference 2004.
* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468, Theorem 12.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set Finset Topology
open TauCeti.Probability (HasLDP IsGoodRateFunction)

open scoped ENNReal NNReal

namespace LMLExplore

section Product

variable {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ a, MeasurableSpace (X a)]
  {P : ∀ a, ℕ → Measure (X a)} {I : ∀ a, X a → ℝ≥0∞}

/-- **The lower bound of the product principle.** If each `P a` satisfies the lower bound of a
large deviation principle at the speed `1 / n` with rate function `I a`, every neighbourhood `s`
of a point `x` satisfies `-∑ a, I a (x a) ≤ liminf_n (1 / n) log (∏ a, P a n) s`. -/
private lemma neg_sum_le_liminf_log_pi [∀ a, TopologicalSpace (X a)]
    [∀ a n, SigmaFinite (P a n)] (h : ∀ a, HasLDP atTop (fun n : ℕ ↦ (n : ℝ≥0)⁻¹) (P a) (I a))
    {x : ∀ a, X a} {s : Set (∀ a, X a)} (hs : s ∈ 𝓝 x) :
    -((∑ a, I a (x a) : ℝ≥0∞) : EReal) ≤ liminf (fun n : ℕ ↦
      (((n⁻¹ : ℝ≥0) : ℝ) : EReal) * ENNReal.log (Measure.pi (fun a ↦ P a n) s)) atTop := by
  refine neg_le_liminf_inv_mul_log_of_mul_exp_le fun r hr ↦ ⟨1, one_ne_zero, ?_⟩
  obtain ⟨g, hg, hgr⟩ := EReal.exists_forall_gt_and_sum_lt hr
  rw [nhds_pi, Filter.mem_pi'] at hs
  obtain ⟨J, U, hU, hUs⟩ := hs
  filter_upwards [eventually_all.2 fun a ↦ (h a).eventually_exp_le_measure (hU a)
    (hg a (Finset.mem_univ a))] with n hn
  calc 1 * ENNReal.ofReal (Real.exp (-(n * r)))
      ≤ ENNReal.ofReal (Real.exp (-(n * ∑ a, g a))) := by
        rw [one_mul]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg ?_))
        exact mul_le_mul_of_nonneg_left hgr.le n.cast_nonneg
    _ = ∏ a, ENNReal.ofReal (Real.exp (-(n * g a))) := by
        rw [← ENNReal.ofReal_prod_of_nonneg fun a _ ↦ (Real.exp_pos _).le, ← Real.exp_sum,
          Finset.mul_sum, Finset.sum_neg_distrib]
    _ ≤ ∏ a, P a n (U a) := Finset.prod_le_prod fun a _ ↦ hn a
    _ = Measure.pi (fun a ↦ P a n) (univ.pi U) := (Measure.pi_pi _ _).symm
    _ ≤ Measure.pi (fun a ↦ P a n) s :=
        measure_mono ((Set.pi_mono' (fun a _ ↦ subset_rfl) (Set.subset_univ _)).trans hUs)

/-- **The upper bound of the product principle near a point.** Near a point `x` with
`r < ∑ a, I a (x a)`, a box of closed neighbourhoods of the coordinates of `x` has product
measure eventually at most `exp (-(n r))`. -/
private lemma exists_mem_nhds_eventually_pi_le_exp [∀ a, TopologicalSpace (X a)]
    [∀ a, RegularSpace (X a)] [∀ a n, IsZeroOrProbabilityMeasure (P a n)]
    (h : ∀ a, HasLDP atTop (fun n : ℕ ↦ (n : ℝ≥0)⁻¹) (P a) (I a)) {x : ∀ a, X a} {r : ℝ}
    (hr : (r : EReal) < ((∑ a, I a (x a) : ℝ≥0∞) : EReal)) :
    ∃ W ∈ 𝓝 x, ∀ᶠ n : ℕ in atTop,
      Measure.pi (fun a ↦ P a n) W ≤ ENNReal.ofReal (Real.exp (-(n * r))) := by
  obtain ⟨g, hg, hgr⟩ := EReal.exists_forall_lt_and_lt_sum hr
  -- Each coordinate gets a closed neighbourhood on which its rate is above `g a`.
  have hC (a : ι) : ∃ C ∈ 𝓝 (x a), ∀ᶠ n : ℕ in atTop,
      P a n C ≤ ENNReal.ofReal (Real.exp (-(n * g a))) := by
    rcases lt_or_ge (g a) 0 with hga | hga
    · refine ⟨univ, univ_mem, Eventually.of_forall fun n ↦ prob_le_one.trans ?_⟩
      rw [ENNReal.one_le_ofReal, Real.one_le_exp_iff, neg_nonneg]
      exact mul_nonpos_of_nonneg_of_nonpos n.cast_nonneg hga.le
    have hlt : ENNReal.ofReal (g a) < I a (x a) := by
      rw [← EReal.coe_ennreal_lt_coe_ennreal_iff, EReal.coe_ennreal_ofReal, max_eq_left hga]
      exact hg a (Finset.mem_univ a)
    obtain ⟨c, hc₁, hc₂⟩ := exists_between hlt
    obtain ⟨C, hCx, hC, hCsub⟩ :=
      exists_mem_nhds_isClosed_subset ((h a).lowerSemicontinuous (x a) c hc₂)
    refine ⟨C, hCx, (h a).eventually_measure_le_exp hC ?_⟩
    rw [← max_eq_left hga, ← EReal.coe_ennreal_ofReal, EReal.coe_ennreal_lt_coe_ennreal_iff]
    exact hc₁.trans_le (le_iInf₂ fun y hy ↦ (hCsub hy).le)
  choose C hCx hCP using hC
  refine ⟨univ.pi C, set_pi_mem_nhds Set.finite_univ fun a _ ↦ hCx a, ?_⟩
  filter_upwards [eventually_all.2 hCP] with n hn
  calc Measure.pi (fun a ↦ P a n) (univ.pi C) = ∏ a, P a n (C a) := Measure.pi_pi _ _
    _ ≤ ∏ a, ENNReal.ofReal (Real.exp (-(n * g a))) := Finset.prod_le_prod fun a _ ↦ hn a
    _ = ENNReal.ofReal (Real.exp (-(n * ∑ a, g a))) := by
        rw [← ENNReal.ofReal_prod_of_nonneg fun a _ ↦ (Real.exp_pos _).le, ← Real.exp_sum,
          Finset.mul_sum, Finset.sum_neg_distrib]
    _ ≤ ENNReal.ofReal (Real.exp (-(n * r))) := by
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg ?_))
        exact mul_le_mul_of_nonneg_left hgr.le n.cast_nonneg

variable [∀ a, SeminormedAddCommGroup (X a)] [∀ a, ProperSpace (X a)]
  [∀ a n, IsZeroOrProbabilityMeasure (P a n)]

/-- **Large deviations of independent coordinates** [DZ98, Exercise 4.2.7]. If, for each `a` in a
finite type, the measures `P a n` of mass at most `1` on a proper normed group satisfy the large
deviation principle with speed `1 / n` and a good rate function `I a`, then the product measures
`Measure.pi fun a ↦ P a n` satisfy the large deviation principle with speed `1 / n` and rate
function `x ↦ ∑ a, I a (x a)`. -/
theorem hasLDP_pi (h : ∀ a, HasLDP atTop (fun n : ℕ ↦ (n : ℝ≥0)⁻¹) (P a) (I a))
    (hI : ∀ a, IsGoodRateFunction (I a)) :
    HasLDP atTop (fun n : ℕ ↦ (n : ℝ≥0)⁻¹) (fun n ↦ Measure.pi fun a ↦ P a n)
      (fun x ↦ ∑ a, I a (x a)) := by
  refine .of_isClosed_of_mem_nhds ?_ (fun F hF ↦ ?_) (fun x s hs ↦ neg_sum_le_liminf_log_pi h hs)
  · simpa using (isGoodRateFunction_sum_mul hI fun _ ↦ one_pos).lowerSemicontinuous
  refine limsup_inv_mul_log_le_neg_of_le_mul_exp fun r hr ↦ ?_
  -- By exponential tightness, the coordinates leave a compact box `K` with small probability.
  choose M hM using fun a ↦ (h a).exists_eventually_measure_norm_ge_le_exp (hI a) r
  set K : Set (∀ a, X a) := univ.pi fun a ↦ Metric.closedBall 0 (M a)
  have hK : IsCompact (F ∩ K) :=
    (isCompact_univ_pi fun a ↦ isCompact_closedBall _ _).inter_left hF
  -- The compact set `F ∩ K` is covered by finitely many boxes of small product measure.
  obtain ⟨C, hC, hCF⟩ : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᶠ n : ℕ in atTop,
      Measure.pi (fun a ↦ P a n) (F ∩ K) ≤ C * ENNReal.ofReal (Real.exp (-(n * r))) := by
    refine hK.induction_on (p := fun s ↦ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᶠ n : ℕ in atTop,
        Measure.pi (fun a ↦ P a n) s ≤ C * ENNReal.ofReal (Real.exp (-(n * r))))
      ⟨0, ENNReal.zero_ne_top, Eventually.of_forall fun n ↦ by simp⟩
      (fun s t hst ⟨C, hC, hCt⟩ ↦ ⟨C, hC, hCt.mono fun n hn ↦ (measure_mono hst).trans hn⟩)
      (fun s t ⟨C₁, hC₁, h₁⟩ ⟨C₂, hC₂, h₂⟩ ↦ ⟨C₁ + C₂, ENNReal.add_ne_top.2 ⟨hC₁, hC₂⟩, ?_⟩)
      fun x hx ↦ ?_
    · filter_upwards [h₁, h₂] with n hn₁ hn₂
      rw [add_mul]
      exact (measure_union_le _ _).trans (add_le_add hn₁ hn₂)
    · obtain ⟨W, hW, hWP⟩ := exists_mem_nhds_eventually_pi_le_exp h
        (hr.trans_le (EReal.coe_ennreal_le_coe_ennreal_iff.2 (iInf₂_le x hx.1)))
      exact ⟨W, mem_nhdsWithin_of_mem_nhds hW, 1, ENNReal.one_ne_top, by simpa using hWP⟩
  refine ⟨C + Fintype.card ι, by finiteness, ?_⟩
  filter_upwards [hCF, eventually_all.2 hM] with n hn hnM
  have hsub : F ⊆ (F ∩ K) ∪ ⋃ a, Function.eval a ⁻¹' {y | M a ≤ ‖y‖} := by
    intro x hx
    by_cases hxK : x ∈ K
    · exact Or.inl ⟨hx, hxK⟩
    · simp only [K, mem_univ_pi, Metric.mem_closedBall, dist_zero_right, not_forall,
        not_le] at hxK
      obtain ⟨a, ha⟩ := hxK
      exact Or.inr (mem_iUnion.2 ⟨a, ha.le⟩)
  calc Measure.pi (fun a ↦ P a n) F
      ≤ Measure.pi (fun a ↦ P a n) (F ∩ K) +
          ∑ a, Measure.pi (fun a ↦ P a n) (Function.eval a ⁻¹' {y | M a ≤ ‖y‖}) :=
        (measure_mono hsub).trans
          ((measure_union_le _ _).trans (add_le_add_right (measure_iUnion_fintype_le _ _) _))
    _ ≤ C * ENNReal.ofReal (Real.exp (-(n * r))) +
          ∑ _a : ι, ENNReal.ofReal (Real.exp (-(n * r))) := by
        gcongr with a
        exact (Measure.pi_eval_preimage_le a _).trans (hnM a)
    _ = (C + Fintype.card ι) * ENNReal.ofReal (Real.exp (-(n * r))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_mul]

/-- **Large deviations of independent coordinates observed in fixed proportions.** If, for each
`a` in a finite type, the measures `P a n` of mass at most `1` on a proper normed group satisfy
the large deviation principle with speed `1 / n` and a good rate function `I a`, and the indices
`m a n` satisfy `m a n / n → w a` with `w a > 0`, then the product measures
`Measure.pi fun a ↦ P a (m a n)` satisfy the large deviation principle with speed `1 / n` and
rate function `x ↦ ∑ a, w a I a (x a)`, a good rate function by
`LMLExplore.isGoodRateFunction_sum_mul`. -/
theorem hasLDP_pi_comp_of_tendsto_div
    (h : ∀ a, HasLDP atTop (fun n : ℕ ↦ (n : ℝ≥0)⁻¹) (P a) (I a))
    (hI : ∀ a, IsGoodRateFunction (I a)) {m : ι → ℕ → ℕ} {w : ι → ℝ} (hw : ∀ a, 0 < w a)
    (hm : ∀ a, Tendsto (fun n ↦ (m a n : ℝ) / n) atTop (𝓝 (w a))) :
    HasLDP atTop (fun n : ℕ ↦ (n : ℝ≥0)⁻¹) (fun n ↦ Measure.pi fun a ↦ P a (m a n))
      (fun x ↦ ∑ a, ENNReal.ofReal (w a) * I a (x a)) :=
  hasLDP_pi (P := fun a n ↦ P a (m a n)) (fun a ↦ (h a).comp_of_tendsto_div (hw a) (hm a))
    fun a ↦ (hI a).ofReal_mul (hw a)

end Product

section Cramer

variable {ι : Type*} [Fintype ι] {m : ι → ℕ → ℕ} {w : ι → ℝ}

/-- **Large deviations of the empirical means under static allocations** [D23, Theorem 12].
Let `ν a`, for `a` in a finite type, be probability measures on `ℝ` whose cumulant generating
functions are finite on a neighbourhood of `0`, with Cramér rate functions `I_a`, and let
`m a n / n → w a` with `w a > 0`. The vector of the empirical means of `m a n` independent samples
of `ν a`, independent across the coordinates `a`, satisfies the large deviation principle with
speed `1 / n` and rate function `x ↦ ∑ a, w a I_a(x a)`. -/
theorem hasLDP_pi_cramer {ν : ι → Measure ℝ} [∀ a, IsProbabilityMeasure (ν a)]
    (hν : ∀ a, 0 ∈ interior (integrableExpSet id (ν a))) (hw : ∀ a, 0 < w a)
    (hm : ∀ a, Tendsto (fun n ↦ (m a n : ℝ) / n) atTop (𝓝 (w a))) :
    HasLDP atTop (fun n : ℕ ↦ (n : ℝ≥0)⁻¹)
      (fun n ↦ Measure.pi fun a ↦ (Measure.pi fun _ : Fin (m a n) ↦ ν a).map
        fun y : Fin (m a n) → ℝ ↦ (∑ i, y i) / (m a n : ℝ))
      (fun x ↦ ∑ a, ENNReal.ofReal (w a) * rateFunction id (ν a) (x a)) :=
  hasLDP_pi_comp_of_tendsto_div
    (P := fun a n ↦ (Measure.pi fun _ : Fin n ↦ ν a).map fun y : Fin n → ℝ ↦ (∑ i, y i) / (n : ℝ))
    (fun a ↦ hasLDP_cramer (integrable_of_mem_interior_integrableExpSet (hν a)))
    (fun a ↦ isGoodRateFunction_rateFunction (hν a)) hw hm

/-- **Large deviations of the empirical means under static allocations, for exponential
families** [D23, Theorem 12]. Let arm `a`, in a finite type, have the member of mean `μ a` of the
exponential family of a nonzero measure `ρ a` on a measurable space `𝓧` and a statistic `T a`, and
let `m a n / n → w a` with `w a > 0`. The vector of the empirical means of the statistics
`T a (Y i)` of `m a n` independent samples `Y i` of each arm `a`, independent across the arms,
satisfies the large deviation principle with speed `1 / n` and rate function
`x ↦ ∑ a, w a dbar_a(x a, μ a)`, with `dbar_a` the extended divergence of the family of arm `a`
(`MeasureTheory.Measure.expFamilyRate`). -/
theorem hasLDP_pi_cramer_expFamily {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : ι → Measure 𝓧}
    [∀ a, NeZero (ρ a)] {T : ι → 𝓧 → ℝ} {μ : ι → ℝ}
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a)) (hw : ∀ a, 0 < w a)
    (hm : ∀ a, Tendsto (fun n ↦ (m a n : ℝ) / n) atTop (𝓝 (w a))) :
    HasLDP atTop (fun n : ℕ ↦ (n : ℝ≥0)⁻¹)
      (fun n ↦ Measure.pi fun a ↦
        (Measure.pi fun _ : Fin (m a n) ↦ (ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))).map
          fun y : Fin (m a n) → 𝓧 ↦ (∑ i, T a (y i)) / (m a n : ℝ))
      (fun x ↦ ∑ a, ENNReal.ofReal (w a) * (ρ a).expFamilyRate (T a) (x a) (μ a)) := by
  have (a : ι) := Measure.isProbabilityMeasure_expFamily
    (interior_subset (Measure.natParam_mem_interior_integrableExpSet (hμ a)))
  exact hasLDP_pi_comp_of_tendsto_div
    (P := fun a n ↦ (Measure.pi fun _ : Fin n ↦
      (ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))).map
        fun y : Fin n → 𝓧 ↦ (∑ i, T a (y i)) / (n : ℝ))
    (fun a ↦ Measure.hasLDP_cramer_expFamily (hμ a))
    (fun a ↦ Measure.isGoodRateFunction_expFamilyRate_left (hμ a)) hw hm

end Cramer

end LMLExplore
