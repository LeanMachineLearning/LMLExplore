/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EffectiveSet.TotalVariation
public import LMLExplore.EValues.EProcess
public import Mathlib.Probability.Moments.Variance

import Mathlib.MeasureTheory.Measure.TotalVariation.Basic

/-!
# The mean-zero null: e-variables without power

The null `meanZeroNull` of the laws on `ℝ` with mean `0` and a finite, positive variance is dense
in total variation among the probability measures on `ℝ`: a law `Q` is approximated by `Q`
restricted to a large interval and scaled by a factor below `1`, completed by two atoms that
restore the mean `0` and make the variance positive. So the results of
`LMLExplore.EValues.EffectiveSet.TotalVariation` apply, and the null cannot be tested with
e-variables against i.i.d. alternatives, the form for e-variables of the theorem of Bahadur and
Savage [BS56]:

* for every finite number of i.i.d. observations, its e-variables are those of the null of all
  laws on `ℝ`; for one observation, they are the measurable functions bounded by `1`
  everywhere;
* against the i.i.d. law of every `Q`, the maximal expected logarithm of an `n`-sample e-variable
  and the bipolar rate vanish, and a test of level `α` has power at most `α`;
* every e-process, for any filtration, for the laws of the independent sequences with marginals in
  the null is at most `1` at every time and on every sequence.

## Main definitions

* `ProbabilityTheory.meanZeroNull`: the laws on `ℝ` with mean `0` and finite, positive variance.

## Main statements

* `ProbabilityTheory.exists_mem_meanZeroNull_etvDist_lt`: the null is dense in total variation.
* `ProbabilityTheory.isEVar_pi_meanZeroNull_iff`: its `ι`-sample e-variables are those of the
  i.i.d. laws of all probability measures.
* `ProbabilityTheory.isEVar_meanZeroNull_iff`: its one-observation e-variables are the measurable
  functions bounded by `1`.
* `ProbabilityTheory.maxLogGrowth_meanZeroNull`, `ProbabilityTheory.bipolarRate_meanZeroNull`,
  `ProbabilityTheory.measure_pi_le_of_forall_meanZeroNull`: no growth and no power against i.i.d.
  alternatives.
* `ProbabilityTheory.le_one_of_isEProcess_infinitePi_meanZeroNull`: e-processes for the laws of
  independent sequences with marginals in the null are at most `1`.

## References

* [BS56] R. R. Bahadur and L. J. Savage, *The nonexistence of certain statistical procedures in
  nonparametric problems*, Ann. Math. Statist. 27 (1956).
-/

public section

open MeasureTheory Filter Set

open scoped ENNReal Topology

namespace ProbabilityTheory

/-- The laws on `ℝ` with mean `0` and a finite, positive variance: the probability measures `μ`
under which the identity is square integrable, with `∫ x ∂μ = 0` and `0 < variance id μ`. -/
def meanZeroNull : Set (Measure ℝ) :=
  {μ | IsProbabilityMeasure μ ∧ MemLp id 2 μ ∧ ∫ x, x ∂μ = 0 ∧ 0 < variance id μ}

/-- Membership in the mean-zero null. -/
lemma mem_meanZeroNull_iff {μ : Measure ℝ} :
    μ ∈ meanZeroNull ↔
      IsProbabilityMeasure μ ∧ MemLp id 2 μ ∧ ∫ x, x ∂μ = 0 ∧ 0 < variance id μ :=
  Iff.rfl

/-- The members of the mean-zero null are probability measures. -/
lemma isProbabilityMeasure_of_mem_meanZeroNull {μ : Measure ℝ} (hμ : μ ∈ meanZeroNull) :
    IsProbabilityMeasure μ :=
  hμ.1

/-! ### Density in total variation -/

/-- **Completion to a law with mean zero.** A finite measure on `ℝ` of mass less than `1` carried
by a bounded interval is below a member of the mean-zero null: add two atoms of mass
`(1 - ν univ) / 2` at `z - 1` and `z + 1`, for the `z` that makes the mean `0`. -/
private lemma exists_mem_meanZeroNull_le (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν univ < 1)
    {M : ℝ} (hM : ∀ᵐ x ∂ν, |x| ≤ M) : ∃ P ∈ meanZeroNull, ν ≤ P := by
  set b := ν.real univ with hb_def
  have hb0 : 0 ≤ b := measureReal_nonneg
  have hb1 : b < 1 := ENNReal.toReal_lt_of_lt_ofReal (by simpa using hν)
  have h1b : 1 - b ≠ 0 := by linarith
  set z := -(∫ x, x ∂ν) / (1 - b) with hz
  set c := ENNReal.ofReal ((1 - b) / 2) with hc
  have hc0 : c ≠ 0 := by rw [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  set D := Measure.dirac (z - 1) + Measure.dirac (z + 1) with hD
  have : IsFiniteMeasure (c • D) := Measure.smul_finite D hct
  set P := ν + c • D with hP
  have hDb : ∀ᵐ x ∂D, |x| ≤ |z| + 1 := by
    rw [hD, ae_add_measure_iff, ae_dirac_eq, ae_dirac_eq, eventually_pure, eventually_pure]
    exact ⟨abs_le.2 ⟨by linarith [neg_abs_le z], by linarith [le_abs_self z]⟩,
      abs_le.2 ⟨by linarith [neg_abs_le z], by linarith [le_abs_self z]⟩⟩
  have hPb : ∀ᵐ x ∂P, |x| ≤ max M (|z| + 1) := by
    rw [hP, ae_add_measure_iff]
    exact ⟨hM.mono fun x hx ↦ hx.trans (le_max_left _ _),
      Measure.ae_smul_measure (hDb.mono fun x hx ↦ hx.trans (le_max_right _ _)) c⟩
  have hint {μ : Measure ℝ} [IsFiniteMeasure μ] {K : ℝ} (hK : ∀ᵐ x ∂μ, |x| ≤ K) :
      Integrable (fun x : ℝ ↦ x) μ :=
    Integrable.of_bound measurable_id.aestronglyMeasurable K (by simpa using hK)
  have hDu : D univ = 2 := by simp [hD, one_add_one_eq_two]
  have hPprob : IsProbabilityMeasure P := by
    constructor
    rw [hP, add_apply, smul_apply, hDu, smul_eq_mul,
      ← ofReal_measureReal (measure_ne_top ν univ), ← hb_def, hc,
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_add hb0 (by linarith), ← ENNReal.ofReal_one]
    congr 1
    ring
  have hmean : ∫ x, x ∂P = 0 := by
    rw [hP, integral_add_measure (hint hM) ((hint hDb).smul_measure hct), integral_smul_measure,
      hD, integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp)),
      integral_dirac, integral_dirac, hc, ENNReal.toReal_ofReal (by linarith), hz, smul_eq_mul]
    field_simp
    ring
  have hmem : MemLp id 2 P := MemLp.of_bound measurable_id.aestronglyMeasurable (max M (|z| + 1))
    (hPb.mono fun x hx ↦ by simpa [Real.norm_eq_abs] using hx)
  have hvar : 0 < variance id P := by
    refine ENNReal.toReal_pos ?_ hmem.evariance_lt_top.ne
    have hz2 : ‖z - 1‖ₑ ^ 2 + ‖z + 1‖ₑ ^ 2 ≠ 0 := by
      simp only [ne_eq, add_eq_zero, pow_eq_zero_iff two_ne_zero, eNorm_eq_zero, not_and]
      intro h1
      linarith
    have hge : c * (‖z - 1‖ₑ ^ 2 + ‖z + 1‖ₑ ^ 2) ≤ evariance id P := by
      calc c * (‖z - 1‖ₑ ^ 2 + ‖z + 1‖ₑ ^ 2) = ∫⁻ x, ‖x - 0‖ₑ ^ 2 ∂(c • D) := by
            rw [lintegral_smul_measure, hD, lintegral_add_measure, lintegral_dirac,
              lintegral_dirac, smul_eq_mul, sub_zero, sub_zero]
      _ ≤ ∫⁻ x, ‖x - 0‖ₑ ^ 2 ∂P := lintegral_mono' (Measure.le_add_left le_rfl) le_rfl
      _ = evariance id P := by rw [evariance, ← hmean]; rfl
    exact (lt_of_lt_of_le (ENNReal.mul_pos hc0 hz2) hge).ne'
  exact ⟨P, ⟨hPprob, hmem, hmean, hvar⟩, Measure.le_add_right le_rfl⟩

/-- **The mean-zero null is dense in total variation**: every probability measure on `ℝ` is a
limit in total variation of laws with mean `0` and a finite, positive variance. -/
theorem exists_mem_meanZeroNull_etvDist_lt (Q : Measure ℝ) [IsProbabilityMeasure Q]
    {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ P ∈ meanZeroNull, etvDist P Q < ε := by
  -- `Q` restricted to `[-M, M]` and scaled by `1 - η` misses a mass at most `2 δ` of `Q`, and
  -- the completion `P` of it is at distance at most twice that mass.
  obtain ⟨δ', hδ'0, hδ'⟩ := ENNReal.exists_nnreal_pos_mul_lt (b := ε) (a := 4) (by norm_num)
    hε.ne'
  set δ : ℝ≥0∞ := (δ' : ℝ≥0∞)
  have hδ0 : δ ≠ 0 := ENNReal.coe_ne_zero.2 hδ'0.ne'
  have hδ2 : 2 * (2 * δ) < ε := by
    calc 2 * (2 * δ) = δ * 4 := by ring
    _ < ε := hδ'
  have hU : (⋃ M : ℕ, Icc (-(M : ℝ)) M) = univ :=
    eq_univ_of_forall fun x ↦ mem_iUnion.2 ⟨⌈|x|⌉₊, abs_le.1 (Nat.le_ceil _)⟩
  have htend : Tendsto (fun M : ℕ ↦ Q (Icc (-(M : ℝ)) (M : ℝ))) atTop (𝓝 1) := by
    have := tendsto_measure_iUnion_atTop (μ := Q) (s := fun M : ℕ ↦ Icc (-(M : ℝ)) (M : ℝ))
      fun m n hmn ↦ Icc_subset_Icc (by simpa using hmn) (by simpa using hmn)
    rwa [hU, measure_univ] at this
  obtain ⟨M, hM⟩ := (htend.eventually (lt_mem_nhds
    (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hδ0))).exists
  set I := Icc (-(M : ℝ)) M
  set η := min δ 2⁻¹
  have hη0 : η ≠ 0 := by simp [η, hδ0]
  have hη1 : η ≤ 1 := ((min_le_right _ _).trans_lt ENNReal.one_half_lt_one).le
  set ν := (1 - η) • Q.restrict I
  have hνQ : ν ≤ Q := fun s ↦ by
    calc ν s = (1 - η) * Q.restrict I s := rfl
    _ ≤ Q.restrict I s := mul_le_of_le_one_left' tsub_le_self
    _ ≤ Q s := Measure.restrict_le_self s
  have hνuniv : ν univ = (1 - η) * Q I := by simp [ν]
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le Q hνQ
  have hν1 : ν univ < 1 := by
    rw [hνuniv]
    calc (1 - η) * Q I ≤ 1 - η := mul_le_of_le_one_right' prob_le_one
    _ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hη0
  have hνM : ∀ᵐ x ∂ν, |x| ≤ (M : ℝ) :=
    Measure.ae_smul_measure
      (ae_restrict_of_forall_mem measurableSet_Icc fun x hx ↦ abs_le.2 (mem_Icc.1 hx)) _
  obtain ⟨P, hP, hνP⟩ := exists_mem_meanZeroNull_le ν hν1 hνM
  have := hP.1
  -- `ν` misses a mass less than `2 δ` of `Q`.
  have hmiss : 1 - ν univ ≤ 2 * δ := by
    refine tsub_le_iff_left.2 ?_
    calc (1 : ℝ≥0∞) ≤ Q I + δ := tsub_le_iff_right.1 hM.le
    _ = (1 - η) * Q I + η * Q I + δ := by rw [← add_mul, tsub_add_cancel_of_le hη1, one_mul]
    _ ≤ ν univ + 2 * δ := by
      rw [hνuniv, two_mul, add_assoc]
      gcongr
      exact (mul_le_of_le_one_right' prob_le_one).trans (min_le_left _ _)
  refine ⟨P, hP, lt_of_le_of_lt ?_ hδ2⟩
  calc etvDist P Q ≤ etvDist P ν + etvDist ν Q := etvDist_triangle _ _ _
  _ = (1 - ν univ) + (1 - ν univ) := by
    rw [etvDist_of_ge hνP, etvDist_of_le hνQ, measure_univ (μ := P), measure_univ (μ := Q)]
  _ ≤ 2 * (2 * δ) := by rw [← two_mul]; gcongr

/-! ### E-variables -/

/-- **Same e-variables as for all laws.** For every finite set `ι` of i.i.d. real observations, a
function is an e-variable for the i.i.d. laws of the mean-zero null exactly when it is one for the
i.i.d. laws of all probability measures on `ℝ`. -/
theorem isEVar_pi_meanZeroNull_iff {ι : Type*} [Fintype ι] {X : (ι → ℝ) → ℝ≥0∞} :
    IsEVar X ((fun P ↦ Measure.pi fun _ : ι ↦ P) '' meanZeroNull) ↔
      IsEVar X ((fun P ↦ Measure.pi fun _ : ι ↦ P) '' {P | IsProbabilityMeasure P}) :=
  isEVar_pi_iff_of_forall_exists_etvDist_lt (fun _ ↦ isProbabilityMeasure_of_mem_meanZeroNull)
    fun Q _ _ hε ↦ exists_mem_meanZeroNull_etvDist_lt Q hε

/-- **One observation.** The e-variables for the laws on `ℝ` with mean `0` and a finite, positive
variance are the measurable functions bounded by `1` everywhere. -/
theorem isEVar_meanZeroNull_iff {X : ℝ → ℝ≥0∞} :
    IsEVar X meanZeroNull ↔ Measurable X ∧ ∀ x, X x ≤ 1 :=
  isEVar_iff_of_forall_exists_etvDist_dirac_lt
    (fun _ hP ↦ (isProbabilityMeasure_of_mem_meanZeroNull hP).measure_univ.le)
    fun x _ hε ↦ exists_mem_meanZeroNull_etvDist_lt (Measure.dirac x) hε

/-! ### No power against i.i.d. alternatives -/

/-- **No growth.** For every law `Q` on `ℝ` and every number `n` of observations, the maximal
expected logarithm under `Q ^ n` of an `n`-sample e-variable for the i.i.d. laws of the mean-zero
null is `0`. -/
theorem maxLogGrowth_meanZeroNull (Q : Measure ℝ) [IsProbabilityMeasure Q] (n : ℕ) :
    maxLogGrowth Q meanZeroNull n = 0 :=
  maxLogGrowth_eq_zero_of_forall_exists_etvDist_lt
    (fun _ ↦ isProbabilityMeasure_of_mem_meanZeroNull)
    (fun _ hε ↦ exists_mem_meanZeroNull_etvDist_lt Q hε) n

/-- **The bipolar rate is zero.** For every law `Q` on `ℝ`, the optimal growth rate of the
evidence against the i.i.d. laws of the mean-zero null under the i.i.d. law of `Q` is `0`. -/
theorem bipolarRate_meanZeroNull (Q : Measure ℝ) [IsProbabilityMeasure Q] :
    bipolarRate Q meanZeroNull = 0 :=
  bipolarRate_eq_zero_of_forall_exists_etvDist_lt
    (fun _ ↦ isProbabilityMeasure_of_mem_meanZeroNull)
    fun _ hε ↦ exists_mem_meanZeroNull_etvDist_lt Q hε

/-- **No power.** A measurable set of `ι` real observations with probability at most `α` under
the i.i.d. law of every member of the mean-zero null has probability at most `α` under the
i.i.d. law of every probability measure on `ℝ`. -/
theorem measure_pi_le_of_forall_meanZeroNull {ι : Type*} [Fintype ι] {R : Set (ι → ℝ)}
    (hR : MeasurableSet R) {α : ℝ≥0∞}
    (hα : ∀ P ∈ meanZeroNull, Measure.pi (fun _ : ι ↦ P) R ≤ α) (Q : Measure ℝ)
    [IsProbabilityMeasure Q] :
    Measure.pi (fun _ : ι ↦ Q) R ≤ α :=
  measure_pi_le_of_forall_exists_etvDist_lt (fun _ ↦ isProbabilityMeasure_of_mem_meanZeroNull)
    (fun _ hε ↦ exists_mem_meanZeroNull_etvDist_lt Q hε) hR hα

/-- **Independent sequences.** Every e-process, for any filtration, for the laws of the
independent sequences of real observations whose marginals have mean `0` and a finite, positive
variance is at most `1` at every time and on every sequence. -/
theorem le_one_of_isEProcess_infinitePi_meanZeroNull
    {ℱ : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → ℝ))} {E : ℕ → (ℕ → ℝ) → ℝ≥0∞}
    (hE : IsEProcess E ℱ (Measure.infinitePi '' {P : ℕ → Measure ℝ | ∀ n, P n ∈ meanZeroNull}))
    (n : ℕ) (x : ℕ → ℝ) :
    E n x ≤ 1 :=
  ((isEVar_infinitePi_iff_of_forall_exists_etvDist_dirac_lt
    (fun _ ↦ isProbabilityMeasure_of_mem_meanZeroNull)
    (fun y _ hε ↦ exists_mem_meanZeroNull_etvDist_lt (Measure.dirac y) hε)).1 (hE.isEVar n)).2 x

end ProbabilityTheory
